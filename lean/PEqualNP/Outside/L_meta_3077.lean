import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3077
open PEqualNP.CircuitLowerBounds
abbrev Sig:=BitVec 512
def zero : Sig:=0
def one : Sig:=BitVec.allOnes 512
def neg (a:Sig) : Sig := ~~~a
def bin (d:Bool) (a b:Sig) : Sig:=if d then a ||| b else a &&& b
def proper (a:Sig) : Prop:=a ≠ zero∧a ≠ one
lemma bin_comm (d:Bool) (a b:Sig) : bin d a b=bin d b a:=by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
def Live (fu:Sig) : Nat→ Nat→ Finset Sig→ Prop:=fun k t S =>
  ∀ (M:(Nat→ Nat→ Finset Sig→ Prop)),(proper fu→ M 0 0 {fu}) →
  (∀ {k t:Nat} {U:Finset Sig} {a:Sig},proper a→ neg a ∉ insert a U→ M k t (insert (neg a) U)→ M (k+1) (t+1) (insert a U)) →
  (∀ {k t:Nat} {U:Finset Sig} {a b:Sig} {d:Bool},proper a→ proper b→ a ≠ b→ bin d a b ∉ insert a (insert b U)→ M k t (insert (bin d a b) U)→ M (k+1) t (insert a (insert b U))) →
  M k t S
lemma Live.stop {fu:Sig}  (h0:proper fu) : Live fu 0 0 {fu}:=fun M stop unary binary => @stop  h0
lemma Live.unary {fu:Sig} {k t:Nat} {U:Finset Sig} {a:Sig} (h0:proper a) (h1:neg a ∉ insert a U) (h2:Live fu k t (insert (neg a) U)) : Live fu (k+1) (t+1) (insert a U):=fun M stop unary binary => @unary k t U a h0 h1 (h2 M stop unary binary)
lemma Live.binary {fu:Sig} {k t:Nat} {U:Finset Sig} {a b:Sig} {d:Bool} (h0:proper a) (h1:proper b) (h2:a ≠ b) (h3:bin d a b ∉ insert a (insert b U)) (h4:Live fu k t (insert (bin d a b) U)) : Live fu (k+1) t (insert a (insert b U)):=fun M stop unary binary => @binary k t U a b d h0 h1 h2 h3 (h4 M stop unary binary)
lemma Live.induct {fu:Sig} {M:(Nat→ Nat→ Finset Sig→ Prop)} {k t S} (h:Live fu k t S)
  (stop:proper fu→ M 0 0 {fu})
  (unary:∀ {k t:Nat} {U:Finset Sig} {a:Sig},proper a→ neg a ∉ insert a U→ Live fu k t (insert (neg a) U)→ M k t (insert (neg a) U)→ M (k+1) (t+1) (insert a U))
  (binary:∀ {k t:Nat} {U:Finset Sig} {a b:Sig} {d:Bool},proper a→ proper b→ a ≠ b→ bin d a b ∉ insert a (insert b U)→ Live fu k t (insert (bin d a b) U)→ M k t (insert (bin d a b) U)→ M (k+1) t (insert a (insert b U))) : M k t S :=
  (h (fun k t S => Live fu k t S∧M k t S)
  (fun h0 => ⟨@Live.stop fu  h0,@stop  h0⟩)
  (@fun k t U a h0 h1 h2 => ⟨@Live.unary fu k t U a h0 h1 h2.1,@unary k t U a h0 h1 h2.1 h2.2⟩)
  (@fun k t U a b d h0 h1 h2 h3 h4 => ⟨@Live.binary fu k t U a b d h0 h1 h2 h3 h4.1,@binary k t U a b d h0 h1 h2 h3 h4.1 h4.2⟩)).2
lemma Live.recurse {fu:Sig} {M:∀ (k t:Nat) (S:Finset Sig) (proof:Live fu k t S),Prop}
  (stop:∀ (h0:proper fu),M 0 0 {fu} (@Live.stop fu  h0))
  (unary:∀ {k t:Nat} {U:Finset Sig} {a:Sig} (h0:proper a) (h1:neg a ∉ insert a U) (h2:Live fu k t (insert (neg a) U)) (ih:M k t (insert (neg a) U) h2),M (k+1) (t+1) (insert a U) (@Live.unary fu k t U a h0 h1 h2))
  (binary:∀ {k t:Nat} {U:Finset Sig} {a b:Sig} {d:Bool} (h0:proper a) (h1:proper b) (h2:a ≠ b) (h3:bin d a b ∉ insert a (insert b U)) (h4:Live fu k t (insert (bin d a b) U)) (ih:M k t (insert (bin d a b) U) h4),M (k+1) t (insert a (insert b U)) (@Live.binary fu k t U a b d h0 h1 h2 h3 h4))
  {k t S} (h:Live fu k t S) : M k t S h:=by
  have r:=Live.induct (M:=fun k t S => ∀ hh : Live fu k t S,M k t S hh) h
    (fun h0 _ => @stop  h0)
    (@fun k t U a h0 h1 h2 h3 _ => @unary k t U a h0 h1 h2 (h3 h2))
    (@fun k t U a b d h0 h1 h2 h3 h4 h5 _ => @binary k t U a b d h0 h1 h2 h3 h4 (h5 h4))
  exact r h
lemma Live.zeroSet {T t S} (h:Live T 0 t S) : S={T}:=by
  have hh:=h (fun k _ W => k=0→ W={T}) (fun _ _ => rfl)
    (@fun _ _ _ _ _ _ _ e => by omega)
    (@fun _ _ _ _ _ _ _ _ _ _ _ e => by omega)
  exact hh rfl
lemma live_proper {k t S} (h:Live fu k t S) : ∀ a ∈ S,proper a:=by
  induction h using Live.recurse with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert];exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma kp {k t S} (h:Live fu k t S) : t ≤ k∧S.card+t ≤ k+1:=by
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
def represented (w:List Sig) (v:Sig) : Prop:=v ∈ w ∨ ¬proper v
lemma get_rep (w:List Sig) (i:Nat) : represented w (w.getD i zero):=by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
lemma bin_laws (a:Sig) :
    bin false a one=a∧bin true a zero=a ∧
    bin false a zero=zero∧bin true a one=one ∧
    bin false a a=a∧bin true a a=a:=by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp
lemma n8 : neg zero=one∧neg one=zero:=by simp [neg,zero,one]
lemma jn {w:List Sig} {a:Sig} (h:represented w a) :
    a=zero∨a=one∨a ∈ w∧proper a:=by
  by_cases hz : a=zero
  · exact Or.inl hz
  by_cases ho : a=one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def witness (w:List Sig) (z:Sig) : Prop :=
  (∃ a ∈ w,proper a∧z=neg a) ∨
  (∃ d a b,a ∈ w∧b ∈ w∧proper a∧proper b∧a ≠ b∧z=bin d a b)
lemma bin_rep {w a b} (d:Bool) (ha:represented w a) (hb:represented w b) :
    represented w (bin d a b)∨witness w (bin d a b):=by
  have rz : represented w zero:=Or.inr (fun h => h.1 rfl)
  have ro : represented w one:=Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases jn ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm];cases d <;> simp_all
  · rw [bin_comm];cases d <;> simp_all
  rcases jn hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b;cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
def isNotT (op:GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false
lemma xj (w:List Sig) (g:Gate)
    (hg:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2) :
    represented w (gv w g) ∨
      (if isNotT g.op then ∃ a,a∈w∧proper a∧gv w g=neg a
       else ∃ d a b,a∈w∧b∈w∧proper a∧proper b∧a≠b∧gv w g=bin d a b):=by
  have nx (a:Sig) (ha:represented w a) : represented w (neg a) ∨ ∃ x,x∈w∧proper x∧neg a=neg x:=by
    rcases jn ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (Or.inr fun h => h.2 n8.1)
    · exact Or.inl (Or.inr fun h => h.1 n8.2)
    · exact Or.inr ⟨a,hm,hp,rfl⟩
  have bn (d:Bool) (a b:Sig) (ha:represented w a) (hb:represented w b) :
      represented w (bin d a b) ∨ ∃ d' x y,x∈w∧y∈w∧proper x∧proper y∧x≠y∧bin d a b=bin d' x y:=by
    have bzero : ∀ v,bin false v zero=zero∧bin true v zero=v:=fun v => ⟨(bin_laws v).2.2.1,(bin_laws v).2.1⟩
    have bone : ∀ v,bin false v one=v∧bin true v one=one:=fun v => ⟨(bin_laws v).1,(bin_laws v).2.2.2.1⟩
    rcases jn ha with rfl | rfl | ⟨hma,hpa⟩
    · rw [bin_comm]
      cases d
      · exact Or.inl (Or.inr fun h => h.1 (bzero b).1)
      · rw [(bzero b).2];exact Or.inl hb
    · rw [bin_comm]
      cases d
      · rw [(bone b).1];exact Or.inl hb
      · exact Or.inl (Or.inr fun h => h.2 (bone b).2)
    · rcases jn hb with rfl | rfl | ⟨hmb,hpb⟩
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
      have hgv : gv w g=one:=by simp only [gv,ho,hi,List.map_nil,List.headD_nil,n8.1]
      exact Or.inl (Or.inr fun h => h.2 hgv)
    | cons i t =>
      have hgv : gv w g=neg (w.getD i zero):=by simp only [gv,ho,hi,List.map_cons,List.headD_cons]
      rw [hgv];exact nx _ (get_rep w i)
lemma pull_gateT {w:List Sig} {z:Sig} {k t S} (isN:Bool) (h:Live fu k t S)
    (hz:represented w z ∨
      (if isN then ∃ a,a∈w∧proper a∧z=neg a
       else ∃ d a b,a∈w∧b∈w∧proper a∧proper b∧a≠b∧z=bin d a b))
    (sub:∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1∧t' ≤ t+isN.toNat∧Live fu k' t' S' ∧ ∀ a ∈ S',a ∈ w:=by
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
          have ht : Live fu k t (insert (neg a) U):=by simpa [U,Finset.insert_erase hm] using h
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
          have ht : Live fu k t (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
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
    (legal:∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2)
    (hp:proper fu) (hout:fu ∈ execute gs w) :
    ∃ k t S,k ≤ gs.length∧t ≤ gs.countP (fun g => isNotT g.op)∧Live fu k t S ∧ ∀ a ∈ S,a ∈ w:=by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{fu},by simp,by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hl,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl',hu',hlu,hT⟩ := pull_gateT (isNotT g.op) hl (xj w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp;omega,?_,hlu,hT⟩;simp only [List.countP_cons]
    cases h : isNotT g.op <;> simp [h] at hu' ⊢ <;> omega
lemma xk {w:List Sig} {z:Sig} {k t S} (h:Live fu k t S)
    (hz:represented w z∨witness w z) (sub:∀ a ∈ S,a ∈ w ++ [z]) :
    ∃ k' t' S',k' ≤ k+1∧Live fu k' t' S' ∧ ∀ a ∈ S',a ∈ w:=by
  rcases hz with hr | (hu | hb)
  · obtain ⟨k',t',S',hk,_,hl,hs⟩ := pull_gateT false h (Or.inl hr) sub;exact ⟨k',t',S',hk,hl,hs⟩
  · obtain ⟨k',t',S',hk,_,hl,hs⟩ := pull_gateT true h (Or.inr hu) sub;exact ⟨k',t',S',hk,hl,hs⟩
  · obtain ⟨k',t',S',hk,_,hl,hs⟩ := pull_gateT false h (Or.inr hb) sub;exact ⟨k',t',S',hk,hl,hs⟩
def bit (i:Fin 512) (a:Sig) : Bool:=a.getLsbD i.val
lemma jj (i) : bit i zero=false:=by simp [bit,zero]
lemma mo (i) : bit i one=true:=by unfold bit one;rw [BitVec.getLsbD_allOnes];simp
lemma bit_neg (i) (a:Sig) : bit i (neg a) = !(bit i a):=by simp [bit,neg,i.isLt]
lemma bit_bin (i d) (a b:Sig) : bit i (bin d a b) =
    (if d then bit i a||bit i b else bit i a&&bit i b):=by cases d <;> simp [bit,bin]
lemma b_read (i) (w:List Sig) (j:Nat) :
    (w.map (bit i)).getD j false=bit i (w.getD j zero):=by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (jj _).symm
  | some a => rfl
lemma b5 (i) (g:Gate) (w:List Sig)
    (hg:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g)=g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false):=by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg;simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact mo _
    | cons a l ih =>
      change bit i (bin false _ _)=(_&&_);rw [bit_bin];exact congrArg (fun x => bit i (w.getD a zero)&&x) ih
  · induction l with
    | nil => exact jj _
    | cons a l ih =>
      change bit i (bin true _ _)=(_||_);rw [bit_bin];exact congrArg (fun x => bit i (w.getD a zero)||x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false;rw [bit_neg,jj]
    | cons a l => exact bit_neg _ _
lemma execute_bits (gs:List Gate) (i) (w:List Sig)
    (hg:∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l:List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)):=by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _=_;rw [ih _ (fun a ha => hg a (by simp [ha]))];simp only [List.foldl_cons,List.map_append,List.map_singleton,b5 i g w (hg g (by simp))]
abbrev fp (R:Type):=R→ Bool
def t5 {R} (a:fp R) : fp R:=fun r => !(a r)
def g0 {R} (isOr:Bool) (a b:fp R) : fp R :=
  if isOr then fun r => a r||b r else fun r => a r&&b r
def fy {R} (a:fp R) : Prop := ∃ b : Bool,a=fun _ => b
noncomputable def n9 {R} (a:fp R) : Nat:=by
  classical exact if fy a then 1 else 0
noncomputable def mq {R} (xs:List (fp R)) : Nat:=(xs.map n9).sum
def fc {R} (pool:List (fp R)) (v:fp R) : Prop:=v ∈ pool∨fy v
def m6 {R} (pool xs:List (fp R)) := ∀ a ∈ xs,fc pool a
def fv {R} (roots:List (fp R)) : Nat→ List (fp R)→ Prop:=fun p f8 =>
  ∀ (M:(Nat→ List (fp R)→ Prop)),(M 0 roots) →
  (∀ {p:Nat} {f8:List (fp R)} {a:fp R},M p f8→ fc f8 a→ M (p+1) (t5 a :: f8)) →
  (∀ {p:Nat} {f8:List (fp R)} {a b:fp R} (op:Bool),M p f8→ fc f8 a→ fc f8 b→ M (p+1) (g0 op a b :: f8)) →
  M p f8
lemma fv.start {R} {roots:List (fp R)}   : fv roots 0 roots:=fun M start one two => @start
lemma fv.one {R} {roots:List (fp R)} {p:Nat} {f8:List (fp R)} {a:fp R} (h0:fv roots p f8) (h1:fc f8 a) : fv roots (p+1) (t5 a :: f8):=fun M start one two => @one p f8 a (h0 M start one two) h1
lemma fv.two {R} {roots:List (fp R)} {p:Nat} {f8:List (fp R)} {a b:fp R} (op:Bool) (h0:fv roots p f8) (h1:fc f8 a) (h2:fc f8 b) : fv roots (p+1) (g0 op a b :: f8):=fun M start one two => @two p f8 a b op (h0 M start one two) h1 h2
lemma fv.induct {R} {roots:List (fp R)} {M:(Nat→ List (fp R)→ Prop)} {p f8} (h:fv roots p f8)
  (start:M 0 roots)
  (one:∀ {p:Nat} {f8:List (fp R)} {a:fp R},fv roots p f8→ M p f8→ fc f8 a→ M (p+1) (t5 a :: f8))
  (two:∀ {p:Nat} {f8:List (fp R)} {a b:fp R} (op:Bool),fv roots p f8→ M p f8→ fc f8 a→ fc f8 b→ M (p+1) (g0 op a b :: f8)) : M p f8 :=
  (h (fun p f8 => fv roots p f8∧M p f8)
  (⟨@fv.start R roots  ,@start  ⟩)
  (@fun p f8 a h0 h1 => ⟨@fv.one R roots p f8 a h0.1 h1,@one p f8 a h0.1 h0.2 h1⟩)
  (@fun p f8 a b op h0 h1 h2 => ⟨@fv.two R roots p f8 a b op h0.1 h1 h2,@two p f8 a b op h0.1 h0.2 h1 h2⟩)).2
lemma fv.recurse {R} {roots:List (fp R)} {M:∀ (p:Nat) (f8:List (fp R)) (proof:fv roots p f8),Prop}
  (start:M 0 roots (@fv.start R roots  ))
  (one:∀ {p:Nat} {f8:List (fp R)} {a:fp R} (h0:fv roots p f8) (ih:M p f8 h0) (h2:fc f8 a),M (p+1) (t5 a :: f8) (@fv.one R roots p f8 a h0 h2))
  (two:∀ {p:Nat} {f8:List (fp R)} {a b:fp R} (op:Bool) (h0:fv roots p f8) (ih:M p f8 h0) (h2:fc f8 a) (h3:fc f8 b),M (p+1) (g0 op a b :: f8) (@fv.two R roots p f8 a b op h0 h2 h3))
  {p f8} (h:fv roots p f8) : M p f8 h:=by
  have r:=fv.induct (M:=fun p f8 => ∀ hh : fv roots p f8,M p f8 hh) h
    (fun  _ => @start  )
    (@fun p f8 a h0 h1 h2 _ => @one p f8 a h0 (h1 h0) h2)
    (@fun p f8 a b op h0 h1 h2 h3 _ => @two p f8 a b op h0 (h1 h0) h2 h3)
  exact r h
def g6 {α : Type} (save:Bool) (x : α) (xs:List α):=if save then x::xs else xs
def kw {R} (goal:fp R) : Nat→ List (fp R)→ Prop:=fun s ws =>
  ∀ (M:(Nat→ List (fp R)→ Prop)),(M 0 [goal]) →
  (∀ {s:Nat} {xs zs:List (fp R)},xs.Perm zs→ M s xs→ M s zs) →
  (∀ {s:Nat} {a:fp R} {rest:List (fp R)} (save:Bool),M s (t5 a :: g6 save a rest)→ M (s+1) (a::rest)) →
  (∀ {s:Nat} {a b:fp R} {rest:List (fp R)} (op ka kb:Bool),M s (g0 op a b :: g6 ka a (g6 kb b rest))→ M (s+1) (a::b::rest)) →
  M s ws
lemma kw.stop {R} {goal:fp R}   : kw goal 0 [goal]:=fun M stop perm one two => @stop
lemma kw.perm {R} {goal:fp R} {s:Nat} {xs zs:List (fp R)} (h0:xs.Perm zs) (h1:kw goal s xs) : kw goal s zs:=fun M stop perm one two => @perm s xs zs h0 (h1 M stop perm one two)
lemma kw.one {R} {goal:fp R} {s:Nat} {a:fp R} {rest:List (fp R)} (save:Bool) (h0:kw goal s (t5 a :: g6 save a rest)) : kw goal (s+1) (a::rest):=fun M stop perm one two => @one s a rest save (h0 M stop perm one two)
lemma kw.two {R} {goal:fp R} {s:Nat} {a b:fp R} {rest:List (fp R)} (op ka kb:Bool) (h0:kw goal s (g0 op a b :: g6 ka a (g6 kb b rest))) : kw goal (s+1) (a::b::rest):=fun M stop perm one two => @two s a b rest op ka kb (h0 M stop perm one two)
lemma kw.induct {R} {goal:fp R} {M:(Nat→ List (fp R)→ Prop)} {s ws} (h:kw goal s ws)
  (stop:M 0 [goal])
  (perm:∀ {s:Nat} {xs zs:List (fp R)},xs.Perm zs→ kw goal s xs→ M s xs→ M s zs)
  (one:∀ {s:Nat} {a:fp R} {rest:List (fp R)} (save:Bool),kw goal s (t5 a :: g6 save a rest)→ M s (t5 a :: g6 save a rest)→ M (s+1) (a::rest))
  (two:∀ {s:Nat} {a b:fp R} {rest:List (fp R)} (op ka kb:Bool),kw goal s (g0 op a b :: g6 ka a (g6 kb b rest))→ M s (g0 op a b :: g6 ka a (g6 kb b rest))→ M (s+1) (a::b::rest)) : M s ws :=
  (h (fun s ws => kw goal s ws∧M s ws)
  (⟨@kw.stop R goal  ,@stop  ⟩)
  (@fun s xs zs h0 h1 => ⟨@kw.perm R goal s xs zs h0 h1.1,@perm s xs zs h0 h1.1 h1.2⟩)
  (@fun s a rest save h0 => ⟨@kw.one R goal s a rest save h0.1,@one s a rest save h0.1 h0.2⟩)
  (@fun s a b rest op ka kb h0 => ⟨@kw.two R goal s a b rest op ka kb h0.1,@two s a b rest op ka kb h0.1 h0.2⟩)).2
lemma kw.recurse {R} {goal:fp R} {M:∀ (s:Nat) (ws:List (fp R)) (proof:kw goal s ws),Prop}
  (stop:M 0 [goal] (@kw.stop R goal  ))
  (perm:∀ {s:Nat} {xs zs:List (fp R)} (h0:xs.Perm zs) (h1:kw goal s xs) (ih:M s xs h1),M s zs (@kw.perm R goal s xs zs h0 h1))
  (one:∀ {s:Nat} {a:fp R} {rest:List (fp R)} (save:Bool) (h0:kw goal s (t5 a :: g6 save a rest)) (ih:M s (t5 a :: g6 save a rest) h0),M (s+1) (a::rest) (@kw.one R goal s a rest save h0))
  (two:∀ {s:Nat} {a b:fp R} {rest:List (fp R)} (op ka kb:Bool) (h0:kw goal s (g0 op a b :: g6 ka a (g6 kb b rest))) (ih:M s (g0 op a b :: g6 ka a (g6 kb b rest)) h0),M (s+1) (a::b::rest) (@kw.two R goal s a b rest op ka kb h0))
  {s ws} (h:kw goal s ws) : M s ws h:=by
  have r:=kw.induct (M:=fun s ws => ∀ hh : kw goal s ws,M s ws hh) h
    (fun  _ => @stop  )
    (@fun s xs zs h0 h1 h2 _ => @perm s xs zs h0 h1 (h2 h1))
    (@fun s a rest save h0 h1 _ => @one s a rest save h0 (h1 h0))
    (@fun s a b rest op ka kb h0 h1 _ => @two s a b rest op ka kb h0 (h1 h0))
  exact r h
lemma kz {R} (a:fp R) (xs) : mq (a::xs)=n9 a+mq xs:=by
  simp [mq]
lemma qm {R} (a:fp R) (xs) (k:Bool) : mq xs ≤ mq (g6 k a xs):=by
  cases k <;> simp [g6,kz]
lemma q4 {R} {a:fp R} (h:fy a) : fy (t5 a):=by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩
lemma t6 {R} {a b:fp R} (op) (h:fy a) (g:fy b) :
    fy (g0 op a b):=by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩
lemma t7 {R} (op) {a b:fp R} {f8}
    (h:fy a∨fy b) (ha:fc f8 a) (hb:fc f8 b) :
    fc f8 (g0 op a b):=by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false,by funext x;simp [g0]⟩
    · simpa [g0] using hb
    · simpa [g0] using hb
    · exact Or.inr ⟨true,by funext x;simp [g0]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false,by funext x;simp [g0]⟩
    · simpa [g0] using ha
    · simpa [g0] using ha
    · exact Or.inr ⟨true,by funext x;simp [g0]⟩
lemma jx {R} {f8 v} (w:fp R) (h:fc f8 v) :
    fc (w::f8) v:=by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr
lemma wo {R} (roots:List (fp R)) {p f8 a} (hp:fv roots p f8)
    (ha:fc f8 a) :
    ∃ q next,fv roots q next∧fc next (t5 a) ∧
        (∀ v,fc f8 v→ fc next v)∧q+n9 a ≤ p+1+n9 (t5 a):=by
  classical
  by_cases c : fy a
  · exact ⟨p,f8,hp,Or.inr (q4 c),fun _ h => h,by simp [n9,c,q4 c]⟩
  · exact ⟨p+1,_,fv.one hp ha,Or.inl (by simp),fun _ h => jx _ h,by simp [n9,c]⟩
lemma wp {R} (roots:List (fp R)) {p f8 a b} (op) (hp:fv roots p f8)
    (ha:fc f8 a) (hb:fc f8 b) :
    ∃ q next,fv roots q next∧fc next (g0 op a b) ∧
        (∀ v,fc f8 v→ fc next v) ∧
        q+n9 a+n9 b ≤ p+1+n9 (g0 op a b):=by
  classical
  by_cases c : fy a∨fy b
  · refine ⟨p,f8,hp,t7 op c ha hb,fun _ h => h,?_⟩
    by_cases ca : fy a <;> by_cases cb : fy b
    · simp [n9,ca,cb,t6 op ca cb]
    · simp [n9,ca,cb]
    · simp [n9,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬fy a:=fun h => c (Or.inl h)
    have cb : ¬fy b:=fun h => c (Or.inr h)
    exact ⟨p+1,_,fv.two op hp ha hb,Or.inl (by simp),fun _ h => jx _ h,
      by simp [n9,ca,cb]⟩
lemma nf {α : Type} {k:Bool} {x a : α} {xs} (h:x ∈ g6 k a xs) :
    x=a∨x∈xs:=by cases k <;> simp_all [g6]
lemma vs {R} {goal:fp R} (nc : ¬fy goal) {s ws}
    (h:kw goal s ws) (roots:List (fp R)) {p f8}
    (hp:fv roots p f8) (hs:m6 f8 ws) :
    ∃ q next,fv roots q next∧fc next goal∧q+mq ws ≤ p+s:=by
  classical
  induction h using kw.recurse generalizing p f8 with
  | stop =>
    exact ⟨p,f8,hp,hs _ (by simp),by simp [mq,n9,nc]⟩
  | perm eq _ ih =>
    have hsub : m6 f8 _:=fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mq,←(eq.map n9).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := wo roots hp (hs a (by simp))
    have ht : m6 T (t5 a :: g6 save a rest):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (nf hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen:=qm a rest save
    rw [kz] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := wp roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : m6 T (g0 op a b :: g6 ka a (g6 kb b rest)):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases nf hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (nf hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen:=qm a (g6 kb b rest) ka
    have hlen' := qm b rest kb
    rw [kz] at hl;refine ⟨q,W,hW,hv,?_⟩;rw [kz,kz];omega
def f6 {R S:Type} (rows:S→ R) (a:fp R) : fp S :=
  fun r => a (rows r)
lemma pn {R S:Type} (rows:S→ R) (k:Bool) (a:fp R) (ws) :
    (g6 k a ws).map (f6 rows) =
    g6 k (f6 rows a) (ws.map (f6 rows)):=by
  cases k <;> simp [g6]
lemma tz {R S:Type} (rows:S→ R) {goal s ws} (h:kw goal s ws) :
    kw (f6 rows goal) s (ws.map (f6 rows)):=by
  induction h using kw.recurse with
  | stop => exact kw.stop
  | perm p _ ih => exact kw.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,pn] at ih ⊢
    exact kw.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,pn] at ih ⊢
    cases op
    · exact kw.two false ka kb ih
    · exact kw.two true ka kb ih
lemma jk {R S:Type} (rows:S→ R) {goal s ws} (h:kw goal s ws)
    (nc : ¬fy (f6 rows goal)) {roots:List (fp S)} {p f8 L}
    (hp:fv roots p f8) (hs:m6 f8 (ws.map (f6 rows)))
    (hl:∀ q bs,fv roots q bs→ fc bs (f6 rows goal)→ L ≤ q) :
    L+mq (ws.map (f6 rows)) ≤ p+s:=by
  obtain ⟨q,bs,hq,ht,hle⟩ := vs nc (tz rows h) roots hp hs
  have hqle:=hl q bs hq ht
  omega
abbrev Row:=Fin 512
def f7 (a:Sig) : fp Row:=fun r => bit r a
def kr (f:fp Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
lemma m8 (f:fp Row) (r:Row) : bit r (kr f)=f r:=by
  simp only [bit,kr,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn];simp [r.isLt]
lemma kf (v:Sig) : kr (f7 v)=v:=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj;exact m8 (f7 v) ⟨j,hj⟩
lemma m7 (f:fp Row) : f7 (kr f)=f:=by
  funext r;exact m8 f r
lemma v1 (a:Sig) : f7 (neg a)=t5 (f7 a):=by
  funext r;exact bit_neg _ _
lemma q5 (d:Bool) (a b:Sig) :
    f7 (bin d a b)=g0 d (f7 a) (f7 b):=by
  funext r
  cases d <;> exact bit_bin _ _ _ _
lemma ry {α β : Type} (f : α → β) (d:Bool) (a : α) (l:List α) :
    (g6 d a l).map f=g6 d (f a) (l.map f):=by cases d <;> rfl
lemma k7 {α : Type} (k:Bool) (a : α) (l:List α)
    (hn:l.Nodup) (ha:a ∉ l) : (g6 k a l).Nodup:=by cases k <;> simp [g6,hn,ha]
lemma m9 (k:Bool) (a:Sig) (l:List Sig) :
    (g6 k a l).toFinset=if k then insert a l.toFinset else l.toFinset:=by
  cases k <;> simp [g6]
lemma s0 {T:Sig} {k u S} (h:Live T k u S) (v:List Sig)
    (hv:v.Nodup) (eqv:v.toFinset=S) : kw (f7 T) k (v.map f7):=by
  classical
  induction h using Live.recurse generalizing v with
  | stop hp =>
    have eq : [T].Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv;simpa [eqv]
    exact kw.perm (eq.map _) kw.stop
  | @unary k u U a ha gi _ ih =>
    let rest:=(U.erase a).toList
    let save:=decide (a ∈ U)
    let tail:=g6 save a rest
    have er : rest.toFinset=U.erase a:=by simp [rest]
    have hm : a ∉ rest:=by simp [rest]
    have hr : rest.Nodup:=Finset.nodup_toList _
    have ht : tail.toFinset=U:=by
      rw [show tail=g6 save a rest by rfl,m9,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd:=k7 save a rest hr hm
    have hf : neg a ∉ tail:=by
      intro hz;exact gi (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress:=ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,ry,v1] at progress
    have perm : (a::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv;simp [er,eqv]
    exact kw.perm (perm.map _) (kw.one save progress)
  | @binary k u U a b d ha hb hab gi _ ih =>
    let rest:=((U.erase a).erase b).toList
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let mid:=g6 kb b rest
    let tail:=g6 ka a mid
    have er : rest.toFinset=(U.erase a).erase b:=by simp [rest]
    have ar : a ∉ rest:=by simp [rest]
    have br : b ∉ rest:=by simp [rest]
    have hr : rest.Nodup:=Finset.nodup_toList _
    have bm:=k7 kb b rest hr br
    have am : a ∉ mid:=by cases h : kb <;> simp [mid,g6,h,hab,ar]
    have nd:=k7 ka a mid bm am
    have ht : tail.toFinset=U:=by
      change (g6 ka a (g6 kb b rest)).toFinset=U;rw [m9,m9,er];ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail:=by
      intro hz;exact gi (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress:=ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change kw _ _ ((bin d a b::g6 ka a (g6 kb b rest)).map f7) at progress;rw [List.map_cons,ry,ry,q5] at progress
    have perm : (a::b::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv;ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact kw.perm (perm.map _) (kw.two d ka kb progress)
lemma xl (f:fp Row) : kr (t5 f)=neg (kr f):=by
  rw [←kf (neg (kr f)),v1,m7]
lemma xm (d:Bool) (f g:fp Row) :
    kr (g0 d f g)=bin d (kr f) (kr g):=by
  rw [←kf (bin d (kr f) (kr g)),q5,m7,m7]
lemma kg {f8:List (fp Row)} {a} (h:fc f8 a) :
    represented (f8.map kr) (kr a):=by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : kr (fun _ => false)=zero:=by
        apply BitVec.eq_of_getLsbD_eq;intro j hj;exact (m8 _ ⟨j,hj⟩).trans (jj ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : kr (fun _ => true)=one:=by
        apply BitVec.eq_of_getLsbD_eq;intro j hj;exact (m8 _ ⟨j,hj⟩).trans (mo ⟨j,hj⟩).symm
      exact fun hp => hp.2 z
lemma b6 {w a} (ha:represented w a) :
    represented w (neg a)∨witness w (neg a):=by
  rcases jn ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 n8.1)
  · exact Or.inl (Or.inr fun h => h.1 n8.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
lemma tk {w:List Sig} {z:Sig} {T k t S} (h:Live T k t S)
    (hz:represented w z∨witness w z) (hs:∀ a ∈ S,a ∈ z::w) :
    ∃ k' t' S',k' ≤ k+1∧Live T k' t' S' ∧ ∀ a ∈ S',a ∈ w:=by
  apply xk h hz;intro a hm;simpa [or_comm] using hs a hm
lemma s1 {roots:List (fp Row)} {p f8}
    (h:fv roots p f8) {T k t S} (run:Live T k t S)
    (sub:∀ a ∈ S,a ∈ f8.map kr) :
    ∃ l v U,l ≤ p+k∧Live T l v U ∧ ∀ a ∈ U,a ∈ roots.map kr:=by
  induction h using fv.recurse generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p f8 a h ih ha =>
    rw [List.map_cons,xl] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := tk run (b6 (kg ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p f8 a b d h ih ha hb =>
    rw [List.map_cons,xm] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := tk run (bin_rep d (kg ha) (kg hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
lemma pt {roots:List Sig} {p f8 T} (hp:proper T)
    (h:fv (roots.map f7) p f8) (hit:fc f8 (f7 T)) :
    ∃ k t S,k ≤ p∧Live T k t S ∧ ∀ a ∈ S,a ∈ roots:=by
  have hm:=kg hit
  rw [kf] at hm
  have mem:=hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := s1 h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩;simpa [List.map_map,Function.comp_def,kf] using hs
lemma lf {T k t S} (h:Live T k t S) {r s:Row}
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
    (a8:∀ v ∈ roots,v ≠ a→ bit r v=bit s v) : a ∈ S:=by
  obtain ⟨v,hv,hd⟩ := lf h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (a8 v (sub v hv) veq))
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
def g8 (f:Row→ Row) (a:Sig):=kr fun r => bit (f r) a
lemma gl (f:Row→ Row) (a:Sig) (r:Row) :
    bit r (g8 f a)=bit (f r) a:=m8 _ _
lemma jy (f:Row→ Row) (a:Sig) :
    f7 (g8 f a)=f6 f (f7 a):=by funext r;exact gl f a r
lemma s2 (f:Row→ Row) (a:Sig) : g8 f (neg a)=neg (g8 f a):=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj;change bit ⟨j,hj⟩ (g8 f (neg a))=bit ⟨j,hj⟩ (neg (g8 f a));rw [gl,bit_neg,bit_neg,gl]
lemma s3 (f:Row→ Row) (d:Bool) (a b:Sig) :
    g8 f (bin d a b)=bin d (g8 f a) (g8 f b):=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj;change bit ⟨j,hj⟩ (g8 f (bin d a b))=bit ⟨j,hj⟩ (bin d (g8 f a) (g8 f b));rw [gl,bit_bin,bit_bin,gl,gl]
lemma wq (f:Row→ Row) (onto:Function.Surjective f) :
    Function.Injective (g8 f):=by
  intro a b h;apply BitVec.eq_of_getLsbD_eq;intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he:=congrArg (bit r) h
  change bit ⟨j,hj⟩ a=bit ⟨j,hj⟩ b;rw [gl,gl,hr] at he;exact he
lemma ma (f:Row→ Row) : g8 f zero=zero∧g8 f one=one:=by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (gl f zero ⟨j,hj⟩).trans ((jj _).trans (jj ⟨j,hj⟩).symm)
  · exact (gl f one ⟨j,hj⟩).trans ((mo _).trans (mo ⟨j,hj⟩).symm)
lemma vt {T k t S} (h:Live T k t S) (f:Row→ Row) (onto:Function.Surjective f) :
    Live (g8 f T) k t (S.image (g8 f)):=by
  have inj:=wq f onto
  obtain ⟨fz,fo⟩ := ma f
  have pp (v) (p:proper v) : proper (g8 f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.recurse with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have gi : g8 f (neg a) ∉ (insert a U).image (g8 f):=by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,s2] at gi ih ⊢
    exact Live.unary (pp _ hp) gi ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have gi : g8 f (bin d a b) ∉ (insert a (insert b U)).image (g8 f):=by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,s3] at gi ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) gi ih
lemma pk {T k t S} (h:Live T k t S) (none:t=0) {r s:Row}
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
def j3 (roots:List Sig) (T:Sig) (L:Nat) : Prop :=
  ∀ p f8,fv (roots.map f7) p f8→ fc f8 (f7 T)→ L ≤ p
def Impossible (T:Sig) (cap:Nat) (S:Finset Sig) : Prop :=
  ∀ k t,k ≤ cap→ ¬Live T k t S
def p8 (T:Sig) (roots:List Sig) (a:Sig) : Prop :=
  ∃ r s : Row,bit r T ≠ bit s T ∧ ∀ v ∈ roots,v ≠ a→ bit r v=bit s v
lemma mb {roots T L} (hp:proper T)
    (z6:∀ a ∈ roots,p8 T roots a)
    (noRun:Impossible T L roots.toFinset) : j3 roots T (L+1):=by
  intro p f8 h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := pt hp h ha
  have he : roots.toFinset=S:=by
    ext a;rw [List.mem_toFinset];refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := z6 _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! tx
  exact noRun k t (by omega) (he.symm ▸ run)
lemma ng {v:Sig} (hv:proper v) : ¬fy (f7 v):=by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v:=by
    have avail : fc ([] : List (fp Row)) (f7 v):=Or.inr ⟨b,h⟩
    simpa only [List.map_nil,kf] using kg avail
  exact (hr.resolve_left (by simp)) hv
lemma vu {R} (a b:List (fp R)) : mq (a++b)=mq a+mq b:=by
  simp [mq]
lemma s4 {R} (xs:List (fp R)) (hc:∀ x ∈ xs,fy x) :
    mq xs=xs.length:=by
  induction xs with
  | nil => simp [mq]
  | cons a xs ih =>
    have ha:=hc a (by simp)
    simp only [kz,List.length_cons,n9,if_pos ha,ih (fun x hx => hc x (by simp [hx]))];omega
lemma re {roots a9:List Sig} {T G:Sig} (pT:proper T) (pG:proper G)
    (r:Row→ Row) (eq:g8 r T=G)
    (fk:∀ a ∈ roots,fc (a9.map f7) (f7 (g8 r a)))
    (lm:Finset Sig) (z5:∀ a ∈ lm,p8 T roots a)
    (constant:∀ a ∈ lm,fy (f7 (g8 r a)))
    (L:Nat) (jv:j3 a9 G L) : j3 roots T (L+lm.card):=by
  classical
  intro p f8 hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := pt pT hh ha
  have subS : lm ⊆ S:=by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := z5 a hs
    exact raw_required run roots a sub i j hd hiso
  let rk:=lm.toList ++ (S \ lm).toList
  have nd : rk.Nodup:=by
    simp only [rk,List.nodup_append];refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩;intro a ha b hb he;subst b;exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : rk.toFinset=S:=by ext a;simp [rk,Finset.union_sdiff_of_subset subS]
  have run' := s0 run rk nd fe
  have gc : f6 r (f7 T)=f7 G:=(jy _ _).symm.trans (congrArg f7 eq)
  have supp : m6 (a9.map f7) ((rk.map f7).map (f6 r)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←jy];exact fk a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound:=jk r run' (gc ▸ ng pG) fv.start supp
    (L:=L) (gc ▸ jv)
  have massLo : lm.card ≤ mq ((rk.map f7).map (f6 r)):=by
    simp only [rk,List.map_append,vu]
    let xs:=(lm.toList.map f7).map (f6 r)
    have only : ∀ v ∈ xs,fy v:=by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←jy];exact constant _ (Finset.mem_toList.mp hmem)
    have sz:=s4 xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz;change lm.card ≤ mq xs+_;rw [sz];omega
  omega
def gg (ws:List Sig) (a:Sig) (keep:Bool) : List Sig :=
  neg a :: g6 keep a (ws.erase a)
def fw (ws:List Sig) (a b:Sig) (d ka kb:Bool) : List Sig :=
  bin d a b :: g6 ka a (g6 kb b ((ws.erase a).erase b))
lemma qn {l:List Sig} (h:l.Nodup) (a:Sig) : (l.erase a).toFinset=l.toFinset.erase a:=by
  ext x;simp [h.mem_erase_iff]
def Sep (T:Sig) (h9:Nat) (pos negRow:Fin h9→ Row)
    (asig:Sig→ BitVec h9 × BitVec h9) : Prop :=
  (∀ i,bit (pos i) T=true∧bit (negRow i) T=false) ∧
  ∀ w i,(asig w).1.getLsbD i.val=bit (pos i) w ∧
    (asig w).2.getLsbD i.val=bit (negRow i) w
def fq {n} (oriented:Bool) (s:BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def fk {n} (oriented:Bool) (sig:Sig→ BitVec n × BitVec n) : List Sig→ BitVec n
  | [] => 0
  | a::ws => fq oriented (sig a) ||| fk oriented sig ws
lemma jz {n:Nat} {oriented:Bool} {sig:Sig→ BitVec n × BitVec n} {ws:List Sig} {i:Fin n} :
    (fk oriented sig ws).getLsbD i.val=true ↔
    ∃ a ∈ ws,(fq oriented (sig a)).getLsbD i.val=true:=by
  induction ws with
  | nil => simp [fk]
  | cons a ws ih =>
    simp only [fk,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
lemma rf {T k t S} (h:Live T k t S) {ws:List Sig} (he:ws.toFinset=S)
    {h9:Nat} {r s:Fin h9→ Row} {sig} (correct:Sep T h9 r s sig)
    (oriented:Bool) (zeroNot:oriented=true→ t=0) :
    fk oriented sig ws=BitVec.allOnes h9:=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj
  let i : Fin h9:=⟨j,hj⟩
  have yes:=(correct.1 i).1
  have no:=(correct.1 i).2
  rw [BitVec.getLsbD_allOnes];simp only [hj,decide_true];apply (jz (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := lf h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩;simp only [fq,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := pk h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩;simp only [fq,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
def rg (raw:List Sig) (T d:Sig) (L:Nat) : Prop :=
  ∃ (f:Row→ Row) (roots:List Sig),(∀ r,bit (f r) d=true) ∧
    (∀ a ∈ raw,fc (roots.map f7) (f6 f (f7 a))) ∧
    ¬fy (f6 f (f7 T)) ∧
    ∀ p f8,fv (roots.map f7) p f8→ fc f8 (f6 f (f7 T))→ L ≤ p
def k0 (d a:Sig):=a &&& d
def fd (d:Sig) (pool:List Sig) (a:Sig) :=
  let m:=k0 d a
  m == zero||m == d||(pool.map (k0 d)).any (fun v => v==m)
lemma xn {f:Row→ Row} {d a b:Sig} (dom:∀ r,bit (f r) d=true)
    (eq:k0 d a=k0 d b) :
    f6 f (f7 a)=f6 f (f7 b):=by
  funext r
  have h:=congrArg (bit (f r)) eq
  change bit (f r) a=bit (f r) b;simpa only [bit,k0,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using h
lemma rh {f:Row→ Row} {d a:Sig} (dom:∀ r,bit (f r) d=true)
    (eq:k0 d a=zero) : f6 f (f7 a)=fun _ => false:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=false;rw [jj] at he;simpa only [bit,k0,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
lemma s5 {f:Row→ Row} {d a:Sig} (dom:∀ r,bit (f r) d=true)
    (eq:k0 d a=d) : f6 f (f7 a)=fun _ => true:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=true;rw [dom r] at he;simpa only [bit,k0,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
def je (f:Row→ Row) (f8:List (fp Row)) (pool:List Sig) :=
  ∀ a ∈ pool,fc f8 (f6 f (f7 a))
lemma g2 {f:Row→ Row} {d a:Sig} {f8 pool}
    (dom:∀ r,bit (f r) d=true) (supplyB:je f f8 pool)
    (check:fd d pool a=true) : fc f8 (f6 f (f7 a)):=by
  simp only [fd,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,rh dom hz⟩
  · exact Or.inr ⟨true,s5 dom ho⟩
  · exact xn dom he ▸ supplyB v hv
abbrev l0:=Nat × Sig × Sig
def choiceVal (c:l0) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def j5 (d:Sig) (pool:List Sig) (c:l0) :=
  fd d pool c.2.1&&(c.1==2||fd d pool c.2.2)
lemma pu {f:Row→ Row} {d:Sig} {roots f8 pool q}
    (dom:∀ r,bit (f r) d=true) (hp:fv roots q f8) (hs:je f f8 pool)
    (c:l0) (lz:j5 d pool c=true) :
    ∃ next,fv roots (q+1) next∧je f next (choiceVal c :: pool):=by
  have ok : fd d pool c.2.1=true∧(c.1==2||fd d pool c.2.2)=true:=by simpa only [j5,Bool.and_eq_true] using lz
  have ha:=g2 dom hs ok.1
  let z:=f6 f (f7 (choiceVal c))
  have hz : fv roots (q+1) (z::f8):=by
    by_cases unary : c.1=2
    · change fv _ _ (f6 f (f7 (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,v1];exact fv.one hp ha
    · have hb : fd d pool c.2.2=true:=by simpa [unary] using ok.2
      have hz' := fv.two (c.1==1) hp ha (g2 dom hs hb)
      change fv _ _ (f6 f (f7 (choiceVal c)) :: _);rw [choiceVal,if_neg unary,q5]
      have comm (b:Bool) (v w:fp Row) : f6 f (g0 b v w)=g0 b (f6 f v) (f6 f w):=by cases b <;> rfl
      rw [comm];exact hz'
  refine ⟨_,hz,?_⟩;intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact jx _ (hs _ hm)
def ks (d:Sig) (pool:List Sig) : List l0→ Option (List Sig)
  | [] => some pool
  | c::cs => if j5 d pool c then ks d (choiceVal c::pool) cs else none
lemma nh {d:Sig} {f:Row→ Row} (dom:∀ r,bit (f r) d=true)
    {roots f8 q pool} (hp:fv roots q f8) (hs:je f f8 pool)
    (cs:List l0) {result} (ok:ks d pool cs=some result) :
    ∃ next,fv roots (q+cs.length) next∧je f next result:=by
  induction cs generalizing f8 q pool with
  | nil => cases ok;exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [ks] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pu dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def f5 (d a:Sig):=k0 d a == zero||k0 d a == d
lemma kk {d:Sig} {f:Row→ Row} (dom:∀ r,bit (f r) d=true)
    (ws:List Sig) : ws.countP (f5 d) ≤ mq ((ws.map f7).map (f6 f)):=by
  classical
  induction ws with
  | nil => simp [mq]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,kz]
    cases h : f5 d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : fy (f6 f (f7 a)):=by
        have hh : k0 d a=zero∨k0 d a=d:=by simpa only [f5,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,rh dom hz⟩
        · exact ⟨true,s5 dom ho⟩
      simpa [n9,hc,Nat.add_comm] using Nat.succ_le_succ ih
def rt (d:Sig) (L k p:Nat) (pool ws:List Sig) :=
  decide (k+p < L+ws.countP (f5 d))&&ws.all (fd d pool)
lemma t8 {raw T d L} (slice:rg raw T d L) (cs:List l0)
    {pool ws cap} (built:ks d raw cs=some pool)
    (nd:ws.Nodup) (cut:rt d L cap cs.length pool ws=true) :
    Impossible T cap ws.toFinset:=by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨f8,hr,hs⟩ := nh dom (fv.start (roots:=roots.map f7)) base cs built
  simp only [rt,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : m6 f8 ((ws.map f7).map (f6 f)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact g2 dom hs (List.all_eq_true.mp all a ha)
  have b:=jk f (s0 h ws nd rfl) nc hr coveredS lo
  have massLo:=kk dom ws
  have hu:=ineq
  simp only [Nat.zero_add] at b;omega
abbrev Move:=Sig × Sig × Row
def ru (d r:Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def tl (d:Row) : Row:=Fin.ofNat 512 (512-d.val)
def v2 (m:Move) (r:Row) : Row :=
  if bit r m.1 then ru m.2.2 r else if bit r m.2.1 then ru (tl m.2.2) r else r
def mux (m a b:Sig):=(m &&& a) ||| (~~~m &&& b)
def s6 (m:Move) (a:Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (tl m.2.2).val) a)
lemma xo (d r:Row) (a:Sig) : bit r (a.rotateRight d.val)=bit (ru d r) a:=by
  unfold bit;rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [ru,h,r.isLt]
lemma z7 (p x y:Bool) : (p&&x || !p&&y)=(if p then x else y):=by cases p <;> simp
lemma b7 (r:Row) (m a b:Sig) :
    bit r (mux m a b)=if bit r m then bit r a else bit r b:=by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact z7 _ _ _
lemma z8 (r:Row) (m:Move) (a:Sig) : bit r (s6 m a)=bit (v2 m r) a:=by
  simp only [s6,b7,xo,v2]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def gq (ms:List Move) (r:Row):=ms.foldl (fun j m => v2 m j) r
def movedWord (ms:List Move) (a:Sig):=ms.foldr s6 a
lemma mc (ms:List Move) (a:Sig) (r:Row) :
    bit r (movedWord ms a)=bit (gq ms r) a:=by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (z8 r m _).trans (ih _)
lemma jl (ms:List Move) (a:Sig) : movedWord ms a=g8 (gq ms) a:=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj;exact (mc ms a ⟨j,hj⟩).trans (gl _ _ ⟨j,hj⟩).symm
def s7 (roots:List Sig) (w:Sig):=w==zero||w==one||roots.contains w
lemma vv {roots w} (ok:s7 roots w=true) :
    fc (roots.map f7) (f7 w):=by
  simp only [s7,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext jj⟩
  · exact Or.inr ⟨true,funext mo⟩
  · exact Or.inl (List.mem_map_of_mem hm)
def l8 (ms:List Move) (raw:List Sig) (T:Sig) (base:List Sig) (G:Sig) :=
  movedWord ms T == G&&raw.all (fun a => s7 base (movedWord ms a))
lemma ni {ms raw T base G} (ok:l8 ms raw T base G=true) :
    g8 (gq ms) T=G ∧
    ∀ a ∈ raw,fc (base.map f7) (f7 (g8 (gq ms) a)):=by
  simp only [l8,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,jl] at ok;exact ⟨ok.1,fun a ha => vv (ok.2 a ha)⟩
lemma xp {ms raw T base G L} (ok:l8 ms raw T base G=true)
    (pT:proper T) (pG:proper G) (hL:j3 base G L) : j3 raw T L:=by
  obtain ⟨eq,supp⟩ := ni ok
  simpa using re pT pG (gq ms) eq supp ∅ (by simp) (by simp) L hL
lemma t9 {ms raw T base G L d} (ok:l8 ms raw T base G=true)
    (all:movedWord ms d=one) (properG:proper G) (hL:j3 base G L) :
    rg raw T d L:=by
  obtain ⟨eq,supp⟩ := ni ok
  have obs : f6 (gq ms) (f7 T)=f7 G :=
    (jy _ _).symm.trans (congrArg f7 eq)
  refine ⟨gq ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←mc,all,mo]
  · intro a ha
    rw [←jy];exact supp a ha
  · rw [obs]
    exact ng properG
  · rw [obs]
    exact hL
def s8 (T:Sig) (roots:List Sig) (a:Sig) (rs:Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a||bit rs.1 w == bit rs.2 w)
lemma s9 {T roots a rs} (ok:s8 T roots a rs=true) : p8 T roots a:=by
  simp only [s8,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok;exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def gh (T:Sig) (raw:List Sig) (xs:List (Sig × Row × Row)) :=
  xs.all (fun a => s8 T raw a.1 a.2)
lemma li {T raw xs} (ok:gh T raw xs=true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset,p8 T raw a:=by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact s9 (List.all_eq_true.mp ok _ hm)
lemma ri {raw T} (properT:proper T) (xs:List (Sig × Row × Row))
    (ok:gh T raw xs=true) :
    j3 raw T ((xs.map Prod.fst).toFinset.card-1):=by
  intro p f8 hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := pt properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card:=by
    apply Finset.card_le_card;intro a ha
    obtain ⟨r,s,hd,iso⟩ := li ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound:=(kp run).2
  omega
def qo (ms:List Move) (T:Sig) (raw:List Sig) (base:List Sig) (G:Sig)
    (xs:List (Sig × Row × Row)) :=
  l8 ms raw T base G&&gh T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero||movedWord ms a.1 == one)
lemma b8 {ms T raw base G xs L} (ok:qo ms T raw base G xs=true)
    (properT:proper T) (properG:proper G) (low:j3 base G L) :
    j3 raw T (L+(xs.map Prod.fst).toFinset.card):=by
  simp only [qo,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := ni ok.1.1
  apply re properT properG _ eq supp _ (li ok.1.2) _ L low;intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh:=List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,jl] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext jj⟩
  · rw [h]
    exact ⟨true,funext mo⟩
def nj (m:Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m:Nat):=(nj m).map Prod.snd
def sa (m j:Nat):=if m.testBit j then inputs.getD j zero else zero
def graphGoal (m:Nat) : Sig :=
  let x:=sa m
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
def subcube (z o:Nat) : Sig :=
  let fixed:=z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def v3 (z o:Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x:=inputs.getD j zero
    let step:=Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v:Nat) : Move :=
  let i:=v &&& 15
  let j:=v >>> 4
  let a:=inputs.getD i zero
  let b:=inputs.getD j zero
  let d:=(1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def q6 (mask:Nat) : List (Sig × Row × Row) :=
  (nj mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))
def kl (m hints:Nat) : List (Sig × Row × Row) :=
  (nj m).map fun (i,a) =>
    let r:=1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def kt (T:Sig):=T != zero&&T != one
lemma k8 (T:Sig) (h:kt T=true) : proper T:=by
  simpa only [kt,proper,Bool.and_eq_true,bne_iff_ne] using h
def sb (m hints L:Nat) :=
  let xs:=kl m hints
  kt (graphGoal m)&&gh (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
lemma size_of {m hints L} (h:sb m hints L=true) :
    j3 (vars m) (graphGoal m) L:=by
  simp only [sb,Bool.and_eq_true,decide_eq_true_eq] at h;intro p f8 hr ha;exact h.2.trans (ri (k8 _ h.1.1) _ h.1.2 p f8 hr ha)
abbrev ColumnInfo:=Nat × Nat × Nat × Nat × Nat
def v4 (m z o:Nat):=m ^^^ (m &&& (z ||| o))
def md (m:Nat) (c:ColumnInfo) (jv:Nat→ Nat) : Bool :=
  let (z,o,q,s,L):=c
  let ms:=v3 z o
  let free:=v4 m z o
  let G:=movedWord ms (graphGoal m)
  let xs:=q6 s
  let count:=(xs.map Prod.fst).toFinset.card
  kt G&&l8 ms (vars m) (graphGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then gh G (vars free) xs&&decide (L ≤ count-1)
     else kt (graphGoal q) &&
       qo (v3 (v4 free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ jv q+count))
lemma col_sound {m:Nat} (c:ColumnInfo) (jv:Nat→ Nat)
    (lz:∀ q,j3 (vars q) (graphGoal q) (jv q))
    (ok:md m c jv=true) : rg (vars m) (graphGoal m) (subcube c.1 c.2.1) c.2.2.2.2:=by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms:=v3 z o
  let free:=v4 m z o
  let G:=movedWord ms (graphGoal m)
  let xs:=q6 s
  change (((kt G&&l8 ms (vars m) (graphGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one))&&_)=true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok;apply t9 ok.1.1.2 ok.1.2 (k8 _ ok.1.1.1);intro p f8 hr ha
  have hh:=ok.2
  by_cases hq : q=0
  · simp only [md,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (ri (k8 _ ok.1.1.1) xs hh.1 p f8 hr ha)
  · simp only [md,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (b8 hh.1.2 (k8 _ ok.1.1.1) (k8 _ hh.1.1) (lz q) p f8 hr ha)
def p9 (old rep:Nat) (swaps:List Nat) :=
  kt (graphGoal old)&&kt (graphGoal rep) &&
    l8 (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
lemma wr {old rep L swaps} (ok:p9 old rep swaps=true)
    (h:j3 (vars rep) (graphGoal rep) L) : j3 (vars old) (graphGoal old) L:=by
  simp only [p9,Bool.and_eq_true] at ok;exact xp ok.2 (k8 _ ok.1.1) (k8 _ ok.1.2) h
def boundsBefore (n1:List (Nat × Nat)) (q:Nat) :=
  ((n1.find? (fun a => a.1 == q)).map Prod.snd).getD 0
lemma before_sound (n1:List (Nat × Nat))
    (sound:∀ e ∈ n1,j3 (vars e.1) (graphGoal e.1) e.2) (q:Nat) :
    j3 (vars q) (graphGoal q) (boundsBefore n1 q):=by
  unfold boundsBefore
  cases h : n1.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he:=List.mem_of_find?_eq_some h
    have hit : (fun a:Nat × Nat => a.1 == q) e=true:=List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q:=beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev BoundPool:=(Sig) × (Nat) × (Nat) × (List Sig)
abbrev BoundPool.domain (c:BoundPool) : Sig:=c.1
abbrev BoundPool.bound (c:BoundPool) : Nat:=c.2.1
abbrev BoundPool.paid (c:BoundPool) : Nat:=c.2.2.1
abbrev BoundPool.wires (c:BoundPool) : List Sig:=c.2.2.2
def ValidPool (raw:List Sig) (T:Sig) (c:BoundPool) :=
  ∃ (f:Row→ Row) (roots:List Sig) (f8:List (fp Row)),
    (∀ r,bit (f r) c.domain=true) ∧ ¬fy (f6 f (f7 T)) ∧
    (∀ q ws,fv (roots.map f7) q ws→ fc ws (f6 f (f7 T))→ c.bound ≤ q) ∧
    fv (roots.map f7) c.paid f8∧je f f8 c.wires∧True
lemma vx {raw T d lb} (h:rg raw T d lb) (cs:List l0) {ws}
    (build:ks d raw cs=some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,jv⟩ := h
  obtain ⟨f8,hr,hs⟩ := nh dom (fv.start (roots:=roots.map f7)) sup cs build
  exact ⟨f,roots,f8,dom,nc,jv,by simpa using hr,hs,trivial⟩
lemma ta {raw T c} (lz:ValidPool raw T c) (k:Nat) (rest:List Sig)
    (p5:l0) (paid:Bool)
    (known:∀ a ∈ rest,fd c.domain c.wires a=true)
    (buy:if paid then j5 c.domain c.wires p5=true
       else fd c.domain c.wires (choiceVal p5)=true)
    (bound:k+c.paid+paid.toNat <
      c.bound+(choiceVal p5 :: rest).countP (f5 c.domain))
    (nd:(choiceVal p5 :: rest).Nodup) :
    Impossible T k (choiceVal p5 :: rest).toFinset:=by
  intro t num ht run
  obtain ⟨f,roots,f8,dom,nc,lo,hp,hs,_⟩ := lz
  let ws:=choiceVal p5::rest
  have done (n:Nat) (out:List (fp Row)) (reach:fv (roots.map f7) n out)
      (zs:je f out (choiceVal p5::rest)) (le:n=c.paid+paid.toNat) : False:=by
    have fk : m6 out ((ws.map f7).map (f6 f)):=by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b:=jk f (s0 run ws nd rfl) nc reach fk lo
    have cm:=kk dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (f5 c.domain) at bound;omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl;intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact g2 dom hs buy
    · exact g2 dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pu dom hp hs p5 buy
    apply done _ _ hr _ rfl;intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail:=g2 dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : fd c.domain c.wires a=true:=known _ hm
        have point : ∀ u ∈ c.wires,fc out (f6 f (f7 u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact g2 dom point ha
      · exact Or.inr con
def scalarPoolCut (c:BoundPool) (k:Nat) (rest:List Sig) (op:l0) :=
  let z:=choiceVal op
  let wm := !(fd c.domain c.wires z)
  ((k+c.paid+wm.toNat < c.bound+(z::rest).countP (f5 c.domain)) &&
    rest.all (fd c.domain c.wires))&&(!wm||j5 c.domain c.wires op)
lemma scalarPoolCut_sound {raw T c} (lz:ValidPool raw T c) {k rest op}
    (nd:(choiceVal op::rest).Nodup) (cut:scalarPoolCut c k rest op=true) :
    Impossible T k (choiceVal op::rest).toFinset:=by
  let wm := !(fd c.domain c.wires (choiceVal op))
  apply ta lz k rest op wm _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : fd c.domain c.wires (choiceVal op) <;> simp_all [wm]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def materialize (raw:List Sig) (cs:List l0) (d:Sig) (lb:Nat) : Option BoundPool :=
  (ks d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
lemma materialize_sound {raw T d L cs c} (slice:rg raw T d L)
    (h:materialize raw cs d L=some c) : ValidPool raw T c:=by
  unfold materialize at h
  cases he : ks d raw cs with
  | none => simp [he,Option.map] at h
  | some pool =>
    rw [he] at h;change some _=some c at h
    injection h with h
    subst c;exact vx slice cs he
abbrev Bits:=BitVec 768
abbrev lj:=Bits × Bits
abbrev ff:=Sig × lj
def km {n:Nat} (r:Fin n→ Row) (v:Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
lemma gm {n:Nat} (r:Fin n→ Row) (v:Sig) (i:Fin n) :
    (km r v).getLsbD i.val=bit (r i) v:=by
  simp only [km,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn];simp [i.isLt]
def fi (r s:Fin 768→ Row) (a:Sig) : lj:=(km r a,km s a)
def k1 (T:Sig) (r s:Fin 768→ Row) :=
  ∀ i,bit (r i) T=true∧bit (s i) T=false
lemma vy {T r s} (h:k1 T r s) : Sep T 768 r s (fi r s):=by
  exact ⟨h,fun a i => ⟨gm _ _ _,gm _ _ _⟩⟩
def fj (r s:Fin 768→ Row) (x:ff):=x.2=fi r s x.1
def v5 (x:ff) : ff:=(neg x.1,~~~x.2.1,~~~x.2.2)
def v6 (d:Bool) (x y:ff) : ff :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)
lemma pv (r:Fin 768→ Row) (a:Sig) : km r (neg a) = ~~~km r a:=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj
  have h:=gm r (neg a) ⟨j,hj⟩
  rw [bit_neg,←gm r a ⟨j,hj⟩] at h;simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
lemma wt (r:Fin 768→ Row) (d:Bool) (a b:Sig) :
    km r (bin d a b)=if d then km r a ||| km r b else km r a &&& km r b:=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj
  have h:=gm r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←gm r a ⟨j,hj⟩,←gm r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
lemma q7 {r s x} (h:fj r s x) : fj r s (v5 x):=by
  change x.2=_ at h;simp only [fj,v5,fi,pv,h]
lemma q8 {r s x y} (d) (hx:fj r s x) (hy:fj r s y) :
    fj r s (v6 d x y):=by
  change x.2=_ at hx;change y.2=_ at hy
  cases d <;> simp only [fj,v6,Bool.false_eq_true,ite_false,ite_true,fi,wt,hx,hy]
def ga (op:Nat) (x y:ff):=if op=2 then v5 x else v6 (op==1) x y
def f0 : ff:=(zero,0,0)
lemma qq (r s) : fj r s f0:=by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0:Bits).getLsbD j=(km r zero).getLsbD j
    rw [show (km r zero).getLsbD j=bit (r ⟨j,hj⟩) zero from gm _ _ ⟨j,hj⟩,jj]
    simp
  · change (0:Bits).getLsbD j=(km s zero).getLsbD j
    rw [show (km s zero).getLsbD j=bit (s ⟨j,hj⟩) zero from gm _ _ ⟨j,hj⟩,jj]
    simp
lemma mr {r s ws} (all:∀ v ∈ ws,fj r s v) (i:Nat) :
    fj r s (List.getD ws i f0):=by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact qq _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def n2 (cols:Nat→ Bits) (i:Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j:Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
lemma mu : ∀ (j:Fin 9) (r:Row),bit r (inputs.getD j.val zero)=r.val.testBit j.val:=by decide +kernel
lemma qr (cols:Nat→ Bits) (i:Fin 768) (j:Fin 9) :
    bit (n2 cols i) (inputs.getD j.val zero)=(cols j.val).getLsbD i.val:=by
  rw [mu];change (BitVec.ofBoolListLE (List.ofFn (fun h:Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val=_;simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn];simp [j.isLt]
def sd (m:Nat) (p q:Nat→ Bits) : List ff :=
  (nj m).map (fun (j,a) => (a,p j,q j))
lemma se {m j a} (h:(j,a) ∈ nj m) :
    j<9∧a=inputs.getD j zero:=by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
lemma v7 (m) (p q:Nat→ Bits) :
    ∀ a ∈ sd m p q,fj (n2 p) (n2 q) a:=by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := se hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (qr p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (gm _ _ ⟨i,hi⟩).symm
  · exact (qr q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (gm _ _ ⟨i,hi⟩).symm
def me (m:Nat) (v:Nat→ Bits) : Bits :=
  let x:=fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
lemma wu (m:Nat) (v:Nat→ Bits) (i:Fin 768) (j:Fin 9) :
    bit (n2 v i) (sa m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val:=by
  by_cases hh : m.testBit j.val=true
  · simpa [sa,hh] using qr v i j
  · simp [sa,hh,jj]
lemma v8 (m:Nat) (v:Nat→ Bits) (i:Fin 768) :
    bit (n2 v i) (graphGoal m)=(me m v).getLsbD i.val:=by
  have pos (j:Nat) (hj:j<9) : (sa m j).getLsbD (n2 v i).val=((if m.testBit j then v j else 0) : Bits).getLsbD i.val:=wu m v i ⟨j,hj⟩
  simp only [bit,graphGoal,me,BitVec.getLsbD_and,BitVec.getLsbD_or];simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev wv:=Bits × Bits × Bits
def kn (z:Bits) (c:wv) : wv :=
  (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def ft (d:Bool) (v:List ff) : wv :=
  v.foldr (fun a c => kn (fq d a.2) c) (0,0,0)
def ku (c:wv) (a:Bits) : Bits:=c.1 &&& ~~~(c.2.1 &&& a)
def mv (c:wv) (a b:Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
lemma b9 (c:wv) (a:Bits) : ku (kn a c) a=c.1:=by
  apply BitVec.eq_of_getLsbD_eq;intro i hi;simp only [ku,kn,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
lemma c2 (c:wv) (a b:Bits) : mv (kn a (kn b c)) a b=c.1:=by
  apply BitVec.eq_of_getLsbD_eq;intro i hi;simp only [mv,kn,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
lemma z9 (c:wv) (a b:Bits) : kn a (kn b c)=kn b (kn a c):=by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi;simp only [kn,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [kn,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
lemma vz (d:Bool) {l r:List ff} (h:l.Perm r) : ft d l=ft d r:=by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (kn (fq d a.2)) ih
  | swap a b t => exact z9 _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
lemma za (d:Bool) (v:List ff) {r s} (good:∀ a ∈ v,fj r s a) :
    (ft d v).1=fk d (fi r s) (v.map Prod.fst):=by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (fq d a.2 ||| (ft d v).1)=fq d (fi r s a.1) ||| _;rw [show a.2=fi r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def j1 (ws:List ff) (a:ff) (keep:Bool) :=
  if keep then ws else ws.erase a
def px (ws:List ff) (a b:ff) (ka kb:Bool) :=
  j1 (j1 ws a ka) b kb
lemma nl {ws:List ff} (a:ff) (ha:a ∈ ws) :
    ws.Perm (a::ws.erase a):=List.perm_cons_erase ha
lemma qs {ws:List ff} (d:Bool) (a:ff) (ha:a ∈ ws) (keep:Bool) :
    (ft d (j1 ws a keep)).1 =
      (if keep then (ft d ws).1 else ku (ft d ws) (fq d a.2)):=by
  cases keep
  · change (ft d (ws.erase a)).1=ku (ft d ws) _
    rw [vz d (nl a ha)];exact (b9 _ _).symm
  · rfl
lemma w0 {ws:List ff} (a b:ff) (ha:a ∈ ws) (hb:b ∈ ws) (hne:a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b):=by
  have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (nl a ha).trans (List.Perm.cons _ (nl b hm))
lemma xq {ws:List ff} (d:Bool) (a b:ff) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:a ≠ b) (ka kb:Bool) :
    (ft d (px ws a b ka kb)).1 =
      (if ka then (if kb then (ft d ws).1 else ku (ft d ws) (fq d b.2))
       else if kb then ku (ft d ws) (fq d a.2)
       else mv (ft d ws) (fq d a.2) (fq d b.2)):=by
  cases ka <;> cases kb
  · change (ft d ((ws.erase a).erase b)).1=mv (ft d ws) _ _
    rw [vz d (w0 a b ha hb ne)];exact (c2 _ _ _).symm
  · exact qs d a ha false
  · exact qs d b hb false
  · rfl
def sameWords (a b:List Sig):=(a.all (fun x => b.contains x))&&(b.all (fun x => a.contains x))
lemma sameWords_sound {xs ys} (h:sameWords xs ys=true) : xs.toFinset=ys.toFinset:=by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h;ext a;simp only [List.mem_toFinset];exact ⟨h.1 a,h.2 a⟩
def keyWord (v:Sig) :=
  let n:=v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev xb:=wv × wv
def py (ws:List ff) : xb:=(ft false ws,ft true ws)
def pz (c:xb) (d:Bool):=if d then c.2 else c.1
lemma ww (ws) (d:Bool) : pz (py ws) d=ft d ws:=by cases d <;> rfl
def m0 (v:wv) (a b:Bits) (un ka kb:Bool) :=
  if un then (if ka then v.1 else ku v a) else
    if ka then (if kb then v.1 else ku v b)
    else if kb then ku v a else mv v a b
def gd (un ka kb:Bool) (a b:ff) (ws:List ff) :=
  if un then j1 ws a ka else px ws a b ka kb
lemma tb {ws:List ff} {a b:ff} (ha:a ∈ ws) (hb:b ∈ ws)
    (un ka kb d:Bool) (ne:un=false→ a≠b) :
    (ft d (gd un ka kb a b ws)).1 =
      m0 (pz (py ws) d) (fq d a.2) (fq d b.2) un ka kb:=by
  rw [ww]
  cases un
  · exact xq d a b ha hb (ne rfl) ka kb
  · exact qs d a ha ka
lemma ko (ws:List ff) (a:ff) (k:Bool) : (j1 ws a k).Sublist ws:=by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
lemma nm (ws:List ff) (a b:ff) (un ka kb:Bool) :
    (gd un ka kb a b ws).Sublist ws:=by
  cases un
  · exact (ko _ _ _).trans (ko _ _ _)
  · exact ko _ _ _
lemma zb (ws:List ff) (a b:ff) (un ka kb:Bool) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:un=false→ a≠b) :
    (gd un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un||kb then 0 else 1):=by
  cases un
  · have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [gd,px,j1,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [gd,j1,List.length_erase_of_mem ha]
def fm (op:Nat) (a b:ff):=ga op a b
def fx (op:Nat) (a b:ff) : l0:=(op,a.1,b.1)
lemma sf (op) (a b:ff) :
    (fm op a b).1=choiceVal (fx op a b):=by
  by_cases h : op=2
  · simp [fm,ga,h,v5,choiceVal,fx]
  · cases hh : op==1 <;> simp [fm,ga,h,hh,v6,choiceVal,fx]
lemma np {r s a b} (ha:fj r s a) (hb:fj r s b) (op:Nat) :
    fj r s (fm op a b):=by
  unfold fm ga;split
  · exact q7 ha
  · exact q8 _ ha hb
def h7 (ws:List ff) (op:Nat) (a b:ff) (ka kb:Bool) :=
  (fm op a b).1 :: (gd (op==2) ka kb a b ws).map Prod.fst
lemma kh {v:List Sig} {w:Sig} (a:Sig) (k:Bool) :
    w ∈ g6 k a v ↔ (w=a∧k=true)∨w∈v:=by cases k <;> simp [g6]
lemma sg {v:List ff} (nd:v.Nodup) (a w:ff) (k:Bool) :
    w ∈ j1 v a k ↔ w∈v∧(w≠a∨k=true):=by
  cases k <;> simp [j1,nd.mem_erase_iff,and_comm]
lemma mx {ws:List ff} (nd:(ws.map Prod.fst).Nodup) {a b:ff}
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
lemma si {ws:List ff} (nd:(ws.map Prod.fst).Nodup) {a b:ff}
    (ha:a ∈ ws) (hb:b ∈ ws) (un ka kb:Bool) (v:Sig) :
    v ∈ (gd un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst∧(v≠a.1∨ka=true)∧(un=true∨v≠b.1∨kb=true):=by
  have wn:=nd.of_map
  have dn:=wn.sublist (ko ws a ka)
  cases un <;> simp only [gd,Bool.false_eq_true,ite_false,ite_true,px,List.mem_map,
    sg wn,sg dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (mx nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (mx nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (mx nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
lemma w1 {ws:List ff} (nd:(ws.map Prod.fst).Nodup) {a:ff} (ha:a∈ws)
    (keep:Bool) :
    (h7 ws 2 a a keep keep).toFinset=(gg (ws.map Prod.fst) a.1 keep).toFinset:=by
  ext v;simp only [h7,gg,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    si nd ha ha,kh,nd.mem_erase_iff,fm,ga,v5,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all
lemma v9 {ws:List ff} (nd:(ws.map Prod.fst).Nodup) {a b:ff}
    (ha:a∈ws) (hb:b∈ws) (ne:a.1≠b.1) (d ka kb:Bool) :
    (h7 ws (if d then 1 else 0) a b ka kb).toFinset =
      (fw (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
  ext v
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  have bv:=List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [h7,fw,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    si nd ha hb,kh,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,fm,ga,v6,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
lemma tc (v:List Sig) (nd:v.Nodup) (a b:Sig) (d ka kb:Bool) :
    (fw v a b d ka kb).toFinset=(fw v b a d kb ka).toFinset:=by
  ext x;simp only [fw,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kh,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto
lemma vc (r s:Row) (h:∀ a ∈ inputs,bit r a=bit s a) : r=s:=by
  apply Fin.ext;apply Nat.eq_of_testBit_eq;intro j
  by_cases hj : j<9
  · let i : Fin 9:=⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs:=by
      rw [← input_list];exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (mu i r).symm.trans ((h _ hm).trans (mu i s))
  · have le : 512 ≤ 2^j:=by
      change 2^9 ≤ 2^j;exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def q0 (p q:List Move):=inputs.all (fun a => movedWord p (movedWord q a) == a)
lemma rj {p q} (h:q0 p q=true) (r:Row) :
    gq q (gq p r)=r:=by
  apply vc;intro a ha;rw [←mc,←mc]
  have eq:=beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def autoOK (T:Sig) (p:List Move) :=
  (movedWord p T == T)&&q0 p p.reverse&&q0 p.reverse p
def g3 (v:Nat) (upper:Nat):=2^769*upper+v
def f4 {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => g3 (f x).toNat (f4 f xs)
def k2 : Nat→ Nat
  | 0 => 0
  | n+1 => g3 1 (k2 n)
lemma qt (x:Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
lemma xr (a b:Bits) (u v:Nat) :
    g3 a.toNat u &&& g3 b.toNat v=g3 (a &&& b).toNat (u &&& v):=by
  apply Nat.eq_of_testBit_eq;intro i;simp only [g3,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (qt _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
lemma zd (a b:Bits) (u v:Nat) :
    g3 a.toNat u ||| g3 b.toNat v=g3 (a ||| b).toNat (u ||| v):=by
  apply Nat.eq_of_testBit_eq;intro i;simp only [g3,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (qt _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
lemma xt (a b:Bits) (u v:Nat) :
    g3 a.toNat u ^^^ g3 b.toNat v=g3 (a ^^^ b).toNat (u ^^^ v):=by
  apply Nat.eq_of_testBit_eq;intro i;simp only [g3,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (qt _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
lemma ln {α} (f g : α → Bits) (xs) :
    f4 f xs &&& f4 g xs=f4 (fun x => f x &&& g x) xs:=by
  induction xs with
  | nil => simp [f4]
  | cons a xs ih => simp only [f4,xr,ih]
lemma nq {α} (f g : α → Bits) (xs) :
    f4 f xs ||| f4 g xs=f4 (fun x => f x ||| g x) xs:=by
  induction xs with
  | nil => simp [f4]
  | cons a xs ih => simp only [f4,zd,ih]
lemma lp {α} (f g : α → Bits) (xs) :
    f4 f xs ^^^ f4 g xs=f4 (fun x => f x ^^^ g x) xs:=by
  induction xs with
  | nil => simp [f4]
  | cons a xs ih => simp only [f4,xt,ih]
lemma qu {α} (a:Bits) (xs:List α) :
    k2 xs.length*a.toNat=f4 (fun _ => a) xs:=by
  induction xs with
  | nil => simp [k2,f4]
  | cons v xs ih => simp only [List.length_cons,k2,f4,g3,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]
def mf (r packed:Nat):=((packed+r) >>> 768) &&& r
lemma ze (n i:Nat) (hi:i<n) : (k2 n).testBit (769*i)=true:=by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [k2,g3,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i:=by omega
      have ge : ¬769*(i+1)<769:=by omega
      simp only [ge,ite_false,di];exact ih _ (by omega)
set_option maxRecDepth 8192 in
lemma zf (a:Bits) : (a.toNat+1).testBit 768=(a==BitVec.allOnes 768):=by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim:=a.isLt
    have ne : a.toNat ≠ 2^768-1:=by
      intro eq;apply h;apply BitVec.eq_of_toNat_eq;simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768:=by omega
    rw [Nat.testBit_eq_false_of_lt lt];exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
lemma c3 {α} (f : α → Bits) (xs:List α) (i:Nat) (hi:i<xs.length) :
    (mf (k2 xs.length) (f4 f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768):=by
  simp only [mf,Nat.testBit_and,Nat.testBit_shiftRight,ze _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [f4,List.length_cons,k2,g3]
    have sum (u v x:Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1):=by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have:=(f a).isLt;omega)]
    have hi' : i < xs.length+1:=hi
    cases i with
    | zero => simpa using zf (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769:=by omega
      have di : 769*(i+1)+768-769=769*i+768:=by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ];apply ih i (by omega)
abbrev pc:=Nat × Nat
abbrev j6:=Nat × Nat × Nat
def l3 {α} (s : α → lj) (xs:List α) : pc :=
  (f4 (fun x => (s x).1) xs,f4 (fun x => (s x).2) xs)
def j7 {α} (c : α → wv) (xs:List α) : j6 :=
  (f4 (fun x => (c x).1) xs,f4 (fun x => (c x).2.1) xs,
   f4 (fun x => (c x).2.2) xs)
def q9 (d:Bool) (a:pc) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
lemma sj (a b:Bits) : a ^^^ (a &&& b)=a &&& ~~~b:=by
  apply BitVec.eq_of_getLsbD_eq;intro i hi;simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
lemma b4 {α} (s : α → lj) (xs:List α) (d:Bool) :
    q9 d (l3 s xs)=f4 (fun x => fq d (s x)) xs:=by
  cases d <;> simp only [q9,l3,fq,Bool.false_eq_true,ite_false,ite_true,ln,lp,sj]
def sk (full:Nat) (op:Nat) (a b:pc) : pc :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
lemma vd (a:Bits) : BitVec.allOnes 768 ^^^ a = ~~~a:=BitVec.allOnes_xor
lemma packed_op {α} (a b : α → ff) (xs:List α) (op:Nat) :
    sk (k2 xs.length*(BitVec.allOnes 768).toNat) op
      (l3 (fun x => (a x).2) xs) (l3 (fun x => (b x).2) xs) =
    l3 (fun x => (fm op (a x) (b x)).2) xs:=by
  by_cases un : op=2
  · simp only [sk,un,ite_true,l3,qu,lp,vd,fm,ga,v5]
  · by_cases one : op=1 <;> simp [sk,un,one,l3,nq,ln,fm,ga,v6]
def gn (c:j6) (a b:Nat) (un ka kb:Bool) :=
  let t4:=fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let b2:=c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else t4 a)
  else if ka then (if kb then c.1 else t4 b)
  else if kb then t4 a else b2
lemma td {α} (c : α → wv) (a b : α → Bits) (xs:List α) (un ka kb:Bool) :
    gn (j7 c xs) (f4 a xs) (f4 b xs) un ka kb =
    f4 (fun x => m0 (c x) (a x) (b x) un ka kb) xs:=by
  cases un <;> cases ka <;> cases kb <;>
    simp only [gn,j7,ln,nq,lp,sj,m0,ku,mv,
      Bool.false_eq_true,ite_false,ite_true]
def pd {α : Type} (f : α → Bool) (mask:Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0)||f x)&&pd f (mask >>> 769) xs
lemma xu {α} (f : α → Bool) (mask:Nat) (xs:List α) (i:Nat) (hi:i<xs.length)
    (bitOn:mask.testBit (769*i)=true) (ok:pd f mask xs=true) : f xs[i]=true:=by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0:=by intro e;simp [e] at bitOn
    simp only [pd,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0:=by
        intro he
        have at0:=congrArg (fun n:Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0;change mask.testBit 0=true at bitOn;simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2;simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
def fl (p:ff→ Bool) (a:ff) (keep:Bool) :=
  if keep then 0 else (p a).toNat
lemma tn (p:ff→ Bool) (ws:List ff) (a:ff) (keep:Bool) :
    ws.countP p ≤ (j1 ws a keep).countP p+fl p a keep:=by
  cases keep
  · simp only [j1,Bool.false_eq_true,ite_false,fl,List.countP_erase]
    split
    next h => simp [h.2];omega
    next => omega
  · simp [j1,fl]
lemma tp (p:ff→ Bool) (ws:List ff) (a b:ff) (un ka kb:Bool) :
    ws.countP p - fl p a ka - fl p b (un||kb) ≤
    (gd un ka kb a b ws).countP p:=by
  have h1:=tn p ws a ka
  have h2:=tn p (j1 ws a ka) b kb
  cases un <;> simp only [gd,px,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [fl];omega
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
def lr : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def g9 : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
lemma lq : lr=(BitVec.allOnes 512).toNat:=by decide +kernel
lemma gj : g9=(BitVec.allOnes 768).toNat:=by decide +kernel
lemma jf {n} (a:BitVec n) : (~~~a).toNat=(BitVec.allOnes n).toNat ^^^ a.toNat:=by
  rw [← BitVec.toNat_xor,BitVec.allOnes_xor]
lemma g7 {n} (a b:BitVec n) : (a &&& ~~~b).toNat=a.toNat ^^^ (a.toNat &&& b.toNat):=by
  rw [← BitVec.toNat_and,← BitVec.toNat_xor];congr 1;apply BitVec.eq_of_getLsbD_eq;intro j hj;simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,hj,decide_true,Bool.true_and]
  cases a.getLsbD j <;> cases b.getLsbD j <;> rfl
lemma qc (x:Nat) : (BitVec.ofNat 512 x).toNat=x &&& lr:=by
  apply Nat.eq_of_testBit_eq;intro j;rw [Nat.testBit_and,BitVec.toNat_ofNat,Nat.testBit_mod_two_pow,lq]
  have h1 : (BitVec.allOnes 512).toNat.testBit j=decide (j < 512):=by
    change (BitVec.allOnes 512).getLsbD j=_;exact BitVec.getLsbD_allOnes
  rw [h1,Bool.and_comm]
def opW (nraw d:Nat) : Nat:=if nraw+d ≤ 17 then 8 else 9
def sl : Nat→ Nat→ Nat→ Nat × Nat
  | 0,idx,b => (idx,b)
  | n+1,idx,b => if idx < b then (idx,b) else sl n (idx - b) (b+1)
def n3 (ow c:Nat) : Nat × Nat × Nat :=
  if ow == 8 then
    if c < 16 then (2,c,c)
    else if c < 136 then let (a,b):=sl 15 (c - 16) 1;(0,a,b)
    else let (a,b):=sl 15 (c - 136) 1;(1,a,b)
  else
    if c < 22 then (2,c,c)
    else if c < 253 then let (a,b):=sl 21 (c - 22) 1;(0,a,b)
    else let (a,b):=sl 21 (c - 253) 1;(1,a,b)
def jg (ow:Nat) : Nat→ Nat→ List ff→ List ff
  | 0,_,ws => ws
  | k+1,bits,ws =>
    let (op,ia,ib):=n3 ow (bits &&& ((1 <<< ow) - 1))
    jg ow k (bits >>> ow) (ws ++ [ga op (ws.getD ia f0) (ws.getD ib f0)])
lemma rl (ow n bits:Nat) (ws:List ff) (r s) (base:∀ v ∈ ws,fj r s v) :
    ∀ v ∈ jg ow n bits ws,fj r s v:=by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    simp only [jg]
    rcases n3 ow (bits &&& ((1 <<< ow) - 1)) with ⟨op,ia,ib⟩
    apply ih;intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl:=List.mem_singleton.mp hz;unfold ga;split
      · exact q7 (mr base _)
      · exact q8 _ (mr base _) (mr base _)
def jh (ow:Nat) : Nat→ Nat→ List Sig→ List Sig
  | 0,_,ws => ws
  | k+1,bits,ws =>
    let (op,ia,ib):=n3 ow (bits &&& ((1 <<< ow) - 1))
    let z:=if op=2 then neg (ws.getD ia zero) else bin (op == 1) (ws.getD ia zero) (ws.getD ib zero)
    jh ow k (bits >>> ow) (ws ++ [z])
lemma te (ow n bits:Nat) (ws:List ff) :
    jh ow n bits (ws.map Prod.fst)=(jg ow n bits ws).map Prod.fst:=by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [jh,jg]
    have hget : ∀ i,(ws.map Prod.fst).getD i zero=(ws.getD i f0).1:=by
      intro i;rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map];cases ws[i]? <;> rfl
    rcases n3 ow (bits &&& ((1 <<< ow) - 1)) with ⟨op,ia,ib⟩
    dsimp only
    have hcode : (if op=2 then neg ((ws.map Prod.fst).getD ia zero)
        else bin (op == 1) ((ws.map Prod.fst).getD ia zero) ((ws.map Prod.fst).getD ib zero)) =
        (ga op (ws.getD ia f0) (ws.getD ib f0)).1:=by
      rw [hget,hget];unfold ga v6 v5;split
      · rfl
      · split <;> rfl
    rw [hcode,← List.map_singleton,← List.map_append];exact ih (bits >>> ow) _
lemma ns (ow:Nat) (ms:List Move) (n bits:Nat) (ws:List Sig) :
    jh ow n bits (ws.map (movedWord ms))=(jh ow n bits ws).map (movedWord ms):=by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [jh]
    have hget (i:Nat) : (ws.map (movedWord ms)).getD i zero=movedWord ms (ws.getD i zero):=by
      rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases ws[i]? with
      | none => exact ((jl ms zero).trans (ma (gq ms)).1).symm
      | some x => rfl
    rcases n3 ow (bits &&& ((1 <<< ow) - 1)) with ⟨op,ia,ib⟩
    dsimp only;rw [hget,hget]
    have hop : (if op=2 then neg (movedWord ms (ws.getD ia zero))
        else bin (op == 1) (movedWord ms (ws.getD ia zero)) (movedWord ms (ws.getD ib zero))) =
        movedWord ms (if op=2 then neg (ws.getD ia zero)
        else bin (op == 1) (ws.getD ia zero) (ws.getD ib zero)):=by
      simp only [jl];split
      · exact (s2 _ _).symm
      · exact (s3 _ _ _ _).symm
    rw [hop,← List.map_singleton,← List.map_append];exact ih (bits >>> ow) _
abbrev n7:=Nat × Nat × Nat
def fb (d:ff) : n7:=(d.1.toNat,d.2.1.toNat,d.2.2.toNat)
def opN (op a b:Nat) : Nat :=
  if op == 2 then lr ^^^ a else if op == 1 then a ||| b else a &&& b
lemma wx (op:Nat) (a b:Sig) :
    opN op a.toNat b.toNat=(if op=2 then neg a else bin (op == 1) a b).toNat:=by
  unfold opN
  by_cases h2 : op=2
  · simp only [h2,beq_self_eq_true,ite_true,neg,jf,lq]
  · simp only [beq_eq_false_iff_ne.mpr h2,Bool.false_eq_true,ite_false,h2]
    by_cases h1 : op=1
    · simp [h1,bin,BitVec.toNat_or]
    · simp [beq_eq_false_iff_ne.mpr h1,bin,BitVec.toNat_and]
lemma xv (op:Nat) (a b:ff) :
    opN op a.1.toNat b.1.toNat=(fm op a b).1.toNat:=by
  rw [wx];unfold fm ga v5 v6
  by_cases h2 : op=2
  · simp [h2]
  · by_cases h1 : op=1 <;> simp [h2,h1,bin]
def jt (op:Nat) (a b:n7) : n7 :=
  if op == 2 then (lr ^^^ a.1,g9 ^^^ a.2.1,g9 ^^^ a.2.2)
  else if op == 1 then (a.1 ||| b.1,a.2.1 ||| b.2.1,a.2.2 ||| b.2.2)
  else (a.1 &&& b.1,a.2.1 &&& b.2.1,a.2.2 &&& b.2.2)
lemma qv (op:Nat) (a b:ff) :
    jt op (fb a) (fb b)=fb (ga op a b):=by
  unfold jt fb ga v5 v6
  by_cases h2 : op=2
  · simp only [h2,beq_self_eq_true,ite_true,neg,jf,lq,gj]
  · simp only [beq_eq_false_iff_ne.mpr h2,Bool.false_eq_true,ite_false,h2]
    by_cases h1 : op=1
    · simp [h1,bin,BitVec.toNat_or]
    · simp [beq_eq_false_iff_ne.mpr h1,h1,bin,BitVec.toNat_and]
def m1 (ow:Nat) : Nat→ Nat→ List n7→ List n7
  | 0,_,ws => ws
  | k+1,bits,ws =>
    let (op,ia,ib):=n3 ow (bits &&& ((1 <<< ow) - 1))
    m1 ow k (bits >>> ow) (ws ++ [jt op (ws.getD ia (0,0,0)) (ws.getD ib (0,0,0))])
lemma nt (ow n bits:Nat) (ws:List ff) :
    m1 ow n bits (ws.map fb)=(jg ow n bits ws).map fb:=by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [m1,jg]
    have hget (i:Nat) : (ws.map fb).getD i (0,0,0)=fb (ws.getD i f0):=by
      rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases ws[i]? <;> simp [f0,fb,zero]
    rcases n3 ow (bits &&& ((1 <<< ow) - 1)) with ⟨op,ia,ib⟩
    dsimp only;rw [hget,hget,qv,← List.map_singleton,← List.map_append];exact ih (bits >>> ow) _
def m2 (ow:Nat) : Nat→ Nat→ List Nat→ List Nat
  | 0,_,ws => ws
  | k+1,bits,ws =>
    let (op,ia,ib):=n3 ow (bits &&& ((1 <<< ow) - 1))
    m2 ow k (bits >>> ow) (ws ++ [opN op (ws.getD ia 0) (ws.getD ib 0)])
lemma sm (ow n bits:Nat) (ws:List Sig) :
    m2 ow n bits (ws.map BitVec.toNat)=(jh ow n bits ws).map BitVec.toNat:=by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [m2,jh]
    have hget (i:Nat) : (ws.map BitVec.toNat).getD i 0=(ws.getD i zero).toNat:=by
      rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases ws[i]? <;> simp [f0,fb,zero]
    rcases n3 ow (bits &&& ((1 <<< ow) - 1)) with ⟨op,ia,ib⟩
    dsimp only;rw [hget,hget,wx,← List.map_singleton,← List.map_append];exact ih (bits >>> ow) _
def j8 (word:Nat→ Nat) (pos len:Nat) :=
  let i:=pos >>> 16
  let b3:=pos &&& 65535
  let lo:=word i >>> b3
  if b3+len ≤ 65536 then lo &&& ((1 <<< len) - 1)
  else (lo ||| (word (i+1) <<< (65536 - b3))) &&& ((1 <<< len) - 1)
def lw0 (nb slots sw vw iw pw:Nat) (data:Nat→ Nat) (h:Nat) : Option (Nat × Nat) :=
  let a:=h % nb
  let sh:=j8 data (a*sw) sw
  let row:=(h / nb+sh) % slots
  let word:=j8 data (nb*sw+row*vw) vw
  some (word &&& ((1 <<< iw) - 1),(word >>> iw) &&& ((1 <<< pw) - 1))
inductive IndexTree (α : Type) where
  | leaf (xs:List α)
  | fork (left:Nat) (a b:IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat→ Option α
  | .leaf xs,i => xs[i]?
  | .fork l a b,i => if i < l then a.read i else b.read (i - l)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
lemma IndexTree.read_mem {α} (tree:IndexTree α) {i x} (e:tree.read i=some x) :
    x ∈ tree.values:=by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork l a b iha ihb =>
    unfold IndexTree.read at e;split at e
    · exact List.mem_append_left _ (iha e)
    · exact List.mem_append_right _ (ihb e)
abbrev PT:=Nat × Nat × Nat × Nat × (Nat→ Nat)
def ePT : PT:=(0,0,0,0,fun _ => 0)
def Forest:=Nat × Nat × (Nat→ Bits × Bits) × IndexTree ColumnInfo × Array (List Nat)
def Forest.mask (c:Forest) : Nat:=c.1
def Forest.cap (c:Forest) : Nat:=c.2.1
def Forest.samples (c:Forest) : Nat→ Bits × Bits:=c.2.2.1
def Forest.cols (c:Forest) : IndexTree ColumnInfo:=c.2.2.2.1
def Forest.autos (c:Forest) : Array (List Nat):=c.2.2.2.2
def j4 (g:Forest) : List ff :=
  sd g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
lemma sn (g:Forest) : ∀ a ∈ j4 g,
    fj (n2 fun j => (g.samples j).1) (n2 fun j => (g.samples j).2) a :=
  v7 g.mask _ _
lemma nu (g:Forest) : (j4 g).map Prod.fst=vars g.mask:=by
  simp [j4,sd,vars,List.map_map,Function.comp_def]
lemma w2 (g:Forest) : (j4 g).length=(vars g.mask).length:=by
  rw [← nu g,List.length_map]
lemma w3 {m:Nat} {p q:Nat→ Bits}
    (hp:me m p=BitVec.allOnes 768) (hq:me m q=0) :
    k1 (graphGoal m) (n2 p) (n2 q):=by
  intro i;simp only [v8,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def gp {α : Type} (bits:Nat) : List α → List α
  | [] => []
  | w :: ws => if bits &&& 1 == 1 then w :: gp (bits >>> 1) ws else gp (bits >>> 1) ws
lemma sp {α : Type} (bits:Nat) (ws:List α) : (gp bits ws).Sublist ws:=by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold gp;split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
lemma k3 {α β : Type} (f : α → β) (bits:Nat) (ws:List α) :
    gp bits (ws.map f)=(gp bits ws).map f:=by
  induction ws generalizing bits with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,gp];split <;> simp [ih]
def k4 (ow:Nat) (f8:List ff) (ops paid:Nat) : Nat→ List l0
  | 0 => []
  | n+1 =>
    let more:=k4 ow f8 (ops >>> ow) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      let (op,ia,ib):=n3 ow (ops &&& ((1 <<< ow) - 1))
      (op,(f8.getD ia f0).1,(f8.getD ib f0).1) :: more
def pe (g:Forest) (ow ops d:Nat) (f8:List ff) (idx paid:Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (k4 ow f8 ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
lemma rm (g:Forest)
    (cols:∀ ci ∈ g.cols.values,rg (vars g.mask) (graphGoal g.mask) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {ow i ops g5 f8 paid c} (h:pe g ow ops g5 f8 i paid=some c) :
    ValidPool (vars g.mask) (graphGoal g.mask) c:=by
  unfold pe at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h;exact materialize_sound (cols ci (g.cols.read_mem e)) h
def sq (data:Nat→ Nat) (w v:Nat) : Nat→ Nat→ List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x:=j8 data pos (w+v)
    (x &&& ((1 <<< w) - 1),x >>> w) :: sq data w v n (pos+w+v)
def graphValid (g:Forest) (jv:Nat→ Nat) :=
  (me g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (me g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => md g.mask c jv) &&
  g.autos.toList.all (fun p => autoOK (graphGoal g.mask) (p.map swapRows))
lemma tf {m cap jv ci hints} (low:∀ q,j3 (vars q) (graphGoal q) (jv q))
    (ok:md m ci jv=true)
    (hp:kt (graphGoal m)=true)
    (ess:gh (graphGoal m) (vars m) (kl m hints)=true)
    (all:(kl m hints).map Prod.fst=vars m)
    (nd:(vars m).Nodup)
    (cut:rt (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (vars m) (vars m)=true) :
    j3 (vars m) (graphGoal m) (cap+1):=by
  apply mb (k8 _ hp) _ (t8 (col_sound ci jv low ok) [] rfl nd cut);intro a ha;apply li ess a;rw [all];exact List.mem_toFinset.mpr ha
def kv (n1:List (Nat × Nat)) := ∀ e ∈ n1,j3 (vars e.1) (graphGoal e.1) e.2
def g1 (old:List (Nat × Nat)) (L:Nat) (ly:List (Nat × List Nat)) :=
  ly.map (fun v => (v.1,L)) ++ old
lemma gw {old L m ly} (a7:kv old)
    (main:j3 (vars m) (graphGoal m) L)
    (ok:ly.all (fun v => p9 v.1 m v.2)=true) :
    kv (g1 old L ly):=by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact wr (List.all_eq_true.mp ok _ hv) main
  · exact a7 e h
lemma tq : kv []:=by simp [kv]
def ImpossibleT (T:Sig) (cap tm:Nat) (S:Finset Sig) : Prop :=
  ∀ k t,k ≤ cap→ (tm < 3→ t ≤ tm)→ ¬Live T k t S
lemma impT3_to_imp {T cap S} (h:ImpossibleT T cap 3 S) : Impossible T cap S :=
  fun k t hk => h k t hk (fun hlt => by omega)
lemma imp_to_impT {T cap tm S} (h:Impossible T cap S) : ImpossibleT T cap tm S :=
  fun k t hk _ => h k t hk
lemma impT_mono {T cap tm1 tm2 S} (hle:tm1 ≤ tm2) (h:ImpossibleT T cap tm2 S) :
    ImpossibleT T cap tm1 S :=
  fun k t hk ht => h k t hk (fun hlt => Nat.le_trans (ht (by omega)) hle)
lemma rotate_excludedT {T n tm} {ws:List Sig} (hi:ImpossibleT T n tm ws.toFinset)
    (p:List Move) (ok:autoOK T p=true) :
    ImpossibleT T n tm (ws.map (movedWord p.reverse)).toFinset:=by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (gq p):=fun r => ⟨gq p.reverse r,rj ok.2 r⟩
  intro k t hk ht h
  have run:=vt h (gq p) onto
  have goal : g8 (gq p) T=T:=(jl p T).symm.trans ok.1.1
  have t5 (x:Sig) : g8 (gq p) (movedWord p.reverse x)=x:=by
    apply BitVec.eq_of_getLsbD_eq;intro j hj;change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _;rw [gl,mc,rj ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (g8 (gq p))=ws.toFinset:=by
    ext a;simp only [Finset.mem_image,List.mem_toFinset,List.mem_map];constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩;simpa only [t5] using hw
    · intro ha;exact ⟨_,⟨a,ha,rfl⟩,t5 a⟩
  rw [goal,back] at run;exact hi k t hk ht run
def ji (tm cap len:Nat) (isNot:Bool) : Nat :=
  let base:=if tm == 3 then 3 else if isNot then tm - 1 else tm
  let slack:=cap - len
  if slack < base then slack else base
lemma wy {T:Sig} {cap tm:Nat} {ws:List Sig} (hn:ws.Nodup) (out:T ∉ ws)
    (oneStep:tm > 0→ ∀ a ∈ ws,∀ keep,neg a ∉ ws→ proper (neg a) →
      (gg ws a keep).length ≤ cap →
      ImpossibleT T (cap - 1) (ji tm cap (gg ws a keep).length true) (gg ws a keep).toFinset)
    (twoStep:∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a ≠ b→ bin d a b ∉ ws →
      proper (bin d a b)→ (fw ws a b d ka kb).length ≤ cap →
      ImpossibleT T (cap - 1) (ji tm cap (fw ws a b d ka kb).length false)
        (fw ws a b d ka kb).toFinset) :
    ImpossibleT T cap tm ws.toFinset:=by
  classical
  intro k t hk ht h
  generalize he : ws.toFinset=S at h
  induction h using Live.recurse with
  | stop hp => exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have gi : neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let keep:=decide (a ∈ U)
    have er:=qn hn a
    have rest : (g6 keep a (ws.erase a)).toFinset=U:=by
      rw [m9,er,he];by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (gg ws a keep).Nodup:=by
      have na : a ∉ ws.erase a:=hn.not_mem_erase
      refine List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h)),
        k7 keep a (ws.erase a) (hn.erase _) na⟩
    have eq : (gg ws a keep).toFinset=insert (neg a) U:=by simp [gg,rest]
    have sc:=(kp tail).2
    have len : (gg ws a keep).length ≤ cap:=by rw [← List.toFinset_card_of_nodup nd,eq];omega
    have htm_pos : tm > 0:=by by_contra h0;have:=ht (by omega);omega
    have ht' : ji tm cap (gg ws a keep).length true < 3→ t ≤ ji tm cap (gg ws a keep).length true:=by
      intro hlt
      have hcard : (gg ws a keep).length=(insert (neg a) U).card:=by rw [← List.toFinset_card_of_nodup nd,eq]
      unfold ji at hlt ⊢;simp only [ite_true] at hlt ⊢
      by_cases h3 : tm=3
      · simp only [h3,beq_self_eq_true,ite_true] at hlt ⊢
        by_cases hsb : cap - (gg ws a keep).length < 3
        · rw [if_pos hsb] at hlt ⊢;omega
        · rw [if_neg hsb] at hlt;omega
      · simp only [beq_eq_false_iff_ne.mpr h3,Bool.false_eq_true,ite_false] at hlt ⊢
        by_cases hsb : cap - (gg ws a keep).length < tm - 1
        · rw [if_pos hsb] at hlt ⊢;omega
        · rw [if_neg hsb] at hlt ⊢;have:=ht (by omega);omega
    exact oneStep htm_pos a am keep gi hz len k t (by omega) ht' (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have gi : bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er : rest.toFinset=(ws.toFinset.erase a).erase b:=by
      rw [show rest=(ws.erase a).erase b by rfl,qn (hn.erase _) b,qn hn a]
    have ke : (g6 ka a (g6 kb b rest)).toFinset=U:=by
      rw [m9,m9,er,he];ext j
      by_cases hja : j=a
      · subst j;by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hab]
      · by_cases hjb : j=b
        · subst j;by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hja]
        · by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hja,hjb]
    have rn : rest.Nodup:=(hn.erase _).erase _
    have ar : a ∉ rest:=fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest:=(hn.erase a).not_mem_erase
    have nk:=k7 kb b rest rn br
    have ax : a ∉ g6 kb b rest:=by cases kb <;> simp [g6,ar,hab]
    have nd : (fw ws a b d ka kb).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))),
        k7 ka a _ nk ax⟩
    have eq : (fw ws a b d ka kb).toFinset=insert (bin d a b) U:=by
      change (bin d a b :: g6 ka a (g6 kb b rest)).toFinset=_;simp [ke]
    have sc:=(kp tail).2
    have len : (fw ws a b d ka kb).length ≤ cap:=by rw [← List.toFinset_card_of_nodup nd,eq];omega
    have ht' : ji tm cap (fw ws a b d ka kb).length false < 3→ t ≤ ji tm cap (fw ws a b d ka kb).length false:=by
      intro hlt
      have hcard : (fw ws a b d ka kb).length=(insert (bin d a b) U).card:=by rw [← List.toFinset_card_of_nodup nd,eq]
      unfold ji at hlt ⊢;simp only [Bool.false_eq_true,ite_false] at hlt ⊢
      by_cases h3 : tm=3
      · simp only [h3,beq_self_eq_true,ite_true] at hlt ⊢
        by_cases hsb : cap - (fw ws a b d ka kb).length < 3
        · rw [if_pos hsb] at hlt ⊢;omega
        · rw [if_neg hsb] at hlt;omega
      · simp only [beq_eq_false_iff_ne.mpr h3,Bool.false_eq_true,ite_false] at hlt ⊢
        by_cases hsb : cap - (fw ws a b d ka kb).length < tm
        · rw [if_pos hsb] at hlt ⊢;omega
        · rw [if_neg hsb] at hlt ⊢;exact ht hlt
    exact twoStep a am b bm d ka kb hab gi hz len k t (by omega) ht' (eq.symm ▸ tail)
inductive gk {R:Type} (goal:fp R) : Nat→ List (fp R)→ Prop
  | stop : gk goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs→ gk goal s xs→ gk goal s zs
  | two {s a b rest} (op ka kb:Bool) :
      gk goal s (g0 op a b :: g6 ka a (g6 kb b rest)) →
      gk goal (s+1) (a :: b :: rest)
lemma gk.toRun {R:Type} {goal:fp R} {s ws} (h:gk goal s ws) : kw goal s ws:=by
  induction h with
  | stop => exact kw.stop
  | perm hp _ ih => exact kw.perm hp ih
  | two op ka kb _ ih => exact kw.two op ka kb ih
lemma qw {r s:Row} {goal:fp Row} {k ws} (h:gk goal k ws)
    (hr:goal r=true) (hs:goal s=false) :
    ∃ w ∈ ws,w r=true∧w s=false:=by
  induction h with
  | stop => exact ⟨goal,by simp,hr,hs⟩
  | perm hp _ ih => obtain ⟨w,hw,h1,h2⟩ := ih;exact ⟨w,hp.mem_iff.mp hw,h1,h2⟩
  | @two k a b rest op ka kb _ ih =>
    obtain ⟨w,hw,h1,h2⟩ := ih
    rcases List.mem_cons.mp hw with rfl | hrest
    · cases op with
      | false =>
        simp only [g0,Bool.false_eq_true,ite_false,Bool.and_eq_true,Bool.and_eq_false_iff] at h1 h2
        rcases h2 with ha | hb
        · exact ⟨a,by simp,h1.1,ha⟩
        · exact ⟨b,by simp,h1.2,hb⟩
      | true =>
        simp only [g0,ite_true,Bool.or_eq_true,Bool.or_eq_false_iff] at h1 h2
        rcases h1 with ha | hb
        · exact ⟨a,by simp,ha,h2.1⟩
        · exact ⟨b,by simp,hb,h2.2⟩
    · rcases nf hrest with rfl | hrest2
      · exact ⟨w,by simp,h1,h2⟩
      · rcases nf hrest2 with rfl | hrest3
        · exact ⟨w,by simp,h1,h2⟩
        · exact ⟨w,by simp [hrest3],h1,h2⟩
lemma ve {T:Sig} {k} {fs:List Sig} (h:gk (f7 T) k (fs.map f7))
    {r s:Fin 768→ Row} (m5:k1 T r s) :
    fk true (fi r s) fs=BitVec.allOnes 768:=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj
  let i : Fin 768:=⟨j,hj⟩
  rw [BitVec.getLsbD_allOnes];simp only [hj,decide_true];apply (jz (i:=i)).mpr
  obtain ⟨w,hw,h1,h2⟩ := qw h (m5 i).1 (m5 i).2
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
  refine ⟨a,ha,?_⟩;simp only [fq,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and,fi,gm];change bit (r i) a=true at h1;change bit (s i) a=false at h2;simp [h1,h2]
lemma xw (a:Sig) : neg (neg a)=a:=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj;simp [neg,hj]
lemma c4 (d:Bool) (a b:Sig) : neg (bin d a b)=bin (!d) (neg a) (neg b):=by
  cases d <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;> simp [neg,bin,hj,Bool.not_and,Bool.not_or]
lemma lk {α β : Type} {R : α → β → Prop} {xs xs':List α} {ys:List β}
    (hp:xs.Perm xs') (h:List.Forall₂ R xs ys) :
    ∃ ys',ys.Perm ys' ∧ List.Forall₂ R xs' ys' := by
  induction hp generalizing ys with
  | nil => cases h;exact ⟨[],List.Perm.nil,List.Forall₂.nil⟩
  | cons x _ ih =>
    cases h with
    | cons hr ht => obtain ⟨ys',hp',ht'⟩ := ih ht;exact ⟨_ :: ys',hp'.cons _,List.Forall₂.cons hr ht'⟩
  | swap x y l =>
    cases h with
    | cons h1 hrest =>
      cases hrest with
      | cons h2 ht => exact ⟨_,List.Perm.swap _ _ _,List.Forall₂.cons h2 (List.Forall₂.cons h1 ht)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨y1,p1,f1⟩ := ih1 h;obtain ⟨y2,p2,f2⟩ := ih2 f1;exact ⟨y2,p1.trans p2,f2⟩
lemma vf {T:Sig} {k t:Nat} {S:Finset Sig} (h:Live T k t S)
    (hsz:S.card+t=k+1) (v:List Sig) (hv:v.Nodup) (eqv:v.toFinset=S) :
    ∃ fs : List Sig,List.Forall₂ (fun w u => u=w∨u=neg w) v fs ∧
      gk (f7 T) (k - t) (fs.map f7):=by
  classical
  induction h using Live.recurse generalizing v with
  | stop hp =>
    have eq : [T].Perm v:=List.perm_of_nodup_nodup_toFinset_eq (by simp) hv (by simp [eqv])
    have h1 : List.Forall₂ (fun w u => u=w∨u=neg w) [T] [T]:=List.Forall₂.cons (Or.inl rfl) List.Forall₂.nil
    obtain ⟨fs,hp',hf⟩ := lk eq h1
    exact ⟨fs,hf,gk.perm (hp'.map f7) gk.stop⟩
  | @unary k t U a ha gi tail ih =>
    have hu : neg a ∉ U:=fun hm => gi (Finset.mem_insert_of_mem hm)
    have hts:=(kp tail).2;rw [Finset.card_insert_of_notMem hu] at hts
    have haU : a ∉ U:=by intro hm;rw [Finset.insert_eq_of_mem hm] at hsz;omega
    rw [Finset.card_insert_of_notMem haU] at hsz
    have hsz' : (insert (neg a) U).card+t=k+1:=by rw [Finset.card_insert_of_notMem hu];omega
    let rest:=U.toList;have hr : rest.Nodup:=Finset.nodup_toList U;have hrf : rest.toFinset=U:=by simp [rest]
    obtain ⟨fs0,hfa,hmr⟩ := ih hsz' (neg a :: rest) (List.nodup_cons.mpr ⟨by simpa [rest] using hu,hr⟩) (by simp [hrf])
    cases hfa with
    | @cons _ u0 _ fs_rest hhd htl =>
      have hhd' : u0=a∨u0=neg a:=by
        rcases hhd with h1 | h1
        · exact Or.inr h1
        · rw [xw] at h1;exact Or.inl h1
      have hpv : (a :: rest).Perm v:=List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨by simpa [rest] using haU,hr⟩) hv (by simp [hrf,eqv])
      obtain ⟨fs,hp',hf⟩ := lk hpv (List.Forall₂.cons hhd' htl)
      rw [show (k+1) - (t+1)=k - t by omega];exact ⟨fs,hf,gk.perm (hp'.map f7) hmr⟩
  | @binary k t U a b d ha hb hab gi tail ih =>
    have hu : bin d a b ∉ U:=fun hm => gi (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have hts1:=(kp tail).1;have hts2:=(kp tail).2;rw [Finset.card_insert_of_notMem hu] at hts2
    have h1:=Finset.card_insert_le (a:=a) (s:=insert b U);have h2:=Finset.card_insert_le (a:=b) (s:=U)
    have haU : a ∉ U:=by
      intro hm
      have hc : (insert a (insert b U)).card=(insert b U).card:=by rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hm)]
      omega
    have hbU : b ∉ U:=by
      intro hm
      have hc : (insert b U).card=U.card:=by rw [Finset.insert_eq_of_mem hm]
      omega
    have hsz' : (insert (bin d a b) U).card+t=k+1:=by
      rw [Finset.card_insert_of_notMem hu];rw [Finset.card_insert_of_notMem (by simp [hab,haU]),Finset.card_insert_of_notMem hbU] at hsz;omega
    let rest:=U.toList;have hr : rest.Nodup:=Finset.nodup_toList U;have hrf : rest.toFinset=U:=by simp [rest]
    obtain ⟨fs0,hfa,hmr⟩ := ih hsz' (bin d a b :: rest) (List.nodup_cons.mpr ⟨by simpa [rest] using hu,hr⟩) (by simp [hrf])
    have hpv : (a :: b :: rest).Perm v:=List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,show a ∉ rest by simpa [rest] using haU,show b ∉ rest by simpa [rest] using hbU,hr]) hv (by simp [hrf,eqv])
    rw [show (k+1) - t=(k - t)+1 by omega]
    cases hfa with
    | @cons _ uz _ fs_rest hhd htl =>
      rcases hhd with h1 | h1
      · subst h1
        have hmr' : gk (f7 T) ((k - t)+1) ((a :: b :: fs_rest).map f7):=gk.two d false false (by simpa [g6,q5] using hmr)
        obtain ⟨fs,hp',hf⟩ := lk hpv (List.Forall₂.cons (Or.inl rfl) (List.Forall₂.cons (Or.inl rfl) htl))
        exact ⟨fs,hf,gk.perm (hp'.map f7) hmr'⟩
      · subst h1;rw [c4] at hmr
        have hmr' : gk (f7 T) ((k - t)+1) ((neg a :: neg b :: fs_rest).map f7):=gk.two (!d) false false (by simpa [g6,q5] using hmr)
        obtain ⟨fs,hp',hf⟩ := lk hpv (List.Forall₂.cons (Or.inr rfl) (List.Forall₂.cons (Or.inr rfl) htl))
        exact ⟨fs,hf,gk.perm (hp'.map f7) hmr'⟩
def q1 (a b:List Nat) : Bool:=a.length == b.length&&a.all (fun x => b.contains x)
lemma tg {xs ys:List Sig} (hnd:xs.Nodup) (h:q1 (xs.map BitVec.toNat) (ys.map BitVec.toNat)=true) :
    xs.toFinset=ys.toFinset:=by
  simp only [q1,List.length_map,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq,List.mem_map] at h
  have hsub : xs.toFinset ⊆ ys.toFinset:=by
    intro x hx
    obtain ⟨y,hy,he⟩ := h.2 x.toNat ⟨x,List.mem_toFinset.mp hx,rfl⟩
    exact List.mem_toFinset.mpr ((BitVec.eq_of_toNat_eq he.symm) ▸ hy)
  have hle : ys.toFinset.card ≤ xs.toFinset.card:=by
    rw [List.toFinset_card_of_nodup hnd,h.1];exact List.toFinset_card_le ys
  exact Finset.eq_of_subset_of_card_le hsub hle
def tr (d:Nat) : List Nat→ List Nat
  | [] => []
  | w :: ws => let m:=w &&& d;if m == 0||m == d then tr d ws else m :: tr d ws
def ju (d:Nat) (mp:List Nat) (a:Nat) : Bool :=
  let m:=a &&& d;m == 0||m == d||mp.any (fun v => v == m)
def ll (ow:Nat) (f8:List Nat) (ops paid:Nat) : Nat→ List (Nat × Nat × Nat)
  | 0 => []
  | n+1 =>
    let more:=ll ow f8 (ops >>> ow) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      let (op,ia,ib):=n3 ow (ops &&& ((1 <<< ow) - 1))
      (op,f8.getD ia 0,f8.getD ib 0) :: more
lemma rp (ow:Nat) (f8:List ff) (ops paid n:Nat) :
    ll ow (f8.map (fun w => w.1.toNat)) ops paid n =
      (k4 ow f8 ops paid n).map (fun c => (c.1,c.2.1.toNat,c.2.2.toNat)):=by
  induction n generalizing ops paid with
  | zero => rfl
  | succ n ih =>
    simp only [ll,k4];split
    · exact ih _ _
    · rcases n3 ow (ops &&& ((1 <<< ow) - 1)) with ⟨op,ia,ib⟩
      have hget (i:Nat) : (f8.map (fun w => w.1.toNat)).getD i 0=(f8.getD i f0).1.toNat:=by
        rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
        cases f8[i]? <;> simp [f0,zero]
      simp only [List.map_cons,hget,ih]
def l4 (d:Nat) (mp:List Nat) : List (Nat × Nat × Nat)→ Option (List Nat)
  | [] => some mp
  | (op,a,b) :: cs =>
    if ju d mp a&&(op == 2||ju d mp b) then
      let m:=opN op a b &&& d
      l4 d (if m == 0||m == d then mp else m :: mp) cs
    else none
def sr (z o:Nat) : Nat :=
  let fixed:=z ||| o
  if z &&& o != 0 then 0 else
    ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o) &&& lr
lemma w4 (z o:Nat) : sr z o=(subcube z o).toNat:=by
  unfold sr subcube;split
  · simp [zero]
  · exact (qc _).symm
lemma l9 (d a:Sig) :
    (a.toNat &&& d.toNat == 0||a.toNat &&& d.toNat == d.toNat)=f5 d a:=by
  simp only [f5,k0]
  have h1 : ((a.toNat &&& d.toNat) == 0)=((a &&& d) == zero):=by
    rw [← BitVec.toNat_and,zero,Bool.eq_iff_iff,beq_iff_eq,beq_iff_eq];exact ⟨fun h => BitVec.eq_of_toNat_eq (by simpa using h),fun h => by simp [h]⟩
  have h2 : ((a.toNat &&& d.toNat) == d.toNat)=((a &&& d) == d):=by
    rw [← BitVec.toNat_and,Bool.eq_iff_iff,beq_iff_eq,beq_iff_eq];exact ⟨fun h => BitVec.eq_of_toNat_eq h,fun h => congrArg BitVec.toNat h⟩
  rw [h1,h2]
lemma jo (d:Sig) (ws:List Sig) (mp:List Nat)
    (heq:∀ m,(m == 0||m == d.toNat||mp.any (· == m)) =
      (m == 0||m == d.toNat||(ws.map (fun w => w.toNat &&& d.toNat)).any (· == m))) (a:Sig) :
    ju d.toNat mp a.toNat=fd d ws a:=by
  unfold ju;rw [heq (a.toNat &&& d.toNat)]
  have hc:=l9 d a
  have h3 : ∀ l : List Sig,(l.map (fun w => w.toNat &&& d.toNat)).any (· == (a.toNat &&& d.toNat)) =
      (l.map (k0 d)).any (fun v => v == (a &&& d)):=by
    intro l;induction l with
    | nil => rfl
    | cons w rest ih =>
      simp only [List.map_cons,List.any_cons,k0]
      have hhd : ((w.toNat &&& d.toNat) == (a.toNat &&& d.toNat))=((w &&& d) == (a &&& d)):=by
        rw [← BitVec.toNat_and,← BitVec.toNat_and,Bool.eq_iff_iff,beq_iff_eq,beq_iff_eq];exact ⟨fun h => BitVec.eq_of_toNat_eq h,fun h => congrArg BitVec.toNat h⟩
      rw [hhd,ih]
  simp only [fd,f5] at hc ⊢
  rw [hc,h3 ws];rfl
lemma zg (d:Sig) (ws:List Sig) (m:Nat) :
    (m == 0||m == d.toNat||(tr d.toNat (ws.map BitVec.toNat)).any (· == m)) =
    (m == 0||m == d.toNat||(ws.map (fun w => w.toNat &&& d.toNat)).any (· == m)):=by
  induction ws with
  | nil => rfl
  | cons w rest ih =>
    simp only [List.map_cons,tr]
    by_cases hc : (w.toNat &&& d.toNat == 0||w.toNat &&& d.toNat == d.toNat)=true
    · rw [if_pos hc,ih];simp only [List.any_cons]
      by_cases hm : (w.toNat &&& d.toNat == m)=true
      · rw [← beq_iff_eq.mp hm];simp [hc]
      · simp [hm]
    · rw [if_neg hc];simp only [List.any_cons]
      cases hm1 : (m == 0||m == d.toNat) <;> cases hm2 : (w.toNat &&& d.toNat == m) <;> simp_all [Bool.or_assoc,Bool.or_left_comm]
lemma qx (d:Sig) (steps:List l0) :
    ∀ (ws:List Sig) (mp mw:List Nat),
      (∀ m,(m == 0||m == d.toNat||mp.any (· == m)) =
        (m == 0||m == d.toNat||(ws.map (fun w => w.toNat &&& d.toNat)).any (· == m))) →
      l4 d.toNat mp (steps.map (fun c => (c.1,c.2.1.toNat,c.2.2.toNat)))=some mw →
      ∃ ws',ks d ws steps=some ws' ∧
        (∀ m,(m == 0||m == d.toNat||mw.any (· == m)) =
          (m == 0||m == d.toNat||(ws'.map (fun w => w.toNat &&& d.toNat)).any (· == m))):=by
  induction steps with
  | nil => intro ws mp mw heq hm;simp only [List.map_nil,l4,Option.some.injEq] at hm;subst hm;exact ⟨ws,rfl,heq⟩
  | cons c cs ih =>
    intro ws mp mw heq hm
    rcases c with ⟨op,a,b⟩
    simp only [List.map_cons,l4] at hm
    have hch : (ju d.toNat mp a.toNat&&(op == 2||ju d.toNat mp b.toNat))=j5 d ws (op,a,b):=by
      simp only [j5,jo d ws mp heq]
    rw [hch] at hm
    cases hc : j5 d ws (op,a,b)
    · rw [hc] at hm;simp at hm
    · simp only [hc,ite_true] at hm
      have hval : opN op a.toNat b.toNat=(choiceVal (op,a,b)).toNat:=by
        rw [wx];unfold choiceVal;by_cases h2 : op=2 <;> simp [h2]
      rw [hval] at hm
      have heq' : ∀ m,(m == 0||m == d.toNat ||
          (if (choiceVal (op,a,b)).toNat &&& d.toNat == 0||(choiceVal (op,a,b)).toNat &&& d.toNat == d.toNat
           then mp else ((choiceVal (op,a,b)).toNat &&& d.toNat) :: mp).any (· == m)) =
          (m == 0||m == d.toNat||((choiceVal (op,a,b) :: ws).map (fun w => w.toNat &&& d.toNat)).any (· == m)):=by
        intro m
        by_cases hzc : ((choiceVal (op,a,b)).toNat &&& d.toNat == 0||(choiceVal (op,a,b)).toNat &&& d.toNat == d.toNat)=true
        · rw [if_pos hzc,heq m];simp only [List.map_cons,List.any_cons]
          by_cases hme : ((choiceVal (op,a,b)).toNat &&& d.toNat == m)=true
          · rw [← beq_iff_eq.mp hme];simp [hzc]
          · simp [hme]
        · rw [if_neg hzc];simp only [List.map_cons,List.any_cons]
          have h1:=heq m
          cases hb1 : (m == 0||m == d.toNat) <;> cases hb2 : ((choiceVal (op,a,b)).toNat &&& d.toNat == m)
          · simp only [hb1,hb2,Bool.false_or] at h1 ⊢;exact h1
          · simp [hb1,hb2]
          · simp [hb1,hb2]
          · simp [hb1,hb2]
      obtain ⟨ws',hbp,heq2⟩ := ih (choiceVal (op,a,b) :: ws) _ mw heq' hm
      exact ⟨ws',by simp [ks,hc,hbp],heq2⟩
abbrev QPN:=Nat × Nat × Nat × Nat × Nat × Nat × List Nat
def my (d:Nat) (mw:List Nat) : List Nat→ Nat→ Nat × Nat × Nat
  | [],_ => (0,0,0)
  | w :: ws,bit =>
    let (cm,jd,bad):=my d mw ws (bit <<< 1)
    let m:=w &&& d
    if m == 0||m == d then (cm+1,jd ||| bit,bad)
    else if mw.any (fun v => v == m) then (cm,jd,bad)
    else (cm,jd,bad ||| bit)
lemma j9 (t:Nat) : (1:Nat).testBit (t+1)=false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by omega:1 < 2^1) (Nat.pow_le_pow_right (by omega) (by omega:1 ≤ t+1)))
lemma h8 (a k b:Nat) :
    ((a ||| (1 <<< k)) >>> b) &&& 1=(((a >>> b) &&& 1) ||| (if b=k then 1 else 0)):=by
  apply Nat.eq_of_testBit_eq;intro t
  cases t with
  | zero =>
    simp only [Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_or,Nat.testBit_one_zero,Bool.and_true,Nat.add_zero];rw [Nat.testBit_shiftLeft]
    by_cases hbk : b=k
    · subst hbk;simp
    · have h0 : (decide (k ≤ b)&&(1:Nat).testBit (b - k))=false:=by
        by_cases hle : k ≤ b
        · rcases Nat.exists_eq_succ_of_ne_zero (by omega:b - k ≠ 0) with ⟨u,hu⟩
          simp [hle,hu,j9]
        · simp [hle]
      simp [hbk,h0]
  | succ t =>
    simp only [Nat.testBit_and,Nat.testBit_or,j9,Bool.and_false]
    split <;> simp [j9]
lemma vg (d:Sig) (wsP:List Sig) (mw:List Nat)
    (heq:∀ m,(m == 0||m == d.toNat||mw.any (· == m)) =
      (m == 0||m == d.toNat||(wsP.map (fun w => w.toNat &&& d.toNat)).any (· == m))) :
    ∀ (ws:List ff) (k:Nat),
      let (cm,jd,bad):=my d.toNat mw (ws.map (fun w => w.1.toNat)) (1 <<< k)
      cm=ws.countP (fun w => f5 d w.1) ∧
      (∀ i,((jd >>> (k+i)) &&& 1)=if i < ws.length then (f5 d (ws.getD i f0).1).toNat else 0) ∧
      (∀ i,((bad >>> (k+i)) &&& 1)=if i < ws.length then (!fd d wsP (ws.getD i f0).1).toNat else 0) ∧
      (∀ t < k,((jd >>> t) &&& 1)=0∧((bad >>> t) &&& 1)=0):=by
  intro ws
  induction ws with
  | nil => intro k;simp [my]
  | cons w rest ih =>
    intro k
    have hsh : (1 <<< k) <<< 1=1 <<< (k+1):=by rw [Nat.shiftLeft_add]
    have hih:=ih (k+1)
    rcases hsc : my d.toNat mw (rest.map (fun x => x.1.toNat)) (1 <<< (k+1)) with ⟨cm,jd,bad⟩
    rw [hsc] at hih;dsimp only at hih
    obtain ⟨hcm,hcmask,hbad,hlow⟩ := hih
    have hisc:=l9 d w.1
    have hav:=jo d wsP mw heq w.1
    simp only [List.map_cons,my,hsh,hsc]
    by_cases hc : (w.1.toNat &&& d.toNat == 0||w.1.toNat &&& d.toNat == d.toNat)=true
    · rw [if_pos hc]
      have hcw : f5 d w.1=true:=by rw [← hisc];exact hc
      have havw : fd d wsP w.1=true:=by rw [← hav];unfold ju;simp [hc]
      refine ⟨by simp [List.countP_cons,hcw,hcm],?_,?_,?_⟩
      · intro i;dsimp only;cases i with
        | zero => rw [Nat.add_zero,h8,(hlow k (by omega)).1];simp [hcw]
        | succ i => rw [h8,if_neg (by omega),Nat.or_zero,show k+(i+1)=(k+1)+i by omega,hcmask i];simp
      · intro i;dsimp only;cases i with
        | zero => rw [Nat.add_zero,(hlow k (by omega)).2];simp [havw]
        | succ i => rw [show k+(i+1)=(k+1)+i by omega,hbad i];simp
      · intro t ht;dsimp only;rw [h8,if_neg (by omega),Nat.or_zero];exact hlow t (by omega)
    · rw [if_neg hc]
      have hcw : f5 d w.1=false:=by rw [← hisc];exact Bool.eq_false_iff.mpr hc
      by_cases hm : mw.any (fun v => v == (w.1.toNat &&& d.toNat))=true
      · rw [if_pos hm]
        have havw : fd d wsP w.1=true:=by rw [← hav];unfold ju;simp [hm]
        refine ⟨by simp [List.countP_cons,hcw,hcm],?_,?_,?_⟩
        · intro i;dsimp only;cases i with
          | zero => rw [Nat.add_zero,(hlow k (by omega)).1];simp [hcw]
          | succ i => rw [show k+(i+1)=(k+1)+i by omega,hcmask i];simp
        · intro i;dsimp only;cases i with
          | zero => rw [Nat.add_zero,(hlow k (by omega)).2];simp [havw]
          | succ i => rw [show k+(i+1)=(k+1)+i by omega,hbad i];simp
        · intro t ht;dsimp only;exact hlow t (by omega)
      · rw [if_neg hm]
        have hcf : (w.1.toNat &&& d.toNat == 0||w.1.toNat &&& d.toNat == d.toNat)=false:=Bool.eq_false_iff.mpr hc
        have hmf : mw.any (fun v => v == (w.1.toNat &&& d.toNat))=false:=Bool.eq_false_iff.mpr hm
        have havw : fd d wsP w.1=false:=by rw [← hav];unfold ju;simp [hcf,hmf]
        refine ⟨by simp [List.countP_cons,hcw,hcm],?_,?_,?_⟩
        · intro i;dsimp only;cases i with
          | zero => rw [Nat.add_zero,(hlow k (by omega)).1];simp [hcw]
          | succ i => rw [show k+(i+1)=(k+1)+i by omega,hcmask i];simp
        · intro i;dsimp only;cases i with
          | zero => rw [Nat.add_zero,h8,(hlow k (by omega)).2];simp [havw]
          | succ i => rw [h8,if_neg (by omega),Nat.or_zero,show k+(i+1)=(k+1)+i by omega,hbad i];simp
        · intro t ht;dsimp only;rw [h8,if_neg (by omega),Nat.or_zero];exact hlow t (by omega)
def m3 (g:Forest) (rawS wsN:List Nat) (_k ow ops g5:Nat) (bankN:List Nat) (idx paid:Nat) : Option QPN :=
  (g.cols.read idx).bind fun ci =>
    let d:=sr ci.1 ci.2.1
    let cs:=ll ow bankN ops paid g5
    (l4 d (tr d rawS) cs).bind fun mw =>
      match my d mw wsN 1 with
      | (cm,jd,bad) => some (d,ci.2.2.2.2,cs.length,cm,jd,bad,mw)
def pf (p:BoundPool) (ws:List ff) (qp:QPN) : Prop :=
  qp.1=p.domain.toNat∧qp.2.1=p.bound∧qp.2.2.1=p.paid ∧
  (∀ m,(m == 0||m == p.domain.toNat||qp.2.2.2.2.2.2.any (· == m)) =
    (m == 0||m == p.domain.toNat||(p.wires.map (fun w => w.toNat &&& p.domain.toNat)).any (· == m))) ∧
  qp.2.2.2.1=ws.countP (fun w => f5 p.domain w.1) ∧
  (∀ i,((qp.2.2.2.2.1 >>> i) &&& 1)=if i < ws.length then (f5 p.domain (ws.getD i f0).1).toNat else 0) ∧
  (∀ i,((qp.2.2.2.2.2.1 >>> i) &&& 1)=if i < ws.length then (!fd p.domain p.wires (ws.getD i f0).1).toNat else 0)
lemma qd (g:Forest) (ws:List ff) (k ow ops g5:Nat) (f8:List ff) (idx paid:Nat) {qp:QPN}
    (h:m3 g ((vars g.mask).map BitVec.toNat) (ws.map (fun w => w.1.toNat)) k ow ops g5
      (f8.map (fun w => w.1.toNat)) idx paid=some qp) :
    ∃ p : BoundPool,pe g ow ops g5 f8 idx paid=some p∧pf p ws qp:=by
  unfold m3 at h
  cases er : g.cols.read idx with
  | none => simp [er] at h
  | some ci =>
    simp only [er,Option.bind_some,w4,rp] at h
    cases hm : l4 (subcube ci.1 ci.2.1).toNat (tr (subcube ci.1 ci.2.1).toNat ((vars g.mask).map BitVec.toNat))
        ((k4 ow f8 ops paid g5).map (fun c => (c.1,c.2.1.toNat,c.2.2.toNat))) with
    | none => simp [hm] at h
    | some mw =>
      simp only [hm,Option.bind_some] at h
      obtain ⟨wsP,hbp,heq⟩ := qx (subcube ci.1 ci.2.1) (k4 ow f8 ops paid g5)
        (vars g.mask) _ mw (zg (subcube ci.1 ci.2.1) (vars g.mask)) hm
      have hsc:=vg (subcube ci.1 ci.2.1) wsP mw heq ws 0
      rcases hs : my (subcube ci.1 ci.2.1).toNat mw (ws.map (fun w => w.1.toNat)) 1 with ⟨cm,jd,bad⟩
      rw [show (1 <<< 0)=1 from rfl,hs] at hsc;dsimp only at hsc;rw [hs] at h;dsimp only at h
      injection h with hqp;subst hqp
      refine ⟨⟨subcube ci.1 ci.2.1,ci.2.2.2.2,(k4 ow f8 ops paid g5).length,wsP⟩,?_,?_⟩
      · simp [pe,er,materialize,hbp]
      · refine ⟨rfl,rfl,by simp,heq,hsc.1,fun i => by simpa using hsc.2.1 i,fun i => by simpa using hsc.2.2.1 i⟩
def pg (s:QPN) (k i j z:Nat) (un ka kb:Bool) : Bool :=
  let (dom,bnd,paid,p3,jd,bad,mw):=s
  let drop:=(if ka then 0 else 1 <<< i) ||| (if un||kb then 0 else 1 <<< j)
  if (bad ||| drop) != drop then false else
  let la:=if ka then 0 else (jd >>> i) &&& 1
  let lb:=if un||kb then 0 else (jd >>> j) &&& 1
  let lhs:=k+paid
  let rhs:=bnd+(p3 - la - lb)
  if lhs+1 < rhs then
    if (((bad >>> i) &&& 1) == 0)&&(un||(((bad >>> j) &&& 1) == 0)) then true
    else let zm:=z &&& dom;zm == 0||zm == dom||mw.any (fun v => v == zm)
  else if lhs > rhs then false
  else
    let zm:=z &&& dom
    let zc:=zm == 0||zm == dom
    if lhs == rhs then zc
    else zc||mw.any (fun v => v == zm)
lemma rq {bad drop t:Nat} (h:(bad ||| drop)=drop) (hb:((bad >>> t) &&& 1)=1) :
    ((drop >>> t) &&& 1)=1:=by
  have h1:=congrArg (fun x => x.testBit t) h
  have h2:=congrArg (fun x => x.testBit 0) hb
  simp only [Nat.testBit_or,Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_one_zero,Bool.and_true,Nat.add_zero] at h1 h2;rw [h2,Bool.true_or] at h1;apply Nat.eq_of_testBit_eq;intro u
  cases u with
  | zero => simp only [Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_one_zero,Bool.and_true,Nat.add_zero,h1.symm]
  | succ u => simp only [Nat.testBit_and,j9,Bool.and_false]
lemma qe {un ka kb a b ws w} (nd:ws.Nodup) (h:w ∈ gd un ka kb a b ws) :
    (ka||w != a)=true∧(un||kb||w != b)=true:=by
  unfold gd at h
  by_cases hun : un=true
  · rw [if_pos hun] at h;simp only [hun,Bool.true_or,and_true]
    cases ka
    · simp only [j1,Bool.false_eq_true,ite_false] at h
      simp only [Bool.false_or,bne_iff_ne];exact fun e => nd.not_mem_erase (e ▸ h)
    · simp
  · rw [if_neg hun] at h
    simp only [px] at h
    have h1 : w ∈ j1 ws a ka:=(ko _ b kb).subset h
    have hnd1 : (j1 ws a ka).Nodup:=nd.sublist (ko ws a ka)
    constructor
    · cases ka
      · simp only [j1,Bool.false_eq_true,ite_false] at h1
        simp only [Bool.false_or,bne_iff_ne];exact fun e => nd.not_mem_erase (e ▸ h1)
      · simp
    · cases kb
      · simp only [j1,Bool.false_eq_true,ite_false] at h
        simp only [Bool.eq_false_iff.mpr hun,Bool.false_or,bne_iff_ne];exact fun e => hnd1.not_mem_erase (e ▸ h)
      · simp
lemma rr {p ws qp k i j op ka kb} (hqv:pf p ws qp)
    (hi:i < ws.length) (hj:j < ws.length) (nd:(ws.map Prod.fst).Nodup)
    (ne:(op == 2)=false→ i ≠ j)
    (h:pg qp k i j (choiceVal (fx op (ws.getD i f0) (ws.getD j f0))).toNat (op == 2) ka kb=true) :
    scalarPoolCut p k ((gd (op == 2) ka kb (ws.getD i f0) (ws.getD j f0) ws).map Prod.fst)
      (fx op (ws.getD i f0) (ws.getD j f0))=true:=by
  rcases qp with ⟨dom,bnd,paid,p3,jd,bad,mw⟩
  obtain ⟨hdom,hbnd,hpaid,hmw,hcm,hcmask,hbad⟩ := hqv
  dsimp only at hdom hbnd hpaid hmw hcm hcmask hbad;subst hdom hbnd hpaid;unfold pg at h;dsimp only at h
  set a:=ws.getD i f0
  set b:=ws.getD j f0
  set un:=(op == 2)
  set z:=choiceVal (fx op a b)
  set drop:=(if ka then 0 else 1 <<< i) ||| (if un||kb then 0 else 1 <<< j)
  by_cases hbd : ((bad ||| drop) != drop)=true
  · rw [if_pos hbd] at h;cases h
  · rw [if_neg hbd] at h
    have hbd_eq : (bad ||| drop)=drop:=by
      simpa [bne_iff_ne] using hbd
    have hrest_av : ((gd un ka kb a b ws).map Prod.fst).all (fd p.domain p.wires)=true:=by
      apply List.all_eq_true.mpr;intro s hs
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hs
      have hws_m : w ∈ ws:=(nm ws a b un ka kb).subset hw
      obtain ⟨t,ht,hwt⟩ := List.getElem_of_mem hws_m
      have hget : ws.getD t f0=w:=by simp [List.getD_eq_getElem?_getD,ht,hwt]
      have hbt:=hbad t;rw [if_pos ht,hget] at hbt
      by_cases hav : fd p.domain p.wires w.1=true
      · exact hav
      · have havf : fd p.domain p.wires w.1=false:=Bool.eq_false_iff.mpr hav
        rw [havf] at hbt;simp only [Bool.not_false,Bool.toNat_true] at hbt
        have hd1:=rq hbd_eq hbt
        have hdrop0 : ((drop >>> t) &&& 1)=0:=by
          have hmem:=qe (List.Nodup.of_map Prod.fst nd) hw
          have hti : !ka→ t ≠ i:=fun hnk he => by
            subst he;have hwa : w=a:=hget.symm
            have h1:=hmem.1;rw [show ka=false by cases ka <;> simp_all] at h1
            simp only [Bool.false_or,bne_iff_ne] at h1;exact h1 hwa
          have htj : !(un||kb)→ t ≠ j:=fun hnk he => by
            subst he;have hwb : w=b:=hget.symm
            have h2:=hmem.2;rw [show (un||kb)=false by cases un <;> cases kb <;> simp_all] at h2
            simp only [Bool.false_or,bne_iff_ne] at h2;exact h2 hwb
          have hpart1 : (((if ka then 0 else 1 <<< i) >>> t) &&& 1)=0:=by
            cases hka : ka
            · simp only [Bool.false_eq_true,ite_false]
              have hne : t ≠ i:=hti (by simp [hka])
              rw [show (1 <<< i)=(0 ||| (1 <<< i)) by simp,h8,if_neg hne];simp
            · simp
          have hpart2 : (((if un||kb then 0 else 1 <<< j) >>> t) &&& 1)=0:=by
            cases huk : (un||kb)
            · simp only [Bool.false_eq_true,ite_false]
              have hne : t ≠ j:=htj (by simp [huk])
              rw [show (1 <<< j)=(0 ||| (1 <<< j)) by simp,h8,if_neg hne];simp
            · simp
          apply Nat.eq_of_testBit_eq;intro u
          have h1:=congrArg (fun x => x.testBit u) hpart1
          have h2:=congrArg (fun x => x.testBit u) hpart2
          cases u with
          | zero =>
            simp only [drop,Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_or,Nat.testBit_one_zero,Bool.and_true,Nat.add_zero,Nat.zero_testBit] at h1 h2 ⊢
            rw [h1,h2];rfl
          | succ u =>
            simp only [Nat.testBit_and,j9,Bool.and_false,Nat.zero_testBit]
        omega
    let jm:=fun w : ff => f5 p.domain w.1
    let rest:=gd un ka kb a b ws
    have ck:=tp jm ws a b un ka kb
    change ws.countP jm - fl jm a ka - fl jm b (un||kb) ≤ rest.countP jm at ck
    have hla : (if ka then 0 else (jd >>> i) &&& 1)=fl jm a ka:=by
      cases ka <;> simp [fl,jm,a,hcmask i,hi]
    have hlb : (if un||kb then 0 else (jd >>> j) &&& 1)=fl jm b (un||kb):=by
      cases (un||kb) <;> simp [fl,jm,b,hcmask j,hj]
    have hzc : (z.toNat &&& p.domain.toNat == 0||z.toNat &&& p.domain.toNat == p.domain.toNat)=f5 p.domain z:=l9 p.domain z
    have hza : (z.toNat &&& p.domain.toNat == 0||z.toNat &&& p.domain.toNat == p.domain.toNat||mw.any (fun v => v == (z.toNat &&& p.domain.toNat))) =
        fd p.domain p.wires z:=jo p.domain p.wires mw hmw z
    have hab_av : (((bad >>> i) &&& 1 == 0)&&(un||((bad >>> j) &&& 1 == 0)))=true→ j5 p.domain p.wires (fx op a b)=true:=by
      intro hok;simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
      have hai : fd p.domain p.wires a.1=true:=by
        have hbi:=hbad i;rw [if_pos hi,hok.1] at hbi
        cases h1 : fd p.domain p.wires a.1
        · change 0=(!fd p.domain p.wires a.1).toNat at hbi;rw [h1] at hbi;simp at hbi
        · rfl
      simp only [j5,fx,hai,Bool.true_and]
      rcases hok.2 with hun | hbj0
      · simp [un] at hun;simp [hun]
      · have haj : fd p.domain p.wires b.1=true:=by
          have hbj:=hbad j;rw [if_pos hj,hbj0] at hbj
          cases h1 : fd p.domain p.wires b.1
          · change 0=(!fd p.domain p.wires b.1).toNat at hbj;rw [h1] at hbj;simp at hbj
          · rfl
        simp [haj,Bool.or_true]
    rw [hla,hlb,hcm] at h
    set la:=fl jm a ka
    set lb:=fl jm b (un||kb)
    set lhs:=k+p.paid
    set rhs:=p.bound+(ws.countP jm - la - lb)
    simp only [scalarPoolCut,hrest_av,Bool.and_true,Bool.not_not,List.countP_cons,List.countP_map,Function.comp_def,
      Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
    change lhs+(!fd p.domain p.wires z).toNat < p.bound+(rest.countP jm+if f5 p.domain z=true then 1 else 0) ∧
      (fd p.domain p.wires z=true∨j5 p.domain p.wires (fx op a b)=true)
    split at h
    · split at h
      next hclean =>
        refine ⟨?_,Or.inr (hab_av hclean)⟩
        cases fd p.domain p.wires z <;> cases f5 p.domain z <;> simp <;> omega
      next =>
        rw [hza] at h;refine ⟨?_,Or.inl h⟩;rw [h];cases f5 p.domain z <;> simp <;> omega
    · split at h
      · cases h
      · by_cases heq : (lhs == rhs)=true
        · rw [if_pos heq] at h;rw [hzc] at h
          have hfa : fd p.domain p.wires z=true:=by rw [← hza];simp only [l9 p.domain z,h,Bool.true_or]
          exact ⟨by rw [hfa,h];simp;omega,Or.inl hfa⟩
        · rw [if_neg heq] at h;rw [hza] at h
          have hne : lhs ≠ rhs:=fun e => heq (beq_iff_eq.mpr e)
          refine ⟨?_,Or.inl h⟩;rw [h];cases f5 p.domain z <;> simp <;> omega
lemma qy (d u:Sig) : (neg u).toNat &&& d.toNat=d.toNat ^^^ (u.toNat &&& d.toNat):=by
  apply Nat.eq_of_testBit_eq;intro j;rw [Nat.testBit_and,Nat.testBit_xor,Nat.testBit_and,neg,jf,Nat.testBit_xor]
  by_cases hj : j < 512
  · have ha : (BitVec.allOnes 512).toNat.testBit j=true:=by
      change (BitVec.allOnes 512).getLsbD j=true;rw [BitVec.getLsbD_allOnes];simp [hj]
    rw [ha];cases u.toNat.testBit j <;> cases d.toNat.testBit j <;> rfl
  · have hd : d.toNat.testBit j=false:=Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le d.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hd]
def lc (domN:Nat) (mp:List Nat) (lim:Nat) : List Nat→ Nat→ Bool
  | [],e => e < lim
  | u :: us,e =>
    if e >= lim then false
    else
      let m:=u &&& domN
      if m == 0||m == domN||mp.any (fun v => v == m) then lc domN mp lim us e
      else if e+1 < lim&&mp.any (fun v => v == (domN ^^^ m)) then lc domN mp lim us (e+1)
      else false
lemma nv {f:Row→ Row} {dom:Sig} (hdom:∀ r,bit (f r) dom=true)
    {roots:List (fp Row)} {ws:List Sig} {mp:List Nat} {lim:Nat}
    (hmw:∀ m,(m == 0||m == dom.toNat||mp.any (· == m)) =
      (m == 0||m == dom.toNat||(ws.map (fun w => w.toNat &&& dom.toNat)).any (· == m)))
    (fs:List Sig) :
    ∀ {f8 p} (e:Nat),
      fv roots p f8→ je f f8 ws →
      lc dom.toNat mp lim (fs.map BitVec.toNat) e=true →
      ∃ e' f8',e+e' < lim∧fv roots (p+e') f8' ∧
        (∀ v,fc f8 v→ fc f8' v)∧je f f8' fs:=by
  induction fs with
  | nil =>
    intro f8 p e hr _ ok;simp only [List.map_nil,lc,decide_eq_true_eq] at ok;exact ⟨0,f8,by omega,by simpa using hr,fun _ h => h,fun _ h => by cases h⟩
  | cons u us ih =>
    intro f8 p e hr hs ok;simp only [List.map_cons,lc] at ok
    by_cases hge : e ≥ lim
    · rw [if_pos hge] at ok;cases ok
    · rw [if_neg hge] at ok
      by_cases hu : (u.toNat &&& dom.toNat == 0||u.toNat &&& dom.toNat == dom.toNat||mp.any (fun v => v == (u.toNat &&& dom.toNat)))=true
      · rw [if_pos hu] at ok
        have hav : fd dom ws u=true:=by rw [← jo dom ws mp hmw u];exact hu
        obtain ⟨e',f8',hlt,hr',hinc,hs'⟩ := ih e hr hs ok
        refine ⟨e',f8',hlt,hr',hinc,fun a ha => ?_⟩
        rcases List.mem_cons.mp ha with rfl | hmem
        · exact hinc _ (g2 hdom hs hav)
        · exact hs' a hmem
      · rw [if_neg hu] at ok
        by_cases hnu : (decide (e+1 < lim)&&mp.any (fun v => v == (dom.toNat ^^^ (u.toNat &&& dom.toNat))))=true
        · rw [if_pos hnu] at ok;simp only [Bool.and_eq_true,decide_eq_true_eq] at hnu
          have havn : fd dom ws (neg u)=true:=by
            rw [← jo dom ws mp hmw (neg u)];unfold ju;rw [qy];simp [hnu.2]
          have hna : fc f8 (f6 f (f7 (neg u))):=g2 hdom hs havn
          let bank1:=t5 (f6 f (f7 (neg u))) :: f8
          obtain ⟨e1,f8',hlt,hr',hinc,hs'⟩ := ih (e+1) (fv.one hr hna) (fun a ha => jx _ (hs a ha)) ok
          have hinv : t5 (f6 f (f7 (neg u)))=f6 f (f7 u):=by
            funext r;unfold t5 f6 f7;rw [bit_neg,Bool.not_not]
          refine ⟨1+e1,f8',by omega,by simpa [Nat.add_assoc] using hr',fun v hv => hinc v (jx _ hv),fun a ha => ?_⟩
          rcases List.mem_cons.mp ha with rfl | hmem
          · exact hinc _ (by rw [← hinv];exact Or.inl (by simp [bank1]))
          · exact hs' a hmem
        · rw [if_neg hnu] at ok;cases ok
lemma nw (d a:Sig) : f5 d (neg a)=f5 d a:=by
  have hneg : neg a &&& d=(a &&& d) ^^^ d:=by
    apply BitVec.eq_of_getLsbD_eq;intro j hj;simp only [neg,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,hj,decide_true,Bool.true_and]
    cases a.getLsbD j <;> cases d.getLsbD j <;> rfl
  have h1 : (neg a &&& d == zero)=(a &&& d == d):=by
    rw [hneg,Bool.eq_iff_iff,beq_iff_eq,beq_iff_eq];constructor
    · intro h;apply BitVec.eq_of_getLsbD_eq;intro j hj
      have hb:=congrArg (fun x:Sig => x.getLsbD j) h
      simp only [zero,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_zero] at hb
      cases h1 : a.getLsbD j <;> cases h2 : d.getLsbD j <;> simp [h1,h2] at hb ⊢
    · intro h;rw [h,zero];exact BitVec.xor_self
  have h2 : (neg a &&& d == d)=(a &&& d == zero):=by
    rw [hneg,Bool.eq_iff_iff,beq_iff_eq,beq_iff_eq];constructor
    · intro h;apply BitVec.eq_of_getLsbD_eq;intro j hj
      have hb:=congrArg (fun x:Sig => x.getLsbD j) h
      simp only [zero,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_zero] at hb ⊢
      cases h1 : a.getLsbD j <;> cases h2 : d.getLsbD j <;> simp [h1,h2] at hb ⊢
    · intro h;rw [h,zero];exact BitVec.zero_xor
  simp only [f5,k0,h1,h2,Bool.or_comm]
lemma ny {d:Sig} {ds:List ff} {fs:List Sig}
    (hfa:List.Forall₂ (fun x y => y=x.1∨y=neg x.1) ds fs) :
    fs.countP (f5 d)=ds.countP (fun x => f5 d x.1):=by
  induction hfa with
  | nil => rfl
  | @cons x y xs ys hhd _ ih =>
    simp only [List.countP_cons,ih]
    rcases hhd with rfl | rfl
    · rfl
    · rw [nw]
abbrev DMP:=Nat × Nat × List Nat × Option (List Nat)
def zh (k' i j aN bN zN:Nat) (un ka kb:Bool) (qp:QPN) : Option DMP :=
  let (domN,bnd,paid,p3,jd,_,mw):=qp
  let la:=if ka then 0 else (jd >>> i) &&& 1
  let lb:=if un||kb then 0 else (jd >>> j) &&& 1
  let zm:=zN &&& domN
  let nc:=(p3 - la - lb)+(if zm == 0||zm == domN then 1 else 0)
  if k' + paid ≥ bnd+nc then none
  else
    let lim:=bnd+nc - (k' + paid)
    let mw2:=if lim > 1&&ju domN mw aN&&(un||ju domN mw bN) then
      some (if zm == 0||zm == domN then mw else zm :: mw)
    else none
    some (domN,lim,mw,mw2)
def l7 (dp:DMP) (fs:List Nat) : Bool :=
  let (domN,lim,mw,mw2):=dp
  if lc domN mw lim fs 0 then true
  else match mw2 with
    | none => false
    | some mw' => lc domN mw' (lim - 1) fs 0
lemma pl {raw T p ws qp dp k' i j op ka kb} {fs:List Sig}
    (lz:ValidPool raw T p) (hqv:pf p ws qp)
    (hi:i < ws.length) (hj:j < ws.length)
    (hrun:kw (f7 T) k' (fs.map f7))
    (hnc_le:(fm op (ws.getD i f0) (ws.getD j f0) ::
        gd (op == 2) ka kb (ws.getD i f0) (ws.getD j f0) ws).countP (fun w => f5 p.domain w.1) ≤
      fs.countP (f5 p.domain))
    (hmk:zh k' i j (ws.getD i f0).1.toNat (ws.getD j f0).1.toNat
      (choiceVal (fx op (ws.getD i f0) (ws.getD j f0))).toNat (op == 2) ka kb qp=some dp)
    (hcut:l7 dp (fs.map BitVec.toNat)=true) : False:=by
  rcases qp with ⟨domN,bnd,paid,p3,jd,bad,mw⟩
  obtain ⟨hdom,hbnd,hpaid,hmw,hcm,hcmask,_⟩ := hqv
  dsimp only at hdom hbnd hpaid hmw hcm hcmask;subst hdom hbnd hpaid
  obtain ⟨f,roots,f8,dom,nc0,lo,hp,hs,_⟩ := lz
  set a:=ws.getD i f0
  set b:=ws.getD j f0
  set un:=(op == 2)
  set z:=choiceVal (fx op a b)
  let jm:=fun w : ff => f5 p.domain w.1
  have ck:=tp jm ws a b un ka kb
  have hla : (if ka then 0 else (jd >>> i) &&& 1)=fl jm a ka:=by
    cases ka <;> simp [fl,jm,a,hcmask i,hi]
  have hlb : (if un||kb then 0 else (jd >>> j) &&& 1)=fl jm b (un||kb):=by
    cases (un||kb) <;> simp [fl,jm,b,hcmask j,hj]
  have hzc : (z.toNat &&& p.domain.toNat == 0||z.toNat &&& p.domain.toNat == p.domain.toNat)=f5 p.domain z:=l9 p.domain z
  have hval : (fm op a b).1=z:=sf op a b
  have hnc_bound : (p3 - (if ka then 0 else (jd >>> i) &&& 1) - (if un||kb then 0 else (jd >>> j) &&& 1)) +
      (if z.toNat &&& p.domain.toNat == 0||z.toNat &&& p.domain.toNat == p.domain.toNat then 1 else 0) ≤
      fs.countP (f5 p.domain):=by
    change p3=ws.countP jm at hcm;rw [hcm,hla,hlb,hzc];simp only [List.countP_cons,hval] at hnc_le;change ws.countP jm - fl jm a ka - fl jm b (un||kb) ≤ (gd un ka kb a b ws).countP jm at ck;change (gd un ka kb a b ws).countP jm+(if f5 p.domain z=true then 1 else 0) ≤ fs.countP (f5 p.domain) at hnc_le;omega
  unfold zh at hmk;dsimp only at hmk
  set nc:=(p3 - (if ka then 0 else (jd >>> i) &&& 1) - (if un||kb then 0 else (jd >>> j) &&& 1)) +
      (if z.toNat &&& p.domain.toNat == 0||z.toNat &&& p.domain.toNat == p.domain.toNat then 1 else 0)
  by_cases hge : k' + p.paid ≥ p.bound+nc
  · rw [if_pos hge] at hmk;cases hmk
  · rw [if_neg hge] at hmk;injection hmk with hdp;subst hdp
    unfold l7 at hcut;dsimp only at hcut
    set lim:=p.bound+nc - (k' + p.paid)
    by_cases ha0 : lc p.domain.toNat mw lim (fs.map BitVec.toNat) 0=true
    · obtain ⟨e',f8',hlt,hr',_,hs'⟩ := nv dom hmw fs 0 hp hs ha0
      have fk : m6 f8' ((fs.map f7).map (f6 f)):=by
        intro v hv;obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv;obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hm;exact hs' _ hu
      have bnd_lo:=jk f hrun nc0 hr' fk lo
      have cm:=kk dom fs;omega
    · rw [if_neg ha0] at hcut
      by_cases hch : (decide (lim > 1)&&ju p.domain.toNat mw a.1.toNat&&(un||ju p.domain.toNat mw b.1.toNat))=true
      · rw [if_pos hch] at hcut;dsimp only at hcut
        simp only [Bool.and_eq_true,decide_eq_true_eq] at hch
        have hok : j5 p.domain p.wires (fx op a b)=true:=by
          simp only [j5,fx,Bool.and_eq_true,← jo p.domain p.wires mw hmw];exact ⟨hch.1.2,hch.2⟩
        obtain ⟨out,hro,hso⟩ := pu dom hp hs (fx op a b) hok
        have hmw2 : ∀ m,(m == 0||m == p.domain.toNat ||
            (if z.toNat &&& p.domain.toNat == 0||z.toNat &&& p.domain.toNat == p.domain.toNat
             then mw else (z.toNat &&& p.domain.toNat) :: mw).any (· == m)) =
            (m == 0||m == p.domain.toNat||((z :: p.wires).map (fun w => w.toNat &&& p.domain.toNat)).any (· == m)):=by
          intro m
          by_cases hzc' : (z.toNat &&& p.domain.toNat == 0||z.toNat &&& p.domain.toNat == p.domain.toNat)=true
          · rw [if_pos hzc',hmw m];simp only [List.map_cons,List.any_cons]
            by_cases hme : (z.toNat &&& p.domain.toNat == m)=true
            · rw [← beq_iff_eq.mp hme];simp [hzc']
            · simp [hme]
          · rw [if_neg hzc'];simp only [List.map_cons,List.any_cons]
            have hm1:=hmw m
            cases hb1 : (m == 0||m == p.domain.toNat) <;> cases hb2 : (z.toNat &&& p.domain.toNat == m)
            · simp only [hb1,hb2,Bool.false_or] at hm1 ⊢;exact hm1
            · simp [hb1,hb2]
            · simp [hb1,hb2]
            · simp [hb1,hb2]
        obtain ⟨e',f8',hlt,hr',_,hs'⟩ := nv dom hmw2 fs 0 hro hso hcut
        have fk : m6 f8' ((fs.map f7).map (f6 f)):=by
          intro v hv;obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv;obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hm;exact hs' _ hu
        have bnd_lo:=jk f hrun nc0 hr' fk lo
        have cm:=kk dom fs;omega
      · rw [if_neg hch] at hcut;cases hcut
def mz (st:Nat × Nat) (d:n7) : Nat × Nat :=
  let b:=d.2.1 ^^^ d.2.2
  (st.1 ||| b,(b ^^^ (b &&& st.1)) ||| (st.2 ^^^ (st.2 &&& b)))
def ss (ds:List n7) : Nat:=(ds.foldl mz (0,0)).2
lemma w5 (ds:List n7) (j:Nat) :
    ∀ u1 uu : Nat,
      (u1.testBit j=false→ uu.testBit j=false) →
      let res:=ds.foldl mz (u1,uu)
      (res.1.testBit j=(u1.testBit j||ds.any (fun d => (d.2.1 ^^^ d.2.2).testBit j))) ∧
      (res.2.testBit j=true →
        (u1.testBit j=false∧ds.countP (fun d => (d.2.1 ^^^ d.2.2).testBit j)=1) ∨
        (uu.testBit j=true∧ds.countP (fun d => (d.2.1 ^^^ d.2.2).testBit j)=0)):=by
  induction ds with
  | nil =>
    intro u1 uu hinv;simp only [List.foldl_nil,List.any_nil,Bool.or_false,true_and];intro h;exact Or.inr ⟨h,rfl⟩
  | cons d rest ih =>
    intro u1 uu hinv;simp only [List.foldl_cons,List.any_cons,List.countP_cons]
    have hinv' : (mz (u1,uu) d).1.testBit j=false→ (mz (u1,uu) d).2.testBit j=false:=by
      unfold mz;dsimp only;simp only [Nat.testBit_or,Nat.testBit_xor,Nat.testBit_and]
      cases h1 : u1.testBit j <;> cases h2 : uu.testBit j <;> cases hb : (d.2.1 ^^^ d.2.2).testBit j <;> simp_all
    obtain ⟨hr1,hr2⟩ := ih (mz (u1,uu) d).1 (mz (u1,uu) d).2 hinv'
    refine ⟨?_,?_⟩
    · rw [hr1];unfold mz;dsimp only;simp [Nat.testBit_or,Bool.or_assoc]
    · intro hres
      have hsub:=hr2 hres
      unfold mz at hsub;dsimp only at hsub;simp only [Nat.testBit_or,Nat.testBit_xor,Nat.testBit_and] at hsub
      have hxb : (d.2.1 ^^^ d.2.2).testBit j=(d.2.1.testBit j ^^ d.2.2.testBit j):=Nat.testBit_xor _ _ _
      rcases hsub with ⟨h1',hc1⟩ | ⟨h2',hc0⟩
      · cases h1 : u1.testBit j <;> cases hb1 : d.2.1.testBit j <;> cases hb2 : d.2.2.testBit j <;>
          simp [h1,hb1,hb2] at h1'
        all_goals exact Or.inl ⟨rfl,by rw [hxb,hb1,hb2];simpa [Nat.testBit_xor] using hc1⟩
      · cases h1 : u1.testBit j <;> cases h2 : uu.testBit j <;> cases hb1 : d.2.1.testBit j <;> cases hb2 : d.2.2.testBit j <;>
          simp [h1,h2,hb1,hb2] at h2'
        all_goals first
          | exact Or.inl ⟨rfl,by rw [hxb,hb1,hb2];simpa [Nat.testBit_xor] using hc0⟩
          | exact Or.inr ⟨rfl,by rw [hxb,hb1,hb2];simpa [Nat.testBit_xor] using hc0⟩
lemma th (ds:List n7) (j:Nat) (hu:(ss ds).testBit j=true) :
    ds.countP (fun d => (d.2.1 ^^^ d.2.2).testBit j)=1:=by
  have h:=(w5 ds j 0 0 (by simp)).2 hu
  rcases h with ⟨_,hc⟩ | ⟨h0,_⟩
  · exact hc
  · simp at h0
lemma mg (r s:Fin 768→ Row) {d:ff} (hf:fj r s d) :
    (d.2.1.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat))=(fq true (fi r s d.1)).toNat:=by
  rw [← g7];exact congrArg BitVec.toNat (by rw [hf];rfl)
lemma ph (r s:Fin 768→ Row) {d:ff} (hf:fj r s d) :
    (d.2.2.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat))=(fq true (fi r s (neg d.1))).toNat:=by
  rw [Nat.and_comm,← g7];apply congrArg BitVec.toNat
  have hnp : (fi r s (neg d.1)).1 = ~~~(fi r s d.1).1:=pv r d.1
  have hnq : (fi r s (neg d.1)).2 = ~~~(fi r s d.1).2:=pv s d.1
  apply BitVec.eq_of_getLsbD_eq;intro j hj
  have hp:=congrArg (fun x => x.1.getLsbD j) hf
  have hq:=congrArg (fun x => x.2.getLsbD j) hf
  simp only [fq,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,hj,decide_true,Bool.true_and,hnp,hnq];rw [hp,hq,Bool.not_not,Bool.and_comm]
lemma m4 (d:ff) (r s:Fin 768→ Row) (hf:fj r s d) {u:Sig}
    (hu:u=d.1∨u=neg d.1) (j:Nat) :
    (fq true (fi r s u)).toNat.testBit j=true→ (d.2.1.toNat ^^^ d.2.2.toNat).testBit j=true:=by
  intro hb
  rcases hu with rfl | rfl
  · rw [← mg r s hf] at hb
    simp only [Nat.testBit_xor,Nat.testBit_and] at hb ⊢
    cases h1 : d.2.1.toNat.testBit j <;> cases h2 : d.2.2.toNat.testBit j <;> simp [h1,h2] at hb ⊢
  · rw [← ph r s hf] at hb
    simp only [Nat.testBit_xor,Nat.testBit_and] at hb ⊢
    cases h1 : d.2.1.toNat.testBit j <;> cases h2 : d.2.2.toNat.testBit j <;> simp [h1,h2] at hb ⊢
def k9 (uu:Nat) : List n7→ List Nat→ Nat→ List (Nat × Nat × Nat) →
    Option (List Nat × Nat × List (Nat × Nat × Nat))
  | [],acc,cov,free => some (acc,cov,free)
  | (s,p,q) :: ds,acc,cov,free =>
    let pq:=p &&& q
    let cp:=p ^^^ pq
    let cn:=q ^^^ pq
    let hp:=(uu &&& cp) != 0
    let hn:=(uu &&& cn) != 0
    if hp&&hn then none
    else if hp then k9 uu ds (s :: acc) (cov ||| cp) free
    else if hn then k9 uu ds ((lr ^^^ s) :: acc) (cov ||| cn) free
    else k9 uu ds acc cov ((s,cp,cn) :: free)
lemma n4 {a b:Nat} (h:(a &&& b != 0)=true) : ∃ j,a.testBit j=true∧b.testBit j=true:=by
  have hne : a &&& b ≠ 0:=by simpa [bne_iff_ne] using h
  by_contra hall;push Not at hall
  apply hne;apply Nat.eq_of_testBit_eq;intro j;rw [Nat.testBit_and,Nat.zero_testBit]
  cases ha : a.testBit j
  · rfl
  · simp [hall j ha]
lemma forall₂_split {α β} {R : α → β → Prop} {l1 l2:List α} {f1 f2:List β} {d : α} {u : β}
    (hfa:List.Forall₂ R (l1 ++ d :: l2) (f1 ++ u :: f2)) (hlen:l1.length=f1.length) :
    List.Forall₂ R l1 f1∧R d u∧List.Forall₂ R l2 f2:=by
  induction l1 generalizing f1 with
  | nil =>
    cases f1 with
    | nil => cases hfa with | cons h1 h2 => exact ⟨List.Forall₂.nil,h1,h2⟩
    | cons _ _ => simp at hlen
  | cons a l1 ih =>
    cases f1 with
    | nil => simp at hlen
    | cons b f1 =>
      cases hfa with
      | cons h1 h2 =>
        obtain ⟨hl1,hdu,hl2⟩ := ih h2 (by simpa using hlen)
        exact ⟨List.Forall₂.cons h1 hl1,hdu,hl2⟩
lemma wz (a:Sig) : a ≠ neg a:=by
  intro h
  have h0:=congrArg (fun x:Sig => x.getLsbD 0) h
  simp only [neg,BitVec.getLsbD_not,show (0:Nat) < 512 by decide,decide_true,Bool.true_and] at h0
  cases ha : a.getLsbD 0 <;> simp [ha] at h0
lemma ls {r s:Fin 768→ Row} {l1 l2:List ff} {f1 f2:List Sig} {d:ff} {u:Sig}
    (hfa:List.Forall₂ (fun x y => y=x.1∨y=neg x.1) (l1 ++ d :: l2) (f1 ++ u :: f2))
    (hlen:l1.length=f1.length)
    (hfaith:∀ x ∈ l1 ++ d :: l2,fj r s x)
    (hcov:(fk true (fi r s) (f1 ++ u :: f2)).toNat=g9)
    {j:Nat} (hu:(ss ((l1 ++ d :: l2).map fb)).testBit j=true) :
    ((d.2.1.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat)).testBit j=true→ u=d.1) ∧
    ((d.2.2.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat)).testBit j=true→ u=neg d.1):=by
  obtain ⟨hfa1,hdu,hfa2⟩ := forall₂_split hfa hlen
  have hcnt:=th ((l1 ++ d :: l2).map fb) j hu
  rw [List.countP_map,List.countP_append,List.countP_cons] at hcnt
  have hother : ∀ x ∈ l1 ++ l2,(d.2.1.toNat ^^^ d.2.2.toNat).testBit j=true→ (x.2.1.toNat ^^^ x.2.2.toNat).testBit j=false:=by
    intro x hx hd0;simp only [Function.comp_def,fb,hd0,ite_true] at hcnt
    have h0 : l1.countP (fun x => (x.2.1.toNat ^^^ x.2.2.toNat).testBit j)=0 ∧
              l2.countP (fun x => (x.2.1.toNat ^^^ x.2.2.toNat).testBit j)=0:=by omega
    rcases List.mem_append.mp hx with hxl | hxr
    · exact Bool.eq_false_iff.mpr (fun ht => by
        have hp : 0 < l1.countP (fun x => (x.2.1.toNat ^^^ x.2.2.toNat).testBit j):=List.countP_pos_iff.mpr ⟨x,hxl,ht⟩
        omega)
    · exact Bool.eq_false_iff.mpr (fun ht => by
        have hp : 0 < l2.countP (fun x => (x.2.1.toNat ^^^ x.2.2.toNat).testBit j):=List.countP_pos_iff.mpr ⟨x,hxr,ht⟩
        omega)
  have hfa_mem {xs:List ff} {ys:List Sig} (h:List.Forall₂ (fun x y => y=x.1∨y=neg x.1) xs ys) {y} (hy:y ∈ ys) :
      ∃ x ∈ xs,y=x.1∨y=neg x.1:=by
    induction h with
    | nil => cases hy
    | cons hr _ ih =>
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact ⟨_,List.mem_cons_self,hr⟩
      · obtain ⟨x,hx,hxy⟩ := ih hy';exact ⟨x,List.mem_cons_of_mem _ hx,hxy⟩
  have hmust_u (hj:j < 768) (hd0:(d.2.1.toNat ^^^ d.2.2.toNat).testBit j=true) :
      (fq true (fi r s u)).toNat.testBit j=true:=by
    have hbit : (fk true (fi r s) (f1 ++ u :: f2)).getLsbD j=true:=by
      change (fk true (fi r s) (f1 ++ u :: f2)).toNat.testBit j=true;rw [hcov,gj];change (BitVec.allOnes 768).getLsbD j=true;rw [BitVec.getLsbD_allOnes];simp [hj]
    obtain ⟨y,hy,hyb⟩ := (jz (i:=⟨j,hj⟩)).mp hbit
    have hybN : (fq true (fi r s y)).toNat.testBit j=true:=hyb
    simp only [List.mem_append,List.mem_cons] at hy
    rcases hy with hyl | rfl | hyr
    · obtain ⟨x,hx,hxy⟩ := hfa_mem hfa1 hyl
      have hxb:=m4 x r s (hfaith x (by simp [hx])) hxy j hybN
      have hxf:=hother x (List.mem_append_left _ hx) hd0
      rw [hxb] at hxf;cases hxf
    · exact hybN
    · obtain ⟨x,hx,hxy⟩ := hfa_mem hfa2 hyr
      have hxb:=m4 x r s (hfaith x (by simp [hx])) hxy j hybN
      have hxf:=hother x (List.mem_append_right _ hx) hd0
      rw [hxb] at hxf;cases hxf
  have hd_faith:=hfaith d (by simp)
  constructor
  · intro hcp
    have hp1 : d.2.1.toNat.testBit j=true∧d.2.2.toNat.testBit j=false:=by
      simp only [Nat.testBit_xor,Nat.testBit_and] at hcp
      cases h1 : d.2.1.toNat.testBit j <;> cases h2 : d.2.2.toNat.testBit j <;> simp_all
    have hj : j < 768:=by
      by_contra hge
      have:=Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le d.2.1.isLt (Nat.pow_le_pow_right (by omega) (by omega:768 ≤ j)))
      rw [hp1.1] at this;cases this
    have hd0 : (d.2.1.toNat ^^^ d.2.2.toNat).testBit j=true:=by simp [Nat.testBit_xor,hp1.1,hp1.2]
    have hu_b:=hmust_u hj hd0
    rcases hdu with rfl | rfl
    · rfl
    · rw [← ph r s hd_faith] at hu_b
      simp only [Nat.testBit_xor,Nat.testBit_and,hp1.1,hp1.2] at hu_b;cases hu_b
  · intro hcn
    have hq1 : d.2.1.toNat.testBit j=false∧d.2.2.toNat.testBit j=true:=by
      simp only [Nat.testBit_xor,Nat.testBit_and] at hcn
      cases h1 : d.2.1.toNat.testBit j <;> cases h2 : d.2.2.toNat.testBit j <;> simp_all
    have hj : j < 768:=by
      by_contra hge
      have:=Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le d.2.2.isLt (Nat.pow_le_pow_right (by omega) (by omega:768 ≤ j)))
      rw [hq1.2] at this;cases this
    have hd0 : (d.2.1.toNat ^^^ d.2.2.toNat).testBit j=true:=by simp [Nat.testBit_xor,hq1.1,hq1.2]
    have hu_b:=hmust_u hj hd0
    rcases hdu with rfl | rfl
    · rw [← mg r s hd_faith] at hu_b
      simp only [Nat.testBit_xor,Nat.testBit_and,hq1.1,hq1.2] at hu_b;cases hu_b
    · rfl
lemma q2 {r s:Fin 768→ Row} {ty:List ff} {ql:List Sig}
    (hfa_all:List.Forall₂ (fun x y => y=x.1∨y=neg x.1) ty ql)
    (hfaith:∀ x ∈ ty,fj r s x)
    (hcov_all:(fk true (fi r s) ql).toNat=g9) :
    ∀ (p6 ds:List ff) (p7 fs:List Sig) (ky gb:List Sig) (kj:List ff) (cov:Nat),
      ty=p6 ++ ds→ ql=p7 ++ fs→ p6.length=p7.length →
      List.Forall₂ (fun d u => u=d.1∨u=neg d.1) kj gb →
      (∀ d ∈ kj,fj r s d) →
      (ky ++ gb ++ fs).Perm ql →
      (cov ||| (fk true (fi r s) (gb ++ fs)).toNat)=g9 →
      ∃ ky' gb' kj' cov',
        k9 (ss (ty.map fb)) (ds.map fb) (ky.map BitVec.toNat) cov
          (kj.map (fun d => (d.1.toNat,d.2.1.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat),d.2.2.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat)))) =
          some (ky'.map BitVec.toNat,cov',
            kj'.map (fun d => (d.1.toNat,d.2.1.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat),d.2.2.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat)))) ∧
        List.Forall₂ (fun d u => u=d.1∨u=neg d.1) kj' gb' ∧
        (∀ d ∈ kj',fj r s d) ∧
        (ky' ++ gb').Perm ql ∧
        (cov' ||| (fk true (fi r s) gb').toNat)=g9:=by
  intro p6 ds
  induction ds generalizing p6 with
  | nil =>
    intro p7 fs ky gb kj cov hD hF hlen hfr hff hperm hcov
    have hfs_nil : fs=[]:=by
      have hl:=hfa_all.length_eq;rw [hD,hF] at hl;simp at hl;exact List.eq_nil_of_length_eq_zero (by omega)
    subst hfs_nil;refine ⟨ky,gb,kj,cov,rfl,hfr,hff,by simpa using hperm,by simpa using hcov⟩
  | cons d rest ih =>
    intro p7 fs ky gb kj cov hD hF hlen hfr hff hperm hcov
    cases fs with
    | nil =>
      have hl:=hfa_all.length_eq;rw [hD,hF] at hl;simp at hl;omega
    | cons u fs' =>
      have hfa_sp : List.Forall₂ (fun x y => y=x.1∨y=neg x.1) (p6 ++ d :: rest) (p7 ++ u :: fs'):=by rwa [← hD,← hF]
      have hfaith_sp : ∀ x ∈ p6 ++ d :: rest,fj r s x:=by rwa [← hD]
      have hcov_sp : (fk true (fi r s) (p7 ++ u :: fs')).toNat=g9:=by rwa [← hF]
      have hd_f : fj r s d:=hfaith_sp d (by simp)
      obtain ⟨_,hdu,_⟩ := forall₂_split hfa_sp hlen
      simp only [List.map_cons,fb,k9]
      set uu:=ss (ty.map fb)
      set pq:=d.2.1.toNat &&& d.2.2.toNat
      set cp:=d.2.1.toNat ^^^ pq
      set cn:=d.2.2.toNat ^^^ pq
      have hfp : ((uu &&& cp) != 0)=true→ u=d.1:=by
        intro hne;obtain ⟨j,hju,hjc⟩ := n4 hne;exact (ls hfa_sp hlen hfaith_sp hcov_sp (by rwa [← hD])).1 hjc
      have hfn : ((uu &&& cn) != 0)=true→ u=neg d.1:=by
        intro hne;obtain ⟨j,hju,hjc⟩ := n4 hne;exact (ls hfa_sp hlen hfaith_sp hcov_sp (by rwa [← hD])).2 hjc
      have hD' : ty=(p6 ++ [d]) ++ rest:=by simpa [List.append_assoc] using hD
      have hF' : ql=(p7 ++ [u]) ++ fs' := by simpa [List.append_assoc] using hF
      have hlen' : (p6 ++ [d]).length=(p7 ++ [u]).length:=by simp [hlen]
      have hcov_split : (fk true (fi r s) (gb ++ u :: fs')).toNat =
          ((fq true (fi r s u)).toNat ||| (fk true (fi r s) (gb ++ fs')).toNat):=by
        rw [← BitVec.toNat_or];congr 1;apply BitVec.eq_of_getLsbD_eq;intro j hj
        let idx : Fin 768:=⟨j,hj⟩
        simp only [BitVec.getLsbD_or]
        have h1:=jz (oriented:=true) (sig:=fi r s) (ws:=gb ++ u :: fs') (i:=idx)
        have h2:=jz (oriented:=true) (sig:=fi r s) (ws:=gb ++ fs') (i:=idx)
        dsimp only [idx] at h1 h2
        cases hb : (fk true (fi r s) (gb ++ u :: fs')).getLsbD j
        · symm;apply Bool.or_eq_false_iff.mpr;constructor
          · cases hct : (fq true (fi r s u)).getLsbD j
            · rfl
            · have:=h1.mpr ⟨u,by simp,hct⟩;rw [hb] at this;cases this
          · cases hct : (fk true (fi r s) (gb ++ fs')).getLsbD j
            · rfl
            · obtain ⟨w,hw,hwb⟩ := h2.mp hct
              have hw' : w ∈ gb ++ u :: fs' := by rcases List.mem_append.mp hw with h | h <;> simp [h]
              have:=h1.mpr ⟨w,hw',hwb⟩;rw [hb] at this;cases this
        · obtain ⟨w,hw,hwb⟩ := h1.mp hb
          simp only [List.mem_append,List.mem_cons] at hw
          rcases hw with hwl | rfl | hwr
          · rw [h2.mpr ⟨w,List.mem_append_left _ hwl,hwb⟩];simp
          · simp [hwb]
          · rw [h2.mpr ⟨w,List.mem_append_right _ hwr,hwb⟩];simp
      by_cases hhp : ((uu &&& cp) != 0)=true
      · have hud:=hfp hhp;subst hud
        by_cases hhn : ((uu &&& cn) != 0)=true
        · exact False.elim (wz d.1 (hfn hhn))
        · simp only [hhp,Bool.eq_false_iff.mpr hhn,Bool.and_false,Bool.false_eq_true,ite_false,ite_true]
          have hperm' : ((d.1 :: ky) ++ gb ++ fs').Perm ql:=by
            rw [List.cons_append,List.cons_append];exact List.perm_middle.symm.trans hperm
          have hcov' : ((cov ||| cp) ||| (fk true (fi r s) (gb ++ fs')).toNat)=g9:=by
            rw [hcov_split,← mg r s hd_f] at hcov;simpa [cp,pq,Nat.or_assoc] using hcov
          simpa [List.map_cons] using ih (p6 ++ [d]) (p7 ++ [d.1]) fs' (d.1 :: ky) gb kj (cov ||| cp) hD' hF' hlen' hfr hff hperm' hcov'
      · by_cases hhn : ((uu &&& cn) != 0)=true
        · have hud:=hfn hhn;subst hud
          simp only [Bool.eq_false_iff.mpr hhp,hhn,Bool.false_and,Bool.false_eq_true,ite_false,ite_true]
          have hneg_nat : lr ^^^ d.1.toNat=(neg d.1).toNat:=by rw [neg,jf,lq]
          have hperm' : ((neg d.1 :: ky) ++ gb ++ fs').Perm ql:=by
            rw [List.cons_append,List.cons_append];exact List.perm_middle.symm.trans hperm
          have hcov' : ((cov ||| cn) ||| (fk true (fi r s) (gb ++ fs')).toNat)=g9:=by
            rw [hcov_split,← ph r s hd_f] at hcov;simpa [cn,pq,Nat.or_assoc] using hcov
          rw [hneg_nat];simpa [List.map_cons] using ih (p6 ++ [d]) (p7 ++ [neg d.1]) fs' (neg d.1 :: ky) gb kj (cov ||| cn) hD' hF' hlen' hfr hff hperm' hcov'
        · simp only [Bool.eq_false_iff.mpr hhp,Bool.eq_false_iff.mpr hhn,Bool.false_and,Bool.false_eq_true,ite_false]
          have hperm' : (ky ++ (u :: gb) ++ fs').Perm ql:=by
            refine List.Perm.trans ?_ hperm;simp only [List.append_assoc];exact List.Perm.append_left ky (List.perm_middle.symm)
          have hcov' : (cov ||| (fk true (fi r s) ((u :: gb) ++ fs')).toNat)=g9:=by
            have hce : fk true (fi r s) ((u :: gb) ++ fs')=fk true (fi r s) (gb ++ u :: fs'):=by
              apply BitVec.eq_of_getLsbD_eq;intro j hj;let idx : Fin 768:=⟨j,hj⟩;rw [Bool.eq_iff_iff,jz (i:=idx),jz (i:=idx)];constructor <;>
              · rintro ⟨w,hw,hwb⟩;refine ⟨w,?_,hwb⟩;simp only [List.mem_append,List.mem_cons] at hw ⊢;tauto
            rw [hce];exact hcov
          have hff' : ∀ x ∈ d :: kj,fj r s x:=fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact hd_f
            · exact hff x hx'
          simpa [List.map_cons,cp,cn,pq] using ih (p6 ++ [d]) (p7 ++ [u]) fs' ky (u :: gb) (d :: kj) cov hD' hF' hlen' (List.Forall₂.cons hdu hfr) hff' hperm' hcov'
def l5 (dpools:List DMP) (acc:List Nat) (cur:Nat) : List (Nat × Nat × Nat)→ Bool
  | [] => if cur != g9 then true else dpools.any (fun dp => l7 dp acc)
  | (s,cp,cn) :: rest =>
    l5 dpools (s :: acc) (cur ||| cp) rest &&
    l5 dpools ((lr ^^^ s) :: acc) (cur ||| cn) rest
lemma qz {r s:Fin 768→ Row} {dpools:List DMP}
    (kj:List ff) (gb:List Sig)
    (hfaith:∀ d ∈ kj,fj r s d)
    (hfa:List.Forall₂ (fun d u => u=d.1∨u=neg d.1) kj gb) :
    ∀ (ky:List Sig) (cur:Nat),
      l5 dpools (ky.map BitVec.toNat) cur
        (kj.map (fun d => (d.1.toNat,d.2.1.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat),d.2.2.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat))))=true →
      (cur ||| (fk true (fi r s) gb).toNat)=g9 →
      dpools.any (fun dp => l7 dp ((gb.reverse ++ ky).map BitVec.toNat))=true:=by
  induction hfa with
  | nil =>
    intro ky cur hok hcov
    have hcur : cur=g9:=by simpa [fk] using hcov
    simp only [List.map_nil,l5,hcur,bne_self_eq_false,Bool.false_eq_true,ite_false] at hok;simpa using hok
  | @cons d u ds fs hhd htl ih =>
    intro ky cur hok hcov
    have hd_f:=hfaith d List.mem_cons_self
    have htl_f : ∀ x ∈ ds,fj r s x:=fun x hx => hfaith x (List.mem_cons_of_mem _ hx)
    simp only [List.map_cons,l5,Bool.and_eq_true] at hok
    rcases hhd with rfl | rfl
    · have hcov' : ((cur ||| (d.2.1.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat))) ||| (fk true (fi r s) fs).toNat)=g9:=by
        rw [mg r s hd_f,Nat.or_assoc,← BitVec.toNat_or];exact hcov
      have res:=ih htl_f (d.1 :: ky) _ hok.1 hcov'
      simpa [List.reverse_cons,List.append_assoc] using res
    · have hneg_nat : lr ^^^ d.1.toNat=(neg d.1).toNat:=by rw [neg,jf,lq]
      have hcov' : ((cur ||| (d.2.2.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat))) ||| (fk true (fi r s) fs).toNat)=g9:=by
        rw [ph r s hd_f,Nat.or_assoc,← BitVec.toNat_or];exact hcov
      rw [hneg_nat] at hok
      have res:=ih htl_f (neg d.1 :: ky) _ hok.2 hcov'
      simpa [List.reverse_cons,List.append_assoc] using res
def qf (j2:List QPN) (cap i j aN bN zN:Nat) (un ka kb:Bool) (cdec:List n7) : Bool :=
  let c1all:=cdec.foldl (fun acc d => acc ||| (d.2.1 ^^^ (d.2.1 &&& d.2.2))) 0
  if c1all == g9 then false else
  match k9 (ss cdec) cdec [] 0 [] with
  | none => true
  | some (acc,cov,free) =>
    if free.length > 4 then false else
    let dpools:=j2.filterMap (zh (cap - 2) i j aN bN zN un ka kb)
    l5 dpools acc cov free
lemma zi {r s:Fin 768→ Row} (ds:List ff) (hfaith:∀ d ∈ ds,fj r s d) (init:Nat) :
    (ds.map fb).foldl (fun acc d => acc ||| (d.2.1 ^^^ (d.2.1 &&& d.2.2))) init =
    (init ||| (fk true (fi r s) (ds.map Prod.fst)).toNat):=by
  induction ds generalizing init with
  | nil => simp [fk]
  | cons d rest ih =>
    simp only [List.map_cons,List.foldl_cons,fb];rw [ih (fun x hx => hfaith x (List.mem_cons_of_mem _ hx))];rw [mg r s (hfaith d List.mem_cons_self),Nat.or_assoc,← BitVec.toNat_or];rfl
lemma su {raw T r s ws j2 cap tm i j op ka kb}
    (m5:k1 T r s) (p4:∀ w ∈ ws,fj r s w)
    (hi:i < ws.length) (hj:j < ws.length)
    (qpValid:∀ qp ∈ j2,∃ p,ValidPool raw T p∧pf p ws qp)
    (ndc:((fm op (ws.getD i f0) (ws.getD j f0) ::
      gd (op == 2) ka kb (ws.getD i f0) (ws.getD j f0) ws).map Prod.fst).Nodup)
    (t3:(fm op (ws.getD i f0) (ws.getD j f0) ::
      gd (op == 2) ka kb (ws.getD i f0) (ws.getD j f0) ws).length+1=cap)
    (hcap2:cap ≥ 2)
    (hdm:qf j2 cap i j (ws.getD i f0).1.toNat (ws.getD j f0).1.toNat
      (choiceVal (fx op (ws.getD i f0) (ws.getD j f0))).toNat (op == 2) ka kb
      ((fm op (ws.getD i f0) (ws.getD j f0) ::
        gd (op == 2) ka kb (ws.getD i f0) (ws.getD j f0) ws).map fb)=true) :
    ImpossibleT T (cap - 1) (ji tm cap (fm op (ws.getD i f0) (ws.getD j f0) ::
      gd (op == 2) ka kb (ws.getD i f0) (ws.getD j f0) ws).length (op == 2))
      ((fm op (ws.getD i f0) (ws.getD j f0) ::
        gd (op == 2) ka kb (ws.getD i f0) (ws.getD j f0) ws).map Prod.fst).toFinset:=by
  let a:=ws.getD i f0
  let b:=ws.getD j f0
  have ha : a ∈ ws:=by simp only [a,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi];exact List.getElem_mem hi
  have hb : b ∈ ws:=by simp only [b,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj];exact List.getElem_mem hj
  let z:=fm op a b
  let keptWs:=gd (op == 2) ka kb a b ws
  let cdec:=z :: keptWs
  change (cdec.map Prod.fst).Nodup at ndc
  have sub : keptWs.Sublist ws:=nm _ _ _ _ _ _
  have hcfaith : ∀ d ∈ cdec,fj r s d:=fun d hd => by
    rcases List.mem_cons.mp hd with rfl | hd'
    · exact np (p4 _ ha) (p4 _ hb) op
    · exact p4 _ (sub.subset hd')
  unfold qf at hdm;dsimp only at hdm;rw [zi cdec hcfaith 0,Nat.zero_or] at hdm
  by_cases hc1 : ((fk true (fi r s) (cdec.map Prod.fst)).toNat == g9)=true
  · rw [if_pos hc1] at hdm;cases hdm
  · rw [if_neg hc1] at hdm
    intro k t hk _ hlive
    have hlen_cdec : cdec.length+1=cap:=t3
    have hsz : (cdec.map Prod.fst).toFinset.card+t ≤ k+1:=(kp hlive).2
    rw [List.toFinset_card_of_nodup ndc] at hsz
    have hlenM : (cdec.map Prod.fst).length=cap - 1:=by rw [List.length_map];omega
    have htpos : t ≠ 0:=by
      intro ht0
      have sep:=rf hlive rfl (vy m5) true (fun _ => ht0)
      have heq : (fk true (fi r s) (cdec.map Prod.fst)).toNat=g9:=by
        rw [sep,gj]
      exact hc1 (beq_iff_eq.mpr heq)
    have hkt : k=cap - 1∧t=1:=by omega
    have hcardEq : (cdec.map Prod.fst).toFinset.card+t=k+1:=by rw [List.toFinset_card_of_nodup ndc];omega
    obtain ⟨fs,hfa_sig,hmr⟩ := vf hlive hcardEq (cdec.map Prod.fst) ndc rfl
    have hfa_dec : List.Forall₂ (fun d u => u=d.1∨u=neg d.1) cdec fs:=List.forall₂_map_left_iff.mp hfa_sig
    have hcov_all : (fk true (fi r s) fs).toNat=g9:=by rw [ve hmr m5,gj]
    obtain ⟨ky',gb',kj',cov',hsp,hfr',hff',hperm',hcov'⟩ :=
      q2 hfa_dec hcfaith hcov_all [] cdec [] fs [] [] [] 0 rfl rfl rfl
        List.Forall₂.nil (fun _ h => by cases h) (by simp) (by simpa using hcov_all)
    simp only [List.map_nil] at hsp;rw [hsp] at hdm;dsimp only at hdm
    by_cases hfl : (kj'.map (fun d => (d.1.toNat,d.2.1.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat),d.2.2.toNat ^^^ (d.2.1.toNat &&& d.2.2.toNat)))).length > 4
    · rw [if_pos hfl] at hdm;cases hdm
    · rw [if_neg hfl] at hdm
      have hcut:=qz kj' gb' hff' hfr' ky' cov' hdm hcov'
      obtain ⟨dp,hdp,hpc⟩ := List.any_eq_true.mp hcut
      obtain ⟨qp,hqp,hmk⟩ := List.mem_filterMap.mp hdp
      obtain ⟨p,hpv,hqv⟩ := qpValid qp hqp
      have hperm_fin : (gb'.reverse ++ ky').Perm fs :=
        ((List.reverse_perm gb').append_right ky').trans ((List.perm_append_comm).trans hperm')
      have hsubk : k - t=cap - 2:=by omega
      rw [hsubk] at hmr
      have hrun : kw (f7 T) (cap - 2) ((gb'.reverse ++ ky').map f7) :=
        (gk.perm (hperm_fin.symm.map f7) hmr).toRun
      have hnc_eq : (gb'.reverse ++ ky').countP (f5 p.domain) =
          cdec.countP (fun w => f5 p.domain w.1):=by
        rw [hperm_fin.countP_eq,ny hfa_dec]
      exact pl hpv hqv hi hj hrun (Nat.le_of_eq hnc_eq.symm) hmk hpc
def vh (z:Nat) (c:Nat × Nat × Nat) : Nat × Nat × Nat :=
  let (c1,u,u2):=c
  (z ||| c1,(z ^^^ (z &&& c1)) ||| (u ^^^ (u &&& z)),(z &&& u) ||| (u2 ^^^ (u2 &&& z)))
def nz (d:Bool) (ws:List n7) : Nat × Nat × Nat :=
  ws.foldr (fun w c => vh (if d then w.2.1 ^^^ (w.2.1 &&& w.2.2) else w.2.1 ^^^ w.2.2) c) (0,0,0)
lemma vi (d:Bool) (ws:List ff) :
    nz d (ws.map fb)=let c:=ft d ws;(c.1.toNat,c.2.1.toNat,c.2.2.toNat):=by
  induction ws with
  | nil => simp [nz,ft]
  | cons w rest ih =>
    simp only [nz,List.map_cons,List.foldr_cons] at ih ⊢
    rw [ih]
    have hcol : (if d then w.2.1.toNat ^^^ (w.2.1.toNat &&& w.2.2.toNat) else w.2.1.toNat ^^^ w.2.2.toNat)=(fq d w.2).toNat:=by
      cases d
      · simp only [fq,Bool.false_eq_true,ite_false,BitVec.toNat_xor]
      · simp only [fq,ite_true,g7]
    change vh (if d then w.2.1.toNat ^^^ (w.2.1.toNat &&& w.2.2.toNat) else w.2.1.toNat ^^^ w.2.2.toNat)
      ((ft d rest).1.toNat,(ft d rest).2.1.toNat,(ft d rest).2.2.toNat) =
      let c:=kn (fq d w.2) (ft d rest);(c.1.toNat,c.2.1.toNat,c.2.2.toNat)
    rw [hcol];simp only [vh,kn,BitVec.toNat_or];rw [g7,g7,g7,BitVec.toNat_and]
def qg (n:Nat) : Nat :=
  let m:=n % 2305843009213693951
  (m*(m+971)) % 2305843009213693951
def gf {α : Type} (un ka kb:Bool) (i j:Nat) (ws:List α) : List α :=
  let rec go (t:Nat) : List α → List α
    | [] => []
    | w :: rest => if (t == i && !ka)||(!un&&t == j && !kb) then go (t+1) rest else w :: go (t+1) rest
  go 0 ws
lemma po {α β} (f : α → β) (un ka kb:Bool) (i j:Nat) (ws:List α) :
    gf un ka kb i j (ws.map f)=(gf un ka kb i j ws).map f:=by
  unfold gf
  suffices ∀ (t:Nat) (xs:List α),gf.go un ka kb i j t (xs.map f)=(gf.go un ka kb i j t xs).map f from this 0 ws
  intro t xs;induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,gf.go];split <;> simp [ih]
lemma n5 {α} [BEq α] [LawfulBEq α] : ∀ {xs:List α},xs.Nodup→ ∀ a : α,xs.erase a=xs.filter (· != a)
  | [],_,_ => rfl
  | x :: xs,hnd,a => by
    have ⟨hxa,hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.erase_cons,List.filter_cons]
    by_cases h : x == a
    · have heq : x=a:=beq_iff_eq.mp h;subst heq
      simp only [h,bne_self_eq_false,ite_true,Bool.false_eq_true,ite_false];exact (List.filter_eq_self.mpr (fun y hy => by simp only [bne_iff_ne];intro e;exact hxa (e ▸ hy))).symm
    · have hne : x ≠ a:=fun e => h (beq_iff_eq.mpr e)
      simp only [h,Bool.false_eq_true,ite_false,bne_iff_ne.mpr hne,ite_true,n5 hnd' a]
lemma r1 {un ka kb} {a b:ff} {ws:List ff} (hnd:ws.Nodup) :
    gd un ka kb a b ws=ws.filter (fun w => (ka||w != a)&&(un||kb||w != b)):=by
  have hdel (xs:List ff) (hn:xs.Nodup) (c:ff) (k:Bool) :
      j1 xs c k=xs.filter (fun w => k||w != c):=by
    cases k
    · simp only [j1,Bool.false_eq_true,ite_false,Bool.false_or];exact n5 hn c
    · simp only [j1,ite_true,Bool.true_or];exact (List.filter_eq_self.mpr (fun _ _ => rfl)).symm
  unfold gd
  cases un
  · simp only [Bool.false_eq_true,ite_false,Bool.false_or,px]
    rw [hdel _ (hnd.sublist (ko ws a ka)),hdel ws hnd,List.filter_filter];congr 1;funext w;exact Bool.and_comm _ _
  · simp only [ite_true,Bool.true_or,Bool.and_true];exact hdel ws hnd a ka
lemma lg {un ka kb i j} {ws:List ff}
    (hi:i < ws.length) (hj:j < ws.length) (nd:(ws.map Prod.fst).Nodup) :
    gf un ka kb i j ws=gd un ka kb (ws.getD i f0) (ws.getD j f0) ws:=by
  have hinj : ∀ t1 t2,t1 < ws.length→ t2 < ws.length→ (ws.getD t1 f0).1=(ws.getD t2 f0).1→ t1=t2:=by
    intro t1 t2 h1 h2 heq
    have hnd:=(List.nodup_iff_injective_getElem (l:=ws.map Prod.fst)).mp nd
    have he2 : (ws.map Prod.fst)[t1]'(by simpa using h1)=(ws.map Prod.fst)[t2]'(by simpa using h2):=by
      simp only [List.getElem_map];simpa [List.getD_eq_getElem?_getD,h1,h2] using heq
    exact Fin.mk.inj (hnd (a₁ := ⟨t1,by simpa using h1⟩) (a₂ := ⟨t2,by simpa using h2⟩) he2)
  rw [r1 (List.Nodup.of_map Prod.fst nd)];unfold gf
  suffices ∀ (k:Nat) (xs:List ff),
      (∀ t (ht:t < xs.length),xs[t]=ws.getD (k+t) f0)→ k+xs.length ≤ ws.length →
      gf.go un ka kb i j k xs=xs.filter (fun w => (ka||w != ws.getD i f0)&&(un||kb||w != ws.getD j f0)) by
    exact this 0 ws (fun t ht => by simp [List.getD_eq_getElem?_getD,ht]) (by simp)
  intro k xs
  induction xs generalizing k with
  | nil => intro _ _;rfl
  | cons x rest ih =>
    intro hget hle
    have hx : x=ws.getD k f0:=by rw [← Nat.add_zero k];exact hget 0 (by simp)
    have hki : (k == i)=(x == ws.getD i f0):=by
      rw [Bool.eq_iff_iff,beq_iff_eq,beq_iff_eq];constructor
      · intro h;subst h;rw [hx]
      · intro h;exact hinj k i (by simp at hle;omega) hi (hx ▸ congrArg Prod.fst h)
    have hkj : (k == j)=(x == ws.getD j f0):=by
      rw [Bool.eq_iff_iff,beq_iff_eq,beq_iff_eq];constructor
      · intro h;subst h;rw [hx]
      · intro h;exact hinj k j (by simp at hle;omega) hj (hx ▸ congrArg Prod.fst h)
    have hcond : (!((k == i && !ka)||(!un&&k == j && !kb))) =
        ((ka||x != ws.getD i f0)&&(un||kb||x != ws.getD j f0)):=by
      simp only [bne,← hki,← hkj]
      generalize (k == i)=bi;generalize (k == j)=bj
      cases ka <;> cases kb <;> cases un <;> cases bi <;> cases bj <;> rfl
    have hrest_get : ∀ (t:Nat) (ht:t < rest.length),rest[t]=ws.getD (k+1+t) f0:=by
      intro t ht;have h1:=hget (t+1) (by simpa using ht);simpa [Nat.add_assoc,Nat.add_comm 1] using h1
    have hih:=ih (k+1) hrest_get (by simp at hle;omega)
    simp only [gf.go,List.filter_cons,← hcond]
    generalize ((k == i && !ka)||(!un&&k == j && !kb))=b
    cases b <;> simp [hih]
def pi (raw:List ff) (f9:Nat→ PT) (slot i:Nat) : Nat × List ff × List ff :=
  let (_,g5,_,_,data):=f9 slot
  let ow:=opW raw.length g5
  let len:=ow*g5
  let h9:=len+raw.length+g5
  let recp:=j8 data (i*h9) h9
  let ops:=recp &&& ((1 <<< len) - 1)
  let f8:=jg ow g5 ops raw
  (ops,f8,gp (recp >>> len) f8)
def stateSetG (g:Forest) (f9:Nat→ PT) (slot i:Nat) (base:List Sig) : List Sig :=
  let (_,g5,_,_,data):=f9 slot
  let nraw:=(vars g.mask).length
  let ow:=opW nraw g5
  let len:=ow*g5
  let h9:=len+nraw+g5
  let recp:=j8 data (i*h9) h9
  let ops:=recp &&& ((1 <<< len) - 1)
  gp (recp >>> len) (jh ow g5 ops base)
def r2 (f9:Nat→ PT) (slot i:Nat) (base:List Nat) : List Nat :=
  let (_,g5,_,_,data):=f9 slot
  let nraw:=base.length
  let ow:=opW nraw g5
  let len:=ow*g5
  let h9:=len+nraw+g5
  let recp:=j8 data (i*h9) h9
  let ops:=recp &&& ((1 <<< len) - 1)
  gp (recp >>> len) (m2 ow g5 ops base)
lemma vj (g:Forest) (f9:Nat→ PT) (slot i:Nat) :
    stateSetG g f9 slot i (vars g.mask)=(pi (j4 g) f9 slot i).2.2.map Prod.fst:=by
  unfold stateSetG pi;rcases f9 slot with ⟨num,g5,cw,offw,data⟩;dsimp only;rw [← w2 g,← nu g,te,k3]
lemma pm (g:Forest) (f9:Nat→ PT) (slot i:Nat) (ms:List Move) :
    stateSetG g f9 slot i ((vars g.mask).map (movedWord ms)) =
      (stateSetG g f9 slot i (vars g.mask)).map (movedWord ms):=by
  unfold stateSetG;rcases f9 slot with ⟨num,g5,cw,offw,data⟩;dsimp only;rw [ns,k3]
lemma vk (g:Forest) (f9:Nat→ PT) (slot i:Nat) (base:List Sig) (hl:base.length=(vars g.mask).length) :
    r2 f9 slot i (base.map BitVec.toNat)=(stateSetG g f9 slot i base).map BitVec.toNat:=by
  unfold r2 stateSetG;rcases f9 slot with ⟨num,g5,cw,offw,data⟩;dsimp only;rw [List.length_map,hl,sm,k3]
def mh (f9:Nat→ PT) (k:Nat) : Nat→ Nat→ Nat→ Option (Nat × Nat)
  | 0,_,_ => none
  | f+1,ct,i =>
    let n:=(f9 (4*k+ct)).1
    if i < n then some (ct,i) else mh f9 k f (ct+1) (i - n)
lemma sv {f9 k f ct i ct' j} (h:mh f9 k f ct i=some (ct',j)) :
    ct ≤ ct' ∧ ct' < ct+f∧j < (f9 (4*k+ct')).1:=by
  induction f generalizing ct i with
  | zero => simp [mh] at h
  | succ f ih =>
    unfold mh at h;dsimp only at h;split at h
    next hlt => injection h with h1;injection h1 with hc hj;subst hc;subst hj;exact ⟨Nat.le_refl _,by omega,hlt⟩
    next => obtain ⟨h1,h2,h3⟩ := ih h;exact ⟨by omega,by omega,h3⟩
def lu (f9:Nat→ PT) (fh:Nat→ Option (List Nat)) (k ct:Nat) (pair:Nat × Nat) : Option (List Nat) :=
  (mh f9 k (4 - ct) ct pair.1).bind fun (ct',j) =>
    (fh pair.2).map (r2 f9 (4*k+ct') j)
lemma r3 (g:Forest) (f9:Nat→ PT) (fh:Nat→ Option (List Nat)) (k ct:Nat)
    (tw:∀ x ∈ g.autos.toList,autoOK (graphGoal g.mask) (x.map swapRows)=true)
    (hrot:∀ p,fh p=(g.autos[p]?).map (fun perm => ((vars g.mask).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat))
    (earlier:∀ ct' ≤ 3,∀ j < (f9 (4*k+ct')).1,ImpossibleT (graphGoal g.mask) k ct' (stateSetG g f9 (4*k+ct') j (vars g.mask)).toFinset)
    {pair outN} (h:lu f9 fh k ct pair=some outN) :
    ∃ out : List Sig,outN=out.map BitVec.toNat∧ImpossibleT (graphGoal g.mask) k ct out.toFinset:=by
  unfold lu at h
  cases hf : mh f9 k (4 - ct) ct pair.1 with
  | none => simp [hf] at h
  | some cj =>
    rcases cj with ⟨ct',j⟩
    simp only [hf,Option.bind_some] at h
    obtain ⟨hle,hlt,hj⟩ := sv hf
    rw [hrot] at h
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      let base:=(vars g.mask).map (movedWord (perm.map swapRows).reverse)
      refine ⟨stateSetG g f9 (4*k+ct') j base,?_,?_⟩
      · rw [← h,vk g f9 (4*k+ct') j base (by simp [base])]
      · rw [show base=(vars g.mask).map (movedWord (perm.map swapRows).reverse) from rfl,pm]
        exact impT_mono hle (rotate_excludedT (earlier ct' (by omega) j hj) _ (tw _ (by simpa using Array.mem_of_getElem? e)))
abbrev xc:=Nat→ Nat→ List (List Nat)
abbrev g4:=Nat × Nat × Nat × List n7 × List Nat × (Nat × Nat × Nat) × (Nat × Nat × Nat) × List QPN × xc × List Nat × Nat
def q3 (g:Forest) (raw:List n7) (rawS:List Nat) (f9:Nat→ PT)
    (idx:Nat→ Nat→ Nat→ Option (Nat × Nat)) (fh:Nat→ Option (List Nat)) (k tm i:Nat) : g4 :=
  let slot:=4*k+tm
  let (num,g5,cw,offw,data):=f9 slot
  let ow:=opW raw.length g5
  let len:=ow*g5
  let h9:=len+raw.length+g5
  let recp:=j8 data (i*h9) h9
  let ops:=recp &&& ((1 <<< len) - 1)
  let f8:=m1 ow g5 ops raw
  let ws:=gp (recp >>> len) f8
  let wsN:=ws.map Prod.fst
  let bankN:=f8.map Prod.fst
  let start:=num*h9
  let c0:=j8 data (start+i*offw) offw
  let c1:=j8 data (start+(i+1)*offw) offw
  let nr:=c1 - c0
  let st:=start+(num+1)*offw+c0*(cw+g5)
  let j2:=(sq data cw g5 nr st).filterMap (fun (a,b) => m3 g rawS wsN (k - 1) ow ops g5 bankN a b)
  let lfn:=fun ct tag => ((idx slot ct tag).bind (lu f9 fh (k - 1) ct)).toList
  let mn:=wsN.map qg
  (k,tm,ws.length,ws,wsN,nz false ws,nz true ws,j2,lfn,mn,mn.foldl (· + ·) 0)
def fbN (c:g4) (i j op:Nat) (ka kb:Bool) : Bool :=
  let (cap,tm,n,ws,wsN,_,_,j2,lfn,mn,qk):=c
  let a:=wsN.getD i 0
  let b:=wsN.getD j 0
  let un:=op == 2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  let ct:=ji tm cap len un
  let z1:=opN op a b
  if z1 == 0||z1 == lr||wsN.any (fun v => v == z1) then true else
  if j2.any (fun qp => pg qp (cap - 1) i j z1 un ka kb) then true else
  if len+1 == cap&&ct == 1&&cap ≥ 2 &&
      qf j2 cap i j a b z1 un ka kb (jt op (ws.getD i (0,0,0)) (ws.getD j (0,0,0)) :: gf un ka kb i j ws) then true else
  let rest:=gf un ka kb i j wsN
  let tag:=qk - (if ka then 0 else mn.getD i 0) - (if un||kb then 0 else mn.getD j 0)+qg z1
  (lfn ct tag).any (q1 (z1 :: rest))
def jp (c:g4) (i j op:Nat) (ka kb:Bool) : Bool :=
  let (cap,tm,n,ws,_,u,v,_,_,_,_):=c
  let un:=op == 2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len > cap then true else
    let d:=ji tm cap len un == 0
    let a:=ws.getD i (0,0,0)
    let b:=ws.getD j (0,0,0)
    let z:=jt op a b
    let col:=fun (w:n7) => if d then w.2.1 ^^^ (w.2.1 &&& w.2.2) else w.2.1 ^^^ w.2.2
    let cv:=if d then v else u
    if (gn cv (col a) (col b) un ka kb ||| col z) != g9 then true else
    fbN c i j op ka kb
lemma ps (c:wv) (a b:Bits) (un ka kb:Bool) :
    (m0 c a b un ka kb).toNat=gn (c.1.toNat,c.2.1.toNat,c.2.2.toNat) a.toNat b.toNat un ka kb:=by
  cases un <;> cases ka <;> cases kb <;>
    simp only [m0,gn,ku,mv,ite_true,ite_false,Bool.false_eq_true] <;>
    try (rw [g7];simp only [BitVec.toNat_and,BitVec.toNat_or])
lemma n6 {raw T r s} {ws:List ff} {j2:List QPN} {lfn:xc} {mn qk cap tm i j op ka kb}
    (m5:k1 T r s) (p4:∀ w ∈ ws,fj r s w)
    (nd:(ws.map Prod.fst).Nodup) (hi:i < ws.length) (hj:j < ws.length)
    (ne:(op == 2)=false→ i ≠ j) (hcap:0 < cap)
    (qpv:∀ qp ∈ j2,∃ p,ValidPool raw T p∧pf p ws qp)
    (lv:∀ ct tag xsN,xsN ∈ lfn ct tag→ ∃ xs : List Sig,xsN=xs.map BitVec.toNat∧ImpossibleT T (cap - 1) ct xs.toFinset)
    (pro:proper (fm op (ws.getD i f0) (ws.getD j f0)).1)
    (gi:(fm op (ws.getD i f0) (ws.getD j f0)).1 ∉ ws.map Prod.fst)
    (test:jp (cap,tm,ws.length,ws.map fb,ws.map (fun w => w.1.toNat),
      nz false (ws.map fb),nz true (ws.map fb),j2,lfn,mn,qk) i j op ka kb=true) :
    ImpossibleT T (cap - 1) (ji tm cap (h7 ws op (ws.getD i f0) (ws.getD j f0) ka kb).length (op == 2))
      (h7 ws op (ws.getD i f0) (ws.getD j f0) ka kb).toFinset:=by
  let a:=ws.getD i f0
  let b:=ws.getD j f0
  have ha : a ∈ ws:=by simp only [a,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi];exact List.getElem_mem hi
  have hb : b ∈ ws:=by simp only [b,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj];exact List.getElem_mem hj
  have hab_ne : (op == 2)=false→ a ≠ b:=fun hun heq => by
    have hnd:=(List.nodup_iff_injective_getElem (l:=ws.map Prod.fst)).mp nd
    have he2 : (ws.map Prod.fst)[i]'(by simpa using hi)=(ws.map Prod.fst)[j]'(by simpa using hj):=by
      simp only [List.getElem_map];simpa [a,b,List.getD_eq_getElem?_getD,hi,hj] using congrArg Prod.fst heq
    exact ne hun (Fin.mk.inj (hnd (a₁ := ⟨i,by simpa using hi⟩) (a₂ := ⟨j,by simpa using hj⟩) he2))
  let z:=fm op a b
  let rest:=gd (op == 2) ka kb a b ws
  let child:=z.1 :: rest.map Prod.fst
  change proper z.1 at pro;change z.1 ∉ ws.map Prod.fst at gi
  have sub : rest.Sublist ws:=nm _ _ _ _ _ _
  have ndc : child.Nodup:=List.nodup_cons.mpr ⟨fun hm => gi ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
  have val:=sf op a b
  have leq : 1+(ws.length - (if ka then 0 else 1) - (if (op == 2)||kb then 0 else 1))=child.length:=by
    change _=(z.1 :: rest.map Prod.fst).length;rw [List.length_cons,List.length_map,zb _ _ _ _ _ _ ha hb hab_ne,Nat.add_comm 1]
  have hgetD (t:Nat) : (ws.map fb).getD t (0,0,0)=fb (ws.getD t f0):=by
    rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map];cases ws[t]? <;> simp [f0,fb,zero]
  have hgetN (t:Nat) : (ws.map (fun w => w.1.toNat)).getD t 0=(ws.getD t f0).1.toNat:=by
    rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map];cases ws[t]? <;> simp [f0,zero]
  intro k t hk ht h;change ji tm cap child.length (op == 2) < 3→ t ≤ ji tm cap child.length (op == 2) at ht;change Live T k t child.toFinset at h
  have hsz:=(kp h).2
  change child.toFinset.card+t ≤ k+1 at hsz;rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap:=by omega
  unfold jp at test;change (if 1+(ws.length - _ - _) > cap then true else _)=true at test;rw [leq,if_neg (by omega)] at test
  set ct:=ji tm cap child.length (op == 2)
  have ht0 : (ct == 0)=true→ t=0:=fun hct => by
    have hc0 : ct=0:=beq_iff_eq.mp hct;have ht' := ht;rw [hc0] at ht';have:=ht' (by decide);omega
  have sep:=rf h rfl (vy m5) (ct == 0) ht0
  let d:=ct == 0
  have g : (ft d rest).1=fk d (fi r s) (rest.map Prod.fst) :=
    za _ _ (fun v hv => p4 _ (sub.subset hv))
  have rz:=tb ha hb (op == 2) ka kb d hab_ne
  have hf:=np (p4 _ ha) (p4 _ hb) op
  change fq d (fi r s z.1) ||| fk d (fi r s) (rest.map Prod.fst)=_ at sep;change z.2=fi r s z.1 at hf;rw [← hf,← g,rz,BitVec.or_comm] at sep
  have hcol_eq (w:ff) : (if d then (fb w).2.1 ^^^ ((fb w).2.1 &&& (fb w).2.2) else (fb w).2.1 ^^^ (fb w).2.2)=(fq d w.2).toNat:=by
    cases d
    · simp only [fq,fb,Bool.false_eq_true,ite_false,BitVec.toNat_xor]
    · simp only [fq,fb,ite_true,g7]
  have hcv_eq : (if d then nz true (ws.map fb) else nz false (ws.map fb)) =
      let cv:=pz (py ws) d;(cv.1.toNat,cv.2.1.toNat,cv.2.2.toNat):=by
    cases d <;> simp [vi,pz,py]
  have htake_eq : gn (let cv:=pz (py ws) d;(cv.1.toNat,cv.2.1.toNat,cv.2.2.toNat)) (fq d a.2).toNat (fq d b.2).toNat (op == 2) ka kb =
      (m0 (pz (py ws) d) (fq d a.2) (fq d b.2) (op == 2) ka kb).toNat :=
    (ps (pz (py ws) d) (fq d a.2) (fq d b.2) (op == 2) ka kb).symm
  have hcomb_eq : (gn (if d then nz true (ws.map fb) else nz false (ws.map fb))
      (if d then ((ws.map fb).getD i (0,0,0)).2.1 ^^^ (((ws.map fb).getD i (0,0,0)).2.1 &&& ((ws.map fb).getD i (0,0,0)).2.2)
       else ((ws.map fb).getD i (0,0,0)).2.1 ^^^ ((ws.map fb).getD i (0,0,0)).2.2)
      (if d then ((ws.map fb).getD j (0,0,0)).2.1 ^^^ (((ws.map fb).getD j (0,0,0)).2.1 &&& ((ws.map fb).getD j (0,0,0)).2.2)
       else ((ws.map fb).getD j (0,0,0)).2.1 ^^^ ((ws.map fb).getD j (0,0,0)).2.2) (op == 2) ka kb |||
      (if d then (jt op ((ws.map fb).getD i (0,0,0)) ((ws.map fb).getD j (0,0,0))).2.1 ^^^ ((jt op ((ws.map fb).getD i (0,0,0)) ((ws.map fb).getD j (0,0,0))).2.1 &&& (jt op ((ws.map fb).getD i (0,0,0)) ((ws.map fb).getD j (0,0,0))).2.2)
       else (jt op ((ws.map fb).getD i (0,0,0)) ((ws.map fb).getD j (0,0,0))).2.1 ^^^ (jt op ((ws.map fb).getD i (0,0,0)) ((ws.map fb).getD j (0,0,0))).2.2))=g9:=by
    have hz_def : ga op (ws.getD i f0) (ws.getD j f0)=z:=rfl
    rw [hgetD i,hgetD j,qv,hz_def,hcol_eq a,hcol_eq b,hcol_eq z,hcv_eq,htake_eq,← BitVec.toNat_or,sep,gj]
  change (if _ != g9 then true else fbN _ i j op ka kb)=true at test;rw [hcomb_eq,bne_self_eq_false] at test;simp only [Bool.false_eq_true,ite_false] at test;unfold fbN at test;dsimp only at test;rw [hgetN i,hgetN j,xv op a b,leq] at test
  have hz_ne0 : (z.1.toNat == 0)=false:=by
    simp only [beq_eq_false_iff_ne];intro heq;exact pro.1 (BitVec.eq_of_toNat_eq (by simpa [zero] using heq))
  have hz_ne1 : (z.1.toNat == lr)=false:=by
    simp only [beq_eq_false_iff_ne];intro heq;exact pro.2 (BitVec.eq_of_toNat_eq (heq.trans lq))
  have hfr : (ws.map (fun w => w.1.toNat)).any (fun v => v == z.1.toNat)=false:=by
    apply Bool.eq_false_iff.mpr;intro hh
    obtain ⟨v,hv,hve⟩ := List.any_eq_true.mp hh
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    exact gi ((BitVec.eq_of_toNat_eq (beq_iff_eq.mp hve)).symm ▸ List.mem_map_of_mem hx)
  rw [hz_ne0,hz_ne1,hfr] at test;simp only [Bool.false_or,Bool.false_eq_true,ite_false] at test
  have nd' : (choiceVal (fx op a b) :: rest.map Prod.fst).Nodup:=val ▸ ndc
  have h' : Live T k t (choiceVal (fx op a b) :: rest.map Prod.fst).toFinset:=val ▸ h
  by_cases hq : j2.any (fun qp => pg qp (cap - 1) i j z.1.toNat (op == 2) ka kb)=true
  · obtain ⟨qp,hqp,hfc⟩ := List.any_eq_true.mp hq
    obtain ⟨p,hpv,hqv⟩ := qpv qp hqp
    exact scalarPoolCut_sound hpv nd' (rr hqv hi hj nd ne (val ▸ hfc)) k t hk h'
  · rw [if_neg hq] at test
    by_cases hdm_c : ((child.length+1 == cap)&&(ct == 1)&&decide (cap ≥ 2) &&
        qf j2 cap i j a.1.toNat b.1.toNat z.1.toNat (op == 2) ka kb
          (jt op ((ws.map fb).getD i (0,0,0)) ((ws.map fb).getD j (0,0,0)) :: gf (op == 2) ka kb i j (ws.map fb)))=true
    · simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at hdm_c
      have hdm_arg : jt op ((ws.map fb).getD i (0,0,0)) ((ws.map fb).getD j (0,0,0)) :: gf (op == 2) ka kb i j (ws.map fb) =
          (z :: rest).map fb:=by
        rw [hgetD i,hgetD j,qv,po,lg hi hj nd];rfl
      have hdm_ok:=hdm_c.2
      rw [hdm_arg,val] at hdm_ok
      have hlen_cdec : (z :: rest).length+1=cap:=by simpa [child] using hdm_c.1.1.1
      have hdm_imp:=su (tm:=tm) m5 p4 hi hj qpv ndc hlen_cdec hdm_c.1.2 hdm_ok
      have hcl : child.length=(z :: rest).length:=by simp [child]
      exact hdm_imp k t hk (by rw [← hcl];exact ht) h
    · rw [if_neg hdm_c] at test
      obtain ⟨xsN,hxsN,hsw⟩ := List.any_eq_true.mp test
      obtain ⟨xs,rfl,hxs_imp⟩ := lv ct _ xsN hxsN
      have hrest_n : gf (op == 2) ka kb i j (ws.map (fun w => w.1.toNat))=(rest.map Prod.fst).map BitVec.toNat:=by
        rw [po,lg hi hj nd];simp [rest,a,b,List.map_map,Function.comp_def]
      rw [hrest_n] at hsw
      have heqS : child.toFinset=xs.toFinset:=tg ndc (by simpa [child] using hsw)
      have hlive_c : Live T k t child.toFinset:=h
      rw [heqS] at hlive_c;exact hxs_imp k t hk ht hlive_c
def jc (c:g4) (i j op:Nat) : Bool :=
  let f:=jp c i j op
  f false false&&f true false&&f false true&&f true true
def w6 (c:g4) (i:Nat) (js:List Nat) : Bool :=
  let unOk:=if c.2.1 == 0 then true else jp c i i 2 false false&&jp c i i 2 true true
  unOk&&js.all (fun j => jc c i j 0&&jc c i j 1)
def ki (c:g4) : List Nat→ Bool
  | [] => true
  | i :: js => w6 c i js&&ki c js
lemma x0 {c js i} (h:ki c js=true) (ht:c.2.1 > 0) (hi:i ∈ js) (keep:Bool) :
    jp c i i 2 keep keep=true:=by
  induction js with
  | nil => simp at hi
  | cons x tail ih =>
    simp only [ki,Bool.and_eq_true] at h
    rcases List.mem_cons.mp hi with rfl | mt
    · have hu:=(Bool.and_eq_true _ _).mp h.1 |>.1
      have hne : (c.2.1 == 0)=false:=beq_eq_false_iff_ne.mpr (by omega)
      simp only [hne,Bool.false_eq_true,ite_false,Bool.and_eq_true] at hu
      cases keep;exact hu.1;exact hu.2
    · exact ih h.2 mt
lemma w7 {c js i j} (h:ki c js=true) (hi:i ∈ js) (hj:j ∈ js) (ne:i ≠ j) (d:Bool) :
    jc c i j (if d then 1 else 0)=true∨jc c j i (if d then 1 else 0)=true:=by
  induction js with
  | nil => simp at hi
  | cons x tail ih =>
    simp only [ki,Bool.and_eq_true] at h
    have row:=(Bool.and_eq_true _ _).mp h.1 |>.2
    rcases List.mem_cons.mp hi with rfl | mi <;> rcases List.mem_cons.mp hj with rfl | mj
    · exact False.elim (ne rfl)
    · left;have p:=List.all_eq_true.mp row j mj;cases d <;> simp_all
    · right;have p:=List.all_eq_true.mp row i mi;cases d <;> simp_all
    · exact ih h.2 mi mj
lemma vl {c i j op} (h:jc c i j op=true) (ka kb:Bool) :
    jp c i j op ka kb=true:=by
  simp only [jc,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
lemma w8 {raw T r s ws j2 lfn mn qk cap tm}
    (m5:k1 T r s) (p4:∀ w ∈ ws,fj r s w)
    (nd:(ws.map Prod.fst).Nodup) (out:T ∉ ws.map Prod.fst)
    (qpv:∀ qp ∈ j2,∃ p,ValidPool raw T p∧pf p ws qp)
    (lv:∀ ct tag xsN,xsN ∈ lfn ct tag→ ∃ xs : List Sig,xsN=xs.map BitVec.toNat∧ImpossibleT T (cap - 1) ct xs.toFinset)
    (vr:cap=0∨ki (cap,tm,ws.length,ws.map fb,ws.map (fun w => w.1.toNat),
      nz false (ws.map fb),nz true (ws.map fb),j2,lfn,mn,qk) (List.range ws.length)=true) :
    ImpossibleT T cap tm (ws.map Prod.fst).toFinset:=by
  rcases vr with rfl | vr
  · intro k t hk _ h
    have hk0 : k=0:=by omega
    subst hk0
    generalize he : (ws.map Prod.fst).toFinset=S at h;rw [h.zeroSet] at he
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  by_cases hc : cap=0
  · subst hc;intro k t hk _ h
    have hk0 : k=0:=by omega
    subst hk0
    generalize he : (ws.map Prod.fst).toFinset=S at h;rw [h.zeroSet] at he
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0 < cap:=by omega
  apply wy nd out
  · intro htpos v hv keep gi pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    obtain ⟨i,hi,hae⟩ := List.getElem_of_mem ha
    have hget : ws.getD i f0=a:=by simp [List.getD_eq_getElem?_getD,hi,hae]
    have hf:=w1 nd ha keep
    have hev:=n6 (op:=2) m5 p4 nd hi hi (by simp) hc' qpv lv
      (hget.symm ▸ pro) (hget.symm ▸ gi) (x0 vr htpos (List.mem_range.mpr hi) keep)
    rw [hget] at hev
    have t3 : (h7 ws 2 a a keep keep).length=(gg (ws.map Prod.fst) a.1 keep).length:=by
      have nd1 : (h7 ws 2 a a keep keep).Nodup:=by
        unfold h7;have sub:=nm ws a a true keep keep;exact List.nodup_cons.mpr ⟨fun hm => gi ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
      have nd2 : (gg (ws.map Prod.fst) a.1 keep).Nodup:=by
        unfold gg;have na : a.1 ∉ (ws.map Prod.fst).erase a.1:=nd.not_mem_erase;refine List.nodup_cons.mpr ⟨fun hm => ?_,k7 keep a.1 _ (nd.erase _) na⟩;rw [kh] at hm;rcases hm with ⟨heq,_⟩ | hm
        · exact gi (heq.symm ▸ List.mem_map_of_mem ha)
        · exact gi (List.mem_of_mem_erase hm)
      rw [← List.toFinset_card_of_nodup nd1,← List.toFinset_card_of_nodup nd2,hf]
    rw [hf,t3] at hev;exact hev
  · intro a ha b hb d ka kb ne gi pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    obtain ⟨i,hi,hae⟩ := List.getElem_of_mem haW
    obtain ⟨j,hj,hbe⟩ := List.getElem_of_mem hbW
    have hgetI : ws.getD i f0=a:=by simp [List.getD_eq_getElem?_getD,hi,hae]
    have hgetJ : ws.getD j f0=b:=by simp [List.getD_eq_getElem?_getD,hj,hbe]
    have hij : i ≠ j:=fun e => ne (by rw [← hgetI,← hgetJ,e])
    have one (i' j':Nat) (hi':i' < ws.length) (hj':j' < ws.length) (hij':i' ≠ j') (ka kb:Bool)
        (a' b':ff) (hga:ws.getD i' f0=a') (hgb:ws.getD j' f0=b')
        (aa:a' ∈ ws) (bb:b' ∈ ws) (ne':a'.1 ≠ b'.1)
        (pr:proper (bin d a'.1 b'.1)) (fr:bin d a'.1 b'.1 ∉ ws.map Prod.fst)
        (test:jc (cap,tm,ws.length,ws.map fb,ws.map (fun w => w.1.toNat),
          nz false (ws.map fb),nz true (ws.map fb),j2,lfn,mn,qk) i' j' (if d then 1 else 0)=true) :
        ImpossibleT T (cap - 1) (ji tm cap (fw (ws.map Prod.fst) a'.1 b'.1 d ka kb).length false)
          (fw (ws.map Prod.fst) a'.1 b'.1 d ka kb).toFinset:=by
      have hf:=v9 nd aa bb ne' d ka kb
      have eq : (fm (if d then 1 else 0) a' b').1=bin d a'.1 b'.1:=by cases d <;> rfl
      have hev:=n6 (op:=if d then 1 else 0) m5 p4 nd hi' hj' (fun _ => hij') hc' qpv lv
        (hga.symm ▸ hgb.symm ▸ eq ▸ pr) (hga.symm ▸ hgb.symm ▸ eq ▸ fr) (vl test ka kb)
      rw [hga,hgb] at hev
      have t3 : (h7 ws (if d then 1 else 0) a' b' ka kb).length=(fw (ws.map Prod.fst) a'.1 b'.1 d ka kb).length:=by
        have nd1 : (h7 ws (if d then 1 else 0) a' b' ka kb).Nodup:=by
          unfold h7;have sub:=nm ws a' b' ((if d then 1 else 0) == 2) ka kb;exact List.nodup_cons.mpr ⟨fun hm => (eq ▸ fr) ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
        have nd2 : (fw (ws.map Prod.fst) a'.1 b'.1 d ka kb).Nodup:=by
          unfold fw;let r0:=((ws.map Prod.fst).erase a'.1).erase b'.1
          have rn : r0.Nodup:=(nd.erase _).erase _
          have ar : a'.1 ∉ r0:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b'.1 ∉ r0:=(nd.erase a'.1).not_mem_erase
          have nk:=k7 kb b'.1 r0 rn br
          have ax : a'.1 ∉ g6 kb b'.1 r0:=by cases kb <;> simp [g6,ar,ne']
          refine List.nodup_cons.mpr ⟨fun hm => ?_,k7 ka a'.1 _ nk ax⟩;rw [kh] at hm;rcases hm with ⟨heq,_⟩ | hm
          · exact fr (heq.symm ▸ List.mem_map_of_mem aa)
          · rw [kh] at hm;rcases hm with ⟨heq,_⟩ | hm
            · exact fr (heq.symm ▸ List.mem_map_of_mem bb)
            · exact fr (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [← List.toFinset_card_of_nodup nd1,← List.toFinset_card_of_nodup nd2,hf]
      have hbo : ((if d then 1 else 0) == 2)=false:=by cases d <;> rfl
      rw [hf,t3,hbo] at hev;exact hev
    rcases w7 vr (List.mem_range.mpr hi) (List.mem_range.mpr hj) hij d with hh | hh
    · exact one i j hi hj hij ka kb a b hgetI hgetJ haW hbW ne pro gi hh
    · have hsw:=tc (ws.map Prod.fst) nd a.1 b.1 d ka kb
      have hlenSw : (fw (ws.map Prod.fst) a.1 b.1 d ka kb).length=(fw (ws.map Prod.fst) b.1 a.1 d kb ka).length:=by
        have ndA : (fw (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup:=by
          unfold fw;let rA:=((ws.map Prod.fst).erase a.1).erase b.1
          have rn : rA.Nodup:=(nd.erase a.1).erase b.1
          have ar : a.1 ∉ rA:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ rA:=(nd.erase a.1).not_mem_erase
          have nk:=k7 kb b.1 rA rn br
          have ax : a.1 ∉ g6 kb b.1 rA:=by cases kb <;> simp [g6,ar,ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_,k7 ka a.1 _ nk ax⟩;rw [kh] at hm;rcases hm with ⟨heq,_⟩ | hm
          · exact gi (heq.symm ▸ List.mem_map_of_mem haW)
          · rw [kh] at hm;rcases hm with ⟨heq,_⟩ | hm
            · exact gi (heq.symm ▸ List.mem_map_of_mem hbW)
            · exact gi (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        have ndB : (fw (ws.map Prod.fst) b.1 a.1 d kb ka).Nodup:=by
          unfold fw;let rB:=((ws.map Prod.fst).erase b.1).erase a.1
          have rn : rB.Nodup:=(nd.erase b.1).erase a.1
          have br : b.1 ∉ rB:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have ar : a.1 ∉ rB:=(nd.erase b.1).not_mem_erase
          have nk:=k7 ka a.1 rB rn ar
          have bx : b.1 ∉ g6 ka a.1 rB:=by cases ka <;> simp [g6,br,Ne.symm ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_,k7 kb b.1 _ nk bx⟩;rw [bin_comm d b.1 a.1] at hm;rw [kh] at hm;rcases hm with ⟨heq,_⟩ | hm
          · exact gi (heq.symm ▸ List.mem_map_of_mem hbW)
          · rw [kh] at hm;rcases hm with ⟨heq,_⟩ | hm
            · exact gi (heq.symm ▸ List.mem_map_of_mem haW)
            · exact gi (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [← List.toFinset_card_of_nodup ndA,← List.toFinset_card_of_nodup ndB,hsw]
      rw [hsw,hlenSw];exact one j i hj hi hij.symm kb ka b a hgetJ hgetI hbW haW (Ne.symm ne) (bin_comm d a.1 b.1 ▸ pro) (bin_comm d a.1 b.1 ▸ gi) hh
def vm (T:Nat) (c:g4) : Bool :=
  decide c.2.2.2.2.1.Nodup && !(c.2.2.2.2.1.contains T)
def jq (g:Forest) (f9:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (fh:Nat→ Option (List Nat)) (k tm i:Nat) : Bool :=
  let raw:=(j4 g).map fb
  let c:=q3 g raw (raw.map Prod.fst) f9 idx fh k tm i
  vm (graphGoal g.mask).toNat c&&(if k=0 then true else ki c (List.range c.2.2.1))
lemma lh (g:Forest) (f9:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (fh:Nat→ Option (List Nat)) (k tm i:Nat)
    (samples:k1 (graphGoal g.mask) (n2 fun j => (g.samples j).1) (n2 fun j => (g.samples j).2))
    (cols:∀ ci ∈ g.cols.values,rg (vars g.mask) (graphGoal g.mask) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (tw:∀ x ∈ g.autos.toList,autoOK (graphGoal g.mask) (x.map swapRows)=true)
    (hrot:∀ p,fh p=(g.autos[p]?).map (fun perm => ((vars g.mask).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat))
    (jv:k > 0→ ∀ ct' ≤ 3,∀ j < (f9 (4*(k - 1)+ct')).1,
      ImpossibleT (graphGoal g.mask) (k - 1) ct' (stateSetG g f9 (4*(k - 1)+ct') j (vars g.mask)).toFinset)
    (pj:jq g f9 idx fh k tm i=true) :
    ImpossibleT (graphGoal g.mask) k tm (stateSetG g f9 (4*k+tm) i (vars g.mask)).toFinset:=by
  rw [vj];unfold jq vm q3 at pj
  rcases hlv : f9 (4*k+tm) with ⟨num,g5,cw,offw,data⟩
  simp only [hlv,List.length_map,nt,k3,List.map_map,Function.comp_def,fb] at pj
  let ow:=opW (j4 g).length g5
  let len:=ow*g5
  let h9:=len+(j4 g).length+g5
  let recp:=j8 data (i*h9) h9
  let ops:=recp &&& ((1 <<< len) - 1)
  let f8:=jg ow g5 ops (j4 g)
  let ws:=gp (recp >>> len) f8
  have hws_eq : (pi (j4 g) f9 (4*k+tm) i).2.2=ws:=by simp [pi,hlv,ws,f8,ops,recp,h9,len,ow]
  rw [hws_eq];simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at pj
  have hN : (ws.map Prod.fst).Nodup:=by
    have hndN : ((ws.map Prod.fst).map BitVec.toNat).Nodup:=by simpa [List.map_map,Function.comp_def] using pj.1.1
    exact (List.nodup_map_iff (fun _ _ => BitVec.eq_of_toNat_eq)).mp hndN
  have hT : graphGoal g.mask ∉ ws.map Prod.fst:=fun hm =>
    pj.1.2 (by simpa [List.map_map,Function.comp_def] using List.mem_map_of_mem (f:=BitVec.toNat) hm)
  by_cases h0 : k=0
  · subst k;intro k' t' hk' _ h
    have hk0 : k' = 0:=by omega
    subst hk0
    generalize he : (ws.map Prod.fst).toFinset=S at h;rw [h.zeroSet] at he
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hchk2 : ki (k,tm,ws.length,ws.map fb,ws.map (fun w => w.1.toNat),
      nz false (ws.map fb),nz true (ws.map fb),
      (sq data cw g5 (j8 data (num*h9+(i+1)*offw) offw - j8 data (num*h9+i*offw) offw)
        (num*h9+(num+1)*offw+j8 data (num*h9+i*offw) offw*(cw+g5))).filterMap
        (fun x => m3 g ((j4 g).map (fun w => w.1.toNat)) (ws.map (fun w => w.1.toNat)) (k - 1) ow ops g5 (f8.map (fun w => w.1.toNat)) x.1 x.2),
      fun ct tag => ((idx (4*k+tm) ct tag).bind (lu f9 fh (k - 1) ct)).toList,
      (ws.map (fun w => w.1.toNat)).map qg,((ws.map (fun w => w.1.toNat)).map qg).foldl (· + ·) 0) (List.range ws.length)=true:=by
    simpa only [h0,ite_false,List.length_map,List.map_map,Function.comp_def,fb] using pj.2
  apply w8 (raw:=vars g.mask) samples _ hN hT _ _ (Or.inr hchk2)
  · intro v hv;exact rl _ _ _ _ _ _ (sn g) v ((sp _ _).subset hv)
  · intro qp hqp
    obtain ⟨⟨a,b⟩,_,hbq⟩ := List.mem_filterMap.mp hqp
    have hraw : (j4 g).map (fun w => w.1.toNat)=(vars g.mask).map BitVec.toNat:=by
      rw [← nu g,List.map_map];rfl
    rw [hraw] at hbq
    obtain ⟨p,hbr,hqv⟩ := qd g ws (k - 1) ow ops g5 f8 a b hbq
    exact ⟨p,rm g cols hbr,hqv⟩
  · intro ct tag xsN hx
    have e : ((idx (4*k+tm) ct tag).bind (lu f9 fh (k - 1) ct))=some xsN:=by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact r3 g f9 fh (k - 1) ct tw hrot (jv (by omega)) h
def blockG (g:Forest) (f9:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (fh:Nat→ Option (List Nat)) (k tm start:Nat) : Nat→ Bool
  | 0 => true
  | n+1 => jq g f9 idx fh k tm start&&blockG g f9 idx fh k tm (start+1) n
lemma ts {g f9 idx fh k tm start n} (h:blockG g f9 idx fh k tm start n=true)
    (i:Nat) (lo:start ≤ i) (hi:i < start+n) : jq g f9 idx fh k tm i=true:=by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [blockG,Bool.and_eq_true] at h
    by_cases eq : i=start
    · exact eq ▸ h.1
    · exact ih h.2 (by omega) (by omega)
lemma blockG_merge {g f9 idx fh k tm start a b}
    (ha:blockG g f9 idx fh k tm start a=true)
    (hb:blockG g f9 idx fh k tm (start+a) b=true) :
    blockG g f9 idx fh k tm start (a+b)=true:=by
  induction a generalizing start with
  | zero => simpa [blockG] using hb
  | succ a ih =>
    simp only [blockG,Nat.succ_add,Bool.and_eq_true] at ha ⊢
    exact ⟨ha.1,ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm 1] using hb)⟩
lemma blockG_zero {g lv idx rot k tm s n} (hn:n=0) : blockG g lv idx rot k tm s n=true:=by subst hn;rfl
lemma blockG_eq {g lv idx rot k tm k' tm' n n'}
    (h:blockG g lv idx rot k' tm' 0 n' = true) (hk:k=k') (ht:tm=tm') (hn:n=n') :
    blockG g lv idx rot k tm 0 n=true:=by subst hk;subst ht;subst hn;exact h
lemma rot_at_of {m na:Nat} {r:Nat→ Option (List Nat)} {auts:Array (List Nat)}
    (heq:(List.range na).all (fun p => match r p,auts[p]? with
      | some xs,some perm => xs == ((vars m).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat
      | _,_ => false)=true)
    (hnone:∀ p ≥ na,r p=none) (hsz:auts.size=na) :
    ∀ p,r p=(auts[p]?).map (fun perm => ((vars m).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat):=by
  intro p
  by_cases hp : p < na
  · have h:=List.all_eq_true.mp heq p (List.mem_range.mpr hp)
    cases h1 : r p <;> cases h2 : auts[p]? <;> simp [h1,h2] at h ⊢;exact h
  · rw [hnone p (by omega),Array.getElem?_eq_none (by omega)];rfl
def r6 (x:Nat) : Bits:=BitVec.ofNat 768 (x*0x10000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001)
lemma k5 {old m cap ci hints ly} (prev:kv old)
    (ok:(md m ci (boundsBefore old)&&kt (graphGoal m) &&
      gh (graphGoal m) (vars m) (kl m hints) &&
      rt (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (vars m) (vars m) &&
      ly.all (fun v => p9 v.1 m v.2))=true)
    (all:(kl m hints).map Prod.fst=vars m)
    (nd:(vars m).Nodup) :
    kv (g1 old (cap+1) ly):=by
  simp only [Bool.and_eq_true] at ok;exact gw prev (tf (before_sound old prev) ok.1.1.1.1 ok.1.1.1.2 ok.1.1.2 all nd ok.1.2) ok.2
lemma x1 {g f9 idx fh k tm start n}
    (h:∀ i,start ≤ i→ i < start+n→ jq g f9 idx fh k tm i=true) :
    blockG g f9 idx fh k tm start n=true:=by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [blockG,Bool.and_eq_true];exact ⟨h _ (by omega) (by omega),ih (fun i lo hi => h i (by omega) (by omega))⟩
def f3 {α} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => (f3 f xs <<< 769)+f x
lemma xx {α} (f : α → Bits) (xs:List α) :
    f3 (fun x => (f x).toNat) xs=f4 f xs:=by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [f3,f4,g3,ih,Nat.shiftLeft_eq,Nat.mul_comm]
def lw (k tm n r:Nat) (u v:j6) (xs:List g4)
    (i j op:Nat) (ca0 ca1 cb0 cb1 cz0 cz1:Nat) : Bool :=
  let un:=op == 2
  let go (ka kb:Bool) : Bool :=
    let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
    if len > k then true else
      let dd:=ji tm k len un == 0
      let mask:=mf r (gn (if dd then v else u) (if dd then ca1 else ca0) (if dd then cb1 else cb0) un ka kb ||| (if dd then cz1 else cz0))
      pd (fun c => fbN c i j op ka kb) mask xs
  if un then go false false&&go true true
  else go false false&&go true false&&go false true&&go true true
def n0 (k tm ar r:Nat) (u v:j6) (xs:List g4)
    (i pa qa ca0 ca1:Nat) : Nat→ List (Nat × Nat × Nat × Nat)→ Bool
  | _,[] => true
  | j,(pb,qb,cb0,cb1) :: bs =>
    let ap:=pa &&& pb;let aq:=qa &&& qb
    let op0:=lw k tm ar r u v xs i j 0 ca0 ca1 cb0 cb1 (ap ^^^ aq) (ap ^^^ (ap &&& aq))
    let op1:=if op0 then
      let bp:=pa ||| pb;let bq:=qa ||| qb
      lw k tm ar r u v xs i j 1 ca0 ca1 cb0 cb1 (bp ^^^ bq) (bp ^^^ (bp &&& bq))
    else false
    op1&&n0 k tm ar r u v xs i pa qa ca0 ca1 (j+1) bs
def lx (k tm ar r full:Nat) (u v:j6) (xs:List g4) :
    Nat→ List (Nat × Nat × Nat × Nat)→ Bool
  | _,[] => true
  | i,(pa,qa,ca0,ca1) :: rest =>
    let unOk:=if tm == 0 then true else
      let zp:=full ^^^ pa;let zq:=full ^^^ qa
      lw k tm ar r u v xs i i 2 ca0 ca1 ca0 ca1 (zp ^^^ zq) (zp ^^^ (zp &&& zq))
    unOk&&n0 k tm ar r u v xs i pa qa ca0 ca1 (i+1) rest&&lx k tm ar r full u v xs (i+1) rest
def fg (xs:List g4) (i:Nat) : Nat × Nat × Nat × Nat :=
  let p:=f3 (fun c => (c.2.2.2.1.getD i (0,0,0)).2.1) xs
  let q:=f3 (fun c => (c.2.2.2.1.getD i (0,0,0)).2.2) xs
  (p,q,p ^^^ q,p ^^^ (p &&& q))
def p0 (g:Forest) (f9:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (fh:Nat→ Option (List Nat)) (k tm start n ar:Nat) : Bool :=
  let raw:=(j4 g).map fb
  let rawS:=raw.map Prod.fst
  let xs:=((List.range n).map (start + ·)).map (q3 g raw rawS f9 idx fh k tm)
  xs.all (fun c => c.2.2.1 == ar&&vm (graphGoal g.mask).toNat c) &&
  let r:=k2 xs.length
  let full:=r*g9
  let u : j6:=(f3 (fun c => c.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.2) xs)
  let v : j6:=(f3 (fun c => c.2.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.2) xs)
  let wsP : List (Nat × Nat × Nat × Nat):=(List.range ar).map (fg xs)
  lx k tm ar r full u v xs 0 wsP
def l6 (c:g4) : Prop :=
  (∀ w ∈ c.2.2.2.1,w.2.1 < 2^768∧w.2.2 < 2^768) ∧
  (c.2.2.2.2.2.1.1 < 2^768∧c.2.2.2.2.2.1.2.1 < 2^768∧c.2.2.2.2.2.1.2.2 < 2^768) ∧
  (c.2.2.2.2.2.2.1.1 < 2^768∧c.2.2.2.2.2.2.1.2.1 < 2^768∧c.2.2.2.2.2.2.1.2.2 < 2^768)
def kq (n:Nat) : Bits:=BitVec.ofNat 768 n
lemma fa {n:Nat} (h:n < 2^768) : (kq n).toNat=n:=by
  simp [kq,Nat.mod_eq_of_lt h]
def k6 (w:n7) : lj:=(kq w.2.1,kq w.2.2)
def gr (cv:Nat × Nat × Nat) : wv:=(kq cv.1,kq cv.2.1,kq cv.2.2)
lemma xy (d:ff) : (fb d).2.1 < 2^768∧(fb d).2.2 < 2^768:=⟨d.2.1.isLt,d.2.2.isLt⟩
lemma sx (g:Forest) (f9:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (fh:Nat→ Option (List Nat)) (k tm i:Nat) :
    l6 (q3 g ((j4 g).map fb) (((j4 g).map fb).map Prod.fst) f9 idx fh k tm i):=by
  unfold q3 l6;rcases f9 (4*k+tm) with ⟨num,g5,cw,offw,data⟩;dsimp only;simp only [List.length_map,nt,k3];refine ⟨?_,?_,?_⟩
  · intro w hw;obtain ⟨d,_,rfl⟩ := List.mem_map.mp hw;exact xy d
  · rw [vi];exact ⟨(ft false _).1.isLt,(ft false _).2.1.isLt,(ft false _).2.2.isLt⟩
  · rw [vi];exact ⟨(ft true _).1.isLt,(ft true _).2.1.isLt,(ft true _).2.2.isLt⟩
lemma gu {k tm ar full:Nat} {xs:List g4} {i j op:Nat} {ka kb:Bool}
    (hrng:∀ c ∈ xs,l6 c) (hfull:full=k2 xs.length*g9)
    (hq:q < xs.length) (hb:xs[q].1=k) (ht:xs[q].2.1=tm) (ha:xs[q].2.2.1=ar)
    (hun:op == 2→ (ka=false∧kb=false)∨(ka=true∧kb=true))
    (hpass :
      let r:=k2 xs.length
      let u : j6:=(f3 (fun c => c.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.2) xs)
      let v : j6:=(f3 (fun c => c.2.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.2) xs)
      let pa:=(fg xs i).1
      let qa:=(fg xs i).2.1
      let pb:=(fg xs j).1
      let qb:=(fg xs j).2.1
      let zp:=if op == 2 then full ^^^ pa else if op == 1 then pa ||| pb else pa &&& pb
      let zq:=if op == 2 then full ^^^ qa else if op == 1 then qa ||| qb else qa &&& qb
      lw k tm ar r u v xs i j op (fg xs i).2.2.1 (fg xs i).2.2.2 (fg xs j).2.2.1 (fg xs j).2.2.2 (zp ^^^ zq) (zp ^^^ (zp &&& zq))=true) :
    jp xs[q] i j op ka kb=true:=by
  subst hfull;dsimp only [fg] at hpass;unfold lw at hpass;dsimp only at hpass
  have hgo : (let len:=1+(ar - (if ka then 0 else 1) - (if (op == 2)||kb then 0 else 1))
      if len > k then true else
        let dd:=ji tm k len (op == 2) == 0
        let r:=k2 xs.length
        let full:=r*g9
        let u : j6:=(f3 (fun c => c.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.2) xs)
        let v : j6:=(f3 (fun c => c.2.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.2) xs)
        let pa:=f3 (fun c => (c.2.2.2.1.getD i (0,0,0)).2.1) xs
        let qa:=f3 (fun c => (c.2.2.2.1.getD i (0,0,0)).2.2) xs
        let pb:=f3 (fun c => (c.2.2.2.1.getD j (0,0,0)).2.1) xs
        let qb:=f3 (fun c => (c.2.2.2.1.getD j (0,0,0)).2.2) xs
        let zp:=if op == 2 then full ^^^ pa else if op == 1 then pa ||| pb else pa &&& pb
        let zq:=if op == 2 then full ^^^ qa else if op == 1 then qa ||| qb else qa &&& qb
        let mask:=mf r (gn (if dd then v else u) (if dd then pa ^^^ (pa &&& qa) else pa ^^^ qa) (if dd then pb ^^^ (pb &&& qb) else pb ^^^ qb) (op == 2) ka kb ||| (if dd then zp ^^^ (zp &&& zq) else zp ^^^ zq))
        pd (fun c => fbN c i j op ka kb) mask xs)=true:=by
    by_cases h2 : (op == 2)=true
    · rw [if_pos h2] at hpass;simp only [Bool.and_eq_true] at hpass
      rcases hun h2 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hpass.1
      · exact hpass.2
    · rw [if_neg h2] at hpass;simp only [Bool.and_eq_true] at hpass
      cases ka <;> cases kb
      · exact hpass.1.1.1
      · exact hpass.1.2
      · exact hpass.1.1.2
      · exact hpass.2
  dsimp only at hgo
  set len:=1+(ar - (if ka then 0 else 1) - (if (op == 2)||kb then 0 else 1))
  by_cases tx : len > k
  · rcases hxq : xs[q] with ⟨cap,tmm,nn,ws,wsN,u0,v0,j2,lfn,mn,qk⟩
    rw [hxq] at hb ha;dsimp only at hb ha;subst hb ha;dsimp only [jp,len] at tx ⊢;rw [if_pos tx]
  · rw [if_neg tx] at hgo
    set dd:=ji tm k len (op == 2) == 0
    have hget_lt (c:g4) (hc:c ∈ xs) (idx:Nat) : (c.2.2.2.1.getD idx (0,0,0)).2.1 < 2^768∧(c.2.2.2.1.getD idx (0,0,0)).2.2 < 2^768:=by
      rw [List.getD_eq_getElem?_getD]
      cases he : c.2.2.2.1[idx]? with
      | none => exact ⟨Nat.two_pow_pos 768,Nat.two_pow_pos 768⟩
      | some w => exact (hrng c hc).1 w (List.mem_of_getElem? he)
    have hlane_eq (f:g4→ Nat) (ys:List g4) (hf:∀ c ∈ ys,f c < 2^768) :
        f3 f ys=f4 (fun c => kq (f c)) ys:=by
      induction ys with
      | nil => rfl
      | cons c rest ih =>
        simp only [f3,f4,g3,fa (hf c List.mem_cons_self),Nat.shiftLeft_eq,Nat.mul_comm];rw [ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))]
    have hpa : f3 (fun c => (c.2.2.2.1.getD i (0,0,0)).2.1) xs=f4 (fun c => (k6 (c.2.2.2.1.getD i (0,0,0))).1) xs :=
      hlane_eq _ xs (fun c hc => (hget_lt c hc i).1)
    have hqa : f3 (fun c => (c.2.2.2.1.getD i (0,0,0)).2.2) xs=f4 (fun c => (k6 (c.2.2.2.1.getD i (0,0,0))).2) xs :=
      hlane_eq _ xs (fun c hc => (hget_lt c hc i).2)
    have hpb : f3 (fun c => (c.2.2.2.1.getD j (0,0,0)).2.1) xs=f4 (fun c => (k6 (c.2.2.2.1.getD j (0,0,0))).1) xs :=
      hlane_eq _ xs (fun c hc => (hget_lt c hc j).1)
    have hqb : f3 (fun c => (c.2.2.2.1.getD j (0,0,0)).2.2) xs=f4 (fun c => (k6 (c.2.2.2.1.getD j (0,0,0))).2) xs :=
      hlane_eq _ xs (fun c hc => (hget_lt c hc j).2)
    have hu : (f3 (fun c => c.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.2) xs) =
        j7 (fun c => gr c.2.2.2.2.2.1) xs:=by
      simp only [j7,gr];rw [hlane_eq _ xs (fun c hc => (hrng c hc).2.1.1),hlane_eq _ xs (fun c hc => (hrng c hc).2.1.2.1),hlane_eq _ xs (fun c hc => (hrng c hc).2.1.2.2)]
    have hv : (f3 (fun c => c.2.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.2) xs) =
        j7 (fun c => gr c.2.2.2.2.2.2.1) xs:=by
      simp only [j7,gr];rw [hlane_eq _ xs (fun c hc => (hrng c hc).2.2.1),hlane_eq _ xs (fun c hc => (hrng c hc).2.2.2.1),hlane_eq _ xs (fun c hc => (hrng c hc).2.2.2.2)]
    let aB : g4→ lj:=fun c => k6 (c.2.2.2.1.getD i (0,0,0))
    let bB : g4→ lj:=fun c => k6 (c.2.2.2.1.getD j (0,0,0))
    let zB : g4→ lj:=fun c =>
      if op == 2 then (~~~(aB c).1,~~~(aB c).2) else if op == 1 then ((aB c).1 ||| (bB c).1,(aB c).2 ||| (bB c).2) else ((aB c).1 &&& (bB c).1,(aB c).2 &&& (bB c).2)
    have hzp : (if op == 2 then k2 xs.length*g9 ^^^ f4 (fun c => (aB c).1) xs
        else if op == 1 then f4 (fun c => (aB c).1) xs ||| f4 (fun c => (bB c).1) xs
        else f4 (fun c => (aB c).1) xs &&& f4 (fun c => (bB c).1) xs) =
        f4 (fun c => (zB c).1) xs:=by
      by_cases h2 : op == 2
      · simp only [zB,h2,ite_true,gj,qu,lp,vd]
      · by_cases h1 : op == 1 <;> simp only [zB,h2,h1,Bool.false_eq_true,ite_false,ite_true,nq,ln]
    have hzq : (if op == 2 then k2 xs.length*g9 ^^^ f4 (fun c => (aB c).2) xs
        else if op == 1 then f4 (fun c => (aB c).2) xs ||| f4 (fun c => (bB c).2) xs
        else f4 (fun c => (aB c).2) xs &&& f4 (fun c => (bB c).2) xs) =
        f4 (fun c => (zB c).2) xs:=by
      by_cases h2 : op == 2
      · simp only [zB,h2,ite_true,gj,qu,lp,vd]
      · by_cases h1 : op == 1 <;> simp only [zB,h2,h1,Bool.false_eq_true,ite_false,ite_true,nq,ln]
    have hcol_lane (f:g4→ lj) :
        (if dd then f4 (fun c => (f c).1) xs ^^^ (f4 (fun c => (f c).1) xs &&& f4 (fun c => (f c).2) xs)
         else f4 (fun c => (f c).1) xs ^^^ f4 (fun c => (f c).2) xs) =
        f4 (fun c => fq dd (f c)) xs:=by
      cases dd <;> simp [fq,ln,lp,sj]
    have hcv_lane : (if dd then j7 (fun c => gr c.2.2.2.2.2.2.1) xs else j7 (fun c => gr c.2.2.2.2.2.1) xs) =
        j7 (fun c => if dd then gr c.2.2.2.2.2.2.1 else gr c.2.2.2.2.2.1) xs:=by
      cases dd <;> rfl
    rw [hpa,hqa,hpb,hqb,hu,hv] at hgo;change pd (fun c => fbN c i j op ka kb) (mf (k2 xs.length)
      (gn (if dd then j7 (fun c => gr c.2.2.2.2.2.2.1) xs else j7 (fun c => gr c.2.2.2.2.2.1) xs)
        (if dd then f4 (fun c => (aB c).1) xs ^^^ (f4 (fun c => (aB c).1) xs &&& f4 (fun c => (aB c).2) xs)
         else f4 (fun c => (aB c).1) xs ^^^ f4 (fun c => (aB c).2) xs)
        (if dd then f4 (fun c => (bB c).1) xs ^^^ (f4 (fun c => (bB c).1) xs &&& f4 (fun c => (bB c).2) xs)
         else f4 (fun c => (bB c).1) xs ^^^ f4 (fun c => (bB c).2) xs)
        (op == 2) ka kb |||
       (if dd then _ ^^^ (_ &&& _) else _ ^^^ _))) xs=true at hgo
    rw [hzp,hzq,hcol_lane aB,hcol_lane bB,hcol_lane zB,hcv_lane,td,nq] at hgo
    let combB : Bits:=m0 (if dd then gr xs[q].2.2.2.2.2.2.1 else gr xs[q].2.2.2.2.2.1)
      (fq dd (aB xs[q])) (fq dd (bB xs[q])) (op == 2) ka kb ||| fq dd (zB xs[q])
    have hq_mem : xs[q] ∈ xs:=List.getElem_mem hq
    have hq_a:=hget_lt xs[q] hq_mem i
    have hq_b:=hget_lt xs[q] hq_mem j
    have hq_c:=hrng xs[q] hq_mem
    have hcomb_nat : combB.toNat =
        let a:=xs[q].2.2.2.1.getD i (0,0,0)
        let b:=xs[q].2.2.2.1.getD j (0,0,0)
        let z:=jt op a b
        let col:=fun (w:n7) => if dd then w.2.1 ^^^ (w.2.1 &&& w.2.2) else w.2.1 ^^^ w.2.2
        gn (if dd then xs[q].2.2.2.2.2.2.1 else xs[q].2.2.2.2.2.1) (col a) (col b) (op == 2) ka kb ||| col z:=by
      have hcol_q (w:n7) (h1:w.2.1 < 2^768) (h2:w.2.2 < 2^768) :
          (fq dd (k6 w)).toNat=(if dd then w.2.1 ^^^ (w.2.1 &&& w.2.2) else w.2.1 ^^^ w.2.2):=by
        cases dd
        · simp only [fq,k6,Bool.false_eq_true,ite_false,BitVec.toNat_xor,fa h1,fa h2]
        · simp only [fq,k6,ite_true,g7,fa h1,fa h2]
      have hz_sig : zB xs[q]=k6 (jt op (xs[q].2.2.2.1.getD i (0,0,0)) (xs[q].2.2.2.1.getD j (0,0,0))):=by
        simp only [zB,jt,aB,bB,k6]
        by_cases h2 : op == 2
        · simp only [h2,ite_true,Prod.mk.injEq]
          exact ⟨BitVec.eq_of_toNat_eq (by rw [jf,← gj,fa hq_a.1,fa (Nat.xor_lt_two_pow (by rw [gj];exact BitVec.isLt _) hq_a.1)]),
                 BitVec.eq_of_toNat_eq (by rw [jf,← gj,fa hq_a.2,fa (Nat.xor_lt_two_pow (by rw [gj];exact BitVec.isLt _) hq_a.2)])⟩
        · by_cases h1 : op == 1
          · simp only [h2,h1,Bool.false_eq_true,ite_false,ite_true,Prod.mk.injEq]
            exact ⟨BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_or,fa hq_a.1,fa hq_b.1,fa (Nat.or_lt_two_pow hq_a.1 hq_b.1)]),
                   BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_or,fa hq_a.2,fa hq_b.2,fa (Nat.or_lt_two_pow hq_a.2 hq_b.2)])⟩
          · simp only [h2,h1,Bool.false_eq_true,ite_false,Prod.mk.injEq]
            exact ⟨BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_and,fa hq_a.1,fa hq_b.1,fa (Nat.and_lt_two_pow _ hq_b.1)]),
                   BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_and,fa hq_a.2,fa hq_b.2,fa (Nat.and_lt_two_pow _ hq_b.2)])⟩
      have hzq_lt : (jt op (xs[q].2.2.2.1.getD i (0,0,0)) (xs[q].2.2.2.1.getD j (0,0,0))).2.1 < 2^768 ∧
          (jt op (xs[q].2.2.2.1.getD i (0,0,0)) (xs[q].2.2.2.1.getD j (0,0,0))).2.2 < 2^768:=by
        unfold jt
        by_cases h2 : op == 2
        · simp only [h2,ite_true];exact ⟨Nat.xor_lt_two_pow (by rw [gj];exact BitVec.isLt _) hq_a.1,Nat.xor_lt_two_pow (by rw [gj];exact BitVec.isLt _) hq_a.2⟩
        · by_cases h1 : op == 1
          · simp only [h2,h1,Bool.false_eq_true,ite_false,ite_true];exact ⟨Nat.or_lt_two_pow hq_a.1 hq_b.1,Nat.or_lt_two_pow hq_a.2 hq_b.2⟩
          · simp only [h2,h1,Bool.false_eq_true,ite_false];exact ⟨Nat.and_lt_two_pow _ hq_b.1,Nat.and_lt_two_pow _ hq_b.2⟩
      have htk : (m0 (if dd then gr xs[q].2.2.2.2.2.2.1 else gr xs[q].2.2.2.2.2.1)
          (fq dd (aB xs[q])) (fq dd (bB xs[q])) (op == 2) ka kb).toNat =
          gn (if dd then xs[q].2.2.2.2.2.2.1 else xs[q].2.2.2.2.2.1)
            (if dd then (xs[q].2.2.2.1.getD i (0,0,0)).2.1 ^^^ ((xs[q].2.2.2.1.getD i (0,0,0)).2.1 &&& (xs[q].2.2.2.1.getD i (0,0,0)).2.2) else (xs[q].2.2.2.1.getD i (0,0,0)).2.1 ^^^ (xs[q].2.2.2.1.getD i (0,0,0)).2.2)
            (if dd then (xs[q].2.2.2.1.getD j (0,0,0)).2.1 ^^^ ((xs[q].2.2.2.1.getD j (0,0,0)).2.1 &&& (xs[q].2.2.2.1.getD j (0,0,0)).2.2) else (xs[q].2.2.2.1.getD j (0,0,0)).2.1 ^^^ (xs[q].2.2.2.1.getD j (0,0,0)).2.2)
            (op == 2) ka kb:=by
        rw [ps,hcol_q _ hq_a.1 hq_a.2,hcol_q _ hq_b.1 hq_b.2]
        cases dd
        · simp only [Bool.false_eq_true,ite_false,gr,
            fa hq_c.2.1.1,fa hq_c.2.1.2.1,fa hq_c.2.1.2.2]
        · simp only [ite_true,gr,
            fa hq_c.2.2.1,fa hq_c.2.2.2.1,fa hq_c.2.2.2.2]
      dsimp only [combB];rw [BitVec.toNat_or,htk,hz_sig,hcol_q _ hzq_lt.1 hzq_lt.2]
    rcases hxq : xs[q] with ⟨cap,tmm,nn,ws,wsN,u0,v0,j2,lfn,mn,qk⟩
    rw [hxq] at hb ht ha hcomb_nat;dsimp only at hb ht ha hcomb_nat;subst hb ht ha;dsimp only [jp,len] at tx ⊢
    rw [if_neg tx]
    by_cases hhit : combB=BitVec.allOnes 768
    · have hfb:=xu _ _ _ q hq (by rw [c3 _ _ _ hq];exact beq_iff_eq.mpr hhit) hgo
      rw [hxq] at hfb
      have hite (b:Bool) : (if b=true then true else fbN (cap,tmm,nn,ws,wsN,u0,v0,j2,lfn,mn,qk) i j op ka kb)=true:=by
        cases b <;> simp [hfb]
      exact hite _
    · have hne : (combB.toNat != g9)=true:=by
        simp only [bne_iff_ne];intro heq;apply hhit;apply BitVec.eq_of_toNat_eq;rw [heq,gj]
      rw [hcomb_nat] at hne;exact if_pos hne
lemma ti {k tm ar:Nat} {xs:List g4}
    (hrng:∀ c ∈ xs,l6 c)
    {q:Nat} (hq:q < xs.length) (hb:xs[q].1=k) (ht:xs[q].2.1=tm) (ha:xs[q].2.2.1=ar)
    (i j0 lenJ:Nat) :
    n0 k tm ar (k2 xs.length)
      (f3 (fun c => c.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.2) xs)
      (f3 (fun c => c.2.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.2) xs)
      xs i (fg xs i).1 (fg xs i).2.1 (fg xs i).2.2.1 (fg xs i).2.2.2 j0 ((List.range' j0 lenJ).map (fg xs))=true →
    (List.range' j0 lenJ).all (fun j => jc xs[q] i j 0&&jc xs[q] i j 1)=true:=by
  induction lenJ generalizing j0 with
  | zero => intro _;rfl
  | succ lenJ ih =>
    intro hok;simp only [List.range'_succ,List.map_cons,n0,Bool.and_eq_true] at hok
    have hop0 : lw k tm ar (k2 xs.length)
        (f3 (fun c => c.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.2) xs)
        (f3 (fun c => c.2.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.2) xs)
        xs i j0 0 (fg xs i).2.2.1 (fg xs i).2.2.2 (fg xs j0).2.2.1 (fg xs j0).2.2.2
        ((fg xs i).1 &&& (fg xs j0).1 ^^^ ((fg xs i).2.1 &&& (fg xs j0).2.1))
        ((fg xs i).1 &&& (fg xs j0).1 ^^^ ((fg xs i).1 &&& (fg xs j0).1 &&& ((fg xs i).2.1 &&& (fg xs j0).2.1)))=true:=by
      split at hok
      · assumption
      · cases hok.1
    have hop1 : lw k tm ar (k2 xs.length)
        (f3 (fun c => c.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.2) xs)
        (f3 (fun c => c.2.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.2) xs)
        xs i j0 1 (fg xs i).2.2.1 (fg xs i).2.2.2 (fg xs j0).2.2.1 (fg xs j0).2.2.2
        (((fg xs i).1 ||| (fg xs j0).1) ^^^ ((fg xs i).2.1 ||| (fg xs j0).2.1))
        (((fg xs i).1 ||| (fg xs j0).1) ^^^ (((fg xs i).1 ||| (fg xs j0).1) &&& ((fg xs i).2.1 ||| (fg xs j0).2.1)))=true:=by
      have h1:=hok.1;rw [if_pos hop0] at h1;exact h1
    simp only [List.range'_succ,List.all_cons,Bool.and_eq_true];refine ⟨⟨?_,?_⟩,ih (j0+1) hok.2⟩
    · simp only [jc,Bool.and_eq_true]
      exact ⟨⟨⟨gu hrng rfl hq hb ht ha (by simp) hop0,gu hrng rfl hq hb ht ha (by simp) hop0⟩,
        gu hrng rfl hq hb ht ha (by simp) hop0⟩,gu hrng rfl hq hb ht ha (by simp) hop0⟩
    · simp only [jc,Bool.and_eq_true]
      exact ⟨⟨⟨gu hrng rfl hq hb ht ha (by simp) hop1,gu hrng rfl hq hb ht ha (by simp) hop1⟩,
        gu hrng rfl hq hb ht ha (by simp) hop1⟩,gu hrng rfl hq hb ht ha (by simp) hop1⟩
lemma tj {k tm ar full:Nat} {xs:List g4}
    (hrng:∀ c ∈ xs,l6 c) (hfull:full=k2 xs.length*g9)
    {q:Nat} (hq:q < xs.length) (hb:xs[q].1=k) (ht:xs[q].2.1=tm) (ha:xs[q].2.2.1=ar)
    (i0 lenI:Nat) :
    lx k tm ar (k2 xs.length) full
      (f3 (fun c => c.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.2) xs)
      (f3 (fun c => c.2.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.2) xs)
      xs i0 ((List.range' i0 lenI).map (fg xs))=true →
    ki xs[q] (List.range' i0 lenI)=true:=by
  induction lenI generalizing i0 with
  | zero => intro _;rfl
  | succ lenI ih =>
    intro hok;simp only [List.range'_succ,List.map_cons,lx,Bool.and_eq_true] at hok;simp only [List.range'_succ,ki,w6,Bool.and_eq_true];refine ⟨⟨?_,ti hrng hq hb ht ha i0 (i0+1) lenI hok.1.2⟩,ih (i0+1) hok.2⟩;rw [ht]
    by_cases htm : (tm == 0)=true
    · simp [htm]
    · rw [if_neg htm] at hok ⊢
      simp only [Bool.and_eq_true];exact ⟨gu hrng hfull hq hb ht ha (fun _ => Or.inl ⟨rfl,rfl⟩) hok.1.1,
             gu hrng hfull hq hb ht ha (fun _ => Or.inr ⟨rfl,rfl⟩) hok.1.1⟩
lemma chunkBlockG {g f9 idx fh k tm start n ar}
    (h:p0 g f9 idx fh k tm start n ar=true) :
    blockG g f9 idx fh k tm start n=true:=by
  unfold p0 at h;rw [Bool.and_eq_true] at h
  let raw:=(j4 g).map fb
  let rawS:=raw.map Prod.fst
  let xs:=((List.range n).map (start + ·)).map (q3 g raw rawS f9 idx fh k tm)
  have hrng : ∀ c ∈ xs,l6 c:=fun c hc => by
    obtain ⟨idx0,_,rfl⟩ := List.mem_map.mp hc;exact sx g f9 idx fh k tm idx0
  apply x1;intro i lo hi
  have hm : q3 g raw rawS f9 idx fh k tm i ∈ xs:=by
    apply List.mem_map.mpr;exact ⟨i,List.mem_map.mpr ⟨i - start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one:=List.all_eq_true.mp h.1 _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k:=by rw [e];rfl
  have ht : xs[q].2.1=tm:=by rw [e];rfl
  have ha : xs[q].2.2.1=ar:=e ▸ one.1
  simp only [jq,Bool.and_eq_true];refine ⟨one.2,?_⟩;split
  · rfl
  · rw [one.1,List.range_eq_range']
    have h2 : lx k tm ar (k2 xs.length) (k2 xs.length*g9)
        (f3 (fun c => c.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.1.2.2) xs)
        (f3 (fun c => c.2.2.2.2.2.2.1.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.1) xs,f3 (fun c => c.2.2.2.2.2.2.1.2.2) xs)
        xs 0 ((List.range' 0 ar).map (fg xs))=true:=by
      simpa only [← List.range_eq_range'] using h.2
    exact e ▸ tj hrng rfl hq hb ht ha 0 ar h2
def cellsG (g:Forest) (f9:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (fh:Nat→ Option (List Nat)) (k tm start n ar:Nat) : Nat→ Prop
  | 0 => p0 g f9 idx fh k tm start n ar=true
  | d+1 => cellsG g f9 idx fh k tm start (n / 2) ar d ∧
             cellsG g f9 idx fh k tm (start+n / 2) (n - n / 2) ar d
lemma cellsBlockG {g f9 idx fh k tm start n ar d}
    (h:cellsG g f9 idx fh k tm start n ar d) :
    blockG g f9 idx fh k tm start n=true:=by
  induction d generalizing start n with
  | zero => exact chunkBlockG h
  | succ d ih =>
    have v:=blockG_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
lemma forestG_all (g:Forest) (f9:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (fh:Nat→ Option (List Nat)) (top:Nat)
    (jv:Nat→ Nat)
    (lo:∀ m,j3 (vars m) (graphGoal m) (jv m))
    (lz:graphValid g jv=true)
    (hrot:∀ p,fh p=(g.autos[p]?).map (fun perm => ((vars g.mask).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat))
    (tabs:∀ k ≤ top,∀ tm ≤ 3,blockG g f9 idx fh k tm 0 (f9 (4*k+tm)).1=true) :
    ∀ k ≤ top,∀ tm ≤ 3,∀ i < (f9 (4*k+tm)).1,
      ImpossibleT (graphGoal g.mask) k tm (stateSetG g f9 (4*k+tm) i (vars g.mask)).toFinset:=by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at lz
  have m5:=w3 lz.1.1.1 lz.1.1.2
  have cols : ∀ ci ∈ g.cols.values,rg (vars g.mask) (graphGoal g.mask) (subcube ci.1 ci.2.1) ci.2.2.2.2 :=
    fun ci hc => col_sound ci jv lo (lz.1.2 ci hc)
  have tw:=lz.2
  intro k
  induction k with
  | zero =>
    intro hk tm htm i hi;exact lh g f9 idx fh 0 tm i m5 cols tw hrot
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (ts (tabs 0 hk tm htm) i (Nat.zero_le i) (by simpa using hi))
  | succ k ih =>
    intro hk tm htm i hi;exact lh g f9 idx fh (k+1) tm i m5 cols tw hrot
      (fun _ ct' hct j hj => ih (by omega) ct' hct j hj)
      (ts (tabs (k+1) hk tm htm) i (Nat.zero_le i) (by simpa using hi))
lemma jr {g f9 idx fh jv i hints}
    (low:∀ q,j3 (vars q) (graphGoal q) (jv q))
    (geom:graphValid g jv=true)
    (hrot:∀ p,fh p=(g.autos[p]?).map (fun perm => ((vars g.mask).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat))
    (tabs:∀ k ≤ g.cap,∀ tm ≤ 3,blockG g f9 idx fh k tm 0 (f9 (4*k+tm)).1=true)
    (idxOk:decide (i < (f9 (4*g.cap+3)).1) &&
      sameWords (stateSetG g f9 (4*g.cap+3) i (vars g.mask)) (vars g.mask)=true)
    (hp:kt (graphGoal g.mask)=true)
    (ess:gh (graphGoal g.mask) (vars g.mask) (kl g.mask hints)=true)
    (all:(kl g.mask hints).map Prod.fst=vars g.mask) :
    j3 (vars g.mask) (graphGoal g.mask) (g.cap+1):=by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at idxOk;apply mb (k8 _ hp) _ (impT3_to_imp ?_)
  · intro a ha;apply li ess a;rw [all];exact List.mem_toFinset.mpr ha
  · rw [← sameWords_sound idxOk.2]
    exact forestG_all g f9 idx fh g.cap jv low geom hrot tabs g.cap (Nat.le_refl _) 3 (by decide) i idxOk.1
def vn (g:Forest) (p:Nat) : Option (List Nat) :=
  (g.autos[p]?).map (fun perm => ((vars g.mask).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat)
def gx : Nat:=(inputs.getD 0 zero).toNat
def kc : Nat:=(inputs.getD 1 zero).toNat
def gy : Nat:=(inputs.getD 2 zero).toNat
def gz : Nat:=(inputs.getD 3 zero).toNat
def h6 : Nat:=(inputs.getD 4 zero).toNat
def jw : Nat:=(inputs.getD 5 zero).toNat
def ml : Nat:=(inputs.getD 6 zero).toNat
def kx : Nat:=(inputs.getD 7 zero).toNat
def mm : Nat:=(inputs.getD 8 zero).toNat
def x2 : IndexTree ColumnInfo:=(.leaf [])
def zj : Array (List Nat):=Array.mk [[],[33,48]]
def s15 : Nat→ Bits × Bits
| 0 => (r6 0x59cc1f8efd67307e3bf59cc1f8efd673,r6 0x1949bb08906526ec2241949bb0890652)
| 1 => (r6 0xe1fc7ff0ff87f1ffc3fe1fc7ff0ff87f,r6 0x20a644c04882991301220a644c048829)
| 2 => (r6 0xbe73e3ff1ef9cf8ffc7be73e3ff1ef9c,r6 0x14512a24045144a890114512a2404514)
| 3 => (r6 0x3f8383ffe0fe0e0fff83f8383ffe0fe0,r6 0x2b82d59220ae0b564882b82d59220ae0)
| _ => (0,0)
def g15 : Forest:=⟨15,3,s15,x2,zj⟩
def g15L15 : PT:=(1,0,1,1,fun _ => 0xf)
def zk : Nat→ PT
| 15 => g15L15
| _ => ePT
def g15Ix : Nat→ Nat→ Nat→ Option (Nat × Nat)
| _,_ => fun _ => none
abbrev bg15:=blockG g15 zk g15Ix (vn g15)
abbrev bm15 (k tm s a b:Nat) := @blockG_merge g15 zk g15Ix (vn g15) k tm s a b
set_option maxHeartbeats 0 in
lemma zl : bg15 3 3 0 1=true:=chunkBlockG (ar:=4) (by decide +kernel)
lemma a15_15 : bg15 3 3 0 1=true:=zl
lemma t15 : ∀ k ≤ 3,∀ tm ≤ 3,bg15 k tm 0 (zk (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq a15_15 rfl rfl rfl
set_option maxHeartbeats 0 in
lemma geom15 : graphValid g15 (boundsBefore [])=true:=by
  simp only [graphValid,Bool.and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,by decide +kernel⟩,by decide +kernel⟩
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma low15 : j3 (vars 15) (graphGoal 15) 4 :=
  jr (g:=g15) (i:=0) (hints:=8449) (before_sound [] tq) geom15 (fun _ => rfl) t15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat):=[(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def rv:=g1 [] 4 maps15
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma xd : kv rv:=gw tq low15 (by decide +kernel)
def x3 : IndexTree ColumnInfo:=(.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def w9 : Array (List Nat):=Array.mk [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def s31 : Nat→ Bits × Bits
| 0 => (r6 0xfd10fb39878078e38ee3ff1dfa21f673,r6 0x901093290e18e0c20882461120212652)
| 1 => (r6 0xff63243f8007ff03f0fc77e1fec6487f,r6 0x48622414b0a61e01c050218090c44829)
| 2 => (r6 0x1e83c7ce007f87fc00ff87fe3d078f9c,r6 0x481c28a4351a1b000a9044809038514)
| 3 => (r6 0xe0fc07f0787807ffff0007ffc1f80fe0,r6 0x205805702c2a4c4b2400032440b00ae0)
| 4 => (r6 0xfff8007f8007fffffff80001fff000,r6 0xa7680051c5132492649000014ed000)
| _ => (0,0)
def xe : Nat→ Option (List Nat)
| 0 => some [gx,kc,gy,gz,h6]
| 1 => some [gx,h6,gz,gy,kc]
| 2 => some [kc,gx,h6,gz,gy]
| 3 => some [kc,gy,gz,h6,gx]
| 4 => some [gy,kc,gx,h6,gz]
| 5 => some [gy,gz,h6,gx,kc]
| 6 => some [gz,gy,kc,gx,h6]
| 7 => some [gz,h6,gx,kc,gy]
| 8 => some [h6,gx,kc,gy,gz]
| 9 => some [h6,gz,gy,kc,gx]
| _ => none
lemma zn : ∀ p,xe p=(w9[p]?).map (fun perm => ((vars 31).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat) :=
  rot_at_of (na:=10) (by decide +kernel) (fun p hp => by unfold xe;match p with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => omega | _+10 => rfl) rfl
def g31 : Forest:=⟨31,6,s31,x3,w9⟩
def g31L20 : PT:=(2,1,3,1,fun _ => 0xcfe27f88)
def g31L23 : PT:=(1,1,3,1,fun _ => 0x4be00)
def g31L27 : PT:=(1,0,3,3,fun _ => 0x14e51f)
def zo:=lw0 5 15 4 6 2 4 (fun _ => 0x930010209408215c04235540204)
def sy:=lw0 1 11 4 5 1 4 (fun _ => 0x48c084200a0300)
def zr : Nat→ PT
| 20 => g31L20
| 23 => g31L23
| 27 => g31L27
| _ => ePT
def g31Ix : Nat→ Nat→ Nat→ Option (Nat × Nat)
| 27,0 => zo
| 27,1 => sy
| 27,2 => sy
| 27,3 => sy
| _,_ => fun _ => none
abbrev x4:=blockG g31 zr g31Ix xe
abbrev bm31 (k tm s a b:Nat) := @blockG_merge g31 zr g31Ix xe k tm s a b
set_option maxHeartbeats 0 in
lemma zt : x4 5 0 0 2=true:=chunkBlockG (ar:=6) (by decide +kernel)
lemma a31_20 : x4 5 0 0 2=true:=zt
set_option maxHeartbeats 0 in
lemma zu : x4 5 3 0 1=true:=chunkBlockG (ar:=5) (by decide +kernel)
lemma a31_23 : x4 5 3 0 1=true:=zu
set_option maxHeartbeats 0 in
lemma zv : x4 6 3 0 1=true:=chunkBlockG (ar:=5) (by decide +kernel)
lemma a31_27 : x4 6 3 0 1=true:=zv
lemma t31 : ∀ k ≤ 6,∀ tm ≤ 3,x4 k tm 0 (zr (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq a31_20 rfl rfl rfl | exact blockG_eq a31_23 rfl rfl rfl | exact blockG_eq a31_27 rfl rfl rfl
set_option maxHeartbeats 0 in
lemma geom31 : graphValid g31 (boundsBefore rv)=true:=by
  simp only [graphValid,Bool.and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma low31 : j3 (vars 31) (graphGoal 31) 7 :=
  jr (g:=g31) (i:=0) (hints:=8449) (before_sound rv xd) geom31 zn t31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat):=[(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def xf:=g1 rv 7 maps31
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma c5 : kv xf:=gw xd low31 (by decide +kernel)
def maps47 : List (Nat × List Nat):=[(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def xg:=g1 xf 5 maps47
set_option maxHeartbeats 0 in
lemma c6 : kv xg:=k5 (m:=47) (cap:=4) (ci:=(8,0,39,0,4)) (hints:=8449) c5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat):=[(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def xh:=g1 xg 5 maps55
set_option maxHeartbeats 0 in
lemma c7 : kv xh:=k5 (m:=55) (cap:=4) (ci:=(16,0,39,0,4)) (hints:=257) c6 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat):=[(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def rx:=g1 xh 8 maps63
set_option maxHeartbeats 0 in
lemma xi : kv rx:=k5 (m:=63) (cap:=7) (ci:=(32,0,31,0,7)) (hints:=8449) c7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def wa : IndexTree ColumnInfo:=(.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def xz : Array (List Nat):=Array.mk [[],[83,32]]
def s111 : Nat→ Bits × Bits
| 0 => (r6 0x4217c4d939d9b59bde7c36792839f673,r6 0x52024891291125101a30245928112652)
| 1 => (r6 0x8f8c07e1ce663fe36fbcc981ff26487f,r6 0x1348660846402424100810085244829)
| 2 => (r6 0x34687b3e0f87c67c73db0e1e31c78f9c,r6 0xf648611c0a800020220a0e1430838514)
| 3 => (r6 0x38707c3ff007f87f83e3f01fc1f80fe0,r6 0x9b61e23f007d05b00c1f00bc1780ae0)
| 5 => (r6 0xc07f803ffff8007ffc03ffe001fff000,r6 0xac7db5685440002dc403dba001eed000)
| 6 => (r6 0xff80003fffffff800003fffffe000000,r6 0xfec9409f0b8abc8000037eff7a000000)
| _ => (0,0)
def y0 : Forest:=⟨111,6,s111,wa,xz⟩
def c8 : PT:=(1,0,2,2,fun _ => 0x933f)
def x5 : Nat→ PT
| 27 => c8
| _ => ePT
def zw : Nat→ Nat→ Nat→ Option (Nat × Nat)
| _,_ => fun _ => none
abbrev zx:=blockG y0 x5 zw (vn y0)
abbrev bm111 (k tm s a b:Nat) := @blockG_merge y0 x5 zw (vn y0) k tm s a b
set_option maxHeartbeats 0 in
lemma y3 : zx 6 3 0 1=true:=chunkBlockG (ar:=6) (by decide +kernel)
lemma c9 : zx 6 3 0 1=true:=y3
lemma t111 : ∀ k ≤ 6,∀ tm ≤ 3,zx k tm 0 (x5 (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq c9 rfl rfl rfl
set_option maxHeartbeats 0 in
lemma e0 : graphValid y0 (boundsBefore rx)=true:=by
  simp only [graphValid,Bool.and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,by decide +kernel⟩,by decide +kernel⟩
set_option maxHeartbeats 0 in
lemma low111 : j3 (vars 111) (graphGoal 111) 7 :=
  jr (g:=y0) (i:=0) (hints:=16785665) (before_sound rx xi) e0 (fun _ => rfl) t111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def e2 : List (Nat × List Nat):=[(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def wb:=g1 rx 7 e2
set_option maxHeartbeats 0 in
lemma zy : kv wb:=gw xi low111 (by decide +kernel)
def e3 : List (Nat × List Nat):=[(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def qh:=g1 wb 6 e3
set_option maxHeartbeats 0 in
lemma wc : kv qh:=k5 (m:=119) (cap:=5) (ci:=(4,0,115,0,5)) (hints:=16777473) zy (by decide +kernel) (by decide +kernel) (by decide +kernel)
def wd : IndexTree ColumnInfo:=(.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def tt : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def s189 : Nat→ Bits × Bits
| 0 => (r6 0x1c3c16b689b913efae1121d833f4fc,r6 0xc987504a4093801450011215802a4ac)
| 2 => (r6 0x87a20798c731dfe277cb82067f2cc8cf,r6 0x92ea119006201542018a82041528c8ca)
| 3 => (r6 0xc63c7e0f83e1e7c79f31c3861cf0f0f,r6 0x2c054640d004001878601c3060870605)
| 4 => (r6 0x843f8ff003fe07f81fce03f81f00ff0,r6 0xc16288ba0030c0200080e00e81700950)
| 5 => (r6 0xf07c00ffffc0007ffe00ffc001fff000,r6 0xf26608f94b800076a200ca8001fd5000)
| 7 => (r6 0xff8000ffffffff800000fffffe000000,r6 0xd11a606b01b8a000000357bea000000)
| _ => (0,0)
def vo : Nat→ Option (List Nat)
| 0 => some [gx,gy,gz,h6,jw,kx]
| 1 => some [gx,gy,kx,jw,h6,gz]
| 2 => some [gy,gx,h6,gz,kx,jw]
| 3 => some [gy,gx,jw,kx,gz,h6]
| 4 => some [gz,jw,gx,h6,gy,kx]
| 5 => some [gz,jw,kx,gy,h6,gx]
| 6 => some [h6,kx,gy,gz,gx,jw]
| 7 => some [h6,kx,jw,gx,gz,gy]
| 8 => some [jw,gz,gy,kx,gx,h6]
| 9 => some [jw,gz,h6,gx,kx,gy]
| 10 => some [kx,h6,gx,jw,gy,gz]
| 11 => some [kx,h6,gz,gy,jw,gx]
| _ => none
lemma y4 : ∀ p,vo p=(tt[p]?).map (fun perm => ((vars 189).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat) :=
  rot_at_of (na:=12) (by decide +kernel) (fun p hp => by unfold vo;match p with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => omega | _+12 => rfl) rfl
def e4 : Forest:=⟨189,7,s189,wd,tt⟩
def e5 : PT:=(2,1,4,1,fun _ => 0x93fc4ff88)
def e6 : PT:=(1,1,4,1,fun _ => 0xf7e00)
def e7 : PT:=(1,0,4,3,fun _ => 0x513647c3f)
def y5:=lw0 2 15 4 6 2 4 (fun _ => 0x208960274114240d08201501)
def r4:=lw0 1 11 4 5 1 4 (fun _ => 0x50280c0200902c0)
def x6 : Nat→ PT
| 24 => e5
| 27 => e6
| 31 => e7
| _ => ePT
def zz : Nat→ Nat→ Nat→ Option (Nat × Nat)
| 31,0 => y5
| 31,1 => r4
| 31,2 => r4
| 31,3 => r4
| _,_ => fun _ => none
abbrev t0:=blockG e4 x6 zz vo
abbrev bm189 (k tm s a b:Nat) := @blockG_merge e4 x6 zz vo k tm s a b
set_option maxHeartbeats 0 in
lemma y6 : t0 6 0 0 2=true:=chunkBlockG (ar:=7) (by decide +kernel)
lemma e8 : t0 6 0 0 2=true:=y6
set_option maxHeartbeats 0 in
lemma y7 : t0 6 3 0 1=true:=chunkBlockG (ar:=6) (by decide +kernel)
lemma e9 : t0 6 3 0 1=true:=y7
set_option maxHeartbeats 0 in
lemma y8 : t0 7 3 0 1=true:=chunkBlockG (ar:=6) (by decide +kernel)
lemma a189_31 : t0 7 3 0 1=true:=y8
lemma t189 : ∀ k ≤ 7,∀ tm ≤ 3,t0 k tm 0 (x6 (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq e8 rfl rfl rfl | exact blockG_eq e9 rfl rfl rfl | exact blockG_eq a189_31 rfl rfl rfl
set_option maxHeartbeats 0 in
lemma geom189 : graphValid e4 (boundsBefore qh)=true:=by
  simp only [graphValid,Bool.and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces];repeat' apply And.intro;all_goals decide +kernel
set_option maxHeartbeats 0 in
lemma low189 : j3 (vars 189) (graphGoal 189) 8 :=
  jr (g:=e4) (i:=0) (hints:=536879876) (before_sound qh wc) geom189 y4 t189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat):=[(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def we:=g1 qh 8 maps189
set_option maxHeartbeats 0 in
lemma a2 : kv we:=gw wc low189 (by decide +kernel)
def maps127 : List (Nat × List Nat):=[(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def qi:=g1 we 9 maps127
set_option maxHeartbeats 0 in
lemma wf : kv qi:=k5 (m:=127) (cap:=8) (ci:=(32,0,95,0,8)) (hints:=16785665) a2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def wg : IndexTree ColumnInfo:=(.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def tu : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def s191 : Nat→ Bits × Bits
| 0 => (r6 0xca0e419f380821075b301c73e21f673,r6 0x300400100082102532000224212652)
| 1 => (r6 0x84fe92ba0cb30c6249c366a4c8c6487f,r6 0xfcce82a804330c6248c164a488c44829)
| 2 => (r6 0x32542be2b54010038e7c8738f1078f9c,r6 0x2102000304010010028831071038514)
| 3 => (r6 0x2368ccccd903e07c0f80f83f01f80fe0,r6 0xa068c484c903e0580f80502f00b00ae0)
| 4 => (r6 0xb8f0f0f1e7c007ff000ffc001fff000,r6 0xf86080b007c0027d000afc0014ed000)
| 5 => (r6 0xcc0ff00fe07fff800000fffffe000000,r6 0x8fc1200a806a59000000fffdda000000)
| 7 => (r6 0xf00ffff0007fffffffff000000000000,r6 0x702cdb500015a6feffd7000000000000)
| _ => (0,0)
def vp : Nat→ Option (List Nat)
| 0 => some [gx,kc,gy,gz,h6,jw,kx]
| 1 => some [gx,kc,gy,kx,jw,h6,gz]
| 2 => some [gy,kc,gx,h6,gz,kx,jw]
| 3 => some [gy,kc,gx,jw,kx,gz,h6]
| _ => none
lemma y9 : ∀ p,vp p=(tu[p]?).map (fun perm => ((vars 191).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat) :=
  rot_at_of (na:=4) (by decide +kernel) (fun p hp => by unfold vp;match p with | 0 | 1 | 2 | 3 => omega | _+4 => rfl) rfl
def g191 : Forest:=⟨191,10,s191,wg,tu⟩
def g191L24 : PT:=(3,4,6,1,fun _ => 0x15eacc222446fc56844488c7d09338901)
def g191L28 : PT:=(17,3,6,5,fun _ => 0x1c118721ed51143c26cf0b09414140985c260e8c20e5a508314a5294a4102fda507899fccc0803ed988f8eede5e6a2ff5938c8bdf6809a277d072689fea522e27fc268b89df6941e267fa50789fea962447fa0889119fc227e237da38f88fea422623fc8f8988)
def ya:=lw0 3 9 4 4 2 2 (fun _ => 0x303332313000)
def g191L31 : PT:=(18,3,6,4,fun _ => 0x170a08c4a0e118944a2599984322111000000009bea01e2e7da50789fe0b624477a9e8911be8222447f28911039f4ce2407f8891101ed4180c07d5050301bbaa09c03ce050400ed8180c03d6050300fc80c0803ec040100fd00c0403f8020100)
def yb:=lw0 1 2 2 4 2 2 (fun _ => 0xc)
def g191L32 : PT:=(32,2,6,7,fun _ => 0x1212af928e0b89869147898a09c7af92118e0a47c78991afc789c7898a20a7c0818f0a0e8a408d0b20a78504a78740a7890e91868b870f128d1189a78a278b880807408b918f05098389110511cd952234482f1cb666c57294a9109f3868c172a4c9901a2c4870a0c080ffccc77fe623bff271dff928effccc5ffe522fff3117ff938bffcbc5ffe4a2fff4113ff9a89ffcac4ffe7a27ff1913ff8e89ffc5c4ffc1e27ff2d11ffa088ffcd447fe5623ff3f11ff9088ffc6c47fe2e23ff1311ff9a00ffc6807fe3003ff1401ff0200)
def yc:=lw0 4 19 5 7 5 2 (fun _ => 0x2480d0214711224460a170110f224421100180)
def g191L35 : PT:=(69,2,6,8,fun _ => 0x3c4a3447024406284a284626be4a0b1f1e2014144000463e26001c02262426383e164a1e38281ebe48002800281e260002291e28261e0248281dbe14821e9e0628063828263a46342428264a142e1c261e3e2828264a40341e1c26284b021c0648242ebe4a4abe4a472a4abe473e824b3e4a47373e9f3e4b373e9f3e833e4646463ebe4a463b369f3e9f2a833e9f2a4a064a262e28471ebf1ebf369f3e9f369f3ebf3ebf494541373329231f170f0b02fcf2eee4ded6cec6b8b4aca8a2989288827e7a787674706e6a68666462605c5a5856524e4c4a484642403e3c3834302c2a281c1814100c0804017f079abf83cadfe8e32ff4519fd938cbf83c65fe8a3bdf2d1def8f8ebf83c75fe8e2eff4517f79a8bfbcac5fde322efe0f177fa089fe9344ffa2e26fe0f137fa011bfcf08dfe8622ff41117f9f88fec7c47fa2622fe0f11f79903fbca01fde600fef2607f78a03fbcb81fde480fef1207f71103fbc401ff66807fb2a03fd8e01fec580ff62407fa2203fe8e00ff45807fa2403fd1001ef0400fb81807f40403fd2c01fe9a00ff4a807f89c03fd2001fe8d00ff47807fa3003fd1401fe0200fd4488edc180fae0a07f50301f702007d80c03f40401fc0100)
def yd:=lw0 10 34 6 7 5 2 (fun _ => 0x15ae102c11108243030b2e122d63742150450110247611183800a9c1e4410c00860036d1200)
def r5:=lw0 11 38 6 7 5 2 (fun _ => 0x18c90f862c1c2259090a43b084c24302a412447124648907051910d02b0308089c10040400840c0181)
def g191L39 : PT:=(12,1,6,7,fun _ => 0xf010704e8f3e00083828c48f3e0019f2806f8a1e0419f277c70f064c09f8252f8f003c09f820e7df4a00b9426881831c3cfdf033cb81063cf932e49180837c7cfbe04fc1013efd29509d33568ce141620280ff9aff95ff8cff8eff8bff89ff11ff88ff00f703fd01fe00)
def ye:=lw0 14 82 7 8 6 2 (fun _ => 0x214544e0480824004623c6d64800f3c2480348064754c7c2c80191c5e5482447a35422360808081588044011933561c480a503178295438501c3f402083281145210c8058684109288017453f748080736e0c2814c00a80280000001100c0)
def r7:=lw0 36 159 8 9 7 2 (fun _ => 0x2808a21081148a9c464f4449d0c1163d2e22e9c7530100393607416d08aa64590048b4050cc18b014cf2548d11910720d1891623b707cad14140f49218b8d01161aab0e0d00d210da7c822f22cf8322e4263c76a11502e381d47917720949e707001130f6171b040008a37d42b40436cd8548a131689f4a17419148a1621ec85032de8455c429961130b21fc0e0920848b228040189461001e1162c94890f88ab90d0ac0b084be9145340f84947b01a9148ba1610300021215010339011124031c0e031107110c1b000c260651000600292b0b02010f00)
def g191L43 : PT:=(1,0,6,2,fun _ => 0x9efe7f)
def r8:=lw0 10 41 6 6 4 2 (fun _ => 0xc64c1c120660cca4a42822305acb31200c283309e77e0c8cc5e711a32830c001180044040100)
def x7 : Nat→ PT
| 24 => g191L24
| 28 => g191L28
| 31 => g191L31
| 32 => g191L32
| 35 => g191L35
| 39 => g191L39
| 43 => g191L43
| _ => ePT
def a3 : Nat→ Nat→ Nat→ Option (Nat × Nat)
| 28,0 => ya
| 31,0 => yb
| 32,0 => yc
| 35,0 => yd
| 35,1 => r5
| 35,2 => r5
| 35,3 => r5
| 39,0 => ye
| 39,1 => r7
| 39,2 => r7
| 39,3 => r7
| 43,1 => r8
| 43,2 => r8
| 43,3 => r8
| _,_ => fun _ => none
abbrev ld:=blockG g191 x7 a3 vp
abbrev bm191 (k tm s a b:Nat) := @blockG_merge g191 x7 a3 vp k tm s a b
set_option maxHeartbeats 0 in
lemma yf : ld 6 0 0 3=true:=chunkBlockG (ar:=7) (by decide +kernel)
lemma a191_24 : ld 6 0 0 3=true:=yf
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma yg : ld 7 0 0 17=true:=by apply cellsBlockG (ar:=8) (d:=1);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma a191_28 : ld 7 0 0 17=true:=yg
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma yh : ld 7 3 0 18=true:=by apply cellsBlockG (ar:=7) (d:=1);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma a191_31 : ld 7 3 0 18=true:=yh
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma yi : ld 8 0 0 32=true:=by apply cellsBlockG (ar:=9) (d:=2);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma a191_32 : ld 8 0 0 32=true:=yi
set_option maxHeartbeats 0 in
lemma yj : ld 8 3 0 8=true:=chunkBlockG (ar:=7) (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma yk : ld 8 3 8 61=true:=by apply cellsBlockG (ar:=8) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma a191_35 : ld 8 3 0 69=true:=(bm191 8 3 0 8 61 yj yk)
set_option maxHeartbeats 0 in
lemma yl : ld 9 3 0 3=true:=chunkBlockG (ar:=7) (by decide +kernel)
set_option maxHeartbeats 0 in
lemma ym : ld 9 3 3 9=true:=chunkBlockG (ar:=8) (by decide +kernel)
lemma a191_39 : ld 9 3 0 12=true:=(bm191 9 3 0 3 9 yl ym)
set_option maxHeartbeats 0 in
lemma yn : ld 10 3 0 1=true:=chunkBlockG (ar:=7) (by decide +kernel)
lemma a191_43 : ld 10 3 0 1=true:=yn
lemma t191 : ∀ k ≤ 10,∀ tm ≤ 3,ld k tm 0 (x7 (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq a191_24 rfl rfl rfl | exact blockG_eq a191_28 rfl rfl rfl | exact blockG_eq a191_31 rfl rfl rfl | exact blockG_eq a191_32 rfl rfl rfl | exact blockG_eq a191_35 rfl rfl rfl | exact blockG_eq a191_39 rfl rfl rfl | exact blockG_eq a191_43 rfl rfl rfl
set_option maxHeartbeats 0 in
lemma geom191 : graphValid g191 (boundsBefore qi)=true:=by
  simp only [graphValid,Bool.and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces];repeat' apply And.intro;all_goals decide +kernel
set_option maxHeartbeats 0 in
lemma low191 : j3 (vars 191) (graphGoal 191) 11 :=
  jr (g:=g191) (i:=0) (hints:=536879361) (before_sound qi wf) geom191 y9 t191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat):=[(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def wh:=g1 qi 11 maps191
set_option maxHeartbeats 0 in
lemma a4 : kv wh:=gw wf low191 (by decide +kernel)
def maps251 : List (Nat × List Nat):=[(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def wi:=g1 wh 8 maps251
set_option maxHeartbeats 0 in
lemma a5 : kv wi:=k5 (m:=251) (cap:=7) (ci:=(8,0,243,0,7)) (hints:=1358970881) a4 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat):=[(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def qj:=g1 wi 12 maps255
set_option maxHeartbeats 0 in
lemma wj : kv qj:=k5 (m:=255) (cap:=11) (ci:=(64,0,191,0,11)) (hints:=553656577) a5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def wk : IndexTree ColumnInfo:=(.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def tv : Array (List Nat):=Array.mk [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
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
def vq : Nat→ Option (List Nat)
| 0 => some [gx,kc,gy,gz,h6,jw,ml,mm]
| 1 => some [gx,kc,ml,mm,jw,h6,gy,gz]
| 2 => some [kc,gx,h6,gz,gy,ml,jw,mm]
| 3 => some [kc,gx,jw,mm,ml,gy,h6,gz]
| 4 => some [gz,mm,jw,gx,h6,gy,ml,kc]
| 5 => some [gz,mm,ml,kc,gy,h6,jw,gx]
| 6 => some [mm,gz,gy,kc,ml,jw,h6,gx]
| 7 => some [mm,gz,h6,gx,jw,ml,gy,kc]
| _ => none
lemma yo : ∀ p,vq p=(tv[p]?).map (fun perm => ((vars 383).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat) :=
  rot_at_of (na:=8) (by decide +kernel) (fun p hp => by unfold vq;match p with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _+8 => rfl) rfl
def g383 : Forest:=⟨383,12,s383,wk,tv⟩
def g383L31 : PT:=(6,5,6,3,fun _ => 0x180350640181cd64802ce89f3d193b17a74bd9e268b13c735edc84c589e9d2f680a220422ed90154050011f4c80a8c1400)
def g383L32 : PT:=(5,4,6,2,fun _ => 0x1e30c839d54cef9eb0088bafb0aa0a610bfcbc378810bfc0aa08810df5b38c1400)
def g383L35 : PT:=(49,4,6,6,fun _ => 0x1d0c81d09c7a47c30058e80c4310c426f40160c8323e8390c80f0e40f0e43909c3935c380e4160a5280c9ba0c917f8c1a47c2447d28ae99e79a58e181e75c6da6996175d65544d245038d30b28a28a2892482071c71c71c71c70c09f6468c9d8bf749e8c9d8bcafaab02613cb7aaaf2613bd6ba358b13df4ad358b13af6bd268b13be6b9268b13f749e268b13af6bd098b13be6b9098b13cf6bd098b13de6b9098b138fbb709a788c77b33ba710ad7ba3ba710af3b73ba710cf6a7ac28108fbbe28a610adbba28a610aebb928a610af9b628a610afab528a610df4af3788109fcbe288810afcbd288810f74a0288810bf8b7288810afcbd098810cfcbd0988108efb93c03009de0ab12f00b760aa028009fc0aad28009fab7098c009de0ab11400df4b38c1400bf40a8c14009eeb93c0300be6b93c0300be6b9350300be6b9260300f749e260300bdcba2f0100f74a0280100bf8b7280100f74070301008f6bd098b138fcbd098810)
def r9:=lw0 2 17 5 6 3 3 (fun _ => 0xe041b10851860c60013501a11803)
def g383L36 : PT:=(9,3,6,5,fun _ => 0x180487235718d4643517aa0f426160b860311a8d4627a0e8d42979c1cb4988205ffb32d8bdff3c11177feccbe23fbc650446ffa00888bfe1340217fc268003fbd046005ffb31400)
def yp:=lw0 2 11 4 6 3 3 (fun _ => 0x584b0c44c101b1420a)
def g383L39 : PT:=(102,3,6,9,fun _ => 0x24160e86029c7ec85871d91a25c3a1d180503e161805860140b0c12a24130281e27098a06a241c8d448351d09c747a1784c62681a25cd0340b819f4181a875d0131205860228b89c3ae818c5c3016190a43a302a8742e3a0c0bc38311305c7418180d84c0f19099f418194a068300788470181a0987418109e874251a03c3a571c84c1efa8fca01f1f1c021ae127d0284d1f078e438d713c7e50fa1035c7006130a43a2f106a074161d0c75016078e82c321d03c68341002828050b01412265b87e3e421695d34161827c34651309c482f138c66e3a191a3c6b73478d74653d15d74e33b8c974322ba68ae9f7195cd06832a7d3e650bf678e30f18741d638d45fc7d98b896511f12ca23fe32b8e8f4571d1e8ae3a3d15c74573d0a0d057ec95c5068e3f43b3e392c68d1098341200fc7cbd9e8f2783b5d6e872b85bada6bb4d9ec96330d7ebd5d2d966b0572ad50a651a7d329648a391286401f0f476399bcd86833190c4602f974b6592b150a250279389a4c259249046229087c3d1e0ec763a1c8e06e361a8d06633190c4622f178a04a220f87034170a0441c0b03802efd896c5efda52d8b9fe793d17fd8de762ffb464ec5defb0088bddf6011173feb4222f7f4e8445ebfadaa139fe134a273fed2784f5fd54f09efda59e139ff684c277bec0984efbd79309ff6ad8b13fec6b1627fda7a2c4ffb134589ff6098b139fe134f11bde9cbe227fda50444ff3ca0889ff6917113febc22227f84d3886f7b3a710dee774e21bdc269c427fda50086f7a7a0109ff6850217fab0a0437dd053086fb28a610ff95f1021ff0de2043fe5044087fc288810ff81310213fcf28002f7d81400777a02800bf75c50017f6b4a002ff5614004ff3c8c00bbf622801fd6305002ff560a005feb38b00fed1916017fabe20027f9e01807f68b03009fe780201ff2200402ff5997805fead2f00bfc7940017f8268002ff5694005feaf2d00bfc7918017face3003fb17c6007f6a08c00ff93d18017f8263002ff598a005fe3c0300fed400601fda300c03fb1e01807f6350300fec5a0601fda780c03fb1301805fe3c0100ff9180201fd80c0403fe1e00807fc2f0100ff9400201ff0a00403fe0180804efb0088b97e1354277d8262c4e7b84d3885fc098810bbd625e017bac0a003bb5014005faae2800bf95a500177ac45003fa460a007f4030100)
def yq:=lw0 1 11 4 6 3 3 (fun _ => 0x50401451431050850)
def ra:=lw0 29 110 7 9 6 3 (fun _ => 0x3118f204bcd018ad1c31169780c311897c62124d8c53c192d0b0521d18c5c8631060703e1a150c5d409518502a220b378201e0b9551631468c448e905f386020c7b0d6046098346390029c062080881c620a1383d2a02188a05e21118c48e1b4f861aaa0134290795188c46204070c463cb00c40015c1746062db50840e2160100555831404603022428004040053000081000411c)
def g383L43 : PT:=(43,2,6,9,fun _ => 0x3405da0c0807c49a3645850a0c2418c58e4771cd7649f40cb8f1e35a0dc745c7c805f40c0685850925c5cd49ce8bde84d5c7cb5e8a2a080d4715c989de8d67d5ea0bf671c9b40838cc875dedc5ca07c80a09098815de8c8ac7ca27ea0eaa1e8589d5dea978f1da0bc7e7c9d5ce869eaa0d0595c2ae850d0205c9c9469a0587492a1967d5ee85de85892699494749cd45f1c74eb43678cc080a092545cea471f438f64c05070e89f8c5c7c778ce8c85f1f43649c60a0927e945ce89b43678f1c809ce8c87ca1eb1f8c5da07f1f8d5c09dc7f8c7d5ce95deb43678da07f1ce87de95c7da0a1351dcf65a07f438f1ca06b6555a28d967f678de95c967f436555cda0907c5c5f8c7c7ca07ca0a07e8d8f43655f8f1e7ca07f43671f8da27e391788c0df6f5783b1cae169b3190c05e2c954a24ea511c843c1c8d05b2b94496481f8ec722f1508c38190b050241004003ffa58bffcb62fff9e8bffe762fff088bffe784fff2613ffe9e23ff2f88ffe8223ff8b88ffc2223ffa010ffca043ffa000ffca003ff8c00ffc5003ff0300ffc0403fe9d8bbfc222effa513bfe9e22ff0888bfe9c43fe8b00ffa2003fe2f00ffa8003fe2800ff8b403fe8c00ff85003fe0300ff80402bfaa13fda2c4ef7a710bee9843fc8810fd80c03fc0100)
def yr:=lw0 5 19 5 7 4 3 (fun _ => 0x38440f8818912084b78414484101800186a01c00)
def rb:=lw0 66 207 8 10 7 3 (fun _ => 0x3980e03d1982b586050094201ce10ab030141586cb7b885f12d1e1089211381094dd0402debe420206617432191d28c05b0a4140a0b9c984c8e338305d1c97b3405c0048662fd1f19a5d04460210261883a89b9d70493199141424b058249704ee68551503107254443b214c390fc0316435125d64c60015c63118a40b836c8801201130240603b0494ce2198202586126c662b83307e3c0002706e18030511352e2422f4cc97064400de3d10430068130280f128be07843e482390286b005850017012171174297b823102f1581d4c82232a5811d90178488700d237401942c8489502f050ec66504c04083c06066e6eb9cdc52f005c0d03e16b9e13c86084668d736010001080200010105021300001f5f000301020b56181a1e080b980e001e0800001803002f0c2c04050c04149d0c11000041151e05080219000051090c0000285902)
def g383L47 : PT:=(6,1,6,6,fun _ => 0x1410747e3d0c764be33e5cbbaa1671c73ea0fa82ee9447c67d1d0b31f19f89958e30603ff17ff13ffc47fc43fe01fe00)
def rc:=lw0 47 108 7 9 6 3 (fun _ => 0x2b8e49c4e018db95860c020248603059040c00cd8a82e99ce18853138a26894120c08bb22b158ac3e2b101401c58158171bda05126530d8b47b18510b4a83a158623c564e15844568a7072437080ca240e020f09443c83021d060807f2a20a02d098882b240a0562b0e09056132c88c1a53900ac202b31868283800906004800400000001c18000005000404000080000d1250002242420200084ac00005010214002)
def g383L51 : PT:=(1,0,6,3,fun _ => 0x74198e0ff)
def rd:=lw0 10 38 6 6 3 3 (fun _ => 0x186504821c6344235d0061861460e2401c1518c19c186186186186186000040080108000)
def x8 : Nat→ PT
| 31 => g383L31
| 32 => g383L32
| 35 => g383L35
| 36 => g383L36
| 39 => g383L39
| 43 => g383L43
| 47 => g383L47
| 51 => g383L51
| _ => ePT
def a6 : Nat→ Nat→ Nat→ Option (Nat × Nat)
| 35,1 => r9
| 35,2 => r9
| 35,3 => r9
| 36,0 => yp
| 39,0 => yq
| 39,1 => ra
| 39,2 => ra
| 39,3 => ra
| 43,0 => yr
| 43,1 => rb
| 43,2 => rb
| 43,3 => rb
| 47,1 => rc
| 47,2 => rc
| 47,3 => rc
| 51,1 => rd
| 51,2 => rd
| 51,3 => rd
| _,_ => fun _ => none
abbrev kd:=blockG g383 x8 a6 vq
abbrev wl (k tm s a b:Nat) := @blockG_merge g383 x8 a6 vq k tm s a b
set_option maxHeartbeats 0 in
lemma yt : kd 7 3 0 6=true:=chunkBlockG (ar:=7) (by decide +kernel)
lemma a383_31 : kd 7 3 0 6=true:=yt
set_option maxHeartbeats 0 in
lemma yu : kd 8 0 0 5=true:=chunkBlockG (ar:=9) (by decide +kernel)
lemma a383_32 : kd 8 0 0 5=true:=yu
set_option maxHeartbeats 0 in
lemma yv : kd 8 3 0 2=true:=chunkBlockG (ar:=7) (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma yw : kd 8 3 2 47=true:=by apply cellsBlockG (ar:=8) (d:=2);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma a383_35 : kd 8 3 0 49=true:=(wl 8 3 0 2 47 yv yw)
set_option maxHeartbeats 0 in
lemma yx : kd 9 0 0 9=true:=chunkBlockG (ar:=10) (by decide +kernel)
lemma a383_36 : kd 9 0 0 9=true:=yx
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma yy : kd 9 3 0 13=true:=by apply cellsBlockG (ar:=8) (d:=1);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma x9 : kd 9 3 13 89=true:=by apply cellsBlockG (ar:=9) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma a383_39 : kd 9 3 0 102=true:=(wl 9 3 0 13 89 yy x9)
set_option maxHeartbeats 0 in
lemma yz : kd 10 3 0 7=true:=chunkBlockG (ar:=8) (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma z0 : kd 10 3 7 16=true:=by apply cellsBlockG (ar:=9) (d:=1);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma xa : kd 10 3 23 20=true:=by apply cellsBlockG (ar:=10) (d:=1);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma a383_43 : kd 10 3 0 43=true:=(wl 10 3 0 7 36 yz (wl 10 3 7 16 20 z0 xa))
set_option maxHeartbeats 0 in
lemma z2 : kd 11 3 0 1=true:=chunkBlockG (ar:=8) (by decide +kernel)
set_option maxHeartbeats 0 in
lemma z3 : kd 11 3 1 5=true:=chunkBlockG (ar:=9) (by decide +kernel)
lemma a383_47 : kd 11 3 0 6=true:=(wl 11 3 0 1 5 z2 z3)
set_option maxHeartbeats 0 in
lemma z4 : kd 12 3 0 1=true:=chunkBlockG (ar:=8) (by decide +kernel)
lemma a383_51 : kd 12 3 0 1=true:=z4
lemma t383 : ∀ k ≤ 12,∀ tm ≤ 3,kd k tm 0 (x8 (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq a383_31 rfl rfl rfl | exact blockG_eq a383_32 rfl rfl rfl | exact blockG_eq a383_35 rfl rfl rfl | exact blockG_eq a383_36 rfl rfl rfl | exact blockG_eq a383_39 rfl rfl rfl | exact blockG_eq a383_43 rfl rfl rfl | exact blockG_eq a383_47 rfl rfl rfl | exact blockG_eq a383_51 rfl rfl rfl
set_option maxHeartbeats 0 in
lemma geom383 : graphValid g383 (boundsBefore qj)=true:=by
  simp only [graphValid,Bool.and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces];repeat' apply And.intro;all_goals decide +kernel
set_option maxHeartbeats 0 in
lemma low383 : j3 (vars 383) (graphGoal 383) 13 :=
  jr (g:=g383) (i:=0) (hints:=12901687553) (before_sound qj wj) geom383 yo t383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat):=[(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383:=g1 qj 13 maps383
set_option maxHeartbeats 0 in
lemma valid383 : kv known383:=gw wj low383 (by decide +kernel)
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
def rotN0 : List Nat:=[gx,kc,gy,gz,h6,jw,ml,kx,mm]
def rotN1 : List Nat:=[gx,jw,mm,gz,h6,kc,kx,ml,gy]
def rotN2 : List Nat:=[kc,gx,jw,mm,ml,gy,h6,kx,gz]
def rotN3 : List Nat:=[kc,gy,gz,mm,ml,gx,kx,h6,jw]
def rotN4 : List Nat:=[gy,kc,gx,jw,kx,gz,ml,h6,mm]
def rotN5 : List Nat:=[gy,gz,mm,jw,kx,kc,h6,ml,gx]
def rotN6 : List Nat:=[gz,gy,kc,gx,h6,mm,kx,ml,jw]
def rotN7 : List Nat:=[gz,mm,jw,gx,h6,gy,ml,kx,kc]
def rotN8 : List Nat:=[jw,gx,kc,gy,kx,mm,h6,ml,gz]
def rotN9 : List Nat:=[jw,mm,gz,gy,kx,gx,ml,h6,kc]
def rotN10 : List Nat:=[mm,gz,gy,kc,ml,jw,h6,kx,gx]
def rotN11 : List Nat:=[mm,jw,gx,kc,ml,gz,kx,h6,gy]
def rotDS : Nat→ Option (List Nat)
  | 0 => some rotN0 | 1 => some rotN1 | 2 => some rotN2 | 3 => some rotN3
  | 4 => some rotN4 | 5 => some rotN5 | 6 => some rotN6 | 7 => some rotN7
  | 8 => some rotN8 | 9 => some rotN9 | 10 => some rotN10 | 11 => some rotN11
  | _ => none
lemma rotDS_at : ∀ p,rotDS p=(deadautos[p]?).map (fun perm => ((vars 511).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat) :=
  rot_at_of (na:=12) (by decide +kernel) (fun p hp => by unfold rotDS;match p with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => omega | _+12 => rfl) rfl
def deadcolumns : IndexTree ColumnInfo := (.fork 126 (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(0,1,460,50,8),(0,2,440,69,8),(0,4,369,138,8)]) (.leaf [(0,8,227,276,8),(0,16,486,9,10),(0,32,94,385,8),(0,64,189,258,10)])) (.fork 4 (.leaf [(0,128,347,36,10),(0,256,151,104,8),(1,0,510,0,12),(1,16,486,8,9)]) (.leaf [(2,0,509,0,12),(2,1,460,48,7),(2,4,369,136,7),(2,64,189,256,9)]))) (.fork 8 (.fork 4 (.leaf [(2,128,345,36,7),(4,0,507,0,12),(4,2,440,65,7),(4,8,227,272,7)]) (.leaf [(4,16,482,9,7),(4,128,347,32,9),(5,2,440,64,6),(6,0,505,0,9)])) (.fork 4 (.leaf [(6,16,480,9,6),(6,64,185,256,6),(6,128,345,32,6),(7,0,504,0,7)]) (.leaf [(7,16,480,8,5),(8,0,503,0,12),(8,4,369,130,7),(8,16,486,1,9)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(8,64,181,258,7),(8,128,339,36,7),(8,256,151,96,7),(9,0,486,0,8)]) (.leaf [(9,16,486,0,8),(10,0,501,0,8),(10,4,369,128,6),(10,16,484,1,6)])) (.fork 4 (.leaf [(10,64,181,256,6),(12,0,499,0,9),(12,16,482,1,6),(12,64,177,258,6)]) (.leaf [(12,128,339,32,6),(14,0,497,0,7),(14,16,480,1,5),(15,0,480,0,4)]))) (.fork 8 (.fork 4 (.leaf [(15,16,480,0,4),(16,0,495,0,13),(17,0,494,0,11),(19,0,492,0,8)]) (.leaf [(19,64,172,256,5),(20,8,227,256,6),(21,0,490,0,7),(21,2,424,64,5)])) (.fork 4 (.leaf [(21,128,330,32,5),(24,0,487,0,11),(25,0,486,0,8),(27,0,484,0,5)]) (.leaf [(29,0,482,0,5),(31,0,480,0,4),(32,0,479,0,12),(32,1,460,18,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(32,128,347,4,9),(32,256,151,72,7),(33,0,478,0,9)]) (.leaf [(34,1,460,16,6),(34,128,345,4,6),(35,0,476,0,7),(35,64,156,256,5)])) (.fork 4 (.leaf [(36,0,347,0,8),(36,128,347,0,8),(38,128,345,0,5),(40,0,471,0,8)]) (.leaf [(40,16,454,1,6),(40,128,339,4,6),(40,256,151,64,6),(41,16,454,0,5)]))) (.fork 8 (.fork 4 (.leaf [(44,128,339,0,5),(49,0,462,0,8),(50,1,460,0,5),(51,0,460,0,5)]) (.leaf [(53,128,330,0,4),(56,256,135,64,5),(64,0,447,0,13),(64,1,396,50,7)])) (.fork 4 (.leaf [(64,2,440,5,7),(64,8,163,276,7),(64,32,30,385,7),(64,256,151,40,7)]) (.leaf [(66,0,445,0,11),(66,1,396,48,6),(66,4,305,136,6),(68,2,440,1,6)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(68,8,163,272,6),(69,2,440,0,5),(70,0,441,0,8),(72,4,305,130,6)]) (.leaf [(72,16,422,1,6),(72,256,151,32,6),(74,0,437,0,7),(74,4,305,128,5)])) (.fork 4 (.leaf [(78,0,433,0,5),(80,0,431,0,11),(81,0,430,0,8),(81,2,424,4,5)]) (.leaf [(83,0,428,0,7),(84,8,163,256,5),(85,2,424,0,4),(87,0,424,0,4)]))) (.fork 8 (.fork 4 (.leaf [(89,0,422,0,5),(96,0,415,0,9),(96,1,396,18,6),(96,256,151,8,6)]) (.leaf [(98,0,413,0,7),(98,1,396,16,5),(98,128,281,4,5),(102,128,281,0,4)])) (.fork 4 (.leaf [(104,256,151,0,5),(112,1,396,2,5),(113,0,398,0,5),(114,1,396,0,4)]) (.leaf [(115,0,396,0,4),(120,256,135,0,4),(128,0,383,0,13),(128,1,332,50,7)])))))) (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(128,2,312,69,7),(128,4,369,10,7),(128,32,94,257,7)]) (.leaf [(130,0,381,0,9),(130,1,332,48,6),(130,4,369,8,6),(130,64,61,256,6)])) (.fork 4 (.leaf [(132,0,379,0,11),(132,2,312,65,6),(132,8,99,272,6),(132,16,354,9,6)]) (.leaf [(134,0,377,0,8),(134,64,57,256,5),(136,0,375,0,9),(136,4,369,2,6)]))) (.fork 8 (.fork 4 (.leaf [(136,16,358,1,6),(136,256,23,96,6),(138,4,369,0,5),(140,0,371,0,8)]) (.leaf [(140,16,354,1,5),(141,16,354,0,4),(144,0,367,0,11),(145,0,366,0,8)])) (.fork 4 (.leaf [(147,0,364,0,5),(153,0,358,0,5),(154,4,353,0,4),(156,0,355,0,7)]) (.leaf [(157,0,354,0,4),(160,0,351,0,11),(160,1,332,18,6),(160,64,29,258,6)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(160,256,23,72,6),(161,16,326,8,5),(162,0,349,0,7),(162,1,332,16,5)]) (.leaf [(162,64,29,256,5),(164,0,347,0,8),(168,16,326,1,5),(169,16,326,0,4)])) (.fork 4 (.leaf [(172,0,339,0,5),(177,0,334,0,7),(178,1,332,0,4),(179,0,332,0,4)]) (.leaf [(192,0,319,0,11),(192,2,312,5,6),(192,4,305,10,6),(193,2,312,4,5)]))) (.fork 8 (.fork 4 (.leaf [(194,0,317,0,8),(194,4,305,8,5),(196,2,312,1,5),(197,2,312,0,4)]) (.leaf [(198,0,313,0,7),(200,4,305,2,5),(200,256,23,32,5),(202,4,305,0,4)])) (.fork 4 (.leaf [(224,256,23,8,5),(232,256,23,0,4),(256,0,255,0,12),(256,8,227,20,7)]) (.leaf [(256,16,230,9,7),(256,32,94,129,7),(256,64,189,2,9),(258,0,189,0,8)]))))) (.fork 32 (.fork 16 (.fork 8 (.fork 4 (.leaf [(258,64,189,0,8),(260,0,251,0,8),(260,8,227,16,6),(260,64,185,2,6)]) (.leaf [(262,64,185,0,5),(264,0,247,0,9),(264,16,230,1,6),(265,16,230,0,5)])) (.fork 4 (.leaf [(266,64,181,0,5),(268,0,243,0,7),(268,64,177,2,5),(270,64,177,0,4)]) (.leaf [(273,32,78,128,5),(275,64,172,0,4),(276,8,227,0,5),(280,0,231,0,8)]))) (.fork 8 (.fork 4 (.leaf [(288,0,223,0,9),(288,16,198,9,6),(289,64,156,2,5),(291,64,156,0,4)]) (.leaf [(296,0,215,0,7),(296,16,198,1,5),(297,16,198,0,4),(305,0,206,0,5)])) (.fork 4 (.leaf [(320,0,191,0,11),(320,16,166,9,6),(320,32,30,129,6),(320,128,27,36,6)]) (.leaf [(321,32,30,128,5),(322,0,189,0,8),(324,0,187,0,7),(324,8,163,16,5)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(324,128,27,32,5),(326,0,185,0,5),(328,0,183,0,8),(328,16,166,1,5)]) (.leaf [(329,16,166,0,4),(332,0,179,0,5),(340,8,163,0,4),(344,0,167,0,7)])) (.fork 4 (.leaf [(352,0,159,0,8),(352,128,27,4,5),(356,128,27,0,4),(384,0,127,0,9)]) (.leaf [(384,8,99,20,6),(384,32,94,1,6),(384,64,61,2,6),(386,64,61,0,5)]))) (.fork 8 (.fork 4 (.leaf [(388,8,99,16,5),(388,64,57,2,5),(390,64,57,0,4),(392,0,119,0,6)]) (.leaf [(396,0,115,0,5),(401,32,78,0,4),(404,8,99,0,4),(416,0,95,0,8)])) (.fork 4 (.leaf [(416,64,29,2,5),(418,64,29,0,4),(448,0,63,0,8),(448,32,30,1,5)]) (.leaf [(449,32,30,0,4),(480,0,31,0,7),(484,0,27,0,4),(488,0,23,0,4)])))))))
def dead : Forest := ⟨511,13,deadsamples,deadcolumns,deadautos⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]; repeat' apply And.intro; all_goals decide +kernel
def qL32 : PT := (1,7,8,1,fun _ => 0xa1afe70ad00ba5af8e)
def qL36 : PT := (48,6,8,4,fun _ => 0x1c1c7070f0b3d50f103d50f7c0055c0b3c2cf3d71f0f0bdccbaaaaaa999998777765433222222222222100000000000ca7f35a21729651df54e7e528256ca3b2df45e805d2d747716fab9ec30aaf8ec2ff71a21729651d85fc2b442e52ca3a2bf86aeca03d6c7617fb6d10b94b28ee3f94b16a3275d1d47bf7a7b0c2abe3b0bfdee885ca59477c73a0aba68dad8e8b7e1abb4a0d5f1d86fedf402e96be3b8f6cf45618557c771ed98a5c30aaf8e8afe1abb280f651df34e9a9e5256b63be9cccd1cf4557c751efdb8ac30aaf8ecb5f2da0174b5d1d95be3f442e52ca3b8b7d1cf618557c7617f0ad10b94ad8ee3db274b86155f1dc6bd92970c2abe3a2dfee0660d2d7c77d1d939c9ea3af8ef9b3294d274b5f1d15ff7433129aca3be2dca535155d6c77c57a9aba095b28e8b7fb8198d4b5f1d15ff743306a6b63bea9d04aca4fd6c77c738da0aba6b28ec37f75a0174b5d1dc5be7e7b0c2abe3be2dd14a55d3594751ef0da5c30aaf8ec37e15a0174b5f1d13ff78330a72ba3be69ca4ad3d359477cb9a5a69998af8ef8af2b5341575b1d15ff74330656b63bec5ca4b4cce5747457fdd0cc195b28e)
def qH0_36 := lw0 1 2 2 5 1 4 (fun _ => 0x80)
def qL37 : PT := (4,6,8,1,fun _ => 0xa39fb41588255f1d45bf682b18b6be3a8d7ed05628957c751eeda0abf12af8e)
def qL40 : PT := (425,5,8,10,fun _ => 0xc0000010274cf408c00099eb02d8720820000340078000619000d808c0b00e80000a404a01a01a00fa0151db803000377c0a3801400c7d5619301003530b9aa4cf485003e02100dd83dc31a1880d586409b619301000400000080318f805200600040e0c32602000400101e80e00d400006098830100042ccc05f0c40d835a60e000007fc3161430101a8c0b021000009d40e01d0001872c0400080000d8c04605c078850c1e71c1c405c80350000158018000022001400284f99e8c4028e0c300400c8000385985b0c80040be99e8c4103c01d185b1f028f385605b071850c04000800209e0400234cf667b33d237a1a859873d98870c667b310001800406a35a021009d83c10b21900f002333d000800037a08d71c1cf409433d602000863901e04c0008000432023025400400103e8d5000407d03700046f904f1be011800406c013c07a7aa1a218e010807200063e4d680d4000227ccf406c03c0004ea675203c00000c800003204dc0d5872c0459ecf5409c00202500000fd30b44c000c0020020002c405c81bd9aa30f40640000038000078000185f0c675331001b0cf402b30b01900006f804ac0e1c2c06a4983aa607006a3d50a380141a407600f8b9008c002001000267b3b7a0e00d4e21804001002000101e80e038c02b30b18e0000042c04001001400037c845851e06535a602302d87bc311724cf583803b02a821800400017270c400205501a800186400260e000400033d01d81545c9c3101c81546a873d43506880dc00101c80001e6052001000036206c0d881445300119cd0cf662033d00280026a803560e4d5002b33d61e8108ea805260f032ce2007085dccf4734c3d9858c2c28e03903eb0e4018c040008264000039000001400073d05e000661606c0364c2c04f35a0d88c4067a00105e051c6a806c023607836380b01c80026a80150de8ea402279a025301000203902a8004178c3900082f000204600101281e68980134c418720011aa004400000000e8b9008d81e01a851d864002037b072220039000015800c01dc0201b00020000d881fc00f3a903f801c12c05500180000020009aa005581600200001a00001bd1d4868a03d01c988039c00408d99e81a000031c99eccf5816754027000806a00022786240040000dee1500640001be0050000710019000106a01d60200080400000190001c7071001901f7008002000800000400000100000720000018002734b3d01900030080028278c2cea803d18821a8e1600203a8a6002a01100e800008c0020190001864002001000007200000100000a441e0210b30e7b80b0ded15209e048001307009c002634000800002002100d103c03e01980c80fa37c023000800a0000008003862002000000800000500002f06a800100100026d9ae6b9a66899a6498a609825e9725a9625594e529464f9364b92a4891a459124290a428fe3e8f23a8e2368d2328c22f8b62b8a6278962388e2288a218821e8761b86a1885e158561384a1083a0c82e09822068160480e01805ff7f5fb7e9f97e1f77d5f37c9f17bded7b1ea7a5e97a5e979de6795e4789e077ddf779dc76dd9761d875dd6755d474dd2741ce72dca721c7719c470dc2709c1701c06fdbe6f9bc6edb96ddb56cdb16c1ae6b1ab6a9aa69da468da2685a06799c6699965d956559464d9163d8d6318a629896218661583609815fd7d5f17b5e9785d9745c9715c16f5b96e5b56c5a96a5a1675996458d625815e5755b5655855954551535414f5354b52146515435053f4f93c4ed3a4e1374d9354cd314c12e4b52c4a9284992548d224811f4791c46d1a46518459144491043d0d4310b429094210741904404ff3f8fd3f0fb3e0f73d8f63d4f43ccf13c0ef3b4eb3a4e7394e3388e0378db368d9364d835cd5354d434cd2340cf338cc328c831cc6314c3304bf2f4bb2e4b82d8b42c8b22c4af2b4ac2a8a92a0a628ca127c9c2689925c9625092248922408e2308c22c8921c85210822047f1f87e1f47d1ec7a1e4771d8741c8711c4711c0701c06e1b06a1a46719864188601785c16c5a1605615854148501384c1304b128481184511042104400fc3d0f03b0e8380d8340c8300b82c0a4280982408c210801e0701a06417054130400e0300b02407014020025ff0cc6a7b28ef37eae56a6b63b5fd8dc031ad8ee7eeee527eb63a9ff0c940ab28ef5be3e8aaeba3b57f94c62daf8ed7faa6fc4abe3bdf3a68da0b28ec7fedf1e72b63b5f7ccc231ad8ed7de2b08c6ba3a5ffcd0b94b28ed7df2f08c6ba3a5ffccc795b28ed7be582e96ba3b57fc5ab9eaf8ec7fea7002aba3bdcf9c9496ae8ec7fe694416ba3a5ffd0c742ae8ed6fc0b14c6b63bdeb968a99ae8ee7eeea669ab63bd7ba0949fad8ed7de3708c6b63bcfba7a694ad8ef7ce9a8236b63b57f8cc631ae8ed6fe3314c6b63bdbb9c9499ae8ed5fd3d3a52b63b5f702c231ad8e97fc330656ca3b1ff08c00aae8ee6feea6672ba3b1ff085101ae8eb7f7424e96be3b57f02c631ad8ea7ff42282abe3bdf68a958bae8e97ff4b0a72ba3b9bfb8999cad8ed7ec0b04c6b63bd3f999ea3af8ed7fa36fcc6ba3bddd9c93a5af8eb7bf3e8e3eba3b57f8cc631ad8ef2fe7296aaba3b5fe8bc4abae8e97ff3c2eaeb63b5bf8ac531ad8ed6fe3714c6b63a5ffcf0ba6ae8ef6be3e6672ba3bddd9493a5af8ed7fa36fcc6b63bd5f4e9394b28ec7fee316aeb63b5bfa9c512af8ec7fef02e96ba3bddb939f94b28ed5fe2b18c6ba3bdf6a98c8bae8ed7ee3704c6b63b57f8dc631ae8ee7f67a282abe3bdbe8b9caaae8e97ff4b10faba3bddba694a2b28ec7feab002aba3b5fe8abf31ae8ec7fea54406ba3bded96a593ae8ee7ec2a527eb63b5dfc294a2b28ef73e4e525aba3b1ffa75193ae8e97ff3c2e9ab63bd7dab9e8aad8ee6fc2a6662be3b57fc74e94ad8ee7eee29a52b63b5bfc69998af8ef3de569a9eba3ad7fccab9eaf8ef3f6aa4e96be3bddb57a694ad8ef3eeae9a52b63bcdfab9ca9ae8ee7eee2527eb63bd6f8f4e94b28ed7fa2c2e96ba3b57f8dc631ad8ec7fee02e96ba3b5fe8abf31ad8ef76e8a9a52b63b5ef960ba6ae8ef5ed3a9a52b63b9fbb89f94b28ee7eef6527eb63bdcf9ca98fae8ef5de567e82ca3b5f7ccc231ae8ee3fea6ac2ab63bd77ab8da0b28ed7df2f08c6b63b9fb0aa694ad8ef5deae8236b63b1ff955101ae8ef6ee722a66ba3b5bf8cc531ae8ed5ff1e7a7eb63b9bfb7999cad8ef7ce329a36b63bc7fa0aba9b28e97fc330696be3bcfba799a6ad8ef75e528256b63bd779fa095ad8ed7f63700c6ba3bd7b949fa0b28ef75ea68256b63bddb9594a6b28eb7ef469a52b63bd77aba095ad8ed5fc2d3a52b63b57fc1a0abad8ef7da52562eba3a5ff0cc195ad8ed7f80afcc6b63b57f59c1a9ad8ea7ff3e282abe3bdbda59998af8ec7fc2b06a6b63b5bf58c1a5af8ed7df128236b63b5fe8cbf31ad8ef75e9e5256ca3ad7fd10b94b28ef6deaa6a32ba3b9bfb7aa9cad8ed7be5b0252ba3b5dfc195a9ad8ef5f68e7a4ebe3a5ffd0c1a5af8ee7f6ea6296ba3b1ffb6c1a2b28e97fd74169aba3bdfc8ba593ae8ec7fedf12aeb63bcf7a695a7ad8ee5fede8eaeb63b97fb8a3abad8ea7ff428adeb63a5ffccc4abad8e97fd7652aeb63b5fda5c43eae8ed77f4b104abe3bc7fa2aba6b28ef1fea682aeb63b9bfb8aa9cad8ed5fd670656b63ad7fcfa0abad8ec7fee82e96ba3b97f0aab9eaf8ef6fa2e728eba3b1ffa75101ae8ea7ff46502aca3bd7d8aab9eaf8ef7f22e6296ba3bcfbab99a6ad8ef7ae5a669aba3a5ffd1c195ad8ec7fedc2eaeb63b1ffb7c5abad8ee5fedaae7abe3b57f8ac631ad8ee5fee28eaeba3b9fdbd9e8aaf8ef7e6667a2abe3bdbe8b4da5ae8ef7ae5a5266ba3bdaf969899ae8ef1fe9a82aeb63a5ffd10ba6ad8ed3ff06aea6ca3adfbcd94a6b28ef5faae7a2eba3b5bfaac542ae8ef6fa2e6672ba3adfed29e8bae8ef6ee72669aba3bdeb9694a6ae8ec7fea54632ba3b4ff5ac29cae8ef5fa2e8eaeba3b97f5994bbad8ec7fee82e9ab63bcdf95aba9b28ee7f42a4e96be3b5bf99c29cae8ee77e8a502aca3b97f59940ab28e97fd742252b63bdf6a5958bae8ef3be5a969aba3ad7fd29fa0b28e97ff342e96ba3b5fb0cc131ad8ec7fc2b12aeb63adf7cf8da0b28ef75ea65682ba3bd6fab9e8fae8ee7f6f26296ba3b5bf8ac531ae8ed7be5b06aaba3b5f78ac231ad8ed7de9f0a72ba3bd7e8ba2abae8ec7fee302a6ba3bd7b9e949fad8e97fc33069eb63b5dfa9c29cae8ed7ee3304c6b63b1ff0ac6a5af8e97ff3c2e96ba3b5fbcdc131ad8ed6fe682e52ca3a5ff0cc6a5af8ed7f64f1a96be3b1ffb7c6a5af8ed6feab0a72ba3b5fbcbc131ad8e97ff331a96be3b57fa3c6a5af8ee7ee7e502aca3b9dfb8a99cad8eb7bf3e665aba3b5bf58c6a5af8e97ff431a96be3bcdfab95a9ae8e97fd74140ab63bdeb8f9f94b28ef5ee7a7e52ca3b9bfba999cad8ef6ee6a7e52ca3bddb93a694ad8ee7eef67e52ca3adf7d2a095ad8ef57eae528aca3adfbd29f94b28ea7ff42a42aba3b5fe8bc0a9ae8ed7be5b02a6ba3b97f0aa2abad8ed7be582e66ba3ad7fcba2abad8ee7f662942abe3b5fe8cbf31ae8ef57e528aaeb63bdbd934da5af8ef1fe9a8aaeb63bcfb94a7a6b28ee5fee28aaeb63bd7dab939ead8ef3be5a96aaba3b5fb94c12daf8ef67ea6728eba3a5ffcfc12daf8ed77ea7104abe3b5bf0b4da5af8ea7ff4a62f2ba3a5ffd10ba5af8e97fc3312aaba3bd7d93ab9eaf8ed6ff402e96be3bcfe8ba5aaae8ef2fe6a96aaba3b8ffb8a5aaae8ef5beae8e3eba3bdbba69998af8ed3fe9b1a9eca3b5f795c6a7b28ee6fef13696ba3bcf795a7a6b28ef67e8e4e72ba3bd9fa9999cae8ef67eaa4e72ba3bd5f599495ad8ef6be728e3eba3adef0cab8fae8e97ff4b104abe3b5ef96c0a6ae8ef1fea68eaeb63bcfba5a694ad8ee3feaea6deb63b5fbc2a694ad8ee6fc293696be3a5ffd593a5af8ee6fedd3696be3b5bfc14da5af8ee6fef13696be3b57fd10b94b28ef76e569a52b63bcfeaba98bae8ed5feaf0282b63b5bfc64da5af8ef76e567e52ca3b5fb99c1a5af8e97ff302e96be3a5ffcd0ba6ad8ef77a72a62eba3bd5f599495b28ee6fc2a6672ba3bdaf96999cae8ed5ff093a52b63b9bfbd999cae8ec7fc282e96be3a5ffd00ba5af8ef6de9e6a66ba3b1ffbc0ba5af8ef73e3e528aca3a5ffd10b94ad8ee6feda728eba3a5ffd10b94b28e97ff3f0696be3bcfb8daba6b28ef3f69a4e96be3a5ff0cc29cae8ec7fc2b1696be3bded9698a5ae8ef3eeae9a36b63b5ef8f0b94b28ec7fed82e52ca3a5ffd20b94b28ef1fe9a8eaeb63adefcca996ae8ef7da8e562eba3b9df0a94a2ad8ed5fd67129aca3bdd794a095b28ef75ea68256ca3bd7b5994a6b28ef5deae8256ca3a5ffcfc6a6b28eb77f32a656ca3b9bf0a9caaae8ef6be3e72aaba3b9df9ca90aae8ed5fd670656ca3a5ffd00babae8ef6be5a72aaba3bcfb94aba6b28ef776727a4ebe3b97fb69eabae8ef1fe82ae9aca3bddb95949fad8e97fc3306a6b63bcdfaba99cad8e97ff3308c6b63b4ffabc1a9ad8e97ff302eaeb63bc7fa69eabad8ec7fc282eaeb63bdd7a79594ae8ed5fc2d3a52ca3a5ffcd0babad8ec7fc282e9ab63b5bf8dc531ae8ee3fe9aac2ab63a5ffd2c195ad8ea7ff30c42ab63bd7da39e8aaf8e97fc331cfaba3a5ff0cc131ad8ea7ff3e7c2ab63a5ffd2c11baf8e97fc331a9eb63bdd7a79495ad8ee5fede8aaeb63bc7fa99eabad8ea7fc32502ab63b97f59940aad8ed7de3308c6b63b5fba6c11baf8ef73e72a65aba3b4ffc2a6abad8ee77edea672b63b97f9ea30aaf8ee5fd6652f6b63bd9f9a94a2b28ef6be593696ba3bcfba5a68dad8e97ff342e52b63b57fd10b94ad8e97ff482e52b63b57fc54e94ad8e97fc33068aca3a5ff5d94a5af8e97fc33129aca3b5f78cc231ae8ed7de3708c6ba3bcefa9ab8fae8ef3de9a6a9eb63b5fb8ac131ad8ed5ff013a52ca3bd3f9a4e94b28ed5ff093a52ca3b57fc74e94b28e97ff342eaeba3bd3f9c9ea3af8ea7fd730256ba3adbfd04ca6ad8e97ff569a52b63ad7fd10b94ad8e97fd741696ba3a5ff5d0801af8eb6ff41329aba3a5ff5d02a5af8e97fd74200ab63a5ff5da605ad8eb6ff402e96be3a5ff5d0205b28e)
def qH0_40 := lw0 17 56 6 10 6 4 (fun _ => 0x21044340d0270081b0340b050a3040120b403078260600c0902f03c230a0170180e07ce90b02202434710050706b0a40101c1a020340103408019000150a813074160b865628008818e19c4411c0b981002c0)
def qL41 : PT := (119,5,8,8,fun _ => 0x3a40e002e04100100e602e80f032c0080ed03cb02d84600303c835414800305001e6044fa979ebe15ea90227aa00100bec1c028302c09a439017907084600406281ec00402f605b08c1a007b60e01400060a706202400f203606980f01a6c3901780f00e604902801001c301c01283cc10a07300d308d87202f602014807c03c60e014000a08c073814000a079a1e82bc86406c06a828c16a03c605b08c06e02f60e01401aa0a363e03080e6cb7056806c1340dc07402d01340dc00181ed80805206682bc17000b0360354146c3203cb0700a0c0b0268354146c3203c80200d80e8039831000005201a81400780a407a01e401603b03c82d405ec3203c83a00e701e071c0781c6044611b0c80f202e05c81ec1aa0a380e03cc1a603b071b0100a440b611b0e405e00103883bc1020dc001014819c0827ad00b980805201e01b017501e036000805e05205a0334164c3201782681b803e01e03dc05f832057d2dc16405207910c80f2042010c0100780ba046012000402f016407811e0b501e52de81608f60e02d807c06c00100bc83805000080bc17207b00080bff7ebdbd3c7bfb7afa39b8b7f776f675f534b433b332b271f170f06fef6eee2dad2cac2bab2a6a29a928a827a726a625a4e423a322a221a1205fdf5ede5ddd5cdc5c1b9b1a9a1958d857d756d655d5951493d352d251d110900f0e8e0d4ccc4bcb4aca4a49c948c847c6c6058584c443830282020181008031ef01c30aaf8ec7bcb70c2abe3adf6cb958bae8ec7bc4b0c2abe3b5af8fc531ae8ec7be630c2abe3b1feb6bf31ae8ec7be4f0c2abe3b1efa3c30aaf8ec7be970c2abe3b1fda5c00aae8ed7f22f00c6ba3b5ee8fbf31ae8ec7f82afc4abe3b5f68bc21bae8e87ff494632ba3a1ff5d02bdad8ed7ae3f04c6ba3a1ffd25193ae8ed5fa2f18b6ba3b1ef9ec30aaf8ec7be3d4422ba3a1ffd25105ae8ec7fa2d4422ba3a1ffcb5108ae8ec6fc2b144abe3b17fb8c62dae8ed7db2b08c6ba3a1ffcf5108ae8ef75a52562eba3b1febdbf12af8ed5be5b18b6ba3b17f0ac62daf8ec6fc2b14c6ba3a1ff5d05b7ad8ed6fa2f14c6ba3a57fd10b94ad8ed7da2f08b6ba3a1ff5d05bdad8ec6fd372696be3b1fd0ac031ad8ec7dedb08c6ba3a1ff5d08b7ad8ed5be3f18c6ba3b17f0ac62dae8ed7ea2f04c6ba3b1fbd4c131ad8ec7f6df00c6b63b1febabf12af8ec7eee304c6b63b17fbac62dae8ec7df5308c6b63a1ffcd5108ae8ec7dc2b08c6ba3b1fdb8c031ad8ec7f695464eba3b1bfb6c531ae8ec7ec2b04c6b63b57e8bc631ae8ed79e3f08c6ba3b1fdd4c031ae8ec5fc2b18c6b63a5bfd00ba5ae8ec7df5308c6ba3b1ef965108ae8ec7f82afcc6ba3a5fecdbf31ae8e87ff2d4416ba3a1ffcd5105ae8e87ff354406ba3a1ffd25101ae8ec6fc2b14c6b63b1bfb8c531ae8ef7d22a322eba3bdf4a58c8bae8ed7b73b00c6ba3b1f70ac231ad8ec7be2b0c2abe3a1ff5d08bcad8ec5fedf18c6b63bdd6a9958bae8e87ff35464eba3b17f0ac631ae8ed7b63f00c6ba3b1df0ac412af8e96ff402e96be3b1dfd4c412af8ec7ec2b04c6ba3b1ef1bc30aaf8ec7f42b00c6ba3a1ffcb5195ae8ec7f6954632ba3a1ff5d02bbaf8e95ff442e52ba3b1fbb6c131ae8ec6fc2b1472b63b1bfb8c531ad8e87fd7416e2b63a57f5d9407b28e87ff3d4406ba3a5bfd00ba5ad8ec5fd3b2652b63a1ffcf518cae8ec7f82afcc6b63b1fe8b5193ae8e95ff442e52ca3a1ff5d02b8ad8e95fd76501eb63bdf18a8c8dae8e87fd7422e2b63b17f4ec994b28ec6ff253696ba3a1ff5d05bbae8e87fd740aeab63a5bf5da506af8ed7da2f08c6ba3a1ff5d01bcae8e87fd7422f2ba3a1ff5d01bdae8e)
def qH0_41 := lw0 16 58 6 10 6 4 (fun _ => 0xd007684576282175c4b0d02b08c6b3a5e06641b0a0a31942202d296703406434069d9098340605937c340d02f07020688340a80847c2d0a42778adf0b25f058340d00a07c17170250c00d320000c041140001198)
def qH1_41 := lw0 1 11 4 7 3 4 (fun _ => 0x5982600020308118840)
def qL42 : PT := (2,5,8,2,fun _ => 0x811408a4c7b4070c2abe3b1af06c30aaf8e)
def qL44 : PT := (382,4,8,11,fun _ => 0x234205851834a0744d40201b84dc3406e84ddbe02420741c84e02d8768045be23402602540f02283083620f41940206b019834a4082584100ba0b034a0701ba020210750a3877073c5d8d8834a0701d618800bbe073801440a0f08a0258505be002a1943423401f0605be073a5d802a1903097202182140703605182740f45482502920f3aa0760045be2352075be02720f3be5aa41ca1cc022025be05c866829060a0202f01d61880083801b8750a3bbe07380122d20202d81b01e61880082594c40f3be037e18a1907304681ba4c20f02f01d985a02008804235234023846a070d8836078001821402000c1924c01ba0f3be02720f43414c20f24d20204d81bdaa00b01e000a1401e20f001036533bbe02720f41ca1c80902107182617220f23445325dc0200116602101b01aa02618806c3414c20f23402700982500bc0b034c073be05100121cc0b01f00ba3500181484183600097207a003a40a0204101bc3423420200981a80119eac29db98585e00081b205c02001427bbe0270013be07380121920201982ebbe02400086b01b00721c85e82f19e9880230013aa062c0f41918807381f061618bbe06186880ea14074863daa20204c843013205a3502520702520f07982902541921940f5be423a7225dbaa0608009be2350de82e861bbe41921940f3aa06d000c1c86782d82902101281b20f001419028e1880081a814d1c006c1914c40f04a9c2808c1c84302da35618c19219402008bbe2350015aa3be00087603120201983b41c87582d80b01e0009be07820f1ea83b00fcc2824a0f21401e20f41c82e8211dba1c86082f20201d8089db83d0388dec1921900882543401483c20f0d8c07034c34014834c0705e8551d4c1ca1cc0202103d0de838a1cc0b40200b8258fd40f02e80123541c855021078001c0202400b872802822021024a0f01381b20f039c1920203101e3be024000a34023875a350de82e83482184682e00902dbbe02400103000080117240b05500b9be01b40207601bbbe05100101aa023be0270018dea0204323531820201b00602d87581b863001bbe01a024c0f012a0f01b87986140f08a20207402240201b067000868039bbe00b01e00087a0045be419023846b1820201b00621916600182c435434234067009b1806b81f06b06586281b01e20f07280287181381283620f01b03820205e03983201b20f5be01320f18801283620702286b03640220201b8d8baa06280183108720f05b06340f5be205c0202e02901b3be06b07280104881283640703085e83602101b8580a3c549d481ba0f02101b40f08b01b01620f01aa0240581e22781281b20f07b0410a3a02022002cc2baa01b18580406805908a075859bbe02740f41921905c8433aa068002baa072802a3500101db1c00101a9cd0010a3985c0205e02e01d16601ae1880146697220f01aa2780094c07a00287a0045be02902101281b20f066bbe618a1940f01e0011ad03604202903985e8380360360013aa51840201b00607a002878003a0200101d81507d0558a3c1c86002d83803b20f25301bc0f1ea83b00f85a80281e61880087e0460a386180106441925340f23501b40f21907304304124081b40f03801a9ea80107816600182520f06582600ec1921900886181984683a04ae18800c34073046a350de82ebaa0760009d4a19019c0f18801d61884321916640f51820e02101b20f5be02420704303a019a0e03620f00e835a19046800dbe00121901aa27c4c01d96620201e20580120222780101b09440206402e440c0201b04143414c45dc1921940200886801b05c8213be02700101ba4c20f3be41940206b019c1ca1cc0200605c99ea0202341ca1c806074c3797220f21c80c03821941405c81486901a03b40f08b40201b05e01b85001b20f01ba0202d81b1be21401e20f3aa08a40204d87b03088a05b20f06923502b98583806801b1dbdaa02520e45e81b20f5aa40584c81b20f056800a190148089db81e20201ba4c20f20e17202920f01e019a0f5be0012351db9be07400381e0009c2e1882880082507e20f5be0042352356189be0750238768039db8314190de83187800386c04301983d0388dea3500381e019a0f4194020550199880738040554350de825419019a0f0554350de8384024350b042a01e019a0f3be02c43503b20f06b43500886b01f43501d61880897220f019972019a0f06b84d819c1c84102e844800a1c84203984d800a353aa076000c1921906700881e6188008312190308dea3500184a800bbe004235434014a1420f3be188073802bbe0738028314190de831a35002c1921920201f00885c84e84d800c53000c5321401e20f21920202e819c1906e84dc02000c27c02000c2781e42781d4278dec27a3502881e20f01e019c0f1db98805f0013be03140201983084301983081e61880084a800bbe1db825000a3521961885182740f02521940f019c1914c40f3be02700180894c014808a3503340f06340f03300106300105c847046846800a3500094c21920202e819a1914c40f1c2a35007a340730443be073802dbe21918807385c99e98802300123561884ae1884303f3be219618dbe19e8738013be07380104a800dbe028e188088042350630011db82882020207680101a024c0f4f49df3ae744e59c537e6dcd79a733e65cc69873025ecba96b2ca574ab95329e51ca09392624b49391b226434838ff1f23c4758e51be364698c918a2fc5c8b515a29c5089b12622c4287f0f21c4348630ba144258430760d41682904607c0d81301600bfd7f0fd5f93ee7d6fa1f2be17bcf69ec3d47a2f35e43c4780ef1dcbb5760eb5d53a5746e81ce39972ce4dc8b8d714e19c137f6f8de5bb3736e0db5b4b666c4d79ad3576a6d41a634968ad099fb3c674cdd9ab3165aca593323640c758d31762ac4d8830b610c1981aff5f6be17b2f25dcbb174ae55c4b796dad85a8b4567acb58eb09602bb56eacd562a954aa894f29c52ca494728b50ea0d4027c4f49dd3a2714da9a1322614ba9692ba554a49392524848a9092023e4788e51a23145e8b1142254448790e21a42c84d0820d41481d02a023fe7f0fc9f63e67bcf59e83c677cee1d93ac74ce81cc390714e01bd3746d4d91af3586a8d31a333c668cb99331e630c49843005f0bc1752e45b8b51662c4578ad1552a2538a514327c4f09c9362664bc9612924a4888f91c23245c8a11221a42c841052064007e0f91ec3c8778eb1ce390710df1b83646b0d31a0334658c818a3085f0bb16e2d4590b01582a0528a113e2684b8951262404608910c20c4087f0f81e43b0720da1a8338640c01782d8570a81442784c094120230440820f81e03806a0c81782c04e08c1081e0340580981001a02c04805006003bff1945651ddff08a2ae8eeffd351594777fe2a52ca3bbff45315f1ddffa6abad8eeffd34ad94777fe6a4eba3bbfe39555b1ddff9e95b28eeffc54ad94777fe4eaeba3bbff294d651ddff8aa2b28eeffc654d6c777ff129ab63bbff2b3d5d1ddff9394ad8eeff82d3594777fea652ca3bbff27535b1ddff99a7ae8eeffcfc9d94777fe5256ca3bbff2b475d1ddffa5abae8eeffc9cad94777fe3652ca3bbff294b5f1ddff0894ae8eeff8e52d7c777fe32aeb63bbff39575d1ddffc4a6b28eeffcc54d74777fc222ab63bbff3f2b651ddffc19cae8eeffd054d6c777fe8272ba3bbfe934b5f1ddffa5a7ad8eeffd04a594777fe7a52ca3bbff8f41651ddff0893ad8eeffd055574777ff0a52b63bbff414d651ddffa2aaae8eeffc552d7c777fe34c6b63bbfe0b335d1ddffc294b28eeff8149d7c777fe56aaba3bbff4f45651ddff8d31ae8eeffc9d3574777fe368aca3bbfe052b651ddff058ab28eeffe34a594777fc162abe3bbff812b651ddff8d9eb28eeffe053d6c777ff12aeb63bbff3d555d1ddff0205b28eeffca4e574777fc2e96be3bbff14635d1ddffc48dad8eeffe3ca594777fe6416b63bbff83275f1ddff8aaaae8eeffccd2d7c777fc2e52ca3bbff4b4f5d1ddffa605ad8eeffe0d3d74777fe529eba3bbff1b57651ddff9fa5af8eeffc602d94777fe56aeba3bbff4d2b5b1ddffa794b28eeffe0d2d7c777fe66aeb63bbff294f5b1ddffc5a5af8eeffd4cc57c777fe3016ba3bbff4d155b1ddff93a7ad8eeffc9c6d74777fe7e9eb63bbff4d3d5b1ddff9f98af8eeffe054d6c777fc200ab63bbff8b295b1ddff9ea5af8eeffcd02d6c777feae62be3bbff15275f1ddffa7abae8eeffe24d574777fe5652ba3bbff1b535b1ddff9993af8eeff8152d7c777fcba4ebe3bbff4d395b1ddff9502ad8eeffc682d94777fe822aca3bbff1b27651ddffa3a5af8eeffd349d7c777fe729eb63bbff53155f1ddffab95b28eeffccd356c777fe8e4ebe3bbff8f415b1ddff318aaf8eeffe2d4d74777fe564eba3bbff19395d1ddff9a02ad8eeffe24557c777feae52ca3bbff33535b1ddffa093b28eeff814c57c777ff0252ca3bbff8b155f1ddff8daaae8eeffd1c557c777fc06aeba3bbff8d295b1ddff42aaae8eeffe0cad94777fe9652b63bbfe03535d1ddff98abae8eeffe0d3d6c777ff0656ba3bbff19575d1ddffa6a7ae8eeffa455d74777fe4ea6ba3bbff274b5f1ddff9e8aaf8eeffd4d5d6c777fe5282b63bbfe034f5d1ddffc6a7ad8eeffd4ce56c777fea40aca3bbfe0b555d1ddff8c08ae8eeffe3ce574777fe32aaba3bbfe994b5d1ddff9598ae8eeffc64a594777fe4eaaba3bbff4b475d1ddffc0a7ae8eeffcd5156c777fe9a9eb63bbff4b295d1ddff94aaae8eeffcfc6594777fe6a96ba3bbff27475d1ddffa7a3ae8eeffc9d3d74777fe562aba3bbfe7d535d1ddff058aae8eeffc654d74777fe7aa6ba3bbff27295d1ddffa5a9ae8eeffcd55d74777fe5236b63bbfe113f5b1ddffc0a9ae8eeffce54d74777ff169ab63bbff1b535d1ddff94a9ae8eeffd2d3574777fc2232b63bbff4d535d1ddff9aa9ae8eeff82d3574777fe2a82b63bbff8d535d1ddffa9abae8eeffc618d74777ff06a6ba3bbff272b5b1ddff8a9cae8eeffcf4e574777fe9672ba3bbff33535d1ddff0801ae8eeffe354d6c777ff0aaeca3bbff1b395d1ddffa9a3ae8eeffd34c57c777fe5672ba3bbff454f5d1ddffc29cae8eeffe34e574777fe2a9eb63bbff41535d1ddff8aa7ae8eeffd153d6c777fe629eba3bbff3f535b1ddff9ea7ae8eeffd34e574777ff1a9eba3bbff2b4d5d1ddff02a7ad8eeffd04e56c777fe7a9eb63bbff5341651ddff99a7ad8eeffe352d7c777fe8e9eb63bbff19295b1ddffaba7ad8eeffca80d74777fe4e52ca3bbff3f395b1ddff9599ae8eeffc9d056c777fe2a52b63bbfe0b1b5d1ddff088dae8eeffc554d74777fd329aba3bbff4b1b5d1ddff089eae8eeffcfd3d94777fc140ab63bbfe11275d1ddffc48db28eeffd049d74777fe52aab63bbfe10035f1ddff4f94ad8eeffd580d7c777fe9e72ba3bbff39155f1ddff088dad8eeffe2cad74777fc222aba3bbff19455d1ddff98a2ae8eeffc6d5d6c777fe968aba3bbff35455d1ddffc595ad8eeff82d2d74777fe5696ba3bbff414b5d1ddffc59eaf8eeffc9c6d6c777fcf822ba3bbff40115d1ddff9a05ae8eeffc6d556c777fe6652b63bbfe17575b1ddff8aabad8eeffc9d5d6c777fe56aeb63bbff4b575b1ddffc0abad8eeffca55d6c777ff06aeb63bbff35575b1ddffc2abad8eeffcfd556c777fe72aeb63bbff8b575b1ddff8da3ad8eeffca51d6c777fe9aa6b63bbff4d475b1ddff95a3ad8eeffd4d1d6c777fc0a72b63bbff1b395b1ddff949cad8eeffcace56c777fc0aaab63bbfe0b555b1ddff8ca6ad8eeffcad556c777fe82aab63bbff45555b1ddff999eaf8eeffe0cf57c777fe727abe3bbff4b455b1ddffc79eaf8eeff8154d6c777fe2aa6b63bbff4d355b1ddffc5a0ad8eeffcf54d6c777fe96a6b63bbff1b53651ddff94a9ad8eeffe0d4d6c777fe6aa6b63bbff8b535b1ddff3102ad8eeff845156c777fe2a8ab63bbff19455b1ddff8da2ad8eeffccd156c777fe9a8ab63bbff14635b1ddff8c31ad8eeffc502d6c777fe3016b63bbff4a0b5b1ddff8d05ad8eeff8e4d56c777fc2e9ab63bbff29355b1ddff9f9aad8eeffc54ad6c777fe7a56b63bbff4b2b5b1ddffc095ad8eeffca4ad6c777fe6656b63bbff3f2b5b1ddffc195ad8eeffcf46d6c777fe9636b63bbff331b5b1ddffa68dad8eeffe2c6d6c777ff1e36b63bbfe11415b1ddffa5a0ad8eeffe05056c777fe6682b63bbff4d415b1ddffc0a0b28eeffcfd4d94777ff06a6ca3bbfe11295b1ddff0b94ad8eeffe05356c777fe7a52b63bbff81295b1ddffa694ad8eeffe3ca56c777fc227ab63bbff274d5b1ddffa5a6ad8eeffe15356c777fd329ab63bbff8d4d5b1ddffc095ae8e)
def qH0_44 := lw0 124 260 9 14 10 4 (fun _ => 0x62f414a63f819a067411e120dc2604a41530624174047418403e801e00a8163034c0b700200c805dd832064c0cd02fc06b058012804ec11605bc49a04881a0000000e042089702280b6145e5760279da1028003c014449c041c089026c16804c414774581506550135056009875e80ec06580fc03cc03e004c091005808003800ea0220067031e8cf01d022215b022203be50d062c0ac002d89c037808c168404201ea57900900ad0630060020402c01000d40460167013c1700014015056c0b3044c49402380030888173088822200d011b168805f02d41170044222015c0ce055802500c811000041410628045065418e0621d8304b812d02900a6059822208880d0088822208880db088804660981a706340da75442220699c9901f80f6013812f056811f053c12c0154182003c17b049d4f800e419406600a3040005b117c148049400704101540361d6c04ac10b02b84c1654956d04f812a944402700100ca05a40bd057011c05a8018028404d04c807504d00e501c807c057c13800300060028052058800211f0d1404c003f04e808703b418f04e419001dc178053982e126559f018417f00e80b00234009006997000d813705f1c7c010c180004817d04300e702f007344004022a008741a150385c160b000040863030184a0200000001f0500c00040005414000681c060a0b8080612010000211010206600038002400000080000000f400010000408000080018020280002150102400080f00c10000300450040900c60010100000000802c16050013c0eab2a00c00000009008000101802080c84c0000000240c15000000016)
def qL45 : PT := (495,4,8,12,fun _ => 0x405bbe45ec11bbe21cc0220203400300207a817bcd45dc3401785d85c01c83f85183a83506b81bc18c03803002001036070a194022020673c2c35017baa06d423c1185d8045be02959e85707383545d81b004003802079dbe0295881cd078c11a5ec5dc3504901b01a88a00200105087080203202c85a03cbbe223c0740e3be411c5ee5be0f63402365e81285302241905864d00f06400301ec11877c5ecad04906fa1905b40e411877e1c06085a8351dbb18012041c0f03cc0e0040010023ad05242a02300bc0505b00385bc1183ac05c5e85200d4023ea853017854c0e40505a85a06d423870c1ebd4c0f02900898807304945bbdbbbe435057851411c0e079c0f03c9db9be00f21905841ec023d480b86999e80223505841940220200d0a381781960807d0d8869860cad0520221cd40f03ca0241925b8210580a3c1ec0f03cbbe2194022023be41ebad0a3c1185f80200080161960f0631ea8530610360309aa20307b070e42a5e86980203801a84bc0f40e06585a069baa39ec0f066858466827c1185a00083987d1c2c11c05b85beac0a06998805786540207b8d8869808e4d07140f0a3c1e8709db9be00507284b9ad02f84b80f405c5e8363aa07006561e86fa0f05a00ac0584185206f81b05b466c0f0c485800206703501e0493ad1cd40f02940e07187083000301985839e8234118778190020089ea9c28699aa01a80400f0360293be405b0481ec5d84b8a380d03980201781ac0201b017c0e41187b01a81900b8363db85e41183a80380204d8291dbc2a0191c2a0f0653be00202901a84bc0e046017bdbc0f40e04c03cc1920f0651be066e1885a006c058398020523be051411c5ebaa39e81b40e28805a41180201341905801a839c0f0293be41ebaa0a3c1181b60580200117205240f40e03584b80201a84782902240e02000685040f03c81900207006500207d035071bbe418c0380200bbea869821066c0f05843445e85200ed1c03c8379cd40f03c8739be03400041400f25345ec0e40f07980200303604b98801e0580673ad01a802029017800c0507d07980b00203486439ec5dc350493dbbad01ac0f029038c18c0380300102940f03c9cd40f02906904140e202038017a1cc022023be21cc0220200200801e05865b9db80380243544c053e5be0f61902305783085305f41e808c0507687180b18803487799e81960808702e87e411bbe3ad003c0f0293dbc0203986d8493dbc0f40e04c03ca1940f01c80200187703c81a850002036817c1ec0f05002942a0020238168583be21940f3be20243542a40e3be05005860807a83185323419e87b03600083040505b45dc3504942a38800202381905b00405881f857849418a0f04c04b81ac0f01b05a21940220200203001905b06a82b41187380203783806542a00085140505b63e01b01a88a00200162d0698588de85b0dee3e19e82f069b8800205881905b28802241187b00201ec5e8491dbc1ec020398300493be45dc0f43518582904b806c05c0f03cc1e80201600b85a03439ec5e8d881780200100087d069c0e067037c0505a20241907483840241c81781c80207683c83041e8020718580340020530643dbbaa41e8500a3c118028020008000de9cd046035073817c5b80200801685800243505202200201b03c83800405e0590363aa19e85bc0f0580020368b005a0670413ad41c817c0e41185a05301587b1dbe0e00307d0c803c84c05381601b21185a054c0f07c0580673c280243501780205041c83c866802000c5886986163e0a399e80f62d06981a81b04b80241c83c83461e99e80204906400241c853c191cd06503601fe1886805b1ea84103980241c817bbe42a0200de85785141184486c84b8191cd40f06539ebc2baa41cc1180314c41186440f016047bdbbbe40506685a05ba85c11873bd4c1cc11bdbc020b007285200ea0e00f050870baa38e06141f83618801e05805d80887683b1c28669cd069bbe05405800286dc0f05818585a02939ec0506685a00140f07d03cbc2d1c0680010008023ea85240e065c1184b87d40505a01640f01e05a00200102b07d070851411877a85c0204f07a07180206682105801a80205182901e00b0021ad1cd017c5bbbe0500580080020690580080020690585be03419e988405c5e836021037c0f05840840f07d03ca1905801a80f01b04b84d00200086e85200300205582920243501a82140f03600303781983c840c0e00400205385a01e802050071a5e83640e050012c0f03ca2a20806705981b08a0021ea81a86981600203486407d40f05804281f87985800203002e8651be03425e83603464d211864002435069a0243521940f3be223c0f21940220240e05a03c80b98581e05a00202202103600303201987080300202d83605e3cd40f1ad0361db80221905800a806c058698068021ad07080806701e40f05800ac05839ac2c1181920a0028011be00f06504f83fc1187b3aa01abcd40f03621940220201bc0f01a83c8030360b005a2194022021db9be01aa0f03601a8a385a3be223c5dbdbbcd402435017c1cc021ad1be1ad02901ac11b9ebc2c1940f0653dbbbe40f435002802000bea8491dbd9eb88003a350024350491dba0e46684a21185a3be202419000e1887783a84c3cd40f4353cd40f41903cb9eb883be40f43500f21905821940220203418e25e83603498e07d83401285e85365b83483400c80305219e87385003400001580207b03460585f85d8b005207545d88700200081f03507683b017d49e5b836025605852c1180380204102965b9be034e05834076052c11834642a5e869c0f07084c04b83400203487b45d8870028010008001be07380f05b035040a071db82903400264d05306443e05d02105786dc1184c20f02905d02041f99e836060618e0e07dc5e85de4d00f06418802607785d0a3a1fe1883b0509eae42a5e8698340000258020778068d881781400305206401e01ac0f0360234021c28234021cd65b99e8240520088738590531db83485d03404de3384782381799e80206f01c84e84383503418e1be25e836003840834877cad03607785d02021fe1c6189db82e82107b05a8031d482903400203486440f0c483600b18800703603607384785318580200081c87483b838877817ddb821036037862ac2e2a01aa1186884c04b80ec0e0699aa20a00200100080001c8718388778527be03861ee1c85e02f0430720351aa19ea0581b61885a23e20e205867059825008e6a852c119858398363aa40e2c2c0504083d88703f05a839863411a2a02985803400203487787803425314c411c5ee5b80904183a83545b84280204005784965b9db81c8026428c803c823c0220201c80207483801e01781a9ad20f02945d8201cd02945d81a80400203282902c9d482903440f405c070348644031ad03600200083f87d05261e9209ea84b81b08a00280107303e81a85e85b01783440e40325306461883684b81a80205a02906d41183ae5b80202204c03c81e05601b00201b81a86987680b00201e071c05c020d88698dee0807a83b05301a80205002907684080a07205380380201b05381b01ac18c03c03002001029069c1f81a8040029d480f03607d8128535aa20f03607740f43403ce3e00ee2d31c0699aa00400081f01c87603581183a9db8a385a405c0505a40e047c0f03c81a8020398363aa39e866c0f0585aa01b01aa0e6059db88a04187e21182c9ad03663e01a80262d0d88699aa01a9cd40f03602202103661e86140f05a0020d8c5e817bdbbbe405839c0504be1e88845be1885a00241c817a0581a81b05a61ea0f06105a3be45dc0f43505302707b19e87284be1e9ea85a63e01900202f0d8869c0e05a0539ad3be40f02963e01908700200082f0698361ad05a01ae0587d0d886981a81b05a61e86721186f84b81200206985a08a04f80680206903cbdb819405c020b00525aa21882784b84080381b8538290188a385a18585007687603a9db9be01b61885a0a399e85003600201a81b03cc05839c0504ba3e68820f07c81880b81b08b05a3dbbc2c0f41903c81a88a18580405e03620f03641940220219e80f23503659e8de9c287e211c083884020693cd03c88700080a07a83503181685307c0039d486507c19e81901480386519e81918820f06521905821920a18806501f802daa06500201206985a05d41f9ea86541f81900280204886500f2350580dee2a18e64286984c00f0292192021c2e080020009720522192021cd21940f0650321ad00f0361db81900206e0b0052000e6a8de9be035052c1199e86e05201a8020069cd1ad069a1903661881e0580dee4d07140f00898807384900206707303504918800206721905821905865b99e85d82183504965b83618802404965b83618802184961e99e80317241185a00206901e1720490020c4a1903604307d83085303460818800206987b0dea5d9dbe1885d19e87385b23e06485a018c0801e05818801905818801905819e80f43505800241904a85819e81905805fc5dc0a0870010009db84d85f03505b01786e00a0013aa0650030020198581db81ac0f62d0688b005218e61882f98e0190580dec1905819e81905860e00380f45307781e01ac0f03601408700206901e04908700206d8089c286988a40f01a83cc5a458456453c51c4e449c4844644444244043c439c38434c32430c2ec2b429c28426424c23421c1fc1cc19c17415413c1140ec0d40b409405c03c013febfcbfb3f9bf73f5bf3bf2bf13ef3ed3eabe63e2be13df3dcbda3d83d5bd33d1bcfbcdbcc3c9bc83c63c4bc2bc0bbf3bd3babb8bb73b53b33b03ad3aa3a7ba5ba43a23a039e39b398b97394b9339138eb8cb89387385382b7fb7db7bb78376374370b6eb6d36bb69b65b64362360b5db5bb59b57b5535134fb4cb4b349347343b4033d33b337b35332b3032f32cb2a328325b24322b2031e31c31a318b15b1331130f30db0bb09b07b053012ffafd2faaf8af6af3af1af02ee2ebae92e6ae42e32e0adeadc2da2d72d22cface2cc2c9ac72c52c2ac12bfabcabbab9ab7ab52b32b0aad2abaaa2a72a5aa42a129ea9b299a97a95293291a8f28d28ba89286a84282a8027ea7d27b279a77a75a74271a6fa6e26c269a68265a63a61a5ea5ca5aa58a5525325125024e24ba49a48a46a44a41a3fa3ea3c23a237235233a31a2fa2da2ba2a229228226a25223a21a1fa1da1ba19217215213210a0e20aa08a06204a02a009ff1fc9fb1f99f71f59f31f09ee9ec1e99e81e51e39e11df9dd9db1d99d81d61d29cf9ce1cb9c89c31c01be1ba1b81b61b41ae9ac9aa1a71a59a31a099e99d19999819599419219018e98d18b18918498117e97c97b17697497297116f16d16896596296115b95715415194f14d94a94794614414113e93b93813693393192f92c92b12812692412211d11a91911711591311210f90d10b1089069041020fd8fa0f88f70f50f28ee0ec8eb0e90e70e48df8de0db0d88d70d50d30d00cd8cc0ca0c80c60c48c30c18be8bd0bb0b78b60b38b20af8ad8aa8a78a58a38a189f09c89a89889689489208f88c88b88a08808588287e87c87987707607407207006e06b06986706586406186005e85c85985605485185084f04d04b04884604504203f83d03a03783583383082c82b02902782602402202081a81801601281100f80e00c80a00800500200077be523eca3bbfb28035f1d9ff1c0ab28ecff8105594757ff0662be3b3ff54155d1ddfba602ad8ecff970556c767fe96f2ba3b9ff53575d1dd7f9ea3af8eaff85d5d74775feae82ca3b3ff3e15651d5ffc2aaae8ecffcc5ed74777f65006ca3bb7f2935651dd7f4e94b28eaff85c9d6c777ee369aca3b3fe39775f1ddef9f8fb28ecffe4d356c776fe7e6aca3bbfb314b5f1d9ff01bdae8ecff8dded74767fc16f6b63b3fe5b795d1ddefa28fb28eef780cb574767fe8ef6ba3b3ff55795d1ddefa396ae8eebfcfd056c767fe52e2b63bbfc63175d1d5ffc094ad8eef7844b574757ff029eb63b9fe114d5b1ddef8a96ae8eaff85d4d6c777bc163eca3bbdf272d5d1ddfdab01ad8ecffe4c9d7c777be625aba3b9ff28115b1ddefa696ae8eaffe098d6c777de6a9eba3bbef4f2b651d9ffa60aae8eeff0445d74767fe96e2b63abff834f5d1d9ffabb7ad8ecff845e574776fe668eb63b3fe116f5b1dcffa6a7ad8eef7d54b574757ff0672ba3bbdf331f5d1ddf78d8cb28eefbcd53d6c776fe6a66ba3bbdf451f5d1d9ffc9a5ae8ecffcf5bd6c757fc2e36b63bbdf572d5d1ddfeaa8bae8eaffe28e56c767fc0aeebe3abff885d5b1d5ffc0abae8ecffca5dd74777bcb65aba3b3fe02155d1ddbfa29ab28ecffc505574767fc06f2ba3b3ff44155d1d5ffc29cad8ecffca05574777fa2a2eba3bbfc03175d1ddbf9aaaad8eaffe0d4d74777bcc63eba3b3ff29775f1ddfea58bae8eaff85c656c767fcc42aba3bbdf4b2d5d1d5ffc231ae8eeff4cc5d74757ff0a7aba3b3ff277b5d1d5ffc5a7ad8ecffd55c56c767fc202aba3b3ff276f5b1d9ffa20ab28eeff4e45d74777be725aba3abff894d651ddfeab8bae8ecffcc85574757ff00bab63b3fe36155d1d9ffabb8ad8eaffe00e594767fc0aeeb63b3fe0a155d1d9ff9c0aae8eef7ca4b574777f86e2eba3bb7f4a0d5f1ddbf9406af8ecffc55c56c757fc2e7abe3bafe9d295b1d9ffa6b8ad8eefec54f594757ff1a9eb63b3ff56155d1d9ff02baad8eeff02c5d74777deac0eb63abff89315f1d9ff2d0aae8eef7cf4b574767fe2af6b63bbef28075b1ddbf9406ad8ecffcf5ed6c773fea6aeb63bbfb273d651d9ff1cbdad8ecffcfddd6c767fea6f6b63b3ff3f7b5b1ddfb8d94ae8eaff85c6574775fe981eb63b3ff4d7b5b1d9ffaabcad8ecffce5ed6c767fe8af6b63abff85535d1d9ffa3bdad8eefbcad3d6c767feaef6b63b3fe0b775d1d9ff1cbbad8ecff815ed6c767fe52eeb63abff82375d1ddef9c8fae8ecffc55ed74777bc0a3eca3b3ff536f5b1d9ff99bdae8eefed300d6c767fc042abe3b3fe24155f1d9ff99b8ad8eaffe38e594777be665aba3abfe17295b1d9ff8abaad8ecffd10556c757ff00c6ba3bb7e9b4b5d1d9ffa5baad8ecffccdbd6c767fc6c2abe3bbfd47175d1dd7faba2b28eaff85ce574777fa8a2eba3bbfb19155d1d9ffa3baad8ecff8e0556c767fe4c2abe3b3ff53715b1ddf795a7ae8eeefc9ca574767fe602abe3abfe171b651d9ff9e0aaf8eedfce51d6c7777e72a6ba3b3fe5a155f1d9ff94bdad8ecffe4ca594757ff066ab63b3ff4a155f1ddbf1c9ab28eefdc546d74767fe52deb63b3fe11795b1d9ffa30aaf8ecff82dbd6c776fe6aaaba3b3ff4b795b1d5ffc01cad8ee7fd355d6c777bea65aba3b3ff3d755b1d9ff99baad8eebfcf51d74767fe9adeb63b3ff396f5b1ddbf059ab28ecff98dbd6c777fa9a2eba3b3ff476f5b1d5ffc08dae8ecffd55bd6c767fe7eeebe3b3fe11715b1d9ff93b8ad8eaffe151574757ff046ebe3b3ff3d715b1d9ff2eb8ad8ecff8e5c56c757ff0a7aca3b3ff277b5b1d9ff9cb8ad8ee7fd2d356c777de3236ba3b3ff45715b1d9ffa30aae8eedfd58356c767fe4c2aba3abfe17395b1d9ff9ebdae8ecff98dc56c7777e4e52ca3bbfd27175d1d9ffc9a9ad8eaffe222d74757ff0a2aca3b3ff47715b1d9ff9fb8ad8ecffccded6c757ff0256ca3abff854d651d9ffa90aad8eedfd30356c777de980eb63bbef2807651dd7f9407ad8eeff4c45d74757ff04b6ba3bbdf271f5d1d5ff0b9aad8ecffcc05574777be963eba3abff812b5b1ddefa98fae8eef7d547d74767fc0ae2b63bbdf571f5d1d5ffc19cad8ecffd15dd74767fe942aba3bbbf4c0b5b1d5ffc542ae8eaff85ccd747777eac16b63abff85275d1d5ffc63eae8ee7fca04594767fc082ab63bbfa034b5f1d5ffc73eae8ecff840556c767fe502ab63b3fe5d755b1dd7f9eabad8ecffcf8556c757ff0a52ba3bbfb28035b1ddfd9e8aaf8ecffd30556c767fcc42ab63b3ff56155b1d5ffc031ad8eefdd58156c757ff028aca3abff8345651d5ffc2a2b28eefecf49d7c757ff1e8aca3abfe172b651d5ff0babad8eeefca4ad94767fe782aba3abff832b651d5ffc795b28eeff4a45d74757fc2e4eca3abff83535b1dd7f9eabae8eaff85d3594767fe9aeab63baff41575d1ddfda593ae8eefdca53594773fe9e9aca3b9ff574d651ddbf9caaae8eeefd4cad94757ff1a9aca3bbdf151f5d1d5ffc21cb28eaffe021574777ec0a52ca3bbbe0b29651ddf7a095b28eeefca5156c757fc2e52ca3abff8b4b5f1d5ffc094b28eaff85cf594775fe7e7aca3bbfb274b5f1ddbf9ca3ae8eaff85c5594777be7a3eba3bbfb1915651dddf94a2b28eaff85d2d7c776fe6672ba3bbbf2b295d1ddfea98bae8eaffe0d2d7c776fd3696be3abff814d5d1d9ffc9a9ae8eeefca4ad6c7777e4e72ba3b3ff4b7b5d1d5ffc1a7ad8ecffe4d2d7c757ff067aca3abff8d4f651ddbf9998af8ecffcfdd56c757fc2e4ebe3baff280f651d5ff0b8aaf8eaffe155d74775fe8aaeba3abff89575d1dd7fa3abae8eaff85c6594773fe96aaba3b3ff456f5b1d5ffc1aaae8eaffe255574776fc0a6aca3abff81335d1d5ffc2a3ae8ecffcc5e574757ff104abe3b3ff93155f1d5ffc742ae8eaffe096d7c777bc223eba3baff45575b1d5ffc49eae8eaffe316d7c757fc2e7aba3b3ff52155d1d5ffc0a9ae8eefdcfca594777f4fa96ba3b3fe0a15651dddf95a9ae8eaffe352d7c757ff04c6ba3bbdf471f5d1ddfe2d8bae8eaffe04e574767fe96deb63abff85395d1ddfd98a5ae8eaff85d3d74757ff029eba3bbdf87275d1dcffa6a7ae8eef78e47d94777be523eba3abfe174d5d1d9ff8a0aaf8ee7fd2d3574777ee369aba3b3ff2815651dcffaba9b28eefdca53574777ee669aba3abfe174f5b1ddfe9e8bae8eaffe322d74757ff129eb63bbf715335d1d5ff0ba9ae8eedfcc4cd74757ff0a66ba3abff845b5d1d5ffc42dae8eef782c7d74777ee5266ba3abff8c5b5d1d5ff0b94ae8eebfd5cf57c757ff0252ba3bbfb273d5d1d5ff0b93ae8eef7d347d74767ff264eba3abfe17155d1d9ff050aad8eaff85d2d74777f63296ba3b9fe11575b1d5ffc0abad8eebfd055d6c767fc16e2b63abff89575b1dd7fa3abad8eaffe2d5d6c757ff0a8eb63bbbf27295b1ddbf999cad8eeefd4ce56c757ff086eba3bb7f55395b1d5ffc79cad8eaffe054d6c7777e56a6b63bbef2b415d1ddfb9402ad8eaffe118d6c7777e5016b63bb7f33355b1ddf79a8cae8eaff85cad6c757ff0656b63bbef412b5b1d5ffc71bae8eefbc646d6c757ff0236b63bbf74d1b5b1ddf7a08dad8eaff85d056c757ff0282b63baff3d3f5b1d5ff0ba0b28eefbc6d0594775fe7e82ca3abfe17355d1d5ffc22ead8eaffe04fd6c777ee527eb63abfe1753651ddfba694ad8ecffe4ca56c757fc2e2ab63bbfb19155b1ddfd9e8aad8eaffe3c556c757fc2e7ab63bbfb273d5b1d5ff0ba6ad8eefdccd356c757fc2e66b63abfe172b5d1ddfd938cad8eefed2c656c757fc2e96b63bbfb274b5b1d5ff0babb28eaffe022d74757ff0872b63abff8e395b1d5ffc43eae8e)
def qH0_45 := lw0 96 557 10 14 10 4 (fun _ => 0x22206382220671c7b0889cf7140c18002200fb02a4114059c22202702220178222021dc220889495653415408881a3028c897732c03b029c16206a1cdf0489822005805095700e005b802b02980e8655c02204601680888068019422201080cb0889cc0031422232980ad02958f505e807902b808b088815801980d862e817c003c22200800c1013c22200c416504a1c9493e822203280b0019005a08880f0088801d043813103340c201f803c00bc0c300780da05440cc0412916088852308880e4406418955b408f61ec144009404602cc22205744af028817203700f402280ee025812405dc222034c0dd025190e260c12c03f00ab043c11b0888017024c4f4a5fecd8088819230642221614137066418174380789434040066003a02a00e27288047044817f051802472f415704140ac02bc0fe11a805b04ec0c80888086038c22208899540454422088810a05398cb00cc043055959f0175d06245996503e000d01d403f04b406371e9c71020002a03f4149088813000b0222730406a0068191049806d345048bb06403400300a102c422201ed89006354b70158152043250463000e605644df33e80a00130028056c0deb4dcc2f0418129027401100f80aa02e8045060c222023001b652406e0164194068011f021401f34301a4015c1437660222654808100f5c9042f5cf500b80b60508090b4300732694222008c22202c82220208141025c16d0889cfe95e413c03ce511009c0b401382220268098164597e73d019001b057a01ea57608880b704c814fa33dca5627c135088842105d4052051c127088810102642220180222b4a013403b0497054d8f7027816b00d406f005002d088807d088805f08881170484053040a154048e50c026c0d2088818655fc222088885d051407f01d856b6510103648c08d11e6198127c054045806b069ecac02248b701d04ba05540910054072046818702fc12b0302cfa088817100a414d044402105f6d52052c19a0184222623801900dc0d190640e10124062088813e53e00d703dc15004b84d103c80fa0038222088806962f40cf00c812a01c017075440f9067c11905d809f0889d160154543088851501dc04104400c605f804b088803903240840481906088822200e004404fc10808880e9b4ac09205aa4d5009857e0889d4908880ed014411d088822202f022202f4048053015e02e0136039c09501600eb751001091380120354185037c01302e422200c00d4063c22208880ea01342220695981058c1070658197059001c012813312c806765540f1088808e04e5d5211980f508880830629872845817903bc0d904340ff017007108880bb0888222058415c08882222280b018090107300400048370395f01188248070009701c0000c030a800028874580006c4701c110080800498014b1034000f4a51480c00c000042e6e808004151881f004020ec560840102c05014c10a803148000a0064343b0040529c110102a018132a8910184512ca0004000082e3a85b0786001410)
def qH1_45 := lw0 52 127 7 11 7 4 (fun _ => 0x1d41e8790780483c80e0dc1e430b220f20741b0790ec1e43c87204c0d03c8410f21143c8790000900a05701a08c1f02106a300050790f20ec3c84900e1502782d0961640b8470521e42900b0e20680206a0f2134178620361e41381f0f2da43806c002d701f8151881383a02c0baf180b0380da0a8110630ca1e4340790721e42f8730cc1e40784000414c0607900a0600f3d80d60a02535d65c15828006012144018690f23182a8110320202606f040818008044010004000100808306040130200003000400104000030c000030400002060001300002020218382)
def qL46 : PT := (173,4,8,10,fun _ => 0x7ab8638398171e8000ccf00cb0a00904783881d1f40098628f884697b17b0d52b50470730467ab03913401d04717703d0d493497a84696e0010d507b0470d517b16eab514504787117a87f1638620081a58382c062037a05a14d96faa983891208f86200996faa981790a84670a0228d403c00e00c16c0d81a206b96faa987b1128460f80780e406c03c16c06a08983983c06c7aa14c8f881684697b16f10aab504717b2b50467340648d490a84697a8d497b03904717ab0b8638389f517a008d27838b0b01d1f400186296e90b2b484717b2b504717703d0d416e07815a06c03c1f006b8211f484683880e9e80180d487a81730a84697b87117a88f86200075290a97a84673407c8d50d517b17703d0d48280010d596e08817e0841300d583917ab0b1f4009862b0b87b8631bf17a008d2681684608f04717a7aaab400d14504796faa983891200014dc610391f504608583981606f83c7aa14c9be97a07c14d07b0390b4b0b04687e0010d596f87a17e0841300d5aa98398169e986200070a83c00813e0e41ec06a08987b12186297a83d0d596faa981708e84703904717a70a0268d417b08f04700e17786200904683c8d500c07e00986304683c8d47350469768d484670b1cb0469768d484707b04793517a8469ee84747104670a81607e84697b96eb0b8398b400014c18c86583c7aa14d47104783986308e97a13104703904717b07b046b0a73504717b0d4131047c619ab9348461e614006c0480e61c616804683d0d41a40920381e60e61401c604673402884697b00e01c00986304707f8638398171e8008cce0e7ea80021f40a403c16806b03904680e6b401887307b1530460a900f862009047144ab504618d86583c7aa14c8f80010d50211530470a808f04696e0010d487a95a8471447ab04618d8640947aa14c18d86583c7aa14c87f83917a1f40098621f484683890287e1738627aa6b484707f83881d1f40098628f80010d587b87186317b0c0d26809839816b0b1f4009863c618171f484696e83c0d488f83990b86297a8168478171f484696e95a8470730478389f40000d48280010d59ab12000014d2b49f48468212b49f484670b1f50471ef046b0b07b047039046ab51e90471f50471aa08f04600e11e0a46b406a87e0010d51778388291f586200917783888e1f586200917786288f1bed2680880e0648d587117a88e1638620098718209f40000d41ae00c1a40d807873406b87b870977163862009a21817c700187aa14d8a987b83917ab0a0098639ab9350478209f50479aa88f04787b90a97b0478398631f400070b87b86383917ab0a0014cf96f87b8b4b0b047816b0a9f5047a218165980847aa14c6b5046b0b017046b0b0170478388291f586200883c8d503d0d418d86583c7aa14d96f87a17e07c1300d410214008e1981da0d58398167aa0ca14d839a2181608583c7aa14c10383807876e28e1a40d400e06c7aa16c06b821c700227aa14c00e18a03c0a40c806b6859362d815ed735bd6557d5954d4f52d434dd2946d1142cfd3cce5364d1324c32f4b72ccad27c9322c851fc711ac6115c4b1143f0ec350bc2305c09013fefd3e8f83d2f2bc0eebaee8392e2b86df376dc36ad835cd4b4ed2b44cfb38cd32ecab26c7310c1b02beaf6bc2ecb9ae2b7ad6b1ac2acaaaa8292a0a7e9da7099a6095a5092a448fa388ca2887a1283a027f9f27b1de749ca709ba6d9b06a9a6679986418a6097c5e1725b9685915e5514e509364a9244610e400f43a0da350ce320c02d8a827896228862007a1c06c1a05e148460f02e0801603001cbf0608ae8ecbf8385574773f40422ba3b3f77405651ddeb028fb28ecfe808557c766fc1af6ba3b2fe0e15651d9fbbd02b28ee5f840356c777b4065aba3bbf20403651d9bf06b8ad8eeee8280d7c756ff1472b63bbb6040b651ddd70305b28ecfda88156c747fd4656ba3bbe60605651d1ffc70aae8eafee018d747677edc16ca3b37e0d755b1ddcf058fb28ecefa882d6c7677ee016ca3bbba020b651dd9f059ab28eebe8380d74776ec081aba3b3fb74035b1dd6f078fb28ecef8285594747ff102aba3b9ee06115b1d9fd5101ae8ecfddd81574774fc1c1abe3b3bf7a0b651d9df5105b28eebe8380d94767ec082aca3bb76040d5b1d5dfc412af8ee7d8104574771fc1c22ba3b9df1e115d1d97f07bbaf8ecdf835ed6c7757c1c16ca3b3fa037b5d1d57fc631ae8ecefa882d74767ec0af6ba3bbba0a035b1d5bfc512af8eebd8381594747fd464eba3b9f61005651ddf50301ad8eebb8183d94774fc1e6aca3b3f6a205651d9bf06bcae8ec7f8405574765fc281eb63b3be0a155d1d8ff0a08ad8eee782cb574765fed81eca3b2fe0f6f5b1d9dfb605b28ee77844b574776dc0c1aba3b3bf6c0b5d1ddde058bae8ecbfdb83d947757c1c16ba3abfd7e635b1ddfc018bae8ee3f8403d94777e80a2eba3bb760535651ddaf0696ae8eeb783cb574777d40c06ca3bafc0f175d1ddf50301ae8eefb4645d74776dc0c1ab63bbed2b175d1d97fba07b28ecfe80855747767c1816ba3a3ff80155d1ddbe068bae8ecfea880d7c767ec0af6b63b37e0c155d1d9fd01bdad8eabfe318d6c775f41c06b63b3be0b7b5b1d97f07bdad8ee7e8400d6c763fee022ba3b1fe117b5b1d5f7c231ad8eadfe298d6c7737c1422ba3b1ff6c115d1d8ff5108ae8eed7c783574777740416ba3ba7e0e0d5b1dd7d0701af8eeed8102d747775c0c16ba3b3fb78035b1dcdf0805b28eee7c782d74773dc0c22ba3b3bf700b5d1d9bf060aaf8eede8300d74777e40806b63babe0a0f5b1d9fdb701ad8ecfedc00d6c767ec0adeb63b3f605755b1ddeb0296ae8ee7f0445d74766fc1adeb63b3f605715b1d97f07b8ad8e8ffa880d747767c141ab63b9f604115b1dcdf0508ad8ee3f838456c763fd4422b63bbf204035f1ddbd0601af8e8ffa882d74773f42006be3abfd7e635d1ddf90201ae8eef98101d6c7775c140eb63baee0e075b1dcf70803b28eebd8103d6c774fc1c1aba3bbe604075d1dd770703ae8eafbe118d74777b4063eba3bbd6051f5d1dd6f078fae8eeed8102d6c7677c2816b63b3f604155b1d5fbc131ad8eaff5f8957c755ff18b6be3abf782635d1d5bfc531ae8eabfe316d74747fd4422ba3abfb80635b1d1ff518cae8e)
def qH0_46 := lw0 27 59 6 14 10 4 (fun _ => 0x5bc12505b019704bc11e0888161068422206980d6066c22204e013a06741480610160068816603680d00568182052818b05d00a40338100057c168088822208881400678036031c169049c0be0618195060013d03d805506200c4063019305cc10905ec0e505e1e4c80073c004d00000018000b00000b200084240)
def qH1_46 := lw0 30 95 7 11 7 4 (fun _ => 0x6b0f21241c87903a14c3c86c0300f42500f0ae1e5ee06a0b20f83c84e06c0800805509a1d19704602c0fc3803075c1000f84205e115a28350ce0dc0703a0883182b03b62c180348c40b016c1a01c6801702402d05c0880b8250260c82585f0ba1841504104c06c3283c78a09c3904372c1e4238240b40cc2f35c0c818c1882b1b00b02060c08028006cc831754c0f0608400004c5851400007101c901)
def qH2_46 := lw0 1 3 2 6 2 4 (fun _ => 0x4200)
def qL47 : PT := (1,4,8,2,fun _ => 0x1ef9ea804591efc30aaf8e)
def qH1_47 := lw0 25 31 5 11 7 4 (fun _ => 0x378760dc0a4710797c4188368f51e6dbdb101e7e21e43c8f10ea1c43c8f60f21e58f0ed6e22a439bf66ec000ce00140000020080000000400000)
def qH2_47 := lw0 3 19 5 6 2 4 (fun _ => 0x284e84104108c8410010410408410000)
def qL50 : PT := (82,3,8,10,fun _ => 0x21eb3d064c406341eef90c6190d37aaedc1fb85863078500860d52ddcd55483902c1fc3197b08e35385ef81480f35a06a044630d2008c40b002d14c0f01b05203cf541ac3d051755cd55aaa8a60640231ea3a1c2b7cc703ba188a617acf5c29bd8630784306a76ecf5c282610c078353b703902d858d11a5d52c28a3046edc0a004735078de8af0d42ed9e83200831823bd5862e1611c6a76ecf58841e140df04306a76ec700a39a8622181686a76edf20e0049aa11dc2c3114d08e35068820e171c1fa86234c5e8d101a0106939a0d5070024d573421a18c238d4e14688040230c5ea8d370aede1eb3d1bed69aa5855c82d011cb71461a18840b7352f54c1a90472dddb8a3064c41cd37cab4a6011cb776f0f41439a05b5694c02376e0ca083101a2e686955a14608e5bbb787acf4125856b40d85a02376e1519eb100c5df0de81e0d4ede2a032820c4068c1e1a51a8530c60090ca0f3d514d070024d570b07a350a676f1521eb3d06431808c318471a9c2cb78b451c5a0231302ee0e31019a11c0f3d586229a350d376e2059ec390082f41c83f862e15be06a87029c0277c83cf54353b70e01501fb10009078deb9a0d50724d0040e6f545a06a37a011cd38583cea4350bb8383a003bd570b0c4534235271a9dba30816c2c68f5406b078290d20e62999e83706b02d85c040043441b01e86361469bd56a90f59e835838011858bd7ab61618c230d92dc1bc1c8160105075430b0785343d67a0d405bd517b8e0b003630b0c45a4b776f0f59ec10621013be0398700f05006a76e1cc2203f06a2f59ee38b0ad680f43114e1b19e835838f545e83603c2b4a39858622d25bc3d8b41701189896eedc1ec0b617d531c03528e616188b41410724d00476e23c6906a96f5500202c620018640a687acf5ad6387ab0c4c286c4ce25e5bbb787acf41aa308390785058506c23c3543d67a0ca083101a5df2ad2e40462de1eb3d6162f71c0357aa616188b41850f59ec0b6b434ac2ae4046e681f835838c2dea86f8622f611d854ce1e60e5108160102141e7aa2981f835838c2c668bd03d615eac3114c34e5bc1019c0121c02d7341aa1ec85140010660ed0d43383601e7340d65bc3d17e010210980d42d20e3d507ed68c2c31846149d4c3d838011ad58586308deacb70d81a2aa43d67ac70164bb8d50c46438567ac4005869ef8078168bd0d4cf41ac1c6163a05e83f862f56119850a4011cd35a8703904c431846ea5dbb3d17a11c0b0048730e2188980d40bddb844072c405e8a008e0121cb5a86229a1c07987b0e608004ef90e0398e40d434a1ec1018fdf0118bd1c8d521eb3d820c40020bd872f57be4318090e0350d20d1552083108163463441e97a2999eb1c0d2e14168bd0d4e160f06c1402f435310016e6834c1e6f82285e86a96edf2aa41c816011c28478632f4534238d43b85f06887acf71c38518f0c45e868aa90418840b1a4346d48a397a08e5bd54816011c2e3897a29b0cc06f9bbae9b86dbb4ac9b0abbac6a9a7a96a3a839ee759b26596e5191e3e8d22a886178460a7fdf97b9e076dd1729c36e1ac6799161d7b5b9605514e5093a4c92846d11418fd3c0e8370d4334c8304b72bca22648d210781a8611644b100390cc2a0741302000dff08ad8edff93ad8edff9fb28edff3eae8edff1cad8edff45ae8edff8db28edffabb28edffa5ad8edff8cad8edff95ae8edff99ad8edffa6ad8edff9ead8edff8aad8edff94ad8edffa9b28edff1bae8edff9fad8edff2ead8edff9aae8edffa0b28edffa0ad8edff8dad8edff95ad8edff8cae8edff9aad8edff05ad8edff31ad8edffa2ad8edff02ad8edffa0ae8edffa9ad8edff9eaf8edffaaad8edff9cad8edff98ae8edffa3ad8edffabad8edff05ae8edff08ae8edffa5ae8edffa2ae8edff8aae8edff01af8edff93ae8edff9eae8edff8dae8edff94ae8edff2dae8edff1cb28edff99ae8edff01ae8edffa7ad8edffa6ae8edffa7ae8edff9cae8edff31ae8edffa9ae8edff1baf8edff2daf8edff42ae8edff12af8edffa3ae8edffaaae8edff02b28edff8cb28edffabae8edffa3af8edff8aaf8edff93af8edff98af8edffa7b28edffa5af8edff05b28edff8ab28edff93b28edff9eb28edff94b28edffa6b28edff95b28edffa2b28e)
def qH0_50 := lw0 211 427 9 15 11 4 (fun _ => 0x1ca00bc055812401a403a402b8094001004d9c8a009c020001bc023810b02c4038003a014802e005700b9803e014400ac09980cf01ae04a807a00df70ee04400bb013d00be023448f8165022a053009c808862500540058814602d401200a0807e007e022809d80b401460190049005d01d0008c03a81450214009002f00c511c2020c09080840210049c06700c4000c02f40308120020602c001900fc019405c801e0018020e001d8978152017cc3dc03e816102ccc431878802001a00154036003371c201480a7016e02a20590077800502ae00e009630e0004c05b004380e400da05dc03e017b002004fc049817d000400e400700800196e47c00a00c6005a257c0828013005403a80b7812602ea01dc01a011f00000158039817c001401e401b800461fc018007b8003120802b005c007f013a046405980c1027801ec02d004e1222020808e00b5024403b000f81430062e52c09a814210ea055006180e1024a047809a002e00d2009c06680fd0050e42c0ae810d0134028007580b70230019c007841b0034059c02500ed02f2c1d589f004c00c4058c0b480ff61460438063812d0236038c04f810900520468042b10b0260026c057005900b8025403881140074c51c005801b01dc04e80ad811600a602e401d80dc015000b0094001202e80260073841b7250014407900f80060011803d015a0102041800080e202b2007008108fc0132005c050817a0180055800e80c2026e00d400b00f6015a24c407c80d4725e025c04700bf00d603f98a5810c72aa043d88888ef015e00840208096025604a40a5007000cc01c802680760246039804800fa029e0331c9180220270056002a0104004a00340210009714624f8043007801b603ec09700b2022e00f400c812f0836106c02180f50288035820d808b0088016c027816d0190018c08e806e00d400540b40178026402e8069816b014a054dc89014000d0012405b017101bcc3cc0448149028e05780a680dd01b4024402c00bb0224057c09880aa011802f007800f10192040404f00d50296012c052013e6214044404780a901e600300b0003600ca243000f0113008001400088155008a02984a380d801b2029c068800200102070001f0200000000283c0c000a05028000000026010e028a600020080000000500005001e41a2c0400c02000e8840a00019004e110702026010080c0201010401c16000440002000002220000080023000d80a010a800009201808d62d0000006001b8b82e01048001c00018480e1401004069d0280000032d0142a0e00044060000000120000014421b15858000900800160200004080301000061000804200208820000603040d4180300c3a350004c04000080002080080c080000000160300808b200038043e0105804000e0181c282c0a00800020500c00191d0180a030002c0001030087c01)
def qH1_50 := lw0 205 640 10 14 10 4 (fun _ => 0x12a073dd70070811f05b829d05f000604c002506601e413cd9ea014801803c41a9078197004500d6159829d00fc0ee00cc0de331815306f000e03b41ec0518162064c1500685c7717b406000581e704c5437072c0df074455614c41b0013c1da05580820a745d4077429d01e41d9257c14b0a7451d02e4015042806b025c16902741b401a029d04881dc0a740a400f41630655cfb05840431548574158c4fb03b01b802f81040279897059c1cd023c15903e81bd74c410d153c1a6014c14407840ca031c17564345e415200e605240b165cc188124413904b415f010802c063429d0a7406e03e59e404b010e04cacc504ec0a806901401404019072590e152c1071744518036410303d80bf02e812104d81df128405b02159b6002412503a0034931411506280e963d00fe070408a026853c64100a900981b10470105007805703d00c304fc1e204f815106880c802bdd8706e4004077817a03381eb158010b039405f01d010200f801d13f193101e029d02845cd051c02343140c203600f2005207d04201240520020009c0cb0598061156029d0375de401ccc74045c29d150007c0a741d803bc00701884c301581d39215d0e05bc04c070c19b02981d287a805465f0184005c112012d8cc029c1c6038817902b4519079805d071014315500f5020d90901e9d0800200fb157408060e8067025400c022005a061d430a780096002c11806401d6642015803301a515b000f06301d00170138735405e027c0d4725c16a03e050a02f00b001400e705b401305941280384177176450716cc19717481b2148419f67b41520444021044c0a000d807100280ac01dc16b0118011b2b80f7000c12b0514135065810106800e405f403107a810f02b803706f808d93101c8046814d05c412f052801c13d415e0a7403211edcf505e0137034412e0a74099073808b025190700d40f305c007e024d8f501600a306d814205f811b01bc03c04400b2053017f011d08e0608040011004515664c20754109071c12714a055710e99a2055c1ad036c505060400d25e80b401d81db06181d402400bd0138022020402b177c172067001a01241aa06d416800a002a01b00d7069c16063ec092034806d6404005026c02e06e8134078c029060012603f40ab02100c974340897689dd504580bb122c1c0033403901440da04740aa02d413d63880c004e810c048c29d05b003807140660a7406a0a741ab0a740a5060c07001ec15a00e998700ec0f0012029d72840590a740dc1410000073001b06b814103180fc0a740eb0a7401007a029d056c0ff026017306ec14e012815c059006905ec0e016445ca067859a021808c04cc29d03a9d7c066987a024407f06fc106057402f0644185063c1ac01040b7034c0c1021c00101f41d70048063062590c04781b300c012902cc0a203145e6651007576d8055055010014301b702d81e9009018b157814f035404d064811906640c4038d9ca0a741af0a7409c034018e33141a802380b8055588c000819d25a4176007c194068c12000b406415a41ca07b947f01c813c07940cf0194010340015c63000310540f0f828034020140a028000180001800054000002d0000700003035570ec000181d0242602806010141381700003000a2030000081102c160001f0001000425048020602701c2d000310d40006c000903301c020281c02c520740000004008001282a12801000010480203c18000040800000c190b4200040b000000080306c170f402014000dd3f10c30048010283c02c09034020406d0240301c010045b004d10741002411064530080b0580419400048000300c0000000c0f0001000c3107c0031013000000483b0c00904c00008770c8100500002c120b0040040a00000114e7008020000000804034310041517c0011c2300401)
def qH2_50 := lw0 20 45 6 12 8 4 (fun _ => 0x14809e1350ae0ae0020ae06767400302302a07802c60708700601b09a00700e09705304703f0040510741760000ae04107200168000818d00501908002b00f05d0400ae040001340088482009004043000100)
def qL51 : PT := (42,3,8,9,fun _ => 0x20e4d508e28e18c231a4e143546aef80783543d82028fbe6381230c45ebd519d2dc1b41c8161ce18f5403c298c2c23460a4e0e4d508f0c4618918462983546a07a02ec282317a33a1e8178210e4768a0ef90e2188e40d508d182677aa33a5bc3d06d0720583503c1cfaa41e4606161880bb0ad6811bd519d2dc3843d8160d8297544616145702387b0701b8367aa34a1886a11f61611a304cf0726a8ce70b0c45301e846a4c3546a96f5521ec10816e69c2da917b2f4118ce96ee6a1ec10461df06555a15e08dea8ce0e10f60e00217a1b11841e0a5615ad01e862339d4b9a87b040768bd0e10e61c77c1b9079ad2308622ee1ec1c821df2188a37aa2461186a8d4339cd3857abdf11841e03c1a85b847ef956811c3119ae16ad02316f0c40839aab408c5bd5a04611dcd77c83c2446906aef9d501c823ef82ec0f06a96e0fc1b83683902d18585ea8381cd41e1690c61ec1c17a0dc39c1eb0af545743103c152188477abdf2ad02300e01a18f54b0a08c0e754b0a08e5bd54816e69c2e3803d0c65e8bd5271a81ef54b0ae68118bdea811c11cb7aa9072058478632f451c2370a2f63503d86207005bd5b0a08c23f7c0462f7be0a383c2445e86a96f55205847c710c448cbd14c2f63577c1760783500bef82f40f06a039df0118bd0462f423d76a750a44e65f2a8dc3210fb7738db0cd5f2b944994a23d12853f9ecee692f15ca24d208f0702c1288436100601c0600dfb02ad8e9ff0aad8ecff08b28ed7f07ae8eddf05ad8e9ffbbae8edbf06af8edfb02ae8edef8fae8edf703ae8edbf06ae8ed7f07ad8edf703b28edf703ad8edfd01ae8edfd01af8ecff08ad8edbf06ad8e9ffb8ad8e9ffb7ad8e9ffbaad8e9ffbcad8edfd01ad8e9ff0aaf8e9ffbbad8eddf05ae8ecff08ae8e9ffbdad8e9ff0aae8edfe8bae8ed7f07b28edef96ae8e9ffbcae8edfb02b28e9ffbdae8e9ffbbaf8edfd01b28eddf05b28e9ff0ab28edef8fb28edbf9ab28e9ffbcb28e)
def qH1_51 := lw0 127 258 9 14 10 4 (fun _ => 0xd2c9d02ba09f823208703a40ca8102074826c07e02880b20316248833809d039e0a103b00de12be0cd838409601120ef0a4a14e81be2b63b4407381d604f032c0b983b208780bc0658a962a03a8cc9900b20e208b827e01c828c81ba03b023a0df02d00b003a20a400fc07781c40e002f44bd0a582ef80d00e683a808c02ca0f4816c02f830e06b02980d7833c0a30296c9602a80eb02be29701e8097034814e837a0bc853a0d680860d482da08f8280082830808a03be14e836814e819e09d82d607300740b600b8045828a09083000be02100c682240d282a20c8015a07802c60770916ca300800e482500f6038ee9701ea03d820e0c8819209983d60cf81d80948a900af031c09203dc06d036e0f682000a80218c9702220668ba807f02ae089ba1c06f0a300f301fe0bb82720f081f607180cc0c281f20e6036c0ba01da2a301e60b381940e9ba580ab03820ac830605f033402582120b800da07082fa0cb829206b834e0ad03ba0e8030c04c024406900a80b302a40d981760bb02d40e503ce294818e0d880e20a702ea0ce82680e7028e0a7821a0ac02f008a812209e020209903440c48a8a29e0262090020806882340a5022c0c103320bf837009281a60c90180008018f00003008000c0100008180001000a04500800043c0081c0000000500c3e00800420112810200202000000605084021e160544a010426c1401000d400111100c080100001182000018020000001320004814021a00004cc10018105001018045811058209e5802800120d0000006050000000220004c3e0000074020000020069e00800006405800064d)
def qH2_51 := lw0 62 196 8 12 8 4 (fun _ => 0x8f06205f13807b00b03d0a604412403c7a001409002d0ae0a00ae0a20ae0ae0ae01106b06a1a40aa14109402417b01002100902c07a04e04107606405608114418d0330600200251a704b01304f0ae18509803914a03108963102e05900c0320340480ae0370a801e09613108501f07506806103b0a303074208600a17614505a07002b06708c63805409107306e15009309d0166246a704604c19507106d09562b08e13002907903e6a008806926405501500d09c08b01d06605308a09b0ae0120ae71c0170a104d05101a05b09f09204203a7a71a905805207d1a604304502716c0820a41290ac02a05764201c0260ae0a907f09908317c03662507e0a703503804900e02805e06505c06c79202208d02f0a51790770630ab08704a01806f05019207c08400020044a90c000102001112060016052c001e150802040565281400000400020d120806210d05261210180001061f1842002200001987020a0500100b0a)
def qH3_51 := lw0 1 2 2 5 1 4 (fun _ => 0x80)
def qL55 : PT := (5,2,8,6,fun _ => 0x16eaa07a0e02005ef81897a118d45b87a080161cef81c6a8188465b87a0e017aa062c28461e838081abbe062118d4184cda248205ffb28ebff5f1d7feba3affd6c71ffad8e)
def qH2_55 := lw0 33 101 7 11 7 4 (fun _ => 0xc01c0400fc1681f090c94270450082958b0420200d80503305c0698582a03c0e1d288a02c0842783e0a20d01e81166006c0c83b0120e40383101e1002338a0060b04605005209c0600b0040bc128477600202180d0561f00b87c0601240707c0002542207c0480c80081504c0dc1104c03a104440280241280983a02824c118050780d42680616012d85010400104222879202000050048000140c7a85200b242a04f0a0804081)
def qH3_55 := lw0 14 61 6 10 6 4 (fun _ => 0x26090070140c055971381b1680e0842a058120780d1181409c170180804c0f18c2a0885407c10074110680a070000a82a0642a010290a8180802a09457768490259a0042375c0b0a00200c2a84b680153e050031d6102)
def qLv : Nat → PT
| 32 => qL32
| 36 => qL36
| 37 => qL37
| 40 => qL40
| 41 => qL41
| 42 => qL42
| 44 => qL44
| 45 => qL45
| 46 => qL46
| 47 => qL47
| 50 => qL50
| 51 => qL51
| 55 => qL55
| _ => ePT
def qIx : Nat → Nat → Nat → Option (Nat × Nat)
| 36,0 => qH0_36
| 40,0 => qH0_40
| 41,0 => qH0_41
| 41,1 => qH1_41
| 44,0 => qH0_44
| 45,0 => qH0_45
| 45,1 => qH1_45
| 46,0 => qH0_46
| 46,1 => qH1_46
| 46,2 => qH2_46
| 47,1 => qH1_47
| 47,2 => qH2_47
| 50,0 => qH0_50
| 50,1 => qH1_50
| 50,2 => qH2_50
| 51,1 => qH1_51
| 51,2 => qH2_51
| 51,3 => qH3_51
| 55,2 => qH2_55
| 55,3 => qH3_55
| _,_ => fun _ => none
abbrev qB := blockG dead qLv qIx rotDS
abbrev qM (k tm s a b : Nat) := @blockG_merge dead qLv qIx rotDS k tm s a b
set_option maxHeartbeats 0 in
lemma qc32_0 : qB 8 0 0 1=true:=chunkBlockG (ar:=9) (by decide +kernel)
lemma qa32 : qB 8 0 0 1=true:=qc32_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc36_0 : qB 9 0 0 48=true:=by apply cellsBlockG (ar:=10) (d:=2);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa36 : qB 9 0 0 48=true:=qc36_0
set_option maxHeartbeats 0 in
lemma qc37_0 : qB 9 1 0 4=true:=chunkBlockG (ar:=9) (by decide +kernel)
lemma qa37 : qB 9 1 0 4=true:=qc37_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc40_0 : qB 10 0 0 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc40_96 : qB 10 0 96 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc40_192 : qB 10 0 192 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc40_288 : qB 10 0 288 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc40_384 : qB 10 0 384 41=true:=by apply cellsBlockG (ar:=11) (d:=2);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa40 : qB 10 0 0 425=true:=(qM 10 0 0 192 233 (qM 10 0 0 96 96 qc40_0 qc40_96) (qM 10 0 192 96 137 qc40_192 (qM 10 0 288 96 41 qc40_288 qc40_384)))
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc41_0 : qB 10 1 0 96=true:=by apply cellsBlockG (ar:=10) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc41_96 : qB 10 1 96 23=true:=by apply cellsBlockG (ar:=10) (d:=1);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa41 : qB 10 1 0 119=true:=(qM 10 1 0 96 23 qc41_0 qc41_96)
set_option maxHeartbeats 0 in
lemma qc42_0 : qB 10 2 0 2=true:=chunkBlockG (ar:=9) (by decide +kernel)
lemma qa42 : qB 10 2 0 2=true:=qc42_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc44_0 : qB 11 0 0 96=true:=by apply cellsBlockG (ar:=12) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc44_96 : qB 11 0 96 96=true:=by apply cellsBlockG (ar:=12) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc44_192 : qB 11 0 192 96=true:=by apply cellsBlockG (ar:=12) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc44_288 : qB 11 0 288 94=true:=by apply cellsBlockG (ar:=12) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa44 : qB 11 0 0 382=true:=(qM 11 0 0 192 190 (qM 11 0 0 96 96 qc44_0 qc44_96) (qM 11 0 192 96 94 qc44_192 qc44_288))
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc45_0 : qB 11 1 0 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc45_96 : qB 11 1 96 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc45_192 : qB 11 1 192 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc45_288 : qB 11 1 288 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc45_384 : qB 11 1 384 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc45_480 : qB 11 1 480 15=true:=by apply cellsBlockG (ar:=11) (d:=1);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa45 : qB 11 1 0 495=true:=(qM 11 1 0 288 207 (qM 11 1 0 96 192 qc45_0 (qM 11 1 96 96 96 qc45_96 qc45_192)) (qM 11 1 288 96 111 qc45_288 (qM 11 1 384 96 15 qc45_384 qc45_480)))
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc46_0 : qB 11 2 0 96=true:=by apply cellsBlockG (ar:=10) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc46_96 : qB 11 2 96 77=true:=by apply cellsBlockG (ar:=10) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa46 : qB 11 2 0 173=true:=(qM 11 2 0 96 77 qc46_0 qc46_96)
set_option maxHeartbeats 0 in
lemma qc47_0 : qB 11 3 0 1=true:=chunkBlockG (ar:=9) (by decide +kernel)
lemma qa47 : qB 11 3 0 1=true:=qc47_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc50_0 : qB 12 2 0 82=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa50 : qB 12 2 0 82=true:=qc50_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc51_0 : qB 12 3 0 42=true:=by apply cellsBlockG (ar:=10) (d:=2);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa51 : qB 12 3 0 42=true:=qc51_0
set_option maxHeartbeats 0 in
lemma qc55_0 : qB 13 3 0 1=true:=chunkBlockG (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
lemma qc55_1 : qB 13 3 1 4=true:=chunkBlockG (ar:=10) (by decide +kernel)
lemma qa55 : qB 13 3 0 5=true:=(qM 13 3 0 1 4 qc55_0 qc55_1)
lemma tablesq : ∀ k ≤ 13,∀ tm ≤ 3,qB k tm 0 (qLv (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq qa32 rfl rfl rfl | exact blockG_eq qa36 rfl rfl rfl | exact blockG_eq qa37 rfl rfl rfl | exact blockG_eq qa40 rfl rfl rfl | exact blockG_eq qa41 rfl rfl rfl | exact blockG_eq qa42 rfl rfl rfl | exact blockG_eq qa44 rfl rfl rfl | exact blockG_eq qa45 rfl rfl rfl | exact blockG_eq qa46 rfl rfl rfl | exact blockG_eq qa47 rfl rfl rfl | exact blockG_eq qa50 rfl rfl rfl | exact blockG_eq qa51 rfl rfl rfl | exact blockG_eq qa55 rfl rfl rfl
def ones3077 : Sig := neg zero
def evalSig3077 (w : List Sig) (p : Fin 26) : Sig :=
  if p.val = 25 then ones3077 else w.getD p.val zero
def gateVal3077 (w : List Sig) (g : Fin 3 × Fin 26 × Fin 26) : Sig :=
  if g.1.val = 0 then bin false (evalSig3077 w g.2.1) (evalSig3077 w g.2.2)
  else if g.1.val = 1 then bin true (evalSig3077 w g.2.1) (evalSig3077 w g.2.2)
  else neg (evalSig3077 w g.2.1)
def exec3077 (gs : List (Fin 3 × Fin 26 × Fin 26)) (w : List Sig) : List Sig :=
  gs.foldl (fun w g => w ++ [gateVal3077 w g]) w
theorem bit_ones3077 (r : Row) : bit r ones3077 = true := by unfold ones3077; rw [bit_neg]; simp [bit, zero]
theorem not_proper_ones3077 : ¬proper ones3077 := by unfold proper ones3077; decide +kernel
theorem bit_evalSig3077 (r : Row) (w : List Sig) (p : Fin 26) :
    bit r (evalSig3077 w p) = if p.val = 25 then true else (w.map (bit r)).getD p.val false := by
  unfold evalSig3077
  split_ifs with h
  · exact bit_ones3077 r
  · exact (b_read r w p.val).symm
theorem bit_gateVal3077 (r : Row) (w : List Sig) (g : Fin 3 × Fin 26 × Fin 26) :
    bit r (gateVal3077 w g) =
      (let rd := fun (x : List Bool) (p : Fin 26) => if p.val = 25 then true else x.getD p.val false
       if g.1.val = 0 then rd (w.map (bit r)) g.2.1 && rd (w.map (bit r)) g.2.2
       else if g.1.val = 1 then rd (w.map (bit r)) g.2.1 || rd (w.map (bit r)) g.2.2
       else !rd (w.map (bit r)) g.2.1) := by
  unfold gateVal3077
  split_ifs <;> simp only [bit_bin, bit_neg, bit_evalSig3077, ite_true, Bool.false_eq_true, ite_false]
theorem exec3077_bits (r : Row) (gs : List (Fin 3 × Fin 26 × Fin 26)) (w : List Sig) :
    (exec3077 gs w).map (bit r) =
      List.foldl (fun (x13 : List Bool) (x14 : Fin 3 × Fin 26 × Fin 26) =>
        let rd := fun (x12 : List Bool) (x13 : Fin 26) => if x13.val = 25 then true else x12.getD x13.val false
        x13 ++ [if x14.1.val = 0 then rd x13 x14.2.1 && rd x13 x14.2.2
                else if x14.1.val = 1 then rd x13 x14.2.1 || rd x13 x14.2.2
                else !rd x13 x14.2.1]) (w.map (bit r)) gs := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [exec3077, List.foldl_cons] at ih ⊢
    rw [ih, List.map_append, List.map_cons, List.map_nil, bit_gateVal3077]
theorem evalSig3077_rep (w : List Sig) (p : Fin 26) : represented w (evalSig3077 w p) := by
  unfold evalSig3077
  split_ifs
  · exact Or.inr not_proper_ones3077
  · exact get_rep w p.val
theorem neg_rep3077 {w a} (ha : represented w a) : represented w (neg a) ∨ ∃ x, x ∈ w ∧ proper x ∧ neg a = neg x := by
  by_cases hp : proper a
  · exact Or.inr ⟨a, ha.resolve_right (fun h => h hp), hp, rfl⟩
  · left; right
    intro hn
    unfold proper at hn hp
    rcases hn with ⟨h1, h2⟩
    apply hp
    refine ⟨fun e => h2 (by rw [e]; decide +kernel), fun e => h1 (by rw [e]; decide +kernel)⟩
theorem extract3077 (gs : List (Fin 3 × Fin 26 × Fin 26)) (w : List Sig) {z : Sig}
    (pz : proper z) (hm : z ∈ exec3077 gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live z k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil =>
    exact ⟨0, 0, {z}, by simp, Live.stop pz, fun a ha => by simpa [exec3077, Finset.mem_singleton.mp ha] using hm⟩
  | cons g gs ih =>
    obtain ⟨k, t, S, hk, run, sub⟩ := ih (w ++ [gateVal3077 w g]) hm
    by_cases h0 : g.1.val = 0
    · have hgv : gateVal3077 w g = bin false (evalSig3077 w g.2.1) (evalSig3077 w g.2.2) := by simp [gateVal3077, h0]
      have hrep : represented w (gateVal3077 w g) ∨ (if false then ∃ a, a ∈ w ∧ proper a ∧ gateVal3077 w g = neg a else ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ gateVal3077 w g = bin d a b) := by
        rw [hgv]; simp only [Bool.false_eq_true, ite_false]
        obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws (evalSig3077 w g.2.1)
        obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws (evalSig3077 w g.2.2)
        have ha := evalSig3077_rep w g.2.1; have hb := evalSig3077_rep w g.2.2
        by_cases ha0 : evalSig3077 w g.2.1 = zero
        · rw [ha0, bin_comm, bz]; exact Or.inl (Or.inr (fun h => h.1 rfl))
        · by_cases ha1 : evalSig3077 w g.2.1 = one
          · rw [ha1, bin_comm, b1]; exact Or.inl hb
          · by_cases hb0 : evalSig3077 w g.2.2 = zero
            · rw [hb0, az]; exact Or.inl (Or.inr (fun h => h.1 rfl))
            · by_cases hb1 : evalSig3077 w g.2.2 = one
              · rw [hb1, a1]; exact Or.inl ha
              · by_cases hab : evalSig3077 w g.2.1 = evalSig3077 w g.2.2
                · rw [← hab, aa]; exact Or.inl ha
                · exact Or.inr ⟨false, _, _, ha.resolve_right (fun h => h ⟨ha0, ha1⟩), hb.resolve_right (fun h => h ⟨hb0, hb1⟩), ⟨ha0, ha1⟩, ⟨hb0, hb1⟩, hab, rfl⟩
      obtain ⟨k', t', S', hk', _, run', sub'⟩ := pull_gateT false run hrep sub
      exact ⟨k', t', S', by simp; omega, run', sub'⟩
    · by_cases h1 : g.1.val = 1
      · have hgv : gateVal3077 w g = bin true (evalSig3077 w g.2.1) (evalSig3077 w g.2.2) := by simp [gateVal3077, h0, h1]
        have hrep : represented w (gateVal3077 w g) ∨ (if false then ∃ a, a ∈ w ∧ proper a ∧ gateVal3077 w g = neg a else ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ gateVal3077 w g = bin d a b) := by
          rw [hgv]; simp only [Bool.false_eq_true, ite_false]
          obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws (evalSig3077 w g.2.1)
          obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws (evalSig3077 w g.2.2)
          have ha := evalSig3077_rep w g.2.1; have hb := evalSig3077_rep w g.2.2
          by_cases ha0 : evalSig3077 w g.2.1 = zero
          · rw [ha0, bin_comm, b0]; exact Or.inl hb
          · by_cases ha1 : evalSig3077 w g.2.1 = one
            · rw [ha1, bin_comm, bo]; exact Or.inl (Or.inr (fun h => h.2 rfl))
            · by_cases hb0 : evalSig3077 w g.2.2 = zero
              · rw [hb0, a0]; exact Or.inl ha
              · by_cases hb1 : evalSig3077 w g.2.2 = one
                · rw [hb1, ao]; exact Or.inl (Or.inr (fun h => h.2 rfl))
                · by_cases hab : evalSig3077 w g.2.1 = evalSig3077 w g.2.2
                  · rw [← hab, aa']; exact Or.inl ha
                  · exact Or.inr ⟨true, _, _, ha.resolve_right (fun h => h ⟨ha0, ha1⟩), hb.resolve_right (fun h => h ⟨hb0, hb1⟩), ⟨ha0, ha1⟩, ⟨hb0, hb1⟩, hab, rfl⟩
        obtain ⟨k', t', S', hk', _, run', sub'⟩ := pull_gateT false run hrep sub
        exact ⟨k', t', S', by simp; omega, run', sub'⟩
      · have hgv : gateVal3077 w g = neg (evalSig3077 w g.2.1) := by simp [gateVal3077, h0, h1]
        have hrep : represented w (gateVal3077 w g) ∨ (if true then ∃ a, a ∈ w ∧ proper a ∧ gateVal3077 w g = neg a else ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ gateVal3077 w g = bin d a b) := by
          rw [hgv]; simp only [ite_true]; exact neg_rep3077 (evalSig3077_rep w g.2.1)
        obtain ⟨k', t', S', hk', _, run', sub'⟩ := pull_gateT true run hrep sub
        exact ⟨k', t', S', by simp; omega, run', sub'⟩
def seed9 : Sig := bin true (inputs.getD 0 zero) (inputs.getD 4 zero)
def w10 (j : Fin 9) : Sig := bin true seed9 (inputs.getD j.val zero)
def fam3077 (j : Fin 9) : List Sig := inputs ++ [seed9, w10 j]
def witTable3077 (j i : Fin 9) : Row × Row :=
  let (a, b) := match j.val, i.val with
    | 2, 2 => (9,13)
    | 3, 3 => (5,13)
    | 6, 6 => (18,82)
    | 7, 7 => (5,133)
    | 8, 8 => (9,265)
    | _, 0 => (16,17)
    | _, 1 => (1,3)
    | _, 2 => (2,6)
    | _, 3 => (4,12)
    | _, 4 => (1,17)
    | _, 5 => (1,33)
    | _, 6 => (2,66)
    | _, 7 => (4,132)
    | _, _ => (8,264)
  (Fin.ofNat 512 a, Fin.ofNat 512 b)
theorem wit3077_ok :
    (List.finRange 9).all (fun j => (List.finRange 9).all (fun i =>
      let p := witTable3077 j i
      (bit p.1 graph != bit p.2 graph) &&
      (fam3077 j).all (fun w => w == inputs.getD i.val zero || bit p.1 w == bit p.2 w))) = true := by
  decide +kernel
theorem inputs_sub_3077 {j k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ fam3077 j) :
    inputs.toFinset ⊆ S := by
  intro v hv
  have hm := List.mem_toFinset.mp hv
  rw [← input_list, List.mem_ofFn] at hm
  obtain ⟨i, rfl⟩ := hm
  have hj := List.all_eq_true.mp wit3077_ok j (List.mem_finRange j)
  have hh := List.all_eq_true.mp hj i (List.mem_finRange i)
  simp only [Bool.and_eq_true, bne_iff_ne] at hh
  have h2' := List.all_eq_true.mp hh.2
  exact raw_required h _ _ sub (witTable3077 j i).1 (witTable3077 j i).2 hh.1
    (fun w hw hn => by
      have ha := h2' w hw
      simp only [Bool.or_eq_true, beq_iff_eq] at ha
      exact ha.resolve_left hn)
def col17 : ColumnInfo := (17, 0, 494, 0, 11)
def pool17 : BoundPool := ⟨subcube 17 0, 11, 0, vars 511⟩
theorem col17_valid : ValidPool (vars 511) graph pool17 := by
  have hgd := geomdead
  simp only [graphValid, Bool.and_eq_true, List.all_eq_true] at hgd
  have hmem : col17 ∈ dead.cols.values := List.contains_iff_mem.mp (by decide +kernel : dead.cols.values.contains col17 = true)
  have hslice := col_sound col17 (boundsBefore known383) (before_sound known383 valid383) (hgd.1.2 col17 hmem)
  have htgt : graphGoal dead.mask = graph := by decide +kernel
  rw [htgt] at hslice
  exact materialize_sound (cs := []) hslice rfl
theorem noSeed9_base : Impossible graph 13 (seed9 :: inputs).toFinset := by
  have heq : choiceVal (0, seed9, seed9) = seed9 := by
    change bin false seed9 seed9 = seed9; unfold bin; exact BitVec.and_self
  have hnd : (choiceVal (0, seed9, seed9) :: inputs).Nodup := by
    rw [heq]; exact of_decide_eq_true (by decide +kernel : decide (seed9 :: inputs).Nodup = true)
  have hcut : scalarPoolCut pool17 13 inputs (0, seed9, seed9) = true := by decide +kernel
  have h := scalarPoolCut_sound col17_valid hnd hcut
  rwa [heq] at h
theorem noSeed9_ext_j (j : Fin 9)
    (heq : choiceVal (0, w10 j, w10 j) = w10 j)
    (hnd0 : decide (w10 j :: seed9 :: inputs).Nodup = true)
    (hcut : scalarPoolCut pool17 13 (seed9 :: inputs) (0, w10 j, w10 j) = true) :
    Impossible graph 13 (w10 j :: seed9 :: inputs).toFinset := by
  have hnd : (choiceVal (0, w10 j, w10 j) :: seed9 :: inputs).Nodup := by
    rw [heq]; exact of_decide_eq_true hnd0
  have h := scalarPoolCut_sound col17_valid hnd hcut
  rwa [heq] at h
theorem noSeed9_ext (j : Fin 9) (hj0 : j.val ≠ 0) (hj4 : j.val ≠ 4) :
    Impossible graph 13 (w10 j :: seed9 :: inputs).toFinset := by
  fin_cases j
  · exact False.elim (hj0 rfl)
  · exact noSeed9_ext_j ⟨1, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact noSeed9_ext_j ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact noSeed9_ext_j ⟨3, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact False.elim (hj4 rfl)
  · exact noSeed9_ext_j ⟨5, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact noSeed9_ext_j ⟨6, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact noSeed9_ext_j ⟨7, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact noSeed9_ext_j ⟨8, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem rootU_imp (idx : Nat) (hi : idx < 5) :
    ImpossibleT graph 13 3 (stateSetG dead qLv 55 idx (vars dead.mask)).toFinset := by
  have hall := forestG_all dead qLv qIx rotDS 13 (boundsBefore known383)
    (before_sound known383 valid383) geomdead rotDS_at tablesq 13 (by decide) 3 (by decide) idx hi
  have htgt : graphGoal dead.mask = graph := by decide +kernel
  rwa [htgt] at hall
theorem perm1_ok : autoOK graph ((dead.autos.getD 1 []).map swapRows) = true := by decide +kernel
theorem no3077_pos : ImpossibleT graph 13 3 inputs.toFinset := by
  have h := rootU_imp 0 (by decide)
  have hs : sameWords (stateSetG dead qLv 55 0 (vars dead.mask)) inputs = true := by decide +kernel
  rwa [sameWords_sound hs] at h
theorem no3077_keep0 (j : Fin 9) (hj0 : j.val ≠ 0) (hj4 : j.val ≠ 4) :
    ImpossibleT graph 13 3 (inputs ++ [w10 j]).toFinset := by
  fin_cases j
  · exact False.elim (hj0 rfl)
  · have h := rootU_imp 1 (by decide)
    have hs : sameWords (stateSetG dead qLv 55 1 (vars dead.mask)) (inputs ++ [w10 ⟨1,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rootU_imp 2 (by decide)
    have hs : sameWords (stateSetG dead qLv 55 2 (vars dead.mask)) (inputs ++ [w10 ⟨2,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rootU_imp 3 (by decide)
    have hs : sameWords (stateSetG dead qLv 55 3 (vars dead.mask)) (inputs ++ [w10 ⟨3,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · exact False.elim (hj4 rfl)
  · have h := rotate_excludedT (rootU_imp 1 (by decide)) ((dead.autos.getD 1 []).map swapRows) perm1_ok
    have hs : sameWords ((stateSetG dead qLv 55 1 (vars dead.mask)).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (inputs ++ [w10 ⟨5,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rootU_imp 4 (by decide)
    have hs : sameWords (stateSetG dead qLv 55 4 (vars dead.mask)) (inputs ++ [w10 ⟨6,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rotate_excludedT (rootU_imp 4 (by decide)) ((dead.autos.getD 1 []).map swapRows) perm1_ok
    have hs : sameWords ((stateSetG dead qLv 55 4 (vars dead.mask)).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (inputs ++ [w10 ⟨7,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rotate_excludedT (rootU_imp 2 (by decide)) ((dead.autos.getD 1 []).map swapRows) perm1_ok
    have hs : sameWords ((stateSetG dead qLv 55 2 (vars dead.mask)).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (inputs ++ [w10 ⟨8,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
theorem kill3077 {j : Fin 9} {k t S} (hk : k ≤ 13) (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ fam3077 j) : False := by
  have haveIn := inputs_sub_3077 h sub
  by_cases hj0 : j.val = 0
  · have hw : w10 j = seed9 := by
      have : j = ⟨0, by decide⟩ := Fin.ext hj0; subst this; decide +kernel
    by_cases hs : seed9 ∈ S
    · have eqS : S = (seed9 :: inputs).toFinset := by
        apply Finset.Subset.antisymm
        · intro v hv
          have hm := sub v hv
          simp only [fam3077, hw, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
          rcases hm with hm | rfl | rfl <;> simp [*]
        · intro v hv
          simp only [List.toFinset_cons, Finset.mem_insert] at hv
          rcases hv with rfl | hv
          · exact hs
          · exact haveIn hv
      exact noSeed9_base k t hk (eqS ▸ h)
    · have eqS : S = inputs.toFinset := by
        apply Finset.Subset.antisymm
        · intro v hv
          have hm := sub v hv
          simp only [fam3077, hw, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
          rcases hm with hm | rfl | rfl
          · exact List.mem_toFinset.mpr hm
          · exact False.elim (hs hv)
          · exact False.elim (hs hv)
        · exact haveIn
      exact no3077_pos k t hk (fun h0 => by omega) (eqS ▸ h)
  · by_cases hj4 : j.val = 4
    · have hw : w10 j = seed9 := by
        have : j = ⟨4, by decide⟩ := Fin.ext hj4; subst this; decide +kernel
      by_cases hs : seed9 ∈ S
      · have eqS : S = (seed9 :: inputs).toFinset := by
          apply Finset.Subset.antisymm
          · intro v hv
            have hm := sub v hv
            simp only [fam3077, hw, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
            rcases hm with hm | rfl | rfl <;> simp [*]
          · intro v hv
            simp only [List.toFinset_cons, Finset.mem_insert] at hv
            rcases hv with rfl | hv
            · exact hs
            · exact haveIn hv
        exact noSeed9_base k t hk (eqS ▸ h)
      · have eqS : S = inputs.toFinset := by
          apply Finset.Subset.antisymm
          · intro v hv
            have hm := sub v hv
            simp only [fam3077, hw, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
            rcases hm with hm | rfl | rfl
            · exact List.mem_toFinset.mpr hm
            · exact False.elim (hs hv)
            · exact False.elim (hs hv)
          · exact haveIn
        exact no3077_pos k t hk (fun h0 => by omega) (eqS ▸ h)
    · by_cases hs : seed9 ∈ S
      · by_cases hw : w10 j ∈ S
        · have eqS : S = (w10 j :: seed9 :: inputs).toFinset := by
            apply Finset.Subset.antisymm
            · intro v hv
              have hm := sub v hv
              simp only [fam3077, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
              rcases hm with hm | rfl | rfl <;> simp [*]
            · intro v hv
              simp only [List.toFinset_cons, Finset.mem_insert] at hv
              rcases hv with rfl | rfl | hv
              · exact hw
              · exact hs
              · exact haveIn hv
          exact noSeed9_ext j hj0 hj4 k t hk (eqS ▸ h)
        · have eqS : S = (seed9 :: inputs).toFinset := by
            apply Finset.Subset.antisymm
            · intro v hv
              have hm := sub v hv
              simp only [fam3077, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
              rcases hm with hm | rfl | rfl
              · simp [hm]
              · simp
              · exact False.elim (hw hv)
            · intro v hv
              simp only [List.toFinset_cons, Finset.mem_insert] at hv
              rcases hv with rfl | hv
              · exact hs
              · exact haveIn hv
          exact noSeed9_base k t hk (eqS ▸ h)
      · by_cases hw : w10 j ∈ S
        · have eqS : S = (inputs ++ [w10 j]).toFinset := by
            apply Finset.Subset.antisymm
            · intro v hv
              have hm := sub v hv
              simp only [fam3077, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
              rcases hm with hm | rfl | rfl
              · exact List.mem_toFinset.mpr (List.mem_append_left _ hm)
              · exact False.elim (hs hv)
              · exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_singleton_self _))
            · intro v hv
              have hm := List.mem_toFinset.mp hv
              simp only [List.mem_append, List.mem_singleton] at hm
              rcases hm with hm | rfl
              · exact haveIn (List.mem_toFinset.mpr hm)
              · exact hw
          exact no3077_keep0 j hj0 hj4 k t hk (fun h0 => by omega) (eqS ▸ h)
        · have eqS : S = inputs.toFinset := by
            apply Finset.Subset.antisymm
            · intro v hv
              have hm := sub v hv
              simp only [fam3077, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
              rcases hm with hm | rfl | rfl
              · exact List.mem_toFinset.mpr hm
              · exact False.elim (hs hv)
              · exact False.elim (hw hv)
            · exact haveIn
          exact no3077_pos k t hk (fun h0 => by omega) (eqS ▸ h)
theorem sample_eq_testBit_all : ∀ (r : Row) (i : Fin 9), sample r i = r.val.testBit i.val := by
  decide +kernel
theorem sample_eq_testBit (r : Row) (i : Fin 9) : sample r i = r.val.testBit i.val :=
  sample_eq_testBit_all r i
theorem bit_seed9 (r : Row) : bit r seed9 = (sample r 0 || sample r 4) := by
  simp only [seed9, bit_bin, sample, ite_true]; rfl
theorem edge3077_eq (r : Row) :
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun (x14 : ℕ) =>
      r.val.testBit (Fin.ofNat 9 (x14 / 10)).val && r.val.testBit (Fin.ofNat 9 (x14 % 10)).val) = bit r graph := by
  rw [edge_table r]
  unfold edge
  simp only [sample_eq_testBit, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]; rfl
theorem step0_sub (x1 x2 : Fin 26) (h9 : x1.val = 9 ∨ x2.val = 9) (h1 : x1.val ≠ 25) (h2 : x2.val ≠ 25) :
    ∃ j : Fin 9, ∀ v ∈ (inputs ++ [seed9]) ++ [gateVal3077 (inputs ++ [seed9]) ((1 : Fin 3), x1, x2)], v ∈ fam3077 j := by
  have hlen : (inputs ++ [seed9]).length = 10 := by rw [List.length_append, ← input_list, List.length_ofFn]; rfl
  have hget9 : (inputs ++ [seed9]).getD 9 zero = seed9 := by
    have hli : inputs.length = 9 := by rw [← input_list, List.length_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hli]
    simp
  have hgv : gateVal3077 (inputs ++ [seed9]) ((1 : Fin 3), x1, x2) =
      bin true (evalSig3077 (inputs ++ [seed9]) x1) (evalSig3077 (inputs ++ [seed9]) x2) := rfl
  have hbin_or : ∀ p : Fin 26, p.val ≠ 25 →
      ∃ j : Fin 9, bin true seed9 (evalSig3077 (inputs ++ [seed9]) p) = w10 j ∨
        bin true seed9 (evalSig3077 (inputs ++ [seed9]) p) = seed9 := by
    intro p hp
    unfold evalSig3077
    rw [if_neg hp]
    by_cases hlt : p.val < 9
    · refine ⟨⟨p.val, hlt⟩, Or.inl ?_⟩
      have hli : inputs.length = 9 := by rw [← input_list, List.length_ofFn]
      have hgp : (inputs ++ [seed9]).getD p.val zero = inputs.getD p.val zero := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rw [hgp]; rfl
    · refine ⟨⟨0, by decide⟩, Or.inr ?_⟩
      by_cases h9p : p.val = 9
      · rw [h9p, hget9]; decide +kernel
      · have hge : (inputs ++ [seed9]).length ≤ p.val := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
        change bin true seed9 zero = seed9
        decide +kernel
  have hpair : ∃ j : Fin 9, gateVal3077 (inputs ++ [seed9]) ((1 : Fin 3), x1, x2) = w10 j ∨
      gateVal3077 (inputs ++ [seed9]) ((1 : Fin 3), x1, x2) = seed9 := by
    rw [hgv]
    rcases h9 with h9 | h9
    · have he1 : evalSig3077 (inputs ++ [seed9]) x1 = seed9 := by
        unfold evalSig3077; rw [if_neg h1, h9, hget9]
      rw [he1]; exact hbin_or x2 h2
    · have he2 : evalSig3077 (inputs ++ [seed9]) x2 = seed9 := by
        unfold evalSig3077; rw [if_neg h2, h9, hget9]
      rw [he2, bin_comm]; exact hbin_or x1 h1
  obtain ⟨j, hj⟩ := hpair
  refine ⟨j, fun v hv => ?_⟩
  simp only [List.mem_append, List.mem_singleton] at hv
  rcases hv with (hv | rfl) | rfl
  · exact List.mem_append_left _ hv
  · exact List.mem_append_right _ (by simp)
  · rcases hj with hj | hj
    · rw [hj]; exact List.mem_append_right _ (by simp)
    · rw [hj]; exact List.mem_append_right _ (by simp)
theorem main3077 : ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 = (9 : ℕ) ∨ ↑x2 = (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), ∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  intro x1 x2 x3 x4 hlen h9 h1 h2 _
  by_contra hno
  push Not at hno
  let w0 : List Sig := (inputs ++ [seed9]) ++ [gateVal3077 (inputs ++ [seed9]) ((1 : Fin 3), x1, x2)]
  have goalEq : (exec3077 x4 w0).getD x3.val zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro m hm
    let r : Row := ⟨m, hm⟩
    change bit r ((exec3077 x4 w0).getD x3.val zero) = bit r graph
    rw [← b_read, exec3077_bits r x4 w0]
    have hbits0 : (inputs ++ [seed9]).map (bit r) = List.ofFn (fun i : Fin 9 => r.val.testBit i.val) ++ [r.val.testBit 0 || r.val.testBit 4] := by
      simp only [List.map_append, List.map_cons, List.map_nil, bit_seed9]
      rw [← sampled, show sample r = fun i : Fin 9 => r.val.testBit i.val from funext (sample_eq_testBit r)]; rfl
    have hw0 : w0.map (bit r) =
        List.foldl (fun (x13 : List Bool) (x14 : Fin 3 × Fin 26 × Fin 26) =>
          let rd := fun (x12 : List Bool) (x13 : Fin 26) => if x13.val = 25 then true else x12.getD x13.val false
          x13 ++ [if x14.1.val = 0 then rd x13 x14.2.1 && rd x13 x14.2.2
                  else if x14.1.val = 1 then rd x13 x14.2.1 || rd x13 x14.2.2
                  else !rd x13 x14.2.1])
          (List.ofFn (fun i : Fin 9 => r.val.testBit i.val) ++ [r.val.testBit 0 || r.val.testBit 4]) [((1 : Fin 3), x1, x2)] := by
      simp only [w0, List.map_append, List.map_cons, List.map_nil, bit_gateVal3077, List.foldl_cons, List.foldl_nil, hbits0]
    rw [hw0]
    have hx := Classical.byContradiction (hno m hm)
    exact hx.trans (edge3077_eq r)
  have out := get_rep (exec3077 x4 w0) x3.val
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k, t, S, hk, run, sub⟩ := extract3077 x4 w0 graph_proper targetIn
  obtain ⟨j, hj⟩ := step0_sub x1 x2 h9 h1 h2
  exact kill3077 (hk.trans hlen) run (fun v hv => hj v (sub v hv))
end PEqualNP.Outside.L_meta_3077
theorem PEqualNP.Outside.L_meta_3077 : ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 = (9 : ℕ) ∨ ↑x2 = (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), ∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) :=
  PEqualNP.Outside.L_meta_3077.main3077
