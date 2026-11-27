import PEqualNP.Defs
-- The Live/Run/Forest verification framework and subgraph lower bounds
-- (known383,known1015,and dead) are adapted from PressF10,pequalnp-proofs PR 4332,
-- and L_meta_3271 / L_meta_3273,licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_3216
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero:Sig := 0
def one:Sig := BitVec.allOnes 512
def neg (a:Sig) : Sig := ~~~a
def bin (d:Bool) (a b:Sig) : Sig := if d then a ||| b else a &&& b
def q7 (a:Sig) : Prop := a ≠ zero /\ a ≠ one
lemma qau (d:Bool) (a b:Sig) : bin d a b=bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
def inputs:List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def vq:Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def qu:Sig := inputs.getD 0 zero
def qn:Sig := neg qu
def jc (mode:Nat) (a:Sig) : Bool :=
  if mode==2 then a != qu
  else if mode==3 then a != qu&&a != qn
  else true
def zq (mode:Nat) (d:Bool) (a b:Sig) (ka kb:Bool) : Bool :=
  if mode==2 then
    (a != qu&&b != qu)||!d
  else if mode==3 then
    if a==qu then d&&!ka&&b != qn
    else if b==qu then d&&!kb&&a != qn
    else if a==qn then !d&&!ka
    else if b==qn then !d&&!kb
    else true
  else true
def vd (mode op:Nat) (a b:Sig) (ka kb:Bool) : Bool :=
  if op==2 then jc mode a
  else zq mode (op==1) a b ka kb
lemma qmn (mode:Nat) (d:Bool) (a b:Sig) (ka kb:Bool) (hne:a ≠ b) :
    zq mode d a b ka kb=zq mode d b a kb ka := by
  unfold zq
  by_cases h2:(mode==2)=true
  . simp [h2,Bool.and_comm]
  . simp only [h2,Bool.false_eq_true,ite_false]
    by_cases h3:(mode==3)=true
    . simp only [h3,ite_true]
      by_cases ax:a=qu
      . have bx:b ≠ qu := fun e => hne (ax.trans e.symm)
        simp [ax,bx]
      . by_cases bx:b=qu
        . simp [ax,bx]
        . by_cases an:a=qn
          . have bn:b ≠ qn := fun e => hne (an.trans e.symm)
            simp [ax,bx,an,bn]
          . by_cases bn:b=qn
            . simp [ax,bx,an,bn]
            . simp [ax,bx,an,bn]
    . simp [h3]
def j3 (mode:Nat) (target:Sig) (k t:Nat) (S:Finset Sig) : Prop :=
  ∀ P:Nat -> Nat -> Finset Sig -> Prop,
    (q7 target -> P 0 0 {target}) →
    (∀ {k t:Nat} {U:Finset Sig} {a:Sig},q7 a -> jc mode a=true →
      neg a ∉ insert a U -> P k t (insert (neg a) U) -> P (k+1) (t+1) (insert a U)) →
    (∀ {k t:Nat} {U:Finset Sig} {a b:Sig} {d:Bool},q7 a -> q7 b -> a ≠ b →
      zq mode d a b (decide (a ∈ U)) (decide (b ∈ U))=true →
      bin d a b ∉ insert a (insert b U) →
      P k t (insert (bin d a b) U) -> P (k+1) t (insert a (insert b U))) →
    P k t S
abbrev v4 (target:Sig) (k t:Nat) (S:Finset Sig) : Prop := j3 0 target k t S
lemma qaz {mode target} (hp:q7 target) : j3 mode target 0 0 {target} :=
  fun _ hs _ _ => hs hp
lemma qaf {mode target k t U a} (ha:q7 a) (hallow:jc mode a=true)
    (hfresh:neg a ∉ insert a U) (tail:j3 mode target k t (insert (neg a) U)) :
    j3 mode target (k+1) (t+1) (insert a U) :=
  fun P hs hu hb => hu ha hallow hfresh (tail P hs hu hb)
lemma yn {mode target k t U a b d} (ha:q7 a) (hb:q7 b) (hab:a ≠ b)
    (hallow:zq mode d a b (decide (a ∈ U)) (decide (b ∈ U))=true)
    (hfresh:bin d a b ∉ insert a (insert b U))
    (tail:j3 mode target k t (insert (bin d a b) U)) :
    j3 mode target (k+1) t (insert a (insert b U)) :=
  fun P hs hu hbn => hbn ha hb hab hallow hfresh (tail P hs hu hbn)
lemma qda {target} (hp:q7 target) : v4 target 0 0 {target} := qaz hp
lemma qdv {target k t U a} (ha:q7 a) (hfresh:neg a ∉ insert a U)
    (tail:v4 target k t (insert (neg a) U)) : v4 target (k+1) (t+1) (insert a U) :=
  qaf ha rfl hfresh tail
lemma qcs {target k t U a b d} (ha:q7 a) (hb:q7 b) (hab:a ≠ b)
    (hfresh:bin d a b ∉ insert a (insert b U))
    (tail:v4 target k t (insert (bin d a b) U)) :
    v4 target (k+1) t (insert a (insert b U)) :=
  yn ha hb hab rfl hfresh tail
lemma wc {mode target k t S} (h:j3 mode target k t S) : v4 target k t S :=
  h (v4 target) (fun hp => qda hp) (fun ha _ hf ih => qdv ha hf ih)
    (fun ha hb hab _ hf ih => qcs ha hb hab hf ih)
def qmz (mode:Nat) (target:Sig) (k t:Nat) (S:Finset Sig) : Prop :=
  (k=0 /\ t=0 /\ S={target} /\ q7 target) ∨
  (∃ k' t' U a,k=k'+1 /\ t=t'+1 /\ S=insert a U /\ q7 a ∧
    jc mode a=true /\ neg a ∉ insert a U /\ j3 mode target k' t' (insert (neg a) U)) ∨
  (∃ k' U a b d,k=k'+1 /\ S=insert a (insert b U) /\ q7 a /\ q7 b /\ a ≠ b ∧
    zq mode d a b (decide (a ∈ U)) (decide (b ∈ U))=true ∧
    bin d a b ∉ insert a (insert b U) /\ j3 mode target k' t (insert (bin d a b) U))
lemma qct {mode target k t S} (h:j3 mode target k t S) :
    qmz mode target k t S :=
  (h (fun k t S => j3 mode target k t S /\ qmz mode target k t S)
    (fun hp => ⟨qaz hp,Or.inl ⟨rfl,rfl,rfl,hp⟩⟩)
    (fun ha hallow hf ih => ⟨qaf ha hallow hf ih.1,
      Or.inr (Or.inl ⟨_,_,_,_,rfl,rfl,rfl,ha,hallow,hf,ih.1⟩)⟩)
    (fun ha hb hab hallow hf ih => ⟨yn ha hb hab hallow hf ih.1,
      Or.inr (Or.inr ⟨_,_,_,_,_,rfl,rfl,ha,hb,hab,hallow,hf,ih.1⟩)⟩)).2
lemma qcr {target k t S} (h:v4 target k t S) : ∀ a ∈ S,q7 a :=
  h (fun _ _ S => ∀ a ∈ S,q7 a)
    (fun hp => by simpa using hp)
    (fun ha _ _ ih => by simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h)))
    (fun ha hb _ _ _ ih => by
      simp only [Finset.forall_mem_insert]
      exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩)
lemma qeq {mode target k t S} (h:j3 mode target k t S) : ∀ a ∈ S,q7 a :=
  qcr (wc h)
lemma qdb {target k t S} (h:v4 target k t S) : t ≤ k /\ S.card+t ≤ k+1 :=
  h (fun k t S => t ≤ k /\ S.card+t ≤ k+1)
    (fun _ => by simp)
    (fun {_ _ U a} _ _ hf ih => by
      have hu:neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
      rw [Finset.card_insert_of_notMem hu] at ih
      have hc := Finset.card_insert_le a U
      exact ⟨by omega,by omega⟩)
    (fun {_ _ U a b d} _ _ _ _ hf ih => by
      have hu:bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
      rw [Finset.card_insert_of_notMem hu] at ih
      have h1 := Finset.card_insert_le (a := a) (s := insert b U)
      have h2 := Finset.card_insert_le (a := b) (s := U)
      exact ⟨by omega,by omega⟩)
lemma qit {mode target k t S} (h:j3 mode target k t S) :
    t ≤ k /\ S.card+t ≤ k+1 :=
  qdb (wc h)
def gv (w:List Sig) (g:Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def ze (gs:List Gate) (w:List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def zr (w:List Sig) (v:Sig) : Prop := v ∈ w \/ ¬q7 v
lemma qa9 (w:List Sig) (i:Nat) : zr w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h:w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
lemma vl (a:Sig) :
    bin false a one=a /\ bin true a zero=a ∧
    bin false a zero=zero /\ bin true a one=one ∧
    bin false a a=a /\ bin true a a=a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,
    BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self]
  simp
lemma qd7:neg zero=one /\ neg one=zero := by simp [neg,zero,one]
lemma y6 {w:List Sig} {a:Sig} (h:zr w a) :
    a=zero \/ a=one \/ a ∈ w /\ q7 a := by
  by_cases hz:a=zero
  . exact Or.inl hz
  by_cases ho:a=one
  . exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def qa5 (w:List Sig) (z:Sig) : Prop :=
  (∃ a ∈ w,q7 a /\ z=neg a) ∨
  (∃ d a b,a ∈ w /\ b ∈ w /\ q7 a /\ q7 b /\ a ≠ b /\ z=bin d a b)
lemma qni {w a b} (d:Bool) (ha:zr w a) (hb:zr w b) :
    zr w (bin d a b) \/ qa5 w (bin d a b) := by
  have rz:zr w zero := Or.inr (fun h => h.1 rfl)
  have ro:zr w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := vl a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := vl b
  rcases y6 ha with rfl | rfl | ⟨ham,hap⟩
  . rw [qau];cases d <;> simp_all
  . rw [qau];cases d <;> simp_all
  rcases y6 hb with rfl | rfl | ⟨hbm,hbp⟩
  . cases d <;> simp_all
  . cases d <;> simp_all
  by_cases he:a=b
  . subst b;cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
lemma qpk (w:List Sig) (g:Gate)
    (h:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) /\ g.inputs.length ≤ 2) :
    zr w (gv w g) \/ qa5 w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz:zr w zero := Or.inr (fun h => h.1 rfl)
  have ro:zr w one := Or.inr (fun h => h.2 rfl)
  have nx (a:Sig) (ha:zr w a) : zr w (neg a) \/ qa5 w (neg a) := by
    rcases y6 ha with rfl | rfl | ⟨hm,hp⟩
    . exact Or.inl (qd7.1 ▸ ro)
    . exact Or.inl (qd7.2 ▸ rz)
    . exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    . exact Or.inl ro
    . exact Or.inl rz
    . exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      . simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(vl _).1] using Or.inl (b := qa5 w (w.getD i zero)) (qa9 w i)
      . simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(vl _).2.1] using Or.inl (b := qa5 w (w.getD i zero)) (qa9 w i)
      . exact nx _ (qa9 w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        . simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(vl _).1] using qni false (qa9 w i) (qa9 w j)
        . simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(vl _).2.1] using qni true (qa9 w i) (qa9 w j)
        . exact nx _ (qa9 w i)
lemma qe3 {target:Sig} {w:List Sig} {z:Sig} {k t S} (h:v4 target k t S)
    (hz:zr w z \/ qa5 w z) (sub:∀ a ∈ S,a ∈ w ++ [z]) :
    ∃ k' t' S',k' ≤ k+1 /\ v4 target k' t' S' /\ ∀ a ∈ S',a ∈ w := by
  by_cases hm:z ∈ S
  . by_cases hw:z ∈ w
    . refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu:a ∈ w \/ a=z := by simpa using sub a ha
      rcases hu with hu | rfl
      . exact hu
      . exact hw
    . have hp := qcr h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      . exact False.elim ((hr.resolve_left hw) hp)
      . subst z
        let U := S.erase (neg a)
        have ht:v4 target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu:∀ v ∈ U,v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf:neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          . exact hw (eq.symm ▸ ha)
          . exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,qdv hp' hf ht,by simpa using And.intro ha hu⟩
      . subst z
        let U := S.erase (bin d a b)
        have ht:v4 target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu:∀ v ∈ U,v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf:bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          . exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          . exact hw (eq.symm ▸ hb)
          . exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,qcs pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  . refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn:a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
lemma qvw {target:Sig} (gs:List Gate) (w:List Sig)
    (legal:∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) /\ g.inputs.length ≤ 2)
    (hp:q7 target) (hout:target ∈ ze gs w) :
    ∃ k t S,k ≤ gs.length /\ v4 target k t S /\ ∀ a ∈ S,a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,qda hp,by simpa [ze] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w ++ [gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := qe3 ht (qpk w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp;omega,hu,hT⟩
def bit (i:Fin 512) (a:Sig) : Bool := a.getLsbD i.val
lemma j5 (i) : bit i zero=false := by simp [bit,zero]
lemma yg (i) : bit i one=true := by unfold bit one;rw [BitVec.getLsbD_allOnes];simp
lemma yh (i) (a:Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
lemma qam (i d) (a b:Sig) : bit i (bin d a b) =
    (if d then bit i a||bit i b else bit i a&&bit i b) := by cases d <;> simp [bit,bin]
lemma qe1 (i) (w:List Sig) (j:Nat) :
    (w.map (bit i)).getD j false=bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (j5 _).symm
  | some a => rfl
lemma zbl (i) (g:Gate) (w:List Sig)
    (hg:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g)=g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [qe1]
  rcases hg with rfl | rfl | rfl
  . induction l with
    | nil => exact yg _
    | cons a l ih =>
      change bit i (bin false _ _)=(_&&_)
      rw [qam];exact congrArg (fun x => bit i (w.getD a zero)&&x) ih
  . induction l with
    | nil => exact j5 _
    | cons a l ih =>
      change bit i (bin true _ _)=(_||_)
      rw [qam];exact congrArg (fun x => bit i (w.getD a zero)||x) ih
  . cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [yh,j5]
    | cons a l => exact yh _ _
lemma yp (gs:List Gate) (i) (w:List Sig)
    (hg:∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (ze gs w).map (bit i) =
    gs.foldl (fun (l:List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (ze gs (w ++ [gv w g])).map _=_
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,zbl i g w (hg g (by simp))]
abbrev jv (R:Type) := R -> Bool
def inv {R} (a:jv R) : jv R := fun r => !(a r)
def jr {R} (isOr:Bool) (a b:jv R) : jv R :=
  if isOr then fun r => a r||b r else fun r => a r&&b r
def zw {R} (a:jv R) : Prop := ∃ b:Bool,a=fun _ => b
noncomputable def cost {R} (a:jv R) : Nat := by
  classical exact if zw a then 1 else 0
noncomputable def mass {R} (xs:List (jv R)) : Nat := (xs.map cost).sum
def q4 {R} (pool:List (jv R)) (v:jv R) : Prop := v ∈ pool \/ zw v
def qar {R} (pool xs:List (jv R)) := ∀ a ∈ xs,q4 pool a
def vk {R} (roots:List (jv R)) (p:Nat) (bank:List (jv R)) : Prop :=
  ∀ P:Nat -> List (jv R) -> Prop,
    P 0 roots →
    (∀ {p bank a},q4 bank a -> P p bank -> P (p+1) (inv a :: bank)) →
    (∀ {p bank a b} (op:Bool),q4 bank a -> q4 bank b →
      P p bank -> P (p+1) (jr op a b :: bank)) →
    P p bank
lemma qad {R} {roots:List (jv R)} : vk roots 0 roots :=
  fun _ hs _ _ => hs
lemma qmq {R} {roots:List (jv R)} {p bank a} (hp:vk roots p bank)
    (ha:q4 bank a) : vk roots (p+1) (inv a :: bank) :=
  fun P hs h1 h2 => h1 ha (hp P hs h1 h2)
lemma qmp {R} {roots:List (jv R)} {p bank a b} (op:Bool)
    (hp:vk roots p bank) (ha:q4 bank a) (hb:q4 bank b) :
    vk roots (p+1) (jr op a b :: bank) :=
  fun P hs h1 h2 => h2 op ha hb (hp P hs h1 h2)
def vi {α : Type} (save:Bool) (x : α) (xs:List α) := if save then x :: xs else xs
def Run {R} (goal:jv R) (s:Nat) (ws:List (jv R)) : Prop :=
  ∀ P:Nat -> List (jv R) -> Prop,
    P 0 [goal] →
    (∀ {s xs zs},xs.Perm zs -> P s xs -> P s zs) →
    (∀ {s a rest} (save:Bool),P s (inv a :: vi save a rest) -> P (s+1) (a :: rest)) →
    (∀ {s a b rest} (op ka kb:Bool),
      P s (jr op a b :: vi ka a (vi kb b rest)) -> P (s+1) (a :: b :: rest)) →
    P s ws
lemma qpi {R} {goal:jv R} : Run goal 0 [goal] :=
  fun _ hs _ _ _ => hs
lemma qd5 {R} {goal:jv R} {s xs zs} (hp:xs.Perm zs) (h:Run goal s xs) :
    Run goal s zs :=
  fun P hs hpm h1 h2 => hpm hp (h P hs hpm h1 h2)
lemma qvt {R} {goal:jv R} {s a rest} (save:Bool)
    (h:Run goal s (inv a :: vi save a rest)) : Run goal (s+1) (a :: rest) :=
  fun P hs hpm h1 h2 => h1 save (h P hs hpm h1 h2)
lemma qm6 {R} {goal:jv R} {s a b rest} (op ka kb:Bool)
    (h:Run goal s (jr op a b :: vi ka a (vi kb b rest))) :
    Run goal (s+1) (a :: b :: rest) :=
  fun P hs hpm h1 h2 => h2 op ka kb (h P hs hpm h1 h2)
lemma yz {R} (a:jv R) (xs) : mass (a :: xs)=cost a+mass xs := by
  simp [mass]
lemma qe4 {R} (a:jv R) (xs) (k:Bool) : mass xs ≤ mass (vi k a xs) := by
  cases k <;> simp [vi,yz]
lemma qes {R} {a:jv R} (h:zw a) : zw (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩
lemma qks {R} {a b:jv R} (op) (h:zw a) (g:zw b) :
    zw (jr op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩
lemma qko {R} (op) {a b:jv R} {bank}
    (h:zw a \/ zw b) (ha:q4 bank a) (hb:q4 bank b) :
    q4 bank (jr op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  . cases op <;> cases v
    . exact Or.inr ⟨false,by funext x;simp [jr]⟩
    . simpa [jr] using hb
    . simpa [jr] using hb
    . exact Or.inr ⟨true,by funext x;simp [jr]⟩
  . cases op <;> cases v
    . exact Or.inr ⟨false,by funext x;simp [jr]⟩
    . simpa [jr] using ha
    . simpa [jr] using ha
    . exact Or.inr ⟨true,by funext x;simp [jr]⟩
lemma qa2 {R} {bank v} (w:jv R) (h:q4 bank v) :
    q4 (w :: bank) v :=
  h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr
lemma qu1 {R} (roots:List (jv R)) {p bank a} (hp:vk roots p bank)
    (ha:q4 bank a) :
    ∃ q next,vk roots q next /\ q4 next (inv a) ∧
        (∀ v,q4 bank v -> q4 next v) /\ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c:zw a
  . exact ⟨p,bank,hp,Or.inr (qes c),fun _ h => h,by simp [cost,c,qes c]⟩
  . exact ⟨p+1,_,qmq hp ha,Or.inl (by simp),fun _ h => qa2 _ h,by simp [cost,c]⟩
lemma qu0 {R} (roots:List (jv R)) {p bank a b} (op) (hp:vk roots p bank)
    (ha:q4 bank a) (hb:q4 bank b) :
    ∃ q next,vk roots q next /\ q4 next (jr op a b) ∧
        (∀ v,q4 bank v -> q4 next v) ∧
        q+cost a+cost b ≤ p+1+cost (jr op a b) := by
  classical
  by_cases c:zw a \/ zw b
  . refine ⟨p,bank,hp,qko op c ha hb,fun _ h => h,?_⟩
    by_cases ca:zw a <;> by_cases cb:zw b
    . simp [cost,ca,cb,qks op ca cb]
    . simp [cost,ca,cb]
    . simp [cost,ca,cb]
    . exact False.elim (c.elim ca cb)
  . have ca:¬zw a := fun h => c (Or.inl h)
    have cb:¬zw b := fun h => c (Or.inr h)
    exact ⟨p+1,_,qmp op hp ha hb,Or.inl (by simp),fun _ h => qa2 _ h,
      by simp [cost,ca,cb]⟩
lemma qhz {α : Type} {k:Bool} {x a : α} {xs} (h:x ∈ vi k a xs) :
    x=a \/ x ∈ xs := by cases k <;> simp_all [vi]
lemma qfz {R} {goal:jv R} (nc:¬zw goal) {s ws}
    (h:Run goal s ws) (roots:List (jv R)) {p bank}
    (hp:vk roots p bank) (hs:qar bank ws) :
    ∃ q next,vk roots q next /\ q4 next goal /\ q+mass ws ≤ p+s := by
  classical
  refine h (fun s ws => ∀ p bank,vk roots p bank -> qar bank ws →
      ∃ q next,vk roots q next /\ q4 next goal /\ q+mass ws ≤ p+s)
    ?_ ?_ ?_ ?_ p bank hp hs
  . intro p bank hp hs
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  . intro s xs zs eq ih p bank hp hs
    have hsub:qar bank xs := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih p bank hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,← (eq.map cost).sum_eq] using hl⟩
  . intro s a rest save ih p bank hp hs
    obtain ⟨r,T,hT,hz,inc,le⟩ := qu1 roots hp (hs a (by simp))
    have ht:qar T (inv a :: vi save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      . exact hz
      . exact inc v (hs v (List.mem_cons.mpr (qhz hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih r T hT ht
    have hlen := qe4 a rest save
    rw [yz] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  . intro s a b rest op ka kb ih p bank hp hs
    obtain ⟨r,T,hT,hz,inc,le⟩ := qu0 roots op hp (hs a (by simp)) (hs b (by simp))
    have ht:qar T (jr op a b :: vi ka a (vi kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      . exact hz
      . apply inc v
        apply hs
        rcases qhz hh with rfl | hh
        . simp
        . exact List.mem_cons_of_mem _ (List.mem_cons.mpr (qhz hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih r T hT ht
    have hlen := qe4 a (vi kb b rest) ka
    have hlen' := qe4 b rest kb
    rw [yz] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [yz,yz]
    omega
def qj {R S:Type} (rows:S -> R) (a:jv R) : jv S :=
  fun r => a (rows r)
lemma qdj {R S:Type} (rows:S -> R) (k:Bool) (a:jv R) (ws) :
    (vi k a ws).map (qj rows) =
    vi k (qj rows a) (ws.map (qj rows)) := by
  cases k <;> simp [vi]
lemma qnm {R S:Type} (rows:S -> R) {goal s ws} (h:Run goal s ws) :
    Run (qj rows goal) s (ws.map (qj rows)) :=
  h (fun s ws => Run (qj rows goal) s (ws.map (qj rows)))
    qpi
    (fun p ih => qd5 (p.map _) ih)
    (fun save ih => by
      simp only [List.map_cons,qdj] at ih ⊢
      exact qvt save ih)
    (fun op ka kb ih => by
      simp only [List.map_cons,qdj] at ih ⊢
      cases op
      . exact qm6 false ka kb ih
      . exact qm6 true ka kb ih)
lemma w7 {R S:Type} (rows:S -> R) {goal s ws} (h:Run goal s ws)
    (nc:¬zw (qj rows goal)) {roots:List (jv S)} {p bank L}
    (hp:vk roots p bank) (hs:qar bank (ws.map (qj rows)))
    (hl:∀ q bs,vk roots q bs -> q4 bs (qj rows goal) -> L ≤ q) :
    L+mass (ws.map (qj rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := qfz nc (qnm rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega
abbrev Row := Fin 512
def qm (a:Sig) : jv Row := fun r => bit r a
def wy (f:jv Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
lemma qbr (f:jv Row) (r:Row) : bit r (wy f)=f r := by
  simp only [bit,wy,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [r.isLt]
lemma w2 (v:Sig) : wy (qm v)=v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact qbr (qm v) ⟨j,hj⟩
lemma qbj (f:jv Row) : qm (wy f)=f := by
  funext r
  exact qbr f r
lemma qm7 (a:Sig) : qm (neg a)=inv (qm a) := by
  funext r
  exact yh _ _
lemma qm8 (d:Bool) (a b:Sig) :
    qm (bin d a b)=jr d (qm a) (qm b) := by
  funext r
  cases d <;> exact qam _ _ _ _
lemma qh0 {α β : Type} (f : α -> β) (d:Bool) (a : α) (l:List α) :
    (vi d a l).map f=vi d (f a) (l.map f) := by cases d <;> rfl
lemma qc7 {α : Type} (k:Bool) (a : α) (l:List α)
    (hn:l.Nodup) (ha:a ∉ l) : (vi k a l).Nodup := by cases k <;> simp [vi,hn,ha]
lemma qbl (k:Bool) (a:Sig) (l:List Sig) :
    (vi k a l).toFinset=if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [vi]
lemma qcm {T:Sig} {k u S} (h:v4 T k u S) (v:List Sig)
    (hv:v.Nodup) (eqv:v.toFinset=S) : Run (qm T) k (v.map qm) := by
  classical
  exact h (fun k _ S => ∀ v:List Sig,v.Nodup -> v.toFinset=S -> Run (qm T) k (v.map qm))
    (fun _ v hv eqv => by
      have eq : [T].Perm v := by
        apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
        simp [eqv]
      exact qd5 (eq.map _) qpi)
    (fun {_ _ U a} _ _ fresh ih v hv eqv => by
      let rest := (U.erase a).toList
      let save := decide (a ∈ U)
      let tail := vi save a rest
      have er:rest.toFinset=U.erase a := by simp [rest]
      have hm:a ∉ rest := by simp [rest]
      have hr:rest.Nodup := Finset.nodup_toList _
      have ht:tail.toFinset=U := by
        rw [show tail=vi save a rest by rfl,qbl,er]
        by_cases hh:a ∈ U <;> simp [save,hh]
      have nd := qc7 save a rest hr hm
      have hf:neg a ∉ tail := by
        intro hz
        exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
      have progress := ih (neg a :: tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
      rw [List.map_cons,qh0,qm7] at progress
      have perm:(a :: rest).Perm v := by
        apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
        simp [er,eqv]
      exact qd5 (perm.map _) (qvt save progress))
    (fun {_ _ U a b d} _ _ hab _ fresh ih v hv eqv => by
      let rest := ((U.erase a).erase b).toList
      let ka := decide (a ∈ U)
      let kb := decide (b ∈ U)
      let mid := vi kb b rest
      let tail := vi ka a mid
      have er:rest.toFinset=(U.erase a).erase b := by simp [rest]
      have ar:a ∉ rest := by simp [rest]
      have br:b ∉ rest := by simp [rest]
      have hr:rest.Nodup := Finset.nodup_toList _
      have bm := qc7 kb b rest hr br
      have am:a ∉ mid := by cases h:kb <;> simp [mid,vi,h,hab,ar]
      have nd := qc7 ka a mid bm am
      have ht:tail.toFinset=U := by
        change (vi ka a (vi kb b rest)).toFinset=U
        rw [qbl,qbl,er]
        ext j
        by_cases aa:a ∈ U <;> by_cases bb:b ∈ U <;> by_cases aj:j=a <;>
          by_cases bj:j=b <;> simp_all [ka,kb]
      have hf:bin d a b ∉ tail := by
        intro hz
        exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
      have progress := ih (bin d a b :: tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
      change Run _ _ ((bin d a b :: vi ka a (vi kb b rest)).map qm) at progress
      rw [List.map_cons,qh0,qh0,qm8] at progress
      have perm:(a :: b :: rest).Perm v := by
        apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
        ext j
        by_cases ja:j=a <;> by_cases jb:j=b <;> simp_all
      exact qd5 (perm.map _) (qm6 d ka kb progress))
    v hv eqv
lemma qv6 (f:jv Row) : wy (inv f)=neg (wy f) := by
  rw [← w2 (neg (wy f)),qm7,qbj]
lemma qv7 (d:Bool) (f g:jv Row) :
    wy (jr d f g)=bin d (wy f) (wy g) := by
  rw [← w2 (bin d (wy f) (wy g)),qm8,qbj,qbj]
lemma w4 {bank:List (jv Row)} {a} (h:q4 bank a) :
    zr (bank.map wy) (wy a) := by
  rcases h with hm | ⟨b,rfl⟩
  . exact Or.inl (List.mem_map_of_mem hm)
  . apply Or.inr
    cases b
    . have z:wy (fun _ => false)=zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (qbr _ ⟨j,hj⟩).trans (j5 ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    . have z:wy (fun _ => true)=one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (qbr _ ⟨j,hj⟩).trans (yg ⟨j,hj⟩).symm
      exact fun hp => hp.2 z
lemma zbz {w a} (ha:zr w a) :
    zr w (neg a) \/ qa5 w (neg a) := by
  rcases y6 ha with rfl | rfl | ⟨hm,hp⟩
  . exact Or.inl (Or.inr fun h => h.2 qd7.1)
  . exact Or.inl (Or.inr fun h => h.1 qd7.2)
  . exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
lemma qms {w:List Sig} {z:Sig} {T k t S} (h:v4 T k t S)
    (hz:zr w z \/ qa5 w z) (hs:∀ a ∈ S,a ∈ z :: w) :
    ∃ k' t' S',k' ≤ k+1 /\ v4 T k' t' S' /\ ∀ a ∈ S',a ∈ w := by
  apply qe3 h hz
  intro a hm
  simpa [or_comm] using hs a hm
lemma qi3 {roots:List (jv Row)} {p bank}
    (h:vk roots p bank) {T k t S} (run:v4 T k t S)
    (sub:∀ a ∈ S,a ∈ bank.map wy) :
    ∃ l v U,l ≤ p+k /\ v4 T l v U /\ ∀ a ∈ U,a ∈ roots.map wy := by
  refine h (fun p bank => ∀ k t S,v4 T k t S -> (∀ a ∈ S,a ∈ bank.map wy) →
      ∃ l v U,l ≤ p+k /\ v4 T l v U /\ ∀ a ∈ U,a ∈ roots.map wy)
    ?_ ?_ ?_ k t S run sub
  . intro k t S run sub
    exact ⟨k,t,S,by omega,run,sub⟩
  . intro p bank a ha ih k t S run sub
    rw [List.map_cons,qv6] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := qms run (zbz (w4 ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih k' t' S' run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  . intro p bank a b d ha hb ih k t S run sub
    rw [List.map_cons,qv7] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := qms run (qni d (w4 ha) (w4 hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih k' t' S' run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
lemma qay {roots:List Sig} {p bank T} (hp:q7 T)
    (h:vk (roots.map qm) p bank) (hit:q4 bank (qm T)) :
    ∃ k t S,k ≤ p /\ v4 T k t S /\ ∀ a ∈ S,a ∈ roots := by
  have hm := w4 hit
  rw [w2] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := qi3 h (qda hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,w2] using hs
lemma qak {T k t S} (h:v4 T k t S) {r s:Row}
    (diff:bit r T ≠ bit s T) : ∃ a ∈ S,bit r a ≠ bit s a :=
  h (fun _ _ S => ∃ a ∈ S,bit r a ≠ bit s a)
    (fun _ => ⟨_,by simp,diff⟩)
    (fun {_ _ _ a} _ _ _ ih => by
      obtain ⟨v,hv,hd⟩ := ih
      rcases Finset.mem_insert.mp hv with rfl | hu
      . refine ⟨a,by simp,?_⟩
        exact fun he => hd (by rw [yh,yh,he])
      . exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩)
    (fun {_ _ _ a b d} _ _ _ _ _ ih => by
      obtain ⟨v,hv,hd⟩ := ih
      rcases Finset.mem_insert.mp hv with rfl | hu
      . by_cases aeq:bit r a=bit s a
        . refine ⟨b,by simp,?_⟩
          intro beq
          exact hd (by rw [qam,qam,aeq,beq])
        . exact ⟨a,by simp,aeq⟩
      . exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩)
lemma vz {T k t S} (h:v4 T k t S) (roots:List Sig) (a:Sig)
    (sub:∀ v ∈ S,v ∈ roots) (r s:Row) (diff:bit r T ≠ bit s T)
    (isolated:∀ v ∈ roots,v ≠ a -> bit r v=bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := qak h diff
  by_cases veq:v=a
  . simpa [veq] using hv
  . exact False.elim (hd (isolated v (sub v hv) veq))
lemma qt9:List.ofFn (fun j:Fin 9 => inputs.getD j.val zero)=inputs := rfl
def q5 (f:Row -> Row) (a:Sig) := wy fun r => bit (f r) a
lemma jz (f:Row -> Row) (a:Sig) (r:Row) :
    bit r (q5 f a)=bit (f r) a := qbr _ _
lemma ju (f:Row -> Row) (a:Sig) :
    qm (q5 f a)=qj f (qm a) := by funext r;exact jz f a r
lemma qax (f:Row -> Row) (a:Sig) : q5 f (neg a)=neg (q5 f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (q5 f (neg a))=bit ⟨j,hj⟩ (neg (q5 f a))
  rw [jz,yh,yh,jz]
lemma qdt (f:Row -> Row) (d:Bool) (a b:Sig) :
    q5 f (bin d a b)=bin d (q5 f a) (q5 f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (q5 f (bin d a b))=bit ⟨j,hj⟩ (bin d (q5 f a) (q5 f b))
  rw [jz,qam,qam,jz,jz]
lemma qip (f:Row -> Row) (onto:Function.Surjective f) :
    Function.Injective (q5 f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a=bit ⟨j,hj⟩ b
  rw [jz,jz,hr] at he
  exact he
lemma wv (f:Row -> Row) : q5 f zero=zero /\ q5 f one=one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  . exact (jz f zero ⟨j,hj⟩).trans ((j5 _).trans (j5 ⟨j,hj⟩).symm)
  . exact (jz f one ⟨j,hj⟩).trans ((yg _).trans (yg ⟨j,hj⟩).symm)
lemma qnr {mode T k t S} (h:j3 mode T k t S) (f:Row -> Row)
    (onto:Function.Surjective f) (fix0:mode=0 \/ q5 f qu=qu) :
    j3 mode (q5 f T) k t (S.image (q5 f)) := by
  classical
  have inj := qip f onto
  obtain ⟨fz,fo⟩ := wv f
  have pp (v) (p:q7 v) : q7 (q5 f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  have eqx0 (h0:q5 f qu=qu) (v:Sig) : (q5 f v==qu)=(v==qu) := by
    by_cases hv:v=qu
    . simp [hv,h0]
    . have hne:q5 f v ≠ qu := fun e => hv (inj (e.trans h0.symm))
      simp [hv,hne]
  have eqnx0 (h0:q5 f qu=qu) (v:Sig) : (q5 f v==qn)=(v==qn) := by
    have hn0:q5 f qn=qn := by rw [qn,qax,h0]
    by_cases hv:v=qn
    . simp [hv,hn0]
    . have hne:q5 f v ≠ qn := fun e => hv (inj (e.trans hn0.symm))
      simp [hv,hne]
  have au (a:Sig) : jc mode (q5 f a)=jc mode a := by
    rcases fix0 with rfl | h0
    . simp only [jc,Nat.reduceBEq,Bool.false_eq_true,ite_false]
    . simp only [jc,bne,eqx0 h0,eqnx0 h0]
  have ab (d:Bool) (a b:Sig) (ka kb:Bool) :
      zq mode d (q5 f a) (q5 f b) ka kb=zq mode d a b ka kb := by
    rcases fix0 with rfl | h0
    . simp only [zq,Nat.reduceBEq,Bool.false_eq_true,ite_false]
    . simp only [zq,bne,eqx0 h0,eqnx0 h0]
  exact h (fun k t S => j3 mode (q5 f T) k t (S.image (q5 f)))
    (fun hp => by simpa using qaz (mode := mode) (pp _ hp))
    (fun {_ _ U a} hp hallow hf ih => by
      have fresh:q5 f (neg a) ∉ (insert a U).image (q5 f) := by
        intro hm
        obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
        exact hf (inj eq ▸ hv)
      simp only [Finset.image_insert,qax] at fresh ih ⊢
      exact qaf (pp _ hp) (by rw [au];exact hallow) fresh ih)
    (fun {_ _ U a b d} ha hb hab hallow hf ih => by
      have fresh:q5 f (bin d a b) ∉ (insert a (insert b U)).image (q5 f) := by
        intro hm
        obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
        exact hf (inj eq ▸ hv)
      have mem_eq (v:Sig) : decide (q5 f v ∈ U.image (q5 f))=decide (v ∈ U) := by
        by_cases hv:v ∈ U
        . have hmi:q5 f v ∈ U.image (q5 f) := Finset.mem_image_of_mem _ hv
          simp only [hv,hmi,decide_true]
        . have hni:q5 f v ∉ U.image (q5 f) := by
            intro hm;obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp hm;exact hv (inj eq ▸ hw)
          simp only [hv,hni,decide_false]
      simp only [Finset.image_insert,qdt] at fresh ih ⊢
      refine yn (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) ?_ fresh ih
      rw [mem_eq,mem_eq,ab]
      exact hallow)
lemma qdi {T k t S} (h:v4 T k t S) (none:t=0) {r s:Row}
    (pos:bit r T=true) (negRow:bit s T=false) :
    ∃ a ∈ S,bit r a=true /\ bit s a=false :=
  h (fun _ t S => t=0 -> ∃ a ∈ S,bit r a=true /\ bit s a=false)
    (fun _ _ => ⟨_,by simp,pos,negRow⟩)
    (fun _ _ _ _ h0 => by omega)
    (fun {_ _ _ a b d} _ _ _ _ _ ih h0 => by
      obtain ⟨v,hv,hp,hn⟩ := ih h0
      rcases Finset.mem_insert.mp hv with rfl | hu
      . rw [qam] at hp hn
        cases d <;> cases p:bit r a <;> cases q:bit s a <;>
          cases u:bit r b <;> cases z:bit s b <;> simp_all
      . exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩)
    none
def qy (roots:List Sig) (T:Sig) (L:Nat) : Prop :=
  ∀ p bank,vk (roots.map qm) p bank -> q4 bank (qm T) -> L ≤ p
def zg (mode:Nat) (T:Sig) (cap:Nat) (S:Finset Sig) : Prop :=
  ∀ k t,k ≤ cap -> ¬j3 mode T k t S
abbrev wo (T:Sig) (cap:Nat) (S:Finset Sig) : Prop := zg 0 T cap S
lemma qgb {mode T cap S} (h:wo T cap S) : zg mode T cap S :=
  fun k t hk hr => h k t hk (wc hr)
def qdf (T:Sig) (roots:List Sig) (a:Sig) : Prop :=
  ∃ r s:Row,bit r T ≠ bit s T /\ ∀ v ∈ roots,v ≠ a -> bit r v=bit s v
lemma qbu {roots T L} (hp:q7 T)
    (essential:∀ a ∈ roots,qdf T roots a)
    (noRun:wo T L roots.toFinset) : qy roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := qay hp h ha
  have he:roots.toFinset=S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact vz run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)
lemma yt {v:Sig} (hv:q7 v) : ¬zw (qm v) := by
  rintro ⟨b,h⟩
  have hr:zr ([] : List Sig) v := by
    have avail:q4 ([] : List (jv Row)) (qm v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,w2] using w4 avail
  exact (hr.resolve_left (by simp)) hv
lemma qft {R} (a b:List (jv R)) : mass (a ++ b)=mass a+mass b := by
  simp [mass]
lemma qc0 {R} (xs:List (jv R)) (hc:∀ x ∈ xs,zw x) :
    mass xs=xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [yz,List.length_cons,cost,ite_eq_left_iff,ih (fun x hx => hc x (by simp [hx]))]
    split
    . omega
    . next h => exact False.elim (h ha)
lemma wb {roots:List Sig} {T:Sig} {k t S L}
    (pT:q7 T) (run:v4 T k t S) (sub:∀ a ∈ S,a ∈ roots) (hL:qy roots T L) :
    L ≤ k := by
  classical
  have nd:S.toList.Nodup := Finset.nodup_toList S
  have eqv:S.toList.toFinset=S := by simp
  have r := qcm run S.toList nd eqv
  have supp:qar (roots.map qm) (S.toList.map qm) := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,bs,hq,ht,hle⟩ := qfz (yt pT) r (roots.map qm) qad supp
  have hlq := hL q bs hq ht
  omega
lemma qfv {roots other:List Sig} {T G:Sig} (pT:q7 T) (pG:q7 G)
    (r:Row -> Row) (eq:q5 r T=G)
    (covered:∀ a ∈ roots,q4 (other.map qm) (qm (q5 r a)))
    (singles:Finset Sig) (necessary:∀ a ∈ singles,qdf T roots a)
    (constant:∀ a ∈ singles,zw (qm (q5 r a)))
    (L:Nat) (prior:qy other G L) : qy roots T (L+singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := qay pT hh ha
  have subS:singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact vz run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd:front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe:front.toFinset=S := by ext a;simp [front,Finset.union_sdiff_of_subset subS]
  have run' := qcm run front nd fe
  have gc:qj r (qm T)=qm G := (ju _ _).symm.trans (congrArg qm eq)
  have supp:qar (other.map qm) ((front.map qm).map (qj r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [← ju]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := w7 r run' (gc ▸ yt pG) qad supp
    (L := L) (gc ▸ prior)
  have massLo:singles.card ≤ mass ((front.map qm).map (qj r)) := by
    simp only [front,List.map_append,qft]
    let xs := (singles.toList.map qm).map (qj r)
    have only:∀ v ∈ xs,zw v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [← ju]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := qc0 xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs+_
    rw [sz]
    omega
  omega
def qac (ws:List Sig) (a:Sig) (keep:Bool) : List Sig :=
  neg a :: vi keep a (ws.erase a)
def wk (ws:List Sig) (a b:Sig) (d ka kb:Bool) : List Sig :=
  bin d a b :: vi ka a (vi kb b ((ws.erase a).erase b))
lemma qfe {l:List Sig} (h:l.Nodup) (a:Sig) : (l.erase a).toFinset=l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]
lemma qu2 {mode:Nat} {T:Sig} {cap:Nat} {ws:List Sig} (hn:ws.Nodup) (out:T ∉ ws)
    (oneStep:∀ a ∈ ws,∀ keep,jc mode a=true -> neg a ∉ ws -> q7 (neg a) →
      (qac ws a keep).length ≤ cap →
      zg mode T (cap - 1) (qac ws a keep).toFinset)
    (twoStep:∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a ≠ b -> zq mode d a b ka kb=true →
      bin d a b ∉ ws -> q7 (bin d a b) -> (wk ws a b d ka kb).length ≤ cap →
      zg mode T (cap - 1) (wk ws a b d ka kb).toFinset) :
    zg mode T cap ws.toFinset := by
  classical
  intro k t hk h
  rcases qct h with ⟨rfl,rfl,he,_⟩ | ⟨k',t',U,a,rfl,rfl,he,ha,hallow,hf,tail⟩ |
      ⟨k',U,a,b,d,rfl,he,ha,hb,hab,hallow,hf,tail⟩
  . have mem:T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  . have am:a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh:neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := qeq tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := qfe hn a
    have rest:(vi keep a (ws.erase a)).toFinset=U := by
      rw [qbl,er,he]
      by_cases hm:a ∈ U <;> simp [keep,hm]
    have nd:(qac ws a keep).Nodup := by
      have na:a ∉ ws.erase a := hn.not_mem_erase
      have nk := qc7 keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq:(qac ws a keep).toFinset=insert (neg a) U := by simp [qac,rest]
    have sc := (qit tail).2
    have len:(qac ws a keep).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep hallow fresh hz len k' t' (by omega) (eq.symm ▸ tail)
  . have am:a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm:b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh:bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := qeq tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er:rest.toFinset=(ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,qfe (hn.erase _) b,qfe hn a]
    have ke:(vi ka a (vi kb b rest)).toFinset=U := by
      rw [qbl,qbl,er,he]
      ext j
      by_cases aa:a ∈ U <;> by_cases bb:b ∈ U <;> by_cases ja:j=a <;>
        by_cases jb:j=b <;> simp_all [ka,kb]
    have rn:rest.Nodup := (hn.erase _).erase _
    have ar:a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br:b ∉ rest := (hn.erase a).not_mem_erase
    have nk := qc7 kb b rest rn br
    have ax:a ∉ vi kb b rest := by cases kb <;> simp [vi,ar,hab]
    have nd:(wk ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,qc7 ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq:(wk ws a b d ka kb).toFinset=insert (bin d a b) U := by
      change (bin d a b :: vi ka a (vi kb b rest)).toFinset=_
      simp [ke]
    have sc := (qit tail).2
    have len:(wk ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab hallow fresh hz len k' t (by omega) (eq.symm ▸ tail)
def Sep (T:Sig) (width:Nat) (pos negRow:Fin width -> Row)
    (asig:Sig -> BitVec width × BitVec width) : Prop :=
  (∀ i,bit (pos i) T=true /\ bit (negRow i) T=false) ∧
  ∀ w i,(asig w).1.getLsbD i.val=bit (pos i) w ∧
    (asig w).2.getLsbD i.val=bit (negRow i) w
def zy {n} (oriented:Bool) (s:BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented:Bool) (sig:Sig -> BitVec n × BitVec n) : List Sig -> BitVec n
  | [] => 0
  | a :: ws => zy oriented (sig a) ||| covered oriented sig ws
lemma qq1 {n:Nat} {oriented:Bool} {sig:Sig -> BitVec n × BitVec n} {ws:List Sig} {i:Fin n} :
    (covered oriented sig ws).getLsbD i.val=true ↔
    ∃ a ∈ ws,(zy oriented (sig a)).getLsbD i.val=true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
lemma qq2 {T k t S} (h:v4 T k t S) {ws:List Sig} (he:ws.toFinset=S)
    {width:Nat} {r s:Fin width -> Row} {sig} (correct:Sep T width r s sig)
    (oriented:Bool) (zeroNot:oriented=true -> t=0) :
    covered oriented sig ws=BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i:Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes];simp only [hj,decide_true]
  apply (qq1 (i := i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := qak h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [zy,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx:bit (r i) a <;> cases hy:bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := qdi h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [zy,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
lemma qjk {T cap ws k t} (h:v4 T k t (List.toFinset ws))
    (hk:k ≤ cap) (hn:ws.Nodup) {n:Nat} {r s:Fin n -> Row} {sig}
    (correct:Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws=BitVec.allOnes n := by
  apply qq2 h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (qdb h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega
def qfs (raw:List Sig) (T d:Sig) (L:Nat) : Prop :=
  ∃ (f:Row -> Row) (roots:List Sig),(∀ r,bit (f r) d=true) ∧
    (∀ a ∈ raw,q4 (roots.map qm) (qj f (qm a))) ∧
    ¬zw (qj f (qm T)) ∧
    ∀ p bank,vk (roots.map qm) p bank -> q4 bank (qj f (qm T)) -> L ≤ p
def q0 (d a:Sig) := a &&& d
def qz (d:Sig) (pool:List Sig) (a:Sig) :=
  let m := q0 d a
  m==zero||m==d||(pool.map (q0 d)).any (fun v => v==m)
lemma qwi {f:Row -> Row} {d a b:Sig} (dom:∀ r,bit (f r) d=true)
    (eq:q0 d a=q0 d b) :
    qj f (qm a)=qj f (qm b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a=bit (f r) b
  simpa only [bit,q0,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using h
lemma qfu {f:Row -> Row} {d a:Sig} (dom:∀ r,bit (f r) d=true)
    (eq:q0 d a=zero) : qj f (qm a)=fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a=false
  rw [j5] at he
  simpa only [bit,q0,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
lemma qis {f:Row -> Row} {d a:Sig} (dom:∀ r,bit (f r) d=true)
    (eq:q0 d a=d) : qj f (qm a)=fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a=true
  rw [dom r] at he
  simpa only [bit,q0,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
def yc (f:Row -> Row) (bank:List (jv Row)) (pool:List Sig) :=
  ∀ a ∈ pool,q4 bank (qj f (qm a))
lemma jq {f:Row -> Row} {d a:Sig} {bank pool}
    (dom:∀ r,bit (f r) d=true) (supplyB:yc f bank pool)
    (check:qz d pool a=true) : q4 bank (qj f (qm a)) := by
  simp only [qz,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  . exact Or.inr ⟨false,qfu dom hz⟩
  . exact Or.inr ⟨true,qis dom ho⟩
  . exact qwi dom he ▸ supplyB v hv
abbrev ya := Nat × Sig × Sig
def ql (c:ya) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def yk (d:Sig) (pool:List Sig) (c:ya) :=
  qz d pool c.2.1&&(c.1==2||qz d pool c.2.2)
lemma qiq {f:Row -> Row} {d:Sig} {roots bank pool q}
    (dom:∀ r,bit (f r) d=true) (hp:vk roots q bank) (hs:yc f bank pool)
    (c:ya) (valid:yk d pool c=true) :
    ∃ next,vk roots (q+1) next /\ yc f next (ql c :: pool) := by
  have ok:qz d pool c.2.1=true /\ (c.1==2||qz d pool c.2.2)=true := by
    simpa only [yk,Bool.and_eq_true] using valid
  have ha := jq dom hs ok.1
  let z := qj f (qm (ql c))
  have hz:vk roots (q+1) (z :: bank) := by
    by_cases unary:c.1=2
    . change vk _ _ (qj f (qm (ql c)) :: _)
      rw [ql,if_pos unary,qm7]
      exact qmq hp ha
    . have hb:qz d pool c.2.2=true := by simpa [unary] using ok.2
      have hz' := qmp (c.1==1) hp ha (jq dom hs hb)
      change vk _ _ (qj f (qm (ql c)) :: _)
      rw [ql,if_neg unary,qm8]
      have comm (b:Bool) (v w:jv Row) :
          qj f (jr b v w)=jr b (qj f v) (qj f w) := by
        cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  . exact Or.inl (by simp [z])
  . exact qa2 _ (hs _ hm)
def w0 (d:Sig) (pool:List Sig) : List ya -> Option (List Sig)
  | [] => some pool
  | c :: cs => if yk d pool c then w0 d (ql c :: pool) cs else none
lemma qc1 {d:Sig} {f:Row -> Row} (dom:∀ r,bit (f r) d=true)
    {roots bank q pool} (hp:vk roots q bank) (hs:yc f bank pool)
    (cs:List ya) {result} (ok:w0 d pool cs=some result) :
    ∃ next,vk roots (q+cs.length) next /\ yc f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok;exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [w0] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := qiq dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def qg (d a:Sig) := q0 d a==zero||q0 d a==d
lemma qce {d:Sig} {f:Row -> Row} (dom:∀ r,bit (f r) d=true)
    (ws:List Sig) : ws.countP (qg d) ≤ mass ((ws.map qm).map (qj f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,yz]
    cases h:qg d a
    . simpa using (Nat.le_add_left _ _ |> ih.trans)
    . have hc:zw (qj f (qm a)) := by
        have hh:q0 d a=zero \/ q0 d a=d := by
          simpa only [qg,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        . exact ⟨false,qfu dom hz⟩
        . exact ⟨true,qis dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def qd1 (d:Sig) (L k p:Nat) (pool ws:List Sig) :=
  decide (k+p < L+ws.countP (qg d))&&ws.all (qz d pool)
lemma qdk {raw T d L} (slice:qfs raw T d L) (cs:List ya)
    {pool ws cap} (built:w0 d raw cs=some pool)
    (nd:ws.Nodup) (cut:qd1 d L cap cs.length pool ws=true) :
    wo T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := qc1 dom (qad (roots := roots.map qm)) base cs built
  simp only [qd1,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS:qar bank ((ws.map qm).map (qj f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact jq dom hs (List.all_eq_true.mp all a ha)
  have b := w7 f (qcm h ws nd rfl) nc hr coveredS lo
  have massLo := qce dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega
abbrev qcj := Sig × Sig × Row
def qho (d r:Row) : Row :=
  if h:r.val < 512 - d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val - (512 - d.val),by omega⟩
def qmx (d:Row) : Row := Fin.ofNat 512 (512 - d.val)
def qa7 (m:qcj) (r:Row) : Row :=
  if bit r m.1 then qho m.2.2 r else if bit r m.2.1 then qho (qmx m.2.2) r else r
def mux (m a b:Sig) := (m &&& a) ||| (~~~m &&& b)
def qck (m:qcj) (a:Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (qmx m.2.2).val) a)
lemma qye (d r:Row) (a:Sig) : bit r (a.rotateRight d.val)=bit (qho d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h:r.val < 512 - d.val <;> simp [qho,h,r.isLt]
lemma za7 (p x y:Bool) : (p&&x||!p&&y)=(if p then x else y) := by cases p <;> simp
lemma zcz (r:Row) (m a b:Sig) :
    bit r (mux m a b)=if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact za7 _ _ _
lemma zba (r:Row) (m:qcj) (a:Sig) : bit r (qck m a)=bit (qa7 m r) a := by
  simp only [qck,zcz,qye,qa7]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def z5 (ms:List qcj) (r:Row) := ms.foldl (fun j m => qa7 m j) r
def q1 (ms:List qcj) (a:Sig) := ms.foldr qck a
lemma qbs (ms:List qcj) (a:Sig) (r:Row) :
    bit r (q1 ms a)=bit (z5 ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (zba r m _).trans (ih _)
lemma zt (ms:List qcj) (a:Sig) : q1 ms a=q5 (z5 ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (qbs ms a ⟨j,hj⟩).trans (jz _ _ ⟨j,hj⟩).symm
def qio (roots:List Sig) (w:Sig) := w==zero||w==one||roots.contains w
lemma qqt {roots w} (ok:qio roots w=true) :
    q4 (roots.map qm) (qm w) := by
  simp only [qio,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  . exact Or.inr ⟨false,funext j5⟩
  . exact Or.inr ⟨true,funext yg⟩
  . exact Or.inl (List.mem_map_of_mem hm)
def vt (ms:List qcj) (raw:List Sig) (T:Sig) (base:List Sig) (G:Sig) :=
  q1 ms T==G&&raw.all (fun a => qio base (q1 ms a))
lemma qbc {ms raw T base G} (ok:vt ms raw T base G=true) :
    q5 (z5 ms) T=G ∧
    ∀ a ∈ raw,q4 (base.map qm) (qm (q5 (z5 ms) a)) := by
  simp only [vt,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,zt] at ok
  exact ⟨ok.1,fun a ha => qqt (ok.2 a ha)⟩
lemma qe5 {ms raw T base G L} (ok:vt ms raw T base G=true)
    (pT:q7 T) (pG:q7 G) (hL:qy base G L) : qy raw T L := by
  obtain ⟨eq,supp⟩ := qbc ok
  simpa using qfv pT pG (z5 ms) eq supp ∅ (by simp) (by simp) L hL
lemma qki {ms raw T base G L d} (ok:vt ms raw T base G=true)
    (all:q1 ms d=one) (properG:q7 G) (hL:qy base G L) :
    qfs raw T d L := by
  obtain ⟨eq,supp⟩ := qbc ok
  have obs:qj (z5 ms) (qm T)=qm G :=
    (ju _ _).symm.trans (congrArg qm eq)
  refine ⟨z5 ms,base,?_,?_,?_,?_⟩
  . intro r
    rw [← qbs,all,yg]
  . intro a ha
    rw [← ju]
    exact supp a ha
  . rw [obs]
    exact yt properG
  . rw [obs]
    exact hL
def qhy (T:Sig) (roots:List Sig) (a:Sig) (rs:Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w==a||bit rs.1 w==bit rs.2 w)
lemma qiw {T roots a rs} (ok:qhy T roots a rs=true) : qdf T roots a := by
  simp only [qhy,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def zo (T:Sig) (raw:List Sig) (xs:List (Sig × Row × Row)) :=
  xs.all (fun a => qhy T raw a.1 a.2)
lemma vn {T raw xs} (ok:zo T raw xs=true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset,qdf T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact qiw (List.all_eq_true.mp ok _ hm)
lemma qfw {raw T} (properT:q7 T) (xs:List (Sig × Row × Row))
    (ok:zo T raw xs=true) :
    qy raw T ((xs.map Prod.fst).toFinset.card - 1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := qay properT hr hit
  have le:(xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := vn ok a ha
    exact vz run raw a sub r s hd iso
  have bound := (qdb run).2
  omega
def qfh (ms:List qcj) (T:Sig) (raw:List Sig) (base:List Sig) (G:Sig)
    (xs:List (Sig × Row × Row)) :=
  vt ms raw T base G&&zo T raw xs &&
    xs.all (fun a => q1 ms a.1==zero||q1 ms a.1==one)
lemma zbx {ms T raw base G xs L} (ok:qfh ms T raw base G xs=true)
    (properT:q7 T) (properG:q7 G) (low:qy base G L) :
    qy raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [qfh,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := qbc ok.1.1
  apply qfv properT properG _ eq supp _ (vn ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,zt] at hh
  rcases hh with h | h
  . rw [h]
    exact ⟨false,funext j5⟩
  . rw [h]
    exact ⟨true,funext yg⟩
def wi (m:Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def qo (m:Nat) : List Sig :=
  if m.testBit 10 then (wi m).map Prod.snd ++ [qn] else (wi m).map Prod.snd
def j4 (m:Nat) : List Sig :=
  (wi m).map fun (i,a) => if i==0 then neg a else a
def qai (m kind:Nat) : List Sig :=
  if !m.testBit 10 then qo m
  else if kind==0 then qo (m &&& 511)
  else if kind==1 then j4 (m &&& 511)
  else qo m
def qe0 (m j:Nat) :=
  if m.testBit j then (if m.testBit 9&&j==0 then neg (inputs.getD 0 zero) else inputs.getD j zero) else zero
def qa (m:Nat) : Sig :=
  let x := qe0 m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def jx:qcj := (qn,qu,Fin.ofNat 512 1)
def zgn:Nat -> Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def zgm:Nat -> Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def zgl:Nat -> Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def wf (z o:Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((zgn (fixed &&& 7)*zgm ((fixed >>> 3) &&& 7)*zgl ((fixed >>> 6) &&& 7)) <<< o)
def wu (z o:Nat) : List qcj :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def ji (v:Nat) : qcj :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j) - (1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def qeo (baseRow mask:Nat) : List (Sig × Row × Row) :=
  (wi mask).map fun (i,a) => (a,Fin.ofNat 512 baseRow,Fin.ofNat 512 (baseRow ^^^ (1 <<< i)))
def z2 (m hints:Nat) : List (Sig × Row × Row) :=
  let base := if m.testBit 9&&m.testBit 0 then 1 else 0
  (wi m).map fun (i,a) =>
    let r := base ^^^ (1 <<< ((hints >>> (4*i)) &&& 15))
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ^^^ (1 <<< i)))
def zz (T:Sig) := T != zero&&T != one
lemma zx (T:Sig) (h:zz T=true) : q7 T := by
  simpa only [zz,q7,Bool.and_eq_true,bne_iff_ne] using h
def qiv (m hints L:Nat) :=
  let xs := z2 m hints
  zz (qa m)&&zo (qa m) (qo m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card - 1)
lemma zgo {m hints L} (h:qiv m hints L=true) :
    qy (qo m) (qa m) L := by
  simp only [qiv,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (qfw (zx _ h.1.1) _ h.1.2 p bank hr ha)
abbrev vp := Nat × Nat × Nat × Nat × Nat × Nat
def qvx (m z o:Nat) := (m &&& 511) ^^^ ((m &&& 511) &&& (z ||| o))
def vu (m:Nat) : Sig := qa m
def yq (m z o q s L:Nat) (raw:List Sig) (ms:List qcj) (freeRoots:List Sig)
    (baseRow lz lo:Nat) (prior:Nat -> Nat) : Bool :=
  let G := q1 ms (vu m)
  let xs := qeo baseRow s
  let count := (xs.map Prod.fst).toFinset.card
  zz G&&vt ms raw (vu m) freeRoots G &&
    (q1 ms (wf z o)==one) &&
    (if q=0 then zo G freeRoots xs&&decide (L ≤ count - 1)
     else zz (qa q) &&
       qfh (wu lz lo) G freeRoots (qo q) (qa q) xs &&
       decide (L ≤ prior q+count))
lemma v2 {m z o q s L raw ms freeRoots baseRow lz lo} {prior:Nat -> Nat}
    (valid:∀ q,qy (qo q) (qa q) (prior q))
    (ok:yq m z o q s L raw ms freeRoots baseRow lz lo prior=true) :
    qfs raw (vu m) (wf z o) L := by
  let G := q1 ms (vu m)
  let xs := qeo baseRow s
  change (((zz G&&vt ms raw (vu m) freeRoots G) &&
    (q1 ms (wf z o)==one))&&_)=true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply qki ok.1.1.2 ok.1.2 (zx _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq:q=0
  . simp only [hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (qfw (zx _ ok.1.1.1) _ hh.1 p bank hr ha)
  . simp only [hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (zbx hh.1.2 (zx _ ok.1.1.1) (zx _ hh.1.1) (valid q) p bank hr ha)
def qbm (m:Nat) (c:vp) (prior:Nat -> Nat) : Bool :=
  let (z,o,q,s,L,kind) := c
  let free := qvx m z o
  let drop := qvx free q 0
  if !m.testBit 10 then
    let baseRow := if m.testBit 9&&free.testBit 0 then 1 else 0
    let lz := if m.testBit 9&&drop.testBit 0 then drop &&& (511 ^^^ 1) else drop
    let lo := if m.testBit 9&&drop.testBit 0 then 1 else 0
    yq m z o q s L (qo m) (wu z o) (qo free) baseRow lz lo prior
  else if kind==0 then
    yq m z o q s L (qo (m &&& 511)) (wu z o) (qo free) 0 drop 0 prior
  else if kind==1 then
    let baseRow := if free.testBit 0 then 1 else 0
    let lz := if drop.testBit 0 then drop &&& (511 ^^^ 1) else drop
    let lo := if drop.testBit 0 then 1 else 0
    yq m z o q s L (j4 (m &&& 511)) (wu z o ++ [jx]) (qo free) baseRow lz lo prior
  else
    let freeRoots := if free.testBit 0 then qo (1024 ||| free) else qo free
    yq m z o q s L (qo m) (wu z o) freeRoots 0 drop 0 prior
lemma qde {m:Nat} (c:vp) (prior:Nat -> Nat)
    (valid:∀ q,qy (qo q) (qa q) (prior q))
    (ok:qbm m c prior=true) :
    qfs (qai m c.2.2.2.2.2) (vu m) (wf c.1 c.2.1) c.2.2.2.2.1 := by
  obtain ⟨z,o,q,s,L,kind⟩ := c
  unfold qbm at ok
  unfold qai
  dsimp only at ok ⊢
  split at ok
  . next h10 =>
    simp only [h10,ite_true]
    exact v2 valid ok
  . next h10 =>
    simp only [h10,ite_false]
    split at ok
    . next hk0 =>
      simp only [hk0,ite_true]
      exact v2 valid ok
    . next hk0 =>
      simp only [hk0,ite_false]
      split at ok
      . next hk1 =>
        simp only [hk1,ite_true]
        exact v2 valid ok
      . next hk1 =>
        simp only [hk1,ite_false]
        exact v2 valid ok
def qe2 (old rep:Nat) (swaps:List Nat) :=
  zz (qa old)&&zz (qa rep) &&
    vt (swaps.map ji) (qo old) (qa old) (qo rep) (qa rep)
lemma qtu {old rep L swaps} (ok:qe2 old rep swaps=true)
    (h:qy (qo rep) (qa rep) L) : qy (qo old) (qa old) L := by
  simp only [qe2,Bool.and_eq_true] at ok
  exact qe5 ok.2 (zx _ ok.1.1) (zx _ ok.1.2) h
def qt (entries:List (Nat × Nat)) (q:Nat) :=
  ((entries.find? (fun a => a.1==q)).map Prod.snd).getD 0
lemma qe (entries:List (Nat × Nat))
    (sound:∀ e ∈ entries,qy (qo e.1) (qa e.1) e.2) (q:Nat) :
    qy (qo q) (qa q) (qt entries q) := by
  unfold qt
  cases h:entries.find? (fun a => a.1==q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit:(fun a:Nat × Nat => a.1==q) e=true :=
      List.find?_some (p := fun a:Nat × Nat => a.1==q) (a := e) h
    have eq:e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev z8 := Sig × Nat × Nat × List Sig
def qv (c:z8) : Sig := c.1
def jw (c:z8) : Nat := c.2.1
def j6 (c:z8) : Nat := c.2.2.1
def zp (c:z8) : List Sig := c.2.2.2
def wa (raw:List Sig) (T:Sig) (c:z8) :=
  ∃ (f:Row -> Row) (roots:List Sig) (bank:List (jv Row)),
    (∀ r,bit (f r) (qv c)=true) /\ ¬zw (qj f (qm T)) ∧
    (∀ q ws,vk (roots.map qm) q ws -> q4 ws (qj f (qm T)) -> jw c ≤ q) ∧
    vk (roots.map qm) (j6 c) bank /\ yc f bank (zp c) /\ True
lemma qiy {raw1 raw2 T c} (h:wa raw1 T c) : wa raw2 T c := h
lemma qrh {raw T d lb} (h:qfs raw T d lb) (cs:List ya) {ws}
    (build:w0 d raw cs=some ws) : wa raw T (d,lb,cs.length,ws) := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := qc1 dom (qad (roots := roots.map qm)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [j6] using hr,hs,trivial⟩
lemma qkf {raw T c} (valid:wa raw T c) (k:Nat) (rest:List Sig)
    (choice:ya) (paid:Bool)
    (known:∀ a ∈ rest,qz (qv c) (zp c) a=true)
    (buy:if paid then yk (qv c) (zp c) choice=true
       else qz (qv c) (zp c) (ql choice)=true)
    (bound:k+j6 c+paid.toNat <
      jw c+(ql choice :: rest).countP (qg (qv c)))
    (nd:(ql choice :: rest).Nodup) :
    wo T k (ql choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := ql choice :: rest
  have done (n:Nat) (out:List (jv Row)) (reach:vk (roots.map qm) n out)
      (zs:yc f out (ql choice :: rest)) (le:n=j6 c+paid.toNat) : False := by
    have covered:qar out ((ws.map qm).map (qj f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := w7 f (qcm run ws nd rfl) nc reach covered lo
    have cm := qce dom ws
    change k+j6 c+paid.toNat < jw c+ws.countP (qg (qv c)) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    . exact jq dom hs buy
    . exact jq dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := qiq dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    . exact hc _ (by simp)
    . have avail := jq dom hs (known _ hm)
      rcases avail with mem | con
      . have ha:qz (qv c) (zp c) a=true := known _ hm
        have point:∀ u ∈ zp c,q4 out (qj f (qm u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact jq dom point ha
      . exact Or.inr con
def jf (c:z8) (k:Nat) (rest:List Sig) (op:ya) :=
  let z := ql op
  let extra := !(qz (qv c) (zp c) z)
  ((k+j6 c+extra.toNat < jw c+(z :: rest).countP (qg (qv c))) &&
    rest.all (qz (qv c) (zp c)))&&(!extra||yk (qv c) (zp c) op)
lemma qdh {raw T c} (valid:wa raw T c) {k rest op}
    (nd:(ql op :: rest).Nodup) (cut:jf c k rest op=true) :
    wo T k (ql op :: rest).toFinset := by
  let extra := !(qz (qv c) (zp c) (ql op))
  apply qkf valid k rest op extra _ _ _ nd
  . simp only [jf,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  . simp only [jf,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he:qz (qv c) (zp c) (ql op) <;> simp_all [extra]
  . simp only [jf,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def qbb (raw:List Sig) (cs:List ya) (d:Sig) (lb:Nat) : Option z8 :=
  (w0 d raw cs).map (fun pool => (d,lb,cs.length,pool))
lemma qew {raw T d L cs c} (slice:qfs raw T d L)
    (h:qbb raw cs d L=some c) : wa raw T c := by
  unfold qbb at h
  cases he:w0 d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact qrh slice cs he
abbrev zi := BitVec 768
abbrev qhr := zi × zi
abbrev qw := Sig × qhr
def w9 {n:Nat} (r:Fin n -> Row) (v:Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
lemma jp {n:Nat} (r:Fin n -> Row) (v:Sig) (i:Fin n) :
    (w9 r v).getLsbD i.val=bit (r i) v := by
  simp only [w9,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def w5 (r s:Fin 768 -> Row) (a:Sig) : qhr := (w9 r a,w9 s a)
def qae (T:Sig) (r s:Fin 768 -> Row) :=
  ∀ i,bit (r i) T=true /\ bit (s i) T=false
lemma qzh {T r s} (h:qae T r s) : Sep T 768 r s (w5 r s) :=
  ⟨h,fun a i => ⟨jp _ _ _,jp _ _ _⟩⟩
def z9 (r s:Fin 768 -> Row) (x:qw) := x.2=w5 r s x.1
def qm4 (x:qw) : qw := (neg x.1,~~~x.2.1,~~~x.2.2)
def qtb (d:Bool) (x y:qw) : qw :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)
lemma qtv (r:Fin 768 -> Row) (a:Sig) : w9 r (neg a) = ~~~w9 r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := jp r (neg a) ⟨j,hj⟩
  rw [yh,← jp r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
lemma qtw (r:Fin 768 -> Row) (d:Bool) (a b:Sig) :
    w9 r (bin d a b)=if d then w9 r a ||| w9 r b else w9 r a &&& w9 r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := jp r (bin d a b) ⟨j,hj⟩
  rw [qam,← jp r a ⟨j,hj⟩,← jp r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
lemma qb7 {r s x} (h:z9 r s x) : z9 r s (qm4 x) := by
  change x.2=_ at h
  simp only [z9,qm4,w5,qtv,h]
lemma qet {r s x y} (d) (hx:z9 r s x) (hy:z9 r s y) :
    z9 r s (qtb d x y) := by
  change x.2=_ at hx
  change y.2=_ at hy
  cases d <;> simp only [z9,qtb,Bool.false_eq_true,ite_false,ite_true,w5,qtw,hx,hy]
def jy (op:Nat) (x y:qw) := if op=2 then qm4 x else qtb (op==1) x y
def qb:qw := (zero,0,0)
lemma qfn (r s) : z9 r s qb := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  . change (0:zi).getLsbD j=(w9 r zero).getLsbD j
    rw [show (w9 r zero).getLsbD j=bit (r ⟨j,hj⟩) zero from jp _ _ ⟨j,hj⟩,j5]
    simp
  . change (0:zi).getLsbD j=(w9 s zero).getLsbD j
    rw [show (w9 s zero).getLsbD j=bit (s ⟨j,hj⟩) zero from jp _ _ ⟨j,hj⟩,j5]
    simp
lemma qb8 {r s ws} (all:∀ v ∈ ws,z9 r s v) (i:Nat) :
    z9 r s (List.getD ws i qb) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e:ws[i]? with
  | none => exact qfn _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def qa0 (n:Nat) (bits:Nat) (ws:List qw) : List qw :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) qb
    let b := ws.getD ((bits >>> 4) &&& 15) qb
    qa0 k (bits >>> 10) (ws ++ [jy ((bits >>> 8) &&& 3) a b])
lemma qge (n bits) (ws) (r s) (base:∀ v ∈ ws,z9 r s v) :
    ∀ v ∈ qa0 n bits ws,z9 r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    . exact base _ hw
    . obtain rfl := List.mem_singleton.mp hz
      unfold jy
      split
      . exact qb7 (qb8 base _)
      . exact qet _ (qb8 base _) (qb8 base _)
def y8 (cols:Nat -> zi) (i:Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j:Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
lemma qrb:∀ r:Row,bit r (inputs.getD 0 zero)=r.val.testBit 0 := by decide +kernel
lemma qra:∀ r:Row,bit r (inputs.getD 1 zero)=r.val.testBit 1 := by decide +kernel
lemma qq9:∀ r:Row,bit r (inputs.getD 2 zero)=r.val.testBit 2 := by decide +kernel
lemma qq8:∀ r:Row,bit r (inputs.getD 3 zero)=r.val.testBit 3 := by decide +kernel
lemma qq7:∀ r:Row,bit r (inputs.getD 4 zero)=r.val.testBit 4 := by decide +kernel
lemma qq6:∀ r:Row,bit r (inputs.getD 5 zero)=r.val.testBit 5 := by decide +kernel
lemma qq5:∀ r:Row,bit r (inputs.getD 6 zero)=r.val.testBit 6 := by decide +kernel
lemma qq4:∀ r:Row,bit r (inputs.getD 7 zero)=r.val.testBit 7 := by decide +kernel
lemma qq3:∀ r:Row,bit r (inputs.getD 8 zero)=r.val.testBit 8 := by decide +kernel
lemma qb5:∀ (j:Fin 9) (r:Row),
    bit r (inputs.getD j.val zero)=r.val.testBit j.val := by
  intro j r
  fin_cases j
  . exact qrb r
  . exact qra r
  . exact qq9 r
  . exact qq8 r
  . exact qq7 r
  . exact qq6 r
  . exact qq5 r
  . exact qq4 r
  . exact qq3 r
lemma qap (cols:Nat -> zi) (i:Fin 768) (j:Fin 9) :
    bit (y8 cols i) (inputs.getD j.val zero)=(cols j.val).getLsbD i.val := by
  rw [qb5]
  change (BitVec.ofBoolListLE (List.ofFn (fun h:Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val=_
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def qd6 (m:Nat) (p q:Nat -> zi) : List qw :=
  let base := (wi m).map (fun (j,a) => (a,p j,q j))
  if m.testBit 10 then base ++ [(qn,~~~(p 0),~~~(q 0))] else base
lemma qcy {m j a} (h:(j,a) ∈ wi m) :
    j < 9 /\ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
lemma qnn (m) (p q:Nat -> zi) :
    ∀ a ∈ qd6 m p q,z9 (y8 p) (y8 q) a := by
  have base_f:∀ a ∈ (wi m).map (fun (j,a) => (a,p j,q j)),
      z9 (y8 p) (y8 q) a := by
    intro a ha
    obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
    obtain ⟨hj,rfl⟩ := qcy hv
    apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
    . exact (qap p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (jp _ _ ⟨i,hi⟩).symm
    . exact (qap q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (jp _ _ ⟨i,hi⟩).symm
  have x0_f:z9 (y8 p) (y8 q) (qu,p 0,q 0) := by
    apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
    . exact (qap p ⟨i,hi⟩ ⟨0,by decide⟩).symm.trans (jp _ _ ⟨i,hi⟩).symm
    . exact (qap q ⟨i,hi⟩ ⟨0,by decide⟩).symm.trans (jp _ _ ⟨i,hi⟩).symm
  intro a ha
  unfold qd6 at ha
  split at ha
  . rcases List.mem_append.mp ha with hb | hx
    . exact base_f a hb
    . obtain rfl := List.mem_singleton.mp hx
      have hdn:(qn,~~~p 0,~~~q 0)=qm4 (qu,p 0,q 0) := by unfold qn qm4;rfl
      rw [hdn]
      exact qb7 x0_f
  . exact base_f a ha
def qh1 (m:Nat) (v:Nat -> zi) : zi :=
  let x := fun j => if m.testBit j then (if m.testBit 9&&j==0 then ~~~(v 0) else v j) else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
lemma qu9 (m:Nat) (v:Nat -> zi) (i:Fin 768) (j:Fin 9) :
    bit (y8 v i) (qe0 m j.val) =
    ((if m.testBit j.val then (if m.testBit 9&&j.val==0 then ~~~(v 0) else v j.val) else 0) : zi).getLsbD i.val := by
  by_cases hh:m.testBit j.val=true
  . by_cases hf:(m.testBit 9&&j.val==0)=true
    . have hj0:j.val=0 := by
        simp only [Bool.and_eq_true,beq_iff_eq] at hf;exact hf.2
      simp only [qe0,hh,hf,ite_true,yh,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
      exact congrArg Bool.not (qap v i ⟨0,by decide⟩)
    . simpa [qe0,hh,hf] using qap v i j
  . simp [qe0,hh,j5]
lemma qn6 (m:Nat) (v:Nat -> zi) (i:Fin 768) :
    bit (y8 v i) (qa m)=(qh1 m v).getLsbD i.val := by
  have pos (j:Nat) (hj:j < 9) : (qe0 m j).getLsbD (y8 v i).val =
      ((if m.testBit j then (if m.testBit 9&&j==0 then ~~~(v 0) else v j) else 0) : zi).getLsbD i.val :=
    qu9 m v i ⟨j,hj⟩
  simp only [bit,qa,qh1,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),
    pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := zi × zi × zi
def yy (z:zi) (c:Cov) : Cov :=
  (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def je (d:Bool) (v:List qw) : Cov :=
  v.foldr (fun a c => yy (zy d a.2) c) (0,0,0)
def y3 (c:Cov) (a:zi) : zi := c.1 &&& ~~~(c.2.1 &&& a)
def qc5 (c:Cov) (a b:zi) : zi :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
lemma zcp (c:Cov) (a:zi) : y3 (yy a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [y3,yy,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
lemma zco (c:Cov) (a b:zi) : qc5 (yy a (yy b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [qc5,yy,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
lemma zam (c:Cov) (a b:zi) : yy a (yy b c)=yy b (yy a c) := by
  apply Prod.ext
  . apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [yy,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  . apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [yy,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
lemma qpl (d:Bool) {l r:List qw} (h:l.Perm r) : je d l=je d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (yy (zy d a.2)) ih
  | swap a b t => exact zam _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
lemma zal (d:Bool) (v:List qw) {r s} (good:∀ a ∈ v,z9 r s a) :
    (je d v).1=covered d (w5 r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (zy d a.2 ||| (je d v).1)=zy d (w5 r s a.1) ||| _
    rw [show a.2=w5 r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def wx (ws:List qw) (a:qw) (keep:Bool) :=
  if keep then ws else ws.erase a
def qdr (ws:List qw) (a b:qw) (ka kb:Bool) :=
  wx (wx ws a ka) b kb
lemma qcw {ws:List qw} (a:qw) (ha:a ∈ ws) :
    ws.Perm (a :: ws.erase a) := List.perm_cons_erase ha
lemma qff {ws:List qw} (d:Bool) (a:qw) (ha:a ∈ ws) (keep:Bool) :
    (je d (wx ws a keep)).1 =
      (if keep then (je d ws).1 else y3 (je d ws) (zy d a.2)) := by
  cases keep
  . change (je d (ws.erase a)).1=y3 (je d ws) _
    rw [qpl d (qcw a ha)]
    exact (zcp _ _).symm
  . rfl
lemma qqy {ws:List qw} (a b:qw) (ha:a ∈ ws) (hb:b ∈ ws) (hne:a ≠ b) :
    ws.Perm (a :: b :: (ws.erase a).erase b) := by
  have hm:b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (qcw a ha).trans (List.Perm.cons _ (qcw b hm))
lemma qyb {ws:List qw} (d:Bool) (a b:qw) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:a ≠ b) (ka kb:Bool) :
    (je d (qdr ws a b ka kb)).1 =
      (if ka then (if kb then (je d ws).1 else y3 (je d ws) (zy d b.2))
       else if kb then y3 (je d ws) (zy d a.2)
       else qc5 (je d ws) (zy d a.2) (zy d b.2)) := by
  cases ka <;> cases kb
  . change (je d ((ws.erase a).erase b)).1=qc5 (je d ws) _ _
    rw [qpl d (qqy a b ha hb ne)]
    exact (zco _ _ _).symm
  . exact qff d a ha false
  . exact qff d b hb false
  . rfl
def ye (a b:List Sig) := (a.all (fun x => b.contains x))&&(b.all (fun x => a.contains x))
lemma qcc {xs ys} (h:ye xs ys=true) : xs.toFinset=ys.toFinset := by
  simp only [ye,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩
def w6 (v:Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def we (xs:List Sig) := xs.foldl (fun v x => v+w6 x) 0
def wm (pools:List z8) (links:Nat -> List (List Sig)) (k:Nat)
    (rest:List Sig) (op:ya) :=
  let ws := ql op :: rest
  (links (we ws)).any (ye ws)||pools.any (fun p => jf p k rest op)
lemma qfp {mode raw T pools links k rest op}
    (pValid:∀ p ∈ pools,wa raw T p)
    (lValid:∀ tag xs,xs ∈ links tag -> zg mode T k (List.toFinset xs))
    (nd:(ql op :: rest).Nodup)
    (h:wm pools links k rest op=true) :
    zg mode T k (ql op :: rest).toFinset := by
  simp only [wm,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  . rw [qcc ok]
    exact lValid _ _ hx
  . exact qgb (qdh (pValid _ hp) nd ok)
abbrev qhs := Cov × Cov
def qbx (ws:List qw) : qhs := (je false ws,je true ws)
def qbg (c:qhs) (d:Bool) := if d then c.2 else c.1
lemma qud (ws) (d:Bool) : qbg (qbx ws) d=je d ws := by cases d <;> rfl
def y5 (v:Cov) (a b:zi) (un ka kb:Bool) :=
  if un then (if ka then v.1 else y3 v a) else
    if ka then (if kb then v.1 else y3 v b)
    else if kb then y3 v a else qc5 v a b
def jk (un ka kb:Bool) (a b:qw) (ws:List qw) :=
  if un then wx ws a ka else qdr ws a b ka kb
lemma qkj {ws:List qw} {a b:qw} (ha:a ∈ ws) (hb:b ∈ ws)
    (un ka kb d:Bool) (ne:un=false -> a ≠ b) :
    (je d (jk un ka kb a b ws)).1 =
      y5 (qbg (qbx ws) d) (zy d a.2) (zy d b.2) un ka kb := by
  rw [qud]
  cases un
  . exact qyb d a b ha hb (ne rfl) ka kb
  . exact qff d a ha ka
lemma qbz (ws:List qw) (a:qw) (k:Bool) : (wx ws a k).Sublist ws := by
  cases k
  . exact List.erase_sublist
  . exact List.Sublist.refl _
lemma qpj (ws:List qw) (a b:qw) (un ka kb:Bool) :
    (jk un ka kb a b ws).Sublist ws := by
  cases un
  . exact (qbz _ _ _).trans (qbz _ _ _)
  . exact qbz _ _ _
lemma qzq (ws:List qw) (a b:qw) (un ka kb:Bool) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:un=false -> a ≠ b) :
    (jk un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un||kb then 0 else 1) := by
  cases un
  . have hm:b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [jk,qdr,wx,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  . cases ka <;> cases kb <;> simp [jk,wx,List.length_erase_of_mem ha]
def qr (op:Nat) (a b:qw) := jy op a b
def zl (op:Nat) (a b:qw) : ya := (op,a.1,b.1)
lemma qdu (op) (a b:qw) :
    (qr op a b).1=ql (zl op a b) := by
  by_cases h:op=2
  . simp [qr,jy,h,qm4,ql,zl]
  . cases hh:op==1 <;> simp [qr,jy,h,hh,qtb,ql,zl]
lemma qi5 {r s a b} (ha:z9 r s a) (hb:z9 r s b) (op:Nat) :
    z9 r s (qr op a b) := by
  unfold qr jy
  split
  . exact qb7 ha
  . exact qet _ ha hb
abbrev j8 := Nat × Nat × List qw × qhs × List z8 × (Nat -> List (List Sig))
def vg (mode:Nat) (c:j8) (op:Nat) (a b z:qw) (ka kb:Bool) :=
  if !vd mode op a.1 b.1 ka kb then true else
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len > cap then true else
    let d := len==cap
    let rs := y5 (qbg cov d) (zy d a.2) (zy d b.2) un ka kb
    if (rs ||| zy d z.2) != BitVec.allOnes 768 then true else
    if !zz z.1||ws.any (fun v => v.1==z.1) then true else
      let rest := (jk un ka kb a b ws).map Prod.fst
      wm pools links (cap - 1) rest (zl op a b)
def qbp (ws:List qw) (op:Nat) (a b:qw) (ka kb:Bool) :=
  (qr op a b).1 :: (jk (op==2) ka kb a b ws).map Prod.fst
lemma qc4 {mode raw T r s ws pools links cap a b op ka kb}
    (pairs:qae T r s) (faith:∀ w ∈ ws,z9 r s w)
    (nd:(ws.map Prod.fst).Nodup) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:(op==2)=false -> a ≠ b) (hcap:0 < cap)
    (pv:∀ p ∈ pools,wa raw T p)
    (lv:∀ tag xs,xs ∈ links tag -> zg mode T (cap - 1) (List.toFinset xs))
    (hallow:vd mode op a.1 b.1 ka kb=true)
    (pro:q7 (qr op a b).1) (fresh:(qr op a b).1 ∉ ws.map Prod.fst)
    (test:vg mode (cap,ws.length,ws,qbx ws,pools,links) op a b (qr op a b) ka kb=true) :
    zg mode T (cap - 1) (qbp ws op a b ka kb).toFinset := by
  let z := qr op a b
  let rest := jk (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub:rest.Sublist ws := qpj _ _ _ _ _ _
  have ndc:child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr:ws.any (fun v => v.1==z.1)=false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp:zz z.1=true := by simpa [zz,q7] using pro
  have leq:1+(ws.length - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))=child.length := by
    change _=(z.1 :: rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,qzq _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hL := wc h
  have hsz := (qdb hL).2
  change child.toFinset.card+t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len:child.length ≤ cap := by omega
  unfold vg at test
  simp only [hallow,Bool.not_true,Bool.false_eq_true,ite_false] at test
  change (if 1+(ws.length - _ - _) > cap then true else _)=true at test
  rw [leq,if_neg (by omega)] at test
  have sep := qjk hL hk ndc (qzh pairs)
  have ce:cap - 1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g:(je d rest).1=covered d (w5 r s) (rest.map Prod.fst) :=
    zal _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := qkj ha hb (op==2) ka kb d ne
  have hf := qi5 (faith _ ha) (faith _ hb) op
  have deq:decide (child.length=cap)=(child.length==cap) := by
    by_cases he:child.length=cap <;> simp [he]
  change covered (decide (child.length=cap)) (w5 r s) child=BitVec.allOnes 768 at sep
  rw [deq] at sep
  change zy d (w5 r s z.1) ||| covered d (w5 r s) (rest.map Prod.fst)=_ at sep
  change z.2=w5 r s z.1 at hf
  rw [← hf,← g,rz,BitVec.or_comm] at sep
  have be:((y5 (qbg (qbx ws) d) (zy d a.2) (zy d b.2) (op==2) ka kb ||| zy d z.2) != BitVec.allOnes 768)=false := by simp [sep]
  change (if (_ != _) then true else if !zz z.1||ws.any (fun v => v.1==z.1) then true else _)=true at test
  rw [be,pp,fr] at test
  have val := qdu op a b
  change z.1=_ at val
  have nd' := ndc
  change (z.1 :: rest.map Prod.fst).Nodup at nd'
  change j3 mode T k t (z.1 :: rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact qfp pv lv nd' test k t hk h
def wg (mode:Nat) (ctx:j8) (a b:qw) (d:Bool) :=
  let op := if d then 1 else 0
  let z := qr op a b
  let attempt := vg mode ctx op a b z
  attempt false false&&attempt true false&&attempt false true&&attempt true true
def qhn (mode:Nat) (ctx:j8) (a:qw) (bs:List qw) :=
  let z := qr 2 a a
  vg mode ctx 2 a a z false false&&vg mode ctx 2 a a z true true &&
    bs.all (fun b => wg mode ctx a b false&&wg mode ctx a b true)
def y2 (mode:Nat) (ctx:j8) : List qw -> Bool
  | [] => true
  | a :: bs => qhn mode ctx a bs&&y2 mode ctx bs
lemma qyo {mode ctx ws} (h:y2 mode ctx ws=true) {a:qw} (ha:a ∈ ws) (keep:Bool) :
    vg mode ctx 2 a a (qr 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [y2,Bool.and_eq_true,qhn] at h
    rcases List.mem_cons.mp ha with rfl | hm
    . cases keep
      . exact h.1.1.1
      . exact h.1.1.2
    . exact ih h.2 hm
lemma qvj {mode ctx ws} (h:y2 mode ctx ws=true) {a b:qw} (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:a ≠ b) (d:Bool) : wg mode ctx a b d=true \/ wg mode ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [y2,Bool.and_eq_true,qhn,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    . have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    . rcases List.mem_cons.mp hb with rfl | hbTail
      . right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      . exact ih h.2 haTail hbTail
lemma qpo {mode ctx a b d} (h:wg mode ctx a b d=true) (ka kb:Bool) :
    vg mode ctx (if d then 1 else 0) a b (qr (if d then 1 else 0) a b) ka kb=true := by
  simp only [wg,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
lemma qin {v:List Sig} {w:Sig} (a:Sig) (k:Bool) :
    w ∈ vi k a v ↔ (w=a /\ k=true) \/ w ∈ v := by cases k <;> simp [vi]
lemma qir {v:List qw} (nd:v.Nodup) (a w:qw) (k:Bool) :
    w ∈ wx v a k ↔ w ∈ v /\ (w ≠ a \/ k=true) := by
  cases k <;> simp [wx,nd.mem_erase_iff,and_comm]
lemma qb3 {ws:List qw} (nd:(ws.map Prod.fst).Nodup) {a b:qw}
    (ha:a ∈ ws) (hb:b ∈ ws) (eq:a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    . rfl
    . exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    . exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    . exact ih ht haTail hbTail
lemma qiu {ws:List qw} (nd:(ws.map Prod.fst).Nodup) {a b:qw}
    (ha:a ∈ ws) (hb:b ∈ ws) (un ka kb:Bool) (v:Sig) :
    v ∈ (jk un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst /\ (v ≠ a.1 \/ ka=true) /\ (un=true \/ v ≠ b.1 \/ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (qbz ws a ka)
  cases un <;> simp only [jk,Bool.false_eq_true,ite_false,ite_true,qdr,List.mem_map,
    qir wn,qir dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (qb3 nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (qb3 nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (qb3 nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
lemma qpn {ws:List qw} (nd:(ws.map Prod.fst).Nodup) {a:qw} (ha:a ∈ ws)
    (keep:Bool) :
    (qbp ws 2 a a keep keep).toFinset=(qac (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [qbp,qac,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    qiu nd ha ha,qin,nd.mem_erase_iff,qr,jy,qm4,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  by_cases e:v=a.1 <;> cases keep <;> simp_all
lemma qn7 {ws:List qw} (nd:(ws.map Prod.fst).Nodup) {a b:qw}
    (ha:a ∈ ws) (hb:b ∈ ws) (ne:a.1 ≠ b.1) (d ka kb:Bool) :
    (qbp ws (if d then 1 else 0) a b ka kb).toFinset =
      (wk (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv := List.mem_map_of_mem (f := Prod.fst) hb
  cases d <;> simp only [qbp,wk,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    qiu nd ha hb,qin,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,qr,jy,qtb,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va:v=a.1 <;> by_cases vb:v=b.1 <;> cases ka <;> cases kb <;> simp_all
lemma qkq (v:List Sig) (nd:v.Nodup) (a b:Sig) (d ka kb:Bool) :
    (wk v a b d ka kb).toFinset=(wk v b a d kb ka).toFinset := by
  ext x
  simp only [wk,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    qin,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,qau d b a]
  tauto
lemma qtx {mode raw T r s ws pools links cap}
    (pairs:qae T r s) (faith:∀ w ∈ ws,z9 r s w)
    (nd:(ws.map Prod.fst).Nodup) (out:T ∉ ws.map Prod.fst)
    (pv:∀ p ∈ pools,wa raw T p)
    (lv:∀ tag xs,xs ∈ links tag -> zg mode T (cap - 1) (List.toFinset xs))
    (checks:y2 mode (cap,ws.length,ws,qbx ws,pools,links) ws=true) :
    zg mode T cap (ws.map Prod.fst).toFinset := by
  by_cases hc:cap=0
  . intro k t hk h
    have ke:k=0 := by omega
    subst k
    rcases qct h with ⟨_,_,he,_⟩ | ⟨_,_,_,_,h1,_⟩ | ⟨_,_,_,_,_,h1,_⟩
    . exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
    . omega
    . omega
  have hc':0 < cap := by omega
  apply qu2 nd out
  . intro v hv keep hallow fresh pro _len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := qpn nd ha keep
    rw [← hf]
    exact qc4 pairs faith nd ha ha (by simp) hc' pv lv hallow pro fresh (qyo checks ha keep)
  . intro a ha b hb d ka kb ne hallow fresh pro _len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab:a ≠ b := fun e => ne (congrArg Prod.fst e)
    have one (a b:qw) (aa:a ∈ ws) (bb:b ∈ ws) (ne':a.1 ≠ b.1) (ka kb:Bool)
        (hal:zq mode d a.1 b.1 ka kb=true)
        (pr:q7 (bin d a.1 b.1)) (fr:bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test:wg mode (cap,ws.length,ws,qbx ws,pools,links) a b d=true) :
        zg mode T (cap - 1) (wk (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [← qn7 nd aa bb ne']
      have eq:(qr (if d then 1 else 0) a b).1=bin d a.1 b.1 := by cases d <;> rfl
      have halm:vd mode (if d then 1 else 0) a.1 b.1 ka kb=true := by
        cases d <;> simpa [vd] using hal
      exact qc4 pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        halm (eq ▸ pr) (eq ▸ fr) (qpo test ka kb)
    rcases qvj checks haW hbW ab d with hh | hh
    . exact one a b haW hbW ne ka kb hallow pro fresh hh
    . rw [qkq _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka ((qmn mode d a.1 b.1 ka kb ne).symm.trans hallow)
        (qau d a.1 b.1 ▸ pro) (qau d a.1 b.1 ▸ fresh) hh
lemma qoe (r s:Row) (h:∀ a ∈ inputs,bit r a=bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj:j < 9
  . let i:Fin 9 := ⟨j,hj⟩
    have hm:inputs.getD i.val zero ∈ inputs := by
      rw [← qt9]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (qb5 i r).symm.trans ((h _ hm).trans (qb5 i s))
  . have le:512 ≤ 2 ^ j := by
      change 2 ^ 9 ≤ 2 ^ j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def qdx (p q:List qcj) := inputs.all (fun a => q1 p (q1 q a)==a)
lemma qf0 {p q} (h:qdx p q=true) (r:Row) :
    z5 q (z5 p r)=r := by
  apply qoe
  intro a ha
  rw [← qbs,← qbs]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def qhw (mode:Nat) (T:Sig) (p:List qcj) :=
  (q1 p T==T)&&qdx p p.reverse&&qdx p.reverse p &&
    (mode==0||q1 p qu==qu)
lemma qf6 {mode T n} {ws:List Sig} (hi:zg mode T n ws.toFinset)
    (p:List qcj) (ok:qhw mode T p=true) :
    zg mode T n (ws.map (q1 p.reverse)).toFinset := by
  simp only [qhw,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  have onto:Function.Surjective (z5 p) := fun r => ⟨z5 p.reverse r,qf0 ok.1.2 r⟩
  have fix0:mode=0 \/ q5 (z5 p) qu=qu := by
    rcases ok.2 with h0 | hx
    . exact Or.inl h0
    . exact Or.inr ((zt p qu).symm.trans hx)
  intro k t hk h
  have run := qnr h (z5 p) onto fix0
  have goal:q5 (z5 p) T=T := (zt p T).symm.trans ok.1.1.1
  have inv (x:Sig) : q5 (z5 p) (q1 p.reverse x)=x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
    rw [jz,qbs,qf0 ok.1.1.2]
  have back:(ws.map (q1 p.reverse)).toFinset.image (q5 (z5 p))=ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    . rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    . intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run
abbrev qs := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat -> Nat)
def q6:qs := (0,0,0,0,0,0,0,fun _ => 0)
def vr (word:Nat -> Nat) (pos len:Nat) :=
  let i := Nat.shiftRight pos 13
  let shift := Nat.land pos 8191
  let lo := Nat.shiftRight (word i) shift
  let msk := Nat.sub (Nat.shiftLeft 1 len) 1
  match Nat.ble (Nat.add shift len) 8192 with
  | true => Nat.land lo msk
  | false => Nat.land (Nat.lor lo (Nat.shiftLeft (word (Nat.add i 1)) (Nat.sub 8192 shift))) msk
def qf (nb slots sw vw iw pw:Nat) (data:Nat -> Nat) (h:Nat) : Option (Nat × Nat) :=
  let a := Nat.mod h nb
  let sh := vr data (Nat.mul a sw) sw
  let row := Nat.mod (Nat.add (Nat.div h nb) sh) slots
  let word := vr data (Nat.add (Nat.mul nb sw) (Nat.mul row vw)) vw
  match Nat.beq (Nat.shiftRight word (Nat.add iw pw)) (Nat.mod (Nat.div h (Nat.mul nb slots)) 16) with
  | true => some (Nat.land word (Nat.sub (Nat.shiftLeft 1 iw) 1),
                  Nat.land (Nat.shiftRight word iw) (Nat.sub (Nat.shiftLeft 1 pw) 1))
  | false => none
abbrev qx := Nat × Nat × Nat × (Nat -> zi × zi) × List vp ×
  List (List Nat) × (Nat -> qs) × (Nat -> Nat -> Option (Nat × Nat))
def jh (g:qx) : Nat := g.1
def qoh (g:qx) : Nat := g.2.1
def vj (g:qx) : Nat := g.2.2.1
def w1 (g:qx) : Nat -> zi × zi := g.2.2.2.1
def qhv (g:qx) : List vp := g.2.2.2.2.1
def qdq (g:qx) : List (List Nat) := g.2.2.2.2.2.1
def jn (g:qx) : Nat -> qs := g.2.2.2.2.2.2.1
def qdp (g:qx) : Nat -> Nat -> Option (Nat × Nat) := g.2.2.2.2.2.2.2
def j7 (g:qx) :=
  qd6 (jh g) (fun j => (w1 g j).1) (fun j => (w1 g j).2)
lemma qix (g:qx) : ∀ a ∈ j7 g,
    z9 (y8 fun j => (w1 g j).1) (y8 fun j => (w1 g j).2) a :=
  qnn (jh g) (fun j => (w1 g j).1) (fun j => (w1 g j).2)
def zn (g:qx) := vu (jh g)
def yr (m:Nat) (v:Nat -> zi) := qh1 m v
lemma qyc (m:Nat) (v:Nat -> zi) (i:Fin 768) :
    bit (y8 v i) (vu m)=(yr m v).getLsbD i.val :=
  qn6 m v i
lemma qf3 {m:Nat} {p q:Nat -> zi}
    (hp:yr m p=BitVec.allOnes 768) (hq:yr m q=0) :
    qae (vu m) (y8 p) (y8 q) := by
  intro i
  simp only [qyc,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def vh {α : Type} (bits:Nat) : List α -> List α
  | [] => []
  | w :: ws => if bits &&& 1==1 then w :: vh (bits >>> 1) ws else vh (bits >>> 1) ws
lemma qi1 {α : Type} (bits:Nat) (ws:List α) : (vh bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold vh
    split
    . exact List.Sublist.cons₂ _ (ih _)
    . exact List.Sublist.cons _ (ih _)
def yj (g:qx) (k i:Nat) : Nat × List qw × List qw :=
  let raw := j7 g
  let (_,depth,_,_,_,_,_,data) := jn g k
  let len := 10*depth
  let width := len+raw.length+depth
  let recp := vr data (i*width) width
  let ops := recp &&& ((1 <<< len) - 1)
  let bank := qa0 depth ops raw
  (ops,bank,vh (recp >>> len) bank)
def qmu (x pos width:Nat) := (x >>> pos) &&& ((1 <<< width) - 1)
def jm (bank:List qw) (ops paid:Nat) : Nat -> List ya
  | 0 => []
  | n+1 =>
    let more := jm bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1==0 then more else
      (qmu ops 8 2,(bank.getD (ops &&& 15) qb).1,
        (bank.getD (qmu ops 4 4) qb).1) :: more
def y0 (g:qx) (ops d:Nat) (bank:List qw) (idx paid:Nat) : Option z8 :=
  ((qhv g)[idx]?).bind fun ci =>
    let kind := ci.2.2.2.2.2
    let raw := qai (jh g) kind
    let base := jm bank ops paid d
    let steps :=
      if (jh g).testBit 10&&paid.testBit d then
        if kind==0 then (2,qu,qu) :: base
        else if kind==1 then (2,qn,qn) :: base
        else base
      else base
    qbb raw steps (wf ci.1 ci.2.1) ci.2.2.2.2.1
lemma qgg (g:qx)
    (cols:∀ ci ∈ qhv g,qfs (qai (jh g) ci.2.2.2.2.2) (zn g) (wf ci.1 ci.2.1) ci.2.2.2.2.1)
    {i ops depth bank paid c} (h:y0 g ops depth bank i paid=some c) :
    wa (qo (jh g)) (zn g) c := by
  unfold y0 at h
  cases e:(qhv g)[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    exact qiy (qew (cols ci (List.mem_of_getElem? e)) h)
def qen (data:Nat -> Nat) (w v:Nat) : Nat -> Nat -> List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := vr data pos (w+v)
    (x &&& ((1 <<< w) - 1),x >>> w) :: qen data w v n (pos+w+v)
def wh (g:qx) (k i:Nat) := (yj g k i).2.2.map Prod.fst
def yf (g:qx) (k:Nat) (pair:Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (jn g k).1 then none else
    ((qdq g)[pair.2]?).map fun perm => (wh g k pair.1).map (q1 (perm.map ji).reverse)
lemma qf8 (g:qx) (k:Nat)
    (names:∀ x ∈ qdq g,qhw (vj g) (zn g) (x.map ji)=true)
    (earlier:∀ i < (jn g k).1,zg (vj g) (zn g) k (wh g k i).toFinset)
    {pair out} (h:yf g k pair=some out) :
    zg (vj g) (zn g) k out.toFinset := by
  unfold yf at h
  split at h
  . contradiction
  next valid =>
    cases e:(qdq g)[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact qf6 (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))
def ym (g:qx) (k i:Nat) :=
  let raw := j7 g
  let (num,depth,cw,_iw,_pw,offw,lw,data) := jn g k
  let (ops,bank,ws) := yj g k i
  let values := ws.map Prod.fst
  let start := num*(10*depth+raw.length+depth)
  let pos := start+num*offw+vr data (start+i*offw) offw
  let nr := vr data pos 5
  let st := pos+5+lw
  let paidw := if (jh g).testBit 10 then depth+1 else depth
  let rules := (qen data cw paidw nr st).filterMap (fun (a,b) => y0 g ops depth bank a b)
  let ls := fun tag => ((qdp g k tag).bind (yf g (k - 1))).toList
  decide values.Nodup&&!(values.contains (zn g)) &&
    (if k=0 then true else y2 (vj g) (k,ws.length,ws,qbx ws,rules,ls) ws)
lemma qa3 (g:qx) (k i:Nat)
    (samples:qae (zn g) (y8 fun j => (w1 g j).1) (y8 fun j => (w1 g j).2))
    (cols:∀ ci ∈ qhv g,qfs (qai (jh g) ci.2.2.2.2.2) (zn g) (wf ci.1 ci.2.1) ci.2.2.2.2.1)
    (names:∀ x ∈ qdq g,qhw (vj g) (zn g) (x.map ji)=true)
    (prior:k > 0 -> ∀ j < (jn g (k - 1)).1,zg (vj g) (zn g) (k - 1) (wh g (k - 1) j).toFinset)
    (checked:ym g k i=true) : zg (vj g) (zn g) k (wh g k i).toFinset := by
  simp only [ym,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT:zn g ∉ wh g k i := by simpa [wh] using checked.1.2
  by_cases h0:k=0
  . subst k
    intro t u lo h
    have ht:t=0 := by omega
    subst t
    rcases qct h with ⟨_,_,he,_⟩ | ⟨_,_,_,_,h1,_⟩ | ⟨_,_,_,_,_,h1,_⟩
    . exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
    . omega
    . omega
  apply qtx (raw := qo (jh g)) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  . intro v hv
    apply qge _ _ _ _ _ (qix g) v
    exact (qi1 _ _).subset hv
  . intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact qgg g cols h
  . intro tag xs hx
    have e:((qdp g k tag).bind (yf g (k - 1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact qf8 g _ names (prior (by omega)) h
def qc (g:qx) (k start:Nat) : Nat -> Bool
  | 0 => true
  | n+1 => ym g k (start+n)&&qc g k start n
lemma qpm {g k start n} (h:qc g k start n=true) (j:Nat) (lo:start ≤ j) (hi:j < start+n) :
    ym g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [qc,Bool.and_eq_true] at h
    by_cases eq:j=start+n
    . simpa [eq] using h.1
    . exact ih h.2 (by omega)
lemma qri {g k start a b} (h:qc g k start a=true)
    (h':qc g k (start+a) b=true) : qc g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [qc,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,qc,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def qp (g:qx) (top:Nat) :=
  ∀ k ≤ top,qc g k 0 (jn g k).1=true
def qi (g:qx) (prior:Nat -> Nat) :=
  (yr (jh g) (fun j => (w1 g j).1)==BitVec.allOnes 768) &&
  (yr (jh g) (fun j => (w1 g j).2)==0) &&
  (qhv g).all (fun c => qbm (jh g) c prior) &&
  (qdq g).all (fun p => qhw (vj g) (zn g) (p.map ji))
lemma qux (g:qx) (top:Nat) (prior:Nat -> Nat)
    (lower:∀ q,qy (qo q) (qa q) (prior q))
    (geometry:qi g prior=true) (rows:qp g top) :
    ∀ k ≤ top,∀ i < (jn g k).1,zg (vj g) (zn g) k (wh g k i).toFinset := by
  simp only [qi,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply qa3 g 0 i (qf3 geometry.1.1.1 geometry.1.1.2)
      (fun x hx => qde _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact qpm (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply qa3 g _ i (qf3 geometry.1.1.1 geometry.1.1.2)
      (fun x hx => qde _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact qpm (rows _ hk) i (by omega) (by omega)
def qbd (g:qx) (k i:Nat) (ws:List Sig) :=
  decide (i < (jn g k).1)&&ye (wh g k i) ws
lemma qaw {g top prior k i ws} (low:∀ q,qy (qo q) (qa q) (prior q))
    (geom:qi g prior=true) (blocks:qp g top) (le:k ≤ top)
    (idx:qbd g k i ws=true) : zg (vj g) (zn g) k ws.toFinset := by
  simp only [qbd,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [← qcc idx.2]
  exact qux g top prior low geom blocks _ le i idx.1
lemma zh {g prior i hints} (hm0:vj g=0)
    (low:∀ q,qy (qo q) (qa q) (prior q))
    (geom:qi g prior=true) (blocks:qp g (qoh g))
    (idx:qbd g (qoh g) i (qo (jh g))=true) (hp:zz (zn g)=true)
    (ess:zo (zn g) (qo (jh g)) (z2 (jh g) hints)=true)
    (all:(z2 (jh g) hints).map Prod.fst=qo (jh g)) :
    qy (qo (jh g)) (zn g) (qoh g+1) := by
  have noR := qaw low geom blocks (Nat.le_refl _) idx
  rw [hm0] at noR
  apply qbu (zx _ hp) _ noR
  intro a ha
  apply vn ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
lemma qkm {m cap prior ci hints} (hm10:m.testBit 10=false)
    (low:∀ q,qy (qo q) (qa q) (prior q))
    (ok:qbm m ci prior=true)
    (hp:zz (qa m)=true)
    (ess:zo (qa m) (qo m) (z2 m hints)=true)
    (all:(z2 m hints).map Prod.fst=qo m)
    (nd:(qo m).Nodup)
    (cut:qd1 (wf ci.1 ci.2.1) ci.2.2.2.2.1 cap 0 (qo m) (qo m)=true) :
    qy (qo m) (qa m) (cap+1) := by
  have hraw:qai m ci.2.2.2.2.2=qo m := by simp [qai,hm10]
  have hsl := qde ci prior low ok
  rw [hraw] at hsl
  apply qbu (zx _ hp) _ (qdk hsl [] rfl nd cut)
  intro a ha
  apply vn ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
lemma yx {m L:Nat}
    (hm10:(1024 ||| m).testBit 10=true)
    (hvars:qo (1024 ||| m)=qo m ++ [qn])
    (hdrop0:∀ a ∈ qo (1024 ||| m),a ≠ qu -> a ∈ j4 m)
    (hgoal:qa (1024 ||| m)=qa m)
    (hp:zz (qa m)=true) (hp1:zz (qa (512 ||| m))=true)
    (hflip:vt [jx] (j4 m) (qa m) (qo (512 ||| m)) (qa (512 ||| m))=true)
    (hL0:qy (qo m) (qa m) L)
    (hL1:qy (qo (512 ||| m)) (qa (512 ||| m)) L)
    (xs:List (Sig × Row × Row))
    (ess:zo (qa m) (qo (1024 ||| m)) xs=true)
    (hxs:∀ a ∈ qo m,a ≠ qu -> a ∈ xs.map Prod.fst)
    (noRun:wo (qa m) (L - 1) (qo (1024 ||| m)).toFinset) :
    qy (qo (1024 ||| m)) (qa (1024 ||| m)) L := by
  rw [hgoal]
  have pT := zx _ hp
  have hflipL:qy (j4 m) (qa m) L :=
    qe5 hflip pT (zx _ hp1) hL1
  intro p bank hr ha
  obtain ⟨k,t,S,hk,run,sub⟩ := qay pT hr ha
  by_cases hnx:qn ∈ S
  . by_cases hx0:qu ∈ S
    . have hS:(qo (1024 ||| m)).toFinset=S := by
        ext a
        rw [List.mem_toFinset]
        refine ⟨fun hm => ?_,sub a⟩
        rw [hvars,List.mem_append,List.mem_singleton] at hm
        rcases hm with hm | rfl
        . by_cases ha0:a=qu
          . exact ha0 ▸ hx0
          . have ha_xs:a ∈ (xs.map Prod.fst).toFinset := List.mem_toFinset.mpr (hxs a hm ha0)
            obtain ⟨r1,r2,hd,iso⟩ := vn ess a ha_xs
            exact vz run _ a sub r1 r2 hd iso
        . exact hnx
      by_contra! small
      exact noRun k t (by omega) (hS.symm ▸ run)
    . have subF:∀ a ∈ S,a ∈ j4 m := fun a ha => hdrop0 a (sub a ha) (fun e => hx0 (e ▸ ha))
      exact le_trans (wb pT run subF hflipL) hk
  . have sub0:∀ a ∈ S,a ∈ qo m := by
      intro a ha
      have hm := sub a ha
      rw [hvars,List.mem_append,List.mem_singleton] at hm
      exact hm.resolve_right (fun e => hnx (e ▸ ha))
    exact le_trans (wb pT run sub0 hL0) hk
lemma yv {g m prior i xs} (hm:jh g=1024 ||| m) (hmode:vj g=0)
    (hvars:qo (1024 ||| m)=qo m ++ [qn])
    (hdrop0:∀ a ∈ qo (1024 ||| m),a ≠ qu -> a ∈ j4 m)
    (hgoal:qa (1024 ||| m)=qa m)
    (hp:zz (qa m)=true) (hp1:zz (qa (512 ||| m))=true)
    (hflip:vt [jx] (j4 m) (qa m) (qo (512 ||| m)) (qa (512 ||| m))=true)
    (low:∀ q,qy (qo q) (qa q) (prior q))
    (hL0:qoh g+1 ≤ prior m) (hL1:qoh g+1 ≤ prior (512 ||| m))
    (geom:qi g prior=true) (blocks:qp g (qoh g))
    (idx:qbd g (qoh g) i (qo (jh g))=true)
    (ess:zo (qa m) (qo (1024 ||| m)) xs=true)
    (hxs:(qo m).all (fun a => a==qu||(xs.map Prod.fst).contains a)=true) :
    qy (qo (1024 ||| m)) (qa (1024 ||| m)) (qoh g+1) := by
  have noR := qaw low geom blocks (Nat.le_refl _) idx
  unfold zn vu at noR
  rw [hmode,hm,hgoal] at noR
  refine yx (by simp [Nat.testBit_or];left;decide) hvars hdrop0 hgoal hp hp1 hflip
    (fun p b hr ha => le_trans hL0 (low m p b hr ha))
    (fun p b hr ha => le_trans hL1 (low (512 ||| m) p b hr ha))
    xs ess (fun a ha hne => ?_) (by simpa using noR)
  have hall := List.all_eq_true.mp hxs a ha
  simp only [Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at hall
  exact hall.resolve_left hne
lemma v1 {m cap prior ci xs} (hk2:ci.2.2.2.2.2=2)
    (hvars:qo (1024 ||| m)=qo m ++ [qn])
    (hdrop0:∀ a ∈ qo (1024 ||| m),a ≠ qu -> a ∈ j4 m)
    (hgoal:qa (1024 ||| m)=qa m)
    (hp:zz (qa m)=true) (hp1:zz (qa (512 ||| m))=true)
    (hflip:vt [jx] (j4 m) (qa m) (qo (512 ||| m)) (qa (512 ||| m))=true)
    (low:∀ q,qy (qo q) (qa q) (prior q))
    (hL0:cap+1 ≤ prior m) (hL1:cap+1 ≤ prior (512 ||| m))
    (ok:qbm (1024 ||| m) ci prior=true)
    (nd:(qo (1024 ||| m)).Nodup)
    (cut:qd1 (wf ci.1 ci.2.1) ci.2.2.2.2.1 cap 0 (qo (1024 ||| m)) (qo (1024 ||| m))=true)
    (ess:zo (qa m) (qo (1024 ||| m)) xs=true)
    (hxs:(qo m).all (fun a => a==qu||(xs.map Prod.fst).contains a)=true) :
    qy (qo (1024 ||| m)) (qa (1024 ||| m)) (cap+1) := by
  have h10:(1024 ||| m).testBit 10=true := by simp [Nat.testBit_or];left;decide
  have hraw:qai (1024 ||| m) ci.2.2.2.2.2=qo (1024 ||| m) := by simp [qai,hk2,h10]
  have hsl := qde ci prior low ok
  rw [hraw] at hsl
  have noR := qdk hsl [] rfl nd cut
  unfold vu at noR
  rw [hgoal] at noR
  refine yx h10 hvars hdrop0 hgoal hp hp1 hflip
    (fun p b hr ha => le_trans hL0 (low m p b hr ha))
    (fun p b hr ha => le_trans hL1 (low (512 ||| m) p b hr ha))
    xs ess (fun a ha hne => ?_) (by simpa using noR)
  have hall := List.all_eq_true.mp hxs a ha
  simp only [Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at hall
  exact hall.resolve_left hne
lemma qnq {m m0 L:Nat}
    (hvars:qo (1024 ||| m)=qo m ++ [qn])
    (hdrop0:∀ a ∈ qo (1024 ||| m),a ≠ qu -> a ∈ j4 m)
    (hgoal:qa (1024 ||| m)=qa m)
    (hp:zz (qa m)=true) (hp1:zz (qa (512 ||| m))=true)
    (hp0:zz (qa m0)=true)
    (hflip:vt [jx] (j4 m) (qa m) (qo (512 ||| m)) (qa (512 ||| m))=true)
    (hmap0:vt (wu 1 0) (qo (1024 ||| m)) (qa m) (qo m0) (qa m0)=true)
    (hc0:q1 (wu 1 0) qu=zero) (hcn0:q1 (wu 1 0) qn=one)
    (hne0:qu ≠ qn)
    (hL0:qy (qo m) (qa m) L)
    (hL1:qy (qo (512 ||| m)) (qa (512 ||| m)) L)
    (hL2:qy (qo m0) (qa m0) (L - 2)) (hge2:2 ≤ L) :
    qy (qo (1024 ||| m)) (qa (1024 ||| m)) L := by
  classical
  rw [hgoal]
  have pT := zx _ hp
  have hflipL:qy (j4 m) (qa m) L :=
    qe5 hflip pT (zx _ hp1) hL1
  intro p bank hr ha
  obtain ⟨k,t,S,hk,run,sub⟩ := qay pT hr ha
  by_cases hnx:qn ∈ S
  . by_cases hx0:qu ∈ S
    . obtain ⟨eq0,supp0⟩ := qbc hmap0
      let singles:Finset Sig := {qu,qn}
      have hcard:singles.card=2 := Finset.card_pair hne0
      have subS:singles ⊆ S := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | hb
        . exact hx0
        . exact (Finset.mem_singleton.mp hb) ▸ hnx
      let front := singles.toList ++ (S \ singles).toList
      have nd:front.Nodup := by
        simp only [front,List.nodup_append]
        refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
        intro a ha b hb he
        subst b
        exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
      have fe:front.toFinset=S := by ext a;simp [front,Finset.union_sdiff_of_subset subS]
      have run' := qcm run front nd fe
      have gc:qj (z5 (wu 1 0)) (qm (qa m))=qm (qa m0) :=
        (ju _ _).symm.trans (congrArg qm eq0)
      have supp:qar ((qo m0).map qm) ((front.map qm).map (qj (z5 (wu 1 0)))) := by
        intro v hv
        obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
        obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
        rw [← ju]
        exact supp0 a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
      have bound := w7 (z5 (wu 1 0)) run' (gc ▸ yt (zx _ hp0))
        qad supp (L := L - 2) (gc ▸ hL2)
      have massLo:2 ≤ mass ((front.map qm).map (qj (z5 (wu 1 0)))) := by
        simp only [front,List.map_append,qft]
        let xs := (singles.toList.map qm).map (qj (z5 (wu 1 0)))
        have only:∀ v ∈ xs,zw v := by
          intro v hv
          obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
          obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
          rw [← ju,← zt]
          rcases Finset.mem_insert.mp (Finset.mem_toList.mp hmem) with rfl | hb
          . rw [hc0];exact ⟨false,funext j5⟩
          . rw [Finset.mem_singleton.mp hb,hcn0];exact ⟨true,funext yg⟩
        have sz := qc0 xs only
        simp only [xs,List.length_map,Finset.length_toList,hcard] at sz
        change 2 ≤ mass xs+_
        rw [sz]
        omega
      omega
    . have subF:∀ a ∈ S,a ∈ j4 m := fun a ha => hdrop0 a (sub a ha) (fun e => hx0 (e ▸ ha))
      exact le_trans (wb pT run subF hflipL) hk
  . have sub0:∀ a ∈ S,a ∈ qo m := by
      intro a ha
      have hm := sub a ha
      rw [hvars,List.mem_append,List.mem_singleton] at hm
      exact hm.resolve_right (fun e => hnx (e ▸ ha))
    exact le_trans (wb pT run sub0 hL0) hk
def zv (entries:List (Nat × Nat)) := ∀ e ∈ entries,qy (qo e.1) (qa e.1) e.2
def qh (old:List (Nat × Nat)) (L:Nat) (relabels:List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
lemma qd {old L m relabels} (previous:zv old)
    (main:qy (qo m) (qa m) L)
    (ok:relabels.all (fun v => qe2 v.1 m v.2)=true) :
    zv (qh old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  . obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact qtu (List.all_eq_true.mp ok _ hv) main
  . exact previous e h
lemma qmw:zv [] := by simp [zv]
def jj (v:Nat) (upper:Nat) := 2 ^ 769*upper+v
def qq {α : Type} (f : α -> zi) : List α -> Nat
  | [] => 0
  | x :: xs => jj (f x).toNat (qq f xs)
def ve:Nat -> Nat
  | 0 => 0
  | n+1 => jj 1 (ve n)
lemma qe8 (x:zi) : x.toNat < 2 ^ 769 :=
  lt_trans x.isLt (by decide +kernel)
lemma qwg (a b:zi) (u v:Nat) :
    jj a.toNat u &&& jj b.toNat v=jj (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [jj,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (qe8 _)]
  by_cases h:i < 769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
lemma qzg (a b:zi) (u v:Nat) :
    jj a.toNat u ||| jj b.toNat v=jj (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [jj,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (qe8 _)]
  by_cases h:i < 769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
lemma qwf (a b:zi) (u v:Nat) :
    jj a.toNat u ^^^ jj b.toNat v=jj (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [jj,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (qe8 _)]
  by_cases h:i < 769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
lemma qe7 {α} (f g : α -> zi) (xs) :
    qq f xs &&& qq g xs=qq (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [qq]
  | cons a xs ih => simp only [qq,qwg,ih]
lemma qh2 {α} (f g : α -> zi) (xs) :
    qq f xs ||| qq g xs=qq (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [qq]
  | cons a xs ih => simp only [qq,qzg,ih]
lemma qe6 {α} (f g : α -> zi) (xs) :
    qq f xs ^^^ qq g xs=qq (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [qq]
  | cons a xs ih => simp only [qq,qwf,ih]
lemma qyd {α} (a:zi) (xs:List α) :
    ve xs.length*a.toNat=qq (fun _ => a) xs := by
  induction xs with
  | nil => simp [ve,qq]
  | cons v xs ih => simp only [List.length_cons,ve,qq,jj,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]
def qbq (r packed:Nat) := ((packed+r) >>> 768) &&& r
lemma qyv (n i:Nat) (hi:i < n) : (ve n).testBit (769*i)=true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [ve,jj,Nat.testBit_two_pow_mul_add _ (by decide +kernel:1 < 2 ^ 769)]
    cases i with
    | zero => simp
    | succ i =>
      have di:769*(i+1) - 769=769*i := by omega
      have ge:¬769*(i+1) < 769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
lemma qzx (a:zi) : (a.toNat+1).testBit 768=(a==BitVec.allOnes 768) := by
  by_cases h:a=BitVec.allOnes 768
  . subst a
    decide +kernel
  . have lim := a.isLt
    have ne:a.toNat ≠ 2 ^ 768 - 1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt:a.toNat+1 < 2 ^ 768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
lemma zbm {α} (f : α -> zi) (xs:List α) (i:Nat) (hi:i < xs.length) :
    (qbq (ve xs.length) (qq f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [qbq,Nat.testBit_and,Nat.testBit_shiftRight,qyv _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [qq,List.length_cons,ve,jj]
    have sum (u v x:Nat) : 2 ^ 769*u+x+(2 ^ 769*v+1)=2 ^ 769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1 < 2 ^ 769 from by have := (f a).isLt;omega)]
    have hi':i < xs.length+1 := hi
    cases i with
    | zero => simpa using qzx (f a)
    | succ i =>
      have ge:¬769*(i+1)+768 < 769 := by omega
      have di:769*(i+1)+768 - 769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)
abbrev y1 := Nat × Nat
abbrev qbt := Nat × Nat × Nat
def z6 {α} (s : α -> qhr) (xs:List α) : y1 :=
  (qq (fun x => (s x).1) xs,qq (fun x => (s x).2) xs)
def vc {α} (c : α -> Cov) (xs:List α) : qbt :=
  (qq (fun x => (c x).1) xs,qq (fun x => (c x).2.1) xs,
   qq (fun x => (c x).2.2) xs)
def q2 (d:Bool) (a:y1) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
lemma qoi (a b:zi) : a ^^^ (a &&& b)=a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
lemma qbi {α} (s : α -> qhr) (xs:List α) (d:Bool) :
    q2 d (z6 s xs)=qq (fun x => zy d (s x)) xs := by
  cases d <;> simp only [q2,z6,zy,Bool.false_eq_true,ite_false,ite_true,qe7,qe6,qoi]
def wz (full:Nat) (op:Nat) (a b:y1) : y1 :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
lemma zbg (a:zi) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
lemma qwh {α} (a b : α -> qw) (xs:List α) (op:Nat) :
    wz (ve xs.length*(BitVec.allOnes 768).toNat) op
      (z6 (fun x => (a x).2) xs) (z6 (fun x => (b x).2) xs) =
    z6 (fun x => (qr op (a x) (b x)).2) xs := by
  by_cases un:op=2
  . simp only [wz,un,ite_true,z6,qyd,qe6,zbg,qr,jy,qm4]
  . by_cases one:op=1 <;> simp [wz,un,one,z6,qh2,qe7,qr,jy,qtb]
def qds (c:qbt) (a b:Nat) (un ka kb:Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
lemma qkh {α} (c : α -> Cov) (a b : α -> zi) (xs:List α) (un ka kb:Bool) :
    qds (vc c xs) (qq a xs) (qq b xs) un ka kb =
    qq (fun x => y5 (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [qds,vc,qe7,qh2,qe6,qoi,y5,y3,qc5,
      Bool.false_eq_true,ite_false,ite_true]
def zd (c:j8) (i:Nat) := c.2.2.1.getD i qb
def qd3 (mode:Nat) (c:j8) (i j op:Nat) (ka kb:Bool) :=
  let a := zd c i
  let b := zd c j
  vg mode c op a b (qr op a b) ka kb
def qfg (c:j8) (d un ka kb:Bool) (op i j:Nat) :=
  let a := zd c i
  let b := zd c j
  y5 (qbg c.2.2.2.1 d) (zy d a.2) (zy d b.2) un ka kb |||
    zy d (qr op a b).2
def qhl (p:z8) (m:Sig) :=
  m==zero||m==qv p||((zp p).map (q0 (qv p))).any (fun v => v==m)
lemma yu (p:z8) (x:Sig) :
    qz (qv p) (zp p) x=qhl p (q0 (qv p) x) := rfl
def zf (p:qw -> Bool) (a:qw) (keep:Bool) :=
  if keep then 0 else (p a).toNat
lemma qmt (p:qw -> Bool) (ws:List qw) (a:qw) (keep:Bool) :
    ws.countP p ≤ (wx ws a keep).countP p+zf p a keep := by
  cases keep
  . simp only [wx,Bool.false_eq_true,ite_false,zf,List.countP_erase]
    split
    next h => simp [h.2];omega
    next => omega
  . simp [wx,zf]
lemma qxl (p:qw -> Bool) (ws:List qw) (a b:qw) (un ka kb:Bool) :
    ws.countP p - zf p a ka - zf p b (un||kb) ≤
    (jk un ka kb a b ws).countP p := by
  have h1 := qmt p ws a ka
  have h2 := qmt p (wx ws a ka) b kb
  cases un <;> simp only [jk,qdr,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [zf];omega
abbrev qmy := z8 × Nat × Bool
def w3 (ws:List qw) (p:z8) : qmy :=
  (p,ws.countP (fun w => qg (qv p) w.1),
     ws.all (fun w => qz (qv p) (zp p) w.1))
def qco (s:qmy) (k:Nat) (a b:qw) (op:Nat) (ka kb:Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w:qw => qg (qv p) w.1
  let z := ql (zl op a b)
  let zm := q0 (qv p) z
  let zc := qg (qv p) z
  let cm := s.2.1 - zf const a ka - zf const b (un||kb)+zc.toNat
  let free := zc||zm==q0 (qv p) a.1||zm==q0 (qv p) b.1
  decide (k+j6 p+(!free).toNat < jw p+cm)
lemma qkp {p k ws a b op ka kb} (ha:a ∈ ws) (hb:b ∈ ws)
    (h:qco (w3 ws p) k a b op ka kb=true) :
    jf p k ((jk (op==2) ka kb a b ws).map Prod.fst) (zl op a b)=true := by
  let z := ql (zl op a b)
  let const := fun w:qw => qg (qv p) w.1
  let free := qg (qv p) z||q0 (qv p) z==q0 (qv p) a.1 ||
      q0 (qv p) z==q0 (qv p) b.1
  let rest := jk (op==2) ka kb a b ws
  have ck := qxl const ws a b (op==2) ka kb
  change ws.countP const - zf const a ka - zf const b ((op==2)||kb) ≤ rest.countP const at ck
  by_cases all:ws.all (fun w => qz (qv p) (zp p) w.1)=true
  . have hav := List.all_eq_true.mp all
    have ready:free=true -> qz (qv p) (zp p) z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc | za) | zb
      . simp only [qz,qg,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      . rw [yu,za,← yu]
        exact hav _ ha
      . rw [yu,zb,← yu]
        exact hav _ hb
    have extra:(!qz (qv p) (zp p) z).toNat ≤ (!free).toNat := by
      cases hf:free <;> cases he:qz (qv p) (zp p) z <;> simp_all
    have hs:(rest.map Prod.fst).all (qz (qv p) (zp p))=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((qpj ws a b (op==2) ka kb).subset hw)
    have opOK:yk (qv p) (zp p) (zl op a b)=true := by
      simp [yk,zl,hav _ ha,hav _ hb]
    simp only [qco,w3,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+j6 p+(!free).toNat < jw p+(ws.countP const - zf const a ka -
        zf const b ((op==2)||kb)+(qg (qv p) z).toNat) at h
    dsimp only [rest] at hs
    simp only [jf,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+j6 p+(!qz (qv p) (zp p) z).toNat <
      jw p+(rest.countP const+if qg (qv p) z then 1 else 0)
    cases hc:qg (qv p) z <;> simp [hc] at h ⊢ <;> omega
  . simp [qco,w3,all] at h
lemma qwj {g k start n} (h:∀ (i:Nat),start ≤ i -> i < start+n -> ym g k i=true) :
    qc g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [qc,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def jd:List Nat -> Nat -> Nat
  | [],_ => 0
  | x :: _,0 => x
  | _ :: xs,n+1 => jd xs n
def wt (x:Nat) : List Nat -> Bool
  | [] => false
  | y :: ys => match Nat.beq x y with | true => true | false => wt x ys
def qcl:List Nat -> Bool
  | [] => true
  | x :: xs => match wt x xs with | true => false | false => qcl xs
def v0 (x:Nat) : List Nat -> Option (List Nat)
  | [] => none
  | y :: ys =>
    match Nat.beq x y with
    | true => some ys
    | false =>
      match v0 x ys with
      | none => none
      | some r => some (y :: r)
def qas:List Nat -> List Nat -> Bool
  | [],[] => true
  | [],_ :: _ => false
  | x :: xs,ys =>
    match v0 x ys with
    | none => false
    | some ys' => qas xs ys'
def v6 {α : Type} (p : α -> Bool) : List α -> Bool
  | [] => true
  | x :: xs => match p x with | true => v6 p xs | false => false
def y9 {α : Type} (p : α -> Bool) : List α -> Bool
  | [] => false
  | x :: xs => match p x with | true => true | false => y9 p xs
lemma qns {α : Type} (p : α -> Bool) (xs:List α) :
    v6 p xs=true ↔ ∀ x ∈ xs,p x=true := by
  induction xs with
  | nil => simp [v6]
  | cons x xs ih =>
    unfold v6
    cases h:p x <;> simp [h,ih]
lemma qer {α : Type} (p : α -> Bool) (xs:List α) :
    y9 p xs=true ↔ ∃ x ∈ xs,p x=true := by
  induction xs with
  | nil => simp [y9]
  | cons x xs ih =>
    unfold y9
    cases h:p x <;> simp [h,ih]
lemma qba (x:Nat) (xs:List Nat) : wt x xs=true ↔ x ∈ xs := by
  induction xs with
  | nil => simp [wt]
  | cons y ys ih =>
    unfold wt
    cases h:Nat.beq x y with
    | true =>
      have eq:x=y := Nat.eq_of_beq_eq_true h
      simp [eq]
    | false =>
      have ne:x ≠ y := fun e => by rw [e,Nat.beq_refl] at h;contradiction
      simp [ne,ih]
lemma qi4 {ws:List Sig} (h:qcl (ws.map BitVec.toNat)=true) : ws.Nodup := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.map_cons,qcl] at h
    cases hm:wt w.toNat (ws.map BitVec.toNat) with
    | true => rw [hm] at h;contradiction
    | false =>
      rw [hm] at h
      refine List.nodup_cons.mpr ⟨?_,ih h⟩
      intro hw
      have hmem:wt w.toNat (ws.map BitVec.toNat)=true :=
        (qba w.toNat (ws.map BitVec.toNat)).mpr (List.mem_map_of_mem (f := BitVec.toNat) hw)
      rw [hm] at hmem;contradiction
lemma qev {x:Nat} {ys ys':List Nat} (h:v0 x ys=some ys') :
    ys.Perm (x :: ys') := by
  induction ys generalizing ys' with
  | nil => simp [v0] at h
  | cons y ys ih =>
    unfold v0 at h
    cases hb:Nat.beq x y with
    | true =>
      have eq:x=y := Nat.eq_of_beq_eq_true hb
      rw [hb] at h;injection h with h;subst ys';rw [eq]
    | false =>
      rw [hb] at h
      cases he:v0 x ys with
      | none => rw [he] at h;contradiction
      | some r =>
        rw [he] at h;injection h with h;subst ys'
        exact (List.Perm.cons y (ih he)).trans (List.Perm.swap x y r)
lemma qkl {xs ys:List Nat} (h:qas xs ys=true) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact List.Perm.nil
    | cons _ _ => simp [qas] at h
  | cons x xs ih =>
    unfold qas at h
    cases he:v0 x ys with
    | none => rw [he] at h;contradiction
    | some ys' =>
      rw [he] at h
      exact (List.Perm.cons x (ih h)).trans (qev he).symm
lemma qdz {xs ys:List Sig}
    (h:qas (xs.map BitVec.toNat) (ys.map BitVec.toNat)=true) : ye xs ys=true := by
  have hp := qkl h
  have mem_iff:∀ a:Sig,a ∈ xs ↔ a ∈ ys := fun a => by
    constructor <;> intro ha
    . obtain ⟨b,hb,eq⟩ := List.mem_map.mp (hp.mem_iff.mp (List.mem_map_of_mem ha))
      exact (BitVec.eq_of_toNat_eq eq) ▸ hb
    . obtain ⟨b,hb,eq⟩ := List.mem_map.mp (hp.mem_iff.mpr (List.mem_map_of_mem ha))
      exact (BitVec.eq_of_toNat_eq eq) ▸ hb
  simp only [ye,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
  exact ⟨fun a ha => (mem_iff a).mp ha,fun a ha => (mem_iff a).mpr ha⟩
lemma yb:(zero:Sig).toNat=0 := BitVec.toNat_zero
lemma qcz (ws:List Sig) (i:Nat) :
    jd (ws.map BitVec.toNat) i=(ws.getD i zero).toNat := by
  induction ws generalizing i with
  | nil => simp [jd,yb]
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ n => exact ih n
lemma ww (ws:List qw) (i:Nat) :
    jd (ws.map (fun w => w.1.toNat)) i=(ws.getD i qb).1.toNat := by
  induction ws generalizing i with
  | nil => simp [jd,qb,yb]
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ n => exact ih n
lemma vv {α : Type} (f : α -> Nat) (ws:List α) (i:Nat) (hi:i < ws.length) :
    jd (ws.map f) i=f ws[i] := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ n => exact ih n (by simpa using hi)
def qdy:Nat := (BitVec.allOnes 512).toNat
def x0N:Nat := qu.toNat
def qs8:Nat := qn.toNat
def qd2:List Nat := inputs.map BitVec.toNat
def qat (op a b:Nat) : Nat :=
  match Nat.beq op 2 with
  | true => Nat.xor qdy a
  | false => match Nat.beq op 1 with | true => Nat.lor a b | false => Nat.land a b
lemma qah (op:Nat) (a b:Sig) :
    qat op a.toNat b.toNat=(ql (op,a,b)).toNat := by
  unfold qat ql
  by_cases h2:op=2
  . subst op
    change (BitVec.allOnes 512).toNat ^^^ a.toNat=(neg a).toNat
    rw [← BitVec.toNat_xor,BitVec.allOnes_xor];rfl
  . have hq:Nat.beq op 2=false := beq_eq_false_iff_ne.mpr h2
    simp only [hq,h2,ite_false]
    by_cases h1:op=1
    . subst op;rfl
    . have hq1:Nat.beq op 1=false := beq_eq_false_iff_ne.mpr h1
      simp only [hq1,bin,show (op==1)=false from hq1,Bool.false_eq_true,ite_false]
      rfl
def qcx (mode a:Nat) : Bool :=
  match Nat.beq mode 2 with
  | true => !(Nat.beq a x0N)
  | false => match Nat.beq mode 3 with
    | true => match Nat.beq a x0N with | true => false | false => !(Nat.beq a qs8)
    | false => true
def qfi (mode:Nat) (d:Bool) (a b:Nat) (ka kb:Bool) : Bool :=
  match Nat.beq mode 2 with
  | true => match d with
    | false => true
    | true => match Nat.beq a x0N with | true => false | false => !(Nat.beq b x0N)
  | false => match Nat.beq mode 3 with
    | true =>
      match Nat.beq a x0N with
      | true => match d with | false => false | true => match ka with | true => false | false => !(Nat.beq b qs8)
      | false => match Nat.beq b x0N with
        | true => match d with | false => false | true => match kb with | true => false | false => !(Nat.beq a qs8)
        | false => match Nat.beq a qs8 with
          | true => match d with | true => false | false => !ka
          | false => match Nat.beq b qs8 with
            | true => match d with | true => false | false => !kb
            | false => true
    | false => true
def qb1 (mode op a b:Nat) (ka kb:Bool) : Bool :=
  match Nat.beq op 2 with
  | true => qcx mode a
  | false => qfi mode (Nat.beq op 1) a b ka kb
lemma z7 (a b:Sig) : Nat.beq a.toNat b.toNat=(a==b) := by
  by_cases h:a=b
  . subst b;simp [Nat.beq_refl]
  . have hne:a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    rw [beq_eq_false_iff_ne.mpr h]
    exact beq_eq_false_iff_ne.mpr hne
lemma qkd (mode:Nat) (a:Sig) :
    qcx mode a.toNat=jc mode a := by
  unfold qcx jc x0N qs8
  rw [z7,z7]
  cases h2:Nat.beq mode 2
  . cases h3:Nat.beq mode 3
    . simp [show (mode==2)=false from h2,show (mode==3)=false from h3]
    . cases hx:(a==qu) <;> cases hn:(a==qn) <;>
        simp [show (mode==2)=false from h2,show (mode==3)=true from h3,hx,hn,bne]
  . cases hx:(a==qu) <;> simp [show (mode==2)=true from h2,hx,bne]
lemma qod (mode:Nat) (d:Bool) (a b:Sig) (ka kb:Bool) :
    qfi mode d a.toNat b.toNat ka kb=zq mode d a b ka kb := by
  unfold qfi zq x0N qs8
  rw [z7,z7,z7,z7]
  cases h2:Nat.beq mode 2
  . cases h3:Nat.beq mode 3
    . simp only [show (mode==2)=false from h2,show (mode==3)=false from h3,
        Bool.false_eq_true,ite_false]
    . simp only [show (mode==2)=false from h2,show (mode==3)=true from h3,
        Bool.false_eq_true,ite_false,ite_true,bne]
      cases ax:(a==qu) <;> cases bx:(b==qu) <;>
        cases an:(a==qn) <;> cases bn:(b==qn) <;>
        cases d <;> cases ka <;> cases kb <;> rfl
  . simp only [show (mode==2)=true from h2,ite_true,bne]
    cases d <;> cases ax:(a==qu) <;> cases bx:(b==qu) <;> rfl
lemma qmm (mode op:Nat) (a b:Sig) (ka kb:Bool) :
    qb1 mode op a.toNat b.toNat ka kb=vd mode op a b ka kb := by
  unfold qb1 vd
  cases h2:Nat.beq op 2
  . simp only [show (op==2)=false from h2,Bool.false_eq_true,ite_false]
    exact qod mode (Nat.beq op 1) a b ka kb
  . simp only [show (op==2)=true from h2,ite_true]
    exact qkd mode a
def yl (d:Nat) (mpool:List Nat) (m:Nat) : Bool :=
  match Nat.beq m 0 with
  | true => true
  | false => match Nat.beq m d with | true => true | false => wt m mpool
def yd (d m:Nat) : Bool :=
  match Nat.beq m 0 with | true => true | false => Nat.beq m d
lemma y7 (d a:Sig) :
    yd d.toNat (Nat.land a.toNat d.toNat)=qg d a := by
  have he:Nat.land a.toNat d.toNat=(q0 d a).toNat := rfl
  rw [he]
  unfold yd qg
  have h0:Nat.beq (q0 d a).toNat 0=(q0 d a==zero) := by
    rw [← yb];exact z7 (q0 d a) zero
  have hd:Nat.beq (q0 d a).toNat d.toNat=(q0 d a==d) := z7 (q0 d a) d
  rw [h0,hd]
  cases (q0 d a==zero) <;> rfl
lemma wq (d:Sig) (pool:List Sig) (a:Sig) :
    yl d.toNat (pool.map (fun w => Nat.land w.toNat d.toNat)) (Nat.land a.toNat d.toNat) =
    qz d pool a := by
  have he:Nat.land a.toNat d.toNat=(q0 d a).toNat := rfl
  have hmp:pool.map (fun w => Nat.land w.toNat d.toNat)=(pool.map (q0 d)).map BitVec.toNat := by
    rw [List.map_map];rfl
  rw [he,hmp]
  unfold yl qz
  dsimp only
  have h0:Nat.beq (q0 d a).toNat 0=(q0 d a==zero) := by
    rw [← yb];exact z7 (q0 d a) zero
  have hd:Nat.beq (q0 d a).toNat d.toNat=(q0 d a==d) := z7 (q0 d a) d
  have hmem:wt (q0 d a).toNat ((pool.map (q0 d)).map BitVec.toNat) =
      (pool.map (q0 d)).any (fun v => v==q0 d a) := by
    apply Bool.eq_iff_iff.mpr
    rw [qba,List.mem_map,List.any_eq_true]
    constructor
    . rintro ⟨v,hv,eq⟩;exact ⟨v,hv,beq_iff_eq.mpr (BitVec.eq_of_toNat_eq eq)⟩
    . rintro ⟨v,hv,eq⟩;exact ⟨v,hv,congrArg BitVec.toNat (beq_iff_eq.mp eq)⟩
  rw [h0,hd,hmem]
  cases (q0 d a==zero) <;> cases (q0 d a==d) <;> rfl
def qc9 (d:Nat) (mpool:List Nat) : List ya -> Option (List Nat)
  | [] => some mpool
  | c :: cs =>
    match yl d mpool (Nat.land c.2.1.toNat d) with
    | false => none
    | true =>
      let ok2 := match Nat.beq c.1 2 with | true => true | false => yl d mpool (Nat.land c.2.2.toNat d)
      match ok2 with
      | false => none
      | true => qc9 d (Nat.land (qat c.1 c.2.1.toNat c.2.2.toNat) d :: mpool) cs
lemma qnp (d:Sig) (pool:List Sig) (cs:List ya) :
    qc9 d.toNat (pool.map (fun w => Nat.land w.toNat d.toNat)) cs =
    (w0 d pool cs).map (fun p => p.map (fun w => Nat.land w.toNat d.toNat)) := by
  induction cs generalizing pool with
  | nil => rfl
  | cons c cs ih =>
    unfold qc9 w0 yk
    rw [wq,wq]
    cases ha:qz d pool c.2.1 with
    | false => simp [ha]
    | true =>
      cases h2:Nat.beq c.1 2 with
      | true =>
        simp only [ha,show (c.1==2)=true from h2,Bool.true_or,Bool.and_true,ite_true]
        rw [qah]
        exact ih (ql c :: pool)
      | false =>
        cases hb:qz d pool c.2.2 with
        | false => simp [ha,show (c.1==2)=false from h2,hb]
        | true =>
          simp only [ha,show (c.1==2)=false from h2,hb,Bool.false_or,Bool.and_true,ite_true]
          rw [qah]
          exact ih (ql c :: pool)
abbrev qhx := Nat × Nat × Nat × List Nat
def yi (p:z8) : qhx :=
  let d := (qv p).toNat
  (d,jw p,j6 p,(zp p).map (fun w => Nat.land w.toNat d))
def qnh (m kind:Nat) : List Nat := (qai m kind).map BitVec.toNat
def qb0 (g:qx) (ops depth:Nat) (bank:List qw) (idx paid:Nat) : Option qhx :=
  match (qhv g)[idx]? with
  | none => none
  | some ci =>
    let kind := ci.2.2.2.2.2
    let base := jm bank ops paid depth
    let steps :=
      match (jh g).testBit 10 with
      | false => base
      | true => match paid.testBit depth with
        | false => base
        | true => match Nat.beq kind 0 with
          | true => (2,qu,qu) :: base
          | false => match Nat.beq kind 1 with
            | true => (2,qn,qn) :: base
            | false => base
    let d := (wf ci.1 ci.2.1).toNat
    let mp0 := (qnh (jh g) kind).map (fun w => Nat.land w d)
    match qc9 d mp0 steps with
    | none => none
    | some mp => some (d,ci.2.2.2.2.1,steps.length,mp)
lemma qkr (g:qx) (ops depth:Nat) (bank:List qw) (idx paid:Nat) :
    qb0 g ops depth bank idx paid=(y0 g ops depth bank idx paid).map yi := by
  unfold qb0 y0 qbb
  cases (qhv g)[idx]? with
  | none => rfl
  | some ci =>
    dsimp only [Option.bind_some]
    have hsteps :
      (match (jh g).testBit 10 with
        | false => jm bank ops paid depth
        | true => match paid.testBit depth with
          | false => jm bank ops paid depth
          | true => match Nat.beq ci.2.2.2.2.2 0 with
            | true => (2,qu,qu) :: jm bank ops paid depth
            | false => match Nat.beq ci.2.2.2.2.2 1 with
              | true => (2,qn,qn) :: jm bank ops paid depth
              | false => jm bank ops paid depth) =
      (if (jh g).testBit 10&&paid.testBit depth then
        if ci.2.2.2.2.2==0 then (2,qu,qu) :: jm bank ops paid depth
        else if ci.2.2.2.2.2==1 then (2,qn,qn) :: jm bank ops paid depth
        else jm bank ops paid depth
      else jm bank ops paid depth) := by
      change _=(if (jh g).testBit 10&&paid.testBit depth then
        if Nat.beq ci.2.2.2.2.2 0 then _ else if Nat.beq ci.2.2.2.2.2 1 then _ else _ else _)
      cases (jh g).testBit 10 <;> cases paid.testBit depth <;>
        cases Nat.beq ci.2.2.2.2.2 0 <;> cases Nat.beq ci.2.2.2.2.2 1 <;> rfl
    rw [hsteps]
    have hmp0:(qnh (jh g) ci.2.2.2.2.2).map (fun w => Nat.land w (wf ci.1 ci.2.1).toNat) =
        (qai (jh g) ci.2.2.2.2.2).map (fun w => Nat.land w.toNat (wf ci.1 ci.2.1).toNat) := by
      simp [qnh,List.map_map,Function.comp_def]
    rw [hmp0,qnp]
    cases w0 (wf ci.1 ci.2.1) (qai (jh g) ci.2.2.2.2.2) _ <;> rfl
abbrev qm5 := Nat × Nat × Nat × Nat × Nat × List Nat
def vy (d:Nat) (mp:List Nat) : List Nat -> Option (Nat × Nat × List Nat)
  | [] => some (0,0,[])
  | w :: ws =>
    let m := Nat.land w d
    match yl d mp m with
    | false => none
    | true =>
      match vy d mp ws with
      | none => none
      | some (cc,cm,mws) =>
        match yd d m with
        | true => some (Nat.add cc 1,Nat.lor 1 (Nat.shiftLeft cm 1),m :: mws)
        | false => some (cc,Nat.shiftLeft cm 1,m :: mws)
def qav (wsN:List Nat) (p:qhx) : Option qm5 :=
  let (d,lb,paid,mp) := p
  match vy d mp wsN with
  | none => none
  | some (cc,cm,mws) => some (d,lb,paid,cc,cm,mws)
lemma qdn (cm i:Nat) (b:Bool) :
    Nat.land (Nat.shiftRight (if b then Nat.lor 1 (Nat.shiftLeft cm 1) else Nat.shiftLeft cm 1) i) 1 =
    match i with | 0 => b.toNat | n+1 => Nat.land (Nat.shiftRight cm n) 1 := by
  have hlt1 (k:Nat) : Nat.testBit 1 (k+1)=false :=
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) 2))
  have hltm (x k:Nat) : (x &&& 1).testBit (k+1)=false := by
    rw [Nat.testBit_and,hlt1 k,Bool.and_false]
  cases i with
  | zero =>
    cases b <;> apply Nat.eq_of_testBit_eq <;> intro k <;> cases k with
    | zero =>
      change (((if _ then 1 ||| cm <<< 1 else cm <<< 1) >>> 0) &&& 1).testBit 0=_
      simp [Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftLeft]
    | succ k =>
      change (((if _ then 1 ||| cm <<< 1 else cm <<< 1) >>> 0) &&& 1).testBit (k+1)=_
      rw [hltm];simp [hlt1]
  | succ n =>
    cases b <;> apply Nat.eq_of_testBit_eq <;> intro k <;> cases k with
    | zero =>
      change (((if _ then 1 ||| cm <<< 1 else cm <<< 1) >>> (n+1)) &&& 1).testBit 0=((cm >>> n) &&& 1).testBit 0
      simp [Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_or,Nat.testBit_shiftLeft,hlt1]
    | succ k =>
      change (((if _ then 1 ||| cm <<< 1 else cm <<< 1) >>> (n+1)) &&& 1).testBit (k+1) =
        ((cm >>> n) &&& 1).testBit (k+1)
      rw [hltm,hltm]
lemma qeu (p:z8) (ws:List qw) {cc cm mws}
    (h:vy (qv p).toNat ((zp p).map (fun w => Nat.land w.toNat (qv p).toNat))
      (ws.map (fun w => w.1.toNat))=some (cc,cm,mws)) :
    ws.all (fun w => qz (qv p) (zp p) w.1)=true ∧
    cc=ws.countP (fun w => qg (qv p) w.1) ∧
    mws=ws.map (fun w => Nat.land w.1.toNat (qv p).toNat) ∧
    ∀ i < ws.length,Nat.land (Nat.shiftRight cm i) 1 =
      (qg (qv p) (ws.getD i qb).1).toNat := by
  induction ws generalizing cc cm mws with
  | nil =>
    simp [vy] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact ⟨rfl,rfl,rfl,fun _ hi => by simp at hi⟩
  | cons w ws ih =>
    simp only [List.map_cons,vy,wq] at h
    cases ha:qz (qv p) (zp p) w.1 with
    | false => rw [ha] at h;contradiction
    | true =>
      rw [ha] at h
      cases hrec:vy (qv p).toNat ((zp p).map (fun w => Nat.land w.toNat (qv p).toNat))
          (ws.map (fun w => w.1.toNat)) with
      | none => rw [hrec] at h;contradiction
      | some res =>
        obtain ⟨cc',cm',mws'⟩ := res
        rw [hrec] at h
        obtain ⟨hall,hcc,hmws,hcm⟩ := ih hrec
        rw [y7] at h
        cases hc:qg (qv p) w.1 with
        | true =>
          rw [hc] at h;injection h with h;obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj h
          refine ⟨by simp [ha,hall],by simp [List.countP_cons,hc,hcc],by simp [hmws],?_⟩
          intro i hi
          have hb := qdn cm' i true
          simp only [ite_true] at hb
          rw [hb]
          cases i with
          | zero => simp [hc]
          | succ n => exact hcm n (by simpa using hi)
        | false =>
          rw [hc] at h;injection h with h;obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj h
          refine ⟨by simp [ha,hall],by simp [List.countP_cons,hc,hcc],by simp [hmws],?_⟩
          intro i hi
          have hb := qdn cm' i false
          simp only [Bool.false_eq_true,ite_false] at hb
          rw [hb]
          cases i with
          | zero => simp [hc]
          | succ n => exact hcm n (by simpa using hi)
def qby (q:qm5) (k1 i j op:Nat) (ka kb:Bool) : Bool :=
  let (d,lb,paid,ccnt,cmask,mws) := q
  let un := Nat.beq op 2
  let lossA := match ka with | true => 0 | false => Nat.land (Nat.shiftRight cmask i) 1
  let lossB := match un with
    | true => 0
    | false => match kb with | true => 0 | false => Nat.land (Nat.shiftRight cmask j) 1
  let need := Nat.add k1 paid
  let base := Nat.add lb (Nat.sub (Nat.sub ccnt lossA) lossB)
  match Nat.blt (Nat.add need 1) base with
  | true => true
  | false =>
    match Nat.blt need (Nat.add base 1) with
    | false => false
    | true =>
      let ma := jd mws i
      let mb := jd mws j
      let zm := match un with
        | true => Nat.xor d ma
        | false => match Nat.beq op 1 with | true => Nat.lor ma mb | false => Nat.land ma mb
      let zc := yd d zm
      match Nat.beq need base with
      | true => zc
      | false =>
        match zc with
        | true => true
        | false => match Nat.beq zm ma with | true => true | false => Nat.beq zm mb
lemma qca (d:Sig) (op:Nat) (a b:Sig) :
    (q0 d (ql (op,a,b))).toNat =
    match Nat.beq op 2 with
    | true => Nat.xor d.toNat (Nat.land a.toNat d.toNat)
    | false => match Nat.beq op 1 with
      | true => Nat.lor (Nat.land a.toNat d.toNat) (Nat.land b.toNat d.toNat)
      | false => Nat.land (Nat.land a.toNat d.toNat) (Nat.land b.toNat d.toNat) := by
  have land_eq (x y:Sig) : Nat.land x.toNat y.toNat=(x &&& y).toNat := rfl
  have lor_eq (x y:Sig) : Nat.lor x.toNat y.toNat=(x ||| y).toNat := rfl
  have xor_eq (x y:Sig) : Nat.xor x.toNat y.toNat=(x ^^^ y).toNat := rfl
  by_cases h2:op=2
  . subst op
    simp only [Nat.beq_refl,ql,ite_true,q0,neg,land_eq,xor_eq]
    congr 1
    apply BitVec.eq_of_getLsbD_eq;intro idx hidx
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,hidx,decide_true,Bool.true_and]
    cases a.getLsbD idx <;> cases d.getLsbD idx <;> rfl
  . have hq2:Nat.beq op 2=false := beq_eq_false_iff_ne.mpr h2
    simp only [hq2,ql,h2,ite_false,q0,land_eq]
    by_cases h1:op=1
    . subst op
      simp only [Nat.beq_refl,bin,show (1==1)=true from rfl,ite_true,lor_eq]
      congr 1
      apply BitVec.eq_of_getLsbD_eq;intro idx hidx
      simp only [BitVec.getLsbD_and,BitVec.getLsbD_or]
      cases a.getLsbD idx <;> cases b.getLsbD idx <;> cases d.getLsbD idx <;> rfl
    . have hq1:Nat.beq op 1=false := beq_eq_false_iff_ne.mpr h1
      simp only [hq1,bin,show (op==1)=false from hq1,Bool.false_eq_true,ite_false,land_eq]
      congr 1
      apply BitVec.eq_of_getLsbD_eq;intro idx hidx
      simp only [BitVec.getLsbD_and]
      cases a.getLsbD idx <;> cases b.getLsbD idx <;> cases d.getLsbD idx <;> rfl
lemma qfm {p:z8} {ws:List qw} {q:qm5} {k1 i j op:Nat} {ka kb:Bool}
    (hi:i < ws.length) (hj:j < ws.length)
    (hs:qav (ws.map (fun w => w.1.toNat)) (yi p)=some q)
    (hf:qby q k1 i j op ka kb=true) :
    qco (w3 ws p) k1 (ws.getD i qb) (ws.getD j qb) op ka kb=true := by
  unfold qav yi at hs
  dsimp only at hs
  cases haux:vy (qv p).toNat ((zp p).map (fun w => Nat.land w.toNat (qv p).toNat))
      (ws.map (fun w => w.1.toNat)) with
  | none => rw [haux] at hs;contradiction
  | some res =>
    obtain ⟨cc,cm,mws⟩ := res
    rw [haux] at hs;injection hs with hs;subst q
    obtain ⟨hall,hcc,hmws,hcm⟩ := qeu p ws haux
    let a := ws.getD i qb
    let b := ws.getD j qb
    have hma:jd mws i=(q0 (qv p) a.1).toNat := by
      rw [hmws,vv _ ws i hi]
      simp [a,List.getD_eq_getElem?_getD,hi,q0]
    have hmb:jd mws j=(q0 (qv p) b.1).toNat := by
      rw [hmws,vv _ ws j hj]
      simp [b,List.getD_eq_getElem?_getD,hj,q0]
    have hla:∀ b:Bool,(match b with | true => 0 | false => Nat.land (Nat.shiftRight cm i) 1) =
        zf (fun w:qw => qg (qv p) w.1) a b := fun b => by
      cases b with
      | true => rfl
      | false => exact hcm i hi
    have hlb:∀ (op':Nat) (b':Bool),(match Nat.beq op' 2 with
        | true => 0
        | false => match b' with | true => 0 | false => Nat.land (Nat.shiftRight cm j) 1) =
        zf (fun w:qw => qg (qv p) w.1) b ((op'==2)||b') := fun op' b' => by
      cases h2:Nat.beq op' 2 with
      | true => simp [show (op'==2)=true from h2,zf]
      | false =>
        cases b' with
        | true => simp [show (op'==2)=false from h2,zf]
        | false =>
          simp only [show (op'==2)=false from h2,Bool.false_or,zf,Bool.false_eq_true,ite_false]
          exact hcm j hj
    unfold qco w3
    simp only [hall,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq,← hcc]
    change k1+j6 p+(!(qg (qv p) (ql (zl op a b)) ||
        q0 (qv p) (ql (zl op a b))==q0 (qv p) a.1 ||
        q0 (qv p) (ql (zl op a b))==q0 (qv p) b.1)).toNat <
      jw p+(cc - zf (fun w:qw => qg (qv p) w.1) a ka -
        zf (fun w:qw => qg (qv p) w.1) b ((op==2)||kb) +
        (qg (qv p) (ql (zl op a b))).toNat)
    unfold qby at hf
    dsimp only at hf
    rw [hla ka,hlb op kb] at hf
    set L1 := zf (fun w:qw => qg (qv p) w.1) a ka
    set L2 := zf (fun w:qw => qg (qv p) w.1) b ((op==2)||kb)
    set z := ql (zl op a b)
    set zc := qg (qv p) z
    set free := zc||q0 (qv p) z==q0 (qv p) a.1 ||
        q0 (qv p) z==q0 (qv p) b.1
    cases hfast:Nat.blt (Nat.add (Nat.add k1 (j6 p)) 1) (Nat.add (jw p) (Nat.sub (Nat.sub cc L1) L2)) with
    | true =>
      have hlt:k1+j6 p+1 < jw p+(cc - L1 - L2) := Nat.blt_eq.mp hfast
      cases free <;> cases zc <;> simp <;> omega
    | false =>
      rw [hfast] at hf
      cases hok:Nat.blt (Nat.add k1 (j6 p)) (Nat.add (Nat.add (jw p) (Nat.sub (Nat.sub cc L1) L2)) 1) with
      | false => rw [hok] at hf;contradiction
      | true =>
        rw [hok] at hf
        have hlt2:k1+j6 p < jw p+(cc - L1 - L2)+1 := Nat.blt_eq.mp hok
        have hge:¬(k1+j6 p+1 < jw p+(cc - L1 - L2)) := fun h => by
          have h':(Nat.add (Nat.add k1 (j6 p)) 1).blt (Nat.add (jw p) (Nat.sub (Nat.sub cc L1) L2))=true :=
            Nat.blt_eq.mpr h
          rw [hfast] at h';contradiction
        rw [hma,hmb] at hf
        have hzm:(match Nat.beq op 2 with
            | true => Nat.xor (qv p).toNat (q0 (qv p) a.1).toNat
            | false => match Nat.beq op 1 with
              | true => Nat.lor (q0 (qv p) a.1).toNat (q0 (qv p) b.1).toNat
              | false => Nat.land (q0 (qv p) a.1).toNat (q0 (qv p) b.1).toNat) =
            (q0 (qv p) z).toNat := (qca (qv p) op a.1 b.1).symm
        rw [hzm] at hf
        have hzc:yd (qv p).toNat (q0 (qv p) z).toNat=zc := y7 (qv p) z
        rw [hzc] at hf
        cases heq:Nat.beq (Nat.add k1 (j6 p)) (Nat.add (jw p) (Nat.sub (Nat.sub cc L1) L2)) with
        | true =>
          rw [heq] at hf
          have hzt:zc=true := hf
          have hft:free=true := by simp [free,hzt]
          simp [hzt,hft];omega
        | false =>
          rw [heq] at hf
          have hne:k1+j6 p ≠ jw p+(cc - L1 - L2) := fun e => by
            have:Nat.beq (Nat.add k1 (j6 p)) (Nat.add (jw p) (Nat.sub (Nat.sub cc L1) L2))=true :=
              beq_iff_eq.mpr e
            rw [heq] at this;contradiction
          have hft:free=true := by
            simp only [free,Bool.or_eq_true]
            cases hzt:zc with
            | true => left;left;exact rfl
            | false =>
              rw [hzt] at hf
              cases ha1:Nat.beq (q0 (qv p) z).toNat (q0 (qv p) a.1).toNat with
              | true =>
                left;right;rw [← z7];exact ha1
              | false =>
                rw [ha1] at hf
                right;rw [← z7];exact hf
          cases zc <;> simp [hft] <;> omega
def wp (d:Nat) (mp:List Nat) : List Nat -> Option Nat
  | [] => some 0
  | w :: ws =>
    let m := Nat.land w d
    match yl d mp m with
    | false => none
    | true =>
      match wp d mp ws with
      | none => none
      | some c => some (match yd d m with | true => Nat.add c 1 | false => c)
lemma qfo (p:z8) (rest:List Sig) {c:Nat}
    (h:wp (qv p).toNat ((zp p).map (fun w => Nat.land w.toNat (qv p).toNat))
      (rest.map BitVec.toNat)=some c) :
    rest.all (qz (qv p) (zp p))=true ∧
    c=rest.countP (qg (qv p)) := by
  induction rest generalizing c with
  | nil => simp [wp] at h;subst c;exact ⟨rfl,rfl⟩
  | cons w ws ih =>
    simp only [List.map_cons,wp,wq] at h
    cases ha:qz (qv p) (zp p) w with
    | false => rw [ha] at h;contradiction
    | true =>
      rw [ha] at h
      cases hrec:wp (qv p).toNat ((zp p).map (fun w => Nat.land w.toNat (qv p).toNat))
          (ws.map BitVec.toNat) with
      | none => rw [hrec] at h;contradiction
      | some c' =>
        rw [hrec,y7] at h
        injection h with h;subst c
        obtain ⟨hall,hcnt⟩ := ih hrec
        cases hc:qg (qv p) w <;> simp [ha,hall,List.countP_cons,hc,hcnt]
def qaj (p:qhx) (k:Nat) (rest:List Nat) (op a b z:Nat) : Bool :=
  let (d,lb,paid,mp) := p
  let zm := Nat.land z d
  let extra := match yl d mp zm with | true => false | false => true
  match wp d mp rest with
  | none => false
  | some cc0 =>
    let cc := match yd d zm with | true => Nat.add cc0 1 | false => cc0
    match Nat.blt (Nat.add (Nat.add k paid) (match extra with | true => 1 | false => 0)) (Nat.add lb cc) with
    | false => false
    | true => match extra with
      | false => true
      | true =>
        match yl d mp (Nat.land a d) with
        | false => false
        | true => match Nat.beq op 2 with | true => true | false => yl d mp (Nat.land b d)
lemma qcg {p:z8} {k op:Nat} {rest:List Sig} {a b:Sig}
    (h:qaj (yi p) k (rest.map BitVec.toNat) op a.toNat b.toNat (ql (op,a,b)).toNat=true) :
    jf p k rest (op,a,b)=true := by
  unfold qaj yi at h
  dsimp only at h
  rw [wq] at h
  cases hcnt:wp (qv p).toNat ((zp p).map (fun w => Nat.land w.toNat (qv p).toNat))
      (rest.map BitVec.toNat) with
  | none => rw [hcnt] at h;contradiction
  | some cc0 =>
    rw [hcnt,y7] at h
    obtain ⟨hall,hcc0⟩ := qfo p rest hcnt
    have hcntz:(ql (op,a,b) :: rest).countP (qg (qv p)) =
        (match qg (qv p) (ql (op,a,b)) with | true => Nat.add cc0 1 | false => cc0) := by
      rw [List.countP_cons,← hcc0]
      cases qg (qv p) (ql (op,a,b)) <;> rfl
    unfold jf
    dsimp only
    rw [hall,hcntz]
    cases hav:qz (qv p) (zp p) (ql (op,a,b)) with
    | true =>
      simp only [hav,Bool.not_true,Bool.not_false,Bool.toNat_false,Bool.and_true,Bool.true_or] at h ⊢
      cases hlt:Nat.blt (Nat.add (Nat.add k (j6 p)) 0) _ with
      | false => rw [hlt] at h;contradiction
      | true =>
        have hlt':k+j6 p+0 < jw p+(match qg (qv p) (ql (op,a,b)) with | true => Nat.add cc0 1 | false => cc0) :=
          Nat.blt_eq.mp hlt
        exact decide_eq_true hlt'
    | false =>
      simp only [hav,Bool.not_false,Bool.toNat_true,Bool.and_true,Bool.false_or] at h ⊢
      cases hlt:Nat.blt (Nat.add (Nat.add k (j6 p)) 1) _ with
      | false => rw [hlt] at h;contradiction
      | true =>
        rw [hlt,wq,wq] at h
        have hlt':k+j6 p+1 < jw p+(match qg (qv p) (ql (op,a,b)) with | true => Nat.add cc0 1 | false => cc0) :=
          Nat.blt_eq.mp hlt
        refine Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true hlt',?_⟩
        unfold yk
        cases ha:qz (qv p) (zp p) a with
        | false => rw [ha] at h;contradiction
        | true =>
          rw [ha] at h
          cases h2:Nat.beq op 2 with
          | true => simp [ha,show (op==2)=true from h2]
          | false => rw [h2] at h;simp [ha,show (op==2)=false from h2,h]
def wl:Nat -> List Nat -> List Nat
  | _,[] => []
  | 0,_ :: xs => xs
  | n+1,x :: xs => x :: wl n xs
def qcp (un ka kb:Bool) (i j:Nat) (xs:List Nat) : List Nat :=
  match un with
  | true => match ka with | true => xs | false => wl i xs
  | false =>
    let xs1 := match ka with | true => xs | false => wl i xs
    match kb with
    | true => xs1
    | false => wl (match ka with | true => j | false => Nat.sub j 1) xs1
lemma vx {ws:List qw} (hnd:(ws.map Prod.fst).Nodup) {i:Nat} (hi:i < ws.length) :
    wl i (ws.map (fun w => w.1.toNat)) =
    ((ws.erase (ws.getD i qb)).map Prod.fst).map BitVec.toNat := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    obtain ⟨hmem,hnd'⟩ := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      simp [wl,List.erase_cons_head,List.map_map,Function.comp_def]
    | succ n =>
      have hn:n < ws.length := by simpa using hi
      have hget:(w :: ws).getD (n+1) qb=ws.getD n qb := rfl
      have hne:w ≠ ws.getD n qb := by
        intro eq
        have hm:ws.getD n qb ∈ ws := by simp [List.getD_eq_getElem?_getD,hn]
        exact hmem (eq ▸ List.mem_map_of_mem hm)
      have hbeq:(w==ws.getD n qb)=false := beq_eq_false_iff_ne.mpr hne
      simp only [List.map_cons,wl,hget,List.erase_cons,hbeq,Bool.false_eq_true,ite_false]
      exact congrArg (w.1.toNat :: ·) (ih hnd' hn)
lemma qkn {ws:List qw} (hnd:(ws.map Prod.fst).Nodup) {i j:Nat}
    (hij:i < j) (hj:j < ws.length) :
    (ws.erase (ws.getD i qb)).getD (j - 1) qb=ws.getD j qb := by
  induction ws generalizing i j with
  | nil => simp at hj
  | cons w ws ih =>
    obtain ⟨hmem,hnd'⟩ := List.nodup_cons.mp hnd
    cases j with
    | zero => omega
    | succ j' =>
      cases i with
      | zero =>
        simp [List.erase_cons_head]
      | succ i' =>
        have hi':i' < ws.length := by simp at hj;omega
        have hj':j' < ws.length := by simpa using hj
        have hne:w ≠ ws.getD i' qb := by
          intro eq
          have hm:ws.getD i' qb ∈ ws := by simp [List.getD_eq_getElem?_getD,hi']
          exact hmem (eq ▸ List.mem_map_of_mem hm)
        have hbeq:(w==ws.getD i' qb)=false := beq_eq_false_iff_ne.mpr hne
        have hsub:j'+1 - 1=(j' - 1)+1 := by omega
        change ((w :: ws).erase (ws.getD i' qb)).getD (j'+1 - 1) qb=ws.getD j' qb
        rw [List.erase_cons,hbeq,hsub]
        exact ih hnd' (by omega) hj'
lemma qqx {ws:List qw} (hnd:(ws.map Prod.fst).Nodup) {i j:Nat}
    (un ka kb:Bool) (hi:i < ws.length) (hj:j < ws.length) (hij:un=false -> i < j) :
    qcp un ka kb i j (ws.map (fun w => w.1.toNat)) =
    ((jk un ka kb (ws.getD i qb) (ws.getD j qb) ws).map Prod.fst).map BitVec.toNat := by
  cases un with
  | true =>
    cases ka with
    | true => simp [qcp,jk,wx,List.map_map,Function.comp_def]
    | false => exact vx hnd hi
  | false =>
    have hlt := hij rfl
    cases ka with
    | true =>
      cases kb with
      | true => simp [qcp,jk,qdr,wx,List.map_map,Function.comp_def]
      | false => exact vx hnd hj
    | false =>
      cases kb with
      | true => exact vx hnd hi
      | false =>
        simp only [qcp,jk,qdr,wx,Bool.false_eq_true,ite_false]
        rw [vx hnd hi]
        have hnd1:((ws.erase (ws.getD i qb)).map Prod.fst).Nodup :=
          hnd.sublist (List.erase_sublist.map _)
        have hlen1:j - 1 < (ws.erase (ws.getD i qb)).length := by
          have hm:ws.getD i qb ∈ ws := by simp [List.getD_eq_getElem?_getD,hi]
          rw [List.length_erase_of_mem hm];omega
        have hmap:((ws.erase (ws.getD i qb)).map Prod.fst).map BitVec.toNat =
            (ws.erase (ws.getD i qb)).map (fun w => w.1.toNat) := by
          simp [List.map_map,Function.comp_def]
        change wl (j - 1) _=_
        rw [hmap,vx hnd1 hlen1,qkn hnd hlt hj]
def wj (v:Nat) : Nat :=
  let n := Nat.mod v 2305843009213693951
  Nat.mod (Nat.mul n (Nat.add n 971)) 2305843009213693951
lemma qcu (a:Sig) : wj a.toNat=w6 a := rfl
lemma qga (xs:List Sig) (init:Nat) :
    xs.foldl (fun v x => v+w6 x) init=init+we xs := by
  induction xs generalizing init with
  | nil => simp [we]
  | cons x xs ih =>
    unfold we
    simp only [List.foldl_cons,Nat.zero_add]
    rw [ih,ih (w6 x),Nat.add_assoc]
lemma qag (x:Sig) (xs:List Sig) : we (x :: xs)=w6 x+we xs := by
  unfold we
  simp only [List.foldl_cons,Nat.zero_add]
  exact qga xs (w6 x)
lemma qfx {xs ys:List Sig} (h:xs.Perm ys) : we xs=we ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [qag,ih]
  | swap x y l => simp [qag];omega
  | trans _ _ h1 h2 => exact h1.trans h2
lemma qjj (ws:List qw) :
    ((ws.map (fun w => w.1.toNat)).map wj).foldl Nat.add 0=we (ws.map Prod.fst) := by
  have go (xs:List qw) (init:Nat) :
      ((xs.map (fun w => w.1.toNat)).map wj).foldl Nat.add init =
      (xs.map Prod.fst).foldl (fun v x => v+w6 x) init := by
    induction xs generalizing init with
    | nil => rfl
    | cons x xs ih => exact ih _
  exact go ws 0
def qtc (un ka kb:Bool) (ksum ki kj:Nat) : Nat :=
  let h1 := match ka with | true => ksum | false => Nat.sub ksum ki
  match un with
  | true => h1
  | false => match kb with | true => h1 | false => Nat.sub h1 kj
lemma qex {ws:List qw} (hnd:(ws.map Prod.fst).Nodup) {i j:Nat}
    (un ka kb:Bool) (hi:i < ws.length) (hj:j < ws.length) (hij:un=false -> i < j)
    (z:Sig) :
    let kws := (ws.map (fun w => w.1.toNat)).map wj
    let ksum := kws.foldl Nat.add 0
    Nat.add (qtc un ka kb ksum (jd kws i) (jd kws j)) (wj z.toNat) =
    we (z :: (jk un ka kb (ws.getD i qb) (ws.getD j qb) ws).map Prod.fst) := by
  dsimp only [qtc]
  rw [qjj,qag,qcu,Nat.add_comm]
  congr 1
  have hki:jd ((ws.map (fun w => w.1.toNat)).map wj) i =
      w6 (ws.getD i qb).1 := by
    rw [List.map_map,vv _ ws i hi]
    simp [List.getD_eq_getElem?_getD,hi,qcu]
  have hkj:jd ((ws.map (fun w => w.1.toNat)).map wj) j =
      w6 (ws.getD j qb).1 := by
    rw [List.map_map,vv _ ws j hj]
    simp [List.getD_eq_getElem?_getD,hj,qcu]
  rw [hki,hkj]
  have hma:ws.getD i qb ∈ ws := by simp [List.getD_eq_getElem?_getD,hi]
  have hmb:ws.getD j qb ∈ ws := by simp [List.getD_eq_getElem?_getD,hj]
  have hdel1 (a:qw) (ha:a ∈ ws) :
      we (ws.map Prod.fst) - w6 a.1=we ((ws.erase a).map Prod.fst) := by
    have hp := qfx ((List.perm_cons_erase ha).map Prod.fst)
    rw [List.map_cons,qag] at hp
    omega
  cases un with
  | true =>
    cases ka with
    | true => rfl
    | false => exact hdel1 _ hma
  | false =>
    have hlt := hij rfl
    have hne:ws.getD i qb ≠ ws.getD j qb := by
      intro eq
      have h1:(ws.map Prod.fst)[i]'(by simpa using hi)=(ws.map Prod.fst)[j]'(by simpa using hj) := by
        simp only [List.getElem_map]
        simp [List.getD_eq_getElem?_getD,hi,hj] at eq
        exact congrArg Prod.fst eq
      exact Nat.ne_of_lt hlt ((List.Nodup.getElem_inj_iff hnd).mp h1)
    cases ka with
    | true =>
      cases kb with
      | true => rfl
      | false => exact hdel1 _ hmb
    | false =>
      cases kb with
      | true => exact hdel1 _ hma
      | false =>
        change (we (ws.map Prod.fst) - w6 (ws.getD i qb).1) -
            w6 (ws.getD j qb).1 =
          we (((ws.erase (ws.getD i qb)).erase (ws.getD j qb)).map Prod.fst)
        rw [hdel1 _ hma]
        have hmb':ws.getD j qb ∈ ws.erase (ws.getD i qb) :=
          (List.mem_erase_of_ne (Ne.symm hne)).mpr hmb
        have hp := qfx ((List.perm_cons_erase hmb').map Prod.fst)
        rw [List.map_cons,qag] at hp
        omega
def v7 (v:Nat) : Bool :=
  let i := Nat.land v 15
  let j := Nat.shiftRight v 4
  Nat.blt i j&&Nat.blt j 9
def qc6 (v k:Nat) : Nat :=
  let i := Nat.land v 15
  let j := Nat.shiftRight v 4
  match Nat.beq k i with
  | true => j
  | false => match Nat.beq k j with | true => i | false => k
def wd (swaps:List Nat) (k:Nat) : Nat :=
  swaps.foldl (fun acc v => qc6 v acc) k
lemma qcf :
    ∀ (v:Fin 144),v7 v.val=true -> ∀ (k:Fin 9),
      qck (ji v.val) (inputs.getD k.val zero)=inputs.getD (qc6 v.val k.val) zero ∧
      qc6 v.val k.val < 9 := by
  decide +kernel
lemma qnj {v:Nat} (hv:v7 v=true) : v < 144 := by
  unfold v7 at hv
  simp only [Bool.and_eq_true] at hv
  have h1:v &&& 15 < v >>> 4 := Nat.blt_eq.mp hv.1
  have h2:v >>> 4 < 9 := Nat.blt_eq.mp hv.2
  have hdiv:v >>> 4=v / 16 := Nat.shiftRight_eq_div_pow v 4
  have hmod:v &&& 15=v % 16 := by simpa using Nat.and_two_pow_sub_one_eq_mod v 4
  omega
lemma qbv {v k:Nat} (hv:v7 v=true) (hk:k < 9) :
    qck (ji v) (inputs.getD k zero)=inputs.getD (qc6 v k) zero ∧
    qc6 v k < 9 :=
  qcf ⟨v,qnj hv⟩ hv ⟨k,hk⟩
lemma qfk (ms ns:List qcj) (a:Sig) :
    q1 (ms ++ ns) a=q1 ms (q1 ns a) := by
  simp [q1,List.foldr_append]
lemma yw (p:List Nat) (hp:v6 v7 p=true) {k:Nat} (hk:k < 9) :
    q1 (p.map ji).reverse (inputs.getD k zero)=inputs.getD (wd p k) zero ∧
    wd p k < 9 := by
  induction p generalizing k with
  | nil => exact ⟨rfl,hk⟩
  | cons v vs ih =>
    simp only [v6] at hp
    cases hv:v7 v with
    | false => rw [hv] at hp;contradiction
    | true =>
      rw [hv] at hp
      obtain ⟨hw,hlt⟩ := qbv hv hk
      simp only [List.map_cons,List.reverse_cons,qfk,wd,List.foldl_cons]
      have h1:q1 [ji v] (inputs.getD k zero)=inputs.getD (qc6 v k) zero := hw
      rw [h1]
      exact ih hp hlt
def qbe:Nat -> Nat -> List Nat -> List Nat
  | 0,_,ws => ws
  | k+1,bits,ws =>
    let a := jd ws (Nat.land bits 15)
    let b := jd ws (Nat.land (Nat.shiftRight bits 4) 15)
    qbe k (Nat.shiftRight bits 10) (ws ++ [qat (Nat.land (Nat.shiftRight bits 8) 3) a b])
lemma qcd (f:Row -> Row) (ws:List qw) (j:Nat) :
    jd (ws.map (fun d => (q5 f d.1).toNat)) j =
    (q5 f (ws.getD j qb).1).toNat := by
  induction ws generalizing j with
  | nil => simp [jd,qb,(wv f).1,yb]
  | cons w ws ih =>
    cases j with
    | zero => rfl
    | succ m => exact ih m
lemma qgf (f:Row -> Row) (n bits:Nat) (ws:List qw) :
    qbe n bits (ws.map (fun d => (q5 f d.1).toNat)) =
    (qa0 n bits ws).map (fun d => (q5 f d.1).toNat) := by
  induction n generalizing bits ws with
  | zero => rfl
  | succ n ih =>
    unfold qbe qa0
    dsimp only
    rw [qcd,qcd,qah]
    have hstep:ql (Nat.land (Nat.shiftRight bits 8) 3,
        q5 f (ws.getD (Nat.land bits 15) qb).1,
        q5 f (ws.getD (Nat.land (Nat.shiftRight bits 4) 15) qb).1) =
        q5 f (jy ((bits >>> 8) &&& 3)
          (ws.getD (bits &&& 15) qb)
          (ws.getD ((bits >>> 4) &&& 15) qb)).1 := by
      change ql ((bits >>> 8) &&& 3,_,_)=_
      unfold ql jy
      by_cases h2:((bits >>> 8) &&& 3)=2
      . simp [h2,qm4,qax]
      . cases h1:(((bits >>> 8) &&& 3)==1) <;> simp [h2,h1,qtb,qdt]
    rw [hstep]
    have happ:ws.map (fun d => (q5 f d.1).toNat) ++
        [(q5 f (jy ((bits >>> 8) &&& 3)
          (ws.getD (bits &&& 15) qb)
          (ws.getD ((bits >>> 4) &&& 15) qb)).1).toNat] =
        (ws ++ [jy ((bits >>> 8) &&& 3)
          (ws.getD (bits &&& 15) qb)
          (ws.getD ((bits >>> 4) &&& 15) qb)]).map (fun d => (q5 f d.1).toNat) := by
      simp
    rw [happ]
    exact ih _ _
lemma qi2 {α β : Type} (f : α -> β) (bits:Nat) (ws:List α) :
    vh bits (ws.map f)=(vh bits ws).map f := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons]
    unfold vh
    by_cases h:(bits &&& 1==1)=true
    . rw [if_pos h,if_pos h,List.map_cons,ih]
    . rw [if_neg h,if_neg h,ih]
def qan (m:Nat) (p:List Nat) : List Nat :=
  let base := (wi m).map (fun (i,_) => jd qd2 (wd p i))
  match m.testBit 10 with
  | true => base ++ [qat 2 (jd qd2 (wd p 0)) 0]
  | false => base
lemma qno (m:Nat) (p:List Nat) (hp:v6 v7 p=true) :
    qan m p =
    (qo m).map (fun w => (q1 (p.map ji).reverse w).toNat) := by
  have hbase:(wi m).map (fun (i,_) => jd qd2 (wd p i)) =
      ((wi m).map Prod.snd).map (fun w => (q1 (p.map ji).reverse w).toNat) := by
    rw [List.map_map]
    apply List.map_congr_left
    rintro ⟨i,a⟩ hm
    obtain ⟨hi,rfl⟩ := qcy hm
    obtain ⟨hmv,_⟩ := yw p hp hi
    dsimp only [Function.comp_def]
    rw [hmv,qd2,qcz]
  unfold qan qo
  cases ht:m.testBit 10 with
  | false => simpa [ht] using hbase
  | true =>
    simp only [ht,ite_true,List.map_append,List.map_singleton,hbase]
    congr 1;congr 1
    obtain ⟨hmv0,_⟩ := yw p hp (by omega:0 < 9)
    rw [qd2,qcz,← hmv0]
    have h0:qat 2 (q1 (p.map ji).reverse (inputs.getD 0 zero)).toNat 0 =
        (ql (2,q1 (p.map ji).reverse (inputs.getD 0 zero),zero)).toNat := by
      conv => lhs;arg 3;rw [← yb]
      exact qah 2 _ _
    rw [h0]
    have hch:ql (2,q1 (p.map ji).reverse (inputs.getD 0 zero),zero) =
        neg (q1 (p.map ji).reverse qu) := rfl
    rw [hch]
    congr 1
    change neg (q1 (p.map ji).reverse qu)=q1 (p.map ji).reverse (neg qu)
    rw [zt,zt,qax]
def qb4 (g:qx) (rawPerm:List Nat) (k i:Nat) : List Nat :=
  let (_,depth,_,_,_,_,_,data) := jn g k
  let len := Nat.mul 10 depth
  let width := Nat.add len (Nat.add rawPerm.length depth)
  let recp := vr data (Nat.mul i width) width
  let ops := Nat.land recp (Nat.sub (Nat.shiftLeft 1 len) 1)
  let bank := qbe depth ops rawPerm
  vh (Nat.shiftRight recp len) bank
lemma qf4 (g:qx) : (j7 g).map Prod.fst=qo (jh g) := by
  unfold j7 qd6 qo
  cases ht:(jh g).testBit 10 <;> simp [ht,List.map_map,Function.comp_def]
lemma qf7 (g:qx) (p:List Nat) (hp:v6 v7 p=true) (k i:Nat) :
    qb4 g (qan (jh g) p) k i =
    ((wh g k i).map (q1 (p.map ji).reverse)).map BitVec.toNat := by
  have hraw:qan (jh g) p =
      (j7 g).map (fun d => (q5 (z5 (p.map ji).reverse) d.1).toNat) := by
    rw [qno _ _ hp,← qf4 g,List.map_map]
    apply List.map_congr_left
    intro d _
    simp [Function.comp_def,zt]
  have hlen:(qan (jh g) p).length=(j7 g).length := by rw [hraw,List.length_map]
  unfold qb4 wh yj
  dsimp only
  rw [hlen,hraw,qgf,qi2,List.map_map,List.map_map]
  have hw:Nat.add (Nat.mul 10 (jn g k).2.1) (Nat.add (j7 g).length (jn g k).2.1) =
      10*(jn g k).2.1+(j7 g).length+(jn g k).2.1 := by
    change 10*(jn g k).2.1+((j7 g).length+(jn g k).2.1)=_
    rw [Nat.add_assoc]
  rw [hw]
  change (vh _ _).map _=(vh _ _).map _
  apply List.map_congr_left
  intro d _
  simp [Function.comp_def,zt]
def qmr (g:qx) (pidx:Nat) : Option (List Nat) :=
  match (qdq g)[pidx]? with
  | none => none
  | some p =>
    match v6 v7 p with
    | false => none
    | true => some (qan (jh g) p)
def qcn (g:qx) (k h:Nat) : Option (List Nat) :=
  match qdp g k h with
  | none => none
  | some pair =>
    let k1 := Nat.sub k 1
    match Nat.blt pair.1 (jn g k1).1 with
    | false => none
    | true =>
      match qmr g pair.2 with
      | none => none
      | some rp => some (qb4 g rp k1 pair.1)
lemma qi6 {g:qx} {k h:Nat} {xs:List Nat}
    (hl:qcn g k h=some xs) :
    ∃ ys:List Sig,((qdp g k h).bind (yf g (k - 1)))=some ys ∧
      ys.map BitVec.toNat=xs := by
  unfold qcn at hl
  cases hf:qdp g k h with
  | none => rw [hf] at hl;contradiction
  | some pair =>
    rw [hf] at hl;dsimp only at hl
    cases hlt:Nat.blt pair.1 (jn g (Nat.sub k 1)).1 with
    | false => rw [hlt] at hl;contradiction
    | true =>
      rw [hlt] at hl;dsimp only at hl
      unfold qmr at hl
      cases ha:(qdq g)[pair.2]? with
      | none => rw [ha] at hl;contradiction
      | some perm =>
        rw [ha] at hl;dsimp only at hl
        cases hv:v6 v7 perm with
        | false => rw [hv] at hl;contradiction
        | true =>
          rw [hv] at hl;injection hl with hl;subst xs
          refine ⟨(wh g (k - 1) pair.1).map (q1 (perm.map ji).reverse),?_,?_⟩
          . simp only [Option.bind_some,yf]
            have hlt0:pair.1 < (jn g (k - 1)).1 := Nat.blt_eq.mp hlt
            have hlt':¬(pair.1 ≥ (jn g (k - 1)).1) := by omega
            rw [if_neg hlt',ha];rfl
          . exact (qf7 g perm hv (k - 1) pair.1).symm
abbrev qke := Nat × Nat × List qw × List Nat × qhs × List qhx × List qm5 × Nat × List Nat
def jo (g:qx) (k i:Nat) : qke :=
  let raw := j7 g
  let (num,depth,cw,_iw,_pw,offw,lw,data) := jn g k
  let (ops,bank,ws) := yj g k i
  let wsN := ws.map (fun w => w.1.toNat)
  let start := Nat.mul num (Nat.add (Nat.mul 10 depth) (Nat.add raw.length depth))
  let pos := Nat.add (Nat.add start (Nat.mul num offw)) (vr data (Nat.add start (Nat.mul i offw)) offw)
  let nr := vr data pos 5
  let st := Nat.add (Nat.add pos 5) lw
  let paidw := match (jh g).testBit 10 with | true => Nat.add depth 1 | false => depth
  let poolsO := (qen data cw paidw nr st).filterMap (fun (a,b) => qb0 g ops depth bank a b)
  let qpoolsO := poolsO.filterMap (qav wsN)
  let kws := wsN.map wj
  let ksum := kws.foldl Nat.add 0
  (k,wsN.length,ws,wsN,qbx ws,poolsO,qpoolsO,ksum,kws)
def qdc (g:qx) (c:qke) (i j op:Nat) (ka kb:Bool) : Bool :=
  let (cap,_,_,wsN,_,poolsO,qpoolsO,ksum,kws) := c
  let mode := vj g
  let dis := match Nat.beq mode 0 with
    | true => false
    | false => !(qb1 mode op (jd wsN i) (jd wsN j) ka kb)
  match dis with
  | true => true
  | false =>
    let k1 := Nat.sub cap 1
    match y9 (fun q => qby q k1 i j op ka kb) qpoolsO with
    | true => true
    | false =>
      let a := jd wsN i
      let b := jd wsN j
      let z := qat op a b
      match Nat.beq z 0 with
      | true => true
      | false => match Nat.beq z qdy with
        | true => true
        | false => match wt z wsN with
          | true => true
          | false =>
            let un := Nat.beq op 2
            let rest := qcp un ka kb i j wsN
            let h := Nat.add (qtc un ka kb ksum (jd kws i) (jd kws j)) (wj z)
            let hit := match qcn g cap h with
              | none => false
              | some xs => qas (z :: rest) xs
            match hit with
            | true => true
            | false => y9 (fun p => qaj p k1 rest op a b z) poolsO
def q3 (g:qx) (k i:Nat) : j8 :=
  let raw := j7 g
  let (num,depth,cw,_iw,_pw,offw,lw,data) := jn g k
  let (ops,bank,ws) := yj g k i
  let start := num*(10*depth+raw.length+depth)
  let pos := start+num*offw+vr data (start+i*offw) offw
  let nr := vr data pos 5
  let st := pos+5+lw
  let paidw := if (jh g).testBit 10 then depth+1 else depth
  let rules := (qen data cw paidw nr st).filterMap (fun (a,b) => y0 g ops depth bank a b)
  let ls := fun tag => ((qdp g k tag).bind (yf g (k - 1))).toList
  (k,ws.length,ws,qbx ws,rules,ls)
lemma qey {α β γ : Type} (f : α -> Option β) (h : β -> γ) (xs:List α) :
    xs.filterMap (fun a => (f a).map h)=(xs.filterMap f).map h := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    cases f x <;> simp [ih]
lemma qnw (g:qx) (k idx:Nat) :
    (jo g k idx).2.2.2.2.2.1=(q3 g k idx).2.2.2.2.1.map yi := by
  unfold jo q3
  dsimp only
  set p := jn g k
  have hpw:(match (jh g).testBit 10 with | true => Nat.add p.2.1 1 | false => p.2.1) =
      (if (jh g).testBit 10 then p.2.1+1 else p.2.1) := by
    cases (jh g).testBit 10 <;> rfl
  have hst:Nat.mul p.1 (Nat.add (Nat.mul 10 p.2.1) (Nat.add (j7 g).length p.2.1)) =
      p.1*(10*p.2.1+(j7 g).length+p.2.1) := by
    change p.1*(10*p.2.1+((j7 g).length+p.2.1))=_
    rw [Nat.add_assoc]
  have hpos:Nat.add (Nat.add (Nat.mul p.1 (Nat.add (Nat.mul 10 p.2.1) (Nat.add (j7 g).length p.2.1)))
      (Nat.mul p.1 p.2.2.2.2.2.1))
      (vr p.2.2.2.2.2.2.2 (Nat.add (Nat.mul p.1 (Nat.add (Nat.mul 10 p.2.1) (Nat.add (j7 g).length p.2.1)))
      (Nat.mul idx p.2.2.2.2.2.1)) p.2.2.2.2.2.1) =
      p.1*(10*p.2.1+(j7 g).length+p.2.1)+p.1*p.2.2.2.2.2.1 +
      vr p.2.2.2.2.2.2.2 (p.1*(10*p.2.1+(j7 g).length+p.2.1)+idx*p.2.2.2.2.2.1) p.2.2.2.2.2.1 := by
    rw [hst];rfl
  rw [hpw,hpos]
  have hfn:(fun x:Nat × Nat => qb0 g (yj g k idx).1 p.2.1 (yj g k idx).2.1 x.1 x.2) =
      (fun x:Nat × Nat => (y0 g (yj g k idx).1 p.2.1 (yj g k idx).2.1 x.1 x.2).map yi) := by
    funext x;exact qkr g _ _ _ x.1 x.2
  rw [hfn]
  exact qey _ _ _
lemma v3 {mode:Nat} {nc:j8} {op:Nat} {a b z:qw} {ka kb:Bool}
    (hc:wm nc.2.2.2.2.1 nc.2.2.2.2.2 (nc.1 - 1)
      ((jk (op==2) ka kb a b nc.2.2.1).map Prod.fst) (zl op a b)=true) :
    vg mode nc op a b z ka kb=true := by
  obtain ⟨cap,n,ws,cov,pools,links⟩ := nc
  unfold vg;dsimp only
  by_cases h1:(!vd mode op a.1 b.1 ka kb)=true
  . rw [if_pos h1]
  rw [if_neg h1]
  by_cases h2:1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1)) > cap
  . rw [if_pos h2]
  rw [if_neg h2]
  by_cases h3:((y5 (qbg cov (1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))==cap))
      (zy (1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))==cap) a.2)
      (zy (1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))==cap) b.2) (op==2) ka kb |||
      zy (1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))==cap) z.2) != BitVec.allOnes 768)=true
  . rw [if_pos h3]
  rw [if_neg h3]
  by_cases h4:(!zz z.1||ws.any (fun v => v.1==z.1))=true
  . rw [if_pos h4]
  rw [if_neg h4];exact hc
lemma wr {mode:Nat} {nc:j8} {op:Nat} {a b z:qw} {ka kb:Bool}
    (hf:(!zz z.1||nc.2.2.1.any (fun v => v.1==z.1))=true) :
    vg mode nc op a b z ka kb=true := by
  obtain ⟨cap,n,ws,cov,pools,links⟩ := nc
  unfold vg;dsimp only
  by_cases h1:(!vd mode op a.1 b.1 ka kb)=true
  . rw [if_pos h1]
  rw [if_neg h1]
  by_cases h2:1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1)) > cap
  . rw [if_pos h2]
  rw [if_neg h2]
  by_cases h3:((y5 (qbg cov (1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))==cap))
      (zy (1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))==cap) a.2)
      (zy (1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))==cap) b.2) (op==2) ka kb |||
      zy (1+(n - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))==cap) z.2) != BitVec.allOnes 768)=true
  . rw [if_pos h3]
  rw [if_neg h3,if_pos hf]
lemma qgd {g:qx} {k idx i j op:Nat} {ka kb:Bool}
    (hnd:((q3 g k idx).2.2.1.map Prod.fst).Nodup)
    (hi:i < (q3 g k idx).2.2.1.length)
    (hj:j < (q3 g k idx).2.2.1.length)
    (hij:(op==2)=false -> i < j)
    (hfb:qdc g (jo g k idx) i j op ka kb=true) :
    qd3 (vj g) (q3 g k idx) i j op ka kb=true := by
  set nc := q3 g k idx
  set ws := nc.2.2.1
  set rules := nc.2.2.2.2.1
  set a := ws.getD i qb
  set b := ws.getD j qb
  unfold qd3 zd
  change vg (vj g) nc op a b (qr op a b) ka kb=true
  have hwsN:(jo g k idx).2.2.2.1=ws.map (fun w => w.1.toNat) := rfl
  have hpools:(jo g k idx).2.2.2.2.2.1=rules.map yi := qnw g k idx
  have hqp:(jo g k idx).2.2.2.2.2.2.1=(rules.map yi).filterMap (qav (ws.map (fun w => w.1.toNat))) := by
    change (jo g k idx).2.2.2.2.2.1.filterMap (qav (ws.map (fun w => w.1.toNat)))=_
    rw [hpools]
  have hkws:(jo g k idx).2.2.2.2.2.2.2.2=(ws.map (fun w => w.1.toNat)).map wj := rfl
  have hksum:(jo g k idx).2.2.2.2.2.2.2.1=((ws.map (fun w => w.1.toNat)).map wj).foldl Nat.add 0 := rfl
  have hma:a ∈ ws := by simp [a,List.getD_eq_getElem?_getD,hi]
  have hmb:b ∈ ws := by simp [b,List.getD_eq_getElem?_getD,hj]
  have hdis_eq:(match Nat.beq (vj g) 0 with
      | true => false
      | false => !(qb1 (vj g) op (jd (ws.map (fun w => w.1.toNat)) i)
          (jd (ws.map (fun w => w.1.toNat)) j) ka kb)) =
      !vd (vj g) op a.1 b.1 ka kb := by
    rw [ww,ww,qmm]
    cases hm:Nat.beq (vj g) 0 with
    | true =>
      have h0:vj g=0 := Nat.eq_of_beq_eq_true hm
      simp [h0,vd,jc,zq]
    | false => rfl
  unfold qdc at hfb
  dsimp only at hfb
  have hc1:(jo g k idx).1=k := rfl
  rw [hwsN,hdis_eq,hc1] at hfb
  cases hal:(!vd (vj g) op a.1 b.1 ka kb) with
  | true =>
    unfold vg
    dsimp only
    rw [if_pos hal]
  | false =>
    rw [hal] at hfb;dsimp only at hfb
    cases hqb:y9 (fun q => qby q (Nat.sub k 1) i j op ka kb) (jo g k idx).2.2.2.2.2.2.1 with
    | true =>
      obtain ⟨q,hqm,hqok⟩ := (qer _ _).mp hqb
      rw [hqp,List.mem_filterMap] at hqm
      obtain ⟨po,hpom,hsum⟩ := hqm
      obtain ⟨p,hpm,rfl⟩ := List.mem_map.mp hpom
      have hfc := qfm hi hj hsum hqok
      have hsc := qkp hma hmb hfc
      have hcut:rules.any (fun p => jf p (k - 1)
          ((jk (op==2) ka kb a b ws).map Prod.fst) (zl op a b))=true :=
        List.any_eq_true.mpr ⟨p,hpm,hsc⟩
      exact v3 (nc := nc) (by
        unfold wm;dsimp only
        exact Bool.or_eq_true _ _ |>.mpr (Or.inr hcut))
    | false =>
      rw [hqb] at hfb;dsimp only at hfb
      rw [ww,ww,qah] at hfb
      have hz_eq:ql (op,a.1,b.1)=(qr op a b).1 := (qdu op a b).symm
      rw [hz_eq] at hfb
      cases hz0:Nat.beq (qr op a b).1.toNat 0 with
      | true =>
        have eq0:(qr op a b).1=zero :=
          BitVec.eq_of_toNat_eq ((Nat.eq_of_beq_eq_true hz0).trans yb.symm)
        exact wr (nc := nc) (by simp [zz,eq0])
      | false =>
        rw [hz0] at hfb;dsimp only at hfb
        cases hz1:Nat.beq (qr op a b).1.toNat qdy with
        | true =>
          have eq1:(qr op a b).1=one := BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hz1)
          exact wr (nc := nc) (by simp [zz,eq1])
        | false =>
          rw [hz1] at hfb;dsimp only at hfb
          cases hmem:wt (qr op a b).1.toNat (ws.map (fun w => w.1.toNat)) with
          | true =>
            obtain ⟨w,hwm,heq⟩ := List.mem_map.mp ((qba _ _).mp hmem)
            have hany:ws.any (fun v => v.1==(qr op a b).1)=true :=
              List.any_eq_true.mpr ⟨w,hwm,beq_iff_eq.mpr (BitVec.eq_of_toNat_eq heq)⟩
            exact wr (nc := nc) (by
              change (!zz (qr op a b).1||ws.any (fun v => v.1==(qr op a b).1))=true
              rw [hany,Bool.or_true])
          | false =>
            rw [hmem] at hfb;dsimp only at hfb
            have hun:Nat.beq op 2=(op==2) := rfl
            have hdrop := qqx hnd (op==2) ka kb hi hj hij
            have hkey := qex hnd (op==2) ka kb hi hj hij (qr op a b).1
            dsimp only at hkey
            rw [hkws,hksum,hun,hdrop,hkey] at hfb
            cases hlk:(match qcn g k (we ((qr op a b).1 :: (jk (op==2) ka kb a b ws).map Prod.fst)) with
                | none => false
                | some xs => qas ((qr op a b).1.toNat :: ((jk (op==2) ka kb a b ws).map Prod.fst).map BitVec.toNat) xs) with
            | true =>
              cases hli:qcn g k (we ((qr op a b).1 :: (jk (op==2) ka kb a b ws).map Prod.fst)) with
              | none => rw [hli] at hlk;contradiction
              | some xs =>
                rw [hli] at hlk;dsimp only at hlk
                obtain ⟨ys,hys,rfl⟩ := qi6 hli
                have hsw:ye ((qr op a b).1 :: (jk (op==2) ka kb a b ws).map Prod.fst) ys=true :=
                  qdz hlk
                have hany:(nc.2.2.2.2.2 (we (ql (zl op a b) :: (jk (op==2) ka kb a b ws).map Prod.fst))).any
                    (ye (ql (zl op a b) :: (jk (op==2) ka kb a b ws).map Prod.fst))=true := by
                  rw [← qdu op a b]
                  change (((qdp g k _).bind (yf g (k - 1))).toList).any _=true
                  rw [hys];simp [hsw]
                exact v3 (nc := nc) (by unfold wm;dsimp only;rw [hany,Bool.true_or])
            | false =>
              rw [hlk] at hfb;dsimp only at hfb
              change y9 _ (jo g k idx).2.2.2.2.2.1=true at hfb
              rw [hpools] at hfb
              obtain ⟨po,hpom,hsc2⟩ := (qer _ _).mp hfb
              obtain ⟨p,hpm,rfl⟩ := List.mem_map.mp hpom
              rw [← hz_eq] at hsc2
              have hsc := qcg hsc2
              have hcut:rules.any (fun p => jf p (k - 1)
                  ((jk (op==2) ka kb a b ws).map Prod.fst) (zl op a b))=true :=
                List.any_eq_true.mpr ⟨p,hpm,hsc⟩
              exact v3 (nc := nc) (by
        unfold wm;dsimp only
        exact Bool.or_eq_true _ _ |>.mpr (Or.inr hcut))
def qbk (f:qke -> Bool) (mask:Nat) : List qke -> Bool
  | [] => true
  | x :: xs =>
    match Nat.beq mask 0 with
    | true => true
    | false =>
      match Nat.beq (Nat.land mask 1) 0 with
      | true => qbk f (Nat.shiftRight mask 769) xs
      | false => match f x with
        | true => qbk f (Nat.shiftRight mask 769) xs
        | false => false
lemma qpt (f:qke -> Bool) (mask:Nat) (xs:List qke) (q:Nat) (hq:q < xs.length)
    (bitOn:mask.testBit (769*q)=true) (ok:qbk f mask xs=true) : f xs[q]=true := by
  induction xs generalizing mask q with
  | nil => simp at hq
  | cons x xs ih =>
    have hne:Nat.beq mask 0=false := by
      cases hb:Nat.beq mask 0 with
      | true => have e := Nat.eq_of_beq_eq_true hb;simp [e] at bitOn
      | false => rfl
    unfold qbk at ok
    rw [hne] at ok;dsimp only at ok
    cases q with
    | zero =>
      have hnz:Nat.beq (Nat.land mask 1) 0=false := by
        cases hb:Nat.beq (Nat.land mask 1) 0 with
        | true =>
          have e := Nat.eq_of_beq_eq_true hb
          have at0 := congrArg (fun n:Nat => n.testBit 0) e
          change (mask &&& 1).testBit 0=(0:Nat).testBit 0 at at0
          rw [Nat.testBit_and] at at0
          change mask.testBit 0=true at bitOn
          simp [bitOn] at at0
        | false => rfl
      rw [hnz] at ok;dsimp only at ok
      cases hfx:f x with
      | true => exact hfx
      | false => rw [hfx] at ok;contradiction
    | succ q =>
      have hbit':(Nat.shiftRight mask 769).testBit (769*q)=true := by
        change (mask >>> 769).testBit (769*q)=true
        simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
      cases hb:Nat.beq (Nat.land mask 1) 0 with
      | true =>
        rw [hb] at ok
        exact ih (Nat.shiftRight mask 769) q (by simpa using hq) hbit' ok
      | false =>
        rw [hb] at ok;dsimp only at ok
        cases hfx:f x with
        | false => rw [hfx] at ok;contradiction
        | true =>
          rw [hfx] at ok
          exact ih (Nat.shiftRight mask 769) q (by simpa using hq) hbit' ok
def bmO (g:qx) (k ar r:Nat) (col0 col1:List Nat) (u v:qbt) (xs:List qke)
    (i j op zcol0 zcol1:Nat) (ka kb:Bool) : Bool :=
  let un := Nat.beq op 2
  let len := Nat.add 1 (Nat.sub (Nat.sub ar (match ka with | true => 0 | false => 1))
    (match un with | true => 0 | false => match kb with | true => 0 | false => 1))
  match Nat.blt k len with
  | true => true
  | false =>
    let d := Nat.beq len k
    let ca := jd (match d with | true => col1 | false => col0) i
    let cb := jd (match d with | true => col1 | false => col0) j
    let cz := match d with | true => zcol1 | false => zcol0
    let cov := match d with | true => v | false => u
    let mask := qbq r (Nat.lor (qds cov ca cb un ka kb) cz)
    qbk (fun c => qdc g c i j op ka kb) mask xs
def qbo (g:qx) (k ar r full:Nat) (wsP:List y1) (col0 col1:List Nat)
    (u v:qbt) (xs:List qke) (i:Nat) (a:y1) : List Nat -> Bool
  | [] => true
  | j :: jt =>
    let bw := wsP.getD j (0,0)
    let z0 := wz full 0 a bw
    let z00 := q2 false z0
    let z01 := q2 true z0
    match bmO g k ar r col0 col1 u v xs i j 0 z00 z01 false false with
    | false => false
    | true => match bmO g k ar r col0 col1 u v xs i j 0 z00 z01 true false with
      | false => false
      | true => match bmO g k ar r col0 col1 u v xs i j 0 z00 z01 false true with
        | false => false
        | true => match bmO g k ar r col0 col1 u v xs i j 0 z00 z01 true true with
          | false => false
          | true =>
            let z1 := wz full 1 a bw
            let z10 := q2 false z1
            let z11 := q2 true z1
            match bmO g k ar r col0 col1 u v xs i j 1 z10 z11 false false with
            | false => false
            | true => match bmO g k ar r col0 col1 u v xs i j 1 z10 z11 true false with
              | false => false
              | true => match bmO g k ar r col0 col1 u v xs i j 1 z10 z11 false true with
                | false => false
                | true => match bmO g k ar r col0 col1 u v xs i j 1 z10 z11 true true with
                  | false => false
                  | true => qbo g k ar r full wsP col0 col1 u v xs i a jt
def qc8 (g:qx) (k ar r full:Nat) (wsP:List y1) (col0 col1:List Nat)
    (u v:qbt) (xs:List qke) : List Nat -> Bool
  | [] => true
  | i :: js =>
    let a := wsP.getD i (0,0)
    let zu := wz full 2 a a
    let zu0 := q2 false zu
    let zu1 := q2 true zu
    match bmO g k ar r col0 col1 u v xs i i 2 zu0 zu1 false false with
    | false => false
    | true => match bmO g k ar r col0 col1 u v xs i i 2 zu0 zu1 true true with
      | false => false
      | true => match qbo g k ar r full wsP col0 col1 u v xs i a js with
        | false => false
        | true => qc8 g k ar r full wsP col0 col1 u v xs js
def qcv (tN ar:Nat) (c:qke) : Bool :=
  match Nat.beq c.2.1 ar with
  | false => false
  | true => match qcl c.2.2.2.1 with
    | false => false
    | true => !(wt tN c.2.2.2.1)
def qfd (g:qx) (k start n ar:Nat) : Bool :=
  let xs := ((List.range n).map (start+·)).map (jo g k)
  let tN := (zn g).toNat
  match v6 (qcv tN ar) xs with
  | false => false
  | true =>
    match Nat.beq k 0 with
    | true => true
    | false =>
      let r := ve n
      let full := Nat.mul r (BitVec.allOnes 768).toNat
      let wsP := (List.range ar).map (fun i => z6 (fun c => (c.2.2.1.getD i qb).2) xs)
      let col0 := wsP.map (q2 false)
      let col1 := wsP.map (q2 true)
      let u := vc (fun c => c.2.2.2.2.1.1) xs
      let v := vc (fun c => c.2.2.2.2.1.2) xs
      qc8 g k ar r full wsP col0 col1 u v xs (List.range ar)
lemma qty (ar op:Nat) (ka kb:Bool) :
    Nat.add 1 (Nat.sub (Nat.sub ar (match ka with | true => 0 | false => 1))
      (match Nat.beq op 2 with | true => 0 | false => match kb with | true => 0 | false => 1)) =
    1+(ar - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1)) := by
  change _=1+(ar - (if ka then 0 else 1) - (if Nat.beq op 2||kb then 0 else 1))
  cases ka <;> cases Nat.beq op 2 <;> cases kb <;> rfl
lemma qbh {g:qx} {k start n ar:Nat} {i j op:Nat} {ka kb:Bool}
    (hi:i < ar) (hj:j < ar) (hij:(op==2)=false -> i < j)
    {q:Nat} (hq:q < n)
    (hnd:((q3 g k (start+q)).2.2.1.map Prod.fst).Nodup)
    (har:(q3 g k (start+q)).2.2.1.length=ar)
    (pass :
      let xs := ((List.range n).map (start+·)).map (jo g k)
      let r := ve n
      let full := Nat.mul r (BitVec.allOnes 768).toNat
      let wsP := (List.range ar).map (fun t => z6 (fun c => (c.2.2.1.getD t qb).2) xs)
      let col0 := wsP.map (q2 false)
      let col1 := wsP.map (q2 true)
      let u := vc (fun c => c.2.2.2.2.1.1) xs
      let v := vc (fun c => c.2.2.2.2.1.2) xs
      let z := wz full op (wsP.getD i (0,0)) (wsP.getD j (0,0))
      bmO g k ar r col0 col1 u v xs i j op (q2 false z) (q2 true z) ka kb=true) :
    qd3 (vj g) (q3 g k (start+q)) i j op ka kb=true := by
  dsimp only at pass
  set xs := ((List.range n).map (start+·)).map (jo g k)
  set r := ve n
  set full := Nat.mul r (BitVec.allOnes 768).toNat
  set wsP := (List.range ar).map (fun t => z6 (fun c => (c.2.2.1.getD t qb).2) xs)
  set col0 := wsP.map (q2 false)
  set col1 := wsP.map (q2 true)
  set u := vc (fun c => c.2.2.2.2.1.1) xs
  set v := vc (fun c => c.2.2.2.2.1.2) xs
  set nc := q3 g k (start+q)
  have hxlen:xs.length=n := by simp [xs]
  have hqx:q < xs.length := by rw [hxlen];exact hq
  have hxsq:xs[q]'hqx=jo g k (start+q) := by simp [xs]
  let len := 1+(ar - (if ka then 0 else 1) - (if (op==2)||kb then 0 else 1))
  let d := len==k
  have hwsP_at (t:Nat) (ht:t < ar) :
      wsP.getD t (0,0)=z6 (fun c => (c.2.2.1.getD t qb).2) xs := by
    simp [wsP,List.getD_eq_getElem?_getD,ht]
  have hcol_at (dir:Bool) (t:Nat) (ht:t < ar) :
      jd (match dir with | true => col1 | false => col0) t =
      q2 dir (z6 (fun c => (c.2.2.1.getD t qb).2) xs) := by
    cases dir with
    | false =>
      have h1 := vv (q2 false) wsP t (by simp [wsP,ht])
      rw [h1];simp [wsP,ht]
    | true =>
      have h1 := vv (q2 true) wsP t (by simp [wsP,ht])
      rw [h1];simp [wsP,ht]
  have hnc_len:nc.2.1=ar := har
  have eval:qd3 (vj g) nc i j op ka kb =
      if !vd (vj g) op (zd nc i).1 (zd nc j).1 ka kb then true
      else if len > k then true
      else if qfg nc d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !zz (qr op (zd nc i) (zd nc j)).1 ||
        nc.2.2.1.any (fun v => v.1==(qr op (zd nc i) (zd nc j)).1)
      then true else wm nc.2.2.2.2.1 nc.2.2.2.2.2 (k - 1)
        ((jk (op==2) ka kb (zd nc i) (zd nc j) nc.2.2.1).map Prod.fst)
        (zl op (zd nc i) (zd nc j)) := by
    simp only [qd3,vg,hnc_len,len,d,qfg];rfl
  by_cases hdis:(!vd (vj g) op (zd nc i).1 (zd nc j).1 ka kb)=true
  . rw [eval,if_pos hdis]
  by_cases small:len > k
  . simp [eval,hdis,small]
  . unfold bmO at pass
    dsimp only at pass
    rw [qty ar op ka kb] at pass
    have hblt:Nat.blt k len=false := by
      cases hb:Nat.blt k len with
      | true => have := Nat.blt_eq.mp hb;omega
      | false => rfl
    change (match Nat.blt k len with | true => true | false => _)=true at pass
    rw [hblt] at pass;dsimp only at pass
    have hd_eq:Nat.beq len k=d := rfl
    rw [hd_eq,hcol_at d i hi,hcol_at d j hj,hwsP_at i hi,hwsP_at j hj] at pass
    have hzcol:∀ dir:Bool,(match dir with
        | true => q2 true (wz full op (z6 (fun c => (c.2.2.1.getD i qb).2) xs)
            (z6 (fun c => (c.2.2.1.getD j qb).2) xs))
        | false => q2 false (wz full op (z6 (fun c => (c.2.2.1.getD i qb).2) xs)
            (z6 (fun c => (c.2.2.1.getD j qb).2) xs))) =
        q2 dir (wz (ve xs.length*(BitVec.allOnes 768).toNat) op
          (z6 (fun c => (c.2.2.1.getD i qb).2) xs)
          (z6 (fun c => (c.2.2.1.getD j qb).2) xs)) := fun dir => by
      have hfull:full=ve xs.length*(BitVec.allOnes 768).toNat := by
        change ve n*(BitVec.allOnes 768).toNat=_
        rw [hxlen]
      rw [hfull];cases dir <;> rfl
    have hcov:∀ dir:Bool,(match dir with | true => v | false => u)=vc (fun c => qbg c.2.2.2.2.1 dir) xs := fun dir => by
      cases dir <;> rfl
    have hr_eq:r=ve xs.length := by simp [r,hxlen]
    rw [hzcol d,hcov d,qwh,qbi,qbi,qbi,qkh,hr_eq] at pass
    change qbk (fun c => qdc g c i j op ka kb)
      (qbq (ve xs.length) (qq (fun c => y5 (qbg c.2.2.2.2.1 d)
        (zy d (c.2.2.1.getD i qb).2) (zy d (c.2.2.1.getD j qb).2)
        (op==2) ka kb) xs |||
        qq (fun c => zy d (qr op (c.2.2.1.getD i qb)
        (c.2.2.1.getD j qb)).2) xs)) xs=true at pass
    rw [qh2] at pass
    by_cases hit:qfg nc d (op==2) ka kb op i j=BitVec.allOnes 768
    . have hbit:(qbq (ve xs.length) (qq (fun c =>
          y5 (qbg c.2.2.2.2.1 d) (zy d (c.2.2.1.getD i qb).2)
            (zy d (c.2.2.1.getD j qb).2) (op==2) ka kb |||
          zy d (qr op (c.2.2.1.getD i qb)
            (c.2.2.1.getD j qb)).2) xs)).testBit (769*q)=true := by
        rw [zbm _ _ _ hqx,hxsq]
        exact beq_iff_eq.mpr hit
      have hfb := qpt _ _ _ q hqx hbit pass
      rw [hxsq] at hfb
      exact qgd hnd (har ▸ hi) (har ▸ hj) hij hfb
    . rw [eval,if_neg hdis,if_neg small,if_pos (bne_iff_ne.mpr hit)]
lemma qnk {g:qx} {k start n ar:Nat} {i:Nat} (hi:i < ar)
    {q:Nat} (hq:q < n)
    (hnd:((q3 g k (start+q)).2.2.1.map Prod.fst).Nodup)
    (har:(q3 g k (start+q)).2.2.1.length=ar)
    (js:List Nat) (hbounds:∀ j ∈ js,i < j /\ j < ar)
    (pass :
      let xs := ((List.range n).map (start+·)).map (jo g k)
      let r := ve n
      let full := Nat.mul r (BitVec.allOnes 768).toNat
      let wsP := (List.range ar).map (fun t => z6 (fun c => (c.2.2.1.getD t qb).2) xs)
      let col0 := wsP.map (q2 false)
      let col1 := wsP.map (q2 true)
      let u := vc (fun c => c.2.2.2.2.1.1) xs
      let v := vc (fun c => c.2.2.2.2.1.2) xs
      qbo g k ar r full wsP col0 col1 u v xs i (wsP.getD i (0,0)) js=true) :
    ∀ j ∈ js,
      wg (vj g) (q3 g k (start+q))
        (zd (q3 g k (start+q)) i)
        (zd (q3 g k (start+q)) j) false=true ∧
      wg (vj g) (q3 g k (start+q))
        (zd (q3 g k (start+q)) i)
        (zd (q3 g k (start+q)) j) true=true := by
  induction js with
  | nil => intro j hj;simp at hj
  | cons j jt ih =>
    dsimp only [qbo] at pass
    cases h00:bmO g k ar (ve n) _ _ _ _ _ i j 0 _ _ false false <;> rw [h00] at pass
    . contradiction
    cases h01:bmO g k ar (ve n) _ _ _ _ _ i j 0 _ _ true false <;> rw [h01] at pass
    . contradiction
    cases h02:bmO g k ar (ve n) _ _ _ _ _ i j 0 _ _ false true <;> rw [h02] at pass
    . contradiction
    cases h03:bmO g k ar (ve n) _ _ _ _ _ i j 0 _ _ true true <;> rw [h03] at pass
    . contradiction
    cases h10:bmO g k ar (ve n) _ _ _ _ _ i j 1 _ _ false false <;> rw [h10] at pass
    . contradiction
    cases h11:bmO g k ar (ve n) _ _ _ _ _ i j 1 _ _ true false <;> rw [h11] at pass
    . contradiction
    cases h12:bmO g k ar (ve n) _ _ _ _ _ i j 1 _ _ false true <;> rw [h12] at pass
    . contradiction
    cases h13:bmO g k ar (ve n) _ _ _ _ _ i j 1 _ _ true true <;> rw [h13] at pass
    . contradiction
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    . obtain ⟨hlt,hjlt⟩ := hbounds x List.mem_cons_self
      have c00 := qbh hi hjlt (fun _ => hlt) hq hnd har h00
      have c01 := qbh hi hjlt (fun _ => hlt) hq hnd har h01
      have c02 := qbh hi hjlt (fun _ => hlt) hq hnd har h02
      have c03 := qbh hi hjlt (fun _ => hlt) hq hnd har h03
      have c10 := qbh hi hjlt (fun _ => hlt) hq hnd har h10
      have c11 := qbh hi hjlt (fun _ => hlt) hq hnd har h11
      have c12 := qbh hi hjlt (fun _ => hlt) hq hnd har h12
      have c13 := qbh hi hjlt (fun _ => hlt) hq hnd har h13
      exact ⟨by simp only [wg,Bool.and_eq_true];exact ⟨⟨⟨c00,c01⟩,c02⟩,c03⟩,
             by simp only [wg,Bool.and_eq_true];exact ⟨⟨⟨c10,c11⟩,c12⟩,c13⟩⟩
    . exact ih (fun y hy => hbounds y (List.mem_cons_of_mem _ hy)) pass x hx'
lemma qnl {g:qx} {k start n ar:Nat} {q:Nat} (hq:q < n)
    (hnd:((q3 g k (start+q)).2.2.1.map Prod.fst).Nodup)
    (har:(q3 g k (start+q)).2.2.1.length=ar)
    (js:List Nat) (hbounds:∀ j ∈ js,j < ar) (hsort:js.Pairwise (· < ·))
    (pass :
      let xs := ((List.range n).map (start+·)).map (jo g k)
      let r := ve n
      let full := Nat.mul r (BitVec.allOnes 768).toNat
      let wsP := (List.range ar).map (fun t => z6 (fun c => (c.2.2.1.getD t qb).2) xs)
      let col0 := wsP.map (q2 false)
      let col1 := wsP.map (q2 true)
      let u := vc (fun c => c.2.2.2.2.1.1) xs
      let v := vc (fun c => c.2.2.2.2.1.2) xs
      qc8 g k ar r full wsP col0 col1 u v xs js=true) :
    y2 (vj g) (q3 g k (start+q)) (js.map (zd (q3 g k (start+q))))=true := by
  induction js with
  | nil => rfl
  | cons i jt ih =>
    dsimp only [qc8] at pass
    obtain ⟨hpair,hsort'⟩ := List.pairwise_cons.mp hsort
    have hi:i < ar := hbounds i List.mem_cons_self
    cases hu0:bmO g k ar (ve n) _ _ _ _ _ i i 2 _ _ false false <;> rw [hu0] at pass
    . contradiction
    cases hu1:bmO g k ar (ve n) _ _ _ _ _ i i 2 _ _ true true <;> rw [hu1] at pass
    . contradiction
    cases hjok:qbo g k ar (ve n) _ _ _ _ _ _ _ i _ jt <;> rw [hjok] at pass
    . contradiction
    simp only [List.map_cons,y2,qhn,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    refine ⟨⟨⟨qbh hi hi (by simp) hq hnd har hu0,qbh hi hi (by simp) hq hnd har hu1⟩,?_⟩,
      ih (fun y hy => hbounds y (List.mem_cons_of_mem _ hy)) hsort' pass⟩
    rintro _ ⟨j,hj,rfl⟩
    exact qnk hi hq hnd har jt (fun y hy => ⟨hpair y hy,hbounds y (List.mem_cons_of_mem _ hy)⟩) hjok j hj
lemma zbb {g:qx} {k start n ar:Nat}
    (h:qfd g k start n ar=true) : qc g k start n=true := by
  unfold qfd at h
  dsimp only at h
  cases hhdr:v6 (qcv (zn g).toNat ar) (((List.range n).map (start+·)).map (jo g k)) with
  | false => rw [hhdr] at h;contradiction
  | true =>
    rw [hhdr] at h;dsimp only at h
    have hall := (qns _ _).mp hhdr
    apply qwj
    intro idx hlo hhi
    set q := idx - start
    have hq:q < n := by omega
    have hidx:start+q=idx := by omega
    have hmem:jo g k idx ∈ ((List.range n).map (start+·)).map (jo g k) :=
      List.mem_map.mpr ⟨idx,List.mem_map.mpr ⟨q,List.mem_range.mpr hq,hidx⟩,rfl⟩
    have hitem := hall _ hmem
    unfold qcv at hitem
    cases harb:Nat.beq (jo g k idx).2.1 ar with
    | false => rw [harb] at hitem;contradiction
    | true =>
      rw [harb] at hitem;dsimp only at hitem
      have har:(q3 g k idx).2.2.1.length=ar := by
        have e := Nat.eq_of_beq_eq_true harb
        simpa [jo,q3] using e
      cases hndb:qcl (jo g k idx).2.2.2.1 with
      | false => rw [hndb] at hitem;contradiction
      | true =>
        rw [hndb] at hitem;dsimp only at hitem
        have hmapN:(jo g k idx).2.2.2.1=((q3 g k idx).2.2.1.map Prod.fst).map BitVec.toNat := by
          simp [jo,q3,List.map_map,Function.comp_def]
        have hnd:((q3 g k idx).2.2.1.map Prod.fst).Nodup := qi4 (hmapN ▸ hndb)
        have hout:(!((q3 g k idx).2.2.1.map Prod.fst).contains (zn g))=true := by
          cases hc:((q3 g k idx).2.2.1.map Prod.fst).contains (zn g) with
          | false => rfl
          | true =>
            exfalso
            have hmt:zn g ∈ (q3 g k idx).2.2.1.map Prod.fst := by
              simpa using hc
            have hmtN:wt (zn g).toNat (jo g k idx).2.2.2.1=true :=
              (qba _ _).mpr (hmapN ▸ List.mem_map_of_mem (f := BitVec.toNat) hmt)
            rw [hmtN] at hitem;contradiction
        change (decide ((q3 g k idx).2.2.1.map Prod.fst).Nodup &&
            !(((q3 g k idx).2.2.1.map Prod.fst).contains (zn g)) &&
            (if k=0 then true else y2 (vj g) (q3 g k idx) (q3 g k idx).2.2.1))=true
        rw [decide_eq_true hnd,hout]
        simp only [Bool.true_and]
        cases hk0:Nat.beq k 0 with
        | true => simp [Nat.eq_of_beq_eq_true hk0]
        | false =>
          have hne0:k ≠ 0 := fun e => by rw [e] at hk0;contradiction
          rw [hk0] at h;dsimp only at h
          rw [if_neg hne0]
          have hrun := qnl (g := g) (k := k) (start := start) (n := n) (ar := ar)
            hq (hidx ▸ hnd) (hidx ▸ har) (List.range ar) (fun _ => List.mem_range.mp) List.pairwise_lt_range h
          have heq:(List.range ar).map (zd (q3 g k (start+q))) =
              (q3 g k (start+q)).2.2.1 := by
            apply List.ext_getElem
            . simp [hidx,har]
            . intro t ht1 ht2
              simp [zd,List.getD_eq_getElem?_getD,ht2]
          rw [heq,hidx] at hrun
          exact hrun
def q8 {α} (f : α -> Bool) (xs:List α) : Nat -> Prop
  | 0 => xs.all f=true
  | d+1 => q8 f (xs.take (xs.length / 2)) d /\ q8 f (xs.drop (xs.length / 2)) d
lemma qk {α f xs d} (h : @q8 α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap:((xs.take (xs.length / 2)) ++ (xs.drop (xs.length / 2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
lemma bOk {g k s n} (ar) (h:qfd g k s n ar=true) : qc g k s n=true := zbb h
lemma bM {g k s s2 a b c} (h1:qc g k s a=true) (h2:qc g k s2 b=true) (hs:s+a=s2:=by rfl) (hc:a+b=c:=by rfl) : qc g k s c=true := by subst hs;subst hc;exact qri h1 h2
lemma qal {m cap prior ci hints} (low:∀ q,qy (qo q) (qa q) (prior q))
    (h:m.testBit 10=false /\ qbm m ci prior=true /\ zz (qa m)=true ∧
         zo (qa m) (qo m) (z2 m hints)=true ∧
         (z2 m hints).map Prod.fst=qo m /\ (qo m).Nodup ∧
         qd1 (wf ci.1 ci.2.1) ci.2.2.2.2.1 cap 0 (qo m) (qo m)=true) :
    qy (qo m) (qa m) (cap+1) :=
  qkm h.1 low h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2
def zgk (i:Nat) : Nat := 0xf
def quu:Nat -> zi × zi
  | 0 => (~~~0x450c158721b28662,~~~0xbaf336f3c3dba6e6)
  | 1 => (~~~0x208007016064812a,0x20812421801324c4)
  | 2 => (0xefbdbf97f9f6bf6a,0x102a401415600a0a)
  | 3 => (0xf3a9d7437375f5ba,0xfc028ab620235b0)
  | _ => (0,0)
def qx5:Nat -> qs
  | 3 => (1,0,0,0,1,0,0,zgk)
  | _ => q6
def zaf:Nat -> Nat -> Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15:qx := (15,3,0,quu,[],[[],[33,48]],qx5,zaf)
def zby (i:Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def zgj (i:Nat) : Nat := 0x84001e90fd02fd01fa00
def zgi (i:Nat) : Nat := 0x11a20bf
def qur:Nat -> zi × zi
  | 0 => (~~~0x2500054d2aa04606662631110534ca84870631d44aab5c453684d5629a,0x250142092220460600407048c382809c2160e048740030a88143281c44)
  | 1 => (~~~0x10a2012b90d9015a8d5845610028cbe5006852e54a42d2ab82986cccb4,~~~0x6f55deefef2efebe3bcff7c9df9e97dfbfefe7c97fe7b2fb97db7cdef4)
  | 2 => (0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4)
  | 3 => (0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002)
  | 4 => (~~~0x70189009bae0259007b49250c70a449095a11775b2941c08e39b55c0,~~~0x7f89676ff777dffed8f1f9cfeffee9ddaff3fbcf75e8bcffebe3bf5dc6)
  | _ => (0,0)
def qx2:Nat -> qs
  | 5 => (3,1,3,0,4,4,0,zgj)
  | 6 => (1,0,3,2,4,0,0,zgi)
  | _ => q6
def zae:Nat -> Nat -> Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => qf 5 25 2 10 2 4 (zby)
  | _ => fun _ => none
def g31:qx := (31,6,0,qur,[(1,0,30,0,4,0),(2,0,29,0,4,0),(4,0,27,0,4,0),(8,0,23,0,4,0),(16,0,15,0,4,0)],[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]],qx2,zae)
def zfh (i:Nat) : Nat := 0x120ff
def qqr:Nat -> zi × zi
  | 0 => (0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444)
  | 1 => (0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909)
  | 2 => (0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452)
  | 3 => (0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac)
  | 5 => (0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9)
  | 6 => (0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6)
  | _ => (0,0)
def quv:Nat -> qs
  | 6 => (1,0,2,0,1,0,0,zfh)
  | _ => q6
def qx6:Nat -> Nat -> Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def qyt:qx := (111,6,0,qqr,[(4,8,99,0,4,0),(1,32,78,0,4,0),(64,0,47,0,5,0)],[[],[83,32]],quv,qx6)
def qzv (i:Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def zfg (i:Nat) : Nat := 0x82000f487f40bfa03fa00
def zff (i:Nat) : Nat := 0x1f5859bf
def qqq:Nat -> zi × zi
  | 0 => (0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264)
  | 2 => (0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9)
  | 3 => (0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32)
  | 4 => (0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108)
  | 5 => (0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519)
  | 7 => (0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826)
  | _ => (0,0)
def qut:Nat -> qs
  | 6 => (3,1,3,0,4,4,0,zfg)
  | 7 => (1,0,3,2,4,0,0,zff)
  | _ => q6
def qx4:Nat -> Nat -> Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => qf 5 18 5 10 2 4 (qzv)
  | _ => fun _ => none
def qta:qx := (189,7,0,qqq,[(1,0,188,0,5,0),(12,0,177,0,4,0),(16,0,173,0,5,0),(17,0,172,0,4,0),(24,0,165,0,4,0),(33,0,156,0,4,0),(132,0,57,0,4,0),(160,0,29,0,4,0)],[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]],qut,qx4)
def qxk (i:Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def qzs (i:Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def qzt (i:Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def qzu (i:Nat) : Nat := 0x2c
def zfe (i:Nat) : Nat := 0x47d6448788a00
def zfd (i:Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def zfc (i:Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def zfb (i:Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def zca (i:Nat) : Nat := 0x1f3c11ff
def qqp:Nat -> zi × zi
  | 0 => (0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200)
  | 1 => (0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161)
  | 2 => (0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882)
  | 3 => (0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544)
  | 4 => (0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891)
  | 5 => (0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a)
  | 7 => (0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474)
  | _ => (0,0)
def qus:Nat -> qs
  | 6 => (1,4,6,0,2,0,0,zfe)
  | 7 => (28,3,6,0,2,8,0,zfd)
  | 8 => (100,2,6,5,2,12,0,zfc)
  | 9 => (12,1,6,7,2,9,0,zfb)
  | 10 => (1,0,6,4,2,0,0,zca)
  | _ => q6
def qx3:Nat -> Nat -> Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => qf 1 3 0 6 0 2 (qzu)
  | 8 => qf 17 64 6 11 5 2 (qzt)
  | 9 => qf 68 242 7 13 7 2 (qzs)
  | 10 => qf 9 46 4 10 4 2 (qxk)
  | _ => fun _ => none
def qd0:qx := (191,10,0,qqp,[(1,0,190,0,7,0),(2,0,189,0,8,0),(3,0,188,0,5,0),(4,0,187,0,7,0),(6,0,185,0,5,0),(8,0,183,0,8,0),(0,8,163,20,6,0),(10,0,181,0,5,0),(12,0,179,0,5,0),(4,8,163,16,5,0),(14,0,177,0,4,0),(16,0,175,0,8,0),(0,16,166,9,6,0),(1,16,166,8,5,0),(19,0,172,0,4,0),(24,0,167,0,7,0),(16,8,163,4,5,0),(8,16,166,1,5,0),(25,0,166,0,4,0),(9,16,166,0,4,0),(20,8,163,0,4,0),(32,0,159,0,8,0),(1,32,30,128,5,0),(35,0,156,0,4,0),(40,0,151,0,5,0),(48,0,143,0,5,0),(56,0,135,0,4,0),(128,0,63,0,8,0),(130,0,61,0,5,0),(4,128,27,32,5,0),(136,0,55,0,5,0),(160,0,31,0,7,0),(128,32,30,1,5,0),(32,128,27,4,5,0),(161,0,30,0,4,0),(129,32,30,0,4,0),(164,0,27,0,4,0),(36,128,27,0,4,0)],[[],[84,115],[117,67,32],[116,83,32]],qus,qx3)
def qxh (i:Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def qxi (i:Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def qxj (i:Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def qzr (i:Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def zfa (i:Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def ze9 (i:Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def zb9 (i:Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def zb8 (i:Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def zb7 (i:Nat) : Nat := 0x11b280e4ff
def qqo:Nat -> zi × zi
  | 0 => (0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80)
  | 1 => (0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201)
  | 2 => (0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512)
  | 3 => (0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204)
  | 4 => (0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039)
  | 5 => (0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002)
  | 6 => (0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464)
  | 8 => (0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)
  | _ => (0,0)
def quq:Nat -> qs
  | 8 => (25,4,6,0,3,8,0,zfa)
  | 9 => (91,3,6,5,3,11,0,ze9)
  | 10 => (41,2,6,7,3,12,0,zb9)
  | 11 => (6,1,6,6,3,8,0,zb8)
  | 12 => (1,0,6,3,3,0,0,zb7)
  | _ => q6
def qx1:Nat -> Nat -> Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => qf 17 68 7 12 5 3 (qzr)
  | 10 => qf 57 200 7 14 7 3 (qxj)
  | 11 => qf 30 108 6 13 6 3 (qxi)
  | 12 => qf 6 61 1 10 3 3 (qxh)
  | _ => fun _ => none
def qdo:qx := (383,12,0,qqo,[(1,0,382,0,9,0),(0,1,332,50,7,0),(2,0,381,0,9,0),(0,2,312,69,7,0),(3,0,380,0,6,0),(2,1,332,48,6,0),(1,2,312,68,6,0),(4,0,379,0,11,0),(5,0,378,0,7,0),(7,0,376,0,5,0),(5,2,312,64,5,0),(8,0,375,0,9,0),(0,8,99,276,7,0),(12,0,371,0,8,0),(13,0,354,0,4,0),(14,0,369,0,5,0),(16,0,367,0,11,0),(17,0,366,0,8,0),(18,0,365,0,7,0),(19,0,364,0,5,0),(18,1,332,32,5,0),(24,0,359,0,8,0),(25,0,358,0,5,0),(28,0,355,0,7,0),(20,8,99,256,5,0),(32,0,351,0,11,0),(33,0,350,0,8,0),(32,1,332,18,6,0),(35,0,348,0,5,0),(34,1,332,16,5,0),(44,0,339,0,5,0),(49,0,334,0,7,0),(48,1,332,2,5,0),(33,16,326,8,5,0),(56,0,327,0,5,0),(64,0,319,0,11,0),(65,0,318,0,7,0),(66,0,317,0,8,0),(67,0,316,0,5,0),(65,2,312,4,5,0),(70,0,313,0,7,0),(34,64,29,256,5,0),(256,0,127,0,9,0),(0,256,23,104,7,0),(264,0,119,0,6,0),(256,8,99,20,6,0),(8,256,23,96,6,0),(268,0,115,0,5,0),(260,8,99,16,5,0),(280,0,103,0,5,0),(272,8,99,4,5,0),(288,0,95,0,8,0),(289,0,94,0,5,0),(40,256,23,64,5,0),(304,0,79,0,5,0),(320,0,63,0,8,0),(322,0,61,0,5,0),(258,64,61,0,5,0),(352,0,31,0,7,0)],[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]],quq,qx1)
set_option maxHeartbeats 0 in
lemma zd8:qi g15 (qt [])=true := by
  simp only [qi,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qk (d:=0) ?_⟩,qk (d:=0) ?_⟩
  all_goals simp only [q8]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
lemma zbk:qc g15 3 0 1=true := bOk 4 (by decide +kernel)
lemma zfn:qc g15 3 0 1=true := zbk
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qyx:qp g15 3 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . exact zfn
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zgh:qy (qo 15) (qa 15) 4 :=
  zh (hm0:=rfl) (g:=g15) (i:=0) (hints:=8449) (qe [] qmw) zd8 qyx (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qhq := qh [] 4 [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
lemma qvs:zv qhq := qd qmw zgh (by decide +kernel)
set_option maxHeartbeats 0 in
lemma zd7:qi g31 (qt qhq)=true := by
  simp only [qi,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qk (d:=1) ?_⟩,qk (d:=2) ?_⟩
  all_goals simp only [q8]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
lemma zbj:qc g31 5 0 1=true := bOk 5 (by decide +kernel)
lemma zbi:qc g31 5 1 2=true := bOk 6 (by decide +kernel)
lemma zbh:qc g31 6 0 1=true := bOk 5 (by decide +kernel)
lemma zfm:qc g31 6 0 1=true := zbh
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qyw:qp g31 6 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact (bM zbj zbi)
  . exact zfm
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zgg:qy (qo 31) (qa 31) 7 :=
  zh (hm0:=rfl) (g:=g31) (i:=0) (hints:=8449) (qe qhq qvs) zd7 qyw (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qnf := qh qhq 7 [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
lemma qvr:zv qnf := qd qvs zgg (by decide +kernel)
lemma zgf:qy (qo 47) (qa 47) 5 :=
  qal (m:=47) (cap:=4) (ci:=(8,0,39,0,4,0)) (hints:=8449) (qe qnf qvr) (by decide +kernel)
def qne := qh qnf 5 [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
lemma qvq:zv qne := qd qvr zgf (by decide +kernel)
lemma zge:qy (qo 55) (qa 55) 5 :=
  qal (m:=55) (cap:=4) (ci:=(16,0,39,0,4,0)) (hints:=257) (qe qne qvq) (by decide +kernel)
def qnd := qh qne 5 [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
lemma qvp:zv qnd := qd qvq zge (by decide +kernel)
lemma zgd:qy (qo 63) (qa 63) 8 :=
  qal (m:=63) (cap:=7) (ci:=(32,0,31,0,7,0)) (hints:=8449) (qe qnd qvp) (by decide +kernel)
def qhp := qh qnd 8 [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
lemma qvo:zv qhp := qd qvp zgd (by decide +kernel)
set_option maxHeartbeats 0 in
lemma zb3:qi qyt (qt qhp)=true := by
  simp only [qi,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qk (d:=0) ?_⟩,qk (d:=0) ?_⟩
  all_goals simp only [q8]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
lemma qze:qc qyt 6 0 1=true := bOk 6 (by decide +kernel)
lemma zcy:qc qyt 6 0 1=true := qze
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qv5:qp qyt 6 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact zcy
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zd6:qy (qo 111) (qa 111) 7 :=
  zh (hm0:=rfl) (g:=qyt) (i:=0) (hints:=16785665) (qe qhp qvo) zb3 qv5 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qim := qh qhp 7 [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
lemma qph:zv qim := qd qvo zd6 (by decide +kernel)
lemma zd5:qy (qo 119) (qa 119) 6 :=
  qal (m:=119) (cap:=5) (ci:=(4,0,115,0,5,0)) (hints:=16777473) (qe qim qph) (by decide +kernel)
def qem := qh qim 6 [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
lemma qpg:zv qem := qd qph zd5 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma zb2:qi qta (qt qem)=true := by
  simp only [qi,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qk (d:=1) ?_⟩,qk (d:=2) ?_⟩
  all_goals simp only [q8]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
lemma qzd:qc qta 6 0 1=true := bOk 6 (by decide +kernel)
lemma qzc:qc qta 6 1 2=true := bOk 7 (by decide +kernel)
lemma qzb:qc qta 7 0 1=true := bOk 6 (by decide +kernel)
lemma zcx:qc qta 7 0 1=true := qzb
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qv4:qp qta 7 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact (bM qzd qzc)
  . exact zcx
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zd3:qy (qo 189) (qa 189) 8 :=
  zh (hm0:=rfl) (g:=qta) (i:=0) (hints:=536879876) (qe qem qpg) zb2 qv4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qil := qh qem 8 [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
lemma qpe:zv qil := qd qpg zd3 (by decide +kernel)
lemma zd4:qy (qo 127) (qa 127) 9 :=
  qal (m:=127) (cap:=8) (ci:=(32,0,95,0,8,0)) (hints:=16785665) (qe qil qpe) (by decide +kernel)
def qel := qh qil 9 [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
lemma qpf:zv qel := qd qpe zd4 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma zb1:qi qd0 (qt qel)=true := by
  simp only [qi,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qk (d:=4) ?_⟩,qk (d:=1) ?_⟩
  all_goals simp only [q8]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
lemma qza:qc qd0 6 0 1=true := bOk 7 (by decide +kernel)
lemma zcw:qc qd0 6 0 1=true := qza
lemma qy9:qc qd0 7 0 13=true := bOk 7 (by decide +kernel)
lemma qy8:qc qd0 7 13 15=true := bOk 8 (by decide +kernel)
lemma qy7:qc qd0 8 0 7=true := bOk 7 (by decide +kernel)
lemma qy6:qc qd0 8 7 61=true := bOk 8 (by decide +kernel)
lemma qy5:qc qd0 8 68 32=true := bOk 9 (by decide +kernel)
lemma qy4:qc qd0 9 0 3=true := bOk 7 (by decide +kernel)
lemma qy3:qc qd0 9 3 9=true := bOk 8 (by decide +kernel)
lemma qwe:qc qd0 10 0 1=true := bOk 7 (by decide +kernel)
lemma za9:qc qd0 10 0 1=true := qwe
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qv3:qp qd0 10 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact zcw
  . exact (bM qy9 qy8)
  . exact (bM (bM qy7 qy6) qy5)
  . exact (bM qy4 qy3)
  . exact za9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zd2:qy (qo 191) (qa 191) 11 :=
  zh (hm0:=rfl) (g:=qd0) (i:=0) (hints:=536879361) (qe qel qpf) zb1 qv3 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qik := qh qel 11 [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
lemma qpd:zv qik := qd qpf zd2 (by decide +kernel)
lemma zd1:qy (qo 251) (qa 251) 8 :=
  qal (m:=251) (cap:=7) (ci:=(8,0,243,0,7,0)) (hints:=1358970881) (qe qik qpd) (by decide +kernel)
def qij := qh qik 8 [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
lemma qpc:zv qij := qd qpd zd1 (by decide +kernel)
lemma zd0:qy (qo 255) (qa 255) 12 :=
  qal (m:=255) (cap:=11) (ci:=(64,0,191,0,11,0)) (hints:=553656577) (qe qij qpc) (by decide +kernel)
def qek := qh qij 12 [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
lemma qpb:zv qek := qd qpc zd0 (by decide +kernel)
set_option maxHeartbeats 0 in
lemma zb0:qi qdo (qt qek)=true := by
  simp only [qi,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qk (d:=4) ?_⟩,qk (d:=2) ?_⟩
  all_goals simp only [q8]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
lemma qy2:qc qdo 8 0 23=true := bOk 8 (by decide +kernel)
lemma qy1:qc qdo 8 23 2=true := bOk 9 (by decide +kernel)
lemma qy0:qc qdo 9 0 9=true := bOk 8 (by decide +kernel)
lemma qyz:qc qdo 9 9 75=true := bOk 9 (by decide +kernel)
lemma qyy:qc qdo 9 84 7=true := bOk 10 (by decide +kernel)
lemma qwd:qc qdo 10 0 5=true := bOk 8 (by decide +kernel)
lemma qwc:qc qdo 10 5 16=true := bOk 9 (by decide +kernel)
lemma qwb:qc qdo 10 21 20=true := bOk 10 (by decide +kernel)
lemma qwa:qc qdo 11 0 1=true := bOk 8 (by decide +kernel)
lemma qv9:qc qdo 11 1 5=true := bOk 9 (by decide +kernel)
lemma qv8:qc qdo 12 0 1=true := bOk 8 (by decide +kernel)
lemma za8:qc qdo 12 0 1=true := qv8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qv2:qp qdo 12 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact (bM qy2 qy1)
  . exact (bM (bM qy0 qyz) qyy)
  . exact (bM (bM qwd qwc) qwb)
  . exact (bM qwa qv9)
  . exact za8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zdz:qy (qo 383) (qa 383) 13 :=
  zh (hm0:=rfl) (g:=qdo) (i:=0) (hints:=12901687553) (qe qek qpb) zb0 qv2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qaa := qh qek 13 [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
lemma qd4:zv qaa := qd qpb zdz (by decide +kernel)
abbrev qji := qaa
def qw7 (i:Nat) : Nat := 0x3000
def ze8 (i:Nat) : Nat := 0x7a00
def ze7 (i:Nat) : Nat := 0xf
def qqn:Nat -> zi × zi
  | 0 => (0xf060607000df8e18,~~~0xd0a124024b16b1c6)
  | 1 => (~~~0x7c000e008e0780,~~~0xfda7efef6bf6b7ce)
  | 2 => (0xfffc7e7e3fdf8f9c,0x440300a42102950c)
  | 3 => (0xffff807fc78e0fe0,0x88105d49061d6ae0)
  | 4 => (0x0,0x0)
  | 5 => (0x0,0x0)
  | 6 => (0x0,0x0)
  | 7 => (0x0,0x0)
  | 8 => (0x0,0x0)
  | _ => (0,0)
def qup:Nat -> qs
  | 3 => (1,1,0,0,0,0,0,ze8)
  | 4 => (1,0,0,0,0,0,0,ze7)
  | _ => q6
def qx0:Nat -> Nat -> Option (Nat × Nat)
  | 4 => qf 1 5 3 4 0 0 (qw7)
  | _ => fun _ => none
def qys:qx := (527,4,0,qqn,[],[[]],qup,qx0)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qz9:qi qys (qt qji)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=0)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qr4:qc qys 3 0 1=true := bOk 4 (by decide +kernel)
lemma qr3:qc qys 4 0 1=true := bOk 4 (by decide +kernel)
lemma qtp:qp qys 4 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . exact qr4
  . exact qr3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zdy:qy (qo 527) (qa 527) 5 :=
  zh (hm0:=rfl) (g:=qys) (i:=0) (hints:=8449) (qe qaa qd4) qz9 qtp (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qej := qh qaa 5 [(527,[]),(541,[50,65]),(647,[115,99,83,67]),(677,[114,33,97,82,50,65]),(835,[131,115,98,83,66]),(865,[130,33,113,99,82,65])]
lemma qpa:zv qej := qd qd4 zdy (by decide +kernel)
abbrev qjh := qej
def qw6 (i:Nat) : Nat := 0x3000
def ze6 (i:Nat) : Nat := 0x7a00
def ze5 (i:Nat) : Nat := 0xf
def qqm:Nat -> zi × zi
  | 0 => (0xe00060700041cc18,~~~0xa104200249025246)
  | 1 => (~~~0xe1800e008e0360,~~~0xfb3f77ef6dfb576e)
  | 2 => (0xffe07e7e3f41cf1c,0x881d10a4251b570c)
  | 3 => (0x0,0x0)
  | 4 => (0xffff807fc78e0fe0,0x10905d49061dada0)
  | 5 => (0x0,0x0)
  | 6 => (0x0,0x0)
  | 7 => (0x0,0x0)
  | 8 => (0x0,0x0)
  | _ => (0,0)
def quo:Nat -> qs
  | 3 => (1,1,0,0,0,0,0,ze6)
  | 4 => (1,0,0,0,0,0,0,ze5)
  | _ => q6
def qxz:Nat -> Nat -> Option (Nat × Nat)
  | 4 => qf 1 5 3 4 0 0 (qw6)
  | _ => fun _ => none
def qyr:qx := (535,4,0,qqm,[],[[]],quo,qxz)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qz8:qi qyr (qt qjh)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=0)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qr2:qc qyr 3 0 1=true := bOk 4 (by decide +kernel)
lemma qr1:qc qyr 4 0 1=true := bOk 4 (by decide +kernel)
lemma qto:qp qyr 4 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . exact qr2
  . exact qr1
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zdx:qy (qo 535) (qa 535) 5 :=
  zh (hm0:=rfl) (g:=qyr) (i:=0) (hints:=257) (qe qej qpa) qz8 qto (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qei := qh qej 5 [(535,[]),(539,[50,65]),(551,[84]),(569,[65,33,82,49]),(595,[98,82,50]),(611,[66,100,82,50]),(689,[114,33,97,82,49])]
lemma qo9:zv qei := qd qpa zdx (by decide +kernel)
abbrev qjg := qei
def qw5 (i:Nat) : Nat := 0x39006660000720000010
def qw4 (i:Nat) : Nat := 0x5f80000218800000000000000000000000006dc3e11f50db0fcd000000000000029d020600174e40d8029175006bf8c009480000000000000000000017250050010000010c0000
def qw3 (i:Nat) : Nat := 0x514018400000000000000aae8da19b06000061c0000748000000101cd2c00b080000000000000000004b4511000002002000
def ze4 (i:Nat) : Nat := 0x9e99850506786550600ba18931802f06154a00
def ze3 (i:Nat) : Nat := 0xac2a084200000000008c00193c0005140fca9401f951803f283007e4ca00fc98c01f921802f4ab006791233d722445ba44803b467007388a33db08c896c524c6d8a4985e14141
def ze2 (i:Nat) : Nat := 0x2ea610a04098482975305e74d34d2bae2640fe00fd41fd32fd31fd21fd20fd10be44de33fa00
def ze1 (i:Nat) : Nat := 0x1a209f
def qql:Nat -> zi × zi
  | 0 => (0x7f800fe01f80701f8000007f00e001c00fc7038038101ade1fe1f60e18,~~~0x148293202a8490868888280d01200441000824124322624266260921c6)
  | 1 => (~~~0xfffe0007fe0007e038000ff80000e38e0700711139ffe0139b780,~~~0x7dd7b36b7ffdd9afdd9b7f5fbbb4dfebffbef77b673b7e7377273bb7ce)
  | 2 => (0x7fffffffe000001ffffe007fffff81ff8e07e3f1ff0ef8c01fe1078f9c,0xc418101164c49820401194488104c2012024121250a2231332303850c)
  | 3 => (0x7fffffffffffffe00000007ffffffe000ff803fe3ff0f29e1e01f80fe0,0x300e06060810021c3838e20810020087249002480a60c1464c4ca80ae0)
  | 4 => (0x7fffffffffffffffffffff80000000000ffffc003fff031fe001fff000,0x4070081810600c0040410070e09c713849249000348c00b9919156d000)
  | 5 => (0x0,0x0)
  | 6 => (0x0,0x0)
  | 7 => (0x0,0x0)
  | 8 => (0x0,0x0)
  | _ => (0,0)
def qun:Nat -> qs
  | 4 => (4,3,3,0,0,0,0,ze4)
  | 5 => (16,2,3,0,0,6,0,ze3)
  | 6 => (10,1,3,0,0,6,0,ze2)
  | 7 => (1,0,3,0,0,0,0,ze1)
  | _ => q6
def qxy:Nat -> Nat -> Option (Nat × Nat)
  | 5 => qf 2 12 4 7 2 1 (qw5)
  | 6 => qf 12 55 6 9 4 1 (qw4)
  | 7 => qf 8 40 6 9 4 1 (qw3)
  | _ => fun _ => none
def qm3:qx := (543,7,0,qql,[(2,0,541,0,5,0),(4,0,539,0,5,0),(8,0,535,0,5,0),(16,0,527,0,5,0),(0,1,30,0,4,0)],[[],[50,65]],qun,qxy)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qz7:qi qm3 (qt qjg)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=2)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qr0:qc qm3 4 0 4=true := bOk 5 (by decide +kernel)
lemma qlk:qc qm3 5 0 10=true := bOk 5 (by decide +kernel)
lemma qlj:qc qm3 5 10 6=true := bOk 6 (by decide +kernel)
lemma qli:qc qm3 6 0 3=true := bOk 5 (by decide +kernel)
lemma qlh:qc qm3 6 3 7=true := bOk 6 (by decide +kernel)
lemma qrz:qc qm3 7 0 1=true := bOk 5 (by decide +kernel)
lemma qtn:qp qm3 7 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qr0
  . exact (bM qlk qlj)
  . exact (bM qli qlh)
  . exact qrz
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zdw:qy (qo 543) (qa 543) 8 :=
  zh (hm0:=rfl) (g:=qm3) (i:=0) (hints:=8449) (qe qei qo9) qz7 qtn (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qii := qh qei 8 [(543,[]),(679,[115,67,100,83]),(867,[131,50,66,116,99,82])]
lemma qo8:zv qii := qd qo9 zdw (by decide +kernel)
lemma zdv:qy (qo 559) (qa 559) 6 :=
  qal (m:=559) (cap:=5) (ci:=(8,0,551,0,5,0)) (hints:=8449) (qe qii qo8) (by decide +kernel)
def qih := qh qii 6 [(559,[]),(573,[50,65]),(663,[115,99,83,67]),(881,[130,50,81,115,98,65])]
lemma qo7:zv qih := qd qo8 zdv (by decide +kernel)
lemma zdu:qy (qo 567) (qa 567) 6 :=
  qal (m:=567) (cap:=5) (ci:=(16,0,551,0,5,0)) (hints:=257) (qe qih qo7) (by decide +kernel)
def qig := qh qih 6 [(567,[]),(571,[50,65]),(627,[98,50])]
lemma qo6:zv qig := qd qo7 zdu (by decide +kernel)
lemma zdt:qy (qo 591) (qa 591) 6 :=
  qal (m:=591) (cap:=5) (ci:=(64,0,527,0,5,0)) (hints:=16785665) (qe qig qo6) (by decide +kernel)
def qif := qh qig 6 [(591,[])]
lemma qo5:zv qif := qd qo6 zdt (by decide +kernel)
lemma zds:qy (qo 603) (qa 603) 6 :=
  qal (m:=603) (cap:=5) (ci:=(8,0,595,0,5,0)) (hints:=16793601) (qe qif qo5) (by decide +kernel)
def qie := qh qif 6 [(603,[]),(697,[118,81,33]),(739,[67,116,83])]
lemma qo4:zv qie := qd qo5 zds (by decide +kernel)
lemma zdn:qy (qo 669) (qa 669) 6 :=
  qal (m:=669) (cap:=5) (ci:=(128,0,541,0,5,0)) (hints:=536879876) (qe qie qo4) (by decide +kernel)
def qic := qh qie 6 [(669,[]),(857,[130,114,98,82])]
lemma qoz:zv qic := qd qo4 zdn (by decide +kernel)
lemma zdr:qy (qo 607) (qa 607) 9 :=
  qal (m:=607) (cap:=8) (ci:=(64,0,543,0,8,0)) (hints:=16785665) (qe qic qoz) (by decide +kernel)
def qeh := qh qic 9 [(607,[]),(743,[67,116,83]),(995,[99,33,129,115,82,65])]
lemma qo3:zv qeh := qd qoz zdr (by decide +kernel)
abbrev qjf := qeh
def qw2 (i:Nat) : Nat := 0x1f0080b100000000000000000
def ze0 (i:Nat) : Nat := 0x4ad0d42818d2240fb08fe8037a83bd40
def zez (i:Nat) : Nat := 0xa993f
def qqk:Nat -> zi × zi
  | 0 => (0x1fff800000007ffff00000fff8000fffc0001fffe00007f80007fffc00001fff8000000000003fff800000000000001ffff00001fc0000000ff8000001ff83c1c0fc1c381fc007007000e00e07fff8e3001ff0fc067c1fe3c999adc60e18,0x6dfdd4f575fd6ff5f2fd6fdfd6bf37ffee7abdfedcfe5eff77a7ffafab5bd5fadab37abfdeaf6f5efab97abeeedf7eaf5ffeaf2f57fdbbf7ffd7dee7b7f7ffffebf5eeff1ebcdff3b7db79b6f96f865bb9f7b73f91f4cde739a7dbb9adeede39)
  | 1 => (0xf0001ffffffff0007fffffffff0000000fffffffffffffffffffffffffffffffe00000001ffff0003ffffffff0001ffff01ffffffffe000007fffffffffffe0f83c1f8e01ffffe03c7e3fe3fe1fe187fff03201003fffffc00fcc981ff26487f,0x40a8802000884261009040128425204a401000908094004a2000250000100050803200348000400c80100024401640020120020004882804b001000004a0000180404820048846018141181220420010312521108130c0042124810109244831)
  | 2 => (0xffffe000000000007ffffffffffffffff00000001ffffffff8000007ffffffffffffffffe00000003fffffffffffe000001ffffffffffffff8000ffffffc01f003fe00ffe03f1ffc07fc7fc7fe301f8c01e3c01ffcfe06001fe30e1e31c78f9c,0x800106462621848624218484180842108b2316230020881042324832306118830304230108c9899303022300808008c46448c444611001210262600221009250019600452015085402a822844a34aa8c8242c24524ca10a94aca0e143083850c)
  | 3 => (0x7fffffffffffffffffffffffe000000000000007ffffffffffffffffffffffffc000000000000000001ffffffffffffffffff000000001fffc0000ffffc01ffff8007ff8ffc01ff001fc001fff0000001f03f01fc1f80fe0,0xece18b858ce0b3848c60918e0318463004420c416c7136384c4b1c4c182611c0c184c26130202042c3c4c370b1b930b8993088986200246248404b4c63924a6ac0000aa4ac012aad0004d20b5cb557115bd249acb106756b535f00bc1780ae0)
  | 4 => (0x0,0x0)
  | 5 => (~~~0x7ffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000001ffffffffffffffffffffffffffe00000000ffffffe00000007fff00001ffffe00001ffffffffc1ffc001ffe000fff,0x8f000c060f003c070f80e1f00be077c0c7838f818f81c7c07073e07020381e0102070381c0c0c18302070380c1c1c0c001c0f0e07c13387c70788c707c2393b4ae4aa0000001d3324d20000f96f865a21f7b713016085e739a7dba001eed000)
  | 6 => (~~~0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000001fffffffffff0000000001ffffffffffff83fffc000001ffffff,0xf001f007f000c007f000fe000c007800f803f001f001f800007c007fc03fe001fc07fc01ff00fe03fc07fc00fe01ff00e1ff00ff801c3f807f80f07f803c1cc733934d39326800000000000dfbdffefc6dad80c0e8307fbdedb7efef6000000)
  | 7 => (0x0,0x0)
  | 8 => (0x0,0x0)
  | _ => (0,0)
def qum:Nat -> qs
  | 6 => (4,1,3,0,0,6,0,ze0)
  | 7 => (1,0,3,0,0,0,0,zez)
  | _ => q6
def qxx:Nat -> Nat -> Option (Nat × Nat)
  | 7 => qf 2 15 4 6 2 0 (qw2)
  | _ => fun _ => none
def qyq:qx := (623,7,0,qqk,[(32,0,591,0,6,0),(64,0,559,0,6,0),(4,8,611,0,5,0),(72,0,551,0,5,0),(0,1,78,0,4,0),(0,33,78,0,4,0)],[[]],qum,qxx)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qz6:qi qyq (qt qjf)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=2)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qry:qc qyq 6 0 4=true := bOk 6 (by decide +kernel)
lemma qrx:qc qyq 7 0 1=true := bOk 6 (by decide +kernel)
lemma qtm:qp qyq 7 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qry
  . exact qrx
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zdq:qy (qo 623) (qa 623) 8 :=
  zh (hm0:=rfl) (g:=qyq) (i:=0) (hints:=16785665) (qe qeh qo3) qz6 qtm (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qeg := qh qeh 8 [(623,[]),(855,[131,115,83,67,98])]
lemma qo2:zv qeg := qd qo3 zdq (by decide +kernel)
abbrev qje := qeg
def qw1 (i:Nat) : Nat := 0x60
def qw0 (i:Nat) : Nat := 0x3080010800000
def zey (i:Nat) : Nat := 0xee80140
def zex (i:Nat) : Nat := 0x15029cb182c507f803f401bd40
def zew (i:Nat) : Nat := 0x3a8ff
def qqj:Nat -> zi × zi
  | 0 => (0x1fff000000007fffe00000fffc0001fffc00000000fffc0001fc0001fffc00003ffe000000000000000000000000001fffc00007f00000000000000001ff87c1c0fe1c0e03fc00007000f00f0f9ffc78001ff800007c1f03d99b36f00f00,0x6fffd9faf7fedffdf5fedfbff6bfdbfffdcfebdffb7ffbefebfffdf3fffbf5dbebfdbaedf5ffbebf6f5fbfaff7dfff5fbfff5ebebff6efdfffd7f7fffbffffffeff5eeff9eef5bff7ddb7db6fddfcdd7bdff7bbfeb6aefef7baffbbb76fedf55)
  | 1 => (0xf0001fffffffe0007fffffffff00000001ffffffff8000ffffffffffffffffffffffc00000003ffff0000ffff8001fffe01ffffffff8000007fffc01fffffe0f87c1f8f01f8fffe071e3fe3ff1ff119fff8030180207f9fc001cd9833fca4c4f,0x416a8050029485690150802aa42ad02aa805400a920ab209401548001550001000a900e801d50022401720092016c00502a004002a20a0157002a02a0250000180c04830048248e030c11c1230930084399a70986222e20c632c910224ca4c45)
  | 2 => (0x0,0x0)
  | 3 => (0xffffe000000000007ffffffffffffffffe000000000000fffffffe000001ffffffffffffffffc00000000fffffffe000001ffffffffffffff8000001fffc01f007fe00ffe00fe3ff81fc7fc7fe701e1c01f9c01ffc0600001f031e1c38f38f8c,0x80430c9c58c7098e2863090c380c610c316671631c531c0211061099261c9861310e0c30988613338999c4c040808989c8c989130c4004862263394c9080925003560052a0056125816826845675763c8aa9d14ab41636b5ad561e1438a38a8c)
  | 4 => (0x7fffffffffffffffffffffffffffff00000000000001fffffffffffffffffffffffff00000000000001ffffffffffffffffffffe000001fff80000fffff003fffe007ff8ff801fe001fe001ffff806001fe3e01fc0fc0ff0,0xd8c1160a318163041841230c0308230c008020c200c20ac625861225861208242301041211824040202090d851b1216131210243080091844840001231924a6a80000a50aa0024a54004920a98a89c1115622154360414a52a9e00b405c0550)
  | 5 => (~~~0x7ffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000001ffffffffffffffffffffffffffe00000000fffffffc0000007fff00001ffffe00001ffffffffc1ffc001fff000fff,0x9f00180c3e007c071f81c3f00bf03bf018f838fc06fc0cf839f81c39f81c10383c02081c1e038380c1c0e0e061c1c18001c1e383f04ce1f8707c271c3e2393b4da4aa000000039369920000fddfcdd621ff7b99824287ef7baffba000fed000)
  | 6 => (~~~0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000003ffffffffff0000000001ffffffffffff83fffc000000ffffff,0xe001e00fc0018007e001fc000c003c001f003f0007000f003e00003e001fe03fc003f01fe003fc00fe00ff007e01fe01c1fe03fc0070fe007f80381fc03c1cc763934c9d349900000000000cf6cff7bc2658c06058505f39cd36efddb000000)
  | 7 => (0x0,0x0)
  | 8 => (0x0,0x0)
  | _ => (0,0)
def qul:Nat -> qs
  | 5 => (1,2,3,0,0,0,0,zey)
  | 6 => (3,1,3,0,0,5,0,zex)
  | 7 => (1,0,3,0,0,0,0,zew)
  | _ => q6
def qxw:Nat -> Nat -> Option (Nat × Nat)
  | 6 => qf 1 5 3 5 0 1 (qw1)
  | 7 => qf 2 9 4 7 2 1 (qw0)
  | _ => fun _ => none
def qs9:qx := (635,7,0,qqj,[(8,0,627,0,6,0),(32,0,603,0,6,0),(64,0,571,0,6,0),(2,64,569,0,5,0),(16,8,611,0,5,0),(24,0,611,0,5,0),(66,0,569,0,5,0)],[[],[99,65]],qul,qxw)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qz5:qi qs9 (qt qje)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=2)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qrw:qc qs9 5 0 1=true := bOk 6 (by decide +kernel)
lemma qlg:qc qs9 6 0 2=true := bOk 6 (by decide +kernel)
lemma qlf:qc qs9 6 2 1=true := bOk 7 (by decide +kernel)
lemma qrv:qc qs9 7 0 1=true := bOk 6 (by decide +kernel)
lemma qtl:qp qs9 7 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qrw
  . exact (bM qlg qlf)
  . exact qrv
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zdp:qy (qo 635) (qa 635) 8 :=
  zh (hm0:=rfl) (g:=qs9) (i:=0) (hints:=16793601) (qe qeg qo2) qz5 qtl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qid := qh qeg 8 [(635,[]),(699,[118,81])]
lemma qo1:zv qid := qd qo2 zdp (by decide +kernel)
lemma zdm:qy (qo 671) (qa 671) 9 :=
  qal (m:=671) (cap:=8) (ci:=(128,0,543,0,8,0)) (hints:=536879361) (qe qid qo1) (by decide +kernel)
def qee := qh qid 9 [(671,[]),(687,[84,115]),(875,[130,50,33,97,115,82,65]),(889,[130,114,98,81])]
lemma qoy:zv qee := qd qo1 zdm (by decide +kernel)
abbrev qjd := qee
def qwz (i:Nat) : Nat := 0x480000
def qwy (i:Nat) : Nat := 0x2562100000340000003d8680000000a7fc8038142470000000a32f8000000000000086800000000002860035003eed4daf9193760000000c5000000040140001040000
def qwx (i:Nat) : Nat := 0xc9802976a8a803ae56a1800a4000000000000000000a60000000006200000c5008000067000000000000880000b0000002804c601000000041000
def zev (i:Nat) : Nat := 0x4fa7718143
def zeu (i:Nat) : Nat := 0x2a1202a0400a4144280411c03178018a6006c0100000280fe58a00fe58600fe54a00fe50e00fe50a00fe4c600be99a00d795633de95600ed91211ee91200e78ce44db88a55fc84600be18143
def zet (i:Nat) : Nat := 0xbd103010230988319cc2384c4126b6ba286f1a79f3d37efcb78c9180ff007f54bfa87fd42fe98ff4c3fa41fd10bf2aef913ec23fa00
def zes (i:Nat) : Nat := 0x32ba13f
def qqi:Nat -> zi × zi
  | 0 => (0x3ffe0000fff0001fffc0001ffe000fff8000fc001fffc0001ffe000fff0000003ffe000fc003ffe0000fff00000000007ff800000000007ffc0007e00000003f000ff3e383e38381f80700e003aaafaa2fa8802f80fb5f33f33fbb659cc0e0c,0xaabd5afea9eabfd55fabbfd57d5ffacf96ff6ebfeabfabbfd4fd5ffa9f2bfdbfd6fe5ffef3ff75d5afead6ad7f5af6d7aeb96bfddfbafbfebcb5ff5ddfdd7dfeeeffff7f3bbf3bbcdfdf7b6f6dbbe6ba70bbdcb6eade9b555ebafbb6d9fd5e5c)
  | 1 => (0x0,0x0)
  | 2 => (0x3fffffff0000001fffffffe000000fffffff00001fffffffe000000ffffffc003ffffffffffffffffff0000001fff0007fffffe001ffe07ffffff80000fff03ffff38303e303e3ffc1c7c7f8fe333033bff2e83020fd130330382067f2cc8cf,0x30018028c0cc15181230251859854c02204448898c2430251895894c04412112989484a400940018028c06c0698004033012024816c020480901221412e01024009418100a100a084c0c182304a183102931ba9322462455514582041528c8ca)
  | 3 => (0xfc00000000000001ffffffffffffff000000000001ffffffffffffff0000000003ffffff00003fffffffffffffe0000007ffffffffe00007fffffffffff00003ffffc03fc03fc03f1fe07f8ff1fc3c03c303cf03fc0fc50330331c3861cf0f0f,0xc3260c430d30c86080c1086002001064c31183123108c10860220210c98c46246021010819219860c4306106020c9864c3043010800c4d131218440084062688042080234023401500a02504a10c3c8586864508942952aaa4921c2860870505)
  | 4 => (0xfffffffffffffffe00000000000000000000000001fffffffffffffffffffffffc00000000003ffffffffffffffffffff800000000000007fffffffffffffffc0000ffc0003fffc01fff800ffe3fc003fc03f003fff00603c03ce03f81f00ff0,0x8108c004011811b0231816c16608b04660c2cc031023180c40c601001881882c61630a2c6208108c082084c102081043843611b10b0642021880118884000a8c6694000141280155500094833c222701198a262c209555a28e01681700a50)
  | 5 => (~~~0x1ffffffffffffffffffffffffffffffffffc00000000000000000000000000000000007ffffffffffffffffffff0000003fffffe000000fffc00003fffc0003ffffd733f33f003ffe000fff,0x3000f001801e001c003e007007800c0078000f003e003e00f80f801e01f01f00f807c0c0f801000f0004007000c006002003801c00c0003c01f0181f007830c0f87254128000001a5a4a400029a6302023dcb2428412555492d30001fd5000)
  | 6 => (0x0,0x0)
  | 7 => (~~~0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000001fffffffffc000000003ffffffffcf0ff0ff000001ffffff,0x3c01f000e00e001e003c001801800f00780003001c003c001001000e00e00200300180003003e01f000f80f801f00f807c07c01e01f0187c03e0061e00f80c30f0084a9a529a52680000000001658c7d6c40140850849aaaa282cfbea000000)
  | 8 => (0x0,0x0)
  | _ => (0,0)
def quk:Nat -> qs
  | 5 => (1,3,4,0,0,0,0,zev)
  | 6 => (15,2,4,0,0,7,0,zeu)
  | 7 => (12,1,4,0,0,7,0,zet)
  | 8 => (1,0,4,0,0,0,0,zes)
  | _ => q6
def qxv:Nat -> Nat -> Option (Nat × Nat)
  | 6 => qf 1 5 3 5 0 1 (qwz)
  | 7 => qf 11 53 6 9 4 1 (qwy)
  | 8 => qf 9 46 6 9 4 1 (qwx)
  | _ => fun _ => none
def qm2:qx := (701,8,0,qqi,[(4,0,697,0,6,0),(32,0,669,0,6,0),(128,0,573,0,6,0),(0,1,188,0,5,0),(12,0,689,0,5,0),(24,0,677,0,5,0),(132,0,569,0,5,0),(160,0,541,0,5,0),(16,1,172,0,4,0),(32,1,156,0,4,0)],[[],[84,115]],quk,qxv)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qz4:qi qm2 (qt qjd)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=2)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qru:qc qm2 5 0 1=true := bOk 6 (by decide +kernel)
lemma qle:qc qm2 6 0 9=true := bOk 6 (by decide +kernel)
lemma qld:qc qm2 6 9 6=true := bOk 7 (by decide +kernel)
lemma qlc:qc qm2 7 0 4=true := bOk 6 (by decide +kernel)
lemma qlb:qc qm2 7 4 8=true := bOk 7 (by decide +kernel)
lemma qrt:qc qm2 8 0 1=true := bOk 6 (by decide +kernel)
lemma qtk:qp qm2 8 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qru
  . exact (bM qle qld)
  . exact (bM qlc qlb)
  . exact qrt
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zdl:qy (qo 701) (qa 701) 9 :=
  zh (hm0:=rfl) (g:=qm2) (i:=0) (hints:=536879876) (qe qee qoy) qz4 qtk (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qed := qh qee 9 [(701,[]),(859,[130,50,98,82,115,33,65])]
lemma qox:zv qed := qd qoy zdl (by decide +kernel)
abbrev qjb := qed
def qwv (i:Nat) : Nat := 0xa800000
def qwu (i:Nat) : Nat := 0xb00000892000015401e3f640000348000000fc79800880000156000000001d7000e8000000317ec00000000000d1b080001040000001
def qwt (i:Nat) : Nat := 0x194002180000000024000c9802420000000000084003aa0022108ce0051800010900158000000717e400000000000000
def zep (i:Nat) : Nat := 0x4fa7759010
def zeo (i:Nat) : Nat := 0x408021faaaaaaaaa00be99810db95622dd95611de95410ed91211ee91010d78ce55eb88a44fc84410be58810be18131be18121
def zen (i:Nat) : Nat := 0x2811c0a02214a532fa652483fc23fd53fea17f4d3fa63fd21bf2aef913ec23f810
def zem (i:Nat) : Nat := 0x680ff
def qqg:Nat -> zi × zi
  | 0 => (0x7ffe0007fff80003ffc003fff80007e003fffc0000fffc000fffc0007f000fff8000000ffff00007ff8007ffc000fffc0007f8003fff80007e000001fe00001fc3e0e0f0e0e07c1c7038001b37e34f9277c7e1e03fffe3fcb39798cd6e18,0x6d6b54ad77b296b75b5a99bbba5355aeb55fad555baad6aa9babe952ad5b6af5b5596addab5b156b76b5935bf5a2ad76b4cad776a5bd6d515aaf55ddedab69d6dfffd3f4e6f8e6f37f1e79b9b6190da33a8a0b4f21a0460003ffb39799cd6e39)
  | 1 => (0xffff80000007fffffffc000003fffffff80003ffffffff0000000fffffff80000ffffffffffffffffff8000007ffffffffffffffffffffffffff80003fffffffffe20300f880f8ffe01ffffe3f1dc803b01f9ff803ffd80c7c6f02061f0ff87f,0x4042108842200422021211211002000420490800110084809202400000020241201000880202004204211211210008042080822001080800100204818800008080000000200020210004108812190803300a08080000060003ff020611084831)
  | 2 => (0x7fffffffffffffc000000000003fffffffffffffff000000000000ffffffe000ffffffffffffff8000000fffffff800003fffffffffffc001fffff01c03ff00ff00fc7fe07e3fc7e1f003c01be40ffdf80a03e01c3c181cf18f9c,0x860c663198c420c41060020023186630c1923218620c180c20308c63318c4c98c1820c11306c218c20c6046046333198c01300443611b06260c4010830cc0104093403350099005425202a1284a0f494c854a51555d8b166f4003c180ca1850c)
  | 3 => (0xfffffffffff800000000000000000000000003fffffffffffffffffffffffffff0000000000fffffffffffffffffffff0000000000003ffffffffffffffe0000001ffc0000ffff007fff803ff8fe0003ffe3f80ffe0022338190c01fe0fe0fe0,0x87000c00300c7006380dc0dc06380c70605c0618030e030c0c3018406100021061c30e0c3804600470018018004002006e01b80c02e01840308001101004c18e24a540000224a004a4a8025204e010913235a2a8a010c9908b5c005405e0ae0)
  | 4 => (0x0,0x0)
  | 5 => (0x0,0x0)
  | 6 => (~~~0x3fffffffffffffffffffffffffffffffffffff0000000000000000000000000000000003fffffffffffffffffffffe0000000ffffff8000003fff000003fffc000fffffea33fd9f001fff000fff,0xf8007001c00f8007c00e00e007c00f80006007e003f003f00fc01f807e0703e07e03f00fc00780078002002003801c007001c00003001f803f0181e01f0701f038e99464a00000073934d00006651cc0221f7b30e8a28ddac00e94000f7b000)
  | 7 => (0x0,0x0)
  | 8 => (~~~0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000007fffffffff0000000003ffffffffda0ffc7f000000ffffff,0xf0007801e007000780030030038007000018038003c000c003000e00380000c008004001000f800f8007c07c07c03e00f803e00707c03e007c0061e03e0181e00c11229894cc949a000000000091ae12ec5c000411141322534a16babf000000)
  | _ => (0,0)
def qui:Nat -> qs
  | 5 => (1,3,3,0,0,0,0,zep)
  | 6 => (12,2,3,0,0,4,0,zeo)
  | 7 => (10,1,3,0,0,5,0,zen)
  | 8 => (1,0,3,0,0,0,0,zem)
  | _ => q6
def qxt:Nat -> Nat -> Option (Nat × Nat)
  | 6 => qf 1 5 3 5 0 1 (qwv)
  | 7 => qf 9 45 6 9 4 1 (qwu)
  | 8 => qf 8 37 6 9 4 1 (qwt)
  | _ => fun _ => none
def qof:qx := (847,8,0,qqg,[(0,1,334,0,7,0),(1,0,332,2,5,0),(12,0,835,0,5,0),(320,0,527,0,5,0),(2,0,332,0,4,0)],[[],[131,98]],qui,qxt)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qz2:qi qof (qt qjb)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=2)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qrs:qc qof 5 0 1=true := bOk 6 (by decide +kernel)
lemma qrr:qc qof 6 0 12=true := bOk 6 (by decide +kernel)
lemma qk6:qc qof 7 0 4=true := bOk 6 (by decide +kernel)
lemma qk5:qc qof 7 4 6=true := bOk 7 (by decide +kernel)
lemma qrq:qc qof 8 0 1=true := bOk 6 (by decide +kernel)
lemma qti:qp qof 8 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qrs
  . exact qrr
  . exact (bM qk6 qk5)
  . exact qrq
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zdh:qy (qo 847) (qa 847) 9 :=
  zh (hm0:=rfl) (g:=qof) (i:=0) (hints:=12901687553) (qe qed qox) qz2 qti (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qeb := qh qed 9 [(847,[]),(941,[98,118,81,130,50,65])]
lemma qot:zv qeb := qd qox zdh (by decide +kernel)
abbrev qja := qeb
def qws (i:Nat) : Nat := 0x3a80e78000000004822800000000000021
def zel (i:Nat) : Nat := 0x22d468110906cb1b48903bc67ee22fd007d4c7f241f830
def zek (i:Nat) : Nat := 0x218ff
def qqf:Nat -> zi × zi
  | 0 => (0xffe00003fffe0000fff8000fe0007fffe00001ffff0000000000007fff80003fe0003fffe00003fff800000000001fff8000ffff00001ff0000000007f8001ffc3f0e01f800e03f800707000c18fff827f831ffc001fc7fff07feccc2ce0ce0c,0x5d5efbab9cd5defab397ef6e9ffaaead5dd5d53aaadeaf5eadbd5add597eafbb9fd77a2d5d7baba9575bebabb75ebd5975fed6a2ebabdb4ebd6f6d7fed7befffebf4f4dfcd6f1bfe6b7c79b6d5856e8b5a9293f5553e44526a53eccd6ce5ce5c)
  | 1 => (0x0,0x0)
  | 2 => (0xfffffffc00000000fffffff000007ffffffffe000000001fffc0007fffffffc000003ffffffffc00000003fff8001fffffffffffffffe0000007ffc07ffffe3e0380ff1c0f8fe3c07c7ffe3fde77800c601c1f01e01ff800007f0f0b308cf8cf,0x91949232d6996b4c02248448d66348c1891919a32ce8c988c13193119248c912d665ac41961232cd659d32c0258cd612592460c4b230926b26720824805248160280350c058320c02c149a12dfd7a25fe856b711e156aff76ef70f0b308ca8ca)
  | 3 => (~~~0xffffffffffff8000000000000000001fffffff80000000000000000000000000000003ffffffe00000000000000000000007ffff8000003ffc00ffe00ff000007f8000381f87fff18000e001ffe0007c0f83cff3c00f00f0,0x60020c00020001018c03183008c03060060600c1003020306060c0604030200008000860020c0008000400cc01300040008030800c100000800318900008040011500009004490a80292484202804200329482a00891008910830000a505505)
  | 4 => (0x7fffffffffffffffffffffffff800000000000003fffffffffffffffffffffffe0000000ffffffffffffffffffff800001fffc00001ffff003ffff807ff8ff80000f801fe3ffffe001807f83c00fc0ff0ff0,0x1818c30318c18c60a306c60c1b300c0811818030208c0c0c08181058186c0c231b06300818430301061183010604185861b08400c302000c3044400049630daa680000154920025449004920d585480b501293d1550204526a53c00d40a50a50)
  | 5 => (0x0,0x0)
  | 6 => (~~~0x7fffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000fffffffffffffffffffffffffe000000001ffffffc0000007fff0000000fffe003ffffffff83fffc000fff000fff,0xe000fc001f000f803c00f80003c00ff001fe003fc00ff00ff01fe01fe00ff03c03f800f0007c000e001e000e0018006001c007f003fc03803f807e0e0e03f0cc8da64640000003a7724e000066b98f30023ffd62660c1e9cb39ebaa000fff000)
  | 7 => (0x0,0x0)
  | 8 => (~~~0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000003ffffffffff00000000001ffffffffff9807ffc000000ffffff,0x1f0003e001f000c00700001c0070001e0001c000f0001000200060007000001c003f001f8003f007e003f007e01f807e00f800fc001c0fc0078030707c01313248989a6e499000000000009946704ffc400281981021634c61455ff5000000)
  | _ => (0,0)
def quh:Nat -> qs
  | 6 => (6,1,3,0,0,6,0,zel)
  | 7 => (1,0,3,0,0,0,0,zek)
  | _ => q6
def qxs:Nat -> Nat -> Option (Nat × Nat)
  | 7 => qf 3 18 5 7 3 0 (qws)
  | _ => fun _ => none
def qyp:qx := (861,7,0,qqf,[(4,0,857,0,6,0),(0,1,348,0,5,0),(1,0,332,16,5,0),(256,64,541,0,5,0),(16,1,332,0,4,0),(17,0,332,0,4,0)],[[]],quh,qxs)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qz1:qi qyp (qt qja)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=2)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qrp:qc qyp 6 0 6=true := bOk 6 (by decide +kernel)
lemma qro:qc qyp 7 0 1=true := bOk 6 (by decide +kernel)
lemma qth:qp qyp 7 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qrp
  . exact qro
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zdg:qy (qo 861) (qa 861) 8 :=
  zh (hm0:=rfl) (g:=qyp) (i:=0) (hints:=13019128580) (qe qeb qot) qz1 qth (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qea := qh qeb 8 [(861,[]),(925,[118,130])]
lemma qos:zv qea := qd qot zdg (by decide +kernel)
abbrev qi8 := qea
def qwo (i:Nat) : Nat := 0x20000
def qwn (i:Nat) : Nat := 0x5900c8058000000000
def zef (i:Nat) : Nat := 0xbe99810
def zee (i:Nat) : Nat := 0xd460147d847f401f810
def zed (i:Nat) : Nat := 0x48ff
def qqd:Nat -> zi × zi
  | 0 => (0xf80000fffc0000000ffffe00001fffc0007fffc00007f0007fff00000001ffffc00003fff8000fffe0000ffff80000fe0000003fffe00007fc0003fe000001ffc1fc00fc1c0e03f070e00e0080e39ffc307ffc07f3f007ffff839c3398cdc2d8,0xb7ad56aa9bdd75b56cacadbadadab1b76f52d2b5b5b6afedcb52db5776abac95b5bb5b5a36b7eac95adb6ad296b5aed5f7bdb575ac5ad6f7535bb769badbffffe9ff1afe9e6f9bfa7cf36f36849207b42817d423d3d2884212439c7399cdc6d9)
  | 1 => (0xffffff00000007ffffffffffffe00000007ffffffff800007ffffffffffffffffffffc0000000fffffffffffffffff00000ffffffffffffffffffffffffffe1e01e01fe01f8fff807ffc7fff871c64003f9c003fffffff801ffe10c21f0f0fff,0x2108048813102000480809108092212442008020202429410200820204010801211012122424408010804080042004852221002108108420021100011080000a00600a4006028900143022128492048028144022818280421242104211090491)
  | 2 => (0xfffffffffffff8000fffffffffffffffff800000000000007fffffff8001fffffffffffffffff00000000ffffffffffffff0003ffffffff8000003fffffe01e001ffe0ffe00fe3ff80ff8fc7f81ff80031e7ffc403fc0183e3801f3c1cf1f31c,0xc201980320064619810130201300020004181b0606c0c20e0064006420cc30260602606040c0830d830d830320c0c80041061986008300421860380020108aa0008520a6a0052092804505442804f91152a11944466c1214a5940a3c0ca0a30c)
  | 3 => (0x0,0x0)
  | 4 => (0x0,0x0)
  | 5 => (0x0,0x0)
  | 6 => (0xfffffffffffffffffffffffffffffff800000000001fffffffffffffffffffffffff000000000000000003ffffffffffffffc00000001fffe0000fffff003ffff000ff8ffe07fffc1f80007fc00067c1c03e03fe0fe03e0,0x31e033c06780de0031c0031c00c40188031c00c70000880c780c7818f00138002380008001000e000e001bc006f01805c03e00310018800002204c031c2c644a000028c8a002ab290009a019202838c1e890cd6c44208c6c8d402940f60360)
  | 7 => (~~~0xffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000003ffffffffffffffffffffffe00000000fffffffc0000000fff00007ffffe000007fffffffc1ffc003fff0003ff,0x43e003c027800e00e3e01c3e01cf839f063e038f8070cf06f80ef805f01c1c0383c038307060c101c100c1c07070001860820383e1c1f046383c271c3e13156ad2a53000000034c4e9a4000d7fb0622ad5ee2b98880c5eb5a6bf5c0005f5c00)
  | 8 => (~~~0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000003ffffffffff0000000001ffffffffffff83fffc000000ffffff,0x7c000c0038007000fc001fc001f003e007c003f00000f007000f0006001fe003fc003fc07f80fe01fe00fe007f800e1f80fc03fc01fe00783fc0381fc01c19931d39cd31349d00000000000e6dfd7c33e170332030b07739372bfd6bf000000)
  | _ => (0,0)
def quf:Nat -> qs
  | 5 => (1,2,2,0,0,0,0,zef)
  | 6 => (3,1,2,0,0,3,0,zee)
  | 7 => (1,0,2,0,0,0,0,zed)
  | _ => q6
def qxq:Nat -> Nat -> Option (Nat × Nat)
  | 6 => qf 1 5 3 5 0 1 (qwo)
  | 7 => qf 2 10 4 7 2 1 (qwn)
  | _ => fun _ => none
def qv0:qx := (967,7,0,qqd,[(0,1,454,0,5,0),(4,128,835,0,5,0),(64,256,647,0,5,0)],[[],[135,98]],quf,qxq)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qzz:qi qv0 (qt qi8)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=0)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qrm:qc qv0 5 0 1=true := bOk 6 (by decide +kernel)
lemma qrl:qc qv0 6 0 3=true := bOk 6 (by decide +kernel)
lemma qrk:qc qv0 7 0 1=true := bOk 6 (by decide +kernel)
lemma qtf:qp qv0 7 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qrm
  . exact qrl
  . exact qrk
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zdc:qy (qo 967) (qa 967) 8 :=
  zh (hm0:=rfl) (g:=qv0) (i:=0) (hints:=26323452161) (qe qea qos) qzz qtf (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qh6 := qh qea 8 [(967,[]),(997,[134,81,65,114,49])]
lemma qoo:zv qh6 := qd qos zdc (by decide +kernel)
lemma zdo:qy (qo 639) (qa 639) 10 :=
  qal (m:=639) (cap:=9) (ci:=(32,0,607,0,9,0)) (hints:=16785665) (qe qh6 qoo) (by decide +kernel)
def qef := qh qh6 10 [(639,[]),(759,[84,115]),(887,[131,84,115,98]),(951,[134,81,114,50,65]),(955,[98,134,114,81]),(1011,[98,99,81,131,114,65])]
lemma qo0:zv qef := qd qoo zdo (by decide +kernel)
abbrev qjc := qef
def qww (i:Nat) : Nat := 0xc400000025800001900000006000
def qt1 (i:Nat) : Nat := 0x35ac00000030800000000000000000
def zer (i:Nat) : Nat := 0x277ac1301c6f43a7a80fdc01117f972802feb9401fa88a00
def zeq (i:Nat) : Nat := 0x948ba2c0dd21462e893174486a8a80ff803fd20fb88bfa00
def zb6 (i:Nat) : Nat := 0x21a27f
def qqh:Nat -> zi × zi
  | 0 => (0x1ffffc0000000000000000001fffff000000ffe0000000001ffc00000000ffff1ffc3f381ffc3f801f80700fff1f007f003807e703807001f71f0f7ffd8760dbf871c0c70017ffdc006fe1fc061dffe1f87fc137fdf7b8c70fe38c1f60e18,0xfff7dbfcbdbffbbdbff7dbff5fffdbff2f6fffeefdfbffffbffbdf3dbffefffffffbffebf7ddfff3fdddfcd7b6fffdfff7fddbfb7f7dbfb7b6df7ff5b7f7db6ea9bbb7ff7cf77b7ff5deeefabfeeffa6fafbddff607fdf7bdcf1fffddbf6de39)
  | 1 => (0x1ffffffffffc00001fffff001fffffffffff00000000ffffffffffffffff00f803e0383f03e03c0f1c0ffc70f81f1c781e3e3f07e3e3fc7ef763707801b8831c03f63107b007801ec0700ffff80600000007fe1b30c6249c366a4c8c6487f,0x526491282914912929649092045311120a4524445551496911200029149400000580160280d00e014050c05182038050c180c0a1301c0a11824f5775a7909b6ca988336d34b30878314c2608b5ae7f867879ccef60330c6248c164a488c44831)
  | 2 => (0x1fffffffffffffffe00000001fffffffffffffffffff00001ffffffff8000f001c003fc01c003ff01ff07f8f001fe07fe03fc7f803fc7f8f0783818001c0f3fffc7839e7c018001f007ff1fc061c01e0007fc134010038e7c8738f1078f9c,0x849800410021020002000224608402244008488000021200224c000021200290300040011400400089000802103000a60214014843001482109028801801000302430492ca4c118040b041300a000038828211101fc01001002883107103850c)
  | 3 => (0xfffe000000000000000000000001fffffffffffffffffffffffe00000000000f0001fffc0001fffc0001fff800fffe0007fffc007fffc007ff1f803fe0001ff03e0007fc1f8001fffe0007ffe0000188001f87800203e07c0f80f83f01f80fe0,0x1820e18e0e061c0e0c38e0c38918604083818100006060420400898e060724250001aa6c00009254000155980044960004ab680014a68004e405803fe2a22db07c9059241591242a9a0016cde0832e432d2ca6a5a003e0540f80502f00a80ae0)
  | 4 => (~~~0x1fffffffffffffffffffffffffffffffffff00001fffffffe00000001ffffff00000007ffffff80000007ffe0003fffffe0003ffff8001ffffe00000007fffffff9f7ffe007fffb83ff800fff003ffe000fff,0xe0c102003038203030410304000183870c0e0e089983838c38711230383848cada9a0000000164a2d59400000099293b5000000069492720001a7fc01544124e812126db6866415561dee010030451a4d2d3595a407c002bd000afc00156d000)
  | 5 => (0xffffffffffffe00000000000000ffffffffffffff80000000001fffffffffe000000007fffffffe000000000000001817e1e00000087fff800000fffffe000000,0xff0003f0003fc0003f8003f801e003f8000ff000e003fc003f801c003fc00f036322cc89a51400000000000000ee4dcda74d92720000000000133ad131878002000207ff7cf7791980d482602c0862a0e2e3999c606a9a000000fffdda000000)
  | 6 => (0x0,0x0)
  | 7 => (0xfffffffffffffffffffffffffff0000000000000000000000001ffffffffffffffffff800000000000000000000006017fe000000107fffffffff000000000000,0x1fc003fc0003fc001fc000e01fc000ff0000f01fc000fc001e03fc000700c8c4d31324a69b93b26e9a6e4e40000000000000000000000000cc52ec6783ffcfdbc780001008066030b0481d0301d471d1c6663801565feffd7000000000000)
  | 8 => (0x0,0x0)
  | _ => (0,0)
def quj:Nat -> qs
  | 8 => (4,2,3,0,0,5,0,zer)
  | 9 => (4,1,3,0,0,7,0,zeq)
  | 10 => (1,0,3,0,0,0,0,zb6)
  | _ => q6
def qxu:Nat -> Nat -> Option (Nat × Nat)
  | 9 => qf 2 16 4 7 2 1 (qww)
  | 10 => qf 2 16 4 7 2 1 (qt1)
  | _ => fun _ => none
def qog:qx := (703,10,0,qqh,[(2,0,701,0,9,0),(4,0,699,0,8,0),(24,0,679,0,8,0),(160,0,543,0,8,0),(0,1,190,0,7,0)],[[],[84,115]],quj,qxu)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qz3:qi qog (qt qjc)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=2)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qla:qc qog 8 0 1=true := bOk 7 (by decide +kernel)
lemma qk9:qc qog 8 1 3=true := bOk 8 (by decide +kernel)
lemma qk8:qc qog 9 0 2=true := bOk 7 (by decide +kernel)
lemma qk7:qc qog 9 2 2=true := bOk 8 (by decide +kernel)
lemma qn3:qc qog 10 0 1=true := bOk 7 (by decide +kernel)
lemma qtj:qp qog 10 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact (bM qla qk9)
  . exact (bM qk8 qk7)
  . exact qn3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zdk:qy (qo 703) (qa 703) 11 :=
  zh (hm0:=rfl) (g:=qog) (i:=0) (hints:=536879361) (qe qef qo0) qz3 qtj (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qib := qh qef 11 [(703,[]),(831,[135,50,65]),(891,[130,50,81,115,98,65])]
lemma qow:zv qib := qd qo0 zdk (by decide +kernel)
lemma zdj:qy (qo 735) (qa 735) 10 :=
  qal (m:=735) (cap:=9) (ci:=(64,0,671,0,9,0)) (hints:=553656577) (qe qib qow) (by decide +kernel)
def qec := qh qib 10 [(735,[]),(751,[84,115]),(1003,[99,33,129,115,82,65]),(1017,[118,130,81])]
lemma qov:zv qec := qd qow zdj (by decide +kernel)
abbrev qi9 := qec
def qwr (i:Nat) : Nat := 0x70
def qwq (i:Nat) : Nat := 0x26540f0000000010
def qwp (i:Nat) : Nat := 0x12c019000002d00000000088a0400
def qt0 (i:Nat) : Nat := 0x3b700000014002800000000
def zej (i:Nat) : Nat := 0x67a801829dd31
def zei (i:Nat) : Nat := 0xbfa884c600fd233846009ed829dd31
def zeh (i:Nat) : Nat := 0xedb0350738e8f279400002ff3ba63fe4c600bf8e098fd633847ed19c01fc84600
def zeg (i:Nat) : Nat := 0x3a948d324c5d3e9e70e3b4d970da5aed8c80ff4c7de33fd847fa00
def zb5 (i:Nat) : Nat := 0x2163537f
def qqe:Nat -> zi × zi
  | 0 => (0x1ffffc000000000000000001fffffc000003ff80000000007ff00000000fffe1fe1f8381ff1f000f870380ffc3c1c0f838e07c707007001dc1c53fff19605dfce45989eff9efee0003f87f007f97fffe07fe1f7ece7c1798e999adf60e18,0xb7af7b6acbdbabbbedbbedd5d7ffedd5cbdbabfbb77efbff6f5eeecfddbefffffff5fe9fd3cdff9fd6efc79be6fff3f5eefe3cf37e7b7db736ddebc42bdd1dfb57d4d655c91bd9ffaf5acfc87d24d17e999da5351ffece7db799ebb9adf6de39)
  | 1 => (0x1ffffffffffc0000fffffc01fffffffffffc0000000ffffffffffffffff00f00301c03f0381f078c07e3ff0e03c1f8c03fffe07c7e3fc7e5c206c200199c6600fc678e3fff300e100400ffff98e001e0003fe990082c861f0981fec6487f,0x20064200811001124032080081028800811001110524016440080004801400000500200800c0180502840180a2020040480008212018141102448284024009a94640504108121130841044002424011a090880111f9008288611010108c44831)
  | 2 => (0x1fffffffffffffff00000001fffffffffffffffffff000007fffffff8001f001c01ffc01c01ff80ff803f8f003fe00ffc0fc7f807fc7f8f9fc38fc001e1c7800e7860fcc01c00fe007ff7fc00180000007fe0360f04f181c8e1e31078f9c,0xc4c98c0c126230208100b1191a25311912623220004892098993000911202290b0014014d400c00a5808c80148300196004a405446802a8250997d68fc84b656b882ae96d34c42c10be092d55ac17e65b4b56f6ea060f047180c8e143103850c)
  | 3 => (0xffffe00000000000000000000001ffffffffffffffffffffffff80000000000e0001ffe00001ffe0000ffffc00fffc0000ffff007fff8007ff1e003f00001fe07fff07f80ff001fff00007ff800067001e1e07c0160300701fe0f01fc1f80fe0,0x1020030e000c1c0061c0060e04800602000c040000020400200046006070422000092a00000012000011228004454000094950009250004a402001700084100421901682cb085125000252280020098424210805f8300000540500bc0a80ae0)
  | 4 => (~~~0x1fffffffffffffffffffffffffffffffffff00001fffffffe0000000fffffff00000000ffffff80000007ffe0003fffffe0007ffff8000ffffe00000007fffffff9f7ffe007fffb83ff801fff001ffe000fff,0x60c1040038302030820c1810001c181c38303822670c38e0c1c488e183848cd5b34000000016a9394a00000009aa2e4aa000000724a4d20001debc02b101cfb1500d615c10910ed8f5ac0400c045166999da535007c007da000aba00156d000)
  | 5 => (0x0,0x0)
  | 6 => (0xffffffffffffe00000000000000ffffffffffffff80000000001fffffffffe000000007fffffffe000000000000001817e1e00000087fff800000fffffe000000,0x7f0007f0003fc000fc001fe007001fe0003fc003800fc000fe00f001fc00f066246d4c5191400000000000000ed3b3934e7269a00000000000a4c5b4c1e6000001107bef7ede64612630183904862a0e2e639c6604ba5000000fefef6000000)
  | 7 => (0x0,0x0)
  | 8 => (0xfffffffffffffffffffffffffff0000000000000000000000001ffffffffffffffffff800000000000000000000006017fe000000107fffffffff000000000000,0xf8001f8003fc0003f000fe000381fe0003fc0003c07f000ff000700fe00070098c99291a6269b4dce74e64d27400000000000000000000000015b3a0b3e09effbde2f801000200a80d9c020460b01d471d19c63980345afffabf000000000000)
  | _ => (0,0)
def qug:Nat -> qs
  | 6 => (1,4,3,0,0,0,0,zej)
  | 7 => (3,3,3,0,0,0,0,zei)
  | 8 => (6,2,3,0,0,6,0,zeh)
  | 9 => (4,1,3,0,0,7,0,zeg)
  | 10 => (1,0,3,0,0,0,0,zb5)
  | _ => q6
def qxr:Nat -> Nat -> Option (Nat × Nat)
  | 7 => qf 1 5 3 4 0 0 (qwr)
  | 8 => qf 2 9 4 6 2 0 (qwq)
  | 9 => qf 3 18 5 7 3 0 (qwp)
  | 10 => qf 2 15 4 6 2 0 (qt0)
  | _ => fun _ => none
def qhu:qx := (863,10,0,qqe,[(4,0,859,0,9,0),(16,0,847,0,9,0),(0,1,350,0,8,0),(2,0,861,0,8,0),(8,0,855,0,8,0),(320,0,543,0,8,0),(16,1,334,0,7,0),(28,0,835,0,5,0)],[[]],qug,qxr)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qz0:qi qhu (qt qi9)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=2)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qrn:qc qhu 6 0 1=true := bOk 7 (by decide +kernel)
lemma qk4:qc qhu 7 0 2=true := bOk 7 (by decide +kernel)
lemma qk3:qc qhu 7 2 1=true := bOk 8 (by decide +kernel)
lemma qk2:qc qhu 8 0 3=true := bOk 7 (by decide +kernel)
lemma qk1:qc qhu 8 3 3=true := bOk 8 (by decide +kernel)
lemma qk0:qc qhu 9 0 3=true := bOk 7 (by decide +kernel)
lemma qkz:qc qhu 9 3 1=true := bOk 8 (by decide +kernel)
lemma qn2:qc qhu 10 0 1=true := bOk 7 (by decide +kernel)
lemma qtg:qp qhu 10 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qrn
  . exact (bM qk4 qk3)
  . exact (bM qk2 qk1)
  . exact (bM qk0 qkz)
  . exact qn2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zdf:qy (qo 863) (qa 863) 11 :=
  zh (hm0:=rfl) (g:=qhu) (i:=0) (hints:=12901687553) (qe qec qov) qz0 qtg (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qh9 := qh qec 11 [(863,[]),(879,[84,131,98]),(943,[98,118,81,130,50,65]),(957,[118,130,81])]
lemma qor:zv qh9 := qd qov zdf (by decide +kernel)
lemma zde:qy (qo 893) (qa 893) 10 :=
  qal (m:=893) (cap:=9) (ci:=(4,0,889,0,9,0)) (hints:=13019128580) (qe qh9 qor) (by decide +kernel)
def qh8 := qh qh9 10 [(893,[]),(927,[98,118,81,130,50,65])]
lemma qoq:zv qh8 := qd qor zde (by decide +kernel)
lemma zdb:qy (qo 975) (qa 975) 10 :=
  qal (m:=975) (cap:=9) (ci:=(128,0,847,0,9,0)) (hints:=13438558465) (qe qh8 qoq) (by decide +kernel)
def qh5 := qh qh8 10 [(975,[]),(1005,[118,81,130,65])]
lemma qon:zv qh5 := qd qoq zdb (by decide +kernel)
lemma zda:qy (qo 983) (qa 983) 9 :=
  qal (m:=983) (cap:=8) (ci:=(16,0,967,0,8,0)) (hints:=26323452161) (qe qh5 qon) (by decide +kernel)
def qh4 := qh qh5 9 [(983,[]),(1013,[134,81,114,49])]
lemma qom:zv qh4 := qd qon zda (by decide +kernel)
lemma zc9:qy (qo 989) (qa 989) 9 :=
  qal (m:=989) (cap:=8) (ci:=(64,0,925,0,8,0)) (hints:=13555999492) (qe qh4 qom) (by decide +kernel)
def qd9 := qh qh4 9 [(989,[])]
lemma qol:zv qd9 := qd qom zc9 (by decide +kernel)
abbrev qi7 := qd9
def qwm (i:Nat) : Nat := 0x180000
def qwl (i:Nat) : Nat := 0xa6c00000141a2f10000001000060000001
def qwk (i:Nat) : Nat := 0x596020061988000070493640083000000000000000000000
def qtz (i:Nat) : Nat := 0xa900003000000000b200110000
def zec (i:Nat) : Nat := 0x47e65e884c600
def zeb (i:Nat) : Nat := 0x2808000ad705ad60bfa884c600dfa881c131bfa881c1319fe881c1319fa881c131fd200846339f9809dd31
def zea (i:Nat) : Nat := 0x873630203cd8a51e6c996f950cb205fe774c7fc98c01fe1c131bf8e098fda33803eb08c677e1c131
def zd9 (i:Nat) : Nat := 0x140e59660b2cb521965c9903fd31f78cffa00
def zb4 (i:Nat) : Nat := 0x22232ff
def qqc:Nat -> zi × zi
  | 0 => (0x1fffff000001ffc00001fffff00000000000000000007ff00000000fffc1ff1fc00ff8fc1c0fc38380ffc3f070f8e0e00e0e0e07001901e4c78cfff85dfcc459fefe7fe0243fe4007f007edffffff83c1d7370f39bd8ecdf70996c18,0xb6f6d6ef7ad6bad6b7fdd735bbfbad6d2d6b75edd6efad6eb7ffedadd6f7ffffffe9ff9ff1affafe9e6febdbe6ffebfa7cfaf6f36faf6f37b6d90926a4ac5ee84fdca548afee7da136afa68afd28813c533150aa1ff371f39bd9ecdf71bb6db9)
  | 1 => (0xffff00001ffffffffffffffffffffffffffffff00001fffffc007ffffffffff01e00381e01f0c0e01f8e03e3ff0e03807fc0f8fc7e0f8fffc7e90e27388b10006600fc663b004001fe3ffe007fff86e00000783fe5c24302031f00ec4399fc9f,0x2004844250841084204800211021084008420048840d084000908008840200000a00180600a08040060400c0a2040100148030302002021102490926a40812004640a0402b204401220a02003028011c111040221fc241020311008c41104891)
  | 2 => (0x1ffffffffffe00000001fffffffffffffffe000000007fffffff8001e001c01ffe0f00ffe00ffc03f8f003ff80ff00ff8ff00fc7f8f1f0383ff3e0007800c787cc007ffe383007c07fc000c8001f803c01007cbc1c1c8f107ce18f1c,0x758180d830024180490858602cc3006418058810040300b3905000100a42150a000c008520b00a6a00a6c0148300092804b004506b00542d090500809f7e422b8894d8ac40411ca1cf08dc34ec13a2166259adca00028bc1c0c8a1028e1870c)
  | 3 => (0x0,0x0)
  | 4 => (0x0,0x0)
  | 5 => (0xffffffffe0000000000000000001ffffffffffffffffffffffff80000000000e0001ffe0000fff00000ffffc00fffc0000ffff000ffff007ff1e003fc0fc00007fff07f80fff80003fc007ff800079001fe007c01a0380c01fe0f01f80fe0fe0,0x46000060000b80006e0060003700008000061000088000c2000012000c702620000410000054a000002890800524800005242000b252004a410000400ac40404a1805488d0c008036a1068a04000038422110881f8000c01280c01a00ba0da0)
  | 6 => (~~~0x1fffffffffffffffffffffffffffffffffff00001fffffff00000000fffffff00000000fffffff0000007ffe0003fff0000007ffff8000fffffffc00007fffffff9e81fff87fffb83ff001fff001fff000fff,0xc78000880018c000c70000002380018f800c7e0018f0018fc02609c018f80b86644a000000065328c8a0000000eaaeab290000000dc9c9a00012324000b560f1881007bfd44889065df5dccc08426860e263b9cc602800e94000ff6000efb000)
  | 7 => (0xffffffffffff000000000000000fffffffffffffff0000000001fffffff000000000007ffffffffffc00000000000180801ff8000087fff000000ffffff000000,0xf800e0f01c1f00e0f80118383c01c1f00e0f800e1f01c1f002384e0e1f004c0d56ad2ab2a530000000000000008d334c4ea49c9a40000000000faff3f60018850502b23532f1ee15c1061010100c45c699da6523407fd700000035e5d7000000)
  | 8 => (0xfffffffffffffffffffffffffff0000000000000000000000001ffffffffffffffffff800000000000000000000006017fe000000107fffffffff000000000000,0xff001fe000ff0001e03fc001fe000ff0000fe001fe0003c0700fe00070099931b4dd39c8a4d3134d3272740000000000000000000000000dcdbbff429f0635e3f800228170198008012060b017871d9c46338057ff16ad7f000000000000)
  | _ => (0,0)
def que:Nat -> qs
  | 6 => (1,4,3,0,0,0,0,zec)
  | 7 => (7,3,3,0,0,5,0,zeb)
  | 8 => (7,2,3,0,0,6,0,zea)
  | 9 => (3,1,3,0,0,6,0,zd9)
  | 10 => (1,0,3,0,0,0,0,zb4)
  | _ => q6
def qxp:Nat -> Nat -> Option (Nat × Nat)
  | 7 => qf 1 5 3 6 0 2 (qwm)
  | 8 => qf 4 19 5 9 3 2 (qwl)
  | 9 => qf 4 23 5 9 3 2 (qwk)
  | 10 => qf 2 15 4 8 2 2 (qtz)
  | _ => fun _ => none
def qht:qx := (999,10,0,qqc,[(0,1,486,0,8,0),(2,0,997,0,8,0),(32,0,967,0,8,0),(132,0,867,0,8,0),(320,0,679,0,8,0)],[[],[135,98],[134,114,81],[118,130,81]],que,qxp)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qzy:qi qht (qt qi7)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=2)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qrj:qc qht 6 0 1=true := bOk 7 (by decide +kernel)
lemma qky:qc qht 7 0 3=true := bOk 7 (by decide +kernel)
lemma qkx:qc qht 7 3 4=true := bOk 8 (by decide +kernel)
lemma qkw:qc qht 8 0 3=true := bOk 7 (by decide +kernel)
lemma qkv:qc qht 8 3 4=true := bOk 8 (by decide +kernel)
lemma qku:qc qht 9 0 2=true := bOk 7 (by decide +kernel)
lemma qkt:qc qht 9 2 1=true := bOk 8 (by decide +kernel)
lemma qn1:qc qht 10 0 1=true := bOk 7 (by decide +kernel)
lemma qte:qp qht 10 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qrj
  . exact (bM qky qkx)
  . exact (bM qkw qkv)
  . exact (bM qku qkt)
  . exact qn1
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zc7:qy (qo 999) (qa 999) 11 :=
  zh (hm0:=rfl) (g:=qht) (i:=0) (hints:=22028484865) (qe qd9 qol) qzy qte (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qh3 := qh qd9 11 [(999,[])]
lemma qoj:zv qh3 := qd qol zc7 (by decide +kernel)
lemma zdi:qy (qo 767) (qa 767) 12 :=
  qal (m:=767) (cap:=11) (ci:=(64,0,703,0,11,0)) (hints:=553656577) (qe qh3 qoj) (by decide +kernel)
def qia := qh qh3 12 [(767,[]),(1019,[99,81,115,130,65])]
lemma qou:zv qia := qd qoj zdi (by decide +kernel)
lemma zdd:qy (qo 895) (qa 895) 12 :=
  qal (m:=895) (cap:=11) (ci:=(4,0,891,0,11,0)) (hints:=12901687553) (qe qia qou) (by decide +kernel)
def qh7 := qh qia 12 [(895,[]),(959,[98,118,81,130,50,65])]
lemma qop:zv qh7 := qd qou zdd (by decide +kernel)
lemma zc8:qy (qo 991) (qa 991) 12 :=
  qal (m:=991) (cap:=11) (ci:=(128,0,863,0,11,0)) (hints:=13438558465) (qe qh7 qop) (by decide +kernel)
def qd8 := qh qh7 12 [(991,[]),(1021,[118,130,81])]
lemma qok:zv qd8 := qd qop zc8 (by decide +kernel)
abbrev qf9 := qd8
def qt3 (i:Nat) : Nat := 0x1800
def qt2 (i:Nat) : Nat := 0x1f90000281ba00000000034bdc9000324d40000510000000000000000c199c000000001f000000014c008084d6800000000002000
def qpw (i:Nat) : Nat := 0xb300000040b9000000020c23734800000000e7000000000f3000013000e9307a06000003438004320019000000000000000000754000000120000000000000000144000f380000083d68cf14c300000000000b140000000058a000002e00000000000000165000000000000000006b6003818000000000021791a000005c200087c00000fc9e134e8007a80009080004578c0000092a06900888520b84828009240380042522ce44188000000200180000800104000000000000020000080
def qpv (i:Nat) : Nat := 0x1d48012271a00000000000000011800a2bde00000002580000000000000000000000000000000068656deed7719a580144001e780118801c3800003920000000000001a4e56848be2be77b000520002e7d50820000000128000016b00000001340000000043000200000000008102000000400100
def qpu (i:Nat) : Nat := 0xc401f20000000000000000000067c802d601800a000000000001f094200400
def zcd (i:Nat) : Nat := 0x43f8baa658220141
def zcc (i:Nat) : Nat := 0x1600f8c3c40f843a0083dbef8530050000009feaa89061d14cfea659220141cfea658220141deea652420114cfe5ca99201418feaa89060574c7ea667720114c3f9dd96a2124c7e9dc9061121e7a88a7720114f69846449de22
def zcb (i:Nat) : Nat := 0xe3e1c912273f0f45064e59a8034810e0b88784227c02e30e2041c01600f0f6097465e49b8f81c47c397923e2e0d01f109f0281388584f8140a254d93a04c2c763b108ec778f92c2de23b6baf4be2110884be212fa8d46792f8ec8a3b108844206ce58a50ee5212803ff532402837ee995d222bfb4cae908d7fa65419def7d32a0a497ee9945e22dfd4c900a0dfea64805077f51040283dbe7750524efd3b9008a4ff66174486f7b2e90c895fd94486779fec9510ba4ff64a885c67fb2544283bf992201419fec8d10ba6fe60880507f6ae508c89bf97220141fdab8a829277d50a77847bda83114effb92420114ede90cef224ff261744867f930b92833fc985c524bfc48304a0cfea6480507b6cef224239fa7720114ed7224ef114bf65a884927bb27442e53f89061121
def zai (i:Nat) : Nat := 0x891b00f02a1600e12780b131e2c04c98f00fa24c45b050265c780b51267cb865e0926898cb606250d9d3509380b9b260c4c0b171a4d580b31326c9826b02e549815d12e2c04e811516c124a97324c1358173c6c0a58173e5c32e4972e4c12d8971eb89ab031366c9826b02e7c3a304b526cf8744b925e5b83ddf56cd714bb2cba726d8fa1679dbf65d76539263f8d62b87f15c28003ffa2141ffd82507ff5d121ffd72507ff5c524bfe885d2ffa2172bfe885c6ffa2141bfd87486ff61121fbd72913ef5c644dfd429df7f50677fbd414937f49d71dfd219dfef48644ff8805076f9de44df6778477b88a77fb611912fe20141
def zah (i:Nat) : Nat := 0x9264e035034f0d101649a2b4e1a98103ce74d01281a48ebaa044d2c50d306259f66c20560bc03feb97fd41ffa49ff486ff3bfbe44
def zag (i:Nat) : Nat := 0x720d6110208ff
def qnt:Nat -> zi × zi
  | 0 => (0x1f0ef83e1df7c3f1c03be00e000fbe07838077c1f0e01fc001c01c0002cd41ba1e0e1fd191fff89bffe3fff31ba9aa6d9dfff93ffc0e01c3bbffce60007ff87fc003fff3cfafffffffff03ffc0b9bce1ece7bd798dd6cdefb1c3c999adc60e18,0x1f8ebd2f9df5ebf5e9baf1af0c6fbed7ebd375f17af0dff38df6de18dacc453a565a93f590bde8b9fbe1fbd29b9da14dfdfefb3fb45fb5f33afddfea5cffc9ff4a64e8ce7009a79ef9bd35db65b9bce3ece7bd799dd6cdefb3c7dbb9adeede39)
  | 1 => (0x1fff003fe1f80381f83c01ffc1f03f0783f07801fffffe03c1f8ff83fc4e463a6670e0d0062000a4c005c003e3c8338fe0e00270007e37c43ffff062006001fffffd0030f0900000003f000fff21308600843061f0070f86270cc981ff26487f,0x504000280b00280681800a300200600809010001220460180504600484c453a565a9040002400a8c841c8428280210df4e213308052104028a192a2046041b30a60e04e000821969931051a6521308200843061100409862304810109244831)
  | 2 => (0xe00fffc01e0003fe003ffe0ffe0fc007fc007ffe00fc1ffc01ff1ffc1c9078038780ff1e67c000c7000600031c0e3cf1810003bfff8fc607c3001e7c007ffe7ff00100c3c12000000fc003ffc00000f88f01c181c118f00839f30e1e31c78f9c,0x209400400011600002204440280032c0020520054085400aa0888108018008080251ee7c82347108e1005280e84e0010020043984c69d8304245c0912964cb0081f101002ca2022c65a658a0000508f01c180c100a00800a20e143083850c)
  | 3 => (0xfff000001ffffc00003ffff0000ffff800007fffff001ffffe001fffe31f803c07ff03e0780000f80007fffc1ff03f01fe0003c0000ff807fc001f80007fff8000000c03042000fc000003f000c03f01300601fe0e1f01f03e03f01fc1f80fe0,0x6bb080201b5e6c00022f553010855b5800045ea5ab0112aaf400137383170058021302e1180040b84100c3e017f17b17fe6443d1001b39627c089ba2126d61810033e0c46ff1051cd119259245c02a01300600540e1f01f03e01f00bc1780ae0)
  | 4 => (0x0,0x0)
  | 5 => (0x1fffffffffc00000000fffffffff800000001fffffffe00003e0003ff80003ff800000fffff800001fffc001fffffc00000ffff800001fffff8000000002330c02403f03f000fc000001c001c007fe000fe001ffc003ffe001fff000,0xc6089a4888000000009ac95c951000000001d330934800002800008000003f5908080b943c04080199d8040ad20f000100fb5f31a111fea5c218086004048c07001870c708d34d141000001c00728000980014d0003dba001eed000)
  | 6 => (0xffffffffe000000000000000000fffffffffffffffffe0000000000003ffffc0000003ffffffff00000000001ffffffe00000000000fffffffffe000000000000000c030088fc000003f000000fe0001fff800000ffffe000003fffffe000000,0xb2dbd5b52004000004020000210e71e6726e6f39cc9b80001000002103930840000103b7bac1f111020001001d7fdef20b0880c2208defbfd75e2d4c6006020810831d807ff1c60860ce38e182d40001fa5000000ffbf60000037efef6000000)
  | 7 => (~~~0xffffffffffffffffffffffffffffffc000000000003ffffffffffffffffffe000000000000000000ffffffffffffffffffffffffffc3ffcfffffc003fffffff000001fffffffff00000000003ffffffffffff,0xdcede639d38f3249373799c9b9c00000000804010002000020000042017fe7f77f7fd80008310400a011a20ac6607b1f52df07fbc270080064600000804801100303a02f8ffc30d38d30810a34ffffae00000000067f5eb2ff5c000000000000)
  | 8 => (0x3ffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000002fc000c0ffffc0000000000fffffffffffffff00000000000000000000000,0x68f7a7fdecfc08453e0646bc1f3c0fe00000080090042c0360000000800011001004602c00023b800e38e30e20c20c382bd5fe05a8d7abf00000000000000000000000)
  | _ => (0,0)
def qqs:Nat -> qs
  | 7 => (1,5,5,0,0,0,0,zcd)
  | 8 => (11,4,5,0,0,6,0,zcc)
  | 9 => (38,3,5,0,0,9,0,zcb)
  | 10 => (25,2,5,0,0,10,0,zai)
  | 11 => (6,1,5,0,0,8,0,zah)
  | 12 => (1,0,5,0,0,0,0,zag)
  | _ => q6
def quw:Nat -> Nat -> Option (Nat × Nat)
  | 8 => qf 1 5 3 5 0 1 (qt3)
  | 9 => qf 8 41 6 9 4 1 (qt2)
  | 10 => qf 26 122 7 11 6 1 (qpw)
  | 11 => qf 17 81 7 10 5 1 (qpv)
  | 12 => qf 5 29 5 8 3 1 (qpu)
  | _ => fun _ => none
def qaq:qx := (1007,12,0,qnt,[(0,1,494,0,11,0),(8,0,999,0,11,0),(64,0,943,0,11,0),(128,0,879,0,11,0),(2,0,1005,0,10,0),(4,0,1003,0,10,0),(32,0,975,0,10,0),(256,0,751,0,10,0),(12,0,995,0,9,0),(66,0,941,0,9,0),(132,0,875,0,9,0),(160,0,847,0,9,0),(264,0,743,0,9,0),(320,0,687,0,9,0),(0,4,865,138,8,0),(0,256,647,104,8,0),(140,0,867,0,8,0),(328,0,679,0,8,0),(1,0,460,34,7,0),(2,4,865,136,7,0),(8,4,865,130,7,0),(8,256,647,96,7,0),(32,256,647,72,7,0),(128,4,865,10,7,0)],[[],[118,130,81]],qqs,quw)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qxm:qi qaq (qt qf9)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=4)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qn4:qc qaq 7 0 1=true := bOk 8 (by decide +kernel)
lemma qjp:qc qaq 8 0 6=true := bOk 8 (by decide +kernel)
lemma qjo:qc qaq 8 6 5=true := bOk 9 (by decide +kernel)
lemma qjn:qc qaq 9 0 7=true := bOk 8 (by decide +kernel)
lemma qjm:qc qaq 9 7 30=true := bOk 9 (by decide +kernel)
lemma qjl:qc qaq 9 37 1=true := bOk 10 (by decide +kernel)
lemma qgl:qc qaq 10 0 5=true := bOk 8 (by decide +kernel)
lemma qgk:qc qaq 10 5 15=true := bOk 9 (by decide +kernel)
lemma qgj:qc qaq 10 20 5=true := bOk 10 (by decide +kernel)
lemma qgi:qc qaq 11 0 2=true := bOk 8 (by decide +kernel)
lemma qgh:qc qaq 11 2 4=true := bOk 9 (by decide +kernel)
lemma qll:qc qaq 12 0 1=true := bOk 8 (by decide +kernel)
lemma qpp:qp qaq 12 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qn4
  . exact (bM qjp qjo)
  . exact (bM (bM qjn qjm) qjl)
  . exact (bM (bM qgl qgk) qgj)
  . exact (bM qgi qgh)
  . exact qll
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zbw:qy (qo 1007) (qa 1007) 13 :=
  zh (hm0:=rfl) (g:=qaq) (i:=0) (hints:=13438558465) (qe qd8 qok) qxm qpp (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qfa := qh qd8 13 [(1007,[])]
lemma qmo:zv qfa := qd qok zbw (by decide +kernel)
lemma zbv:qy (qo 1015) (qa 1015) 12 :=
  qal (m:=1015) (cap:=11) (ci:=(16,0,999,0,11,0)) (hints:=22028484865) (qe qfa qmo) (by decide +kernel)
def v8 := qh qfa 12 [(1015,[])]
lemma qbn:zv v8 := qd qmo zbv (by decide +kernel)
def qp7 (i:Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def qp8 (i:Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def qp9 (i:Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def qqa (i:Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def qqb (i:Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def qua (i:Nat) : Nat := 0x202e0
def zfl (i:Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def zfj:qs := (2,6,7,0,4,3,0,zfl)
def zfk (i:Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def zfi:qs := (25,5,7,1,4,9,0,zfk)
def zcn (i:Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def zci:qs := (156,4,7,5,4,12,0,zcn)
def zcm (i:Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def zch:qs := (183,3,7,8,4,14,0,zcm)
def zcl (i:Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def zcg:qs := (32,2,7,8,4,12,0,zcl)
def zck (i:Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def zcf:qs := (4,1,7,5,4,8,0,zck)
def zcj (i:Nat) : Nat := 0x17e2b6526070604013ff
def zce:qs := (1,0,7,2,4,0,0,zcj)
def qqz:Nat -> zi × zi
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
def qq0:List vp := [(1,0,510,0,12,0),(0,1,460,50,8,0),(2,0,509,0,12,0),(0,2,440,69,8,0),(3,0,508,0,9,0),(2,1,460,48,7,0),(4,0,507,0,12,0),(0,4,369,138,8,0),(5,0,506,0,8,0),(6,0,505,0,9,0),(4,2,440,65,7,0),(2,4,369,136,7,0),(7,0,504,0,7,0),(5,2,440,64,6,0),(8,0,503,0,12,0),(0,8,227,276,8,0),(9,0,486,0,8,0),(10,0,501,0,8,0),(12,0,499,0,9,0),(8,4,369,130,7,0),(4,8,227,272,7,0),(14,0,497,0,7,0),(10,4,369,128,6,0),(15,0,480,0,4,0),(16,0,495,0,13,0),(0,16,486,9,10,0),(17,0,494,0,11,0),(16,1,460,34,7,0),(19,0,492,0,8,0),(16,4,353,138,7,0),(21,0,490,0,7,0),(21,2,424,64,5,0),(24,0,487,0,11,0),(8,16,486,1,9,0),(25,0,486,0,8,0),(9,16,486,0,8,0),(27,0,484,0,5,0),(11,16,484,0,5,0),(24,4,353,130,6,0),(29,0,482,0,5,0),(26,4,353,128,5,0),(32,0,479,0,12,0),(0,32,94,385,8,0),(32,1,460,18,7,0),(1,32,94,384,7,0),(35,0,476,0,7,0),(34,1,460,16,6,0),(36,0,347,0,8,0),(39,0,344,0,4,0),(40,0,471,0,8,0),(49,0,462,0,8,0),(48,1,460,2,6,0),(50,1,460,0,5,0),(56,0,455,0,7,0),(64,0,447,0,13,0),(0,64,189,258,10,0),(66,0,445,0,11,0),(2,64,189,256,9,0),(67,0,444,0,8,0),(66,1,396,48,6,0),(70,0,441,0,8,0),(69,2,440,0,5,0),(74,0,437,0,7,0),(74,4,305,128,5,0),(80,0,431,0,11,0),(83,0,428,0,7,0),(96,0,415,0,9,0),(96,1,396,18,6,0),(98,1,396,16,5,0),(128,0,383,0,13,0),(128,1,332,50,7,0),(3,128,344,36,6,0),(132,0,379,0,11,0),(4,128,347,32,9,0),(133,0,378,0,7,0),(134,0,377,0,8,0),(132,2,312,65,6,0),(133,2,312,64,5,0),(136,0,375,0,9,0),(128,8,99,276,7,0),(140,0,371,0,8,0),(132,8,99,272,6,0),(138,4,369,0,5,0),(144,0,367,0,11,0),(152,4,353,2,5,0),(160,0,351,0,11,0),(160,1,332,18,6,0),(162,1,332,16,5,0),(164,0,347,0,8,0),(36,128,347,0,8,0),(172,0,339,0,5,0),(176,1,332,2,5,0),(180,0,331,0,5,0),(192,0,319,0,11,0),(198,0,313,0,7,0),(256,0,255,0,12,0),(258,0,189,0,8,0),(260,0,251,0,8,0),(264,0,247,0,9,0),(256,8,227,20,7,0),(8,256,151,96,7,0),(268,0,243,0,7,0),(260,8,227,16,6,0),(273,0,238,0,7,0),(280,0,231,0,8,0),(276,8,227,0,5,0),(288,0,223,0,9,0),(256,32,94,129,7,0),(32,256,151,72,7,0),(257,32,94,128,6,0),(296,0,215,0,7,0),(40,256,151,64,6,0),(304,0,207,0,6,0),(288,16,198,9,6,0),(273,32,78,128,5,0),(56,256,135,64,5,0),(320,0,191,0,11,0),(256,64,189,2,9,0),(322,0,189,0,8,0),(258,64,189,0,8,0),(324,0,187,0,7,0),(324,8,163,16,5,0),(321,32,30,128,5,0),(388,8,99,16,5,0),(168,256,23,64,5,0),(224,256,23,8,5,0)]
def qx9:List (List Nat) := [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def qu3:Nat -> qs
  | 8 => zfj
  | 9 => zfi
  | 10 => zci
  | 11 => zch
  | 12 => zcg
  | 13 => zcf
  | 14 => zce
  | _ => q6
def qx8:Nat -> Nat -> Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => qf 1 3 0 9 1 4 (qua)
  | 10 => qf 17 61 5 13 5 4 (qqb)
  | 11 => qf 124 434 7 16 8 4 (qqa)
  | 12 => qf 137 475 8 16 8 4 (qp9)
  | 13 => qf 26 148 3 13 5 4 (qp8)
  | 14 => qf 7 47 1 10 2 4 (qp7)
  | _ => fun _ => none
def w8:qx := (511,14,0,qqz,qq0,qx9,qu3,qx8)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
lemma zaa:qi w8 (qt qaa)=true := by
  simp only [qi,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,qk (d:=5) ?_⟩,qk (d:=3) ?_⟩
  all_goals simp only [q8]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
lemma qr5:qc w8 8 0 2=true := bOk 9 (by decide +kernel)
lemma qln:qc w8 9 0 12=true := bOk 9 (by decide +kernel)
lemma qlm:qc w8 9 12 13=true := bOk 10 (by decide +kernel)
lemma qj4:qc w8 10 0 6=true := bOk 9 (by decide +kernel)
lemma qj3:qc w8 10 6 32=true := bOk 10 (by decide +kernel)
lemma qj2:qc w8 10 38 32=true := bOk 10 (by decide +kernel)
lemma qj1:qc w8 10 70 32=true := bOk 10 (by decide +kernel)
lemma qj0:qc w8 10 102 11=true := bOk 10 (by decide +kernel)
lemma qfr:qc w8 10 113 32=true := bOk 11 (by decide +kernel)
lemma qfq:qc w8 10 145 11=true := bOk 11 (by decide +kernel)
lemma qjz:qc w8 11 0 4=true := bOk 9 (by decide +kernel)
lemma qjy:qc w8 11 4 32=true := bOk 10 (by decide +kernel)
lemma qjx:qc w8 11 36 19=true := bOk 10 (by decide +kernel)
lemma qjw:qc w8 11 55 32=true := bOk 11 (by decide +kernel)
lemma qjv:qc w8 11 87 4=true := bOk 11 (by decide +kernel)
lemma qgp:qc w8 11 91 32=true := bOk 11 (by decide +kernel)
lemma qgo:qc w8 11 123 32=true := bOk 11 (by decide +kernel)
lemma qgn:qc w8 11 155 1=true := bOk 11 (by decide +kernel)
lemma qgm:qc w8 11 156 27=true := bOk 12 (by decide +kernel)
lemma qju:qc w8 12 0 3=true := bOk 9 (by decide +kernel)
lemma qjt:qc w8 12 3 14=true := bOk 10 (by decide +kernel)
lemma qjs:qc w8 12 17 15=true := bOk 11 (by decide +kernel)
lemma qjr:qc w8 13 0 1=true := bOk 9 (by decide +kernel)
lemma qjq:qc w8 13 1 3=true := bOk 10 (by decide +kernel)
lemma qn5:qc w8 14 0 1=true := bOk 9 (by decide +kernel)
lemma qtq:qp w8 14 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qr5
  . exact (bM qln qlm)
  . exact (bM (bM (bM (bM (bM qj4 qj3) qj2) qj1) qj0) (bM qfr qfq))
  . exact (bM (bM (bM (bM (bM qjz qjy) qjx) qjw) qjv) (bM (bM (bM qgp qgo) qgn) qgm))
  . exact (bM (bM qju qjt) qjs)
  . exact (bM qjr qjq)
  . exact qn5
lemma qu4 {prior:Nat -> Nat}
    (low:∀ q,qy (qo q) (qa q) (prior q))
    (geometry:qi w8 prior=true) (checks:qp w8 14) :
    wo vq 14 inputs.toFinset := by
  have noRun := qaw (g:=w8) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt:zn w8=vq := by decide +kernel
  exact tgt ▸ noRun
def qp6 (_i:Nat) : Nat := 0x4a5600049000000000
def qp5 (_i:Nat) : Nat := 0x5940002a66ae110a19800000000000000000141fc2e068001d8c865500007ca11d80000000000000000000000010c81b0000000000004668000000000a531680000054b7818000000000000000000d460a000000000744800000000014854811800025f0b000000000000555800000000000000000000528f26f2c80000000072400000000068b80000040700000000025080000041a0000000000000000000000000007248004a180008300029f80035180000000000050c0000000006c380000019be0d6c780074580000032291859f71ea1a8006120006a300028e80000058a800000000597f850000963d20007ad0c000031c00050780000000000000000000000000880000000029d0006170000000000000003290a838e00000000008f62d80000491c8000003a38000000000000000000000000002ab80071300000000000078f8000000000aa0000000000000a07cf0000000004a2000000000000000002000000000000000200a110000006530000000000006cf889800000627000000000000000000000000000783d208000002278000000000000004caaa100000000002af0580000000000000000100048400000000000042b08d8000000000000000005d280000049900000031539e000309000000000000688000000000000390741113ae9800418aac00000000000000000000041280000010280000000000045c0000000000000000000000d55801158000000000a980c02010000c02000000402040000000000200400020000404000080c0000000040002000000000
def qp4 (_i:Nat) : Nat := 0x5191e04000000c348001220000251e0d80000000000000000000000000353e4a5f328000000c290000000000000000000000000000015d40000000003a04000605dbd8002cf480c00079b8001403000000188a0009bcb1d000000014c307c00167f00052140000001a7000000025a000000000118d0000000000000000000226073ea1c68980c9e06000000000173fe038000000000c1980000000000000000000000000000000056aa4380000000003877e100000000002a10000000b1d0000000000d9be65400192982609ec001447a0df0c0d3200092a597da8081683800000730170003a6c000c37000000000098560e800000000000000000000000000003aca00000000000016a7000000000000000000004a000000000000000000000000000000000000000064b3868003e7451ba0a000314c000000000000184900000008820a439924e3cd5793c11800000000033f3121d2a12d000000000111600000000000006b9500400000030c4a31454000000690b012000a07b5bc00008212e000000033b61f10d404241150aa94e850b4400034700017a70003270001d1d3342557e50000000293c001792f0841daa856a0999b0b788840b42d8000000263000000020e0000000002a281a0000400000000000052440018200004d4b92c0000000000000e3b0002068000000b46800000014a0000002425272000000160a00000000020b0177d02000005e000ca28000000000000489c00105100032238c40000000176d4287902cc1b653dd1f000704ed166730000000d00478ab0800243c000533000000000042b0000000000000000000000000000000011007290000000000012b8b98d600022f703b8c2e9a2448000000000000623bad0000000015c0010759896870062d691478000001fa1000000000062400000004d8f2b6338000000d8f00000000000008c011540000000000000000000a4900000000000007a0c00000000000000000006aa0003c32000000000152847dd4b800000194381600000000000000000000534dbc0e51a8d506cc48a74001846d1580000016710000a40000a4300020280000000000001c69e7700011bd494000000590000171e00015240000000005db09440006bb00034f9a0d430360800000000034d489c64d0000001607a3c31ed08a90c000000402091400001f80000046930007c640700400014010000001804008010100000001014000040200c040140003406008000100000002004050000000000000000100400001000010000200400000010040903001018020040000006000040040100c0200007
def qp3 (_i:Nat) : Nat := 0xb25330637a8c8980000000000000000000000005b8000196000000000a1c000000000cbe000ba300000000000000000028700054000062f000e38500000a0d0004463080000af62d000000029000a420000000000000002b6c34580b43000000000e14000000000c10d0c31eec683539000000000000000000000000000000000000000000000000004163173bf4400000049400000078978400071f000000000e8a000000006a02000821000000583000000000000000000000000000000000c3d8b71a0000000000000d26000000dc200000000030500000000000011d0000000000000000000000000007a5000745b2cd150000000000005190000000c7420611000000000000000000785000000000000000000f2a68e000a01228000000000000e3c0000006473040000000004921aab2b59d00000000001b000000000000a13c22000333000116000000027599000ca700000000041700000000000090e5a60000004c5000000000000000000000000000000db5ab300000000000000000000023900000000000000000048d00072e923000991000000000000000000212000000000000f0a00000000000000000000073260300013f00000071ae241b1000d09e0f39a000f0bf0741800093aab000000000000000053600000000000000000073e0000008c30080000000000402020080400010080c0002010040200000000802008040002000000004
def qp2 (_i:Nat) : Nat := 0xc100000000000000019900000000000000000000000000000000000035000000000000000000001ce00d180000000000000000000000000000000003200000000000000000000018000000000000000000000000150000032ee0007480000000000001d3000000000000000000000000000006e000000000000000000338000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028002a80000003164400000000001c0000000000000000000007680000000000000000000000000000000000004c000000001e5000000000000000000000000000fb800000000000000000100
def zcv (_i:Nat) : Nat := 0xfa50fb46889563388a11e736558454a02582f366996095260551bb640c6095260551
def zcu:qs := (4,5,6,0,0,4,0,zcv)
def za6 (_i:Nat) : Nat := 0x848200000000000003120c28048b0f0e19878a0b024588040000000000000000084c38704000030f0e1f888b910800000000e4b8c10000061e1e3c20000084040000311c405c7878f0f1e183820000050c1a10001860400000005980a1f82050126e03838207e080e6020c029740e13c11e80e1f823d01c3f046e1d85e0d80480d005fe3ed7d0f8def3d97a8f3de53c5780eeddb3a771cdfdb334d67cce59a32f654c959031b62cc4586307604bf57c2e95b4b55682cb58cadd4f28f514a154027b4ec9c53625349c9252223f4608850e217424834ff1f93e87bcf51d13846ccd219532062cc31772d058caf159294514a013b26c4c4780cd12c1cc2802d0011ffaed5a02531cfdc44ad01298e3fe88568094c73f71131404a63ddb9562202531e7dd111101298f37e88954094c78ff444ee04a631ffaec0a56531cfdc44052b298c7fd5b02a994c63ff5d814c4a639fb8880a62531cefcaa0531298e5fe77029894c7bb72ac44c4a63fd59553260531eeecab4cb0298ff6655889814c7fa72ab0499263dd7956994c9318ffab60527290c7fd5b029894c63ff5d8149ca439df9540a4e521c7fd100527290c7fc0b569394863fe05b149ca431ff56eaa4e521cefcab5527290f37e88955394863ff5d814aca439f78cc0a56521c7fd109501298c7fc0b629594871ff44554aca43cf7a2233565218ffab60531290c7febb029894873ef19814c4a439df9540a62521deecab5526290fb768895531487daf444ab19a439df9552a02531c7fd10052b290f3ee8888a99547de744467112a36fb02d8254981d7bc6605304c0eb7e5502982607fa72ac67113031ff46c0a625328ffd76053129967f611029894cbbe719c454caa3fd99561160932f6ed112ac229947febb4680960b3ef19a3404b059df9551a02582cfec229d012c177d6338440960bbbb2ac2204b05ddd95611a6582feacab19c22c1777655845894cbdaf444aa99263ddb95622a6531e6fd112ad3298fb6e88956224c71ff4425404aa3df38ce2202551e7dd1111012a8f7769954981547fab19aa4c0aa39df9540aa6531cfdc4405532a8cfbd4b029825463fecd814c12a3ff18ce2260551efac674cb02a8f7e622a65815479fb4cb04c0aa39f78cc0aa6551b7e816c1302a8fbc5824c9814c73db08a9404b05ed96095260551fe8cab19c4508fbc6888ce22847db3444ab11423e75a22778ce11
def za1:qs := (93,4,6,0,0,11,0,za6)
def za5 (i:Nat) : Nat := (if i<1 then 0x1cbea591296924c85e3b91a18b344ae1e10b582fc0b5ff6fb77b9bcbddfaec274cb9c1c7ce0c6ed367dac8d2967732f1914c58617aff5784b905aaac4559aaa453da90142e9e54d9a5e127a90b468229d0d88313ff9f10f1274e3899b3cd2865030a9744b3e56d29d940097848121e900872236819b0c345b62b214489144141cf0ca056423c0e305401b4076000ffb88939547ff53260551dff029894c6ffc0a5e531bff029594c6ffd8a4c951ffb609325477fe994c951dff61c094c6ffc0a60951bffaa9825477fe9960951ff78cd825477fc0a56531fdf955294c6ffc0a4a531fdf95532607fde3354981effa2132547bfe8854931fdf955824c7ff55260531fdf955894c6ffc0a62531dff4c8095477fd8202551dff549894c6ffc0a4a551bffaa939546ffd8a4a551dff4e5295477fd894a551ffd60529546ffeaa4a551ff78cd29547bfe884a551bff02939547ff5814e551bff4e9295477fd8356521bff0293960affc0a46582dff029894877fc0a4e521bff029534877fc0a56521ff760d534877fd854e521ffd61531486ffeaa54d21effa21534877fc0a62532ff78cd85487f7e5560d219ffaa9894c73fe884e521cff609894c67fc0a565219ff629594877de3356521ddf955394877ee2262531ddf955894c75fe77625319ffaa939487fd532605319ff62939487bf58260531dfda65814c7fe622605319ff56939487fcd824c931fdd955814c7df677605319ffaa9594867fd8a02531dfb888094c777e55025319ff568094c75fe77025319ff4a8094c73fe8802531edfa2255487bde888cd219ff029594c7f5e558cd21dfd4c5894867feaa56531efda21314877ee2256531fdd95531486ff6aa4c5219ff029894c777e5562521df78cd894867feaa625219ff029894873fe8856521dfd605594c6bfeaa60981ef78cd82607b7e5560981ff38ce22607f6e5588981fd795633607dde778cd819ff029894ca7feaa62532dfd845894cafeeaa60932ff9845824cbf6e5560932aff02982607bf68884532f9f99a554cbb7e8895532fd79563358a7fd1a025829ff4e80960b7f61102582df78cc0960a7fc0aa6582dfd8469960b7de33a6582ff58ce1160bf765584582fdb9562258ff7655845329ff4e809547f5e554c931ef7a21324c67fc0aa6531dfb88a994c777e55a6531d7f9de994c73fe88a6531fdb956224c7bee8888931edfa22554c79fe889dd319ff4a8095467fc0a4e521dfb888095477de994c931efb60932607bde888cd71efba2222547fce3388951df78ce995477ee22a65519ff02a99547fd63360551ff9889815477f69960551efd60981547f755260551efb609526077de3302551ef3a223388bece668ce22e7da2277847bd6888ce11f759de33847f56558ce11ef9a2222847fc63388a119ef5280960bf665588a11 else (if i<2 then 0x538a2cf1d39a45166129d51660ca62ba886094ea88a9d511054214f1d3d98227043c2a8733094f0d40343080362bc88f00126644aa30f0bd9836643e223170ae9f91202a574fc89001695d33224144aa999120984828e0d0e54223c5720c3e0e00146e0e431e43600a0c1e060701f55e0e03088aae43838061858d0caaf0709800b19ab0ca78a38380c21e2b90607068622363e23906170686283e4185c16050c486c06138314051414c0e0a520c5a7e438380618a0c0b607048619049a5423e0d0c161933031fc10cc18ad5e0e13000a282d8640e0884146617041306230b1fc111b020c60f613832d0b14222ce0e3f20c3141f08c0e0c2c828c230b830b28781811c7f040ac2c220598461303830b30302bc1c7b03081b3c4d87c18592abc161e03565a7f058780d5943c0c0d8471fc1a16111c104e1301ab2e0013c167d0c0a6c7f044542c2028d80a7f058619959aab8f607070819302701c1a7c12566c0706094f0c814c13070543611e0e3f21434e438380a1824b90e0e028609289b0028e0e4286163854380fe0e4301433d54150fc870587803d0b82090ca18b40e088451030b9b834004c189c1a00260c467f070740c315abc1c1d030c5617070609c3169fc1c1b018586305421c1c7e02866c050c51c195084d15c7e038343109a87c180084125e0d0e00218a1783148050c125e08644f06254187c1c0650b5561f0700c4ca1aaac3e0e03285c07070784d36a4c150786782d0c1e00e15087059f80c1870ed0c1f064e4e0e0c1127260307c10b0a0426e0e0e4e052027838393814b95e0e0306052e3dab50e0e03066a07070784d3694cd5a27070194282b82cfc1610446a0613831425018790e082a2860682849c1c2088cc0c270616192c3222c2e0e121666161382c08588cc2361e3f830b0c9b18d5c7f0681843657214061f071e193e4721c1a163d866c850987c1a063c46706657838460058c1e06057834fc0610e22c230383072e1281c105450a21e09010c092b0f8382c064f4060ce3f2bc1c830e807c633f2bc1a0610ccf864478384c141cf0c87f0708c08399be1e06274380f0d84535c1c1611982e08260c4e086581958317838203c189c103b0086092f043298831382862c0148170b60b08cfe0c1cfd5e853f8380619a9fd561f0700c436439f42e0b0e806e153f21c1e030cd4fe630b8384601b99d1a7f05858437579f90e0d01866e67559fc1a0610dd5e860011832f339ed5e0d03086f897befddbed6f5ffaa3d23e71f28f90fc47e0cef6777bb8fdb0ec3f557a6bd0ce7af35796bc9ee3f719f87dc1edff6f9f78fb9edbf6d5767db27d83ebc35c5ab9d55ea7751fa8ad356973479a1ccfe674f3559a5cbe654f21f8d4c4ce1330237d6bc95d5ee276d8b5359d2c735feae1d646abf524a7dd30291d44aa10cfbe74536799 else 0xa7861809150c38f6f8aab8f10780e20493c41c0a53c6306604c607089c422818784e2838141234786a38f15471e28a64b180924629d92a8814a0a8a53c74ec7c60324858244ce0c81474ca963c74cc7883814678c3c07133a241814102a10a88c174f170c9c521))
def za0:qs := (168,3,6,0,0,13,0,za5)
def za4 (_i:Nat) : Nat := 0x90704342c18f405323485a1c7a0608c829d0306116014bab1e498286164475383c1424072863a8609441938b193f060ca09c84c850982168014642840ac10b2236667e0c220039b561305002c28c810782b10c583c14054862e668a7e0c241039f050e01beacb830086d55651c4c0955c184804fab4c9e0c121c035501e325705021150c3c9f1e0e33832b208680a07cfd1c1820636667c1604260839e4c2b0a423f03062d0d31799a31f8285087248bcc8f42c1844044591666ac7e0a042208c17330b0702102d199059f8309800e70bc20a8fc0c1063898f6147c860e021a333463f04650a10e260b9985810982168d5cfc18043ab36667aae0c240559f33553f061202ace164599aa57829e09009d5cf90c109804338e666aa7e0c0421c2c7333550306105114da3098306854a7a6d584c18340a53d38b6ae827e0c041a29c87573d4306020d0139fa1aa0b83064e819d5cfd083c1273d367aae0c1c04254a29b553f060e0212a51aba1830087286d543c180449435361aae260c04a1f335706011250c37999eab830900787ccd14fc184823c9e627e0c2414050224f3f060a010e80e4f8212800c583d5cfc14086349c1e127e060c31e0f3f47050a18d079f8280850c61ed5d08fc180433c3e667cae0c2201c9c6f574304010c51199ab9f8281086ccc24fc1c08436667e8e0a1421b333d0b061100d9f85218380866d5c34fc1c48036ae7a1e0c0221b573f4306010cce3851e878380887841c11a032fdc7cfbda9e6af00765ba59cc2e34703b729b3ad70691b399962c5c613afa973ab6058dab59522a5450ba74932a95048da37914285440b9f68f2a75838d9b58d2264c3079728b0a55028d937895246c2178fa875a3801a58c385b22a413388a83ca1b00bd85182220dc05381c807a000ffec3a63ffd824c7ffaa498fff62531ffeb9b03ffd1960bffa72c17ff5e531ffeaca63ffd29547ffa5298fff54981ffe99303ffd39547ffb0a90fff60d21ffea9a43ffd835c7ffa64a8fff60951ffac0aa37fc095477fd1098fdf95531eff3ba63fee224c6ffd3298dffa6551ffac0a637fd894c6ffab298dff02531dff44243f7e55487fbc6690ffd4c521bfec4a437fd39487fba6498fdf95563ff7112c7fde3360bfec22c15ffa6582bfe04b05f7e5558bfbc66b16ffa2132f7f33265f7e554cbfec22995ff56521fef19aa3fde335c77fd10b8eff60981ff711303fde33607efcaac0f7f9dd81bfec4a65fee22547fdb04997f988a11feb19c23f7655847becef08efda2211fe719c45eee6688b7dd11117b799a33
def zaz:qs := (72,2,6,0,0,13,0,za4)
def za3 (_i:Nat) : Nat := 0x18c24d00241069509eacfa1040033d59e9a08300114a13558712080287260e7c2810431e6139f04202008101e64fa304202393173210f81042226559f04200567633e103830021f8c3843e044827ab3e1c18800d327c2830021a8f9661c799b05cd3d400ca2505e0bc00ffd63ffd82ffd62ffd32ffd81ffd71ffd51ffd31ffd21efe66fde33fee22ff611
def zay:qs := (13,1,6,0,0,10,0,za3)
def za2 (_i:Nat) : Nat := 0xc4f0c200110fff
def zax:qs := (1,0,6,0,0,0,0,za2)
def qnz:Nat -> zi × zi
  | 0 => (0x4dccc7c4a2dee672f2dea2082467efb63ba2adcfdbe12efea820eaa15cd76cc87a341824f7b6863269db47174a27fffffffffffffffffc003ffc003fffffc003def781f7bbe07b83ef83c1eefbc1d87bdf7bbdde0f030f7ddf7bdeddd7b83830,0xc6893fd57dfd727feb7d19f7f98e7fe6db9c4ff7fedfece3fdaff16fdf79d7b3ef32fc777ffdfd5bf77fddfbeafeaeeaeeaeeaeeaeeaeeaeeaeeaeeaeeaeeaefffff81ffffe07f83ff83c1ffffc1f87ffffffffe0f030ffffffffffffff83838)
  | 1 => (0x34016d74d438f135ce925f3fbe8e17b5b8db1b67a5f9f4814135d2eeb3f4314fd93c08e7eb23361e47dffb6b7ad4000000000000003ffc000000000003ffffffe0f80217c020fc04208443f0fc03e088410884421105117e1f805f05e7c04879,0x408121042000000cc20418c280800002d018440430030cc1b008c0045d700430c01040603201144841515db0004208e08e08e08e08e08e08e08e08e08e08e08fe0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038)
  | 2 => (0x806eb5465011185759d2c4cdac8c8d2e6be81b7768680a041e0bf915facf27e74f309ef07bc3b7fe4419d99c324c000000000003ffc000000000003fffffc000421085f883ff8800410884220844497c027c3e042ffc0f84010be21e4088bfd0,0x8464000101c84e001820820006504da00000005004b0701c0804001302828300000b80810114c000080402060400c50c50c50c50c50c50c50c50c50c50c50c50000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0)
  | 3 => (0x532a30488f499c39cb23b627c2a789ee8af83f341f919f7a319e163a6f13b9ed1bc3357ad3f79f46cece6633c368000003ffc000000000003ffc003ffc00000084210821084110888ffc0044fffe00109f90089ff20802085ffc800897ffd080,0x11831ac50020146210514420828100c340c088a290503004140a0000009008c0a10034040820060830a910020001a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000)
  | 4 => (0x5b184cc33297c4ee682b04eee4ee13be03c1d2bf176771fda3272707bfa2ff3bbdc0ff1c1c65ccdc3307166e1d34000000000000000000003fffffc000000003ff0011fffc020013f21009ff1088027fe4003fe840102fffe210001ff9110102,0x820002410cf95221c2500000d0002040ca004071121848a2b4a9010a9a504021212034051e34650070540c808aeaa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000)
  | 5 => (0xabccdedc25eecab1d459531ac953a109d62da6eae3a08a5f8cff148269895e97813acff167591d13fb5c75e384c8003ffc003ffc000003ffc0000000000000010842204210842121042110882110947fffffc00080204fffffffffe000020204,0x8154404a82205414400030000542410044053268c20010809002103108310002060012504640214244100400406c06c06c06c06c06c06c06c06c06c06c06c0000000000000000000000000000007fffffc00000000fffffffffe000000000)
  | 6 => (0x8d5570ff38a23e462f760008b2255ed730bad502dc3abda45b389b8eabbe191d2feca3c4f0f9e1f16ee9f44538bbffc000000000003ffc0000000000000000021084408421084243ffffff004001007ffffffffffffff0100400040102000020,0x167898b95fe227c3240b06050f3ae21d0d441ab0024c9116010610d90208b084028b0a050126a81282a6004cf4003703703703703703703703703703703703700000000000000003fffffe000000007ffffffffffffff0000000000000000000)
  | 7 => (0x3cccd357975f9b69ac7b42663e6100cdd38c5649577da3da5f8b690d6e001f4d4ecb47e70c649f722f14ff644398000000003fffffc000000000000000000003ffffff0002100003ffffffffffffffa108211000044004208821085000002400,0x1102aa9a221110da220945fc48878042cc0a2fa05042010202e2d30c60213ce9a284140e5ae2189cc301a4313863383383383383383383383383383383383383fffffe0000000003ffffffffffffff8000000000000000000000000000000000)
  | 8 => (0x39203cefeb8ac927f6d5233b0a756adfaf77a2b2f892012df8f773fc240ada23f1cbe9625c529ea4a6f1fe44c49fffffffffc000000000000000000000000003fffffffffffffffe084220008220004210422111088288411042108004240000,0x40874202a01190081a30a09890410902009284041020008882b00b0664460040054010988259108420502a8002ebc03c03c03c03c03c03c03c03c03c03c03c03fffffffffffffffc000000000000000000000000000000000000000000000000)
  | _ => (0,0)
def qn0:List vp := [(132,0,891,0,11,0),(16,0,1007,0,13,0),(160,0,863,0,11,0),(320,0,703,0,11,0),(66,0,957,0,11,0),(10,4,881,128,7,0),(322,0,701,0,9,0),(34,0,989,0,9,0),(8,16,486,1,9,0),(40,256,663,64,7,0),(256,8,739,20,8,0),(10,0,1013,0,9,0),(256,0,767,0,12,0),(0,16,486,9,10,0),(128,0,895,0,12,0),(8,0,1015,0,12,0),(2,0,1021,0,12,0),(4,0,1019,0,12,0),(64,0,959,0,12,0),(0,128,859,36,11,0),(12,0,1011,0,10,0),(32,0,991,0,12,0),(8,4,881,130,8,0),(8,256,663,96,8,0),(164,0,859,0,9,0),(260,8,739,16,7,0),(32,1,478,0,9,0),(0,4,881,138,9,0),(0,8,739,276,9,0),(2,1,508,0,9,0),(0,256,663,104,9,0),(0,1,510,0,12,0),(130,0,893,0,10,0),(2,4,881,136,8,0),(4,8,739,272,8,0),(384,8,611,20,7,0),(128,8,611,276,8,0),(72,0,951,0,10,0),(0,64,701,258,11,0),(388,0,635,0,8,0),(32,256,663,72,8,0),(68,0,955,0,10,0),(264,0,759,0,10,0),(6,0,1017,0,10,0),(128,256,535,104,8,0),(36,128,859,0,9,0),(40,0,983,0,9,0),(288,0,735,0,10,0),(384,0,639,0,10,0),(192,0,831,0,11,0),(136,0,887,0,10,0)]
def qu8:List (List Nat) := [[],[81,130,118]]
def qrf:Nat -> qs
  | 9 => zcu
  | 10 => za1
  | 11 => za0
  | 12 => zaz
  | 13 => zay
  | 14 => zax
  | _ => q6
def qu7:Nat -> Nat -> Option (Nat × Nat)
  | 10 => qf 2 9 4 7 2 1 (qp6)
  | 11 => qf 35 357 9 12 7 1 (qp5)
  | 12 => qf 69 531 10 13 8 1 (qp4)
  | 13 => qf 32 329 9 12 7 1 (qp3)
  | 14 => qf 7 227 8 9 4 1 (qp2)
  | _ => fun _ => none
def v5:qx := (1023,14,2,qnz,qn0,qu8,qrf,qu7)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qxo:qi v5 (qt v8)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=5)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qvb:qc v5 9 0 4=true := bOk 9 (by decide +kernel)
lemma qml:qc v5 10 0 7=true := bOk 9 (by decide +kernel)
lemma qmk:qc v5 10 7 32=true := bOk 10 (by decide +kernel)
lemma qmj:qc v5 10 39 32=true := bOk 10 (by decide +kernel)
lemma qmi:qc v5 10 71 22=true := bOk 10 (by decide +kernel)
lemma qmh:qc v5 11 0 10=true := bOk 9 (by decide +kernel)
lemma qmg:qc v5 11 10 32=true := bOk 10 (by decide +kernel)
lemma qmf:qc v5 11 42 32=true := bOk 10 (by decide +kernel)
lemma qme:qc v5 11 74 32=true := bOk 10 (by decide +kernel)
lemma qhk:qc v5 11 106 8=true := bOk 10 (by decide +kernel)
lemma qhj:qc v5 11 114 32=true := bOk 11 (by decide +kernel)
lemma qhi:qc v5 11 146 22=true := bOk 11 (by decide +kernel)
lemma qmd:qc v5 12 0 9=true := bOk 9 (by decide +kernel)
lemma qmc:qc v5 12 9 16=true := bOk 10 (by decide +kernel)
lemma qmb:qc v5 12 25 16=true := bOk 10 (by decide +kernel)
lemma qma:qc v5 12 41 11=true := bOk 10 (by decide +kernel)
lemma ql9:qc v5 12 52 16=true := bOk 11 (by decide +kernel)
lemma ql8:qc v5 12 68 4=true := bOk 11 (by decide +kernel)
lemma ql7:qc v5 13 0 4=true := bOk 9 (by decide +kernel)
lemma ql6:qc v5 13 4 9=true := bOk 10 (by decide +kernel)
lemma qr7:qc v5 14 0 1=true := bOk 9 (by decide +kernel)
lemma qpr:qp v5 14 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qvb
  . exact (bM (bM (bM qml qmk) qmj) qmi)
  . exact (bM (bM (bM (bM qmh qmg) qmf) qme) (bM (bM qhk qhj) qhi))
  . exact (bM (bM (bM (bM (bM qmd qmc) qmb) qma) ql9) ql8)
  . exact (bM ql7 ql6)
  . exact qr7
def qxg (_i:Nat) : Nat := 0x2803a00
def qxf (_i:Nat) : Nat := 0x714000000000000000000060a000cd000338000001168106500048940800000000b07c2c0000000000000000000000000000000000000000007c0000000084400000daa00000381000000000000006180061800000000000001e780000000046c0000002f81c0000000000000000000000000000000000000000000049000e320004ec41001d14000000009200000000043640000000178000000000000000000000000000000003080000008834700000180800147000003c7800000000000000000000000000000000000000001ca800001d7206000001a4c00000000000010000000100000000
def qxe (i:Nat) : Nat := (if i<1 then 0xb3e000308513042928600000000000000001a213bf6d2b8e800000050ec8a80000000002a3d84a0000000000000000000000000020574fc0000002000000000000000000000000070a00000019310000000000048000444400195e00051e40000000000000000073b36000082d24d0000000000000000215c00000000008d0000000523800267600000000004b2000000000381e66200000000017454b108b380ea6f00005d607f74c80180000000000000205c5e000000000000050d8138001d040000000000000000331800205a07fa008000000000d1180000000000000003ae381d00000000000000002dbb8a2000000000000000039080000000007b7adc083200000065940000000000000001b07000000282185a00000029000006bd8000001b540340000000000000000000180d0000000000000abc00036ec878c1e8000000000b1d09c60a621f00045dc0000000000000a2907af2fa9c00000000000000cd4b0400000ac001342f2e74cc0000000006cc9c05329d348000000000000154ac1600071330a8001b181070000000000d97882400000000000000000000000000001875d12f0c4000000000000000000000000000000002ae8000000000004147400125b000000369e000f0378c18c2000ca750480008170000000000000000000000000033f0000000604000000000000008800000000000005068000000000000000113651ad8f14f60000000000000c390000000000c4cb0e1990001276a9a0000e1400019d00000000000003ce00000000000000001b3e920000000000000079b400000000000000000000000000000a46a3000000002330000002a12000000000000000000000000000000000000000000000000000000000000024ac0000002960000000000000000000000050b80019500004da2e58c430000000000215a9500000000005830003e4e000d110000000000e9280000007490000000001a49000000000094692780000000000000000000000000281400000000000000004720000000000000814000000000000058d800000011c000000000000000000000000000000000000cb5000000000000000000000000000003cdc000c91000142603e0000002e36000000000000000000061f6e860000000000000000000000000055361950dc000000706000000000000000000000000000001ab80000000002a5600000000038aa00000000000000002120000e49d26c0f2c008ee000000417988be6b533f60400185d00000000010500000002ab0c4420d80000000000000000000000000112e823e4153378a4001a4e0080000000008000000101003004000000000c0401001000020100000002000000000000000000000080000000000000000300c020040000000000000000000400004000000000400 else 0x58618804ca00000000000)
def qt7 (_i:Nat) : Nat := 0x3590a00000374000000000000000d5800000000000000000000000000000000e14000000000000000d2000000000000144ea400f288f000000024200353100009980050c10001070b400000000600000000000000000000000d30000034b000000014e0000000000000000000000000000004180000000000000005700000000000029100000000000cc000000000000000000000000000001b129000000000024d00000000000000002400000000000000000000001dc003b0000000000000000000000000000000149d4000000000000000000000000048000003a8000025500000003f80000000000000000000000000000000019a00000000000000000000000000000000000000000034100000000000000000000000000000
def zgb (_i:Nat) : Nat := 0x2887d468898897487d46879a2121
def zf7:qs := (2,4,5,0,0,3,0,zgb)
def zga (_i:Nat) : Nat := 0x38a180840004142083060d801020a100000000000020903100041b086c21b08400002c2180063d1085c1a02f37738192c45b2c558a751275309347225086d34168983e180ac4c210e038015f9091c910afa8c8e48856f524724427ea334424157d591c940af6848e490c7f1e6884863f8f2b42639f5715a131cfaa88f098f754c9714c6afab2392831fc89889718fe3cad09947f624724433ea323c4451fd191e2228fe44c44ba4fd4647858f3bac63c2651fd191e1638fe948f0b1c7d4647858e3b91319ae58be6652072c9f2aa90396678cd481caf9272044455e5191e2229f844c229047d4647888b36c22a40e51be9952072
def zf6:qs := (33,3,5,0,0,9,0,zga)
def zf9 (_i:Nat) : Nat := 0x180842a302101430a00085461a50800a1c4041a280100b1c042858c0a1e1470e4420880150061a06306041a20287101438a90349862041a10808205074830286101438814946242a387181064430f18843c50214006928f1470f190a3808c10148880820549870042209150e18c0a3c40858715243910c0a445421058c10000a10801581ac081040005284168c558060a3050d286b02981022851428a180a5a4a325086093294405062a10c182093029814c0d18687120c789242038fc3c48625086843421a10c24042e18596843421a10e28608000020020047870406c2c241c02000050863c38203644a2017150e48f0e0dc3872e061910e02130c2c9421a10d0863c38370e1cb010b098616580c30b1d0e20838222a1c90b09461a48584a30825086843431828005151c072f2059687130c743898638083221d1c504844072439e7ea7967426ee6ba68667261e5ca5564e246e41a3c639231e2ca2762221ee19a1861320fe08a035fe1fcdf79f05ed1e9de29dd5da1d2dcb9c65c11bddb49b15aa1a4da399e597191d8e989588186d8598258117fd7c979576174d7397256f169d6295f55c158d5595455114dd4a94153c136d3192e529125d2291f51c114d0d9045010fdcfa8f74ec0e8ce58e24dd0dbcda8d94d80d4cd38d24c10bfcbe8bd4ba0aeca589a493089c86883480074c6986245d053c4a84143e03ac3583042501dc1680f4003fd06120ff9304837f58d72fed21482ff4e072bfd181caffa2120dfd764c6ffa2131dfd541cb7f1c941dfd325c77f5d531dfc725037f88971bfd684c2ffa2132dfd764cb7f5d532fdd634cb7f5c932bfc784cbf74c530bfd684cbf758d30dfd635c6ff4e121bfc784877f5e121ff531487fb1c921bfd28442ff4e110ff9204437f1c910dfd72486ff4e120dfe225d37f5d121bfe88486ff5a131bfc784c7fd54531bfe8858eff1e163fdd324c77f5c931dfd73487ee55140fb941503fa88940ff211503de95540bf958503be99940bf928442fe52110ff1414437e5c910fea22443f68cd10fba44443fc06120bf938482fe52120fe9214837e5c520fe942483fa88930ff211483fa88920fda33483ee91120dfa77482fe56130fd9314c37e5c930fd9534c3f658d30ff2114c3de95530efa664c37e5cd20dbe445ca7f1e1539fc7858f7d84573dee225cf5f95573cfe665ce7f1e154df6115d37b88974d7e555d2fe4e110fe622847f58ce11fb644847fa02222dec7888bf38ce22fae4488a7f1e222f5e558cfb799a33f3e559133f999749fc784877b1c9219fc784c77d5c5319fc785077b88971dde335c76f911719fc784ca7f1e142dec7250b778cd729fd181ca7f4e0729fd481cb7d84472dde331cb6f91072bf9081caef52072df6115cb7b88972dbd7450a6f52072
def zf5:qs := (131,2,5,0,0,12,0,zf9)
def zf8 (_i:Nat) : Nat := 0x80405e4c71411e2901796064c609100490cb901433c00597243166202e2d1c98c11c690808a3e405161a60028b9218b30d21963e4050cf97263202c1403c013941448640f1a00f95941438889427282c98e01e010ca0a2431678194164862cc832e486400101820b00c832e48641e08005090cc08005090cb072c0c98cb00865c80a19a01017922e30478024865c80a19c002080e2972ca13931c0344870086517931824a0c98e292864cf9331aa1a3f0782e2daab1f5c4ab13b24744c7dceb1a72fe55c940f217825032821001ff443fe907fd30ffa81ff487fe98ffd41ffa65ff1cbfea9ffd63ffc45ff553fea17be44ff241f78cffc987f940fdc457f5d2feb8dfd73ff2217f1cafeb97f611
def zf4:qs := (27,1,5,0,0,11,0,zf8)
def zc5 (_i:Nat) : Nat := 0x12852465ff
def zc4:qs := (1,0,5,0,0,0,0,zc5)
def qs6:Nat -> zi × zi
  | 0 => (0x7b56cd930e3f882cff1f09ceae67b1eb62a75afcdcff9fb0963bbd8d6754e9b80e9fe3f424575b5e4562c8136f439ca4312efeac3646e21b8825f4c3423b08d7ae9abad23eb6df5b01dd40ad5b7f8001fc07f0003f888f83e0891112894f9f0f,0x3962508220100c01383102c004c0000665888a035a000505e006c004011404a0800308239080040948403200800300aa200401220086a020220502000c82ac488610100209001145a40800028c491224489122448800781e000000000079f07)
  | 1 => (0x82891f45f430edefdab21fa4cdd97fe6fe272a48d4ae46582e3e54c453309f634d9a7ddd5c679fb0746b21759ed19616faee9bea99b65dfbed19dcd5153a9aaa6c867fd3e739aff1a640594ec49200000000001ffff8788e2178f02e17388139,0xe848004490741100c8306681c58192e998062155825dc4200028801719001a81d0c5096100012899620280093273c02044170f801810847c248200022232513b100e20118220d6e9a01830bc122a66cd9b366cd9b378780e0078f00e07380018)
  | 2 => (0x3c5f36dfb9437ed10cd892b2cbaab7211db3957ceacff8ff2f363874a8a5bf17c342d7ebdb393539ba9fe6e9a6bc3b0aff66cd5f0df15ad8f735b7037b7e792b577d68ef4899edf5f67cdb3b9e8e00fe00000fffc01111144f9022f47a113ff0,0x200420020340801000010200640c0002a040081920104490c20428244640280200821c32241060011074800400001290a8302401610001805d353481080804460095003004280205a1034048c009122448912244800000078000f078001fe0)
  | 3 => (0xe7a1139ffd9aebbbe7535db64cd6c757c2ef919bbf4567e3c9c2cf226eafb6c8ed51f63690bf884f969bdd973dffac7748dbf6b4f84b5cd7d8cfb9d5a5f1f49677fbedc33b1f01dba23644d51aa1800003f80fe000227ff00222ff4024bfe240,0x288000808400272521231e58e08901c7741d0224420a088820140a0702100353091334e1888044046442003928d2208844000812701c08060000004828c082e8a0b142680e82020ca0488c020515b264c993264c99007ff00000ff00003fe000)
  | 4 => (0x98ff8fa87cbdbcd796ad8c1fb6ff73a53ec8437b03353b345299b8be94ef5deabfe2c3e9e69196fb74242f261733b25b95976f8ae6cb7e24e7f6bb17f4cfbe1c814d544fefc6faee8cbfc74935e5800003fff000007fa22087ff44007fe24402,0x5429482018ca58020c0061820212f61881a260410000042101810128b42420a470284a10066288120100d88641080215197d24e908638469a447259704064102410e9812c121c4c10423432192204c993264c993267f800007ff00007fc00000)
  | 5 => (0xdf4adaad538d6bd275f26dffb9688c78f96c39b700abedfedc66cf515a0953dd78ad5ba69741f4f78d3b30556811f9e37840e2db7dc9edfd855a752b769ad34092069f22d16445b32b54e8be31e1ff01fc0000000044444917ffffff80040804,0x40280214448201012050474321900b000100205c0009102300c501182860010011020a5d0064190003104402e0c406c01828082405200009014107002631811243141e2d9444482824800b7a84000e1c3870e1c38700000007ffffff80000000)
  | 7 => (0xafc5f6e78648f58e93aee9dfd204b936f5d5bdb44a1ef206b05c7b5fdf901bbd58664855173838fd6f2f3aff38e2c9d927323b6b03e5217b7fcab3fa0da43be51523c72d8a689abc5c3ae69da9497ffe00000000007ffffffc44888940001080,0x21391c1984c0642048f208c100320138c461903a6126b106100aa87431090c7e04475804091a012d0ef8028123b780422404790d20409925882804150043428200a0050488a81055242f4050315f0e1c3870e1c387ffffff800000000000000)
  | _ => (0,0)
def qs7:List vp := [(4,0,699,0,8,1),(32,0,671,0,9,1),(1,0,190,0,7,2),(24,0,679,0,8,1),(160,0,543,0,8,1),(2,0,701,0,9,1),(136,0,567,0,6,1),(14,0,689,0,5,1),(0,16,166,9,6,0),(4,8,163,16,5,0),(4,128,539,32,6,1),(1,16,166,8,5,2),(16,0,687,0,9,1),(0,8,163,20,6,0),(0,32,30,129,6,0),(0,128,539,36,7,1),(1,32,30,128,5,2),(6,0,697,0,6,1),(40,0,663,0,6,1)]
def qyn:List (List Nat) := [[],[115,84]]
def qvi:Nat -> qs
  | 6 => zf7
  | 7 => zf6
  | 8 => zf5
  | 9 => zf4
  | 10 => zc4
  | _ => q6
def qym:Nat -> Nat -> Option (Nat × Nat)
  | 7 => qf 1 6 3 6 1 1 (qxg)
  | 8 => qf 12 161 8 11 6 1 (qxf)
  | 9 => qf 58 595 10 13 8 1 (qxe)
  | 10 => qf 12 217 8 10 5 1 (qt7)
  | _ => fun _ => none
def qbw:qx := (1215,10,0,qs6,qs7,qyn,qvi,qym)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zad:qi qbw (qt v8)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=4)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qyh:qc qbw 6 0 2=true := bOk 7 (by decide +kernel)
lemma qs1:qc qbw 7 0 11=true := bOk 7 (by decide +kernel)
lemma qs0:qc qbw 7 11 22=true := bOk 8 (by decide +kernel)
lemma qsz:qc qbw 8 0 1=true := bOk 7 (by decide +kernel)
lemma qsy:qc qbw 8 1 16=true := bOk 8 (by decide +kernel)
lemma qsx:qc qbw 8 17 16=true := bOk 8 (by decide +kernel)
lemma qsw:qc qbw 8 33 16=true := bOk 8 (by decide +kernel)
lemma qsv:qc qbw 8 49 16=true := bOk 8 (by decide +kernel)
lemma qsu:qc qbw 8 65 16=true := bOk 8 (by decide +kernel)
lemma qst:qc qbw 8 81 2=true := bOk 8 (by decide +kernel)
lemma qoc:qc qbw 8 83 16=true := bOk 9 (by decide +kernel)
lemma qob:qc qbw 8 99 16=true := bOk 9 (by decide +kernel)
lemma qoa:qc qbw 8 115 16=true := bOk 9 (by decide +kernel)
lemma qss:qc qbw 9 0 13=true := bOk 8 (by decide +kernel)
lemma qsr:qc qbw 9 13 14=true := bOk 9 (by decide +kernel)
lemma qvf:qc qbw 10 0 1=true := bOk 8 (by decide +kernel)
lemma qtt:qp qbw 10 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qyh
  . exact (bM qs1 qs0)
  . exact (bM (bM (bM (bM (bM (bM (bM qsz qsy) qsx) qsw) qsv) qsu) qst) (bM (bM qoc qob) qoa))
  . exact (bM qss qsr)
  . exact qvf
def qxd (_i:Nat) : Nat := 0x18000
def qxc (_i:Nat) : Nat := 0x3340028000c4cbf0005d00000bb991c200000000000006d8000000689d6ac9000000000000000e339000002e006d40000000010e0000003940000000014fb9800006900000000000000000000003cc000800200000
def qxb (_i:Nat) : Nat := 0xeaf9a00157c000000000000013a0014e0df80000172e2d000000000000000002c40000000000000000000000000000000000000000000000000000000000009c6002da000a20000000009b08c887000000000004470000000000000000000000000000005180000000000000000000000000000000000000000000000096400000001f72b00000000000008d00000000000000000003bee60000000001538f0000000000000000000000000000842000000000000000000000000000000000000000000000000000000000000000000001c58000000000000000000000000c84000000000000000010a001c5400000000000000000000749da4c000000000004a284d828000000033080000089c0000000000000702e500000000098c00097800001a81c38000000000000000000000000000000000000000000000000000000000001694e194f00000000000000000000000000000058026a000001d200000000000000000000000000000000000000000000000000000000000004c800000003568000000000000000000000000c9a0000000000176c001ac000000000000000000000000000000000000002670000000000000000000184000789f5800000000003d1000000000000003ae000000370000000000000000000794000000001e4222000000000000000064aca94cc00000f3e000006c900086c000000000000029692e00000000000003c78000000025e8000006980000000000000000000ea80000000000000000000000000000000000000000000000000001a92d585e00000000000a90000000000000000000000000000000000000000000000000000000190640800000000003b90000000000000011400000001618cf00000000000000d06c10000007800026980000000000000000000000000008b80000000198800000000000000000000000038c0017400000000148c000000010480000000000000000000000000000000000000016c00344800000000000000000038e00000000000000001b7400000000000000000000002000000080000001000000040000000000000040000000000000000000000
def qt6 (_i:Nat) : Nat := 0x79b1654000000000000000000000000000000000000003d8000064e3800000000000000000000000000000000000000000000000000000000000000001efe6f8400000000110000000000000000001f5000038a00000000000990018800000000160000000000c100014000000000000000000000000000000000000000000000000000000000000001b1000001800000000000a380000000000000000000000000000001e30000000002800000000045c000000003a60000000000000000000000000
def zf3 (_i:Nat) : Nat := 0x87b4aa994e071
def zfz:qs := (1,4,5,0,0,0,0,zf3)
def zf2 (_i:Nat) : Nat := 0x40c200000081841030c0c20040c208186c410000010a8020c4bfb1aca7a29d988a857769645f514c3e302b2621130500eea39a6290c7f62473486bea3239a439ec780a131ee63985098c7f4a4784c6bba5239a633ed29a21318fe9c8f0a8c7f4a4785863fa723c2c31fd391e1218fe9ca5038e7b0a5381c73ba649c0e31fe994e0718fe9c8f0a965f54c7854a3fa523c2a72fd69a21539beacd10b0c6f5247858ab3a923c4671bd491e233
def zfy:qs := (24,3,5,0,0,8,0,zf2)
def zf1 (_i:Nat) : Nat := 0x20e884001a28284100068800344001b043000d88c3245c90b0c20218a9214941c50e4831618b8610006d10c02284031146360080430a1a2c4021000d83a820006880036220c803502010c3d108802001b503008a100430802285861000d100430800200010020c311100418a8820000164a22200a885442a21510a8841150c4a1a40001150c1a4a4a30a2c1c9544516883441a20d104802002008818c11707104a2050000401000043c408987251e412870f203494715128b1848a888983452c145c1a2c315162e0ea228b4414583a889251068830c4a03084c325c80126412c20093209404790024b0848687450124322c20e883e33bbf62e9bce38def6dc3b5363eb2d2ba233de66c938d30be0abeb782e9daeb335d2afd52a7b4c289cfe9d335263cb293b24245c869031d237c5a88b0e219c2e85309207c027eafa1edbce782ef1cbb9271ae21b1b56652c7187b025eaba171ade582af147a8a50aa0139a6e4d295127a3242a7e0e99a62f25309f91a21a4006d8b61221d02782a01a003df54d52bfe884cbfb58932bfd58486ff5a132bfd584caff5a121dfe331c7fd4c521fed524877f58c71dfd621c77f4c871dfc734877f1cd52bfd680c6ffa2161efd62587fb0a131bfe885477f1cd51f7d52546ff56131bfe884c6ff5a131fdd534c7f74c931ff5614c77f1e131bfd580c6ffa2163bfe8854effa2162efd6358aff4e121bfe8854bfc84510fea22443f68cd10f7a55443f64c530efa66442fe4e120fe921483fa58920ff211483f68cd20f7a55483be99920df8714c2fe42031ff2114c3fa88930fda334c3de95530efa664c3fa889509fc78487f68cd50ff211583fa889609fc784c6fe4a1109fd681cf7d84473dee221cf5f95473cfe661cf7d1e211fe622847f58ce11bf938443bd99a119fc78847f38ce22f6e5588bbb99a22ddc788cfd795633ede668ce7f1e233f7655847771cd319fc785467f1e1619fd281c67f4e0719fd581c67f5a071dee221c67f56073d7e551c73f998719fc784ca7f1e1529fc7858a7f1e1539fc7858e7f460739fd281cf778cc71
def zfx:qs := (101,2,5,0,0,11,0,zf1)
def zf0 (_i:Nat) : Nat := 0x2971c7a25a0371978f4524004f0f4252e4d12d297263a42a2484a6a526b630d2129eacb8f4854390951525d2921a1c84a8a51342524b874b1e84a6971e9e3152129e5d3c61a425312141858311482a058a0c0c908961502c1c80a24a0c9480a1cb271e80b48a063e3d01659b1e812949a21a51e3d01d2931c84a3c72128c50616484430a7fcfbde737bd3316b669c9ee4c859e76a96d5151d3d4c62948b1a8500d800ffc67ff847fe90ffc31ffac7ff54ffeb17fd52ffa65ff4c7feb0ffd51ff221fe4c3fca87f960bf8e37f1cffb08fee22fbc67df9577f337f920
def zfw:qs := (24,1,5,0,0,10,0,zf0)
def zc3 (_i:Nat) : Nat := 0x4740a3ff
def zc2:qs := (1,0,5,0,0,0,0,zc3)
def qs4:Nat -> zi × zi
  | 0 => (0x5b56cd918f3b9a24bf5f89eecf67b5a162a6dafcd47f9b789a1bb98de754a9b80e9ff3e6247f135ec776ca932f839cac7d6eee9c2e4662999225f203411f485728babade3ebedb5f229d4a8f537f80000007f0003f889f03e08f878e1143e387,0x396250c268100c13393106d215c0100675888b035a100515e056d104831414a0902308239480040968403224880328aaa00401220086a020220502006f8aad489710b29249001345a40881aacc4962c58b162c58b000f01e007878e0001e383)
  | 1 => (0xc2893f057474fdebbaa69fa4a5d97faefe17ae4894be42d80e3450ccd330df434d9b7ddd5c4fdfb0366f23fdde51963efcce1bea8b96ddfbff19ded51e2e9a8beea677dff731bcf4f7405b6e449a0001fc00001fff97813e21108892af3e20bd,0xa8410040083c1002cc200000c402b0f8180001008054c4000128800011001a04a0c541200001a08b200000011229c0244457030008108474248000030006500110002000422016c0801a7085102a2142850a14285087801e000000000f3e001c)
  | 2 => (0x3c5f369fb9436ed14ccc12b2c3aab7611d93157caa5ffcff0b143c7c28a5bf17c342d7ebdb313539b89be469a6bc3b02f9464d5f1fd15ad8e535b1037b6a790b575d60e34899f8f0f63cd93b1e8e000000000fffc0790fe4078117f0720447e8,0x2004a016434681300321ca20640d0286a2400919221844b0c60e28265641ea4302b69c32a410700150f4a00480209290a834b441650803805f357481088804661a97783c86a80705e18f424fd5dab56ad5ab56ad780fe0078007f0700003e0)
  | 3 => (0xe7a113dffd9aebbbe7475db644d6c757c2cf919bffd567e3ede0cf2a6eafb6c8ed51f63690bf884f969bdd973dffac774afb76b4fa6b5cd7d8cfbdd5a5e1f4b677fbe5c33b1f14daa27644d59aa180fe03f80fe0002222484a27f92044bffd40,0x288000000080212401201e10c09800c471190224400800890011010000200210081100618840440424000013684002084c00080220180004000000082cc002c081a1480002000208a00800008000050a142850a1428000000007f800003ffc00)
  | 4 => (0x98ff8fa87cbdbcd796b98c1fbeff73a53ee8437b03253b34529bb8b694ef5deabfe2c3e9e69196fb74242f261733b25b9597ef8ae4cb7e24e7f6bb17f4dfbe1c814d5c4fefc6ebef8cbfc74935e5800003fff000007ff40087fa22047fc88a02,0x54294820984a58020c0061820203f61980a66041020004200180002fb40420a570284a10062288124102d88c011a0015117d24e918638469a44725970006412a400e9012c121c4c104234321122068d1a3468d1a347ff00007f800007fc00000)
  | 6 => (0xdf4adaad538d6bd275f26dffb9688c78f96c39b700abedfedc66cf515a0953dd78ad5ba69741f4f78d3b30556811f9e37840e2db7dc9edfd855a752b769ad34092069f22d16445b32b54e8be31e1ff01fc0000000044489117ffffff88100010,0x40280214448201012050474321900b000100205c0009102300c501182860010011020a5d0064190003104402e0c406c01828082405200009014107002631811243141e2d9444482824800b7a84000e1c3870e1c38700000007ffffff80000000)
  | 8 => (0xafc5f6e78648f58e93aee9dfd204b936f5d5bdb44a1ef206b05c7b5fdf901bbd58664855173838fd6f2f3aff38e2c9d927323b6b03e5217b7fcab3fa0da43be51523c72d8a689abc5c3ae69da9497ffe00000000007ffffffc44444900211000,0x21391c1984c0642048f208c100320138c461903a6126b106100aa87431090c7e04475804091a012d0ef8028123b780422404790d20409925882804150043428200a0050488a81055242f4050315f0e1c3870e1c387ffffff800000000000000)
  | _ => (0,0)
def qs5:List vp := [(1,0,350,0,8,2),(2,1,332,16,5,2),(256,0,607,0,9,1),(4,0,859,0,9,1),(268,0,595,0,5,1),(17,0,334,0,7,2),(0,64,541,258,7,1),(8,256,535,64,6,1),(320,0,543,0,8,1),(2,64,541,256,6,1),(0,256,535,72,7,1),(8,0,855,0,8,1),(6,0,857,0,6,1),(0,1,332,18,6,2),(70,0,281,0,4,0),(25,0,326,0,4,2),(3,0,348,0,5,2),(16,0,847,0,9,1),(2,0,861,0,8,1),(322,0,541,0,5,1),(324,0,539,0,5,1),(260,0,603,0,6,1),(72,256,535,0,5,1),(7,0,344,0,4,2)]
def qyl:List (List Nat) := [[]]
def qvh:Nat -> qs
  | 6 => zfz
  | 7 => zfy
  | 8 => zfx
  | 9 => zfw
  | 10 => zc2
  | _ => q6
def qyk:Nat -> Nat -> Option (Nat × Nat)
  | 7 => qf 1 5 3 4 0 0 (qxd)
  | 8 => qf 7 71 7 9 5 0 (qxc)
  | 9 => qf 29 547 10 11 7 0 (qxb)
  | 10 => qf 7 175 8 9 5 0 (qt6)
  | _ => fun _ => none
def qci:qx := (1375,10,0,qs4,qs5,qyl,qvh,qyk)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zac:qi qci (qt v8)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=4)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qyg:qc qci 6 0 1=true := bOk 7 (by decide +kernel)
lemma qsq:qc qci 7 0 3=true := bOk 7 (by decide +kernel)
lemma qsp:qc qci 7 3 21=true := bOk 8 (by decide +kernel)
lemma qso:qc qci 8 0 16=true := bOk 8 (by decide +kernel)
lemma qsn:qc qci 8 16 16=true := bOk 8 (by decide +kernel)
lemma qsm:qc qci 8 32 16=true := bOk 8 (by decide +kernel)
lemma qsl:qc qci 8 48 16=true := bOk 8 (by decide +kernel)
lemma qsk:qc qci 8 64 1=true := bOk 8 (by decide +kernel)
lemma qsj:qc qci 8 65 16=true := bOk 9 (by decide +kernel)
lemma qsi:qc qci 8 81 16=true := bOk 9 (by decide +kernel)
lemma qvd:qc qci 8 97 4=true := bOk 9 (by decide +kernel)
lemma qsh:qc qci 9 0 12=true := bOk 8 (by decide +kernel)
lemma qsg:qc qci 9 12 12=true := bOk 9 (by decide +kernel)
lemma qve:qc qci 10 0 1=true := bOk 8 (by decide +kernel)
lemma qts:qp qci 10 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qyg
  . exact (bM qsq qsp)
  . exact (bM (bM (bM (bM (bM (bM (bM qso qsn) qsm) qsl) qsk) qsj) qsi) qvd)
  . exact (bM qsh qsg)
  . exact qve
def qxa (_i:Nat) : Nat := 0x6000000
def qw9 (_i:Nat) : Nat := 0x48b325a4545000000d9c00000000000000000000004464871d83c8100000000000505000002420000000000000051a00000000000002818100000000000060c0000050cd00000000000014a3c4ae235c0000000020e0000000000000000000f8e0000080000000820200001
def qw8 (_i:Nat) : Nat := 0xc95021c90000000000000000084000000000000000000000000000000000000000c00000000000000000000000000000000000000d79c8c001a20000000000a1c0000012a4000000002aa0000000f840000000000000028b8000000000000000000000984000000003c13c8a918002c1c000003c770a40000000240000005b000000000000000312000000000000000000000000005c000000000000000000000000000000000000000000000000000000000000000000002828003c9c0000000000011a4000000000000000002ab2c6000000000000000000000000000382c000000000000000000000000000000000003ea8002e58000000001e54000000000000000000000000001798ab4000000000000f70000000003f64000000000002c300000000000000004b0000000000003a84001c50000000000c4c00000000000000000000000346c0000000000ac000d94001c4989800210c000003a980023b6ca3264000000000000001e90000000000000d680800000000000000000000000000000000000000000000000014380000000000024a8000e04000000000000000458000002bb000000000100400000000000000000000000000000000000000000000000040c000001c78003ba0000000000000000000000000000000000000000000000000000000000000000000003017c4387c238002d30003034000000000000000000000000000001d5044605400000353800000000000000000000000000000040800255800000000000000000000000000000000000000000000000237800000000000000000000000000000000222603c000002a88000000003f60000000000002c180000000000000000000000000000000000000000000000000000000000000000010680014679140000000000000000000000000000000000000000018700000032600000000000000000000000000009b40000000000018b40000000000000000000000000200000000001018000001000000000000040200000000000
def qt5 (_i:Nat) : Nat := 0x98800000000000028400000000000000000000000000000000000000000000000f2de8404009600000000000000014a000000000000000000002680000000000000000000020000850000000000000000000000055000000000000000000000000000000000000023800000000000000000114002650000000000001830000000000dd3890000000000000630006b003860039161c00001c00000000104000000000000000cc7245a400000000017540800000000000000000000000000000000001480000000000020001000000000000
def zfv (_i:Nat) : Nat := 0x87eaa8794e110
def zfr:qs := (1,4,5,0,0,0,0,zfv)
def zfu (_i:Nat) : Nat := 0x1c00800000000c77acd49f2a2c076d98a33c64a0f1414047f1e5384863f8f2a42431fc795a1218fe9c8f090d7b1e5424863fd323c2635f479545319fc84d1098c7f1e5685463fa723c2a357c7955151abe3cacaa8cfb4a6885463fd329c0e31fd191e1428fe9c8f0a147f4647858a3f8f3442631f8794e110
def zfq:qs := (19,3,5,0,0,7,0,zfu)
def zft (_i:Nat) : Nat := 0x11061a8c4052820208146400e3031f802028e145c68a30327151c3020c6c98a0f0008605162028a101460a2a3a262e0e3088e08a89229220015a1220800002104008d838c1120000220e1e61148110835e1af0d786328e187151d07190b088478d8ca38b245449144121e1a161088b8644023e1b71d734fccb25c42fbb9ad9af2afa6a7d9a2538fa017f1d7749cd701b36b9a96919f6498d62163579595514748915420fb3b8d12506f1281d0037f1e131ff5514c6ff52031bfe884c6ff5a151f7d54547df59551bfe885477f1cd21fed424877f59471bfd484877f8cc71bfd38486ffa2142bfe8858aff5a1219fc784c7be999209fc78487ee91120fda334837e1cd20bf9080c7de95510fda33443fa88910ff211442fe4e110eee6688beb912229fc78847dd95611fd633847f988a11df4788467f1e162ff1314435f95471dde331c77b888719fd581c67f4e0719fd281c67f1e151df4714c67f1e142
def zfp:qs := (47,2,5,0,0,10,0,zft)
def zfs (_i:Nat) : Nat := 0x4dc7b29a22d09b1e9c4150e6224819b4e28b87311226c6903b6434479b4f1ec4459b8f653445d8885c32a5d90d10c2e3d8111162c4c7b015330d0432184293143848d160c65304a84dcf6495c4d10c390ca2887312c00ffc23ff58bfea17fd51ffa63ff0c7fe90fee22fec237f1c7fc907f910
def zfo:qs := (12,1,5,0,0,10,0,zfs)
def zc1 (_i:Nat) : Nat := 0x476043ff
def zc0:qs := (1,0,5,0,0,0,0,zc1)
def qs2:Nat -> zi × zi
  | 0 => (0x5bc38091892f1e203d47a9aee173cca56406bafcf65b89799b0089aae394e19a8859fbaf446f1356a6f6c7b13fadde3cfcfc679cae446199f2857a3f414f601ba9fbe2df143e705626366fce577b800000000fe03f8f8f01e780f047c7042787,0x33727186a0b11c21ec3072e00c6b0180640888435a804525f806c087011404e200072d33128814291844320a04c3446b27d48300c20ee6327615723200f68044840110460f005dc7e42c30138e4ba74e9d3a74e9d078f00e7807003c7000383)
  | 1 => (0xc2bd73055a746dca38bf1fe4ae4f0caffeb7ee00a19a50d10da760e95756d343ce0ddd9d7cd9dfb827eb2cffd95f92b2f94197ea0b96cffbfd3d54d19c7b96dfce6e6f93fdb335b977c9510d449e00000007f01ffff8811f208f9088494be0bd,0x80c0004010f40000c100308004180020e91a01218054c0010029810001201880c8c4010008412099040080025a21c22808020782200800100082000004c012c1912b28100000900100103084820a4183060c183060f8000f000780000003e01c)
  | 2 => (0x3cda7f9fb3536ad14cc432f2c4bcff6c1b13353c887fecf608141c7f2c21bf17c78e5feadb617531991bed4bf4927b92f8d2485f9fd3dbd885b1f93f796a594f565430e26099f8f8f316f5581e8e000003f8001fc0111ff2011127c3f83c43e8,0x280006b04201468010630008c0640cc216a0400819221846b0420e200656426a0201b4ac32841160205034a184042452c480301445550806811c327481090804260085443ac62a0681e9844049d5962c58b162c58b000ff0000003c3f83c03e0)
  | 5 => (0xe72153dfd79aebbae7477df64550cd52c2cfb1d3ffd567ebefe0cf296a8bb2c8ec557e3690bf884f879bd5952bfdece74aef72b4fa6b4dd7d84bbdeda7e1f4f277f3e5833b1f1492227468f79aa180fffc000fe0002222244a224bfc823ffd02,0x288000040000202401301811c10808c4701902384001108800500010084002100811002c8804540426100411080000084400000621180004000000080af002d082a1440112040a20808800580000050a142850a142800000000003fc003ffc00)
  | 6 => (0x98ffcfa856bdbcd696b9ac5fbe7d79a43ee8637303253b34529bb8b794cb59eabee64be9e69196fb65242f261333f2db9597eb8ae4cb6f24e7f2bb3ff4dfbe5c81455c0fefc6ebaf0cbfe74935e5ff000007f0000044444897fc03ffffc08010,0x54284a3440025800085041030300de0800a060580001142200c00038bc44202010280a1c0626190003105c8481040451113d206d0d638469a5452796023341124204940791654ce004a1037810200e1c3870e1c38700000007f803ffffc00000)
  | 7 => (0xdf4a9aad798d6bd375f24dbfb9ea8679f96c19bf00abedfedc66cf505a2d57dd79a9d3a69741f4f79c3b30556c11b9637840e6db7dc9fcfd855e7503769ad300920e9f62d16445f3ab54c8be31e18001fff80000007ff88007fffd1110110a40,0x402900009cca0103240067c22093231181062045020800210185010f2020018571024a51006088124102c00a60da028418680ca010200009004305012404812a411e1a38c400c00924024b23860068d1a3468d1a347ff00007fffc0000000000)
  | 8 => (0xafc5f6e78648f58e93aee9dfd204b936f5d5bdb44a1ef206b05c7b5fdf901bbd58664855173838fd6f2f3aff38e2c9d927323b6b03e5217b7fcab3fa0da43be51523c72d8a689abc5c3ae69da9497ffe00000000007ffffffc40022224a21000,0x21391c1984c0642048f208c100320138c461903a6126b106100aa87431090c7e04475804091a012d0ef8028123b780422404790d20409925882804150043428200a0050488a81055242f4050315f0e1c3870e1c387ffffff800000000000000)
  | _ => (0,0)
def qs3:List vp := [(4,0,995,0,9,1),(324,0,163,0,4,0),(1,0,486,0,8,2),(132,0,867,0,8,1),(2,4,865,128,6,1),(2,64,677,256,6,1),(32,128,835,4,6,1),(32,256,647,64,6,1),(130,4,865,0,5,1),(0,64,677,258,7,1),(0,256,647,96,7,1),(0,4,865,130,7,1),(320,0,679,0,8,1),(32,0,967,0,8,1),(0,128,835,36,7,1),(256,0,743,0,9,1),(260,0,739,0,6,1),(3,0,484,0,5,2),(134,0,865,0,5,1),(2,0,997,0,8,1),(322,0,677,0,5,1),(7,0,480,0,4,2)]
def qyj:List (List Nat) := [[],[98,135],[81,114,134],[81,130,118]]
def qvg:Nat -> qs
  | 6 => zfr
  | 7 => zfq
  | 8 => zfp
  | 9 => zfo
  | 10 => zc0
  | _ => q6
def qyi:Nat -> Nat -> Option (Nat × Nat)
  | 7 => qf 1 5 3 6 0 2 (qxa)
  | 8 => qf 8 75 7 11 5 2 (qw9)
  | 9 => qf 26 481 9 12 6 2 (qw8)
  | 10 => qf 9 163 8 10 4 2 (qt5)
  | _ => fun _ => none
def qez:qx := (1511,10,0,qs2,qs3,qyj,qvg,qyi)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zab:qi qez (qt v8)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=4)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qyf:qc qez 6 0 1=true := bOk 7 (by decide +kernel)
lemma qsf:qc qez 7 0 1=true := bOk 7 (by decide +kernel)
lemma qse:qc qez 7 1 18=true := bOk 8 (by decide +kernel)
lemma qsd:qc qez 8 0 16=true := bOk 8 (by decide +kernel)
lemma qsc:qc qez 8 16 14=true := bOk 8 (by decide +kernel)
lemma qsb:qc qez 8 30 16=true := bOk 9 (by decide +kernel)
lemma qsa:qc qez 8 46 1=true := bOk 9 (by decide +kernel)
lemma qr9:qc qez 9 0 5=true := bOk 8 (by decide +kernel)
lemma qr8:qc qez 9 5 7=true := bOk 9 (by decide +kernel)
lemma qvc:qc qez 10 0 1=true := bOk 8 (by decide +kernel)
lemma qtr:qp qez 10 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qyf
  . exact (bM qsf qse)
  . exact (bM (bM (bM qsd qsc) qsb) qsa)
  . exact (bM qr9 qr8)
  . exact qvc
lemma qab {m:Nat}
    (h:(qo (1024 ||| m)).all (fun a => a==qu||(j4 m).contains a)=true) :
    ∀ a ∈ qo (1024 ||| m),a ≠ qu -> a ∈ j4 m := by
  intro a ha hne
  have hh := List.all_eq_true.mp h a ha
  simp only [Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at hh
  exact hh.resolve_left hne
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zbu:qy (qo 1215) (qa 1215) 11 :=
  yv (g := qbw) (m := 191) (i := 0)
    (xs := (z2 191 536879360).filter (fun p => p.1 != qu))
    rfl rfl (by decide +kernel) (qab (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (qe v8 qbn) (by decide +kernel) (by decide +kernel)
    zad qtt (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qzp:List (Nat × List Nat) := [(1215,[]),(1343,[135,50,65]),(1403,[130,50,81,115,98,65])]
def qvv := qh v8 11 qzp
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zbf:zv qvv := qd qbn zbu (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zbt:qy (qo 1375) (qa 1375) 11 :=
  yv (g := qci) (m := 351) (i := 0)
    (xs := (z2 351 12901687552).filter (fun p => p.1 != qu))
    rfl rfl (by decide +kernel) (qab (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (qe v8 qbn) (by decide +kernel) (by decide +kernel)
    zac qts (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qzo:List (Nat × List Nat) := [(1375,[]),(1391,[84,131,98]),(1455,[98,118,81,130,50,65]),(1469,[118,130,81])]
def qvu := qh qvv 11 qzo
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zbe:zv qvu := qd zbf zbt (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zbr:qy (qo 1511) (qa 1511) 11 :=
  yv (g := qez) (m := 487) (i := 0)
    (xs := (z2 487 22028484864).filter (fun p => p.1 != qu))
    rfl rfl (by decide +kernel) (qab (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (qe v8 qbn) (by decide +kernel) (by decide +kernel)
    zab qtr (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qzm:List (Nat × List Nat) := [(1511,[])]
def qa8 := qh qvu 11 qzm
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qhm:zv qa8 := qd zbe zbr (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zbq:qy (qo 1519) (qa 1519) 13 :=
  qnq (m := 495) (m0 := 494) (L := 13)
    (by decide +kernel) (qab (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun p b hr ha => le_trans (by decide +kernel:13 ≤ qt qa8 495) (qe qa8 qhm 495 p b hr ha))
    (fun p b hr ha => le_trans (by decide +kernel:13 ≤ qt qa8 1007) (qe qa8 qhm 1007 p b hr ha))
    (fun p b hr ha => le_trans (by decide +kernel:11 ≤ qt qa8 494) (qe qa8 qhm 494 p b hr ha))
    (by decide)
def qzl:List (Nat × List Nat) := [(1519,[])]
def qnc := qh qa8 13 qzl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qvn:zv qnc := qd qhm zbq (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zbn:qy (qo 1533) (qa 1533) 12 :=
  v1 (m := 509) (cap := 11) (ci := (64,0,1469,0,11,2))
    (xs := (z2 509 13555999488).filter (fun p => p.1 != qu))
    rfl (by decide +kernel) (qab (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (qe qnc qvn) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qzi:List (Nat × List Nat) := [(1533,[]),(1503,[118,130,81])]
def qnb := qh qnc 12 qzi
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qvm:zv qnb := qd qvn zbn (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zbo:qy (qo 1531) (qa 1531) 12 :=
  v1 (m := 507) (cap := 11) (ci := (128,0,1403,0,11,2))
    (xs := (z2 507 14243872768).filter (fun p => p.1 != qu))
    rfl (by decide +kernel) (qab (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (qe qnb qvm) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qzj:List (Nat × List Nat) := [(1531,[]),(1279,[118,130,81])]
def qna := qh qnb 12 qzj
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qvl:zv qna := qd qvm zbo (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zbp:qy (qo 1527) (qa 1527) 12 :=
  v1 (m := 503) (cap := 11) (ci := (16,0,1511,0,11,2))
    (xs := (z2 503 22028484864).filter (fun p => p.1 != qu))
    rfl (by decide +kernel) (qab (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (qe qna qvl) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qzk:List (Nat × List Nat) := [(1527,[])]
def qm9 := qh qna 12 qzk
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qvk:zv qm9 := qd qvl zbp (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zbs:qy (qo 1471) (qa 1471) 12 :=
  v1 (m := 447) (cap := 11) (ci := (16,0,1455,0,11,2))
    (xs := (z2 447 13421781248).filter (fun p => p.1 != qu))
    rfl (by decide +kernel) (qab (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (qe qm9 qvk) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def qzn:List (Nat × List Nat) := [(1471,[]),(1407,[99,134,65,50,114,81])]
def qe9 := qh qm9 12 qzn
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qv1:zv qe9 := qd qvk zbs (by decide +kernel)
def qt4 (_i:Nat) : Nat := 0x0
def qp1 (_i:Nat) : Nat := 0x1e2db39b69cac02900000000000000000000000003a0ce000058c01850000393c141002
def qp0 (i:Nat) : Nat := (if i<2 then (if i<1 then 0xcd640000000000000000000000000002b5e00000000000000000000000015560000000000000000024c90000000947c00026b40008f2c000f5cf4260000000012000000000000000000000000095a2980a488000a5900000000000bca38031b1000000000000002a0b0000000107c000000000000000000001847431e4e20000000d0840005dc800000000000000000411693ea5f34c083df875000350a9c3f02a000000000000000000000000144e0000000923c0009f6400000000000193bcd00038300000000000000000000000000000c02e24f00000000000000d2d00000000000000000000000005db1c5890f000037180000003559000000000029c80003b1e00000000000000000000000000000000cba14a400000000000000000fe240000000000792c0000000000000000000000000002dd90000000000000051fa1720001eb60000000c2cfba2437c000000000000000002be800000000000000407000000000000000000d97000000000000000000000000000000000000002d8b60511ca0000000d0800000000000000246000000000002405000160800004990000000159800000000008d7c0000000000c18c000000000000008c800000000000000000194f0000000000000000000003440000000000000000001b0c0000000000000000005ec00010cc000000000000000000000000e04ccf400036ff0000000000000000000000000000124000000001920000000c05400000000000000000000000092a400021ab06bb6180000df854b000000000000180000000000000060ec0000000000000000000000000000000000000000000000000000000000030ac00000000000000000000000000000000000d32000000000000008d5000061dc0890000000d74c0000000000d72f96c00000000000000ebe4088d747960000000063bc000000000000000000000000076b77c00000b00003e8a000385b00000000000000000099500000000000000000000000000000000000000000042fc000db700003c0c0007a63dbf002000000000000000000000001001000001001001000000001001000002000000003000000000001003000000004000000000000000001001000001000000000002001003000000000000000000001002002000000000000000002001006000000003000001002000002000000000000000000002002002000001002000001000002000000000000000000000000000000002000000000000000000000001000001000000000000000002000000001001002000000001000003002002000000000001000000000000000000000000000001000001000000000000001001001000000000000002000000000000000000002000000000000000000001000000000000001001001002000000 else 0x1a074064000763000000018175c6c000000000010f400200000000000ce4115c000000000000000009b74000000000000000000000887e81400042ac000000000000000000000000a57a57e0000000000000086e40000000000545668900000000000000000000000000000000cde843f052f504000e004000040000000029119d80000000000024dc067000000061e45d800000000000c1000000002694000000000000000000000000000298500000000003e0a815301b000000000000000000000000000000000000000000000000031c80001c8c00000000000000000000000000000000000000000399e0002c8200010be00000000000000612c000b59c00000000005434000000000000000003d70000000000000000000000000d2e0000000000000000000001c7000000000000000645c000b33aec7000000050d8000d6f0000000000000000000000f1d00000000000000000000032ab2c991e00000002596000000000000000002170820c0000000000000000000000000000000ca14000f2ec000000000000000004cb40000000000854fa7b000000000020d90000000000255d0000000000000000000000000000000000000000000000000000000000000000000000000000000019710000000f668000000000000000000000000000092300000000000000000000000006910000000a18800000000000000000000000010004a500000000000000000101c0000000000000000000000003d0e20e40000000000000000000000009684000000000000000000001d740000000000000025248fe00000000000000000000000000000000000c1da1510000000000000031764240000c3400000005c90000000000000000000003da6bb50000000000000000ea00029c90003dcd000000000000000000000000000000000000000000000000000015b100000000000000d5adae7b5e4000000000000000cc0000000d310000000000000000000000000000000000000000000000000000072f0cd7a3a0000ddd896366a0000b46c000000188600028ac00000000000000834800000000000000000a57308b00000000003120000312f000000000006f3000384300000000000000000000000000000000000a8bc0006184000d4c40000000000000000000000000000000ea6c000ab9400000000000000000000000000000000000000d8380000000000000258700031455c87d48880d49884d00000000000000000000000000003e6600000000000000000000f23801d0000384dc3400000000000000000000032ab00000000000000000000000030e5000000000000000002a8d000000053e1856f3b8000000209db3f0000d24c00000000000000000000000066a4000d1f4000000000000000000000000000000000000) else (if i<3 then 0xb3000000000003ba821fc0000000000e384000000275600000000000000000000074a0000c0b8000000216f0000000000000000000000000000000000000000000000000000000000000000000000000000035840000001c3a00028a20001a7c22d80c3f0b400000000000000000000000000000000000000000000000000000002db33010000000000000000000000000b5a4000000392c000000000000000000000000000000005cc0000000000000000000000000000000000000000000000000000000092e469e0000000540400000001b4bc980005e0b13d0000000000000000009d4f420000000000000032f800000000000000c69c0000000dbb0000000000000029900000003ce60000000000000000000000003ac80002d4a000000000000000003988050f89400039c200010eb99faaf200000000000000000000000000008273f460000000000000000000000002ee80000000000000000000000000000000000000000000000000000000000000000000dc10000000000000000000000000000f39c00000038b20430000a738000064c00000000002466183000000000002630000000000000000000000000000f414000000000000000000000000365213800000008b4ac440000000b4e8000000000000000000000000b6dc000000000000000000000000000000000000000002ca700000000000000a0580005a400000000000000000000000000000000000039000000000000000000000000020f6b4fc00000001b80000000000000000000000000000000000076bc00000020550000000544a56e000000000000000000000629800084ac0000000000000000000000000000d040511dab3493ad60000000000000093a70f30000000000000042680000000000000098e00000000000000000000000000000000000767400000030da92c40000000000000000000000000003c4f000000000000000000000000000000000000000000dbc4000e475adf000000000000000003c5e00000000000000592000000000000000000000000060c80000000000f4c00000000136c680000000005a0000adb00021020000000000000019a286d00033d0d5f4000eb88000000356a00000000000000c2f400000000000000000000000076b800018aa90bec400000003cf200000000001c6f0000000d640000000000000038b70001adaa30800000000000000daa000000000000000000000000000000000000002dc30000000571400000010920000000dbd800000000000000000b2280002c1c000000000000000000000000000000000000005880526c024000000000000000000002b200000000d4d706e0000000000000000000000000000f1d0000000309be4580000000000000000000038a1000000000000000000000000000000023730 else (if i<4 then 0x100e00039750000000000000000000000000a990002c690003823b0180000000000c17eaef000000065e00000000000475c000000000000000000000000000000000000000000000000000000000000000000000000083c0000000277f00000000002d6200000000000000000000041e908100000000001ed500000000000000000000090a19500000000000000000000005a580008557ca30000b0e00000000000000000000000014dd91ec0000000000000000000030a871c400000001a20280000000000000000000000000000000064b80000000000000000000000000000000000000000000000000000000106500000000003c400000000000000073b4000000069ac244000000139cd6b23cfb5603250001fbd000042fdc640000000000000000000000000000000000000026f80000000000b0340003634000000000029963c800000000003c9e000000000000000001177000000010780008108000000000091b00000000c9500000000000000d33400000000000001bce53ec0000000000000000000000000000000000000000000000003546e0f9ede0360000a328000000000000000008ca8000000000094a80c5b748000000000000000000000000000000000000000000000000000000000000000000ce6400000000000000000e53a4d30000000000000000016000000000bcd1ca4435b48400000000003c08000278cd3c400052b40000000000154b8960000000000000000000000000000000000000000000002c7c000000000000000000000000208c0000000000000000022fbc198a4dd75800083e80005536cf900038970000933000000040e1d4773fc000d0b07310000000000000000000000000000000000000000000000000e57c000000000000000000000000000000000000000000000823800000000000000000000340c000000000021b500000000000000a604000000332f00000000000000b1280000001cd5000000000000000cbaad85234000000000000000000000000255000000000000001011b55c000000000000000000000000232c000000099f000000000020db0470000000000000000000000000000000000035b0000000081300000000000000251a1484000000342500021c0000054c0001b58000000000000007de4000b118d9cd40f8277164c22000304920fc0000000000000000000000000000000ede80002cac0000000000000113b000000000000000da800000000009318000000000000000000003d9b00037220000000000000000000000000000000000000000000000c1d0000000000000060280000000000d56c00000014b50000000000189f00000000000af40002cd4b71c000e33c00000025763ce800083b15060000000000335d0002cc1044d9270002 else 0x1c4b5fc0008068000000293900000000000000000296d000000000000000000000b68c0000000caf00000000000000cdec0000000000000000000000000000000000000000000000000000000000000003330000000e1cd9429a74000b63c0000000000000000000028f5d5000000000000000000000019ba000058400000000001d140003c8000000000000000000357a0000000000000000000000002d250002bc70000000000000000000000001e7f000000000000000000885000000000000000000000000000000015b6714400000000000000000000000000034350000000000000000000008c338fd0000000a62400016458ae347800000000007345c41e0ddc3117556f744f00000003d82b38c0000000000000000000000000000000b1a045c1f5000000000000000000000000046f400056c8000000000000000004628109914f15a000000000000000000000000000000000000000000000000000034dc000000060a4000004a6c56e140000002b01b69000000000008a48000000000000000000000000e4b4000000296500000000000000000000000000000000000000000000039cf00000000003998000000000000002a5c00000000000000000000000000000000000000000000000003d700000000000000000000000028501bf00000000000000000000000000001d07000000000025990000000000000000000000000d18)))
def qpz (i:Nat) : Nat := (if i<3 then (if i<1 then 0x6b9200000000000f2160003524800000000000000012700000000000000088f475a9cce8000000000000000000cbda0000000000073b400000000000aab2000000076280ad80001282986c0001259c00000000000701b286000060dc42964628000b09a000000001140000000000000000000000000000000000824c0fd00000001431000000000000e7a000000000001b4880000000000130f800031c50000000000000000000000151d80000000000000000008bba0000000000000000000000102e0000000000000000000000000000005296000000000000000000000000000000355d406000000000003c2811d100000000000000000000000000000000000000000000050da0000000000000000000000000000000002a4d8000000043dc000000000000003a5c8000000000000000000000000000000000a322436400001e0000000000000000711a000000028af000000000000000000000000000000000000000006cc3d484419c00000000000000000000000000000000008710001c07105c3a38000000000000000000000004c3000000000000000000001640000000007900008880000000000000003cb88000000000000000000000000000002d9c000000000001634000000000007c32c4c6000187f000050e6000000000000000000000041690001050badf8000000000000000000180a370800000000000440c0000000000000008f98000000000004ec0000000000000000000000000000000000000004d400000000000000000000008ced017b252601e7a9c00000000000e2240000000000000000000000000000000002d16000000000003c0300000000a71c00066730000000000000000000000000000000001d34ce45000000100000000100200000100000000100200000000000300300100000200000000000000000000000000000700100200100000000000000000000000000000000000000200000000200000000000000000000100000000200000000300000100000000100000000100100000100100100200000200100a000001000000001000000001000000000001002000000000001001000000000001001002000001000000000000000001000001001000000002000000000000000000000000000000000002002000000000001000000002000003001000000000003000000001001000000000001001000000000001000000000000000000001000000000003002000000001001000001000000001001000000001000000002000002000003000002005001000000002000000000006000001000000000000000000000000000000000001000000001000000001000000000000000000000000000001000000000000000000000000000001000000000000000000001000000000001000000000000 else (if i<2 then 0x502c0002100800000000003c74800000000000000000000000000000000081ae00000000000000000000000000000000000000000000028340000000000055b9821000081a446d800011650000c4bc00000000000e65ec6c000000000002e16203b0001813800014390000c87c00000000000000000000000000f62ccee8000000000036d800000001c25a0340000a9980000000717d806d88400005083000000000007854746400000000000000000000000000e94a00000000000000000033368000000000000000000000144d80000000000000000004a06000000000002e0c000000000000000000000004ca0000000000000000000000171740000000000000000000000000000018ea9d97000000000000000000025380000000000000000000000000000000002a6f000000000000000000000000000000000000000000000000000000000000000000000000000000000016570000000000000000000000000000000000000000000000000000000000000000000000000000000000000030c77409124000000000000000163e800075eeb3af4278000000028b4000000000000000000000000000000000000071cf000000000000000000000006e680000000000006f00000000e4380000000000000000000000000070d40000000000069ac0000000000000000000000000000000000000000000000000000000000000002c9e425a0001eb080000000000000000000000000000000000000000000068010000000000000000000000000000001299f95000076568bae000000000000001c91400079250000186000000005afa0000000248f0000000000000000001f1048c3f24e0001c20a2f6401844940000000620700000000000000053c600024ad00000000d72c00000000000000000000000000000087ad8b7000190e1cde000073880000000000000000000000503700000000000000059e800000000000000146880000000000000000000000000085dc00000009afe0000000000000000000000000000000000000149a000000000000000394ce0a3c5180000000000000000000001c732470000000000000000417ec336a8a000000000001875000031520000b86c000000094d862c600880000000000000000000000116607980000000e86400000000000000000000000000000000000000001c53c08f800059e600000000000235c00000000000000000000000000a4900001c458000000000000000000b3160002f38800000000000000000000000001ac3000000010111cd8302ae0b4000000000000000000000000000000000000000260000000310c00328cb4a944000000014480000000000000000000000000000000000000609c00000000000000064dc000000000000000000000000003c02524000000000000000 else 0x1c8e0000000000000000000000000000000094000000000000000d318000000000000001c10587300000000000000000000000000000000000000000049a000072f4000000000002ba328a80000000000000000000000b00e00000000000000164b0000000000000000000000000000000000000000004720000000000000000000000000000000000000000000002d052617c3fd826f05f0000fb2800000000000da5800000000000e0ac1608000189f7053426800000000000000280b8000000000000000000000000030c10000000000000000000000000000000000000000026ac663f00019135c2900000000000000000000000000000000000000000000000000001e30800030d0000000000001566000000000000000000000000000000d0cc000000000000001c0c02d0ba5a79ae00000000000000000000000000ba1a000000000000000000000000000000000000069b2000000000000000b1fa00012bb0000d28600038250900000000000000000000000034ae0000000000000000000d4c43784000000000000000000259f00000002009aa08618e00000000000634e00000000000000000000000000f2f922f4000222300000001c9e00000000d4d8000000092fe0000055000000000000000000000002588000000000000001ae00000946fb286c44811ed2ac0000000000011d000010f680000000457c00000000000187bd1b00000000c7c400000009144033305a80002334000000000000001263c00000000000000000041fd611e0525254800000000000000000000000001d0eca39f0f1039400000000000000000014c7301400000000000000000000000000b4180000000000000000000000000024800000000000000000000000085d0000000000000000001525000000000000c4c00000000000000000000000000000000000000000000000000000b35e000000000000000296c0006dd60001017c0000000000000000000000000000025330000b08ec9a18168000000000030160000000000028cf29ef00000000000000000000000000000000000000000000000000000000607e000000000000000000000000000000000000000778000000024f800000000000000000000000000000050580000000000000068210000108c00000000000000000000000000c42000000000000000012080000001798400048f2000181afc01ea4db00000000000000f4ac00000000000000162b66610000000150300000000000000006b88000000000000000000a20800000000000ab2000000000000000000000000000c22000000000000000108bc00000000001179c000000000000000000000000000000000565e0001c536ebf5dffd302000000000000000000000000000000000000000da0000000000000000001a3b4000000)) else (if i<5 then (if i<4 then 0x8175086c0000000e193a60c000000000000002b0e490a0001e7d00000000818200038ece9290000000000000000000000000000000000000000000005b5a000000000000000000000050c800000003ac700000000000000051c9000170f000000000000000000050e200000000000000000000000000000000000000d2c00006cb000000000000000164c8000000060ae000000000000000000000075ef000000000000000000000000000000000000000000000000000000000000000000000002db30000000000000000001b4c800025c700000000000000000000000000283e0000e7fe45300000000000149080000ac6000000000000000671800049d6000132d3c380000000166008f600000001734581880000001074c00000008a06000000000002288000246580007b2de37c0000000000000000005a4300000000000000000000002cfc80000000000192f0000d95bf79800019540000000000061380000000000000000000000348d80000001a8980000000c3d60000c3780000000000000000000000000187b00001a98000000000000000a46682d800072e6000000000008157b76c0000000000138f40000000037c00000000000000000000000000000095cc000000000000000000000000000000000497400000003aa480000000000251100000000000000000000000000233500000000572800009c3000177480000000902000000000000dc7400008cf80000000000140aaa2d0000a1fc00000000001b0880000000000000011092148000000000004a4b0000000000000000000000000000008218000206d8000000192380000000d03e0000c1380000001c705a4b8000c0f642740000a710000000000021db000000024508000000075ac00000000001084c0000000000000029188000000056c4000000000000000000249f0001e37205e00009ca6000000000000000000367a8000112a0000000000000000000000052500000000000000064d20000000017200000000000000000000001727800000000000000000000000001b2c8000000000014c2701a000000000000000000000000000000000000000000000000000000000000000000000000000000182280000000000000000000000000000000000000000000000005d79d2c00000000380400000000000000052ec00020ab8000000000018ef800011a242e64d8800000000000000000034ea0003b2930f80001a3fc000000033dc000000000000001085400000000000c4140000000000084440000000000000000000000c246000000000000000364cd39000000000000000000000000000efc00000001879c0000000000180272cd0000000021d2b2e8000a332000240680000000000000000009342f730cf10000ac3a0000000000000000000000000072c800 else 0x35a05980007440931000000000000000000014c810ee0000a54d81e0000c2760001c940000211c000384c80001ac4d6000000000000051d80000cea2ae400000000000000000000000000000000000000000347e0000000000000000000000000022dd80644af0000000000000000000000182c00000000322a02cc0000000486c7740000000000004790000000000000000000000090758628000000000000000000000000000000000093a00000000000000000000000000400b0000000000000000000000002280c6000000000000000f4ba00000000000000000000000000000000000004a6a0000000000032140000000091e2dcfb0ec00000000000000000028e800000000000000000000000000000000000001287000072210000000000000000000000000000001b5000000000000000000000000000f0e400012180000c4ee00000000000000000000000000000000008fa80000000000000000000000000229ec05100000003c17800000000001c34c660000000000007c98b3f000000000000000000000000000000016140000000000000000001d34d358f69800009cd000000000000000c0c000000000000000000034d53267bc44a33e4028000000000000000000d40908e80002ca00000e5e400000008b3000000000000d34a775000000000000000000051a80000000000000000001d68c0000000d254000000000000000000000040200000085c00000000000000000000004c498940000093d0000c18408680000000000000000000000000000000000000c4fc000595900000000000000000000000000000000000003a1ba2161a3c00000000000000000000000000f11000000000000000000016bd0000000000000006247000000000000000000000000000000000000000003e70000109d80004a11000000000000000812e000000000004257e2900000000000039dc45380000000441c00000000000000000035c1b3f8a83c00000000000000000000000000000191480000000a088000000000000000000000000000000000000000000003337000000000001c601e290000000000000000001971000049cb000000000000000000000000000000000000024438000abaa00028f8325c00000000000557c00000000000257800000000000196f0000000000000000000000000000000000c7d80000000000000014d58000c36fc49800000001266000000010250000000000000000000000000038fb000008140000000000025c000000000001e894000116a00000003d1e80000000000000000000000000000030e3000000000000000000000030b6725700000000000000000000000000000000007800000206a0000000000008f0c2ba00000000000b103e17000055de0000000000000000000000000000) else (if i<6 then 0xc3a400000000000000000000000000000000000000000000066e00001caaf15000000830000a4c200000000000000000000006a350000000000000000000000000000000000000000000000001d6808e50000000107ec0001cd500000000ac1800000001173cf2800051400000000000000000000d1a00001072291000000000001c154000000080900000000000000000003c218000b1ba0002cbadd7b000000034650000719c0000000000000000000000000000000000000000000000001aa100000001c1600000000a890000000000000000000000000000000009000000000000d7220f480000000a3e4000000090ee814c0000000000000000000000d0c8000000000000001c0cc00000007b444468000000070960000000000000000003b0fb1400093a6fc00000000000000000000000000000003108eaf904000285f80000001a0aea564a54000000000000000537200010ac00004b5c000000000000000f2fc00000000000000000000000000000000000000000000000000001be8000000079a6d1240000000000000000000000000000000000000000013c20001c9cc5c30000000000000009a81c4240000d140000c980000000000000000000000000000000000000000010213519be120c66000230459221ad200000002259000000032c080000000000000000000000000000000000000a52800030cd000000000000000000000000003c9d6a660000000000000000000000000000000000923000000000000000216892a0000000000000001664800000000000000000000000000610000000000000000000000000000000000000000000742800000000000000000028f400000000000000000000000c0e91960000000000000000000000000000000000000000000000000000000000000001e64c0004a0900006670000000000000000000000000000003ca300000000000000000000000a1d5b17187a000000000000000000000000000000000000000000000192c000000000000000000000000000001a3b1ca380000000000000000000000000000019f70001016400000000000000000000000001e1f40000000037a0001e65000000000000000000000000000000000000000001e8799550000000000021f20000000200778080000000000000003b080000d0f0000000000000000000000000038cc0000000000000000000040400000738000f99f40d40000000000000000000000000000000003e2d000000000006113000000000000000385c00000000000000000000000000000168c38d200000000a7780000000000083ac0000000000000005398000000000000000000000127a800000000000000048c0000000102eeb01c0ac0001493c0000000000000000000000000142d0000000000000 else 0x88b0d7390b08000000000000000000c01e000392aaa6400000000000000000000003043000000000000000000000012636e948000000000038ddf1010001c08c0000000c8d80000000460e0000000000064f63a2e000240dd8a9d36a045dc97791d000000000000000d47c0002233000000000000af98000000000000000000000000034920000000036bc00000000000000000000000000000000000000000000000000000000d780000000000000000000000000000002c090000000000000000000000000000000000db140003c5b71370000000000000000000000000000000001a1180000000000100e00000000d374000000048d40000000203e015b000050e860580000000000000000000000a6572816a030000000000000000000363c000000073120000000000063800000000000054577364861aa70407a32f00000000000002400000000000184c400000000000000346afceb33b8c2140000000796a0002a150000000000000000000745c000180a0000000000009368000806800000b68000b1192008000000000000001c405dd3000000000000000000000000000000f2d60000000000003cc65e000000000000c1300003a4c0000000000000000000000000041b300000002c720000000000000000000821fe9d00000000b07ed9ac00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009c8a00000000000000000000006a5300000002c7e28d60000000000000000001d4a8000000000000000000000000000000c69b623036800000000000bae00000000000000000000000000000006504000000000000000000000000000000000000011e200000000000b340000000000000000000182780003400163400000000001c8380001d74000000000007c0a90ca00000000000f44e0000000009100000000000000000018708000000000000000000000000000000000000051c20000eb2ccc600000002cd4c667000000000000000000000004e70000000000000000000713000000000000e15df108000000000000000000000000000000000000000000001b108000ebb80000000197b00000000000000000000000cc28000000145440000000000000000000000000000000000000dc8c00000000000322d08680000000000000000000000000000000003d6d000000000000945000000000000000000000000000000000109940004863000000000000000000000038b1aa5200000000e4e0000000000028d1fa5ff204000000000000000000133a8)))
def qpy (i:Nat) : Nat := (if i<1 then 0x14181d0000000f0f0000000000b32f08785a0000000000000e06000000202522c0000000000000000000000000000048ac000000090d9380000000000000204000000000000000000000000000000000000000000000000000000000000000000000000003ef481900042060fdf4664f8003a32000cc080038fa000000000000000018b000102e00000028300a200092d8001087c7f00070404da000000000000039a0000000000000000000000068e6208003d34000651b8e000061a00000000000000000000cd60000000001d0a0000000003c0383600071d8001e31b55000207d32f00000004dc45d0000003d1e00000019f000004d0000000001c960000002d5a000f0a0001f560000003a6c0000000000000001682b2c61410d09607498000000000000486c0014642468000001d4b0003201a6ce7900000000000000001100000000d3c10ec00000000079c80000007c9759c00000070f8000000000000000000000000000038a400000000000000004210000000f0a0005d5c00000000000000000000003114000000000000292000028f00000000000007d0800162400000000000007540000000000b17ed8c808a0f00021be15c000000000000000081e800063e653cbc800000000000000000002a0000000224e0000000000000000000000000000000000000000000002c264f400000000000000000000003949254000000000000000000000002a6389380800000000010a0000f2b0000002cd80000000610000000000327480e000f548000000d5322c8000000f240000000000000000000000027500000000000000003c426780000003a78eb000079a00000000007af80000000000007213ef0000a53800100b27081778e6498b5a000096b044013000000304721500000000000000000000000000000000384000000000000000000000000000000000000000000000000000000000005c8c0000000000000000000525000000000031a800000180a000309b9180000000000000000eb155d400000000000000000002b3000292a42ad9df263ebc0000000003e540000a080010e2461e398000000000000666c00000074ce5b0001d8dcb0800000065700000000000000000000000000000000000000019e960c00000000000000000000002541ed165cd0b1e740000006c38000001c5e544a29400000000000000000000000000001e0300000000000000000000016000f248000000000d51000290c0000007d900000000000002eb95880005c31ae80006986875d39e697b7000000000000000000010000000004000000040000002000010000300000000000000200001000000040000002000010000100000008000000100802000000040000000004000000100002014010040000006004000140300400010010040900808 else 0x3300000001c7b00000000016875068000c0000051994b5c640000000001012aac33378f00000007ce000000000094580000000000488002616000000592c000000c4a0000001411ebb8000001c480006ce00000000001a5c000000223e954000000000000000130f00000000be0005acf4ceb198778148002888000000000000000014400000000000000000aec43a0000e98000000b49282000146a0007468460000e1380028ce000ba50000001f000000000000000000000000000000000000000000000000000000bd70000000000000648906e4a1412800000104f0000000000000000000000005661a218c0000009900002956000000000000141c0007694c8c00000000000000004310000000000194c0fc000000000000000000000000000004180000000115ba4207000000)
def qpx (_i:Nat) : Nat := 0x670000070e45800940000000000001b58000315e006d88610048000d1c9e000000000000000000000004b96e040079a0066000000001c2000000000075000a2ace3200100b40000000000000001042140000000012000000078800000000000000000000004860000000000000000040050018000
def zct (_i:Nat) : Nat := 0xbcc95389d6095260551
def zcr:qs := (1,6,7,0,0,0,0,zct)
def zcs (_i:Nat) : Nat := 0xb0405d0ef06103a0bd041001000080098354100060004053c441b22fad24219f028061efaed4c2691a60ae75a9a4e304a930325fd7db315226981a3dea6936d5b04a8dced5349c60981547e6c93ac12a4c0aa373e49d6095260531c1f6c62584dd54c171cd9561152c9a60ae6c93ac12a4c0aa36bc4ad6093260531
def zcq:qs := (11,5,7,0,0,8,0,zcs)
def zaw (i:Nat) : Nat := (if i<3 then (if i<1 then 0xac26d736065fd4709b5cd81ceee225aeaa6073b78cd6baa981b3ec9c609526079ed8454b26982c7f611aec9a60b9f58ce1126982e776558449a60a5efb314b26982d7b61152c9a60a1ff2711baa98287fc9c4eeaa60a1ff4709baa982c7ed2c26eaa60a1ff4f09baa982e776558449a4cb1f78cc9baa982a7ed2c26eaa60a1ffb312b26963c77e554ac9a58e1ffb315b26963c7ee2256c9a58f9db9562226963ff46558ce22847ef1a223388a11fb668895622847e75a22778ce11c7f61126eaa60b8fda221126932e67e669549a4cb8dfa22552693287fd1c26eaa4cb1f74f09baa932c7bd4c26eaa4ca1ff5709baa93287fd8c26eaa4cb1fd8449baa932c77e5526eaa4cb1bf9989baa932a7becc52c9a60a1ffb313b26962c77e554ec9a58a1ffb315b26962c7de3356c9a58b99f9556326962e75e558cc9a58a9ef5309a4698287fecc46c9a60b1f78cd1b26982c77e5546c9a60b1ef52d1b26982c7f6114ec9a60b0ffa209baa932c7ee2262c9a4c71df9558b26931c5fe7762c9a4c71df956bb26931c5fe77aec9a4c70ffa22bb26931e76e558889a4c78fba222226931cf7a554ed2a44387fa227726931b7d49c4c9814c71fb8893b26981abf4ac609814c6cfd2718260531d75e5526d324c74f7a209b4c931afccac609324c65f7272bb4c93187fdac26d524c63fe430ab6093187fdac26d824c65fd4709b6093187fdac26d874c7ef1609326053187fecc26d5a4c71fb8889b569318ff90caed5a4c61ff272bb5693187fd8c26d7a4c70ffa209b5e93187fd2c26d8a4c61ff5709b6293187fecc26d8a4c71fb8889b62931c77e5526d8a4c61ffb318b269318ff90caed8a4c61ff272bb6293187fd5c4ac9a4c61ff6312b26931c77e554ac9a4c70ffa212b26931c77d5256c9a4c61ffb315b26931c7ee2256c9a4c70ffa215b26931c3fd8262c9a4c717f9dc9b62931d7d63326d81547ed96095260551b3f49c609815465fd272bb6055187fdac26d325461ff6b09b6095197bd4c26d825471fb8889baa951c7de3326eaa5461ff4f09b62971c7de3326d8a5c75f98889b6055187fecc4ec9a5c70ffa213b2697187fecc62c9a5c71f78cd8b26971e3de888cc9a5c75778cc9b61d7187fd3c4ac9a6061ff5712b2698187fecc4ac9a6071f78cd2b26981c77e554ac9a6061ff6313b2697187fc9c4aeaa4c61ff2718baa93187fd2c26eaa4c71ef5309baa93187fd5c26eaa4c61ff6309baa931c7ee2226eaa4c71df9549baa931c5fe7726eaa4c70ffa209baa931a7bd4c26eaa4c61ff4f12b2695187fc9c56eaa4c61ffb312b26951c7de334ac9a5470ffa212b2695187fecc4ec9a5471fb8893b26951c7ee22aec9a5471f78cebb26951e7ce338889a5478fba222226951d7755226d815471fdaa89b6055187fd8c4ac9a5471ed8454b26982 else (if i<2 then 0x58a443bf28ce2262910ef6a558898a442dfc2712b54510b7f09c4ed51442dfc2718b5451097f89c56d214c3ddc5489b54510f7e22226d51443df48cc9b54510f3f28826d51443fd86095254510bf72cc549514437dcaed5254510ff523354951443edca215254510dfe222aed514437f48cebb54510dbf288aed51443ff08ce2254510fbe28888951442dfc4b09b54510cbfa8856d2a443bd6956334a910ebda888cd2a443adea22554a91097f89c56d2a4425fe2718b4a910e77a5526d3a4423fe572bb4e910cf7a55aed3a443bda956224e910eb7a889553a4425fe2715b4e91097f89c5ed3a4425fe2718b56910d7f15126d3a4435de9549b4e910d5fa7726d3a4434fea209b4e910a7f89c5693a4429fe2712b56910a7f89c4ed5a4431fe26d3b56910e7ea2226d5a4439f68cc9b56910cfea22aed5a4433f68cebb56910efca338895a443afaa22225691097f89c62d3a443edaa215354920deea66aed524836faa22bb54920fbe28884552483fb299a3354920fbca888cd52483fd49563384520fbd2888ce11483edca225584520fe5a6695633483ed6a22558cd20eed95a99a334835de9549b46930fbd2888cd51443fd49553148530f75a5526d314c2ff4b31814c530ff5255605314c27f6572bb4c530df5a55aed314c3fd2956224c530fb5a88955314c35f626d3b5453097f92c26d514c35f64f09b5453097facc26d514c35fa8889b545309ef96caed814c37f4aed31485309df97caed52443fd29563388910fbca888ce22443edaa225588910fb5a8895633443e76a22778cd10ef5a554c53a483bdc956114e920ebf2888453a483b9e99a554e920eb7a889553a4833be56e664e920ef72558458a483f9a9995354920dbea8856d21483fd89553148520fbe2884c5214837da956bb48520dbea88aed21483fd29563348520fbca888cd21483edaa225548520ff6152605514837daaed5254520fb6a88549514827be5b2bb60520ff498354d52482fdab315354920d77a5526d8a48333f9dd6baa981c7f51c26eaa6061ff4b09baa98187fd3c26eaa6061ff5709baa981c7ee2226eaa6071f78cc9baa981c77e5526eaa60717f9dc9baa98187fd5c26d6a4cb1df9549b5a93287fecc4ec9a6071fd8449b629328ff90caed8a4ca1ff272bb62932c77e5546c9a4cb0ffa211b2693287fecc56c9a4cb1fd8455b26932c6fe6656c9a4cb0ffa215b26932c7f61162c9a4cb1df9558b2693287fd1c26d8a4cb8dfa225526931c77e554ec9a60717f9dd3b2698187fecc56c9a6071fb8895b26981c7de3356c9a6079f38ce2226981e76e558889a6079d79563326981e5de778cc9a6061ff6b09b4c981ce7e555aeaa6074ef5309b6098193fecc26d826070ffaa89b60981d3de3326d826074df9549b60981b3bd4c26d826064ff272bb6098187fd else 0xc6bfb4b2aa54931a7fc9c46d8a4ca5ffb309b5a93297fd5c26d6a4ca9ff271ab60931a7fc9c5a95a4ca5ffb309b56932d7ed8226d5a4cb1ff6289b56932a7fc9caa9325465ff6309b5693297fd1c26d5a4ca9ff2715a46932a7fc9caa9524c71ff5493b26981c7fd8226d5a4c75fd4c89b60551a7fc9c6ad835c69ffb318326971b7f49c4c981547ef96093260551a7fc9caa9326069ff271ab4c951a7fc9caa982546def5309b60951a7fdac26d825465ff4f09b6095197fd8c26d325471ff26dab60951a7fc9c6ad82547cfd2718260551aefd6caa9326065ff272bb4c981c7feaa26d326065ff5709b4c981a7fc9c6ad326069ff271854e921c7fd8526d3a4871ffaed8226951a7fecc5489a6069ffb313226981a7fd8c4c89a5479fb6093226951a7fecc4c89a5471ff4c95b26981c7febb4c89a5469ffb318226951a7fecc5cc9a6071ff6095b26931a7fecc6149a48797f61d7b26931c7fd5262c9a4c69ffb318326921c7febb2691a60a9ff5709a46982c7febb61c9a4c71ffaa89b4698297fecc26d1a60b1ff5689b46982c7fd3a26d1a60a5ff5709b46982e77d8554c9a4879f760d5326921a7fecc61c9a4c69ffb31532692197fc9caed854869ff272aa60d21e5fd872697a4c65ff272bb60d21c7feaa26d834871ff5489b6293197fd5c26d834865ff6309b54d21a7fc9caa9534869ff2715262931ebed825498a4c65ff272bb54d21b7dc9c60d534871ffaa89b54d2197fecc46c9a60a5ffb309b54d21a7fc9c6ad83486dfb2711b60932b7ec9c56d824cadfd2715260531c7fd854ec9a486df72715b4c931c7fd8356c9a4863ff4f2bb62921ffc51c609324c7ef96095260531c7fd6a26d5a4ca5ff6309b54931c3fe8826eaa4871df9549baa92187fd8c26d3a4871f78cc9baa92187fd5c26d3a4861ff2718b4e92187fd8c4ec9a4861ff2715b4e921c7de3326d8a487fd295633889609df97caed525821ff6b09b60d21b6f89c56a664c3fb254e668893087fd5c4ec9a4861ff272bb62921eee95a99a224c3e7ca227784530c77e5526d8a487ef8a2222845308ff90caed8a487fd8956228453087fd3c26d5a4861ff2718b5692187fd8c26d5a4871df9558b2692187fc9caed3a4871f78cd8b2692187fecc26d5a4861ffb318b26921c7de3326d5a4870ffa209b56921c3fe8856c9a4863fe432bb56921c7de3356c9a4861ff4b09b5693187fd3c26d8a4861ff5709b6292187fecc56c9a4863fe432bb4e92187fecc26d8a4870ffa209b4e921c77e5526d3a4879d79563326921e3de888cc9a4861ff6315b26921e37e889549a4861ff6b09b54d21c3fe884ec9a4871df9553b2692187fc9caed5a4865fe4b09b56910d7ea2226d5a4435f68cc9b56910d3fa8826d5a4425fe2718b5e910ef71525458a442bfcb315162910efe22254)) else (if i<4 then 0x19028e1d026638c40511c62028a02804962e044041e31c3dc390718138c09c6040080d6823831bc62038801c03002c018014012028ee06e048123e32b8ade273873e18b845e0a380bdfbb7dddf037a3ddbb751dcd370bdbeb6d1dad36a3da1b675d963647d8db619d7f35dfd73b5b1d68358fd5fb549d483503d3fb4edd3434bfd2bb485d1d3457d11b435d0633fbcf7b3cdcf233b7ce0b365ccf332bcc3b2f1cb532b7ca6b27dc9b324fc8cb215c7e31dbc6fb1a1c64315bc4fb121c4130e7c32b0adc24307fc1bb05dc13302fc04aff5bf62fbbbe4af75bd32f2fbc4aef5bb32ebbba4ae8db9c2e53b8dae25b852e03b7cadd5b6e2d9bb5fad6db542d3fb48ad11b402cb3b28ac55b022bbbadbab5dad62b53ac1ab01abc2aa3a95aa45a8d2a23a84aa0da7f29afa58a915a3e289fa20a8299f727cb9eea7a99e927939d1a6f99ab2647990a5e997625c7970a5bd95c256b947a50d93f24a3924a48d922248391ca461914243f90ba41d90323fb8faa3cd8ef23b78eca3ad8ea23a38e4a3818dc235f8d3a33d8cb231b8c2a2f98bd22ef8baa2d98b222c38afa2ad8a7228b89ea2698962247890a23d88e221b882a1f987721d7874a1cd87221c386fa1ad867218b85ea1698562147850a13d84e213384ba11d846210783da0f183b20db835a0c582d20a3824a08181c204780da025808201b805a01180320078009ff17f81fcf7ef9fad7e41f8b7de9f697d61f477cd9f257c51f037bc9ed57b41ebf7ae9eb57ac1eab7a69e7d78c1dd776e9d9d7601d637519cf973a1c6b7169c557021bf76f99b696d61b476cd9b256c51ac76b09ab16a81a3b68a9a196851a0f6829a0566e19a765c9961654193f64b990563d18a76199855611181b60297ed5f717d75f197b55d717035b996d55a2168359c965557c15df55e9569559155f5569555554153f54e953554c151353d94b5517140f4fc93d54ee13a74d093314b312bb4aa92a549911ff47b91dd467118b45b915144d111744190f543910df43690c9431109b422906d414103f40b90294060fcb3f18f793d10ef73a18e213840e0b36f8d713580d133318c6d3170c4b2fc8bed2e50b472be8ae92b60abb2958a4528d09ff27b89d1258092b24688cd223084b20e88291f707cb1eb87491ce06df1b086bd1ab065f18485ad167058b14f84f1126044b10283bd0dc03530cd83190bf02a309581f1069018705a810503d00e303480cd032009f020802900031ff54c9b6292197fd5c26d824c63ff4f2bb56921a7fc9c60d5a486bbf5b2aa5cd81c7fd8326d5a486cff5709b60981c7feaa26d524c65ff5709baa9318ffd8caed3a4874ff26d5b60981b3fc9c56d826065ff272bb549819dfd7caed52607cfb2718254981c7fd834ac9a5469ff5709baa931afecac609524c6dfb27182549319dfd7caed524 else (if i<5 then 0x70285c16070b038581c2c0e160708000002c14206070a17840040d0818182c0c16060c568604c315a100b78c8ad1b8605c3020000000010182c18160c0b0605830340a4182021705084282a14150b03058182c0c16060b03040b40904042d0800001c6056844b0400800e018016707022600500700c01070670281f3c1300b88e330804719840238cc2011c66100804801403001808405cc718181400501700758b81101078c70670251c6040e06d04e1704d03b048638c09c60602804a08001161c088019e31c2dc0d4718138c09c604e302718100500400700c021022300e302718181f00b81101078c70658f70241c604e3020000000a00e018008043014638c0b41800b0101491e302f18138c09c605a0d8080a46742100700c02168369e80a3347ad0b41b8934f14e302718148350200118c604e3103044121038805c40202ef1903eb0ce06e04038701778c3a102270370201c381141209684200e00ce06e04f1903e601c605e30440402e00eb20e04e3cf18e16e1c838c0ac3c0880838138f3c6385b8720e30200000038c0800082402212d089589c0c0a806606e090a02400a00801800c00e02e700500700c00638280a31c620b08e31058471882c218c080b803ac5b8138f3c638838720e302b0f03e016e04e3cf18e20e1c838c09c6040d0e718e06e04052501700781f00b58678c70270341c604e302718e05000e06002538c09c620b08e310104718808238c40411c604e30271810010302078c68259019c605c2c0004905000238c09c6040742101200500400c02181f30001401001c03008607ccf18d04d06e16402100400700c68381f3414400494506c13bc2bc3bc61412602804a044041e31c2da3dc39071810405408b47b8740ec0f9801c031a0c010086028c718100500400700c021811300280200600801080b9801401001c030040084070e718138c0c0a3c6408b83410385c131c1028e17022e0d04103b04c701200400c0050218113002803806002010c0518e302718182738314050094088083c6385ac7b8720e302718118270b01082621c604e3101c501a04b41af18f16048306504046980059000148221d084048014010030084088c018016d06d04044570708968268300129c604e30200800e01802004303e638c09c62038a02804962dc79c3de31c19c0d0718170f78c81f70682070380a39c6202080718100500700c0067028113006005803002b814089805c01e07c02de3160dc19c090718138c080380638180338f4051a029c2d60e075c38064d02802f022b0503b02a038701200400700c383811340dc0d00cb8740c14048010030040e3c05cc00a00e018020705014638c41611c620b08e31058471882c238c792f8578779070ec153809003806002b874089a02804a044042055e31c3963d1014e0ef else 0x40fc170a07e05440381811832e051c1c8602a0c8470ee0c281581f1003c0f880702a0db0a25877061406c4a78201111c4bc104d0ee0c280a83240519c384042452454722b00028270f4280c89618204302225a109d087a176104043022230b6871343860460a04b4215a10ac38607fa1445a044902370b062380a01c100e84306507026070b83860460a24806742180a01c141a85684303f05a280a82d1682e8208e84208370c06f8204b011120360dc5015e0901a33a10c08c198a02a0cc501506a283180d14144068a02a0b44316182882d1408c140a0b60a0506b0142836814141ac138a0ce0bc43241b854048318262419417880b28205d0870e2814834101080308086028570ad0c26860ad08462c230e183481414174178a0460bc501506422926901408c1784b0e0be0c8502370b062381182f14054178a07e0b85015063c0830100c08c1784b0c105f05c2006021141741788e842e16170b0b058602a0cc4b0ee0c280a832100e1c58a0002046e1626870c0540a88e302718100500700c00402180a31c60404801401003008405cce06b0402ef18742038600500700c00402180a3405381b873c61d080e18e30200002802003806010c0898060e101200500400c02181f33c640fb83381c1041318c302e18138c0b86040e18101200500400c02181f3381ac13c640f9d080e1801403002c010086028c718808280a70301768b70e81d81139c62020804801401003002c084070ef1903ee0ce0704104c638c09c604e302038c0809002006002810c089801401001c03008607cc00ad0401801604202e680a01258781f00b78c70370e40001401001c03002c084070e718138c080000a01801604270501460009002006002810c0898e302718180a68778c81f81470e8113c120400044a040c4280e14070f020781020441022081104071c30505a1000000216050b0285816070b038581c2c0e160708180701420000070203810010742c18160c080e06250203818150800092d68c100e04070345ab18200)))
def zar:qs := (475,4,7,0,0,14,0,zaw)
def zav (i:Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0xd2a442bfe4da74a8eff9854a910cff9349d2a3ff68cd7a4433fe95934a8dffabb5e910cffa764d2a3ff68cd5a442bfe95934a8e7fd3226951f7f510ad2219ff6089a5477fcc52f4885ff98b5e910affa764d2a3f769de33443fad2ac66884ff98b4a910dfb2629d241efaa2222443dbd444aa886bfa884a910def4aa95221ef6a2233443fb52ac448879fa889dd10dfb466952213fe62d3a4836fd3bb14886f7a5562910dfb466c5221bfa8898a4437f8a8b148877f09b54510fee2a4a8a217fcaed51443ff1112a2887fd23354510f7e510a8a215fe26d5a4427fc9da54886fea22569109ff576ad2219fe26d5a442bfc4da74886bfa884e910dbf4ee9d221bde9553a4437f511274884ffabb4e910cff1369d2213fe62d3a4427fcada74887fca3388910dfb466ad2211ff26d8a4ca3fe4dad49947fc9baa9819dfad7553034ff26d826072ff3b934c0e77e5526981cfbc664d3039fb8889a6063fead934c0c7fd3b269818ffa564d30357f26d875c71ff44134b8e7de33269718ffb164d2633fe56d2a4433f71113498e77e5526931cbfcee4d2638ffa209a4c6bee4da6498c7fc9baa9318ffb164d2e31ff4ec9a5463ff5d934a8e7ee2226951cfbc664d2a35fd26d815463fe4dd54a8c7fc9b629718ffa764d2e31ff4ac9a5473ef19934c157bd4b269828ff937553051ff4ac9a58e3fead934b1e7ee2226963cefcaa4d2c71ff46c9a4cbfb32ac4508fbe68888a11feacab19c23f759de33847deb4446708f9f6889de11fd9ccd19c45ef3a223388bfe319c4508c7fd5b269328ffb164d2659fd8449a4cb3bf2a9349966fe6626932c7fd104d2651ff26eaa4cb3fb08934c147fd5b26962cdfac64d2c59f78cc9a58b3bf2a934b147fd1b269828ffa764d3059ef52c9a60a3ff5d934c147fd3b26962aff1368d261edea2255483f3d334aa907bda888cd20fdb4cd19a41fd695633483df944422907f725584520ffa46708a41efaa2152483f75332a4907fca3354920ffc422a92417faaed52483fb4a9aa49047febb26931dfe4229d241bde9553a48377d33274906bfa884e920cff136c5241afe6058a4827fd5db14907f695254520dfb466c52415fe26d8a482ff4ada42907fe13148520bfd57690a41ff28cd21483fb52aa42907bea8848520dfe422c5241fd6956335823fe4da7490c7fc9b569218ff936c52431ff4ec9a4863fead93490c7fd8b26921ffa26290a619df9549a4871ff4413490c7fc9baa9218ff936ad2631ff26d7a4c63fe4db1498c7fd2b269318ffab64d2639f78cc9a486fecada629877d89b4c530ffa30298a617f6aed314c3fe511262987f5a554c530fbb4ee98a61ef6a21314c3fb52ac44b07fe22284530fee4ab08a61f7c9de114c3df944422987eea6688930f7d51111261ff28ce22582bfc4daa29847bd4b26982 else 0x5ffabb54d10fef30aa9a21ff660d53442ffcc5aa6887fd9524c530ffe42295261fde9552a4c3f7d33254987f7a555a930bff2b690a617fe62d214c3fbd2ab04887fd95348530bff57690a61fde955214c3dfd44242987fda3360910bff576c1221efe60d82443fbd2aa34987bed8254981fef4aa9d221cff26d82606dff5db04c0ebfeaa60981f7bc66c1303edf95582606bfe4dae6c0ffea224e910bff5769d221bfb88aaa6073fec1934b8ef7e55aa981dbfcef55303ff38ce22607fb72ac44c0ff5e558cd81fbbcef19b03fde9550a4cbf7d332149957fc9b56932ffe2a29d221bdf9556a4cb7ef19d54c0ef7e55aa963dfdc45552c75ff26d835c7fbb2ac22c17dde3361d71dfbc67552e3affa22aa5c7def44466b8ffea2242981aff936953035ff26d3a607df6c1264c0d7fc9b5e981dff304ad221bfe4c95a4433fe99134c0e7fd5226981cffae64d303bfe4ed5a4437fc95ab4887bfa884e910fbf4ee9d2215ff26d32606bfe4dab4c0efde33aa962defcab552c5fd79563358abfe4da34c167fc9a46982dff2a49d2219ff46c9a60b7fc9d254886ff95a4a910f7f51095221fde9552a442bfe4dad49957fd1b26982ffe2a295221dfd8449a60a7fe8dd54c14ffd3baa982dff314952219ff26eaa60b7fb08d54c16fde33aa982aff93755305ff58ce1160bfed19a54886ff98a4e9109ffd76c5265bfd8458a4cb7fcbd274886ff95a4e910eff1369d2217fe62d3a442ffcbda74885ff95b4e910bfdd76c1265bfbaa9824cbf3f2aac6b17f6e5560932dfec2355265bdf956aa4cb77f33554996bfe88aa932feecab08a65efda22114cbf3f334aa997b7e8895532bff31695221bfe6153a443ff308b04996fdeaa4c931febcaa99263ef7a21324c6bfe4daa498cffcab60931aff936c12635ff26d874c67fe95d5498cffd5baa9319ffb1755263bfe4e90a5473fe4dd5498efee22aa931defcab55263b7f9deaa4c75ff4455498d7fc9baa931bff2b695221efba22224c7dbf444aa98f9fe889dd31dff254852a3efea217a442ffb5db0298e7fd8b26931cffaa44d2639ff6089a4c73fec393498eff9534a910dff2a4c5221bfe4c98a442bfead93498d7fd7b26931affb164d2637f7aed324c7bbf2a93498f5fe7726931e7fd104d263ff54c9814c7dfac130298eff9814e920dfed54c0a63ff9889814c7fbb2ab0298fdf67760531ff9b0499263dfd6049a4c7bf711134a8f7de3326951fedcab11263fdd54981547dfac1302a8dff6bb60551dfed54c0aa3ff988981547feb19b02a8d7fc9b4c951efeb024d2a37fe4ed2a443ff5112b4886fee22aa951dfbc67552a3ff38ce22547df744444a8eff98a56910dfbc66c52e3fdb9562258effcc5ab48857fc9b60951ffe302852a3ffa8890a547fed19a14a8d7fc9b4a951cff934952a3bfe60) else (if i<3 then 0x49d305ffb609524c77ff55264c0dffebb4c981dffb56992a37ff62d325477fed5a64c0effd8356921ffdb04992a3ff762d324c7feeada6498dffebb4c951dffb04ad263bffaa9325477ff55234c16ffdab60951cff936ad2433ffaed5a4877ef19ab490fff18354510aff936ad2437feaed32443ff4c1264885ff98b4c910bff2b699221fbe56a664c2ffcada64b07f7a554c960fef2a6a92c17feaed525835ff442b490dffabb54d60ffd444a9ac1fde9550a487dfd4421490cffd5b4e9219ffb169d2433ffaed3a4877bf2aa7490ebfe884e9219ffb16ad243ff68cd52583fbd2aa1498ff7a5562910cff936ad263bfd6055a4c67ff5dab498efee2256931aff936ad2639ff2695a4c7fed19b14886bfe885e931aff936bd2639ff60c9a487ff5113148867fc9b62931d7fb04c52633ffaed8a4c77f71131498ef7e5562931dbfceec52635ff26d8a4c73fe4d31498dffabb62910ffe2a2c52219ff56c9a4c73fe4d2f498fff18254510cff936c5243bfd4c58a4867ff5db1490efde3362921defcaac52435ff26d8a487ff8992a28867fd5326921cffb0a4d243ffc62d51443ff89daa2887b7e8895521bfed7698a43bfdaa931487fbb2aa6290fbf6884c521aff936a9a435ff26d83487efd3bb14886fde33aa921defcab55243affa22aa487faf2ac6690fbde888cd21ffe256a8a217feaed51483fed19aa2907bfa8854520ffd2a4c0a417feaed81483fed19b02907f7a5560520bff576c2a21ffa58d52483ff4c1aa4907dfa7760d10fef4aac1a21ffa88983443efcc3ae2987bfa885cd10bff2d6a9a417fe62d53483fecc1aa6907f798554d20bff576a9a41ffc84553483f7d332a6907bfa8854d20dff2b4b1a417feaed63483fbd2aac6905ffabb60d20ffe422c1a417feaed834437fcb2a74906ff9854e920dff2a29d241efea211a483fbd2aa74907efa664e920f7f5109d241fbe9995a483dfd442b4907ef9655a920fef4aab5241fde9551a4837fca8b14907f7a5562920ffd444c2a21ffa60d21483ff4c2a42907fda3361d10bff576c3a21ff68cd85442ffcada62905ff98b4c520ffe30298a41fde95531483dfd44262906ff9ab54520ffd256a8a417fe62d51483ff8c0aa2907fe95348520f7f510a9221ff68cd52442ffd5daa4887f795354910ffd304a9221bfe6ad514c3fec9daa2985ff98b54910eff136a8a61ffc605514c2ffd5daa2987fea2254530bff316b8a61fde95583482ffd5dae2987bfa885c530f7f304c0a617feaed814c3ff511302987f7a5560530fbf4eec0a61bfe569624c3feca9ac4985ffabb58930fef4aab1261ffc845824c3dfd44264887f7a554c910cffaf64d2637feaed65483fed19aca905ffabb61520ffe422c2a41ff68cd85482ffd5dae6887df9875cd10bff316b9a21efea2153443ff5112a688 else 0xd954b35498547d5462543c542153fb53d5536d5347532c530652e052ba525d524d521c51f651d051b5519a513d50e0507850104fea4fc44f7d4f364eef4ed44eb94e9e4e834e314ddf4db94d934d784d104cc94c8d4c514c2b4c104bf54bda4b7d4b364b104af54aae4a5c4a3649ef49d449b9495c4941492648f5488d4872484c4826480b47f047d547c547aa478f475e4738471d470246e746cc46bc46ac469c468c467c4656463045ff45d945a8456c44f9449c443f43f843b1435f434442e742c142a64280425a41e741d741bc41ac419c4176415b413540d84086403f3fc13f9b3f5f3f2e3ee73e7f3e223dfc3dec3dd13db63d4e3ce63cb53c8f3c693c433c1d3bb53b793b693b593b493af73a9a3a693a4e3a333a0d39d139a039853975394f3929390e38f338cd38a7388c387c382a380f37ff37ef379d374b372536bd36a23645362a35d835bd356b355b3509348b347b33fd33d733bc3354330232b03269323831e6319f313730cf3072302b2fd92f922f4b2ee32e9c2e552ded2dbc2d8b2d4f2d1e2ced2cbc2c8b2c5a2c1e2bcc2b4e2b1d2af72ab02a5e2a0c29d02989294228fb28bf2878281b27df2777270426b2264a261925f325c2259c254a24ed249b243e23f723b02353230c22db2294223721cf218820e9208c203a1fe81fa11f5a1f131ec11e591dfc1daa1d6e1d271ca91c4c1bef1ba81b611b1a1ad31a8c1a4519f319a1194f18fd18b6186f181217cb179a175e172216f11652160015a3154614ff14b81466141f13e31391133412f812b1125f121811c6115e111710d01089104d0ffb0fca0f8e0f5d0f2c0ef00e9e0e200db80d710d2a0ce30c9c0c600c240be80ba10b650b290af80abc0a800a4409e709a0094308db0894084207f007b40778074706ea068d062505bd0576052404e804a1045a041e03e203b103800339030802ab0264021d01cb016e011c00d50078003c0000dffb56c1a43eff56d82606fff5db0690effeaa60d21bffd76c2a43bffaa9874c6fff5db0e98fbfd3b60981bffd768d3057ffaed824c6fff5daa4c0fff51b60931dffb56c1263dff4c89a5477ff552a498f7fc9b46982dffa748d305bff5691a60b7ff5530498effebb62932dffd54b9b037ffaed8a4cb7fed5b06b8dffebb5cd81ffea64c0aa3bff46d8a4cbffac2a6290dffebb5a932dffd54a9a43ffb56d824cbdff5db04c0ffeebb60932eff936b5265bff6153a487bfec1134a8f7fc9b54d21ffbb06a9a437ffaed53487ff68db049977fc9b60951ffeaa4c0a637ffaed825477ff55304a8ffed8256932dffb14ad265dff61c9a4c7efec3af498dffebb56932eff936ad265bff5498a4c77fea9b1490dffebb46932ffdb048d265bff6291a4cb7fead234996ffeaa60d71bffd76c1ae3bff5a95a4cafff5daa498dffebb4e982dffd5)) else (if i<6 then (if i<5 then 0x1681813303718b4518a103a8b620608cf38c31c940e818c130371806cca081338c07e0921a99c63031040fcc30263303504099c603f048651ce301690304e5606a09c603e04e5504e3009c35048504261dc628e40604cc055c620311c09caa39c62030270bcae3101a8e026430f8bdc620351c5c5e609c620350c540ec0dc628204e530ea2d8830263ce3187320438270ec0d8738c0766022e081838b50ee3187303403c70e029c5819718c1981a824b8270ec0d8738c076670405dc5987718c0d871dc5b87718c1a1f18260675060bdc608e000530ec0d8738cc5e5606e30c162f238b61ce1d81b82718e781ea00fb82060e41c630b51ec3900f20a39251ea79c6306616a0d30500538f078e0dc6306616a092e09c398361ce301d99c1017720c2dc618f61c7316c0d8738cc5e5042e30c7a8e03006cc06947415036e300c181d00d71860800140d01b718a380c14c1b8c51c000882cc7b8c51c433c63dc618350c0e8c609c6286000430ea4185b0263ce3187320431260ec2cc1a8e7186624c40c7a8e718c2ccc494319e306c2cc7b8c3b14e0ac1d88286616609c62183a9030467985b8c31c760ec1941982718000c62d48307604c79c630e640895aa3d4730b718570ee1981b020125839b8380835a833f831982f382cd82b2828c82668235821a81ff81d981a8818d81678141811b80df80b980888062803180167ffb7fd57fa47f7e7f587f327f0c7efc7ed67ea57e7f7e647e3e7e187e087dcc7d9b7d807d5a7d347d037cd27c967c7b7c3f7c0e7bdd7bb77b917b6b7b457b1f7b047ade7ab87a877a617a467a1579fa79c979ae797d79577931790b78da789e78837852783777e57793776d775276ea76c476a9768e7668764d7627760175e675c075a5757f7559753e752374d1747f7422741273f773a573747359733372cb726e721c720171af715d71377106709e704c70266fd46f826f1a6ef46ece6eb36e616e046dde6dad6d7c6d2a6d0f6cbd6c606c036bdd6bb76b5a6b3f6ae26a906a5f6a396a2969f869d269b76991691e68cc68a668806865684a683a682a67f967d367b8679d67776751672066ef66d466b9669e6683665d6637661165eb65c565aa658f657f6559653e652364fd64cc64a66480645a6434640e63e863c2639163766350632a630462de62b862876261624662206210620061e561d561af6189616e6153612d60f160d660b06095607a6054602360085fe25fb15f8b5f705f555f3a5f1f5ef95ed35ead5e7c5e4b5e1a5df45dc35d925d775d465d155cd95ca85c775c5c5c2b5bfa5bc95ba35b885b625b475b2c5b115af65adb5ab55a9a5a7f5a595a335a0d59fd59e259c759a1597b5955592f590958d858a7588158665835580f57e957c3579d5782576756f456d95692566c5646561555e45592556c5546552b54 else 0xc83706a0703082d8338c306a092e314118f07c451ee310742d202c7180c50718328217188394791c618341ca1c80f9c620e51e440ce30c128f228f61ce32169003a8361ce300d950928703082dc630e30670140491601f01604408246718a3d872d47b0e7190b48e318703b1e0540ec18c138c0006424c18cf18f306e300d1c132125168418718f718740e60d8738c000503a06c0d38c61c060c06c0d30e7190540c1a02b0604ce30c1018301b31ec39c60182b1260e62dc628361c63160fd09210026e3147b0e4001606a09c60292b878400654129e718c2d8828e492c828e2c22b8f872e0dc643e81aa716e3e10306706e30811d8300a0521110138c00383541a5c618331f8348e30c7e0d198bc28e330691c6183c1a371605dc838c60c63d811e0a18b71f07dc1b8c60cc091045c5b87718c18c1b023b8b60d051c621e41e80e1a20c931e718c0d87e38318b63ce3181b0fc706828e3e05383718c1985982401230ee3141b0e0266306c39c603b2212616841c618f61c6424c2c0d19e31ee30c1b06461440a81d08306036e30c130b4b8270ea0d8738c0766343051c101902c4ae1d12c70609dc7b8c800c39d029c5992718c1981b0f63c870462dc838c800c3d871dc130f716c39c638385a742482d83b8c306c38c8490818b718c3d8719c583c720e3187c0d338261ee2d8738c706094e0f20a38b63cc0dc6306524c3d307dc918b61ec79c63066068705045c5b0771860d871c04b03604e301495c3b8612cc0d8102931a187ce2dc3b86000005c630384ec097045c399063ce318130b61c802ee40c3b8c616c398131e4190604c79c630ec86630ec098f38c61d90cce09c3b0331ce301d99c938b30ee3141b0e3387716c19c62833046724e4145b8c31ec38ce4945b0633c63dc61833b8570ee4145b06718608ee2cc930653ca3dc62833b87516c40c119e718638ee1dc328b718c0cc119c9387316e3141b0e342030ee080bb8e718c2d81a1c3b86606609c6029330331ce331410c3e20606e331414c119e71863b1415819827198a0868610016256e1d85828704109c741b71800581b903a0b048619c6303604702ee2cc3b0263ce318830e43873170808f38c20443a20a0c5b0263ce31876413187604c79c630ec826044e2dc3986718c09819dc3b86606c09c602930c00020a5814352b8770c00414b027190d4f07dc398b604c79c631061c851c06e0ab8c0305616c1943b8c304c0ccc2d4398233ce318818e3b0760ca2dc6182606660ea2cc119e718c40c71d89320e0861d8328b07ce3181a583b0b50ce30c1303331261661dc628e6066624c1d81a8e71809cd8c4c138c406a1cb8c508182718638cf2873b8c406a1c1390c738c406a1c1395c60130490c48e301720304e4704c39c7b8c076542481d45b0331ce30121cc3a28c50849106045) else (if i<7 then 0xb8c6052a0ee31c5a8f60402b068443e20483c10788120f041f046402800a1805387716e3181303342950ea19c63036040a4c046c2a0c30e0c4ac09c6303052004a63045a90189030e2c5ea4058bd4809c3b10022a794138c51d8a10e1dc630230cc0c149a17a9030e3048c40461981387718e2e1a980fb0270e62dc338c86a7125611480e1338c87ec0a1ac243235620246ac40412581c267181218143f848862009c58bd480849584518a2c90281803c70ec2dc338c606a09263012094608bb0a351822cc38dc64151484118211824042302e310909c620b118c4168810810c62124163450c4048a188091431012286202620162016201620190810140cd060cc621241637180ed0301f218c42081866310801b40c462507dc630e96258280c1c3840016001c6282507055505583809506a09c630680088690514f38c60ca0d47c3a439261ce1dc618382a6724c39c639031f054d015c2b87718e40c14153aa11162837069c612c256c3a0ac184215030c2c685585890a81a616342a06d858e4a78570e0241602b836e318741854850b0b000261616161543614480f1c685130b07ea487e15c3b9084ee30c1415078882a648c3b0e71860e139e0a987306e30c1427303c82a64a1a414616678c1b8c60c63d604417187180a06361702187280a051810c811c938c31ec381d83c3392928e1dc630633c60e0a83c4f8570ee318301b3040ec1e21c6210050360c1034c18406d830a1460d70ae1c0d83b71864141260038570ee301f8006162082226c220c01a06c8a480db0b1800524c2c60f94930b183a524c2c700214427088e1d8338c10660924180d9820780ecac1c2c1c2c2c303706b8c716a08c1823382570ae31c582660e20822218380d04ca488a49838949307129207cc1c72a1c630e506004a81cc142d08840762304a1c2c1916b071b0645ac1c6c198389833071092b08a1c6633022141f046402908185b00183b8c504a0c009c8399213070b070b92716e3183b0e5060f0ea4b4228c516a0e16830380a06462c6a2c18392718e4187b0e3420f12028198949685d08a314803085a0f118e34289c9784718e2cc1c2d0607d0a11c4e4bc2f84718e42168303a870b92718e2d8718385a0f0f0441842d324848c5b07850e30c1b0e5a870c0a06062d05c2d800c1dc618360c609624ac26851c8410e2724e30c5b90060c3d8742d0789624a2ccf183718c18c79d45b126200f9c618f61c760c099c62833040fccc0dc618e036460e00185b8c60c609419d85b10718c18c128f322fc5e81c0da0b60ce3141982498745f8bd0920b04ce3141b0e4b14e0ac1d8828b718c18c1218930b30ee3141b0e330b324a7941b8c60ca3ce84903a83718c38099945b03304099c6024320dc1aa4905b0671860cc799e4a1060c63dc628207c6c0a8418338c5040f8 else (if i<8 then 0x543a9084ee31414150788525134240e06a92d0861c861e138190784524a1dc629e82aa0c1e1cc8207100a70ee31c5b035040f0ee15c3b8c000c401e28231688400c1c3b8b718c0d4103c418cc080fc6633020261b87718e2d818115058bc1e20c8207119287d07cc3b0e718c0f17a205187316e3181982c5e724264ac2207212131681c6c402c400c027516451604d880d45b101000516c407044493120610be1f38c61ca2d81aa08b0760ce31413039647c1aa4b420d17813620345ec4048bd88098805880490d8532081c80b5438491a2d04e245aa1c5a1012107180d014a1868374203f50c441ba101328620330582b0881c462d03891928b1026464a2c60611928b189261821868511b68518491240806028248849087108b082e03ea1c68b8138917287101b45ca1c608021d05d084087a10100d21e844403064029458c1223251630640b1458c1004b41830140cd060c0882d41861c98bd430b1428c5163c50a31458f1428c5163c63a15438f18e8550e3093105430872641d08a1878bd43081682404c352414661316818481828511a6851834029a1460fd198824827100a09321060544903f03622ca85543090aa860363a0aa1c4a1c168805049908305a24813087218740c2459a15438c09a2cd0aa1c80c416287188b120212421c443143894382d100a05921472b586287188761806c60b586287056445ac314381820140572118610132325163070051866852214470c33429186000100d014c31431106e84618000809906e84618a18a8374230c074404010486684268420e2082081866842220482c3342101230c5208ac806d142901a2852023061301e0c25820124b4402066028409119881fa331036029a14624845880a02c101b458a1c606116287182e058a1c622c224843880502c158503081878a14838c1e28520e3078a14838c1e43d08e30604415c856184908c30158002026458a406a18838817811618a1888bd862861a2f61800060fd162901835058a40622c48094338c140d963435c638b048a1d83083204a518a2c4c180538c404a0c1499c621006a3718818050cc621007e81886310802640c496ca0d8338c53ca3e1c9c1da8c5163080a2c158d06b12140a316e318f30361f8e0e834133121a0d6242e08c485c11890b8231207c3e08c4858a1463101e28518c406e4a5078470c044d0b8c6078a12a3145987198c440241a0fd890d21e20e083487883820e0a43260cc79c630361f1290c4026310921440c4471853828d1c614e0a3e0ac5058358109c3b8b718c0805283c1a0f11e15c3b8c516c080560d0888851435c3b8c052c19458832049718e2d8329e51e02941e0d07890140d4c80c08828320382261cc5b8c307834d044c598771860f0698c5c1471860cc7e0d318c3162b0a6404a3145894628b140a60ec1941 else 0x259504158560c28650bd880e17c32143385ec4070521a43a1c346172506c18148a0542f81a386b056138e18c0d625c109001858a00504103085ac1c705742a908624604a1840a7422861d85d0861c70561ac001c0a0530a21ac322c1486d0e47047144358644965410880e1b312e092508a49838814d841192516c40728314441886485f0b9458c14d85616381404a1a8e0881086a3d0810610ccc90c11c2d60e1108a1c1842e1887620285d0bd880c14d84616386a152561411990616586ac1d8300124350022125a16140c14e8550e3078c1a0ac942092874c2d481208e288a10c6171581a87103086361702190283085d8121f1208e2885f05482481dc281829076a1860eec29871c38a2912870518284f1e85b082863056138e14400864301702814c35208704709c7036140a1440d625c1092a282881830760c00492a2820818432c0ac40822d83b061b060530a06c1ac2c281c2860ec1800921ac0061608c2216140011006815a121a9282d041392718e2c08b0e6060c0f051c5811718c39818233e0562004c662d0389c938c7166858181161d8bc1e241402c520312422c402816080882c90a330ee304080274851a20450a40622c48081004e50e3c0ac4040814384e1a4e50e88078bd830b17b06128b022e49c630e6060c0ea2c05387718c0cc103c3c11060e49c3a8b718c0d8720c604c601b1306014e31c5b033040c0e8812768550e4518c185835496841830725e17c238c72007cd083c4b8571808c1f01b616110c1200f82361ce3185a8f08876160604e4850b8c03ec39478443a92d0ae300fb0e0760f0f83549684198c50a8410a118339270e285c601f53ca0c1e2605187316c0dc6182c5e7c1aa4b420cd080af0ae1dc62820887800e1dc6044616208c19e0a3858400c1c3b8c616a082224c66040303319810130cc6604178570ee300fb0b504110fa1))))
def zaq:qs := (632,3,7,0,0,16,0,zav)
def zau (i:Nat) : Nat := (if i<1 then 0x1874091e6310e90ce8a304c7b0685b18471fbe2ee0fb2eeb67a84e8979d0e5ef91ce27f82cdf8778cdcdf6d8da0f624d69f52ad28f41ccf47372cc4f2bec92f200c65f14cc3df0a2c136feebe66f44bb6ee90b8c6de6b66ed5ab416cb0b146c1aaf16b7aace6aeeaa66a44a7e6986a44e8aaa0de7c49d466de99ae616970659495264b891b64048e963468bee27e878e16683ce08080d5fea7ea5f2c7abde3276d5d10724dc166eb5b586be5aae6965a04669595a64158a661458065ec575c5bf569e597561c56f557254754c851a540a4ed537e4c552c049fd22a472d19e454d0fe42a5068409cfd23df4f283b9ce8838a4dde35fcd203354c943124c082eccb5e2c74adc2a44a4628149ba25e4910231488420e47ee1e6473a1be46b819b4622175c596152c50012ac46010543c00dac3200b5428a08fc1ea06a415403fc096012c000fff4c951fff60951fff4e982fff46982fff56932fff5e981fff5a932fff4e981fff60d21fff60d71fff54d21fff56981fff62921fff62932fff56921fff4a981fff61521fff5cd81fff54931fff60931fff61d31fff62931fffaa931fff4e921fff46932fff54981fff56931fff4c981fff4a951fff4e951fff4a931fffaa982fff5e931bff56921bff62921ffd4c521bffaa921bff4e921fdf95521effa2121ffe42931bff56931bff5e931bff62931dff26931ff78cd21ffe4c520ffe62920ffe5a920ffe56920ffe4e920ffe46920ffe61d10ffe61510ffe54960ffe5cd10ffe54d10ffe60910ffe54910ffe4c910ffe62910ffe5e910ffe56910ffe4e910ffe60d10ffe42921ffe54d60ffd60531ffe4c960ffe60930ffe58930ffe60530ffe5c530ffe54530ffe54520ffe5a930ffe4a930ffe46930ffe61520ffe59520ffe60d20ffe58d20ffe54d20ffe60520ffe48530ff78cd81fdf95581f7f9dd81ffe42932bff5a932bff62932ffb60932bffaa932ffd84532fdf95532fbf99932ffb88981fbf58d62bffaa962ff78cd62fdf95562ffe42982dff26982bffaa982ffd84582ff78cd82bffaa963ffb88963fdf95563effa2132ffe4a910bffaa931ffb88931fdf95531f7f9dd31effa2131ffe42951dff26951ffd60551bffaa951ffb88951ff78cd51bff62971f7f61d71bffaa971bffaa981eff60981ff78cd71ffe42981effa2171ff74c931f7e9dd10fde95510ff68cd10ffa88910fde955609ff26931ff988a11ff58ce11efea2110f7d9de11efda2211ffc54510ff38ce22bfe62910fbb99a22efba2222bfe56910fb799a33bfe4e910bfe4a910fdd95611ff64c5309ff269329ff269719ff26921efea2120fbe99920fde95520ff68cd20ffc845209ff26962ff68cd60ffa88930fbe99930ffa549209ff269519ff26982ffa485209ff26981bfe62920ffa88960bfe4e9209ff26963ffc84530 else (if i<2 then 0x81ae4361c822798c238183c51c230ec3106c60367e158706c8e6301830140889245a164320c1990ec610481b0111248b42c4b080872798c209102398050222490e8390c8306445b1881904c1248741c4304c2022c9e2098c4408e603e088921712489508906084320c1f11643b1881c00a1248741c8b42c0d0918c2190320980883e159248910e8385e85b184191ccc37056143f61d904188b63102561a13316c820cc611e81230d1458b4198c23c834489e4f08c3836c620714048761d0b442202798c2088e40520530ec3216c62064120298a01161d866310b00c82486ec3b04c731881c507ca0246498742d8c23903465182308c930c8590ec62069ca18742c822798c4408e461ac3b168331841a04761c1e6308b0091003a204316c3c40c62048f21d20a34161d204408b631024790e4e82c5a408810ec62048f21c940c26631020fc24330ec331881a041498350018b8d5876198c40d024848c3b164331881a0470a43f61d8622d8c40d024320c3c408f3188720521a34361d2042c904798c439024e86c82408590e8f318872049ca01b61d8642d8c20903445e87106c607a58501509d828558f42d836310e50760c324c3a16c61068721926410b6308f438c0d3248311e4f318859068c158506d87641066310b2092c621c8784a46098b6418c4390f8b4f0684cc5b201e3188790480b58262d906310f438254324c5a0ec61068719926408b6310f438cc592483428c621e81a3c862c1e6309203c0341a144324c5c28c623c87a071c210662d8f63183834c22014c5b0e83004c641a41a738649144188b6311e43d034b2028b188104d0687e7ce18b451062498c4790f40d3140760f888c130ec621c41a59262c9e20d066308f3b04c5b20c611e8719146098f22d836310e3b04c5b0ec610687198b640874091e6310e48110a304c1a16c7b181da1c86098762d8c20d0e3304c7916c1b1887191462d8f60d06630823b24c5a0c4f11ec6106762d8f41983630823304c5b2012b180711e761d8222d8e63103301b06828c5b1e83306c607c41298b61d102089e6308e3b16c3b0cc62064118256098b6418c23d0e3b20c3a164113cc611c70518222d8363d8c0010e405f17b0408b16c3b1841a1c96098b6418c23d0e330605b1ec6000471a2061d8263903632283b24c5a3c81b1887c7076098b61d034398c8bcec5b0ec331841206662d872089e4418c238e90316c110ec7318819d2061c136088b6398c40d0c1048c5b0ec611c819d8b61d024798c43a413b20c39168123cc621c90212061c186098e42d8c20d0c830e4113c85b18471d8e6080321d8c8c4273c5ac1316c831887a1c762d876182963103408f17b04c5b0e08b180191c88518b63d836320d307cc5b0cc3b188184e41218b61c904091e6310e4810144501030ec102245b1cc6206a64 else 0x1845b14116c955083b1887106a0c2350958b6310641c8220d245814c3b0c14b1881a0488d40a61d8b2198c40d02410ec9708c3022c62071421066318b2788f028830f20d4a20c38224f104c611d14208be15876310202a0d1111190795930f97916c610481a63222d068511424b38ac98c4790f40d8180791745f97b2443b1845a1c81ad8c62c8f4080a834443b0ec6316818224145e1e202961d860458c209038a1043b24c63168702281c5e1e25876318b4080a20c3c8351178601e31759e5ec610481a6360f214ad894c348b4498c23c8327990ac63138602204ec956285b1887106c8d6158022709c44001874198c42c83209a1e42b1a1295a4284920c85b184793c41b78561d0b6301f208443b24c2b0e05b180fa1d0a88890ed9261d8c40c1143a2f0f121db24c38224731881c5080c03c836b1c358b21d0663083409685b24c603e8711e221c3c8a2a8c358722d0663083409483b24c6316871061e1c306498c6408b4390f0f10c930ec603e1da1c4187884400a61d8b6198c40a354128c930e85b180f93c418789044306098b21d8c4390340141e316c3a0cc620641201804c3b609870f18c22c0e40d4c1316c3b1881a1d179c3b0443c6098722d8c40d0e4e5ec931643b18872067cbd8762d066308240cec38340db1887030607c306099042d8c23d0e432485a0c4f11ec642841a2140283c63d0b41983630824b04c7b18870765cbc136498722d8c40d0e402a8920e81b184704e761d0304d8c208243482c39044f3184702678c592e101321d8c40c244450c9708c3a0645b1812222f6498740d8c23813385845a160a0684913c41b188311eb0282c22d0b241100cd8c4188223d645a1643862c62044821c8f240a0b092448140d88b2790620d8c23d60f92489120880581f116c621c47ac0a21d0722d0b0b0006310620c82582218924891168585843b1887106b0442c2491221d070a08b6310e20d706f0ac3b16c820cc610488e19262d06278836308f421c47b18129192e15876408b6310e38141650a8a60a43a0e48220191168331841399261d8c439038bc13390e482201721cc623c45a04902a0d0fc1b63c3c60d8c42c82485083a404823c813188706e941d060ac8363082000e0f85643a0e100824813c41216c611cc0281f0ae854530521d07241100348642d8c209e0f856492240a0704313c8591ec6106c07c2b24912241100b50b6308e23d624924891168585a1210ec611c))
def zap:qs := (175,2,7,0,0,14,0,zau)
def zat (_i:Nat) : Nat := 0x97a09168746038067a188240904382c3c8c0700948b43a191803011a82209022d0e10460083c0e54a10e8205a3918033c35168f0320d18023ce028928a22c0c8c0f03c06a12a0916904603c1c74123c168346038c144122d1e8346038e1410279048f41a38168c4a2d208701079180e1021048b47a0d180e322d0e82472300664f2091e8305a3918745a410e020f2301c71022d0e82472300679110a5f738f696c1d54264452794c794220e33044044001ffd21ffeb1fff60bffac5ffd32ffec0fff5c7ffaa3ffd31ffc887fe4c3ff2c1ff611ff7117f78cfdfccdff920
def zao:qs := (17,1,7,0,0,11,0,zat)
def zas (_i:Nat) : Nat := 0xf0581078187061fff
def zan:qs := (1,0,7,0,0,0,0,zas)
def qnx:Nat -> zi × zi
  | 0 => (0xcddcc7c4a2dee7f2f2deba882567efb63ba2edcfdbe56efea820eae15cd76cd87a341824f7bec63379db47974a24000000000000000003ffc003ffc000003ffc210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f,0x40008905104005228290134290e0b8001800b80c840800041063040000910820e02881240c88811820a804b20115115115115115115115115115115115115100007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07)
  | 1 => (0x34016d74d438f135ce925f3fbe8e17b5b8db1b67a5f9f4814135d2eeb3f4314fd93c08e7eb23361e47dffb6b7ad4000000000000003ffc000000000003ffffffe0f82017c010fc20208423f0fc21e208410884411044517e1f805f05e7c20279,0x408121042000000cc20418c280800002d018440430030cc1b008c0045d700430c01040603201144841515db0004208e08e08e08e08e08e08e08e08e08e08e08fe0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038)
  | 2 => (0x806eb5465011185759d2c4cdac8c8d2e6be81b7768680a041e0bf915facf27e74f309ef07bc3b7fe4419d99c324c000000000003ffc000000000003fffffc000421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0,0x8464000101c84e001820820006504da00000005004b0701c0804001302828300000b80810114c000080402060400c50c50c50c50c50c50c50c50c50c50c50c50000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0)
  | 3 => (0x532a30488f499c39cb23b627c2a789ee8af83f341f919f7a319e163a6f13b9ed1bc3357ad3f79f46cece6633c368000003ffc000000000003ffc003ffc00000084208421082110448ffc0044fffe00109f90089ff08802085ffc800897ffc480,0x11831ac50020146210514420828100c340c088a290503004140a0000009008c0a10034040820060830a910020001a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000)
  | 4 => (0x5b184cc33297c4ee682b04eee4ee13be03c1d2bf176771fda3272707bfa2ff3bbdc0ff1c1c65ccdc3307166e1d34000000000000000000003fffffc000000003ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff9088802,0x820002410cf95221c2500000d0002040ca004071121848a2b4a9010a9a504021212034051e34650070540c808aeaa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000)
  | 5 => (0xabccdedc25eecab1d459531ac953a109d62da6eae3a08a5f8cff148269895e97813acff167591d13fb5c75e384c8003ffc003ffc000003ffc0000000000000010842084210822109042108882108917fffffc00802010fffffffffe000101004,0x8154404a82205414400030000542410044053268c20010809002103108310002060012504640214244100400406c06c06c06c06c06c06c06c06c06c06c06c0000000000000000000000000000007fffffc00000000fffffffffe000000000)
  | 6 => (0x8d5570ff38a23e462f760008b2255ed730bad502dc3abda45b389b8eabbe191d2feca3c4f0f9e1f16ee9f44538bbffc000000000003ffc0000000000000000021084108421044213ffffff004001007ffffffffffffff0100400040102000020,0x167898b95fe227c3240b06050f3ae21d0d441ab0024c9116010610d90208b084028b0a050126a81282a6004cf4003703703703703703703703703703703703700000000000000003fffffe000000007ffffffffffffff0000000000000000000)
  | 7 => (0x3cccd357975f9b69ac7b42663e6100cdd38c5649577da3da5f8b690d6e001f4d4ecb47e70c649f722f14ff644398000000003fffffc000000000000000000003ffffff0002080003ffffffffffffffa108211000041004208821085000002100,0x1102aa9a221110da220945fc48878042cc0a2fa05042010202e2d30c60213ce9a284140e5ae2189cc301a4313863383383383383383383383383383383383383fffffe0000000003ffffffffffffff8000000000000000000000000000000000)
  | 8 => (0x39203cefeb8ac927f6d5233b0a756adfaf77a2b2f892012df8f773fc240ada23f1cbe9625c529ea4a6f1fe44c49fffffffffc000000000000000000000000003fffffffffffffffe084210008210004210422110882228411042108004210000,0x40874202a01190081a30a09890410902009284041020008882b00b0664460040054010988259108420502a8002ebc03c03c03c03c03c03c03c03c03c03c03c03fffffffffffffffc000000000000000000000000000000000000000000000000)
  | _ => (0,0)
def qny:List vp := [(260,8,739,16,7,1),(34,1,460,16,6,2),(320,0,1215,0,11,2),(132,0,1403,0,11,2),(64,0,447,0,13,0),(128,0,383,0,13,0),(2,0,1533,0,12,2),(32,0,1503,0,12,2),(256,64,701,2,10,1),(8,16,486,1,9,0),(0,256,663,104,9,1),(8,0,1527,0,12,2),(16,0,1519,0,13,2),(258,64,701,0,9,1),(66,0,1469,0,11,2),(160,0,1375,0,11,2),(4,0,1531,0,12,2),(0,4,881,138,9,1),(256,0,1279,0,12,2),(8,4,881,130,8,1),(0,128,859,36,11,1),(10,0,1013,0,9,1),(0,16,486,9,10,0),(0,32,94,385,8,0),(4,8,739,272,8,1),(32,1,460,18,7,2),(128,8,611,276,8,1),(256,8,739,20,8,1),(0,1,460,50,8,2),(0,16,486,9,10,1),(192,0,1343,0,11,2),(0,8,739,276,9,1),(0,64,701,258,11,1),(1,0,510,0,12,2),(0,2,440,69,8,0),(257,32,94,128,6,2),(2,4,881,136,8,1),(35,0,476,0,7,2),(32,256,663,72,8,1),(10,4,881,128,7,1),(12,0,1011,0,10,1),(268,0,243,0,7,0),(64,1,396,50,7,2),(25,0,486,0,8,2),(3,0,508,0,9,2),(34,0,989,0,9,1),(40,0,983,0,9,1),(6,0,1017,0,10,1),(1,32,94,384,7,2),(164,0,859,0,9,1),(264,0,759,0,10,1),(288,0,735,0,10,1),(384,0,639,0,10,1),(388,0,635,0,8,1),(136,0,887,0,10,1),(12,64,689,258,7,1),(130,0,893,0,10,1),(136,256,535,96,7,1),(384,8,611,20,7,1),(14,0,497,0,7,0),(1,2,440,68,7,2),(7,0,504,0,7,2),(40,256,663,64,7,1),(8,256,663,96,8,1),(1,16,486,8,9,2),(68,0,955,0,10,1),(96,1,396,18,6,2),(72,0,951,0,10,1),(5,2,440,64,6,2),(4,2,440,65,7,0),(33,0,478,0,9,2),(129,0,382,0,9,2),(257,0,254,0,8,2),(5,0,506,0,8,2),(264,128,595,36,7,1),(96,0,927,0,10,1),(128,1,332,50,7,2),(2,64,701,256,10,1),(65,0,446,0,9,2),(130,1,332,48,6,2),(4,128,859,32,10,1),(128,256,535,104,8,1)]
def qu6:List (List Nat) := [[],[81,130,118]]
def qrd:Nat -> qs
  | 8 => zcr
  | 9 => zcq
  | 10 => zar
  | 11 => zaq
  | 12 => zap
  | 13 => zao
  | 14 => zan
  | _ => q6
def qu5:Nat -> Nat -> Option (Nat × Nat)
  | 9 => qf 1 5 3 5 0 1 (qt4)
  | 10 => qf 4 29 5 9 4 1 (qp1)
  | 11 => qf 178 2485 12 14 9 1 (qp0)
  | 12 => qf 255 3577 12 15 10 1 (qpz)
  | 13 => qf 74 761 10 13 8 1 (qpy)
  | 14 => qf 9 89 7 10 5 1 (qpx)
  | _ => fun _ => none
def zj:qx := (1535,14,3,qnx,qny,qu6,qrd,qu5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma qxn:qi zj (qt qe9)=true := by
  unfold qi
  refine Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply qk (d:=6)
  simp only [q8]
  repeat' apply And.intro
  all_goals decide +kernel
lemma qva:qc zj 8 0 1=true := bOk 9 (by decide +kernel)
lemma qn9:qc zj 9 0 4=true := bOk 9 (by decide +kernel)
lemma qn8:qc zj 9 4 7=true := bOk 10 (by decide +kernel)
lemma ql5:qc zj 10 0 1=true := bOk 9 (by decide +kernel)
lemma ql4:qc zj 10 1 32=true := bOk 10 (by decide +kernel)
lemma ql3:qc zj 10 33 32=true := bOk 10 (by decide +kernel)
lemma ql2:qc zj 10 65 32=true := bOk 10 (by decide +kernel)
lemma qkc:qc zj 10 97 32=true := bOk 10 (by decide +kernel)
lemma qkb:qc zj 10 129 32=true := bOk 10 (by decide +kernel)
lemma qka:qc zj 10 161 32=true := bOk 10 (by decide +kernel)
lemma qj9:qc zj 10 193 32=true := bOk 10 (by decide +kernel)
lemma qhh:qc zj 10 225 32=true := bOk 10 (by decide +kernel)
lemma qhg:qc zj 10 257 32=true := bOk 10 (by decide +kernel)
lemma qhf:qc zj 10 289 32=true := bOk 10 (by decide +kernel)
lemma qhe:qc zj 10 321 32=true := bOk 10 (by decide +kernel)
lemma qhd:qc zj 10 353 9=true := bOk 10 (by decide +kernel)
lemma qhc:qc zj 10 362 32=true := bOk 11 (by decide +kernel)
lemma qhb:qc zj 10 394 32=true := bOk 11 (by decide +kernel)
lemma qha:qc zj 10 426 32=true := bOk 11 (by decide +kernel)
lemma ql1:qc zj 10 458 17=true := bOk 11 (by decide +kernel)
lemma ql0:qc zj 11 0 1=true := bOk 9 (by decide +kernel)
lemma qlz:qc zj 11 1 32=true := bOk 10 (by decide +kernel)
lemma qly:qc zj 11 33 32=true := bOk 10 (by decide +kernel)
lemma qlx:qc zj 11 65 32=true := bOk 10 (by decide +kernel)
lemma qj8:qc zj 11 97 32=true := bOk 10 (by decide +kernel)
lemma qj7:qc zj 11 129 32=true := bOk 10 (by decide +kernel)
lemma qj6:qc zj 11 161 14=true := bOk 10 (by decide +kernel)
lemma qj5:qc zj 11 175 32=true := bOk 11 (by decide +kernel)
lemma qg9:qc zj 11 207 32=true := bOk 11 (by decide +kernel)
lemma qg8:qc zj 11 239 32=true := bOk 11 (by decide +kernel)
lemma qg7:qc zj 11 271 32=true := bOk 11 (by decide +kernel)
lemma qg6:qc zj 11 303 32=true := bOk 11 (by decide +kernel)
lemma qg5:qc zj 11 335 32=true := bOk 11 (by decide +kernel)
lemma qg4:qc zj 11 367 32=true := bOk 11 (by decide +kernel)
lemma qg3:qc zj 11 399 32=true := bOk 11 (by decide +kernel)
lemma qg2:qc zj 11 431 32=true := bOk 11 (by decide +kernel)
lemma qg1:qc zj 11 463 32=true := bOk 11 (by decide +kernel)
lemma qg0:qc zj 11 495 32=true := bOk 11 (by decide +kernel)
lemma qgz:qc zj 11 527 29=true := bOk 11 (by decide +kernel)
lemma qgy:qc zj 11 556 32=true := bOk 12 (by decide +kernel)
lemma qgx:qc zj 11 588 32=true := bOk 12 (by decide +kernel)
lemma qgw:qc zj 11 620 12=true := bOk 12 (by decide +kernel)
lemma qlw:qc zj 12 0 16=true := bOk 10 (by decide +kernel)
lemma qlv:qc zj 12 16 16=true := bOk 10 (by decide +kernel)
lemma qlu:qc zj 12 32 12=true := bOk 10 (by decide +kernel)
lemma qlt:qc zj 12 44 16=true := bOk 11 (by decide +kernel)
lemma qls:qc zj 12 60 16=true := bOk 11 (by decide +kernel)
lemma qlr:qc zj 12 76 16=true := bOk 11 (by decide +kernel)
lemma qlq:qc zj 12 92 16=true := bOk 11 (by decide +kernel)
lemma qgv:qc zj 12 108 16=true := bOk 11 (by decide +kernel)
lemma qgu:qc zj 12 124 16=true := bOk 11 (by decide +kernel)
lemma qgt:qc zj 12 140 2=true := bOk 11 (by decide +kernel)
lemma qgs:qc zj 12 142 16=true := bOk 12 (by decide +kernel)
lemma qgr:qc zj 12 158 16=true := bOk 12 (by decide +kernel)
lemma qgq:qc zj 12 174 1=true := bOk 12 (by decide +kernel)
lemma qlp:qc zj 13 0 8=true := bOk 10 (by decide +kernel)
lemma qlo:qc zj 13 8 9=true := bOk 11 (by decide +kernel)
lemma qr6:qc zj 14 0 1=true := bOk 10 (by decide +kernel)
lemma qpq:qp zj 14 := by
  intro k hk
  interval_cases k
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . rfl
  . exact qva
  . exact (bM qn9 qn8)
  . exact (bM (bM (bM (bM (bM (bM (bM ql5 ql4) ql3) ql2) (bM (bM (bM qkc qkb) qka) qj9)) (bM (bM (bM qhh qhg) qhf) qhe)) (bM (bM (bM qhd qhc) qhb) qha)) ql1)
  . exact (bM (bM (bM (bM (bM (bM (bM (bM ql0 qlz) qly) qlx) (bM (bM (bM qj8 qj7) qj6) qj5)) (bM (bM (bM qg9 qg8) qg7) qg6)) (bM (bM (bM qg5 qg4) qg3) qg2)) (bM (bM (bM qg1 qg0) qgz) qgy)) (bM qgx qgw))
  . exact (bM (bM (bM (bM (bM (bM (bM qlw qlv) qlu) qlt) qls) qlr) qlq) (bM (bM (bM (bM (bM qgv qgu) qgt) qgs) qgr) qgq))
  . exact (bM qlp qlo)
  . exact qr6
lemma qya:wo vq 14 inputs.toFinset :=
  qu4 (qe qaa qd4) zaa qtq
lemma qrg:zg 2 (qa 1023) 14 inputs.toFinset := by
  have noRun := qaw (g := v5) (qe v8 qbn) qxo qpr
    (k := 14) (Nat.le_refl _) (i := 0) (ws := inputs) (by decide +kernel)
  have tgt:zn v5=qa 1023 := by decide +kernel
  exact tgt ▸ noRun
lemma qre:zg 3 vq 14 (inputs ++ [qn]).toFinset := by
  have noRun := qaw (g := zj) (qe qe9 qv1) qxn qpq
    (k := 14) (Nat.le_refl _) (i := 0) (ws := inputs ++ [qn]) (by decide +kernel)
  have tgt:zn zj=vq := by decide +kernel
  exact tgt ▸ noRun
def f0 (y:Fin 8 -> Bool) : Bool :=
  ([1,10,19,5,14,23,38,47,60] : List Nat).any fun e =>
    y (Fin.ofNat 8 (e / 8))&&y (Fin.ofNat 8 (e % 8))
def G9 (y:Fin 9 -> Bool) : Bool :=
  ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any fun e =>
    y (Fin.ofNat 9 (e / 10))&&y (Fin.ofNat 9 (e % 10))
def qm1 (i:Fin 512) : Fin 8 -> Bool :=
  fun j => bit i (inputs.getD (j.val+1) zero)
def qm0 (i:Fin 512) : Fin 9 -> Bool :=
  fun j => bit i (inputs.getD j.val zero)
def ev0 (i:Fin 512) : Fin 512 :=
  Fin.ofNat 512 (i.val &&& 510)
lemma qtd:qo 510 =
    [inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,
     inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero,inputs.getD 8 zero] := by
  decide +kernel
lemma qb2 (i:Fin 512) : (qo 510).map (bit i)=List.ofFn (qm1 i) := by
  rw [qtd];simp [qm1,List.ofFn_succ]
lemma qfy (i:Fin 512) :
    (inputs ++ [qn]).map (bit i)=List.ofFn (qm0 i) ++ [!(qm0 i 0)] := by
  have hn:bit i qn = !(qm0 i 0) := by simp [qn,qu,qm0,yh]
  rw [List.map_append,List.map_singleton,hn]
  congr 1
lemma zak (i:Fin 512) :
    (inputs ++ [qn]).map (bit (ev0 i))=false :: List.ofFn (qm1 i) ++ [true] := by
  rw [qfy]
  have h0:qm0 (ev0 i) 0=false := by revert i;decide +kernel
  have ht:∀ j:Fin 8,qm0 (ev0 i) j.succ=qm1 i j := by revert i;decide +kernel
  have hl:List.ofFn (qm0 (ev0 i))=false :: List.ofFn (qm1 i) := by
    rw [List.ofFn_succ,h0];congr 1;exact congrArg List.ofFn (funext ht)
  rw [hl,h0];rfl
lemma qdl (i:Fin 512) : bit i (qa 510)=f0 (qm1 i) := by
  revert i;decide +kernel
lemma quc (i:Fin 512) : bit i vq=G9 (qm0 i) := by
  revert i;decide +kernel
def zk (gs:List Gate) (w:List Bool) : List Bool :=
  gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) w
lemma qfj (gs gs':List Gate) (w:List Bool) :
    zk (gs ++ gs') w=zk gs' (zk gs w) := by
  simp [zk,List.foldl_append]
lemma qcb (gs:List Gate) : ∀ w:List Bool,
    ∃ t:List Bool,zk gs w=w ++ t /\ t.length=gs.length := by
  induction gs with
  | nil => intro w;exact ⟨[],by simp [zk],rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t,ht,hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,?_,by simp [hl]⟩
    have h1:zk (g :: gs) w =
        zk gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [h1,ht];simp
lemma qfl (gs:List Gate) (w:List Bool) :
    (zk gs w).length=w.length+gs.length := by
  obtain ⟨t,ht,hl⟩ := qcb gs w;rw [ht];simp [hl]
lemma qc3 (gs gs':List Gate) (w:List Sig) :
    ze (gs ++ gs') w=ze gs' (ze gs w) := by
  simp [ze,List.foldl_append]
lemma qdm (gs:List Gate) : ∀ w:List Sig,
    ∃ t:List Sig,ze gs w=w ++ t /\ t.length=gs.length := by
  induction gs with
  | nil => intro w;exact ⟨[],by simp [ze],rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t,ht,hl⟩ := ih (w ++ [gv w g])
    refine ⟨gv w g :: t,?_,by simp [hl]⟩
    have h1:ze (g :: gs) w=ze gs (w ++ [gv w g]) := rfl
    rw [h1,ht];simp
lemma qc2 (gs:List Gate) (w:List Sig) :
    (ze gs w).length=w.length+gs.length := by
  obtain ⟨t,ht,hl⟩ := qdm gs w;rw [ht];simp [hl]
lemma jg (gs:List Gate) (w:List Sig) (i:Nat) (h:i < w.length) :
    (ze gs w).getD i zero=w.getD i zero := by
  obtain ⟨t,ht,_⟩ := qdm gs w;rw [ht,List.getD_append _ _ _ _ h]
lemma vm {α : Type} (L:List α) (S d : α) (j:Nat) (h:j ≠ L.length) :
    (L ++ [S]).getD j d=L.getD j d := by
  by_cases hj:j < L.length
  . exact List.getD_append _ _ _ _ hj
  . rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
lemma yo {α : Type} (L:List α) (S d : α) : (L ++ [S]).getD L.length d=S := by simp
def Ok (g:Gate) : Prop :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) /\ g.inputs.length ≤ 2
def NOk (g:Gate) : Prop := Ok g /\ (g.op=GateOp.not -> g.inputs.length ≤ 1)
lemma qyu:qy (qo 510) (qa 510) 12 := fun p b hr ha =>
  le_trans (by decide +kernel:12 ≤ qt qaa 510)
    (qe qaa qd4 510 p b hr ha)
lemma qch:¬ PEqualNP.MetaComplexity.HasCircuitSize 8 f0 11 := by
  rintro ⟨C,hfan,hsz,hev⟩
  have heq:(ze C.gates (qo 510)).getD C.output zero=qa 510 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i:Fin 512 := ⟨j,hj⟩
    change bit i ((ze C.gates (qo 510)).getD C.output zero)=bit i (qa 510)
    rw [← qe1,yp C.gates i (qo 510) (fun g hg => (hfan g hg).1),qb2,
      qdl]
    exact hev (qm1 i)
  have hp:q7 (qa 510) := zx _ (by decide +kernel)
  have hmem:qa 510 ∈ ze C.gates (qo 510) := by
    rw [← heq]
    by_cases hlt:C.output < (ze C.gates (qo 510)).length
    . rw [List.getD_eq_getElem _ _ hlt];exact List.getElem_mem hlt
    . rw [List.getD_eq_default _ _ (by omega)] at heq;exact False.elim (hp.1 heq.symm)
  obtain ⟨k,t,S,hk,run,sub⟩ := qvw C.gates (qo 510) hfan hp hmem
  have h12 := wb hp run sub qyu
  have hlen:C.gates.length ≤ 11 := hsz
  omega
abbrev jl := Bool ⊕ Nat
def jl.val (w:List Bool) : jl -> Bool | Sum.inl c => c | Sum.inr j => w.getD j false
def jl.Valid (m:Nat) : jl -> Prop | Sum.inl _ => True | Sum.inr j => j < m
def qa6 (m:Nat) : List jl -> Option Gate × jl
  | [] => (none,Sum.inl true)
  | Sum.inl c :: _ => (none,Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not,[j]⟩,Sum.inr m)
def y4 (m:Nat) : List jl -> Option Gate × jl
  | [] => (none,Sum.inl true)
  | [Sum.inl c] => (none,Sum.inl c)
  | [Sum.inr j] => (none,Sum.inr j)
  | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c&&d))
  | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
  | _ => (none,Sum.inl false)
def qbf (m:Nat) : List jl -> Option Gate × jl
  | [] => (none,Sum.inl false)
  | [Sum.inl c] => (none,Sum.inl c)
  | [Sum.inr j] => (none,Sum.inr j)
  | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c||d))
  | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
  | _ => (none,Sum.inl false)
def q9 (op:GateOp) (m:Nat) (ins:List jl) : Option Gate × jl :=
  match op with
  | GateOp.and => y4 m ins | GateOp.or => qbf m ins
  | GateOp.not => qa6 m ins | _ => (none,Sum.inl false)
lemma qps (op:GateOp) (m:Nat) (ins:List jl) :
    ∀ g ∈ (q9 op m ins).1,Ok g := by
  intro g hg
  cases op <;> simp only [q9] at hg
  . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [y4] at hg;subst hg;simp [Ok]
  . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [qbf] at hg;subst hg;simp [Ok]
  . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
      simp [qa6] at hg;subst hg;simp [Ok]
  . simp at hg
  . simp at hg
lemma qi0 (op:GateOp) (m:Nat) (ins:List jl)
    (hop:op=GateOp.and \/ op=GateOp.or \/ op=GateOp.not) (hlen:ins.length ≤ 2)
    (hnot:op=GateOp.not -> ins.length ≤ 1) (hc:∃ c,Sum.inl c ∈ ins) :
    (q9 op m ins).1=none := by
  obtain ⟨c,hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [q9,y4]
  . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [q9,qbf]
  . have h1 := hnot rfl
    rcases ins with _ | ⟨a,_ | ⟨b,l⟩⟩ <;> (try cases a) <;> simp_all [q9,qa6]
lemma qiz (op:GateOp) (hop:op=GateOp.and \/ op=GateOp.or \/ op=GateOp.not)
    (w:List Bool) (ins:List jl) (hlen:ins.length ≤ 2)
    (hv:∀ s ∈ ins,s.Valid w.length) :
    ((q9 op w.length ins).2).Valid (w.length+(q9 op w.length ins).1.toList.length) ∧
    ((q9 op w.length ins).2).val (zk (q9 op w.length ins).1.toList w)
     =op.eval (ins.map (jl.val w)) := by
  rcases hop with rfl | rfl | rfl
  . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
    . simp [q9,y4,jl.Valid,jl.val,GateOp.eval]
    . cases a <;> simp_all [q9,y4,jl.Valid,jl.val,GateOp.eval,zk]
    . cases a <;> cases b <;> (try rename_i c e;cases c) <;> (try cases e) <;>
        simp_all [q9,y4,jl.Valid,jl.val,GateOp.eval,zk]
    . simp at hlen
  . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
    . simp [q9,qbf,jl.Valid,jl.val,GateOp.eval]
    . cases a <;> simp_all [q9,qbf,jl.Valid,jl.val,GateOp.eval,zk]
    . cases a <;> cases b <;> (try rename_i c e;cases c) <;> (try cases e) <;>
        simp_all [q9,qbf,jl.Valid,jl.val,GateOp.eval,zk]
    . simp at hlen
  . rcases ins with _ | ⟨a,l⟩
    . simp [q9,qa6,jl.Valid,jl.val,GateOp.eval]
    . cases a <;> simp_all [q9,qa6,jl.Valid,jl.val,GateOp.eval,zk]
def z3 (acc:List jl × List Gate) (g:Gate) : List jl × List Gate :=
  let r := q9 g.op (8+acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2],acc.2 ++ r.1.toList)
def elim (gs:List Gate) (acc:List jl × List Gate) : List jl × List Gate :=
  gs.foldl z3 acc
lemma qdd (g:Gate) (gs:List Gate) (acc:List jl × List Gate) :
    elim (g :: gs) acc=elim gs (z3 acc g) := rfl
lemma qqw (p q:List Gate) (acc:List jl × List Gate) :
    elim (p ++ q) acc=elim q (elim p acc) := by simp [elim,List.foldl_append]
lemma qnv (gs:List Gate) : ∀ acc:List jl × List Gate,
    (elim gs acc).1.length=acc.1.length+gs.length := by
  induction gs with
  | nil => intro acc;rfl
  | cons g gs ih => intro acc;rw [qdd,ih];simp [z3];omega
lemma qao (k:Nat) (d:jl) (gs:List Gate) : ∀ acc:List jl × List Gate,
    k < acc.1.length -> (elim gs acc).1.getD k d=acc.1.getD k d := by
  induction gs with
  | nil => intro acc _;rfl
  | cons g gs ih =>
    intro acc hk;rw [qdd,ih (z3 acc g) (by simp [z3];omega)]
    exact vm _ _ _ _ (by omega)
lemma qng (gs:List Gate) : ∀ acc:List jl × List Gate,
    (∀ g ∈ acc.2,Ok g) -> ∀ g ∈ (elim gs acc).2,Ok g := by
  induction gs with
  | nil => intro acc h;exact h
  | cons g gs ih =>
    intro acc h;apply ih (z3 acc g);intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    . exact h g' h1
    . exact qps _ _ _ g' (by simpa using h1)
def vo (g:Gate) : Bool := g.inputs.contains 0||g.inputs.contains 9
lemma qkg {α : Type} (o:Option α) : o.toList.length ≤ 1 := by cases o <;> simp
lemma qa4 (acc:List jl × List Gate) (g:Gate) (hg:NOk g)
    (h0:acc.1.getD 0 (Sum.inl false)=Sum.inl false)
    (h9:acc.1.getD 9 (Sum.inl false)=Sum.inl true) :
    (z3 acc g).2.length ≤ acc.2.length+if vo g then 0 else 1 := by
  simp only [z3,List.length_append]
  cases hrd:vo g
  . simp only [Bool.false_eq_true,ite_false]
    have h1 := qkg (q9 g.op (8+acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
    omega
  . simp only [ite_true,Nat.add_zero]
    have hnone:(q9 g.op (8+acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1=none := by
      apply qi0 _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
      simp only [vo,Bool.or_eq_true,List.contains_eq_mem,decide_eq_true_eq] at hrd
      rcases hrd with hm | hm
      . exact ⟨false,List.mem_map.2 ⟨0,hm,h0⟩⟩
      . exact ⟨true,List.mem_map.2 ⟨9,hm,h9⟩⟩
    rw [hnone];simp
lemma qa1 (gs:List Gate) : ∀ acc:List jl × List Gate,
    (∀ g ∈ gs,NOk g) -> 10 ≤ acc.1.length →
    acc.1.getD 0 (Sum.inl false)=Sum.inl false →
    acc.1.getD 9 (Sum.inl false)=Sum.inl true →
    (elim gs acc).2.length ≤ acc.2.length+(gs.filter fun g => !vo g).length := by
  induction gs with
  | nil => intro acc _ _ _ _;simp [elim]
  | cons g gs ih =>
    intro acc hok hl h0 h9
    rw [qdd]
    have hstep := qa4 acc g (hok g List.mem_cons_self) h0 h9
    have hrest := ih (z3 acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [z3];omega)
      (by simp only [z3];rw [vm _ _ _ _ (by omega)];exact h0)
      (by simp only [z3];rw [vm _ _ _ _ (by omega)];exact h9)
    cases hr:vo g
    . simp only [hr,Bool.false_eq_true,ite_false] at hstep
      simp only [List.filter_cons,hr,Bool.not_false,ite_true,List.length_cons]
      omega
    . simp only [hr,ite_true,Nat.add_zero] at hstep
      simp only [List.filter_cons,hr,Bool.not_true,Bool.false_eq_true,ite_false]
      omega
lemma jl.valid_mono {m m':Nat} (h:m ≤ m') : ∀ s:jl,s.Valid m -> s.Valid m'
  | Sum.inl _,_ => trivial
  | Sum.inr _,hj => lt_of_lt_of_le hj h
lemma jl.val_append (w t:List Bool) : ∀ s:jl,s.Valid w.length →
    s.val (w ++ t)=s.val w
  | Sum.inl _,_ => rfl
  | Sum.inr _,hj => List.getD_append _ _ _ _ hj
def zbd (y:List Bool) (w:List Bool) (acc:List jl × List Gate) : Prop :=
  acc.1.length=w.length /\ ∀ i:Nat,
    (acc.1.getD i (Sum.inl false)).Valid (8+acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (zk acc.2 y)=w.getD i false
lemma qzw (y:List Bool) (hy:y.length=8) (gs:List Gate) :
    ∀ (w:List Bool) (acc:List jl × List Gate),(∀ g ∈ gs,Ok g) -> zbd y w acc →
      zbd y (zk gs w) (elim gs acc) := by
  induction gs with
  | nil => intro w acc _ h;exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (z3 acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl,hi⟩ := h
    set w' := zk acc.2 y with hw'
    have lw':w'.length=8+acc.2.length := by rw [hw',qfl,hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := qiz g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (fun s hs => by obtain ⟨a,_,rfl⟩ := List.mem_map.1 hs;rw [lw'];exact (hi a).1)
    rw [lw'] at hs
    set r := q9 g.op (8+acc.2.length) ins
    have hvals:ins.map (jl.val w')=g.inputs.map fun i => w.getD i false := by
      rw [hins,List.map_map];exact List.map_congr_left (fun a _ => (hi a).2)
    have hnew:zk (acc.2 ++ r.1.toList) y=zk r.1.toList w' := qfj _ _ _
    obtain ⟨t,ht,_⟩ := qcb r.1.toList w'
    refine ⟨by simp [z3,hl],fun i => ?_⟩
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (8+(acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (zk (acc.2 ++ r.1.toList) y)=_
    rw [hnew,List.length_append,← Nat.add_assoc]
    by_cases hil:i=acc.1.length
    . subst hil;rw [yo,hl,yo];exact ⟨hs.1,by rw [hs.2,hvals]⟩
    . rw [vm _ _ _ _ hil,vm _ _ _ _ (by omega)]
      refine ⟨jl.valid_mono (by omega) _ (hi i).1,?_⟩
      rw [ht,jl.val_append _ _ _ (by rw [lw'];exact (hi i).1)];exact (hi i).2
def vf:List jl :=
  [Sum.inl false,Sum.inr 0,Sum.inr 1,Sum.inr 2,Sum.inr 3,Sum.inr 4,Sum.inr 5,Sum.inr 6,Sum.inr 7,Sum.inl true]
lemma qt8 (y:Fin 8 -> Bool) :
    zbd (List.ofFn y) (false :: List.ofFn y ++ [true]) (vf,[]) := by
  refine ⟨by simp [vf],fun i => ?_⟩
  have hrow:false :: List.ofFn y ++ [true] =
      [false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,true] := by simp [List.ofFn_succ]
  rw [hrow]
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | _+10 => simp [vf,jl.Valid,jl.val,zk]
lemma qnu {target:Sig} (gs:List Gate) (w:List Sig)
    (legal:∀ g ∈ gs,Ok g) {k t S} (h:v4 target k t S)
    (sub:∀ a ∈ S,a ∈ ze gs w) :
    ∃ k' t' S',k' ≤ k+gs.length /\ v4 target k' t' S' /\ ∀ a ∈ S',a ∈ w := by
  induction gs generalizing w k t S with
  | nil => exact ⟨k,t,S,by simp,h,sub⟩
  | cons g gs ih =>
    obtain ⟨k1,t1,S1,hk1,h1,sub1⟩ := ih (w ++ [gv w g]) (fun a ha => legal a (by simp [ha])) h sub
    obtain ⟨k2,t2,S2,hk2,h2,sub2⟩ := qe3 h1 (qpk w g (legal g (by simp))) sub1
    exact ⟨k2,t2,S2,by simp;omega,h2,sub2⟩
lemma qdw {α : Type} : ∀ (l:List α) (j:Nat) (_:j < l.length),
    l=l.take j ++ l[j] :: l.drop (j+1)
  | [],_,h => by simp at h
  | _ :: _,0,_ => rfl
  | a :: l,j+1,h => congrArg (a :: ·) (qdw l j (by simpa using h))
lemma qkk (eg:List Gate) (outE:Nat)
    (hok:∀ g ∈ eg,Ok g) (hlen:eg.length=12)
    (hev:∀ y:Fin 8 -> Bool,(zk eg (List.ofFn y)).getD outE false=f0 y)
    (j:Nat) (hj:j < 8+eg.length) :
    q7 ((ze eg (qo 510)).getD j zero) := by
  have heq:(ze eg (qo 510)).getD outE zero=qa 510 := by
    apply BitVec.eq_of_getLsbD_eq;intro r hr;let i:Fin 512 := ⟨r,hr⟩
    change bit i ((ze eg (qo 510)).getD outE zero)=bit i (qa 510)
    rw [← qe1,yp eg i (qo 510) (fun g hg => (hok g hg).1),qb2,qdl]
    exact hev (qm1 i)
  have hp510:q7 (qa 510) := zx _ (by decide +kernel)
  have hout:qa 510 ∈ ze eg (qo 510) := by
    rw [← heq]
    by_cases hlt:outE < (ze eg (qo 510)).length
    . rw [List.getD_eq_getElem _ _ hlt];exact List.getElem_mem hlt
    . rw [List.getD_eq_default _ _ (by omega)] at heq;exact False.elim (hp510.1 heq.symm)
  by_cases hj8:j < 8
  . have hvlen:(qo 510).length=8 := by decide +kernel
    rw [jg eg (qo 510) j (by omega)]
    have hmem:(qo 510).getD j zero ∈ qo 510 := by
      rw [List.getD_eq_getElem _ _ (by omega)];exact List.getElem_mem _
    exact zx _ (List.all_eq_true.mp (by decide +kernel:(qo 510).all zz=true) _ hmem)
  . by_contra hnp
    have hidx:j - 8 < eg.length := by omega
    have hsplit:eg=eg.take (j - 8) ++ eg[j - 8] :: eg.drop (j - 8+1) :=
      qdw eg (j - 8) hidx
    set p1 := eg.take (j - 8);set g1 := eg[j - 8];set t1 := eg.drop (j - 8+1)
    have hlp1:p1.length=j - 8 := by simp [p1];omega
    have hlt1:p1.length+t1.length=11 := by
      have := congrArg List.length hsplit;simp only [List.length_append,List.length_cons] at this;omega
    have hokp1:∀ g ∈ p1,Ok g := fun g hg => hok g (hsplit ▸ List.mem_append_left _ hg)
    have hokt1:∀ g ∈ t1,Ok g := fun g hg => hok g (hsplit ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hg))
    have hex:ze eg (qo 510)=ze t1 (ze p1 (qo 510) ++ [gv (ze p1 (qo 510)) g1]) := by
      rw [hsplit,qc3];rfl
    have hvlen:(qo 510).length=8 := by decide +kernel
    have hlenp:(ze p1 (qo 510)).length=j := by rw [qc2,hvlen,hlp1];omega
    have hz_eq:(ze eg (qo 510)).getD j zero=gv (ze p1 (qo 510)) g1 := by
      rw [hex,jg t1 _ j (by simp [hlenp]),← hlenp,yo]
    rw [hz_eq] at hnp;rw [hex] at hout
    obtain ⟨k1,u1,S1,hk1,hL1,sub1⟩ := qvw t1 _ hokt1 hp510 hout
    have hsubp:∀ a ∈ S1,a ∈ ze p1 (qo 510) := fun a ha =>
      (by simpa using sub1 a ha:a ∈ ze p1 (qo 510) \/ a=gv (ze p1 (qo 510)) g1).resolve_right
        (fun e => hnp (e ▸ qcr hL1 a ha))
    obtain ⟨k2,u2,S2,hk2,hL2,sub2⟩ := qnu p1 (qo 510) hokp1 hL1 hsubp
    have h12 := wb hp510 hL2 sub2 qyu
    omega
lemma qdg (op:GateOp) (m:Nat) (ins:List jl) (e:Gate)
    (hop:op=GateOp.and \/ op=GateOp.or \/ op=GateOp.not) (hlen:ins.length ≤ 2)
    (hnot:op=GateOp.not -> ins.length ≤ 1) (hs:(q9 op m ins).1=some e) :
    (q9 op m ins).2=Sum.inr m ∧
    ((op=GateOp.not /\ ∃ j,ins=[Sum.inr j]) ∨
     ((op=GateOp.and \/ op=GateOp.or) /\ ∃ j1 j2,ins=[Sum.inr j1,Sum.inr j2])) := by
  rcases hop with rfl | rfl | rfl
  . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [q9,y4] at hs;exact ⟨rfl,Or.inr ⟨Or.inl rfl,_,_,rfl⟩⟩
  . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [q9,qbf] at hs;exact ⟨rfl,Or.inr ⟨Or.inr rfl,_,_,rfl⟩⟩
  . have hn := hnot rfl
    rcases ins with _ | ⟨a,_ | ⟨b,l⟩⟩
    . simp [q9,qa6] at hs
    . cases a
      . simp [q9,qa6] at hs
      . exact ⟨rfl,Or.inl ⟨rfl,_,rfl⟩⟩
    . simp at hn
lemma qf5 (op:GateOp) (m:Nat) (acc:List jl) (ks:List Nat) (j:Nat)
    (hop:op=GateOp.and \/ op=GateOp.or \/ op=GateOp.not) (hlen:ks.length ≤ 2)
    (hnot:op=GateOp.not -> ks.length ≤ 1)
    (h0:acc.getD 0 (Sum.inl false)=Sum.inl false)
    (h9:acc.getD 9 (Sum.inl false)=Sum.inl true)
    (hrd:0 ∈ ks \/ 9 ∈ ks)
    (hr:(q9 op m (ks.map fun i => acc.getD i (Sum.inl false))).2=Sum.inr j) :
    (op=GateOp.or /\ ∃ k,(ks=[0,k] \/ ks=[k,0]) /\ acc.getD k (Sum.inl false)=Sum.inr j) ∨
    (op=GateOp.and /\ ∃ k,(ks=[9,k] \/ ks=[k,9]) /\ acc.getD k (Sum.inl false)=Sum.inr j) := by
  rcases hop with rfl | rfl | rfl
  . rcases ks with _ | ⟨k1,_ | ⟨k2,_ | ⟨k3,l⟩⟩⟩
    . simp at hrd
    . simp only [List.mem_singleton] at hrd
      rcases hrd with rfl | rfl <;> (simp only [List.map_cons,List.map_nil,h0,h9,q9,y4] at hr;cases hr)
    . simp only [List.map_cons,List.map_nil,q9] at hr
      cases h1:acc.getD k1 (Sum.inl false) with
      | inl c1 =>
        cases h2:acc.getD k2 (Sum.inl false) with
        | inl c2 => rw [h1,h2] at hr;cases hr
        | inr j2 =>
          rw [h1,h2] at hr;cases c1
          . cases hr
          . simp only [y4,cond_true,Sum.inr.injEq] at hr;subst hr
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hrd
            rcases hrd with (rfl | rfl) | (rfl | rfl)
            . rw [h0] at h1;cases h1
            . rw [h0] at h2;cases h2
            . exact Or.inr ⟨rfl,k2,Or.inl rfl,h2⟩
            . rw [h9] at h2;cases h2
      | inr j1 =>
        cases h2:acc.getD k2 (Sum.inl false) with
        | inl c2 =>
          rw [h1,h2] at hr;cases c2
          . cases hr
          . simp only [y4,cond_true,Sum.inr.injEq] at hr;subst hr
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hrd
            rcases hrd with (rfl | rfl) | (rfl | rfl)
            . rw [h0] at h1;cases h1
            . rw [h0] at h2;cases h2
            . rw [h9] at h1;cases h1
            . exact Or.inr ⟨rfl,k1,Or.inr rfl,h1⟩
        | inr j2 =>
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hrd
          rcases hrd with (rfl | rfl) | (rfl | rfl)
          . rw [h0] at h1;cases h1
          . rw [h0] at h2;cases h2
          . rw [h9] at h1;cases h1
          . rw [h9] at h2;cases h2
    . simp at hlen
  . rcases ks with _ | ⟨k1,_ | ⟨k2,_ | ⟨k3,l⟩⟩⟩
    . simp at hrd
    . simp only [List.mem_singleton] at hrd
      rcases hrd with rfl | rfl <;> (simp only [List.map_cons,List.map_nil,h0,h9,q9,qbf] at hr;cases hr)
    . simp only [List.map_cons,List.map_nil,q9] at hr
      cases h1:acc.getD k1 (Sum.inl false) with
      | inl c1 =>
        cases h2:acc.getD k2 (Sum.inl false) with
        | inl c2 => rw [h1,h2] at hr;cases hr
        | inr j2 =>
          rw [h1,h2] at hr;cases c1
          . simp only [qbf,cond_false,Sum.inr.injEq] at hr;subst hr
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hrd
            rcases hrd with (rfl | rfl) | (rfl | rfl)
            . exact Or.inl ⟨rfl,k2,Or.inl rfl,h2⟩
            . rw [h0] at h2;cases h2
            . rw [h9] at h1;cases h1
            . rw [h9] at h2;cases h2
          . cases hr
      | inr j1 =>
        cases h2:acc.getD k2 (Sum.inl false) with
        | inl c2 =>
          rw [h1,h2] at hr;cases c2
          . simp only [qbf,cond_false,Sum.inr.injEq] at hr;subst hr
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hrd
            rcases hrd with (rfl | rfl) | (rfl | rfl)
            . rw [h0] at h1;cases h1
            . exact Or.inl ⟨rfl,k1,Or.inr rfl,h1⟩
            . rw [h9] at h1;cases h1
            . rw [h9] at h2;cases h2
          . cases hr
        | inr j2 =>
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hrd
          rcases hrd with (rfl | rfl) | (rfl | rfl)
          . rw [h0] at h1;cases h1
          . rw [h0] at h2;cases h2
          . rw [h9] at h1;cases h1
          . rw [h9] at h2;cases h2
    . simp at hlen
  . have hn := hnot rfl
    rcases ks with _ | ⟨k1,_ | ⟨k2,l⟩⟩
    . simp at hrd
    . simp only [List.mem_singleton] at hrd
      rcases hrd with rfl | rfl <;> (simp only [List.map_cons,List.map_nil,h0,h9,q9,qa6] at hr;cases hr)
    . simp at hn
def z4 (a:Sig) : Sig := q5 (qa7 jx) a
lemma qqu (r:Row) : qa7 jx (qa7 jx r)=r := by revert r;decide +kernel
lemma quz:Function.Surjective (qa7 jx) := fun r => ⟨qa7 jx r,qqu r⟩
lemma v9:Function.Injective z4 := qip _ quz
lemma quy:z4 zero=zero := (wv _).1
lemma qx7:z4 one=one := (wv _).2
lemma qfc (a:Sig) : z4 (neg a)=neg (z4 a) := qax _ a
lemma qmv (d:Bool) (a b:Sig) : z4 (bin d a b)=bin d (z4 a) (z4 b) := qdt _ d a b
lemma zaj:z4 qu=qn := by
  change q5 (z5 [jx]) qu=qn
  rw [← zt];decide +kernel
lemma qfb:z4 qn=qu := by rw [qn,qfc,zaj,qn];exact BitVec.not_not
lemma qqv:z4 vq=qa 1023 := by
  change q5 (z5 [jx]) vq=qa 1023
  rw [← zt];decide +kernel
lemma qb6 {a:Sig} (ha:q7 a) : q7 (z4 a) :=
  ⟨fun e => ha.1 (v9 (e.trans quy.symm)),fun e => ha.2 (v9 (e.trans qx7.symm))⟩
def qcq (S:Set Nat) (idx:Nat) (g:Gate) : Prop :=
  idx ∈ S →
    (g.op=GateOp.not /\ ∃ k,g.inputs=[k] /\ k ∈ S /\ k < idx) ∨
    ((g.op=GateOp.and \/ g.op=GateOp.or) /\ ∃ k1 k2,g.inputs=[k1,k2] /\ k1 ∈ S /\ k2 ∈ S /\ k1 < idx /\ k2 < idx) ∨
    (g.op=GateOp.or /\ ∃ k,(g.inputs=[0,k] \/ g.inputs=[k,0]) /\ k ∈ S /\ k < idx) ∨
    (g.op=GateOp.and /\ ∃ k,(g.inputs=[9,k] \/ g.inputs=[k,9]) /\ k ∈ S /\ k < idx)
lemma qep {I:Finset Nat} {W:List Sig} {S:Set Nat}
    (hI:∀ i ∈ I,i ∈ S \/ i=0 \/ i=9)
    (hW0:W.getD 0 zero=qu) (hW9:W.getD 9 zero=qn)
    (hS:∀ k ∈ S,W.getD k zero ≠ qu /\ W.getD k zero ≠ qn) :
    (qu ∈ I.image (fun i => W.getD i zero) ↔ 0 ∈ I) ∧
    (qn ∈ I.image (fun i => W.getD i zero) ↔ 9 ∈ I) := by
  have hne:qu ≠ qn := by decide +kernel
  refine ⟨⟨fun hm => ?_,fun h0 => Finset.mem_image.mpr ⟨0,h0,hW0⟩⟩,
          ⟨fun hm => ?_,fun h9 => Finset.mem_image.mpr ⟨9,h9,hW9⟩⟩⟩
  . obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hm
    rcases hI i hi with hs | rfl | rfl
    . exact False.elim ((hS i hs).1 he)
    . exact hi
    . rw [hW9] at he;exact False.elim (hne he.symm)
  . obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hm
    rcases hI i hi with hs | rfl | rfl
    . exact False.elim ((hS i hs).2 he)
    . rw [hW0] at he;exact False.elim (hne he)
    . exact hi
lemma au2 {a:Sig} (h:a ≠ qu) : jc 2 a=true := by
  simp [jc,bne_iff_ne,h]
lemma au3 {a:Sig} (h0:a ≠ qu) (h9:a ≠ qn) : jc 3 a=true := by
  simp [jc,bne_iff_ne,h0,h9]
lemma qvz {a b:Sig} {ka kb:Bool} : zq 2 false a b ka kb=true := by
  simp [zq]
lemma zgc {a b:Sig} {ka kb:Bool} (ha:a ≠ qu) (hb:b ≠ qu) :
    zq 2 true a b ka kb=true := by
  simp [zq,bne_iff_ne,ha,hb]
lemma qvy {d:Bool} {a b:Sig} {ka kb:Bool}
    (ha0:a ≠ qu) (hb0:b ≠ qu) (ha9:a ≠ qn) (hb9:b ≠ qn) :
    zq 3 d a b ka kb=true := by
  simp [zq,beq_iff_eq,ha0,hb0,ha9,hb9]
lemma zc6 {b:Sig} {kb:Bool} (hb9:b ≠ qn) :
    zq 3 true qu b false kb=true := by
  simp [zq,bne_iff_ne,hb9]
lemma zbc {b:Sig} {kb:Bool} (hb0:b ≠ qu) (hne:qn ≠ qu) :
    zq 3 false qn b false kb=true := by
  simp [zq,beq_iff_eq,hne,hb0]
lemma qzf {S:Set Nat} {W:List Sig} {idx:Nat} {g:Gate} {k u:Nat} {I:Finset Nat}
    (need3:Bool) (hidx10:10 ≤ idx)
    (hW0:W.getD 0 zero=qu) (hW9:W.getD 9 zero=qn)
    (hS:∀ m ∈ S,q7 (W.getD m zero) /\ W.getD m zero ≠ qu /\ W.getD m zero ≠ qn)
    (hIlt:∀ i ∈ I,i < idx+1) (hIok:∀ i ∈ I,i ∈ S \/ i=0 \/ i=9)
    (hspec:qcq S idx g) (hval:idx ∈ S -> W.getD idx zero=gv W g)
    (hL0:9 ∉ I -> v4 vq k u (I.image (fun i => W.getD i zero)))
    (hL2:0 ∉ I -> j3 2 (qa 1023) k u (I.image (fun i => z4 (W.getD i zero))))
    (hL3:need3=true -> j3 3 vq k u (I.image (fun i => W.getD i zero)))
    (hno0:need3=true -> idx ∈ S -> 0 ∈ g.inputs -> 0 ∉ I)
    (hno9:need3=true -> idx ∈ S -> 9 ∈ g.inputs -> 9 ∉ I) :
    ∃ (k' u':Nat) (I':Finset Nat),k' ≤ k+1 ∧
      (∀ i ∈ I',i < idx) /\ (∀ i ∈ I',i ∈ S \/ i=0 \/ i=9) ∧
      (0 ∈ I' -> 0 ∈ I \/ (idx ∈ S /\ 0 ∈ g.inputs)) ∧
      (9 ∈ I' -> 9 ∈ I \/ (idx ∈ S /\ 9 ∈ g.inputs)) ∧
      (9 ∉ I' -> v4 vq k' u' (I'.image (fun i => W.getD i zero))) ∧
      (0 ∉ I' -> j3 2 (qa 1023) k' u' (I'.image (fun i => z4 (W.getD i zero)))) ∧
      (need3=true -> j3 3 vq k' u' (I'.image (fun i => W.getD i zero))) := by
  classical
  have hne09:qu ≠ qn := by decide +kernel
  have hpx0:q7 qu := zx _ (by decide +kernel)
  have hpnx0:q7 qn := zx _ (by decide +kernel)
  by_cases hmem:idx ∈ I
  . have hidxS:idx ∈ S := by rcases hIok idx hmem with hs | h0 | h9;exact hs;omega;omega
    let I0 := I.erase idx
    have hI0lt:∀ i ∈ I0,i < idx := fun i hi => by obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hi;have := hIlt i hm;omega
    have hI0ok:∀ i ∈ I0,i ∈ S \/ i=0 \/ i=9 := fun i hi => hIok i (Finset.mem_of_mem_erase hi)
    have h0sub:0 ∈ I0 ↔ 0 ∈ I := by simp [I0,show (0:Nat) ≠ idx by omega]
    have h9sub:9 ∈ I0 ↔ 9 ∈ I := by simp [I0,show (9:Nat) ≠ idx by omega]
    set z := W.getD idx zero
    let U := I0.image (fun i => W.getD i zero)
    let U2 := I0.image (fun i => z4 (W.getD i zero))
    have hIU:I.image (fun i => W.getD i zero)=insert z U := by
      have:I=insert idx I0 := (Finset.insert_erase hmem).symm
      conv_lhs => rw [this,Finset.image_insert]
    have hIU2:I.image (fun i => z4 (W.getD i zero))=insert (z4 z) U2 := by
      have:I=insert idx I0 := (Finset.insert_erase hmem).symm
      conv_lhs => rw [this,Finset.image_insert]
    by_cases hzU:z ∈ U
    . have heq1:I0.image (fun i => W.getD i zero)=I.image (fun i => W.getD i zero) := by
        rw [hIU,Finset.insert_eq_of_mem hzU]
      have hzU2:z4 z ∈ U2 := by
        obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hzU
        exact Finset.mem_image.mpr ⟨j,hj,congrArg z4 he⟩
      have heq2:I0.image (fun i => z4 (W.getD i zero))=I.image (fun i => z4 (W.getD i zero)) := by
        rw [hIU2,Finset.insert_eq_of_mem hzU2]
      exact ⟨k,u,I0,by omega,hI0lt,hI0ok,fun h => Or.inl (h0sub.mp h),fun h => Or.inl (h9sub.mp h),
        fun h => heq1.symm ▸ hL0 (fun h9 => h (h9sub.mpr h9)),
        fun h => heq2.symm ▸ hL2 (fun h0 => h (h0sub.mpr h0)),fun hn => heq1.symm ▸ hL3 hn⟩
    . have hzU2:z4 z ∉ U2 := fun hm => by
        obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hm
        exact hzU (Finset.mem_image.mpr ⟨j,hj,v9 he⟩)
      have hgv := hval hidxS
      have hsp := hspec hidxS
      have hbin_helper (d:Bool) (a b:Nat) (ha_lt:a < idx) (hb_lt:b < idx)
          (ha_ok:a ∈ S \/ a=0 \/ a=9) (hb_ok:b ∈ S \/ b=0 \/ b=9)
          (ha_in:a ∈ g.inputs) (hb_in:b ∈ g.inputs)
          (ha_p:q7 (W.getD a zero)) (hb_p:q7 (W.getD b zero))
          (hz_bin:z=bin d (W.getD a zero) (W.getD b zero))
          (hall2:0 ∉ insert a (insert b I0) →
            zq 2 d (z4 (W.getD a zero)) (z4 (W.getD b zero))
              (decide (z4 (W.getD a zero) ∈ U2)) (decide (z4 (W.getD b zero) ∈ U2))=true)
          (hall3:need3=true -> zq 3 d (W.getD a zero) (W.getD b zero)
            (decide (W.getD a zero ∈ U)) (decide (W.getD b zero ∈ U))=true) :
          ∃ (k' u':Nat) (I':Finset Nat),k' ≤ k+1 ∧
            (∀ i ∈ I',i < idx) /\ (∀ i ∈ I',i ∈ S \/ i=0 \/ i=9) ∧
            (0 ∈ I' -> 0 ∈ I \/ (idx ∈ S /\ 0 ∈ g.inputs)) ∧
            (9 ∈ I' -> 9 ∈ I \/ (idx ∈ S /\ 9 ∈ g.inputs)) ∧
            (9 ∉ I' -> v4 vq k' u' (I'.image (fun i => W.getD i zero))) ∧
            (0 ∉ I' -> j3 2 (qa 1023) k' u' (I'.image (fun i => z4 (W.getD i zero)))) ∧
            (need3=true -> j3 3 vq k' u' (I'.image (fun i => W.getD i zero))) := by
        set va := W.getD a zero;set vb := W.getD b zero
        have hcol (c:Nat) (hclt:c < idx) (hcok:c ∈ S \/ c=0 \/ c=9) (hcin:c ∈ g.inputs)
            (hzc:z=W.getD c zero) :
            ∃ (k' u':Nat) (I':Finset Nat),k' ≤ k+1 ∧
              (∀ i ∈ I',i < idx) /\ (∀ i ∈ I',i ∈ S \/ i=0 \/ i=9) ∧
              (0 ∈ I' -> 0 ∈ I \/ (idx ∈ S /\ 0 ∈ g.inputs)) ∧
              (9 ∈ I' -> 9 ∈ I \/ (idx ∈ S /\ 9 ∈ g.inputs)) ∧
              (9 ∉ I' -> v4 vq k' u' (I'.image (fun i => W.getD i zero))) ∧
              (0 ∉ I' -> j3 2 (qa 1023) k' u' (I'.image (fun i => z4 (W.getD i zero)))) ∧
              (need3=true -> j3 3 vq k' u' (I'.image (fun i => W.getD i zero))) := by
          let I1 := insert c I0
          have heq1:I1.image (fun i => W.getD i zero)=I.image (fun i => W.getD i zero) := by
            rw [hIU,Finset.image_insert,← hzc]
          have heq2:I1.image (fun i => z4 (W.getD i zero))=I.image (fun i => z4 (W.getD i zero)) := by
            rw [hIU2,Finset.image_insert,← hzc]
          refine ⟨k,u,I1,by omega,?_,?_,?_,?_,?_,?_,fun hn => heq1.symm ▸ hL3 hn⟩
          . intro i hi;rcases Finset.mem_insert.mp hi with rfl | hm;exact hclt;exact hI0lt i hm
          . intro i hi;rcases Finset.mem_insert.mp hi with rfl | hm;exact hcok;exact hI0ok i hm
          . intro h0;rcases Finset.mem_insert.mp h0 with rfl | hm;exact Or.inr ⟨hidxS,hcin⟩;exact Or.inl (h0sub.mp hm)
          . intro h9;rcases Finset.mem_insert.mp h9 with rfl | hm;exact Or.inr ⟨hidxS,hcin⟩;exact Or.inl (h9sub.mp hm)
          . intro h9;exact heq1.symm ▸ hL0 (fun hm => h9 (Finset.mem_insert_of_mem (h9sub.mpr hm)))
          . intro h0;exact heq2.symm ▸ hL2 (fun hm => h0 (Finset.mem_insert_of_mem (h0sub.mpr hm)))
        by_cases hza:z=va
        . exact hcol a ha_lt ha_ok ha_in hza
        . by_cases hzb:z=vb
          . exact hcol b hb_lt hb_ok hb_in hzb
          . have hab:va ≠ vb := fun e => by
              rw [e] at hz_bin
              have hid:bin d vb vb=vb := by cases d;exact (vl vb).2.2.2.2.1;exact (vl vb).2.2.2.2.2
              exact hzb (hz_bin.trans hid)
            have hfr:bin d va vb ∉ insert va (insert vb U) := by
              rw [← hz_bin];intro hm
              rcases Finset.mem_insert.mp hm with h1 | hm;exact hza h1
              rcases Finset.mem_insert.mp hm with h2 | hm;exact hzb h2
              exact hzU hm
            have hfr2:bin d (z4 va) (z4 vb) ∉ insert (z4 va) (insert (z4 vb) U2) := by
              rw [← qmv,← hz_bin];intro hm
              rcases Finset.mem_insert.mp hm with h1 | hm;exact hza (v9 h1)
              rcases Finset.mem_insert.mp hm with h2 | hm;exact hzb (v9 h2)
              exact hzU2 hm
            let I1 := insert a (insert b I0)
            have heq1:I1.image (fun i => W.getD i zero)=insert va (insert vb U) := by simp [I1,U,va,vb]
            have heq2:I1.image (fun i => z4 (W.getD i zero))=insert (z4 va) (insert (z4 vb) U2) := by simp [I1,U2,va,vb]
            refine ⟨k+1,u,I1,Nat.le_refl _,?_,?_,?_,?_,?_,?_,?_⟩
            . intro i hi
              rcases Finset.mem_insert.mp hi with rfl | hi;exact ha_lt
              rcases Finset.mem_insert.mp hi with rfl | hi;exact hb_lt
              exact hI0lt i hi
            . intro i hi
              rcases Finset.mem_insert.mp hi with rfl | hi;exact ha_ok
              rcases Finset.mem_insert.mp hi with rfl | hi;exact hb_ok
              exact hI0ok i hi
            . intro h0
              rcases Finset.mem_insert.mp h0 with rfl | h0;exact Or.inr ⟨hidxS,ha_in⟩
              rcases Finset.mem_insert.mp h0 with rfl | h0;exact Or.inr ⟨hidxS,hb_in⟩
              exact Or.inl (h0sub.mp h0)
            . intro h9
              rcases Finset.mem_insert.mp h9 with rfl | h9;exact Or.inr ⟨hidxS,ha_in⟩
              rcases Finset.mem_insert.mp h9 with rfl | h9;exact Or.inr ⟨hidxS,hb_in⟩
              exact Or.inl (h9sub.mp h9)
            . intro h9;rw [heq1]
              have h9I:9 ∉ I := fun hm => h9 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (h9sub.mpr hm)))
              exact qcs ha_p hb_p hab hfr (by rw [← hz_bin,← hIU];exact hL0 h9I)
            . intro h0;rw [heq2]
              have h0I:0 ∉ I := fun hm => h0 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (h0sub.mpr hm)))
              exact yn (qb6 ha_p) (qb6 hb_p) (fun e => hab (v9 e)) (hall2 h0) hfr2
                (by rw [← qmv,← hz_bin,← hIU2];exact hL2 h0I)
            . intro hn;rw [heq1]
              exact yn ha_p hb_p hab (hall3 hn) hfr (by rw [← hz_bin,← hIU];exact hL3 hn)
      rcases hsp with ⟨hop,a,hins,haS,halt⟩ | ⟨hop,a,b,hins,haS,hbS,halt,hblt⟩ |
          ⟨hop,b,hins,hbS,hblt⟩ | ⟨hop,b,hins,hbS,hblt⟩
      . have hz_neg:z=neg (W.getD a zero) := by rw [hgv];simp [gv,hop,hins]
        have hza:z ≠ W.getD a zero := fun e => by
          have hbit := congrArg (bit ⟨0,by decide⟩) (e.symm.trans hz_neg)
          rw [yh] at hbit;cases h:bit ⟨0,by decide⟩ (W.getD a zero) <;> simp [h] at hbit
        have hfr:neg (W.getD a zero) ∉ insert (W.getD a zero) U := by
          rw [← hz_neg];intro hm;rcases Finset.mem_insert.mp hm with h1 | hm;exact hza h1;exact hzU hm
        have hfr2:neg (z4 (W.getD a zero)) ∉ insert (z4 (W.getD a zero)) U2 := by
          rw [← qfc,← hz_neg];intro hm
          rcases Finset.mem_insert.mp hm with h1 | hm;exact hza (v9 h1);exact hzU2 hm
        obtain ⟨hap,ha0,ha9⟩ := hS a haS
        have ha2x:z4 (W.getD a zero) ≠ qu := fun e => ha9 (v9 (e.trans qfb.symm))
        let I1 := insert a I0
        have heq1:I1.image (fun i => W.getD i zero)=insert (W.getD a zero) U := by simp [I1,U]
        have heq2:I1.image (fun i => z4 (W.getD i zero))=insert (z4 (W.getD a zero)) U2 := by simp [I1,U2]
        refine ⟨k+1,u+1,I1,Nat.le_refl _,?_,?_,?_,?_,?_,?_,?_⟩
        . intro i hi;rcases Finset.mem_insert.mp hi with rfl | hm;exact halt;exact hI0lt i hm
        . intro i hi;rcases Finset.mem_insert.mp hi with rfl | hm;exact Or.inl haS;exact hI0ok i hm
        . intro h0;rcases Finset.mem_insert.mp h0 with rfl | hm;exact Or.inr ⟨hidxS,by simp [hins]⟩;exact Or.inl (h0sub.mp hm)
        . intro h9;rcases Finset.mem_insert.mp h9 with rfl | hm;exact Or.inr ⟨hidxS,by simp [hins]⟩;exact Or.inl (h9sub.mp hm)
        . intro h9;rw [heq1]
          have h9I:9 ∉ I := fun hm => h9 (Finset.mem_insert_of_mem (h9sub.mpr hm))
          exact qdv hap hfr (by rw [← hz_neg,← hIU];exact hL0 h9I)
        . intro h0;rw [heq2]
          have h0I:0 ∉ I := fun hm => h0 (Finset.mem_insert_of_mem (h0sub.mpr hm))
          exact qaf (qb6 hap) (au2 ha2x) hfr2
            (by rw [← qfc,← hz_neg,← hIU2];exact hL2 h0I)
        . intro hn;rw [heq1]
          exact qaf hap (au3 ha0 ha9) hfr (by rw [← hz_neg,← hIU];exact hL3 hn)
      . obtain ⟨hap,ha0,ha9⟩ := hS a haS;obtain ⟨hbp,hb0,hb9⟩ := hS b hbS
        have ha2x:z4 (W.getD a zero) ≠ qu := fun e => ha9 (v9 (e.trans qfb.symm))
        have hb2x:z4 (W.getD b zero) ≠ qu := fun e => hb9 (v9 (e.trans qfb.symm))
        rcases hop with hop | hop
        . exact hbin_helper false a b halt hblt (Or.inl haS) (Or.inl hbS) (by simp [hins]) (by simp [hins])
            hap hbp (by rw [hgv];simp [gv,hop,hins,(vl _).1])
            (fun _ => qvz) (fun _ => qvy ha0 hb0 ha9 hb9)
        . exact hbin_helper true a b halt hblt (Or.inl haS) (Or.inl hbS) (by simp [hins]) (by simp [hins])
            hap hbp (by rw [hgv];simp [gv,hop,hins,(vl _).2.1])
            (fun _ => zgc ha2x hb2x) (fun _ => qvy ha0 hb0 ha9 hb9)
      . obtain ⟨hbp,_,hb9⟩ := hS b hbS
        have h0in:0 ∈ g.inputs := by rcases hins with h | h <;> simp [h]
        have hbin_in:b ∈ g.inputs := by rcases hins with h | h <;> simp [h]
        have hz_bin:z=bin true (W.getD 0 zero) (W.getD b zero) := by
          rw [hgv];rcases hins with h | h
          . simp [gv,hop,h,(vl _).2.1]
          . simp [gv,hop,h,(vl _).2.1,qau]
        exact hbin_helper true 0 b (by omega) hblt (Or.inr (Or.inl rfl)) (Or.inl hbS) h0in hbin_in
          (hW0 ▸ hpx0) hbp hz_bin (fun h0 => False.elim (h0 (Finset.mem_insert_self 0 _))) (fun hn => by
            have hx0U:qu ∉ U := fun h => hno0 hn hidxS h0in
              (h0sub.mp ((qep hI0ok hW0 hW9 (fun m hm => (hS m hm).2)).1.mp h))
            rw [hW0,decide_eq_false hx0U];exact zc6 hb9)
      . obtain ⟨hbp,hb0,_⟩ := hS b hbS
        have h9in:9 ∈ g.inputs := by rcases hins with h | h <;> simp [h]
        have hbin_in:b ∈ g.inputs := by rcases hins with h | h <;> simp [h]
        have hz_bin:z=bin false (W.getD 9 zero) (W.getD b zero) := by
          rw [hgv];rcases hins with h | h
          . simp [gv,hop,h,(vl _).1]
          . simp [gv,hop,h,(vl _).1,qau]
        exact hbin_helper false 9 b (by omega) hblt (Or.inr (Or.inr rfl)) (Or.inl hbS) h9in hbin_in
          (hW9 ▸ hpnx0) hbp hz_bin (fun _ => qvz) (fun hn => by
            have hnx0U:qn ∉ U := fun h => hno9 hn hidxS h9in
              (h9sub.mp ((qep hI0ok hW0 hW9 (fun m hm => (hS m hm).2)).2.mp h))
            rw [hW9,decide_eq_false hnx0U];exact zbc hb0 hne09.symm)
  . refine ⟨k,u,I,by omega,?_,hIok,fun h => Or.inl h,fun h => Or.inl h,hL0,hL2,hL3⟩
    intro i hi;have hlt := hIlt i hi;have hne:i ≠ idx := fun e => hmem (e ▸ hi);omega
lemma qb9 (need3:Bool) (S:Set Nat) (W:List Sig)
    (hW0:W.getD 0 zero=qu) (hW9:W.getD 9 zero=qn)
    (hS:∀ m ∈ S,q7 (W.getD m zero) /\ W.getD m zero ≠ qu /\ W.getD m zero ≠ qn) :
    ∀ (gs:List Gate) (base:Nat),
      (∀ (j:Nat) (g:Gate),gs[j]?=some g -> qcq S (10+base+j) g) →
      (∀ (j:Nat) (g:Gate),gs[j]?=some g -> 10+base+j ∈ S -> W.getD (10+base+j) zero=gv W g) →
      ∀ (k u:Nat) (I:Finset Nat),
        (∀ i ∈ I,i < 10+base+gs.length) -> (∀ i ∈ I,i ∈ S \/ i=0 \/ i=9) →
        (9 ∉ I -> v4 vq k u (I.image (fun i => W.getD i zero))) →
        (0 ∉ I -> j3 2 (qa 1023) k u (I.image (fun i => z4 (W.getD i zero)))) →
        (need3=true -> j3 3 vq k u (I.image (fun i => W.getD i zero))) →
        (need3=true -> ∀ (j:Nat) (g:Gate),gs[j]?=some g -> 10+base+j ∈ S -> 0 ∈ g.inputs -> 0 ∉ I ∧
          ∀ (j':Nat) (g':Gate),j < j' -> gs[j']?=some g' -> 10+base+j' ∈ S -> 0 ∉ g'.inputs) →
        (need3=true -> ∀ (j:Nat) (g:Gate),gs[j]?=some g -> 10+base+j ∈ S -> 9 ∈ g.inputs -> 9 ∉ I ∧
          ∀ (j':Nat) (g':Gate),j < j' -> gs[j']?=some g' -> 10+base+j' ∈ S -> 9 ∉ g'.inputs) →
        ∃ (k' u':Nat) (I':Finset Nat),k' ≤ k+gs.length ∧
          (∀ i ∈ I',i < 10+base) /\ (∀ i ∈ I',i ∈ S \/ i=0 \/ i=9) ∧
          ((∀ (j:Nat) (g:Gate),gs[j]?=some g -> 10+base+j ∈ S -> 0 ∉ g.inputs) -> 0 ∉ I -> 0 ∉ I') ∧
          ((∀ (j:Nat) (g:Gate),gs[j]?=some g -> 10+base+j ∈ S -> 9 ∉ g.inputs) -> 9 ∉ I -> 9 ∉ I') ∧
          (9 ∉ I' -> v4 vq k' u' (I'.image (fun i => W.getD i zero))) ∧
          (0 ∉ I' -> j3 2 (qa 1023) k' u' (I'.image (fun i => z4 (W.getD i zero)))) ∧
          (need3=true -> j3 3 vq k' u' (I'.image (fun i => W.getD i zero))) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro base _ _ k u I hlt hok hL0 hL2 hL3 _ _
    exact ⟨k,u,I,by simp,by simpa using hlt,hok,fun _ h => h,fun _ h => h,hL0,hL2,hL3⟩
  | append_singleton gs g ih =>
    intro base hspec hval k u I hlt hok hL0 hL2 hL3 hu0 hu9
    have hlast:(gs ++ [g])[gs.length]?=some g := by simp
    have hlt':∀ i ∈ I,i < (10+base+gs.length)+1 := fun i hi => by have := hlt i hi;simp at this;omega
    obtain ⟨k1,u1,I1,hk1,hlt1,hok1,h0step,h9step,hL01,hL21,hL31⟩ :=
      qzf need3 (by omega) hW0 hW9 hS hlt' hok (hspec gs.length g hlast) (hval gs.length g hlast)
        hL0 hL2 hL3 (fun hn hs h0 => (hu0 hn gs.length g hlast hs h0).1) (fun hn hs h9 => (hu9 hn gs.length g hlast hs h9).1)
    have hlift (j:Nat) (g':Gate) (hj:gs[j]?=some g') : (gs ++ [g])[j]?=some g' /\ j < gs.length := by
      have hjlt:j < gs.length := by by_contra hge;rw [List.getElem?_eq_none (by omega)] at hj;cases hj
      exact ⟨by rw [List.getElem?_append_left hjlt];exact hj,hjlt⟩
    obtain ⟨k2,u2,I2,hk2,hlt2,hok2,hno0,hno9,hL02,hL22,hL32⟩ :=
      ih base (fun j g' hj => hspec j g' (hlift j g' hj).1) (fun j g' hj => hval j g' (hlift j g' hj).1)
        k1 u1 I1 hlt1 hok1 hL01 hL21 hL31
        (fun hn j g' hj hs h0in => by
          obtain ⟨hj1,hjlt⟩ := hlift j g' hj
          obtain ⟨h0I,h0lat⟩ := hu0 hn j g' hj1 hs h0in
          refine ⟨fun h0I1 => ?_,fun j' g'' hjj' hj' hs' => h0lat j' g'' hjj' (hlift j' g'' hj').1 hs'⟩
          rcases h0step h0I1 with hm | ⟨hsg,h0g⟩;exact h0I hm;exact h0lat gs.length g hjlt hlast hsg h0g)
        (fun hn j g' hj hs h9in => by
          obtain ⟨hj1,hjlt⟩ := hlift j g' hj
          obtain ⟨h9I,h9lat⟩ := hu9 hn j g' hj1 hs h9in
          refine ⟨fun h9I1 => ?_,fun j' g'' hjj' hj' hs' => h9lat j' g'' hjj' (hlift j' g'' hj').1 hs'⟩
          rcases h9step h9I1 with hm | ⟨hsg,h9g⟩;exact h9I hm;exact h9lat gs.length g hjlt hlast hsg h9g)
    refine ⟨k2,u2,I2,by simp;omega,hlt2,hok2,?_,?_,hL02,hL22,hL32⟩
    . intro hall h0I
      apply hno0 (fun j g' hj hs => hall j g' (hlift j g' hj).1 hs)
      intro h0I1;rcases h0step h0I1 with hm | ⟨hsg,h0g⟩;exact h0I hm;exact hall gs.length g hlast hsg h0g
    . intro hall h9I
      apply hno9 (fun j g' hj hs => hall j g' (hlift j g' hj).1 hs)
      intro h9I1;rcases h9step h9I1 with hm | ⟨hsg,h9g⟩;exact h9I hm;exact hall gs.length g hlast hsg h9g
lemma qf2 {k u:Nat} {T:Finset Sig} (hk:k ≤ 14)
    (hL:v4 vq k u T) (hsub:∀ a ∈ T,a ∈ inputs) : False := by
  have hess:zo vq inputs (z2 511 13438558465)=true := by decide +kernel
  have hall:(z2 511 13438558465).map Prod.fst=inputs := by decide +kernel
  have hT:inputs.toFinset=T := by
    ext a;rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hsub a⟩
    obtain ⟨r,s,hd,iso⟩ := vn hess a (hall ▸ List.mem_toFinset.mpr hm)
    exact vz hL inputs a hsub r s hd iso
  exact qya k u hk (hT.symm ▸ hL)
lemma qf1 {k u:Nat} {T:Finset Sig} (hk:k ≤ 14)
    (hL:j3 2 (qa 1023) k u T) (hsub:∀ a ∈ T,a ∈ inputs) : False := by
  have hess:zo (qa 1023) inputs (z2 1023 13438558465)=true := by decide +kernel
  have hall:(z2 1023 13438558465).map Prod.fst=inputs := by decide +kernel
  have hT:inputs.toFinset=T := by
    ext a;rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hsub a⟩
    obtain ⟨r,s,hd,iso⟩ := vn hess a (hall ▸ List.mem_toFinset.mpr hm)
    exact vz (wc hL) inputs a hsub r s hd iso
  exact qrg k u hk (hT.symm ▸ hL)
lemma qrc {k u:Nat} {T:Finset Sig} (hk:k ≤ 14)
    (hL:j3 3 vq k u T) (hsub:∀ a ∈ T,a ∈ inputs ++ [qn])
    (hx0:qu ∈ T) (hnx0:qn ∈ T) : False := by
  let xs := (z2 511 13438558465).filter (fun p => p.1 != qu)
  have hess:zo vq (inputs ++ [qn]) xs=true := by decide +kernel
  have hall:inputs.all (fun a => a==qu||(xs.map Prod.fst).contains a)=true := by decide +kernel
  have hT:(inputs ++ [qn]).toFinset=T := by
    ext a;rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hsub a⟩
    rcases List.mem_append.mp hm with hi | hn
    . by_cases ha0:a=qu
      . exact ha0 ▸ hx0
      . have h1 := List.all_eq_true.mp hall a hi
        simp only [Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at h1
        obtain ⟨r,s,hd,iso⟩ := vn hess a (List.mem_toFinset.mpr (h1.resolve_left ha0))
        exact vz (wc hL) (inputs ++ [qn]) a hsub r s hd iso
    . rw [List.mem_singleton] at hn;exact hn ▸ hnx0
  exact qre k u hk (hT.symm ▸ hL)
lemma qub (W:List Sig) (p:List Gate) (g:Gate) (t:List Gate) (init:List Sig)
    (hW:W=ze (p ++ g :: t) init) (hlt:∀ k ∈ g.inputs,k < init.length+p.length) :
    W.getD (init.length+p.length) zero=gv W g := by
  have hex:W=ze t (ze p init ++ [gv (ze p init) g]) := by rw [hW,qc3];rfl
  have hlp:(ze p init).length=init.length+p.length := qc2 p init
  have hgw:W.getD (init.length+p.length) zero=gv (ze p init) g := by
    rw [hex,jg t _ (init.length+p.length) (by simp [hlp]),← hlp,yo]
  rw [hgw]
  have hmap:g.inputs.map (fun i => (ze p init).getD i zero)=g.inputs.map (fun i => W.getD i zero) := by
    apply List.map_congr_left;intro k hk
    have hklt := hlt k hk
    rw [hex,jg t _ k (by simp [hlp];omega),List.getD_append _ _ _ _ (by omega)]
  unfold gv;rw [hmap]
lemma qgc (j:Nat) (hj:j < 10) (hne:j ≠ 0) :
    z4 ((inputs ++ [qn]).getD j zero) ∈ inputs := by
  have h1:z4 ((inputs ++ [qn]).getD j zero)=q1 [jx] ((inputs ++ [qn]).getD j zero) :=
    (zt [jx] _).symm
  rw [h1]
  have hmem (w:Sig) (hc:inputs.contains w=true) : w ∈ inputs := by
    simpa only [List.contains_eq_mem,decide_eq_true_eq] using hc
  apply hmem
  interval_cases j
  . exact False.elim (hne rfl)
  . decide +kernel
  . decide +kernel
  . decide +kernel
  . decide +kernel
  . decide +kernel
  . decide +kernel
  . decide +kernel
  . decide +kernel
  . decide +kernel
lemma main_3216:∀ (x1 x2 x3:List Gate) (x4 x5:Gate) (x6:Nat),have x7:Circuit:={gates:=x1++x4::(x2++x5::x3),output:=x6};PEqualNP.MetaComplexity.FanInTwo x7 -> x1.length+x2.length+x3.length=12 -> x6<24 -> (∀ x11 ∈ x7.gates,(x11.op=GateOp.not -> x11.inputs.length<=1) /\ ∀ x13 ∈ x11.inputs,x13<=24) -> (∀ x12 ∈ x1++x2++x3,0 ∉ x12.inputs /\ 9 ∉ x12.inputs) -> (List.filter (fun x13:Gate => x13.inputs.contains 4) (x1++x2++x3)).length<=1 -> (∀ x14 ∈ [x4,x5],0 ∈ x14.inputs \/ 9 ∈ x14.inputs) -> (∀ x15:Fin 8 -> Bool,x7.eval (false::List.ofFn x15++[true])=[1,10,19,5,14,23,38,47,60].any fun x16:Nat => x15 (Fin.ofNat 8 (x16/8))&&x15 (Fin.ofNat 8 (x16 % 8))) -> ∃ x16:Fin 8 -> Bool,x7.eval (true::List.ofFn x16++[false]) ≠ (x16 0||x16 3||x16 4||x16 1&&x16 2||x16 1&&x16 6||x16 2&&x16 7||x16 5&&x16 7) := by
  intro P Q R a b o
  let C:Circuit := ⟨P ++ a :: (Q ++ b :: R),o⟩
  change PEqualNP.MetaComplexity.FanInTwo C -> _
  intro hfan hlen ho1 hnorm hclean _ hhits lowEval
  by_contra! highEval
  have hnok:∀ g ∈ C.gates,NOk g := fun g hg => ⟨hfan g hg,(hnorm g hg).1⟩
  have hsz:C.gates.length=14 := by
    change (P ++ a :: (Q ++ b :: R)).length=14;simp only [List.length_append,List.length_cons];omega
  have hrd_a:vo a=true := by rcases hhits a (by simp) with h | h <;> simp [vo,h]
  have hrd_b:vo b=true := by rcases hhits b (by simp) with h | h <;> simp [vo,h]
  have hrd_clean (g:Gate) (hg:g ∈ P ++ Q ++ R) : vo g=false := by
    obtain ⟨h0,h9⟩ := hclean g hg;simp [vo,h0,h9]
  have hfilt_eq (L:List Gate) (inc:∀ g ∈ L,g ∈ P ++ Q ++ R) : L.filter (fun g => !vo g)=L :=
    List.filter_eq_self.mpr (fun g hg => by simp [hrd_clean g (inc g hg)])
  have hnonrd:(C.gates.filter (fun g => !vo g)).length=12 := by
    change ((P ++ a :: (Q ++ b :: R)).filter (fun g => !vo g)).length=12
    simp only [List.filter_append,List.filter_cons,hrd_a,hrd_b,Bool.not_true,Bool.false_eq_true,ite_false]
    rw [hfilt_eq P (fun g h => by simp [h]),hfilt_eq Q (fun g h => by simp [h]),hfilt_eq R (fun g h => by simp [h])]
    simp only [List.length_append];omega
  set acc := elim C.gates (vf,[]) with hacc
  have hinv:∀ y:Fin 8 -> Bool,zbd (List.ofFn y) (zk C.gates (false :: List.ofFn y ++ [true])) acc :=
    fun y => qzw (List.ofFn y) (by simp) C.gates _ _ (fun g hg => (hnok g hg).1) (qt8 y)
  have hval_out:∀ y:Fin 8 -> Bool,(acc.1.getD o (Sum.inl false)).val (zk acc.2 (List.ofFn y))=f0 y :=
    fun y => by rw [((hinv y).2 o).2];exact lowEval y
  have hlen_le:acc.2.length ≤ 12 := by
    have h1 := qa1 C.gates (vf,[]) hnok (by simp [vf]) rfl rfl
    simp only [List.length_nil,Nat.zero_add,hnonrd] at h1;exact h1
  have hout_inr:∃ outE,acc.1.getD o (Sum.inl false)=Sum.inr outE := by
    cases hst:acc.1.getD o (Sum.inl false) with
    | inl c =>
      exfalso
      have hne:f0 (fun _ => true) ≠ f0 (fun _ => false) := by decide +kernel
      exact hne (by rw [← hval_out (fun _ => true),← hval_out (fun _ => false),hst];rfl)
    | inr outE => exact ⟨outE,rfl⟩
  obtain ⟨outE,houtE⟩ := hout_inr
  have hlen_eg:acc.2.length=12 := by
    by_contra hne;apply qch
    refine ⟨⟨acc.2,outE⟩,qng C.gates (vf,[]) (by simp),by change acc.2.length ≤ 11;omega,fun y => ?_⟩
    have := hval_out y;rw [houtE] at this;exact this
  have hev_eg:∀ y:Fin 8 -> Bool,(zk acc.2 (List.ofFn y)).getD outE false=f0 y := fun y => by
    have := hval_out y;rw [houtE] at this;exact this
  let S:Set Nat := { i | ∃ j,acc.1.getD i (Sum.inl false)=Sum.inr j }
  have hoS:o ∈ S := ⟨outE,houtE⟩
  have hacc0:acc.1.getD 0 (Sum.inl false)=Sum.inl false := qao 0 _ C.gates (vf,[]) (by simp [vf])
  have hacc9:acc.1.getD 9 (Sum.inl false)=Sum.inl true := qao 9 _ C.gates (vf,[]) (by simp [vf])
  have h0nS:0 ∉ S := fun ⟨_,h⟩ => by rw [hacc0] at h;cases h
  have h9nS:9 ∉ S := fun ⟨_,h⟩ => by rw [hacc9] at h;cases h
  let W := ze C.gates (inputs ++ [qn])
  have hW0:W.getD 0 zero=qu := by
    rw [jg C.gates (inputs ++ [qn]) 0 (by simp [inputs])];simp [qu,inputs]
  have hW9:W.getD 9 zero=qn := by
    rw [jg C.gates (inputs ++ [qn]) 9 (by simp [inputs])];simp [inputs]
  have hWo:W.getD o zero=vq := by
    apply BitVec.eq_of_getLsbD_eq;intro j hj;let i:Fin 512 := ⟨j,hj⟩
    change bit i (W.getD o zero)=bit i vq
    rw [← qe1,yp C.gates i (inputs ++ [qn]) (fun g hg => (hnok g hg).1.1),qfy,quc]
    let x := qm0 i;let y := Fin.tail x
    have eta:Fin.cons (x 0) y=x := Fin.cons_self_tail x
    have rows:List.ofFn x=x 0 :: List.ofFn y := by
      conv_lhs => rw [← eta,List.ofFn_succ]
      simp [y,Fin.cons_succ]
    have table0:∀ u:Fin 8 -> Bool,f0 u=G9 (Fin.cons false u) := by decide +kernel
    have table1:∀ u:Fin 8 -> Bool,(u 0||u 3||u 4||u 1&&u 2||u 1&&u 6 ||
        u 2&&u 7||u 5&&u 7)=G9 (Fin.cons true u) := by decide +kernel
    change C.eval (List.ofFn x ++ [!x 0])=G9 x;rw [rows]
    cases hx0:x 0
    . exact (lowEval y).trans ((table0 y).trans (congrArg G9 (by simpa only [hx0] using eta)))
    . exact (highEval y).trans ((table1 y).trans (congrArg G9 (by simpa only [hx0] using eta)))
  have hS_prop:∀ m ∈ S,q7 (W.getD m zero) /\ W.getD m zero ≠ qu /\ W.getD m zero ≠ qn := by
    intro m ⟨j,hj⟩
    have hj_lt:j < 8+acc.2.length := by have hv := ((hinv (fun _ => false)).2 m).1;rw [hj] at hv;exact hv
    have hpj := qkk acc.2 outE (qng C.gates (vf,[]) (by simp)) hlen_eg hev_eg j hj_lt
    have hrel (i:Fin 512) : bit (ev0 i) (W.getD m zero)=bit i ((ze acc.2 (qo 510)).getD j zero) := by
      rw [← qe1,← qe1,
        yp C.gates (ev0 i) (inputs ++ [qn]) (fun g hg => (hnok g hg).1.1),zak,
        yp acc.2 i (qo 510) (fun g hg => (qng C.gates (vf,[]) (by simp) g hg).1),qb2]
      have hi := ((hinv (qm1 i)).2 m).2;rw [hj] at hi;exact hi.symm
    have hev0_x0:∀ i:Fin 512,bit (ev0 i) qu=false := by decide +kernel
    have hev0_nx0:∀ i:Fin 512,bit (ev0 i) qn=true := by decide +kernel
    refine ⟨⟨fun hmz => hpj.1 ?_,fun hmo => hpj.2 ?_⟩,fun hmx => hpj.1 ?_,fun hmnx => hpj.2 ?_⟩
    . apply BitVec.eq_of_getLsbD_eq;intro r hr;change bit ⟨r,hr⟩ _=bit ⟨r,hr⟩ zero;rw [← hrel,hmz,j5,j5]
    . apply BitVec.eq_of_getLsbD_eq;intro r hr;change bit ⟨r,hr⟩ _=bit ⟨r,hr⟩ one;rw [← hrel,hmo,yg,yg]
    . apply BitVec.eq_of_getLsbD_eq;intro r hr;change bit ⟨r,hr⟩ _=bit ⟨r,hr⟩ zero;rw [← hrel,hmx,hev0_x0,j5]
    . apply BitVec.eq_of_getLsbD_eq;intro r hr;change bit ⟨r,hr⟩ _=bit ⟨r,hr⟩ one;rw [← hrel,hmnx,hev0_nx0,yg]
  have hgate_info:∀ (j:Nat) (g:Gate),C.gates[j]?=some g →
      qcq S (10+0+j) g /\ (10+0+j ∈ S -> W.getD (10+0+j) zero=gv W g) := by
    intro j g hj
    have hjlt:j < C.gates.length := by by_contra hge;rw [List.getElem?_eq_none (by omega)] at hj;cases hj
    have hsplit:C.gates=C.gates.take j ++ g :: C.gates.drop (j+1) := by
      have hg_eq:C.gates[j]=g := Option.some.inj ((List.getElem?_eq_getElem hjlt).symm.trans hj)
      rw [← hg_eq];exact qdw C.gates j hjlt
    set pre := C.gates.take j;set post := C.gates.drop (j+1)
    have hlpre:pre.length=j := by simp [pre];omega
    have hacc_p:elim C.gates (vf,[])=elim post (z3 (elim pre (vf,[])) g) := by
      rw [hsplit,qqw,qdd]
    set acc_p := elim pre (vf,[])
    have hl1:acc_p.1.length=10+j := by rw [qnv];simp [vf,hlpre]
    have haccp0:acc_p.1.getD 0 (Sum.inl false)=Sum.inl false := qao 0 _ pre (vf,[]) (by simp [vf])
    have haccp9:acc_p.1.getD 9 (Sum.inl false)=Sum.inl true := qao 9 _ pre (vf,[]) (by simp [vf])
    have hnok_pre:∀ g' ∈ pre,NOk g' := fun g' hg' => hnok g' (hsplit ▸ List.mem_append_left _ hg')
    have hnok_g:NOk g := hnok g (hsplit ▸ List.mem_append_right _ List.mem_cons_self)
    have hnok_post:∀ g' ∈ post,NOk g' := fun g' hg' => hnok g' (hsplit ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hg'))
    have hst_lt (k:Nat) (hk:k < 10+j) : acc.1.getD k (Sum.inl false)=acc_p.1.getD k (Sum.inl false) := by
      rw [hacc,hacc_p,qao k _ post _ (by simp [z3,hl1];omega)]
      simp only [z3];exact vm _ _ _ _ (by omega)
    have hst_at:acc.1.getD (10+j) (Sum.inl false) =
        (q9 g.op (8+acc_p.2.length) (g.inputs.map fun i => acc_p.1.getD i (Sum.inl false))).2 := by
      rw [hacc,hacc_p,qao (10+j) _ post _ (by simp [z3,hl1])]
      simp only [z3];rw [← hl1,yo]
    have hget_inr (k m:Nat) (hk:acc_p.1.getD k (Sum.inl false)=Sum.inr m) : k ∈ S /\ k < 10+j := by
      have hklt:k < 10+j := by by_contra hge;rw [List.getD_eq_default _ _ (by omega)] at hk;cases hk
      exact ⟨⟨m,by rw [hst_lt k hklt];exact hk⟩,hklt⟩
    have hgspec:qcq S (10+0+j) g := by
      simp only [Nat.add_zero]
      intro hjs
      by_cases hrd:vo g=true
      . obtain ⟨m,hm⟩ := hjs;rw [hst_at] at hm
        have hrd':0 ∈ g.inputs \/ 9 ∈ g.inputs := by
          simpa only [vo,Bool.or_eq_true,List.contains_eq_mem,decide_eq_true_eq] using hrd
        rcases qf5 g.op (8+acc_p.2.length) acc_p.1 g.inputs m hnok_g.1.1 hnok_g.1.2 hnok_g.2
            haccp0 haccp9 hrd' hm with ⟨hop,k,hks,hkinr⟩ | ⟨hop,k,hks,hkinr⟩
        . obtain ⟨hkS,hklt⟩ := hget_inr k m hkinr;exact Or.inr (Or.inr (Or.inl ⟨hop,k,hks,hkS,hklt⟩))
        . obtain ⟨hkS,hklt⟩ := hget_inr k m hkinr;exact Or.inr (Or.inr (Or.inr ⟨hop,k,hks,hkS,hklt⟩))
      . have hb1:acc_p.2.length ≤ (pre.filter fun g => !vo g).length := by
          simpa using qa1 pre (vf,[]) hnok_pre (by simp [vf]) rfl rfl
        have hb2 := qa4 acc_p g hnok_g haccp0 haccp9
        have hb3 := qa1 post (z3 acc_p g) hnok_post (by simp [z3,hl1];omega)
          (by simp only [z3];rw [vm _ _ _ _ (by omega)];exact haccp0)
          (by simp only [z3];rw [vm _ _ _ _ (by omega)];exact haccp9)
        have hfs:(C.gates.filter fun g => !vo g).length =
            (pre.filter fun g => !vo g).length+1+(post.filter fun g => !vo g).length := by
          conv_lhs => rw [hsplit]
          simp [List.filter_append,hrd];omega
        have hstep_eq:(z3 acc_p g).2.length=acc_p.2.length+1 := by
          rw [hacc,hacc_p] at hlen_eg
          have hrdf:vo g=false := Bool.eq_false_iff.mpr hrd
          simp only [hrdf,Bool.false_eq_true,ite_false] at hb2
          omega
        have hsome:∃ e,(q9 g.op (8+acc_p.2.length)
            (g.inputs.map fun i => acc_p.1.getD i (Sum.inl false))).1=some e := by
          cases hopt:(q9 g.op (8+acc_p.2.length)
              (g.inputs.map fun i => acc_p.1.getD i (Sum.inl false))).1 with
          | none => simp only [z3,hopt,Option.toList_none,List.append_nil] at hstep_eq;omega
          | some e => exact ⟨e,rfl⟩
        obtain ⟨e,he⟩ := hsome
        obtain ⟨_,hsh⟩ := qdg g.op (8+acc_p.2.length) _ e hnok_g.1.1
          (by simpa using hnok_g.1.2) (fun h => by simpa using hnok_g.2 h) he
        rcases hsh with ⟨hop,m,hins⟩ | ⟨hop,m1,m2,hins⟩
        . have hl:g.inputs.length=1 := by simpa using congrArg List.length hins
          rcases hgl:g.inputs with _ | ⟨k1,_ | ⟨k2,l⟩⟩
          . simp [hgl] at hl
          . simp only [hgl,List.map_cons,List.map_nil,List.cons.injEq,and_true] at hins
            obtain ⟨hk1S,hk1lt⟩ := hget_inr k1 m hins;exact Or.inl ⟨hop,k1,rfl,hk1S,hk1lt⟩
          . simp [hgl] at hl
        . have hl:g.inputs.length=2 := by simpa using congrArg List.length hins
          rcases hgl:g.inputs with _ | ⟨k1,_ | ⟨k2,_ | ⟨k3,l⟩⟩⟩
          . simp [hgl] at hl
          . simp [hgl] at hl
          . simp only [hgl,List.map_cons,List.map_nil,List.cons.injEq,and_true] at hins
            obtain ⟨hk1S,hk1lt⟩ := hget_inr k1 m1 hins.1;obtain ⟨hk2S,hk2lt⟩ := hget_inr k2 m2 hins.2
            exact Or.inr (Or.inl ⟨hop,k1,k2,rfl,hk1S,hk2S,hk1lt,hk2lt⟩)
          . simp [hgl] at hl
    refine ⟨hgspec,fun hjs => ?_⟩
    have hlt_in:∀ k ∈ g.inputs,k < (inputs ++ [qn]).length+pre.length := by
      have hlen10:(inputs ++ [qn]).length=10 := by simp [inputs]
      rw [hlen10,hlpre]
      have hsp := hgspec hjs
      simp only [Nat.add_zero] at hsp
      intro k hk
      rcases hsp with ⟨_,k1,hins,_,h1⟩ | ⟨_,k1,k2,hins,_,_,h1,h2⟩ |
          ⟨_,k1,hins,_,h1⟩ | ⟨_,k1,hins,_,h1⟩
      . rw [hins,List.mem_singleton] at hk;omega
      . rw [hins] at hk;simp at hk;rcases hk with rfl | rfl <;> omega
      . rcases hins with hins | hins <;> (rw [hins] at hk;simp at hk;rcases hk with rfl | rfl <;> omega)
      . rcases hins with hins | hins <;> (rw [hins] at hk;simp at hk;rcases hk with rfl | rfl <;> omega)
    simpa [inputs,hlpre] using qub W pre g post (inputs ++ [qn]) (by rw [← hsplit]) hlt_in
  have hspec_all:∀ (j:Nat) (g:Gate),C.gates[j]?=some g -> qcq S (10+0+j) g :=
    fun j g hj => (hgate_info j g hj).1
  have hval_all:∀ (j:Nat) (g:Gate),C.gates[j]?=some g -> 10+0+j ∈ S -> W.getD (10+0+j) zero=gv W g :=
    fun j g hj => (hgate_info j g hj).2
  let ia := P.length;let ib := P.length+1+Q.length
  have honly_ab:∀ (j:Nat) (g:Gate),C.gates[j]?=some g -> (0 ∈ g.inputs \/ 9 ∈ g.inputs) -> j=ia \/ j=ib := by
    intro j g hj hrd;by_contra hne;push Not at hne
    have hjlt:j < C.gates.length := by by_contra hge;rw [List.getElem?_eq_none (by omega)] at hj;cases hj
    have hg_eq:C.gates[j]=g := Option.some.inj ((List.getElem?_eq_getElem hjlt).symm.trans hj)
    have hmem:g ∈ P ++ Q ++ R := by
      by_cases hp:j < P.length
      . have:C.gates[j]=P[j] := List.getElem_append_left hp
        rw [← hg_eq,this];exact List.mem_append_left _ (List.mem_append_left _ (List.getElem_mem hp))
      . by_cases hq:j - (P.length+1) < Q.length
        . have:C.gates[j]=Q[j - (P.length+1)] := by
            change (P ++ a :: (Q ++ b :: R))[j]=_
            rw [List.getElem_append_right (by omega)]
            simp only [show j - P.length=(j - (P.length+1))+1 by omega,List.getElem_cons_succ]
            exact List.getElem_append_left hq
          rw [← hg_eq,this];exact List.mem_append_left _ (List.mem_append_right _ (List.getElem_mem hq))
        . have hrlt:j - (P.length+1+Q.length+1) < R.length := by omega
          have:C.gates[j]=R[j - (P.length+1+Q.length+1)] := by
            change (P ++ a :: (Q ++ b :: R))[j]=_
            rw [List.getElem_append_right (by omega)]
            simp only [show j - P.length=(j - (P.length+1))+1 by omega,List.getElem_cons_succ]
            rw [List.getElem_append_right (by omega)]
            simp only [show j - (P.length+1) - Q.length=(j - (P.length+1+Q.length+1))+1 by omega,List.getElem_cons_succ]
          rw [← hg_eq,this];exact List.mem_append_right _ (List.getElem_mem hrlt)
    obtain ⟨h0,h9⟩ := hclean g hmem;exact hrd.elim h0 h9
  have hnot_both (j:Nat) (g:Gate) (hj:C.gates[j]?=some g) (hs:10+0+j ∈ S) :
      ¬ (0 ∈ g.inputs /\ 9 ∈ g.inputs) := by
    have hsp := hspec_all j g hj hs
    rintro ⟨h0,h9⟩
    rcases hsp with ⟨_,k,hins,hkS,_⟩ | ⟨_,k1,k2,hins,hk1S,hk2S,_,_⟩ |
        ⟨_,k,hins,hkS,_⟩ | ⟨_,k,hins,hkS,_⟩
    . rw [hins,List.mem_singleton] at h0;exact h0nS (h0 ▸ hkS)
    . rw [hins] at h0;simp at h0;rcases h0 with rfl | rfl;exact h0nS hk1S;exact h0nS hk2S
    . rcases hins with hins | hins <;> (rw [hins] at h9;simp at h9;exact h9nS (h9 ▸ hkS))
    . rcases hins with hins | hins <;> (rw [hins] at h0;simp at h0;exact h0nS (h0 ▸ hkS))
  have hL0_init:9 ∉ ({o} : Finset Nat) -> v4 vq 0 0 (({o} : Finset Nat).image (fun i => W.getD i zero)) := by
    intro _;simp only [Finset.image_singleton,hWo];exact qda (zx _ (by decide +kernel))
  have hL2_init:0 ∉ ({o} : Finset Nat) -> j3 2 (qa 1023) 0 0 (({o} : Finset Nat).image (fun i => z4 (W.getD i zero))) := by
    intro _;simp only [Finset.image_singleton,hWo,qqv];exact qaz (zx _ (by decide +kernel))
  have ho_lt:∀ i ∈ ({o} : Finset Nat),i < 10+0+C.gates.length := fun i hi => by rw [Finset.mem_singleton] at hi;omega
  have ho_ok:∀ i ∈ ({o} : Finset Nat),i ∈ S \/ i=0 \/ i=9 := fun i hi => by rw [Finset.mem_singleton] at hi;exact Or.inl (hi ▸ hoS)
  have ho_ne0:0 ∉ ({o} : Finset Nat) := by simp [show (0:Nat) ≠ o from fun e => h0nS (e ▸ hoS)]
  have ho_ne9:9 ∉ ({o} : Finset Nat) := by simp [show (9:Nat) ≠ o from fun e => h9nS (e ▸ hoS)]
  have hsub1 (I':Finset Nat) (hlt:∀ i ∈ I',i < 10+0) (h9:9 ∉ I') :
      ∀ v ∈ I'.image (fun i => W.getD i zero),v ∈ inputs := by
    intro v hv;obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have hilt := hlt i hi;have hne9:i ≠ 9 := fun e => h9 (e ▸ hi)
    rw [jg C.gates (inputs ++ [qn]) i (by simp [inputs];omega),
      List.getD_append _ _ _ _ (by simp [inputs];omega),List.getD_eq_getElem _ _ (by simp [inputs];omega)]
    exact List.getElem_mem _
  have hsub2 (I':Finset Nat) (hlt:∀ i ∈ I',i < 10+0) (h0:0 ∉ I') :
      ∀ v ∈ I'.image (fun i => z4 (W.getD i zero)),v ∈ inputs := by
    intro v hv;obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have hilt := hlt i hi;have hne0:i ≠ 0 := fun e => h0 (e ▸ hi)
    rw [jg C.gates (inputs ++ [qn]) i (by simp [inputs];omega)]
    exact qgc i (by omega) hne0
  have hsub3 (I':Finset Nat) (hlt:∀ i ∈ I',i < 10+0) :
      ∀ v ∈ I'.image (fun i => W.getD i zero),v ∈ inputs ++ [qn] := by
    intro v hv;obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv;have hilt := hlt i hi
    rw [jg C.gates (inputs ++ [qn]) i (by simp [inputs];omega),
      List.getD_eq_getElem _ _ (by simp [inputs];omega)]
    exact List.getElem_mem _
  by_cases hno9_all:∀ (j:Nat) (g:Gate),C.gates[j]?=some g -> 10+0+j ∈ S -> 9 ∉ g.inputs
  . obtain ⟨k',u',I',hk',hlt',_,_,hno9',hL0',_,_⟩ :=
      qb9 false S W hW0 hW9 hS_prop C.gates 0 hspec_all hval_all 0 0 {o} ho_lt ho_ok
        hL0_init hL2_init (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    have h9' := hno9' hno9_all ho_ne9
    exact qf2 (by omega) (hL0' h9') (hsub1 I' hlt' h9')
  . by_cases hno0_all:∀ (j:Nat) (g:Gate),C.gates[j]?=some g -> 10+0+j ∈ S -> 0 ∉ g.inputs
    . obtain ⟨k',u',I',hk',hlt',_,hno0',_,_,hL2',_⟩ :=
        qb9 false S W hW0 hW9 hS_prop C.gates 0 hspec_all hval_all 0 0 {o} ho_lt ho_ok
          hL0_init hL2_init (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
      have h0' := hno0' hno0_all ho_ne0
      exact qf1 (by omega) (hL2' h0') (hsub2 I' hlt' h0')
    . push Not at hno9_all hno0_all
      obtain ⟨j9,g9,hj9,hs9,h9in⟩ := hno9_all
      obtain ⟨j0,g0,hj0,hs0,h0in⟩ := hno0_all
      have huniq0 (j:Nat) (g:Gate) (hj:C.gates[j]?=some g) (hs:10+0+j ∈ S) (h0g:0 ∈ g.inputs) : j=j0 := by
        have hab1 := honly_ab j g hj (Or.inl h0g);have hab0 := honly_ab j0 g0 hj0 (Or.inl h0in)
        have hab9 := honly_ab j9 g9 hj9 (Or.inr h9in)
        have hnej9:j ≠ j9 := fun e => by
          subst e;have hg_eq:g=g9 := Option.some.inj (hj.symm.trans hj9)
          exact hnot_both j g hj hs ⟨h0g,hg_eq ▸ h9in⟩
        have hne09:j0 ≠ j9 := fun e => by
          subst e;have hg_eq:g0=g9 := Option.some.inj (hj0.symm.trans hj9)
          exact hnot_both j0 g0 hj0 hs0 ⟨h0in,hg_eq ▸ h9in⟩
        omega
      have huniq9 (j:Nat) (g:Gate) (hj:C.gates[j]?=some g) (hs:10+0+j ∈ S) (h9g:9 ∈ g.inputs) : j=j9 := by
        have hab1 := honly_ab j g hj (Or.inr h9g);have hab0 := honly_ab j0 g0 hj0 (Or.inl h0in)
        have hab9 := honly_ab j9 g9 hj9 (Or.inr h9in)
        have hnej0:j ≠ j0 := fun e => by
          subst e;have hg_eq:g=g0 := Option.some.inj (hj.symm.trans hj0)
          exact hnot_both j g hj hs ⟨hg_eq ▸ h0in,h9g⟩
        have hne09:j0 ≠ j9 := fun e => by
          subst e;have hg_eq:g0=g9 := Option.some.inj (hj0.symm.trans hj9)
          exact hnot_both j0 g0 hj0 hs0 ⟨h0in,hg_eq ▸ h9in⟩
        omega
      obtain ⟨k',u',I',hk',hlt',_,_,_,hL0',hL2',hL3'⟩ :=
        qb9 true S W hW0 hW9 hS_prop C.gates 0 hspec_all hval_all 0 0 {o} ho_lt ho_ok
          hL0_init hL2_init
          (fun _ => by simp only [Finset.image_singleton,hWo];exact qaz (zx _ (by decide +kernel)))
          (fun _ j g hj hs h0g => ⟨ho_ne0,fun j' g' hjj' hj' hs' h0g' => by
            have e1 := huniq0 j g hj hs h0g;have e2 := huniq0 j' g' hj' hs' h0g';omega⟩)
          (fun _ j g hj hs h9g => ⟨ho_ne9,fun j' g' hjj' hj' hs' h9g' => by
            have e1 := huniq9 j g hj hs h9g;have e2 := huniq9 j' g' hj' hs' h9g';omega⟩)
      by_cases h9I:9 ∈ I'
      . by_cases h0I:0 ∈ I'
        . exact qrc (by omega) (hL3' rfl) (hsub3 I' hlt')
            (Finset.mem_image.mpr ⟨0,h0I,hW0⟩) (Finset.mem_image.mpr ⟨9,h9I,hW9⟩)
        . exact qf1 (by omega) (hL2' h0I) (hsub2 I' hlt' h0I)
      . exact qf2 (by omega) (hL0' h9I) (hsub1 I' hlt' h9I)
end PEqualNP.Outside.L_meta_3216

theorem PEqualNP.Outside.L_meta_3216 :
    ∀ (x1 x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → x1.length + x2.length + x3.length = (12 : ℕ) → x6 < (24 : ℕ) → (∀ x11 ∈ x7.gates, (x11.op = PEqualNP.CircuitLowerBounds.GateOp.not → x11.inputs.length ≤ (1 : ℕ)) ∧ ∀ x13 ∈ x11.inputs, x13 ≤ (24 : ℕ)) → (∀ x12 ∈ x1 ++ x2 ++ x3, (0 : ℕ) ∉ x12.inputs ∧ (9 : ℕ) ∉ x12.inputs) → (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.inputs.contains (4 : ℕ)) (x1 ++ x2 ++ x3)).length ≤ (1 : ℕ) → (∀ x14 ∈ [x4, x5], (0 : ℕ) ∈ x14.inputs ∨ (9 : ℕ) ∈ x14.inputs) → (∀ (x15 : Fin (8 : ℕ) → Bool), x7.eval (Bool.false :: List.ofFn x15 ++ [Bool.true]) = [(1 : ℕ), (10 : ℕ), (19 : ℕ), (5 : ℕ), (14 : ℕ), (23 : ℕ), (38 : ℕ), (47 : ℕ), (60 : ℕ)].any fun (x16 : ℕ) => x15 (Fin.ofNat (8 : ℕ) (x16 / (8 : ℕ))) && x15 (Fin.ofNat (8 : ℕ) (x16 % (8 : ℕ)))) → ∃ (x16 : Fin (8 : ℕ) → Bool), x7.eval (Bool.true :: List.ofFn x16 ++ [Bool.false]) ≠ (x16 (0 : Fin (8 : ℕ)) || x16 (3 : Fin (8 : ℕ)) || x16 (4 : Fin (8 : ℕ)) || x16 (1 : Fin (8 : ℕ)) && x16 (2 : Fin (8 : ℕ)) || x16 (1 : Fin (8 : ℕ)) && x16 (6 : Fin (8 : ℕ)) || x16 (2 : Fin (8 : ℕ)) && x16 (7 : Fin (8 : ℕ)) || x16 (5 : Fin (8 : ℕ)) && x16 (7 : Fin (8 : ℕ))) :=
  PEqualNP.Outside.L_meta_3216.main_3216
