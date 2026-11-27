import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10452
abbrev Forest:=Nat → Nat × Nat
def unpack (packed width index : Nat) : Nat :=
 (packed>>>(width*index))&&&((1<<<width) - 1)
def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
 (Nat.rec (motive:=fun _=>Nat → Bool) (fun _=>true)
 (fun _ next i=>check i&&next (i+1)) count) start
theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check=true) (lo : start ≤ i) (hi : i < start+count) :
    check i=true:=by
  induction count generalizing start with
  | zero=>omega
  | succ count ih =>
    change (check start&&treeBlock (start+1) count check)=true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here,rest⟩
    by_cases eq : i=start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)
theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check=true)
    (b : treeBlock (start+left) right check=true) :
    treeBlock start (left+right) check=true:=by
  induction left generalizing start with
  | zero=>simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start&&treeBlock (start+1) (left+right) check)=true
    change (check start&&treeBlock (start+1) left check)=true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here,rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here,ih rest (by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using b)⟩
abbrev Word:=Nat
def rootWords (base : List Word) (token : Nat) : List Word :=
  List.rec (motive:=fun _=>Nat → List Word) (fun _=>[])
    (fun word _ next bits =>
      let tail:=next (bits>>>1)
      if bits&&&1==0 then tail else word :: tail) base token
def insertWord (w : Word) (ws : List Word) : List Word :=
 List.rec [w] (fun a tail next=>if w ≤ a then w :: a :: tail else a :: next) ws
def gateToken (a b op keep : Nat) : Nat:=((a*64+b)*3+op)*4+keep
def stockWord (mask : Nat) (stock : List Word) (needed : List Word) (word : Word) : List Word :=
  let v:=word&&&mask
  if v==0||v==mask||stock.contains v||needed.contains v then needed
  else v :: needed
def recipeStart (mask : Nat) (stock words : List Word) : List Word :=
 (List.rec (motive:=fun _=>List Word → List Word) id
 (fun word _ next seen=>next (stockWord mask stock seen word)) words) []
def recipeClosure (mask : Nat) (stock : List Word) (history : List (Word × Word × Word))
 (start : List Word) : List Word :=
 List.rec (motive:=fun _=>List Word → List Word) id
 (fun (out,a,b) _ next seen =>
 next (if seen.contains (out&&&mask) then stockWord mask stock (stockWord mask stock seen a) b else seen))
 history start
def maskFlat (mask word : Nat) : Bool :=
  let v:=word&&&mask
  v==0||v==mask
def flatCount (mask : Nat) (words : List Word) : Nat :=
 List.rec 0 (fun word _ count=>if maskFlat mask word then count+1 else count) words
def availableB (mask : Nat) (bank : List Word) (w : Word) : Bool :=
  w==0||w==mask||bank.contains w
def AvailableWord (mask : Nat) (bank : List Word) (word : Word) : Prop :=
 word=0 ∨ word=mask ∨ word ∈ bank
def GateWord (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  (∃ a,AvailableWord mask bank a ∧ out=mask^^^a) ∨
  (∃ a b,AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out=a&&&b ∨ out=a|||b))
theorem projectGate {mask cut : Nat} (submask : mask&&&cut=cut)
    {roots : List Word} {out : Word} (gate : GateWord mask roots out) :
    GateWord cut (roots.map (· &&& cut)) (out&&&cut):=by
  have av {word : Word} (ha : AvailableWord mask roots word) :
      AvailableWord cut (roots.map (· &&& cut)) (word&&&cut):=by
    rcases ha with rfl | rfl | hm
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl submask)
    · exact Or.inr (Or.inr (List.mem_map_of_mem hm))
  rcases gate with ⟨a,ha,rfl⟩ | ⟨a,b,ha,hb,eq | eq⟩
  · refine Or.inl ⟨a&&&cut,av ha, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    have cutAt:=congrArg (fun n : Nat=>n.testBit i) submask
    simp only [Nat.testBit_and,Nat.testBit_xor] at cutAt ⊢
    cases h : cut.testBit i
    · simp
    · simp [h] at cutAt
      simp [cutAt]
  · subst out
    refine Or.inr ⟨a&&&cut,b&&&cut,av ha,av hb,Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases cut.testBit i <;> simp
  · subst out
    refine Or.inr ⟨a&&&cut,b&&&cut,av ha,av hb,Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and,Nat.testBit_or]
    cases cut.testBit i <;> simp
def AgreesAt (i j : Nat) (word : Word) : Prop :=
 word.testBit i=word.testBit j
def properWord (mask word : Word) : Prop:=word ≠ 0 ∧ word ≠ mask
def binWord (isOr : Bool) (a b : Word) : Word :=
  if isOr then a|||b else a&&&b
theorem binWord_comm (d : Bool) (a b : Word) : binWord d a b=binWord d b a:=by
  cases d <;> simp [binWord,Nat.land_comm,Nat.lor_comm]
variable {mask : Nat} {target : Word}
def LiveWord (mask : Nat) (target : Word) : Nat → Nat → Finset (Word) → Prop
  | 0,t,S=>t=0 ∧ S={target} ∧ properWord mask target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset (Word)) (a : Word),t=u+1 ∧ S=insert a U ∧ properWord mask a ∧
      (mask^^^a) ∉ insert a U ∧ LiveWord mask target k u (insert ((mask^^^a)) U)) ∨
    (∃ (U : Finset (Word)) (a b : Word) (d : Bool),S=insert a (insert b U) ∧ properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      binWord d a b ∉ insert a (insert b U) ∧ LiveWord mask target k t (insert (binWord d a b) U))
theorem LiveWord.stop {target : Word} (hp : properWord mask target) : LiveWord mask target 0 0 {target}:=⟨rfl,rfl,hp⟩
theorem LiveWord.unary {target : Word} {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
    (hfresh : (mask^^^a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask^^^a)) U)) :
    LiveWord mask target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem LiveWord.binary {target : Word} {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
    (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)) :
    LiveWord mask target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem LiveWord.ind {target : Word} {motive : ∀ (k t : Nat) (S : Finset (Word)),LiveWord mask target k t S → Prop}
    (stop : ∀ (hp : properWord mask target),motive 0 0 {target} (LiveWord.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
      (hfresh : (mask^^^a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask^^^a)) U)),
      motive k t (insert ((mask^^^a)) U) tail → motive (k+1) (t+1) (insert a U) (LiveWord.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
      (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)),
      motive k t (insert (binWord d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (LiveWord.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset (Word)} (h : LiveWord mask target k t S) : motive k t S h:=by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩:=h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)
theorem liveWordProper {k t S} (h : LiveWord mask target k t S) : ∀ a ∈ S,properWord mask a:=by
  induction h using LiveWord.ind with
  | stop hp=>simpa using hp
  | unary ha hf _ ih=>simpa using And.intro ha (fun a h=>ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h=>ih a (Finset.mem_insert_of_mem h)⟩
theorem liveWordSize {k t S} (h : LiveWord mask target k t S) : t ≤ k ∧ S.card+t ≤ k+1:=by
  induction h using LiveWord.ind with
  | stop hp=>simp
  | @unary k t U a ha hf _ ih =>
    have hu : (mask^^^a) ∉ U:=fun hm=>hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc:=Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : binWord d a b ∉ U:=fun hm=>hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1:=Finset.card_insert_le (a:=a) (s:=insert b U)
    have h2:=Finset.card_insert_le (a:=b) (s:=U)
    exact ⟨by omega,by omega⟩
def wordRep (mask : Nat) (ws : List Word) (w : Word) : Prop :=
 w ∈ ws ∨ ¬properWord mask w
def Masked (mask word : Nat) : Prop:=word&&&mask=word
theorem maskedAvailable {bank : List Word} {word : Word}
    (all : ∀ w ∈ bank,Masked mask w) (aw : AvailableWord mask bank word) :
    Masked mask word:=by
  rcases aw with rfl | rfl | hw
  · simp [Masked]
  · simp [Masked]
  · exact all _ hw
theorem maskedGate {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank,Masked mask w) (g : GateWord mask bank out) :
    Masked mask out:=by
  rcases g with ⟨a,ha,rfl⟩ | ⟨a,b,ha,hb,ea | ea⟩
  · have h:=projectGate (mask:=mask) (cut:=mask) (by simp)
      (roots:=bank) (out:=mask^^^a) (Or.inl ⟨a,ha,rfl⟩)
    have ma:=maskedAvailable all ha
    unfold Masked at ma ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bit:=congrArg (fun n : Nat=>n.testBit i) ma
    simp only [Nat.testBit_and,Nat.testBit_xor] at bit ⊢
    cases hm : mask.testBit i <;> simp_all
  · subst out
    have ma:=maskedAvailable all ha
    have mb:=maskedAvailable all hb
    simp only [Masked] at ma mb ⊢
    rw [Nat.land_assoc,mb]
  · subst out
    have ma:=maskedAvailable all ha
    have mb:=maskedAvailable all hb
    unfold Masked at ma mb ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bitA:=congrArg (fun n : Nat=>n.testBit i) ma
    have bitB:=congrArg (fun n : Nat=>n.testBit i) mb
    simp only [Nat.testBit_and,Nat.testBit_or] at bitA bitB ⊢
    cases hm : mask.testBit i <;> simp_all
def binaryWitness (mask : Nat) (bank : List Word) (out : Word) : Prop :=
 ∃ d a b,a ∈ bank ∧ b ∈ bank ∧ properWord mask a ∧ properWord mask b ∧
 a ≠ b ∧ out=binWord d a b
theorem classifyBinary {bank : List Word}
    (all : ∀ w ∈ bank,Masked mask w) (d : Bool) {a b : Word}
    (ha : AvailableWord mask bank a) (hb : AvailableWord mask bank b) :
    wordRep mask bank (binWord d a b) ∨ binaryWitness mask bank (binWord d a b):=by
  have c0 : wordRep mask bank 0:=Or.inr fun h=>h.1 rfl
  have cm : wordRep mask bank mask:=Or.inr fun h=>h.2 rfl
  have classify {w : Word} (hw : AvailableWord mask bank w) :
      w=0 ∨ w=mask ∨ w ∈ bank ∧ properWord mask w:=by
    by_cases zh : w=0
    · exact Or.inl zh
    by_cases mh : w=mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh,zh,mh⟩)
  have ma : a&&&mask=a:=maskedAvailable all ha
  have mb : b&&&mask=b:=maskedAvailable all hb
  have absorbA : a|||mask=mask:=by
    apply Nat.eq_of_testBit_eq
    intro i
    have h:=congrArg (fun n : Nat=>n.testBit i) ma
    simp only [Nat.testBit_and,Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  have absorbB : b|||mask=mask:=by
    apply Nat.eq_of_testBit_eq
    intro i
    have h:=congrArg (fun n : Nat=>n.testBit i) mb
    simp only [Nat.testBit_and,Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  rcases classify ha with rfl | hma | ⟨ha',pa⟩
  · rw [binWord_comm]
    cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord,hz] using c0)
      · exact Or.inl (by simpa [binWord,hm] using cm)
      · exact Or.inl (by simpa [binWord,wordRep] using
          (Or.inl hv : wordRep mask bank b))
  · rw [hma,binWord_comm]
    cases d
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord,hz] using c0)
      · exact Or.inl (by simpa [binWord,hm] using cm)
      · exact Or.inl (by simpa [binWord,mb,wordRep] using
          (Or.inl hv : wordRep mask bank b))
    · exact Or.inl (by simpa [binWord,absorbB] using cm)
  rcases classify hb with rfl | hmb | ⟨hb',pb⟩
  · cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · exact Or.inl (by simpa [binWord,wordRep] using
        (Or.inl ha' : wordRep mask bank a))
  · rw [hmb]
    cases d
    · exact Or.inl (by simpa [binWord,ma,wordRep] using
        (Or.inl ha' : wordRep mask bank a))
    · exact Or.inl (by simpa [binWord,absorbA] using cm)
  by_cases eq : a=b
  · subst b
    cases d <;> exact Or.inl (by simpa [binWord,wordRep] using
      (Or.inl ha' : wordRep mask bank a))
  exact Or.inr ⟨d,a,b,ha',hb',pa,pb,eq,rfl⟩
theorem insertWordMem {x w : Word} {ws : List Word} :
    x ∈ insertWord w ws ↔ x=w ∨ x ∈ ws:=by
  induction ws with
  | nil=>simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih,or_assoc,or_left_comm]
theorem insertWordNodup {w : Word} {ws : List Word} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup:=by
  induction ws with
  | nil=>simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh,nd⟩
    have hn:=List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail:=by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem,hnot.1.symm,hn.1],ih hn.2 hnot.2⟩
theorem insertWordSet (w : Word) (ws : List Word) :
    (insertWord w ws).toFinset=insert w ws.toFinset:=by
  ext x
  simp [insertWordMem]
theorem eraseWordSet {ws : List Word} (nd : ws.Nodup) (w : Word) :
    (ws.erase w).toFinset=ws.toFinset.erase w:=by
  ext x
  simp [nd.mem_erase_iff,and_comm]
theorem gateTokenFields {a b op keep : Nat} (hb : b < 64) (ho : op < 3) (hk : keep < 4) :
    gateToken a b op keep % 4=keep ∧
    gateToken a b op keep / 4 % 3=op ∧
    gateToken a b op keep / (4*3*64)=a ∧
    gateToken a b op keep / (4*3) % 64=b:=by
  unfold gateToken
  omega
def keepWord (save : Bool) (w : Word) (ws : List Word) : List Word :=
 if save then ws else ws.erase w
theorem keepNodup {ws : List Word} (nd : ws.Nodup) (save : Bool) (w : Word) :
    (keepWord save w ws).Nodup:=by
  cases save
  · exact nd.erase _
  · exact nd
theorem keepSubset (save : Bool) (w : Word) (ws : List Word) :
    ∀ v ∈ keepWord save w ws,v ∈ ws:=by
  cases save
  · exact fun _ h=>List.mem_of_mem_erase h
  · exact fun _ h=>h
theorem keepSet {ws : List Word} (nd : ws.Nodup) {w : Word} {U : Finset Word}
    (eq : ws.toFinset=insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset=U:=by
  by_cases hw : w ∈ U
  · simp [keepWord,hw,eq,Finset.insert_eq_of_mem hw]
  · simp [keepWord,hw,eraseWordSet nd,eq]
theorem keepPairSet {ws : List Word} (nd : ws.Nodup) {a b : Word} {U : Finset Word}
    (ab : a ≠ b) (eq : ws.toFinset=insert a (insert b U)) :
    (keepWord (decide (b ∈ U)) b (keepWord (decide (a ∈ U)) a ws)).toFinset=U:=by
  have x : decide (a ∈ insert b U)=decide (a ∈ U):=by simp [ab]
  have h:=keepSet nd eq
  rw [x] at h
  exact keepSet (keepNodup nd _ _) h
theorem getWord {ws : List Word} {x : Word} (h : x ∈ ws) :
    ws.getD (ws.idxOf x) 0=x:=by
  have inb:=List.idxOf_lt_length_iff.mpr h
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb
theorem rootWordSublist (base : List Word) (token : Nat) : (rootWords base token).Sublist base:=by
  induction base generalizing token with
  | nil=>exact List.Sublist.slnil
  | cons w ws ih =>
    change (if token&&&1==0 then rootWords ws (token>>>1)
      else w :: rootWords ws (token>>>1)).Sublist (w :: ws)
    split
    · exact (ih _).cons _
    · exact (ih _).cons₂ _
theorem rootToken (base : List Word) (S : Finset Word) :
    ∃ token < 2 ^ base.length,(rootWords base token).toFinset=base.toFinset ∩ S:=by
  induction base with
  | nil=>exact ⟨0,by simp,by simp [rootWords]⟩
  | cons w ws ih =>
    obtain ⟨token,htoken,ih⟩:=ih
    let bit : Nat:=if w ∈ S then 1 else 0
    have hbit : bit < 2:=by dsimp [bit];split <;> decide
    let code:=2*token+bit
    have low : code&&&1=bit:=by
      rw [show (1 : Nat)=2 ^ 1 - 1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
      dsimp [code]
      omega
    have high : code>>>1=token:=by
      rw [Nat.shiftRight_eq_div_pow]
      change code / 2=token
      dsimp [code]
      omega
    refine ⟨code, ?_, ?_⟩
    · simp only [List.length_cons,pow_succ]
      dsimp [code]
      omega
    · change (if code&&&1==0 then rootWords ws (code>>>1)
        else w :: rootWords ws (code>>>1)).toFinset=_
      rw [low,high]
      by_cases hw : w ∈ S
      · simp [bit,hw,ih]
      · simp [bit,hw,ih]
theorem liveAgrees {i j k t : Nat} {S : Finset Word}
    (h : LiveWord mask target k t S) (m : AgreesAt i j mask)
    (all : ∀ w ∈ S,AgreesAt i j w) : AgreesAt i j target:=by
  induction h using LiveWord.ind with
  | stop=>exact all _ (Finset.mem_singleton_self _)
  | @unary k t U a pa fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp only [AgreesAt,Nat.testBit_xor]
      rw [show mask.testBit i=mask.testBit j from m,
        show a.testBit i=a.testBit j from all a (Finset.mem_insert_self _ _)]
    · exact all _ (Finset.mem_insert_of_mem hw)
  | @binary k t U a b d pa pb ab fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have aa : a.testBit i=a.testBit j:=all a (Finset.mem_insert_self _ _)
      have bb : b.testBit i=b.testBit j:=all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      cases d <;> simp [AgreesAt,binWord,Nat.testBit_and,Nat.testBit_or,aa,bb]
    · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
theorem positiveInMask {i : Nat} (mt : Masked mask target) (ht : target.testBit i=true) :
    mask.testBit i=true:=by
  have h:=congrArg (fun n : Nat=>n.testBit i) mt
  simpa [Nat.testBit_and,ht] using h
variable {rows : Nat}
def fullMask (rows : Nat) : Nat:=2 ^ rows - 1
theorem toNatMasked (v : BitVec rows) : Masked (fullMask rows) v.toNat:=by
  unfold Masked fullMask
  rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt v.isLt]
theorem notNat (v : BitVec rows) : (~~~v).toNat=fullMask rows^^^v.toNat:=by
  rw [← BitVec.xor_allOnes,BitVec.toNat_xor,Nat.xor_comm,BitVec.toNat_allOnes]
  rfl
theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat:=by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none=>exact Or.inl rfl
  | some a=>exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))
theorem availableB_spec {mask : Nat} {bank : List Word} {v : Word} :
    availableB mask bank v=true ↔ AvailableWord mask bank v:=by
  simp [availableB,AvailableWord,or_assoc]
abbrev PointWire (rows : Nat):=Fin rows → Bool
def encodePoint (f : PointWire rows) : BitVec rows :=
 (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
theorem encodeBit (f : PointWire rows) (i : Fin rows) :
    (encodePoint f).getLsbD i.val=f i:=by
  simp only [encodePoint,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
theorem encodeAnd (a b : PointWire rows) :
    encodePoint (fun i=>a i&&b i)=encodePoint a&&&encodePoint b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and,encodeBit a ⟨i,hi⟩,encodeBit b ⟨i,hi⟩,encodeBit _ ⟨i,hi⟩]
theorem encodeOr (a b : PointWire rows) :
    encodePoint (fun i=>a i||b i)=encodePoint a|||encodePoint b:=by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or,encodeBit a ⟨i,hi⟩,encodeBit b ⟨i,hi⟩,encodeBit _ ⟨i,hi⟩]
def pointWord (f : PointWire rows) : Word:=(encodePoint f).toNat
def relabel (sourceIndex : Fin rows → Fin rows) (word : Word) : Word :=
 pointWord fun i=>word.testBit (sourceIndex i).val
theorem pointZero : pointWord (fun _ : Fin rows=>false)=0:=by
  have eq : encodePoint (fun _ : Fin rows=>false)=0:=by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i,hi⟩]
    simp
  simp [pointWord,eq]
theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0=0:=by
  simpa [relabel] using (pointZero (rows:=rows))
theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a&&&b)=relabel sourceIndex a&&&relabel sourceIndex b:=by
  simp only [relabel,Nat.testBit_and,pointWord,encodeAnd,BitVec.toNat_and]
theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a|||b)=relabel sourceIndex a|||relabel sourceIndex b:=by
  simp only [relabel,Nat.testBit_or,pointWord,encodeOr,BitVec.toNat_or]
theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a^^^b)=relabel sourceIndex a^^^relabel sourceIndex b:=by
  have eq : encodePoint (fun i=>(a^^^b).testBit (sourceIndex i).val) =
      encodePoint (fun i=>a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i=>b.testBit (sourceIndex i).val):=by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor,encodeBit _ ⟨i,hi⟩,encodeBit _ ⟨i,hi⟩,encodeBit _ ⟨i,hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel,pointWord,BitVec.toNat_xor] using congrArg BitVec.toNat eq
theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Word) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val=word.testBit (sourceIndex i).val :=
  encodeBit _ i
theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Word) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i=false:=by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)
theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Word} (ba : Masked (fullMask rows) a) (bb : Masked (fullMask rows) b)
    (eq : relabel sourceIndex a=relabel sourceIndex b) : a=b:=by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j,h⟩:=onto ⟨i,inside⟩
    have bit:=congrArg (fun w : Nat=>w.testBit j.val) eq
    simpa only [relabelBit,h] using bit
  · have ea:=congrArg (fun w : Nat=>w.testBit i) ba
    have eb:=congrArg (fun w : Nat=>w.testBit i) bb
    simp only [Nat.testBit_and,fullMask,Nat.testBit_two_pow_sub_one,inside,decide_false,
      Bool.and_false] at ea eb
    rw [← ea, ← eb]
def DagAuto (mask goal : Word) (select : Fin rows → Fin rows) : Prop :=
 Function.Surjective select ∧ relabel select mask=mask ∧ relabel select goal=goal
abbrev WordMoveStep:=List (Word × Nat) × List (Word × Nat)
abbrev WordMove:=List WordMoveStep
def mixStep (m : WordMoveStep) (w : Word) : Word :=
  let left:=List.rec 0 (fun (part,n) _ acc=>((w&&&part)<<<n)|||acc) m.1
  let right:=List.rec 0 (fun (part,n) _ acc=>((w&&&part)>>>n)|||acc) m.2
  left|||right
def BitLinear (f : Word → Word) : Prop :=
 ∀ w i,(f w).testBit i=true ↔ ∃ j,w.testBit j=true ∧ (f (2 ^ j)).testBit i=true
theorem bitLinearZero : BitLinear (fun _=>0):=by
  simp [BitLinear]
theorem bitLinearOr {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w=>f w|||g w):=by
  intro w i
  change ((f w|||g w).testBit i=true) ↔ _
  simp only [Nat.testBit_or,Bool.or_eq_true]
  rw [hf w i,hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩
theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w=>(w&&&mask)<<<n):=by
  intro w i
  simp only [Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_two_pow,
    Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨h,hw,hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩
theorem bitLinearRight (mask n : Nat) : BitLinear (fun w=>(w&&&mask)>>>n):=by
  intro w i
  simp only [Nat.testBit_shiftRight,Nat.testBit_and,Nat.testBit_two_pow,
    Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩
theorem mixStepLinear (move : WordMoveStep) : BitLinear (mixStep move):=by
  obtain ⟨left,right⟩:=move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil=>exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part,count⟩:=entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil=>exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part,count⟩:=entry
      exact bitLinearOr (bitLinearRight part count) ih
def mixMove (move : WordMove) (w : Word) : Word :=
 (List.rec (motive:=fun _=>Word → Word) id
 (fun step _ next w=>next (mixStep step w)) move) w
theorem bitLinearId : BitLinear id:=by
  intro w i
  change w.testBit i=true ↔ ∃ j,w.testBit j=true ∧ (2 ^ j).testBit i=true
  simp [Nat.testBit_two_pow]
theorem bitLinearComp {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w=>f (g w)):=by
  intro w i
  change (f (g w)).testBit i=true ↔ ∃ j,w.testBit j=true ∧ (f (g (2 ^ j))).testBit i=true
  rw [hf]
  constructor
  · rintro ⟨j,gj,fj⟩
    obtain ⟨k,wk,gk⟩:=(hg w j).mp gj
    exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
  · rintro ⟨j,wj,h⟩
    obtain ⟨k,gk,fk⟩:=(hf (g (2^j)) i).mp h
    exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩
theorem mixMoveLinear (move : WordMove) : BitLinear (mixMove move):=by
  induction move with
  | nil=>exact bitLinearId
  | cons op ops ih =>
    change BitLinear (fun w=>mixMove ops (mixStep op w))
    exact bitLinearComp ih (mixStepLinear op)
def permuteAxes (axes : List Nat) (offset row : Nat) : Nat :=
  offset^^^(List.rec (motive:=fun _=>Nat → Nat) (fun _=>0)
    (fun j _ next i=>(if row.testBit i then 1<<<j else 0)|||next (i+1)) axes) 0
theorem relabelLinear (select : Fin rows → Fin rows) : BitLinear (relabel select):=by
  intro w i
  by_cases inside : i < rows
  · let ii : Fin rows:=⟨i,inside⟩
    change (relabel select w).testBit ii.val=true ↔ _
    rw [relabelBit]
    constructor
    · intro h
      refine ⟨(select ii).val,h,?_⟩
      change (relabel select (2 ^ (select ii).val)).testBit ii.val=true
      rw [relabelBit,Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val=true at bit
      rw [relabelBit,Nat.testBit_two_pow,decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Word} {move : WordMove}
    (bounded : Masked (fullMask rows) mask)
    (basis : ∀ i : Fin rows,mask.testBit i.val=true →
      mixMove move (2 ^ i.val)=relabel select (2 ^ i.val))
    {w : Word} (masked : Masked mask w) : mixMove move w=relabel select w:=by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear,relabelLinear]
  have source {j : Nat} (bit : w.testBit j=true) :
      mixMove move (2^j)=relabel select (2^j):=by
    have m : mask.testBit j=true:=by
      have eq:=congrArg (fun x : Nat=>x.testBit j) masked
      simpa [Nat.testBit_and,bit] using eq
    have within : j < rows:=by
      have eq:=congrArg (fun x : Nat=>x.testBit j) bounded
      simpa [Nat.testBit_and,fullMask,Nat.testBit_two_pow_sub_one,m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩
theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i,inverse (select i)=i) :
    ∀ j : Fin rows,select (inverse j)=j →
      relabel select (2 ^ j.val)=2 ^ (inverse j).val:=by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows:=⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val=_
    rw [relabelBit,Nat.testBit_two_pow,Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j=select pos:=Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j=pos:=Fin.ext eq
      rw [← hp,right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside),Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i:=by have:=(inverse j).isLt;omega
    simp [ne]
theorem dagAutoFromMove {select inverse : Fin rows → Fin rows} {mask goal : Word} {move : WordMove}
    (left : ∀ i,inverse (select i)=i)
    (right : ∀ i,select (inverse i)=i)
    (bm : Masked (fullMask rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows,mask.testBit i.val=true →
      mixMove move (2 ^ i.val)=2 ^ (inverse i).val)
    (sameMask : mixMove move mask=mask) (sameGoal : mixMove move goal=goal) :
    DagAuto mask goal select ∧ ∀ w,Masked mask w → mixMove move w=relabel select w:=by
  have agree {w : Word} (hw : Masked mask w) : mixMove move w=relabel select w :=
    wordMoveAgreement bm (fun i h=>(basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i=>⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h=>agree h⟩
abbrev Witness:=Word × Nat × Nat
def witnessWord (w : Witness) : Word:=w.1
def essentialB (mask target : Word) (stock : List Word) (entry : Witness) : Bool :=
  let (w,p,n):=entry
  mask.testBit p&&mask.testBit n&&target.testBit p && !target.testBit n &&
    (w.testBit p != w.testBit n) &&
    stock.all (fun x=>x==w||x.testBit p==x.testBit n)
theorem essentialRequired {stock : List Word} {entry : Witness} {S : Finset Word} {k t : Nat}
    (ok : essentialB mask target stock entry=true)
    (sub : ∀ w ∈ S,w ∈ stock) (live : LiveWord mask target k t S) :
    witnessWord entry ∈ S:=by
  obtain ⟨w,p,n⟩:=entry
  simp only [essentialB,Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨mp,mn⟩,tp⟩,tn⟩,unequal⟩,rest⟩:=ok
  by_contra no
  have all : ∀ x ∈ S,AgreesAt p n x:=by
    intro x hx
    have h:=List.all_eq_true.mp rest x (sub x hx)
    have hw : x ≠ w:=fun e=>no (by simpa [witnessWord,e] using hx)
    simpa [hw,AgreesAt] using h
  have agree:=liveAgrees live (mp.trans mn.symm) all
  have falseBit : target.testBit n=false:=by simpa using tn
  simp [AgreesAt,tp,falseBit] at agree
theorem kw_step (goal : Word) (D D' : Finset Word) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D',x ≠ w → x ∈ D)
    (hf : ∀ e i,goal.testBit e=true → goal.testBit i=false →
      f e i ∈ D' ∧ (f e i).testBit e=true ∧ (f e i).testBit i=false)
    (hr : ∀ e i e' i',goal.testBit e=true → goal.testBit e'=true → goal.testBit i=false → goal.testBit i'=false → f e i=f e' i' → f e i'=f e i)
    (hcu : ∀ e i,w.testBit e=true → w.testBit i=false → c e i=true →
      u.testBit e=true ∧ u.testBit i=false)
    (hcv : ∀ e i,w.testBit e=true → w.testBit i=false → c e i=false →
      v.testBit e=true ∧ v.testBit i=false)
    (hc : ∀ e i e' i',c e i=c e' i' → c e i'=c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i,goal.testBit e=true → goal.testBit i=false →
        g e i ∈ D ∧ (g e i).testBit e=true ∧ (g e i).testBit i=false) ∧
      (∀ e i e' i',goal.testBit e=true → goal.testBit e'=true → goal.testBit i=false → goal.testBit i'=false → g e i=g e' i' → g e i'=g e i):=by
  have hg : ∀ e i,goal.testBit e=true → goal.testBit i=false → f e i=w →
      ((if f e i=w then (cond (c e i) u v) else f e i)=u ∧ c e i=true) ∨
      ((if f e i=w then (cond (c e i) u v) else f e i)=v ∧ c e i=false):=by
    intro e i _ _ h
    rw [ite_eq_left (h)]
    cases c e i
    · exact Or.inr ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
  refine ⟨fun e i=>if f e i=w then (cond (c e i) u v) else f e i, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1,h2,h3⟩:=hf e i he hi
    show (if f e i=w then (cond (c e i) u v) else f e i) ∈ D ∧
      (if f e i=w then (cond (c e i) u v) else f e i).testBit e=true ∧
      (if f e i=w then (cond (c e i) u v) else f e i).testBit i=false
    by_cases hw : f e i=w
    · rw [hw] at h2 h3
      rcases hg e i he hi hw with ⟨hx,hcc⟩ | ⟨hx,hcc⟩
      · rw [hx];exact ⟨hu,hcu e i h2 h3 hcc⟩
      · rw [hx];exact ⟨hv,hcv e i h2 h3 hcc⟩
    · rw [ite_eq_right (hw)];exact ⟨hsub _ h1 hw,h2,h3⟩
  · intro e i e' i' he he' hi hi' heq
    show (if f e i'=w then (cond (c e i') u v) else f e i') =
      (if f e i=w then (cond (c e i) u v) else f e i)
    have heq' : (if f e i=w then (cond (c e i) u v) else f e i) =
      (if f e' i'=w then (cond (c e' i') u v) else f e' i'):=heq
    by_cases h1 : f e i=w
    · by_cases h2 : f e' i'=w
      · have h3 : f e i'=w:=(hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
        have hcc : c e i=c e' i':=by
          rcases hg e i he hi h1 with ⟨hx,hx'⟩ | ⟨hx,hx'⟩ <;>
            rcases hg e' i' he' hi' h2 with ⟨hy,hy'⟩ | ⟨hy,hy'⟩
          · rw [hx',hy']
          · exact absurd (hx.symm.trans (heq'.trans hy)) huv
          · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
          · rw [hx',hy']
        rw [ite_eq_left (h3),ite_eq_left (h1),hc e i e' i' hcc]
      · exfalso
        rw [ite_eq_right (h2)] at heq'
        have hm:=(hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx,_⟩ | ⟨hx,_⟩
        · exact huD (by rw [← hx,heq'];exact hm)
        · exact hvD (by rw [← hx,heq'];exact hm)
    · by_cases h2 : f e' i'=w
      · exfalso
        rw [ite_eq_right (h1)] at heq'
        have hm:=(hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx,_⟩ | ⟨hx,_⟩
        · exact huD (by rw [← hx, ← heq'];exact hm)
        · exact hvD (by rw [← hx, ← heq'];exact hm)
      · have h1n : (if f e i=w then (cond (c e i) u v) else f e i)=f e i:=ite_eq_right h1
        have h2n : (if f e' i'=w then (cond (c e' i') u v) else f e' i')=f e' i':=ite_eq_right h2
        rw [h1n,h2n] at heq'
        have h3:=hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i'=w:=by rw [h3];exact h1
        rw [h1n,ite_eq_right (h3n)]
        exact h3
theorem and_cu (u v e i : ℕ) (h1 : (u&&&v).testBit e=true) (_h2 : (u&&&v).testBit i=false)
    (h3 : (!(u.testBit i))=true) : u.testBit e=true ∧ u.testBit i=false:=by
  rw [Nat.testBit_and] at h1
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem and_cv (u v e i : ℕ) (h1 : (u&&&v).testBit e=true) (h2 : (u&&&v).testBit i=false)
    (h3 : (!(u.testBit i))=false) : v.testBit e=true ∧ v.testBit i=false:=by
  rw [Nat.testBit_and] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem or_cu (u v e i : ℕ) (_h1 : (u|||v).testBit e=true) (h2 : (u|||v).testBit i=false)
    (h3 : u.testBit e=true) : u.testBit e=true ∧ u.testBit i=false:=by
  rw [Nat.testBit_or] at h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem or_cv (u v e i : ℕ) (h1 : (u|||v).testBit e=true) (h2 : (u|||v).testBit i=false)
    (h3 : u.testBit e=false) : v.testBit e=true ∧ v.testBit i=false:=by
  rw [Nat.testBit_or] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
def KWPartition (goal : Word) (ws : Finset Word) : Prop :=
 ∃ f : Nat → Nat → Word,
 (∀ e i,goal.testBit e=true → goal.testBit i=false →
 f e i ∈ ws ∧ (f e i).testBit e=true ∧ (f e i).testBit i=false) ∧
 (∀ e i e' i',goal.testBit e=true → goal.testBit e'=true →
 goal.testBit i=false → goal.testBit i'=false → f e i=f e' i' → f e i'=f e i)
theorem kwFromLive {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) (tight : S.card=k+1) : KWPartition goal S:=by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,eq,_⟩:=live
    subst S
    exact ⟨fun _ _=>goal,fun _ _ hp hn=>⟨by simp,hp,hn⟩,fun _ _ _ _ _ _ _ _ _=>rfl⟩
  | succ k ih =>
    rcases live with ⟨u,U,a,eq,_⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,fresh,tail⟩
    · omega
    let w:=binWord op a b
    have wU : w ∉ U:=fun h=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have wA : w ≠ a:=fun eq=>fresh (Finset.mem_insert.mpr (Or.inl eq))
    have wB : w ≠ b:=fun eq=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl eq)))
    have tailSize:=(liveWordSize tail).2
    change (insert w U).card+0 ≤ k+1 at tailSize
    rw [Finset.card_insert_of_notMem wU] at tailSize
    have paCard:=Finset.card_insert_le a (insert b U)
    have pbCard:=Finset.card_insert_le b U
    have aU : a ∉ U:=by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at tight
      omega
    have bU : b ∉ U:=by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      have:=Finset.card_insert_le a U
      omega
    obtain ⟨f,hf,hr⟩:=ih tail (by
      change (insert w U).card=k+1
      rw [Finset.card_insert_of_notMem wU]
      omega)
    have keepA : a ∉ insert w U:=by simp [wA.symm,aU]
    have keepB : b ∉ insert w U:=by simp [wB.symm,bU]
    have other : ∀ x ∈ insert w U,x ≠ w → x ∈ insert a (insert b U):=by
      intro x hx hn
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left hn))
    have ha : a ∈ insert a (insert b U):=Finset.mem_insert_self ..
    have hb : b ∈ insert a (insert b U):=Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    cases op
    · exact kw_step goal _ _ a b w (fun _ i => !(a.testBit i)) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3=>and_cu a b e i h1 h2 h3) (fun e i h1 h2 h3=>and_cv a b e i h1 h2 h3)
        (fun _ _ _ _ h=>h.symm)
    · exact kw_step goal _ _ a b w (fun e _=>a.testBit e) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3=>or_cu a b e i h1 h2 h3) (fun e i h1 h2 h3=>or_cv a b e i h1 h2 h3)
        (fun _ _ _ _ _=>rfl)
theorem liveDirected {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) {p n : Nat}
    (hp : goal.testBit p=true) (hn : goal.testBit n=false) :
    ∃ w ∈ S,w.testBit p=true ∧ w.testBit n=false:=by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,rfl,_⟩:=live
    exact ⟨goal,by simp,hp,hn⟩
  | succ k ih =>
    rcases live with ⟨u,U,a,ueq,_⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,fresh,tail⟩
    · omega
    obtain ⟨w,hw,wp,wn⟩:=ih tail
    rcases Finset.mem_insert.mp hw with eq | hU
    · subst w
      cases op
      · by_cases ha : a.testBit n=false
        · exact ⟨a,Finset.mem_insert_self ..,and_cu a b p n wp wn (by simp [ha])⟩
        · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            and_cv a b p n wp wn (by cases h : a.testBit n <;> simp_all)⟩
      · by_cases ha : a.testBit p=true
        · exact ⟨a,Finset.mem_insert_self ..,or_cu a b p n wp wn ha⟩
        · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            or_cv a b p n wp wn (by cases h : a.testBit p <;> simp_all)⟩
    · exact ⟨w,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),wp,wn⟩
namespace PackedRect
def domN (w d : ℕ) : Bool :=
 Nat.beq (Nat.land (Nat.land w 4095) (Nat.sub 16777215 d)) 0 &&
 Nat.beq (Nat.land (Nat.land d (Nat.sub 16777215 w)) 16773120) 0
def blk (m : Bool) (w d : ℕ) : Bool:=cond m (domN w d) (Nat.beq w d)
theorem land_compl (w : ℕ) : w&&&(16777215 - w)=0:=by
  rcases lt_or_ge w (2 ^ 24) with h | h
  · apply Nat.eq_of_testBit_eq
    intro i
    have e : 16777215 - w=2 ^ 24 - (w+1):=by omega
    rw [e,Nat.testBit_and,Nat.testBit_two_pow_sub_succ h]
    cases w.testBit i <;> simp
  · have e : 16777215 - w=0:=by omega
    simp [e]
theorem domN_refl (w : ℕ) : domN w w=true:=by
  have h:=land_compl w
  have h1 : Nat.land (Nat.land w 4095) (Nat.sub 16777215 w)=0:=by
    show (w&&&4095)&&&(16777215 - w)=0
    rw [Nat.and_right_comm,h];simp
  have h2 : Nat.land (Nat.land w (Nat.sub 16777215 w)) 16773120=0:=by
    show (w&&&(16777215 - w))&&&16773120=0
    rw [h];simp
  unfold domN
  rw [h1,h2]
  rfl
theorem blk_refl (m : Bool) (w : ℕ) : blk m w w=true:=by
  cases m
  · simp [blk]
  · simp [blk,domN_refl]
def Reach (m : Bool) : Finset Word → Nat → Prop
  | D,0=>D={4095}
  | D,k+1=>D={4095} ∨ ∃ (u v w : Word) (ka kb : Bool),
    u ∈ D ∧ v ∈ D ∧ (w=u&&&v ∨ w=u|||v) ∧
    (∀ d ∈ D,blk m w d=false) ∧ True ∧
    Reach m (insert w (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)))) k
theorem Reach.ind {m : Bool} {P : ∀ D k,Reach m D k → Prop}
    (done : ∀ k,P {4095} k (by cases k <;> first | rfl | exact Or.inl rfl))
    (step : ∀ D k u v w (ka kb : Bool) (hu : u ∈ D) (hv : v ∈ D)
      (hw : w=u&&&v ∨ w=u|||v) (hd : ∀ d ∈ D,blk m w d=false),True →
      (tail : Reach m (insert w (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)))) k) →
      P (insert w (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)))) k tail →
      P D (k+1) (Or.inr ⟨u,v,w,ka,kb,hu,hv,hw,hd,trivial,tail⟩))
    {D k} (h : Reach m D k) : P D k h:=by
  induction k generalizing D with
  | zero =>
    change D={4095} at h
    subst D
    exact done 0
  | succ k ih =>
    rcases h with he | ⟨u,v,w,ka,kb,hu,hv,gate,hd,hb,tail⟩
    · subst D
      exact done (k+1)
    · exact step D k u v w ka kb hu hv gate hd hb tail (ih tail)
theorem Reach.card {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) : D.card ≤ k+1:=by
  induction h using Reach.ind with
  | done k=>simp
  | step D k u v w ka kb hu hv hw hd hb _ ih =>
    have hwD : w ∉ D:=fun hm=>by
      have:=hd w hm
      rw [blk_refl] at this
      exact Bool.noConfusion this
    have hwF : w ∉ D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)) :=
      fun hm=>hwD (Finset.mem_of_mem_filter _ hm)
    rw [Finset.card_insert_of_notMem hwF] at ih
    have hsub : D ⊆ insert u (insert v
        (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)))):=by
      intro x hx
      by_cases h1 : x=u
      · simp [h1]
      by_cases h2 : x=v
      · simp [h2]
      simp [hx,h1,h2]
    have h2:=Finset.card_le_card hsub
    have h3:=Finset.card_insert_le u (insert v
        (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))))
    have h4:=Finset.card_insert_le v
        (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)))
    omega
theorem tb4095 (i : ℕ) : (4095 : ℕ).testBit i=decide (i < 12):=by
  have e : (4095 : ℕ)=2 ^ 12 - 1:=by norm_num
  rw [e,Nat.testBit_two_pow_sub_one]
theorem Reach.sep {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) (e i : ℕ) (he : e < 12)
    (hi : 12 ≤ i) : ∃ w ∈ D,w.testBit e=true ∧ w.testBit i=false:=by
  induction h using Reach.ind with
  | done k =>
    refine ⟨4095,by simp, ?_, ?_⟩
    · rw [tb4095];simpa using he
    · rw [tb4095];simpa using hi
  | step D k u v w ka kb hu hv hw hd hb _ ih =>
    obtain ⟨x,hx,h1,h2⟩:=ih
    rcases Finset.mem_insert.mp hx with hxw | hx
    · subst hxw
      rcases hw with hw | hw
      · subst hw
        rw [Nat.testBit_and] at h1 h2
        cases hum : u.testBit i
        · exact ⟨u,hu,by simp_all,hum⟩
        · exact ⟨v,hv,by simp_all,by simp_all⟩
      · subst hw
        rw [Nat.testBit_or] at h1 h2
        cases hue : u.testBit e
        · exact ⟨v,hv,by simp_all,by simp_all⟩
        · exact ⟨u,hu,hue,by simp_all⟩
    · exact ⟨x,Finset.mem_of_mem_filter _ hx,h1,h2⟩
def tb (w e : ℕ) : Bool := !(Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)
theorem tb_eq (w e : ℕ) : tb w e=w.testBit e:=by
  have h : Nat.land (Nat.shiftRight w e) 1=1&&&(w>>>e):=Nat.and_comm _ _
  unfold tb Nat.testBit
  rw [h]
  generalize (1&&&w>>>e)=X
  cases X <;> rfl
def rect (x J : ℕ) : ℕ → ℕ
  | 0=>0
  | e+1=>Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)
def rectW (x : ℕ) : ℕ := rect x (Nat.xor (Nat.shiftRight x 12) 4095) 12
theorem rect_tb (x J i : ℕ) (hJ : J.testBit i=true) : ∀ n e : ℕ,e < n → x.testBit e=true →
    (rect x J n).testBit (12*e+i)=true:=by
  intro n
  induction n with
  | zero=>intro e he;omega
  | succ n ih =>
    intro e he hx
    show ((cond (tb x n) (J<<<(12*n)) 0)|||rect x J n).testBit (12*e+i)=true
    rw [Nat.testBit_or]
    by_cases hen : e=n
    · subst hen
      rw [tb_eq,hx]
      simp [Nat.testBit_shiftLeft,hJ]
    · rw [ih e (by omega) hx]
      simp
theorem rectW_tb (x e i : ℕ) (he : e < 12) (hi : i < 12) (h1 : x.testBit e=true)
    (h2 : x.testBit (12+i)=false) : (rectW x).testBit (12*e+i)=true:=by
  apply rect_tb _ _ _ _ 12 e he h1
  show ((x>>>12)^^^4095).testBit i=true
  rw [Nat.testBit_xor,Nat.testBit_shiftRight,h2,tb4095]
  simp [hi]
theorem sep_bit {m : Bool} {D : Finset ℕ} {k : ℕ} (hR : Reach m D k) (p : ℕ) (hp : p < 144) :
    ∃ x ∈ D,(rectW x).testBit p=true:=by
  obtain ⟨x,hx,h1,h2⟩:=hR.sep (p / 12) (12+p % 12) (by omega) (by omega)
  refine ⟨x,hx, ?_⟩
  have:=rectW_tb x (p / 12) (p % 12) (by omega) (Nat.mod_lt _ (by norm_num)) h1 h2
  rwa [Nat.div_add_mod] at this
def full : ℕ := 22300745198530623141535718272648361505980415
theorem full_eq : full=2 ^ 144 - 1:=by norm_num [full]
def bor (a b : Bool) : Bool := @Bool.rec (fun _=>Bool) b true a
def band (a b : Bool) : Bool := @Bool.rec (fun _=>Bool) false b a
def bnot (a : Bool) : Bool := @Bool.rec (fun _=>Bool) true false a
theorem band_eq (a b : Bool) : band a b=(a&&b):=by cases a <;> rfl
theorem bnot_eq (a : Bool) : bnot a = !a:=by cases a <;> rfl
def tb' (w e : ℕ) : Bool:=bnot (Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)
theorem tb'_eq (w e : ℕ) : tb' w e=tb w e:=by
  unfold tb' tb;rw [bnot_eq]
def rect' (x J n : ℕ) : ℕ :=
 @Nat.rec (fun _ => ℕ) 0
 (fun e ih=>Nat.lor (@Bool.rec (fun _ => ℕ) 0 (Nat.shiftLeft J (Nat.mul 12 e)) (tb' x e)) ih) n
theorem rect'_eq (x J n : ℕ) : rect' x J n=rect x J n:=by
  induction n with
  | zero=>rfl
  | succ e ih =>
    show Nat.lor (@Bool.rec (fun _ => ℕ) 0 (Nat.shiftLeft J (Nat.mul 12 e)) (tb' x e)) (rect' x J e) =
      Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)
    rw [ih,tb'_eq]
    cases tb x e <;> rfl
theorem rectTest (x J n q : Nat) (bounded : J < 4096) :
    (rect x J n).testBit q =
      (decide (q / 12 < n)&&x.testBit (q / 12)&&J.testBit (q % 12)):=by
  induction n with
  | zero=>simp [rect]
  | succ n ih =>
    change ((cond (tb x n) (J<<<(12*n)) 0)|||rect x J n).testBit q=_
    rw [Nat.testBit_or,ih,tb_eq]
    by_cases before : q / 12 < n
    · have start : ¬ 12*n ≤ q:=by omega
      have next : q/12 < n+1:=by omega
      cases x.testBit n <;> simp [Nat.testBit_shiftLeft,start,before,next]
    by_cases lane : q / 12=n
    · have start : 12*n ≤ q:=by omega
      have off : q-12*n=q % 12:=by omega
      have next : q/12 < n+1:=by omega
      cases enabled : x.testBit n <;> simp [Nat.testBit_shiftLeft,start,off,before,next,lane,enabled]
    · have next : ¬ q/12 < n+1:=by omega
      have off : 12 ≤ q-12*n:=by omega
      have beyond : J.testBit (q-12*n)=false:=by
        apply Nat.testBit_lt_two_pow
        exact lt_of_lt_of_le bounded (Nat.pow_le_pow_right (by decide : 0 < 2) off)
      cases x.testBit n <;> simp [Nat.testBit_shiftLeft,before,next,beyond]
def rectScan (p : Nat → Bool) : Nat → Nat → Bool :=
 Nat.rec p (fun k prev s=>prev s&&prev (s+2^k))
theorem rectScanAt {p : Nat → Bool} {k s i : Nat}
    (h : rectScan p k s=true) (lo : s ≤ i) (hi : i < s+2^k) : p i=true:=by
  induction k generalizing s with
  | zero =>
    have eq : i=s:=by omega
    simpa [eq,rectScan] using h
  | succ k ih =>
    obtain ⟨left,right⟩:=Bool.and_eq_true_iff.mp h
    by_cases half : i < s+2^k
    · exact ih left lo half
    · apply ih right (by omega)
      rw [Nat.pow_succ] at hi
      omega
def rectRowMask (p : Nat) : Nat :=
  let table:=0xfffffffffffffffffffff000ffffff000fffffffff000000fff000fffffffff000fff000fff000000ffffff000000000000fffffffff000ffffff000000fff000fff000fff000000000000ffffff000000fff000000000000fff000000000000
  (unpack table 48 (p&&&15)) |||
    ((unpack table 48 ((p>>>4)&&&15))<<<48) |||
    ((unpack table 48 ((p>>>8)&&&15))<<<96)
def rectRepeat (J : Nat) : Nat:=J*0x1001001001001001001001001001001001
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rectArithmeticCheck :
    rectScan (fun v=>Nat.beq (rectRowMask v) (rect' v 4095 12) &&
      Nat.beq (rectRepeat v) (rect' 4095 v 12)) 12 0=true:=by
  decide +kernel
theorem rectArithmeticAt {i : Nat} (h : i < 4096) :
    rectRowMask i=rect i 4095 12 ∧ rectRepeat i=rect 4095 i 12:=by
  have line:=rectScanAt rectArithmeticCheck (i:=i) (Nat.zero_le _) (by simpa using h)
  obtain ⟨a,b⟩:=Bool.and_eq_true_iff.mp line
  exact ⟨(Nat.beq_eq.mp a).trans (rect'_eq ..),(Nat.beq_eq.mp b).trans (rect'_eq ..)⟩
def rectW' (x : Nat) : Nat :=
  let J:=(x>>>12)^^^4095
  if Nat.blt J 4096 then rectRowMask (x % 4096)&&&rectRepeat J
  else rect' x J 12
theorem rectW'_eq (x : Nat) : rectW' x=rectW x:=by
  unfold rectW' rectW
  let J:=(x>>>12)^^^4095
  change (if Nat.blt J 4096 then rectRowMask (x % 4096)&&&rectRepeat J
    else rect' x J 12)=rect x J 12
  split
  · next good =>
    have small:=Nat.blt_eq.mp good
    have modSmall : x % 4096 < 4096:=Nat.mod_lt _ (by decide)
    rw [(rectArithmeticAt modSmall).1,(rectArithmeticAt small).2]
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.testBit_and,rectTest _ _ _ _ (by decide),rectTest _ _ _ _ small,
      rectTest _ _ _ _ small,tb4095,tb4095]
    change (_&&(x % 2^12).testBit (q/12)&&_&&_)=_
    rw [Nat.testBit_mod_two_pow]
    have modLt : q % 12 < 12:=Nat.mod_lt _ (by decide)
    simp only [modLt,decide_true,Bool.and_true]
    cases decide (q/12 < 12) <;> rfl
  · exact rect'_eq ..
theorem ite_p {c : Prop} [Decidable c] (a b : ℕ) (h : c) : (if c then a else b)=a:=by
  split
  · rfl
  · contradiction
theorem ite_n {c : Prop} [Decidable c] (a b : ℕ) (h : ¬ c) : (if c then a else b)=b:=by
  split
  · contradiction
  · rfl
theorem pw_forall {α : Type} {R : α → α → Prop} (hs : ∀ a b,R a b → R b a) :
    ∀ l : List α,l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l,a ≠ b → R a b:=by
  intro l
  induction l with
  | nil=>intro _ a ha;simp at ha
  | cons x l ih =>
    intro h a ha b hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · rw [ha'];exact h.1 b hb'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · rw [hb'];exact hs _ _ (h.1 a ha')
      · exact ih h.2 a ha' b hb' hab
theorem size_lb2 (D : Finset ℕ) (u v : ℕ) (ka kb : Bool) :
    D.card ≤ (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))).card +
      (cond ka 0 1+cond kb 0 1):=by
  have hsub : D ⊆ (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))) ∪
      ((cond ka ∅ {u}) ∪ (cond kb ∅ {v})):=by
    intro x hx
    by_cases h1 : x=u <;> by_cases h2 : x=v <;> cases ka <;> cases kb <;> simp_all
  have h1:=Finset.card_le_card hsub
  have h2:=Finset.card_union_le (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)))
    ((cond ka ∅ {u}) ∪ (cond kb ∅ {v}))
  have h3:=Finset.card_union_le (cond ka (∅ : Finset ℕ) {u}) (cond kb ∅ {v})
  have h4 : (cond ka (∅ : Finset ℕ) {u}).card=cond ka 0 1:=by cases ka <;> simp
  have h5 : (cond kb (∅ : Finset ℕ) {v}).card=cond kb 0 1:=by cases kb <;> simp
  omega
theorem and_cu (u v e i : ℕ) (h1 : (u&&&v).testBit e=true) (_h2 : (u&&&v).testBit i=false)
    (h3 : (!(u.testBit i))=true) : u.testBit e=true ∧ u.testBit i=false:=by
  rw [Nat.testBit_and] at h1
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem and_cv (u v e i : ℕ) (h1 : (u&&&v).testBit e=true) (h2 : (u&&&v).testBit i=false)
    (h3 : (!(u.testBit i))=false) : v.testBit e=true ∧ v.testBit i=false:=by
  rw [Nat.testBit_and] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem or_cu (u v e i : ℕ) (_h1 : (u|||v).testBit e=true) (h2 : (u|||v).testBit i=false)
    (h3 : u.testBit e=true) : u.testBit e=true ∧ u.testBit i=false:=by
  rw [Nat.testBit_or] at h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem or_cv (u v e i : ℕ) (h1 : (u|||v).testBit e=true) (h2 : (u|||v).testBit i=false)
    (h3 : u.testBit e=false) : v.testBit e=true ∧ v.testBit i=false:=by
  rw [Nat.testBit_or] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem tb_land (a b q : ℕ) : (Nat.land a b).testBit q=(a.testBit q&&b.testBit q) :=
  Nat.testBit_and a b q
theorem tb_lor (a b q : ℕ) : (Nat.lor a b).testBit q=(a.testBit q||b.testBit q) :=
  Nat.testBit_or a b q
theorem tb_xor (a b q : ℕ) : (Nat.xor a b).testBit q=Bool.xor (a.testBit q) (b.testBit q) :=
  Nat.testBit_xor a b q
theorem full_tb (q : ℕ) : full.testBit q=decide (q < 144):=by
  rw [full_eq,Nat.testBit_two_pow_sub_one]
theorem land_sub (h a : ℕ) (H : ∀ q,h.testBit q=true → a.testBit q=true) :
    Nat.land h a=h:=by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land]
  cases hh : h.testBit q
  · rfl
  · rw [H q hh];rfl
theorem land_disj (a h : ℕ) (H : ∀ q,a.testBit q=true → h.testBit q=true → False) :
    Nat.land a h=0:=by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land,Nat.zero_testBit]
  cases ha : a.testBit q
  · rfl
  · cases hh : h.testBit q
    · rfl
    · exact (H q ha hh).elim
def orS (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x s)
def orSL (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x s)
theorem orS_tb (x s q : ℕ) : (orS x s).testBit q=(x.testBit q||x.testBit (s+q)):=by
  show (x|||x>>>s).testBit q=_
  rw [Nat.testBit_or,Nat.testBit_shiftRight]
theorem orSL_tb (x s q : ℕ) :
    (orSL x s).testBit q=(x.testBit q||(decide (s ≤ q)&&x.testBit (q - s))):=by
  show (x|||x<<<s).testBit q=_
  simp only [Nat.testBit_or,Nat.testBit_shiftLeft,ge_iff_le]
theorem orS_ex (k p x n s : ℕ)
    (hx : ∀ q,x.testBit q=true → ∃ j,j < n ∧ p.testBit (k*j+q)=true) (q : ℕ)
    (h : (orS x (k*s)).testBit q=true) : ∃ j,j < n+s ∧ p.testBit (k*j+q)=true:=by
  rw [orS_tb,Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨j,hj,hp⟩:=hx q h
    exact ⟨j,by omega,hp⟩
  · obtain ⟨j,hj,hp⟩:=hx _ h
    refine ⟨j+s,by omega, ?_⟩
    rw [Nat.mul_add,Nat.add_assoc];exact hp
theorem orSL_ex (k p x n s : ℕ)
    (hx : ∀ q,x.testBit q=true → ∃ j,j < n ∧ k*j ≤ q ∧ p.testBit (q - k*j)=true)
    (q : ℕ) (h : (orSL x (k*s)).testBit q=true) :
    ∃ j,j < n+s ∧ k*j ≤ q ∧ p.testBit (q - k*j)=true:=by
  rw [orSL_tb,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with h | ⟨hs,h⟩
  · obtain ⟨j,hj,hq,hp⟩:=hx q h
    exact ⟨j,by omega,hq,hp⟩
  · obtain ⟨j,hj,hq,hp⟩:=hx _ h
    have e : q - k*(j+s)=q - k*s - k*j:=by rw [Nat.mul_add];omega
    refine ⟨j+s,by omega, ?_, ?_⟩
    · rw [Nat.mul_add];omega
    · rw [e];exact hp
def rowM : ℕ := 5445847423328601499764522166702896582657
theorem rowM_tb (q : ℕ) (h : rowM.testBit q=true) : q < 144 ∧ q % 12=0:=by
  have hlt : q < 144:=by
    by_contra hq
    have h0 : rowM.testBit q=false:=by
      apply Nat.testBit_lt_two_pow
      have h1 : rowM < 2 ^ 144:=by norm_num [rowM]
      have h2 : (2 : ℕ) ^ 144 ≤ 2 ^ q:=Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [h0] at h
    exact Bool.noConfusion h
  have hall : ∀ q : ℕ,q < 144 → rowM.testBit q=true → q % 12=0:=by decide +kernel
  exact ⟨hlt,hall q hlt h⟩
def rowsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 6) 3) 1) 1) rowM
def colsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 96) 48) 24) 12) 4095
def hullC (p : ℕ) : ℕ :=
 Nat.land (orSL (orSL (orSL (orSL (rowsOf p) 6) 3) 1) 1)
 (orSL (orSL (orSL (orSL (colsOf p) 96) 48) 24) 12)
def hull (p : ℕ) : ℕ := hullC (Nat.land p full)
theorem rowsOf_tb (p q : ℕ) (h : (rowsOf p).testBit q=true) :
    (q < 144 ∧ q % 12=0) ∧ ∃ j,j < 12 ∧ p.testBit (j+q)=true:=by
  unfold rowsOf at h
  rw [tb_land,Bool.and_eq_true] at h
  refine ⟨rowM_tb q h.2, ?_⟩
  have h0 : ∀ q,p.testBit q=true → ∃ j,j < 1 ∧ p.testBit (1*j+q)=true :=
    fun q hq=>⟨0,by norm_num,by simpa using hq⟩
  have h1:=orS_ex 1 p _ 1 6 h0
  have h2:=orS_ex 1 p _ _ 3 h1
  have h3:=orS_ex 1 p _ _ 1 h2
  have h4:=orS_ex 1 p _ _ 1 h3
  obtain ⟨j,hj,hp⟩:=h4 q h.1
  exact ⟨j,by omega,by simpa using hp⟩
theorem colsOf_tb (p q : ℕ) (h : (colsOf p).testBit q=true) :
    q < 12 ∧ ∃ j,j < 16 ∧ p.testBit (12*j+q)=true:=by
  unfold colsOf at h
  rw [tb_land,Bool.and_eq_true,tb4095,decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h0 : ∀ q,p.testBit q=true → ∃ j,j < 1 ∧ p.testBit (12*j+q)=true :=
    fun q hq=>⟨0,by norm_num,by simpa using hq⟩
  have h1:=orS_ex 12 p _ 1 8 h0
  have h2:=orS_ex 12 p _ _ 4 h1
  have h3:=orS_ex 12 p _ _ 2 h2
  have h4:=orS_ex 12 p _ _ 1 h3
  obtain ⟨j,hj,hp⟩:=h4 q h.1
  exact ⟨j,by omega,hp⟩
theorem hullC_spec (p : ℕ) (hp : ∀ q,p.testBit q=true → q < 144) (q : ℕ)
    (h : (hullC p).testBit q=true) :
    q < 144 ∧ ∃ i e',i < 12 ∧ e' < 12 ∧ p.testBit (12*(q / 12)+i)=true ∧
      p.testBit (12*e'+q % 12)=true:=by
  unfold hullC at h
  rw [tb_land,Bool.and_eq_true] at h
  obtain ⟨hR,hC⟩:=h
  have r0 : ∀ q,(rowsOf p).testBit q=true →
      ∃ j,j < 1 ∧ 1*j ≤ q ∧ (rowsOf p).testBit (q - 1*j)=true :=
    fun q hq=>⟨0,by norm_num,by omega,by simpa using hq⟩
  have r1:=orSL_ex 1 (rowsOf p) _ 1 6 r0
  have r2:=orSL_ex 1 (rowsOf p) _ _ 3 r1
  have r3:=orSL_ex 1 (rowsOf p) _ _ 1 r2
  have r4:=orSL_ex 1 (rowsOf p) _ _ 1 r3
  obtain ⟨j,hj,hjq,hr⟩:=r4 q hR
  obtain ⟨⟨hb,hm⟩,i,hi,hpi⟩:=rowsOf_tb p _ hr
  have c0 : ∀ q,(colsOf p).testBit q=true →
      ∃ j,j < 1 ∧ 12*j ≤ q ∧ (colsOf p).testBit (q - 12*j)=true :=
    fun q hq=>⟨0,by norm_num,by omega,by simpa using hq⟩
  have c1:=orSL_ex 12 (colsOf p) _ 1 8 c0
  have c2:=orSL_ex 12 (colsOf p) _ _ 4 c1
  have c3:=orSL_ex 12 (colsOf p) _ _ 2 c2
  have c4:=orSL_ex 12 (colsOf p) _ _ 1 c3
  obtain ⟨j',hj',hjq',hc⟩:=c4 q hC
  obtain ⟨hlt,e',he',hpe⟩:=colsOf_tb p _ hc
  have e1 : i+(q - 1*j)=12*(q / 12)+i:=by omega
  have e2 : q - 12*j'=q % 12:=by omega
  rw [e1] at hpi
  rw [e2] at hpe
  have hb':=hp _ hpe
  exact ⟨by omega,i,e',hi,by omega,hpi,hpe⟩
theorem hull_spec (p q : ℕ) (h : (hull p).testBit q=true) :
    q < 144 ∧ ∃ i e',i < 12 ∧ e' < 12 ∧ p.testBit (12*(q / 12)+i)=true ∧
      p.testBit (12*e'+q % 12)=true:=by
  have hp : ∀ q,(Nat.land p full).testBit q=true → q < 144:=by
    intro q hq
    rw [tb_land,full_tb,Bool.and_eq_true,decide_eq_true_eq] at hq
    exact hq.2
  obtain ⟨h1,i,e',hi,he,ha,hb⟩:=hullC_spec _ hp q h
  rw [tb_land,Bool.and_eq_true] at ha hb
  exact ⟨h1,i,e',hi,he,ha.1,hb.1⟩
def tw : List ℕ → ℕ → ℕ → ℕ
  | [],_,t=>t
  | a :: l,o,t=>tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))
def priv (t a : ℕ) : ℕ := hull (Nat.land a (Nat.xor t full))
def hullsOK (t : ℕ) : List ℕ → ℕ → Bool
  | [],_=>true
  | a :: l,acc=>Nat.beq (Nat.land (priv t a) a) (priv t a) &&
      (Nat.beq (Nat.land acc (priv t a)) 0&&hullsOK t l (Nat.lor acc (priv t a)))
def avOK1 (as : List ℕ) : Bool:=hullsOK (tw as 0 0) as 0
def rectOK1 (l : List ℕ) : Bool:=avOK1 (l.map rectW)
def IsRect (R : ℕ → Prop) : Prop :=
 ∀ e i e' i' : ℕ,e < 12 → i < 12 → e' < 12 → i' < 12 →
 R (12*e+i) → R (12*e'+i') → R (12*e+i')
def Part (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
 (∀ z ∈ zs,IsRect z.1) ∧
 (∀ z ∈ zs, ∀ q,z.1 q → q < 144) ∧
 (zs.Pairwise (fun z z' => ∀ q,z.1 q → z'.1 q → False)) ∧
 (∀ q,q < 144 → ∃ z ∈ zs,z.1 q) ∧
 (∀ z ∈ zs, ∀ q,z.1 q → z.2.testBit q=true)
theorem Part.rect {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs,IsRect z.1:=h.1
theorem Part.disj {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    zs.Pairwise (fun z z' => ∀ q,z.1 q → z'.1 q → False):=h.2.2.1
theorem Part.cov {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ q,q < 144 → ∃ z ∈ zs,z.1 q:=h.2.2.2.1
theorem Part.sub {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q,z.1 q → z.2.testBit q=true:=h.2.2.2.2
theorem tw_spec (q : ℕ) : ∀ (as : List ℕ) (o t : ℕ),(tw as o t).testBit q=false →
    t.testBit q=false ∧ (o.testBit q=true → ∀ a ∈ as,a.testBit q=false) ∧
    as.Pairwise (fun a b => ¬ (a.testBit q=true ∧ b.testBit q=true)):=by
  intro as
  induction as with
  | nil=>intro o t h;exact ⟨h,fun _ a ha=>by simp at ha,List.Pairwise.nil⟩
  | cons a l ih =>
    intro o t h
    obtain ⟨h1,h2,h3⟩:=ih (Nat.lor o a) (Nat.lor t (Nat.land o a)) h
    rw [tb_lor,Bool.or_eq_false_iff,tb_land] at h1
    refine ⟨h1.1, ?_, ?_⟩
    · intro ho b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have h4:=h1.2
        rw [ho] at h4
        simpa using h4
      · exact h2 (by rw [tb_lor,ho];rfl) b hb
    · refine List.pairwise_cons.mpr ⟨?_,h3⟩
      intro b hb hab
      have h4:=h2 (by rw [tb_lor,hab.1];simp) b hb
      rw [h4] at hab
      exact Bool.noConfusion hab.2
theorem priv_in {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) : ∀ z ∈ zs, ∀ q,
    (priv (tw (zs.map Prod.snd) 0 0) z.2).testBit q=true → z.1 q:=by
  intro z hz q hq
  obtain ⟨hq144,i,e',hi,he',ha,hb⟩:=hull_spec _ q hq
  have key : ∀ x,x < 144 →
      (Nat.land z.2 (Nat.xor (tw (zs.map Prod.snd) 0 0) full)).testBit x=true → z.1 x:=by
    intro x hx hbit
    rw [tb_land,tb_xor,full_tb,Bool.and_eq_true] at hbit
    obtain ⟨hzx,ht⟩:=hbit
    have ht' : (tw (zs.map Prod.snd) 0 0).testBit x=false:=by simpa [hx] using ht
    obtain ⟨_,_,hpw⟩:=tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z',hz',hzq⟩:=hP.cov x hx
    by_cases hzz : z'=z
    · rw [← hzz];exact hzq
    · exfalso
      exact pw_forall (fun a b h h'=>h ⟨h'.2,h'.1⟩) zs hpw z' hz' z hz hzz
        ⟨hP.sub z' hz' x hzq,hzx⟩
  have h1:=key _ (by omega) ha
  have h2:=key _ (by omega) hb
  have h3:=hP.rect z hz (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3
theorem hullsOK_sound (t : ℕ) : ∀ (zs : List ((ℕ → Prop) × ℕ)) (acc : ℕ),
    (∀ z ∈ zs, ∀ q,(priv t z.2).testBit q=true → z.1 q) →
    (∀ z ∈ zs, ∀ q,z.1 q → z.2.testBit q=true) →
    zs.Pairwise (fun z z' => ∀ q,z.1 q → z'.1 q → False) →
    (∀ q,acc.testBit q=true → ∀ z ∈ zs, ¬ z.1 q) →
    hullsOK t (zs.map Prod.snd) acc=true:=by
  intro zs
  induction zs with
  | nil=>intros;rfl
  | cons z zs ih =>
    intro acc hh hs hd ha
    rw [List.pairwise_cons] at hd
    have hz:=hh z List.mem_cons_self
    have e1:=land_sub _ _ (fun q hq=>hs z List.mem_cons_self q (hz q hq))
    have e2:=land_disj acc (priv t z.2) (fun q h1 h2=>ha q h1 z List.mem_cons_self (hz q h2))
    have e3:=ih (Nat.lor acc (priv t z.2)) (fun z' hz'=>hh z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz'=>hs z' (List.mem_cons_of_mem _ hz')) hd.2 (fun q hq z' hz' hz'q=>by
        rw [tb_lor,Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact ha q hq z' (List.mem_cons_of_mem _ hz') hz'q
        · exact hd.1 z' hz' q (hz q hq) hz'q)
    show (Nat.beq (Nat.land (priv t z.2) z.2) (priv t z.2) &&
      (Nat.beq (Nat.land acc (priv t z.2)) 0 &&
        hullsOK t (zs.map Prod.snd) (Nat.lor acc (priv t z.2))))=true
    rw [e1,e2,e3,Nat.beq_refl]
    rfl
theorem avOK1_sound {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    avOK1 (zs.map Prod.snd)=true :=
  hullsOK_sound _ zs 0 (priv_in hP) hP.sub hP.disj (fun q hq=>by simp at hq)
def tw' (l : List ℕ) : ℕ → ℕ → ℕ :=
 @List.rec ℕ (fun _ => ℕ → ℕ → ℕ) (fun _ t=>t)
 (fun a _ ih o t=>ih (Nat.lor o a) (Nat.lor t (Nat.land o a))) l
theorem tw'_eq (l : List ℕ) : ∀ o t : ℕ,tw' l o t=tw l o t:=by
  induction l with
  | nil=>intro o t;rfl
  | cons a l ih =>
    intro o t
    show tw' l (Nat.lor o a) (Nat.lor t (Nat.land o a))=tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))
    exact ih _ _
def hullsOK' (t : ℕ) (l : List ℕ) : ℕ → Bool :=
 @List.rec ℕ (fun _ => ℕ → Bool) (fun _=>true)
 (fun a _ ih acc=>(fun h=>band (Nat.beq (Nat.land h a) h)
 (band (Nat.beq (Nat.land acc h) 0) (ih (Nat.lor acc h)))) (priv t a)) l
theorem hullsOK'_eq (t : ℕ) (l : List ℕ) : ∀ acc : ℕ,hullsOK' t l acc=hullsOK t l acc:=by
  induction l with
  | nil=>intro acc;rfl
  | cons a l ih =>
    intro acc
    show band (Nat.beq (Nat.land (priv t a) a) (priv t a))
      (band (Nat.beq (Nat.land acc (priv t a)) 0) (hullsOK' t l (Nat.lor acc (priv t a)))) =
      (Nat.beq (Nat.land (priv t a) a) (priv t a) &&
        (Nat.beq (Nat.land acc (priv t a)) 0&&hullsOK t l (Nat.lor acc (priv t a))))
    rw [ih,band_eq,band_eq]
def mapW' (l : List ℕ) : List ℕ :=
 @List.rec ℕ (fun _=>List ℕ) [] (fun x _ ih=>rectW' x :: ih) l
theorem mapW'_eq (l : List ℕ) : mapW' l=l.map rectW:=by
  induction l with
  | nil=>rfl
  | cons x l ih =>
    show rectW' x :: mapW' l=rectW x :: l.map rectW
    rw [ih,rectW'_eq]
def Pc (x e i : ℕ) : Prop:=x.testBit e=true ∧ x.testBit i=false
def IsRect2 (S : ℕ → ℕ → Prop) : Prop := ∀ e i e' i' : ℕ,S e i → S e' i' → S e i'
theorem pc_rect (x : ℕ) : IsRect2 (Pc x):=fun _ _ _ _ h1 h2=>⟨h1.1,h2.2⟩
def KS (D : Finset ℕ) (j : ℕ) (f : ℕ → ℕ → ℕ) (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ)
 (Pi : ℕ → ℕ → ℕ → Prop) : Prop :=
 (∀ e i,e < 12 → 12 ≤ i → f e i ∈ D ∧ env (f e i) e i) ∧
 (∀ x ∈ D,IsRect2 (env x)) ∧
 (∀ x ∈ D, ∀ e i,env x e i → Pc x e i) ∧
 (∀ x ∈ D, ∀ y ∈ D,x ≠ y → c x=c y → ∀ e i,env x e i → env y e i → False) ∧
 (∀ x ∈ D,1 ≤ c x → ∀ e i,env x e i → Pi (c x) e i) ∧
 (∀ n,IsRect2 (Pi n)) ∧
 (∀ n e i,1 ≤ n → Pi n e i → ∃ y ∈ D,1 ≤ c y ∧ c y ≤ n ∧ Pc y e i) ∧
 (∀ x ∈ D,c x ≤ j)
theorem KS.own {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ e i,e < 12 → 12 ≤ i → f e i ∈ D ∧ env (f e i) e i:=h.1
theorem KS.envR {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ x ∈ D,IsRect2 (env x):=h.2.1
theorem KS.envP {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ x ∈ D, ∀ e i,env x e i → Pc x e i:=h.2.2.1
theorem KS.s1 {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ x ∈ D, ∀ y ∈ D,x ≠ y → c x=c y → ∀ e i,env x e i → env y e i → False:=h.2.2.2.1
theorem KS.s2 {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ x ∈ D,1 ≤ c x → ∀ e i,env x e i → Pi (c x) e i:=h.2.2.2.2.1
theorem KS.piR {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ n,IsRect2 (Pi n):=h.2.2.2.2.2.1
theorem KS.s3 {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ n e i,1 ≤ n → Pi n e i → ∃ y ∈ D,1 ≤ c y ∧ c y ≤ n ∧ Pc y e i:=h.2.2.2.2.2.2.1
theorem KS.lab {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ x ∈ D,c x ≤ j:=h.2.2.2.2.2.2.2
theorem ks_done : KS {4095} 0 (fun _ _=>4095) (fun _ e i=>Pc 4095 e i) (fun _=>0)
    (fun _ _ _=>False):=by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e i he hi
    refine ⟨by simp, ?_, ?_⟩
    · rw [tb4095];simpa using he
    · rw [tb4095];simpa using hi
  · intro x _;exact pc_rect 4095
  · intro x hx e i h
    rw [Finset.mem_singleton.mp hx];exact h
  · intro x hx y hy hxy
    exact absurd ((Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm) hxy
  · intro x _ h;simp at h
  · intro n e i e' i' h;exact h.elim
  · intro n e i _ h;exact h.elim
  · intro x _;exact le_rfl
def shiftL (c : ℕ → ℕ) (x y : ℕ) : ℕ := if y=x then 1 else if c y=0 then 0 else c y+1
theorem shiftL_self (c : ℕ → ℕ) (x : ℕ) : shiftL c x x=1:=by
  unfold shiftL;exact ite_p _ _ rfl
theorem shiftL_ne (c : ℕ → ℕ) (x y : ℕ) (h : y ≠ x) :
    (c y=0 ∧ shiftL c x y=0) ∨ (1 ≤ c y ∧ shiftL c x y=c y+1):=by
  unfold shiftL
  rw [ite_n _ _ h]
  by_cases h0 : c y=0
  · rw [ite_p _ _ h0];exact Or.inl ⟨h0,rfl⟩
  · rw [ite_n _ _ h0];exact Or.inr ⟨by omega,rfl⟩
theorem KS.promote {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) (x : ℕ) (hxD : x ∈ D) :
    KS D (j+1) f (fun y e i=>(y=x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (shiftL c x)
      (fun n e i=>(n=1 ∧ Pc x e i) ∨ (2 ≤ n ∧ Pi (n - 1) e i)):=by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1,h2⟩:=h.own e i he hi
    refine ⟨h1, ?_⟩
    by_cases hx : f e i=x
    · exact Or.inl ⟨hx,hx ▸ h.envP _ h1 e i h2⟩
    · exact Or.inr ⟨hx,h2⟩
  · intro y hy e i e' i' h1 h2
    rcases h1 with ⟨hx,h1⟩ | ⟨hx,h1⟩ <;> rcases h2 with ⟨hx',h2⟩ | ⟨hx',h2⟩
    · exact Or.inl ⟨hx,pc_rect x e i e' i' h1 h2⟩
    · exact absurd hx hx'
    · exact absurd hx' hx
    · exact Or.inr ⟨hx,h.envR y hy e i e' i' h1 h2⟩
  · intro y hy e i h1
    rcases h1 with ⟨hx,h1⟩ | ⟨hx,h1⟩
    · rw [hx];exact h1
    · exact h.envP y hy e i h1
  · intro y hy z hz hyz hc e i h1 h2
    by_cases hyx : y=x
    · have hzx : z ≠ x:=fun hh=>hyz (hyx.trans hh.symm)
      rw [hyx,shiftL_self] at hc
      rcases shiftL_ne c x z hzx with ⟨_,h3⟩ | ⟨_,h3⟩ <;> omega
    · by_cases hzx : z=x
      · rw [hzx,shiftL_self] at hc
        rcases shiftL_ne c x y hyx with ⟨_,h3⟩ | ⟨_,h3⟩ <;> omega
      · have hcc : c y=c z:=by
          rcases shiftL_ne c x y hyx with ⟨_,h3⟩ | ⟨_,h3⟩ <;>
            rcases shiftL_ne c x z hzx with ⟨_,h4⟩ | ⟨_,h4⟩ <;> omega
        rcases h1 with ⟨hx,_⟩ | ⟨_,h1⟩
        · exact hyx hx
        · rcases h2 with ⟨hx,_⟩ | ⟨_,h2⟩
          · exact hzx hx
          · exact h.s1 y hy z hz hyz hcc e i h1 h2
  · intro y hy hc e i h1
    rcases h1 with ⟨hx,h1⟩ | ⟨hx,h1⟩
    · rw [hx,shiftL_self];exact Or.inl ⟨rfl,h1⟩
    · rcases shiftL_ne c x y hx with ⟨_,h3⟩ | ⟨h4,h3⟩
      · omega
      · rw [h3]
        refine Or.inr ⟨by omega, ?_⟩
        rw [Nat.add_sub_cancel]
        exact h.s2 y hy h4 e i h1
  · intro n e i e' i' h1 h2
    rcases h1 with ⟨hn,h1⟩ | ⟨hn,h1⟩ <;> rcases h2 with ⟨hn',h2⟩ | ⟨hn',h2⟩
    · exact Or.inl ⟨hn,pc_rect x e i e' i' h1 h2⟩
    · omega
    · omega
    · exact Or.inr ⟨hn,h.piR _ e i e' i' h1 h2⟩
  · intro n e i hn h1
    rcases h1 with ⟨hn1,h1⟩ | ⟨hn2,h1⟩
    · exact ⟨x,hxD,by rw [shiftL_self],by rw [shiftL_self];omega,h1⟩
    · obtain ⟨y,hy,h3,h4,h5⟩:=h.s3 (n - 1) e i (by omega) h1
      by_cases hyx : y=x
      · exact ⟨y,hy,by rw [hyx,shiftL_self],by rw [hyx,shiftL_self];omega,h5⟩
      · rcases shiftL_ne c x y hyx with ⟨_,h6⟩ | ⟨_,h6⟩
        · omega
        · exact ⟨y,hy,by omega,by omega,h5⟩
  · intro y hy
    have:=h.lab y hy
    by_cases hyx : y=x
    · rw [hyx,shiftL_self];omega
    · rcases shiftL_ne c x y hyx with ⟨_,h6⟩ | ⟨_,h6⟩ <;> omega
def Prom (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x : ℕ) : Prop :=
 (∀ e i,Pc x e i → env x e i) ∧ 1 ≤ c x ∧ (1 ≤ c w → c x ≤ c w)
theorem prom_self (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x : ℕ) :
    Prom (fun y e i=>(y=x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (shiftL c x) w x:=by
  refine ⟨fun e i h=>Or.inl ⟨rfl,h⟩,by rw [shiftL_self],fun h=>by rw [shiftL_self];exact h⟩
theorem prom_other (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x y : ℕ) (hyx : y ≠ x) (hwx : w ≠ x)
    (h : Prom env c w y) :
    Prom (fun y e i=>(y=x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (shiftL c x) w y:=by
  obtain ⟨h1,h2,h3⟩:=h
  refine ⟨fun e i hp=>Or.inr ⟨hyx,h1 e i hp⟩, ?_, ?_⟩
  · rcases shiftL_ne c x y hyx with ⟨_,h6⟩ | ⟨_,h6⟩ <;> omega
  · intro hw
    rcases shiftL_ne c x y hyx with ⟨_,h6⟩ | ⟨_,h6⟩ <;>
      rcases shiftL_ne c x w hwx with ⟨_,h7⟩ | ⟨_,h7⟩ <;> omega
theorem ks_prom {D' : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (hK : KS D' j f env c Pi) (u v w : ℕ) (_huw : u ≠ w) (hvw : v ≠ w)
    (huv : u ≠ v) (ka kb : Bool) (hua : u ∈ D' ↔ ka=true) (hvb : v ∈ D' ↔ kb=true) :
    ∃ (j2 : ℕ) (env2 : ℕ → ℕ → ℕ → Prop) (c2 : ℕ → ℕ) (Pi2 : ℕ → ℕ → ℕ → Prop),
      KS D' j2 f env2 c2 Pi2 ∧ j2=j+(cond ka 1 0+cond kb 1 0) ∧
      (u ∈ D' → Prom env2 c2 w u) ∧ (v ∈ D' → Prom env2 c2 w v):=by
  cases ka <;> cases kb
  · exact ⟨j,env,c,Pi,hK,rfl,fun h=>Bool.noConfusion (hua.mp h),
      fun h=>Bool.noConfusion (hvb.mp h)⟩
  · exact ⟨_,_,_,_,hK.promote v (hvb.mpr rfl),rfl,fun h=>Bool.noConfusion (hua.mp h),
      fun _=>prom_self env c w v⟩
  · exact ⟨_,_,_,_,hK.promote u (hua.mpr rfl),rfl,fun _=>prom_self env c w u,
      fun h=>Bool.noConfusion (hvb.mp h)⟩
  · exact ⟨_,_,_,_,(hK.promote u (hua.mpr rfl)).promote v (hvb.mpr rfl),rfl,
      fun _=>prom_other _ _ w v u huv (Ne.symm hvw) (prom_self env c w u),
      fun _=>prom_self _ _ w v⟩
theorem KS.step {D D' : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D' j f env c Pi) (u v w : ℕ) (hu : u ∈ D) (hv : v ∈ D)
    (huv : u ≠ v) (hwD : w ∉ D) (hw : w ∈ D') (hD' : ∀ x ∈ D',x ≠ w → x ∈ D)
    (cc : ℕ → ℕ → Bool)
    (hcu : ∀ e i,Pc w e i → cc e i=true → Pc u e i)
    (hcv : ∀ e i,Pc w e i → cc e i=false → Pc v e i)
    (hcr : ∀ (b : Bool) (e i e' i' : ℕ),cc e i=b → cc e' i'=b → cc e i'=b)
    (hku : u ∈ D' → Prom env c w u) (hkv : v ∈ D' → Prom env c w v) :
    ∃ (f2 : ℕ → ℕ → ℕ) (env2 : ℕ → ℕ → ℕ → Prop) (c2 : ℕ → ℕ),KS D j f2 env2 c2 Pi:=by
  have hc2a : ∀ x,x ∈ D' → (if x ∈ D' then c x else c w)=c x:=fun x hx=>ite_p _ _ hx
  have hc2b : ∀ x,x ∉ D' → (if x ∈ D' then c x else c w)=c w:=fun x hx=>ite_n _ _ hx
  refine ⟨fun e i=>if f e i=w then cond (cc e i) u v else f e i,
    fun x e i=>(x ∈ D' ∧ env x e i) ∨
      (x ∉ D' ∧ env w e i ∧ ((x=u ∧ cc e i=true) ∨ (x=v ∧ cc e i=false))),
    fun x=>if x ∈ D' then c x else c w, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1,h2⟩:=h.own e i he hi
    show (if f e i=w then cond (cc e i) u v else f e i) ∈ D ∧
      (((if f e i=w then cond (cc e i) u v else f e i) ∈ D' ∧
        env (if f e i=w then cond (cc e i) u v else f e i) e i) ∨
      ((if f e i=w then cond (cc e i) u v else f e i) ∉ D' ∧ env w e i ∧
        (((if f e i=w then cond (cc e i) u v else f e i)=u ∧ cc e i=true) ∨
         ((if f e i=w then cond (cc e i) u v else f e i)=v ∧ cc e i=false))))
    by_cases hfw : f e i=w
    · rw [ite_p _ _ hfw]
      rw [hfw] at h2
      have hpw:=h.envP w hw e i h2
      cases hcc : cc e i
      · refine ⟨hv, ?_⟩
        by_cases hvD : v ∈ D'
        · exact Or.inl ⟨hvD,(hkv hvD).1 e i (hcv e i hpw hcc)⟩
        · exact Or.inr ⟨hvD,h2,Or.inr ⟨rfl,rfl⟩⟩
      · refine ⟨hu, ?_⟩
        by_cases huD : u ∈ D'
        · exact Or.inl ⟨huD,(hku huD).1 e i (hcu e i hpw hcc)⟩
        · exact Or.inr ⟨huD,h2,Or.inl ⟨rfl,rfl⟩⟩
    · rw [ite_n _ _ hfw]
      exact ⟨hD' _ h1 hfw,Or.inl ⟨h1,h2⟩⟩
  · intro x _ e i e' i' h1 h2
    rcases h1 with ⟨hx,h1⟩ | ⟨hx,h1,h1c⟩ <;> rcases h2 with ⟨hx',h2⟩ | ⟨hx',h2,h2c⟩
    · exact Or.inl ⟨hx,h.envR x hx e i e' i' h1 h2⟩
    · exact absurd hx hx'
    · exact absurd hx' hx
    · refine Or.inr ⟨hx,h.envR w hw e i e' i' h1 h2, ?_⟩
      rcases h1c with ⟨hxu,hc1⟩ | ⟨hxv,hc1⟩ <;> rcases h2c with ⟨hxu',hc2⟩ | ⟨hxv',hc2⟩
      · exact Or.inl ⟨hxu,hcr true e i e' i' hc1 hc2⟩
      · exact absurd (hxu.symm.trans hxv') huv
      · exact absurd (hxu'.symm.trans hxv) huv
      · exact Or.inr ⟨hxv,hcr false e i e' i' hc1 hc2⟩
  · intro x _ e i h1
    rcases h1 with ⟨hx,h1⟩ | ⟨_,h1,h1c⟩
    · exact h.envP x hx e i h1
    · have hpw:=h.envP w hw e i h1
      rcases h1c with ⟨hxu,hc1⟩ | ⟨hxv,hc1⟩
      · rw [hxu];exact hcu e i hpw hc1
      · rw [hxv];exact hcv e i hpw hc1
  · intro x hx y hy hxy hc e i h1 h2
    have hxw : x ≠ w:=fun hh=>hwD (hh ▸ hx)
    have hyw : y ≠ w:=fun hh=>hwD (hh ▸ hy)
    have hc' : (if x ∈ D' then c x else c w)=(if y ∈ D' then c y else c w):=hc
    rcases h1 with ⟨hx',h1⟩ | ⟨hx',h1,h1c⟩ <;> rcases h2 with ⟨hy',h2⟩ | ⟨hy',h2,h2c⟩
    · rw [hc2a x hx',hc2a y hy'] at hc'
      exact h.s1 x hx' y hy' hxy hc' e i h1 h2
    · rw [hc2a x hx',hc2b y hy'] at hc'
      exact h.s1 x hx' w hw hxw hc' e i h1 h2
    · rw [hc2b x hx',hc2a y hy'] at hc'
      exact h.s1 w hw y hy' (Ne.symm hyw) hc' e i h1 h2
    · rcases h1c with ⟨hxu,hc1⟩ | ⟨hxv,hc1⟩ <;> rcases h2c with ⟨hyu,hc2⟩ | ⟨hyv,hc2⟩
      · exact hxy (hxu.trans hyu.symm)
      · rw [hc1] at hc2;exact Bool.noConfusion hc2
      · rw [hc1] at hc2;exact Bool.noConfusion hc2
      · exact hxy (hxv.trans hyv.symm)
  · intro x _ hc e i h1
    have hc' : 1 ≤ (if x ∈ D' then c x else c w):=hc
    show Pi (if x ∈ D' then c x else c w) e i
    rcases h1 with ⟨hx',h1⟩ | ⟨hx',h1,_⟩
    · rw [hc2a x hx'] at hc' ⊢
      exact h.s2 x hx' hc' e i h1
    · rw [hc2b x hx'] at hc' ⊢
      exact h.s2 w hw hc' e i h1
  · exact h.piR
  · intro n e i hn h1
    obtain ⟨y,hy,h3,h4,h5⟩:=h.s3 n e i hn h1
    show ∃ y ∈ D,1 ≤ (if y ∈ D' then c y else c w) ∧ (if y ∈ D' then c y else c w) ≤ n ∧ Pc y e i
    by_cases hyw : y=w
    · rw [hyw] at h3 h4 h5
      cases hcc : cc e i
      · refine ⟨v,hv, ?_, ?_,hcv e i h5 hcc⟩
        · by_cases hvD : v ∈ D'
          · rw [hc2a v hvD];exact (hkv hvD).2.1
          · rw [hc2b v hvD];exact h3
        · by_cases hvD : v ∈ D'
          · rw [hc2a v hvD];exact le_trans ((hkv hvD).2.2 h3) h4
          · rw [hc2b v hvD];exact h4
      · refine ⟨u,hu, ?_, ?_,hcu e i h5 hcc⟩
        · by_cases huD : u ∈ D'
          · rw [hc2a u huD];exact (hku huD).2.1
          · rw [hc2b u huD];exact h3
        · by_cases huD : u ∈ D'
          · rw [hc2a u huD];exact le_trans ((hku huD).2.2 h3) h4
          · rw [hc2b u huD];exact h4
    · exact ⟨y,hD' y hy hyw,by rw [hc2a y hy];exact h3,by rw [hc2a y hy];exact h4,h5⟩
  · intro x _
    show (if x ∈ D' then c x else c w) ≤ j
    by_cases hx' : x ∈ D'
    · rw [hc2a x hx'];exact h.lab x hx'
    · rw [hc2b x hx'];exact h.lab w hw
theorem cond_sum (b : Bool) : (cond b 1 0 : ℕ)+cond b 0 1=1:=by cases b <;> rfl
theorem Reach.ks {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) :
    ∃ (j : ℕ) (f : ℕ → ℕ → ℕ) (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (Pi : ℕ → ℕ → ℕ → Prop),
      KS D j f env c Pi ∧ j+D.card ≤ k+1:=by
  induction h using Reach.ind with
  | done k=>exact ⟨0,_,_,_,_,ks_done,by simp⟩
  | step D k u v w ka kb hu hv hw hd hb hR ih =>
    obtain ⟨j,f,env,c,Pi,hK,hj⟩:=ih
    have hwD : w ∉ D:=fun hm=>by
      have:=hd w hm
      rw [blk_refl] at this
      exact Bool.noConfusion this
    have hwu : w ≠ u:=fun h=>hwD (h ▸ hu)
    have hwv : w ≠ v:=fun h=>hwD (h ▸ hv)
    have huv : u ≠ v:=by
      rintro rfl
      rcases hw with hw | hw
      · rw [Nat.and_self] at hw;exact hwu hw
      · rw [Nat.or_self] at hw;exact hwu hw
    have hwF : w ∉ D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v)) :=
      fun hm=>hwD (Finset.mem_of_mem_filter _ hm)
    rw [Finset.card_insert_of_notMem hwF] at hj
    have hsz:=size_lb2 D u v ka kb
    generalize (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))).card=size at hj hsz
    have hua : u ∈ insert w (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))) ↔
        ka=true:=by
      rw [Finset.mem_insert,Finset.mem_filter]
      constructor
      · rintro (h | ⟨_,h,_⟩)
        · exact absurd h.symm hwu
        · exact h.resolve_right (fun hh=>hh rfl)
      · intro h
        exact Or.inr ⟨hu,Or.inl h,Or.inr huv⟩
    have hvb : v ∈ insert w (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))) ↔
        kb=true:=by
      rw [Finset.mem_insert,Finset.mem_filter]
      constructor
      · rintro (h | ⟨_,_,h⟩)
        · exact absurd h.symm hwv
        · exact h.resolve_right (fun hh=>hh rfl)
      · intro h
        exact Or.inr ⟨hv,Or.inr (Ne.symm huv),Or.inl h⟩
    obtain ⟨j2,env2,c2,Pi2,hK2,hj2,hpu,hpv⟩ :=
      ks_prom hK u v w (Ne.symm hwu) (Ne.symm hwv) huv ka kb hua hvb
    have hD' : ∀ x ∈ insert w (D.filter (fun x=>(ka=true ∨ x ≠ u) ∧ (kb=true ∨ x ≠ v))),
        x ≠ w → x ∈ D:=by
      intro x hx hxw
      rcases Finset.mem_insert.mp hx with h | h
      · exact absurd h hxw
      · exact Finset.mem_of_mem_filter _ h
    have hfin : ∃ (f2 : ℕ → ℕ → ℕ) (env3 : ℕ → ℕ → ℕ → Prop) (c3 : ℕ → ℕ),
        KS D j2 f2 env3 c3 Pi2:=by
      rcases hw with rfl | rfl
      · exact hK2.step u v (u&&&v) hu hv huv hwD (Finset.mem_insert_self _ _) hD'
          (fun _ i => !(u.testBit i))
          (fun e i h1 h3=>and_cu u v e i h1.1 h1.2 h3)
          (fun e i h1 h3=>and_cv u v e i h1.1 h1.2 h3)
          (fun b e i e' i' _ h2=>h2) hpu hpv
      · exact hK2.step u v (u|||v) hu hv huv hwD (Finset.mem_insert_self _ _) hD'
          (fun e _=>u.testBit e)
          (fun e i h1 h3=>or_cu u v e i h1.1 h1.2 h3)
          (fun e i h1 h3=>or_cv u v e i h1.1 h1.2 h3)
          (fun b e i e' i' h1 _=>h1) hpu hpv
    obtain ⟨f2,env3,c3,hK3⟩:=hfin
    refine ⟨j2,f2,env3,c3,Pi2,hK3, ?_⟩
    have e1:=cond_sum ka
    have e2:=cond_sum kb
    omega
def MS (l : List ℕ) (j : ℕ) (Env : ℕ → ℕ → Prop) (c : ℕ → ℕ) (PiM : ℕ → ℕ → Prop) : Prop :=
 (∀ q,q < 144 → ∃ x ∈ l,Env x q) ∧
 (∀ x ∈ l,IsRect (Env x)) ∧
 (∀ x ∈ l, ∀ q,Env x q → q < 144 ∧ (rectW x).testBit q=true) ∧
 (∀ x ∈ l, ∀ y ∈ l,x ≠ y → c x=c y → ∀ q,Env x q → Env y q → False) ∧
 (∀ x ∈ l,1 ≤ c x → ∀ q,Env x q → PiM (c x) q) ∧
 (∀ n,IsRect (PiM n)) ∧
 (∀ n q,1 ≤ n → PiM n q → ∃ y ∈ l,1 ≤ c y ∧ c y ≤ n ∧ (rectW y).testBit q=true) ∧
 (∀ x ∈ l,c x ≤ j)
theorem MS.own {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ q,q < 144 → ∃ x ∈ l,Env x q:=h.1
theorem MS.envR {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ x ∈ l,IsRect (Env x):=h.2.1
theorem MS.envB {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ x ∈ l, ∀ q,Env x q → q < 144 ∧ (rectW x).testBit q=true:=h.2.2.1
theorem MS.s1 {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ x ∈ l, ∀ y ∈ l,x ≠ y → c x=c y → ∀ q,Env x q → Env y q → False:=h.2.2.2.1
theorem MS.s2 {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ x ∈ l,1 ≤ c x → ∀ q,Env x q → PiM (c x) q:=h.2.2.2.2.1
theorem MS.piR {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ n,IsRect (PiM n):=h.2.2.2.2.2.1
theorem MS.s3 {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ n q,1 ≤ n → PiM n q → ∃ y ∈ l,1 ≤ c y ∧ c y ≤ n ∧ (rectW y).testBit q=true:=h.2.2.2.2.2.2.1
theorem MS.lab {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ x ∈ l,c x ≤ j:=h.2.2.2.2.2.2.2
theorem rect_conv (S : ℕ → ℕ → Prop) (hS : IsRect2 S) :
    IsRect (fun q=>q < 144 ∧ S (q / 12) (12+q % 12)):=by
  intro e i e' i' he hi he' hi' h1 h2
  have h1' : S ((12*e+i) / 12) (12+(12*e+i) % 12):=h1.2
  have h2' : S ((12*e'+i') / 12) (12+(12*e'+i') % 12):=h2.2
  have e1 : (12*e+i) / 12=e:=by omega
  have e2 : (12*e+i) % 12=i:=by omega
  have e3 : (12*e'+i') / 12=e':=by omega
  have e4 : (12*e'+i') % 12=i':=by omega
  have e5 : (12*e+i') / 12=e:=by omega
  have e6 : (12*e+i') % 12=i':=by omega
  rw [e1,e2] at h1'
  rw [e3,e4] at h2'
  show 12*e+i' < 144 ∧ S ((12*e+i') / 12) (12+(12*e+i') % 12)
  rw [e5,e6]
  exact ⟨by omega,hS _ _ _ _ h1' h2'⟩
theorem pc_bit (x q : ℕ) (hq : q < 144) (h : Pc x (q / 12) (12+q % 12)) :
    (rectW x).testBit q=true:=by
  have h3:=rectW_tb x (q / 12) (q % 12) (by omega) (Nat.mod_lt _ (by norm_num)) h.1 h.2
  rwa [Nat.div_add_mod] at h3
theorem KS.toMS {l : List ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS l.toFinset j f env c Pi) :
    MS l j (fun x q=>q < 144 ∧ env x (q / 12) (12+q % 12)) c
      (fun n q=>q < 144 ∧ Pi n (q / 12) (12+q % 12)):=by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨h1,h2⟩:=h.own (q / 12) (12+q % 12) (by omega) (by omega)
    exact ⟨_,List.mem_toFinset.mp h1,hq,h2⟩
  · intro x hx
    exact rect_conv _ (h.envR x (List.mem_toFinset.mpr hx))
  · intro x hx q hq
    exact ⟨hq.1,pc_bit x q hq.1 (h.envP x (List.mem_toFinset.mpr hx) _ _ hq.2)⟩
  · intro x hx y hy hxy hc q h1 h2
    exact h.s1 x (List.mem_toFinset.mpr hx) y (List.mem_toFinset.mpr hy) hxy hc _ _ h1.2 h2.2
  · intro x hx hc q h1
    exact ⟨h1.1,h.s2 x (List.mem_toFinset.mpr hx) hc _ _ h1.2⟩
  · intro n
    exact rect_conv _ (h.piR n)
  · intro n q hn h1
    obtain ⟨y,hy,h3,h4,h5⟩:=h.s3 n _ _ hn h1.2
    exact ⟨y,List.mem_toFinset.mp hy,h3,h4,pc_bit y q h1.1 h5⟩
  · intro x hx
    exact h.lab x (List.mem_toFinset.mpr hx)
theorem MS.priv_env {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop}
    (hM : MS l j Env c PiM) : ∀ y ∈ l, ∀ q,
    (priv (tw (l.map rectW) 0 0) (rectW y)).testBit q=true → Env y q:=by
  intro y hy q hq
  obtain ⟨hq144,i,e',hi,he',ha,hb⟩:=hull_spec _ q hq
  have key : ∀ x,x < 144 →
      (Nat.land (rectW y) (Nat.xor (tw (l.map rectW) 0 0) full)).testBit x=true → Env y x:=by
    intro x hx hbit
    rw [tb_land,tb_xor,full_tb,Bool.and_eq_true] at hbit
    obtain ⟨hzx,ht⟩:=hbit
    have ht' : (tw (l.map rectW) 0 0).testBit x=false:=by simpa [hx] using ht
    obtain ⟨_,_,hpw⟩:=tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z,hz,hzq⟩:=hM.own x hx
    by_cases hzz : z=y
    · rw [← hzz];exact hzq
    · exfalso
      exact pw_forall (fun a b h h'=>h ⟨h'.2,h'.1⟩) l hpw z hz y hy hzz
        ⟨(hM.envB z hz x hzq).2,hzx⟩
  have h1:=key _ (by omega) ha
  have h2:=key _ (by omega) hb
  have h3:=hM.envR y hy (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3
def ValidLab (l : List ℕ) (K : ℕ) (c : ℕ → ℕ) : Prop :=
 (∀ x ∈ l,c x ≤ K) ∧
 (∀ x ∈ l, ∀ y ∈ l,x ≠ y → c x=c y →
 Nat.land (priv (tw (l.map rectW) 0 0) (rectW x)) (priv (tw (l.map rectW) 0 0) (rectW y))=0) ∧
 (∀ i U : ℕ,1 ≤ i →
 (∀ q,U.testBit q=true →
 ∃ x ∈ l,c x=i ∧ (priv (tw (l.map rectW) 0 0) (rectW x)).testBit q=true) →
 ∀ q,(hull U).testBit q=true → ∃ y ∈ l,1 ≤ c y ∧ c y ≤ i ∧ (rectW y).testBit q=true) ∧
 (∀ x ∈ l, ∀ q,(priv (tw (l.map rectW) 0 0) (rectW x)).testBit q=true →
 (rectW x).testBit q=true)
theorem MS.validLab {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop}
    (hM : MS l j Env c PiM) (K : ℕ) (hK : j ≤ K) : ValidLab l K c:=by
  refine ⟨fun x hx=>le_trans (hM.lab x hx) hK, ?_, ?_, ?_⟩
  · intro x hx y hy hxy hc
    exact land_disj _ _ (fun q h1 h2 =>
      hM.s1 x hx y hy hxy hc q (hM.priv_env x hx q h1) (hM.priv_env y hy q h2))
  · intro i U hi hU q hq
    obtain ⟨_,a,e',ha,he',h1,h2⟩:=hull_spec _ q hq
    obtain ⟨x1,hx1,hc1,hb1⟩:=hU _ h1
    obtain ⟨x2,hx2,hc2,hb2⟩:=hU _ h2
    have hp1:=hM.s2 x1 hx1 (by omega) _ (hM.priv_env x1 hx1 _ hb1)
    have hp2:=hM.s2 x2 hx2 (by omega) _ (hM.priv_env x2 hx2 _ hb2)
    rw [hc1] at hp1
    rw [hc2] at hp2
    have h3:=hM.piR i (q / 12) a e' (q % 12) (by omega) ha he' (Nat.mod_lt _ (by norm_num))
      hp1 hp2
    rw [Nat.div_add_mod] at h3
    exact hM.s3 i q hi h3
  · intro x hx q hq
    exact (hM.envB x hx q (hM.priv_env x hx q hq)).2
theorem reach_validLab {m : Bool} {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hR : Reach m l.toFinset k) :
    ∃ c : ℕ → ℕ,ValidLab l (Nat.sub (Nat.succ k) l.length) c:=by
  obtain ⟨j,f,env,c,Pi,hK,hj⟩:=hR.ks
  rw [List.toFinset_card_of_nodup hnd] at hj
  exact ⟨c,hK.toMS.validLab _ (by
    show j ≤ (k+1) - l.length
    omega)⟩
def subM (h c : ℕ) : Bool:=Nat.beq (Nat.land h c) h
def fcov (t t2 : ℕ) : List ℕ → ℕ
  | []=>0
  | a :: l=>cond (Nat.beq (Nat.land (priv t a) t2) 0) (Nat.lor a (fcov t t2 l)) (fcov t t2 l)
def privH (l : List ℕ) (x : ℕ) : ℕ := priv (tw (l.map rectW) 0 0) (rectW x)
def t2Of (l : List ℕ) : ℕ := tw ((l.map rectW).map (priv (tw (l.map rectW) 0 0))) 0 0
def isConf (l : List ℕ) (x : ℕ) : Prop:=Nat.land (privH l x) (t2Of l) ≠ 0
def ClassLab (l : List ℕ) (K : ℕ) (c : ℕ → ℕ) : Prop :=
 (∀ x ∈ l,isConf l x → c x ≤ K) ∧
 (l.Pairwise (fun x y=>isConf l x → isConf l y → c x=c y →
 Nat.land (privH l x) (privH l y)=0)) ∧
 (∀ i U : ℕ,1 ≤ i → i ≤ K →
 (∀ r,U.testBit r=true →
 ∃ x ∈ l,isConf l x ∧ c x=i ∧ (privH l x).testBit r=true) →
 ∀ q,(hull U).testBit q=true →
 ∃ y ∈ l,(rectW y).testBit q=true ∧ (isConf l y → 1 ≤ c y ∧ c y ≤ i))
theorem ClassLab.le {l : List ℕ} {K : ℕ} {c : ℕ → ℕ} (h : ClassLab l K c) :
    ∀ x ∈ l,isConf l x → c x ≤ K:=h.1
theorem ClassLab.ne {l : List ℕ} {K : ℕ} {c : ℕ → ℕ} (h : ClassLab l K c) :
    l.Pairwise (fun x y=>isConf l x → isConf l y → c x=c y →
        Nat.land (privH l x) (privH l y)=0):=h.2.1
theorem ClassLab.cov {l : List ℕ} {K : ℕ} {c : ℕ → ℕ} (h : ClassLab l K c) :
    ∀ i U : ℕ,1 ≤ i → i ≤ K →
        (∀ r,U.testBit r=true →
          ∃ x ∈ l,isConf l x ∧ c x=i ∧ (privH l x).testBit r=true) →
        ∀ q,(hull U).testBit q=true →
        ∃ y ∈ l,(rectW y).testBit q=true ∧ (isConf l y → 1 ≤ c y ∧ c y ≤ i):=h.2.2
theorem land_zero_tb (a b q : ℕ) (h : Nat.land a b=0) (ha : a.testBit q=true)
    (hb : b.testBit q=true) : False:=by
  have e:=tb_land a b q
  rw [h,ha,hb,Nat.zero_testBit] at e
  exact Bool.noConfusion e
theorem fcov_tb (t t2 q : ℕ) : ∀ as : List ℕ, ∀ a ∈ as,
    Nat.beq (Nat.land (priv t a) t2) 0=true → a.testBit q=true →
    (fcov t t2 as).testBit q=true:=by
  intro as
  induction as with
  | nil=>intro a ha;simp at ha
  | cons b as ih =>
    intro a ha hb hq
    show (cond (Nat.beq (Nat.land (priv t b) t2) 0) (Nat.lor b (fcov t t2 as))
      (fcov t t2 as)).testBit q=true
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hb]
      show (Nat.lor a (fcov t t2 as)).testBit q=true
      rw [tb_lor,hq]
      rfl
    · have:=ih a ha hb hq
      cases Nat.beq (Nat.land (priv t b) t2) 0
      · exact this
      · show (Nat.lor b (fcov t t2 as)).testBit q=true
        rw [tb_lor,this]
        exact Bool.or_true _
theorem beq0_false {n : ℕ} (h : Nat.beq n 0=false) : n ≠ 0:=by
  intro e
  rw [e] at h
  exact Bool.noConfusion h
def forceWord (w : Word) (k : Word → Bool) : Bool :=
 Nat.rec (k 0) (fun n _=>k (n+1)) w
theorem forceWordEq (w : Word) (k : Word → Bool) : forceWord w k=k w:=by
  cases w <;> rfl
def forceColumns (ws : List Word) (k : List Word → Bool) : Bool :=
 (List.rec (motive:=fun _=>(List Word → Bool) → Bool) (fun f=>f [])
 (fun a _ next f=>forceWord a (fun w=>next (fun tail=>f (w :: tail)))) ws) k
theorem forceColumnsEq (ws : List Word) (k : List Word → Bool) : forceColumns ws k=k ws:=by
  induction ws generalizing k with
  | nil=>rfl
  | cons a ws ih =>
    change forceWord a (fun w=>forceColumns ws (fun tail=>k (w :: tail)))=_
    rw [forceWordEq,ih]
def fastRectColumn (ws : List Word) : Bool :=
 forceColumns (mapW' ws) fun rs =>
 forceWord (tw' rs 0 0) fun twice=>hullsOK' twice rs 0
theorem fastRectColumnEq (ws : List Word) : fastRectColumn ws=rectOK1 ws:=by
  simp only [fastRectColumn,forceColumnsEq,forceWordEq,mapW'_eq,hullsOK'_eq,tw'_eq,rectOK1,avOK1]
end PackedRect
abbrev RowChart:={ rows : List Nat // rows.length=24 }
def chartRow (chart : RowChart) (i : Nat) : Nat :=
 chart.val.getD i 0
def chartBits (w : Word) (rows : List Nat) : Word :=
  List.rec 0 (fun r _ packed=>((w>>>r)&&&1)|||(packed<<<1)) rows
theorem chartBitsBit (w : Word) (rows : List Nat) (i : Nat) (hi : i < rows.length) :
    (chartBits w rows).testBit i=w.testBit (rows.getD i 0):=by
  induction rows generalizing i with
  | nil=>simp at hi
  | cons row rows ih =>
    change (((w>>>row)&&&1)|||(chartBits w rows<<<1)).testBit i=_
    rw [Nat.testBit_or,Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_shiftLeft]
    cases i with
    | zero=>simp
    | succ i =>
      have lt : i < rows.length:=by simpa using hi
      simp [ih i lt,Nat.testBit_succ]
def chartWord (chart : RowChart) (w : Word) : Word:=chartBits w chart.val
def ChartOK (goal : Word) (chart : RowChart) : Prop :=
 (∀ i : Fin 12,goal.testBit (chartRow chart i.val)=true) ∧
 (∀ i : Fin 12,goal.testBit (chartRow chart (12+i.val))=false)
def chartCheck (goal : Word) (chart : Option RowChart) : Bool :=
 chart.all fun c => @decide (ChartOK goal c) (by unfold ChartOK;infer_instance)
theorem chartOfCheck {goal : Word} {chart : Option RowChart}
    (ok : chartCheck goal chart=true) (c : RowChart) (eq : chart=some c) :
    ChartOK goal c:=by
  subst chart
  unfold ChartOK
  exact of_decide_eq_true ok
theorem chartWordBit (chart : RowChart) (w : Word) {i : Nat} (hi : i < 24) :
    (chartWord chart w).testBit i=w.testBit (chartRow chart i):=by
  exact chartBitsBit w chart.val i (by rw [chart.property];exact hi)
theorem chartPos {goal : Word} {chart : RowChart} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart i)=true:=ok.1 ⟨i,hi⟩
theorem chartNeg {goal : Word} {chart : RowChart} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart (12+i))=false:=ok.2 ⟨i,hi⟩
theorem chartRectangles {goal : Word} {chart : RowChart} {ws : List Word}
    (ok : ChartOK goal chart) (nd : ws.Nodup) (kw : KWPartition goal ws.toFinset) :
    PackedRect.rectOK1 (ws.map (chartWord chart))=true:=by
  obtain ⟨f,good,rectangle⟩:=kw
  let label:=fun p n=>f (chartRow chart p) (chartRow chart (12+n))
  let part:=fun w=>((fun q : Nat=>q < 144 ∧ label (q/12) (q % 12)=w),
    PackedRect.rectW (chartWord chart w))
  have partition : PackedRect.Part (ws.map part):=by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro z hz
      obtain ⟨w,_,rfl⟩:=List.mem_map.mp hz
      intro p n p' n' hp hn hp' hn' h h'
      have divmod (a b : Nat) (lt : b < 12) :
          (12*a+b)/12=a ∧ (12*a+b)%12=b:=by omega
      have h1:=h.2
      have h2:=h'.2
      rw [(divmod p n hn).1,(divmod p n hn).2] at h1
      rw [(divmod p' n' hn').1,(divmod p' n' hn').2] at h2
      refine ⟨by omega,?_⟩
      rw [(divmod p n' hn').1,(divmod p n' hn').2]
      exact (rectangle _ _ _ _ (chartPos ok hp) (chartPos ok hp') (chartNeg ok hn)
        (chartNeg ok hn') (h1.trans h2.symm)).trans h1
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩:=List.mem_map.mp hz
      exact hq.1
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun hne q h1 h2=>hne (h1.2.symm.trans h2.2)) nd
    · intro q hq
      have member:=(good _ _ (chartPos ok (show q/12 < 12 by omega))
        (chartNeg ok (Nat.mod_lt q (by decide : 0 < 12)))).1
      exact ⟨_,List.mem_map.mpr ⟨_,List.mem_toFinset.mp member,rfl⟩,hq,rfl⟩
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩:=List.mem_map.mp hz
      obtain ⟨bound,same⟩:=hq
      have hp : q/12 < 12:=by omega
      have hn : q % 12 < 12:=Nat.mod_lt _ (by decide)
      have h:=(good _ _ (chartPos ok hp) (chartNeg ok hn)).2
      change (label (q/12) (q % 12)).testBit (chartRow chart (q/12))=true ∧
        (label (q/12) (q % 12)).testBit (chartRow chart (12+q % 12))=false at h
      rw [same] at h
      have bit:=PackedRect.rectW_tb (chartWord chart w) (q/12) (q % 12) hp hn
        ((chartWordBit chart w (by omega)).trans h.1)
        ((chartWordBit chart w (by omega)).trans h.2)
      rwa [Nat.div_add_mod] at bit
  have hw:=PackedRect.avOK1_sound partition
  simpa only [PackedRect.rectOK1,List.map_map,Function.comp_def,part] using hw
theorem maskedBelow {mask w : Word} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w:=by
  unfold Masked at *
  rw [← bw,Nat.land_assoc,bm,bw]
theorem maskedTransfer {mask w : Word} {select : Fin rows → Fin rows}
    (same : relabel select mask=mask) (hw : Masked mask w) :
    Masked mask (relabel select w):=by
  unfold Masked at *
  rw [← same, ← relabelAnd,hw]
theorem liveMaskedImage {mask goal : Word} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k t : Nat} {S : Finset Word} (live : LiveWord mask goal k t S)
    (masked : ∀ w ∈ S,Masked mask w) :
    LiveWord mask goal k t (S.image (relabel select)):=by
  let f:=relabel select
  have hmask : f mask=mask:=auto.2.1
  have inj {a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
      f a=f b → a=b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have proper {a : Word} (ma : Masked mask a) (ha : properWord mask a) :
      properWord mask (f a):=by
    exact ⟨fun eq=>ha.1 (inj ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq=>ha.2 (inj ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {S : Finset Word} {v : Word} (hv : v ∉ S) (mv : Masked mask v)
      (ms : ∀ w ∈ S,Masked mask w) : f v ∉ S.image f:=by
    intro hw
    obtain ⟨w,hs,eq⟩:=Finset.mem_image.mp hw
    exact hv (inj (ms w hs) mv eq ▸ hs)
  induction live using LiveWord.ind with
  | stop hp =>
    rw [Finset.image_singleton,auto.2.2]
    exact LiveWord.stop hp
  | @unary k t U a ha fresh tail ih =>
    let v:=mask^^^a
    have ma:=masked a (Finset.mem_insert_self ..)
    have mv : Masked mask v:=by
      apply maskedGate (bank:=[a]) (by simpa using ma)
      exact Or.inl ⟨a,Or.inr (Or.inr (by simp)),rfl⟩
    have hnew : ∀ w ∈ insert v U,Masked mask w:=by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem hU)
    have fve : f v=mask^^^f a:=by
      change relabel select (mask^^^a)=_
      rw [relabelXor,auto.2.1]
    have ht:=ih hnew
    have hf:=freshImage fresh mv masked
    change LiveWord mask goal (k+1) (t+1) ((insert a U).image f)
    rw [Finset.image_insert] at ht hf
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht hf
    rw [Finset.image_insert]
    exact LiveWord.unary (proper ma ha) hf ht
  | @binary k t U a b op pa pb ab fresh tail ih =>
    let v:=binWord op a b
    have ma:=masked a (Finset.mem_insert_self ..)
    have mb:=masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v:=by
      apply maskedGate (bank:=[a,b]) (by simpa using And.intro ma mb)
      exact Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by
        cases op <;> simp [v,binWord]⟩
    have hnew : ∀ w ∈ insert v U,Masked mask w:=by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have fve : f v=binWord op (f a) (f b):=by
      cases op
      · exact relabelAnd ..
      · exact relabelOr ..
    have ht:=ih hnew
    have hf:=freshImage fresh mv masked
    change LiveWord mask goal (k+1) t ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert,Finset.image_insert,fve] at hf
    rw [Finset.image_insert,Finset.image_insert]
    exact LiveWord.binary (proper ma pa) (proper mb pb) (fun h=>ab (inj ma mb h)) hf ht
def dagMoveWords (m : WordMove) (ws : List Word) : List Word :=
 List.rec [] (fun w _ next=>insertWord (mixMove m w) next) ws
theorem dagMoveSet {m : WordMove} {ws : List Word} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws,mixMove m w=relabel select w) :
    (dagMoveWords m ws).toFinset=ws.toFinset.image (relabel select):=by
  induction ws with
  | nil=>simp [dagMoveWords]
  | cons w ws ih =>
    change (insertWord (mixMove m w) (dagMoveWords m ws)).toFinset=_
    rw [insertWordSet,ih (fun w hw=>agree _ (List.mem_cons_of_mem _ hw)),
      agree _ List.mem_cons_self,List.toFinset_cons,Finset.image_insert]
def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args:=g.inputs.map fun i=>bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and=>args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or=>args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _=>0
def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
 List (BitVec rows) :=
 bank ++ [hcsGateVal bank g]
theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i=(bank.map fun w=>w.getLsbD i).getD k false:=by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases bank[k]? <;> simp
theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val=(xs.map fun w=>w.getLsbD i.val).all id:=by
  induction xs with
  | nil=>simp [i.isLt]
  | cons a t ih=>simp only [List.foldr_cons,BitVec.getLsbD_and,List.map_cons,List.all_cons,id_eq,ih]
theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val=(xs.map fun w=>w.getLsbD i.val).any id:=by
  induction xs with
  | nil=>simp
  | cons a t ih=>simp only [List.foldr_cons,BitVec.getLsbD_or,List.map_cons,List.any_cons,id_eq,ih]
theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k=>(bank.map fun w=>w.getLsbD i.val).getD k false):=by
  obtain ⟨op,ins⟩:=g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal,PEqualNP.CircuitLowerBounds.GateOp.eval,hcsAndBit,List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal,PEqualNP.CircuitLowerBounds.GateOp.eval,hcsOrBit,List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal,PEqualNP.CircuitLowerBounds.GateOp.eval,BitVec.getLsbD_not,i.isLt,
      decide_true,Bool.true_and]
    cases ins with
    | nil=>simp
    | cons k _=>simp only [List.map_cons,List.headD_cons,hcsGetDBit]
theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs,g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w=>w.getLsbD i.val) =
      gs.foldl (fun w g=>w ++ [g.op.eval (g.inputs.map fun k=>w.getD k false)])
        (bank.map fun w=>w.getLsbD i.val):=by
  induction gs generalizing bank with
  | nil=>rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w=>w.getLsbD i.val) =
        (bank.map fun w=>w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k=>(bank.map fun w=>w.getLsbD i.val).getD k false)]:=by
      simp only [hcsStep,List.map_append,List.map_cons,List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg')),hstep]
def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0,s=>p s
  | k+1,s=>hcsCheckPow p k s&&hcsCheckPow p k (s+2 ^ k)
theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s=true) (lo : s ≤ i) (hi : i < s+2 ^ k) : p i=true:=by
  induction k generalizing s with
  | zero =>
    have e : i=s:=by omega
    simpa [hcsCheckPow,e] using h
  | succ k ih =>
    simp only [hcsCheckPow,Bool.and_eq_true] at h
    by_cases hlt : i < s+2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi;omega)
def hcsBitsNat : {k : Nat} → (Fin k → Bool) → Nat
  | 0,_=>0
  | k+1,x=>(if x 0 then 1 else 0)+2*hcsBitsNat (fun i : Fin k=>x i.succ)
theorem hcsBitsNat_lt : ∀ {k : Nat} (x : Fin k → Bool),hcsBitsNat x < 2 ^ k
  | 0,_=>by simp [hcsBitsNat]
  | k+1,x=>by
    have ih:=hcsBitsNat_lt (fun i : Fin k=>x i.succ)
    simp only [hcsBitsNat,Nat.pow_succ]
    cases x 0
    · simp;omega
    · simp;omega
theorem hcsBitsNat_testBit : ∀ {k : Nat} (x : Fin k → Bool) (i : Fin k),
    (hcsBitsNat x).testBit i.val=x i
  | 0,_,i=>Fin.elim0 i
  | k+1,x,i=>by
    refine Fin.cases ?_ ?_ i
    · simp only [hcsBitsNat,Fin.val_zero]
      cases x 0
      · simp [Nat.testBit_zero]
      · have hmod : (1+2*hcsBitsNat (fun m : Fin k=>x m.succ)) % 2=1:=by omega
        simp [Nat.testBit_zero,hmod]
    · intro j
      have ih:=hcsBitsNat_testBit (fun m : Fin k=>x m.succ) j
      have hdiv : ((if x 0 then 1 else 0)+2*hcsBitsNat (fun m : Fin k=>x m.succ)) / 2 =
          hcsBitsNat (fun m : Fin k=>x m.succ):=by
        cases x 0
        · simp
        · simp;omega
      simpa only [hcsBitsNat,Fin.val_succ,Nat.testBit_succ,hdiv] using ih
theorem hcsWitnessEval {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hRaw : hcsCheckPow (fun r=>(raw.map fun v=>v.getLsbD r)==List.ofFn fun j : Fin n=>r.testBit j.val) n 0=true)
    (hGoal : hcsCheckPow (fun r=>goal.getLsbD r==f (fun j : Fin n=>r.testBit j.val)) n 0=true)
    (hEval : (C.gates.foldl hcsStep raw).getD C.output 0=goal) :
    ∀ x : Fin n → Bool,C.eval (List.ofFn x)=f x:=by
  intro x
  let r:=hcsBitsNat x
  have hr : r < 2 ^ n:=hcsBitsNat_lt x
  have hx : x=fun j : Fin n=>r.testBit j.val:=by
    funext j
    exact (hcsBitsNat_testBit x j).symm
  rw [hx]
  have hbank : raw.map (fun v=>v.getLsbD r)=List.ofFn fun j : Fin n=>r.testBit j.val :=
    beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
  have hfg : goal.getLsbD r=f (fun j : Fin n=>r.testBit j.val) :=
    beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
  have hbits:=hcsFoldBits raw ⟨r,hr⟩ C.gates hfan
  change (C.gates.foldl (fun w g=>w ++ [g.op.eval (g.inputs.map fun k=>w.getD k false)])
    (List.ofFn fun j : Fin n=>r.testBit j.val)).getD C.output false =
      f (fun j : Fin n=>r.testBit j.val)
  rw [← hbank, ← hbits, ← hcsGetDBit,hEval,hfg]
theorem hcsEvalWord {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r=>(raw.map fun v=>v.getLsbD r)==List.ofFn fun j : Fin n=>r.testBit j.val) n 0=true)
    (hGoal : hcsCheckPow (fun r=>goal.getLsbD r==f (fun j : Fin n=>r.testBit j.val)) n 0=true)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hev : ∀ x,C.eval (List.ofFn x)=f x) :
    (C.gates.foldl hcsStep raw).getD C.output 0=goal:=by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let y : Fin n → Bool:=fun k=>j.testBit k.val
  have hbank : raw.map (fun v=>v.getLsbD j)=List.ofFn y :=
    beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
  have hfg : goal.getLsbD j=f y :=
    beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
  have hbits:=hcsFoldBits raw ⟨j,hj⟩ C.gates hfan
  have hevj : (C.wires (List.ofFn y)).getD C.output false=f y:=hev y
  change (C.gates.foldl (fun w g=>w ++ [g.op.eval (g.inputs.map fun k=>w.getD k false)])
    (List.ofFn y)).getD C.output false=f y at hevj
  rw [← hbank, ← hbits] at hevj
  rw [hfg, ← hevj, ← hcsGetDBit]
def ExactLower (mask : Nat) (stock : List Word) (goal : Word) (t min : Nat) : Prop :=
 ∀ k S,LiveWord mask goal k t S → (∀ w ∈ S,AvailableWord mask stock w) → min ≤ k
abbrev ExactBound:=Nat × List Word × Nat × Nat × Word
def ExactKnown (bounds : List ExactBound) : Prop :=
 ∀ b ∈ bounds,
 ExactLower b.1 b.2.1 b.2.2.2.2 0 b.2.2.1 ∧
 ExactLower b.1 b.2.1 b.2.2.2.2 1 b.2.2.2.1
theorem extendExactKnown {b : ExactBound} {bs : List ExactBound}
    (old : ExactKnown bs)
    (h0 : ExactLower b.1 b.2.1 b.2.2.2.2 0 b.2.2.1)
    (h1 : ExactLower b.1 b.2.1 b.2.2.2.2 1 b.2.2.2.1) :
    ExactKnown (b :: bs):=by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨h0,h1⟩
  · exact old x hx
theorem stockMaskedOfCheck {mask : Word} {stock : List Word}
    (h : stock.all (fun w=>w&&&mask==w)=true) :
    ∀ w ∈ stock,Masked mask w :=
  fun w hw=>beq_iff_eq.mp (List.all_eq_true.mp h w hw)
theorem pullWordExact {mask target : Word} {w : List Word} {z : Word} {k t : Nat} {S : Finset Word}
    (h : LiveWord mask target k t S) (sub : ∀ a ∈ S,a ∈ w ++ [z]) :
    (wordRep mask w z → ∃ S',LiveWord mask target k t S' ∧ ∀ a ∈ S',a ∈ w) ∧
    (binaryWitness mask w z → ∃ k' S',k' ≤ k+1 ∧ LiveWord mask target k' t S' ∧ ∀ a ∈ S',a ∈ w) ∧
    ((∃ a ∈ w,properWord mask a ∧ z=mask^^^a) →
      ∃ k' t' S',k' ≤ k+1 ∧ t ≤ t' ∧ t' ≤ t+1 ∧ k'+(t+1 - t') ≤ k+1 ∧
        LiveWord mask target k' t' S' ∧ ∀ a ∈ S',a ∈ w):=by
  have noZ (hdrop : z ∉ S ∨ z ∈ w) : ∀ a ∈ S,a ∈ w:=by
    intro a ha
    have hu : a ∈ w ∨ a=z:=by simpa using sub a ha
    rcases hu with hu | rfl
    · exact hu
    · exact hdrop.resolve_left (fun hn=>hn ha)
  refine ⟨?_, ?_, ?_⟩
  · intro hr
    by_cases hm : z ∈ S
    · by_cases hw : z ∈ w
      · exact ⟨S,h,noZ (Or.inr hw)⟩
      · exact False.elim ((hr.resolve_left hw) (liveWordProper h z hm))
    · exact ⟨S,h,noZ (Or.inl hm)⟩
  · intro hb
    by_cases hm : z ∈ S
    · by_cases hw : z ∈ w
      · exact ⟨k,S,by omega,h,noZ (Or.inr hw)⟩
      · obtain ⟨d,a,b,ha,hb',pa,pb,hab,rfl⟩:=hb
        let U:=S.erase (binWord d a b)
        have ht : LiveWord mask target k t (insert (binWord d a b) U):=by
          simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:=by
          intro v hv
          obtain ⟨hne,hvm⟩:=Finset.mem_erase.mp hv
          simpa [hne] using sub v hvm
        have hf : binWord d a b ∉ insert a (insert b U):=by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb')
          · exact hw (hu _ u)
        exact ⟨k+1,insert a (insert b U),Nat.le_refl _,
          LiveWord.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb' hu)⟩
    · exact ⟨k,S,by omega,h,noZ (Or.inl hm)⟩
  · intro hu_w
    by_cases hm : z ∈ S
    · by_cases hw : z ∈ w
      · exact ⟨k,t,S,by omega,by omega,by omega,by omega,h,noZ (Or.inr hw)⟩
      · obtain ⟨a,ha,pa,rfl⟩:=hu_w
        let U:=S.erase (mask^^^a)
        have ht : LiveWord mask target k t (insert (mask^^^a) U):=by
          simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:=by
          intro v hv
          obtain ⟨hne,hvm⟩:=Finset.mem_erase.mp hv
          simpa [hne] using sub v hvm
        have hf : mask^^^a ∉ insert a U:=by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨k+1,t+1,insert a U,Nat.le_refl _,by omega,Nat.le_refl _,by omega,
          LiveWord.unary pa hf ht,by simpa using And.intro ha hu⟩
    · exact ⟨k,t,S,by omega,by omega,by omega,by omega,h,noZ (Or.inl hm)⟩
theorem xorMaskCut {mask cut a : Word} (sub : mask&&&cut=cut) :
    (mask^^^a)&&&cut=cut^^^(a&&&cut):=by
  apply Nat.eq_of_testBit_eq;intro i
  have h:=congrArg (fun n : Nat=>n.testBit i) sub
  simp only [Nat.testBit_and,Nat.testBit_xor] at h ⊢
  cases hc : cut.testBit i
  · simp
  · simp [hc] at h;simp [h]
theorem binWordCut {cut a b : Word} (d : Bool) :
    binWord d a b&&&cut=binWord d (a&&&cut) (b&&&cut):=by
  apply Nat.eq_of_testBit_eq;intro i
  cases d <;> simp only [binWord,Bool.false_eq_true,ite_true,ite_false,
    Nat.testBit_and,Nat.testBit_or] <;> cases cut.testBit i <;> simp
theorem maskFlatIff (cut w : Word) : maskFlat cut w=true ↔ ¬properWord cut (w&&&cut):=by
  simp only [maskFlat,properWord,Bool.or_eq_true,beq_iff_eq]
  tauto
theorem flatFilterInsertLe (cut a : Word) (U : Finset Word) :
    ((insert a U).filter (fun w=>maskFlat cut w=true)).card ≤
      (U.filter (fun w=>maskFlat cut w=true)).card +
        if maskFlat cut a=true then 1 else 0:=by
  by_cases ha : a ∈ U
  · rw [Finset.insert_eq_of_mem ha];split <;> omega
  · rw [Finset.filter_insert]
    split
    · rw [Finset.card_insert_of_notMem (by simp [ha])]
    · exact Nat.le_refl _
theorem flatFilterInsertEq (cut a : Word) (U : Finset Word) (ha : a ∉ U) :
    ((insert a U).filter (fun w=>maskFlat cut w=true)).card =
      (U.filter (fun w=>maskFlat cut w=true)).card +
        if maskFlat cut a=true then 1 else 0:=by
  rw [Finset.filter_insert]
  split
  · rw [Finset.card_insert_of_notMem (by simp [ha])]
  · omega
theorem properXorCut {cut a : Word} :
    properWord cut (cut^^^a) ↔ properWord cut a:=by
  have cancel : cut^^^(cut^^^a)=a:=by
    apply Nat.eq_of_testBit_eq;intro i;simp only [Nat.testBit_xor]
    cases cut.testBit i <;> cases a.testBit i <;> simp
  have selfZero : cut^^^cut=0:=by
    apply Nat.eq_of_testBit_eq;intro i;simp
  constructor
  · intro ⟨h0,hm⟩
    exact ⟨fun eq=>hm (by rw [eq,Nat.xor_zero]),fun eq=>h0 (by rw [eq,selfZero])⟩
  · intro ⟨h0,hm⟩
    exact ⟨fun eq=>hm (by rw [← cancel,eq,Nat.xor_zero]),fun eq=>h0 (by rw [← cancel,eq,selfZero])⟩
theorem flatBinRep {cut : Word} {wList : List Word} {x y : Word} (d : Bool)
    (hx : x ∈ wList) (hy : y ∈ wList) (mx : Masked cut x) (my : Masked cut y)
    (hflat : ¬properWord cut x ∨ ¬properWord cut y) :
    wordRep cut wList (binWord d x y):=by
  have absorb {u : Word} (mu : Masked cut u) : cut&&&u=u ∧ cut|||u=cut:=by
    constructor
    · rw [Nat.land_comm];exact mu
    · apply Nat.eq_of_testBit_eq;intro i
      have h:=congrArg (fun n : Nat=>n.testBit i) mu
      simp only [Nat.testBit_and,Nat.testBit_or] at h ⊢
      cases hc : cut.testBit i <;> simp_all
  have splitFlat {u : Word} (h : ¬properWord cut u) : u=0 ∨ u=cut:=by
    by_cases h0 : u=0
    · exact Or.inl h0
    · exact Or.inr (by by_contra h1;exact h ⟨h0,h1⟩)
  rcases hflat with hfx | hfy
  · rcases splitFlat hfx with hx0 | hxc
    · rw [hx0];cases d
      · exact Or.inr (by simp [binWord,properWord])
      · exact Or.inl (by simpa [binWord] using hy)
    · rw [hxc];cases d
      · exact Or.inl (by simpa [binWord,(absorb my).1] using hy)
      · exact Or.inr (by simp [binWord,(absorb my).2,properWord])
  · rcases splitFlat hfy with hy0 | hyc
    · rw [hy0];cases d
      · exact Or.inr (by simp [binWord,properWord])
      · exact Or.inl (by simpa [binWord] using hx)
    · rw [hyc];cases d
      · exact Or.inl (by simpa [binWord,Nat.land_comm,(absorb mx).1] using hx)
      · exact Or.inr (by simp [binWord,Nat.lor_comm,(absorb mx).2,properWord])
theorem projectLiveExact {mask cut target : Word} (submask : mask&&&cut=cut)
    (hgoal : properWord cut (target&&&cut)) {k t : Nat} {S : Finset Word}
    (live : LiveWord mask target k t S) :
    ∃ k' t' S',LiveWord cut (target&&&cut) k' t' S' ∧
      t' ≤ t ∧ k'+(S.filter (fun w=>maskFlat cut w=true)).card+(t - t') ≤ k ∧
      ∀ v ∈ S', ∃ w ∈ S,v=w&&&cut:=by
  induction live using LiveWord.ind with
  | stop hp =>
    have hmf : ¬(maskFlat cut target=true):=fun h=>(maskFlatIff cut target).mp h hgoal
    have hfl : (({target} : Finset Word).filter (fun w=>maskFlat cut w=true)).card=0:=by
      simp [hmf]
    exact ⟨0,0,{target&&&cut},LiveWord.stop hgoal,Nat.le_refl _,by omega,
      fun v hv=>⟨target,Finset.mem_singleton_self _,by simpa using hv⟩⟩
  | @unary k t U a ha hfresh tail ih =>
    obtain ⟨k',t',S',hlive,ht,hcard,hsub⟩:=ih
    have hzU : mask^^^a ∉ U:=fun hm=>hfresh (Finset.mem_insert_of_mem hm)
    have hfcChild:=flatFilterInsertEq cut (mask^^^a) U hzU
    have hfcPar:=flatFilterInsertLe cut a U
    have hzeq : (mask^^^a)&&&cut=cut^^^(a&&&cut):=xorMaskCut submask
    have hpropEq : properWord cut ((mask^^^a)&&&cut) ↔ properWord cut (a&&&cut):=by
      rw [hzeq];exact properXorCut
    let wList : List Word:=(insert a U).toList.map (· &&& cut)
    have subList : ∀ v ∈ S',v ∈ wList ++ [(mask^^^a)&&&cut]:=by
      intro v hv;obtain ⟨u,hu,rfl⟩:=hsub v hv
      rcases Finset.mem_insert.mp hu with rfl | huU
      · exact List.mem_append_right _ List.mem_cons_self
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨u,Finset.mem_toList.mpr (Finset.mem_insert_of_mem huU),rfl⟩)
    by_cases hpa : properWord cut (a&&&cut)
    · have hpz : properWord cut ((mask^^^a)&&&cut):=hpropEq.mpr hpa
      have hma : ¬(maskFlat cut a=true):=fun h=>(maskFlatIff cut a).mp h hpa
      have hmz : ¬(maskFlat cut (mask^^^a)=true):=fun h=>(maskFlatIff cut (mask^^^a)).mp h hpz
      have haMem : a&&&cut ∈ wList :=
        List.mem_map.mpr ⟨a,Finset.mem_toList.mpr (Finset.mem_insert_self a U),rfl⟩
      obtain ⟨k2,t2,S2,hk2,_,ht2,hsum2,hl2,hsub2⟩ :=
        (pullWordExact hlive subList).2.2 ⟨a&&&cut,haMem,hpa,hzeq⟩
      refine ⟨k2,t2,S2,hl2,by omega, ?_, ?_⟩
      · simp only [hma,hmz,Bool.false_eq_true, ↓reduceIte] at hfcChild hfcPar;omega
      · intro v hv;obtain ⟨u,hu,rfl⟩:=List.mem_map.mp (hsub2 v hv);exact ⟨u,Finset.mem_toList.mp hu,rfl⟩
    · have hpz : ¬properWord cut ((mask^^^a)&&&cut):=fun h=>hpa (hpropEq.mp h)
      have hma : maskFlat cut a=true:=(maskFlatIff cut a).mpr hpa
      have hmz : maskFlat cut (mask^^^a)=true:=(maskFlatIff cut (mask^^^a)).mpr hpz
      obtain ⟨S2,hl2,hsub2⟩:=(pullWordExact hlive subList).1 (Or.inr hpz)
      refine ⟨k',t',S2,hl2,by omega, ?_, ?_⟩
      · simp only [hma,hmz, ↓reduceIte] at hfcChild hfcPar;omega
      · intro v hv;obtain ⟨u,hu,rfl⟩:=List.mem_map.mp (hsub2 v hv);exact ⟨u,Finset.mem_toList.mp hu,rfl⟩
  | @binary k t U a b d pa pb hab hfresh tail ih =>
    obtain ⟨k',t',S',hlive,ht,hcard,hsub⟩:=ih
    have hzU : binWord d a b ∉ U:=fun hm=>hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have hfcChild:=flatFilterInsertEq cut (binWord d a b) U hzU
    have hfcPar1:=flatFilterInsertLe cut a (insert b U)
    have hfcPar2:=flatFilterInsertLe cut b U
    let wList : List Word:=(insert a (insert b U)).toList.map (· &&& cut)
    have subList : ∀ v ∈ S',v ∈ wList ++ [binWord d a b&&&cut]:=by
      intro v hv;obtain ⟨u,hu,rfl⟩:=hsub v hv
      rcases Finset.mem_insert.mp hu with rfl | huU
      · exact List.mem_append_right _ List.mem_cons_self
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨u,Finset.mem_toList.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem huU)),rfl⟩)
    have hzeq : binWord d a b&&&cut=binWord d (a&&&cut) (b&&&cut):=binWordCut d
    have haMem : a&&&cut ∈ wList :=
      List.mem_map.mpr ⟨a,Finset.mem_toList.mpr (Finset.mem_insert_self a _),rfl⟩
    have hbMem : b&&&cut ∈ wList :=
      List.mem_map.mpr ⟨b,Finset.mem_toList.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self b _)),rfl⟩
    have finishSub : ∀ {S2 : Finset Word},(∀ v ∈ S2,v ∈ wList) →
        ∀ v ∈ S2, ∃ w ∈ insert a (insert b U),v=w&&&cut:=by
      intro S2 hs2 v hv;obtain ⟨u,hu,rfl⟩:=List.mem_map.mp (hs2 v hv);exact ⟨u,Finset.mem_toList.mp hu,rfl⟩
    by_cases hpa : properWord cut (a&&&cut)
    · have hma : ¬(maskFlat cut a=true):=fun h=>(maskFlatIff cut a).mp h hpa
      by_cases hpb : properWord cut (b&&&cut)
      · have hmb : ¬(maskFlat cut b=true):=fun h=>(maskFlatIff cut b).mp h hpb
        by_cases heq : a&&&cut=b&&&cut
        · have hrep : wordRep cut wList (binWord d a b&&&cut):=by
            rw [hzeq,heq];cases d <;> exact Or.inl (by simpa [binWord] using hbMem)
          obtain ⟨S2,hl2,hsub2⟩:=(pullWordExact hlive subList).1 hrep
          refine ⟨k',t',S2,hl2,ht, ?_,finishSub hsub2⟩
          simp only [hma,hmb,Bool.false_eq_true, ↓reduceIte] at hfcChild hfcPar1 hfcPar2
          by_cases hmz : maskFlat cut (binWord d a b)=true <;> simp [hmz] at hfcChild <;> omega
        · have hbin : binaryWitness cut wList (binWord d a b&&&cut) :=
            ⟨d,a&&&cut,b&&&cut,haMem,hbMem,hpa,hpb,heq,hzeq⟩
          obtain ⟨k2,S2,hk2,hl2,hsub2⟩:=(pullWordExact hlive subList).2.1 hbin
          refine ⟨k2,t',S2,hl2,ht, ?_,finishSub hsub2⟩
          simp only [hma,hmb,Bool.false_eq_true, ↓reduceIte] at hfcChild hfcPar1 hfcPar2
          by_cases hmz : maskFlat cut (binWord d a b)=true <;> simp [hmz] at hfcChild <;> omega
      · have hmb : maskFlat cut b=true:=(maskFlatIff cut b).mpr hpb
        have hrep : wordRep cut wList (binWord d a b&&&cut):=by
          rw [hzeq];exact flatBinRep d haMem hbMem (by simp [Masked]) (by simp [Masked]) (Or.inr hpb)
        obtain ⟨S2,hl2,hsub2⟩:=(pullWordExact hlive subList).1 hrep
        refine ⟨k',t',S2,hl2,ht, ?_,finishSub hsub2⟩
        simp only [hma,hmb,Bool.false_eq_true, ↓reduceIte] at hfcChild hfcPar1 hfcPar2
        by_cases hmz : maskFlat cut (binWord d a b)=true <;> simp [hmz] at hfcChild <;> omega
    · have hma : maskFlat cut a=true:=(maskFlatIff cut a).mpr hpa
      by_cases hpb : properWord cut (b&&&cut)
      · have hmb : ¬(maskFlat cut b=true):=fun h=>(maskFlatIff cut b).mp h hpb
        have hrep : wordRep cut wList (binWord d a b&&&cut):=by
          rw [hzeq];exact flatBinRep d haMem hbMem (by simp [Masked]) (by simp [Masked]) (Or.inl hpa)
        obtain ⟨S2,hl2,hsub2⟩:=(pullWordExact hlive subList).1 hrep
        refine ⟨k',t',S2,hl2,ht, ?_,finishSub hsub2⟩
        simp only [hma,hmb,Bool.false_eq_true, ↓reduceIte] at hfcChild hfcPar1 hfcPar2
        by_cases hmz : maskFlat cut (binWord d a b)=true <;> simp [hmz] at hfcChild <;> omega
      · have hmb : maskFlat cut b=true:=(maskFlatIff cut b).mpr hpb
        have hrep : wordRep cut wList (binWord d a b&&&cut):=by
          rw [hzeq];exact flatBinRep d haMem hbMem (by simp [Masked]) (by simp [Masked]) (Or.inl hpa)
        have hpz : ¬properWord cut (binWord d a b&&&cut):=by
          rw [hzeq]
          have ha0 : a&&&cut=0 ∨ a&&&cut=cut:=by
            by_cases h0 : a&&&cut=0
            · exact Or.inl h0
            · exact Or.inr (by by_contra h1;exact hpa ⟨h0,h1⟩)
          have hb0 : b&&&cut=0 ∨ b&&&cut=cut:=by
            by_cases h0 : b&&&cut=0
            · exact Or.inl h0
            · exact Or.inr (by by_contra h1;exact hpb ⟨h0,h1⟩)
          rcases ha0 with h1 | h1 <;> rcases hb0 with h2 | h2 <;> cases d <;>
            simp [h1,h2,binWord,properWord]
        have hmz : maskFlat cut (binWord d a b)=true:=(maskFlatIff cut (binWord d a b)).mpr hpz
        obtain ⟨S2,hl2,hsub2⟩:=(pullWordExact hlive subList).1 hrep
        refine ⟨k',t',S2,hl2,ht, ?_,finishSub hsub2⟩
        simp only [hma,hmb,hmz, ↓reduceIte] at hfcChild hfcPar1 hfcPar2;omega
theorem flatCountEqFilter (cut : Word) {ws : List Word} (nd : ws.Nodup) :
    flatCount cut ws=(ws.toFinset.filter (fun w=>maskFlat cut w=true)).card:=by
  induction ws with
  | nil=>rfl
  | cons w ws ih =>
    have hnd:=List.nodup_cons.mp nd
    have hw : w ∉ ws.toFinset:=by simpa using hnd.1
    change (if maskFlat cut w then flatCount cut ws+1 else flatCount cut ws)=_
    rw [List.toFinset_cons,flatFilterInsertEq cut w ws.toFinset hw,ih hnd.2]
    cases maskFlat cut w <;> simp
theorem liveInjImage {m1 m2 g1 g2 : Word} (f : Word → Word)
    (h0 : f 0=0) (hm : f m1=m2)
    (hxor : ∀ a,f (m1^^^a)=m2^^^f a)
    (hand : ∀ a b,f (a&&&b)=f a&&&f b)
    (hor : ∀ a b,f (a|||b)=f a|||f b)
    (hgoal : f g1=g2)
    (hinj : ∀ a b,Masked m1 a → Masked m1 b → f a=f b → a=b)
    {k t : Nat} {S : Finset Word} (live : LiveWord m1 g1 k t S)
    (hM : ∀ w ∈ S,Masked m1 w) :
    LiveWord m2 g2 k t (S.image f):=by
  have hprop {a : Word} (ma : Masked m1 a) (pa : properWord m1 a) : properWord m2 (f a) :=
    ⟨fun eq=>pa.1 (hinj a 0 ma (by simp [Masked]) (eq.trans h0.symm)),
     fun eq=>pa.2 (hinj a m1 ma (by simp [Masked]) (eq.trans hm.symm))⟩
  have hfresh {T : Finset Word} {v : Word} (hv : v ∉ T) (mv : Masked m1 v)
      (mT : ∀ w ∈ T,Masked m1 w) : f v ∉ T.image f:=by
    intro hmem;obtain ⟨w,hw,eq⟩:=Finset.mem_image.mp hmem
    exact hv (hinj w v (mT w hw) mv eq ▸ hw)
  induction live using LiveWord.ind with
  | stop hp =>
    rw [Finset.image_singleton,hgoal]
    exact LiveWord.stop (hgoal ▸ hprop (hM g1 (Finset.mem_singleton_self g1)) hp)
  | @unary k t U a pa fresh tail ih =>
    let v:=m1^^^a
    have ma:=hM a (Finset.mem_insert_self a U)
    have mv : Masked m1 v:=maskedGate (bank:=[a]) (by simpa using ma) (Or.inl ⟨a,Or.inr (Or.inr (by simp)),rfl⟩)
    have hnew : ∀ w ∈ insert v U,Masked m1 w:=fun w hw=>by
      rcases Finset.mem_insert.mp hw with rfl | hU
      · exact mv
      · exact hM w (Finset.mem_insert_of_mem hU)
    have ht:=ih hnew
    have hf:=hfresh fresh mv hM
    rw [Finset.image_insert,hxor a] at ht hf
    rw [Finset.image_insert]
    exact LiveWord.unary (hprop ma pa) hf ht
  | @binary k t U a b d pa pb hab fresh tail ih =>
    let v:=binWord d a b
    have ma:=hM a (Finset.mem_insert_self a _)
    have mb:=hM b (Finset.mem_insert_of_mem (Finset.mem_insert_self b U))
    have mv : Masked m1 v:=maskedGate (bank:=[a,b]) (by simpa using And.intro ma mb)
      (Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by cases d <;> simp [v,binWord]⟩)
    have hnew : ∀ w ∈ insert v U,Masked m1 w:=fun w hw=>by
      rcases Finset.mem_insert.mp hw with rfl | hU
      · exact mv
      · exact hM w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have hfv : f v=binWord d (f a) (f b):=by cases d <;> simp [v,binWord,hand,hor]
    have ht:=ih hnew
    have hf:=hfresh fresh mv hM
    rw [Finset.image_insert,hfv] at ht
    rw [Finset.image_insert,Finset.image_insert,hfv] at hf
    rw [Finset.image_insert,Finset.image_insert]
    exact LiveWord.binary (hprop ma pa) (hprop mb pb) (fun h=>hab (hinj a b ma mb h)) hf ht
theorem exactLowerInjMap {m1 m2 g1 g2 t min : Nat} {s1 s2 : List Word} (f : Word → Word)
    (h0 : f 0=0) (hm : f m1=m2)
    (hxor : ∀ a,f (m1^^^a)=m2^^^f a)
    (hand : ∀ a b,f (a&&&b)=f a&&&f b)
    (hor : ∀ a b,f (a|||b)=f a|||f b)
    (hgoal : f g1=g2)
    (hinj : ∀ a b,Masked m1 a → Masked m1 b → f a=f b → a=b)
    (s1M : ∀ w ∈ s1,Masked m1 w)
    (sup : ∀ w ∈ s1,AvailableWord m2 s2 (f w))
    (hlow : ExactLower m2 s2 g2 t min) :
    ExactLower m1 s1 g1 t min:=by
  intro k S hlive hS
  have hSM : ∀ w ∈ S,Masked m1 w:=fun w hw=>maskedAvailable s1M (hS w hw)
  have hl2:=liveInjImage f h0 hm hxor hand hor hgoal hinj hlive hSM
  have hS2 : ∀ v ∈ S.image f,AvailableWord m2 s2 v:=by
    intro v hv;obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hv
    rcases hS w hw with rfl | rfl | hmem
    · exact Or.inl h0
    · exact Or.inr (Or.inl hm)
    · exact sup w hmem
  exact hlow k (S.image f) hl2 hS2
theorem exactLowerRelabel {rows : Nat} (select inv : Fin rows → Fin rows)
    {m1 m2 g1 g2 t min : Nat} {s1 s2 : List Word}
    (check : decide ((∀ i,select (inv i)=i) ∧
      (m1&&&fullMask rows=m1) ∧
      relabel select m1=m2 ∧ relabel select g1=g2 ∧
      s1.all (fun w=>w&&&m1==w)=true ∧
      s1.all (fun w=>availableB m2 s2 (relabel select w))=true)=true)
    (hlow : ExactLower m2 s2 g2 t min) :
    ExactLower m1 s1 g1 t min:=by
  obtain ⟨hsurj,bm,hm,hg,s1M,sup⟩:=of_decide_eq_true check
  have onto : Function.Surjective select:=fun y=>⟨inv y,hsurj y⟩
  have hinj : ∀ a b,Masked m1 a → Masked m1 b → relabel select a=relabel select b → a=b :=
    fun a b ma mb eq=>relabelInj select onto (maskedBelow bm ma) (maskedBelow bm mb) eq
  exact exactLowerInjMap (relabel select) (relabelZero select) hm
    (fun a=>by rw [relabelXor,hm]) (relabelAnd select) (relabelOr select) hg hinj
    (fun w hw=>beq_iff_eq.mp (List.all_eq_true.mp s1M w hw))
    (fun w hw=>availableB_spec.mp (List.all_eq_true.mp sup w hw)) hlow
def exProject {rows m : Nat} (source : Fin m → Fin rows) (w : Word) : Word :=
 pointWord fun i=>w.testBit (source i).val
theorem exactLowerProjectInj {rows m : Nat} (source : Fin m → Fin rows)
    {m1 m2 : Word} {s1 s2 : List Word} {g1 g2 t min : Nat}
    (check : decide ((m1&&&fullMask rows=m1) ∧
      (∀ r : Fin rows,m1.testBit r.val=true → ∃ i : Fin m,source i=r) ∧
      exProject source m1=m2 ∧ exProject source g1=g2 ∧
      s1.all (fun w=>w&&&m1==w)=true ∧
      s1.all (fun w=>availableB m2 s2 (exProject source w))=true)=true)
    (hlow : ExactLower m2 s2 g2 t min) :
    ExactLower m1 s1 g1 t min:=by
  obtain ⟨bm,hsurj,hm,hg,s1M,sup⟩:=of_decide_eq_true check
  let f:=exProject source
  have hz : f 0=0:=by simpa only [f,exProject,Nat.zero_testBit] using (pointZero (rows:=m))
  have hand (a b : Word) : f (a&&&b)=f a&&&f b:=by
    simp only [f,exProject,Nat.testBit_and,pointWord,encodeAnd,BitVec.toNat_and]
  have hor (a b : Word) : f (a|||b)=f a|||f b:=by
    simp only [f,exProject,Nat.testBit_or,pointWord,encodeOr,BitVec.toNat_or]
  have hxor (a : Word) : f (m1^^^a)=m2^^^f a:=by
    have hx : encodePoint (fun i : Fin m=>(m1^^^a).testBit (source i).val) =
        encodePoint (fun i : Fin m=>m1.testBit (source i).val) ^^^
        encodePoint (fun i : Fin m=>a.testBit (source i).val):=by
      apply BitVec.eq_of_getLsbD_eq;intro i hi
      rw [BitVec.getLsbD_xor,encodeBit _ ⟨i,hi⟩,encodeBit _ ⟨i,hi⟩,encodeBit _ ⟨i,hi⟩]
      exact Nat.testBit_xor _ _ _
    have h2 : f (m1^^^a)=f m1^^^f a:=by
      simpa only [f,exProject,pointWord,BitVec.toNat_xor] using congrArg BitVec.toNat hx
    rw [h2];exact congrArg (· ^^^ f a) hm
  have hinj : ∀ a b,Masked m1 a → Masked m1 b → f a=f b → a=b:=by
    intro a b ma mb eq
    apply Nat.eq_of_testBit_eq;intro r
    by_cases hmr : m1.testBit r=true
    · have hrlt : r < rows:=by
        by_contra! big
        have eb:=congrArg (fun n : Nat=>n.testBit r) bm
        simp [fullMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,hmr,Nat.not_lt.mpr big] at eb
      obtain ⟨i,hi⟩:=hsurj ⟨r,hrlt⟩ hmr
      have hbit:=congrArg (fun n : Nat=>n.testBit i.val) eq
      simp only [f,exProject,pointWord,BitVec.testBit_toNat,i.isLt,decide_true,Bool.true_and,encodeBit,hi] at hbit
      exact hbit
    · have ea:=congrArg (fun n : Nat=>n.testBit r) ma
      have eb:=congrArg (fun n : Nat=>n.testBit r) mb
      simp [Masked,Nat.testBit_and,hmr] at ea eb
      rw [ea,eb]
  exact exactLowerInjMap f hz hm hxor hand hor hg hinj
    (fun w hw=>beq_iff_eq.mp (List.all_eq_true.mp s1M w hw))
    (fun w hw=>availableB_spec.mp (List.all_eq_true.mp sup w hw)) hlow
def dagForceWord1 {α : Type} (word : Word) (cont : Word → α) : α :=
 Nat.rec (cont 0) (fun k _=>cont (k+1)) word
theorem dagForceWord1Eq {α : Type} (word : Word) (cont : Word → α) :
    dagForceWord1 word cont=cont word:=by cases word <;> rfl
def dagForceWords1 (words : List Word) (cont : List Word → Bool) : Bool :=
 (List.rec (motive:=fun _=>(List Word → Bool) → Bool) (fun k=>k [])
 (fun w _ next k=>dagForceWord1 w (fun v=>next (fun rest=>k (v :: rest)))) words) cont
theorem dagForceWords1Eq (words : List Word) (cont : List Word → Bool) :
    dagForceWords1 words cont=cont words:=by
  induction words generalizing cont with
  | nil=>rfl
  | cons w ws ih =>
    change dagForceWord1 w (fun v=>dagForceWords1 ws (fun rest=>cont (v :: rest)))=_
    rw [dagForceWord1Eq,ih]
def recipeGateBin (mask : Nat) (bank : List Word) (v a b : Word) : Bool :=
  availableB mask bank a&&availableB mask bank b&&(v==(a&&&b)||v==(a|||b))
def replayRecipesExact (mask : Nat) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) (notsLeft : Nat) : List Word × Nat :=
  (List.rec (motive:=fun _=>List Word → Nat → List Word × Nat) (fun _ _=>([],0))
    (fun (w,a,b) _ next bank nl =>
      dagForceWord1 (w&&&mask) fun v =>
        if needed.contains v && !availableB mask bank v then
          dagForceWord1 (a&&&mask) fun am =>
            dagForceWord1 (b&&&mask) fun bm =>
              if recipeGateBin mask bank v am bm then
                let r:=next (v :: bank) nl
                (v :: r.1,r.2)
              else if nl > 0&&availableB mask bank am&&v==(mask^^^am) then
                let r:=next (v :: bank) (nl - 1)
                (v :: r.1,r.2+1)
              else next bank nl
        else next bank nl) recipes) bank notsLeft
theorem pullReplayExact {mask goal : Word} {needed : List Word}
    {recipes : List (Word × Word × Word)} {bank : List Word} {nl k t : Nat} {S : Finset Word}
    (bankM : ∀ w ∈ bank,Masked mask w)
    (hlive : LiveWord mask goal k t S)
    (hsub : ∀ w ∈ S,w ∈ (replayRecipesExact mask needed recipes bank nl).1 ++ bank) :
    ∃ k' t' S',
      k'+(t+(replayRecipesExact mask needed recipes bank nl).2 - t') ≤
        k+(replayRecipesExact mask needed recipes bank nl).1.length ∧
      (replayRecipesExact mask needed recipes bank nl).2 ≤ nl ∧
      t ≤ t' ∧ t' ≤ t+(replayRecipesExact mask needed recipes bank nl).2 ∧
      LiveWord mask goal k' t' S' ∧ ∀ w ∈ S',w ∈ bank:=by
  induction recipes generalizing bank nl k t S with
  | nil =>
    exact ⟨k,t,S,by simp [replayRecipesExact],Nat.zero_le _,Nat.le_refl _,by simp [replayRecipesExact],hlive,by simpa [replayRecipesExact] using hsub⟩
  | cons rec rest ih =>
    obtain ⟨w,a,b⟩:=rec
    let v:=w&&&mask
    let am:=a&&&mask
    let bm:=b&&&mask
    have hstep : replayRecipesExact mask needed ((w,a,b) :: rest) bank nl =
      if needed.contains v && !availableB mask bank v then
        if recipeGateBin mask bank v am bm then
          let r:=replayRecipesExact mask needed rest (v :: bank) nl
          (v :: r.1,r.2)
        else if nl > 0&&availableB mask bank am&&v==(mask^^^am) then
          let r:=replayRecipesExact mask needed rest (v :: bank) (nl - 1)
          (v :: r.1,r.2+1)
        else replayRecipesExact mask needed rest bank nl
      else replayRecipesExact mask needed rest bank nl:=by
      change dagForceWord1 v (fun v=>if needed.contains v && !availableB mask bank v then
        dagForceWord1 am (fun am=>dagForceWord1 bm (fun bm =>
          if recipeGateBin mask bank v am bm then
            let r:=replayRecipesExact mask needed rest (v :: bank) nl
            (v :: r.1,r.2)
          else if nl > 0&&availableB mask bank am&&v==(mask^^^am) then
            let r:=replayRecipesExact mask needed rest (v :: bank) (nl - 1)
            (v :: r.1,r.2+1)
          else replayRecipesExact mask needed rest bank nl))
        else replayRecipesExact mask needed rest bank nl)=_
      simp only [dagForceWord1Eq]
    rw [hstep] at hsub ⊢
    by_cases hcond : (needed.contains v && !availableB mask bank v)=true
    · rw [if_pos hcond] at hsub ⊢
      by_cases hbin : recipeGateBin mask bank v am bm=true
      · rw [if_pos hbin] at hsub ⊢
        dsimp only at hsub ⊢
        have bankM' : ∀ u ∈ v :: bank,Masked mask u:=fun u hu=>by
          rcases List.mem_cons.mp hu with rfl | hu
          · simp [v,Masked]
          · exact bankM u hu
        have hsub' : ∀ u ∈ S,u ∈ (replayRecipesExact mask needed rest (v :: bank) nl).1 ++ (v :: bank):=by
          intro u hu
          have hm:=hsub u hu
          simp only [List.mem_append,List.mem_cons] at hm ⊢
          rcases hm with (huv | h1) | h2
          · exact Or.inr (Or.inl huv)
          · exact Or.inl h1
          · exact Or.inr (Or.inr h2)
        obtain ⟨k1,t1,S1,hk1,hu1,ht1lo,ht1,hl1,hs1⟩:=ih bankM' hlive hsub'
        have hs1' : ∀ u ∈ S1,u ∈ bank ++ [v]:=fun u hu=>by simpa [or_comm] using hs1 u hu
        simp only [recipeGateBin,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,availableB_spec] at hbin
        obtain ⟨⟨ham,hbm⟩,hveq⟩:=hbin
        have hcls : wordRep mask bank v ∨ binaryWitness mask bank v:=by
          rcases hveq with hv | hv
          · rw [hv];exact classifyBinary bankM false ham hbm
          · rw [hv];exact classifyBinary bankM true ham hbm
        rcases hcls with hrep | hbw
        · obtain ⟨S2,hl2,hs2⟩:=(pullWordExact hl1 hs1').1 hrep
          exact ⟨k1,t1,S2,by simp only [List.length_cons];omega,hu1,ht1lo,ht1,hl2,hs2⟩
        · obtain ⟨k2,S2,hk2,hl2,hs2⟩:=(pullWordExact hl1 hs1').2.1 hbw
          exact ⟨k2,t1,S2,by simp only [List.length_cons];omega,hu1,ht1lo,ht1,hl2,hs2⟩
      · rw [if_neg hbin] at hsub ⊢
        by_cases hun : (nl > 0&&availableB mask bank am&&(v==mask^^^am))=true
        · rw [if_pos hun] at hsub ⊢
          dsimp only at hsub ⊢
          have bankM' : ∀ u ∈ v :: bank,Masked mask u:=fun u hu=>by
            rcases List.mem_cons.mp hu with rfl | hu
            · simp [v,Masked]
            · exact bankM u hu
          have hsub' : ∀ u ∈ S,u ∈ (replayRecipesExact mask needed rest (v :: bank) (nl - 1)).1 ++ (v :: bank):=by
            intro u hu
            have hm:=hsub u hu
            simp only [List.mem_append,List.mem_cons] at hm ⊢
            rcases hm with (huv | h1) | h2
            · exact Or.inr (Or.inl huv)
            · exact Or.inl h1
            · exact Or.inr (Or.inr h2)
          obtain ⟨k1,t1,S1,hk1,hu1,ht1lo,ht1,hl1,hs1⟩:=ih bankM' hlive hsub'
          have hs1' : ∀ u ∈ S1,u ∈ bank ++ [v]:=fun u hu=>by simpa [or_comm] using hs1 u hu
          simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,availableB_spec] at hun
          obtain ⟨⟨hnl,ham⟩,hveq⟩:=hun
          have hcls : wordRep mask bank v ∨ (∃ a ∈ bank,properWord mask a ∧ v=mask^^^a):=by
            by_cases ha0 : am=0
            · exact Or.inl (Or.inr (by simp [hveq,ha0,properWord]))
            by_cases ham2 : am=mask
            · have hself : mask^^^mask=0:=by apply Nat.eq_of_testBit_eq;intro i;simp
              exact Or.inl (Or.inr (by simp [hveq,ham2,hself,properWord]))
            exact Or.inr ⟨am,(ham.resolve_left ha0).resolve_left ham2,⟨ha0,ham2⟩,hveq⟩
          rcases hcls with hrep | huw
          · obtain ⟨S2,hl2,hs2⟩:=(pullWordExact hl1 hs1').1 hrep
            exact ⟨k1,t1,S2,by simp only [List.length_cons];omega,by omega,ht1lo,by omega,hl2,hs2⟩
          · obtain ⟨k2,t2,S2,hk2,ht2lo,ht2,hsum2,hl2,hs2⟩:=(pullWordExact hl1 hs1').2.2 huw
            exact ⟨k2,t2,S2,by simp only [List.length_cons];omega,by omega,by omega,by omega,hl2,hs2⟩
        · rw [if_neg hun] at hsub ⊢
          exact ih bankM hlive hsub
    · rw [if_neg hcond] at hsub ⊢
      exact ih bankM hlive hsub
abbrev RowState1:=Nat × Nat × List Word × List (Word × Word × Word)
abbrev CutCheck1:=RowState1 → Bool
def exactBoundCloses (allowNotInPast : Bool) (target : Word) (state : RowState1) (bound : ExactBound) : Bool :=
  let (cut,stock,lower0,lower1,goal):=bound
  let (fuel,nots,ws,history):=state
  let lower1Eff:=min lower1 (lower0+1)
  let maxLower :=
    if nots==1 then lower1Eff
    else if allowNotInPast then max lower0 lower1Eff
    else lower0
  let nl:=if nots==0&&allowNotInPast then 1 else 0
  (target&&&cut)==goal&&goal != 0&&goal != cut &&
    dagForceWord1 (fuel - flatCount cut ws) (fun remaining =>
      if Nat.blt remaining maxLower then
        dagForceWords1 (recipeStart cut stock ws) (fun start =>
          if Nat.blt (start.length+remaining) maxLower then
            dagForceWords1 (recipeClosure cut stock history start) (fun needed =>
              if Nat.blt (needed.length+remaining) maxLower then
                let res:=replayRecipesExact cut needed history.reverse stock nl
                dagForceWords1 res.1 (fun replay =>
                  let effLower:=if nots==1||res.2 != 0 then lower1Eff else lower0
                  Nat.blt (replay.length+remaining) effLower &&
                    ws.all (fun w=>availableB cut (replay ++ stock) (w&&&cut)))
              else false)
          else false)
      else false)
def exactKnownCloses (allowNotInPast : Bool) (target : Word) (bounds : List ExactBound) (state : RowState1) : Bool :=
  List.rec false (fun bound _ later=>exactBoundCloses allowNotInPast target state bound||later) bounds
def WordViable1 (mask target : Word) (state : RowState1) : Prop :=
 state.2.2.1.Nodup ∧ ∃ k,k ≤ state.1 ∧ LiveWord mask target k state.2.1 state.2.2.1.toFinset
theorem exactBoundClosesSound {allowNotInPast : Bool} {mask target : Word}
    {state : RowState1} {bound : ExactBound}
    (h0 : ExactLower bound.1 bound.2.1 bound.2.2.2.2 0 bound.2.2.1)
    (h1 : ExactLower bound.1 bound.2.1 bound.2.2.2.2 1 bound.2.2.2.1)
    (submask : mask&&&bound.1=bound.1)
    (stockM : ∀ w ∈ bound.2.1,Masked bound.1 w)
    (hnots : state.2.1 ≤ 1)
    (viable : WordViable1 mask target state) :
    exactBoundCloses allowNotInPast target state bound=false:=by
  rcases state with ⟨fuel,nots,ws,history⟩
  rcases bound with ⟨cut,stock,lower0,lower1,goal⟩
  dsimp only at h0 h1 submask stockM hnots viable
  obtain ⟨nd,k,hk,live⟩:=viable
  change ws.Nodup at nd
  change k ≤ fuel at hk
  change LiveWord mask target k nots ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  unfold exactBoundCloses at hc
  dsimp only at hc
  generalize hmaxL : (if nots==1 then min lower1 (lower0+1) else if allowNotInPast then max lower0 (min lower1 (lower0+1)) else lower0)=maxL at hc
  generalize hnl : (if nots==0&&allowNotInPast then 1 else 0)=nl at hc
  simp only [dagForceWord1Eq,dagForceWords1Eq,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,Nat.blt_eq] at hc
  obtain ⟨⟨⟨goalEq,nz⟩,nf⟩,scan⟩:=hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨hlen,hsrc⟩
  rw [Nat.blt_eq] at hlen
  have hpg : properWord cut (target&&&cut):=by rw [goalEq];exact ⟨nz,nf⟩
  obtain ⟨k',t',S',hlive',ht',hcard',hsub'⟩:=projectLiveExact submask hpg live
  rw [← flatCountEqFilter cut nd] at hcard'
  let res:=replayRecipesExact cut (recipeClosure cut stock history (recipeStart cut stock ws)) history.reverse stock nl
  have hS'mem : ∀ v ∈ S',v ∈ res.1 ++ stock:=by
    intro v hv
    obtain ⟨w,hw,rfl⟩:=hsub' v hv
    have hav:=availableB_spec.mp (List.all_eq_true.mp hsrc w (List.mem_toFinset.mp hw))
    have hpv:=liveWordProper hlive' (w&&&cut) hv
    exact (hav.resolve_left hpv.1).resolve_left hpv.2
  rw [goalEq] at hlive'
  obtain ⟨k2,t2,S2,hk2,huLe,ht2lo,ht2,hlive2,hsub2⟩:=pullReplayExact stockM hlive' hS'mem
  have hS2av : ∀ w ∈ S2,AvailableWord cut stock w:=fun w hw=>Or.inr (Or.inr (hsub2 w hw))
  change res.1.length+(fuel - flatCount cut ws) < (if (nots==1||res.2 != 0)=true then min lower1 (lower0+1) else lower0) at hlen
  change res.2 ≤ nl at huLe
  change k2+(t'+res.2 - t2) ≤ k'+res.1.length at hk2
  change t2 ≤ t'+res.2 at ht2
  by_cases hn1 : nots=1
  · subst hn1
    have hnl0 : nl=0:=by rw [← hnl];rfl
    have hu0 : res.2=0:=by omega
    simp only [beq_self_eq_true,Bool.true_or, ↓reduceIte] at hlen
    have ht2' : t2=t':=by omega
    rw [ht2'] at hlive2
    have hcases : t'=0 ∨ t'=1:=by omega
    rcases hcases with rfl | rfl
    · have hl:=h0 k2 S2 hlive2 hS2av
      have : min lower1 (lower0+1) ≤ lower0+1:=Nat.min_le_right _ _
      omega
    · have hl:=h1 k2 S2 hlive2 hS2av
      have : min lower1 (lower0+1) ≤ lower1:=Nat.min_le_left _ _
      omega
  · have hn0 : nots=0:=by omega
    subst hn0
    have ht'0 : t'=0:=by omega
    subst ht'0
    by_cases hu0 : res.2=0
    · simp only [hu0,bne_self_eq_false,Bool.or_false,beq_iff_eq,zero_ne_one, ↓reduceIte] at hlen
      have ht20 : t2=0:=by omega
      subst ht20
      have hl:=h0 k2 S2 hlive2 hS2av
      omega
    · have hbne : (res.2 != 0)=true:=bne_iff_ne.mpr hu0
      simp only [hbne,Bool.or_true, ↓reduceIte] at hlen
      have hnlLe : nl ≤ 1:=by rw [← hnl];cases allowNotInPast <;> decide
      have hu1 : res.2=1:=by omega
      have ht2c : t2=0 ∨ t2=1:=by omega
      rcases ht2c with rfl | rfl
      · have hl:=h0 k2 S2 hlive2 hS2av
        have : min lower1 (lower0+1) ≤ lower0+1:=Nat.min_le_right _ _
        omega
      · have hl:=h1 k2 S2 hlive2 hS2av
        have : min lower1 (lower0+1) ≤ lower1:=Nat.min_le_left _ _
        omega
theorem exactKnownClosesSound {allowNotInPast : Bool} {mask target : Word}
    {bounds : List ExactBound} {state : RowState1}
    (known : ExactKnown bounds)
    (submasks : ∀ b ∈ bounds,mask&&&b.1=b.1)
    (stocksM : ∀ b ∈ bounds, ∀ w ∈ b.2.1,Masked b.1 w)
    (hnots : state.2.1 ≤ 1)
    (viable : WordViable1 mask target state) :
    exactKnownCloses allowNotInPast target bounds state=false:=by
  induction bounds with
  | nil=>rfl
  | cons b bs ih =>
    change (exactBoundCloses allowNotInPast target state b ||
      exactKnownCloses allowNotInPast target bs state)=false
    have hb:=known b List.mem_cons_self
    rw [exactBoundClosesSound hb.1 hb.2 (submasks b List.mem_cons_self)
      (stocksM b List.mem_cons_self) hnots viable]
    exact ih (fun x hx=>known x (List.mem_cons_of_mem _ hx))
      (fun x hx=>submasks x (List.mem_cons_of_mem _ hx))
      (fun x hx=>stocksM x (List.mem_cons_of_mem _ hx))
theorem chartBitsLt (w : Nat) (l : List Nat) : chartBits w l < 2 ^ l.length:=by
  induction l with
  | nil=>simp [chartBits]
  | cons r rs ih =>
    change (((w>>>r)&&&1)|||(chartBits w rs<<<1)) < 2 ^ (rs.length+1)
    have hb : ((w>>>r)&&&1) < 2:=by
      rw [show (1 : Nat)=2 ^ 1 - 1 from rfl,Nat.and_two_pow_sub_one_eq_mod,Nat.pow_one]
      exact Nat.mod_lt _ (by decide)
    have heq : (((w>>>r)&&&1)|||(chartBits w rs<<<1))=((w>>>r)&&&1)+2*chartBits w rs:=by
      apply Nat.eq_of_testBit_eq;intro j
      rw [Nat.testBit_or,Nat.testBit_shiftLeft]
      cases j with
      | zero =>
        simp [Nat.testBit_zero,Nat.add_mod,Nat.mul_mod_right]
      | succ j =>
        have h0 : ((w>>>r)&&&1).testBit (j+1)=false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (n:=2) (by decide) (show 1 ≤ j+1 by omega)))
        have hd : (((w>>>r)&&&1)+2*chartBits w rs) / 2=chartBits w rs:=by
          have : ((w>>>r)&&&1) / 2=0:=Nat.div_eq_of_lt hb
          rw [Nat.add_mul_div_left _ _ (by decide),this,Nat.zero_add]
        rw [h0,Bool.false_or,Nat.testBit_succ,hd];simp
    rw [heq,Nat.pow_succ,Nat.add_comm]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hb _) (by
      rw [Nat.mul_comm 2, ← Nat.succ_mul];exact Nat.mul_le_mul_right 2 ih)
theorem chartWordOut (chart : RowChart) (w : Word) {i : Nat} (hi : 24 ≤ i) :
    (chartWord chart w).testBit i=false:=by
  have hlt : chartWord chart w < 2 ^ 24:=by
    simpa [chartWord,chart.property] using chartBitsLt w chart.val
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hi))
theorem chartWordAnd (chart : RowChart) (a b : Word) :
    chartWord chart (a&&&b)=chartWord chart a&&&chartWord chart b:=by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases hi : i < 24
  · rw [Nat.testBit_and,chartWordBit chart _ hi,chartWordBit chart _ hi,chartWordBit chart _ hi,Nat.testBit_and]
  · simp [Nat.testBit_and,chartWordOut chart _ (Nat.le_of_not_lt hi)]
theorem chartWordOr (chart : RowChart) (a b : Word) :
    chartWord chart (a|||b)=chartWord chart a|||chartWord chart b:=by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases hi : i < 24
  · rw [Nat.testBit_or,chartWordBit chart _ hi,chartWordBit chart _ hi,chartWordBit chart _ hi,Nat.testBit_or]
  · simp [Nat.testBit_or,chartWordOut chart _ (Nat.le_of_not_lt hi)]
theorem chartWordGoal {goal : Word} {chart : RowChart} (ok : ChartOK goal chart) :
    chartWord chart goal=4095:=by
  apply Nat.eq_of_testBit_eq;intro i
  rw [PackedRect.tb4095]
  by_cases hi : i < 24
  · rw [chartWordBit chart goal hi]
    by_cases h12 : i < 12
    · simp [h12,chartPos ok h12]
    · have hsub : i=12+(i - 12):=by omega
      have hneg:=chartNeg ok (show i - 12 < 12 by omega)
      rw [← hsub] at hneg
      simp [h12,hneg]
  · simp [chartWordOut chart goal (Nat.le_of_not_lt hi),show ¬ i < 12 by omega]
theorem liveToReachChart {mask goal : Word} {chart : RowChart} (ok : ChartOK goal chart)
    {k : Nat} {S : Finset Word} (live : LiveWord mask goal k 0 S) :
    ∃ k' S',k' ≤ k ∧ S' ⊆ S.image (chartWord chart) ∧ PackedRect.Reach false S' k':=by
  let f:=chartWord chart
  have step : ∀ {k t : Nat} {S : Finset Word},LiveWord mask goal k t S → t=0 →
      ∃ k' S',k' ≤ k ∧ S' ⊆ S.image f ∧ PackedRect.Reach false S' k':=by
    intro k t S h
    induction h using LiveWord.ind with
    | stop _ =>
      intro _
      refine ⟨0,{4095},Nat.le_refl _, ?_,rfl⟩
      dsimp only [f];rw [Finset.image_singleton,chartWordGoal ok]
    | unary _ _ _ _=>intro ht;omega
    | @binary k t U a b d _ _ _ _ tail ih =>
      intro ht
      obtain ⟨k',S',hk',hsub,hR⟩:=ih ht
      let z:=binWord d a b
      let T:=(insert a (insert b U)).image f
      have hfz : f z=binWord d (f a) (f b):=by cases d;exact chartWordAnd chart a b;exact chartWordOr chart a b
      have hUsub : U.image f ⊆ T:=Finset.image_subset_image (fun x hx=>Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
      by_cases hmem : f z ∈ S'
      · by_cases hinT : f z ∈ T
        · refine ⟨k',S',by omega, ?_,hR⟩
          intro x hx;have h1:=hsub hx;rw [Finset.image_insert] at h1
          rcases Finset.mem_insert.mp h1 with rfl | hxU
          · exact hinT
          · exact hUsub hxU
        · let U':=S'.erase (f z)
          have hU'sub : U' ⊆ T:=by
            intro x hx;obtain ⟨hne,hxS⟩:=Finset.mem_erase.mp hx
            have h1:=hsub hxS;rw [Finset.image_insert] at h1
            exact hUsub ((Finset.mem_insert.mp h1).resolve_left hne)
          let S2:=insert (f a) (insert (f b) U')
          have hfaT : f a ∈ T:=Finset.mem_image_of_mem f (Finset.mem_insert_self a _)
          have hfbT : f b ∈ T:=Finset.mem_image_of_mem f (Finset.mem_insert_of_mem (Finset.mem_insert_self b U))
          have hS2sub : S2 ⊆ T:=by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hfaT
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hfbT
            · exact hU'sub hx
          have hfab : f a ≠ f b:=by
            intro eq;apply hinT;rw [hfz,eq];cases d <;> simpa [binWord] using hfbT
          have hfnot : f z ∉ S2:=fun hm=>hinT (hS2sub hm)
          refine ⟨k'+1,S2,by omega,hS2sub,Or.inr ⟨f a,f b,f z,decide (f a ∈ U'),decide (f b ∈ U'),
            Finset.mem_insert_self _ _,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
            by rw [hfz];cases d <;> simp [binWord], ?_,trivial, ?_⟩⟩
          · intro x hx
            simp only [PackedRect.blk,cond_false]
            apply Bool.eq_false_iff.mpr
            intro eq;exact hfnot ((Nat.beq_eq.mp eq) ▸ hx)
          · have hf : S2.filter (fun x=>(decide (f a ∈ U')=true ∨ x ≠ f a) ∧ (decide (f b ∈ U')=true ∨ x ≠ f b))=U':=by
              ext x;rw [Finset.mem_filter]
              by_cases ha : x=f a
              · subst x;simp [S2,hfab]
              by_cases hb : x=f b
              · subst x;simp [S2,hfab.symm]
              simp [S2,ha,hb]
            rw [hf,Finset.insert_erase hmem]
            exact hR
      · refine ⟨k',S',by omega, ?_,hR⟩
        intro x hx;have hne : x ≠ f z:=fun eq=>hmem (eq ▸ hx)
        have h1:=hsub hx;rw [Finset.image_insert] at h1
        exact hUsub ((Finset.mem_insert.mp h1).resolve_left hne)
  exact step live rfl
theorem pairwiseDisjRect {q : Nat} {xs : List Nat}
    (hp : xs.Pairwise (fun a b => ¬ ((PackedRect.rectW a).testBit q=true ∧ (PackedRect.rectW b).testBit q=true)))
    {u v : Nat} (hu : u ∈ xs) (hv : v ∈ xs) (huv : u ≠ v) :
    ¬ ((PackedRect.rectW u).testBit q=true ∧ (PackedRect.rectW v).testBit q=true):=by
  induction hp with
  | nil=>simp at hu
  | @cons x xs hx _ ih =>
    rcases List.mem_cons.mp hu with hu1 | hu2 <;> rcases List.mem_cons.mp hv with hv1 | hv2
    · exact absurd (hu1.trans hv1.symm) huv
    · rw [hu1];exact hx v hv2
    · rw [hv1];intro ⟨h1,h2⟩;exact hx u hu2 ⟨h2,h1⟩
    · exact ih hu2 hv2
theorem twSublist {q : Nat} {l' l : List Nat} (hnd' : l'.Nodup) (hsub : ∀ x ∈ l',x ∈ l)
    (h : (PackedRect.tw (l'.map PackedRect.rectW) 0 0).testBit q=true) :
    (PackedRect.tw (l.map PackedRect.rectW) 0 0).testBit q=true:=by
  by_contra hfalse
  have hf : (PackedRect.tw (l.map PackedRect.rectW) 0 0).testBit q=false:=by
    cases hb : (PackedRect.tw (l.map PackedRect.rectW) 0 0).testBit q <;> simp_all
  have hpwL:=List.pairwise_map.mp (PackedRect.tw_spec q (l.map PackedRect.rectW) 0 0 hf).2.2
  have hpw' : l'.Pairwise (fun x y => ¬ ((PackedRect.rectW x).testBit q=true ∧ (PackedRect.rectW y).testBit q=true)) :=
    List.Pairwise.imp_of_mem (fun {a b} ha hb hab=>pairwiseDisjRect hpwL (hsub a ha) (hsub b hb) hab) hnd'
  have hzero : ∀ (xs : List Nat) (o t : Nat),
      t.testBit q=false →
      (o.testBit q=true → ∀ x ∈ xs,(PackedRect.rectW x).testBit q=false) →
      xs.Pairwise (fun x y => ¬ ((PackedRect.rectW x).testBit q=true ∧ (PackedRect.rectW y).testBit q=true)) →
      (PackedRect.tw (xs.map PackedRect.rectW) o t).testBit q=false:=by
    intro xs
    induction xs with
    | nil=>intro o t ht _ _;exact ht
    | cons x xs ih =>
      intro o t ht ho hpx
      obtain ⟨hx,hxs⟩:=List.pairwise_cons.mp hpx
      apply ih (Nat.lor o (PackedRect.rectW x)) (Nat.lor t (Nat.land o (PackedRect.rectW x)))
      · rw [PackedRect.tb_lor,Bool.or_eq_false_iff,PackedRect.tb_land]
        refine ⟨ht, ?_⟩
        cases hox : o.testBit q
        · simp
        · simp [ho hox x List.mem_cons_self]
      · intro hox y hy
        rw [PackedRect.tb_lor,Bool.or_eq_true] at hox
        rcases hox with h1 | h2
        · exact ho h1 y (List.mem_cons_of_mem _ hy)
        · cases hry : (PackedRect.rectW y).testBit q
          · rfl
          · exact False.elim (hx y hy ⟨h2,hry⟩)
      · exact hxs
  have hc:=hzero l' 0 0 (by simp) (by simp) hpw'
  rw [hc] at h
  exact Bool.noConfusion h
theorem hullMonotone {a b q : Nat} (hsub : ∀ r < 144,a.testBit r=true → b.testBit r=true)
    (hq : (PackedRect.hull a).testBit q=true) : (PackedRect.hull b).testBit q=true:=by
  have landM {x y m : Nat} (h : ∀ r,x.testBit r=true → y.testBit r=true) :
      ∀ r,(Nat.land x m).testBit r=true → (Nat.land y m).testBit r=true:=by
    intro r hr;rw [PackedRect.tb_land,Bool.and_eq_true] at hr ⊢;exact ⟨h r hr.1,hr.2⟩
  have orSM {x y s : Nat} (h : ∀ r,x.testBit r=true → y.testBit r=true) :
      ∀ r,(PackedRect.orS x s).testBit r=true → (PackedRect.orS y s).testBit r=true:=by
    intro r hr;rw [PackedRect.orS_tb,Bool.or_eq_true] at hr ⊢;exact hr.imp (h r) (h (s+r))
  have orSLM {x y s : Nat} (h : ∀ r,x.testBit r=true → y.testBit r=true) :
      ∀ r,(PackedRect.orSL x s).testBit r=true → (PackedRect.orSL y s).testBit r=true:=by
    intro r hr;rw [PackedRect.orSL_tb,Bool.or_eq_true,Bool.and_eq_true] at hr ⊢
    exact hr.imp (h r) (fun ⟨h1,h2⟩=>⟨h1,h (r - s) h2⟩)
  have h1 : ∀ r,(Nat.land a PackedRect.full).testBit r=true → (Nat.land b PackedRect.full).testBit r=true:=by
    intro r hr
    rw [PackedRect.tb_land,PackedRect.full_tb,Bool.and_eq_true,decide_eq_true_eq] at hr ⊢
    exact ⟨hsub r hr.2 hr.1,hr.2⟩
  have hR:=orSLM (orSLM (orSLM (orSLM (landM (orSM (orSM (orSM (orSM h1 (s:=6)) (s:=3)) (s:=1)) (s:=1)) (m:=PackedRect.rowM)) (s:=6)) (s:=3)) (s:=1)) (s:=1)
  have hC:=orSLM (orSLM (orSLM (orSLM (landM (orSM (orSM (orSM (orSM h1 (s:=96)) (s:=48)) (s:=24)) (s:=12)) (m:=4095)) (s:=96)) (s:=48)) (s:=24)) (s:=12)
  unfold PackedRect.hull PackedRect.hullC PackedRect.rowsOf PackedRect.colsOf at hq ⊢
  rw [PackedRect.tb_land,Bool.and_eq_true] at hq ⊢
  exact ⟨hR q hq.1,hC q hq.2⟩
def privCount (l : List Word) : Nat :=
  let rs:=PackedRect.mapW' l
  let t:=PackedRect.tw' rs 0 0
  (rs.filter (fun r => !Nat.beq (Nat.land (Nat.land r (Nat.xor t PackedRect.full)) PackedRect.full) 0)).length
def childState1 (mask token : Nat) (state : RowState1) : Option RowState1 :=
  let (fuel,nots,ws,history):=state
  let keep:=token % 4
  let op:=(token / 4) % 3
  let a:=token / (4*3*64)
  let b:=(token / (4*3)) % 64
  if fuel==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b) then none
  else
    let x:=ws.getD a 0
    let y:=ws.getD b 0
    let w:=if op==0 then x&&&y else if op==1 then x|||y else mask^^^x
    if w==0||w==mask||ws.contains w then none
    else
      let rest:=if keep.testBit 0 then ws else ws.erase x
      let rest:=if op==2||keep.testBit 1 then rest else rest.erase y
      let nextNots:=if op==2 then nots - 1 else nots
      some (fuel - 1,nextNots,insertWord w rest,(w,x,y) :: history)
def rootState1 (base : List Word) (fuel initNots token : Nat) : RowState1 :=
 (fuel,initNots,rootWords base token,[])
def dagTrace1 (mask : Word) (stock : List Word) (fuel initNots : Nat) (forest : Forest)
    (i : Nat) : Option RowState1 :=
  (Nat.rec (motive:=fun _=>Nat → Option RowState1) (fun _=>none)
    (fun _ previous j =>
      let (parent,token):=forest j
      if parent==0 then
        if token < 2 ^ stock.length then some (rootState1 stock fuel initNots token) else none
      else (previous (parent - 1)).bind (childState1 mask token)) (fuel+1)) i
abbrev DagLink1:=Nat × Nat
def dagPartition1 (directed : Bool) (ws : List Word) : Word → Word → Bool :=
  List.rec
    (fun p n=>Nat.beq p 0||Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0||Nat.beq n 0 ||
      dagForceWord1 (p&&&w) (fun up =>
        dagForceWord1 (n&&&w) (fun down =>
          rest up down &&
            dagForceWord1 (p^^^up) (fun offP =>
              dagForceWord1 (if directed then n else n^^^down) (rest offP))))) ws
theorem dagOffBits1 {v w : Word} {i : Nat} (bit : (v^^^(v&&&w)).testBit i=true) :
    v.testBit i=true ∧ w.testBit i=false:=by
  rw [Nat.testBit_xor,Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv,hw] at bit ⊢
theorem dagPartition1Sound {directed : Bool} {ws : List Word} {positive negative : Word}
    (fail : dagPartition1 directed ws positive negative=false) :
    ∃ p n,positive.testBit p=true ∧ negative.testBit n=true ∧
      ∀ w ∈ ws,if directed then w.testBit p=true → w.testBit n=true
                  else w.testBit p=w.testBit n:=by
  have nonempty {w : Word} (hn : w ≠ 0) : ∃ j,w.testBit j=true:=by
    by_contra! all;apply hn;apply Nat.eq_of_testBit_eq;intro i;simp [all i]
  induction ws generalizing positive negative with
  | nil =>
    change (Nat.beq positive 0||Nat.beq negative 0)=false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p,hp⟩:=nonempty (w:=positive) (fun eq=>by simp [eq] at fail)
    obtain ⟨n,hn⟩:=nonempty (w:=negative) (fun eq=>by simp [eq] at fail)
    exact ⟨p,n,hp,hn,by simp⟩
  | cons w ws ih =>
    change (Nat.beq positive 0||Nat.beq negative 0 ||
      dagForceWord1 (positive&&&w) (fun up =>
        dagForceWord1 (negative&&&w) (fun down =>
          dagPartition1 directed ws up down &&
            dagForceWord1 (positive^^^up) (fun offP =>
              dagForceWord1 (if directed then negative else negative^^^down)
                (dagPartition1 directed ws offP)))))=false at fail
    simp only [dagForceWord1Eq,Bool.or_eq_false_iff,Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩:=ih on
      rw [Nat.testBit_and,Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1, ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2,hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩:=ih off
      have hp':=dagOffBits1 hp
      cases mode : directed
      · have hn' : negative.testBit n=true ∧ w.testBit n=false:=by
          apply dagOffBits1;simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn'.1, ?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2,hn'.2]
        · simpa [mode] using agree _ tail
      · have hn' : negative.testBit n=true:=by simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn', ?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2]
        · simpa [mode] using agree _ tail
theorem dagPartition1Live {mask goal : Word} {ws : List Word} {k t : Nat} {directed : Bool}
    (goalMask : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed=true → t=0) :
    dagPartition1 directed ws goal (mask^^^goal)=true:=by
  by_contra fail
  have openPair : dagPartition1 directed ws goal (mask^^^goal)=false:=by
    cases h : dagPartition1 directed ws goal (mask^^^goal) <;> simp_all
  obtain ⟨p,n,hp,hn,agree⟩:=dagPartition1Sound openPair
  have pm:=positiveInMask goalMask hp
  have nm : mask.testBit n=true ∧ goal.testBit n=false:=by
    rw [Nat.testBit_xor] at hn
    have implied:=fun ht : goal.testBit n=true=>positiveInMask goalMask ht
    cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
  cases mode : directed with
  | false =>
    have same:=liveAgrees live (pm.trans nm.1.symm) (fun w hw=>by
      simpa [mode,AgreesAt] using agree w (List.mem_toFinset.mp hw))
    simp [AgreesAt,hp,nm.2] at same
  | true =>
    have ht:=noNot mode
    subst t
    obtain ⟨w,hw,a,b⟩:=liveDirected live hp nm.2
    have same:=agree w (List.mem_toFinset.mp hw)
    simp [mode,a,b] at same
abbrev DagSample1:=Nat × Nat
abbrev DagSignals1:=Word × Word
abbrev DagCounts1:=Word × Word × Word
abbrev DagTagged1:=Word × DagSignals1
def dagForceCache1 (tags : List DagSignals1) (use : List DagSignals1 → Bool) : Bool :=
 (List.rec (motive:=fun _=>(List DagSignals1 → Bool) → Bool) (fun k=>k [])
 (fun tag _ next k =>
 dagForceWord1 tag.1 (fun up=>dagForceWord1 tag.2 (fun down =>
 next (fun tail=>k ((up,down) :: tail))))) tags) use
theorem dagForceCache1Eq (tags : List DagSignals1) (use : List DagSignals1 → Bool) :
    dagForceCache1 tags use=use tags:=by
  induction tags generalizing use with
  | nil=>rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩:=tag
    change dagForceWord1 a (fun up=>dagForceWord1 b (fun down =>
      dagForceCache1 rest (fun tail=>use ((up,down) :: tail))))=_
    simp only [dagForceWord1Eq,ih]
def dagGateWord1 (mask op x y : Word) : Word :=
  if Nat.beq op 0 then x&&&y else if Nat.beq op 1 then x|||y else mask^^^x
def dagTagBases1 (stock : List Word) (positive negative width : Nat) : List DagTagged1 :=
 (List.rec (motive:=fun _=>Nat → List DagTagged1) (fun _=>[])
 (fun w _ next i=>(w,unpack positive width i,unpack negative width i) :: next (i+1)) stock) 0
theorem dagKeepMem1 {ws : List Word} {x w : Word} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep=true ∨ w ≠ x):=by
  cases keep
  · simpa [keepWord,nd.mem_erase_iff,and_comm] using h
  · simpa [keepWord] using h
def dagSizeFloor1 (n op keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) -
    (if op==2||keep.testBit 1 then 0 else 1))+1
def dagKept1 (ws : List Word) (op keep x y : Nat) : List Word :=
  keepWord (op==2||keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
def dagDirectChild1 (mask : Word) (state : RowState1) (a b op keep x y out : Nat) : Option RowState1 :=
  let (fuel,nots,ws,history):=state
  if fuel==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b) then none
  else if out==0||out==mask||ws.contains out then none
  else
    let nextNots:=if op==2 then nots - 1 else nots
    some (fuel - 1,nextNots,insertWord out (dagKept1 ws op keep x y),(out,x,y) :: history)
theorem dagDirectChild1Eq {mask a b op keep : Nat} {state : RowState1}
    (hb : b < 64) (hop : op < 3) (hk : keep < 4) :
    let x:=state.2.2.1.getD a 0
    let y:=state.2.2.1.getD b 0
    dagDirectChild1 mask state a b op keep x y (dagGateWord1 mask op x y) =
      childState1 mask (gateToken a b op keep) state:=by
  obtain ⟨fuel,nots,ws,history⟩:=state
  obtain ⟨keepEq,opEq,aEq,bEq⟩:=gateTokenFields (a:=a) hb hop hk
  simp only [childState1,dagDirectChild1,dagKept1,keepWord,keepEq,opEq,aEq,bEq,dagGateWord1]
  cases op with
  | zero=>rfl
  | succ op=>cases op <;> rfl
def dagAllowedRoot1 (witnesses : List Witness) (ws : List Word) : Bool :=
 witnesses.all (fun entry=>ws.contains (witnessWord entry))
def HasChild1 (mask : Nat) (state child : RowState1) : Prop :=
 ∃ a b op keep,a < state.2.2.1.length ∧
 ((a=b ∧ op=2 ∧ keep < 2 ∧ state.2.1 ≠ 0) ∨
 (a < b ∧ b < state.2.2.1.length ∧ op < 2 ∧ keep < 4)) ∧
 childState1 mask (gateToken a b op keep) state=some child
theorem wordProgress1 {mask target : Word} {state : RowState1}
    (width : state.2.2.1.length ≤ 64) (viable : WordViable1 mask target state) :
    (state.2.1=0 ∧ target ∈ state.2.2.1) ∨
      ∃ child,HasChild1 mask state child ∧ WordViable1 mask target child ∧ child.2.1 ≤ state.2.1:=by
  obtain ⟨fuel,nots,ws,history⟩:=state
  change ws.length ≤ 64 at width
  obtain ⟨nd,k,cap,live⟩:=viable
  change k ≤ fuel at cap
  change LiveWord mask target k nots ws.toFinset at live
  cases k with
  | zero =>
    left
    obtain ⟨ht0,eq,_⟩:=live
    exact ⟨ht0,List.mem_toFinset.mp (by rw [eq];simp)⟩
  | succ k =>
    right
    rcases live with ⟨u,U,x,rfl,eq,px,fresh,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,fresh,tail⟩
    · let a:=ws.idxOf x
      have xm : x ∈ ws:=by rw [← List.mem_toFinset,eq];simp
      have ha : a < ws.length:=List.idxOf_lt_length_iff.mpr xm
      have hx : ws.getD a 0=x:=getWord xm
      have p:=liveWordProper tail (mask^^^x) (Finset.mem_insert_self _ _)
      let save:=decide (x ∈ U)
      let keep:=if save then 1 else 0
      have keepLt : keep < 2:=by dsimp [keep];split <;> decide
      have keepBit : keep.testBit 0=save:=by unfold keep;cases save <;> decide
      have fn : mask^^^x ∉ ws:=by simpa [← List.mem_toFinset,eq] using fresh
      let rest:=keepWord save x ws
      let child : RowState1:=(fuel - 1,u,insertWord (mask^^^x) rest,(mask^^^x,x,x) :: history)
      obtain ⟨ke,op,aa,bb⟩:=gateTokenFields (a:=a) (show a < 64 by omega) (by decide : 2 < 3) (by omega : keep < 4)
      have heval : childState1 mask (gateToken a a 2 keep) (fuel,u+1,ws,history)=some child:=by
        simp only [childState1,ke,op,aa,bb,hx,keepBit]
        simp [show fuel ≠ 0 by omega,Nat.not_le_of_lt ha,Nat.not_le_of_lt keepLt,p.1,p.2,fn,keepWord,child,rest]
      refine ⟨child,⟨a,a,2,keep,ha,Or.inl ⟨rfl,rfl,keepLt,Nat.succ_ne_zero u⟩,heval⟩, ?_,by change u ≤ u+1;omega⟩
      refine ⟨insertWordNodup (keepNodup nd save x) (fun h=>fn (keepSubset save x ws _ h)),k,by change k ≤ fuel - 1;omega, ?_⟩
      change LiveWord mask target k u (insertWord (mask^^^x) rest).toFinset
      rw [insertWordSet,keepSet nd eq]
      exact tail
    · have doBin (x y : Word) (d : Bool) (eq : ws.toFinset=insert x (insert y U))
          (xy : x ≠ y) (ordered : ws.idxOf x < ws.idxOf y)
          (fresh : binWord d x y ∉ insert x (insert y U))
          (tail : LiveWord mask target k nots (insert (binWord d x y) U)) :
          ∃ child,HasChild1 mask (fuel,nots,ws,history) child ∧ WordViable1 mask target child ∧ child.2.1 ≤ nots:=by
        let a:=ws.idxOf x
        let b:=ws.idxOf y
        have xm : x ∈ ws:=by rw [← List.mem_toFinset,eq];simp
        have ym : y ∈ ws:=by rw [← List.mem_toFinset,eq];simp
        have ha : a < ws.length:=List.idxOf_lt_length_iff.mpr xm
        have hb : b < ws.length:=List.idxOf_lt_length_iff.mpr ym
        have hx : ws.getD a 0=x:=getWord xm
        have hy : ws.getD b 0=y:=getWord ym
        let v:=binWord d x y
        have p:=liveWordProper tail v (Finset.mem_insert_self _ _)
        let saveA:=decide (x ∈ U)
        let saveB:=decide (y ∈ U)
        let keep:=(if saveA then 1 else 0)+(if saveB then 2 else 0)
        have keepLt : keep < 4:=by dsimp [keep];split <;> split <;> decide
        have kb0 : keep.testBit 0=saveA:=by dsimp [keep];cases saveA <;> cases saveB <;> decide
        have kb1 : keep.testBit 1=saveB:=by dsimp [keep];cases saveA <;> cases saveB <;> decide
        have fn : v ∉ ws:=by simpa [← List.mem_toFinset,eq] using fresh
        let rest:=keepWord saveB y (keepWord saveA x ws)
        let opN:=if d then 1 else 0
        have hop : opN < 2:=by dsimp [opN];cases d <;> decide
        obtain ⟨ke,op,aa,bb⟩:=gateTokenFields (a:=a) (show b < 64 by omega) (by omega : opN < 3) keepLt
        let child : RowState1:=(fuel - 1,nots,insertWord v rest,(v,x,y) :: history)
        have heval : childState1 mask (gateToken a b opN keep) (fuel,nots,ws,history)=some child:=by
          have habLt : a < b:=ordered
          simp only [childState1,ke,op,aa,bb,hx,hy,kb0,kb1]
          cases d <;> (
            simp only [v,binWord, ↓reduceIte,Bool.false_eq_true] at p fn
            simp [opN,show fuel ≠ 0 by omega,habLt,Nat.not_le_of_lt hb,keepWord,binWord,p.1,p.2,fn,child,rest,v])
        refine ⟨child,⟨a,b,opN,keep,ha,Or.inr ⟨ordered,hb,hop,keepLt⟩,heval⟩, ?_,Nat.le_refl _⟩
        refine ⟨insertWordNodup (keepNodup (keepNodup nd saveA x) saveB y)
            (fun h=>fn (keepSubset saveA x ws _ (keepSubset saveB y _ _ h))),
          k,by change k ≤ fuel - 1;omega, ?_⟩
        change LiveWord mask target k nots (insertWord v rest).toFinset
        rw [insertWordSet,keepPairSet nd xy eq]
        exact tail
      have xm : x ∈ ws:=by rw [← List.mem_toFinset,eq];simp
      have ym : y ∈ ws:=by rw [← List.mem_toFinset,eq];simp
      have diff : ws.idxOf x ≠ ws.idxOf y:=by
        intro same;apply xy;rw [← getWord xm,same,getWord ym]
      by_cases hord : ws.idxOf x < ws.idxOf y
      · exact doBin x y d eq xy hord fresh tail
      · exact doBin y x d (by rw [eq,Finset.insert_comm]) xy.symm (by omega)
          (by rw [binWord_comm d y x,Finset.insert_comm];exact fresh)
          (by rw [binWord_comm d y x];exact tail)
theorem dagDirectChild1Nots {mask a b op keep x y out : Nat} {state child : RowState1}
    (h : dagDirectChild1 mask state a b op keep x y out=some child) :
    child.2.1=(if op==2 then state.2.1 - 1 else state.2.1) ∧
    (out==0||out==mask||state.2.2.1.contains out)=false:=by
  obtain ⟨fuel,nots,ws,history⟩:=state
  let bad : Bool:=fuel==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b)
  let stale : Bool:=out==0||out==mask||ws.contains out
  change (if bad then none else if stale then none else
    some (fuel - 1,if op==2 then nots - 1 else nots,insertWord out (dagKept1 ws op keep x y),(out,x,y) :: history))=some child at h
  by_cases h1 : bad=true
  · simp [h1] at h
  by_cases h2 : stale=true
  · simp [h1,h2] at h
  have heq : (fuel - 1,if op==2 then nots - 1 else nots,insertWord out (dagKept1 ws op keep x y),(out,x,y) :: history)=child:=by
    simpa [h1,h2] using h
  refine ⟨by rw [← heq],Bool.eq_false_iff.mpr h2⟩
theorem childState1Data {mask token : Nat} {state child : RowState1}
    (eval : childState1 mask token state=some child)
    (masked : ∀ w ∈ state.2.2.1,Masked mask w) :
    child.1 < state.1 ∧ child.2.1 ≤ state.2.1 ∧ ∀ w ∈ child.2.2.1,Masked mask w:=by
  obtain ⟨fuel,nots,ws,history⟩:=state
  let keep:=token % 4
  let op:=token / 4 % 3
  let a:=token / (4*3*64)
  let b:=token / (4*3) % 64
  let x:=ws.getD a 0
  let y:=ws.getD b 0
  let z:=if op==0 then x&&&y else if op==1 then x|||y else mask^^^x
  let rest:=keepWord (op==2||keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let nextNots:=if op==2 then nots - 1 else nots
  let bad : Bool:=fuel==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b)
  let stale : Bool:=z==0||z==mask||ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1,nextNots,insertWord z rest,(z,x,y) :: history))=some child at eval
  by_cases hb : bad=true
  · simp [hb] at eval
  by_cases hs : stale=true
  · simp [hb,hs] at eval
  have eq : (fuel - 1,nextNots,insertWord z rest,(z,x,y) :: history)=child:=by simpa [hb,hs] using eval
  subst child
  have pos : 0 < fuel:=by
    by_contra! h
    have he : fuel=0:=by omega
    exact hb (by simp [bad,he])
  have hnle : nextNots ≤ nots:=by
    dsimp only [nextNots];by_cases h : (op==2)=true <;> simp [h] <;> omega
  refine ⟨by dsimp;omega,hnle, ?_⟩
  have read (i : Nat) : AvailableWord mask ws (ws.getD i 0):=by
    simp only [List.getD_eq_getElem?_getD]
    cases h : ws[i]? with
    | none=>exact Or.inl rfl
    | some a=>exact Or.inr (Or.inr (List.mem_of_getElem? h))
  have hm : Masked mask z:=by
    apply maskedGate masked
    unfold z
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inl rfl⟩
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inr rfl⟩
    · exact Or.inl ⟨x,read _,rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · exact masked w (keepSubset (keep.testBit 0) x ws w (keepSubset (op==2||keep.testBit 1) y _ w other))
def isNotOp : PEqualNP.CircuitLowerBounds.GateOp → Bool
  | PEqualNP.CircuitLowerBounds.GateOp.not=>true
  | _=>false
def notCount (gs : List PEqualNP.CircuitLowerBounds.Gate) : Nat :=
 (gs.filter (fun g=>isNotOp g.op)).length
theorem notCountLeOne {gs : List PEqualNP.CircuitLowerBounds.Gate}
    (h1 : ∀ i j : Fin gs.length,
      (gs.get i).op=PEqualNP.CircuitLowerBounds.GateOp.not →
      (gs.get j).op=PEqualNP.CircuitLowerBounds.GateOp.not → i=j) :
    notCount gs ≤ 1:=by
  induction gs with
  | nil=>simp [notCount]
  | cons g gs ih =>
    have htail : ∀ i j : Fin gs.length,
        (gs.get i).op=PEqualNP.CircuitLowerBounds.GateOp.not →
        (gs.get j).op=PEqualNP.CircuitLowerBounds.GateOp.not → i=j:=by
      intro i j hi hj
      exact Fin.succ_inj.mp (h1 i.succ j.succ hi hj)
    cases hgop : g.op with
    | not =>
      have hnone : ∀ x ∈ gs,isNotOp x.op=false:=by
        intro x hx
        cases hxop : x.op <;> simp only [isNotOp]
        exfalso
        obtain ⟨k,hk,rfl⟩:=List.mem_iff_getElem.mp hx
        have heq:=h1 ⟨0,by simp⟩ ⟨k+1,by simp [hk]⟩ hgop (by simpa using hxop)
        have hval:=congrArg Fin.val heq
        dsimp at hval;omega
      have hfil : gs.filter (fun x=>isNotOp x.op)=[]:=by
        rw [List.filter_eq_nil_iff];intro x hx;simp [hnone x hx]
      have : (List.filter (fun x=>isNotOp x.op) (g :: gs))=[g]:=by
        rw [List.filter_cons,hgop];exact congrArg (g :: ·) hfil
      simp [notCount,this]
    | and=>exact by simpa [notCount,hgop,isNotOp] using ih htail
    | or=>exact by simpa [notCount,hgop,isNotOp] using ih htail
    | mod _=>exact by simpa [notCount,hgop,isNotOp] using ih htail
    | maj=>exact by simpa [notCount,hgop,isNotOp] using ih htail
theorem hcsExtractExact {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate) (goal : Word)
    (hlegal : ∀ g ∈ gs,
      (g.op=PEqualNP.CircuitLowerBounds.GateOp.and ∨
       g.op=PEqualNP.CircuitLowerBounds.GateOp.or ∨
       g.op=PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2)
    (hpg : properWord (fullMask rows) goal)
    (hhit : goal ∈ (gs.foldl hcsStep bank).map BitVec.toNat) :
    ∃ k t S,k ≤ gs.length ∧ t ≤ notCount gs ∧
      LiveWord (fullMask rows) goal k t S ∧ ∀ w ∈ S,w ∈ bank.map BitVec.toNat:=by
  induction gs generalizing bank with
  | nil =>
    exact ⟨0,0,{goal},Nat.le_refl _,Nat.zero_le _,LiveWord.stop hpg,by simpa using hhit⟩
  | cons g gs ih =>
    have hg:=hlegal g List.mem_cons_self
    have hrest : ∀ g' ∈ gs,
        (g'.op=PEqualNP.CircuitLowerBounds.GateOp.and ∨
         g'.op=PEqualNP.CircuitLowerBounds.GateOp.or ∨
         g'.op=PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg'=>hlegal g' (List.mem_cons_of_mem _ hg')
    obtain ⟨k,t,S,hk,ht,hlive,hsub⟩:=ih (hcsStep bank g) hrest hhit
    have hstepEq : (hcsStep bank g).map BitVec.toNat=bank.map BitVec.toNat ++ [(hcsGateVal bank g).toNat]:=by
      simp [hcsStep]
    rw [hstepEq] at hsub
    have hM : ∀ w ∈ bank.map BitVec.toNat,Masked (fullMask rows) w:=fun w hw=>by
      obtain ⟨v,_,rfl⟩:=List.mem_map.mp hw;exact toNatMasked v
    obtain ⟨op,ins⟩:=g
    have hop:=hg.1
    have hlen:=hg.2
    rcases hop with rfl | rfl | rfl
    · have hnc : notCount (⟨.and,ins⟩ :: gs)=notCount gs:=by simp [notCount,isNotOp]
      rw [hnc]
      cases ins with
      | nil =>
        have hrep : wordRep (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank ⟨.and,[]⟩).toNat :=
          Or.inr (by simp [hcsGateVal,fullMask,properWord])
        obtain ⟨S',hl',hs'⟩:=(pullWordExact hlive hsub).1 hrep
        exact ⟨k,t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
      | cons a rest =>
        cases rest with
        | nil =>
          have hval : (hcsGateVal bank ⟨.and,[a]⟩).toNat=(bank.getD a 0).toNat:=by simp [hcsGateVal]
          have hav:=toNatAvailable bank a
          have hrep : wordRep (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank ⟨.and,[a]⟩).toNat:=by
            rw [hval]
            rcases hav with h0 | hm | hmem
            · exact Or.inr (by rw [h0];exact fun h=>h.1 rfl)
            · exact Or.inr (by rw [hm];exact fun h=>h.2 rfl)
            · exact Or.inl hmem
          obtain ⟨S',hl',hs'⟩:=(pullWordExact hlive hsub).1 hrep
          exact ⟨k,t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
        | cons b rest =>
          cases rest with
          | nil =>
            have hval : (hcsGateVal bank ⟨.and,[a,b]⟩).toNat=binWord false (bank.getD a 0).toNat (bank.getD b 0).toNat:=by
              simp [hcsGateVal,binWord,BitVec.toNat_and]
            rw [hval] at hsub
            rcases classifyBinary hM false (toNatAvailable bank a) (toNatAvailable bank b) with hrep | hbw
            · obtain ⟨S',hl',hs'⟩:=(pullWordExact hlive hsub).1 hrep
              exact ⟨k,t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
            · obtain ⟨k',S',hk',hl',hs'⟩:=(pullWordExact hlive hsub).2.1 hbw
              exact ⟨k',t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
          | cons _ _=>simp at hlen
    · have hnc : notCount (⟨.or,ins⟩ :: gs)=notCount gs:=by simp [notCount,isNotOp]
      rw [hnc]
      cases ins with
      | nil =>
        have hrep : wordRep (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank ⟨.or,[]⟩).toNat :=
          Or.inr (by simp [hcsGateVal,properWord])
        obtain ⟨S',hl',hs'⟩:=(pullWordExact hlive hsub).1 hrep
        exact ⟨k,t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
      | cons a rest =>
        cases rest with
        | nil =>
          have hval : (hcsGateVal bank ⟨.or,[a]⟩).toNat=(bank.getD a 0).toNat:=by simp [hcsGateVal]
          have hav:=toNatAvailable bank a
          have hrep : wordRep (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank ⟨.or,[a]⟩).toNat:=by
            rw [hval]
            rcases hav with h0 | hm | hmem
            · exact Or.inr (by rw [h0];exact fun h=>h.1 rfl)
            · exact Or.inr (by rw [hm];exact fun h=>h.2 rfl)
            · exact Or.inl hmem
          obtain ⟨S',hl',hs'⟩:=(pullWordExact hlive hsub).1 hrep
          exact ⟨k,t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
        | cons b rest =>
          cases rest with
          | nil =>
            have hval : (hcsGateVal bank ⟨.or,[a,b]⟩).toNat=binWord true (bank.getD a 0).toNat (bank.getD b 0).toNat:=by
              simp [hcsGateVal,binWord,BitVec.toNat_or]
            rw [hval] at hsub
            rcases classifyBinary hM true (toNatAvailable bank a) (toNatAvailable bank b) with hrep | hbw
            · obtain ⟨S',hl',hs'⟩:=(pullWordExact hlive hsub).1 hrep
              exact ⟨k,t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
            · obtain ⟨k',S',hk',hl',hs'⟩:=(pullWordExact hlive hsub).2.1 hbw
              exact ⟨k',t,S',by simp only [List.length_cons];omega,ht,hl',hs'⟩
          | cons _ _=>simp at hlen
    · have hnc : notCount (⟨.not,ins⟩ :: gs)=notCount gs+1:=by simp [notCount,isNotOp]
      rw [hnc]
      cases ins with
      | nil =>
        have hrep : wordRep (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank ⟨.not,[]⟩).toNat:=by
          have : (hcsGateVal bank ⟨.not,[]⟩).toNat=fullMask rows:=by
            simpa [hcsGateVal] using notNat (0 : BitVec rows)
          exact Or.inr (by simp [this,properWord])
        obtain ⟨S',hl',hs'⟩:=(pullWordExact hlive hsub).1 hrep
        exact ⟨k,t,S',by simp only [List.length_cons];omega,by omega,hl',hs'⟩
      | cons a rest =>
        have hval : (hcsGateVal bank ⟨.not,a :: rest⟩).toNat=fullMask rows^^^(bank.getD a 0).toNat:=by
          simpa [hcsGateVal] using notNat (bank.getD a 0)
        have hav:=toNatAvailable bank a
        by_cases ha0 : (bank.getD a 0).toNat=0
        · have hrep : wordRep (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank ⟨.not,a :: rest⟩).toNat:=by
            right;rw [hval,ha0];simp [properWord]
          obtain ⟨S',hl',hs'⟩:=(pullWordExact hlive hsub).1 hrep
          exact ⟨k,t,S',by simp only [List.length_cons];omega,by omega,hl',hs'⟩
        by_cases ham : (bank.getD a 0).toNat=fullMask rows
        · have hself : fullMask rows^^^fullMask rows=0:=by
            apply Nat.eq_of_testBit_eq;intro i;simp
          have hrep : wordRep (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank ⟨.not,a :: rest⟩).toNat:=by
            right;rw [hval,ham,hself];simp [properWord]
          obtain ⟨S',hl',hs'⟩:=(pullWordExact hlive hsub).1 hrep
          exact ⟨k,t,S',by simp only [List.length_cons];omega,by omega,hl',hs'⟩
        have hmem : (bank.getD a 0).toNat ∈ bank.map BitVec.toNat:=(hav.resolve_left ha0).resolve_left ham
        obtain ⟨k',t',S',hk',_,ht',_,hl',hs'⟩ :=
          (pullWordExact hlive hsub).2.2 ⟨(bank.getD a 0).toNat,hmem,⟨ha0,ham⟩,hval⟩
        exact ⟨k',t',S',by simp only [List.length_cons];omega,by omega,hl',hs'⟩
theorem liveWordToMonoCircuit {rows : Nat} (bank : List (BitVec rows)) (goal : BitVec rows)
    {k : Nat} {S : Finset Word}
    (live : LiveWord (fullMask rows) goal.toNat k 0 S)
    (sub : ∀ w ∈ S,w ∈ bank.map BitVec.toNat) :
    ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : Nat),
      (∀ g ∈ gs,(g.op=PEqualNP.CircuitLowerBounds.GateOp.and ∨
                  g.op=PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length ≤ k ∧
      (gs.foldl hcsStep bank).getD o 0=goal:=by
  generalize ht : (0 : Nat)=t at live
  induction live using LiveWord.ind generalizing bank with
  | stop hp =>
    have hmem : goal.toNat ∈ bank.map BitVec.toNat:=sub goal.toNat (Finset.mem_singleton_self _)
    obtain ⟨v,hv,hveq⟩:=List.mem_map.mp hmem
    have hvgoal : v=goal:=BitVec.eq_of_toNat_eq hveq
    subst hvgoal
    obtain ⟨i,hi,heq⟩:=List.mem_iff_getElem.mp hv
    refine ⟨[],i,fun _ h=>False.elim (List.not_mem_nil h),Nat.le_refl _, ?_⟩
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi] using heq
  | unary _ _ _ _=>exact False.elim (Nat.succ_ne_zero _ ht.symm)
  | @binary k t U a b d pa pb hab hfresh tail ih =>
    have haMem : a ∈ bank.map BitVec.toNat:=sub a (Finset.mem_insert_self a _)
    have hbMem : b ∈ bank.map BitVec.toNat:=sub b (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    obtain ⟨va,hva,hvaEq⟩:=List.mem_map.mp haMem
    obtain ⟨vb,hvb,hvbEq⟩:=List.mem_map.mp hbMem
    obtain ⟨ia,hia,hiaEq⟩:=List.mem_iff_getElem.mp hva
    obtain ⟨ib,hib,hibEq⟩:=List.mem_iff_getElem.mp hvb
    let g : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨if d then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and,[ia,ib]⟩
    have hgetA : (bank.getD ia 0).toNat=a:=by
      have : bank.getD ia 0=va:=by simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hia] using hiaEq
      rw [this,hvaEq]
    have hgetB : (bank.getD ib 0).toNat=b:=by
      have : bank.getD ib 0=vb:=by simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hib] using hibEq
      rw [this,hvbEq]
    have hval : (hcsGateVal bank g).toNat=binWord d a b:=by
      cases d
      · change (hcsGateVal bank ⟨.and,[ia,ib]⟩).toNat=a&&&b
        simp only [hcsGateVal,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,BitVec.and_allOnes,BitVec.toNat_and,hgetA,hgetB]
      · change (hcsGateVal bank ⟨.or,[ia,ib]⟩).toNat=a|||b
        simp only [hcsGateVal,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,BitVec.toNat_or,hgetA,hgetB]
        simp [Nat.or_zero]
    have hsub' : ∀ w ∈ insert (binWord d a b) U,w ∈ (hcsStep bank g).map BitVec.toNat:=by
      intro w hw
      simp only [hcsStep,List.map_append,List.map_cons,List.map_nil,List.mem_append,List.mem_singleton]
      rcases Finset.mem_insert.mp hw with rfl | hu
      · exact Or.inr hval.symm
      · exact Or.inl (sub w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)))
    obtain ⟨gs,o,hleg,hlen,heval⟩:=ih (hcsStep bank g) hsub' ht
    refine ⟨g :: gs,o, ?_,by simp only [List.length_cons];omega,heval⟩
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · cases d <;> simp [g]
    · exact hleg g' hg'
def fBor (a b : Bool) : Bool := @Bool.rec (fun _=>Bool) b true a
def fBand (a b : Bool) : Bool := @Bool.rec (fun _=>Bool) false b a
def fBnot (a : Bool) : Bool := @Bool.rec (fun _=>Bool) true false a
theorem fBor_eq (a b : Bool) : fBor a b=(a||b):=by cases a <;> rfl
theorem fBand_eq (a b : Bool) : fBand a b=(a&&b):=by cases a <;> rfl
theorem fBnot_eq (a : Bool) : fBnot a = !a:=by cases a <;> rfl
def fForce {α : Type} (w : Word) (k : Word → α) : α :=
 @Nat.rec (fun _ => α) (k 0) (fun n _=>k (Nat.succ n)) w
theorem fForce_eq {α : Type} (w : Word) (k : Word → α) : fForce w k=k w:=by
  cases w <;> rfl
def fForceWords {α : Type} (ws : List Word) (k : List Word → α) : α :=
 (List.rec (motive:=fun _=>(List Word → α) → α) (fun f=>f [])
 (fun w _ next f=>fForce w (fun v=>next (fun rest=>f (v :: rest)))) ws) k
theorem fForceWords_eq {α : Type} (ws : List Word) (k : List Word → α) :
    fForceWords ws k=k ws:=by
  induction ws generalizing k with
  | nil=>rfl
  | cons w ws ih =>
    change fForce w (fun v=>fForceWords ws (fun rest=>k (v :: rest)))=_
    rw [fForce_eq,ih]
theorem fNatBeq_iff_beq (a b : Nat) : Nat.beq a b=(a==b):=rfl
theorem fNatBle_iff_le (a b : Nat) : Nat.ble a b=decide (a ≤ b):=by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b:=fun hl=>Bool.noConfusion ((Nat.ble_eq.mpr hl).symm.trans h)
    simp [this]
  · simp [Nat.ble_eq.mp h]
theorem fNatBlt_iff_lt (a b : Nat) : Nat.blt a b=decide (a < b):=by
  cases h : Nat.blt a b
  · have : ¬ a < b:=fun hl=>Bool.noConfusion ((Nat.blt_eq.mpr hl).symm.trans h)
    simp [this]
  · simp [Nat.blt_eq.mp h]
def fContains (w : Word) (ws : List Word) : Bool :=
 List.rec false (fun a _ next=>fBor (Nat.beq a w) next) ws
theorem fContains_eq (w : Word) (ws : List Word) : fContains w ws=ws.contains w:=by
  induction ws with
  | nil=>rfl
  | cons a ws ih =>
    change fBor (Nat.beq a w) (fContains w ws)=(a :: ws).contains w
    rw [fBor_eq,ih,List.contains_cons,Bool.or_comm]
    cases h : Nat.beq a w
    · have hne : w ≠ a:=fun he=>Bool.noConfusion ((Nat.beq_eq.mpr he.symm).symm.trans h)
      simp [hne]
    · have heq : w=a:=(Nat.beq_eq.mp h).symm
      simp [heq]
def fErase (w : Word) (ws : List Word) : List Word :=
 List.rec [] (fun a tail next => @Bool.rec (fun _=>List Word) (a :: next) tail (Nat.beq a w)) ws
theorem fErase_eq (w : Word) (ws : List Word) : fErase w ws=ws.erase w:=by
  induction ws with
  | nil=>rfl
  | cons a ws ih =>
    change @Bool.rec (fun _=>List Word) (a :: fErase w ws) ws (Nat.beq a w)=(a :: ws).erase w
    rw [ih,List.erase_cons]
    cases h : Nat.beq a w
    · have hne : a ≠ w:=fun he=>Bool.noConfusion ((Nat.beq_eq.mpr he).symm.trans h)
      simp [hne]
    · have heq : a=w:=Nat.beq_eq.mp h
      simp [heq]
def fInsert (w : Word) (ws : List Word) : List Word :=
 fForce w fun w =>
 List.rec [w] (fun a tail next =>
 @Bool.rec (fun _=>List Word) (a :: next) (w :: a :: tail) (Nat.ble w a)) ws
theorem fInsert_eq (w : Word) (ws : List Word) : fInsert w ws=insertWord w ws:=by
  unfold fInsert;rw [fForce_eq]
  induction ws with
  | nil=>rfl
  | cons a ws ih =>
    change @Bool.rec (fun _=>List Word) (a :: List.rec [w] _ ws) (w :: a :: ws) (Nat.ble w a) =
      if w ≤ a then w :: a :: ws else a :: insertWord w ws
    rw [ih]
    cases h : Nat.ble w a
    · have hlt : ¬ w ≤ a:=fun hle=>Bool.noConfusion ((Nat.ble_eq.mpr hle).symm.trans h)
      simp [hlt]
    · simp [Nat.ble_eq.mp h]
def fGetD (ws : List Word) (i : Nat) : Word :=
 (List.rec (motive:=fun _=>Nat → Word) (fun _=>0)
 (fun a _ next k => @Nat.rec (fun _=>Word) a (fun j _=>next j) k) ws) i
theorem fGetD_eq (ws : List Word) (i : Nat) : fGetD ws i=ws.getD i 0:=by
  induction ws generalizing i with
  | nil=>rfl
  | cons a ws ih =>
    cases i with
    | zero=>rfl
    | succ j=>exact ih j
def fGetDTags (tags : List DagSignals1) (i : Nat) : DagSignals1 :=
 (List.rec (motive:=fun _=>Nat → DagSignals1) (fun _=>(0,0))
 (fun a _ next k => @Nat.rec (fun _=>DagSignals1) a (fun j _=>next j) k) tags) i
def fGetDTagged (bank : List DagTagged1) (i : Nat) : DagTagged1 :=
 (List.rec (motive:=fun _=>Nat → DagTagged1) (fun _=>(0,0,0))
 (fun a _ next k => @Nat.rec (fun _=>DagTagged1) a (fun j _=>next j) k) bank) i
def fListEq (as bs : List Word) : Bool :=
 (List.rec (motive:=fun _=>List Word → Bool)
 (fun bs=>List.rec true (fun _ _ _=>false) bs)
 (fun a _ next bs=>List.rec false (fun b bs' _=>fBand (Nat.beq a b) (next bs')) bs) as) bs
theorem fListEq_eq (as bs : List Word) : fListEq as bs=(as==bs):=by
  induction as generalizing bs with
  | nil=>cases bs <;> rfl
  | cons a as ih =>
    cases bs with
    | nil=>rfl
    | cons b bs =>
      change fBand (Nat.beq a b) (fListEq as bs)=((a==b)&&(as==bs))
      rw [fBand_eq,ih];rfl
def fListLen (ws : List Word) : Nat :=
 List.rec 0 (fun _ _ n=>Nat.add n 1) ws
theorem fListLen_eq (ws : List Word) : fListLen ws=ws.length:=by
  induction ws with
  | nil=>rfl
  | cons _ _ ih=>change fListLen _+1=_;rw [ih];rfl
def fDedup (ws : List Word) : List Word :=
 List.rec [] (fun w _ rest => @Bool.rec (fun _=>List Word) (w :: rest) rest (fContains w rest)) ws
theorem fDedup_mem {w : Word} {ws : List Word} : w ∈ fDedup ws ↔ w ∈ ws:=by
  induction ws with
  | nil=>simp [fDedup]
  | cons a ws ih =>
    change w ∈ @Bool.rec (fun _=>List Word) (a :: fDedup ws) (fDedup ws) (fContains a (fDedup ws)) ↔ _
    rw [fContains_eq]
    cases hc : (fDedup ws).contains a
    · simp [ih]
    · have ha : a ∈ fDedup ws:=List.contains_iff_mem.mp hc
      constructor
      · intro hw;exact List.mem_cons_of_mem a (ih.mp hw)
      · intro hw
        rcases List.mem_cons.mp hw with rfl | htail
        · exact ha
        · exact ih.mpr htail
theorem fDedup_nodup (ws : List Word) : (fDedup ws).Nodup:=by
  induction ws with
  | nil=>exact List.nodup_nil
  | cons a ws ih =>
    change (@Bool.rec (fun _=>List Word) (a :: fDedup ws) (fDedup ws) (fContains a (fDedup ws))).Nodup
    rw [fContains_eq]
    cases hc : (fDedup ws).contains a
    · refine List.nodup_cons.mpr ⟨?_,ih⟩
      intro hm;have:=List.contains_iff_mem.mpr hm;rw [hc] at this;exact Bool.noConfusion this
    · exact ih
def fTestBit (w i : Word) : Bool :=
 fBnot (Nat.beq (Nat.land (Nat.shiftRight w i) 1) 0)
theorem fTestBit_eq (w i : Word) : fTestBit w i=w.testBit i:=by
  unfold fTestBit;rw [fBnot_eq];exact PackedRect.tb_eq w i
def fUnpack (packed width index : Nat) : Nat :=
 Nat.land (Nat.shiftRight packed (Nat.mul width index)) (Nat.sub (Nat.shiftLeft 1 width) 1)
theorem fUnpack_eq (packed width index : Nat) : fUnpack packed width index=unpack packed width index:=rfl
def fDecodeNode (parentWidth width packed index : Nat) : Nat × Nat :=
 fForce (fUnpack packed width index) fun entry =>
 (Nat.land entry (Nat.sub (Nat.shiftLeft 1 parentWidth) 1),Nat.shiftRight entry parentWidth)
def fSortedMaskedAux (mask : Word) (ws : List Word) : Word → Bool :=
 List.rec (motive:=fun _=>Word → Bool) (fun _=>true)
 (fun w _ next p=>fBand (Nat.blt p w) (fBand (Nat.beq (Nat.land w mask) w) (next w))) ws
def fSortedMasked (mask : Word) (ws : List Word) : Bool :=
 List.rec true (fun w tail _=>fBand (Nat.beq (Nat.land w mask) w) (fSortedMaskedAux mask tail w)) ws
theorem fSortedMaskedAux_spec {mask : Word} {ws : List Word} {p : Word}
    (h : fSortedMaskedAux mask ws p=true) :
    (∀ w ∈ ws,p < w) ∧ ws.Nodup ∧ (∀ w ∈ ws,Masked mask w):=by
  induction ws generalizing p with
  | nil=>exact ⟨by simp,List.nodup_nil,by simp⟩
  | cons a ws ih =>
    change fBand (Nat.blt p a) (fBand (Nat.beq (Nat.land a mask) a) (fSortedMaskedAux mask ws a))=true at h
    rw [fBand_eq,fBand_eq,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq,Nat.beq_eq] at h
    obtain ⟨hpa,ham,hrest⟩:=h
    obtain ⟨hlt,hnd,hms⟩:=ih hrest
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hpa
      · exact Nat.lt_trans hpa (hlt w hw)
    · refine List.nodup_cons.mpr ⟨?_,hnd⟩
      intro hm;exact Nat.lt_irrefl a (hlt a hm)
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ham
      · exact hms w hw
theorem fSortedMasked_spec {mask : Word} {ws : List Word} (h : fSortedMasked mask ws=true) :
    ws.Nodup ∧ ∀ w ∈ ws,Masked mask w:=by
  cases ws with
  | nil=>exact ⟨List.nodup_nil,by simp⟩
  | cons a ws =>
    change fBand (Nat.beq (Nat.land a mask) a) (fSortedMaskedAux mask ws a)=true at h
    rw [fBand_eq,Bool.and_eq_true,Nat.beq_eq] at h
    obtain ⟨hlt,hnd,hms⟩:=fSortedMaskedAux_spec h.2
    refine ⟨List.nodup_cons.mpr ⟨fun hm=>Nat.lt_irrefl a (hlt a hm),hnd⟩, ?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact h.1
    · exact hms w hw
def fMixStep (m : WordMoveStep) (w : Word) : Word :=
  fForce w fun w =>
    let left:=List.rec 0 (fun p _ acc=>Nat.lor (Nat.shiftLeft (Nat.land w p.1) p.2) acc) m.1
    let right:=List.rec 0 (fun p _ acc=>Nat.lor (Nat.shiftRight (Nat.land w p.1) p.2) acc) m.2
    Nat.lor left right
theorem fMixStep_eq (m : WordMoveStep) (w : Word) : fMixStep m w=mixStep m w:=by
  unfold fMixStep mixStep;rw [fForce_eq];rfl
def fMixMove (move : WordMove) (w : Word) : Word :=
 (List.rec (motive:=fun _=>Word → Word) (fun v=>v)
 (fun step _ next v=>fForce (fMixStep step v) next) move) w
theorem fMixMove_eq (move : WordMove) (w : Word) : fMixMove move w=mixMove move w:=by
  induction move generalizing w with
  | nil=>rfl
  | cons s ss ih =>
    change fForce (fMixStep s w) (fMixMove ss)=mixMove ss (mixStep s w)
    rw [fForce_eq,fMixStep_eq,ih]
def fDagMoveWords (m : WordMove) (ws : List Word) : List Word :=
 List.rec [] (fun w _ next=>fInsert (fMixMove m w) next) ws
theorem fDagMoveWords_eq (m : WordMove) (ws : List Word) : fDagMoveWords m ws=dagMoveWords m ws:=by
  induction ws with
  | nil=>rfl
  | cons w ws ih =>
    change fInsert (fMixMove m w) (fDagMoveWords m ws)=insertWord (mixMove m w) (dagMoveWords m ws)
    rw [fInsert_eq,fMixMove_eq,ih]
noncomputable def fDagMoveWordsTerm : {f : WordMove → List Word → List Word // f=fDagMoveWords}:=by
  refine ⟨?f, ?proof⟩
  case proof =>
    delta fDagMoveWords fInsert fMixMove fMixStep
    beta_reduce
    exact rfl
noncomputable def fDagMoveWordsRun : WordMove → List Word → List Word:=fDagMoveWordsTerm.1
theorem fDagMoveWordsRun_eq (m : WordMove) (ws : List Word) : fDagMoveWordsRun m ws=dagMoveWords m ws :=
  (congrFun (congrFun fDagMoveWordsTerm.2 m) ws).trans (fDagMoveWords_eq m ws)
def fKeepWord (save : Bool) (w : Word) (ws : List Word) : List Word :=
 @Bool.rec (fun _=>List Word) (fErase w ws) ws save
theorem fKeepWord_eq (save : Bool) (w : Word) (ws : List Word) : fKeepWord save w ws=keepWord save w ws:=by
  cases save
  · exact fErase_eq w ws
  · rfl
def fGateWord (mask op x y : Word) : Word :=
 @Bool.rec (fun _=>Word)
 (@Bool.rec (fun _=>Word) (Nat.xor mask x) (Nat.lor x y) (Nat.beq op 1))
 (Nat.land x y) (Nat.beq op 0)
theorem fGateWord_eq (mask op x y : Word) : fGateWord mask op x y=dagGateWord1 mask op x y:=by
  unfold fGateWord dagGateWord1
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> rfl
def fTagKeep (keep : Bool) (w : Word) (bank : List DagTagged1) : List DagTagged1 :=
 @Bool.rec (fun _=>List DagTagged1)
 (List.rec [] (fun tag tail next => @Bool.rec (fun _=>List DagTagged1) (tag :: next) tail (Nat.beq tag.1 w)) bank)
 bank keep
def fTagInsert (tag : DagTagged1) (bank : List DagTagged1) : List DagTagged1 :=
 List.rec [tag] (fun old tail next => @Bool.rec (fun _=>List DagTagged1) (old :: next) (tag :: old :: tail) (Nat.ble tag.1 old.1)) bank
def fTagStep (mask full token : Word) (bank : List DagTagged1) : List DagTagged1 :=
  fForce (Nat.mod token 4) fun keep =>
    fForce (Nat.mod (Nat.div token 4) 3) fun op =>
      let x:=fGetDTagged bank (Nat.div token 768)
      let y:=fGetDTagged bank (Nat.mod (Nat.div token 12) 64)
      fForce (fGateWord mask op x.1 y.1) fun w =>
        fForce (fGateWord full op x.2.1 y.2.1) fun up =>
          fForce (fGateWord full op x.2.2 y.2.2) fun dn =>
            fTagInsert (w,up,dn)
              (fTagKeep (fBor (Nat.beq op 2) (fTestBit keep 1)) y.1
                (fTagKeep (fTestBit keep 0) x.1 bank))
noncomputable def fTagStepTerm : {f : Word → Word → Word → List DagTagged1 → List DagTagged1 // f=fTagStep}:=by
  refine ⟨?f, ?proof⟩
  case proof =>
    delta fTagStep fTagInsert fTagKeep fGetDTagged fGateWord fTestBit fBor fBnot
    beta_reduce
    exact rfl
def fTagRoot (bank : List DagTagged1) (token : Nat) : List DagTagged1 :=
 (List.rec (motive:=fun _=>Nat → List DagTagged1) (fun _=>[])
 (fun tag _ next k =>
 fForce (Nat.shiftRight k 1) fun hi =>
 @Bool.rec (fun _=>List DagTagged1) (tag :: next hi) (next hi) (Nat.beq (Nat.land k 1) 0)) bank) token
noncomputable def fDagTraceTags (mask width : Word) (root : List DagTagged1) (fuel : Nat) (forest : Forest)
    (i : Nat) : List DagSignals1 :=
  let full:=Nat.sub (Nat.shiftLeft 1 width) 1
  let tags:=(Nat.rec (motive:=fun _=>Nat → List DagTagged1) (fun _=>[])
    (fun _ previous j =>
      let pt:=forest j
      fForce pt.1 fun parent =>
        fForce pt.2 fun token =>
          @Bool.rec (fun _=>List DagTagged1)
            (fForce (Nat.sub parent 1) fun p1=>fTagStepTerm.1 mask full token (previous p1))
            (fTagRoot root token)
            (Nat.beq parent 0)) (Nat.add fuel 1)) i
  List.rec [] (fun tag _ rest=>tag.2 :: rest) tags
def fChildState (mask token : Nat) (state : RowState1) : Option RowState1 :=
  let (fuel,nots,ws,history):=state
  fForce (Nat.mod token 4) fun keep =>
    fForce (Nat.mod (Nat.div token 4) 3) fun op =>
      fForce (Nat.div token 768) fun a =>
        fForce (Nat.mod (Nat.div token 12) 64) fun b =>
          let badOp := @Bool.rec (fun _=>Bool)
            (Nat.ble b a)
            (fBor (fBnot (Nat.beq a b)) (fBor (Nat.ble 2 keep) (Nat.beq nots 0)))
            (Nat.beq op 2)
          @Bool.rec (fun _=>Option RowState1)
            (fForce (fGetD ws a) fun x =>
              fForce (fGetD ws b) fun y =>
                fForce (fGateWord mask op x y) fun w =>
                  @Bool.rec (fun _=>Option RowState1)
                    (let kp0:=fTestBit keep 0
                     let kp1:=fBor (Nat.beq op 2) (fTestBit keep 1)
                     let nextNots := @Bool.rec (fun _=>Nat) nots (Nat.sub nots 1) (Nat.beq op 2)
                     fForce (Nat.sub fuel 1) fun nf =>
                       fForce nextNots fun nn =>
                         fForceWords (fInsert w (fKeepWord kp1 y (fKeepWord kp0 x ws))) fun nws =>
                           some (nf,nn,nws,(w,x,y) :: history))
                    none
                    (fBor (Nat.beq w 0) (fBor (Nat.beq w mask) (fContains w ws))))
            none
            (fBor (Nat.beq fuel 0) (fBor (Nat.ble (fListLen ws) b) badOp))
theorem fChildState_eq (mask token : Nat) (state : RowState1) :
    fChildState mask token state=childState1 mask token state:=by
  obtain ⟨fuel,nots,ws,history⟩:=state
  unfold fChildState childState1
  simp only [fForce_eq,fForceWords_eq,fBor_eq,fBnot_eq,fGetD_eq,fGateWord_eq,
    fContains_eq,fTestBit_eq,fInsert_eq,fKeepWord_eq,fListLen_eq,dagGateWord1,keepWord]
  rw [show Nat.div token 768=token / (4*3*64) from rfl,
      show Nat.mod (Nat.div token 12) 64=token / (4*3) % 64 from rfl,
      show Nat.mod (Nat.div token 4) 3=token / 4 % 3 from rfl,
      show Nat.mod token 4=token % 4 from rfl]
  have hbad : (Nat.beq fuel 0||(Nat.ble ws.length (token / (4*3) % 64) ||
      @Bool.rec (fun _=>Bool) (Nat.ble (token / (4*3) % 64) (token / (4*3*64)))
        (!Nat.beq (token / (4*3*64)) (token / (4*3) % 64)||(Nat.ble 2 (token % 4)||Nat.beq nots 0))
        (Nat.beq (token / 4 % 3) 2))) =
      ((fuel==0)||decide (token / (4*3) % 64 ≥ ws.length) ||
        if (token / 4 % 3==2)=true then
          ((token / (4*3*64) != token / (4*3) % 64)||decide (token % 4 ≥ 2)||(nots==0))
        else decide (token / (4*3*64) ≥ token / (4*3) % 64)):=by
    rw [fNatBle_iff_le,fNatBle_iff_le,fNatBle_iff_le,fNatBeq_iff_beq,fNatBeq_iff_beq,fNatBeq_iff_beq,fNatBeq_iff_beq]
    cases (token / 4 % 3==2) <;> simp [bne,Bool.or_assoc]
  cases hb : (Nat.beq fuel 0||(Nat.ble ws.length (token / (4*3) % 64) ||
      @Bool.rec (fun _=>Bool) (Nat.ble (token / (4*3) % 64) (token / (4*3*64)))
        (!Nat.beq (token / (4*3*64)) (token / (4*3) % 64)||(Nat.ble 2 (token % 4)||Nat.beq nots 0))
        (Nat.beq (token / 4 % 3) 2)))
  · have hb2:=hbad.symm.trans hb
    rw [hb2];simp only [Bool.false_eq_true, ↓reduceIte]
    have hweq : (if Nat.beq (token / 4 % 3) 0=true then ws.getD (token / (4*3*64)) 0&&&ws.getD (token / (4*3) % 64) 0
        else if Nat.beq (token / 4 % 3) 1=true then ws.getD (token / (4*3*64)) 0|||ws.getD (token / (4*3) % 64) 0
        else mask^^^ws.getD (token / (4*3*64)) 0) =
        (if (token / 4 % 3==0)=true then ws.getD (token / (4*3*64)) 0&&&ws.getD (token / (4*3) % 64) 0
        else if (token / 4 % 3==1)=true then ws.getD (token / (4*3*64)) 0|||ws.getD (token / (4*3) % 64) 0
        else mask^^^ws.getD (token / (4*3*64)) 0):=rfl
    rw [hweq]
    generalize (if (token / 4 % 3==0)=true then ws.getD (token / (4*3*64)) 0&&&ws.getD (token / (4*3) % 64) 0
        else if (token / 4 % 3==1)=true then ws.getD (token / (4*3*64)) 0|||ws.getD (token / (4*3) % 64) 0
        else mask^^^ws.getD (token / (4*3*64)) 0)=w
    have hst : (Nat.beq w 0||(Nat.beq w mask||ws.contains w))=((w==0)||(w==mask)||ws.contains w):=by
      rw [fNatBeq_iff_beq,fNatBeq_iff_beq,Bool.or_assoc]
    rw [hst]
    cases (w==0)||(w==mask)||ws.contains w
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [fNatBeq_iff_beq]
      cases (token / 4 % 3==2) <;> rfl
    · rfl
  · rw [hbad.symm.trans hb];rfl
noncomputable def fChildStateTerm : {f : Nat → Nat → RowState1 → Option RowState1 // f=fChildState}:=by
  refine ⟨?f, ?proof⟩
  case proof =>
    delta fChildState fGateWord fKeepWord fInsert fErase fContains fGetD fListLen fTestBit fBor fBand fBnot
    beta_reduce
    exact rfl
noncomputable def fChildStateRun : Nat → Nat → RowState1 → Option RowState1:=fChildStateTerm.1
theorem fChildStateRun_eq (mask token : Nat) (state : RowState1) :
    fChildStateRun mask token state=childState1 mask token state :=
  (congrFun (congrFun (congrFun fChildStateTerm.2 mask) token) state).trans (fChildState_eq mask token state)
abbrev LightState1:=Nat × Nat × List Word
def fChildLight (mask token : Nat) (state : LightState1) : Option LightState1 :=
  let (fuel,nots,ws):=state
  fForce (Nat.mod token 4) fun keep =>
    fForce (Nat.mod (Nat.div token 4) 3) fun op =>
      fForce (Nat.div token 768) fun a =>
        fForce (Nat.mod (Nat.div token 12) 64) fun b =>
          let badOp := @Bool.rec (fun _=>Bool)
            (Nat.ble b a)
            (fBor (fBnot (Nat.beq a b)) (fBor (Nat.ble 2 keep) (Nat.beq nots 0)))
            (Nat.beq op 2)
          @Bool.rec (fun _=>Option LightState1)
            (fForce (fGetD ws a) fun x =>
              fForce (fGetD ws b) fun y =>
                fForce (fGateWord mask op x y) fun w =>
                  @Bool.rec (fun _=>Option LightState1)
                    (let kp0:=fTestBit keep 0
                     let kp1:=fBor (Nat.beq op 2) (fTestBit keep 1)
                     let nextNots := @Bool.rec (fun _=>Nat) nots (Nat.sub nots 1) (Nat.beq op 2)
                     fForce (Nat.sub fuel 1) fun nf =>
                       fForce nextNots fun nn =>
                         fForceWords (fInsert w (fKeepWord kp1 y (fKeepWord kp0 x ws))) fun nws =>
                           some (nf,nn,nws))
                    none
                    (fBor (Nat.beq w 0) (fBor (Nat.beq w mask) (fContains w ws))))
            none
            (fBor (Nat.beq fuel 0) (fBor (Nat.ble (fListLen ws) b) badOp))
theorem fChildLight_eq (mask token : Nat) (state : RowState1) :
    fChildLight mask token (state.1,state.2.1,state.2.2.1) =
      (fChildState mask token state).map (fun s=>(s.1,s.2.1,s.2.2.1)):=by
  obtain ⟨fuel,nots,ws,history⟩:=state
  unfold fChildLight fChildState
  simp only [fForce_eq,fForceWords_eq]
  cases fBor (Nat.beq fuel 0) (fBor (Nat.ble (fListLen ws) (Nat.mod (Nat.div token 12) 64))
      (@Bool.rec (fun _=>Bool) (Nat.ble (Nat.mod (Nat.div token 12) 64) (Nat.div token 768))
        (fBor (fBnot (Nat.beq (Nat.div token 768) (Nat.mod (Nat.div token 12) 64)))
          (fBor (Nat.ble 2 (Nat.mod token 4)) (Nat.beq nots 0)))
        (Nat.beq (Nat.mod (Nat.div token 4) 3) 2)))
  · dsimp only
    cases fBor (Nat.beq (fGateWord mask (Nat.mod (Nat.div token 4) 3) (fGetD ws (Nat.div token 768)) (fGetD ws (Nat.mod (Nat.div token 12) 64))) 0)
        (fBor (Nat.beq (fGateWord mask (Nat.mod (Nat.div token 4) 3) (fGetD ws (Nat.div token 768)) (fGetD ws (Nat.mod (Nat.div token 12) 64))) mask)
          (fContains (fGateWord mask (Nat.mod (Nat.div token 4) 3) (fGetD ws (Nat.div token 768)) (fGetD ws (Nat.mod (Nat.div token 12) 64))) ws)) <;> rfl
  · rfl
noncomputable def fChildLightTerm : {f : Nat → Nat → LightState1 → Option LightState1 // f=fChildLight}:=by
  refine ⟨?f, ?proof⟩
  case proof =>
    delta fChildLight fGateWord fKeepWord fInsert fErase fContains fGetD fListLen fTestBit fBor fBand fBnot
    beta_reduce
    exact rfl
noncomputable def fChildLightRun : Nat → Nat → LightState1 → Option LightState1:=fChildLightTerm.1
theorem fChildLightRun_eq (mask token : Nat) (state : RowState1) :
    fChildLightRun mask token (state.1,state.2.1,state.2.2.1) =
      (childState1 mask token state).map (fun s=>(s.1,s.2.1,s.2.2.1)):=by
  rw [show fChildLightRun=fChildLight from fChildLightTerm.2,fChildLight_eq,fChildState_eq]
def fRootWords (base : List Word) (token : Nat) : List Word :=
 (List.rec (motive:=fun _=>Nat → List Word) (fun _=>[])
 (fun word _ next bits =>
 fForce (Nat.shiftRight bits 1) fun hi =>
 @Bool.rec (fun _=>List Word) (word :: next hi) (next hi) (Nat.beq (Nat.land bits 1) 0)) base) token
theorem fRootWords_eq (base : List Word) (token : Nat) : fRootWords base token=rootWords base token:=by
  induction base generalizing token with
  | nil=>rfl
  | cons w ws ih =>
    change fForce (Nat.shiftRight token 1) (fun hi =>
      @Bool.rec (fun _=>List Word) (w :: fRootWords ws hi) (fRootWords ws hi) (Nat.beq (Nat.land token 1) 0)) =
      if (token&&&1==0)=true then rootWords ws (token>>>1) else w :: rootWords ws (token>>>1)
    rw [fForce_eq,ih]
    have hq : Nat.beq (Nat.land token 1) 0=(token&&&1==0):=rfl
    rw [hq]
    cases (token&&&1==0) <;> rfl
def dagTraceN (mask : Word) (stock : List Word) (fuel initNots : Nat) (forest : Forest) (n : Nat) :
    Nat → Option RowState1 :=
  Nat.rec (motive:=fun _=>Nat → Option RowState1) (fun _=>none)
    (fun _ previous j =>
      let (parent,token):=forest j
      if parent==0 then
        if token < 2 ^ stock.length then some (rootState1 stock fuel initNots token) else none
      else (previous (parent - 1)).bind (childState1 mask token)) n
theorem childState1_fuel {mask token : Nat} {s child : RowState1}
    (h : childState1 mask token s=some child) : 0 < s.1 ∧ child.1=s.1 - 1:=by
  obtain ⟨fuel,nots,ws,history⟩:=s
  let keep:=token % 4
  let op:=token / 4 % 3
  let a:=token / (4*3*64)
  let b:=token / (4*3) % 64
  let x:=ws.getD a 0
  let y:=ws.getD b 0
  let w:=if op==0 then x&&&y else if op==1 then x|||y else mask^^^x
  let bad : Bool:=fuel==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b)
  let stale : Bool:=w==0||w==mask||ws.contains w
  change (if bad then none else if stale then none else
    some (fuel - 1,if op==2 then nots - 1 else nots,
      insertWord w (if op==2||keep.testBit 1 then (if keep.testBit 0 then ws else ws.erase x) else (if keep.testBit 0 then ws else ws.erase x).erase y),
      (w,x,y) :: history))=some child at h
  by_cases hb : bad=true
  · simp [hb] at h
  by_cases hs : stale=true
  · simp [hb,hs] at h
  have heq : (fuel - 1,if op==2 then nots - 1 else nots,
      insertWord w (if op==2||keep.testBit 1 then (if keep.testBit 0 then ws else ws.erase x) else (if keep.testBit 0 then ws else ws.erase x).erase y),
      (w,x,y) :: history)=child:=by simpa [hb,hs] using h
  have hpos : 0 < fuel:=by
    by_contra! hz
    have h0 : fuel=0:=by omega
    exact hb (by simp [bad,h0])
  exact ⟨hpos,by rw [← heq]⟩
theorem dagTraceN_mono {mask : Word} {stock : List Word} {fuel initNots : Nat} {forest : Forest}
    {n m j : Nat} {st : RowState1} (hle : n ≤ m)
    (h : dagTraceN mask stock fuel initNots forest n j=some st) :
    dagTraceN mask stock fuel initNots forest m j=some st:=by
  induction n generalizing m j st with
  | zero=>simp [dagTraceN] at h
  | succ n ih =>
    cases m with
    | zero=>omega
    | succ m =>
      change (if (forest j).1==0 then
        if (forest j).2 < 2 ^ stock.length then some (rootState1 stock fuel initNots (forest j).2) else none
        else (dagTraceN mask stock fuel initNots forest n ((forest j).1 - 1)).bind (childState1 mask (forest j).2))=some st at h
      change (if (forest j).1==0 then
        if (forest j).2 < 2 ^ stock.length then some (rootState1 stock fuel initNots (forest j).2) else none
        else (dagTraceN mask stock fuel initNots forest m ((forest j).1 - 1)).bind (childState1 mask (forest j).2))=some st
      by_cases hp : ((forest j).1==0)=true
      · simpa [hp] using h
      · simp only [hp,Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hprev : dagTraceN mask stock fuel initNots forest n ((forest j).1 - 1) with
        | none=>rw [hprev] at h;simp at h
        | some pst =>
          rw [hprev] at h
          rw [ih (by omega) hprev]
          exact h
theorem dagTraceN_tight {mask : Word} {stock : List Word} {fuel initNots : Nat} {forest : Forest}
    {n j : Nat} {st : RowState1}
    (h : dagTraceN mask stock fuel initNots forest n j=some st) :
    st.1 ≤ fuel ∧ dagTraceN mask stock fuel initNots forest (fuel+1 - st.1) j=some st:=by
  induction n generalizing j st with
  | zero=>simp [dagTraceN] at h
  | succ n ih =>
    change (if (forest j).1==0 then
      if (forest j).2 < 2 ^ stock.length then some (rootState1 stock fuel initNots (forest j).2) else none
      else (dagTraceN mask stock fuel initNots forest n ((forest j).1 - 1)).bind (childState1 mask (forest j).2))=some st at h
    by_cases hp : ((forest j).1==0)=true
    · simp only [hp, ↓reduceIte] at h
      by_cases ht : (forest j).2 < 2 ^ stock.length
      · simp only [ht, ↓reduceIte,Option.some.injEq] at h
        subst st
        refine ⟨Nat.le_refl _, ?_⟩
        have h1 : fuel+1 - fuel=1:=by omega
        change dagTraceN mask stock fuel initNots forest (fuel+1 - fuel) j=_
        rw [h1]
        change (if (forest j).1==0 then
          if (forest j).2 < 2 ^ stock.length then some (rootState1 stock fuel initNots (forest j).2) else none else _)=_
        simp [hp,ht]
      · simp [ht] at h
    · simp only [hp,Bool.false_eq_true, ↓reduceIte] at h
      cases hprev : dagTraceN mask stock fuel initNots forest n ((forest j).1 - 1) with
      | none=>rw [hprev] at h;simp at h
      | some pst =>
        rw [hprev] at h
        obtain ⟨hpLe,hpTight⟩:=ih hprev
        obtain ⟨hpPos,hsEq⟩:=childState1_fuel h
        refine ⟨by omega, ?_⟩
        have hstep : fuel+1 - st.1=(fuel+1 - pst.1)+1:=by omega
        rw [hstep]
        change (if (forest j).1==0 then _
          else (dagTraceN mask stock fuel initNots forest (fuel+1 - pst.1) ((forest j).1 - 1)).bind (childState1 mask (forest j).2))=some st
        simp only [hp,Bool.false_eq_true, ↓reduceIte,hpTight]
        exact h
theorem dagTrace1_treeChild {mask : Word} {stock : List Word} {fuel initNots i dest token : Nat}
    {forest : Forest} {s child : RowState1}
    (hs : dagTrace1 mask stock fuel initNots forest i=some s)
    (heval : childState1 mask token s=some child)
    (hfor : forest dest=(i+1,token)) :
    dagTrace1 mask stock fuel initNots forest dest=some child:=by
  obtain ⟨hLe,hTight⟩:=dagTraceN_tight (show dagTraceN mask stock fuel initNots forest (fuel+1) i=some s from hs)
  obtain ⟨hPos,_⟩:=childState1_fuel heval
  have hFuel : dagTraceN mask stock fuel initNots forest fuel i=some s :=
    dagTraceN_mono (by omega) hTight
  change (if (forest dest).1==0 then _
    else (dagTraceN mask stock fuel initNots forest fuel ((forest dest).1 - 1)).bind (childState1 mask (forest dest).2))=some child
  rw [hfor]
  have hne : ((i+1 : Nat)==0)=false:=rfl
  simp only [hne,Bool.false_eq_true, ↓reduceIte,Nat.add_sub_cancel,hFuel]
  exact heval
theorem dagTrace1_treeRoot {mask : Word} {stock : List Word} {fuel initNots dest token : Nat}
    {forest : Forest} (ht : token < 2 ^ stock.length) (hfor : forest dest=(0,token)) :
    dagTrace1 mask stock fuel initNots forest dest=some (rootState1 stock fuel initNots token):=by
  change (if (forest dest).1==0 then
    if (forest dest).2 < 2 ^ stock.length then some (rootState1 stock fuel initNots (forest dest).2) else none else _)=_
  rw [hfor]
  simp [ht]
noncomputable def fDagTrace (mask : Word) (stock : List Word) (fuel initNots : Nat) (forest : Forest)
    (i : Nat) : Option RowState1 :=
  let lim:=Nat.shiftLeft 1 (fListLen stock)
  (Nat.rec (motive:=fun _=>Nat → Option RowState1) (fun _=>none)
    (fun _ previous j =>
      let pt:=forest j
      fForce pt.1 fun parent =>
        fForce pt.2 fun token =>
          @Bool.rec (fun _=>Option RowState1)
            (fForce (Nat.sub parent 1) fun p1 =>
              @Option.rec RowState1 (fun _=>Option RowState1) none (fChildStateRun mask token) (previous p1))
            (@Bool.rec (fun _=>Option RowState1) none (some (fuel,initNots,fRootWords stock token,[]))
              (Nat.blt token lim))
            (Nat.beq parent 0)) (Nat.add fuel 1)) i
theorem fDagTrace_eq (mask : Word) (stock : List Word) (fuel initNots : Nat) (forest : Forest) (i : Nat) :
    fDagTrace mask stock fuel initNots forest i=dagTrace1 mask stock fuel initNots forest i:=by
  have hlim : Nat.shiftLeft 1 (fListLen stock)=2 ^ stock.length:=by
    rw [fListLen_eq]
    change 1<<<stock.length=2 ^ stock.length
    rw [Nat.shiftLeft_eq,Nat.one_mul]
  suffices h : ∀ n j,
      (Nat.rec (motive:=fun _=>Nat → Option RowState1) (fun _=>none)
        (fun _ previous j =>
          let pt:=forest j
          fForce pt.1 fun parent =>
            fForce pt.2 fun token =>
              @Bool.rec (fun _=>Option RowState1)
                (fForce (Nat.sub parent 1) fun p1 =>
                  @Option.rec RowState1 (fun _=>Option RowState1) none (fChildStateRun mask token) (previous p1))
                (@Bool.rec (fun _=>Option RowState1) none (some (fuel,initNots,fRootWords stock token,[]))
                  (Nat.blt token (Nat.shiftLeft 1 (fListLen stock))))
                (Nat.beq parent 0)) n) j =
      dagTraceN mask stock fuel initNots forest n j from h (fuel+1) i
  intro n
  induction n with
  | zero=>intro _;rfl
  | succ n ih =>
    intro j
    change _=(if (forest j).1==0 then
      if (forest j).2 < 2 ^ stock.length then some (rootState1 stock fuel initNots (forest j).2) else none
      else (dagTraceN mask stock fuel initNots forest n ((forest j).1 - 1)).bind (childState1 mask (forest j).2))
    dsimp only
    rw [fForce_eq,fForce_eq]
    cases hp : Nat.beq (forest j).1 0
    · dsimp only
      rw [fForce_eq,ih]
      have hne : ((forest j).1==0)=false:=hp
      simp only [hne,Bool.false_eq_true, ↓reduceIte]
      cases dagTraceN mask stock fuel initNots forest n ((forest j).1 - 1) with
      | none=>rfl
      | some st=>exact fChildStateRun_eq mask (forest j).2 st
    · dsimp only
      have heq : ((forest j).1==0)=true:=hp
      simp only [heq, ↓reduceIte,hlim,fRootWords_eq,rootState1]
      cases hlt : Nat.blt (forest j).2 (2 ^ stock.length)
      · have : ¬ (forest j).2 < 2 ^ stock.length:=fun h=>Bool.noConfusion ((Nat.blt_eq.mpr h).symm.trans hlt)
        simp [this]
      · simp [Nat.blt_eq.mp hlt]
noncomputable def fDagTraceLight (mask : Word) (stock : List Word) (fuel initNots : Nat) (forest : Forest)
    (i : Nat) : Option LightState1 :=
  let lim:=Nat.shiftLeft 1 (fListLen stock)
  (Nat.rec (motive:=fun _=>Nat → Option LightState1) (fun _=>none)
    (fun _ previous j =>
      let pt:=forest j
      fForce pt.1 fun parent =>
        fForce pt.2 fun token =>
          @Bool.rec (fun _=>Option LightState1)
            (fForce (Nat.sub parent 1) fun p1 =>
              @Option.rec LightState1 (fun _=>Option LightState1) none (fChildLightRun mask token) (previous p1))
            (@Bool.rec (fun _=>Option LightState1) none (some (fuel,initNots,fRootWords stock token))
              (Nat.blt token lim))
            (Nat.beq parent 0)) (Nat.add fuel 1)) i
theorem fDagTraceLight_eq (mask : Word) (stock : List Word) (fuel initNots : Nat) (forest : Forest) (i : Nat) :
    fDagTraceLight mask stock fuel initNots forest i =
      (dagTrace1 mask stock fuel initNots forest i).map (fun s=>(s.1,s.2.1,s.2.2.1)):=by
  have hlim : Nat.shiftLeft 1 (fListLen stock)=2 ^ stock.length:=by
    rw [fListLen_eq];change 1<<<stock.length=2 ^ stock.length;rw [Nat.shiftLeft_eq,Nat.one_mul]
  suffices h : ∀ n j,
      (Nat.rec (motive:=fun _=>Nat → Option LightState1) (fun _=>none)
        (fun _ previous j =>
          let pt:=forest j
          fForce pt.1 fun parent =>
            fForce pt.2 fun token =>
              @Bool.rec (fun _=>Option LightState1)
                (fForce (Nat.sub parent 1) fun p1 =>
                  @Option.rec LightState1 (fun _=>Option LightState1) none (fChildLightRun mask token) (previous p1))
                (@Bool.rec (fun _=>Option LightState1) none (some (fuel,initNots,fRootWords stock token))
                  (Nat.blt token (Nat.shiftLeft 1 (fListLen stock))))
                (Nat.beq parent 0)) n) j =
      (dagTraceN mask stock fuel initNots forest n j).map (fun s=>(s.1,s.2.1,s.2.2.1)) from h (fuel+1) i
  intro n
  induction n with
  | zero=>intro _;rfl
  | succ n ih =>
    intro j
    change _=(if (forest j).1==0 then
      if (forest j).2 < 2 ^ stock.length then some (rootState1 stock fuel initNots (forest j).2) else none
      else (dagTraceN mask stock fuel initNots forest n ((forest j).1 - 1)).bind (childState1 mask (forest j).2)).map (fun s=>(s.1,s.2.1,s.2.2.1))
    dsimp only
    rw [fForce_eq,fForce_eq]
    cases hp : Nat.beq (forest j).1 0
    · dsimp only
      rw [fForce_eq,ih]
      have hne : ((forest j).1==0)=false:=hp
      simp only [hne,Bool.false_eq_true, ↓reduceIte]
      cases dagTraceN mask stock fuel initNots forest n ((forest j).1 - 1) with
      | none=>rfl
      | some st=>exact fChildLightRun_eq mask (forest j).2 st
    · dsimp only
      have heq : ((forest j).1==0)=true:=hp
      simp only [heq, ↓reduceIte,hlim,fRootWords_eq,rootState1]
      cases hlt : Nat.blt (forest j).2 (2 ^ stock.length)
      · have : ¬ (forest j).2 < 2 ^ stock.length:=fun h=>Bool.noConfusion ((Nat.blt_eq.mpr h).symm.trans hlt)
        simp [this]
      · simp [Nat.blt_eq.mp hlt]
def fMaskFlat (mask word : Word) : Bool :=
 fForce (Nat.land word mask) fun v=>fBor (Nat.beq v 0) (Nat.beq v mask)
theorem fMaskFlat_eq (mask word : Word) : fMaskFlat mask word=maskFlat mask word:=by
  unfold fMaskFlat maskFlat;rw [fForce_eq,fBor_eq];rfl
def fFlatCount (mask : Word) (ws : List Word) : Nat :=
 List.rec 0 (fun w _ c => @Bool.rec (fun _=>Nat) c (Nat.add c 1) (fMaskFlat mask w)) ws
theorem fFlatCount_eq (mask : Word) (ws : List Word) : fFlatCount mask ws=flatCount mask ws:=by
  induction ws with
  | nil=>rfl
  | cons w ws ih =>
    change @Bool.rec (fun _=>Nat) (fFlatCount mask ws) (Nat.add (fFlatCount mask ws) 1) (fMaskFlat mask w) =
      if maskFlat mask w then flatCount mask ws+1 else flatCount mask ws
    rw [ih,fMaskFlat_eq]
    cases maskFlat mask w <;> rfl
def fAvailableB (mask : Word) (bank : List Word) (w : Word) : Bool :=
 fBor (Nat.beq w 0) (fBor (Nat.beq w mask) (fContains w bank))
theorem fAvailableB_eq (mask : Word) (bank : List Word) (w : Word) :
    fAvailableB mask bank w=availableB mask bank w:=by
  unfold fAvailableB availableB
  rw [fBor_eq,fBor_eq,fContains_eq,fNatBeq_iff_beq,fNatBeq_iff_beq,Bool.or_assoc]
def fStockWord (mask : Word) (stock needed : List Word) (word : Word) : List Word :=
 fForce (Nat.land word mask) fun v =>
 @Bool.rec (fun _=>List Word) (v :: needed) needed
 (fBor (Nat.beq v 0) (fBor (Nat.beq v mask) (fBor (fContains v stock) (fContains v needed))))
theorem fStockWord_eq (mask : Word) (stock needed : List Word) (word : Word) :
    fStockWord mask stock needed word=stockWord mask stock needed word:=by
  unfold fStockWord stockWord
  rw [fForce_eq,fBor_eq,fBor_eq,fBor_eq,fContains_eq,fContains_eq]
  have h : (Nat.beq (Nat.land word mask) 0||(Nat.beq (Nat.land word mask) mask ||
      (stock.contains (Nat.land word mask)||needed.contains (Nat.land word mask)))) =
      ((word&&&mask==0)||(word&&&mask==mask)||stock.contains (word&&&mask)||needed.contains (word&&&mask)):=by
    rw [fNatBeq_iff_beq,fNatBeq_iff_beq,Bool.or_assoc,Bool.or_assoc];rfl
  rw [h]
  change @Bool.rec (fun _=>List Word) ((word&&&mask) :: needed) needed ((word&&&mask==0)||(word&&&mask==mask)||stock.contains (word&&&mask)||needed.contains (word&&&mask)) =
    if ((word&&&mask==0)||(word&&&mask==mask)||stock.contains (word&&&mask)||needed.contains (word&&&mask)) then needed else (word&&&mask) :: needed
  cases ((word&&&mask==0)||(word&&&mask==mask)||stock.contains (word&&&mask)||needed.contains (word&&&mask)) <;> rfl
def fRecipeStart (mask : Word) (stock words : List Word) : List Word :=
 (List.rec (motive:=fun _=>List Word → List Word) (fun s=>s)
 (fun word _ next seen=>next (fStockWord mask stock seen word)) words) []
theorem fRecipeStart_eq (mask : Word) (stock words : List Word) :
    fRecipeStart mask stock words=recipeStart mask stock words:=by
  suffices h : ∀ seen,
      (List.rec (motive:=fun _=>List Word → List Word) (fun s=>s)
        (fun word _ next seen=>next (fStockWord mask stock seen word)) words) seen =
      (List.rec (motive:=fun _=>List Word → List Word) id
        (fun word _ next seen=>next (stockWord mask stock seen word)) words) seen from h []
  induction words with
  | nil=>intro _;rfl
  | cons w ws ih=>intro seen;dsimp only;rw [fStockWord_eq];exact ih _
def fRecipeClosure (mask : Word) (stock : List Word) (history : List (Word × Word × Word))
 (start : List Word) : List Word :=
 (List.rec (motive:=fun _=>List Word → List Word) (fun s=>s)
 (fun rec _ next seen =>
 fForce (Nat.land rec.1 mask) fun vm =>
 next (@Bool.rec (fun _=>List Word) seen
 (fStockWord mask stock (fStockWord mask stock seen rec.2.1) rec.2.2) (fContains vm seen))) history) start
theorem fRecipeClosure_eq (mask : Word) (stock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : fRecipeClosure mask stock history start=recipeClosure mask stock history start:=by
  induction history generalizing start with
  | nil=>rfl
  | cons rec rest ih =>
    obtain ⟨out,a,b⟩:=rec
    change fForce (Nat.land out mask) (fun vm =>
      fRecipeClosure mask stock rest (@Bool.rec (fun _=>List Word) start
        (fStockWord mask stock (fStockWord mask stock start a) b) (fContains vm start))) =
      recipeClosure mask stock rest (if start.contains (out&&&mask) then stockWord mask stock (stockWord mask stock start a) b else start)
    rw [fForce_eq,fContains_eq,fStockWord_eq,fStockWord_eq,ih]
    cases start.contains (out&&&mask) <;> rfl
def fListRev {α : Type} (xs : List α) : List α :=
 (List.rec (motive:=fun _=>List α → List α) (fun acc=>acc) (fun x _ next acc=>next (x :: acc)) xs) []
theorem fListRev_eq {α : Type} (xs : List α) : fListRev xs=xs.reverse:=by
  suffices h : ∀ acc,
      (List.rec (motive:=fun _=>List α → List α) (fun acc=>acc) (fun x _ next acc=>next (x :: acc)) xs) acc =
      xs.reverse ++ acc by
    have h0:=h []
    simpa [fListRev] using h0
  induction xs with
  | nil=>intro _;rfl
  | cons x xs ih=>intro acc;dsimp only;rw [ih];simp
def fRecipeGateBin (mask : Word) (bank : List Word) (v a b : Word) : Bool :=
 fBand (fAvailableB mask bank a)
 (fBand (fAvailableB mask bank b) (fBor (Nat.beq v (Nat.land a b)) (Nat.beq v (Nat.lor a b))))
theorem fRecipeGateBin_eq (mask : Word) (bank : List Word) (v a b : Word) :
    fRecipeGateBin mask bank v a b=recipeGateBin mask bank v a b:=by
  unfold fRecipeGateBin recipeGateBin
  rw [fBand_eq,fBand_eq,fBor_eq,fAvailableB_eq,fAvailableB_eq,fNatBeq_iff_beq,fNatBeq_iff_beq,Bool.and_assoc];rfl
def fReplayRecipesExact (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) (notsLeft : Nat) : List Word × Nat :=
  (List.rec (motive:=fun _=>List Word → Nat → List Word × Nat) (fun _ _=>([],0))
    (fun rec _ next bank nl =>
      fForce (Nat.land rec.1 mask) fun v =>
        @Bool.rec (fun _=>List Word × Nat) (next bank nl)
          (fForce (Nat.land rec.2.1 mask) fun am =>
            fForce (Nat.land rec.2.2 mask) fun bm =>
              @Bool.rec (fun _=>List Word × Nat)
                (@Bool.rec (fun _=>List Word × Nat) (next bank nl)
                  (let r:=next (v :: bank) (Nat.sub nl 1);(v :: r.1,Nat.add r.2 1))
                  (fBand (Nat.blt 0 nl) (fBand (fAvailableB mask bank am) (Nat.beq v (Nat.xor mask am)))))
                (let r:=next (v :: bank) nl;(v :: r.1,r.2))
                (fRecipeGateBin mask bank v am bm))
          (fBand (fContains v needed) (fBnot (fAvailableB mask bank v)))) recipes) bank notsLeft
theorem fReplayRecipesExact_eq (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) (nl : Nat) :
    fReplayRecipesExact mask needed recipes bank nl=replayRecipesExact mask needed recipes bank nl:=by
  induction recipes generalizing bank nl with
  | nil=>rfl
  | cons rec rest ih =>
    obtain ⟨w,a,b⟩:=rec
    change fForce (Nat.land w mask) (fun v =>
      @Bool.rec (fun _=>List Word × Nat) (fReplayRecipesExact mask needed rest bank nl)
        (fForce (Nat.land a mask) fun am =>
          fForce (Nat.land b mask) fun bm =>
            @Bool.rec (fun _=>List Word × Nat)
              (@Bool.rec (fun _=>List Word × Nat) (fReplayRecipesExact mask needed rest bank nl)
                (let r:=fReplayRecipesExact mask needed rest (v :: bank) (Nat.sub nl 1);(v :: r.1,Nat.add r.2 1))
                (fBand (Nat.blt 0 nl) (fBand (fAvailableB mask bank am) (Nat.beq v (Nat.xor mask am)))))
              (let r:=fReplayRecipesExact mask needed rest (v :: bank) nl;(v :: r.1,r.2))
              (fRecipeGateBin mask bank v am bm))
        (fBand (fContains v needed) (fBnot (fAvailableB mask bank v)))) =
      dagForceWord1 (w&&&mask) (fun v =>
        if needed.contains v && !availableB mask bank v then
          dagForceWord1 (a&&&mask) (fun am =>
            dagForceWord1 (b&&&mask) (fun bm =>
              if recipeGateBin mask bank v am bm then
                let r:=replayRecipesExact mask needed rest (v :: bank) nl
                (v :: r.1,r.2)
              else if nl > 0&&availableB mask bank am&&v==(mask^^^am) then
                let r:=replayRecipesExact mask needed rest (v :: bank) (nl - 1)
                (v :: r.1,r.2+1)
              else replayRecipesExact mask needed rest bank nl))
        else replayRecipesExact mask needed rest bank nl)
    rw [fForce_eq,dagForceWord1Eq,fBand_eq,fContains_eq,fBnot_eq,fAvailableB_eq]
    cases needed.contains (w&&&mask) && !availableB mask bank (w&&&mask)
    · simp only [Bool.false_eq_true, ↓reduceIte];exact ih bank nl
    · simp only [↓reduceIte,fForce_eq,dagForceWord1Eq,fRecipeGateBin_eq]
      cases recipeGateBin mask bank (w&&&mask) (a&&&mask) (b&&&mask)
      · simp only [Bool.false_eq_true, ↓reduceIte,fBand_eq,fAvailableB_eq]
        have hc : (Nat.blt 0 nl&&(availableB mask bank (Nat.land a mask)&&Nat.beq (Nat.land w mask) (Nat.xor mask (Nat.land a mask)))) =
            (decide (nl > 0)&&availableB mask bank (a&&&mask)&&((w&&&mask)==(mask^^^(a&&&mask)))):=by
          rw [fNatBlt_iff_lt,fNatBeq_iff_beq,Bool.and_assoc];rfl
        rw [hc]
        cases decide (nl > 0)&&availableB mask bank (a&&&mask)&&((w&&&mask)==(mask^^^(a&&&mask)))
        · simp only [Bool.false_eq_true, ↓reduceIte];exact ih bank nl
        · simp only [↓reduceIte];rw [ih _ _];rfl
      · simp only [↓reduceIte];rw [ih _ _];rfl
def fAllAvail (cut : Word) (bank ws : List Word) : Bool :=
 List.rec true (fun w _ next=>fBand (fAvailableB cut bank (Nat.land w cut)) next) ws
theorem fAllAvail_eq (cut : Word) (bank ws : List Word) :
    fAllAvail cut bank ws=ws.all (fun w=>availableB cut bank (w&&&cut)):=by
  induction ws with
  | nil=>rfl
  | cons w ws ih =>
    change fBand (fAvailableB cut bank (Nat.land w cut)) (fAllAvail cut bank ws) =
      (availableB cut bank (w&&&cut)&&ws.all (fun w=>availableB cut bank (w&&&cut)))
    rw [fBand_eq,fAvailableB_eq,ih];rfl
def fAppend (xs ys : List Word) : List Word :=
 List.rec ys (fun x _ next=>x :: next) xs
theorem fAppend_eq (xs ys : List Word) : fAppend xs ys=xs ++ ys:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>exact congrArg (x :: ·) ih
def fMin (a b : Nat) : Nat := @Bool.rec (fun _=>Nat) b a (Nat.ble a b)
theorem fMin_eq (a b : Nat) : fMin a b=min a b:=by
  unfold fMin
  cases h : Nat.ble a b
  · have : ¬ a ≤ b:=fun hl=>Bool.noConfusion ((Nat.ble_eq.mpr hl).symm.trans h)
    exact (Nat.min_eq_right (Nat.le_of_not_ge this)).symm
  · exact (Nat.min_eq_left (Nat.ble_eq.mp h)).symm
def fMax (a b : Nat) : Nat := @Bool.rec (fun _=>Nat) a b (Nat.ble a b)
theorem fMax_eq (a b : Nat) : fMax a b=max a b:=by
  unfold fMax
  cases h : Nat.ble a b
  · have : ¬ a ≤ b:=fun hl=>Bool.noConfusion ((Nat.ble_eq.mpr hl).symm.trans h)
    exact (Nat.max_eq_left (Nat.le_of_not_ge this)).symm
  · exact (Nat.max_eq_right (Nat.ble_eq.mp h)).symm
def fExactBoundCloses (allowNotInPast : Bool) (target : Word) (state : RowState1) (bound : ExactBound) : Bool :=
  let (cut,stock,lower0,lower1,goal):=bound
  let (fuel,nots,ws,history):=state
  let lower1Eff:=fMin lower1 (Nat.add lower0 1)
  let maxLower :=
    @Bool.rec (fun _=>Nat)
      (@Bool.rec (fun _=>Nat) lower0 (fMax lower0 lower1Eff) allowNotInPast)
      lower1Eff
      (Nat.beq nots 1)
  let nl := @Bool.rec (fun _=>Nat) 0 1 (fBand (Nat.beq nots 0) allowNotInPast)
  fForce (Nat.sub fuel (fFlatCount cut ws)) fun remaining =>
    @Bool.rec (fun _=>Bool) false
      (fBand (Nat.beq (Nat.land target cut) goal)
        (fBand (fBnot (Nat.beq goal 0))
          (fBand (fBnot (Nat.beq goal cut))
            (fForceWords (fRecipeStart cut stock ws) fun start =>
              @Bool.rec (fun _=>Bool) false
                (fForceWords (fRecipeClosure cut stock history start) fun needed =>
                  @Bool.rec (fun _=>Bool) false
                    (let res:=fReplayRecipesExact cut needed (fListRev history) stock nl
                     fForceWords res.1 fun replay =>
                       let effLower := @Bool.rec (fun _=>Nat) lower0 lower1Eff
                         (fBor (Nat.beq nots 1) (fBnot (Nat.beq res.2 0)))
                       fBand (Nat.blt (Nat.add (fListLen replay) remaining) effLower)
                         (fAllAvail cut (fAppend replay stock) ws))
                    (Nat.blt (Nat.add (fListLen needed) remaining) maxLower))
                (Nat.blt (Nat.add (fListLen start) remaining) maxLower)))))
      (Nat.blt remaining maxLower)
theorem fExactBoundCloses_eq (allowNotInPast : Bool) (target : Word) (state : RowState1) (bound : ExactBound) :
    fExactBoundCloses allowNotInPast target state bound=exactBoundCloses allowNotInPast target state bound:=by
  obtain ⟨fuel,nots,ws,history⟩:=state
  obtain ⟨cut,stock,lower0,lower1,goal⟩:=bound
  unfold fExactBoundCloses exactBoundCloses
  simp only [fForce_eq,fForceWords_eq,dagForceWord1Eq,dagForceWords1Eq,
    fBand_eq,fBor_eq,fBnot_eq,fFlatCount_eq,fRecipeStart_eq,fRecipeClosure_eq,
    fListRev_eq,fReplayRecipesExact_eq,fListLen_eq,fAllAvail_eq,fAppend_eq,fMin_eq,fMax_eq]
  have hmax : (@Bool.rec (fun _=>Nat)
      (@Bool.rec (fun _=>Nat) lower0 (max lower0 (min lower1 (lower0+1))) allowNotInPast)
      (min lower1 (lower0+1)) (Nat.beq nots 1)) =
      (if (nots==1)=true then min lower1 (lower0+1)
       else if allowNotInPast=true then max lower0 (min lower1 (lower0+1)) else lower0):=by
    rw [fNatBeq_iff_beq];cases (nots==1) <;> cases allowNotInPast <;> rfl
  have hnl : (@Bool.rec (fun _=>Nat) 0 1 (Nat.beq nots 0&&allowNotInPast)) =
      (if ((nots==0)&&allowNotInPast)=true then 1 else 0):=by
    rw [fNatBeq_iff_beq];cases (nots==0) <;> cases allowNotInPast <;> rfl
  rw [hmax,hnl]
  generalize (if (nots==1)=true then min lower1 (lower0+1)
    else if allowNotInPast=true then max lower0 (min lower1 (lower0+1)) else lower0)=maxL
  generalize (if ((nots==0)&&allowNotInPast)=true then 1 else 0)=nl
  have hpre : (Nat.beq (Nat.land target cut) goal&&(!Nat.beq goal 0 && !Nat.beq goal cut)) =
      (((target&&&cut)==goal)&&(goal != 0)&&(goal != cut)):=by
    rw [fNatBeq_iff_beq,fNatBeq_iff_beq,fNatBeq_iff_beq]
    simp [bne,Bool.and_assoc]
  cases hrem : Nat.blt (fuel - flatCount cut ws) maxL
  · simp [hrem]
  · simp only [hrem, ↓reduceIte]
    rw [← Bool.and_assoc, ← Bool.and_assoc,show (Nat.beq (Nat.land target cut) goal && !Nat.beq goal 0 && !Nat.beq goal cut) =
      (((target&&&cut)==goal)&&(goal != 0)&&(goal != cut)) by rw [Bool.and_assoc,hpre]]
    cases (((target&&&cut)==goal)&&(goal != 0)&&(goal != cut))
    · rfl
    · simp only [Bool.true_and]
      cases Nat.blt ((recipeStart cut stock ws).length+(fuel - flatCount cut ws)) maxL
      · rfl
      · simp only [↓reduceIte]
        cases Nat.blt ((recipeClosure cut stock history (recipeStart cut stock ws)).length+(fuel - flatCount cut ws)) maxL
        · rfl
        · simp only [↓reduceIte]
          have hbrec : ∀ b : Bool,(@Bool.rec (fun _=>Nat) lower0 (min lower1 (lower0+1)) b) =
              (if b=true then min lower1 (lower0+1) else lower0):=fun b=>by cases b <;> rfl
          have heff : (@Bool.rec (fun _=>Nat) lower0 (min lower1 (lower0+1))
              (Nat.beq nots 1 || !Nat.beq (replayRecipesExact cut (recipeClosure cut stock history (recipeStart cut stock ws)) history.reverse stock nl).2 0)) =
              (if ((nots==1)||((replayRecipesExact cut (recipeClosure cut stock history (recipeStart cut stock ws)) history.reverse stock nl).2 != 0))=true
               then min lower1 (lower0+1) else lower0):=by
            rw [fNatBeq_iff_beq,fNatBeq_iff_beq]
            simp only [bne]
            exact hbrec _
          rw [heff];rfl
noncomputable def fExactBoundClosesTerm : {f : Bool → Word → RowState1 → ExactBound → Bool // f=fExactBoundCloses}:=by
  refine ⟨?f, ?proof⟩
  case proof =>
    delta fExactBoundCloses fFlatCount fMaskFlat fRecipeStart fRecipeClosure fStockWord fReplayRecipesExact
      fRecipeGateBin fAvailableB fAllAvail fAppend fListRev fListLen fContains fMin fMax fBand fBor fBnot
    beta_reduce
    exact rfl
noncomputable def fExactKnownCloses (allowNotInPast : Bool) (target : Word) (bounds : List ExactBound)
 (state : RowState1) : Bool :=
 List.rec false (fun bound _ later=>fBor (fExactBoundClosesTerm.1 allowNotInPast target state bound) later) bounds
theorem fExactKnownCloses_eq (allowNotInPast : Bool) (target : Word) (bounds : List ExactBound) (state : RowState1) :
    fExactKnownCloses allowNotInPast target bounds state=exactKnownCloses allowNotInPast target bounds state:=by
  induction bounds with
  | nil=>rfl
  | cons b bs ih =>
    change fBor (fExactBoundClosesTerm.1 allowNotInPast target state b) (fExactKnownCloses allowNotInPast target bs state) =
      (exactBoundCloses allowNotInPast target state b||exactKnownCloses allowNotInPast target bs state)
    rw [fBor_eq,ih,show fExactBoundClosesTerm.1=fExactBoundCloses from fExactBoundClosesTerm.2,fExactBoundCloses_eq]
def fPartition (directed : Bool) (ws : List Word) : Word → Word → Bool :=
 List.rec
 (fun p n=>fBor (Nat.beq p 0) (Nat.beq n 0))
 (fun w _ rest p n =>
 fBor (Nat.beq p 0) (fBor (Nat.beq n 0)
 (fForce (Nat.land p w) fun up =>
 fForce (Nat.land n w) fun down =>
 fBand (rest up down)
 (fForce (Nat.xor p up) fun offP =>
 fForce (@Bool.rec (fun _=>Word) (Nat.xor n down) n directed) (rest offP))))) ws
theorem fPartition_eq (directed : Bool) (ws : List Word) (p n : Word) :
    fPartition directed ws p n=dagPartition1 directed ws p n:=by
  induction ws generalizing p n with
  | nil=>change fBor (Nat.beq p 0) (Nat.beq n 0)=(Nat.beq p 0||Nat.beq n 0);rw [fBor_eq]
  | cons w ws ih =>
    change fBor (Nat.beq p 0) (fBor (Nat.beq n 0)
        (fForce (Nat.land p w) fun up =>
          fForce (Nat.land n w) fun down =>
            fBand (fPartition directed ws up down)
              (fForce (Nat.xor p up) fun offP =>
                fForce (@Bool.rec (fun _=>Word) (Nat.xor n down) n directed) (fPartition directed ws offP)))) =
      (Nat.beq p 0||Nat.beq n 0 ||
        dagForceWord1 (p&&&w) (fun up =>
          dagForceWord1 (n&&&w) (fun down =>
            dagPartition1 directed ws up down &&
              dagForceWord1 (p^^^up) (fun offP =>
                dagForceWord1 (if directed then n else n^^^down) (dagPartition1 directed ws offP)))))
    simp only [fBor_eq,fBand_eq,fForce_eq,dagForceWord1Eq,ih,Bool.or_assoc]
    cases directed <;> rfl
noncomputable def fPartitionTerm : {f : Bool → List Word → Word → Word → Bool // f=fPartition}:=by
  refine ⟨?f, ?proof⟩
  case proof =>
    delta fPartition fBor fBand
    beta_reduce
    exact rfl
noncomputable def fPartitionRun : Bool → List Word → Word → Word → Bool:=fPartitionTerm.1
theorem fPartitionRun_eq (directed : Bool) (ws : List Word) (p n : Word) :
    fPartitionRun directed ws p n=dagPartition1 directed ws p n :=
  (congrFun (congrFun (congrFun (congrFun fPartitionTerm.2 directed) ws) p) n).trans (fPartition_eq directed ws p n)
noncomputable def fFastRectTerm : {f : List Word → Bool // f=PackedRect.fastRectColumn}:=by
  refine ⟨?f, ?proof⟩
  case proof =>
    delta PackedRect.fastRectColumn PackedRect.forceColumns PackedRect.mapW' PackedRect.hullsOK'
      PackedRect.tw' PackedRect.priv PackedRect.hull PackedRect.hullC PackedRect.rowsOf PackedRect.colsOf
      PackedRect.orS PackedRect.orSL PackedRect.rowM PackedRect.full PackedRect.rectW'
      PackedRect.rectRowMask PackedRect.rectRepeat PackedRect.rect' PackedRect.tb'
      PackedRect.band PackedRect.bor PackedRect.bnot unpack
    beta_reduce
    exact rfl
noncomputable def fFastRect : List Word → Bool:=fFastRectTerm.1
theorem fFastRect_eq (ws : List Word) : fFastRect ws=PackedRect.rectOK1 ws :=
  (congrFun fFastRectTerm.2 ws).trans (PackedRect.fastRectColumnEq ws)
def fGoK1 (base : Word) (items : List (Word × Word)) : Word → Word → Word → Bool :=
 List.rec
 (fun _ u1 c1=>PackedRect.subM (PackedRect.hull u1) (Nat.lor base c1))
 (fun ah _ next u0 u1 c1 =>
 fBor
 (fBand (Nat.beq (Nat.land u0 ah.2) 0)
 (fForce (Nat.lor u0 ah.2) fun u0'=>next u0' u1 c1))
 (fBand (Nat.beq (Nat.land u1 ah.2) 0)
 (fForce (Nat.lor u1 ah.2) fun u1' =>
 fForce (Nat.lor c1 ah.1) fun c1'=>next u0 u1' c1')))
 items
def fGoK2 (base : Word) (items : List (Word × Word)) : Word → Word → Word → Word → Word → Bool :=
 List.rec
 (fun _ u1 u2 c1 c2 =>
 fForce (Nat.lor base c1) fun cov1 =>
 fBand (PackedRect.subM (PackedRect.hull u1) cov1)
 (PackedRect.subM (PackedRect.hull u2) (Nat.lor cov1 c2)))
 (fun ah _ next u0 u1 u2 c1 c2 =>
 fBor
 (fBand (Nat.beq (Nat.land u0 ah.2) 0)
 (fForce (Nat.lor u0 ah.2) fun u0'=>next u0' u1 u2 c1 c2))
 (fBor
 (fBand (Nat.beq (Nat.land u1 ah.2) 0)
 (fForce (Nat.lor u1 ah.2) fun u1' =>
 fForce (Nat.lor c1 ah.1) fun c1'=>next u0 u1' u2 c1' c2))
 (fBand (Nat.beq (Nat.land u2 ah.2) 0)
 (fForce (Nat.lor u2 ah.2) fun u2' =>
 fForce (Nat.lor c2 ah.1) fun c2'=>next u0 u1 u2' c1 c2'))))
 items
def fPrepRects (t : Word) (rs : List Word) :
 Nat → Word → Word → List (Word × Word) → (Nat → Word → List (Word × Word) → Bool) → Bool :=
 List.rec
 (fun p _ t2 acc k=>k p t2 acc)
 (fun a _ next p o2 t2 acc k =>
 fForce (Nat.land (Nat.land a (Nat.xor t PackedRect.full)) PackedRect.full) fun raw =>
 @Bool.rec (fun _=>Bool)
 (fForce (PackedRect.hullC raw) fun h =>
 fBand (PackedRect.subM h a)
 (fForce (Nat.lor o2 h) fun o2' =>
 fForce (Nat.lor t2 (Nat.land o2 h)) fun t2' =>
 next (Nat.add p 1) o2' t2' ((Nat.land a PackedRect.full,h) :: acc) k))
 (next p o2 t2 ((Nat.land a PackedRect.full,0) :: acc) k)
 (Nat.beq raw 0))
 rs
def fSplitItems (t2 : Word) (ahs : List (Word × Word)) :
 Word → List (Word × Word) → (Word → List (Word × Word) → Bool) → Bool :=
 List.rec
 (fun base items k=>k base items)
 (fun ah _ next base items k =>
 @Bool.rec (fun _=>Bool)
 (next base (ah :: items) k)
 (fForce (Nat.lor base ah.1) fun base'=>next base' items k)
 (Nat.beq (Nat.land ah.2 t2) 0))
 ahs
def fClassFromPrep (maxK K t2 : Word) (ahs : List (Word × Word)) : Bool :=
 @Bool.rec (fun _=>Bool)
 (@Bool.rec (fun _=>Bool)
 (@Bool.rec (fun _=>Bool)
 (fSplitItems t2 ahs 0 [] fun base items =>
 @Bool.rec (fun _=>Bool)
 (@Bool.rec (fun _=>Bool) true (fGoK2 base items 0 0 0 0 0) (Nat.beq K 2))
 (fGoK1 base items 0 0 0)
 (Nat.beq K 1))
 false
 (Nat.beq K 0))
 true
 (Nat.blt maxK K))
 true
 (Nat.beq t2 0)
def fChartBits (w : Word) (rows : List Nat) : Word :=
 List.rec 0 (fun r _ packed=>Nat.lor (Nat.land (Nat.shiftRight w r) 1) (Nat.shiftLeft packed 1)) rows
theorem fChartBits_eq (w : Word) (rows : List Nat) : fChartBits w rows=chartBits w rows:=by
  induction rows with
  | nil=>rfl
  | cons r rs ih =>
    change Nat.lor (Nat.land (Nat.shiftRight w r) 1) (Nat.shiftLeft (fChartBits w rs) 1) =
      (((w>>>r)&&&1)|||(chartBits w rs<<<1))
    rw [ih];rfl
def fMapChart (rows : List Nat) (ws : List Word) : List Word :=
 List.rec [] (fun w _ next=>fChartBits w rows :: next) ws
theorem fMapChart_eq (c : RowChart) (ws : List Word) : fMapChart c.val ws=ws.map (chartWord c):=by
  induction ws with
  | nil=>rfl
  | cons w ws ih =>
    change fChartBits w c.val :: fMapChart c.val ws=chartWord c w :: ws.map (chartWord c)
    rw [fChartBits_eq,ih];rfl
noncomputable def fKw64Algo (maxK : Nat) (rows : List Nat) (fuel : Nat) (ws : List Word) : Bool :=
 fForceWords (fMapChart rows ws) fun cws =>
 @Bool.rec (fun _=>Bool)
 (fForceWords (fDedup cws) fun l =>
 @Bool.rec (fun _=>Bool)
 (fForceWords (PackedRect.mapW' l) fun rs =>
 fForce (PackedRect.tw' rs 0 0) fun t =>
 fPrepRects t rs 0 0 0 [] fun p t2 ahs =>
 fBand (Nat.ble p (Nat.add fuel 1))
 (fClassFromPrep maxK (Nat.sub (Nat.add fuel 1) p) t2 ahs))
 true
 (Nat.blt maxK (Nat.sub (Nat.add fuel 1) (fListLen l))))
 (fFastRect cws)
 (Nat.beq (fListLen ws) (Nat.add fuel 1))
theorem hullC_zero_eq : PackedRect.hullC 0=0:=by decide +kernel
theorem fPrepRects_spec {t : Word} {rs : List Word}
    (hsub : ∀ a ∈ rs,PackedRect.subM (PackedRect.priv t a) a=true) :
    ∀ p o2 t2 acc k,
      fPrepRects t rs p o2 t2 acc k =
        k (p+(rs.filter (fun a => !Nat.beq (Nat.land (Nat.land a (Nat.xor t PackedRect.full)) PackedRect.full) 0)).length)
          (PackedRect.tw (rs.map (PackedRect.priv t)) o2 t2)
          ((rs.map (fun a=>(Nat.land a PackedRect.full,PackedRect.priv t a))).reverse ++ acc):=by
  induction rs with
  | nil=>intro p o2 t2 acc k;simp [fPrepRects,PackedRect.tw]
  | cons a rs ih =>
    intro p o2 t2 acc k
    change fForce (Nat.land (Nat.land a (Nat.xor t PackedRect.full)) PackedRect.full) (fun raw =>
      @Bool.rec (fun _=>Bool)
        (fForce (PackedRect.hullC raw) fun h =>
          fBand (PackedRect.subM h a)
            (fForce (Nat.lor o2 h) fun o2' =>
              fForce (Nat.lor t2 (Nat.land o2 h)) fun t2' =>
                fPrepRects t rs (Nat.add p 1) o2' t2' ((Nat.land a PackedRect.full,h) :: acc) k))
        (fPrepRects t rs p o2 t2 ((Nat.land a PackedRect.full,0) :: acc) k)
        (Nat.beq raw 0))=_
    rw [fForce_eq]
    have hsubA:=hsub a List.mem_cons_self
    have hsubR : ∀ x ∈ rs,PackedRect.subM (PackedRect.priv t x) x=true:=fun x hx=>hsub x (List.mem_cons_of_mem _ hx)
    cases hz : Nat.beq (Nat.land (Nat.land a (Nat.xor t PackedRect.full)) PackedRect.full) 0
    · dsimp only
      rw [fForce_eq]
      have hpriv : PackedRect.hullC (Nat.land (Nat.land a (Nat.xor t PackedRect.full)) PackedRect.full)=PackedRect.priv t a:=rfl
      rw [hpriv,hsubA,fBand_eq,Bool.true_and,fForce_eq,fForce_eq,ih hsubR]
      simp only [List.filter_cons,hz,Bool.not_false, ↓reduceIte,List.length_cons,PackedRect.tw,List.map_cons,
        List.reverse_cons,List.append_assoc,List.singleton_append]
      congr 1;change p+1+_=p+(_+1);omega
    · dsimp only
      have hraw0 : Nat.land (Nat.land a (Nat.xor t PackedRect.full)) PackedRect.full=0:=Nat.beq_eq.mp hz
      have hpriv0 : PackedRect.priv t a=0:=by
        change PackedRect.hullC (Nat.land (Nat.land a (Nat.xor t PackedRect.full)) PackedRect.full)=0
        rw [hraw0];exact hullC_zero_eq
      rw [ih hsubR]
      have ho2 : Nat.lor o2 0=o2:=Nat.or_zero o2
      have ht2 : Nat.lor t2 (Nat.land o2 0)=t2:=by change t2|||(o2&&&0)=t2;simp
      simp only [List.filter_cons,hz,Bool.not_true,Bool.false_eq_true, ↓reduceIte,PackedRect.tw,
        List.map_cons,hpriv0,ho2,ht2,List.reverse_cons,List.append_assoc,List.singleton_append]
theorem fSplitItems_spec {t2 : Word} {ahs : List (Word × Word)} :
    ∀ base items k,
      fSplitItems t2 ahs base items k =
        k (ahs.foldl (fun b ah=>if Nat.beq (Nat.land ah.2 t2) 0 then Nat.lor b ah.1 else b) base)
          ((ahs.filter (fun ah => !Nat.beq (Nat.land ah.2 t2) 0)).reverse ++ items):=by
  induction ahs with
  | nil=>intro base items k;rfl
  | cons ah ahs ih =>
    intro base items k
    change @Bool.rec (fun _=>Bool)
      (fSplitItems t2 ahs base (ah :: items) k)
      (fForce (Nat.lor base ah.1) fun base'=>fSplitItems t2 ahs base' items k)
      (Nat.beq (Nat.land ah.2 t2) 0)=_
    cases hz : Nat.beq (Nat.land ah.2 t2) 0
    · dsimp only;rw [ih]
      simp only [List.foldl_cons,hz,Bool.false_eq_true, ↓reduceIte,List.filter_cons,Bool.not_false,
        List.reverse_cons,List.append_assoc,List.singleton_append]
    · dsimp only;rw [fForce_eq,ih]
      simp only [List.foldl_cons,hz, ↓reduceIte,List.filter_cons,Bool.not_true,Bool.false_eq_true]
theorem fGoK1_inv {base : Word} {M : Word × Word × Nat → Prop}
    (hcov : ∀ q,
      (∃ U : Word,(∀ r,U.testBit r=true → ∃ p,M p ∧ p.2.2=1 ∧ p.2.1.testBit r=true) ∧
        (PackedRect.hull U).testBit q=true) →
      base.testBit q=true ∨ ∃ p,M p ∧ p.2.2=1 ∧ p.1.testBit q=true) :
    ∀ (rest : List (Word × Word × Nat)) (u0 u1 c1 : Word),
      (∀ p ∈ rest,M p) → (∀ p ∈ rest,p.2.2 ≤ 1) →
      rest.Pairwise (fun p r=>p.2.2=r.2.2 → Nat.land p.2.1 r.2.1=0) →
      (∀ r ∈ rest,r.2.2=0 → Nat.land u0 r.2.1=0) →
      (∀ r ∈ rest,r.2.2=1 → Nat.land u1 r.2.1=0) →
      (∀ q,u1.testBit q=true → ∃ p,M p ∧ p.2.2=1 ∧ p.2.1.testBit q=true) →
      (∀ p,M p → p.2.2=1 → p ∈ rest ∨ ∀ q,p.1.testBit q=true → c1.testBit q=true) →
      fGoK1 base (rest.map (fun p=>(p.1,p.2.1))) u0 u1 c1=true:=by
  intro rest
  induction rest with
  | nil =>
    intro u0 u1 c1 _ _ _ _ _ Iu1 Ic1
    change PackedRect.subM (PackedRect.hull u1) (Nat.lor base c1)=true
    unfold PackedRect.subM
    have hsub : Nat.land (PackedRect.hull u1) (Nat.lor base c1)=PackedRect.hull u1:=by
      apply PackedRect.land_sub;intro q hq;rw [PackedRect.tb_lor]
      rcases hcov q ⟨u1,Iu1,hq⟩ with hb | ⟨p,hp,hp1,hpq⟩
      · rw [hb];rfl
      · rcases Ic1 p hp hp1 with hm | hc
        · simp at hm
        · rw [hc q hpq];exact Bool.or_true _
    rw [hsub];exact Nat.beq_refl _
  | cons it rest ih =>
    intro u0 u1 c1 hM hK hP Iu0 Iu1 Iu1b Ic1
    have hP':=List.pairwise_cons.mp hP
    have hit : it ∈ it :: rest:=List.mem_cons_self
    have hk:=hK it hit
    change fBor
      (fBand (Nat.beq (Nat.land u0 it.2.1) 0)
        (fForce (Nat.lor u0 it.2.1) fun u0'=>fGoK1 base (rest.map (fun p=>(p.1,p.2.1))) u0' u1 c1))
      (fBand (Nat.beq (Nat.land u1 it.2.1) 0)
        (fForce (Nat.lor u1 it.2.1) fun u1' =>
          fForce (Nat.lor c1 it.1) fun c1'=>fGoK1 base (rest.map (fun p=>(p.1,p.2.1))) u0 u1' c1'))=true
    rw [fBor_eq,fBand_eq,fBand_eq,fForce_eq,fForce_eq,fForce_eq,Bool.or_eq_true]
    by_cases h0 : it.2.2=0
    · left
      rw [Bool.and_eq_true,Iu0 it hit h0,Nat.beq_refl]
      refine ⟨rfl,ih (Nat.lor u0 it.2.1) u1 c1 (fun p hp=>hM p (List.mem_cons_of_mem _ hp))
        (fun p hp=>hK p (List.mem_cons_of_mem _ hp)) hP'.2 ?_ ?_ Iu1b ?_⟩
      · intro r hr hr0
        apply PackedRect.land_disj;intro q h1 h2
        rw [PackedRect.tb_lor,Bool.or_eq_true] at h1
        rcases h1 with h1 | h1
        · exact PackedRect.land_zero_tb _ _ q (Iu0 r (List.mem_cons_of_mem _ hr) hr0) h1 h2
        · exact PackedRect.land_zero_tb _ _ q (hP'.1 r hr (h0.trans hr0.symm)) h1 h2
      · intro r hr hr1;exact Iu1 r (List.mem_cons_of_mem _ hr) hr1
      · intro p hp hp1
        rcases Ic1 p hp hp1 with hm | hc
        · rcases List.mem_cons.mp hm with rfl | hm;omega;exact Or.inl hm
        · exact Or.inr hc
    · right
      have h1 : it.2.2=1:=by omega
      rw [Bool.and_eq_true,Iu1 it hit h1,Nat.beq_refl]
      refine ⟨rfl,ih u0 (Nat.lor u1 it.2.1) (Nat.lor c1 it.1) (fun p hp=>hM p (List.mem_cons_of_mem _ hp))
        (fun p hp=>hK p (List.mem_cons_of_mem _ hp)) hP'.2 ?_ ?_ ?_ ?_⟩
      · intro r hr hr0;exact Iu0 r (List.mem_cons_of_mem _ hr) hr0
      · intro r hr hr1
        apply PackedRect.land_disj;intro q h1' h2'
        rw [PackedRect.tb_lor,Bool.or_eq_true] at h1'
        rcases h1' with h1' | h1'
        · exact PackedRect.land_zero_tb _ _ q (Iu1 r (List.mem_cons_of_mem _ hr) hr1) h1' h2'
        · exact PackedRect.land_zero_tb _ _ q (hP'.1 r hr (h1.trans hr1.symm)) h1' h2'
      · intro q hq
        rw [PackedRect.tb_lor,Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact Iu1b q hq
        · exact ⟨it,hM it hit,h1,hq⟩
      · intro p hp hp1
        rcases Ic1 p hp hp1 with hm | hc
        · rcases List.mem_cons.mp hm with rfl | hm
          · exact Or.inr (fun q hq=>by rw [PackedRect.tb_lor,hq];exact Bool.or_true _)
          · exact Or.inl hm
        · exact Or.inr (fun q hq=>by rw [PackedRect.tb_lor,hc q hq];rfl)
theorem fGoK2_inv {base : Word} {M : Word × Word × Nat → Prop}
    (hcov1 : ∀ q,
      (∃ U : Word,(∀ r,U.testBit r=true → ∃ p,M p ∧ p.2.2=1 ∧ p.2.1.testBit r=true) ∧
        (PackedRect.hull U).testBit q=true) →
      base.testBit q=true ∨ ∃ p,M p ∧ p.2.2=1 ∧ p.1.testBit q=true)
    (hcov2 : ∀ q,
      (∃ U : Word,(∀ r,U.testBit r=true → ∃ p,M p ∧ p.2.2=2 ∧ p.2.1.testBit r=true) ∧
        (PackedRect.hull U).testBit q=true) →
      base.testBit q=true ∨ ∃ p,M p ∧ (p.2.2=1 ∨ p.2.2=2) ∧ p.1.testBit q=true) :
    ∀ (rest : List (Word × Word × Nat)) (u0 u1 u2 c1 c2 : Word),
      (∀ p ∈ rest,M p) → (∀ p ∈ rest,p.2.2 ≤ 2) →
      rest.Pairwise (fun p r=>p.2.2=r.2.2 → Nat.land p.2.1 r.2.1=0) →
      (∀ r ∈ rest,r.2.2=0 → Nat.land u0 r.2.1=0) →
      (∀ r ∈ rest,r.2.2=1 → Nat.land u1 r.2.1=0) →
      (∀ r ∈ rest,r.2.2=2 → Nat.land u2 r.2.1=0) →
      (∀ q,u1.testBit q=true → ∃ p,M p ∧ p.2.2=1 ∧ p.2.1.testBit q=true) →
      (∀ q,u2.testBit q=true → ∃ p,M p ∧ p.2.2=2 ∧ p.2.1.testBit q=true) →
      (∀ p,M p → p.2.2=1 → p ∈ rest ∨ ∀ q,p.1.testBit q=true → c1.testBit q=true) →
      (∀ p,M p → p.2.2=2 → p ∈ rest ∨ ∀ q,p.1.testBit q=true → c2.testBit q=true) →
      fGoK2 base (rest.map (fun p=>(p.1,p.2.1))) u0 u1 u2 c1 c2=true:=by
  intro rest
  induction rest with
  | nil =>
    intro u0 u1 u2 c1 c2 _ _ _ _ _ _ Iu1b Iu2b Ic1 Ic2
    change fForce (Nat.lor base c1) (fun cov1 =>
      fBand (PackedRect.subM (PackedRect.hull u1) cov1)
        (PackedRect.subM (PackedRect.hull u2) (Nat.lor cov1 c2)))=true
    rw [fForce_eq,fBand_eq,Bool.and_eq_true]
    constructor
    · unfold PackedRect.subM
      have hsub : Nat.land (PackedRect.hull u1) (Nat.lor base c1)=PackedRect.hull u1:=by
        apply PackedRect.land_sub;intro q hq;rw [PackedRect.tb_lor]
        rcases hcov1 q ⟨u1,Iu1b,hq⟩ with hb | ⟨p,hp,hp1,hpq⟩
        · rw [hb];rfl
        · rcases Ic1 p hp hp1 with hm | hc;simp at hm;rw [hc q hpq];exact Bool.or_true _
      rw [hsub];exact Nat.beq_refl _
    · unfold PackedRect.subM
      have hsub : Nat.land (PackedRect.hull u2) (Nat.lor (Nat.lor base c1) c2)=PackedRect.hull u2:=by
        apply PackedRect.land_sub;intro q hq;rw [PackedRect.tb_lor,PackedRect.tb_lor]
        rcases hcov2 q ⟨u2,Iu2b,hq⟩ with hb | ⟨p,hp,hp1 | hp2,hpq⟩
        · rw [hb];rfl
        · rcases Ic1 p hp hp1 with hm | hc;simp at hm;rw [hc q hpq];simp
        · rcases Ic2 p hp hp2 with hm | hc;simp at hm;rw [hc q hpq];simp
      rw [hsub];exact Nat.beq_refl _
  | cons it rest ih =>
    intro u0 u1 u2 c1 c2 hM hK hP Iu0 Iu1 Iu2 Iu1b Iu2b Ic1 Ic2
    have hP':=List.pairwise_cons.mp hP
    have hit : it ∈ it :: rest:=List.mem_cons_self
    have hk:=hK it hit
    change fBor
      (fBand (Nat.beq (Nat.land u0 it.2.1) 0)
        (fForce (Nat.lor u0 it.2.1) fun u0'=>fGoK2 base (rest.map (fun p=>(p.1,p.2.1))) u0' u1 u2 c1 c2))
      (fBor
        (fBand (Nat.beq (Nat.land u1 it.2.1) 0)
          (fForce (Nat.lor u1 it.2.1) fun u1' =>
            fForce (Nat.lor c1 it.1) fun c1'=>fGoK2 base (rest.map (fun p=>(p.1,p.2.1))) u0 u1' u2 c1' c2))
        (fBand (Nat.beq (Nat.land u2 it.2.1) 0)
          (fForce (Nat.lor u2 it.2.1) fun u2' =>
            fForce (Nat.lor c2 it.1) fun c2'=>fGoK2 base (rest.map (fun p=>(p.1,p.2.1))) u0 u1 u2' c1 c2')))=true
    simp only [fBor_eq,fBand_eq,fForce_eq,Bool.or_eq_true,Bool.and_eq_true]
    by_cases h0 : it.2.2=0
    · left
      rw [Iu0 it hit h0,Nat.beq_refl]
      refine ⟨rfl,ih (Nat.lor u0 it.2.1) u1 u2 c1 c2 (fun p hp=>hM p (List.mem_cons_of_mem _ hp))
        (fun p hp=>hK p (List.mem_cons_of_mem _ hp)) hP'.2 ?_
        (fun r hr hr1=>Iu1 r (List.mem_cons_of_mem _ hr) hr1)
        (fun r hr hr2=>Iu2 r (List.mem_cons_of_mem _ hr) hr2) Iu1b Iu2b ?_ ?_⟩
      · intro r hr hr0
        apply PackedRect.land_disj;intro q h1 h2
        rw [PackedRect.tb_lor,Bool.or_eq_true] at h1
        rcases h1 with h1 | h1
        · exact PackedRect.land_zero_tb _ _ q (Iu0 r (List.mem_cons_of_mem _ hr) hr0) h1 h2
        · exact PackedRect.land_zero_tb _ _ q (hP'.1 r hr (h0.trans hr0.symm)) h1 h2
      · intro p hp hp1;rcases Ic1 p hp hp1 with hm | hc
        · rcases List.mem_cons.mp hm with rfl | hm;omega;exact Or.inl hm
        · exact Or.inr hc
      · intro p hp hp2;rcases Ic2 p hp hp2 with hm | hc
        · rcases List.mem_cons.mp hm with rfl | hm;omega;exact Or.inl hm
        · exact Or.inr hc
    · by_cases h1 : it.2.2=1
      · right;left
        rw [Iu1 it hit h1,Nat.beq_refl]
        refine ⟨rfl,ih u0 (Nat.lor u1 it.2.1) u2 (Nat.lor c1 it.1) c2 (fun p hp=>hM p (List.mem_cons_of_mem _ hp))
          (fun p hp=>hK p (List.mem_cons_of_mem _ hp)) hP'.2
          (fun r hr hr0=>Iu0 r (List.mem_cons_of_mem _ hr) hr0) ?_
          (fun r hr hr2=>Iu2 r (List.mem_cons_of_mem _ hr) hr2) ?_ Iu2b ?_ ?_⟩
        · intro r hr hr1
          apply PackedRect.land_disj;intro q ha hb
          rw [PackedRect.tb_lor,Bool.or_eq_true] at ha
          rcases ha with ha | ha
          · exact PackedRect.land_zero_tb _ _ q (Iu1 r (List.mem_cons_of_mem _ hr) hr1) ha hb
          · exact PackedRect.land_zero_tb _ _ q (hP'.1 r hr (h1.trans hr1.symm)) ha hb
        · intro q hq;rw [PackedRect.tb_lor,Bool.or_eq_true] at hq
          rcases hq with hq | hq
          · exact Iu1b q hq
          · exact ⟨it,hM it hit,h1,hq⟩
        · intro p hp hp1;rcases Ic1 p hp hp1 with hm | hc
          · rcases List.mem_cons.mp hm with rfl | hm
            · exact Or.inr (fun q hq=>by rw [PackedRect.tb_lor,hq];exact Bool.or_true _)
            · exact Or.inl hm
          · exact Or.inr (fun q hq=>by rw [PackedRect.tb_lor,hc q hq];rfl)
        · intro p hp hp2;rcases Ic2 p hp hp2 with hm | hc
          · rcases List.mem_cons.mp hm with rfl | hm;omega;exact Or.inl hm
          · exact Or.inr hc
      · right;right
        have h2 : it.2.2=2:=by omega
        rw [Iu2 it hit h2,Nat.beq_refl]
        refine ⟨rfl,ih u0 u1 (Nat.lor u2 it.2.1) c1 (Nat.lor c2 it.1) (fun p hp=>hM p (List.mem_cons_of_mem _ hp))
          (fun p hp=>hK p (List.mem_cons_of_mem _ hp)) hP'.2
          (fun r hr hr0=>Iu0 r (List.mem_cons_of_mem _ hr) hr0)
          (fun r hr hr1=>Iu1 r (List.mem_cons_of_mem _ hr) hr1) ?_ Iu1b ?_ ?_ ?_⟩
        · intro r hr hr2
          apply PackedRect.land_disj;intro q ha hb
          rw [PackedRect.tb_lor,Bool.or_eq_true] at ha
          rcases ha with ha | ha
          · exact PackedRect.land_zero_tb _ _ q (Iu2 r (List.mem_cons_of_mem _ hr) hr2) ha hb
          · exact PackedRect.land_zero_tb _ _ q (hP'.1 r hr (h2.trans hr2.symm)) ha hb
        · intro q hq;rw [PackedRect.tb_lor,Bool.or_eq_true] at hq
          rcases hq with hq | hq
          · exact Iu2b q hq
          · exact ⟨it,hM it hit,h2,hq⟩
        · intro p hp hp1;rcases Ic1 p hp hp1 with hm | hc
          · rcases List.mem_cons.mp hm with rfl | hm;omega;exact Or.inl hm
          · exact Or.inr hc
        · intro p hp hp2;rcases Ic2 p hp hp2 with hm | hc
          · rcases List.mem_cons.mp hm with rfl | hm
            · exact Or.inr (fun q hq=>by rw [PackedRect.tb_lor,hq];exact Bool.or_true _)
            · exact Or.inl hm
          · exact Or.inr (fun q hq=>by rw [PackedRect.tb_lor,hc q hq];rfl)
theorem fFoldlBase_tb (t2 : Word) (ahs : List (Word × Word)) (b q : Word) :
    (ahs.foldl (fun acc ah=>if Nat.beq (Nat.land ah.2 t2) 0 then Nat.lor acc ah.1 else acc) b).testBit q=true ↔
      b.testBit q=true ∨ ∃ ah ∈ ahs,Nat.beq (Nat.land ah.2 t2) 0=true ∧ ah.1.testBit q=true:=by
  induction ahs generalizing b with
  | nil=>simp
  | cons ah ahs ih =>
    simp only [List.foldl_cons,ih,List.mem_cons]
    cases hz : Nat.beq (Nat.land ah.2 t2) 0
    · simp only [hz,Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro (hb | ⟨x,hx,h1,h2⟩)
        · exact Or.inl hb
        · exact Or.inr ⟨x,Or.inr hx,h1,h2⟩
      · rintro (hb | ⟨x,rfl | hx,h1,h2⟩)
        · exact Or.inl hb
        · rw [hz] at h1;exact Bool.noConfusion h1
        · exact Or.inr ⟨x,hx,h1,h2⟩
    · simp only [hz, ↓reduceIte,PackedRect.tb_lor,Bool.or_eq_true,true_and]
      constructor
      · rintro ((hb | ha) | ⟨x,hx,h1,h2⟩)
        · exact Or.inl hb
        · exact Or.inr ⟨ah,Or.inl rfl,hz,ha⟩
        · exact Or.inr ⟨x,Or.inr hx,h1,h2⟩
      · rintro (hb | ⟨x,rfl | hx,h1,h2⟩)
        · exact Or.inl (Or.inl hb)
        · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨x,hx,h1,h2⟩
theorem fFoldlBase_eq_fcov (t t2 : Word) (rs : List Word) :
    ((rs.map (fun a=>(Nat.land a PackedRect.full,PackedRect.priv t a))).reverse.foldl
      (fun acc ah=>if Nat.beq (Nat.land ah.2 t2) 0 then Nat.lor acc ah.1 else acc) 0) =
    Nat.land (PackedRect.fcov t t2 rs) PackedRect.full:=by
  apply Nat.eq_of_testBit_eq;intro q
  apply Bool.eq_iff_iff.mpr
  rw [fFoldlBase_tb,PackedRect.tb_land,Bool.and_eq_true,PackedRect.full_tb,decide_eq_true_eq]
  simp only [Nat.zero_testBit,Bool.false_eq_true,false_or,List.mem_reverse,List.mem_map]
  constructor
  · rintro ⟨ah,⟨a,ha,rfl⟩,hdisj,hq⟩
    rw [PackedRect.tb_land,PackedRect.full_tb,Bool.and_eq_true,decide_eq_true_eq] at hq
    exact ⟨PackedRect.fcov_tb t t2 q rs a ha hdisj hq.1,hq.2⟩
  · rintro ⟨hf,hq144⟩
    suffices h : ∀ xs : List Word,(PackedRect.fcov t t2 xs).testBit q=true →
        ∃ a ∈ xs,Nat.beq (Nat.land (PackedRect.priv t a) t2) 0=true ∧ a.testBit q=true by
      obtain ⟨a,ha,hd,hqa⟩:=h rs hf
      exact ⟨(Nat.land a PackedRect.full,PackedRect.priv t a),⟨a,ha,rfl⟩,hd,
        by rw [PackedRect.tb_land,PackedRect.full_tb,hqa,decide_eq_true hq144];rfl⟩
    intro xs
    induction xs with
    | nil=>intro h;simp [PackedRect.fcov] at h
    | cons a xs ih =>
      intro h
      change (cond (Nat.beq (Nat.land (PackedRect.priv t a) t2) 0)
        (Nat.lor a (PackedRect.fcov t t2 xs)) (PackedRect.fcov t t2 xs)).testBit q=true at h
      cases hd : Nat.beq (Nat.land (PackedRect.priv t a) t2) 0
      · rw [hd] at h
        obtain ⟨x,hx,hxd,hxq⟩:=ih h
        exact ⟨x,List.mem_cons_of_mem _ hx,hxd,hxq⟩
      · rw [hd] at h
        change (Nat.lor a (PackedRect.fcov t t2 xs)).testBit q=true at h
        rw [PackedRect.tb_lor,Bool.or_eq_true] at h
        rcases h with ha | hr
        · exact ⟨a,List.mem_cons_self,hd,ha⟩
        · obtain ⟨x,hx,hxd,hxq⟩:=ih hr
          exact ⟨x,List.mem_cons_of_mem _ hx,hxd,hxq⟩
theorem fClassFromPrep_sound {maxK : Nat} {l : List Word} {K : Nat} {c : Nat → Nat}
    (hCL : PackedRect.ClassLab l K c) :
    fClassFromPrep maxK K
      (PackedRect.tw ((l.map PackedRect.rectW).map (PackedRect.priv (PackedRect.tw (l.map PackedRect.rectW) 0 0))) 0 0)
      (((l.map PackedRect.rectW).map (fun a=>(Nat.land a PackedRect.full,PackedRect.priv (PackedRect.tw (l.map PackedRect.rectW) 0 0) a))).reverse)=true:=by
  let rs:=l.map PackedRect.rectW
  let t:=PackedRect.tw rs 0 0
  let t2:=PackedRect.tw (rs.map (PackedRect.priv t)) 0 0
  let ahs:=(rs.map (fun a=>(Nat.land a PackedRect.full,PackedRect.priv t a))).reverse
  change fClassFromPrep maxK K t2 ahs=true
  unfold fClassFromPrep
  cases ht2 : Nat.beq t2 0
  · dsimp only
    have ht2ne : t2 ≠ 0:=fun hz=>Bool.noConfusion ((Nat.beq_eq.mpr hz).symm.trans ht2)
    cases hcap : Nat.blt maxK K
    · dsimp only
      cases hK0 : Nat.beq K 0
      · dsimp only
        rw [fSplitItems_spec]
        have hitems_eq : (ahs.filter (fun ah => !Nat.beq (Nat.land ah.2 t2) 0)).reverse ++ [] =
            (l.filter (fun x => !Nat.beq (Nat.land (PackedRect.privH l x) t2) 0)).map
              (fun x=>(Nat.land (PackedRect.rectW x) PackedRect.full,PackedRect.privH l x)):=by
          simp only [ahs,rs,List.append_nil,List.filter_reverse,List.reverse_reverse,List.filter_map,List.map_map]
          rfl
        have hbase_eq : ahs.foldl (fun b ah=>if Nat.beq (Nat.land ah.2 t2) 0 then Nat.lor b ah.1 else b) 0 =
            Nat.land (PackedRect.fcov t t2 rs) PackedRect.full:=fFoldlBase_eq_fcov t t2 rs
        rw [hitems_eq,hbase_eq]
        let fl:=l.filter (fun x => !Nat.beq (Nat.land (PackedRect.privH l x) t2) 0)
        let all:=fl.map (fun x=>(Nat.land (PackedRect.rectW x) PackedRect.full,PackedRect.privH l x,c x))
        have hall_map : all.map (fun p=>(p.1,p.2.1)) =
            fl.map (fun x=>(Nat.land (PackedRect.rectW x) PackedRect.full,PackedRect.privH l x)):=by
          simp only [all,List.map_map];rfl
        have ht2_def : t2=PackedRect.t2Of l:=rfl
        have hmem_all : ∀ p ∈ all, ∃ x ∈ l,PackedRect.isConf l x ∧
            p=(Nat.land (PackedRect.rectW x) PackedRect.full,PackedRect.privH l x,c x):=by
          intro p hp
          obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hp
          obtain ⟨hxl,hxf⟩:=List.mem_filter.mp hx
          refine ⟨x,hxl, ?_,rfl⟩
          apply PackedRect.beq0_false
          rw [← ht2_def]
          cases hb : Nat.beq (Nat.land (PackedRect.privH l x) t2) 0
          · rfl
          · rw [hb] at hxf;exact Bool.noConfusion hxf
        have hall_pw : all.Pairwise (fun p r=>p.2.2=r.2.2 → Nat.land p.2.1 r.2.1=0):=by
          rw [List.pairwise_map]
          refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.filter _ hCL.ne)
          intro x y hx hy hxy hceq
          have hcx : PackedRect.isConf l x:=PackedRect.beq0_false (by
            rw [← ht2_def];have:=(List.mem_filter.mp hx).2
            cases hb : Nat.beq (Nat.land (PackedRect.privH l x) t2) 0;rfl;rw [hb] at this;exact Bool.noConfusion this)
          have hcy : PackedRect.isConf l y:=PackedRect.beq0_false (by
            rw [← ht2_def];have:=(List.mem_filter.mp hy).2
            cases hb : Nat.beq (Nat.land (PackedRect.privH l y) t2) 0;rfl;rw [hb] at this;exact Bool.noConfusion this)
          exact hxy hcx hcy hceq
        have hall_K : ∀ p ∈ all,p.2.2 ≤ K:=by
          intro p hp;obtain ⟨x,hx,hcx,rfl⟩:=hmem_all p hp;exact hCL.le x hx hcx
        have hcov_gen : ∀ i,1 ≤ i → i ≤ K → ∀ q,
            (∃ U : Word,(∀ r,U.testBit r=true → ∃ p,p ∈ all ∧ p.2.2=i ∧ p.2.1.testBit r=true) ∧
              (PackedRect.hull U).testBit q=true) →
            (Nat.land (PackedRect.fcov t t2 rs) PackedRect.full).testBit q=true ∨
              ∃ p,p ∈ all ∧ (1 ≤ p.2.2 ∧ p.2.2 ≤ i) ∧ p.1.testBit q=true:=by
          intro i hi1 hiK q ⟨U,hU,hUq⟩
          have hq144 : q < 144:=(PackedRect.hull_spec U q hUq).1
          obtain ⟨y,hy,hyq,hyc⟩:=hCL.cov i U hi1 hiK (by
            intro r hr;obtain ⟨p,hp,hpi,hpr⟩:=hU r hr
            obtain ⟨x,hx,hcx,rfl⟩:=hmem_all p hp
            exact ⟨x,hx,hcx,hpi,hpr⟩) q hUq
          cases hb : Nat.beq (Nat.land (PackedRect.privH l y) t2) 0
          · right
            have hcy : PackedRect.isConf l y:=PackedRect.beq0_false (by rwa [← ht2_def])
            refine ⟨(Nat.land (PackedRect.rectW y) PackedRect.full,PackedRect.privH l y,c y), ?_,hyc hcy, ?_⟩
            · exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hy,by rw [hb];rfl⟩)
            · rw [PackedRect.tb_land,PackedRect.full_tb,hyq,decide_eq_true hq144];rfl
          · left
            rw [PackedRect.tb_land,PackedRect.full_tb,decide_eq_true hq144,Bool.and_true]
            exact PackedRect.fcov_tb t t2 q rs (PackedRect.rectW y) (List.mem_map_of_mem hy) hb hyq
        cases hK1 : Nat.beq K 1
        · dsimp only
          cases hK2 : Nat.beq K 2
          · rfl
          · dsimp only
            have hKe2 : K=2:=Nat.beq_eq.mp hK2
            rw [← hall_map]
            apply fGoK2_inv (M:=(· ∈ all))
            · intro q hq
              rcases hcov_gen 1 (by omega) (by omega) q hq with hl | ⟨p,hp,⟨hp1,hp2⟩,hpq⟩
              · exact Or.inl hl
              · exact Or.inr ⟨p,hp,by omega,hpq⟩
            · intro q hq
              rcases hcov_gen 2 (by omega) (by omega) q hq with hl | ⟨p,hp,⟨hp1,hp2⟩,hpq⟩
              · exact Or.inl hl
              · exact Or.inr ⟨p,hp,by omega,hpq⟩
            · exact fun p hp=>hp
            · intro p hp;have:=hall_K p hp;omega
            · exact hall_pw
            · intro _ _ _;simp
            · intro _ _ _;simp
            · intro _ _ _;simp
            · intro _ h;simp at h
            · intro _ h;simp at h
            · exact fun p hp _=>Or.inl hp
            · exact fun p hp _=>Or.inl hp
        · dsimp only
          have hKe1 : K=1:=Nat.beq_eq.mp hK1
          rw [← hall_map]
          apply fGoK1_inv (M:=(· ∈ all))
          · intro q hq
            rcases hcov_gen 1 (by omega) (by omega) q hq with hl | ⟨p,hp,⟨hp1,hp2⟩,hpq⟩
            · exact Or.inl hl
            · exact Or.inr ⟨p,hp,by omega,hpq⟩
          · exact fun p hp=>hp
          · intro p hp;have:=hall_K p hp;omega
          · exact hall_pw
          · intro _ _ _;simp
          · intro _ _ _;simp
          · intro _ h;simp at h
          · exact fun p hp _=>Or.inl hp
      · exfalso
        have hKe0 : K=0:=Nat.beq_eq.mp hK0
        have ht2_def : t2=PackedRect.t2Of l:=rfl
        have hex : ∃ q,t2.testBit q=true:=by
          by_contra! hall;apply ht2ne;apply Nat.eq_of_testBit_eq;intro q
          have hq:=hall q;cases h : t2.testBit q <;> simp_all
        obtain ⟨q,hq⟩:=hex
        have hpw : (rs.map (PackedRect.priv t)).Pairwise (fun a b => ¬(a.testBit q=true ∧ b.testBit q=true)):=by
          rw [List.pairwise_map,List.pairwise_map]
          refine List.Pairwise.imp_of_mem ?_ hCL.ne
          intro a b ha hb hne ⟨haq,hbq⟩
          have haq' : (PackedRect.privH l a).testBit q=true:=haq
          have hbq' : (PackedRect.privH l b).testBit q=true:=hbq
          have hca : PackedRect.isConf l a:=fun hz=>by
            have:=congrArg (fun n : Nat=>n.testBit q) hz
            rw [PackedRect.tb_land, ← ht2_def,haq',hq,Nat.zero_testBit] at this;exact Bool.noConfusion this
          have hcb : PackedRect.isConf l b:=fun hz=>by
            have:=congrArg (fun n : Nat=>n.testBit q) hz
            rw [PackedRect.tb_land, ← ht2_def,hbq',hq,Nat.zero_testBit] at this;exact Bool.noConfusion this
          have h0a:=hCL.le a ha hca
          have h0b:=hCL.le b hb hcb
          have hdisj:=hne hca hcb (by omega)
          exact PackedRect.land_zero_tb _ _ q hdisj haq hbq
        have hzero : ∀ (xs : List Word) (o tt : Word),
            tt.testBit q=false → (o.testBit q=true → ∀ a ∈ xs,a.testBit q=false) →
            xs.Pairwise (fun a b => ¬(a.testBit q=true ∧ b.testBit q=true)) →
            (PackedRect.tw xs o tt).testBit q=false:=by
          intro xs;induction xs with
          | nil=>intro o tt htt _ _;exact htt
          | cons a xs ih =>
            intro o tt htt ho hpx
            obtain ⟨ha,hxs⟩:=List.pairwise_cons.mp hpx
            apply ih (Nat.lor o a) (Nat.lor tt (Nat.land o a))
            · rw [PackedRect.tb_lor,Bool.or_eq_false_iff,PackedRect.tb_land]
              refine ⟨htt, ?_⟩
              cases hox : o.testBit q
              · simp
              · simp [ho hox a List.mem_cons_self]
            · intro hox b hb
              rw [PackedRect.tb_lor,Bool.or_eq_true] at hox
              rcases hox with h1 | h2
              · exact ho h1 b (List.mem_cons_of_mem _ hb)
              · cases hbq : b.testBit q
                · rfl
                · exact False.elim (ha b hb ⟨h2,hbq⟩)
            · exact hxs
        have hf:=hzero _ 0 0 (by simp) (by simp) hpw
        rw [hf] at hq;exact Bool.noConfusion hq
    · rfl
  · rfl
noncomputable def fKw64Term : {f : Nat → List Nat → Nat → List Word → Bool // f=fKw64Algo}:=by
  refine ⟨?f, ?proof⟩
  case proof =>
    delta fKw64Algo fMapChart fChartBits fDedup fContains fClassFromPrep fPrepRects fSplitItems
      fGoK1 fGoK2 fListLen
      PackedRect.mapW' PackedRect.tw' PackedRect.subM PackedRect.hull PackedRect.hullC
      PackedRect.rowsOf PackedRect.colsOf PackedRect.orS PackedRect.orSL PackedRect.rowM
      PackedRect.full PackedRect.rectW' PackedRect.rectRowMask PackedRect.rectRepeat
      PackedRect.rect' PackedRect.tb' PackedRect.band PackedRect.bor PackedRect.bnot fBand fBor fBnot unpack
    beta_reduce
    exact rfl
noncomputable def fKw64 : Nat → List Nat → Nat → List Word → Bool:=fKw64Term.1
theorem fKw64_sound {maxK : Nat} {mask goal : Word} {c : RowChart} {ws : List Word} {k fuel : Nat}
    (ok : ChartOK goal c) (nd : ws.Nodup) (cap : k ≤ fuel)
    (live : LiveWord mask goal k 0 ws.toFinset) :
    fKw64 maxK c.val fuel ws=true:=by
  rw [show fKw64=fKw64Algo from fKw64Term.2]
  unfold fKw64Algo
  rw [fForceWords_eq,fMapChart_eq,fListLen_eq]
  cases htight : Nat.beq ws.length (Nat.add fuel 1)
  · dsimp only
    rw [fForceWords_eq,fListLen_eq]
    cases Nat.blt maxK (Nat.sub (Nat.add fuel 1) (fDedup (ws.map (chartWord c))).length)
    · dsimp only
      rw [fForceWords_eq,PackedRect.mapW'_eq,fForce_eq,PackedRect.tw'_eq]
      obtain ⟨k',S',hk',hsub,hR⟩:=liveToReachChart ok live
      let l:=fDedup (ws.map (chartWord c))
      have hndL : l.Nodup:=fDedup_nodup _
      have hsubL : S' ⊆ l.toFinset:=fun x hx=>by
        rw [List.mem_toFinset,fDedup_mem];exact List.mem_toFinset.mp (by simpa using hsub hx)
      let l':=S'.toList
      have hnd' : l'.Nodup:=Finset.nodup_toList S'
      have hset' : l'.toFinset=S':=by ext x;simp [l']
      have hlen' : l'.length=S'.card:=Finset.length_toList S'
      obtain ⟨col,hVL⟩:=PackedRect.reach_validLab hnd' (hset'.symm ▸ hR)
      have hsub' : ∀ x ∈ l',x ∈ l:=fun x hx=>List.mem_toFinset.mp (hsubL (Finset.mem_toList.mp hx))
      let tL:=PackedRect.tw (l.map PackedRect.rectW) 0 0
      have hprivSub : ∀ x q,(PackedRect.privH l x).testBit q=true →
          (PackedRect.priv (PackedRect.tw (l'.map PackedRect.rectW) 0 0) (PackedRect.rectW x)).testBit q=true:=by
        intro x q hq
        apply hullMonotone _ hq
        intro r hr144 hr
        rw [PackedRect.tb_land,PackedRect.tb_xor,Bool.and_eq_true] at hr ⊢
        refine ⟨hr.1, ?_⟩
        have h1 : tL.testBit r=false:=by
          have:=hr.2;rw [PackedRect.full_tb,decide_eq_true hr144] at this
          dsimp only [tL] at this ⊢
          cases h : (PackedRect.tw (l.map PackedRect.rectW) 0 0).testBit r <;> simp_all
        have h2 : (PackedRect.tw (l'.map PackedRect.rectW) 0 0).testBit r=false:=by
          by_contra ht
          have ht1 : (PackedRect.tw (l'.map PackedRect.rectW) 0 0).testBit r=true:=by
            cases h : (PackedRect.tw (l'.map PackedRect.rectW) 0 0).testBit r <;> simp_all
          have:=twSublist hnd' hsub' ht1
          rw [h1] at this;exact Bool.noConfusion this
        rw [h2,PackedRect.full_tb,decide_eq_true hr144];rfl
      have hprivMem : ∀ x ∈ l,
          Nat.land (Nat.land (PackedRect.rectW x) (Nat.xor tL PackedRect.full)) PackedRect.full ≠ 0 → x ∈ S':=by
        intro x hx hne
        have hex : ∃ q,(Nat.land (Nat.land (PackedRect.rectW x) (Nat.xor tL PackedRect.full)) PackedRect.full).testBit q=true:=by
          by_contra! hall;apply hne;apply Nat.eq_of_testBit_eq;intro q
          have hq:=hall q;cases h : (Nat.land (Nat.land (PackedRect.rectW x) (Nat.xor tL PackedRect.full)) PackedRect.full).testBit q <;> simp_all
        obtain ⟨q,hq⟩:=hex
        rw [PackedRect.tb_land,PackedRect.tb_land,PackedRect.tb_xor,PackedRect.full_tb,
          Bool.and_eq_true,Bool.and_eq_true,decide_eq_true_eq] at hq
        obtain ⟨⟨hrx,htx⟩,hq144⟩:=hq
        have htf : tL.testBit q=false:=by cases h : tL.testBit q <;> simp_all
        obtain ⟨y,hyS,hry⟩:=PackedRect.sep_bit hR q hq144
        have hyL : y ∈ l:=List.mem_toFinset.mp (hsubL hyS)
        have hpw:=List.pairwise_map.mp (PackedRect.tw_spec q (l.map PackedRect.rectW) 0 0 htf).2.2
        have hxy : x=y:=by by_contra hne';exact pairwiseDisjRect hpw hx hyL hne' ⟨hrx,hry⟩
        rwa [hxy]
      have hsubAll : ∀ a ∈ l.map PackedRect.rectW,PackedRect.subM (PackedRect.priv tL a) a=true:=by
        intro a ha;obtain ⟨x,hx,rfl⟩:=List.mem_map.mp ha
        unfold PackedRect.subM
        apply Nat.beq_eq.mpr
        apply PackedRect.land_sub
        intro q hq
        by_cases hnz : Nat.land (Nat.land (PackedRect.rectW x) (Nat.xor tL PackedRect.full)) PackedRect.full=0
        · exfalso
          have hp0 : PackedRect.priv tL (PackedRect.rectW x)=0:=by
            change PackedRect.hullC (Nat.land (Nat.land (PackedRect.rectW x) (Nat.xor tL PackedRect.full)) PackedRect.full)=0
            rw [hnz];exact hullC_zero_eq
          rw [hp0,Nat.zero_testBit] at hq;exact Bool.noConfusion hq
        · have hx' : x ∈ l':=Finset.mem_toList.mpr (hprivMem x hx hnz)
          exact hVL.2.2.2 x hx' q (hprivSub x q hq)
      rw [fPrepRects_spec hsubAll,fBand_eq,Bool.and_eq_true]
      have hpEq : (0+((l.map PackedRect.rectW).filter (fun a => !Nat.beq (Nat.land (Nat.land a (Nat.xor tL PackedRect.full)) PackedRect.full) 0)).length)=privCount l:=by
        unfold privCount;dsimp only;rw [PackedRect.mapW'_eq,PackedRect.tw'_eq];simp [tL]
      rw [hpEq]
      have hpLe : privCount l ≤ fuel+1:=by
        let lP:=l.filter (fun x => !Nat.beq (Nat.land (Nat.land (PackedRect.rectW x) (Nat.xor tL PackedRect.full)) PackedRect.full) 0)
        have hfeq : privCount l=lP.length:=by
          unfold privCount;dsimp only;rw [PackedRect.mapW'_eq,PackedRect.tw'_eq,List.filter_map,List.length_map];rfl
        have hlPsub : lP.toFinset ⊆ S':=fun x hx=>by
          have hf:=List.mem_filter.mp (List.mem_toFinset.mp hx)
          exact hprivMem x hf.1 (fun hz=>by have hf2:=hf.2;rw [hz] at hf2;exact Bool.noConfusion hf2)
        have hpS : lP.length ≤ S'.card:=by
          rw [← List.toFinset_card_of_nodup (hndL.filter _)];exact Finset.card_le_card hlPsub
        have hScard : S'.card ≤ k'+1:=hR.card
        omega
      refine ⟨Nat.ble_eq.mpr hpLe, ?_⟩
      have hconfIn : ∀ x ∈ l,PackedRect.isConf l x → x ∈ l':=by
        intro x hx hconf
        apply Finset.mem_toList.mpr;apply hprivMem x hx;intro hz;apply hconf
        apply Nat.eq_of_testBit_eq;intro q;rw [PackedRect.tb_land,Nat.zero_testBit]
        cases hp : (PackedRect.privH l x).testBit q
        · simp
        · obtain ⟨hql,i,_,hi,_,h1,_⟩:=PackedRect.hull_spec _ q hp
          have hbit:=congrArg (fun n : Nat=>n.testBit (12*(q / 12)+i)) hz
          have hlt : 12*(q / 12)+i < 144:=by omega
          rw [PackedRect.tb_land,PackedRect.full_tb,decide_eq_true hlt,Bool.and_true,Nat.zero_testBit] at hbit
          rw [hbit] at h1;exact Bool.noConfusion h1
      have hpLeS : privCount l ≤ S'.card:=by
        let lP:=l.filter (fun x => !Nat.beq (Nat.land (Nat.land (PackedRect.rectW x) (Nat.xor tL PackedRect.full)) PackedRect.full) 0)
        have hlPsub : lP.toFinset ⊆ S':=fun x hx=>by
          have hf:=List.mem_filter.mp (List.mem_toFinset.mp hx)
          exact hprivMem x hf.1 (fun hz=>by have hf2:=hf.2;rw [hz] at hf2;simp at hf2)
        have hfeq : privCount l=lP.length:=by
          unfold privCount;dsimp only;rw [PackedRect.mapW'_eq,PackedRect.tw'_eq,List.filter_map,List.length_map];rfl
        rw [hfeq, ← List.toFinset_card_of_nodup (hndL.filter _)]
        exact Finset.card_le_card hlPsub
      have hScard : S'.card ≤ k'+1:=hR.card
      have hKge : Nat.sub (Nat.succ k') l'.length ≤ Nat.sub (Nat.add fuel 1) (privCount l):=by
        change (k'+1) - l'.length ≤ (fuel+1) - privCount l;omega
      have hCL : PackedRect.ClassLab l (Nat.sub (Nat.add fuel 1) (privCount l)) col:=by
        refine ⟨?_, ?_, ?_⟩
        · intro x hx hconf;exact Nat.le_trans (hVL.1 x (hconfIn x hx hconf)) hKge
        · refine List.Pairwise.imp_of_mem ?_ hndL
          intro x y hx hy hne hcx hcy hceq
          have hdisj:=hVL.2.1 x (hconfIn x hx hcx) y (hconfIn y hy hcy) hne hceq
          apply PackedRect.land_disj;intro q h1 h2
          have hb:=congrArg (fun n : Nat=>n.testBit q) hdisj
          rw [PackedRect.tb_land,hprivSub x q h1,hprivSub y q h2,Nat.zero_testBit] at hb
          exact Bool.noConfusion hb
        · intro i U hi1 _ hU q hq
          have hU' : ∀ r,U.testBit r=true →
              ∃ x ∈ l',col x=i ∧ (PackedRect.priv (PackedRect.tw (l'.map PackedRect.rectW) 0 0) (PackedRect.rectW x)).testBit r=true:=by
            intro r hr;obtain ⟨x,hx,hcx,hceq,hpx⟩:=hU r hr
            exact ⟨x,hconfIn x hx hcx,hceq,hprivSub x r hpx⟩
          obtain ⟨y,hy',hc1,hci,hry⟩:=hVL.2.2.1 i U hi1 hU' q hq
          exact ⟨y,hsub' y hy',hry,fun _=>⟨hc1,hci⟩⟩
      simpa only [List.append_nil] using fClassFromPrep_sound (maxK:=maxK) hCL
    · rfl
  · dsimp only
    rw [fFastRect_eq]
    have hlen : ws.length=fuel+1:=Nat.beq_eq.mp htight
    have hcard:=(liveWordSize live).2
    rw [List.toFinset_card_of_nodup nd] at hcard
    have hk : ws.toFinset.card=k+1:=by
      have:=List.toFinset_card_of_nodup nd;omega
    exact chartRectangles ok nd (kwFromLive live hk)
noncomputable def fKwSafeCheck (maxK : Nat) (is24 : Bool) (chart : Option RowChart) (fuel : Nat) (ws : List Word) : Bool :=
 @Bool.rec (fun _=>Bool)
 (@Option.rec RowChart (fun _=>Bool) true (fun c=>fKw64 maxK c.val fuel ws) chart)
 true
 is24
theorem fKwSafeSound {maxK : Nat} {is24 : Bool} {mask goal : Word} {chart : Option RowChart}
    {ws : List Word} {k fuel : Nat}
    (is24Spec : is24=true → mask=16777215 ∧ goal=4095)
    (chartOK : ∀ c,chart=some c → ChartOK goal c)
    (nd : ws.Nodup) (cap : k ≤ fuel) (live : LiveWord mask goal k 0 ws.toFinset) :
    fKwSafeCheck maxK is24 chart fuel ws=true:=by
  unfold fKwSafeCheck
  cases h24 : is24
  · dsimp only
    cases hc : chart with
    | none=>rfl
    | some c=>exact fKw64_sound (chartOK c hc) nd cap live
  · rfl
noncomputable def fDagLocal (maxK : Nat) (is24 : Bool) (mask goal : Word) (chart : Option RowChart)
    (cut : CutCheck1) (state : RowState1) : Bool :=
  let (fuel,nots,ws,_):=state
  let n:=fListLen ws
  fBor (Nat.blt (Nat.add fuel 1) (Nat.add n nots))
    (@Bool.rec (fun _=>Bool)
      (fBor (Nat.beq fuel 0)
        (@Bool.rec (fun _=>Bool)
          (fBor (cut state) (fBnot (fPartitionRun false ws goal (Nat.xor mask goal))))
          (@Bool.rec (fun _=>Bool)
            (fBor (cut state)
              (fBor (fBnot (fPartitionRun true ws goal (Nat.xor mask goal)))
                (fBnot (fKwSafeCheck maxK is24 chart fuel ws))))
            (fBor (fBnot (fKwSafeCheck maxK is24 chart fuel ws))
              (fBor (cut state)
                (fBnot (fPartitionRun true ws goal (Nat.xor mask goal)))))
            (Nat.beq n (Nat.add fuel 1)))
          (Nat.beq nots 0)))
      false
      (fBand (Nat.beq nots 0) (fContains goal ws)))
theorem fDagLocalOpen {maxK : Nat} {is24 : Bool} {mask goal : Word} {chart : Option RowChart}
    {cut : CutCheck1} {state : RowState1}
    (is24Spec : is24=true → mask=16777215 ∧ goal=4095)
    (masked : Masked mask goal) (chartOK : ∀ c,chart=some c → ChartOK goal c)
    (viable : WordViable1 mask goal state) (noCut : cut state=false) :
    fDagLocal maxK is24 mask goal chart cut state=false:=by
  obtain ⟨fuel,nots,ws,history⟩:=state
  obtain ⟨nd,k,cap,live⟩:=viable
  change k ≤ fuel at cap
  have card:=(liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change ws.length+nots ≤ k+1 at card
  unfold fDagLocal
  simp only [fListLen_eq,fBor_eq,fBand_eq,fBnot_eq,fContains_eq,fPartitionRun_eq]
  have hfit : Nat.blt (Nat.add fuel 1) (Nat.add ws.length nots)=false:=by
    cases h : Nat.blt (Nat.add fuel 1) (Nat.add ws.length nots)
    · rfl
    · have hlt : fuel+1 < ws.length+nots:=Nat.blt_eq.mp h;omega
  rw [hfit,Bool.false_or]
  cases hhit : (Nat.beq nots 0&&ws.contains goal)
  · dsimp only
    have hfp : Nat.beq fuel 0=false:=by
      cases hz : Nat.beq fuel 0
      · rfl
      · exfalso
        have hfz : fuel=0:=Nat.beq_eq.mp hz
        have kz : k=0:=by omega
        subst k
        obtain ⟨ht0,eq,_⟩:=live
        change nots=0 at ht0
        have hm : goal ∈ ws:=List.mem_toFinset.mp (by rw [eq];simp)
        have : (Nat.beq nots 0&&ws.contains goal)=true:=by
          rw [ht0,Nat.beq_refl,List.contains_iff_mem.mpr hm];rfl
        rw [this] at hhit;exact Bool.noConfusion hhit
    rw [hfp,Bool.false_or]
    cases hn0 : Nat.beq nots 0
    · dsimp only
      have hpart : dagPartition1 false ws goal (Nat.xor mask goal)=true :=
        dagPartition1Live (directed:=false) masked live (fun h=>Bool.noConfusion h)
      rw [noCut,hpart];rfl
    · dsimp only
      have ht0 : nots=0:=Nat.beq_eq.mp hn0
      subst ht0
      have hpart : dagPartition1 true ws goal (Nat.xor mask goal)=true :=
        dagPartition1Live (directed:=true) masked live (fun _=>rfl)
      have hkw:=fKwSafeSound (maxK:=maxK) is24Spec chartOK nd cap live
      cases Nat.beq ws.length (Nat.add fuel 1) <;> dsimp only <;> rw [noCut,hpart,hkw] <;> rfl
  · rfl
abbrev DagBucket1:=Nat → Option DagLink1
abbrev DagBuckets1:=Nat → (DagBucket1 → Bool) → Bool
def BucketsValid (buckets : DagBuckets1) : Prop :=
 ∀ p k,buckets p k=true → ∃ f : DagBucket1,k f=true
def dagScanBucket (entries : List (Nat × Nat × Nat)) (token : Nat) : Option DagLink1 :=
 List.rec none (fun e _ next =>
 @Bool.rec (fun _=>Option DagLink1)
 (@Bool.rec (fun _=>Option DagLink1) next none (Nat.blt token e.1))
 (some (e.2.1,e.2.2))
 (Nat.beq token e.1)) entries
def dagUnpackBucket (data width entryMask tokenBits tokenMask destMask autoShift : Nat)
 (size offset : Nat) (k : List (Nat × Nat × Nat) → Bool) : Bool :=
 (Nat.rec (motive:=fun _=>Nat → (List (Nat × Nat × Nat) → Bool) → Bool)
 (fun _ f=>f [])
 (fun _ next idx f =>
 fForce (Nat.land (Nat.shiftRight data (Nat.mul width idx)) entryMask) fun code =>
 fForce (Nat.land code tokenMask) fun tok =>
 fForce (Nat.land (Nat.shiftRight code tokenBits) destMask) fun dest =>
 fForce (Nat.shiftRight code autoShift) fun auto =>
 next (Nat.add idx 1) (fun rest=>f ((tok,dest,auto) :: rest)))
 size) offset k
theorem dagUnpackBucket_ex (data width entryMask tokenBits tokenMask destMask autoShift size offset : Nat)
    (k : List (Nat × Nat × Nat) → Bool)
    (h : dagUnpackBucket data width entryMask tokenBits tokenMask destMask autoShift size offset k=true) :
    ∃ entries,k entries=true:=by
  induction size generalizing offset k with
  | zero=>exact ⟨[],h⟩
  | succ s ih =>
    have h1 : dagUnpackBucket data width entryMask tokenBits tokenMask destMask autoShift s (Nat.add offset 1)
        (fun rest=>k ((Nat.land (Nat.land (Nat.shiftRight data (Nat.mul width offset)) entryMask) tokenMask,
          Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight data (Nat.mul width offset)) entryMask) tokenBits) destMask,
          Nat.shiftRight (Nat.land (Nat.shiftRight data (Nat.mul width offset)) entryMask) autoShift) :: rest))=true:=by
      unfold dagUnpackBucket at h ⊢
      dsimp only at h
      simp only [fForce_eq] at h ⊢
      exact h
    obtain ⟨rest,hr⟩:=ih _ _ h1
    exact ⟨_ :: rest,hr⟩
def dagBinBucket (data width entryMask tokenBits tokenMask destMask autoShift trials lo hi token : Nat) :
 Option DagLink1 :=
 (Nat.rec (motive:=fun _=>Nat → Nat → Option DagLink1) (fun _ _=>none)
 (fun _ next l h =>
 @Bool.rec (fun _=>Option DagLink1) none
 (fForce (Nat.div (Nat.add l h) 2) fun mid =>
 fForce (Nat.land (Nat.shiftRight data (Nat.mul width mid)) entryMask) fun code =>
 fForce (Nat.land code tokenMask) fun key =>
 @Bool.rec (fun _=>Option DagLink1)
 (@Bool.rec (fun _=>Option DagLink1)
 (fForce (Nat.add mid 1) fun mid1=>next mid1 h)
 (next l mid)
 (Nat.blt token key))
 (some (Nat.land (Nat.shiftRight code tokenBits) destMask,Nat.shiftRight code autoShift))
 (Nat.beq token key))
 (Nat.blt l h))
 trials) lo hi
def dagBucketBlock (index data indexWidth indexMask sizeBits sizeMask width entryMask
 tokenBits tokenMask destMask autoShift trials : Nat) (parent : Nat) (k : DagBucket1 → Bool) : Bool :=
 fForce (Nat.land (Nat.shiftRight index (Nat.mul indexWidth parent)) indexMask) fun entry =>
 fForce (Nat.land entry sizeMask) fun size =>
 @Bool.rec (fun _=>Bool)
 (fForce (Nat.shiftRight entry sizeBits) fun off =>
 @Bool.rec (fun _=>Bool)
 (fForce (Nat.add off size) fun hi =>
 k (dagBinBucket data width entryMask tokenBits tokenMask destMask autoShift trials off hi))
 (dagUnpackBucket data width entryMask tokenBits tokenMask destMask autoShift size off fun entries =>
 k (dagScanBucket entries))
 (Nat.ble size 8))
 (k (fun _=>none))
 (Nat.beq size 0)
theorem dagBucketBlock_valid (index data indexWidth indexMask sizeBits sizeMask width entryMask
    tokenBits tokenMask destMask autoShift trials : Nat) :
    BucketsValid (dagBucketBlock index data indexWidth indexMask sizeBits sizeMask width entryMask
      tokenBits tokenMask destMask autoShift trials):=by
  intro parent k h
  unfold dagBucketBlock at h
  simp only [fForce_eq] at h
  cases h0 : Nat.beq (Nat.land (Nat.land (Nat.shiftRight index (Nat.mul indexWidth parent)) indexMask) sizeMask) 0
  · rw [h0] at h;dsimp only at h
    cases hle : Nat.ble (Nat.land (Nat.land (Nat.shiftRight index (Nat.mul indexWidth parent)) indexMask) sizeMask) 8
    · rw [hle] at h;dsimp only at h;exact ⟨_,h⟩
    · rw [hle] at h;dsimp only at h
      obtain ⟨entries,he⟩:=dagUnpackBucket_ex _ _ _ _ _ _ _ _ _ _ h
      exact ⟨dagScanBucket entries,he⟩
  · rw [h0] at h;exact ⟨fun _=>none,h⟩
abbrev DagMovesFn1:=Nat → Option WordMove
def DagMovesFnOK1 (mask goal : Word) (width : Nat) (moves : DagMovesFn1) : Prop :=
 ∀ (a : Nat) (m : WordMove),moves a=some m →
 ∃ select : Fin width → Fin width,DagAuto mask goal select ∧
 ∀ w,Masked mask w → mixMove m w=relabel select w
noncomputable def fDagRefTree (count : Nat) (forest : Forest)
    (lightStates : Nat → Option LightState1) (moves : DagMovesFn1)
    (parent : Nat) (bucket : DagBucket1) (token : Nat) (state : RowState1) : Bool :=
  @Option.rec DagLink1 (fun _=>Bool) false
    (fun lnk =>
      fBand (Nat.blt lnk.1 count)
        (fBor
          (fBand (Nat.beq lnk.2 0)
            (let pt:=forest lnk.1
             fBand (Nat.beq pt.1 parent) (Nat.beq pt.2 token)))
          (@Option.rec LightState1 (fun _=>Bool) false
            (fun saved =>
              fBand (Nat.beq saved.1 state.1)
                (fBand (Nat.beq saved.2.1 state.2.1)
                  (@Bool.rec (fun _=>Bool)
                    (@Option.rec WordMove (fun _=>Bool) false
                      (fun m=>fListEq saved.2.2 (fDagMoveWordsRun m state.2.2.1))
                      (moves lnk.2))
                    (fListEq saved.2.2 state.2.2.1)
                    (Nat.beq lnk.2 0))))
            (lightStates lnk.1))))
    (bucket token)
noncomputable def fDagRefTreeTerm :
    {f : Nat → Forest → (Nat → Option LightState1) → DagMovesFn1 → Nat → DagBucket1 → Nat → RowState1 → Bool // f=fDagRefTree}:=by
  refine ⟨?f, ?proof⟩
  case proof =>
    delta fDagRefTree fListEq fBand fBor
    beta_reduce
    exact rfl
noncomputable def fDagRefRun:=fDagRefTreeTerm.1
theorem fDagLinkedTree {mask goal : Word} {width fuel initNots count parent token : Nat}
    {stock : List Word} {forest : Forest} {moves : DagMovesFn1} {bucket : DagBucket1}
    {state : RowState1}
    (hTree : ∀ dest,forest dest=(parent,token) →
      dagTrace1 mask stock fuel initNots forest dest=some state)
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesFnOK1 mask goal width moves)
    (masked : ∀ w ∈ state.2.2.1,Masked mask w)
    (ok : fDagRefRun count forest (fDagTraceLight mask stock fuel initNots forest) moves parent bucket token state=true)
    {k : Nat} (live : LiveWord mask goal k state.2.1 state.2.2.1.toFinset) :
    ∃ i saved,i < count ∧ dagTrace1 mask stock fuel initNots forest i=some saved ∧
      saved.1=state.1 ∧ saved.2.1=state.2.1 ∧
      LiveWord mask goal k saved.2.1 saved.2.2.1.toFinset:=by
  rw [show fDagRefRun=fDagRefTree from fDagRefTreeTerm.2] at ok
  unfold fDagRefTree at ok
  cases hb : bucket token with
  | none=>rw [hb] at ok;exact Bool.noConfusion ok
  | some lnk =>
    obtain ⟨dest,auto⟩:=lnk
    rw [hb] at ok;dsimp only at ok
    rw [fBand_eq,fBor_eq,Bool.and_eq_true,Nat.blt_eq,Bool.or_eq_true] at ok
    obtain ⟨hdest,htree | hslow⟩:=ok
    · rw [fBand_eq,fBand_eq,Bool.and_eq_true,Bool.and_eq_true,Nat.beq_eq,Nat.beq_eq,Nat.beq_eq] at htree
      obtain ⟨_,hp,ht⟩:=htree
      have hfor : forest dest=(parent,token):=Prod.ext hp ht
      exact ⟨dest,state,hdest,hTree dest hfor,rfl,rfl,live⟩
    · rw [fDagTraceLight_eq] at hslow
      cases hs : dagTrace1 mask stock fuel initNots forest dest with
      | none=>rw [hs] at hslow;exact Bool.noConfusion hslow
      | some saved =>
        rw [hs] at hslow;dsimp only [Option.map] at hslow
        rw [fBand_eq,fBand_eq,Bool.and_eq_true,Bool.and_eq_true,Nat.beq_eq,Nat.beq_eq] at hslow
        obtain ⟨hf,hn,hws⟩:=hslow
        refine ⟨dest,saved,hdest,hs,hf,hn, ?_⟩
        rw [hn]
        cases ha : Nat.beq auto 0
        · rw [ha] at hws;dsimp only at hws
          cases hm : moves auto with
          | none=>rw [hm] at hws;exact Bool.noConfusion hws
          | some m =>
            rw [hm] at hws;dsimp only at hws
            rw [fListEq_eq,fDagMoveWordsRun_eq] at hws
            have same : saved.2.2.1=dagMoveWords m state.2.2.1:=beq_iff_eq.mp hws
            obtain ⟨select,autoOk,agree⟩:=valid auto m hm
            rw [same,dagMoveSet (fun w hw=>agree w (masked w hw))]
            exact liveMaskedImage autoOk bounds live (fun w hw=>masked _ (List.mem_toFinset.mp hw))
        · rw [ha] at hws;dsimp only at hws
          rw [fListEq_eq] at hws
          have same : saved.2.2.1=state.2.2.1:=beq_iff_eq.mp hws
          rwa [same]
def fPackWords (stride : Nat) (ws : List Word) : Word :=
  let m:=Nat.sub (Nat.shiftLeft 1 stride) 1
  List.rec 0 (fun w _ tail=>Nat.lor (Nat.land w m) (Nat.shiftLeft tail stride)) ws
def fLaneMarks (stride n : Nat) : Word :=
 Nat.rec 0 (fun _ more=>Nat.lor 1 (Nat.shiftLeft more stride)) n
theorem fPackBits {stride : Nat} {ws : List Word} {i row : Nat} (inside : i < ws.length) (width : row < stride) :
    (fPackWords stride ws).testBit (stride*i+row)=(ws.getD i 0).testBit row:=by
  induction ws generalizing i with
  | nil=>simp at inside
  | cons w ws ih =>
    change ((w&&&(1<<<stride - 1))|||(fPackWords stride ws<<<stride)).testBit (stride*i+row)=_
    rw [Nat.testBit_or,Nat.testBit_and,Nat.testBit_shiftLeft,show (1<<<stride)=2 ^ stride by rw [Nat.shiftLeft_eq,Nat.one_mul]]
    cases i with
    | zero =>
      have hm : (2 ^ stride - 1).testBit row=true:=by rw [Nat.testBit_two_pow_sub_one];simp [width]
      have hnl : ¬ stride ≤ row:=by omega
      simp [hm,hnl]
    | succ i =>
      have hi : i < ws.length:=by simpa using inside
      have hmul : stride*(i+1)=stride*i+stride:=Nat.mul_succ stride i
      have hm : (2 ^ stride - 1).testBit (stride*i.succ+row)=false:=by
        rw [Nat.testBit_two_pow_sub_one]
        have : ¬ stride*(i+1)+row < stride:=by rw [hmul];omega
        simp [this]
      have crossed : stride ≤ stride*i.succ+row:=by change stride ≤ stride*(i+1)+row;rw [hmul];omega
      have offset : stride*i.succ+row - stride=stride*i+row:=by change stride*(i+1)+row - stride=_;rw [hmul];omega
      simp [hm,crossed,offset,ih hi]
theorem fMarkBits {stride length i : Nat} (inside : i < length) :
    (fLaneMarks stride length).testBit (stride*i)=true:=by
  induction length generalizing i with
  | zero=>omega
  | succ length ih =>
    change (1|||(fLaneMarks stride length<<<stride)).testBit (stride*i)=true
    rw [Nat.testBit_or,Nat.testBit_shiftLeft]
    cases i with
    | zero=>simp
    | succ i =>
      have hi : i < length:=by simpa using inside
      have hmul : stride*(i+1)=stride*i+stride:=Nat.mul_succ stride i
      have crossed : stride ≤ stride*i.succ:=by change stride ≤ stride*(i+1);rw [hmul];omega
      have offset : stride*i.succ - stride=stride*i:=by change stride*(i+1) - stride=_;rw [hmul];omega
      simp [crossed,offset,ih hi]
def fHighest (steps : Nat) (value : Word) : Nat :=
  (Nat.rec (motive:=fun _=>Word → Nat → Nat) (fun _ offset=>offset)
    (fun i next w offset =>
      let shift:=Nat.shiftLeft 1 i
      fForce (Nat.shiftRight w shift) fun upper =>
        @Bool.rec (fun _=>Nat) (next upper (Nat.add offset shift)) (next w offset) (Nat.beq upper 0))
    steps) value 0
def fSignalContrast (directed : Bool) (full : Word) (tag : DagSignals1) : Word :=
 @Bool.rec (fun _=>Word) (Nat.xor tag.1 tag.2) (Nat.land tag.1 (Nat.xor tag.2 full)) directed
def fCountSigns (directed : Bool) (full : Word) (tags : List DagSignals1)
 (use : DagCounts1 → Bool) : Bool :=
 (List.rec (motive:=fun _=>(DagCounts1 → Bool) → Bool) (fun k=>k (0,0,0))
 (fun tag _ more k =>
 fForce (fSignalContrast directed full tag) fun column =>
 more fun acc =>
 fForce (Nat.lor acc.1 column) fun once =>
 fForce (Nat.lor acc.2.1 (Nat.land acc.1 column)) fun twice =>
 fForce (Nat.lor acc.2.2 (Nat.land acc.2.1 column)) fun thrice=>k (once,twice,thrice))
 tags) use
theorem fCountSigns_eq (directed : Bool) (full : Word) (tags : List DagSignals1) (use : DagCounts1 → Bool) :
    fCountSigns directed full tags use =
      use (tags.foldr (fun tag acc =>
        let c:=fSignalContrast directed full tag
        (Nat.lor acc.1 c,Nat.lor acc.2.1 (Nat.land acc.1 c),Nat.lor acc.2.2 (Nat.land acc.2.1 c))) (0,0,0)):=by
  induction tags generalizing use with
  | nil=>rfl
  | cons tag tags ih =>
    change fForce (fSignalContrast directed full tag) (fun column =>
      fCountSigns directed full tags (fun acc =>
        fForce (Nat.lor acc.1 column) (fun once =>
          fForce (Nat.lor acc.2.1 (Nat.land acc.1 column)) (fun twice =>
            fForce (Nat.lor acc.2.2 (Nat.land acc.2.1 column)) (fun thrice=>use (once,twice,thrice))))))=_
    simp only [fForce_eq,ih];rfl
def SampleValid (stride : Nat) (mask goal : Word) (sample : DagSample1) : Prop :=
  ∀ idx < sample.2,
    let code:=unpack sample.1 18 idx
    let p:=Nat.land code 511
    let n:=Nat.shiftRight code 9
    goal.testBit p=true ∧ mask.testBit n=true ∧ goal.testBit n=false ∧ p < stride ∧ n < stride
def sampleValidCheck (stride : Nat) (mask goal : Word) (sample : DagSample1) : Bool :=
  treeBlock 0 sample.2 fun idx =>
    let code:=fUnpack sample.1 18 idx
    let p:=Nat.land code 511
    let n:=Nat.shiftRight code 9
    fTestBit goal p&&fTestBit mask n && !fTestBit goal n&&Nat.blt p stride&&Nat.blt n stride
theorem sampleValidOfCheck {stride : Nat} {mask goal : Word} {sample : DagSample1}
    (ok : sampleValidCheck stride mask goal sample=true) :
    SampleValid stride mask goal sample:=by
  intro idx hidx
  have h:=treeBlock_at ok (Nat.zero_le idx) (by simpa using hidx)
  simp only [fUnpack_eq,fTestBit_eq,Bool.and_eq_true,Bool.not_eq_true',Nat.blt_eq] at h
  exact ⟨h.1.1.1.1,h.1.1.1.2,h.1.1.2,h.1.2,h.2⟩
theorem xor_land_full_lt (s x : Nat) :
    Nat.xor (Nat.sub (Nat.shiftLeft 1 s) 1) (Nat.land x (Nat.sub (Nat.shiftLeft 1 s) 1)) < 2 ^ s:=by
  have hfull : Nat.sub (Nat.shiftLeft 1 s) 1=2 ^ s - 1:=by
    change (1<<<s) - 1=2 ^ s - 1;rw [Nat.shiftLeft_eq,Nat.one_mul]
  rw [hfull]
  have hmask : Nat.xor (2 ^ s - 1) (Nat.land x (2 ^ s - 1)) =
      (Nat.xor (2 ^ s - 1) (Nat.land x (2 ^ s - 1)))&&&(2 ^ s - 1):=by
    apply Nat.eq_of_testBit_eq;intro q
    rw [Nat.testBit_and,PackedRect.tb_xor,PackedRect.tb_land]
    cases (2 ^ s - 1).testBit q <;> cases x.testBit q <;> decide
  rw [hmask,Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos s)
theorem fHighest_lt {steps v lim : Nat} (hv : v ≠ 0) (hlt : v < 2 ^ lim) :
    fHighest steps v < lim:=by
  suffices h : ∀ (st rem acc d : Nat),rem ≠ 0 → rem < 2 ^ d →
      (Nat.rec (motive:=fun _=>Word → Nat → Nat) (fun _ offset=>offset)
        (fun i next w offset =>
          let shift:=Nat.shiftLeft 1 i
          fForce (Nat.shiftRight w shift) fun upper =>
            @Bool.rec (fun _=>Nat) (next upper (Nat.add offset shift)) (next w offset) (Nat.beq upper 0))
        st) rem acc < acc+d by
    simpa [fHighest] using h steps v 0 lim hv hlt
  intro st
  induction st with
  | zero =>
    intro rem acc d hne hlt
    change acc < acc+d
    have hd : 0 < d:=by
      cases d with
      | zero=>simp at hlt;exact absurd hlt hne
      | succ _=>exact Nat.succ_pos _
    omega
  | succ s ih =>
    intro rem acc d hne hlt
    dsimp only
    rw [fForce_eq]
    have hsh : Nat.shiftLeft 1 s=2 ^ s:=by change 1<<<s=2 ^ s;rw [Nat.shiftLeft_eq,Nat.one_mul]
    cases hz : Nat.beq (Nat.shiftRight rem (Nat.shiftLeft 1 s)) 0
    · dsimp only
      have hnz : rem>>>2 ^ s ≠ 0:=by
        intro h0;rw [hsh] at hz;change Nat.beq (rem>>>2 ^ s) 0=false at hz;rw [h0] at hz;exact Bool.noConfusion hz
      have hdiv : rem>>>2 ^ s=rem / 2 ^ (2 ^ s):=Nat.shiftRight_eq_div_pow rem (2 ^ s)
      have hle : 2 ^ (2 ^ s) ≤ rem:=by
        by_contra hlt2
        have hlt3 : rem < 2 ^ (2 ^ s):=Nat.lt_of_not_ge hlt2
        exact hnz (hdiv.trans (Nat.div_eq_of_lt hlt3))
      have hsd : 2 ^ s < d:=by
        by_contra hge
        have hle2 : d ≤ 2 ^ s:=Nat.le_of_not_lt hge
        have hp : 2 ^ d ≤ 2 ^ (2 ^ s):=Nat.pow_le_pow_right (by decide) hle2
        omega
      have hrem2 : rem>>>2 ^ s < 2 ^ (d - 2 ^ s):=by
        rw [hdiv,Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,Nat.sub_add_cancel (Nat.le_of_lt hsd)]
        exact hlt
      have hrec:=ih (Nat.shiftRight rem (Nat.shiftLeft 1 s)) (Nat.add acc (Nat.shiftLeft 1 s)) (d - 2 ^ s) (by rwa [hsh]) (by rwa [hsh])
      have hadd : Nat.add acc (Nat.shiftLeft 1 s)+(d - 2 ^ s)=acc+d:=by rw [hsh];change acc+2 ^ s+(d - 2 ^ s)=acc+d;omega
      rwa [hadd] at hrec
    · dsimp only
      exact ih rem acc d hne hlt
def fPackedSingleV3 (packed active out : Word) (directed : Bool) (code : Nat) : Bool :=
  fForce (Nat.land code 511) fun p =>
  fForce (Nat.shiftRight code 9) fun n =>
  let op:=Nat.land (Nat.shiftRight out p) 1
  let on:=Nat.land (Nat.shiftRight out n) 1
  @Bool.rec (fun _=>Bool)
    (@Bool.rec (fun _=>Bool) false
      (Nat.beq (Nat.land (Nat.xor (Nat.shiftRight packed p) (Nat.shiftRight packed n)) active) 0)
      (Nat.beq op on))
    (@Bool.rec (fun _=>Bool) false
      (Nat.beq (Nat.land (Nat.shiftRight packed p) (Nat.xor (Nat.land (Nat.shiftRight packed n) active) active)) 0)
      (Nat.ble op on))
    directed
theorem fPackedSingleV3_open {stride : Nat} {mask goal : Word} {a b op keep out : Nat}
    {state child : RowState1} {active : Word} {code : Nat}
    (hstride : 0 < stride)
    (hact : ∀ i < state.2.2.1.length,
      (keep.testBit 0=true ∨ i ≠ a) →
      (((op==2)||keep.testBit 1)=true ∨ i ≠ b) →
      active.testBit (stride*i)=true)
    (hvalid : let p:=Nat.land code 511;let n:=Nat.shiftRight code 9
      goal.testBit p=true ∧ mask.testBit n=true ∧ goal.testBit n=false ∧ p < stride ∧ n < stride)
    (masked : Masked mask goal) (viable : WordViable1 mask goal child)
    (parentNd : state.2.2.1.Nodup)
    (eval : dagDirectChild1 mask state a b op keep (state.2.2.1.getD a 0) (state.2.2.1.getD b 0) out=some child) :
    fPackedSingleV3 (fPackWords stride state.2.2.1) active out (Nat.beq child.2.1 0) code=false:=by
  obtain ⟨fuel,nots,ws,history⟩:=state
  let x:=ws.getD a 0
  let y:=ws.getD b 0
  let bad : Bool:=fuel==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b)
  let stale : Bool:=out==0||out==mask||ws.contains out
  let bank:=dagKept1 ws op keep x y
  let nextNots:=if op==2 then nots - 1 else nots
  change (if bad then none else if stale then none else
    some (fuel - 1,nextNots,insertWord out bank,(out,x,y) :: history))=some child at eval
  by_cases hbad : bad=true
  · simp [hbad] at eval
  by_cases hst : stale=true
  · simp [hbad,hst] at eval
  have heq : (fuel - 1,nextNots,insertWord out bank,(out,x,y) :: history)=child:=by
    simpa [hbad,hst] using eval
  subst child
  obtain ⟨nd,k,_,live⟩:=viable
  change LiveWord mask goal k nextNots (insertWord out bank).toFinset at live
  have hsame : (out :: bank).toFinset=(insertWord out bank).toFinset:=by
    ext w;simp only [List.mem_toFinset,List.mem_cons,insertWordMem]
  have live' : LiveWord mask goal k nextNots (out :: bank).toFinset:=by rwa [hsame]
  obtain ⟨hp,mn,hneg,wp,wn⟩:=hvalid
  let p:=Nat.land code 511
  let n:=Nat.shiftRight code 9
  let kp0:=keep.testBit 0
  let kp1:=(op==2)||keep.testBit 1
  apply Bool.eq_false_iff.mpr
  intro closed
  unfold fPackedSingleV3 at closed
  rw [fForce_eq,fForce_eq] at closed
  have hbitEq : ∀ (w j : Nat),Nat.land (Nat.shiftRight w j) 1=if w.testBit j then 1 else 0:=by
    intro w j
    have htb : fTestBit w j=w.testBit j:=fTestBit_eq w j
    unfold fTestBit at htb
    rw [fBnot_eq] at htb
    have hle : Nat.land (Nat.shiftRight w j) 1 < 2:=by
      change (w>>>j)&&&1 < 2
      have h1 : (w>>>j)&&&(2 ^ 1 - 1)=(w>>>j) % 2 ^ 1:=Nat.and_two_pow_sub_one_eq_mod (w>>>j) 1
      change (w>>>j)&&&(2 ^ 1 - 1) < 2 ^ 1
      rw [h1];exact Nat.mod_lt _ (by decide)
    cases h : w.testBit j
    · rw [h] at htb
      have h0 : Nat.beq (Nat.land (Nat.shiftRight w j) 1) 0=true:=by
        cases hq : Nat.beq (Nat.land (Nat.shiftRight w j) 1) 0;rw [hq] at htb;exact Bool.noConfusion htb;rfl
      change Nat.land (Nat.shiftRight w j) 1=0
      exact Nat.beq_eq.mp h0
    · rw [h] at htb
      have hne0 : Nat.land (Nat.shiftRight w j) 1 ≠ 0:=fun h0=>by
        rw [h0] at htb;exact Bool.noConfusion htb
      change Nat.land (Nat.shiftRight w j) 1=1
      omega
  have hbank : ∀ w ∈ out :: bank,
      (if Nat.beq nextNots 0 then !w.testBit p||w.testBit n else w.testBit p==w.testBit n)=true:=by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | later
    · cases hdir : Nat.beq nextNots 0
      · rw [hdir] at closed;dsimp only at closed
        cases hok : Nat.beq (Nat.land (Nat.shiftRight w p) 1) (Nat.land (Nat.shiftRight w n) 1)
        · rw [hok] at closed;exact Bool.noConfusion closed
        · have he:=Nat.beq_eq.mp hok
          rw [hbitEq w p,hbitEq w n] at he
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases h1 : w.testBit p <;> cases h2 : w.testBit n <;> simp_all
      · rw [hdir] at closed;dsimp only at closed
        cases hok : Nat.ble (Nat.land (Nat.shiftRight w p) 1) (Nat.land (Nat.shiftRight w n) 1)
        · rw [hok] at closed;exact Bool.noConfusion closed
        · have hle:=Nat.ble_eq.mp hok
          rw [hbitEq w p,hbitEq w n] at hle
          simp only [↓reduceIte]
          cases h1 : w.testBit p <;> cases h2 : w.testBit n <;> simp_all
    have rightMem:=dagKeepMem1 (keepNodup parentNd kp0 x) later
    have leftMem:=dagKeepMem1 parentNd rightMem.1
    obtain ⟨i,inside,eq⟩:=List.mem_iff_getElem.mp leftMem.1
    have atIndex : ws.getD i 0=w:=by
      simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside] using eq
    have hia : kp0=true ∨ i ≠ a:=by
      rcases leftMem.2 with h | h;exact Or.inl h;exact Or.inr (fun heq=>h (heq ▸ atIndex).symm)
    have hib : kp1=true ∨ i ≠ b:=by
      rcases rightMem.2 with h | h;exact Or.inl h;exact Or.inr (fun heq=>h (heq ▸ atIndex).symm)
    have hactI : active.testBit (stride*i)=true:=hact i inside hia hib
    have test {j : Nat} (within : j < stride) :
        (Nat.shiftRight (fPackWords stride ws) j).testBit (stride*i)=w.testBit j:=by
      rw [show (Nat.shiftRight (fPackWords stride ws) j).testBit (stride*i) =
            (fPackWords stride ws).testBit (j+stride*i) from Nat.testBit_shiftRight ..,
        Nat.add_comm j,fPackBits inside within,atIndex]
    have pt:=test (j:=p) wp
    have nt:=test (j:=n) wn
    cases hdir : Nat.beq nextNots 0
    · rw [hdir] at closed;dsimp only at closed
      cases hok : Nat.beq (Nat.land (Nat.shiftRight out p) 1) (Nat.land (Nat.shiftRight out n) 1)
      · rw [hok] at closed;exact Bool.noConfusion closed
      · rw [hok] at closed;dsimp only at closed
        have hzero:=Nat.beq_eq.mp closed
        have hbit:=congrArg (fun word=>Nat.testBit word (stride*i)) hzero
        rw [PackedRect.tb_land,PackedRect.tb_xor,pt,nt,hactI,Nat.zero_testBit] at hbit
        change (w.testBit (code&&&511)==w.testBit (code>>>9))=true
        change (Bool.xor (w.testBit (code&&&511)) (w.testBit (code>>>9))&&true)=false at hbit
        revert hbit
        cases w.testBit (code&&&511) <;> cases w.testBit (code>>>9) <;> decide
    · rw [hdir] at closed;dsimp only at closed
      cases hok : Nat.ble (Nat.land (Nat.shiftRight out p) 1) (Nat.land (Nat.shiftRight out n) 1)
      · rw [hok] at closed;exact Bool.noConfusion closed
      · rw [hok] at closed;dsimp only at closed
        have hzero:=Nat.beq_eq.mp closed
        have hbit:=congrArg (fun word=>Nat.testBit word (stride*i)) hzero
        rw [PackedRect.tb_land,PackedRect.tb_xor,PackedRect.tb_land,pt,nt,hactI,Nat.zero_testBit] at hbit
        change (!w.testBit (code&&&511)||w.testBit (code>>>9))=true
        change (w.testBit (code&&&511)&&Bool.xor (w.testBit (code>>>9)&&true) true)=false at hbit
        revert hbit
        cases w.testBit (code&&&511) <;> cases w.testBit (code>>>9) <;> decide
  cases hdir : Nat.beq nextNots 0
  · have h:=liveAgrees live' ((positiveInMask masked hp).trans mn.symm) (fun w hw=>by
      have hb:=hbank w (List.mem_toFinset.mp hw)
      simp only [hdir,Bool.false_eq_true, ↓reduceIte,beq_iff_eq] at hb
      exact hb)
    change goal.testBit (code.land 511)=goal.testBit (code.shiftRight 9) at h
    rw [hp,hneg] at h
    exact Bool.noConfusion h
  · have ht0 : nextNots=0:=Nat.beq_eq.mp hdir
    rw [ht0] at live'
    obtain ⟨w,hw,on,off⟩:=liveDirected live' hp hneg
    have hb:=hbank w (List.mem_toFinset.mp hw)
    dsimp only [p,n] at hb on off
    simp only [hdir, ↓reduceIte,on,off] at hb
    exact Bool.noConfusion hb
noncomputable def fPackedSingleV3Term :
    {f : Word → Word → Word → Bool → Nat → Bool // f=fPackedSingleV3}:=by
  refine ⟨?f, ?proof⟩
  case proof =>
    delta fPackedSingleV3
    beta_reduce
    exact rfl
noncomputable def fPackedSingleV3Run:=fPackedSingleV3Term.1
def fTreeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
 (Nat.rec (motive:=fun _=>Nat → Bool) (fun _=>true)
 (fun _ next i=>fBand (check i) (next (Nat.add i 1))) count) start
theorem fTreeBlock_eq (start count : Nat) (check : Nat → Bool) :
    fTreeBlock start count check=treeBlock start count check:=by
  induction count generalizing start with
  | zero=>rfl
  | succ c ih =>
    change fBand (check start) (fTreeBlock (Nat.add start 1) c check)=(check start&&treeBlock (start+1) c check)
    rw [fBand_eq,ih]
noncomputable def fDagRefSlow (lightStates : Nat → Option LightState1) (moves : DagMovesFn1)
 (lnk : DagLink1) (state : RowState1) : Bool :=
 @Option.rec LightState1 (fun _=>Bool) false
 (fun saved =>
 fBand (Nat.beq saved.1 state.1)
 (fBand (Nat.beq saved.2.1 state.2.1)
 (@Bool.rec (fun _=>Bool)
 (@Option.rec WordMove (fun _=>Bool) false
 (fun m=>fListEq saved.2.2 (fDagMoveWordsRun m state.2.2.1))
 (moves lnk.2))
 (fListEq saved.2.2 state.2.2.1)
 (Nat.beq lnk.2 0))))
 (lightStates lnk.1)
noncomputable def fCheckKeep (maxK steps : Nat) (is24 : Bool) (mask goal : Word)
    (chart : Option RowChart) (cut : CutCheck1)
    (count : Nat) (forest : Forest) (lightStates : Nat → Option LightState1) (moves : DagMovesFn1)
    (parent : Nat) (bucket : DagBucket1)
    (sample : DagSample1) (packed active : Word)
    (cf nextNots : Nat) (directed : Bool) (ws : List Word) (history : List (Word × Word × Word))
    (x y out full cout rest tok : Word) (kp0 kp1 : Bool) : Bool :=
  fForce (Nat.xor full (Nat.land (Nat.lor rest cout) full)) fun missing =>
    let fallback:=fun _ : Unit =>
      @Option.rec DagLink1 (fun _=>Bool)
        (fForceWords (fInsert out (fKeepWord kp1 y (fKeepWord kp0 x ws))) fun cws =>
          fDagLocal maxK is24 mask goal chart cut (cf,nextNots,cws,(out,x,y) :: history))
        (fun lnk =>
          @Bool.rec (fun _=>Bool)
            (fForceWords (fInsert out (fKeepWord kp1 y (fKeepWord kp0 x ws))) fun cws =>
              let child : RowState1:=(cf,nextNots,cws,(out,x,y) :: history)
              fBor (fBand (Nat.blt lnk.1 count) (fDagRefSlow lightStates moves lnk child))
                (fDagLocal maxK is24 mask goal chart cut child))
            true
            (fBand (Nat.blt lnk.1 count)
              (fBand (Nat.beq lnk.2 0)
                (let pt:=forest lnk.1
                 fBand (Nat.beq pt.1 parent) (Nat.beq pt.2 tok)))))
        (bucket tok)
    @Bool.rec (fun _=>Bool)
      (fForce (fUnpack sample.1 18 (fHighest steps missing)) fun code =>
        @Bool.rec (fun _=>Bool) (fallback ()) true
          (fPackedSingleV3Run packed active out directed code))
      (fallback ())
      (Nat.beq missing 0)
noncomputable def fCheckKeepTerm :
    {f : Nat → Nat → Bool → Word → Word → Option RowChart → CutCheck1 →
      Nat → Forest → (Nat → Option LightState1) → DagMovesFn1 → Nat → DagBucket1 →
      DagSample1 → Word → Word → Nat → Nat → Bool → List Word → List (Word × Word × Word) →
      Word → Word → Word → Word → Word → Word → Word → Bool → Bool → Bool // f=fCheckKeep}:=by
  refine ⟨?f, ?proof⟩
  case proof =>
    delta fCheckKeep fDagRefSlow fListEq fKeepWord fInsert fErase fUnpack fHighest
      fDagLocal fKwSafeCheck fListLen fContains fBand fBor fBnot
    beta_reduce
    exact rfl
noncomputable def fCheckKeepRun:=fCheckKeepTerm.1
noncomputable def fDagCheckChildren (maxK stride steps : Nat) (is24 : Bool) (mask goal : Word)
    (chart : Option RowChart) (cut : CutCheck1)
    (count : Nat) (forest : Forest) (lightStates : Nat → Option LightState1) (moves : DagMovesFn1)
    (parent : Nat) (bucket : DagBucket1)
    (state : RowState1) (sample : DagSample1) (tags : List DagSignals1) : Bool :=
  let (fuel,nots,ws,history):=state
  fForce (fListLen ws) fun n =>
  fBand (Nat.ble n 64)
  (fBand (fBnot (fBand (Nat.beq nots 0) (fContains goal ws)))
  (fForce (fPackWords stride ws) fun packed =>
  fForce (fLaneMarks stride n) fun marks =>
  dagForceCache1 tags fun tags =>
  fForce (Nat.sub (Nat.shiftLeft 1 sample.2) 1) fun full =>
  fCountSigns false full tags fun normal =>
  fCountSigns true full tags fun tight =>
  fForce (Nat.sub fuel 1) fun cf =>
  let dirSame:=Nat.beq nots 0
  let countsSame := @Bool.rec (fun _=>DagCounts1) normal tight dirSame
  let cS1:=countsSame.1
  let cS2:=countsSame.2.1
  let cS3:=countsSame.2.2
  let canK0Same:=Nat.ble (Nat.add (Nat.sub n 1) nots) fuel
  let canK1Same:=Nat.ble (Nat.add n nots) fuel
  let canK2Same:=Nat.ble (Nat.add (Nat.add n 1) nots) fuel
  let nots1:=Nat.sub nots 1
  let dirNot:=Nat.beq nots1 0
  let countsNot := @Bool.rec (fun _=>DagCounts1) normal tight dirNot
  let canK0Not:=Nat.ble (Nat.add n nots1) fuel
  let canK1Not:=Nat.ble (Nat.add (Nat.add n 1) nots1) fuel
  fTreeBlock 0 n fun a =>
    fForce (fGetD ws a) fun x =>
    @Prod.rec Word Word (fun _=>Bool) (fun xs1 xs2 =>
      fForce (Nat.xor marks (Nat.shiftLeft 1 (Nat.mul stride a))) fun actNoA =>
      let doUnary :=
        @Bool.rec (fun _=>Bool)
          (fForce (Nat.xor mask x) fun out =>
            @Bool.rec (fun _=>Bool)
              (fForce (fSignalContrast dirNot full (xs1,xs2)) fun cxN =>
               fForce (fSignalContrast dirNot full (Nat.xor full xs1,Nat.xor full xs2)) fun coutN =>
               fForce (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) a) 3) 2) 4) fun baseTok =>
               let r0:=Nat.lor countsNot.2.1 (Nat.xor countsNot.1 (Nat.land countsNot.1 cxN))
               let r1:=countsNot.1
               fBand
                 (@Bool.rec (fun _=>Bool) true
                   (fCheckKeepRun maxK steps is24 mask goal chart cut count forest lightStates moves parent bucket
                     sample packed actNoA cf nots1 dirNot ws history x x out full coutN r0 baseTok false true)
                   canK0Not)
                 (@Bool.rec (fun _=>Bool) true
                   (fCheckKeepRun maxK steps is24 mask goal chart cut count forest lightStates moves parent bucket
                     sample packed marks cf nots1 dirNot ws history x x out full coutN r1 (Nat.add baseTok 1) true true)
                   canK1Not))
              true
              (fBor (Nat.beq out 0) (fBor (Nat.beq out mask) (fContains out ws))))
          true
          dirSame
      fForce (fSignalContrast dirSame full (xs1,xs2)) fun cxS =>
      fBand doUnary
        (fTreeBlock (Nat.add a 1) (Nat.sub n (Nat.add a 1)) fun b =>
          fForce (fGetD ws b) fun y =>
          @Prod.rec Word Word (fun _=>Bool) (fun ys1 ys2 =>
            fForce (Nat.shiftLeft 1 (Nat.mul stride b)) fun omB =>
            fForce (Nat.xor marks omB) fun actNoB =>
            fForce (Nat.xor actNoA omB) fun actNoAB =>
            fForce (fSignalContrast dirSame full (ys1,ys2)) fun cyS =>
            fForce (Nat.mul (Nat.add (Nat.mul a 64) b) 3) fun baseAB =>
            fForce (Nat.lor cS3 (Nat.lor (Nat.xor cS2 (Nat.land (Nat.land cS2 cxS) cyS)) (Nat.xor cS1 (Nat.land cS1 (Nat.lor cxS cyS))))) fun r0 =>
            fForce (Nat.lor cS2 (Nat.xor cS1 (Nat.land cS1 cyS))) fun r1 =>
            fForce (Nat.lor cS2 (Nat.xor cS1 (Nat.land cS1 cxS))) fun r2 =>
            let doBin:=fun op out up dn =>
              fForce out fun out =>
                @Bool.rec (fun _=>Bool)
                  (fForce (fSignalContrast dirSame full (up,dn)) fun coutS =>
                   fForce (Nat.mul (Nat.add baseAB op) 4) fun baseTok =>
                   fBand
                     (@Bool.rec (fun _=>Bool) true
                       (fCheckKeepRun maxK steps is24 mask goal chart cut count forest lightStates moves parent bucket
                         sample packed actNoAB cf nots dirSame ws history x y out full coutS r0 baseTok false false)
                       canK0Same)
                     (fBand
                       (@Bool.rec (fun _=>Bool) true
                         (fCheckKeepRun maxK steps is24 mask goal chart cut count forest lightStates moves parent bucket
                           sample packed actNoB cf nots dirSame ws history x y out full coutS r1 (Nat.add baseTok 1) true false)
                         canK1Same)
                       (fBand
                         (@Bool.rec (fun _=>Bool) true
                           (fCheckKeepRun maxK steps is24 mask goal chart cut count forest lightStates moves parent bucket
                             sample packed actNoA cf nots dirSame ws history x y out full coutS r2 (Nat.add baseTok 2) false true)
                           canK1Same)
                         (@Bool.rec (fun _=>Bool) true
                           (fCheckKeepRun maxK steps is24 mask goal chart cut count forest lightStates moves parent bucket
                             sample packed marks cf nots dirSame ws history x y out full coutS cS1 (Nat.add baseTok 3) true true)
                           canK2Same))))
                  true
                  (fBor (Nat.beq out 0) (fBor (Nat.beq out mask) (fContains out ws)))
            fBand (doBin 0 (Nat.land x y) (Nat.land xs1 ys1) (Nat.land xs2 ys2))
              (doBin 1 (Nat.lor x y) (Nat.lor xs1 ys1) (Nat.lor xs2 ys2)))
          (fGetDTags tags b)))
    (fGetDTags tags a)))
theorem fCheckKeep_extract {maxK stride steps : Nat} {is24 : Bool} {mask goal : Word}
    {chart : Option RowChart} {cut : CutCheck1}
    {count : Nat} {forest : Forest} {lightStates : Nat → Option LightState1} {moves : DagMovesFn1}
    {parent : Nat} {bucket : DagBucket1}
    {sample : DagSample1} {a b op keep : Nat} {state child : RowState1}
    {active cout rest : Word} {kp0 kp1 : Bool}
    (hstride : 0 < stride)
    (hsamp : SampleValid stride mask goal sample)
    (hact : ∀ i < state.2.2.1.length,
      (kp0=true ∨ i ≠ a) → (kp1=true ∨ i ≠ b) → active.testBit (stride*i)=true)
    (hkp0 : kp0=keep.testBit 0)
    (hkp1 : kp1=((op==2)||keep.testBit 1))
    (hb : b < 64) (hop : op < 3) (hk : keep < 4)
    (eval : childState1 mask (gateToken a b op keep) state=some child)
    (masked : Masked mask goal) (viable : WordViable1 mask goal child) (nd : state.2.2.1.Nodup)
    (openChild : fDagLocal maxK is24 mask goal chart cut child=false)
    (hcheck : fCheckKeepRun maxK steps is24 mask goal chart cut count forest lightStates moves parent bucket
      sample (fPackWords stride state.2.2.1) active
      (Nat.sub state.1 1) (if op==2 then Nat.sub state.2.1 1 else state.2.1)
      (Nat.beq (if op==2 then Nat.sub state.2.1 1 else state.2.1) 0)
      state.2.2.1 state.2.2.2 (state.2.2.1.getD a 0) (state.2.2.1.getD b 0)
      (dagGateWord1 mask op (state.2.2.1.getD a 0) (state.2.2.1.getD b 0))
      (Nat.sub (Nat.shiftLeft 1 sample.2) 1) cout rest
      (gateToken a b op keep) kp0 kp1=true) :
    fDagRefRun count forest lightStates moves parent bucket (gateToken a b op keep) child=true:=by
  obtain ⟨fuel,nots,ws,history⟩:=state
  have direct:=(dagDirectChild1Eq (mask:=mask) (state:=(fuel,nots,ws,history)) hb hop hk).trans eval
  obtain ⟨hc2,_⟩:=dagDirectChild1Nots direct
  have hce : child=(Nat.sub fuel 1,if op==2 then Nat.sub nots 1 else nots,
      fInsert (dagGateWord1 mask op (ws.getD a 0) (ws.getD b 0))
        (fKeepWord kp1 (ws.getD b 0) (fKeepWord kp0 (ws.getD a 0) ws)),
      (dagGateWord1 mask op (ws.getD a 0) (ws.getD b 0),ws.getD a 0,ws.getD b 0) :: history):=by
    let x:=ws.getD a 0;let y:=ws.getD b 0;let out:=dagGateWord1 mask op x y
    let bad : Bool:=fuel==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b)
    let stale : Bool:=out==0||out==mask||ws.contains out
    change (if bad then none else if stale then none else
      some (fuel - 1,if op==2 then nots - 1 else nots,insertWord out (dagKept1 ws op keep x y),(out,x,y) :: history))=some child at direct
    by_cases h1 : bad=true;simp [h1] at direct
    by_cases h2 : stale=true;simp [h1,h2] at direct
    have heq : (fuel - 1,if op==2 then nots - 1 else nots,insertWord out (dagKept1 ws op keep x y),(out,x,y) :: history)=child:=by
      simpa [h1,h2] using direct
    rw [← heq,fInsert_eq,fKeepWord_eq,fKeepWord_eq,hkp0,hkp1];rfl
  have hfb : @Option.rec DagLink1 (fun _=>Bool)
      (fForceWords (fInsert (dagGateWord1 mask op (ws.getD a 0) (ws.getD b 0))
        (fKeepWord kp1 (ws.getD b 0) (fKeepWord kp0 (ws.getD a 0) ws))) fun cws =>
        fDagLocal maxK is24 mask goal chart cut
          (Nat.sub fuel 1,if op==2 then Nat.sub nots 1 else nots,cws,
            (dagGateWord1 mask op (ws.getD a 0) (ws.getD b 0),ws.getD a 0,ws.getD b 0) :: history))
      (fun lnk =>
        @Bool.rec (fun _=>Bool)
          (fForceWords (fInsert (dagGateWord1 mask op (ws.getD a 0) (ws.getD b 0))
            (fKeepWord kp1 (ws.getD b 0) (fKeepWord kp0 (ws.getD a 0) ws))) fun cws =>
            let ch : RowState1:=(Nat.sub fuel 1,if op==2 then Nat.sub nots 1 else nots,cws,
              (dagGateWord1 mask op (ws.getD a 0) (ws.getD b 0),ws.getD a 0,ws.getD b 0) :: history)
            fBor (fBand (Nat.blt lnk.1 count) (fDagRefSlow lightStates moves lnk ch))
              (fDagLocal maxK is24 mask goal chart cut ch))
          true
          (fBand (Nat.blt lnk.1 count)
            (fBand (Nat.beq lnk.2 0)
              (let pt:=forest lnk.1
               fBand (Nat.beq pt.1 parent) (Nat.beq pt.2 (gateToken a b op keep))))))
      (bucket (gateToken a b op keep))=true →
      fDagRefRun count forest lightStates moves parent bucket (gateToken a b op keep) child=true:=by
    intro h
    rw [show fDagRefRun=fDagRefTree from fDagRefTreeTerm.2]
    unfold fDagRefTree
    cases hbk : bucket (gateToken a b op keep) with
    | none =>
      rw [hbk] at h;dsimp only at h
      rw [fForceWords_eq, ← hce,openChild] at h
      exact Bool.noConfusion h
    | some lnk =>
      rw [hbk] at h;dsimp only at h ⊢
      rw [fBand_eq,fBor_eq,Bool.and_eq_true,Bool.or_eq_true]
      cases htr : fBand (Nat.blt lnk.1 count) (fBand (Nat.beq lnk.2 0)
          (fBand (Nat.beq (forest lnk.1).1 parent) (Nat.beq (forest lnk.1).2 (gateToken a b op keep))))
      · rw [htr] at h;dsimp only at h
        rw [fForceWords_eq,fBor_eq,fBand_eq, ← hce,openChild,Bool.or_false,Bool.and_eq_true] at h
        exact ⟨h.1,Or.inr h.2⟩
      · simp only [fBand_eq,Bool.and_eq_true] at htr
        refine ⟨htr.1,Or.inl ?_⟩
        simp only [fBand_eq,Bool.and_eq_true]
        exact htr.2
  rw [show fCheckKeepRun=fCheckKeep from fCheckKeepTerm.2] at hcheck
  unfold fCheckKeep at hcheck
  rw [fForce_eq] at hcheck
  let miss:=Nat.xor (Nat.sub (Nat.shiftLeft 1 sample.2) 1)
    (Nat.land (Nat.lor rest cout) (Nat.sub (Nat.shiftLeft 1 sample.2) 1))
  cases hm : Nat.beq miss 0
  · rw [hm] at hcheck;dsimp only at hcheck
    have hnz : miss ≠ 0:=fun h0=>by rw [h0] at hm;exact Bool.noConfusion hm
    have hlt : miss < 2 ^ sample.2:=xor_land_full_lt sample.2 (Nat.lor rest cout)
    have hidx : fHighest steps miss < sample.2:=fHighest_lt hnz hlt
    have hv:=hsamp (fHighest steps miss) hidx
    rw [← fUnpack_eq] at hv
    have hsingle : fPackedSingleV3Run (fPackWords stride ws) active
        (dagGateWord1 mask op (ws.getD a 0) (ws.getD b 0))
        (Nat.beq (if op==2 then Nat.sub nots 1 else nots) 0)
        (fUnpack sample.1 18 (fHighest steps miss))=false:=by
      rw [show fPackedSingleV3Run=fPackedSingleV3 from fPackedSingleV3Term.2]
      have hact' : ∀ i < (fuel,nots,ws,history).2.2.1.length,
          (keep.testBit 0=true ∨ i ≠ a) →
          (((op==2)||keep.testBit 1)=true ∨ i ≠ b) →
          active.testBit (stride*i)=true:=by
        intro i hi h1 h2;exact hact i hi (hkp0 ▸ h1) (hkp1 ▸ h2)
      have h:=fPackedSingleV3_open hstride hact' hv masked viable nd direct
      have hcn : child.2.1=(if op==2 then Nat.sub nots 1 else nots):=hc2
      rw [hcn] at h;exact h
    rw [fForce_eq,hsingle] at hcheck
    dsimp only at hcheck
    exact hfb hcheck
  · rw [hm] at hcheck;dsimp only at hcheck
    exact hfb hcheck
theorem fActBit_xor {stride length j i : Nat} (hstride : 0 < stride) (hi : i < length) (hne : i ≠ j) :
    (Nat.xor (fLaneMarks stride length) (Nat.shiftLeft 1 (Nat.mul stride j))).testBit (stride*i)=true:=by
  rw [PackedRect.tb_xor,fMarkBits hi]
  have hmul : stride*j ≠ stride*i:=fun hm=>hne ((Nat.mul_left_cancel hstride hm).symm)
  have h0 : (Nat.shiftLeft 1 (Nat.mul stride j)).testBit (stride*i)=false:=by
    change (1<<<(stride*j)).testBit (stride*i)=false
    rw [Nat.shiftLeft_eq,Nat.one_mul,Nat.testBit_two_pow];simp [hmul]
  rw [h0];rfl
theorem fActBit_xor2 {stride length a b i : Nat} (hstride : 0 < stride) (hi : i < length) (ha : i ≠ a) (hb : i ≠ b) :
    (Nat.xor (Nat.xor (fLaneMarks stride length) (Nat.shiftLeft 1 (Nat.mul stride a))) (Nat.shiftLeft 1 (Nat.mul stride b))).testBit (stride*i)=true:=by
  rw [PackedRect.tb_xor,fActBit_xor hstride hi ha]
  have hmul : stride*b ≠ stride*i:=fun hm=>hb ((Nat.mul_left_cancel hstride hm).symm)
  have h0 : (Nat.shiftLeft 1 (Nat.mul stride b)).testBit (stride*i)=false:=by
    change (1<<<(stride*b)).testBit (stride*i)=false
    rw [Nat.shiftLeft_eq,Nat.one_mul,Nat.testBit_two_pow];simp [hmul]
  rw [h0];rfl
theorem fDagChildAt {maxK stride steps : Nat} {is24 : Bool} {mask goal : Word} {chart : Option RowChart}
    {cut : CutCheck1} {count : Nat} {forest : Forest} {lightStates : Nat → Option LightState1}
    {moves : DagMovesFn1} {parent : Nat} {bucket : DagBucket1}
    {state child : RowState1} {sample : DagSample1} {tags : List DagSignals1} {a b op keep : Nat}
    (hstride : 0 < stride)
    (hsamp : SampleValid stride mask goal sample)
    (checked : fDagCheckChildren maxK stride steps is24 mask goal chart cut count forest lightStates moves parent bucket state sample tags=true)
    (ha : a < state.2.2.1.length)
    (legal : (a=b ∧ op=2 ∧ keep < 2 ∧ state.2.1 ≠ 0) ∨
      (a < b ∧ b < state.2.2.1.length ∧ op < 2 ∧ keep < 4))
    (eval : childState1 mask (gateToken a b op keep) state=some child)
    (masked : Masked mask goal) (viable : WordViable1 mask goal child) (nd : state.2.2.1.Nodup)
    (openChild : fDagLocal maxK is24 mask goal chart cut child=false) :
    fDagRefRun count forest lightStates moves parent bucket (gateToken a b op keep) child=true:=by
  obtain ⟨fuel,nots,ws,history⟩:=state
  change a < ws.length at ha
  unfold fDagCheckChildren at checked
  simp only [fForce_eq,dagForceCache1Eq,fCountSigns_eq,fBand_eq,fBnot_eq,
    fListLen_eq,fContains_eq,fTreeBlock_eq,Bool.and_eq_true] at checked
  obtain ⟨hwidthB,_,hloop⟩:=checked
  have width : ws.length ≤ 64:=Nat.ble_eq.mp hwidthB
  have atA:=treeBlock_at hloop (i:=a) (Nat.zero_le _) (by simpa using ha)
  simp only [fForce_eq,fBand_eq,fGetD_eq,fTreeBlock_eq,Bool.and_eq_true] at atA
  obtain ⟨unary,binary⟩:=atA
  have hchildFit : ∀ (hop : op < 3) (hb : b < 64) (hk : keep < 4),
      dagSizeFloor1 ws.length op keep+(if op==2 then nots - 1 else nots) ≤ fuel:=by
    intro hop hb hk
    have hdir:=(dagDirectChild1Eq (mask:=mask) (state:=(fuel,nots,ws,history)) hb hop hk).trans eval
    let x:=ws.getD a 0;let y:=ws.getD b 0;let out:=dagGateWord1 mask op x y
    let bad : Bool:=fuel==0||b ≥ ws.length||(if op==2 then a != b||keep ≥ 2||nots==0 else a ≥ b)
    let stale : Bool:=out==0||out==mask||ws.contains out
    change (if bad then none else if stale then none else
      some (fuel - 1,if op==2 then nots - 1 else nots,insertWord out (dagKept1 ws op keep x y),(out,x,y) :: history))=some child at hdir
    by_cases h1 : bad=true;simp [h1] at hdir
    by_cases h2 : stale=true;simp [h1,h2] at hdir
    have heq : (fuel - 1,if op==2 then nots - 1 else nots,insertWord out (dagKept1 ws op keep x y),(out,x,y) :: history)=child:=by
      simpa [h1,h2] using hdir
    have hpos : 0 < fuel:=(childState1_fuel eval).1
    have hins : (insertWord out (dagKept1 ws op keep x y)).length=(dagKept1 ws op keep x y).length+1:=by
      generalize dagKept1 ws op keep x y=l
      induction l with
      | nil=>rfl
      | cons u us ih=>change (if out ≤ u then out :: u :: us else u :: insertWord out us).length=_;split <;> simp [ih]
    have hkl : ∀ (kp : Bool) (u : Word) (l : List Word),l.length - (if kp then 0 else 1) ≤ (keepWord kp u l).length:=by
      intro kp u l;cases kp;exact List.le_length_erase;simp [keepWord]
    have h1l:=hkl (keep.testBit 0) x ws
    have h2l:=hkl (op==2||keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    rw [← heq] at openChild
    unfold fDagLocal at openChild
    simp only [fBor_eq,fListLen_eq,Bool.or_eq_false_iff] at openChild
    have hnf : ¬ (fuel - 1+1 < (insertWord out (dagKept1 ws op keep x y)).length+(if op==2 then nots - 1 else nots)):=by
      intro hlt
      have hb' : Nat.blt (Nat.add (fuel - 1) 1) (Nat.add (insertWord out (dagKept1 ws op keep x y)).length (if op==2 then nots - 1 else nots))=true :=
        Nat.blt_eq.mpr hlt
      rw [hb'] at openChild;exact Bool.noConfusion openChild.1
    unfold dagSizeFloor1
    dsimp only [dagKept1] at hins hnf
    omega
  rcases legal with ⟨rfl,rfl,hk,hn⟩ | ⟨ab,hb,hop,hk⟩
  · have hnf : Nat.beq nots 0=false:=by cases nots;exact absurd rfl hn;rfl
    rw [hnf] at unary;dsimp only at unary
    have fields:=dagDirectChild1Eq (mask:=mask) (state:=(fuel,nots,ws,history)) (a:=a) (b:=a) (op:=2) (keep:=keep) (by omega) (by decide) (by omega)
    have direct:=fields.trans eval
    obtain ⟨_,hfresh⟩:=dagDirectChild1Nots direct
    have hstF : fBor (Nat.beq (Nat.xor mask (ws.getD a 0)) 0)
        (fBor (Nat.beq (Nat.xor mask (ws.getD a 0)) mask) (ws.contains (Nat.xor mask (ws.getD a 0))))=false:=by
      simp only [fBor_eq,fNatBeq_iff_beq]
      simpa [dagGateWord1,Bool.or_assoc] using hfresh
    rw [hstF] at unary;dsimp only at unary
    simp only [fForce_eq,fBand_eq,Bool.and_eq_true] at unary
    obtain ⟨hu0,hu1⟩:=unary
    have hfit:=hchildFit (by decide) (by omega) (by omega)
    have hgt : dagGateWord1 mask 2 (ws.getD a 0) (ws.getD a 0)=Nat.xor mask (ws.getD a 0):=rfl
    have htok0 : Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) a) 3) 2) 4=gateToken a a 2 0:=rfl
    have htok1 : Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) a) 3) 2) 4) 1=gateToken a a 2 1:=rfl
    have heq2 : (if ((2 : Nat)==2)=true then Nat.sub nots 1 else nots)=Nat.sub nots 1:=rfl
    have hka : keep=0 ∨ keep=1:=by omega
    rcases hka with rfl | rfl
    · have hc0 : Nat.ble (Nat.add ws.length (Nat.sub nots 1)) fuel=true:=by
        apply Nat.ble_eq.mpr
        have hdf : ws.length - 1 - 0+1+(nots - 1) ≤ fuel:=hfit
        change ws.length+(nots - 1) ≤ fuel
        omega
      rw [hc0] at hu0;dsimp only at hu0
      have hact0 : ∀ i < (fuel,nots,ws,history).2.2.1.length,(false=true ∨ i ≠ a) → (true=true ∨ i ≠ a) →
          (Nat.xor (fLaneMarks stride ws.length) (Nat.shiftLeft 1 (Nat.mul stride a))).testBit (stride*i)=true:=by
        intro i hi h1 _;exact fActBit_xor hstride hi (h1.resolve_left Bool.noConfusion)
      exact fCheckKeep_extract (kp0:=false) (kp1:=true) hstride hsamp hact0 rfl rfl (by omega) (by decide) (by decide) eval masked viable nd openChild
        (by simpa only [heq2,hgt,htok0] using hu0)
    · have hc1 : Nat.ble (Nat.add (Nat.add ws.length 1) (Nat.sub nots 1)) fuel=true:=by
        apply Nat.ble_eq.mpr
        have hdf : ws.length - 0 - 0+1+(nots - 1) ≤ fuel:=hfit
        change ws.length+1+(nots - 1) ≤ fuel
        omega
      rw [hc1] at hu1;dsimp only at hu1
      have hact1 : ∀ i < (fuel,nots,ws,history).2.2.1.length,(true=true ∨ i ≠ a) → (true=true ∨ i ≠ a) →
          (fLaneMarks stride ws.length).testBit (stride*i)=true:=fun i hi _ _=>fMarkBits hi
      exact fCheckKeep_extract (kp0:=true) (kp1:=true) hstride hsamp hact1 rfl rfl (by omega) (by decide) (by decide) eval masked viable nd openChild
        (by simpa only [heq2,hgt,htok1] using hu1)
  · change b < ws.length at hb
    have hlo : Nat.add a 1 ≤ b:=by change a+1 ≤ b;omega
    have hhi : b < Nat.add a 1+Nat.sub ws.length (Nat.add a 1):=by change b < a+1+(ws.length - (a+1));omega
    have atB:=treeBlock_at binary (i:=b) hlo hhi
    simp only [fForce_eq,fGetD_eq,fBand_eq,Bool.and_eq_true] at atB
    obtain ⟨hAnd,hOr⟩:=atB
    have fields:=dagDirectChild1Eq (mask:=mask) (state:=(fuel,nots,ws,history)) (a:=a) (b:=b) (op:=op) (keep:=keep) (by omega) (by omega) hk
    have direct:=fields.trans eval
    obtain ⟨_,hfresh⟩:=dagDirectChild1Nots direct
    have hfit:=hchildFit (by omega) (by omega) hk
    have handleOp : ∀ (opv : Nat) (hopEq : op=opv) (hopLt : opv < 2)
        (coutS r0 r1 r2 r3 : Word)
        (hbr : @Bool.rec (fun _=>Bool)
          ((@Bool.rec (fun _=>Bool) true (fCheckKeepRun maxK steps is24 mask goal chart cut count forest lightStates moves parent bucket sample
            (fPackWords stride ws) (Nat.xor (Nat.xor (fLaneMarks stride ws.length) (Nat.shiftLeft 1 (Nat.mul stride a))) (Nat.shiftLeft 1 (Nat.mul stride b)))
            (Nat.sub fuel 1) nots (Nat.beq nots 0) ws history
            (ws.getD a 0) (ws.getD b 0) (dagGateWord1 mask opv (ws.getD a 0) (ws.getD b 0))
            (Nat.sub (Nat.shiftLeft 1 sample.2) 1) coutS r0 (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) b) 3) opv) 4) false false)
            (Nat.ble (Nat.add (Nat.sub ws.length 1) nots) fuel)) &&
          ((@Bool.rec (fun _=>Bool) true (fCheckKeepRun maxK steps is24 mask goal chart cut count forest lightStates moves parent bucket sample
            (fPackWords stride ws) (Nat.xor (fLaneMarks stride ws.length) (Nat.shiftLeft 1 (Nat.mul stride b)))
            (Nat.sub fuel 1) nots (Nat.beq nots 0) ws history
            (ws.getD a 0) (ws.getD b 0) (dagGateWord1 mask opv (ws.getD a 0) (ws.getD b 0))
            (Nat.sub (Nat.shiftLeft 1 sample.2) 1) coutS r1 (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) b) 3) opv) 4) 1) true false)
            (Nat.ble (Nat.add ws.length nots) fuel)) &&
          ((@Bool.rec (fun _=>Bool) true (fCheckKeepRun maxK steps is24 mask goal chart cut count forest lightStates moves parent bucket sample
            (fPackWords stride ws) (Nat.xor (fLaneMarks stride ws.length) (Nat.shiftLeft 1 (Nat.mul stride a)))
            (Nat.sub fuel 1) nots (Nat.beq nots 0) ws history
            (ws.getD a 0) (ws.getD b 0) (dagGateWord1 mask opv (ws.getD a 0) (ws.getD b 0))
            (Nat.sub (Nat.shiftLeft 1 sample.2) 1) coutS r2 (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) b) 3) opv) 4) 2) false true)
            (Nat.ble (Nat.add ws.length nots) fuel)) &&
          (@Bool.rec (fun _=>Bool) true (fCheckKeepRun maxK steps is24 mask goal chart cut count forest lightStates moves parent bucket sample
            (fPackWords stride ws) (fLaneMarks stride ws.length)
            (Nat.sub fuel 1) nots (Nat.beq nots 0) ws history
            (ws.getD a 0) (ws.getD b 0) (dagGateWord1 mask opv (ws.getD a 0) (ws.getD b 0))
            (Nat.sub (Nat.shiftLeft 1 sample.2) 1) coutS r3 (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) b) 3) opv) 4) 3) true true)
            (Nat.ble (Nat.add (Nat.add ws.length 1) nots) fuel)))))
          true
          (fBor (Nat.beq (dagGateWord1 mask opv (ws.getD a 0) (ws.getD b 0)) 0)
            (fBor (Nat.beq (dagGateWord1 mask opv (ws.getD a 0) (ws.getD b 0)) mask)
              (ws.contains (dagGateWord1 mask opv (ws.getD a 0) (ws.getD b 0)))))=true),
        fDagRefRun count forest lightStates moves parent bucket (gateToken a b op keep) child=true:=by
      intro opv hopEq hopLt coutS r0 r1 r2 r3 hbr
      subst op
      have hstF : fBor (Nat.beq (dagGateWord1 mask opv (ws.getD a 0) (ws.getD b 0)) 0)
          (fBor (Nat.beq (dagGateWord1 mask opv (ws.getD a 0) (ws.getD b 0)) mask)
            (ws.contains (dagGateWord1 mask opv (ws.getD a 0) (ws.getD b 0))))=false:=by
        simp only [fBor_eq,fNatBeq_iff_beq]
        simpa [Bool.or_assoc] using hfresh
      rw [hstF] at hbr;dsimp only at hbr
      simp only [Bool.and_eq_true] at hbr
      obtain ⟨hk0,hk1,hk2,hk3⟩:=hbr
      have hne2 : (opv==2)=false:=by cases h : (opv==2);rfl;exfalso;have:=beq_iff_eq.mp h;omega
      have hne2i : (if (opv==2)=true then Nat.sub nots 1 else nots)=nots:=by rw [hne2];rfl
      have hne2i' : (if (opv==2)=true then nots - 1 else nots)=nots:=by rw [hne2];rfl
      have htok0 : Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) b) 3) opv) 4=gateToken a b opv 0:=rfl
      have htok1 : Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) b) 3) opv) 4) 1=gateToken a b opv 1:=rfl
      have htok2 : Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) b) 3) opv) 4) 2=gateToken a b opv 2:=rfl
      have htok3 : Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul a 64) b) 3) opv) 4) 3=gateToken a b opv 3:=rfl
      have hcases : keep=0 ∨ keep=1 ∨ keep=2 ∨ keep=3:=by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · have hc : Nat.ble (Nat.add (Nat.sub ws.length 1) nots) fuel=true:=by
          apply Nat.ble_eq.mpr
          have hfl : dagSizeFloor1 ws.length opv 0=ws.length - 1 - 1+1:=by unfold dagSizeFloor1;rw [hne2];rfl
          rw [hfl,hne2i'] at hfit
          change ws.length - 1+nots ≤ fuel;omega
        rw [hc] at hk0;dsimp only at hk0
        have hact0 : ∀ i < (fuel,nots,ws,history).2.2.1.length,(false=true ∨ i ≠ a) → (false=true ∨ i ≠ b) →
            (Nat.xor (Nat.xor (fLaneMarks stride ws.length) (Nat.shiftLeft 1 (Nat.mul stride a))) (Nat.shiftLeft 1 (Nat.mul stride b))).testBit (stride*i)=true:=by
          intro i hi h1 h2;exact fActBit_xor2 hstride hi (h1.resolve_left Bool.noConfusion) (h2.resolve_left Bool.noConfusion)
        exact fCheckKeep_extract (kp0:=false) (kp1:=false) hstride hsamp hact0 rfl (by rw [hne2];rfl) (by omega) (by omega) (by decide) eval masked viable nd openChild
          (by simpa only [hne2i,htok0] using hk0)
      · have hc : Nat.ble (Nat.add ws.length nots) fuel=true:=by
          apply Nat.ble_eq.mpr
          have hfl : dagSizeFloor1 ws.length opv 1=ws.length - 0 - 1+1:=by unfold dagSizeFloor1;rw [hne2];rfl
          rw [hfl,hne2i'] at hfit
          change ws.length+nots ≤ fuel;omega
        rw [hc] at hk1;dsimp only at hk1
        have hact1 : ∀ i < (fuel,nots,ws,history).2.2.1.length,(true=true ∨ i ≠ a) → (false=true ∨ i ≠ b) →
            (Nat.xor (fLaneMarks stride ws.length) (Nat.shiftLeft 1 (Nat.mul stride b))).testBit (stride*i)=true:=by
          intro i hi _ h2;exact fActBit_xor hstride hi (h2.resolve_left Bool.noConfusion)
        exact fCheckKeep_extract (kp0:=true) (kp1:=false) hstride hsamp hact1 rfl (by rw [hne2];rfl) (by omega) (by omega) (by decide) eval masked viable nd openChild
          (by simpa only [hne2i,htok1] using hk1)
      · have hc : Nat.ble (Nat.add ws.length nots) fuel=true:=by
          apply Nat.ble_eq.mpr
          have hfl : dagSizeFloor1 ws.length opv 2=ws.length - 1 - 0+1:=by unfold dagSizeFloor1;rw [hne2];rfl
          rw [hfl,hne2i'] at hfit
          change ws.length+nots ≤ fuel;omega
        rw [hc] at hk2;dsimp only at hk2
        have hact2 : ∀ i < (fuel,nots,ws,history).2.2.1.length,(false=true ∨ i ≠ a) → (true=true ∨ i ≠ b) →
            (Nat.xor (fLaneMarks stride ws.length) (Nat.shiftLeft 1 (Nat.mul stride a))).testBit (stride*i)=true:=by
          intro i hi h1 _;exact fActBit_xor hstride hi (h1.resolve_left Bool.noConfusion)
        exact fCheckKeep_extract (kp0:=false) (kp1:=true) hstride hsamp hact2 rfl (by rw [hne2];rfl) (by omega) (by omega) (by decide) eval masked viable nd openChild
          (by simpa only [hne2i,htok2] using hk2)
      · have hc : Nat.ble (Nat.add (Nat.add ws.length 1) nots) fuel=true:=by
          apply Nat.ble_eq.mpr
          have hfl : dagSizeFloor1 ws.length opv 3=ws.length - 0 - 0+1:=by unfold dagSizeFloor1;rw [hne2];rfl
          rw [hfl,hne2i'] at hfit
          change ws.length+1+nots ≤ fuel;omega
        rw [hc] at hk3;dsimp only at hk3
        have hact3 : ∀ i < (fuel,nots,ws,history).2.2.1.length,(true=true ∨ i ≠ a) → (true=true ∨ i ≠ b) →
            (fLaneMarks stride ws.length).testBit (stride*i)=true:=fun i hi _ _=>fMarkBits hi
        exact fCheckKeep_extract (kp0:=true) (kp1:=true) hstride hsamp hact3 rfl (by rw [hne2];rfl) (by omega) (by omega) (by decide) eval masked viable nd openChild
          (by simpa only [hne2i,htok3] using hk3)
    have hopc : op=0 ∨ op=1:=by omega
    rcases hopc with h0 | h1
    · exact handleOp 0 h0 (by decide) _ _ _ _ _ hAnd
    · exact handleOp 1 h1 (by decide) _ _ _ _ _ hOr
noncomputable def fDagCheckChildrenTerm :
    {f : Nat → Nat → Nat → Bool → Word → Word → Option RowChart → CutCheck1 →
      Nat → Forest → (Nat → Option LightState1) → DagMovesFn1 → Nat → DagBucket1 →
      RowState1 → DagSample1 → List DagSignals1 → Bool // f=fDagCheckChildren}:=by
  refine ⟨?f, ?proof⟩
  case proof =>
    delta fDagCheckChildren fPackWords fLaneMarks fCountSigns fSignalContrast
      fContains fGetD fGetDTags fListLen fTreeBlock fBand fBor fBnot
    beta_reduce
    exact rfl
noncomputable def fDagCheckChildrenRun:=fDagCheckChildrenTerm.1
noncomputable def fDagCheckNode (maxK stride steps : Nat) (is24 : Bool) (mask goal : Word)
    (chart : Option RowChart) (cut : CutCheck1) (count : Nat) (forest : Forest)
    (states : Nat → Option RowState1) (lightStates : Nat → Option LightState1)
    (moves : DagMovesFn1) (buckets : DagBuckets1) (sample : DagSample1)
    (tags : Nat → List DagSignals1) (i : Nat) : Bool :=
  @Option.rec RowState1 (fun _=>Bool) false
    (fun st =>
      let (fuel,nots,ws,history):=st
      fForceWords ws fun forced =>
        fBand (fSortedMasked mask forced)
          (buckets (Nat.add i 1) fun bucket =>
            fDagCheckChildrenRun maxK stride steps is24 mask goal chart cut
              count forest lightStates moves (Nat.add i 1) bucket
              (fuel,nots,forced,history) sample (tags i)))
    (states i)
noncomputable def fDagCheckRoots (maxK : Nat) (is24 : Bool) (mask goal : Word) (chart : Option RowChart)
    (cut : CutCheck1) (witnesses : List Witness) (count : Nat) (forest : Forest)
    (lightStates : Nat → Option LightState1) (moves : DagMovesFn1) (buckets : DagBuckets1)
    (stock : List Word) (fuel initNots : Nat) : Bool :=
  buckets 0 fun bucket =>
    treeBlock 0 (2 ^ stock.length) fun token =>
      let state:=rootState1 stock fuel initNots token
      !dagAllowedRoot1 witnesses state.2.2.1||fDagLocal maxK is24 mask goal chart cut state ||
        fDagRefRun count forest lightStates moves 0 bucket token state
theorem fDagAllNodes {maxK stride steps : Nat} {is24 : Bool} {mask goal : Word}
    {width fuel initNots count : Nat} {stock : List Word} {chart : Option RowChart}
    {cut : CutCheck1} {forest : Forest} {moves : DagMovesFn1} {buckets : DagBuckets1}
    {sample : DagSample1} {tags : Nat → List DagSignals1}
    (hstride : 0 < stride)
    (hsamp : SampleValid stride mask goal sample)
    (is24Spec : is24=true → mask=16777215 ∧ goal=4095)
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (chartOK : ∀ c,chart=some c → ChartOK goal c)
    (cutSound : ∀ s,s.2.1 ≤ 1 → WordViable1 mask goal s → cut s=false)
    (autos : DagMovesFnOK1 mask goal width moves)
    (bvalid : BucketsValid buckets)
    (verified : treeBlock 0 count (fDagCheckNode maxK stride steps is24 mask goal chart cut count forest
      (fDagTrace mask stock fuel initNots forest) (fDagTraceLight mask stock fuel initNots forest)
      moves buckets sample tags)=true) :
    ∀ cap i saved,i < count → dagTrace1 mask stock fuel initNots forest i=some saved →
      saved.1=cap → saved.2.1 ≤ 1 → ∀ k,k ≤ cap → ¬ LiveWord mask goal k saved.2.1 saved.2.2.1.toFinset:=by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel sNots k kBound live
    rcases s with ⟨remaining,nots,words,history⟩
    let s : RowState1:=(remaining,nots,words,history)
    have checked:=treeBlock_at verified (Nat.zero_le i) (by simpa using iBound)
    change fDagCheckNode maxK stride steps is24 mask goal chart cut count forest
      (fDagTrace mask stock fuel initNots forest) (fDagTraceLight mask stock fuel initNots forest)
      moves buckets sample tags i=true at checked
    unfold fDagCheckNode at checked
    rw [fDagTrace_eq,stateEq] at checked
    dsimp only at checked
    rw [fForceWords_eq,fBand_eq,Bool.and_eq_true] at checked
    obtain ⟨nd,masked⟩:=fSortedMasked_spec checked.1
    obtain ⟨bucket,ok⟩:=bvalid (Nat.add i 1) _ checked.2
    rw [show fDagCheckChildrenRun=fDagCheckChildren from fDagCheckChildrenTerm.2] at ok
    have viable : WordViable1 mask goal s:=⟨nd,k,sFuel ▸ kBound,live⟩
    have scanned:=ok
    unfold fDagCheckChildren at scanned
    simp only [fForce_eq,fBand_eq,fBnot_eq,fListLen_eq,fContains_eq,Bool.and_eq_true] at scanned
    have hwidth : words.length ≤ 64:=Nat.ble_eq.mp scanned.1
    have habsent : !(Nat.beq nots 0&&words.contains goal)=true:=scanned.2.1
    rcases wordProgress1 hwidth viable with ⟨hn0,hit⟩ | ⟨child,possible,cv,cnle⟩
    · simp only [s] at hn0 hit
      have : (Nat.beq nots 0&&words.contains goal)=true:=by
        rw [hn0,Nat.beq_refl,List.contains_iff_mem.mpr hit];rfl
      rw [this] at habsent;exact Bool.noConfusion habsent
    obtain ⟨a,b,op,keep,ha,legal,eval⟩:=possible
    have cn1 : child.2.1 ≤ 1:=Nat.le_trans cnle sNots
    have r:=fDagChildAt hstride hsamp ok ha legal eval goalMask cv nd
      (fDagLocalOpen is24Spec goalMask chartOK cv (cutSound _ cn1 cv))
    have ⟨less,_,cm⟩:=childState1Data eval masked
    have below : child.1 < cap:=sFuel ▸ less
    obtain ⟨_,k',fits,clive⟩:=cv
    obtain ⟨j,dest,bound,restore,fuelEq,notsEq,tail⟩ :=
      fDagLinkedTree (fun d hf=>dagTrace1_treeChild stateEq eval hf) maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq (notsEq.symm ▸ cn1) k' fits tail
theorem exactLowerDagFast {maxK stride steps : Nat} {is24 allowNotInPast : Bool}
    {mask goal : Word} {width fuel initNots count : Nat}
    {stock : List Word} {chart : Option RowChart}
    {forest : Forest} {moves : DagMovesFn1} {buckets : DagBuckets1} {sample : DagSample1}
    {tags : Nat → List DagSignals1}
    {bounds : List ExactBound} {witnesses : List Witness}
    (hstride : 0 < stride)
    (hsamp : SampleValid stride mask goal sample)
    (is24Spec : is24=true → mask=16777215 ∧ goal=4095)
    (initNotsLe : initNots ≤ 1)
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (chartOK : ∀ c,chart=some c → ChartOK goal c)
    (autos : DagMovesFnOK1 mask goal width moves)
    (bvalid : BucketsValid buckets)
    (stockMasked : ∀ w ∈ stock,Masked mask w) (stockNd : stock.Nodup)
    (essential : witnesses.all (essentialB mask goal stock)=true)
    (known : ExactKnown bounds)
    (submasks : ∀ b ∈ bounds,mask&&&b.1=b.1)
    (stocksM : ∀ b ∈ bounds, ∀ w ∈ b.2.1,Masked b.1 w)
    (rootCheck : fDagCheckRoots maxK is24 mask goal chart (fExactKnownCloses allowNotInPast goal bounds) witnesses
      count forest (fDagTraceLight mask stock fuel initNots forest) moves buckets stock fuel initNots=true)
    (nodeCheck : treeBlock 0 count (fDagCheckNode maxK stride steps is24 mask goal chart
      (fExactKnownCloses allowNotInPast goal bounds) count forest
      (fDagTrace mask stock fuel initNots forest) (fDagTraceLight mask stock fuel initNots forest)
      moves buckets sample tags)=true) :
    ExactLower mask stock goal initNots (fuel+1):=by
  intro k S live hS
  by_contra! small
  have sub : ∀ w ∈ S,w ∈ stock:=by
    intro w hw;have hp:=liveWordProper live w hw
    exact ((hS w hw).resolve_left hp.1).resolve_left hp.2
  have included : S ⊆ stock.toFinset:=fun w hw=>List.mem_toFinset.mpr (sub w hw)
  obtain ⟨token,tokenBound,eq⟩:=rootToken stock S
  rw [Finset.inter_eq_right.mpr included] at eq
  let state:=rootState1 stock fuel initNots token
  have eq' : state.2.2.1.toFinset=S:=eq
  have v : WordViable1 mask goal state:=by
    refine ⟨(rootWordSublist stock token).nodup stockNd,k, ?_, ?_⟩
    · change k ≤ fuel;omega
    · rwa [eq']
  have cutOpen (s : RowState1) (hs : s.2.1 ≤ 1) (h : WordViable1 mask goal s) :
      fExactKnownCloses allowNotInPast goal bounds s=false:=by
    rw [fExactKnownCloses_eq]
    exact exactKnownClosesSound known submasks stocksM hs h
  have openRoot:=fDagLocalOpen (maxK:=maxK) is24Spec goalMask chartOK v (cutOpen _ initNotsLe v)
  have allowed : dagAllowedRoot1 witnesses state.2.2.1=true:=by
    apply List.all_eq_true.mpr;intro entry mem
    apply List.contains_iff_mem.mpr;rw [← List.mem_toFinset,eq']
    exact essentialRequired (List.all_eq_true.mp essential entry mem) sub live
  obtain ⟨bucket,rootB⟩:=bvalid 0 _ rootCheck
  have checked:=treeBlock_at rootB (Nat.zero_le token) (by simpa using tokenBound)
  change (!dagAllowedRoot1 witnesses state.2.2.1 ||
    fDagLocal maxK is24 mask goal chart (fExactKnownCloses allowNotInPast goal bounds) state ||
    fDagRefRun count forest (fDagTraceLight mask stock fuel initNots forest) moves 0 bucket token state)=true at checked
  simp only [allowed,openRoot,Bool.not_true,Bool.false_or] at checked
  have finish:=fDagAllNodes hstride hsamp is24Spec maskBounds goalMask chartOK cutOpen autos bvalid nodeCheck
  have fits : k ≤ fuel:=by omega
  have still : LiveWord mask goal k initNots state.2.2.1.toFinset:=by rwa [eq']
  have stateMask : ∀ w ∈ state.2.2.1,Masked mask w:=fun w hw =>
    stockMasked _ ((rootWordSublist stock token).subset hw)
  obtain ⟨i,s,hi,restore,cap,notsEq,plan⟩ :=
    fDagLinkedTree (fun d hf=>dagTrace1_treeRoot tokenBound hf) maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap (notsEq.symm ▸ initNotsLe) k fits plan
theorem relabelId {rows : Nat} {w : Word} (bm : Masked (fullMask rows) w) :
    relabel (id : Fin rows → Fin rows) w=w:=by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases h : i < rows
  · exact relabelBit id w ⟨i,h⟩
  · rw [relabelOutside id w i (Nat.le_of_not_gt h)]
    have eb:=congrArg (fun x : Nat=>x.testBit i) bm
    simpa [Masked,Nat.testBit_and,fullMask,Nat.testBit_two_pow_sub_one,h] using eb.symm
theorem relabelComp {rows : Nat} (s1 s2 : Fin rows → Fin rows) (w : Word) :
    relabel (s1 ∘ s2) w=relabel s2 (relabel s1 w):=by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases h : i < rows
  · change (relabel (s1 ∘ s2) w).testBit (⟨i,h⟩ : Fin rows).val =
      (relabel s2 (relabel s1 w)).testBit (⟨i,h⟩ : Fin rows).val
    rw [relabelBit,relabelBit,relabelBit];rfl
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt h),relabelOutside _ _ _ (Nat.le_of_not_gt h)]
theorem mixMove_append (m1 m2 : WordMove) (w : Word) :
    mixMove (m1 ++ m2) w=mixMove m2 (mixMove m1 w):=by
  induction m1 generalizing w with
  | nil=>rfl
  | cons s rest ih=>exact ih (mixStep s w)
def MoveAutoOK (mask goal : Word) (width : Nat) (m : WordMove) : Prop :=
 ∃ select : Fin width → Fin width,DagAuto mask goal select ∧
 ∀ w,Masked mask w → mixMove m w=relabel select w
theorem moveAutoOK_nil {width : Nat} {mask goal : Word}
    (bm : Masked (fullMask width) mask) (gm : Masked mask goal) :
    MoveAutoOK mask goal width [] :=
  ⟨id,⟨Function.surjective_id,relabelId bm,relabelId (maskedBelow bm gm)⟩,
    fun _ hw=>(relabelId (maskedBelow bm hw)).symm⟩
theorem moveAutoOK_append {width : Nat} {mask goal : Word} {m1 m2 : WordMove}
    (h1 : MoveAutoOK mask goal width m1) (h2 : MoveAutoOK mask goal width m2) :
    MoveAutoOK mask goal width (m1 ++ m2):=by
  obtain ⟨s1,a1,ag1⟩:=h1
  obtain ⟨s2,a2,ag2⟩:=h2
  refine ⟨s1 ∘ s2,⟨a1.1.comp a2.1, ?_, ?_⟩, ?_⟩
  · rw [relabelComp,a1.2.1,a2.2.1]
  · rw [relabelComp,a1.2.2,a2.2.2]
  · intro w hw
    rw [mixMove_append,ag1 w hw,ag2 _ (maskedTransfer a1.2.1 hw),relabelComp]
def fSwapBits (a b i : Nat) : Nat :=
 @Bool.rec (fun _=>Nat)
 (Nat.xor i (Nat.lor (Nat.shiftLeft 1 a) (Nat.shiftLeft 1 b)))
 i
 (Nat.beq (Nat.land (Nat.shiftRight i a) 1) (Nat.land (Nat.shiftRight i b) 1))
def fMoveAutoCheck (width : Nat) (mask goal : Word) (m : WordMove)
 (sel inv : Nat → Nat) : Bool :=
 fBand (Nat.beq (Nat.land mask (fullMask width)) mask)
 (fBand (Nat.beq (Nat.land goal mask) goal)
 (fBand (Nat.beq (fMixMove m mask) mask)
 (fBand (Nat.beq (fMixMove m goal) goal)
 (fTreeBlock 0 width (fun i =>
 fBand (Nat.blt (sel i) width)
 (fBand (Nat.blt (inv i) width)
 (fBand (Nat.beq (inv (sel i)) i)
 (fBand (Nat.beq (sel (inv i)) i)
 (fBor (Nat.beq (Nat.land (Nat.shiftRight mask i) 1) 0)
 (Nat.beq (fMixMove m (Nat.shiftLeft 1 i)) (Nat.shiftLeft 1 (inv i))))))))))))
theorem moveAutoOK_of_check {width : Nat} {mask goal : Word} {m : WordMove}
    {sel inv : Nat → Nat} (hok : fMoveAutoCheck width mask goal m sel inv=true) :
    MoveAutoOK mask goal width m:=by
  unfold fMoveAutoCheck at hok
  simp only [fBand_eq,fTreeBlock_eq,Bool.and_eq_true,Nat.beq_eq] at hok
  obtain ⟨bm,gm,mm,mg,hloop⟩:=hok
  rw [fMixMove_eq] at mm mg
  have hrow : ∀ i : Fin width,
      sel i.val < width ∧ inv i.val < width ∧ inv (sel i.val)=i.val ∧ sel (inv i.val)=i.val ∧
      (mask.testBit i.val=true → mixMove m (2 ^ i.val)=2 ^ inv i.val):=by
    intro i
    have hi:=treeBlock_at hloop (Nat.zero_le i.val) (by simpa using i.isLt)
    simp only [fBand_eq,fBor_eq,Bool.and_eq_true,Bool.or_eq_true,Nat.blt_eq,Nat.beq_eq] at hi
    obtain ⟨hs,hv,hil,hir,hb⟩:=hi
    refine ⟨hs,hv,hil,hir,fun hbit => ?_⟩
    rcases hb with h0 | heq
    · exfalso
      have h0' : (Nat.land (Nat.shiftRight mask i.val) 1).testBit 0=false:=by rw [h0];rfl
      change ((mask>>>i.val)&&&1).testBit 0=false at h0'
      simp [Nat.testBit_and,Nat.testBit_shiftRight,hbit] at h0'
    · simpa [fMixMove_eq,Nat.shiftLeft_eq] using heq
  let sF : Fin width → Fin width:=fun i=>⟨sel i.val,(hrow i).1⟩
  let iF : Fin width → Fin width:=fun i=>⟨inv i.val,(hrow i).2.1⟩
  exact ⟨sF,dagAutoFromMove (inverse:=iF)
    (fun i=>Fin.ext (hrow i).2.2.1)
    (fun i=>Fin.ext (hrow i).2.2.2.1)
    bm gm (fun i h=>(hrow i).2.2.2.2 h) mm mg⟩
def fGetDMove (gens : List WordMove) (idx : Nat) : WordMove :=
 (List.rec (motive:=fun _=>Nat → WordMove) (fun _=>[])
 (fun g _ next k=>Nat.casesOn k g (fun k'=>next k')) gens) idx
theorem fGetDMove_ok {width : Nat} {mask goal : Word}
    (bm : Masked (fullMask width) mask) (gm : Masked mask goal)
    {gens : List WordMove} (hg : ∀ m ∈ gens,MoveAutoOK mask goal width m) :
    ∀ idx,MoveAutoOK mask goal width (fGetDMove gens idx):=by
  induction gens with
  | nil=>intro _;exact moveAutoOK_nil bm gm
  | cons g gs ih =>
    intro idx
    cases idx with
    | zero=>exact hg g List.mem_cons_self
    | succ k=>exact ih (fun m hm=>hg m (List.mem_cons_of_mem _ hm)) k
def fAppendSteps (m1 m2 : WordMove) : WordMove :=
 List.rec m2 (fun s _ next=>s :: next) m1
theorem fAppendSteps_eq (m1 m2 : WordMove) : fAppendSteps m1 m2=m1 ++ m2:=by
  induction m1 with
  | nil=>rfl
  | cons s rest ih=>exact congrArg (s :: ·) ih
def fUnpackMove (gens : List WordMove) (idxBits idxMask code : Nat) : WordMove :=
  let len:=Nat.land code 7
  (Nat.rec (motive:=fun _=>Nat → WordMove) (fun _=>[])
    (fun _ next rest =>
      fAppendSteps (fGetDMove gens (Nat.land rest idxMask)) (next (Nat.shiftRight rest idxBits)))
    len) (Nat.shiftRight code 3)
theorem fUnpackMove_ok {width : Nat} {mask goal : Word}
    (bm : Masked (fullMask width) mask) (gm : Masked mask goal)
    {gens : List WordMove} (hg : ∀ m ∈ gens,MoveAutoOK mask goal width m)
    (idxBits idxMask code : Nat) :
    MoveAutoOK mask goal width (fUnpackMove gens idxBits idxMask code):=by
  unfold fUnpackMove
  suffices h : ∀ n rest,MoveAutoOK mask goal width
      ((Nat.rec (motive:=fun _=>Nat → WordMove) (fun _=>[])
        (fun _ next r=>fAppendSteps (fGetDMove gens (Nat.land r idxMask)) (next (Nat.shiftRight r idxBits))) n) rest) from h _ _
  intro n
  induction n with
  | zero=>intro _;exact moveAutoOK_nil bm gm
  | succ n ih =>
    intro rest
    change MoveAutoOK mask goal width (fAppendSteps _ _)
    rw [fAppendSteps_eq]
    exact moveAutoOK_append (fGetDMove_ok bm gm hg _) (ih _)
def fPackedMovesFn (gens : List WordMove) (packed bound chunkBits chunkMask idxBits idxMask : Nat)
 (a : Nat) : Option WordMove :=
 @Bool.rec (fun _=>Option WordMove) none
 (some (fUnpackMove gens idxBits idxMask (Nat.land (Nat.shiftRight packed (Nat.mul chunkBits a)) chunkMask)))
 (Nat.blt a bound)
theorem dagMovesFnOK1OfPackedGens {width : Nat} {mask goal : Word}
    {gens : List WordMove} {packed bound chunkBits chunkMask idxBits idxMask : Nat}
    (bm : Masked (fullMask width) mask) (gm : Masked mask goal)
    (hg : ∀ m ∈ gens,MoveAutoOK mask goal width m) :
    DagMovesFnOK1 mask goal width (fPackedMovesFn gens packed bound chunkBits chunkMask idxBits idxMask):=by
  intro a m hm
  unfold fPackedMovesFn at hm
  cases h : Nat.blt a bound
  · rw [h] at hm;exact nomatch hm
  · rw [h] at hm
    have heq : fUnpackMove gens idxBits idxMask (Nat.land (Nat.shiftRight packed (Nat.mul chunkBits a)) chunkMask)=m :=
      Option.some.inj hm
    rw [← heq]
    exact fUnpackMove_ok bm gm hg idxBits idxMask _
def s64_01 : WordMoveStep:=([(0x9999999999999999,0),(0x2222222222222222,1)],[(0x4444444444444444,1)])
def s64_02 : WordMoveStep:=([(0xa5a5a5a5a5a5a5a5,0),(0xa0a0a0a0a0a0a0a,3)],[(0x5050505050505050,3)])
def s64_03 : WordMoveStep:=([(0xaa55aa55aa55aa55,0),(0xaa00aa00aa00aa,7)],[(0x5500550055005500,7)])
def s64_04 : WordMoveStep:=([(0xaaaa5555aaaa5555,0),(0xaaaa0000aaaa,15)],[(0x5555000055550000,15)])
def s64_05 : WordMoveStep:=([(0xaaaaaaaa55555555,0),(0xaaaaaaaa,31)],[(0x5555555500000000,31)])
def s64_12 : WordMoveStep:=([(0xc3c3c3c3c3c3c3c3,0),(0xc0c0c0c0c0c0c0c,2)],[(0x3030303030303030,2)])
def s64_13 : WordMoveStep:=([(0xcc33cc33cc33cc33,0),(0xcc00cc00cc00cc,6)],[(0x3300330033003300,6)])
def s64_14 : WordMoveStep:=([(0xcccc3333cccc3333,0),(0xcccc0000cccc,14)],[(0x3333000033330000,14)])
def s64_15 : WordMoveStep:=([(0xcccccccc33333333,0),(0xcccccccc,30)],[(0x3333333300000000,30)])
def s64_23 : WordMoveStep:=([(0xf00ff00ff00ff00f,0),(0xf000f000f000f0,4)],[(0xf000f000f000f00,4)])
def s64_24 : WordMoveStep:=([(0xf0f00f0ff0f00f0f,0),(0xf0f00000f0f0,12)],[(0xf0f00000f0f0000,12)])
def s64_25 : WordMoveStep:=([(0xf0f0f0f00f0f0f0f,0),(0xf0f0f0f0,28)],[(0xf0f0f0f00000000,28)])
def s64_34 : WordMoveStep:=([(0xff0000ffff0000ff,0),(0xff000000ff00,8)],[(0xff000000ff0000,8)])
def s64_35 : WordMoveStep:=([(0xff00ff0000ff00ff,0),(0xff00ff00,24)],[(0xff00ff00000000,24)])
def s64_45 : WordMoveStep:=([(0xffff00000000ffff,0),(0xffff0000,16)],[(0xffff00000000,16)])
def k4_64_t0Mask : Word:=0xffff
def k4_64_t0Goal : Word:=0xfee8
def k4_64_t0Stock : List Word:=[0xaaaa,0xcccc,0xf0f0,0xff00]
def k4_64_t0Chart : Option RowChart:=some ⟨[3,5,6,9,10,12,3,3,3,3,3,3,1,2,4,8,1,1,1,1,1,1,1,1],rfl⟩
def k4_64_t0Wit : List Witness:=[(0xaaaa,3,2),(0xcccc,3,1),(0xf0f0,5,1),(0xff00,9,1)]
def k4_64_t0Sample : DagSample1:=(0x80304024100a02018100c02014080c01018040a0100c0203008240205,13)
def k4_64_t0Data : Forest:=fun i=>fDecodeNode 3 9 0xe4a9a64f278 i
def k4_64_t0Buckets : DagBuckets1 :=
  dagBucketBlock 0x1116a0003801 0x80715b3646ca85836060aa162b8389dd32b72c9d931f62c6cd02b3209c901f2206c10130203c000f 9 0x1ff 4 0xf 18 0x3ffff 11 0x7ff 0x7 14 4
theorem k4_64_t0BucketsValid : BucketsValid k4_64_t0Buckets :=
  dagBucketBlock_valid 0x1116a0003801 0x80715b3646ca85836060aa162b8389dd32b72c9d931f62c6cd02b3209c901f2206c10130203c000f 9 0x1ff 4 0xf 18 0x3ffff 11 0x7ff 0x7 14 4
noncomputable def k4_64_t0Tags:=fDagTraceTags k4_64_t0Mask 13 (dagTagBases1 k4_64_t0Stock 0x6a90f86c7988f 0x6804b00070007 13) 6 k4_64_t0Data
noncomputable def k4_64_t0States:=fDagTrace k4_64_t0Mask k4_64_t0Stock 6 0 k4_64_t0Data
noncomputable def k4_64_t0Light:=fDagTraceLight k4_64_t0Mask k4_64_t0Stock 6 0 k4_64_t0Data
def k4_64_t0Gens : List WordMove:=[[s64_01],[s64_02],[s64_12],[s64_13],[s64_23]]
def k4_64_t0MovesFn : DagMovesFn1 :=
  fPackedMovesFn k4_64_t0Gens 0xca8c308210200111a011021000 9 12 0xfff 3 0x7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_64_t0GensOK : ∀ m ∈ k4_64_t0Gens,MoveAutoOK k4_64_t0Mask k4_64_t0Goal 64 m:=by
  simp only [k4_64_t0Gens,List.mem_cons,List.not_mem_nil,or_false]
  intro m hm;rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 1) (inv:=fSwapBits 0 1) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 2) (inv:=fSwapBits 0 2) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 2) (inv:=fSwapBits 1 2) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 3) (inv:=fSwapBits 1 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 2 3) (inv:=fSwapBits 2 3) (by decide +kernel)
theorem k4_64_t0Autos : DagMovesFnOK1 k4_64_t0Mask k4_64_t0Goal 64 k4_64_t0MovesFn :=
  dagMovesFnOK1OfPackedGens (by unfold Masked;decide +kernel) (by unfold Masked;decide +kernel) k4_64_t0GensOK
def k4_64_t0Cuts : List ExactBound:=[]
theorem k4_64_t0Known : ExactKnown k4_64_t0Cuts:=show ExactKnown [] from fun _ h=>False.elim (List.not_mem_nil h)
noncomputable def k4_64_t0Check:=fDagCheckNode 2 64 6 false k4_64_t0Mask k4_64_t0Goal k4_64_t0Chart (fExactKnownCloses false k4_64_t0Goal k4_64_t0Cuts) 5 k4_64_t0Data k4_64_t0States k4_64_t0Light k4_64_t0MovesFn k4_64_t0Buckets k4_64_t0Sample k4_64_t0Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_64_t0Roots : fDagCheckRoots 2 false k4_64_t0Mask k4_64_t0Goal k4_64_t0Chart (fExactKnownCloses false k4_64_t0Goal k4_64_t0Cuts) k4_64_t0Wit 5 k4_64_t0Data k4_64_t0Light k4_64_t0MovesFn k4_64_t0Buckets k4_64_t0Stock 6 0=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_64_t0B0 : treeBlock 0 5 k4_64_t0Check=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_64_t0Lower : ExactLower k4_64_t0Mask k4_64_t0Stock k4_64_t0Goal 0 7:=by
  apply exactLowerDagFast (maxK:=2) (stride:=64) (steps:=6)
    (is24:=false) (allowNotInPast:=false) (width:=64)
    (sample:=k4_64_t0Sample) (tags:=k4_64_t0Tags)
    (by decide) (sampleValidOfCheck (by decide +kernel)) (fun h=>Bool.noConfusion h) (by decide) _ _ _ k4_64_t0Autos k4_64_t0BucketsValid _ _ _ k4_64_t0Known _ _ k4_64_t0Roots k4_64_t0B0
  · unfold Masked;decide +kernel
  · unfold Masked;decide +kernel
  · exact chartOfCheck (chart:=k4_64_t0Chart) (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold k4_64_t0Stock;decide +kernel
  · decide +kernel
  · exact fun _ h=>False.elim (List.not_mem_nil h)
  · exact fun _ h=>False.elim (List.not_mem_nil h)
def k4_64_t1Mask : Word:=0xffff
def k4_64_t1Goal : Word:=0xfee8
def k4_64_t1Stock : List Word:=[0xaaaa,0xcccc,0xf0f0,0xff00]
def k4_64_t1Chart : Option RowChart:=some ⟨[3,5,6,9,10,12,3,3,3,3,3,3,1,2,4,8,1,1,1,1,1,1,1,1],rfl⟩
def k4_64_t1Wit : List Witness:=[(0xaaaa,3,2),(0xcccc,3,1),(0xf0f0,5,1),(0xff00,9,1)]
def k4_64_t1Sample : DagSample1:=(0x818020a0400c080304028100c04024080601018040a0203008050100c0203008140209,16)
def k4_64_t1Data : Forest:=fun i=>fDecodeNode 5 17 0x51700cb0084e4c1ec68e324681234071a020a31c481a24045002080343b15118988054431d198e0c0a86052302818130c07840342013080784024201e0 i
def k4_64_t1Buckets : DagBuckets1 :=
  dagBucketBlock 0x9c29a19629030008e18c10000000008a18057847426866616225c35a100000044b2eb226030001 0x8e18e170070360381c0286d80e36cc61360301b00c0d01406804033260186348b19425cc70ac0501701c0b992158c602c0481501c1881a0440a06805433029180140500782603a1001c0a00804cc702406891012088088400401e0682e63616b190398a81ac4cac336461950b00d8180548b00e058068280311663c0b31d0518e0a40d85006a27034130190240a81005207028030131940d8c80644502a2201301407808034e192da1b15d0989d82c432332b91193c0cc7e04636813153181598809c8603e4201b0180980803c020120000f 12 0xfff 5 0x1f 21 0x1fffff 12 0xfff 0x1f 17 5
theorem k4_64_t1BucketsValid : BucketsValid k4_64_t1Buckets :=
  dagBucketBlock_valid 0x9c29a19629030008e18c10000000008a18057847426866616225c35a100000044b2eb226030001 0x8e18e170070360381c0286d80e36cc61360301b00c0d01406804033260186348b19425cc70ac0501701c0b992158c602c0481501c1881a0440a06805433029180140500782603a1001c0a00804cc702406891012088088400401e0682e63616b190398a81ac4cac336461950b00d8180548b00e058068280311663c0b31d0518e0a40d85006a27034130190240a81005207028030131940d8c80644502a2201301407808034e192da1b15d0989d82c432332b91193c0cc7e04636813153181598809c8603e4201b0180980803c020120000f 12 0xfff 5 0x1f 21 0x1fffff 12 0xfff 0x1f 17 5
noncomputable def k4_64_t1Tags:=fDagTraceTags k4_64_t1Mask 16 (dagTagBases1 k4_64_t1Stock 0x4e6185b2f9cc321f 0x2e00113000c8c007 16) 7 k4_64_t1Data
noncomputable def k4_64_t1States:=fDagTrace k4_64_t1Mask k4_64_t1Stock 7 1 k4_64_t1Data
noncomputable def k4_64_t1Light:=fDagTraceLight k4_64_t1Mask k4_64_t1Stock 7 1 k4_64_t1Data
def k4_64_t1Gens : List WordMove:=[[s64_01],[s64_02],[s64_03],[s64_12],[s64_13],[s64_23]]
def k4_64_t1MovesFn : DagMovesFn1 :=
  fPackedMovesFn k4_64_t1Gens 0x10ab030c2b130ca142001162019029000 11 12 0xfff 3 0x7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_64_t1GensOK : ∀ m ∈ k4_64_t1Gens,MoveAutoOK k4_64_t1Mask k4_64_t1Goal 64 m:=by
  simp only [k4_64_t1Gens,List.mem_cons,List.not_mem_nil,or_false]
  intro m hm;rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 1) (inv:=fSwapBits 0 1) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 2) (inv:=fSwapBits 0 2) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 3) (inv:=fSwapBits 0 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 2) (inv:=fSwapBits 1 2) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 3) (inv:=fSwapBits 1 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 2 3) (inv:=fSwapBits 2 3) (by decide +kernel)
theorem k4_64_t1Autos : DagMovesFnOK1 k4_64_t1Mask k4_64_t1Goal 64 k4_64_t1MovesFn :=
  dagMovesFnOK1OfPackedGens (by unfold Masked;decide +kernel) (by unfold Masked;decide +kernel) k4_64_t1GensOK
def k4_64_t1Cuts : List ExactBound:=[]
theorem k4_64_t1Known : ExactKnown k4_64_t1Cuts:=show ExactKnown [] from fun _ h=>False.elim (List.not_mem_nil h)
noncomputable def k4_64_t1Check:=fDagCheckNode 2 64 6 false k4_64_t1Mask k4_64_t1Goal k4_64_t1Chart (fExactKnownCloses true k4_64_t1Goal k4_64_t1Cuts) 29 k4_64_t1Data k4_64_t1States k4_64_t1Light k4_64_t1MovesFn k4_64_t1Buckets k4_64_t1Sample k4_64_t1Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_64_t1Roots : fDagCheckRoots 2 false k4_64_t1Mask k4_64_t1Goal k4_64_t1Chart (fExactKnownCloses true k4_64_t1Goal k4_64_t1Cuts) k4_64_t1Wit 29 k4_64_t1Data k4_64_t1Light k4_64_t1MovesFn k4_64_t1Buckets k4_64_t1Stock 7 1=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_64_t1B0 : treeBlock 0 29 k4_64_t1Check=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_64_t1Lower : ExactLower k4_64_t1Mask k4_64_t1Stock k4_64_t1Goal 1 8:=by
  apply exactLowerDagFast (maxK:=2) (stride:=64) (steps:=6)
    (is24:=false) (allowNotInPast:=true) (width:=64)
    (sample:=k4_64_t1Sample) (tags:=k4_64_t1Tags)
    (by decide) (sampleValidOfCheck (by decide +kernel)) (fun h=>Bool.noConfusion h) (by decide) _ _ _ k4_64_t1Autos k4_64_t1BucketsValid _ _ _ k4_64_t1Known _ _ k4_64_t1Roots k4_64_t1B0
  · unfold Masked;decide +kernel
  · unfold Masked;decide +kernel
  · exact chartOfCheck (chart:=k4_64_t1Chart) (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold k4_64_t1Stock;decide +kernel
  · decide +kernel
  · exact fun _ h=>False.elim (List.not_mem_nil h)
  · exact fun _ h=>False.elim (List.not_mem_nil h)
def k4_4_5Fact : ExactBound:=(k4_64_t0Mask,k4_64_t0Stock,7,8,k4_64_t0Goal)
def k4_0_1Mask : Word:=0x1111111111111111
def k4_0_1Goal : Word:=0x1111111011101000
def k4_0_1Stock : List Word:=[0x1010101010101010,0x1100110011001100,0x1111000011110000,0x1111111100000000]
def k4_0_1Fact : ExactBound:=(k4_0_1Mask,k4_0_1Stock,7,8,k4_0_1Goal)
def k4_0_1Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [2,3,4,5,0,1] 0 i.val)
def k4_0_1Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [4,5,0,1,2,3] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_0_1_t0Lower : ExactLower k4_0_1Mask k4_0_1Stock k4_0_1Goal 0 7 :=
  exactLowerRelabel k4_0_1Sel k4_0_1Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_0_1_t1Lower : ExactLower k4_0_1Mask k4_0_1Stock k4_0_1Goal 1 8 :=
  exactLowerRelabel k4_0_1Sel k4_0_1Inv (by decide +kernel) k4_64_t1Lower
def k4_0_2Mask : Word:=0x505050505050505
def k4_0_2Goal : Word:=0x505050405040400
def k4_0_2Stock : List Word:=[0x404040404040404,0x500050005000500,0x505000005050000,0x505050500000000]
def k4_0_2Fact : ExactBound:=(k4_0_2Mask,k4_0_2Stock,7,8,k4_0_2Goal)
def k4_0_2Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [1,3,4,5,0,2] 0 i.val)
def k4_0_2Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [4,0,5,1,2,3] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_0_2_t0Lower : ExactLower k4_0_2Mask k4_0_2Stock k4_0_2Goal 0 7 :=
  exactLowerRelabel k4_0_2Sel k4_0_2Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_0_2_t1Lower : ExactLower k4_0_2Mask k4_0_2Stock k4_0_2Goal 1 8 :=
  exactLowerRelabel k4_0_2Sel k4_0_2Inv (by decide +kernel) k4_64_t1Lower
def k4_0_3Mask : Word:=0x55005500550055
def k4_0_3Goal : Word:=0x55005400540040
def k4_0_3Stock : List Word:=[0x44004400440044,0x50005000500050,0x55000000550000,0x55005500000000]
def k4_0_3Fact : ExactBound:=(k4_0_3Mask,k4_0_3Stock,7,8,k4_0_3Goal)
def k4_0_3Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [1,2,4,5,0,3] 0 i.val)
def k4_0_3Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [4,0,1,5,2,3] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_0_3_t0Lower : ExactLower k4_0_3Mask k4_0_3Stock k4_0_3Goal 0 7 :=
  exactLowerRelabel k4_0_3Sel k4_0_3Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_0_3_t1Lower : ExactLower k4_0_3Mask k4_0_3Stock k4_0_3Goal 1 8 :=
  exactLowerRelabel k4_0_3Sel k4_0_3Inv (by decide +kernel) k4_64_t1Lower
def k4_0_4Mask : Word:=0x555500005555
def k4_0_4Goal : Word:=0x555400005440
def k4_0_4Stock : List Word:=[0x444400004444,0x505000005050,0x550000005500,0x555500000000]
def k4_0_4Fact : ExactBound:=(k4_0_4Mask,k4_0_4Stock,7,8,k4_0_4Goal)
def k4_0_4Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [1,2,3,5,0,4] 0 i.val)
def k4_0_4Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [4,0,1,2,5,3] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_0_4_t0Lower : ExactLower k4_0_4Mask k4_0_4Stock k4_0_4Goal 0 7 :=
  exactLowerRelabel k4_0_4Sel k4_0_4Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_0_4_t1Lower : ExactLower k4_0_4Mask k4_0_4Stock k4_0_4Goal 1 8 :=
  exactLowerRelabel k4_0_4Sel k4_0_4Inv (by decide +kernel) k4_64_t1Lower
def k4_0_5Mask : Word:=0x55555555
def k4_0_5Goal : Word:=0x55545440
def k4_0_5Stock : List Word:=[0x44444444,0x50505050,0x55005500,0x55550000]
def k4_0_5Fact : ExactBound:=(k4_0_5Mask,k4_0_5Stock,7,8,k4_0_5Goal)
def k4_0_5Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [1,2,3,4,0,5] 0 i.val)
def k4_0_5Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [4,0,1,2,3,5] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_0_5_t0Lower : ExactLower k4_0_5Mask k4_0_5Stock k4_0_5Goal 0 7 :=
  exactLowerRelabel k4_0_5Sel k4_0_5Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_0_5_t1Lower : ExactLower k4_0_5Mask k4_0_5Stock k4_0_5Goal 1 8 :=
  exactLowerRelabel k4_0_5Sel k4_0_5Inv (by decide +kernel) k4_64_t1Lower
def k4_1_2Mask : Word:=0x303030303030303
def k4_1_2Goal : Word:=0x303030203020200
def k4_1_2Stock : List Word:=[0x202020202020202,0x300030003000300,0x303000003030000,0x303030300000000]
def k4_1_2Fact : ExactBound:=(k4_1_2Mask,k4_1_2Stock,7,8,k4_1_2Goal)
def k4_1_2Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,3,4,5,1,2] 0 i.val)
def k4_1_2Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,4,5,1,2,3] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_1_2_t0Lower : ExactLower k4_1_2Mask k4_1_2Stock k4_1_2Goal 0 7 :=
  exactLowerRelabel k4_1_2Sel k4_1_2Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_1_2_t1Lower : ExactLower k4_1_2Mask k4_1_2Stock k4_1_2Goal 1 8 :=
  exactLowerRelabel k4_1_2Sel k4_1_2Inv (by decide +kernel) k4_64_t1Lower
def k4_1_3Mask : Word:=0x33003300330033
def k4_1_3Goal : Word:=0x33003200320020
def k4_1_3Stock : List Word:=[0x22002200220022,0x30003000300030,0x33000000330000,0x33003300000000]
def k4_1_3Fact : ExactBound:=(k4_1_3Mask,k4_1_3Stock,7,8,k4_1_3Goal)
def k4_1_3Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,2,4,5,1,3] 0 i.val)
def k4_1_3Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,4,1,5,2,3] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_1_3_t0Lower : ExactLower k4_1_3Mask k4_1_3Stock k4_1_3Goal 0 7 :=
  exactLowerRelabel k4_1_3Sel k4_1_3Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_1_3_t1Lower : ExactLower k4_1_3Mask k4_1_3Stock k4_1_3Goal 1 8 :=
  exactLowerRelabel k4_1_3Sel k4_1_3Inv (by decide +kernel) k4_64_t1Lower
def k4_1_4Mask : Word:=0x333300003333
def k4_1_4Goal : Word:=0x333200003220
def k4_1_4Stock : List Word:=[0x222200002222,0x303000003030,0x330000003300,0x333300000000]
def k4_1_4Fact : ExactBound:=(k4_1_4Mask,k4_1_4Stock,7,8,k4_1_4Goal)
def k4_1_4Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,2,3,5,1,4] 0 i.val)
def k4_1_4Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,4,1,2,5,3] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_1_4_t0Lower : ExactLower k4_1_4Mask k4_1_4Stock k4_1_4Goal 0 7 :=
  exactLowerRelabel k4_1_4Sel k4_1_4Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_1_4_t1Lower : ExactLower k4_1_4Mask k4_1_4Stock k4_1_4Goal 1 8 :=
  exactLowerRelabel k4_1_4Sel k4_1_4Inv (by decide +kernel) k4_64_t1Lower
def k4_1_5Mask : Word:=0x33333333
def k4_1_5Goal : Word:=0x33323220
def k4_1_5Stock : List Word:=[0x22222222,0x30303030,0x33003300,0x33330000]
def k4_1_5Fact : ExactBound:=(k4_1_5Mask,k4_1_5Stock,7,8,k4_1_5Goal)
def k4_1_5Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,2,3,4,1,5] 0 i.val)
def k4_1_5Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,4,1,2,3,5] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_1_5_t0Lower : ExactLower k4_1_5Mask k4_1_5Stock k4_1_5Goal 0 7 :=
  exactLowerRelabel k4_1_5Sel k4_1_5Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_1_5_t1Lower : ExactLower k4_1_5Mask k4_1_5Stock k4_1_5Goal 1 8 :=
  exactLowerRelabel k4_1_5Sel k4_1_5Inv (by decide +kernel) k4_64_t1Lower
def k4_2_3Mask : Word:=0xf000f000f000f
def k4_2_3Goal : Word:=0xf000e000e0008
def k4_2_3Stock : List Word:=[0xa000a000a000a,0xc000c000c000c,0xf0000000f0000,0xf000f00000000]
def k4_2_3Fact : ExactBound:=(k4_2_3Mask,k4_2_3Stock,7,8,k4_2_3Goal)
def k4_2_3Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,4,5,2,3] 0 i.val)
def k4_2_3Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,4,5,2,3] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_2_3_t0Lower : ExactLower k4_2_3Mask k4_2_3Stock k4_2_3Goal 0 7 :=
  exactLowerRelabel k4_2_3Sel k4_2_3Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_2_3_t1Lower : ExactLower k4_2_3Mask k4_2_3Stock k4_2_3Goal 1 8 :=
  exactLowerRelabel k4_2_3Sel k4_2_3Inv (by decide +kernel) k4_64_t1Lower
def k4_2_4Mask : Word:=0xf0f00000f0f
def k4_2_4Goal : Word:=0xf0e00000e08
def k4_2_4Stock : List Word:=[0xa0a00000a0a,0xc0c00000c0c,0xf0000000f00,0xf0f00000000]
def k4_2_4Fact : ExactBound:=(k4_2_4Mask,k4_2_4Stock,7,8,k4_2_4Goal)
def k4_2_4Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,3,5,2,4] 0 i.val)
def k4_2_4Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,4,2,5,3] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_2_4_t0Lower : ExactLower k4_2_4Mask k4_2_4Stock k4_2_4Goal 0 7 :=
  exactLowerRelabel k4_2_4Sel k4_2_4Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_2_4_t1Lower : ExactLower k4_2_4Mask k4_2_4Stock k4_2_4Goal 1 8 :=
  exactLowerRelabel k4_2_4Sel k4_2_4Inv (by decide +kernel) k4_64_t1Lower
def k4_2_5Mask : Word:=0xf0f0f0f
def k4_2_5Goal : Word:=0xf0e0e08
def k4_2_5Stock : List Word:=[0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def k4_2_5Fact : ExactBound:=(k4_2_5Mask,k4_2_5Stock,7,8,k4_2_5Goal)
def k4_2_5Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,3,4,2,5] 0 i.val)
def k4_2_5Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,4,2,3,5] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_2_5_t0Lower : ExactLower k4_2_5Mask k4_2_5Stock k4_2_5Goal 0 7 :=
  exactLowerRelabel k4_2_5Sel k4_2_5Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_2_5_t1Lower : ExactLower k4_2_5Mask k4_2_5Stock k4_2_5Goal 1 8 :=
  exactLowerRelabel k4_2_5Sel k4_2_5Inv (by decide +kernel) k4_64_t1Lower
def k4_3_4Mask : Word:=0xff000000ff
def k4_3_4Goal : Word:=0xfe000000e8
def k4_3_4Stock : List Word:=[0xaa000000aa,0xcc000000cc,0xf0000000f0,0xff00000000]
def k4_3_4Fact : ExactBound:=(k4_3_4Mask,k4_3_4Stock,7,8,k4_3_4Goal)
def k4_3_4Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,2,5,3,4] 0 i.val)
def k4_3_4Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,2,4,5,3] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_3_4_t0Lower : ExactLower k4_3_4Mask k4_3_4Stock k4_3_4Goal 0 7 :=
  exactLowerRelabel k4_3_4Sel k4_3_4Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_3_4_t1Lower : ExactLower k4_3_4Mask k4_3_4Stock k4_3_4Goal 1 8 :=
  exactLowerRelabel k4_3_4Sel k4_3_4Inv (by decide +kernel) k4_64_t1Lower
def k4_3_5Mask : Word:=0xff00ff
def k4_3_5Goal : Word:=0xfe00e8
def k4_3_5Stock : List Word:=[0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def k4_3_5Fact : ExactBound:=(k4_3_5Mask,k4_3_5Stock,7,8,k4_3_5Goal)
def k4_3_5Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,2,4,3,5] 0 i.val)
def k4_3_5Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,2,4,3,5] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_3_5_t0Lower : ExactLower k4_3_5Mask k4_3_5Stock k4_3_5Goal 0 7 :=
  exactLowerRelabel k4_3_5Sel k4_3_5Inv (by decide +kernel) k4_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_3_5_t1Lower : ExactLower k4_3_5Mask k4_3_5Stock k4_3_5Goal 1 8 :=
  exactLowerRelabel k4_3_5Sel k4_3_5Inv (by decide +kernel) k4_64_t1Lower
def k5_64_t0Mask : Word:=0xffffffff
def k5_64_t0Goal : Word:=0xfffefee8
def k5_64_t0Stock : List Word:=[0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def k5_64_t0Chart : Option RowChart:=some ⟨[3,5,6,9,10,12,17,18,20,24,3,3,1,2,4,8,16,1,1,1,1,1,1,1],rfl⟩
def k5_64_t0Wit : List Witness:=[(0xaaaaaaaa,3,2),(0xcccccccc,3,1),(0xf0f0f0f0,5,1),(0xff00ff00,9,1),(0xffff0000,17,1)]
def k5_64_t0Sample : DagSample1:=(0x10090804808060804420140200c100a08060040604030101801028080501048080c0205002090081402110100c0203,21)
def k5_64_t0Data : Forest:=fun i=>fDecodeNode 4 16 0x634b34283288937702b763c694256425c4333373036301c3937262b262a202a2013101f0 i
def k5_64_t0Buckets : DagBuckets1 :=
  dagBucketBlock 0x4a192311618c0372eb35240003542fc0d001 0x116340458d1b06406418d1700405400d00e01c03407150942040d080f32803a4dded6377358accd3372b4cac2d0370340aee9c4eb265380c63c12d8d40b6295a4d3aab34281ccd1c73281a413a4b04239c0d0a70280ae5380b9420a99380a6425a0d39483421a01384804202710cc89432a24dcc764229d8d828343020cdc2704201c0d80601c21710c259430164dc6464318d9084463710d8d80462b00d8a962342508cd92232a188108420360080aa819379858de4162b884cde0132b704c7d010373840aca101f00404c0001f 11 0x7ff 4 0xf 22 0x3fffff 12 0xfff 0x1f 17 4
theorem k5_64_t0BucketsValid : BucketsValid k5_64_t0Buckets :=
  dagBucketBlock_valid 0x4a192311618c0372eb35240003542fc0d001 0x116340458d1b06406418d1700405400d00e01c03407150942040d080f32803a4dded6377358accd3372b4cac2d0370340aee9c4eb265380c63c12d8d40b6295a4d3aab34281ccd1c73281a413a4b04239c0d0a70280ae5380b9420a99380a6425a0d39483421a01384804202710cc89432a24dcc764229d8d828343020cdc2704201c0d80601c21710c259430164dc6464318d9084463710d8d80462b00d8a962342508cd92232a188108420360080aa819379858de4162b884cde0132b704c7d010373840aca101f00404c0001f 11 0x7ff 4 0xf 22 0x3fffff 12 0xfff 0x1f 17 4
noncomputable def k5_64_t0Tags:=fDagTraceTags k5_64_t0Mask 21 (dagTagBases1 k5_64_t0Stock 0xb24a4837281465a19a5072811f 0xb200082600120580025040001d 21) 9 k5_64_t0Data
noncomputable def k5_64_t0States:=fDagTrace k5_64_t0Mask k5_64_t0Stock 9 0 k5_64_t0Data
noncomputable def k5_64_t0Light:=fDagTraceLight k5_64_t0Mask k5_64_t0Stock 9 0 k5_64_t0Data
def k5_64_t0Gens : List WordMove:=[[s64_01],[s64_02],[s64_03],[s64_12],[s64_13],[s64_14],[s64_23],[s64_24],[s64_34]]
def k5_64_t0MovesFn : DagMovesFn1 :=
  fPackedMovesFn k5_64_t0Gens 0x73270e8301905c3294085160082a1d4203203083060060a1cc60318b0870600c080000843ab0064401068000c8043200874000c4002080000 24 19 0x7ffff 4 0xf
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_64_t0GensOK : ∀ m ∈ k5_64_t0Gens,MoveAutoOK k5_64_t0Mask k5_64_t0Goal 64 m:=by
  simp only [k5_64_t0Gens,List.mem_cons,List.not_mem_nil,or_false]
  intro m hm;rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 1) (inv:=fSwapBits 0 1) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 2) (inv:=fSwapBits 0 2) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 3) (inv:=fSwapBits 0 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 2) (inv:=fSwapBits 1 2) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 3) (inv:=fSwapBits 1 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 4) (inv:=fSwapBits 1 4) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 2 3) (inv:=fSwapBits 2 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 2 4) (inv:=fSwapBits 2 4) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 3 4) (inv:=fSwapBits 3 4) (by decide +kernel)
theorem k5_64_t0Autos : DagMovesFnOK1 k5_64_t0Mask k5_64_t0Goal 64 k5_64_t0MovesFn :=
  dagMovesFnOK1OfPackedGens (by unfold Masked;decide +kernel) (by unfold Masked;decide +kernel) k5_64_t0GensOK
def k5_64_t0Cuts : List ExactBound:=[k4_0_5Fact,k4_1_5Fact,k4_2_5Fact,k4_3_5Fact,k4_4_5Fact]
theorem k5_64_t0Known : ExactKnown k5_64_t0Cuts:=extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (show ExactKnown [] from fun _ h=>False.elim (List.not_mem_nil h)) k4_64_t0Lower k4_64_t1Lower) k4_3_5_t0Lower k4_3_5_t1Lower) k4_2_5_t0Lower k4_2_5_t1Lower) k4_1_5_t0Lower k4_1_5_t1Lower) k4_0_5_t0Lower k4_0_5_t1Lower
noncomputable def k5_64_t0Check:=fDagCheckNode 2 64 6 false k5_64_t0Mask k5_64_t0Goal k5_64_t0Chart (fExactKnownCloses false k5_64_t0Goal k5_64_t0Cuts) 18 k5_64_t0Data k5_64_t0States k5_64_t0Light k5_64_t0MovesFn k5_64_t0Buckets k5_64_t0Sample k5_64_t0Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_64_t0Roots : fDagCheckRoots 2 false k5_64_t0Mask k5_64_t0Goal k5_64_t0Chart (fExactKnownCloses false k5_64_t0Goal k5_64_t0Cuts) k5_64_t0Wit 18 k5_64_t0Data k5_64_t0Light k5_64_t0MovesFn k5_64_t0Buckets k5_64_t0Stock 9 0=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_64_t0B0 : treeBlock 0 18 k5_64_t0Check=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_64_t0Lower : ExactLower k5_64_t0Mask k5_64_t0Stock k5_64_t0Goal 0 10:=by
  apply exactLowerDagFast (maxK:=2) (stride:=64) (steps:=6)
    (is24:=false) (allowNotInPast:=false) (width:=64)
    (sample:=k5_64_t0Sample) (tags:=k5_64_t0Tags)
    (by decide) (sampleValidOfCheck (by decide +kernel)) (fun h=>Bool.noConfusion h) (by decide) _ _ _ k5_64_t0Autos k5_64_t0BucketsValid _ _ _ k5_64_t0Known _ _ k5_64_t0Roots k5_64_t0B0
  · unfold Masked;decide +kernel
  · unfold Masked;decide +kernel
  · exact chartOfCheck (chart:=k5_64_t0Chart) (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold k5_64_t0Stock;decide +kernel
  · decide +kernel
  · simp only [k5_64_t0Cuts,List.mem_cons,List.not_mem_nil,or_false];intro b h;rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · simp only [k5_64_t0Cuts,List.mem_cons,List.not_mem_nil,or_false];intro b h;rcases h with rfl | rfl | rfl | rfl | rfl <;> exact stockMaskedOfCheck (by decide +kernel)
def k5_64_t1Mask : Word:=0xffffffff
def k5_64_t1Goal : Word:=0xfffefee8
def k5_64_t1Stock : List Word:=[0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def k5_64_t1Chart : Option RowChart:=some ⟨[3,5,6,9,10,12,17,18,20,24,3,3,1,2,4,8,16,1,1,1,1,1,1,1],rfl⟩
def k5_64_t1Wit : List Witness:=[(0xaaaaaaaa,3,2),(0xcccccccc,3,1),(0xf0f0f0f0,5,1),(0xff00ff00,9,1),(0xffff0000,17,1)]
def k5_64_t1Sample : DagSample1:=(0x40501050200900848021408028040c08014020c04018200308048020a0200c201108050100908060100a02018100c01018101802030041202050040a0201402090081402110100c0203,33)
def k5_64_t1Data : Forest:=fun i=>fDecodeNode 7 19 0x318a2069200aa3814c70288ec61198c219944364079278da4f1ab203463666c6acd8d19b1a3202560048c00717c9b2c6365806cb18d154a02864c4cc84959052b202563c46c688a52106211ec3d3d88465908cb211863130c6060d08c19b1832830084624dcb8159702a2f28450d08a1941464e1ac68358f4531e0ac4213284259084e1c09c431126e224d844968892c118861ccdc399b070360e0381f10c349b063360c06c1a4dc28158502a0be9e1310823210403208060124dc1b158362a060540d8841b100362b0402604024080f80 i
def k5_64_t1Buckets : DagBuckets1 :=
  dagBucketBlock 0xbb06ea1ba04000b812d84b586d41b486d010002ce1b20ec420002c02af080000002b06aa12a04a612961000284900000009f8e7459a1a6429712506000232f8a1616900020e483060a100020810001fa77b1c0007911e210001c8d0001bc6000000068b59e2641d6f152c94240001385000000000000004c100004a8c0000000f1d3630baf25c878f19a45490b5020600bc001 0x1eae62802b8ca00ae31842898d0ea231c16880d00a20106a8a4d0ba46346288ca06a431c1ab0ca06aa31c1aa0ca06a631c02b00d00aa02a02a00a40a602802918c1ea06284e80ca00a002802898c00a03280a798d009e6288e60cd219832822600d06980288e58ca219631c22580a069601c8e50cd219432822500d06940288e48ca219231c22480a069201c0279902b9a640aa698d1b9c6289a68d0259a3345670ca0b9a0402a680d029c0283e20cd0e88328022004009c93c42118d0e8431c16100d0084010026a4f1a849342221900b8a6346210ca068a31c026190068e33402598d809463502498d068c328862250248a9349e299000906342218c70f860346a030e678a9369e0a4b638a6368e0988468a3368e38c6868e3191a30c6068231502280da78e026023809408c0240208026c866341210c70f8603452100a008a01c862190228663486198a06883401e18cd0686328022010018603402180a008893602198d938433602100d808233402098d008094009da50007693401f99323663408598cd086604019980d007c64201e99040786408d90cd216432821900d066402801d98f0074634b580cd1d6003401d18d007094c01ca52206c9407db24d1b6a64cada1902a6863455a8d3266834095a0cd026a04c2da0100a6803401c310806ec3d7db2509c6c64259b0d0836c04219b2530b5c94029724d1b6864c7189901b6263401b0d3125c3404570cd156804c59881015620340168071b60634016007006cc42457250806a6421da0d08e563280570108056010693bd15568c428d530e556294201a190956663201998c406463055818a485662819518840623420180cda1563340178ca005c0420148025a4cc39016a4dd94c92d89618de25663685618ae15662a85418847583371d58cd865832b1958ca865031505600dc15603601600ac05602a01400255546404d518d02543400150cd015494e015250815234e0148d08050328353a530c4e9400d3993024e640093b13804e64e01318d1a1d251bcfbd3a72af459c8bd13034c4ebcd253833e64e9d1990804664100e990274a63e01298f404863c09118d5d3063401118a5b3062800a988402262058d0d3ae4434284c0d0232e33484b8ca033404e9d1010863004020b80d062e028051b138046c4201030e014494e011250814264e010990802862058c8d395323420cc8138232042686bd1403ec43646b0e413c94304ea50803c93700ea4d803892d00da4b1c306426cc18d963034254c0cd833004208c00d9a18f4500d310d918c391cca50c73094218ca4dc630936189a4b472e64218b98d813234304c0d0803233700c0cd802631504b810802e03600b007042af4f04ab13c02ac430ca253822894200a24d962664e54999093266360c98d382263420098cd832404e0890108024036108b10c122943008a4dc3200430c7810822003708780d802002b00780a801cf4f046b13801ac421c62538618942046193801864200580c8014030681bd14412c43641b0e4112943004a4dd70692d0c4190c30e64208418dc20e63600418ac00e62a00298840086205830d0950c3364c30ca830c04208300d800c02a401b10cd06943301a4dc30664308198dc00662b680b0e6904937640a4b68046379c118ad7026219010cde30432b8410c7d30231524100dc80402b181007c004013000802400001f 14 0x3fff 5 0x1f 26 0x3ffffff 13 0x1fff 0x7f 20 5
theorem k5_64_t1BucketsValid : BucketsValid k5_64_t1Buckets :=
  dagBucketBlock_valid 0xbb06ea1ba04000b812d84b586d41b486d010002ce1b20ec420002c02af080000002b06aa12a04a612961000284900000009f8e7459a1a6429712506000232f8a1616900020e483060a100020810001fa77b1c0007911e210001c8d0001bc6000000068b59e2641d6f152c94240001385000000000000004c100004a8c0000000f1d3630baf25c878f19a45490b5020600bc001 0x1eae62802b8ca00ae31842898d0ea231c16880d00a20106a8a4d0ba46346288ca06a431c1ab0ca06aa31c1aa0ca06a631c02b00d00aa02a02a00a40a602802918c1ea06284e80ca00a002802898c00a03280a798d009e6288e60cd219832822600d06980288e58ca219631c22580a069601c8e50cd219432822500d06940288e48ca219231c22480a069201c0279902b9a640aa698d1b9c6289a68d0259a3345670ca0b9a0402a680d029c0283e20cd0e88328022004009c93c42118d0e8431c16100d0084010026a4f1a849342221900b8a6346210ca068a31c026190068e33402598d809463502498d068c328862250248a9349e299000906342218c70f860346a030e678a9369e0a4b638a6368e0988468a3368e38c6868e3191a30c6068231502280da78e026023809408c0240208026c866341210c70f8603452100a008a01c862190228663486198a06883401e18cd0686328022010018603402180a008893602198d938433602100d808233402098d008094009da50007693401f99323663408598cd086604019980d007c64201e99040786408d90cd216432821900d066402801d98f0074634b580cd1d6003401d18d007094c01ca52206c9407db24d1b6a64cada1902a6863455a8d3266834095a0cd026a04c2da0100a6803401c310806ec3d7db2509c6c64259b0d0836c04219b2530b5c94029724d1b6864c7189901b6263401b0d3125c3404570cd156804c59881015620340168071b60634016007006cc42457250806a6421da0d08e563280570108056010693bd15568c428d530e556294201a190956663201998c406463055818a485662819518840623420180cda1563340178ca005c0420148025a4cc39016a4dd94c92d89618de25663685618ae15662a85418847583371d58cd865832b1958ca865031505600dc15603601600ac05602a01400255546404d518d02543400150cd015494e015250815234e0148d08050328353a530c4e9400d3993024e640093b13804e64e01318d1a1d251bcfbd3a72af459c8bd13034c4ebcd253833e64e9d1990804664100e990274a63e01298f404863c09118d5d3063401118a5b3062800a988402262058d0d3ae4434284c0d0232e33484b8ca033404e9d1010863004020b80d062e028051b138046c4201030e014494e011250814264e010990802862058c8d395323420cc8138232042686bd1403ec43646b0e413c94304ea50803c93700ea4d803892d00da4b1c306426cc18d963034254c0cd833004208c00d9a18f4500d310d918c391cca50c73094218ca4dc630936189a4b472e64218b98d813234304c0d0803233700c0cd802631504b810802e03600b007042af4f04ab13c02ac430ca253822894200a24d962664e54999093266360c98d382263420098cd832404e0890108024036108b10c122943008a4dc3200430c7810822003708780d802002b00780a801cf4f046b13801ac421c62538618942046193801864200580c8014030681bd14412c43641b0e4112943004a4dd70692d0c4190c30e64208418dc20e63600418ac00e62a00298840086205830d0950c3364c30ca830c04208300d800c02a401b10cd06943301a4dc30664308198dc00662b680b0e6904937640a4b68046379c118ad7026219010cde30432b8410c7d30231524100dc80402b181007c004013000802400001f 14 0x3fff 5 0x1f 26 0x3ffffff 13 0x1fff 0x7f 20 5
noncomputable def k5_64_t1Tags:=fDagTraceTags k5_64_t1Mask 33 (dagTagBases1 k5_64_t1Stock 0xb02685842688eb2865e08eaa051f0d287424d003f 0x4a6680000040aa00000208a83080012843110001d 33) 10 k5_64_t1Data
noncomputable def k5_64_t1States:=fDagTrace k5_64_t1Mask k5_64_t1Stock 10 1 k5_64_t1Data
noncomputable def k5_64_t1Light:=fDagTraceLight k5_64_t1Mask k5_64_t1Stock 10 1 k5_64_t1Data
def k5_64_t1Gens : List WordMove:=[[s64_01],[s64_02],[s64_03],[s64_04],[s64_12],[s64_13],[s64_14],[s64_23],[s64_24],[s64_34]]
def k5_64_t1MovesFn : DagMovesFn1 :=
  fPackedMovesFn k5_64_t1Gens 0x4213985180ea2c0008cbb040061412a2e5d8a04b0b0051410c0e5d424c304075061280c01014bb1c0852612c6c01494c20c0741730c701d4984a0b004141300c01c10048200002000c402550042a00964000a42611803a20086412eac2619803aa00944000840020804ba00984000e4002480000 49 19 0x7ffff 4 0xf
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_64_t1GensOK : ∀ m ∈ k5_64_t1Gens,MoveAutoOK k5_64_t1Mask k5_64_t1Goal 64 m:=by
  simp only [k5_64_t1Gens,List.mem_cons,List.not_mem_nil,or_false]
  intro m hm;rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 1) (inv:=fSwapBits 0 1) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 2) (inv:=fSwapBits 0 2) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 3) (inv:=fSwapBits 0 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 4) (inv:=fSwapBits 0 4) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 2) (inv:=fSwapBits 1 2) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 3) (inv:=fSwapBits 1 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 4) (inv:=fSwapBits 1 4) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 2 3) (inv:=fSwapBits 2 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 2 4) (inv:=fSwapBits 2 4) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 3 4) (inv:=fSwapBits 3 4) (by decide +kernel)
theorem k5_64_t1Autos : DagMovesFnOK1 k5_64_t1Mask k5_64_t1Goal 64 k5_64_t1MovesFn :=
  dagMovesFnOK1OfPackedGens (by unfold Masked;decide +kernel) (by unfold Masked;decide +kernel) k5_64_t1GensOK
def k5_64_t1Cuts : List ExactBound:=[k4_0_5Fact,k4_1_5Fact,k4_2_5Fact,k4_3_5Fact,k4_4_5Fact]
theorem k5_64_t1Known : ExactKnown k5_64_t1Cuts:=extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (show ExactKnown [] from fun _ h=>False.elim (List.not_mem_nil h)) k4_64_t0Lower k4_64_t1Lower) k4_3_5_t0Lower k4_3_5_t1Lower) k4_2_5_t0Lower k4_2_5_t1Lower) k4_1_5_t0Lower k4_1_5_t1Lower) k4_0_5_t0Lower k4_0_5_t1Lower
noncomputable def k5_64_t1Check:=fDagCheckNode 2 64 6 false k5_64_t1Mask k5_64_t1Goal k5_64_t1Chart (fExactKnownCloses true k5_64_t1Goal k5_64_t1Cuts) 88 k5_64_t1Data k5_64_t1States k5_64_t1Light k5_64_t1MovesFn k5_64_t1Buckets k5_64_t1Sample k5_64_t1Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_64_t1Roots : fDagCheckRoots 2 false k5_64_t1Mask k5_64_t1Goal k5_64_t1Chart (fExactKnownCloses true k5_64_t1Goal k5_64_t1Cuts) k5_64_t1Wit 88 k5_64_t1Data k5_64_t1Light k5_64_t1MovesFn k5_64_t1Buckets k5_64_t1Stock 10 1=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_64_t1B0 : treeBlock 0 88 k5_64_t1Check=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_64_t1Lower : ExactLower k5_64_t1Mask k5_64_t1Stock k5_64_t1Goal 1 11:=by
  apply exactLowerDagFast (maxK:=2) (stride:=64) (steps:=6)
    (is24:=false) (allowNotInPast:=true) (width:=64)
    (sample:=k5_64_t1Sample) (tags:=k5_64_t1Tags)
    (by decide) (sampleValidOfCheck (by decide +kernel)) (fun h=>Bool.noConfusion h) (by decide) _ _ _ k5_64_t1Autos k5_64_t1BucketsValid _ _ _ k5_64_t1Known _ _ k5_64_t1Roots k5_64_t1B0
  · unfold Masked;decide +kernel
  · unfold Masked;decide +kernel
  · exact chartOfCheck (chart:=k5_64_t1Chart) (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold k5_64_t1Stock;decide +kernel
  · decide +kernel
  · simp only [k5_64_t1Cuts,List.mem_cons,List.not_mem_nil,or_false];intro b h;rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · simp only [k5_64_t1Cuts,List.mem_cons,List.not_mem_nil,or_false];intro b h;rcases h with rfl | rfl | rfl | rfl | rfl <;> exact stockMaskedOfCheck (by decide +kernel)
def k5_5Fact : ExactBound:=(k5_64_t0Mask,k5_64_t0Stock,10,11,k5_64_t0Goal)
def k5_0Mask : Word:=0x5555555555555555
def k5_0Goal : Word:=0x5555555455545440
def k5_0Stock : List Word:=[0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]
def k5_0Fact : ExactBound:=(k5_0Mask,k5_0Stock,10,11,k5_0Goal)
def k5_0Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [1,2,3,4,5,0] 0 i.val)
def k5_0Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [5,0,1,2,3,4] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_0_t0Lower : ExactLower k5_0Mask k5_0Stock k5_0Goal 0 10 :=
  exactLowerRelabel k5_0Sel k5_0Inv (by decide +kernel) k5_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_0_t1Lower : ExactLower k5_0Mask k5_0Stock k5_0Goal 1 11 :=
  exactLowerRelabel k5_0Sel k5_0Inv (by decide +kernel) k5_64_t1Lower
def k5_1Mask : Word:=0x3333333333333333
def k5_1Goal : Word:=0x3333333233323220
def k5_1Stock : List Word:=[0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]
def k5_1Fact : ExactBound:=(k5_1Mask,k5_1Stock,10,11,k5_1Goal)
def k5_1Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,2,3,4,5,1] 0 i.val)
def k5_1Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,5,1,2,3,4] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_1_t0Lower : ExactLower k5_1Mask k5_1Stock k5_1Goal 0 10 :=
  exactLowerRelabel k5_1Sel k5_1Inv (by decide +kernel) k5_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_1_t1Lower : ExactLower k5_1Mask k5_1Stock k5_1Goal 1 11 :=
  exactLowerRelabel k5_1Sel k5_1Inv (by decide +kernel) k5_64_t1Lower
def k5_2Mask : Word:=0xf0f0f0f0f0f0f0f
def k5_2Goal : Word:=0xf0f0f0e0f0e0e08
def k5_2Stock : List Word:=[0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000]
def k5_2Fact : ExactBound:=(k5_2Mask,k5_2Stock,10,11,k5_2Goal)
def k5_2Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,3,4,5,2] 0 i.val)
def k5_2Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,5,2,3,4] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_2_t0Lower : ExactLower k5_2Mask k5_2Stock k5_2Goal 0 10 :=
  exactLowerRelabel k5_2Sel k5_2Inv (by decide +kernel) k5_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_2_t1Lower : ExactLower k5_2Mask k5_2Stock k5_2Goal 1 11 :=
  exactLowerRelabel k5_2Sel k5_2Inv (by decide +kernel) k5_64_t1Lower
def k5_3Mask : Word:=0xff00ff00ff00ff
def k5_3Goal : Word:=0xff00fe00fe00e8
def k5_3Stock : List Word:=[0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]
def k5_3Fact : ExactBound:=(k5_3Mask,k5_3Stock,10,11,k5_3Goal)
def k5_3Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,2,4,5,3] 0 i.val)
def k5_3Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,2,5,3,4] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_3_t0Lower : ExactLower k5_3Mask k5_3Stock k5_3Goal 0 10 :=
  exactLowerRelabel k5_3Sel k5_3Inv (by decide +kernel) k5_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_3_t1Lower : ExactLower k5_3Mask k5_3Stock k5_3Goal 1 11 :=
  exactLowerRelabel k5_3Sel k5_3Inv (by decide +kernel) k5_64_t1Lower
def k5_4Mask : Word:=0xffff0000ffff
def k5_4Goal : Word:=0xfffe0000fee8
def k5_4Stock : List Word:=[0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000]
def k5_4Fact : ExactBound:=(k5_4Mask,k5_4Stock,10,11,k5_4Goal)
def k5_4Sel (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,2,3,5,4] 0 i.val)
def k5_4Inv (i : Fin 64) : Fin 64:=Fin.ofNat 64 (permuteAxes [0,1,2,3,5,4] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_4_t0Lower : ExactLower k5_4Mask k5_4Stock k5_4Goal 0 10 :=
  exactLowerRelabel k5_4Sel k5_4Inv (by decide +kernel) k5_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k5_4_t1Lower : ExactLower k5_4Mask k5_4Stock k5_4Goal 1 11 :=
  exactLowerRelabel k5_4Sel k5_4Inv (by decide +kernel) k5_64_t1Lower
def k6_64_t0Mask : Word:=0xffffffffffffffff
def k6_64_t0Goal : Word:=0xfffffffefffefee8
def k6_64_t0Stock : List Word:=[0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def k6_64_t0Chart : Option RowChart:=some ⟨[3,5,6,9,10,12,17,18,20,24,33,34,1,2,4,8,16,32,1,1,1,1,1,1],rfl⟩
def k6_64_t0Wit : List Witness:=[(0xaaaaaaaaaaaaaaaa,3,2),(0xcccccccccccccccc,3,1),(0xf0f0f0f0f0f0f0f0,5,1),(0xff00ff00ff00ff00,9,1),(0xffff0000ffff0000,17,1),(0xffffffff00000000,33,1)]
def k6_64_t0Sample : DagSample1:=(0x109004300108408110206010060409002280105004180405020240800c20051006004280802802181000c020c0103040210802440220088804050401402140400c022402018020a0804820111009010090101840280200c403008050100c02030041208060081401088100a080c010280406008240102802090084408050088402050100c0203,60)
def k6_64_t0Data : Forest:=fun i =>
  match Nat.shiftRight i 8 with
  | 0=>fDecodeNode 8 21 0x4a744990a2468512042893264418d2212910e64c871a642a5021129906f54817a640b16201898fc94c7e3263f2531f5280f434c79620bc3101e0682f0c41766203b2501d8082ec629754a0388d09bd298dcc4c6a4a6353d31a5898d264c694a13419019de9cccc4e664a73325059927ccc935661a733313194098ca01c65008b0a50980c84c063260314b0004d80698be9405d1a62d3d395d89cae94e571a72b8d095d280ac94e553272a98d15409caa9355362128a5094406ea2634501a1278ca13d8c09d2584d632259931258a88ec4c464ac22c968f98b47cc493e6209f2568f929c7c65a3e0271f3d3cf589c7ac433d3219e80d8f52a8786583c4ac1d1938cd2b0646583102d18c968b5eb45a65a2d325169904b4c805a3402d4ac164968a5eb452c5a294ad14a538a4c9c5204e296261431689d2b44e9402732d138d60998824a34e221ad10c96881eb440c5a2062510310480cb44093e1f3210fbd3878c9c3c94f1d4a70ea50c74c9c3a6421d0218eb10871284383431c1a10e0c74718863602b1b92d0d3d6868cb43435a1a1a00d0cd8686503405a1a6270c8cac6409c3202a1900e0cbd3c61e9c3094e180218c010861e9e2ec43176210ba5085c6862e042176218b25085926e2c6361601b8b00d85aacc26c661362d09b1544d2b42665a13933093d68498b42525b107a788253c400842125b0f4a787a5383cc9c1e6340f92d072538392921c04e0e7a706b1383529c1af4f0c621863108324b61725a0b62d058d3c2c69c1604e0b92d853d3c29e9c14c4e0a4a7850d3829e9e12c4e0962184990c24c8412f4f0832184190820c6e103420819b040ca020086100420849b8380ac1c0540f25b06321833d3c158860ac42054a102990815886089370449b02310c0c66e063360301b0180700d26e0462b023150100a8080260203f00 (Nat.land i 255)
  | 1=>fDecodeNode 9 21 0x9309849a486502372991a0408b82145a5221268101040809a0400cd1fa068fdc407d99a38f121b1880d89406c4a635a501a9280d164068c9e3399019cc80cdc40624a031250181884bf6425f81b2fcd017c650be9365b815adf161658a8aff4c5762c2b413156c80a864c538272981014d284a302851b20279901386989c3404e1a626cd3135ea899f4c4cb2c2631392a69c953324ab26247d3120c808d340469a622f13115e9c89 (Nat.land i 255)
  | _=>(0,0)
def k6_64_t0Buckets : DagBuckets1:=fun parent k =>
  match Nat.shiftRight parent 7 with
  | 0=>dagBucketBlock 0x9b624d7126a0600009a60cd10a6785328599014bf265e852ec29740cb80a5a872d0195454955645952203904347e123c0d1d048e60c682e320917c58b81c58122b05140689c143d4616a10a4484a241c240000000081e6c0e06038effc87fc080001fb10fd417e41be439ec96f5447945bc125dd0e000076e1bb605d39ee74a7380b8d3dbf1edf026f4136a41ac24d38a00003471da18800006801800019e0800006721b2d318c2ac0185f042f2196fa6b40f59e0acc0d5da2adc45585a9f354d88a603528228d1d39b498914ae5a4a351a2c894f4249a0438fc96769f39289bb38c95260122c2f95434a4184c962409107647d983d071a708c04c58202657108a86384272a0f1204cb01058009e0001 0x7698d0c78cc5001c633413d41940078b13003c129801de64c13d018e007725307730c68279831c00d61940076a5004f286382bd6f4c00ec1a60075b10403a98802bce94000e91a09d5b8d00e2e4638837203400e162600743104039d88001cc94051ce3140bee8d047b3868001ca04125ba014007218a506e0050a39493419b918e0aed8c74038c66a63c431d00e34a029ed993003886383b9633416db6270aedb109536d29ca7b694232e232718f11908078869c01c434201cf027006781097b6529a01c294c5fd84a0afe725017b6126abd9c9344fd9326a86c19054338c809fb06354fce31a09ec8d345360682299c34013d819a89e70cd0036409a03b004101ce020006c00d4033806803acc4e00d66212fe525397b29284a19464e4fca3210a650d384f28684039404e00ca02118ef2530037869801b232831e062618eea5300380c9801ba34c00d819400690130038189801be94c11d332600698c700379e9801bac4c35d34a6006b99600370c9801a204c00db4a12f659900c76863a337031c00da320006cbd38036189c01ae94e00d64a0806aa4f8035126abd9693431d332700698d38034009c019402a00d262618e89930034409801a001c76b732605db8c710adc098616e02800ce00e395c990096e4080019401c42b74a600668d31cae8650336e01072b819a006780440339284019a64200cc319006598a506d8c5001940132ec932600648d313b18c829d766404dc631aa6dd98d13318c52997662816c61a08b5d8d00571866a2b7633413c619489dd8ca00f18082058c03502bb01a006300a402ec05001909404cc4326a76299053ae8c809b8a6294dba31409e20d345b146822d7434015c51948add0ca0031009a078a04103ba020016280a40ae80509b726344cb93140adc8cd04ee46509b843294cc218e8ae100a44f0803a0b88c4c00c64ac00e2a53003152805d8e64c00c71a6016001600efc098057e04000c67a70062b138031129c5d8664e2ec2321176098d536e0c68018634e00c21a100608cd456e0668037e04e00be01a0060a5000b01e9c057ec4e00c04a7005f993802f8c685d7a34e00bd027005e250002ecc98037464000ba31a275b8d0136dc6682d6e04015b701a005e24d402ed88401749422eb919b975c0ca4bad8650017203700b8014805b00a002e0c682b6e94200b71a1005b0ca002d58c00168c5881984ac404c2531fa61280135c65808ae326035719015a006b0ab0034c53801a00f4001607600098390004000b492c464d3d6226698b101349407e9a49a045699001ab4c68ab04340538219a0ec101007208068aaf4340537a19a0ebd010071e80680562f5800b17a60059b192025d2b0fd2e94c08ac32c0356193155fc6b0a6fe34c1d7f02c0e3f813002c8c98115264006a931a47d48d3155f8680a6fc3346aa90260ebf010071f8068016464c80963203f4b18d155e4680a6f23341d790200e3c80d002c58a80160c4c08ab326005831323675eb0fd30c649a8362c4cc1b13002bd2b0055a66403aa32c015519300298c68671e36458811ac2bc08d30223c0c841020581f81026015499300290c68671c358338d1a647538d01cdc0668111c058088d02632d3810101c00680146634098e7ad04473d399a9d8b4cb4ec4e7f8c4ad3f462539ee38cb4f51c64e03a71ad01538d380288650691805a338c0272f5100d13db80501550f5806ae63245ccb1622a65898235095800ae33241cc99620a64c98014c63433871b22c3e8d615df4698110e064207d02c0fbe81301aad898014663484954a03d4a98a002ba4b50532f5a00ad62d0056312402ad883012ac4000aa4ad0054a53a0251280015065a34891ad17538d39d1c4680131205a00a702720b881000299e9e0348c4f00a56270052310c1e8d29eff2a94e06a34a1bf4aa508068cc9ef72a64e00a3321bd4a9908d22069c67103422ea219b04c401382220084014403600a14aa445025300280cb07b0c64c3c863201dc318d0ce18680630c3340886020034300d0027d2b0cef864c657c3202abe0d314df06803af804c1c7c02033b78cd195bc650aade034536f01433bd990155ec6803af6040099e626044f310236712990f3864c089e627034f25380278c9c013a958139a3321ec199604e64c98cef0640657831a004d0190d20c0b0013204c557802029bc00d001780382d2494d71844a60ac92505c21128027249356f8449a09cd99680270cb0d0ee64c677732032bb98d00e4869a05243416c841a000490cd5ae10668013605a56770262abb81014ddc06800ba01c885c62609c825645a4529a88c294c159149aa1b0a4d27644cb4dac265868753264e489909b984c80ceea63400901ac81c88d352d8469805223354a6119a48c8816965840b0acea04c90910212d30810155d406800b801c1d624a00e3124d04e58c9878ec6403b7631a19b98100c5cc06800b601c158e31a89c718a44e54680cee43346572194002d0040026a4b40132f5a929162d4848a5680260cb4012e64a0096320804a99005634c6a3ac0634138d3148e3018a05a0c6b498b434c00941a01e3a0cd0edd06500518035008c01482c83d6002498c80322c5800916260049a5605600cc87ef06583e7832601450d900e246b0051234c33690321a340160cda009800b201c005800e1e391900edc8c6800ae01c009292d0048bd6802418b4011e95a008e4a70045a5050d812802d0265a008d3271db799319dd0c80031235a00881a001b50168023009c66ce040005600e0045b130ed98c6866cc04c005500e014549680a25eb40114c5a00894ad00442500021ccb42cfa35a3c711a01db88ca00d900b400a8010008562635c22561258529890c29400e8432606c2190002186b07eee34c3e771a012298ca0d18409866c204000530080042b104994868048a432800520080abd8d00914465000a201048604a012278ca0cd80080009e0100d8462714c219389d38c68010834e244e18e06a700d001380206304c593281626ae30b130c605882b6c2c4031834ad29bba56151d5298a6ea940008232c80c099348184c9801026411f613200ca998a0020c6b42aee35816751a60aba8d01314c66800da328006b02c80b50134058c09800d40410063020004149680205eb40100c5a007a626803fb12801f988266dec4032784ad18b925314dd128000fa65a007931b18b898a061a06b400e03365d4f19a09b28ca07d8589c00f893e0d6f49a9ca724d0c9dcc9c00f66421d5f31a0c308d3801bc6546e9c328135f18e00bd3d6801e9e9c64f2c5a31796272a39a5694dcd29c02f265a00793270b398d6855cc69c00d8328016202d0031013855e1e9e2aeef4e1575627003c253c01dd29c00ec94315724a10039250455d126aa2be9340075327003a1909797cc802ed034f17611a70ab98cac559c63a32a031c01680278039810c019c06a4aa003401726270039310805c529c00e2942546732729b3990805c069e02de34e00701a180378d0801b863a02cc04f01600270033010c018008400dac435f654a1afafa509799526ebcbe9365065321a82f99093d94c6e9ebe63614651a18a2f8d084d9466e26be336006c18f80b2810c057c08400ca037005f01b003600ac01ae4b400d4f5a316962d18b42568c59d28000d265a31663148ca798a001a06b400ce340006619b26278cd0019465000c805a006362718b09939c940c6800c432b316018e85a70c70018409c4aa00340060015182700a0017c03800bcf4f005d7a7012e3138017129c9cb264f4e53327262d990d3168c8498ae6414d5631aa6a818d13158c5298a062816591a78b298d384d6c68626b434213571a08aab0cd4554066826ac329135019401ac813c0d4c09c00b6043005a021002b8104095806a04a00340056014802800a00165e9e02b0c4f0157627002c310c015d88402ac94e00564a117aa993d393cc9c5caa6434d4f32100aa8d3c593c69c00aa343154f1a100aa0138015008400a6c4301514a180292508014526e02a0642005031b17a78d0cbd386845c9e3372e4e19b00a7810c0538084009e037004e01b3d263d964cd1ec92888f5998257ac49a23d365c95e993c88c6699256324d1031626481899368896695254b24b102562548129810986650f34332082219651894cb01e8864d4525326001a19001910c6a804a63400443149d9298a1e5106ccae4a36458201ac2b900d31dd10684984a3404f2019a26100ca191100cc3e4a064202002c0f9001317910084264a040192001a099000a0252e4cc109725a7b487b33d243d69fcb98ccfc5cc5a7b2e4b33d1725682520ccc109065a342e1b319970d693c74668983a328092e033041701686474068263a028004dab34518c99a20c5ecc0098c66004b62d3d1d316001298aa048cc4d802d62600233105f8b5880068896600494ad3d1c256200b1298fc5894003403330024196818f8cb0107a64c063d3201a158d99e10c6b4a644358551f1a6298f8d0024ac0ccc48605a1c2202c0e8f8130707c080008f26601467b300233d6805158cc008ac5a03424b3012125680cfcccc047e65a342a1b319950d6824a80cc105405a7b3a7ad3d1d3d39fcb58b4fc5ac4e7b2d4ad3d16a5380cf8cb4047c64e34291ad19948d3824a40b4105204e004492d80a1bd6dece1eb40086f4f7a387a73f963169f8b189c028495b7d2d4ad0021253df0b529c067a65a023d327001e18d0d0a06b4665034e2e411a1398d8cd024a00b4105004e0041021200d80d001024b60e7ef5b073e7ad031fbd3c18f9e9c0e7ac5a063d627009fa56c04f92b4007e94f003e4a7009e996800f4c9c007863434261ad19930d3824980b4104c04e003b92d45183d6a20c18b4066895a003a4a7001ba53400c9298007294902364a0801b24d4f494cb46c7064e3b21326338f19019478c68684a35a2e381a718908d315478680a63c334092502d001c013818840983a3c0401c1e01a009bbd6800dde9c026cc5a0036627009aa56800d529c7a4665a3c233271a118d68cc8c69c124605a0823027001a3d3c04cd89e0264c4e0033621801931091c9129c7e4864e003192d8018496808bdeb4005ec5a162b4ad8b12a5684cb929e265a94e13294a68a942504746128026509351c1849a0b1019684cb0c9c763c64c3c1c3201d8e18d00cac6b6064a35a002e1a780168d3800a469a04503412c181a000140cd4a860668064005a002c027188f0130cc700806238034001700e0015c96c04a9eb60252f5a002a7a78014bd3804a18b40050c4e01274ad8b112568009d29e2a4494e161f32d0a8f9938ec6cc68024c35a00261a7018c8168086409c002c01c00257a78091b13c009189c0046c432b184a7150c25080488c9e024264e002232180109908587869c2a3c3422415194018c01380860084002a01000207a7990fb13cc87989c623ec43311e621190e2538c471284023e64f011e327000f990c0078c84003a637311b3148c8a98a0047069c0038342001b19b260a8cd00068650023204f0118027000c810c0060084082ec4301174a1800ba4dd3858c869c2a6424d1631ba68a98d93058c56982a62a16161a18b0a8d08545866e2a2a3361316195898a8ca80c58086062a042021601b810a80d80058056002a02a001492dbd893d6dec35eb4f424f4f7a0d7a73f853169f82989cf61495a7a0a4a70489196c2434cb4102464f080d3270009990d7840c840020641000b320030798d50020c68001e6293b083141a050d68cc2869cee1e3424c081a027838cd1301c650121405a080a0272f0781084c20080320e03413070140209496c0449eb60024f4f031162d81883168084589e0420c4e0011621800831080c3d2b4041e94e000f4a1018719680838c9c001c64234091ad19848d38c424684121205a0809027030481081035e9e021ac4f000d6218186253c0c2d29c0418943020b4a1000624dc002d26c7a1064e3c083211d8418d8d02069c6610342310819b0484013820200840c10036040a7a78085313c00298862c1294f16084a70a84a50c54212842612937130849b0b039938541cc84260e63603091a781840d3808246860410342000919b80040cd80c1c09c040e042000701b000300703c15e9e180ac4f0b056218182a53c0815286000a9370904327848199382010c861006642060431b830198d80010c56000662a34021a719810d08c40866c5c0432a090202704010108180806c000402a6401621b180a50d880526ec202643600131baf0098ad4804686a2023374f01195a6008c7c6c04086340203719010158980807c0004026000003f 17 0x1ffff 6 0x3f 29 0x1fffffff 13 0x1fff 0xff 21 6 (Nat.land parent 127) k
  | 1=>dagBucketBlock 0xa59524a8c7442a09cfca7c33d100000027640000004e840000009c14dc4000000000000000000000000000013619a8cd06662000990cc440000000004c0658928400049c64c3251920c8c6424000900c78a3a20008e080000011938aa44522030d386080021450557f3becc000f920003e04000f717a93a71c6cd9a6aa3504000d0465331cd8a40005fb2ed1724b4555ca91d3cc00049da31d1088260001ea0ec87333819b4cd286720001948b7455627b12588c64151ea0e8c68c33117a0a1c3d41950aa04c82060e205981d004a002 0x135034009100817488100026806801353342e91020004d00d0026729801210100099e2008c801000240020552a634029501a014a40a0363e038313134c139899409cb0c707650c50272831c398f18e004c8c7002646680129028009698e004c1900025ec8001309400097ca018cb5900025a680012c0400098e24004c3100025f280012b04000974a620c780a0025b280012c01c00959a6004b25000256c800129640009549e004a59000250c80831e6340093b26004998d00a420685d2764000939a000c9010002480685d2664000931a00148c130064a08001230280093e200049a500024005001220280591ca00048d8a00e47880012494c0092ca017484d0002420800124c420291ca10048d908ba406845d223360090021004880d80a43280012134000901941747cca0023e0505d1e328008fb200047e4d8023c057030c95880864a63f4325002638cb0111c64c068e3202b3d0d6155e8698a6f43401e7a02c0ebd013071e8080111b640068db1a2abccd014de66683af30401c7981a01477130023b881010a94c7e854a0044699301a34c80aaf234c53791a00ebc813071e4080aaed33453769940ebb40d071da050011dc58128bb200045d8a0ce0c6801106040008e62a0046f132161129909089405c781a610bc01300237e990d09c4c8484c9a0046b162120f2990b08f4c808462c41437130462ec985d1934c008c82617460d01d1c66680118040417181a08c5d9320212c690104934008c3204040d8d18228080a2e203487896260345e530022ec9866fa35858789a62bbc4d0021f40b040f104c1f7882043c4b104ba2c69c5d15340338019b00458138022a0801100036337f1a619bf4d00ba2866810fe04c087e820004500d025fd89c10fec42018a4a700452509fe08c9cfd046427b821a73d410d08d1f809c66fc04200898141ebe5930f1f2c8076f9634337c9a018be4cd021f20800cf9034337c19a18be0ca021f00680cf8028677732032bb98d155dc680a6ee3341d770200e3b80d00224c80ceec63465763140042c160461008066eb03431758140032407009f066800f8328027081a003840a00222c80011034c00879a00042d930021c6980109340118432609c24d60021a698010cf540085fa608c231300210668010a65800839a0014100a4020803a2709f4e0084e275040653a7e02c9c010834e00839990ac0cca44e0663a0503029008180e8041656285ed28004fb340026f82c0934c100018e038010594c6975b2600c00d300200680b0e904c006300e50bda531a5d0c9804ff35801809a61a374130018a038010664c007f99a00310070020be9942f6c4c007d19a08b0c130018603800fe334008202019b6c0d0018403800fd3342e610260040c1000208c803acf6342e611a60040cd00f1c866800fc034006080e02bff13001ff268010234c006000801bffd3002018b00101c4c007db260c3bcd30d5a209800bf01000807a7013ff13801ff29c00fa64e007f3210b3c4d3801fa68406d204e007e021002f804009f789800fb64c007d31a08af4130017a02000f9948007c326153358d0099a06848bc328005e008003dcd30b56e65034b7028007b4a03aba190001e789800f594c136c9942a3a253001e2c982ce534c136c194003d3d5001e7e9800f064c186b9a609b5cca001e58b026d5328 13 0x1fff 4 0xf 29 0x1fffffff 12 0xfff 0x1ff 21 4 (Nat.land parent 127) k
  | 2=>dagBucketBlock 0xbc6e100000002d1002c1002b1000000000000000002a100000a0800002719840000000908008c621845f2749a360908000000000000000388000000034400304a2244811c46109002 0x2e9f01a174f80d0027c020013f940009fc98004f80a0ba7c668013e034009f320004fa4d216732990939940009eca0004f253146640506736334089b01a004ec100ba740681133935009d02119cdc0a8ce6a0806734034349aca119cd64d8266ac841135636239a9a1114d4cd8a26a0844f35036119ce26004e4cd002732900136328009999a0049c070026a0500134028009b314004940400266c800138340009b82000490040026c6800123010 10 0x3ff 4 0xf 29 0x1fffffff 12 0xfff 0x1ff 21 4 (Nat.land parent 127) k
  | _=>k (fun _=>none)
theorem k6_64_t0BucketsValid : BucketsValid k6_64_t0Buckets:=by
  intro parent k h
  unfold k6_64_t0Buckets at h
  split at h <;> first | exact dagBucketBlock_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h | exact ⟨fun _=>none,h⟩
noncomputable def k6_64_t0Tags:=fDagTraceTags k6_64_t0Mask 60 (dagTagBases1 k6_64_t0Stock 0xe31105842502d0858e24010c19ca200943da0114696c086b4187628e41140408a18b8a13083300c2668520007f 0x225002500000001c8200c088800062000281041600180000020224110e0c10840081208201005095000006d 60) 12 k6_64_t0Data
noncomputable def k6_64_t0States:=fDagTrace k6_64_t0Mask k6_64_t0Stock 12 0 k6_64_t0Data
noncomputable def k6_64_t0Light:=fDagTraceLight k6_64_t0Mask k6_64_t0Stock 12 0 k6_64_t0Data
def k6_64_t0Gens : List WordMove:=[[s64_01],[s64_02],[s64_03],[s64_04],[s64_05],[s64_12],[s64_13],[s64_14],[s64_15],[s64_23],[s64_24],[s64_25],[s64_34],[s64_35],[s64_45]]
def k6_64_t0MovesFn : DagMovesFn1 :=
  fPackedMovesFn k6_64_t0Gens 0x3a60e075b1cecb72a01306c32a0a76db9500083401904c3b5ca0752a400b536193033b65c6f65b0d0da618016c6fb6a0a865b940ca728192c30365d2764c1deda64a196c703aa0a005b9300d7461d90703b59200631b0da549d96a77b6552864a9c0eb528014a4c3a606004b8bedb61a194c33b2e0e8053930096161d9270002c900061a000022192e13b2d9286d31ced972a01ac2c3b18676d31d0d9728012e4c3b20600740b0007141dac300318586d41ced982a192e503b60600638b00e616000c2800004865c04eda70a1b2c13b2582f65c050da7081d7010029c1f6cb050c9609db7014329c2074b040096061daa10031418002820e9848012e6fb6d8a86531400b6261b5093b2dcef6cc250c97381d8e70031cd8003120db519d94a37b6d4686528c009517db7094329ce004b1300c516000a28036c1876d8400ca0601d20c00241000602000e040000040025d00003900ed660018c8032558075b3000a64001b080031d0000310edb580194ac032e18765c400da7601d70c0029d0064b30edb880194ec002590006aa00ec5601daac0031500072a0000520019680002c80765b000da4001d68000288076cb000c94001b6803b6d800652000e9400012400034800762000ed400018400038800000 162 23 0x7fffff 4 0xf
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6_64_t0GensOK : ∀ m ∈ k6_64_t0Gens,MoveAutoOK k6_64_t0Mask k6_64_t0Goal 64 m:=by
  simp only [k6_64_t0Gens,List.mem_cons,List.not_mem_nil,or_false]
  intro m hm;rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 1) (inv:=fSwapBits 0 1) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 2) (inv:=fSwapBits 0 2) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 3) (inv:=fSwapBits 0 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 4) (inv:=fSwapBits 0 4) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 5) (inv:=fSwapBits 0 5) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 2) (inv:=fSwapBits 1 2) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 3) (inv:=fSwapBits 1 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 4) (inv:=fSwapBits 1 4) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 5) (inv:=fSwapBits 1 5) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 2 3) (inv:=fSwapBits 2 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 2 4) (inv:=fSwapBits 2 4) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 2 5) (inv:=fSwapBits 2 5) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 3 4) (inv:=fSwapBits 3 4) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 3 5) (inv:=fSwapBits 3 5) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 4 5) (inv:=fSwapBits 4 5) (by decide +kernel)
theorem k6_64_t0Autos : DagMovesFnOK1 k6_64_t0Mask k6_64_t0Goal 64 k6_64_t0MovesFn :=
  dagMovesFnOK1OfPackedGens (by unfold Masked;decide +kernel) (by unfold Masked;decide +kernel) k6_64_t0GensOK
def k6_64_t0Cuts : List ExactBound:=[k5_0Fact,k5_1Fact,k5_2Fact,k5_3Fact,k5_4Fact,k5_5Fact,k4_0_1Fact,k4_0_2Fact,k4_0_3Fact,k4_0_4Fact,k4_0_5Fact,k4_1_2Fact,k4_1_3Fact,k4_1_4Fact,k4_1_5Fact,k4_2_3Fact,k4_2_4Fact,k4_2_5Fact,k4_3_4Fact,k4_3_5Fact,k4_4_5Fact]
theorem k6_64_t0Known : ExactKnown k6_64_t0Cuts:=extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (show ExactKnown [] from fun _ h=>False.elim (List.not_mem_nil h)) k4_64_t0Lower k4_64_t1Lower) k4_3_5_t0Lower k4_3_5_t1Lower) k4_3_4_t0Lower k4_3_4_t1Lower) k4_2_5_t0Lower k4_2_5_t1Lower) k4_2_4_t0Lower k4_2_4_t1Lower) k4_2_3_t0Lower k4_2_3_t1Lower) k4_1_5_t0Lower k4_1_5_t1Lower) k4_1_4_t0Lower k4_1_4_t1Lower) k4_1_3_t0Lower k4_1_3_t1Lower) k4_1_2_t0Lower k4_1_2_t1Lower) k4_0_5_t0Lower k4_0_5_t1Lower) k4_0_4_t0Lower k4_0_4_t1Lower) k4_0_3_t0Lower k4_0_3_t1Lower) k4_0_2_t0Lower k4_0_2_t1Lower) k4_0_1_t0Lower k4_0_1_t1Lower) k5_64_t0Lower k5_64_t1Lower) k5_4_t0Lower k5_4_t1Lower) k5_3_t0Lower k5_3_t1Lower) k5_2_t0Lower k5_2_t1Lower) k5_1_t0Lower k5_1_t1Lower) k5_0_t0Lower k5_0_t1Lower
noncomputable def k6_64_t0Check:=fDagCheckNode 2 64 6 false k6_64_t0Mask k6_64_t0Goal k6_64_t0Chart (fExactKnownCloses false k6_64_t0Goal k6_64_t0Cuts) 320 k6_64_t0Data k6_64_t0States k6_64_t0Light k6_64_t0MovesFn k6_64_t0Buckets k6_64_t0Sample k6_64_t0Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6_64_t0Roots : fDagCheckRoots 2 false k6_64_t0Mask k6_64_t0Goal k6_64_t0Chart (fExactKnownCloses false k6_64_t0Goal k6_64_t0Cuts) k6_64_t0Wit 320 k6_64_t0Data k6_64_t0Light k6_64_t0MovesFn k6_64_t0Buckets k6_64_t0Stock 12 0=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6_64_t0B0 : treeBlock 0 256 k6_64_t0Check=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6_64_t0B256 : treeBlock 256 64 k6_64_t0Check=true:=by decide +kernel
theorem k6_64_t0Blocks : treeBlock 0 320 k6_64_t0Check=true:=(@treeBlock_merge 0 256 64 k6_64_t0Check k6_64_t0B0 k6_64_t0B256)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6_64_t0Lower : ExactLower k6_64_t0Mask k6_64_t0Stock k6_64_t0Goal 0 13:=by
  apply exactLowerDagFast (maxK:=2) (stride:=64) (steps:=6)
    (is24:=false) (allowNotInPast:=false) (width:=64)
    (sample:=k6_64_t0Sample) (tags:=k6_64_t0Tags)
    (by decide) (sampleValidOfCheck (by decide +kernel)) (fun h=>Bool.noConfusion h) (by decide) _ _ _ k6_64_t0Autos k6_64_t0BucketsValid _ _ _ k6_64_t0Known _ _ k6_64_t0Roots k6_64_t0Blocks
  · unfold Masked;decide +kernel
  · unfold Masked;decide +kernel
  · exact chartOfCheck (chart:=k6_64_t0Chart) (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold k6_64_t0Stock;decide +kernel
  · decide +kernel
  · simp only [k6_64_t0Cuts,List.mem_cons,List.not_mem_nil,or_false];intro b h;rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · simp only [k6_64_t0Cuts,List.mem_cons,List.not_mem_nil,or_false];intro b h;rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact stockMaskedOfCheck (by decide +kernel)
def k6_64_t1Mask : Word:=0xffffffffffffffff
def k6_64_t1Goal : Word:=0xfffffffefffefee8
def k6_64_t1Stock : List Word:=[0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def k6_64_t1Chart : Option RowChart:=some ⟨[3,5,6,9,10,12,17,18,20,24,33,34,1,2,4,8,16,32,1,1,1,1,1,1],rfl⟩
def k6_64_t1Wit : List Witness:=[(0xaaaaaaaaaaaaaaaa,3,2),(0xcccccccccccccccc,3,1),(0xf0f0f0f0f0f0f0f0,5,1),(0xff00ff00ff00ff00,9,1),(0xffff0000ffff0000,17,1),(0xffffffff00000000,33,1)]
def k6_64_t1Sample : DagSample1:=(0x40c0000301060041102060400610028020c0103004280204420060085002220086040180089020050802820091001410050800c200c01014020a1000c100304018402210084201210090402808044080308050403004024080604030201801018041202030100a080c010280406008140108808240102802090201402110088402050080c0403,60)
def k6_64_t1Data : Forest:=fun i =>
  match Nat.shiftRight i 8 with
  | 0=>fDecodeNode 7 20 0x327433214331a431a743621c231bc231b4219b4202a4092d3f0273f0253f024bf0243f62d3e4ad3e4a03e6273d3273d62d3c0273c92d3b62d3b0363a02a39ab3387b3387b33763337626377a735627350273502a3392d3202532024327a731027317a7b04a730021b0021303332fab32e9332e7b32e4b32e02a2e92d2d62d2d0252d62dac62d2c4ad2c4a72c4a02c32dac32d2c7a7ab321ab3212b92d2a62d2a3272a0272a7a7a962729621a94a12932129314297a7a8621a8621284a1281a128aaea6928a69282662d2562aa54ad2532d2592d247ad2462d24aaea4928a49282492da37a7a37a2a37a22392da27a7a24a7a20212292da14a7a14a7213272131a2192da07a7a07a720627204a720027a0027207a79f4a11f0219f0211f92d9e92d1e4a79e4a71e4a49e0271e92d9d7a79d7a71d6271d4a79d4a71d7a29d7a21d7a79c6219c6211c61c9c61c1c7a79b6219b6211b0219b0211b6219a01b9a01b1a92d9992d1962d191a7991a7190271992d987a7987a718627184a7981a7187a2987a2187a7976219762117321973211761c977a796321963211631b961a11619b1619416021960211649b950159501515ab39492d9492d1462d144a7141a714024147a79362193621134a1137a79262192621124a112321121a1121941292d917a7917a7114a7110211101e9162190ab38e92d0e7ad0e62d0e0250e0240e92d8d7a78d7a70d01f0d01e0d92d8c4a78c4a70c3270c31a0c6218b31b0b01b0b92d8a3218a7a78962189621094a1093210961c8961c096218849b8849b0849688496086218719b8719b0701b0700e076218649b0619b0649b85015057a7846218462104321040180449b83315833150301503310833100331582009810048101f80 (Nat.land i 255)
  | 1=>fDecodeNode 8 21 0x4b0472556352a91b2558b7ad45c9422d2b5149588a496453d6a24081129608892d4349561a4a10d25a854a4c2a5221409d0ac4c8462d41a56a0d281060108262740813a058b500c558002d404969fe4aafef5a7f62d3fc941fde9efcf4e7e7a4bf3d15f9e88fcf4e7d4ad3e8139f5e9ef80437c0213e3151ec0a8f6f4e7962d3cbd39dd29cee9357792d3b0139d8092ecf4e750273abd3dd1886e8c4274c3439c941cc6b4e405a72aaeb95571caab8e0f5a6f320b7bd69b8c94dc6416e320370d39b8680dd2516ec3436d571b24b4d72506b92d353d69a98b4d494e6a327350139a9eb0d2c4c6962d342569a1280d1266677ad33b1999ccb4ce05a6701433c96d9989ecc64e66027b3013998052cc0286662d32b15594cb4ca35a6502d32c96991eb4c8c5a64928323d3d8de9cc725a627ad3131698989ac465a6292831253d8529cc29436149fb0bd698129cc004e6000eb0007180cb4be35a5f02d2fc96979eb4bcc4a5e620af253978cb4bd2515e9282f3d3d75e9cba94f5d4a72ea50d7527cba6425d7a2aebd3970c9cb92515c7a2ae3d117129eb694e5b4a1ad99396cc84b66345b021adbd3d69886b4c425a4a12d0d0d68684b431d5a61cad310d64056b325a587ad2c1969606b4b03405819b2c0ca1600b4b1251589282c3d3d5de9caec4e571a7ab8d395c656ae04e570152b80715de8aaef4f567a72b253958086ac042567a7aab10d55884aa942551a1aa810955872aac3855621aa24dd5126ca86365401baa00d95125aa806c5303029015145ecca0c665062628499939eb49c95a4e1a02731393409c9a0284d00826815131e9c94f4e4962724a56926acc90f6648633242569206b4900544893323bd691d8b48ef5a4692da2bd3d15e9c8ac4e454a7a2a539146848af5a4462722253910c9c886344492da1a53d0d29c8694343 (Nat.land i 255)
  | 2=>fDecodeNode 9 22 0x275024a3409285012813f9284f989d3d3274f406b3daae4f24a13b7a74e9e893a7a74e589d394a74e4685396264e1281384a74dcc9d3731a4ddeb5366274d8cb5361a74d809d367a7cd4c87351a14d4087350214d529d344a4cd0c9d340274d1e9d336274cd29d337a24cd887326214c9887316214c528531321cc4c853101bcc5e9d306274c129d304a0cc0c9d3031a4c009d307a24c0c872f3214bcc6f2f319cbc6852f1944bc0872f0214bd89d2e4a14b86852e0214ba4c92d01a4b40212d7ac4a40c12962d4a06b1274a64958b524327491881231a748cc9d214a7481eb1190304664b1183264586b114030451899124ac4400c11002a43e4b50d7ad4358b50d4ad4340910d4a042d2810662141529d053214140c10492d401eb50062d4012b50032d401e9efe621bf9884fe321bf8c84fe1a03f4650fd92d3f18b4fc32d3f0090fc7ad3ed89cfb4ad3ecc9cfb6273e9284fa3213e989cf94a13e4684f94a73cc09cf36263c529cf03203b9898ea9323a40c0e492d38d8b4e362038529cdc620b6189cd63273592b0d562c3500c0d37ac349eb0d14ac345e9acb02b32d8b4ca626328090c94ac31d280c731a3180acc692d311eb4c44ad310cb4c4024311e9cc362730cc9cc301f30d898c1620af5e9cbb6272ecc84bb7a72e8c9cba3212e8c68ba621ae4c84b931bae4cb0b84a72d8c9cb67a72d589cb56272d0c9cb431a2d069cb419a2d00a8b30082ca4ccb102d2c4022b10082c6ab8b06322bcc98ad62a2ad898aa01e2a4068a80082a00b4a701a29c020a700829009ca3008a8c020a3c3428aab8a0928a7f0d09eaae2758b49c9282718b49b624a6d8829b4ad26d29c9b02726de9e9a621a68c869a01b269ec0999332598cc961a725a4cc957ad2558cc954ad255280954a62524b49363324d8829362024d2b4934a024ccb49332024eacc921ad2480b4927a724589c9192d2400b49092da3de9e8f7a723cc9c8f (Nat.land i 255)
  | 3=>fDecodeNode 10 23 0x1a14883589040b12080d23f00e47ef5a8f80c91e80423d62c47404c8b40811680422d0124580408a80511500422a7ac452f548a58b11330f22532044555c8864a10fa50a1e01443cf45879ec90e81021d1ac43805886c6810d31521862c42e05885deb50ab16a154ad42a342855eb109010a0e32641a63483589d06256a0c32741834c82809904c96a0202c3f60347ed294fc8139f932a3ee9547c52b0f82539ef4a63de0407b9290f6bd39ea0213d404c7918a8f0b131e00263b0f4e7518b0e980d1d37a738ac5870cc98e08d31c162c3800406f8068df00a1be00837c6586e807cdb2551b532636a0286d4080d980d1b30143660106cc068d880a1b10083626406ac680d5b131a77a734c94e698c84d30d09a602134c9586940b0d2b161a3626344c4c684698d0b139a01a7340c5867e4b4cda5699b32733604e669e9ecca50d99321b3263465c668cba551954a632a64c650698ca01319462a324c4c645898c4b1298632630694e5fc69cbfa5317e4a62fa64c5f64a0be81317caae2f6c585e5278bbb131767aa2ea0405d5eb4ba25697402d2e80425d0082ba0101744a52e464e5c9ea8b8b125706242e0f4e5b929cb725316e6272da64e5b4c64b6b1216c9282d69405a8090b480316900e2d095a59c09cb3807167aae2cc92c59989cb2a53965928acb25059129cb1a501637a72c4c4e588c9cb118a56201f2c4940580c80b018d1609282c0f4e57589caebd395c6272b894e57067cae3d155c7a22b894056de9cad19395a31a2b4342568684acbd1559314ab004e55de8aab30e55661c2ad55c555898a91931527a72a2c4e54529ca8a509513272a2642544c80a83d394f62729e94153d27ca7a4d54f62629c034538038a718d14d00e29a95a530cb4a618d14c02d29801d530038a60d3947624a8ac4151529ca2993945320a8a34e514680a2bd394462728894e510c9ca20d3944027288011511886a1b109434a128664350cc84a198dd4331928662950c086a1810943009a8632850aab8a0bd1141 (Nat.land i 255)
  | 4=>fDecodeNode 11 24 0xe4fc00e4ec0144e73124e61944d11a04d001a4c84a04b131a4af01a4af31a4ae61e49302049101a48d02648c62648701a4874a147949846d01546b312c6931246932046631a46649946531b46531a4624a045f00e44649a43d199437314c3131443132642962642702442262641e0244091a63fb0263fb01a3f96263ed0203ea0083ea19a3e701e3e700c3e762c3e11a63de0263dc19a3db01a3d94a63d549a3ce0203cd0213c84a63c601a3c40263b24ac3b131e3b01a03af19a3a001a3a04a039832438919a3887a438162637e4a637e02037c4a637a7ac3786263754a637531437532637462737132737101b36c61f3691a13694a036732636662636502c36401436400e36462635f4a635f02635f7a635b32635b7a635832635801435700e3574a035202635001a34c01434c4a03471a63463243454a134019433f19a33e01833d32033b01e33a32733802133800e3374a033092832d7a232b4a632a6203271a03274a03266243251943246263234a632262732132732101b32119432031a31f01a31f62731e4a731e1a731e194b1e19431e31a31c19a31c3203194a431732031731b3164a03121a031031f30d32130c62430b4a030b49eb0a49e30a32130a31a30a6213084a13083213083203086213074a13073213074a030601ab0549e3033263013262ff01a2fc00e2fc01a2f700e2f700e2f54a02f24a02ed6212ec3212ec01b2ec0262eb4a62e94a02e84a02e70202e73262e67a72e21a72e20142e01a02de4a42dc4a02db31ead50212d54a02d431a2d34a02cd6212cc4a12cc3212cc4a02cb1942cb49f2c849aac53212c531a2c519bac419b2c418fac418dac4015ac41a02c31942c300e2c231a2bf7ac2bb0202b90082b93202b41a02b24ac2ae0082ae7ac2a70082a76262a302a2997a62987a62976262974a629662629532629502a29502429449a28f62628d02a28d7a628c4a628c02a28a4a028731a28431a28192c27932627802a26d7a626a01e2687a626532626331a26302a26162626062625f4a025b6212514a125149aa4f326249621246194245621244 (Nat.land i 255)
  | _=>(0,0)
def k6_64_t1Buckets : DagBuckets1:=fun parent k =>
  match Nat.shiftRight parent 7 with
  | 0=>dagBucketBlock 0x8212a058b8101a02c57fe35ff417f719fd037e639f7887da11f5457be5de76177799db4a75f39d15a72f59cac47202dc2967031dbc916e33db4d06b579aa8b69f2da44e680459c4f64a9d8c5961a5d82125ea7974985b9656954590555a28550614f1452a4948495162d3fd7000013ccc4e43d364b0000135444ca2d2d164a92d278b48b4d200b46b551652450251382445250f48437190cc44300d088e42105058b40d24000040328fd4e3f308fb463e328f7073c460ee8a3b220e89039240e0903772cdb4a33accc8982fc98b9d52d350ae1b2a060a1d92754894a323b5c8a912126082491e1a072191b35465dc17c6c581c14e484ed312e344ac311264414d0f8343a100dc302d6709a6c20d70686c159204c280f1002070058a001540001 0x3c525a00f0c95403bd25000f03d6803bec5a00ec30e1931c95a5cc71969271c35a09c7016961bb25100eebd3c03b8f4e00edbd2403b4f4500ecbd119f1ac4e64c6a539731a64e49c68d38271a04e01ec3d6803b0f4e06ebb16803ae95a01eb016803ac04e00eabd3c07a804f01e9813803a804300e9810803a0c5800e93151670295891b5a5323ed694046c09961f6d664c7bb599001b0235822b58d3082d634000e7016003a205400e6010007a0f5a00e83d38039ec5a5ec125680f9a05a02e6813966fe94046bf99001afe34001e73d68039cf4e01e6a568039a94e00e624d5730065a5bc0193966fc63449c00d69230034e46bf0cd0270005a08c001381afc03400e5c96b1f7cf5ac5df31680f8c05a00e50138039004d00e20130039204901e43d680390f4e01e38168038e04e00e33d3c078ac4f01e23138038ac4300e23108038786800e14940672e9641fc9a5605b7894c65a3a5018e8e9345cbe999172f865816dd193246ca6408fb298d00f2e3642ec98d60037834c6ea38d01b28e33449be819126f805800dd0131f6ca0407bb280d0028001c00dfd574037d55c16e0a5685b6295916c6a560675e94d66a32530635e94165a325005b5e93563a324d05a3292d16e0196966e265892b2193246c86408fb218d0038235a00d88d64031a35803d78d35be8c34c02d78d05ba8c34000d78cd5b28c334008c8c54038005a46b88161fac804c7db20101eec8034009f80731a3155dc58c3d17167cc4cc6d6a5685b5a95920a4a560675c94d66a22533175a94217d6a504869294018d724d59688934168c24b7a35c65a99a219624ac464ce7d7190a6a8864091b118d3375a35a00d68d64e29235803d70d35be8834cccd68d08075a34139a48d000b5c3356ea20cd00230315d7d7016a06880587eb101335b5c04282a20101f6c4034009f0070037b55c16dda5308a8a94020a2a4d05b7064c5bb1990166c663448af81011abe034009e80700f2f25a00de3d6b3b5ac5accd6a568672a65a00dd9904635863516d618a466fa35a16db8d0246b83348fae0ca00ef605a009e004161a955d49bec968036925100dd3d6ad636f44d8d7316b5b5c95a19ca1968037264a00dc1904036e64018d598d48a8663416d598a48286628168b188466f835a00db0d39ca7834c00da8d016ec233459b08ca00f2605a02d500d40354029008a8024036786800d8bd90175af5804d6bd30033cf4400d7b190075cc5800d73130631496425a3a560928e94c5db819917aca6585db2993166bc63402d38d900f4c35802d30d3122a406449a8816122a204c009d8070036555c18bb193166ba634009d0070036325a00d84940135af5a01d6b168671895a19bd19696eb864059ae18d0074e35a03aa0168027201c58695574035f25a8c924944035cf5a00d6b1680346c3919c5a568035894e00d425059686940168924b466f265a00d5993966b264c91b09900074c35a00d28d00020e31403a98168035404e48a80100027001c18ced5700352f5800cebd100350c4c59a798d1229e04c009b807161a155d02d3c9680b4325102ce49400b4cf5a00d3b1680342c3900ce30e0034c95a00d2a500671065a1688988466ea35a5bad8d0166b632803a68168026c01000d249980746f6600d1bd680344c6619ba259862e895a59aba500074266600d099680e9836602a60d68026a32801d00198034005a00cf80a0033d25b19c3b168033ac4f18c3b13866e695a18b9a538073865a00ce19380e9635a02a58d38026832801cd0168033604f00cd0138033202900cc00a239e355c00cbb1680324c5900c6b160032cc5501c8b134f292c4c00c8b104ee92c402cc9a569b28c9586da22531b28894000ca9968031865918c29960071664d25a31930031664124a31900032835a18b78d617ac834c5db20d00b26632800c98169228c05849a20131228804000998040032525a00c7c9400322f5a00c83168e69495a01c3196866e435a18b60d00b26432803a50168026401000c73d3c031af4e3ba4b138e69294e01c5193c070a64e19b88d38b6623342c988ca00e9204e00988040031925a00c3c9400316f5a00c531680312c4d39a3a569b28694000c41968620c6201ba90d68b25e32803a38169228604000978041619b25118c33d3c630af4e18c0bd14928cc4e00c3253c030a94e00c2250c030693f00c0a4b4e68c64e319718d06e8c34e2c970c700e8c04e0e9700d0025c01000c13d68e682c5a38a0b138070295a00c0a53866d665a18b59938b25a63403a08d680a8234e00968c70070005a00c0013802fe01d00bf00723a5155d8e7855711afac5a46bd31651ae2c5847bcb1361288c4c46bcb1060e88c407787b0e51af895a7bb22561f2c494c7bb1250002fa65a00bd196402e265801bc9934968864c00bc9904928864046af18a472666281687988402f835a18b20d6066c434c18b10d0002bc33672998cd002ac32800bd816802a805900a4816006a604d01a4013002a604100a4010002060095865d57402f525a00ba494402e725000bcbd691ee0c5a00b5313402f0c4a00bbb10522b2c40778730e51eca95a00bb25391ab894c7bb0a50002ea65a00b498d91ab6628188298806ea235a00ad0cda165e33416a70ca0068e05a00810025619525100b93d3c02e2f4e00b5bd149288c4e00b8253c02de94e00b7250c02da93e0eaca4d55e5c9347786a4b51ec864e00b61908726264022a118d06e8834e00ac8ca94a5c32816a10c7006a404f01a30138020200901b4557402d125101b53d6802d4f4e00b3bd1402ccf4447b4b1691ad2c4e7cafa569eebe94e01b4996802d264e19af8d6862be34e00aa8ca0068a05a00a2813802000095864c94462caf4f18b23d3a2618f4518b1313802ca94f00b2253802c694318ae250802b89417298a50062c293579a124d1de1892d00b1193802c264287a1190002c06341aa88d3c6a8834e18af8cac62a031d1c980c7061fe31501a8813c068804e00af810c02a00352d9800d001fe0095864494402bcf4f57643d1406bac4f01ae313802bac4300ae310802aec3901ada53802b6942778224b1f2a064e7ba8190806b434f01ac8d3802b434300ac8d0802b031d16848c54069e04f01a18138029e04300a1810801fc0095863bd1402acc435763b0e6229c94388a1250a1e9c93787a124da1dfa92d78a7190de28464277a718ddde84636777e98845e9c34317a10d085a9c33716a10cd802aa31f167e8c54069c04301a10108029c03700a100d802aa02b007e8025618d55d00aa4968029925100a5c94002a6f5a46a93169de16c3946a8a5691aa094000a919691a9e6291c9798a05a1662100a88d6802a034000a78cd9ca5e33400a70ca0029a05a007e0021618b25100a53d3c0292f4e00a0bd140290c4e46a3a53d1a8c94e778524b51a8864ea29818d0028e34f00a30d38028a32b46a18c74325c31c16850c54028804e2d9800d0028602a449700a0028401c586249440280f4f009fbd3a324ef458c77bd100a7cc4e009f2539d67664f75999939ca7a643729e1909ca7264172989901d270635749818d1ca70629729818a1c9f6621199d8d3c666634e169e8d0c5a78342169c8d045a62340189c0cd46260334169c0ca45a60328167d8c540e7604f03998138027a043009e01080272041009881000a70035029800d00270029009800a001f60095861c9440276f4f5761bd140674c4f019cb1380274c43009cb108026ac39009a30e0067094e009c25090e6e64f759799390a6e64374979909c9f4621019b8d3c665e34e009b8d0c625e342167d0c54066c04e009b010801f000858613d140266c43576130e406649430198a50802649370098a4d8025a92d01981908026063643978d0d0e5c34242978cdd0a5c336727c8c54065e04301970108025e037009700d859f20090b94c9903252f700d943d903250f580294b1c00e50c6402943161222e6704f8799913a1e658468799010a1e634088b8dc0461e36410878d601a1e34000878cd0025806c488b19610a4a64c468719010a1c634088b0d60024a34c06870d00021c33400958180023a958088e25301a38940008e24d1221a64c468699010a1a63408868d301a1a34000868cd002540540294d5980a512660094bd980250c660093b130223694c068da4d12630666449219690a14658488619310a48642448519011a18634098c0d980a4835a00850d60221834c00920d080a1434006860cd00a44054009100f0024d2660192bd98024af5a079231981a48c5a01922598024895a498a8d99222a35a00918d011a1233442848ca01e44f5a06913d380644c5a00913138263c95a088f2539262865a488a1938262835a088a0d38064205a009081380240028428f8070023e010008eb1600238958028da530023694046831961220a64c468299001a0c35808828d301a0a340008f0150063af5a008ebd384a34c5a058d25680638f5a008e3d380636c5a008db138023495a49839969220e64e468218d0260e35a08838d381a08334008cd5980a31266008c3d98022ec66028931343a14c4c008931043214c400387a598022c95a0086a5600a1894c008625000a0e64c008399000e06366008a8d691a02358487f8d3119fe340007d8ca002280540089c9980624f6600893d680622c660088b1680e169660285a5680e0436602810d6919fc340007d0ca00220f5a0d8531683214c4e038525680a1494e038319680a0c64e03808d680a0234e067c8cd001f23280087c96c061cf5b0186bd68021cf4f0086bd380618c5a00863138061695b01852568021694f008525380e0a65a028299380208634037f8d6809fe34e00848d0909f2340007e8cd00210f5a0183b168020ec4e01832568020c94e01829968020a64e008218d00df835a027e0d3801f031c0081c96d1e04f5b4780bd691a04f4f4680bd391dfec5a467fb138060495b0180a568020494f0080a5380200943467f24d419f2934017f996801fe64e007f190909f2640007e98d005f835a007e0d3811f6f4f017db13c01f6c43457d253d15f294e447d250d11f2942427d24dd09f2936037d193c0df264e027d190c09f2642007d18dc01f2636037c0d3809f0342007c0cd801ecf640b78bd6029e2f4c0c78b19035e0c580c78313009e29640378256009e094c007b815001dc040007b496829e2f5a0778b16805e295a0975016801ea04e007a012801e60490079012009e325a02783d6801e2c5a0078256801de9400974816809da04e007680d805dcc5a007731381dda95a0676a53805da65a0076993819d8f5a0076316805d605a0075813801d525a0274bd6801d2c5a0572c99001ccf70406a3d90fda8f58027231c00dc6c640271b16061a29702b65a590a996958026899c02d966640a65996001d006c0073815001cd5663f6a499801caf660171b19801c4c4c19692598e99094c03691998899064c315f815001c203c0272559809c726600723d9801c6c660071313065a09660368199809c0054007000f005c2f5a0070bd3805c0c5a00703138659e95a1867a5380d9e65a0267993805be05a006f813801baf6425673d60919cf4c2066b190d994c5835653130619a9642b652560a99494c026699902d946580a651930cd82060006c00f001bc054006d00f001bb25a24673d68859cc5a1967256801b804a006d812005b4f5a006d3d388598c5a20663138659895a186625380d9865a0266193805b205a006c813801b0f4f066bb13801ae94e016b013c05aa04e006b010c01aa0420669bd94199cf6407693d642d8af5806693d34298af4c066a31988194c642164b1608192c4c0069a594019c96401692564518a958006925344d8a94c006a1998619466419649960619264c006218d0cd80060065e80f0017a0240069d59801a52660068bd981d96c662064313001a096601631998018663400678150197603c006749684d8af5a0066b1681d9495a0e612500058a65a006118a0019804a1865c96c619525a1864bd680196c5b006531686190c4108613100019295a00642538998494c0063a500018c65b00629968a174048065d00c0017201800623d3c9d86c4f276131389986c43266131081d8694f07612538198694306612508058664f016119380186643006119089970030065c009001700180060c9680980f5a00603168657a95a165fa5386174940165d24d00d7a65a005f99380974640005d18d00d6e05a005f0138016a04c025a01000168034005ebd3c0576c4f005e31380176c43015d25380174942015c99380172642005c18a00d6604e02598108016ef4f015b313c056ac4e005b310c016ac42015a2538016894217599938596664200598d0a38a58698e2061a3994af66da52bd9768fef64db50bd6788c8f58da50bd3784c8f4c87293d161c80f44e950b19b8cc8c64e42f31638cbcc4ce650a59b70c8964dd2f256370bc94c8e529998414a665103f9990454265968321960414264d673219321d4a6420052990400fe640065098d57cc8634005098a564c8628002918840080620b7508d99fcc8364802f0d61fcbc34cb3508d09c8c8340772f0cd1c8bc3288e50819890c8064252f016090bc04c8750810858c80401c2f00d058bc028015961a4016555d0957c998215f25a0058c9440161250b9563d9ae158f5a87273d12fcdec66be37b16ae4de966b837a568255866608561968009c62049378d9920de35a772d8cd1c8b63280937819820de05a1c2d80d058b6028581ce1a7151b5668c28d576307f55cc739499b14e4f660352b198015ec5a0055b166e114c58005731540954c4dc03731300154c41be3731000130c390048b0e00d429660056a56ae110958c036a532f8da940034e9998015865a064d9960213464c064d1900009662049360d9ad54035a7b308d61f4ba34c7b2e8d0024d80668c50016880c2058222e813080ba040015461a4015155d0155c998015725a0053c944014d25001553d980154f5a0154b1980152c5a004bb0e4012cc38034fa598093e95a034e1998093865a0025188124d636648358d6824d606608358169607155d0052c96d5c7125101523d6ee514f5a00523d3ee114f4e0051bd140144f44bf37316af8dcc4eb937256ae0dc94e034d9968093664e0024988124d435a48350d3824d405a08350139606f55d0050c96d5c6f25101503d6ee510f5a00503d3ee110f4e8726bd16fcdac5abe36b138053e95bbb372568013e94fba372538012a92d034d1968093464e004c98d0009062049348d6920d234e424f0d0a9cb23340934816820d204e004f01097cb2034581b5574013b25b571b49441d38f5b074dbd681938f4f064dbd381928f4506483d101d34c5a064d3138053895b014da568013894f004da538012892d004824b0053465a004d1938013263449338d6920ce34e0933816820ce04e044c559c0531267004c496c0d2cf66024bbd6c092cf5a004bbd3c012cf4e034ab198092ac5a004ab1380d28966024a2568012894e4933199920cc65a4633193824cc36608330d6818cc34e03490198092605b02490168012604f00490138112325b0148bd6c0122f4f03482568092094e0048250924ca65a4832993918ca64209328d6820ca34e06328d080d1e05b03470168091e04f02470138011e04300470109606755d0046c96c011925a8c284946307d250c738bd6b14e2c5a0343a56c0cfe95a0045a53c011494e0042a53400fa94c0044a5240908941653125000108935633124d000f492d003aa4b170c865a5144193964c064c912e19023cb863449320d69091034e46300d31f4b83407b2e0cd024c805a0044013818c004c222e010080b803458195574010f25b57194944050cf5b0142bd68010cf4f0042bd380102f4500403d100508c5a00423138050695b01412568010694f0041253800f292d003c24b170c665a5b31993924c635a48318d3824c605a083181396063251003fbd3d5c62f45013f313c04fac4e003f310c00fac42003e30e400f6c38643125398cc49425c3119396cc464249310d3920c43420931013820c4042043d496c04f4f5b003d3d3c0cf2c5b033c316808f2c4f023c313800f2c43003c310970be95a5b2fa53964be942492f996920be64e462f990824be35a082f8d3818be342033b816c0cec05a023b813c08ec04e003b810c00ec042043abd3c04eac4f003ab10c0ce804f0339813808e80430239810800e8037003980d9605d55d0039496c00e325a8c27c946307b25002383d6800e0c5a1936256c64c895a1637a53c58dc94e1635253458c494c1834a50488ac9401634a4d480ac9341623a4b464bc65a1636993964b864c5b2d190164b463403360d6c0cc835a00378d3c00dc34e00350d3400c434c02348d04e8ac34000348cd4e0ac33400238c540cbc05a0036813918b804c482d010118b4034002a8071605b55d0036496d5c5b2510135bd6c04d4f5a0035bd3c00d4f4e00333d1400caf440134b16800d2c4e0134256c64c295a0034253c60c294e162324b464ba65a182e993964b263401338d6800ce34e00218c500cae05a022b813800a801c5816494400c8f4f57163d1404c6c4f0131313800c6c430031310800bec39392b2538e0ac9420130993c04c064e0030990c00c06421622988464b834e182e0d08b0a6328032b013808ac042002980416057251002f3d3d5c56f45472eb13d1cb8c4e462eb10d18b8c42772230e51cb494e462d250804ba64f012e193800ba643002e190800b6637462c98a470a66281622188404b434e002d0d0800b233672298cd000b0328012b813c04ac04e002b810c00ac042002100256054f45042ab10d5c54c39012aa50c00aa937551524b5d4a864375299909d0a8637742998d9c8a862b722998a9c882621192a0d0c64a6342182a0cdc60a6336162a0cac58a632a16208c540ca80430329810808a8037022980d800a802b002980a800820090029559c04a32670128499800a325b002849681c9ef660627bd68049ec660027b16824969660825a568009c94e0024a5301890940002424d1248e66648239969089a64e422299311888640422218d0248e36608238d68009a34e00228d30188834000220cd000980480425c96c0496f5b0025bd3c0c94c5b0324b1680894c4f0224b1380094c430024b1080c9095a02242538009094249219969208664e46219908248635a08218d3818863420423c96c048ef5b0023bd3c0c8cc5b0322b168088cc4f0222b138008cc430022b1080c8895a02222538008894203219968088664e002199080c8435a02210d38008434200208ca0008125b011fbd6c047cf5a001fbd3c007cf4e071eb168187ac4e011ea568007a94e091d0168207404e001e0108007603d041d3d3c0474c4f001d310cf8735673e19d598fc5d2663e173d980c72c670319b198c470c5a001c31640062c58021bb1348858c4c001bb1048058c4019172598f46e95a26162560a05694c2615a5000c5c666311b99681858658081599301856640311481500052030001cd59c0471266001c4968046ef66001bbd68046cc66001b3168645a9661816a5680c5a66602169968006a04a001a0120006725b01193d6c0462f5a00193d3c0062f4e211631688058c4e19162568605894e03161968085864e001800f8005e03c0017496c1c5af5b07163d68185af4f06163d381c56c5a0615b138045a95b01162568005a94f00162538045665a001599380054634061400f000500240414bd3c0452c4f0014b10c645094e181425085850936031419380850642001418d80c4e04e02138108004e03658075574004d25b57074946e448f5bb90ebd6ae048f4fb80ebd3a1c26f4587083d12fc30c5abe0c313ae43095ab80c2538244865b090e9968204864f080e9938004a643871119080044641000d990018426355f0b18d00042629590b18a0002662100081881243035a480c0d3acc42342720b0d01dc2a334720a8ca0243005a080c013a1c42042160b0100702a034160a80a1601b55d0412496d5c1b25101123d6c0048f4f5506bd140c46c5b031131680846c4f021131380046c4300113108003ec39000f30e00c4295a0210a538004294203101968084064e001019080024620490b8d69202e34e460b8d08242e05a080b8138182e04258064944103af4f57063d14043ac4f000eb10d5418c39030e253c0c3694e020e250c0836942000e24dc0036936000d24b4003292c5c0b19396c2c642590b18d9242c34e480b0d09182c336090b0138202c042060b00d96017251040c3d3d5c16f45010c313c0030c435505b0e4642e94f190b2538602e943180b2508582e937160b24d8582292d190a9938602a642160a98d80c2e34f030b0d38082e343020b0d08002e337000b0cd80022315030a8138082a042000a80d8002801c1009c96c3426f5b0c09bd3c0c26c5b0209b13c0026c4309092568202494e06092508002493649089969202264e46089909082263609088d68202234e06088d08002233610083d3c3420c4f0c08310c0c2094f0208250c002093709078138201e042060780d8001e02a0407496c041cf5b00073d3c0c1ac5b03063168081ac4f02063138001ac4300063108641695a1805a538581694203059968081664e0005990800140305801c9444012f4f5701bd143412c4f0c04b10d5406c390304a53c08129430004a4dd440692d0904193c240e64e0804190c200e642060418dc180e636000418ac000e62a00029884000862049030d39200c34246030cd9080c32a09030138200c042060300d8000c02a3301bd3cc806c4f3101b10ca40694f2801a50c98069370901993c2006643060198dc000662b5800bd163804c435700b0e634049438c0124dd540292d8a01190e2404637870118ad44026217a010d0de40433777010cadc80431f42008c547c040431e0100dc700402b1601007c000401300008024000003f 18 0x3ffff 6 0x3f 30 0x3fffffff 13 0x1fff 0x1ff 22 6 (Nat.land parent 127) k
  | 1=>dagBucketBlock 0x1afbf5a2e950d10d9e9f3638000000000000000000cc89980b2d1e4c7000192840000000000192072118000c7498e071a16286c34f850f09080000000000000060c300000003022600200017e8ef925ee2bc4d770eeb1dd22b9877112e015ba3b58f64b6c61d74cadc7589a9bb5268a38b43227d4cf62000138aa6e1cd82998d301a574c9aa0001250e452c8058ecb19a21cbc26981d8ff25f5480007bccf705ed0bd247850e7c800039646fd8d4d99d633056166b8d16e1ac6b532e9a612a525214a028b49077a0c13d6270d0d941a6631d8595495e9189209438485f88993000021283188601099411101a4001a 0x2947a780d26c4f01a4989c0149b10c029262123d2294f47a4129c8d48a50d1a904a100d2264f01a40c9c0148990c029032100d1c34e00a386848d47a50032803140051e34044a0066801470ca0028d92d01518f5a00a318b48545a56912884a0a250894042a2126a854224d0028b32d0151064102a10c80014418d4028431a0150234000a046680145012002897ad00d10c5a00a2189c0143a568068632d0050c64e00a1589c0342253802844a100d0664e00a0cc8407400d380a801a100504c4e01a0529c0140a5090e803272150064201a0069c01400d08227f7a7034fec4e009fd29c013f0138167c626004f8934039f1e98193e3160027d626064f8f4e029f189c013e2538267a027064f6042029ec06c013d80a8027b320004f4c4c009e64c8073c31900a7862c00ceec58009dd89879352560966a32c004ecc40059d9eb0013b31000e7692c004eef64409c1eb03735a560166b32c004f0060009de4b4053b3d68027662d0ccd895a039b0cb4053a80f00275018004eac403a999280453319000275620044e8f4e069d189c013a25381a73626004e694c019c8098013901000273620804e2036009c989c0d38a538027132720cdac4c009c12b04334253082684a0004dec5800984c680136bd60da6862c004d895819994cb0013018d0026e030004daf580597ccb0012f98d0026c7ac004d695800978c5041333130025d31a07cb894c0e971280012e18a0425a626074b493405968c98012d18a03a594a0004b2628189aa4b055343d601a644a0004d4f4d1f969e98112e31602e636260ecb49400698d268013481589a5c7ac03cd0f4d2998de9801343168c66362c004cec4c0896d268013299343e5b326194aa054289540780f290090025200c004cc0480695004801288060c6647a798cc6f4e2899189e5131b1381a644a7834c694e00990c9e01319938c65001e144a0030069400480128006062657ac004ca958009912806f2db130125a49a07cb664c17968c80013198d0026202b134c2c59269718b04f3031349e5b626134c0c412696d8800d30a5641a5c4ac03cc094d0796d2980d3025041a5b4a0004c265900970cb003301934065b326004c06410096cc80672c01509a4f0180349e0240093c0300130c96802607ad0b4bec5a0097d2b4012f1968025d0241349a03006934048012e3d38025b6270b4b494e00968c9c012c80f866564a60c4ac94016959268052b1900025631a01c9204c02924080012480d002586260dcae95819955298312aa4d00e55326014aa63403920098012581000a4801a0c4a863416950c50012bb13002564ac00caa94c009552800129996066523260c4a46400093cc50072301300a46020004aec4105938c80012718a062513200049a62800959e9c012ab1380652327004a864200940c68052280d002537a70c4a4c4e1894526a012919380251321004a06340093d8862f26a50c5a4e4a10b49a93701934c8601271908024d31b81c860420290c06c0725b1300a4b620004929580192129801242500024c32c0bc8e64c1691cc8003238d3002471a001496c4e0092d29c0125193802497a700490c4e17918c9c2d2298d0024519a0048ec4e00918c9c012298d002441a700486334775a0c80e4b418d071681a00b2d0334009080a8eeb39901c96731a0e2ce3401659c669172081021e4101a2148201c009040200120499afdbd7b35f37af5ab96f58cd70deb16925bd3332437a65a77598c80e4b318d025bd1b30437a35a1c5986802cb30cd0063f0330047e05a8b8f8083171e81021e3e01ac3c7a034428f803a851e8070023e0088047a010008f2ab8cac499018d8931a3db1234c7d5a8680f6b50cd08189026112d4040205a8068051cbd6002397a600438f44008ed8c980dca562f9b94a60444a65806894c98fabc0d61ed781a6112f0058205e0098011d1930222232003444634d3888698fabb8d01ed7719a4b44404c225dc08040bb80d301bb4a05f376934008e8c9980dc1902f9b831a3ead23407b5a466844b48100816901a00472c54008e189980db253022243263eaec34c225d8098011c3130023701e0042004c008d8068851a8070023500801458c5a028a52b490d9196821b21ad0046805a008cc0688519007002320086d3caf64e265deb1c2cbbd338d95632722fac58e35f5899b8caa593757d4ac6e2fa94c028a0cc8171319602a263263fb18364805e86b0febd0d30918c03212af4058245e8098010781001a0f01a2146201c008c40200713a5680a274a724b6065a486c0c9c12d80d6821b01a700c6005a008c009c851780750a2e00e0045e011008b80200116e1a369e37b271326f58e164de99c6ca3193917c62c71af8c4cdc65d2c9babda563717b4a60144c6640388ccb005119930022031a3fb16364805e46b0febc8d329d5e19a12316064255e40b048bc81317d5e01a5c41355c59624cb005111930021f31a24358358486ac699a5108d029d5a19a04358058086ac0991f1081017d5a01a0045955cbe6d9898010f18d29d5d19a2faba034018aeaba0115c94425ac7ad04358f4e87865e8b2110b16a3e216275fb5495abe6a929d72d6196ae1ac32700432621038846b405108d38021d19424b5405a486a809d0f0e80d1dd5801400455868c57edec990de3d631dbc7a662becc64c86e98b18edd3132f1fb4b261378958c16f129978fb199309ba32c60b7464c00880c68fec40d9201751ac3faea34c246200c84aba816091750260045355c06891898010f18d2f1fb92d0044f250c16f1eb4011431681a0761c03c4c95ac46dd28178de196ae1b731424b4e35a0969c0b4b071d576f1f692d44a4b251c16e9eb4011331696d896270044ac490089188380dbb1001a1761c8340cc380088d2b40111253ae1f54a66036a940bd6f0cb4010a988525a61ad2144234ea956c68012d301680221027302b60405838a4a201103d3d5ce27a280c3ec4fb97d589c010fb10ee1f562143a46c390787929f7edba5381a1e4a1df36e9420685125a030f193ee5b73270043c643b86dcc84010a188525a51a72434a3424287466c12d2813821a50210043a03600871ec180da3162f9b46260142e9580085d298faba1961ed74326112e8358205d06980109019002100260041e0400086e4cd7eda3d9af9b47ad00434c66038552cc050aa56802144a024b466664868ccb4850c993a9d5732004b463660868c6b4010c8d397d571a001c1c066028380b401068100021893300c2ef660085deb4010b319806154b30042a95a0085128092d0999921a132d04b42366086846b4070601980a0c02d004260410082c0800109a53006129330042525a008458cc01083104020f62000c1c966008392b40106a500060c3330041865a0082cc8092d00d9921a01ad2333e340096800cc10d00168199f02000415566c770e4cd8ae1bd9802074ac0140c94c0081928092cf19990a0932d3db0e6587d5ccc98f6b99900259e1b30041235a2061c6b044b98d3081731a001c06066008200b401028164020102c00c0ef5a0081de9c0303316802066272433864e0867069c070001680a000270040b25a4866ccb48ccc9900219b1ad03332340008100b40101c96c06017ad00404f4f00805e9c03001968020032724b3435a4866869c8ccc0cd0259a02d0433404e0666006806f2a59001ff4b02c3c6958007ed298d4c52501a58a49a2e32a6645c650cb0a2fb1932457032047ae0634496546c892ca0d6109f61a63eae03407b5c066812ca8190259402c003ec04c225c008040b800d315cbaae62be695a007cd2b200ee256315fe4ab003fc955007f52a806f82535ad854a6013e09416a61528000f824d5a58549a0039692ce77c0cb51ec29962496f32648ade6408f5bcc69acf80d69ed851ac3f2de34c7d5bc680f6b78cd315f002d1030a058235bc09844b78100816f01a2cb0864c915b8c811eb718d119841a63eadc3407b5b86680cc20130896e020102dc034037964b400fe495401fa928003f6f5a8c475e898ed8b16b15b14ad2e32e65a4965c6b412cb81680df462d013dec4d027b989800f7b10401ee620003a4c38007e52b400fc256001f74962e32c65a915b4c991eb6990125961ad3eada34c7b5b468012cb0168896d026102da040096564b400fb3d6a311c7a263b5ec5ac56bd2b406f199681984320813da635007b4c52b8c98d6859f51a048ab23348f56465092c9816801f50203eab20347b56405000f9bd9321c17ac63b82f4c007c18c990e031631dc0626013d6964007d12c006f5256009ea4a62eb0c664945c8cb126b9193129861b2402e43587f5c869814c30190957202c122e404c007ce4b400f9495401f192863b82f5ac57058b402f5a56801d04962e32465a496486b412c9016801f092d63b80f5ac67058b402f5256801ef4a4803dc948007b128200f4a501719132d28bda64e915b0c8092c88d6909ed1a73ead8340096440b400f68138896c020003d8c4c027ae4b404f3c94009ea7ad003d6c5a0079d87000f5256801e94a02e32065a496406b412c8016801cc02028bd0028427a003800f4004005e762d003cec4e5c63d2b4b6c7a539218f3270431e34e017980b400f3013a38f6aae003cac5a007898b200ee316001e462a80bc0c4d6863589800f031059d8d620003aac385578d2b4d2c2a56261714a64bae29405178ccb4bac29962517132649ae26404278c6b494c28d6201711a63fae23400078c0b414c281609571026122e2040 15 0x7fff 5 0x1f 31 0x7fffffff 13 0x1fff 0x3ff 23 5 (Nat.land parent 127) k
  | 2=>dagBucketBlock 0x874143126121b06c98244c072e008cff447f80bf229f708f8cb7b44bce31e196ed0f76023a725cf12e64572e139311c806e3437045b7535b02ad704682db3531931ec806622780001850ebf4d5f02aed2d6f9cb78157912ae395310a70a5264a882d3e189ec14d29261212f06948c4963a4225199e8a8943e5a1c0d05a280893de99ea14eca26e6032b218e1cc1185c512e009691cab265484288713b249798451b21a39052078a839ca1b078cf24611a2f8400000b6205614261412c1095044906230610e280000428420c20000000003f881ec40f2107120339417890ba085c042c8615830a81052082786114a086103f101a940d0105e280000160609c5046201f100c0e038a01a08091000000009 0xe0929c01c08d3803804a64262494083c49268397019611b7f32657ea6640aed4cc690b6e8ca05b3a18e006fb25072b812b001bfa53213174a041e2e93487ce8cb001bf1931f3553203deaa6341cb7863801be0130f3130201de2603446df0c99aba49903534931a0e5ba31c00df009929a481024f4901a395ba02800ce803801bdd572131862641e30c4046d292b0f9a9a531ef534a02369062885b406682d960ca1234162c4262cc4c7bd452b15faaa5311b494a0006f064c46d1cc50bd978d3216cf19a0b65632871c4c09801bbc940037a62c006f294c7bd3d2808da298a05b29194006c463446d08c5001a10cd05b28194006f293c00dd1e8801bc313127404a62468093446d18cb0f9a919311f463203dea463485b286502d928c7003777aa2368893416c90c6801bb010003757ad23eb6c5a00dd12b48da1a4d06f2132d42d9264016c80c6801b981680372021006e204100dc00800bb32530036a49e2bd9093447d64cb08fac193003673201161a63452b206502d868c70036f4a507e8294158b1d2801da0a4d55ec749a006dc64e1cb5cc98478619008b0c31a0068232a52b1c6502d860c70036d7aa07e82f4c24c618b0498b31303b4049a2b59c64022c28c68378c0d606f161a60068032816c286388fb63128036c624806d6c4805d99882b163b10143664a74358e94c24c2528001b318d95ac731a1161262847d9869d0b638d306f091a00b61231c57b19268458418d14ac61940b61031c00da9e9c01b23d10931b627006d294e00da129801b299088b0731a0de3634e16c1c6388facbd3803676271263494e00d98c9c01b298c83b3e3148de3434e00cf863c038e013803646242bd7cc4022c09280a55f18d05b02314006c725000ca865001b12501334e3263de9a64016c0c638019c98d00361024006c000c00ce0c688daf80d0035f00e236bcf5a7cd2d8b4f7a5b138035e4ad0ce9665a18d2cc9c019b98d0075d02d006ba04e46d7006801ae0070035baae00694f5819d45e9831a9b161775562600e8c94018d4926801ad24b2d30532040e686341ac64698ad660c70b6d601a006af25100d6589c31a53135cad762602ea2c41aac11881135230e403584a73ce1894c84c5528001a898daa30431a40e2a6281accc682b1620d00633318eab58831c18a6462a019880a4b6d50140052e00900d5a4a157a618d156d118e305a2034b6a8e4a28fa9b1380353626c3e18c4c47d55883398ab10226a361c806aa94eeac5529801aa2500634931b3e66463573b48c69059a98a5e70b3143e5306217cd2469c31990d3472d21a60d66a34123c2c680314c0c551f2f020d1da804000cbc0525b6a00a00296004806a6f4e00d4989d234f30e277354a7006a264e00d40c52358b8d3807160270069e03e00d3406a019700a582cb01475668c43eac55885379a250e6f154a140e6864381c54c8557a618ac6b341a18d62a3425bd3066e31a60c7c073402180e2a04246d3006e01a600ac034b9280069c94079c0d26801a69900034c31a0e5a231c00d298b003a4b13003496200069095801d1d29801a3a501ef3132c3e65e64c7bcbcc8001a08d6097191a61263234000c500b003898130031302000694f4e00d2589c03a32539f3323270d63034e18cc063a0389013803487a700688f4500d0de8801a3b13803464a73e64c64e01d0069ce5668d04034519f0068433500cfc6688d9e8c7407110273959a94c00d09280f7981931ef2e3200067a31c00d05e9c498cb1386f184a70068064e52b18c84019f98d1de9d3103e66634e00cf868445830cd0070f02700e7925100cf1e8a33983138633062100676c397ccc129cf79825091b3b496a3e7a64e46cf4c84039e8d38033d1a100e1c04e00c38084019d98a63ab9928c74fb25087ce929d0f9625361f0c4a64465694188c2d2810f95a4d61f0b49a43d2892d77ce8c9cef961935df0c3263c65664178c2cc80ef9598d5df0b31a3bd2862116ce869c2d960d345b0c1a60be5634117c2c6802d958cd45b0b19a0b52831500ce809c01960134030c02600e5604101c2c080019580d4030b01a0052800901ce64a2019cbd14072a62700654c4200ce1872019bb0e223034a743e0694278c0cc9cef8199085f031a70b60634201c0c09c018181080336aae23e6494c46cc9280396818a007321a60066434072b4066801960ca2cb106262366695846cd5298d188193072cf3140066635800cd4698e5678cd0032b1940064e04c00c89e88d188313162c24a60e59c65823c14c988d9898d1771019a29d8432817c1463803993d3003217a200666c5800cd5898e5672561eb054a64461465800cd0c988d9798d072cc18e00e4c04c00ccde9c0199313803314a70066094200cbcc9c0197190a1f063202ee2034e46cb463a39658c7003260270051e00800cb4c80b1324944032c7a700648f4500c81e880195b13a230a4a70065494100ca527c019424d61f0649a43d2692d78c14c9cef4898845f051a70b52231500c9409c018180a8028e0040064ec4c47c98c988d9318d072ca18e00e4c04c00c98068e56500a0032500e0064863446c8c068019180711b227ad23642c5a00c892b43964a4d0032132d3959264000c80c68018f81691b1e01aa363a03400c7803a018e80711b1a326515a66340cb20638018d0130b6d301a2259002800c34039476919028ad231a2362831d0cb1c6385d690100b6d201a0062802a44b1c0500186007347134a0d2d88940d0c4cc9d61621933430b3203862634133b106808d898c7432c418e1de2604e62b100987785810003130152258802800c2c038e189b1312f0f4a62362465846c5cc99456b18d11b1118e17d9803444b0805001828070cec44a00a61e64111b04c80018e0d3872c71a60a608340a2b546505f6200a0030f00f0258201c00c1002145689900b6d10200060601c00c6d892018d3104bad26200063294e62b112987785a50003183270062464d72b1cc98018b99052f043200062c34e00c24698018a8d028ad4194236200111cb10020018a3d3803136270062494e00c44c9cef4d988003101a75159633400c3c09c0187004562637a28061ac4300c31884018130e4030b4a10061464300c24c84018418dc03073190060c62960b0cc510f4918851b051a1a360834277a4062a0182810c03040210060601316a40013455fa50032be31416d7e34044af866801810ca00301aae00600f4475b80cb0eb6f1931cafa3203a5ac63472b58c5033700d6066de1a60b5f434018b586682d6b0ca00ee002c01dbc04c00be8080056b00d002d6014005fd25100bf64a0e57f9939caf5326b95ae64c75bccc82eb6a9901d2f331aba5aa63472bccc52e56a98a1ca8d3108b5fe34e16bd469a2d6b8d3066f31a08cdaa34018bcc66a316a8cd05af31948b5aa32816a3462a017f813802f5026805ae04c03bcc082076a81000af301a815aa03400bcc052016a80a0028d004e355d251c5ab9872017e2501cef9327395e264d72b48c98eb791905d6d4320395f263673bc4c6ae76918d1d2f2314ba5a862872a30c422f7c8d385af11a68b5a434c19bc8682336a0d005af919b0bde233517b4866831790ca462d41940b51831501be409c0178813402d202601de404103b50080017c80d806f101a80da403402bc8052056a00a0028c004805f725072be0c80e96898d1cad13140b5f034018b446682d688ca00ee07a7005f4c4e02be529c017c9939d6dd1a7215f033574bc0652e5780c7466dd027005f003518bc00522d78007402f7aae005eac5805bc58980978b10002e561c005e695801bc929801792501d2ce32c3ad9864c74b30c8031670d6066cc1a60c59834002bb40b0077601300aec020005ed25000bd5e9c017a3d1012f162700de294e75b40c9c33680d3806ed0272c4c125100bcde9d195abd1402f2627005e294e00ba525aeb6799390af0321215dc63574b2cc68e544188466cf1a7005e034200bb866a31658cd05a8818a80dd804e00bac0680140802062e4928005dec4c00b9187001772501625e928815daf4e02b9de8a0571bd100aec627005da94e00b9d25a0171a4b002ec327005d663475b2869ce5430c5466ca0270b50c00900ba9eb40374b16802e9627215d095a00ba0cb403738d6802e71a700dcc05a00b9809c0172bd3dd6c94a7215c894374b252843364993802e43218c59264201b8c69c01718d0806e1027005c404300b840851d3e494002e04a7005b894d00b5d298016fa52406db4a082da494000b6d26a096924d002de327005aa64c01b50c80016a18d10add1a7215a034d74b1c69887678d05d6c41a02159e33574b10668016e813802d00268c58e04c01b3c0823362010002cf01a8c58803400b71e9c016cbd1002db627005b494e01b4cc9c87640d3806c8027005b0c4300b5d8840969250806d232121d9c34343b1c6840367010c06c70212c4b6f4500b59886016ab10a5a9f61c805a894200b4cc860169190802bf310a1d9834343b1068485688cdd0acb194a158632872a1062a0366010c06c4021005a203700b2c052016180a05a84004805a0f4e00b25e880167b13802ce4a70059a94100b30c9c016598d10ec21a70059404e18a00010b12d3d1462c86218c58ec4218af98723162250802c83218058e64200b18c6e016298cc02be3108058834200b0c6500161010c02c10213950600900b0189c035fa53802bf4a121d7c64e42af8c84035f0d3802be1a100d7a04e00af4084015e499036b87b206570f5803ae18c8055c31611aa63202154c63406a9868001530cd01abb0200057603442ae8038015d00411aa53202154a63406a9468001528cd016b77ac0056ec404ba88cb0915219011aa231a05d4435808a906800d510cd00eb792c0656ef6400ae5eb08d50999136a332c2454664006a846c81f518d6022a31a0005700600cade4b4055bbd6802b762d24d5c65a4cad4c9c8d4f993112b53212153e64042ad4c6c894f98d026ae1ad0656a34e06a7c698055a8d08029f1a00056a33602a7c668195901200ab201e0056403000ad86b0015a0d0122ab1a60056a94c00acc668055881510ab47ad00568c5a07acd2b40d59a53806b332d0056664e00ac98808558993922a03200056234e08a806800d58253802b03270355ec4e00abd29c914e99011a9d31a0453a34006a746688d4d9931229e3200353634c08a786808d4e18a01a9c19400558c5803a912b00552253002a44a024d3235848a646988d4c8d00028d1940055cf5814a858b0015125900ea34ac0154694046a546c8934c0d6122981a00051832800ab40c00156496056a17ac0a542c5802a852800150a4d0528b1ac2452e34046a5c66801458ca002ab1a60055664c02a8129801502500028a1940055435800a246500154818002a86260051032800aa189801430ca02e851a60350a33400a146500b513d6002a463200d46c5800a8d8980153a5600a971b201d2c35802a58698014a0cd002a60300052633400a940a8054e9900029d31a0152434000a486680152496802a37ad00544c5a00a852b4014fa5000a9e32001d3035a46a4069885420cd002a00240052233400a7d280014d98a022841a00150633400a406500b4e1930029c31a0050431c0ea6d280014e9930029e3202451e34000a046381d4da500029b3140750034000a00638014ea530029e4a02150034c02a38680034eb138029d6210053894e01a6cc9c014d99080e8f1a70151e3424ba55eb08d4cb1911e9862c23530c4c14a552b0014c9990069832c0053064c00a50c68014d0180029131a04506c400ea41280054198d002903140053325a00a61eb4014bb16922906200052c95a00a49298014a99681a843140051e340 17 0x1ffff 6 0x3f 31 0x7fffffff 13 0x1fff 0x3ff 23 6 (Nat.land parent 127) k
  | 3=>dagBucketBlock 0x8a990dbc0004303850902bdf5800007ad4f0a9da3800000000001d14b98571cae115c10b7e26e4cd824000000000000001a2733290000000193332410000000000000000000000000032210000c80400031e161d0000000000000000000000030c100000000000000061420001840afe55dd0b915694ac285802ab294f3a98350949e953a1a648000090c51e1a3a1460a8a1110220ca3ed679a0ef21d64394c7204e309ba635126240c1197a42e865a94b029584289450089e113442490478c88390651e5438a06560b4b158826a448288c210881f1038305e90a4c138820383c2060c089c0d20124018601100010000 0xfca62c01794c4c00f2988125b61962476c32647ed86407edb06b0fbb60d31ef6c1a011ed805822db009841b6010003cd4a680f9a94104f3526b25b59932476b32047ed6634c5f34c54fdb58d31f76b1a03ded6334ccf3465447b581308b6b020106d6034eef34054b9c59931278b1a604f1604c00f3c0b001de01300bce0200079c0346be1129805e4250003c849a2e71c6585ce34c9923b499023f6931a24f1c35849e34698fbb48d01ef6919a04f1c05809e3409845b48100836901a35f0894e00f3529405e4a5040bc74a00079293500f1d26801dea4b147cc32748ed06408fda0c6885e60d39f7681a03ded033400f3009c45b40100836801a007966541ff08c98b9c48d6173881a648e803348fd0065093c4816127880263ee800347bd0005093c4bd38278962763f4694ec5e8cc9c07e10d380bc61948078c31d5ce2809d239f80a23f3f00e34f0893494da8cb127b51932036a1ac3fed434c25da80b049b5013003ca4aa00f8894c00f1128125b3193247663203f6cc34c7dd9868047b301308b660200078ac4c00f252b123b29931f7651a6116ca04c00f2129c01e3a531738732724f0e34e09e1c09c01e198d05bc61a048e7c33400f18080fb9f00d003c54a465772c4cc5ee526991dcbd3003c462c64770c4c92d9cc98fdb38d308f6702600788f4ec7ee589d8bdca539738632728f8664249e1869c85e18d0827860270078604201f05eb001e0bd32636f4ac4bede94c69e1126929b799624f6f3262ef0863480dbc6b0ffb78d312b8419a12ede05824dbc09815c200d073c23264c68264097d04c682de10d3253411a049e8233400f0809901a08101ff4101a00782c5400f0189931b72532536e326406dc34c25db809801e0313003bf0260077c05800ef9e9c01deb16247644a647ec89407dd90c98f7b219008b641a6106c834000ef006801dd816003bb62c00776f4e91d6d2991fada501f75b1a63deb634000c0465001dd3161737d4ac48eb494c8fd6928093be8d61f75a1a63deb434000c006502ddc8d324b591a048eb23348fd64650017f804003b93263363864065c70c68c78e18a1caff1ac0077034c92d6068123ac0cd23f581940076ec5892d5d2b123aba5323f574a03f6ae3587dd5c698f7ab8d0002fe194005fa3285bd59298b3ab2501234b1a62369634000bec65005db013003b60200076a03400ed005001d980407f893260cf003585cdfc69937a30cd2674619424ef804c00be8020b7a70cd1674e194005f001019e2ccb03fc419308b1131a1062262819dfc6b033bf0d31cafa1a02dea433459d4865007c5013003b09280076465816ec4680b7a78cd1674f19442df03405bd34668b3a68ca0678b7a701f00c4ec7e8929d8bd11938677c1a701f1204e02e9805201d3007562709288cefef4e16ebde8a07bfb13803af61cf7f4894eeee90c9c33c40d385bb11990c74a32916e9463a2d558c540f880270076203e02e9405201d2807402ab0048076095400ebcc9801d700a002f7194005ec32800eb408001d600d003ab014007540105cd28c98b7a51901674a31a005ea01c00bd065001d480d003a80140074e01066c3d298cb87a501674132c496a264c91d44c8003d18d3003a31a024e6604c48ccc080017980731af962632e2895868c5d299378b19632f553264ee3264002e886b003d20d32c31002c24e6a04c00bc80398d7cb131971249a2e69264c9ac60c8123a998d003a219a2466403400bc403801d08cd003a60202466003400bc003801d00cd10af00260074a04048cb806801d319008b0e31a215e034c00e94680b7a80cd0039f01a005de01c00bb80380bd1313003a249a2f68c34c5bd20668b3a30ca002ed00801f44f4c00e8d8b001d231319b113262d68035892d48698b7a38cd12726026005d8010589b24a201d1bd3a32b37a281744c4e02e6d87201d12538039b4968cf0a64e00e84c842d54188467781a70074034259cfc68007938138039f021005d601000e792b001750ca0039d02c0073664c00ba465001cd0130039801400738c5814ba06b001740ca0039b6262de8864c00b9c63801cc8130039700e00734c4c18dd8cb001cc8d312323026005cc01c00e6189c31bb193803971a70164604e00e598b031baa5917b5b4ac2eeb694c48c886c893908d6123211a6005ca32800e540c801c880a002e4194007200285bd0cc8001718c7063714ac2463c34c00b8865001c900a0039592d0072895a19dcccb401c99938637032601e3e05a48c740800170807063714a70163c34e00e4809c01c8bd3c03904a18cee064e00e3cc8631b819080f1d0270163a04200e2c69929a50d024f4a19a165c032800b8002003c3bd6003877a636e369586cc6d29801c718d0038d19a165be32849c6c0b0918d813002df0081671264c6dc60c80d98c18d0b2dd18e0071204c49c60080918c00d002dd0080071895400e2d298798a2500ef1449a2fdba6582ce20c98db8b1901b31631a215ba05800e20098938b0101231601a0071464c6dc64c80d98c98d003891a612e1e34024c3c668856e816003880262f6a20405dd44068596f00717b591a62eeb23402cb70650016e0040038762a0070cc4c6dc692984b8e193063661ac2f6b034c2cb6c650938d013002db0080070cc4c19d9c69831b38cd0b2da194005b40102cb64c68016c8c70676e1a616db03342cb60650016c0040bad71a016dae3342cb5c650016b8041b7124a6366249402cb40650938901312312020005a001071c51898d987a561b7174a60070a64c5ecc469859678ca1230f02c24e2e04c00b3c020e38a3131b31449a1859c34c2cb38650918a00d002ce0081659a32800b3402001c2b131b711326366226342cb2863893888131231101a005940102cb24c6801648c70931c62618d906341bc7069859640c703ac801a0059001000e118946963a500c6c73141858e3402cb1c6381d6380a002c700818d8c6342cb186381d6300d002c600818d8a6402cb146381d62810002c50080070664c2cb00c6801600c70c6be4a01657c6280eaf8680015f0c70b2bd1940057a010 15 0x7fff 5 0x1f 31 0x7fffffff 13 0x1fff 0x3ff 23 5 (Nat.land parent 127) k
  | 4=>dagBucketBlock 0x2f81bd86f220000000000000000000000000000bb8aec1ba080000002e230002de20002dc1b686d62b488000b292c81b1840000002c22b0040000002be1ae8ab810002b61ad04000ac0aa84a984000a88800000029e2a706982a50a902a30a882a0127c29aa652c930e36b88aa0cb8111fc4000000000000007b9de64779000075900007489d017195bc56e85b056918000659d8a6620574a5b1162550c13474c851303fa8f643c88ea43988dc53510ce32e2c0002a20a42000000026948e62114729191c6021518000140848410102e90990187000000c 0x2824c4c008252581682294c0082264c00820958008146340081263400810628008200540081ef4c0b816c4c068169341881c0480081c03c0081ac580081af4c2380ec400081604a0081864c0081663416812c4c0081294c0081064c0081405400812c4c00810c4c1680e9400080e6400080e940008086280080c634028040340080a64c0080a6340080c94c0080cc420080a9421680894000808640037fe040027fe03400808935008066340080033416804634008043340080664c0080464c0080034c0080494c007fe32800804c42008023420080094c0080232800800c42007fe342776c2640726c26341c6c2340166c2334776be334726be328427fc658a76bc640a66bc634007fc3585f6bc340596bc334007fa058427f401c007f4010be76ac58be768c4cb876a958b876894c4876a3584876834c776ba334726ba3280876a0580876804c1c6ba034166ba028067f8040007f8034007f601c007f4f5abf76cc5abe76cc4eb976c95ab876c94e4976635a4876634e776b8334726b83280976a05a0876a04e7d6c664c7b6c6640226c634c206c6340007f2064007c8058c47f004cc37f0040427f001c007f0010027eec4c007eec40007cac38c076494cbe764940087da64c067da6407d6f434c7b6f4340226f404c206f40407d6c43347b6c4328226c4034206c4028007eec58087d864c7d6f234c226f204c027ec958027ea94c027e464c487583584875634c087580580875604c027ec94e027e264e4875a34e0875a04e027e894e027e064e4875434e0875804e4875234c487503400875204c087500404874e34208752042007d4940007d2940007ec04c007ea040427e801c007e8010007cc634877cc34077678334877e6048007e6024007d4940007d2940007e4040007e2028427e001c007e0010007def58007dcf54e6700c4ce5700934de70064cda700628e0712f4ce5716c58e66fec4cdf712940e56fe934a969033460690034007d8f4c067c0f44007dac58c076294ca968a34c6068a04c007d8c3cda784f58e0710f4ce5710c58e66fcc4ce56f8934e06f864cad68e34ca968e3346668e04c6068e034427d6340a9684334007d604060684034c074c934007d6640c074a634897d00407967a034007d555cda784c58e2714c4ce1714c40e3716958e46f894ce36f8940dc716658dd6f864cdc6f86407f70a358806f034c7f6f03402470a058256f004c246f0040b87a52504874234c48740340427d03340874204c08740040007d0034007d3250017cd251007ccf4509742c4e08742c42877c2c39017d094e007d0942bf74c64ebe74c642067b4621b974c34eb874c342007b43154973e04e4873e042007ce028007caf64c0760c58be760c4c027c0958007c094c7d6ee6587b6ee64c226ee358206ee34c007c8040057ba958007ba940427c6658007c6358007b6934007c4058007b4634007c2340a7676334007b0034057b8958007b8940007c0c54c075e94cac68864c6568834c007aa058007bec58007b6934007bc058007a8034c075ec4c027ac04c007a6034007baf5a007b8c5a007b695a4973665a4873664e427b46420973635a0873634e007b4342037ae05a027ae04ec075c94cbe75c940027aa64c007aa6407d6ec34c7b6ec340226ec04c206ec040007b2f58007a8634c075cf4c007ae64c007a66344673033406730034be75cc4e007ac64e4873434e427b03420873404e007b0042027aaf4c007ae64c007ac6344672e3340672e034017aac5a007aac4e007a895a017a665a007a664e4973235a4873234e0973205a0873204e7e6ea6587d6ea64c7b6ea640236ea358226ea34c206ea340007a0064007a434c007a204c427a234c7d6e43407b6e4334007a204c226e4040206e4034ac686640656863407d6e264c7b6e2640226e234c206e23404872434c467243340872404c06724034007a0f6448728364806e63587f6e634c4672233408728064256e6058246e604c067220344872634c4671e3340872604c0671e034007a125a4972a35a7d6e03407b6e03340972a05a226e0040206e00345c7186585179664c916da6408f6da634497183584279634c7d6da3407b6da334097180580079604c226da040206da034 14 0x3fff 5 0x1f 32 0xffffffff 13 0x1fff 0x7ff 24 5 (Nat.land parent 127) k
  | 5=>dagBucketBlock 0x9c840002310c50489050f0c00000008606000214141067e8ef911f0080000000f609e22b90d7182e109c00b7826e04d90c00000000000d60c0003406650cc70c00030856082000000000005e88b521506a943500a9f053a126054b040001222a2c6440600010c120c341028104f439a903386640c000188230820000b631642290e00009e1934200004c040001282000049040000000230642107e1800000003e047a08e831b8636040000d02190431040000bc217022d040000b01138a250846108420f061c0830205c10b0200002a084c2090210081820243000008040e080000302000008100c1000001080008000 0x85172530022e32664c1af45c68358738b06a4b7662b3213a45664174884c81af1598d9ca2b31ab9442634d68acc54e71598a5ce213143941a621c98ac68431158d0462211a063456336168ac66a2d108cd3162b1950bc56329178846502d068c573e2b02101456041028840819b1580d8022b01a80442034cc8ac054031580a406210140041a009028b60800116c0d10a2d0140045a01c7589068033120103322b3203ac4434019888080011640d10a2c0140045801c428ae0500115c071d6203203a4406341988068031100cd0062a02000454034008ad280e90f9931d620b200c43e34c198826800514c130062a820004569407487ec50310fcca0022981400452028058a72800114d8a00e29e200045494c008ab280eb0f0d00661e0202c408f45008a9885190af0e40a29ca10144f92d008a6c840113d885d61e9a1214523367282a62a330f4108022901b0b415009008a20980113cd0002270200045094c0089f2800113410002274a00044d0404289929801131930022582c0044bf4e42894c9c01128d380623e2600447c400188ac98011159010a249940044902842890680eb0e4cd1d21c9940044804019872068310e40a002241a000c44334008886500111e52002234a000c4364075874680330e810002234a021c39340a0862650030e4100c61881421c40335a186066885100ca6821819400c4003532860068011000a4c6180140044563d00886c6a011098d10a221a12143f3417486c68087104cd50e1c19a004440420087e082310d8100062081a80c3803400887280850dcca0021b814004426344287c63a850d8c70021f00e8043601c42866650030fd900021fb1a02c3e94000880c9801105901d6191a00043d0400587d280010f98a0061fe200044094c00883280870c4d00061e02000440c420087f284010f99090e191a10043c04218826010010f6500061e1a00043c32818875280010dcca0021dc9f02c366340086c638010d4ca0021a19a0043a9351986d268010e5908c618320004386340086406a870c00d16203e1c98c319373186126d190524b4621bb1b8c4366361885ec42010dccdc021b19b0043531f00868636010bcc54021881b8043003600866056e505002462194a00043234000862650a90c18d10e1801a0043001c4285ec68010bccd00217b1a234276404284ec680d09cd00021399a2142e01c0085c0201b0b71603216e260042ef580d8598b0190b31300e164ac0142c94c4684c66885098ca002168202142c01c00858020970959302e129a60042b32800856c80050a812002151a0014259580084b29801068ca00214cac2442434000832650010a004122119a0234233340083065001058ca0020a994014203581583c68001078ca00213fac0041d3340084c02001070cd00212e2601c2134c0084b8980b07cd30520b9a604414340028286508504ccd00a0d99a07413334478498b08d093130061232c0042464c0083ac680108f13002114a60042194c008480a80108fd30021032600422f4c008438982907993002104a60a41e64c0083f8988d07a530020f3260041d054008380900106ccd0220a31a0041b6400c8266380106e4d10a0c4a60041864c008358988505e530020bb260041905400831e980505f130020bca6004160540082ac8001056500020a31a0141333400828c688504d8d0020999a00413634 15 0x7fff 6 0x3f 31 0x7fffffff 12 0xfff 0x7ff 23 6 (Nat.land parent 127) k
  | 6=>dagBucketBlock 0xbf15f0af09762b8adc06d4d664b28d852b8b584ab8d586a494c600052128893b99c1cc5e531281929c9064271b68d0c6440000008aa44161e20008690002165092831c0cde9ef22779bad0000ea10000000000e820003911c44dd56d93649b020006b8b4d19e8c96640b1c58a4000611b044000bc55c9ad51646ad5551a990000a0600000013a69854b8a5492828f545a220d0c485140a1f14eae7233811ad4d246543119718b2656328a9350964465221104c7a83940000d8c62a27a11286a032214506b828c0aa0410110000004000 0x3c8e20343b8e202800974c4c0097294c0092434ced932334ec9323281c89001016918634009700400096cf440096e9407b93893446930628169143280096e94c4a92c94c7b93a64c46932640479326348587a3281690e31c0096cf584692e9341690c634469500401690a3280096a94c1b90464c16904634009620580096ac4c0096894c009666280096404c0096003400962c580096464c5e8f634c168fe32816900328168fc63400962c4e0096064e1b8f434e168f03285887694057876934238de640228de63452876328168de31c248e8c4c228da6341b8e834c168da31c248d694c228d66281b8d634c168d631c0095cc41248d49404795c9360595c636228d46281b8d43405095c336168d431c0095e03658876940228ce634168ce31c58876c40248ee94c248ec940228ca6281b8ee34c1b8ec340168ca31c58876c420095cc3e00954c380e95a94200956636228c86280095a342168c831c0095864000958940848d26407a8d23400095664c00954c4c228bc940168bc6280091663400952058469500404694e034009500280094e01c5786631c009226340094cc4c0094a94c009206280094804c7b93694c7b9349401893634c189343400091e3281893634200946f4c0094464c588743345687431c00942f4c0094064c1893e0400093e0280093c01c82932340668c0334b1882034e6842f45d5842c399384292d9391a62a7c91a629738846287c842621d591a3361891a3351c88433418842315e691a0420091a0412d88404000842009ad8880406087e0280093a640018e6040608780280093a940b28e4640588723406088001c0093804c0093603400934028019329407c91a640bd8883403c8dc040258ea340248ea334009329407c9106400092c34c258e6340018e2040009329401b8ea3280092ef440093034c0092e6480092831c0192c6400092c634238c4340228c43340192cc40248ea94c248e6940228c2328248eac420092c9421b8ea6427c9123420092a32a018e00420092a328009283344692603c0092603000924640888dc634878dc6280092203c59920c4e4692094e0092064e0191e04e0091e042009186344691c0340091c01c7687c940eb8e464c888d86401c88231c00906c38eb8e494c9c8e4940aa8be940878c464c9c8e46401c88031c009120400091a640878c66341c87e31caa8bec40a88be634588643405686431c878c4c4c9c8e4c400091a9401c87c34c238c03400091004000919250888c6940878c6934878c494c888d8940788c0640178c03400090e04000916f440090cf440091494c608660284691264c1c87a31c0091204c7287a0280090e01c00912c4000910340878c23341c8780100090e940888c2640878c26280090cc480090a0340090a32800908c4c1490294c00902628468f80284b902c4c009049580090694c008f4058468f602800904c4e4690294e0090264e008fe04e00900036008fc035008f0034468f4958008f4358008fe328008fc634008fa034008f8c4e008f694e008f434e008f2329008f0328338746342f87401c3b8cc94c008ee634008ec334a288a328888d2340a28863281c874010008ea6407a8be634ac88834c008e6340008e43341c872010008ea6403b8c6634a288831c62872940a48823281c864010008e89486187c934ac88864c008e66403b8d8634468e4642b0870640008e463662870634a387c340a287c3343b8dc940008e2640b086434cd08c0340338720403b8dc940a287e328008e2940a2878328008e0040a387cc40b086494cd08c0940148be04033872940008e0340148be040a2880028888d2640008ce6306086e628008de63e018c46356186c634008c46296086c628008dc642008c66419586c640008d8635008d0634008cc626468c0335a5870334008c003533870034008dac48018c4c40008c694c008d8940008c2628888d693e008d693d008d493c888d29356186c934008d26429586c640008d06346086a628008cec42008bcc38008cc942008ca642008c8640008c6c42008c4942008c26426086a62a87836620788be342178be042008c094060862628468be34033870634178be31d6086031c008be0355886003460866634008bc93c6085e934428ba94c008ba64c 13 0x1fff 4 0xf 32 0xffffffff 13 0x1fff 0x7ff 24 4 (Nat.land parent 127) k
  | 7=>dagBucketBlock 0x8e245980000008a1441218909384080020e3043818c0860220007ea3e15ee2f610003ccde24e3e6fa3659aa8d41698b4499a8cc16513208000c71630b145882c22608b0057e2be1000000170c0000002b6d492a2200027913669834b125452469024620000000000000221000000042980000008233f99e94eaa7233721b44d6469234099c4cc265132098c4c4261130097c4b865752a19488a044d3000130496249224091c48c24512118f907663a11c88d5000034117309a040c0000d305cc268103069825006c0000000000024001 0xa794a6694d294ca0026b826214d8010429ae6994f290cd29a52194004d704c5f948068b32900a0026c1a6004d704c7d952680f72a4cd08a54820104a90347d94e680f729ccd00a6b020004d6034089aac80fb2dcd008a5b820004d4634009a6c68013418a21e6899a3bc93328009a8c68013518d00269b1a734bbc4ce5977269bd2ed9336a5db14004d5c400699f87181312502a64c1a030498040009ab898f32500a0026a020214d301c009a602091300101225f81a00cd2f45009a587293302509226049b4fccc92d09980c84113018d89a6631094cc03422898066c0d330c54ca6002118cc00360099801201348cd0026881e034d0024009a00300533e5300267ca03ecb664c7b96cc80452d8d30825b1a0564a8340ab950668cb2a01018e5401a004ce6340099ac5001330ca00265814004cfc58c09852995925d931964b9a6004ca05800995298013358a10a67326004ce34c0099a09801330cd0026531a004cb0344697c6500d2f80a2fa60ca0604c16400099529981306501fa589a63ecb13407b962668472c41308a58820104b103402993280013264d24a57b2648cae6408f95cc68fd2bcd31f6571a03dcae3342395e098452b8100825701a11caf63c0298ec680131d8a05a641a048cad3348f95a65001320101f65681a3dcad0285c97a698932f413002634a048cab6407d956680452ac101725e32024cbc34009978080a331d9090a639a1004c70420098a651232540a002634a6494ac6407e958680472b01005a6299a004c50349892c6692f258ca2524b01a49c960287d954c80f72a98d08a551a0104aa3347d946680f728ccd0022e9943eca13407b94266801170ca2464fb202cc9e634008b6039232799023e4f31a2449b04046936068011680716e4f3202cc9e634489340808d2680d10a2d00e2dc9f6405993ec68851680700261fa20b4c43345b938650b3270c700262026004c395800984c98013098f0026080e004c1340008b2038011600710a2c00e2145801c008ae0388515c0710a2b80e004c00280097e051391ccd327a399a000455010668e0c80b3258d324a4e9a024c89040008a8020bd264d026a3a99a0045301000980068011480410a29020004bf0340098066885148100025f81a0045101c008a06500113cc70025f00e0044e01c0089a020012f8d00025f4a0014843581590268001130ca06258b2c24c7a04c488f40800112c07052250262447c03400894038911e40d00a3e8200c4b1658028f80b0071ec1300a3d820014790406d8eec98d91dd900b22498e24c7704c488ee08001124040065e4a6004bc9406d8ecc98d91d99017e24b1a24c7604c488ec080851240d0b25eb2636c746406c8e8c68012f4131263a02024474034258e0668491c0ca17e24026214480405e93a068bb2740a1b63a99a364753282c890020012f59217e241a636c733346c8e6650012f0cd0b223994004470101895869859118ca002230083647064c2c87a638911c0130021e8081a43b94031876c50610ecd00b21d98e0743b02800876020012efd205a4918e2ac4831c 13 0x1fff 4 0xf 31 0x7fffffff 12 0xfff 0x7ff 23 4 (Nat.land parent 127) k
  | 8=>dagBucketBlock 0x22186400846027c8007a40000000785d2001c9705b9654005ed715894b4b000485190011142400000000000000000000003e80000000000000000000000000ea00000000da000000000032800000c12e4aa000a1000002640000000244891e8001a800000000005a144420e4000c400000290002100019000000000000000000000000000000044000000000000024000040000000000000000000000 0x4ed34c009dac98013b6508ee74320514e231c3b9cec81593898d0ee7631a514e101c619c0c68c13818a002764a0004ec930009d4c800139a4d40274b1a444e662a469d6654013ac0aa2275313004ea625009d2c48c33818d00274320004e7634619c1268013a19000273b1a30ce0936009cd2640138e4b00272b1b004e4634009c8c68c137cc700271ca03ace1334199c206803388d00027119a214e231c009c40394337ccd0027081a004e1340009c32680b3818d0027018e21cdf028009c06646337d900c66fc9a004df629009bcc508d370cd10a6e194024db334009ba02001375930026d19a004dc010009b98980136e530026d824004da048009b5898013658a0026cb26004d9048 10 0x3ff 3 0x7 31 0x7fffffff 12 0xfff 0x7ff 23 3 (Nat.land parent 127) k
  | 9=>dagBucketBlock 0x1806f8dd200000000000b2955000000000000000000000000051400138c0000096728400000000000000000000000000000000000000922000000008a910618c1200000000000000e25a232200000000000000000000000000000031100000180800000bc4000005c2acd50a2838c64c000002e4584a89410000009880000000000000000484000000000000000022200000000202000788001c200068894102188288410440000000002200000001 0x1dcfe028009fc6508d3f8c70027f00e33cfc634659f8c50bd3f0cd1667e194124fd634229f8638373f40d05a7e008004fc634d09f6669113f0c70027e80e004fb6293b9f663da13ec078027db1a234fc328009f8050013ed891f67701a4fcfa030269f40480d3e8060027d006134fa334009f4650853e5900027c9a04a4f5640919ecc691f3d58a2027a9a03ecf63347b9ea6504b3d41008a7b01a104f5028029f0650013e0c72467a01447cf401c169f0668013e00d05a7998e0b4f1328009ee098013de500027bb200dced340169da650013de500027aca0124eb640479eac500b3d4ca08a7598e0dceb040509ea0502d3ac0419e75ca0004f6634229ccc50bd3acd005a7318e004f50345e9d7260013d18d08a7298e114e3934169c6c50013c0ca1de77194004ee328009e4638c13840708e7219a004f3c3c009e4080013c4ca0027881a004f004c009dc0682d3b80a1de7700e004efc38879c8680393840421e724a043ce4640009df898013b80d00276826004ed94c 11 0x7ff 4 0xf 31 0x7fffffff 12 0xfff 0x7ff 23 4 (Nat.land parent 127) k
  | _=>k (fun _=>none)
theorem k6_64_t1BucketsValid : BucketsValid k6_64_t1Buckets:=by
  intro parent k h
  unfold k6_64_t1Buckets at h
  split at h <;> first | exact dagBucketBlock_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h | exact ⟨fun _=>none,h⟩
noncomputable def k6_64_t1Tags:=fDagTraceTags k6_64_t1Mask 60 (dagTagBases1 k6_64_t1Stock 0x80448006c403308b82b00012c52c102bc3314042cd8c00598cd8889a85244614227d113428350205eb2320007f 0x6010826c40000000107301284200080000418028580008200000110852030c000800030281010e8040000005e 60) 13 k6_64_t1Data
noncomputable def k6_64_t1States:=fDagTrace k6_64_t1Mask k6_64_t1Stock 13 1 k6_64_t1Data
noncomputable def k6_64_t1Light:=fDagTraceLight k6_64_t1Mask k6_64_t1Stock 13 1 k6_64_t1Data
def k6_64_t1Gens : List WordMove:=[[s64_01],[s64_02],[s64_03],[s64_04],[s64_05],[s64_12],[s64_13],[s64_14],[s64_15],[s64_23],[s64_24],[s64_25],[s64_34],[s64_35],[s64_45]]
def k6_64_t1MovesFn : DagMovesFn1 :=
  fPackedMovesFn k6_64_t1Gens 0xeb639d96e57b2e0a86d3940db829d94e540260d865414edb72a0010680358d8064130ed7281d4a9002d4df64aa50cb52801502c3260676cb8decb61a1b4c303660e005b1beda82a196e5032e0a76d3950ca728192c30002cd06cb840c9839d96c7402a09875b94eda54a1b2e93b260ef6d3250cb6381d505002dc980631b0007241b4a93b2d4e864a9c0eb528014a4fb2a0686db8c0e9818012e2fb6d8686530cecb83a1d7050029c98002920096161db4900365187649c000b2401d44c3b65200649b000a2401da8c0030d00071200002200122832dc2764b85ed980a192e103ad8200530300950601902c3b5c600040a00e71601ac2c3b186764c150d9728012e4c0294d87640c00d71601d02c001c5076b0c00c6161b5073b660a864b940095261db030031c580730b00061400146800004865c04eda70a1b2c13b2582f65c050da7081d7010029c1f6cb050c9609db7014329c2074b0400960601aa0c3b54200628300e506000a0bb2a1286db9c0e9848012e6fb6d8a8653140d9849d92e743a98a06d424ecb73bdb3094325ce075b1400a6261d8e703b61200639b0006241b6a33b2946f6da8d0ca5181d2a3002545f6dc250ca7381d2c500258987628c0ed518018a2c001450764840ecb0801b40c03ac180648300db061d94103b6c200650300e90600120803b41800602000e04000004002a10764c400d9761db4d003299807643000d740000e403b598006320ecb580016c803a99806d430ecb7801d6cc002990006c200ec7601db0c0031d00003100db561d94b03b6d600652b00e9560012a83b2e2006d3b00eb860014e83b65a0064b30edb880194ec03a598004b2000d5401d8ac03b5580062a000e540000a40032d000059000ea4001b2803b2d8006d2000eb400014403b6580064a000db401d94c03b6d800652000e9400012400034800762000ed400018400038800000 240 23 0x7fffff 4 0xf
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6_64_t1GensOK : ∀ m ∈ k6_64_t1Gens,MoveAutoOK k6_64_t1Mask k6_64_t1Goal 64 m:=by
  simp only [k6_64_t1Gens,List.mem_cons,List.not_mem_nil,or_false]
  intro m hm;rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 1) (inv:=fSwapBits 0 1) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 2) (inv:=fSwapBits 0 2) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 3) (inv:=fSwapBits 0 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 4) (inv:=fSwapBits 0 4) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 0 5) (inv:=fSwapBits 0 5) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 2) (inv:=fSwapBits 1 2) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 3) (inv:=fSwapBits 1 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 4) (inv:=fSwapBits 1 4) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 1 5) (inv:=fSwapBits 1 5) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 2 3) (inv:=fSwapBits 2 3) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 2 4) (inv:=fSwapBits 2 4) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 2 5) (inv:=fSwapBits 2 5) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 3 4) (inv:=fSwapBits 3 4) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 3 5) (inv:=fSwapBits 3 5) (by decide +kernel)
  · exact moveAutoOK_of_check (sel:=fSwapBits 4 5) (inv:=fSwapBits 4 5) (by decide +kernel)
theorem k6_64_t1Autos : DagMovesFnOK1 k6_64_t1Mask k6_64_t1Goal 64 k6_64_t1MovesFn :=
  dagMovesFnOK1OfPackedGens (by unfold Masked;decide +kernel) (by unfold Masked;decide +kernel) k6_64_t1GensOK
def k6_64_t1Cuts : List ExactBound:=[k5_0Fact,k5_1Fact,k5_2Fact,k5_3Fact,k5_4Fact,k5_5Fact,k4_0_1Fact,k4_0_2Fact,k4_0_3Fact,k4_0_4Fact,k4_0_5Fact,k4_1_2Fact,k4_1_3Fact,k4_1_4Fact,k4_1_5Fact,k4_2_3Fact,k4_2_4Fact,k4_2_5Fact,k4_3_4Fact,k4_3_5Fact,k4_4_5Fact]
theorem k6_64_t1Known : ExactKnown k6_64_t1Cuts:=extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (show ExactKnown [] from fun _ h=>False.elim (List.not_mem_nil h)) k4_64_t0Lower k4_64_t1Lower) k4_3_5_t0Lower k4_3_5_t1Lower) k4_3_4_t0Lower k4_3_4_t1Lower) k4_2_5_t0Lower k4_2_5_t1Lower) k4_2_4_t0Lower k4_2_4_t1Lower) k4_2_3_t0Lower k4_2_3_t1Lower) k4_1_5_t0Lower k4_1_5_t1Lower) k4_1_4_t0Lower k4_1_4_t1Lower) k4_1_3_t0Lower k4_1_3_t1Lower) k4_1_2_t0Lower k4_1_2_t1Lower) k4_0_5_t0Lower k4_0_5_t1Lower) k4_0_4_t0Lower k4_0_4_t1Lower) k4_0_3_t0Lower k4_0_3_t1Lower) k4_0_2_t0Lower k4_0_2_t1Lower) k4_0_1_t0Lower k4_0_1_t1Lower) k5_64_t0Lower k5_64_t1Lower) k5_4_t0Lower k5_4_t1Lower) k5_3_t0Lower k5_3_t1Lower) k5_2_t0Lower k5_2_t1Lower) k5_1_t0Lower k5_1_t1Lower) k5_0_t0Lower k5_0_t1Lower
noncomputable def k6_64_t1Check:=fDagCheckNode 2 64 6 false k6_64_t1Mask k6_64_t1Goal k6_64_t1Chart (fExactKnownCloses true k6_64_t1Goal k6_64_t1Cuts) 1279 k6_64_t1Data k6_64_t1States k6_64_t1Light k6_64_t1MovesFn k6_64_t1Buckets k6_64_t1Sample k6_64_t1Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6_64_t1Roots : fDagCheckRoots 2 false k6_64_t1Mask k6_64_t1Goal k6_64_t1Chart (fExactKnownCloses true k6_64_t1Goal k6_64_t1Cuts) k6_64_t1Wit 1279 k6_64_t1Data k6_64_t1Light k6_64_t1MovesFn k6_64_t1Buckets k6_64_t1Stock 13 1=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6_64_t1B0 : treeBlock 0 256 k6_64_t1Check=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6_64_t1B256 : treeBlock 256 256 k6_64_t1Check=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6_64_t1B512 : treeBlock 512 256 k6_64_t1Check=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6_64_t1B768 : treeBlock 768 256 k6_64_t1Check=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6_64_t1B1024 : treeBlock 1024 255 k6_64_t1Check=true:=by decide +kernel
theorem k6_64_t1Blocks : treeBlock 0 1279 k6_64_t1Check=true:=(@treeBlock_merge 0 512 767 k6_64_t1Check (@treeBlock_merge 0 256 256 k6_64_t1Check k6_64_t1B0 k6_64_t1B256) (@treeBlock_merge 512 256 511 k6_64_t1Check k6_64_t1B512 (@treeBlock_merge 768 256 255 k6_64_t1Check k6_64_t1B768 k6_64_t1B1024)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k6_64_t1Lower : ExactLower k6_64_t1Mask k6_64_t1Stock k6_64_t1Goal 1 14:=by
  apply exactLowerDagFast (maxK:=2) (stride:=64) (steps:=6)
    (is24:=false) (allowNotInPast:=true) (width:=64)
    (sample:=k6_64_t1Sample) (tags:=k6_64_t1Tags)
    (by decide) (sampleValidOfCheck (by decide +kernel)) (fun h=>Bool.noConfusion h) (by decide) _ _ _ k6_64_t1Autos k6_64_t1BucketsValid _ _ _ k6_64_t1Known _ _ k6_64_t1Roots k6_64_t1Blocks
  · unfold Masked;decide +kernel
  · unfold Masked;decide +kernel
  · exact chartOfCheck (chart:=k6_64_t1Chart) (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold k6_64_t1Stock;decide +kernel
  · decide +kernel
  · simp only [k6_64_t1Cuts,List.mem_cons,List.not_mem_nil,or_false];intro b h;rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · simp only [k6_64_t1Cuts,List.mem_cons,List.not_mem_nil,or_false];intro b h;rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact stockMaskedOfCheck (by decide +kernel)
def cutK6_0Mask : Word:=0x55555555555555555555555555555555
def cutK6_0Goal : Word:=0x55555555555555545555555455545440
def cutK6_0Stock : List Word:=[0x44444444444444444444444444444444,0x50505050505050505050505050505050,0x55005500550055005500550055005500,0x55550000555500005555000055550000,0x55555555000000005555555500000000,0x55555555555555550000000000000000]
def cutK6_0Fact : ExactBound:=(cutK6_0Mask,cutK6_0Stock,13,14,cutK6_0Goal)
def mapK6_0 (i : Fin 64) : Fin 128:=Fin.ofNat 128 (permuteAxes [1,2,3,4,5,6] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_0_t0Lower : ExactLower cutK6_0Mask cutK6_0Stock cutK6_0Goal 0 13 :=
  exactLowerProjectInj mapK6_0 (by decide +kernel) k6_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_0_t1Lower : ExactLower cutK6_0Mask cutK6_0Stock cutK6_0Goal 1 14 :=
  exactLowerProjectInj mapK6_0 (by decide +kernel) k6_64_t1Lower
def cutK6_1Mask : Word:=0x33333333333333333333333333333333
def cutK6_1Goal : Word:=0x33333333333333323333333233323220
def cutK6_1Stock : List Word:=[0x22222222222222222222222222222222,0x30303030303030303030303030303030,0x33003300330033003300330033003300,0x33330000333300003333000033330000,0x33333333000000003333333300000000,0x33333333333333330000000000000000]
def cutK6_1Fact : ExactBound:=(cutK6_1Mask,cutK6_1Stock,13,14,cutK6_1Goal)
def mapK6_1 (i : Fin 64) : Fin 128:=Fin.ofNat 128 (permuteAxes [0,2,3,4,5,6] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_1_t0Lower : ExactLower cutK6_1Mask cutK6_1Stock cutK6_1Goal 0 13 :=
  exactLowerProjectInj mapK6_1 (by decide +kernel) k6_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_1_t1Lower : ExactLower cutK6_1Mask cutK6_1Stock cutK6_1Goal 1 14 :=
  exactLowerProjectInj mapK6_1 (by decide +kernel) k6_64_t1Lower
def cutK6_2Mask : Word:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def cutK6_2Goal : Word:=0xf0f0f0f0f0f0f0e0f0f0f0e0f0e0e08
def cutK6_2Stock : List Word:=[0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0xf000f000f000f000f000f000f000f00,0xf0f00000f0f00000f0f00000f0f0000,0xf0f0f0f000000000f0f0f0f00000000,0xf0f0f0f0f0f0f0f0000000000000000]
def cutK6_2Fact : ExactBound:=(cutK6_2Mask,cutK6_2Stock,13,14,cutK6_2Goal)
def mapK6_2 (i : Fin 64) : Fin 128:=Fin.ofNat 128 (permuteAxes [0,1,3,4,5,6] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_2_t0Lower : ExactLower cutK6_2Mask cutK6_2Stock cutK6_2Goal 0 13 :=
  exactLowerProjectInj mapK6_2 (by decide +kernel) k6_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_2_t1Lower : ExactLower cutK6_2Mask cutK6_2Stock cutK6_2Goal 1 14 :=
  exactLowerProjectInj mapK6_2 (by decide +kernel) k6_64_t1Lower
def cutK6_3Mask : Word:=0xff00ff00ff00ff00ff00ff00ff00ff
def cutK6_3Goal : Word:=0xff00ff00ff00fe00ff00fe00fe00e8
def cutK6_3Stock : List Word:=[0xaa00aa00aa00aa00aa00aa00aa00aa,0xcc00cc00cc00cc00cc00cc00cc00cc,0xf000f000f000f000f000f000f000f0,0xff000000ff000000ff000000ff0000,0xff00ff0000000000ff00ff00000000,0xff00ff00ff00ff0000000000000000]
def cutK6_3Fact : ExactBound:=(cutK6_3Mask,cutK6_3Stock,13,14,cutK6_3Goal)
def mapK6_3 (i : Fin 64) : Fin 128:=Fin.ofNat 128 (permuteAxes [0,1,2,4,5,6] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_3_t0Lower : ExactLower cutK6_3Mask cutK6_3Stock cutK6_3Goal 0 13 :=
  exactLowerProjectInj mapK6_3 (by decide +kernel) k6_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_3_t1Lower : ExactLower cutK6_3Mask cutK6_3Stock cutK6_3Goal 1 14 :=
  exactLowerProjectInj mapK6_3 (by decide +kernel) k6_64_t1Lower
def cutK6_4Mask : Word:=0xffff0000ffff0000ffff0000ffff
def cutK6_4Goal : Word:=0xffff0000fffe0000fffe0000fee8
def cutK6_4Stock : List Word:=[0xaaaa0000aaaa0000aaaa0000aaaa,0xcccc0000cccc0000cccc0000cccc,0xf0f00000f0f00000f0f00000f0f0,0xff000000ff000000ff000000ff00,0xffff000000000000ffff00000000,0xffff0000ffff0000000000000000]
def cutK6_4Fact : ExactBound:=(cutK6_4Mask,cutK6_4Stock,13,14,cutK6_4Goal)
def mapK6_4 (i : Fin 64) : Fin 128:=Fin.ofNat 128 (permuteAxes [0,1,2,3,5,6] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_4_t0Lower : ExactLower cutK6_4Mask cutK6_4Stock cutK6_4Goal 0 13 :=
  exactLowerProjectInj mapK6_4 (by decide +kernel) k6_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_4_t1Lower : ExactLower cutK6_4Mask cutK6_4Stock cutK6_4Goal 1 14 :=
  exactLowerProjectInj mapK6_4 (by decide +kernel) k6_64_t1Lower
def cutK6_5Mask : Word:=0xffffffff00000000ffffffff
def cutK6_5Goal : Word:=0xfffffffe00000000fffefee8
def cutK6_5Stock : List Word:=[0xaaaaaaaa00000000aaaaaaaa,0xcccccccc00000000cccccccc,0xf0f0f0f000000000f0f0f0f0,0xff00ff0000000000ff00ff00,0xffff000000000000ffff0000,0xffffffff0000000000000000]
def cutK6_5Fact : ExactBound:=(cutK6_5Mask,cutK6_5Stock,13,14,cutK6_5Goal)
def mapK6_5 (i : Fin 64) : Fin 128:=Fin.ofNat 128 (permuteAxes [0,1,2,3,4,6] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_5_t0Lower : ExactLower cutK6_5Mask cutK6_5Stock cutK6_5Goal 0 13 :=
  exactLowerProjectInj mapK6_5 (by decide +kernel) k6_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_5_t1Lower : ExactLower cutK6_5Mask cutK6_5Stock cutK6_5Goal 1 14 :=
  exactLowerProjectInj mapK6_5 (by decide +kernel) k6_64_t1Lower
def cutK6_6Mask : Word:=0xffffffffffffffff
def cutK6_6Goal : Word:=0xfffffffefffefee8
def cutK6_6Stock : List Word:=[0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def cutK6_6Fact : ExactBound:=(cutK6_6Mask,cutK6_6Stock,13,14,cutK6_6Goal)
def mapK6_6 (i : Fin 64) : Fin 128:=Fin.ofNat 128 (permuteAxes [0,1,2,3,4,5] 0 i.val)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_6_t0Lower : ExactLower cutK6_6Mask cutK6_6Stock cutK6_6Goal 0 13 :=
  exactLowerProjectInj mapK6_6 (by decide +kernel) k6_64_t0Lower
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cutK6_6_t1Lower : ExactLower cutK6_6Mask cutK6_6Stock cutK6_6Goal 1 14 :=
  exactLowerProjectInj mapK6_6 (by decide +kernel) k6_64_t1Lower
def k7_128_t1Mask : Word:=0xffffffffffffffffffffffffffffffff
def k7_128_t1Goal : Word:=0xfffffffffffffffefffffffefffefee8
def k7_128_t1Stock : List Word:=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
def k7_128_t1Chart : Option RowChart:=some ⟨[3,5,6,9,10,12,17,18,20,24,33,34,1,2,4,8,16,32,64,1,1,1,1,1],rfl⟩
def k7_128_t1Wit : List Witness:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,3,2),(0xcccccccccccccccccccccccccccccccc,3,1),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,1),(0xff00ff00ff00ff00ff00ff00ff00ff00,9,1),(0xffff0000ffff0000ffff0000ffff0000,17,1),(0xffffffff00000000ffffffff00000000,33,1),(0xffffffffffffffff0000000000000000,65,1)]
def k7_128_t1Sample : DagSample1:=(0x4024100a040302011080482014080604021100884024100a0403020104804220110804820140806002018080c020500824021101018040a01048080c020501018004060102804120108804420201402410088402110082402050100c0203,42)
def k7_128_t1Data : Forest:=fun i=>fDecodeNode 1 8 0xfe i
def k7_128_t1Buckets : DagBuckets1 :=
  dagBucketBlock 0x1 0x7f 2 0x3 1 0x1 9 0x1ff 7 0x7f 0x1 8 1
theorem k7_128_t1BucketsValid : BucketsValid k7_128_t1Buckets :=
  dagBucketBlock_valid 0x1 0x7f 2 0x3 1 0x1 9 0x1ff 7 0x7f 0x1 8 1
noncomputable def k7_128_t1Tags:=fDagTraceTags k7_128_t1Mask 42 (dagTagBases1 k7_128_t1Stock 0x3f09614001f044a8880784224c410e22111c20209108f8108448842007c0e44200000ff 0x3f00000001f00008000780000c000e00001c00000000f8008000000007c08000000007d 42) 15 k7_128_t1Data
noncomputable def k7_128_t1States:=fDagTrace k7_128_t1Mask k7_128_t1Stock 15 1 k7_128_t1Data
noncomputable def k7_128_t1Light:=fDagTraceLight k7_128_t1Mask k7_128_t1Stock 15 1 k7_128_t1Data
def k7_128_t1MovesFn : DagMovesFn1:=fun _=>none
theorem k7_128_t1Autos : DagMovesFnOK1 k7_128_t1Mask k7_128_t1Goal 128 k7_128_t1MovesFn:=fun _ _ h=>nomatch h
def k7_128_t1Cuts : List ExactBound:=[cutK6_0Fact,cutK6_1Fact,cutK6_2Fact,cutK6_3Fact,cutK6_4Fact,cutK6_5Fact,cutK6_6Fact]
theorem k7_128_t1Known : ExactKnown k7_128_t1Cuts:=extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (extendExactKnown (show ExactKnown [] from fun _ h=>False.elim (List.not_mem_nil h)) cutK6_6_t0Lower cutK6_6_t1Lower) cutK6_5_t0Lower cutK6_5_t1Lower) cutK6_4_t0Lower cutK6_4_t1Lower) cutK6_3_t0Lower cutK6_3_t1Lower) cutK6_2_t0Lower cutK6_2_t1Lower) cutK6_1_t0Lower cutK6_1_t1Lower) cutK6_0_t0Lower cutK6_0_t1Lower
noncomputable def k7_128_t1Check:=fDagCheckNode 2 128 6 false k7_128_t1Mask k7_128_t1Goal k7_128_t1Chart (fExactKnownCloses true k7_128_t1Goal k7_128_t1Cuts) 1 k7_128_t1Data k7_128_t1States k7_128_t1Light k7_128_t1MovesFn k7_128_t1Buckets k7_128_t1Sample k7_128_t1Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k7_128_t1Roots : fDagCheckRoots 2 false k7_128_t1Mask k7_128_t1Goal k7_128_t1Chart (fExactKnownCloses true k7_128_t1Goal k7_128_t1Cuts) k7_128_t1Wit 1 k7_128_t1Data k7_128_t1Light k7_128_t1MovesFn k7_128_t1Buckets k7_128_t1Stock 15 1=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k7_128_t1B0 : treeBlock 0 1 k7_128_t1Check=true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k7_128_t1Lower : ExactLower k7_128_t1Mask k7_128_t1Stock k7_128_t1Goal 1 16:=by
  apply exactLowerDagFast (maxK:=2) (stride:=128) (steps:=6)
    (is24:=false) (allowNotInPast:=true) (width:=128)
    (sample:=k7_128_t1Sample) (tags:=k7_128_t1Tags)
    (by decide) (sampleValidOfCheck (by decide +kernel)) (fun h=>Bool.noConfusion h) (by decide) _ _ _ k7_128_t1Autos k7_128_t1BucketsValid _ _ _ k7_128_t1Known _ _ k7_128_t1Roots k7_128_t1B0
  · unfold Masked;decide +kernel
  · unfold Masked;decide +kernel
  · exact chartOfCheck (chart:=k7_128_t1Chart) (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold k7_128_t1Stock;decide +kernel
  · decide +kernel
  · simp only [k7_128_t1Cuts,List.mem_cons,List.not_mem_nil,or_false];intro b h;rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · simp only [k7_128_t1Cuts,List.mem_cons,List.not_mem_nil,or_false];intro b h;rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact stockMaskedOfCheck (by decide +kernel)
def raw128 : List (BitVec 128):=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
def goal128 : BitVec 128:=0xfffffffffffffffefffffffefffefee8
def raw128Words : List Word:=raw128.map BitVec.toNat
def monoCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or,[0,1]⟩,⟨.and,[0,1]⟩,⟨.or,[2,3]⟩,⟨.and,[2,3]⟩,⟨.or,[4,5]⟩,⟨.and,[4,5]⟩,⟨.or,[7,9]⟩,⟨.and,[7,9]⟩,⟨.and,[13,11]⟩,⟨.or,[13,11]⟩,⟨.and,[16,6]⟩,⟨.or,[8,10]⟩,⟨.or,[12,14]⟩,⟨.or,[15,17]⟩,⟨.or,[18,19]⟩,⟨.or,[20,21]⟩],22⟩
def target10452 : (Fin 7 → Bool) → Bool:=fun x : Fin 7 → Bool=>decide (∃ i < ([0,1,0,2,1,2,0,3,1,3,2,3,0,4,1,4,2,4,3,4,0,5,1,5,2,5,3,5,4,5,0,6,1,6,2,6,3,6,4,6,5,6] : List ℕ).length / 2,(List.ofFn x).getD (([0,1,0,2,1,2,0,3,1,3,2,3,0,4,1,4,2,4,3,4,0,5,1,5,2,5,3,5,4,5,0,6,1,6,2,6,3,6,4,6,5,6] : List ℕ).getD (2*i) 0) false=true ∧ (List.ofFn x).getD (([0,1,0,2,1,2,0,3,1,3,2,3,0,4,1,4,2,4,3,4,0,5,1,5,2,5,3,5,4,5,0,6,1,6,2,6,3,6,4,6,5,6] : List ℕ).getD (2*i+1) 0) false=true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem raw128OK : hcsCheckPow (fun r=>(raw128.map fun v=>v.getLsbD r)==List.ofFn fun j : Fin 7=>r.testBit j.val) 7 0=true:=by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem goal128OK : hcsCheckPow (fun r=>goal128.getLsbD r==target10452 (fun j : Fin 7=>r.testBit j.val)) 7 0=true:=by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k7_128_t1Raw : ExactLower (fullMask 128) raw128Words goal128.toNat 1 16:=by
  intro k S live hS
  apply k7_128_t1Lower k S (by simpa [k7_128_t1Mask,k7_128_t1Goal,fullMask,goal128] using live)
  intro w hw
  have h1:=hS w hw
  rcases h1 with rfl | h1 | h1
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (by simpa [k7_128_t1Mask,fullMask] using h1))
  · have hm : availableB k7_128_t1Mask k7_128_t1Stock w=true :=
      List.all_eq_true.mp (by decide +kernel : raw128Words.all (fun u=>availableB k7_128_t1Mask k7_128_t1Stock u)=true) w h1
    exact availableB_spec.mp hm
end PEqualNP.Outside.L_meta_10452
open PEqualNP.Outside.L_meta_10452 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_10452 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 1, 0, 2, 1, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1, 0, 2, 1, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1, 0, 2, 1, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 1, 0, 2, 1, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1, 0, 2, 1, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1, 0, 2, 1, 2, 0, 3, 1, 3, 2, 3, 0, 4, 1, 4, 2, 4, 3, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates out legal oneNot computes
  have hfan : PEqualNP.MetaComplexity.FanInTwo ⟨gates, out⟩ := by
    intro g hg; exact legal g hg
  have hev : (gates.foldl hcsStep raw128).getD out 0 = goal128 :=
    hcsEvalWord raw128 goal128 target10452 raw128OK goal128OK ⟨gates, out⟩ hfan computes
  have hhit : goal128.toNat ∈ (gates.foldl hcsStep raw128).map BitVec.toNat := by
    rw [List.getD_eq_getElem?_getD] at hev
    cases h : (gates.foldl hcsStep raw128)[out]? with
    | none =>
      rw [h] at hev
      have hne : (0 : BitVec 128) ≠ goal128 := by decide +kernel
      exact False.elim (hne hev)
    | some v =>
      rw [h] at hev
      exact List.mem_map.mpr ⟨v, List.mem_of_getElem? h, congrArg BitVec.toNat hev⟩
  obtain ⟨k, t, S, hk, ht, hlive, hsub⟩ := hcsExtractExact raw128 gates goal128.toNat legal (by unfold properWord; decide +kernel) hhit
  have ht1 : t ≤ 1 := Nat.le_trans ht (notCountLeOne oneNot)
  by_cases ht0 : t = 0
  · subst ht0
    obtain ⟨gs', o', hleg', hlen', heval'⟩ := liveWordToMonoCircuit raw128 goal128 hlive hsub
    have hfan' : PEqualNP.MetaComplexity.FanInTwo ⟨gs', o'⟩ := by
      intro g hg
      have h := hleg' g hg
      exact ⟨by rcases h.1 with h1 | h1; exact Or.inl h1; exact Or.inr (Or.inl h1), h.2⟩
    refine ⟨gs', o', hleg', Nat.le_trans hlen' hk, ?_⟩
    exact hcsWitnessEval raw128 goal128 ⟨gs', o'⟩ target10452 hfan' raw128OK goal128OK heval'
  · have ht1eq : t = 1 := by omega
    subst ht1eq
    have size : 16 ≤ gates.length := Nat.le_trans (k7_128_t1Raw k S hlive (fun w hw => Or.inr (Or.inr (hsub w hw)))) hk
    have monoEval : ∀ x, monoCircuit.eval (List.ofFn x) = target10452 x := by
      intro x
      have clean : PEqualNP.MetaComplexity.FanInTwo monoCircuit := by
        intro gate member
        simp only [monoCircuit, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      exact hcsWitnessEval raw128 goal128 monoCircuit target10452 clean raw128OK goal128OK (by decide +kernel) x
    refine ⟨monoCircuit.gates, monoCircuit.output, ?_, ?_, monoEval⟩
    · intro gate member
      simp only [monoCircuit, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · exact Nat.le_trans (by decide +kernel : monoCircuit.gates.length ≤ 16) size
