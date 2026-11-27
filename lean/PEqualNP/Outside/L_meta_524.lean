import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.G524

abbrev B := BitVec 234
abbrev Sig := B × B
def top : B := BitVec.allOnes 234
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n=k-t then
    base == top && !(v.contains g) && g != zero && g != one && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && !(v.contains g) && g != zero && g != one && r (g::(h++rest)))

def before (a b : Sig) : Bool :=
  if a.1 = b.1 then decide (a.2.toNat < b.2.toNat) else decide (a.1.toNat < b.1.toNat)


def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  v.any (unaryAt k t r v (coverage (decide (0<t)) v))

def binarySlow (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  before a b &&
    (let rest := dropped [a,b] v
     let keep := [[],[a],[b],[a,b]]
     let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
     tryGate k t r v rest (v.length-2) mask (bin false a b) keep || tryGate k t r v rest (v.length-2) mask (bin true a b) keep)

def tightBinary (r : List Sig → Bool) (v : List Sig) (u : B) (a b : Sig) : Bool :=
  let ua := u &&& sep false a
  let ub := u &&& sep false b
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => !(v.contains g) && g != zero && g != one && r (g::rest)
  ((((ua &&& ~~~b.1) ||| (ub &&& ~~~a.1)) == 0) && use (bin false a b)) ||
    ((((ua &&& b.2) ||| (ub &&& a.2)) == 0) && use (bin true a b))

def binaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  if t=0 ∧ v.length-2=k then before a b && tightBinary r v c.2.1 a b
  else binarySlow k t r v c a b

private theorem need_unique (c : Cov) (a b : Sig) (op : Bool)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  cases op <;> simp only [sep,bin,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

private theorem fast_accept {k t r v c a b}
    (h : binarySlow k t r v c a b=true) : binaryAt k t r v c a b=true := by
  unfold binaryAt
  split
  · rename_i cut
    obtain ⟨rfl,hn⟩ := cut
    obtain ⟨ho,hs⟩ := Bool.and_eq_true_iff.mp h
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ho,?_⟩
    simp only [tryGate,Nat.sub_zero,hn,ite_true,Nat.lt_irrefl,decide_false,Bool.or_eq_true,Bool.and_eq_true,
      beq_iff_eq] at hs
    simp only [tightBinary,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq]
    rcases hs with z | z
    · exact Or.inl ⟨need_unique c a b false z.1.1.1.1,⟨⟨⟨z.1.1.1.2,z.1.1.2⟩,z.1.2⟩,z.2⟩⟩
    · exact Or.inr ⟨need_unique c a b true z.1.1.1.1,⟨⟨⟨z.1.1.1.2,z.1.1.2⟩,z.1.2⟩,z.2⟩⟩
  · exact h

private theorem fast_mono {k t v c a b} {r s : List Sig → Bool}
    (h : ∀ w, r w = true → s w = true)
    (hslow : binarySlow k t r v c a b=true → binarySlow k t s v c a b=true)
    (hr : binaryAt k t r v c a b=true) : binaryAt k t s v c a b=true := by
  by_cases hcut : t=0 ∧ v.length-2=k
  · simp only [binaryAt,if_pos hcut,tightBinary,Bool.and_eq_true,Bool.or_eq_true] at hr ⊢
    obtain ⟨order,z⟩ := hr
    refine ⟨order,?_⟩
    rcases z with ⟨p,hp,hr⟩ | ⟨p,hp,hr⟩
    · exact Or.inl ⟨p,hp,h _ hr⟩
    · exact Or.inr ⟨p,hp,h _ hr⟩
  · simpa only [binaryAt,if_neg hcut] using hslow (by simpa only [binaryAt,if_neg hcut] using hr)

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  v.any (fun a => v.any (binaryAt k t r v (coverage (decide (0<t)) v) a))

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v.contains target
  | k+1,t,v =>
    if t>k+1 ∨ v.length>k+1-t+1 then false else
    v.contains target ||
    (decide (0<t) && unaryMoves k (t-1) (search k (t-1)) v) ||
    binaryMoves k t (search k t) v

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



def raw0 : Sig := (1847655313251220544174144638083628675537233864338544456384253857366271,2647491097202568450281102938848811747079)
def raw1 : Sig := (5081117006528930417956861017432526512659121059022980364858440586166271,1630237251090298572320907102247708482548136075986118781369619374436464)
def raw2 : Sig := (26099068884698998779587054804376199319272113572626408984505128274886400,25881598165990606097053739310014828128206532127222293360978057220557707)
def raw3 : Sig := (7373506023848867606014770477350846687514289768518094712061295113207808,13427419630041409956817114808927030898647973802775249480860128523316)
def raw4 : Sig := (27597086059167223923429580669777265354755006441276275573446065921196032,27593505413828777861677506010500376504505397954246757416213640611217857)
def raw5 : Sig := (14727320398207244391514452096299415634572787867032637614307708520890368,102843936752860762217842195118570266655352902452327425930829342)
def raw6 : Sig := (27606985339161650498107229328681154914630997669573749460764629179301888,27606985284318220317175337827477618980349778682598989137156052294361312)
def raw7 : Sig := (27606985387162255149727331436010821033497654093972752196513164534218752,27606985387162255149727331436009454586458806410019833896855713277868280)

def raw : List Sig := [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U))

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 234
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 234 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 234
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 234 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 234)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 234) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 234 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 234)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

private lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

private lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,ha,hp.1,hp.2,hr] at *
  · simp only [tryGate,if_neg tight,Bool.and_eq_true,bne_iff_ne,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not,
      List.any_eq_true,decide_eq_true_eq,beq_iff_eq]
    exact ⟨h,hh,⟨⟨⟨⟨hl,cov⟩,ha⟩,hp.1⟩,hp.2⟩,hr⟩

private lemma ordered {a b : Sig} (h : a≠b) : before a b = true ∨ before b a = true := by
  by_cases e : a.1=b.1
  · have h2 : a.2.toNat≠b.2.toNat := fun h2 => h (Prod.ext e (BitVec.eq_of_toNat_eq h2))
    simp [before,e]; omega
  · have h1 : a.1.toNat≠b.1.toNat := fun h1 => e (BitVec.eq_of_toNat_eq h1)
    simp [before,e,Ne.symm e]; omega

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (l : Live m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → search k t v = true) :
    unaryMoves k t (search k t) v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (ord : before a b=true) (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → search k t v = true) :
    binaryMoves k t (search k t) v = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have ok := gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)
  apply List.any_eq_true.mpr
  refine ⟨a,ah,List.any_eq_true.mpr ⟨b,bh,fast_accept (Bool.and_eq_true_iff.mpr ⟨ord,?_⟩)⟩⟩
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  dsimp only
  rw [hlen,hmask]
  cases d
  · exact Bool.or_eq_true_iff.mpr (Or.inl ok)
  · exact Bool.or_eq_true_iff.mpr (Or.inr ok)

private lemma search_complete {m t S} (l : Live m t S) (K : Nat) (hle : m ≤ K)
    (v : List Sig) (hv : v.Nodup) (he : v.toFinset=S) : search K t v = true := by
  have size := live_size l
  rw [←he,List.toFinset_card_of_nodup hv] at size
  induction l generalizing K v with
  | stop =>
    have ht : v.contains target = true := List.contains_iff_mem.mpr (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
    cases K with
    | zero => exact ht
    | succ k =>
      rw [search,if_neg (by omega),ht]
      rfl
  | @unary m t U a ha hf tail ih =>
    cases K with
    | zero => omega
    | succ k =>
      rw [search,if_neg (by omega)]
      apply Bool.or_eq_true_iff.mpr; left
      apply Bool.or_eq_true_iff.mpr; right
      apply Bool.and_eq_true_iff.mpr
      refine ⟨by simp,unary_found hv he (by omega) hf tail ?_⟩
      intro w hn eq
      have sz := live_size tail
      rw [←eq,List.toFinset_card_of_nodup hn] at sz
      exact ih k (by omega) w hn eq sz
  | @binary m t U a b d ha hb hab hf tail ih =>
    cases K with
    | zero => omega
    | succ k =>
      rw [search,if_neg (by omega)]
      apply Bool.or_eq_true_iff.mpr
      right
      have cont (w : List Sig) (hn : w.Nodup) (eq : w.toFinset=insert (bin d a b) U) : search k t w = true := by
        have sz := live_size tail
        rw [←eq,List.toFinset_card_of_nodup hn] at sz
        exact ih k (by omega) w hn eq sz
      rcases ordered hab with o | o
      · exact binary_found hv he (by omega) o hab hf tail cont
      · rw [Finset.insert_comm a b] at he hf
        rw [bin_comm d a b] at hf tail cont
        exact binary_found hv he (by omega) o hab.symm hf tail cont
open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (side : Bool) (i : Fin 234) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 234).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
private lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

private lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

private lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]

def sample (s : Bool) (i : Fin 234) (j : Fin 8) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 0 && x 6) || (x 0 && x 7)

private lemma sample_ok : ∀ (s : Bool) (i : Fin 234), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 8 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 8 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 10)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 3, search 10 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=8 := rfl
  change C.gates.length ≤ 10 at hc
  exact ⟨t,by omega,search_complete ht 10 (by omega) raw raw_nd eq⟩
-- A finite list of rejected successor states can be reused by the checker.
-- The closed Boolean check verifies that the list covers every enabled move.
def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
  v.contains target || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

private lemma try_mono {k t v rest n c g opts} {r s : List Sig → Bool}
    (h : ∀ w, r w = true → s w = true)
    (hr : tryGate k t r v rest n c g opts = true) : tryGate k t s v rest n c g opts = true := by
  by_cases tight : n=k-t
  · simp only [tryGate,if_pos tight,Bool.and_eq_true] at hr ⊢
    exact ⟨hr.1,h _ hr.2⟩
  · simp only [tryGate,if_neg tight,Bool.and_eq_true,List.any_eq_true] at hr ⊢
    obtain ⟨a,ha,hc,hit⟩ := hr
    exact ⟨a,ha,hc,h _ hit⟩

private lemma umove_mono {k t v} {r s : List Sig → Bool}
    (h : ∀ w, r w = true → s w = true)
    (hr : unaryMoves k t r v = true) : unaryMoves k t s v = true := by
  obtain ⟨a,ha,move⟩ := List.any_eq_true.mp hr
  exact List.any_eq_true.mpr ⟨a,ha,try_mono h move⟩

private lemma bmove_mono {k t v} {r s : List Sig → Bool}
    (h : ∀ w, r w = true → s w = true)
    (hr : binaryMoves k t r v = true) : binaryMoves k t s v = true := by
  obtain ⟨a,ha,m⟩ := List.any_eq_true.mp hr
  obtain ⟨b,hb,z⟩ := List.any_eq_true.mp m
  apply List.any_eq_true.mpr
  refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,fast_mono h ?_ z⟩⟩
  intro slow
  obtain ⟨o,w⟩ := Bool.and_eq_true_iff.mp slow
  apply Bool.and_eq_true_iff.mpr
  refine ⟨o,?_⟩
  rcases Bool.or_eq_true_iff.mp w with p | p
  · exact Bool.or_eq_true_iff.mpr (Or.inl (try_mono h p))
  · exact Bool.or_eq_true_iff.mpr (Or.inr (try_mono h p))

private lemma reject_step (k t : Nat) (v : List Sig) (U A : List (List Sig))
    (hu : ∀ w ∈ U, search k (t-1) w = false)
    (hb : ∀ w ∈ A, search k t w = false)
    (hc : stepTest k t v (fun w => !(U.contains w)) (fun w => !(A.contains w)) = false) :
    search (k+1) t v = false := by
  cases ht : search (k+1) t v with
  | false => rfl
  | true =>
    exfalso
    have mono (n : Nat) (L : List (List Sig)) (hL : ∀ w ∈ L, search k n w=false) (w : List Sig)
        (hp : search k n w=true) : !(L.contains w) = true := by
      have hn : w ∉ L := fun hm => by have eq := hL _ hm; simp [hp] at eq
      simp [List.contains_eq_mem,hn]
    simp only [search] at ht
    unfold stepTest at hc
    split at ht
    · contradiction
    next hn =>
      rw [if_neg hn] at hc
      apply Bool.noConfusion (show false = true from hc.symm.trans ?_)
      rcases Bool.or_eq_true_iff.mp ht with a | b
      · rcases Bool.or_eq_true_iff.mp a with hit | u
        · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl hit)))
        · obtain ⟨hn,p⟩ := Bool.and_eq_true_iff.mp u
          exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr
            (Or.inr (Bool.and_eq_true_iff.mpr ⟨hn,umove_mono (mono _ U hu) p⟩))))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (bmove_mono (mono _ A hb) b))

private def wire0 : Sig := bin false raw0 raw1

private def wire1 : Sig := bin true raw0 raw1

private def wire2 : Sig := bin false raw0 raw2

private def wire3 : Sig := bin true raw0 raw2

private def wire4 : Sig := bin false raw0 raw3

private def wire5 : Sig := bin true raw0 raw3

private def wire6 : Sig := bin false raw0 raw4

private def wire7 : Sig := bin true raw0 raw4

private def wire8 : Sig := bin false raw0 raw5

private def wire9 : Sig := bin true raw0 raw5

private def wire10 : Sig := bin false raw0 raw6

private def wire11 : Sig := bin true raw0 raw6

private def wire12 : Sig := bin false raw0 raw7

private def wire13 : Sig := bin true raw0 raw7

private def wire14 : Sig := bin false raw1 raw2

private def wire15 : Sig := bin true raw1 raw2

private def wire16 : Sig := bin false raw1 raw3

private def wire17 : Sig := bin true raw1 raw3

private def wire18 : Sig := bin false raw1 raw4

private def wire19 : Sig := bin true raw1 raw4

private def wire20 : Sig := bin false raw1 raw5

private def wire21 : Sig := bin true raw1 raw5

private def wire22 : Sig := bin false raw1 raw6

private def wire23 : Sig := bin true raw1 raw6

private def wire24 : Sig := bin false raw1 raw7

private def wire25 : Sig := bin true raw1 raw7

private def wire26 : Sig := bin false raw2 raw4

private def wire27 : Sig := bin true raw2 raw4

private def wire28 : Sig := bin false raw2 raw6

private def wire29 : Sig := bin true raw2 raw6

private def wire30 : Sig := bin false raw2 raw7

private def wire31 : Sig := bin true raw2 raw7

private def wire32 : Sig := bin false raw3 raw2

private def wire33 : Sig := bin true raw3 raw2

private def wire34 : Sig := bin false raw3 raw4

private def wire35 : Sig := bin true raw3 raw4

private def wire36 : Sig := bin false raw3 raw5

private def wire37 : Sig := bin true raw3 raw5

private def wire38 : Sig := bin false raw3 raw6

private def wire39 : Sig := bin true raw3 raw6

private def wire40 : Sig := bin false raw3 raw7

private def wire41 : Sig := bin true raw3 raw7

private def wire42 : Sig := bin false raw4 raw6

private def wire43 : Sig := bin true raw4 raw6

private def wire44 : Sig := bin false raw4 raw7

private def wire45 : Sig := bin true raw4 raw7

private def wire46 : Sig := bin false raw5 raw2

private def wire47 : Sig := bin true raw5 raw2

private def wire48 : Sig := bin false raw5 raw4

private def wire49 : Sig := bin true raw5 raw4

private def wire50 : Sig := bin false raw5 raw6

private def wire51 : Sig := bin true raw5 raw6

private def wire52 : Sig := bin false raw5 raw7

private def wire53 : Sig := bin true raw5 raw7

private def wire54 : Sig := bin false raw6 raw7

private def wire55 : Sig := bin true raw6 raw7

private def wire56 : Sig := bin false wire0 raw2

private def wire57 : Sig := bin true wire0 raw2

private def wire58 : Sig := bin false wire0 raw3

private def wire59 : Sig := bin true wire0 raw3

private def wire60 : Sig := bin false wire0 raw4

private def wire61 : Sig := bin true wire0 raw4

private def wire62 : Sig := bin false wire0 raw5

private def wire63 : Sig := bin true wire0 raw5

private def wire64 : Sig := bin false wire0 raw6

private def wire65 : Sig := bin true wire0 raw6

private def wire66 : Sig := bin false wire0 raw7

private def wire67 : Sig := bin true wire0 raw7

private def wire68 : Sig := bin false wire3 raw4

private def wire69 : Sig := bin true wire3 raw4

private def wire70 : Sig := bin false wire3 raw6

private def wire71 : Sig := bin true wire3 raw6

private def wire72 : Sig := bin false wire3 raw7

private def wire73 : Sig := bin true wire3 raw7

private def wire74 : Sig := bin false raw1 wire3

private def wire75 : Sig := bin true raw1 wire3

private def wire76 : Sig := bin false raw3 wire3

private def wire77 : Sig := bin true raw3 wire3

private def wire78 : Sig := bin false raw5 wire3

private def wire79 : Sig := bin true raw5 wire3

private def wire80 : Sig := bin false wire9 raw2

private def wire81 : Sig := bin false wire9 raw4

private def wire82 : Sig := bin true wire9 raw4

private def wire83 : Sig := bin false wire9 raw6

private def wire84 : Sig := bin true wire9 raw6

private def wire85 : Sig := bin false wire9 raw7

private def wire86 : Sig := bin true wire9 raw7

private def wire87 : Sig := bin false raw1 wire9

private def wire88 : Sig := bin true raw1 wire9

private def wire89 : Sig := bin false raw3 wire9

private def wire90 : Sig := bin true raw3 wire9

private def wire91 : Sig := bin true wire10 raw1

private def wire92 : Sig := bin false wire10 raw2

private def wire93 : Sig := bin true wire10 raw2

private def wire94 : Sig := bin false wire10 raw3

private def wire95 : Sig := bin true wire10 raw3

private def wire96 : Sig := bin false wire10 raw4

private def wire97 : Sig := bin true wire10 raw4

private def wire98 : Sig := bin false wire10 raw5

private def wire99 : Sig := bin true wire10 raw5

private def wire100 : Sig := bin false wire10 raw7

private def wire101 : Sig := bin true wire10 raw7

private def wire102 : Sig := bin true wire12 raw1

private def wire103 : Sig := bin false wire12 raw2

private def wire104 : Sig := bin true wire12 raw2

private def wire105 : Sig := bin false wire12 raw3

private def wire106 : Sig := bin true wire12 raw3

private def wire107 : Sig := bin false wire12 raw4

private def wire108 : Sig := bin true wire12 raw4

private def wire109 : Sig := bin false wire12 raw5

private def wire110 : Sig := bin true wire12 raw5

private def wire111 : Sig := bin true wire12 raw6

private def wire112 : Sig := bin false wire14 raw3

private def wire113 : Sig := bin true wire14 raw3

private def wire114 : Sig := bin false wire14 raw4

private def wire115 : Sig := bin true wire14 raw4

private def wire116 : Sig := bin false wire14 raw5

private def wire117 : Sig := bin true wire14 raw5

private def wire118 : Sig := bin false wire14 raw6

private def wire119 : Sig := bin true wire14 raw6

private def wire120 : Sig := bin false wire14 raw7

private def wire121 : Sig := bin true wire14 raw7

private def wire122 : Sig := bin true raw0 wire14

private def wire123 : Sig := bin false wire17 raw2

private def wire124 : Sig := bin true wire17 raw2

private def wire125 : Sig := bin false wire17 raw4

private def wire126 : Sig := bin true wire17 raw4

private def wire127 : Sig := bin false wire17 raw5

private def wire128 : Sig := bin true wire17 raw5

private def wire129 : Sig := bin false wire17 raw6

private def wire130 : Sig := bin true wire17 raw6

private def wire131 : Sig := bin false wire17 raw7

private def wire132 : Sig := bin true wire17 raw7

private def wire133 : Sig := bin false raw0 wire17

private def wire134 : Sig := bin true raw0 wire17

private def wire135 : Sig := bin false wire23 raw7

private def wire136 : Sig := bin true wire23 raw7

private def wire137 : Sig := bin false raw0 wire23

private def wire138 : Sig := bin true raw0 wire23

private def wire139 : Sig := bin false raw2 wire23

private def wire140 : Sig := bin true raw2 wire23

private def wire141 : Sig := bin false raw3 wire23

private def wire142 : Sig := bin false raw4 wire23

private def wire143 : Sig := bin true raw4 wire23

private def wire144 : Sig := bin false raw5 wire23

private def wire145 : Sig := bin true raw5 wire23

private def wire146 : Sig := bin false raw0 wire25

private def wire147 : Sig := bin true raw0 wire25

private def wire148 : Sig := bin false raw2 wire25

private def wire149 : Sig := bin true raw2 wire25

private def wire150 : Sig := bin false raw3 wire25

private def wire151 : Sig := bin false raw4 wire25

private def wire152 : Sig := bin true raw4 wire25

private def wire153 : Sig := bin false raw5 wire25

private def wire154 : Sig := bin true raw5 wire25

private def wire155 : Sig := bin false raw6 wire25

private def wire156 : Sig := bin false wire27 raw6

private def wire157 : Sig := bin true wire27 raw6

private def wire158 : Sig := bin false wire27 raw7

private def wire159 : Sig := bin true wire27 raw7

private def wire160 : Sig := bin false raw0 wire27

private def wire161 : Sig := bin false raw1 wire27

private def wire162 : Sig := bin true raw1 wire27

private def wire163 : Sig := bin false raw3 wire27

private def wire164 : Sig := bin true raw3 wire27

private def wire165 : Sig := bin false raw5 wire27

private def wire166 : Sig := bin true raw5 wire27

private def wire167 : Sig := bin false wire32 raw4

private def wire168 : Sig := bin true wire32 raw4

private def wire169 : Sig := bin false wire32 raw5

private def wire170 : Sig := bin true wire32 raw5

private def wire171 : Sig := bin false wire32 raw6

private def wire172 : Sig := bin true wire32 raw6

private def wire173 : Sig := bin false wire32 raw7

private def wire174 : Sig := bin true wire32 raw7

private def wire175 : Sig := bin false raw0 wire32

private def wire176 : Sig := bin true raw0 wire32

private def wire177 : Sig := bin true raw1 wire32

private def wire178 : Sig := bin true wire34 raw2

private def wire179 : Sig := bin false wire34 raw5

private def wire180 : Sig := bin true wire34 raw5

private def wire181 : Sig := bin false wire34 raw6

private def wire182 : Sig := bin true wire34 raw6

private def wire183 : Sig := bin false wire34 raw7

private def wire184 : Sig := bin true wire34 raw7

private def wire185 : Sig := bin false raw0 wire34

private def wire186 : Sig := bin true raw0 wire34

private def wire187 : Sig := bin false raw1 wire34

private def wire188 : Sig := bin true raw1 wire34

private def wire189 : Sig := bin false wire37 raw2

private def wire190 : Sig := bin true wire37 raw2

private def wire191 : Sig := bin false wire37 raw4

private def wire192 : Sig := bin true wire37 raw4

private def wire193 : Sig := bin false wire37 raw6

private def wire194 : Sig := bin true wire37 raw6

private def wire195 : Sig := bin false wire37 raw7

private def wire196 : Sig := bin true wire37 raw7

private def wire197 : Sig := bin false raw0 wire37

private def wire198 : Sig := bin false raw1 wire37

private def wire199 : Sig := bin false wire43 raw7

private def wire200 : Sig := bin true wire43 raw7

private def wire201 : Sig := bin false raw0 wire43

private def wire202 : Sig := bin true raw0 wire43

private def wire203 : Sig := bin false raw1 wire43

private def wire204 : Sig := bin false raw2 wire43

private def wire205 : Sig := bin false raw3 wire43

private def wire206 : Sig := bin true raw3 wire43

private def wire207 : Sig := bin false raw5 wire43

private def wire208 : Sig := bin true raw5 wire43

private def wire209 : Sig := bin false wire48 raw2

private def wire210 : Sig := bin true wire48 raw2

private def wire211 : Sig := bin false wire48 raw6

private def wire212 : Sig := bin true wire48 raw6

private def wire213 : Sig := bin false wire48 raw7

private def wire214 : Sig := bin true wire48 raw7

private def wire215 : Sig := bin false raw0 wire48

private def wire216 : Sig := bin true raw0 wire48

private def wire217 : Sig := bin false raw1 wire48

private def wire218 : Sig := bin true raw1 wire48

private def wire219 : Sig := bin true raw3 wire48

private def wire220 : Sig := bin false wire50 raw2

private def wire221 : Sig := bin true wire50 raw2

private def wire222 : Sig := bin true wire50 raw4

private def wire223 : Sig := bin false wire50 raw7

private def wire224 : Sig := bin true wire50 raw7

private def wire225 : Sig := bin true raw0 wire50

private def wire226 : Sig := bin false raw1 wire50

private def wire227 : Sig := bin true raw1 wire50

private def wire228 : Sig := bin false raw3 wire50

private def wire229 : Sig := bin true raw3 wire50

private def wire230 : Sig := bin false raw0 wire55

private def wire231 : Sig := bin true raw0 wire55

private def wire232 : Sig := bin false raw1 wire55

private def wire233 : Sig := bin false raw2 wire55

private def wire234 : Sig := bin true raw2 wire55

private def wire235 : Sig := bin false raw3 wire55

private def wire236 : Sig := bin true raw3 wire55

private def wire237 : Sig := bin false raw4 wire55

private def wire238 : Sig := bin false raw5 wire55

private def wire239 : Sig := bin true raw5 wire55

private def wire240 : Sig := neg raw0

private def wire241 : Sig := neg raw1

private def wire242 : Sig := neg raw2

private def wire243 : Sig := neg raw3

private def wire244 : Sig := neg raw4

private def wire245 : Sig := neg raw5

private def wire246 : Sig := neg raw6

private def wire247 : Sig := neg raw7

private def st0 : List Sig := [wire56,raw2,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node0 : search 8 0 st0 = false := by decide +kernel

private def st1 : List Sig := [wire57,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1 : search 8 0 st1 = false := by decide +kernel

private def st2 : List Sig := [wire57,wire0,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node2 : search 8 0 st2 = false := by decide +kernel

private def st3 : List Sig := [wire57,raw2,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node3 : search 8 0 st3 = false := by decide +kernel

private def st4 : List Sig := [wire58,raw3,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node4 : search 8 0 st4 = false := by decide +kernel

private def st5 : List Sig := [wire59,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node5 : search 8 0 st5 = false := by decide +kernel

private def st6 : List Sig := [wire59,wire0,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node6 : search 8 0 st6 = false := by decide +kernel

private def st7 : List Sig := [wire59,raw3,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node7 : search 8 0 st7 = false := by decide +kernel

private def st8 : List Sig := [wire60,raw4,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node8 : search 8 0 st8 = false := by decide +kernel

private def st9 : List Sig := [wire61,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node9 : search 8 0 st9 = false := by decide +kernel

private def st10 : List Sig := [wire61,wire0,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node10 : search 8 0 st10 = false := by decide +kernel

private def st11 : List Sig := [wire61,raw4,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node11 : search 8 0 st11 = false := by decide +kernel

private def st12 : List Sig := [wire62,raw5,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node12 : search 8 0 st12 = false := by decide +kernel

private def st13 : List Sig := [wire63,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node13 : search 8 0 st13 = false := by decide +kernel

private def st14 : List Sig := [wire63,wire0,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node14 : search 8 0 st14 = false := by decide +kernel

private def st15 : List Sig := [wire63,raw5,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node15 : search 8 0 st15 = false := by decide +kernel

private def st16 : List Sig := [wire64,raw6,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node16 : search 8 0 st16 = false := by decide +kernel

private def st17 : List Sig := [wire65,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node17 : search 8 0 st17 = false := by decide +kernel

private def st18 : List Sig := [wire65,wire0,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node18 : search 8 0 st18 = false := by decide +kernel

private def st19 : List Sig := [wire65,raw6,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node19 : search 8 0 st19 = false := by decide +kernel

private def st20 : List Sig := [wire66,raw7,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node20 : search 8 0 st20 = false := by decide +kernel

private def st21 : List Sig := [wire67,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node21 : search 8 0 st21 = false := by decide +kernel

private def st22 : List Sig := [wire67,wire0,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node22 : search 8 0 st22 = false := by decide +kernel

private def st23 : List Sig := [wire67,raw7,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node23 : search 8 0 st23 = false := by decide +kernel

private def st24 : List Sig := [wire12,raw0,wire0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node24 : search 8 0 st24 = false := by decide +kernel

private def st25 : List Sig := [wire14,raw2,wire0,raw0,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node25 : search 8 0 st25 = false := by decide +kernel

private def st26 : List Sig := [wire17,raw3,wire0,raw0,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node26 : search 8 0 st26 = false := by decide +kernel

private def st27 : List Sig := [wire25,raw1,wire0,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node27 : search 8 0 st27 = false := by decide +kernel

private def st28 : List Sig := [wire55,raw6,wire0,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node28 : search 8 0 st28 = false := by decide +kernel

private def st29 : List Sig := [wire0,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node29 : search 9 0 st29 = false := by
  apply reject_step 8 0 st29 [] [st0,st1,st2,st3,st4,st5,st6,st7,st8,st9,st10,st11,st12,st13,st14,st15,st16,st17,st18,st19,st20,st21,st22,st23,st24,st25,st26,st27,st28]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node0
    · exact node1
    · exact node2
    · exact node3
    · exact node4
    · exact node5
    · exact node6
    · exact node7
    · exact node8
    · exact node9
    · exact node10
    · exact node11
    · exact node12
    · exact node13
    · exact node14
    · exact node15
    · exact node16
    · exact node17
    · exact node18
    · exact node19
    · exact node20
    · exact node21
    · exact node22
    · exact node23
    · exact node24
    · exact node25
    · exact node26
    · exact node27
    · exact node28
  · decide +kernel

private def st30 : List Sig := [wire1,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node30 : search 9 0 st30 = false := by decide +kernel

private def st31 : List Sig := [wire2,raw0,raw2,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node31 : search 9 0 st31 = false := by decide +kernel

private def st32 : List Sig := [wire68,raw4,raw0,raw2,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node32 : search 8 0 st32 = false := by decide +kernel

private def st33 : List Sig := [wire69,raw4,raw0,raw2,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node33 : search 8 0 st33 = false := by decide +kernel

private def st34 : List Sig := [wire70,raw6,raw0,raw2,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node34 : search 8 0 st34 = false := by decide +kernel

private def st35 : List Sig := [wire71,raw6,raw0,raw2,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node35 : search 8 0 st35 = false := by decide +kernel

private def st36 : List Sig := [wire72,raw0,raw2,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node36 : search 8 0 st36 = false := by decide +kernel

private def st37 : List Sig := [wire72,wire3,raw0,raw2,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node37 : search 8 0 st37 = false := by decide +kernel

private def st38 : List Sig := [wire72,raw7,raw0,raw2,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node38 : search 8 0 st38 = false := by decide +kernel

private def st39 : List Sig := [wire73,raw7,raw0,raw2,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node39 : search 8 0 st39 = false := by decide +kernel

private def st40 : List Sig := [wire1,raw1,wire3,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node40 : search 8 0 st40 = false := by decide +kernel

private def st41 : List Sig := [wire5,raw3,wire3,raw2,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node41 : search 8 0 st41 = false := by decide +kernel

private def st42 : List Sig := [wire12,raw0,wire3,raw2,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node42 : search 8 0 st42 = false := by decide +kernel

private def st43 : List Sig := [wire27,raw4,wire3,raw0,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node43 : search 8 0 st43 = false := by decide +kernel

private def st44 : List Sig := [wire29,raw6,wire3,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node44 : search 8 0 st44 = false := by decide +kernel

private def st45 : List Sig := [wire31,raw7,wire3,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node45 : search 8 0 st45 = false := by decide +kernel

private def st46 : List Sig := [wire74,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node46 : search 8 0 st46 = false := by decide +kernel

private def st47 : List Sig := [wire74,raw1,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node47 : search 8 0 st47 = false := by decide +kernel

private def st48 : List Sig := [wire74,wire3,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node48 : search 8 0 st48 = false := by decide +kernel

private def st49 : List Sig := [wire75,raw1,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node49 : search 8 0 st49 = false := by decide +kernel

private def st50 : List Sig := [wire15,raw1,wire3,raw0,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node50 : search 8 0 st50 = false := by decide +kernel

private def st51 : List Sig := [wire25,raw1,wire3,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node51 : search 8 0 st51 = false := by decide +kernel

private def st52 : List Sig := [wire76,raw3,raw0,raw2,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node52 : search 8 0 st52 = false := by decide +kernel

private def st53 : List Sig := [wire77,raw3,raw0,raw2,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node53 : search 8 0 st53 = false := by decide +kernel

private def st54 : List Sig := [wire32,raw3,wire3,raw0,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node54 : search 8 0 st54 = false := by decide +kernel

private def st55 : List Sig := [wire78,raw5,raw0,raw2,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node55 : search 8 0 st55 = false := by decide +kernel

private def st56 : List Sig := [wire79,raw5,raw0,raw2,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node56 : search 8 0 st56 = false := by decide +kernel

private def st57 : List Sig := [wire55,raw6,wire3,raw0,raw2,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node57 : search 8 0 st57 = false := by decide +kernel

private def st58 : List Sig := [wire3,raw0,raw2,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node58 : search 9 0 st58 = false := by
  apply reject_step 8 0 st58 [] [st32,st33,st34,st35,st36,st37,st38,st39,st40,st41,st42,st43,st44,st45,st46,st47,st48,st49,st50,st51,st52,st53,st54,st55,st56,st57]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node32
    · exact node33
    · exact node34
    · exact node35
    · exact node36
    · exact node37
    · exact node38
    · exact node39
    · exact node40
    · exact node41
    · exact node42
    · exact node43
    · exact node44
    · exact node45
    · exact node46
    · exact node47
    · exact node48
    · exact node49
    · exact node50
    · exact node51
    · exact node52
    · exact node53
    · exact node54
    · exact node55
    · exact node56
    · exact node57
  · decide +kernel

private def st59 : List Sig := [wire4,raw0,raw3,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node59 : search 9 0 st59 = false := by decide +kernel

private def st60 : List Sig := [wire5,raw0,raw3,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node60 : search 9 0 st60 = false := by decide +kernel

private def st61 : List Sig := [wire6,raw0,raw4,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node61 : search 9 0 st61 = false := by decide +kernel

private def st62 : List Sig := [wire7,raw0,raw4,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node62 : search 9 0 st62 = false := by decide +kernel

private def st63 : List Sig := [wire8,raw0,raw5,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node63 : search 9 0 st63 = false := by decide +kernel

private def st64 : List Sig := [wire80,raw2,raw0,raw5,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node64 : search 8 0 st64 = false := by decide +kernel

private def st65 : List Sig := [wire79,raw2,raw0,raw5,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node65 : search 8 0 st65 = false := by decide +kernel

private def st66 : List Sig := [wire81,raw4,raw0,raw5,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node66 : search 8 0 st66 = false := by decide +kernel

private def st67 : List Sig := [wire82,raw4,raw0,raw5,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node67 : search 8 0 st67 = false := by decide +kernel

private def st68 : List Sig := [wire83,raw0,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node68 : search 8 0 st68 = false := by decide +kernel

private def st69 : List Sig := [wire83,wire9,raw0,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node69 : search 8 0 st69 = false := by decide +kernel

private def st70 : List Sig := [wire83,raw6,raw0,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node70 : search 8 0 st70 = false := by decide +kernel

private def st71 : List Sig := [wire84,raw6,raw0,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node71 : search 8 0 st71 = false := by decide +kernel

private def st72 : List Sig := [wire85,raw0,raw5,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node72 : search 8 0 st72 = false := by decide +kernel

private def st73 : List Sig := [wire85,wire9,raw0,raw5,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node73 : search 8 0 st73 = false := by decide +kernel

private def st74 : List Sig := [wire85,raw7,raw0,raw5,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node74 : search 8 0 st74 = false := by decide +kernel

private def st75 : List Sig := [wire86,raw7,raw0,raw5,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node75 : search 8 0 st75 = false := by decide +kernel

private def st76 : List Sig := [wire7,raw4,wire9,raw5,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node76 : search 8 0 st76 = false := by decide +kernel

private def st77 : List Sig := [wire11,raw6,wire9,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node77 : search 8 0 st77 = false := by decide +kernel

private def st78 : List Sig := [wire12,raw0,wire9,raw5,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node78 : search 8 0 st78 = false := by decide +kernel

private def st79 : List Sig := [wire48,raw4,wire9,raw0,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node79 : search 8 0 st79 = false := by decide +kernel

private def st80 : List Sig := [wire51,raw6,wire9,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node80 : search 8 0 st80 = false := by decide +kernel

private def st81 : List Sig := [wire53,raw7,wire9,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node81 : search 8 0 st81 = false := by decide +kernel

private def st82 : List Sig := [wire87,raw1,raw0,raw5,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node82 : search 8 0 st82 = false := by decide +kernel

private def st83 : List Sig := [wire88,raw1,raw0,raw5,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node83 : search 8 0 st83 = false := by decide +kernel

private def st84 : List Sig := [wire21,raw1,wire9,raw0,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node84 : search 8 0 st84 = false := by decide +kernel

private def st85 : List Sig := [wire25,raw1,wire9,raw0,raw5,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node85 : search 8 0 st85 = false := by decide +kernel

private def st86 : List Sig := [wire89,raw3,raw0,raw5,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node86 : search 8 0 st86 = false := by decide +kernel

private def st87 : List Sig := [wire90,raw3,raw0,raw5,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node87 : search 8 0 st87 = false := by decide +kernel

private def st88 : List Sig := [wire37,raw3,wire9,raw0,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node88 : search 8 0 st88 = false := by decide +kernel

private def st89 : List Sig := [wire55,raw6,wire9,raw0,raw5,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node89 : search 8 0 st89 = false := by decide +kernel

private def st90 : List Sig := [wire9,raw0,raw5,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node90 : search 9 0 st90 = false := by
  apply reject_step 8 0 st90 [] [st64,st65,st66,st67,st68,st69,st70,st71,st72,st73,st74,st75,st76,st77,st78,st79,st80,st81,st82,st83,st84,st85,st86,st87,st88,st89]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node64
    · exact node65
    · exact node66
    · exact node67
    · exact node68
    · exact node69
    · exact node70
    · exact node71
    · exact node72
    · exact node73
    · exact node74
    · exact node75
    · exact node76
    · exact node77
    · exact node78
    · exact node79
    · exact node80
    · exact node81
    · exact node82
    · exact node83
    · exact node84
    · exact node85
    · exact node86
    · exact node87
    · exact node88
    · exact node89
  · decide +kernel

private def st91 : List Sig := [wire64,raw1,raw0,raw6,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node91 : search 8 0 st91 = false := by decide +kernel

private def st92 : List Sig := [wire91,raw0,raw6,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node92 : search 8 0 st92 = false := by decide +kernel

private def st93 : List Sig := [wire91,wire10,raw0,raw6,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node93 : search 8 0 st93 = false := by decide +kernel

private def st94 : List Sig := [wire91,raw1,raw0,raw6,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node94 : search 8 0 st94 = false := by decide +kernel

private def st95 : List Sig := [wire92,raw2,raw0,raw6,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node95 : search 8 0 st95 = false := by decide +kernel

private def st96 : List Sig := [wire93,raw0,raw6,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node96 : search 8 0 st96 = false := by decide +kernel

private def st97 : List Sig := [wire93,wire10,raw0,raw6,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node97 : search 8 0 st97 = false := by decide +kernel

private def st98 : List Sig := [wire93,raw2,raw0,raw6,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node98 : search 8 0 st98 = false := by decide +kernel

private def st99 : List Sig := [wire94,raw3,raw0,raw6,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node99 : search 8 0 st99 = false := by decide +kernel

private def st100 : List Sig := [wire95,raw0,raw6,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node100 : search 8 0 st100 = false := by decide +kernel

private def st101 : List Sig := [wire95,wire10,raw0,raw6,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node101 : search 8 0 st101 = false := by decide +kernel

private def st102 : List Sig := [wire95,raw3,raw0,raw6,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node102 : search 8 0 st102 = false := by decide +kernel

private def st103 : List Sig := [wire96,raw4,raw0,raw6,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node103 : search 8 0 st103 = false := by decide +kernel

private def st104 : List Sig := [wire97,raw0,raw6,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node104 : search 8 0 st104 = false := by decide +kernel

private def st105 : List Sig := [wire97,wire10,raw0,raw6,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node105 : search 8 0 st105 = false := by decide +kernel

private def st106 : List Sig := [wire97,raw4,raw0,raw6,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node106 : search 8 0 st106 = false := by decide +kernel

private def st107 : List Sig := [wire98,raw5,raw0,raw6,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node107 : search 8 0 st107 = false := by decide +kernel

private def st108 : List Sig := [wire99,raw0,raw6,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node108 : search 8 0 st108 = false := by decide +kernel

private def st109 : List Sig := [wire99,wire10,raw0,raw6,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node109 : search 8 0 st109 = false := by decide +kernel

private def st110 : List Sig := [wire99,raw5,raw0,raw6,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node110 : search 8 0 st110 = false := by decide +kernel

private def st111 : List Sig := [wire100,raw7,raw0,raw6,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node111 : search 8 0 st111 = false := by decide +kernel

private def st112 : List Sig := [wire101,raw0,raw6,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node112 : search 8 0 st112 = false := by decide +kernel

private def st113 : List Sig := [wire101,wire10,raw0,raw6,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node113 : search 8 0 st113 = false := by decide +kernel

private def st114 : List Sig := [wire101,raw7,raw0,raw6,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node114 : search 8 0 st114 = false := by decide +kernel

private def st115 : List Sig := [wire12,raw0,wire10,raw6,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node115 : search 8 0 st115 = false := by decide +kernel

private def st116 : List Sig := [wire55,raw6,wire10,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node116 : search 8 0 st116 = false := by decide +kernel

private def st117 : List Sig := [wire25,raw1,wire10,raw0,raw6,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node117 : search 8 0 st117 = false := by decide +kernel

private def st118 : List Sig := [wire43,raw4,wire10,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node118 : search 8 0 st118 = false := by decide +kernel

private def st119 : List Sig := [wire50,raw5,wire10,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node119 : search 8 0 st119 = false := by decide +kernel

private def st120 : List Sig := [wire10,raw0,raw6,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node120 : search 9 0 st120 = false := by
  apply reject_step 8 0 st120 [] [st91,st92,st93,st94,st95,st96,st97,st98,st99,st100,st101,st102,st103,st104,st105,st106,st107,st108,st109,st110,st111,st112,st113,st114,st115,st116,st117,st118,st119]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node91
    · exact node92
    · exact node93
    · exact node94
    · exact node95
    · exact node96
    · exact node97
    · exact node98
    · exact node99
    · exact node100
    · exact node101
    · exact node102
    · exact node103
    · exact node104
    · exact node105
    · exact node106
    · exact node107
    · exact node108
    · exact node109
    · exact node110
    · exact node111
    · exact node112
    · exact node113
    · exact node114
    · exact node115
    · exact node116
    · exact node117
    · exact node118
    · exact node119
  · decide +kernel

private def st121 : List Sig := [wire11,raw0,raw6,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node121 : search 9 0 st121 = false := by decide +kernel

private def st122 : List Sig := [wire66,wire12,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node122 : search 8 0 st122 = false := by decide +kernel

private def st123 : List Sig := [wire102,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node123 : search 8 0 st123 = false := by decide +kernel

private def st124 : List Sig := [wire102,wire12,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node124 : search 8 0 st124 = false := by decide +kernel

private def st125 : List Sig := [wire102,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node125 : search 8 0 st125 = false := by decide +kernel

private def st126 : List Sig := [wire102,wire12,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node126 : search 8 0 st126 = false := by decide +kernel

private def st127 : List Sig := [wire103,wire12,raw2,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node127 : search 8 0 st127 = false := by decide +kernel

private def st128 : List Sig := [wire104,wire12,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node128 : search 8 0 st128 = false := by decide +kernel

private def st129 : List Sig := [wire104,wire12,raw2,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node129 : search 8 0 st129 = false := by decide +kernel

private def st130 : List Sig := [wire105,wire12,raw3,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node130 : search 8 0 st130 = false := by decide +kernel

private def st131 : List Sig := [wire106,wire12,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node131 : search 8 0 st131 = false := by decide +kernel

private def st132 : List Sig := [wire106,wire12,raw3,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node132 : search 8 0 st132 = false := by decide +kernel

private def st133 : List Sig := [wire107,wire12,raw4,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node133 : search 8 0 st133 = false := by decide +kernel

private def st134 : List Sig := [wire108,wire12,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node134 : search 8 0 st134 = false := by decide +kernel

private def st135 : List Sig := [wire108,wire12,raw4,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node135 : search 8 0 st135 = false := by decide +kernel

private def st136 : List Sig := [wire109,wire12,raw5,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node136 : search 8 0 st136 = false := by decide +kernel

private def st137 : List Sig := [wire110,wire12,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node137 : search 8 0 st137 = false := by decide +kernel

private def st138 : List Sig := [wire110,wire12,raw5,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node138 : search 8 0 st138 = false := by decide +kernel

private def st139 : List Sig := [wire100,wire12,raw6,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node139 : search 8 0 st139 = false := by decide +kernel

private def st140 : List Sig := [wire111,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node140 : search 8 0 st140 = false := by decide +kernel

private def st141 : List Sig := [wire111,wire12,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node141 : search 8 0 st141 = false := by decide +kernel

private def st142 : List Sig := [wire111,raw6,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node142 : search 8 0 st142 = false := by decide +kernel

private def st143 : List Sig := [wire111,wire12,raw6,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node143 : search 8 0 st143 = false := by decide +kernel

private def st144 : List Sig := [wire0,raw0,raw1,wire12,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node144 : search 8 0 st144 = false := by decide +kernel

private def st145 : List Sig := [wire1,raw0,raw1,wire12,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node145 : search 8 0 st145 = false := by decide +kernel

private def st146 : List Sig := [wire2,raw0,raw2,wire12,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node146 : search 8 0 st146 = false := by decide +kernel

private def st147 : List Sig := [wire3,raw0,raw2,wire12,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node147 : search 8 0 st147 = false := by decide +kernel

private def st148 : List Sig := [wire4,raw0,raw3,wire12,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node148 : search 8 0 st148 = false := by decide +kernel

private def st149 : List Sig := [wire5,raw0,raw3,wire12,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node149 : search 8 0 st149 = false := by decide +kernel

private def st150 : List Sig := [wire6,raw0,raw4,wire12,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node150 : search 8 0 st150 = false := by decide +kernel

private def st151 : List Sig := [wire7,raw0,raw4,wire12,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node151 : search 8 0 st151 = false := by decide +kernel

private def st152 : List Sig := [wire8,raw0,raw5,wire12,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node152 : search 8 0 st152 = false := by decide +kernel

private def st153 : List Sig := [wire9,raw0,raw5,wire12,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node153 : search 8 0 st153 = false := by decide +kernel

private def st154 : List Sig := [wire10,raw0,raw6,wire12,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node154 : search 8 0 st154 = false := by decide +kernel

private def st155 : List Sig := [wire11,raw0,raw6,wire12,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node155 : search 8 0 st155 = false := by decide +kernel

private def st156 : List Sig := [wire14,raw1,raw2,wire12,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node156 : search 8 0 st156 = false := by decide +kernel

private def st157 : List Sig := [wire15,raw1,raw2,wire12,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node157 : search 8 0 st157 = false := by decide +kernel

private def st158 : List Sig := [wire16,raw1,raw3,wire12,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node158 : search 8 0 st158 = false := by decide +kernel

private def st159 : List Sig := [wire17,raw1,raw3,wire12,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node159 : search 8 0 st159 = false := by decide +kernel

private def st160 : List Sig := [wire18,raw1,raw4,wire12,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node160 : search 8 0 st160 = false := by decide +kernel

private def st161 : List Sig := [wire19,raw1,raw4,wire12,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node161 : search 8 0 st161 = false := by decide +kernel

private def st162 : List Sig := [wire20,raw1,raw5,wire12,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node162 : search 8 0 st162 = false := by decide +kernel

private def st163 : List Sig := [wire21,raw1,raw5,wire12,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node163 : search 8 0 st163 = false := by decide +kernel

private def st164 : List Sig := [wire22,raw1,raw6,wire12,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node164 : search 8 0 st164 = false := by decide +kernel

private def st165 : List Sig := [wire23,raw1,raw6,wire12,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node165 : search 8 0 st165 = false := by decide +kernel

private def st166 : List Sig := [wire26,raw2,raw4,wire12,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node166 : search 8 0 st166 = false := by decide +kernel

private def st167 : List Sig := [wire27,raw2,raw4,wire12,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node167 : search 8 0 st167 = false := by decide +kernel

private def st168 : List Sig := [wire28,raw2,raw6,wire12,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node168 : search 8 0 st168 = false := by decide +kernel

private def st169 : List Sig := [wire29,raw2,raw6,wire12,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node169 : search 8 0 st169 = false := by decide +kernel

private def st170 : List Sig := [wire32,raw3,raw2,wire12,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node170 : search 8 0 st170 = false := by decide +kernel

private def st171 : List Sig := [wire33,raw3,raw2,wire12,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node171 : search 8 0 st171 = false := by decide +kernel

private def st172 : List Sig := [wire34,raw3,raw4,wire12,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node172 : search 8 0 st172 = false := by decide +kernel

private def st173 : List Sig := [wire35,raw3,raw4,wire12,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node173 : search 8 0 st173 = false := by decide +kernel

private def st174 : List Sig := [wire36,raw3,raw5,wire12,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node174 : search 8 0 st174 = false := by decide +kernel

private def st175 : List Sig := [wire37,raw3,raw5,wire12,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node175 : search 8 0 st175 = false := by decide +kernel

private def st176 : List Sig := [wire38,raw3,raw6,wire12,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node176 : search 8 0 st176 = false := by decide +kernel

private def st177 : List Sig := [wire39,raw3,raw6,wire12,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node177 : search 8 0 st177 = false := by decide +kernel

private def st178 : List Sig := [wire42,raw4,raw6,wire12,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node178 : search 8 0 st178 = false := by decide +kernel

private def st179 : List Sig := [wire43,raw4,raw6,wire12,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node179 : search 8 0 st179 = false := by decide +kernel

private def st180 : List Sig := [wire46,raw5,raw2,wire12,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node180 : search 8 0 st180 = false := by decide +kernel

private def st181 : List Sig := [wire47,raw5,raw2,wire12,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node181 : search 8 0 st181 = false := by decide +kernel

private def st182 : List Sig := [wire48,raw5,raw4,wire12,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node182 : search 8 0 st182 = false := by decide +kernel

private def st183 : List Sig := [wire49,raw5,raw4,wire12,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node183 : search 8 0 st183 = false := by decide +kernel

private def st184 : List Sig := [wire50,raw5,raw6,wire12,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node184 : search 8 0 st184 = false := by decide +kernel

private def st185 : List Sig := [wire51,raw5,raw6,wire12,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node185 : search 8 0 st185 = false := by decide +kernel

private def st186 : List Sig := [wire12,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node186 : search 9 0 st186 = false := by
  apply reject_step 8 0 st186 [] [st122,st123,st124,st125,st126,st127,st128,st129,st130,st131,st132,st133,st134,st135,st136,st137,st138,st139,st140,st141,st142,st143,st144,st145,st146,st147,st148,st149,st150,st151,st152,st153,st154,st155,st156,st157,st158,st159,st160,st161,st162,st163,st164,st165,st166,st167,st168,st169,st170,st171,st172,st173,st174,st175,st176,st177,st178,st179,st180,st181,st182,st183,st184,st185]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node122
    · exact node123
    · exact node124
    · exact node125
    · exact node126
    · exact node127
    · exact node128
    · exact node129
    · exact node130
    · exact node131
    · exact node132
    · exact node133
    · exact node134
    · exact node135
    · exact node136
    · exact node137
    · exact node138
    · exact node139
    · exact node140
    · exact node141
    · exact node142
    · exact node143
    · exact node144
    · exact node145
    · exact node146
    · exact node147
    · exact node148
    · exact node149
    · exact node150
    · exact node151
    · exact node152
    · exact node153
    · exact node154
    · exact node155
    · exact node156
    · exact node157
    · exact node158
    · exact node159
    · exact node160
    · exact node161
    · exact node162
    · exact node163
    · exact node164
    · exact node165
    · exact node166
    · exact node167
    · exact node168
    · exact node169
    · exact node170
    · exact node171
    · exact node172
    · exact node173
    · exact node174
    · exact node175
    · exact node176
    · exact node177
    · exact node178
    · exact node179
    · exact node180
    · exact node181
    · exact node182
    · exact node183
    · exact node184
    · exact node185
  · decide +kernel

private def st187 : List Sig := [wire66,raw1,raw0,raw7,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node187 : search 8 0 st187 = false := by decide +kernel

private def st188 : List Sig := [wire102,raw0,raw7,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node188 : search 8 0 st188 = false := by decide +kernel

private def st189 : List Sig := [wire102,wire12,raw0,raw7,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node189 : search 8 0 st189 = false := by decide +kernel

private def st190 : List Sig := [wire102,raw1,raw0,raw7,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node190 : search 8 0 st190 = false := by decide +kernel

private def st191 : List Sig := [wire103,raw2,raw0,raw7,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node191 : search 8 0 st191 = false := by decide +kernel

private def st192 : List Sig := [wire104,raw0,raw7,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node192 : search 8 0 st192 = false := by decide +kernel

private def st193 : List Sig := [wire104,wire12,raw0,raw7,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node193 : search 8 0 st193 = false := by decide +kernel

private def st194 : List Sig := [wire104,raw2,raw0,raw7,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node194 : search 8 0 st194 = false := by decide +kernel

private def st195 : List Sig := [wire105,raw3,raw0,raw7,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node195 : search 8 0 st195 = false := by decide +kernel

private def st196 : List Sig := [wire106,raw0,raw7,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node196 : search 8 0 st196 = false := by decide +kernel

private def st197 : List Sig := [wire106,wire12,raw0,raw7,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node197 : search 8 0 st197 = false := by decide +kernel

private def st198 : List Sig := [wire106,raw3,raw0,raw7,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node198 : search 8 0 st198 = false := by decide +kernel

private def st199 : List Sig := [wire107,raw4,raw0,raw7,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node199 : search 8 0 st199 = false := by decide +kernel

private def st200 : List Sig := [wire108,raw0,raw7,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node200 : search 8 0 st200 = false := by decide +kernel

private def st201 : List Sig := [wire108,wire12,raw0,raw7,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node201 : search 8 0 st201 = false := by decide +kernel

private def st202 : List Sig := [wire108,raw4,raw0,raw7,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node202 : search 8 0 st202 = false := by decide +kernel

private def st203 : List Sig := [wire109,raw5,raw0,raw7,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node203 : search 8 0 st203 = false := by decide +kernel

private def st204 : List Sig := [wire110,raw0,raw7,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node204 : search 8 0 st204 = false := by decide +kernel

private def st205 : List Sig := [wire110,wire12,raw0,raw7,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node205 : search 8 0 st205 = false := by decide +kernel

private def st206 : List Sig := [wire110,raw5,raw0,raw7,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node206 : search 8 0 st206 = false := by decide +kernel

private def st207 : List Sig := [wire100,raw6,raw0,raw7,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node207 : search 8 0 st207 = false := by decide +kernel

private def st208 : List Sig := [wire111,raw0,raw7,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node208 : search 8 0 st208 = false := by decide +kernel

private def st209 : List Sig := [wire111,wire12,raw0,raw7,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node209 : search 8 0 st209 = false := by decide +kernel

private def st210 : List Sig := [wire111,raw6,raw0,raw7,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node210 : search 8 0 st210 = false := by decide +kernel

private def st211 : List Sig := [wire13,raw0,wire12,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node211 : search 8 0 st211 = false := by decide +kernel

private def st212 : List Sig := [wire24,raw1,wire12,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node212 : search 8 0 st212 = false := by decide +kernel

private def st213 : List Sig := [wire25,raw1,wire12,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node213 : search 8 0 st213 = false := by decide +kernel

private def st214 : List Sig := [wire30,raw2,wire12,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node214 : search 8 0 st214 = false := by decide +kernel

private def st215 : List Sig := [wire31,raw2,wire12,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node215 : search 8 0 st215 = false := by decide +kernel

private def st216 : List Sig := [wire40,raw3,wire12,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node216 : search 8 0 st216 = false := by decide +kernel

private def st217 : List Sig := [wire41,raw3,wire12,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node217 : search 8 0 st217 = false := by decide +kernel

private def st218 : List Sig := [wire44,raw4,wire12,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node218 : search 8 0 st218 = false := by decide +kernel

private def st219 : List Sig := [wire45,raw4,wire12,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node219 : search 8 0 st219 = false := by decide +kernel

private def st220 : List Sig := [wire52,raw5,wire12,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node220 : search 8 0 st220 = false := by decide +kernel

private def st221 : List Sig := [wire53,raw5,wire12,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node221 : search 8 0 st221 = false := by decide +kernel

private def st222 : List Sig := [wire54,raw6,wire12,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node222 : search 8 0 st222 = false := by decide +kernel

private def st223 : List Sig := [wire55,raw6,wire12,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node223 : search 8 0 st223 = false := by decide +kernel

private def st224 : List Sig := [wire12,raw0,raw7,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node224 : search 9 0 st224 = false := by
  apply reject_step 8 0 st224 [] [st187,st188,st189,st190,st191,st192,st193,st194,st195,st196,st197,st198,st199,st200,st201,st202,st203,st204,st205,st206,st207,st208,st209,st210,st211,st212,st213,st214,st215,st216,st217,st218,st219,st220,st221,st222,st223]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node187
    · exact node188
    · exact node189
    · exact node190
    · exact node191
    · exact node192
    · exact node193
    · exact node194
    · exact node195
    · exact node196
    · exact node197
    · exact node198
    · exact node199
    · exact node200
    · exact node201
    · exact node202
    · exact node203
    · exact node204
    · exact node205
    · exact node206
    · exact node207
    · exact node208
    · exact node209
    · exact node210
    · exact node211
    · exact node212
    · exact node213
    · exact node214
    · exact node215
    · exact node216
    · exact node217
    · exact node218
    · exact node219
    · exact node220
    · exact node221
    · exact node222
    · exact node223
  · decide +kernel

private def st225 : List Sig := [wire13,raw0,raw7,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node225 : search 9 0 st225 = false := by decide +kernel

private def st226 : List Sig := [wire112,raw3,raw1,raw2,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node226 : search 8 0 st226 = false := by decide +kernel

private def st227 : List Sig := [wire113,raw1,raw2,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node227 : search 8 0 st227 = false := by decide +kernel

private def st228 : List Sig := [wire113,wire14,raw1,raw2,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node228 : search 8 0 st228 = false := by decide +kernel

private def st229 : List Sig := [wire113,raw3,raw1,raw2,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node229 : search 8 0 st229 = false := by decide +kernel

private def st230 : List Sig := [wire114,raw4,raw1,raw2,raw0,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node230 : search 8 0 st230 = false := by decide +kernel

private def st231 : List Sig := [wire115,raw1,raw2,raw0,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node231 : search 8 0 st231 = false := by decide +kernel

private def st232 : List Sig := [wire115,wire14,raw1,raw2,raw0,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node232 : search 8 0 st232 = false := by decide +kernel

private def st233 : List Sig := [wire115,raw4,raw1,raw2,raw0,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node233 : search 8 0 st233 = false := by decide +kernel

private def st234 : List Sig := [wire116,raw5,raw1,raw2,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node234 : search 8 0 st234 = false := by decide +kernel

private def st235 : List Sig := [wire117,raw1,raw2,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node235 : search 8 0 st235 = false := by decide +kernel

private def st236 : List Sig := [wire117,wire14,raw1,raw2,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node236 : search 8 0 st236 = false := by decide +kernel

private def st237 : List Sig := [wire117,raw5,raw1,raw2,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node237 : search 8 0 st237 = false := by decide +kernel

private def st238 : List Sig := [wire118,raw6,raw1,raw2,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node238 : search 8 0 st238 = false := by decide +kernel

private def st239 : List Sig := [wire119,raw1,raw2,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node239 : search 8 0 st239 = false := by decide +kernel

private def st240 : List Sig := [wire119,wire14,raw1,raw2,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node240 : search 8 0 st240 = false := by decide +kernel

private def st241 : List Sig := [wire119,raw6,raw1,raw2,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node241 : search 8 0 st241 = false := by decide +kernel

private def st242 : List Sig := [wire120,raw7,raw1,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node242 : search 8 0 st242 = false := by decide +kernel

private def st243 : List Sig := [wire121,raw1,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node243 : search 8 0 st243 = false := by decide +kernel

private def st244 : List Sig := [wire121,wire14,raw1,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node244 : search 8 0 st244 = false := by decide +kernel

private def st245 : List Sig := [wire121,raw7,raw1,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node245 : search 8 0 st245 = false := by decide +kernel

private def st246 : List Sig := [wire23,raw6,wire14,raw2,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node246 : search 8 0 st246 = false := by decide +kernel

private def st247 : List Sig := [wire25,wire14,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node247 : search 8 0 st247 = false := by decide +kernel

private def st248 : List Sig := [wire25,raw1,wire14,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node248 : search 8 0 st248 = false := by decide +kernel

private def st249 : List Sig := [wire25,raw7,wire14,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node249 : search 8 0 st249 = false := by decide +kernel

private def st250 : List Sig := [wire27,raw4,wire14,raw1,raw0,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node250 : search 8 0 st250 = false := by decide +kernel

private def st251 : List Sig := [wire56,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node251 : search 8 0 st251 = false := by decide +kernel

private def st252 : List Sig := [wire122,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node252 : search 8 0 st252 = false := by decide +kernel

private def st253 : List Sig := [wire122,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node253 : search 8 0 st253 = false := by decide +kernel

private def st254 : List Sig := [wire122,wire14,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node254 : search 8 0 st254 = false := by decide +kernel

private def st255 : List Sig := [wire0,raw0,wire14,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node255 : search 8 0 st255 = false := by decide +kernel

private def st256 : List Sig := [wire12,raw0,wire14,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node256 : search 8 0 st256 = false := by decide +kernel

private def st257 : List Sig := [wire32,raw3,wire14,raw1,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node257 : search 8 0 st257 = false := by decide +kernel

private def st258 : List Sig := [wire55,raw6,wire14,raw1,raw2,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node258 : search 8 0 st258 = false := by decide +kernel

private def st259 : List Sig := [wire14,raw1,raw2,raw0,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node259 : search 9 0 st259 = false := by
  apply reject_step 8 0 st259 [] [st226,st227,st228,st229,st230,st231,st232,st233,st234,st235,st236,st237,st238,st239,st240,st241,st242,st243,st244,st245,st246,st247,st248,st249,st250,st251,st252,st253,st254,st255,st256,st257,st258]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node226
    · exact node227
    · exact node228
    · exact node229
    · exact node230
    · exact node231
    · exact node232
    · exact node233
    · exact node234
    · exact node235
    · exact node236
    · exact node237
    · exact node238
    · exact node239
    · exact node240
    · exact node241
    · exact node242
    · exact node243
    · exact node244
    · exact node245
    · exact node246
    · exact node247
    · exact node248
    · exact node249
    · exact node250
    · exact node251
    · exact node252
    · exact node253
    · exact node254
    · exact node255
    · exact node256
    · exact node257
    · exact node258
  · decide +kernel

private def st260 : List Sig := [wire15,raw1,raw2,raw0,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node260 : search 9 0 st260 = false := by decide +kernel

private def st261 : List Sig := [wire16,raw1,raw3,raw0,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node261 : search 9 0 st261 = false := by decide +kernel

private def st262 : List Sig := [wire123,raw1,raw3,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node262 : search 8 0 st262 = false := by decide +kernel

private def st263 : List Sig := [wire123,wire17,raw1,raw3,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node263 : search 8 0 st263 = false := by decide +kernel

private def st264 : List Sig := [wire123,raw2,raw1,raw3,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node264 : search 8 0 st264 = false := by decide +kernel

private def st265 : List Sig := [wire124,raw2,raw1,raw3,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node265 : search 8 0 st265 = false := by decide +kernel

private def st266 : List Sig := [wire125,raw4,raw1,raw3,raw0,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node266 : search 8 0 st266 = false := by decide +kernel

private def st267 : List Sig := [wire126,raw4,raw1,raw3,raw0,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node267 : search 8 0 st267 = false := by decide +kernel

private def st268 : List Sig := [wire127,raw5,raw1,raw3,raw0,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node268 : search 8 0 st268 = false := by decide +kernel

private def st269 : List Sig := [wire128,raw5,raw1,raw3,raw0,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node269 : search 8 0 st269 = false := by decide +kernel

private def st270 : List Sig := [wire129,raw6,raw1,raw3,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node270 : search 8 0 st270 = false := by decide +kernel

private def st271 : List Sig := [wire130,raw6,raw1,raw3,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node271 : search 8 0 st271 = false := by decide +kernel

private def st272 : List Sig := [wire131,raw7,raw1,raw3,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node272 : search 8 0 st272 = false := by decide +kernel

private def st273 : List Sig := [wire132,raw7,raw1,raw3,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node273 : search 8 0 st273 = false := by decide +kernel

private def st274 : List Sig := [wire15,raw2,wire17,raw3,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node274 : search 8 0 st274 = false := by decide +kernel

private def st275 : List Sig := [wire19,raw4,wire17,raw3,raw0,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node275 : search 8 0 st275 = false := by decide +kernel

private def st276 : List Sig := [wire23,raw6,wire17,raw3,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node276 : search 8 0 st276 = false := by decide +kernel

private def st277 : List Sig := [wire25,wire17,raw3,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node277 : search 8 0 st277 = false := by decide +kernel

private def st278 : List Sig := [wire25,raw1,wire17,raw3,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node278 : search 8 0 st278 = false := by decide +kernel

private def st279 : List Sig := [wire25,raw7,wire17,raw3,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node279 : search 8 0 st279 = false := by decide +kernel

private def st280 : List Sig := [wire33,raw2,wire17,raw1,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node280 : search 8 0 st280 = false := by decide +kernel

private def st281 : List Sig := [wire34,raw4,wire17,raw1,raw0,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node281 : search 8 0 st281 = false := by decide +kernel

private def st282 : List Sig := [wire37,raw5,wire17,raw1,raw0,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node282 : search 8 0 st282 = false := by decide +kernel

private def st283 : List Sig := [wire133,raw0,raw1,raw3,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node283 : search 8 0 st283 = false := by decide +kernel

private def st284 : List Sig := [wire134,raw0,raw1,raw3,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node284 : search 8 0 st284 = false := by decide +kernel

private def st285 : List Sig := [wire0,raw0,wire17,raw3,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node285 : search 8 0 st285 = false := by decide +kernel

private def st286 : List Sig := [wire5,raw0,wire17,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node286 : search 8 0 st286 = false := by decide +kernel

private def st287 : List Sig := [wire12,raw0,wire17,raw1,raw3,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node287 : search 8 0 st287 = false := by decide +kernel

private def st288 : List Sig := [wire55,raw6,wire17,raw1,raw3,raw0,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node288 : search 8 0 st288 = false := by decide +kernel

private def st289 : List Sig := [wire17,raw1,raw3,raw0,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node289 : search 9 0 st289 = false := by
  apply reject_step 8 0 st289 [] [st262,st263,st264,st265,st266,st267,st268,st269,st270,st271,st272,st273,st274,st275,st276,st277,st278,st279,st280,st281,st282,st283,st284,st285,st286,st287,st288]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node262
    · exact node263
    · exact node264
    · exact node265
    · exact node266
    · exact node267
    · exact node268
    · exact node269
    · exact node270
    · exact node271
    · exact node272
    · exact node273
    · exact node274
    · exact node275
    · exact node276
    · exact node277
    · exact node278
    · exact node279
    · exact node280
    · exact node281
    · exact node282
    · exact node283
    · exact node284
    · exact node285
    · exact node286
    · exact node287
    · exact node288
  · decide +kernel

private def st290 : List Sig := [wire18,raw1,raw4,raw0,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node290 : search 9 0 st290 = false := by decide +kernel

private def st291 : List Sig := [wire19,raw1,raw4,raw0,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node291 : search 9 0 st291 = false := by decide +kernel

private def st292 : List Sig := [wire20,raw1,raw5,raw0,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node292 : search 9 0 st292 = false := by decide +kernel

private def st293 : List Sig := [wire21,raw1,raw5,raw0,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node293 : search 9 0 st293 = false := by decide +kernel

private def st294 : List Sig := [wire22,raw1,raw6,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node294 : search 9 0 st294 = false := by decide +kernel

private def st295 : List Sig := [wire135,raw7,raw1,raw6,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node295 : search 8 0 st295 = false := by decide +kernel

private def st296 : List Sig := [wire136,raw1,raw6,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node296 : search 8 0 st296 = false := by decide +kernel

private def st297 : List Sig := [wire136,wire23,raw1,raw6,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node297 : search 8 0 st297 = false := by decide +kernel

private def st298 : List Sig := [wire136,raw7,raw1,raw6,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node298 : search 8 0 st298 = false := by decide +kernel

private def st299 : List Sig := [wire14,raw2,wire23,raw6,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node299 : search 8 0 st299 = false := by decide +kernel

private def st300 : List Sig := [wire17,raw3,wire23,raw6,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node300 : search 8 0 st300 = false := by decide +kernel

private def st301 : List Sig := [wire21,raw5,wire23,raw6,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node301 : search 8 0 st301 = false := by decide +kernel

private def st302 : List Sig := [wire25,raw1,wire23,raw6,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node302 : search 8 0 st302 = false := by decide +kernel

private def st303 : List Sig := [wire55,raw6,wire23,raw1,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node303 : search 8 0 st303 = false := by decide +kernel

private def st304 : List Sig := [wire137,raw0,raw1,raw6,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node304 : search 8 0 st304 = false := by decide +kernel

private def st305 : List Sig := [wire138,raw0,raw1,raw6,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node305 : search 8 0 st305 = false := by decide +kernel

private def st306 : List Sig := [wire1,raw0,wire23,raw6,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node306 : search 8 0 st306 = false := by decide +kernel

private def st307 : List Sig := [wire11,raw0,wire23,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node307 : search 8 0 st307 = false := by decide +kernel

private def st308 : List Sig := [wire12,raw0,wire23,raw1,raw6,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node308 : search 8 0 st308 = false := by decide +kernel

private def st309 : List Sig := [wire139,raw2,raw1,raw6,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node309 : search 8 0 st309 = false := by decide +kernel

private def st310 : List Sig := [wire140,raw2,raw1,raw6,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node310 : search 8 0 st310 = false := by decide +kernel

private def st311 : List Sig := [wire29,raw2,wire23,raw1,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node311 : search 8 0 st311 = false := by decide +kernel

private def st312 : List Sig := [wire141,raw3,raw1,raw6,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node312 : search 8 0 st312 = false := by decide +kernel

private def st313 : List Sig := [wire130,raw3,raw1,raw6,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node313 : search 8 0 st313 = false := by decide +kernel

private def st314 : List Sig := [wire142,raw4,raw1,raw6,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node314 : search 8 0 st314 = false := by decide +kernel

private def st315 : List Sig := [wire143,raw4,raw1,raw6,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node315 : search 8 0 st315 = false := by decide +kernel

private def st316 : List Sig := [wire43,raw4,wire23,raw1,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node316 : search 8 0 st316 = false := by decide +kernel

private def st317 : List Sig := [wire144,raw5,raw1,raw6,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node317 : search 8 0 st317 = false := by decide +kernel

private def st318 : List Sig := [wire145,raw5,raw1,raw6,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node318 : search 8 0 st318 = false := by decide +kernel

private def st319 : List Sig := [wire50,raw5,wire23,raw1,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node319 : search 8 0 st319 = false := by decide +kernel

private def st320 : List Sig := [wire23,raw1,raw6,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node320 : search 9 0 st320 = false := by
  apply reject_step 8 0 st320 [] [st295,st296,st297,st298,st299,st300,st301,st302,st303,st304,st305,st306,st307,st308,st309,st310,st311,st312,st313,st314,st315,st316,st317,st318,st319]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node295
    · exact node296
    · exact node297
    · exact node298
    · exact node299
    · exact node300
    · exact node301
    · exact node302
    · exact node303
    · exact node304
    · exact node305
    · exact node306
    · exact node307
    · exact node308
    · exact node309
    · exact node310
    · exact node311
    · exact node312
    · exact node313
    · exact node314
    · exact node315
    · exact node316
    · exact node317
    · exact node318
    · exact node319
  · decide +kernel

private def st321 : List Sig := [wire24,raw1,raw7,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node321 : search 9 0 st321 = false := by decide +kernel

private def st322 : List Sig := [wire14,raw2,wire25,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node322 : search 8 0 st322 = false := by decide +kernel

private def st323 : List Sig := [wire14,raw1,raw2,wire25,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node323 : search 8 0 st323 = false := by decide +kernel

private def st324 : List Sig := [wire15,raw1,raw2,wire25,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node324 : search 8 0 st324 = false := by decide +kernel

private def st325 : List Sig := [wire16,raw1,raw3,wire25,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node325 : search 8 0 st325 = false := by decide +kernel

private def st326 : List Sig := [wire17,raw3,wire25,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node326 : search 8 0 st326 = false := by decide +kernel

private def st327 : List Sig := [wire17,raw1,raw3,wire25,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node327 : search 8 0 st327 = false := by decide +kernel

private def st328 : List Sig := [wire18,raw1,raw4,wire25,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node328 : search 8 0 st328 = false := by decide +kernel

private def st329 : List Sig := [wire19,raw1,raw4,wire25,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node329 : search 8 0 st329 = false := by decide +kernel

private def st330 : List Sig := [wire20,raw1,raw5,wire25,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node330 : search 8 0 st330 = false := by decide +kernel

private def st331 : List Sig := [wire21,raw1,raw5,wire25,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node331 : search 8 0 st331 = false := by decide +kernel

private def st332 : List Sig := [wire22,raw1,raw6,wire25,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node332 : search 8 0 st332 = false := by decide +kernel

private def st333 : List Sig := [wire23,raw1,raw6,wire25,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node333 : search 8 0 st333 = false := by decide +kernel

private def st334 : List Sig := [wire146,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node334 : search 8 0 st334 = false := by decide +kernel

private def st335 : List Sig := [wire146,raw0,wire25,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node335 : search 8 0 st335 = false := by decide +kernel

private def st336 : List Sig := [wire147,raw0,wire25,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node336 : search 8 0 st336 = false := by decide +kernel

private def st337 : List Sig := [wire0,raw0,raw1,wire25,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node337 : search 8 0 st337 = false := by decide +kernel

private def st338 : List Sig := [wire1,raw0,wire25,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node338 : search 8 0 st338 = false := by decide +kernel

private def st339 : List Sig := [wire1,raw0,raw1,wire25,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node339 : search 8 0 st339 = false := by decide +kernel

private def st340 : List Sig := [wire2,raw0,raw2,wire25,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node340 : search 8 0 st340 = false := by decide +kernel

private def st341 : List Sig := [wire3,raw0,raw2,wire25,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node341 : search 8 0 st341 = false := by decide +kernel

private def st342 : List Sig := [wire4,raw0,raw3,wire25,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node342 : search 8 0 st342 = false := by decide +kernel

private def st343 : List Sig := [wire5,raw0,raw3,wire25,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node343 : search 8 0 st343 = false := by decide +kernel

private def st344 : List Sig := [wire6,raw0,raw4,wire25,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node344 : search 8 0 st344 = false := by decide +kernel

private def st345 : List Sig := [wire7,raw0,raw4,wire25,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node345 : search 8 0 st345 = false := by decide +kernel

private def st346 : List Sig := [wire8,raw0,raw5,wire25,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node346 : search 8 0 st346 = false := by decide +kernel

private def st347 : List Sig := [wire9,raw0,raw5,wire25,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node347 : search 8 0 st347 = false := by decide +kernel

private def st348 : List Sig := [wire10,raw0,raw6,wire25,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node348 : search 8 0 st348 = false := by decide +kernel

private def st349 : List Sig := [wire11,raw0,raw6,wire25,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node349 : search 8 0 st349 = false := by decide +kernel

private def st350 : List Sig := [wire148,raw2,wire25,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node350 : search 8 0 st350 = false := by decide +kernel

private def st351 : List Sig := [wire149,raw2,wire25,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node351 : search 8 0 st351 = false := by decide +kernel

private def st352 : List Sig := [wire26,raw2,raw4,wire25,raw1,raw0,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node352 : search 8 0 st352 = false := by decide +kernel

private def st353 : List Sig := [wire27,raw2,raw4,wire25,raw1,raw0,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node353 : search 8 0 st353 = false := by decide +kernel

private def st354 : List Sig := [wire28,raw2,raw6,wire25,raw1,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node354 : search 8 0 st354 = false := by decide +kernel

private def st355 : List Sig := [wire29,raw2,raw6,wire25,raw1,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node355 : search 8 0 st355 = false := by decide +kernel

private def st356 : List Sig := [wire150,raw3,wire25,raw1,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node356 : search 8 0 st356 = false := by decide +kernel

private def st357 : List Sig := [wire132,raw3,wire25,raw1,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node357 : search 8 0 st357 = false := by decide +kernel

private def st358 : List Sig := [wire32,raw3,raw2,wire25,raw1,raw0,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node358 : search 8 0 st358 = false := by decide +kernel

private def st359 : List Sig := [wire33,raw3,raw2,wire25,raw1,raw0,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node359 : search 8 0 st359 = false := by decide +kernel

private def st360 : List Sig := [wire34,raw3,raw4,wire25,raw1,raw0,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node360 : search 8 0 st360 = false := by decide +kernel

private def st361 : List Sig := [wire35,raw3,raw4,wire25,raw1,raw0,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node361 : search 8 0 st361 = false := by decide +kernel

private def st362 : List Sig := [wire36,raw3,raw5,wire25,raw1,raw0,raw2,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node362 : search 8 0 st362 = false := by decide +kernel

private def st363 : List Sig := [wire37,raw3,raw5,wire25,raw1,raw0,raw2,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node363 : search 8 0 st363 = false := by decide +kernel

private def st364 : List Sig := [wire38,raw3,raw6,wire25,raw1,raw0,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node364 : search 8 0 st364 = false := by decide +kernel

private def st365 : List Sig := [wire39,raw3,raw6,wire25,raw1,raw0,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node365 : search 8 0 st365 = false := by decide +kernel

private def st366 : List Sig := [wire151,raw4,wire25,raw1,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node366 : search 8 0 st366 = false := by decide +kernel

private def st367 : List Sig := [wire152,raw4,wire25,raw1,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node367 : search 8 0 st367 = false := by decide +kernel

private def st368 : List Sig := [wire42,raw4,raw6,wire25,raw1,raw0,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node368 : search 8 0 st368 = false := by decide +kernel

private def st369 : List Sig := [wire43,raw4,raw6,wire25,raw1,raw0,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node369 : search 8 0 st369 = false := by decide +kernel

private def st370 : List Sig := [wire153,raw5,wire25,raw1,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node370 : search 8 0 st370 = false := by decide +kernel

private def st371 : List Sig := [wire154,raw5,wire25,raw1,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node371 : search 8 0 st371 = false := by decide +kernel

private def st372 : List Sig := [wire46,raw5,raw2,wire25,raw1,raw0,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node372 : search 8 0 st372 = false := by decide +kernel

private def st373 : List Sig := [wire47,raw5,raw2,wire25,raw1,raw0,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node373 : search 8 0 st373 = false := by decide +kernel

private def st374 : List Sig := [wire48,raw5,raw4,wire25,raw1,raw0,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node374 : search 8 0 st374 = false := by decide +kernel

private def st375 : List Sig := [wire49,raw5,raw4,wire25,raw1,raw0,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node375 : search 8 0 st375 = false := by decide +kernel

private def st376 : List Sig := [wire50,raw5,raw6,wire25,raw1,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node376 : search 8 0 st376 = false := by decide +kernel

private def st377 : List Sig := [wire51,raw5,raw6,wire25,raw1,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node377 : search 8 0 st377 = false := by decide +kernel

private def st378 : List Sig := [wire155,raw6,wire25,raw1,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node378 : search 8 0 st378 = false := by decide +kernel

private def st379 : List Sig := [wire136,raw6,raw1,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node379 : search 8 0 st379 = false := by decide +kernel

private def st380 : List Sig := [wire136,raw6,wire25,raw1,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node380 : search 8 0 st380 = false := by decide +kernel

private def st381 : List Sig := [wire25,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node381 : search 9 0 st381 = false := by
  apply reject_step 8 0 st381 [] [st322,st323,st324,st325,st326,st327,st328,st329,st330,st331,st332,st333,st334,st335,st336,st337,st338,st339,st340,st341,st342,st343,st344,st345,st346,st347,st348,st349,st350,st351,st352,st353,st354,st355,st356,st357,st358,st359,st360,st361,st362,st363,st364,st365,st366,st367,st368,st369,st370,st371,st372,st373,st374,st375,st376,st377,st378,st379,st380]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node322
    · exact node323
    · exact node324
    · exact node325
    · exact node326
    · exact node327
    · exact node328
    · exact node329
    · exact node330
    · exact node331
    · exact node332
    · exact node333
    · exact node334
    · exact node335
    · exact node336
    · exact node337
    · exact node338
    · exact node339
    · exact node340
    · exact node341
    · exact node342
    · exact node343
    · exact node344
    · exact node345
    · exact node346
    · exact node347
    · exact node348
    · exact node349
    · exact node350
    · exact node351
    · exact node352
    · exact node353
    · exact node354
    · exact node355
    · exact node356
    · exact node357
    · exact node358
    · exact node359
    · exact node360
    · exact node361
    · exact node362
    · exact node363
    · exact node364
    · exact node365
    · exact node366
    · exact node367
    · exact node368
    · exact node369
    · exact node370
    · exact node371
    · exact node372
    · exact node373
    · exact node374
    · exact node375
    · exact node376
    · exact node377
    · exact node378
    · exact node379
    · exact node380
  · decide +kernel

private def st382 : List Sig := [wire25,raw1,raw7,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node382 : search 9 0 st382 = false := by decide +kernel

private def st383 : List Sig := [wire26,raw2,raw4,raw0,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node383 : search 9 0 st383 = false := by decide +kernel

private def st384 : List Sig := [wire156,raw6,raw2,raw4,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node384 : search 8 0 st384 = false := by decide +kernel

private def st385 : List Sig := [wire157,raw6,raw2,raw4,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node385 : search 8 0 st385 = false := by decide +kernel

private def st386 : List Sig := [wire158,raw7,raw2,raw4,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node386 : search 8 0 st386 = false := by decide +kernel

private def st387 : List Sig := [wire159,raw7,raw2,raw4,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node387 : search 8 0 st387 = false := by decide +kernel

private def st388 : List Sig := [wire43,raw6,wire27,raw2,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node388 : search 8 0 st388 = false := by decide +kernel

private def st389 : List Sig := [wire160,raw0,raw2,raw4,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node389 : search 8 0 st389 = false := by decide +kernel

private def st390 : List Sig := [wire69,raw0,raw2,raw4,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node390 : search 8 0 st390 = false := by decide +kernel

private def st391 : List Sig := [wire3,raw0,wire27,raw4,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node391 : search 8 0 st391 = false := by decide +kernel

private def st392 : List Sig := [wire12,raw0,wire27,raw2,raw4,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node392 : search 8 0 st392 = false := by decide +kernel

private def st393 : List Sig := [wire161,raw1,raw2,raw4,raw0,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node393 : search 8 0 st393 = false := by decide +kernel

private def st394 : List Sig := [wire162,raw1,raw2,raw4,raw0,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node394 : search 8 0 st394 = false := by decide +kernel

private def st395 : List Sig := [wire14,raw1,wire27,raw4,raw0,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node395 : search 8 0 st395 = false := by decide +kernel

private def st396 : List Sig := [wire19,raw1,wire27,raw2,raw0,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node396 : search 8 0 st396 = false := by decide +kernel

private def st397 : List Sig := [wire25,raw1,wire27,raw2,raw4,raw0,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node397 : search 8 0 st397 = false := by decide +kernel

private def st398 : List Sig := [wire163,raw2,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node398 : search 8 0 st398 = false := by decide +kernel

private def st399 : List Sig := [wire163,raw3,raw2,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node399 : search 8 0 st399 = false := by decide +kernel

private def st400 : List Sig := [wire163,wire27,raw2,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node400 : search 8 0 st400 = false := by decide +kernel

private def st401 : List Sig := [wire164,raw3,raw2,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node401 : search 8 0 st401 = false := by decide +kernel

private def st402 : List Sig := [wire33,raw3,wire27,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node402 : search 8 0 st402 = false := by decide +kernel

private def st403 : List Sig := [wire35,raw3,wire27,raw2,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node403 : search 8 0 st403 = false := by decide +kernel

private def st404 : List Sig := [wire165,raw5,raw2,raw4,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node404 : search 8 0 st404 = false := by decide +kernel

private def st405 : List Sig := [wire166,raw5,raw2,raw4,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node405 : search 8 0 st405 = false := by decide +kernel

private def st406 : List Sig := [wire47,raw5,wire27,raw4,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node406 : search 8 0 st406 = false := by decide +kernel

private def st407 : List Sig := [wire48,raw5,wire27,raw2,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node407 : search 8 0 st407 = false := by decide +kernel

private def st408 : List Sig := [wire55,raw6,wire27,raw2,raw4,raw0,raw1,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node408 : search 8 0 st408 = false := by decide +kernel

private def st409 : List Sig := [wire27,raw2,raw4,raw0,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node409 : search 9 0 st409 = false := by
  apply reject_step 8 0 st409 [] [st384,st385,st386,st387,st388,st389,st390,st391,st392,st393,st394,st395,st396,st397,st398,st399,st400,st401,st402,st403,st404,st405,st406,st407,st408]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node384
    · exact node385
    · exact node386
    · exact node387
    · exact node388
    · exact node389
    · exact node390
    · exact node391
    · exact node392
    · exact node393
    · exact node394
    · exact node395
    · exact node396
    · exact node397
    · exact node398
    · exact node399
    · exact node400
    · exact node401
    · exact node402
    · exact node403
    · exact node404
    · exact node405
    · exact node406
    · exact node407
    · exact node408
  · decide +kernel

private def st410 : List Sig := [wire28,raw2,raw6,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node410 : search 9 0 st410 = false := by decide +kernel

private def st411 : List Sig := [wire29,raw2,raw6,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node411 : search 9 0 st411 = false := by decide +kernel

private def st412 : List Sig := [wire30,raw2,raw7,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node412 : search 9 0 st412 = false := by decide +kernel

private def st413 : List Sig := [wire31,raw2,raw7,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node413 : search 9 0 st413 = false := by decide +kernel

private def st414 : List Sig := [wire167,raw4,raw3,raw2,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node414 : search 8 0 st414 = false := by decide +kernel

private def st415 : List Sig := [wire168,raw3,raw2,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node415 : search 8 0 st415 = false := by decide +kernel

private def st416 : List Sig := [wire168,wire32,raw3,raw2,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node416 : search 8 0 st416 = false := by decide +kernel

private def st417 : List Sig := [wire168,raw4,raw3,raw2,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node417 : search 8 0 st417 = false := by decide +kernel

private def st418 : List Sig := [wire169,raw5,raw3,raw2,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node418 : search 8 0 st418 = false := by decide +kernel

private def st419 : List Sig := [wire170,raw3,raw2,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node419 : search 8 0 st419 = false := by decide +kernel

private def st420 : List Sig := [wire170,wire32,raw3,raw2,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node420 : search 8 0 st420 = false := by decide +kernel

private def st421 : List Sig := [wire170,raw5,raw3,raw2,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node421 : search 8 0 st421 = false := by decide +kernel

private def st422 : List Sig := [wire171,raw6,raw3,raw2,raw0,raw1,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node422 : search 8 0 st422 = false := by decide +kernel

private def st423 : List Sig := [wire172,raw3,raw2,raw0,raw1,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node423 : search 8 0 st423 = false := by decide +kernel

private def st424 : List Sig := [wire172,wire32,raw3,raw2,raw0,raw1,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node424 : search 8 0 st424 = false := by decide +kernel

private def st425 : List Sig := [wire172,raw6,raw3,raw2,raw0,raw1,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node425 : search 8 0 st425 = false := by decide +kernel

private def st426 : List Sig := [wire173,raw7,raw3,raw2,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node426 : search 8 0 st426 = false := by decide +kernel

private def st427 : List Sig := [wire174,raw3,raw2,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node427 : search 8 0 st427 = false := by decide +kernel

private def st428 : List Sig := [wire174,wire32,raw3,raw2,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node428 : search 8 0 st428 = false := by decide +kernel

private def st429 : List Sig := [wire174,raw7,raw3,raw2,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node429 : search 8 0 st429 = false := by decide +kernel

private def st430 : List Sig := [wire34,raw4,wire32,raw2,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node430 : search 8 0 st430 = false := by decide +kernel

private def st431 : List Sig := [wire37,raw5,wire32,raw2,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node431 : search 8 0 st431 = false := by decide +kernel

private def st432 : List Sig := [wire175,raw0,raw3,raw2,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node432 : search 8 0 st432 = false := by decide +kernel

private def st433 : List Sig := [wire176,raw3,raw2,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node433 : search 8 0 st433 = false := by decide +kernel

private def st434 : List Sig := [wire176,raw0,raw3,raw2,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node434 : search 8 0 st434 = false := by decide +kernel

private def st435 : List Sig := [wire176,wire32,raw3,raw2,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node435 : search 8 0 st435 = false := by decide +kernel

private def st436 : List Sig := [wire3,raw0,wire32,raw3,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node436 : search 8 0 st436 = false := by decide +kernel

private def st437 : List Sig := [wire12,raw0,wire32,raw3,raw2,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node437 : search 8 0 st437 = false := by decide +kernel

private def st438 : List Sig := [wire112,raw1,raw3,raw2,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node438 : search 8 0 st438 = false := by decide +kernel

private def st439 : List Sig := [wire177,raw3,raw2,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node439 : search 8 0 st439 = false := by decide +kernel

private def st440 : List Sig := [wire177,raw1,raw3,raw2,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node440 : search 8 0 st440 = false := by decide +kernel

private def st441 : List Sig := [wire177,wire32,raw3,raw2,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node441 : search 8 0 st441 = false := by decide +kernel

private def st442 : List Sig := [wire14,raw1,wire32,raw3,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node442 : search 8 0 st442 = false := by decide +kernel

private def st443 : List Sig := [wire25,raw1,wire32,raw3,raw2,raw0,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node443 : search 8 0 st443 = false := by decide +kernel

private def st444 : List Sig := [wire55,raw6,wire32,raw3,raw2,raw0,raw1,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node444 : search 8 0 st444 = false := by decide +kernel

private def st445 : List Sig := [wire32,raw3,raw2,raw0,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node445 : search 9 0 st445 = false := by
  apply reject_step 8 0 st445 [] [st414,st415,st416,st417,st418,st419,st420,st421,st422,st423,st424,st425,st426,st427,st428,st429,st430,st431,st432,st433,st434,st435,st436,st437,st438,st439,st440,st441,st442,st443,st444]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node414
    · exact node415
    · exact node416
    · exact node417
    · exact node418
    · exact node419
    · exact node420
    · exact node421
    · exact node422
    · exact node423
    · exact node424
    · exact node425
    · exact node426
    · exact node427
    · exact node428
    · exact node429
    · exact node430
    · exact node431
    · exact node432
    · exact node433
    · exact node434
    · exact node435
    · exact node436
    · exact node437
    · exact node438
    · exact node439
    · exact node440
    · exact node441
    · exact node442
    · exact node443
    · exact node444
  · decide +kernel

private def st446 : List Sig := [wire33,raw3,raw2,raw0,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node446 : search 9 0 st446 = false := by decide +kernel

private def st447 : List Sig := [wire167,raw2,raw3,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node447 : search 8 0 st447 = false := by decide +kernel

private def st448 : List Sig := [wire178,raw3,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node448 : search 8 0 st448 = false := by decide +kernel

private def st449 : List Sig := [wire178,wire34,raw3,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node449 : search 8 0 st449 = false := by decide +kernel

private def st450 : List Sig := [wire178,raw2,raw3,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node450 : search 8 0 st450 = false := by decide +kernel

private def st451 : List Sig := [wire179,raw5,raw3,raw4,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node451 : search 8 0 st451 = false := by decide +kernel

private def st452 : List Sig := [wire180,raw3,raw4,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node452 : search 8 0 st452 = false := by decide +kernel

private def st453 : List Sig := [wire180,wire34,raw3,raw4,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node453 : search 8 0 st453 = false := by decide +kernel

private def st454 : List Sig := [wire180,raw5,raw3,raw4,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node454 : search 8 0 st454 = false := by decide +kernel

private def st455 : List Sig := [wire181,raw6,raw3,raw4,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node455 : search 8 0 st455 = false := by decide +kernel

private def st456 : List Sig := [wire182,raw3,raw4,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node456 : search 8 0 st456 = false := by decide +kernel

private def st457 : List Sig := [wire182,wire34,raw3,raw4,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node457 : search 8 0 st457 = false := by decide +kernel

private def st458 : List Sig := [wire182,raw6,raw3,raw4,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node458 : search 8 0 st458 = false := by decide +kernel

private def st459 : List Sig := [wire183,raw7,raw3,raw4,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node459 : search 8 0 st459 = false := by decide +kernel

private def st460 : List Sig := [wire184,raw3,raw4,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node460 : search 8 0 st460 = false := by decide +kernel

private def st461 : List Sig := [wire184,wire34,raw3,raw4,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node461 : search 8 0 st461 = false := by decide +kernel

private def st462 : List Sig := [wire184,raw7,raw3,raw4,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node462 : search 8 0 st462 = false := by decide +kernel

private def st463 : List Sig := [wire32,raw2,wire34,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node463 : search 8 0 st463 = false := by decide +kernel

private def st464 : List Sig := [wire43,raw6,wire34,raw3,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node464 : search 8 0 st464 = false := by decide +kernel

private def st465 : List Sig := [wire185,raw0,raw3,raw4,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node465 : search 8 0 st465 = false := by decide +kernel

private def st466 : List Sig := [wire186,raw3,raw4,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node466 : search 8 0 st466 = false := by decide +kernel

private def st467 : List Sig := [wire186,raw0,raw3,raw4,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node467 : search 8 0 st467 = false := by decide +kernel

private def st468 : List Sig := [wire186,wire34,raw3,raw4,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node468 : search 8 0 st468 = false := by decide +kernel

private def st469 : List Sig := [wire12,raw0,wire34,raw3,raw4,raw1,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node469 : search 8 0 st469 = false := by decide +kernel

private def st470 : List Sig := [wire187,raw1,raw3,raw4,raw0,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node470 : search 8 0 st470 = false := by decide +kernel

private def st471 : List Sig := [wire188,raw3,raw4,raw0,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node471 : search 8 0 st471 = false := by decide +kernel

private def st472 : List Sig := [wire188,raw1,raw3,raw4,raw0,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node472 : search 8 0 st472 = false := by decide +kernel

private def st473 : List Sig := [wire188,wire34,raw3,raw4,raw0,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node473 : search 8 0 st473 = false := by decide +kernel

private def st474 : List Sig := [wire17,raw1,wire34,raw4,raw0,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node474 : search 8 0 st474 = false := by decide +kernel

private def st475 : List Sig := [wire25,raw1,wire34,raw3,raw4,raw0,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node475 : search 8 0 st475 = false := by decide +kernel

private def st476 : List Sig := [wire48,raw5,wire34,raw3,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node476 : search 8 0 st476 = false := by decide +kernel

private def st477 : List Sig := [wire55,raw6,wire34,raw3,raw4,raw0,raw1,raw2,raw5]

set_option maxRecDepth 10000 in
private theorem node477 : search 8 0 st477 = false := by decide +kernel

private def st478 : List Sig := [wire34,raw3,raw4,raw0,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node478 : search 9 0 st478 = false := by
  apply reject_step 8 0 st478 [] [st447,st448,st449,st450,st451,st452,st453,st454,st455,st456,st457,st458,st459,st460,st461,st462,st463,st464,st465,st466,st467,st468,st469,st470,st471,st472,st473,st474,st475,st476,st477]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node447
    · exact node448
    · exact node449
    · exact node450
    · exact node451
    · exact node452
    · exact node453
    · exact node454
    · exact node455
    · exact node456
    · exact node457
    · exact node458
    · exact node459
    · exact node460
    · exact node461
    · exact node462
    · exact node463
    · exact node464
    · exact node465
    · exact node466
    · exact node467
    · exact node468
    · exact node469
    · exact node470
    · exact node471
    · exact node472
    · exact node473
    · exact node474
    · exact node475
    · exact node476
    · exact node477
  · decide +kernel

private def st479 : List Sig := [wire35,raw3,raw4,raw0,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node479 : search 9 0 st479 = false := by decide +kernel

private def st480 : List Sig := [wire36,raw3,raw5,raw0,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node480 : search 9 0 st480 = false := by decide +kernel

private def st481 : List Sig := [wire189,raw2,raw3,raw5,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node481 : search 8 0 st481 = false := by decide +kernel

private def st482 : List Sig := [wire190,raw2,raw3,raw5,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node482 : search 8 0 st482 = false := by decide +kernel

private def st483 : List Sig := [wire191,raw3,raw5,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node483 : search 8 0 st483 = false := by decide +kernel

private def st484 : List Sig := [wire191,wire37,raw3,raw5,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node484 : search 8 0 st484 = false := by decide +kernel

private def st485 : List Sig := [wire191,raw4,raw3,raw5,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node485 : search 8 0 st485 = false := by decide +kernel

private def st486 : List Sig := [wire192,raw4,raw3,raw5,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node486 : search 8 0 st486 = false := by decide +kernel

private def st487 : List Sig := [wire193,raw6,raw3,raw5,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node487 : search 8 0 st487 = false := by decide +kernel

private def st488 : List Sig := [wire194,raw6,raw3,raw5,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node488 : search 8 0 st488 = false := by decide +kernel

private def st489 : List Sig := [wire195,raw7,raw3,raw5,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node489 : search 8 0 st489 = false := by decide +kernel

private def st490 : List Sig := [wire196,raw7,raw3,raw5,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node490 : search 8 0 st490 = false := by decide +kernel

private def st491 : List Sig := [wire32,raw2,wire37,raw5,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node491 : search 8 0 st491 = false := by decide +kernel

private def st492 : List Sig := [wire35,raw4,wire37,raw5,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node492 : search 8 0 st492 = false := by decide +kernel

private def st493 : List Sig := [wire39,raw6,wire37,raw5,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node493 : search 8 0 st493 = false := by decide +kernel

private def st494 : List Sig := [wire47,raw2,wire37,raw3,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node494 : search 8 0 st494 = false := by decide +kernel

private def st495 : List Sig := [wire49,raw4,wire37,raw3,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node495 : search 8 0 st495 = false := by decide +kernel

private def st496 : List Sig := [wire50,raw6,wire37,raw3,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node496 : search 8 0 st496 = false := by decide +kernel

private def st497 : List Sig := [wire197,raw0,raw3,raw5,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node497 : search 8 0 st497 = false := by decide +kernel

private def st498 : List Sig := [wire90,raw0,raw3,raw5,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node498 : search 8 0 st498 = false := by decide +kernel

private def st499 : List Sig := [wire9,raw0,wire37,raw3,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node499 : search 8 0 st499 = false := by decide +kernel

private def st500 : List Sig := [wire12,raw0,wire37,raw3,raw5,raw1,raw2,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node500 : search 8 0 st500 = false := by decide +kernel

private def st501 : List Sig := [wire198,raw1,raw3,raw5,raw0,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node501 : search 8 0 st501 = false := by decide +kernel

private def st502 : List Sig := [wire128,raw1,raw3,raw5,raw0,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node502 : search 8 0 st502 = false := by decide +kernel

private def st503 : List Sig := [wire17,raw1,wire37,raw5,raw0,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node503 : search 8 0 st503 = false := by decide +kernel

private def st504 : List Sig := [wire25,raw1,wire37,raw3,raw5,raw0,raw2,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node504 : search 8 0 st504 = false := by decide +kernel

private def st505 : List Sig := [wire55,raw6,wire37,raw3,raw5,raw0,raw1,raw2,raw4]

set_option maxRecDepth 10000 in
private theorem node505 : search 8 0 st505 = false := by decide +kernel

private def st506 : List Sig := [wire37,raw3,raw5,raw0,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node506 : search 9 0 st506 = false := by
  apply reject_step 8 0 st506 [] [st481,st482,st483,st484,st485,st486,st487,st488,st489,st490,st491,st492,st493,st494,st495,st496,st497,st498,st499,st500,st501,st502,st503,st504,st505]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node481
    · exact node482
    · exact node483
    · exact node484
    · exact node485
    · exact node486
    · exact node487
    · exact node488
    · exact node489
    · exact node490
    · exact node491
    · exact node492
    · exact node493
    · exact node494
    · exact node495
    · exact node496
    · exact node497
    · exact node498
    · exact node499
    · exact node500
    · exact node501
    · exact node502
    · exact node503
    · exact node504
    · exact node505
  · decide +kernel

private def st507 : List Sig := [wire38,raw3,raw6,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node507 : search 9 0 st507 = false := by decide +kernel

private def st508 : List Sig := [wire39,raw3,raw6,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node508 : search 9 0 st508 = false := by decide +kernel

private def st509 : List Sig := [wire40,raw3,raw7,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node509 : search 9 0 st509 = false := by decide +kernel

private def st510 : List Sig := [wire41,raw3,raw7,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node510 : search 9 0 st510 = false := by decide +kernel

private def st511 : List Sig := [wire42,raw4,raw6,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node511 : search 9 0 st511 = false := by decide +kernel

private def st512 : List Sig := [wire199,raw7,raw4,raw6,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node512 : search 8 0 st512 = false := by decide +kernel

private def st513 : List Sig := [wire200,raw7,raw4,raw6,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node513 : search 8 0 st513 = false := by decide +kernel

private def st514 : List Sig := [wire55,wire43,raw4,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node514 : search 8 0 st514 = false := by decide +kernel

private def st515 : List Sig := [wire55,raw6,wire43,raw4,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node515 : search 8 0 st515 = false := by decide +kernel

private def st516 : List Sig := [wire55,raw7,wire43,raw4,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node516 : search 8 0 st516 = false := by decide +kernel

private def st517 : List Sig := [wire201,raw0,raw4,raw6,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node517 : search 8 0 st517 = false := by decide +kernel

private def st518 : List Sig := [wire202,raw0,raw4,raw6,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node518 : search 8 0 st518 = false := by decide +kernel

private def st519 : List Sig := [wire7,raw0,wire43,raw6,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node519 : search 8 0 st519 = false := by decide +kernel

private def st520 : List Sig := [wire10,raw0,wire43,raw4,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node520 : search 8 0 st520 = false := by decide +kernel

private def st521 : List Sig := [wire12,raw0,wire43,raw4,raw6,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node521 : search 8 0 st521 = false := by decide +kernel

private def st522 : List Sig := [wire203,raw1,raw4,raw6,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node522 : search 8 0 st522 = false := by decide +kernel

private def st523 : List Sig := [wire143,raw1,raw4,raw6,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node523 : search 8 0 st523 = false := by decide +kernel

private def st524 : List Sig := [wire23,raw1,wire43,raw4,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node524 : search 8 0 st524 = false := by decide +kernel

private def st525 : List Sig := [wire25,raw1,wire43,raw4,raw6,raw0,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node525 : search 8 0 st525 = false := by decide +kernel

private def st526 : List Sig := [wire204,raw2,raw4,raw6,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node526 : search 8 0 st526 = false := by decide +kernel

private def st527 : List Sig := [wire157,raw2,raw4,raw6,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node527 : search 8 0 st527 = false := by decide +kernel

private def st528 : List Sig := [wire27,raw2,wire43,raw6,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node528 : search 8 0 st528 = false := by decide +kernel

private def st529 : List Sig := [wire205,raw3,raw4,raw6,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node529 : search 8 0 st529 = false := by decide +kernel

private def st530 : List Sig := [wire206,raw3,raw4,raw6,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node530 : search 8 0 st530 = false := by decide +kernel

private def st531 : List Sig := [wire34,raw3,wire43,raw6,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node531 : search 8 0 st531 = false := by decide +kernel

private def st532 : List Sig := [wire39,raw3,wire43,raw4,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node532 : search 8 0 st532 = false := by decide +kernel

private def st533 : List Sig := [wire207,raw4,raw6,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node533 : search 8 0 st533 = false := by decide +kernel

private def st534 : List Sig := [wire207,raw5,raw4,raw6,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node534 : search 8 0 st534 = false := by decide +kernel

private def st535 : List Sig := [wire207,wire43,raw4,raw6,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node535 : search 8 0 st535 = false := by decide +kernel

private def st536 : List Sig := [wire208,raw5,raw4,raw6,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node536 : search 8 0 st536 = false := by decide +kernel

private def st537 : List Sig := [wire49,raw5,wire43,raw6,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node537 : search 8 0 st537 = false := by decide +kernel

private def st538 : List Sig := [wire51,raw5,wire43,raw4,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node538 : search 8 0 st538 = false := by decide +kernel

private def st539 : List Sig := [wire43,raw4,raw6,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node539 : search 9 0 st539 = false := by
  apply reject_step 8 0 st539 [] [st512,st513,st514,st515,st516,st517,st518,st519,st520,st521,st522,st523,st524,st525,st526,st527,st528,st529,st530,st531,st532,st533,st534,st535,st536,st537,st538]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node512
    · exact node513
    · exact node514
    · exact node515
    · exact node516
    · exact node517
    · exact node518
    · exact node519
    · exact node520
    · exact node521
    · exact node522
    · exact node523
    · exact node524
    · exact node525
    · exact node526
    · exact node527
    · exact node528
    · exact node529
    · exact node530
    · exact node531
    · exact node532
    · exact node533
    · exact node534
    · exact node535
    · exact node536
    · exact node537
    · exact node538
  · decide +kernel

private def st540 : List Sig := [wire44,raw4,raw7,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node540 : search 9 0 st540 = false := by decide +kernel

private def st541 : List Sig := [wire45,raw4,raw7,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node541 : search 9 0 st541 = false := by decide +kernel

private def st542 : List Sig := [wire46,raw5,raw2,raw0,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node542 : search 9 0 st542 = false := by decide +kernel

private def st543 : List Sig := [wire47,raw5,raw2,raw0,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node543 : search 9 0 st543 = false := by decide +kernel

private def st544 : List Sig := [wire209,raw2,raw5,raw4,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node544 : search 8 0 st544 = false := by decide +kernel

private def st545 : List Sig := [wire210,raw5,raw4,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node545 : search 8 0 st545 = false := by decide +kernel

private def st546 : List Sig := [wire210,wire48,raw5,raw4,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node546 : search 8 0 st546 = false := by decide +kernel

private def st547 : List Sig := [wire210,raw2,raw5,raw4,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node547 : search 8 0 st547 = false := by decide +kernel

private def st548 : List Sig := [wire211,raw6,raw5,raw4,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node548 : search 8 0 st548 = false := by decide +kernel

private def st549 : List Sig := [wire212,raw5,raw4,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node549 : search 8 0 st549 = false := by decide +kernel

private def st550 : List Sig := [wire212,wire48,raw5,raw4,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node550 : search 8 0 st550 = false := by decide +kernel

private def st551 : List Sig := [wire212,raw6,raw5,raw4,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node551 : search 8 0 st551 = false := by decide +kernel

private def st552 : List Sig := [wire213,raw7,raw5,raw4,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node552 : search 8 0 st552 = false := by decide +kernel

private def st553 : List Sig := [wire214,raw5,raw4,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node553 : search 8 0 st553 = false := by decide +kernel

private def st554 : List Sig := [wire214,wire48,raw5,raw4,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node554 : search 8 0 st554 = false := by decide +kernel

private def st555 : List Sig := [wire214,raw7,raw5,raw4,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node555 : search 8 0 st555 = false := by decide +kernel

private def st556 : List Sig := [wire50,raw6,wire48,raw4,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node556 : search 8 0 st556 = false := by decide +kernel

private def st557 : List Sig := [wire215,raw0,raw5,raw4,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node557 : search 8 0 st557 = false := by decide +kernel

private def st558 : List Sig := [wire216,raw5,raw4,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node558 : search 8 0 st558 = false := by decide +kernel

private def st559 : List Sig := [wire216,raw0,raw5,raw4,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node559 : search 8 0 st559 = false := by decide +kernel

private def st560 : List Sig := [wire216,wire48,raw5,raw4,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node560 : search 8 0 st560 = false := by decide +kernel

private def st561 : List Sig := [wire9,raw0,wire48,raw4,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node561 : search 8 0 st561 = false := by decide +kernel

private def st562 : List Sig := [wire12,raw0,wire48,raw5,raw4,raw1,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node562 : search 8 0 st562 = false := by decide +kernel

private def st563 : List Sig := [wire217,raw1,raw5,raw4,raw0,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node563 : search 8 0 st563 = false := by decide +kernel

private def st564 : List Sig := [wire218,raw5,raw4,raw0,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node564 : search 8 0 st564 = false := by decide +kernel

private def st565 : List Sig := [wire218,raw1,raw5,raw4,raw0,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node565 : search 8 0 st565 = false := by decide +kernel

private def st566 : List Sig := [wire218,wire48,raw5,raw4,raw0,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node566 : search 8 0 st566 = false := by decide +kernel

private def st567 : List Sig := [wire25,raw1,wire48,raw5,raw4,raw0,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node567 : search 8 0 st567 = false := by decide +kernel

private def st568 : List Sig := [wire27,raw2,wire48,raw5,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node568 : search 8 0 st568 = false := by decide +kernel

private def st569 : List Sig := [wire179,raw3,raw5,raw4,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node569 : search 8 0 st569 = false := by decide +kernel

private def st570 : List Sig := [wire219,raw5,raw4,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node570 : search 8 0 st570 = false := by decide +kernel

private def st571 : List Sig := [wire219,raw3,raw5,raw4,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node571 : search 8 0 st571 = false := by decide +kernel

private def st572 : List Sig := [wire219,wire48,raw5,raw4,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node572 : search 8 0 st572 = false := by decide +kernel

private def st573 : List Sig := [wire34,raw3,wire48,raw5,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node573 : search 8 0 st573 = false := by decide +kernel

private def st574 : List Sig := [wire55,raw6,wire48,raw5,raw4,raw0,raw1,raw2,raw3]

set_option maxRecDepth 10000 in
private theorem node574 : search 8 0 st574 = false := by decide +kernel

private def st575 : List Sig := [wire48,raw5,raw4,raw0,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node575 : search 9 0 st575 = false := by
  apply reject_step 8 0 st575 [] [st544,st545,st546,st547,st548,st549,st550,st551,st552,st553,st554,st555,st556,st557,st558,st559,st560,st561,st562,st563,st564,st565,st566,st567,st568,st569,st570,st571,st572,st573,st574]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node544
    · exact node545
    · exact node546
    · exact node547
    · exact node548
    · exact node549
    · exact node550
    · exact node551
    · exact node552
    · exact node553
    · exact node554
    · exact node555
    · exact node556
    · exact node557
    · exact node558
    · exact node559
    · exact node560
    · exact node561
    · exact node562
    · exact node563
    · exact node564
    · exact node565
    · exact node566
    · exact node567
    · exact node568
    · exact node569
    · exact node570
    · exact node571
    · exact node572
    · exact node573
    · exact node574
  · decide +kernel

private def st576 : List Sig := [wire49,raw5,raw4,raw0,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node576 : search 9 0 st576 = false := by decide +kernel

private def st577 : List Sig := [wire220,raw2,raw5,raw6,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node577 : search 8 0 st577 = false := by decide +kernel

private def st578 : List Sig := [wire221,raw5,raw6,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node578 : search 8 0 st578 = false := by decide +kernel

private def st579 : List Sig := [wire221,wire50,raw5,raw6,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node579 : search 8 0 st579 = false := by decide +kernel

private def st580 : List Sig := [wire221,raw2,raw5,raw6,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node580 : search 8 0 st580 = false := by decide +kernel

private def st581 : List Sig := [wire211,raw4,raw5,raw6,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node581 : search 8 0 st581 = false := by decide +kernel

private def st582 : List Sig := [wire222,raw5,raw6,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node582 : search 8 0 st582 = false := by decide +kernel

private def st583 : List Sig := [wire222,wire50,raw5,raw6,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node583 : search 8 0 st583 = false := by decide +kernel

private def st584 : List Sig := [wire222,raw4,raw5,raw6,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node584 : search 8 0 st584 = false := by decide +kernel

private def st585 : List Sig := [wire223,raw7,raw5,raw6,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node585 : search 8 0 st585 = false := by decide +kernel

private def st586 : List Sig := [wire224,raw5,raw6,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node586 : search 8 0 st586 = false := by decide +kernel

private def st587 : List Sig := [wire224,wire50,raw5,raw6,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node587 : search 8 0 st587 = false := by decide +kernel

private def st588 : List Sig := [wire224,raw7,raw5,raw6,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node588 : search 8 0 st588 = false := by decide +kernel

private def st589 : List Sig := [wire48,raw4,wire50,raw6,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node589 : search 8 0 st589 = false := by decide +kernel

private def st590 : List Sig := [wire55,wire50,raw5,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node590 : search 8 0 st590 = false := by decide +kernel

private def st591 : List Sig := [wire55,raw6,wire50,raw5,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node591 : search 8 0 st591 = false := by decide +kernel

private def st592 : List Sig := [wire55,raw7,wire50,raw5,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node592 : search 8 0 st592 = false := by decide +kernel

private def st593 : List Sig := [wire98,raw0,raw5,raw6,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node593 : search 8 0 st593 = false := by decide +kernel

private def st594 : List Sig := [wire225,raw5,raw6,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node594 : search 8 0 st594 = false := by decide +kernel

private def st595 : List Sig := [wire225,raw0,raw5,raw6,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node595 : search 8 0 st595 = false := by decide +kernel

private def st596 : List Sig := [wire225,wire50,raw5,raw6,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node596 : search 8 0 st596 = false := by decide +kernel

private def st597 : List Sig := [wire10,raw0,wire50,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node597 : search 8 0 st597 = false := by decide +kernel

private def st598 : List Sig := [wire12,raw0,wire50,raw5,raw6,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node598 : search 8 0 st598 = false := by decide +kernel

private def st599 : List Sig := [wire226,raw1,raw5,raw6,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node599 : search 8 0 st599 = false := by decide +kernel

private def st600 : List Sig := [wire227,raw5,raw6,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node600 : search 8 0 st600 = false := by decide +kernel

private def st601 : List Sig := [wire227,raw1,raw5,raw6,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node601 : search 8 0 st601 = false := by decide +kernel

private def st602 : List Sig := [wire227,wire50,raw5,raw6,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node602 : search 8 0 st602 = false := by decide +kernel

private def st603 : List Sig := [wire23,raw1,wire50,raw5,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node603 : search 8 0 st603 = false := by decide +kernel

private def st604 : List Sig := [wire25,raw1,wire50,raw5,raw6,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node604 : search 8 0 st604 = false := by decide +kernel

private def st605 : List Sig := [wire228,raw3,raw5,raw6,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node605 : search 8 0 st605 = false := by decide +kernel

private def st606 : List Sig := [wire229,raw5,raw6,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node606 : search 8 0 st606 = false := by decide +kernel

private def st607 : List Sig := [wire229,raw3,raw5,raw6,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node607 : search 8 0 st607 = false := by decide +kernel

private def st608 : List Sig := [wire229,wire50,raw5,raw6,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node608 : search 8 0 st608 = false := by decide +kernel

private def st609 : List Sig := [wire37,raw3,wire50,raw6,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node609 : search 8 0 st609 = false := by decide +kernel

private def st610 : List Sig := [wire50,raw5,raw6,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node610 : search 9 0 st610 = false := by
  apply reject_step 8 0 st610 [] [st577,st578,st579,st580,st581,st582,st583,st584,st585,st586,st587,st588,st589,st590,st591,st592,st593,st594,st595,st596,st597,st598,st599,st600,st601,st602,st603,st604,st605,st606,st607,st608,st609]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node577
    · exact node578
    · exact node579
    · exact node580
    · exact node581
    · exact node582
    · exact node583
    · exact node584
    · exact node585
    · exact node586
    · exact node587
    · exact node588
    · exact node589
    · exact node590
    · exact node591
    · exact node592
    · exact node593
    · exact node594
    · exact node595
    · exact node596
    · exact node597
    · exact node598
    · exact node599
    · exact node600
    · exact node601
    · exact node602
    · exact node603
    · exact node604
    · exact node605
    · exact node606
    · exact node607
    · exact node608
    · exact node609
  · decide +kernel

private def st611 : List Sig := [wire51,raw5,raw6,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node611 : search 9 0 st611 = false := by decide +kernel

private def st612 : List Sig := [wire52,raw5,raw7,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node612 : search 9 0 st612 = false := by decide +kernel

private def st613 : List Sig := [wire53,raw5,raw7,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node613 : search 9 0 st613 = false := by decide +kernel

private def st614 : List Sig := [wire54,raw6,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node614 : search 9 0 st614 = false := by decide +kernel

private def st615 : List Sig := [wire230,raw0,raw6,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node615 : search 8 0 st615 = false := by decide +kernel

private def st616 : List Sig := [wire230,raw0,wire55,raw6,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node616 : search 8 0 st616 = false := by decide +kernel

private def st617 : List Sig := [wire231,raw0,wire55,raw6,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node617 : search 8 0 st617 = false := by decide +kernel

private def st618 : List Sig := [wire10,raw0,raw6,wire55,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node618 : search 8 0 st618 = false := by decide +kernel

private def st619 : List Sig := [wire11,raw0,wire55,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node619 : search 8 0 st619 = false := by decide +kernel

private def st620 : List Sig := [wire11,raw0,raw6,wire55,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node620 : search 8 0 st620 = false := by decide +kernel

private def st621 : List Sig := [wire0,raw0,raw1,wire55,raw6,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node621 : search 8 0 st621 = false := by decide +kernel

private def st622 : List Sig := [wire1,raw0,raw1,wire55,raw6,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node622 : search 8 0 st622 = false := by decide +kernel

private def st623 : List Sig := [wire2,raw0,raw2,wire55,raw6,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node623 : search 8 0 st623 = false := by decide +kernel

private def st624 : List Sig := [wire3,raw0,raw2,wire55,raw6,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node624 : search 8 0 st624 = false := by decide +kernel

private def st625 : List Sig := [wire4,raw0,raw3,wire55,raw6,raw1,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node625 : search 8 0 st625 = false := by decide +kernel

private def st626 : List Sig := [wire5,raw0,raw3,wire55,raw6,raw1,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node626 : search 8 0 st626 = false := by decide +kernel

private def st627 : List Sig := [wire6,raw0,raw4,wire55,raw6,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node627 : search 8 0 st627 = false := by decide +kernel

private def st628 : List Sig := [wire7,raw0,raw4,wire55,raw6,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node628 : search 8 0 st628 = false := by decide +kernel

private def st629 : List Sig := [wire8,raw0,raw5,wire55,raw6,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node629 : search 8 0 st629 = false := by decide +kernel

private def st630 : List Sig := [wire9,raw0,raw5,wire55,raw6,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node630 : search 8 0 st630 = false := by decide +kernel

private def st631 : List Sig := [wire232,raw1,wire55,raw6,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node631 : search 8 0 st631 = false := by decide +kernel

private def st632 : List Sig := [wire136,raw1,wire55,raw6,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node632 : search 8 0 st632 = false := by decide +kernel

private def st633 : List Sig := [wire22,raw1,raw6,wire55,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node633 : search 8 0 st633 = false := by decide +kernel

private def st634 : List Sig := [wire23,raw1,raw6,wire55,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node634 : search 8 0 st634 = false := by decide +kernel

private def st635 : List Sig := [wire14,raw1,raw2,wire55,raw6,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node635 : search 8 0 st635 = false := by decide +kernel

private def st636 : List Sig := [wire15,raw1,raw2,wire55,raw6,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node636 : search 8 0 st636 = false := by decide +kernel

private def st637 : List Sig := [wire16,raw1,raw3,wire55,raw6,raw0,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node637 : search 8 0 st637 = false := by decide +kernel

private def st638 : List Sig := [wire17,raw1,raw3,wire55,raw6,raw0,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node638 : search 8 0 st638 = false := by decide +kernel

private def st639 : List Sig := [wire18,raw1,raw4,wire55,raw6,raw0,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node639 : search 8 0 st639 = false := by decide +kernel

private def st640 : List Sig := [wire19,raw1,raw4,wire55,raw6,raw0,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node640 : search 8 0 st640 = false := by decide +kernel

private def st641 : List Sig := [wire20,raw1,raw5,wire55,raw6,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node641 : search 8 0 st641 = false := by decide +kernel

private def st642 : List Sig := [wire21,raw1,raw5,wire55,raw6,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node642 : search 8 0 st642 = false := by decide +kernel

private def st643 : List Sig := [wire233,raw2,wire55,raw6,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node643 : search 8 0 st643 = false := by decide +kernel

private def st644 : List Sig := [wire234,raw2,wire55,raw6,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node644 : search 8 0 st644 = false := by decide +kernel

private def st645 : List Sig := [wire28,raw2,raw6,wire55,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node645 : search 8 0 st645 = false := by decide +kernel

private def st646 : List Sig := [wire29,raw2,raw6,wire55,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node646 : search 8 0 st646 = false := by decide +kernel

private def st647 : List Sig := [wire26,raw2,raw4,wire55,raw6,raw0,raw1,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node647 : search 8 0 st647 = false := by decide +kernel

private def st648 : List Sig := [wire27,raw2,raw4,wire55,raw6,raw0,raw1,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node648 : search 8 0 st648 = false := by decide +kernel

private def st649 : List Sig := [wire235,raw3,wire55,raw6,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node649 : search 8 0 st649 = false := by decide +kernel

private def st650 : List Sig := [wire236,raw3,wire55,raw6,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node650 : search 8 0 st650 = false := by decide +kernel

private def st651 : List Sig := [wire38,raw3,raw6,wire55,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node651 : search 8 0 st651 = false := by decide +kernel

private def st652 : List Sig := [wire39,raw3,raw6,wire55,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node652 : search 8 0 st652 = false := by decide +kernel

private def st653 : List Sig := [wire32,raw3,raw2,wire55,raw6,raw0,raw1,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node653 : search 8 0 st653 = false := by decide +kernel

private def st654 : List Sig := [wire33,raw3,raw2,wire55,raw6,raw0,raw1,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node654 : search 8 0 st654 = false := by decide +kernel

private def st655 : List Sig := [wire34,raw3,raw4,wire55,raw6,raw0,raw1,raw2,raw5]

set_option maxRecDepth 10000 in
private theorem node655 : search 8 0 st655 = false := by decide +kernel

private def st656 : List Sig := [wire35,raw3,raw4,wire55,raw6,raw0,raw1,raw2,raw5]

set_option maxRecDepth 10000 in
private theorem node656 : search 8 0 st656 = false := by decide +kernel

private def st657 : List Sig := [wire36,raw3,raw5,wire55,raw6,raw0,raw1,raw2,raw4]

set_option maxRecDepth 10000 in
private theorem node657 : search 8 0 st657 = false := by decide +kernel

private def st658 : List Sig := [wire37,raw3,raw5,wire55,raw6,raw0,raw1,raw2,raw4]

set_option maxRecDepth 10000 in
private theorem node658 : search 8 0 st658 = false := by decide +kernel

private def st659 : List Sig := [wire237,raw4,wire55,raw6,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node659 : search 8 0 st659 = false := by decide +kernel

private def st660 : List Sig := [wire200,raw4,wire55,raw6,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node660 : search 8 0 st660 = false := by decide +kernel

private def st661 : List Sig := [wire42,raw4,raw6,wire55,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node661 : search 8 0 st661 = false := by decide +kernel

private def st662 : List Sig := [wire43,raw4,wire55,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node662 : search 8 0 st662 = false := by decide +kernel

private def st663 : List Sig := [wire43,raw4,raw6,wire55,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node663 : search 8 0 st663 = false := by decide +kernel

private def st664 : List Sig := [wire238,raw5,wire55,raw6,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node664 : search 8 0 st664 = false := by decide +kernel

private def st665 : List Sig := [wire239,raw5,wire55,raw6,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node665 : search 8 0 st665 = false := by decide +kernel

private def st666 : List Sig := [wire50,raw5,wire55,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node666 : search 8 0 st666 = false := by decide +kernel

private def st667 : List Sig := [wire50,raw5,raw6,wire55,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node667 : search 8 0 st667 = false := by decide +kernel

private def st668 : List Sig := [wire51,raw5,raw6,wire55,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node668 : search 8 0 st668 = false := by decide +kernel

private def st669 : List Sig := [wire46,raw5,raw2,wire55,raw6,raw0,raw1,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node669 : search 8 0 st669 = false := by decide +kernel

private def st670 : List Sig := [wire47,raw5,raw2,wire55,raw6,raw0,raw1,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node670 : search 8 0 st670 = false := by decide +kernel

private def st671 : List Sig := [wire48,raw5,raw4,wire55,raw6,raw0,raw1,raw2,raw3]

set_option maxRecDepth 10000 in
private theorem node671 : search 8 0 st671 = false := by decide +kernel

private def st672 : List Sig := [wire49,raw5,raw4,wire55,raw6,raw0,raw1,raw2,raw3]

set_option maxRecDepth 10000 in
private theorem node672 : search 8 0 st672 = false := by decide +kernel

private def st673 : List Sig := [wire55,raw6,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node673 : search 9 0 st673 = false := by
  apply reject_step 8 0 st673 [] [st615,st616,st617,st618,st619,st620,st621,st622,st623,st624,st625,st626,st627,st628,st629,st630,st631,st296,st632,st633,st634,st635,st636,st637,st638,st639,st640,st641,st642,st643,st644,st645,st646,st647,st648,st649,st650,st651,st652,st653,st654,st655,st656,st657,st658,st659,st660,st661,st662,st663,st664,st665,st666,st667,st668,st669,st670,st671,st672]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node615
    · exact node616
    · exact node617
    · exact node618
    · exact node619
    · exact node620
    · exact node621
    · exact node622
    · exact node623
    · exact node624
    · exact node625
    · exact node626
    · exact node627
    · exact node628
    · exact node629
    · exact node630
    · exact node631
    · exact node296
    · exact node632
    · exact node633
    · exact node634
    · exact node635
    · exact node636
    · exact node637
    · exact node638
    · exact node639
    · exact node640
    · exact node641
    · exact node642
    · exact node643
    · exact node644
    · exact node645
    · exact node646
    · exact node647
    · exact node648
    · exact node649
    · exact node650
    · exact node651
    · exact node652
    · exact node653
    · exact node654
    · exact node655
    · exact node656
    · exact node657
    · exact node658
    · exact node659
    · exact node660
    · exact node661
    · exact node662
    · exact node663
    · exact node664
    · exact node665
    · exact node666
    · exact node667
    · exact node668
    · exact node669
    · exact node670
    · exact node671
    · exact node672
  · decide +kernel

private def st674 : List Sig := [wire55,raw6,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node674 : search 9 0 st674 = false := by decide +kernel

set_option maxRecDepth 10000 in
private theorem node675 : search 10 0 raw = false := by
  apply reject_step 9 0 raw [] [st29,st30,st31,st58,st59,st60,st61,st62,st63,st90,st120,st121,st186,st224,st225,st259,st260,st261,st289,st290,st291,st292,st293,st294,st320,st321,st381,st382,st383,st409,st410,st411,st412,st413,st445,st446,st478,st479,st480,st506,st507,st508,st509,st510,st511,st539,st540,st541,st542,st543,st575,st576,st610,st611,st612,st613,st614,st673,st674]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node29
    · exact node30
    · exact node31
    · exact node58
    · exact node59
    · exact node60
    · exact node61
    · exact node62
    · exact node63
    · exact node90
    · exact node120
    · exact node121
    · exact node186
    · exact node224
    · exact node225
    · exact node259
    · exact node260
    · exact node261
    · exact node289
    · exact node290
    · exact node291
    · exact node292
    · exact node293
    · exact node294
    · exact node320
    · exact node321
    · exact node381
    · exact node382
    · exact node383
    · exact node409
    · exact node410
    · exact node411
    · exact node412
    · exact node413
    · exact node445
    · exact node446
    · exact node478
    · exact node479
    · exact node480
    · exact node506
    · exact node507
    · exact node508
    · exact node509
    · exact node510
    · exact node511
    · exact node539
    · exact node540
    · exact node541
    · exact node542
    · exact node543
    · exact node575
    · exact node576
    · exact node610
    · exact node611
    · exact node612
    · exact node613
    · exact node614
    · exact node673
    · exact node674
  · decide +kernel

private def st676 : List Sig := [wire240,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node676 : search 9 0 st676 = false := by decide +kernel

private def st677 : List Sig := [wire241,raw1,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node677 : search 9 0 st677 = false := by decide +kernel

private def st678 : List Sig := [wire242,raw2,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node678 : search 9 0 st678 = false := by decide +kernel

private def st679 : List Sig := [wire243,raw3,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node679 : search 9 0 st679 = false := by decide +kernel

private def st680 : List Sig := [wire244,raw4,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node680 : search 9 0 st680 = false := by decide +kernel

private def st681 : List Sig := [wire245,raw5,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node681 : search 9 0 st681 = false := by decide +kernel

private def st682 : List Sig := [wire246,raw6,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node682 : search 9 0 st682 = false := by decide +kernel

private def st683 : List Sig := [wire247,raw7,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node683 : search 9 0 st683 = false := by decide +kernel

private def st684 : List Sig := [wire0,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node684 : search 9 1 st684 = false := by decide +kernel

private def st685 : List Sig := [wire1,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node685 : search 9 1 st685 = false := by decide +kernel

private def st686 : List Sig := [wire2,raw0,raw2,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node686 : search 9 1 st686 = false := by decide +kernel

private def st687 : List Sig := [wire3,raw0,raw2,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node687 : search 9 1 st687 = false := by decide +kernel

private def st688 : List Sig := [wire4,raw0,raw3,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node688 : search 9 1 st688 = false := by decide +kernel

private def st689 : List Sig := [wire5,raw0,raw3,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node689 : search 9 1 st689 = false := by decide +kernel

private def st690 : List Sig := [wire6,raw0,raw4,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node690 : search 9 1 st690 = false := by decide +kernel

private def st691 : List Sig := [wire7,raw0,raw4,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node691 : search 9 1 st691 = false := by decide +kernel

private def st692 : List Sig := [wire8,raw0,raw5,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node692 : search 9 1 st692 = false := by decide +kernel

private def st693 : List Sig := [wire9,raw0,raw5,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node693 : search 9 1 st693 = false := by decide +kernel

private def st694 : List Sig := [wire10,raw0,raw6,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node694 : search 9 1 st694 = false := by decide +kernel

private def st695 : List Sig := [wire11,raw0,raw6,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node695 : search 9 1 st695 = false := by decide +kernel

private def st696 : List Sig := [wire12,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node696 : search 9 1 st696 = false := by decide +kernel

private def st697 : List Sig := [wire12,raw0,raw7,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node697 : search 9 1 st697 = false := by decide +kernel

private def st698 : List Sig := [wire13,raw0,raw7,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node698 : search 9 1 st698 = false := by decide +kernel

private def st699 : List Sig := [wire14,raw1,raw2,raw0,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node699 : search 9 1 st699 = false := by decide +kernel

private def st700 : List Sig := [wire15,raw1,raw2,raw0,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node700 : search 9 1 st700 = false := by decide +kernel

private def st701 : List Sig := [wire16,raw1,raw3,raw0,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node701 : search 9 1 st701 = false := by decide +kernel

private def st702 : List Sig := [wire17,raw1,raw3,raw0,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node702 : search 9 1 st702 = false := by decide +kernel

private def st703 : List Sig := [wire18,raw1,raw4,raw0,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node703 : search 9 1 st703 = false := by decide +kernel

private def st704 : List Sig := [wire19,raw1,raw4,raw0,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node704 : search 9 1 st704 = false := by decide +kernel

private def st705 : List Sig := [wire20,raw1,raw5,raw0,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node705 : search 9 1 st705 = false := by decide +kernel

private def st706 : List Sig := [wire21,raw1,raw5,raw0,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node706 : search 9 1 st706 = false := by decide +kernel

private def st707 : List Sig := [wire22,raw1,raw6,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node707 : search 9 1 st707 = false := by decide +kernel

private def st708 : List Sig := [wire23,raw1,raw6,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node708 : search 9 1 st708 = false := by decide +kernel

private def st709 : List Sig := [wire24,raw1,raw7,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node709 : search 9 1 st709 = false := by decide +kernel

private def st710 : List Sig := [wire25,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node710 : search 9 1 st710 = false := by decide +kernel

private def st711 : List Sig := [wire25,raw1,raw7,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node711 : search 9 1 st711 = false := by decide +kernel

private def st712 : List Sig := [wire26,raw2,raw4,raw0,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node712 : search 9 1 st712 = false := by decide +kernel

private def st713 : List Sig := [wire27,raw2,raw4,raw0,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node713 : search 9 1 st713 = false := by decide +kernel

private def st714 : List Sig := [wire28,raw2,raw6,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node714 : search 9 1 st714 = false := by decide +kernel

private def st715 : List Sig := [wire29,raw2,raw6,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node715 : search 9 1 st715 = false := by decide +kernel

private def st716 : List Sig := [wire30,raw2,raw7,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node716 : search 9 1 st716 = false := by decide +kernel

private def st717 : List Sig := [wire31,raw2,raw7,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node717 : search 9 1 st717 = false := by decide +kernel

private def st718 : List Sig := [wire32,raw3,raw2,raw0,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node718 : search 9 1 st718 = false := by decide +kernel

private def st719 : List Sig := [wire33,raw3,raw2,raw0,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node719 : search 9 1 st719 = false := by decide +kernel

private def st720 : List Sig := [wire34,raw3,raw4,raw0,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node720 : search 9 1 st720 = false := by decide +kernel

private def st721 : List Sig := [wire35,raw3,raw4,raw0,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node721 : search 9 1 st721 = false := by decide +kernel

private def st722 : List Sig := [wire36,raw3,raw5,raw0,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node722 : search 9 1 st722 = false := by decide +kernel

private def st723 : List Sig := [wire37,raw3,raw5,raw0,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node723 : search 9 1 st723 = false := by decide +kernel

private def st724 : List Sig := [wire38,raw3,raw6,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node724 : search 9 1 st724 = false := by decide +kernel

private def st725 : List Sig := [wire39,raw3,raw6,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node725 : search 9 1 st725 = false := by decide +kernel

private def st726 : List Sig := [wire40,raw3,raw7,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node726 : search 9 1 st726 = false := by decide +kernel

private def st727 : List Sig := [wire41,raw3,raw7,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node727 : search 9 1 st727 = false := by decide +kernel

private def st728 : List Sig := [wire42,raw4,raw6,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node728 : search 9 1 st728 = false := by decide +kernel

private def st729 : List Sig := [wire43,raw4,raw6,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node729 : search 9 1 st729 = false := by decide +kernel

private def st730 : List Sig := [wire44,raw4,raw7,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node730 : search 9 1 st730 = false := by decide +kernel

private def st731 : List Sig := [wire45,raw4,raw7,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node731 : search 9 1 st731 = false := by decide +kernel

private def st732 : List Sig := [wire46,raw5,raw2,raw0,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node732 : search 9 1 st732 = false := by decide +kernel

private def st733 : List Sig := [wire47,raw5,raw2,raw0,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node733 : search 9 1 st733 = false := by decide +kernel

private def st734 : List Sig := [wire48,raw5,raw4,raw0,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node734 : search 9 1 st734 = false := by decide +kernel

private def st735 : List Sig := [wire49,raw5,raw4,raw0,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node735 : search 9 1 st735 = false := by decide +kernel

private def st736 : List Sig := [wire50,raw5,raw6,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node736 : search 9 1 st736 = false := by decide +kernel

private def st737 : List Sig := [wire51,raw5,raw6,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node737 : search 9 1 st737 = false := by decide +kernel

private def st738 : List Sig := [wire52,raw5,raw7,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node738 : search 9 1 st738 = false := by decide +kernel

private def st739 : List Sig := [wire53,raw5,raw7,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node739 : search 9 1 st739 = false := by decide +kernel

private def st740 : List Sig := [wire54,raw6,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node740 : search 9 1 st740 = false := by decide +kernel

private def st741 : List Sig := [wire55,raw6,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node741 : search 9 1 st741 = false := by decide +kernel

private def st742 : List Sig := [wire55,raw6,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node742 : search 9 1 st742 = false := by decide +kernel

set_option maxRecDepth 10000 in
private theorem node743 : search 10 1 raw = false := by
  apply reject_step 9 1 raw [st676,st677,st678,st679,st680,st681,st682,st683] [st684,st685,st686,st687,st688,st689,st690,st691,st692,st693,st694,st695,st696,st697,st698,st699,st700,st701,st702,st703,st704,st705,st706,st707,st708,st709,st710,st711,st712,st713,st714,st715,st716,st717,st718,st719,st720,st721,st722,st723,st724,st725,st726,st727,st728,st729,st730,st731,st732,st733,st734,st735,st736,st737,st738,st739,st740,st741,st742]
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node676
    · exact node677
    · exact node678
    · exact node679
    · exact node680
    · exact node681
    · exact node682
    · exact node683
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node684
    · exact node685
    · exact node686
    · exact node687
    · exact node688
    · exact node689
    · exact node690
    · exact node691
    · exact node692
    · exact node693
    · exact node694
    · exact node695
    · exact node696
    · exact node697
    · exact node698
    · exact node699
    · exact node700
    · exact node701
    · exact node702
    · exact node703
    · exact node704
    · exact node705
    · exact node706
    · exact node707
    · exact node708
    · exact node709
    · exact node710
    · exact node711
    · exact node712
    · exact node713
    · exact node714
    · exact node715
    · exact node716
    · exact node717
    · exact node718
    · exact node719
    · exact node720
    · exact node721
    · exact node722
    · exact node723
    · exact node724
    · exact node725
    · exact node726
    · exact node727
    · exact node728
    · exact node729
    · exact node730
    · exact node731
    · exact node732
    · exact node733
    · exact node734
    · exact node735
    · exact node736
    · exact node737
    · exact node738
    · exact node739
    · exact node740
    · exact node741
    · exact node742
  · decide +kernel

private def st744 : List Sig := [wire240,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node744 : search 9 1 st744 = false := by decide +kernel

private def st745 : List Sig := [wire240,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node745 : search 9 1 st745 = false := by decide +kernel

private def st746 : List Sig := [wire241,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node746 : search 9 1 st746 = false := by decide +kernel

private def st747 : List Sig := [wire241,raw1,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node747 : search 9 1 st747 = false := by decide +kernel

private def st748 : List Sig := [wire242,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node748 : search 9 1 st748 = false := by decide +kernel

private def st749 : List Sig := [wire242,raw2,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node749 : search 9 1 st749 = false := by decide +kernel

private def st750 : List Sig := [wire243,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node750 : search 9 1 st750 = false := by decide +kernel

private def st751 : List Sig := [wire243,raw3,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node751 : search 9 1 st751 = false := by decide +kernel

private def st752 : List Sig := [wire244,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node752 : search 9 1 st752 = false := by decide +kernel

private def st753 : List Sig := [wire244,raw4,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node753 : search 9 1 st753 = false := by decide +kernel

private def st754 : List Sig := [wire245,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node754 : search 9 1 st754 = false := by decide +kernel

private def st755 : List Sig := [wire245,raw5,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node755 : search 9 1 st755 = false := by decide +kernel

private def st756 : List Sig := [wire246,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node756 : search 9 1 st756 = false := by decide +kernel

private def st757 : List Sig := [wire246,raw6,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node757 : search 9 1 st757 = false := by decide +kernel

private def st758 : List Sig := [wire247,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node758 : search 9 1 st758 = false := by decide +kernel

private def st759 : List Sig := [wire247,raw7,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node759 : search 9 1 st759 = false := by decide +kernel

private def st760 : List Sig := [wire12,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node760 : search 9 2 st760 = false := by decide +kernel

private def st761 : List Sig := [wire25,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node761 : search 9 2 st761 = false := by decide +kernel

private def st762 : List Sig := [wire55,raw6,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node762 : search 9 2 st762 = false := by decide +kernel

set_option maxRecDepth 10000 in
private theorem node763 : search 10 2 raw = false := by
  apply reject_step 9 2 raw [st744,st745,st746,st747,st748,st749,st750,st751,st752,st753,st754,st755,st756,st757,st758,st759] [st760,st761,st762]
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node744
    · exact node745
    · exact node746
    · exact node747
    · exact node748
    · exact node749
    · exact node750
    · exact node751
    · exact node752
    · exact node753
    · exact node754
    · exact node755
    · exact node756
    · exact node757
    · exact node758
    · exact node759
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact node760
    · exact node761
    · exact node762
  · decide +kernel

set_option maxRecDepth 10000 in
private theorem node764 : search 10 3 raw = false := by decide +kernel

private lemma excluded0 : search 10 0 raw = false := node675

private lemma excluded1 : search 10 1 raw = false := node743

private lemma excluded2 : search 10 2 raw = false := node763

private lemma excluded3 : search 10 3 raw = false := node764

end PEqualNP.Outside.G524

open PEqualNP.Outside.G524

theorem PEqualNP.Outside.L_meta_524 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 0 && x 6) || (x 0 && x 7)) s → 11 ≤ s := by
  intro s hs
  by_contra h
  obtain ⟨C,hg,hc,he⟩ := hs
  obtain ⟨t,ht,found⟩ := circuit_search C (by omega) hg he
  interval_cases t <;> simp_all only [excluded0,excluded1,excluded2,excluded3,Bool.false_eq_true]
