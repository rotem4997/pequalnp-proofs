import Mathlib
import PEqualNP.Defs
-- The live-wire checker is adapted from ljste's PR 2918 and jfsantoropereira's L-meta-1007.
-- The search, samples, and eight-gate witness are adapted from Vkuparin's L-meta-1419 (PR #2922), Apache-2.0.
namespace PEqualNP.Outside.L_meta_8634_aux

abbrev B := BitVec 32
abbrev Sig := B × B
def top : B := BitVec.allOnes 32
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

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



-- Each bit position pairs a positive and a negative input row.
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
def Live : Nat → Nat → Finset Sig → Prop
  | 0, t, S => t = 0 ∧ S = {target}
  | k+1, t, S =>
    (∃ u U a, t = u+1 ∧ S = insert a U ∧ proper a ∧ neg a ∉ insert a U ∧ Live k u (insert (neg a) U)) ∨
    (∃ U a b d, S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live k t (insert (bin d a b) U))

lemma Live.stop : Live 0 0 {target} := ⟨rfl,rfl⟩

lemma Live.unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U) := Or.inl ⟨_,_,_,rfl,rfl,ha,hfresh,tail⟩

lemma Live.binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U)) := Or.inr ⟨_,_,_,_,rfl,ha,hb,hab,hfresh,tail⟩

lemma liveInd {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P k t (insert (neg a) U) tail → P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P k t (insert (bin d a b) U) tail → P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

lemma liveCases {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail
    · exact binary ha hb hab hf tail

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h using liveInd with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using liveInd with
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
  by_cases hi : i < 32
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 32 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 32
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 32 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 32)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 32) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 32 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 32)] <;> simp [hi]
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

def isNot (op : GateOp) : Bool := match op with | .not => true | _ => false

lemma isNot_iff (op : GateOp) : isNot op = true ↔ op = .not := by cases op <;> simp [isNot]

def witness (allow : Bool) (w : List Sig) (z : Sig) : Prop :=
  (allow = true ∧ ∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness false w (bin d a b) := by
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
    represented w (gv w g) ∨ witness (isNot g.op) w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness true w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨rfl,a,hm,hp,rfl⟩)
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
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,isNot,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {flag : Bool} {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness flag w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ t' ≤ t+flag.toNat ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨flagOn,a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
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
        exact ⟨_,_,_,Nat.le_refl _,by simp [flagOn],Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
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
        exact ⟨_,_,_,Nat.le_refl _,by omega,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ t ≤ gs.countP (fun g => isNot g.op) ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,hcount,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hcnt,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,hu,hT⟩
    cases hf : isNot g.op <;> simp [List.countP_cons,hf] at hcnt ⊢ <;> omega

def bit (side : Bool) (i : Fin 32) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 32).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
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


def evalT (T : ℕ) (x : Fin 5 → Bool) := Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)
def sample (raw : List Sig) (s : Bool) (i : Fin 32) (j : Fin 5) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 5 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (T : ℕ) (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, evalT T (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = evalT T x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample raw s i)
    rw [sample_list raw raw_id,sample_ok] at eq
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

private lemma necessary (raw : List Sig) (every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true) {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
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

def special : List Sig := []
def gateAvailable (v : List Sig) (g : Sig) : Bool :=
  !(v.contains g) && g != zero && g != one

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    base == top && gateAvailable v g && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && gateAvailable v g && r (g::(h++rest)))

def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  !(special.contains a) &&
    tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let c := coverage (decide (0<t)) v
  v.any (unaryAt k t r v c)

def allowedKeeps (a b : Sig) : List (List Sig) :=
  [[],[a],[b],[a,b]].filter (fun w => w.all fun x => !(special.contains x))

def fastBinary (r : List Sig → Bool) (v : List Sig) (a b : Sig) (ua ub : B) : Bool :=
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => gateAvailable v g && r (g::rest)
  ((ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 &&
    !(special.contains a) && !(special.contains b) && use (bin false a b)) ||
    ((ua &&& b.2) == 0 && (ub &&& a.2) == 0 && use (bin true a b))

def slowBinary (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  ((!(special.contains a) && !(special.contains b)) &&
    tryGate k t r v rest (v.length-2) mask (bin false a b) [[],[a],[b],[a,b]]) ||
    tryGate k t r v rest (v.length-2) mask (bin true a b) (allowedKeeps a b)

def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t

lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let d := decide (0<t)
  let c := coverage d v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a, c.2.1 &&& sep false a))
    scanPairs (fun a b => fastBinary r v a.1 b.1 a.2 b.2) acts
  else scanPairs (slowBinary k t r v c) v

def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
    v == [target] || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v == [target]
  | k+1,t,v => stepTest k t v (search k (t-1)) (search k t)

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
    simp [tryGate,tight,ok,gateAvailable,ha,hp.1,hp.2,hr] at *
  · have hav : gateAvailable v g = true := by simp [gateAvailable, ha, hp.1, hp.2]
    simp only [tryGate, ite_eq_right tight, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, hav, and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩

private lemma unique_needed (c : Cov) (a b : Sig) (op : Bool)
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

private lemma fast_ok {k r v c a b}
    (hlen : v.length-2=k) (h : slowBinary k 0 r v c a b = true) :
    fastBinary r v a b (c.2.1 &&& sep false a) (c.2.1 &&& sep false b) = true := by
  simp only [slowBinary,tryGate,Nat.sub_zero,hlen,ite_true,decide_false,Bool.or_eq_true,
    Bool.and_eq_true,beq_iff_eq] at h
  simp only [fastBinary, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hc,hav⟩,hr⟩ | ⟨⟨hc,hav⟩,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b false hc)
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b true hc)
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (ha : a ∉ special) (l : Live m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → r v = true) :
    unaryMoves k t r v = true := by
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
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simp [ha], gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

private lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    slowBinary k t r v (coverage (decide (0<t)) v) a b = true := by
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
  have allow : h ∈ allowedKeeps a b := by
    apply List.mem_filter.mpr
    refine ⟨opts,List.all_eq_true.mpr (fun x hx => ?_)⟩
    have hm : x ∈ U := (List.mem_filter.mp hx).2 |> of_decide_eq_true
    rcases List.mem_cons.mp (List.mem_filter.mp hx).1 with rfl | hx
    · simpa using fun ha : x ∈ special => (hra ha).2 hm
    · obtain rfl := List.mem_singleton.mp hx
      simpa using fun hb : x ∈ special => (hrb hb).2 hm
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  unfold slowBinary
  dsimp only
  rw [hlen,hmask]
  cases d with
  | false =>
    have na : a ∉ special := fun ha => Bool.false_ne_true (hra ha).1
    have nb : b ∉ special := fun hb => Bool.false_ne_true (hrb hb).1
    apply Bool.or_eq_true_iff.mpr
    left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh hra hrb l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Live m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
  have h2 := slow_found hv e' hle hab.symm hf hrb hra ht (by simpa only [bin_comm d b a] using ih)
  unfold binaryMoves
  split
  · rename_i cut
    simp only [Bool.and_eq_true, beq_iff_eq] at cut
    obtain ⟨rfl,hvlen⟩ := cut
    have hlen : v.length - 2 = k := by omega
    let f := fun x => (x, (coverage false v).2.1 &&& sep false x)
    have na : f a ∈ v.map f := List.mem_map_of_mem ah
    have nb : f b ∈ v.map f := List.mem_map_of_mem bh
    exact scanPairs_complete _ na nb (fun e => hab (congrArg Prod.fst e))
      (fast_ok hlen h1) (fast_ok hlen h2)
  · exact scanPairs_complete _ ah bh hab h1 h2

private lemma reduced_step {m t S : Nat} {s : Finset Sig} {v : List Sig} {u b : List Sig → Bool}
    (h : Live m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset = s)
    (hu : ∀ w, w.Nodup → ∀ l ≤ S, Live l (t-1) w.toFinset → u w = true)
    (hb' : ∀ w, w.Nodup → ∀ l ≤ S, Live l t w.toFinset → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h
  rw [← he, List.toFinset_card_of_nodup hv] at size
  rw [stepTest, if_neg (by omega)]
  induction h using liveCases with
  | stop =>
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    have eq := List.perm_singleton.mp p
    simp [eq]
  | @unary m t U a ha hf tail =>
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp, unary_found hv he (by omega) hf (by simp [special]) tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf (by simp [special]) (by simp [special]) tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

lemma search_complete {m t : Nat} {S : Finset Sig} (h : Live m t S) (k : Nat) (hk : m ≤ k)
    (v : List Sig) (hv : v.Nodup) (hs : v.toFinset = S) : search k t v = true := by
  induction k generalizing m t S v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    obtain ⟨rfl,rfl⟩ := h
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    simp [search, List.perm_singleton.mp p]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hv hs <;>
      exact fun w hn l hl hh => ih hh hl w hn rfl


-- Five essential raw signals require at least four binary gates in the live circuit.
-- With a seven-gate budget, it suffices to search zero through three live NOT gates.

def Excluded (k t : Nat) (v : List Sig) : Prop :=
  v.Nodup → ∀ m ≤ k, ¬ Live m t v.toFinset

def ExcludedList (k t : Nat) : List (List Sig) → Prop
  | [] => True
  | v :: vs => Excluded k t v ∧ ExcludedList k t vs

lemma excluded_mem {k t w} {vs : List (List Sig)} (h : ExcludedList k t vs)
    (mem : w∈vs) : Excluded k t w := by
  induction vs with
  | nil => simp at mem
  | cons v vs ih =>
    rcases List.mem_cons.mp mem with rfl|tail
    · exact h.1
    · exact ih h.2 tail

lemma leafExcluded {k t v} (test : search k t v=false) : Excluded k t v := by
  intro nd m hm live
  have found := search_complete live k hm v nd rfl
  rw [test] at found
  contradiction

lemma cutExcluded {k t v} (us bs : List (List Sig))
    (hu : ExcludedList k (t-1) us) (hb : ExcludedList k t bs)
    (test : stepTest k t v (fun w => decide (w∉us)) (fun w => decide (w∉bs))=false) :
    Excluded (k+1) t v := by
  intro nd m hm live
  have pos := reduced_step live hm nd rfl
    (u:=fun w => decide (w∉us)) (b:=fun w => decide (w∉bs))
    (fun w hw l hl h => decide_eq_true (fun mem => excluded_mem hu mem hw l hl h))
    (fun w hw l hl h => decide_eq_true (fun mem => excluded_mem hb mem hw l hl h))
  rw [test] at pos
  contradiction

theorem cost (T : ℕ) (raw : List Sig) (s : ℕ)
    (raw_id : List.ofFn (fun j : Fin 5 => raw.getD j.val zero) = raw)
    (samples : ∀ b i, evalT T (sample raw b i) = b)
    (nd : raw.Nodup) (len : raw.length = 5)
    (essential : raw.all (fun a => unionSep true (raw.erase a) != top) = true)
    (test : ∀ t : Fin (s-3), Excluded s t.val raw)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (correct : ∀ x, C.eval (List.ofFn x) = evalT T x) : s < C.gates.length := by
  by_contra! small
  obtain ⟨k,t,S,hk,count,live,sub⟩ := extract C.gates raw legal (circuit_target T raw raw_id samples C legal correct)
  have eq := necessary raw essential live sub
  have size := live_size live
  rw [←eq,List.toFinset_card_of_nodup nd,len] at size
  exact test ⟨t,by omega⟩ nd k (by omega) (eq.symm ▸ live)


open PEqualNP.CircuitLowerBounds

-- Bit j of each coordinate evaluates that input on row j of the following positive/negative pairs.
-- (7,3), (7,5), (7,6), (11,3), (11,9), (11,10), (13,5), (13,9), (13,12), (15,14), (19,3), (19,17), (19,18), (23,21), (23,22), (27,25), (27,26), (29,21), (29,25), (29,28), (30,14), (30,22), (30,26), (30,28), (7,14), (7,21), (7,22), (7,25), (7,26), (7,28), (11,14), (11,21)
def raw4 : List Sig := [(0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

-- The following checked frontiers split the first two gate choices. Each leaf is evaluated by the kernel.
def wires0 : List Sig := [(0xff01fe3f, 0x00000409), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

def wires1 : List Sig := [(0x3f006207, 0x00000000), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires1 : Excluded 5 0 wires1 := leafExcluded (by decide +kernel)

def wires2 : List Sig := [(0xffffffff, 0xe7ba674f), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires2 : Excluded 5 0 wires2 := leafExcluded (by decide +kernel)

def wires3 : List Sig := [(0xc0018238, 0x00000000), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires3 : Excluded 5 0 wires3 := leafExcluded (by decide +kernel)

def wires4 : List Sig := [(0xffffffff, 0x79dd87b9), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires4 : Excluded 5 0 wires4 := leafExcluded (by decide +kernel)

def wires5 : List Sig := [(0x0001fc00, 0x00000000), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires5 : Excluded 5 0 wires5 := leafExcluded (by decide +kernel)

def wires6 : List Sig := [(0xfffffe3f, 0xbeeffc09), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires6 : Excluded 5 0 wires6 := leafExcluded (by decide +kernel)

def wires7 : List Sig := [(0xffffffff, 0xdf77feff), (0xff01fe3f, 0x00000409), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires7 : Excluded 5 0 wires7 := leafExcluded (by decide +kernel)

def wires8 : List Sig := [(0xffffffff, 0xdf77feff), (0xff0fffff, 0x8a06acdb), (0xff01fe3f, 0x00000409), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires8 : Excluded 5 0 wires8 := leafExcluded (by decide +kernel)

def wires9 : List Sig := [(0xffffffff, 0xdf77feff), (0xfff1fe3f, 0x5571562d), (0xff01fe3f, 0x00000409), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires9 : Excluded 5 0 wires9 := leafExcluded (by decide +kernel)

def wires10 : List Sig := [(0x3f0e63c7, 0x82022042), (0x3ffe63c7, 0xe7ba6346), (0xff01fe3f, 0x00000409), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires10 : Excluded 5 0 wires10 := leafExcluded (by decide +kernel)

def wires11 : List Sig := [(0xc00f83f8, 0x08048090), (0xc0ff83f8, 0x79dd83b0), (0xff01fe3f, 0x00000409), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires11 : Excluded 5 0 wires11 := leafExcluded (by decide +kernel)

def wires12 : List Sig := [(0x3ff06207, 0x45304204), (0x3ffe63c7, 0xe7ba6346), (0xff01fe3f, 0x00000409), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires12 : Excluded 5 0 wires12 := leafExcluded (by decide +kernel)

def wires13 : List Sig := [(0xc0f18238, 0x51510220), (0xc0ff83f8, 0x79dd83b0), (0xff01fe3f, 0x00000409), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires13 : Excluded 5 0 wires13 := leafExcluded (by decide +kernel)

def wires14 : List Sig := [(0x00f1fc00, 0x14615000), (0xff01fe3f, 0x00000409), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires14 : Excluded 5 0 wires14 := leafExcluded (by decide +kernel)

def wires15 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff01fe3f, 0x00000409), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires15 : Excluded 5 0 wires15 := leafExcluded (by decide +kernel)

def wires16 : List Sig := [(0x00f1fc00, 0x14615000), (0x00fffc00, 0xbeeff800), (0xff01fe3f, 0x00000409), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires16 : Excluded 5 0 wires16 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires0 : Excluded 6 0 wires0 :=
  cutExcluded (k:=5) (t:=0) (v:=wires0) [] [wires1, wires2, wires3, wires4, wires5, wires6, wires7, wires8, wires9, wires10, wires11, wires12, wires13, wires14, wires15, wires16]
    True.intro
    ⟨exclude5_0_wires1, exclude5_0_wires2, exclude5_0_wires3, exclude5_0_wires4, exclude5_0_wires5, exclude5_0_wires6, exclude5_0_wires7, exclude5_0_wires8, exclude5_0_wires9, exclude5_0_wires10, exclude5_0_wires11, exclude5_0_wires12, exclude5_0_wires13, exclude5_0_wires14, exclude5_0_wires15, exclude5_0_wires16, True.intro⟩
    (by decide +kernel)

def wires17 : List Sig := [(0xffffffff, 0xdf77feff), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

def wires18 : List Sig := [(0x3ffe63c7, 0xc7326246), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires18 : Excluded 5 0 wires18 := leafExcluded (by decide +kernel)

def wires19 : List Sig := [(0x3ffe63c7, 0xc7326246), (0xffffffff, 0xdf77feff), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires19 : Excluded 5 0 wires19 := leafExcluded (by decide +kernel)

def wires20 : List Sig := [(0x3ffe63c7, 0xc7326246), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires20 : Excluded 5 0 wires20 := leafExcluded (by decide +kernel)

def wires21 : List Sig := [(0xc0ff83f8, 0x595582b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires21 : Excluded 5 0 wires21 := leafExcluded (by decide +kernel)

def wires22 : List Sig := [(0xc0ff83f8, 0x595582b0), (0xffffffff, 0xdf77feff), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires22 : Excluded 5 0 wires22 := leafExcluded (by decide +kernel)

def wires23 : List Sig := [(0xc0ff83f8, 0x595582b0), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires23 : Excluded 5 0 wires23 := leafExcluded (by decide +kernel)

def wires24 : List Sig := [(0x00fffc00, 0x9e67f800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires24 : Excluded 5 0 wires24 := leafExcluded (by decide +kernel)

def wires25 : List Sig := [(0x00fffc00, 0x9e67f800), (0xffffffff, 0xdf77feff), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires25 : Excluded 5 0 wires25 := leafExcluded (by decide +kernel)

def wires26 : List Sig := [(0x00fffc00, 0x9e67f800), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires26 : Excluded 5 0 wires26 := leafExcluded (by decide +kernel)

def wires27 : List Sig := [(0xffffffff, 0xfffffeff), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires27 : Excluded 5 0 wires27 := leafExcluded (by decide +kernel)

def wires28 : List Sig := [(0xff01fe3f, 0x00000409), (0xffffffff, 0xdf77feff), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires28 : Excluded 5 0 wires28 := leafExcluded (by decide +kernel)

def wires29 : List Sig := [(0xff01fe3f, 0x00000409), (0xff0fffff, 0x8a06acdb), (0xffffffff, 0xdf77feff), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires29 : Excluded 5 0 wires29 := leafExcluded (by decide +kernel)

def wires30 : List Sig := [(0xff01fe3f, 0x00000409), (0xfff1fe3f, 0x5571562d), (0xffffffff, 0xdf77feff), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires30 : Excluded 5 0 wires30 := leafExcluded (by decide +kernel)

def wires31 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xffffffff, 0xdf77feff), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires31 : Excluded 5 0 wires31 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires17 : Excluded 6 0 wires17 :=
  cutExcluded (k:=5) (t:=0) (v:=wires17) [] [wires18, wires19, wires20, wires21, wires22, wires23, wires24, wires25, wires26, wires27, wires28, wires29, wires30, wires31]
    True.intro
    ⟨exclude5_0_wires18, exclude5_0_wires19, exclude5_0_wires20, exclude5_0_wires21, exclude5_0_wires22, exclude5_0_wires23, exclude5_0_wires24, exclude5_0_wires25, exclude5_0_wires26, exclude5_0_wires27, exclude5_0_wires28, exclude5_0_wires29, exclude5_0_wires30, exclude5_0_wires31, True.intro⟩
    (by decide +kernel)

def wires32 : List Sig := [(0x3f0e63c7, 0x82022042), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

def wires33 : List Sig := [(0x3f006207, 0x00000000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires33 : Excluded 5 0 wires33 := leafExcluded (by decide +kernel)

def wires34 : List Sig := [(0xffffffff, 0xd773766f), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires34 : Excluded 5 0 wires34 := leafExcluded (by decide +kernel)

def wires35 : List Sig := [(0x000e03c0, 0x00000000), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires35 : Excluded 5 0 wires35 := leafExcluded (by decide +kernel)

def wires36 : List Sig := [(0xffffe3ff, 0xfbdfa3f2), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires36 : Excluded 5 0 wires36 := leafExcluded (by decide +kernel)

def wires37 : List Sig := [(0x000e6000, 0x82022000), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires37 : Excluded 5 0 wires37 := leafExcluded (by decide +kernel)

def wires38 : List Sig := [(0x3fffffc7, 0xbeeff842), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires38 : Excluded 5 0 wires38 := leafExcluded (by decide +kernel)

def wires39 : List Sig := [(0x3fffffc7, 0xbeeff842), (0x3f0e63c7, 0x82022042), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires39 : Excluded 5 0 wires39 := leafExcluded (by decide +kernel)

def wires40 : List Sig := [(0x3fffffc7, 0xbeeff842), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires40 : Excluded 5 0 wires40 := leafExcluded (by decide +kernel)

def wires41 : List Sig := [(0xffffffff, 0xefbeefdf), (0xff0fffff, 0x8a06acdb), (0x3f0e63c7, 0x82022042), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires41 : Excluded 5 0 wires41 := leafExcluded (by decide +kernel)

def wires42 : List Sig := [(0xff01fe3f, 0x00000409), (0xfff1fe3f, 0x5571562d), (0x3f0e63c7, 0x82022042), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires42 : Excluded 5 0 wires42 := leafExcluded (by decide +kernel)

def wires43 : List Sig := [(0x3ff06207, 0x45304204), (0xfff1fe3f, 0x5571562d), (0x3f0e63c7, 0x82022042), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires43 : Excluded 5 0 wires43 := leafExcluded (by decide +kernel)

def wires44 : List Sig := [(0x00fe03c0, 0x61980300), (0xc0ff83f8, 0x79dd83b0), (0x3f0e63c7, 0x82022042), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires44 : Excluded 5 0 wires44 := leafExcluded (by decide +kernel)

def wires45 : List Sig := [(0x00fe6000, 0xa6aa6000), (0x00fffc00, 0xbeeff800), (0x3f0e63c7, 0x82022042), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires45 : Excluded 5 0 wires45 := leafExcluded (by decide +kernel)

def wires46 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x3f0e63c7, 0x82022042), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires46 : Excluded 5 0 wires46 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires32 : Excluded 6 0 wires32 :=
  cutExcluded (k:=5) (t:=0) (v:=wires32) [] [wires33, wires34, wires35, wires36, wires37, wires38, wires39, wires40, wires41, wires42, wires43, wires44, wires45, wires46]
    True.intro
    ⟨exclude5_0_wires33, exclude5_0_wires34, exclude5_0_wires35, exclude5_0_wires36, exclude5_0_wires37, exclude5_0_wires38, exclude5_0_wires39, exclude5_0_wires40, exclude5_0_wires41, exclude5_0_wires42, exclude5_0_wires43, exclude5_0_wires44, exclude5_0_wires45, exclude5_0_wires46, True.intro⟩
    (by decide +kernel)

def wires47 : List Sig := [(0xffffffff, 0xefbeefdf), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

def wires48 : List Sig := [(0xfff1fe3f, 0x4530460d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires48 : Excluded 5 0 wires48 := leafExcluded (by decide +kernel)

def wires49 : List Sig := [(0xfff1fe3f, 0x4530460d), (0xffffffff, 0xefbeefdf), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires49 : Excluded 5 0 wires49 := leafExcluded (by decide +kernel)

def wires50 : List Sig := [(0xfff1fe3f, 0x4530460d), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires50 : Excluded 5 0 wires50 := leafExcluded (by decide +kernel)

def wires51 : List Sig := [(0xc0ff83f8, 0x699c8390), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires51 : Excluded 5 0 wires51 := leafExcluded (by decide +kernel)

def wires52 : List Sig := [(0xc0ff83f8, 0x699c8390), (0xffffffff, 0xefbeefdf), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires52 : Excluded 5 0 wires52 := leafExcluded (by decide +kernel)

def wires53 : List Sig := [(0xc0ff83f8, 0x699c8390), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires53 : Excluded 5 0 wires53 := leafExcluded (by decide +kernel)

def wires54 : List Sig := [(0xffffffff, 0xffffefff), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires54 : Excluded 5 0 wires54 := leafExcluded (by decide +kernel)

def wires55 : List Sig := [(0x00fffc00, 0xaeaee800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires55 : Excluded 5 0 wires55 := leafExcluded (by decide +kernel)

def wires56 : List Sig := [(0x00fffc00, 0xaeaee800), (0xffffffff, 0xefbeefdf), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires56 : Excluded 5 0 wires56 := leafExcluded (by decide +kernel)

def wires57 : List Sig := [(0x00fffc00, 0xaeaee800), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires57 : Excluded 5 0 wires57 := leafExcluded (by decide +kernel)

def wires58 : List Sig := [(0xffffffff, 0xffffffdf), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires58 : Excluded 5 0 wires58 := leafExcluded (by decide +kernel)

def wires59 : List Sig := [(0x3f0e63c7, 0x82022042), (0xff0fffff, 0x8a06acdb), (0xffffffff, 0xefbeefdf), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires59 : Excluded 5 0 wires59 := leafExcluded (by decide +kernel)

def wires60 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xffffffff, 0xefbeefdf), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires60 : Excluded 5 0 wires60 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires47 : Excluded 6 0 wires47 :=
  cutExcluded (k:=5) (t:=0) (v:=wires47) [] [wires48, wires49, wires50, wires51, wires52, wires53, wires54, wires55, wires56, wires57, wires58, wires59, wires60]
    True.intro
    ⟨exclude5_0_wires48, exclude5_0_wires49, exclude5_0_wires50, exclude5_0_wires51, exclude5_0_wires52, exclude5_0_wires53, exclude5_0_wires54, exclude5_0_wires55, exclude5_0_wires56, exclude5_0_wires57, exclude5_0_wires58, exclude5_0_wires59, exclude5_0_wires60, True.intro⟩
    (by decide +kernel)

def wires61 : List Sig := [(0xc00f83f8, 0x08048090), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

def wires62 : List Sig := [(0xc0018238, 0x00000000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires62 : Excluded 5 0 wires62 := leafExcluded (by decide +kernel)

def wires63 : List Sig := [(0xffffffff, 0x5d75d6bd), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires63 : Excluded 5 0 wires63 := leafExcluded (by decide +kernel)

def wires64 : List Sig := [(0x000e03c0, 0x00000000), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires64 : Excluded 5 0 wires64 := leafExcluded (by decide +kernel)

def wires65 : List Sig := [(0xffffe3ff, 0xefbee3d6), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires65 : Excluded 5 0 wires65 := leafExcluded (by decide +kernel)

def wires66 : List Sig := [(0x000f8000, 0x08048000), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires66 : Excluded 5 0 wires66 := leafExcluded (by decide +kernel)

def wires67 : List Sig := [(0xc0fffff8, 0xbeeff890), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires67 : Excluded 5 0 wires67 := leafExcluded (by decide +kernel)

def wires68 : List Sig := [(0xc0fffff8, 0xbeeff890), (0xc00f83f8, 0x08048090), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires68 : Excluded 5 0 wires68 := leafExcluded (by decide +kernel)

def wires69 : List Sig := [(0xc0fffff8, 0xbeeff890), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires69 : Excluded 5 0 wires69 := leafExcluded (by decide +kernel)

def wires70 : List Sig := [(0xffffffff, 0xfbdfaffb), (0xff0fffff, 0x8a06acdb), (0xc00f83f8, 0x08048090), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires70 : Excluded 5 0 wires70 := leafExcluded (by decide +kernel)

def wires71 : List Sig := [(0xff01fe3f, 0x00000409), (0xfff1fe3f, 0x5571562d), (0xc00f83f8, 0x08048090), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires71 : Excluded 5 0 wires71 := leafExcluded (by decide +kernel)

def wires72 : List Sig := [(0xc0f18238, 0x51510220), (0xfff1fe3f, 0x5571562d), (0xc00f83f8, 0x08048090), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires72 : Excluded 5 0 wires72 := leafExcluded (by decide +kernel)

def wires73 : List Sig := [(0x00fe03c0, 0x61980300), (0x3ffe63c7, 0xe7ba6346), (0xc00f83f8, 0x08048090), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires73 : Excluded 5 0 wires73 := leafExcluded (by decide +kernel)

def wires74 : List Sig := [(0x00ff8000, 0x38cd8000), (0x00fffc00, 0xbeeff800), (0xc00f83f8, 0x08048090), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires74 : Excluded 5 0 wires74 := leafExcluded (by decide +kernel)

def wires75 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xc00f83f8, 0x08048090), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires75 : Excluded 5 0 wires75 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires61 : Excluded 6 0 wires61 :=
  cutExcluded (k:=5) (t:=0) (v:=wires61) [] [wires62, wires63, wires64, wires65, wires66, wires67, wires68, wires69, wires70, wires71, wires72, wires73, wires74, wires75]
    True.intro
    ⟨exclude5_0_wires62, exclude5_0_wires63, exclude5_0_wires64, exclude5_0_wires65, exclude5_0_wires66, exclude5_0_wires67, exclude5_0_wires68, exclude5_0_wires69, exclude5_0_wires70, exclude5_0_wires71, exclude5_0_wires72, exclude5_0_wires73, exclude5_0_wires74, exclude5_0_wires75, True.intro⟩
    (by decide +kernel)

def wires76 : List Sig := [(0xffffffff, 0xfbdfaffb), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

def wires77 : List Sig := [(0xfff1fe3f, 0x51510629), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires77 : Excluded 5 0 wires77 := leafExcluded (by decide +kernel)

def wires78 : List Sig := [(0xfff1fe3f, 0x51510629), (0xffffffff, 0xfbdfaffb), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires78 : Excluded 5 0 wires78 := leafExcluded (by decide +kernel)

def wires79 : List Sig := [(0xfff1fe3f, 0x51510629), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires79 : Excluded 5 0 wires79 := leafExcluded (by decide +kernel)

def wires80 : List Sig := [(0x3ffe63c7, 0xe39a2342), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires80 : Excluded 5 0 wires80 := leafExcluded (by decide +kernel)

def wires81 : List Sig := [(0x3ffe63c7, 0xe39a2342), (0xffffffff, 0xfbdfaffb), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires81 : Excluded 5 0 wires81 := leafExcluded (by decide +kernel)

def wires82 : List Sig := [(0x3ffe63c7, 0xe39a2342), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires82 : Excluded 5 0 wires82 := leafExcluded (by decide +kernel)

def wires83 : List Sig := [(0xffffffff, 0xffffefff), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires83 : Excluded 5 0 wires83 := leafExcluded (by decide +kernel)

def wires84 : List Sig := [(0x00fffc00, 0xbacfa800), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires84 : Excluded 5 0 wires84 := leafExcluded (by decide +kernel)

def wires85 : List Sig := [(0x00fffc00, 0xbacfa800), (0xffffffff, 0xfbdfaffb), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires85 : Excluded 5 0 wires85 := leafExcluded (by decide +kernel)

def wires86 : List Sig := [(0x00fffc00, 0xbacfa800), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires86 : Excluded 5 0 wires86 := leafExcluded (by decide +kernel)

def wires87 : List Sig := [(0xffffffff, 0xfffffffb), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires87 : Excluded 5 0 wires87 := leafExcluded (by decide +kernel)

def wires88 : List Sig := [(0xc00f83f8, 0x08048090), (0xff0fffff, 0x8a06acdb), (0xffffffff, 0xfbdfaffb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires88 : Excluded 5 0 wires88 := leafExcluded (by decide +kernel)

def wires89 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xffffffff, 0xfbdfaffb), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires89 : Excluded 5 0 wires89 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires76 : Excluded 6 0 wires76 :=
  cutExcluded (k:=5) (t:=0) (v:=wires76) [] [wires77, wires78, wires79, wires80, wires81, wires82, wires83, wires84, wires85, wires86, wires87, wires88, wires89]
    True.intro
    ⟨exclude5_0_wires77, exclude5_0_wires78, exclude5_0_wires79, exclude5_0_wires80, exclude5_0_wires81, exclude5_0_wires82, exclude5_0_wires83, exclude5_0_wires84, exclude5_0_wires85, exclude5_0_wires86, exclude5_0_wires87, exclude5_0_wires88, exclude5_0_wires89, True.intro⟩
    (by decide +kernel)

def wires90 : List Sig := [(0x000ffc00, 0x8a06a800), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

def wires91 : List Sig := [(0x0001fc00, 0x00000000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires91 : Excluded 5 0 wires91 := leafExcluded (by decide +kernel)

def wires92 : List Sig := [(0xfffffe3f, 0xdf77fe2d), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires92 : Excluded 5 0 wires92 := leafExcluded (by decide +kernel)

def wires93 : List Sig := [(0x000e6000, 0x82022000), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires93 : Excluded 5 0 wires93 := leafExcluded (by decide +kernel)

def wires94 : List Sig := [(0x3fffffc7, 0xefbeeb46), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires94 : Excluded 5 0 wires94 := leafExcluded (by decide +kernel)

def wires95 : List Sig := [(0x000f8000, 0x08048000), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires95 : Excluded 5 0 wires95 := leafExcluded (by decide +kernel)

def wires96 : List Sig := [(0xc0fffff8, 0xfbdfabb0), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires96 : Excluded 5 0 wires96 := leafExcluded (by decide +kernel)

def wires97 : List Sig := [(0xffffffff, 0xbeeffcdb), (0xff0fffff, 0x8a06acdb), (0x000ffc00, 0x8a06a800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires97 : Excluded 5 0 wires97 := leafExcluded (by decide +kernel)

def wires98 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x000ffc00, 0x8a06a800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires98 : Excluded 5 0 wires98 := leafExcluded (by decide +kernel)

def wires99 : List Sig := [(0x00fe6000, 0xa6aa6000), (0x3ffe63c7, 0xe7ba6346), (0x000ffc00, 0x8a06a800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires99 : Excluded 5 0 wires99 := leafExcluded (by decide +kernel)

def wires100 : List Sig := [(0x00ff8000, 0x38cd8000), (0xc0ff83f8, 0x79dd83b0), (0x000ffc00, 0x8a06a800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires100 : Excluded 5 0 wires100 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires90 : Excluded 6 0 wires90 :=
  cutExcluded (k:=5) (t:=0) (v:=wires90) [] [wires91, wires92, wires93, wires94, wires95, wires96, wires97, wires98, wires99, wires100]
    True.intro
    ⟨exclude5_0_wires91, exclude5_0_wires92, exclude5_0_wires93, exclude5_0_wires94, exclude5_0_wires95, exclude5_0_wires96, exclude5_0_wires97, exclude5_0_wires98, exclude5_0_wires99, exclude5_0_wires100, True.intro⟩
    (by decide +kernel)

def wires101 : List Sig := [(0xffffffff, 0xbeeffcdb), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

def wires102 : List Sig := [(0xfff1fe3f, 0x14615409), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires102 : Excluded 5 0 wires102 := leafExcluded (by decide +kernel)

def wires103 : List Sig := [(0xfff1fe3f, 0x14615409), (0xffffffff, 0xbeeffcdb), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires103 : Excluded 5 0 wires103 := leafExcluded (by decide +kernel)

def wires104 : List Sig := [(0xfff1fe3f, 0x14615409), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires104 : Excluded 5 0 wires104 := leafExcluded (by decide +kernel)

def wires105 : List Sig := [(0xffffffff, 0xfffffeff), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires105 : Excluded 5 0 wires105 := leafExcluded (by decide +kernel)

def wires106 : List Sig := [(0x3ffe63c7, 0xa6aa6042), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires106 : Excluded 5 0 wires106 := leafExcluded (by decide +kernel)

def wires107 : List Sig := [(0x3ffe63c7, 0xa6aa6042), (0xffffffff, 0xbeeffcdb), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires107 : Excluded 5 0 wires107 := leafExcluded (by decide +kernel)

def wires108 : List Sig := [(0x3ffe63c7, 0xa6aa6042), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires108 : Excluded 5 0 wires108 := leafExcluded (by decide +kernel)

def wires109 : List Sig := [(0xffffffff, 0xffffffdf), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires109 : Excluded 5 0 wires109 := leafExcluded (by decide +kernel)

def wires110 : List Sig := [(0xc0ff83f8, 0x38cd8090), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires110 : Excluded 5 0 wires110 := leafExcluded (by decide +kernel)

def wires111 : List Sig := [(0xc0ff83f8, 0x38cd8090), (0xffffffff, 0xbeeffcdb), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires111 : Excluded 5 0 wires111 := leafExcluded (by decide +kernel)

def wires112 : List Sig := [(0xc0ff83f8, 0x38cd8090), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires112 : Excluded 5 0 wires112 := leafExcluded (by decide +kernel)

def wires113 : List Sig := [(0xffffffff, 0xfffffffb), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires113 : Excluded 5 0 wires113 := leafExcluded (by decide +kernel)

def wires114 : List Sig := [(0x000ffc00, 0x8a06a800), (0xff0fffff, 0x8a06acdb), (0xffffffff, 0xbeeffcdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires114 : Excluded 5 0 wires114 := leafExcluded (by decide +kernel)

def wires115 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xffffffff, 0xbeeffcdb), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires115 : Excluded 5 0 wires115 := leafExcluded (by decide +kernel)

def wires116 : List Sig := [(0x3fffffc7, 0xfffffb46), (0x3ffe63c7, 0xe7ba6346), (0xffffffff, 0xbeeffcdb), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires116 : Excluded 5 0 wires116 := leafExcluded (by decide +kernel)

def wires117 : List Sig := [(0xc0fffff8, 0xfffffbb0), (0xc0ff83f8, 0x79dd83b0), (0xffffffff, 0xbeeffcdb), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires117 : Excluded 5 0 wires117 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires101 : Excluded 6 0 wires101 :=
  cutExcluded (k:=5) (t:=0) (v:=wires101) [] [wires102, wires103, wires104, wires105, wires106, wires107, wires108, wires109, wires110, wires111, wires112, wires113, wires114, wires115, wires116, wires117]
    True.intro
    ⟨exclude5_0_wires102, exclude5_0_wires103, exclude5_0_wires104, exclude5_0_wires105, exclude5_0_wires106, exclude5_0_wires107, exclude5_0_wires108, exclude5_0_wires109, exclude5_0_wires110, exclude5_0_wires111, exclude5_0_wires112, exclude5_0_wires113, exclude5_0_wires114, exclude5_0_wires115, exclude5_0_wires116, exclude5_0_wires117, True.intro⟩
    (by decide +kernel)

def wires118 : List Sig := [(0x3ff06207, 0x45304204), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

def wires119 : List Sig := [(0x3f006207, 0x00000000), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires119 : Excluded 5 0 wires119 := leafExcluded (by decide +kernel)

def wires120 : List Sig := [(0xffffffff, 0xcf36eedf), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires120 : Excluded 5 0 wires120 := leafExcluded (by decide +kernel)

def wires121 : List Sig := [(0x00f00200, 0x41100200), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires121 : Excluded 5 0 wires121 := leafExcluded (by decide +kernel)

def wires122 : List Sig := [(0xffffe3ff, 0x7dfdc3b4), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires122 : Excluded 5 0 wires122 := leafExcluded (by decide +kernel)

def wires123 : List Sig := [(0x00f06000, 0x04204000), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires123 : Excluded 5 0 wires123 := leafExcluded (by decide +kernel)

def wires124 : List Sig := [(0x3ffffe07, 0xfffffa04), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires124 : Excluded 5 0 wires124 := leafExcluded (by decide +kernel)

def wires125 : List Sig := [(0xffffffff, 0xf7fb776f), (0x3ff06207, 0x45304204), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires125 : Excluded 5 0 wires125 := leafExcluded (by decide +kernel)

def wires126 : List Sig := [(0xffffffff, 0xf7fb776f), (0xfff1fe3f, 0x5571562d), (0x3ff06207, 0x45304204), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires126 : Excluded 5 0 wires126 := leafExcluded (by decide +kernel)

def wires127 : List Sig := [(0xffffffff, 0xf7fb776f), (0x3ffe63c7, 0xe7ba6346), (0x3ff06207, 0x45304204), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires127 : Excluded 5 0 wires127 := leafExcluded (by decide +kernel)

def wires128 : List Sig := [(0xff01fe3f, 0x00000409), (0xff0fffff, 0x8a06acdb), (0x3ff06207, 0x45304204), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires128 : Excluded 5 0 wires128 := leafExcluded (by decide +kernel)

def wires129 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x3ff06207, 0x45304204), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires129 : Excluded 5 0 wires129 := leafExcluded (by decide +kernel)

def wires130 : List Sig := [(0x3f0e63c7, 0x82022042), (0xff0fffff, 0x8a06acdb), (0x3ff06207, 0x45304204), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires130 : Excluded 5 0 wires130 := leafExcluded (by decide +kernel)

def wires131 : List Sig := [(0x00fe03c0, 0x61980300), (0xc0ff83f8, 0x79dd83b0), (0x3ff06207, 0x45304204), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires131 : Excluded 5 0 wires131 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires118 : Excluded 6 0 wires118 :=
  cutExcluded (k:=5) (t:=0) (v:=wires118) [] [wires119, wires120, wires121, wires122, wires123, wires124, wires125, wires126, wires127, wires128, wires129, wires130, wires131]
    True.intro
    ⟨exclude5_0_wires119, exclude5_0_wires120, exclude5_0_wires121, exclude5_0_wires122, exclude5_0_wires123, exclude5_0_wires124, exclude5_0_wires125, exclude5_0_wires126, exclude5_0_wires127, exclude5_0_wires128, exclude5_0_wires129, exclude5_0_wires130, exclude5_0_wires131, True.intro⟩
    (by decide +kernel)

def wires132 : List Sig := [(0xffffffff, 0xf7fb776f), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

def wires133 : List Sig := [(0xff0fffff, 0x8202244b), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires133 : Excluded 5 0 wires133 := leafExcluded (by decide +kernel)

def wires134 : List Sig := [(0xff0fffff, 0x8202244b), (0xffffffff, 0xf7fb776f), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires134 : Excluded 5 0 wires134 := leafExcluded (by decide +kernel)

def wires135 : List Sig := [(0xff0fffff, 0x8202244b), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires135 : Excluded 5 0 wires135 := leafExcluded (by decide +kernel)

def wires136 : List Sig := [(0xc0ff83f8, 0x71d90320), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires136 : Excluded 5 0 wires136 := leafExcluded (by decide +kernel)

def wires137 : List Sig := [(0xc0ff83f8, 0x71d90320), (0xffffffff, 0xf7fb776f), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires137 : Excluded 5 0 wires137 := leafExcluded (by decide +kernel)

def wires138 : List Sig := [(0xc0ff83f8, 0x71d90320), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires138 : Excluded 5 0 wires138 := leafExcluded (by decide +kernel)

def wires139 : List Sig := [(0xffffffff, 0xfffff7ff), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires139 : Excluded 5 0 wires139 := leafExcluded (by decide +kernel)

def wires140 : List Sig := [(0x00fffc00, 0xb6eb7000), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires140 : Excluded 5 0 wires140 := leafExcluded (by decide +kernel)

def wires141 : List Sig := [(0x00fffc00, 0xb6eb7000), (0xffffffff, 0xf7fb776f), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires141 : Excluded 5 0 wires141 := leafExcluded (by decide +kernel)

def wires142 : List Sig := [(0x00fffc00, 0xb6eb7000), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires142 : Excluded 5 0 wires142 := leafExcluded (by decide +kernel)

def wires143 : List Sig := [(0xffffffff, 0xffffff6f), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires143 : Excluded 5 0 wires143 := leafExcluded (by decide +kernel)

def wires144 : List Sig := [(0x3ff06207, 0x45304204), (0xffffffff, 0xf7fb776f), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires144 : Excluded 5 0 wires144 := leafExcluded (by decide +kernel)

def wires145 : List Sig := [(0x3ff06207, 0x45304204), (0xfff1fe3f, 0x5571562d), (0xffffffff, 0xf7fb776f), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires145 : Excluded 5 0 wires145 := leafExcluded (by decide +kernel)

def wires146 : List Sig := [(0x3ff06207, 0x45304204), (0x3ffe63c7, 0xe7ba6346), (0xffffffff, 0xf7fb776f), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires146 : Excluded 5 0 wires146 := leafExcluded (by decide +kernel)

def wires147 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xffffffff, 0xf7fb776f), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires147 : Excluded 5 0 wires147 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires132 : Excluded 6 0 wires132 :=
  cutExcluded (k:=5) (t:=0) (v:=wires132) [] [wires133, wires134, wires135, wires136, wires137, wires138, wires139, wires140, wires141, wires142, wires143, wires144, wires145, wires146, wires147]
    True.intro
    ⟨exclude5_0_wires133, exclude5_0_wires134, exclude5_0_wires135, exclude5_0_wires136, exclude5_0_wires137, exclude5_0_wires138, exclude5_0_wires139, exclude5_0_wires140, exclude5_0_wires141, exclude5_0_wires142, exclude5_0_wires143, exclude5_0_wires144, exclude5_0_wires145, exclude5_0_wires146, exclude5_0_wires147, True.intro⟩
    (by decide +kernel)

def wires148 : List Sig := [(0xc0f18238, 0x51510220), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

def wires149 : List Sig := [(0xc0018238, 0x00000000), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires149 : Excluded 5 0 wires149 := leafExcluded (by decide +kernel)

def wires150 : List Sig := [(0xffffffff, 0xdb57aefb), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires150 : Excluded 5 0 wires150 := leafExcluded (by decide +kernel)

def wires151 : List Sig := [(0x00f00200, 0x41100200), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires151 : Excluded 5 0 wires151 := leafExcluded (by decide +kernel)

def wires152 : List Sig := [(0xffffe3ff, 0xf7fb6366), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires152 : Excluded 5 0 wires152 := leafExcluded (by decide +kernel)

def wires153 : List Sig := [(0x00f18000, 0x10410000), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires153 : Excluded 5 0 wires153 := leafExcluded (by decide +kernel)

def wires154 : List Sig := [(0xc0fffe38, 0xfffffa20), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires154 : Excluded 5 0 wires154 := leafExcluded (by decide +kernel)

def wires155 : List Sig := [(0xffffffff, 0x7dfdd7bd), (0xc0f18238, 0x51510220), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires155 : Excluded 5 0 wires155 := leafExcluded (by decide +kernel)

def wires156 : List Sig := [(0xffffffff, 0x7dfdd7bd), (0xfff1fe3f, 0x5571562d), (0xc0f18238, 0x51510220), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires156 : Excluded 5 0 wires156 := leafExcluded (by decide +kernel)

def wires157 : List Sig := [(0xffffffff, 0x7dfdd7bd), (0xc0ff83f8, 0x79dd83b0), (0xc0f18238, 0x51510220), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires157 : Excluded 5 0 wires157 := leafExcluded (by decide +kernel)

def wires158 : List Sig := [(0xff01fe3f, 0x00000409), (0xff0fffff, 0x8a06acdb), (0xc0f18238, 0x51510220), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires158 : Excluded 5 0 wires158 := leafExcluded (by decide +kernel)

def wires159 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xc0f18238, 0x51510220), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires159 : Excluded 5 0 wires159 := leafExcluded (by decide +kernel)

def wires160 : List Sig := [(0xc00f83f8, 0x08048090), (0xff0fffff, 0x8a06acdb), (0xc0f18238, 0x51510220), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires160 : Excluded 5 0 wires160 := leafExcluded (by decide +kernel)

def wires161 : List Sig := [(0x00fe03c0, 0x61980300), (0x3ffe63c7, 0xe7ba6346), (0xc0f18238, 0x51510220), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires161 : Excluded 5 0 wires161 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires148 : Excluded 6 0 wires148 :=
  cutExcluded (k:=5) (t:=0) (v:=wires148) [] [wires149, wires150, wires151, wires152, wires153, wires154, wires155, wires156, wires157, wires158, wires159, wires160, wires161]
    True.intro
    ⟨exclude5_0_wires149, exclude5_0_wires150, exclude5_0_wires151, exclude5_0_wires152, exclude5_0_wires153, exclude5_0_wires154, exclude5_0_wires155, exclude5_0_wires156, exclude5_0_wires157, exclude5_0_wires158, exclude5_0_wires159, exclude5_0_wires160, exclude5_0_wires161, True.intro⟩
    (by decide +kernel)

def wires162 : List Sig := [(0xffffffff, 0x7dfdd7bd), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

def wires163 : List Sig := [(0xff0fffff, 0x08048499), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires163 : Excluded 5 0 wires163 := leafExcluded (by decide +kernel)

def wires164 : List Sig := [(0xff0fffff, 0x08048499), (0xffffffff, 0x7dfdd7bd), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires164 : Excluded 5 0 wires164 := leafExcluded (by decide +kernel)

def wires165 : List Sig := [(0xff0fffff, 0x08048499), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires165 : Excluded 5 0 wires165 := leafExcluded (by decide +kernel)

def wires166 : List Sig := [(0x3ffe63c7, 0x65b84304), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires166 : Excluded 5 0 wires166 := leafExcluded (by decide +kernel)

def wires167 : List Sig := [(0x3ffe63c7, 0x65b84304), (0xffffffff, 0x7dfdd7bd), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires167 : Excluded 5 0 wires167 := leafExcluded (by decide +kernel)

def wires168 : List Sig := [(0x3ffe63c7, 0x65b84304), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires168 : Excluded 5 0 wires168 := leafExcluded (by decide +kernel)

def wires169 : List Sig := [(0xffffffff, 0xfffff7ff), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires169 : Excluded 5 0 wires169 := leafExcluded (by decide +kernel)

def wires170 : List Sig := [(0x00fffc00, 0x3cedd000), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires170 : Excluded 5 0 wires170 := leafExcluded (by decide +kernel)

def wires171 : List Sig := [(0x00fffc00, 0x3cedd000), (0xffffffff, 0x7dfdd7bd), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires171 : Excluded 5 0 wires171 := leafExcluded (by decide +kernel)

def wires172 : List Sig := [(0x00fffc00, 0x3cedd000), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires172 : Excluded 5 0 wires172 := leafExcluded (by decide +kernel)

def wires173 : List Sig := [(0xffffffff, 0xffffffbd), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires173 : Excluded 5 0 wires173 := leafExcluded (by decide +kernel)

def wires174 : List Sig := [(0xc0f18238, 0x51510220), (0xffffffff, 0x7dfdd7bd), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires174 : Excluded 5 0 wires174 := leafExcluded (by decide +kernel)

def wires175 : List Sig := [(0xc0f18238, 0x51510220), (0xfff1fe3f, 0x5571562d), (0xffffffff, 0x7dfdd7bd), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires175 : Excluded 5 0 wires175 := leafExcluded (by decide +kernel)

def wires176 : List Sig := [(0xc0f18238, 0x51510220), (0xc0ff83f8, 0x79dd83b0), (0xffffffff, 0x7dfdd7bd), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires176 : Excluded 5 0 wires176 := leafExcluded (by decide +kernel)

def wires177 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xffffffff, 0x7dfdd7bd), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires177 : Excluded 5 0 wires177 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires162 : Excluded 6 0 wires162 :=
  cutExcluded (k:=5) (t:=0) (v:=wires162) [] [wires163, wires164, wires165, wires166, wires167, wires168, wires169, wires170, wires171, wires172, wires173, wires174, wires175, wires176, wires177]
    True.intro
    ⟨exclude5_0_wires163, exclude5_0_wires164, exclude5_0_wires165, exclude5_0_wires166, exclude5_0_wires167, exclude5_0_wires168, exclude5_0_wires169, exclude5_0_wires170, exclude5_0_wires171, exclude5_0_wires172, exclude5_0_wires173, exclude5_0_wires174, exclude5_0_wires175, exclude5_0_wires176, exclude5_0_wires177, True.intro⟩
    (by decide +kernel)

def wires178 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

def wires179 : List Sig := [(0x0001fc00, 0x00000000), (0x00f1fc00, 0x14615000), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires179 : Excluded 5 0 wires179 := leafExcluded (by decide +kernel)

def wires180 : List Sig := [(0xffffffff, 0x9e67fcdb), (0x00f1fc00, 0x14615000), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires180 : Excluded 5 0 wires180 := leafExcluded (by decide +kernel)

def wires181 : List Sig := [(0x00f06000, 0x04204000), (0x00f1fc00, 0x14615000), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires181 : Excluded 5 0 wires181 := leafExcluded (by decide +kernel)

def wires182 : List Sig := [(0x3fffffc7, 0xf7fb7346), (0x00f1fc00, 0x14615000), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires182 : Excluded 5 0 wires182 := leafExcluded (by decide +kernel)

def wires183 : List Sig := [(0x00f18000, 0x10410000), (0x00f1fc00, 0x14615000), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires183 : Excluded 5 0 wires183 := leafExcluded (by decide +kernel)

def wires184 : List Sig := [(0xc0fffff8, 0x7dfdd3b0), (0x00f1fc00, 0x14615000), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires184 : Excluded 5 0 wires184 := leafExcluded (by decide +kernel)

def wires185 : List Sig := [(0xff01fe3f, 0x00000409), (0xff0fffff, 0x8a06acdb), (0x00f1fc00, 0x14615000), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires185 : Excluded 5 0 wires185 := leafExcluded (by decide +kernel)

def wires186 : List Sig := [(0xff01fe3f, 0x00000409), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x00f1fc00, 0x14615000), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires186 : Excluded 5 0 wires186 := leafExcluded (by decide +kernel)

def wires187 : List Sig := [(0xffffffff, 0xdf77feff), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x00f1fc00, 0x14615000), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires187 : Excluded 5 0 wires187 := leafExcluded (by decide +kernel)

def wires188 : List Sig := [(0x3ff06207, 0x45304204), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00f1fc00, 0x14615000), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires188 : Excluded 5 0 wires188 := leafExcluded (by decide +kernel)

def wires189 : List Sig := [(0xffffffff, 0xf7fb776f), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00f1fc00, 0x14615000), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires189 : Excluded 5 0 wires189 := leafExcluded (by decide +kernel)

def wires190 : List Sig := [(0xc0f18238, 0x51510220), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00f1fc00, 0x14615000), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires190 : Excluded 5 0 wires190 := leafExcluded (by decide +kernel)

def wires191 : List Sig := [(0xffffffff, 0x7dfdd7bd), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00f1fc00, 0x14615000), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires191 : Excluded 5 0 wires191 := leafExcluded (by decide +kernel)

def wires192 : List Sig := [(0x3f0e63c7, 0x82022042), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires192 : Excluded 5 0 wires192 := leafExcluded (by decide +kernel)

def wires193 : List Sig := [(0xffffffff, 0xefbeefdf), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires193 : Excluded 5 0 wires193 := leafExcluded (by decide +kernel)

def wires194 : List Sig := [(0xc00f83f8, 0x08048090), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires194 : Excluded 5 0 wires194 := leafExcluded (by decide +kernel)

def wires195 : List Sig := [(0xffffffff, 0xfbdfaffb), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires195 : Excluded 5 0 wires195 := leafExcluded (by decide +kernel)

def wires196 : List Sig := [(0x00fe03c0, 0x61980300), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires196 : Excluded 5 0 wires196 := leafExcluded (by decide +kernel)

def wires197 : List Sig := [(0xffffe3ff, 0xffffe3f6), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires197 : Excluded 5 0 wires197 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires178 : Excluded 6 0 wires178 :=
  cutExcluded (k:=5) (t:=0) (v:=wires178) [] [wires179, wires180, wires181, wires182, wires183, wires184, wires185, wires186, wires187, wires188, wires189, wires190, wires191, wires192, wires193, wires194, wires195, wires196, wires197]
    True.intro
    ⟨exclude5_0_wires179, exclude5_0_wires180, exclude5_0_wires181, exclude5_0_wires182, exclude5_0_wires183, exclude5_0_wires184, exclude5_0_wires185, exclude5_0_wires186, exclude5_0_wires187, exclude5_0_wires188, exclude5_0_wires189, exclude5_0_wires190, exclude5_0_wires191, exclude5_0_wires192, exclude5_0_wires193, exclude5_0_wires194, exclude5_0_wires195, exclude5_0_wires196, exclude5_0_wires197, True.intro⟩
    (by decide +kernel)

def wires198 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

def wires199 : List Sig := [(0x0001fc00, 0x00000000), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires199 : Excluded 5 0 wires199 := leafExcluded (by decide +kernel)

def wires200 : List Sig := [(0xffffffff, 0x9e67fcdb), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires200 : Excluded 5 0 wires200 := leafExcluded (by decide +kernel)

def wires201 : List Sig := [(0x00f06000, 0x04204000), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires201 : Excluded 5 0 wires201 := leafExcluded (by decide +kernel)

def wires202 : List Sig := [(0x3fffffc7, 0xf7fb7346), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires202 : Excluded 5 0 wires202 := leafExcluded (by decide +kernel)

def wires203 : List Sig := [(0x00f18000, 0x10410000), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires203 : Excluded 5 0 wires203 := leafExcluded (by decide +kernel)

def wires204 : List Sig := [(0xc0fffff8, 0x7dfdd3b0), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires204 : Excluded 5 0 wires204 := leafExcluded (by decide +kernel)

def wires205 : List Sig := [(0xfffffe3f, 0xfffffe2d), (0xfff1fe3f, 0x5571562d), (0x00f1fc00, 0x14615000), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires205 : Excluded 5 0 wires205 := leafExcluded (by decide +kernel)

def wires206 : List Sig := [(0xff01fe3f, 0x00000409), (0xff0fffff, 0x8a06acdb), (0x00f1fc00, 0x14615000), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires206 : Excluded 5 0 wires206 := leafExcluded (by decide +kernel)

def wires207 : List Sig := [(0x000ffc00, 0x8a06a800), (0xff0fffff, 0x8a06acdb), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires207 : Excluded 5 0 wires207 := leafExcluded (by decide +kernel)

def wires208 : List Sig := [(0xffffffff, 0xbeeffcdb), (0xff0fffff, 0x8a06acdb), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires208 : Excluded 5 0 wires208 := leafExcluded (by decide +kernel)

def wires209 : List Sig := [(0x00fe6000, 0xa6aa6000), (0x3ffe63c7, 0xe7ba6346), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires209 : Excluded 5 0 wires209 := leafExcluded (by decide +kernel)

def wires210 : List Sig := [(0x3fffffc7, 0xfffffb46), (0x3ffe63c7, 0xe7ba6346), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires210 : Excluded 5 0 wires210 := leafExcluded (by decide +kernel)

def wires211 : List Sig := [(0x00ff8000, 0x38cd8000), (0xc0ff83f8, 0x79dd83b0), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires211 : Excluded 5 0 wires211 := leafExcluded (by decide +kernel)

def wires212 : List Sig := [(0xc0fffff8, 0xfffffbb0), (0xc0ff83f8, 0x79dd83b0), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires212 : Excluded 5 0 wires212 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires198 : Excluded 6 0 wires198 :=
  cutExcluded (k:=5) (t:=0) (v:=wires198) [] [wires199, wires200, wires201, wires202, wires203, wires204, wires205, wires206, wires207, wires208, wires209, wires210, wires211, wires212]
    True.intro
    ⟨exclude5_0_wires199, exclude5_0_wires200, exclude5_0_wires201, exclude5_0_wires202, exclude5_0_wires203, exclude5_0_wires204, exclude5_0_wires205, exclude5_0_wires206, exclude5_0_wires207, exclude5_0_wires208, exclude5_0_wires209, exclude5_0_wires210, exclude5_0_wires211, exclude5_0_wires212, True.intro⟩
    (by decide +kernel)

def wires213 : List Sig := [(0xfffffe3f, 0xfffffe2d), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

def wires214 : List Sig := [(0xff0ffe3f, 0x8a06ac09), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires214 : Excluded 5 0 wires214 := leafExcluded (by decide +kernel)

def wires215 : List Sig := [(0xffffffff, 0xfffffeff), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires215 : Excluded 5 0 wires215 := leafExcluded (by decide +kernel)

def wires216 : List Sig := [(0x3ffe6207, 0xe7ba6204), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires216 : Excluded 5 0 wires216 := leafExcluded (by decide +kernel)

def wires217 : List Sig := [(0xffffffff, 0xffffff6f), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires217 : Excluded 5 0 wires217 := leafExcluded (by decide +kernel)

def wires218 : List Sig := [(0xc0ff8238, 0x79dd8220), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires218 : Excluded 5 0 wires218 := leafExcluded (by decide +kernel)

def wires219 : List Sig := [(0xffffffff, 0xffffffbd), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires219 : Excluded 5 0 wires219 := leafExcluded (by decide +kernel)

def wires220 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xfffffe3f, 0xfffffe2d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires220 : Excluded 5 0 wires220 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires213 : Excluded 6 0 wires213 :=
  cutExcluded (k:=5) (t:=0) (v:=wires213) [] [wires214, wires215, wires216, wires217, wires218, wires219, wires220]
    True.intro
    ⟨exclude5_0_wires214, exclude5_0_wires215, exclude5_0_wires216, exclude5_0_wires217, exclude5_0_wires218, exclude5_0_wires219, exclude5_0_wires220, True.intro⟩
    (by decide +kernel)

def wires221 : List Sig := [(0x00fe03c0, 0x61980300), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

def wires222 : List Sig := [(0x000e03c0, 0x00000000), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires222 : Excluded 5 0 wires222 := leafExcluded (by decide +kernel)

def wires223 : List Sig := [(0xffffffff, 0xeb9eafdb), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires223 : Excluded 5 0 wires223 := leafExcluded (by decide +kernel)

def wires224 : List Sig := [(0x00f00200, 0x41100200), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires224 : Excluded 5 0 wires224 := leafExcluded (by decide +kernel)

def wires225 : List Sig := [(0xffffffff, 0x75f9572d), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires225 : Excluded 5 0 wires225 := leafExcluded (by decide +kernel)

def wires226 : List Sig := [(0x00fe0000, 0x20880000), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires226 : Excluded 5 0 wires226 := leafExcluded (by decide +kernel)

def wires227 : List Sig := [(0x00ffffc0, 0xfffffb00), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires227 : Excluded 5 0 wires227 := leafExcluded (by decide +kernel)

def wires228 : List Sig := [(0xffffe3ff, 0xffffe3f6), (0x00fe03c0, 0x61980300), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires228 : Excluded 5 0 wires228 := leafExcluded (by decide +kernel)

def wires229 : List Sig := [(0xffffe3ff, 0xffffe3f6), (0x3ffe63c7, 0xe7ba6346), (0x00fe03c0, 0x61980300), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires229 : Excluded 5 0 wires229 := leafExcluded (by decide +kernel)

def wires230 : List Sig := [(0xffffe3ff, 0xffffe3f6), (0xc0ff83f8, 0x79dd83b0), (0x00fe03c0, 0x61980300), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires230 : Excluded 5 0 wires230 := leafExcluded (by decide +kernel)

def wires231 : List Sig := [(0x3f0e63c7, 0x82022042), (0xff0fffff, 0x8a06acdb), (0x00fe03c0, 0x61980300), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires231 : Excluded 5 0 wires231 := leafExcluded (by decide +kernel)

def wires232 : List Sig := [(0x3ff06207, 0x45304204), (0xfff1fe3f, 0x5571562d), (0x00fe03c0, 0x61980300), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires232 : Excluded 5 0 wires232 := leafExcluded (by decide +kernel)

def wires233 : List Sig := [(0x3fffffc7, 0xfffffb46), (0x00fffc00, 0xbeeff800), (0x00fe03c0, 0x61980300), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires233 : Excluded 5 0 wires233 := leafExcluded (by decide +kernel)

def wires234 : List Sig := [(0xc00f83f8, 0x08048090), (0xff0fffff, 0x8a06acdb), (0x00fe03c0, 0x61980300), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires234 : Excluded 5 0 wires234 := leafExcluded (by decide +kernel)

def wires235 : List Sig := [(0xc0f18238, 0x51510220), (0xfff1fe3f, 0x5571562d), (0x00fe03c0, 0x61980300), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires235 : Excluded 5 0 wires235 := leafExcluded (by decide +kernel)

def wires236 : List Sig := [(0xc0fffff8, 0xfffffbb0), (0x00fffc00, 0xbeeff800), (0x00fe03c0, 0x61980300), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires236 : Excluded 5 0 wires236 := leafExcluded (by decide +kernel)

def wires237 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x00fe03c0, 0x61980300), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires237 : Excluded 5 0 wires237 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires221 : Excluded 6 0 wires221 :=
  cutExcluded (k:=5) (t:=0) (v:=wires221) [] [wires222, wires223, wires224, wires225, wires226, wires227, wires228, wires229, wires230, wires231, wires232, wires233, wires234, wires235, wires236, wires237]
    True.intro
    ⟨exclude5_0_wires222, exclude5_0_wires223, exclude5_0_wires224, exclude5_0_wires225, exclude5_0_wires226, exclude5_0_wires227, exclude5_0_wires228, exclude5_0_wires229, exclude5_0_wires230, exclude5_0_wires231, exclude5_0_wires232, exclude5_0_wires233, exclude5_0_wires234, exclude5_0_wires235, exclude5_0_wires236, exclude5_0_wires237, True.intro⟩
    (by decide +kernel)

def wires238 : List Sig := [(0xffffe3ff, 0xffffe3f6), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

def wires239 : List Sig := [(0xff0fe3ff, 0x8a06a0d2), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires239 : Excluded 5 0 wires239 := leafExcluded (by decide +kernel)

def wires240 : List Sig := [(0xffffffff, 0xffffefff), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires240 : Excluded 5 0 wires240 := leafExcluded (by decide +kernel)

def wires241 : List Sig := [(0xfff1e23f, 0x55714224), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires241 : Excluded 5 0 wires241 := leafExcluded (by decide +kernel)

def wires242 : List Sig := [(0xffffffff, 0xfffff7ff), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires242 : Excluded 5 0 wires242 := leafExcluded (by decide +kernel)

def wires243 : List Sig := [(0x00ffe000, 0xbeefe000), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires243 : Excluded 5 0 wires243 := leafExcluded (by decide +kernel)

def wires244 : List Sig := [(0xffffffff, 0xfffffbf6), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires244 : Excluded 5 0 wires244 := leafExcluded (by decide +kernel)

def wires245 : List Sig := [(0x00fe03c0, 0x61980300), (0xffffe3ff, 0xffffe3f6), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires245 : Excluded 5 0 wires245 := leafExcluded (by decide +kernel)

def wires246 : List Sig := [(0x00fe03c0, 0x61980300), (0x3ffe63c7, 0xe7ba6346), (0xffffe3ff, 0xffffe3f6), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires246 : Excluded 5 0 wires246 := leafExcluded (by decide +kernel)

def wires247 : List Sig := [(0x00fe03c0, 0x61980300), (0xc0ff83f8, 0x79dd83b0), (0xffffe3ff, 0xffffe3f6), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires247 : Excluded 5 0 wires247 := leafExcluded (by decide +kernel)

def wires248 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xffffe3ff, 0xffffe3f6), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires248 : Excluded 5 0 wires248 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires238 : Excluded 6 0 wires238 :=
  cutExcluded (k:=5) (t:=0) (v:=wires238) [] [wires239, wires240, wires241, wires242, wires243, wires244, wires245, wires246, wires247, wires248]
    True.intro
    ⟨exclude5_0_wires239, exclude5_0_wires240, exclude5_0_wires241, exclude5_0_wires242, exclude5_0_wires243, exclude5_0_wires244, exclude5_0_wires245, exclude5_0_wires246, exclude5_0_wires247, exclude5_0_wires248, True.intro⟩
    (by decide +kernel)

def wires249 : List Sig := [(0x00fe6000, 0xa6aa6000), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

def wires250 : List Sig := [(0x000e6000, 0x82022000), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires250 : Excluded 5 0 wires250 := leafExcluded (by decide +kernel)

def wires251 : List Sig := [(0xffffffff, 0xaeaeecdb), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires251 : Excluded 5 0 wires251 := leafExcluded (by decide +kernel)

def wires252 : List Sig := [(0x00f06000, 0x04204000), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires252 : Excluded 5 0 wires252 := leafExcluded (by decide +kernel)

def wires253 : List Sig := [(0xfffffe3f, 0xf7fb762d), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires253 : Excluded 5 0 wires253 := leafExcluded (by decide +kernel)

def wires254 : List Sig := [(0x00fe0000, 0x20880000), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires254 : Excluded 5 0 wires254 := leafExcluded (by decide +kernel)

def wires255 : List Sig := [(0xc0ffe3f8, 0xffffe3b0), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires255 : Excluded 5 0 wires255 := leafExcluded (by decide +kernel)

def wires256 : List Sig := [(0x3fffffc7, 0xfffffb46), (0x00fe6000, 0xa6aa6000), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires256 : Excluded 5 0 wires256 := leafExcluded (by decide +kernel)

def wires257 : List Sig := [(0x3fffffc7, 0xfffffb46), (0x3ffe63c7, 0xe7ba6346), (0x00fe6000, 0xa6aa6000), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires257 : Excluded 5 0 wires257 := leafExcluded (by decide +kernel)

def wires258 : List Sig := [(0x3fffffc7, 0xfffffb46), (0x00fffc00, 0xbeeff800), (0x00fe6000, 0xa6aa6000), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires258 : Excluded 5 0 wires258 := leafExcluded (by decide +kernel)

def wires259 : List Sig := [(0x3f0e63c7, 0x82022042), (0xff0fffff, 0x8a06acdb), (0x00fe6000, 0xa6aa6000), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires259 : Excluded 5 0 wires259 := leafExcluded (by decide +kernel)

def wires260 : List Sig := [(0x000ffc00, 0x8a06a800), (0xff0fffff, 0x8a06acdb), (0x00fe6000, 0xa6aa6000), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires260 : Excluded 5 0 wires260 := leafExcluded (by decide +kernel)

def wires261 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x00fe6000, 0xa6aa6000), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires261 : Excluded 5 0 wires261 := leafExcluded (by decide +kernel)

def wires262 : List Sig := [(0xc0fffff8, 0xfffffbb0), (0xc0ff83f8, 0x79dd83b0), (0x00fe6000, 0xa6aa6000), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires262 : Excluded 5 0 wires262 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires249 : Excluded 6 0 wires249 :=
  cutExcluded (k:=5) (t:=0) (v:=wires249) [] [wires250, wires251, wires252, wires253, wires254, wires255, wires256, wires257, wires258, wires259, wires260, wires261, wires262]
    True.intro
    ⟨exclude5_0_wires250, exclude5_0_wires251, exclude5_0_wires252, exclude5_0_wires253, exclude5_0_wires254, exclude5_0_wires255, exclude5_0_wires256, exclude5_0_wires257, exclude5_0_wires258, exclude5_0_wires259, exclude5_0_wires260, exclude5_0_wires261, exclude5_0_wires262, True.intro⟩
    (by decide +kernel)

def wires263 : List Sig := [(0x3fffffc7, 0xfffffb46), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

def wires264 : List Sig := [(0x3f0fffc7, 0x8a06a842), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires264 : Excluded 5 0 wires264 := leafExcluded (by decide +kernel)

def wires265 : List Sig := [(0xffffffff, 0xffffffdf), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires265 : Excluded 5 0 wires265 := leafExcluded (by decide +kernel)

def wires266 : List Sig := [(0x3ff1fe07, 0x55715204), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires266 : Excluded 5 0 wires266 := leafExcluded (by decide +kernel)

def wires267 : List Sig := [(0xffffffff, 0xffffff6f), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires267 : Excluded 5 0 wires267 := leafExcluded (by decide +kernel)

def wires268 : List Sig := [(0x00ff83c0, 0x79dd8300), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires268 : Excluded 5 0 wires268 := leafExcluded (by decide +kernel)

def wires269 : List Sig := [(0xffffffff, 0xfffffbf6), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires269 : Excluded 5 0 wires269 := leafExcluded (by decide +kernel)

def wires270 : List Sig := [(0x00fe6000, 0xa6aa6000), (0x3fffffc7, 0xfffffb46), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires270 : Excluded 5 0 wires270 := leafExcluded (by decide +kernel)

def wires271 : List Sig := [(0x00fe6000, 0xa6aa6000), (0x3ffe63c7, 0xe7ba6346), (0x3fffffc7, 0xfffffb46), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires271 : Excluded 5 0 wires271 := leafExcluded (by decide +kernel)

def wires272 : List Sig := [(0x00fe6000, 0xa6aa6000), (0x00fffc00, 0xbeeff800), (0x3fffffc7, 0xfffffb46), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires272 : Excluded 5 0 wires272 := leafExcluded (by decide +kernel)

def wires273 : List Sig := [(0x00fe03c0, 0x61980300), (0xc0ff83f8, 0x79dd83b0), (0x3fffffc7, 0xfffffb46), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires273 : Excluded 5 0 wires273 := leafExcluded (by decide +kernel)

def wires274 : List Sig := [(0xffffffff, 0xbeeffcdb), (0xff0fffff, 0x8a06acdb), (0x3fffffc7, 0xfffffb46), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires274 : Excluded 5 0 wires274 := leafExcluded (by decide +kernel)

def wires275 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x3fffffc7, 0xfffffb46), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires275 : Excluded 5 0 wires275 := leafExcluded (by decide +kernel)

def wires276 : List Sig := [(0x00ff8000, 0x38cd8000), (0xc0ff83f8, 0x79dd83b0), (0x3fffffc7, 0xfffffb46), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires276 : Excluded 5 0 wires276 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires263 : Excluded 6 0 wires263 :=
  cutExcluded (k:=5) (t:=0) (v:=wires263) [] [wires264, wires265, wires266, wires267, wires268, wires269, wires270, wires271, wires272, wires273, wires274, wires275, wires276]
    True.intro
    ⟨exclude5_0_wires264, exclude5_0_wires265, exclude5_0_wires266, exclude5_0_wires267, exclude5_0_wires268, exclude5_0_wires269, exclude5_0_wires270, exclude5_0_wires271, exclude5_0_wires272, exclude5_0_wires273, exclude5_0_wires274, exclude5_0_wires275, exclude5_0_wires276, True.intro⟩
    (by decide +kernel)

def wires277 : List Sig := [(0x00ff8000, 0x38cd8000), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

def wires278 : List Sig := [(0x000f8000, 0x08048000), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires278 : Excluded 5 0 wires278 := leafExcluded (by decide +kernel)

def wires279 : List Sig := [(0xffffffff, 0xbacfacdb), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires279 : Excluded 5 0 wires279 := leafExcluded (by decide +kernel)

def wires280 : List Sig := [(0x00f18000, 0x10410000), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires280 : Excluded 5 0 wires280 := leafExcluded (by decide +kernel)

def wires281 : List Sig := [(0xfffffe3f, 0x7dfdd62d), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires281 : Excluded 5 0 wires281 := leafExcluded (by decide +kernel)

def wires282 : List Sig := [(0x00fe0000, 0x20880000), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires282 : Excluded 5 0 wires282 := leafExcluded (by decide +kernel)

def wires283 : List Sig := [(0x3fffe3c7, 0xffffe346), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires283 : Excluded 5 0 wires283 := leafExcluded (by decide +kernel)

def wires284 : List Sig := [(0xc0fffff8, 0xfffffbb0), (0x00ff8000, 0x38cd8000), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires284 : Excluded 5 0 wires284 := leafExcluded (by decide +kernel)

def wires285 : List Sig := [(0xc0fffff8, 0xfffffbb0), (0xc0ff83f8, 0x79dd83b0), (0x00ff8000, 0x38cd8000), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires285 : Excluded 5 0 wires285 := leafExcluded (by decide +kernel)

def wires286 : List Sig := [(0xc0fffff8, 0xfffffbb0), (0x00fffc00, 0xbeeff800), (0x00ff8000, 0x38cd8000), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires286 : Excluded 5 0 wires286 := leafExcluded (by decide +kernel)

def wires287 : List Sig := [(0xc00f83f8, 0x08048090), (0xff0fffff, 0x8a06acdb), (0x00ff8000, 0x38cd8000), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires287 : Excluded 5 0 wires287 := leafExcluded (by decide +kernel)

def wires288 : List Sig := [(0x000ffc00, 0x8a06a800), (0xff0fffff, 0x8a06acdb), (0x00ff8000, 0x38cd8000), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires288 : Excluded 5 0 wires288 := leafExcluded (by decide +kernel)

def wires289 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x00ff8000, 0x38cd8000), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires289 : Excluded 5 0 wires289 := leafExcluded (by decide +kernel)

def wires290 : List Sig := [(0x3fffffc7, 0xfffffb46), (0x3ffe63c7, 0xe7ba6346), (0x00ff8000, 0x38cd8000), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires290 : Excluded 5 0 wires290 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires277 : Excluded 6 0 wires277 :=
  cutExcluded (k:=5) (t:=0) (v:=wires277) [] [wires278, wires279, wires280, wires281, wires282, wires283, wires284, wires285, wires286, wires287, wires288, wires289, wires290]
    True.intro
    ⟨exclude5_0_wires278, exclude5_0_wires279, exclude5_0_wires280, exclude5_0_wires281, exclude5_0_wires282, exclude5_0_wires283, exclude5_0_wires284, exclude5_0_wires285, exclude5_0_wires286, exclude5_0_wires287, exclude5_0_wires288, exclude5_0_wires289, exclude5_0_wires290, True.intro⟩
    (by decide +kernel)

def wires291 : List Sig := [(0xc0fffff8, 0xfffffbb0), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

def wires292 : List Sig := [(0xc00ffff8, 0x8a06a890), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires292 : Excluded 5 0 wires292 := leafExcluded (by decide +kernel)

def wires293 : List Sig := [(0xffffffff, 0xfffffffb), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires293 : Excluded 5 0 wires293 := leafExcluded (by decide +kernel)

def wires294 : List Sig := [(0xc0f1fe38, 0x55715220), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires294 : Excluded 5 0 wires294 := leafExcluded (by decide +kernel)

def wires295 : List Sig := [(0xffffffff, 0xffffffbd), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires295 : Excluded 5 0 wires295 := leafExcluded (by decide +kernel)

def wires296 : List Sig := [(0x00fe63c0, 0xe7ba6300), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires296 : Excluded 5 0 wires296 := leafExcluded (by decide +kernel)

def wires297 : List Sig := [(0xffffffff, 0xfffffbf6), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires297 : Excluded 5 0 wires297 := leafExcluded (by decide +kernel)

def wires298 : List Sig := [(0x00ff8000, 0x38cd8000), (0xc0fffff8, 0xfffffbb0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires298 : Excluded 5 0 wires298 := leafExcluded (by decide +kernel)

def wires299 : List Sig := [(0x00ff8000, 0x38cd8000), (0xc0ff83f8, 0x79dd83b0), (0xc0fffff8, 0xfffffbb0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires299 : Excluded 5 0 wires299 := leafExcluded (by decide +kernel)

def wires300 : List Sig := [(0x00ff8000, 0x38cd8000), (0x00fffc00, 0xbeeff800), (0xc0fffff8, 0xfffffbb0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires300 : Excluded 5 0 wires300 := leafExcluded (by decide +kernel)

def wires301 : List Sig := [(0x00fe03c0, 0x61980300), (0x3ffe63c7, 0xe7ba6346), (0xc0fffff8, 0xfffffbb0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires301 : Excluded 5 0 wires301 := leafExcluded (by decide +kernel)

def wires302 : List Sig := [(0xffffffff, 0xbeeffcdb), (0xff0fffff, 0x8a06acdb), (0xc0fffff8, 0xfffffbb0), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires302 : Excluded 5 0 wires302 := leafExcluded (by decide +kernel)

def wires303 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xc0fffff8, 0xfffffbb0), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires303 : Excluded 5 0 wires303 := leafExcluded (by decide +kernel)

def wires304 : List Sig := [(0x00fe6000, 0xa6aa6000), (0x3ffe63c7, 0xe7ba6346), (0xc0fffff8, 0xfffffbb0), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires304 : Excluded 5 0 wires304 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires291 : Excluded 6 0 wires291 :=
  cutExcluded (k:=5) (t:=0) (v:=wires291) [] [wires292, wires293, wires294, wires295, wires296, wires297, wires298, wires299, wires300, wires301, wires302, wires303, wires304]
    True.intro
    ⟨exclude5_0_wires292, exclude5_0_wires293, exclude5_0_wires294, exclude5_0_wires295, exclude5_0_wires296, exclude5_0_wires297, exclude5_0_wires298, exclude5_0_wires299, exclude5_0_wires300, exclude5_0_wires301, exclude5_0_wires302, exclude5_0_wires303, exclude5_0_wires304, True.intro⟩
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude7_0_raw4 : Excluded 7 0 raw4 :=
  cutExcluded (k:=6) (t:=0) (v:=raw4) [] [wires0, wires17, wires32, wires47, wires61, wires76, wires90, wires101, wires118, wires132, wires148, wires162, wires178, wires198, wires213, wires221, wires238, wires249, wires263, wires277, wires291]
    True.intro
    ⟨exclude6_0_wires0, exclude6_0_wires17, exclude6_0_wires32, exclude6_0_wires47, exclude6_0_wires61, exclude6_0_wires76, exclude6_0_wires90, exclude6_0_wires101, exclude6_0_wires118, exclude6_0_wires132, exclude6_0_wires148, exclude6_0_wires162, exclude6_0_wires178, exclude6_0_wires198, exclude6_0_wires213, exclude6_0_wires221, exclude6_0_wires238, exclude6_0_wires249, exclude6_0_wires263, exclude6_0_wires277, exclude6_0_wires291, True.intro⟩
    (by decide +kernel)

def wires305 : List Sig := [(0x00f00000, 0x75f95324), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

def wires306 : List Sig := [(0x00f00000, 0x55715224), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires306 : Excluded 5 0 wires306 := leafExcluded (by decide +kernel)

def wires307 : List Sig := [(0xfff1fe3f, 0x75f9572d), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires307 : Excluded 5 0 wires307 := leafExcluded (by decide +kernel)

def wires308 : List Sig := [(0x00f00000, 0x65b84304), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires308 : Excluded 5 0 wires308 := leafExcluded (by decide +kernel)

def wires309 : List Sig := [(0x3ffe63c7, 0xf7fb7366), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires309 : Excluded 5 0 wires309 := leafExcluded (by decide +kernel)

def wires310 : List Sig := [(0x00f00000, 0x71d90320), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires310 : Excluded 5 0 wires310 := leafExcluded (by decide +kernel)

def wires311 : List Sig := [(0xc0ff83f8, 0x7dfdd3b4), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires311 : Excluded 5 0 wires311 := leafExcluded (by decide +kernel)

def wires312 : List Sig := [(0x00f00000, 0x34e95000), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires312 : Excluded 5 0 wires312 := leafExcluded (by decide +kernel)

def wires313 : List Sig := [(0x00fffc00, 0xfffffb24), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires313 : Excluded 5 0 wires313 := leafExcluded (by decide +kernel)

def wires314 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x00f00000, 0x75f95324), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires314 : Excluded 5 0 wires314 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires305 : Excluded 6 0 wires305 :=
  cutExcluded (k:=5) (t:=0) (v:=wires305) [] [wires306, wires307, wires308, wires309, wires310, wires311, wires312, wires313, wires314]
    True.intro
    ⟨exclude5_0_wires306, exclude5_0_wires307, exclude5_0_wires308, exclude5_0_wires309, exclude5_0_wires310, exclude5_0_wires311, exclude5_0_wires312, exclude5_0_wires313, exclude5_0_wires314, True.intro⟩
    (by decide +kernel)

def wires315 : List Sig := [(0x000e01c0, 0xaa8ea9d2), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

def wires316 : List Sig := [(0x000e01c0, 0x8a06a8d2), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires316 : Excluded 5 0 wires316 := leafExcluded (by decide +kernel)

def wires317 : List Sig := [(0xff0fffff, 0xaa8eaddb), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires317 : Excluded 5 0 wires317 := leafExcluded (by decide +kernel)

def wires318 : List Sig := [(0x000e01c0, 0xa28a2142), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires318 : Excluded 5 0 wires318 := leafExcluded (by decide +kernel)

def wires319 : List Sig := [(0x3ffe63c7, 0xefbeebd6), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires319 : Excluded 5 0 wires319 := leafExcluded (by decide +kernel)

def wires320 : List Sig := [(0x000e01c0, 0x288c8190), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires320 : Excluded 5 0 wires320 := leafExcluded (by decide +kernel)

def wires321 : List Sig := [(0xc0ff83f8, 0xfbdfabf2), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires321 : Excluded 5 0 wires321 := leafExcluded (by decide +kernel)

def wires322 : List Sig := [(0x000e0000, 0xaa8ea800), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires322 : Excluded 5 0 wires322 := leafExcluded (by decide +kernel)

def wires323 : List Sig := [(0x00fffdc0, 0xbeeff9d2), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires323 : Excluded 5 0 wires323 := leafExcluded (by decide +kernel)

def wires324 : List Sig := [(0x00fffdc0, 0xbeeff9d2), (0x000e01c0, 0xaa8ea9d2), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires324 : Excluded 5 0 wires324 := leafExcluded (by decide +kernel)

def wires325 : List Sig := [(0x00fffdc0, 0xbeeff9d2), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires325 : Excluded 5 0 wires325 := leafExcluded (by decide +kernel)

def wires326 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x000e01c0, 0xaa8ea9d2), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires326 : Excluded 5 0 wires326 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires315 : Excluded 6 0 wires315 :=
  cutExcluded (k:=5) (t:=0) (v:=wires315) [] [wires316, wires317, wires318, wires319, wires320, wires321, wires322, wires323, wires324, wires325, wires326]
    True.intro
    ⟨exclude5_0_wires316, exclude5_0_wires317, exclude5_0_wires318, exclude5_0_wires319, exclude5_0_wires320, exclude5_0_wires321, exclude5_0_wires322, exclude5_0_wires323, exclude5_0_wires324, exclude5_0_wires325, exclude5_0_wires326, True.intro⟩
    (by decide +kernel)

def wires327 : List Sig := [(0xc0019c38, 0x18459cb9), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

def wires328 : List Sig := [(0xc0019c38, 0x08048c99), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires328 : Excluded 5 0 wires328 := leafExcluded (by decide +kernel)

def wires329 : List Sig := [(0xff0fffff, 0x9a47bcfb), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires329 : Excluded 5 0 wires329 := leafExcluded (by decide +kernel)

def wires330 : List Sig := [(0xc0019c38, 0x10411429), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires330 : Excluded 5 0 wires330 := leafExcluded (by decide +kernel)

def wires331 : List Sig := [(0xfff1fe3f, 0x5d75debd), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires331 : Excluded 5 0 wires331 := leafExcluded (by decide +kernel)

def wires332 : List Sig := [(0xc0018038, 0x184580b0), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires332 : Excluded 5 0 wires332 := leafExcluded (by decide +kernel)

def wires333 : List Sig := [(0xc0ff9ff8, 0x79dd9fb9), (0xc0ff83f8, 0x79dd83b0), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires333 : Excluded 5 0 wires333 := leafExcluded (by decide +kernel)

def wires334 : List Sig := [(0x00019c00, 0x18459800), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires334 : Excluded 5 0 wires334 := leafExcluded (by decide +kernel)

def wires335 : List Sig := [(0xc0fffc38, 0xbeeffcb9), (0x00fffc00, 0xbeeff800), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires335 : Excluded 5 0 wires335 := leafExcluded (by decide +kernel)

def wires336 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xc0019c38, 0x18459cb9), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires336 : Excluded 5 0 wires336 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires327 : Excluded 6 0 wires327 :=
  cutExcluded (k:=5) (t:=0) (v:=wires327) [] [wires328, wires329, wires330, wires331, wires332, wires333, wires334, wires335, wires336]
    True.intro
    ⟨exclude5_0_wires328, exclude5_0_wires329, exclude5_0_wires330, exclude5_0_wires331, exclude5_0_wires332, exclude5_0_wires333, exclude5_0_wires334, exclude5_0_wires335, exclude5_0_wires336, True.intro⟩
    (by decide +kernel)

def wires337 : List Sig := [(0x3f007c07, 0x86227c4f), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

def wires338 : List Sig := [(0x3f007c07, 0x82022c4b), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires338 : Excluded 5 0 wires338 := leafExcluded (by decide +kernel)

def wires339 : List Sig := [(0xff0fffff, 0x8e26fcdf), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires339 : Excluded 5 0 wires339 := leafExcluded (by decide +kernel)

def wires340 : List Sig := [(0x3f007c07, 0x0420540d), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires340 : Excluded 5 0 wires340 := leafExcluded (by decide +kernel)

def wires341 : List Sig := [(0xfff1fe3f, 0xd7737e6f), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires341 : Excluded 5 0 wires341 := leafExcluded (by decide +kernel)

def wires342 : List Sig := [(0x3f006007, 0x86226046), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires342 : Excluded 5 0 wires342 := leafExcluded (by decide +kernel)

def wires343 : List Sig := [(0x3ffe7fc7, 0xe7ba7f4f), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires343 : Excluded 5 0 wires343 := leafExcluded (by decide +kernel)

def wires344 : List Sig := [(0x00007c00, 0x86227800), (0x00fffc00, 0xbeeff800), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires344 : Excluded 5 0 wires344 := leafExcluded (by decide +kernel)

def wires345 : List Sig := [(0x3ffffc07, 0xbeeffc4f), (0x00fffc00, 0xbeeff800), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires345 : Excluded 5 0 wires345 := leafExcluded (by decide +kernel)

def wires346 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x3f007c07, 0x86227c4f), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires346 : Excluded 5 0 wires346 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires337 : Excluded 6 0 wires337 :=
  cutExcluded (k:=5) (t:=0) (v:=wires337) [] [wires338, wires339, wires340, wires341, wires342, wires343, wires344, wires345, wires346]
    True.intro
    ⟨exclude5_0_wires338, exclude5_0_wires339, exclude5_0_wires340, exclude5_0_wires341, exclude5_0_wires342, exclude5_0_wires343, exclude5_0_wires344, exclude5_0_wires345, exclude5_0_wires346, True.intro⟩
    (by decide +kernel)

def wires347 : List Sig := [(0xff0003ff, 0x411007ff), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

def wires348 : List Sig := [(0xff0003ff, 0x000004db), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires348 : Excluded 5 0 wires348 := leafExcluded (by decide +kernel)

def wires349 : List Sig := [(0xff0fffff, 0xcb16afff), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires349 : Excluded 5 0 wires349 := leafExcluded (by decide +kernel)

def wires350 : List Sig := [(0xff00023f, 0x4110062d), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires350 : Excluded 5 0 wires350 := leafExcluded (by decide +kernel)

def wires351 : List Sig := [(0xfff1ffff, 0x557157ff), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires351 : Excluded 5 0 wires351 := leafExcluded (by decide +kernel)

def wires352 : List Sig := [(0x3f0003c7, 0x41100346), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires352 : Excluded 5 0 wires352 := leafExcluded (by decide +kernel)

def wires353 : List Sig := [(0xfffe63ff, 0xe7ba67ff), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires353 : Excluded 5 0 wires353 := leafExcluded (by decide +kernel)

def wires354 : List Sig := [(0xc00003f8, 0x411003b0), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires354 : Excluded 5 0 wires354 := leafExcluded (by decide +kernel)

def wires355 : List Sig := [(0xffff83ff, 0x79dd87ff), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires355 : Excluded 5 0 wires355 := leafExcluded (by decide +kernel)

def wires356 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0003ff, 0x411007ff), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires356 : Excluded 5 0 wires356 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_0_wires347 : Excluded 6 0 wires347 :=
  cutExcluded (k:=5) (t:=0) (v:=wires347) [] [wires348, wires349, wires350, wires351, wires352, wires353, wires354, wires355, wires356]
    True.intro
    ⟨exclude5_0_wires348, exclude5_0_wires349, exclude5_0_wires350, exclude5_0_wires351, exclude5_0_wires352, exclude5_0_wires353, exclude5_0_wires354, exclude5_0_wires355, exclude5_0_wires356, True.intro⟩
    (by decide +kernel)

def wires357 : List Sig := [(0x00fe01c0, 0xfffffbf6), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires357 : Excluded 5 0 wires357 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires7 : Excluded 5 1 wires7 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires14 : Excluded 5 1 wires14 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires0 : Excluded 6 1 wires0 :=
  cutExcluded (k:=5) (t:=1) (v:=wires0) [wires357] [wires7, wires14]
    ⟨exclude5_0_wires357, True.intro⟩
    ⟨exclude5_1_wires7, exclude5_1_wires14, True.intro⟩
    (by decide +kernel)

def wires358 : List Sig := [(0x00000000, 0x20880100), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires358 : Excluded 5 0 wires358 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires18 : Excluded 5 1 wires18 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires21 : Excluded 5 1 wires21 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires24 : Excluded 5 1 wires24 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires28 : Excluded 5 1 wires28 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires17 : Excluded 6 1 wires17 :=
  cutExcluded (k:=5) (t:=1) (v:=wires17) [wires358] [wires18, wires21, wires24, wires28]
    ⟨exclude5_0_wires358, True.intro⟩
    ⟨exclude5_1_wires18, exclude5_1_wires21, exclude5_1_wires24, exclude5_1_wires28, True.intro⟩
    (by decide +kernel)

def wires359 : List Sig := [(0xc0f19c38, 0x7dfddfbd), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires359 : Excluded 5 0 wires359 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires38 : Excluded 5 1 wires38 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires32 : Excluded 6 1 wires32 :=
  cutExcluded (k:=5) (t:=1) (v:=wires32) [wires359] [wires38]
    ⟨exclude5_0_wires359, True.intro⟩
    ⟨exclude5_1_wires38, True.intro⟩
    (by decide +kernel)

def wires360 : List Sig := [(0x00000000, 0x10411020), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires360 : Excluded 5 0 wires360 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires48 : Excluded 5 1 wires48 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires51 : Excluded 5 1 wires51 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires55 : Excluded 5 1 wires55 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires47 : Excluded 6 1 wires47 :=
  cutExcluded (k:=5) (t:=1) (v:=wires47) [wires360] [wires48, wires51, wires55]
    ⟨exclude5_0_wires360, True.intro⟩
    ⟨exclude5_1_wires48, exclude5_1_wires51, exclude5_1_wires55, True.intro⟩
    (by decide +kernel)

def wires361 : List Sig := [(0x3ff07c07, 0xf7fb7f6f), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires361 : Excluded 5 0 wires361 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires67 : Excluded 5 1 wires67 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires61 : Excluded 6 1 wires61 :=
  cutExcluded (k:=5) (t:=1) (v:=wires61) [wires361] [wires67]
    ⟨exclude5_0_wires361, True.intro⟩
    ⟨exclude5_1_wires67, True.intro⟩
    (by decide +kernel)

def wires362 : List Sig := [(0x00000000, 0x04205004), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires362 : Excluded 5 0 wires362 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires77 : Excluded 5 1 wires77 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires80 : Excluded 5 1 wires80 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires84 : Excluded 5 1 wires84 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires76 : Excluded 6 1 wires76 :=
  cutExcluded (k:=5) (t:=1) (v:=wires76) [wires362] [wires77, wires80, wires84]
    ⟨exclude5_0_wires362, True.intro⟩
    ⟨exclude5_1_wires77, exclude5_1_wires80, exclude5_1_wires84, True.intro⟩
    (by decide +kernel)

def wires363 : List Sig := [(0xfff003ff, 0x75f957ff), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires363 : Excluded 5 0 wires363 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires90 : Excluded 6 1 wires90 :=
  cutExcluded (k:=5) (t:=1) (v:=wires90) [wires363] []
    ⟨exclude5_0_wires363, True.intro⟩
    True.intro
    (by decide +kernel)

def wires364 : List Sig := [(0x00000000, 0x41100324), (0xff0fffff, 0x8a06acdb), (0x00fffc00, 0xbeeff800), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires364 : Excluded 5 0 wires364 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires102 : Excluded 5 1 wires102 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires106 : Excluded 5 1 wires106 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires110 : Excluded 5 1 wires110 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires101 : Excluded 6 1 wires101 :=
  cutExcluded (k:=5) (t:=1) (v:=wires101) [wires364] [wires102, wires106, wires110]
    ⟨exclude5_0_wires364, True.intro⟩
    ⟨exclude5_1_wires102, exclude5_1_wires106, exclude5_1_wires110, True.intro⟩
    (by decide +kernel)

def wires365 : List Sig := [(0xc00f9df8, 0xbacfbdfb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires365 : Excluded 5 0 wires365 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires125 : Excluded 5 1 wires125 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires118 : Excluded 6 1 wires118 :=
  cutExcluded (k:=5) (t:=1) (v:=wires118) [wires365] [wires125]
    ⟨exclude5_0_wires365, True.intro⟩
    ⟨exclude5_1_wires125, True.intro⟩
    (by decide +kernel)

def wires366 : List Sig := [(0x00000000, 0x08048890), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires366 : Excluded 5 0 wires366 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires133 : Excluded 5 1 wires133 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires136 : Excluded 5 1 wires136 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires140 : Excluded 5 1 wires140 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires144 : Excluded 5 1 wires144 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires132 : Excluded 6 1 wires132 :=
  cutExcluded (k:=5) (t:=1) (v:=wires132) [wires366] [wires133, wires136, wires140, wires144]
    ⟨exclude5_0_wires366, True.intro⟩
    ⟨exclude5_1_wires133, exclude5_1_wires136, exclude5_1_wires140, exclude5_1_wires144, True.intro⟩
    (by decide +kernel)

def wires367 : List Sig := [(0x3f0e7dc7, 0xaeaefddf), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires367 : Excluded 5 0 wires367 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires155 : Excluded 5 1 wires155 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires148 : Excluded 6 1 wires148 :=
  cutExcluded (k:=5) (t:=1) (v:=wires148) [wires367] [wires155]
    ⟨exclude5_0_wires367, True.intro⟩
    ⟨exclude5_1_wires155, True.intro⟩
    (by decide +kernel)

def wires368 : List Sig := [(0x00000000, 0x82022842), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires368 : Excluded 5 0 wires368 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires163 : Excluded 5 1 wires163 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires166 : Excluded 5 1 wires166 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires170 : Excluded 5 1 wires170 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires174 : Excluded 5 1 wires174 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires162 : Excluded 6 1 wires162 :=
  cutExcluded (k:=5) (t:=1) (v:=wires162) [wires368] [wires163, wires166, wires170, wires174]
    ⟨exclude5_0_wires368, True.intro⟩
    ⟨exclude5_1_wires163, exclude5_1_wires166, exclude5_1_wires170, exclude5_1_wires174, True.intro⟩
    (by decide +kernel)

def wires369 : List Sig := [(0xff0e03ff, 0xeb9eafff), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires369 : Excluded 5 0 wires369 := leafExcluded (by decide +kernel)

def wires370 : List Sig := [(0x000e01c0, 0xaa8ea9d2), (0xfff1fe3f, 0x5571562d), (0x00f1fc00, 0x14615000), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires370 : Excluded 5 0 wires370 := leafExcluded (by decide +kernel)

def wires371 : List Sig := [(0x00f00000, 0x75f95324), (0xff0fffff, 0x8a06acdb), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires371 : Excluded 5 0 wires371 := leafExcluded (by decide +kernel)

def wires372 : List Sig := [(0xc0019c38, 0x18459cb9), (0x3ffe63c7, 0xe7ba6346), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires372 : Excluded 5 0 wires372 := leafExcluded (by decide +kernel)

def wires373 : List Sig := [(0x3f007c07, 0x86227c4f), (0xc0ff83f8, 0x79dd83b0), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires373 : Excluded 5 0 wires373 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires185 : Excluded 5 1 wires185 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires178 : Excluded 6 1 wires178 :=
  cutExcluded (k:=5) (t:=1) (v:=wires178) [wires369, wires370, wires371, wires372, wires373] [wires185]
    ⟨exclude5_0_wires369, exclude5_0_wires370, exclude5_0_wires371, exclude5_0_wires372, exclude5_0_wires373, True.intro⟩
    ⟨exclude5_1_wires185, True.intro⟩
    (by decide +kernel)

def wires374 : List Sig := [(0xff0e03ff, 0xeb9eafff), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires374 : Excluded 5 0 wires374 := leafExcluded (by decide +kernel)

def wires375 : List Sig := [(0xff0003ff, 0x411007ff), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires375 : Excluded 5 0 wires375 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires198 : Excluded 6 1 wires198 :=
  cutExcluded (k:=5) (t:=1) (v:=wires198) [wires374, wires375] []
    ⟨exclude5_0_wires374, exclude5_0_wires375, True.intro⟩
    True.intro
    (by decide +kernel)

def wires376 : List Sig := [(0x000001c0, 0x000001d2), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires376 : Excluded 5 0 wires376 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires213 : Excluded 6 1 wires213 :=
  cutExcluded (k:=5) (t:=1) (v:=wires213) [wires376] []
    ⟨exclude5_0_wires376, True.intro⟩
    True.intro
    (by decide +kernel)

def wires377 : List Sig := [(0xff01fc3f, 0x9e67fcff), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires377 : Excluded 5 0 wires377 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires228 : Excluded 5 1 wires228 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires221 : Excluded 6 1 wires221 :=
  cutExcluded (k:=5) (t:=1) (v:=wires221) [wires377] [wires228]
    ⟨exclude5_0_wires377, True.intro⟩
    ⟨exclude5_1_wires228, True.intro⟩
    (by decide +kernel)

def wires378 : List Sig := [(0x00001c00, 0x00001c09), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires378 : Excluded 5 0 wires378 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires245 : Excluded 5 1 wires245 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires238 : Excluded 6 1 wires238 :=
  cutExcluded (k:=5) (t:=1) (v:=wires238) [wires378] [wires245]
    ⟨exclude5_0_wires378, True.intro⟩
    ⟨exclude5_1_wires245, True.intro⟩
    (by decide +kernel)

def wires379 : List Sig := [(0xff019fff, 0x59559fff), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires379 : Excluded 5 0 wires379 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires256 : Excluded 5 1 wires256 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires249 : Excluded 6 1 wires249 :=
  cutExcluded (k:=5) (t:=1) (v:=wires249) [wires379] [wires256]
    ⟨exclude5_0_wires379, True.intro⟩
    ⟨exclude5_1_wires256, True.intro⟩
    (by decide +kernel)

def wires380 : List Sig := [(0xc0000038, 0x000004b9), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires380 : Excluded 5 0 wires380 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires270 : Excluded 5 1 wires270 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires263 : Excluded 6 1 wires263 :=
  cutExcluded (k:=5) (t:=1) (v:=wires263) [wires380] [wires270]
    ⟨exclude5_0_wires380, True.intro⟩
    ⟨exclude5_1_wires270, True.intro⟩
    (by decide +kernel)

def wires381 : List Sig := [(0xff007fff, 0xc7327fff), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires381 : Excluded 5 0 wires381 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires284 : Excluded 5 1 wires284 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires277 : Excluded 6 1 wires277 :=
  cutExcluded (k:=5) (t:=1) (v:=wires277) [wires381] [wires284]
    ⟨exclude5_0_wires381, True.intro⟩
    ⟨exclude5_1_wires284, True.intro⟩
    (by decide +kernel)

def wires382 : List Sig := [(0x3f000007, 0x0000044f), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires382 : Excluded 5 0 wires382 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires298 : Excluded 5 1 wires298 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires291 : Excluded 6 1 wires291 :=
  cutExcluded (k:=5) (t:=1) (v:=wires291) [wires382] [wires298]
    ⟨exclude5_0_wires382, True.intro⟩
    ⟨exclude5_1_wires298, True.intro⟩
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude7_1_raw4 : Excluded 7 1 raw4 :=
  cutExcluded (k:=6) (t:=1) (v:=raw4) [wires305, wires315, wires327, wires337, wires347] [wires0, wires17, wires32, wires47, wires61, wires76, wires90, wires101, wires118, wires132, wires148, wires162, wires178, wires198, wires213, wires221, wires238, wires249, wires263, wires277, wires291]
    ⟨exclude6_0_wires305, exclude6_0_wires315, exclude6_0_wires327, exclude6_0_wires337, exclude6_0_wires347, True.intro⟩
    ⟨exclude6_1_wires0, exclude6_1_wires17, exclude6_1_wires32, exclude6_1_wires47, exclude6_1_wires61, exclude6_1_wires76, exclude6_1_wires90, exclude6_1_wires101, exclude6_1_wires118, exclude6_1_wires132, exclude6_1_wires148, exclude6_1_wires162, exclude6_1_wires178, exclude6_1_wires198, exclude6_1_wires213, exclude6_1_wires221, exclude6_1_wires238, exclude6_1_wires249, exclude6_1_wires263, exclude6_1_wires277, exclude6_1_wires291, True.intro⟩
    (by decide +kernel)

def wires383 : List Sig := [(0x00f00000, 0x75f95324), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_raw4 : Excluded 5 0 raw4 := leafExcluded (by decide +kernel)

def wires384 : List Sig := [(0xff0fffff, 0x8a06acdb), (0x00f00000, 0x75f95324), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires384 : Excluded 5 0 wires384 := leafExcluded (by decide +kernel)

def wires385 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x00f00000, 0x75f95324), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires385 : Excluded 5 1 wires385 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires383 : Excluded 6 1 wires383 :=
  cutExcluded (k:=5) (t:=1) (v:=wires383) [raw4, wires384] [wires385]
    ⟨exclude5_0_raw4, exclude5_0_wires384, True.intro⟩
    ⟨exclude5_1_wires385, True.intro⟩
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires305 : Excluded 6 1 wires305 :=
  cutExcluded (k:=5) (t:=1) (v:=wires305) [] []
    True.intro
    True.intro
    (by decide +kernel)

def wires386 : List Sig := [(0x000e01c0, 0xaa8ea9d2), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

def wires387 : List Sig := [(0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires387 : Excluded 5 0 wires387 := leafExcluded (by decide +kernel)

def wires388 : List Sig := [(0xfff1fe3f, 0x5571562d), (0x000e01c0, 0xaa8ea9d2), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires388 : Excluded 5 0 wires388 := leafExcluded (by decide +kernel)

def wires389 : List Sig := [(0x00fffdc0, 0xbeeff9d2), (0x000e01c0, 0xaa8ea9d2), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires389 : Excluded 5 1 wires389 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires386 : Excluded 6 1 wires386 :=
  cutExcluded (k:=5) (t:=1) (v:=wires386) [wires387, wires388] [wires389]
    ⟨exclude5_0_wires387, exclude5_0_wires388, True.intro⟩
    ⟨exclude5_1_wires389, True.intro⟩
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires323 : Excluded 5 1 wires323 := leafExcluded (by decide +kernel)

def wires390 : List Sig := [(0x00f1fc00, 0x14615000), (0x000e01c0, 0xaa8ea9d2), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires390 : Excluded 5 1 wires390 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires315 : Excluded 6 1 wires315 :=
  cutExcluded (k:=5) (t:=1) (v:=wires315) [] [wires323, wires390]
    True.intro
    ⟨exclude5_1_wires323, exclude5_1_wires390, True.intro⟩
    (by decide +kernel)

def wires391 : List Sig := [(0xc0019c38, 0x18459cb9), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

def wires392 : List Sig := [(0x3ffe63c7, 0xe7ba6346), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires392 : Excluded 5 0 wires392 := leafExcluded (by decide +kernel)

def wires393 : List Sig := [(0x3ffe63c7, 0xe7ba6346), (0xc0019c38, 0x18459cb9), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires393 : Excluded 5 0 wires393 := leafExcluded (by decide +kernel)

def wires394 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xc0019c38, 0x18459cb9), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires394 : Excluded 5 1 wires394 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires391 : Excluded 6 1 wires391 :=
  cutExcluded (k:=5) (t:=1) (v:=wires391) [wires392, wires393] [wires394]
    ⟨exclude5_0_wires392, exclude5_0_wires393, True.intro⟩
    ⟨exclude5_1_wires394, True.intro⟩
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires327 : Excluded 6 1 wires327 :=
  cutExcluded (k:=5) (t:=1) (v:=wires327) [] []
    True.intro
    True.intro
    (by decide +kernel)

def wires395 : List Sig := [(0x3f007c07, 0x86227c4f), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

def wires396 : List Sig := [(0xc0ff83f8, 0x79dd83b0), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires396 : Excluded 5 0 wires396 := leafExcluded (by decide +kernel)

def wires397 : List Sig := [(0xc0ff83f8, 0x79dd83b0), (0x3f007c07, 0x86227c4f), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires397 : Excluded 5 0 wires397 := leafExcluded (by decide +kernel)

def wires398 : List Sig := [(0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x3f007c07, 0x86227c4f), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires398 : Excluded 5 1 wires398 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires395 : Excluded 6 1 wires395 :=
  cutExcluded (k:=5) (t:=1) (v:=wires395) [wires396, wires397] [wires398]
    ⟨exclude5_0_wires396, exclude5_0_wires397, True.intro⟩
    ⟨exclude5_1_wires398, True.intro⟩
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires337 : Excluded 6 1 wires337 :=
  cutExcluded (k:=5) (t:=1) (v:=wires337) [] []
    True.intro
    True.intro
    (by decide +kernel)

def wires399 : List Sig := [(0xff0003ff, 0x411007ff), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

def wires400 : List Sig := [(0x00fffc00, 0xbeeff800), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires400 : Excluded 5 0 wires400 := leafExcluded (by decide +kernel)

def wires401 : List Sig := [(0x00fffc00, 0xbeeff800), (0xff0003ff, 0x411007ff), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_0_wires401 : Excluded 5 0 wires401 := leafExcluded (by decide +kernel)

def wires402 : List Sig := [(0xff00023f, 0x4110062d), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires402 : Excluded 5 1 wires402 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires399 : Excluded 6 1 wires399 :=
  cutExcluded (k:=5) (t:=1) (v:=wires399) [wires400, wires401] [wires402]
    ⟨exclude5_0_wires400, exclude5_0_wires401, True.intro⟩
    ⟨exclude5_1_wires402, True.intro⟩
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_1_wires347 : Excluded 6 1 wires347 :=
  cutExcluded (k:=5) (t:=1) (v:=wires347) [] []
    True.intro
    True.intro
    (by decide +kernel)

def wires403 : List Sig := [(0xff0e03ff, 0xeb9eafff), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires403 : Excluded 5 1 wires403 := leafExcluded (by decide +kernel)

def wires404 : List Sig := [(0x000e01c0, 0xaa8ea9d2), (0x00f1fc00, 0x14615000), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires404 : Excluded 5 1 wires404 := leafExcluded (by decide +kernel)

def wires405 : List Sig := [(0x00f00000, 0x75f95324), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires405 : Excluded 5 1 wires405 := leafExcluded (by decide +kernel)

def wires406 : List Sig := [(0xc0019c38, 0x18459cb9), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires406 : Excluded 5 1 wires406 := leafExcluded (by decide +kernel)

def wires407 : List Sig := [(0x3f007c07, 0x86227c4f), (0x00f1fc00, 0x14615000), (0xfff1fe3f, 0x5571562d), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires407 : Excluded 5 1 wires407 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_2_wires178 : Excluded 6 2 wires178 :=
  cutExcluded (k:=5) (t:=2) (v:=wires178) [wires403, wires404, wires405, wires406, wires407] []
    ⟨exclude5_1_wires403, exclude5_1_wires404, exclude5_1_wires405, exclude5_1_wires406, exclude5_1_wires407, True.intro⟩
    True.intro
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude7_2_raw4 : Excluded 7 2 raw4 :=
  cutExcluded (k:=6) (t:=2) (v:=raw4) [wires383, wires305, wires386, wires315, wires391, wires327, wires395, wires337, wires399, wires347] [wires178]
    ⟨exclude6_1_wires383, exclude6_1_wires305, exclude6_1_wires386, exclude6_1_wires315, exclude6_1_wires391, exclude6_1_wires327, exclude6_1_wires395, exclude6_1_wires337, exclude6_1_wires399, exclude6_1_wires347, True.intro⟩
    ⟨exclude6_2_wires178, True.intro⟩
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_raw4 : Excluded 5 1 raw4 := leafExcluded (by decide +kernel)

def wires408 : List Sig := [(0x000e01c0, 0xaa8ea9d2), (0x00f00000, 0x75f95324), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires408 : Excluded 5 1 wires408 := leafExcluded (by decide +kernel)

def wires409 : List Sig := [(0xc0019c38, 0x18459cb9), (0x00f00000, 0x75f95324), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires409 : Excluded 5 1 wires409 := leafExcluded (by decide +kernel)

def wires410 : List Sig := [(0x3f007c07, 0x86227c4f), (0x00f00000, 0x75f95324), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires410 : Excluded 5 1 wires410 := leafExcluded (by decide +kernel)

def wires411 : List Sig := [(0xff0003ff, 0x411007ff), (0x00f00000, 0x75f95324), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires411 : Excluded 5 1 wires411 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_2_wires383 : Excluded 6 2 wires383 :=
  cutExcluded (k:=5) (t:=2) (v:=wires383) [raw4, wires408, wires409, wires410, wires411] []
    ⟨exclude5_1_raw4, exclude5_1_wires408, exclude5_1_wires409, exclude5_1_wires410, exclude5_1_wires411, True.intro⟩
    True.intro
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires387 : Excluded 5 1 wires387 := leafExcluded (by decide +kernel)

def wires412 : List Sig := [(0x00f00000, 0x75f95324), (0x000e01c0, 0xaa8ea9d2), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires412 : Excluded 5 1 wires412 := leafExcluded (by decide +kernel)

def wires413 : List Sig := [(0xc0019c38, 0x18459cb9), (0x000e01c0, 0xaa8ea9d2), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires413 : Excluded 5 1 wires413 := leafExcluded (by decide +kernel)

def wires414 : List Sig := [(0x3f007c07, 0x86227c4f), (0x000e01c0, 0xaa8ea9d2), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires414 : Excluded 5 1 wires414 := leafExcluded (by decide +kernel)

def wires415 : List Sig := [(0xff0003ff, 0x411007ff), (0x000e01c0, 0xaa8ea9d2), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires415 : Excluded 5 1 wires415 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_2_wires386 : Excluded 6 2 wires386 :=
  cutExcluded (k:=5) (t:=2) (v:=wires386) [wires387, wires412, wires413, wires414, wires415] []
    ⟨exclude5_1_wires387, exclude5_1_wires412, exclude5_1_wires413, exclude5_1_wires414, exclude5_1_wires415, True.intro⟩
    True.intro
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires392 : Excluded 5 1 wires392 := leafExcluded (by decide +kernel)

def wires416 : List Sig := [(0x00f00000, 0x75f95324), (0xc0019c38, 0x18459cb9), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires416 : Excluded 5 1 wires416 := leafExcluded (by decide +kernel)

def wires417 : List Sig := [(0x000e01c0, 0xaa8ea9d2), (0xc0019c38, 0x18459cb9), (0xff0fffff, 0x8a06acdb), (0xc0ff83f8, 0x79dd83b0), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires417 : Excluded 5 1 wires417 := leafExcluded (by decide +kernel)

def wires418 : List Sig := [(0x3f007c07, 0x86227c4f), (0xc0019c38, 0x18459cb9), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires418 : Excluded 5 1 wires418 := leafExcluded (by decide +kernel)

def wires419 : List Sig := [(0xff0003ff, 0x411007ff), (0xc0019c38, 0x18459cb9), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires419 : Excluded 5 1 wires419 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_2_wires391 : Excluded 6 2 wires391 :=
  cutExcluded (k:=5) (t:=2) (v:=wires391) [wires392, wires416, wires417, wires418, wires419] []
    ⟨exclude5_1_wires392, exclude5_1_wires416, exclude5_1_wires417, exclude5_1_wires418, exclude5_1_wires419, True.intro⟩
    True.intro
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires396 : Excluded 5 1 wires396 := leafExcluded (by decide +kernel)

def wires420 : List Sig := [(0x00f00000, 0x75f95324), (0x3f007c07, 0x86227c4f), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires420 : Excluded 5 1 wires420 := leafExcluded (by decide +kernel)

def wires421 : List Sig := [(0x000e01c0, 0xaa8ea9d2), (0x3f007c07, 0x86227c4f), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires421 : Excluded 5 1 wires421 := leafExcluded (by decide +kernel)

def wires422 : List Sig := [(0xc0019c38, 0x18459cb9), (0x3f007c07, 0x86227c4f), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x00fffc00, 0xbeeff800)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires422 : Excluded 5 1 wires422 := leafExcluded (by decide +kernel)

def wires423 : List Sig := [(0xff0003ff, 0x411007ff), (0x3f007c07, 0x86227c4f), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires423 : Excluded 5 1 wires423 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_2_wires395 : Excluded 6 2 wires395 :=
  cutExcluded (k:=5) (t:=2) (v:=wires395) [wires396, wires420, wires421, wires422, wires423] []
    ⟨exclude5_1_wires396, exclude5_1_wires420, exclude5_1_wires421, exclude5_1_wires422, exclude5_1_wires423, True.intro⟩
    True.intro
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires400 : Excluded 5 1 wires400 := leafExcluded (by decide +kernel)

def wires424 : List Sig := [(0x00f00000, 0x75f95324), (0xff0003ff, 0x411007ff), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires424 : Excluded 5 1 wires424 := leafExcluded (by decide +kernel)

def wires425 : List Sig := [(0x000e01c0, 0xaa8ea9d2), (0xff0003ff, 0x411007ff), (0xff0fffff, 0x8a06acdb), (0x3ffe63c7, 0xe7ba6346), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires425 : Excluded 5 1 wires425 := leafExcluded (by decide +kernel)

def wires426 : List Sig := [(0xc0019c38, 0x18459cb9), (0xff0003ff, 0x411007ff), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0xc0ff83f8, 0x79dd83b0)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires426 : Excluded 5 1 wires426 := leafExcluded (by decide +kernel)

def wires427 : List Sig := [(0x3f007c07, 0x86227c4f), (0xff0003ff, 0x411007ff), (0xff0fffff, 0x8a06acdb), (0xfff1fe3f, 0x5571562d), (0x3ffe63c7, 0xe7ba6346)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude5_1_wires427 : Excluded 5 1 wires427 := leafExcluded (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude6_2_wires399 : Excluded 6 2 wires399 :=
  cutExcluded (k:=5) (t:=2) (v:=wires399) [wires400, wires424, wires425, wires426, wires427] []
    ⟨exclude5_1_wires400, exclude5_1_wires424, exclude5_1_wires425, exclude5_1_wires426, exclude5_1_wires427, True.intro⟩
    True.intro
    (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma exclude7_3_raw4 : Excluded 7 3 raw4 :=
  cutExcluded (k:=6) (t:=3) (v:=raw4) [wires383, wires386, wires391, wires395, wires399] []
    ⟨exclude6_2_wires383, exclude6_2_wires386, exclude6_2_wires391, exclude6_2_wires395, exclude6_2_wires399, True.intro⟩
    True.intro
    (by decide +kernel)
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem minimum (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (correct : ∀ x,C.eval (List.ofFn x)=evalT 0xe888a880 x) : 7<C.gates.length := by
  apply cost 0xe888a880 raw4 7 rfl (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) _ C legal correct
  intro t
  fin_cases t <;> first | exact exclude7_0_raw4 | exact exclude7_1_raw4 | exact exclude7_2_raw4 | exact exclude7_3_raw4

def eightGateCircuit : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [10, 11]⟩],12⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
lemma eightGateCircuit_ok : ∀ x : Fin 5 → Bool,eightGateCircuit.eval (List.ofFn x)=evalT 0xe888a880 x := by decide +kernel
end PEqualNP.Outside.L_meta_8634_aux
open PEqualNP.Outside.L_meta_8634_aux
theorem PEqualNP.Outside.L_meta_8634 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xe888a880 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xe888a880 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C,legal,size,correct⟩
  have lower := minimum C legal correct
  refine ⟨eightGateCircuit,?_,?_,eightGateCircuit_ok⟩
  · simp [eightGateCircuit,PEqualNP.MetaComplexity.Monotone2]
  · change C.gates.length ≤ s at size
    change 8 ≤ s
    omega
