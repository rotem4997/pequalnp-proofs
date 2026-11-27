import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs

-- The seven-vertex test follows Vkuparin's L-meta-1419, ljste's PR 2918
-- and jfsantoropereira's L-meta-1007. The circuit and paired rows are for the posted graph.
-- With no NOT gate the original circuit already works. If a circuit with a NOT gate
-- had at most ten entries, its live operations would have at most nine binary gates.
-- Test those operations on 256 paired positive and negative input rows.
namespace PEqualNP.Outside.L_meta_10852_aux

abbrev B := BitVec 256
abbrev Sig := B × B
def top : B := BitVec.allOnes 256
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
  by_cases hi : i < 256
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 256
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 256 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 256)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 256) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 256 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 256)] <;> simp [hi]
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
  (allow = false ∧ ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

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
  exact Or.inr (Or.inr ⟨rfl,d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

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
    ∃ k' t' S', k' + t + flag.toNat ≤ k+1+t' ∧ t' ≤ t+flag.toNat ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by cases flag <;> simp <;> omega,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨flagOn,a,ha,hp',eq⟩ | ⟨flagOff,d,a,b,ha,hb,pa,pb,hab,eq⟩)
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
        exact ⟨_,_,_,by simp [flagOn] <;> omega,by simp [flagOn],Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
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
        exact ⟨_,_,_,by simp [flagOff] <;> omega,by omega,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by cases flag <;> simp <;> omega,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k + gs.countP (fun g => isNot g.op) ≤ gs.length + t ∧ t ≤ gs.countP (fun g => isNot g.op) ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,hcount,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hcnt,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    refine ⟨l,u,T,?_,?_,hu,hT⟩ <;>
      cases hf : isNot g.op <;> simp [List.countP_cons,hf] at hl hcnt ⊢ <;> omega

def bit (side : Bool) (i : Fin 256) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 256).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
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


def evalT (T : ℕ) (x : Fin 7 → Bool) := Nat.testBit T (∑ i : Fin 7, if x i then 2 ^ (i : ℕ) else 0)
def sample (raw : List Sig) (s : Bool) (i : Fin 256) (j : Fin 7) := bit s i (raw.getD j.val zero)
private lemma sample_list (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 7 => raw.getD j.val zero) = raw) (s i) : List.ofFn (sample raw s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 7 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (T : ℕ) (raw : List Sig) (raw_id : List.ofFn (fun j : Fin 7 => raw.getD j.val zero) = raw)
    (sample_ok : ∀ s i, evalT T (sample raw s i) = s) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = evalT T x) : target ∈ execute C.gates raw := by
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

lemma reduced_step {m t S : Nat} {s : Finset Sig} {v : List Sig} {u b : List Sig → Bool}
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


lemma notCount (gs : List Gate)
    (single : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j) :
    gs.countP (fun g => isNot g.op) ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have rest : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j := by
      intro i j hi hj
      exact Fin.succ_inj.mp (single i.succ j.succ hi hj)
    by_cases hg : g.op = .not
    · have z : gs.countP (fun h => isNot h.op) = 0 := by
        apply List.countP_eq_zero.mpr
        intro a ha
        obtain ⟨i,hi⟩ := List.mem_iff_get.mp ha
        intro h
        have hiNot : (gs.get i).op = .not := by rw [hi]; exact (isNot_iff _).mp h
        have eqn := single (0 : Fin (g::gs).length) i.succ hg hiNot
        exact Fin.succ_ne_zero i eqn.symm
      have hf : isNot g.op = true := (isNot_iff _).mpr hg
      simp [List.countP_cons,hf,z]
    · have flag : isNot g.op = false := Bool.eq_false_iff.mpr (fun h => hg ((isNot_iff _).mp h))
      simpa [List.countP_cons,flag] using ih rest

def root : List Sig := [
  (0xf83c0781fe0fe07fc0ff80fffffff80001f8007e07ff8001024f1106932673ff,0x5914128462012004c42a82186294302082082082082080000245000291023155),
  (0x3fc007fe0ff0ff83ff07ff03e07c000000001f81f8000406b38c229b1cdb9ccc,0x2b50231c263062814d230e09aa585269a69a69a69a698402b38c008b144a94cc),
  (0x3ffff8000fff0003fff80003ff8000007e07e00000000098c3f0cce3e0e3e0f0,0x3398f2084ed70a23aeb21432db50a0e38e38e38e38e38088c2d044a3a0e3e0f0),
  (0xc00000000ffffffc00000003fffff81f80000000001fc8e0fc00f0fc00fc00ff,0x820140308d6adb68288028431c63c1c71c71c71c71c748a0d400f0fc00fc00aa),
  (0xffffffffffffffc0000000000000001ffe070ff0000ff0000ffff00,0x28041098c9c7230c470e01001059659659659659670fd0000ff0000b54a00),
  (0xfffffffff000000000000000000007e00007fffe00007f000000ffffff000000,0x423046180001040000040800002010410410410410459000000bb544a000000),
  (0x7fffff8000000007fffffff000000000000,0x6186186186186182657292a000000000000)]

def goalTable : Nat := 0xfffffffffffefffafefefefeeeeeaa00

theorem samples_match : ∀ b i, evalT goalTable (sample root b i) = b := by
  decide +kernel

def Blocked (k t : Nat) (v : List Sig) : Prop :=
  ∀ m ≤ k, ¬ Live m t v.toFinset

def Batch (k t : Nat) : List (List Sig) → Prop
  | [] => True
  | a :: rest => Blocked k t a ∧ Batch k t rest

theorem in_batch {k t ws w} (h : Batch k t ws) (mem : w ∈ ws) : Blocked k t w := by
  induction ws with
  | nil => simp at mem
  | cons a l ih =>
    rcases List.mem_cons.mp mem with rfl | m
    · exact h.1
    · exact ih h.2 m

def sameBank (w v : List Sig) : Bool :=
  w.all v.contains && v.all w.contains

theorem sameBank_eq {w v : List Sig} (h : sameBank w v = true) : w.toFinset = v.toFinset := by
  obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨fun h => List.contains_iff_mem.mp (List.all_eq_true.mp ha a h),
         fun h => List.contains_iff_mem.mp (List.all_eq_true.mp hb a h)⟩

def allowChild (states : List (List Sig)) (w : List Sig) : Bool :=
  !(states.any (sameBank w))

theorem allow_live {k t m states w} (bad : Batch k t states) (sz : m ≤ k)
    (live : Live m t w.toFinset) : allowChild states w = true := by
  have noMatch : states.any (sameBank w) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨v,hv,eq⟩ := List.any_eq_true.mp hh
    exact in_batch bad hv m sz (sameBank_eq eq ▸ live)
  simp [allowChild, noMatch]

theorem block_step {k t v} (unary binary : List (List Sig)) (hu : Batch k (t-1) unary)
    (hb : Batch k t binary) (nd : v.Nodup)
    (ok : stepTest k t v (allowChild unary) (allowChild binary) = false) : Blocked (k+1) t v := by
  intro m small h
  have good := reduced_step (u := allowChild unary) (b := allowChild binary) h small nd rfl
    (fun _ _ _ sz l => allow_live hu sz l) (fun _ _ _ sz l => allow_live hb sz l)
  exact Bool.false_ne_true (ok.symm.trans good)

theorem block_search {k t v} (nd : v.Nodup) (ok : search k t v = false) : Blocked k t v := by
  intro m small live
  exact Bool.false_ne_true (ok.symm.trans (search_complete live k small v nd rfl))

open PEqualNP.CircuitLowerBounds

def edgeFn (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def replacement : Circuit :=
  ⟨[⟨.or, [0, 6]⟩,
      ⟨.or, [3, 5]⟩,
      ⟨.and, [7, 8]⟩,
      ⟨.or, [5, 6]⟩,
      ⟨.or, [0, 2]⟩,
      ⟨.and, [10, 11]⟩,
      ⟨.or, [9, 12]⟩,
      ⟨.or, [0, 1]⟩,
      ⟨.or, [4, 5]⟩,
      ⟨.and, [14, 15]⟩,
      ⟨.or, [13, 16]⟩], 17⟩

theorem replacement_size : replacement.gates.length = 11 := rfl

theorem replacement_basis : ∀ g ∈ replacement.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [replacement]

set_option maxRecDepth 16000 in
theorem replacement_correct : ∀ x : Fin 7 → Bool, replacement.eval (List.ofFn x) = edgeFn x := by
  decide +kernel

theorem table_agrees : ∀ x : Fin 7 → Bool, edgeFn x = evalT goalTable x := by
  decide +kernel

-- Count binary gates even when the single NOT is discarded from a live plan.
theorem lower_with_not (gs : List Gate) (o : ℕ)
    (basis : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (oneNot : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (used : ∃ g ∈ gs, g.op = .not)
    (correct : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = edgeFn x)
    (zeroNot : Blocked 9 0 root) (one : Blocked 10 1 root) : 11 ≤ gs.length := by
  by_contra! small
  have legal : PEqualNP.MetaComplexity.FanInTwo (⟨gs,o⟩ : Circuit) := by
    simpa only [PEqualNP.MetaComplexity.FanInTwo, Set.mem_insert_iff, Set.mem_singleton_iff] using basis
  have hout := circuit_target goalTable root rfl samples_match (⟨gs,o⟩ : Circuit) legal
    (fun x => (correct x).trans (table_agrees x))
  obtain ⟨k,t,S,hk,count,live,sub⟩ := extract gs root legal hout
  have eq := necessary root (by decide +kernel) live sub
  have hL : Live k t root.toFinset := eq.symm ▸ live
  have atMostOne := notCount gs oneNot
  have positive : 0 < gs.countP (fun g => isNot g.op) := by
    obtain ⟨g,hg,op⟩ := used
    by_contra! hz
    have absent := List.countP_eq_zero.mp (Nat.le_zero.mp hz) g hg
    exact absent ((isNot_iff _).mpr op)
  by_cases z : t = 0
  · subst t
    exact zeroNot k (by omega) hL
  · have u : t = 1 := by omega
    subst t
    exact one k (by omega) hL

-- Each named bank is a set of live wire signatures. The following exclusions
-- are small subproblems of the same two finite searches.

def sig0 : Sig := (0xf83c0781fe0fe07fc0ff80fffffff80001f8007e07ff8001024f1106932673ff, 0x5914128462012004c42a82186294302082082082082080000245000291023155)
def sig1 : Sig := (0x3fc007fe0ff0ff83ff07ff03e07c000000001f81f8000406b38c229b1cdb9ccc, 0x2b50231c263062814d230e09aa585269a69a69a69a698402b38c008b144a94cc)
def sig2 : Sig := (0x3ffff8000fff0003fff80003ff8000007e07e00000000098c3f0cce3e0e3e0f0, 0x3398f2084ed70a23aeb21432db50a0e38e38e38e38e38088c2d044a3a0e3e0f0)
def sig3 : Sig := (0xc00000000ffffffc00000003fffff81f80000000001fc8e0fc00f0fc00fc00ff, 0x820140308d6adb68288028431c63c1c71c71c71c71c748a0d400f0fc00fc00aa)
def sig4 : Sig := (0xffffffffffffffc0000000000000001ffe070ff0000ff0000ffff00, 0x28041098c9c7230c470e01001059659659659659670fd0000ff0000b54a00)
def sig5 : Sig := (0xfffffffff000000000000000000007e00007fffe00007f000000ffffff000000, 0x423046180001040000040800002010410410410410459000000bb544a000000)
def sig6 : Sig := (0x7fffff8000000007fffffff000000000000, 0x6186186186186182657292a000000000000)
def sig7 : Sig := (0x380007800e00e003c0078003e07c00000000000000000000020c0002100210cc, 0x910020422002000442202082210102082082082082080000204000210021044)
def sig8 : Sig := (0xfffc07fffffffffffffffffffffff80001f81fffffff8407b3cf339f9fffffff, 0x7b54339c66316285cd2b8e19eadc7269a69a69a69a698402b3cd008b954ab5dd)
def sig9 : Sig := (0x383c00000e0f0003c0f80003ff800000000000000000000002400002802260f0, 0x1110120042010000842200104210202082082082082080000240000280022050)
def sig10 : Sig := (0xffffff81ffffe07fffff80fffffff8007fffe07e07ff8099c3ffdde7f3e7f3ff, 0x7b9cf28c6ed72a27eeba963afbd4b0e38e38e38e38e38088c2d544a3b1e3f1f5)
def sig11 : Sig := (0xc00000000e0fe07c00000003fffff80000000000001f800000001004002400ff, 0x0)
def sig12 : Sig := (0xf83c0781ffffffffc0ff80fffffff81f81f8007e07ffc8e1fe4ff1fe93fe73ff, 0xdb1552b4ef6bfb6cecaaaa5b7ef7f1e79e79e79e79e7c8a0d645f0fe91fe31ff)
def sig13 : Sig := (0xe0fe07fc0ff80fc000000000000000007e000010000110000267300, 0x0)
def sig14 : Sig := (0xf83c0781fffffffffffffffffffff80001f8007ffffff0ff024fff0693ffffff, 0x591692c56b8dbc76f4eef2f8729535b6db6db6db6db6f0fd0245ff0291b77b55)
def sig15 : Sig := (0xf83c0781f000000000000000000000000000007e000000000000110693000000, 0x0)
def sig16 : Sig := (0xfffffffffe0fe07fc0ff80ffffffffe001fffffe07ffff01024fffffff2673ff, 0x5d3716e5e2013044c42ac29862963124924924924924d9000245bb56db023155)
def sig17 : Sig := (0x1f8000000000001024f000000000000, 0x0)
def sig18 : Sig := (0xf83c0781fe0fe07fc0ff80fffffffffffff8007e07ffffffffff1106932673ff, 0x5914128462012004c42a821862943638e38e38e38e38a6572b6f000291023155)
def sig19 : Sig := (0x3fc000000ff00003ff000003e000000000000000000000008380008300c380c0, 0x23102208061002010c2204008a500061861861861861800082800083004280c0)
def sig20 : Sig := (0x3ffffffe0fffff83ffffff03fffc00007e07ff81f800049ef3fceefbfcfbfcfc, 0x3bd8f31c6ef76aa3efb31e3bfb58f2ebaebaebaebaeb848af3dc44abb4ebf4fc)
def sig21 : Sig := (0xff0ff8000000003e07c00000000000000000000b000209800d800cc, 0x200001004204200080008010840404104104104104100009000008800480088)
def sig22 : Sig := (0xffc007fe0fffffffff07ff03fffff81f80001f81f81fcce6ff8cf2ff1cff9cff, 0xab51633caf7afbe96da32e4bbe7bd3efbefbefbefbefcca2f78cf0ff14fe94ee)
def sig23 : Sig := (0xff0ff83ff07ff000000000000000001f80000060000220000db9c00, 0x0)
def sig24 : Sig := (0x3fc007fe0fffffffffffffffe07c000000001f81ffe074ffb38cff9b1cffffcc, 0x2b52a35d2fbcfef37de77ee9ba5957fffffffffffffff4ffb38cff8b14ffdecc)
def sig25 : Sig := (0x3fc007fe00000000000000000000000000001f80000004000000229b1c000000, 0x0)
def sig26 : Sig := (0xfffffffffff0ff83ff07ff03e07c07e00007fffff8007f06b38cffffffdb9ccc, 0x2f73277da63072c14d234e89aa5a536db6db6db6db6ddd02b38cbbdf5e4a94cc)
def sig27 : Sig := (0x406b38c000000000000, 0x20820820820820804022108000000000000)
def sig28 : Sig := (0x3fc007fe0ff0ff83ff07ff03e07c07fffff81f81f8007fffffff229b1cdb9ccc, 0x2b50231c263062814d230e09aa585679e79e79e79e79a657bbae008b144a94cc)
def sig29 : Sig := (0xfff000000000003ff8000000000000000000080c000c0e000e000f0, 0x20040000c420a2028800002184080c30c30c30c30c30080c00040a000e000a0)
def sig30 : Sig := (0xfffff8000ffffffffff80003fffff81ffe07e000001fc8f8fff0fcffe0ffe0ff, 0xb399f238cfffdb6baeb23c73df73e1e79e79e79e79e7c8a8d6d0f4ffa0ffe0fa)
def sig31 : Sig := (0xfff0003fff800000000000000000000000000980000cc0000e3e000, 0x800008840822208010201000008208208208208200880000440000a14000)
def sig32 : Sig := (0x3ffff8000fffffffffffffffff8000007e07e001ffe070ffc3f0ffe3e0fffff0, 0x339af2494fdf9e73bef674f2db51a5f7df7df7df7df7f0fdc2d0ffa3a0f7eaf0)
def sig33 : Sig := (0x3ffff8000000000000000000000000000007e000000000000000cce3e0000000, 0x0)
def sig34 : Sig := (0xffffffffffff0003fff80003ff8007e07e07fffe00007f98c3f0ffffffe3e0f0, 0x37bbf669ced71a63aeb254b2db52a1e79e79e79e79e7d988c2d0fff7eae3e0f0)
def sig35 : Sig := (0x7e00000000000098c3f0000000000000, 0x0)
def sig36 : Sig := (0x3ffff8000fff0003fff80003ff8007ffffffe00000007fffffffcce3e0e3e0f0, 0x3398f2084ed70a23aeb21432db50a6fbefbefbefbefba6dfebfa44a3a0e3e0f0)
def sig37 : Sig := (0xffffffc000000000000000000000000000040e00000f00000fc0000, 0x9089860208020401001018618618618618640a00000f00000b40000)
def sig38 : Sig := (0xc00000000ffffffffffffffffffff81f80000001fffff8fffc00fffc00ffffff, 0x8203c0718deedf7a38c478e31c63c5d75d75d75d75d778fdd400fffc00fd4aaa)
def sig39 : Sig := (0xc000000000000000000000000000000000000000000048000000f0fc00000000, 0x1002080001040000000000002010410410410410448000000b05400000000)
def sig40 : Sig := (0xfffffffffffffffc00000003ffffffff8007fffe001fffe0fc00fffffffc00ff, 0x862344718d6adb68288068c31c63c1c71c71c71c71c759a0d400fbfc4afc00aa)
def sig41 : Sig := (0x1f80000000000048e0fc00000000000000, 0x0)
def sig42 : Sig := (0xc00000000ffffffc00000003fffffffffff80000001ffffffffff0fc00fc00ff, 0x820140308d6adb68288028431c63c7df7df7df7df7df6ef7fd2af0fc00fc00aa)
def sig43 : Sig := (0x70000000ff0000000000, 0x2004100001040000040800000010410410410410450000000bb0000000000)
def sig44 : Sig := (0xfffffffffffffffffffffffc000007e00007ffffffe07fff0000ffffffffff00, 0x4238461898c9c7230c470e01003059659659659659679fd0000ff544ab54a00)
def sig45 : Sig := (0x70ff0000000000000000, 0x41041041041041020550000000000000000)
def sig46 : Sig := (0xffffffffffffffc000007fffff80001ffe07fffffffff0000ffff00, 0x28041098c9c7230c470e01001079e79e79e79e79e76ff292aff0000b54a00)
def sig47 : Sig := (0x7e00000000000007f000000000000000000, 0x0)
def sig48 : Sig := (0xfffffffff000000000000000000007fffffffffe00007fffffffffffff000000, 0x423046180001040000040800002071c71c71c71c71c7f57292abb544a000000)
def sig49 : Sig := (0xe00e00000000003e07c0000000000000000000000000000000000cc, 0x0)
def sig50 : Sig := (0xe00e003c00780000000000000000000000000000000000000021000, 0x0)
def sig51 : Sig := (0x3800078000000000000000000000000000000000000000000000000210000000, 0x0)
def sig52 : Sig := (0x20c000000000000, 0x0)
def sig53 : Sig := (0x3ffc00000fff0003fff80003ff800000000000000000000083c0008380e3e0f0, 0x33103208461102018c220410ca502061861861861861800082c000838042a0d0)
def sig54 : Sig := (0xfffffffffffffffffffffffffffff8007fffffffffff849ff3ffffffffffffff, 0x7bdcf39c6ef76aa7efbb9e3bfbdcf2ebaebaebaebaeb848af3dd44abb5ebf5fd)
def sig55 : Sig := (0xc00000000ffffffc00000003fffff80000000000001f8000b000309c00fc00ff, 0x200001004204200080008010840404104104104104100009000008800480088)
def sig56 : Sig := (0xfffc07fffffffffffffffffffffff81f81f81fffffffcce7ffcff3ff9fffffff, 0xfb5573bcef7bfbededabae5bfefff3efbefbefbefbefcca2f7cdf0ff95feb5ff)
def sig57 : Sig := (0xffffffffffffffc0000000000000001ffe000070000330000ffff00, 0x0)
def sig58 : Sig := (0xfffc07fffffffffffffffffffffff80001f81ffffffff4ffb3cfff9f9fffffff, 0x7b56b3dd6fbdfef7fdeffef9fadd77fffffffffffffff4ffb3cdff8b95ffffdd)
def sig59 : Sig := (0xfffc07fff0000000000000000000000000001ffe000004000000339f9f000000, 0x0)
def sig60 : Sig := (0xffffffffffffffffffffffffffffffe001ffffffffffff07b3cfffffffffffff, 0x7f7737fde63172c5cd2bce99eade736db6db6db6db6ddd02b3cdbbdfdf4ab5dd)
def sig61 : Sig := (0x1f8000000000407b3cf000000000000, 0x20820820820820804022108000000000000)
def sig62 : Sig := (0xfffc07fffffffffffffffffffffffffffff81fffffffffffffff339f9fffffff, 0x7b54339c66316285cd2b8e19eadc7679e79e79e79e79a657bbef008b954ab5dd)
def sig63 : Sig := (0x3fc007800ff0e003ff078003e07c00000000000000000000838c008310c390cc, 0x2b10220c261022014c220608aa501061861861861861800082840083104290c4)
def sig64 : Sig := (0xc00000000fffe07c00000003fffff80000000000001f8080c000d0e400e400ff, 0x20040000c420a2028800002184080c30c30c30c30c30080c00040a000e000a0)
def sig65 : Sig := (0xffffff81ffffffffffff80fffffff81fffffe07e07ffc8f9fffffdfff3fff3ff, 0xfb9df2bceffffb6feebabe7bfff7f1e79e79e79e79e7c8a8d6d5f4ffb1fff1ff)
def sig66 : Sig := (0xfffe07fffff80fc000000000000000007e000990000dd0000e7f300, 0x800008840822208010201000008208208208208200880000440000a14000)
def sig67 : Sig := (0xffffff81fffffffffffffffffffff8007fffe07ffffff0ffc3ffffe7f3ffffff, 0x7b9ef2cd6fdfbe77fefef6fafbd5b5f7df7df7df7df7f0fdc2d5ffa3b1f7fbf5)
def sig68 : Sig := (0xffffff81f000000000000000000000000007e07e000000000000dde7f3000000, 0x0)
def sig69 : Sig := (0xffffffffffffe07fffff80ffffffffe07ffffffe07ffff99c3ffffffffe7f3ff, 0x7fbff6edeed73a67eebad6bafbd6b1e79e79e79e79e7d988c2d5fff7fbe3f1f5)
def sig70 : Sig := (0x7ff8000000000099c3ff000000000000, 0x0)
def sig71 : Sig := (0xffffff81ffffe07fffff80ffffffffffffffe07e07ffffffffffdde7f3e7f3ff, 0x7b9cf28c6ed72a27eeba963afbd4b6fbefbefbefbefba6dfebff44a3b1e3f1f5)
def sig72 : Sig := (0xf83c0781fe0fe07c00000003fffff8000000007e001f800000001106932400ff, 0x0)
def sig73 : Sig := (0xffffffffffffffffc0ff80ffffffffff81fffffe07ffffe1fe4ffffffffe73ff, 0xdf3756f5ef6bfb6cecaaeadb7ef7f1e79e79e79e79e7d9a0d645fbfedbfe31ff)
def sig74 : Sig := (0x3fc007fe0ff0ff8000000003e07c000000001f8000000400b000229b1cd800cc, 0x200001004204200080008010840404104104104104100009000008800480088)
def sig75 : Sig := (0xffffffffffffffffff07ff03ffffffff8007fffff81fffe6ff8cffffffff9cff, 0xaf73677daf7afbe96da36ecbbe7bd3efbefbefbefbefdda2f78cfbff5efe94ee)
def sig76 : Sig := (0xffffffc000000000000000000000000000070e00000ff0000fc0000, 0x2004109089860208060c01001018618618618618650a00000fb0000b40000)
def sig77 : Sig := (0xffffffffffffffffffffffffffffffff8007fffffffffffffc00ffffffffffff, 0x8623c4718deedf7a38c478e31c63c5d75d75d75d75d779fdd400fffc4afd4aaa)
def sig78 : Sig := (0x7ff8000000000007fe0fc00000000000000, 0x0)
def sig79 : Sig := (0xfffffffffffffffc00000003fffffffffffffffe001ffffffffffffffffc00ff, 0x862344718d6adb68288068c31c63c7df7df7df7df7df7ff7fd2afbfc4afc00aa)
def sig80 : Sig := (0xf83c0781fe0fe07fc0ff80fc000000000000007e07e000010000110693267300, 0x0)
def sig81 : Sig := (0xffffffffffffffffffffffffffffffe001ffffffffffffff024fffffffffffff, 0x5d3796e5eb8dbc76f4eef2f8729735b6db6db6db6db6f9fd0245ff56dbb77b55)
def sig82 : Sig := (0x3fc007fe0ff0ff83ff07ff000000000000001f81f80004060000229b1cdb9c00, 0x0)
def sig83 : Sig := (0xffffffffffffffffffffffffe07c07e00007ffffffe07fffb38cffffffffffcc, 0x2f73a77dafbcfef37de77ee9ba5b57fffffffffffffffdffb38cffdf5effdecc)
def sig84 : Sig := (0xc00000000ffffffc000000000000000000000000000048e00000f0fc00fc0000, 0x1002089089860208020401003018618618618618648a00000f05400b40000)
def sig85 : Sig := (0x7e00000000000007fff0000000000000000, 0x41041041041041020550000000000000000)
def sig86 : Sig := (0xfffffffffffffffffffffffc000007ffffffffffffe07fffffffffffffffff00, 0x4238461898c9c7230c470e01003079e79e79e79e79e7fff292aff544ab54a00)
def sig87 : Sig := (0x3ffff8000fff000000000003ff8000000007e00000000080c000cce3e0e000f0, 0x20040000c420a2028800002184080c30c30c30c30c30080c00040a000e000a0)
def sig88 : Sig := (0xfffffffffffffffffff80003fffffffffe07fffe001ffff8fff0ffffffffe0ff, 0xb7bbf679cfffdb6baeb27cf3df73e1e79e79e79e79e7d9a8d6d0ffffeaffe0fa)
def sig89 : Sig := (0x3fc007fe0e00e003c0078003e07c000000001f8000000400020c229b1c0210cc, 0x910020422002000442202082210102082082082082080000204000210021044)
def sig90 : Sig := (0x3ffff8000fff0003fff80000000000000007e000000000980000cce3e0e3e000, 0x800008840822208010201000008208208208208200880000440000a14000)
def sig91 : Sig := (0xffffffffffffffffffffffffff8007e07e07ffffffe07fffc3f0fffffffffff0, 0x37bbf669cfdf9e73bef674f2db53a5f7df7df7df7df7f9fdc2d0fff7eaf7eaf0)
def sig92 : Sig := (0x380007800e00e003c0078003e07c00000000000000000406b38c0002100210cc, 0x9100204220020004422020822101228a28a28a28a288402230c000210021044)
def sig93 : Sig := (0xe0f000000000003ff800000000000000000000000000000002000f0, 0x0)
def sig94 : Sig := (0xe0f0003c0f800000000000000000000000000000000000000226000, 0x0)
def sig95 : Sig := (0x383c000000000000000000000000000000000000000000000000000280000000, 0x0)
def sig96 : Sig := (0x240000000000000, 0x0)
def sig97 : Sig := (0xe0fe07c000000000000000000000000000000000000100000240000, 0x0)
def sig98 : Sig := (0xc00000000ffffffffffffffffffff80000000001fffff0ff0000ff0400ffffff, 0x28041098c9c7230c470e01001059659659659659670fd0000ff0000b54a00)
def sig99 : Sig := (0xc000000000000000000000000000000000000000000000000000100400000000, 0x0)
def sig100 : Sig := (0xfffffffffe0fe07c00000003ffffffe00007fffe001fff000000ffffff2400ff, 0x423046180001040000040800002010410410410410459000000bb544a000000)
def sig101 : Sig := (0xc00000000e0fe07c00000003fffffffffff80000001fffffffff1004002400ff, 0x6186186186186182657292a000000000000)
def sig102 : Sig := (0xc00000000e0fe07c00000003fffff80000000000001fc8000000f0fc002400ff, 0x1002080001040000000000002010410410410410448000000b05400000000)
def sig103 : Sig := (0xc00000000e0fe07c00000003fffff81f80000000001fc8e0fc001004002400ff, 0x0)
def sig104 : Sig := (0xf83c0781fffffffffffffffffffffffffff8007fffffffffffffff0693ffffff, 0x591692c56b8dbc76f4eef2f8729537befbefbefbefbef6ff2b6fff0291b77b55)
def sig105 : Sig := (0xf83c0781fffffffffffffffffffff80001f8007fffff8007024f330693ffffff, 0x5914128462012004c42a82186294302082082082082080000245000291023155)
def sig106 : Sig := (0xe0fe07fc0ff80fc000000000000000007e070010000ff0000267300, 0x2004100001040000040800000010410410410410450000000bb0000000000)
def sig107 : Sig := (0x7e001f8000000007f01024f000000000000, 0x0)
def sig108 : Sig := (0xfffffffffe0fe07fc0ff80fffffffffffffffffe07ffffffffffffffff2673ff, 0x5d3716e5e2013044c42ac2986296373cf3cf3cf3cf3cff572b6fbb56db023155)
def sig109 : Sig := (0xfffc07fffe0fe07fc0ff80fffffff80001f81ffe07ff8401024f339f9f2673ff, 0x5914128462012004c42a82186294302082082082082080000245000291023155)
def sig110 : Sig := (0xffffff81fe0fe07fc0ff80fffffff80001ffe07e07ff8001024fdde7f32673ff, 0x5914128462012004c42a82186294302082082082082080000245000291023155)
def sig111 : Sig := (0xfffffffffe0fe07fc0ff80fc000007e00007fffe07e07f010000ffffff267300, 0x423046180001040000040800002010410410410410459000000bb544a000000)
def sig112 : Sig := (0xf83c0781ffffffffc0ff80fffffffffffff8007e07fffffffffff1fe93fe73ff, 0xdb1552b4ef6bfb6cecaaaa5b7ef7f7ffffffffffffffeef7ff6ff0fe91fe31ff)
def sig113 : Sig := (0xe0fe07fc0ff80fc000000000000000007e070ff0000110000267300, 0x41041041041041020550000000000000000)
def sig114 : Sig := (0xf83c0781f000000000000000000007e00000007e00007f000000110693000000, 0x0)
def sig115 : Sig := (0xf83c0781fe0fe07fc0ff80fffffff8007ff8007e07ff8099c3ff1106932673ff, 0x5914128462012004c42a82186294302082082082082080000245000291023155)
def sig116 : Sig := (0xfffff8000fffe07ffff80003fffff8007e07e000001f8098c3f0dce7e0e7e0ff, 0x3398f2084ed70a23aeb21432db50a0e38e38e38e38e38088c2d044a3a0e3e0f0)
def sig117 : Sig := (0x3ffff8000fffe07fffff80ffff8000007e07e00007e00099c3f0dde3e0e7f3f0, 0x3398f2084ed70a23aeb21432db50a0e38e38e38e38e38088c2d044a3a0e3e0f0)
def sig118 : Sig := (0xc00000000fffffffc0ff80fffffff81f8000000007ffc8e1fc00f1fc00fe73ff, 0x820140308d6adb68288028431c63c1c71c71c71c71c748a0d400f0fc00fc00aa)
def sig119 : Sig := (0x110000000000, 0x0)
def sig120 : Sig := (0x10000000000000000, 0x0)
def sig121 : Sig := (0xe0fe07fc0ff80fc000007fffff8000007e07fffffff110000267300, 0x6186186186186182657292a000000000000)
def sig122 : Sig := (0xf83c0781fffffffffffffffc000000000000007fffe070ff0000ff0693ffff00, 0x28041098c9c7230c470e01001059659659659659670fd0000ff0000b54a00)
def sig123 : Sig := (0xffffffffffffffc0000000001f80001ffe070ff024fff0000ffff00, 0x28041098c9c7230c470e01001059659659659659670fd0000ff0000b54a00)
def sig124 : Sig := (0xffffff81ffff0003fff80003ff8000007e07e07e00000098c3f0dde7f3e3e0f0, 0x3398f2084ed70a23aeb21432db50a0e38e38e38e38e38088c2d044a3a0e3e0f0)
def sig125 : Sig := (0xf83c0781fffffffc00000003fffff81f8000007e001fc8e0fc00f1fe93fc00ff, 0x820140308d6adb68288028431c63c1c71c71c71c71c748a0d400f0fc00fc00aa)
def sig126 : Sig := (0xf83c0781f000000000000000000007fffff8007e00007fffffff110693000000, 0x6186186186186182657292a000000000000)
def sig127 : Sig := (0xf83c0781f0000000000000000000000001f8007e00000001024f110693000000, 0x0)
def sig128 : Sig := (0x3ffff8000e0f0003c0f80003ff8000000007e000000000000240cce3e02260f0, 0x1110120042010000842200104210202082082082082080000240000280022050)
def sig129 : Sig := (0x3ffff8000000000000000000000000007e07e00000000098c3f0cce3e0000000, 0x0)
def sig130 : Sig := (0xffffffffffff0003fff80003ff8007fffffffffe00007fffffffffffffe3e0f0, 0x37bbf669ced71a63aeb254b2db52a7ffffffffffffffffdfebfafff7eae3e0f0)
def sig131 : Sig := (0xc000000000000000000000000000001f80000000000048e0fc00f0fc00000000, 0x1002080001040000000000002010410410410410448000000b05400000000)
def sig132 : Sig := (0x70ff0000ff0000000000, 0x2004100001040000040800000051451451451451470550000bb0000000000)
def sig133 : Sig := (0xfffffffff000000000000000000007e001fffffe00007f01024fffffff000000, 0x423046180001040000040800002010410410410410459000000bb544a000000)
def sig134 : Sig := (0x3ffff8000fff0003fff80003ff8000007fffe00000000099c3ffcce3e0e3e0f0, 0x3398f2084ed70a23aeb21432db50a0e38e38e38e38e38088c2d044a3a0e3e0f0)
def sig135 : Sig := (0xc00000000ffffffc00000003fffff81f81f80000001fc8e1fe4ff0fc00fc00ff, 0x820140308d6adb68288028431c63c1c71c71c71c71c748a0d400f0fc00fc00aa)
def sig136 : Sig := (0x383c00000e0f0003c0f80003ff8000007e00000000000098c3f00002802260f0, 0x1110120042010000842200104210202082082082082080000240000280022050)
def sig137 : Sig := (0xf83c0781fe0fe07fc0ff80fffffff81f81f8007e07ffc8e1fe4f1106932673ff, 0x5914128462012004c42a82186294302082082082082080000245000291023155)
def sig138 : Sig := (0xc0e000000000, 0x0)
def sig139 : Sig := (0x80c000000000000000, 0x0)
def sig140 : Sig := (0xcc0000000000, 0x0)
def sig141 : Sig := (0x980000000000000000, 0x0)
def sig142 : Sig := (0xfffff8000ffffffc00000003fffff81f8007e000001fc8e0fc00fcffe0fc00ff, 0x820140308d6adb68288028431c63c1c71c71c71c71c748a0d400f0fc00fc00aa)
def sig143 : Sig := (0x3ffff8000ffffffffffffffc000000000007e001ffe070ff0000ffe3e0ffff00, 0x28041098c9c7230c470e01001059659659659659670fd0000ff0000b54a00)
def sig144 : Sig := (0x3ffff8000000000000000000000007ffffffe00000007fffffffcce3e0000000, 0x6186186186186182657292a000000000000)
def sig145 : Sig := (0xc00000000ffffffc00000003fffff81ffe000000001fc8f8fff0f0fc00fc00ff, 0x820140308d6adb68288028431c63c1c71c71c71c71c748a0d400f0fc00fc00aa)
def sig146 : Sig := (0xffffffffffffffc000000007e000001ffe070ffc3f0ff0000ffff00, 0x28041098c9c7230c470e01001059659659659659670fd0000ff0000b54a00)
def sig147 : Sig := (0xfffffffff000000000000000000007e07e07fffe00007f98c3f0ffffff000000, 0x423046180001040000040800002010410410410410459000000bb544a000000)
def sig148 : Sig := (0x40e00000000000000000, 0x0)
def sig149 : Sig := (0x48000000000000000000, 0x0)
def sig150 : Sig := (0xfffffffff000000000000000000007ff8007fffe00007fe0fc00ffffff000000, 0x423046180001040000040800002010410410410410459000000bb544a000000)
def sig151 : Sig := (0x3ffff8000fff0003fff80003ff80001ffe07e000000048f8fff0cce3e0e3e0f0, 0x3398f2084ed70a23aeb21432db50a0e38e38e38e38e38088c2d044a3a0e3e0f0)
def sig152 : Sig := (0xffffffffffffffc0000001f80000001ffe078fffc00ff0000ffff00, 0x28041098c9c7230c470e01001059659659659659670fd0000ff0000b54a00)
def sig153 : Sig := (0xb000000000000000, 0x0)
def sig154 : Sig := (0x70000000000000000000, 0x0)
def sig155 : Sig := (0x4000000000000000000, 0x0)
def sig156 : Sig := (0xf83c0781fe0fe07fc0ff80ffffffffe001f8007e07ffff01024f1106932673ff, 0x5914128462012004c42a82186294302082082082082080000245000291023155)
def sig157 : Sig := (0x3ffff8000fff0003fff80003ff8007e07e07e00000007f98c3f0cce3e0e3e0f0, 0x3398f2084ed70a23aeb21432db50a0e38e38e38e38e38088c2d044a3a0e3e0f0)
def sig158 : Sig := (0xc00000000ffffffc00000003ffffffff80000000001fffe0fc00f0fc00fc00ff, 0x820140308d6adb68288028431c63c1c71c71c71c71c748a0d400f0fc00fc00aa)
def sig159 : Sig := (0xffffffffffffffc000007e000000001ffe07fff0000ff0000ffff00, 0x28041098c9c7230c470e01001059659659659659670fd0000ff0000b54a00)
def sig160 : Sig := (0x3fc007fe0fffffffffffffffe07c000000001f81ffe00407b38c339b1cffffcc, 0x2b50231c263062814d230e09aa585269a69a69a69a698402b38c008b144a94cc)
def sig161 : Sig := (0xff00003ff0000000000000000000000000000000000000000c38000, 0x0)
def sig162 : Sig := (0x3fc0000000000000000000000000000000000000000000000000008300000000, 0x0)
def sig163 : Sig := (0x8380000000000000, 0x0)
def sig164 : Sig := (0xff0ff80000000000000000000000000000000000000200000d80000, 0x0)
def sig165 : Sig := (0x209800000000, 0x0)
def sig166 : Sig := (0xffc007fe0fffffffff07ff03fffff80000001f81f81f8406b38c329f1cff9cff, 0x2b50231c263062814d230e09aa585269a69a69a69a698402b38c008b144a94cc)
def sig167 : Sig := (0x3ffff8000fffff83ffffff03ff8000007e07e001f800009ec3f0eee3e0fbfcf0, 0x3398f2084ed70a23aeb21432db50a0e38e38e38e38e38088c2d044a3a0e3e0f0)
def sig168 : Sig := (0xc00000000fffffffff07ff03fffff81f80000001f81fc8e6fc00f2fc00ff9cff, 0x820140308d6adb68288028431c63c1c71c71c71c71c748a0d400f0fc00fc00aa)
def sig169 : Sig := (0x220000000000, 0x0)
def sig170 : Sig := (0xfffffffffff0ff83ff07ff00000007e00007fffff8007f060000ffffffdb9c00, 0x423046180001040000040800002010410410410410459000000bb544a000000)
def sig171 : Sig := (0x60000000000000000, 0x0)
def sig172 : Sig := (0xff0ff83ff07ff00000007fffff80001f8007fffffff220000db9c00, 0x6186186186186182657292a000000000000)
def sig173 : Sig := (0x3ffffffe0fff0003fff80003ff8000007e07ff8000000498c3f0eefbfce3e0f0, 0x3398f2084ed70a23aeb21432db50a0e38e38e38e38e38088c2d044a3a0e3e0f0)
def sig174 : Sig := (0xffc007fe0ffffffc00000003fffff81f80001f80001fcce0fc00f2ff1cfc00ff, 0x820140308d6adb68288028431c63c1c71c71c71c71c748a0d400f0fc00fc00aa)
def sig175 : Sig := (0x3fc007fe0ffffffffffffffc0000000000001f81ffe074ff0000ff9b1cffff00, 0x28041098c9c7230c470e01001059659659659659670fd0000ff0000b54a00)
def sig176 : Sig := (0x3fc007fe0000000000000000000007fffff81f8000007fffffff229b1c000000, 0x6186186186186182657292a000000000000)
def sig177 : Sig := (0xfffffffffff0ff83ff07ff03e07c07fffffffffff8007fffffffffffffdb9ccc, 0x2f73277da63072c14d234e89aa5a577df7df7df7df7dff57bbaebbdf5e4a94cc)
def sig178 : Sig := (0xfffc07fffff0ff83ff07ff03e07c000000001ffff8000406b38c339f9fdb9ccc, 0x2b50231c263062814d230e09aa585269a69a69a69a698402b38c008b144a94cc)
def sig179 : Sig := (0x3fc007fe0ff0ff83ff07ff03e07c000001f81f81f8000407b3cf229b1cdb9ccc, 0x2b50231c263062814d230e09aa585269a69a69a69a698402b38c008b144a94cc)
def sig180 : Sig := (0x3fc007fe00000000000000000000000000001f8000000406b38c229b1c000000, 0x20820820820820804022108000000000000)
def sig181 : Sig := (0x3fc007fe0ff0ff83ff07ff03e07c001f80001f81f8004ce6ff8c229b1cdb9ccc, 0x2b50231c263062814d230e09aa585269a69a69a69a698402b38c008b144a94cc)
def sig182 : Sig := (0x3fc007fe0ff0ff83ff07ff03e07c07e000001f81f8007f06b38c229b1cdb9ccc, 0x2b50231c263062814d230e09aa585269a69a69a69a698402b38c008b144a94cc)
def sig183 : Sig := (0x3ffffffe0ff0ff83ff07ff03e07c00000007ff81f8000406b38ceefbfcdb9ccc, 0x2b50231c263062814d230e09aa585269a69a69a69a698402b38c008b144a94cc)
def sig184 : Sig := (0x3fc007fe0ff0ff83ff07ff03e07c00007e001f81f800049ef3fc229b1cdb9ccc, 0x2b50231c263062814d230e09aa585269a69a69a69a698402b38c008b144a94cc)
def sig185 : Sig := (0x7c3f87e01f01f803f007f00000007fffe07ff81f8007ffefdb0eef96cd98c00, 0xa6ebed7b9dfedffb3bd57de79d6bcfdf7df7df7df7df7ffffdbafffd6efdceaa)
def sig186 : Sig := (0xc03ff801f00f007c00f800fc1f83ffffffffe07e07fffbf94c73dd64e3246333, 0xd4afdce3d9cf9d7eb2dcf1f655a7ad965965965965967bfd4c73ff74ebb56b33)
def sig187 : Sig := (0xc00007fff000fffc0007fffc007fffff81f81fffffffff673c0f331c1f1c1f0f, 0xcc670df7b128f5dc514debcd24af5f1c71c71c71c71c7f773d2fbb5c5f1c1f0f)
def sig188 : Sig := (0x3ffffffff0000003fffffffc000007e07fffffffffe0371f03ff0f03ff03ff00, 0x7dfebfcf72952497d77fd7bce39c3e38e38e38e38e38b75f2bff0f03ff03ff55)
def sig189 : Sig := (0xfffffffff000000000000003fffffffffffffffe001f8f00ffff00ffff0000ff, 0xfffd7fbef673638dcf3b8f1feffefa69a69a69a69a698f02ffff00ffff4ab5ff)
def sig190 : Sig := (0xffffffffffffffffffff81ffff80001ffff80ffffff000000ffffff, 0xfbdcfb9e7fffefbfffffbf7ffffdfefbefbefbefbefba6ffffff44abb5ffffff)
def sig191 : Sig := (0xfffffffffffffffffffffffffffff8000007ffffffff80000000ffffffffffff, 0xfffffffffffffffffffffffffffff9e79e79e79e79e7d9a8d6d5ffffffffffff)
def sig192 : Sig := (0x7c0007e01f01f803f007f000000000000001f81f8000406b18022990cd98c00, 0x224021180430428109010c01884842492492492492490402b188008904488488)
def sig193 : Sig := (0x3fc3fffe0ff0ff83ff07ff03e07c07fffe07ff81f8007ffeffbceefb7cdb9ccc, 0xaffbef7fbffefffb7ff77fefbf7bdfffffffffffffffffffffbeffff7effdeee)
def sig194 : Sig := (0x7c3f80001f000003f000000000000007e07e00000000098c1b0cce160c18000, 0x2288e0080cd60a232a901422994080c30c30c30c30c30088c09044a120e1c0a0)
def sig195 : Sig := (0x3ffff87e0fff1f83fff87f03ff8007fffe07ff81f8007ffefff0eefbecfbecf0, 0xb7fbff7bdfffdffbbff77df7df7beffffffffffffffffffffffaffffeeffeefa)
def sig196 : Sig := (0x1f01f80000000000000001f80000000000048e0fc00e0f800d80000, 0x820140308d6adb68288028431c63c1c71c71c71c71c748a0d400f0fc00fc00aa)
def sig197 : Sig := (0xc7c3f87e0ffffffc3f007f03fffffffffe07ff81f81ffffefdb0fefd6cfd8cff, 0xa6ebed7b9dfedffb3bd57de79d6bcfdf7df7df7df7df7ffffdbafffd6efdceaa)
def sig198 : Sig := (0x1f01f803f007f000000000000000001f80070fe0000ee0000d98c00, 0x28041098c9c7230c470e01001059659659659659670fd0000ff0000b54a00)
def sig199 : Sig := (0x7c3f87e0ffffffffffffffc000007fffe07ff81ffe07ffffdb0fff96cffff00, 0xa6ebed7b9dfedffb3bd57de79d6bcfdf7df7df7df7df7ffffdbafffd6efdceaa)
def sig200 : Sig := (0x7c3f87e0000000000000000000007e00007ff8000007f000000eef96c000000, 0x423046180001040000040800002010410410410410459000000bb544a000000)
def sig201 : Sig := (0xfffffffff1f01f803f007f00000007fffe07fffff8007ffefdb0ffffffd98c00, 0xa6ebed7b9dfedffb3bd57de79d6bcfdf7df7df7df7df7ffffdbafffd6efdceaa)
def sig202 : Sig := (0x7fffe00000000007ffefdb0000000000000, 0x6186186186186182657292a000000000000)
def sig203 : Sig := (0x7c3f87e01f01f803f007f00000007ffffffff81f8007fffffffeef96cd98c00, 0xa6ebed7b9dfedffb3bd57de79d6bcfdf7df7df7df7df7ffffdbafffd6efdceaa)
def sig204 : Sig := (0xc03c0001f00f007c00f800fc1f83f80001f8007e07ff80010043110483246333, 0x5004108040010004800880104084200000000000000000000041000081002111)
def sig205 : Sig := (0xf83fff81fe0fe07fc0ff80ffffffffffffffe07e07fffbf94e7fdd66f32673ff, 0xddbfdee7fbcfbd7ef6fef3fe77b7bdb6db6db6db6db6fbfd4e77ff76fbb77b77)
def sig206 : Sig := (0x3ff800000f000000f800001f8000007e07e000000000984070cc60e0206030, 0x1088d00048c70822a29010325100a082082082082082008840504420a0a16030)
def sig207 : Sig := (0xfffff801ffff007ffff800ffff83ffffffffe07e07fffbf9cff3dde7e3e7e3f3, 0xf7bffeebdfdf9f7fbefef5f6dff7adf7df7df7df7df7fbfdcef3fff7ebf7ebf3)
def sig208 : Sig := (0xc0000000000f007c000000001f83f81f80000000001fc8e04c00d06400240033, 0x80014020894a9968208020421423818618618618618648a04400f07400b40022)
def sig209 : Sig := (0xc03ff801fffffffc00f800ffffffffffffffe07e07fffbf9fc73fdfce3fc63ff, 0xd6afdcf3ddefdf7ebadcf9f75de7edd75d75d75d75d77bfddc73fffcebfd6bbb)
def sig210 : Sig := (0xf007c00f800fc000000000000000007e070f90000dd0000246300, 0x28041098c9c7230c470e01001059659659659659670fd0000ff0000b54a00)
def sig211 : Sig := (0xc03ff801fffffffffffffffc1f83ffffffffe07ffffffbff4c73ff64e3ffff33, 0xd4afdce3d9cf9d7eb2dcf1f655a7ad965965965965967bfd4c73ff74ebb56b33)
def sig212 : Sig := (0xc03ff801f000000000000000000007e00007e07e00007b000000dd64e3000000, 0x423046180001040000040800002010410410410410459000000bb544a000000)
def sig213 : Sig := (0xfffffffff00f007c00f800fc1f83fffffffffffe07fffff94c73ffffff246333, 0xd4afdce3d9cf9d7eb2dcf1f655a7ad965965965965967bfd4c73ff74ebb56b33)
def sig214 : Sig := (0x7fffff8000000007bf94c73000000000000, 0x41041041041041022550822000000000000)
def sig215 : Sig := (0xc03ff801f00f007c00f800fc1f83ffffffffe07e07ffffffffffdd64e3246333, 0xd4afdce3d9cf9d7eb2dcf1f655a7af9e79e79e79e79e7fff6d7bff74ebb56b33)
def sig216 : Sig := (0xc0000781f000e07c000780fc007ff80001f8007e07ff8001000f11041304130f, 0x4804008420002004400882082084100000000000000000000005000011001105)
def sig217 : Sig := (0xf83c07fffe0fffffc0ffffffffffffff81f81fffffffff673e4f331e9f3e7fff, 0xdd771ff7f329f5dcd56febdd66bf7f3cf3cf3cf3cf3cff773f6fbb5edf1e3f5f)
def sig218 : Sig := (0x7fe0000ff800007ff00007c000000001f81f8000406300c22181c181c0c, 0x84001142020608041010a09200852082082082082080402310c00081408140c)
def sig219 : Sig := (0xffc007fffff0ffffff07ffffe07fffff81f81fffffffff67bf8f339f1fdf9fcf, 0xef772fffb738f7dd5d6fefcdaeff5f7df7df7df7df7dff77bfafbbdf5f5e9fcf)
def sig220 : Sig := (0xc00000000000fffc00000000007ff81f80000000001fc8603c00301c001c000f, 0x800100308128d148000028410423410410410410410448201400b05c001c000a)
def sig221 : Sig := (0xc00007fffffffffc0007ffffffffffff81f81fffffffffe7fc0ff3fc1ffc1fff, 0xce674df7bd6afffc79cdebcf3cefdfdf7df7df7df7df7ff7fd2ffbfc5ffc1faf)
def sig222 : Sig := (0xfffc0007fffc0000000000000001ffe0706700003300001c1f00, 0x2004101089450104460c00001051451451451451470750000bb0000140a00)
def sig223 : Sig := (0xc00007fffffffffffffffffc007fffff81f81fffffffffff3c0fff1c1fffff0f, 0xcc678df7b9acfdfe71cdfbed34af5f9e79e79e79e79e7fff3d2fff5c5fbd5f0f)
def sig224 : Sig := (0xc00007fff000000000000000000007e000001ffe00007f000000331c1f000000, 0x423046180001040000040800002010410410410410459000000bb544a000000)
def sig225 : Sig := (0xfffffffff000fffc0007fffc007fffff81ffffffffffff673c0fffffff1c1f0f, 0xcc670df7b128f5dc514debcd24af5f1c71c71c71c71c7f773d2fbb5c5f1c1f0f)
def sig226 : Sig := (0x7ff81f8000000007f673c0f000000000000, 0x6186186186186182657292a000000000000)
def sig227 : Sig := (0xc00007fff000fffc0007fffc007ffffffff81fffffffffffffff331c1f1c1f0f, 0xcc670df7b128f5dc514debcd24af5f1c71c71c71c71c7f773d2fbb5c5f1c1f0f)
def sig228 : Sig := (0x383c0781f0000003c0ff80fc0000000001f8007e07e00001024f010293027300, 0x5914128462012004c42a82186294302082082082082080000245000291023155)
def sig229 : Sig := (0xfffffffffe0fe07fffffffffffffffe07fffffffffffb71f03ff1f07ff27ffff, 0x7dfebfcf72952497d77fd7bce39c3e38e38e38e38e38b75f2bff0f03ff03ff55)
def sig230 : Sig := (0x3fc007fe00000003ff07ff000000000000001f81f8000406038c02031c039c00, 0x2950230c2210208145230608a2181228a28a28a28a288402238c000314029444)
def sig231 : Sig := (0x3ffffffffff0ff83ffffffffe07c07e07fffffffffe0371fb3ff2f9bffdbffcc, 0x7ffebfdf76b56697df7fdfbdebdc7e79e79e79e79e79b75fbbff0f8bff4bffdd)
def sig232 : Sig := (0x3ffff80000000003fff80000000000007e07e0000000001803f00c03e003e000, 0x3198b2084295000386321430c3102020820820820820800802d00403a003e050)
def sig233 : Sig := (0x3fffffffffff0003ffffffffff8007e07fffffffffe0379fc3ffcfe3ffe3fff0, 0x7ffeffcf7ed72eb7ffffd7befbdcbefbefbefbefbefbb7dfebff4fa3ffe3fff5)
def sig234 : Sig := (0x3fffffffc0000000000000001ffe0301f00000f000003ff00, 0x2804100840412104450a000000410410410410410305d00000f0000014a00)
def sig235 : Sig := (0x3ffffffffffffffffffffffc000007e07fffffffffe077ff03ffff03ffffff00, 0x7dfebfcf7b9dbcf7f7fff7fcf39d3fbefbefbefbefbef7ff2bffff03ffb7ff55)
def sig236 : Sig := (0x3ffffffff000000000000000000007e00007fffe0000370000000f03ff000000, 0x4220441000000000000408000000000000000000000110000000b004a000000)
def sig237 : Sig := (0xfffffffff0000003fffffffc000007e07fffffffffe07f1f03ffffffff03ff00, 0x7dffbfeff29534d7d77fd7bce39e3f3cf3cf3cf3cf3cff5f2bffbf57ff03ff55)
def sig238 : Sig := (0x7e07ff800000000371f03ff000000000000, 0x6186186186186182657292a000000000000)
def sig239 : Sig := (0x3ffffffff0000003fffffffc000007ffffffffffffe07fffffff0f03ff03ff00, 0x7dfebfcf72952497d77fd7bce39c3e38e38e38e38e38b75f2bff0f03ff03ff55)
def sig240 : Sig := (0xf83c0781f000000000000003fffff80001f8007e001f8000024f0006930000ff, 0x5914128462012004c42a82186294302082082082082080000245000291023155)
def sig241 : Sig := (0xfffffffffe0fe07fc0ff80fffffffffffffffffe07ff8f01ffff11ffff2673ff, 0xfffd7fbef673638dcf3b8f1feffefa69a69a69a69a698f02ffff00ffff4ab5ff)
def sig242 : Sig := (0x3fc007fe0000000000000003e07c000000001f8000000400b38c009b1c0000cc, 0x2b50231c263062814d230e09aa585269a69a69a69a698402b38c008b144a94cc)
def sig243 : Sig := (0xfffffffffff0ff83ff07ff03fffffffffffffffff81f8f06ffff22ffffdb9cff, 0xfffd7fbef673638dcf3b8f1feffefa69a69a69a69a698f02ffff00ffff4ab5ff)
def sig244 : Sig := (0x3ffff8000000000000000003ff8000007e07e00000000000c3f000e3e00000f0, 0x33987208465302018e320412cb50a0618618618618618000c2d000a3a042a0f0)
def sig245 : Sig := (0xffffffffffff0003fff80003fffffffffffffffe001f8f98ffffccffffe3e0ff, 0xfffdffbefef76bafefbb9f3ffffefaebaebaebaebaeb8f8affff44ffffebf5ff)
def sig246 : Sig := (0xc00000000000000000000003fffff81f80000000001f8800fc0000fc000000ff, 0x8201403084624308080008030c62c0410410410410410800d40000fc004800aa)
def sig247 : Sig := (0xfffffffffffffffc00000003fffffffffffffffe001fcfe0fffff0fffffc00ff, 0xfffd7fbeff7bfbedefbbaf5ffffffbefbefbefbefbefcfa2fffff0fffffeb5ff)
def sig248 : Sig := (0xfffffffff000000000000000000007e00007fffe00000f00000000ffff000000, 0x42104208000000000000000000200000000000000000900000000544a000000)
def sig249 : Sig := (0xfffffffff000000000000003fffffffffffffffe001fff00ffffffffff0000ff, 0xffff7ffff67373cdcf3bcf9feffefb6db6db6db6db6ddf02ffffbbffff4ab5ff)
def sig250 : Sig := (0x7fffff8000000000f00ffff000000000000, 0x2082082082082080602292a000000000000)
def sig251 : Sig := (0xfffffffff000000000000003fffffffffffffffe001fffffffff00ffff0000ff, 0xfffd7fbef673638dcf3b8f1feffefe79e79e79e79e79af57ffff00ffff4ab5ff)
def sig252 : Sig := (0xe0fe07fc0ff80fffffff80001f8000007ff8001024f0000002673ff, 0x5914128462012004c42a82186294302082082082082080000245000291023155)
def sig253 : Sig := (0xf83c0781fffffffffffffffffffff81ffff8007fffff80ffffff110693ffffff, 0xfbdcfb9e7fffefbfffffbf7ffffdfefbefbefbefbefba6ffffff44abb5ffffff)
def sig254 : Sig := (0xff0ff83ff07ff03e07c000000000001f8000006b38c000000db9ccc, 0x2b50231c263062814d230e09aa585269a69a69a69a698402b38c008b144a94cc)
def sig255 : Sig := (0x3fc007fe0ffffffffffffffffffff81ffff81f81ffff84ffffff229b1cffffff, 0xfbdcfb9e7fffefbfffffbf7ffffdfefbefbefbefbefba6ffffff44abb5ffffff)
def sig256 : Sig := (0xfff0003fff80003ff8000007e00000000000098c3f0000000e3e0f0, 0x3398f2084ed70a23aeb21432db50a0e38e38e38e38e38088c2d044a3a0e3e0f0)
def sig257 : Sig := (0x3ffff8000ffffffffffffffffffff81fffffe001ffff80ffffffcce3e0ffffff, 0xfbdcfb9e7fffefbfffffbf7ffffdfefbefbefbefbefba6ffffff44abb5ffffff)
def sig258 : Sig := (0xffffffc00000003fffff81f80000000001f80e0fc00000000fc00ff, 0x820040100d6acb28288028431c61c0c30c30c30c30c300a0d40040a800fc00aa)
def sig259 : Sig := (0xc00000000ffffffffffffffffffff81ffff80001ffffc8fffffff0fc00ffffff, 0xfbddfbbeffffffffffffbf7fffffffffffffffffffffeefffffff4ffb5ffffff)
def sig260 : Sig := (0xffffffffffffffc0000000000000001ffe000ff0000000000ffff00, 0x8000098c8c3230c430601001049249249249249220fd0000440000b54a00)
def sig261 : Sig := (0xffffffffffffffffffff81ffff80001fffff0ffffffff0000ffffff, 0xfbdefbdf7ffffffffffffffffffdfffffffffffffffff6ffffffffabb5ffffff)
def sig262 : Sig := (0x1ffff80000000000ffffff000000000000, 0x6186186186186182657292a000000000000)
def sig263 : Sig := (0xffffffffffffffffffffffffff80001ffffffffffff000000ffffff, 0xfbdcfb9e7fffefbfffffbf7ffffdfefbefbefbefbefba6ffffff44abb5ffffff)
def sig264 : Sig := (0xf83c0781fe0fe07fc0ff80fffffff8000000007e07ff800000001106932673ff, 0x5914128462012004c42a82186294302082082082082080000245000291023155)
def sig265 : Sig := (0xfffffffffffffffffffffffffffff80001ffffffffff8001024fffffffffffff, 0xfffffffffffffffffffffffffffff9e79e79e79e79e7d9a8d6d5ffffffffffff)
def sig266 : Sig := (0x3fc007fe0ff0ff83ff07ff03e07c000000001f81f80000000000229b1cdb9ccc, 0x2b50231c263062814d230e09aa58506186186186186180009284008b144a94cc)
def sig267 : Sig := (0xfffffffffffffffffffffffffffff8000007ffffffff8406b38cffffffffffff, 0xfffffffffffffffffffffffffffffbefbefbefbefbefddaaf7ddffffffffffff)
def sig268 : Sig := (0x3ffff8000fff0003fff80003ff8000000007e000000000000000cce3e0e3e0f0, 0x3398f2084ed70a23aeb21432db50a0e38e38e38e38e38088c2d044a3a0e3e0f0)
def sig269 : Sig := (0xfffffffffffffffffffffffffffff8007e07ffffffff8098c3f0ffffffffffff, 0xfffffffffffffffffffffffffffff9e79e79e79e79e7d9a8d6d5ffffffffffff)
def sig270 : Sig := (0xc00000000ffffffc00000003fffff80000000000001f80000000f0fc00fc00ff, 0x820140308d6adb68288028431c63c1c71c71c71c71c748a0d400f0fc00fc00aa)
def sig271 : Sig := (0xfffffffffffffffffffffffffffff81f8007ffffffffc8e0fc00ffffffffffff, 0xfffffffffffffffffffffffffffff9e79e79e79e79e7d9a8d6d5ffffffffffff)
def sig272 : Sig := (0xffffffffffffffc0000000000000001ffe000000000ff0000ffff00, 0x28041098c9c7230c470e01001018618618618618650a80000ff0000b54a00)
def sig273 : Sig := (0xfffffffffffffffffffffffffffff8000007fffffffff0ff0000ffffffffffff, 0xfffffffffffffffffffffffffffffdf7df7df7df7df7f9fdd6d5ffffffffffff)
def sig274 : Sig := (0xfffffffff000000000000000000000000007fffe000000000000ffffff000000, 0x423046180001040000040800002010410410410410459000000bb544a000000)
def sig275 : Sig := (0xffffffffffffffffffffffffffffffe00007ffffffffff000000ffffffffffff, 0xfffffffffffffffffffffffffffff9e79e79e79e79e7d9a8d6d5ffffffffffff)
def sig276 : Sig := (0x3f8000000000000000000000007fffe07e00000007bf84c30cc6060000000, 0x84abcc6399ce9d7a32d471e615238d965965965965967bfd4c32ff746ab54a22)
def sig277 : Sig := (0x7e00001f8000007f00000007ff80001f81f8007f663c0022180c180c00, 0x84630d739128d5d8114569c5042b4f1c71c71c71c71c7f773d2abb5c4e1c0e0a)
def sig278 : Sig := (0x3fffffffc000000007ff80001ffe0001f03ff00000003ff00, 0x79dcbb8e72952497d77f973ce39c3e38e38e38e38e38a65f2bff0403b503ff55)
def sig279 : Sig := (0x3fffff81ffff80000001f8000ffff0000000000ff, 0xfbdc7b9e7673638dcf3b8f1feffcfa69a69a69a69a698602ffff00abb54ab5ff)
def sig280 : Sig := (0x3ffffffff1f01f83fffffffc000007ffffffffffffe07fffffffeffbffdbff00, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def sig281 : Sig := (0x1f01f803f007f000000001ffe000001f80000fefdb0000000d98c00, 0xa2c8e91a1dfecfbb3bd53d679d69cedb6db6db6db6db26fffdba44a924fdceaa)
def sig282 : Sig := (0x7c3f87e01f01f803f007f00000000000007ff81f80000000000eef96cd98c00, 0xa6ebed7b9dfedffb3bd57de79d6bc9c71c71c71c71c759a8d490fffd6efdceaa)
def sig283 : Sig := (0xfffffffff1f01f803f007f03fffffffffffffffff81ffffeffffeeffffd98cff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def sig284 : Sig := (0x7c3f87e0fffffffffffffffffffffffffffff81ffffffffffffeef96cffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def sig285 : Sig := (0xffffffffffffffffffff80000000001ffff80000000000000ffffff, 0xfbdcfb9e7fffefbfffffbf7ffffdf8e38e38e38e38e380a8d6d544abb5ffffff)
def sig286 : Sig := (0xfffffffffffffffffffffffffffffffffe07fffffffffffefdb0ffffffffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def sig287 : Sig := (0xc00007fffffffffffffffffffffffffffff81fffffffffffffff331c1fffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def sig288 : Sig := (0xffffffffffffffffffffffffffffffff81ffffffffffff673c0fffffffffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def sig289 : Sig := (0xffffffffffffffffffffffffffffffe07fffffffffffb71f03ffffffffffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def sig290 : Sig := (0xfffffffffffffffffffffffffffff81fffffffffffff80ffffffffffffffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def sig291 : Sig := (0xfffffffff00f007c00f800fffffffffffffffffe07fffff9ffffddffff2463ff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def sig292 : Sig := (0xc03ff801ffffffffffffffffffffffffffffe07ffffffbffffffdd64e3ffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def bank0 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6]
def bank1 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig7]
def bank2 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig185]
def bank3 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig186]
def bank4 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig187]
def bank5 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig188]
def bank6 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig189]
def bank7 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig190]
def bank8 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig191]
def bank9 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig8]
def bank10 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig8, sig185]
def bank11 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig8, sig186]
def bank12 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig8, sig187]
def bank13 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig8, sig188]
def bank14 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig8, sig189]
def bank15 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig8, sig190]
def bank16 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig8, sig191]
def bank17 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig8, sig276]
def bank18 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig9]
def bank19 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig9, sig185]
def bank20 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig9, sig186]
def bank21 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig9, sig187]
def bank22 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig9, sig188]
def bank23 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig9, sig189]
def bank24 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig9, sig190]
def bank25 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig9, sig191]
def bank26 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig10]
def bank27 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig10, sig185]
def bank28 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig10, sig186]
def bank29 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig10, sig187]
def bank30 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig10, sig188]
def bank31 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig10, sig189]
def bank32 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig10, sig190]
def bank33 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig10, sig191]
def bank34 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig10, sig277]
def bank35 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig11]
def bank36 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig11, sig185]
def bank37 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig11, sig186]
def bank38 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig11, sig187]
def bank39 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig11, sig188]
def bank40 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig11, sig189]
def bank41 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig11, sig190]
def bank42 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig11, sig191]
def bank43 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig11, sig280]
def bank44 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig12]
def bank45 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig12, sig185]
def bank46 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig12, sig186]
def bank47 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig12, sig187]
def bank48 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig12, sig188]
def bank49 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig12, sig189]
def bank50 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig12, sig190]
def bank51 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig12, sig191]
def bank52 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig13]
def bank53 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig13, sig185]
def bank54 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig13, sig186]
def bank55 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig13, sig187]
def bank56 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig13, sig188]
def bank57 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig13, sig189]
def bank58 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig13, sig190]
def bank59 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig13, sig191]
def bank60 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig13, sig283]
def bank61 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig14]
def bank62 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig14, sig185]
def bank63 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig14, sig186]
def bank64 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig14, sig187]
def bank65 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig14, sig188]
def bank66 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig14, sig189]
def bank67 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig14, sig190]
def bank68 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig14, sig191]
def bank69 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig15]
def bank70 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig15, sig185]
def bank71 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig15, sig186]
def bank72 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig15, sig187]
def bank73 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig15, sig188]
def bank74 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig15, sig189]
def bank75 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig15, sig190]
def bank76 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig15, sig191]
def bank77 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig15, sig284]
def bank78 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig16]
def bank79 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig16, sig185]
def bank80 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig16, sig186]
def bank81 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig16, sig187]
def bank82 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig16, sig188]
def bank83 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig16, sig189]
def bank84 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig16, sig190]
def bank85 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig16, sig191]
def bank86 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig16, sig281]
def bank87 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig17]
def bank88 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig17, sig185]
def bank89 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig17, sig186]
def bank90 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig17, sig187]
def bank91 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig17, sig188]
def bank92 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig17, sig189]
def bank93 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig17, sig190]
def bank94 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig17, sig191]
def bank95 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig17, sig286]
def bank96 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig18]
def bank97 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig18, sig185]
def bank98 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig18, sig186]
def bank99 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig18, sig187]
def bank100 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig18, sig188]
def bank101 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig18, sig189]
def bank102 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig18, sig190]
def bank103 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig18, sig191]
def bank104 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig18, sig282]
def bank105 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig19]
def bank106 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig19, sig185]
def bank107 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig19, sig186]
def bank108 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig19, sig187]
def bank109 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig19, sig188]
def bank110 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig19, sig189]
def bank111 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig19, sig190]
def bank112 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig19, sig191]
def bank113 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig20]
def bank114 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig20, sig185]
def bank115 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig20, sig186]
def bank116 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig20, sig187]
def bank117 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig20, sig188]
def bank118 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig20, sig189]
def bank119 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig20, sig190]
def bank120 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig20, sig191]
def bank121 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig21]
def bank122 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig21, sig185]
def bank123 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig21, sig186]
def bank124 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig21, sig187]
def bank125 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig21, sig188]
def bank126 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig21, sig189]
def bank127 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig21, sig190]
def bank128 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig21, sig191]
def bank129 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig22]
def bank130 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig22, sig185]
def bank131 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig22, sig186]
def bank132 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig22, sig187]
def bank133 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig22, sig188]
def bank134 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig22, sig189]
def bank135 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig22, sig190]
def bank136 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig22, sig191]
def bank137 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig23]
def bank138 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig23, sig185]
def bank139 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig23, sig186]
def bank140 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig23, sig187]
def bank141 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig23, sig188]
def bank142 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig23, sig189]
def bank143 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig23, sig190]
def bank144 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig23, sig191]
def bank145 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig23, sig291]
def bank146 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig24]
def bank147 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig24, sig185]
def bank148 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig24, sig186]
def bank149 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig24, sig187]
def bank150 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig24, sig188]
def bank151 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig24, sig189]
def bank152 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig24, sig190]
def bank153 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig24, sig191]
def bank154 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig25]
def bank155 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig25, sig185]
def bank156 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig25, sig186]
def bank157 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig25, sig187]
def bank158 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig25, sig188]
def bank159 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig25, sig189]
def bank160 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig25, sig190]
def bank161 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig25, sig191]
def bank162 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig25, sig292]
def bank163 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig26]
def bank164 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig26, sig185]
def bank165 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig26, sig186]
def bank166 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig26, sig187]
def bank167 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig26, sig188]
def bank168 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig26, sig189]
def bank169 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig26, sig190]
def bank170 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig26, sig191]
def bank171 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig27]
def bank172 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig27, sig185]
def bank173 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig27, sig186]
def bank174 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig27, sig187]
def bank175 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig27, sig188]
def bank176 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig27, sig189]
def bank177 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig27, sig190]
def bank178 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig27, sig191]
def bank179 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig28]
def bank180 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig28, sig185]
def bank181 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig28, sig186]
def bank182 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig28, sig187]
def bank183 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig28, sig188]
def bank184 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig28, sig189]
def bank185 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig28, sig190]
def bank186 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig28, sig191]
def bank187 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig29]
def bank188 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig29, sig185]
def bank189 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig29, sig186]
def bank190 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig29, sig187]
def bank191 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig29, sig188]
def bank192 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig29, sig189]
def bank193 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig29, sig190]
def bank194 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig29, sig191]
def bank195 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig30]
def bank196 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig30, sig185]
def bank197 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig30, sig186]
def bank198 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig30, sig187]
def bank199 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig30, sig188]
def bank200 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig30, sig189]
def bank201 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig30, sig190]
def bank202 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig30, sig191]
def bank203 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig31]
def bank204 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig31, sig185]
def bank205 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig31, sig186]
def bank206 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig31, sig187]
def bank207 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig31, sig188]
def bank208 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig31, sig189]
def bank209 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig31, sig190]
def bank210 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig31, sig191]
def bank211 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig32]
def bank212 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig32, sig185]
def bank213 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig32, sig186]
def bank214 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig32, sig187]
def bank215 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig32, sig188]
def bank216 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig32, sig189]
def bank217 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig32, sig190]
def bank218 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig32, sig191]
def bank219 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig33]
def bank220 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig33, sig185]
def bank221 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig33, sig186]
def bank222 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig33, sig187]
def bank223 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig33, sig188]
def bank224 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig33, sig189]
def bank225 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig33, sig190]
def bank226 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig33, sig191]
def bank227 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig33, sig287]
def bank228 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig34]
def bank229 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig34, sig185]
def bank230 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig34, sig186]
def bank231 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig34, sig187]
def bank232 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig34, sig188]
def bank233 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig34, sig189]
def bank234 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig34, sig190]
def bank235 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig34, sig191]
def bank236 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig35]
def bank237 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig35, sig185]
def bank238 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig35, sig186]
def bank239 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig35, sig187]
def bank240 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig35, sig188]
def bank241 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig35, sig189]
def bank242 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig35, sig190]
def bank243 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig35, sig191]
def bank244 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig35, sig288]
def bank245 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig36]
def bank246 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig36, sig185]
def bank247 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig36, sig186]
def bank248 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig36, sig187]
def bank249 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig36, sig188]
def bank250 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig36, sig189]
def bank251 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig36, sig190]
def bank252 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig36, sig191]
def bank253 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig37]
def bank254 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig37, sig185]
def bank255 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig37, sig186]
def bank256 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig37, sig187]
def bank257 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig37, sig188]
def bank258 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig37, sig189]
def bank259 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig37, sig190]
def bank260 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig37, sig191]
def bank261 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig38]
def bank262 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig38, sig185]
def bank263 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig38, sig186]
def bank264 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig38, sig187]
def bank265 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig38, sig188]
def bank266 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig38, sig189]
def bank267 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig38, sig190]
def bank268 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig38, sig191]
def bank269 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig39]
def bank270 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig39, sig185]
def bank271 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig39, sig186]
def bank272 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig39, sig187]
def bank273 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig39, sig188]
def bank274 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig39, sig189]
def bank275 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig39, sig190]
def bank276 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig39, sig191]
def bank277 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig40]
def bank278 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig40, sig185]
def bank279 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig40, sig186]
def bank280 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig40, sig187]
def bank281 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig40, sig188]
def bank282 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig40, sig189]
def bank283 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig40, sig190]
def bank284 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig40, sig191]
def bank285 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig40, sig278]
def bank286 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig41]
def bank287 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig41, sig185]
def bank288 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig41, sig186]
def bank289 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig41, sig187]
def bank290 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig41, sig188]
def bank291 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig41, sig189]
def bank292 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig41, sig190]
def bank293 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig41, sig191]
def bank294 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig41, sig289]
def bank295 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig42]
def bank296 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig42, sig185]
def bank297 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig42, sig186]
def bank298 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig42, sig187]
def bank299 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig42, sig188]
def bank300 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig42, sig189]
def bank301 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig42, sig190]
def bank302 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig42, sig191]
def bank303 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig43]
def bank304 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig43, sig185]
def bank305 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig43, sig186]
def bank306 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig43, sig187]
def bank307 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig43, sig188]
def bank308 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig43, sig189]
def bank309 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig43, sig190]
def bank310 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig43, sig191]
def bank311 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig44]
def bank312 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig44, sig185]
def bank313 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig44, sig186]
def bank314 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig44, sig187]
def bank315 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig44, sig188]
def bank316 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig44, sig189]
def bank317 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig44, sig190]
def bank318 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig44, sig191]
def bank319 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig44, sig279]
def bank320 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig45]
def bank321 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig45, sig185]
def bank322 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig45, sig186]
def bank323 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig45, sig187]
def bank324 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig45, sig188]
def bank325 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig45, sig189]
def bank326 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig45, sig190]
def bank327 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig45, sig191]
def bank328 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig46]
def bank329 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig46, sig185]
def bank330 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig46, sig186]
def bank331 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig46, sig187]
def bank332 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig46, sig188]
def bank333 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig46, sig189]
def bank334 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig46, sig190]
def bank335 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig46, sig191]
def bank336 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig47]
def bank337 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig47, sig185]
def bank338 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig47, sig186]
def bank339 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig47, sig187]
def bank340 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig47, sig188]
def bank341 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig47, sig189]
def bank342 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig47, sig190]
def bank343 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig47, sig191]
def bank344 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig47, sig290]
def bank345 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig48]
def bank346 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig48, sig185]
def bank347 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig48, sig186]
def bank348 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig48, sig187]
def bank349 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig48, sig188]
def bank350 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig48, sig189]
def bank351 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig48, sig190]
def bank352 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig48, sig191]
def bank353 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig48, sig285]
def bank354 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig49]
def bank355 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig50]
def bank356 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig51]
def bank357 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig52]
def bank358 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig53]
def bank359 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig54]
def bank360 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig55]
def bank361 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig56]
def bank362 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig57]
def bank363 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig58]
def bank364 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig59]
def bank365 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig60]
def bank366 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig61]
def bank367 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig62]
def bank368 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig63]
def bank369 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig64]
def bank370 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig65]
def bank371 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig66]
def bank372 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig67]
def bank373 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig68]
def bank374 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig69]
def bank375 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig70]
def bank376 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig71]
def bank377 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig72]
def bank378 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig73]
def bank379 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig74]
def bank380 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig75]
def bank381 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig76]
def bank382 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig77]
def bank383 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig78]
def bank384 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig79]
def bank385 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig80]
def bank386 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig81]
def bank387 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig82]
def bank388 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig83]
def bank389 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig84]
def bank390 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig85]
def bank391 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig86]
def bank392 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig87]
def bank393 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig88]
def bank394 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig89]
def bank395 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig90]
def bank396 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig91]
def bank397 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig92]
def bank398 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig93]
def bank399 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig94]
def bank400 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig95]
def bank401 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig96]
def bank402 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig97]
def bank403 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig98]
def bank404 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig99]
def bank405 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig100]
def bank406 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig101]
def bank407 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig102]
def bank408 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig103]
def bank409 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig104]
def bank410 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig105]
def bank411 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig106]
def bank412 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig107]
def bank413 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig108]
def bank414 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig109]
def bank415 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig110]
def bank416 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig111]
def bank417 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig112]
def bank418 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig113]
def bank419 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig114]
def bank420 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig115]
def bank421 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig116]
def bank422 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig117]
def bank423 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig118]
def bank424 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig119]
def bank425 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig120]
def bank426 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig121]
def bank427 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig122]
def bank428 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig123]
def bank429 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig124]
def bank430 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig125]
def bank431 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig126]
def bank432 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig127]
def bank433 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig128]
def bank434 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig129]
def bank435 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig130]
def bank436 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig131]
def bank437 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig132]
def bank438 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig133]
def bank439 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig134]
def bank440 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig135]
def bank441 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig136]
def bank442 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig137]
def bank443 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig138]
def bank444 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig139]
def bank445 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig140]
def bank446 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig141]
def bank447 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig142]
def bank448 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig143]
def bank449 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig144]
def bank450 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig145]
def bank451 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig146]
def bank452 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig147]
def bank453 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig148]
def bank454 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig149]
def bank455 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig150]
def bank456 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig151]
def bank457 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig152]
def bank458 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig153]
def bank459 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig154]
def bank460 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig155]
def bank461 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig156]
def bank462 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig157]
def bank463 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig158]
def bank464 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig159]
def bank465 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig160]
def bank466 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig161]
def bank467 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig162]
def bank468 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig163]
def bank469 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig164]
def bank470 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig165]
def bank471 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig166]
def bank472 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig167]
def bank473 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig168]
def bank474 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig169]
def bank475 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig170]
def bank476 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig171]
def bank477 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig172]
def bank478 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig173]
def bank479 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig174]
def bank480 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig175]
def bank481 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig176]
def bank482 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig177]
def bank483 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig178]
def bank484 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig179]
def bank485 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig180]
def bank486 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig181]
def bank487 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig182]
def bank488 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig183]
def bank489 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig184]
def bank490 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig185]
def bank491 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig185, sig192]
def bank492 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig185, sig193]
def bank493 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig185, sig194]
def bank494 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig185, sig195]
def bank495 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig185, sig196]
def bank496 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig185, sig197]
def bank497 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig185, sig198]
def bank498 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig185, sig199]
def bank499 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig185, sig200]
def bank500 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig185, sig201]
def bank501 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig185, sig202]
def bank502 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig185, sig203]
def bank503 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig186]
def bank504 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig186, sig204]
def bank505 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig186, sig205]
def bank506 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig186, sig206]
def bank507 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig186, sig207]
def bank508 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig186, sig208]
def bank509 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig186, sig209]
def bank510 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig186, sig210]
def bank511 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig186, sig211]
def bank512 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig186, sig212]
def bank513 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig186, sig213]
def bank514 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig186, sig214]
def bank515 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig186, sig215]
def bank516 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig187]
def bank517 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig187, sig216]
def bank518 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig187, sig217]
def bank519 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig187, sig218]
def bank520 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig187, sig219]
def bank521 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig187, sig220]
def bank522 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig187, sig221]
def bank523 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig187, sig222]
def bank524 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig187, sig223]
def bank525 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig187, sig224]
def bank526 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig187, sig225]
def bank527 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig187, sig226]
def bank528 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig187, sig227]
def bank529 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig188]
def bank530 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig188, sig228]
def bank531 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig188, sig229]
def bank532 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig188, sig230]
def bank533 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig188, sig231]
def bank534 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig188, sig232]
def bank535 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig188, sig233]
def bank536 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig188, sig234]
def bank537 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig188, sig235]
def bank538 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig188, sig236]
def bank539 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig188, sig237]
def bank540 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig188, sig238]
def bank541 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig188, sig239]
def bank542 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig189]
def bank543 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig189, sig240]
def bank544 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig189, sig241]
def bank545 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig189, sig242]
def bank546 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig189, sig243]
def bank547 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig189, sig244]
def bank548 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig189, sig245]
def bank549 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig189, sig246]
def bank550 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig189, sig247]
def bank551 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig189, sig248]
def bank552 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig189, sig249]
def bank553 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig189, sig250]
def bank554 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig189, sig251]
def bank555 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig190]
def bank556 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig190, sig252]
def bank557 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig190, sig253]
def bank558 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig190, sig254]
def bank559 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig190, sig255]
def bank560 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig190, sig256]
def bank561 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig190, sig257]
def bank562 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig190, sig258]
def bank563 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig190, sig259]
def bank564 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig190, sig260]
def bank565 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig190, sig261]
def bank566 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig190, sig262]
def bank567 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig190, sig263]
def bank568 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig191]
def bank569 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig191, sig264]
def bank570 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig191, sig265]
def bank571 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig191, sig266]
def bank572 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig191, sig267]
def bank573 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig191, sig268]
def bank574 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig191, sig269]
def bank575 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig191, sig270]
def bank576 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig191, sig271]
def bank577 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig191, sig272]
def bank578 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig191, sig273]
def bank579 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig191, sig274]
def bank580 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig191, sig275]
def bank581 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig192]
def bank582 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig193]
def bank583 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig194]
def bank584 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig195]
def bank585 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig196]
def bank586 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig197]
def bank587 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig198]
def bank588 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig199]
def bank589 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig200]
def bank590 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig201]
def bank591 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig202]
def bank592 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig203]
def bank593 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig204]
def bank594 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig205]
def bank595 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig206]
def bank596 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig207]
def bank597 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig208]
def bank598 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig209]
def bank599 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig210]
def bank600 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig211]
def bank601 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig212]
def bank602 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig213]
def bank603 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig214]
def bank604 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig215]
def bank605 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig216]
def bank606 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig217]
def bank607 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig218]
def bank608 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig219]
def bank609 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig220]
def bank610 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig221]
def bank611 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig222]
def bank612 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig223]
def bank613 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig224]
def bank614 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig225]
def bank615 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig226]
def bank616 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig227]
def bank617 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig228]
def bank618 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig229]
def bank619 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig230]
def bank620 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig231]
def bank621 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig232]
def bank622 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig233]
def bank623 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig234]
def bank624 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig235]
def bank625 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig236]
def bank626 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig237]
def bank627 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig238]
def bank628 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig239]
def bank629 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig240]
def bank630 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig241]
def bank631 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig242]
def bank632 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig243]
def bank633 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig244]
def bank634 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig245]
def bank635 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig246]
def bank636 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig247]
def bank637 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig248]
def bank638 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig249]
def bank639 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig250]
def bank640 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig251]
def bank641 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig252]
def bank642 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig253]
def bank643 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig254]
def bank644 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig255]
def bank645 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig256]
def bank646 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig257]
def bank647 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig258]
def bank648 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig259]
def bank649 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig260]
def bank650 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig261]
def bank651 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig262]
def bank652 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig263]
def bank653 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig264]
def bank654 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig265]
def bank655 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig266]
def bank656 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig267]
def bank657 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig268]
def bank658 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig269]
def bank659 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig270]
def bank660 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig271]
def bank661 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig272]
def bank662 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig273]
def bank663 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig274]
def bank664 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig275]
def bank665 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig276]
def bank666 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig277]
def bank667 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig278]
def bank668 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig279]
def bank669 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig280]
def bank670 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig281]
def bank671 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig282]
def bank672 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig283]
def bank673 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig284]
def bank674 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig285]
def bank675 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig286]
def bank676 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig287]
def bank677 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig288]
def bank678 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig289]
def bank679 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig290]
def bank680 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig291]
def bank681 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig6, sig292]
def bank682 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig11, sig101]
def bank683 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig13, sig121]
def bank684 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig15, sig126]
def bank685 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig17, sig18]
def bank686 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig18, sig42]
def bank687 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig18, sig46]
def bank688 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig18, sig48]
def bank689 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig23, sig172]
def bank690 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig25, sig176]
def bank691 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig28, sig48]
def bank692 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig33, sig144]
def bank693 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig35, sig36]
def bank694 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig36, sig48]
def bank695 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig41, sig42]
def bank696 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig47, sig48]
def bank697 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig101]
def bank698 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig121]
def bank699 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig126]
def bank700 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig144]
def bank701 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig172]
def bank702 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig5, sig176]
def bank703 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig11, sig100]
def bank704 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig13, sig111]
def bank705 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig15, sig16]
def bank706 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig16, sig40]
def bank707 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig16, sig44]
def bank708 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig16, sig48]
def bank709 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig17, sig133]
def bank710 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig23, sig170]
def bank711 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig25, sig26]
def bank712 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig26, sig44]
def bank713 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig33, sig34]
def bank714 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig34, sig48]
def bank715 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig35, sig147]
def bank716 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig39, sig40]
def bank717 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig40, sig48]
def bank718 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig41, sig150]
def bank719 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig43, sig44]
def bank720 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig47, sig48]
def bank721 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig100]
def bank722 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig111]
def bank723 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig133]
def bank724 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig147]
def bank725 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig150]
def bank726 : List Sig := [sig0, sig1, sig2, sig3, sig4, sig6, sig170]
def bank727 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig7, sig44]
def bank728 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig8, sig44]
def bank729 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig8, sig57]
def bank730 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig9, sig44]
def bank731 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig10, sig44]
def bank732 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig11, sig44]
def bank733 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig11, sig98]
def bank734 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig12, sig44]
def bank735 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig13, sig14]
def bank736 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig13, sig23]
def bank737 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig13, sig44]
def bank738 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig14, sig44]
def bank739 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig15, sig44]
def bank740 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig15, sig122]
def bank741 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig16, sig44]
def bank742 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig17, sig44]
def bank743 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig17, sig123]
def bank744 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig18, sig44]
def bank745 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig19, sig44]
def bank746 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig20, sig44]
def bank747 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig21, sig44]
def bank748 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig22, sig44]
def bank749 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig23, sig24]
def bank750 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig23, sig38]
def bank751 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig23, sig44]
def bank752 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig23, sig46]
def bank753 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig24, sig44]
def bank754 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig25, sig44]
def bank755 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig25, sig175]
def bank756 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig26, sig44]
def bank757 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig27, sig44]
def bank758 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig28, sig44]
def bank759 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig29, sig44]
def bank760 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig30, sig44]
def bank761 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig31, sig44]
def bank762 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig32, sig44]
def bank763 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig33, sig44]
def bank764 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig33, sig143]
def bank765 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig34, sig44]
def bank766 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig35, sig44]
def bank767 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig35, sig146]
def bank768 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig36, sig44]
def bank769 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig37, sig44]
def bank770 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig38, sig44]
def bank771 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig39, sig44]
def bank772 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig40, sig44]
def bank773 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig41, sig44]
def bank774 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig41, sig152]
def bank775 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig42, sig44]
def bank776 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig43, sig44]
def bank777 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44]
def bank778 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig45]
def bank779 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig46]
def bank780 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig47]
def bank781 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig48]
def bank782 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig77]
def bank783 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig80]
def bank784 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig81]
def bank785 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig82]
def bank786 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig83]
def bank787 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig84]
def bank788 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig85]
def bank789 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig86]
def bank790 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig90]
def bank791 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig91]
def bank792 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig185]
def bank793 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig186]
def bank794 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig187]
def bank795 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig188]
def bank796 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig189]
def bank797 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig190]
def bank798 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig191]
def bank799 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig44, sig279]
def bank800 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig47, sig159]
def bank801 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig57]
def bank802 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig98]
def bank803 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig122]
def bank804 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig123]
def bank805 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig143]
def bank806 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig146]
def bank807 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig152]
def bank808 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig159]
def bank809 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig175]
def bank810 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig190, sig260]
def bank811 : List Sig := [sig0, sig1, sig2, sig3, sig5, sig6, sig260]
def bank812 : List Sig := [sig0, sig1, sig2, sig3, sig6, sig16, sig44]
def bank813 : List Sig := [sig0, sig1, sig2, sig3, sig6, sig26, sig44]
def bank814 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig7, sig40]
def bank815 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig8, sig40]
def bank816 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig9, sig40]
def bank817 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig10, sig40]
def bank818 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig11, sig12]
def bank819 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig11, sig30]
def bank820 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig11, sig40]
def bank821 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig11, sig41]
def bank822 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig12, sig40]
def bank823 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig13, sig40]
def bank824 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig13, sig118]
def bank825 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig14, sig40]
def bank826 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig15, sig40]
def bank827 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig15, sig125]
def bank828 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig16, sig40]
def bank829 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig17, sig40]
def bank830 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig17, sig135]
def bank831 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig18, sig40]
def bank832 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig18, sig103]
def bank833 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig19, sig40]
def bank834 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig20, sig40]
def bank835 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig21, sig40]
def bank836 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig22, sig40]
def bank837 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig23, sig40]
def bank838 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig23, sig168]
def bank839 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig24, sig40]
def bank840 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig25, sig40]
def bank841 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig25, sig174]
def bank842 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig26, sig40]
def bank843 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig27, sig40]
def bank844 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig28, sig40]
def bank845 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig29, sig40]
def bank846 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig30, sig40]
def bank847 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig31, sig40]
def bank848 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig32, sig40]
def bank849 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig33, sig40]
def bank850 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig33, sig142]
def bank851 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig34, sig40]
def bank852 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig35, sig40]
def bank853 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig35, sig145]
def bank854 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig36, sig40]
def bank855 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig37, sig40]
def bank856 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig38, sig40]
def bank857 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig38, sig41]
def bank858 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig39, sig40]
def bank859 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40]
def bank860 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig41]
def bank861 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig42]
def bank862 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig43]
def bank863 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig44]
def bank864 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig45]
def bank865 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig46]
def bank866 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig47]
def bank867 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig48]
def bank868 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig72]
def bank869 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig73]
def bank870 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig74]
def bank871 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig75]
def bank872 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig76]
def bank873 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig77]
def bank874 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig78]
def bank875 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig79]
def bank876 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig87]
def bank877 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig88]
def bank878 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig185]
def bank879 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig186]
def bank880 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig187]
def bank881 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig188]
def bank882 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig189]
def bank883 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig190]
def bank884 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig191]
def bank885 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig40, sig278]
def bank886 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig41, sig42]
def bank887 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig47, sig158]
def bank888 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig103]
def bank889 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig118]
def bank890 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig125]
def bank891 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig135]
def bank892 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig142]
def bank893 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig145]
def bank894 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig158]
def bank895 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig168]
def bank896 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig174]
def bank897 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig190, sig258]
def bank898 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig6, sig258]
def bank899 : List Sig := [sig0, sig1, sig2, sig4, sig5, sig41, sig42]
def bank900 : List Sig := [sig0, sig1, sig2, sig4, sig6, sig16, sig40]
def bank901 : List Sig := [sig0, sig1, sig2, sig4, sig6, sig40, sig48]
def bank902 : List Sig := [sig0, sig1, sig2, sig5, sig6, sig40, sig44]
def bank903 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig7, sig10]
def bank904 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig8, sig10]
def bank905 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig9, sig10]
def bank906 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10]
def bank907 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig11]
def bank908 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig12]
def bank909 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig13]
def bank910 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig14]
def bank911 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig15]
def bank912 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig16]
def bank913 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig17]
def bank914 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig18]
def bank915 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig19]
def bank916 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig20]
def bank917 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig21]
def bank918 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig22]
def bank919 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig23]
def bank920 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig24]
def bank921 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig25]
def bank922 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig26]
def bank923 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig27]
def bank924 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig28]
def bank925 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig29]
def bank926 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig30]
def bank927 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig31]
def bank928 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig32]
def bank929 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig33]
def bank930 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig34]
def bank931 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig35]
def bank932 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig36]
def bank933 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig37]
def bank934 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig38]
def bank935 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig39]
def bank936 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig40]
def bank937 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig41]
def bank938 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig42]
def bank939 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig43]
def bank940 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig44]
def bank941 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig45]
def bank942 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig46]
def bank943 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig47]
def bank944 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig48]
def bank945 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig54]
def bank946 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig63]
def bank947 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig64]
def bank948 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig65]
def bank949 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig66]
def bank950 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig67]
def bank951 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig68]
def bank952 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig69]
def bank953 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig70]
def bank954 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig71]
def bank955 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig185]
def bank956 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig186]
def bank957 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig187]
def bank958 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig188]
def bank959 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig189]
def bank960 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig190]
def bank961 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig191]
def bank962 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig10, sig277]
def bank963 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig11, sig116]
def bank964 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig13, sig117]
def bank965 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig15, sig124]
def bank966 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig17, sig134]
def bank967 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig20, sig35]
def bank968 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig23, sig167]
def bank969 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig25, sig173]
def bank970 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig30, sig33]
def bank971 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig33, sig34]
def bank972 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig33, sig35]
def bank973 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig35, sig36]
def bank974 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig41, sig151]
def bank975 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig47, sig157]
def bank976 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig48, sig129]
def bank977 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig116]
def bank978 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig117]
def bank979 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig124]
def bank980 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig129]
def bank981 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig134]
def bank982 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig151]
def bank983 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig157]
def bank984 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig167]
def bank985 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig173]
def bank986 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig185, sig194]
def bank987 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig6, sig194]
def bank988 : List Sig := [sig0, sig1, sig3, sig4, sig5, sig35, sig36]
def bank989 : List Sig := [sig0, sig1, sig3, sig5, sig6, sig10, sig44]
def bank990 : List Sig := [sig0, sig1, sig4, sig5, sig6, sig10, sig40]
def bank991 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank992 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8]
def bank993 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig9]
def bank994 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig10]
def bank995 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig11]
def bank996 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig12]
def bank997 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig13]
def bank998 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig14]
def bank999 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig15]
def bank1000 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig16]
def bank1001 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig17]
def bank1002 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig18]
def bank1003 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig19]
def bank1004 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig20]
def bank1005 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig21]
def bank1006 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig22]
def bank1007 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig23]
def bank1008 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig24]
def bank1009 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig25]
def bank1010 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig26]
def bank1011 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig27]
def bank1012 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig28]
def bank1013 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig29]
def bank1014 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig30]
def bank1015 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig31]
def bank1016 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig32]
def bank1017 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig33]
def bank1018 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig34]
def bank1019 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig35]
def bank1020 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig36]
def bank1021 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig37]
def bank1022 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig38]
def bank1023 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig39]
def bank1024 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig40]
def bank1025 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig41]
def bank1026 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig42]
def bank1027 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig43]
def bank1028 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig44]
def bank1029 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig45]
def bank1030 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig46]
def bank1031 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig47]
def bank1032 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig48]
def bank1033 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig53]
def bank1034 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig54]
def bank1035 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig55]
def bank1036 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig56]
def bank1037 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig57]
def bank1038 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig58]
def bank1039 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig59]
def bank1040 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig60]
def bank1041 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig61]
def bank1042 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig62]
def bank1043 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig185]
def bank1044 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig186]
def bank1045 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig187]
def bank1046 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig188]
def bank1047 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig189]
def bank1048 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig190]
def bank1049 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig191]
def bank1050 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig8, sig276]
def bank1051 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig11, sig166]
def bank1052 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig13, sig160]
def bank1053 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig15, sig178]
def bank1054 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig17, sig179]
def bank1055 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig20, sig23]
def bank1056 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig23, sig24]
def bank1057 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig23, sig25]
def bank1058 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig23, sig28]
def bank1059 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig25, sig26]
def bank1060 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig33, sig183]
def bank1061 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig35, sig184]
def bank1062 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig41, sig181]
def bank1063 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig44, sig82]
def bank1064 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig47, sig182]
def bank1065 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig82]
def bank1066 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig160]
def bank1067 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig166]
def bank1068 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig178]
def bank1069 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig179]
def bank1070 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig181]
def bank1071 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig182]
def bank1072 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig183]
def bank1073 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig184]
def bank1074 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig185, sig192]
def bank1075 : List Sig := [sig0, sig2, sig3, sig4, sig5, sig6, sig192]
def bank1076 : List Sig := [sig0, sig2, sig3, sig5, sig6, sig8, sig44]
def bank1077 : List Sig := [sig0, sig2, sig3, sig5, sig6, sig8, sig57]
def bank1078 : List Sig := [sig0, sig2, sig3, sig5, sig6, sig44, sig82]
def bank1079 : List Sig := [sig0, sig2, sig4, sig5, sig6, sig8, sig40]
def bank1080 : List Sig := [sig0, sig3, sig4, sig5, sig6, sig8, sig10]
def bank1081 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig7, sig8]
def bank1082 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig8, sig14]
def bank1083 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig8, sig16]
def bank1084 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig9, sig10]
def bank1085 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig10, sig16]
def bank1086 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig10, sig18]
def bank1087 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig11, sig12]
def bank1088 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig12, sig18]
def bank1089 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig13, sig14]
def bank1090 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig15, sig16]
def bank1091 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig16, sig18]
def bank1092 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig17, sig18]
def bank1093 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig23, sig105]
def bank1094 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig25, sig109]
def bank1095 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig33, sig110]
def bank1096 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig35, sig115]
def bank1097 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig41, sig137]
def bank1098 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig47, sig156]
def bank1099 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig105]
def bank1100 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig109]
def bank1101 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig110]
def bank1102 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig115]
def bank1103 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig137]
def bank1104 : List Sig := [sig1, sig2, sig3, sig4, sig5, sig6, sig156]
def bank1105 : List Sig := [sig1, sig3, sig4, sig5, sig6, sig10, sig16]
def bank1106 : List Sig := [sig1, sig3, sig4, sig5, sig6, sig10, sig18]
def bank1107 : List Sig := [sig2, sig3, sig4, sig5, sig6, sig8, sig14]
def bank1108 : List Sig := [sig2, sig3, sig4, sig5, sig6, sig8, sig16]

set_option maxRecDepth 24000 in
theorem excluded640 : Blocked 8 0 bank859 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded651 : Blocked 8 0 bank906 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1202 : Blocked 9 1 bank18 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1232 : Blocked 9 1 bank269 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1200 : Blocked 9 1 bank1 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded227 : Blocked 8 0 bank137 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1236 : Blocked 9 1 bank303 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1207 : Blocked 9 1 bank61 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1219 : Blocked 9 1 bank163 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded125 : Blocked 8 0 bank35 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded309 : Blocked 8 0 bank219 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1214 : Blocked 9 1 bank121 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1224 : Blocked 9 1 bank203 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1229 : Blocked 9 1 bank245 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1235 : Blocked 9 1 bank295 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded650 : Blocked 8 0 bank898 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded661 : Blocked 8 0 bank987 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1221 : Blocked 9 1 bank179 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1239 : Blocked 9 1 bank328 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded168 : Blocked 8 0 bank78 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded186 : Blocked 8 0 bank96 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded435 : Blocked 8 0 bank345 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded326 : Blocked 8 0 bank236 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded376 : Blocked 8 0 bank286 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1213 : Blocked 9 1 bank113 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1231 : Blocked 9 1 bank261 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded639 : Blocked 8 0 bank811 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded672 : Blocked 8 0 bank1075 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1205 : Blocked 9 1 bank44 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1227 : Blocked 9 1 bank228 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1223 : Blocked 9 1 bank195 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded99 : Blocked 8 0 bank9 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded401 : Blocked 8 0 bank311 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded142 : Blocked 8 0 bank52 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded244 : Blocked 8 0 bank154 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1160 : Blocked 8 1 bank1077 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1161 : Blocked 8 1 bank1078 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded630 : Blocked 8 0 bank792 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded668 : Blocked 8 0 bank1048 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1159 : Blocked 8 1 bank1076 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1220 : Blocked 9 1 bank171 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1238 : Blocked 9 1 bank320 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded600 : Blocked 8 0 bank653 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded610 : Blocked 8 0 bank663 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1230 : Blocked 9 1 bank253 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded536 : Blocked 8 0 bank589 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded588 : Blocked 8 0 bank641 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1212 : Blocked 9 1 bank105 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded919 : Blocked 8 1 bank801 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1150 : Blocked 8 1 bank1065 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1222 : Blocked 9 1 bank187 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1215 : Blocked 9 1 bank129 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1225 : Blocked 9 1 bank211 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded619 : Blocked 8 0 bank672 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded627 : Blocked 8 0 bank680 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded628 : Blocked 8 0 bank681 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1217 : Blocked 9 1 bank146 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded641 : Blocked 8 0 bank878 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded657 : Blocked 8 0 bank960 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded635 : Blocked 8 0 bank797 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded663 : Blocked 8 0 bank1043 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded637 : Blocked 8 0 bank799 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded670 : Blocked 8 0 bank1050 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded540 : Blocked 8 0 bank593 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded584 : Blocked 8 0 bank637 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded995 : Blocked 8 1 bank888 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1076 : Blocked 8 1 bank980 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded177 : Blocked 8 0 bank87 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded426 : Blocked 8 0 bank336 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded159 : Blocked 8 0 bank69 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded552 : Blocked 8 0 bank605 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded572 : Blocked 8 0 bank625 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded928 : Blocked 8 1 bank812 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1191 : Blocked 8 1 bank1108 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded548 : Blocked 8 0 bank601 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded576 : Blocked 8 0 bank629 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded620 : Blocked 8 0 bank673 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded530 : Blocked 8 0 bank583 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded594 : Blocked 8 0 bank647 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded616 : Blocked 8 0 bank669 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded623 : Blocked 8 0 bank676 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded646 : Blocked 8 0 bank883 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded652 : Blocked 8 0 bank955 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1005 : Blocked 8 1 bank900 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1188 : Blocked 8 1 bank1105 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded624 : Blocked 8 0 bank677 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded625 : Blocked 8 0 bank678 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded602 : Blocked 8 0 bank655 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded608 : Blocked 8 0 bank661 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded631 : Blocked 8 0 bank793 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded667 : Blocked 8 0 bank1047 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded169 : Blocked 8 0 bank79 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded174 : Blocked 8 0 bank84 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded150 : Blocked 8 0 bank60 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded252 : Blocked 8 0 bank162 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded528 : Blocked 8 0 bank581 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded560 : Blocked 8 0 bank613 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded564 : Blocked 8 0 bank617 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded596 : Blocked 8 0 bank649 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded647 : Blocked 8 0 bank884 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded658 : Blocked 8 0 bank961 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded235 : Blocked 8 0 bank145 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded535 : Blocked 8 0 bank588 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded591 : Blocked 8 0 bank644 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded636 : Blocked 8 0 bank798 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded669 : Blocked 8 0 bank1049 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded116 : Blocked 8 0 bank26 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded367 : Blocked 8 0 bank277 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded533 : Blocked 8 0 bank586 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded593 : Blocked 8 0 bank646 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded167 : Blocked 8 0 bank77 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded269 : Blocked 8 0 bank179 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded418 : Blocked 8 0 bank328 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded634 : Blocked 8 0 bank796 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded664 : Blocked 8 0 bank1044 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded133 : Blocked 8 0 bank43 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded175 : Blocked 8 0 bank85 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded317 : Blocked 8 0 bank227 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded334 : Blocked 8 0 bank244 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded384 : Blocked 8 0 bank294 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded539 : Blocked 8 0 bank592 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded599 : Blocked 8 0 bank652 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1083 : Blocked 8 1 bank989 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1162 : Blocked 8 1 bank1079 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded203 : Blocked 8 0 bank113 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded351 : Blocked 8 0 bank261 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1084 : Blocked 8 1 bank990 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded553 : Blocked 8 0 bank606 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded573 : Blocked 8 0 bank626 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded537 : Blocked 8 0 bank590 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded550 : Blocked 8 0 bank603 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded586 : Blocked 8 0 bank639 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded589 : Blocked 8 0 bank642 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded622 : Blocked 8 0 bank675 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded626 : Blocked 8 0 bank679 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded85 : Blocked 7 0 bank1077 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded86 : Blocked 7 0 bank1078 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded185 : Blocked 8 0 bank95 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded434 : Blocked 8 0 bank344 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded648 : Blocked 8 0 bank885 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded659 : Blocked 8 0 bank962 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded644 : Blocked 8 0 bank881 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded654 : Blocked 8 0 bank957 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded151 : Blocked 8 0 bank61 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded253 : Blocked 8 0 bank163 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded134 : Blocked 8 0 bank44 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded318 : Blocked 8 0 bank228 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded234 : Blocked 8 0 bank144 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded538 : Blocked 8 0 bank591 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded598 : Blocked 8 0 bank651 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded131 : Blocked 8 0 bank41 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded310 : Blocked 8 0 bank220 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded335 : Blocked 8 0 bank245 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded385 : Blocked 8 0 bank295 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded632 : Blocked 8 0 bank794 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded666 : Blocked 8 0 bank1046 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded554 : Blocked 8 0 bank607 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded570 : Blocked 8 0 bank623 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded211 : Blocked 8 0 bank121 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded293 : Blocked 8 0 bank203 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded547 : Blocked 8 0 bank600 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded579 : Blocked 8 0 bank632 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded633 : Blocked 8 0 bank795 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded665 : Blocked 8 0 bank1045 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded285 : Blocked 8 0 bank195 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded544 : Blocked 8 0 bank597 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded580 : Blocked 8 0 bank633 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded603 : Blocked 8 0 bank656 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded609 : Blocked 8 0 bank662 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded91 : Blocked 8 0 bank1 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded108 : Blocked 8 0 bank18 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded359 : Blocked 8 0 bank269 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded393 : Blocked 8 0 bank303 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded542 : Blocked 8 0 bank595 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded551 : Blocked 8 0 bank604 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded556 : Blocked 8 0 bank609 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded562 : Blocked 8 0 bank615 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded568 : Blocked 8 0 bank621 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded574 : Blocked 8 0 bank627 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded582 : Blocked 8 0 bank635 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded587 : Blocked 8 0 bank640 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded642 : Blocked 8 0 bank879 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded643 : Blocked 8 0 bank880 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded655 : Blocked 8 0 bank958 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded656 : Blocked 8 0 bank959 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded228 : Blocked 8 0 bank138 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded233 : Blocked 8 0 bank143 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded559 : Blocked 8 0 bank612 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded567 : Blocked 8 0 bank620 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded84 : Blocked 7 0 bank1076 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded261 : Blocked 8 0 bank171 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded410 : Blocked 8 0 bank320 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded605 : Blocked 8 0 bank658 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded607 : Blocked 8 0 bank660 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded541 : Blocked 8 0 bank594 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded585 : Blocked 8 0 bank638 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded612 : Blocked 8 0 bank665 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded615 : Blocked 8 0 bank668 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded853 : Blocked 8 1 bank726 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1182 : Blocked 8 1 bank1099 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded126 : Blocked 8 0 bank36 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded143 : Blocked 8 0 bank53 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded160 : Blocked 8 0 bank70 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded165 : Blocked 8 0 bank75 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded178 : Blocked 8 0 bank88 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded250 : Blocked 8 0 bank160 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded315 : Blocked 8 0 bank225 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded432 : Blocked 8 0 bank342 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded618 : Blocked 8 0 bank671 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded621 : Blocked 8 0 bank674 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded649 : Blocked 8 0 bank897 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded660 : Blocked 8 0 bank986 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded148 : Blocked 8 0 bank58 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded170 : Blocked 8 0 bank80 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded173 : Blocked 8 0 bank83 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded245 : Blocked 8 0 bank155 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded327 : Blocked 8 0 bank237 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded382 : Blocked 8 0 bank292 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded529 : Blocked 8 0 bank582 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded531 : Blocked 8 0 bank584 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded558 : Blocked 8 0 bank611 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded566 : Blocked 8 0 bank619 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded595 : Blocked 8 0 bank648 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded597 : Blocked 8 0 bank650 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded638 : Blocked 8 0 bank810 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded645 : Blocked 8 0 bank882 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded653 : Blocked 8 0 bank956 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded671 : Blocked 8 0 bank1074 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1007 : Blocked 8 1 bank902 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1163 : Blocked 8 1 bank1080 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded171 : Blocked 8 0 bank81 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded172 : Blocked 8 0 bank82 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1006 : Blocked 8 1 bank901 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1189 : Blocked 8 1 bank1106 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded332 : Blocked 8 0 bank242 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded377 : Blocked 8 0 bank287 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded534 : Blocked 8 0 bank587 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded590 : Blocked 8 0 bank643 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded824 : Blocked 8 1 bank697 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded827 : Blocked 8 1 bank700 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded851 : Blocked 8 1 bank724 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1186 : Blocked 8 1 bank1103 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded105 : Blocked 8 0 bank15 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded402 : Blocked 8 0 bank312 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded561 : Blocked 8 0 bank614 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded563 : Blocked 8 0 bank616 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded565 : Blocked 8 0 bank618 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded575 : Blocked 8 0 bank628 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded192 : Blocked 8 0 bank102 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded436 : Blocked 8 0 bank346 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded549 : Blocked 8 0 bank602 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded577 : Blocked 8 0 bank630 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded195 : Blocked 8 0 bank105 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded343 : Blocked 8 0 bank253 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded532 : Blocked 8 0 bank585 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded545 : Blocked 8 0 bank598 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded581 : Blocked 8 0 bank634 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded592 : Blocked 8 0 bank645 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded601 : Blocked 8 0 bank654 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded604 : Blocked 8 0 bank657 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded606 : Blocked 8 0 bank659 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded611 : Blocked 8 0 bank664 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded546 : Blocked 8 0 bank599 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded578 : Blocked 8 0 bank631 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded848 : Blocked 8 1 bank721 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded920 : Blocked 8 1 bank802 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1004 : Blocked 8 1 bank899 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1082 : Blocked 8 1 bank988 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1157 : Blocked 8 1 bank1072 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1184 : Blocked 8 1 bank1101 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded277 : Blocked 8 0 bank187 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded929 : Blocked 8 1 bank813 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1190 : Blocked 8 1 bank1107 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded183 : Blocked 8 0 bank93 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded219 : Blocked 8 0 bank129 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded301 : Blocked 8 0 bank211 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded427 : Blocked 8 0 bank337 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded583 : Blocked 8 0 bank636 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded909 : Blocked 8 1 bank783 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1132 : Blocked 8 1 bank1039 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded106 : Blocked 8 0 bank16 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded408 : Blocked 8 0 bank318 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded557 : Blocked 8 0 bank610 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded569 : Blocked 8 0 bank622 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded571 : Blocked 8 0 bank624 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded911 : Blocked 8 1 bank785 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded937 : Blocked 8 1 bank821 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1068 : Blocked 8 1 bank972 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1130 : Blocked 8 1 bank1037 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded187 : Blocked 8 0 bank97 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded441 : Blocked 8 0 bank351 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded543 : Blocked 8 0 bank596 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded176 : Blocked 8 0 bank86 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded555 : Blocked 8 0 bank608 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded852 : Blocked 8 1 bank725 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1000 : Blocked 8 1 bank893 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1078 : Blocked 8 1 bank982 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1185 : Blocked 8 1 bank1102 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded328 : Blocked 8 0 bank238 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded381 : Blocked 8 0 bank291 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded452 : Blocked 8 0 bank499 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded504 : Blocked 8 0 bank556 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded613 : Blocked 8 0 bank666 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded614 : Blocked 8 0 bank667 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded850 : Blocked 8 1 bank723 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded890 : Blocked 8 1 bank763 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded998 : Blocked 8 1 bank891 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1079 : Blocked 8 1 bank983 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1088 : Blocked 8 1 bank995 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1187 : Blocked 8 1 bank1104 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded617 : Blocked 8 0 bank670 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded761 : Blocked 8 1 bank442 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded771 : Blocked 8 1 bank452 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded868 : Blocked 8 1 bank741 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1093 : Blocked 8 1 bank1000 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded128 : Blocked 8 0 bank38 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded144 : Blocked 8 0 bank54 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded230 : Blocked 8 0 bank140 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded231 : Blocked 8 0 bank141 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded249 : Blocked 8 0 bank159 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded313 : Blocked 8 0 bank223 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded825 : Blocked 8 1 bank698 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded829 : Blocked 8 1 bank702 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded842 : Blocked 8 1 bank715 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded849 : Blocked 8 1 bank722 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded922 : Blocked 8 1 bank804 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded927 : Blocked 8 1 bank809 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded944 : Blocked 8 1 bank828 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded996 : Blocked 8 1 bank889 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1002 : Blocked 8 1 bank895 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1016 : Blocked 8 1 bank912 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1080 : Blocked 8 1 bank984 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1081 : Blocked 8 1 bank985 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1151 : Blocked 8 1 bank1066 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1156 : Blocked 8 1 bank1071 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1180 : Blocked 8 1 bank1097 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1183 : Blocked 8 1 bank1100 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded236 : Blocked 8 0 bank146 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded855 : Blocked 8 1 bank728 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded864 : Blocked 8 1 bank737 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded989 : Blocked 8 1 bank874 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1057 : Blocked 8 1 bank953 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1102 : Blocked 8 1 bank1009 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1121 : Blocked 8 1 bank1028 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded727 : Blocked 8 1 bank408 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded753 : Blocked 8 1 bank434 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded826 : Blocked 8 1 bank699 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded828 : Blocked 8 1 bank701 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded20 : Blocked 7 0 bank763 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded40 : Blocked 7 0 bank812 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded42 : Blocked 7 0 bank902 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded46 : Blocked 7 0 bank995 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded88 : Blocked 7 0 bank1080 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded90 : Blocked 7 0 bank1108 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded100 : Blocked 8 0 bank10 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded407 : Blocked 8 0 bank317 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded812 : Blocked 8 1 bank685 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded823 : Blocked 8 1 bank696 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded845 : Blocked 8 1 bank718 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded921 : Blocked 8 1 bank803 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded924 : Blocked 8 1 bank806 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded982 : Blocked 8 1 bank867 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded983 : Blocked 8 1 bank868 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded997 : Blocked 8 1 bank890 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1001 : Blocked 8 1 bank894 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1018 : Blocked 8 1 bank914 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1055 : Blocked 8 1 bank951 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1075 : Blocked 8 1 bank979 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1077 : Blocked 8 1 bank981 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1153 : Blocked 8 1 bank1068 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1155 : Blocked 8 1 bank1070 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1179 : Blocked 8 1 bank1096 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded43 : Blocked 7 0 bank989 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded87 : Blocked 7 0 bank1079 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded104 : Blocked 8 0 bank14 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded190 : Blocked 8 0 bank100 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded403 : Blocked 8 0 bank313 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded405 : Blocked 8 0 bank315 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded438 : Blocked 8 0 bank348 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded681 : Blocked 8 1 bank362 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded706 : Blocked 8 1 bank387 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded894 : Blocked 8 1 bank767 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded965 : Blocked 8 1 bank849 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded981 : Blocked 8 1 bank866 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1011 : Blocked 8 1 bank907 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1017 : Blocked 8 1 bank913 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1147 : Blocked 8 1 bank1062 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded102 : Blocked 8 0 bank12 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded194 : Blocked 8 0 bank104 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded443 : Blocked 8 0 bank353 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded906 : Blocked 8 1 bank780 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded923 : Blocked 8 1 bank805 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded925 : Blocked 8 1 bank807 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded926 : Blocked 8 1 bank808 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded969 : Blocked 8 1 bank853 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded999 : Blocked 8 1 bank892 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1003 : Blocked 8 1 bank896 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1070 : Blocked 8 1 bank974 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1073 : Blocked 8 1 bank977 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1074 : Blocked 8 1 bank978 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1094 : Blocked 8 1 bank1001 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1152 : Blocked 8 1 bank1067 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1154 : Blocked 8 1 bank1069 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1158 : Blocked 8 1 bank1073 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded31 : Blocked 7 0 bank783 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded80 : Blocked 7 0 bank1039 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded122 : Blocked 8 0 bank32 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded184 : Blocked 8 0 bank94 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded333 : Blocked 8 0 bank243 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded368 : Blocked 8 0 bank278 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded383 : Blocked 8 0 bank293 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded433 : Blocked 8 0 bank343 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded901 : Blocked 8 1 bank774 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded907 : Blocked 8 1 bank781 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded947 : Blocked 8 1 bank831 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1048 : Blocked 8 1 bank944 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1095 : Blocked 8 1 bank1002 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1146 : Blocked 8 1 bank1061 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded129 : Blocked 8 0 bank39 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded157 : Blocked 8 0 bank67 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded212 : Blocked 8 0 bank122 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded217 : Blocked 8 0 bank127 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded254 : Blocked 8 0 bank164 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded294 : Blocked 8 0 bank204 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded299 : Blocked 8 0 bank209 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded312 : Blocked 8 0 bank222 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded329 : Blocked 8 0 bank239 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded380 : Blocked 8 0 bank290 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded694 : Blocked 8 1 bank375 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded702 : Blocked 8 1 bank383 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded732 : Blocked 8 1 bank413 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded879 : Blocked 8 1 bank752 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded893 : Blocked 8 1 bank766 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded968 : Blocked 8 1 bank852 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1041 : Blocked 8 1 bank937 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1118 : Blocked 8 1 bank1025 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1143 : Blocked 8 1 bank1058 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded33 : Blocked 7 0 bank785 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded78 : Blocked 7 0 bank1037 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded97 : Blocked 8 0 bank7 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded114 : Blocked 8 0 bank24 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded127 : Blocked 8 0 bank37 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded130 : Blocked 8 0 bank40 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded132 : Blocked 8 0 bank42 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded145 : Blocked 8 0 bank55 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded146 : Blocked 8 0 bank56 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded149 : Blocked 8 0 bank59 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded161 : Blocked 8 0 bank71 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded162 : Blocked 8 0 bank72 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded163 : Blocked 8 0 bank73 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded164 : Blocked 8 0 bank74 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded179 : Blocked 8 0 bank89 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded180 : Blocked 8 0 bank90 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded182 : Blocked 8 0 bank92 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded247 : Blocked 8 0 bank157 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded248 : Blocked 8 0 bank158 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded251 : Blocked 8 0 bank161 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded311 : Blocked 8 0 bank221 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded314 : Blocked 8 0 bank224 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded316 : Blocked 8 0 bank226 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded330 : Blocked 8 0 bank240 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded331 : Blocked 8 0 bank241 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded360 : Blocked 8 0 bank270 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded378 : Blocked 8 0 bank288 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded379 : Blocked 8 0 bank289 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded394 : Blocked 8 0 bank304 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded428 : Blocked 8 0 bank338 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded430 : Blocked 8 0 bank340 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded431 : Blocked 8 0 bank341 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded729 : Blocked 8 1 bank410 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded794 : Blocked 8 1 bank475 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded809 : Blocked 8 1 bank682 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded811 : Blocked 8 1 bank684 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded819 : Blocked 8 1 bank692 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded856 : Blocked 8 1 bank729 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded863 : Blocked 8 1 bank736 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1142 : Blocked 8 1 bank1057 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1148 : Blocked 8 1 bank1063 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded41 : Blocked 7 0 bank813 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded89 : Blocked 7 0 bank1107 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded107 : Blocked 8 0 bank17 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded152 : Blocked 8 0 bank62 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded158 : Blocked 8 0 bank68 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded259 : Blocked 8 0 bank169 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded260 : Blocked 8 0 bank170 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded409 : Blocked 8 0 bank319 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded449 : Blocked 8 0 bank496 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded451 : Blocked 8 0 bank498 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded453 : Blocked 8 0 bank500 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded455 : Blocked 8 0 bank502 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded505 : Blocked 8 0 bank557 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded507 : Blocked 8 0 bank559 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded509 : Blocked 8 0 bank561 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded515 : Blocked 8 0 bank567 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded683 : Blocked 8 1 bank364 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded704 : Blocked 8 1 bank385 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded731 : Blocked 8 1 bank412 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded738 : Blocked 8 1 bank419 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded751 : Blocked 8 1 bank432 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded810 : Blocked 8 1 bank683 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded817 : Blocked 8 1 bank690 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded831 : Blocked 8 1 bank704 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded836 : Blocked 8 1 bank709 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded837 : Blocked 8 1 bank710 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded878 : Blocked 8 1 bank751 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded881 : Blocked 8 1 bank754 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded882 : Blocked 8 1 bank755 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded939 : Blocked 8 1 bank823 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded940 : Blocked 8 1 bank824 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded946 : Blocked 8 1 bank830 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded953 : Blocked 8 1 bank837 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1023 : Blocked 8 1 bank919 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1025 : Blocked 8 1 bank921 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1065 : Blocked 8 1 bank969 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1071 : Blocked 8 1 bank975 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1090 : Blocked 8 1 bank997 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1100 : Blocked 8 1 bank1007 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1137 : Blocked 8 1 bank1052 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1176 : Blocked 8 1 bank1093 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1177 : Blocked 8 1 bank1094 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1181 : Blocked 8 1 bank1098 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded92 : Blocked 8 0 bank2 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded103 : Blocked 8 0 bank13 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded109 : Blocked 8 0 bank19 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded147 : Blocked 8 0 bank57 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded189 : Blocked 8 0 bank99 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded191 : Blocked 8 0 bank101 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded193 : Blocked 8 0 bank103 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded229 : Blocked 8 0 bank139 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded232 : Blocked 8 0 bank142 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded246 : Blocked 8 0 bank156 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded365 : Blocked 8 0 bank275 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded399 : Blocked 8 0 bank309 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded404 : Blocked 8 0 bank314 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded437 : Blocked 8 0 bank347 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded439 : Blocked 8 0 bank349 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded442 : Blocked 8 0 bank352 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded692 : Blocked 8 1 bank373 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded696 : Blocked 8 1 bank377 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded721 : Blocked 8 1 bank402 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded724 : Blocked 8 1 bank405 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded733 : Blocked 8 1 bank414 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded734 : Blocked 8 1 bank415 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded735 : Blocked 8 1 bank416 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded757 : Blocked 8 1 bank438 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded780 : Blocked 8 1 bank461 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded816 : Blocked 8 1 bank689 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded830 : Blocked 8 1 bank703 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded859 : Blocked 8 1 bank732 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded860 : Blocked 8 1 bank733 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded866 : Blocked 8 1 bank739 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded867 : Blocked 8 1 bank740 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded900 : Blocked 8 1 bank773 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded934 : Blocked 8 1 bank818 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded936 : Blocked 8 1 bank820 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded942 : Blocked 8 1 bank826 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded943 : Blocked 8 1 bank827 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded954 : Blocked 8 1 bank838 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded956 : Blocked 8 1 bank840 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded957 : Blocked 8 1 bank841 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded975 : Blocked 8 1 bank860 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1013 : Blocked 8 1 bank909 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1015 : Blocked 8 1 bank911 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1033 : Blocked 8 1 bank929 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1035 : Blocked 8 1 bank931 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1060 : Blocked 8 1 bank964 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1061 : Blocked 8 1 bank965 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1064 : Blocked 8 1 bank968 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1067 : Blocked 8 1 bank971 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1092 : Blocked 8 1 bank999 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1110 : Blocked 8 1 bank1017 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1112 : Blocked 8 1 bank1019 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1138 : Blocked 8 1 bank1053 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1145 : Blocked 8 1 bank1060 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1178 : Blocked 8 1 bank1095 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded101 : Blocked 8 0 bank11 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded196 : Blocked 8 0 bank106 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded286 : Blocked 8 0 bank196 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded291 : Blocked 8 0 bank201 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded349 : Blocked 8 0 bank259 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded406 : Blocked 8 0 bank316 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded674 : Blocked 8 1 bank355 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded725 : Blocked 8 1 bank406 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded739 : Blocked 8 1 bank420 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded763 : Blocked 8 1 bank444 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded768 : Blocked 8 1 bank449 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded774 : Blocked 8 1 bank455 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded786 : Blocked 8 1 bank467 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded788 : Blocked 8 1 bank469 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded833 : Blocked 8 1 bank706 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded834 : Blocked 8 1 bank707 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded869 : Blocked 8 1 bank742 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded870 : Blocked 8 1 bank743 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded891 : Blocked 8 1 bank764 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded931 : Blocked 8 1 bank815 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded945 : Blocked 8 1 bank829 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded966 : Blocked 8 1 bank850 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded994 : Blocked 8 1 bank887 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1044 : Blocked 8 1 bank940 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1047 : Blocked 8 1 bank943 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1059 : Blocked 8 1 bank963 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1062 : Blocked 8 1 bank966 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1124 : Blocked 8 1 bank1031 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1136 : Blocked 8 1 bank1051 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1149 : Blocked 8 1 bank1064 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1166 : Blocked 8 1 bank1083 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1168 : Blocked 8 1 bank1085 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded29 : Blocked 7 0 bank781 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded53 : Blocked 7 0 bank1002 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded111 : Blocked 8 0 bank21 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded117 : Blocked 8 0 bank27 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded121 : Blocked 8 0 bank31 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded123 : Blocked 8 0 bank33 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded156 : Blocked 8 0 bank66 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded209 : Blocked 8 0 bank119 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded255 : Blocked 8 0 bank165 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded275 : Blocked 8 0 bank185 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded341 : Blocked 8 0 bank251 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded352 : Blocked 8 0 bank262 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded363 : Blocked 8 0 bank273 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded369 : Blocked 8 0 bank279 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded373 : Blocked 8 0 bank283 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded374 : Blocked 8 0 bank284 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded386 : Blocked 8 0 bank296 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded419 : Blocked 8 0 bank329 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded673 : Blocked 8 1 bank354 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded675 : Blocked 8 1 bank356 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded717 : Blocked 8 1 bank398 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded718 : Blocked 8 1 bank399 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded719 : Blocked 8 1 bank400 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded720 : Blocked 8 1 bank401 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded723 : Blocked 8 1 bank404 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded743 : Blocked 8 1 bank424 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded762 : Blocked 8 1 bank443 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded772 : Blocked 8 1 bank453 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded773 : Blocked 8 1 bank454 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded785 : Blocked 8 1 bank466 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded787 : Blocked 8 1 bank468 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded789 : Blocked 8 1 bank470 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded793 : Blocked 8 1 bank474 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded915 : Blocked 8 1 bank789 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded918 : Blocked 8 1 bank800 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded948 : Blocked 8 1 bank832 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1072 : Blocked 8 1 bank976 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1135 : Blocked 8 1 bank1042 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1139 : Blocked 8 1 bank1054 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded7 : Blocked 7 0 bank741 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded51 : Blocked 7 0 bank1000 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded93 : Blocked 8 0 bank3 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded119 : Blocked 8 0 bank29 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded138 : Blocked 8 0 bank48 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded140 : Blocked 8 0 bank50 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded153 : Blocked 8 0 bank63 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded188 : Blocked 8 0 bank98 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded204 : Blocked 8 0 bank114 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded210 : Blocked 8 0 bank120 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded258 : Blocked 8 0 bank168 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded262 : Blocked 8 0 bank172 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded274 : Blocked 8 0 bank184 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded278 : Blocked 8 0 bank188 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded283 : Blocked 8 0 bank193 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded319 : Blocked 8 0 bank229 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded321 : Blocked 8 0 bank231 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded336 : Blocked 8 0 bank246 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded357 : Blocked 8 0 bank267 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded358 : Blocked 8 0 bank268 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded371 : Blocked 8 0 bank281 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded372 : Blocked 8 0 bank282 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded391 : Blocked 8 0 bank301 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded398 : Blocked 8 0 bank308 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded416 : Blocked 8 0 bank326 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded420 : Blocked 8 0 bank330 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded440 : Blocked 8 0 bank350 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded446 : Blocked 8 0 bank493 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded510 : Blocked 8 0 bank562 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded676 : Blocked 8 1 bank357 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded744 : Blocked 8 1 bank425 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded764 : Blocked 8 1 bank445 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded765 : Blocked 8 1 bank446 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded777 : Blocked 8 1 bank458 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded778 : Blocked 8 1 bank459 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded779 : Blocked 8 1 bank460 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded895 : Blocked 8 1 bank768 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded910 : Blocked 8 1 bank784 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1119 : Blocked 8 1 bank1026 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1133 : Blocked 8 1 bank1040 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1 : Blocked 7 0 bank728 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded69 : Blocked 7 0 bank1028 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded118 : Blocked 8 0 bank28 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded120 : Blocked 8 0 bank30 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded155 : Blocked 8 0 bank65 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded201 : Blocked 8 0 bank111 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded208 : Blocked 8 0 bank118 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded220 : Blocked 8 0 bank130 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded225 : Blocked 8 0 bank135 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded237 : Blocked 8 0 bank147 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded242 : Blocked 8 0 bank152 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded256 : Blocked 8 0 bank166 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded267 : Blocked 8 0 bank177 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded270 : Blocked 8 0 bank180 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded302 : Blocked 8 0 bank212 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded307 : Blocked 8 0 bank217 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded344 : Blocked 8 0 bank254 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded353 : Blocked 8 0 bank263 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded370 : Blocked 8 0 bank280 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded411 : Blocked 8 0 bank321 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded424 : Blocked 8 0 bank334 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded445 : Blocked 8 0 bank492 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded447 : Blocked 8 0 bank494 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded511 : Blocked 8 0 bank563 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded513 : Blocked 8 0 bank565 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded684 : Blocked 8 1 bank365 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded705 : Blocked 8 1 bank386 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded795 : Blocked 8 1 bank476 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded813 : Blocked 8 1 bank686 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded815 : Blocked 8 1 bank688 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded821 : Blocked 8 1 bank694 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded854 : Blocked 8 1 bank727 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded857 : Blocked 8 1 bank730 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded858 : Blocked 8 1 bank731 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded871 : Blocked 8 1 bank744 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded908 : Blocked 8 1 bank782 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded930 : Blocked 8 1 bank814 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded932 : Blocked 8 1 bank816 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded933 : Blocked 8 1 bank817 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded978 : Blocked 8 1 bank863 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded990 : Blocked 8 1 bank875 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1009 : Blocked 8 1 bank904 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1039 : Blocked 8 1 bank935 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1040 : Blocked 8 1 bank936 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1043 : Blocked 8 1 bank939 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1058 : Blocked 8 1 bank954 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1116 : Blocked 8 1 bank1023 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1117 : Blocked 8 1 bank1024 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1120 : Blocked 8 1 bank1027 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1125 : Blocked 8 1 bank1032 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1127 : Blocked 8 1 bank1034 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded4 : Blocked 7 0 bank732 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded8 : Blocked 7 0 bank742 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded22 : Blocked 7 0 bank766 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded26 : Blocked 7 0 bank773 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded58 : Blocked 7 0 bank1017 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded60 : Blocked 7 0 bank1019 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded66 : Blocked 7 0 bank1025 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded72 : Blocked 7 0 bank1031 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded124 : Blocked 8 0 bank34 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded135 : Blocked 8 0 bank45 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded154 : Blocked 8 0 bank64 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded166 : Blocked 8 0 bank76 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded181 : Blocked 8 0 bank91 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded207 : Blocked 8 0 bank117 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded215 : Blocked 8 0 bank125 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded257 : Blocked 8 0 bank167 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded276 : Blocked 8 0 bank186 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded296 : Blocked 8 0 bank206 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded324 : Blocked 8 0 bank234 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded338 : Blocked 8 0 bank248 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded340 : Blocked 8 0 bank250 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded354 : Blocked 8 0 bank264 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded375 : Blocked 8 0 bank285 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded387 : Blocked 8 0 bank297 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded389 : Blocked 8 0 bank299 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded425 : Blocked 8 0 bank335 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded429 : Blocked 8 0 bank339 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded456 : Blocked 8 0 bank504 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded468 : Blocked 8 0 bank517 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded488 : Blocked 8 0 bank538 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded500 : Blocked 8 0 bank551 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded686 : Blocked 8 1 bank367 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded710 : Blocked 8 1 bank391 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded784 : Blocked 8 1 bank465 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded799 : Blocked 8 1 bank480 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded814 : Blocked 8 1 bank687 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded818 : Blocked 8 1 bank691 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded874 : Blocked 8 1 bank747 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded883 : Blocked 8 1 bank756 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded892 : Blocked 8 1 bank765 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded897 : Blocked 8 1 bank770 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded905 : Blocked 8 1 bank779 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded950 : Blocked 8 1 bank834 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded976 : Blocked 8 1 bank861 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1036 : Blocked 8 1 bank932 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1038 : Blocked 8 1 bank934 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1089 : Blocked 8 1 bank996 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1091 : Blocked 8 1 bank998 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1097 : Blocked 8 1 bank1004 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1105 : Blocked 8 1 bank1012 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1108 : Blocked 8 1 bank1015 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded6 : Blocked 7 0 bank739 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded9 : Blocked 7 0 bank744 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded14 : Blocked 7 0 bank754 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded21 : Blocked 7 0 bank765 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded28 : Blocked 7 0 bank780 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded32 : Blocked 7 0 bank784 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded37 : Blocked 7 0 bank789 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded47 : Blocked 7 0 bank996 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded48 : Blocked 7 0 bank997 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded50 : Blocked 7 0 bank999 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded52 : Blocked 7 0 bank1001 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded73 : Blocked 7 0 bank1032 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded81 : Blocked 7 0 bank1040 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded83 : Blocked 7 0 bank1042 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded94 : Blocked 8 0 bank4 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded95 : Blocked 8 0 bank5 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded96 : Blocked 8 0 bank6 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded98 : Blocked 8 0 bank8 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded110 : Blocked 8 0 bank20 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded112 : Blocked 8 0 bank22 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded113 : Blocked 8 0 bank23 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded115 : Blocked 8 0 bank25 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded141 : Blocked 8 0 bank51 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded213 : Blocked 8 0 bank123 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded214 : Blocked 8 0 bank124 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded216 : Blocked 8 0 bank126 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded218 : Blocked 8 0 bank128 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded221 : Blocked 8 0 bank131 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded226 : Blocked 8 0 bank136 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded263 : Blocked 8 0 bank173 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded268 : Blocked 8 0 bank178 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded271 : Blocked 8 0 bank181 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded273 : Blocked 8 0 bank183 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded292 : Blocked 8 0 bank202 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded295 : Blocked 8 0 bank205 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded297 : Blocked 8 0 bank207 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded298 : Blocked 8 0 bank208 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded300 : Blocked 8 0 bank210 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded306 : Blocked 8 0 bank216 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded308 : Blocked 8 0 bank218 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded325 : Blocked 8 0 bank235 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded361 : Blocked 8 0 bank271 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded362 : Blocked 8 0 bank272 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded364 : Blocked 8 0 bank274 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded366 : Blocked 8 0 bank276 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded395 : Blocked 8 0 bank305 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded396 : Blocked 8 0 bank306 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded397 : Blocked 8 0 bank307 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded400 : Blocked 8 0 bank310 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded415 : Blocked 8 0 bank325 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded417 : Blocked 8 0 bank327 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded421 : Blocked 8 0 bank331 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded423 : Blocked 8 0 bank333 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded464 : Blocked 8 0 bank512 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded469 : Blocked 8 0 bank518 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded489 : Blocked 8 0 bank539 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded492 : Blocked 8 0 bank543 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded516 : Blocked 8 0 bank569 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded519 : Blocked 8 0 bank572 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded525 : Blocked 8 0 bank578 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded526 : Blocked 8 0 bank579 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded679 : Blocked 8 1 bank360 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded690 : Blocked 8 1 bank371 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded698 : Blocked 8 1 bank379 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded713 : Blocked 8 1 bank394 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded714 : Blocked 8 1 bank395 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded726 : Blocked 8 1 bank407 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded730 : Blocked 8 1 bank411 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded752 : Blocked 8 1 bank433 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded755 : Blocked 8 1 bank436 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded760 : Blocked 8 1 bank441 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded820 : Blocked 8 1 bank693 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded822 : Blocked 8 1 bank695 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded835 : Blocked 8 1 bank708 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded840 : Blocked 8 1 bank713 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded841 : Blocked 8 1 bank714 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded865 : Blocked 8 1 bank738 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded888 : Blocked 8 1 bank761 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded899 : Blocked 8 1 bank772 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded903 : Blocked 8 1 bank776 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded916 : Blocked 8 1 bank790 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded917 : Blocked 8 1 bank791 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded970 : Blocked 8 1 bank854 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded973 : Blocked 8 1 bank857 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded974 : Blocked 8 1 bank858 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded988 : Blocked 8 1 bank873 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1010 : Blocked 8 1 bank905 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1042 : Blocked 8 1 bank938 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1049 : Blocked 8 1 bank945 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1063 : Blocked 8 1 bank967 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1085 : Blocked 8 1 bank991 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1087 : Blocked 8 1 bank994 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1098 : Blocked 8 1 bank1005 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1103 : Blocked 8 1 bank1010 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1128 : Blocked 8 1 bank1035 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1129 : Blocked 8 1 bank1036 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1170 : Blocked 8 1 bank1087 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1171 : Blocked 8 1 bank1088 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1174 : Blocked 8 1 bank1091 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded23 : Blocked 7 0 bank768 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded30 : Blocked 7 0 bank782 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded67 : Blocked 7 0 bank1026 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded75 : Blocked 7 0 bank1034 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded139 : Blocked 8 0 bank49 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded197 : Blocked 8 0 bank107 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded198 : Blocked 8 0 bank108 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded199 : Blocked 8 0 bank109 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded205 : Blocked 8 0 bank115 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded206 : Blocked 8 0 bank116 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded223 : Blocked 8 0 bank133 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded224 : Blocked 8 0 bank134 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded238 : Blocked 8 0 bank148 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded241 : Blocked 8 0 bank151 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded272 : Blocked 8 0 bank182 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded279 : Blocked 8 0 bank189 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded280 : Blocked 8 0 bank190 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded281 : Blocked 8 0 bank191 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded282 : Blocked 8 0 bank192 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded287 : Blocked 8 0 bank197 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded288 : Blocked 8 0 bank198 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded289 : Blocked 8 0 bank199 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded290 : Blocked 8 0 bank200 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded303 : Blocked 8 0 bank213 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded304 : Blocked 8 0 bank214 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded320 : Blocked 8 0 bank230 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded339 : Blocked 8 0 bank249 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded342 : Blocked 8 0 bank252 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded346 : Blocked 8 0 bank256 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded347 : Blocked 8 0 bank257 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded348 : Blocked 8 0 bank258 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded355 : Blocked 8 0 bank265 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded356 : Blocked 8 0 bank266 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded388 : Blocked 8 0 bank298 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded392 : Blocked 8 0 bank302 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded422 : Blocked 8 0 bank332 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded444 : Blocked 8 0 bank491 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded448 : Blocked 8 0 bank495 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded450 : Blocked 8 0 bank497 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded454 : Blocked 8 0 bank501 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded457 : Blocked 8 0 bank505 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded476 : Blocked 8 0 bank525 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded480 : Blocked 8 0 bank530 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded501 : Blocked 8 0 bank552 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded506 : Blocked 8 0 bank558 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded508 : Blocked 8 0 bank560 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded512 : Blocked 8 0 bank564 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded514 : Blocked 8 0 bank566 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded518 : Blocked 8 0 bank571 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded524 : Blocked 8 0 bank577 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded678 : Blocked 8 1 bank359 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded680 : Blocked 8 1 bank361 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded695 : Blocked 8 1 bank376 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded701 : Blocked 8 1 bank382 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded703 : Blocked 8 1 bank384 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded715 : Blocked 8 1 bank396 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded728 : Blocked 8 1 bank409 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded801 : Blocked 8 1 bank482 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded832 : Blocked 8 1 bank705 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded839 : Blocked 8 1 bank712 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded844 : Blocked 8 1 bank717 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded847 : Blocked 8 1 bank720 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded862 : Blocked 8 1 bank735 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded872 : Blocked 8 1 bank745 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded877 : Blocked 8 1 bank750 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded880 : Blocked 8 1 bank753 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded884 : Blocked 8 1 bank757 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded889 : Blocked 8 1 bank762 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded898 : Blocked 8 1 bank771 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded912 : Blocked 8 1 bank786 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded935 : Blocked 8 1 bank819 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded938 : Blocked 8 1 bank822 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded951 : Blocked 8 1 bank835 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded952 : Blocked 8 1 bank836 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded959 : Blocked 8 1 bank843 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded962 : Blocked 8 1 bank846 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded963 : Blocked 8 1 bank847 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded972 : Blocked 8 1 bank856 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded977 : Blocked 8 1 bank862 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded979 : Blocked 8 1 bank864 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded985 : Blocked 8 1 bank870 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded993 : Blocked 8 1 bank886 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1008 : Blocked 8 1 bank903 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1020 : Blocked 8 1 bank916 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1021 : Blocked 8 1 bank917 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1027 : Blocked 8 1 bank923 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1030 : Blocked 8 1 bank926 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1031 : Blocked 8 1 bank927 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1032 : Blocked 8 1 bank928 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1034 : Blocked 8 1 bank930 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1045 : Blocked 8 1 bank941 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1053 : Blocked 8 1 bank949 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1066 : Blocked 8 1 bank970 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1069 : Blocked 8 1 bank973 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1086 : Blocked 8 1 bank993 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1099 : Blocked 8 1 bank1006 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1101 : Blocked 8 1 bank1008 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1114 : Blocked 8 1 bank1021 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1122 : Blocked 8 1 bank1029 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1131 : Blocked 8 1 bank1038 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1140 : Blocked 8 1 bank1055 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1144 : Blocked 8 1 bank1059 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1165 : Blocked 8 1 bank1082 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1169 : Blocked 8 1 bank1086 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1173 : Blocked 8 1 bank1090 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1175 : Blocked 8 1 bank1092 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded0 : Blocked 7 0 bank727 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded2 : Blocked 7 0 bank730 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded12 : Blocked 7 0 bank747 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded56 : Blocked 7 0 bank1015 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded64 : Blocked 7 0 bank1023 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded68 : Blocked 7 0 bank1027 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded136 : Blocked 8 0 bank46 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded137 : Blocked 8 0 bank47 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded200 : Blocked 8 0 bank110 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded202 : Blocked 8 0 bank112 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded222 : Blocked 8 0 bank132 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded239 : Blocked 8 0 bank149 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded240 : Blocked 8 0 bank150 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded243 : Blocked 8 0 bank153 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded264 : Blocked 8 0 bank174 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded265 : Blocked 8 0 bank175 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded266 : Blocked 8 0 bank176 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded284 : Blocked 8 0 bank194 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded305 : Blocked 8 0 bank215 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded322 : Blocked 8 0 bank232 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded323 : Blocked 8 0 bank233 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded337 : Blocked 8 0 bank247 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded345 : Blocked 8 0 bank255 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded350 : Blocked 8 0 bank260 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded390 : Blocked 8 0 bank300 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded412 : Blocked 8 0 bank322 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded413 : Blocked 8 0 bank323 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded414 : Blocked 8 0 bank324 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded460 : Blocked 8 0 bank508 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded466 : Blocked 8 0 bank514 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded467 : Blocked 8 0 bank515 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded475 : Blocked 8 0 bank524 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded483 : Blocked 8 0 bank533 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded496 : Blocked 8 0 bank547 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded502 : Blocked 8 0 bank553 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded503 : Blocked 8 0 bank554 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded677 : Blocked 8 1 bank358 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded682 : Blocked 8 1 bank363 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded685 : Blocked 8 1 bank366 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded687 : Blocked 8 1 bank368 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded688 : Blocked 8 1 bank369 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded700 : Blocked 8 1 bank381 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded707 : Blocked 8 1 bank388 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded708 : Blocked 8 1 bank389 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded709 : Blocked 8 1 bank390 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded711 : Blocked 8 1 bank392 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded722 : Blocked 8 1 bank403 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded736 : Blocked 8 1 bank417 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded737 : Blocked 8 1 bank418 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded740 : Blocked 8 1 bank421 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded741 : Blocked 8 1 bank422 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded742 : Blocked 8 1 bank423 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded745 : Blocked 8 1 bank426 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded746 : Blocked 8 1 bank427 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded747 : Blocked 8 1 bank428 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded748 : Blocked 8 1 bank429 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded749 : Blocked 8 1 bank430 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded750 : Blocked 8 1 bank431 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded754 : Blocked 8 1 bank435 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded758 : Blocked 8 1 bank439 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded759 : Blocked 8 1 bank440 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded766 : Blocked 8 1 bank447 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded767 : Blocked 8 1 bank448 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded769 : Blocked 8 1 bank450 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded770 : Blocked 8 1 bank451 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded775 : Blocked 8 1 bank456 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded776 : Blocked 8 1 bank457 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded781 : Blocked 8 1 bank462 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded782 : Blocked 8 1 bank463 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded783 : Blocked 8 1 bank464 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded790 : Blocked 8 1 bank471 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded791 : Blocked 8 1 bank472 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded792 : Blocked 8 1 bank473 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded796 : Blocked 8 1 bank477 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded797 : Blocked 8 1 bank478 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded798 : Blocked 8 1 bank479 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded800 : Blocked 8 1 bank481 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded802 : Blocked 8 1 bank483 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded803 : Blocked 8 1 bank484 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded804 : Blocked 8 1 bank485 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded805 : Blocked 8 1 bank486 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded806 : Blocked 8 1 bank487 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded807 : Blocked 8 1 bank488 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded808 : Blocked 8 1 bank489 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded843 : Blocked 8 1 bank716 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded846 : Blocked 8 1 bank719 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded873 : Blocked 8 1 bank746 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded885 : Blocked 8 1 bank758 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded941 : Blocked 8 1 bank825 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded958 : Blocked 8 1 bank842 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded960 : Blocked 8 1 bank844 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded984 : Blocked 8 1 bank869 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded986 : Blocked 8 1 bank871 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded992 : Blocked 8 1 bank877 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1014 : Blocked 8 1 bank910 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1026 : Blocked 8 1 bank922 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1046 : Blocked 8 1 bank942 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1052 : Blocked 8 1 bank948 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1054 : Blocked 8 1 bank950 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1056 : Blocked 8 1 bank952 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1115 : Blocked 8 1 bank1022 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1123 : Blocked 8 1 bank1030 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1164 : Blocked 8 1 bank1081 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1167 : Blocked 8 1 bank1084 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded3 : Blocked 7 0 bank731 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded10 : Blocked 7 0 bank745 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded11 : Blocked 7 0 bank746 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded15 : Blocked 7 0 bank756 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded16 : Blocked 7 0 bank757 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded17 : Blocked 7 0 bank758 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded38 : Blocked 7 0 bank790 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded39 : Blocked 7 0 bank791 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded49 : Blocked 7 0 bank998 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded62 : Blocked 7 0 bank1021 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded63 : Blocked 7 0 bank1022 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded65 : Blocked 7 0 bank1024 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded70 : Blocked 7 0 bank1029 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded71 : Blocked 7 0 bank1030 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded76 : Blocked 7 0 bank1035 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded77 : Blocked 7 0 bank1036 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded458 : Blocked 8 0 bank506 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded459 : Blocked 8 0 bank507 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded461 : Blocked 8 0 bank509 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded462 : Blocked 8 0 bank510 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded463 : Blocked 8 0 bank511 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded465 : Blocked 8 0 bank513 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded470 : Blocked 8 0 bank519 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded471 : Blocked 8 0 bank520 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded472 : Blocked 8 0 bank521 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded473 : Blocked 8 0 bank522 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded474 : Blocked 8 0 bank523 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded477 : Blocked 8 0 bank526 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded478 : Blocked 8 0 bank527 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded479 : Blocked 8 0 bank528 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded481 : Blocked 8 0 bank531 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded482 : Blocked 8 0 bank532 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded484 : Blocked 8 0 bank534 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded485 : Blocked 8 0 bank535 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded486 : Blocked 8 0 bank536 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded487 : Blocked 8 0 bank537 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded490 : Blocked 8 0 bank540 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded491 : Blocked 8 0 bank541 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded493 : Blocked 8 0 bank544 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded494 : Blocked 8 0 bank545 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded495 : Blocked 8 0 bank546 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded497 : Blocked 8 0 bank548 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded498 : Blocked 8 0 bank549 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded499 : Blocked 8 0 bank550 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded517 : Blocked 8 0 bank570 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded520 : Blocked 8 0 bank573 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded521 : Blocked 8 0 bank574 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded522 : Blocked 8 0 bank575 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded523 : Blocked 8 0 bank576 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded527 : Blocked 8 0 bank580 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded689 : Blocked 8 1 bank370 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded691 : Blocked 8 1 bank372 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded693 : Blocked 8 1 bank374 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded697 : Blocked 8 1 bank378 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded699 : Blocked 8 1 bank380 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded712 : Blocked 8 1 bank393 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded716 : Blocked 8 1 bank397 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded756 : Blocked 8 1 bank437 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded838 : Blocked 8 1 bank711 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded861 : Blocked 8 1 bank734 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded875 : Blocked 8 1 bank748 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded876 : Blocked 8 1 bank749 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded886 : Blocked 8 1 bank759 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded887 : Blocked 8 1 bank760 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded896 : Blocked 8 1 bank769 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded902 : Blocked 8 1 bank775 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded904 : Blocked 8 1 bank778 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded913 : Blocked 8 1 bank787 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded914 : Blocked 8 1 bank788 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded949 : Blocked 8 1 bank833 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded955 : Blocked 8 1 bank839 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded961 : Blocked 8 1 bank845 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded964 : Blocked 8 1 bank848 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded967 : Blocked 8 1 bank851 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded971 : Blocked 8 1 bank855 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded980 : Blocked 8 1 bank865 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded987 : Blocked 8 1 bank872 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded991 : Blocked 8 1 bank876 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1012 : Blocked 8 1 bank908 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1019 : Blocked 8 1 bank915 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1022 : Blocked 8 1 bank918 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1024 : Blocked 8 1 bank920 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1028 : Blocked 8 1 bank924 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1029 : Blocked 8 1 bank925 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1037 : Blocked 8 1 bank933 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1050 : Blocked 8 1 bank946 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1051 : Blocked 8 1 bank947 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1096 : Blocked 8 1 bank1003 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1104 : Blocked 8 1 bank1011 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1106 : Blocked 8 1 bank1013 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1107 : Blocked 8 1 bank1014 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1109 : Blocked 8 1 bank1016 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1111 : Blocked 8 1 bank1018 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1113 : Blocked 8 1 bank1020 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1126 : Blocked 8 1 bank1033 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1134 : Blocked 8 1 bank1041 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1141 : Blocked 8 1 bank1056 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded1172 : Blocked 8 1 bank1089 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded5 : Blocked 7 0 bank734 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded13 : Blocked 7 0 bank748 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded18 : Blocked 7 0 bank759 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded19 : Blocked 7 0 bank760 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded24 : Blocked 7 0 bank771 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded25 : Blocked 7 0 bank772 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded27 : Blocked 7 0 bank775 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded34 : Blocked 7 0 bank786 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded35 : Blocked 7 0 bank787 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded36 : Blocked 7 0 bank788 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded44 : Blocked 7 0 bank993 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded45 : Blocked 7 0 bank994 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded54 : Blocked 7 0 bank1013 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded55 : Blocked 7 0 bank1014 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded57 : Blocked 7 0 bank1016 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded59 : Blocked 7 0 bank1018 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded61 : Blocked 7 0 bank1020 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded74 : Blocked 7 0 bank1033 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded79 : Blocked 7 0 bank1038 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem excluded82 : Blocked 7 0 bank1041 :=
  block_search (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
theorem cuts1246 : stepTest 9 1 bank0
    (allowChild [bank490, bank503, bank516, bank529, bank542, bank555, bank568]) (allowChild [bank1, bank992, bank9, bank18, bank906, bank26, bank35, bank44, bank52, bank61, bank69, bank78, bank87, bank96, bank105, bank113, bank121, bank129, bank137, bank146, bank154, bank163, bank171, bank179, bank187, bank195, bank203, bank211, bank219, bank228, bank236, bank245, bank253, bank261, bank269, bank859, bank277, bank286, bank295, bank303, bank777, bank311, bank320, bank328, bank336, bank345]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts629 : stepTest 7 0 bank777
    (allowChild []) (allowChild [bank727, bank1076, bank728, bank730, bank989, bank731, bank732, bank734, bank739, bank812, bank741, bank742, bank744, bank783, bank784, bank745, bank746, bank747, bank748, bank754, bank813, bank756, bank757, bank758, bank1078, bank785, bank786, bank759, bank760, bank763, bank765, bank766, bank768, bank790, bank791, bank771, bank902, bank772, bank773, bank775, bank787, bank782, bank780, bank781, bank788, bank789]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts662 : stepTest 7 0 bank992
    (allowChild []) (allowChild [bank993, bank1080, bank994, bank995, bank996, bank997, bank1107, bank998, bank999, bank1108, bank1000, bank1001, bank1002, bank1013, bank1014, bank1015, bank1016, bank1017, bank1018, bank1019, bank1020, bank1033, bank1034, bank1021, bank1022, bank1023, bank1079, bank1024, bank1025, bank1026, bank1035, bank1036, bank1027, bank1076, bank1028, bank1029, bank1030, bank1077, bank1037, bank1038, bank1031, bank1032, bank1039, bank1040, bank1041, bank1042]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1192 : stepTest 8 0 bank0
    (allowChild []) (allowChild [bank1, bank992, bank9, bank18, bank906, bank26, bank35, bank44, bank52, bank61, bank69, bank78, bank87, bank96, bank105, bank113, bank121, bank129, bank137, bank146, bank154, bank163, bank171, bank179, bank187, bank195, bank203, bank211, bank219, bank228, bank236, bank245, bank253, bank261, bank269, bank859, bank277, bank286, bank295, bank303, bank777, bank311, bank320, bank328, bank336, bank345]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1193 : stepTest 8 0 bank490
    (allowChild []) (allowChild [bank2, bank1043, bank10, bank19, bank955, bank27, bank36, bank45, bank53, bank62, bank70, bank79, bank88, bank97, bank106, bank114, bank122, bank130, bank138, bank147, bank155, bank164, bank172, bank180, bank1075, bank581, bank1074, bank491, bank582, bank492, bank188, bank196, bank204, bank212, bank220, bank229, bank237, bank246, bank987, bank583, bank986, bank493, bank584, bank494, bank254, bank262, bank270, bank878, bank278, bank287, bank296, bank585, bank495, bank586, bank496, bank304, bank792, bank312, bank321, bank329, bank587, bank497, bank588, bank498, bank337, bank346, bank589, bank499, bank590, bank500, bank591, bank501, bank592, bank502]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1194 : stepTest 8 0 bank503
    (allowChild []) (allowChild [bank3, bank1044, bank11, bank20, bank956, bank28, bank37, bank46, bank54, bank63, bank71, bank80, bank89, bank98, bank593, bank504, bank594, bank505, bank107, bank115, bank123, bank131, bank139, bank148, bank156, bank165, bank173, bank181, bank189, bank197, bank205, bank213, bank221, bank230, bank238, bank247, bank595, bank506, bank596, bank507, bank255, bank263, bank271, bank879, bank279, bank288, bank297, bank597, bank508, bank598, bank509, bank305, bank793, bank313, bank322, bank330, bank599, bank510, bank600, bank511, bank338, bank347, bank601, bank512, bank602, bank513, bank603, bank514, bank604, bank515]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1195 : stepTest 8 0 bank516
    (allowChild []) (allowChild [bank4, bank1045, bank12, bank21, bank957, bank29, bank38, bank47, bank55, bank64, bank72, bank81, bank90, bank99, bank605, bank517, bank606, bank518, bank108, bank116, bank124, bank132, bank140, bank149, bank157, bank166, bank174, bank182, bank607, bank519, bank608, bank520, bank190, bank198, bank206, bank214, bank222, bank231, bank239, bank248, bank256, bank264, bank272, bank880, bank280, bank289, bank298, bank609, bank521, bank610, bank522, bank306, bank794, bank314, bank323, bank331, bank611, bank523, bank612, bank524, bank339, bank348, bank613, bank525, bank614, bank526, bank615, bank527, bank616, bank528]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1196 : stepTest 8 0 bank529
    (allowChild []) (allowChild [bank5, bank1046, bank13, bank22, bank958, bank30, bank39, bank48, bank56, bank65, bank73, bank82, bank91, bank100, bank617, bank530, bank618, bank531, bank109, bank117, bank125, bank133, bank141, bank150, bank158, bank167, bank175, bank183, bank619, bank532, bank620, bank533, bank191, bank199, bank207, bank215, bank223, bank232, bank240, bank249, bank621, bank534, bank622, bank535, bank257, bank265, bank273, bank881, bank281, bank290, bank299, bank307, bank795, bank315, bank324, bank332, bank623, bank536, bank624, bank537, bank340, bank349, bank625, bank538, bank626, bank539, bank627, bank540, bank628, bank541]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1197 : stepTest 8 0 bank542
    (allowChild []) (allowChild [bank6, bank1047, bank14, bank23, bank959, bank31, bank40, bank49, bank57, bank66, bank74, bank83, bank92, bank101, bank629, bank543, bank630, bank544, bank110, bank118, bank126, bank134, bank142, bank151, bank159, bank168, bank176, bank184, bank631, bank545, bank632, bank546, bank192, bank200, bank208, bank216, bank224, bank233, bank241, bank250, bank633, bank547, bank634, bank548, bank258, bank266, bank274, bank882, bank282, bank291, bank300, bank635, bank549, bank636, bank550, bank308, bank796, bank316, bank325, bank333, bank341, bank350, bank637, bank551, bank638, bank552, bank639, bank553, bank640, bank554]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1198 : stepTest 8 0 bank555
    (allowChild []) (allowChild [bank7, bank1048, bank15, bank24, bank960, bank32, bank41, bank50, bank58, bank67, bank75, bank84, bank93, bank102, bank641, bank556, bank642, bank557, bank111, bank119, bank127, bank135, bank143, bank152, bank160, bank169, bank177, bank185, bank643, bank558, bank644, bank559, bank193, bank201, bank209, bank217, bank225, bank234, bank242, bank251, bank645, bank560, bank646, bank561, bank259, bank267, bank275, bank883, bank283, bank292, bank301, bank898, bank647, bank897, bank562, bank648, bank563, bank309, bank797, bank317, bank326, bank334, bank811, bank649, bank810, bank564, bank650, bank565, bank342, bank351, bank651, bank566, bank652, bank567]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1199 : stepTest 8 0 bank568
    (allowChild []) (allowChild [bank8, bank1049, bank16, bank25, bank961, bank33, bank42, bank51, bank59, bank68, bank76, bank85, bank94, bank103, bank653, bank569, bank654, bank570, bank112, bank120, bank128, bank136, bank144, bank153, bank161, bank170, bank178, bank186, bank655, bank571, bank656, bank572, bank194, bank202, bank210, bank218, bank226, bank235, bank243, bank252, bank657, bank573, bank658, bank574, bank260, bank268, bank276, bank884, bank284, bank293, bank302, bank659, bank575, bank660, bank576, bank310, bank798, bank318, bank327, bank335, bank661, bank577, bank662, bank578, bank343, bank352, bank663, bank579, bank664, bank580]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1201 : stepTest 8 1 bank9
    (allowChild [bank10, bank1044, bank11, bank12, bank13, bank14, bank15, bank16, bank665, bank17]) (allowChild [bank991, bank1081, bank904, bank1082, bank1083, bank1003, bank1004, bank1005, bank1006, bank1007, bank1008, bank1009, bank1010, bank1011, bank1012, bank358, bank359, bank815, bank360, bank361, bank728, bank801, bank362, bank729, bank363, bank364, bank365, bank366, bank367]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1203 : stepTest 8 1 bank26
    (allowChild [bank27, bank28, bank957, bank29, bank30, bank31, bank32, bank33, bank666, bank34]) (allowChild [bank994, bank905, bank1084, bank1085, bank1086, bank915, bank916, bank368, bank359, bank925, bank926, bank927, bank928, bank929, bank930, bank931, bank932, bank817, bank369, bank370, bank731, bank371, bank372, bank373, bank374, bank375, bank376]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1204 : stepTest 8 1 bank35
    (allowChild [bank36, bank37, bank38, bank39, bank40, bank41, bank42, bank669, bank43]) (allowChild [bank995, bank907, bank818, bank1087, bank354, bank1067, bank471, bank1051, bank819, bank398, bank977, bank421, bank963, bank820, bank821, bank732, bank402, bank802, bank403, bank733, bank404, bank721, bank405, bank703, bank697, bank406, bank682]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1206 : stepTest 8 1 bank52
    (allowChild [bank53, bank54, bank55, bank56, bank57, bank58, bank59, bank672, bank60]) (allowChild [bank997, bank909, bank735, bank1089, bank736, bank355, bank1066, bank465, bank1052, bank399, bank978, bank422, bank964, bank823, bank402, bank889, bank423, bank824, bank737, bank424, bank722, bank416, bank704, bank425, bank698, bank426, bank683]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1208 : stepTest 8 1 bank69
    (allowChild [bank70, bank71, bank72, bank73, bank74, bank75, bank76, bank673, bank77]) (allowChild [bank999, bank911, bank705, bank1090, bank356, bank1068, bank483, bank1053, bank400, bank979, bank429, bank965, bank826, bank404, bank890, bank430, bank827, bank739, bank424, bank803, bank427, bank740, bank699, bank431, bank684]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1209 : stepTest 8 1 bank78
    (allowChild [bank79, bank80, bank81, bank82, bank83, bank84, bank85, bank670, bank86]) (allowChild [bank1108, bank1000, bank1083, bank1105, bank912, bank1085, bank705, bank1090, bank1091, bank394, bank365, bank433, bank374, bank900, bank706, bank828, bank407, bank378, bank812, bank707, bank741, bank411, bank386, bank708, bank412, bank413]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1210 : stepTest 8 1 bank87
    (allowChild [bank88, bank89, bank90, bank91, bank92, bank93, bank94, bank675, bank95]) (allowChild [bank1001, bank913, bank685, bank1092, bank357, bank1069, bank484, bank1054, bank401, bank981, bank439, bank966, bank829, bank891, bank440, bank830, bank742, bank425, bank804, bank428, bank743, bank723, bank438, bank709]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1211 : stepTest 8 1 bank96
    (allowChild [bank97, bank98, bank99, bank100, bank101, bank102, bank103, bank671, bank104]) (allowChild [bank1002, bank1106, bank914, bank1086, bank1088, bank1091, bank685, bank1092, bank397, bank367, bank441, bank376, bank831, bank686, bank888, bank408, bank832, bank417, bank744, bank687, bank418, bank409, bank688, bank419, bank413]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1216 : stepTest 8 1 bank137
    (allowChild [bank138, bank139, bank140, bank141, bank142, bank143, bank144, bank680, bank145]) (allowChild [bank1007, bank919, bank736, bank355, bank1099, bank410, bank1093, bank1055, bank749, bank1056, bank1057, bank1058, bank466, bank984, bank472, bank968, bank750, bank837, bank469, bank895, bank473, bank838, bank751, bank752, bank474, bank726, bank475, bank710, bank476, bank701, bank477, bank689]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1218 : stepTest 8 1 bank154
    (allowChild [bank155, bank156, bank157, bank158, bank159, bank160, bank161, bank681, bank162]) (allowChild [bank1009, bank921, bank356, bank1100, bank414, bank1094, bank1057, bank711, bank1059, bank467, bank985, bank478, bank969, bank840, bank470, bank896, bank479, bank841, bank754, bank474, bank809, bank480, bank755, bank460, bank702, bank481, bank690]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1226 : stepTest 8 1 bank219
    (allowChild [bank220, bank221, bank222, bank223, bank224, bank225, bank226, bank676, bank227]) (allowChild [bank1017, bank929, bank400, bank1101, bank415, bank1095, bank467, bank1072, bank488, bank1060, bank970, bank713, bank971, bank972, bank849, bank443, bank892, bank447, bank850, bank763, bank445, bank805, bank448, bank764, bank700, bank449, bank692]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1228 : stepTest 8 1 bank236
    (allowChild [bank237, bank238, bank239, bank240, bank241, bank242, bank243, bank677, bank244]) (allowChild [bank1019, bank931, bank401, bank1102, bank420, bank1096, bank967, bank468, bank1073, bank489, bank1061, bank972, bank988, bank693, bank973, bank852, bank444, bank893, bank450, bank853, bank766, bank446, bank806, bank451, bank767, bank724, bank452, bank715]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1233 : stepTest 8 1 bank277
    (allowChild [bank278, bank279, bank280, bank881, bank281, bank282, bank283, bank284, bank667, bank285]) (allowChild [bank1024, bank936, bank820, bank822, bank706, bank377, bank378, bank835, bank836, bank379, bank380, bank845, bank846, bank392, bank393, bank855, bank856, bank716, bank858, bank860, bank861, bank772, bank381, bank382, bank717, bank383, bank384]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1234 : stepTest 8 1 bank286
    (allowChild [bank287, bank288, bank289, bank290, bank291, bank292, bank293, bank678, bank294]) (allowChild [bank1025, bank937, bank821, bank1103, bank442, bank1097, bank458, bank1070, bank486, bank1062, bank444, bank982, bank456, bank974, bank857, bank860, bank899, bank695, bank886, bank773, bank453, bank807, bank457, bank774, bank454, bank725, bank455, bank718]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1237 : stepTest 8 1 bank311
    (allowChild [bank312, bank313, bank314, bank315, bank796, bank316, bank317, bank318, bank668, bank319]) (allowChild [bank1028, bank940, bank737, bank738, bank707, bank385, bank386, bank751, bank753, bank712, bank1065, bank387, bank1063, bank388, bank761, bank762, bank395, bank396, bank769, bank770, bank863, bank389, bank382, bank719, bank776, bank778, bank779, bank390, bank391]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1240 : stepTest 8 1 bank336
    (allowChild [bank337, bank338, bank339, bank340, bank341, bank342, bank343, bank679, bank344]) (allowChild [bank1031, bank943, bank1104, bank461, bank1098, bank460, bank1071, bank487, bank1064, bank983, bank462, bank975, bank866, bank454, bank894, bank463, bank887, bank780, bank459, bank808, bank464, bank800, bank696, bank720]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1241 : stepTest 8 1 bank345
    (allowChild [bank346, bank347, bank348, bank349, bank350, bank351, bank352, bank674, bank353]) (allowChild [bank1032, bank944, bank708, bank688, bank432, bank413, bank691, bank485, bank482, bank714, bank694, bank980, bank434, bank976, bank435, bank901, bank717, bank867, bank436, bank384, bank781, bank437, bank391, bank696, bank720]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1242 : stepTest 8 1 bank777
    (allowChild [bank792, bank793, bank794, bank795, bank797, bank798, bank799]) (allowChild [bank727, bank1076, bank728, bank730, bank989, bank731, bank732, bank734, bank739, bank812, bank741, bank742, bank744, bank783, bank784, bank745, bank746, bank747, bank748, bank754, bank813, bank756, bank757, bank758, bank1078, bank785, bank786, bank759, bank760, bank763, bank765, bank766, bank768, bank790, bank791, bank771, bank902, bank772, bank773, bank775, bank787, bank782, bank780, bank781, bank788, bank789]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1243 : stepTest 8 1 bank859
    (allowChild [bank878, bank879, bank880, bank882, bank883, bank884, bank885]) (allowChild [bank814, bank1079, bank815, bank816, bank990, bank817, bank823, bank825, bank826, bank900, bank828, bank829, bank831, bank868, bank869, bank833, bank834, bank837, bank839, bank840, bank842, bank843, bank844, bank870, bank871, bank847, bank848, bank849, bank851, bank852, bank854, bank876, bank877, bank862, bank902, bank863, bank864, bank865, bank872, bank873, bank866, bank901, bank867, bank874, bank875]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1244 : stepTest 8 1 bank906
    (allowChild [bank955, bank956, bank958, bank959, bank960, bank961, bank962]) (allowChild [bank903, bank1080, bank904, bank907, bank908, bank909, bank910, bank911, bank1105, bank912, bank913, bank1106, bank914, bank917, bank918, bank919, bank920, bank921, bank922, bank923, bank924, bank946, bank945, bank933, bank934, bank935, bank990, bank936, bank937, bank938, bank947, bank948, bank939, bank989, bank940, bank941, bank942, bank949, bank950, bank943, bank944, bank951, bank952, bank953, bank954]) = false := by decide +kernel

set_option maxRecDepth 24000 in
theorem cuts1245 : stepTest 8 1 bank992
    (allowChild [bank1043, bank1045, bank1046, bank1047, bank1048, bank1049, bank1050]) (allowChild [bank993, bank1080, bank994, bank995, bank996, bank997, bank1107, bank998, bank999, bank1108, bank1000, bank1001, bank1002, bank1013, bank1014, bank1015, bank1016, bank1017, bank1018, bank1019, bank1020, bank1033, bank1034, bank1021, bank1022, bank1023, bank1079, bank1024, bank1025, bank1026, bank1035, bank1036, bank1027, bank1076, bank1028, bank1029, bank1030, bank1077, bank1037, bank1038, bank1031, bank1032, bank1039, bank1040, bank1041, bank1042]) = false := by decide +kernel

theorem excluded629 : Blocked 8 0 bank777 :=
  block_step []
    [bank727, bank1076, bank728, bank730, bank989, bank731, bank732, bank734, bank739, bank812, bank741, bank742, bank744, bank783, bank784, bank745, bank746, bank747, bank748, bank754, bank813, bank756, bank757, bank758, bank1078, bank785, bank786, bank759, bank760, bank763, bank765, bank766, bank768, bank790, bank791, bank771, bank902, bank772, bank773, bank775, bank787, bank782, bank780, bank781, bank788, bank789]
    True.intro
    ⟨excluded0, excluded84, excluded1, excluded2, excluded43, excluded3, excluded4, excluded5, excluded6, excluded40, excluded7, excluded8, excluded9, excluded31, excluded32, excluded10, excluded11, excluded12, excluded13, excluded14, excluded41, excluded15, excluded16, excluded17, excluded86, excluded33, excluded34, excluded18, excluded19, excluded20, excluded21, excluded22, excluded23, excluded38, excluded39, excluded24, excluded42, excluded25, excluded26, excluded27, excluded35, excluded30, excluded28, excluded29, excluded36, excluded37, True.intro⟩
    (by decide +kernel) cuts629

theorem excluded662 : Blocked 8 0 bank992 :=
  block_step []
    [bank993, bank1080, bank994, bank995, bank996, bank997, bank1107, bank998, bank999, bank1108, bank1000, bank1001, bank1002, bank1013, bank1014, bank1015, bank1016, bank1017, bank1018, bank1019, bank1020, bank1033, bank1034, bank1021, bank1022, bank1023, bank1079, bank1024, bank1025, bank1026, bank1035, bank1036, bank1027, bank1076, bank1028, bank1029, bank1030, bank1077, bank1037, bank1038, bank1031, bank1032, bank1039, bank1040, bank1041, bank1042]
    True.intro
    ⟨excluded44, excluded88, excluded45, excluded46, excluded47, excluded48, excluded89, excluded49, excluded50, excluded90, excluded51, excluded52, excluded53, excluded54, excluded55, excluded56, excluded57, excluded58, excluded59, excluded60, excluded61, excluded74, excluded75, excluded62, excluded63, excluded64, excluded87, excluded65, excluded66, excluded67, excluded76, excluded77, excluded68, excluded84, excluded69, excluded70, excluded71, excluded85, excluded78, excluded79, excluded72, excluded73, excluded80, excluded81, excluded82, excluded83, True.intro⟩
    (by decide +kernel) cuts662

theorem excluded1192 : Blocked 9 0 bank0 :=
  block_step []
    [bank1, bank992, bank9, bank18, bank906, bank26, bank35, bank44, bank52, bank61, bank69, bank78, bank87, bank96, bank105, bank113, bank121, bank129, bank137, bank146, bank154, bank163, bank171, bank179, bank187, bank195, bank203, bank211, bank219, bank228, bank236, bank245, bank253, bank261, bank269, bank859, bank277, bank286, bank295, bank303, bank777, bank311, bank320, bank328, bank336, bank345]
    True.intro
    ⟨excluded91, excluded662, excluded99, excluded108, excluded651, excluded116, excluded125, excluded134, excluded142, excluded151, excluded159, excluded168, excluded177, excluded186, excluded195, excluded203, excluded211, excluded219, excluded227, excluded236, excluded244, excluded253, excluded261, excluded269, excluded277, excluded285, excluded293, excluded301, excluded309, excluded318, excluded326, excluded335, excluded343, excluded351, excluded359, excluded640, excluded367, excluded376, excluded385, excluded393, excluded629, excluded401, excluded410, excluded418, excluded426, excluded435, True.intro⟩
    (by decide +kernel) cuts1192

theorem excluded1193 : Blocked 9 0 bank490 :=
  block_step []
    [bank2, bank1043, bank10, bank19, bank955, bank27, bank36, bank45, bank53, bank62, bank70, bank79, bank88, bank97, bank106, bank114, bank122, bank130, bank138, bank147, bank155, bank164, bank172, bank180, bank1075, bank581, bank1074, bank491, bank582, bank492, bank188, bank196, bank204, bank212, bank220, bank229, bank237, bank246, bank987, bank583, bank986, bank493, bank584, bank494, bank254, bank262, bank270, bank878, bank278, bank287, bank296, bank585, bank495, bank586, bank496, bank304, bank792, bank312, bank321, bank329, bank587, bank497, bank588, bank498, bank337, bank346, bank589, bank499, bank590, bank500, bank591, bank501, bank592, bank502]
    True.intro
    ⟨excluded92, excluded663, excluded100, excluded109, excluded652, excluded117, excluded126, excluded135, excluded143, excluded152, excluded160, excluded169, excluded178, excluded187, excluded196, excluded204, excluded212, excluded220, excluded228, excluded237, excluded245, excluded254, excluded262, excluded270, excluded672, excluded528, excluded671, excluded444, excluded529, excluded445, excluded278, excluded286, excluded294, excluded302, excluded310, excluded319, excluded327, excluded336, excluded661, excluded530, excluded660, excluded446, excluded531, excluded447, excluded344, excluded352, excluded360, excluded641, excluded368, excluded377, excluded386, excluded532, excluded448, excluded533, excluded449, excluded394, excluded630, excluded402, excluded411, excluded419, excluded534, excluded450, excluded535, excluded451, excluded427, excluded436, excluded536, excluded452, excluded537, excluded453, excluded538, excluded454, excluded539, excluded455, True.intro⟩
    (by decide +kernel) cuts1193

theorem excluded1194 : Blocked 9 0 bank503 :=
  block_step []
    [bank3, bank1044, bank11, bank20, bank956, bank28, bank37, bank46, bank54, bank63, bank71, bank80, bank89, bank98, bank593, bank504, bank594, bank505, bank107, bank115, bank123, bank131, bank139, bank148, bank156, bank165, bank173, bank181, bank189, bank197, bank205, bank213, bank221, bank230, bank238, bank247, bank595, bank506, bank596, bank507, bank255, bank263, bank271, bank879, bank279, bank288, bank297, bank597, bank508, bank598, bank509, bank305, bank793, bank313, bank322, bank330, bank599, bank510, bank600, bank511, bank338, bank347, bank601, bank512, bank602, bank513, bank603, bank514, bank604, bank515]
    True.intro
    ⟨excluded93, excluded664, excluded101, excluded110, excluded653, excluded118, excluded127, excluded136, excluded144, excluded153, excluded161, excluded170, excluded179, excluded188, excluded540, excluded456, excluded541, excluded457, excluded197, excluded205, excluded213, excluded221, excluded229, excluded238, excluded246, excluded255, excluded263, excluded271, excluded279, excluded287, excluded295, excluded303, excluded311, excluded320, excluded328, excluded337, excluded542, excluded458, excluded543, excluded459, excluded345, excluded353, excluded361, excluded642, excluded369, excluded378, excluded387, excluded544, excluded460, excluded545, excluded461, excluded395, excluded631, excluded403, excluded412, excluded420, excluded546, excluded462, excluded547, excluded463, excluded428, excluded437, excluded548, excluded464, excluded549, excluded465, excluded550, excluded466, excluded551, excluded467, True.intro⟩
    (by decide +kernel) cuts1194

theorem excluded1195 : Blocked 9 0 bank516 :=
  block_step []
    [bank4, bank1045, bank12, bank21, bank957, bank29, bank38, bank47, bank55, bank64, bank72, bank81, bank90, bank99, bank605, bank517, bank606, bank518, bank108, bank116, bank124, bank132, bank140, bank149, bank157, bank166, bank174, bank182, bank607, bank519, bank608, bank520, bank190, bank198, bank206, bank214, bank222, bank231, bank239, bank248, bank256, bank264, bank272, bank880, bank280, bank289, bank298, bank609, bank521, bank610, bank522, bank306, bank794, bank314, bank323, bank331, bank611, bank523, bank612, bank524, bank339, bank348, bank613, bank525, bank614, bank526, bank615, bank527, bank616, bank528]
    True.intro
    ⟨excluded94, excluded665, excluded102, excluded111, excluded654, excluded119, excluded128, excluded137, excluded145, excluded154, excluded162, excluded171, excluded180, excluded189, excluded552, excluded468, excluded553, excluded469, excluded198, excluded206, excluded214, excluded222, excluded230, excluded239, excluded247, excluded256, excluded264, excluded272, excluded554, excluded470, excluded555, excluded471, excluded280, excluded288, excluded296, excluded304, excluded312, excluded321, excluded329, excluded338, excluded346, excluded354, excluded362, excluded643, excluded370, excluded379, excluded388, excluded556, excluded472, excluded557, excluded473, excluded396, excluded632, excluded404, excluded413, excluded421, excluded558, excluded474, excluded559, excluded475, excluded429, excluded438, excluded560, excluded476, excluded561, excluded477, excluded562, excluded478, excluded563, excluded479, True.intro⟩
    (by decide +kernel) cuts1195

theorem excluded1196 : Blocked 9 0 bank529 :=
  block_step []
    [bank5, bank1046, bank13, bank22, bank958, bank30, bank39, bank48, bank56, bank65, bank73, bank82, bank91, bank100, bank617, bank530, bank618, bank531, bank109, bank117, bank125, bank133, bank141, bank150, bank158, bank167, bank175, bank183, bank619, bank532, bank620, bank533, bank191, bank199, bank207, bank215, bank223, bank232, bank240, bank249, bank621, bank534, bank622, bank535, bank257, bank265, bank273, bank881, bank281, bank290, bank299, bank307, bank795, bank315, bank324, bank332, bank623, bank536, bank624, bank537, bank340, bank349, bank625, bank538, bank626, bank539, bank627, bank540, bank628, bank541]
    True.intro
    ⟨excluded95, excluded666, excluded103, excluded112, excluded655, excluded120, excluded129, excluded138, excluded146, excluded155, excluded163, excluded172, excluded181, excluded190, excluded564, excluded480, excluded565, excluded481, excluded199, excluded207, excluded215, excluded223, excluded231, excluded240, excluded248, excluded257, excluded265, excluded273, excluded566, excluded482, excluded567, excluded483, excluded281, excluded289, excluded297, excluded305, excluded313, excluded322, excluded330, excluded339, excluded568, excluded484, excluded569, excluded485, excluded347, excluded355, excluded363, excluded644, excluded371, excluded380, excluded389, excluded397, excluded633, excluded405, excluded414, excluded422, excluded570, excluded486, excluded571, excluded487, excluded430, excluded439, excluded572, excluded488, excluded573, excluded489, excluded574, excluded490, excluded575, excluded491, True.intro⟩
    (by decide +kernel) cuts1196

theorem excluded1197 : Blocked 9 0 bank542 :=
  block_step []
    [bank6, bank1047, bank14, bank23, bank959, bank31, bank40, bank49, bank57, bank66, bank74, bank83, bank92, bank101, bank629, bank543, bank630, bank544, bank110, bank118, bank126, bank134, bank142, bank151, bank159, bank168, bank176, bank184, bank631, bank545, bank632, bank546, bank192, bank200, bank208, bank216, bank224, bank233, bank241, bank250, bank633, bank547, bank634, bank548, bank258, bank266, bank274, bank882, bank282, bank291, bank300, bank635, bank549, bank636, bank550, bank308, bank796, bank316, bank325, bank333, bank341, bank350, bank637, bank551, bank638, bank552, bank639, bank553, bank640, bank554]
    True.intro
    ⟨excluded96, excluded667, excluded104, excluded113, excluded656, excluded121, excluded130, excluded139, excluded147, excluded156, excluded164, excluded173, excluded182, excluded191, excluded576, excluded492, excluded577, excluded493, excluded200, excluded208, excluded216, excluded224, excluded232, excluded241, excluded249, excluded258, excluded266, excluded274, excluded578, excluded494, excluded579, excluded495, excluded282, excluded290, excluded298, excluded306, excluded314, excluded323, excluded331, excluded340, excluded580, excluded496, excluded581, excluded497, excluded348, excluded356, excluded364, excluded645, excluded372, excluded381, excluded390, excluded582, excluded498, excluded583, excluded499, excluded398, excluded634, excluded406, excluded415, excluded423, excluded431, excluded440, excluded584, excluded500, excluded585, excluded501, excluded586, excluded502, excluded587, excluded503, True.intro⟩
    (by decide +kernel) cuts1197

theorem excluded1198 : Blocked 9 0 bank555 :=
  block_step []
    [bank7, bank1048, bank15, bank24, bank960, bank32, bank41, bank50, bank58, bank67, bank75, bank84, bank93, bank102, bank641, bank556, bank642, bank557, bank111, bank119, bank127, bank135, bank143, bank152, bank160, bank169, bank177, bank185, bank643, bank558, bank644, bank559, bank193, bank201, bank209, bank217, bank225, bank234, bank242, bank251, bank645, bank560, bank646, bank561, bank259, bank267, bank275, bank883, bank283, bank292, bank301, bank898, bank647, bank897, bank562, bank648, bank563, bank309, bank797, bank317, bank326, bank334, bank811, bank649, bank810, bank564, bank650, bank565, bank342, bank351, bank651, bank566, bank652, bank567]
    True.intro
    ⟨excluded97, excluded668, excluded105, excluded114, excluded657, excluded122, excluded131, excluded140, excluded148, excluded157, excluded165, excluded174, excluded183, excluded192, excluded588, excluded504, excluded589, excluded505, excluded201, excluded209, excluded217, excluded225, excluded233, excluded242, excluded250, excluded259, excluded267, excluded275, excluded590, excluded506, excluded591, excluded507, excluded283, excluded291, excluded299, excluded307, excluded315, excluded324, excluded332, excluded341, excluded592, excluded508, excluded593, excluded509, excluded349, excluded357, excluded365, excluded646, excluded373, excluded382, excluded391, excluded650, excluded594, excluded649, excluded510, excluded595, excluded511, excluded399, excluded635, excluded407, excluded416, excluded424, excluded639, excluded596, excluded638, excluded512, excluded597, excluded513, excluded432, excluded441, excluded598, excluded514, excluded599, excluded515, True.intro⟩
    (by decide +kernel) cuts1198

theorem excluded1199 : Blocked 9 0 bank568 :=
  block_step []
    [bank8, bank1049, bank16, bank25, bank961, bank33, bank42, bank51, bank59, bank68, bank76, bank85, bank94, bank103, bank653, bank569, bank654, bank570, bank112, bank120, bank128, bank136, bank144, bank153, bank161, bank170, bank178, bank186, bank655, bank571, bank656, bank572, bank194, bank202, bank210, bank218, bank226, bank235, bank243, bank252, bank657, bank573, bank658, bank574, bank260, bank268, bank276, bank884, bank284, bank293, bank302, bank659, bank575, bank660, bank576, bank310, bank798, bank318, bank327, bank335, bank661, bank577, bank662, bank578, bank343, bank352, bank663, bank579, bank664, bank580]
    True.intro
    ⟨excluded98, excluded669, excluded106, excluded115, excluded658, excluded123, excluded132, excluded141, excluded149, excluded158, excluded166, excluded175, excluded184, excluded193, excluded600, excluded516, excluded601, excluded517, excluded202, excluded210, excluded218, excluded226, excluded234, excluded243, excluded251, excluded260, excluded268, excluded276, excluded602, excluded518, excluded603, excluded519, excluded284, excluded292, excluded300, excluded308, excluded316, excluded325, excluded333, excluded342, excluded604, excluded520, excluded605, excluded521, excluded350, excluded358, excluded366, excluded647, excluded374, excluded383, excluded392, excluded606, excluded522, excluded607, excluded523, excluded400, excluded636, excluded408, excluded417, excluded425, excluded608, excluded524, excluded609, excluded525, excluded433, excluded442, excluded610, excluded526, excluded611, excluded527, True.intro⟩
    (by decide +kernel) cuts1199

theorem excluded1201 : Blocked 9 1 bank9 :=
  block_step [bank10, bank1044, bank11, bank12, bank13, bank14, bank15, bank16, bank665, bank17]
    [bank991, bank1081, bank904, bank1082, bank1083, bank1003, bank1004, bank1005, bank1006, bank1007, bank1008, bank1009, bank1010, bank1011, bank1012, bank358, bank359, bank815, bank360, bank361, bank728, bank801, bank362, bank729, bank363, bank364, bank365, bank366, bank367]
    ⟨excluded100, excluded664, excluded101, excluded102, excluded103, excluded104, excluded105, excluded106, excluded612, excluded107, True.intro⟩
    ⟨excluded1085, excluded1164, excluded1009, excluded1165, excluded1166, excluded1096, excluded1097, excluded1098, excluded1099, excluded1100, excluded1101, excluded1102, excluded1103, excluded1104, excluded1105, excluded677, excluded678, excluded931, excluded679, excluded680, excluded855, excluded919, excluded681, excluded856, excluded682, excluded683, excluded684, excluded685, excluded686, True.intro⟩
    (by decide +kernel) cuts1201

theorem excluded1203 : Blocked 9 1 bank26 :=
  block_step [bank27, bank28, bank957, bank29, bank30, bank31, bank32, bank33, bank666, bank34]
    [bank994, bank905, bank1084, bank1085, bank1086, bank915, bank916, bank368, bank359, bank925, bank926, bank927, bank928, bank929, bank930, bank931, bank932, bank817, bank369, bank370, bank731, bank371, bank372, bank373, bank374, bank375, bank376]
    ⟨excluded117, excluded118, excluded654, excluded119, excluded120, excluded121, excluded122, excluded123, excluded613, excluded124, True.intro⟩
    ⟨excluded1087, excluded1010, excluded1167, excluded1168, excluded1169, excluded1019, excluded1020, excluded687, excluded678, excluded1029, excluded1030, excluded1031, excluded1032, excluded1033, excluded1034, excluded1035, excluded1036, excluded933, excluded688, excluded689, excluded858, excluded690, excluded691, excluded692, excluded693, excluded694, excluded695, True.intro⟩
    (by decide +kernel) cuts1203

theorem excluded1204 : Blocked 9 1 bank35 :=
  block_step [bank36, bank37, bank38, bank39, bank40, bank41, bank42, bank669, bank43]
    [bank995, bank907, bank818, bank1087, bank354, bank1067, bank471, bank1051, bank819, bank398, bank977, bank421, bank963, bank820, bank821, bank732, bank402, bank802, bank403, bank733, bank404, bank721, bank405, bank703, bank697, bank406, bank682]
    ⟨excluded126, excluded127, excluded128, excluded129, excluded130, excluded131, excluded132, excluded616, excluded133, True.intro⟩
    ⟨excluded1088, excluded1011, excluded934, excluded1170, excluded673, excluded1152, excluded790, excluded1136, excluded935, excluded717, excluded1073, excluded740, excluded1059, excluded936, excluded937, excluded859, excluded721, excluded920, excluded722, excluded860, excluded723, excluded848, excluded724, excluded830, excluded824, excluded725, excluded809, True.intro⟩
    (by decide +kernel) cuts1204

theorem excluded1206 : Blocked 9 1 bank52 :=
  block_step [bank53, bank54, bank55, bank56, bank57, bank58, bank59, bank672, bank60]
    [bank997, bank909, bank735, bank1089, bank736, bank355, bank1066, bank465, bank1052, bank399, bank978, bank422, bank964, bank823, bank402, bank889, bank423, bank824, bank737, bank424, bank722, bank416, bank704, bank425, bank698, bank426, bank683]
    ⟨excluded143, excluded144, excluded145, excluded146, excluded147, excluded148, excluded149, excluded619, excluded150, True.intro⟩
    ⟨excluded1090, excluded1013, excluded862, excluded1172, excluded863, excluded674, excluded1151, excluded784, excluded1137, excluded718, excluded1074, excluded741, excluded1060, excluded939, excluded721, excluded996, excluded742, excluded940, excluded864, excluded743, excluded849, excluded735, excluded831, excluded744, excluded825, excluded745, excluded810, True.intro⟩
    (by decide +kernel) cuts1206

theorem excluded1208 : Blocked 9 1 bank69 :=
  block_step [bank70, bank71, bank72, bank73, bank74, bank75, bank76, bank673, bank77]
    [bank999, bank911, bank705, bank1090, bank356, bank1068, bank483, bank1053, bank400, bank979, bank429, bank965, bank826, bank404, bank890, bank430, bank827, bank739, bank424, bank803, bank427, bank740, bank699, bank431, bank684]
    ⟨excluded160, excluded161, excluded162, excluded163, excluded164, excluded165, excluded166, excluded620, excluded167, True.intro⟩
    ⟨excluded1092, excluded1015, excluded832, excluded1173, excluded675, excluded1153, excluded802, excluded1138, excluded719, excluded1075, excluded748, excluded1061, excluded942, excluded723, excluded997, excluded749, excluded943, excluded866, excluded743, excluded921, excluded746, excluded867, excluded826, excluded750, excluded811, True.intro⟩
    (by decide +kernel) cuts1208

theorem excluded1209 : Blocked 9 1 bank78 :=
  block_step [bank79, bank80, bank81, bank82, bank83, bank84, bank85, bank670, bank86]
    [bank1108, bank1000, bank1083, bank1105, bank912, bank1085, bank705, bank1090, bank1091, bank394, bank365, bank433, bank374, bank900, bank706, bank828, bank407, bank378, bank812, bank707, bank741, bank411, bank386, bank708, bank412, bank413]
    ⟨excluded169, excluded170, excluded171, excluded172, excluded173, excluded174, excluded175, excluded617, excluded176, True.intro⟩
    ⟨excluded1191, excluded1093, excluded1166, excluded1188, excluded1016, excluded1168, excluded832, excluded1173, excluded1174, excluded713, excluded684, excluded752, excluded693, excluded1005, excluded833, excluded944, excluded726, excluded697, excluded928, excluded834, excluded868, excluded730, excluded705, excluded835, excluded731, excluded732, True.intro⟩
    (by decide +kernel) cuts1209

theorem excluded1210 : Blocked 9 1 bank87 :=
  block_step [bank88, bank89, bank90, bank91, bank92, bank93, bank94, bank675, bank95]
    [bank1001, bank913, bank685, bank1092, bank357, bank1069, bank484, bank1054, bank401, bank981, bank439, bank966, bank829, bank891, bank440, bank830, bank742, bank425, bank804, bank428, bank743, bank723, bank438, bank709]
    ⟨excluded178, excluded179, excluded180, excluded181, excluded182, excluded183, excluded184, excluded622, excluded185, True.intro⟩
    ⟨excluded1094, excluded1017, excluded812, excluded1175, excluded676, excluded1154, excluded803, excluded1139, excluded720, excluded1077, excluded758, excluded1062, excluded945, excluded998, excluded759, excluded946, excluded869, excluded744, excluded922, excluded747, excluded870, excluded850, excluded757, excluded836, True.intro⟩
    (by decide +kernel) cuts1210

theorem excluded1211 : Blocked 9 1 bank96 :=
  block_step [bank97, bank98, bank99, bank100, bank101, bank102, bank103, bank671, bank104]
    [bank1002, bank1106, bank914, bank1086, bank1088, bank1091, bank685, bank1092, bank397, bank367, bank441, bank376, bank831, bank686, bank888, bank408, bank832, bank417, bank744, bank687, bank418, bank409, bank688, bank419, bank413]
    ⟨excluded187, excluded188, excluded189, excluded190, excluded191, excluded192, excluded193, excluded618, excluded194, True.intro⟩
    ⟨excluded1095, excluded1189, excluded1018, excluded1169, excluded1171, excluded1174, excluded812, excluded1175, excluded716, excluded686, excluded760, excluded695, excluded947, excluded813, excluded995, excluded727, excluded948, excluded736, excluded871, excluded814, excluded737, excluded728, excluded815, excluded738, excluded732, True.intro⟩
    (by decide +kernel) cuts1211

theorem excluded1216 : Blocked 9 1 bank137 :=
  block_step [bank138, bank139, bank140, bank141, bank142, bank143, bank144, bank680, bank145]
    [bank1007, bank919, bank736, bank355, bank1099, bank410, bank1093, bank1055, bank749, bank1056, bank1057, bank1058, bank466, bank984, bank472, bank968, bank750, bank837, bank469, bank895, bank473, bank838, bank751, bank752, bank474, bank726, bank475, bank710, bank476, bank701, bank477, bank689]
    ⟨excluded228, excluded229, excluded230, excluded231, excluded232, excluded233, excluded234, excluded627, excluded235, True.intro⟩
    ⟨excluded1100, excluded1023, excluded863, excluded674, excluded1182, excluded729, excluded1176, excluded1140, excluded876, excluded1141, excluded1142, excluded1143, excluded785, excluded1080, excluded791, excluded1064, excluded877, excluded953, excluded788, excluded1002, excluded792, excluded954, excluded878, excluded879, excluded793, excluded853, excluded794, excluded837, excluded795, excluded828, excluded796, excluded816, True.intro⟩
    (by decide +kernel) cuts1216

theorem excluded1218 : Blocked 9 1 bank154 :=
  block_step [bank155, bank156, bank157, bank158, bank159, bank160, bank161, bank681, bank162]
    [bank1009, bank921, bank356, bank1100, bank414, bank1094, bank1057, bank711, bank1059, bank467, bank985, bank478, bank969, bank840, bank470, bank896, bank479, bank841, bank754, bank474, bank809, bank480, bank755, bank460, bank702, bank481, bank690]
    ⟨excluded245, excluded246, excluded247, excluded248, excluded249, excluded250, excluded251, excluded628, excluded252, True.intro⟩
    ⟨excluded1102, excluded1025, excluded675, excluded1183, excluded733, excluded1177, excluded1142, excluded838, excluded1144, excluded786, excluded1081, excluded797, excluded1065, excluded956, excluded789, excluded1003, excluded798, excluded957, excluded881, excluded793, excluded927, excluded799, excluded882, excluded779, excluded829, excluded800, excluded817, True.intro⟩
    (by decide +kernel) cuts1218

theorem excluded1226 : Blocked 9 1 bank219 :=
  block_step [bank220, bank221, bank222, bank223, bank224, bank225, bank226, bank676, bank227]
    [bank1017, bank929, bank400, bank1101, bank415, bank1095, bank467, bank1072, bank488, bank1060, bank970, bank713, bank971, bank972, bank849, bank443, bank892, bank447, bank850, bank763, bank445, bank805, bank448, bank764, bank700, bank449, bank692]
    ⟨excluded310, excluded311, excluded312, excluded313, excluded314, excluded315, excluded316, excluded623, excluded317, True.intro⟩
    ⟨excluded1110, excluded1033, excluded719, excluded1184, excluded734, excluded1178, excluded786, excluded1157, excluded807, excluded1145, excluded1066, excluded840, excluded1067, excluded1068, excluded965, excluded762, excluded999, excluded766, excluded966, excluded890, excluded764, excluded923, excluded767, excluded891, excluded827, excluded768, excluded819, True.intro⟩
    (by decide +kernel) cuts1226

theorem excluded1228 : Blocked 9 1 bank236 :=
  block_step [bank237, bank238, bank239, bank240, bank241, bank242, bank243, bank677, bank244]
    [bank1019, bank931, bank401, bank1102, bank420, bank1096, bank967, bank468, bank1073, bank489, bank1061, bank972, bank988, bank693, bank973, bank852, bank444, bank893, bank450, bank853, bank766, bank446, bank806, bank451, bank767, bank724, bank452, bank715]
    ⟨excluded327, excluded328, excluded329, excluded330, excluded331, excluded332, excluded333, excluded624, excluded334, True.intro⟩
    ⟨excluded1112, excluded1035, excluded720, excluded1185, excluded739, excluded1179, excluded1063, excluded787, excluded1158, excluded808, excluded1146, excluded1068, excluded1082, excluded820, excluded1069, excluded968, excluded763, excluded1000, excluded769, excluded969, excluded893, excluded765, excluded924, excluded770, excluded894, excluded851, excluded771, excluded842, True.intro⟩
    (by decide +kernel) cuts1228

theorem excluded1233 : Blocked 9 1 bank277 :=
  block_step [bank278, bank279, bank280, bank881, bank281, bank282, bank283, bank284, bank667, bank285]
    [bank1024, bank936, bank820, bank822, bank706, bank377, bank378, bank835, bank836, bank379, bank380, bank845, bank846, bank392, bank393, bank855, bank856, bank716, bank858, bank860, bank861, bank772, bank381, bank382, bank717, bank383, bank384]
    ⟨excluded368, excluded369, excluded370, excluded644, excluded371, excluded372, excluded373, excluded374, excluded614, excluded375, True.intro⟩
    ⟨excluded1117, excluded1040, excluded936, excluded938, excluded833, excluded696, excluded697, excluded951, excluded952, excluded698, excluded699, excluded961, excluded962, excluded711, excluded712, excluded971, excluded972, excluded843, excluded974, excluded975, excluded976, excluded899, excluded700, excluded701, excluded844, excluded702, excluded703, True.intro⟩
    (by decide +kernel) cuts1233

theorem excluded1234 : Blocked 9 1 bank286 :=
  block_step [bank287, bank288, bank289, bank290, bank291, bank292, bank293, bank678, bank294]
    [bank1025, bank937, bank821, bank1103, bank442, bank1097, bank458, bank1070, bank486, bank1062, bank444, bank982, bank456, bank974, bank857, bank860, bank899, bank695, bank886, bank773, bank453, bank807, bank457, bank774, bank454, bank725, bank455, bank718]
    ⟨excluded377, excluded378, excluded379, excluded380, excluded381, excluded382, excluded383, excluded625, excluded384, True.intro⟩
    ⟨excluded1118, excluded1041, excluded937, excluded1186, excluded761, excluded1180, excluded777, excluded1155, excluded805, excluded1147, excluded763, excluded1078, excluded775, excluded1070, excluded973, excluded975, excluded1004, excluded822, excluded993, excluded900, excluded772, excluded925, excluded776, excluded901, excluded773, excluded852, excluded774, excluded845, True.intro⟩
    (by decide +kernel) cuts1234

theorem excluded1237 : Blocked 9 1 bank311 :=
  block_step [bank312, bank313, bank314, bank315, bank796, bank316, bank317, bank318, bank668, bank319]
    [bank1028, bank940, bank737, bank738, bank707, bank385, bank386, bank751, bank753, bank712, bank1065, bank387, bank1063, bank388, bank761, bank762, bank395, bank396, bank769, bank770, bank863, bank389, bank382, bank719, bank776, bank778, bank779, bank390, bank391]
    ⟨excluded402, excluded403, excluded404, excluded405, excluded634, excluded406, excluded407, excluded408, excluded615, excluded409, True.intro⟩
    ⟨excluded1121, excluded1044, excluded864, excluded865, excluded834, excluded704, excluded705, excluded878, excluded880, excluded839, excluded1150, excluded706, excluded1148, excluded707, excluded888, excluded889, excluded714, excluded715, excluded896, excluded897, excluded978, excluded708, excluded701, excluded846, excluded903, excluded904, excluded905, excluded709, excluded710, True.intro⟩
    (by decide +kernel) cuts1237

theorem excluded1240 : Blocked 9 1 bank336 :=
  block_step [bank337, bank338, bank339, bank340, bank341, bank342, bank343, bank679, bank344]
    [bank1031, bank943, bank1104, bank461, bank1098, bank460, bank1071, bank487, bank1064, bank983, bank462, bank975, bank866, bank454, bank894, bank463, bank887, bank780, bank459, bank808, bank464, bank800, bank696, bank720]
    ⟨excluded427, excluded428, excluded429, excluded430, excluded431, excluded432, excluded433, excluded626, excluded434, True.intro⟩
    ⟨excluded1124, excluded1047, excluded1187, excluded780, excluded1181, excluded779, excluded1156, excluded806, excluded1149, excluded1079, excluded781, excluded1071, excluded981, excluded773, excluded1001, excluded782, excluded994, excluded906, excluded778, excluded926, excluded783, excluded918, excluded823, excluded847, True.intro⟩
    (by decide +kernel) cuts1240

theorem excluded1241 : Blocked 9 1 bank345 :=
  block_step [bank346, bank347, bank348, bank349, bank350, bank351, bank352, bank674, bank353]
    [bank1032, bank944, bank708, bank688, bank432, bank413, bank691, bank485, bank482, bank714, bank694, bank980, bank434, bank976, bank435, bank901, bank717, bank867, bank436, bank384, bank781, bank437, bank391, bank696, bank720]
    ⟨excluded436, excluded437, excluded438, excluded439, excluded440, excluded441, excluded442, excluded621, excluded443, True.intro⟩
    ⟨excluded1125, excluded1048, excluded835, excluded815, excluded751, excluded732, excluded818, excluded804, excluded801, excluded841, excluded821, excluded1076, excluded753, excluded1072, excluded754, excluded1006, excluded844, excluded982, excluded755, excluded703, excluded907, excluded756, excluded710, excluded823, excluded847, True.intro⟩
    (by decide +kernel) cuts1241

theorem excluded1242 : Blocked 9 1 bank777 :=
  block_step [bank792, bank793, bank794, bank795, bank797, bank798, bank799]
    [bank727, bank1076, bank728, bank730, bank989, bank731, bank732, bank734, bank739, bank812, bank741, bank742, bank744, bank783, bank784, bank745, bank746, bank747, bank748, bank754, bank813, bank756, bank757, bank758, bank1078, bank785, bank786, bank759, bank760, bank763, bank765, bank766, bank768, bank790, bank791, bank771, bank902, bank772, bank773, bank775, bank787, bank782, bank780, bank781, bank788, bank789]
    ⟨excluded630, excluded631, excluded632, excluded633, excluded635, excluded636, excluded637, True.intro⟩
    ⟨excluded854, excluded1159, excluded855, excluded857, excluded1083, excluded858, excluded859, excluded861, excluded866, excluded928, excluded868, excluded869, excluded871, excluded909, excluded910, excluded872, excluded873, excluded874, excluded875, excluded881, excluded929, excluded883, excluded884, excluded885, excluded1161, excluded911, excluded912, excluded886, excluded887, excluded890, excluded892, excluded893, excluded895, excluded916, excluded917, excluded898, excluded1007, excluded899, excluded900, excluded902, excluded913, excluded908, excluded906, excluded907, excluded914, excluded915, True.intro⟩
    (by decide +kernel) cuts1242

theorem excluded1243 : Blocked 9 1 bank859 :=
  block_step [bank878, bank879, bank880, bank882, bank883, bank884, bank885]
    [bank814, bank1079, bank815, bank816, bank990, bank817, bank823, bank825, bank826, bank900, bank828, bank829, bank831, bank868, bank869, bank833, bank834, bank837, bank839, bank840, bank842, bank843, bank844, bank870, bank871, bank847, bank848, bank849, bank851, bank852, bank854, bank876, bank877, bank862, bank902, bank863, bank864, bank865, bank872, bank873, bank866, bank901, bank867, bank874, bank875]
    ⟨excluded641, excluded642, excluded643, excluded645, excluded646, excluded647, excluded648, True.intro⟩
    ⟨excluded930, excluded1162, excluded931, excluded932, excluded1084, excluded933, excluded939, excluded941, excluded942, excluded1005, excluded944, excluded945, excluded947, excluded983, excluded984, excluded949, excluded950, excluded953, excluded955, excluded956, excluded958, excluded959, excluded960, excluded985, excluded986, excluded963, excluded964, excluded965, excluded967, excluded968, excluded970, excluded991, excluded992, excluded977, excluded1007, excluded978, excluded979, excluded980, excluded987, excluded988, excluded981, excluded1006, excluded982, excluded989, excluded990, True.intro⟩
    (by decide +kernel) cuts1243

theorem excluded1244 : Blocked 9 1 bank906 :=
  block_step [bank955, bank956, bank958, bank959, bank960, bank961, bank962]
    [bank903, bank1080, bank904, bank907, bank908, bank909, bank910, bank911, bank1105, bank912, bank913, bank1106, bank914, bank917, bank918, bank919, bank920, bank921, bank922, bank923, bank924, bank946, bank945, bank933, bank934, bank935, bank990, bank936, bank937, bank938, bank947, bank948, bank939, bank989, bank940, bank941, bank942, bank949, bank950, bank943, bank944, bank951, bank952, bank953, bank954]
    ⟨excluded652, excluded653, excluded655, excluded656, excluded657, excluded658, excluded659, True.intro⟩
    ⟨excluded1008, excluded1163, excluded1009, excluded1011, excluded1012, excluded1013, excluded1014, excluded1015, excluded1188, excluded1016, excluded1017, excluded1189, excluded1018, excluded1021, excluded1022, excluded1023, excluded1024, excluded1025, excluded1026, excluded1027, excluded1028, excluded1050, excluded1049, excluded1037, excluded1038, excluded1039, excluded1084, excluded1040, excluded1041, excluded1042, excluded1051, excluded1052, excluded1043, excluded1083, excluded1044, excluded1045, excluded1046, excluded1053, excluded1054, excluded1047, excluded1048, excluded1055, excluded1056, excluded1057, excluded1058, True.intro⟩
    (by decide +kernel) cuts1244

theorem excluded1245 : Blocked 9 1 bank992 :=
  block_step [bank1043, bank1045, bank1046, bank1047, bank1048, bank1049, bank1050]
    [bank993, bank1080, bank994, bank995, bank996, bank997, bank1107, bank998, bank999, bank1108, bank1000, bank1001, bank1002, bank1013, bank1014, bank1015, bank1016, bank1017, bank1018, bank1019, bank1020, bank1033, bank1034, bank1021, bank1022, bank1023, bank1079, bank1024, bank1025, bank1026, bank1035, bank1036, bank1027, bank1076, bank1028, bank1029, bank1030, bank1077, bank1037, bank1038, bank1031, bank1032, bank1039, bank1040, bank1041, bank1042]
    ⟨excluded663, excluded665, excluded666, excluded667, excluded668, excluded669, excluded670, True.intro⟩
    ⟨excluded1086, excluded1163, excluded1087, excluded1088, excluded1089, excluded1090, excluded1190, excluded1091, excluded1092, excluded1191, excluded1093, excluded1094, excluded1095, excluded1106, excluded1107, excluded1108, excluded1109, excluded1110, excluded1111, excluded1112, excluded1113, excluded1126, excluded1127, excluded1114, excluded1115, excluded1116, excluded1162, excluded1117, excluded1118, excluded1119, excluded1128, excluded1129, excluded1120, excluded1159, excluded1121, excluded1122, excluded1123, excluded1160, excluded1130, excluded1131, excluded1124, excluded1125, excluded1132, excluded1133, excluded1134, excluded1135, True.intro⟩
    (by decide +kernel) cuts1245

theorem excluded1246 : Blocked 10 1 bank0 :=
  block_step [bank490, bank503, bank516, bank529, bank542, bank555, bank568]
    [bank1, bank992, bank9, bank18, bank906, bank26, bank35, bank44, bank52, bank61, bank69, bank78, bank87, bank96, bank105, bank113, bank121, bank129, bank137, bank146, bank154, bank163, bank171, bank179, bank187, bank195, bank203, bank211, bank219, bank228, bank236, bank245, bank253, bank261, bank269, bank859, bank277, bank286, bank295, bank303, bank777, bank311, bank320, bank328, bank336, bank345]
    ⟨excluded1193, excluded1194, excluded1195, excluded1196, excluded1197, excluded1198, excluded1199, True.intro⟩
    ⟨excluded1200, excluded1245, excluded1201, excluded1202, excluded1244, excluded1203, excluded1204, excluded1205, excluded1206, excluded1207, excluded1208, excluded1209, excluded1210, excluded1211, excluded1212, excluded1213, excluded1214, excluded1215, excluded1216, excluded1217, excluded1218, excluded1219, excluded1220, excluded1221, excluded1222, excluded1223, excluded1224, excluded1225, excluded1226, excluded1227, excluded1228, excluded1229, excluded1230, excluded1231, excluded1232, excluded1243, excluded1233, excluded1234, excluded1235, excluded1236, excluded1242, excluded1237, excluded1238, excluded1239, excluded1240, excluded1241, True.intro⟩
    (by decide +kernel) cuts1246

theorem zero_excluded : Blocked 9 0 root := excluded1192

theorem one_excluded : Blocked 10 1 root := excluded1246

end PEqualNP.Outside.L_meta_10852_aux

open PEqualNP.Outside.L_meta_10852_aux

theorem PEqualNP.Outside.L_meta_10852 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o basis single computes
  by_cases used : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact ⟨replacement.gates, replacement.output, replacement_basis,
      lower_with_not gates o basis single used computes zero_excluded one_excluded, replacement_correct⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    refine ⟨?_, (basis g hg).2⟩
    rcases (basis g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (used ⟨g, hg, h⟩).elim
