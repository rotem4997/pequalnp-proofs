import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_14802

private abbrev Q := BitVec 64

private def norm (w : Q) := if w.getLsbD 0 then ~~~w else w

private def ops (a b : Q) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]

private def Trail (t : Q) (s : Finset Q) (n : ℕ) : Prop :=
  ∀ P : Finset Q → ℕ → Prop,
    (∀ k, P {t} k) →
    (∀ {r : Finset Q} {a b c : Q} {k : ℕ}, a ≠ b → c ∉ insert a (insert b r) →
      c ≠ 0 → c ∈ ops a b → P (insert c r) k → P (insert a (insert b r)) (k+1)) →
    P s n

private theorem Trail.done {t : Q} (k : ℕ) : Trail t {t} k :=
  fun _ done _ => done k

private theorem Trail.step {t a b c : Q} {r : Finset Q} {k : ℕ} (hab : a ≠ b)
    (hf : c ∉ insert a (insert b r)) (nz : c ≠ 0) (hc : c ∈ ops a b)
    (h : Trail t (insert c r) k) : Trail t (insert a (insert b r)) (k+1) :=
  fun P done step => step hab hf nz hc (h P done step)

private theorem trail_ind {t : Q} {P : Finset Q → ℕ → Prop} {s n} (h : Trail t s n)
    (done : ∀ k, P {t} k)
    (step : ∀ {r a b c k}, a ≠ b → c ∉ insert a (insert b r) → c ≠ 0 → c ∈ ops a b →
      Trail t (insert c r) k → P (insert c r) k → P (insert a (insert b r)) (k+1)) : P s n :=
  (h (fun r k => Trail t r k ∧ P r k) (fun k => ⟨Trail.done k, done k⟩)
    (fun hab hf nz hc h' => ⟨Trail.step hab hf nz hc h'.1, step hab hf nz hc h'.1 h'.2⟩)).2

private theorem trail_lift {t s n} (h : Trail t s n) : Trail t s (n+1) := by
  apply trail_ind (P := fun s n => Trail t s (n+1)) h
  · intro k; exact Trail.done _
  · intro r a b c k hab hf nz hc _ ih; exact .step hab hf nz hc ih

private theorem trail_mono {t s n m} (h : Trail t s n) (le : n ≤ m) : Trail t s m := by
  induction le with
  | refl => exact h
  | step _ ih => exact trail_lift ih

private theorem trail_card {t s n} (h : Trail t s n) : s.card ≤ n+1 := by
  apply trail_ind (P := fun s n => s.card ≤ n+1) h
  · simp
  · intro r a b c k hab fresh nz hc h ih
    have hn : c ∉ r := fun hh => fresh (by simp [hh])
    rw [Finset.card_insert_of_notMem hn] at ih
    have := Finset.card_insert_le a (insert b r)
    have := Finset.card_insert_le b r
    omega

private def construction (t : Q) : ℕ → Finset Q → Prop
  | 0,s => t∈s
  | k+1,s => construction t k s ∨ ∃ a∈s,∃ b∈s,a≠b ∧
      ∃c∈ops a b,c≠0 ∧ c∉s ∧ construction t k (insert c s)

private lemma constructLift {t s i j} (h : i≤j) (ok : construction t i s) :
    construction t j s := by
  induction h with
  | refl => exact ok
  | step _ ih => exact Or.inl ih

private lemma extractConstruction {t : Q} {s : Finset Q} {k} (h : construction t k s) :
    ∃r⊆s, Trail t r k := by
  induction k generalizing s with
  | zero => exact ⟨{t},Finset.singleton_subset_iff.mpr h,Trail.done 0⟩
  | succ k ih =>
    rcases h with short|⟨a,ha,b,hb,ab,c,hc,nz,newC,more⟩
    · obtain ⟨r,hr,ok⟩:=ih short
      exact ⟨r,hr,trail_lift ok⟩
    · obtain ⟨v,hv,ok⟩:=ih more
      by_cases present : c∈v
      · let r:=v.erase c
        have sub : r⊆s := by
          intro x hx
          exact (Finset.mem_insert.mp (hv (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx)
        have inputs : insert a (insert b r) ⊆s := Finset.insert_subset_iff.mpr ⟨ha,Finset.insert_subset_iff.mpr ⟨hb,sub⟩⟩
        have tail : Trail t (insert c r) k := by simpa only [r,Finset.insert_erase present] using ok
        exact ⟨_,inputs,.step ab (fun yes => newC (inputs yes)) nz hc tail⟩
      · exact ⟨v,fun x hx => (Finset.mem_insert.mp (hv hx)).resolve_left (fun e => present (e ▸ hx)),trail_lift ok⟩

private lemma realizeTrail {t : Q} {s : Finset Q} {k : Nat} (h : Trail t s k) :
    ∀P : Finset Q,s⊆P → construction t k P := by
  apply trail_ind (P:=fun s k => ∀P : Finset Q,s⊆P → construction t k P) h
  · intro k P sub
    exact constructLift (Nat.zero_le k) (show construction t 0 P from sub (Finset.mem_singleton_self _))
  · intro r a b c k ab fresh nz hc tail ih P sub
    have small : r⊆P := fun w hw => sub (by simp [hw])
    have next := ih (insert c P) (Finset.insert_subset_insert _ small)
    by_cases m : c∈P
    · rw [Finset.insert_eq_of_mem m] at next
      exact Or.inl next
    · exact Or.inr ⟨a,sub (by simp),b,sub (by simp),ab,c,hc,nz,m,next⟩

private def restrictWord (d w : Q) := w &&& d
private lemma restrictOps (d a b c : Q) (h : c∈ops a b) :
    restrictWord d c∈ops (restrictWord d a) (restrictWord d b) := by
  simp only [ops,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  rcases h with rfl|rfl|rfl|rfl
  · left;apply BitVec.eq_of_getLsbD_eq;intro i hi
    simp [restrictWord,Bool.and_comm,Bool.and_left_comm]
  · right;left;apply BitVec.eq_of_getLsbD_eq;intro i hi
    simp only [restrictWord,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases d.getLsbD i <;> rfl
  · right;right;left;apply BitVec.eq_of_getLsbD_eq;intro i hi
    simp only [restrictWord,BitVec.getLsbD_and,BitVec.getLsbD_not,decide_eq_true hi,Bool.true_and]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases d.getLsbD i <;> rfl
  · right;right;right;apply BitVec.eq_of_getLsbD_eq;intro i hi
    simp only [restrictWord,BitVec.getLsbD_and,BitVec.getLsbD_not,decide_eq_true hi,Bool.true_and]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases d.getLsbD i <;> rfl

private def dead (d : Q) (s : Finset Q) := (s.filter fun w => restrictWord d w=0).card
private lemma deadLe (d a : Q) (s : Finset Q) :
    dead d (insert a s) ≤ dead d s+(if restrictWord d a=0 then 1 else 0) := by
  by_cases h : restrictWord d a=0
  · simpa only [dead,Finset.filter_insert,ite_eq_left h] using Finset.card_insert_le a (s.filter fun w => restrictWord d w=0)
  · simp only [dead,Finset.filter_insert,ite_eq_right h,Nat.add_zero,le_refl]
private lemma deadEq (d a : Q) (s : Finset Q) (h : a∉s) :
    dead d (insert a s)=dead d s+(if restrictWord d a=0 then 1 else 0) := by
  have absent : a∉s.filter (fun w => restrictWord d w=0) := fun m => h (Finset.mem_filter.mp m).1
  by_cases z : restrictWord d a=0
  · simp only [dead,Finset.filter_insert,ite_eq_left z,Finset.card_insert_of_notMem absent]
  · simp only [dead,Finset.filter_insert,ite_eq_right z,Nat.add_zero]

private lemma zeroLeft (b c : Q) (h : c∈ops 0 b) : c=0 ∨ c=b := by
  change c∈ops (0#64) b at h
  change c=0#64 ∨ c=b
  simp only [ops,List.mem_cons,List.not_mem_nil,or_false,BitVec.zero_and,BitVec.zero_or,
    BitVec.not_zero,BitVec.and_allOnes] at h
  tauto
private lemma zeroRight (a c : Q) (h : c∈ops a 0) : c=0 ∨ c=a := by
  change c∈ops a (0#64) at h
  change c=0#64 ∨ c=a
  simp only [ops,List.mem_cons,List.not_mem_nil,or_false,BitVec.and_zero,BitVec.or_zero,
    BitVec.not_zero,BitVec.and_allOnes,BitVec.zero_and] at h
  tauto
private lemma sameOp (a c : Q) (h : c∈ops a a) : c=a ∨ c=0 := by simpa [ops] using h

private theorem projected {t : Q} {s : Finset Q} {k} (h : Trail t s k) (d : Q)
    (nonzero : restrictWord d t≠0) :
    dead d s≤k ∧ ∀P : Finset Q,(∀x∈s,restrictWord d x≠0 → restrictWord d x∈P) →
      construction (restrictWord d t) (k-dead d s) P := by
  apply trail_ind (P:=fun s k => dead d s≤k ∧ ∀P : Finset Q,
    (∀x∈s,restrictWord d x≠0 → restrictWord d x∈P) → construction (restrictWord d t) (k-dead d s) P) h
  · intro k
    have no : dead d {t}=0 := by
      unfold dead
      rw [Finset.filter_singleton,ite_eq_right nonzero]
      rfl
    refine ⟨by omega,?_⟩
    intro P src
    apply constructLift (Nat.zero_le _)
    exact src t (by simp) nonzero
  · intro r a b c k ab fresh nz hc tail ih
    have cr : c∉r := fun hm => fresh (by simp [hm])
    have full := deadEq d c r cr
    have one := deadLe d a (insert b r)
    have two := deadLe d b r
    have op := restrictOps d a b c hc
    have paid := ih.1
    by_cases bothNew : restrictWord d c≠0 ∧ restrictWord d c≠restrictWord d a ∧ restrictWord d c≠restrictWord d b
    · obtain ⟨cz,ca,cb⟩:=bothNew
      have az : restrictWord d a≠0 := by
        intro e;rw [e] at op;exact (zeroLeft _ _ op).elim cz cb
      have bz : restrictWord d b≠0 := by
        intro e;rw [e] at op;exact (zeroRight _ _ op).elim cz ca
      have unequal : restrictWord d a≠restrictWord d b := by
        intro e;rw [e] at op;exact (sameOp _ _ op).elim cb cz
      simp only [cz,az,bz,ite_false,Nat.add_zero] at full one two
      refine ⟨by omega,?_⟩
      intro P src
      have ha:=src a (by simp) az
      have hb:=src b (by simp) bz
      have next := ih.2 (insert (restrictWord d c) P) (by
        intro w hw hz
        rcases Finset.mem_insert.mp hw with rfl|hr
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (src w (by simp [hr]) hz))
      by_cases avail : restrictWord d c∈P
      · rw [Finset.insert_eq_of_mem avail] at next
        exact constructLift (by omega) next
      · have add : construction (restrictWord d t) (k-dead d (insert c r)+1) P :=
          Or.inr ⟨_,ha,_,hb,unequal,_,op,cz,avail,next⟩
        exact constructLift (by omega) add
    · have balance : dead d (insert a (insert b r)) ≤ dead d (insert c r)+1 := by
        by_cases za : restrictWord d a=0 <;> by_cases zb : restrictWord d b=0
        · rw [za,zb] at op
          have zero : restrictWord d c=0 := by simpa using zeroLeft _ _ op
          simp only [za,zb,zero,ite_true] at full one two
          omega
        all_goals simp only [za,zb,ite_true,ite_false,Nat.add_zero] at one two <;> split at full <;> omega
      refine ⟨by omega,?_⟩
      intro P src
      have next := ih.2 P (by
        intro w hw hz
        rcases Finset.mem_insert.mp hw with rfl|hr
        · have ab' : restrictWord d w=restrictWord d a ∨ restrictWord d w=restrictWord d b := by tauto
          rcases ab' with eq|eq
          · exact eq ▸ src a (by simp) (eq ▸ hz)
          · exact eq ▸ src b (by simp) (eq ▸ hz)
        · exact src w (by simp [hr]) hz)
      exact constructLift (by omega) next

private theorem trail_sep {t s n} (h : Trail t s n) (i j : ℕ) (hi : i < 64) (hj : j < 64)
    (same : ∀ x ∈ s, x.getLsbD i = x.getLsbD j) : t.getLsbD i = t.getLsbD j := by
  revert same
  apply trail_ind (P := fun s _ => (∀ x ∈ s, x.getLsbD i = x.getLsbD j) → t.getLsbD i = t.getLsbD j) h
  · intro k same; exact same _ (by simp)
  · intro r a b c k hab fresh nz hc h ih same
    apply ih
    have ha := same a (by simp)
    have hb := same b (by simp)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxr
    · simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;>
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hi, decide_eq_true hj, ha, hb]
    · exact same _ (by simp [hxr])

private def groups : List Q → Q → Q → List (Q × Q)
  | [],p,n => if p=0 ∨ n=0 then [] else [(p,n)]
  | w::ws,p,n => if p=0 ∨ n=0 then [] else
      groups ws (p &&& w) (n &&& w) ++ groups ws (p &&& ~~~w) (n &&& ~~~w)

private lemma nonzeroBit {a : Q} (h : a≠0) : ∃i : Fin 64,a.getLsbD i.val=true := by
  by_contra none
  apply h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have notOn : a.getLsbD i≠true := fun yes => none ⟨⟨i,hi⟩,yes⟩
  rw [Bool.eq_false_iff.mpr notOn]
  simp

private lemma groupFacts (ws : List Q) (p n : Q) {u v : Q} (mem : (u,v) ∈ groups ws p n) :
    u ≠ 0 ∧ v ≠ 0 ∧
    (∀i : Fin 64,u.getLsbD i.val=true → p.getLsbD i.val=true) ∧
    (∀i : Fin 64,v.getLsbD i.val=true → n.getLsbD i.val=true) ∧
    (∀i j : Fin 64,u.getLsbD i.val=true → v.getLsbD j.val=true →
      ∀w∈ws,w.getLsbD i.val=w.getLsbD j.val) := by
  induction ws generalizing p n with
  | nil =>
    simp only [groups] at mem
    split at mem
    · contradiction
    next h =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (List.mem_singleton.mp mem)
      exact ⟨fun x => h (Or.inl x),fun x => h (Or.inr x),fun _ x => x,fun _ x => x,by simp⟩
  | cons w ws ih =>
    simp only [groups] at mem
    split at mem
    · contradiction
    rcases List.mem_append.mp mem with pos|neg
    · obtain ⟨un,vn,hp,hn,same⟩:=ih _ _ pos
      simp only [BitVec.getLsbD_and,Bool.and_eq_true] at hp hn
      refine ⟨un,vn,fun i hi => (hp i hi).1,fun i hi => (hn i hi).1,?_⟩
      intro i j hi hj z hz
      rcases List.mem_cons.mp hz with rfl|tail
      · exact (hp i hi).2.trans (hn j hj).2.symm
      · exact same i j hi hj z tail
    · obtain ⟨un,vn,hp,hn,same⟩:=ih _ _ neg
      have pa (i : Fin 64) (hi : u.getLsbD i.val=true) : p.getLsbD i.val=true ∧ w.getLsbD i.val=false := by
        simpa only [BitVec.getLsbD_and,BitVec.getLsbD_not,decide_eq_true i.isLt,Bool.true_and,
          Bool.and_eq_true,Bool.not_eq_true'] using hp i hi
      have na (i : Fin 64) (hi : v.getLsbD i.val=true) : n.getLsbD i.val=true ∧ w.getLsbD i.val=false := by
        simpa only [BitVec.getLsbD_and,BitVec.getLsbD_not,decide_eq_true i.isLt,Bool.true_and,
          Bool.and_eq_true,Bool.not_eq_true'] using hn i hi
      refine ⟨un,vn,fun i hi => (pa i hi).1,fun i hi => (na i hi).1,?_⟩
      intro i j hi hj z hz
      rcases List.mem_cons.mp hz with rfl|tail
      · exact (pa i hi).2.trans (na j hj).2.symm
      · exact same i j hi hj z tail

private def cover (t : Q) (ws : List Q) := (groups ws t (~~~t)).isEmpty
private theorem trail_cover {t : Q} {ws : List Q} {n} (h : Trail t ws.toFinset n) :
    cover t ws=true := by
  apply List.isEmpty_iff.mpr
  apply List.eq_nil_iff_forall_not_mem.mpr
  rintro ⟨u,v⟩ mem
  obtain ⟨un,vn,p,n',agree⟩:=groupFacts _ _ _ mem
  obtain ⟨i,hi⟩:=nonzeroBit un
  obtain ⟨j,hj⟩:=nonzeroBit vn
  have off : t.getLsbD j.val=false := by
    simpa only [BitVec.getLsbD_not,decide_eq_true j.isLt,Bool.true_and,Bool.not_eq_true'] using n' j hj
  have eq:=trail_sep h i.val j.val i.isLt j.isLt (fun w hw => agree i j hi hj w (List.mem_toFinset.mp hw))
  exact Bool.false_ne_true (off.symm.trans (eq.symm.trans (p i hi)))

private def alreadySplit (c u v : Q) :=
  ((u &&& c)==0 && (v &&& c)==v) || ((u &&& c)==u && (v &&& c)==0)
private lemma subsetOn {u c : Q} (on : ∀i : Fin 64,u.getLsbD i.val=true → c.getLsbD i.val=true) : u &&& c=u := by
  apply BitVec.eq_of_getLsbD_eq;intro i hi
  rw [BitVec.getLsbD_and]
  cases e : u.getLsbD i
  · rfl
  · exact on ⟨i,hi⟩ e
private lemma subsetOff {u c : Q} (off : ∀i : Fin 64,u.getLsbD i.val=true → c.getLsbD i.val=false) : u &&& c=0 := by
  apply BitVec.eq_of_getLsbD_eq;intro i hi
  rw [BitVec.getLsbD_and]
  cases e : u.getLsbD i <;> simp [e,off ⟨i,hi⟩]
private lemma finalSplit {c : Q} {ws : List Q} {t k} (h : Trail t (c::ws).toFinset k) :
    ((groups ws t (~~~t)).all fun g => alreadySplit c g.1 g.2)=true := by
  apply List.all_eq_true.mpr
  rintro ⟨u,v⟩ mem
  obtain ⟨un,vn,p,n',agree⟩:=groupFacts _ _ _ mem
  obtain ⟨i,hi⟩:=nonzeroBit un
  obtain ⟨j,hj⟩:=nonzeroBit vn
  have differs (a b : Fin 64) (ha : u.getLsbD a.val=true) (hb : v.getLsbD b.val=true) :
      c.getLsbD a.val≠c.getLsbD b.val := by
    intro eq
    have same := trail_sep h a.val b.val a.isLt b.isLt (by
      intro w hw
      rcases List.mem_cons.mp (List.mem_toFinset.mp hw) with rfl|rest
      · exact eq
      · exact agree a b ha hb w rest)
    have off : t.getLsbD b.val=false := by
      simpa only [BitVec.getLsbD_not,decide_eq_true b.isLt,Bool.true_and,Bool.not_eq_true'] using n' b hb
    exact Bool.false_ne_true (off.symm.trans (same.symm.trans (p a ha)))
  unfold alreadySplit
  apply Bool.or_eq_true_iff.mpr
  cases e : c.getLsbD i.val with
  | false =>
    have right (b : Fin 64) (hb : v.getLsbD b.val=true) : c.getLsbD b.val=true := by
      cases eb : c.getLsbD b.val with
      | true => rfl
      | false => exact (differs i b hi hb (e.trans eb.symm)).elim
    have left (a : Fin 64) (ha : u.getLsbD a.val=true) : c.getLsbD a.val=false :=
      Bool.eq_false_iff.mpr (fun on => differs a j ha hj (on.trans (right j hj).symm))
    exact Or.inl (Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr (subsetOff left),beq_iff_eq.mpr (subsetOn right)⟩)
  | true =>
    have right (b : Fin 64) (hb : v.getLsbD b.val=true) : c.getLsbD b.val=false :=
      Bool.eq_false_iff.mpr (fun on => differs i b hi hb (e.trans on.symm))
    have left (a : Fin 64) (ha : u.getLsbD a.val=true) : c.getLsbD a.val=true := by
      cases ea : c.getLsbD a.val with
      | true => rfl
      | false => exact (differs a j ha hj (ea.trans (right j hj).symm)).elim
    exact Or.inr (Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr (subsetOn left),beq_iff_eq.mpr (subsetOff right)⟩)

private abbrev Hint := Q × ℕ × List Q
private def soundHints (t : Q) (hs : List Hint) := ∀h∈hs,restrictWord h.1 t≠0 ∧
  ¬ construction (restrictWord h.1 t) (h.2.1-1) h.2.2.toFinset
private lemma hintLink {d t child : Q} {b : Nat} {L : List Q} (e : restrictWord d t=child)
    (nz : child≠0) (lower : ¬construction child (b-1) L.toFinset) :
    restrictWord d t≠0 ∧ ¬construction (restrictWord d t) (b-1) L.toFinset := e ▸ And.intro nz lower
private def chooseHints : Nat → List Hint → List Hint
  | _,[] => []
  | m,h::hs => if m=0 then [] else if m.testBit 0 then h::chooseHints (m/2) hs else chooseHints (m/2) hs
private lemma chosenSound {t hs} (h : soundHints t hs) (m) : soundHints t (chooseHints m hs) := by
  suffices sub : ∀ (l : List Hint) (i : Nat),chooseHints i l ⊆ l from fun x hx => h x (sub _ _ hx)
  intro l
  induction l with
  | nil => intro i;simp [chooseHints]
  | cons a tl ih =>
    intro i x hx
    simp only [chooseHints] at hx
    split at hx
    · contradiction
    · split at hx
      · exact (List.mem_cons.mp hx).elim (fun eq => List.mem_cons.mpr (Or.inl eq))
          (fun e => List.mem_cons.mpr (Or.inr (ih _ e)))
      · exact List.mem_cons.mpr (Or.inr (ih _ hx))
private def canGrant (P : Finset Q) (w : Q) := ∃a∈P,∃b∈P,w∈ops a b

private lemma grantGate {P : Finset Q} {t w : Q} {k : Nat} (nz : w≠0)
    (easy : canGrant P w) (next : construction t k (insert w P)) : construction t (k+1) P := by
  by_cases present : w∈P
  · rw [Finset.insert_eq_of_mem present] at next
    exact Or.inl next
  · obtain ⟨a,ha,b,hb,op⟩:=easy
    have ne : a≠b := by
      rintro rfl
      rcases sameOp _ _ op with eq|zero
      · exact present (eq ▸ ha)
      · exact nz zero
    exact Or.inr ⟨a,ha,b,hb,ne,w,op,nz,present,next⟩

private lemma grantAll {P : Finset Q} {t : Q} {k : Nat} (extra : List Q)
    (easy : ∀w∈extra,w≠0 ∧ canGrant P w)
    (run : construction t k (extra.toFinset ∪ P)) : construction t (k+extra.length) P := by
  induction extra generalizing P with
  | nil => simpa only [List.toFinset_nil,Finset.empty_union,List.length_nil,Nat.add_zero] using run
  | cons w xs ih =>
    obtain ⟨nz,make⟩:=easy w (List.mem_cons_self)
    have shifted : construction t k (xs.toFinset ∪ insert w P) := by
      simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert] using run
    have supply : ∀z∈xs,z≠0 ∧ canGrant (insert w P) z := by
      intro z hz
      obtain ⟨non,a,ha,b,hb,op⟩:=easy z (List.mem_cons_of_mem _ hz)
      exact ⟨non,a,Finset.mem_insert_of_mem ha,b,Finset.mem_insert_of_mem hb,op⟩
    have pre:=ih supply shifted
    simpa only [List.length_cons,Nat.add_assoc] using grantGate nz make pre

private def extraSignals (d : Q) (L : List Q) (ws : List Q) :=
  (ws.map (restrictWord d)).filter fun w => w != 0 && !(L.contains w)
private def oneStep (L : List Q) := L.flatMap fun a => L.flatMap fun b => ops a b
private lemma extraSpec {d L ws w} : w∈extraSignals d L ws ↔
    (∃v∈ws,restrictWord d v=w) ∧ w≠0 ∧ w∉L := by
  simp [extraSignals]
private lemma easySpec {L w} (h : w∈oneStep L) : canGrant L.toFinset w := by
  obtain ⟨a,ha,x⟩:=List.mem_flatMap.mp h
  obtain ⟨b,hb,ok⟩:=List.mem_flatMap.mp x
  exact ⟨a,List.mem_toFinset.mpr ha,b,List.mem_toFinset.mpr hb,ok⟩

private def canProject (h : Hint) (k : Nat) (ws : List Q) : Bool :=
  let deadCount := (ws.filter fun w => restrictWord h.1 w == 0).length
  if h.2.1+deadCount≤k then true else
    let extra:=extraSignals h.1 h.2.2 ws
    if h.2.1+deadCount≤k+extra.length then true else
      extra.any fun w => !((oneStep h.2.2).contains w)
private def compatible (hs : List Hint) (t : Q) (k : Nat) (ws : List Q) :=
  cover t ws && hs.all fun h => canProject h k ws

private lemma compatibleSound {hs : List Hint} {t : Q} {ws : List Q} {n}
    (hyp : soundHints t hs) (ok : Trail t ws.toFinset n) (hn : ws.Nodup) : compatible hs t n ws=true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨trail_cover ok,List.all_eq_true.mpr ?_⟩
  rintro ⟨d,b,L⟩ mem
  obtain ⟨non,lb⟩:=hyp _ mem
  change restrictWord d t≠0 at non
  change ¬construction (restrictWord d t) (b-1) L.toFinset at lb
  have eq : (ws.filter fun w => restrictWord d w == 0).toFinset =
      ws.toFinset.filter fun w => restrictWord d w=0 := by ext w;simp only [List.mem_toFinset,List.mem_filter,Finset.mem_filter,beq_iff_eq]
  have card := List.toFinset_card_of_nodup (hn.filter fun w => restrictWord d w == 0)
  rw [eq] at card
  change dead d ws.toFinset=_ at card
  unfold canProject
  dsimp only
  split
  · rfl
  split
  · rfl
  next short =>
    have miss : ∃w∈extraSignals d L ws,w∉oneStep L := by
      by_contra bad
      obtain ⟨enough,make⟩:=projected ok d non
      let extra:=extraSignals d L ws
      have run:=make (extra.toFinset ∪ L.toFinset) (by
        intro v hv nz
        by_cases existsIn : restrictWord d v∈L
        · exact Finset.mem_union_right _ (List.mem_toFinset.mpr existsIn)
        · exact Finset.mem_union_left _ (List.mem_toFinset.mpr
            (extraSpec.mpr ⟨⟨v,List.mem_toFinset.mp hv,rfl⟩,nz,existsIn⟩)))
      have good (w) (hw : w∈extra) : w≠0 ∧ canGrant L.toFinset w := by
        refine ⟨(extraSpec.mp hw).2.1,easySpec ?_⟩
        by_contra absent
        exact bad ⟨w,hw,absent⟩
      have total:=grantAll extra good run
      have budget : n-dead d ws.toFinset+extra.length ≤ b-1 := by dsimp only [extra];omega
      exact lb (constructLift budget total)
    obtain ⟨w,m,absent⟩:=miss
    have off : (oneStep L).contains w=false := Bool.eq_false_iff.mpr (fun h => absent (List.contains_iff_mem.mp h))
    exact List.any_eq_true.mpr ⟨w,m,by rw [off] <;> rfl⟩

private theorem trailNoZero {t s k} (h : Trail t s k) (ht : t≠0) : (0 : Q)∉s := by
  apply trail_ind (P:=fun s _ => (0 : Q)∉s) h
  · intro n
    simpa only [Finset.mem_singleton] using Ne.symm ht
  · intro r a b c k ab fresh nz hc run ih
    intro zero
    rcases Finset.mem_insert.mp zero with ra|rest
    · subst a
      exact (zeroLeft _ _ hc).elim nz (fun eq => fresh (by simp [eq]))
    · rcases Finset.mem_insert.mp rest with rb|inside
      · subst b
        exact (zeroRight _ _ hc).elim nz (fun eq => fresh (by simp [eq]))
      · exact ih (Finset.mem_insert_of_mem inside)

private def pools (ws : List Q) (a b : Q) : List (List Q) :=
  [ws.filter (fun x => x != a && x != b), ws.filter (· != a), ws.filter (· != b), ws]

private def walk (hs : List Hint) (t : Q) : ℕ → List Q → Bool
  | 0, ws => ws.contains t
  | n+1, ws =>
    ws.length ≤ n+2 && compatible hs t (n+1) ws &&
    (ws.contains t || ws.any fun a => ws.any fun b => a < b &&
      (pools ws a b).any fun r => r.length ≤ n &&
        (ops a b).any fun c => !(ws.contains c) && c != 0 && walk hs t n (c :: r))

private theorem pools_find {ws : List Q} {r : Finset Q} {a b : Q}
    (hw : ws.toFinset = insert a (insert b r)) (hn : ws.Nodup) :
    ∃ l ∈ pools ws a b, l.Nodup ∧ l.toFinset = r := by
  have mem (x : Q) : x ∈ ws ↔ x = a ∨ x = b ∨ x ∈ r := by
    rw [← List.mem_toFinset, hw]; simp
  by_cases ha : a ∈ r <;> by_cases hb : b ∈ r
  · exact ⟨ws, by simp [pools], hn, by simpa [ha,hb] using hw⟩
  · refine ⟨ws.filter (· != b), by simp [pools], hn.filter _, ?_⟩
    ext x; simp [mem, ha, hb]; grind
  · refine ⟨ws.filter (· != a), by simp [pools], hn.filter _, ?_⟩
    ext x; simp [mem, ha, hb]; grind
  · refine ⟨ws.filter (fun x => x != a && x != b), by simp [pools], hn.filter _, ?_⟩
    ext x; simp [mem, ha, hb]; grind

private theorem ops_swap {a b c : Q} (h : c ∈ ops a b) : c ∈ ops b a := by
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at *
  rw [BitVec.and_comm a b, BitVec.or_comm a b] at h
  tauto

private theorem walk_pair {hs : List Hint} {a b c : Q} {r : Finset Q} {t : Q} {k : ℕ}
    {ws : List Q} (hab : a < b) (hw : ws.toFinset = insert a (insert b r))
    (hn : ws.Nodup) (fresh : c ∉ insert a (insert b r)) (nz : c ≠ 0) (hc : c ∈ ops a b)
    (hdr : Trail t (insert c r) k)
    (ih : ∀ vs : List Q, vs.toFinset = insert c r → vs.Nodup → walk hs t k vs = true) :
    (ws.any fun a => ws.any fun b => a < b &&
      (pools ws a b).any fun r => r.length ≤ k &&
        (ops a b).any fun c => !(ws.contains c) && c != 0 && walk hs t k (c :: r)) = true := by
  obtain ⟨l, hl, hnl, hfl⟩ := pools_find hw hn
  have ha : a ∈ ws := by rw [← List.mem_toFinset, hw]; simp
  have hb : b ∈ ws := by rw [← List.mem_toFinset, hw]; simp
  have hnws : c ∉ ws := by simpa [← hw] using fresh
  have hnr : c ∉ r := fun h => fresh (by simp [h])
  have hnlc : c ∉ l := by simpa [← hfl] using hnr
  have hsize := trail_card hdr
  rw [Finset.card_insert_of_notMem hnr, ← hfl, List.toFinset_card_of_nodup hnl] at hsize
  apply List.any_eq_true.mpr
  refine ⟨a, ha, List.any_eq_true.mpr ⟨b, hb, ?_⟩⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hab, List.any_eq_true.mpr ⟨l, hl, ?_⟩⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, List.any_eq_true.mpr ⟨c, hc, ?_⟩⟩
  simp [hnws, nz, ih (c :: l) (by simp [hfl]) (List.nodup_cons.mpr ⟨hnlc, hnl⟩)] <;> exact nz

private theorem trail_walk {hs : List Hint} {t s n} (sound : soundHints t hs) (h : Trail t s n) :
    ∀ ws : List Q, ws.toFinset = s → ws.Nodup → walk hs t n ws = true := by
  apply trail_ind (P := fun s n => ∀ ws : List Q, ws.toFinset = s → ws.Nodup → walk hs t n ws = true) h
  · intro k
    intro ws hw hn
    have ht : t ∈ ws := by rw [← List.mem_toFinset, hw]; simp
    cases k with
    | zero => simpa [walk] using ht
    | succ k =>
      have hcv := compatibleSound (t := t) (n := k+1) (ws := ws) sound (hw ▸ Trail.done (t := t) (k+1)) hn
      have hc := List.toFinset_card_of_nodup hn
      rw [hw, Finset.card_singleton] at hc
      simp [walk, ht, hcv, show ws.length ≤ k+2 by omega]
  · intro r a b c k hab fresh nz hc h ih
    intro ws hw hn
    have hall := Trail.step hab fresh nz hc h
    have hcv := compatibleSound (ws := ws) sound (hw ▸ hall) hn
    have hsize := trail_card hall
    rw [← hw, List.toFinset_card_of_nodup hn] at hsize
    simp only [walk, show ws.length ≤ k+2 by omega, decide_true, hcv, Bool.true_and]
    rw [Bool.or_eq_true]
    right
    have hne : a.toNat ≠ b.toNat := fun he => hab (BitVec.eq_of_toNat_eq he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact walk_pair hlt hw hn fresh nz hc h ih
    · rw [Finset.insert_comm] at hw fresh
      exact walk_pair hgt hw hn fresh nz (ops_swap hc) h ih

private def necessaryBasis (t : Q) (raw : List Q) : Bool :=
  raw.sublists.all fun ws => ws == raw || !(cover t ws)

private lemma rejectConstruction {hs : List Hint} {t : Q} {raw : List Q} {k : Nat}
    (sound : soundHints t hs) (nd : raw.Nodup) (allInputs : necessaryBasis t raw=true)
    (reject : walk hs t k raw=false) : ¬construction t k raw.toFinset := by
  intro possible
  obtain ⟨s,sub,trace⟩:=extractConstruction possible
  let ws:=raw.filter (·∈s)
  have setEq : ws.toFinset=s := by ext x;simp [ws];exact fun a => List.mem_toFinset.mp (sub a)
  have works:=trail_walk sound trace ws setEq (nd.filter _)
  have cut := trail_cover (setEq ▸ trace : Trail t ws.toFinset k)
  have h := List.all_eq_true.mp allInputs ws (List.mem_sublists.mpr List.filter_sublist)
  change (ws == raw || !(cover t ws))=true at h
  have same : ws=raw := by simpa only [cut,Bool.not_true,Bool.or_false,beq_iff_eq] using h
  rw [same,reject] at works
  contradiction

private def renameWord (π : Fin 64 → Fin 64) (w : Q) : Q :=
  BitVec.cast (List.length_ofFn) (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 64 => w.getLsbD (π i).val)))
private lemma renameBit (π : Fin 64 → Fin 64) (w : Q) (i : Fin 64) :
    (renameWord π w).getLsbD i.val=w.getLsbD (π i).val := by
  simp only [renameWord,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.getElem_ofFn,Option.getD_some]
private lemma renameTest (π : Fin 64 → Fin 64) (a b : Q)
    (test : ∀ i : Fin 64,a.getLsbD (π i).val=b.getLsbD i.val) : renameWord π a=b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (renameBit π a ⟨j,hj⟩).trans (test ⟨j,hj⟩)
private lemma renameAnd (π : Fin 64 → Fin 64) (a b : Q) :
    renameWord π (a &&& b)=renameWord π a &&& renameWord π b := by
  apply renameTest;intro i
  simp only [BitVec.getLsbD_and,renameBit]
private lemma renameOr (π : Fin 64 → Fin 64) (a b : Q) :
    renameWord π (a ||| b)=renameWord π a ||| renameWord π b := by
  apply renameTest;intro i
  simp only [BitVec.getLsbD_or,renameBit]
private lemma renameNot (π : Fin 64 → Fin 64) (a : Q) :
    renameWord π (~~~a) = ~~~(renameWord π a) := by
  apply renameTest;intro i
  simp only [BitVec.getLsbD_not,decide_eq_true i.isLt,decide_eq_true (π i).isLt,renameBit]
private lemma renameZero (π : Fin 64 → Fin 64) : renameWord π 0=0 := by
  apply renameTest;intro i;simp
private lemma renameAll (π : Fin 64 → Fin 64) : renameWord π (BitVec.allOnes 64)=BitVec.allOnes 64 := by
  apply renameTest;intro i
  simp only [BitVec.getLsbD_allOnes,decide_eq_true i.isLt,decide_eq_true (π i).isLt]
private lemma renameOp (π : Fin 64 → Fin 64) (a b c : Q) (h : c∈ops a b) :
    renameWord π c∈ops (renameWord π a) (renameWord π b) := by
  simp only [ops,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  rcases h with rfl|rfl|rfl|rfl
  · exact Or.inl (renameAnd π a b)
  · exact Or.inr (Or.inl (renameOr π a b))
  · right;right;left;rw [renameAnd,renameNot]
  · right;right;right;rw [renameAnd,renameNot]
private lemma renameInj {π : Fin 64 → Fin 64} (inv : ∀ i,π (π i)=i) : Function.Injective (renameWord π) := by
  intro a b eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin 64 := ⟨i,hi⟩
  have same := congrArg (fun w : Q => w.getLsbD (π j).val) eq
  simp only [renameBit,inv] at same
  exact same
private lemma relabelConstruction (π : Fin 64 → Fin 64) (inv : ∀i,π (π i)=i)
    {t k s} (h : construction t k s) : construction (renameWord π t) k (s.image (renameWord π)) := by
  have inj:=renameInj inv
  induction k generalizing s with
  | zero => exact Finset.mem_image.mpr ⟨t,h,rfl⟩
  | succ k ih =>
    rcases h with short|⟨a,ha,b,hb,ab,c,hc,nz,fresh,ok⟩
    · exact Or.inl (ih short)
    · have next:=ih ok
      rw [Finset.image_insert] at next
      refine Or.inr ⟨_,Finset.mem_image_of_mem _ ha,_,Finset.mem_image_of_mem _ hb,fun eq => ab (inj eq),
        _,renameOp π _ _ _ hc,?_,?_,next⟩
      · exact fun zero => nz (inj (zero.trans (renameZero π).symm))
      · rintro mem
        obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp mem
        exact fresh (inj eq ▸ hv)

private abbrev Bank := List (List Nat)
private def decode (dictionary : Nat → Q) (bits : Nat) : Nat → Nat → List Q
  | 0,_ => []
  | fuel+1,c => if c=0 then [] else
      dictionary ((c % (2^bits))-1) :: decode dictionary bits fuel (c >>> bits)
private def fingerprint (ws : List Q) : Nat := ws.foldl (fun h w =>
  let z:=w.toNat % 2147483647
  (h+z*z+3*z) % 2147483647) 1
private def sameMembers (xs ys : List Q) := xs.all ys.contains && ys.all xs.contains
private lemma sameMembers_eq {xs ys : List Q} (h : sameMembers xs ys=true) : xs.toFinset=ys.toFinset := by
  obtain ⟨left,right⟩:=Bool.and_eq_true_iff.mp h
  ext w
  simp only [List.mem_toFinset]
  exact ⟨fun hx => List.contains_iff_mem.mp (List.all_eq_true.mp left _ hx),
    fun hy => List.contains_iff_mem.mp (List.all_eq_true.mp right _ hy)⟩
private def recorded (D : Nat → Q) (bits buckets : Nat) (bank : Bank) (ws : List Q) : Bool :=
  match bank[(fingerprint ws)%buckets]? with
  | none => false
  | some row => row.any fun key => sameMembers (decode D bits 8 (key >>> 12)) ws

private lemma recordMember {D bits buckets bank ws} (h : recorded D bits buckets bank ws=true) :
    ∃row∈bank,∃key∈row,(decode D bits 8 (key >>> 12)).toFinset=ws.toFinset := by
  unfold recorded at h
  split at h
  · contradiction
  next row eq =>
    obtain ⟨key,inside,agree⟩:=List.any_eq_true.mp h
    exact ⟨row,List.mem_of_getElem? eq,key,inside,sameMembers_eq agree⟩

private def rejectChild (hs : List Hint) (t : Q) (D : Nat → Q) (bits buckets : Nat) (bank : Bank)
    (k : Nat) (ws : List Q) : Bool :=
  if k=0 then !(ws.contains t) else
    !(hs.all fun h => canProject h k ws) || recorded D bits buckets bank ws
private def certified (D : Nat → Q) (bits : Nat) (bank : Bank) (t : Q) (k : Nat) :=
  ∀row∈bank,∀key∈row,¬ Trail t (decode D bits 8 (key >>> 12)).toFinset k
private def checkChildren (t : Q) (k : Nat) (ws : List Q) (reject : List Q → Bool) : Bool :=
  decide ws.Nodup && !(ws.contains t) && ws.all fun a => ws.all fun b =>
    if a<b then (pools ws a b).all fun r =>
      if r.length≤k then
        let remaining:=groups r t (~~~t)
        (ops a b).all fun c => if c∈ws ∨ c=0 then true else !(remaining.all fun g => alreadySplit c g.1 g.2) || reject (c::r)
      else true
    else true

private lemma traceCases {t s n} (h : Trail t s n) :
    s={t} ∨ ∃r a b c k,n=k+1 ∧ s=insert a (insert b r) ∧ a≠b ∧
      c∉s ∧ c≠0 ∧ c∈ops a b ∧ Trail t (insert c r) k := by
  apply trail_ind (P:=fun s n => s={t} ∨ ∃r a b c k,n=k+1 ∧ s=insert a (insert b r) ∧
    a≠b ∧ c∉s ∧ c≠0 ∧ c∈ops a b ∧ Trail t (insert c r) k) h
  · intro k;exact Or.inl rfl
  · intro r a b c k ab newC nz hc run ih
    exact Or.inr ⟨r,a,b,c,k,rfl,rfl,ab,newC,nz,hc,run⟩

private lemma rejectionSound {hs t D bits buckets bank k ws} (sound : soundHints t hs)
    (layer : certified D bits bank t k) (nd : ws.Nodup)
    (passed : rejectChild hs t D bits buckets bank k ws=true) :
    ¬Trail t ws.toFinset k := by
  intro trace
  unfold rejectChild at passed
  split at passed
  next eq =>
    rcases traceCases trace with one|⟨r,a,b,c,j,number,rest⟩
    · have mem : t∈ws := List.mem_toFinset.mp (one ▸ Finset.mem_singleton_self _)
      rw [List.contains_iff_mem.mpr mem] at passed
      exact Bool.false_ne_true passed
    · omega
  next non =>
    have compatibleNow:=(Bool.and_eq_true_iff.mp (compatibleSound sound trace nd)).2
    simp only [compatibleNow,Bool.not_true,Bool.false_or] at passed
    obtain ⟨row,hr,key,hk,eq⟩:=recordMember passed
    exact layer row hr key hk (eq ▸ trace)

private lemma checkedBranch {t k reject ws}
    (all : checkChildren t k ws reject=true)
    (sound : ∀v : List Q,v.Nodup → reject v=true → ¬Trail t v.toFinset k)
    {a b c r} (lt : a<b) (shape : ws.toFinset=insert a (insert b r))
    (fresh : c∉ws.toFinset) (nz : c≠0) (op : c∈ops a b) (child : Trail t (insert c r) k) : False := by
  simp only [checkChildren,Bool.and_eq_true,decide_eq_true_eq] at all
  have nd : ws.Nodup := all.1.1
  obtain ⟨v,hv,ndv,ev⟩:=pools_find shape nd
  have ma : a∈ws := List.mem_toFinset.mp (shape ▸ Finset.mem_insert_self _ _)
  have mb : b∈ws := by rw [←List.mem_toFinset,shape];simp
  have mc : c∉ws := fun yes => fresh (List.mem_toFinset.mpr yes)
  have nr : c∉r := fun yes => fresh (shape ▸ (by simp [yes]))
  have nc : c∉v := fun yes => nr (ev ▸ List.mem_toFinset.mpr yes)
  have length:=trail_card child
  rw [Finset.card_insert_of_notMem nr,←ev,List.toFinset_card_of_nodup ndv] at length
  have h := List.all_eq_true.mp (List.all_eq_true.mp all.2 a ma) b mb
  rw [ite_eq_left lt] at h
  have hr:=List.all_eq_true.mp h v hv
  rw [ite_eq_left (show v.length≤k by omega)] at hr
  have hc:=List.all_eq_true.mp hr c op
  rw [ite_eq_right (show ¬(c∈ws ∨ c=0) from fun x => x.elim mc nz)] at hc
  have liveC : Trail t (c::v).toFinset k := by simpa only [List.toFinset_cons,ev] using child
  simp only [finalSplit liveC,Bool.not_true,Bool.false_or] at hc
  exact sound (c::v) (List.nodup_cons.mpr ⟨nc,ndv⟩) hc (by simpa only [List.toFinset_cons,ev] using child)

private lemma checkedSound {t k ws reject} (all : checkChildren t k ws reject=true)
    (sound : ∀v : List Q,v.Nodup → reject v=true → ¬Trail t v.toFinset k) :
    ¬Trail t ws.toFinset (k+1) := by
  intro h
  rcases traceCases h with one|⟨r,a,b,c,j,idx,eq,ne,fresh,nz,op,child⟩
  · have mem : t∈ws := List.mem_toFinset.mp (one ▸ Finset.mem_singleton_self _)
    have off := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp all).1).2
    rw [List.contains_iff_mem.mpr mem] at off
    exact Bool.false_ne_true off
  · obtain rfl : k=j := by omega
    have neval : a.toNat≠b.toNat := fun e => ne (BitVec.eq_of_toNat_eq e)
    rcases lt_or_gt_of_ne neval with lt|gt
    · exact checkedBranch all sound lt eq fresh nz op child
    · rw [Finset.insert_comm] at eq
      exact checkedBranch all sound gt eq fresh nz (ops_swap op) child

private def layerTest (D : Nat → Q) (advice : Array Nat) (bits buckets k : Nat) (next : Bank) (hs : List Hint)
    (t : Q) (row : List Nat) : Bool :=
  row.all fun key => checkChildren t k (decode D bits 8 (key >>> 12))
    (rejectChild (chooseHints (advice[Nat.mod key 4096]?.getD 0) hs) t D bits buckets next k)
private lemma layerSound {D advice bits buckets k next hs t cur}
    (sound : soundHints t hs) (prev : certified D bits next t k)
    (ok : cur.all (layerTest D advice bits buckets k next hs t)=true) : certified D bits cur t (k+1) := by
  intro row hr key hk
  have good:=List.all_eq_true.mp (List.all_eq_true.mp ok row hr) key hk
  exact checkedSound good (fun v nd h => rejectionSound (chosenSound sound _) prev nd h)

private lemma basisRefute {hs : List Hint} {t : Q} {raw : List Q} {k : Nat}
    (sound : soundHints t hs) (nd : raw.Nodup) (needed : necessaryBasis t raw=true)
    (ruled : raw.length>k+1 ∨ compatible hs t k raw=false ∨ ¬Trail t raw.toFinset k) :
    ¬construction t k raw.toFinset := by
  intro h
  obtain ⟨s,sub,trace⟩:=extractConstruction h
  let ws:=raw.filter (·∈s)
  have setEq : ws.toFinset=s := by ext x;simp [ws];exact fun a => List.mem_toFinset.mp (sub a)
  have cut:=trail_cover (setEq ▸ trace : Trail t ws.toFinset k)
  have hit:=List.all_eq_true.mp needed ws (List.mem_sublists.mpr List.filter_sublist)
  change (ws == raw || !(cover t ws))=true at hit
  have same : ws=raw := by simpa only [cut,Bool.not_true,Bool.or_false,beq_iff_eq] using hit
  rw [same] at setEq
  have full : Trail t raw.toFinset k := setEq ▸ trace
  rcases ruled with size|no|no
  · have bound:=trail_card full
    rw [List.toFinset_card_of_nodup nd] at bound
    omega
  · exact Bool.false_ne_true (no.symm.trans (compatibleSound sound full nd))
  · exact no full

private def binaryWord (op : Nat) (a b : Q) : Q :=
  if op=0 then a &&& b else if op=1 then a ||| b else a &&& ~~~b
private lemma renameBinary (π : Fin 64 → Fin 64) (op : Nat) (a b : Q) :
    renameWord π (binaryWord op a b)=binaryWord op (renameWord π a) (renameWord π b) := by
  unfold binaryWord
  split
  · exact renameAnd _ _ _
  · split
    · exact renameOr _ _ _
    · rw [renameAnd,renameNot]

private lemma renameTrace {t s k} (h : Trail t s k) (π : Fin 64 → Fin 64) (inv : ∀i,π (π i)=i) :
    Trail (renameWord π t) (s.image (renameWord π)) k := by
  have inj:=renameInj inv
  apply trail_ind (P:=fun s n => Trail (renameWord π t) (s.image (renameWord π)) n) h
  · intro n
    rw [Finset.image_singleton];exact Trail.done _
  · intro r a b c n ne fresh nz op child ih
    simp only [Finset.image_insert] at ih ⊢
    apply Trail.step (fun eq => ne (inj eq)) _ (fun e => nz (inj (e.trans (renameZero π).symm))) (renameOp π _ _ _ op) ih
    intro mem
    have m : renameWord π c∈(insert a (insert b r)).image (renameWord π) := by
      simpa only [Finset.image_insert] using mem
    obtain ⟨x,hx,e⟩:=Finset.mem_image.mp m
    exact fresh (inj e ▸ hx)

private def firstOperand (bits code : Nat) := Nat.mod (code >>> bits) (2^bits)
private def secondOperand (bits code : Nat) := Nat.mod code (2^bits)
private def recipeTest (D : Nat → Q) (bits n : Nat) (plan : Array Nat) :=
  (List.range plan.size).all fun j =>
    let code:=plan[j]?.getD 0
    let a:=firstOperand bits code
    let b:=secondOperand bits code
    decide (a<n+j) && decide (b<n+j) &&
    (D (n+j) == binaryWord (code >>> (2*bits)) (D a) (D b))
private lemma recipeTransfer (D E : Nat → Q) (π : Fin 64 → Fin 64) (bits n : Nat) (plan : Array Nat)
    (left : recipeTest D bits n plan=true) (right : recipeTest E bits n plan=true)
    (initial : ∀i<n,renameWord π (D i)=E i) :
    ∀i<n+plan.size,renameWord π (D i)=E i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro valid
    by_cases input : i<n
    · exact initial i input
    · let j:=i-n
      have hj : j<plan.size := by dsimp [j];omega
      have eq : n+j=i := by dsimp [j];omega
      let code:=plan[j]?.getD 0
      have a:=List.all_eq_true.mp left j (List.mem_range.mpr hj)
      have b:=List.all_eq_true.mp right j (List.mem_range.mpr hj)
      simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at a b
      rw [eq] at a b
      rw [a.2,b.2,renameBinary,ih _ a.1.1 (by omega),ih _ a.1.2 (by omega)]

private def mappedIndex (perms : Array (Array Nat)) (N g i : Nat) :=
  if i<N then ((perms[g]?.getD #[])[i]?.getD N) else N
private def idsOf (bits : Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | k+1,c => if c=0 then [] else ((c % (2^bits))-1)::idsOf bits k (c >>> bits)
private lemma decodeIds (D : Nat → Q) (bits k c : Nat) : decode D bits k c=(idsOf bits k c).map D := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih => by_cases eq : c=0 <;> simp only [decode,idsOf,eq,ite_true,ite_false,List.map_nil,List.map_cons,ih]
private def rowAction (D : Nat → Q) (t : Q) (g : Nat → Nat) :=
  ∀xs : List Nat,∀k,Trail t (xs.map D).toFinset k → Trail t ((xs.map g).map D).toFinset k
private lemma actionByRename (D : Nat → Q) (π : Fin 64 → Fin 64) (g : Nat → Nat) (t : Q)
    (inv : ∀i,π (π i)=i) (stable : renameWord π t=t) (correct : ∀i,renameWord π (D i)=D (g i)) :
    rowAction D t g := by
  intro xs k h
  have moved:=renameTrace h π inv
  rw [stable] at moved
  have eq : (xs.map D).toFinset.image (renameWord π)=((xs.map g).map D).toFinset := by
    ext w
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨y,⟨i,hi,rfl⟩,e⟩
      exact ⟨g i,⟨i,hi,rfl⟩,(correct i).symm.trans e⟩
    · rintro ⟨y,⟨i,hi,rfl⟩,e⟩
      exact ⟨D i,⟨i,hi,rfl⟩,(correct i).trans e⟩
  exact eq ▸ moved
private def moveIds (perms : Array (Array Nat)) (N : Nat) (xs : List Nat) (path : List Nat) : List Nat :=
  path.foldl (fun ids g => ids.map (mappedIndex perms N g)) xs
private lemma movedTrace (D : Nat → Q) (t : Q) (perms : Array (Array Nat)) (N : Nat)
    (rule : ∀g<perms.size,rowAction D t (mappedIndex perms N g)) (ids path : List Nat)
    (valid : ∀g∈path,g<perms.size) {k} (h : Trail t (ids.map D).toFinset k) :
    Trail t ((moveIds perms N ids path).map D).toFinset k := by
  induction path generalizing ids with
  | nil => exact h
  | cons g rest ih =>
    exact ih _ (fun j hj => valid j (by simp [hj])) (rule g (valid g (by simp)) ids k h)

private def orbitRow (D : Nat → Q) (bits buckets N : Nat) (reps : Bank)
    (perms : Array (Array Nat)) (paths : Array (List Nat)) (row : List Nat) : Bool :=
  row.all fun key =>
    match paths[Nat.mod key 4096]? with
    | none => false
    | some path =>
      path.all (fun g => decide (g<perms.size)) &&
        recorded D bits buckets reps ((moveIds perms N (idsOf bits 8 (key >>> 12)) path).map D)
private lemma orbitSafe {D bits buckets N reps perms paths bank t k}
    (rule : ∀g<perms.size,rowAction D t (mappedIndex perms N g))
    (known : certified D bits reps t k)
    (covers : bank.all (orbitRow D bits buckets N reps perms paths)=true) :
    certified D bits bank t k := by
  intro row hr key hk trace
  have ok:=List.all_eq_true.mp (List.all_eq_true.mp covers row hr) key hk
  change (match paths[Nat.mod key 4096]? with
    | none => false
    | some path => path.all (fun g => decide (g<perms.size)) &&
        recorded D bits buckets reps ((moveIds perms N (idsOf bits 8 (key >>> 12)) path).map D))=true at ok
  split at ok
  · contradiction
  next path _ =>
    obtain ⟨within,present⟩:=Bool.and_eq_true_iff.mp ok
    obtain ⟨row',hr',key',hk',eq⟩:=recordMember present
    rw [decodeIds] at trace
    have h:=movedTrace D t perms N rule _ path (fun g hg => of_decide_eq_true (List.all_eq_true.mp within _ hg)) trace
    exact known row' hr' key' hk' (eq ▸ h)

private def raw0 : Q := 0x889622a95b6008a
private def raw1 : Q := 0x11124453295c842c
private def raw2 : Q := 0x2223889c4e660130
private def raw3 : Q := 0x443c10e0707829c0
private def raw4 : Q := 0x87c01f007f800e00
private def raw5 : Q := 0xf8001fff80013000
private def raw6 : Q := 0xffffe0000001c000
private def target : Q := 0xfffffffffffe0000
private def expandWord (packed : Nat) : Q := BitVec.ofNat 64 packed
private lemma emptyBank {D bits t k} : certified D bits [] t k := by intro row h;simp at h
private def reindex0 : Array Nat := #[0,4,2,5,1,3,6,8,7,9,10,11,12,13,14,15,16,17,18,19,22,21,20,25,27,23,26,24,30,29,28,34,32,36,31,35,33,39,38,37,40,43,42,41,44,47,49,45,48,46,50,53,52,51,54,57,56,55,58,61,60,59,62,63]
private def pi0 (i : Fin 64) : Fin 64 :=
  ⟨Nat.mod (reindex0[i.val]?.getD 0) 64,Nat.mod_lt _ (by decide)⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem inv0 : ∀i,pi0 (pi0 i)=i := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv0_raw0 : renameWord pi0 raw0=raw2 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv0_raw1 : renameWord pi0 raw1=raw1 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv0_raw2 : renameWord pi0 raw2=raw0 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv0_raw3 : renameWord pi0 raw3=raw3 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv0_raw4 : renameWord pi0 raw4=raw4 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv0_raw5 : renameWord pi0 raw5=raw5 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv0_raw6 : renameWord pi0 raw6=raw6 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv0_target : renameWord pi0 target=target := renameTest _ _ _ (by decide +kernel)
private def reindex2 : Array Nat := #[0,1,6,7,4,8,2,3,5,9,11,10,14,15,12,13,16,17,21,19,20,18,22,23,28,25,26,30,24,29,27,45,50,51,47,48,53,46,52,49,54,55,58,57,56,31,37,34,35,39,32,33,38,36,40,41,44,43,42,59,62,61,60,63]
private def pi2 (i : Fin 64) : Fin 64 :=
  ⟨Nat.mod (reindex2[i.val]?.getD 0) 64,Nat.mod_lt _ (by decide)⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem inv2 : ∀i,pi2 (pi2 i)=i := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv2_raw0 : renameWord pi2 raw0=raw0 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv2_raw1 : renameWord pi2 raw1=raw3 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv2_raw2 : renameWord pi2 raw2=raw2 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv2_raw3 : renameWord pi2 raw3=raw1 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv2_raw4 : renameWord pi2 raw4=raw4 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv2_raw5 : renameWord pi2 raw5=raw6 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv2_raw6 : renameWord pi2 raw6=raw5 := renameTest _ _ _ (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem mv2_target : renameWord pi2 target=target := renameTest _ _ _ (by decide +kernel)
private def domain5 : Q := ~~~(raw1 ||| raw3 ||| raw4 ||| raw5 ||| raw6)
private def goal5 : Q := restrictWord domain5 target
private def sources5 : List Q := [restrictWord domain5 raw0,restrictWord domain5 raw2]
private def hints5 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound5 : soundHints goal5 hints5 := by
  simp [soundHints,hints5]
private theorem lower5 : ¬construction goal5 0 sources5.toFinset := by
  apply basisRefute sound5 (by decide +kernel) (by decide +kernel)
  exact Or.inl (by decide)
private def domain10 : Q := ~~~(raw0 ||| raw2 ||| raw4 ||| raw5 ||| raw6)
private def goal10 : Q := restrictWord domain10 target
private def sources10 : List Q := [restrictWord domain10 raw1,restrictWord domain10 raw3]
private def hints10 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound10 : soundHints goal10 hints10 := by
  simp [soundHints,hints10]
private theorem lower10 : ¬construction goal10 0 sources10.toFinset := by
  apply basisRefute sound10 (by decide +kernel) (by decide +kernel)
  exact Or.inl (by decide)
private def domain33 : Q := ~~~(raw1 ||| raw2 ||| raw3 ||| raw4 ||| raw6)
private def goal33 : Q := restrictWord domain33 target
private def sources33 : List Q := [restrictWord domain33 raw0,restrictWord domain33 raw5]
private def hints33 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound33 : soundHints goal33 hints33 := by
  simp [soundHints,hints33]
private theorem lower33 : ¬construction goal33 0 sources33.toFinset := by
  apply basisRefute sound33 (by decide +kernel) (by decide +kernel)
  exact Or.inl (by decide)
private def domain36 : Q := ~~~(raw0 ||| raw1 ||| raw3 ||| raw4 ||| raw6)
private def goal36 : Q := restrictWord domain36 target
private def sources36 : List Q := [restrictWord domain36 raw2,restrictWord domain36 raw5]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower36 : ¬construction goal36 0 sources36.toFinset := by
  intro h;have tr:=relabelConstruction pi0 inv0 h
  have dom : renameWord pi0 domain36=domain33 := by
    simp only [domain36,domain33,renameNot,renameOr,mv0_raw0,mv0_raw1,mv0_raw3,mv0_raw4,mv0_raw6] <;> rfl
  have fg : renameWord pi0 goal36=goal33 := by simp only [goal36,goal33,restrictWord,renameAnd,mv0_target,dom]
  have fs : sources36.toFinset.image (renameWord pi0)=sources33.toFinset := by
    simp only [sources36,sources33,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv0_raw2,mv0_raw5] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower33 tr
private def domain65 : Q := ~~~(raw1 ||| raw2 ||| raw3 ||| raw4 ||| raw5)
private def goal65 : Q := restrictWord domain65 target
private def sources65 : List Q := [restrictWord domain65 raw0,restrictWord domain65 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower65 : ¬construction goal65 0 sources65.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain65=domain33 := by
    simp only [domain65,domain33,renameNot,renameOr,mv2_raw1,mv2_raw2,mv2_raw3,mv2_raw4,mv2_raw5] <;> rfl
  have fg : renameWord pi2 goal65=goal33 := by simp only [goal65,goal33,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources65.toFinset.image (renameWord pi2)=sources33.toFinset := by
    simp only [sources65,sources33,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw0,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower33 tr
private def domain68 : Q := ~~~(raw0 ||| raw1 ||| raw3 ||| raw4 ||| raw5)
private def goal68 : Q := restrictWord domain68 target
private def sources68 : List Q := [restrictWord domain68 raw2,restrictWord domain68 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower68 : ¬construction goal68 0 sources68.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain68=domain36 := by
    simp only [domain68,domain36,renameNot,renameOr,mv2_raw0,mv2_raw1,mv2_raw3,mv2_raw4,mv2_raw5] <;> rfl
  have fg : renameWord pi2 goal68=goal36 := by simp only [goal68,goal36,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources68.toFinset.image (renameWord pi2)=sources36.toFinset := by
    simp only [sources68,sources36,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw2,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower36 tr
private def domain34 : Q := ~~~(raw0 ||| raw2 ||| raw3 ||| raw4 ||| raw6)
private def goal34 : Q := restrictWord domain34 target
private def sources34 : List Q := [restrictWord domain34 raw1,restrictWord domain34 raw5]
private def hints34 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound34 : soundHints goal34 hints34 := by
  simp [soundHints,hints34]
private theorem lower34 : ¬construction goal34 0 sources34.toFinset := by
  apply basisRefute sound34 (by decide +kernel) (by decide +kernel)
  exact Or.inl (by decide)
private def domain72 : Q := ~~~(raw0 ||| raw1 ||| raw2 ||| raw4 ||| raw5)
private def goal72 : Q := restrictWord domain72 target
private def sources72 : List Q := [restrictWord domain72 raw3,restrictWord domain72 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower72 : ¬construction goal72 0 sources72.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain72=domain34 := by
    simp only [domain72,domain34,renameNot,renameOr,mv2_raw0,mv2_raw1,mv2_raw2,mv2_raw4,mv2_raw5] <;> rfl
  have fg : renameWord pi2 goal72=goal34 := by simp only [goal72,goal34,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources72.toFinset.image (renameWord pi2)=sources34.toFinset := by
    simp only [sources72,sources34,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw3,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower34 tr
private def domain35 : Q := ~~~(raw2 ||| raw3 ||| raw4 ||| raw6)
private def goal35 : Q := restrictWord domain35 target
private def sources35 : List Q := [restrictWord domain35 raw0,restrictWord domain35 raw1,restrictWord domain35 raw5]
private def hints35 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound35 : soundHints goal35 hints35 := by
  simp [soundHints,hints35]
private theorem lower35 : ¬construction goal35 1 sources35.toFinset := by
  apply basisRefute sound35 (by decide +kernel) (by decide +kernel)
  exact Or.inl (by decide)
private def domain38 : Q := ~~~(raw0 ||| raw3 ||| raw4 ||| raw6)
private def goal38 : Q := restrictWord domain38 target
private def sources38 : List Q := [restrictWord domain38 raw1,restrictWord domain38 raw2,restrictWord domain38 raw5]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower38 : ¬construction goal38 1 sources38.toFinset := by
  intro h;have tr:=relabelConstruction pi0 inv0 h
  have dom : renameWord pi0 domain38=domain35 := by
    simp only [domain38,domain35,renameNot,renameOr,mv0_raw0,mv0_raw3,mv0_raw4,mv0_raw6] <;> rfl
  have fg : renameWord pi0 goal38=goal35 := by simp only [goal38,goal35,restrictWord,renameAnd,mv0_target,dom]
  have fs : sources38.toFinset.image (renameWord pi0)=sources35.toFinset := by
    simp only [sources38,sources35,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv0_raw1,mv0_raw2,mv0_raw5] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower35 tr
private def domain73 : Q := ~~~(raw1 ||| raw2 ||| raw4 ||| raw5)
private def goal73 : Q := restrictWord domain73 target
private def sources73 : List Q := [restrictWord domain73 raw0,restrictWord domain73 raw3,restrictWord domain73 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower73 : ¬construction goal73 1 sources73.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain73=domain35 := by
    simp only [domain73,domain35,renameNot,renameOr,mv2_raw1,mv2_raw2,mv2_raw4,mv2_raw5] <;> rfl
  have fg : renameWord pi2 goal73=goal35 := by simp only [goal73,goal35,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources73.toFinset.image (renameWord pi2)=sources35.toFinset := by
    simp only [sources73,sources35,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw0,mv2_raw3,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower35 tr
private def domain76 : Q := ~~~(raw0 ||| raw1 ||| raw4 ||| raw5)
private def goal76 : Q := restrictWord domain76 target
private def sources76 : List Q := [restrictWord domain76 raw2,restrictWord domain76 raw3,restrictWord domain76 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower76 : ¬construction goal76 1 sources76.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain76=domain38 := by
    simp only [domain76,domain38,renameNot,renameOr,mv2_raw0,mv2_raw1,mv2_raw4,mv2_raw5] <;> rfl
  have fg : renameWord pi2 goal76=goal38 := by simp only [goal76,goal38,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources76.toFinset.image (renameWord pi2)=sources38.toFinset := by
    simp only [sources76,sources38,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw2,mv2_raw3,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower38 tr
private def domain37 : Q := ~~~(raw1 ||| raw3 ||| raw4 ||| raw6)
private def goal37 : Q := restrictWord domain37 target
private def sources37 : List Q := [restrictWord domain37 raw0,restrictWord domain37 raw2,restrictWord domain37 raw5]
private def hints37 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound37 : soundHints goal37 hints37 := by
  simp [soundHints,hints37]
private def packed37 : Array Nat := #[]
private def dict37 (i : Nat) : Q := expandWord (packed37[i]?.getD 0)
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem root37 : checkChildren goal37 2 sources37 (rejectChild (chooseHints 0x0 hints37) goal37 dict37 1 1 ([] : Bank) 2)=true := by decide +kernel
private theorem lower37 : ¬construction goal37 3 sources37.toFinset := by
  apply basisRefute sound37 (by decide +kernel) (by decide +kernel)
  exact Or.inr (Or.inr (checkedSound root37 (fun w nd h => rejectionSound (chosenSound sound37 _) emptyBank nd h)))
private def domain69 : Q := ~~~(raw1 ||| raw3 ||| raw4 ||| raw5)
private def goal69 : Q := restrictWord domain69 target
private def sources69 : List Q := [restrictWord domain69 raw0,restrictWord domain69 raw2,restrictWord domain69 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower69 : ¬construction goal69 3 sources69.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain69=domain37 := by
    simp only [domain69,domain37,renameNot,renameOr,mv2_raw1,mv2_raw3,mv2_raw4,mv2_raw5] <;> rfl
  have fg : renameWord pi2 goal69=goal37 := by simp only [goal69,goal37,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources69.toFinset.image (renameWord pi2)=sources37.toFinset := by
    simp only [sources69,sources37,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw0,mv2_raw2,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower37 tr
private def domain42 : Q := ~~~(raw0 ||| raw2 ||| raw4 ||| raw6)
private def goal42 : Q := restrictWord domain42 target
private def sources42 : List Q := [restrictWord domain42 raw1,restrictWord domain42 raw3,restrictWord domain42 raw5]
private def hints42 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound42 : soundHints goal42 hints42 := by
  simp [soundHints,hints42]
private theorem lower42 : ¬construction goal42 1 sources42.toFinset := by
  apply basisRefute sound42 (by decide +kernel) (by decide +kernel)
  exact Or.inl (by decide)
private def domain74 : Q := ~~~(raw0 ||| raw2 ||| raw4 ||| raw5)
private def goal74 : Q := restrictWord domain74 target
private def sources74 : List Q := [restrictWord domain74 raw1,restrictWord domain74 raw3,restrictWord domain74 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower74 : ¬construction goal74 1 sources74.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain74=domain42 := by
    simp only [domain74,domain42,renameNot,renameOr,mv2_raw0,mv2_raw2,mv2_raw4,mv2_raw5] <;> rfl
  have fg : renameWord pi2 goal74=goal42 := by simp only [goal74,goal42,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources74.toFinset.image (renameWord pi2)=sources42.toFinset := by
    simp only [sources74,sources42,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw1,mv2_raw3,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower42 tr
private def domain97 : Q := ~~~(raw1 ||| raw2 ||| raw3 ||| raw4)
private def goal97 : Q := restrictWord domain97 target
private def sources97 : List Q := [restrictWord domain97 raw0,restrictWord domain97 raw5,restrictWord domain97 raw6]
private def hints97 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound97 : soundHints goal97 hints97 := by
  simp [soundHints,hints97]
private theorem lower97 : ¬construction goal97 1 sources97.toFinset := by
  apply basisRefute sound97 (by decide +kernel) (by decide +kernel)
  exact Or.inl (by decide)
private def domain100 : Q := ~~~(raw0 ||| raw1 ||| raw3 ||| raw4)
private def goal100 : Q := restrictWord domain100 target
private def sources100 : List Q := [restrictWord domain100 raw2,restrictWord domain100 raw5,restrictWord domain100 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower100 : ¬construction goal100 1 sources100.toFinset := by
  intro h;have tr:=relabelConstruction pi0 inv0 h
  have dom : renameWord pi0 domain100=domain97 := by
    simp only [domain100,domain97,renameNot,renameOr,mv0_raw0,mv0_raw1,mv0_raw3,mv0_raw4] <;> rfl
  have fg : renameWord pi0 goal100=goal97 := by simp only [goal100,goal97,restrictWord,renameAnd,mv0_target,dom]
  have fs : sources100.toFinset.image (renameWord pi0)=sources97.toFinset := by
    simp only [sources100,sources97,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv0_raw2,mv0_raw5,mv0_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower97 tr
private def domain15 : Q := ~~~(raw4 ||| raw5 ||| raw6)
private def goal15 : Q := restrictWord domain15 target
private def sources15 : List Q := [restrictWord domain15 raw0,restrictWord domain15 raw1,restrictWord domain15 raw2,restrictWord domain15 raw3]
private def hints15 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound15 : soundHints goal15 hints15 := by
  simp [soundHints,hints15]
private theorem lower15 : ¬construction goal15 2 sources15.toFinset := by
  apply basisRefute sound15 (by decide +kernel) (by decide +kernel)
  exact Or.inl (by decide)
private def domain39 : Q := ~~~(raw3 ||| raw4 ||| raw6)
private def goal39 : Q := restrictWord domain39 target
private def sources39 : List Q := [restrictWord domain39 raw0,restrictWord domain39 raw1,restrictWord domain39 raw2,restrictWord domain39 raw5]
private def hints39 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound39 : soundHints goal39 hints39 := by
  simp [soundHints,hints39]
private def tips39 : Array Nat := #[0x0]
private def packed39 : Array Nat := #[0x30000000c,0xa8006000a,0xb8006000e,0xc80001000,0x1100000024,0x1300000000,0x1b8006000a,0x1b8006002e,0x1c00060030,0x1d00060034,0x1f00060030,0x1f0006003c,0x1f80001000]
private def dict39 (i : Nat) : Q := expandWord (packed39[i]?.getD 0)
private def a39_2_0 : Bank := [[0xd93000,0xd97000,0xda2000,0xdb2000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem z39_2_0 : a39_2_0.all (layerTest dict39 tips39 4 1 1 ([] : Bank) hints39 goal39) = true := by decide +kernel
private def bank39_2 : Bank := a39_2_0
private theorem ok39_2 : certified dict39 4 bank39_2 goal39 2 := by
  apply layerSound (advice:=tips39) (buckets:=1) sound39 emptyBank
  simp only [bank39_2,List.all_append,z39_2_0,Bool.and_self]
private def a39_3_0 : Bank := [[],[0xd921000,0xd942000,0xd952000,0xd962000,0xd982000,0xdc92000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem z39_3_0 : a39_3_0.all (layerTest dict39 tips39 4 1 2 bank39_2 hints39 goal39) = true := by decide +kernel
private def bank39_3 : Bank := a39_3_0
private theorem ok39_3 : certified dict39 4 bank39_3 goal39 3 := by
  apply layerSound (advice:=tips39) (buckets:=1) sound39 ok39_2
  simp only [bank39_3,List.all_append,z39_3_0,Bool.and_self]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem root39 : checkChildren goal39 3 sources39 (rejectChild (chooseHints 0x0 hints39) goal39 dict39 4 2 bank39_3 3)=true := by decide +kernel
private theorem lower39 : ¬construction goal39 4 sources39.toFinset := by
  apply basisRefute sound39 (by decide +kernel) (by decide +kernel)
  exact Or.inr (Or.inr (checkedSound root39 (fun w nd h => rejectionSound (chosenSound sound39 _) ok39_3 nd h)))
private def domain77 : Q := ~~~(raw1 ||| raw4 ||| raw5)
private def goal77 : Q := restrictWord domain77 target
private def sources77 : List Q := [restrictWord domain77 raw0,restrictWord domain77 raw2,restrictWord domain77 raw3,restrictWord domain77 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower77 : ¬construction goal77 4 sources77.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain77=domain39 := by
    simp only [domain77,domain39,renameNot,renameOr,mv2_raw1,mv2_raw4,mv2_raw5] <;> rfl
  have fg : renameWord pi2 goal77=goal39 := by simp only [goal77,goal39,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources77.toFinset.image (renameWord pi2)=sources39.toFinset := by
    simp only [sources77,sources39,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw0,mv2_raw2,mv2_raw3,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower39 tr
private def domain43 : Q := ~~~(raw2 ||| raw4 ||| raw6)
private def goal43 : Q := restrictWord domain43 target
private def sources43 : List Q := [restrictWord domain43 raw0,restrictWord domain43 raw1,restrictWord domain43 raw3,restrictWord domain43 raw5]
private def hints43 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound43 : soundHints goal43 hints43 := by
  simp [soundHints,hints43]
private def packed43 : Array Nat := #[]
private def dict43 (i : Nat) : Q := expandWord (packed43[i]?.getD 0)
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem root43 : checkChildren goal43 2 sources43 (rejectChild (chooseHints 0x0 hints43) goal43 dict43 1 1 ([] : Bank) 2)=true := by decide +kernel
private theorem lower43 : ¬construction goal43 3 sources43.toFinset := by
  apply basisRefute sound43 (by decide +kernel) (by decide +kernel)
  exact Or.inr (Or.inr (checkedSound root43 (fun w nd h => rejectionSound (chosenSound sound43 _) emptyBank nd h)))
private def domain46 : Q := ~~~(raw0 ||| raw4 ||| raw6)
private def goal46 : Q := restrictWord domain46 target
private def sources46 : List Q := [restrictWord domain46 raw1,restrictWord domain46 raw2,restrictWord domain46 raw3,restrictWord domain46 raw5]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower46 : ¬construction goal46 3 sources46.toFinset := by
  intro h;have tr:=relabelConstruction pi0 inv0 h
  have dom : renameWord pi0 domain46=domain43 := by
    simp only [domain46,domain43,renameNot,renameOr,mv0_raw0,mv0_raw4,mv0_raw6] <;> rfl
  have fg : renameWord pi0 goal46=goal43 := by simp only [goal46,goal43,restrictWord,renameAnd,mv0_target,dom]
  have fs : sources46.toFinset.image (renameWord pi0)=sources43.toFinset := by
    simp only [sources46,sources43,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv0_raw1,mv0_raw2,mv0_raw3,mv0_raw5] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower43 tr
private def domain75 : Q := ~~~(raw2 ||| raw4 ||| raw5)
private def goal75 : Q := restrictWord domain75 target
private def sources75 : List Q := [restrictWord domain75 raw0,restrictWord domain75 raw1,restrictWord domain75 raw3,restrictWord domain75 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower75 : ¬construction goal75 3 sources75.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain75=domain43 := by
    simp only [domain75,domain43,renameNot,renameOr,mv2_raw2,mv2_raw4,mv2_raw5] <;> rfl
  have fg : renameWord pi2 goal75=goal43 := by simp only [goal75,goal43,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources75.toFinset.image (renameWord pi2)=sources43.toFinset := by
    simp only [sources75,sources43,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw0,mv2_raw1,mv2_raw3,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower43 tr
private def domain78 : Q := ~~~(raw0 ||| raw4 ||| raw5)
private def goal78 : Q := restrictWord domain78 target
private def sources78 : List Q := [restrictWord domain78 raw1,restrictWord domain78 raw2,restrictWord domain78 raw3,restrictWord domain78 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower78 : ¬construction goal78 3 sources78.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain78=domain46 := by
    simp only [domain78,domain46,renameNot,renameOr,mv2_raw0,mv2_raw4,mv2_raw5] <;> rfl
  have fg : renameWord pi2 goal78=goal46 := by simp only [goal78,goal46,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources78.toFinset.image (renameWord pi2)=sources46.toFinset := by
    simp only [sources78,sources46,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw1,mv2_raw2,mv2_raw3,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower46 tr
private def domain99 : Q := ~~~(raw2 ||| raw3 ||| raw4)
private def goal99 : Q := restrictWord domain99 target
private def sources99 : List Q := [restrictWord domain99 raw0,restrictWord domain99 raw1,restrictWord domain99 raw5,restrictWord domain99 raw6]
private def hints99 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound99 : soundHints goal99 hints99 := by
  simp [soundHints,hints99]
private def packed99 : Array Nat := #[]
private def dict99 (i : Nat) : Q := expandWord (packed99[i]?.getD 0)
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem root99 : checkChildren goal99 2 sources99 (rejectChild (chooseHints 0x0 hints99) goal99 dict99 1 1 ([] : Bank) 2)=true := by decide +kernel
private theorem lower99 : ¬construction goal99 3 sources99.toFinset := by
  apply basisRefute sound99 (by decide +kernel) (by decide +kernel)
  exact Or.inr (Or.inr (checkedSound root99 (fun w nd h => rejectionSound (chosenSound sound99 _) emptyBank nd h)))
private def domain102 : Q := ~~~(raw0 ||| raw3 ||| raw4)
private def goal102 : Q := restrictWord domain102 target
private def sources102 : List Q := [restrictWord domain102 raw1,restrictWord domain102 raw2,restrictWord domain102 raw5,restrictWord domain102 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower102 : ¬construction goal102 3 sources102.toFinset := by
  intro h;have tr:=relabelConstruction pi0 inv0 h
  have dom : renameWord pi0 domain102=domain99 := by
    simp only [domain102,domain99,renameNot,renameOr,mv0_raw0,mv0_raw3,mv0_raw4] <;> rfl
  have fg : renameWord pi0 goal102=goal99 := by simp only [goal102,goal99,restrictWord,renameAnd,mv0_target,dom]
  have fs : sources102.toFinset.image (renameWord pi0)=sources99.toFinset := by
    simp only [sources102,sources99,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv0_raw1,mv0_raw2,mv0_raw5,mv0_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower99 tr
private def domain105 : Q := ~~~(raw1 ||| raw2 ||| raw4)
private def goal105 : Q := restrictWord domain105 target
private def sources105 : List Q := [restrictWord domain105 raw0,restrictWord domain105 raw3,restrictWord domain105 raw5,restrictWord domain105 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower105 : ¬construction goal105 3 sources105.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain105=domain99 := by
    simp only [domain105,domain99,renameNot,renameOr,mv2_raw1,mv2_raw2,mv2_raw4] <;> rfl
  have fg : renameWord pi2 goal105=goal99 := by simp only [goal105,goal99,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources105.toFinset.image (renameWord pi2)=sources99.toFinset := by
    simp only [sources105,sources99,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw0,mv2_raw3,mv2_raw5,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower99 tr
private def domain108 : Q := ~~~(raw0 ||| raw1 ||| raw4)
private def goal108 : Q := restrictWord domain108 target
private def sources108 : List Q := [restrictWord domain108 raw2,restrictWord domain108 raw3,restrictWord domain108 raw5,restrictWord domain108 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower108 : ¬construction goal108 3 sources108.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain108=domain102 := by
    simp only [domain108,domain102,renameNot,renameOr,mv2_raw0,mv2_raw1,mv2_raw4] <;> rfl
  have fg : renameWord pi2 goal108=goal102 := by simp only [goal108,goal102,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources108.toFinset.image (renameWord pi2)=sources102.toFinset := by
    simp only [sources108,sources102,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw2,mv2_raw3,mv2_raw5,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower102 tr
private def domain101 : Q := ~~~(raw1 ||| raw3 ||| raw4)
private def goal101 : Q := restrictWord domain101 target
private def sources101 : List Q := [restrictWord domain101 raw0,restrictWord domain101 raw2,restrictWord domain101 raw5,restrictWord domain101 raw6]
private def hints101 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound101 : soundHints goal101 hints101 := by
  simp [soundHints,hints101]
private def tips101 : Array Nat := #[0x0]
private def packed101 : Array Nat := #[0xc80001000,0x1a00000004000,0x801200880020002,0x2001800c00020010,0x2800000c80011000,0x2801a00000014000,0x2801a00c80015000]
private def dict101 (i : Nat) : Q := expandWord (packed101[i]?.getD 0)
private def a101_2_0 : Bank := [[0x1e3000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem z101_2_0 : a101_2_0.all (layerTest dict101 tips101 3 1 1 ([] : Bank) hints101 goal101) = true := by decide +kernel
private def bank101_2 : Bank := a101_2_0
private theorem ok101_2 : certified dict101 3 bank101_2 goal101 2 := by
  apply layerSound (advice:=tips101) (buckets:=1) sound101 emptyBank
  simp only [bank101_2,List.all_append,z101_2_0,Bool.and_self]
private def a101_3_0 : Bank := [[0xb1a000,0xd19000,0xf63000],[0x1e3000,0xfa3000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem z101_3_0 : a101_3_0.all (layerTest dict101 tips101 3 1 2 bank101_2 hints101 goal101) = true := by decide +kernel
private def bank101_3 : Bank := a101_3_0
private theorem ok101_3 : certified dict101 3 bank101_3 goal101 3 := by
  apply layerSound (advice:=tips101) (buckets:=1) sound101 ok101_2
  simp only [bank101_3,List.all_append,z101_3_0,Bool.and_self]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem root101 : checkChildren goal101 3 sources101 (rejectChild (chooseHints 0x0 hints101) goal101 dict101 3 2 bank101_3 3)=true := by decide +kernel
private theorem lower101 : ¬construction goal101 4 sources101.toFinset := by
  apply basisRefute sound101 (by decide +kernel) (by decide +kernel)
  exact Or.inr (Or.inr (checkedSound root101 (fun w nd h => rejectionSound (chosenSound sound101 _) ok101_3 nd h)))
private def domain106 : Q := ~~~(raw0 ||| raw2 ||| raw4)
private def goal106 : Q := restrictWord domain106 target
private def sources106 : List Q := [restrictWord domain106 raw1,restrictWord domain106 raw3,restrictWord domain106 raw5,restrictWord domain106 raw6]
private def hints106 : List Hint := []
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound106 : soundHints goal106 hints106 := by
  simp [soundHints,hints106]
private def packed106 : Array Nat := #[]
private def dict106 (i : Nat) : Q := expandWord (packed106[i]?.getD 0)
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem root106 : checkChildren goal106 2 sources106 (rejectChild (chooseHints 0x0 hints106) goal106 dict106 1 1 ([] : Bank) 2)=true := by decide +kernel
private theorem lower106 : ¬construction goal106 3 sources106.toFinset := by
  apply basisRefute sound106 (by decide +kernel) (by decide +kernel)
  exact Or.inr (Or.inr (checkedSound root106 (fun w nd h => rejectionSound (chosenSound sound106 _) emptyBank nd h)))
private def domain47 : Q := ~~~(raw4 ||| raw6)
private def goal47 : Q := restrictWord domain47 target
private def sources47 : List Q := [restrictWord domain47 raw0,restrictWord domain47 raw1,restrictWord domain47 raw2,restrictWord domain47 raw3,restrictWord domain47 raw5]
private def hints47 : List Hint := [(domain39,5,sources39),(domain43,4,sources43),(domain46,4,sources46),(domain37,4,sources37),(domain15,3,sources15),(domain35,2,sources35),(domain38,2,sources38),(domain42,2,sources42),(domain5,1,sources5),(domain10,1,sources10),(domain33,1,sources33),(domain34,1,sources34),(domain36,1,sources36)]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound47 : soundHints goal47 hints47 := by
  intro h mem; simp only [hints47,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hintLink (child:=goal39) (by decide +kernel) (by decide +kernel) lower39
  · exact hintLink (child:=goal43) (by decide +kernel) (by decide +kernel) lower43
  · exact hintLink (child:=goal46) (by decide +kernel) (by decide +kernel) lower46
  · exact hintLink (child:=goal37) (by decide +kernel) (by decide +kernel) lower37
  · exact hintLink (child:=goal15) (by decide +kernel) (by decide +kernel) lower15
  · exact hintLink (child:=goal35) (by decide +kernel) (by decide +kernel) lower35
  · exact hintLink (child:=goal38) (by decide +kernel) (by decide +kernel) lower38
  · exact hintLink (child:=goal42) (by decide +kernel) (by decide +kernel) lower42
  · exact hintLink (child:=goal5) (by decide +kernel) (by decide +kernel) lower5
  · exact hintLink (child:=goal10) (by decide +kernel) (by decide +kernel) lower10
  · exact hintLink (child:=goal33) (by decide +kernel) (by decide +kernel) lower33
  · exact hintLink (child:=goal34) (by decide +kernel) (by decide +kernel) lower34
  · exact hintLink (child:=goal36) (by decide +kernel) (by decide +kernel) lower36
private def tips47 : Array Nat := #[0x0,0x1,0x2,0x4,0x8,0xe]
private def packed47 : Array Nat := #[0x2a8036008a,0x53005c002c,0x6380003000,0x638010308a,0x9c00660130,0xbe807601ba,0xac802031c0,0xd500003000,0xd500403130,0xe0007821c0,0xe3807831c0,0xf5007831c0,0xff80003000,0xff8036308a,0xff80663130,0xff807831c0]
private def dict47 (i : Nat) : Q := expandWord (packed47[i]?.getD 0)
private def a47_4_0 : Bank := [[0xd51041000,0x1069ca1001],[0xd524a2000,0xd59441004,0xd61441004]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem z47_4_0 : a47_4_0.all (layerTest dict47 tips47 5 1 3 ([] : Bank) hints47 goal47) = true := by decide +kernel
private def bank47_4 : Bank := a47_4_0
private theorem ok47_4 : certified dict47 5 bank47_4 goal47 4 := by
  apply layerSound (advice:=tips47) (buckets:=1) sound47 emptyBank
  simp only [bank47_4,List.all_append,z47_4_0,Bool.and_self]
private def a47_5_0 : Bank := [[0x1cd51441002],[0x1069441004,0x1aa28c41001,0x1aa31441002,0x1aa41441001,0x1ed51441003]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem z47_5_0 : a47_5_0.all (layerTest dict47 tips47 5 2 4 bank47_4 hints47 goal47) = true := by decide +kernel
private def bank47_5 : Bank := a47_5_0
private theorem ok47_5 : certified dict47 5 bank47_5 goal47 5 := by
  apply layerSound (advice:=tips47) (buckets:=2) sound47 ok47_4
  simp only [bank47_5,List.all_append,z47_5_0,Bool.and_self]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem root47 : checkChildren goal47 5 sources47 (rejectChild (chooseHints 0xe hints47) goal47 dict47 5 2 bank47_5 5)=true := by decide +kernel
private theorem lower47 : ¬construction goal47 6 sources47.toFinset := by
  apply basisRefute sound47 (by decide +kernel) (by decide +kernel)
  exact Or.inr (Or.inr (checkedSound root47 (fun w nd h => rejectionSound (chosenSound sound47 _) ok47_5 nd h)))
private def domain79 : Q := ~~~(raw4 ||| raw5)
private def goal79 : Q := restrictWord domain79 target
private def sources79 : List Q := [restrictWord domain79 raw0,restrictWord domain79 raw1,restrictWord domain79 raw2,restrictWord domain79 raw3,restrictWord domain79 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower79 : ¬construction goal79 6 sources79.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain79=domain47 := by
    simp only [domain79,domain47,renameNot,renameOr,mv2_raw4,mv2_raw5] <;> rfl
  have fg : renameWord pi2 goal79=goal47 := by simp only [goal79,goal47,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources79.toFinset.image (renameWord pi2)=sources47.toFinset := by
    simp only [sources79,sources47,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw0,mv2_raw1,mv2_raw2,mv2_raw3,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower47 tr
private def domain103 : Q := ~~~(raw3 ||| raw4)
private def goal103 : Q := restrictWord domain103 target
private def sources103 : List Q := [restrictWord domain103 raw0,restrictWord domain103 raw1,restrictWord domain103 raw2,restrictWord domain103 raw5,restrictWord domain103 raw6]
private def hints103 : List Hint := [(domain39,5,sources39),(domain101,5,sources101),(domain99,4,sources99),(domain102,4,sources102),(domain37,4,sources37),(domain69,4,sources69),(domain35,2,sources35),(domain38,2,sources38),(domain97,2,sources97),(domain100,2,sources100),(domain5,1,sources5),(domain33,1,sources33),(domain34,1,sources34),(domain36,1,sources36),(domain65,1,sources65),(domain68,1,sources68)]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound103 : soundHints goal103 hints103 := by
  intro h mem; simp only [hints103,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hintLink (child:=goal39) (by decide +kernel) (by decide +kernel) lower39
  · exact hintLink (child:=goal101) (by decide +kernel) (by decide +kernel) lower101
  · exact hintLink (child:=goal99) (by decide +kernel) (by decide +kernel) lower99
  · exact hintLink (child:=goal102) (by decide +kernel) (by decide +kernel) lower102
  · exact hintLink (child:=goal37) (by decide +kernel) (by decide +kernel) lower37
  · exact hintLink (child:=goal69) (by decide +kernel) (by decide +kernel) lower69
  · exact hintLink (child:=goal35) (by decide +kernel) (by decide +kernel) lower35
  · exact hintLink (child:=goal38) (by decide +kernel) (by decide +kernel) lower38
  · exact hintLink (child:=goal97) (by decide +kernel) (by decide +kernel) lower97
  · exact hintLink (child:=goal100) (by decide +kernel) (by decide +kernel) lower100
  · exact hintLink (child:=goal5) (by decide +kernel) (by decide +kernel) lower5
  · exact hintLink (child:=goal33) (by decide +kernel) (by decide +kernel) lower33
  · exact hintLink (child:=goal34) (by decide +kernel) (by decide +kernel) lower34
  · exact hintLink (child:=goal36) (by decide +kernel) (by decide +kernel) lower36
  · exact hintLink (child:=goal65) (by decide +kernel) (by decide +kernel) lower65
  · exact hintLink (child:=goal68) (by decide +kernel) (by decide +kernel) lower68
private def tips103 : Array Nat := #[0x0,0x14,0x20,0x3c]
private def packed103 : Array Nat := #[0x1e8006003a,0x801600a8006000a,0x100240130004802c,0x180060038000800e,0x1803601b8006802e,0x2003801c00060030,0x2803e01e8006003a,0x3002801500008034,0x3003c01f0006803c,0x3803e01f8006803e,0x3800001f80011000,0x3803e0000001c000]
private def dict103 (i : Nat) : Q := expandWord (packed103[i]?.getD 0)
private def a103_4_0 : Bank := [[0xb6321000,0xcb642000,0xcb862000,0xcba62002]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem z103_4_0 : a103_4_0.all (layerTest dict103 tips103 4 1 3 ([] : Bank) hints103 goal103) = true := by decide +kernel
private def bank103_4 : Bank := a103_4_0
private theorem ok103_4 : certified dict103 4 bank103_4 goal103 4 := by
  apply layerSound (advice:=tips103) (buckets:=1) sound103 emptyBank
  simp only [bank103_4,List.all_append,z103_4_0,Bool.and_self]
private def a103_5_0 : Bank := [[0xcb652002,0xcb962002,0xcb7632001]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem z103_5_0 : a103_5_0.all (layerTest dict103 tips103 4 1 4 bank103_4 hints103 goal103) = true := by decide +kernel
private def bank103_5 : Bank := a103_5_0
private theorem ok103_5 : certified dict103 4 bank103_5 goal103 5 := by
  apply layerSound (advice:=tips103) (buckets:=1) sound103 ok103_4
  simp only [bank103_5,List.all_append,z103_5_0,Bool.and_self]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem root103 : checkChildren goal103 5 sources103 (rejectChild (chooseHints 0x3c hints103) goal103 dict103 4 1 bank103_5 5)=true := by decide +kernel
private theorem lower103 : ¬construction goal103 6 sources103.toFinset := by
  apply basisRefute sound103 (by decide +kernel) (by decide +kernel)
  exact Or.inr (Or.inr (checkedSound root103 (fun w nd h => rejectionSound (chosenSound sound103 _) ok103_5 nd h)))
private def domain109 : Q := ~~~(raw1 ||| raw4)
private def goal109 : Q := restrictWord domain109 target
private def sources109 : List Q := [restrictWord domain109 raw0,restrictWord domain109 raw2,restrictWord domain109 raw3,restrictWord domain109 raw5,restrictWord domain109 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower109 : ¬construction goal109 6 sources109.toFinset := by
  intro h;have tr:=relabelConstruction pi2 inv2 h
  have dom : renameWord pi2 domain109=domain103 := by
    simp only [domain109,domain103,renameNot,renameOr,mv2_raw1,mv2_raw4] <;> rfl
  have fg : renameWord pi2 goal109=goal103 := by simp only [goal109,goal103,restrictWord,renameAnd,mv2_target,dom]
  have fs : sources109.toFinset.image (renameWord pi2)=sources103.toFinset := by
    simp only [sources109,sources103,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv2_raw0,mv2_raw2,mv2_raw3,mv2_raw5,mv2_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower103 tr
private def domain107 : Q := ~~~(raw2 ||| raw4)
private def goal107 : Q := restrictWord domain107 target
private def sources107 : List Q := [restrictWord domain107 raw0,restrictWord domain107 raw1,restrictWord domain107 raw3,restrictWord domain107 raw5,restrictWord domain107 raw6]
private def hints107 : List Hint := [(domain43,4,sources43),(domain75,4,sources75),(domain99,4,sources99),(domain105,4,sources105),(domain106,4,sources106),(domain35,2,sources35),(domain42,2,sources42),(domain73,2,sources73),(domain74,2,sources74),(domain97,2,sources97),(domain10,1,sources10),(domain33,1,sources33),(domain34,1,sources34),(domain65,1,sources65),(domain72,1,sources72)]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound107 : soundHints goal107 hints107 := by
  intro h mem; simp only [hints107,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hintLink (child:=goal43) (by decide +kernel) (by decide +kernel) lower43
  · exact hintLink (child:=goal75) (by decide +kernel) (by decide +kernel) lower75
  · exact hintLink (child:=goal99) (by decide +kernel) (by decide +kernel) lower99
  · exact hintLink (child:=goal105) (by decide +kernel) (by decide +kernel) lower105
  · exact hintLink (child:=goal106) (by decide +kernel) (by decide +kernel) lower106
  · exact hintLink (child:=goal35) (by decide +kernel) (by decide +kernel) lower35
  · exact hintLink (child:=goal42) (by decide +kernel) (by decide +kernel) lower42
  · exact hintLink (child:=goal73) (by decide +kernel) (by decide +kernel) lower73
  · exact hintLink (child:=goal74) (by decide +kernel) (by decide +kernel) lower74
  · exact hintLink (child:=goal97) (by decide +kernel) (by decide +kernel) lower97
  · exact hintLink (child:=goal10) (by decide +kernel) (by decide +kernel) lower10
  · exact hintLink (child:=goal33) (by decide +kernel) (by decide +kernel) lower33
  · exact hintLink (child:=goal34) (by decide +kernel) (by decide +kernel) lower34
  · exact hintLink (child:=goal65) (by decide +kernel) (by decide +kernel) lower65
  · exact hintLink (child:=goal72) (by decide +kernel) (by decide +kernel) lower72
private def tips107 : Array Nat := #[0x0,0x1,0x2,0x4,0x8,0x10,0x1f]
private def packed107 : Array Nat := #[0x62801820ca,0x1860000018808e,0x80860228010008a,0x101040430018800c,0x181860638018808e,0x180060030001c00c,0x401c0060001820c0,0x481c6062801820ca,0x480c0020800130c0,0x501c40630018a0cc,0x501400410001f000,0x5800006380013000,0x580860638011308a,0x581040638019b00c,0x581c0063801930c0,0x581c60000001c000,0x581c60228011c08a,0x581c60430019c00c,0x581c60600019e0c0,0x581c60638001f000]
private def dict107 (i : Nat) : Q := expandWord (packed107[i]?.getD 0)
private def a107_4_0 : Bank := [[0x1061883000,0x1062ce4000],[0xc39061000,0x1039062000,0x10624e3000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem z107_4_0 : a107_4_0.all (layerTest dict107 tips107 5 1 3 ([] : Bank) hints107 goal107) = true := by decide +kernel
private def bank107_4 : Bank := a107_4_0
private theorem ok107_4 : certified dict107 5 bank107_4 goal107 4 := by
  apply layerSound (advice:=tips107) (buckets:=1) sound107 emptyBank
  simp only [bank107_4,List.all_append,z107_4_0,Bool.and_self]
private def a107_5_0 : Bank := [[0x20c39483002,0x20e61c83000,0x20f61c83004,0x25061c83003],[0x20c41c83001,0x20d61c83000,0x23061c83000,0x27061c83000],[0x20c51c83000,0x29061c83005]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem z107_5_0 : a107_5_0.all (layerTest dict107 tips107 5 2 4 bank107_4 hints107 goal107) = true := by decide +kernel
private def bank107_5 : Bank := a107_5_0
private theorem ok107_5 : certified dict107 5 bank107_5 goal107 5 := by
  apply layerSound (advice:=tips107) (buckets:=2) sound107 ok107_4
  simp only [bank107_5,List.all_append,z107_5_0,Bool.and_self]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem root107 : checkChildren goal107 5 sources107 (rejectChild (chooseHints 0x1f hints107) goal107 dict107 5 3 bank107_5 5)=true := by decide +kernel
private theorem lower107 : ¬construction goal107 6 sources107.toFinset := by
  apply basisRefute sound107 (by decide +kernel) (by decide +kernel)
  exact Or.inr (Or.inr (checkedSound root107 (fun w nd h => rejectionSound (chosenSound sound107 _) ok107_5 nd h)))
private def domain110 : Q := ~~~(raw0 ||| raw4)
private def goal110 : Q := restrictWord domain110 target
private def sources110 : List Q := [restrictWord domain110 raw1,restrictWord domain110 raw2,restrictWord domain110 raw3,restrictWord domain110 raw5,restrictWord domain110 raw6]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1200000 in
private theorem lower110 : ¬construction goal110 6 sources110.toFinset := by
  intro h;have tr:=relabelConstruction pi0 inv0 h
  have dom : renameWord pi0 domain110=domain107 := by
    simp only [domain110,domain107,renameNot,renameOr,mv0_raw0,mv0_raw4] <;> rfl
  have fg : renameWord pi0 goal110=goal107 := by simp only [goal110,goal107,restrictWord,renameAnd,mv0_target,dom]
  have fs : sources110.toFinset.image (renameWord pi0)=sources107.toFinset := by
    simp only [sources110,sources107,List.toFinset_cons,List.toFinset_nil,Finset.image_insert,Finset.image_empty,restrictWord,renameAnd,dom,mv0_raw1,mv0_raw2,mv0_raw3,mv0_raw5,mv0_raw6] <;> decide +kernel
  rw [fg,fs] at tr
  exact lower107 tr
private def domain111 : Q := ~~~(raw4)
private def goal111 : Q := restrictWord domain111 target
private def sources111 : List Q := [restrictWord domain111 raw0,restrictWord domain111 raw1,restrictWord domain111 raw2,restrictWord domain111 raw3,restrictWord domain111 raw5,restrictWord domain111 raw6]
private def hints111 : List Hint := [(domain47,7,sources47),(domain79,7,sources79),(domain103,7,sources103),(domain107,7,sources107),(domain109,7,sources109),(domain110,7,sources110),(domain39,5,sources39),(domain77,5,sources77),(domain101,5,sources101),(domain43,4,sources43),(domain46,4,sources46),(domain75,4,sources75),(domain78,4,sources78),(domain99,4,sources99),(domain102,4,sources102),(domain105,4,sources105),(domain106,4,sources106),(domain108,4,sources108),(domain37,4,sources37),(domain69,4,sources69),(domain15,3,sources15),(domain35,2,sources35),(domain38,2,sources38),(domain42,2,sources42),(domain73,2,sources73),(domain74,2,sources74),(domain76,2,sources76),(domain97,2,sources97),(domain100,2,sources100),(domain5,1,sources5),(domain10,1,sources10),(domain33,1,sources33),(domain34,1,sources34),(domain36,1,sources36),(domain65,1,sources65),(domain68,1,sources68),(domain72,1,sources72)]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1000000 in
private theorem sound111 : soundHints goal111 hints111 := by
  intro h mem; simp only [hints111,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hintLink (child:=goal47) (by decide +kernel) (by decide +kernel) lower47
  · exact hintLink (child:=goal79) (by decide +kernel) (by decide +kernel) lower79
  · exact hintLink (child:=goal103) (by decide +kernel) (by decide +kernel) lower103
  · exact hintLink (child:=goal107) (by decide +kernel) (by decide +kernel) lower107
  · exact hintLink (child:=goal109) (by decide +kernel) (by decide +kernel) lower109
  · exact hintLink (child:=goal110) (by decide +kernel) (by decide +kernel) lower110
  · exact hintLink (child:=goal39) (by decide +kernel) (by decide +kernel) lower39
  · exact hintLink (child:=goal77) (by decide +kernel) (by decide +kernel) lower77
  · exact hintLink (child:=goal101) (by decide +kernel) (by decide +kernel) lower101
  · exact hintLink (child:=goal43) (by decide +kernel) (by decide +kernel) lower43
  · exact hintLink (child:=goal46) (by decide +kernel) (by decide +kernel) lower46
  · exact hintLink (child:=goal75) (by decide +kernel) (by decide +kernel) lower75
  · exact hintLink (child:=goal78) (by decide +kernel) (by decide +kernel) lower78
  · exact hintLink (child:=goal99) (by decide +kernel) (by decide +kernel) lower99
  · exact hintLink (child:=goal102) (by decide +kernel) (by decide +kernel) lower102
  · exact hintLink (child:=goal105) (by decide +kernel) (by decide +kernel) lower105
  · exact hintLink (child:=goal106) (by decide +kernel) (by decide +kernel) lower106
  · exact hintLink (child:=goal108) (by decide +kernel) (by decide +kernel) lower108
  · exact hintLink (child:=goal37) (by decide +kernel) (by decide +kernel) lower37
  · exact hintLink (child:=goal69) (by decide +kernel) (by decide +kernel) lower69
  · exact hintLink (child:=goal15) (by decide +kernel) (by decide +kernel) lower15
  · exact hintLink (child:=goal35) (by decide +kernel) (by decide +kernel) lower35
  · exact hintLink (child:=goal38) (by decide +kernel) (by decide +kernel) lower38
  · exact hintLink (child:=goal42) (by decide +kernel) (by decide +kernel) lower42
  · exact hintLink (child:=goal73) (by decide +kernel) (by decide +kernel) lower73
  · exact hintLink (child:=goal74) (by decide +kernel) (by decide +kernel) lower74
  · exact hintLink (child:=goal76) (by decide +kernel) (by decide +kernel) lower76
  · exact hintLink (child:=goal97) (by decide +kernel) (by decide +kernel) lower97
  · exact hintLink (child:=goal100) (by decide +kernel) (by decide +kernel) lower100
  · exact hintLink (child:=goal5) (by decide +kernel) (by decide +kernel) lower5
  · exact hintLink (child:=goal10) (by decide +kernel) (by decide +kernel) lower10
  · exact hintLink (child:=goal33) (by decide +kernel) (by decide +kernel) lower33
  · exact hintLink (child:=goal34) (by decide +kernel) (by decide +kernel) lower34
  · exact hintLink (child:=goal36) (by decide +kernel) (by decide +kernel) lower36
  · exact hintLink (child:=goal65) (by decide +kernel) (by decide +kernel) lower65
  · exact hintLink (child:=goal68) (by decide +kernel) (by decide +kernel) lower68
  · exact hintLink (child:=goal72) (by decide +kernel) (by decide +kernel) lower72
private def packed111 : Array Nat := #[0x809602a8036008a,0x10124053005c802c,0x2023809c00660130,0x403c00e0007821c0,0x780000ff80013000,0x783fe0000001c000,0x2a8036008a,0x9c00660130,0xe0007821c0,0x1000800260000,0x960000036008a,0x124000005c802c,0x23800000660130,0x80860228010008a,0x100240130004802c,0x181b607b807e80ae,0x2022809400400130,0x282be0be807601ba,0x3033c0df007e813c,0x402c00a0002021c0,0x483d60ea807e21ca,0x503e40f3007ca1ec,0x5800006380013000,0x581c60000001c000,0x603f80fc007e21f0,0x700000d500013000,0x703680000001c000,0x780960ff8037308a,0x781240ff805db02c,0x782380ff80673130,0x783c00ff807931c0,0x783fe02a8037c08a,0x783fe053005dc02c,0x783fe09c0067c130,0x783fe0e00079e1c0,0x783fe0ff8001f000,0x7b807e00ae,0xbe807601ba,0xdf007e013c,0xea807e21ca,0xfc007e21f0,0xff8036308a,0xff80663130,0x1b6000007e80ae,0x2be000007601ba,0x33c000007e813c,0x3d6000007e01ca,0x3f8000007e01f0,0x3fe0000036c08a,0x3fe0000066c130,0x1010005300580000,0x1013405b007e802c,0x1803601b8006802e,0x181860638018808e,0x180060038001d000,0x2803e01e8006003a,0x2829a0ac80220192,0x3003c01f0006803c,0x303280d500488134,0x300280150001d000,0x383be0ff807e81be,0x3801601f8007100a,0x3803801f80071030,0x3803e00a8007c00a,0x3803e0130005c02c,0x3803e01c0007c030,0x3803e01f8001d000,0x403c004000580000,0x403d00e8007e21c0,0x481c6062801820ca,0x482d20a8802221c2,0x480c202080017000,0x501400410001f000,0x583f60fb807ea1ee,0x580860638011308a,0x581c60228011c08a,0x581c60638001f000,0x602d80ac002221d0,0x603680d400482170,0x6024808400017000,0x683fe0fe807e21fa,0x680920ac80233082,0x682180ac80233110,0x682c00ac802131c0,0x682da02880234082,0x682da08c00234110,0x682da0ac80017000,0x703fc0ff007ea1fc,0x702280d500413130,0x703680940041c130,0x703680d50001f000,0x783fe0ff807ea1fe,0x780100ff80273000,0x781b60ff807fb0ae,0x782be0ff807731ba,0x7833c0ff807fb13c,0x783be0ff807fb1be,0x783d60ff807f31ca,0x783f80ff807f31f0,0x783fe0ff807f31fa,0x783fe0080027c000,0x783fe07b807fc0ae,0x783fe0be8077c1ba,0x783fe0df007fc13c,0x783fe0ff807fc1be,0x783fe0ea807fe1ca,0x783fe0fc007fe1f0,0x783fe0fe807fe1fa,0x783fe0ff8037f08a,0x783fe0ff805df02c,0x783fe0ff807ff0ae,0x783fe0ff8067f130,0x783fe0ff8077f1ba,0x783fe0ff807ff13c,0x783fe0ff8079f1c0,0x783fe0ff807ff1ca,0x783fe0ff807ff1f0,0xff807e01be,0xfe807e21fa,0xff807e21fe,0xff807e30ae,0xff807631ba,0xff807e313c,0xff807e31ca,0xff807e31f0,0xff807e31fa,0x3be000007e81be,0x3fe000007e01fa,0x3fe000007e81fe,0x3fe000007ec0ae,0x3fe0000076c1ba,0x3fe000007ec13c,0x3fe000007ec1be,0x3fe000007ec1ca,0x3fe000007ec1f0,0x809602a80260000,0x80960ff807e01be,0x80960fe807e21fa,0x80960ff807631ba,0x83be02a807e81be,0x83fe02a807e01fa,0x83fe02a8076c1ba,0x101240ff807e81be,0x101240ff807eb0ae,0x101240ff807eb13c,0x103be053007e81be,0x103fe053007ec0ae,0x103fe053007ec13c,0x2023809c00260000,0x202380ff807e01be,0x202380fe807e21fa,0x202380ff807631ba,0x203be09c007e81be,0x203fe09c007e01fa,0x203fe09c0076c1ba,0x380000ff80000000,0x3803e01f8006803e,0x380be03f803680be,0x3813e05f805e803e,0x3823e09f8066813e,0x3803e01f8007103a,0x3803e01b0027c02c,0x3803e01b8007c02e,0x3803e01e8007c03a,0x3803e01f0007c03c,0x3803e01f8007c03e,0x3803e01f8007d00a,0x3803e01f8005d02c,0x3803e01f8007d02e,0x3803e01f8007d030,0x3803e01f8007d03c,0x380be03f803710ba,0x380be03e8037c0ba,0x380be03f8037d08a,0x3823e09f8067113a,0x3823e09e8067c13a,0x3823e09f8067d130,0x403c00fe807e21fa,0x403c00ff807e31ca,0x403c00ff807e31f0,0x403fe0e0007e21fa,0x403fe0e0007ee1ca,0x403fe0e0007ee1f0,0x581c60638018a0ce,0x581e6073805ca0ee,0x583c60e38078a1ce,0x581860638019b08e,0x581a6073805db0ae,0x581c6063801930ca,0x581c60638019c08e,0x581c60628019e0ca,0x581c60638011f08a,0x581c60638019f00c,0x581c60638019f08e,0x581c60638019f0c0,0x581c60638019f0ca,0x581d606b8037f08a,0x581e6073805dc0ae,0x581e6073805df02c,0x583c60e3807931ca,0x583c60e28079e1ca,0x583c60e38079f1c0,0x682da0ac802221d2,0x682de0ae803621da,0x682fa0bc806621f2,0x683da0ec807a21d2,0x683fe00000000000,0x6829a0ac80233192,0x6829e0ae8037319a,0x682ba0bc806731b2,0x682d00ac802731c0,0x682d20ac802331c2,0x682d80ac802331d0,0x682da0ac802331d2,0x682da0ac80234192,0x682da0ac80237082,0x682da0ac80237110,0x682da0ac802171c0,0x682da0ac802371c2,0x682da0ac802371d0,0x682de0ae8037419a,0x682de0ae8037708a,0x682fa0bc806741b2,0x682fa0bc80677130,0x703680d50048a174,0x7036c0d7005ca17c,0x703e80f50078a1f4,0x703280d50049b134,0x7032c0d7005db13c,0x703680d500493170,0x703680d50049c134,0x703680d40049e170,0x703680d50049f024,0x703680d50041f130,0x703680d50049f134,0x703680d50049f140,0x703680d50049f170,0x7036c0d7005dc13c,0x7036c0d7005df02c,0x703780dd0067f130,0x703e80f5007931f0,0x703e80f40079e1f0,0x703e80f50079f1c0,0x780000ff807f30ae,0x780000ff807731ba,0x780000ff807f313c,0x780000ff807f31ca,0x780000ff807f31f0,0x7803e0ff8007303a,0x7803e0ff8007f00a,0x7803e0ff8007f030,0x781860ff8019b08e,0x781c60ff801930ca,0x781c60ff8011f08a,0x7829a0ff80233192,0x782da0ff80237082,0x782da0ff80237110,0x783280ff8049b134,0x783680ff80493170,0x783680ff8041f130,0x783fe000007fc0ae,0x783fe0000077c1ba,0x783fe000007fc13c,0x783fe000007fc1ca,0x783fe000007fc1f0,0x783fe01e8007c03a,0x783fe01f8007d00a,0x783fe01f8007d030,0x783fe0638019c08e,0x783fe0628019e0ca,0x783fe0638011f08a,0x783fe0ac8023c192,0x783fe0ac8023f082,0x783fe0ac8023f110,0x783fe0d50049c134,0x783fe0d40049e170,0x783fe0d50041f130,0xe0007e21fa,0xf6805821fa,0x124000007e81be,0x3ae000005881be,0x180260138005c02e,0x180260138005d02c,0x3002c0170005c03c,0x3002c0170005d02c,0x3803e0000007c02e,0x3803e0000007c03c,0x482c20a0802131c2,0x482c20a0802171c0,0x602c80a4002131d0,0x602c80a4002171c0,0x680000ac802331c2,0x680000ac802331d0]
private def dict111 (i : Nat) : Q := expandWord (packed111[i]?.getD 0)
private def plan111 : Array Nat := #[0x80005,0x80405,0x80605,0x2,0x80004,0x80204,0x80404,0x80002,0x80203,0x40001,0x80400,0x40002,0x40202,0x80601,0x40003,0x40203,0x80802,0x80a02,0x40403,0x80800,0x80a00,0x40004,0x40204,0x40404,0x40604,0x40005,0x40205,0x40405,0x40605,0x40805,0x81e05,0x82205,0x82405,0x82805,0x83005,0x83605,0x83a05,0x81e04,0x82204,0x82404,0x82804,0x83004,0x83e04,0x84204,0x21e,0x1e12,0x81e03,0x81e02,0x84618,0x82203,0x82201,0x82403,0x82400,0x84614,0x40012,0x83603,0x83a03,0x83e03,0x84003,0x84203,0x84603,0x620,0x2818,0x82802,0x82801,0x84612,0x84611,0x40015,0x83602,0x83e02,0x84602,0x83001,0x83000,0x8460f,0x40018,0x83601,0x83a01,0x83c01,0x83e01,0x84201,0x84601,0x40218,0x83a00,0x84200,0x84600,0x41e18,0x361d,0x4001c,0x4001d,0x4021d,0x41e1d,0x4001e,0x4041e,0x4221e,0x3e21,0x40020,0x40021,0x40221,0x41e21,0x40022,0x40422,0x42222,0x40023,0x40223,0x41e23,0x40423,0x42223,0x42423,0x40623,0x42823,0x43023,0x87805,0x40c28,0x8b605,0x8ba05,0x8bc05,0x8be05,0x8c205,0x8c405,0x8c605,0x4142d,0x8a004,0x8b604,0x8ca04,0x8cc04,0x8ce04,0x8d004,0x8d204,0x8d404,0x6f,0x44c00,0x45000,0x45400,0x45a00,0x45e00,0x46200,0x44a01,0x45201,0x45401,0x45801,0x46001,0x46201,0x46c,0x44802,0x44e02,0x45202,0x45602,0x45c02,0x46002,0x7804,0x87803,0x40039,0x40237,0x46802,0x8bc03,0x41240,0x8ca03,0x8cc03,0x8ce03,0x8d003,0x8d803,0x8da03,0x8dc03,0x8de03,0x8e203,0x4003e,0x40041,0x4003b,0x4043d,0x4043f,0x40442,0x44a03,0x45203,0x45403,0x45803,0x46003,0x46203,0x89202,0x40245,0x46a03,0x8ba02,0x4024a,0x8c202,0x8ca02,0x8d202,0x41a4c,0x8da02,0x8dc02,0x8e402,0x8e602,0x40048,0x4024b,0x40247,0x4064a,0x4064b,0x4064c,0x8a001,0x4004d,0x40446,0x47003,0xa005,0x8bc01,0x40052,0x40451,0x41253,0x8c201,0x8c401,0x8c601,0x8cc01,0x8d801,0x8de01,0x8e401,0x8e601,0x8e801,0x40055,0x4004f,0x40454,0x40447,0x8ae00,0x4024e,0x47403,0x8be00,0x40258,0x8c400,0x8ce00,0x8d400,0x8da00,0x4205a,0x8e200,0x8e400,0x8e800,0x40259,0x4024f,0x40448,0x40658,0x40659,0x4065a,0x44804,0x44a04,0x44c04,0x44e04,0x45004,0x46e04,0x47e04,0x48204,0x46a04,0x48a04,0x49604,0x47004,0x4a804,0x4aa04,0x47404,0x49c04,0x4b204,0x45605,0x45805,0x45a05,0x45c05,0x45e05,0x46e05,0x47a05,0x47c05,0x46a05,0x48a05,0x49405,0x47005,0x4a205,0x4a405,0x47405,0x49c05,0x4b005,0x96805,0x8ec09,0x91c04,0x8fc09,0x98a03,0x98c03,0x9da03,0x9dc03,0xa0803,0xa0c03,0x98e01,0x99201,0x9e001,0x9e401,0x9ec01,0x9ee01]
private def tips111 : Array Nat := #[0x0,0x1,0x2,0x3,0x4,0x8,0xb,0x10,0x20,0x23,0x29,0x2a,0x2b,0x3f,0x40,0x80,0x12b,0x200,0x209,0x229,0x248,0x280,0x321,0x400,0x421,0x429,0x460,0x480,0x509,0x629,0x80a,0x82b,0x840,0x888,0x921,0xb2b,0xc00,0x1022,0x102b,0x1040,0x10a0,0x1109,0x1200,0x152b,0x182a,0x2000,0x2001,0x200c,0x200d,0x2048,0x2085,0x2400,0x3000,0x4000,0x4001,0x4024,0x4025,0x4060,0x4085,0x4200,0x4800,0x6128,0x8000,0x8002,0x8018,0x801a,0x804a,0x8088,0x8400,0x9000,0xc010,0x10000,0x10001,0x10002,0x1000b,0x10028,0x10029,0x1002a,0x1003f,0x10048,0x1004a,0x10085,0x10088,0x10108,0x10229,0x10429,0x1082a,0x1102a,0x20000,0x20002,0x20030,0x2003a,0x2004a,0x200a0,0x20200,0x20800,0x22010,0x28128,0x40000,0x40002,0x4002a,0x4002e,0x4002f,0x40080,0x40208,0x4020a,0x4022b,0x40420,0x40422,0x4042b,0x40804,0x40820,0x40c00,0x41004,0x41008,0x41200,0x42000,0x42208,0x43000,0x43200,0x44000,0x44420,0x44800,0x44c00,0x48002,0x48008,0x4800e,0x49000,0x49200,0x50002,0x5000c,0x51802,0x5602e,0x60002,0x60020,0x60026,0x60800,0x60c00,0x80000,0x80001,0x80029,0x80039,0x80040,0x80210,0x80220,0x80408,0x80410,0x80808,0x80809,0x8082b,0x80c00,0x81020,0x81021,0x8102b,0x81200,0x82001,0x82008,0x82019,0x82400,0x82c00,0x84001,0x84020,0x84031,0x84200,0x85200,0x88000,0x88400,0x88808,0x88c00,0x90001,0x90018,0x90601,0xa0000,0xa0200,0xa1020,0xa1200,0xb8039,0xc0000,0xc0028,0xc203c,0xc3008,0xc403c,0xc4810,0xc803c,0xc9004,0xca00c,0xcb000,0xd0000,0xe003c,0xe0804,0xe4024,0xe4800]
private def maps111 : Array (Array Nat) := #[#[2,1,0,3,4,5,7,6,8,9,12,11,10,16,14,18,13,17,15,19,24,21,25,26,20,22,23,29,28,27,30,33,32,31,34,35,38,37,36,40,39,42,41,45,44,43,47,46,49,48,50,51,57,58,59,55,56,52,53,54,60,62,61,65,64,63,66,67,68,78,77,79,72,87,88,89,90,70,69,71,80,82,81,83,85,84,86,73,74,75,76,91,92,95,94,93,96,98,97,99,100,103,102,101,104,106,105,107,111,109,113,108,112,110,114,116,115,117,118,119,122,121,120,124,123,125,126,127,128,131,130,129,132,134,133,148,149,150,151,152,153,154,142,144,143,145,147,146,135,136,137,138,139,140,141,155,156,159,158,157,160,161,164,163,162,165,169,167,170,166,168,174,175,176,171,172,173,177,179,178,180,182,181,224,225,226,227,228,229,230,231,233,232,234,235,236,239,237,238,240,241,242,202,204,203,205,206,207,209,208,210,212,211,213,214,216,215,217,219,218,222,223,220,221,183,184,185,186,187,188,189,190,192,191,193,194,195,197,198,196,199,200,201,245,244,243,247,246,248,250,249,257,258,259,254,256,255,251,252,253,262,261,260,264,263,265,267,266,274,275,276,271,273,272,268,269,270,277,278,279,280,283,284,281,282,286,285,289,290,287,288,292,291],#[0,3,2,1,5,4,10,12,11,9,6,8,7,13,19,20,16,17,24,14,15,21,23,22,18,26,25,31,34,33,32,27,30,29,28,35,46,44,47,43,45,48,49,39,37,40,36,38,41,42,67,68,70,69,71,56,55,77,78,79,80,84,85,81,83,82,86,50,51,53,52,54,72,73,75,74,76,57,58,59,60,63,65,64,61,62,66,87,89,88,90,91,100,105,102,106,107,101,103,104,92,97,94,98,99,93,95,96,108,114,115,111,112,116,109,110,113,127,126,128,133,130,134,129,131,132,118,117,119,123,121,124,125,120,122,135,140,139,141,137,136,138,180,181,182,177,178,179,148,153,152,154,150,149,151,206,202,203,205,204,214,210,211,207,212,213,215,217,218,216,219,220,208,221,222,209,223,145,146,147,142,143,144,183,185,184,190,200,189,188,186,191,194,195,192,193,196,199,201,197,187,198,156,157,159,158,155,163,172,175,161,162,164,165,160,166,169,167,168,170,171,173,174,176,224,226,225,231,241,230,229,227,235,233,236,232,234,240,242,239,237,228,238,263,261,264,260,262,271,272,273,269,268,270,265,266,267,275,274,276,246,244,247,243,245,254,255,256,252,251,253,248,249,250,258,257,259,279,280,277,278,287,288,289,290,291,292,281,282,283,284,285,286]]
private def paths111 : Array (List Nat) := #[[],[0],[1],[0,1]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem planok111 : recipeTest dict111 9 6 plan111=true := by decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem planok111_0 : recipeTest (fun i => dict111 ((mappedIndex maps111 293 0) i)) 9 6 plan111=true := by decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1500000 in
private lemma action111_0 : rowAction dict111 goal111 (mappedIndex maps111 293 0) := by
  have dm : renameWord pi0 domain111=domain111 := by
    simp only [domain111,renameNot,renameOr,mv0_raw4] <;> rfl
  apply actionByRename dict111 pi0 (mappedIndex maps111 293 0) goal111 inv0
  · simp only [goal111,restrictWord,renameAnd,mv0_target,dm]
  · have initial : ∀i<6,renameWord pi0 (dict111 i)=dict111 ((mappedIndex maps111 293 0) i) := by
      intro i hi;interval_cases i
      · rw [show dict111 0=restrictWord domain111 raw0 by decide +kernel]
        simp only [restrictWord,renameAnd,mv0_raw0,dm]
        decide +kernel
      · rw [show dict111 1=restrictWord domain111 raw1 by decide +kernel]
        simp only [restrictWord,renameAnd,mv0_raw1,dm]
        decide +kernel
      · rw [show dict111 2=restrictWord domain111 raw2 by decide +kernel]
        simp only [restrictWord,renameAnd,mv0_raw2,dm]
        decide +kernel
      · rw [show dict111 3=restrictWord domain111 raw3 by decide +kernel]
        simp only [restrictWord,renameAnd,mv0_raw3,dm]
        decide +kernel
      · rw [show dict111 4=restrictWord domain111 raw5 by decide +kernel]
        simp only [restrictWord,renameAnd,mv0_raw5,dm]
        decide +kernel
      · rw [show dict111 5=restrictWord domain111 raw6 by decide +kernel]
        simp only [restrictWord,renameAnd,mv0_raw6,dm]
        decide +kernel
    intro i
    by_cases hi : i<293
    · exact recipeTransfer dict111 (fun i => dict111 ((mappedIndex maps111 293 0) i)) pi0 9 6 plan111 planok111 planok111_0 initial i hi
    · have beyond : packed111[i]? = none := Array.getElem?_eq_none (show packed111.size ≤ i from Nat.le_of_not_gt hi)
      have zero : dict111 i=0 := by unfold dict111;rw [beyond];decide +kernel
      rw [zero,renameZero,mappedIndex,ite_eq_right hi]
      decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem planok111_1 : recipeTest (fun i => dict111 ((mappedIndex maps111 293 1) i)) 9 6 plan111=true := by decide +kernel
set_option maxRecDepth 15000 in
set_option maxHeartbeats 1500000 in
private lemma action111_1 : rowAction dict111 goal111 (mappedIndex maps111 293 1) := by
  have dm : renameWord pi2 domain111=domain111 := by
    simp only [domain111,renameNot,renameOr,mv2_raw4] <;> rfl
  apply actionByRename dict111 pi2 (mappedIndex maps111 293 1) goal111 inv2
  · simp only [goal111,restrictWord,renameAnd,mv2_target,dm]
  · have initial : ∀i<6,renameWord pi2 (dict111 i)=dict111 ((mappedIndex maps111 293 1) i) := by
      intro i hi;interval_cases i
      · rw [show dict111 0=restrictWord domain111 raw0 by decide +kernel]
        simp only [restrictWord,renameAnd,mv2_raw0,dm]
        decide +kernel
      · rw [show dict111 1=restrictWord domain111 raw1 by decide +kernel]
        simp only [restrictWord,renameAnd,mv2_raw1,dm]
        decide +kernel
      · rw [show dict111 2=restrictWord domain111 raw2 by decide +kernel]
        simp only [restrictWord,renameAnd,mv2_raw2,dm]
        decide +kernel
      · rw [show dict111 3=restrictWord domain111 raw3 by decide +kernel]
        simp only [restrictWord,renameAnd,mv2_raw3,dm]
        decide +kernel
      · rw [show dict111 4=restrictWord domain111 raw5 by decide +kernel]
        simp only [restrictWord,renameAnd,mv2_raw5,dm]
        decide +kernel
      · rw [show dict111 5=restrictWord domain111 raw6 by decide +kernel]
        simp only [restrictWord,renameAnd,mv2_raw6,dm]
        decide +kernel
    intro i
    by_cases hi : i<293
    · exact recipeTransfer dict111 (fun i => dict111 ((mappedIndex maps111 293 1) i)) pi2 9 6 plan111 planok111 planok111_1 initial i hi
    · have beyond : packed111[i]? = none := Array.getElem?_eq_none (show packed111.size ≤ i from Nat.le_of_not_gt hi)
      have zero : dict111 i=0 := by unfold dict111;rw [beyond];decide +kernel
      rw [zero,renameZero,mappedIndex,ite_eq_right hi]
      decide +kernel
private lemma action111 : ∀g<maps111.size,rowAction dict111 goal111 (mappedIndex maps111 293 g) := by
  intro g h;change g<2 at h;interval_cases g
  · exact action111_0
  · exact action111_1
private def ar111_4_0 : Bank := [[0x5020480517000,0x62e9042402000],[0x5d020480477000,0x65029042402000,0x65029240802000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_4_0 : ar111_4_0.all (layerTest dict111 tips111 9 1 3 ([] : Bank) hints111 goal111)=true := by decide +kernel
private def br111_4 : Bank := ar111_4_0
private lemma ro111_4 : certified dict111 9 br111_4 goal111 4 :=
  layerSound (buckets:=1) (advice:=tips111) sound111 emptyBank (by simp only [br111_4,List.all_append,zr111_4_0,Bool.and_self])
private def af111_4_0 : Bank := [[0x6502048047f002,0x65029042402000],[0x6020480519002,0x62e9042402000,0x62e9240802002,0x5d020480477000,0x65029240802000,0x65029500812002],[0x5020480517000,0x62e9500812002]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_4_0 : af111_4_0.all (orbitRow dict111 9 2 293 br111_4 maps111 paths111)=true := by decide +kernel
private def bf111_4 : Bank := af111_4_0
private lemma fo111_4 : certified dict111 9 bf111_4 goal111 4 :=
  orbitSafe (buckets:=2) (paths:=paths111) action111 ro111_4 (by simp only [bf111_4,List.all_append,zf111_4_0,Bool.and_self])
private def ar111_5_0 : Bank := [[0xc0524810040a000,0xc05268100488000,0xc055480c0401000,0xc05600100401000,0x484c0b8100401000],[0xa04018080316000,0xc055100c0401000,0x48220f8640401062],[0xc0501c680401000,0xc05610100401000,0x400526810040e000,0x48220e0102402000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_5_0 : ar111_5_0.all (layerTest dict111 tips111 9 3 4 bf111_4 hints111 goal111)=true := by decide +kernel
private def ar111_5_1 : Bank := [[0xa15018085207000],[0xa0401808027e000,0xa44018080226000,0xc050c8542610004,0xc052080c6801000,0xc055300c0401000,0xc058f00c0401000],[0xc0520848040a000,0xc052880c660100e],[0xc0501c6c0401000,0xc052300c6601000,0xc1e0e0107a02000,0xc5d2080c0401000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_5_1 : ar111_5_1.all (layerTest dict111 tips111 9 3 4 bf111_4 hints111 goal111)=true := by decide +kernel
private def ar111_5_2 : Bank := [[0xc1e02048042a000,0x4420028642a02000,0xe020028102402008],[0xa04018080277000,0xa04018080278000,0xa04090081477000,0x4420028107002000,0xca052080c0401000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_5_2 : ar111_5_2.all (layerTest dict111 tips111 9 3 4 bf111_4 hints111 goal111)=true := by decide +kernel
private def br111_5 : Bank := ar111_5_0 ++ ar111_5_1 ++ ar111_5_2
private lemma ro111_5 : certified dict111 9 br111_5 goal111 5 :=
  layerSound (buckets:=3) (advice:=tips111) sound111 fo111_4 (by simp only [br111_5,List.all_append,zr111_5_0,zr111_5_1,zr111_5_2,Bool.and_self])
private def af111_5_0 : Bank := [[0xa44018080226000,0xc1e02048042a000,0x400526810040e000,0x48210f0102601002,0xda22028102402001],[0xc04018080281002,0xc058f80c0401001,0xc05900100601002,0xc05920100601002,0xc1c02048042b001],[0xa0401808027e000,0xc05698100601002,0xc058e80c0401001,0xc1c26810040e002,0x4005020480432003],[0xc04018080285002,0xc0524810040a000,0xc05268100488000,0xc056e0100601003,0xc5d2a0100601002],[0xa15018085207000,0xc04018080318002,0xc05908100601002],[0xc04018cc022d002,0xc052a010240a002,0xc055300c0401000,0xc05620100401002,0xc05750100602001,0xc058e00c0401001,0xc05918100601003,0x44052d8102202001],[0x48220e0102402000],[0xc05220ec0601003,0xc052880c6601000,0xc5d2080c0401000,0x4420028107002000],[],[0xa19010045008001,0xc0520848040a000,0xc056b0100601002,0xc05928100601003,0x485a0d0100602001],[0x4420028642a02000,0x48200f8540602001,0xca052a0100601002],[0xa04018080277000,0xa04018080278000,0xc05610100401000,0xc058f00c0401000,0x48220f8640401000],[0xc052200c6c01002,0xc05768100602003],[0xc04018405c0b002,0xc1e0e0107202002],[0x481b2c8100602003,0xca052080c0401000],[0xc05220f40601002,0xc052d8112a02001,0xc056d8100601002,0x484c0b8100401000,0xe020028102402000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_5_0 : af111_5_0.all (orbitRow dict111 9 9 293 br111_5 maps111 paths111)=true := by decide +kernel
private def af111_5_1 : Bank := [[0xa04090081477000,0xc0401808027f002,0xc0501c680401000,0xc052300c6601000,0xc052780c6601001,0xc055580c0401001,0xc05600100401000,0xc1e0e0107a02000],[0xc0501c6c0401000,0xc05758100602001,0xc1e0e0102610002,0x4420029440802002,0x48210e0100610003,0xda060f0102402003,0xe0060e0102402002],[0xa04018080316000,0xc04098041a2c003,0xc055100c0401000,0xc05910100601003,0x4818258100401002],[0x4405020480431002],[0xc052a1140601002],[0xc0409008fe0a002,0xc050c8542610000,0xc052080c6801000,0xc055480c0401000,0xc1e2d8102202003,0x48200f0102402001]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_5_1 : af111_5_1.all (orbitRow dict111 9 9 293 br111_5 maps111 paths111)=true := by decide +kernel
private def bf111_5 : Bank := af111_5_0 ++ af111_5_1
private lemma fo111_5 : certified dict111 9 bf111_5 goal111 5 :=
  orbitSafe (buckets:=9) (paths:=paths111) action111 ro111_5 (by simp only [bf111_5,List.all_append,zf111_5_0,zf111_5_1,Bool.and_self])
private def ar111_6_0 : Bank := [[0x180a040900c042a005,0x1c040050200c0401008],[0xc055180c0401000,0x183e052300c0401000],[0x14a204018080277001,0x180a0401a3c0401002,0x180a0401a480401000,0x183c05020ec0401000,0x19f8050200c0401000,0x19fc050200c0401000,0x880c1f028640401062,0x1bc0c050200c040102d]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_6_0 : ar111_6_0.all (layerTest dict111 tips111 9 22 5 bf111_5 hints111 goal111)=true := by decide +kernel
private def ar111_6_1 : Bank := [[0x140803010041226000,0x180a04018080276000,0x180a04018091201000,0x180a5c0200c0401003,0x180ac10200c0401000,0x800a4d0200c0401000],[0x180a0401a400401001,0x180a044f80c0401000,0x180a46018081e01000,0x1c00c050200c0488000],[0xa04018080277000,0x183805600100401000,0x19ee050200c0401007,0x880c05020e00401000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_6_1 : ar111_6_1.all (layerTest dict111 tips111 9 22 5 bf111_5 hints111 goal111)=true := by decide +kernel
private def ar111_6_2 : Bank := [[0x900c055400c0401000,0x90cc050200c040108a,0x1ac0c050a80c0401008,0x1cc0c050a80c0401058],[0x180a045680c0401000,0x180a19018d40401005,0x180ac50200c0401000,0x183c05020f40401002,0x18c8050200c0401062,0x1c00c05268100401001,0x1c40c050200c0401000],[0x180a045200c0401000,0x8c0c052300c0401000,0x900c1f2180c0401062]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_6_2 : ar111_6_2.all (layerTest dict111 tips111 9 22 5 bf111_5 hints111 goal111)=true := by decide +kernel
private def ar111_6_3 : Bank := [[0x180a04018dc0401002,0x904405020480401000],[0x180a540200c0207000,0x183c1c0204c0401000,0x880c1c028102402011,0x900c041f00c0401001],[0xc055400c0401000,0x180ab80200c0401000,0x180abc0200c0401000,0x18c2050200c0401000,0x19ea050200c0401000,0x880c050c8540401000,0x90ce050200c0401002]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_6_3 : ar111_6_3.all (layerTest dict111 tips111 9 22 5 bf111_5 hints111 goal111)=true := by decide +kernel
private def ar111_6_4 : Bank := [[0x180a04018080277000,0x180a045080c0401000,0x183e052880c0401003,0x8c0c052880c0401001,0x900c1f0a80c0401062],[0x19f4050200c0401000,0x900c05600100401000],[0x180ab90200c0401004,0x840a04018080226007,0x1980c055180c0401004],[0x180a0401808027a000,0x180a51018081e01048,0x180abb0200c0401000,0x1b40c05600100401005]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_6_4 : ar111_6_4.all (layerTest dict111 tips111 9 22 5 bf111_5 hints111 goal111)=true := by decide +kernel
private def ar111_6_5 : Bank := [[0x180a04018091601000,0x180a4101808020a067,0x19e8050200c0401001,0x900c4b0200c0401000,0x90421c0200c040108a],[0x180a4c0204c0401007],[0xc05600100401000,0x180aa3018400401000,0x180abd0200c0401000,0x180ac60200c0401004,0x1b80c055400c0401004],[0x180a044f00c0401000,0x1838052080c0401000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_6_5 : ar111_6_5.all (layerTest dict111 tips111 9 22 5 bf111_5 hints111 goal111)=true := by decide +kernel
private def ar111_6_6 : Bank := [[0x442002810240200a,0x180a190a84c0401007,0x180a4101808020e000,0x1c00c05020480401008],[0x140803010045207000,0x142a04018080277000,0x180a045380c0401000,0x180ac70200c0401004,0x183c0401808022a000],[0xc056700c0401000,0x18083d4e00c0401000,0x180a4c0b8100401000,0x180ac00200c0401000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_6_6 : ar111_6_6.all (layerTest dict111 tips111 9 22 5 bf111_5 hints111 goal111)=true := by decide +kernel
private def ar111_6_7 : Bank := [[0x180a410900c0401000,0x19f2050200c0401000],[0x180a040980c0225000,0x18c6050a80c0401058],[0x180a045600c0401000,0x900c1e0204c040103f,0x90441c0200c0401000,0x1cc0c052180c040100f],[0x140812018080277000,0x180a0401a4c0401000,0x180a490200c0401000,0x904405268100401000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_6_7 : ar111_6_7.all (layerTest dict111 tips111 9 22 5 bf111_5 hints111 goal111)=true := by decide +kernel
private def ar111_6_8 : Bank := [[0x180a4d02008020e000,0x1a00050200c0401000],[0x180a0401808027c000,0x180a04018091401000,0x180a044e80c0401047,0x180a045700c0401000,0x19fa050200c0401000,0x19fe050200c0401000,0x800c055180c0401000],[0x180a04018080279000,0x180a19018080228000,0x183e052000c0401063,0x900a04018080228002]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_6_8 : ar111_6_8.all (layerTest dict111 tips111 9 22 5 bf111_5 hints111 goal111)=true := by decide +kernel
private def br111_6 : Bank := ar111_6_0 ++ ar111_6_1 ++ ar111_6_2 ++ ar111_6_3 ++ ar111_6_4 ++ ar111_6_5 ++ ar111_6_6 ++ ar111_6_7 ++ ar111_6_8
private lemma ro111_6 : certified dict111 9 br111_6 goal111 6 :=
  layerSound (buckets:=22) (advice:=tips111) sound111 fo111_5 (by simp only [br111_6,List.all_append,zr111_6_0,zr111_6_1,zr111_6_2,zr111_6_3,zr111_6_4,zr111_6_5,zr111_6_6,zr111_6_7,zr111_6_8,Bool.and_self])
private def af111_6_0 : Bank := [[0x180a540200c2201003,0x900a4c0200c0401002,0x9042050200c2001002,0x1cc0c050a80c0401000],[0x180aba0200c0401002,0x180abf0200c0401002,0x183a05020f40601002],[0x840a04018080226000],[0xa04018080277000,0x180a41018440401001,0x180a51018081e01000,0x180a5a0d0100602001,0x183c052080c0401001,0x880c05020e00401000,0x904405020480401000],[0x180ac60200c0401000,0x19fa050200c0401000],[0x180a04018091a01002,0x800a04018080232003,0x8840050c8100401002],[0x140803010045008001],[],[0x180ad80200c0401002,0x880c052a0100601003,0x1b80c050200c2001002],[0xc055400c0401000,0x180acd0200c0401003,0x183c05020e40401002,0x800a4d0200c0401000,0x41c0c050200c0401003],[0x180abd0200c0401000,0x18c4056a0100601002],[0x180a04018dc0401000,0x1838052080c0401000,0x183e052100c0401001,0x4280c050200c0401002],[0x900c041f80c0401001,0x1d00c050200c0401002,0x4480c050200c0401003],[0x180a044c00c0401001,0x180a19018080228000,0x183a05020ec0601003,0x183e052300c0401000,0x840c05298100601003,0x900c1c020480602003,0x1b444050200c0401001],[0x180aa50980c0401001,0x19f0050200c0401001,0x900c1c0200c2002001,0x9042050204c0601003,0x1b40c052d8100602001,0x42c0c050200c0401002],[0x14a2cf0200c0401002,0x180ad70200c0401002,0x18c8050200c0401000,0x800c050c8540602001],[0x180a04018080280002,0x180a045500c0401001,0x180ae20200c0401001,0x180ae40200c0401001,0x900c1f0a80c0401000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_6_0 : af111_6_0.all (orbitRow dict111 9 30 293 br111_6 maps111 paths111)=true := by decide +kernel
private def af111_6_1 : Bank := [[0xc056a0100601002,0x180a04018080282002,0x180ab40200c0401003,0x183c05750100602001,0x840c1e028102601002,0x900a5a0200c0401003],[0x180a04018080277000,0x180a4101808020b002,0x180ae50200c0401001,0x1c040050200c0401000],[0x180a044f00c0401000],[0x180a0401808027d001,0x180a4f018081e01001,0x180a5a0200c2002001,0x183e052880c0401000,0x18c6050a80c0401000,0x1a04050200c0401001,0x90d0050200c0401001],[0x180a04018080276000,0x180a044c80c0401003,0x180ac10200c0401000,0x180ac70200c0401000,0x180aef0200c0401001,0x180af00200c0401001,0x1c00c05268100401000],[0x180a04018091601000,0x180a190a84c0401000,0x90cc050200c0401000,0x1b40c05022540401001,0x4300c050200c0401003],[0x180ae10200c0401001],[0x180a151d00c0401001,0x900a04018080229001,0x900c1f0c80c0401001,0x9044050c8100401002],[0x180a15018080229001,0x180aca0200c0401002,0x183e0401808022d002,0x18bc050204c0601003,0x880c050c8540401000,0x880c05750100602003],[],[0x180a18258100401002,0x180ab30200c0401002,0x183805020f40602001],[0x180a04018091c01002,0x180a470204c0601002,0x180a540200c0207000,0x1838056a0100601002],[0x180a0401808027a000,0x18384d0200c0401002,0x183c5b0200c0401003,0x19f4050200c0401000,0x900c05600100401000,0x1c80c050200c0401001],[0x180ab90200c0401000,0x19f8050200c0401000,0x4380c050200c0401002,0x4440c050200c0401002],[0x180a0401a440401001,0x180ad00200c0401002]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_6_1 : af111_6_1.all (orbitRow dict111 9 30 293 br111_6 maps111 paths111)=true := by decide +kernel
private def af111_6_2 : Bank := [[0x180af10200c0401003],[0x140803010041226000,0x180803010045a0c002,0x180a410900c0401000,0x18c6056a8100601003,0x8840050a8100602003],[0x180a4101808020a000,0x180ab60200c0401002,0x180ab70200c0401003,0x183c056a8100601003,0x840c05290100601002,0x1c00c05750100602001],[0x1cc0c050c80c0401001],[0x140812018080277000,0x14a204018080277000,0x180a0401a4c0401000,0x180a044f80c0401000,0x180ac00200c0401000,0x180ae90200c0401001,0x900c1e020480401002],[0x18083d01808027f002,0x183e052780c0401001,0x800c05600100401002],[0x180a045200c0401000,0x183c1c0204c0401000,0x19e8050200c0401000,0x800c055180c0401000,0x8c0c052300c0401000,0x1b80c055400c0401000,0x1c00c1c0200c0401002],[0x180add0200c0401002],[0x18081201808027f002,0x180a040980c0225000,0x180a4c0b8100401000,0x180a4e0200c2001003,0x180aa3018400401000],[0xc05750100602001,0x18080308008027f002,0x180a0409008022b001,0x180a040900c0431002,0x1b40c05600100401000],[0x180803010041a2c003,0x18083d4e00c0401000,0x180acc0200c0401002,0x840c050200c6c01002,0x90441f0200c0401003,0x4400c050200c0401002],[0x180a0401a500401001,0x180a044b80c0401001,0x180a5c0200c0401000,0x1838050204c0610003,0x800c1f028540602001],[0x180a190a80c2002001,0x800c05230100602003,0x880c055280c0401001,0x900c056d0100601002,0x4180c050200c0401002],[0x180ad50c8100601003],[0xc056700c0401000,0x180a040a00c6c01002,0x18c0050200c2001002,0x18c4050c80c0401001,0x900c0401808022c002,0x900c590200c0401001,0x9040052d8100602001,0x1b40c1e0200c0401003]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_6_2 : af111_6_2.all (orbitRow dict111 9 30 293 br111_6 maps111 paths111)=true := by decide +kernel
private def af111_6_3 : Bank := [[0x180a04018080283002,0x180a044d80c0401003,0x180a4101808020d003,0x180acb0200c0401002],[0x180a0401808027c000,0x180a0401808027f002,0x180a0401a3c0401000,0x180a0401a400401000,0x180a040980c022c002,0x180a5b0200c2202001,0x180abe0200c0401002,0x904405268100401000,0x1bc0c050200c0401000],[0x142a04018080277000,0x180a045000c0401001],[0x180a044e80c0401000,0x180a190204c2001002,0x180ae60200c0401001,0x880c1c028102402000],[0x180a150204c0610003,0x180a1901808022f002,0x180ab50200c0401002,0x180ae30200c0401003,0x800c05288100602003,0x900c1e0204c0401000,0x43c0c050200c0401002],[0x180a045080c0401000,0x900c5f0200c0401002],[0x183805020e40602003],[],[0x18081301808027f003,0x180ace0200c0401002,0x1b40c05020480602001],[0x4420028102402000,0x180a044b00c0401001,0x183a050200c6c01002,0x800c052a0100601002,0x4200c050200c0401002,0x4500c050200c0401003],[0x180a04018400227001,0x180a500200c0401003,0x180a54020480601002,0x180ab80200c0401000,0x183c0401808022a000],[0xc056a8100601003,0x180a540200c020a002,0x90421e0200c0401001,0x1c00c050200c0488000],[0x180a04018091801002,0x180ac50200c0401000,0x18c2050200c0401000,0x1a06050200c0401001,0x900a550200c0401002,0x1a40c050200c0401002,0x1d40c050200c0401003],[0xc055280c0401001,0x180803010045c0b002,0x180a044d00c0401003,0x183c1c0200c2002001,0x900c055400c0401000,0x900c630200c0401003]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_6_3 : af111_6_3.all (orbitRow dict111 9 30 293 br111_6 maps111 paths111)=true := by decide +kernel
private def af111_6_4 : Bank := [[0x180a04018091201000,0x880c05288100401002,0x1a80c050c80c0401001],[0x180ad10200c0401002,0x183c05020ec0401000,0x19fe050200c0401000,0x900c4b0200c0401000],[0x180ac80200c0401002,0x180ad40a8100601002,0x180aea0200c0401001,0x880a5b0200c0401001,0x1a00c055280c0401001],[0x1a08050200c0401001],[0x180a1b2c8100602003,0x180ae80200c0401003,0x1a00050200c0401000,0x90441c0200c0401000,0x44c0c050200c0401003],[0x180a040900c042a000,0x180a041e00c0401001,0x180a045780c0401001,0x183c050204c2001002,0x19ec050200c0401001,0x840c05020ec0601003,0x880a04018080231002,0x900c1c2d8100602003,0x90421c0200c0401000],[0xc050227c0601002,0x180abb0200c0401000,0x180ad20200c0401003],[0xc1e0e0102402002,0x180a04018080287003,0x180a0401a480401000,0x180ac90200c0401002],[0x180a045600c0401000,0x180af20200c0401003,0x19ee050200c0401000,0x1cc0c056d0100601002],[0x180a040a0ec0601003,0x180a490200c0401000,0x180aec0200c0401003,0x1c00c05020480401000],[0x140803010045207000,0x900a04018080228000],[0xc05600100401000,0x180a045700c0401000,0x8c0c052880c0401000],[0xc055180c0401000,0x180a04018080286002,0x9040050a8100602003,0x1b80c052b8100601002],[0xc0401808027f002,0x180a045880c0401001,0x840c1c028100610003,0x1ac0c050a80c0401000],[0x180a19258100401002,0x180a4c0204c0401000],[0x180a04018091401000,0x180ab20200c0401002,0x18380401808022b001,0x1a00c050200c2001002]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_6_4 : af111_6_4.all (orbitRow dict111 9 30 293 br111_6 maps111 paths111)=true := by decide +kernel
private def af111_6_5 : Bank := [[0x180a045680c0401000,0x180a540200c0208001,0x183c05020f40401000,0x900a560200c0401003],[0x19f6050200c0401001,0x880c05278100401002,0x900c1f2180c0401000,0x900c620200c0401002,0x90401e0200c0401001,0x1980c055180c0401000],[],[0x180ae00200c0401003,0x19fc050200c0401000],[0x180a0401840022e003,0x180adf0200c0401003,0x180af30200c0401003,0x1a02050200c0401001,0x840c05020f40601002,0x900c1e268100401002],[0x1838050200c6c02001],[0x180a0401808027b001,0x183805600100401000,0x4540c050200c0401003],[0x143204018080277001,0x180a04090080232003],[0x180a040a0f40601002,0x90ce050200c0401000,0x4140c050200c0401002],[0x900c041f00c0401000],[0xc056d0100601002,0x180a540200c020e002,0x180a590a8100602003,0x180abc0200c0401000,0x180aee0200c0401001,0x183e052000c0401000,0x800c05020e00602001,0x904005020480602001,0x1b00c050200c0401002,0x1c40c050200c0401000,0x4340c050200c0401002],[0x880c1f028640401000],[0x180ac30200c0401002,0x180ade0200c0401002,0x19f2050200c0401000,0x8c0c052780c0401001,0x1b80c050204c0601003,0x1cc0c052180c0401000],[0x180a4101808020e000,0x180a46018081e01000,0x800c1e028102402001,0x90401f0200c0401002],[0x180a04018080284003,0x180a19018d40401000,0x180a4d02008020e000,0x180ad90200c0401003,0x19ea050200c0401000,0x4240c050200c0401003],[0x180a15018080230003,0x180a480200c0401002,0x180ae70200c0401003,0x900c05750100602001,0x9042052b8100601002,0x1980c050204c0601003]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_6_5 : af111_6_5.all (orbitRow dict111 9 30 293 br111_6 maps111 paths111)=true := by decide +kernel
private def af111_6_6 : Bank := [[0x180a04018080279000,0x180a045380c0401000,0x180a045800c0401001,0x900c0401808022e003]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_6_6 : af111_6_6.all (orbitRow dict111 9 30 293 br111_6 maps111 paths111)=true := by decide +kernel
private def bf111_6 : Bank := af111_6_0 ++ af111_6_1 ++ af111_6_2 ++ af111_6_3 ++ af111_6_4 ++ af111_6_5 ++ af111_6_6
private lemma fo111_6 : certified dict111 9 bf111_6 goal111 6 :=
  orbitSafe (buckets:=30) (paths:=paths111) action111 ro111_6 (by simp only [bf111_6,List.all_append,zf111_6_0,zf111_6_1,zf111_6_2,zf111_6_3,zf111_6_4,zf111_6_5,zf111_6_6,Bool.and_self])
private def ar111_7_0 : Bank := [[0x180a0401808022807a],[0x3014083d01840040105b,0x30142c040900c0401053,0x30143204018400401060,0x3014940401840040105a,0x317838050200c0401028,(4564989957 * 2^48 + 2202248679466),(4699207685 * 2^48 + 2202248679463),(14631319557 * 2^48 + 2202248679462)],[0x317c38050200c0401025],[0x180a04018080225088,0x180a190204c04010b9,0x180a4b0200c0401072,0x8840050200c040101d,0x30780a0401840040105f,(13691783684 * 2^48 + 1666451509382),(14773390341 * 2^48 + 2202248679523)]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_7_0 : ar111_7_0.all (layerTest dict111 tips111 9 94 6 bf111_6 hints111 goal111)=true := by decide +kernel
private def ar111_7_1 : Bank := [[0x180a040180802260a9,0x9040050200c040106c,0x3014083d0900c040104d],[0x183c050204c04010a7,0x18c4050200c04010a4,0x9042050200c04010b1,0x31780a0401840040105d,(4564978180 * 2^48 + 1666451509342),(4833413709 * 2^48 + 2202248679430)],[0x180a04018d404010bd,0x1b80c050200c04010bb,(4833413636 * 2^48 + 1666451509381)]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_7_1 : ar111_7_1.all (layerTest dict111 tips111 9 94 6 bf111_6 hints111 goal111)=true := by decide +kernel
private def ar111_7_2 : Bank := [[0x180a041c00c0401051,0x180a190a80c040103d,0x180a4a0200c04010bf],[0x180a0401808022a029,0x180a041e80c04010b0,0x180a042000c0401070,0x180a4d0200c0401010,0x183c05020480401056,0x30740a040900c0401052,0x318838050200c0401097],[0x180a04018d8040105c,(4833413636 * 2^48 + 36836864954507),(14639172613 * 2^48 + 2202248679436)]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_7_2 : ar111_7_2.all (layerTest dict111 tips111 9 94 6 bf111_6 hints111 goal111)=true := by decide +kernel
private def ar111_7_3 : Bank := [[0xc052080c0401067,0x307c0a040900c04010aa,0x317c0a040900c040104b,(4833413636 * 2^48 + 9898830073930)],[0x8c0c050a80c0401078],[0x180a042180c04010a9,0x18bc050200c04010af,0x1b40c050200c040102b],[0x180a041f00c040109a,0x183e050a80c04010a2,0x18be050200c0401083,(4430772229 * 2^48 + 2202248679537)]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_7_3 : ar111_7_3.all (layerTest dict111 tips111 9 94 6 bf111_6 hints111 goal111)=true := by decide +kernel
private def br111_7 : Bank := ar111_7_0 ++ ar111_7_1 ++ ar111_7_2 ++ ar111_7_3
private lemma ro111_7 : certified dict111 9 br111_7 goal111 7 :=
  layerSound (buckets:=94) (advice:=tips111) sound111 fo111_6 (by simp only [br111_7,List.all_append,zr111_7_0,zr111_7_1,zr111_7_2,zr111_7_3,Bool.and_self])
private def af111_7_0 : Bank := [[(14639172613 * 2^48 + 2202248679424)],[0x180a042000c0401000,0x180a4e0200c0401003,0x31800a040980c0401001,(4833413657 * 2^48 + 2202248679427)],[0x180a04018080227001,0x180a0401808022f002,0x180a190204c0401000,0x900c1f0200c0401002,0x9044050200c0401001,(4699207685 * 2^48 + 2202248679424),(4833413636 * 2^48 + 10448585887745)],[0x18be050200c0401000,0x840c050200c2001002,(4430760452 * 2^48 + 9898830073858),(15444478981 * 2^48 + 2202248679426)],[(4430773253 * 2^48 + 2202248679425)],[0x180a0401808022e003,0x18c0050200c0401001,(4296555013 * 2^48 + 2202248679426)],[0x180a5b0200c0401001,(13960219140 * 2^48 + 10448585887745)],[0x180a0401808022a000,(4833413723 * 2^48 + 2202248679425)],[0x1838050200c2002001],[0x183e050a80c0401000,0x900c1c0200c0401002,0x1c00c050200c0401001,0x3014a2150200c0401002,0x30780a150200c0401002,0x31880a150200c0401002],[0x180a0401808022b001,0x180a041d00c0401001,0x180a460200c0401002,0x180a560200c0401003,0x180a570200c0401002,0x183c05020480401000,0x9040050200c0401000,0x30142c040900c0401000,(4833413636 * 2^48 + 1666451509248),(13826001412 * 2^48 + 9898830073858),(15041825797 * 2^48 + 2202248679425)],[0x180a041f80c0401001,0x180a4d0200c0401000,0x307c0a040900c0401000,(4833413719 * 2^48 + 2202248679426)],[0x180a042180c0401000,(4833413709 * 2^48 + 2202248679424)],[0x180a190a80c0401000,0x180a4b0200c0401000,0x1a00c050200c0401003,0x3014a2190200c0401003,0x318c3c050200c0401001,(4833413636 * 2^48 + 36836864954368)],[0x180a04018d40401000,0x180a5a0200c0401003,0x3014083d0980c0401001],[0x180a041c80c0401002],[0x183e050c80c0401001,0x880c05020480401002,0x318838050200c0401000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_7_0 : af111_7_0.all (orbitRow dict111 9 14 293 br111_7 maps111 paths111)=true := by decide +kernel
private def af111_7_1 : Bank := [[(13833341957 * 2^48 + 2202248679427)],[0x180a041e80c0401000,0x317c0a040900c0401000,(4564978197 * 2^48 + 2202248679426),(4564991493 * 2^48 + 2202248679427),(14228654613 * 2^48 + 2202248679426)],[0xc052a0100601002,0x180a040980c2001002,0x3014083d018400401000,0x3014b0190200c0401003,(4296555525 * 2^48 + 2202248679425),(14370212869 * 2^48 + 2202248679427)],[0x3014b0040980c0401001],[(4430772229 * 2^48 + 2202248679424)],[0x180a04018080225000,0x180a04018080226000,0x180a590200c0401001,0x183805020480602001,0x800c05020480602003,0x301494150200c0401002,0x317c3c050200c0401001],[0x183a050204c0601003,(13698599941 * 2^48 + 2202248679426)],[0x180a04018080230003,0x180a510200c0401002,0x183c1c0200c0401002,0x18c4050200c0401000,0x31803c050200c0401001,(4833413636 * 2^48 + 9898830073856),(14362872345 * 2^48 + 2202248679427)],[0x180a04018080231002,0x180a470200c0401002,0x30780a04018400401000,(4564989957 * 2^48 + 2202248679424),(4699195908 * 2^48 + 9898830073858),(13832817669 * 2^48 + 2202248679426),(14235470853 * 2^48 + 2202248679426),(15033973765 * 2^48 + 2202248679425)],[0x8c0c050a80c0401000,(4296556037 * 2^48 + 2202248679426),(4699208709 * 2^48 + 2202248679425)],[0x180a4c0200c0401002,0x180a580200c0401001,0x30142a040980c0401001,0x318c0a190200c0401003],[0x180a04018080232003,0x180a550200c0401002,0x183a050200c2001002],[0x180a0401808022d002,0x180a04018d80401000,0x180a041c00c0401000,0x180a041d80c0401001,0x183c050204c0401000,(13691783684 * 2^48 + 1666451509248)],[0x8c0c050c80c0401001],[0x1980c050200c0401002,0x1b80c050200c0401000,0x30740a040900c0401000,0x317838050200c0401000],[0x180a04018080228000,(14631319557 * 2^48 + 2202248679424),(14638124037 * 2^48 + 2202248679426),(14773390341 * 2^48 + 2202248679424)]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_7_1 : af111_7_1.all (orbitRow dict111 9 14 293 br111_7 maps111 paths111)=true := by decide +kernel
private def af111_7_2 : Bank := [[0x800c050a8100602003,0x900c1e0200c0401003,0x19c0c050200c0401002,0x1a80c050200c0401002,0x30700a190200c0401003,(4296542745 * 2^48 + 2202248679427)],[0xc052080c0401000,0x880c050c8100401002,0x8840050200c0401000,(4564978180 * 2^48 + 1666451509248),(15041301509 * 2^48 + 2202248679427)],[0x180a041f00c0401000,0x18c6050200c0401001,0x1ac0c050200c0401003,0x30149404018400401000,(4833413653 * 2^48 + 2202248679426)],[0x180a042100c0401001,0x9042050200c0401000,0x3014083d0900c0401000,0x317c38050200c0401000],[0x180a4a0200c0401000,0x30700a040980c0401001,(4296542724 * 2^48 + 10448585887745)],[0x180a04018080229001,0x180a520200c0401002,(4564990469 * 2^48 + 2202248679427),(13967559685 * 2^48 + 2202248679427)],[0x180a0401808022c002,0x180a150200c2002001,0x18bc050200c0401000,0x840c050204c0601003,0x30143204018400401000,0x3014a2040900c0401002],[0x180a4f0200c0401003,0x180a530200c0401003,0x1b40c050200c0401000,0x1cc0c050200c0401002,0x31780a04018400401000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_7_2 : af111_7_2.all (orbitRow dict111 9 14 293 br111_7 maps111 paths111)=true := by decide +kernel
private def bf111_7 : Bank := af111_7_0 ++ af111_7_1 ++ af111_7_2
private lemma fo111_7 : certified dict111 9 bf111_7 goal111 7 :=
  orbitSafe (buckets:=14) (paths:=paths111) action111 ro111_7 (by simp only [bf111_7,List.all_append,zf111_7_0,zf111_7_1,zf111_7_2,Bool.and_self])
private def ar111_8_0 : Bank := [[0x180a040184004010bc,0x183a050200c040108c,0x183e050200c040108d],[0x180a040900c040104e,0x180a160200c04010b2,0x1838050200c0401099,0x900c050200c0401066]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zr111_8_0 : ar111_8_0.all (layerTest dict111 tips111 9 41 7 bf111_7 hints111 goal111)=true := by decide +kernel
private def br111_8 : Bank := ar111_8_0
private lemma ro111_8 : certified dict111 9 br111_8 goal111 8 :=
  layerSound (buckets:=41) (advice:=tips111) sound111 fo111_7 (by simp only [br111_8,List.all_append,zr111_8_0,Bool.and_self])
private def af111_8_0 : Bank := [[0x180a04018400401000,0x180a150200c0401002,0x183e050200c0401000,0x880c050200c0401003,0x8c0c050200c0401002],[0x180a040900c0401000,0x180a160200c0401000,0x900c050200c0401000],[0x180a040980c0401001,0x180a190200c0401003,0x183a050200c0401000,0x183c050200c0401001,0x800c050200c0401002,0x840c050200c0401002],[0x1838050200c0401000]]
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem zf111_8_0 : af111_8_0.all (orbitRow dict111 9 2 293 br111_8 maps111 paths111)=true := by decide +kernel
private def bf111_8 : Bank := af111_8_0
private lemma fo111_8 : certified dict111 9 bf111_8 goal111 8 :=
  orbitSafe (buckets:=2) (paths:=paths111) action111 ro111_8 (by simp only [bf111_8,List.all_append,zf111_8_0,Bool.and_self])
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem root111 : checkChildren goal111 8 sources111 (rejectChild (chooseHints 0x3f hints111) goal111 dict111 9 4 bf111_8 8)=true := by decide +kernel
private theorem lower111 : ¬construction goal111 9 sources111.toFinset := by
  apply basisRefute sound111 (by decide +kernel) (by decide +kernel)
  exact Or.inr (Or.inr (checkedSound root111 (fun w nd h => rejectionSound (chosenSound sound111 _) fo111_8 nd h)))
private def readQ (x : Fin 64) (w : Q) := w.getLsbD x.val
private def Basis (gs : List Gate) :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem read_not (x : Fin 64) (w : Q) : readQ x (~~~w) = !(readQ x w) := by
  simp [readQ, x.isLt]
private theorem read_zero (x : Fin 64) : readQ x 0 = false := by simp [readQ]

private theorem getD_table (x : Fin 64) (ws : List Q) (i : ℕ) :
    (ws.map (readQ x)).getD i false = readQ x (ws.getD i 0) := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [readQ]

private def gateQ (ws : List Q) (g : Gate) : Q :=
  match g.op, g.inputs with
  | .and, [] => ~~~0
  | .and, [i] => ws.getD i 0
  | .and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | .or, [] => 0
  | .or, [i] => ws.getD i 0
  | .or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | .not, [] => ~~~0
  | .not, i :: _ => ~~~(ws.getD i 0)
  | _, _ => 0

private theorem read_gateQ (x : Fin 64) (ws : List Q) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => (ws.map (readQ x)).getD i false) =
      readQ x (gateQ ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_table]
  cases op with
  | and =>
    match ins, hlen with
    | [], _ =>
      change true = readQ x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | [i], _ => simp [gateQ, GateOp.eval]
    | [i, j], _ => simp [gateQ, GateOp.eval, readQ, BitVec.getLsbD_and]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => simp [gateQ, GateOp.eval, readQ]
    | [i], _ => simp [gateQ, GateOp.eval]
    | [i, j], _ => simp [gateQ, GateOp.eval, readQ, BitVec.getLsbD_or]
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases ins with
    | nil =>
      change true = readQ x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | cons i is =>
      exact (read_not x (ws.getD i 0)).symm
  | mod m => simp at hop
  | maj => simp at hop

private def wireQs (gs : List Gate) (ws : List Q) : List Q :=
  gs.foldl (fun vs g => vs ++ [gateQ vs g]) ws

private theorem read_wireQs (x : Fin 64) (gs : List Gate) (ws : List Q)
    (h : Basis gs) :
    (Circuit.wires ⟨gs, 0⟩ (ws.map (readQ x))) = (wireQs gs ws).map (readQ x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg := read_gateQ x ws g (h g List.mem_cons_self)
    change Circuit.wires ⟨gs, 0⟩
        (ws.map (readQ x) ++ [g.op.eval (g.inputs.map fun i =>
          (ws.map (readQ x)).getD i false)]) =
      (wireQs gs (ws ++ [gateQ ws g])).map (readQ x)
    rw [hg, ← List.map_singleton, ← List.map_append]
    exact ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

private def isBin (g : Gate) : Bool :=
  match g.op, g.inputs with
  | .and, [_, _] => true
  | .or, [_, _] => true
  | _, _ => false

private def cost (gs : List Gate) : ℕ := gs.countP isBin

private def avail (ws : List Q) : Finset Q := insert 0 (ws.map norm).toFinset

private theorem norm_compl (u : Q) : norm (~~~u) = norm u := by
  unfold norm
  cases h : u.getLsbD 0 <;> simp only [BitVec.getLsbD_not, h] <;> simp

private theorem norm_pair (u v : Q) :
    norm (u &&& v) ∈ ops (norm u) (norm v) ∧ norm (u ||| v) ∈ ops (norm u) (norm v) := by
  unfold norm ops
  cases hu : u.getLsbD 0 <;> cases hv : v.getLsbD 0 <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, hu, hv] <;> simp [BitVec.not_and, BitVec.not_or, BitVec.and_comm, BitVec.or_comm]

private theorem norm_get (ws : List Q) (i : ℕ) : norm (ws.getD i 0) ∈ avail ws := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    simp [avail, List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩]
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [avail, norm]

private theorem fresh_pair {s : Finset Q} {c u v : Q} (hc : c ∈ ops u v) (hu : u ∈ s) (hv : v ∈ s)
    (hz : (0 : Q) ∈ s) (hf : c ∉ s) : u ≠ v := by
  rintro rfl
  simp only [ops, BitVec.and_self, BitVec.or_self, BitVec.and_not_self, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  grind

private theorem fresh_gate (ws : List Q) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hf : norm (gateQ ws g) ∉ avail ws) :
    isBin g = true ∧ ∃ a ∈ avail ws, ∃ b ∈ avail ws, a ≠ b ∧ norm (gateQ ws g) ∈ ops a b := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, len⟩ := hg
  have hz : norm 0 ∈ avail ws := by simp [avail, norm]
  have pair (i j : ℕ) {c : Q} (h : c ∈ ops (norm (ws.getD i 0)) (norm (ws.getD j 0)))
      (hn : c ∉ avail ws) :
      ∃ a ∈ avail ws, ∃ b ∈ avail ws, a ≠ b ∧ c ∈ ops a b :=
    ⟨_, norm_get ws i, _, norm_get ws j, fresh_pair h (norm_get ws i) (norm_get ws j)
      (by simp [avail]) hn, h⟩
  cases op with
  | and =>
    match ins, len with
    | [], _ => exact False.elim (hf (by change norm (~~~(0 : Q)) ∈ avail ws; rwa [norm_compl]))
    | [i], _ => exact False.elim (hf (norm_get ws i))
    | [i,j], _ => exact ⟨rfl, pair i j (norm_pair _ _).1 hf⟩
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, len with
    | [], _ => exact False.elim (hf hz)
    | [i], _ => exact False.elim (hf (norm_get ws i))
    | [i,j], _ => exact ⟨rfl, pair i j (norm_pair _ _).2 hf⟩
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    exfalso
    apply hf
    cases ins with
    | nil => change norm (~~~(0 : Q)) ∈ avail ws; rwa [norm_compl]
    | cons i is => simpa [gateQ, norm_compl] using norm_get ws i
  | mod m => simp at hop
  | maj => simp at hop

private theorem trail_extract {gs : List Gate} (ws : List Q) (hb : Basis gs) (o : ℕ) :
    ∃ s ⊆ avail ws, Trail (norm ((wireQs gs ws).getD o 0)) s (cost gs) := by
  induction gs generalizing ws with
  | nil => exact ⟨{_}, Finset.singleton_subset_iff.mpr (norm_get ws o), .done _⟩
  | cons g gs ih =>
    let c := norm (gateQ ws g)
    obtain ⟨s, hs, ht⟩ := ih (ws ++ [gateQ ws g]) (fun x hx => hb x (by simp [hx]))
    change ∃ s ⊆ avail ws, Trail (norm ((wireQs gs (ws ++ [gateQ ws g])).getD o 0)) s _
    have he : avail (ws ++ [gateQ ws g]) = insert c (avail ws) := by
      ext x; simp [avail, c]; tauto
    rw [he] at hs
    have hcost : cost gs ≤ cost (g :: gs) := by simp [cost, List.countP_cons]
    by_cases sub : s ⊆ avail ws
    · exact ⟨s, sub, trail_mono ht hcost⟩
    · have hn : c ∉ avail ws := by
        intro hh; rw [Finset.insert_eq_of_mem hh] at hs; exact sub hs
      have hcs : c ∈ s := by
        by_contra h
        apply sub; intro x hx
        exact (Finset.mem_insert.mp (hs hx)).resolve_left (by rintro rfl; exact h hx)
      have hr : s.erase c ⊆ avail ws := by
        intro x hx
        exact (Finset.mem_insert.mp (hs (Finset.mem_of_mem_erase hx))).resolve_left
          (Finset.ne_of_mem_erase hx)
      obtain ⟨hbin, a, ha, b, hbb, hab, hc⟩ := fresh_gate ws g (hb g (by simp)) hn
      have heq : insert c (s.erase c) = s := Finset.insert_erase hcs
      have hsub : insert a (insert b (s.erase c)) ⊆ avail ws := Finset.insert_subset_iff.mpr ⟨ha, Finset.insert_subset_iff.mpr ⟨hbb,hr⟩⟩
      refine ⟨_, hsub, ?_⟩
      rw [show cost (g :: gs) = cost gs + 1 by simp [cost, List.countP_cons, hbin]]
      exact .step hab (fun h => hn (hsub h)) (fun h => hn (h ▸ (by simp [avail])))
        hc (by rwa [heq])

private theorem cost_lt {gs : List Gate} (hh : ∃ g ∈ gs, g.op = .not) : cost gs < gs.length := by
  have h : ∃ g ∈ gs, isBin g = false := by
    obtain ⟨g, hg, hop⟩ := hh
    exact ⟨g, hg, by simp [isBin, hop]⟩
  simpa [cost] using (List.countP_lt_length_iff.mpr h)

private lemma wires_append (g1 g2 : List Gate) (x : List Bool) :
    Circuit.wires ⟨g1 ++ g2, 0⟩ x = Circuit.wires ⟨g2, 0⟩ (Circuit.wires ⟨g1, 0⟩ x) := by
  simp [Circuit.wires, List.foldl_append]

private lemma wires_append_singleton (pref : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨pref ++ [g], 0⟩ x =
    Circuit.wires ⟨pref, 0⟩ x ++ [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false)] := by
  rw [wires_append]
  rfl

private lemma wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    simp only [Circuit.wires, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

private lemma wires_cons_getD_lt (pref : List Gate) (g : Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + pref.length) :
    (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD w false = (Circuit.wires ⟨pref, 0⟩ x).getD w false := by
  rw [wires_append_singleton]
  have hlen : (Circuit.wires ⟨pref, 0⟩ x).length = x.length + pref.length := wires_length pref x
  have hlt : w < (Circuit.wires ⟨pref, 0⟩ x).length := by omega
  simp [List.getD, List.getElem?_append_left hlt]

private lemma wires_cons_getD_eq (pref : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD (x.length + pref.length) false =
    g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false) := by
  rw [wires_append_singleton]
  have hlen : (Circuit.wires ⟨pref, 0⟩ x).length = x.length + pref.length := wires_length pref x
  rw [← hlen]
  simp [List.getD]

private def Simple (D : List Bool → Prop) (p : ℕ) (f : List Bool → Bool) : Prop :=
  (∀ x, D x → f x = f (x.set p false)) ∨
  (∀ x, D x → f x = x.getD p false) ∨
  (∀ x, D x → f x = !(x.getD p false))

private lemma simple_const (D : List Bool → Prop) (p : ℕ) (b : Bool) :
    Simple D p (fun _ => b) := Or.inl (fun _ _ => rfl)

private lemma simple_not {D : List Bool → Prop} {p : ℕ} {f : List Bool → Bool}
    (hf : Simple D p f) : Simple D p (fun x => !(f x)) := by
  rcases hf with h1 | h2 | h3
  · exact Or.inl (fun x hx => by dsimp only; rw [h1 x hx])
  · exact Or.inr (Or.inr (fun x hx => by dsimp only; rw [h2 x hx]))
  · exact Or.inr (Or.inl (fun x hx => by dsimp only; rw [h3 x hx, Bool.not_not]))

private lemma wire_simple_all {D : List Bool → Prop} {p : ℕ} {pref : List Gate}
    (hlenD : ∀ x, D x → x.length = 8)
    (hpref : ∀ w < 8 + pref.length, Simple D p (fun x => (Circuit.wires ⟨pref, 0⟩ x).getD w false))
    (w : ℕ) : Simple D p (fun x => (Circuit.wires ⟨pref, 0⟩ x).getD w false) := by
  by_cases hw : w < 8 + pref.length
  · exact hpref w hw
  · left
    intro x hx
    dsimp only
    have h1 : (Circuit.wires ⟨pref, 0⟩ x).length = 8 + pref.length := by
      rw [wires_length, hlenD x hx]
    have h2 : (Circuit.wires ⟨pref, 0⟩ (x.set p false)).length = 8 + pref.length := by
      rw [wires_length, List.length_set, hlenD x hx]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private lemma gate_non_simple {D : List Bool → Prop} {p : ℕ} {pref : List Gate} {g : Gate}
    (hlenD : ∀ x, D x → x.length = 8)
    (hD : ∀ x, D x → D (x.set p false))
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hpref : ∀ w < 8 + pref.length, Simple D p (fun x => (Circuit.wires ⟨pref, 0⟩ x).getD w false))
    (hnot : ¬ Simple D p (fun x => g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false))) :
    isBin g = true ∧ ∃ g' : Gate,
      (g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
      isBin g' = false ∧
      ∀ x, D x → x.getD p false = false →
        g'.op.eval (g'.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false) =
        g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  cases op with
  | not =>
    exfalso; apply hnot
    cases ins with
    | nil => exact simple_const D p true
    | cons a _ => exact simple_not (wire_simple_all hlenD hpref a)
  | mod m => simp at hop
  | maj => simp at hop
  | and =>
    match ins, hlen with
    | [], _ => exact False.elim (hnot (simple_const D p true))
    | [a], _ =>
      exfalso; apply hnot
      simpa [GateOp.eval] using wire_simple_all hlenD hpref a
    | [a, b], _ =>
      refine ⟨rfl, ?_⟩
      have ha := wire_simple_all hlenD hpref a
      have hb := wire_simple_all hlenD hpref b
      dsimp only [Simple] at ha hb
      rcases ha with ha1 | ha2 | ha3
      · rcases hb with hb1 | hb2 | hb3
        · exfalso; apply hnot; left; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha1 x hx, hb1 x hx]
        · refine ⟨⟨.or, []⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, List.any_nil, id_eq, Bool.and_true]
          rw [hb2 x hx, hxp, Bool.and_false]
        · refine ⟨⟨.or, [a]⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          rw [hb3 x hx, hxp, Bool.not_false, Bool.and_true]
      · rcases hb with hb1 | hb2 | hb3
        · refine ⟨⟨.or, []⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, List.any_nil, id_eq, Bool.and_true]
          rw [ha2 x hx, hxp, Bool.false_and]
        · exfalso; apply hnot; right; left; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha2 x hx, hb2 x hx, Bool.and_self]
        · exfalso; apply hnot; left; intro x hx
          have hx' := hD x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha2 x hx, hb3 x hx, ha2 _ hx', hb3 _ hx']
          cases x.getD p false <;> cases (x.set p false).getD p false <;> rfl
      · rcases hb with hb1 | hb2 | hb3
        · refine ⟨⟨.or, [b]⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          rw [ha3 x hx, hxp, Bool.not_false, Bool.true_and]
        · exfalso; apply hnot; left; intro x hx
          have hx' := hD x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha3 x hx, hb2 x hx, ha3 _ hx', hb2 _ hx']
          cases x.getD p false <;> cases (x.set p false).getD p false <;> rfl
        · exfalso; apply hnot; right; right; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha3 x hx, hb3 x hx, Bool.and_self]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => exact False.elim (hnot (simple_const D p false))
    | [a], _ =>
      exfalso; apply hnot
      simpa [GateOp.eval] using wire_simple_all hlenD hpref a
    | [a, b], _ =>
      refine ⟨rfl, ?_⟩
      have ha := wire_simple_all hlenD hpref a
      have hb := wire_simple_all hlenD hpref b
      dsimp only [Simple] at ha hb
      rcases ha with ha1 | ha2 | ha3
      · rcases hb with hb1 | hb2 | hb3
        · exfalso; apply hnot; left; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha1 x hx, hb1 x hx]
        · refine ⟨⟨.or, [a]⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [hb2 x hx, hxp, Bool.or_false]
        · refine ⟨⟨.and, []⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [hb3 x hx, hxp, Bool.not_false, Bool.or_true]
      · rcases hb with hb1 | hb2 | hb3
        · refine ⟨⟨.or, [b]⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha2 x hx, hxp, Bool.false_or]
        · exfalso; apply hnot; right; left; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha2 x hx, hb2 x hx, Bool.or_self]
        · exfalso; apply hnot; left; intro x hx
          have hx' := hD x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha2 x hx, hb3 x hx, ha2 _ hx', hb3 _ hx']
          cases x.getD p false <;> cases (x.set p false).getD p false <;> rfl
      · rcases hb with hb1 | hb2 | hb3
        · refine ⟨⟨.and, []⟩, by simp, rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha3 x hx, hxp, Bool.not_false, Bool.true_or]
        · exfalso; apply hnot; left; intro x hx
          have hx' := hD x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha3 x hx, hb2 x hx, ha3 _ hx', hb2 _ hx']
          cases x.getD p false <;> cases (x.set p false).getD p false <;> rfl
        · exfalso; apply hnot; right; right; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha3 x hx, hb3 x hx, Bool.or_self]
    | _ :: _ :: _ :: _, h => simp at h

private lemma elim_aux (D : List Bool → Prop) (p : ℕ)
    (hlenD : ∀ x, D x → x.length = 8)
    (hD : ∀ x, D x → D (x.set p false))
    (suff : List Gate) (pref : List Gate) (o : ℕ)
    (hb : Basis suff)
    (hpref : ∀ w < 8 + pref.length, Simple D p (fun x => (Circuit.wires ⟨pref, 0⟩ x).getD w false))
    (hnot : ¬ Simple D p (fun x => (Circuit.wires ⟨pref ++ suff, 0⟩ x).getD o false)) :
    ∃ suff' : List Gate, Basis suff' ∧ cost suff' < cost suff ∧
      ∀ x, D x → x.getD p false = false →
        Circuit.wires ⟨pref ++ suff', 0⟩ x = Circuit.wires ⟨pref ++ suff, 0⟩ x := by
  induction suff generalizing pref with
  | nil =>
    exfalso
    apply hnot
    simpa using wire_simple_all hlenD hpref o
  | cons g rest ih =>
    have hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      hb g List.mem_cons_self
    have hrest : Basis rest := fun g' hg' => hb g' (List.mem_cons_of_mem _ hg')
    by_cases hgs : Simple D p (fun x => g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false))
    · have hpref' : ∀ w < 8 + (pref ++ [g]).length,
          Simple D p (fun x => (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD w false) := by
        intro w hw
        have hlen1 : (pref ++ [g]).length = pref.length + 1 := by simp
        by_cases hlt : w < 8 + pref.length
        · have heq : ∀ x, D x → (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD w false =
              (Circuit.wires ⟨pref, 0⟩ x).getD w false := fun x hx =>
            wires_cons_getD_lt pref g x w (by rw [hlenD x hx]; omega)
          have hwS := hpref w hlt
          dsimp only [Simple] at hwS
          rcases hwS with h1 | h2 | h3
          · exact Or.inl (fun x hx => by dsimp only; rw [heq x hx, heq _ (hD x hx), h1 x hx])
          · exact Or.inr (Or.inl (fun x hx => by dsimp only; rw [heq x hx, h2 x hx]))
          · exact Or.inr (Or.inr (fun x hx => by dsimp only; rw [heq x hx, h3 x hx]))
        · have hweq : w = 8 + pref.length := by omega
          subst hweq
          have heq : ∀ x, D x → (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD (8 + pref.length) false =
              g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false) := fun x hx => by
            have := wires_cons_getD_eq pref g x
            rwa [hlenD x hx] at this
          dsimp only [Simple] at hgs
          rcases hgs with h1 | h2 | h3
          · exact Or.inl (fun x hx => by dsimp only; rw [heq x hx, heq _ (hD x hx), h1 x hx])
          · exact Or.inr (Or.inl (fun x hx => by dsimp only; rw [heq x hx, h2 x hx]))
          · exact Or.inr (Or.inr (fun x hx => by dsimp only; rw [heq x hx, h3 x hx]))
      have hnot' : ¬ Simple D p (fun x => (Circuit.wires ⟨(pref ++ [g]) ++ rest, 0⟩ x).getD o false) := by
        simpa [List.append_assoc] using hnot
      obtain ⟨rest', hbr', hcr', hwr'⟩ := ih (pref ++ [g]) hrest hpref' hnot'
      refine ⟨g :: rest', ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hg
        · exact hbr' x hx'
      · unfold cost at hcr' ⊢
        simp only [List.countP_cons]
        cases isBin g <;> simp <;> omega
      · intro x hx hxp
        simpa [List.append_assoc] using hwr' x hx hxp
    · obtain ⟨hbin, g', hg', hbin', hgeval⟩ := gate_non_simple hlenD hD hg hpref hgs
      refine ⟨g' :: rest, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hg'
        · exact hrest x hx'
      · unfold cost
        simp only [List.countP_cons, hbin, hbin']
        simp
      · intro x hx hxp
        have hstep : Circuit.wires ⟨pref ++ [g'], 0⟩ x = Circuit.wires ⟨pref ++ [g], 0⟩ x := by
          rw [wires_append_singleton, wires_append_singleton, hgeval x hx hxp]
        have h1 : pref ++ (g' :: rest) = (pref ++ [g']) ++ rest := by simp
        have h2 : pref ++ (g :: rest) = (pref ++ [g]) ++ rest := by simp
        calc Circuit.wires ⟨pref ++ (g' :: rest), 0⟩ x
            = Circuit.wires ⟨rest, 0⟩ (Circuit.wires ⟨pref ++ [g'], 0⟩ x) := by
                rw [h1]; exact wires_append (pref ++ [g']) rest x
          _ = Circuit.wires ⟨rest, 0⟩ (Circuit.wires ⟨pref ++ [g], 0⟩ x) := by rw [hstep]
          _ = Circuit.wires ⟨pref ++ (g :: rest), 0⟩ x := by
                rw [h2]; exact (wires_append (pref ++ [g]) rest x).symm

private lemma elim_step (D : List Bool → Prop) (p : ℕ)
    (hlenD : ∀ x, D x → x.length = 8)
    (hD : ∀ x, D x → D (x.set p false))
    (gs : List Gate) (o : ℕ) (hb : Basis gs)
    (hnot : ¬ Simple D p (fun x => Circuit.eval ⟨gs, o⟩ x)) :
    ∃ gs' : List Gate, Basis gs' ∧ cost gs' < cost gs ∧
      ∀ x, D x → x.getD p false = false →
        Circuit.eval ⟨gs', o⟩ x = Circuit.eval ⟨gs, o⟩ x := by
  have hpref : ∀ w < 8 + ([] : List Gate).length,
      Simple D p (fun x => (Circuit.wires ⟨[], 0⟩ x).getD w false) := by
    intro w _
    by_cases hwp : w = p
    · subst hwp
      exact Or.inr (Or.inl (fun _ _ => rfl))
    · left
      intro x _
      simp [Circuit.wires, List.getD, List.getElem?_set_ne (Ne.symm hwp)]
  have hnot' : ¬ Simple D p (fun x => (Circuit.wires ⟨[] ++ gs, 0⟩ x).getD o false) := hnot
  obtain ⟨gs', hb', hc', hw'⟩ := elim_aux D p hlenD hD gs [] o hb hpref hnot'
  refine ⟨gs', hb', hc', fun x hx hxp => ?_⟩
  change (Circuit.wires ⟨[] ++ gs', 0⟩ x).getD o false = (Circuit.wires ⟨[] ++ gs, 0⟩ x).getD o false
  rw [hw' x hx hxp]

private def listed : List Nat := [0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7]
private def targetList (xs : List Bool) : Bool :=
  decide (∃ i < listed.length / 2,
    xs.getD (listed.getD (2 * i) 0) false = true ∧
    xs.getD (listed.getD (2 * i + 1) 0) false = true)

private def graphF (x : Fin 8 → Bool) := targetList (List.ofFn x)
private lemma target_eq_list (x : Fin 8 → Bool) : graphF x = targetList (List.ofFn x) := rfl
private lemma ofFn_fin8 (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by simp [List.ofFn_succ]
private def explicit : List Gate := [⟨.or, [3, 5]⟩, ⟨.or, [8, 6]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [3, 11]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [14, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [18, 19]⟩]
private lemma explicitLegal : ∀g∈explicit,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
  intro g hg
  simp only [explicit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma explicitOutput (x : Fin 8 → Bool) : Circuit.eval ⟨explicit,20⟩ (List.ofFn x) = graphF x := by
  rw [target_eq_list, ofFn_fin8 x]
  have eq : ∀ a b c d e f g h : Bool,
      Circuit.eval ⟨explicit,20⟩ [a,b,c,d,e,f,g,h] = targetList [a,b,c,d,e,f,g,h] := by decide +kernel
  exact eq _ _ _ _ _ _ _ _

private def D0 (x : List Bool) : Prop := x.length = 8
private def D1 (x : List Bool) : Prop := D0 x ∧ x.getD 2 false = false

private lemma not_simple_D0 (f : List Bool → Bool) (hf : ∀ x, D0 x → f x = targetList x) :
    ¬ Simple D0 2 f := by
  rintro (h1 | h2 | h3)
  · have h := h1 [false, false, true, false, false, false, true, false] rfl
    rw [hf [false, false, true, false, false, false, true, false] rfl, hf ([false, false, true, false, false, false, true, false].set 2 false) rfl] at h
    exact absurd h (by decide +kernel)
  · have h := h2 [true, false, false, true, false, false, false, false] rfl
    rw [hf [true, false, false, true, false, false, false, false] rfl] at h
    exact absurd h (by decide +kernel)
  · have h := h3 [false, false, false, false, false, false, false, false] rfl
    rw [hf [false, false, false, false, false, false, false, false] rfl] at h
    exact absurd h (by decide +kernel)

private lemma not_simple_D1 (f : List Bool → Bool) (hf : ∀ x, D1 x → f x = targetList x) :
    ¬ Simple D1 5 f := by
  rintro (h1 | h2 | h3)
  · have h := h1 [true, false, false, false, false, true, false, false] ⟨rfl, rfl⟩
    rw [hf [true, false, false, false, false, true, false, false] ⟨rfl, rfl⟩, hf ([true, false, false, false, false, true, false, false].set 5 false) ⟨rfl, rfl⟩] at h
    exact absurd h (by decide +kernel)
  · have h := h2 [true, false, false, true, false, false, false, false] ⟨rfl, rfl⟩
    rw [hf [true, false, false, true, false, false, false, false] ⟨rfl, rfl⟩] at h
    exact absurd h (by decide +kernel)
  · have h := h3 [false, false, false, false, false, false, false, false] ⟨rfl, rfl⟩
    rw [hf [false, false, false, false, false, false, false, false] ⟨rfl, rfl⟩] at h
    exact absurd h (by decide +kernel)
private theorem eval_on_D0 {gs : List Gate} {o : ℕ}
    (hv : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = graphF x)
    (x : List Bool) (hx : D0 x) :
    Circuit.eval ⟨gs, o⟩ x = targetList x := by
  have hlen : x.length = 8 := hx
  let f : Fin 8 → Bool := fun j => x.getD j.val false
  have hof : List.ofFn f = x := by
    apply List.ext_getElem (by simp [hlen])
    intro i hi1 hi2
    simp only [List.getElem_ofFn, f, List.getD, List.getElem?_eq_getElem hi2, Option.getD_some]
  have := hv f
  rw [hof, target_eq_list, hof] at this
  exact this

private def samples : List Q := [restrictWord domain111 raw1, restrictWord domain111 raw0, 0, restrictWord domain111 raw3, restrictWord domain111 raw2, 0, restrictWord domain111 raw5, restrictWord domain111 raw6]
private def bits (i : Fin 64) := samples.map (readQ i)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem sampleCorrect (i : Fin 64) : targetList (bits i) = goal111.getLsbD i.val :=
  by decide +revert +kernel

private theorem gateLower {gs : List Gate} (hb : Basis gs) {o : ℕ}
    (hv : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = graphF x) : 12 ≤ cost gs := by
  by_contra small
  have h0 : ∀ x, D0 x → Circuit.eval ⟨gs,o⟩ x = targetList x := eval_on_D0 hv
  have hd0 : ∀ x, D0 x → D0 (x.set 2 false) := fun x hx => by simpa [D0] using hx
  obtain ⟨gs1, hb1, hc1, he1⟩ := elim_step D0 2 (fun _ h => h) hd0 gs o hb (not_simple_D0 _ h0)
  have h1 : ∀ x, D1 x → Circuit.eval ⟨gs1,o⟩ x = targetList x := fun x hx =>
    (he1 x hx.1 hx.2).trans (h0 x hx.1)
  have hd1 : ∀ x, D1 x → D1 (x.set 5 false) := fun x hx => by
    refine ⟨?_, ?_⟩
    · simpa only [D0, List.length_set] using hx.1
    · simpa [List.getD, List.getElem?_set_ne] using hx.2
  obtain ⟨gs2, hb2, hc2, he2⟩ := elim_step D1 5 (fun _ h => h.1) hd1 gs1 o hb1 (not_simple_D1 _ h1)
  have one (i : Fin 64) : Circuit.eval ⟨gs2,o⟩ (bits i) = goal111.getLsbD i.val := by
    have hd : D1 (bits i) := ⟨rfl, read_zero i⟩
    have h5 : (bits i).getD 5 false = false := read_zero i
    exact (he2 _ hd h5).trans ((h1 _ hd).trans (sampleCorrect i))
  have output : (wireQs gs2 samples).getD o 0 = goal111 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have h := one ⟨j,hj⟩
    change (Circuit.wires ⟨gs2,0⟩ (samples.map (readQ ⟨j,hj⟩))).getD o false = _ at h
    rw [read_wireQs _ _ _ hb2,getD_table] at h
    exact h
  obtain ⟨s,sub,tr⟩ := trail_extract samples hb2 o
  rw [output, show norm goal111 = goal111 by decide +kernel] at tr
  have zero := trailNoZero tr (by decide +kernel)
  have init : avail samples = insert 0 sources111.toFinset := by decide +kernel
  rw [init] at sub
  have feasible := realizeTrail tr sources111.toFinset (fun w hw =>
    (Finset.mem_insert.mp (sub hw)).resolve_left (fun e => zero (e ▸ hw)))
  exact lower111 (constructLift (by omega) feasible)

end PEqualNP.Outside.L_meta_14802

open PEqualNP.Outside.L_meta_14802

theorem PEqualNP.Outside.L_meta_14802 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ computes
  by_cases used : ∃ g ∈ gs, g.op = GateOp.not
  · have basis : Basis gs := by
      intro g hg
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using legal g hg
    refine ⟨explicit, 20, explicitLegal, ?_, explicitOutput⟩
    change 13 ≤ gs.length
    have binary := gateLower basis computes
    have fewer := cost_lt used
    omega
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    exact ⟨hop.imp_right (fun h => h.resolve_right (fun n => used ⟨g,hg,n⟩)), hlen⟩
