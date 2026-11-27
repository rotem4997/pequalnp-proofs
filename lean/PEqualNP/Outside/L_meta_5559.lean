import Mathlib
import PEqualNP.Defs

-- Live-wire extraction adapted from Outside L_meta_3977.
namespace PEqualNP.Outside.L_meta_5559

open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | 0, t, S => t = 0 ∧ S = {target} ∧ proper target
  | k+1, t, S => ∃ (U : Finset Sig) (a b : Sig) (d : Bool),
      S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live target k t (insert (bin d a b) U)

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,rfl,hp⟩ := h
    simpa using hp
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,ha,hb,_,_,ht⟩ := h
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun v hv => ih ht v (Finset.mem_insert_of_mem hv)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,rfl,_⟩ := h
    simp
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,_,_,_,hf,ht⟩ := h
    have sc := ih ht
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at sc
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


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
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
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
  exact Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  cases l with
  | nil =>
    rcases ho with rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨k+1,t,insert a (insert b U),Nat.le_refl _,⟨U,a,b,d,rfl,pa,pb,hab,hf,ht⟩,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,⟨rfl,rfl,hp⟩,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]
abbrev Row := Fin 128
theorem mono_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,rfl,_⟩ := h
    exact ⟨_,by simp,pos,negRow⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,rfl,_,_,_,_,ht⟩ := h
    obtain ⟨v,hv,hp,hn⟩ := ih ht
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]
def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]
theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a.toNat < b.toNat → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).Nodup → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by

  classical
  have usePair (k t : Nat) (U : Finset Sig) (a b : Sig) (d : Bool)
      (he : ws.toFinset = insert a (insert b U)) (lt : a.toNat < b.toNat)
      (hf : bin d a b ∉ insert a (insert b U))
      (tail : Live T k t (insert (bin d a b) U)) (hk : k+1 ≤ cap) : False := by
    have hab : a ≠ b := fun heq => (ne_of_lt lt) (congrArg BitVec.toNat heq)
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb lt fresh hz nd len k t (by omega) (eq.symm ▸ tail)

  intro k t hk h
  cases k with
  | zero =>
    obtain ⟨_,he,_⟩ := h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | succ k =>
    obtain ⟨U,a,b,d,he,_,_,hab,hf,tail⟩ := h
    rcases lt_or_gt_of_ne (fun e => hab (BitVec.eq_of_toNat_eq e)) with lt | lt
    · exact usePair k t U a b d he lt hf tail hk
    · rw [Finset.insert_comm a b] at he hf
      rw [bin_comm d a b] at hf tail
      exact usePair k t U b a d he lt hf tail hk

-- Each sampled column packs sixty-four ordered pairs of promise rows.
-- A live bank must distinguish every positive row from its paired negative.
def goal : Sig := 0xffffffffffffffff
def hits (x : Sig) : BitVec 64 := (x.setWidth 64) &&& ~~~((x >>> 64).setWidth 64)
def cover : List Sig → BitVec 64
  | [] => 0
  | x :: xs => hits x ||| cover xs

theorem cover_mem {w : Sig} {ws : List Sig} (hw : w ∈ ws) (i : ℕ)
    (h : (hits w).getLsbD i = true) : (cover ws).getLsbD i = true := by
  induction ws with
  | nil => simp at hw
  | cons a ws ih =>
    simp only [cover, BitVec.getLsbD_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | hm
    · exact Or.inl h
    · exact Or.inr (ih hm)

theorem goal_bits : ∀ j : Fin 64, bit (⟨j, by omega⟩ : Row) goal = true ∧
    bit (⟨64+j.val, by omega⟩ : Row) goal = false := by decide

theorem necessary {k t ws} (h : Live goal k t (List.toFinset ws)) :
    cover ws = BitVec.allOnes 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨hp,hn⟩ := goal_bits ⟨i,hi⟩
  obtain ⟨w,hw,hw1,hw2⟩ := mono_row_difference h hp hn
  change w.getLsbD i = true at hw1
  change w.getLsbD (64+i) = false at hw2
  simp only [BitVec.getLsbD_allOnes, hi, decide_true]
  apply cover_mem (List.mem_toFinset.mp hw)
  simp [hits,hi,hw1,hw2]

def opts := [false,true]
theorem opt (b : Bool) : b ∈ opts := by cases b <;> decide

def stepOK (ws : List Sig) (n : ℕ) (f : List Sig → Bool) : Bool :=
  ws.all fun a => ws.all fun b =>
    if a.toNat < b.toNat then opts.all fun d =>
      let c := bin d a b
      if c = zero ∨ c = one ∨ c ∈ ws then true else
      opts.all fun ka => opts.all fun kb =>
        let child := childTwo ws a b d ka kb
        if child.length ≤ n then f child else true
    else true

def dead : ℕ → List Sig → Bool
  | 0, ws => !ws.contains goal
  | k+1, ws => if cover ws != BitVec.allOnes 64 then true else
      !ws.contains goal && stepOK ws (k+1) (dead k)

theorem dead_ok (k : ℕ) (ws : List Sig) (nd : ws.Nodup) (hd : dead k ws = true) :
    Impossible goal k ws.toFinset := by
  induction k generalizing ws with
  | zero =>
    have ho : goal ∉ ws := by simpa [dead] using hd
    intro k t hk h
    have hz : k = 0 := by omega
    subst k
    obtain ⟨_,he,_⟩ := h
    exact ho (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | succ k ih =>
    by_cases hc : cover ws = BitVec.allOnes 64
    · have ok : (!ws.contains goal) = true ∧ stepOK ws (k+1) (dead k) = true := by
        simpa only [dead, hc, bne_self_eq_false, Bool.false_eq_true, ite_false, Bool.and_eq_true] using hd
      apply enum_step nd (by simpa using ok.1)
      intro a ha b hb d ka kb lt fresh hp nd' len
      have s1 := List.all_eq_true.mp ok.2 a ha
      have s2 := List.all_eq_true.mp s1 b hb
      simp only [lt, ↓reduceIte] at s2
      have s3 := List.all_eq_true.mp s2 d (opt d)
      simp only [hp.1,hp.2,fresh,or_self,↓reduceIte] at s3
      have s4 := List.all_eq_true.mp (List.all_eq_true.mp s3 ka (opt ka)) kb (opt kb)
      simp only [len,↓reduceIte] at s4
      exact ih _ nd' s4
    · intro l t hl run
      exact hc (necessary run)

def roots : List Sig := [0x80402010080402018000000007ffffff, 0x180c06030180c0600001ffff8000000, 0xe070381c0e07038003fe00000000000, 0x70381c0e070381c07fc0000000000000, 0x80c06030180c06037fffe00000000000, 0x12090482412090488000000ff80001ff, 0x241209048241209000001ff00003fe00, 0x49249249249249240000000007fc0000]
def rowCode (r : Row) := ((0xfedba9740fedba9740fedba9740fedba9740fedba9740fedba9740fedba97401ccccccccc888888888666666666555555555333333333222222222111111111 : ℕ) >>> (4*r.val)) % 16
def rowL (r : Row) : Fin 4 := ⟨rowCode r / 4, by unfold rowCode; omega⟩
def rowR (r : Row) : Fin 4 := ⟨rowCode r % 4, by omega⟩
theorem rows_ok : ∀ r : Row, roots.map (bit r) = PEqualNP.Represents.oneEach (rowL r) (rowR r) := by
  decide +kernel
theorem target_ok : ∀ r : Row, bit r goal = (4462 : ℕ).testBit (4*(rowL r).val+(rowR r).val) := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem checked : roots.sublists.all (dead 7) = true := by decide +kernel

open PEqualNP.Represents
theorem lower : ¬RepSizeAtMost (fun u v : Fin 4 => (4462 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  rintro ⟨C, legal, small, computes⟩
  have eq0 : (execute C.gates roots).getD C.output zero = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r _ = bit r _
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1), rows_ok r, target_ok]
    exact computes _ _
  have H := get_rep (execute C.gates roots) C.output
  rw [eq0] at H
  have hp : proper goal := by unfold proper; decide
  obtain ⟨k,t,S,hk,run,sub⟩ := extract C.gates roots legal hp (H.resolve_right (fun hn => hn hp))
  let ws := roots.filter (fun x => decide (x ∈ S))
  have hsub : ws.Sublist roots := List.filter_sublist
  have nd : roots.Nodup := by decide
  have he : ws.toFinset = S := by
    ext x
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨sub x h,h⟩⟩
  have hc := List.all_eq_true.mp checked ws (List.mem_sublists.mpr hsub)
  have sz : C.gates.length ≤ 7 := small
  exact dead_ok _ _ (nd.sublist hsub) hc k t (by omega) (he.symm ▸ run)

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (4462 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [13, 4]⟩, ⟨GateOp.or, [12, 14]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_5559

theorem PEqualNP.Outside.L_meta_5559 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4462 : ℕ).testBit (4 * u.val + v.val)) 8 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4462 : ℕ).testBit (4 * u.val + v.val)) 7 :=
  ⟨PEqualNP.Outside.L_meta_5559.upper, PEqualNP.Outside.L_meta_5559.lower⟩
