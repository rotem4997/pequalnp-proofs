import PEqualNP.Defs

-- The 8-input lower bound (namespace Foundation) is copied from merged L_meta_8449 (its own credit lines follow).
-- The Transfer section (identify two vertices, relabel, decide) and the overall layout are copied from merged L_meta_9435.
-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_8449.
-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.
-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_10446
namespace Foundation
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xffffffffffffffffffffffffffeaeae8fffefefcfffafaf8ffeeeeecffeaeae8ffffffffffffffffffffffffffeaeae8fffefefcfffafaf8ffeeeeecffeaeae8
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4) || (x 5 && x 7) || (x 6 && x 7)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
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
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 4) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 4) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))


def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
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
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem pieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

structure KWRooms (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

def kwLeaf (T : Sig) : KWRooms {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩

def kwFork {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem kwTight {T k S} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨kwLeaf T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := kwWidth tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have ha : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have hb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
    exact ⟨kwFork d01 ha hb fresh H⟩

def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v

theorem kwOwn {S T v p n} (H : KWRooms S T) (one : onlyWire S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw

theorem kwCross {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : Impossible false T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := kwTight run tight
  exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)

def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def kwWord (pos neg : Nat) (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let field := fun i => (value >>> (4*i)) &&& 15
  let a := ws.getD (field 0) zero
  let b := ws.getD (field 1) zero
  let p := kwProbe pos (field 2)
  let n := kwProbe neg (field 3)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB ws T a p (kwProbe neg (field 4)) && kwWireB ws T b p (kwProbe neg (field 5)) &&
    kwWireB ws T a (kwProbe pos (field 6)) n && kwWireB ws T b (kwProbe pos (field 7)) n
theorem kwWord_sound {pos neg T ws k v} (h : kwWord pos neg T ws k v=true) : Impossible false T k ws.toFinset := by
  simp only [kwWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact kwCross h.1.1.1.1.1 h.1.1.1.1.2 (kwWireB_sound h.1.1.1.2)
    (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2)

def CutRow (g : Forest) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → nodeVerified g k j=true ∨ Impossible g.mode (targetOf g) k (stateSet g k j).toFinset
theorem mixedEmpty (g : Forest) (k a : Nat) : CutRow g k a 0 := by
  intro j lo hi
  omega
theorem checkedRow {g k a n} (h : block g k a n=true) : CutRow g k a n :=
  fun j lo hi => Or.inl (block_at h j lo hi)
theorem joinRow {g k a x y} (first : CutRow g k a x) (last : CutRow g k (a+x) y) :
    CutRow g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def kwTest (pos neg : Nat) (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all (fun j => kwWord pos neg (targetOf g) (stateSet g k (a+j)) k (packedAt data (32*j) 32))
theorem mixedCut {pos neg g k a n data} (mode : g.mode=false) (h : kwTest pos neg g k a n data=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change kwWord pos neg _ (stateSet g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact kwWord_sound hh

def mixedTables (g : Forest) (top : Nat) := ∀ k ≤ top, CutRow g k 0 (g.levels k).1
theorem mixedForest (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : mixedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem mixedRoot {g top prior k i ws} (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : mixedTables g top) (le : k≤top)
    (idx : indexedRoot g k i ws=true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact mixedForest g top prior lower geom blocks _ le i idx.1

def eightInputs : List Sig := vars 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
def eightEdge (x : Fin 8 → Bool) := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4) || (x 5 && x 7) || (x 6 && x 7)

theorem eightTable : ∀ r : Row, bit r graph = eightEdge (sampleEight r) := by decide +kernel
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [← eightList, List.map_ofFn]
  rfl

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [← b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl
def neighbor8449 (i : Fin 8) : Nat := [1,0,0,0,0,1,2,5].getD i.val 0
def absentRow8449 (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< neighbor8449 i)
def presentRow8449 (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor8449 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 8, bit (absentRow8449 i) graph ≠ bit (presentRow8449 i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (absentRow8449 i) (eightInputs.getD j.val zero) =
      bit (presentRow8449 i) (eightInputs.getD j.val zero)) := by decide +kernel


theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 8 C = eightEdge) (small : C.size ≤ 13) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 12 else 13) ∧ Live u graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((congrFun computes (sampleEight r)).trans (eightTable r).symm)
  have len : C.gates.length ≤ 13 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 12 else 13) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode

  have out := get_rep (u:=u) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates eightInputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←eightList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (absentRow8449 i) (presentRow8449 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 13 → ¬Live false graph k eightInputs.toFinset)
    (s : ∀ k, k ≤ 12 → ¬Live true graph k eightInputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 eightEdge 13 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run
def g7Y : Array (Bits × Bits) := #[(0x3ff63ff63ff63ff63ff63ff63ff63ff63ff63f,0x49204920492049204920492049204920492049),(0xc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7,0x92409240924092409240924092409240924092),(0xf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8,0x24812481248124812481248124812481248124),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g7C : List ColumnInfo := []
def g7A : List (List Nat) := [[],[33],[16],[16,32],[32,16],[32]]
def g7D3 (j : Nat) : Nat := 0x7
def g7L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g7D3)
  | _ => emptyPacking
def g7I (_ _ : Nat) : Option (Nat × Nat) := none
def g7 : Forest := ⟨7,3,fun i => g7Y[i]?.getD (0,0),g7C,g7A,g7L,g7I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7P3_0 : block g7 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g7B3 : block g7 3 0 1=true := g7P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7T : checkedTables g7 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g7 0 0 0 = true)
  · exact (rfl : block g7 1 0 0 = true)
  · exact (rfl : block g7 2 0 0 = true)
  · exact g7B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7G : graphValid g7 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low7 : Lower true (varsX 7) (graphGoal 7) 4 := lower_forest (g:=g7) (i:=0) (hints:=1) (before_sound [] baseKnown) g7G g7T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K7 := extendKnown [] 4 [(7,[]),(25,[49,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V7 : Known true K7 := extend_ok (m:=7) baseKnown low7 (by decide +kernel)
def g15Y : Array (Bits × Bits) := #[(0xfd587fff83fffff3fab0ffff07ffffe7f561ff,0x9241082080200001248210410040000249),(0x3baf81fffc0fc7fc775f03fff81f8ff8eebe07,0x818d249212411241031a492424822482063492),(0xc6b78e3ffff007ff8d6f1c7fffe00fff1ade38,0x16324924208a24802c6492484114490058c924),(0x64c703ffffff8000c98e07ffffff0001931c0,0x264f6db8430c070a4c9edb7086180e14993db6),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g15C : List ColumnInfo := [(8,0,7,0,4)]
def g15A : List (List Nat) := [[],[33]]
def g15D4 (j : Nat) : Nat := 0x1f
def g15L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g15D4)
  | _ => emptyPacking
def g15I (_ _ : Nat) : Option (Nat × Nat) := none
def g15 : Forest := ⟨15,4,fun i => g15Y[i]?.getD (0,0),g15C,g15A,g15L,g15I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15P4_0 : block g15 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g15B4 : block g15 4 0 1=true := g15P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15T : checkedTables g15 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact (rfl : block g15 3 0 0 = true)
  · exact g15B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15G : graphValid g15 (boundsBefore K7) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (varsX 15) (graphGoal 15) 5 := lower_forest (g:=g15) (i:=0) (hints:=1) (before_sound K7 V7) g15G g15T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K15 := extendKnown K7 5 [(15,[]),(23,[67]),(27,[49,66]),(29,[49,66,33]),(39,[16,83,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V15 : Known true K15 := extend_ok (m:=15) V7 low15 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[(0xe7ce3fff03ffe3ffe7ce3fff03ffe3ffe7ce3f,0x5489242882049100548924288204910054892),(0xff33c7fffc0ffff8ff33c7fffc0ffff8ff33c7,0x2324914114280220232491411428022023249),(0x0,0x0),(0xaec38fffff003ff0aec38fffff003ff0aec38,0x4aa56d98218b12404aa56d98218b12404aa56d),(0x0,0x0),(0x193dc0fffffffc00193dc0fffffffc00193dc0,0x990db6e0c20c0384990db6e0c20c0384990db6),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := []
def g43A : List (List Nat) := [[],[16,83]]
def g43D3 (j : Nat) : Nat := 0xf
def g43L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g43D3)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,3,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P3_0 : block g43 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B3 : block g43 3 0 1=true := g43P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact g43B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K15) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=1048577) (before_sound K15 V15) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K15 4 [(43,[]),(51,[67]),(77,[33,101]),(85,[33,67,101]),(102,[16,32,83,67,100]),(163,[16,80,48,67,116,100]),(166,[16,80,32,50,67,116,100]),(197,[32,97,16,48,67,117]),(198,[32,97,49,67,117]),(226,[80,113,32,49,66,100,67]),(228,[96,113,32,50,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V15 low43 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[(0x7fe01fffffffe01fffffffe3fc9594400fffff,0x404020100040402010004000000002108421),(0x7fffe00ff87fffe00ff87ffc3f436d41f0001f,0x248492412124888a4421248082032d54a5294a),(0x7ffffff0007ffffff0007fffc3da7081f003e0,0x4909048a424911108942490009d850a94a5294),(0x80000000007fffffffff8000007f0bbe007c00,0xe0e0703840e020301800e091057038c6318c6),(0xffffffffff8000000000000003289bfe0f8000,0x7010180c00701c1c0e047012232898718c6318),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(2,0,29,0,5),(4,0,27,0,5),(8,0,23,0,5),(16,0,15,0,5),(6,0,25,0,4),(24,0,7,0,4)]
def g31A : List (List Nat) := [[],[67],[33],[33,67],[49,66],[49,66,33],[65,50,33],[65,50]]
def g31D4 (j : Nat) : Nat := 0x31826d62141318fd91538426f6254d10
def g31D5 (j : Nat) : Nat := 0x310402003040184208228851040db4e6c278b10910c02fea098df14131bfa9c217d53842fea6885f54d10f7a9221f531443ec20885bd4910
def g31H5 (j : Nat) : Nat := 0x30050000000000000000000001040000003c80000004880000000000000
def g31D6 (j : Nat) : Nat := 0x5408c9033240e4480fd31fe10fd10
def g31H6 (j : Nat) : Nat := 0x65ec4800909c480048390e202c0800b110180b00000061400295528003e1082700c
def g31D7 (j : Nat) : Nat := 0x1605f
def g31H7 (j : Nat) : Nat := 0x932c3d5f90000322e00000391b8000009cc2007045310
def g31L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g31D4)
  | 5 => (10,2,3,0,0,7,0,g31D5)
  | 6 => (3,1,3,0,0,6,0,g31D6)
  | 7 => (1,0,3,0,0,0,0,g31D7)
  | _ => emptyPacking
def g31I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 29 0 9 2 3 g31H5
  | 6 => lookupWord 4 23 4 11 4 3 g31H6
  | 7 => lookupWord 3 19 3 9 2 3 g31H7
  | _ => fun _ => none
def g31 : Forest := ⟨31,7,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P4_0 : block g31 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B4 : block g31 4 0 3=true := g31P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_1 : block g31 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B5 : block g31 5 0 10=true := (@block_merge g31 5 0 1 9 g31P5_0 g31P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P6_0 : block g31 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B6 : block g31 6 0 3=true := g31P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P7_0 : block g31 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B7 : block g31 7 0 1=true := g31P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact g31B4
  · exact g31B5
  · exact g31B6
  · exact g31B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 8 := lower_forest (g:=g31) (i:=0) (hints:=1) (before_sound K43 V43) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K43 8 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V43 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[(0x7ffffc07ff801ffffffffff01fff9eda2d81ff,0x40081081084208410010204000024209a492),(0x801fffffffffe003ff80ffffe03ff925d3fe07,0x4809000120080900202024000805805801249),(0xffe00007fffffffc0000ffffffc007abb20e38,0x491521a524511422942ca4850a1505a8324924),(0x7ffffffffffff0000000009d4fc01c0,0x6e19c2c6386218c31848c70993260994f45b6d),(0x0,0x0),(0xfffffff800000000000000000000675462f000,0x701e0307c07c1f03e070f80e1c38275062edb6),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(8,0,39,0,5)]
def g47A : List (List Nat) := [[],[16,83]]
def g47D5 (j : Nat) : Nat := 0x3f
def g47L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g47D5)
  | _ => emptyPacking
def g47I (_ _ : Nat) : Option (Nat × Nat) := none
def g47 : Forest := ⟨47,5,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5_0 : block g47 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B5 : block g47 5 0 1=true := g47P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact (rfl : block g47 4 0 0 = true)
  · exact g47B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 6 := lower_forest (g:=g47) (i:=0) (hints:=1048577) (before_sound K31 V31) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K31 6 [(47,[]),(55,[67]),(79,[33,101]),(87,[33,67,101]),(103,[16,32,83,67,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[(0xe00ffffe1ffc01ffc3fffffffcb25ce6007fff,0x48201004440884408882020800121046421084),(0xfff007fffffffe0003ff0ffc3f81ab960f801f,0x8242a0a801500815101420908281a980318c63),(0x0,0x0),(0xfffff8001ffffffffc000fffc07dd919f003e0,0x80c23088611086011844200860c91894a529),(0x1ffffffffffff000004f27e9f07c00,0x130b04c111822118022008c1100d26a1294a52),(0xffffffffe000000000000000033aa61a0f8000,0x1c0c07001e03c1e023c08f02213a061bce739c),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,32,25,2,5),(32,0,27,0,5),(2,32,25,0,4),(8,0,51,0,4),(16,0,43,0,4)]
def g59A : List (List Nat) := [[],[67]]
def g59D4 (j : Nat) : Nat := 0x57d4d20
def g59D5 (j : Nat) : Nat := 0x60880480e140fd32fe20fd20
def g59H5 (j : Nat) : Nat := 0xe
def g59D6 (j : Nat) : Nat := 0x18d09f
def g59H6 (j : Nat) : Nat := 0xc200500da000000160200
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (3,1,3,0,0,5,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g59H5
  | 6 => lookupWord 1 13 0 7 2 1 g59H6
  | _ => fun _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B4 : block g59 4 0 1=true := g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : block g59 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 3=true := g59P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 1=true := g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact g59B4
  · exact g59B5
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=1048577) (before_sound K47 V47) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K47 7 [(59,[]),(93,[33,101]),(167,[16,80,50,32,66,116,100]),(199,[32,97,48,65,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V47 low59 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[(0xfffffffffff001fffffc07fffffffb2e4300ff,0x2104208424214420840810910001210a435555),(0xff800ffffffffe003fffffff80ffd494f20f0f,0xa614829414a0945285145022648d414a08888),(0x0,0x0),(0xfffff001ffffffffc00007ffff003ead8500f0,0x4c498d31898c118631626624448c1ea584aaaa),(0x0,0x0),(0x1fffffffffffff800000027d3fcff00,0x700e01c00e00600801800038081023c1503333),(0x0,0x0),(0xfffffffe000000000000000000019d530df000,0x80700e01f00f81f03e0387c070e19c120dcccc),(0x0,0x0)]
def g171C : List ColumnInfo := []
def g171A : List (List Nat) := [[],[80,115]]
def g171D4 (j : Nat) : Nat := 0x1f
def g171L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g171D4)
  | _ => emptyPacking
def g171I (_ _ : Nat) : Option (Nat × Nat) := none
def g171 : Forest := ⟨171,4,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P4_0 : block g171 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B4 : block g171 4 0 1=true := g171P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact g171B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 5 := lower_forest (g:=g171) (i:=0) (hints:=1343225857) (before_sound K59 V59) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K59 5 [(171,[]),(179,[67]),(205,[33,101]),(227,[16,80,48,67,116,100]),(229,[32,97,16,48,67,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V59 low171 (by decide +kernel)
def g185Y : Array (Bits × Bits) := #[(0xfc00ffffffff003fffffffc3feea3a53000fff,0x8a220882222228882208888802201a13249249),(0x0,0x0),(0x0,0x0),(0xffff003fffffffc00ffffffc3ed0c5f603f03f,0x10449104444441124411110080d005c4492492),(0xffffffc00ffffffff003ffffc13eeca103ffc0,0x208822288888822088a22200090ee020924924),(0xffffffffffc0000012793dcfc0000,0xc0f03c0f00f00c0300c03c11112283d81c71c7),(0x0,0x0),(0xfffffffff000000000000000039d530dfc0000,0x300c0300f00f03c0f03c022229d5005e38e38),(0x0,0x0)]
def g185C : List ColumnInfo := [(0,32,25,128,5)]
def g185A : List (List Nat) := [[],[117],[67],[67,117],[48],[48,117],[48,64],[48,64,117],[64,48],[64,48,117],[64],[64,117]]
def g185D5 (j : Nat) : Nat := 0x3f
def g185L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g185D5)
  | _ => emptyPacking
def g185I (_ _ : Nat) : Option (Nat × Nat) := none
def g185 : Forest := ⟨185,5,fun i => g185Y[i]?.getD (0,0),g185C,g185A,g185L,g185I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185P5_0 : block g185 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g185B5 : block g185 5 0 1=true := g185P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185T : checkedTables g185 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g185 0 0 0 = true)
  · exact (rfl : block g185 1 0 0 = true)
  · exact (rfl : block g185 2 0 0 = true)
  · exact (rfl : block g185 3 0 0 = true)
  · exact (rfl : block g185 4 0 0 = true)
  · exact g185B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185G : graphValid g185 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low185 : Lower true (varsX 185) (graphGoal 185) 6 := lower_forest (g:=g185) (i:=0) (hints:=1349517315) (before_sound K171 V171) g185G g185T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K185 := extendKnown K171 6 [(185,[]),(217,[101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V185 : Known true K185 := extend_ok (m:=185) V171 low185 (by decide +kernel)
def g230Y : Array (Bits × Bits) := #[(0x0,0x0),(0xff803ff0fffff007ffff0fffffe47a840003ff,0x21488422212425120902248802603284a5294a),(0xffffc000fffffff803fffffc3f8189fc007c1f,0xa0121440a414824521408108180895918c631),(0x0,0x0),(0x0,0x0),(0xffffffff007ffffffc000fffc07dd9120f83e0,0x4c1209804c09804060584120080dc9025294a5),(0x7ffffffffff000004f27e9f07c00,0x701c0e08700e0180806001c1104f20a06318c6),(0xffffffffff80000000000000033aa61bff8000,0x8060300080700e0703808e02233006198c6318),(0x0,0x0)]
def g230C : List ColumnInfo := [(2,0,228,0,4),(4,0,226,0,4),(32,0,198,0,4),(64,0,166,0,4),(128,0,102,0,4)]
def g230A : List (List Nat) := [[],[82,118],[33,101],[33,97,81,117],[81,33,114,98],[81,114],[97,117],[97,114,82,81],[113,82,98,33],[113,98]]
def g230D4 (j : Nat) : Nat := 0x5dd4530
def g230D5 (j : Nat) : Nat := 0x41030fd30fd10
def g230H5 (j : Nat) : Nat := 0x5
def g230D6 (j : Nat) : Nat := 0x23440bf
def g230H6 (j : Nat) : Nat := 0xa0c316c1953a00000000222700decb0000c
def g230L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g230D4)
  | 5 => (2,1,3,0,0,3,0,g230D5)
  | 6 => (1,0,3,0,0,0,0,g230D6)
  | _ => emptyPacking
def g230I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g230H5
  | 6 => lookupWord 2 17 2 8 1 3 g230H6
  | _ => fun _ => none
def g230 : Forest := ⟨230,6,fun i => g230Y[i]?.getD (0,0),g230C,g230A,g230L,g230I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230P4_0 : block g230 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g230B4 : block g230 4 0 1=true := g230P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230P5_0 : block g230 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g230B5 : block g230 5 0 2=true := g230P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230P6_0 : block g230 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g230B6 : block g230 6 0 1=true := g230P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230T : checkedTables g230 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g230 0 0 0 = true)
  · exact (rfl : block g230 1 0 0 = true)
  · exact (rfl : block g230 2 0 0 = true)
  · exact (rfl : block g230 3 0 0 = true)
  · exact g230B4
  · exact g230B5
  · exact g230B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g230G : graphValid g230 (boundsBefore K185) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low230 : Lower true (varsX 230) (graphGoal 230) 7 := lower_forest (g:=g230) (i:=0) (hints:=1376780576) (before_sound K185 V185) g230G g230T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K230 := extendKnown K185 7 [(230,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V230 : Known true K230 := extend_ok (m:=230) V185 low230 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[(0xffffffffff801ffffec9512d124f58000fffff,0x100800040100400000c1000802045108421084),(0xfffc00ffffffe007ffb434d2ad82683ff0001f,0x21002009200001001301082288208c6318c63),(0xfffffffff80060a337b550b001f003e0,0xa4a0aca9241505415400a3359550a6318c6318),(0xffffff0000000000001b9e016ef8a7c0007c00,0xc0c108303821886218189c012c78225294a529),(0x22eaf858b787c00f8000,0x70230c1c0461184602262f0508384a5294a52),(0x19d26ecc071303e000000,0xf803c0fe00781e07808d266cc0713739ce739c),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(32,0,31,0,8)]
def g63A : List (List Nat) := [[],[67]]
def g63D8 (j : Nat) : Nat := 0x7f
def g63L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g63D8)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,8,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 1=true := g63P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact (rfl : block g63 5 0 0 = true)
  · exact (rfl : block g63 6 0 0 = true)
  · exact (rfl : block g63 7 0 0 = true)
  · exact g63B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K230) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 9 := lower_forest (g:=g63) (i:=0) (hints:=1048577) (before_sound K230 V230) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K230 9 [(63,[]),(95,[33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V230 low63 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[(0xfffffffffc000fffffffbfcea4644349000fff,0x21101084084421100440a082a4044248444444),(0xf0003ffffffff0003fff8a341e99a4fd0ff00f,0x420285009080820288080a0412880495222222),(0x3fffffffffffc00070417beeba22f0f0f0,0x8025002920090024009250400960b022111111),(0xffffc0000000000000000dcf9059dd32000f00,0x4462631c111c447111c0d4d10599d32bbbbbb),(0x0,0x0),(0x117a6d155cf40f0000,0x878383e021e087821e0117a6d155860dddddd),(0xcea977125e06f00000,0xf803fc003e00f803e008ea976124e04eeeeee),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(8,0,103,0,6),(32,0,79,0,6),(64,0,47,0,6),(0,64,43,4,5),(1,0,102,0,4),(1,8,102,0,4),(2,32,77,0,4),(4,64,43,0,4)]
def g111A : List (List Nat) := [[],[33,101],[16,83],[16,32,83,99],[32,16,99,83],[32,99]]
def g111D4 (j : Nat) : Nat := 0x49d7690630
def g111D5 (j : Nat) : Nat := 0x930c0afd8940b758630d754630e790630
def g111H5 (j : Nat) : Nat := 0x40
def g111D6 (j : Nat) : Nat := 0x1908328d50ac254a0742407f4437a81de30
def g111H6 (j : Nat) : Nat := 0x71000007100000110079800000000000000000000004280000000000000000000000000000000000000000a1000000000000000000000000180000030600
def g111D7 (j : Nat) : Nat := 0x3ea881bf
def g111H7 (j : Nat) : Nat := 0x630000025000000149b8134040000a44ab0e006200044
def g111L : Nat → Packing
  | 4 => (1,3,3,0,0,0,0,g111D4)
  | 5 => (4,2,3,0,0,5,0,g111D5)
  | 6 => (3,1,3,0,0,6,0,g111D6)
  | 7 => (1,0,3,0,0,0,0,g111D7)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g111H5
  | 6 => lookupWord 2 67 0 9 2 3 g111H6
  | 7 => lookupWord 3 19 3 9 2 3 g111H7
  | _ => fun _ => none
def g111 : Forest := ⟨111,7,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P4_0 : block g111 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B4 : block g111 4 0 1=true := g111P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5_0 : block g111 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B5 : block g111 5 0 4=true := g111P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_0 : block g111 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_2 : block g111 6 2 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B6 : block g111 6 0 3=true := (@block_merge g111 6 0 2 1 g111P6_0 g111P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 1=true := g111P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact g111B4
  · exact g111B5
  · exact g111B6
  · exact g111B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=34603009) (before_sound K63 V63) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K63 8 [(111,[]),(119,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V63 low111 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),(0xfffffffffffffff18df3c9d0ddd2000fff,0x102a1500485402210241057109401c9230c30c),(0xffffffffffffffff74086aaadf4d03f03f,0x154005490015440148c300862a8c1410c30c3),(0xffff000003fffff000098725f7ef20a5fc0000,0x22184618e118608220e18424f7ce0085555555),(0xfffffffffc000000000c6b77362576e0fc0000,0x4460986102618704470c6b5300217660aaaaaa),(0xc8adab5d9c21e000fc0,0x8780e07e0381f808780c8a8ab499c20ccf3cf3),(0x6754a985f269d03f000,0xf800ff8003fe000f800245429857269cf3cf3c),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(0,8,102,16,5)]
def g126A : List (List Nat) := [[],[67],[33,101],[33,67,101]]
def g126D5 (j : Nat) : Nat := 0x7f
def g126L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g126D5)
  | _ => emptyPacking
def g126I (_ _ : Nat) : Option (Nat × Nat) := none
def g126 : Forest := ⟨126,5,fun i => g126Y[i]?.getD (0,0),g126C,g126A,g126L,g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P5_0 : block g126 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B5 : block g126 5 0 1=true := g126P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0 = true)
  · exact (rfl : block g126 1 0 0 = true)
  · exact (rfl : block g126 2 0 0 = true)
  · exact (rfl : block g126 3 0 0 = true)
  · exact (rfl : block g126 4 0 0 = true)
  · exact g126B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 6 := lower_forest (g:=g126) (i:=0) (hints:=34816288) (before_sound K111 V111) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K111 6 [(126,[]),(190,[82,118]),(250,[81,114])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V111 low126 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[(0xfffffffffc003ffffffff1a1598052c0007fff,0x400008408008000003820a14100120a5294a5),(0xfe001fffffffc003ffe28556a668be41ff801f,0x841490090820828820281502600a450842108),(0x1ffffffffffc001c104ebbbe88800f83e0,0x508a9229211411411484100e98be08a5294a52),(0xffffe00000000000000373e416674c80007c00,0x61131c31c22722722703534416674cb5ad6b5a),(0x0,0x0),(0x45e9b45573d3ff00000,0x801c003e003803803804568b01441906318c63),(0x0,0x0),(0x33aa5dc49781be000000,0x1e01fc003c03c03c033a854c49380b9ce739c),(0x0,0x0)]
def g175C : List ColumnInfo := [(8,0,167,0,7)]
def g175A : List (List Nat) := [[]]
def g175D7 (j : Nat) : Nat := 0x7f
def g175L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g175D7)
  | _ => emptyPacking
def g175I (_ _ : Nat) : Option (Nat × Nat) := none
def g175 : Forest := ⟨175,7,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 1=true := g175P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact (rfl : block g175 3 0 0 = true)
  · exact (rfl : block g175 4 0 0 = true)
  · exact (rfl : block g175 5 0 0 = true)
  · exact (rfl : block g175 6 0 0 = true)
  · exact g175B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 8 := lower_forest (g:=g175) (i:=0) (hints:=1343225857) (before_sound K126 V126) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K126 8 [(175,[]),(183,[67]),(207,[33,101]),(215,[33,67,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V126 low175 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[(0xffffffffffffffff7f80c3a6235900003ffff,0x20441000088200000238041062048249249249),(0xffff801ffff003ff4a523a898dcd000fc003f,0xca80a13550242589448003a898d85c30c30c30),(0x0,0x0),(0xf0000001ffffffc00b00f1aeec62603f000fc0,0x8308c218610841106100e1aa84622492492492),(0xfffffffe0000000008dc59059b93603f03f000,0xc1104218230862188c4180519914924924924),(0x917a6d155cf0fc0fc0000,0x1e004003c0080209172011440701c71c71c7),(0x0,0x0),(0x4ea977125e06fc0000000,0xfe00781fc00f03c04e8976021e06e38e38e38),(0x0,0x0)]
def g187C : List ColumnInfo := [(128,0,59,0,7)]
def g187A : List (List Nat) := [[],[67]]
def g187D7 (j : Nat) : Nat := 0x7f
def g187L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g187D7)
  | _ => emptyPacking
def g187I (_ _ : Nat) : Option (Nat × Nat) := none
def g187 : Forest := ⟨187,7,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 1=true := g187P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact (rfl : block g187 4 0 0 = true)
  · exact (rfl : block g187 5 0 0 = true)
  · exact (rfl : block g187 6 0 0 = true)
  · exact g187B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 8 := lower_forest (g:=g187) (i:=0) (hints:=1343225857) (before_sound K175 V175) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K175 8 [(187,[]),(221,[33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V175 low187 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[(0xffffffffffffffffffbbc95ca230bb8003ffff,0x41000010208000000b0001c00301a09249249),(0x0,0x0),(0xfff8003ffffc001fffcbaca185ca998000003f,0xa8a116aa54908ac4544baca185ca81b6db6db6),(0x3fffffffe0003c26a2eec72340fc0fc0,0x30c2230c18211088860c2622a6062152492492),(0xffffffc0000000000046e3d85cdfc000fff000,0xc104443060c223111842c1c058c9c024924924),(0x48bd2f1bac4e7f000000,0xfe0078007f003c01e048ad0a1ba40e071c71c7),(0x0,0x0),(0xe754b7112b657f000000,0x7803f8003c01e00a750b5000b6178e38e38),(0x0,0x0)]
def g189C : List ColumnInfo := [(0,32,29,128,6)]
def g189A : List (List Nat) := [[],[117],[67],[67,117]]
def g189D6 (j : Nat) : Nat := 0x7f
def g189L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g189D6)
  | _ => emptyPacking
def g189I (_ _ : Nat) : Option (Nat × Nat) := none
def g189 : Forest := ⟨189,6,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B6 : block g189 6 0 1=true := g189P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : checkedTables g189 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact g189B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 7 := lower_forest (g:=g189) (i:=0) (hints:=1349517314) (before_sound K187 V187) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K187 7 [(189,[]),(219,[33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V187 low189 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[(0xffff00ffff00fffffa2bb094026c0000000fff,0x14822a29222a2828f80b30840260c30c30c30c),(0x7fffffffffff00ff833c0b47b6240000fff03f,0x210400420400020002340b0130052492492492),(0x800000ffffffff0070408ffac158003f03ffc0,0x402804804800000200008472c11a1861861861),(0x0,0x0),(0x0,0x0),(0xffffff00000000000dcf04976c500fc0fc0000,0x630480c704c4c4c09c900964c505145145145),(0x1175782c5bc3f03f000000,0x7c0700f807070701175280c0ac06186186186),(0xce937660389bffc0000000,0x780080f000808080c6025660300b8e38e38e38),(0x0,0x0)]
def g231C : List ColumnInfo := [(1,0,230,0,7),(32,0,199,0,7),(64,0,167,0,7),(0,128,7,96,6),(128,0,103,0,6),(2,0,229,0,5),(4,0,227,0,5)]
def g231A : List (List Nat) := [[],[33,101]]
def g231D5 (j : Nat) : Nat := 0x4fb7058a21
def g231D6 (j : Nat) : Nat := 0x40080504c50ac85b400bf58a21fed8121bed8121b758c21be58021
def g231H6 (j : Nat) : Nat := 0x6
def g231D7 (j : Nat) : Nat := 0x190e6a1474365a981d90ea6147888807f887fa43fc21
def g231H7 (j : Nat) : Nat := 0x990000000000000072000000000000640000000000000000a1000000000000000000000000300000000000d3000000000000
def g231D8 (j : Nat) : Nat := 0x468817f
def g231H8 (j : Nat) : Nat := 0x4a000002100000008003f000000000
def g231L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g231D5)
  | 6 => (5,2,3,0,0,6,0,g231D6)
  | 7 => (3,1,3,0,0,7,0,g231D7)
  | 8 => (1,0,3,0,0,0,0,g231D8)
  | _ => emptyPacking
def g231I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g231H6
  | 7 => lookupWord 1 53 0 8 3 1 g231H7
  | 8 => lookupWord 1 17 0 7 2 1 g231H8
  | _ => fun _ => none
def g231 : Forest := ⟨231,8,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P5_0 : block g231 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B5 : block g231 5 0 1=true := g231P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_0 : block g231 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_3 : block g231 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B6 : block g231 6 0 5=true := (@block_merge g231 6 0 3 2 g231P6_0 g231P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : block g231 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : block g231 7 0 3=true := g231P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P8_0 : block g231 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B8 : block g231 8 0 1=true := g231P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact g231B5
  · exact g231B6
  · exact g231B7
  · exact g231B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 9 := lower_forest (g:=g231) (i:=0) (hints:=1376780289) (before_sound K189 V189) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K189 9 [(231,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V189 low231 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[(0xfffe0007fffffffffffffc50275825dc0003ff,0x42040490909101200487b410200824d0a5294a),(0xffffffffffff8001fffc4d4b5ca68cec007c1f,0x142888450502220c882049415ca0882d18c631),(0x0,0x0),(0x7fffffffe0001c13507f6713a0003e0,0x98b11166262444491130412507f6512b5ad6b5),(0x0,0x0),(0xfffffff8000000000002371ec266fe200ffc00,0xe0c021803838087021c2141a824676006318c6),(0x245e978dd6253f00000,0xff003e003fc00f803e0245c968546252739ce7),(0x73aa5b8895b2bff8000,0x1c007c0007001c0052a24108909298c6318),(0x0,0x0)]
def g235C : List ColumnInfo := [(0,8,226,1,5),(0,64,43,128,5),(8,0,227,0,5),(64,0,171,0,5)]
def g235A : List (List Nat) := [[],[112,81,99]]
def g235D6 (j : Nat) : Nat := 0xe413f
def g235L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g235D6)
  | _ => emptyPacking
def g235I (_ _ : Nat) : Option (Nat × Nat) := none
def g235 : Forest := ⟨235,6,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 1=true := g235P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact (rfl : block g235 4 0 0 = true)
  · exact (rfl : block g235 5 0 0 = true)
  · exact g235B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 7 := lower_forest (g:=g235) (i:=0) (hints:=1460666369) (before_sound K231 V231) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K231 7 [(235,[]),(237,[33,101]),(243,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V231 low235 (by decide +kernel)
def g249Y : Array (Bits × Bits) := #[(0xfffffffff000ffffffb58b416b05fa80000fff,0x88822222208a088088b4034101055a09249249),(0x0,0x0),(0x0,0x0),(0xffffffffffff000fffc9a9da84d299c003f03f,0x11044444411011211049a882840281d2492492),(0xfffffffffff000383638eedc270003ffc0,0x2228888882202202220014386ad82424924924),(0xffff0000000000000046f3c05ccfc400fc0000,0x3c300f0f043c43c43c44e3405ccec4071c71c7),(0x48ad2f1bac4a7f000000,0x3fc00ff007c07c07c048ad0a1bac4a071c71c7),(0xe754b7112b657ffc0000,0xc000f0000800800800a310b500012178e38e38),(0x0,0x0)]
def g249C : List ColumnInfo := [(0,128,25,96,6)]
def g249A : List (List Nat) := [[],[101],[67],[67,101],[48],[48,101],[48,64],[48,64,101],[64,48],[64,48,101],[64],[64,101]]
def g249D6 (j : Nat) : Nat := 0x7f
def g249L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g249D6)
  | _ => emptyPacking
def g249I (_ _ : Nat) : Option (Nat × Nat) := none
def g249 : Forest := ⟨249,6,fun i => g249Y[i]?.getD (0,0),g249C,g249A,g249L,g249I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_0 : block g249 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B6 : block g249 6 0 1=true := g249P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249T : checkedTables g249 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g249 0 0 0 = true)
  · exact (rfl : block g249 1 0 0 = true)
  · exact (rfl : block g249 2 0 0 = true)
  · exact (rfl : block g249 3 0 0 = true)
  · exact (rfl : block g249 4 0 0 = true)
  · exact (rfl : block g249 5 0 0 = true)
  · exact g249B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249G : graphValid g249 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low249 : Lower true (varsX 249) (graphGoal 249) 7 := lower_forest (g:=g249) (i:=0) (hints:=1466957827) (before_sound K235 V235) g249G g249T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K249 := extendKnown K235 7 [(249,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V249 : Known true K249 := extend_ok (m:=249) V235 low249 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[(0xff403282a1b39566cd04e4c30000000fffffff,0x328020208022c90004c020408102040810),(0xff330568ce45a69d11414d650003fff000007f,0x480300608e45069c10414001183060c183060c),(0xa6d406511e4a5058b393ac01fc07f0003f80,0x9220c406511a00400030932c060c183060c183),(0x5869537e211b88b23a823bfe0000001fc000,0x1c5009535c011b083022822b4a952a54a952a5),(0xdce9997cc40ef261d2118fe00000fe00000,0xe00dc40883cc40c5061d2110952a54a952a54a),(0x11736d4978710327ee89cc0003f800000000,0x10730d4138710327ae89cce7cf9f3e7cf9f3),(0xcea9248a495e2bafa33e8001fc0000000000,0xce29208a415e2baf832c80f9f3e7cf9f3e7c),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(32,0,95,0,9),(64,0,63,0,9),(0,32,93,2,8),(0,64,59,4,8),(8,0,119,0,8),(16,0,111,0,8),(2,0,93,0,7),(2,32,93,0,7),(4,0,59,0,7),(4,64,59,0,7),(0,8,102,17,6),(0,16,102,9,6),(1,0,126,0,6),(24,0,103,0,6),(40,0,87,0,6),(64,32,29,2,6),(72,0,55,0,6),(1,8,102,16,5),(1,16,102,8,5),(2,64,25,4,5),(4,32,25,2,5),(8,16,102,1,5),(8,32,85,2,5),(8,64,51,4,5),(16,8,102,1,5),(66,0,29,0,5),(66,32,29,0,5),(68,32,25,2,5),(6,32,25,0,4),(9,16,102,0,4),(10,32,85,0,4),(12,64,51,0,4),(17,8,102,0,4),(25,0,102,0,4),(38,64,25,0,4)]
def g127A : List (List Nat) := [[],[67],[33,101],[33,67,101]]
def g127D5 (j : Nat) : Nat := 0x3d8930c0a1b2899661e518c207da961e6294630a476a3731d2514c303d98dd26294530ca665262201314c28aca25db845cd10
def g127D6 (j : Nat) : Nat := 0x1620200260e04080000068fe004001e08207080800027c204000000000000001c28200000002080a08080000068ba1680181e002000c382c3f00160fa2780180060fe004060fe0058382060c64040982068f057821e0fe2f801d755a5494a51d445053e4c52e4ad234811845512415023fcfc3e4f63ccf03b4ea39cdf370d9358d3340c8300bd2e8b72d0a227c97250912247c1a86719057150470fc3c0bc270901200187d8750e62946a7f28c1ae128d1f662625c251a3ec84c4b84a38ef96608704c61fb31310e098e2f612621c131c76c14c4382634ec92619718c29ef22bb2e31861f65987946308bfc930f28c6187d875da518c22fb31ba4a31845f6617294630cb6c12e528c6127d9898a518c30fb0f314a31865be097254230a3ecbcc4a846159d91dcc744c297d2e3a2c298727dcc7458530c5fba700b0a6153e971d2514c3a3ee63a4a29864fdd1829453093ecc4c528a61c3f7498a514c327ee8c04a2986b6988804c530c9fba704a8261c3f74989504c3d3286b0a80987c650e51501309aecc4a3182610fd98dce6284297f28b9cc50853b24976dcd10a76492ecb9a218bd76e11734431ef22c3cc48843f6637398910a5fca2e731221af391602624425ef22c04c4885b9249764c510b78c84c498a213f297201314427e3244026288679dcb8148110b72492ed082212f59898a10442de321314208851b249865c25183ecc4c4b84a347990989709467332840262984f8648804c510
def g127H6 (j : Nat) : Nat := 0x600000000000090000000001900f80000000000255200000
def g127D7 (j : Nat) : Nat := (if j<1 then 0x70027870c060a1504800c07c0c3861a83d138020320e141e0811260e160f0380c3880c43841e0885804385c1e00309287160fc00d060c83850704380c61060f833243e0c19921c1990102f83c0c261c18370781c50661c5c01230e1b0680c9a389c5c27048c270780110f83c0a2a304e051e921f068c112e8fc1050305e08468e1f07808a0689c1e00470e200c03c0c38813047030e271789c02461c5e0f002387102601e061c409f009087138048c38707e2f0018212780870c25c1e004492871b8bc42404c4eb2ea3e94e73e52e43e22e01dceda4d95d74d5cd4dd35d0bccfcc0cb1c87c54c33c09be8bbeb8bb7cb52b31b10ae6ad7aada8ca6ba41a179f69c399997896094891e9189099038fd8ee8d68d08c18bb8b58a689787f87086185284c83480a7fb7ec7d47bc7ad79e79878977a75072f70e6ff6de6c66b768d66c64b6336126035e25c159757f56754f52550d4f54dd4aa4894714624414203ff3e73ab37835732d3032e22b829727f24c22b2011d71ad1831501260fc0d20b108706602a000cfd43dc161d7d435ca51e7d4398a51d7f835c251d7d835c251d7d435c251d7f825c251d7d825c2519ff825d1319fd80dc931cff7498931cfd7498931afd8098931ef66250531cfe62dc1319fd821c131cfe621c131d7d43dc950e7d4398950b7f825d6309fd81dd230cfd865c6309ff825c630cfd765c630aff8758630cff7458630cfd7458630aff8058630b7d8794630e7d7694630d7f7494630d7d7494630b7d8294630d7d7294630e7e6294630b7d80946309fd8748630df57148630b7f8254230d7d7254230e7e6254230ef96190230f7a51902309fd82dc530cff7458530ebf7458530cfd7458530ebc7458530edd4358530aff8058530d7f7494530f3f7494530d7d7494530f3c7494530f5d4394530b7d8294530d7f7294530e7e6294530b7d8094530bdf824c530ddf724c530ede624c530dbf7448530b7f8254130e7e6254130ef96190130f7a5190130ef96150130f7a5150130bdd818c130edd618c130f5e518c1309fd82dce10afd8798a10cff7398a10cfd7398a10afd8098a109fd82dcd10cfd76dcd109ff825cd10cfd765cd10bbf845cd10def725c910afd8798910cff7398910cfd7398910afd8098910ef5764c510bf7824c510ef6624c510fe77248510bbf844c110ff38148110ff13148110bf78148110fe52148110ef57684110bf58284110ef66284110ff12084110c7d865c25197f825c251c7e625c2519bd841c1319ed821c131a7d8098950c7d765d63097d87946309be871d130d9f731d130cbf7458530d3f7494530bd8804c530d3f7454130f9943501309bf845ce108fd8798a10af98098a10aec825d9109bf845cd108fd8798910af58198910af98098910bf0804c510af78158110fe1214811087d8798a51 else 0xc405880b1016230d8218598ac40d88080b82c90c29c1648784018080200140602008004628384412003c16002c20302800403c3f0780241a0b04814001033101620384e08019226100602008005a380780180c0400e08942a03043a3e1007c010338401a09002b1410be130580130802e08784a12043c220c0481118a0e1307810a0883012043c220e04185b0983c088030100400211d06080c1d84c1e05102839060240890ec220c382e10282e102018080200100428200085070b84080428200085070a0a0d0216141c28385040836142a0d029347130a0e14182e10282e10282030404082030404060200800401f030e180d04800d0a084f81870c06010820080c0400e08945a15003e0f030e1872821)
def g127H7 (j : Nat) : Nat := 0xf9aca5433914b0ce08000928616000000a11000000a1da98da7c1883a734000000000315a21623000013e3874c81bf00612d193268a166a000201935c0290d45312d00093250e000000000b2a000c31162b3618e799000000000000339b2482c000327f8d0000000a2000a1a2222b13255a432ba04000265000e0bea9a03d0a51e206229f1f00070f000730910805017f3700000022069140994b000b5475f60700001c02eda6000f2f0c231888004028c0061c20c3401080
def g127D8 (j : Nat) : Nat := 0x1e054382418084181525120600342a261c70a8443c1c0471872120506010029251c9854140491d0a471c330701261c543c08744c11118787429170513021c8448381800d87111c330305261c51cc1c0498715110e0506021c7c4481e0c448343814180408729160e060044761c71c0cc1c049871b0701261c444c087894d152113061934545c1c087181218230117061c4460c0b02c5c1c0491e23170211221c518498711101c17070210607471d02c1c0111e182f140c20170213061c30a0b0100c58987111d1305361c445411dc58749111b240213051c486080603024584c1c00c25170700604850308c584c012c147206b1702111d2468388c584c146183a220e13051c487c1c045840c1707006048405c1c00a1d17070028844c1c00a1d1307003444408c0c1471d170216111d2458885c1844616170700611c44685c111471d161307003444504c1c01815142813070048501c012498711182c21100f0317061c30905c1c00a871d182c2814100401261c309050412c1c011874922161301221c51a80124987111a1d24303c5c4c01a498718200f0063061c447080544c018c18711202c28141303061d2481c0b0a0504c1c0498726161301221c51215c1c00744111c4b04441c88585841241c0114987204873070045261c7c1c04987104b07001c445c0c5c4091a15271710186c5c5c4488613271713041854900c5c4071b1a031711221c5c44180121149871c602c47271e130700883f4102014fbc7bf3d41e34ed474b39a1c74df46cf3581a54d0466b32a18e4c3c5fb2f21744b645972b61534a6c51b280136498449f24211a489443321010247ec3e31e80ee474438b1b80d6468432b18a0be45a42b714809b44ac23b11608443e41cf0d606142dc14f09c04541ec0e306602d413c08b03a01640840230003fea1263ff50d21ffae3187fd218c3fe90a61ff5ca10ffee6887fd73443fea1a21ffdc910ffae4887fd32443ff18221ff4c110ffc40887fd204437ea1ac3df50e51bfee898dfd744c6ffb9263bf98931fba6498ff5414c6ffb82637f1c131bfae690f7d43543be992a1df5d630bfee9185fd748c2feb8c61bf58630efca31877d508c3fd204617fdd130f7ee8985fd744c3de3a261f750d30bfee2986fd614c3bf28a61f74c530efaa0987fa404c3fca0261f78c130dfaed085ff73842feb9c217fdca10bfae5086fe628437eb0421fe88210dfaec885ff73442feb9a217fdc910bfae4886fe62443fa98a21fd48510dfac0887fa20443fc90221fd841109fee0b0d7d729473f314a35f5c251afee4a867e625433eb02a16fdd130
def g127H8 (j : Nat) : Nat := (if j<1 then 0xef534000246243a000e20d154001f4e000000000147a000000000000000041f40b60000000000000e39918006c8d8000000000000000000000000004740000000000000000000000000000000000000000000000000000000396800000042742c000000000000000012130000003942000b1910a400000000044e8000506000000000014c000000122a66800000000000000000000d78000e3e546ecede170000000000000c9e000000000000000038f0000000000000000000000000000000003950000000000000095c0000003d86e9600000009180000000000000000000000000000000022c00000000000000000ca600000000000000000000003c5000000000000008fb000000000000000000000002480000000000000d868001804000816a564000000f1200000008190003d9c00000000000000000008900000000000e3f0000000ac7eab80000010b400000c4000000f5f0000001f50000000000000000039d400000002c80000012de000382c00000018480000000000000000dac000000000000000000000000000330006487ce60007aa000000000000020780000000000000000000000591d0a00000000000000705000000147c000a388002d8a0000000003be4000000000000000000000000000000000000000000794000094e0000007b7069000000000000000000005d9000000000000000000000000000000000000009400000000000000000000000000000000000000000000000000000000001228000000000035502000116c000000000000000000000000000000000000000032000000000000000000000000000928000000000000000000000000000000000005b3545ca610000000000000000048c000401da7800000000000061bc0000000000003c43b380000003167ee300000000000000003178001746c31000000000000000000ac00000000000000000000000000000000000000051000019e4000000000000089e24da3900000006438b98000000000000000087000000000000000000007d9640c0000000000001a5f00000038f60000000000001c1400000000000000000000000057b070000000e10c2e00038120000000000000000fa080000000000000000694000000000000000000000000000004328000000e2a00000000000000000000c40000000000000000080680000000000000000000000000000000000000000002d40000006175df400065529b7019e490000000000000000000000000000078dc0000000000000cd20000005685c245299a100000000002020000000000000000000000079d800000173e0007d4b0c6000000000000080f0000000001b5f0007908001c2f00000000000000000003e6573d0000000152000010a1400020000101100000011000000010000010000125300011 else 0x12ce31b01afd8806000000000000000000003868000000109c000a40a0c0002c760009a880ac000652349000000000036d8000000000000699f8cc00000000000000000000000000000f1e8000000000000000000000000000000000000000000000000000000000000052275240000000000000001c510000000000000e9b800000000000000000000000000001022000000000000020a00000000000000004c10000000000000000000000000019900000001c3c00000000004b00002bf00000000010150002d58000000000000207400010e000384600002605812ba00041374e55b0c1ae112d5580a0000b9000000082c0000000000000f0fe0f00e000000000000000000000000000000000000197a0000007a96c96416537148800e00000038ff007c00f8128d7)
def g127D9 (j : Nat) : Nat := 0x423263c1803473d16049090500720009821e2c44438305263c524120c0242c98e6024180748064a24093148c10e48381262c4821c78116207122c98b12086140498b120871bedb8c0cf1fcb9411646000ff50ffd31ff487fe30ff4c3fe10ff442fd61df9477d50
def g127H9 (j : Nat) : Nat := 0xd8f10a5219880182e22f8880006800000001ceb45f916b0b0003c770117a1000143c000416dac4a64722b12000341a000000401e86c614f022cadc6664cb09690b45db3081d400b04240bb190000000000964800000101951e8000001f45000389608229f00063280000000005a89155046000706f846f2119ee8e091b215f1f3815021cacadc1120001434000404c00084a190000000143c0007d2fd2204d4490000e55647a1fdc8c0000000508003054000913b8dda7e000600e070001808a200000d56c9a59e08c6c50c0f0000a79c00000204b0b00000000a0e0e5088b0209c000041800000028399660004149c2f44c21a000006218563514cd29163ea4bf96c01b235817d60780ee1852cb98c11483ac49b15f45400000000078c3415cc6d0f800061ca7c6210a32f0143444c60058c0023210100218003
def g127D10 (j : Nat) : Nat := 0x48e28808037f
def g127H10 (j : Nat) : Nat := 0x10027130806a10000050d42902f1800cb000c4001ac388000014394930192343aad1000004105
def g127L : Nat → Packing
  | 5 => (6,5,6,0,0,5,0,g127D5)
  | 6 => (59,4,6,0,0,10,0,g127D6)
  | 7 => (127,3,6,0,0,12,0,g127D7)
  | 8 => (78,2,6,0,0,13,0,g127D8)
  | 9 => (10,1,6,0,0,9,0,g127D9)
  | 10 => (1,0,6,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 31 0 7 3 0 g127H6
  | 7 => lookupWord 20 113 6 12 6 2 g127H7
  | 8 => lookupWord 53 797 4 13 7 2 g127H8
  | 9 => lookupWord 33 181 5 13 7 2 g127H9
  | 10 => lookupWord 5 29 3 10 4 2 g127H10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P5_0 : block g127 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B5 : block g127 5 0 6=true := g127P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_5 : block g127 6 5 54=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 59=true := (@block_merge g127 6 0 5 54 g127P6_0 g127P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1 : block g127 7 1 26=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_27 : block g127 7 27 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_123 : block g127 7 123 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 127=true := (@block_merge g127 7 0 27 100 (@block_merge g127 7 0 1 26 g127P7_0 g127P7_1) (@block_merge g127 7 27 96 4 g127P7_27 g127P7_123))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_8 : block g127 8 8 54=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_62 : block g127 8 62 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 78=true := (@block_merge g127 8 0 8 70 g127P8_0 (@block_merge g127 8 8 54 16 g127P8_8 g127P8_62))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_3 : block g127 9 3 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 10=true := (@block_merge g127 9 0 3 7 g127P9_0 g127P9_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 1=true := g127P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0 = true)
  · exact (rfl : block g127 1 0 0 = true)
  · exact (rfl : block g127 2 0 0 = true)
  · exact (rfl : block g127 3 0 0 = true)
  · exact (rfl : block g127 4 0 0 = true)
  · exact g127B5
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K249) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=34603009) (before_sound K249 V249) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K249 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V249 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[(0xe049c150c946a30c47df4000000000ffffffff,0x9c0500042000c4300400909090909090909),(0x9b922423027b5a12189d6e0000ffff000000ff,0x290200302214a12089d225050505050505050),(0x536a112c9b8d38dbd0409c000000ff0000ff00,0x5162112c998c30c190409ca6a6a6a6a6a6a6a6),(0x2c2439fb3005d042a97a9b00ff000000ff0000,0x280439ab30059042085a193232323232323232),(0x6e75c8bc6a86745a4a08600ff0000ff000000,0x6e20400c6a86701a4a086c4c4c4c4c4c4c4c4),(0x8b9a6e4bcb085e13a4075ff00ff0000000000,0x82906e4889085403240550707070707070707),(0x0,0x0),(0x6754920534af14b5cf8c13ff00000000000000,0x67549001342f10b5cd8c02f8f8f8f8f8f8f8f8),(0x0,0x0)]
def g191C : List ColumnInfo := [(0,128,31,32,9),(128,0,63,0,9),(4,0,187,0,8),(8,0,183,0,8),(16,0,175,0,8),(32,0,31,0,8),(32,128,31,0,8),(0,32,29,130,7),(2,0,189,0,7),(24,0,167,0,7),(0,8,166,17,6),(0,16,166,9,6),(1,0,190,0,6),(4,32,25,130,6),(6,0,185,0,6),(1,8,166,16,5),(1,16,166,8,5),(12,0,179,0,5),(16,8,166,1,5),(9,16,166,0,4)]
def g191A : List (List Nat) := [[],[67]]
def g191D5 (j : Nat) : Nat := 0x2789a42413288530
def g191D6 (j : Nat) : Nat := 0x388081c4040000000f0f80200000000003c0080000000000079a15a20fc3e08507e1f079039f4e2652c9345e23027e3d9e0ea723318cc05d2d15ca85124d1a87409ecea6f3498c842100679e49811c1328f6cb900994433ad94201328867cb224026510d796477288530be3c8a6510a617c8904ca214c279f24c0c60985796477388620ad7ca2e710c419e7985c6218823dd2fc0a64904faa5c804c9209f4c8900992411ef9261e30c423df24c0ee70856be5183dc910ad7ca2e7b92211ef985cc72442b5f28b98e4886e9613728c5109f4c910098a219e687dca2144335f09b9260885f8a5e2188110cf3b9702902219e792e1d100433cf0fc1220087715cf8244010af34c2e48802139994201324c27332840262984f8644804c920
def g191H6 (j : Nat) : Nat := 0x7
def g191D7 (j : Nat) : Nat := (if j<1 then 0x1a00c281c402130c0c407101000020810e04081e0070810c0400f0420082c20431200830302083f0700300081000008816305918c20e04881220401164092088200043816004064040c1003c1a3068c1a30428127e008022044410822080c04003a3043f082a4a30838122043810c2208443c20c043c1880208001020c08303820c06201a0043018804381002f0b870c33986e1e40ce6c2142f0f8780305e4e1e00c1393878045205e4c3e1e012279a882830589e1e00a0c143f870b984e1e0280f8780383e1e00b8783903040fe1e00f87802e1e00b87802e60e0b8780383100fe60e1043843b803c5e1e0100e1043803b943c58b289488688087286485685084283c82e82881a8148067f87ea7d47ce7c07b27ac78e78076275c74e74073a73472e7207127046f66e86da6d46c66b06a268466e65064a63c63663062a61c60e5f85ea5dc5ce5c85b259c58e58057256c55e55054a53c52e5205125044ee4e84da4cc4b649848a47445e45044243441e4083fa3ec3d63c83b239c38e38037236435634834230c2de2b028a25c2362081da1b419617816213c11e1080f20dc0c60a808205402e0009fd80dc5329fd811c1329fd80dc9319fd821c131bec804ca21ded325c2219ff815ca309ff825c630def825c630dec825c630bef825c6309fd8788630df571886309fd8748630ded7248630df571486309fd81dc930bdf814c9309fd82dc530ddd32dc530bdf824c530ddf724c530dbf7488530def7288530fcd3288530dbf7448530bdd828c130bdd818c1309fd81dce20def7388620ded7388620fe57188620bed80886209fd81dcd209ff815cd20bbf845cd20bef814c9209ff874c5209fc874c520fe77148520bbf844c120bed81881209fd878c310bbf844c3109fd82dce109fd81dce109fd82dcd109ff825cd10bbf845cd10bef825cd10def83dc910ded83dc910def81dc910ded81dc910ded80dc910def73dc910ded73dc910fe781dc910df7815c910def725c910bee871c910def731c910ded731c910def724c910fe7728c510bf7824c510fe7724c510fe4724c510def724c510bfb804c510bf8804c510bf68788510fe77288510fe53288510fe772485109fe878c110def728c110bbf844c110def724c110feb7288110def7288110fe62188110feb7248110fe93248110ff38148110ff13148110def7248110bf78148110fe52148110fea2048110bf58284110fe77284110fe47284110ff12084110def7284110df78744010fe782440109bd841c1329f5811c1329bd841c1319ed821c131be7814ca219ef825c630bd8804c930bd8804c5309bf845ce20de57188620be980886209bf845cd20be8804c9209bf845ce109bf845cd109ef825cd109ee871c910bb5848c510fe22188110fe121481109f78744010dd57344010de57244010 else 0x30b878030f04002040c1e004002040c30400204008040810a07100c200081c4040a2a)
def g191H7 (j : Nat) : Nat := 0x14116200000167000691001c6c0000043e88142e0c000c0485198b214788370f01603b89408001255cc80011bc58819941122698ee82b0124f0bb07e6c281a800
def g191D8 (j : Nat) : Nat := 0x21a21418a86883868500a1044344284150d0a044206150d10e122434281113143c4868898a1440c841a31e11322292424630cc03831c0a31e11146303488c793111c180304488e0c01e4c6443021c302463c226292224628c108831c0a2223c3858700a108c64708606911c21e4c5183821c0c2c38040830528c3273111e4e1cc3c88a1c461852730c1e4e61c30493987063c76692209cc3c7080b0c9cc3c50e20161cd2460f873291e21105994c81458a080c442cc3081628203119a10ea47661e261182116692308c20866692304878730a26308c28b313170e6128878a28161cc4c5c2233091e2e1c028488230c2539860c12161cc2898c101901f9870c0b3280c461159948a22161539878c0b0c8cca478c2c504063b30c407e61c210c3207e60430ecc294899948e1e202c2a730c14261cc2898a2c504063b30c1c203203f30e18203203f30e186661c1901f987084330e1e202c39948a149e104a730f1858ac98f30e1b0e4c68a4661858a080c7661b263cc384479898e10466523c4203f322102901f98708407e61c2661c11011987883b3291e20b141018ecc307203b30f108431d984c24858fc50f30e8b0c8d3985203f4e010346148f2101d986203f4e61c2f026f4ee3ed2ebaea9e8e679e6c66264a63ce3662c61ee0ddfcde4ddadd0dc6db25a4d9e590d78d6b556d4cd46535519d054e9cd8ccb4ba4a9494c79468453c34c194083f03d83c03abb97382b6e35d34532d315307af32db2c32ab29a28227126024ba3721ba039eb9de1cd1bc1a798f97795f9479369259149000ef0de0d40c30b209688587485904482c8148007ff724c7feb9461ff9c630ffae3187fe218c3fe90c61ff88530ffa42987fd71883ffb9a41ff5cd20ffee2907fd71483fe98a41ff8c120ffa60907fe30c43fe98621ff5ca10ffa41087ff73443feb9a21ffdc910ffae4887fd32443fe98a21ff8c110ffa60887fe20443fe90221ff84110bfee2995ff704cafe382657f9c231bfae118dff724c7ee992637fdc131bf8e098dfd73887f6994437f9c221bfae110dfd73486feb94617f5c630f7ee8985ff724c3ee992617fdc530fba62987de304c2ffb9c417f5ce20bfae3107ee21882ffb9a417f5cd20fda64905ff71483f690a41fb88120bfae7887f531c42ffb9c217f5ce10bfee5085fd72842feb8c21fe88210ff241087f710842ffb9a217f5cd10bfee4887ef72442feb9221fb1c910fec62887f531443fb10a21fd48510ff440887f920443fb082217f5cc10bfce0087f510042deba4636fdd130bdee48857d75042eeb98217b5c810
def g191H8 (j : Nat) : Nat := 0x14c4001dc41400000000000000000000000000000000010ec00000249fd7000000000000241c000000000000001dac000000000000000000000000001f680000000000008e4000000000000000000000002c50d74cfc000000d180029d58a85dc000000000000000000000003127b64000002c800000015b2314000edc9b40000030e818c0000000000000038580038b80031a8424000003500000001444000000000000000000001c2c0000000000021080000019880000000000031d000000000000000000000000283c0000000000000000000010cc000000000000000000d800002b800040c00000000254601290c0000031864482040000000000000029cc0000000000000000000004c000000000000317c000000000000000000000000cf0000002cbc0018040000000000000000000000028880010d35c8000001c905a000000000000000000000000000000007d4d4000000000000921c98000000000000000000000000000002cf80000000000000000000000000000000035968f4000000000000000000000808000000000000003fc8002691c300000000000000000000000000000000000000000000000000000000030340019bc0000000000000030600000000000000000000000029079c00000010940000000000000031540000000038dc00000000000016400000000282ad63190000000000000c40001c0197a53400195c00000248407800000000000054c0000000000029980028b000385f5d800392c000000528000000000000000002c8c0000014b4000000000000001d6c0000000000000000000026ccae400199c000002d3c0000000004e0000000000000001054000efc0000024a4000000000000ea40000000000000000024640012e800000000000000000000000302104d700000000000000000000000000000000000000000000000000003e88000002d14000ee26d1558548000000eac00000000216af1191c002dbaad4003d100020ad950000001138000000000000000003c68000002cc800246d016c180014a2039074000000000000000002870000000000000000000001d319a4cd8058a4808488cb4000
def g191D9 (j : Nat) : Nat := 0x8c211e74c48e09331c24279d3122834853102854cc7090906453123424267c53123c281c7d214c3c275214c2834cc7090a07d274c3050d274c2a02061027d331c4f6b7998ba55a58fc662a114601e003fd32ff8c7fd31ff887fd21ff8c3fd30ff883fd20ffc43fe10ff443fc10
def g191H9 (j : Nat) : Nat := 0xe2b0000000009a370f910b4673774c99d933000d1f000212000000000000b18000a1a000000000000000000125d1d413000ac9d2a40d55a2d7a30788507b2164e231000806000eb600052600000000092d0d5bda0000000003cfcce000000f520004474b50000000000008d181c0a889548e12ca248c3100000000000000139000dc561b35700035600062863852300021400025b000e8fdb2c5504be0bc09d17e01142e34000a270000c6000000ed8929615540a5d88144800044fb2ffcd000b9e000819a0400000000094312ed2223e30300000024919c000f3f13b0350005548a480e732305c518ca90ca5900000000093a316000000a3ce9f000145000000b940000d90000000000000005c40000000006a9f5800064a000b5000004d00000025e6a5c0204455c341000b2000a20823d1d02d4000f1e5117535360052470829900c63c10400030c11822c30010c9080244004
def g191D10 (j : Nat) : Nat := 0x1124c27f
def g191H10 (j : Nat) : Nat := 0xc49d704c04223f30ec000041555fcb58036e00005a6f6000010c0000005208c0006c2
def g191L : Nat → Packing
  | 5 => (1,5,5,0,0,0,0,g191D5)
  | 6 => (33,4,5,0,0,9,0,g191D6)
  | 7 => (120,3,5,0,0,12,0,g191D7)
  | 8 => (95,2,5,0,0,12,0,g191D8)
  | 9 => (13,1,5,0,0,9,0,g191D9)
  | 10 => (1,0,5,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g191H6
  | 7 => lookupWord 8 43 5 11 6 1 g191H7
  | 8 => lookupWord 35 521 2 12 7 1 g191H8
  | 9 => lookupWord 32 211 6 12 7 1 g191H9
  | 10 => lookupWord 4 29 4 9 4 1 g191H10
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P5_0 : block g191 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B5 : block g191 5 0 1=true := g191P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_0 : block g191 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_3 : block g191 6 3 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B6 : block g191 6 0 33=true := (@block_merge g191 6 0 3 30 g191P6_0 g191P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_0 : block g191 7 0 23=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_23 : block g191 7 23 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_119 : block g191 7 119 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B7 : block g191 7 0 120=true := (@block_merge g191 7 0 23 97 g191P7_0 (@block_merge g191 7 23 96 1 g191P7_23 g191P7_119))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_0 : block g191 8 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_6 : block g191 8 6 58=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_64 : block g191 8 64 31=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B8 : block g191 8 0 95=true := (@block_merge g191 8 0 6 89 g191P8_0 (@block_merge g191 8 6 58 31 g191P8_6 g191P8_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_0 : block g191 9 0 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B9 : block g191 9 0 13=true := g191P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B10 : block g191 10 0 1=true := g191P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact g191B5
  · exact g191B6
  · exact g191B7
  · exact g191B8
  · exact g191B9
  · exact g191B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=1343225857) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[]),(223,[33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[(0xffc39029dc0bddb218603b24000000001fffff,0x20029008d408c822184008242850a142850a14),(0xfff0a7602250514fc6d511a9000007ffe0007f,0x44005602210110cc691110144891224489122),(0x3d0a0729af02383e1544cc0003f80fe03f80,0x493d020709270210200400c883060c183060c1),(0x8203bfa1407d467ac7e9a000000001fc000,0x8e0820332a1407d467ac769ad7af5ebd7af5eb),(0x0,0x0),(0x6e75e8bc2aa6361a0a48601fc07f0000000,0xf006a20e88c2a2630120a4861a3468d1a3468d),(0x8b9a4e4bcb285c13a4475fe03f800000000,0xb920e098b081c13a44241c3870e1c3870e),(0x6754920534ad14b5cf8813fffc0000000000,0x61449005240d1434c50811e1c3870e1c3870),(0x0,0x0)]
def g239C : List ColumnInfo := [(8,0,231,0,9),(0,8,230,1,8),(32,0,207,0,8),(64,0,175,0,8),(128,0,111,0,8),(0,128,15,96,7),(1,0,230,0,7),(1,8,230,0,7),(2,0,237,0,7),(4,0,235,0,7),(40,0,199,0,7),(72,0,167,0,7),(0,32,77,130,6),(0,64,43,132,6),(8,128,7,96,6),(32,128,15,64,6),(64,128,15,32,6),(136,0,103,0,6),(160,0,79,0,6),(192,0,47,0,6),(2,8,228,1,5),(2,32,77,128,5),(4,8,226,1,5),(4,64,43,128,5),(10,0,229,0,5),(12,0,227,0,5),(32,8,198,1,5),(34,0,205,0,5),(64,8,166,1,5),(68,0,171,0,5),(96,0,15,0,5),(96,128,15,0,5),(128,8,102,1,5),(3,8,228,0,4),(5,8,226,0,4),(33,8,198,0,4),(42,0,197,0,4),(65,8,166,0,4),(76,0,163,0,4),(129,8,102,0,4),(130,32,77,0,4),(132,64,43,0,4)]
def g239A : List (List Nat) := [[],[33,101]]
def g239D5 (j : Nat) : Nat := 0x30a66e9176201734869d3a15d0805cd21
def g239D6 (j : Nat) : Nat := 0x2c404000000070c100001c3708200003430415040710105c1570dc2100701c709c7040b10105c15b0ec2100b1c1b06c0080710105c1570dc211c404001c051c2e101000000000000000034204000002c4040000000000000020c10183b8ad2b32c6b02baad2a4a7a98a4a789ca6c99a5691a408c2027f1e2749cc6f18e62178579585211a429043f8e4350ce320c22f0b62c0aa2909e260922087c1d8701a85a1504e120420f0360c02a09000aec48306b948393d87552529069bf2caa6e498e57e177258931cebb9702a126399f84dc9614c6bb120c1ae510ef158b814ca21acfca2ecb9a435d7915d1734873b6ec402e690e765d8805cd21cedba100b9a439d97420173486fa120b9ca290df424173545219f24c284a8a43bc782545314873cf2dc3a4210e7965b8748421cf3c870e908439e590e1d21086bcb21c3a4210e79e1f8648421af3cbb0c908439e787619210873cf0fc024210d79e5d8048421cf3c3b0090843de39848570087bc72c90ae010f78659215c021ef0c3242b80439e79848570087bc72090ae010f78641215c0219f3cc24210ac1be12160021582b3f28c32e318573e49855c630ae64930ab8c614df96551718c2bab23412e3184776617298630caec2ae530c619cd825ca618c2baf22b94c318667e117258630aebc8ae4b0c6199f845c5618c23bb30b94a3186376197294630ce6c12e528c6199d87552418c23bb30b94831867360972906308eecc2e510c619d5825c6218c23bb2fc22431857565e5148630ee2b94a290c61dc572545218c2fc32121242885f864a2148110
def g239H6 (j : Nat) : Nat := 0x2402d7c0
def g239D7 (j : Nat) : Nat := (if j<1 then 0xd835ca619ff805ca619fd80dc9619fd82dc1619fd82dd1519fd80dd1519fc8750951d7d54dc1519fd82dc1519ff805d641dbd545ca41ddd835ca419ff805ca419fd8794a41f3d5494a41dbd545c2419fd80dd5419ff805d5419fd80dc941bbf80509419fd82dc141dbd42dc141ddd65dc931ddd64dc931ddd54dc931bdd8198931ddf7258931bdf8158931f5d5494931bdd8194931ddf7254931bdf8154931bdd8590931bdf8550931ddf7250931ddf7258531bdf8254531ddf7254531f5d52545319ff805d621ddd835ca219ff805ca21b7f8558a21ddd744ca21fcd624ca21bf78054621bbf845d9219fd80dd1219ff805d121aff8655121ddf765cd21ddd765cd21ddf745cd21ddd745cd21bbf8458521fd57394521bf58094521fd57354521fe54254521bf78054521bef8254521ddf754c521ddd754c521bdf824c521fd5514c521fe78648421fe58648421fe78048421fe58048421df9865c0219fd82dc560fe72188560bbd8408560fe52108560bf980085609fd81dd540dbd54dc9409fd81dc940f3d5494940bbf8550940df77154540bbf8550540bbf8250540dbf7250540df771c8540ddd865c630ddd855c630ddd655c630ddd845c630ddd645c630ddd545c630dde825c630ddd825c630bdd8298630ddd7298630bdf8258630ddd7258630ddd7158630bdd8494630bdd8294630ddd7294630bdf8454630f5d5454630bdf8254630ddd7254630ddd7154630bdd8590630f9d5490630bdd8290630ddd7290630bdf8550630bdd8550630bdf8250630ddd7250630f9d4250630ddd7150630bdd8588630bdd8488630bdd8288630ddd7288630fd55188630ddd8748630bdf8448630bdd8448630ddd7148630fd65148630fd55148630bdd84086309fd8798b10bf58198b10b7f8558b109fd8794b10bf58194b10bbf845d910bef825d510bec825d5109fd82dd1109ff825d110aff8655110bf5819c910dfb805c9109fd8798910bbd8498910def7298910bf58198910bf98098910b7f8558910def72589109fd8794910bf58194910bf980949109fd8790910afd8690910bf58190910bf980909109ff8750910bbf8458510bfb80545109fd87c8510bf980c8510bf58288510fe64248510fe54248510ff38048510bfb8048510bfb8250110ff12150110ff22148110ff12148110adf86551319de8798931b9d8498931b5f85589319de87949319de8790931add8690931bd78150931b9f8458531bd7814ca21bd8805cd21bcf824c521de78748421ddb835c021de5215c021adf86552309df825c6309dd8798630b5d8598630b9f84586309dd8794630add86946309dd87906309dd8788630dd57188630fc721886309dd8748630dd571486309dd8708630add8608630b9d8408630bd980086309ef825d510fe121481109e78748421de1215c021 else 0x70201000401000401000402040200082a0b10041004001004001310061060100f0020080026202c40184010004010004010004000400100000c407000d0c101885f0b0008000004201a12002c082012410080020cb00200f00284e0700180c3800a43002bc00802000803c0082b81c006110586c2081408108c0e00313060202860854104820d04604305804200008909060b1010b85586c2118e0b018e131182c00c01870b0981c00784c0e003c20381c001030102c40184010004236207c300060c2010000a82206230830e30c20034c2080620214042c1408020d1286160c0a10342040008344a185830188420b02081430406217c20083420b0401148810001201000000208581002c14080208014040218200040011041c061c20080022083c0c385c0c385c0c38400040016030e10240c410c43c0080801000780c384002482060c1287040780c38404a18401000441030487040401000580c38441030487040400c38580c3840d4384010004094384092081830042150810870843804386088384230a84098385c004c1c3c061c20021c224e030e1e030e10010e10550e112701870f0e0e030e111f86148489c4e1f0b1388230c8923d0210205c2bc7e270f85c01d8109840617e270f8415a38d80c085c30a418300050224603021e0302100028112301810f8800a10504408009018182816009248c088160a00030a2182c01249019249180c08849c012030c124901f030e10242bc00b8220e371f8817e185785c01c43c40bf0c2bc2e00f1708ac4502251119880c3ca1b50c2855424a10706b829c1120590147fe3f91fbcfc67e03ee9f68fa57cb3e1df02f697ad3d51e9cf487a13ccde36f0c7833bdddbeec7757ba39d10e67730b925c62e196fc37a5ba2dc26de366db06d7d6b7357daa0d2f68bb4459f2cea66db2c5944c8a634b145860c0f6002f7d7a0bb85d02dfd6f2b6a5adad5569eb4058fac1d602ae9571ab5158aaad54f29f54eea6852ca94d488a2350ea8153ec9f04f0a76d3869b44ce26592fc9784b9258d2ba9574a8a50926692d48aa4192008f1475a3711ac8be457a25d0fe87042c21010508224051fc8fa27b93cc1e00ef475939c1c80e106f036c1b00d5069033c1980c9063030c1800bd05c72e096a4b225702ac1500a50507277935c96c49e24311b889a43e2130ff07803961a88cc05e82dc15d8a8c50426a12908c440e1e60e7069030616b0a504801fe0de063022808a000dd)
def g239H7 (j : Nat) : Nat := 0x72a001e280031e0000000000000000000000e4d2bc00000000000115510000000000000000000000000a1400691000000478008ee002c98170000024a80003210501000b24002f9bb166d47c00000e1600115eae00000000527000000000000004f80000000000000000c7600000000000000000000000000000000000000072c3800000000358000000000000014000000000000000000269f8c81e2d431dce980018ce90d0300142016800d0ce3a0380003a08e9aec366423400000529cfc00000001cdc0000015200000000000000000000000014de70000000005d600000394000b404c112800c12000a12f847b6d0004bc00173c00000000002a300000000108000608a905c63a30428430017d8000002
def g239D8 (j : Nat) : Nat := (if j<1 then 0x443504f86481d25091142193c6494250444386481d25210b11410e18749434fc44286481d0925110d213e187494544434286481d15110d092522187454443424986481c3014100b010e1c5c8c0870c1b10342014100c0b00561c9221715c00887183014100b010e1c5c8250c0905040243c0871728342414100f010a1c3090d0905040342c0871524343014100807030c84922210d0c05040302c0872857005e1c8450908c0211787182217001d0854609211715c022080720571e0c145e0b00717c71008c00f1a231c43003c517c78308c00f1803130c581c906c7c417c315c20908c024402423003c51b0cc7c417c30908c0271f105f0c570b00208c417c315c2c008092127130f0850185fe57eb3f0df40f897bd3d9dea0f397913c3dde0edd7653acdd28e7972f391dc68e2170337adb90dad6c735ddab8d45697343d9f0cdd663329d920c7962f311d850c196032f9d7a0bb55cf2dfd6d0b5159f2cad630b015732b1d568a95541296d468a114fd275d3609914bf255d260915477232d16088d43b218d0a082d4071facf907a93c51ddcea874138d1c2cdb86b534f19dcca062930517ccbb05b12c315cca9052928513ac9a84ad24511dc8b844d21b105c7f83dd1df0e7c7003611a10c8c6002ed1630aac51025d11b083c3d01bd0d3062c2e014d097044c1f80e1063027c11006101f005c000ffee8a8ffd42547ffb82a3ff94a41ffca4a0ffd52507fea8a83ff59621ffac510ffd52887ffbb243ff5d921ffee890ffd74487feb2243ff55121ffac290ffd51487fea0a43ffdc121ffae090ffe21583fe90ac1ff08560ffca4a07fd52503fea8a81ffc8540ffa42a07fd65c43ff31621ff58b10ffca5887fd52c43febb221ff5d510ffaca887fd74443feb2221ff55110ffce4887fd72443ff31221ff58910ffca4887fd52443ff21221ff50910ffac2887fd51443fea0a21ffc8510ffa42885fd72986feb84c37fdc961bfee0b0dfd74946feb94a37f5c251bfee8a8f7d54546ffb92a37fdc151bfaeb20fbd54906feb94837f5c241bfeeaa0dfd75506ffb9283ef50941bfee0a0fdd654c7eeb2263f755131fbcc498fdd624c7ef29263f754931fbc8498fdd424c7eeb0a63f754531fba8298dfd75886feba4437f5ca21fba6510ff551886feb84437fdd121bfae890fdd73487fb28a43fd54521fba6290dff70486feba0437f5c021bfee2b05ff75502febaa81ef55140bfee4a07bd42502ffb8a81ef50540fbac9187dd548c3ef30c61f758630fbca3187dd518c3ef20c61f750630fbc43187dd218c3ee10c617f5d710bfae9885fd72c43fa90e217fdd510bfaea885ff74442feba2217fdc910bfae4887f621443fa90a21fe50110ff240884ff76552bebacc36fdd1619faed28ddf724c7f390c433f5d821b7ae810fe521086fcb8043775c630 else 0x83420d0c350854383400d4710250e0a050601002084341401b0c150c6c3030d0c4382110e06004c5c54381800529150e06005c745054144c010a4a0150d0b011074142c015106f0055084428180121515110a06005c785474442818005281836042700210c6428180151b142423011c42221c0471212060100149c68481804005271a110d0a060100149c8438180400c231874350c0a0600307088180231514220601008c5468180402315150e004e1c145054442804087151d0e021ca4145094380400887190e021c743452827054244c0871c94350f021c54380130587148c6c310b021c642801205871435110a021c7854721c0870c8887021c4444280402109871d0e021c14a45094380402187190e0074361c5094442804021871c86021d0854505428028871436010e1c480151b87120100861c4090887c0211404184300203c60d090301c00f211c1b0040a040d090503c047281d3f00306c4060504020115c0081724241410080457020c849090604834f42c015211300545c7c50c050402c783c01720343024140b13020d1c90806048fc043171d1302207c4010d060503c408c082243424140c0713020884906048fc0171b1a3c190e081413005c5490d0c06050403c01b205e1300243c5460d09050403c0471b210e021d4d3c58087525011121c557c408444280504f874920210e0111421d3c742801550c4438749210e0111085525421c843424f444987151c21110d3d0a1c547428750281124554313090c221c84f8715241030201814100b010c5c9c00c1b0c04201814100c08545c2700b8584820017c30947882617010c205c50d0504030215c0084724341814100c050b005491b0d0605040342c01527130f090226211c71d1585c01714242217010c5c6898584838240150847242420343014100c0b011ca09c00c1b10145c57130f0b0024211ca0d090301c00f271c20120b023e1c5c78f0005041787151d13021c7c5450d0c08050301c4c023245e111300243e1c54801c01523102113003e1c5468652500d252112197c5494)
def g239H8 (j : Nat) : Nat := 0x31b731ea7cf63000009692ce9b800250101401b590014074a43b92e7c33658753118c000252f587212d84000a340000000000000000333c00049d1cfc00000000019bfe56000b39d03887c2757927574000000246f88bd560009162643148e9d0000001d51aae8a8b5cbc134a5a11810c4cc44880450be31c217049e86a815f6695a000000134b599800014600000010b8a312761be8001c71259454bb144040006260e6012c0b2a2e8000000c3b1b7011b8568c4e2860d4000e3ac3d4972670532019a16aa79d4e48d22e800196c550a104001b36a47183686946e81800034a3accc38da280000001cad6826b60000001ab6761074f07982e8089688c6d28a5704b3c4e0000000016e3cc4d2121fa61380262a0a520842d1e159241534a294e049a4d31435080d67af94cb0b6a39c49f44381f5134578d63800c42864b65b97b04fb75758fadc89d30875fd03388a33b696e129d2af4d54f7ca24728afb2df0f6902ebbe30f159c2106000051ef534000f9a800367dcbd5641897c65f64455126f4d4f55a2a9d4a744000000604c00144290dc20a123a1cc1e0542c0c6c07cbf4a7d82205000330e30942664928c54e5e8b446356bcd274fc314cc400063f65b0003ac277e49196c786fe11c6389f88d89ad314daf80bf020a3fc6af002cca75e2a3f373886201c13f4a94874095877a91e47a1544ab72600013e887b0ce12590ffd7cd06d1d4220003f67897632b29d9580b50005c8703049f000403030455001507640b02446f1c1e95280020013219026800160f1105000101200119041916010f100f00030104011303050302000d02043a071a02051d0d07000b080002
def g239D9 (j : Nat) : Nat := 0x8ac7804880c24404045cac7807c912101818e404401e489042024721007905c48402563c288401c010609111e144205e003244818f0c7c40500412244028f0e20c363e01414095131e2438500414042c7890e109110090a101822e1cac7890e1098020e1220240201c78e2442305021c41e54394242c02b121c2101c912202c0890e1210e48011121c20e344870830914205bc6710cb974aa44b0830e395f2503704b852044003fd64ff553fe61ff587fe51ff547fe41ff507fe21ff487fc21ff583fd40ffc43fd10f74c7de30
def g239H9 (j : Nat) : Nat := (if j<1 then 0xe8f0000000000000000000000000009680000000000000000000000000000000000000000000000000000842039e84000000262a0000000000000000000000000000012a000000158282e800000000000000000000000000000000c6f0000000000000000000000000000000000000000000000000000000000000164b0000000000000000000000000002c8000000e2c000000000000000000000000000000000000000812ae180000000000000000000fad8000000000000000000000012a8000000000000000000000000000000000000000000000000e3a5d92c080000000000000000f4289400313720000000001376000000000000030d80000000000000000000000000000000152f09374af512000000000000000000000000000007178000000000000387c000a2100000b50480000003508000000000000000000000000018ebb1b00018f4000000000000000000000000000000000000001e5000000069700000004190000000000000000000000000000000000000000002ca40000000000aa4000190800000000000000000000000000000000000000000001a000a1700004ca000000000349ca1e00000000000000000002e3e00000000012e800000000036fc00052f0000c22c41b30800288e08300000000000000000000001323718c09c0000000000000000000000000000000000000030dc00000049af04400000000000000008bee02c0f40000006223d1a0000000000001802c3400000000002248000000000000000000000000000030d4000000000000140800000000000000000000001c700000000000000bb80002af400000055fc000000000000000000000028c389582300000000000000000000001e7b0000000000000f050000001869000000000000000000000000000000001d18000000000000160379880000000000000000000000000000000000000000000000000000000000000000000000000000001b4000000000160c00000000000011040004b18000000235000000000138800000000006510000000c740000000000000000000000000000000040a000000000051f4000000000000000000000000000000000000000000000000000047c000000000280e0000000003e82000000000000000033980000000000000000000000000000000000000000000000000000000832000000000000000091c0000000000000000308000000000000000000000000000000000000000000000000e40000000000000000000000000000000000000000000000000000000000000000000041a0000000001267000000000000094580038840000000000000000926116c0000000000000000000000708000000000000000000002000c1290000000088200082023008202240003 else 0x7ccc4ee00000000034be000000000000044d5b10000000000000000000000000000000000000000000000000000000000000000000000000000004014000d4e00000000000000000000000000cc580000000000000000000000000613c000000000561cedea150000003c5241263884742800000000000000000000000000000000068ef8f0573000000000006300000000000000000000000056000000000000063f000000000000000000000000000000001e0cc04800000000000000000000000000001402000e39000000000000000038f20000000002b02000000000000000043e00002b8000000000000000000000000000000006a000000000000000000000000000000000000000000000004b080000000002b2800000000000000000000000000000001a140000000000000000000000000050980000000000000002c6e00000000000011000000000000000000000000000000000000000000006a0400000000000000000000000003e7fb43e450000000000000000000000000000000000000000000000b6ea81ad21468000aa50000001c6c2b014de61a0000000001cec0000000000001c57000000000000000000024a6000e15800000000000000000000000000002e3c000000000000020e000000000000000000000000006218002cc000000000026d0c1d000000367c000000000000000000000000000000000000000000a1e0000000d1c000000007e0000000000000000000000000000000000000000000000000000c62000203da260000000000001c46000000000000094310a9288000000000000000000000000000009b580004880000004480000000000000000000000000000b0000000000000000000000000010640000000000406000000000105a0000001e68571b438002466000e246998000c360000002c2c0000000003c2e000000251811cf7779800000000000000000000e0000000000000001228003cfe0007130000000000000000)
def g239D10 (j : Nat) : Nat := 0xe2061002ff
def g239H10 (j : Nat) : Nat := 0x7800000000612d5ac40050e0069a0015200000006040030a001c347800004880000087399a8046645db65fd4d6287346480048cc570200260370002007f
def g239L : Nat → Packing
  | 5 => (2,5,6,0,0,3,0,g239D5)
  | 6 => (64,4,6,0,0,10,0,g239D6)
  | 7 => (205,3,6,0,0,13,0,g239D7)
  | 8 => (144,2,6,0,0,13,0,g239D8)
  | 9 => (17,1,6,0,0,11,0,g239D9)
  | 10 => (1,0,6,0,0,0,0,g239D10)
  | _ => emptyPacking
def g239I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 0 6 1 1 g239H6
  | 7 => lookupWord 19 193 4 11 6 1 g239H7
  | 8 => lookupWord 70 331 8 13 8 1 g239H8
  | 9 => lookupWord 52 1069 3 13 8 1 g239H9
  | 10 => lookupWord 7 47 3 10 5 1 g239H10
  | _ => fun _ => none
def g239 : Forest := ⟨239,10,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P5_0 : block g239 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B5 : block g239 5 0 2=true := g239P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P6_0 : block g239 6 0 64=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B6 : block g239 6 0 64=true := g239P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_0 : block g239 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_2 : block g239 7 2 34=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_36 : block g239 7 36 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_132 : block g239 7 132 73=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B7 : block g239 7 0 205=true := (@block_merge g239 7 0 36 169 (@block_merge g239 7 0 2 34 g239P7_0 g239P7_2) (@block_merge g239 7 36 96 73 g239P7_36 g239P7_132))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_0 : block g239 8 0 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_11 : block g239 8 11 80=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_91 : block g239 8 91 53=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B8 : block g239 8 0 144=true := (@block_merge g239 8 0 11 133 g239P8_0 (@block_merge g239 8 11 80 53 g239P8_11 g239P8_91))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_0 : block g239 9 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_2 : block g239 9 2 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B9 : block g239 9 0 17=true := (@block_merge g239 9 0 2 15 g239P9_0 g239P9_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_0 : block g239 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B10 : block g239 10 0 1=true := g239P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g239 0 0 0 = true)
  · exact (rfl : block g239 1 0 0 = true)
  · exact (rfl : block g239 2 0 0 = true)
  · exact (rfl : block g239 3 0 0 = true)
  · exact (rfl : block g239 4 0 0 = true)
  · exact g239B5
  · exact g239B6
  · exact g239B7
  · exact g239B8
  · exact g239B9
  · exact g239B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 11 := lower_forest (g:=g239) (i:=0) (hints:=1376780289) (before_sound K191 V191) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K191 11 [(239,[]),(247,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V191 low239 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[(0xfb52c240d1b74154668251de00000000ffffff,0x140c040910340444280109824242424242424),(0xf81c3ecf0606eabd142d5066000000ff0000ff,0xa0143e0f0204aab914044066c3c3c3c3c3c3c3),(0x0,0x0),(0x684b1bf1ab012505e58a7250000ff0000ff00,0x328021af0ab012101c18250549494949494949),(0x5861214eb0c85ab30738e3b0000ff00ff0000,0xc4061210600c85ab20638a2292929292929292),(0x46a65ca74619cc5887d0d1800ff00ff000000,0x42a40c074611444087905181c1c1c1c1c1c1c),(0x48b9a6913c9e72a09aca5ccff000000000000,0x48a9a4913c1c52209aca54c1f1f1f1f1f1f1f),(0x2754927a84d3e2baf803a80ffff0000000000,0x2550126880c2a09a6001a80e0e0e0e0e0e0e0),(0x0,0x0)]
def g251C : List ColumnInfo := [(0,64,59,128,8),(64,0,187,0,8),(0,128,27,96,7),(2,0,249,0,7),(8,0,243,0,7),(16,0,235,0,7),(32,0,219,0,7),(128,0,59,0,7),(0,8,226,17,6),(0,16,226,9,6),(0,32,25,130,6),(1,0,250,0,6),(34,0,217,0,6),(64,32,25,130,6),(1,8,226,16,5),(1,16,226,8,5),(8,16,226,1,5),(24,0,227,0,5),(9,16,226,0,4)]
def g251A : List (List Nat) := [[],[67]]
def g251D7 (j : Nat) : Nat := 0xc3802a02feb8c4177dcd20
def g251D8 (j : Nat) : Nat := 0x1218113852871509848a180338b2871830a11203c91618084852481c51218a030b2a11c51023ce80c264cde511f87800ff4cbfd21ff883fd20ff843fd10
def g251H8 (j : Nat) : Nat := 0x1803
def g251D9 (j : Nat) : Nat := 0x1694823b0047f
def g251H9 (j : Nat) : Nat := 0xac00001400000800000000000030000080000053a8000000000044000001ce
def g251L : Nat → Packing
  | 7 => (2,2,5,0,0,5,0,g251D7)
  | 8 => (6,1,5,0,0,9,0,g251D8)
  | 9 => (1,0,5,0,0,0,0,g251D9)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 0 5 1 0 g251H8
  | 9 => lookupWord 2 37 1 8 3 1 g251H9
  | _ => fun _ => none
def g251 : Forest := ⟨251,9,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_1 : block g251 7 1 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 2=true := (@block_merge g251 7 0 1 1 g251P7_0 g251P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 6=true := g251P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 1=true := g251P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0 = true)
  · exact (rfl : block g251 1 0 0 = true)
  · exact (rfl : block g251 2 0 0 = true)
  · exact (rfl : block g251 3 0 0 = true)
  · exact (rfl : block g251 4 0 0 = true)
  · exact (rfl : block g251 5 0 0 = true)
  · exact (rfl : block g251 6 0 0 = true)
  · exact g251B7
  · exact g251B8
  · exact g251B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 10 := lower_forest (g:=g251) (i:=0) (hints:=1460666369) (before_sound K239 V239) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K239 10 [(251,[]),(253,[33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V239 low251 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),(0x32d1bf146811d81721d97620000000000fffff,0x32513e106801500720c93025314c5314c5314c),(0x8aa601fc2274ce88ac0fa5500000003ff003ff,0x80a201ac02748e880c04855a0e83a0e83a0e83),(0xd8c03f25c5c327d2fe28e0f00000ffc0000000,0x88c01f2545c327d0aa28603354d5354d5354d5),(0xd445281b889ec12e5f5499f00000ffc0000000,0x5405201a881cc02e555499ccab2acab2acab2a),(0x6d9390805debae3845d6431003ff00000ffc00,0x4d80808015e28c3845124310cc330cc330cc33),(0x6a6cd6ea9e8415f7a032190ffc00003ff00000,0x6a4c94409c800177a0120800f03c0f03c0f03c),(0x952a4f3b5578326d10e5b80fffff0000000000,0x90224b3b4018320010e5b00f03c0f03c0f03c0),(0x0,0x0)]
def g254C : List ColumnInfo := [(0,8,230,16,8)]
def g254A : List (List Nat) := [[],[67],[82,118],[82,67,118],[33,101],[33,67,101],[33,97,81,117],[33,97,67,81,117],[81,33,114,98],[81,33,67,114,98],[81,114],[81,114,67],[97,117],[97,67,117],[97,114,82,81],[97,114,67,82,81],[113,82,98,33],[113,82,67,98,33],[113,98],[113,98,67]]
def g254D8 (j : Nat) : Nat := 0xff
def g254L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g254D8)
  | _ => emptyPacking
def g254I (_ _ : Nat) : Option (Nat × Nat) := none
def g254 : Forest := ⟨254,8,fun i => g254Y[i]?.getD (0,0),g254C,g254A,g254L,g254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P8_0 : block g254 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B8 : block g254 8 0 1=true := g254P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254T : checkedTables g254 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g254 0 0 0 = true)
  · exact (rfl : block g254 1 0 0 = true)
  · exact (rfl : block g254 2 0 0 = true)
  · exact (rfl : block g254 3 0 0 = true)
  · exact (rfl : block g254 4 0 0 = true)
  · exact (rfl : block g254 5 0 0 = true)
  · exact (rfl : block g254 6 0 0 = true)
  · exact (rfl : block g254 7 0 0 = true)
  · exact g254B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254G : graphValid g254 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 9 := lower_forest (g:=g254) (i:=0) (hints:=1376993568) (before_sound K251 V251) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K251 9 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V251 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[(0x91a30437000000000000000000ffffffffffff,0x80a00003090090090090090090090090090090),(0xcb0d1e60000000000000ffffff000000000fff,0x30d1c6050c50c50c50c50c50c50c50c50c50c),(0x1840c28b000000000fff000fff000000fff000,0x1840c288a03a03a03a03a03a03a03a03a03a03),(0x2fc4d91c000000fff000000000000fff000000,0xb04891c325325325325325325325325325325),(0x664b7820000000fff000000000fff000000000,0x644b7020c4ac4ac4ac4ac4ac4ac4ac4ac4ac4a),(0x44342349000fff000000fff000000000000000,0x44202301073073073073073073073073073073),(0xc50aa4c6fff000000fff000000000000000000,0xc502244607c07c07c07c07c07c07c07c07c07c),(0x879a998ffffff000000000000000000000000,0x8598898f80f80f80f80f80f80f80f80f80f80),(0x0,0x0)]
def g255C : List ColumnInfo := [(8,0,247,0,11),(16,0,239,0,11),(32,0,223,0,11),(64,0,191,0,11),(128,0,127,0,11),(0,128,31,96,10),(2,0,253,0,10),(4,0,251,0,10),(0,8,230,17,9),(0,16,230,9,9),(0,32,93,130,9),(0,64,59,132,9),(1,0,254,0,9),(32,128,31,64,9),(64,128,31,32,9),(192,0,63,0,9),(1,8,230,16,8),(1,16,230,8,8),(2,32,93,128,8),(4,64,59,128,8),(34,0,221,0,8),(48,0,207,0,8),(68,0,187,0,8),(80,0,175,0,8),(96,0,31,0,8),(96,128,31,0,8),(128,32,93,2,8),(2,128,29,96,7),(4,128,27,96,7),(6,0,249,0,7),(17,0,230,0,7),(17,8,230,0,7),(20,0,235,0,7),(36,0,219,0,7),(130,0,93,0,7),(130,32,93,0,7),(132,0,59,0,7),(132,64,59,0,7),(34,64,25,132,6),(68,32,25,130,6),(38,64,25,128,5),(70,32,25,128,5),(162,64,25,4,5)]
def g255A : List (List Nat) := [[],[67],[33,101],[33,67,101]]
def g255D4 (j : Nat) : Nat := 0xe500719c470cb969d2154110
def g255D5 (j : Nat) : Nat := 0xd8a04003f86081f47bc87d183e4eff0c2e5b33539a80072036d9b46cca865d21543a01b88e1970cbf2c90aa1d441c670cb969d2154110ea80e23865cb4e90aa0886b08758ca6dd2154140443201b88e1970cbf2c90aa19501c470cb969d2154110
def g255H5 (j : Nat) : Nat := 0x80
def g255D6 (j : Nat) : Nat := 0x20b052656282ec4fc308002c441000000e86040b110400000000000002d304000000000009d04d2bf07c305644007241f0607977d1de47d1bf0ee406f477c0790fc1f4617d19f0ff07a304f1034efc1fc0f118281ac4713b237f03f06c42d4c7f0c7c3fc1fc042817275f03f07f0c4e127c5dc1fc029d17c43d0bf07f02277c446e112cefc1fc0e108281bb0bf03f0f87c49252323d45c87d0e219420835052074087ecfc1ef3d87a4f31e33c0774ed1d73a872ce41c53846fcde1b936c6b4c918f30c5f4ab1352343cc630a51141a42101b000d2a7b2e85a16438650ada8f01b4e8590e1921a2aecaed3a264386487a136d9b32a19748550e90db46cca865d21543b88e9ba4e859048550e62bb4ec9a0e5921543a1cf05202a17158150d663b6ec5a26462054350b718b969d2154140c2aea8ed992e53824430e9aa3b164b94e0910d12db76d498e09424430cbae9b52618250910e22dc5263a6609424428abb2898e998250910e325c5263a160942442b8af19a2e938254110af23c168ba4e095044328eaeba6e118254110ea2ba6e938260950442acab2b84e098254110ea2ba6e138260950442accb2b84e858254110eb23a2e13a160950443a98e9b82e858254110eb23a4e0ba160950443a4a71ca8e0942541108f2acb2a1825095044338a2a3b66094254110cf20a8ec58250950443788edbb16094254110bb22c8ed38248550443519718b969d2154110da6382ec58258150442798b20ba4856054110cd29b76d4a8509204432436d1b32a19748550d04dc32e197e592154341a718b865e9048550a864c86dda124960542a1cf05202a17158150d461c62e5a74855044355070cb969d2154110ec21a7e9b8448550442919325a7e992154110b460c96dd2158150442b48329b74855050110
def g255H6 (j : Nat) : Nat := 0xc50000b3002100b4100000000000006600000000000000000000d20000fc000000
def g255D7 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x3db1c1742c12a0886f2bb4aa08254110de5551c2104a8221b4e6dca85095044379454704a12a0886f28a86094254110fc576cc1284a8221fc8ec58250950443f91da70490aa0887f2384e092154110d4df4dc1304a8221ad9e0ba160950443f31db34090aa0885e6ab82896054110f4d704c12c0a822179cec58258150442f355c104b02a0887c6b825c96054110fcc705d0ac0a8221f98e092158150443557d3704c1280886ba782e858250110bc776cc12a0a02217ccec58254140442f955c104a8280887d2b825c95050110fe470490aa0a0221bb8e9ba160a204436d4db950a1240886f29b52a142481109f6774ca72290221ee8e1382e4520443f90aa705c8a40885fa0b850b9148110fb434eca24290221f6869f8448520443bb1c1722a8240887b6382e455048110f74705c8a8090221f686dd2150120442957d9342c870ca17ca3a15812050971c7c763d4b00402438f8ea7a1600804871565cb41c328490e5a594e8572a0121cb4f29d0ae4c024345dec52026171543436db150cba42a8694db32a19748550dc5768d072c90aa1b98ec5a0e5921543715d3748c8242a86e63a6e859048550de4749d0b2090aa198eed1a0e5921543335d9341cb242a8686fb7aa09258150d0dd51c3924b02a1b196dda124960543633c3b42492c0a86e61b068492581509ccb6354f04b02a1a1e480a85c560542c375c124b8ac0a85c65b12497158150b0d970d3a42b02a1798ec5a048560542b35db344c8c40a85763b16899188150ca5953c92e4a828154b2e5a748550502e93d8ae490aa0a052afb664b94e0910e64f22aa704c12210ebae898609424431564c74cc12848863a498e858250910e94b2fcb70890a2199969792e4560442f14db749c12a0885e29b6e138254110d4774dd2304a8221acae8ba46095044351dd3708c12a0886a6ba6e098254110ce5553c2104a8221acaaa3842095044359454704a12a0886e2ba6e094254110bc576cc1284a82217c8ec58250950443e90d3f0890aa0887e23a6e112154110be4365c2242a8221ec8e138248550443e91c22e490aa0885f20b85092154110aac972d3a42a8221b1969fa648550442f30d874c90aa0885e63b66812154110acd572512c0a822169aae0a258150442f30d8944b02a0884e6aba2096054110acd572412c0a822169aae08258150443c35c12e4b02a0886e63a2e856054110bcc57490ac0a82217982e92158150443e30dba42b02a0887c61724856054110d94b4fd3242a02213caae88254140443e90dba42a8280887d21724855050110b74170a172290221e6869f84485204439b1c1722a824088506cb865f9648550a2d170cbd2090aa194a65da4a412154329454328b9440a8652994e857288150aac172d3a42a8221b1869fa648550443c91c22e490aa0885e23b65092154110 else 0xe68359db67299b966a198c65c195464b591163d58ce62c9880619184860b18055fa57d85f1d7a05e117735d897515cd56ed5aed689595d60f56f158a55094ef524544950313da4ea138c4d3d31d4bd92ae49c523447b11af451910943050634098fde3e84f6f3c70ec93ab4e91397ce3837ecdb33580d183340c9e31b0c242fc8bb52de0b3b2bccab629e4a1b274c99625648f022a085520347c51df47351bb46a51974615178c5b11578516133848610a03d50e8c3450b9c29f093021a07741a005b814704280c202140480003793d1722c8a40aa72afb268590e1942e56f42d0b21c3285fa8e45915812050bb52da742c870c90f5a5876939160121ed4f2cd2722c0243d6961f94e4580487b53cb729c8b0090f3e3b1ea58020121e7c753d0b0040243cabed3a264386487957d2744c870c90eda794e857260121e36b0ed2722c0243d6969172e4580486bd3dd285c8b0090f1e587e4b9160121eb4f28b9722c0243c5dec52026171543733d8b41cb242a87e2ba6e919048550fcc74dd0b2090aa1fc8e93a164121543733d3742c8242a8666fb26839648550fcc762d0242b02a1d9aed9a264620543bb1d8b44c8c40a86e3ba6e919148150dcd74dd1322902a1bcae93a264520543753d8b41cb242a06da597e859048540dd4f4dd0b2090a819abec9a0e5921502ed3d8ae4c8242a065b597e859048540db4ae5d0b2090a81be2e8b8364520503755d3744c8a40a07f8383e452148140e55f6cc9729c1221ce9ec592e53824431d754325ca7048856afb664b94e0910af4f62c9729c1221aeaaa120e53824435d3d8b45c27048862bea9e5b8460910e55f2dd2704c1221ce9e47a4e0982443957cb729c13048853aeb9e138260910e55f2dc2704c12214edae784e45824439d3c9709c8b04887727925539160910e5cf2dc1722c1221ce9e5382e4582443d92aa705c8b0488653da76949850910e35b6e4c704a1221ccb6d498e0942443d53d3742c12848853aeba2618250910c75d744c304a1221ccb6d498609424423d75d130c12848866ac98e998250910e55931d3304a12219e9263a1609424439d24c742c1284886ea7a6e858250910db4b2ed170890a216e9ae3a4e0921443cd2cbf09c12428867a6b92a14248510de4b6a5428490a216b96c6a9e0960442772d8d53c12c0886e65a5e0b91581109dcd7054a42b0221bccec5a2e1150442d9d5c749c12a0886f29a2e938254110be5365c2704a8221e8ee9ba460950443d39d3742c12a0887b33a4e858254110dc774dd2304a8221bcae8ba460950442d9d5d708c12a0887a3ba6e1182541109e7575c2304a8221b8ee9b8460950443799d0f08c12a0887a6ba6e098254110f65749c1304a8221b9ae9b8260950443d95c2704c12a0886e73a6e858254110de6749d0b04a8221ecce13a16095044) else (if j<3 then 0xd8609e0e110ba07860b88d06e801f40c3e1740c3e100ce81c18341861c223a71fa0586120ed110b867060a08f060b8620c1941953c0c168607430314ee021d0e29a1d0b08834181a0c0ec023a160bf8861fe17c0b8c345170de17e109f0e28fc105027c34a3f04140922fc37c4f85f00a88c06f627c3f80d25a64291c0dfc06a30a44f83f03e1dc74456446f1862b62099f83f01140f977a3bc0e8db13e0fc3720458cf88f07e07128ba3312f81f13e085d16e4fc4e248a04f89f068902813e24290be23c1f81c4ba38bb0fe0fc4e2427c178a0a43b8b713a1fc1f046486f05f03e0bc50522bc5f81f07c10291725fc1f81f11888291bc17c0f83f10148a3718844ef83237e06c6622d4c9d8bd0fc17c15462ec5f81d0c147c1054345de2053ae27c1f81c461411f07e07c45240a05c19f07e01cbf89a486f83f03e1fc45242f422a5c7c7289b1fa17c0d8d713e1f1f1c7209b1bbf0fe0252e223fc2d2217c0b2217c4f81447e109f13e13110ec37c4f85f01888bb07e03c5f84477488dd0fe0686f89f0629aca1f63f0c397f13e07121b63f0c397f13e07121b63dc1f89c484b93f0fe271211e1fc4f80b2f63f121965fc1f89c484b83447e27c04522d11f81f13e1f1217e0211f89f0f890b31f862cbf89f03890c72fe27c0c23c485387f13e0312c222d11789707e029d78bf0f0911707097c0a23f114e8c707067c4f808a451a7f0188fc485228d3b88f064edc5623f03e1e1227067c4b82727e04291b885c4e85f07e0029e223fc1c25f004ebc5e2237c0c25f07e231113a37c1f89f030951105034cbf83f0308fc4052360cf8132fe0fc4e2437c1f81f1308b1205037c1f8034fe2611e2430d3f83f0308fc405230d3f83f13890834ee2fc1e2425141a784761fc0a25f047f83f03e2512c220a06f83f1308512c220a06f83f01e2e11a240a0613af15e27c1f8034f08d1220e7f41f8172f437c278a3fc4c23f005488476c3bc4f80f17e1c92c224187788475e2fc0f8724b0891a1be26c3f81f08900d62ec4fc0f86875e2fc21fe1fc1f89248438be0be07c18ba2f46d19f03e0fc31664bc5f87c484f80e493287315a4fc0f876485137c33a17c1f800a4613af17e07c1c242dc4713f03e1e1217864c7c2472fe27c01a63f988e61297ae5da97265b8969e5a195be53d94b251093a64cd92c64a091e646890da41a8ffa3e28f1a39f8e0e35c8caa3038bca2e18b422bf8aba29289da24f88fa222884620087921d386de1a6865618485a2157851a135849211383b20c582d2098821e076819605480e2027802dfef7f79fc27ec5f957de5f737d89f517d01f247c21ee17b41eb47a61e7c79ade397875e017795dc976e1da77659d8575a5d4d74f1d207411ce87331cb07251c78719dc5670e9c1e6fb1bc56e79b6c6d99b3f6c8daf16ad1a776941a1 else 0x1098a184098138d30ec087d0c143a0dc00514820028f87f0628880a128fc3f82260b0705bc10a52b418521d5fd0c119350c11ca0414e517841c2906e3946f836444996d1c2d197042787f042f86f042f82176a3866462585447e085d0f08ec6387f044c23f0fe087c301d8c0ec605a3821741a8de002f0112c28a7b0c0e87a7c103ba442d8c0ec6050f4470b6082477608451c1f0c098606c6786086082a4412960c5306e08252ca0f860ca5dc1f0c199104a9e860b4303a4414820c1d07c37410b43039068885075e185f0c1f854442a220e47f0c1349f0c101618183a0d86049491d080ef0c0914a1d8a61a290760f0c0be08290be08290b4302327437c1e8620c1992170cf0c12c7182160c38215c105e182f041a220b0cb8211cb58011cb04659110865d110a69a0c0961fc10960dc00a867860869cc00a8882c4415a73002f87f0421a7c31e0f861069f0cb821f0c993e183b0ca1960f0c10098e70f6087f0f608434e639c1d0c20d359331f433c11688acb787f07c30bf0fe0f110e639c3f834444c220c1142332e61898441c220a0c0708))
def g255H7 (j : Nat) : Nat := 0xeb013800d030b8000002565b00308243400109a80741c880072400102c00000f10c400bf290002be44c28d09a17cc826e460012488c8880035281800126ec972da29e7000611a2a0398fa8a40e279508000000008edaa001e0c0048de2c0000010fd2463ab42800d60
def g255D8 (j : Nat) : Nat := (if j<3 then (if j<1 then 0x2158110f395c92158110bce68b8454110fcae938254110fcae138254110ecee138254110e9ee998254110ecee918254110edce858254110b9ee998254110ecee118254110edae098254110bdaaa08254110fcae108254110f4ee117254110f5ae097254110bce2a14254110fcae094254110fca6094254110fcce112154110fd8e0921541109dbaa48254110adbaa08254110e5be097254110f5969d2154110f99e992154110fd86812154110f595c92154110f9ae896054110f9a2896054110e9ee096054110f9ae096054110e9e6096054110f9a2096054110f1e5c96054110f9ce856054110f9c4856054110aebaa08250110e6be097250110f6969d2150110fa9e992150110fe8e812150110f695c92150110fcae095050110fca2095050110f4e5c95050110fcc4855050110bbae998288110bf8e858288110f7869d2188110eeae0b8448110fcae095448110bea2a14248110fcc5539148110fe850b9148110f7869d2148110fe86512148110fe8e112148110cf9e0b9148110edae095048110ddce455048110fd84855048110eeae094048110fe84854048110a6b69220e0971e3a58220e097192f6839650971f2a5812050971c3b61d96a0121c6b61d94a0121cabe1994a0121c3b61d9620121c7361d93201218faea58020121bc9e852055121b4be81545c9219ab6839650921aab6838650921cabe199488121d1be5d96e0950c5b263825c950b1b69b825c950d0fe1f9650950b8b69b8250950d8be5b8250950c4f261425c550b0fe99425c550a5b2a19748550d1b65f9648550b9a6839648550d5a65e9048550d9ae5a9048550bca6929048550b9ae999048550bcae91904855099e6839648550d1be597248550b59e857248550b8be994248550d8be594248550a9baa09258150b99684925815099baa7825815099baa48258150a1f2a1715815099b2a52158150d4ee1d9488150b5a2a17288150d5aa617288150b5ae857288150d5a5c99188150d4e6517188150b9ae992188150dca6512188150dd86452188150d5ce457148150dd8e452148150c6be4b825c540d2b65f96485409ab2a56048540cabe5b8248540d2be597248540b69e85724854094f2a57154140baae992188140b9a6979158220e3ae617158220e9a69b9854220aab69b94e0910aab69b84e0910ccb6949850910cabe5b8250910d3965f9648510e69e117248510f495517248510ba9e9942485109b92a52158110b8e69b8454110ecae1382541109daaa48254110adaaa08254110e4ee117254110e5ae097254110bca2a14254110b8ee994254110f5869d2154110f98e992154110fc8e112154110ecce112154110f585c92154110fc85092154110e9ae096054110f984856054110fc84855050110aea2a14248110ee8e112148110fc85512148110d4a6517288150 else (if j<2 then 0xbdde858254110bdbaa08254110f5be097254110fd9e092154110f9ee096054110f9e6096054110eafe998250110bafe998250110eebe098250110bede858250110bebaa08250110f6be097250110f6d69d2150110fe9e092150110fcee095050110fce6095050110fbae998288110ff8e858288110feae099448110feae0b8448110fec6939148110fec6539148110fece139148110ff8e0b9148110ef9e0b9148110f7969d2148110fdae095048110fdce455048110fece454048110bcbe899148154cafe8590e1942caf68590e1942faae456048142faa6456048142f69e852050971dabe9190e1921db9e8590e1921d6b61d94a0121d6b61f9460121dabe5b9460121d7961f9160121de96939160121db9e5b9160121de9e539160121ee9e139160121fc95539160121cfaea58020121ef8e858020121bb9e858058121cafe9190e1921cbbe8990e1921fc9e852055121c6f61d94a0121d6b65172a0121b79e8572a0121d795c991a0121c6f61f9460121d6be517260121b79e857260121c7d61f9160121d795cb9160121de950b91601219f9e859888121d6b61d9488121d7961d9188121f1b583825c950c5f480985c550b9b6839648550f9ae999048550fcae919048550fd8e859048550b9be999048550bd9e85904855099f6839648550f1e4838758150f1be1f9258150b9baa09258150f1be1c9258150b9b6849258150b9baa78258150f1be9f8258150d9be4b9158150f1be497158150f1b2497158150b9baa52158150b9b2a52158150f1b69d2158150f9a6812158150f1b5c92158150dda6899188150f5ce457148150fd8e452148150d67e0f925c540bab6839648540fa3e5b8348540babe999048540be9e859048540dabea56048540dab2a56048540f2b65d60485409af6839648540da7e5b8348540e6b65f8248540f2b5817248540f4be9f9254140b4f2a57254140f4be497254140b4fe857254140f4b69d2154140f4b5c92154140f66e0d7148140f6ce457148140fe2e0d2148140fe8e452148140ceb64b94e0910bab69b94e0910bab69b84e0910aeb68b84e0910cafe5b9460910cebe4b9460910ecde455460910cafe5b8460910dcde455460910cbbe5b8260910ecb5538260910cebe929820910ceba638420910dcb6949850910ceb2638250910dabe5b8250910eabe998250910ee9e858250910ceb2618250910babe998250910be9e858250910d792619748510bb96839648510f6965f8448510fa9e5b8448510fe8e139048510bf8aa09048510e6d65f8448510be968b8448510ee9e138248510fc95538248510bb9e998248510f69e117248510be92a14248510abbaa09258110bb968492581109bbaa48258110abbaa08258110e3be097258110b9d6979158110db9e4b9158110bb9aa52158110bb92a52158110f3969d else 0xdd3982726ce3a9c5e38707020dec1ba837186dc0d9d9b0b35c06ae8d4a1a73349a689cd0599e533886664cbc194d32446404c6b18b0310a617cc1c98182fee5f58bda978a2ed25d0cb8e96fc2dac5ac0b4a16782c905888afe15db2b6a563cab495432a3a53f0a6d94ba2914517ca1c941327da4f1c9d0937b26aa4cbc98992ed257a4a489361246244047e88ec91b8233845ec8ad113e223a440486890ab2100417c81f10181fe43f447d58f8a1ed23d2078e8f011dc03ad47478e641c86389c6fe0dd61b5636146b20d3e1a3a33f066b0ca618ec316861f0c1817f82f6c5d58b8a16d22d0c58e8afc15b62ae854c8a7814ae28ec50f8a0313ba26dc4cb097a12b224f4493090511dc2334456088b10d4212441408110ff41fa03e607ab0f1e1db83a407220df81b9436206ad0d2c19d432c86330c1a17b02e585aa0b1c15dc2a8853a0a46140827304ca095211f8233844608400fe81ef03bd07380dec1ad033e06300bf016d82bf05460a1c135824f045208340f881d00368064c0b401510242040007200b9011c01b401e801c0000fcbe899148154fcde459148154fabe999148142fe9e459148142f6b61f9460121fabe5b9460121f7961f9160121fb9e5b9160121fe96939160121fe9e539160121fb9e858058121e6f61f9460121f6be517260121ded6939160121e7d61f9160121dede539160121df9e4b9160121f795cb9160121fe950b9160121df9e859888121f9be999048550fd9e859048550f9ee999148150fcee919148150fdae899148150fdce459148150f6b65d9048540fabe999048540fe9e859048540f6765f8348540d6f65d9048540f6b5c99048540bede859048540fe6e0f9148140faee999148140fe6e0d9148140feae899148140fece459148140dede8592e1110aefaa394e0910deb64b94e0910fea48394e0910beb68b84e0910ebde479660910eafe5b9460910dafe5b9460910debe4b9460910aefaa78460910eafe5b84609109efaa78460910dafe5b8460910dede478460910ebbe5b8260910eebe938260910eebe538260910dbbe5b8260910eebe138260910fcb5538260910dbde5b9160910dede539160910eede139160910fcd5539160910ef9e0b9160910debe929820910deba638420910d6f69c9850910dcf6949850910deb2638250910deb2618250910fabe998250910fe9e858250910f6d65f8448510f7965f8248510fe9e938248510fe9e138248510f7965d8248510fb9e998248510bbbaa09258110ebbaa78258110bbbaa78258110bbde858258110bbbaa08258110f3be097258110fb9e0b9158110fb9e092158110fcee938254110fcee138254110f9ee998254110fcee918254110fcee118254110fdae098254110fdce858254110e9fe998254110edde858254110b9fe998254110edbe09825411)) else (if j<5 then (if j<4 then 0xfe068be19a22a3c28f89e0050282e45f0de2781e12a23c9924f0cc5f81e2784399fa3f83e0133890c13f8049782328bc168a65f81e0d24342325e8ee2b242f89e0623490923f8888a97e0524358fe1d229109c119763f81a2e243589c6705e0782148dc1780e28bbe0e24331989781e27822e8de0783e1b8b4662430bb46783e0789890de278064c522789e0e24140864f891487e0789e0e8f890bc158aa5f81e0e243705e00cbe08522c8e65f89e0123890c85705e2780a5e8d488f25e19c1781e0853e20fc161814781e0853e20fe00ad88d242687e0789e0e19490de0f81888542781496222e8960f80e2f87a3b243781e0e18c90ca2a97e0f8162843e1b24398b22783e0787863243c19e0f80e2f87490ce0f8162f87a3d24361865f81e0f89490ca4d8be2781148be0788888522619a3f81e1f83629243f81e27821489e1e8de153e2713c0f80e2f842e8de2781e15222e8aa5e8de27854f8bc0d8aa5f81e168c3787c4f03e00bbe173e329188f863163e211763781e2785888d2599586781e2783630e8b223e058d62f83e10ee1f83e0789290bc3197e0789e11223123e278065f85c30dc3385e1f89e0422370ca5f81e2784888de003ae2f85e08ac5c3b62f85e0786c88f0ed8be1f80c88b0ef89e0197e11223781e27840ee222e19e2781891a62a23e0789e1e242e19e2783e00522f81e2783e1e242d8f62d88c4f81e1e243f8162f83e1e242823e2781e1e242e19e278065d8f890d86781e0b8a148b86425e0783e213a313ae0d8fe1f81e24248890c4f89e045223884ee1863b8be0787e0c24493be2781e1c24888c14f81e0f89890b61f824e851e078889422403c8eb8fe2787e0125089010787e0789e170c3618c5d0d0eb13e0789e1f844c8f43789e1f80888dc9293e058be18b8fb31e963a4c7018d4b19762f6c5a58a6b1366234c421878b0d06172c289840b0656092c0c980b2ffa5fc6bf317dd2fa35f18bdc17a7af335e2ebc0176faecd5d6cba697442e715cc8b93571dae245c1ab7ed6f72ddc5b8ab6cd6d0ad8f5af0b5856a52d385a56b45167eace659bcb34565facad592cb1fd6342c515874b0796062bf557c6af1d5d5ab9456faad855a52b335624abed574aad7558aaab95492a7654b4a90d5162a1553f2a79d4e829b95330a6054b52953526ea46d48228e851a2a2e944ca88250e0a1794212821500a9fa53e927bb4f3e9e0d3b627554e869cc538fa7034dd89b69361a6a24cee996d31d260f4bd297212d3a57c4ac09525291a4f849b892d924d247e48ba90f120da3f0478a8ea51c1a35d465a8c3117aa2d945708a49138a2554472884d0f6a1cc435686290b22143424e8405072a0bf414681f502e202c40167f94fdf9f943ee67d20f8e9efc3da27aacf429e643c7c789cf031dea3b9276c8ec39d6b3a9474a4e819c else 0x89e15223f888ef81a3d222e8ea5f81e170de25223b0ca1f89e068f488d23b86a5f81e270de1782470d0ef89e1f80c88c29b83c3787e0789e132240a760f87e0789e170d4891c3385e2787e0422329520f0de1f81e2784889123f0ca5f81e2784888f0ef0da0b87e2781e1622403be2683e0787e16223c3bc3787e278088f843f0c65f89e0785888cc3789e1f81e16223584c6781e0d8a148de0789e0f840eb22338960f808eb8be1f85489160f89e0523e123a3383e1f81e2123e143a3f83e2781e1f844883a3a4745f8148b8a948d60f89e07868ef84488e29c3be0789e1f84c88fe2781e1c3ac88be0f89e0522140a29d88e0c3b62f81e1f84c892657890ef81e1f84488fe0c97e0789e170d888fe0b0de278188850378229f89e0785c362238a7e070de1783e26223f8029f0d62f85e0e183f8343781e219588ca63f89a1f83e00a613622383be0f81e2622140de0e87e262188850303be0f80e2e22140c0eb89e0f804eb8be10a788938618264f89e1f80e3e24438363a23e2781e1e243d8ee0f87e078888e2439a688f81e278763e243b9763b87e0783e26243b9363b83e0787e26243e1963f81e1f89e0a243e1865f81e278363e2439a763a23e0789e1e243f81e2783e1e24299386787e0789e0e2439a708383e1f81e222363e2449a6e0a2362d8fe0787891063e19e0f8162f87890f60823e2781e1d8f890f6098fe2781e1c23890e63d83e2781e1c23890e69b8288f89e0452322343789e0782148de0f89e0622148be0f87e078989622378162f87e0e25860de0f80e2e22148be0f81097898893a3783e278088852298ee27824ef80e2f87096224f83e0587e242269e243821e0997e078908b8f891108f81e2783891a6378214f81e2423890de0f8161f8908e24698e08783e078908e24698fe0f8108b8a69e24378213789e0422891a63f83e0225e2422140de1f89e1781c3622370d62f81e1787888ce203be013be138be1e224789e17818893a2f89e1f85e02224e8ce203be038a4ef85e1e224680e3c23e278708524383da0423e2786e3c214910e2c23e1f80e3d243423a07890f9522c3bc378265f81e278588900e987e0f81e2785888f09783e0786e2f840ee2240a7e1f81e2423e170c3f0ca3f87e2781088d23823e1f81e2785c30fa3d8743789e02223587e050de2223e10d86781e1f82e2f840e8e29b830ef89e178143786889229b8343787e043be27848893e0789e0f85888be0787e0f89490be0e8fe1f81e2125088fe0f89e0422148be1f0de0789e1422303b60a3be2784c3781e1c224f87e0193c3199e10dc2780660a7e178232be25f0dc2e8fe07843c8ee1f0dc2f8028f843f0ce2c9925f85e08dc338b26493e1f84349326781e27848e8dc338b26497e1782370ce2f87e0c99e10c28f87e2781e0850313be2787e04a22e0) else (if j<6 then 0x86e08869d8f61a22221863f0d61d822f87e0a221d3ae1f8388884ef87e0e22219763f0ce1f83888c4ef87e0e22230de1f838889c3787e0e22210fc3787e0e18290fe1f83436222f88e3f83088865b8e61f83088b88907a063e258f836818f884ee0d61c83a06223622c36818f8806681c3068610fc306549478fe804e8a0e90f61e8188d0c3789a0422e3c3e2a92c3b87a043e2987e0c3b8889e1f820ee2220a68620f6070c28a6a3e1960e0c2aa6e050c8f88a9b814323e22a7432221c2288d0c1c0de0e22183a14f83888502a8fa0f0d0889e0b0d088708d80c343e228fe2787e058d888d05d3f08f89e0785c3b8c453fe2781c384c2f8109f8908f84e30d61f03e078909b8d08f84448ec3781e1f0be14a23b83e2781e11a30e8c68f89e0783e103a370ee223be04932638a94908ef8128b8a948be278128a50203be069814f82e2850390ce0c3be1f85e0788a890e1f89e0782140ae0c3be0789e1f84a88ea8f89e1abe140b0ef89e1f80a88a28f87e2781e085034a3e2787e0782140c0ef83e0789288503416e0f89c3781e170e689068c16c3f89e070de178247884ef87e04a22b47c3f80e2c9924a523d890ef80a4a9962c523c2622f87a1589e0f81a88524f87e0f80e2ca2148d28f80e2a52243be058aa8c522f85a678052f82148d24f81a6053e0b8a140f24f801438be08523789e1f80a88502f83e2781288522a4a8ef8124b8b26252383ae1783e038b2885238adc1783e0524328ce3f83e1f8111322378389781e23222e8ce1d1989781e2782140ee4d18e0f81e24523519e0789e08522b87e0e25e0789488503f83e2781488522897e0f81e268f893223f8088d8b492a62f05e0783a1b8ac94a63f83e0325c1788138d08c21e078386496e2d8ec913e078386788c9050370588788a5e23490ac38cbe0f80e2d25c104e3d29e0619a1f89e08a749114938fe0783a18543223a1f8149221e0b8e15102ed2586781e0f89a185042978878949622140c328bbe052586782e28504783e0525a1f888885038bbe052586782328503f83e0423e2787490da3e19e0787e0d8a490fe0789e0852230122f85a3312cf0de2785e03222e8be250144f85482ba3789e05223409c00baa378548f89e1d3e40bbc07894f8d02d87c0197e253e340c328bbe038b488d0370025e8de2785a3b3e3d01a3789e1297a3d3c38cbe138a2ed3e2c3a2ee8de0784c88ca3d8ee2b89a17872963e3f00a963e728863d89a158be1aa58f8e7213662d8963f87e02a588926ed8ee213be038be1ca588926e98ee213ae2f81e1ca58892c4d8d62f848f0a6378762f858f8a0f48fc0cbbe27856378688312503a23c3dc0f89e1781e18ba4a3bc3583e278148f87e111a3f0c65f81e2784488fa3923e278065f85c30fe1f0de0789e1122370d60f81a3f85e25223f0de1d83e07 else 0xbb6305a60ba162261f030e8961d020e869423b20a52238760ca2183ba6782148502b87e08501c3aa8f86e050c2c3aa8f86e0884eb0de083b288a9448294871443aa0c5222bec9f88e043b430d28f821485022a3e2383148928aa3e23821483a30500eca3e08522aa3e1b821403a285128f821489a34bae1f83488a2ea8fe1f83488b86187e0d8c2619e19836309e1f836307865876098c20d1465862e89a3187c043b488a2ea8de1f000ed2232cb402c744aba2ca744d87c053e28a761d222e894fa8de2701488ba348f6323c1e19631870e8929913635868f0be183b6307865874098c26830885c619460f0c270c20a3a18a6c628fc3098628fc3182223ac8d861b876085a3d834886c628fc35822197e19221996a1d221897a39221897a3d83488929b0d60d22243bc3287e0890e8a6a0870eb82151923f83c3090e8a6e0f0c243b4670d23894882e0b22143aa9b221c3ba3b22183b48f87e08829f18e0f0c20a7c6583c309c6493c3682268fc36830888a5483c6283c30aa4f0d0e87c3187a0c3a2787a083a1a5291ca748a3a2853833856083a28a660e19830829b838660c203b60853488502987e0c3b4889c3207e0e222052c938588f83c30de085388f0c230de0e221f0de0e221a1843f0c1b0fe0e2343080e90ee0d0d888a69e1860f0d638a69f0d86383638b63f0c61f82222363f)))
def g255H8 (j : Nat) : Nat := (if j<1 then 0x480c0000000000000000000000000000000000000000000000000000183205300000000001425502e00000000000000000000047480000000000000000000000000000000000000000000014398000000000000030d3c3e00000003182a6d3858a23800000070f400000000000000a2e0000000782a00000000000000000000120700000000000000303600000000000000000000063200000000000c0f8000000000000000000000000415000000000000007134000000000000000000000000000000000014618000000000000000000000000000000000018b0000000000000000000000000000000070fc0000000000000000000000000000000000000000000000000000006502bf040056296a0000000000206880c780ac0ea8780000001e5e000000039aa0000000000000000000008550000000000166c8001c17c83c000000000000000000000000000000000000000000e0380000000000000000000000000000000000000000010fa000000045f800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000068340000001c128000000000000000000000000a35d0a60004848000000020a0000000507d84f8000000591c000000000000014058000000000000000000004166000000000000000000000000000000000000000000000783800000000000000000000000000002168000e08000185c80000000000a4c0000000710e000000046a000104a6588000000000000000000000000000000000000000001e6b800000000000000000000000000000000000000000000146000006430000000000000028840000000c06000000000016380000000000000000000000000000316e0000000000000000000008628000000284e00000000000000000000000000000000001c3fb1100000000000616800000000000000000000003180000001002000000005e8001e3350d0000613600000002158000c37800000000000000000000000000000000000000000000000000000000000000090a0000000c370001471800000064ec00030aa0000000000000005100000000000000000000000000000000000000000000000000000000000000000000000000000511e000000184000000000000000000000000000000000000000000028cee700001604000000058d9e6399420000000000698c86680000000000000000000000000000000000000000000000000000000692400000000000000000000000000000000000000000066f0001c25800000048e8211000000000000000000000000000000000000000000000000000000000000000306c00014ba000000000000000000000c3000002304945a010005000001280000202200010040000002 else (if j<2 then 0x1195e460000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000122d00000000000000000000000000004974000000000010a000000000000000000000000031ba0000000000684200000000000000000000000000000000000000000000078240459192000795c000000000018f6a0519c2c1fc97600000014658000000201e0000000000000000000000000000000000000000000000000000000000000000000000000000100180000000000000000064680000390000000000000000000000000000617c00000000002874073800000000000000001c2c800000000000000000000000000000000000000000000000000000000000e578000000094e000000000000000000000739800000000000000001e3500000000000000000121a8000a7238bf41e800000000000000000000489c000000183c00000000000000000045880000000000000580400000000000000000094a0000998000000060200000000000000000000000000000000000000042a5160000000000060260000001869000000000000000001464000000000000000000000000000000000000000000000000000000002150000000000000000000000818e8ba00000000000000000000000000000006aa1a56d04600050f360b00000000000000000005b0000000712e00011cc00000000000001e1300000000000000000000000000000001032800000000000000102000000103121a600000000000000000000000029be000000000000000000000400712600000000000000000000000000000000000000000000000c20000000000000000000000000000000000000000000000000000598400000000000000000000044f00000000000000000000008bc000000000000000000000000000006da080c140000000000000021060000000000789f25580000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c220000000382200000002746066000000000000000000000e48000000000000000000a620001e4a8000000187000038820000000000000000000000000001e710000000000044ec060000000000000000000000a5261080000000e4c800000000000002940000301a0002086000000000000000000000c14800000000000000000000000000000000000000000000000028a4000000000000000000000e448000036f922a1cc146a5900000000001267000105488a3e3b000101d8000668800000009a000019b0000000000000000000000e4e000000000000000000000785c0000000000000062680000000000000000144100000000000000000000000000000000000108a00038e200000 else 0x14230001c1b800000000000000000000000000000000000000000000000000016240000000611400041b906b00000000000000000145c000106780000000000000000083b80b6204800000039caa2600000001892000000004b30ac0000000000000000000000000001a3a80000))
def g255D9 (j : Nat) : Nat := (if j<2 then (if j<1 then 0xca8240887ee50120442e7f22902a9ead91e1942f57c8ac0a15ebe452050b3dc41c12e3cbf9650971adfc8284b8f2f581425c7b5a40a12e36ed90e1921bd6c870890e7b61e80486ddb2d40243aef86a0121bd6ca50090efae0280486ddf2cc02437af9460121dd7c230090fcb55180486fcf22c02439ed8720121b76cb10090df364c804877d30040243aef9858121d764c2c090f3b61d604865fb21c324373f9055121f96902a890f3b58172487d5f2ca1243fa79150921bd7c828490fab5814248775a85c02436ed9688121d77c344090deb65220486fcb2310243beb8088121f74b044090f5be5f82543cdb2dc12a167d96e0950abe4c2e4a875be0972542aff22b92a1d3f8750950f97c1284a874f50971543adb2e90aa1e6f9648550fb548242a87da64121542cff2c90aa1d6d7248550f96a1242a871fe1d60543cdf24b02a1e6c9258150f37c12c0a879b209605438fae2b02a1e6f2158150f3690ac0a85dea6220543af70f102a17799188150ebcb8c40a87da48620543af70e902a1f6b8248150bbdc8a40a875e5c520543ed242902a1d9f835c540adfc92e2a066fe097150337b04b8a81f8f83c8540f56b0642a076b65d21503d5f2c90a81f8f8348540f56b0242a05afe592150375f0490a81bad8248540ed6b9242a074fe5d50503e5f24a8281f2c9254140e9eb92a0a074f5c550503e5e42a8281f2d2154140edcb8c40a07ea48620503f370690281db97148140fd490a40a07bae45608833db2ec0841b792061610ddc903090865f6157284337b08b9421b798254210ebcb92a1084ef64b84442d7b2dc2221baf94e0910d9eaa704886ebe138244367aa8c12213ee9820910dd7c21048866fe1172443a7aa8b92219ef825c910bd64c284884ef26142442d7f2ca1221baf8250910dd6c12848877965d21443dcf2c90a21fa79448510fd3c2242887f8e4121443fc12090a21bb78448510f9aaa242887795c921443f4a8490a21aef8258110f7290ac0887cee11504436f704a8221f6b8254110dbcc12a0887da20950443af2e4a8221f394254110fb890aa0886dbe0950443eca42a8221e796054110dd7c1280887e948540443e72a0a02217ea9888110ef4b9440887f8486204437770890221f395448110fd4a1240887f84852044327ae5c02a9aaf86e054295ec870ca17aa5812050a97f2ca12e372f9055321c76c3f0c90dcbe41544865d930b02438ef865c921e96aa2e490d79e4572486d5f2ca1243aaf8650921b1fcb284a845f26171542e7329102a1d697288150c9eb930aa066be0971502e732b102819ad845c620d75cc2c11073a5c5608836d730a8441d6b9754220db4c0aa11075a5c550883b52e2a04419e59760420ce6c1ae2106796057108275930a1221f255448510d9dc22a0886dae0950443e5284a8221f612154110 else 0x62dbc5608a251312236c43187b50e0e19642cc850f090a0fa4194827b03be04c404a7ff8feddfb4bf1b7d76f991f0fbdd17af4f4d5e73bc9978a8f03dde9bb85766eebc9d56ba567410e70dcc8394271fae275c2338016f54dd71b82b6ae6caed825addb5766a50d3b1a5834746870d0159e4b37b6648cb7d951b2796456c8058de31656252c3b584fb063603cbf417bcaf3d5e02bb15744ae325bc8b6596ad2d1559a0b251627ac015778ae015a6aaff553ea96950aa9d9533aa56148528c55112a11140427cc4f209d51387a6dc4d52996d30fa5da4b1894f926f249948a8903d1e0a36146268b15140223b43fe86e90bf213941e8830503e20373ff67e90fa69f083d2c7944f019d9a3a9873f8e539c2c37bc6e64da59b06358269f0d1719e033006510c7f989f30c66078be8178b2e7a5b98b50965c2c2e576cacb155a2a2a5340a45943427cc4ea89b2932925a44a3492411f12334457889110cb213041287f98fae1e9c3c487620e761c6237d46d38d591a0432f46408c4e18242f345c40b4c15ea2ac05358a14138c25bc49988ee112e219041887e30f4e1dac39786fc0d921a5832d06390bfa174c2c705490a1a13202460459084c0fcc1d7036906480bc415f0282049e084c0e70192029a046807380b4010201380007efe5180487fef22c0243fbd9048540fdfca704887efe1382443dff2cc1221fbf9460910fdfc2304887fbe0982443fef22c1221eff8258110f7ec12c0887dfe0950443efb04a8221fbf8250110fdec1280887fde4520443e7f22902a9f3d9148154fd7c8a40a17eb6452050bbdb0f40243ded8760121f77cb30090febe5180487fcf22c0243eed80581219fecc50090e7f61e80486f7b2940243ded72a0121bfac8d0090e7f61d80486f7f28c0243ded7260121fd6a130090dfde4580486fdb3110243ded8788121ebe9070ea87db64121543cff22b02a1e7d2158150fbdc8a40a87de64520543f5f2090a81fad9048540edecba42a07e7e0d21502f7f2090a81f3f9254140f9e90aa0a07eee4520503f7322902817bd92e1110ddfca704887ebe5382443f5f09c1221bbf84e0910f9eaa704886bfe598244377f28c12216ff9660910ddfc2304887cf551824437df04c12217ee9820910fd7c21048876fe1172443bdf04b92217bc9850910fd7c1284887eb60942443fc93090a21fe79048510efacba42887ede1121443fcf0490a21fe58248510f77c92c0887bb249604435ff04b0221eef8258110f76412c08873f5c960443def22b0221ef52158110fbdc12a0887de609504436ff04a8221f6f8254110dbec12a0887db20950443afae4a8221f752154110ddfc1280887ebe094044377b04a0221fac8250110edeb9280887ed48540443fd30510221fb99448110fddc2240887fce4520442fef2290221fe52148110fb) else (if j<3 then 0x89c3e170122487624476260713c02eb1787c2a367cd2d4478f80e1b14a51f218f80a170f88528f8e1e0871387c06394a22450aa4c563f0f81111e23c762e0386638f8e1ee270f80c72944470f31cd3c3e2700a51120a4c662f0387c2a3c4482e9488e1d6370389c2e1c44ae351f87c4e10786e051d8cc5e1f0a3e38748f89e017789c26370e3e531985c4e0444cc309782c5e070f85111d8e0ce070f83868571080670f818684f13843d168fc0e1e1b828a461147a2d1387c0c37091889258e0ce0f0387c4890ec762f0387c186448763f0f8186e2708223e1823c0e2708a633070dc3e071384911f0d47e07138691198386e1f0385c4488f1dc351f87c0e2244704f0f81c4e17070c384e2186e1f0b81c4a3a44945d168fc0e1f0b0c91230d45a3f0f8091188fc0a2f0f0dc1e10f86e270f81c2088c0a00f1381c308e1b8420270c11e071097c2a38f41c370f81c4e144470ea2f0d41e270387c288930762633801d62f0f83c22719c0e2707841d193e1d48f138029183b0660d1f87c0e2709224a3389c0e08a450970789c0e1f09221d2117068ed1f81c2e1f11224c760dc0e270e8e911d898c23c33801d62f0f83c2283bc4e070f8491182d43e0f030dc2e24448e087687c2e071051112183c708f0f81c4890ec7e070f83c4890c118631f87c0e270624422d12c7e070f83c48910118604389c1e070d8f122618c563f0387c1890e1163f1381c3890c0ce071382291783c3e071225111b8212e1f038829888ec3e0b4f8011e24487e1e1b85c4e044460f0758e86e171381c3889211a071f87c40fa487e0f1381c308f083a38762586e07058b0ce1f089097043bc0e270b871121170c44d1f81c3e270b0c4d1f87c0e20470c311f87c0e204785861e1811437003bc4e1f0b824b158fc3e04445e27038411100a9f05f1823c4e070b0e471b8011e204f84361b0bc0a392f8431270d87e1f1380370382c5e10745c3f1381c3288bc4e0707841d168a8be070785861b81451487c30ef0383c2128d8ce270050205ea28be27030dc21f059208f0097c4a38fc7c670f81c1110d82c912781c4e1d1c7c943380c5e0f0c66244b87c0888b44a2f0f849f1789c0e1844a42d128a89e023387c21c2c4be371381c2e08f4b863198bc0e0f087e0f0389c3290bc162c3386521419c1e07138652198bc18670ca42b1589c0e1f0a22331383c062f0f85111e8d454670f83c21a89c1a2f0387c2488fc3e270384111453c4e070d222a2781c4e1c485e071383c3890bc4e1f0023121618110970f81c4e08a48a91b51469fd53c7a7294d8699752f2a57f4a3292cd226a3d546de8bdd13fa2194342845d0469fdf3e627a9cf179d8139ca71b4de89b2334ea671cc9e98c530765e7cb8a96672bde554ca5b9451278e4c6494791e122ae42a47e28f051d1a377c6aa8ccb181 else (if j<4 then 0x386e071384538891c1c37018bc229c447a1f0789c029c444c387783c0e244450304619c3e071382c78910118631f87c0e27062447058fc0e1f1225111d8fc1e1f038912888e9d45b1f83c0e270e25112421c163f0f81c4894448e0b1781c363c4a223f0781c4888a45a04470dc3e27098f1f218fc3e270b8186888e9d45d018f11c370b89c38f941e0871387c2e031f0d11258bc3e07098f86888e86a04453bc4e170d8f1f270dc10ef0389c3e1444829b038811e151f861fc3125360f0f81c408f0a8f8624230ce1a1b81c4e17068e4a1b83c3e07128fc2889086e0f03881de170e2247068fc3e071022921c22c0e270f8547c307c8a3b1b87c4e044466371381c21044466371097c0e144466371387c0e14446e1f0382cc918b86c2f038453288c4bc361781c3a3f08a2432d864be061b0b47e1144923e1b0bc0e1f08a23b3389c0e0f083a37038851148912e06198bc3e0f0a9847138051140912e0f1381c20ed307c3c770dc02671385c32493c4e070f841d288d4c61f1381c1140d878ee1b81c3e1710a2470cbe51e071050361e3b86e270f80511e98860ef0389c3e170488941f818662f0f83c2a613c4e012f841d288c48e270f841d288c51e1f1381c1140c1da1f1381c1140c0c44a22864be27038228244a1da650f81c1628a086602f0dc4e061f85c1230dc0e270f0e51193a87c371387c0288e1d4630f8025e08a070ef1381c22888061007789c0e1f08a2392e0f1de270f81c228901d8371381c2099447e270f81c2288746c2f138051140b12e0f13818645f0a98441f0b1dc370b81c4e19309257043bc0e270b86511d0bc4e070f841d288f850ef138051140d82e070624c5138c99c170781c48909c70c12f05c0e0f128f122319c3c17038292328f82e05178292138d8ce1e0b83c0491947a3f0125c388a68661f1125c08889c663f038745892446c660b81c1628a46c660a25c0e2704ba3f0f81c4488a454670389c1148b8cc170383c425d1e24460a19c062f045231748fc4e070e24911d8b43e0d4f809288a688c150f25c0867078853202210c112e1992e070788c7298e27c170781c4490e1108707890c4914c762d0f8353e0445463d0f0411e0f03889229914b63d0cba28e043383c449144bc170781c4e1a4842451d8b0ce024b83c34d100ca3f0781c3e22487a3b1619c0e1f05463b1587c0e244452351e19c0e0f0d8a921f05c0e0f1124271a1947e0f0387c4490f478670387c162a4870670389c1148a8044f0e8d45e12787e160780c7e1e7cc63d1a8bc363f093e327d1746a2b1f87c0e124490f2028d47e1f0b888948121ee1713814629a4470ed1d8981c4f00bb4662f0f859f331381e0713859f2e8f47402268dc4e1f093c40799747619768dc2e0710d0912f03c0a312f89c2a3e7c82ea288f46e1713869f20ba8b23d1b else 0x2512928e1f88c18e8e282887789c1148c9f29d1d8780a3711225d24a78c20d1f0c294f18c1a3e1858e90e8f86e08b1de1d1d829114a747a1b063a91191943e08770c28768fc3e0a445e26198fc1888ac721f053b111789c3c37058f11198fc34ef06222c7f894088b1f0c34458ec3a02763e370f8486e0c445a3f0f89c06344462ed1f86c6e0712223c1f87c0e27098d111c27810ef018dc4e1f0a224e1d89410e8a780c5a88a090ed3053c0e0b14503d3187c4e070450361d83868ef0385c4e194494353381c40ef0b87c123821de0710a2281b0e28c370789c0288a4851c4f0fc2e0317834c14938760c770dc02671093292426c4a15043bc062d44524f0d0dc1e0710a2291e9829e0317822819831dc3f038851948e1d43d3051c062f0452407583c3e2700a2281c93c3145310dc0e27045248a383c4e01445235044a1d14f018b5114118263f0787c0a2c4922470789c0488a454970287c429c444c39758bc129f0125c4888a09a3c3381c3e0f1124394c230ca3f0387c4e0a48923b14bbc4e0244d23d1cba1da370b89c0e1a44934994ba63a3f0f039fc4b17806832bb454051913c2e270e8e9e288b802ef113e691a22c762d0b0052e247cce4c458b8063f123e691e8fc0e270f851f630e53a3a27801de27098dc38f9541e270f8011e16198e414d8386e1f0389c2a3a44960d1f0dc3e07138491228ec1c370f81c2e2244829b070dc3e07138547489386e27038747488d8c8eb0f0dc0e2708a7c1263b47c330787c0e1711224b0f184be071383c2a3e18910474a747c370f81c2e2244ac347787c4e051d2238770dc0e270f85c11c938ce1f0389c2e0e18829c418386e1f0389c2a3a44a29b070dc3e05168fc2489247c67028bc1e1f0b0c412a8386e1f0389c208d1c9a091f0dc3e07138511230d410ef1381c3e144486287783c0e2244523b14501de0f0388911490230e8a719c062f0450414e0cc18ef0389c3e151d22524623c0e241b87c20ef049e0f0389c20ef0d223f068786e07138453889010e092f89c0e131f0d11278386e07138453888f4363f0781c4e161a2240438)))
def g255H9 (j : Nat) : Nat := (if j<1 then 0x2c03f000160c4c95a86b00000000000714d0000453dc3b28840000804bc3a592571880003867000082140000000500e0000000000050cce14cc64e012e5224072e4f00003173530b41ec45c84ff2112608a42028f97149232a433b9780001035c88d8000c1640517c2c000040c1818e8b83124000063df802f52e42d260ac000506971b4461c00000000001e48bc7a80000000000012a881a623a0000000000041a0a10400050c5622e61584a8716e003fe642801800090e0d1ec07b495800012483a30000000000001ec62c7911a3446b83a88ab61234587402000030fd020ec0b80006022000106020ef11fe460000000000001844645700000001c4f8cae40fe70b800000000000026742fb4cd00000001c5f8000383090c440ccc033057000181758a9800052b40000000596b8167a17800000000000000386f284800000000000594b3a3e000306eb86191c60000c75d07c0001810c00030ad614fa5008390000e010211800028bc8319844c0000000e22ce1b2caee14ca23fe5e647e9992000183cc000000038c2000248400007111a249c24d0a000018036c6170e111d2000102608e7f312a26f45409040305a3b8a8f4d8b018c000281bc8b45153c666438a9370000000000039340001e01c000502062cea134000608a0000000000059570000417c40f00000000623b40c001c4a41858981ec96c00000000ccaf13f0000000000058ba000180240c4000000000000000386dd1f6c44800000000000a128c215163301e000000048c3f28de5f50178000e12a000144d000000000000000098100006478cc3389f927385380aa0000a3160001046383a12ac00038730000000000024bb50bf128980fa429a9710001221c05b8000e176665c00010540001a57987461070001251d46df12db0b780318508000a2bf414444c00000000733cc6788b6e204000389480000001e093828701b505a65240b2412600000000000182c0001a650abd0000405c00000763941b2b200014808882309620a0000513a12cd6583033508b314780a4c57d8b1d0556051022f801021a000000000009218000301c192e027722940700000d033e37e8ba9130611b85fc000000000000001c6c8000000000014c7800071260000000214a00000000000405220f000030c748ea1ac8438888c589c00000000000204f00016418c05d079a13d00f000001036271220000008e561aa2546a9e800032f4000000000000000000144a688f0001c08488298f40000000000000001161a48c02240d2723200010350000418e000184308d422de04f44050000a0e6033482421c02011d20415022090011530da0020002401430830410011811000450c20012050c22090430800064812819830001010010c20c204039534010714c4860403c001710108918018b0000121ca1c0 else 0x83c1432913130f58042037d142616ae0d2cba0000000000540007948000065a20658000000104c9c64e027e26c6074000398d721dc3c40000000121200010add09600c8a0c800011140000000000070850001e28aca1e983a1a7c0d8000490b3182247000000000001c43f83fd9000046816400020bd0000000246c000040dca2678978000000481a2c4bd12800aa00030a90000b2ee0003496697c0000a1680006881d2abc613c880000e242000204ed1725027e00383b8000f1540003c72000042f7c3ca6994996426aa49f47d28ac000163f00006016d17143e103ef8ed408f82400130000000060ee8b5019872db64a94c8f915406ae13a86e38d6a191862acb)
def g255D10 (j : Nat) : Nat := (if j<1 then 0x386c0c4c287111e1d470310a4507448c1d45c0c1c386c2281c75054713030e1b089c745828cc3c012c11a249c451e0b0f031304489118210c4c0c3c1471226320a49151f030f04882c092c4c347111f1d160a330f03048c88211c4c0c3c14712211e08a4463303130f0448a43c1825392c0c411220a48311f030f071080c8292c0c347c1c4231c00271b0f0b107880ac6c3c4c2471f1c7c2c1b0d1f0b0310449c78189c04645c3c29f244a247e0701191f0f130a7cb1f12471d8189c046c4c3c29f3046010b1d4b0f107c8c6c3c0c4c247111e271b011f0f13087c846c1c3c0c4c2111f0119170f070a30746c1c3c0c2c4111f0119170f070a307c4c086c213111b070f02182b104470009c386c2c41f1f070f0310484460bc3c0c286c4111f1e1b0f03104460947c3c0c4c286c1221b130f030844647078c0611c0c4c3c2c128331f0f03130448786c1c3c0c4c2111c6b00470d144861592474591c3c01f1f1b0f03104464b43c6c4c0c2111d2d0f1b130308447c611c0c40b87c21f0f021b0b10446c4c3c0871217021b1308445298751c4c0c3121e0b124b030c446c3c4c01211170f13087c4c3c009c40cc2192f1833130307087c0520cc4c1c31b0f031308445c608c3c40cc1c21f070f031308446dcd6d335fdaa8d31687338d970c9163330ed828be55df2e4d6b8b395892bbd598aa553b292d450a094ef26dd32896d4a1247d2008e546522bd11887142920dd0287f13e51eccf307653a31c9ce206e535f1a5cce0649313181cbc85c12cb15ccaa052d28513ac98849d23710ec8303f91eb0edc7303791ad0cfc6403011730b1c558289137090c4482050f5072c3601910b9054c27012108503ac1a00b9053022c0d805101d006c000ffe80487ff60121fff82443ff60910ffd20443efe0542fef80487fba0121fed80487fb20121dfd87486ffe0121fee20487dfe0950f7d21543ef48540bfd828437f5ca10fbf84442ffe0910fef82442ff60910fec824437f5c910fbd42443fd48510efd60443df54110fbd40443fe88110ff920443cfe0954f3d20553ebe0542ebf8650aefe0142ebd6050beb481429ff825c76f50971eed60c877b61d21eef86487ebe1121eed60486bfe1921bbf84487cf55121ded72487eb50921d7f87543dbe0950f6c825435f5c950f3d425435f5c550f6f21543db48550e7d60543de88150f7920543e7e0d40bbf82502ef60940dbd71503ebc8540fad21503cf54140fba20503ee48140bed818837b5c620bed810837b5c420afd86842df61610bbd84843de54210bbf84443cf55110bef82443eb50910fe521443de54110fea204434fe1d54d3d72552cfe0154eaf8650bab58142abf8650aeb61321f2d54c86ebe1121f2d54487cb50950b3d85502ebe0940bad84883ba58220f6950883ea50220bcd83082f960420 else 0x1387421d86c1c0c451292a18761ca133031304a49118cc0c4c3c2c186472444763313030d1f0a1b04ac147c3c0c4c2861122070f0313091844808070645281d4cc0c4c129284a1c77061b03130b0d44a87864c1dc0c4c2c3c1241d15044b03130f094474a29251d2387c3c045c128281814a07533031304a491207851dc186c0c4c2c3512d1d150e0b030710489c98c4543820c47c0c4c12928491576047627011b130b0d1e7cd47c1c386c0c2c411204e05151f030e1b0a44941c786c3c0c2c41120261b030f130b051c8118c47c3c0c4c2c18626302c24751e1b030f130b04b118c1047c3c0c4c2c1862a3117030d1e1b0b04886c3c0c4c247111c1846307703130f0b051ca8743c153c0c286c411261f071f0f031048448874011c786c3c2c41f24744b061b0f0313091c44a0cc3c0c447c2c186204b130f011c44547c647c3c0c411191b130f0308446c6c0c4c21120182c1b0f03130a1c448c6c0c4c21113181f1b0f031308447c2c0c347c1231905451f021a170f0884311c4c1c086c213221d10761917030f07089c0c4c1c21d147444a71300a06114b871d4c4386c2c0c4c12832182f0313061f087c)
def g255H10 (j : Nat) : Nat := (if j<1 then 0x600000000000000059fe00000000000000000032678000000163980000000000000000001059000061f40000000b00ac34000000000000000000020040000000000040a400000000000000000000000000000000000003c5f810d000000000000000000021cfc648000017c00000006832e000000283900b00000000000000000001c34c000000082500002074985f0000000000000000000000000024dd00000001c0080000000000000000000000c17800000000000000106400000000000000000000001229400000000000000244d80000000000003d181c00000001c3808ad716c00000000000511800000000000000140d800000000000000001480000000000000051200001839308a34cac1bc000000040530000e49400000000000000000000000000000000000000000a3a80000000420c00030090000000081c40000000000000000001039604a0000000000000000000000000000000000000000020c80000000000039ae0003096800000000000000000001ce0000000000049cf644c00000000000000000000000000000000000000000000385780003096000000000000001a3ec00000000000000000000000000000000000000000000000000000000a454000000000000000000000000018470000000000000001c40eaae0000000146c00000001e0540002856000000010653124d1820000000000000000002c220000890a000000060b100000000000000000000000000201a00000001c2e0000000000000000000f12a00000000000000020f000000005134a30b418000070c4013ec5d80000001a23c00000000000000000000000000000000000000001035000000006126000326e00008196000000000000000000000050cf0000000007be082607a0000000000040fe000349900000000000247a8000000000000000000000000000000000000000000000000a1b600024530000d016c22908500000000000000000000000000000029308142000000008d10001649c0000000000000000000000000171e00000000000000000000000000000000000000000000000000000000000000000000409a0000000000092360000000292f00000000000000060de00000000000000000000000000c0864130000410c000000000000000e06a00000000000e05600000000000000000000000000000164580000000d1f80000000585100000001c66482160ce62140000000000000008908000f0d8000147a000000000000000000000000000000000000000000000283700014107083e86df05f2380000582d7046000064a8000000103bc00000000000000000000000000000000000000000000000000000000000000000007900002100011010001012001102010100001007100002030000103300021000001063140000011001 else (if j<2 then 0x60da0000000000030d2c19a00000000000e0ee000045400000000000045a800000000000000000031c5a42c000000000000000000000000012040000000000000000000000000000000000000000000002822800000000000000000021560000000000000000000000490000000002018e820725d044000000000000000000000000001c16c00048ce000000000000000d99de04f0068000f00c0000000680740140000084d05ad234000000000000000a18c00000000000000100180000000000000000a300000003861d038b20264208628000000044c400054dee9e2000000000005208000000000000000000000000001144a38c00020d6b1dc000000040bd000181ec000504a00000000000000000000000291183f000000000007888603ee29c000000000000003c4228fa0000000000000000001645c00000000001024400000000000000341568330001836648190f310f3015c00078980000000308f412af23a00000000000000162ea82444c7f1640000000000060680000000000000000000000000000000000000000000000001233800000000000000789c000000000000000911c00000000000000000000000000801e000188100000000000000000000000000000000000000000347f00000000000000000000000000000000000000000000000000000000343a88890001e2500000000c023c48b6870000000180b24280000212000000000000000161d80001074000000030438052f0dc000000000000000000000b603a0000000000028b8000180ec000000011fe00034248000000000000005a0762520000000000000000003c62308600000000000400e00000001218000000000001c2c00000000000000010ec000000000000000000062b800000000000408a82a80000000000000000000001a19704ca0083080000284f000000000000000609281bf2395c890000812ec2d00000000000084980000000a256000000000000000000000000000000000000000000000000186310eb00000000000590e000000000000000000000000000000c08400000000000000182a80000000c178a1f8000689601c20000000000000000000012000000000000000000000000000000000000000000000101e0001a0fa40b80000000000206a8000000042cc00000000000000000038610000000000000000000000002e8000000000000000000000000000000028000000004780000000000000000000000000000005069000000000000000000103e704000000000000000000000001e35c000502e000000000000000000000000000000000000000000000121e000000068470000000103400000000000180480000000847c0000000714000000000000000000038562083a032041400000003232000000020f else 0x1720000000000000000000000000000000000000000000000003446800081ba0000096689f10c174258740000f1f00000000481d00000002c6e0000b0300000000306b00000000000000030d40000000000000000000a898000d1160001c60481400000002091800000000000000000000000000000000050f00000000000000000000000100251fa000000000000000000000000000000000000000000000e4600000000000000000000000000121f0000184e008c000000000000001627400048ed0000a4462648000904c000000000000036000000020c70000000000000000000000342a00000000000000000000000000087900000000409c0330000516e00000000000000000000000000000003c40000000701894c40000000715200))
def g255D11 (j : Nat) : Nat := 0x28c3a1a044870a087283c18700344844480e323c38112106824818c46240861e1111e0060b0e0c21c6060f0e042890480e30340890e14122382184a1c0890488e044c6810e2423e4c68702242823078d0e044830860f1c911870220d188c4810e10d62d0f21408e6b1ea8a266712e30060007fd21ffc21ff443dea15fd71fde43fb487bea87bd40fdc41fb0839eaa7ad42
def g255H11 (j : Nat) : Nat := 0x1217e3120c400040100000030760009a500000000000007114021c2c4a7000003d251d10000000000012f0000000000000000045e23c000000000000099900000000004118000000000000082c6a1c1d72e00034660000000000000000713113e8aa46000039740000000003031065c24b0db16800184a000090c4b200000000010220000000001852000000295c4700000000002a4e00011080000010659050001cb1a1981d0001898000e1fc00000000060c785400000000050a8000a2d0000000000450000612c0000000006d348b6000000000000000000000038c3654233691d0917243090003ab200000000000000000001d2c000000d23000000000030400000000000007d59cc8000f02800341f80da141937406000a0a00034ac0000000000001663000000000000000060dbc7a000000000000000000018080000001158000000000000219c000000a29000000000000000000002160000000000000000490187ce220000001434a34000584c05c00e0000000000000203800140d235004c10ac7200000050100000000000000001837729b09449de49000000346000000000000012810000000000000000000000000000000000000000000000000000000000000062770f80000000008220000000841c0e00004be0000180989e18112c108a191
def g255D12 (j : Nat) : Nat := 0x1c60c0102047ff
def g255H12 (j : Nat) : Nat := 0x325128499a24c30c0000088c0a40e178411b2a21c8bc04000032b00000328
def g255L : Nat → Packing
  | 4 => (1,8,6,0,0,0,0,g255D4)
  | 5 => (7,7,6,0,0,7,0,g255D5)
  | 6 => (48,6,6,0,0,11,0,g255D6)
  | 7 => (234,5,6,0,0,14,0,g255D7)
  | 8 => (411,4,6,0,0,15,0,g255D8)
  | 9 => (307,3,6,0,0,15,0,g255D9)
  | 10 => (104,2,6,0,0,13,0,g255D10)
  | 11 => (13,1,6,0,0,10,0,g255D11)
  | 12 => (1,0,6,0,0,0,0,g255D12)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g255H5
  | 6 => lookupWord 2 41 0 8 3 1 g255H6
  | 7 => lookupWord 12 71 5 11 6 1 g255H7
  | 8 => lookupWord 59 1223 3 14 8 2 g255H8
  | 9 => lookupWord 107 641 6 15 9 2 g255H9
  | 10 => lookupWord 82 1229 4 15 9 2 g255H10
  | 11 => lookupWord 28 293 3 13 7 2 g255H11
  | 12 => lookupWord 4 23 3 10 4 2 g255H12
  | _ => fun _ => none
def g255 : Forest := ⟨255,12,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P4_0 : block g255 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B4 : block g255 4 0 1=true := g255P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P5_0 : block g255 5 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P5_2 : block g255 5 2 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B5 : block g255 5 0 7=true := (@block_merge g255 5 0 2 5 g255P5_0 g255P5_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P6_0 : block g255 6 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P6_11 : block g255 6 11 37=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B6 : block g255 6 0 48=true := (@block_merge g255 6 0 11 37 g255P6_0 g255P6_11)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_9 : block g255 7 9 81=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_90 : block g255 7 90 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_186 : block g255 7 186 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 234=true := (@block_merge g255 7 0 90 144 (@block_merge g255 7 0 9 81 g255P7_0 g255P7_9) (@block_merge g255 7 90 96 48 g255P7_90 g255P7_186))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_1 : block g255 8 1 93=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_94 : block g255 8 94 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_190 : block g255 8 190 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_286 : block g255 8 286 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_382 : block g255 8 382 29=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 411=true := (@block_merge g255 8 0 190 221 (@block_merge g255 8 0 1 189 g255P8_0 (@block_merge g255 8 1 93 96 g255P8_1 g255P8_94)) (@block_merge g255 8 190 96 125 g255P8_190 (@block_merge g255 8 286 96 29 g255P8_286 g255P8_382)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 38=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_38 : block g255 9 38 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_134 : block g255 9 134 64=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_198 : block g255 9 198 92=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_290 : block g255 9 290 17=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 307=true := (@block_merge g255 9 0 134 173 (@block_merge g255 9 0 38 96 g255P9_0 g255P9_38) (@block_merge g255 9 134 64 109 g255P9_134 (@block_merge g255 9 198 92 17 g255P9_198 g255P9_290)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 19=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_19 : block g255 10 19 54=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_73 : block g255 10 73 26=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_99 : block g255 10 99 5=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 104=true := (@block_merge g255 10 0 73 31 (@block_merge g255 10 0 19 54 g255P10_0 g255P10_19) (@block_merge g255 10 73 26 5 g255P10_73 g255P10_99))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_2 : block g255 11 2 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_10 : block g255 11 10 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 13=true := (@block_merge g255 11 0 2 11 g255P11_0 (@block_merge g255 11 2 8 3 g255P11_2 g255P11_10))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 1=true := g255P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact g255B4
  · exact g255B5
  · exact g255B6
  · exact g255B7
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 12 eightInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=12) (i:=0) (before_sound K254 V254) g255G g255T (by decide) (by decide +kernel)
def mo255Y : Array (Bits × Bits) := #[(0x91a30437000000000000000000ffffffffffff,0x80a00003090090090090090090090090090090),(0xcb0d1e60000000000000ffffff000000000fff,0x30d1c6050c50c50c50c50c50c50c50c50c50c),(0x1840c28b000000000fff000fff000000fff000,0x1840c288a03a03a03a03a03a03a03a03a03a03),(0x2fc4d91c000000fff000000000000fff000000,0xb04891c325325325325325325325325325325),(0x664b7820000000fff000000000fff000000000,0x644b7020c4ac4ac4ac4ac4ac4ac4ac4ac4ac4a),(0x44342349000fff000000fff000000000000000,0x44202301073073073073073073073073073073),(0xc50aa4c6fff000000fff000000000000000000,0xc502244607c07c07c07c07c07c07c07c07c07c),(0x879a998ffffff000000000000000000000000,0x8598898f80f80f80f80f80f80f80f80f80f80),(0x0,0x0)]
def mo255C : List ColumnInfo := [(8,0,247,0,11),(16,0,239,0,11),(32,0,223,0,11),(64,0,191,0,11),(128,0,127,0,11),(0,128,31,96,10),(2,0,253,0,10),(4,0,251,0,10),(0,8,230,17,9),(0,16,230,9,9),(0,32,93,130,9),(0,64,59,132,9),(1,0,254,0,9),(24,0,231,0,9),(32,128,31,64,9),(64,128,31,32,9),(160,0,95,0,9),(192,0,63,0,9),(1,8,230,16,8),(1,16,230,8,8),(2,32,93,128,8),(4,64,59,128,8),(8,16,230,1,8),(16,8,230,1,8),(34,0,221,0,8),(40,0,215,0,8),(48,0,207,0,8),(68,0,187,0,8),(72,0,183,0,8),(80,0,175,0,8),(96,0,31,0,8),(96,128,31,0,8),(128,32,93,2,8),(128,64,59,4,8),(136,0,119,0,8),(144,0,111,0,8),(9,16,230,0,7),(17,8,230,0,7),(25,0,230,0,7),(56,0,199,0,7),(130,32,93,0,7),(132,64,59,0,7)]
def mo255A : List (List Nat) := [[],[67],[33,101],[33,67,101]]
def mo255D5 (j : Nat) : Nat := 0xc0e1751d3321b02a55258521
def mo255D6 (j : Nat) : Nat := 0x183c5d3321b02a55258521
def mo255H6 (j : Nat) : Nat := 0xb
def mo255D7 (j : Nat) : Nat := 0x305705397c3cd82d549d2213c6cc150087e4c86c0a9549614870f9321b02a55258521a3e4c86c0a9549614863f8700ba549616012187e5c92e952584804871f12e9935496120121c799976d0a064d214c31e6655b428193485309f91c42c193585214c314f6ddb56a48408530d16db76d4a9609600420f9321b02a55258521
def mo255H7 (j : Nat) : Nat := 0xb02800
def mo255D8 (j : Nat) : Nat := (if j<1 then 0x71f6dd324b090098e3ecba6496120131e5db6cc92c240263cf96c592584804c61fe5d324b090098d3f5b16496120131e57b28b12c240263cbb64962584804c71dec3b484830690e3bd856909060d21a7f160cc30ea1a434fe2c198615434867dada140c1ac290cfe5b228153585219fe160d4286b0a439f96cca9549614873f2d8152a92c290e7e4b02a55258521cfc952c1aa4b0a439f92a543549614871dec33484826290e7b5a4584904c5219fc974a92c2c0243c5f2e197654804878be5432eca90090f27ca86599520121e4fb0ecb32a40243c3f65d96614804878ee5c32ec990090f35cb86559320121e6bb0ecab2640243c7765d8564c8048796ecb30ac990090f39d876519320121e73b0aca32640243c7d2e197644804879ba5c32ac890090f375876559120121e3eb2ec2b2240243cf561d93644804879eac2b26c890090f3e5876499120121eaeb2ecaac240243d7565d9358480487baacab26b090090f7959464d6120121ebcb2ec92c240243df164d92584804867f25d2a4b090090f7c5935496120121f73328c9a86c00430ff2e8984c9615431ee5432ec9a429863dca86559348530cfb32e5032690a619f6654a064d214c2dea5c326b0a42985fd0b064d61485309fc974a92c290a6196f6dda9210214c339edab52420429867b9b06a48408530fd32caa1ac2a0261be669943545404c3f8ca1aa4a8a80986f99a550d2150130ff2286b0a42a0261be669543085404c2d765930cb2b068863ec982898654d10c5f950cb2e6412218bf2a19654c82443576d3306412e48872ecb26989854910c5fb4cd1930a92214bf6d89860d52442f725930cb2a62886af587698824c510bdcb6c412e498a21abd6d8a85493144277adb150a92628863f4a865d9348510c7e950cb32690a218fd2a19564d214427f25d30ca9242885be4b864d5248510d5eb6c542a490a219f565da324121443772d32a448242886fc5a35489048510bfc164c3262a82217bc6d8824c550442f78db14090aa0885fd1b328121541109fe174caa62902217f82e89848520442ff05c34e90a40886fe0a869d2148110f7c130c3a42902217f82e5a548520442ff05c34a90a40887be1866152148110bfc170d1a4290221bf869da3485204437f0d2b4690a40887be18660d2148110bfc174b9a42902217f82e17348520442ff05d2a690a40885fe0b954d2148110bfc170a9a42902217f82e15248520442ff05c26490a40885be4b85492148110bbe36e50242902217dc6d4a048520442fe8d994090a40886fe0ba4857048110dfc17490aa0902213fc2e921541204438f6db952c12c008736db52a582580108fcb6054aa4b0a43ce66519350d800867ccda140c9a42986d99a750c2150130de334aa1842a02617786dca048520442fb0da94090a40885fc1b32812148110 else 0x367743d850504e0fc1960cc013e27c3f84e0464c881963ac6a83600458eb1aa0d80100981239e7384c2a04c0914a130ae14026320492923a444828f91da3846a8c917a2c45289911a2043a8690ba1442283905a0840a808ff9fc3f27d8f99f03da7a8f39e43c2778ed9d83aa748e79cc392718e19c037a6e8db9b43626b8d59a834a688cf99c332658c999031a628c39843025f8bd9782ea5c8b796c2d2598b19602ba568ab9542a2538a594828a5089f93c2724d89993025a4a8939242424788d91822a4488790c212418819001fa3e87b8f41e23b8758e81ca3886f8dc1b2358698ba1421f43204b06406400297edb144c8900b9d2fdb6289912015387f970d1120a9ac37d96c8a16548058)
def mo255H8 (j : Nat) : Nat := 0xe200000113e3617e431800422010030700000029030000000000e08000014b20000b58499610
def mo255D9 (j : Nat) : Nat := (if j<3 then (if j<1 then 0x9420131cef5959420131cfb69d9220131cfb6999220131cfb5d99220131cfb6959220131cfb5d59220131cfb5959220131cfb68592201318ff6859220131cef6517220131cfb6497220131cdf6556220131cef6516220131cfb6496220131cef6515220131cfb6495220131cef6517120131cfb6497120131cef6516120131cfb6496120131cbf6595120131cef6515120131cfb64951201319ef6909060d218ff6a0905cd219fd684905cd218ff6a09054d219fb6889054d219fd6849054d219fe2819850d219ef690904c521cf75d59320121cf75959320121cf764d7120121cf764d6120121cbf6595120121cf764d5120121d5f65d9520121d9f6599520121cbf6598520121cf761d9320121cf76159320121d7765d9320121dd76559320121de76519320121d7d65d9120121ddd6559120121df564d9120121df96499120121ddd6556120121df564d6120121c7f65d8020121cdf6558020121cf764d80201218ff6a0905cc21cdf614905cc21eee2919360021cfe6519360021afe2a57360021afe6a54360021ef664d4360021afe28173600218ff688984c5708ff684984c9508ff68898585508ff688984c5508ff2a19648550cfd2616148550af72a19348530bf62819348530c7f65d8408530cdf65584085309ef6a48408530d6f65c8408530dcf6548408530d7765d4308530dd76554308530cfe6119008530dee2119008530df650d9008530fe65d54350130fe65954350130fe650d7150130fe650d6150130fe650d5150130fe650d2150130b7e69c2150130bde6942150130fe650c2150130afb2898661510bbb2898659510afb2898660d10cbf61d9620910cbf6598520910cf761d9320910cf76159320910c7f65d8320910cbf6598320910cdf6558320910bbb698825c910cbf69898549109bf69898549108ff2a583549108ff2a5854c910bf9289864c510b7d69c824c510bbd698824c510bdd694824c510afd2a1524c510cfd2618748510afd2a19548510afd2a19348510afd2a15248510b7d69c9048510bbd6989048510bdd6949048510bf568c9048510bfa2898654110bbe6988254110bf668c82541109fd2a52154110ff82a12148110ff82612148110ff869d2148110ff861d2148110ff86952148110ff86552148110ff86152148110ff85d52148110ff85952148110ff868d2148110ff860d2148110ff85cd2148110ff854d2148110ff850d2148110ff85c92148110ff85892148110ff85492148110ff84c92148110ff86812148110ff82812148110ff84857048110ff84855048110ff84853048110cfb2a5825c010cfb2a58258010ebb6998258010e9f6156258010eb760d6258010ebb6096258010cdf6598548010cf76598348010cfb6598248010ede6156048010ef660d6048010efa60960480109f92a55258521 else (if j<2 then 0xbfd2a15248510ff95895248510bfd2a13248510ff95493248510ff95499048510dfd65c9048510ff95489048510cff6619748510cff2618748510aff2a19348510cff6598348510aff2a13248510efd60d6148510dfd6593148510b7f69c9048510bbf6989048510bf768c9048510bbf698825c110dfd2a5215c1109ff2a5215c110ebf61562581109ff2a55258110aff2a15258110dfd2a52158110ff954921581109ff2a52158110ffa2898654110bfe2a16354110efe6198254110bfe6988254110bfe6a16254110bfe2a16254110fbe6196254110bfe2a13254110ffc6193154110ffc6093154110ffc2093154110ffc5893154110ffc2a12154110ffc6992154110ffc6192154110ffc68d2154110ffc60d2154110ffc58d2154110ffc50d2154110ffc5892154110ffc4c92154110bfb2898654110bbf6988254110dfd2a52154110ffc6812154110ffc2812154110efe6096054110fbe5896054110ffc4856054110bfb289864c110b7f69c824c110bbf698824c110bdf694824c110aff2a1524c110ff9549214c110ffc485504c110efe2618748110efe6198548110efe2618348110efe6198348110bfe2a17348110bfe2a55348110bfe2a15348110bfe2a56148110ffc2613148110ffc65d3148110ffc61d3148110ffc6593148110ffc6193148110ffc5d93148110ffc6553148110ffc6153148110ffc5d53148110ffc5953148110ffc5c93148110ffc5893148110ffc5493148110bfe2a53148110ffc6453148110ffc5c53148110ffc5853148110ffc5453148110ffc2a52148110ffc69d2148110ffc65d2148110ffc61d2148110ffc6952148110ffc6552148110ffc6152148110ffc5d52148110ffc68d2148110ffc64d2148110ffc60d2148110ffc5cd2148110ffc54d2148110ffc50d2148110ffc5c52148110ffc5452148110ffc4c52148110cff69d9848110cff6618748110cff65985481109ff2a56148110ff92a12148110ff92612148110ff969d2148110ff961d2148110ff96952148110ff96552148110ff96152148110ff95d52148110ff95952148110ff96092148110ff95c92148110ff95892148110ff95492148110ffc2812148110ffc4857048110cff6617048110ff94857048110dfe6595048110ffc4855048110ff94855048110ffc4853048110cff6419760810efb2a58258010ebf6156258010edf65d8548010edf6598548010edf5d98548010cff6598548010ef765d8348010ef76598348010ef75d98348010efb69d8248010efb65d8248010efb6998248010efb6598248010efb5d98248010edf6157248010ef760d7248010efb6097248010edf6156248010ef760d6248010efb6096248010efe61560480108ff68098549618ff68098549318ff2a58454931afd2a15250531cef5d99420131cef5d5 else 0x19748530cff6619548530cff2619548530cff6558448530def6548448530df765d9348530df76559348530df76554348530efd6616148530efd2616148530efd6116148530fed2116148530ff564d6148530ff550d6148530ff95496148530df76593148530ff55853148530cff6558408530def6548408530df76554308530dfe69d90085309ff2a5215c130bdf694215c130bfe680215c1309ff2a561541309ff2a52154130fbe5956150130bfe6995150130fde5495150130bfe6952150130ffc5852150130bfe6942150130efb2898661510bfb2898661510efb2898660d10bfb2898660d10ebf6196560d109ff688985cd109ff6889858d10cff2618558d109ff6889854d10cff2618654d10bfb2898654d10bfb2898650d10cff6599560910cff65d9360910cff6559360910aff2a57360910aff2a55360910aff2a17360910aff2a16360910aff2a15360910dbf61d9620910cff6598520910dbf6598520910dbf6597520910df761d9320910df76159320910df75d59320910cff6598320910d7f65d8320910dbf6598320910ddf6558320910aff2a17320910dbf6597320910aff2a15320910dbf6595320910d7f65d4320910dbf6594320910ddf6554320910cff261835c910efb60c825c910cff6618558910cff2618558910ebf6198558910cff6618358910cff2618358910ebf6198358910cff6989854910cff68c9854910dbf69898549109ff2a58654910cff26186549109ff2a58354910cff2618354910cff2616354910cff2614354910cff2618254910cff2616254910cff69c984c910cff698984c910cff694984c9109ff2a5874c910cff261874c9109ff2a5864c910cff261864c910cff261764c9109ff2a5854c910cff261854c910cff261754c910cff261654c910cff261824c910cff261724c910cff261624c910aff2a1524c910cff261524c910bbf698825c510bf768c825c510aff2a1325c510ebf60d62585109ff2a53258510aff2a13258510bfb2898654510bbf6988254510bf768c8254510aff2a13254510ff9289864c510fbd619654c510efd619824c510efd61c824c510bfd698824c510bfd2a1724c510ff9209724c510bfd6a1624c510bfd2a1624c510fbd619624c510bfd2a1524c510bfb289864c510b7f69c824c510bbf698824c510efd609614c510fbd589614c510bfd2a19748510dfd2619748510efd2618748510bfd2a19648510bfd2a19548510dfd2619548510efd2618548510efd6198548510bfd2a19348510dfd65d9348510dfd6599348510dfd6559348510efd6198348510bfd2a57348510bfd2a17348510bfd2a56348510bfd2a16348510bfd2a55348510bfd2a15348510ff92615248510ff96595248510ff96195248510ff964d5248510ff960d5248510ff958d5248510ff950d524851)) else (if j<5 then (if j<4 then 0x31cff69c9850931cff6949850931cff2617550931cff2616550931aff2a1425c531ebf61162585319ff2a54258531aff2a14258531aff2a14254531fbd5896150531cff69d9220131cff6999220131cff5d99220131cff6959220131cff5d59220131cff5959220131cff6859220131cff6497220131cff6496220131cff6495220131cff6497120131cff6496120131ebf5896120131cff6495120131cff6189061521cff61c9060d21cff6149060d219ff680985cd21cff261845cd219ff6a0905cd219ff684905cd219ff6809854d21cff2618654d219ff6a09054d21cff6189054d219ff6889054d21cff6618750d21cff6618550d21bfd2818558521efd6118358521bfd2818358521bfd2a15358521bfd2815358521bfd6a14358521ff960d5258521ff950d5258521cff619944c5219ff2a5424c521dfd651614c521efd619414c521cff618904c521dfd584904c521aff2a17360121aff2a15360121efd60d6160121ff95496160121e7f2a19720121edf2a19520121ddf65d9520121edf61d9520121d7f65d9520121dbf6599520121e7f65d8520121ebf6598520121dbf6598520121df761d9320121df76159320121df75d59320121df75959320121cff61d9320121cff6159320121df765d9320121ef761d9320121df76559320121ef76159320121dfd65d9120121efd61d9120121dfd6559120121efd6159120121d7f65d9120121ddf6559120121df764d9120121df764d7120121f7d65d6120121fdd6556120121dfd64d6120121ff564d6120121ff96496120121ff95496120121df764d6120121dbf6595120121df764d5120121d7f65d8020121ddf6558020121df764d8020121efe65d9360021efe6519360021efe6517360021efe65d4360021cff65d9360021aff2a57360021cff688984c570cff288984c570cff68c9848570aff2a19348570cff2619348570cff2614348570aff2a13148570cff2613148570cff2619048570bf768c9048570ddf6554308570dfe68d9008570dfe50d90085709ff6889858d50cff698984c950cff684984c950cff261624c950cff68c9858550cff6889858550cff26143585509ff2a53258550aff2a13258550cff2613258550cff698984c550cff688984c550cff288984c550cff261624c550cff6989848550cff68c9848550aff2a19648550cff2619648550aff2a19348550cff2619348550cff2616348550cff2614348550cff2616248550aff2a13248550cff2613248550efd2616148550cff2619048550bbf6989048550bf768c9048550f9f5895158150aff2a12158150ebf5958458530faf5948458530fb759543585309ff2a55258530cff6598454530def6588454530df76594354530edf6115254530fcf2115254530fd750d5254530fb7589614c530cff6619748530cff26 else 0xc6b714dc3b708dc0b6fcdbdb6f0dbab6e4db7b6d8db4b6ccdb1b6c0daeb6b4dabb6a8da8b69cda5b690da2b684d9fb678d9cb66cd99b660d96b654d93b648d90b63cd8db630d8ab624d87b618d84b60cd81b600d7eb5f4d7bb5e8d78b5dcd75b5d0d72b5c4d6fb5b8d6cb5acd69b5a0d66b594d63b588d60b57cd5db570d5ab564d57b558d54b54cd51b540d4eb534d4bb528d48b51cd45b510d42b504d3fb4f8d3cb4ecd39b4e0d36b4d4d33b4c8d30b4bcd2db4b0d2ab4a4d27b498d24b48cd21b480d1eb474d1bb468d18b45cd15b450d12b444d0fb438d0cb42cd09b420d06b414d03b408d00b3fccfdb3f0cfab3e4cf7b3d8cf4b3cccf1b3c0ceeb3b4cebb3a8ce8b39cce5b390ce2b384cdfb378cdcb36ccd9b360cd6b354cd3b348cd0b33cccdb330ccab324cc7b318cc4b30ccc1b300cbeb2f4cbbb2e8cb8b2dccb5b2d0cb2b2c4cafb2b8cacb2acca9b2a0ca6b294ca3b288ca0b27cc9db270c9ab264c97b258c94b24cc91b240c8eb234c8bb228c88b21cc85b210c82b204c7fb1f8c7cb1ecc79b1e0c76b1d4c73b1c8c70b1bcc6db1b0c6ab1a4c67b198c64b18cc61b180c5eb174c5bb168c58b15cc55b150c52b144c4fb138c4cb12cc49b120c46b114c43b108c40b0fcc3db0f0c3ab0e4c37b0d8c34b0ccc31b0c0c2eb0b4c2bb0a8c28b09cc25b090c22b084c1fb078c1cb06cc19b060c16b054c13b048c10b03cc0db030c0ab024c07b018c04b00cc01b000bfeaff4bfbafe8bf8afdcbf5afd0bf2afc4befafb8becafacbe9af3cbbc2ea4ba02e3eb7f2da6b56ad04b35ac76b122c10aec2b46abeaa9aa93aa02a68a942a38a88ca1527f49e5273e9ba26b099ba63697fa59e959a524938a48c912a3f48e7a33e8ba229288f21e68692158845a0d4824a05a7fe9f9a7d39ee47ad9e887919ddc75c9d0872f1c6670e1bd86e59b726c49ac66999a06667194664398c261898205fa17925cf16f05b596bc59e962458295c8555150852c946650693ec4ef93724c492bc49c122e473919645511124319084413100a3f20f7c3c98eda3a88e6a38c8df036b8d6c3458cca3248c6430b0bf42ef0b8e2d58b1e2a309fa26e096224588ac213081e1f707861cc06f81ab067418f06041690544136848e11083e20ea83360b582a809e824c08781be05780fe02f007a0108000cff6899120173cff2899120173cff6999220153cff6859220153cff6999120153cff6899120153cff28991201539ff6809854d619ff6889054d61cff68c9854961cff6809854961cff2809854961cff2614354961cff6959220161cff6859220161edf2a19520161fdd28595201619ff6889058d519ff6849058d51bdf28163549519ff6889058551cff6999220151cff6496220151cff6989854931cff6909854931cff6809854931cff2616454931cff26162549) else (if j<6 then 0xf0fc2e01c1620824d8d0a4971dc6a028873c6779cf71dc670dc2801ce71249a20bb3949b1ec260188b3c7b1ec4b0ec2402cf5258822c7b12c3402ce525881ec5b12c3b0900525881cc731b41e00431cc6d078012c7b154112488602c61f13c4b45d1342d0740b0cc7274ef13c1f0344d08c7c508c9344d0ac3d071231c730dc2705c091dce1a93a480bb10c3b06c0b394725c470dc2895ce15c470dc2704c06506a92c3b014eb06921aa4b10c3b0947b06921ea4b0ec0b0528a486f07c053d43d385f13c1f034ed0a141bc4f07c0d3b42154602c0400f42d3897450702c090140400c01d01122324b3ec3f0b12d00c71f24338c7d03121724f08c7d0312172431f400a31216ce226c2d0014c48601ec3b0ac1b02ce181304ace2308bb08604c8bf13c3f0bc1b008c2313c4acef0c8bb08141c13048cf3388c14130488c1a44c5413048282305c5413123c22305d3ac3d08c7c505d38c7d0b14134e31c25d0b14169512448d081414558509444886715c4709c17001544c12f0ce1561344e12449c5711c17001525086f0fc239c3709c1701cf738684e12709c1701cf11dce2215739c470dc1700941e1584e1273bc3f07c0f1086250a84e12739c470dc170047250984e12741cf1213849c41549477c649215853c4f0fc2f05122214711c37092411dc1448884dc1701cf738585613711c37049444878561470112734584e1270dce1a45852138485b154505613849c470dc1701c225090561484dc470dc2705c04489715c470dc2705c01549444d122a1515614251c544d121c1304ac1b02cfb12ce1d1504c12b12c3b06c0b08942515452c184a24154b529495228650d4250540517442c145134350945a521311e12240c7114f154491ec493e551247b124f954411ec493c55100a52548515441094150286254a52408515445094110286254a52548515445094150286241304986d16c3954604d8861b45b0e55198962345b0c5517c1f02cef13430506ecebb34ecbbb28ec8bb1cec5bb10ec2bb04ebfbaf8ebcbaeceb9bae0eb6bad4eb3bac8eb0babceadbab0eaabaa4ea7ba98ea4ba8cea1ba80e9eba74e9bba68e98ba5ce95ba50e92ba44e8fba38e8cba2ce89ba20e86ba14e83ba08e80b9fce7db9f0e7ab9e4e77b9d8e74b9cce71b9c0e6eb9b4e6bb9a8e68b99ce65b990e62b984e5fb978e5cb96ce59b960e56b954e53b948e50b93ce4db930e4ab924e47b918e44b90ce41b900e3eb8f4e3bb8e8e38b8dce35b8d0e32b8c4e2fb8b8e2cb8ace29b8a0e26b894e23b888e20b87ce1db870e1ab864e17b858e14b84ce11b840e0eb834e0bb828e08b81ce05b810e02b804dffb7f8dfcb7ecdf9b7e0df6b7d4df3b7c8df0b7bcdedb7b0deab7a4de7b798de4b78cde1b780ddeb774ddbb768dd8b75cdd5b750dd2b744dcfb738dccb72cdc9b720d else 0x902004e0f4200400d3a15850a02c0501003d08a5850702c0501003d08924507b0814c903825c761a0ce01ce1a0971d868338073c673a0971dc3713808319421cf619c1831c3e01ce1c13711c27059473f80830883380745ce11ce619c470dc27060ce0194260ce01d073c471380831df650504dc5711c3709c165380830902c090140400c0200594e020c2acf42686432c3e02ce1d0b42a86b06c3f0b80432c52413b12c1b3f80431141ec4b0a94b3d09e010c1c13b1505b12c2b0694e010c26ce42686b12c3b090ce02942686416c4b0ec2b07804329426ce426c7a1ac2e010cb3c8b0b80432a8b3c5b1ec4b0e94b3d09f0b80430904ec4b0ec1a52cff0b804309b380c42ec7b12c1a029422ce426c7b12c343380a508b390ce0298a505f13c3f0849d004c18090074093e4e1413d024f9384c140b02405010030044cd0b402413e1742d004c141312f85d0b401306f13c3f0b41d004c1b85e1383e0b141274013080320861d86705cf19ce8218770dc1831c46508b3908a1e86b050cb0acf22cf03108a1ec4b0ec1f0a9526ce0310ba1ec4b06c0a508b380c42287b12c3b06942013049c5f0fc1f0294130804c12f13c1f0195a504c22c430ec2b06c0a50673dc4709c1301c37387711c3709c1301941813717c3f0bc1148604fc4f0fc1650521bc4f0fc214c521413049c5f0fc2f07c0a544c241304bc4f0fc1f02952504c2413f13c3f0bc1a54521c1304bc4f0fc2f07c025494130ab3c14b0e9512cff0ac3a54404c12b06c053d4e1a9504c1202ac5b12c330ac1b00aa569404c08b16c4b0ec2b04c0280b0280900c020058761b40914a92c0a9258761b409307c1f06f13c3f0ac0704c82307c19c1b00432cca324c3308c1c1f06b00901c06310c3308c81b07c18cd0ccb328c930cc230707c1ac02409d1801d028f84a8e1c0b0240400c01d0094e3a12240902004e080100055e3a14240b0138200740c938ef0e12850a024080140400400e09142105b0f82052551413f13c3f0bc1a008c1c13327c4f0fc2f07812208c240701945a0e82a20601e84a0c18a20551fc4f0fc2e00c151a88214751945f0fc2e02c1a20851fc4f0f80562c1a207a4ac10a92b04201d8460d82019881a4791bc4)))
def mo255H9 (j : Nat) : Nat := 0x3c80000000000000006194000000000000000000000000987800051e00000001082000000085880000000000000000061ef40361600000002c7970dc000000000010280000000000000000001c8000a20d462000000011f40000000000913000000000000000000285541c000000080f000000000000003c4d0003821e1ff4680001e2f000301b000340e0000000000000000000000000000d8c0000000382500000000000000b49c000000000000000000000000104c000000000000000000000000000000000000009058034a9d8415654bc7444a00000000000000082c0000000a1140000002e4000000000003d0d000000000024480000000000000031484280000000904000000000000000000000000000000000000414c03481211100000000000c108000000000019200000000000000000000000003949a61a86c00000000000000000000101d686400000000000000000000000000000000000843007f5640000000f14c0000000000980400000000000000000000205c0000000e49216f803c00000000000000000a19000000b80009045c0bf94e25f0000a6641ba12a30b400000000000002c240001830080c000046566800000000002835e1f800045640009080000000000050ab547e1c4216646800000024730000000000295af12800000004590003a29000144ba0fdc01409b00961a51340000678e1780000000000311fe5a6978e1f716867301f000018700000000000855660e0000000000000000000000000a3f000000019880000000e1221c0e45419c00054dc000593000000004175154433390400000000000001438940345b000000030c800038b8000c0c40000000000990c000000000000000001908c3ef4f4000d8a000008400006000000058400000000000000000000000021440000003b18a0f6885115fc6d707800000000000001c54000346160140000000000000000008840000003d500003c760001e140000e63f82c000a9aae1100000000000040f953446000000051dd43ae4d6a230000802c14000090300000000000000000000000005207a3ed0ed939c13cc6f01d4000000000000000000060d56000000000024668498536f105163000000000000000001a0d10e40560000000000000000000000002c1989d400000000004124000c0d8000118c00081ab02b00020270000000e21041a0000972000000000000000000000000153328b302f000225600000008021d320003249000262aa1ace0a283c0008880131501085dd17c000000000000000000000000000000000000000000000e1b0000000000031829650002423000000000000060002e18b92a0071139429a08ac7a000000000000002002000401030211010603001011a000001090040003020541030311
def mo255D10 (j : Nat) : Nat := (if j<5 then (if j<2 then (if j<1 then 0xec1ae2886ff609714437fb06b0a21bfd8258510f7eb12c2886ff619514437fb06a8a21bfd8254510ffac3a62887fd61931443feaec98a21ff5854c510ffabaa62887fd59531443feb0498a21ff4824c510ffab9262887fd58931443feaa498a21bfd864c510dfec1262887fd5c531443feac298a21ff5514c510ffa4c242887fd65d21443feb0e90a21ff59648510ffac3242887fd5d921443feb2a90a21ff58548510ffabaa42887fd59521443feb2690a21ff58348510ffab9a42887fd58d21443feaa690a21ff54348510ffab9242887fd58921443feaa490a21ff53248510ffac8242887fd24121442ffb2c90a21bfd8348510dfec1242887fd5c521443feac290a21ff55148510ffa98a42886ff60970443fea42b8221bfd8558110f7eb2ac0887bf58960443dfac2b0221ff52158110ffcc32a0887fe60d50443ff2c6a8221ff94354110ffcc12a0887fe20950443ff2c4a8221ff93254110dfec32a0886ff60950443fea42a8221ff96054110dfec3260886ff615304437fb0498221ff5214c110ffca8260887fe26120443ff30e90221ff99548110ffcc2a40887fe5d520443ff2ca90221ff98348110ffcb9a40887fe54d20443ff28690221ff99148110ffcb8a40887fe58520443ff2a290221ff93148110ffc90a40886ff61520442ffb2290221ff52148110ffcb8240887fe54120443ff26090221bfd7660c10dfecbb04086ff659820437faecc1021bfd835c810dfec12e4086ff615620437fb06b1021bfd8258810dfec12e0086ff615600437fb04b0021efd6258010bfecb240086ff615200437fb0490021ff960480109fec8900b9cff6488054e7fb22402a73fd92201719fe4c2a4b0cff64880586efb2a402c33fd92201519fe4c2a498cff261424c67fb2440263fe55258521afecb90090ddf65480486fbb2640243b7d855cc21ddec22e610e7f61d430876fb0aa1843bf99760021dfcc9b0010efe5cd800877f286c00433fc984c5709fe4c242b85df654215c2fbb2610ae17f990085709fe4c264a84ff261615427f93098aa13fc9848550f3eb2ac0a857f65c214c2efb2a10a617f99008530bf64930c8857f65c82442dfb2c4122177d9520910beec9904884ff261524427f93099221fe55248510ff898aa0887fc48550443fe26290221ff121481109fecc240887f9485204436faecc2821bdd7660c10df6cbb04086fb659820437daecc1021b7d855c810deec1ae4086fb609720436fb0ab1021bdd8358810df6c12c4086bf619700436fb0ab8021bdd835c010df6c12e0086df615600437bb06b0021bed8258010cfec3a40086bf619200436fb0a90021bdd8348010df6c1240084bf6588054e6fb2a402c32fd962015197ecb10098cdf654804c677b28402633ed92201319beca90090cf764c80487f3286a0261fe12148110 else 0x22a298ff74c9514c7feaeca0a63ff57550531ffab2a8298ffd5c9414c7feac4a0a63ff55250531ffab8a8298ffd585414c7feaa2a0a63bfd7620131dfeba90098eff594804c77fae440263bfd6220131dfea910098eff5c4804c77fac240263bfd5120131bfe4830e90eff61985486ff920c2a43bfd7560d21dfeb2b0690eff61d834877fb0ac1a43bfd8460d21bfe4830690dff26173486ff920b9a437fc9854d21dfec32a690dff24153486ffb30a1a43bfd8550d21dfec1ae290ffd61561487feb06b0a43ff55358521ffaa1ac290eff60d61486ff920b0a43bfd8654521dfec1aa290ffd585514877fb0c98a437fd944c521fee9926290ffd58531487fea8298a437fc904c521dfec3b0090eff615804877fb06c0243ff56160121dfeba90090eff594804877fae240243bfd6120121dfea890090eff48480487bfb2e40243bfd8720121fbeca90090eff61480486ffb2640243fdd9320121ffac890090ffd584804877fb00402437fc905cc21dfec2a8610eff65d800877fb26c0043bfd7360021dfea1b0010eff261215c2ffb2010ae17fc9858d50dfec3286a87df59543542ffb2c412a17fc9858950fbea9ac4a87df58d52543efa86a92a1f7d6254950bfe4c264a87df59532543efaa4992a1bfc9858550f7eb12c2a87df58d51543efa86a8aa1f7d6254550fbe992a2a86ff26121542ffb2c90aa1ff56148550f7eb0ac0a87df545605437faeac2261bfd6561130fdeba908987ef594844c3fbaeaa1a61fdd6550d30dfec22e2987ef211714c3fba86b8a61bfc9858530f7eb2ac2986ff611614c3f7908b0a61fdd4358530bfecb2a2986ff619514c37fb08a8a61fbc8454530feea1aa2987df549514c3fbaec98a61fdd754c530feeb2a62987f75c9314c3fbac498a61fdd524c530feeb8a62987f7585314c3fbaa298a61bfd9848530dfe4c242985ff655214c37fb0890a61fbc8448530feec9a42987f750d214c3feac290a61fdd3148530bfeca842986ff610214c3f790810a61fdd4308530bfec8042985ff659504c3efacaa8261f7d5254130fbea8aa0987fe5d5404c3ff2caa0261ff97150130ffcb0a80987fe545404c3ff242a0261ff82150130ff64930c886ff61985443dfb0cb2a21bfd7660d10dfebab06886ff595834437fb0ec1a21bfd8660d10dfec2b06885ff26173442ff930b1a21bfd8558d10bfe4c2a6886ff619534437fb0ca1a21bfd8550d10dfecbb04886ff655824437faeac1221bfd6560910dfec9b04886ff5cd824437faa6c1221bfd4360910dfec3b04886ff619824437fb0ac1221bfd8360910dfec3904885ff658824437fb0a41221bfd8320910bfe4c2e4886ff60d72443fd904b92217fd9858910bfe4c2c4887bf619624437fb0ab1221bfd8358910bfe4c2a4886ff60d52442ff93099221bfd854c910df) else (if j<3 then 0xa2987ff65d214c3ffb2a90a61ffd7548530ffeb8a42987ff585214c3ffaa290a61ffd9048530ffe90ae0987ff085704c3ff924a8261ffd6254130ffeb0aa0987ff485504c3ffb0cc2a21ffd8760d10ffec3306887ff5d983443ffb0ac1a21ffd7560d10ffeb2b06887ff61563443ffb0ca9a21ffd8750d10ffec3286887ff5d943443ffb0aa1a21ffd7550d10ffecbb04887ff61d82443ffb2cc1221ffd8660910ffebb304887ff65582443ffb0ac1221ffd7560910ffeb2b04887ff64d82443ffb06c1221ffd7360910ffeb1b04887ff54d82443ffa86c1221ffd8720910ffec2904887ff5d482443ffb0641221ffd7320910ffea9904887ff50c82443ffb06b9221ffd435c910ffec12e4887ff61562443ffb06b1221ffd5358910ffea1ac4887ff60962443ffb0ca9221ffd8354910ffeb1aa4887ff50d52443ffb04a9221ffd6254910ffec3a64887ff61932443ffaec99221ffd854c910ffebaa64887ff59532443ffb0499221ffd724c910ffeb1264887ff54932443ffb06b8a21ffd435c510ffec12e2887ff20971443ffa64b8a21ffd8358510ffea1ac2887ff60961443ffa64b0a21ffc9058510ffec32a2887ff60d51443ffac6a8a21ffd4354510ffec12a2887ff20951443ffac4a8a21ffd3254510ffec3a62887ff61931443ffaec98a21ffd824c510ffe41262887ff5c931443ffac498a21ffc9848510ffecba42887ff61d21443ffb2c90a21ffd8648510ffebb242887ff64d21443ffb0690a21ffd7348510ffeb1a42887ff50d21443ffae490a21ffd6248510ffe99242887ff64121443ff92090a21ffd825c110ffe412e0887ff48570443ffb0ab0221ffd8258110ffea92c0887ff54560443ffa42b0221ffd8654110ffec12a0887ff20950443ffac4a8221ffd6054110ffec3a60887ff61930443ffaec98221ffd854c110ffebaa60887ff60930443ff90498221ffd724c110ffeb1260887ff54930443ffae298221ffd614c110ffea8a60887ff48530443ff93090221ffd8748110ffecaa40887ff61520443ffaea90221ffd6548110ffec8a40887ff5c520443ffac290221ffd5148110ffe90a40887ff5c120443ffaa090221ffd9748010ffecb240087ff5d920043ffae490021ffd6248010ffeb2a8498fff59543487ffaca90a61ffd6550d10ffeb2a60885ff26153586ff920a9ac3efd6550d61dfea9100b0fdf65480586ffb26402c3efd6458d51bfe482c6a8dff659435477fb0ca1aa3f7d6354951fbea1aa4a8fbf58961546ff920b0aa3bfd6220151dfebb30898eff5d5844c77facac22637fd9620931bfe4c2e498eff611724c6ff930b1263bfd8558931dfec22c498ff754d624c6ff930a9263bfd8454931feebaa6498ff7595324c77fb08b8a63fdd325c531dfec22c298fbf589614c7fba64b0a63bfd8654531dfec else (if j<4 then 0x99ea938a866a7dca740a6b6a62ca5a2a52aa434a398a2fca260a18ea0ce9fd89ef49e7c9dbc9cea9c189b589a8699b4993c98c4984c97b097269666957094c2940292e891f290fc904e8f8e8ece8dfc8d848ce88c5e8be68b028a7889a688e688268754869485b08502841e833a82208172807c7f987e6c7dd07d107caa7bfc7b967b1e7a7079c27938788a77dc76f875de7530743a738c72ba721e717070d470266fc06f126e646dfe6d866cfc6c726bfa6b826ae66a926a2c69c668e26834676266c665e264fe63c062ee61b060a85f7c5eaa5dfc5d065c465b865aa259f45934588657ea577256c4563a559e54f053fa52e051fc512a508e50044f564f024e424d5e4cd44c384bae4b6c4b184a6a49bc4920489647b2477046c2466e459c44b843c2429641b240e03fa23eac3dec3d503c903bf43b343a8639ea38f4383437bc36ea363c35c4353a346833a8331e32a6321c3180312c307e2fd02f342eaa2dfc2d4e2ca02c042b7a2b022a7829dc296428ec282c27b426d026582598250e246023d6235e22e62238217820ca1ff81f5c1ed21ddc1ce61c4a1bd21b361abe1a46197418a217f41746168615c615061422135012a21218117c10bc10320f600eb20e160d560c840bc40b4c0ac20a4a09e40936088807ec0786070e067205d6053a04c2044a03d2036c0306027c0204019e012600ae0001ffd4354961ffeca900b0fff50d62547ffa86b0aa3ffc9058551ffeba90498fff551624c7ffac8a9263ffd6254931ffebaa8498fff209714c7ffa84b8a63ffd4258531ffeb22a298fff209514c7ffac4a8a63ffd4254531ffebb28298fff5c9414c7ffac4a0a63ffd8661521ffec3b0690fff61583487ffaeac1a43ffd6560d21ffec230690fff61173487ffb0ca9a43ffd8454d21ffeb22a690fff61d43487ffb0aa1a43ffd7550d21ffec1ae290fff50d71487ffb06b0a43ffd4358521ffec32a290fff60d51487ffac6a8a43ffd4354521ffeb12a290fff61d31487ffb0c98a43ffd764c521ffec226290fff5d131487ffac898a43ffd724c521ffeb126290fff50931487ffb2ec0243ffd8760121ffecab0090fff61580487ffaeac0243ffd6560121ffec9b0090fff60d80487ffae6c0243ffd5360121ffea1b0090fff5c580487ffac2c0243ffd5160121ffe98b0090fff65c80487ffb0e40243ffd9520121ffec290090fff5d480487ffaca40243ffd9120121ffeb890090fff58480487ffaa240243ffd8020121ffec9a42b87ff50d215c3ffa6290ae1ffd9048570ffe48242b87ff50c215c3ffa86412a1ffd4358950ffeb1264a87ff50d61543ffa64b0aa1ffc9058550ffeb1262a87ff65921543ffb2690aa1ffd6348550ffea1a42a87ff58921543ffa6490aa1ffd9048550ffe48242a87ff48560543ffaa4b0a61ffd6254530ffeb0a else 0x26860923c54a7082686090a46a2a63888ae184d0c12228bc4e1a538413430488a2f138694e104d0c12231dc4c16002a131b1fc409e0c28121b1dc409e082a121b8421c0054262f0c41800a04c5c371387c206027003e1b89c3e160026370c40130a0485c371387c20404c60071387c224a2060a8502612e270f85c1e0133279326d326132553249323d323132253219320d320131f531e931dd31d131c531b931ad31a131953189317d317131653159314d314131353129311d3111310530f930ed30e130d530c930bd30b130a53099308d308130753069305d305130453039302d3021301530092ffd2ff12fe52fd92fcd2fc12fb52fa92f9d2f912f852f792f6d2f612f552f492f3d2f312f252f192f0d2f012ef52ee92edd2ed12ec52eb92ead2ea12e952e892e7d2e712e652e592e4d2e412e352e292e1d2e112e052df92ded2de12dd52dc92dbd2db12da52d992d8d2d812d752d692d5d2d512d452d392d2d2d212d152d092cfd2cf12ce52cd92ccd2cc12cb52ca92c9d2c912c852c792c6d2c612c552c492c3d2c312c252c192c0d2c012bf52be92bdd2bd12bc52bb92bad2ba12b952b892b7d2b712b652b592b4d2b412b352b292b1d2b112b052af92aed2ae12ad52ac92abd2ab12aa52a992a8d2a812a752a692a5d2a512a452a392a2d2a212a152a0929fd29f129e529d929cd29c129b529a9299d299129852979296d296129552949293d293129252919290d290128f528e928dd28d128c528b928ad28a128952889287d287128652859284d284128352829281d2811280527f927ed27e127d527c927bd27b127a52799278d278127752769275d275127452739272d27212715270926fd26f126e526d926cd26c126b526a9269d269126852679266d26612655264925bf2523248723eb234f22b321e121572097201f1f831f1d1e5d1dd31d491cd11c471be11b211a3d19d7197118b11827178b1701166515b71509149113f5132312bd1233118510fb103b0f8d0ef10e1f0d4d0cc30c5d0bf70b5b0ad10a47099908d90807076b06ab05eb051904470351026d019b0092ffc0feeefe40fd38fcd2fc00fb64fa92f9d2f900f888f7fef762f6a2f5d0f56af4cef40ef384f2e8f270f1e6f138f01eef82ee9eee38ed66ec94ebe6eb14ea78e982e8c2e7cce6c4e628e544e44ee358e262e16ce0ace046df74defcde06dd58dcf2dc56db96daa0d9f2d920d8a8d7e8d770d68cd602d566d4cad3e6d34ad2aed200d164d0c8d01acf6ccebece10cd50cca2cbf4cb58cabcca0ec960c8a0c7bcc720c660c58ec4e0c3d8c384c30cc2a6c1e6c14ac0d2c05abfacbf10be86be0ebd84bcd6bc28bb68baf0ba78b9cab940b8b6b81ab77eb6e2b634b598b4d8b43cb3c4b316b244b1ccb154b0dcb064afb6af08ae5aadbead22acbcabd8ab2aaaa0aa16a))) else (if j<7 then (if j<6 then 0x8863184cf54061467a1988c260b018655262ace4c25048a8508ec461b0982246021824584c24c56230d84c16015528474319444250d074140d010113893380e94348b842260c87822160483802015529138911d00a01a8bc4e1f0b83c02ac4e2447320e47433058013094199ec467171523a1b0b45a231286c3a0b0680c0098498494462b148391d0cc461b0a0cc109b002468320ec7034058211a04219c530e27c1e04499f0667110689b3f89c2e0f0229122a950789f078112833459c401c0d43a0a04494f602229c550d27c1e024a9e8623d38909d128340093391498202813a22128482a0a069e860db01246a51274fe270b83c049218aa511c2686a784a9c351d0f44423390d4309849848a2d0dc24a53c8fc409848aa4c4c1ec42795624311085138923cab861c0f45a22128683098490cc2451745e270f84554a2182612239545098491ec32ae18703b1a1f8009c38605f138714c760026382c0fc4e1e3b0014099013878485020301208e0f029dc40a85090d82b0dc4e163c2615091253e0f031fc4290522a402f89c3c704c30121c1609c070e854ee229428482c158602f102fc3e10909058280b86e270f85800993436170780cee205428461b8253e01489e4e1f87c129f00a4281b0dc4e1f0891c1320e18a0d011487435969e404d0e86a785a9c35010e8647a3a9a354a8b40e2257868a43a1a9a570781078333d9c331582c8e270e2bc28a70581078319c183c1980cf670cc5e23038715e14520f06669407a3493828f092387048228f46c2707808f4713c12370094472c63c7c091c8d8f096386e0f008f8f23638605f13874092705298e0912090450f05c1e063b88550a140b03f0e498ee270428122416090451f8782e0f031dc40a1713627011dc489155284603024f2391b484e1c3185c0e038855e192b83882391b486e170380e21578654e1707104752118dc371385c1a7f028647230dc1e013c8e4e1b0c5be270b824be011c8e1f04abc0238a06e270cabc2238946048228e0be1d0b83c0a771028582c158602f1281c3e149382122c2a076170f83c067710284d0981c31253b89c1090509098498f42e1f07814ee2050a0a51c0cc0e270f8424e0848a0a04c25c4e1f0b83c02a91ca2381789c34370b8313e01552912302a140381b89c3e170627c08916d589f07810a62c4a0cd125ab08e0c4e0cd1670ec389f0781128333d9c44538913e170597c067c4a0c570627c089419a2ce1c3147a250d27c1457012486a79624a3d0d11c149a1a9f4e268693e0f01254f435388a5a638893e0a2b814f49218a1252f89c2e0a51115ba7a4d0c5a538893e170697c0a7a490c510c26864a84a9c351d0c8a09a60254f1e8e134353c254e182686a784a9c2d1d308ae253c2686aa8489a3f0929c4a784d0d5509134be1253894f09a18244238 else 0x250d074240a5e28592c9445e270f85c1925002454900f06a22128683a0a06808a89190ca3a1c094240d392f4f2618894411e854140d010144a753cca3a1e8884a120903144953e869732188a44a228884a120a8281a02029f432a9e06c23130581c04509e55269d0c43d1108c3015050340404512a6d3a194743d1109434180903144b990c45a251047a22128683a0a068080a750a2884918ec260b3e254067101463b1186c19233f8512a0151668d0224ce1648ce63b1186c189052804c5a80d067c4858b31280148937c60a31588c3613064912a013240a0198bc21250224c7262ccf60b0e8112670f160a24d88c260b3e8112262cce6230d84c1a0448284c919e87a2211874140d0385124a988b4511d0b444250d0742415050324a0448f8b61d8ec260b3e80ce89131649b1f0ac56230f04c2608528112362cc7c2b1186c1a00522448518a5549f1387c2e0f0124472d9e8c6130580c314b38889c4a8ec260b019e4767121b67a3188c260b00aa444e24cfe17078047e2154989c499cd12a8b156723188c360b020e142627126731186c16011c284c4e25076833c589c4988146f95465245789c3e1705243b1186c2523048e921e264760b3d9c921a26c461304aa921a2b1323b1186c10a24888ab019a9212271261b38d22c4e24cf2d95450ac4e24ce4631186c1603088e14302a476230d84c1523012448518ac461b0982c02aa4d24472e2a550a3178493032488c21130442c090700408a33c1855328b444250d07424120628074ba48c23c190b444250d07424150503404024cab144923134611d84c1604499f0762338b89c491847c2d1708c4c130b02c1c030028c32aa31589c491847c2d1588c360b020ec20a1c968ac4c8f45a231286c3a130a82c10a3012482251047835050340405129f4e2c268723d1283400953e9c4d1d0f444250503404044e24cea1a50dc260701138933988c22aa50a23e118982c0e02271227954a0361288c4c1607009489c489e55302612a7d128541a050caa484c24c76230d82c0a750a2855398ec461891834209450963e1588c1125082514230ac0a10499b141826126230d82c0a750a28484c244ea750a28c71c261262305814ea14508c2b1186c160092851409134e43c1a888461d050340405092b143516894411e8884a1a0e8281a02029d428a1e9509d390f4263f0f83c00971028631f0ac56230d82c00984a85142d0e8461a0a831292254843a1107414544a483a2d14854220d05418949094ad062524128f85a250e8013a0b08249428261223b1529c4e1f0b83c02aa18c6130580cf8311d9c3c559dc3e0f010dc44a10ce6230d82c023a50767b41281b10aadf4a09146230d8506608908e12260e474330449066033d9c4c548ec461b0448124a11158a41d8106093347098488ec56230d84c1601552) else (if j<8 then 0x2866130581c063986550a1086c25118982c0e031c554a1547435118943a0d02271247250b4641d8f066310421086792de67c1d8f066341186c267312821e891cd08433e482355a8c4a0c49be331d8d4167c4856f33d8ec661b099cc4a0c48aa3a1c0d4213539114f229d47a12229ea41a9d47a1305254f191489a7f1385c1c050caa4e1085806731302542a9147a250e854f442987a3d0a9fc4442906a3d128742a7b05243e108380a711302242a154989d110941a720430924a934743d11094341d398218491547a250e9c88520d47a250e9cc1490c46c251307804ae049c54258f062360624ce8b8ec78311b031267c5c76731d87816245ca912219f062360587176744888331185812a33e2f12219c466230d85818945ca84b398f812330a2ecf8910c70331187812a33f85178914ce63b1187818b95224420789c3e125d24322d14070321789c3e12909c2e108983219070115c0890a85d168943a12214c35168943a122148371387c2c0a5d2435168943a13052430530b45c260b0181619549035168943a1604a897491215c2e130780c091c9458240f454220d0409495188a3d1789c3e1305254620934560d1924291c8c452210c8581c0154a89252194e2591c8d812212a25242587812731225242a0f44626049d12921507626049c54894906803422ecf8b0ade67b1d8cc3614019cc48bc58b6731e00c28bc599e3b1d88c3614019f178b10c76230e00ce8bc58762b1186c28045e2c3b158f414412700c61e9fc2e0f038855192692a3b1d8b446250583406030e286d3b89c1e051229422a908c83b1d0d0108c5d9c42320ec74340421176790ce83b1e08c380c49881e8ba50b9251d8ec2609019f4189338a4a51d8ec5a231284c260c9282c3891b24a3b1e88c4a1b0d8240a0a5224611f832427d009c3030954f0371385c12ac928054928e878351109414087115122c184b23d380dc4e1d0b8324a0161943d1108c3a0a0629124a940d43c1a888461d09054189254b06d1d0f06a22128683a0a2a245b0d85c1e033d9c333b89c3e0f012834261101803419e315613086240600946f90a4e0f1387c260a4871123212474340582c067b38a0cc2e124782c11890361c058294491b0b8541609038130124cd2627126150583406033c8ece2a29138911e8b4462509854160d0180c32a9f138951688c4a1b0e82c1a03008e94362945a231286c3a130a82a46091d246c4e24c260b019e286751c9060199fc4e170780476192ca89c499cc461b05804e4a51ca524520d456230d842460a4a8e592491c1e0138d234320d43408a69e97a71028a1f07814f23d387a7f1385c1e015460612892482381b89c2e0f029e5b308fc2e0f009fc42a8f13a22128281a020224ce0da50ba2212848240c529e920da5ca2592491c4e1f07814ea1050aa74300f444 else (if j<9 then 0x8c3c00522f1620410963c190cc105e019d0c28430963c190cc1056019f0c299c0b84b1d83056230f010c4a16200ac260c8661b059f8086338b09c2a130682b1184c14a33c1780861ace84a1988c3613042b05c0431286084290963b098286676019f0c2c260b84b1e0ac460a5187c20a33f010c399d0b84b1d88c360c1700948616130912491c1e00a09e2927130ba2310854160d0180958a12130912491c4e1f0780180a8529d42261d01a034224cf159c878230e02c1a03103c9489161261b0a82c167d019c44542545a231286c3a0b0680942e88c4a1b0e84c22015d8264282649e270f85c10a8508b4026164929706804f270c1324e06804f2713072912c0e06e270e9c67229c8c83d110941408651714282649c29170983c085680142617c4e1f0a8252162a8ca2a1107404a534883c180942a0a05814e4953ca6731182c08a85286385188c16053f8515a190c460b3a86148a8c14c2b15814366c547a7c1e8884a1f092f15491215098489248c29170982c0e022814a1930fa723108814022e3114229d07a221286830150502c08a248cc2b0c30144a8a8ca2d110942415050314a0254bc2e10898321e08851403b04a4581b0b84c1e092b142915c98b6168b44c150a83400a30d2a5e170983c1052805732101324e170983c16042b1422852804c3498c3615058340603119ece2a2a4ca2d11894361d0583406030928695a2b14a2d11894361d09854160b00a470528942a0d019e9561902184c210e8660b0015078333e18633817098441d0ec16041588c386250d10852130883a1d84c1603390d0c679acf84c210ec461b058105e10521895359d0b84c220e876230d82c082c312868508a154331182c061b0898531787c22994856230d854160d0180cf140a59c5f1386940a14ca434560f446250d86c2a0b0680c027250d0981c0dc4e1f0b82c02913c4e1f08a453142a87e270f84952994880a33c0d44a0d009fc261a54a8aa562894a2b1588c36141e0c53291a490461c264fa01389986242a8c43a1a8a8441d01848aa697c1e033e0f06670d078330789c3e145628c032942283c199ece328d07834160903813022b1429b34a4622511c1e06111e8e1c9248e0f031e47236388249571dc4e0d030494231c0da3a1e8c86a222d094145448ca3d111cc461d022494231c0ce0f0388c325c508249231dc4a1f0781824a1313a231282804724928461288c4609561c928a1047c251188c3873012514251984a231182c08715628492c9340c770f89c10925099251283404731187124a1324c25118941a023b87124a14894463b89c1e060a8655260d846260b0380c7156284a918f44623061d144910c7a2311870e6045124424e0d446230580928745095251188c360b021d1449128b44a231dc4e1f0781820a158e0641f0844c160483802012e else 0xc480a78bd17c045874ac349b08625013c9422489e2ab1303082f15084a4349ac4a0279171220bd1245b1283004f250824d00a5c4e0d3b0695202649c3e130781a75001614261682a0339894d4a254784c2188c260b002ace86250ae214f1f83294546c781b85c1e23009115230840c7154c8284c9387c2606878e05500985610898ea0860aa521d1940c7211294d4a8f84623061d142a8c5583611810e66c50762638ab188a0a492461f0903c0e031c4c8a141309426110662305818e8602e30641f00d167448583e01a0cf890ace83b1e08c36207a8294891406e230f851225c5c72592a89c3e16012497220d4314d3d8292a70e4a22f1287c2c02492e445a8884a0a059c1b4a2489a221284828a53c36c1491344413392e94490c4b22d0b87c4490512e45380f06a22128683a130628922e0d126833e2e2b388ec36245d29121e8e8783012854e60a4a9e4d388f06a124a9e971e8e87a2212294fe150d8292280d84626070114e113caa4d3c8f44a1f0924972a914ea3a1e88842180a82818a248ba751d0f444250d060260c51245d388f44a1a4a28971da3808bb3a2c2b4300cf8bc5856731d86c4c045c29242124cf61e022f16670e14623099f808bc9074933988c3616022f160a1292c3d1d8ec2e1e022ece8b14c762b118782a130829808bc90b4931d8))))
def mo255H10 (j : Nat) : Nat := (if j<1 then 0xf138787c190a29d0736026743c510700003402706948f8d1560000aa180000e8dd00000000000071bab55970af75e141730000000000000000000040fc596b000000000000000000000000626de4310000ca200000f0bb78d429bc6122420319dc107ce1a90000a26b0000000001beb274f0a3000080fb3cf902791812c930a4d60000d43d253031fd0000a06370bc3564228c80ab24e600e2e8db8473b0f774721226706e0000292ba4193511e21b811dc8c2309d00000000b03a912cb1a2513b25498165c19f64b9613c10ee1868519c6180f1e375d70000f02900000000055e88f331f0106cc9e50000000000000000e242da38782dc47cd055b2054cefa0d60a2f61c4e00c594a64e3000052210000ea3f122df43e000000000000000031c2e8f4925f000018c900000000112734a88922008d00000000803531ed08d50000858401b699e430b0f1de3112455ff21e550c01e200d011b3000018d62126e054d1a422508a4d9142d191c8eaa1d900007278e62f14d7f2140a5d68711557393c12412845c8e11192b285d268b0970000e11aa15d058ca4af000000000000a10b0000e1a055aef161c62d14fd0000d51731ec0000594580e9000019bac06215560000000060e1206d60eb71cb627d2c170000f01dd153000041310000922395aa00000000220c2ce6150349b9185200005087a0287820d92a64b029db6034d5c50000b0c8a0d518bb8a2c000048eec562ca5b000050790000000090cd51ae116ed13a0000a100d46d824c216d105e09cd0000e263021f421649d4b8bc000098e8c266312b0000a04a909459bbd0f6b59c0000c425d8e53115b1987a576154000000000000f010143a00000000c258b209c2899460021d6ce9b08300000000000054282158c11691d0a1b900000000d009610f621c39c6462370b57080b22f903800000583f284920f10200000e235ce6d963fb05648ecc0c9518f00000000393bc41a81e7410e482eb61fa27251360000514b54eef2766022000065b651f30000b174f24fd17cc5db9a23520110c2303781c62642021f07013207601c07335700052d3f16000a0100042c0008001e010010353f02006600142100001b12140602049418050d045b0202154b06050120060c0a190201012408040d230803020b0e0902003122330e20010500272a010a010622053b3803000201060d1e2227000929030015220001400f04011a01041d0200312a000f17000128032a090602020042164d190b1d040202002700124909034b17021506000b0001031f0d01040c0021000a10001341080002101624260405041c0208480e010201010600001c006c141213021a2700010c00030e1227005d122a31150c003c0d001603080613001d0702002104025e041d0100051103000423090100080001030e00000d080905 else (if j<2 then 0x4275d1240000000019232865d9d6a4f4d804d61798d3c28d414f7a220000b07d1451b12d362b3071128ed94b2cf140d1e068c270928b60392458526ed0de3119962e30a05114f287b20d30a1e02e406a6940d9042607755b0000c28f519081a50000c6160000b101ba3784e5d86d9e7121fe24d90405a110c5558060a1ef30dad0ba70fa82250e73621aa251c9da5563f00a000070480000f1e868c866302179e16770b7914891eee8cda1b50000e49f005071690000a1e5f0c3f166a042820b1430e046211e243bb17291c8e5d01043e12ec00780f1e471c0b2ca4e000041da0000f46af02f000000004cf331aa7253916be60e54d80000e5c239bd161a418be855300f647dc0d2ba33000021b4028668c66e6fc9e2c1e6115a2178618515c4d21550e8f195e011f23ec204d05349c239c988f0d9ce54e4000054a50000217f00000000853cf2597875708c0000acf4c93e0000e10d000000000000000060add149906700000000423800002012a256e111000051fc000041ea915c0000000000000000000029df293101cada1e8cea259e81d6000000000000459df1442688b262f1b11a1bc801e051924a7008d27e09c7f29000ec56200000626c000002282814e86a3230d0f95106593740cb10b1614cf82bd5890000a9cc446719d5000020f5f00d9e6e0000c1a8c181927c0000017089565905443332240000d0789070513461c7019b0510e2915500024628c7c081f09e00002206a0dc00000002408af247500198ba0000b5187159703fd614d143781f6237b12a80cfd4fa803d05b58093000000000a47f8e3452e4a53411c287338f7d8eba0316267f0c1e9d2f548d23d5213a58b85b45ce8f52dd92511f9212f021945660000b05f103cc0000000704f9040f08b9a70353eb16f84780000e624f56bb00b91e920e0d0ff623318ab0027000071230000a2120000c257a5abf25c0000652a0000b059d1eb000039de71c9f16491a32150d55ce0e6000044b1107770a2493500003a7f887928e025de0000c15e2220ca1a08c00000c13000004273000082087099a231000051dd617579fc00009125b86f04d2c0df227b555a4019a03e9819f095659b754a2064ca09423f205b35fa850fa0c0f023d848994784da1633f2835537101eb04ba0c63a4af18ef1a7a408a1bfb04451b7b1f7f5c0c1b0015fc1d5313fc0890000b27f0000526a50a720e314fe85f478a7601be11f00a8000038ad009259aa0236d157919321f291c35631414d6a3b80c400000cd2b0853934b09f0000000060b6924408d700d4a5cb0102e24d00009117f07e0000817a205c0000f1bd222a3006808e58f9c0aa2184902ca18cd1c17a5081fb201fb19780a68014825e35e2a0d7d0bd7025c227623a44ec61cd81629249806191d2106535ffe1dfb076d26fc072801a68 else 0x909af10a1199f0c528aa2591a596d55db0db0000f9e0061c059f317d0000d171185061fab243813700006049d649816a5104a84a0000a196c5ef2a3641ad9109000000004815650189e80000225a00000000a18a00008a2425e730b8628a0a32b0325003e1a6013225d101056592e19a81bcc08609cbe01831c00000f07b01d8e0ed000008f5a8fa39c5000000002612818750fe00003a8000000000d44d00000000184c0000c07a0000812848bf0000000060f325610000625be09b0000000061af00000000c22c0000e0bf000094eb71dc4cf00000e41268ce000000009a1f41ab38d2d1402084da2ba18d02800000f1bb656dc81ee23425a0b1b249d1159800009434c240d160f27a0000387729d0a47ba1b81813b177e417220e300e0000407500008cfa9133c8e4a92cb05a000000f260910000501591c5a0b990aeb1e16041000008b90000a145000000002210417e39e70202a40de1d4762cb5ca087b682a000000000000c0b30000f1cf9189c81cd0d30000e6095255555850a9c570f06f809ca0904823904ea1940000002441385a3939210000292660f484ff9a1c3254f516e017311b6515f146725229362004a186f1f4702b8155787d69d7a066747a523c75f000009634000088de80c7514140e5a13d4108a0ac52110000417671f660ce78ef1047315bd222323b34509ceb00008a3a48a42036116381db000029273a06459aa849000054180000000050570000614e0000660c000008ca00000000000038fe1098d030da2ad25d0000810c61ff00000000617b00000000906bc1885074721800000000000000009277c03ba261000000000045d005f432f1f1a0caa0214229807f693995eb24ed0000c1a18e0971f580e74232924b11d310e4f81750fd205df248e13e58e6182830f8f1d13605e01611d700000000058db1e00000d19e8271881de22ec0f04a7e58d9d1f870a4e139816888e7224ed2815013c13555bf08e2a04d202d51030096504cb9e3208f705850eac9bea1acf80e220a8152b8c1f0523088912000cc2269d113f0d86a2620a540d9822b1560a265c441c0ef98e9053df632a082b883e8c3102a7151c0dd01cc6e74726080b4b50231cef5d948fbc18211470474087a124520be99cf98da44f245c3096ab26485c1a16ca54bd18302880000214a0a357118e9ddf12100330928001c72076282c1e4e19df129000088fca2392217e2))
def mo255D11 (j : Nat) : Nat := (if j<1 then 0x586c4c3c2c1c03311030f0893044871513124707c4c3c2c1c02b0d0b07013b10507151447078606c4c3c2c1c02c504f113f0b0700481854a074213c44ec3c1c012060a2c1d0053104f0f0b041848a0b0705c4c3c214c113c012063307003c1c1838618c4c315c10ac0070627130c5708501c18948c4c3c215c114c0070627044f00483c18387c2c114c0131206292063130c4f042b0048189c4c308c2c114062423130f0853044f0048189be52f5ebba2ea2b912deeb6e2d62b3f2ca6b142c02af32b8ead62b0aaab2a56a8029b2a5328f6a2a285a9fd27a69d227029b1268e996260296d255e93e24c291d242e8f0236a8bf22b6892220a871217e84e20da823202e7f21f727c51ec679e1e127711d6e7421c9a7091ba66c81ae26a51a5667e19c2661194e64418c261d18165f017725c516a659615ea567154653c148a50d13ce4d613024a7123e47c117244910d641c103a3f70f863d80f2a3bd0eb639e0e523830dbe35e0d3233b0cb631e0c3a2ff0bbe2e20b322bb0aae29c0a1226d096624008c221f08361fc07b21db072e1c006d21a3065618205ca161051e138048a11303ee0e6033a0b9027e09201fa06d016604a00e2025004e0003ff59153ffd7550fff59543ffd435c7ff54d61ffd43587ff54961ffc80587ff58d51ffd43547ff58951ffd61547ff5d931ffd754c7ff59531ffd744c7ff59131ffd544c7ff20931ffd724c7ff58931ffd524c7ff50931ffd714c7ff58531ffd514c7ff50531ffd87487ff61521ffd75487ff59521ffd83487ff5cd21ffd53487ff50d21ffd71487ff58521ffd51487ff4c521ffd80487ff20121ffd73087ff50c21ffd435c3ff4c570ffd215c3ff08570ffd63543ff50d50ffc82543ff58950ffd32543ff58550ffd31543ff48550ffd60543ff5d530ffd654c3ff5c530ffd614c3ff54530ffd214c3ff08530ffd704c3ff54130ffd87443ff61910ffd76443ff61510ffd75443ff59510ffd83443ff5cd10ffd63443ff54d10ffd43443ff60910ffc82443ff5c910ffd62443ff54910ffd32443ff5c510ffd61443ff54510ffd31443ff48510ffd70443ff58110ffd50443ff4c110ffd20443ff5d810ffd72043ff58810ffd70043ff58010ffd20042ff20173bfd8654fdf55153bfc8054eff61543bfc805c7bf59561bfc80586ff61951f7d52546ff20151bfd864c6ff61531bfd844c7f754d31fdd324c7fd50531bfc804c6ff61521bfd83487fd58521bfc80486ff61421bfd83086ff60021bfd86543df59550f7d53543df54950f7d51542ff61530bfd844c3ef21130fdd434c3f74c530ff9404c2ff61910bfd85442ff60d10bfd82443fd4c510ff521443fe54110ff920442ff61810bfd85042ff60c10bfd820427f61c21b7d85086f760c21bf9800867f61c10afd86042df61410bdd83042fb60810 else (if j<2 then 0x5450221a1515014b130f0934c8742c1c04f28181f0b0453013f10185498718c4c3c14ec0142058561515061c1b130f09005194d1514874586c4c3c2c1c028545219141c1b130f0b054f0148d160841874f65864e202615171100230e570a521e1934d8786408f124d8e1e1d1d1893063c4a38813124746c1c08f8e204c4b07011e3d1a3881c478655c124c48e4394122e1e19030f123a5049349131202c355c1c08ec447142c6c4e18482b0703112e396e50c158647c324c4c18e9412284d1c18490f07023b115450b874724c38ec4c11214244c491f0f07023b10509478643c18ec013c494125582321e060153062142913c9088744818054c188a45f28921d1d0a06011a23053a913cc240847818014c2c1c4884f55a43460221d1e0603130f052962213a90e241485458180150846c4c3c2c188a43c921516120600230d57095306211e91190474681124f4e241d1d1a070f10493950909474286c1c04f4e1c504c491e1b0b0703113d54b8655c1c0514e191f130d3b07005078750c1c0144f182d11570700517c7478641c4c3c224c112248a1d1e1893053c493891c4706554fc4c2c12443122c661d1d3b130c93045048a87868540c4c3c2124d24504c4a19151f130f0b0700b141312864506c4c3c2c155c04734310ca6191f07013d3891b1413120b86c4c2c1c04f4b5b3454311f0f07013b1050915068547c4c3c224c11228321d1d09130700193d38a13471206c4c2c1c04f55144330321d1d0b130f053b0050a87478540c4c324c214c1061230544e1514491c1c1b130f0b070050e87478606c113c0124f4e28511e1b130b053f004d54490cc874706c313c14ec0c412142e1e1a1507130f08489091514068545470786c4c3c2c1c013123c2d1e4f0702490e19389294393c1c0924f864e243c2e53124f0b07012e493e18c4786134f124e183c2d1f0a53113e184d5448b158545c4c394c2138612283e00384c48e04c11514121b10030c38509060bc4c3148e80131c1d3b130e0450487130f122811100b07013b10505480a8606c4c28f13831224331013063b00505484706c3c1c0c40e14202c1b130e384c486084fc4c2171512181d3b130c5c504870786c4c3c241121f10093b0c48505c78606c4c3c212171f130e03085c9060b0a860605c4c3c2801328321f130d3b07005088640c4c3c217121d0f0b07013f105470b0a86070605c4c3c213122c310857113b0f07001c1828b1514c4c3c21707061224242017130f08570453001c18cc404c18ec015141d5513070310390c508c30024c10ec41214211c1f0f07003b1050806c3c1c0c40e141c1c053b130c485c5080706c4c3c241121f130f0820905c4c3c2411215181a07130f08485c800c4c3c21716181e190f0b053f031054907c4c34ec1c0141c1e1807130f08485c80b0a090847 else 0x661d1e1a523b110e085c90b548092508d4f193c211d19110a017a4b110d395234e87868240528e4d8f20645a1c0d05013b12559450b1408874052c2c48f954d2b07013b10545061483c253c1c08fc452152858211d050073123a29566194c52874012c4c3988a8e4d28602b130702392d6e2a60a1847c4c18ec043551426060155469538687818050a5144f1d13055452957c62387470086174f4e2424761d1c02193f13090c5c90b1a8747004ec4c31714242851140311570f08491c5ca2906438147804fa54e246c582204520313093d2d6e94c1506814780c34ec4a514281c061a03130f085c9098747428106804fa54e24591e041a03113f0954510e94c874781c4c34e80a514261d1c045312030f08185c90b87434286c1c04f4e221f130d3b07005078750c1c0144f1913070054517c6151486454140c4c3c2652888581d0619013d953891916074140c4c34e651428))
def mo255H11 (j : Nat) : Nat := (if j<3 then (if j<1 then 0x120000a4365ade60a60001c10bb54c0001633c000000000000b18c000000000001e17a0000000000000194e1260000c566000000000000000000009d160000ecc663dc0000b23a00000001338e00000000000000000000823c000000000001855b601e0000000024d0000000000000ab9a0001f4c1711fcc046d02000001b200000000c106000041a3839733be00000000a5380001421fa2f00000e326000021880000dd422bdde0200000000000000000000000000000000134fd609e40a00000000000000000000000000000d0a8297a000129260000a3f40000000000000000000000000000000000006140828e0000000182aa000000016af000000000000000000000000121dbcd5a0000ab96000000000000000000000000027600000001a09305740000000000000000000000001431421a6024254a00000001a1840000a4fa0000000000000000000160740000408991680000c242000000000000c568651a00016942410e000000000000000000010c38000124b60000000000006190ebf4c39c00000001e14b116782a604e689e000018931ed4a247ed236000122de00000000000000000000d20800000000000000000000000000000000627c000000013351e49e0000000000000000000024cd2076000000000000000000000000000000000000000000000001a94a000000000000c22e00000000000000000000000000000001eb9c00000000000144d32c8320ae00000000c886000163c40000217c43d80000000000000000822004e20000000000000000000194f62c91a542d4a800000001000400010c9e0001e3ae0000000000000000625173e6000000000000000183600000000051580000a10800000001a28400000000000000000001d3480000d2a8000022b0a48d0573a3da000000000000738000000000000043de0000c342000001c0000000000000000000000000d11c000000017d40000000000000000000000000697dec2b60a20000000000000001a1fdf4b600010bae0000e1de0000e525808a000140d9c028000012380000ebce0000000000000001824e00000000000144e800000000000000000000000000000001f139a0800001e3ea0001e56e00000000000154e40000000000000001525e00000000000065080080231800000400100001002010c000800321400000810880300021000200880118920200031880108c4030020088002884429400224060000100824294430982300407000422804c008200858000021110030186208000000210004428c671846100c8b39027000600000220007000000004000c0108400000611800101020008000804041281014410004c0002720c6110c0008c05004021082000c430000100006005012000408460000430022200c200080110041100c61882a00021008c0 else (if j<2 then 0xc4e0000000000000000e01400006c8a0000824101e991541006b4db017154c4e90823a90002000000010c6311e1a4be00008c100000c3a4415c000043980001eba1922f82d600008534000035420001547c000000000001b1f800000000000000000000000000016a4a8224000000000000a558000109f80000d4e2000000014044000000000000000153220000000000000000000000000000000000000000000000560000c22d4ba800014ad60001211aa42feba442d000014970a0720000d2aa908c000124c36b9841e400000000000000000001219e0000000182c6f4bb22e28528e1b405360236e0bc021c93740000000161dc000000000000000061bee1c4024c0000e1ae00000000000000000000000000000000c04c000000000000000000001243229e0001ea2c0000ecc3c21400000000000000000000000042a8000000000000c2920001cd374ac600000000000000000000000082f4000000000000e0b954e60000000000012a37eb380001fd600001b3900000000038e5a9a8000000000000052c00000000000004680000000000000000000000000001823874bee507650e00000000000054f00000000000000000ea1400000000000000000000000000008116000044aa000000012a6400000000000144e08054d2cc037dca9bd530c4e400000001cd2c0000000000000000000105500001800800000000739400000000000000010318000183c622c2645000000000000000000000000000000000000000000001a3b0000000000000000023246c87f4c360be00000000000000000000236600000000000000000000b23400016caaf38a844f91fbe37e00000000000000000000000000000000d075b0884376000155320001c452000000000000000114980000000064260000c18e000000000000a52381fe00000000000000000000000000016244000000000000000000000000000000000001011e00018a76000000014b666a74449db2d8e083c5640000000063f3c830000000000000000083bcb1840001b34eac8492320000000000000001e226000000000000000000000000000000016403b1f40000a1ea0001819b4c5e0000d27600000000a9ff33bc000040180000e336a27ac18242943181515c000000000000232e000000000000c4f00000000000000001623022ac0001b3df6c9c0000000161c600000000000000000000000132ea353a00000001c55d4152687c0000abf200000001acba00014b50000000000000000000000000000000012c649d18e3d400000001e47c0000000160d00000a4c6000000000000000048376248000000000000000000000000329fc0991247433a000000000000b4f9cc1a13fbe9bc000090afc3bfb0e80001839be01200000000000000000000a4ea00000000000000013295e5 else 0xd2d7344800000158124b4a43020dd5340001831753360000aca9e4b00000000000000000000000011522000000000001c2a2000000000001656154ec0000000000000000ac26c0da00000000000000000000000000000000000008560000a2160000a2340000000000008a0668f928c00001a2d48d4449bb713d453163faf199d0ef4c8e8cf6037000000000d2600000000103acc2b20001c4ff0cb0737242cce425405b343e820e80b6000000000000000000014a2f41fb553600000000000000000000000000000000000104960000e111433e000140780000000000000000f40a00000000000000000001f296000000000000000000000000b0cd735e8ab20000000000000acc00000000000000000000249a0000cd0000002bac0000000190e4206703b760c20000000142bc000000014504c53244727370814fe41669fa10dde25703060000000000000001a254a32c00002c9600000000e04e00000000623e00000000000083720000000102e600000000a4304bd701ce826400000000c0c78199e4ae000000000000000000000000000000014c9a00000000323100070d04000000008d320000000000000000000000000000000000000000e30f400c000000000000000000000000000000018abde3fe000000000000728e0000e26e0000000000018a3f8290c2ce0000000000000000000000000000d2700001284e0000d52a000000010cae00000000000000000000000000016828000120f24071207c00000000000000010096000000000001436e0000000000000000c02f808c000044120000000000000000f2560001800e000000000000e30a00012046000000000001cad001a40001723e0000000000000001c274000123c3c124a1bcc07eb24524b20001e8e842d200000000000000000001c3c0000144ac0000000004844841236da0ca22ee00000000000000011252000002120001c9440001b2cf61a6a45f403200008c4361d6c1ba628c50f983ee0000439e00000001243243f8000000000001a12e01b1818ab3ba00000ad20328b1c36346a1f662c00000c3e793d3d266223a000000004cb200000001eaeed3780001250200000001403444d86cada2ca0000000000000000c8ca8192a350a99000000001d0d00000000000000000000000000000a5482393211c000023115966000132d2000000016b9e000000000000000000000000000145000000000000000000000000000001cbefc9f6000000000000000002220000d25a031c00000001044c0001350bd42a000000000000000193d1c039b2de6d490c4a0000000000004474000000000001a114c3a0000000007d6b73479190000000000000000052a60001841c0000a563000a0000000000000000000000000001dcf60001e1f80000508200000000e0ec14e8000000)) else (if j<5 then (if j<4 then 0xdc0000f3ca000000000000252e00000000044400000000000000000000000000000000000069940000000000014404b136a43c313a000000004969b19400000000435ca555297e0000000181ca0000837400000001e47600000000000061f5f43400000000000000008ca20a38000100ac000000000000000000000000000000000001b0aa000000000000000000000000b34c000000008bf8000154940000000000000000000000000001a3120000000000000001a2e400000000006a00000000000089cc00000000f356000181026c6000000000000113760000b4a520a4000000000000000100aa612c00000000205e0000a478e2fc152470d8c3ba0000000000000000000189da00000000000124460000000000000001620000000000000023e9a3d7b2c800008438000000000001041e000000000000000000000000000000000000000001e0000101300001625e000000000000208e0000000000000000b24e0001a211d35800000000000000000000612860260000a176846b43b80001b0500000000000000000000171002315cc1c000000000000e2f8a40c000000000000000054240000000000000000352e000000000000000000000001301600000000a4089215dd1dc06320230364fcda00000001f3420000000000000000d31c0000000000000000000000000000922c000000000000000000000001403ba4910cc000000000000160ea000000018420a1e3a30d43e4e02a0000000000000001fd1ae9760000000001320001c3540000240600000000e362114db8e8000191dc0000411800000000e862a26a01860000000000000000a03e0001e5760001e81914aba15e0001d368ec2f2144000000000001ea480001c516e42840860000000022b5a13a22fe0001c0430c8d68720bdb8422626961adc39460bb040ac3aba0d40000000000000000000000015328208400000000000050d3ed2a0000000000000000000083e20000000000017d58000121aa000000000000000000000000000149dfa27800000000000000000000000000000000000000000000922a00000000000000019325a3320000000000000000000000000000000000000001ebab851c000101cceb940000a50c00000001643b74372a8852c755280001c167b42041d8000000000000c3220000822a00018208000000000000c15ad3cc45190341049800000001621800000000000000000000205c0001533c0000000000000000e0c00001e1e7c2a4000092c200000001e0cc0000a8bb84a800000000887fc07a8466d2ae0000c0de00000000000000000001fd63d1ca00000000000083b20001610c91186204000064d72010a1c8000000002c98d52df25589496488f1a444f7713fb41f6206096740f8000000000000000000000000000000000000000141b800 else 0x6a00000001c252000000000001806e0000000041f00000000000000001cca00000000000014ca40000000000012c29697503fd3338938c00000000000000000000251fcc2280374c0a2345606d61c2000050f00000e8f6000000000000000000000000000000000000312122ba0000231a000000000000000000000000e946a33800000000ad1e00000000000000000000000062dc000000000000000000000001c4f2841841ec00000001db24000000012280000152060001737a0001a13e00000000000023020000000000000000000000006348000000000000d1340000000000000001a20a000000000001e50a00000001c9dd842a83ced3820000a2e8000000000000000000000001122600000000f0a6ed4000000001119a000000000000000000010150816400000000dac20000000121a8d3d80000c0b1f3c48401a13600000001212a000000000001a2fa000000000000000000000000000000000000000000000000000000000000ca0a000000000000000000000000000000000000000184b4000000000000f3d600000000000000000000000000000000000000012547532e036a42be000191ee000064c009d00000504bc4ce920ac49364dae01653340000000000010282b9ba8161e391e2880000c965c29a0000000000015d2200000000000055216471e48600000000000000000000000000000000e465646c000000016458000000000000000000000000000000000000000000000000000000000000000000012b6a00000001828a00000001c43473f874bc452001380000000120680000000000000000000164c9601b2c25d35363f6000089be8d1ce0c800000001acda0001452a000000013d000202c9600000b55a2c5200000000e4dc00000000000000000001e3a20001fd660000e515298e000190da0000c19c0000000072240000491200000000000000000000c25a00000000fd6c0000000000000001c16a00000000000000000000000000000000c2670197306200000000000082600001a25c000000000001c42c00000000055ec1a10d06d2f1d539abf60000000000000000000045700000026c00010ba20000e4800000f412000064de000000000001c4ca0000849400000000000000012982429c0000000148e764a60000000000000001014c72220000000033ab22b744c528c800000001830400018050000025520000000143780000096ba2c800000000000000000000ba3410de2cde000105440169441a000000000000a27fa34c000000000001554a00000000741ce17e000000000000000190b1a38bac9400000000000080f000000000000000000000000000008ca60000000000001330c4ee82f72541c27160ef70d5245441d2b568000164a20000000000000001fd1e656d456a8c13a5100000000000e180) else (if j<6 then 0xa2964c4000012c3600000000000184820001416cd18600000000000000000000fd5a00000000d14a0000c48e000043f0000000000000000048040000000063e1326a0000000000000001a2328bec82e18d4fe0900000000000000000000101eeaba794ee0000000000000001c448000000006000e4b80000000000000000e84a00000000350e000141800000031e0c2d4229c4fc000043cb453fd132000000000000e272000000018a18000000000000000000000001434b896c4a6c0000000000000000000000000000000000000cca0001247a8bf00000c88a0000000141d4000000000001440e0001c45ac82382ae00000001c16e0000000000000000000000000001b1060000b272000000018b2000000000000000000000000000000000000000000000000091cc0000000053e28121c4f80000000033b000000000000000000000f23c000000013104000000000000c24a0000b36761d1c34f217800000000cc5c000000000000d0f20000000011bbe99944bbc17302980000f355416242f29188fd69e1574330000004ec0000000035180000096f03520000000100640000000000000000000000000000000000000000835e2388000000000001c2da000000000001e2580000000000000000c09a000120ce00e60001e0520001c134c2d8000000000001b4b800000000f427f3ce000000000000000000016b5b69780000000000000001d122b14600000000000095000001f44034a20972000192c0c1018962286420e560c4000114fa0000000035160000000000000000000160e80000000000000001a11210ed126c000100d6d1440000c4416888000069a400000001a1b600000000e1f2000000000000044294ce00000000000042eb453a0000c2c5a3d00000000000000001313000000000a0600000000000000000000000005d2400000000b0feb8d8000173d400000000000000000000000000018a0c0001c9d6000000000000000000000000000180fc69b0000000014c1e00000001e98a000123680aea0001aa5e40a8000020fa000000013221e09413a0000000000000000000000000b4a68334000000000000927c0001c860a556f2b40000c54c0000805800000000000000016bd80000000000000000a37a000014d000000001ad5ef3dc23d20001a0d34a8a000082860000844aa8fc000183840000003000000000000043c823b4000000000001246148fb44d5d4ca00000000000000000000000104148d4d21740000000024a504f4a4a1202c00000000139e00000000804800000000000000000000000000000000000009140001750c0001cc21e48a0001445c6a99c0f6000000000000000000000001213ce3208462000032740411a30142a0e356000000018381246e000023cc00007b380000ea else 0x111ec000000000000000000000000000000000000f2b1e0b40001403c0000a9fc0001ec038c5064bcc1220001a146000073600000804000000000a9d8d384f048000000000000000025790d24000168d80000000000000000000060ff42ec453c235940f40000d39c00000000a0e20001438ff11a00000000000000000ccfc1420000000000000bebe0b2000000010149a09c00000001443e984a00000001514000000000238c00000001a15400009d200000000122b9a2462308c387a26243820000000043ed0aec0000000000000000000000000001a457129c00014526000188ffea01a8e5a01dcc886104000191f0a04a0000000183a7418c4939c54fb1c40000032ba35a0000000000)))
def mo255D12 (j : Nat) : Nat := 0x520c0203c52a10a41807c60e180801e9470e1c301890cc941c9490a00944870868e1c106830070f1c38685060441e5480f121c18038518203860a0404487092921c286890e14180405890e11582520070c5070d0600f1c3070d0e0c08838a101c305020224385044242c3850d121c2830080b121c229049c02418aec380d2704b36969621a7559752d1b3748a13000ffaebff597feb9ffd53ffa87ff5c7feb0ffd51ffa63ff487fe10ffd70ffaa1ff4c3fe887fc10
def mo255H12 (j : Nat) : Nat := 0x52a7027707ae0961290046071cbd8484a2bfc2cb22285e0012c7b01ac134630eaf5896906d4a4e0960000001a021064644083bc25000090f000003628eb485589bab3f8d1b34688cc2f90dcc3fd91e5ba24ebb3ed821c2b6906aa8f0df24beca40000000d3b44b4000000000000000005476000305102058c4f0e0000a1c9c1f309123a00042d7bbcc302638000000000012498001806480a84600535c580000000001d11000000058b400000ba000644c0007abc000000000000000003028000000081e222e0002448000000141a34c1a1f78fc629c0f780c904422881300000000c8808020006890e41000133390860000000000683000064640000001846eadc8358001d1a4cf32228001832d0da0006912d4321002122c5a607430750a247cb35585c31ca8ee23a192a000181e42c949704c80008add834a118000a27ec812ae7ac0000000103520a80007058000390ee0b247400038e3935e0f9a0f8000000000144b7a5982868f00001041c05ff0c248388fe89532442c0000b317b18abcbb12c458000000000060bd0764031d2f22164bc83ca038d43a81baa85013d2fdcdd82ada4b71780016cb32c3831800000068bc60de2e800078ec332720cf21a28b4330001a089304000000083e9498ec68001820800022222e3d2488f40000000e16ca3400044349b7084fd15ff0f2af800000072c40001814e2600016a020c8eb28001f3bed19a1b800108080015278000000280fe42d909a434000c4904fdcad311d2291abbf03800132a08756180063c40e8060000cae0000ca361515320001092b472316142b460609826f348b115c19e8c0a33800123910b7a34b8b8000000174a8000dc6604dc1f80000006494a1280000001842000082ad1e512200032a520f7714149024353a0001bc7470a0006856039bc0004b8d1c041800b0c290484c1902a4c01d0eb40161070182002098c0e002070200980222009f080800502280010c0830602040011c001810004086
def mo255D13 (j : Nat) : Nat := 0x103081005ff
def mo255H13 (j : Nat) : Nat := 0x12e8006270c00001f500000492278002bd0f40800960c1e40000012497e0a90f4600687742ee9389c00000003380000066ed35e000003940000000384e60000009600045228c00
def mo255L : Nat → Packing
  | 5 => (1,8,6,0,0,0,0,mo255D5)
  | 6 => (1,7,6,0,0,0,0,mo255D6)
  | 7 => (12,6,6,0,0,7,0,mo255D7)
  | 8 => (134,5,6,0,0,11,0,mo255D8)
  | 9 => (658,4,6,0,0,14,0,mo255D9)
  | 10 => (701,3,6,0,0,16,0,mo255D10)
  | 11 => (155,2,6,0,0,14,0,mo255D11)
  | 12 => (16,1,6,0,0,10,0,mo255D12)
  | 13 => (1,0,6,0,0,0,0,mo255D13)
  | _ => emptyPacking
def mo255I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 mo255H6
  | 7 => lookupWord 1 5 0 5 0 1 mo255H7
  | 8 => lookupWord 4 29 4 10 4 2 mo255H8
  | 9 => lookupWord 56 563 4 14 8 2 mo255H9
  | 10 => lookupWord 269 1327 8 16 10 2 mo255H10
  | 11 => lookupWord 309 3109 5 16 10 2 mo255H11
  | 12 => lookupWord 69 379 7 14 8 2 mo255H12
  | 13 => lookupWord 7 53 5 10 4 2 mo255H13
  | _ => fun _ => none
def mo255 : Forest := ⟨1279,13,fun i => mo255Y[i]?.getD (0,0),mo255C,mo255A,mo255L,mo255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P5_0 : CutRow mo255 5 0 1 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x73791240) rfl (by decide +kernel)
theorem mo255B5 : CutRow mo255 5 0 1 := mo255P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P6_0 : CutRow mo255 6 0 1 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x73791260) rfl (by decide +kernel)
theorem mo255B6 : CutRow mo255 6 0 1 := mo255P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P7_0 : CutRow mo255 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P7_1 : CutRow mo255 7 1 11 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x73791210737562107379121057971270737912107379126084a1952065ab4410481a95615278001073791220) rfl (by decide +kernel)
theorem mo255B7 : CutRow mo255 7 0 12 := (@joinRow mo255 7 0 1 11 mo255P7_0 mo255P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_0 : CutRow mo255 8 0 8 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_8 : CutRow mo255 8 8 96 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x7379123073791230737912607379126073791260737912607379126073791260737912607379a22073791220737912207379a220737912707379127073791210737912207379127073791270737912707379b21073791280737912107379128080a67520527a0010737912807379128084a1953065ab441073791280481a957262795070527800105278001025870080758450507584006075840050758400605748506575870060527a001073483220537a101073483230527a001073793220527a5010527a5010727a2320727b2330727a2320727b0330727a2330537a1080534a1080534a108073783210727b2320737912207378307073783210737832805767035157670352378732617575128557b703625797125067873260678732604797b2805797125067873260527a506567a7236157b7035165ab5065527a506557971250678732605797125057941250678432603797125057b70351737912103787a26157971251757912854787a26057971250579712617379122073791220) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_104 : CutRow mo255 8 104 30 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x627b2120627b2120527a0010627b2180634b3170727b0330634b3170727b032073791230534a6080634b3120634b318084a1b54165ab442184a1954065ab5410481ab573534a6060481a9573627b506073756210627b5060727b0320627b5060634b3120717b038073791210737912307379123073791230) rfl (by decide +kernel)
theorem mo255B8 : CutRow mo255 8 0 134 := (@joinRow mo255 8 0 8 126 mo255P8_0 (@joinRow mo255 8 8 96 30 mo255P8_8 mo255P8_104))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_0 : CutRow mo255 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_1 : CutRow mo255 9 1 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_97 : CutRow mo255 9 97 66 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_163 : CutRow mo255 9 163 96 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x80a4755180a4755180a47591866b0976096b768494b386403797b29225a7507080a5754025a7507037873282379412723784328237971272084a758357b7036227a7237257b7036227a7237257b7036257b703625717036257b7036257b7036257b7036257b7036257b7036227b7037357b7036227a7237227a7237257b70362579712615797126157971261378732715797126157971261570712615797126157b7036257971261378732713787a27157941261084a7583378732715797126157b70362527a0010427a90105273001073783230493b8674484a7583481a9563484a7583481a9563494b7684484a7583484a7583329b4721484a7583484a7583084a7583094b7684579712613787a271427a9010484a75932617517157071261494b7694084a7593737912307375322073753230737912307379123073791230627b2120737912807379128073791280737912207379122073791220737912207379122073791230737912907379122073791230737912907379122037971282) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_259 : CutRow mo255 9 259 96 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x727a2330727b2330727a2330727a2330727a2320727a2330727a2330727a2330727a2330727a2330727a2340727a2340627b2110727a233073783220737832207379322073783220737832207378322073783220527a5070727a2330727a2330727a2330727a2330527a5070737832207378322073783220734832207378322073483220737832107378321073783210727a23207378321073483210096b76747378322073783210727a2330727a2320737832107378322073783210527a001073793230727b2340524a0010727b2340524a5070727a23307378a23073783230737832907378a2307378a2207378a2305273501073783230737532307378322073723210737832303787327136176171378732723787328226175171378732823787327227a7238327a7237257170362576703625614516037873271575712613787327157670362378732713784327194b386405757126157670362329b4732329b474373783220570712615757126137273272372732723727327180a47541) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_355 : CutRow mo255 9 355 96 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x80a6759180a675406279212094b68662258450702584008025840070258400805248508725870080527a501073783220527a501073783220527a50107378323073483230517a00107348323073483230727a233080a47541527a0010527a0010527a0010527a0010527a0010517a0010517a0010417a001073783230527a00107378323073783230737832807378328073783280527a0010737832307378323073783230537a10107378a23073483230727a234080a4755180a4755180a47591527a0010527a0010527a0010527a0010527a5010527a0010527a0010527a501073793230727b2340737832307378323073783230737832307379323073493230866b09767379323073793230537a1010537a1010537a1010727a2340727b2340727a2340537a6010537a1010727a2340537a1010537a1010537a1010537a1010537a1010537a1010727b2340537a10107378323073783290727b2340524a501073783230534a6010737832207378323073783290534a1010727a2320727a2330) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_451 : CutRow mo255 9 451 96 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x7379122073791220727b23307379129073791210737912107379129073793230737912907379a230737912307379129080a6754080a6754035a7107080a675404278901080a67551727b8340427b8120727b8340727b8340727b834065ab5421727b8340727b83407379a2307379a29080a6759180a6754080a6754062415120527a0010707b2340527a0010627b2120624b5120627b212062715120524a5010727b0340627b5120727b0340627b5120624b512073791230727b03407379123073791230727b0340727b03407349323094b6866273791230707b2340727b0340737912207379123073751230737512907375623073753230524a5010524850105248501052785010524a00105248001052480010524a0010524800105248001062492120527a001073791230524a001073791230524a00105248001084a1954165ab542152480010524a507073791220524a507052485070481a9583524850706248507062492120480a9593527a0010527800105278001080a6754065ab4421) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_547 : CutRow mo255 9 547 96 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x627b2120627b2110524a0010627b2120514a0010737912307379123073791230527a0010527a001062795120527a0010527a0010527a0010527a0010527a0010527a0010427a9010624b2120637b3120524a5010524a0010624b2110727b0340727b0340727b0340727b0340727b0340727b0340727b0340727b0340727b0340727b0340727b0340727b0340634b3120727b03407379123084a1b55165ab44217379a23073793230737932307378323073791230524a001073493230514a00107349323084a1955165ab542173791220481a9574481ab58473793220534a6070481a9584727b2320624a5060624b212073793230481a9584624b2110634b3120717b0330527a0010527a0010727b23307379321073791230737912307379123073791230737912307379123073791230737912307379323073791280737912807379128073791280727b2340727b2340737912807379128073791280737912807379a2207379122073791220737912207379a230737912307379129073791290) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_643 : CutRow mo255 9 643 15 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x627b2120627b2120527a0010524a0010627b2120624b2120627b212052485010534a6010527a501073756230527a5010527a50107379123073791230) rfl (by decide +kernel)
theorem mo255B9 : CutRow mo255 9 0 658 := (@joinRow mo255 9 0 259 399 (@joinRow mo255 9 0 97 162 (@joinRow mo255 9 0 1 96 mo255P9_0 mo255P9_1) (@joinRow mo255 9 97 66 96 mo255P9_97 mo255P9_163)) (@joinRow mo255 9 259 192 207 (@joinRow mo255 9 259 96 96 mo255P9_259 mo255P9_355) (@joinRow mo255 9 451 96 111 mo255P9_451 (@joinRow mo255 9 547 96 15 mo255P9_547 mo255P9_643))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_0 : CutRow mo255 10 0 11 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_11 : CutRow mo255 10 11 73 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_84 : CutRow mo255 10 84 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_180 : CutRow mo255 10 180 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_276 : CutRow mo255 10 276 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_372 : CutRow mo255 10 372 63 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_435 : CutRow mo255 10 435 5 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_440 : CutRow mo255 10 440 96 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x727a2340727a2340727a2340727a2340727a2340727a2340727a2340727a2340727a2340727a23407378323091b676627378323073783230727a234073783230956b287573783230727a23407378323073783230737832307348323094b68662737832307378323073783230727a2340727a2340727a2340727a2340727a2340727a2340727a2340727a2340737832307378323073783230737832307378323073783230727a2340737832307378a2307348323094b386627378323073783230727a234073783230737832307378a2307378a2307378a2307372323073723230737232307372323073723230329b474391b47662329b4743329b4743329b474380a4755180a4755180a4755180a4755180a4755180a4755180a4755180a4755180a47551866b097691b67662956b287594b6866294b3866280a4755180a4755191b4766280a4755180a47551329b474380a4755191b47662329b474391b47662329b474380a4755191b476627379123073791230737912307379123073791230) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_536 : CutRow mo255 10 536 96 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x7379123073791230737912307379123073791230737912307379123073791230727b834084a19551727b83407379a2307379a23080a6755165ab442162415120727603406271512072760340627151206241512073751230727603407345623094b38662737512307276034073701230737512307375623052485010524800105248501084a1955184a1955184a1955194b38662956b287594b3866284a1955184a1955180a6755165ab4421624051206270512094b386627378323073783230737832307378323073783230737832307378323073483230727a234080a4755180a4755180a4755180a4755180a4755173783230737832307378323073783230737832307378323073783230737832307378323073783230737832307378a23073483230727a234080a47551737832307378323073783230737832307378a230727a234080a475517378323080a47551737832307378323073783230727a234080a4755173783230737832307378323073483230866b09767378323073783230) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_632 : CutRow mo255 10 632 69 := mixedCut (pos:=464983315956381412732701187) (neg:=93987222814732544234310106376236) (data:=fun _ => 0x524a5010627b2120524a0010524a5010627b2120627b2120624b2120624b5120624b512084a59551627b212094b6a662956b2875627b2120627b2120624b212094b6a662627b2120427b8120624b212073793230727b2340727b2340727b2340727b234084a195517379a23073491230734912307349123084a1955184a1955184a19551727b234094b38662727b2340956b287573793230727b23407349323094b3866273793230727b2340727b2340727b234084a09551727b8340724b2340727b2340727b234084a0955173793230737932307379323073793230737932307379323073793230727b23407379a2307349123084a19551737932307379323073793230727b2340737912307379123073791230) rfl (by decide +kernel)
theorem mo255B10 : CutRow mo255 10 0 701 := (@joinRow mo255 10 0 372 329 (@joinRow mo255 10 0 84 288 (@joinRow mo255 10 0 11 73 mo255P10_0 mo255P10_11) (@joinRow mo255 10 84 96 192 mo255P10_84 (@joinRow mo255 10 180 96 96 mo255P10_180 mo255P10_276))) (@joinRow mo255 10 372 68 261 (@joinRow mo255 10 372 63 5 mo255P10_372 mo255P10_435) (@joinRow mo255 10 440 96 165 mo255P10_440 (@joinRow mo255 10 536 96 69 mo255P10_536 mo255P10_632))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_0 : CutRow mo255 11 0 9 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_9 : CutRow mo255 11 9 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_57 : CutRow mo255 11 57 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_153 : CutRow mo255 11 153 2 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B11 : CutRow mo255 11 0 155 := (@joinRow mo255 11 0 57 98 (@joinRow mo255 11 0 9 48 mo255P11_0 mo255P11_9) (@joinRow mo255 11 57 96 2 mo255P11_57 mo255P11_153))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P12_0 : CutRow mo255 12 0 16 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B12 : CutRow mo255 12 0 16 := mo255P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P13_0 : CutRow mo255 13 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B13 : CutRow mo255 13 0 1 := mo255P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255T : mixedTables mo255 13 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo255 0 0)
  · exact (mixedEmpty mo255 1 0)
  · exact (mixedEmpty mo255 2 0)
  · exact (mixedEmpty mo255 3 0)
  · exact (mixedEmpty mo255 4 0)
  · exact mo255B5
  · exact mo255B6
  · exact mo255B7
  · exact mo255B8
  · exact mo255B9
  · exact mo255B10
  · exact mo255B11
  · exact mo255B12
  · exact mo255B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255G : graphValid mo255 (boundsBefore K254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255R : Impossible false graph 13 eightInputs.toFinset := by
  rw [show graph = targetOf mo255 by decide +kernel]
  exact mixedRoot (g:=mo255) (top:=13) (i:=0) (before_sound K254 (known_down V254)) mo255G mo255T (by decide) (by decide +kernel)

end Foundation

theorem Foundation.lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4) || (x 5 && x 7) || (x 6 && x 7)) t → 14 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact PEqualNP.Outside.L_meta_10446.Foundation.directSplit PEqualNP.Outside.L_meta_10446.Foundation.mo255R PEqualNP.Outside.L_meta_10446.Foundation.g255R ⟨C,hf,by omega,heq⟩

namespace Transfer
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds


-- Circuit input relabeling from L-meta-927.
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this



def identify (i : Fin 9) : Fin 8 := match i.val with
  | 0 => 1
  | 1 => 4
  | 2 => 7
  | 3 => 3
  | 4 => 2
  | 5 => 3
  | 6 => 5
  | 7 => 6
  | _ => 0
def large := fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8)
def small := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4) || (x 5 && x 7) || (x 6 && x 7)
theorem image : (fun x : Fin 8 → Bool => large (x ∘ identify)) = small := by decide +kernel
end Transfer
end PEqualNP.Outside.L_meta_10446

theorem PEqualNP.Outside.L_meta_10446 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8)) t → 14 ≤ t := by
  intro t ht
  have reduced := PEqualNP.Outside.L_meta_10446.Transfer.relabel_size PEqualNP.Outside.L_meta_10446.Transfer.identify PEqualNP.Outside.L_meta_10446.Transfer.large t ht
  rw [PEqualNP.Outside.L_meta_10446.Transfer.image] at reduced
  exact PEqualNP.Outside.L_meta_10446.Foundation.lower t reduced
