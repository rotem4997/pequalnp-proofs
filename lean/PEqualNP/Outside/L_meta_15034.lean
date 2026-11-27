import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_15034.Model
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
theorem getRep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
        exact Or.inl (getRep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (getRep w i) (getRep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (getRep w i)

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

theorem extractPlan {u target} (gs : List Gate) (w : List Sig)
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

theorem bRead (i) (w : List Sig) (j : Nat) :
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
  simp only [bRead]
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

theorem exeBits (gs : List Gate) (i) (w : List Sig)
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
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
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

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
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
  let n := v.toNat % 2305843009213693951
  ((n*n % 2305843009213693951)*(n+7)+971*n) % 2305843009213693951
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

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


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


end PEqualNP.Outside.L_meta_15034.Model

namespace PEqualNP.Outside.L_meta_15034
open PEqualNP.Outside.L_meta_15034.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def SBf (j : Nat) : Nat := [7, 7, 6, 8, 7, 7].getD j 0

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d (SBf j) k cs.length pool ws)

def mirrorSteps : List Move := []

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 2 == 1 && autoOK (target g) mirrorSteps then ws.map (movedWord mirrorSteps.reverse) else ws

theorem variant_ok {g k ws} (h : Impossible true (target g) k (List.toFinset ws)) (code : Nat) :
    Impossible true (target g) k (variant g code ws).toFinset := by
  unfold variant
  split
  next e =>
    simp only [Bool.and_eq_true] at e
    exact rotate_excluded h _ e.2
  next => exact h

def links (g : Atlas) (k tag : Nat) : List (List Sig) :=
  let code := locate g k tag
  let row := code / 2
  if row < count g k then [variant g code (vals g k row)] else []

def checkRow (g : Atlas) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  let h := tip g k i
  decide vs.Nodup && !vs.contains (target g) &&
    (if h != 0 then deadTest (roots g) vs k h else
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) (SBf (min ((tip g k i % 8)-1) 5))

theorem checked {g : Atlas} {r s} (ready : Ready g r s) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkRow g l i = true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    have h := good k (by omega) i hi
    simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at h
    by_cases hn : tip g k i = 0
    · simp only [hn,bne_self_eq_false, Bool.false_eq_true,ite_false] at h
      by_cases hk : k=0
      · subst k
        intro n cap run
        have : n=0 := by omega
        subst n
        have hm : target g ∈ (vals g 0 i).toFinset := run.1 ▸ Finset.mem_singleton_self _
        exact h.1.2 (List.mem_toFinset.mp hm)
      apply node_sound (raw:=roots g) ready.1 _ h.1.1 h.1.2 _ _ h.2
      · intro a ha
        exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
      · simp
      · intro tag xs hx
        simp only [links] at hx
        split at hx
        next le =>
          obtain rfl := List.mem_singleton.mp hx
          exact variant_ok (ih (k-1) (by omega) (fun l hl => good l (by omega)) _ le) _
        next => simp at hx
    · simp only [bne_iff_ne.mpr hn, ite_true] at h
      have test := h.2
      simp only [deadTest,Option.any_eq_true] at test
      obtain ⟨bank,he,hc⟩ := test
      exact poolCut_sound (ready.2.2 k i hi hn) _ he h.1.1 hc

def segment (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && segment test start n

theorem segmentRange {test start n} (h : segment test start n=true) (i : Nat)
    (lo : start ≤ i) (hi : i<start+n) : test i=true := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_of_ge lo hi)
  | succ n ih =>
    simp only [segment,Bool.and_eq_true] at h
    by_cases eq : i=start+n
    · exact eq.symm ▸ h.1
    · exact ih h.2 (lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq)

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_15034

namespace PEqualNP.Outside.L_meta_15034
open PEqualNP.Outside.L_meta_15034.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x2156800080078680008800e542881226006260610d1c3e900002e6c0192a2400050a40800e151824a00c0b28013910074b0f0c0401800d92c40c90cd441ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20ee20fd20fc20ec20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xbc74012d2509440008840000fd5000ad40ed355c2d007114e800000158a88ccce0005c00c110001148000000013890d400013c0094b400213088f8785460595400c40000f06400d828240118004c98a4b90c0000dc0014001c00000000396030a0007c01643440014c6800f5040000b0000000000000000000d00000e51c18486d200c4400816800c89d28003c000450000a040c040a2a0200040400040e0000000200020204080400020200100b9d4310edca421db54843bb28887755110ef4a021de54043bd286857950d0af4a1995e54332b7294836d52906bea6a0d714d41af298835d53106dca420db54841bd280837950106dca518db54a319faa2633c544c67ca818cf55031b7290636d520c6f4a018de54031b7286436d52886f6a090de14121f3a8a43eb50486d8a090fa14121b4282436e52086dca5a05b54b40af29c815d53902dea4a05b14940b7296616d52cc27ca9184f55230b7a92616c524c2daa3105b942209f2a0413d54082bca6105754c20bb2884175510835ca8106b55020e729841cd53083cca2105b54420f2a88416551082dca0107a94020f520041e940083d460107a4c020b7296216d52c43ca43887a08310b7a94216c52842dea4885b14910f290a213e540427aa8085794c10aea98216e52042daa4087a08010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1a788030aac09602430018a61c500412a2e826380022101c058800ab1543544439a18152906686054a31ca99050487296414121d298c50487496314121c355153083265454420c955151083465354420d154d51083606054420b258e40083615190020d854540082a9648c020d85463008361514c020b818121c42e161083109919521442696508010ca55020043495308010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x10400c00008001825916314121a42e8302a210541731815108320b1aa32004188591518c020
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | 2 => packedAt s0K2 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (788+((h/14+packedAt s0K5 (704+(h % 14)*6) 6) % 58)*7) 7
  | 4 => packedAt s0K4 (2697+((h/30+packedAt s0K4 (2457+(h % 30)*8) 8) % 146)*8) 8
  | 3 => packedAt s0K3 (990+((h/8+packedAt s0K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s0K2 (249+((h/1+packedAt s0K2 (245+(h % 1)*4) 4) % 12)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x38f1fe3c7f8ffe3c63838fc38fc3ffe61c39f
  | 2 => 0xfc0fe1fff87ff8fc07c03f1fff1ff81e067cf3
  | 3 => 0xffe03ff80ff1ff8003fe03fe03fe1878f1c
  | 4 => 0xfff00003ffff001fffffc0003fffc001f80fe0
  | 5 => 0xfffffffc0000001fffffffffc0000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x5011888452415001460a902510250a9860c185
  | 2 => 0x8220440811001040040090889089044021432
  | 3 => 0xab4455492532a03e88052a42aa42a545870e18
  | 4 => 0x3100589210203248d291800034930188a80bc0
  | 5 => 0xc20881002644c493252634930000061155e000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffffcf0fcf0ccc0fffffcf0fcf0ccc0fffffcf0fcf0ccc0fffffcf0fcf0ccc0fffffcf0fcf0ccc0fffffcf0fcf0ccc0fffffcf0fcf0ccc0fffffcf0fcf0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15034
namespace PEqualNP.Outside.L_meta_15034
open PEqualNP.Outside.L_meta_15034.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x38008802a000004a00b803c000000000c80182000000492263ea00004208500000158000002812601180006ce8020000035200000000138000347062ca8000002438000680004000000005000f0060022000000016100000300002000608000000c000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20ee20fd20fc20ec20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x34271d20564b522f00555805433c42443f220016455a0446540e12233a410f371c2a2b3b17114e470a2e0b1e01494830324d33090c53100600023e2900000000312c4a003908133d2528004f140d4c3818191b592107261f00000000500024003500001500004003002d511a57360a0674183060c2000230099020040100001860618003004c183319d4310edca421db54843bb28887755110ef4a021de54043bd286857950d0af4a1995e54332b7294836d52906bea6a0d714d41af298835d53106dca420db54841bd280837950106dca518db54a319faa2633c544c67ca818cf55031b7290636d520c6f4a018de54031b7286436d52886f6a090de14121f3a8a43eb50486d8a090fa14121b4282436e52086dca5a05b54b40af29c815d53902dea4a05b14940b7296616d52cc27ca9184f55230b7a92616c524c2daa3105b942209f2a0413d54082bca6105754c20bb2884175510835ca8106b55020e729841cd53083cca2105b54420f2a88416551082dca0107a94020f520041e940083d460107a4c020b7296216d52c43ca43887a08310b7a94216c52842dea4885b14910f290a213e540427aa8085794c10aea98216e52042daa4087a08010
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x12c52891a18240062e00020058088001c02ac0028002000031e000000000000480980384004005005071543544439a18152906686054a31ca99050487296414121d298c50487496314121c355153083265454420c955151083465354420d154d51083606054420b258e40083615190020d854540082a9648c020d85463008361514c020b818121c42e161083109919521442696508010ca55020043495308010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x68042001825916314121a42e8302a210541731815108320b1aa32004188591518c020
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | 2 => packedAt s1K2 (i*49) 49
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (802+((h/14+packedAt s1K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s1K4 (2667+((h/30+packedAt s1K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s1K3 (998+((h/8+packedAt s1K3 (950+(h % 8)*6) 6) % 48)*6) 6
  | 2 => packedAt s1K2 (248+((h/1+packedAt s1K2 (245+(h % 1)*3) 3) % 8)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x38f1fe3c7f8ffe3c63838fc38fc3ffe61c39f
  | 2 => 0xfc0fe1fff87ff8fc07c03f1fff1ff81e067cf3
  | 3 => 0xffe03ff80ff1ff8003fe03fe03fe1878f1c
  | 4 => 0xfff00003ffff001fffffc0003fffc001f80fe0
  | 5 => 0xfffffffc0000001fffffffffc0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x5011888452415001460a902510250a9860c185
  | 2 => 0x8220440811001040040090889089044021432
  | 3 => 0xab4455492532a03e88052a42aa42a545870e18
  | 4 => 0x3100589210203248d291800034930188a80bc0
  | 5 => 0xc20881002644c493252634930000061155e000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffffaf0faf0aaa0fffffaf0faf0aaa0fffffaf0faf0aaa0fffffaf0faf0aaa0fffffaf0faf0aaa0fffffaf0faf0aaa0fffffaf0faf0aaa0fffffaf0faf0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15034
namespace PEqualNP.Outside.L_meta_15034
open PEqualNP.Outside.L_meta_15034.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x84600200df43be43bc43dc439c43
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x11484c1800211e5390f1ca421e354843cb28887955110f34a021e654043
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x4203055254443c25495010f115154043
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 5
  | 3 => 7
  | 2 => 3
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | 2 => packedAt s2K2 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (84+((h/1+packedAt s2K4 (80+(h % 1)*4) 4) % 9)*4) 4
  | 3 => packedAt s2K3 (197+((h/2+packedAt s2K3 (189+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt s2K2 (116+((h/1+packedAt s2K2 (114+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf8f0fff0fffe3f0f1e380e3fe3fe0ffc30f3cf
  | 1 => 0xff0fff0fffc7f01fc00fc7fc7ff07cc33cf3
  | 3 => 0xfff0fff0fff8ffe0000ff8ff8fff8303cf3c
  | 4 => 0xff0000ffff0000fffffff000fff00003fc0fc0
  | 5 => 0xffffff00000000ffffffffff00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1182212442440050a09220920920528305145
  | 1 => 0x5222842428480850144244424424a050c12492
  | 3 => 0xa4444848829001aa2004889089094a03028a28
  | 4 => 0x30066682221c92334690e000f2406319540fc0
  | 5 => 0xc088880ccce124cc99270f2400018c62abf000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xffffee88ee88ee88ffffee88ee88ee88ffffee88ee88ee88ffffee88ee88ee88ffffee88ee88ee88ffffee88ee88ee88ffffee88ee88ee88ffffee88ee88ee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15034
namespace PEqualNP.Outside.L_meta_15034
open PEqualNP.Outside.L_meta_15034.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x681bf42d037a85a05f94740fb28e817651d02faa3a07d54740baa8e81bf41d037a83a05f55240bf29c81de53902bca7205f54e40eea9c815d53902fca5205f54a40bf28c817d51902fca1206fd0240fda04817f53502f8a6a06f90d40de21a817f52502f8a4a06fd0940dea12817f51502f8a2a06fd0540dea0a81fb405037c80a05f95040bf298817d53102fca4205f54840bf288817d51102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a99877d0f30ee21e617e52cc2faa59877ccb30ee996617e51cc3eca3985d94730bea8e61f551cc2eaa39877cc730ee98e617f548c2fca9186f952309f2a4617d548c37aa9184f55230be2a4617d538c2fca5185f54a30bf28c617d518c2fca1187e90230fca0461df308c3f661185fd5130bf2a2617d544c2f8a89877d0d30ee21a617f524c2f8a49877cc930ee992617f514c2f8a29877cc530ee98a61fa404c3f280987ecc130ef182617f540c2fca8185f55030be2a0617e530c2fca4185f54830bf288617d510c2fca01877cc030fd18061dd300c3f260185fd5320bf2a6417d54c82f8a9905fd4f20bf29e417d53c82f8a7905f94720bea8e41ef21c83da43905fd5220bf2a4417d54882f8a9105fd4e20bf29c417d53882f8a7105f54a20bf28c417d51882fca1107e90220fca0441fa30883f261107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a417f51483eea2905dd4520be28a41f451482e8a2907bc8520f690a41fa40483f280907e8c120fc98241fb20483dc40905fd5020bf2a041be540827ca8105f55020deaa0413d54082f8a8105fd4c20bf29841de53082bca6105f54c20eea98415d53082f8a6105f94820bf28841f651082eca2105f54420faa88417551082fca0107bc8020fd10041ed20083f240105fd5310bf2a6217d54c42f8a9885fd4f10bf29e217d53c42f8a7885fd4b10bf296217d52c42f8a5887d88710fa90e21fa40c43f281887e8c310fc98621fb20c43f041885fd5210bf2a4217d54842f8a9085fd4e10bf29c217d53842f8a7085fd4a10bf294217d52842f8a5085f54610fb20c21f541843ec63087d4c610fb90c21f421842fca1087e88210fc90421f710843f621085fd5110bf2a2217d54442f8a8885fd4d10bf29a217d53442f8a6885fd4910bf292217d52442f8a4887d88510fa90a21fa20443f240887ec4110fb082217f54042fca8086f950109f2a0217d540437aa8084f55010be2a0217f53042fca6087794c10af298217d53043baa6085754c10be298217f52042fca4087b94810b7290217d52043daa4085b54810be290217e51043ec82087d50410fb18821f531043ee42087d08410bf28021fa40043f280087e8c010fc98021fb20043f040087dc4010fd08021f510043f220087c44010
  | 1 => 0xf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442fb28885765110afaa2217d54442baa88857e5010bf4a0215e94042bea8085f95010af2a0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465ee428cbda851977cca32f7994657e518cafaa3195f94232bea84657f544cb7ea8994fd5132bf2a2657d544caf8a8996f151329e2a265de434cbba86997b90932f6a1265ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32efa1865dc430cafca41977cc832f719065dd320cbda64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83be43d077887a0df94b41bea9683bf42d077a85a0df94341fd286837a50d06faa1a0fe54341bca86837d54906fca720f794e41af29c837d53907baa720d754e41bf294837d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a83be435077886a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d53106fca420df54841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f7d0f31ee21e637e52cc6faa598f7ccb31ee996637e50cc7f4a198de94331bea8663f950cc6f2a198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31bf294637d528c6fca318fd90631faa0c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263df434c7b88698dfd4931be29263df324c7ba6498fd90531faa0a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52886fca310fd90621faa0c43f631887ea6310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fd90521faa0a43f631487ea6290fdc8521f710a437f50487f6a090ded4121be28243f850486f0a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81be43d037887a05f94b40bea9
  | 2 => 0x1c24432cb712f000001430000420004598700087c8583928e000002a800076800042206000c6074000538091f106e000001b124a000000000000d5502731240011400000c27000000252000000004c03d400027468398121c64727514c0f911a00000297146a9c002804b424c00000000504db9f600033c000003cc0014c870000360b39be2b06614b0410284d84c00029a0783301a0009e400000522a7ce19e44c47a47b2812e646d46a30000000002330000002c8002a40006e0000000013900020c7280000000000000000278278f08003320001e8223a68907c0973f800111800350000b8800030000000000ec7bc000883da724001350bc0010d1653b29ac258002240000000024803447a1300000000000000024000000009400018d4da8645909517283c1898948402c841f5006348358b62a63213d0eb45a8309d29b34e000348001e00002a0003c60013e23f000990000530008b80000005842521800000000fd0002429a0001cf0000004a0000001fd2e8003d4169089a04d84603e0814a82f8bc1e04f0000619880005a8f7000152000ad1aa286001008780b82b0fd9f33d6671151b64288c88505b30c26c7190e39a10c798482a821800a41452a48a6246292948748001541bc0d80a380001410000004052c000000000c70003ca2fc0020e32c0000003c0a004010001104003000080040000c150000201002004010400001c02028000040800c00008010000602803000000000501400004030480108400014070000000c0100802000030080000004004060080000000000000000800000024010040d02801000080200202401004020580c010000180700000010000200001402078000000000403064040001500005000060000d00002010190000001001000010100100000008140100305800000000000b0040202c01034010380100814010010040001c1500401018010081f0080b0100901400024000000402805028000040002c00010040001001004004070040302015000030000000405004060040b028000000000401000010380a0380702c0601c02000070040103afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443fb28887765110efaa221fd54443baa88877e5010ff4a021de94043bea8087f95010ef2a021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855f5350af8a6a17714d42ae29a85b
  | 3 => 0x23e4fa1f4000e40002100029e1e44ac369db0002c122a0b3725ac428cc000508c1215148000ada7500098c0000004048c001a300000007a27000000340003c4000b102a1560cc000000000000005d0080000025b0000007d1ae5340000000040c000788000003f0000000325ed159fd2d05a4ac9764ee870fa21212c00000000000970c88fe506a4c0026933e71c000000007580028446ca848b8b749027cc5a1d0924008a96134a000668890ae714a201054c4ccaf8b115c074001df0ce304190e008035cb32212bc000000362fc0001f87907637cb680044a00106800514754229300e200088a8f1da4303b800000829350a71a6888dd83e000474c9926366000c51190a4388e200e0004a003a2f000000cd14b000450000000000012790500000012800176134ec0000500000011a1b20009900034c00000000000000000000700000002e000000401702c87e4ef0000000b48f83005e118000ba02a79cc81cc1403b0898c41bc5bcce95d0009393d84e000228361310001ed4714a40839cab9e837e000002900007fc7e8000004e4648730000004100002e000be860000000000004a6744728ef50e000002a54dc2e08104431e4dc0025e538600568b5492a74000d13960000003c1f68f1460005446bc53002000655258a5000a8d200001229d0e721e20e540311ab1ac0012ba17412554a88a20ea7c09c0c70945c86023d3903b8329f72547755209a19ca514417a3700010c00015e7e0680264fc000b615c0c66d4878000680a4d20002683dc0000033637400000184001251d2000000d81974363fc629ec22c4b411a5527a9d86525f3ae614ff21633c7709d9c129e000a01b44cc001100000003a8a30000000004e8000008d4baa0700016027a5110e2300025945855815899290354d117c5528c40020517868400000470000000000000013808e022a249600035200126800000190000000f45140000000047800051488000880160008403918103e1552626f0100e85e9ba000411429bd0000300012e00000000000000000000000008dc86800000140002034c21f9040903280000000040049d3380000000000271000994001bc2c617c000001502cc74000000000c20d452a60c0017f1423180980000a1311d0da27c00123a3b000958f91740001a85a0000001590106e0000013f84727e070708f4240898bb97951620c6d9603a06c8d69ac384184c91
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x540825e63150209758c540827661150209d584540827a60150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209d98453082756114c209e98053083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083706054420d954720083395488020d654e200837151880209bd95200836551480209ed9520083395448020d654d20082f06148020dc545200825e63d53109758f54c423e64d4f108f59353c423e6414b108f59052c425e6314b109758c52c42f06048710b658e40c42b9648c310f848720c42b96408310b658c20c42f161083109798f548425d63d52108f993538423d64d4e108f990528423d6414a109798c528425d6314a10b558e41842b5648c610ad59021842d56308610bc58021842f06148210f8c85208425e63d51109758f544427561951109e582544423e64d4d108f59353442756194d109e582534427761549109ed81524423e64149108f590524425e63149109758c524427665885109d19521442f060485109e99620442786548110bc18520443e121481109798f540425d63d50109b98b540426d62d50108f59654043366195010ce982540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c755253043566194c10d6982530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d52043646154810da181520423e64148108f590520425e63148109758c520426e62148109d984520427a60148109d59641042d56390410d554e41043655290410bc58241043365450410d554d410436552504109d59631042b5648c410cd5523104365528c410bc5823104335544c410d594d3104365524c4109d597210436552c84109d59421042b56408410b558c21043655208410bc58021042796590010b658e40043595390010da54a40042f16190010ce95140043595350010da54940043b141500109e59630042b9648c010ce5523004369528c010bc5863004339544c010d694d3004369524c010f44c5300427965c8010da54b20043e321c80109e59420042b96408010b658c20043695208010bc584200436552c40109e59610043695284010bc58610042776544010d9549100427b6544010da54910042f36544010dcd9510042f36444010bc59110043b25444010ec55110042f36344010bc58d10043d25344010f454d10042f26244010bc18910043735244010f894910043715244010f854910043615244010
  | 1 => 0x867a6094d219e582534863f6454d218f191534867b6054d219e18153486d563905219d19541486b5648c5219d195314863e64141218f590504865e63141219758c504873a6414121ce590504875a6314121d658c50487724114121dc50450487723114121dc4c4504877321141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219d984540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c218f990530863d6414c219798c53086766114c219e98053086796014c21cd552210875553884219bd9521086776548421cd55121087555348421bc181210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b2154021dc88550087692154021dc485500871d5310f40ab58843d02b56110f40a718d42d025e63947409758e51d03566394740d558e51d03364354740cd10d51d03374254740cd50951d033651507409d98653902756194e40d598653903556194e40d6982539031e53d0240bc98740902ad6210d40ad58443502ba6010d409798c525025d63149409d98452502756114940a718d42502ba60d0540bc987405029e63901408fd95401027b65500409d98754cc27561d53309b98854cc26d62153309d98454cc2756115330c755043cc2cd6210f30b558443cc29c644cb308f99251cc23d6494730cd99251cc3356494730d5d0d51cc3544354730d5cc951cc3553254730d594531cc27661952309d586548c3366195230cd586548c33a6095230ce951408c31e54cc230bc987308c27661951309d586544c25e65d0d30c7550434c2cd6210d30b5584434c2da6010d308f990524c23d64149309d984524c2756114930a7191324c2da60cc530b698e404c2786550130e610d404c2f261cc130a7992304c25e63d50309b988540c26d62150309d984540c27561150309e980540c23e64940308f592500c25f654c0309ed95300c25f63553209718d54c825e63153209758c54c827661153209d58454c823f6454f208f19153c823e6414f208f59053c82766114f209d58453c82e860487209798f548825d63d52209d986548827561952208f993538823d64d4e209d98653882756194e20b658e40882b9648c2209d9865448275619512097d8d544825c63551209dd85544827461551209d98653482756194d208fd91534823c6454d209dd8553482746154d208f990514823d64145209798c514825d6314520cd99051483356414520d598c51483556314520dc580514836451c8520b658e404837051901209e19540483705150120ae5923048370518c1209e1953048370514c120dc147204825e63d50209758f540827661d50209d587540823d65950208f99
  | 2 => 0x4354442cdd095110b354254442d694e5010b595394042dc9465010b715194042d694d5010b595354042dc9455010b715154042ce90d5010b384354042ced095010b3942540429d98454cca7561153329e98054cca796015332c715143cca3e64947328f59251cca3e64943328f59250cca7661152329d584548ca7a60152329e580548cb1f5410e32b3588438cb8c4390a32b318d428cb8f4350a329ed81518ca7860546329dd85508ca7461542328f992544ca5f63551329d984544ca7561151329e980544ca7960151328f994544cb1d6315132cb588544cb366115132cd584544cb3a6015132ce580544ca5e6590d32c7152434ca5c6550d32c7151434cb2c5490932e390e424ca6c6550932e350d424cb1c548c9329d987540ca7561d50329e983540ca7960d50328f596540cb1c63550328f990540ca5e63150329b988540ca7661150329d584540ca7a60150329e580540ca5d65d0c32c7553430ca5d6510c32c7550430cacd6210c32c7553320cb2d548c83297d95320ca9c644c832c7551320ca6f654c832cb551320cb365494432cd552510cb365454432cd551510cb574354432d510d510cb573254432d54c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500cb5b4354032d610d500cb5b3254032d64c9500cb1d5310f41ab58843d06b96010f41a718d42d065e63943419758e50d075a6394341d658e50d073a4354341ce10d50d073b4254341ce50950d067a6094e419e58253907566194e41d698253907596094e41c794f41906f260d0641ab58843506b66110d41ae580435065e63149419758c525067a60149419e580525069c6350941bc983415069e63905418fd95411067765504419e98354cc67960d53319b98854cc66d62153319e98054cc6796015331c755043cc6cd6210f31b658043cc69c644cb318f99250cc63d6494331ce99250cc7396494331d6d0d50cc7584354331d6cc950cc75932543319e982548c6796095231cd986548c73a6095231ce582548c7365450631c7953318c6f260cc6319e982544c679609513197997434c71d5410d31b3588434c6d66110d31b6580434c63e64149318f590524c67a60149319e580524c69c644c931b598e414c6746550531e510d414c6f260cc531a7992314c65e63d50319b988540c66d62150319d984540c67a60150319e580540c63e64944318f592510c65f654c4319dd95310c65f63553219718d54c865e63153219758c54c867a60153219e58054c863f6454f218f19153c863e6414f218f59053c867a6014f219e58053c865e63d52219758f548867a60952219e582548863e64d4e218f593538867a6094e219e58253886d56390621ad592318867a60951219e582544865f63551219718d544867b60551219e181544
  | 3 => 0x217498310909634287011b9d5000000838000e4000002070000001a8003945001f00056e9d8002090000003380000000000000000538a62895506756417b000230000e7000119461150007d044ab44445f40005e43cae83f800000831338004e4970959d94701d0528e31044042b0c3000938dc0754fa1700010d420130ca1aa36e418001bf3587510e02847c000000e63ac4d4228bc0008480000045e000001b0000000000001608d063000000001320aa4cca74158000008ac000cb0523b56080005c4301d94800064400085000598f89a93d21a0560ec12a2b961000100a58e10542e272ce78001fc00157800500188000002243849eac305e42400139000000ffa314965400713f000000a19790f25c8000884f620ce91c52da001358002bc0015908b408000000110000593992f0000005b9bb0867f126a403b07e03d1e35a2894000001944e89194934830159800580099638f743e2640003a08201800010000040604c000640000413024060100501000024010300201002044000040b0040100c0400802024170040003c050101a0a8280040d0140a08c020080200407004011e0050080502002000060040b00000014020080001c0b0740600802014020000200c0007402028000000c0040000001004020000304c22000000000603810014000000700001068050200000001000020080c0040b0000001000010000180000402040000001400005018060240603c0500003000200300001432010070000e00c09014000141c010000000204006018030300002c0b0000100c00000040042b0200100004020010000300c01010010280100c07004000281e0200c02c1b00c1203c04000010000202423018210080d0080c00013000130180d00001000000040503c5f0580e00a7661149439d5845250e7a60149439e5805250e7a60d45439e5835150e7661d41439d5875050e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9f6150c43a7d814310f8d4394843c750d5210f8d4354843cbd0d5210f4e4354843cb50d5210f4d4354843c350d5210f954394443d994a5110f655294443e550d5110f665254443d95495110f994394043da94a5010f695294043dc9465010f715194043e650d5010f6a5254043da5495010f725154043dc5455010e5e63947429758e51d0a5e63943429758e50d0aad6210e429ed815190a7860546429dd855090a7461542429d9845350a756114d429e9805350a796014d42d35885350b566114d42d55845350b5a6014d42d65805350a3e65d0d42c714f4350b1c5350d42c714e4250a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842a718d4210b1d53508429bd954210b4d5350842d594e5110b555394442d594d5110b555354442cd90d5110b34
  | 4 => 0x28f47417d5291700024ca21251023790d9d10000d8ac80036a000000bd00005c001020000016a05b57e0c8000000009b86c11c30263ca78000000000007632cae40000027827c0025f5047ed3e03827c2580019f032ad80016b4e2ab53cabe2229e08228632e000320000de974b70120000709800034c8a400000068af0c100053e8e4cf00055c000f71b24eaa8c222cc114a907d0ee2a42793792025c284388064aa0a9539451e47cc0c270000000000004b21281994d4cab14001880e03ec488af0c0464711744ee0000019a18212c8c183000000591b1338590e315d1d296cf08004763596727e0003a0c6a1a3b8720b48004603f05a00000086141a69000ac4ad95700e7b4001fd0003902029400072400000220000000000000000000024e9b000000276000a10002484d04c06c0000003e800000794000000002496800b32a46c000ad000415118000000000000035a001190000004b00000a000a5cb98f3000584001a7000000001f51c07dc6e0000005e800000000001508f100034000226000000001cc000854000000001251e0cc0a42cc1b80000091cdc800136929122ab062138268ce23a2910027f4849883691f4bc5fc6d18b084438b413718e3d432a0310c2753080c4c018c102c64d01e07b14101a821698ef1e800c5a800592a655c1db0000000f9e02280000022740c000d08000006f4ac29e4b03a91eabb16cad54513850e665161b61ca791290d1318680de0243d6000280ba326648000000007385c9d0486838c304703a7746a051454a80370cf21e44c5c0004ac4991683f30e7f8000f00008a00000017c020472490cc15c6b8020000000012a09e7044d09733059400000416000fca5011a7b0420a9000000399df000a6000000440a408015348c488309774047d8f12c418a624999d747e6a02ca8b0584c41ca93026ac0439af21028c532913f4a100f07e52a8d9299845965d4541ab000174ae285000000002442ac5d80a8a000036c000c92349d0b829c43a6d0ad185176884180f81203340089c000000b11c359e5b1369a541ab28be0a209079c9b1de31403c6426349e4286a8a740a7a834acd184001511cd4a20000d0000001ecf7a1142c000f31320006396905a2528cc6982307a06d3d1d337c0951a8ab38868d442452966e9530945249040a16a1d6aa8b7a481a495cf912d3e04a0c814651a600a38fd05aa386e80041459c2986b0000008b20f552000a88b1078000bc07c1f20015e82145c6b813a0100023c7f80050237d2a1c700a688cda6a1b2a6cd986a4262fced0100aa40c8f15f0ee7a0aaa9a2c01600480000042c002ac000968bf0040008641114a2a800
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x9a007e0000000000000000006a0060ae0400741e96a40000b200560000006e080000000000308600c6008000005200000000002aac00000000b4b0000600000000b6c262000000008a4c42008e000000b80000000000005a0054c000341400a20000003200ba0000007264000018be008c0000000090481024a6200a003e4a009802000000000094007058000000000016000000c4680000000000000038004e00a07882462600002c0000003c84000000c8000000001a0000000000aa6c000000120000000000000000449c2e7a0000000000003a000000000000009e00000000007c0000ca0c00002200004000006600365c00500e00000000005e0000000076009200000000000000881c0000280000a8000000000000bc0000010000a00000040201008040000030000400000100200000000000030000002000000200008064ab88c4a1887265c06250c43932e1b0a8621c9571d814310e863b286a908743dc54354843a1ee0a1aa421f054354a5110f82a1aa4a8887c250d5294043e1286a92a021f11435455010f22b12c229a85925896014d42ca2c2b00a6a15257210d5110a8a39a84a88854a5c84354042a30e6a12a02160f54588438ca473b686a14658358d6215132c4ac4b08a89962962580544cb18b0ac02a265439d64390932c18caa1a849960d54588430ca0e3b2a899065515c84354432a28e8992a2195497210d500ca8c3a264a80658354d6210f41a52e421aa1a0d187350950d0706aa2c421e63525c84354331a30e8992a198e0d54588434c6c2b9086a0a63645c04350531c32c8b18a090d51739045048698ba462282438c5506048421ca2a63024210e0d5358843d0292b9086a8e81451cd4254740c1aa8b1087985457210d51cc28a3a264a8e61835516210d30b12e421a80985917110d404c30ab22c628a419458c5190120c62c828c6090631541852008328a98c290041495d06154810a8ae630aa4085297418152042a4b98c0a90219158d5290410cc2a4b0482086256454a3104330a92c118821895915208410c8ac6a904208661525802104324b1aa520021985496190010e22a6a0a8008721525054004314b22a51802198549618c010e22a898a6008741524c530042b0bae43900219859721c8010c52c8a904008649635482004330a92c210021345cf6444010962e9b1a20087115454d1004258ba0c488021345cc6244010ac2eb29220084707654910043912a2a488021c85515244010e84a6a922008741535491004331bb2a488021981d95244010cc6c8a922008661645491004331b1aa4880219858d5244010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xae2084600c00905811d94354843909801d9435484390980dc5435484390581dc14354843a21841d95244010a41831d95244010a4183d915244010a2184d8d5244010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 682
  | 4 => 725
  | 3 => 102
  | 2 => 8
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (i*5) 5
  | 6 => packedAt s3K6 (i*16) 16
  | 5 => packedAt s3K5 (i*27) 27
  | 4 => packedAt s3K4 (i*38) 38
  | 3 => packedAt s3K3 (i*49) 49
  | 2 => packedAt s3K2 (i*60) 60
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (20684+((h/227+packedAt s3K5 (18414+(h % 227)*10) 10) % 990)*11) 11
  | 4 => packedAt s3K4 (29960+((h/241+packedAt s3K4 (27550+(h % 241)*10) 10) % 958)*11) 11
  | 3 => packedAt s3K3 (5304+((h/34+packedAt s3K3 (4998+(h % 34)*9) 9) % 283)*8) 8
  | 2 => packedAt s3K2 (488+((h/2+packedAt s3K2 (480+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x78e3c71fc71fe3f31e3831c7c71f8ff3134cf
  | 1 => 0x7f03f81ff81ffc7c1fc03e07f81ff1fc238f3
  | 2 => 0xf8003ffe3ffe3ff8fe0003ff8ffe3fe003cf3c
  | 4 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x50e046228542944030a0a905141448ca311445
  | 1 => 0xa10c89450a252808c144522228889614c22892
  | 2 => 0x11000100000010200004801202000004128
  | 4 => 0x32240129a1200c92546918000e4d0246540ec0
  | 5 => 0xc44822400249b124a992639340000498abb000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfffff8f8f8f8e8e8fffff8f8f8f8e8e8fffff8f8f8f8e8e8fffff8f8f8f8e8e8fffff8f8f8f8e8e8fffff8f8f8f8e8e8fffff8f8f8f8e8e8fffff8f8f8f8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15034
namespace PEqualNP.Outside.L_meta_15034
open PEqualNP.Outside.L_meta_15034.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2d06493283e1002f56000212025280541878d400002702b87003c00e824600a1736440192c69105482c0180e2840c5855493380004003c300b080083540000ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32df32fe32fd32dd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x143a03456761b808000023a050e091f9a436850e190f877248c8961e3c90ca45714178404205894c66223044427d3796c5e6c289b4dc861c20c0048189ed080028000ac0029800485a13a087200228f0441f0000076104001098003280cd65926828000c001ccce682093c003e3d1d4005400198003d1497c1c3025174e423389386a183f000b8190e9fc0006000140026001605c00381a8542d1a0480e003c000805509910741619800002c0a984c00f0085c001a1b0001003080013020a09000a0108050600001e011f05011e000e0e2d0104000e020a002901041a01130004010f000228b7294876d5290ebca7215754e42cf29c859d5390a7ca5214f546429ea84855e5310abaa6215d94442baa88857a5010af2a0216794c42cea98853e5210b5ca4216d944429ea8885b55110a6aa2216e940429ea8085b95010a72a0214f953329eaa6659e54ccb3aa9996790b32ce216655d538cb5885194fd51329e2a265ac424cb3ea8996715132e7a9265cf424cb3c84996710932e6212658c424cabca6194f94b41cf996839d32d067aa1a0cf552419e292839f325073a64a0edd45419fa82833e541067ca918cf552319f2a0633d540c6dca418db54831bd2806379500c67ea990cf15321af29e435d53c879a6590cf952219eaa443b5418867ea890cf15121e699243b5414867ca810cf55021af298435d53086f4a010de540219f296819f32d033a65a04f547409eaa4813c525033e64a0674c9409fa8a81bb505027ca8204f952309eaa4613e540c27aa8185b94830b6a906176510c2eaa2184fd53209e2a6415e53c82baa790734cb209f2a4413d548837281104fd51209e2a241cd324837280904f950209eaa0415e53082baa6105d94420baa88413e54c427aa9884f952109eaa4213e544427aa88857d4d10ae29a213e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x12897801600000500002b0078c2520088843499088385c50000b408c006c000000002c00c4980323ca00248000000013b03e541873a382a452a83231a5802e000230481006838914041021a20183a358e5210b165354442c554d5110b315194042c694d5010b195354042cc9455010b315154042a558442cca996010b32a9584428caa96010a32a9584424caa96010932a3993524ca1e6590932a398a424ca1e6510932a5584424ca996010932b1584424cac96010932a3994424cb0e6510932e1984424ca8d6110932e1584424ca856110932e2980424ca8d6010932e2580424ca8960109328e580525070c524c9418e58054c870c544cb21c315132486346550521e14c941486356114940c314932502356115320c315132c830c544c9208e195404838932501208b189544424d6214d10d454d10043615244010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x830080104071942a1a05866010932d04c2b00849968161580424ca84b80a499283425c0544cb21c08ca9928290d05711493250282b88a899641821953250120
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | 2 => packedAt s4K2 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (864+((h/16+packedAt s4K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s4K4 (4032+((h/45+packedAt s4K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s4K3 (2012+((h/16+packedAt s4K3 (1900+(h % 16)*7) 7) % 73)*7) 7
  | 2 => packedAt s4K2 (453+((h/3+packedAt s4K2 (441+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1e3f878fc7f8fe3f1c71f1c1e3f0fe3f0d34cf
  | 1 => 0x1fc7f80ff8ff1fc7e07e3e01fc7f0fc7323b33
  | 2 => 0xe007fff3ff001ff8ff803ffe3f800ff8c3cc3c
  | 3 => 0xfff80003ffffe000ffffc0003ffff000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4300a010422108400810504840904222051045
  | 1 => 0x84210220904030084022221084240504122112
  | 2 => 0x921101001244012480048429022890404c28
  | 3 => 0x890554a24900492b5448024324aa090e80e80
  | 5 => 0xd124660836e49924da793939000cc126bfb000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15034
namespace PEqualNP.Outside.L_meta_15034
open PEqualNP.Outside.L_meta_15034.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x42bc6802a94499380032e008002c4c04f172274d18048c70c4e00a16143cfa254905a8561d4885a00d85260090300108000018495c14c0670402c0000004ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32df32fe32fd32dd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x302600351a09285171d8d8000a800004a002008a00120007800000109e000000000000c8000064000010e00089103a4d070c4ae74011f00e002717c000026000f64631000b272169c4c000200bcce0000204000000000000007800000000000760a001480000001501a3600000d200000e8106b1800000001300012000800006002c0004e3f24000000000058240000000840000000fc0000080f02a2088c561c298e46429001940a2200000000000000fa0b318600000001dc500000000f20041140dc5d0016c0000369bcbc000000000141e9e8b43e128e0e0610f0dc00350000000000000000000000000830000068561085cea0000000007300000000000210001a3300000001617000000d80096472a8000c86000cc001f0094400003f80000430000000008100402020040403000081000000000e02000000004000040604008040002018080000000040202018000800000000401b7294876d5290ebca7215754e42cf29c859d5390a7ca5214f546429ea84855e5310abaa6215d94442baa88857a5010af2a0216794c42cea98853e5210b5ca4216d944429ea8885b55110a6aa2216e940429ea8085b95010a72a0214f953329eaa6659e54ccb3aa9996790b32ce216655d538cb5885194fd51329e2a265ac424cb3ea8996715132e7a9265cf424cb3c84996710932e6212658c424cabca6194f94b41cf996839d32d067aa1a0cf552419e292839f325073a64a0edd45419fa82833e541067ca918cf552319f2a0633d540c6dca418db54831bd2806379500c67ea990cf15321af29e435d53c879a6590cf952219eaa443b5418867ea890cf15121e699243b5414867ca810cf55021af298435d53086f4a010de540219f296819f32d033a65a04f547409eaa4813c525033e64a0674c9409fa8a81bb505027ca8204f952309eaa4613e540c27aa8185b94830b6a906176510c2eaa2184fd53209e2a6415e53c82baa790734cb209f2a4413d548837281104fd51209e2a241cd324837280904f950209eaa0415e53082baa6105d94420baa88413e54c427aa9884f952109eaa4213e544427aa88857d4d10ae29a213e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x80e0001699000001a00005803ea9300007108a048c015024422f28a47803c3400c2eb091612951180c018310e9d02e500c000360040026742ab48060118a241000808101820200182a358e5210b165354442c554d5110b315194042c694d5010b195354042cc9455010b315154042a558442cca996010b32a9584428caa96010a32a9584424caa96010932a3993524ca1e6590932a398a424ca1e6510932a5584424ca996010932b1584424cac96010932a3994424cb0e6510932e1984424ca8d6110932e1584424ca856110932e2980424ca8d6010932e2580424ca8960109328e580525070c524c9418e58054c870c544cb21c315132486346550521e14c941486356114940c314932502356115320c315132c830c544c9208e195404838932501208b189544424d6214d10d454d10043615244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x204618400200a001c0c3a05866010932d04c2b00849968161580424ca84b80a499283425c0544cb21c08ca9928290d05711493250282b88a899641821953250120
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (864+((h/16+packedAt s5K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s5K4 (4077+((h/45+packedAt s5K4 (3672+(h % 45)*9) 9) % 261)*9) 9
  | 3 => packedAt s5K3 (2012+((h/16+packedAt s5K3 (1900+(h % 16)*7) 7) % 67)*7) 7
  | 2 => packedAt s5K2 (453+((h/3+packedAt s5K2 (441+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e3f878fc7f8fe3f1c71f1c1e3f0fe3f0d34cf
  | 1 => 0x1fc7f80ff8ff1fc7e07e3e01fc7f0fc7323b33
  | 2 => 0xe007fff3ff001ff8ff803ffe3f800ff8c3cc3c
  | 3 => 0xfff80003ffffe000ffffc0003ffff000fc0fc0
  | 4 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4300a010422108400810504840904222051045
  | 1 => 0x84210220904030084022221084240504122112
  | 2 => 0x921101001244012480048429022890404c28
  | 3 => 0x890554a24900492b5448024324aa090e80e80
  | 4 => 0xd124660836e49924da793939000cc126bfb000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8fef8eee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15034
namespace PEqualNP.Outside.L_meta_15034
open PEqualNP.Outside.L_meta_15034.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10054f028d223179d0001c0000d4d1e0000020128588a1e0573900b00270e192b06e21a36367d5ba48885bb06a0cb22a0022d2898916664003d4660e17263800052260810d0614000000c4800c08800264c18002ffd5009fe54007f55009fc5401ffd4c07fe5301ff54c07fc5301ffd0c07fe4301ff50c07fc4302ffd4801fe52007f5480bfc52027fd0801fe42007f50809fc4201ffcc807df3201ff8c807fd3200774c807fc3202ffd4405fe51007f54405fc51027fd0405fe41007f50405fc4101ffcc405fe3101ff4c405fc31007fc8405fe21007f48405fc2102ffd4003fe50007f54003fc50027fd0003fe40007f50003fc4001ffcc003fe3001ff4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x864001ff8432000ff82190003ff65480017fb2a400dff9952002dfcca90003fd65480017eb2a400dff1952002df8ca90003ff64480017fb22400cff99120025fcc890003fd64480017eb22400cff19120025f8c890037ff5448019ff2a24000ff55120067f8a89002fff63480177fb1a400bff98d2001dfcc69002ffd63480177eb1a400bff18d2001df8c69002fff5348017ff29a400bff54d2005ff8a69002fff4348017ff21a400bff50d2005ff88690006ff624801bffa924009ff94920007faa490027fc5248019ffa124009ff90920007fa8490027fc4248017ff992400bf7cc92004ffc649002fee3248017fe9924000f74c92005fda6490003cd3248013fe1924000ffd8520005fec29002bfe61480057f30a4000ff58520057f8c29000afc614801bffa8a400aff94520007faa29002bfc5148019ffa0a400aff90520007fa829002bfc4148017ff98a400aff8c52005ffa629002bfc3148013ff90a4000fbc8520057fc4290003fd2148001f690a4009ff0852000dfec090007ff5048003ff2824001fe9412000ffaa090003f95048003fe2824001ffd012000ffc8090007fa4048003fea024000fe5012000ff88090007ff3048003ff1824001ff4c12000ff86090007ff2048013fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffe2090007fe1048003fd0824001ff04120007feca88002ff6544011ff32a2005bf99510007faca88002fd6544011fe32a2005bf19510007fec888002ff644400fff3222004bf99110007fac888002fd644400ffe3222004bf19110047fea88801ffe5444001feaa22007ff15110037fec68801aff6344001efb1a2000b7d8d10037fcc68800efe634400dfeb1a2006bf58d10037f8c68800efc634400dee31a2003b718d10037fea68801bfe534400dfea9a2006ff14d10037fe868801bfe434400dfea1a2006ff10d10007fec488002ff6244001ff3122009bf98910007fac488002fd6244001fe3122009bf18910047fea488003fe5244001fea922008ff1491003ffe8488003fe4244001fea122007ff10910037fe648801bdf324400dff1922006ff4c910007ba648801bfc32440037fb0a2002ffd4510017fca28800bfd5144005fe28a2002ffd0510017fc828800bfd4144005fe20a2002ffcc510017fc628800bf63144005fe98a2006fd4c510017f8628800bff2144005ff10a2002fd88510017fa4288003f52144005fe10a2001bfd811000ffea088007fe5044003fea822001ff1411000ffe8088007fe4044003fea022001ff1011000ffe6088007fe3044003fd1822001ff4c110037f26088007fc3044003ff9022001ff8811000ff44088007fd2044001fc9022001ff0811000ffe208800bfb1044003ff0822001fd8411000ff82088007f41044003fc0822001fc04110
  | 1 => 0x77c5054003fc282a001ffd015000ffc80a8007fa4054003fe202a001ffcc15000ffc60a8007fd3054003fe182a001ff8815000ff440a8007fc2054003ff882a001ff8415000ff820a8003ff65500017fb2a8014ff9954002dfccaa0003fd65500017eb2a8014ff1954002df8caa0006ff6450009ffaa28014efd5140027fca8a0013fd5450009fe2a28004ef1514009ffec6a004eff6350027ff31a8003bf98d4009ffac6a004efd6350027fe31a8003bf18d4009ffea6a004ffe5350027fea9a8013ff14d40027fe86a0013bf4350009ff21a8004ff50d4009f7a86a0013fc4350001ffb128000bfd8940007fcc4a0003fd6250001fe3128009bf189400a7fea4a0003fe5250001fea928014ff14940027fe84a0013bf4250009ff2128004ff509400077a84a0013fc4250027ff9928013f7cc94009ffc64a004ffd3250001ee9928013ff0c940007fec2a0002ff6150025ff30a8002bf98540007fac2a004bfc61500057e30a8014ffd4540097fca2a0003fd5150025fe28a8004ffd05400277e82a0013fe4150009fea0a8000ef50540027f882a004fff3150025ff18a8013ff4c540097f862a0003ff2150025ff10a8000ff48540097f842a0006ff6050003ffa828001ff9414000ff4a0a0007fd5050001fca828001ff1414000ffe80a0013fb4050003ff2028001ef9014000ff880a0007bc4050003fc2028001ffcc14000ffc60a0007fd3050003fe1828001ff8814000ff440a0007fc2050003ff8828001ff8414000ff820a0027ff65c80137fb2e4009ff9972002dfccb90027fd65c80017eb2e4009ff1972004df8cb90027ff64c80137fb264009ff99320025fcc990027fd64c80017eb264009ff1932004df8c990047ff54c8021ff2a64000ff55320087f8a990027ff63c80137fb1e4009ff98f2001dfcc790027de63c80076f31e4009ff58f2007dfac790027dd63c80016eb1e4009ff18f2004df8c79003fff53c801fff29e400fff54f2007ff8a79003fff43c801fff21e400fff50f2007ff88790006fe62c8013ffa964009ff94b2004ffaa590027fc52c8013ffa164009ff90b2004ffa8590027fc42c8013ff9964009f7ccb2004ffc6590027ee32c8013fe9964009f74cb2007fda6590003cd32c8013fe1964009ffd872004ffcc39000afe61c8013feb0e4000bf5872004ff8c39000afc61c8023ffa8e400eff94720007faa39003bfc51c8021ffa0e400eff90720007fa839003bfc41c801fff98e400eff8c72007ffa639003bfc31c8013ff90e4009fbc872004ffc4390027fd21c8001f690e4009ff0872000dfac190007ff50c8003ff2864001ff5432000ff8a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1864001ff4c32000ff86190007fe20c8003f71064001fe8832000ff84190007ec20c8003ff8
  | 2 => 0x21017fe839080bfe41c8405fea0e4202ff10721017fe639080bfe31c8405fe98e4202ff0c721017fc439080bee21c8405fb10e4202ff08721017d84390827ff60c8413ff3064201bf9832104ffac190802fd60c8413fe3064201bf183210fffea190873fe50c8439fe286421effd03210e7fc8190873fc40c843bff986421cff8c3210effa6190873fc30c8413ff1064209ff08321017fe219080bfe10c8405fe0864200ffd9521005feca9086ffe654840b7f32a4200ff59521005faca9086ffc654840b7e32a4200ffd9121005fec89086bfe64484097f3224200ff59121005fac89086bfc64484097e322421bffd51210d7fca890803fd5448435fe2a24219ffd8d210cdfec690867fe63484077f31a4219ff58d210cdfac690867fc63484077e31a4219ffd4d210cffca690867fd5348433fe29a4219ffd0d210cffc8690867fd4348433fe21a4202bfd89210dffea490827fe5248401fea924209ff149210d7fe8490827fe4248401fea124209ff109210cffe6490867df3248413ff1924219fb8c9210cffa6490803dd3248433f69924200f34c92104ff8649080aff6148405ffa8a4202ff94521017eca29080bfd5148401faa8a4202ff14521017fe829080bfe4148405fb20a4202ff50521007ea829080bfc4148405ff98a4202ff8c521017fa629080bfc3148405ff90a4209fdc8521017fc429080bee2148405fe10a4202fb08521017e84290803ff60484017fb024218ff9812100dfcc090803fd6048431fe3024201bf181210dffea090863fe5048431fe282421affd01210c7fc8090863fc4048433ff9824218ff8c1210cffa6090863fc3048431ff1024209ff08121017fe209080bf71048405ff0824202ff0412100dfecaa8003ff64540017fb22a017ff99150025fcc8a8003fd645402ffe322a004bf1915002ffea8a8017fe545402fbf2a2a005ff5515002ff8a8a80177c545402dffb1aa016bfd8d500b7fcc6a800efe635402dfeb1aa016bf58d500b7f8c6a800efc635400bffa9aa005dfd4d5002ffca6a8017fd535402dbea9aa005ff14d500b7fe86a805bfe435402dfea1aa016ff10d50007fec4a8002ff6254001ff312a000ff58950007f8c4a8026fc625400bffa92a005dfd495002ffca4a8017fd5254001bea92a005ff149500bffe84a8003fe4254001fea12a017ff109500b7fe64a805bdf325402dff192a016ff4c950007ba64a805bfc3254001ffb0aa000bfd85500affcc2a800afe6154001feb0aa015ff18550015f8c2a8017ff515400bbfa8aa005ff9455002ffaa2a80037d515400bfe28aa017ffd05500affc82a8003fd415402bfe20aa016ffcc5500affc62a805bfd315402bfe18aa000ffc85500affc42a8003fd215402bfe10aa001bfd815000ffea0a8017fb5054003ff282a001df9415000ff8a0a800
  | 3 => 0xe312a209bf1895102ffea4a88177f525440bff292a205ff54951006faa4a8817fc525444bffa12a200ff90951007fa84a8897fc4254449ff992a224f7cc951127fc64a8893fd3254401ee992a224ff0c951015fec2a880bff515440bfba8aa202ff94551016fca2a880bfc5154405be28aa202fd14551017fe82a880bfe4154405fb20aa202ff10551017fe62a880bfe3154405fe98aa202ff0c551017fc42a880bf62154405fe10aa200ffd8151005fec0a888ffe60544037f302a200ff5815111ff8c0a8806fc605440bffa82a205dfd415102ffca0a8817fc505444bffa02a223ff9015111ff880a8893ff3054447ff182a224ff4c15111ff860a888ffe2054447fe102a202ffc4151017fc20a880bfc1054401ffb2a8200bfd9541117fccaa0816fe6550401feb2a8200bf59541117f8caa0816fc65504057fb228204ffd51411177ea8a0813fe5450409feaa28204ff1514102778a8a0887ff63504437fb1a8221ff98d4101dfcc6a0887fd63504437eb1a8221ff18d4101df8c6a0887ff5350443ff29a8221ff54d4110ff8a6a0813ff4350409dfa1a8204ff90d41027fa86a0887bd4350409fe21a8200ffd8941005fec4a0803fe6250401feb128200ff1894104df8c4a088bff5250401ff2928200ff54941117f8a4a0813ff4250409dfa128204ff90941027fa84a0803bd4250409fe2128221ffcc94110fbe64a0887fe3250443fe9928200f74c94110ff864a080aff6150405ffa8a8202ff94541017eca2a080bfd5150401faa8a8202ff14541017fe82a0813f74150405ff20a8202ef90541017f882a080bbc4150405fa20a8202ffcc541017fc62a080bfd3150405fe18a8202ff88541017ec42a080bfc2150401ffb028200bfd8141107fcc0a0806fe6050401feb028220ff1814100df8c0a088bff5050441ff2828220ff14141027fe80a0813bf4050409ff2028204ff1014110ffe60a0883fe3050443fe9828220ff0c141107fc40a0883fc2050405ff8828202ff84141017f820a0827ff65c84137fb2e4209ff9972102dfccb90827fd65c84017eb2e4209ff1972104df8cb90827ff64c84137fb264209ff99321025fcc990827fd64c84017eb264209ff1932104df8c99087fff54c843dff2a64200ff553210f7f8a990827ff63c84137fb1e4209ff98f2101dfcc790827de63c84076f31e4209ff58f210edfac790827dd63c84016eb1e4209ff18f2104df8c790877ff53c843bff29e421dff54f210eff8a790877ff43c843bff21e421dff50f210eff8879080afe62c8413ffa964209ff94b2104ffaa590827fc52c8413ffa164209ff90b2104ffa8590827fc42c8413ff9964209f7ccb2104ffc6590827ee32c8413fe9964209f74cb210efda6590803cd32c8413fe1964202bf58721017fea39080bfe51c8405fea8e4202ff147
  | 4 => 0x27fd61908017eb0c8409ff18642015f8c3210c7ff519085fff28c842fff14642027fe8321013fe4190809fe20c8430ffcc64217ffc63210c3fd319085ffe18c8409ff8864204ff84321027ff6090813ff3048401bf9824204ffac121002fd6090813fe3048401bf1824218ffea1210bbfe509085dfe2848404ffd0242027fc8121013fc4090861ff984842eff8c242187fa61210bbfc3090813ff1048409ff0824217ffe21210bbfe109085dfe0848400ffd9542005fecaa10037f65508013fb2a842dff9954202dfccaa1003fd65508017eb2a842dff1954202df8caa10037c655080b3e32a8409bfd9142027fea8a1013fe5450809df2a28404ff551420077aa8a1013fc5450859ffb1a842cbfd8d42167fcc6a100efe6350859feb1a842cbf58d42167f8c6a100efc6350859ffa9a842cff94d42167faa6a10b3fc5350809ffa1a8404ff90d42027fa86a1013fc43508097fb12842dffd494204ffca4a1003ee5250801fea928400fb5494204ff8a4a1013ff4250809f7a128409ff9094204f7c84a1027fc4250813de2128404fb10942167fe64a10b3df3250813ff192842cff4c94204ff864a1003ff61508017fb0a842bff98542015fcc2a1003fd6150857fe30a8402bf1854216ffea2a10affe5150857fe28a8404ffd05420277e82a1013fe4150809fe20a842cffcc54215ffc62a10b3fd3150857fe18a842bff8854204ff842a1003ff60508017fb02842aff9814200dfcc0a1003fd6050855fe3028401bf1814216ffea0a10abfe5050855fe2828404ffd01420277e80a1013fe4050809fe202842cffcc142157fc60a10b3fd3050855fe182842aff8814204ff840a10afff1050855ff082842aff04142007beca990a7de654c801eeb2a6429f719532007bec8990a3de644c801eeb226428f71913214fbea8990a3de544c801eeaa26428f71513201fbec49900edf624c807e7b126429f7d493204fbca499003dd524c813ee2926428f7d093204fbc8499003dd424c813ee2126400f7d853213fbcc299003dd614c84fee30a6429f7d453213fbca29909fdc514c851efa0a6427f79053213fb8829909fde214c813ee10a6400f7d8132137bcc099003dd604c84dee3026429f7d4132137bca09909bdc504c851efa026426f790132137b8809909bde204c813ee1026427f7c4132137bc209909bdc104c8057fb2aa200ffd9151005fec8a8897fe64544097f322a200ff5915112ff8c8a8812fc645440bffaa2a205ff9515112efca8a8817fd545440bfe2a2a205df15151127fec6a8892ff6354449ff31aa203bf98d51127fac6a8892fd6354449fe31aa203bf18d5102ffea6a88177f535440bff29aa205ff54d51126faa6a8817fc5354449ffa1aa224ff90d51127fa86a8893fc4354401ffb12a200bfd8951007fcc4a8803fd6254401f
  | 5 => 0x525204ffec729026ff6394813ff31ca403bf98e5204fbcc72900ede6394813feb1ca438bf58e5204fbac729002dd6394813fe31ca409bf18e5202ffea729017fe539480bfea9ca405ff14e521c7fe87290e3fe4394871fea1ca438ff10e5204dfcc529027ff5294813bfa94a405fbd4a5204ff8a529027ec5294813ffa14a409ff10a5204ffe6529027df3294813ff194a409ff4ca5204ff86529027ff6194813ff30ca402bf9865204ffac329002fd6194813fe30ca402bf1865202ffea329017fe519480bfe28ca439ffd06521bffc83290dffc4194871ff98ca437ff8c6521c7fa63290dffc3194813ff10ca409ff0865204ffec129027fe60948037f304a409ff58252005fac129027fc60948037e304a405ffd425202ffca129017fc5094873ffa04a436ff902521b7f881290e3ff309486dff184a438ff4c2521b7f86129027fe2094813fe104a437ffc42521b7fc21290dbfc10948137fb2aa400ffd9152005fec8a9003bf64548015fb22a435ff99152025fcc8a9003fd645486bfe322a404bf1915200778c8a9012bc645480bffaa2a405dfd515202ffca8a9017fd5454801beaa2a405ff151521a7fec6a90d2ff6354869ff31aa403bf98d521a7fac6a90d2fd6354869fe31aa403bf18d5202ffea6a9017fe535480bfea9aa405ff14d521a7fe86a90d3fe4354869fea1aa434ff10d5202dfec4a9017ff525480bf7a92a409ff9495204efca4a9027fc5254813be292a405fb149521affe84a9027fc4254869ff992a434f7cc95204ffc64a90d3fd3254813fe192a400ffd8552005fec2a90cffe61548057f30aa400ff5855219ff8c2a900afc615480bffa8aa405dfd455202ffca2a9017fc515486bffa0aa433ff9055219ff882a90d3ff3154867ff18aa434ff4c55219ff862a90cffe2154813fe10aa400ffd8152005fec0a90cbfe60548037f302a400ff58152197f8c0a9006fc605480bffa82a405dfd415202ffca0a9017fc505486bffa02a432ff90152197f880a90d3ff3054865ff182a434ff4c152197f860a90cbfe2054813fe102a433ffc4152197fc20a90cbfc1054813ffb2c8409bfd964204ffccb21016fe6590813feb2c8400bf5964204ff8cb21026fc65908097eb248404ffd524218f7ea921013fe5490809feaa48404ff1524202778a921027ff63908137fb1c8409ff98e4201dfcc721027de63908076f31c8409ff58e42185fac721027dd63908016eb1c8409ff18e4204df8c7210c3ff5390861ff29c8430ff54e42187f8a721013ff4390809ff21c8404ff50e42027f88721026fe6290813ffa948409ff94a4204fdca521027fd5290801f6a948409ff14a4204ffe8521027bf4290809f7a148409ff10a4204fd88521027ff3290813ef9948409ff8ca4204ffa6521027fc3290813ffb0c8409ff98642015fcc321
  | 6 => 0x54030080000000101c00c0100000401403c0080300001c0080001a14802806016000010000080100101c0060000080202c0040d002000000000050260040780000a0080080201e0080000002800800002000004010040020041882200401c00000000000008000020100500a03e0180201500400003002004008008010000200000d0020780800201a000010010001140000000c0080000c00c0080000f014000000000140100180001e0140200100c0280080000400403804000028010020100440000e004050090110000000600100e0000400a000038000020080000700100000c01000000000028010040000000001a0081200c0000040000100405c0a0080020400581500c024040050000080500600003400803004014008010000300000000200001800004004000000140000080601000400000064000010000000300400101a0540000301800c010020020a80080100600c0300601c0840381b00c0000600600e00003803006040008000000140380f004014010010020000081200c0080180b00002800000014004008070000041180500603c0000400801405005000000070000700000000300a0080180000c0000380c01804c0200d00e010020010040040580e00002c040080000140080710a0180000f00c008028190240001380800000c060000000000c00601801c0400200400410002002004010020000040000200200800000026018008000000101e00001400408811000010080040000100380601600c0800401204c008090120200200b0000000000001c000097fb2aa804bfd9154027fea8aa017bf5455009ff2a2a804df95154027f8a8aa0137c5455009de2a2a804cf151541e7fec6aa0f2ff6355079ff31aa803bf98d541e7fac6aa0f2fd6355079fe31aa803bf18d5402ffea6aa017fe535500bfea9aa805ff14d54027fe86aa013fe4355009fea1aa804ff10d54007fec4aa002ff6255001ff312a800ff58954007f8c4aa026fc625500bffa92a805dfd495402ff8a4aa013ff4255009dfa12a804ff109541e7fe64aa0f3df3255079ff192a83cff4c9541e7f864aa003ff61550017fb0aa83bff98554015fcc2aa003fd6155077fe30aa802bf1855402ffea2aa017fe515500bfe28aa804ffd0554027fc82aa013fc4155079ff98aa83bff8c5541e7fa62aa0effc3155077ff10aa83bff08554007fec0aa002ff6055075ff302a801bf98154007fac0aa0ebfc60550037e302a805ffd415402ffca0aa017fc5055009ffa02a804ff90154027f880aa0f3ff3055075ff182a83cff4c1541d7f860aa0ebfe2055075fe102a83bffc41541d7fc20aa0ebfc105500b7eb2ca409ffd925204ffcc929012fe6494813feb24a400bf5925204ff8c929026fc649480bffaa4a405ff952521cefca929017fd549480bfe2a4a405df1
  | 7 => 0x18f1e24fe4291c05530b053144e42b1e43eb0000000000004fd00521b53300024e5475340b243000032d0000001d500039a48a4a73f200050b3fa3c40005130000000004180000000000f00000ce1701660002254c23ab57900014d14b1a112a00036d29e33c00b08a3783851bf13f5050f717c1061004f83bc0004b65482650004920952d74b00001aa1c82f723f00049000052b0025321a84a828100000046042637031212736f5612ed18d00010e3564c70310002c339700006d26d43f0182c53654781dd28f22d2a556d4023ce29037700049b2df05c32b3050000000fd49e0000000000002dd02102319343b1910ab05e0002fe4e631e19034301f5020000004d800029856713e44825c0004912280370000471ac21c5194d951a2514050003ac00006f0723e70000ed0000515100002710000790005860000003c318e3b612602d2c437b2eb4ee3a53440002240e20004c64ec2f90003f338606c3300e30000002de05d0004d30003d50000003711af45800010800030b00000000051f2500003890a65491a00c50005915780004cb08829c4142bc0000004c900008500005750a00045d27529420342e15b33317b52531c1ba1c30461521604c81bb0a306e0035760f150340b2ad5352f605002903f4ed3d63642572022ff2061424791c22483740c716b2a14074f727d3a62051c526a23d3220c608e08f3204610920c947152a27b3f51df0000063610000004bc31f4120134e40000342140ad29917251e00012401038a0002b256349f0a40004390002740562fa5230001fc57e11009a02e1cd37a00000000031d4cf04b16812d3f756c00000025e0e84cd00034500000000000044400020400047c5214c30cf55f0002960c84a14f62bb27c2a75202f844547e2ec4513c92c624a5410000003a900000002b0001550121364ab4a445a00024c0001fd39308032f00032a03905f3af00000030a26f0000000000004631483d80701491c91ab1583002ee2ca0432b144c47a34f00051621f09640a0001b40dd11500004a1e85291e90d009010b2f213a4a94fa0000b547d0000003a700000000049a00056f00048e1dc49d0004af1ce2b623107e2b42ea0243ad4720f81170a953907c1cf1b24b238136a3312b300000004f00000000009b00004d4fc0002264e200059000048110c3625241f32d40ba04c0002fb00042d4ff42844924513354c50633d3373180421a953c2660000002114974650000e70004523320fb45316e5594d216726e00033548f3a300000039e0001cb1b31a74100000002c947b05b1780980003fe4354570000000070000200080904e01c0501000202c000040000100200800201401006000004000190020000d0050040000000700600002000002030010190340040b00800e0000200300001439809012000008260060
  | 8 => 0xea20c3505733f626b1a53e93a13b229525a17a10f10748500000057f0000000004080c401c31915614002a01457d40906800050f08116c0000000d313945532357c0004400003841464b30530002e30000001280002b90003d43f835a2b000043d0000dc0003d234100000027f4d041d1eb20a53d00000039145931a04936b2ac0000000000001e300000000000040d0712290160001ad0732d50005521882e70b103e19522f0000001e60000d423c0a732537c4f100000017d0e00004ca0000000000000003ea51c5080004ba0003d31801c758110a49c1e516f52729d58e4ad0000524ac41b0b30943b01db41f3b538300048d19b24400038237f3805544dc1850000000eb34e1860a84871ca32142f03213730937e45f55e23712f39d15952c5570010f31a31314421b91a21b540c3014733fc5750974410f607f4e55600f21620000000000000000000000000000221113882da13b0000000000003b30000000000000830000000004622805222af4471f117128b41155c5144bd40f4824be2001b70593b72150fe0172e20b800f04840e5510000001770b421e0000000001e72163b900043600000050700000013000000006156200000000000000030c00054e0004e900014428900000000049800000049930f35100000023e5420000002e90000000002010000000003552d23600fa1da4a63a435f12e32800022a06700054b2be21225b0004680db1981d60005434740110000004370a50000580001472600000d70f42b515a2e60002f40001194641570004da0000002a60001960004b75175260602ef4173923e31c429b58510d09100000022304e35b0383dd0e600000045e3e60001b80ff2780e409e2680193ee1541d700000003024613200a4834f448b00028819d11e0001020000000842331f00083940660d80000003064560b719f15d00039b00015f15c0004272d10000000000000000005010000000000000000000001790e50003ec33e00056634b2bd24b0000002d826c0003470fc2a800058356a00000000033f1132210000000000002aa09f00016900003a4660040000000000000000000000001340000005112130003630ef03c19e00043800026900006311a49646700027306b24100020800011d4a33d00000000000004d42c80001732302833a24e71d824d0d50410005744a23f13e23da54f3d14d71f71e02930de25d3c01d20bd10401b4221d10ae1200002f53aa1224b93c22e40871632421433c519442409d54002856e00042000000020911f1ae3bf32c0000770761830002a300021a51b2f04aa28d32e5581d92f11ec3963b12343ae0d606236822c00000043e4d506a19c30814c00012b0204d617600032700018403500016a47714a01e2fd0404f246d0000cd00019a2c70003c145c3e02760002fc2524a0530
  | 9 => 0x2070004331fe07d1e10ca57246f1382c246a0003ef5040af2db00000011c2e500036c0000001b65690000a03cf0e931400036e2dc4f500000000000005528c1180001d34e01f200000050d0c134c0000000b900029a2d300001d53f3d713c1ff0822913a80000752401f51f946b34d44a4340002722593bd2b80005371f80003483491f62c002502f4ea00048005a1a60000be4004f340321d0bc0000001452a24e34eb1f417f3571d40000c20bb1094f91875284b826100000022e45400000029745b00022b3160004880002c126300042c0540004693b43de0004cc4ce0000005383290f500002c58b24718100054a3521610000002390002ae3db00037912936747031530742a3dc58700047517500d2384164fb46e1892b746c3394de58a3990003fd3e814f0000ea0001654194c111b55558c58d2795560a133b53b2823c72bf00926200000035c00000039856b00027a48c4bb23500c0001c10000000000d15803f928a00001a08c00000000000030200e3b80000004b439c51200033655d0001c618c1d052f10304509309c15157755031700044f0004a50a20004ae38d2d92104d100018228e23208b30e3cd1a454d00050c3244010bf3344b13ba3f000050e00047f24f34613d4464e15642430aa0d22873ff3133c63bb1cc38749309912517e2ce12153631051838c20f4430b620d21955a2702f334a3e135321747640411239017430439f0ec0d907a4e853e38f35442344d10142123a57b5150260e10444894dd2545452a45703693265712e80c00df0000005845680890862e04944c55462cc3752855880361995003d935e0cb20e3f415e1b05891414c007435d4bf1ee07b1bc0781bd41a44b3a02365441054df1b10da00048414e3e52180151643e400024938e2d041e26400031b45041525f00000053a3df0003fb3591531142cd0000000652e118a22238b3c82860001974ef1161233110691ef00016d27756543c55b2272a940625318b12c4b53ed00000003b26715039529f0cc1ed3be4311fa58258f23b08d33a30d50900735852e2ba3380003cb43a51d41c37228420b2ab2584322920c32cb0ee37325600052d0000000000000004f03030000000000000000004133400002550f90000001be2d603d2a019202734236657a37627e1351de3cc3ca4db37d0ac0642204254951fb4c42cf4860331
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd751891003dbe7418910005bd7418910035de7318910005dd7318910006df6318910006dc631891004eee6218910006ed6218910217f0101891004cff7694910004fe7694910004fd769491004cfc7694910035de7394910005dd7394910006df63949101c6dc6394910015f67194910005f5719491000dfa7094910005f970949101b7f01094910004ff7654910004fe7654910004fd7654910004fc765491002e7e65549100067d6554910005bf745491003dbc7454910006df63549101a6dc6354910197f0105491004cff7690910004fe7690910004fd769091004cfc7690910035de7390910005dd7390910006df6390910186dc6390910015f67190910005f5719091000dfa7090910005f97090910177f01090910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100457c7550910026be6450910006bd6450910006df6350910166dc6350910157f01050910006df764c910005de764c910006de764c910004de764c910006dd764c910005dc764c910006dc764c910004dc764c910006df654c91014ede654c910006dd654c91014edc654c910006df644c910146de644c910006dd644c910146dc644c91020ddf724c910037cf724c910006df624c91004ede624c910007ce624c91004ece624c910006dd624c910007cd624c910006cd624c91004edc624c91013fd6714c910007d5714c910136df614c91013fcf214c91013fd6214c91013fcd214c910137da704c910007d9704c910136df604c910137cf204c910137da204c910137cd204c91013fdb104c910137d6104c910137d4104c910137d8104c910137d0104c91000df4764851004ef4764851000cf47648510006f76548510006f56548510006f76448510006f56448510205f77348510205f57348510007d763485101ffd46348510015f77248510017e77248510007e7624851004ef6624851004ef46248510007e462485101ffd732485101ffe63248510007d532485101ffe53248510007c53248510007f3704851000df6704851000df470485100c7f0704851000df07048510016f76048510017f360485100c7f230485101fff130485100c7e720485100c7f220485100c7e52048510015f8764811004ef87648110014f87648110006fb6548110006f96548110006fb6448110006f964481101f5fb73481101f5f97348110007db63481101efd8634811000dfb724811000feb7248110007eb624811004efa624811004ef86248110007e862481101efdb32481101efea3248110007d932481101efe93248110007c93248110007f37148110015fa7148110015f87148110057f07148110015f0714811000efb614811000ff36148110057f231481101eff13148110057eb2148110057f22148110057e92148110007f12148110007e12148110
  | 1 => 0x9110006bd4359110004ff725911004cfc725911003ebf4259110006df3259110244ff7159110006f77159110096f62159110104ff7059110006fb7059110106fa2059110004ff7655110004fe7655110004fd7655110004fc765511003f3c54551101e6dc63551101d7f0105511023dde76d8d10036de76d8d1001cde76d8d10006df65d8d10006de65d8d10006dd65d8d10006dc65d8d10006df64d8d10006de64d8d10006dd64d8d10006dc64d8d10005dd72d8d1022fd771d8d1022fd471d8d10237d621d8d10237db70d8d1022fd870d8d1022fda20d8d10237db10d8d1022fd610d8d1022fd410d8d1022fd810d8d1022fd010d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10004dd72d8d10006dc72d8d10006df52d8d10006dc52d8d10006df42d8d10006dc42d8d1022edf71d8d10236de71d8d1022edd71d8d1022edc71d8d10236df51d8d10236de51d8d10236dd51d8d10236dc51d8d10236df41d8d10236de41d8d10236dd41d8d10236dc41d8d10236df21d8d10236de21d8d10236dd21d8d10236dc21d8d1022edf70d8d1022ede70d8d1022edd70d8d1022edc70d8d1022edf50d8d1022ede50d8d1022edd50d8d1022edc50d8d1022edf40d8d1022ede40d8d1022edd40d8d1022edc40d8d1022edf20d8d1022ede20d8d1022edd20d8d1022edc20d8d1022edf10d8d1022ede10d8d1022edd10d8d1022edc10d8d1004cfe76d8910035dc73d8910006df63d8910006dc63d891021ff010d891002cfe75d8910004fd75d891002cfc75d8910024fe74d8910004fd74d8910024fc74d8910004ff73d8910006df73d891001cfe73d8910004fd73d891001cfc73d8910006dc73d891001cdc73d8910006df32d891000cff71d8910014fe71d891000cfd71d8910014fc71d8910226ef21d8910226ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d891021eef20d891021eed20d89100c4fd7698910035de7398910005dd7398910006df6398910006dc6398910006ef62989100c5f57198910055f970989100e7f0109891004cff7658910005df7358910035dc7358910006df6358910006dc63589100e5f77158910075fb70589100c7f01058910004ff755891002cfe755891002cfc7558910004ff7458910024fe7458910024fc7458910004ff7358910006df7358910004df735891001cfe7358910004fd735891001cfc7358910006dc735891001cdc7358910006ef7258910006df3258910006ee3258910006ed32589100e4ff7158910006f771589100c4ff7058910006fb705891021cfe76189100457e75189100057
  | 2 => 0x297e93254120007c93254120005fb715412006f7b5154120007795154120007eb2154120007e9215412004df87650120026f8765012004cf87650120005fb7550120005f97550120006fb6550120006f9655012000dfb745012000fbb7450120007bb6450120026fa6450120026f86450120067b8645012028fbb5450120067b85450120067bb4350120287b94350120007eb725012004dfa725012004df87250120007e8725012000efb625012000feb6250120067bb4250120007b94250120287db3250120287ea3250120007d93250120287e93250120007c93250120005fb7150120067bb4150120007b94150120007eb2150120007e9215012002cfe76d95100467e65d951003dbe74d9510005bd74d9510006dc63d951026ff010d951011cfd75d9510024fe74d9510006be74d9510024be74d9510004fd74d9510006bd74d9510004bd74d9510024fc74d9510004ff73d951001cfe73d9510004fd73d951001cfc73d951004cfe72d9510004fd72d9510006df32d951000cff71d9510014fe71d951000cfd71d9510014fc71d951027e7f51d951027e7d51d951027ef621d9510014ff70d951000cfe70d9510014fd70d951000cfc70d951026e7f50d951026e7d50d951026efa20d951002cff76595100467c6559510005df7359510035dc7359510006dc6359510265f77159510275fb705951011ff0105951026cff75595100067f7559510004ff7459510024fe7459510024fc74595100067e54595100467c5459510004ff7359510006df7359510004df735951001cfe7359510004fd735951001cfc7359510006dc735951001cdc73595100467f53595100067d5359510004ff725951004cfc72595100467f5259510006df3259510264ff7159510006f771595100aef6215951011cff7059510006fb705951011efa2059510024fe76d91100457e75d91100057d75d911003ebe64d9110006dc63d911024ff010d911002cfe75d91100067e75d911002c7e75d9110004fd75d91100067d75d91100047d75d911002cfc75d9110104fd74d9110004ff73d911001cfe73d9110004fd73d911001cfc73d911004cfe72d9110004fd72d9110006df32d911000cff71d9110014fe71d911000cfd71d9110014fc71d911025ebf41d911025ebd41d911025ef621d9110014ff70d911000cfe70d9110014fd70d911000cfc70d911024ebf40d911024ebd40d911024efa20d9110024ff765911003ebc6459110005df7359110035dc7359110006dc6359110245f77159110255fb7059110107f01059110004ff755911002cfe755911002cfc755911024cff7459110006bf7459110006bf545911003ebc5459110004ff7359110006df7359110004df735911001cfe7359110004fd735911001cfc7359110006dc735911001cdc735911003ebf435
  | 3 => 0xe644c920007cd644c9202cfcc644c9202d7cf544c9202cfce544c920007cd544c9202cfcc544c920007cf714c9202c7ce714c920007cd714c9202c7cc714c9202c7ce614c9202c7cc614c9202d7cf514c9202c7ce514c9202c7cc514c9202cfcf414c9202c7ce414c9202c7cc414c920137cf704c920007cb704c920137ce704c920137cd704c920137cc704c920137c8704c92004fcf604c92004ecf604c92004fcb604c920137cf504c920137ce504c920137ca504c920137cd504c920137cc504c920137cf404c920137ce404c920137ca404c920137cd404c920137cc404c920137cf104c920137ce104c920137ca104c920137cc104c920014fe76d8520007cd32d8520056f661d852002cfe75d8520004fd75d852002cfc75d8520024fe74d8520004fd74d8520024fc74d8520004ff73d852001cfe73d8520004fd73d852001cfc73d852000cfd72d8520014fc72d8520006df32d8520006ee32d8520006dd32d8520006ed32d8520006cd32d8520006f731d8520056f431d8520056f621d852000cfe70d852004cfd70d852000cfc70d85200e6f710d8520005df735852005ddc7358520007cd3258520056f46158520004ff7654520004fe7654520004fc765452002e7e65545200067d6554520007cd325452000dfa7054520004ff7650520004fe7650520004fc7650520026be6450520006bd6450520007cd325052000dfa7050520215ee76c852004eee76c852004def73c852004fce73c85202bded73c852004fcd73c8520005cd73c85202b6ef63c85202b6ed63c85200c5ed71c8520016ee61c8520016ec61c852004feb70c852000dee70c852000dec70c852004fe870c852004eef60c852004feb60c85200e7ea50c85200e7ea40c85200e7ea10c852000cfc76485202a7cf3248520007cd3248520006f76148520016f4614852004fe42148520005fb704852000df8704852004fe8204852000dec7648520016ec764852000cec76485202adef73485202aded73485202a6ef63485202a6ed634852004def714852004fe77148520007e76148520016ee6148520016ec6148520057e46148520057e65148520007e55148520057e64148520007e54148520007eb704852000dee704852000dec70485200c7e8704852004eef604852004feb60485200c7ea50485200c7ea40485200c7e710485200c7ea104852004df8765412002ef8765412004cf8765412000dfb755412000f7b75541200077b655412002efa655412002ef8655412006f786554120005fb7454120006fb6454120006f9645412029f7a545412006f78545412006f7b5354120297795354120007eb725412004dfa725412004df87254120007e8725412000efb625412000feb625412006f7b5254120007795254120297db3254120297ea3254120007d93254120
  | 4 => 0x952004cfc72d952006e7f52d9520006df32d9520014fe71d9520004fd71d9520014fc71d952004cff70d952004cfd70d95201b67f50d95201b67d50d95201b6fa40d952006e7c6559520005bf7459520065bc74595202e5ef72595201b4ff75595200067f7559520004ff7459520006bf7459520004bf7459520024fe7459520024fc7459520006bc7459520024bc7459520004ff735952001cfe7359520004fd735952001cfc73595202e4ff7259520006ef7259520006df3259520004ff7159520014fe7159520014fc715952006e7f5159520194ff7059520006fb7059520196fa4059520024fe76d9120066be64d912002cfe75d9120004fd75d912002cfc75d9120006bf54d9120066bc54d9120004ff73d912001cfe73d9120004fd73d912001cfc73d912004cfe72d912000cfd72d912004cfc72d9120066bf42d9120006df32d9120014fe71d9120004fd71d9120014fc71d912004cff70d912004cfd70d9120176fa50d9120176bf40d9120176bd40d91200057f755912006d7c7559120066bc64591202ddef7259120004ff75591200067f75591200047f755912002cfe755912002cfc75591200067c755912002c7c7559120174ff7459120006bf7459120004ff735912001cfe7359120004fd735912001cfc73591202dcff7259120006ef7259120006df3259120004ff7159120014fe7159120014fc7159120066bf4159120154ff7059120006fb7059120156fa5059120004ff7655120004fe7655120004fd7655120004fc76551200673c545512000dfa705512002cff765492000cfe7654920194fd765492000cfc76549200067f655492002e7c6554920005bf7454920065bc7454920005fb705492000df87054920024ff765092000cfe7650920154fd765092000cfc76509200057f755092006d7c7550920006bf6450920026bc6450920005fb705092000df8705092001edf764c920136de764c920136dd764c92001edc764c920006df654c92014ede654c920006dd654c92014edc654c920006df644c920146de644c920006dd644c920146dc644c92004ddf724c92005fcf724c92004edf624c9202d7cf524c92004fce524c920007cd524c92004fcc524c9202cfcf424c92004fce424c920007cd424c92004fcc424c92013ede614c92013edc614c92004fcf214c9202c7ce214c92004fcc214c920007db704c920137d8704c92004edf604c920137da504c920137da404c92004fdb204c920137ce204c92004fcc204c92004fd8204c920137da104c92005fcf764c92001ecf764c920137cc764c92001ecc764c920007cf754c9202d7ce754c920007cd754c9202d7cc754c920007cf654c9202d7ce654c920007cd654c9202d7cc654c920007cf744c9202cfce744c920007cd744c9202cfcc744c920007cf644c9202cfc
  | 5 => 0x4ede4258f2004edd4258f2004edc4258f20006df7158f20006de7158f20006dd7158f20006dc7158f20006df5158f20006de5158f20006dc5158f20006df4158f20006de4158f20006dc4158f2004edf2158f2004ecf2158f2004ede2158f2004edd2158f2004edc2158f20136df7058f20136de7058f20136dd7058f20136dc7058f20136df5058f20136de5058f20136dd5058f20136dc5058f20136df4058f20136de4058f20136dd4058f20136dc4058f2004edf2058f2004ede2058f2004edd2058f2004edc2058f20136df1058f20136de1058f20136dd1058f20136dc1058f2004fcf764cb2004dcf764cb2031ecf764cb20007cf754cb20317ce754cb20007cd754cb20317cc754cb2004fcf654cb2004fce654cb2004fcd654cb2004fcc654cb20007cf744cb2030fce744cb20007cd744cb2030fcc744cb2004fcf644cb2004fce644cb2004fcd644cb2004fcc644cb20317cf544cb2030fce544cb20007cd544cb2030fcc544cb20007cf714cb20307ce714cb20007cd714cb20307cc714cb2004fcf614cb2004fce614cb2004fcd614cb2004fcc614cb20317cf514cb20307ce514cb20307cc514cb2030fcf414cb20307ce414cb20307cc414cb20137cf704cb20137ce704cb20137cd704cb20137cc704cb20136cd604cb20137cf504cb20137ce504cb20137cd504cb20137cc504cb20137cf404cb20137ce404cb20137cd404cb20137cc404cb20137cf104cb20137ce104cb20137cc104cb20004ff755872002cfe755872002cfc7558720004ff7458720024fe7458720024fc7458720004ff735872001cfe7358720004fd735872001cfc735872000cfe7258720014fd725872000cfc725872004edf325872004eee325872004edd3258720006ed3258720006cd325872004ef77158720076f65158720076f6415872004ef7215872004ef4215872004efa205872004ef920587200c6f71058720004ff7654720004fd765472004cfc765472002e7e65547200067d6554720126de6354720006dd6354720007cd3254720016f66154720006f56154720004ff7650720004fd765072004cfc7650720026be6450720006bd645072010ede6350720006dd6350720007cd3250720016f66150720006f5615072004def76487202feef76487202f5ef73487202f5ed734872004eef634872004fce63487202eeed634872004fcd6348720006cd634872004fe7714872004fe76148720016ee6148720016ec614872004fe46148720077e65148720007e55148720077e64148720007e5414872000dee704872000dec70487200c7e7104872002cfe76d952006e7e65d9520024fe74d9520004fd74d9520024fc74d95200067e54d952006e7c54d9520004ff73d952001cfe73d9520004fd73d952001cfc73d952004cfe72d952000cfd72d
  | 6 => 0xc6550540335bf7350540335bd735054032ebf635054032ebd6350540005bf7250540006bf625054032f9f32505400079d3250540025bf7150540027b77150540007b76150540016be6150540016bc6150540097b46150540097b65150540007b55150540097b62150540007bb705054000dbe705054000dbc7050540107b87050540026bf6050540027bb6050540107ba5050540107ba2050540004fe76c8540004fd76c854004cfc76c8540025be74c8540005bd74c854009dde73c8540005dd73c8540007cd32c854000dfa70c8540005f970c8540004ff7648540004fe7648540004fc7648540025be7448540005bd7448540007cd3248540016f66148540007b54148540025f8765414002ef87654140024f8765414000dfb755414000f7b75541400077b655414002efa655414002ef865541400a7786554140007bb7454140025fa7454140025f874541400bfb8745414000efb645414000fbb64541400a7bb54541400bf7a54541400bf7854541400bfb854541400bf3854541400a77b53541403277953541400bfbb4354140327b94354140005fb7254140006fb62541400a77b52541400077952541400bfbb4254140007b94254140327db3254140007d932541400a77b51541400077951541400bfbb4154140007b9415414004e7f7559720004ff7459720006bf7459720004bf7459720024fe7459720024fc7459720006bc7459720024bc745972008e7f5459720004ff735972001cfe7359720004fd735972001cfc735972004cff725972000cfe725972004cfd725972000cfc725972004e7e525972004e7c525972004edf325972004edd3259720004ff7159720014fe7159720014fc715972008e7f51597201967f50597201967d505972004efa205972004ef92059720004ff75593200067f75593200047f755932002cfe755932002cfc75593200067c755932002c7c755932004ebf7459320086be5459320004ff735932001cfe7359320004fd735932001cfc735932004cff725932000cfe725932004cfd725932000cfc725932004ebe425932004ebc425932004edf325932004edd3259320004ff7159320014fe7159320014fc7159320086bf4159320156bf4059320156bd405932004efa205932004ef92059320004ff765532004cfe7655320004fd765532004cfc765532002e7e65553200067d6555320026be6455320006bd64553200873c54553201e6de6355320006df7558f20006de7558f20006dd7558f20006dc7558f20006df7458f20006de7458f20006dd7458f20006dc7458f20006df5458f20006de5458f20006dd5458f20006dc5458f2004edf7258f2004cdf7258f2004ede7258f2004edd7258f2004cdd7258f2004edc7258f2004edf5258f2004ede5258f2004edd5258f2004edc5258f2004edf4258f20
  | 7 => 0x9540004ff725954004cfc72595400a67f52595400bebf4259540006df3259540004ff7159540014fe7159540014fc71595401d4ff7059540006fb70595401d6fa205954004cfe76d894002cfe75d8940004fd75d894002cfc75d894000cfd74d8940004ff73d894001cfe73d8940004fd73d894001cfc73d8940366ee42d8940366ed42d8940006df32d8940014fe71d8940004fd71d8940014fc71d8940366bf41d8940024fd70d89402defa50d89402deef20d894009dde7398940005dd7398940006ef6298940065f970989400057f75589400a57c7558940085fb70589400a57e75189400057d751894009dde7318940005dd731894004eee6218940006ed6218940095f67118940005f57118940004fe7694940004fd769494004cfc76949400067f659494002e7c6594940025be7494940005bd74949401cf3c549494009dde7394940005dd739494000dfa7094940005f97094940004ff7654940004fe7654940004fc765494002e7e65549400067d6554940005bf7454940025bc74549400a73f545494000dfa705494000dbc765094004ebc765094000cbc76509400073f75509400a5be75509400a5bc75509400073c75509400a53c7550940006bf6550940006bd655094035dbf735094035dbd7350940025bf7250940027af7250940007af625094004ebe625094004ebc6250940007ac6250940007ae5250940007ad52509403579f3250940005bf7150940007bb705094000dbe705094000dbc7050940157b87050940026bf6050940027bb6050940157ba5050940157ba2050940006df764c940006de764c940006dd764c940006dc764c940006df654c94014ede654c940006dd654c94014edc654c9401479e744c9400079d744c940136df644c94034f9f544c9401479c544c94020ddf724c94009fcf724c940006df624c94004ede624c94004edc624c9401479f424c9400079d424c94013ede614c94013edc614c9401479f414c940136df604c940137da504c940147db404c9401379e404c9401379c404c940137d8404c940137da204c940014fe76d8540096f661d854002cfe75d8540004fd75d854002cfc75d854000cfd74d8540014fc74d8540006bf54d8540346bc54d8540004ff73d854001cfe73d8540004fd73d854001cfc73d8540346bf43d8540006bd43d854004cfe72d8540004fd72d8540346bf42d8540006bd42d8540006df32d8540006dd32d8540096f641d8540346f541d8540024fd70d8540246fa20d8540246f710d8540005df735854009ddc7358540096f4615854033dfb7058540004ff7654540004fe7654540004fc76545400067f655454002e7c6554540005bf7454540025bc745454012f3c545454000dbc7650540016bc765054000cbc76505400a5be75505400a5bc7550540116be6550540116b
  | 8 => 0x76d525095000dfa7050950006df764c950006de764c950006dd764c950006dc764c95014f5e754c9500075d754c950136df654c950006df644c950146de644c950146dc644c9503af5e544c95014f5c544c95020ddf724c9500b7cf724c950006df624c95004ede624c95004edc624c95014f5f524c9500075d524c95013ede614c95013edc614c95014f5f514c950136df604c95014fdb504c9501375e504c9501375c504c950137d8504c950137da404c950137da204c950014fe76d85500aef661d855000cfd75d8550014fc75d8550024fe74d8550004fd74d8550024fc74d85500067e54d85503a67c54d8550004ff73d855001cfe73d8550004fd73d855001cfc73d85503a67f53d85500067d53d855004cfe72d8550004fd72d85503a67f52d85500067d52d8550006df32d8550006dd32d85500aef651d85503a6f551d855002cfd70d8550266fa20d8550266f710d8550005df73585500b5dc73585500aef4615855039dfb705855000d7c76545500167c765455000c7c76545500bd7e74545500bd7c745455012e7e645455012e7c64545503957f73545503957d735455038e7f635455038e7d63545500057f72545500067f625455038f5f32545500075d325455002d7f715455002f7771545500077761545500167e61545500167c61545500af7461545500af7641545500af7621545500077b705455000d7e705455000d7c705455011f78705455002e7f605455002f7b605455011f7a405455011f7a2054550004ff7650550004fe7650550004fc76505500057f755055002d7c7550550006bf6450550026bc64505500bf3c5450550007755150550004fe76c8550004fd76c855004cfc76c855002d7e75c85500057d75c85500b5de73c8550005dd73c8550007cd32c855000dfa70c8550005f970c8550004ff7648550004fe7648550004fc764855002d7e75485500057d7548550007cd3248550016f6614855000775514855002cfe76d95400a67e65d9540025be74d954000dbd74d95400a73f54d95401d4fd75d954000cff74d9540024fe74d954000cfd74d9540376bd74d954000cbd74d9540024fc74d95403867f54d95400a6bf54d95403867d54d9540386bc54d9540004ff73d954001cfe73d9540004fd73d954001cfc73d954004cfe72d9540004fd72d95400a67c52d9540386bf42d9540006df32d9540014fe71d9540004fd71d9540014fc71d95400a67f51d9540024ff70d9540024fd70d95403767f50d95403767d50d9540376fa20d954002cff76595400a67c655954036dbf74595400bf3c545954037dfb7059540374ff75595400067f755954036cff7459540006bf74595400a6bf54595400be7e54595400be7c54595400bebc54595400be3c5459540004ff735954001cfe7359540004fd735954001cfc735
  | 9 => 0x57550521006f76550521006f56550521015f77450521017b77450521007b76450521026f66450521026f464505210d7b464505213e7b754505210d7b454505210d7b743505213dfb54350521007e7725052104df6725052104df47250521007e47250521016f76250521017e762505210d7b74250521007b542505213dfd732505213dfe63250521007d532505213dfe53250521007c53250521005f770505210d7b7405052100cfe76d8121007cd32d81210c6fa60d812102cfe75d8121004fd75d812102cfc75d8121024fe74d8121004fd74d8121024fc74d8121004ff73d812101cfe73d8121004fd73d812101cfc73d8121014fd72d812100cfc72d8121006df32d8121006ee32d8121006dd32d8121006ed32d8121006cd32d812104cfd71d812100cfc71d8121006fb30d81210c6f830d81210c6fa20d81210c6fa10d8121005df73581210cddc7358121007cd32581210c6f86058121024fe76d915002d7e75d915000d7d75d91500bebe64d91500bf3e54d915000cfd75d915036e7d75d915000c7d75d9150024fc75d91500be7e54d91500bebe54d91503d6bd54d91500be7c54d9150004ff73d915001cfe73d9150004fd73d915001cfc73d915004cfe72d9150004fd72d91503d67f52d91500bebc42d9150006df32d9150014fe71d9150004fd71d9150014fc71d91500bebf41d915002cfd70d915036ebf40d915036efa20d91500bebc64591500bf3c54591503cdfb705915004cfe76d895000cfd75d8950024fe74d8950004fd74d8950024fc74d8950004ff73d895001cfe73d8950004fd73d895001cfc73d89503c6ee52d89503c6ed52d8950006df32d8950014fe71d8950004fd71d8950014fc71d89503c67f51d895002cfd70d89502e6fa40d89502e6ef20d89500b5de7398950005dd7398950006ef629895006df97098950005bf74589500bdbc745895008dfb70589500bdbe7418950005bd74189500b5de7318950005dd731895004eee6218950006ed62189500adf67118950005f5711895000d7c765495004e7c765495000c7c76549500073f74549500bd7e74549500bd7c74549500073c74549500bd3c74549500067f64549503bd7f73549503bd7d735495002d7f725495002f6f72549500076f625495004e7e625495004e7c62549500076c62549503b75f32549500057f71549500077b705495000d7e705495000d7c705495019778705495002e7f605495002f7b60549501977a40549501977a2054950004fe7690950004fd769095004cfc769095002d7e75909500057d7590950006bf6490950026bc64909500bf3c54909500b5de7390950005dd73909500076d529095000dfa7090950005f97090950004ff7650950004fe7650950004fc76509500057f755095002d7c7550950026be64509500bf3e5450950
  | 10 => 0x9121004fd735912101cfc7359121414ff7259121006ef7259121006df325912115cff7159121006f7715912115ef65159121004ff705912100cfe705912100cfc70591210d6bf4059121004ff7655121004fe7655121004fd7655121004fc76551210d73c5455121015f6715512102cff7654921014fe765492119cfd7654921014fc76549210067f655492102e7c6554921005bf74549210d5bc7454921005f77154921015f47154921024ff7650921014fe765092115cfd7650921014fc76509210057f75509210dd7c7550921006bf6450921026bc6450921005f77150921015f4715092101edf764c92113ede764c92113edd764c92101edc764c921006df654c92114ede654c921006dd654c92114edc654c921006df644c921146de644c921006dd644c921146dc644c92104ddf724c9210cfcf724c92104edf624c92140fcf524c92104fce524c921007cd524c92104fcc524c921407cf424c92104fce424c921007cd424c92104fcc424c921007d7714c92113fd4714c92104edf614c92113fd6514c92113fd6414c92104fd7214c92113fce214c92104fcc214c92104fd4214c921136de604c921136dc604c92104fcf204c9213ffce204c92104fcc204c92113fd7104c9210cfcf764c92101ecf764c92113fcc764c92101ecc764c921007cf754c92140fce754c921007cd754c92140fcc754c921007cf654c92140fce654c921007cd654c92140fcc654c921007cf744c921407ce744c921007cd744c921407cc744c921007cf644c921407ce644c921007cd644c921407cc644c92140fcf544c921407ce544c921007cd544c921407cc544c92113fcf714c921007c7714c92113fce714c92113fcd714c92113fcc714c92113fc4714c92104fcf614c92104ecf614c92104fc7614c92113fcf514c92113fce514c92113fc6514c92113fcd514c92113fcc514c92113fcf414c92113fce414c92113fc6414c92113fcd414c92113fcc414c921007cf704c9213ffce704c921007cd704c9213ffcc704c9213ffce604c9213ffcc604c92140fcf504c9213ffce504c9213ffcc504c921407cf404c9213ffce404c9213ffcc404c92113fcf104c92113fc7104c92113fce104c92113fcc104c92104df4765452102ef4765452104cf47654521015f7755452101777755452100777655452102ef6655452102ef465545210df746554521005f77454521006f76454521006f564545213f77654545210df7454545210df7753545213ef755354521007e7725452104df6725452104df47254521007e47254521016f76254521017e762545210df7752545210077552545213efd732545213efe63254521007d532545213efe53254521007c53254521005f770545210df77505452104df47650521026f4765052104cf47650521005f77550521005f
  | 11 => 0x4edd2058f2104edc2058f2113edf1058f2113ede1058f2113edd1058f2113edc1058f2104fcf764cb2104dcf764cb2143ecf764cb21007cf754cb21437ce754cb21007cd754cb21437cc754cb2104fcf654cb2104fce654cb2104fcd654cb2104fcc654cb21007cf744cb2142fce744cb21007cd744cb2142fcc744cb2104fcf644cb2104fce644cb2104fcd644cb2104fcc644cb21437cf544cb2142fce544cb21007cd544cb2142fcc544cb2113fcf714cb2113fce714cb2113fcd714cb2113fcc714cb2113ecd614cb2113fcf514cb2113fce514cb2113fcd514cb2113fcc514cb2113fcf414cb2113fce414cb2113fcd414cb2113fcc414cb21007cf704cb21427ce704cb21007cd704cb21427cc704cb2104fcf604cb2104fce604cb2104fcd604cb2104fcc604cb21437cf504cb21427ce504cb21427cc504cb2142fcf404cb21427ce404cb21427cc404cb2113fcf104cb2113fce104cb2113fcc104cb21004ff755832102cfe755832102cfc7558321004ff7458321024fe7458321024fc7458321004ff735832101cfe7358321004fd735832101cfc7358321014fe725832100cfd7258321014fc725832104edf325832104eee325832104edd3258321006ed3258321006cd325832104ef6215832104ef5215832104efb70583210e6fa50583210e6fa405832104efb205832104ef820583210e6fa105832102cfe76d95210de7e65d9521024fe74d9521004fd74d9521024fc74d95210067e54d95210de7c54d9521004ff73d952101cfe73d9521004fd73d952101cfc73d9521014fd72d95210de7f52d9521006df32d952104cff71d952104cfd71d95211be7f51d95211be7d51d95211bef641d952100cfe70d9521004fd70d952100cfc70d95210de7c6559521005bf74595210d5bc745952141def72595211bcff75595210067f7559521004ff7459521006bf7459521004bf7459521024fe7459521024fc7459521006bc7459521024bc7459521004ff735952101cfe7359521004fd735952101cfc735952141cff7259521006ef7259521006df325952119cff7159521006f7715952119ef64159521004ff705952100cfe705952100cfc70595210de7f5059521024fe76d91210d6be64d912102cfe75d9121004fd75d912102cfc75d9121006bf54d91210d6bc54d9121004ff73d912101cfe73d9121004fd73d912101cfc73d9121014fd72d91210d6bf42d9121006df32d912104cff71d912104cfd71d912117ef651d912117ebf41d912117ebd41d912100cfe70d9121004fd70d912100cfc70d91210057f75591210dd7c75591210d6bc6459121415ef7259121004ff75591210067f75591210047f755912102cfe755912102cfc75591210067c755912102c7c755912117cff7459121006bf7459121004ff735912101cfe735
  | 12 => 0x46554541007b77454541025f67454541025f4745454112fb47454541016f76454541017b76454541117b7545454112f76545454112f74545454112fb4545454112f34545454111777535454144775535454112fb74354541447b54354541005f77254541006f7625454111777525454100775525454112fb74254541007b54254541447d73254541007d5325454111777505454112fb7405454100cfe76d8141106fa60d814102cfe75d8141004fd75d814102cfc75d8141014fd74d814100cfc74d8141006bf54d814133ebc54d8141004ff73d814101cfe73d8141004fd73d814101cfc73d814133ebf43d8141006bd43d814104cfe72d8141004fd72d814133ebf42d8141006bd42d8141006df32d8141006dd32d8141024fd71d8141256f621d8141106fa40d8141106fa10d8141005df735814110ddc7358141106f8605814104e7f7559721004ff7459721006bf7459721004bf7459721024fe7459721024fc7459721006bc7459721024bc74597210fe7f5459721004ff735972101cfe7359721004fd735972101cfc7359721014fe7259721014fc725972104e7e525972104e7c525972104edf325972104edd325972119e7f515972119e7d515972104ef6215972104ef52159721004ff705972100cfe705972100cfc70597210fe7f5059721004ff75593210067f75593210047f755932102cfe755932102cfc75593210067c755932102c7c755932104ebf74593210f6be5459321004ff735932101cfe7359321004fd735932101cfc7359321014fe7259321014fc725932104ebe425932104ebc425932104edf325932104edd325932115ebf415932115ebd415932104ef6215932104ef52159321004ff705932100cfe705932100cfc70593210f6bf4059321004ff765532104cfe7655321004fd765532104cfc765532102e7e65553210067d6555321026be6455321006bd64553210f73c54553211e6de6355321006df7558f21006de7558f21006dd7558f21006dc7558f21006df7458f21006de7458f21006dd7458f21006dc7458f21006df5458f21006de5458f21006dd5458f21006dc5458f2104edf7258f2104ede7258f2104edd7258f2104edc7258f2104edf5258f2104ede5258f2104edd5258f2104edc5258f2104edf4258f2104ede4258f2104edd4258f2104edc4258f2113edf7158f2113ede7158f2113edd7158f2113edc7158f2113edf5158f2113ede5158f2113edd5158f2113edc5158f2113edf4158f2113ede4158f2113edd4158f2113edc4158f2104edf2158f2104ede2158f2104edd2158f2104edc2158f21006df7058f21006de7058f21006dd7058f21006dc7058f21006df5058f21006de5058f21006dc5058f21006df4058f21006de4058f21006dc4058f2104edf2058f2104ecf2058f2104ede2058f21
  | 13 => 0x9541004ff73d954101cfe73d9541004fd73d954101cfc73d954104cfe72d9541004fd72d95411167c52d954148ebf42d9541006df32d9541024ff71d9541024fd71d954147e7f51d954147e7d51d954147ef621d954100cfe70d9541004fd70d954100cfc70d95411167f50d954102cff76595411167c6559541475bf745954112f3c5459541485f7715954147cff75595410067f7559541474ff7459541006bf7459541116bf545954112e7e545954112e7c545954112ebc545954112e3c5459541004ff735954101cfe7359541004fd735954101cfc7359541004ff725954104cfc72595411167f525954112ebf4259541006df32595411dcff7159541006f771595411def62159541004ff705954100cfe705954100cfc705954104cfe76d894102cfe75d8941004fd75d894102cfc75d8941014fd74d8941004ff73d894101cfe73d8941004fd73d894101cfc73d894146eee42d894146eed42d8941006df32d8941024fd71d8941416f651d8941416ef21d894100cfe70d8941004fd70d894100cfc70d894146ebf40d894110dde7398941005dd7398941006ef62989410d5f571989410057f75589411157c75589410f5f771589411157e75189410057d751894110dde7318941005dd731894104eee6218941006ed6218941105fa7018941005f97018941004fe7694941004fd769494104cfc76949410067f659494102e7c6594941025be7494941005bd74949411cf3c549494110dde7394941005dd7394941015f67194941005f57194941004ff7654941004fe7654941004fc765494102e7e65549410067d6554941005bf7454941025bc74549411173f5454941015f67154941015bc765094104ebc7650941014bc76509410073f7550941115be7550941115bc75509410073c75509411153c7550941006bf6550941006bd6550941465bf7350941465bd7350941025bf7250941027af7250941007af625094104ebe625094104ebc6250941007ac6250941007ae5250941007ad525094145f9f3250941007b77150941015be7150941015bc715094115fb47150941026bf6150941027b7615094115fb6515094115fb62150941005bf7050941006df764c941006de764c941006dd764c941006dc764c941006df654c94114ede654c941006dd654c94114edc654c9411479e744c9410079d744c94113edf644c9414579f544c9411479c544c94144ddf724c94110fcf724c941006df624c94104ede624c94104edc624c9411479f424c9410079d424c94113edf614c94113fd6514c941147d7414c94113f9e414c94113f9c414c94113fd4414c94113fd6214c941136de604c941136dc604c9411479f404c941025f4765454102ef47654541024f47654541015f7755454101777755454100777655454102ef6655454102ef465545411177
  | 14 => 0x4fd73d915101cfc73d915104cfe72d9151004fd72d91514be7f52d915112ebc42d9151006df32d915102cfd71d9151476bf41d9151476f621d915100cfe70d9151004fd70d915100cfc70d915112ebf40d915112ebc645915112f3c54591514b5f7715915104cfe76d8951014fd75d8951024fe74d8951004fd74d8951024fc74d8951004ff73d895101cfe73d8951004fd73d895101cfc73d89514aeee52d89514aeed52d8951006df32d895102cfd71d895141ef641d895141eef21d895100cfe70d8951004fd70d895100cfc70d89514ae7f50d8951125de7398951005dd7398951006ef62989510ddf57198951005bf745895112dbc74589510fdf7715895112dbe7418951005bd7418951125de7318951005dd731895104eee6218951006ed621895111dfa7018951005f970189510157c765495104e7c76549510147c76549510073f745495112d7e745495112d7c74549510073c745495112d3c74549510067f64549514a57f73549514a57d735495102d7f725495102f6f72549510076f625495104e7e625495104e7c62549510076c625495149f5f32549510077771549510157e71549510157c715495119f74715495102e7f615495102f77615495119f76415495119f7621549510057f7054951004fe7690951004fd769095104cfc769095102d7e75909510057d7590951006bf6490951026bc649095112f3c5490951125de7390951005dd73909510076d5290951015f67190951005f57190951004ff7650951004fe7650951004fc76509510057f755095102d7c7550951026be645095112f3e54509510076d5250951015f67150951006df764c951006de764c951006dd764c951006dc764c95114f5e754c9510075d754c95113edf654c951006df644c951146de644c951146dc644c9514975e544c95114f5c544c95144ddf724c951127cf724c951006df624c95104ede624c95104edc624c95114f5f524c9510075d524c95113edf614c95114fd7514c95113f5e514c95113f5c514c95113fd4514c95113fd6414c95113fd6214c951136de604c951136dc604c95114f5f504c95100cfe76d815111efa60d8151014fd75d815100cfc75d8151024fe74d8151004fd74d8151024fc74d81510067e54d815139e7c54d8151004ff73d815101cfe73d8151004fd73d815101cfc73d815139e7f53d81510067d53d815104cfe72d8151004fd72d815139e7f52d81510067d52d8151006df32d8151006dd32d815102cfd71d8151276f621d815111efa50d815111efa10d8151005df7358151125dc735815111ef8605815102cfe76d95411167e65d9541025be74d9541015bd74d95411173f54d95411dcfd75d9541014ff74d9541014fd74d954147ebd74d9541014bd74d954148e7f54d9541116bf54d954148e7d54d954148ebc54d
  | 15 => 0xc74549320079c74549321459c745493214f5f54549320075d545493204ddf725493204edf62549321a7cf625493214fcf525493204f5e525493204f5c525493204fcc525493204f4c525493204fce4254932005df715493213dde715493213ddc715493214f5f515493204fcf2154932005df7054932135de7054932135dc705493214f5f505493204fcf20549324d5df765093201dde7650932165dd765093201ddc7650932005df75509320075f75509320055f755093214dde7550932005dd755093214ddc75509320075c755093214d5c755093204ddf74509320079f64509321479c64509321479e54509320079d545093204ddf725093204edf6250932167cf625093204fce5250932007cd5250932147cf425093204f9e425093204f9c425093204fcc425093204f8c4250932005df715093213dde715093213ddc71509321479f415093204fcf2150932005df7050932135de7050932135dc70509321479f405093204fcf205093213dde76d853214dde75d8532005dd75d853214ddc75d8532145de74d8532005dd74d8532145dc74d85320efcf72d853204dde72d853201ddd72d85320eedf62d85320efcf62d853213ede61d853213fd661d853213edc61d853213fd621d8532135de70d8532005dd70d8532135dc70d8532007d610d853213fd410d8532005df755853214dde755853214ddc7558532005df7458532145de7458532145dc74585324cddf7258532007cf72585324cdcf72585320cedf62585320cfcf625853213ddf7158532007d7615853213ede615853213edc615853213fd4615853213ed46158532005df7058532007db7058532005db7058532135de7058532135dc7058532007d87058532135d8705853213fd71058532135de76d813214dde75d8132005dd75d813214ddc75d8132145de74d8132005dd74d8132145dc74d813207fcf72d813204dde72d813201ddd72d813207edf62d813207fcf62d813213dde71d8132005dd71d813213ddc71d8132006df61d8132006dd61d8132136de60d8132137da60d8132136dc60d8132137da20d8132007db10d8132137d810d8132005df755813214dde755813214ddc7558132005df7458132145de7458132145dc74581324c5df7258132007cf72581324c5cf725813205edf625813205fcf6258132005df7158132007d77158132005d7715813213dde715813213ddc7158132007d4715813213dd47158132006df6158132006dd6158132135df7058132007db6058132136de6058132136dc6058132137d86058132136d86058132137da1058132024fe76d915102d7e75d91510157d75d915112ebe64d915112f3e54d9151014fd75d91514767d75d91510147d75d915112e7e54d915112ebe54d91514bebd54d915112e7c54d9151004ff73d915101cfe73d9151
  | 16 => 0x8542006df32d854215ef641d854215ef621d854200cfe70d8542004fd70d854200cfc70d85420f6bf40d85420057f755854216d7c75585420067f65585420067c655854215ef4615854200cfe76d81420067f65d81420067c65d8142156fa60d814202cfe75d8142004fd75d814202cfc75d814204cfd74d8142004ff73d814201cfe73d8142004fd73d814201cfc73d8142024fd72d8142006df32d8142014fe71d8142004fd71d8142014fc71d8142086bf41d8142156fa40d8142156fa20d81420057f755814216d7c75581420067f65581420067c6558142156f860581424fdde76d953214ede65d953214f5e65d953214edc65d9532145de74d9532005dd74d9532145dc74d95320075e54d953214f5c54d953204dde72d953201ddd72d95321c6df62d95321c7cf62d953214f5f52d953213dde71d9532005dd71d953213ddc71d9532135de70d9532005dd70d9532135dc70d95321c5df75595320075f655953214ede655953214edc655953214f5c6559532005df74595320079f74595320059f7459532145de7459532145dc74595320079c74595321459c74595324dddf7259532007cf72595324ddcf72595321a6df62595321a7cf6259532005df715953213dde715953213ddc715953214f5f5159532005df7059532135de7059532135dc705953214f5f50595324f5de76d913214dde75d9132005dd75d913214ddc75d9132006df65d9132006dd65d9132146de64d91321479e64d9132146dc64d91320079f54d91321479c54d913204dde72d913201ddd72d9132186df62d9132187cf62d91321479f42d913213dde71d9132005dd71d913213ddc71d9132135de70d9132005dd70d9132135dc70d9132005df75591320075f75591320055f755913214dde755913214ddc75591320075c755913214d5c7559132006df6559132006dd6559132185df74591320079f6459132146de6459132146dc64591321479c64591324d5df7259132007cf72591324d5cf7259132166df6259132167cf6259132005df715913213dde715913213ddc71591321479f4159132005df7059132135de7059132135dc70591321479f4059132005df7655132005de7655132005dd7655132005dc76551324eddf75551324e5df745513214f9f54551321475e54551321475c54551321479c54551321471c5455132005df7255132007cf7255132005cf725513204dde725513204ddc7255132007cc725513204dcc72551321e6df62551321e7cf625513214f5f52551321479f4255132005df715513213dde715513213ddc7155132005df7055132135de7055132135dc70551324dddf765493201dde76549321a5dd765493201ddc765493204ddf75549320075f655493214f5c6554932005df74549320079f74549320059f7454932145de7454932145d
  | 17 => 0x1ce7f41d95421ce7e41d95421ce7d41d95421ce7c41d95420067f31d95420067e31d95420067d31d95420067c31d954252e7f21d95420067e21d954252e7c21d95420067f70d95420067e70d95420067d70d95420067c70d95421ce7f40d95421ce7e40d95421ce7d40d95421ce7c40d95420067f30d95420067e30d95420067d30d95420067c30d954252e7f20d95420067e20d954252e7c20d95420067f10d95420067e10d95420067c10d954216e7c6559542525ef72595421ccff75595420067f75595421acff7459542006bf745954218cbf7459542004ff735954201cfe7359542004fd735954201cfc7359542524ff7259542006ef7259542006df3259542004ff7159542014fe7159542014fc7159542004ff705954200cfe705954200cfc70595421cd7e761954216e7e76195421cc7e761954250f3e741954216f3d741954251e7f641954251e3f641954216f5e731954216f5d73195420067f63195420067e63195420067d63195420067c631954250f6d721954250e7f621954250f6f421954251f3e421954251f3c421954250f6c42195420075f321954216f76711954216f7571195420067e61195420067c611954250f3f411954216f7a701954216f7970195420067e60195420067c601954250f3f401954204dbc765514202ebc765514204cbc7655142025bf75551420273f75551420073f655514202ebe655514202ebc655514216f3c655514202e3c6555142007af725514204dbe725514204dbc7255142007ac7255142026bf6255142027af625514216f3f52551425179f3255142005bf7155142005bf705514250dee769494204eee76949421aded75949421cf6f659494202eee659494202eec659494216f6c659494202e6c659494204faf7494942025ee749494204dec749494204fac749494204eef649494204faf64949421cf6e54949421cfae54949421cf2e549494216fad54949421cf6c549494204fce739494204fcd73949421cfaf41949421cfaf409494202cff7654942024fe76549421acfd7654942024fc76549420067f655494202e7c6554942005bf7454942025bc74549420073d545494204f6c525494204fac4254942507cf3254942025ec765494202eec7654942024ec765494204def755494204f6f75549420076f655494202eee655494202eec655494216f6c6554942007af7454942025ee7454942025ec74549421afac745494204eef645494204faf64549421af6f54549421afae54549421af6d545494216fad54549420072d545494216f6f51549421afaf415494216f6f50549421afaf4054942014fe76d85420067f65d85420067c65d854215ef661d854202cfe75d8542004fd75d854202cfc75d854204cfd74d8542004ff73d854201cfe73d8542004fd73d854201cfc73d8542024fd72d
  | 18 => 0xe4158e42146dd4158e42146dc4158e4204edf2158e4204ede2158e4204edd2158e4204edc2158e42006df7058e42006de7058e42006dd7058e42006dc7058e42006df5058e42006de5058e42006dc5058e42146df4058e42146de4058e42146dd4058e42146dc4058e4204edf2058e4204ede2058e4204edd2058e4204edc2058e42006df1058e42006de1058e42006dc1058e4204def7654a42536ef7654a4204f6f7554a4204f6f6554a4202eee6554a4204eec6554a4204f6c6554a4218faf7454a42025ee7454a42025ec7454a421afac7454a42025ac7454a421af6f5454a4218faf5454a4218f2f5454a421af6d5454a421afac5454a4204fce6354a4204fcd6354a4218f6f5154a4218f6f5054a42004ff755864202cfe755864202cfc7558642006bf54586420d6bc5458642004ff735864201cfe7358642004fd735864201cfc735864204cfe725864204cfc725864204ebf425864204ebd425864204edf325864204edd325864204ef7715864217ef6515864217ef6415864204ef7215864204ef42158642004ff705864200cfe705864200cfc705864217ef71058642004ff755824202cfe755824202cfc7558242006bf5458242066bc5458242004ff735824201cfe7358242004fd735824201cfc735824204cfe725824204cfc725824204ebf425824204ebd425824204edf325824204edd3258242004ff7158242014fe7158242014fc715824204efb7058242176fa5058242176fa405824204efb205824204ef82058242176fa105824202cfe76d954216e7e65d954204cff74d954204cfd74d95421ce7f54d95421ce7d54d9542004ff73d954201cfe73d9542004fd73d954201cfc73d954216e7f53d95420067e53d95420067d53d954216e7c53d9542024fd72d954216e7f52d9542006df32d9542014fe71d9542004fd71d9542014fc71d954216e7f51d95420067e51d954216e7c51d954200cfe70d9542004fd70d954200cfc70d954216e7f50d95420067e50d954216e7c50d954250d7e76d954202c7e76d954252f3f74d95421cf3c74d95420067f63d95420067e63d95420067d63d95420067c63d95421cf6f72d95421cf6f42d954252f3e42d954252f3c42d95421cf6c42d95420075f32d95420067e61d95420067c61d95421cf3f41d95420067e60d95420067c60d95421cf3f40d954252e7f74d95421ce7e74d95421ce7d74d95421ce7c74d95420067f73d95420067e73d95420067d73d95420067c73d95421ce7f43d95421ce7e43d95421ce7d43d95421ce7c43d95421ce7f72d954252e7e72d95421ce7d72d954252e7c72d95421ce7f42d954252e7e42d954252e7c42d95420067f32d95420065f32d954252e7e32d95420067d32d954252e7c32d95420067f71d95420067e71d95420067d71d95420067c71d9542
  | 19 => 0x9152006bf30d9152006be30d9152006bd30d9152006bc30d915254ebf20d9152006be20d915254ebc20d9152006bf10d9152006be10d9152006bc10d91521aebc6459152545ef725915218dbe76191521aebe76191521af3e75191521af3d751915251ebf651915251e3f65191521af9e73191521af9d7319152006bf6319152006be6319152006bd6319152006bc63191521afad7219152526bf6219152537af521915251f3e521915251f3c5219152537ac52191520079f32191521afb671191521afb57119152006be6119152006bc61191525373f51191521afba70191521afb97019152006be6019152006bc60191525373f501915204d7c76551520267c765515204c7c765515202d7f745515202f3f74551520073f64551520267e64551520267c64551521af3c64551520263c64551520076f725515204d7e725515204d7c72551520076c725515202e7f625515202f6f62551521af3f425515253f5f32551520057f71551520057f7055152014fe76d8552006bf64d8552006bc64d855219ef661d855204cfd75d8552024fe74d8552004fd74d8552024fc74d8552004ff73d855201cfe73d8552004fd73d855201cfc73d855202cfd72d8552006df32d855219ef651d855219ef621d855200cfe70d8552004fd70d855200cfc70d85520fe7f50d8552005bf74585521adbc7458552006bf6458552006bc645855219ef4615855200cfe76d8152006bf64d8152006bc64d8152196fa60d815204cfd75d8152024fe74d8152004fd74d8152024fc74d8152004ff73d815201cfe73d8152004fd73d815201cfc73d815202cfd72d8152006df32d8152014fe71d8152004fd71d8152014fc71d815208e7f51d8152196fa50d8152196fa20d8152005bf74581521adbc7458152006bf6458152006bc6458152196f8605815204e7f755964218ebf74596421ae7f545964218ebf545964218e3f54596421ae7d54596421aebc5459642004ff735964201cfe7359642004fd735964201cfc735964204cfe725964204cfc725964204e7e525964204e7c525964204ebf425964204ebd425964204edf325964204edd3259642004ff7159642014fe7159642014fc715964218e7f5159642004ff705964200cfe705964200cfc705964218e7f5059642006df7558e42006de7558e42006dd7558e42006dc7558e42186df7458e42186de7458e42146dd7458e42186dc7458e42146df5458e42146de5458e42146dd5458e42146dc5458e4204edf7258e4204ede7258e4204edd7258e4204edc7258e4204edf5258e4204ede5258e4204edd5258e4204edc5258e4204edf4258e4204ede4258e4204edd4258e4204edc4258e42006df7158e42006de7158e42006dd7158e42006dc7158e42006df5158e42006de5158e42006dc5158e42146df4158e42146d
  | 20 => 0x14edf5158e5214ede5158e5214edd5158e5214edc5158e52006df4158e52006de4158e52006dc4158e5204edf2158e5204ede2158e5204edd2158e5204edc2158e52006df7058e52006de7058e52006dd7058e52006dc7058e5214edf5058e5214ede5058e5214edd5058e5214edc5058e52006df4058e52006de4058e52006dc4058e5204edf2058e5204ede2058e5204edd2058e5204edc2058e52006df1058e52006de1058e52006dc1058e52004ff7458652024fe7458652024fc74586520067e54586520de7c5458652004ff735865201cfe7358652004fd735865201cfc735865204cfe725865204cfc725865204e7f525865204e7d525865204edf325865204edd325865204ef771586521bef651586521bef6415865204ef7215865204ef42158652004ff705865200cfe705865200cfc70586521bef71058652004ff7458252024fe7458252024fc74582520067e545825206e7c5458252004ff735825201cfe7358252004fd735825201cfc735825204cfe725825204cfc725825204e7f525825204e7d525825204edf325825204edd3258252004ff7158252014fe7158252014fc715825204efb70582521b6fa50582521b6fa405825204efb205825204ef820582521b6fa1058252024fe76d91521aebe64d915204cfd75d91521aebe54d915218ebd54d9152004ff73d915201cfe73d9152004fd73d915201cfc73d91521aebf43d9152006be43d9152006bd43d91521aebc43d915202cfd72d91521aebf42d9152006df32d9152014fe71d9152004fd71d9152014fc71d91521aebf41d9152006be41d91521aebc41d915200cfe70d9152004fd70d915200cfc70d91521aebf40d9152006be40d91521aebc40d91521adbe76d9152024be76d915254f3f75d915218f3c75d9152006bf63d9152006be63d9152006bd63d9152006bc63d915218faf72d915218faf52d915254f3e52d915254f3c52d915218fac52d91520079f32d9152006be61d9152006bc61d915218f3f51d9152006be60d9152006bc60d915218f3f50d915254ebf75d91521aebe75d915218ebc75d9152006bf73d9152006be73d9152006bd73d9152006bc73d915218ebf53d915218ebe53d915218ebd53d915218ebc53d915218ebf72d915254ebe72d915218ebd72d915254ebc72d915218ebf52d915254ebe52d915254ebc52d9152006bf32d91520069f32d915254ebe32d9152006bd32d915254ebc32d9152006bf71d9152006be71d9152006bd71d9152006bc71d915218ebf51d915218ebe51d915218ebd51d915218ebc51d9152006bf31d9152006be31d9152006bd31d9152006bc31d915254ebf21d9152006be21d915254ebc21d9152006bf70d9152006be70d9152006bd70d9152006bc70d915218ebf50d915218ebe50d915218ebd50d915218ebc50d
  | 21 => 0xc000010003801000a000000000000a00400500240000070058018000005002800400200200000680060000020014000000000801000200000280300040090010000002005002800002e002000005c004004010801800200d000002c00200e001006401400200080000020010008008002011000800000a00200100080000000008000030017001001000800f000800400600d00080000000020000020010000002004c00400404cfe76d89545273c54d8954024fd75d895402cfd74d8954004ff73d895401cfe73d8954004fd73d895401cfc73d8954546ee52d8954526ee42d8954006df32d8954006ee32d8954006ed32d8954014fe71d8954004fd71d8954014fc71d895400cfe70d8954004fd70d895400cfc70d895452e7f659895454ebf64989541cf3c54989541e5de7398954005dd7398954006ef62989541af3c545895452e7f651895454ebf641895450f3c54189541e5de7318954005dd731895404eee6218954006ed62189541ddf67118954005f571189541d5fa7018954005f97018954014fe76d85544873c54d85541def661d8554024fd75d855402cfd74d85544b6bf54d85544867e54d85544867c54d8554486bc54d85544863c54d8554004ff73d855401cfe73d8554004fd73d855401cfc73d855404cfe72d8554004fd72d85544b67f52d8554486bf42d8554006df32d85541def651d85541def641d855400cfe70d8554004fd70d855400cfc70d855412f3c54585541def4615855400cfe76d815437f3c54d81541d6fa60d8154024fd75d815402cfd74d81543cebf54d815437e7e54d815437e7c54d815437ebc54d815437e3c54d8154004ff73d815401cfe73d8154004fd73d815401cfc73d815404cfe72d8154004fd72d81543ce7f52d815437ebf42d8154006df32d8154014fe71d8154004fd71d8154014fc71d81541d6fa50d81541d6fa40d81540bf3c54581541d6f8605815404ebf74592521ce7e54592521cebe54592521ce3e545925216ebd54592521ce7c5459252004ff735925201cfe7359252004fd735925201cfc735925204cfe725925204cfc725925204e7f525925204e7d525925204ebe425925204ebc425925204edf325925204edd3259252004ff7159252014fe7159252014fc71592521cebf4159252004ff705925200cfe705925200cfc70592521cebf40592521c6df7558e521c6de7558e5214edd7558e521c6dc7558e52006df7458e52006de7458e52006dd7458e52006dc7458e5214edf5458e5214ede5458e5214edd5458e5214edc5458e5204edf7258e5204ede7258e5204edd7258e5204edc7258e5204edf5258e5204ede5258e5204edd5258e5204edc5258e5204edf4258e5204ede4258e5204edd4258e5204edc4258e52006df7158e52006de7158e52006dd7158e52006dc7158e52
  | 22 => 0x1000c002000002800c000005003002c0000230000008002001000000402c00f006000c004003002804000e00100000000060000048000002007004803000200100100000120010000008008008000003400600000b800c002000000000000e00a002000000000b001802400c0050018008004004001004c000005000000000c00e000800000800100100000300000078000022002006000000e0040000034006008000003800201100d80000040000000008000008001800c0020050038008002002005804801200400000040300030030014000023006002806c005001000000a0040010004000003001003000401900000000000000040000004002002800003e00a00300000000510020000000002002002800c000007803800000e001000000000400a00040080020010004028000000000c0240030018000000000000000801e000000000400201c000003c000003001000800200000580680160010068008002009004000c012010000001c01200d0098000006000002803c00800000c004c00400700b000000a0030010000048004006000400a001000800c00600300180000140040098024012002000001c002000000000800201f002800c006000000801c000002000800c00000f00000040060000008000004003000007400000300000000000010000000016002000003001400100000780020010078000004000001001800c0000048008000000007804804e0000008000000000003001800e0100000000002040000000c008013004800800000200400080300080048030002005000003c0080000008008000002000000800202100100280040070028008014000002801c0080000000008016001001801800400000380000320010048028000000000002c002000002005402600000600000080010008008002000000004c002001003004400000400000100160040080010004007017800400200400180000020000010018004024002003c0260040000010000002000800000800000100100000030028000004014007800004400000d000c0240140000014004000000002c01400900400240000040000008032000000005400001d0040050002007001803802e001000003801a0000070018000002004000002a0000010024002007000001402c00a001001400800401d006401c000003001001e0010008038002003001000800000500700000100040018000002006004006400601a001000000a001002003c000000008800000a003001000c018000002005002a000002801000a00500e000c000000000802c00200e00080000000000118020000002000800401000b01900440080440000014000002006000c00e0050010034006015001000c002000005000001000000300080020000010000008006000000000000900a800
  | 23 => 0x313993b200708bae44f82a996ca36b06920005483024ebac2620117e4000096508920c54800054d80000005b10001d414307eb0000001beaa946b90000000132000000047a000746a1540000006980000e7c64a29831202464460af80000000006a480000000002e1a338cbc89d470242d3b61b25561328b907ac0f514656b65f73d5b634152afb00005340720000e100013a400000029144282af44900014c400066d2519002b932140000000bbf00018999ac00000000019c80c92de1564000cf93018000001002000001e01d0000014000001000800001c000005800c000000000000000e0000000000002001001000001a0080030018002003001800001000c000800001200200080000000230000000006011003800c0000070008048028000007800801000000180040040110008000016002003802803400200000580000140028000010000000800c00c000001801c0040070000028004001005804000a00500000040000000000008018006006006c014004000004400e0130038018006001000002c0000040000000002002000800004a01200080000180010000010004000005800401200001200140000000008000002005003800400400000c003c0060090008000030002001801c0260120000008004009000000000e01d00080040060060068004000004000802801600b00080000000050080000000001000000000c005000000402c0020100004002000000004400601300d000c01000a02a800000000000c0034002001001001401200200100480160010018014036004000000800800100000000060010120010008000004801c002043005801001c0040108028014004001803400c008000001800e00700780040060010000010000001005000800001e008802c00e005000800000400502c80200000060008000000007000000400201a01380000020000048004002010000000400201500f0004008000006803c000000000000800601f0020000000000000800401000d006001800200700c000c00000100080c801a001003801400400a002800c00200000c8000002000001001000000b000000001a0050098000010000000800000e000005001000e002001000800601600000000000000028158000001000800000200200200000120010058004010002000809000e0000008058000001000003800a00000100000060010000000000006007800800e0000018060000000000002c00000300100000120010000000002000000004801600600000140000010018024008001001000c010001000800000000000080000040000038008000001002000000c00a0008000000009008000000400d00080000000010000010002001000001000600400e00000260020008004004004003001403000a001001c00a001004000400200
  | 24 => 0x455f2799e1da3a00000032f11a446a00003a4312b5a0000a740000003de8ea878462752d0e605e49342c3ae35a4427b63d30ec0003391c6920835a0300770394bf68db4f7abe88d837400000000000000000001998ad32d1350543c3e83839ad40fac743042754a6ab7200028019144d6147000061257c321800087cc1006a1be00008c773821e4e7e0003ce1668ca800015d8a6c0009fa51c2430000b7e1902ea46de2fc297085d5c02c52bd1e04f7627661d0c7dc0894d3588001c5453415a909c4302f34110de8afa00015e95a043e94c36f0f74578ab55c32dbcca000a441a6cc02c65120c2e6d2ea0000001fb46045ca65586dd624d6d5ab8000f7e11f3e01e7cda4dc052805f8000d0149c80000006f705d90550f8a3c1231da5c260000af067c7d40000902a297a63d700038ec00000026400003a600034809a58f8e5112208913da9af734306886a71165aa204cdc3015eca7d80002f161f000000045e16a24a43aee64182adec00000058ba229bdcd7a00000018b400060925140e4e11000071c000863234b6e451e613465a89996c7d211834f8a8aa0364737c95a8be033a2538b2e2fd44e28d107470064eb9185c63ec38a8c215747d36840ad8b48ac800000004d4b900002be4000da700038fc0000004c99091b1c893287b8380007435278000000000000000000019c1fe80000000005ac262d8ba12935d89cc68023e262a59c0000000ad890115cc076cf947d8524c35362c555ec68c622a0358d800000020c48b60006260000000d871ec80016ce00000035d17908681898c10000bea00000000007040b40e7cd50909560000081c41c0002bc16906446b52e20000b7730f1430f2494f0000405b12daa45a00003726204a90e45b480006dea56941a2c86d18001862d5524f00006248b0616845172a16f0f2155d0c85e870b800178620d115800116ebec4440f9c3d200060b800081822d258b7440000000001a0126e4e354210f40b81be00028080005e313e800000070f7048430faaadd30c8774f446f3059ac941ec0aa366398876e000000083d7ca0005fe8000000ca50002e608ac58044f231446a0ae3300001a9400000025e52fc06e0002574f180002fc24ec0007c6350825d698d0f043800000005845b04147807a300000019726dc000000066201154f1b3800047b24304c181ed112af2fa525600000028ed2f40000cb8000ffece60002aa4e44902062140475832d3c0266db1600036a22815540b06bba49544abca3638000cc4b4700000005826762ac38780000002a71760ad6d694ec22d5964000685ab8c0004c0648a95911681b6b191bc000b9a25d8001c2a27c41e000097a0003ef233d9d61bd000040c0004e100000000000000003414ffc73c4b7a33568ca5c10b1ff000c00042106980000005f5865400063364
  | 25 => 0xec935200006fb0d46e022200018c19ce000000000160c0cd000346c00002b3b591b98ec61d38293700009e24651f30d7227e100149caa2ac50c60038c2c1164d2b64caf033e33e85686b6000205261c15e3924c037e0d540855c497e93280004a512614f44cd2a80000000d6250500000000006d5a2e800059e6a711f8100000362371552e7746a60000dd88a900001d000062b55d80007020004228d144ea658039a610670d263eb80004d83320189f1c00026f54e1134ec671e0002f388663170000001be800000000012068805201fcc05e73a72f1dd9b2a76014888ec0865f52271d280000004f422fc00000029325ad34c00053e92741101a157e201c67a97d11185dd23c4fb3af36280009984ca9a6c0006a300000000000000002798888b1400016b505e9323591bd923400036c1b29504ddf1da00002f85cc00030bc74c32c5eb39bc22400056513641705f05708000e5a5f34988704dd6c3827a2af98f2e3261c84e4302e8b6c2b564d1481210600000001020000000ffa0000002c05880c321a30fc80005615aca779918e235730358f5e761506043c69c27f00012549427510d7832986cb3464d1970aca43168fb3380ce140116028d96e000710271909207a00000010f000000034180000000b51b1400000000015d938e0007080000f2200000000014480003a689685384a4713af049289360000000030c61000278cace56f730aac000000026a94186be22800021f80009ff34f996800096436c9885b7c000335939c23c9e50000000fcc2a200029acc44000000279c0d27947128001a3800069e800019614e65191e0000000349b26ce1200050321100005d367186799f8382000000000075848926e4796000010999400000050822c506ee3922d302020c0000ae9e2d6c20002c9abe000027840eb830a2cd153f220ed368c33488202ca168e900000008d00001c305e400000000000014961f60fe2a8c2e4a630001014e3e0006b88000000000000000073c000109882c0000005b6800002e00022fa67c0007be00001642668952c780019c0000000183d9907382d1adb90581e5130a4157a040b67680000006e10000001144b54000115c00000000037bc22ab383dc0001b30db5000143800000000000017bebd44c4275c000c725fc0b1030a7a427000001b84b73b508fc2aa78949f80002fa59472aab898ea6cd6c12b1800082a0601201a080003ac8474b580000310ea4a408d65b2b04d07a5e263f814530210a7158240f9edd447d0db8bce54d00002b128070b1661e41bca0b103823fd9fc4f201f98bccf40003322d8c000000000336d7ee49220a0001390cb1503af8913425470ea310dc034b05680005c21830001a25ac2a13062a7acf6cab300012e4ba472901a188cd406252c880000006e4582aa6141c31a0f0291ca
  | 26 => 0xa66ba728b80010da0004040000d840000000000ec4a515c78001830809613838cac6000000000044e0001b9000124c1cd5b9a55102a0000b200009100003929edc2920000798ccd0f6cc92c10ae4b6e2574a8800123e96c0003140c5c54219115e473a0e812096616221c93209bbc78ccb811c0000e88c5e4129fd53a0be35d5344ce4002e26806c04548846eb82318dc0fe57601155420006798308a82e1a1908d316920bf6f104acf662ed68b84d801e00000000017e07bc23cb7200000000003035c9ec2304984b539675a3b8b3a8e543ad02f36880000003a30000788a9514c0fdd5487a62180e5400000000020b43e443a2128001050bcc33a8d0c29e78d1d0ba38b700000001c2050a1b831aac3c00000073880015d66111c290b164eac74758001b8c00000000012cabb400017b00384a5266315980c77322eb058becba60c32af441c61b00038f8b8456c702a11c0f8b9211095cc000d4820faef0000bcd71e80003fa2c766ca10d1cab9e0d1984069a00009605091f6b1b5ef10a8ad28d4502942183a3806170388eee0cf00012f96cc09819780009ec00049c0000462d7f3260d548940000001bf800017626f800103200002b09958f0b1f438b98d9deadc4c6034cc5a0fa67132911d052d2d2b8a02c40d91613214c023cf04a82d40008a535e3188b4ed6b051274d4743102082990a62be851937fd1bc00056692a10a84205429824efecfb5c296e4614e6d413ba040d6df06d080001ba5ed00000008766595d906615e82db00005ec0009b76dc008d384a934083208000000006287400000000037f0a42e7e000079da7222f64827a4a6c2b71cca880d1041d56d2eb0fce60069031b4186c2472119845c05b4000090c000e190000000bb2000075129800000000026f08703fe68f0001416acf3711624000000000183400095800035749f84cb251a87c9ca3546020cec9ba0001c5256c3f4b2038d27e17c20003b38e80ddad2d0001af54f24d154731814547e30280f21ab4047257227cb1819644899191302ff0001cdceb88d75dea86dc021110ef0a983524062d000016e8c9638db8d4e6c2b100025582d887627eb5a0000c37246b83cdaa24e3c11c4800000062f8001a1a5044429a380003cd0000fe0000bab0000001238c6b4b922f400000052e9e6849400014a8f2812800000000000002811f4a3099a24492f021b0d2c6c30000000d58a8900000000007ee144b8e94c29fe181b25469009e2d702105aab712bda14c0043f6583a9c008cdb023a34d07f88700a2b88992613e1a783bd39c0001c81e604b6ba807080740003b00000000fde83901d0000000a4628e992c0fe8292cb1fb16067937200bad3245543390000bd46854c499080000003268000b140003d485180243b151aac848c200035b0d61884d1a0000b0d14c2ef0
  | 27 => 0x29045eac895a7add4654e1b29481a80004da4541d480000000001ab8000e7700000014ec35763b84340003690002bd55440000000749988000386926c0008611958804e481ac5ff09343540633529744cfc3f05a92999432cbd42b3604000000000000000097300008f100499727f0000cda500646a16800000037aa0e000018f12e8a1d17000000036a1d0e5ba00000000001272f483d0000a1200018dd4d40006a3ab6cc6cc9e2333849800baf0f98a801020774840000fb877d39928101f22d170127a80002700ca23d8e0c0d000006cc25c6dd6a92f9c00084b223b8c0a5e5da46eb2003a066c6f624b8f5a02c029334c734d181aeaf1cfc25fc3679c29908af108813045d82d8744b78d89238c69c1e0d4fed6f50b800195200009892b1b0caed64a0600786b1828d268572886952500008100766c41ed007a96956c10e46ac34a31f8855994e03006a4d4cacd83329a30187e8c33c3081168470e4f9108d6d200010891f53e89820000000e7684148b27ec978000471059cd38588730179102e6691ad01100000000000ca5c0057e0001811aae0c818331c079c000000078c000b3730c00000001570003965cd200000030a12c21706e63551340b1a29117bc000000000308018ce14488ad89a8865f4abb128362d0c085b1385baa2e52409140002aa206b1353ba000546924c38cbf1552800111ed4d54780011e44485fe251c7988ad000027dab68e73a79d58df20000950fe41f6d3a5542fb4f4a53f34a0001ab80002d80001676000499915518c00062c00014e6ba06598f402dcbc2075b6440003c71ed0821aa24750002b4816ebb70002c2c0000d12e780011de00066e1a9db6273d08489dce28cf64522f457721a866f92fc0d86671d7000011c3e50f12a217ec9f10000001cd4e5457723a83f60006f480014507f80000001984e723423728000147596a5d013200000000001e0334000000000000042f9f3485a0002780acd28860c303182988880c1bcb73c5a62d253426413644de4bc23f04e827a02ea46006acc019201216d853c0001058bdc9fd1d380015ae000360354c2b200001b80011b2bad1b2a4e80007dd00039cc6c45752678a647a677c57913480004813b7a131aec61a40f257824c5bd341a2cd25e00072581312be0db4d10c351dc22638e391133a3152712c70a76000012ae8800068f3a383c5d06d2f31cb7080001876010000fb4c3446c0b78be20002eb274410cccf12980000000000002afce807f400000007921b402596ec0000002478000000d80016af3d7180000000c2c57e92349eb7f8000ccb3932cc000002417114b10304f80001b4ca22000378000000082e53a8001a80d3b1f09450ef696368111ad338e880001a6800078a0002e1daac2ea62a19c4e5e00012e394180200000000002445ab6d71190
  | 28 => 0x95d4e4874300c823088c0de198d11c5a16d6a954de89620c9870caee4d43b29360e5c74e7372c4ce8ad25605aa743e00ff31516d80160006ee81f938649751686d40000005148a480001dc0000745214ac42a630c179200000023dc000a83000035c49800041f3974112d675a0964138a5382c5b9fd61881111b80016f0d793790001baa93c0002175c1685c0001dc8d66a6e65f0e705ee00066f26180001847332ca9ab080327c80015780003b3000000000071680000000002838001ac830f245af000004763648ae849e00000037e80008344391ca1b2000058ca948bcc31b16ca20947c8e44660000012000740000072ca6f000108818e00000023b501e00058f2770fd063144c9270000000000000096aa714f088d8000ce10b0800cd56000500b10c4361563e81fd83900de4fe0000000d2768180000000000000001ca400000015fc000000632026c00078e1dd312cc0e4360a0800058000003a957434800067bb7117f60001ac8000ca431e6f4366c5d00000001fc8a38e37000000083cda00000ebd3e010810d092556e59214b0355cb4d7043f8001bfa00003cb314fca16d39a1c74ccc2821dc03c86a03d420221f431489b5ae2189cb86bf428a3f4f542ab45e3205a540001800c50000bd504d073c000ca70001a2ce7214b33826c153485e3963031c30a6022a000150c25f3a9858d76a0b618e006c33a1713cf12459aa4aa1fa0000c7896864387dd8424c95a9aad95b2db66f0297d39ad123ca9f513be1ef6442b3898467847c1cccf8aa816ec1e14274c664d203b5518b826e59955aeaac25eeb3b1bb80a16b000011be0000002d2c00083f00019743207ca0000e885d27350d5a258000df928c0da8f2e7b900000000008946d48ca00003883bc80007b600041599cc00000000006e9bd43874aa923955ab4a661a341cb60001f00000534e4c0000001a50d00374b57d770c7e6de136c0004500000f5555c50563eaa1c8ca8b90000b343d03a437d934c07600000019dc26800000000000006a600000000000d87130a840000130fa80000002f01339fe80007a85a180000003842ad80000001d90000b2859c01505401680002334c180010ea000103b7dd54035c00025fc68835e402863841228a00001ec3ac6be3cc9c4000000059f00000004110001abcd040005f9a6155169e4000000000059f2c1800000000029b8001a56cc70000000000000000000132ccbf00000000001e10000001774da60002c40ef400000025243be97636d2b900000003bf1a613346db000000000000030a000000017f00000000000000000000000000000250dc62afd0000000a944ce4352ac598c74b1f990d0cd450a62907b9a6464e1b6a9b42346fd6cd32bc0001ce0ed86480000000000bd1cf421d000000053e2633d38000a20c3d73c8f88776d36
  | 29 => 0xb5ee203800047066c1d5078a6e85cb800036c0e66458041356a145d0800174a0002e232614720005d1a854000a376eb015188cbc507e07100020000cdafb93700000000000440aa60000000bd60004fbb9ec0007f96fd800031ad6e000320c0000001d9b6702324e941190fd6523a55d819e455260b06718b1376407722b064b7ec0e70313b80000000000000000000364000000000068826b03f2b9c000000086ea2b28d8eac0000001de966c0000000003a0800000054f8000000d7c08e000066e0000a980013c0ad5703800000078f00039f13924900b488090ee0fd378a4b5bda2905c219fd3f2d502cc80006f83780001638000bef4558a5d258e5800033c434444342925a857c0ab48e9fa85fcb64000350d836cad59e8a0d52cd351b1aba4316e415b5817d1828fe4762565cae1fe38b2c094bcd0a21799ecd6053217c1db85b83d800000018d0b6000033e15fc45937e00004e2a784590000000749000000000000056b28bc0009f52e0000013ab3552bba29b1e00057980019fa75f4ed288c43200003400000009910000fd45dcbf95bd00011e80421368be82b01254c71be8f64175191ab9414896e17b00000000000cd00000000006b600016be3ff03095984b23470003458d820002922e7c35ccf45802e2da8c5cd58498c8000dc9000000000000000000f0000000172b6ecd0c5473ec154d7a4e8525819a000000048310005648e663da29cdacb70337800000042b1b2225d656c151560f99accbf468a18a0d3c9bd0002c1000055a25681b56ac0000000001bec0000000001a467781b080004a4000000000131a971000389164c0003a60000c52000616392915400002987510cc00069207680008241f8b3b9c9cbdb6bf0491c140552ce8000000d4500012680000004e01b7d6f86d16e19d54c7c00069b9714fa2000000000000000043a000180a000000000117c8133808000000000276953cd8c46700000016584525f900010dc00000024f91aa0190000000c7a90e34b9f6c41469526bb2d0832bcb12b2c3840c84060e2e28b5ea4d07209989d43686e8117120ec5123112580003b91a9800000044017d9131586d2e0a1b7cd57200000035edc6c4ec560800059e10400029640441d53fdb078836a8014333fd6ec4c700031040008f03489ae878268153bb6d115e9ad3681fc5748800262290c0002680000cb86ec1540000945b661740530fbc6fe0000001180e605c700000018d21f873a0000000dc10000001822cae2e4aec539e09100013c400000040b00000009210001c600007130000a8cfac07820904392e08f564f800144e0005bf800176600027b900c198bff0000a2040a44b0002c2195828066682090b238e000090800038924c88c9814b283d82c8cf905152c311142a2df1742371d6bc9c10cc97519e01501bf0c3
  | 30 => 0x28685480667ae1ee0cd54e8ca84800000182ddb0000000000c53002a38c908c670000000000e2c1538000bc27193b6a9ec2c03b60500349d18d6527d21cd0b613b5a70000ac45723b6069420e71734e880c6cc2b864c8a2d41206500400005606a26bc2fd48e4000000305000000009b8001a42db716b00011e64b2026a938ec89b52f2a2edbc226243387ac54a6120a62710d6856a5a69ed54fc04947c86441684534183298a500006a10000000e1f3d00001b4a0000fa2e0cf62a5821e2eb923673101334650ca0004a08294eb6cb00000001b3a00028f0ef800058548092d95bebc61928840dce0000001dd47a4e3809e80000006342a300006d84b80000b249661662b69160000e0825a175d8e28a12502508f08a16637ab4104c0002740e0cdaea5b06d0000000e5f11d38f12b800000017546ce5fe1d1b65c0009a3139000000054032b892cdc60003e20000aaa5ce000232400039700003e000094b3ec8001314b445be800108c5de3f803818060003ce9c080002a837f98393dccd0000105ca125db253a83d094deb55c17051a21ff6af10a55bc5c63dd13fc93e63b1be99f1664d8c35b800004000000000005ce0000003164c7000005d1f8185452b32d903d2489ae2ae00012cc39b000315c726000000294c76a2600f6000025006f18c0a79c5e84f047b6e85a08486c21d209d6e1600022400347cb239aa4822647c114800090a00007a96557cc0f75920000e420001d42c3506a4e45fd0f8c45c26e2d9a38521a0002fe9815444b31510904c000cc11e8af900002e640a00000004ab10f1005788c7300016a9ba4b3c2ee01900000004bb9d5c64ee6b51800000000bd000299503ee530002cb90147030a20000d0e0002a49a9000058d020269c00078840d00000000041a892a4c480001321670622e21557800066ca3f64900001ce31648796046e68204cf000126000013ca8c4684dce50e02e4a74699123800100c0001f2071400063a632a4105be00064e12880004511de0a300002ae00000000000575212bfc0000000bc0001b2ca544be00008fe0000001c9c394cdd5a80000ae800059980d8b6a0661b5813c000db273b118c164dda0f88000d520001bb8000be8daf67485e9c8e5a6000010413838b1358cfc000e0d674000000094829c94a8a7c2c60000001a780000001ba96a288d000000124013f0001e859429992a1a75187800058b08e47acab259f800089ed4b00014f4f2c0004e50d040000003efb18dcce0000003934e8203e4db05ac8122d76ec90685260005248000000c2b09c00000009ec00018540006923918a51c6884d5ed000152200030b88d1b32cd23e10c74000000000245d644dbf04500011b4c5b67a80009ea00000033e91b89f30491dc00000000000000000000000144d54e000430000000072
  | 31 => 0x4010b070c3fbb3508648d3090809c0000ec4d892bc0000380002bbc84c3fa53480005c80000001548000000623800055a0003e180000009ba565acd99406b81df8139b9a4212918001c5c25000015b8d1ab8e00000000005642ab2c740000004df00000540000002cbcf9cca22461520000b4055a3154912000236b4a51580000000000000a4408d800183eaab65d0be400000021700017b00000a4000009492a5160a352443ee6f398090de96d35682f184a5df00000000001e60000000728000443187c00013c1b000a546ca722c2000122600000032a923200000007300000006278001cd864709a9f884aa927322952cac04ba292a139190e651a90078508e7d373308825e3eb5cc829d46695366ba14176cb9d585299cb7c3190e588940007c9699b4c5bcce330c4069d77c8894eb01c549821c6bea1e9bc84770d0122898caf772485cda58c9715a2b456f208310929f0ddce755eba6fdcaccf24a80000bba000574022cfd2c5c6c917400004ef410a0cd0641d840e374c380d9e3200051ae600068486088e2b812d4a5ecb640001baa6a8a06bbb647b41c17c01f5cb0cf0000dde42bb39460eb6a73c2ce4000acc4b000a00001bf372993cae291459d00000c05f23248000f3647a28926a159230c41b0000ae04870000001a1c1ed0001d090080000ae28695ce6cb0000000000e1c30e09211463df16d00000003715aab1a8000b5d000172c00000071485291e225e5c0000088400000028f4a8800072185946f686b00032ec0009cc00000000002cb32424a0bfe2585041da011ab68000263c000000000110510ed4f02d800000033a00006eda7e3301f680007f6326000000071e0000002d140000000000f7922a0002d400
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xcd6211d9324400199a423b2648800336a00764c9100066cc00ec9922000ccf201d932440019b4403b2648800333480764c9100066d880ec9922000cd6101d932440019a8203b2648800336040764c91000668080ec9922028a9e84d95324400153b09b2a6488026b3a0b654c91000566c16ca99220008df8759532440011b90eb2a64880a697a17644c9100052ec2ec89922009ace82d91324400159b05b22648800237e1d644c9100046e43ac899220038dc87d8932440ff59b0d3126488003339da624c910006663b4c4992207fbc58198932440b17930131264882c3f0042624c9100046fc3ac499220038dc87589324400d3990eb126488026b3e19624c910006663b2c49922084bc78158932440c179700b1264882bff0041624c91000667c3ac49922003ace8758932440075990eb1264880033321d624c91001c6643ac49922084acf815893244001d8f02b1264881feb3e01624c91000765c02c49922026ad4865c532440019a8ecb8a64882baf1e09714c910135e8402e29922027ad8865c132440019b0ecb8264882b6f2e09704c91013de840ae09922000dd1715c1324400156b09b2a42880263d21d65485100053ac2ec890a20098f487591214408b9a8edb1a4288117741c36348510005e2c18c490a2000ad4864c921440139a8ec992428809b741c132485103ffe11026490a2000ec7864c9214400178d0c9924288002f12193248510007624326490a2009ec7764c92144013d88ec9924288003b1d95324851000762b2a6490a2000ec7644c92144001d8ac899242881fff0a013248510007e0c026490a207ffc0704c9214404fd8ec0992428809ff0d81324851000cf943ee090a2000fc132dc1214400157309b2a40880263e21d65481100053cc2ec890220098f887591204408d9b0edb1a408811b741c76348110005e4c18c49022000ad8864c920440139b0ec992408809f741c532481102c7e110a649022000ecb864c920440017950c9924088002f2219324811000764432649022009ecb764c92044013d90ec9924088003b2d95324811000764b2a649022000ecb644c92044001d92c89924088163f0a053248110007e0c0a649022058fc0714c9204404dd96c2992408809bf0d853248110014f943ee29022000fc132dc520440033e10e90a4088006bc2192148110016783b2429022009ee0624852044155f866490a4088003f04c9214811000df043a429022002de08748520440033c10e90a4088006f8a19214811000df0432429022009ee0864852044013dc6ec90a408800b789d92148110016f03b2429022009ee0764852044001dc6ca90a4088003b8595214811000771b22429022000ee16448520441597c70690a40882b2f860d214811055ef1b9a4290220abde1734852044001f86c690a40882abf018d2148110
  | 1 => 0xb0e296c688002a7a1052d8d100054ec20a5b1a2046ad68114b63440015ab02296c688116b6a0052d8d100056cc00a5b1a20008de8710b63440011bb0e216c68800297a1442d8d100052ec2885b1a2046ad68110b63440015ab02216c688116b6a0042d8d100056cc0085b1a20008df835d762440071b906baec48800237e0d74d891001c6e41ae9b122000acd82dcf624400159b0439ec48800374041739891000566c10c731220b4ed01018e62440071bd0db9ac4881163721b7358910006e8086e6b1220008de87d8d62440011bd0e31ac4882d335dc4635891059e6db80c6b1220038de87dcd62440011ef02b9ac4880023ee0173589100046f438e6b122003ccc738c962440071d90e992c488003351cf715891000c7d43ee0b122000cd873dc16244001ae020ba8c4880036c041741891004e67312e63122000dd0105cc624400d1bb0fb18c488003179d763189100062ebaec63122000c9e74d8c624400193ae9b18c488002b360b63189100062f3a8c63122000c5d7518c624400193ce8318c488003275d0631891000566c10c63122047cd57118c62441659b2e0318c4882c7b4040631891000477c3ac43122000ccd7358862440071b9073b4a48800237e0d769491001c6e41aed29220008dc865ce5244001ba020b9ca48800237e1f63949100046ec3ec729220018f4865c652440033e100b8ca48800a3e2197094910014f840ae129220038de83dd952440011bb07bb2a4880122fa1276549100045ec24eca9220008bf845d9524400917908bb2a48800237e0d765491001c6e41aeca92200987c875955244001878e8b2aa4880269b20965549100064e31ee8a922000db010dd1524400193ee9b1aa488003271d3635491001c6e41ced21220008df835da42440071b906bb48488002372197390910006e8082e721220008df87d8e42440011bb0fb1c84880063d219719091000cf8402e321220028f8865c242440053e102b84848800e37a0f76509100046ec1eeca12200587e859d942440010fb0b3b284880021fe15765091002c3e42aeca1220008df835d942440071b906bb284880031718f7550910006b8086eaa1220098bc875914244001878eab228488026ab20964509100062fbaec6a122000c5c75d8d4244001da021bb2648800237a1a764c910006e8084ec9922000acd829d932440011bb053b264880033360a764c9100066790cec9922000ccd219d9324400199e413b2648800333482764c91000567c12ec9922000ad7815d932440015b700bb2648800374040764c91014d2f428ec9922000a5d851d9324405153d083b26488002a7610764c91000768080ec9922000c5e851d932440018bb0a3b2648800327a10764c9100064ec20ec9922000ccd821d932440019ad023b2648800335604764c91000667908ec9922000
  | 2 => 0x93254120006e5c3a64a824000dc8874c95048013b94ec992a090027721d932541202d7a542a64a824000f49854c9504804db96ea992a09009bd2dd53254120007a5b2a64a82405af48654c95048001b96e8992a0902f7d295132541202d7a42a264a82405af4b514c95048001b9265b8aa090003d24c95154120005e4c1e42a824000f6151485504800337309baa80900263e219755012029e9c2a2eaa024004aba84d954048179c70a9b2a80900123e21d6550120005e4c18e4a024000be1811c940480033710ea1280900272e1d9425012028d9c42a84a024009da87250940480139b0ec9928090167e2d093250120007c4a1264a024000dcb874c94048001b910e9928090027729d9325012004ee43b264a024000dcb754c94048001b92ea9928090167e2a113250120007c4c2264a024026dcb744c9404804df16e89928090003e2d9132501202cfc432264a0240bbf8b544c940480b3f10a89928090167e2d053250120006e4996e2a024000f893250540480017930790a8090003e85052150120006d8082e9b2a2000c9e7418f654400193ae831eca88002b360863d95105d768080c7b2a20048bf875d3654400196c42ba6ca880032e88174d95100245f426e7b2a20008bd84dcf654417393ce9996ca88003275d332d9510006e8086e6b2a2000acd8218d6544171da02031aca880028fa13755951001c6f43ee6b2a20008dd82dcd65440011bd0e39aca8800e1f21d53595100046f43e64b2a20038dc87cc96544001ae020baec888003179d463d91100062eba8c7b222000acd8218f644416fda02031ec8880161fe1d75d91100063b10aebb222000c7a205d7644400b0fd0bb9ec8880021f61773d91105b62f3ae65b222000c5d75ccb6444001ba021b9ac888002b360863591105af68080c6b222000a3e85dd164440071bd0fb9ac8880023760b73591100046f438e6b2220038bc8750d64440011bd0f992c88800e3721f32591100061e2a6ecaa220038de83dd954440011bb07bb2a8880021f61676551100045ec24ecaa22000c3c545d954440011bf06bb2a88800e3720d765511000477c12ecaa220098ec825d9544400153d09b2ec688002a761365d8d100046ec3ccbb1a20008df8759763440014bd0bb26c6880029761764d8d100046ec3cc9b1a20008df875936344001ba020b96c688002a7a1375d8d100054ec26ebb1a2000a5e85dd363440014bb0bba6c68800237a1c54d8d100046ec38a9b1a2000e1d54153634400159d042a6c688002b360854d8d102356b408a9b1a2000ad581153634408b5b5002a6c688002b660054d8d1000667b94e5b1a2000a5e851cb63440014bb0a396c688002a7a1072d8d100054ec20e5b1a2046ad6811cb634408b5ab02396c688116b6a0072d8d102356cc00e5b1a20008de8714b63440011b
  | 3 => 0x690e4009ccf7158d21c8013d8ee2b1a4390003b194563487200076320ac690e407fec71058d21c80ffd8a20b1a4390003b158d514872000762b1a8290e4000c3d7495365480014f3012a6ca900122fa1f74595200061fba8e8b2a40008bf845cd654800917908b9aca900023de0573595200147a40ae6b2a4000c9f74cc96548173938e9992ca900030f5d754d91200055cc06a9b22400587e87dd56448001878ebba2c8900021fe15735912002c3e42ae6b2240008f7815cd64480051e902b9ac89000317dd732591205b62e3ae64b224000c3c549d954480010ff0abb2a8900022fe1176551200061e2a0ecaa24000c3c74d955248001878ebb22849009ab360b654c9200054fc22ca9924028a9c84595324804d59b05b22649000297e15644c92014d2e42ac89924026acc865493248053c98caa926490002e3e11524c9202cdc6422a49924026acc86509324800169f0aa12649016ad3215424c92014746322849924009ada86dc1324804d79101baa6490002b3e19754c92013566432ea9924000b8f845d532480b371908baa6490002f2e01754c920135e4402ea99240c0e4c65595324800171f08b2a6490166e3211654c920005e5c02ca9924026bc880dd1324800159f0cba2649009ab3219744c920005a7c2ae8992405ab4c855d1324800179700ba2649009af2201744c920005a7c2ac8992405ab4c85591324817fd18c8b226490002f2e01644c92000567c32a89924000acc8655132480b3e18a8aa2649009af2a01544c920135e4406e29924000fc210dc5324800159f0cb8a649009ab3219714c9202c6e238ae29924000bcb805c5324804d79100b8a649009af2a1f704c920136e543ee09924009bca86dc132480137910db82649009b729db704c920136e43b6e09924000bc985dc1324800179309b826490002f2607704c920006e5b8ee09924000dc971dc1324800117f08baec2900122f21175d85200043fc2ae9b0a400587c855d3614804d99ae4996c290027331c932d852001e6739a65b0a4058ec4314cb614810f99f0e996c2900773321d32d852000763c0a65b0a4058ec4814cb614801399ae0996c290213b1c4132d85200076299663b0a400b9cc874c961480050f90eb2aa2900968f2116554520136e538264a8a40028bc8759141480454790ab22829009b729c13250520006e5c02e790a4000dc8805cf214801399ec0b9e429002772d8173c8520006e5282e790a4000dca405cf21480b1b9420b9e42901637244173c8520136663b26490a4000ec532d852148001b9265b8242900065e617745412002d3d42ec8a8240bee3854d91504800b1f10eb22a090002f260c7254120005f0c08e4a8240019788754950480138f0eca92a09014ece211525412004eb4392a4a824009cd8764c950480b5e96a4992a090003d254
  | 4 => 0x25000159f04bb264a0002b5e05764c94013d6a40aec9928026a9d84d953250187c38a8b2a64a0002b3e09654c94004d66412ca9928026a9c865d132500d36390aba264a030ae3e09744c94004d4e432849928069b1c855093250013d18c4a1264a000a2f21175d85400061e2a2ebb0a80048f980dcf61500014790aa16c2a000a1fa1f655454000c5f436e8a8a8026c9c764c941500093690ea8a82a008b8d19551505400043fc2aed90a800587c855db21500031790cba642a00524f21574c854004c7c432e190a8000dc9325c321500031790cba242a00524f215744854013f6330a6490a8000f853250521501836750bba2a0a005ece21152541400a59c42a84a828000f295250950500519b0ec992a0a01d7c6151325414002e3c3b2a2a828017b38845455050009970eca0aa0a0052ce215415414000798a8a82a8280048be87dd165c815393e65ba2cb902a7274cb745972054e5d106e8b2e40a9cb920dd165c814787eea3a2cb900022fe1173597200245e422e6b2e400587e87dd564c814b8be65baac990297174cb755932052e3d106eab2640a5c7920dd564c814787ee83aac9900021fe15735932002c3e42ae6b2640a587f855d954c815317f08bb2a9900261f21d65553200251e422caaa640098bc8759154c800b4790ab22a990002a7e117558f200054e422eab1e4000a5f855d163c80014b90aba2c79000237a1c5458f200046ec38a8b1e4000e1d5415163c801359d042a2c790002b36085458f200056b408a8b1e4000ad58115163c804d5b5002a2c790002b66005458f2004d67414e2b1e405eacd829c563c80015b700b8ac79009ab62017158f200052f428e2b1e4000a5d851c563c800153d0838ac790002a76107158f2004d67410e2b1e400facd821c563c80019aae238ac79009ab6a007158f200056cc00e2b1e4000a9e8494563c800153b0928ac790026b3a0a5158f2000566c14a2b1e4009ace8214563c800159b0428ac79000297a164158f200052ec2c82b1e4009ace8290563c800159b0520ac790026b3a084158f2000566c1082b1e4000acf865d532c800171f08baa6590186e3211754cb2000567c32e89964000b4f855d132c80c56990aba26590002b3e19544cb2004d66432a89964061f0c5455132c800159f0cb8a6590183711c5714cb20005e5c02e29964026bc8805c532c800799ce6992c39000333e1d32587203066643a64b0e4000ec7814c961c80c1d8902992c390027b1dc532587203076328a64b0e4060ec6414c961c80ffd8e20992c3900022fe1176547200245e422eca8e400287c8759551c804b47908b2aa3900263d21d615472000762992c2a8e400087f855d941c800b0f90abb2839000a2f21d64507201151e42ac8a0e40098f48758541c8001d8a64b0a8390003b1e0563487200076240ac
  | 5 => 0x80a6d613755052104c7a432eaa0a427ed34545d5414840956d09b2a8290b238d15365505210247a43acaa0a4200bc5831c941484017c300392829080a6d21d425052104e5a3b284a0a427cb34855094148413b48e4a128290827351d93250521407c3a1264a0a4200f85424c94148401b8f0e99282908037121d325052104ee33b264a0a4209dc4764c94148401b8eea9928290803715d53250521407c342264a0a4200f85844c9414844fb8ee8992829089fe1dd13250521007c3b2264a0a4280f84644c9414858ff0ea89928290a03e11513250521407c3a0264a0a4200dc532dc1414840117f08baec0908122f21175d81210043fc2ae9b02420587c855d3604844f99ae4996c090827331c932d812101e6739a65b02427fec8304cb60484c799f0e996c09083f3321d32d812104e66b8a65b024200ecb804cb60484ffd9100996c0909ffb284132d81210076499661b0242199cc874c960484030fb0bb9ec8a8107175d732d91500046fc1ae3b12a0038dc835c762540011df0eb10c4a805e4fa1f745495054e1e3b6e8a92a0a3c3f761d15254147878ec3a2a4a828e1fa1f64549500be1e3a6c8a92a000b2d841895254001a70e9b82a4a80061f21975909500061ebaec9212a017b2c8454a4254001c5ec8a9484a80263e21970909505f69c2a2e1212a00587c851d9425400187ca83b284a80061fa1b755095002cb643aa4a12a000acd829d9325400153f08bb264a80a2a7211764c95000567c12ec992a000ad7815d9325404f5a902bb264a809a97219754c9503ad8e422ea992a0c6b4f825d5325404d4bb0bb2264a802697219524c9503ad8e422a4992a009e4c6254932540050f90aba6c2a80030f15174d855002c7cc06e7b0aa000a3c8454b615404d8b8ec992a2a80061fa1b75505500145f43ec8a0aa00597487545415404bc68c8a8a82a80022fe1176c85500245e422ed90aa00187c865d7215402f27908bae42a80263e21970c8550006e4992e190aa00187c865d5215402f27908baa42a809fb19853248550007a2992a290aa0018bd84dcf655008393ae9996caa005e8fa17745954062f0e2a664b2a8000c3c54dc56550189c70a9b82caa000237e0d71d894001c6e41ae3b1280008ef8758862500031790cba4a4a00030fd95749494004c7c432e129280bcd38545c25250009179083b2a4a00030fd50765494004c3e43acaa928017c3c74595525000317d0dba2a4a00066ea03745494050c9f43eeaa1280a5c3c76dd54250001a70e1baa84a028f0fdd8755094051e1e3b0eaa1280a38be87d954250029878ebb2a84a00262f21d65509400a61e3aacaa128000b2d851894250029a58eb29284a00038bd965250940024d643aa4a128000e2d655494250001a70ebb8284a0002b360a764c9400052fc2aec9928029a5c855d93
  | 6 => 0x52ec2c80b1e4209ace8290163c840159b05202c790826b3a084058f2100566c1080b1e4200acf865d532c840171f08baa6590a16e3211754cb2100567c32e89964200b4f855d132c850d6990aba26590802b3e19544cb2104d66432a89964285f0c5455132c840159f0cb826590802f1e05704cb2113de240ae09964284dc8705c132c840799ce6992c19080333e1d32583214266643a64b064200ecb804c960c8509d9100992c190827b2dc132583214276528264b064284eca404c960c8509d9420992c1908030f5d254d95210053ac0ca9b2a42048be87dd1654840187eea3a2ca908022fe1173595210245e422e6b2a42008fb805cd65484031f100b9aca9080327dd332595215ce4e3a664b2a4200c3d75d53644840156b03aa6c8908161fa1f75591210061e3aee8b22420087f855cd644840b0f90ab9ac8908023ee01735912100c7c402e6b224200c5f75cc9644856d8b8eb992c8908030f15276551210043fc2aecaa242008bf845d95448401878a83b2a8908030f1d365549210061e3aec8a124227acd82d95324840153f08b2a64908a2a7211654c92113d66c16c89924200a5f8559132484534b90ab22649089eb3219524c92114f2632aa49924200b8f84549324850171908a92649089eb3219424c921005a7c2a849924281b4c855093248451d18c8a12649089ef1207754c92100567c32ea9924227acc865d5324840171f08baa6490a02e3211754c921005e3c0aea9924227bc4815d53248599c98cab2a6490802e3e11654c921405c6422ca9924200bc781595324844f78903ba26490802b3e19744c92113d66432e89924200b4f855d132485036990aba26490802f1e05744c92113de240ae89924200b4f8559132485036990ab226490b2fa3191644c921005e3c0ac89924200acf8655132484015990caa26490a03c3151544c92113de340aa89924227bc687dc5324844fb8d0fb8a6490826f1a1b714c92104de2436e29924227dc676dc5324844fb88edb8a6490802f1617714c921005e2c26e29924200bc580dc5324844f78903b82649080371dc7704c921007e1886e09924200acf865c1324844f5990cb826490802f1e05704c92113de240ae09924200dc7715c132484ffb90e0b82649080a5d617745452102d3b42ec8a8a42cae3454d91514840b1e90eb22a290802f160c7254521005f0c00e4a8a42029748754951484138e8eca92a2909facd211525452104eb2392a4a8a4209cd4764c95148503e8ea4992a290803d15493254521006e3c3a64a8a4200dc4874c95148413b8cec992a290827711d9325452140fa342a64a8a4200f45854c9514844fb8eea992a29089fd1dd53254521007a3b2a64a8a4281f44654c95148401b8ee8992a290b27d1951325452140fa22a264a8a4281f47504c95148401b8a65b82a29
  | 7 => 0x2c8454a4254401c5ec8a9484a88263d21971909516569a2a2e3212a200c3e541d942544050fd0dbaa84a880a5da07755095102cb643aa4a12a200acd829d9325440153f08bb264a88a2a7211764c95100567c12ec992a200adb805d9325444d5b100bb264a889e97219754c9514958e422ea992a2d2b4f825d5325444f4bb0bb2264a882697219524c9514958e422a4992a209e4c6254932544030f90aba6c0a88030f15174d815102c7ac0ee7b02a200a3c8454b605440517b09b9ecaa0a27275d332d954112d1f42ee8b2a82d1e1c54cc965505a1c68a9b8acaa08030f15370595410046fc1ae1b1282038dc835c362504011df0eb10c4a080a2f21974949410061fb2ae929282098f4865c65250591a68a8b8ca4a08030fd50765494104c3e43acaa928225c3c74595525040517d0dba2a4a080a6da07745494150c9f43eeaa1282a5c3c76dd54250401a68e3baa84a0a8f0fdd8755094151e1e3b0eaa1282a38be87d954250445878ebb2a84a08262f21d65509411161e3aacaa128200b2d851894250445a58eb29284a08038bd965250941024d643aa4a128200e2d655494250401a68ebb8a84a0802b360a764c9410052fc2aec9928229a5c855d9325040159f04bb264a0802b6e01764c9411356c402ec9928227a9d84d95325059fc38a8b2a64a0802b3e09654c94104d66412ca9928227a9c865d132505156390aba264a0b3ae3e09744c94104d4e43284992828ab1c855093250413d18c4a1264a0b36cda17745454112d9a422a4a8a8222b34855095150401e4aa4a12a2a08a3351d932545414978a2a264a8a82018bc845d76050401878a8baec0a08123d60773d81410051e42a85b0282048be87dd165c855393e65ba2cb90aa7274cb745972154e5b10ee8b2e42a9cb521dd165c854787eea3a2cb908022fe1173597210245e422e6b2e420587e87dd564c854b8be65baac990a97174cb755932152e3b10eeab2642a5c7521dd564c854787ee83aac9908021fe15735932102c3e42ae6b2642a587f855d954c855317f08bb2a9908261f21d65553210251e422caaa642098bc8759154c840b4790ab22a990802a7e117558f210054e422eab1e4200a5f855d163c84014b90aba2c79080237a1c5458f210046ec38a8b1e4200e1d5415163c841359d042a2c790802b36085458f2113d6b408a8b1e4200ad58115163c84015b5002a2c790802b66005458f2104d67414e0b1e4256acd829c163c84015af02b82c79089eb52057058f210052f428e0b1e4200a5d851c163c840153d08382c790802a76107058f2104d67410e0b1e421dacd821c163c844f5ad02382c790802b56047058f210066cb80e0b1e4200a9e8494163c840153b09282c790826b3a0a5058f2100566c14a0b1e4209ace8214163c840159b04282c79080297a164058f210
  | 8 => 0xebb22c89900353dd77259132006a63aee4b2264dcd8f74dc9644c80139b05bb2a899003471527655132004afc2aecaa2640099f845d9544c80139f04bb2a89900347150765513204ce743ee4aa264dbf0c54dc9544c80739d0db92a89900e7321b7255132004e6c0ee4aa264009cd80dc9544c94ba9eea392a8992a763dd072551326bf862a0e4aa26400bc5811c9544c80179300392a89936b4715371551326ce8e2a6e0aa26400d1c74d95524c81369d05b2aa49928e67a1f745493254f86296e8a9264a9c9f62dd1524c801b1ec5ba2a4992a763c87745493254ec7906e8a9264a3d1f751d1524c9b1b1ee43a2a49928fc3148745493204cae43aa8a926428d1c74551524c81369904aa2a49928e57a1f755093252f86216eaa1264a5c5f62dd5424c801a9ec5baa849929753c87755093252ea7906eaa1264a999f845d5424c9b139f04baa849929657a1c755093251e8fba0eaa1264d7d4f721d5424c947e18843aa8499003471d7645093204dc7416c8a12640999c87551424c853a38eaaa28499026e32095450932144e643aa4a126429d4c75549424c85171908a928499003c35515250932004cfc22ebb0a642899c845d7614c93739f04baec2990267320975d8532004afc2ae9b0a642995c855d3614c93539f04ba6c2990267320974d85324c4e7c12e1b0a64099cc825c3614c80178b05086c29935bb1187725853213d6b436c2b0a64d5dc772d85614c84d3b50fb82c29900372dcb70585320076830ee0b0a6400dcb82dc1614c8019b6c5b82c29900372d8b7058532006e590ee0b0a6400dc921dc1614c8019b6ec382c29900372dc87058532006e9b88e0b0a6400ed0611c1614c80133f08baec0990a26721175d81324dce7c12ebb0264099cc825d7604c8012bf0aba6c0990a65721574d81324d4e7c12e9b0264099cc825d3604c93339f04b8ec0990267320971d81321346ec3ec3b026400ed010d87604c8011bf0eb0ec09909f351c561d81321356c402c3b026400bc982c43604c801da2c3886c099353b2183725813213ceb43ee2b026400dc772dc5604c801da0c1b8ac09900371e0b71581320066bb16e2b026400dc762dc5604c801b8e41b8ac0990037148371581320066bbb0e2b026400dc7721c5604c801da0c038ac09900237a1f615813213e6a38ec2b026426ad880d85604c801da421b0ac09909a3721d615813213e6a38ac2b026426ad880585604c84d5b50db02c09934f72dcb6058132006e838ec0b02640287d85dcf64545138baeb996c8a880237e0d70d895101c6e41ae1b12a2008ef87588625444b27d0fba2a4a8aa70f1db74549510069a38ee8a92a2a3c3f761d15254547878ec3a2a4a8a8e1fa1f645495112e1e3a6c8a92a200b2d841895254401a68e9b8aa4a880a1f21975909510061ebaec9212a225b
  | 9 => 0x7158e420056c402e2b1c8400a5e851c563908014bb0a38ac7210c2a7a107158e420054ec20e2b1c8409ace821c5639086159b0438ac721003355c47158e420056d400e2b1c8400ad9801c5639085153d0928ac721002a76125158e4204d67410a2b1c8400acd8214563908015af02b82c721002b52057058e420052f428e0b1c8400a5d851c1639086153d08382c721002a76107058e4204d67410e0b1c8430acd821c163908015ad02382c721002b56047058e420066cb80e0b1c8428a9e84941639080153b09282c721026b3a085058e4200566c10a0b1c84008de8704163908011bb0e082c72100297a141058e420052ec2820b1c8428a9e84041639080153b08082c721026b3a081058e4200566c1020b1c8400c3c54dd561908011f700b9ac3210063e20173586420061e2a6eab0484008f7815cd60908051e902b9ac12100e1fe1d53d95420051ec24a3b2a8400a3d8494365509478bced996caa10031ddc671d95421cd1f420e3b2a84a5a3d841c765508010fd0e18ecaa10021f61c31d95421cd1f42063b2a8400a3d840c7655094b4dd0418ecaa10029b60831d95420053d40063b2a8400a79800c7655087347d08386caa12968f61070d95420043f43861b2a840087d870c3655087347d08186caa10028f61030d954252d3741061b2a8400a6d820c365508014ed02186caa10029d60430d95420043f43821b2a840087d87043655087347d08086caa10028f61010d95420052f41821b2a8400a5d83043655094b4dd04086caa10029b60810d95420043fc2ae6b2a84008bf845cd65508010fb0f318caa10028f61263195426bd36c14c632a840087f8758c655080147f08b18caa128f87d9332195420051ec24c232a8400a3d84980655080b47d0db2aa8a12970f1db655514252e97ba8e4aa28496c3c65dc554508f3878cbb82a8a10e70f1d3655494218e1e32ee8a92840993c8755152508134790caa2a4a10130f1d9545494204d96412a8a9284def0f3255152508738d8edb2aa4a10d72b1db745494204d9643aa8a928404d2c87551525081365d0caa2a4a1026cb219545494202f16432a8a928405e2f765515250809a5cecaa2a4a10134b1d9545494202f163b2a8a928404c2c76551525080165f02aa2a4a1002cbe01545494250e1e3a0cbb0a840087e87d9561508010fd0e32ac2a12870f1d065d814252c3e436eab02840087e87d9560508010fd0e32ac0a10029761a54d95320068eba4a9b2a642899e87dd1654c80193ec5ba2ca9900363d8b74595320068fba8e8b2a64ddd4f75dc9654c801b1ee9b92ca99003631d372595321446ec3ecbb226400e1c54d97644c85153908b2ec899002a761b54d91320068ebaea9b22642995e87dd5644c8018bec5baac89900353d8b755913214e2e3aecab2264288dc87595644c801a38
  | 10 => 0x1008008000000040180000900406400804018078000000040c00280500a0540a8000500040000c00202400817000008000000040040080005003c028150000040000100613c1380a0000080880e3be1d32d89540068e2a2e7312a809ccc625ce625500199ae7b14c4aa00347151731895400477c3ac4312a8a5a6f85588625515355f08b10c4aa2971dd95711895454e5bb22e2312a800d34545c4625514b8f6cab80c4aa2a72ed9170189540069c2a2e0312a8018fa80dcf61550011f301b9ec2aa38f8715332d85540061e2a2e1b0aa8028f681dcf60550011eb03b9ec0aa38b8715332d81540061e2a2e3b02a809ace829d163949c359b053a2c72900297e157458e5214d2e42ae8b1ca400adb805c563948015b100b8ac7290e297a147158e520052ec28e2b1ca400a9e841c5639480153b0838ac729026b3a087158e521c566c10e2b1ca400cd5711c563948015b50038ac729002b66007158e5214d2f42c82b1ca400a5d85905639481359d0420ac729002b36084158e520056bc0ae0b1ca400ad4815c163948714bd0a382c729002976147058e520054f420e0b1ca400a9d841c1639481359d04382c7290e2b36087058e520056b408e0b1ca400ad5811c163948019b2e0382c7290a697a164058e520052ec2c80b1ca409ace82101639480159b04202c72900237a1c1058e520046ec3820b1ca429a5e8504163948014bb0a082c729002a7a101058e520054ec2020b1ca409ace82041639480159b04082c7290030f15374586520047dc02e6b0ca4018f8805cd6194801878a9ba2c1290023de0573582520147a40ae6b04a4038bf8750f645480147b0b20ec8a90028f61640d915251e4f3b665b22a400cb7719c7645486347d0a38ec8a92a68f61471d91520045f43863b22a4008bd870c7645486347d0a18ec8a90028f61431d915254d5741063b22a400aad820c764548015750018ec8a9002ae60031d91520065db84e1b22a431a3e851c3645495347b0a386c8a90022fa1c30d91520045ec3861b22a431a3e850c3645480147b0a186c8a92a6aba0830d915200556c1061b22a400ab6810c3645480156b02186c8a90022fa1c10d91520045ec3821b22a431a3e85043645480147b0a086c8a9002a7a0c10d91520054ec1821b22a4a9aae82043645480155b04086c8a90022f61e63191520051ec2cc6322a4e0aad8298c645480117f0eb18c8a90028fe15631915251f0fb2e64322a400a3d85984645480147b0b300c8a90128fa1b645515254e1e3b6c8aa2a4a9d2f741c95454921878c9b8aa8a91bf0f19370551524861e3a8c9b0aa4008be87d91615480117d0e322c2a91bf0f1d464d815254c5e436e8b02a4008be87d91605480117d0e322c0a9026b3a0a7558e426fd66c14eab1c8400a9f845d5639085153908baac721002b6e01
  | 11 => 0x1c29ef8000002238e6aba0d780014f1391f1af593018500ea0d0dc2b5aa0995acc8fca902a025714f8c01f11f410c86828a20e1d39a700000019b8000ce27e00014c8000000838ac12b8000000002c19ee0001050002e40000002338b68819c30002b71b39780082a625380024082c000249117a390320509bb1ba1412978000f8838157931a1c1d52611c62ad8000e19b51c69baa792c00881f910480006200000000024011509c0001180000a71368000d923a800000137aea8002cc075a3528723d8002c69d8a3a00006500000000000000000023f0000000002be8c695f0fd8002cd9d18c08941e30000860ab00c8002d816500021e9ae00017a027000000000089242a229f089a9570000001380001dbaeb00005a2ef0000992048d28e00350c425d80021800012400010600004d8000410002c78000ac82301d8002e700028d0000002b8abaa758b8a780ec16c2e093207029822700023407a800133ad690a98a28919d9e1ab30001a008b1bf18e8001109359d408d8000c509a07e25b95c85899302629fa0a2a586085e0001d30b81352a800000500a0500302300a000008070000041200700e0100b0020000140300700001804802002000010320020080082e0060340201400400801801018004000010020180081200402803001006000170030740080280500004016800004068008020000080100e00204000001016024018070000000100000e03002801014014030020260100380100e0180700000c0080e000004018000000080180e80003e09c0000501a0000000100000000807002004008000000000000100e0040d00301a014000010180840000100c014058000000000680601e0080000a00a000010010020180280000600800001002004008020020140300200e00401000000000010100020140200400001c090010100100200900a01c0000000a024060120000000080000001800800002000020000040100000a0220040000b01800808800000014260000000040080900000c000020200500400001202000000002000018080140040000200205000812004008020000000040480d00200001002010010040040020080481700a00000000002030008050040700100100414c038050000040a80600003800807000000068050020180000300005806811004000020010000040180000402c068080261180080000601800014002000000020160080400000c00001000002004000000000080f8090220080000500600002801006018000040000680180000a008000010000080000a000048028000140080000400000006803036020030130440040000000c014000140020500200200a0080080101e0180500000e0000400001e0000000100a00c008020020000081e0040780080101000406000000000000070020000280
  | 12 => 0x85e82d9a82d12ce1c88a594d0a228829c00002e80012312c94800004498c8002f19860f089fadc80002a8001e3ab380000010a18999faae0001138000000002080000562778389310000938002628000a7a850208000000001fa2171528000001de2be2dea1ca9b1758002c727f0000001d920100000001b0000001cd22c0e9aca05f21d9b7a1117c800000043ad01748018002a18fba930000ef9ea00000021981800009e8a31ae80000017706605c80000000000000003707f0a0800000000000285800000116a658aa00018fa6c0900002d9254923992815276a3008e0dd97600000019c0002ee26c8001332028001e6a078ea8002150b79b92030002f60000000e70000001b00001260f680016a2a79b59fe000100a9e8aa8ef20214eae50fa8000000000000e82afa6380000000025c1d080029a0002c28002ab0cd9738162aca1b2c900015c0000362649441189659c99eb0000000000002130000d81be88a00a9741398002b190728d9200001488bdac986e2b41faa8b0099788000a68002320922569ee9b20338000f1800164a869858c48df054902955963291ac112e067269a5821400007d0001c815527881a8ae228800000072ae9a8e9eba421660002f38359b42e61df85f8a100020390780000000000024300000006c1a09a69c5ad88df80001c2a40000222d4a0184b0002f00001030f70000002849688c60a50971309989fe95da7e92501916e1e41a5a559b99ca13f23e8000e624aa24aae8eead39810fc2d1ad2821a7da579cf172ad327f9628542d41dc0399ce8000000030000f580012101096e803a550cb2ce97d8001c19600110000000010ec80023b00000007ca820000f98002a8a480000440000d68001c100006a2d5adf8000bc0002319e88ba80000017697b83d0bea1398e0000000000000002d0800261ae580000012b18c0000002168eb0000000000001000188001582489878000002cf960a9c8b3068a8fadb94296d8a99a60001f89720cca478a90a42a295a0ce9130001209172089a997a9db0a48001718001d7a472210851970d50000002730528000000932c380000029da6f09c80c17795b8000002371562cb9be0002a6961aec2948000000708c39f289da2c89b22d88325c86694b848a7715f87785ba4d81a29281b8ad25f18180bab98429e29bb8168630bd18d2560e09492c80002970e92369ca944a5017e0001962f29c51cf9800ea182a0a9709d983b05d9e616988e9e7a962108000d499f00008995e18b28e1282688001088002690002cf13d06c947249abd0760002359ab0a014b00013a02818815380022222a1cba7aaaa1459f7879814a29a679908950501c400021a8bc8000c59418432521f80001d615a865ac600013b26a9f582e0002528c780004227c8392450002989b68178002828e280000
  | 13 => 0x2f1ed1b1a3d17f0fb00021e0002bd90107f903a8780d10e8782349340b087706d17103a07d8000000ba0d98721ed9c00f1281905a729461889162e6800200a0c84a2a22950d19ce00b1da0000000000f32da80007b13c1fb800000121a5105102292aa968c90958bf9b828386380002c91c8002ed0ed01ca8b958a6e0000d38000cfa4c04d0cf0000001f50b01cc1ea825a8f0ffa9b9d2a308ca0000002630000ad8fa17e80004b8db1c39b119399aac50239681258539e200000013620691b00000020500017f8000dc8000418349692a500019c9c09840460b509690b06f94a1dd94300018726ea4b9f31271d00c89409e989e0001ab80000010e000186ab807a1668c28000d6000290836aa9030a261832449cd89887c1b303400025980007b9d20bb8ee0000e79b72741a311e9e92b214a80f9e800000018f0000000001f615b0000c18002a38002332da0b4a2f8b98b1a5a10207ea6f8710000000d89c20001a20000618000000f400000000022400000000016b00000003c8001670000000478000000000f20000000a608700015913d8000001afade0e5014088a9f099832892a0d92d27b0330af90f12fa14a6700000000000003e2f1009084abc0000000002c492e80000001380f0002d98000001bd8002f200003c0001cb2eba7a1e100000000000004903f8ca8002a99890000001b0a53199245a5a80029d0400001fc8000001479f38002899290002e88000000690000f90578000000e32542e4adf22d1ef11c1110000000d42ac1952d71751370812a704e8d5a718c323c8e40000e49158859a92b48000532622db04e04700d9b2a290918002f49620c71042ed967837acd28a93c95499a24fae29468c824185d1f6ab90e392c029a118cd0251e0071ac09cc8f810d1bd22b0570558bf0910de1d6800a05a609b88aba18ad214e08f2c42ab8d20002e7ab6856a6622f0d722796ba3b9ec0a18f299e06f28c99b16380025e1d4ab00001791eca1f00000028600000000025fa0708080027522e28c20606b00000000018b83dab61b60001a401d09f1aca830000001c70be0000001d70450c226a27d23c0dd0000000de9509ad8b617c08d2a492780616111028093ba2a9f99a398399189808a85aa0ea0420f96a80a0b20201a50b71b49ac01fa258000820300d02b50748000b900000028402b1732d60002b100027128129390808b8000001640602f08002411520550eb91d8599a49aa090a5d26d02a2ef91ba66845a2193f800000000000124919096000029073000000243a178a280012996fa800f514c11e2378582dc19001292219814d96f2c8a0c24e0bb01585924d08416c90184c0ed9199f702786423f9c486a80515d09498203b80026400017b2720d304ca468002ca9968aea739dd03a92a049a701091de8b38001540211c910d
  | 14 => 0x73a0b2798c98f38fe80000004f86b80003f0000000001e724c8002d519980021d26800012d9ff27c24f26d9d824a2c58000cc2000649d58e100e270817109869ae20789140b1291156adda1611d2c30c129215119eaec90b851a442518001942760001da8f7aa10002398000791948021228e588fabb0da20baf4028a310408001a7a5b07503e8fd08685c2e1250942024143906a7b91204a80019d26b8d084f0002bb8000000000469ffaf30002b280006e80010c295ae02e3000132a1b8001a295e8000002dd0000002bf2e80000002e18000001a18978cb9e58001f022e80000022814015993e1d100490f934a3891a0000000088b28042f51af0121e50a825e9978078118000dbaaf01f0001499e4ae39532bfae91bf87401eab7a128000f018d8001a125882f98aa1a1ad000031000005a2680022016d18088280000000029e00000019200020f0001910ff11f8269388001c78000000002600001502ad010299a230001e08000002121a8a090002462ea00006d80013e80008780008ca1faa30b424e9f4ac21128f613a89b8af18491a8199bc0b5ad79f20fe0e217d000232abca6b00000023622b8000000000678000000069118000000e8a2082d09d0130000000002cb1aa852219274a3823e0a3800080209aee88c1148611702650768f4a592100000481df0a885b02f00002480001e0000001fb2250629fd0da9fc179951a4b02ba9aa94299126807002a889bc91f0001dc9452158d10318000001fdaaa928ab09
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x11d29804172d8d1000570648105cb6344001a0d5460854d8d1000474660105ce62440015c1920417398910006b00418218e62440011d29804373589100057064810dcd624400155193041751891000558648105d4624400159193041741891000568648105d062440011d198041731891000570648105cc6244001c50105d46318910007240417418c624400184e756086318910006135d58218c624400188e746086318910006235d18218c62440018c5716086318910006325c18218c62440011d198041739491000634218105ce52440015c192041739491051e0b20874595524400148d9218f74549100056464c10dd152440015a192043745491000474660105ce42440018d086041739091000570648105ce424400144d9218f75509100055464c10dd5424400156192043755091051e0b2087559142440014d197043764c910005b064810dd932440011d298042764c91000570648109d932440011d198040764c91000570648101d932441c99c182040764c910004b4660101d932440014d197040764c910005b0648101d9324400181d85610764c91000613a15821d9324400184d85608764c91000623a11821d9324400188d84608764c91000631609811d932440018c982600764c91000634605801d932440014c992c40764c9100053164a101d932440014d290840764c91000435660101d932440014c592040764c91000730c80101d932440010d998040764c91000532648101d93244001cc321040764c91000534e60101d932440018d298040764c91000534660101d932440018d198040764c91000434660101d93244001c5295040764c91000714654101d93244001c5285040764c91000714614101d93244001c9294040764c91000724650101d93244001c9284040764c91000724610101d932440014d392040764c91000730a48101d932440014d192040764c91000730648101d932440014c192040764c91000730608101d93244001cc0101da624c91000433a607658932440018c7811d9624c91000632e007658932440070ce98e1d624c9100063121f8158932440018c887e01624c91000634200765c532440018d0811d9704c91013474261715c1324404d4d0965c5704c91013e34219715c132440018d0702193248510006b0d80864c92144001645952193248510005a1650864c9214400168594d95324851000591657644c9214404f5c097601324851013db0259804c92144001ac0866013248510006341c4864c92044001ac361219324811000592654864c92044001689942193248110005a2653654c9204400164995d9132481101357025d814c9204404d6c0966053248110006b0219814c9204404d9c0874c92148110005b02593248520440016a194d9521481100059865764485204408b9c087d8d2148110
  | 1 => 0x252e51dd5811c9544c953987746047255132006c1151811c9544c94b94b75600725513254e62dd1801c9544c801b0854600725513251e43a0874d95524c94790e821d7645093204cc326154549424c81350c9755152509321464321d54549424c8012d298187705853200534a5b711c1614c8012d1981847058532005b064810d87604c8012d39858710d813200534e5d61c43604c8012d2981837158132004b4660601c5604c8014d297843615813200634a1e10d85604c8018d2861c7605813251c8ba636454a425440142d9215174d81510050b64854dc1655054703e98d95749494151d0ba5f65949425044b82c87595525094112cc926152509515040142d9215175d8141006835518215163c84018d1815c07058f210040f660549d9544840142d9215276551210050b648541d954485478358115076551210068315086551324840138794617714c921004d1e5584dc5324844f8c486dc5704c92104f111d9524c9514859370494549325452113d5125d854c9514859370494615325452113d51657744c95148413c8476509325052163dc1255424c9414844f58594dd5325052104d31259754c941485cdd04545d5325052113d6125d844c9414858f70495611325052151c8ba636454a425400142d9215174d85500050b64854dc5655014703e98d95749494051d0ba5f65949425002f82c8759552509400050b648545d7615002f3289854942541400bccc26151505505004bc30765454154140006835518215163c80018d1716007158f20005916548158d21c8001685942056348720005b06408158d21c8001685949456348720005916564158d21c800103d9815276551200050b648549d9544800142d92150765512051e0e600541d95448001a0c54219544c920004e2e5185dc1324800134b95613704c9201353225971dc132480015499520173c852000562650805cf21480015c19120173c852000562652505cf21480015499590173c852004f121d9524c9504817b7089454932541201355225d854c9504817b70894615325412013552657744c95048013c887650932501205ddc2255424c9404804d58994dd5325012004d32259754c940481cbd08545d532501201356225d844c940481777089561132501200056464c105d365440015a19204174d9510004276627418f6544001c90105d063d9510006239d18218f654400188d7460863d9510006b00418218f65440011d29804373595100057064810dcd6544001ac01060863595100055464c105d764440015619204175d9110004176627518f6444001c50105d463d9110006139d58218f644400184d7560863d9110006b00418218f64440011d29804373591100057064810dcd6444001ac01060863591100050b64854dd9544400142d92151765511051e0b208545d95444
  | 2 => 0x528ba509e00594e6b0a85f9267d89e00000098786397a4900024800009d65c0c0288b0450ec221f2708e20316a149940018a6e00000000768004c06c000040894c0797c558f0208001b8f20010e6d9284a800331fe25836761746c9d0001e600000109f800178540004705c0a934479be721e40f0002f8c63817609014351844b0e400000212067308065800000a60c8004b8004f0543f0d03b93a251801100048006630d27889c04122240b61013637858428ae2903a1f160001a4129ba141fa081a83e08a1d00a11958370867186a4c9c4021b47a108071124682e1207004910670382d07a6f0da4f83e5490c68872000ce7c030000e626800410001a0c87f1ce360000b200181481394662000238003a8006608c0019e26000000e85a000000c4001720d106771ae3e8007b99a3f800178a0750d64e0283d9a6811de729f4609ec199025880074800000005718615818169642e000000000695a6807e510bc458ac192024615e5b0aa038767a9662c862001c05516e328f4401b064940000c26a8006400013058000a8280201058040602078080201000000800088081407010140601050380a0f0f02c00030803c1400070000028028084c05158000200008140e0200800180100000040e0e094100008804280706010020100804000b06000020007818360100543648545ce6255147c0c62151739895400543648545cc62550015259215171189540054a648545c0625500142d9215170d85540050b648545c760550014d0905c47158e52006345c5801c563948014d0915c07058e5200634605701c1639480142d9215374586520050b64854dd160948014d0905c47158e42006345c5801c563908014d0915c07058e4200634605701c1639080142d9215375586420050b64854dd5609092182c76e05545494237e0b1db80551525080160d9215365d913200447660549d9544c80150d92152765513200543648541d9544c94790c82150765513
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1e00006a0e000000000000500024462e660042006c580072000000000000484000004a001a000000806874162c001c00020c00060000000000001864265e0000000000002200005c00000084000000708600001400007c626e822a3c040000440000006054000038004e00000000280000000012007a340000000052007e3278001000560000004c3a000000300076000a0000000008003e2000000000000000003600000000005a00020000000000000000000402020400000000000c0251c8194cc90a8b9cc4aa28e10fa8648549d9544c947812c0b242a0ecaa242a3c8164454219544c92151e05300c90a83b2a89028f20990150865513248001448d4020ba0c7b2a2000b20688105d063d9510004583520830431eca88003881740418218f6544001160d4820c10c6b2a2000a146a0105d463d911000588344082ea31ec8880022c1a90418218f6444001c20ba820c10c7b2220008b06a410608635911051c05950c90a8bb2a8880022c1a90418218e6244001428d4020ba8c63122000b10688105d4631891000512350082e8318c488002c81a20417418c6244001068d490c082e72922000c302199204173949100041a35243020b9c84880030c086648105ce42440010e0d4324080ec9922000c3066320040764c91000618331908203b264880024c1a2e60101d9324400182952b30080ec9922000c1469598040764c91000612548cc0203b26488003091a4660101d93244001860d1330080ec9922000c1466295040764c9100060a330ca8203b2648800305198a14101d93244001828cc30a080ec9922000c2466294040764c91000612330ca0203b2648800341195650101d93244001848cc508080ec9922000c2466184040764c9100070230ac20203b264880030c198a48101d93244001860cc324080ec9922000d10a5592040764c9100068832ac90203b2648800348294648101d93244001a40ca324080ec9922000930ea192040764c9100068850ac90203b2648800344185648101d93244001a4142324080ec9922000d2061192040764c91000498352c10203b264880030c198608101d93244001c20c2b04080ec9922000e2061182040764c91000498352080ed31264880028c1a804076989324400146153ec04326490a2000c3025c8660132485100041a3523890c99240880028c2a7d84864c920440018604b90cc0a649022000c3021c964c92148110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xe000020a46c0801006081a95d01060863d9510006041a95d41060863d9110006011a569198040764c910006041a568998040764c910006081a468998040764c9100070018561192040764c910006041a961582040764c910006081a961182040764c910
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x94c
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x3
  | 10 => 0x98a
  | 11 => 0x98c
  | 12 => 0x98d
  | 13 => 0x98e
  | 14 => 0x150a
  | 15 => 0x150c
  | 16 => 0x150d
  | 17 => 0x150e
  | 18 => 0xa0a
  | 19 => 0xa0c
  | 20 => 0xa0e
  | 21 => 0xa4a
  | 22 => 0xa4c
  | 23 => 0xa4d
  | 24 => 0xb09
  | 25 => 0xb0c
  | 26 => 0xb0d
  | 27 => 0xb0e
  | 28 => 0x1549
  | 29 => 0x154c
  | 30 => 0x154d
  | 31 => 0x154e
  | 32 => 0xb89
  | 33 => 0xb8c
  | 34 => 0xb8e
  | 35 => 0xbc9
  | 36 => 0xbcc
  | 37 => 0xbcd
  | 38 => 0xcc9
  | 39 => 0xcca
  | 40 => 0xccd
  | 41 => 0xcce
  | 42 => 0xd09
  | 43 => 0xd0a
  | 44 => 0xd0c
  | 45 => 0xd0e
  | 46 => 0x1609
  | 47 => 0x160a
  | 48 => 0x160c
  | 49 => 0x160e
  | 50 => 0xd49
  | 51 => 0xd4a
  | 52 => 0xd4c
  | 53 => 0xd4d
  | 54 => 0x1649
  | 55 => 0x164a
  | 56 => 0x164c
  | 57 => 0x164d
  | 58 => 0x1049
  | 59 => 0x104a
  | 60 => 0x104c
  | 61 => 0x98954
  | 62 => 0x94994
  | 63 => 0xb0954
  | 64 => 0x94b14
  | 65 => 0x1709
  | 66 => 0x209
  | 67 => 0x1409
  | 68 => 0x128a
  | 69 => 0x1449
  | 70 => 0x12ca
  | 71 => 0x249
  | 72 => 0x1849
  | 73 => 0x1489
  | 74 => 0x180a
  | 75 => 0x130a
  | 76 => 0x19c9
  | 77 => 0x14c9
  | 78 => 0x198a
  | 79 => 0x134a
  | 80 => 0xa0994
  | 81 => 0xa0996
  | 82 => 0xa4994
  | 83 => 0xa4995
  | 84 => 0xb0994
  | 85 => 0x98b14
  | 86 => 0x154994
  | 87 => 0x99554
  | 88 => 0xcc992
  | 89 => 0xcc995
  | 90 => 0xcc996
  | 91 => 0x1889
  | 92 => 0x1a09
  | 93 => 0xb1514
  | 94 => 0x150b14
  | 95 => 0x8a
  | 96 => 0xcd512
  | 97 => 0xcd515
  | 98 => 0xcd516
  | 99 => 0x8c
  | 100 => 0xa4a14
  | 101 => 0xb8a14
  | 102 => 0xa0b94
  | 103 => 0x138d
  | 104 => 0x124d
  | 105 => 0xcca16
  | 106 => 0xd0a14
  | 107 => 0xa0d14
  | 108 => 0x128d
  | 109 => 0x1a89
  | 110 => 0x1949
  | 111 => 0x198d
  | 112 => 0x134d
  | 113 => 0xbca54
  | 114 => 0xa4bd4
  | 115 => 0x138e
  | 116 => 0x124e
  | 117 => 0xcca55
  | 118 => 0xd4a54
  | 119 => 0xa4d54
  | 120 => 0x128e
  | 121 => 0x180e
  | 122 => 0x130e
  | 123 => 0xb8b14
  | 124 => 0xb8b16
  | 125 => 0xbcb14
  | 126 => 0xbcb15
  | 127 => 0xccb11
  | 128 => 0xccb15
  | 129 => 0xccb16
  | 130 => 0x188a
  | 131 => 0x1a0a
  | 132 => 0xcd551
  | 133 => 0xcd555
  | 134 => 0xcd556
  | 135 => 0x20c
  | 136 => 0xbcb94
  | 137 => 0x170a
  | 138 => 0xccb96
  | 139 => 0xd0b94
  | 140 => 0xb8d14
  | 141 => 0x140d
  | 142 => 0x1a8a
  | 143 => 0x194a
  | 144 => 0x19cd
  | 145 => 0x14cd
  | 146 => 0xccbd5
  | 147 => 0xd4bd4
  | 148 => 0xbcd54
  | 149 => 0x140e
  | 150 => 0x184e
  | 151 => 0x148e
  | 152 => 0x128c
  | 153 => 0x140c
  | 154 => 0x188c
  | 155 => 0x1a0c
  | 156 => 0x1a8c
  | 157 => 0x194c
  | 158 => 0x40c
  | 159 => 0x44c
  | 160 => 0xd4d14
  | 161 => 0x44d
  | 162 => 0x104d14
  | 163 => 0x74b
  | 164 => 0x1a0d
  | 165 => 0x194b
  | 166 => 0x40e
  | 167 => 0x104d54
  | 168 => 0x188e
  | 169 => 0x1a8b
  | 170 => 0xb09895c
  | 171 => 0xb09499c
  | 172 => 0x9894b1c
  | 173 => 0x95294
  | 174 => 0x95414
  | 175 => 0xb0cd1
  | 176 => 0x154cd1
  | 177 => 0x24211
  | 178 => 0xca
  | 179 => 0xd512
  | 180 => 0x25551
  | 181 => 0x24b91
  | 182 => 0x170e
  | 183 => 0x25491
  | 184 => 0x24bd1
  | 185 => 0x170d
  | 186 => 0x254d1
  | 187 => 0xcca099e
  | 188 => 0x98a16
  | 189 => 0xcca499d
  | 190 => 0x98a55
  | 191 => 0x98cd5
  | 192 => 0x98cd6
  | 193 => 0x749
  | 194 => 0xa1894
  | 195 => 0xa4cd5
  | 196 => 0x198a55
  | 197 => 0x170a55
  | 198 => 0xa5a14
  | 199 => 0xccb8b1e
  | 200 => 0xb0b96
  | 201 => 0xccbcb1d
  | 202 => 0xb0bd5
  | 203 => 0xb0cd5
  | 204 => 0xb0cd6
  | 205 => 0x74a
  | 206 => 0xb9894
  | 207 => 0xbccd5
  | 208 => 0x19cbd5
  | 209 => 0x170bd5
  | 210 => 0xbda14
  | 211 => 0x151294
  | 212 => 0x170cd1
  | 213 => 0x155414
  | 214 => 0x170cd2
  | 215 => 0x44cd5
  | 216 => 0xcda15
  | 217 => 0x198cd5
  | 218 => 0x19ccd5
  | 219 => 0x1a0cd5
  | 220 => 0x189614
  | 221 => 0x1a1654
  | 222 => 0x104d4d1c
  | 223 => 0x160d54
  | 224 => 0x40cd6
  | 225 => 0x164d14
  | 226 => 0x171995
  | 227 => 0x1719d5
  | 228 => 0x4954
  | 229 => 0xa4cc99d
  | 230 => 0xbcccb1d
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1426
  | 6 => 3727
  | 5 => 1517
  | 4 => 260
  | 3 => 68
  | 2 => 8
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | 6 => packedAt gbK6 (i*48) 39
  | 5 => packedAt gbK5 (i*59) 50
  | 4 => packedAt gbK4 (i*70) 61
  | 3 => packedAt gbK3 (i*81) 72
  | 2 => packedAt gbK2 (i*92) 83
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | 6 => gbHint (packedAt gbK6 (i*48+39) 9)
  | 5 => gbHint (packedAt gbK5 (i*59+50) 9)
  | 4 => gbHint (packedAt gbK4 (i*70+61) 9)
  | 3 => gbHint (packedAt gbK3 (i*81+72) 9)
  | 2 => gbHint (packedAt gbK2 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (57987+((h/475+packedAt gbK7 (52762+(h % 475)*11) 11) % 1883)*12) 12
  | 6 => packedAt gbK6 (195042+((h/1242+packedAt gbK6 (178896+(h % 1242)*13) 13) % 4920)*13) 13
  | 5 => packedAt gbK5 (95058+((h/505+packedAt gbK5 (89503+(h % 505)*11) 11) % 2003)*12) 12
  | 4 => packedAt gbK4 (18974+((h/86+packedAt gbK4 (18200+(h % 86)*9) 9) % 313)*10) 10
  | 3 => packedAt gbK3 (5684+((h/22+packedAt gbK3 (5508+(h % 22)*8) 8) % 170)*8) 8
  | 2 => packedAt gbK2 (744+((h/2+packedAt gbK2 (736+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x71c7c7071c71f1c1e3f03fe1ff0c0d30d34cf
  | 1 => 0x381f8f807e07e3e01fc7fc0fe1f30323323b33
  | 2 => 0x3fe00fff8ff803ffe3f8000ffe000c3cc3cc3c
  | 3 => 0x3ffff0000ffffc0003fffff0000c0fc0fc0fc0
  | 4 => 0xc00000000ffffffffc000000000ff000fff000
  | 5 => 0xfffffffff000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x82041412108105048409014218a0c051051045
  | 1 => 0x10088884240222210842500581430122122112
  | 2 => 0x9200121024800484290082844000404404c28
  | 3 => 0x2d5120090b5448024324aaa0440c0e80e80e80
  | 4 => 0x800000000da79393900030c088655000bfb000
  | 5 => 0x369e4e4e400000000000c301118aabfb000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffffef8fef8eee8fffffef8fef8eee8fffffef8fef8eee8fffffef8fef8eee8fffffef8fef8eee8fffffef8fef8eee8fffffef8fef8eee8fffffef8fef8eee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15034
namespace PEqualNP.Outside.L_meta_15034
open PEqualNP.Outside.L_meta_15034.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 5 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 91 := (concat bs0_4_0 (concat bs0_4_32 bs0_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 5 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 25 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 91 := (concat bs1_4_0 (concat bs1_4_32 bs1_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 44 := (concat bs1_5_0 bs1_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 7 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 5 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 8 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_64 : Interval s3Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_96 : Interval s3Atlas 3 96 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 102 := (concat (concat bs3_3_0 bs3_3_32) (concat bs3_3_64 bs3_3_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_128 : Interval s3Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_160 : Interval s3Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_224 : Interval s3Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_256 : Interval s3Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_320 : Interval s3Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_352 : Interval s3Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_416 : Interval s3Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_448 : Interval s3Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_512 : Interval s3Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_544 : Interval s3Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_608 : Interval s3Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_640 : Interval s3Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_704 : Interval s3Atlas 4 704 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 725 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128))) (concat (concat bs3_4_160 (concat bs3_4_192 bs3_4_224)) (concat bs3_4_256 (concat bs3_4_288 bs3_4_320)))) (concat (concat (concat bs3_4_352 (concat bs3_4_384 bs3_4_416)) (concat bs3_4_448 (concat bs3_4_480 bs3_4_512))) (concat (concat bs3_4_544 (concat bs3_4_576 bs3_4_608)) (concat bs3_4_640 (concat bs3_4_672 bs3_4_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_64 : Interval s3Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_128 : Interval s3Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_160 : Interval s3Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_224 : Interval s3Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_256 : Interval s3Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_320 : Interval s3Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_352 : Interval s3Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_416 : Interval s3Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_448 : Interval s3Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_512 : Interval s3Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_544 : Interval s3Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_608 : Interval s3Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_640 : Interval s3Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 682 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 (concat bs3_5_192 bs3_5_224)) (concat bs3_5_256 (concat bs3_5_288 bs3_5_320)))) (concat (concat (concat bs3_5_352 bs3_5_384) (concat bs3_5_416 (concat bs3_5_448 bs3_5_480))) (concat (concat bs3_5_512 (concat bs3_5_544 bs3_5_576)) (concat bs3_5_608 (concat bs3_5_640 bs3_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := (concat bs3_6_0 bs3_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_7_0 : Interval s3Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_7 : Interval s3Atlas 7 0 1 := bs3_7_0
theorem alls3 : ∀ k ≤ 7, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
  · exact alls3_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 9 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 50 := (concat bs4_3_0 bs4_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_128 : Interval s4Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 136 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 48 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 9 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 50 := (concat bs5_3_0 bs5_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_128 : Interval s5Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 136 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 48 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 8 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 68 := (concat bgb_3_0 (concat bgb_3_32 bgb_3_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_128 : Interval gbAtlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_160 : Interval gbAtlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 260 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_32 : Interval gbAtlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_64 : Interval gbAtlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_128 : Interval gbAtlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_160 : Interval gbAtlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_224 : Interval gbAtlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_256 : Interval gbAtlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_320 : Interval gbAtlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_352 : Interval gbAtlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_416 : Interval gbAtlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_448 : Interval gbAtlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_512 : Interval gbAtlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_544 : Interval gbAtlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_608 : Interval gbAtlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_640 : Interval gbAtlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_704 : Interval gbAtlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_736 : Interval gbAtlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_800 : Interval gbAtlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_832 : Interval gbAtlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_896 : Interval gbAtlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_928 : Interval gbAtlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_992 : Interval gbAtlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1024 : Interval gbAtlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1088 : Interval gbAtlas 5 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1120 : Interval gbAtlas 5 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1184 : Interval gbAtlas 5 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1216 : Interval gbAtlas 5 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1280 : Interval gbAtlas 5 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1312 : Interval gbAtlas 5 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1376 : Interval gbAtlas 5 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1408 : Interval gbAtlas 5 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1472 : Interval gbAtlas 5 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1504 : Interval gbAtlas 5 1504 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1517 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_32 : Interval gbAtlas 6 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_64 : Interval gbAtlas 6 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_128 : Interval gbAtlas 6 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_160 : Interval gbAtlas 6 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_224 : Interval gbAtlas 6 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_256 : Interval gbAtlas 6 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_320 : Interval gbAtlas 6 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_352 : Interval gbAtlas 6 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_416 : Interval gbAtlas 6 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_448 : Interval gbAtlas 6 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_512 : Interval gbAtlas 6 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_544 : Interval gbAtlas 6 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_608 : Interval gbAtlas 6 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_640 : Interval gbAtlas 6 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_704 : Interval gbAtlas 6 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_736 : Interval gbAtlas 6 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_800 : Interval gbAtlas 6 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_832 : Interval gbAtlas 6 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_896 : Interval gbAtlas 6 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_928 : Interval gbAtlas 6 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_992 : Interval gbAtlas 6 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1024 : Interval gbAtlas 6 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1088 : Interval gbAtlas 6 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1120 : Interval gbAtlas 6 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1184 : Interval gbAtlas 6 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1216 : Interval gbAtlas 6 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1280 : Interval gbAtlas 6 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1312 : Interval gbAtlas 6 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1376 : Interval gbAtlas 6 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1408 : Interval gbAtlas 6 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1472 : Interval gbAtlas 6 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1504 : Interval gbAtlas 6 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1568 : Interval gbAtlas 6 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1600 : Interval gbAtlas 6 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1664 : Interval gbAtlas 6 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1696 : Interval gbAtlas 6 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1760 : Interval gbAtlas 6 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1792 : Interval gbAtlas 6 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1856 : Interval gbAtlas 6 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1888 : Interval gbAtlas 6 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1952 : Interval gbAtlas 6 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1984 : Interval gbAtlas 6 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2048 : Interval gbAtlas 6 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2080 : Interval gbAtlas 6 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2144 : Interval gbAtlas 6 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2176 : Interval gbAtlas 6 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2240 : Interval gbAtlas 6 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2272 : Interval gbAtlas 6 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2336 : Interval gbAtlas 6 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2368 : Interval gbAtlas 6 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2432 : Interval gbAtlas 6 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2464 : Interval gbAtlas 6 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2528 : Interval gbAtlas 6 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2560 : Interval gbAtlas 6 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2624 : Interval gbAtlas 6 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2656 : Interval gbAtlas 6 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2720 : Interval gbAtlas 6 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2752 : Interval gbAtlas 6 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2816 : Interval gbAtlas 6 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2848 : Interval gbAtlas 6 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2912 : Interval gbAtlas 6 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2944 : Interval gbAtlas 6 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3008 : Interval gbAtlas 6 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3040 : Interval gbAtlas 6 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3104 : Interval gbAtlas 6 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3136 : Interval gbAtlas 6 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3200 : Interval gbAtlas 6 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3232 : Interval gbAtlas 6 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3296 : Interval gbAtlas 6 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3328 : Interval gbAtlas 6 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3392 : Interval gbAtlas 6 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3424 : Interval gbAtlas 6 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3488 : Interval gbAtlas 6 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3520 : Interval gbAtlas 6 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3584 : Interval gbAtlas 6 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3616 : Interval gbAtlas 6 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3680 : Interval gbAtlas 6 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3712 : Interval gbAtlas 6 3712 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3727 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)))) (concat (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)))))) (concat (concat (concat (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)))) (concat (concat (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496))) (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624)) (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752))))) (concat (concat (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976))) (concat (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)))) (concat (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456))) (concat (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 bgb_6_3584)) (concat (concat bgb_6_3616 bgb_6_3648) (concat bgb_6_3680 bgb_6_3712)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_128 : Interval gbAtlas 7 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_160 : Interval gbAtlas 7 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_224 : Interval gbAtlas 7 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_256 : Interval gbAtlas 7 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_320 : Interval gbAtlas 7 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_352 : Interval gbAtlas 7 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_416 : Interval gbAtlas 7 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_448 : Interval gbAtlas 7 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_512 : Interval gbAtlas 7 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_544 : Interval gbAtlas 7 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_608 : Interval gbAtlas 7 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_640 : Interval gbAtlas 7 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_704 : Interval gbAtlas 7 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_736 : Interval gbAtlas 7 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_800 : Interval gbAtlas 7 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_832 : Interval gbAtlas 7 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_896 : Interval gbAtlas 7 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_928 : Interval gbAtlas 7 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_992 : Interval gbAtlas 7 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1024 : Interval gbAtlas 7 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1088 : Interval gbAtlas 7 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1120 : Interval gbAtlas 7 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1184 : Interval gbAtlas 7 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1216 : Interval gbAtlas 7 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1280 : Interval gbAtlas 7 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1312 : Interval gbAtlas 7 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1376 : Interval gbAtlas 7 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1408 : Interval gbAtlas 7 1408 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1426 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 (concat bgb_7_448 bgb_7_480))) (concat (concat bgb_7_512 (concat bgb_7_544 bgb_7_576)) (concat bgb_7_608 (concat bgb_7_640 bgb_7_672))))) (concat (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832))) (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))) (concat (concat (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)) (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216))) (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := (concat bgb_8_0 bgb_8_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_2 i (by omega) hi
  · exact allgb_3 i (by omega) hi
  · exact allgb_4 i (by omega) hi
  · exact allgb_5 i (by omega) hi
  · exact allgb_6 i (by omega) hi
  · exact allgb_7 i (by omega) hi
  · exact allgb_8 i (by omega) hi
  · exact allgb_9 i (by omega) hi
def Complete (g : Atlas) := ∀ k ≤ top g, ∀ i < count g k, checkRow g k i = true
theorem frozen {g : Atlas} {p n} (ready : Ready g p n) (complete : Complete g)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs=true) (names : xs.map Prod.fst=roots g) :
    Lower true (roots g) (target g) (top g+1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checked ready _ complete 0 row

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 32, 48),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 2 zero,inputs.getD 6 zero,inputs.getD 3 zero,inputs.getD 7 zero,inputs.getD 4 zero,inputs.getD 0 zero,inputs.getD 5 zero,inputs.getD 1 zero]
def fullWord : Sig := 0xffffffffffffeeeefffffffffef8eee8fffffefeffffeeeefffffef8fef8eee8ffffffffffffeeeefffffffffef8eee8fffffefeffffeeeefffffef8fef8eee8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 12 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) (SBf 4) :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) (SBf 5) :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val) := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,32,160)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,32,160)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 8) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 8 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 12)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 12 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_15034.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 fullWord=false)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extractPlan gs fullRoots legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : fullRoots.all plainWord=true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (fullRoots.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,B,hr,hit,hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega

def mono : List Gate := [⟨.and,[5,7]⟩,⟨.or,[0,3]⟩,⟨.or,[9,4]⟩,⟨.and,[10,6]⟩,⟨.or,[0,1]⟩,⟨.or,[12,2]⟩,⟨.or,[5,7]⟩,⟨.and,[13,14]⟩,⟨.or,[0,1]⟩,⟨.and,[16,4]⟩,⟨.or,[8,11]⟩,⟨.or,[18,15]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ correct
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨gs,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg))),len⟩
  · push Not at clean
    obtain ⟨a,ha,hop⟩ := clean
    have lo := binaryLower low gs o (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal) correct
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot,hop] at e
    exact ⟨mono,20,monoShape,by change 13 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_15034

open PEqualNP.Outside.L_meta_15034 in
theorem PEqualNP.Outside.L_meta_15034 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
