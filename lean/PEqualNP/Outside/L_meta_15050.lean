import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_15050.Model
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


end PEqualNP.Outside.L_meta_15050.Model

namespace PEqualNP.Outside.L_meta_15050
open PEqualNP.Outside.L_meta_15050.Model
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

def SBf (j : Nat) : Nat := [7, 7, 6, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_15050

namespace PEqualNP.Outside.L_meta_15050
open PEqualNP.Outside.L_meta_15050.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x5ea40000000a90020002e0608a2a38992960c1139716906874260609566402200b101f0a44400147919a003942d006c79d004c0002410d0901c51cd080085041240ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fa30fd30f930fc30ff20fe20fa20fd20f920fc20ff10fb10fe10fd10fc10f810
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x5d00008006f0c218921a1499cdc3231970004e0000000001804d0a0000208f20018960fc45388ec0000000ac0084001885854291946828001f40000060005a00289408e400b1d4b400419dc98742501c3842400f41a25120000c330f800003530184f0572a9a470370219054410ca1c2836351e8000500000102f09054fe17299cc0001360281e00000004c001e118004300000e00000110003a391d81c00001b49e5610840907c1108cb200001ec720b1f1343a6835978be271716c121100198003f0007896034086c4007010002000403151816010f010100010100080604270300020004000407000002030302001b00000001060002bd28487795090edca421db54843bb28887755110ef4a021de54043bd28485795090abca6215754c42bb28885755110af4a0215e54042bd286657950ccaf4a1195e542329faa2653c544ca7ca8194f55032e69906576510caeaa2195e94032bca80657a50d06f2a1a0ee94341dca86833d54906f6a0a0de14141dba8a83bb5050770a0a0cf95041bd286637950cc67ca918cf55231daa0c63b5414c6f6a098de141319f2a0633d540c6dca418db54831bd2806379500c6f4a190de543219f2a4433d548876a8310ed50521bda824378504867ca810cf55021af298435d53086f4a010de54021bb28e817551d02f2a7185e54a30bd28c61bb418c372831876d4d30bda926178514c37682986e50530ed98a61d9314c2f4a0185ed4e20bca9c417952882f4a3106ed0620dca0c417b53482f2a6907ad4920bc28a41bb414837282907ac8520f490a417a500827ca9884f55310dd2a621b954c42f6a7885e54f10bda96217952c437683886e50710daa0c217a508427ca8084f55010af298215d53042dca4085b54810daa0821ba5404372a8085ed4c10ed298217953043b2a6085654c10bda9021ea52042f2a4087a54810b4a90217a51043e4a2086ed0410f920821b941043e282086c50410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x2801108140000018000007cd9554854a300652b100000090400b8b440468f5a58e884e0ca1e34b88005648380000002600709a400c0c20003072c5001780000800480060838c0c2010200502848d584544cb0d544c832d14c9510cab260d4541cc504504c73141141219a588514c3305150530e4505314c2706154d209658c51483305150520e850521483155350410c9549410426962d4c1096596530431a5454c10c6551530425963d48109a59652043495394810ca95152043295454810d294d52043495354810ac592510423965d0410c654f410432952d0410ac59241043515390410d854a410423b6550410c654d41043295250410d454d41043615250410acd9541043336550410ccd4d41043925350410cc54d41043915350410c454d41043335250410e894941043315250410e854941043215250410
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x404e60000019482000021485c85150530a22e628a829052172d4d4104288baca6a0821445cf5250410a42eb292820870153949410438129aa4a0821c054d5250410
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => packedAt s0K5 (864+((h/16+packedAt s0K5 (768+(h % 16)*6) 6) % 63)*7) 7
  | 4 => packedAt s0K4 (4032+((h/45+packedAt s0K4 (3672+(h % 45)*8) 8) % 180)*9) 9
  | 3 => packedAt s0K3 (2012+((h/16+packedAt s0K3 (1900+(h % 16)*7) 7) % 73)*7) 7
  | 2 => packedAt s0K2 (453+((h/3+packedAt s0K2 (441+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x78e3c71fc31e3c771c70e387c71c71f633c93
  | 2 => 0x7f03f81ffc1ffff81f80fc07f81ffff8430ff
  | 3 => 0xf8003ffe3ffe03f8fe000fff8ffe07e007cf1c
  | 4 => 0xffffc0003ffffc00fffff0000ffff800f80fe0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x70e4472385a2c58870c1660b1c1c514e631c91
  | 2 => 0x810888440a050200810888442080a290842026
  | 3 => 0x10051100908048011200029105240442014518
  | 4 => 0x2220002921000092245220000a491004280ac0
  | 5 => 0xc448224002299324c9a4cd2640002098d6b000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xffffffc0fff0f0c0ffffffc0fff0f0c0ffffffc0fff0f0c0ffffffc0fff0f0c0ffffffc0fff0f0c0ffffffc0fff0f0c0ffffffc0fff0f0c0ffffffc0fff0f0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15050
namespace PEqualNP.Outside.L_meta_15050
open PEqualNP.Outside.L_meta_15050.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0xaae3400412000c01638ad32054905913e6128c083d3823c18000121480036b11a21a289ad5e0002842380000064080525001d0e00017000801500030573c4026083349ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fa30fd30f930fc30ff20fe20fa20fd20f920fc20ff10fb10fe10fd10fc10f810
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x104000c08000390000000003896c68543c0003c0013800004600000006630800000027800000d0a800160000154920000000f6000006c8e0040000da351d9c0ea50350004a002b958ec00358186600290c4c067000003400090000000098d8f800088f4f2000005c280042178a27a1d0700072000c8006f428006e00010000000000000000050008405000008a2622000864d171745a3e00000000014874c668118bd0c58038b0820000090026500138087e000fc0000140583e4a2e0f0907707820006c37000be7f1c0010200310405409000000021001cc002b0000000743ea0c60872d130000e0012ca6403200c181911164d200010300010500080000000000030200000001020a020101040200000b0204050301050407050000070005040cbd28487795090edca421db54843bb28887755110ef4a021de54043bd28485795090abca6215754c42bb28885755110af4a0215e54042bd286657950ccaf4a1195e542329faa2653c544ca7ca8194f55032e69906576510caeaa2195e94032bca80657a50d06f2a1a0ee94341dca86833d54906f6a0a0de14141dba8a83bb5050770a0a0cf95041bd286637950cc67ca918cf55231daa0c63b5414c6f6a098de141319f2a0633d540c6dca418db54831bd2806379500c6f4a190de543219f2a4433d548876a8310ed50521bda824378504867ca810cf55021af298435d53086f4a010de54021bb28e817551d02f2a7185e54a30bd28c61bb418c372831876d4d30bda926178514c37682986e50530ed98a61d9314c2f4a0185ed4e20bca9c417952882f4a3106ed0620dca0c417b53482f2a6907ad4920bc28a41bb414837282907ac8520f490a417a500827ca9884f55310dd2a621b954c42f6a7885e54f10bda96217952c437683886e50710daa0c217a508427ca8084f55010af298215d53042dca4085b54810daa0821ba5404372a8085ed4c10ed298217953043b2a6085654c10bda9021ea52042f2a4087a54810b4a90217a51043e4a2086ed0410f920821b941043e282086c50410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x6073e010002a00d0000940045a4802120c5811445138000387800cb132950bcf00164d5005620c2e3a04b091490000386400d005d185066c00004023048200181052e04000024c0048d584544cb0d544c832d14c9510cab260d4541cc504504c73141141219a588514c3305150530e4505314c2706154d209658c51483305150520e850521483155350410c9549410426962d4c1096596530431a5454c10c6551530425963d48109a59652043495394810ca95152043295454810d294d52043495354810ac592510423965d0410c654f410432952d0410ac59241043515390410d854a410423b6550410c654d41043295250410d454d41043615250410acd9541043336550410ccd4d41043925350410cc54d41043915350410c454d41043335250410e894941043315250410e854941043215250410
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x3404023000429c001485c85150530a22e628a829052172d4d4104288baca6a0821445cf5250410a42eb292820870153949410438129aa4a0821c054d5250410
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => packedAt s1K5 (864+((h/16+packedAt s1K5 (768+(h % 16)*6) 6) % 63)*7) 7
  | 4 => packedAt s1K4 (4032+((h/45+packedAt s1K4 (3672+(h % 45)*8) 8) % 217)*9) 9
  | 3 => packedAt s1K3 (2012+((h/16+packedAt s1K3 (1900+(h % 16)*7) 7) % 67)*7) 7
  | 2 => packedAt s1K2 (453+((h/3+packedAt s1K2 (441+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x78e3c71fc31e3c771c70e387c71c71f633c93
  | 2 => 0x7f03f81ffc1ffff81f80fc07f81ffff8430ff
  | 3 => 0xf8003ffe3ffe03f8fe000fff8ffe07e007cf1c
  | 4 => 0xffffc0003ffffc00fffff0000ffff800f80fe0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x70e4472385a2c58870c1660b1c1c514e631c91
  | 2 => 0x810888440a050200810888442080a290842026
  | 3 => 0x10051100908048011200029105240442014518
  | 4 => 0x2220002921000092245220000a491004280ac0
  | 5 => 0xc448224002299324c9a4cd2640002098d6b000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xffffffa0fff0f0a0ffffffa0fff0f0a0ffffffa0fff0f0a0ffffffa0fff0f0a0ffffffa0fff0f0a0ffffffa0fff0f0a0ffffffa0fff0f0a0ffffffa0fff0f0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15050
namespace PEqualNP.Outside.L_meta_15050
open PEqualNP.Outside.L_meta_15050.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x60480002000fb10f610f410f810f010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xc04080151800000001725084364a8086c55010e929821d153043c4a4087854810
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x88003115454c10c855152043415354810
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
  | 4 => packedAt s2K4 (84+((h/1+packedAt s2K4 (80+(h % 1)*4) 4) % 11)*4) 4
  | 3 => packedAt s2K3 (197+((h/2+packedAt s2K3 (189+(h % 2)*4) 4) % 16)*4) 4
  | 2 => packedAt s2K2 (117+((h/1+packedAt s2K2 (114+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x78f0f1ff0f1fff1c78e0f1c1fc707ffcc3333f
  | 1 => 0x80ff01fff01fffe07f00fe01ff807fff0c3c3f
  | 3 => 0xfffe0fffe0f8ff8000fffe3fff8e000fcfcc
  | 4 => 0xff00000fffff00ffffff00003ffff003f00ff0
  | 5 => 0xfffffff0000000ffffffffffc0000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x111a42a1682a501c282a5054541512a8c31315
  | 1 => 0x6224a5428654a0e05114a228a88a25530c2c2a
  | 3 => 0x14422064220601248000348c0d23081805454c
  | 4 => 0x20044988440032491a460000324c4061500ab0
  | 5 => 0x408880008898c4926498c93100000182aab000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xffffff88ff888888ffffff88ff888888ffffff88ff888888ffffff88ff888888ffffff88ff888888ffffff88ff888888ffffff88ff888888ffffff88ff888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15050
namespace PEqualNP.Outside.L_meta_15050
open PEqualNP.Outside.L_meta_15050.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x5a2003c000000098a4e00217381401d068c4070024c004c64f805044681005921b0018aa9240001e0094014008550034ac602400071000001040601023080183003ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x50410c3c2622511605174a4e0030000018363e0014000f1c00064500000059001e1349561d4d4411343927000809073f2e0d4b101a470058433a12423d33570b0025000354382b002c37400e2f002d002101310a0252483b4f2835040019321b1f2a5355234c240015002029465a1f0800103061c004000400d043c911102c680041c21c0e1c0210b3e5390e7aa521db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb948439ea9087ad5210e5aa421ed94443daa8887ba5010f72a021cf94f429eaa4855f5350ab8a6a167d4d429e29a859c5350a38a6a16bd49429f2a0853f54cca78a9994f952329eaa4659c438cb5a85194fd51329e2a265ad424ca7ca8194f55032ce2186576510caeaa2195e94032bca80655e53906baa720e710f31bd286637950cc67ca918cf552319faa2633c544c7388698cf953219eaa6437b50486f0a090cf950219eaa0435e53086baa610de94021bca80435e53902baa7206710f30bb28e617551cc27ca9184f552309faa2613c544c33886984f953209eaa6417751482e8a2904f950209eaa0415e53082baa6105d94420baa88413e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xb9802a00099ca1640280819e88cc0002c11a0143a400a4821018c500f255294443c95495110f295294043ca5495010f315154043c35885350b166114d42c55845350b1a6014d42c65805350a8d6210e32a318d428ca2c655093287594430cb144354432c610d500ca8d6210f31c610d50cc68d6210d318718d54c868d6210f30c510d51cc28d6210d308718d54c83615244010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x10000084c001815896114d42c12c4b00a6a1611615805350a84b9086a8663415c84354730
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | 2 => packedAt s3K2 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2667+((h/30+packedAt s3K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s3K3 (990+((h/8+packedAt s3K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s3K2 (249+((h/1+packedAt s3K2 (245+(h % 1)*4) 4) % 10)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x878f1ffc3c7fc7e38f1c0e3fc70fc3fe30f4cf
  | 1 => 0xf80fe3ffc07ff8fc0fe00fc7f80ffc3ec338f3
  | 2 => 0xffc3fff8fff1ff0000ff8fff1ffc103cf3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xb011888490a288018504a20941224194305445
  | 1 => 0x32251090945010c0a21444288449828c12892
  | 2 => 0x44440212200800321002089012812201028128
  | 4 => 0x110049a088019244a3486000e468088c540ec0
  | 5 => 0x66089203326e249b4c938f2400803331abf000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xffffe8e8f8f8e8e8ffffe8e8f8f8e8e8ffffe8e8f8f8e8e8ffffe8e8f8f8e8e8ffffe8e8f8f8e8e8ffffe8e8f8f8e8e8ffffe8e8f8f8e8e8ffffe8e8f8f8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15050
namespace PEqualNP.Outside.L_meta_15050
open PEqualNP.Outside.L_meta_15050.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x803200000481801b245400000010ab4a2c01a04300204e3800a0089480002080f26a00140815500308c196007131e0e5cf8900740111a25c0000840c0000040003ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x71d2c0000004e35155804315449262f08423b102b00003e251a0016000e00300d11340b5651283f134b3d0300324021270a463947014d18120236335a4a000050241f2d001b570c0023534c59094114374800000000000005202a220006380f29443c431c3a5245192e1e55174f03020060e00040880a302821209202062510f00101030010083153e5390e7aa521db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb948439ea9087ad5210e5aa421ed94443daa8887ba5010f72a021cf94f429eaa4855f5350ab8a6a167d4d429e29a859c5350a38a6a16bd49429f2a0853f54cca78a9994f952329eaa4659c438cb5a85194fd51329e2a265ad424ca7ca8194f55032ce2186576510caeaa2195e94032bca80655e53906baa720e710f31bd286637950cc67ca918cf552319faa2633c544c7388698cf953219eaa6437b50486f0a090cf950219eaa0435e53086baa610de94021bca80435e53902baa7206710f30bb28e617551cc27ca9184f552309faa2613c544c33886984f953209eaa6417751482e8a2904f950209eaa0415e53082baa6105d94420baa88413e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x94b2e9003aa00042000428661a30072800801ec125a299612200018b255294443c95495110f295294043ca5495010f315154043c35885350b166114d42c55845350b1a6014d42c65805350a8d6210e32a318d428ca2c655093287594430cb144354432c610d500ca8d6210f31c610d50cc68d6210d318718d54c868d6210f30c510d51cc28d6210d308718d54c83615244010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x82006041815896114d42c12c4b00a6a1611615805350a84b9086a8663415c84354730
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s4K5 (788+((h/14+packedAt s4K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s4K4 (2667+((h/30+packedAt s4K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s4K3 (990+((h/8+packedAt s4K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s4K2 (248+((h/1+packedAt s4K2 (245+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x878f1ffc3c7fc7e38f1c0e3fc70fc3fe30f4cf
  | 1 => 0xf80fe3ffc07ff8fc0fe00fc7f80ffc3ec338f3
  | 2 => 0xffc3fff8fff1ff0000ff8fff1ffc103cf3c
  | 3 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xb011888490a288018504a20941224194305445
  | 1 => 0x32251090945010c0a21444288449828c12892
  | 2 => 0x44440212200800321002089012812201028128
  | 3 => 0x110049a088019244a3486000e468088c540ec0
  | 5 => 0x66089203326e249b4c938f2400803331abf000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xffe8ffe8f8e8f8e8ffe8ffe8f8e8f8e8ffe8ffe8f8e8f8e8ffe8ffe8f8e8f8e8ffe8ffe8f8e8f8e8ffe8ffe8f8e8f8e8ffe8ffe8f8e8f8e8ffe8ffe8f8e8f8e8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15050
namespace PEqualNP.Outside.L_meta_15050
open PEqualNP.Outside.L_meta_15050.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x681bf42d037a85a05f94740fb28e817651d02faa3a07d54740baa8e81bf41d037a83a05f55240bf29c81de53902bca7205f54e40eea9c815d53902fca5205f54a40bf28c817d51902fca1206fd0240fda04817f53502f8a6a06f90d40de21a817f52502f8a4a06fd0940dea12817f51502f8a2a06fd0540dea0a81fb405037c80a05f95040bf298817d53102fca4205f54840bf288817d51102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a99877d0f30ee21e617e52cc2faa59877ccb30ee996617e51cc3eca3985d94730bea8e61f551cc2eaa39877cc730ee98e617f548c2fca9186f952309f2a4617d548c37aa9184f55230be2a4617d538c2fca5185f54a30bf28c617d518c2fca1187e90230fca0461df308c3f661185fd5130bf2a2617d544c2f8a89877d0d30ee21a617f524c2f8a49877cc930ee992617f514c2f8a29877cc530ee98a61fa404c3f280987ecc130ef182617f540c2fca8185f55030be2a0617e530c2fca4185f54830bf288617d510c2fca01877cc030fd18061dd300c3f260185fd5320bf2a6417d54c82f8a9905fd4f20bf29e417d53c82f8a7905f94720bea8e41ef21c83da43905fd5220bf2a4417d54882f8a9105fd4e20bf29c417d53882f8a7105f54a20bf28c417d51882fca1107e90220fca0441fa30883f261107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a417f51483eea2905dd4520be28a41f451482e8a2907bc8520f690a41fa40483f280907e8c120fc98241fb20483dc40905fd5020bf2a041be540827ca8105f55020deaa0413d54082f8a8105fd4c20bf29841de53082bca6105f54c20eea98415d53082f8a6105f94820bf28841f651082eca2105f54420faa88417551082fca0107bc8020fd10041ed20083f240105fd5310bf2a6217d54c42f8a9885fd4f10bf29e217d53c42f8a7885fd4b10bf296217d52c42f8a5887d88710fa90e21fa40c43f281887e8c310fc98621fb20c43f041885fd5210bf2a4217d54842f8a9085fd4e10bf29c217d53842f8a7085fd4a10bf294217d52842f8a5085f54610fb20c21f541843ec63087d4c610fb90c21f421842fca1087e88210fc90421f710843f621085fd5110bf2a2217d54442f8a8885fd4d10bf29a217d53442f8a6885fd4910bf292217d52442f8a4887d88510fa90a21fa20443f240887ec4110fb082217f54042fca8086f950109f2a0217d540437aa8084f55010be2a0217f53042fca6087794c10af298217d53043baa6085754c10be298217f52042fca4087b94810b7290217d52043daa4085b54810be290217e51043ec82087d50410fb18821f531043ee42087d08410bf28021fa40043f280087e8c010fc98021fb20043f040087dc4010fd08021f510043f220087c44010
  | 1 => 0xf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442fb28885765110afaa2217d54442baa88857e5010bf4a0215e94042bea8085f95010af2a0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465ee428cbda851977cca32f7994657e518cafaa3195f94232bea84657f544cb7ea8994fd5132bf2a2657d544caf8a8996f151329e2a265de434cbba86997b90932f6a1265ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32efa1865dc430cafca41977cc832f719065dd320cbda64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83be43d077887a0df94b41bea9683bf42d077a85a0df94341fd286837a50d06faa1a0fe54341bca86837d54906fca720f794e41af29c837d53907baa720d754e41bf294837d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a83be435077886a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d53106fca420df54841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f7d0f31ee21e637e52cc6faa598f7ccb31ee996637e50cc7f4a198de94331bea8663f950cc6f2a198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31bf294637d528c6fca318fd90631faa0c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263df434c7b88698dfd4931be29263df324c7ba6498fd90531faa0a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52886fca310fd90621faa0c43f631887ea6310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fd90521faa0a43f631487ea6290fdc8521f710a437f50487f6a090ded4121be28243f850486f0a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81be43d037887a05f94b40bea9
  | 2 => 0x3415e000000670003ac00197472000000003d600000000000000001ac2320008400000000000000186a90e000000018c839d338a919300000004f49d8d7000294001ea29c8ed2e00028000000172000864000003e28b4001164e644c4f8000b414c001561186780002b0004cc0e9500002246d28354a76cee100300934000000000013e000000aa083000546001198f111c000000000001a0f9800000000a688202c000000e70f8001378270ae8d8e08550e43605e000000001429f0000404c922c01403000000000000678382d492c2a1bc1d456800000454a54000000002412b000522001402483480000024f3f8000001b030a6e4d90004f417c5b9fb3863300000000a04c560dc000711188a143038803a090984f835234230000fd0ee23a81d140004226ec37024170928e82240aca894d8e12f26d8bb8004d04b8be8002c8000538003d0000000000000007493f2166c4b70e4000000c302901e71c328001161dc0014f35200021000000000d28003ce000090000000ec4e1140ea819288000729a8f90cd1f20003a0001246e0ca8064dc320000004ea5749894843e604002084e49ecf68002de2345c9fd000000979e21462d0001a344a25c002614c63d91f1a829243cac00052e0002c00000059c001d4000810208140e04d8000d104c0000d0004e200026000050000602c02010000080d000010280400c1a00800010030040805802000130040900002004000180500001008000000002c010080900003018000080300c06038000080100400088010280400405008010180303400000000480100c0b01001024120200000809024000041600c08004030000103c000000000800024020080005c0a03c09014000100e0280000000000000240200c0501002000000280600400000170040700400010000280c008040040201c040000000009024200080002005008000a4020000a0000000800008130040100003000060100500c06008020001400c0001001010070040002c00020010040001c0d02c0100400008010040b01c08004050040000009000170000700001020040000104efca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443fb28887765110efaa221fd54443baa88877e5010ff4a021de94043bea8087f95010ef2a021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855f5350af8a6a17714d42ae29a85b
  | 3 => 0x394000000c02409b0f2130416a253b2302867812900051a8c8002271a497d051521ac88422a6600000000000000280fb9440105d49e0e64343101ea445280007982a17a000321e64ca8f0c888a0306342f0c626a0803f04b3189654591e31262cdf21611e94030a8f182594068be000698eb8ec2a6000001252142c4c4115184a406e9c92846384ea930006f40000018a2d81886b2460884c91200085005a3d1fa00d0806910ea700013a0004a9101df1e067d4ca9f058608000000009f40da7000000059800000908000000000006c81e000001060001302ecce9322b84843d8003b4000000005240008117800095c7a80050c52c0016c0000004205b390001070001009240005c0007b00004300090d2d28c3740007189b25a8a50681c0908e8aa08600257c001d2000718000004da00037a77000000118d40f23f14c000000000000001be99076903000000000000009f91b99b0004b10b86d000974792222b2528001ef2d22c12d98f000000000a4000708860853280000000042a5800002830604534800000000001ad36a0cc0000054232469804000aa42e97c1bc0000016b504988a0800000279078e83e813c95a4506c684fc8194d68149a1d52fe56cb41704b0220d709a000188ff84d28c764001a739e978000ce21a000001fe0007e000000000680a38d03340007784901c6dcdf83714c7748f85915c414da22e23858c200b504aa280019c0000c9092740a00d4b111b2986ccb30812da32c1fa1c52c0e8000000e2628bda7f00011c0000012a99c0000028a000000000008083f9931560f89384e2486bcf480000000000010000730049993c29e52a000396a10001d800014400000000354000000003fc0022b0000000012200031c8ba9e07800000000000000001841647790007805ca80178e50003e0ba0db4821110d8300000841680054c7387f19602a000d116124c7954e91a2e6380cc0ba4aa878c39900d884c5424c50e148fb00010655cbd000000a0501a473ea000d50000ec0003993900005ceb00000018111800000001470bf000000948f700007c4b00000011800000126000000ad0000000022f3c64dc889ab000734000002e20000000040294c5507a3a2000000a900000848800000938332782a2288000005108d47d0002bc1f42522654e4e0848f42ec410001282208e0001550008751f800534000871ee000900bf0ca0003ec4a0
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x540825e63150209758c540827661150209d584540827a60150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209d98453082756114c209e98053083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083706054420d954720083395488020d654e200837151880209bd95200836551480209ed9520083395448020d654d20082f06148020dc545200825e63d53109758f54c423e64d4f108f59353c423e6414b108f59052c425e6314b109758c52c42f06048710b658e40c42b9648c310f848720c42b96408310b658c20c42f161083109798f548425d63d52108f993538423d64d4e108f990528423d6414a109798c528425d6314a10b558e41842b5648c610ad59021842d56308610bc58021842f06148210f8c85208425e63d51109758f544427561951109e582544423e64d4d108f59353442756194d109e582534427761549109ed81524423e64149108f590524425e63149109758c524427665885109d19521442f060485109e99620442786548110bc18520443e121481109798f540425d63d50109b98b540426d62d50108f59654043366195010ce982540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c755253043566194c10d6982530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d52043646154810da181520423e64148108f590520425e63148109758c520426e62148109d984520427a60148109d59641042d56390410d554e41043655290410bc58241043365450410d554d410436552504109d59631042b5648c410cd5523104365528c410bc5823104335544c410d594d3104365524c4109d597210436552c84109d59421042b56408410b558c21043655208410bc58021042796590010b658e40043595390010da54a40042f16190010ce95140043595350010da54940043b141500109e59630042b9648c010ce5523004369528c010bc5863004339544c010d694d3004369524c010f44c5300427965c8010da54b20043e321c80109e59420042b96408010b658c20043695208010bc584200436552c40109e59610043695284010bc58610042776544010d9549100427b6544010da54910042f36544010dcd9510042f36444010bc59110043b25444010ec55110042f36344010bc58d10043d25344010f454d10042f26244010bc18910043735244010f894910043715244010f854910043615244010
  | 1 => 0x867a6094d219e582534863f6454d218f191534867b6054d219e18153486d563905219d19541486b5648c5219d195314863e64141218f590504865e63141219758c504873a6414121ce590504875a6314121d658c50487724114121dc50450487723114121dc4c4504877321141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219d984540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c218f990530863d6414c219798c53086766114c219e98053086796014c21cd552210875553884219bd9521086776548421cd55121087555348421bc181210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b2154021dc88550087692154021dc485500871d5310f40ab58843d02b56110f40a718d42d025e63947409758e51d03566394740d558e51d03364354740cd10d51d03374254740cd50951d033651507409d98653902756194e40d598653903556194e40d6982539031e53d0240bc98740902ad6210d40ad58443502ba6010d409798c525025d63149409d98452502756114940a718d42502ba60d0540bc987405029e63901408fd95401027b65500409d98754cc27561d53309b98854cc26d62153309d98454cc2756115330c755043cc2cd6210f30b558443cc29c644cb308f99251cc23d6494730cd99251cc3356494730d5d0d51cc3544354730d5cc951cc3553254730d594531cc27661952309d586548c3366195230cd586548c33a6095230ce951408c31e54cc230bc987308c27661951309d586544c25e65d0d30c7550434c2cd6210d30b5584434c2da6010d308f990524c23d64149309d984524c2756114930a7191324c2da60cc530b698e404c2786550130e610d404c2f261cc130a7992304c25e63d50309b988540c26d62150309d984540c27561150309e980540c23e64940308f592500c25f654c0309ed95300c25f63553209718d54c825e63153209758c54c827661153209d58454c823f6454f208f19153c823e6414f208f59053c82766114f209d58453c82e860487209798f548825d63d52209d986548827561952208f993538823d64d4e209d98653882756194e20b658e40882b9648c2209d9865448275619512097d8d544825c63551209dd85544827461551209d98653482756194d208fd91534823c6454d209dd8553482746154d208f990514823d64145209798c514825d6314520cd99051483356414520d598c51483556314520dc580514836451c8520b658e404837051901209e19540483705150120ae5923048370518c1209e1953048370514c120dc147204825e63d50209758f540827661d50209d587540823d65950208f99
  | 2 => 0x4354442cdd095110b354254442d694e5010b595394042dc9465010b715194042d694d5010b595354042dc9455010b715154042ce90d5010b384354042ced095010b3942540429d98454cca7561153329e98054cca796015332c715143cca3e64947328f59251cca3e64943328f59250cca7661152329d584548ca7a60152329e580548cb1f5410e32b3588438cb8c4390a32b318d428cb8f4350a329ed81518ca7860546329dd85508ca7461542328f992544ca5f63551329d984544ca7561151329e980544ca7960151328f994544cb1d6315132cb588544cb366115132cd584544cb3a6015132ce580544ca5e6590d32c7152434ca5c6550d32c7151434cb2c5490932e390e424ca6c6550932e350d424cb1c548c9329d987540ca7561d50329e983540ca7960d50328f596540cb1c63550328f990540ca5e63150329b988540ca7661150329d584540ca7a60150329e580540ca5d65d0c32c7553430ca5d6510c32c7550430cacd6210c32c7553320cb2d548c83297d95320ca9c644c832c7551320ca6f654c832cb551320cb365494432cd552510cb365454432cd551510cb574354432d510d510cb573254432d54c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500cb5b4354032d610d500cb5b3254032d64c9500cb1d5310f41ab58843d06b96010f41a718d42d065e63943419758e50d075a6394341d658e50d073a4354341ce10d50d073b4254341ce50950d067a6094e419e58253907566194e41d698253907596094e41c794f41906f260d0641ab58843506b66110d41ae580435065e63149419758c525067a60149419e580525069c6350941bc983415069e63905418fd95411067765504419e98354cc67960d53319b98854cc66d62153319e98054cc6796015331c755043cc6cd6210f31b658043cc69c644cb318f99250cc63d6494331ce99250cc7396494331d6d0d50cc7584354331d6cc950cc75932543319e982548c6796095231cd986548c73a6095231ce582548c7365450631c7953318c6f260cc6319e982544c679609513197997434c71d5410d31b3588434c6d66110d31b6580434c63e64149318f590524c67a60149319e580524c69c644c931b598e414c6746550531e510d414c6f260cc531a7992314c65e63d50319b988540c66d62150319d984540c67a60150319e580540c63e64944318f592510c65f654c4319dd95310c65f63553219718d54c865e63153219758c54c867a60153219e58054c863f6454f218f19153c863e6414f218f59053c867a6014f219e58053c865e63d52219758f548867a60952219e582548863e64d4e218f593538867a6094e219e58253886d56390621ad592318867a60951219e582544865f63551219718d544867b60551219e181544
  | 3 => 0x1d70004d41a85f4da8f51184d336674000e71a6000d887000035d3f990472400000052160000004708c000bc92b000000000c500000073228000000001a24260000000000037c000ea000644000001b426c0010d000000001360106f099057404278000d153e0006f0ac000410000001b62d0e32c9008695129c02381649e1134ea0003a1445360008400000028cbd8c7000000c700000022c00000490000d01dd0000011788205a0f4f20002cc7f800000094000ee1c70009c87216c3b00000b972000214491fb00073c4d0000e47cc000000000000019f0000000026e00000033800492afd450ef1881cc7d96000091d3499300000143a041ba2586e1ab266aa89b9751b25fcd90b30b82fca526b3182992b0680a64ec002c40aa0014906519e2614615b00047800000272201581c53e873894a33548001069523a63280040000000000c0081300001c000060100000000200a01403004000000018050120000100000400c0380102201c0000000400000000000000020040120040180000400000007002000040000160340180700000800800000000008050040100900000000c0c8000080000481701205800001002008048030200000000502c0040000200402c008010060140000500800c0b000000000010000000600300000e0000180001001c000130000080000000200406805004000018000000280000003a018080020060140080001c0040380001200000003000008000020020040000001a004000030000240000000801401004002010028080000000000100a0000080500200401811010000008010040040080002e010060000020080180200400000005002000018000000140080400e0000200a002008060030000000001600400c0800000200c0180500c0067661149439d5845250e7a60149439e5805250e7a60d45439e5835150e7661d41439d5875050e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9f6150c43a7d814310f8d4394843c750d5210f8d4354843cbd0d5210f4e4354843cb50d5210f4d4354843c350d5210f954394443d994a5110f655294443e550d5110f665254443d95495110f994394043da94a5010f695294043dc9465010f715194043e650d5010f6a5254043da5495010f725154043dc5455010e5e63947429758e51d0a5e63943429758e50d0aad6210e429ed815190a7860546429dd855090a7461542429d9845350a756114d429e9805350a796014d42d35885350b566114d42d55845350b5a6014d42d65805350a3e65d0d42c714f4350b1c5350d42c714e4250a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842a718d4210b1d53508429bd954210b4d5350842d594e5110b555394442d594d5110b555354442cd90d5110b34
  | 4 => 0x2144582114306ca44f5a8b24c2f07ba062b000800282000221530cb5380005f0003345dc002d4262000f280000094d2000019aa104bac34cc504670003bc000480e300018c001ca56a031612bd0a8000bf0001286d51a06911486d1daaf0000892c000000000ff91d04896800125000765130003324b4b414e20c0000e90e3a82d40a83740e908f0a354b2000df8002da92c460b625e0000021e5620005c2784a08c0711f13cc40968830416000000eb5a600017800432000001ba00c058000a8474360001ec3de0000000000077c40a834c67e0e416e00046d3a0b90009dd2291a230035528001429f07823f25c824e610722860c862100008e0cb1d6520321352003b40a40f8002ec060000fc0007f4002b4260000c92143ee001320002d4000000002900012500036c1fcab023026000000004781684e1c100089000000594454208004ba8dc1288751e8d8be1f62bc0007a87d56c89cf49983e4190b793a02895c882460a0488ca80004c6c0df0a009800100827558210000a20001d4002151f04e0d30f20003cc000000c08756680055690d2e0894d8b14fe0002c4b18568c33001b47f25b000a8c002b8042000001702f455c0003201c000370004e20f8431aa424a541a00007e000000000cca744e9bb3a40010e22931e000000000008c40005640a5ac0000020629000000000000001db0002c0000953282ec0000000000000109000324000000000001d04e2b400035a975760f00000042216cc110536e238000000ee000000001e878816000174a68079541227e8000f94be114000000560000000035c000ae2522020007613e03c0000000000059c0000000000153aa03120000024e0882acd98fa0006a0e48782bea640000015451400000106000e6ab7000000001780002f4768004ec820000000000000019c03634949a8e000000001a13e0490002cc1521f0002a90004654286a4d04815f000000ae4000b124272cd6ad23704a80007e55a000000000001790d0003dc9948f9c40061d87e9f51dc0ed339c30009840017d000ae808a7d0009103100007049cd795315c00000040000590000f63d0000fca880000e487a790009cc002512e20492784950c0640000018083d3001c258af0000000000000000029aa59570c22b20012f0000f2358d2123372aa0000003aa5303d04f1fe2bc051e342e881110b20deb2cf00cc3100cd0b1730006b0002d041445d401421328c89f9a34549f9071b40007b403a8d0001453d00156414800000000000058000000680000045c0a0001e72e8554cb871000000002c12a260550a2c2965a478a98020628742892220a8002c80006100007b2c6a7931000000000708a54184a000000000000000612a0740002b32800002598b0000004680018c708240203d46a51f0091d2634000000003540018600
  | 5 => 0xb1ce8a0359c160001471265253d934000000360005801746a15d4a8a892a89f2c229d1080000000000000502594de9850009bd678d00625180011205c00070000000a50d38000009c12624143e8b49e80000010c0018716e86000000182394a780011e8accf24d
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x46089abcca300088547a0c324e5a102c002800140400ba5cacc8224c94002000007c0e6856007292a47ec2b686009eb842a816640050a200904a8c986006003a000ab000aa00003696be6678aec41882b2004470587624b4025e8e840000746ea63c00c6401c2a6c9cc0a08062521e2e1226388a481a3e6a0034120068100040040000b0034606830c148000e04000020c0920818202001e4ab88c4a1887265c06250c43932e1b0a8621c9571d814310e863b286a908743dc54354843a1ee0a1aa421f054354a5110f82a1aa4a8887c250d5294043e1286a92a021f11435455010f22b12c229a85925896014d42ca2c2b00a6a15257210d5110a8a39a84a88854a5c84354042a30e6a12a02160f54588438ca473b686a14658358d6215132c4ac4b08a89962962580544cb18b0ac02a265439d64390932c18caa1a849960d54588430ca0e3b2a899065515c84354432a28e8992a2195497210d500ca8c3a264a80658354d6210f41a52e421aa1a0d187350950d0706aa2c421e63525c84354331a30e8992a198e0d54588434c6c2b9086a0a63645c04350531c32c8b18a090d51739045048698ba462282438c5506048421ca2a63024210e0d5358843d0292b9086a8e81451cd4254740c1aa8b1087985457210d51cc28a3a264a8e61835516210d30b12e421a80985917110d404c30ab22c628a419458c5190120c62c828c6090631541852008328a98c290041495d06154810a8ae630aa4085297418152042a4b98c0a90219158d5290410cc2a4b0482086256454a3104330a92c118821895915208410c8ac6a904208661525802104324b1aa520021985496190010e22a6a0a8008721525054004314b22a51802198549618c010e22a898a6008741524c530042b0bae43900219859721c8010c52c8a904008649635482004330a92c210021345cf6444010962e9b1a20087115454d1004258ba0c488021345cc6244010ac2eb29220084707654910043912a2a488021c85515244010e84a6a922008741535491004331bb2a488021981d95244010cc6c8a922008661645491004331b1aa4880219858d5244010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x60c800e4a208905811d94354843909801d9435484390980dc5435484390581dc14354843a21841d95244010a41831d95244010a4183d915244010a2184d8d5244010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 682
  | 4 => 725
  | 3 => 102
  | 2 => 8
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (i*5) 5
  | 6 => packedAt s5K6 (i*16) 16
  | 5 => packedAt s5K5 (i*27) 27
  | 4 => packedAt s5K4 (i*38) 38
  | 3 => packedAt s5K3 (i*49) 49
  | 2 => packedAt s5K2 (i*60) 60
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (20684+((h/227+packedAt s5K5 (18414+(h % 227)*10) 10) % 990)*11) 11
  | 4 => packedAt s5K4 (30201+((h/241+packedAt s5K4 (27550+(h % 241)*11) 11) % 1053)*11) 11
  | 3 => packedAt s5K3 (5236+((h/34+packedAt s5K3 (4998+(h % 34)*7) 7) % 123)*8) 8
  | 2 => packedAt s5K2 (488+((h/2+packedAt s5K2 (480+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x78e3c71fc71fe3f31e3831c7c71f8ff3134cf
  | 1 => 0x7f03f81ff81ffc7c1fc03e07f81ff1fc238f3
  | 2 => 0xf8003ffe3ffe3ff8fe0003ff8ffe3fe003cf3c
  | 3 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 4 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x50e046228542944030a0a905141448ca311445
  | 1 => 0xa10c89450a252808c144522228889614c22892
  | 2 => 0x11000100000010200004801202000004128
  | 3 => 0x32240129a1200c92546918000e4d0246540ec0
  | 4 => 0xc44822400249b124a992639340000498abb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15050
namespace PEqualNP.Outside.L_meta_15050
open PEqualNP.Outside.L_meta_15050.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12d50f0b1a6a317110001c00007803660014b11284020000400f10a9ca63e19d2f6e41a2c3629115481d5bb062ccb20815e80289400000491b30060e0d2638b9d4e38146800038000000d080042c1802a0400002ffd5009fe5402ff55009fc5402ffd4c07fe5302ff54c07fc53027fd0c07fe43007f50c07fc4302ffd480b7f5202ff9480bfd52005f5480bfc52027fd0801fe42007f50809fc4201ffcc801fe32007f4c807fc3202ffd4405fe5102ff54405fc51027fd0405fe41007f50405fc4101ffcc405fe31007f4c405fc31007fc8405fe21007f48405fc2102ffd4003fe5002ff54003fc50027fd0003fe40007f50003fc4001ffcc003fe30007f4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x64001fb8832000ff44190007fc20c8003f61064001ffc4320077f62190007fe10c8003fe0864001fe0432006ffeca90036ff654801bff32a4005bf9952006ffaca90036fd654801bfe32a4005bf19520007fec890002ff6448019ff3224004bf99120007fac890002fd6448019fe3224004bf1912006ffea890033fe544801bfeaa2400cff15120007fec690002ff6348017ff31a4003bf98d20007fac690002fd6348017fe31a4003bf18d2006ffea69002ffe534801bfea9a400bff14d20067fe869002ffe4348001fea1a400bff10d2000dfec490037ff524801bbfa924009ff9492006ffaa4900037d5248013fe292400cffd092004ffc8490003fd4248013fe212400bffcc92004ffc6490003fd3248013fe1924000ffd8520005fec290003f761480017bb0a400aff98520015fcc290003fd6148015fe30a4002bf18520007e8c29000af4614801bffa8a400aff9452006ffaa29002bfc5148019ffa0a400aff90520007fa829002bfc4148017ff98a400aff8c520007fa629002bfc3148013ff90a4000fbc8520057fc4290003fd2148001f690a4009ff0852000dfec090007ff5048003ff2824001ff5412000ff8a090007ff4048003ff2024001fe9012000ffa8090003f94048003fe2024001ffcc12000ffc6090007fa3048003fe9824000fe4c12000ff86090007ff2048013fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffe2090007fe1048003fd0824001ff04120047feca88022ff6544011ff32a2005bf99510047faca88022fd6544011fe32a2005bf19510007fec888002ff644400fff3222004bf99110007fac888002fd644400ffe3222004bf19110047fea88801ffe5444011feaa22007ff15110007fec688002ff634400dff31a2003bf98d10007fac688002fd634400dfe31a2003bf18d10047fea68801bfe5344011fea9a2006ff14d1003ffe868801bfe4344001fea1a2006ff10d10007fec488002ff6244001ff3122009bf98910007fac488002fd6244001fe3122009bf18910047fea4880237f5244011ff2922008ff54910006faa488023fc524400fffa122000ff90910007fa848801ffc424400dff9922000ff8c910007fa648801bfc32440037fb0a2002ffd4510017fca28800bfd5144005fe28a2002ffd0510017fc828800bfd4144005fe20a2002ffcc510017fc628800bfd3144005fe18a2002ffc8510017fc428800bf62144005fe90a2000fd48510017f84288006ff6044003ffa822001ff9411000ffaa088007fc5044003ffa022001ff9011000ffa8088007fc4044003ff9822001ff8c11000ffa6088007fc3044003ff9022001ff8811000ff44088007fd2044001fc9022001ff0811000ffe208800bfb1044003ff0822001fd8411000ff82088007f41044003fc0822001fc04110
  | 1 => 0x7fe5050003fd2828001ff541400b7f2a0a0007fc5050003ffa028004fed014000ffc80a0007be4050003fe2028001ef1014000ff080a0007ff3050003ff1828001fe8c14000ff860a0007fe2050003fd1028001ff0814000ffe20a0057fb1050003ff0828001ff0414000ff020a004fff654c0277fb2a6013ff9953002dfcca9804ffd654c0277eb2a6013ff1953002df8ca98003ff644c0017fb226014ff99130025fcc898003fd644c0017eb226014ff19130025f8c89804fff544c029ff2a26013ff551300a7f8a898006ff634c007ffa9a6003ff94d3001ffaa69800ffc534c007ffa1a6003ff90d3001ffa869800ffc434c001ffb126000bfd8930007fcc498003fd624c001fe3126009bf1893009ffea49804f7f524c027ff2926013ff54930006faa49804ffc524c029ffa126000ff90930007fa8498053fc424c007ff9926003f7cc93001ffc649800ffd324c001ee9926003ff0c930007fec298002ff614c025ff30a6002bf98530007fac29804bfc614c0057e30a6013ffd4530097fca29804ffd514c025fe28a6014ffd0530097fc8298003fd414c025fe20a6003ffcc53001fbe629800ffe314c007fe98a6000f74c53001ff86298003ff214c025ff10a6000ff48530097f84298006ff604c003ffa826001ff9413000ff4a098007fd504c027fca826001ff1413000ffe8098007fe404c003fd2026001ff50130007f28098007fc404c003ff9826003fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007fe204c003fd1026001ff0813000ffe209804bfb104c003ff0826001ff0413000ff02098027ff65c80137fb2e4009ff9972002dfccb900277e65c800b3f32e4009ff5972008dfacb900277d65c80013eb2e4009ff1972004df8cb90027ff64c80137fb264009ff99320025fcc990027fd64c80017eb264009ff1932004df8c990047ff54c8021ff2a64011ff55320087f8a990027ff63c80137fb1e4009ff98f2001dfcc790027fd63c80017eb1e4009ff18f2004df8c790047ff53c801fff29e4011ff54f2007ff8a790043ff43c801fff21e4000ff50f2007ff88790006fe62c8013ffa964009dfd4b2004ffca590027fd52c8013bea964009ff14b2004ffe8590027fe42c8013fea164009ff10b2004ffe6590027fe32c8013fe9964009ff0cb2004ffec390027fe61c80057f30e4009ff58720005fac390027fc61c80057e30e4011ffd4720077fca390047fd51c801dfe28e4010ffd0720077fc8390003fd41c801dfe20e400fffcc720077fc6390003fd31c801dfe18e4009ffc872004fde4390027fe21c8013fe90e4000fb4872004ff84390006fd60c8003ffa864001ff9432000ffaa190007fc50c8003ffa064001ff9032000ffa8190007fc40c8003ff9864001ff8c32000ffa6190007fc30c8003ff1
  | 2 => 0x21015fac39080bff51c8405ff28e4202ff54721017f8a39080bff41c8405ff20e4202ff50721017f8839080bff31c8405ff18e4202ff4c721017f8639080bfe21c8405f710e4202fd88721017f8439080bec21c8413ffb064209ff9832100dfcc190827fd60c84017eb064209ff1832100df8c19087fff50c8439ff286421fff543210e7f8a19087bff40c8439ff206421cff103210effe6190873fe30c8439fe1864209ff8832104ff8419080bff10c8405ff086421cfd84321017f8219080bf410c8437ffb2a421bbfd95210dffcca90816fe6548437feb2a421bbf595210dff8ca90816fc6548401ffb224200bfd91210d7fcc890812fe6448401feb224200bf591210d7f8c890812fc6448437ffaa2421aff951210dffaa89086bfc5448401ffb1a4200bfd8d210cffcc69080efe6348401feb1a4200bf58d210cff8c69080efc6348437ffa9a4219ff94d210dffaa690867fc5348435ffa1a4219ff90d21007fa8690867fc43484057fb12421bffd49210defea490827fe5248437fea924200df5492104ff8a49086bff4248413ff2124200ff5092104ff88490867ff3248413ff1924200ff4c92104ff8649080aff6148405ffa8a4202ff94521017faa29080bfc5148405ffa0a4202ff90521017ec829080bfd4148401faa0a4202ff10521017fe629080bfe3148405fb18a4202ff4c521007ea629080bfc3148405ff90a4209fdc8521017fc429080bee2148405fe10a4202fb08521017e84290803ff60484017fb024200fed8121005f6c090863fe60484037f3024200ff581210c7f8c090806fc6048401fc3024201be181210dffea090863fe5048437fea824218ff141210d7fe8090863fe4048431fe2024219ffcc1210c7fc6090863fc3048431ff1024209ff08121017fe209080bf71048405ff0824202ff041210b7fecaa005aff655002dff32a8005bf995400b7facaa005afd655002dfe32a8005bf1954000dfec8a0013ff5450009ff2a28004ff55140027f8a8a0003ff63500017fb1a8017ff98d4001dfcc6a0003fd635002ffe31a8003bf18d400b7fea6a005ffe535002dfea9a8017ff14d40027fe86a0013fe4350009fea1a8004ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0026fc625002dffa928016dfd49400b7fca4a005bfd5250001bea928016ff14940027fe84a0013bf4250009ff2128004ff509400077a84a0013fc425002fff9928000ff8c940007fa64a005ffc3250001ffb0a8000bfd85400affcc2a000afe6150001feb0a8015ff18540015f8c2a005bff515002bff28a8016ff545400aff8a2a0013ff4150009dfa0a8004ff90540027fa82a0003bd4150009fe20a8017ffcc5400affc62a0003fd315002bfe18a8000ffc85400affc42a0003fd215002bfe10a8001bfd814000ffea0a000
  | 3 => 0xfb128200bfd8941007fcc4a0803fd6250401fe3128209bf1894112ffea4a08977f525044bff2928225ff54941006faa4a0897fc5250409ffa128204efd0941027fc84a0813fd4250401dea128204ff10941127fe64a0803fe3250401fe9928224ff0c941015fec2a080bff5150405ff28a8202fd94541017faa2a0897f55150405fe28a8202ffd0541027ee82a080bfe4150405df20a8202ff105410177882a080bf44150405ff98a8202ff8c541017ec62a080bfc3150405ff10a8202fd88541017f842a0803ff60504017fb028223ff9814100dfcc0a0803fd6050447fe3028201bf1814112ffea0a088ffe505044bfea828223ff14141027fe80a0813bf4050409ff2028204ff10141127fe60a088ffe3050447fe1828223ff8814111ff840a080bff1050405ff0828223fd84141017f820a080bf41050445ffb2a6222bfd9531117fcca98816fe654c445feb2a6222bf59531117f8ca98816fc654c401ffb226200bfd913110ffcc898812fe644c401feb226200bf5913110ff8c898812fc644c445ffaa26221ff95131117faa898887fc544c4057fb1a6203ffd4d3101ffca69880ffd534c407fe29a6203ffd0d3101ffc869880ffd434c407fe21a6200ffd8931005fec498803fe624c401feb126200ff1893104df8c49888bff524c445bfa926222ff94931117faa4988037d524c445fe2926221ffd0931007fc8498803fd424c443fe2126203ffcc93101fbe649880ffe324c407fe9926200f74c93101ff8649880aff614c405ffa8a6202ff94531017eca29880bfd514c445faa8a6202ff14531017fe829880bfe414c405fb20a6202ff50531007ea829880bfc414c405ff98a6203fdcc531017fc629880bde314c405fe18a6202f70c531017e8629880bfe214c405fb10a6202ff08531007fec098802ff604c441ff3026201bf98131007fac098883fc604c4037e3026222ffd4131107fca09888bfd504c441fe2826221ffd0131107fc8098883fc404c407ff9826203f7cc13101ffc609880ffc304c441ff1026220ff08131017fe209880bfe104c441fb0826202ff04131017e82098827ff65c84137fb2e4209ff9972102dfccb908277e65c840b3f32e4209ff597210fdfacb908277d65c84013eb2e4209ff1972104df8cb90827ff64c84137fb264209ff99321025fcc990827fd64c84017eb264209ff1932104df8c99087fff54c843dff2a6421fff553210f7f8a990827ff63c84137fb1e4209ff98f2101dfcc790827fd63c84017eb1e4209ff18f2104df8c79087fff53c843bff29e421fff54f210eff8a79087bff43c843bff21e4200ff50f210eff8879080afe62c8413ffa964209dfd4b2104ffca590827fd52c8413bea964209ff14b2104ffe8590827fe42c8413fea164209ff10b2104ffe6590827fe32c8413fe9964209ff0cb
  | 4 => 0xbbfc1050813ffb2c6409bfd963204ffccb19016fe658c813bf32c64059f9963204ffacb190b6fd658c813beb2c64009f5963204ff8cb19026fc658c813ffb246409bfd923204ffcc919012fe648c813feb246400bf5923204ff8c919026fc648c85bffaa4642cff9523216ffaa9190b3fc548c8077eb1c6403ffd4e3201ffca71900ffd538c807fe29c6403ffd0e3201ffc871900ffd438c807fe21c6409bf98a3204ffea5190277f528c813ff2946409fb94a3204ffaa5190277d528c85bf6a946400db54a3204ff8a519027ff428c813ff2146409fb90a3204ffa8519003ed428c813fe2146409ffcca3204fbe651900fef328c813fe1946409fb0ca3204ffec319027fe618c8057f30c6409ff58632005fac319027fc618c8057e30c642dffd463215ffca3190b7fd518c857fe28c642cffd063215ffc83190affc418c807ff98c6403ff8c63201ff86319027fe218c813fe10c6409ffd823204ffcc119006fe608c813feb046400bf5823204ff8c119006fc608c85bffa84642aff9423216ffaa1190abfc508c859ffa04642aff90232157f8811900fff308c807ff1846403ff0c23204ffc4119027fc208c857ff884642aff84232157f821190a7ff654c8537fb2a6429ff9953202dfcca990a7fd654c8537eb2a6429ff1953202df8ca99003ff644c8017fb226428ff99132025fcc899003fd644c8017eb226428ff19132025f8c8990a7ff544c851ff2a26429ff55132147f8a899026ff634c807ffa9a6403ff94d3201ffaa69900ffc534c807ffa1a6403ff90d3201fbc869900ffd434c801eea1a6403ff10d3201dfec4990a7ff524c853bfa926409ff9493214fdca4990a7fd524c801bea926429fb54932006daa499027fc524c851ffa126409ff90932007dc8499003fd424c801f6a126409ff1093201ffe649900fef324c813ff1926409f78c93204ff86499027dc324c807f61926400ffd8532005fec29909ffe614c8057f30a6400ff5853213ff8c29900afc614c853ffa8a6427ff9453214ffaa29909ffc514c851ffa0a6427ff9053213ff8829900fff314c807ef98a6403ff8c53201ff8629909ffe214c813fe10a6400ffd8132005fec09909bfe604c8037f3026400ff58132137f8c099006fc604c853ffa826426ff9413214ffaa09909bfc504c851ffa026426ff90132137f8809900fff304c807ef9826403ff8c13201ff8609909bfe204c813fe1026427ffc4132137fc209909bfc104c84bffb2a8225bfd954112ffccaa0816fe655044bfeb2a8225bf5954112ff8caa0816fc65504057fb228204ffd5141027fca8a0813fd5450409fe2a28200ffd8d41005fec6a0893fe63504077f31a8200ff58d41127f8c6a080efc635044bffa9a8224ff94d4112ffaa6a0893fc5350409ffa1a8204ff90d41027fa86a0813fc4350401f
  | 5 => 0x8d52006fac6a90e37c6354873bfa1aa438df90d52006fa86a90e37c435480bbfb12a4059fd895202edec4a90e77f4254813be212a438dfcc95204ef864a90037f615486fbf30aa400df585521bef8c2a90e77f415486fbf20aa437df105521c6fe62a90df7e315486fbe18aa437df8855204ef842a90037f605486dbf302a400df581521b6f8c0a90e77f405486dbf202a436df101521c6fe60a90db7e305486dbe182a436df8815204ef840a90df7f105486dbf082a436df0415204ffecb21026ff6590813ff32c8405bf9964204efccb210167e6590813feb2c8435bf5964204efacb210027d6590813fe32c8409bf19642025fac921013ff5490809ff2a48404ff55242027f8a921027ff6390813ff31c8403bf98e4204ffac721002fd6390813fe31c8409bf18e421affea7210d3fe539086bfea9c8434ff14e42027fe8721013fe4390809fea1c8404ff10e4204dfcc521027ff5290813bfa948409ff94a4204fdca521027fd5290813bea948435fb54a42006daa521027fc5290813ffa148409efd0a42027de8521027fc4290813f62148409ffcca4204ff86521027ff6190813ff30c8402bf9864204ffac321002fd6190813fe30c8402bf186421affea3210cffe519086bfea8c8433ff14642027fe8321013fe4190809fe20c8434ffcc64219ffc63210cffc3190813ff10c8409ff0864204ffec121027fe60908037f3048409ff58242005fac121027fc60908037e3048435ffd4242197fca1210d7fd5090865fe2848404ffd0242027fc8121013fc4090869ff9848432ff8c242197f86121027fe2090813fe1048433ffc4242197fc21210cbfc1090863ffb2a8431bfd954218ffccaa1016fe6550863feb2a8431bf5954218ff8caa1016fc65508137fb228404ffd5142027fca8a1013fd5450809fe2a28400ffd8d42005fec6a10c3fe63508077f31a8400ff58d42187f8c6a100efc6350863ffa9a8430ff94d4218ffaa6a10c3fc5350809ffa1a8404efd0d42027fc86a1013fd4350801dea1a8404ff10d42025fec4a10c7ff5250863bfa928409ff9494218fdca4a10c7fd5250801bea928431fb54942006daa4a1027fc5250809ffa128404fbd094204ffc84a1027be4250813fe2128409ef10942027d884a10c3ff3250813fe1928400ffd8542005fec2a10bffe61508057f30a8400ff5854217ff8c2a100afc6150863ffa8a842fff9454218ffaa2a10bffc5150809ffa0a8404efd0542027fc82a1013fc4150861ff98a842fff8c54217ff862a10bffe2150813fe10a8400ffd8142005fec0a10bbfe60508037f3028400ff58142177f8c0a1006fc6050863ffa82842eff9414218ffaa0a10bbfc5050809ffa028404efd0142027fc80a1013fc4050861ff982842eff8c142177f860a10bbfe2050813fe102842fffc4142177fc20a1
  | 6 => 0x200000a01000003004008030030000040000100801400003020004030070360040000000c038008450000040280100c014018020040000000e00e0840c001036014000020040100100a00c00001001002018068010000100300b02800402803014010040000080040200b01201c0100000200c0000a01200004806000060030040060840380200009800005008010068030080300c8020060500b00502600001007000004070000020140000000c0180100000200c0600601e000000020140040280c00400805803004020090010060540300e00003000000004000000040080140200101e028000010140340480600401408004000000008060000000680f004074020050140000003000000c0300000c0000780100800000005018008088030060000380200c044010000340000a0020060240000005408002800020004020030040000280100601401000004024000000000240100200a0000100000600000804000000000070000100200300001c0b80d00600800812002000028010000000480b04e01400800000000028050060100000e0020040981300a008040000000480a80601e000010010080140700300a0240080201e000000010020240a80201a000038070260140480600400c01802006000008000220000000c0000b00500100000c010080100080380401c0000580500008000003008010018090000340000001201800816016028000040040000980401a0000900100401001000000000000070120100282b0020500080300a00c000360140000200000600479ffb2a863cbfd9543006fecaa18027f6550c79ff32a8605bf995431e7facaa18f2fd6550c79fe32a8605bf195431e6f8caa18167c6550c077fb228604ffd5143027fca8a1813be5450c09feaa2863cef55143027f8a8a180eff6350c07ffa9a8603ff94d4301fbca6a180ffd5350c79eea9a8603ff14d4301ffe86a1813df4350c07ff21a8603ef90d4301ff886a180fbc4350c07ee21a8603e710d43007fec4a1802ff6250c01ff3128600ff58943007f8c4a1826fc6250c79ffa92863cdfd49431e7fca4a18f3fd5250c79fe2928604ffd09430277e84a1813fc4250c07ff9928603f7cc94301ff864a1803ff6150c017fb0a863bff98543015fcc2a1803fd6150c77fe30a8602bf185431e7fea2a18effe5150c79fea8a863bff14543027fe82a1813fe4150c09fe20a8603ffcc54301ffc62a180ffc3150c77ff10a863bff08543007fec0a1802ff6050c75ff3028601bf98143007fac0a18ebfc6050c037e302863cffd41431d7fca0a18f3fd5050c75fe2828604ffd0143027fc80a1813fc4050c07ff9828603ff8c14301ff860a18ebfe2050c75fe102863bffc41431d7fc20a18ebfc1050c01bfb22a439df99152006fac8a90e77c6454801bfb1aa438df9
  | 7 => 0x54e0004ba24b1ef0a74313ea4cf4ac0004700000000050000002120000a95610000004b12fe38639400047824650819700058858600051c00049f44c44e3c90eb1d21794052f700022100013f32a5291c855456d0001af0001ad0000c700016a3260000001fe3de08258100026e40710156e1dc33300b3cd0f23ce0fb52013550f25e13717b3540002073ac4a900000017c00015e11d36f09d08d23b27b4de00252d26636e3993e834a0650001ee00000043728b17102d2052b75365594c001645428a2b92d54212d633b0f82df39b3ff5134f522900048536105451558c5514bc16229b14a0a31f30213c501f41400001d0005690561f12e556800018551d00035b0001321f03f625500037924a50e0313d600021300026a09e4c848900022429348a06a04353d46c0000670001340000000710000001872b858239c55500021e14600002914e32c52c3d03480000dd57717d35600047942533a0000000640e80000005314db0000de05500038845a3664163310000000000005710001033ec3d70002494270000be0000000000000000000002ec3e529726f07f58035305117055228f3144af2e653c3d31bd3bf1db19f04237838b3035841b43f22b23b609f2a44425464920662a500335c0004192f30254440ec0004e045b13a4011c223f0c025003b2771cd13b48c03a08a16f44f29921537b4df37d1480870c240d0860bf00057515a0062393f000000000000044d37a26300f0a401153502f00049a29420c00000011c1d40922aa3b832219c4b90a019d26d00039d05035700047d14f3d402a47b57a57d5582573e31860471ca00030800000057b2d352e19600012152f5784f70000002180000000005170c14d229155c0c85280000e34c52b10002764f94024c63492412ba3f412a00030a30b0003552ef29d0270000001b734b4d800000024307a0000000100570002683842d83651564394cc0334e316d0003000681aa12e0000005701ba03f15c2da42945d2a94f632508e0001ab4280004900d800000010b2170000c957e0883dc0ad2f42be04635d4f800051e0ae0000000004914170000000000000001943c454c2ae34739f18c17622f51f3b52ac1a207816810d1522ab0a210e0753293890003fe0f331612704b40a5210494ae18e57439522214055600000054543a2cc4fb0932ca0482db3a20003580b343c4ab4e630c4c940b23d38f1803750e203e20625f50c38a0000004430003ba4e54d40004200f60005854d31d026700050d38d1c900000000000020420942c0004452bd3c84114980530905534b500000048107700000500206c000040000340380200c0000000604604805801002000000200000000381a00a0580c8000040440300000400402008000000008120000080500700a0000080b0140040d00000401c048120060
  | 8 => 0x47c0004522641da50229046e2534ff55f0005041b82021020000264c11360cc0bd10601a48f48d48e0121ce57906013845907b4d60003b012d00000033f37e2cf16916339804d3e20000001a800011e0001470003761923c60000002a80d60000003a34be1770002790003f70000000a800040032d2dd04531d0002252a34730002ee0690001810143f82cd49531e5900003d83e71f51ea06b58e5400390001882ea3245733200002ed0cd54723834400014d22c0001dd0000db0003db0005250000004470001e000030400046f0002e70000003dd1d100000000004c2f918418d4580aa4a40ab18b08c3da2980000000000002f800000032800050b18a1e741e3a40e65035051fa1e800000018202e36437c12b3412350001bb4dd31f1231ff1254b03c75142000ee0f135e47f4c349308f2f50010794c24f20000000000ed0001c400000000000000032302033710700000000012f4e128649745100041f27a4c70000000960004e257c2a71d35623eb0004964990000004fc20d5420000000f92d000033e2f20b155701500000000004444116b1d800021630d00007d5393ee0ac20e3f130e4300000001243a90000590000001570000004b600049433436700000030128400000000000000036a1a52d916e3b400000015d09751b5723461670000000004e923a0003ef0002c63182fa0002c805f2263820000000004260003f520a00015f2540f51f71220d55655440000003a63ad0ef0a14b71bc00019b0d04f33431a90000004e41100e14693b11110002592ad1b916400000019529c00029642a05835142b22d30627c0d740c2f608921d00004a2d70004634dc49e1050323c03215094040174740df2730fd1b626100000007e1c100002c4fd00a0000980fa15134c0002835891bf3171fb5500d111600807405e23116c3fb3624d70b05874060001fd3962202c71be4aa4222c53a01420000000000000000000000003970001541d943227047114500000000029e2fb0003100003350f731a2420000344e72650000000e01934e831c21b0000002a01260991cb32f1090000000043fc0000001a100000000031942d1280000ea47720b4b80360002620000761fc53705b0003a80000630000000001122e100000026c2bc00011558d0000004563c20001d50d927e00000056f03d4602445180005190ce22e46828e2450002560004570000000b63b90ff0193323520a51f41a400052400041511a34000008041d1184a70950241c50000000003851e428800000000011706e4a53121e506f0000002e334d00017434e0000003870003bc1a62285411ae21123200005a00029a00011f0624bf0002e801e0cf3634da4f40001d700038114c03057f46635a1e62fc01c3fd58300003c0004ee0c61f900019a2bb27154d0001cc56c000516359
  | 9 => 0x17830f00041a4f02b614445f3ca0c34750000a600033800017a0004cd12c0001144552ff34210f00000043b0e400009a4eb33932e00000000037100004f28753413000000000000000055b0000000ba0b200041c2c901b2952cb00007c3a145c28c00053a00000000026b00055e5431553ae0000002521a74ca53b1603f340802b4b42032b406d0222b03150b705200040e4fa4833110002142dc0b51980001df43e00042f00040300010442e0004860000b425a0001e90000000000000004d50bb29222737304e25c38322a2b50000004ea3fa4d90d43ed0000000003c134f1730001e14640281e24f123e0000000f00001c32a60000001eb0000004ad4610000004123724620000004ed25b23646d4344ef00d49d39341800053356b00039113d2750e50000000000005065270004ec44848027444a1131b12af4a01c70000002b309b00900027d00014100050a52258b5263a540f23356000c00001800054b0ca0003cb3cc3f928500000008400043d31b00e2de14330542335f0004840001ed2f00001530000413362fd38e09437454908b0fe51a39e4d009c2081b30004530002d45300000832892303692014330000001e32192e200038c2480b837f1500000002473e648736b3e10d20721311333ab0cb3df1593074820001a01915642c218f23c1de3aa15b1194c45100af55d21036c2690913504385381581754364764671084882823c33700e724d4350fc2d12e40004ce55a00052b0002370001d65320005070403b73093800dc3cf0da54f3450b94a60000000005111653b20c442456628033c1a32c000000000044600058f00000045e00047a1c00001390d33d506c3e023407008120f1905914a13a70731005001b04fe43f4cb2e00134a32401c646b46a41b1f82c43bd25d2f15764d137749c53e3af46519e47e33d1b510a2582c114b33056a1f61ec3e421c18354a05d5232eb36d10c1cf26013c27239222329f28148b11b24c1613d14bd0854494093be1203132e93274721b24130c517f00758a0003d232b3024b236803506117e4bb22b4503bb53f5670003902a20004a225113e4b339a0bc2a10e92bf27f28d44044b24f00021f00000000000017214954836049b1ac03824e2ce0f40372d21990000000000003b30235630002781660001293d905c5124a800021a3e900052a1892c31f25014100
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe70d8910014fd70d891000cfc70d8910216ef20d8910216ed20d89100c4fd76989100457e75989100057d7598910006ef62989100c5f571989100e6f76198910055f97098910076fb60989100e7f0109891004cff76589100e5f77158910075fb70589100c7f01058910004ff755891002cfe7558910004fd755891002cfc7558910004ff7458910024fe7458910024fc7458910004ff735891001cfe735891001cfc7358910006ef72589100067f52589100e4ff7158910006f771589100e4f771589100c4ff7058910006fb7058910074fb7058910214fe76189100457e75189100057d751891003dbe7418910005bd7418910035de7318910005dd731891004eee6218910006ed6218910206f7611891020efb6018910207f010189100067f76549100067e76549100067d76549100067c76549100067f64549101ce7e64549100067d64549101ce7c64549100067f63549101c67e63549100067d63549101c67c63549101fd7f72549100476f72549100067f62549100076f62549100066f625491004e7e62549100067d625491004e7c62549100076c625491004e6c62549101b67f61549101bf7621549101b67f60549101b77a20549101bf7b10549101b77610549101b77410549101b77810549101b770105491004cff7690910004fe7690910004fd769091004cfc76909100457e75909100057d75909100076d5290910015f67190910005f5719091000dfa7090910005f97090910197f01090910004ff7650910004fe7650910004fd7650910004fc7650910026be6450910006bd64509100076d5250910177f0105091004cff768c910004fe768c910004fd768c91004cfc768c9100457e758c9100057d758c9100076d528c910015f6718c910005f5718c91000dfa708c910005f9708c910157f0108c910004ff764c910004fe764c910004fd764c910004fc764c91001ede634c910006dd634c9100076d524c910137f0104c91000df4764851004ef4764851000cf47648510006f76448510006f56448510006f76348510006f56348510015f77248510017e77248510007e7624851004ef6624851004ef46248510007e462485101f7775248510007755248510007f3704851000df6704851000df470485100c7f0704851000df07048510016f76048510017f360485100c7e720485100c7f220485100c7e52048510015f8764811004ef87648110014f87648110006fb6448110006f96448110006fb6348110006f9634811000dfb724811000feb7248110007eb624811004efa624811004ef86248110007e862481101ef7b5248110007795248110007f37148110015fa7148110015f87148110057f07148110015f0714811000efb614811000ff36148110057eb2148110057f22148110057e92148110007f12148110007e12148110
  | 1 => 0xc12000efb624c12000feb624c1202677b524c12000779524c12005fdb324c120007d9324c120005fb714c120007f3614c120096fa614c120096f8614c120007f0614c120096f0614c12005fdb314c120007d9314c120007eb214c120007e9214c120024fe76d911003ebe64d911024ff010d9110004ff75d911002cfe75d9110004fd75d911002cfc75d911011cfd74d911001cfe73d9110004fd73d911001cfc73d911004cfe72d9110004fd72d91100067f52d911000cff71d9110014fe71d911000cfd71d9110014fc71d911025ebf41d911025ebd41d911025ef621d9110014ff70d911000cfe70d9110014fd70d911000cfc70d911024ebf40d911024ebd40d911024efa20d911025efb10d911024ef610d911024ef410d911024ef810d911024ef010d9110024ff765911003ebc6459110245f77159110255fb705911011ff01059110004ff755911002cfe7559110004fd755911002cfc755911024cff7459110006bf7459110004ff735911001cfe735911001cfc7359110004ff725911004cfc72591100067f525911003ebf4259110244ff7159110006f771591100aef6215911011cff7059110006fb705911011efa20591100aefb105911011ef6105911011ef4105911011ef8105911011ef0105911001cfe76d8d10036de63d8d1022ff010d8d10004ff75d8d1002cfe75d8d10004fd75d8d1002cfc75d8d10024fe74d8d10004fd74d8d10024fc74d8d10104fd73d8d1004cfe72d8d10004fd72d8d100067f52d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d1023edf31d8d1023edd31d8d1023ef621d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d1022edf30d8d1022edd30d8d1022efa20d8d1023efb10d8d1022ef610d8d1022ef410d8d1022ef810d8d1022ef010d8d1001cff7658d10036dc6358d10225f77158d10235fb7058d10107f01058d10004ff7558d1002cfe7558d10004fd7558d1002cfc7558d10004ff7458d10024fe7458d10024fc7458d1022cff7358d10006df7358d10004ff7258d1004cfc7258d100067f5258d10036df3258d10224ff7158d10006f77158d10096f62158d10104ff7058d10006fb7058d10106fa2058d10096fb1058d10106f61058d10106f41058d10106f81058d10106f01058d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100457c7550d100379c4350d101d7f01050d1004cfe76d8910217f010d8910004ff75d891002cfe75d8910004fd75d891002cfc75d8910024fe74d8910004fd74d8910024fc74d891001cfe73d8910004fd73d891001cfc73d89100067f52d8910006ee52d8910006ed52d891000cff71d8910014fe71d891000cfd71d8910014fc71d891021eef21d891021eed21d8910014ff70d891000cf
  | 2 => 0xe6f740d85200e6f640d85200e6f540d85200e6f440d85200e6f730d85200e6f630d85200e6f530d85200e6f430d85200e6f720d85200e6f620d85200e6f420d8520056f461585200e5f67618520056f67618520057767518520057757518520006f76518520006f66518520006f56518520006f46518520057b67418520057b57418520006f76418520006f66418520006f56418520006f46418520057d67318520057d57318520006f76318520006f66318520006f56318520006f46318520207e57218520206f76218520007775218520007755218520207f27018520057f17018520206f76018520076f36018520207f24018520207f2301852027ff32018520207e62018520207e42018520207f02018520004ff7650520004fe7650520004fc7650520026be6450520006bd6450520006f76150520016f4615052000dfa705052011ff21050520004ff764c520004fe764c520004fc764c52001ede634c520006dd634c520006f7614c520016f4614c52000dfa704c520107f2104c520205ee76c852004eee76c852004f6e75c852004f6d75c85200c5ed71c85200e7e761c8520016ee61c8520016ec61c8520057e461c8520016e461c852004feb70c852000dee70c852000dec70c852004fe870c852004eef60c852004feb60c85200e7ea40c85200e7ea30c85200e7e610c85200e7ea10c85200e7e210c85200e7e410c852000cfc76485202776f52485200076d5248520006f76148520016f4614852004fe42148520005fb704852000df8704852004fe8204852000dec7648520016ec764852000cec764852004def714852004fe77148520007e76148520016ee6148520016ec6148520057e46148520057e64148520007e54148520057e63148520007e53148520007eb704852000dee704852000dec70485200c7e8704852004eef604852004feb60485200c7ea40485200c7ea30485200c7e710485200c7ea104852004df87650120026f8765012004cf8765012026efb655012026ef9655012000dfb745012000fbb7450120007bb6450120026fa6450120026f86450120067b86450120005fb7350120006fb6350120006f96350120007eb725012004dfa725012004df87250120007e8725012000efb625012000feb625012026f7b5250120007795250120067bb4250120007b94250120005fb7150120007f361501200aefa61501200aef86150120007f061501200aef06150120067bb4150120007b94150120007eb2150120007e9215012004df8764c12001ef8764c12004cf8764c120266fb654c120266f9654c120005fb744c120005f9744c120006fb644c120006f9644c12000dfb734c12000fdb734c120007db634c12001efa634c12001ef8634c12005fd8634c120007eb724c12004dfa724c12004df8724c120007e8724
  | 3 => 0xf3158d20134ff7058d20006fb7058d20136fa4058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d2006d7c7550d2005f9c4350d201def46150d2000dfa7050d2002e7f76549201b67e76549201b67d765492002e7c76549200067f64549201ce7e64549200067d64549201ce7c64549200067f63549201c67e63549200067d63549201c67c635492004d7f725492006f6f725492004e7f625492004f6e425492004f6e32549201be7e61549201be7c61549201be74615492004f6f21549200077b70549201b778705492004e7f60549201b77a40549201b77a305492004f7b20549201b76e205492004f6c205492004f78205492004f6820549201b77a1054920024ff765092000cfe7650920174fd765092000cfc7650920006bf6450920026bc64509200076d525092017ef46150920005fb705092000df8705092001cff764c92000cfe764c920134fd764c92000cfc764c920006df634c92001edc634c9200076d524c92013ef4614c920005fb704c92000df8704c920014fe76d8520056f661d8520004ff75d852002cfe75d8520004fd75d852002cfc75d8520024fe74d8520004fd74d8520024fc74d852001cfe73d8520004fd73d852001cfc73d852000cfd72d8520014fc72d85200067f52d85200067d52d8520006f751d8520056f651d8520006f551d8520056f451d8520006f741d8520056f641d8520056f441d8520006f731d8520056f631d8520056f431d8520056f621d852000cfe70d852004cfd70d852000cfc70d85200e6f710d8520205f676d8520014f676d8520006f765d8520006f665d8520006f565d8520006f465d8520006f764d8520006f664d8520006f564d8520006f464d8520006f763d8520006f663d8520006f563d8520006f463d85200e7e772d85200077752d85200077552d8520287f370d85200e7f070d85200e7f240d85200e7f230d8520287f320d85200e7e620d85200e7e420d85200e7f020d8520006f775d8520006f675d8520006f575d8520006f475d8520006f774d8520006f674d8520006f574d8520006f474d8520006f754d8520006f654d8520006f554d8520006f454d8520006f773d8520006f673d8520006f573d8520006f473d8520006f753d8520006f653d8520006f553d8520006f453d8520006f743d8520006f643d8520006f543d8520006f443d85200e6f772d8520056f672d85200e6f572d85200e6f472d8520006f752d85200067752d8520286f652d8520006f552d85200067552d8520286f452d8520006f742d8520286f642d8520006f542d8520286f442d8520006f732d8520286f632d8520006f532d8520286f432d85200e6f770d85200e6f670d85200e6f570d85200e6f470d85200e6f750d85200e6f650d85200e6f550d85200e6f450d8520
  | 4 => 0xf20006bd6450f2001ede6350f20006dd6350f2007f9c4350f20004ff755872002cfe7558720004fd755872002cfc7558720004ff7458720024fe7458720024fc7458720004ff735872001cfe735872001cfc735872000cfe7258720014fd725872000cfc725872004e7f525872004e7d525872004ef77158720076f64158720076f6315872004ef7215872004ef42158720076fb705872004efa205872004ef920587200c6f71058720076fb10587200c6f81058720004ff7650720004fd765072004cfc765072012e7e65507200067d6550720026be6450720006bd6450720016f66150720006f56150720005fb705072000df8705072011ff01050720004ff764c720004fd764c72004cfc764c7201167e654c7200067d654c72001ede634c720006dd634c720016f6614c720006f5614c720005fb704c72000df8704c720107f0104c72004def764872020eef764872004f6e654872004f6d654872004fe7714872004fe76148720016ee6148720016ec614872004fe46148720077e64148720007e54148720077e63148720007e53148720077eb704872000dee704872000dec70487200c7e8704872000de870487200c7e71048720077eb1048720077e310487200c7e81048720024fe76d9120066be64d9120004ff75d912002cfe75d9120004fd75d912002cfc75d912001cfe73d9120004fd73d912001cfc73d912004cfe72d912000cfd72d912004cfc72d91200067f52d9120066bf42d9120014fe71d9120004fd71d9120014fc71d912004cff70d912004cfd70d9120196bf40d9120196bd40d9120196fa30d9120066bc6459120295ef7259120005f77159120055f47159120004ff755912002cfe7559120004fd755912002cfc7559120194ff7459120006bf7459120004ff735912001cfe735912001cfc7359120294ff7259120006ef72591200067f5259120004ff7159120006f77159120004f77159120014fe7159120014fc7159120006f47159120014f47159120066bf4159120174ff7059120006fb7059120176fa305912001cfe76d8d2005ede63d8d20004ff75d8d2002cfe75d8d20004fd75d8d2002cfc75d8d20024fe74d8d20004fd74d8d20024fc74d8d2004cfe72d8d2000cfd72d8d2004cfc72d8d200067f52d8d2005edf32d8d20014fe71d8d20004fd71d8d20014fc71d8d2004cff70d8d2004cfd70d8d20156fa40d8d20156df30d8d20156dd30d8d2005edc6358d2028def7258d20005f77158d20055f47158d20004ff7558d2002cfe7558d20004fd7558d2002cfc7558d20004ff7458d20024fe7458d20024fc7458d20154ff7358d20006df7358d2028cff7258d20006ef7258d200067f5258d20004ff7158d20006f77158d20004f77158d20014fe7158d20014fc7158d20006f47158d20014f47158d2005ed
  | 5 => 0x16f461c853000dfa70c8530005f970c85300e7f010c8530004ff7648530004fe7648530004fc764853001dde7348530005dd7348530016f66148530007d53148530005fb704853000df87048530097f3104853001df87650130026f8765013001cf876501302a5fb75501302a5f9755013029efb655013029ef9655013000dfb745013000fbb7450130007bb6450130026fa6450130026f864501300a7b86450130007db735013001dfa735013001df873501300bfd8735013000efb635013000fdb6350130005fb7250130006fb625013029f7b52501300077952501300a7bb4250130007b942501300bfdb3250130007d93250130095fa7150130095f871501300aefa61501300aef861501300a7bb4150130007b941501300bfdb3150130007d931501300067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c73597200067f43597200067e43597200067c435972004e7f725972004c7f725972004e7e725972004e7d725972004c7d725972004e7c725972004e7f425972004e7e425972004e7d425972004e7c425972004e7f325972004e7e325972004e7d325972004e7c32597200067f71597200067e71597200067d71597200067c71597200067f41597200067e41597200067c41597200067f31597200067e31597200067c315972004e7f215972004e7e215972004e7d215972004e7c21597201b67f70597201b67e70597201b67d70597201b67c70597201b67f40597201b67e40597201b67d40597201b67c40597201b67f30597201b67e30597201b67d30597201b67c305972004e7f205972004e7e205972004e7d205972004e7c20597201b67f10597201b67e10597201b67d10597201b67c1059720004ff755932002cfe7559320004fd755932002cfc755932004ebf7459320004ff735932001cfe735932001cfc7359320086bf435932004cff725932000cfe725932004cfd725932000cfc725932004e7f525932004e7d525932004ebe425932004ebc4259320004ff7159320014fe7159320014fc7159320086bf4159320176bf4059320176bd405932004efa205932004ef92059320006fb1059320176f81059320004ff7558f2002cfe7558f20004fd7558f2002cfc7558f20004ff7458f20024fe7458f20024fc7458f2004edf7358f2007ede4358f2004cff7258f2000cfe7258f2004cfd7258f2000cfc7258f2004e7f5258f2004e7d5258f2004ede3258f2004edc3258f20004ff7158f20014fe7158f20014fc7158f2007edf3158f20136df3058f20136dd3058f2004efa2058f2004ef92058f20006fb1058f20136f81058f20004ff7650f2004cfe7650f20004fd7650f2004cfc7650f200057f7550f2008d7c7550f201e67e6550f200067d6550f20026be645
  | 6 => 0xb705893009d7e75189300057d75189300a5be7418930005bd741893004eee6218930006ed6218930095f67118930005f571189300067f76549300067e76549300067d76549300067c76549300067f64549301ce7e64549300067d64549301ce7c64549301b67f63549301fd7f725493009f6f72549300067f625493004e7e625493004e7c62549301c75f32549301c76e32549301c76d32549301be7e61549301be7c61549301c75f31549301b77a70549300077970549301b67f60549301b77a40549301c77b30549301b75e30549301b75c30549301b77830549301b77a20549302d77b10549301b7781054930004fe7690930004fd769093004cfc769093009d7e75909300057d759093001dde7390930005dd73909300076d529093000dfa7090930005f97090930004ff7650930004fe7650930004fc7650930026be6450930006bd64509300076d525093000dfa705093000ddc764c93004edc764c93000cdc764c930006df644c930006dd644c93001ddf724c93001fcf724c930007cf624c93004ede624c93004edc624c930007cc624c9302cf5f524c9302cfce524c9300075d524c9302cfcd524c9300074d524c930007ce424c930007cd424c930005df714c930007db704c93000dde704c93000ddc704c930137d8704c93001edf604c93001fdb604c930137da504c9302cfd9504c930137da404c930137da204c9302c7db104c930137d8104c930014fe76d8530096f661d853000dfa70d853001df970d8530097f310d8530004ff75d853002cfe75d8530004fd75d853002cfc75d8530024fe74d8530004fd74d8530024fc74d853000cfd73d8530014fc73d853004cfe72d8530004fd72d85300067f52d85300067d52d85302bedf32d8530006dd32d8530096f641d8530096f631d85302bef531d8530096f421d853001cfd70d8530096f970d853001cf970d8530226fa20d8530226f710d8530096fb10d8530226f810d8530096f461585302b5fb7058530107f01058530004ff7650530004fe7650530004fc7650530006f76150530016f46150530005fb705053000df8705053011ff0105053000ddc764c530016dc764c53000cdc764c530005df724c530006df624c5302af5f524c5300075d524c53001ddf714c53001fd7714c530007d7614c530016de614c530016dc614c530097d4614c530097d6514c5302afd5514c530097d6414c530007d5414c530097d6214c530007db704c53000dde704c53000ddc704c530107d8704c53001edf604c53001fdb604c530107da504c5302afd9504c530107da404c530107da204c530097db104c530107d6104c530107d4104c530107d8104c530107d0104c530004fe76c8530004fd76c853004cfc76c853009d7e75c85300057d75c853001dde73c8530005dd73c8530006f761c8530
  | 7 => 0x854004cfe72d8540004fd72d85400067f52d85400067d52d8540316bf42d8540006bd42d85400aef641d8540316f541d85400aef631d85400aef421d8540024fd70d85400aef970d8540024f970d8540246fa20d8540246f710d85400aefb10d8540246f810d85400aef4615854030dfb705854011ff0105854000dbc7650540016bc765054000cbc7650540005bf7250540006bf62505403073f52505400073d5250540025bf7150540027b77150540007b76150540016be6150540016bc61505400afb461505400afb65150540307b551505400afb631505400afb62150540007bb705054000dbe705054000dbc705054011fb87050540026bf6050540027bb605054011fba5050540307b9505054011fba305054011fba20505400afbb105054011fb6105054011fb4105054011fb8105054011fb01050540004ff764c540004fe764c540004fc764c540006f7614c540016f4614c540007b5414c540005fb704c54000df8704c540107f0104c540004fe76c8540004fd76c854004cfc76c85400b57e75c85400057d75c8540025be74c8540005bd74c8540006f761c8540016f461c854000dfa70c8540005f970c85400e7f010c8540004ff7648540004fe7648540004fc7648540025be7448540005bd7448540016f66148540007b54148540005fb704854000df870485400aff31048540024fe76d91300a6be64d9130004ff75d913002cfe75d9130004fd75d913002cfc75d91301d4fd74d913000cff73d913001cfe73d913000cfd73d913001cfc73d91302febf43d91302febd43d913004cfe72d9130004fd72d91300067f52d91302fedf32d9130014fe71d9130004fd71d9130014fc71d913001cff70d913001cfd70d91302eefa50d9130006f950d91302eebf40d91302eebd40d91302eefa20d9130006fb10d91302eef810d9130024ff76591300057f755913009d7c75591300a6bc64591302e5df73591302f5fb7059130004ff75591300067f75591300047f755913002cfe7559130004fd755913002cfc75591300067c755913002c7c75591302ecff7459130006bf74591302e4ff7359130006df7359130004ff725913004cfc72591300067f52591300a6bf42591300bedf3259130004ff7159130014fe7159130014fc71591301d4ff7059130006fb70591301d6fa5059130006f950591301d6fa2059130006fb10591301d6f8105913004cfe76d8930004ff75d893002cfe75d8930004fd75d893002cfc75d8930024fe74d8930004fd74d8930024fc74d893000cfd73d89300067f52d89302deee32d89302deed32d8930014fe71d8930004fd71d8930014fc71d89302dedf31d893001cfd70d893028efa40d893028eef20d893009d7e75989300057d7598930006ef629893005df97098930005f77158930095f4715893007df
  | 8 => 0x6fa6318121006f96318121006f863181210c7e97218121216fb62181210077b52181210077952181210c7f271181210c7f171181210e6fb61181210e6f3611812120ff24118121007f1411812120ff23118121007f1311812127ff3211812120fea211812120fe8211812120ff0211812101cfe76d8d400bede63d8d40004ff75d8d4002cfe75d8d40004fd75d8d4002cfc75d8d4000cfd74d8d4001cfc74d8d400bede43d8d40346dd43d8d4004cfe72d8d40004fd72d8d400067f52d8d40346bf42d8d40014fe71d8d40004fd71d8d40014fc71d8d40024fd70d8d402e6fa50d8d40006f950d8d402e6df30d8d402e6fa20d8d40006fb10d8d402e6f810d8d400057f7558d400b57c7558d400bedc6358d4033dfb7058d4004cfe76d8940004ff75d894002cfe75d8940004fd75d894002cfc75d894000cfd74d894001cfe73d8940004fd73d894001cfc73d89400067f52d8940336ee42d8940336ed42d8940014fe71d8940004fd71d8940014fc71d8940336bf41d8940024fd70d8940296fa30d8940296ef20d89400b57e75989400057d7598940006ef6298940065f97098940005f771589400adf47158940085fb70589400b57e75189400057d75189400bdde7318940005dd731894004eee6218940006ed62189400adf67118940005f571189400067f76549400067e76549400067d76549400067c76549401b67f64549400067f63549401c67e63549401c67c63549401fd7f72549400b76f72549400067f625494004e7e625494004e7c62549401cf3f42549401cf6e42549401cf6d42549401be7e61549401be7c61549401cf3f41549401b77a70549400077970549401b67f60549401cf7b40549401b73e40549401b73c40549401b77840549401b77a30549401b77a205494032f7b10549401b778105494000dbc765094004ebc765094000cbc7650940006bf6350940025bf7250940027af7250940007af625094004ebe625094004ebc6250940007ac62509403273f5250940327ae52509400073d5250940327ad52509400072d5250940005bf7150940007bb705094000dbe705094000dbc7050940177b87050940026bf6050940027bb6050940177ba5050940327b95050940177ba3050940177ba205094031fbb1050940177b81050940004fe768c940004fd768c94004cfc768c9400b57e758c9400057d758c940025be748c940005bd748c9400076d528c940007ad428c94000dfa708c940005f9708c940004ff764c940004fe764c940004fc764c94001ede634c9400076d524c940007ad424c94000dfa704c940014fe76d85400aef661d854000dfa70d8540025f970d85400aff310d8540004ff75d854002cfe75d8540004fd75d854002cfc75d854000cfd74d8540014fc74d854001cfe73d8540004fd73d854001cfc73d
  | 9 => 0x54250521005f7705052111ef6605052111ef4605052111ef060505210d7b7405052104df4764c52101ef4764c52104cf4764c521356f7654c521356f5654c521005f7744c521005f5744c521006f7644c521006f5644c521015f7734c521017d7734c521007d7634c52101ef6634c52101ef4634c5210cfd4634c521007e7724c52104df6724c52104df4724c521007e4724c521016f7624c521017e7624c52135777524c52100775524c5210cfd7324c521007d5324c521005f7704c521106f6604c521106f4604c521106f0604c5210cfd7304c52100cfe76d81210c6fa60d8121004ff75d812102cfe75d8121004fd75d812102cfc75d8121024fe74d8121004fd74d8121024fc74d812101cfe73d8121004fd73d812101cfc73d8121014fd72d812100cfc72d81210067f52d81210067d52d812104cfd71d812100cfc71d8121006fb50d81210c6fa50d8121006f950d81210c6f850d8121006fb40d81210c6fa40d81210c6f840d8121006fb30d81210c6fa30d81210c6f830d81210c6fa20d81210c6fa10d81210c5fa76d812100cfa76d8121006fb65d8121006fa65d8121006f965d8121006f865d8121006fb64d8121006fa64d8121006f964d8121006f864d8121006fb63d8121006fa63d8121006f963d8121006f863d8121077eb72d81210077b52d81210077952d812134ff371d8121077f071d8121077f241d8121007f141d8121077f231d8121007f131d812134ff321d8121077ea21d8121077e821d8121077f021d8121006fb75d8121006fa75d8121006f975d8121006f875d8121006fb74d8121006fa74d8121006f974d8121006f874d8121006fb54d8121006fa54d8121006f954d8121006f854d8121006fb73d8121006fa73d8121006f973d8121006f873d8121006fb53d8121006fa53d8121006f953d8121006f853d8121006fb43d8121006fa43d8121006f943d8121006f843d8121076fb72d81210c6fa72d8121076f972d8121076f872d8121006fb52d81210067b52d812134efa52d8121006f952d81210067952d812134ef852d8121006fb42d812134efa42d8121006f942d812134ef842d8121006fb32d812134efa32d8121006f932d812134ef832d8121076fb71d81210c6fa71d8121076f871d8121076fb51d8121076fa51d8121076f951d8121076f851d8121076fb41d8121076fa41d8121076f941d8121076f841d8121076fb31d8121076fa31d8121076f931d8121076f831d8121076fb21d8121076fa21d8121076f821d81210c6f86058121075fa76181210c6fa76181210c77a75181210c7797518121006fb6518121006fa6518121006f96518121006f865181210c7ba74181210c7b97418121006fb6418121006fa6418121006f96418121006f864181210c7da73181210c7d97318121006fb6318121
  | 10 => 0x912101cfc73d9121014fd72d91210067f52d91210d6bf42d912104cff71d912104cfd71d912119ebf41d912119ebd41d912119ef631d912100cfe70d9121004fd70d912100cfc70d91210d6bc645912136def7259121005fb70591210c5f87059121004ff755912102cfe7559121004fd755912102cfc755912119cff7459121006bf7459121004ff735912101cfe735912101cfc735912136cff7259121006ef72591210067f525912117cff7159121006f7715912117ef63159121004ff7059121006fb7059121004fb705912100cfe705912100cfc7059121006f8705912100cf870591210d6bf405912101cfe76d8d210cede63d8d21004ff75d8d2102cfe75d8d21004fd75d8d2102cfc75d8d21024fe74d8d21004fd74d8d21024fc74d8d21014fd72d8d210067f52d8d210cedf32d8d2104cff71d8d2104cfd71d8d2115ef641d8d2115edf31d8d2115edd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d210cedc6358d21365ef7258d21005fb7058d210c5f87058d21004ff7558d2102cfe7558d21004fd7558d2102cfc7558d21004ff7458d21024fe7458d21024fc7458d2115cff7358d21006df7358d21364ff7258d21006ef7258d210067f5258d2113cff7158d21006f77158d2113ef64158d21004ff7058d21006fb7058d21004fb7058d2100cfe7058d2100cfc7058d21006f87058d2100cf87058d210cedf3058d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210dd7c7550d210cf9c4350d21015f67150d211d6f86050d2102e7f76549211be7e76549211be7d765492102e7c76549210067f64549211ce7e64549210067d64549211ce7c64549210067f63549211c67e63549210067d63549211c67c635492104d7f72549210df6f725492104e7f625492104f6e425492104f6e32549210077771549211bf74715492104e7f61549211bf7641549211bf76315492104f7721549211bf6e215492104f6c215492104f74215492104f6421549211b67e60549211b67c60549211b678605492104f6f20549211bf771054921024ff7650921014fe765092117cfd7650921014fc7650921006bf6450921026bc64509210076d5250921005f77150921015f47150921176f8605092101cff764c921014fe764c92113cfd764c921014fc764c921006df634c92101edc634c9210076d524c921005f7714c921015f4714c921136f8604c92104df47650521026f4765052104cf4765052135ef7655052135ef56550521015f77450521017b77450521007b76450521026f66450521026f464505210d7b46450521005f77350521006f76350521006f56350521007e7725052104df6725052104df47250521007e47250521016f76250521017e7625052135f7752505210077552505210d7b74250521007b
  | 11 => 0x4cfe72d8131004fd72d81310067f52d81310067d52d81312b6df32d8131006dd32d813101cfd71d8131106f571d813101cf571d8131236f621d8131106fa40d8131106fa30d8131106f820d8131106f610d8131106fa10d8131106f410d8131106f86058131107f010581310067f74597210067e74597210067d74597210067c74597210067f73597210067e73597210067d73597210067c73597210067f43597210067e43597210067c435972104e7f725972104e7e725972104e7d725972104e7c725972104e7f425972104e7e425972104e7d425972104e7c425972104e7f325972104e7e325972104e7d325972104e7c32597211be7f71597211be7e71597211be7d71597211be7c71597211be7f41597211be7e41597211be7d41597211be7c41597211be7f31597211be7e31597211be7d31597211be7c315972104e7f215972104e7e215972104e7d215972104e7c21597210067f70597210067e70597210067d70597210067c70597210067f40597210067e40597210067c40597210067f30597210067e30597210067c305972104e7f205972104e7e205972104e7d205972104e7c20597211be7f10597211be7e10597211be7d10597211be7c1059721004ff755932102cfe7559321004fd755932102cfc755932104ebf7459321004ff735932101cfe735932101cfc73593210f6bf4359321014fe7259321014fc725932104e7f525932104e7d525932104ebe425932104ebc425932117ebf415932117ebd415932104ef6215932104ef52159321004ff705932100cfe705932100cfc70593210f6bf4059321006f6105932117ef41059321004ff7558f2102cfe7558f21004fd7558f2102cfc7558f21004ff7458f21024fe7458f21024fc7458f2104edf7358f210eede4358f21014fe7258f21014fc7258f2104e7f5258f2104e7d5258f2104ede3258f2104edc3258f2113edf3158f2113edd3158f2104ef62158f2104ef52158f21004ff7058f2100cfe7058f2100cfc7058f210eedf3058f21006f61058f2113ef41058f21004ff7650f2104cfe7650f21004fd7650f2104cfc7650f210057f7550f210fd7c7550f211e67e6550f210067d6550f21026be6450f21006bd6450f2101ede6350f21006dd6350f210ef9c4350f21004ff755832102cfe7558321004fd755832102cfc7558321004ff7458321024fe7458321024fc7458321004ff735832101cfe735832101cfc7358321014fe725832100cfd7258321014fc725832104e7f525832104e7d525832104ef6215832104ef5215832104efb70583210e6fa40583210e6fa305832104efb205832104ef820583210e6f610583210e6fa10583210e6f41058321024fe76d91210d6be64d9121004ff75d912102cfe75d9121004fd75d912102cfc75d912101cfe73d9121004fd73d
  | 12 => 0xf32591311dcff7159131006f771591311def65159131006f551591311def62159131004ff705913100cfe705913100cfc7059131006f610591311def4105913104cfe76d8931004ff75d893102cfe75d8931004fd75d893102cfc75d8931024fe74d8931004fd74d8931024fc74d8931014fd73d89310067f52d89313a6ee32d89313a6ed32d893101cfd71d8931366f641d8931366ef21d893100cfe70d8931004fd70d893100cfc70d89313a6df30d89311157e75989310057d7598931006ef62989310cdf571989310edf77158931005fb7058931105f870589311157e75189310057d751893110dbe7418931005bd741893104eee6218931006ed6218931105fa7018931005f970189310067f76549310067e76549310067d76549310067c76549310067f64549311ce7e64549310067d64549311ce7c64549311be7f635493139d7f72549311176f72549310067f625493104e7e625493104e7c62549311c75f32549311c76e32549311c76d32549311bf7671549310077571549311be7f61549311bf7641549311c77731549311bf5e31549311bf5c31549311bf7431549311bf7621549311b67e60549311b67c60549311c75f30549313977610549311bf741054931004fe7690931004fd769093104cfc76909311157e75909310057d759093101dde7390931005dd73909310076d5290931015f67190931005f57190931004ff7650931004fe7650931004fc7650931026be6450931006bd64509310076d5250931015f67150931015dc764c93104edc764c931014dc764c931006df644c931006dd644c93101ddf724c93101fcf724c931007cf624c93104ede624c93104edc624c931007cc624c93138f5f524c93138fce524c9310075d524c93138fcd524c9310074d524c931007ce424c931007cd424c931007d7714c931015de714c931015dc714c93113fd4714c93101edf614c93101fd7614c93113fd6514c93138fd5514c93113fd6414c93113fd6214c931005df704c931387d6104c93113fd4104c93101df47650531026f4765053101cf4765053137df7755053137df57550531376f76550531376f56550531015f77450531017b77450531007b76450531026f66450531026f4645053110fb46450531007d7735053101df6735053101df47350531127d47350531016f76350531017d76350531005f77250531006f7625053137777525053100775525053110fb74250531007b54250531127d73250531007d53250531105f67050531105f4705053111ef6605053111ef4605053110fb74050531127d7305053100cfe76d8131015f671d813101df571d8131106fa60d8131107f210d8131004ff75d813102cfe75d8131004fd75d813102cfc75d8131024fe74d8131004fd74d8131024fc74d8131014fd73d813100cfc73d8131
  | 13 => 0x8941006ef62989410d5f571989410f5f77158941005fb705894111df8705894112d7e75189410057d7518941125de7318941005dd731894104eee6218941006ed621894111dfa7018941005f970189410067f76549410067e76549410067d76549410067c76549411be7f64549410067f63549411c67e63549411c67c635494139d7f725494112f6f72549410067f625494104e7e625494104e7c62549411cf3f42549411cf6e42549411cf6d42549411bf7671549410077571549411be7f61549411cf7741549411bf3e41549411bf3c41549411bf7441549411bf7631549411bf7621549411b67e60549411b67c60549411cf3f40549413df7610549411bf741054941015bc765094104ebc7650941014bc7650941006bf6350941025bf7250941027af7250941007af625094104ebe625094104ebc6250941007ac62509413d73f52509413d7ae52509410073d52509413d7ad52509410072d5250941007b77150941015be7150941015bc715094117fb47150941026bf6150941027b7615094117fb651509413d7b5515094117fb6315094117fb62150941005bf70509413cfb6105094117fb41050941004fe768c941004fd768c94104cfc768c94112d7e758c9410057d758c941025be748c941005bd748c9410076d528c941007ad428c941015f6718c941005f5718c941004ff764c941004fe764c941004fc764c94101ede634c9410076d524c941007ad424c941015f6714c94100cfe76d8141015f671d8141025f571d814111efa60d814111ff210d8141004ff75d814102cfe75d8141004fd75d814102cfc75d8141014fd74d814100cfc74d814101cfe73d8141004fd73d814101cfc73d814104cfe72d8141004fd72d81410067f52d81410067d52d814130ebf42d8141006bd42d8141024fd71d814111ef571d8141024f571d8141256f621d814111efa40d814111efa30d814111ef820d814111ef610d814111efa10d814111ef410d814111ef8605814111ff01058141024fe76d913110ebe64d9131004ff75d913102cfe75d9131004fd75d913102cfc75d91311dcfd74d9131014ff73d9131014fd73d91313c6bf43d91313c6bd43d913104cfe72d9131004fd72d91310067f52d91313c6df32d913101cff71d913101cfd71d91313b6f651d9131006f551d91313b6bf41d91313b6bd41d91313b6f621d913100cfe70d9131004fd70d913100cfc70d9131006f610d91313b6f410d9131024ff76591310057f75591311157c755913110ebc64591313addf73591313bdf77159131004ff75591310067f75591310047f755913102cfe7559131004fd755913102cfc75591310067c755913102c7c75591313b4ff7459131006bf74591313acff7359131006df7359131004ff725913104cfc72591310067f525913110ebf4259131126d
  | 14 => 0x4276c40549321c76f30549321c74f30549321c76e30549321c76c305493242f6f10549324276e10549324276c105493241dee769093204eee769093204def759093204f6e7590932415ed759093204f6d75909320056d759093240eef659093240eed6590932185ed7490932026ee6490932026ec649093204fcf739093201dee739093204dec739093204fcc739093204eef639093204fcf63909321a7ce4390932147cd43909321a7cf31909321a7cf3090932024ff765093201cfe7650932184fd765093201cfc7650932006bf6450932026bc6450932005df735093201ddc73509320079d43509323ff6f52509320076d525093204fac425093204fcc325093201dec7650932026ec765093201cec7650932405ef7550932405ed75509323feef65509323feed655093204def745093204faf7450932007af6450932026ee6450932026ec6450932147ac6450932007cf735093201dee735093201dec7350932187cc735093204eef635093204fcf6350932187af4350932187ce4350932187ad4350932147cd43509320078d4350932147af4150932187cf3150932147af4050932187cf3050932014fe76d85320076d52d853213ef661d8532004ff75d853202cfe75d8532004fd75d853202cfc75d8532024fe74d8532004fd74d8532024fc74d853204cfd73d853201cfd72d85320067f52d85320067d52d853213ef631d853213ef621d853200cfe70d8532004fd70d853200cfc70d85320eedf30d8532006f610d853213ef410d85320076d525853213ef46158532005fb7058532135f8705853200cfe76d81320076d52d8132136fa60d8132004ff75d813202cfe75d8132004fd75d813202cfc75d8132024fe74d8132004fd74d8132024fc74d813204cfd73d813201cfd72d81320067f52d81320067d52d8132014fe71d8132004fd71d8132014fc71d813207edf31d8132136fa30d8132136fa20d8132006fb10d8132136f810d81320076d5258132005f7715813213df47158132136f8605813201cfe76d8d41126de63d8d41004ff75d8d4102cfe75d8d41004fd75d8d4102cfc75d8d41014fd74d8d41126de43d8d413f6dd43d8d4104cfe72d8d41004fd72d8d410067f52d8d413f6bf42d8d41024fd71d8d413aef651d8d41006f551d8d413aedf31d8d413aef621d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006f610d8d413aef410d8d410057f7558d4112d7c7558d41126dc6358d413edf77158d4104cfe76d8941004ff75d894102cfe75d8941004fd75d894102cfc75d8941014fd74d894101cfe73d8941004fd73d894101cfc73d89410067f52d89413e6ee42d89413e6ed42d8941024fd71d894136ef631d894136eef21d894100cfe70d8941004fd70d894100cfc70d89413e6bf40d894112d7e75989410057d759
  | 15 => 0x47158232014f4715823204efb7058232156fa4058232156fa305823204efb205823204ef82058232156fa1058232024fe76d9132146be64d9132004ff75d913202cfe75d9132004fd75d913202cfc75d9132006bf54d9132146bc54d913204cff73d913204cfd73d91321a6bf43d91321a6bd43d913201cfd72d91320067f52d9132006ee52d9132006ed52d9132146bf42d9132014fe71d9132004fd71d9132014fc71d913200cfe70d9132004fd70d913200cfc70d91320057f755913214d7c7559132146bc6459132445ef7259132004ff75591320067f75591320047f755913202cfe7559132004fd755913202cfc75591320067c755913202c7c75591321a4ff7459132006bf7459132184ff7359132006df7359132444ff7259132006ef72591320067f5259132006ee5259132006ed5259132004ff7159132014fe7159132014fc7159132004ff705913200cfe705913200cfc705913204ddc7650d32026dc7650d3204cdc7650d320075f7550d3243f5c7550d3243edf6550d3243edd6550d3201ddf7450d3201f9f7450d320079f6450d32026de6450d32026dc6450d321479c6450d320269c6450d321479e5450d3243f9d5450d32007cf7250d3204dde7250d3204ddc7250d32007cc7250d3201edf6250d3201fcf6250d3243f5f5250d3243fce5250d3243fcd5250d321479f4250d32005df7150d32005df7050d3202e7f76549321c67e76549321c67d765493202e7c76549320067f64549321ce7e64549320067d64549321ce7c64549320075f73549321c75c735493204e7f63549321c75e43549320075d435493204d7f725493214f6f725493204e7f62549324376f425493204f6e425493204f6c42549321c76f325493204f5e325493204f5c325493204f6c32549321be7e61549321be7c61549321c75f315493204f6f215493242f6e215493204f6c21549321b67e60549321b67c60549321c75f305493204f6f20549324276e205493204f6c205493214f6f765493202e6f76549321c76c765493202e6c76549320076f74549324376e74549320076d74549324376c74549320076f64549320066f64549324376e64549320076d64549320066d64549324376c64549321c76f73549320074f73549321c76e73549321c76d73549321c76c73549321c74c735493204f6f635493204e6f635493204f4f63549321c76f43549321c76e43549321c74e43549321c76d43549320074d43549321c76c43549320076f715493242f6e71549320076d715493242f6c715493242f6e615493242f6c61549324376f415493242f6e415493242f6c41549321c76f31549321c74f31549321c76e31549321c76c31549320076f70549324276e70549320076d70549324276c70549324276e60549324276c60549324376f40549324276e4054932
  | 16 => 0x96320067e41596320067c41596321c67f31596321c67e31596321c67d31596321c67c315963204e7f215963204e7e215963204e7d215963204e7c21596320067f70596320067e70596320067d70596320067c70596320067f40596320067e40596320067c40596321c67f30596321c67e30596321c67d30596321c67c305963204e7f205963204e7e205963204e7d205963204e7c20596320067f10596320067e10596320067c1059632004ff755923202cfe7559232004fd755923202cfc755923204ebf7459232186bf4359232186bd435923204cfe725923204cfc725923204e7f525923204eee525923204e7d5259232006ed525923204ebe425923204ebc425923204edf325923204edd3259232004ff7159232014fe7159232014fc7159232166bf4159232004ff705923200cfe705923200cfc7059232166bf405923204f6f7654a3204d6f7654a3247e6f7654a320076f7454a324776e7454a320076d7454a324776c7454a3204f6f6454a3204e6f6454a3204f6e6454a3204f6d6454a320066d6454a3204f6c6454a321c76f7354a321c76e7354a321c76d7354a321c76c7354a321c66d6354a321c76f4354a321c76e4354a321c76d4354a321c76c4354a320076f7154a3246f6e7154a320076d7154a3246f6c7154a3204f6f6154a3204f6e6154a3204f6d6154a3204f6c6154a324776f4154a3246f6e4154a3246f6c4154a321c76f3154a321c76e3154a321c76c3154a320076f7054a324676e7054a320076d7054a324676c7054a3204f6f6054a3204f6e6054a3204f6d6054a3204f6c6054a324776f4054a324676e4054a324676c4054a321c76f3054a321c76e3054a321c76c3054a3246f6f1054a324676e1054a324676c1054a3204def7650a3245eef7650a32455ef7550a32455ed7550a3204eef6550a3204f6e6550a3244eed6550a3204f6d6550a320066d6550a3204faf7450a3204faf6450a32026ee6450a3204eec6450a3204fac6450a3201dee7350a3201dec7350a32187af4350a32187ad4350a32167af4150a32167af4050a32004ff755863202cfe7558632004fd755863202cfc7558632004ff7458632024fe7458632024fc745863204cfe725863204cfc725863204e7f525863204e7d525863204edf325863204edd325863204ef7715863215ef6415863215ef6315863204ef7215863204ef42158632004ff7058632006fb7058632004fb705863200cfe705863200cfc7058632006f8705863200cf8705863215ef71058632004ff755823202cfe7558232004fd755823202cfc7558232004ff7458232024fe7458232024fc745823204cfe725823204cfc725823204e7f525823204e7d525823204edf325823204edd3258232004ff7158232006f77158232004f77158232014fe7158232014fc7158232006f
  | 17 => 0x2e7c76549420073f74549421cf3c745494204e7f64549420067f63549421c67e63549421c67c63549421cf3f43549420073d435494204d7f725494218f6f725494204e7f62549421cf6f425494204f3e425494204f3c425494204f6c425494204f2c42549424976f325494204f6e325494204f6c32549421be7e61549421be7c61549421cf3f415494204f6f215494248f6e215494204f6c21549421b67e60549421b67c60549421cf3f405494204f6f20549424876e205494204f6c205494218f6f765494202e6f76549421cf6c765494202e6c76549421cf6f74549420072f74549421cf6e74549421cf6d74549421cf6c74549421cf2c745494204f6f645494204e6f645494204f2f64549420076f73549424976e73549420076d73549424976c73549420076f63549420066f63549424976e63549420076d63549424976c63549421cf6f43549421cf2f43549421cf6e43549421cf6d43549420072d43549421cf6c43549420076f715494248f6e71549420076d715494248f6c715494248f6e615494248f6c61549421cf6f41549421cf2f41549421cf6e41549421cf6c41549424976f315494248f6e315494248f6c31549420076f70549424876e70549420076d70549424876c70549424876e60549424876c60549421cf6f40549421cf2f40549421cf6e40549421cf6c40549424976f30549424876e30549424876c305494248f6f10549424876e10549424876c1054942014fe76d85420076d52d854217ef661d8542004ff75d854202cfe75d8542004fd75d854202cfc75d854204cfd74d854201cfe73d8542004fd73d854201cfc73d8542024fd72d85420067f52d85420067d52d854217ef641d854217ef621d854200cfe70d8542004fd70d854200cfc70d85420f6bf40d8542006f610d854217ef410d85420076d525854217ef46158542005fb7058542175f8705854200cfe76d81420076d52d8142176fa60d8142004ff75d814202cfe75d8142004fd75d814202cfc75d814204cfd74d814201cfe73d8142004fd73d814201cfc73d8142024fd72d81420067f52d81420067d52d8142014fe71d8142004fd71d8142014fc71d8142086bf41d8142176fa40d8142176fa20d8142006fb10d8142176f810d81420076d5258142005f7715814217df47158142176f860581420067f74596320067e74596320067d74596320067c74596321c67f73596321c67e73596321c67d73596321c67c73596321c67f43596321c67e43596321c67d43596321c67c435963204e7f725963204e7e725963204e7d725963204e7c725963204e7f425963204e7e425963204e6e425963204e7d425963204e7c425963204e7f325963204e7e325963204e7d325963204e7c32596320067f71596320067e71596320067d71596320067c71596320067f415
  | 18 => 0xe3258e4204edc3258e42004ff7158e42014fe7158e42014fc7158e421a6df3158e42004ff7058e4200cfe7058e4200cfc7058e421a6df3058e4204f6f7654a4204d6f7654a424c66f7654a421cf6f7454a421cf6e7454a421cf6d7454a421cf6c7454a421ce6d6454a420076f7354a424bf6e7354a420076d7354a424bf6c7354a4204f6f6354a4204f6e6354a4204f6d6354a420066d6354a4204f6c6354a421cf6f4354a421cf6e4354a421cf6d4354a421cf6c4354a420076f7154a424b76e7154a420076d7154a424b76c7154a4204f6f6154a4204f6e6154a4204f6d6154a4204f6c6154a421cf6f4154a421cf6e4154a421cf6c4154a424bf6f3154a424b76e3154a424b76c3154a420076f7054a424af6e7054a420076d7054a424af6c7054a4204f6f6054a4204f6e6054a4204f6d6054a4204f6c6054a421cf6f4054a421cf6e4054a421cf6c4054a424bf6f3054a424af6e3054a424af6c3054a424b76f1054a424af6e1054a424af6c1054a42004ff755864202cfe7558642004fd755864202cfc7558642004ff735864201cfe735864201cfc735864204cfe725864204cfc725864204e7f525864204e7d525864204ebf425864204ebd425864204ef7715864219ef6415864219ef6315864204ef7215864204ef42158642004ff7058642006fb7058642004fb705864200cfe705864200cfc7058642006f8705864200cf8705864219ef71058642004ff755824202cfe7558242004fd755824202cfc7558242004ff735824201cfe735824201cfc735824204cfe725824204cfc725824204e7f525824204e7d525824204ebf425824204ebd4258242004ff7158242006f77158242004f77158242014fe7158242014fc7158242006f47158242014f4715824204efb7058242196fa4058242196fa305824204efb205824204ef82058242196fa105824201cfe76d8d42186de63d8d42004ff75d8d4202cfe75d8d42004fd75d8d4202cfc75d8d4204cfd74d8d42006df53d8d42186dc53d8d42186de43d8d42166dd43d8d42024fd72d8d420067f52d8d42006ee52d8d42006ed52d8d42186df32d8d42014fe71d8d42004fd71d8d42014fc71d8d4200cfe70d8d42004fd70d8d4200cfc70d8d420057f7558d4218d7c7558d42186dc6358d424a5ef7258d4204dbc7650d4201ebc7650d4204cbc7650d420073f7550d4249f3c7550d4249ebf6550d4249ebd6550d42025bf7350d420279f7350d420079f6350d4201ebe6350d4201ebc6350d421879c6350d4201e9c6350d421879e5350d4249f9d5350d42007af7250d4204dbe7250d4204dbc7250d42007ac7250d42026bf6250d42027af6250d4249f3f5250d4249fae5250d4249fad5250d421879f3250d42005bf7150d42005bf7050d4202e7f76549421ce7e76549421ce7d7654942
  | 19 => 0xd520057f7050d521b57e7050d521b57c7050d521bd7e76d85521cd7e74d85520057d74d85521cd7c74d85521c57e73d85520057d73d85521c57c73d855204d7e72d855202d7d72d85520fe7f62d85520ff6f62d85521be7e61d85521bf7661d85521be7c61d85521bf7621d85521b57e70d85520057d70d85521b57c70d85520077610d85521bf7410d85520057f74585521cd7e74585521cd7c74585520057f73585521c57e73585521c57c73585524d57f72585520076f72585524d56f72585520de7f62585520df6f62585521bd7f71585520077761585521be7e61585521be7c61585521bf7461585521bf7641585521bf7631585520057f70585520077b70585520057b70585521b57e70585521b57c70585520077870585521b57870585521b57e76d81521cd7e74d81520057d74d81521cd7c74d81521c57e73d81520057d73d81521c57c73d815204d7e72d815202d7d72d815208e7f62d815208f6f62d81521bd7e71d81520057d71d81521bd7c71d81520067f61d81520067d61d81521b67e60d81521b77a60d81521b67c60d81521b77a20d81520077b10d81521b77810d81520057f74581521cd7e74581521cd7c74581520057f73581521c57e73581521c57c73581524cd7f72581520076f72581524cd6f725815206e7f625815206f6f62581520057f71581520077771581520057771581521bd7e71581521bd7c71581520077471581521bd7471581520067f61581520067d61581521b57f70581520077b60581521b67e60581521b67c60581521b77860581521b77a40581521b77a30581521ce7f74596421ce7e74596421ce7d74596421ce7c74596420067f73596420067e73596420067d73596420067c73596421ce7f43596421ce7e43596421ce7d43596421ce7c435964204e7f725964204e7e725964204e7d725964204e7c725964204e7f425964204e7e425964204e7d425964204e7c425964204e7f325964204e7e325964204e6e325964204e7d325964204e7c32596420067f71596420067e71596420067d71596420067c71596421ce7f41596421ce7e41596421ce7d41596421ce7c41596420067f31596420067e31596420067c315964204e7f215964204e7e215964204e7d215964204e7c21596420067f70596420067e70596420067d70596420067c70596421ce7f40596421ce7e40596421ce7d40596421ce7c40596420067f30596420067e30596420067c305964204e7f205964204e7e205964204e7d205964204e7c20596420067f10596420067e10596420067c1059642004ff7558e4202cfe7558e42004fd7558e4202cfc7558e4204edf7358e421a6de4358e42146dd4358e4204cfe7258e4204cfc7258e4204e7f5258e4204eee5258e4204e7d5258e42006ed5258e4204ebf4258e4204ebd4258e4204ed
  | 20 => 0x4fd70d8543006f970d8543004f970d854300cfc70d85430057f75585431e57c75585430067f65585430067c65585431279c43585431def4615854300cfe76d81430067f65d81430067c65d81432f79c43d81431ddf671d8143005f571d81431d6fa60d8143004ff75d814302cfe75d8143004fd75d814302cfc75d814301cfd74d8143024fd73d814304cfe72d8143004fd72d81430067f52d814333ebf42d81432f6df32d8143014fe71d8143006f671d8143014f671d8143004fd71d8143006f571d8143004f571d8143014fc71d81431d6fa40d81431d6fa30d81430057f75581431e57c75581430067f65581430067c65581430bf9c43581431d6f860581431cd7e76d91521ce7e64d91521cf3e64d91521ce3e64d91521ce7c64d91521c57e73d91520057d73d91521c57c73d91520073e43d91521cf3c43d91521af6f72d915204d7e72d915202d7d72d91521ae7f62d91521af6f62d91521cf3f42d91521bd7e71d91520057d71d91521bd7c71d91521b57e70d91520057d70d91521b57c70d91521cd7f74591520073f64591521ce7e64591521ce7c64591521cf3c64591521ce3c64591520057f73591520075f73591520055f73591521c57e73591521c57c73591520075c73591521c55c73591521cf3f43591524ed7f72591520076f72591524ed6f725915218e7f625915218f6f62591520057f71591521bd7e71591521bd7c71591520057f70591521b57e70591521b57c70591521c57e76d8d521cd7e74d8d520057d74d8d521cd7c74d8d520067f64d8d520067d64d8d521c67e63d8d521c75e63d8d521c67c63d8d520075f43d8d521c75c43d8d5216f6f72d8d5204d7e72d8d5202d7d72d8d5216e7f62d8d5216f6f62d8d521c75f32d8d521bd7e71d8d520057d71d8d521bd7c71d8d521b57e70d8d520057d70d8d521b57c70d8d520057f7458d520073f7458d520053f7458d521cd7e7458d521cd7c7458d520073c7458d521cd3c7458d520067f6458d520067d6458d521c57f7358d520075f6358d521c67e6358d521c67c6358d521c75c6358d521c65c6358d521c75e4358d524e57f7258d520076f7258d524e56f7258d5214e7f6258d5214f6f6258d520057f7158d521bd7e7158d521bd7c7158d520057f7058d521b57e7058d521b57c7058d520057f7650d520067f7650d520047f7650d520057e7650d520057d7650d520057c7650d520067c7650d520047c7650d521c57f7450d521cf3e6450d520073d6450d521c57f7350d521c75e6350d520075d6350d521cf5f4350d521c73e4350d521c73c4350d521c75c4350d521c71c4350d520057f7250d5204d7e7250d520076e7250d520076d7250d5204d7c7250d524de7f6250d521e76f6250d521cf3f4250d521c75f3250d520057f7150d521bd7e7150d521bd7c715
  | 21 => 0x800400500080080000000000000012008001800000e00000b800001000500200080000000068004002001000800000e002005800800000300a802c000000000802400800100400e8006000005003c00c004006800800400c0020004000004001800800a00100000040020010000000006020001800002600500b000800200100d0034002000000000803a009008800800204a00100340340020098000002004006801800200a5057e76d95431e67e76d954302c7e76d95434f73f74d95434f73c74d95434ff5f73d95434f75c73d95434ff5f43d95434f73e43d95434f73c43d95434f75c43d95434f71c43d95430057d72d95434ff3f42d95434f75f32d95430067e61d95430067c61d95430067e60d95430067c60d95434f67f74d95434fe7e74d95434f67d74d95434f67c74d95434f67f73d95434f67e73d95434f67d73d95434f67c73d95434f67f43d95434f67e43d95434f67d43d95434f67c43d95430067f72d95430067e72d95430067d72d95430047d72d95430067c72d95434fe7f42d95434fe7e42d95434fe7d42d95434fe7c42d95434f67f32d95434f67e32d95434f67d32d95434f67c32d95430067f71d95430067e71d95430067d71d95430067c71d95434fe7f41d95434fe7e41d95434fe7d41d95434fe7c41d95434f67f31d95434f67e31d95434f67d31d95434f67c31d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95434fe7f40d95434fe7e40d95434fe7d40d95434fe7c40d95434f67f30d95434f67e30d95434f67d30d95434f67c30d95430067e20d95430067c20d95430067f10d95430067e10d95430067c10d954304cfe76d89431e57c75d89430067f65d89430067c65d89434479c43d8943004ff75d89430067f75d894302cfe75d8943004fd75d894302cfc75d89430067c75d894302c7c75d894301cfd74d8943024fd73d89430067f52d89434a6ee42d8943446ee32d8943014fe71d8943004fd71d8943014fc71d894300cfe70d8943004fd70d894300cfc70d89431e57e75989430057d75989430067f65989430067c65989431a79c4398943006ef62989430057f75589431e57c75589430067f65589430067c65589431879c43589431e57e75189430057d75189430067f65189430067c651894341f9c431894304eee6218943006ed62189431ddf67118943005f571189431d5fa7018943005f97018943014fe76d85430067f65d85430067c65d85433bf9c43d85431def661d85431d5fa70d8543005f970d8543004ff75d854302cfe75d8543004fd75d854302cfc75d854301cfd74d8543024fd73d854304cfe72d8543004fd72d85430067f52d85433eebf42d85433bedf32d85431def641d85431def631d854300cfe70d8543006fa70d854300cfa70d8543
  | 22 => 0x3000401e001001800000000000000080020000000000000011000000401c01c003004800000600b000c0120400010000006005002003003800700480000180000000000014000008800000000300080b4012001000000001a002000001000000c0010000000006001800800000f0068004052004001000c008000004001400801900900080140000008004004000000800000200200d003c00000b000000400c003000800c002003002001c00800a00100180040000060000004019008001800a003000002c00000001200040000070000004002001001000001e001029800400e01c000005800e00000480000080000020004014034005800002201d000000c00000700080000040040028000058000005005400e018001801c0020000028008000008005802c004000003800800000d0008020004001005800400c0190008000006001002000001e004001002800c0050078004004000004000000800500e000002a00000080000020020058014000001000001c000000006804400800200580080060080000008002002002000001c00c0018004016002016801c010004001000801800200a802801e0020058030000000001800000800000080240060010020000002013000000400a003002804000a00000400000060030080008054009002004c00201b001000000400000400000720090040050010003000800800c00900e000400800000f800800c0170038018008006003800000a012000800400e00400000040060000000000004026004800000000d002800c002003003800000200400500c001000a000000c0080060020014008001003800400e00000380040220060018080012000000003400600d01b000800c01100a000000600e0060004056007004800801e0010060000012003000004800200d0360030000007000000800e002009800c000009000803803800800400000060010000008002000004800c014000000800001201b0000058006002001004c01a000005800400002300100040080010000000024000008802004e0030000010000004000000000200500200480000010000004004002001000801e00200280280080000018098000003002002c000002000000c00200100780140060010010018010005001000c00e003000000000200000200040020060070000002000004000c0000010008020002004000800000e0150020000004003001802000000f000002400a00600080a4064000008001400200900080000240070050000002011001000c000006008800400000000080500020000000010000013007801c004008004000000000101e801c000000001000804c0030088000000001002802401e005002800000002200480080000000000010002005004006c00c010000001c00800f001006c01c004000000
  | 23 => 0x35180003a75168014c740ea0001dc50dec8d0000000d460002749c90e2e5696f5800185ab520000000000c441db0001796d860002a7c0ee4f24e282280000000360001784e7760f9ec5cbec836920001c2883e212ad303845b71a127055009924622bddca675e10511cc01ae30331253c000ba00001554000c883b000000006d8265085c10610f49180ad0c435c20380009c8000000000000023600035f8000a0b00027297b4c481c1116896e0007158ae1160d3a30c8dad0cc3e000000001788903058002003003000800200d0000040014000000000000c00001180000020020000030006002000000800e0130000008014000003806c002002002001400200b00280000040000038020000000002801c010007002800400801100e801c0040030060024004001012800c00600100000000000030000000002005001800c02400500280c80000000028008020004000000000c0020010048002002000001c01600b00100040000000010000010008003800000e00d000001000e00c00380340060000060040002000000000800000100000080040000000000000000000800001000300080000020000048008000007002004000000100000000060100000000004002000004402c000000001c01e01000000240160070018008002001000801801a00100e8004020001000004c00600900280100100000000000012003001002000a007003806000000f00000040580030000004000000001800003200500b00bc000002000800c00a02d00100980000140048008034000006000c0000050018034008000008000c06400800d0018004000000800401c00700200140060000000064006000000002400600300b800c00a007003804401e005003803401c0050010070014006000004c07c0000000008010004002801000204a002000c0020040000034008004005005c0060000040054000003009000000a0110010010000004007804400200000700000060030010000000000005002800600100e0004002001004000001c0030000070000011000800c000004001000c0000080018004000004000000400600d0010048036000003800c006004000000002e00c0000008000001000000400400c004000000000000b800400200001980140060190048028002000009001001a0060008010002002000800801c02600300000020130030024000005001000400400c001002400000a0028018002000002003800c00a00480440180120008000006003000001801a0080030000006010000001c00c00a003000000a000000800800800400080200000060070028000002007003000200000a802402000800000a801000000d800400400000900700000000008004010001008801002600200080000040050030020006001001800000000a000800401c00
  | 24 => 0xe4c23000181d73e3aa00037bc8341f630c0f854500b960409912e0aaa0000d88676de730835c440e76d18e2c306dc7181a2141cf9a0b7500160817e9b75a82b1922291c411ac658d20000003780f7279c2928ccc000ce5266b1980a27b7571192199407c0af818c6c61e712ba89449456261780005d00a60000a60000000570000000085203894411c60003af80000000005578bec43c0000001355c000005f716d40000004d68000000328317a5d0ed83f64cb1c8c4c098f57196ed060a6a2860e040009524ee8000db4b08461a4f1b4800018938cd96686d589a1e09540082d013ac02249211a0000ed000000000012d6e041b286380000d45258ac573a76f1710000ee00006ef04e800000053e00000007841151980fd08c60da3738000842129ba31a4a9a006f183c364c6c354b029690272000149c5ac00000009399de000347abc03260005ad80011dabd868412e576e2df5418fb555aa3f52e1399b0a44006d216c0000000b480005ca1fc00000011e24176480000f2000058a00018e86e4000040d2ea00000000000009c75e498213e61c84c50000e5e5cb45a800120c00000000000002d91d280004eae5d0000b81286e61157abb42fcccc173b6bd894be80000000c8224f00000000003fa58a800000044a0e980000000005658b2966cb6d6c88df800037871aac44000550432ae785b00001af92052603940f70e187fe00000009755dc2cc4d406bc000a120af06a50f48cc42b97f56366856060e8c9620c44f50bc41d85281ac1af40004c45b401995820001480b9121c0007240a3c0d203e40d0d29cc059c16e800129a04702f1bdc24e0005c624ad96a00000000000009e653100000000000000bbc0000002898b44e0a5316a0ad5497416600000013180004ea3360c6246329b00005dc0ed22f85e17887e7000126c25658d49606680006795b0abbc000000030800026e03c000376045c00000009983385a100039d80000000003294726524000285c77007d25022c80000005b100012f6000000000000000048207c49000846c026952e614d4b60f9990800050723e400042d56e186c0001a065f230400008922690d80000003e08000de2a5a00000017f200069e2fa850422402d0ac97f04ea29d97cd422e162f108a14865f839580000000004d1000000069a000192c000000285b0cc0002ce534903495abc5183919db4443241db345bfcc8904d102848cda7022b96c11839b52220f00000d765ea40cd685875e3aa6082400055e953400095565db934000cdd3351b308d45e13118dc5c7e0006132c14f98bbc6d5a5a4000bd737823c80003ea44e000000000010300004ca7b223b000066e00000015197a65086c48f347f0df30000000000000396b804c3cddf60a80000000000001e843fec62373b9585c615714880000006ca00
  | 25 => 0x3aa80800000056917a966e19145f85d400084a00002840009880001d40162e645f121c847a0ca00020e8000c6700000000008c034f800053231f000050c000da6271845c04000049f022cde61ec68b18587ae3410a410804d0058000336994465523f147ca5eb3d00032457c63f51c6af952ee000588000156c07021a1dfc0a8d271292f3cc0cd9869d80011445d32e8b28d0f804a1f3897d64c6403d20000838bb63bb330c3ca2f463cac8dce896200000008e2000000000145ebc30002a548020000000a0d6747315f600013bcb51061a2f00480c93ac33f80621a60e011051d887059e0c14cba78522b0000e8e6876dbb3fc99858673894d44da05b65e0001cd657f0c904cc0006574a8b3519566b13028001bb800049a8000000e5e2fc831cd70a306c929e44268b628109fc3b47e014418fd51a3fd0f31511bd26c672a1e98270d534413479cfadd76e238297f80396ca1260dd6d514050fac57ae690dea674bf6a091899a4052a62534126c19823c351901e985289460eab30e36000615a5153f2000000343800000004e2151cd45394dd20741506645fa37c478e0002cd1d219fa00039d1764aa200043f0000c789d80000e30a588e10cd80014e83b030601fd13a000710237c00014b23d0000000a5571d800016400000016f40001d14558000000a9158d14acf8c5916fd8ed15f853c4551f140260006610139568aac27d8000d6c00049f80009840002b0a20cb1800000000000000000000001640d2947418dcb303f0000000161a3736df0a3872a270597a4cd9c0a5600033d44860000000000000d9f04e8000ef4b02088000000045c0000e68524e893d1b2c400048708c00000007fb6af87ad562c38715305ce80a066b68060c384c65d31f1c0d09cd4090a31a301492a0a89000000013098a9c840003859b7400000038c8000432b8069891452a891363fad1c0005e0000061c0003e5451a5f038a00060119700000006e184d4000c6e4350001a2690a000000069285800001bcce2489315b968024000000000000076e0000000204d882d41b5400012e7110000000000000252491076247b00000006fa1e815c00004040002b640000000bc800049022358523986f40005be1da556a48f24f1e6c00041900000000004b510a921000000051e3190e9e0ae1b806b000000056c0000000000000231da1455d5438f502720006c100010906db283000012a00042e965c00088048b9e50000ae11d7895083c00000008f000000024300000000000000e8103e0000000784acabeb1e8855410c00056f22b800097f017800000067663e2d1502697109f0001a98529377969c0ea40036ca325bb243869b18d43946673409ee82b00880942024d320000d5950800080d543298cc9e0006fe826c34e2f6000221c1febd070ea4c8b105f052005002
  | 26 => 0xd0c0002dd000000000000000d00000ef000000036ea3b6e597b8000d306bf82d488cbba4e01c8828c3b70002909304d9a000032da5a00044f87f8a1c00008f23885fc10a49c834c0008e700000000001ce5d6a58d38c5c900031bc0000003f200018e0c2860b3134c1c65f0198da105429d0d185b51dc0b8140ae3d86a4fa3340339bdc02364b9561a243486d6389c28edbf46597213c829c070b37c332df2089a104d9209461eaf9c00000017e826000035422da93480cc9c000214d4ec0005f7800000068d4db24f456c756390070c00000021b80000000000000000c2e0c145411813e274229e8e2844a57455d8614c680003348dfc0008b31c90d591cad7b25480017661110000d312e400000000014301d75fdac3d992c76000384d5a27ac0b28e10bc8cb031f38a4c08ae72b1abedb9856020181ccaae22234b80010c800000004fc762c710000001af0050678a6e432000066800000000001162c247b29020000000f440000000001ba03bc073800128cb25675b4ac0000000000001bf200048aa23c0005470000000eb2000249a1dcf7e3362bd0000000d7400008e900a00000000000000000000b5c2640000a7800077a28700000009c2b642b5846da6ea9a7272381c306f91d2212c35c5b4104b33cd6a0a52d682acfa00000000001ad4782627910c8c407e3dc000000000017480000009210001380000d3900000000e400055933f000045e2bb0000ff89eb3182a299ae0000002c880000af69f89100004ff3dea4e8000000000111420c00000023ac0340e643b13b4e8a81400536800008bb5da27f4d0059355b9f10a3cdad00005ed4d65d8000026400041f4d59c9477c34523a96a98bee4f52ba78db72d7d0d8888084e8bd2f411481741c13ff872cbbad615383089a960006740001d062351ba26e0000a4c5cc800174ea5900022e4b000002ab00000002d200000000005593f780008d6429000000000000010da24c00000038000006969375d83050070e2527a80000000003df14f98066d40001b85b200004afb9b075c9266541cc05b65783a69d0d54a91872c17484aa1230ae30c4fb65ec00010e989c5122c08c2c6426d32822d2d9324a164fb6a00002ad1d488393d8dd234323bc9f00002a435dc79e00000000010be58a5ac86ecc582402ed289d80882d6e9b178d540004e723fc18a000000000035a0006780001364d00718a2bc000a6f00000017da00035f883c0000006c7b7fc00000001280000004166c58000000cea1a0080000000000000000000006770000dd89e963c000176200000b165492ea3800115bc9bc9f502980b0cde00027887c0ae6dae5981e4c00030a0002a40fbe0002eb09f481c0005bc34a0abc0e51fd80011a42ab41415b000000054600000005790000564000e020000000000000000000097e0005
  | 27 => 0x19199804955511914ece303420351cb60a9411f0f08e7605f5ac2c84d82e175e40000000000434000062c0000002dc800000000031a00007140002a480f000013b0add77e43e00011d186094435d37e172e30442c9a393ec00048f9ecc91880646b14ccce4a7d32197d02880004df92998fc47c5ff1e3d42ab9014596158aa4fd207ab5993600037f000104a0000002228d22db354f0de50aa7d30001b454f000024186180002d000011dd378ac84b412f1c380d6071abfc0803726eeb23da320004610001ae070766d8c88d423d66508fc539e9cc46a9c9c0005b63d500012402420002bc5bf846c26580843e694c5b4acc955c00000000000000006ed97fc68c94700016e406e0002a73580d2a33a3b0b90470a0003440000fd200032f0001140000000220481678d2e78dd519cb4a5920a2800006a000000007e00000000000003900001e6400013c319878824a00b06c8b142b6856595ae1892c2510681f68cf035510212505aad9d1ee00c83eaa4f34b2865c6e9250909e80d846b20742568b46d7c1be88e4846a6457c2ded1b60004232340000d1b630115cfe02e60bb80014547096521fb56526523051f0d038b316a42cb807ad6909614719180e2000361d4520760858e84a44b413171e6800000012d9c68b78d4a00039558740eb0000000366c394d1800000000008200000008dc604a898fc28f867335b8a545df67a000000012439f34f5a427385e91714000dc20002fd40007026f42bd0f96dc06f633dd426b434f4311946c293524210d722bd65368761510b74068800025453a2488748ace83d0001f95cc46bc11983f817608f349019d96e97e59a10e4000bbb37b076c0001c70bb000181e52145b88512122bc4698e8967642f0001934a94acf442891c000000742a0300000000003798c02b40706911d63e46674425bcf9442b33eac759c211c4470c01c726e36b9384150a9fa6db27f99345fe6a82e389709c3191b9b89cac8e0248d457c2af9701b29d8a887b5c4b6389463cb5288c984bc26314b91fc04edbd5ff9c44f2e5c3000358cd96d5d47f00010d299c014ab986280c600024693129796930e1cddcabe00037d885ce110000c31c5e3690001568f5685c1512bacea86125fd000000000000019f08daac23f1b5e80000000cbb81d25275a510800015a8160001274b849fb07e9a9530e0004c0000000001c4103a395e6d105a128b06bc4051b6a4655746ad02c86fd91472a00038d00003fc68e80300001bc167a64523600043a80880c8e5900007f5be047b3862d785d4e474ed25996e6c05000301d438e45259a29cb6601b28b08400000002be163d33427400013a000066300000000000005e52bd80000005fb000177c9ed32618444f889e4deb0918845191b531c8d9a0004fe0000d600fc000000000042a6b20001
  | 28 => 0xda1800047991402245846d1a3d46680000003830e94ace000334cfb220c39babf8f06000116957000084e4e429380000db2ef00247bc1835af80000a40007109340d44a60000389019e52e3a625399880a90000001b6a6e500039d4de849a53d8f00fcc0005c2b0f000069c323800133e00000025a8d12d151248650c9c3090000001c9468469032b00863b3114868800081137e8000c06000194b33911657d38781e4b36000657a75c0000000001c98e969e1176800048a000261800076a00000012900002010001d491186420000374f7817d0eb00001c000017b81ad4d848b45d0001c98a1b113801dbd46e00000df0568bc1159800000000071d266cc700004940000dae0006c094d0000c1824280000000000000000000000001800000011a000233d8ba1a10ec82c1cb818a6762ddc06cbb20310001a9c5640000001c8c00070fa0b0baad5c016b149b825ae07a2cb4f3038f0001fb80961264eaadb1a088e900024a933c68a000294c5f498e422341c58827a74125f48662711c88c953a643f349b83c56033f724829c3729866319fe41847d7435b0040007d60300134000000000000178c12900003000007105d0aa74b520006642dfc5bc0002b7129c28430d2581a0da887d52918bc889c7011fa22985801df2df843454220512085bd77a8035100ea16ba7eb05a0d0d18a11d4b6a87859aab962c04b45f03e40001cf0000d220002b2978026f3ceb5e57aa6735cc31a80009a10000620da4dd62082430304bf3293186893200072599b58ac713679341974683564f13b817a3cc329a09cf3c07b15f9045c6c7f710907c9892dc918893cce52e671ef8b840002f05600d3524427b4288cac00000016e0c5ced47a92a498849b60000000001a3e0003ae2780000add56214547a6cba0001359482000000000162400000000009b20005a7800185441d6d480008184440000000000839364162c0000000001964d761001a81054000ae80a90000cd6cc76a2956c3ba00000018340003661548b1c1ea0005ed800001c26e5c3a01c000a310000414154b6a1262c0000067b0b5a97d32a0000001ccc9b80004fb800039201048400000004e2515800010419e28195c80000005c1ace1b704e7682a2950e2c960278e651ba00068ba6517eeb4e00000002d080f000306d20a0005041160000819000137c000e8b0000000b7cc9246b91657be46f020858531683766f0000cd87160000f246a617300000000000005f48000000566539a86800090d5dca24952eb603141ab875a0f21cc17dd7e47dc65a04ecfd40003fb00004304545ab80000000000000000d9e396000244800000034e80006c25c70000e3947478e61f1bb40000000c08c680000003bc0390000d1a00000000003f27292e5000090f0c6aa11a5cb672c734a93526c355e0000e64296
  | 29 => 0x2ea000000037e0000000aa10000a50000a520000001a9ac364641bd53dcd9c45a200011ab463cb31e87902b544211852a0d7507b000540a86e3822ee0c52cae34d8000d30be025e80000000003be0fb800049f547000031e0000ef08c40001544e227e00003d26810291516e3c4d88000e680000510001068000501886891cb161cea7894d01ba15f19d58eeaab52eac38590cf971912f96cab70721b2198640000000000000000500b2e4f9e8cd00030199b22da522a3e9ccc6e968a299c000b5c3818455a065171bbab407d8ca91d30f68f805e924812d01e039f4301874d406206878d5c6600001ec134c65e0003b9800090463b39b05c000028033a0320c5a4c83d802144fc9614ab20ad4a831b16093505a6d8a000264c61eb820000655cf2600000000013c0006cd8e255d20001cbaaa40009271158cc82a6c5a4c81d4c3a8c0e113365976ae0b47538980000145d79cb8000352332a874e72dc82b530000003f928d395ce107c90001d1135e2aa63d83cc4380ee680acfcdbc4c520a000096c0001830458000b0745f13d0ecc000151a76c87839c6b408dc350e2817faf38262b792eb800000014e7090000f0ee730000000000000000274876400069c17c40001d04192a0800083f716b1b4000d520000001ba281e0001bec00000073e000000000003680000002790000000dc40002e69df80007f514f3069c12c75553a52838c62733f28d18d644c4448f399ce31067d8000706a650002125616abf5ad34b0b3e5402328e78f142ae737800173800000035cd6080005408001c3275b0b887e4d3c1be561b635bcabd40000000a3a32d00036c80003ba0003355aac7354cca13494a00073fac05bc898150fa5e0e42000000000000000000030b8ffc9ef7041be0a6455f73808080009d0000146140eab00002c0ce7a7fa5833a289fc0004968000830000000000000000000007ec05ca142570000c2aa3e70311e4d16e050002458000e3d22ea6340ac2894133048ca0000355800000000000000000002c949880000881cd3cf800000000065f82d8c723fe0e600009f8000000000101c94b0000001b2eccb12580000005a20001b10a5abae06c0ce07aae2c38700002e800000019e800000000018500000d200000646c86dc746800029455442f000000000000004c066a89b26e800162e8912a78b183f04c71842218f6a24d0002840d9c1895d2980925e8ad18f2c70000000040316d1f884c56d0000e2ae7a2ed8000aeadfa00000018b20003e102580009644278000ebad6b4f9058d92a940433828097604c5ef2a24658cb81e0b9c96300000f685755b633d04f80014c234e52c15ed05ee406ea0a140dc7b413480018fa8da0d8000125c0004d714c00000000002a80c129a6277ad8db3c7645282708c6c0000fd2e9181a2eb214322
  | 30 => 0x88c449f03c5940172436f00000013581143e4088412e50900026ed570c4133807a98ae00020483c40842862ee1d440005711358465a6657e1aca74436c97645c00000008791ed800104231559f000141ab933e71acd8207650001b1d2164a81530018d6e934146ae6933015a6a4b5d90fa67721d878089246921105b010ee382a2b6957e210e3a4a2c5052dba1b03a10298d5544d31410e803573f30dcca21f447e97b411cd4f3beb21ca1e0dc400b5b106c5af6dda7256d6d9967d2578000c3f07bb37041ad621dc8074da0afd3461d04c4ca4946f3569466408649b838b98aec44aa829842e63180b3d9a640005629d5c63225a4309a908e03dd49dab5cbcae6d6c19e48a40df709000018c23e353900988481a500034f84b800028a14e0a968381a7b280ef290707d23649140002f5b7d415800000000011b02ba229800193059247bb4440000003c480000ae7750001719a8000054e00006b49833d29301b2665a000206db182590000000b2c3e91c59ba88d0ce91989dad5a86325a982cd5263ac06f887dbb4a3d48838f97109b4257b209b9e7a710185f18164b22c1ab90a6e70d54b000188ea47108871163c3c65a22350fd84c123216c8000ad312b225847e0004b3aba8eee9d617ab358000ae51a3899cf5c3ab2fe23ed4ee05557d05fc7e647d50616ac2ce00000034d01983e24f38bf151e44f26ba25d79ad5427cb7d0938b4d0000514a14ce20000660c920000000000000dc600028d4000dd500025092480000ce800087a00000016500006240001ca000000000013453fe2a70000001a460d5671b194cfe1504ee2ca97020000000000be40001529cfd3e800059386a94f40921ae912c0000006ab8c396e2e150002d59bc45d035cb3e04164ec00200c06d8be66de0000d5861f51ca18c0000000f40001b086d65960001ab603a0001109832e510002b1c00026232db4d402a97a53332d836ace4048309c7886af2e0800102e808000254cb584a26da1f884649482fd08e102ac536798000a98ded4cb800114800027b8000000a0409a20c5cd08882828001c463273741c7c308b954da8c6000056d4c200a00000000232b55692c1115c9c78000b6f0000000d7c7d11972b3459670a00004d94fed954280ce5cf6adf0842a90fe67125519a984a0af52e032999020002d880000007f140800000008f419220cd3ca552480972934e0004802e5843a9df0d2059183cb8400032a86ec1ef2cf0000b880006b3b3498a2122639a1fd4443ca1f7b684c7a1011563471b607b65ee80000000000002bc80004f60001eb5130000000000000018c0002dd8a02746666b2c80e83c53dd800033e77210b0be40000005e6256c958277000321584091e6259951b8ed423c611b9a160004689d54cac57700002f8000000000000020eb3970f000000000
  | 31 => 0x2cd40007a83ec2eb0000d2f29fa45000002a14d115566688d53721b070035b2d291204f096e49c1b14ee866e00000009a4000330b424fa8b7a454828d54cc345d48ded0047f42f332b4b706580a8a6cc1f0a5e594283cb3a82e3fc07709b45116af1e2003e95c0000001c344ab00011e130a6f262290b108e00000000003ee0005fe984cb9ca9b00008c000000064e80009e0bd15c680005d81560001c7000000013626f8000d660001b001228f00bd2ea96ea9650a08e209b01e96d8ab257b2000612932464001e73c32512c0899662a55c2c000014da5758768ca0001decba8000333000103033c1612e2c7ee000000000000054300000000000170000fa0000000000000000008100000005407af32500018860000001a9db54a3770d906cbce0003e9320084c4726ac8820000e4437fba01d021963c030b0aa612f209b5bcb48d580c5a3905867dd00001204d4bab405b94114200028d80014fc8732cc87540000000000ca8000c4c2189b980000002f785a845e13d1ddb50c000bf0007800142c00066309600007de14fb1000ba31d0000000000000000378c77e000456178cb120933c30a900760000002df400000011d80012b071d0c00000212065686ad996fc0e94110d9cdbe7f200016400000002fb143455048d4e589cc00000016a00016dcb9b000169819adca48eb8b8f0240200029280009410dc1c198267917328a103c6a994d51aa18b86445d104300000000e7a691550ab3422a168ad00f949b047d0480007439ff5838804676800000005c6b2879099eb545f20000e9c42121a83ed3b2a2e00010c000016e2672f71bc22bb00037354e269419f1cb14b63020000000000b8a2fab71544679500029192b276317985
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87c855d943440011df04bb286880263b2097650d1000678082eca1a2000d7010dd5434400b1df0ea96c4880271b1897598910006b8082eb3122000c6d75d8a62440011ef02baac4880023ee0175589102863bb8ea4b122069c7b70d4962440031f50fb82c4880035c04175189102865bb0ae83122069cbb605d06244001b6020ba0c48814335d85731891034e6db02e63122000dd0105cc62440011df0eb10c488142b9e05621891034d75c02c43122000e7010dd952440014db053b2a4880029be0976549100053bc0aeca922000a7b805d95244001ce0203b2a4882ab9c043645491000537c12c8a922009a6c825915244153ce020b22a4882a39c043635491000537c12c6a922009a6c8258d524414fce020b1aa4880269ba1b6254910537b0086c4a922005a6e87d89524400b4d90fb12a4880029b613625491000536c1ec4a922050a778158952440d34f700b12a4882969ba18625491000596c20c4a922000b4d8318952440a1ccec2312a4881a79ad806254910527b0080c4a9220508f7815da42440d31f700bb484880035c0417590910006373b2a52122009c6c7654a424412bec020a9484880063d219719091000cf8402e321220028f8865c242440053e102b8484880033c04376509100047bc0aeca1220008fb805d942440019e0203b284880262f21d645091004d56412c8a1220a3eb01059142440018dceca9284880031b1d952509101cf17322a4a122000e2d645494244121ec020a9284881423de05768c91034c7dc02ed1922000d70105d632440018dceca9464880271b1d9528c910467b0082a519220018f4865c632440033e100b8c648800a3e219708c910014f840ae11922000cf010dd932440011ef02bb264880023ee01764c91000678080ec99220098dc8758d3244145da020b1a64880031b9d9524c910006363b2a49922038e4e635493244001c9ac6a926488213d8041524c91024e78386c890a20098f48759121440479e0e0b2242881173c1c3634851004c7a43ac690a2020cf07058d2144083dc6c031242880271d1d9524851004f32312a490a2036d707054921440033e50fb8242880633c1db704851025e7838ec890220098f887591204402b9e0e2b22408811f3c1c7634811004c7c43ac69022012cf07158d2044081dc6c231240880271e1d9524811004f34312a49022037d707154920440053e50fb8a408802b3c1db714811000cf843a429022001af08648520440059e0ec90a4088027b8189214811050fb1a92429022000f615248520440037c10e90a408800b7821d214811000cf043a429022001be28648520440037c10c90a4088027b8219214811004f71bb2429022002de2764852044005bc0ec90a4088027b81d9214811000771b22429022000ee1644852044001dc6c690a4088003b858d2148110
  | 1 => 0xb062a6c290142b9a0854d852000572c10a9b0a401caf28015361480015e3002a6c290072bca0073d852028578c00e7b0a40008f68714f61480011eb0e29ec290002ada1053d85200055ac20a7b0a4050ae68214f61480015cb0429ec290072bca0053d852000578c00a7b0a4000a778550f61480014e90aa1ec2900023da1c43d85200047ac3887b0a4000a768510f61480014eb0a21ec290003a550c43d85202857341087b0a4000ae58210f61480395e50021ec290002bc60043d852000733c12a5b0a4050e664254b61480a1ccc64a96c2900039954942d852000732a9265b0a40008f58799461481495cb05328c290002bc60265185200047bc3aca30a4000af38059461480011eb0f320c290002bc60264185200047bc3ac830a4000af38059061480815e500320c2900023d61e631852000578c04c630a40008f78758c61480015e700b18c290102bca00631852027f39b06a430a40b1e6762548614809fce6c0a90c29013fd8081521852000679080eca0a40028bc8759141480091ed0fb0a829000a3d204764c52000679080ec98a40028dc8758d31480071ed0fb0a62900db1b1d952485201bf3230aa490a4036d687054921480399e0e1b0a429003b3c18770485200e6723b6c290a4002ce47650521480059c8ec98a42900633a1db70485200067830ee6a0240048f88758d404802b5e102b1a8090002f8604725012004e3c3b2a4a024009d687254940480cbce0c2a9280900066e21d425012004e5c3b284a024009da8725094048001e52a4a12809018fac185425012027c7d436e2a024015cf061dc540480815e50db0a80901433c1db615012027e793b0c2a02404fcf0761854048001d66c830a8090057ac1854150120006f1b8e42a024015ee061c8540480035d10c90a8090003e850521501200067830ee898240098f8865d130480133d104ba260900033c185744c12001c7c43ac89824012af08159130480017c30239260900271e1d9524c12004eb4392a4982405ae706154930480033b10e9926090027361d9324c12004ee4392649824000f49524c930480b1da0c2992609013e3ea1b714c1200967830ee29824040af286d8530480a19e0edb0a609013f3c9d8614c12027e783b0c29824000ed3631853048025da0c298a609000378dc7214c1200977030e429824001ae8864853048001f826290a609000e37a0f75d91100046ec1eebb222000cf0105cf6444161ce021a96c8882bfac043745911000678086e6b2220aee7010d4964440475e503b82c8880122fa1375d8d100045ec26ebb1a2000cf0105d3634415bce021a96c6880033c0437458d1056768086e6b1a20abe7010d4963440415e503b82c6880023d6077650d100047cc06eca1a200587e859d943440010fb0b3b286880033c0427650d100043fc2aeca1a2005
  | 2 => 0x97348530106e83826290a60038fa86dc1214c0718f0eca928098003ca5494250130007a4a9264a026000f89424c9404c0033710ea0a8098002ae21941501300af5830a82a026001ad8864c5404c025ba0e298a8098003e450531501300061fba4e8b2e4000a5f835d165c80014b906ba2cb900030f5d074597200052f418e8b2e4000a5d831d165c80134dd043a2cb900469b60874597200053b408e8b2e4000a75811d165c806d4f5003a2cb900029e60074597200051fc22e6b2e4000a3c845cd65c800147d0839acb900028f61073597200062eb98e6b2e4009a6e821cd65c80234db0439acb900029da0473597200053ac08e6b2e4036a7a801cd65c80014f30039acb900021fa1c43597200043ec3886b2e4009a6e8210d65c80014db0421acb900029da0443597200053ac0886b2e4036a7a8010d65c80014f30021acb900269ba0a715972059536c14e2b2e4000a7b805c565c806d4f100b8acb900da9ea0341597200053cc0682b2e4009a6e8210565c80014db0420acb900da9ea0331597200053cc0662b2e4009a6e820c565c80014db0418acb9000237e0d755932001c6e41aeab264000cf010dc564c800117f08baac7900122f2117558f2000678086e2b1e400587c85dd943c80010ff0abb287900161f2157650f200043ec36eaa1e400087e8759543c80010f90eb2a87900038710d6550f2004c5e43ac8a1e4003a9c8359143c80131b90eb1a8790012a72116350f200145e43ac8a0e4079eb01059141c80131e90eb0a839000a3721d634c72038768082c698e40098f48758531c80017c700a0a439008f781c14148720005f1c026290e4020de0704c521c80031f100b8ec89000237e0d755912001c6e41aeab2240008f7815d564480051e902baac8901cf1d1c752591200147b43ee2b224000c7752dc564480019e0e3b82c8900063e20171d8d200e47a436e2b1a40008bf845d5634800917908baac6900023de057558d200147a40aeab1a4073c7471d4963480051ed0fb8ac6900031dd4b7158d200067838ee0b1a40028f681dd943480011eb03bb286900161fa167650d200043ec2ceca1a400087f855d9434800b0f90abb286900023de057650d200147a40aeca1a4000c7461dd543480134d905b22a4900029de0564549201bd3a40ac8a924009a6c82d8d52480014ef02b1aa4900de9d205635492004d3d436e0a924009b6a82dc15248001ce0c3b82a4900db1b1d9525092000717b22a4a124039e2c645494248123cc8c2a9284900db5a1c152509201b6363b2a49924000e4f63549324810bcc8c2a9264900db5a1c1524c92002c7bc3aa3b0a4073c7676d4b614806f8ececa96c290143d808152d85200e579400e9b0a4050af1801d36148001c6ea92a6c2900023da1c54d85200047ac38a9b0a4000ad68315361480015a
  | 3 => 0x2302424faf0864c46048401da6c6988c0908062f61375d8d4000678082e3b1a800087f855cf625000b0f90ab9ec4a00023be1d621894000536c14eca928000a5f835d952500714b906bb2a4a00029be0976549400053bc0aeca928037a74815d952500734f10cb82a4a02dedae09705494032db840ae0a928000b2d85189425000171b0631284a00270f1d9525094004f16312a4a128090f2a205494250001c5f0ca9284a00038b219525094004f17bb2a4a128009e2c765494250001c5ec6a9284a0243caa01525094000794c02a4a128090f28705494250073c5ec0a9284a00e7cad81525094048795182a4a1280b6f2b105494250121e5020a9284a00066ea03715094031ed8086e2a128000f2952dc142500011ef02bb464a000a3d205768c94000c5e432e91928000d2d7454a3250001a5aeaa1464a00263e219708c9400acf840ae11928038e4e6354932500091f301baec2a02d71e5c352d85401ce3cb82a5b0a8000e2d5250b6150009972e0a16c2a00db0f1d952505403df98082a4a0a8023bb281dc141500071ed0fb0a62a000aad219414c5400065a3b28298a8023db07050531500091f50db8262a00062f21974c854031ed8082e990a80098f8865c321500019e6203b242a00062f219744854011ed83828290a80048fa86dc121500031bb07baec8980033c04171d913002c3f43eeab22600087d82dd5644c0010fd0e3aac8980021fa1f525913002c3e43ea4b226000af281dc1644c00b1f10ea82c8980021fe1574d893002c3e42ae9b1260008ef87588624c0014db053b2a4980028fe1176549301cd1e422eca926000a6f825d9524c0014ef02bb2a4980de9d20576549300043fc3ac8a92600087c87591524c0714f10cb82a4982d2dae0970549302d5b840ae0a9260008f7815da424c0051e902bb48498006372197390930006a6b9aa521260098f8865c2424c0253e102b8484980262f21d64509301cf17322a4a126000e2d64549424c0131b90eb226498002d3614624c930005c6c20c49926009c5c76549324c109e9440a92649800393e19524c93000726432a49926009e4f76549324c013c98eca92649800393d91524c93000726b22a49926084f4a80549324c001e9300a926498213d21c1524c9301c727b02a49926038f4b60549324c109e9480a9264982cfd2c41524c930427a4082a49926000b4d85909324c001d1ac8a12649800676a03714c9302c6e8086e29926000f4952dc1324c0071f301baec29826f1e5c352d85301c63cb82a5b0a6000e4d524cb614c0079b2e0996c2980123da1f615053001c7d436e0a0a6036c5c76549314c0e5ea020a92629800b351d9414c530105e84028298a6020bd281dc1314c0031b90cb9e42981637404173c853004c7c432e190a60018f8801d9214c0019e6203b242980063721
  | 4 => 0x4484011f700baac8908063e20175591211fe3c386a4b2242018fa87dc164484018f6a5b82c8908033cdc470591210147a40ae1b1a42188f886dc1634840117f08baac6908122f2117558d210047dc02eab1a42018f8805d5634847f8f0e1a92c6908063ea1f7058d210063da96e0b1a4200cf3711c163484031f501bb286908023e6037650d2102c3f42ceca1a420087d859d943484010ff0abb286908161f2157650d210047dc02eca1a42018f8805d943484018f0c1baa86908029ee0164549211b53c402c8a924200a7b8058d524846d4f100b1aa490826d9a0b715492100738306e2a924237c6c765494248401c5ec8a9284908e78b19152509211beb238aa4a124290e6860549424846f8d8eca92649080393d8d524c9211beb238aa49924284e686054932484019e0c1b9a82908123d21d635052111d78402c6a0a4200be1801c941484138e8eca928290827591c952505213df38302a4a0a42029b4875094148413968eca128290827691c9425052100792a9284a0a4279eb060509414849f1ed0db82829088f3c183705052100678306e898a42098f4865d131484133c904ba262908033c181744c52101c7a43ac898a4220af08059131484017c30039262908271d1d9524c52104eb2392a498a4272e706054931484053a90e9926290827351d9324c52104ee23926498a4200f45524c931484e1da0c0992629093e3da1b704c52110678306e098a42058fb87543604847f8f4eda96c0908db1e9d952d812134fb010aa5b024269af08650760484479e4eca0ec0909a6bc21931d8121106793b263b02420eaf2811d360484d35e3023a6c0908038ed5254d81210047d438a9b0242008f98715360484015b5062a6c090802b660c54d812134d75410a9b024200ae982153604841d5e5022a6c090802bc60454d812107579408e7b024269af1811cf60484011f50e29ec0908023e61c53d81210055d420a7b024200ab98414f60484d35d50429ec090802ba60853d812107579408a7b024200af18114f60484014f70aa1ec0908029e21543d81210047d43887b0242008f98710f60484014f50a21ec0908029e61443d81210074ca1887b024269aea8210f60484015d30421ec09083abca0443d812100578c0887b024200e6b8254b60484d3cd484a96c0909a79a8c952d812100734a9285b024200e69524cb60484011f30f328c090ae2ba60a651812100578c0cca30242008fb8759460484015e702b28c0908023e61e641812100578c0cc830242008fb8759060484015e702b20c090926bca0464181210047cc3cc63024200af18198c60484011f70eb18c090802bce05631812122d79408c6302424fe7361d48604854bcd6c4a90c09093f9cd85521812127fb010aa4302424faf286504604849f5e10ca08c090803acd91411812127d794326
  | 5 => 0x80a2f219748c94100696ba2a51928200d2d7550a32504131e90cb8c64a088e7c201718c9411c72731aa499282048f581dd7605056b8eae3a96c0a08e71d5c552d814100716a9285b028204cb57150b60504051bb07baec8988033c04170d913102c3f43eeab22620087d82dd5644c4010fd0e3aac8988021fa1f525913102c3e43ea4b226200af280dc5644c40b1e90ea8ac8988021fe1574d893102c3e42ae9b1262008ef87588624c4014db053b2a4988028fe1176549311cd1e422eca926200a6f825d9524c4014f700bb2a4988da9e20176549310043fc3ac8a92620087c87591524c4714e90cb8aa498aeed9e097154931395b8402e2a9262008fb805da424c4031f100bb4849880a372197390931006a6b9aa521262098f4865c6424c4413e100b8c84988262f21d64509311cf17322a4a126200e2d64549424c4131b90eb226498802d3614624c931005c6c20c49926209c5c76549324c50be8c42a92649880393e19524c93100726432a49926209e4f76549324c413c98eca92649880393d91524c93100726b22a49926285f4681549324c401e8b02a926498a17d11c5524c9311c727b0aa49926238f4761549324c50be8c82a926498aebd1841524c93142fa2082a49926200b4d85909324c401d1ac8a126498803d154b714c931014eb40ee09926270dd010dc1324c4718e8eca928298803c95494250531007a2a9264a0a6200f85424c9414c4071eb03baec098a6f1d5c752d81311c63ab8aa5b026200e4d524cb604c4079aae2996c0988030fdd274597210052fc1ae8b2e4200a5c835d165c840187ae83a2cb9080297a0c74597210052ec18e8b2e4209a6e821d165c843f4db043a2cb908de9da0474597210053ac08e8b2e4200a7a801d165c84014f3003a2cb908028fe1173597210051e422e6b2e4200a3e841cd65c840147b0839acb90803175cc735972104d37410e6b2e421fa6d821cd65c846f4ed0239acb908029d60473597210053d400e6b2e4200a79801cd65c84010fd0e21acb908021f61c435972104d3741086b2e4200a6d8210d65c846f4ed0221acb908029d60443597210053d40086b2e4200a798010d65c84134dd05382cb90ae69b60a70597210053bc0ae0b2e4237a74815c165c846f4ed03a02cb908029d607405972104d3741080b2e4200a6d8210165c846f4ed03982cb908029d607305972104d3741060b2e4200a6d820c165c84011bf06baac99080e3720d755932100678086e0b2642008bf845d563c840917908baac7908033c0437058f2102c3e42eeca1e420087f855d943c840b0f90abb287908021f61b7550f210043f43acaa1e420087c8759543c8401c3886b2a87908262f21d6450f2101d4e41ac8a1e42098dc8758d43c840953908b1a879080a3d20570d91210046fc1aeab2242038dc835d56
  | 6 => 0x717ba6c8a9264c0e2c74d91524c8134df07b22a4990269b60f645493260f17a1ec8a9264c1e2d43d91524c8012df0eb22a4990a65b21d645493260716322c8a926400c6f87591524c80b4dd0eb22a4990169b21d64549320063643ac8a92640586c87591524c92f4df08b22a4990038be11645493249537c1ac8a926400e4f83591524c87169d0fb9aa4990e353a1f735493204da7436e6a926409b4c86dcd524c871a9cedb9aa4990e3531db7354932005a6c26e6a926400d4f74dcd524c801a9ae9b9aa499002d36077354932005a6c06e6a926400d4f8750d524c80169d0ea1aa499002d321d4354932006a643a86a926409b4e8650d524c8136990ca1aa4990e2d3e1143549321c787c2286a926486f0e7450d524c801e1ae8a1aa499003c3d9143549324378632286a926400b4f8150d524c80169f00a1aa4990e2d320f715493200537c32e2a926438a6c865c5524c80169f06b8aa4990e2d320d7154932005b5c02e2a926484b68805c5524c87169907b82a4990029be1970549321c536432e0a926400b4f835c1524c87169906b82a499002d9e05705493242db240ae0a926400d4f835d6424c801a9906bac84990271bd8d759093204ea7b1aeb2126486d4e435d6424c90da9a86bac849900353cc57590932006a7982eb212640999c8750d424c8135390ca1a849900f271d9435093204dc641286a1264bef0f5250d424c9258daeca9284990e31b1d9525093200717b22a4a126439e2c64549424c801a9ee6a928499003c350d525093204dc643a86a126403d8c8750d424c81371d0ca1a8499026e321943509320274643286a126404e8f7650d424c807b1ceca1a849900f631d94350932027463b286a126403c8c7650d424c801e1f0aa1a84992fbc321543509325fec7baa86a1264bfd8d7550d424c97dd1ecaa1a84992fba35954350932005c7c0a86a126400b8f8050d424c8718dae4a96c299217991855258532426b4382a4b0a6400d6952dc1614c8718dae4a96c099217591c5525813242734302a4b026400d6552dc5604c80517b09baec6a08033c04170d8d410043fc2ae7b12820587c855cf62504011df0eb10c4a08029b60a76549410052fc1aeca928238a5c835d952504014df04bb2a4a08029ee0176549411b53c402eca928239a74865c5525057b6cf04b8aa4a09eedc201715494100596c28c4a128200b8d831894250413878eca9284a08278b189525094148f9310aa4a128200e2f865494250401c590ca9284a08278bdd9525094104f163b2a4a128200e2f635494250523e4d02a9284a0803c9605525094148f9238aa4a128239e2f615494250473e4ec2a9284a0a47c98c552509415e793082a4a128291f24105494250401e4aa5b8a84a080a6da0770509413ced8086e0a1282008fb805da32504031f100bb464a
  | 7 => 0x6f865c152508734d90cb82a4a1002cbe1170549421cd96422e0a928400b67815c152509236c902b82a4a10e71b5c952d854248f3230aa4b0a8490d68705496150801ad2a5b82c2a10e71b5c952d814248eb238aa4b028490e68605496050801acaa5b8ac0a10030fdd2745963204d37414e8b2c648aa6d829d1658c8014bf06ba2cb190e29720d74596320061eba0e8b2c6438a5e831d1658c8014bb063a2cb190269ba08745963216d36c10e8b2c6400a76811d1658c8014eb023a2cb190029ea0074596320053cc00e8b2c6400a7b805c5658c8014f100b8acb190269ba0b415963200536c1682b2c6400a7a80d05658c8014f301a0acb190269ba08415963200536c1082b2c6400a77815c1658c8014e902b82cb190269ba0b405963200536c1680b2c6400a7681d01658c8014eb03a02cb190269ba08405963200536c1080b2c640087e87041658c8010fb0e082cb190028fa1010596320051ec2020b2c6438a5e83041658c8014bb06082cb190269ba08105963200536c1020b2c6405c6e75549648c8014df0cba2a51923b4b1d17454a32005a7c1ae8a946438b4c835d1528c8014dd0eb22a51923a9b21d6454a3204f17c22c8a946400e2f74591528c985c58e8b22a51930f8bd0d6454a3261f16a1ac8a9464c2e2f41591528c985c5e80b22a5190029be197154a32005b5c02e2a94648cb68805c5528c8014df0cb82a519002d9e057054a3246db240ae0a946400e2f84595428c801c5908b2a85190271bdd16550a3204f17ba2caa146492e2f43595428c925c5a86b2a85190038bd056550a3200717a02caa1464008fb805d5618c8031f100baac3190063ea1f705863234e3da96e0b0c6469c7952dc1618c8d39b665b82c3191a7364cb705863227e79b88e0b0c64008f7815d5608c8051e902baac11900a3da1f71582322863ba96e2b046450c7552dc5608c8a19ae65b8ac119143354cb715823227e79b80e2b046400c3d75d53644c80155b05aa6c8990171b9d552d913200717aa2a5b226486e2c5454b644c8011f700b8ec8990063e20171d91320047bc0ae1b2264028f4815c3644c80b0fd0fbaac8990022fe1175591320046fc1aeab22640087e871d5644c801878ebba2c899003171d773591320043f43ea4b22640587c87d49644c80b8d8eb292c8990163b21d52591324fe2e3b6eaa1a649fe1c64dd5434c80953d0db228699002d36147250d32004ecc06e2a1a64009d581dc1434c8714db05b22a4993038bd0b64549320043fc3ac8a92640587c87591524c8012b90ea1aa4990269721943549321cf0e32286a926486f0f4250d524c87169907ba2a499003c390f745493200537c32e8a926438a6c865d1524c90da58e8ba2a499002d3e0d74549321c5a641ae8a9264c0e2e64d91524c9314dd0fb22a4990d69b21f64549320
  | 8 => 0x839acb21003175cc735964204d37410e6b2c8435a6d821cd65908014ed0239acb210029d60473596420053d400e6b2c8400a79801cd65908014f700b8acb210029e201715964204d3741662b2c8400a6d82cc565908014f50198acb210029e603315964204d3741062b2c8400a6d820c565908014ef02b82cb210029d205705964204d3741660b2c8400a6d82cc165908014ed03982cb210029d607305964204d3741060b2c8400a6d820c165908010fd0e082cb210021f61c10596421cd1f42020b2c8400a3d8404165908014bd06082cb210029760c105964204d3741020b2c8400a6d82041659080b8dceaa92c7210029be197354a4200597c22e6a948439b2c845cd529092fa98e6b9aa5210029ba1d6354a424bd3643ac6a948409e4f8358d5290801c9ee6b1aa521307931cd6354a4260f2721ac6a9484c0e4d4358d5290983c9e62b1aa52130793cc16354a4200537c32e2a948400b6b805c5529092b6d100b8aa5210029be197054a42005b3c0ae0a948496b64815c152908011f700baac3210063e201755864200c7d43ee0b0c8469c7b52dc161908d38f2a5b82c3211a72ed0b705864234e5ca16e0b0c844fcf3711c161908011ef02baac12100a3d20575582420147b43ee2b048450c7752dc560908a18eaa5b8ac1211432dd0b71582422865aa16e2b04844fcf3701c5609080b8dceaa96c6a100393d4d52d8d424972629aa5b1a84008fb805c763508031f100b8ec6a10023de0570d8d420147a40ae1b1a849ec3c76dd5435093dc38c7baa86a100ea7a1b6350d4200596c28e4a1a8400d2f751c9435080137301b8a86a10026d6077050d421ce1f3b6e8a928409b2e82dd152508734db05b1aa4a10024f21d435494204d1e43286a928438e1c6350d525081365904a1aa4a124bc3cc943549421cd9743ee8a928439d2e87dd1525081365d0dba2a4a1026cb21b74549421ce973b6e8a928439d2c76dd1525080165b07ba2a4a1002cb607745494200596c06e8a928439b2c84dcd5250801a5ee9b9aa4a1003c3d0f735494200537c32e6a928439a6c865cd525080165f08b9aa4a10e6cb211735494200697ba2e6a928492d4c735cd525091f4dd0fb1aa4a10b69b21f635494204d36c26c6a928400e4f73d8d5250987c98e7b1aa4a130f9390f635494261726a1ec6a92840096f8758d52508632d90eb1aa4a10034be1d43549420059743a86a928400b2c8750d5250801a590ea1aa4a1026cba19435494204d9643286a928439b2f8350d5250873e1f06a1aa4a124bc39cd435494200786b9a86a928400f0f6350d5250925e18c6a1aa4a1002cbe05435494200597c0286a928439b2c84dc552508014df0cb8aa4a10e69b219715494200597c22e2a928439b2c845c552508016d700b8aa4a1242da20171549421cd96426e0a928400a
  | 9 => 0x64591521c4af43ee6b22a400e1c64dcd6454801a9f05b9ac8a900317d8b7359152006a7b16e6b22a400d4e42dcd6454801a9a85b9ac8a900317dd873591520068fba0e6b22a400e1c641cd6454997a5ee9b92c8a932b8b1937259152006a7b9ee4b22a400d4c73dc9645493b2df04ba6c6a90265b20974d8d521c43ec3ec9b1aa439c3e74d936354801c3887b26c6a90021fe1d64d8d521ce1e3a2c9b1aa438a5c8359363548014bb0da1ec6a90038759343d8d52005a6c1687b1aa49a96f825c763548132d904b8ec6a90025ee0171d8d521b4bc402e3b1aa49996f825c363548132d904b86c6a90025de0570d8d521bcba40ae1b1aa43993e87dd16354801c38c7ba2c6a90034be0b7458d520061fb16e8b1aa400d2f62dd16354801a5c65ba2c6a90034b4cb7458d520061fbb0e8b1aa400e1c631d163548010fd0fb22c6a90e70f1d36458d521c52e41ec8b1aa400e1e43d9163548710f90eb22c6a90e70f1d16458d521c52e41ac8b1aa438a5e86d8d6354801a38e9b1ac6a90034bdd37258d52006963a6e4b1aa4c9d4f73dc96354991c98c7b92c6a90025b60b7650d520070e21eeca1aa400c6d82dd943548018dc85bb286a90031b8cb7650d520043f434eca1aa400d1c439d9435480127f08bb286a900257e0d7650d52004b7c12eca1aa400d1c431d9435486f2ed023b286a90025d6047650d521b4bd400eca1aa400979801d94354801c38863b286a90030fa107650d520061ec20eca1aa400c5e831d943548018bb063b286a900317d0c7650d520061f218eca1aa400c3c431d943548018b8863b286a90030710c7650d5200636c10eca1aa400c3f421d943548018dc843b286a90031b5087650d520062f990eca1aa400c6e321d943548018da643b286a90031da047650d520063ac08eca1aa400c7a801d943548018f3003b286a90e24f21d6450d520061e3b2c8a1aa438b1c83591435498f65f04b2286a90e65721d6350d520062e3b2c6a1aa439b1c8458d4354801c3ac8b1a86a931ad3e096350d5200637bb4e4a1aa400c6c769c94354983e188739286a90f29b2197250d52006363b2e4a1aa4c3f0c435c943548132dd05b8a86a90025b60b7150d521b4bd406e2a1aa40097980dc543548132dd05b8286a90025b60b7050d521bcbb40ee0a1aa40097581dc1435498bacee5b0ac2a90da5ea1f7058552006b5b96e0b0aa400c7b62dc16154801ad6c5b82c2a90035adc87058552006b9b88e0b0aa43687d87d876054801ce021b0ec0a90da9e20161d81521bcbb43ee2b02a400d6772dc560548018eec5b8ac0a900359d8b7158152006b3b90e2b02a437c7471d85605486d0f90eb0ac0a93135adcb6058152006b838ec0b02a409a6e829cd65909034db0539acb210028fe1173596421cd1e422e6b2c8439a3e841cd659080147b
  | 10 => 0x18000008010000008000008000008000020000000000000008010020000008000000008008000008010000050000000000010008008010008000000000008020000000000000010000000008000010000000030020000020000000000000000008008000008008018010034710d72d954300637b94e5b2a869fa3e841cb6550d3d47b08396caa1a7a97a0c72d95434fd2ec18e5b2a8600a76811cb6550c014eb02396caa18029ea0072d95430053cc00e5b2a8600a7a80dc76550c014f301b8ecaa18021fa1c21d95430043ec3843b2a869fa3e840876550c0147b0810ecaa1a7a97a0c21d95430052ec1843b2a8600a7a800876550c014f30010ecaa18029da0770d95430053ac0ee1b2a860087e870836550c010fb0e106caa1a7e8fa1020d95430051ec2041b2a869ea5e830836550c014bb06106caa18029da0420d95430053ac0841b2a860087e870436550c010fb0e086caa1a7e8fa1010d95430051ec2021b2a869ea5e830436550c014bb06086caa18029ba0810d954300536c1021b2a8600a6d82dd76250c014db043aec4a18021fe1571d894302c3e42ae3b12860087f855c36250c0b0f90ab86c4a18034710d759894369f0e218cb3128600a6d821966250c01a3887baac4a18021fa1f65589430043f438cab1286d3c3f741956250da58bee632ac4a18034710d751894304e37312ea312863c87d87d946250c014db05b28c4a18031d9c765189430063d386ca31286a0c3d741946250da38bae6328c4a1b438710c651894300536c10ca3128600c76711946250c018f4e0328c4a18023be1d621894300636baac43128600c77655c46250c018e8cab88c4a18036510d71189430063db2ae03128600c78655c06250c01b3086b80c4a18031e9c365d854367f0e218cbb0a8600a6d821976150c018f4e032ec2a18031ed9570d85430063c32ae1b0a8600d98435c36150c031f501baec2a18023e60375d85431fe3d386a5b0a86018fb875c36150c018f6a4b86c2a18032ed0970d85430066d992e1b0a8600d1c43dd56150c010fd0fb2ac2a18021fa1c65585436770e218cab0a8600a6d821956150c018ece3b2ec0a1b378710c65d814300536c10cbb028600c76711976050c018eecab8ec0a18031d19571d8143006ca21ae3b0286028f681dd76050c011eb03baec0a19cf1d9c752d81430147bc3ae3b028600c77525c76050c0196e84b8ec0a180335cc971d814302c3f436eab02869e87c86dd56050c01a3887baac0a18021fa1f65581430043f438cab0286cce1c431956050c014db0432ac0a1a725be0973d915204cb6412e7b22a400a3d8690f645480165b0521ec8a926a5be0971d915204cb6412e3b22a40097b805c7645486d2f100b8ec8a92665be0970d915204cb6412e1b22a400977815c3645486f2e902b86c8a90e68fa1b
  | 11 => 0x4310000000000000000000000000000002c700030606600002300000000042c4190f259b3660000000001082ec21d0000000003610970000000000000000000005964ca00000000056c0e81c60004400000000005e10e30000000004f60000000000000000001030003b62660000bb00000920b06e4af00005c0004590000000960d80000003ea0005d22650002ee3ae0000002cc00000000000000015d00000022847408b5e20000334ec00000000000054d32644f0461010150000000000000000000000000001d40a200013612e1f40004ac0003f900000000000000000000000052404d27b0000000000000000004b30003860000d90000000003c50000005250000000004f10000000000003800000000000000002523d80000a831a00023700000032800057900000000000021a0000000000000801440000000000000000000001ef23a00000000039c0002c63c10000001da0000000000000181c450f00000029f00017609e00049854800000051e00000000000000000000000000080000080100080080200100000000080180080000080000000000000000080180000080000700080100380000080100200000100080080000080100000080080180000000080000100080180080000000080000180300000080000000000180100100180000080000300080200000100100000180180000100000400380080200280100000080080200400200080100000000280000200200000080000000000080080080000100080000080000000000100000000100000200200000000200000000000000080080000080080080000000080000100000300080080080100000080100000080000080000000080080180000000000000000000280080000000080000000000000c00000000200080000000000080080580000200000500080000000000000000000080100000200000000080180080000080100000100180000080200080080000280000000000000180100000000080000000000000000000000100000000280000000180000100200480100080100000080280000000000000080000100000000080200000000000300080080000000200280000100180000000100080400000000000000000600000000180000100000180000200000000200000100080000180000580080080000080300100000000080080000100080200100000100000600080180200000000000180080080180100680000000280000100080000100280000080000000000200080000000200080000000000000000380180280000300000200000080100000180300000100080000080000000100080280300000000280080200480000000000080100280000000000000000000200180080000000080080580100080980300580280080000280280180280000180
  | 12 => 0x5d21b00000000004c0ec00000000003a00000000000009f23b00000002c00000004a00017f0002af0000000000003c300035400000010f0c500019100000000000000000055600027900b00000000000052b0000000000000004b40000003c600030400000052645c00000000000035000054b0000003510483135520000000000002e60000000000920000130000000000000630000000000000000005550000000000000650000000000002ae0001e503e0000005aa00030c34d00000022906200027a53432507f00018729e0000000004da0001f91c11f03d12dc5c15e40e753905e15803b2114140f800000000000000000000000054e0000000003960e539b22203100000000045d0003a828c0002d800000000000000000000000000028a0000000000000000000000002c00000000000f62050000004962270000000000b70000000000003e24215d93b900000009c00000024a0003dc2f02750000000cf0000000000910000000000000a934e0001e700000000000041d3793410000850000000000003470004ed2ab4e100021c2e742039f0bd00005016f5e00001432ef09306f4523c74d718b16b3a90000000000000450c800015c00057819b00000052714c53221f48900000000000041301a2cf0000000005ac00000029d1aa0005c80765740000000000000000004bd12440d0000001610000000000000000000000000e60000000000000000000002f300000000054300036500040500000043631b00038700000000016a0000000000000003970000000000000000004cb00000000000015900000024f00000000000026b0ff00000019009a00600035c0000001324c83bd08100000000041632721909806900000000000000000000000000013400013e3d60000004e000014a25d0000004091f705358602b00000002e5770000000002b332a0000005b20b212012c5440d00000000000000002450003480000002e400029b00500000000000044e3402075d74470001ff0c60005040001cb07a0003440000002133593c44e93fb5712db2460000000000000000000000000003fa0000005850ad0000000004990000000001624d00000000000000005ce2b500000000002834b0002ac0000000000000000994e24d408722a1f52331d30005230000000000000843f550300000023f2a00000001f60000000000002f912900000050a0003cc3f85970004f71cc13d0aa0005c400054541c0004ff0005cb0000000004260000005352b20005580000000410000001f30004f200032019c00001d1cd0cb5c900000000000000000000000047c1ed0fa0c024c5df4d35c313a0001110000001fd04000008900000053b0004445b054a4db52e40a47837b00000000043a38300000037c0004e70fb00055d0000004274cd11c0163b70ab19a
  | 13 => 0x20002902ba0000000000001fa2610000001410033af1de26400000000000000043b5d85400000710003750000000300000005bd0000603e321708e58a0002620000000000000000004df32d0000003c80000004bb5010780000002b41730342952c40644d10000001c200048c2540550000000002d33352425d500000000049d00007949305f1dd1983360001be4c71370fd27c0000000001ee0000000de0010000000000000000000000125990000000000000000000471e92382f640400022600000000002f00000000000034a1ea0000420000000000430000000001fe0000000000000000000000000000005a622c00000051038532f43700000058e46f51b1640000005531163815720ae0005510000ce00000011902a2245be5945e600000000000023c0000c71b80002d21070000002d70000000005980000005953760002c80002440000000001f24223cd36700023500032b1c30000000000000000000000004fe0000000000f70001093bb48100022e00000051300000025f4293885c654111f00037700000000000013b00000000000000000000035f0000000000000003e700030b1c90000000002480003ac00039d0005b30000000005190003df56f11805251417b00054923e0005a433f0000000005890000000002bf0000005a85050000000000005920000004a75c70000001670000003d40000000001df0000003c20000000000000000000000002e20000003620003180000004c008f4c30005ae47500015e00000000000015f0003945cf0000000002080f94150000000000002df1750000000000000000000000000000000000003420002b70001280000000003f41c800000000028d0004c255f1d71041fc1141381b04874394621480f03f31650000003104ba33d00057e0000001fb48a00000000000012f0004610001af00000000044b1100001ce0000000000000005870000172720000000bf1792b93ee4770000002033080580001f12c300052100000000000055e00000000000000000000000003600000000000054c0000004eb0004100390001994250003141ad0003a700000020200000000000000000000000000007c00000000053a1a833447600d0004b52780000005930000000000000005ab11b36826e4a41121470001742b118643d0f32d91523b53cb0ca00000010d0001b658d49400000029c2e852200044d0000000000000000000001ba1952470cd00019f00000000031645e0002740000000000002b000000001446a3523d200030a00020c00000027f58f0004dc0004910001230000274340000005330000000000000000000000000000000000000000001e30000ba00023107e2e318c45000028600000000018d00000000000028300005d2430a400030126a00048d0003994420003a40000000003
  | 14 => 0x17d0260f40000000000000004c50000000002150000003e15e54ce0000003b35c23b800000000018e36a00030e00000000000000000000000000000000000041700000000000000051600009d5d13e917a2a925523d26800030011e00000000000000010200006c0002990000005310001352cb00011d00005712500050c3d30000002580005c03714a508200022500049a0ea00000050820d4c63a125b00038c00000042f0000000700001e20000001a20000000000000000002fe00000004e55c00000000032322300000000010c33a09552a0000005e70000000000000003dd49210031200000000048446906823253f0a11a14ef5d45c53985090004a00a75660000000004513740000002300003910000000000000000005ad02d2b80003290000000000001d10000004a22a80004b10002ce0e000000000000056733c1554a100000000016d00031100034927d10a2f40004b90003b24b700000055b0005d33ca0004a30000000000003bc24100000000019e0000000000000000000000000002bd0000004182a200001f00002456e2be0000004b80000000000000000040000000000000000ed00000000036c3b40005603370003ef3732590004bc1e40000005610000290000000005a500000038b0dc00021e0001ac00000000000000051a14632c00013343f1450004080001eb00006700000000045400015013000005a2344494e50562930001693780000000000004fd00056950600001c0000002c20003301b300002200017e3390000004a60000002cd08c00000000000000000000000037a47303c33856d00000000000000000000022f0000000000000000000000002a30000004430000004f030300000000006a2ca10e47245f4703530002a60000000000000003d927000058c0000001490000000000000000003e00005a00000860000000000000000003a60002a13b040e58800047114e00000000000004b00000000000000000000000000000000050d36e35a03d5570000000000000001d900000043000052f02100000041b51800000000000000000c0003320110000000b90610003055764800000004ea0000000001dc3d53ff1850003565cc0000000000000000000000003a518400000000047d2100003f01b945a00000004919d00057b15b00000014f3171ae0000000001db3210000000002810000000000004a80005cd21457c00000000057f0a60000004460000000002a700054250b2de42b44c4cc00049f43c12700000031e0e44aa26f35b0c434600029a1d23024d21400000000070000000004a90000003841c00b84350000000000000000c94971a400000052000000053e5b900000020a2631934ae0001423fc0004b60000000000000000000002a53ed00037213939e3bf00056400015351700000000012
  | 15 => 0xf81685a90d708a0000000003b11e60000be3ec0000005a753d0000000000000000dd00000000000007500000000037e34551d0000000000000000003f60000000005022180003de0c12120ef3220003a235e2a400000000000000001000024e3e61882bb5d60b42562870000000001b40250000004b200000028e5595b559c3950000000000000000000373892940004e30b140c08d50e0000001b720412b4850901784fc3f10ac13c17216c4f505b40600023900000000007211500025c00012d3fd4ee0000000b00002c50005074010000001d01b12c12360001b20000001055e81ca0d33ce5901e00383f716000000024900036b57a3e81d517100047f32400047e1214de0002202b60001a51660000000000000000004280000000002d00000001bd0000002760000002c92690000001c500000048e1701bb20e0005121890000000001b54680001a943e0542f158433e38d32e4f40002e90005bb00010b07707d59a0000002fc4fb20051c0005374ab30d0000000000fc4c100000030942e2710000352e100000000000009b0003930005ca44831d0730004413333db0f52d446e00000000000037d49b2eb00028b5800b54952aa0004070000000000000000000000005b42fa00000057501b2841a70000003a04d82e50000000000000000000000000002673ad0fe0000000000000001d600000000000000000055a0004f300025e0190001a611a1265910003ba40b2d60005360e25832210000005680004904bf2855a32e000000000057338f46000000000000000052c4d559f5650002965dc00000019200000000008800000000000000000019740f5464f80000004580004c900051f0001510000f10004cf1770000a50005b10000004560000000000000000002da20136f0003570000da0000003900744820001e856b4110000005b700000000000042434c2823c05d01560000000000000000000000002805540000001c700045b0004860b61960002f853c0000e15db24014b28f0df3434530000d248f5da4831633fe0000c32f700007b4d90004232980003eb0001130000000000943ab2515a129100000000022b0003632d54640081d80d649c00049e5af00015a00000000052857000000000041a0000000000000000000004570002ea0000001170001820002f50a318000048b3d72f23551bc00046700001e0cc00051500000034f00033b0000003e542d00024d3e41310000005294e64b000000000059d0000000000000000000005b80003152770002974d60000000000000d12ed08300000000000000000004f0000000001ec38a00015437f00000000000053815725a00012a00017c45500046b3820d550022d26d2575b613f0000000000000000004e439227300018a24b00000058b26c00057d000292000000000000000106
  | 16 => 0x3f24dd0003194e85bf0000000000000000000000000000000005ba16e0000000000203d000a00000000000000000000038e0000000000000000000003580000000000db40300005939a0000005de14d53000000003200000000040236d31c0a01bf5a20000d41cf0b300000056a2ad0002bc0000000004ad0000000000000000000000000c23cf0000000004632d100042a5470000004f900052d0000000000002093be0004320020003604384450e90000004790000000004004330000440bc0af1813aa2fd00000000036446555056200000000000000000036941f00000006b2fb56300000f0513da00047a18f46d28831f5dd00059e46c5810004c400e5bc2ff4880000000001a000054f0000000004120eb00000027e0002600ee00003f0000000005820001ab20f3c944a2164be00046630f3312dd1945e351128947b2503a34fa06d2531a32060000000003701e141e0001830003070001
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x80154990cc5759093200551647305d6424c80130c9850d525093204d8325943549424c871c0c7650d52509324fe8321b8550d424c93dc0c76e154350932004e26438150d424c80138591e01435093200538648105c363504736249660552509415e5c8241815494250473c257154942d814100538648105c3644c47164496605524c9315d5d024181549324c471c457154932d81310040fe61741d165c840141c935d07459721006075d1831d165c840141c945cc735972100607611731cd65c84014e19204370593210053864810dc163c840121d9810d6550f210060721c4359543c840160d9210d6550f2127e98a0860dc5524841392487549425052104f091d9525094148579e2060549425052127e38208605d1314841394487549324c5215d790181524c931484012699221543d8121006866154310f6048401a894360843d812100538648105c763500736289660152509405b5c8245805494250073c297054942d854000538648105c7644c07164896601524c93059dd024580549324c071c497054932d85301056425d414c5404c047a908650531501300040fe61741d165c800141c935d07459720006075d1831d165c800141c945cc735972000607611731cd65c80014e19204371593200053864810dc563c800b06d9221d6550f20004876604359543c800181c8710d6550f20005836484359543c809f1e297e01414872027c78a5f804c521c809fa62821877054920004996488550f6148001a158550c43d8520006a150d8210f614801392887549425012004f0a1d952509404816de2061549425012027d38a5b71c854048047aa086505215012027e38208615d1304801394887549324c12059f90185524c9304809f4e296dc7214c120106b02193148530480014e19204173d91100053864810dcd64440014e19204174d8d100053864810dd163440014e1920427650d1000538648105d9434409f8e0820417650d100055864810dd5434400156192041759891027f18188105d6624400156192041751891000568648105d062440015c19204173189100059864810dd9524400166192040765491027e98208101d952440a1a2761610625491034e8ad81841895244001b2010610625491028691d858318952440d3a4b6060c6254910006d00418318952440015619204175909100053864810dd9424409f8b184040765091000538648101d94244001c60101d9525091004d0b25d6454942441abe2010591525091000558648105d632440014e192043764c91027e3460c101d932440014e192040764c9100071804076549324401344c9758d524c9106a79004163549324406d96087549214811004e98219524852044013c6076549214811024e3821f6448520440478e087591214811022e3821f6348520440418e08758d2148110
  | 1 => 0x30061960a711976050c014659219571d814300545654435c76050c01c146510d71d814300561648435c76050c0111e9810f75581430054364843dd56050c01a0c4360865581430040fe5d8690f645480121e98193735915200507a5c64dcd645480141e96dd0735915200487660641cd645480141e9719073591520058364843d93635480105f9761b43d8d5200487e6164d0f635480141f9759343d8d5200487a6063dd1635480141e9718f7458d5200487660631d1635480141e9790f6458d5200607a1e43d91635480181e861d36358d5200487a6043dd9435480160d9210f7650d5200507658439d9435480150d9210e7650d5200447660431d9435480141d9610c7650d5200543648431d9435480121d9810c7650d5200583648431d943549ada0d8210c7650d5200607611831d9435480144d92d0c7650d5200507a4e431d9435480142d9290c7650d520040f660431d9435480142d9210c7650d5200417660431d9435480144d9210c7650d5200507e60431d9435480181e9810c7650d5200507660431d9435480181d9810c7650d5200407660431d94354801c0e9210c7650d5200507648431d94354801c0d9210c7650d5200503648431d94354801c169110c7650d5200705644431d94354801c1a9010c7650d5200706640431d9435480182d846087650d520061360d821d94354801c0c436087650d520070310e421d9435480141c94cc87650d520070310e321d94354801c1443a047650d520061960a811d94354801c14436047650d5200619609811d94354801c1843a007650d520061a60a801d94354801c18436007650d520061a609801d94354801871816007650d520060720c76591435480181c841d96350d521c4872616458d435487141c975916350d521ce0721d6458d4354801c0c431da7250d520041ba60765c9435480182f841d97250d5200613e0c765c943548016619204361d815200607611731cd659080181c6321d4354942004cae4181dd152508013279160374549421ce0b21b745cd52508013259121d4354942004ca6408750d525080190f8321d43549421ccc32617350d525080190c875cd43549421cd832597350d525080132990e054354942004c96478050d525080103f985d07459632006075d1831d1658c80160d932116550a320058964484595428c801629902116550a320058a64341595428c80162591d016550a32006071908750d524c80182c87e1164549320061321f83591524c87144c965d37354932004d2e4181dcd524c801347916037354932004d16448750d524c8013499021d435493200643e108750d524c87130c985d143549320064321d7450d524c87160c965d14354932004d26438150d524c80134591e01435493200543650835d6424c8015459120d759093200552640835d6424c
  | 2 => 0x6400000f214c0040c000d87b000000a04d3e8c8000002e4000280000090000121c87a0007f428003800022c9106ca3254000240e000f03000021caf06832000f10004f304020001e391081a48e000001000040800000851d800000ca324152840011c00000000005f0007c00000000000000000000000e301c001f44e178b041c6e0000000105118b3268580501c3a0000e84300000089010008c000eb00050164b500000131001bc9209800030fe3b000000c71286612065378dc2f4350003027d091e50418ce6258a8190cc33cf91c000310c639c00200202346d27867418031c43b00008298e200000000001ac002f031094f33d42b07ce13f4a72e0ba30cc2000f70bc003a4a5000ef000000b8003b4182a862000811d4570000d280f8000d20841d00000004d93fc41000fb3340511400000cb00023168160fcce110db000d52a400000fc0a4000003c000b424c00150001dc0b00000264d7108ea1e034090003406c274ee0002a000110e40022086000172b0001480000000158842c81004c9c00006344be1809812c00250f4288ad03c000000000000000e5000000dc741245c37c3d228ab09ca40002c25c8920cd426c00314d834cbb000002dc00000f6000d62d8b123c732086a144ae0b4001f85d374610e0da154001a0330000416cbf0f80002c00000380c0400000180002018040001018000001000101401048040001000140a02020180c0000834020000008020100800040a08004020300804041b1180000000083004000501c000002800000101800000102004120700014021b028040801090080111e9810d72d954300543648435cb6550c0111d9810d759894300543648435d66250c01a0c43608659894300447a6043dd56250c0150d9210f755894300447660435d46250c0150d9210d75189430060b5d1821946250c0184d7360865189430061960a711946250c01869829c0651894300519648655c46250c015159510d711894300705194435c46250c015859210d71189430051a648655c06250c015199510d701894300706194435c06250c015899210d70189430068310d821976150c01079989c065d85430061a60a701976150c014699219570d854300546654435c36150c01c186510d70d854300562648435c36150c0111e9810f75585430054364843dd56150c01a0c4360865585430068310d821976050c01075989c465d814
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x100600110000021d12000698138b1a0180001aa1991d9f00000b80161480208a09908000000597941e01009b038e040018971f8d0c19889500129e8520001b80071c8483000f08118e829c158a890d80210000079300168c8f800784060808000002800a18b01023cc00001000100441b5221b0432cc4a1802415a9194435c46250c01a0232b2421ae231286009066a46510d7018943006810cac9086b80c4a180220da910d821976150c0120cd48ca21ae1b0a8600b026886510d70d8543006810cac9086b86c2a180220da910d821956150c01106d4886c10cbb0286009056a46510d71d814300580b4432886b8ec0a180340465648435c76050c01106d4886c10cab0286008836a19210c7650d5200481b45cc0863b286a900300da2660431d9435480180b50b30218eca1aa400c056859810c7650d5200603540cc0863b286a9003019a0660431d94354801806cc524218eca1aa400c036619210c7650d5200481f50c90863b286a900301598a44431d94354801a02c9522218eca1aa400c056619110c7650d5200680b24c88863b286a900301998a40431d94354801a04c9520218eca1aa400c066619010c7650d5200681324c80863b286a900341191640431d94354801206d4886c10eca1aa400a036a0436087650d5200501b5021c843b286a900280da810e321d9435480140ad4087408eca1aa400b0168843a047650d5200502b5021b023b286a9002c05a210d811d94354801c0221b04c08eca1aa400a066a043a007650d520058134421d003b286a9002819a810d801d94354801604d1086c00eca1aa400e0210d826007650d5200702086c0b003b286a900240da910c769c94354801406d40863b4e4a1aa400a03a9b8321d43549420060192c43ae6a1aa4a100201da91908750d524c8014075370843a86a926400c03258875d14354932006018ec4c286a92849900201da921c4359543c840180643b2421acaa1e42008076a48710d6550f200060190ec9086b2a879013e0e0a8648105d9434409f23053324082eb312204f898ea192043765491027e14308c90203b2848813f4219404076549424409f860c1b24080ec992204fd1064c101d9524c910
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xe00080ca40206010004409ba1959210d70d8543004405ba1959210d71d8143006005a26859810c7650d52006009a26819810c7650d52006011a16819810c7650d52004805ba10d826047650d52004809ba10d826007650d52005801b210d816007650d52
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
  | 18 => 0x9ca
  | 19 => 0x9ce
  | 20 => 0x9cd
  | 21 => 0xa0a
  | 22 => 0xa0e
  | 23 => 0xa0c
  | 24 => 0xb09
  | 25 => 0xb0c
  | 26 => 0xb0d
  | 27 => 0xb0e
  | 28 => 0x1549
  | 29 => 0x154c
  | 30 => 0x154d
  | 31 => 0x154e
  | 32 => 0xb49
  | 33 => 0xb4d
  | 34 => 0xb4e
  | 35 => 0xb89
  | 36 => 0xb8c
  | 37 => 0xb8e
  | 38 => 0xcc9
  | 39 => 0xcca
  | 40 => 0xccd
  | 41 => 0xcce
  | 42 => 0x15c9
  | 43 => 0x15ca
  | 44 => 0x15cd
  | 45 => 0x15ce
  | 46 => 0xd09
  | 47 => 0xd0a
  | 48 => 0xd0c
  | 49 => 0xd0e
  | 50 => 0x1609
  | 51 => 0x160a
  | 52 => 0x160c
  | 53 => 0x160e
  | 54 => 0xd49
  | 55 => 0xd4a
  | 56 => 0xd4c
  | 57 => 0xd4d
  | 58 => 0xe89
  | 59 => 0xe8a
  | 60 => 0xe8e
  | 61 => 0x98956
  | 62 => 0xb0956
  | 63 => 0x1a09
  | 64 => 0x209
  | 65 => 0x8a
  | 66 => 0x1409
  | 67 => 0x128a
  | 68 => 0x16c9
  | 69 => 0x1449
  | 70 => 0x168a
  | 71 => 0x12ca
  | 72 => 0x1849
  | 73 => 0x1489
  | 74 => 0x180a
  | 75 => 0x130a
  | 76 => 0x9c996
  | 77 => 0xa0996
  | 78 => 0xb0996
  | 79 => 0x4b
  | 80 => 0x124b
  | 81 => 0x1709
  | 82 => 0x1889
  | 83 => 0xa09d6
  | 84 => 0x9ca16
  | 85 => 0xb49d6
  | 86 => 0x138c
  | 87 => 0x124c
  | 88 => 0xcc9d2
  | 89 => 0xcc9d6
  | 90 => 0xd49d2
  | 91 => 0x128c
  | 92 => 0x18c9
  | 93 => 0x1789
  | 94 => 0x180c
  | 95 => 0x130c
  | 96 => 0xb8a16
  | 97 => 0x138d
  | 98 => 0x124d
  | 99 => 0xd0a12
  | 100 => 0xd0a16
  | 101 => 0xd4a12
  | 102 => 0x128d
  | 103 => 0x168d
  | 104 => 0x12cd
  | 105 => 0x138b
  | 106 => 0xb4b16
  | 107 => 0xb8b16
  | 108 => 0x170a
  | 109 => 0x188a
  | 110 => 0xb8b56
  | 111 => 0xb4b96
  | 112 => 0xccb51
  | 113 => 0xccb56
  | 114 => 0xd4b51
  | 115 => 0x1a0a
  | 116 => 0x140c
  | 117 => 0x18ca
  | 118 => 0x178a
  | 119 => 0x184c
  | 120 => 0x148c
  | 121 => 0xd0b91
  | 122 => 0xd0b96
  | 123 => 0xd4b91
  | 124 => 0x140d
  | 125 => 0x16cd
  | 126 => 0x144d
  | 127 => 0xd0cd6
  | 128 => 0xccd16
  | 129 => 0x160cd6
  | 130 => 0xcd616
  | 131 => 0x40c
  | 132 => 0xd4cd1
  | 133 => 0xd4cd2
  | 134 => 0xd4cd5
  | 135 => 0xe8cd6
  | 136 => 0x188c
  | 137 => 0xd15d6
  | 138 => 0x15cd16
  | 139 => 0x3cd
  | 140 => 0xd55d1
  | 141 => 0xd55d2
  | 142 => 0xd55d5
  | 143 => 0x3ce
  | 144 => 0xd4d11
  | 145 => 0xd4d12
  | 146 => 0xd4d14
  | 147 => 0xe8d16
  | 148 => 0x170d
  | 149 => 0xd5611
  | 150 => 0xd5612
  | 151 => 0xd5614
  | 152 => 0x40e
  | 153 => 0x128e
  | 154 => 0x140e
  | 155 => 0x1a0c
  | 156 => 0x170e
  | 157 => 0x188e
  | 158 => 0x194c
  | 159 => 0x17cd
  | 160 => 0x74c
  | 161 => 0xb09895e
  | 162 => 0xb4cd1
  | 163 => 0xb8d11
  | 164 => 0x20d51
  | 165 => 0xd5411
  | 166 => 0x140d51
  | 167 => 0xb4d51
  | 168 => 0x144d51
  | 169 => 0xb8d51
  | 170 => 0x148d51
  | 171 => 0x1a0b51
  | 172 => 0x144b51
  | 173 => 0x1a1451
  | 174 => 0x1a0b91
  | 175 => 0x148b91
  | 176 => 0x1a1491
  | 177 => 0xd4211
  | 178 => 0x150b16
  | 179 => 0xd4cc9da
  | 180 => 0x9d296
  | 181 => 0x1a0d
  | 182 => 0xd4d0a1a
  | 183 => 0xa1296
  | 184 => 0x8d52
  | 185 => 0x154996
  | 186 => 0xd4ccb59
  | 187 => 0xb5416
  | 188 => 0xd4d0b99
  | 189 => 0xb9416
  | 190 => 0xe8d0cde
  | 191 => 0xe8ccd1e
  | 192 => 0xccd55
  | 193 => 0x160d54
  | 194 => 0x15cd55
  | 195 => 0xd0d54
  | 196 => 0x151296
  | 197 => 0x155416
  | 198 => 0xe9716
  | 199 => 0xe9896
  | 200 => 0x1a0d54
  | 201 => 0x1715d6
  | 202 => 0x1a0d55
  | 203 => 0x189616
  | 204 => 0x74a14
  | 205 => 0x75814
  | 206 => 0x74b94
  | 207 => 0x75854
  | 208 => 0x74414
  | 209 => 0x5cd
  | 210 => 0x5d5d5
  | 211 => 0x75614
  | 212 => 0xb4d4cd9
  | 213 => 0xb8d4d19
  | 214 => 0x58e96
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1426
  | 6 => 3727
  | 5 => 1513
  | 4 => 267
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
  | 5 => packedAt gbK5 (95315+((h/504+packedAt gbK5 (89267+(h % 504)*12) 12) % 3213)*12) 12
  | 4 => packedAt gbK4 (19491+((h/89+packedAt gbK4 (18690+(h % 89)*9) 9) % 388)*10) 10
  | 3 => packedAt gbK3 (5662+((h/22+packedAt gbK3 (5508+(h % 22)*7) 7) % 90)*8) 8
  | 2 => packedAt gbK2 (744+((h/2+packedAt gbK2 (736+(h % 2)*4) 4) % 14)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x38f1c0e3f31e3831c3e387e0fff1830f3134cf
  | 1 => 0xc0fe00fc7c1fc03e03fc07ff07f60c33c238f3
  | 2 => 0xff0000ff8fe0003ffc7ff8fff808103c03cf3c
  | 3 => 0xffffff000fffffc0007fff0000001fc0fc0fc0
  | 4 => 0xfffffffff800000000fe000fff000
  | 5 => 0xfffffffff000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x18504a20930a0a9048a0912072a18305311445
  | 1 => 0xc0a214442c1445221144224e05460c12c22892
  | 2 => 0x2100208900200004a009409080081028004128
  | 3 => 0x4a348600054691800072340210600540540ec0
  | 4 => 0xa9926391a0000042182a000abb000
  | 5 => 0xb4c938f24000000020004018c60d5abf000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xffffffe8fff8f8e8ffffffe8fff8f8e8ffffffe8fff8f8e8ffffffe8fff8f8e8ffffffe8fff8f8e8ffffffe8fff8f8e8ffffffe8fff8f8e8ffffffe8fff8f8e8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15050
namespace PEqualNP.Outside.L_meta_15050
open PEqualNP.Outside.L_meta_15050.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 9 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 50 := (concat bs0_3_0 bs0_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_128 : Interval s0Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 136 := (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 48 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_2_0 : Interval s1Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 9 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 50 := (concat bs1_3_0 bs1_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_128 : Interval s1Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 136 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := (concat bs1_5_0 bs1_5_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 5 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 91 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 5 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 91 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 8 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 102 := (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 bs5_3_96))
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
theorem bs5_4_128 : Interval s5Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_160 : Interval s5Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_224 : Interval s5Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_256 : Interval s5Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_320 : Interval s5Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_352 : Interval s5Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_416 : Interval s5Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_448 : Interval s5Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_512 : Interval s5Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_544 : Interval s5Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_608 : Interval s5Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_640 : Interval s5Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_704 : Interval s5Atlas 4 704 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 725 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 (concat bs5_4_192 bs5_4_224)) (concat bs5_4_256 (concat bs5_4_288 bs5_4_320)))) (concat (concat (concat bs5_4_352 (concat bs5_4_384 bs5_4_416)) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512))) (concat (concat bs5_4_544 (concat bs5_4_576 bs5_4_608)) (concat bs5_4_640 (concat bs5_4_672 bs5_4_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_64 : Interval s5Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_128 : Interval s5Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_160 : Interval s5Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_224 : Interval s5Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_256 : Interval s5Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_320 : Interval s5Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_352 : Interval s5Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_416 : Interval s5Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_448 : Interval s5Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_512 : Interval s5Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_544 : Interval s5Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_608 : Interval s5Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_640 : Interval s5Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 682 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 (concat bs5_5_192 bs5_5_224)) (concat bs5_5_256 (concat bs5_5_288 bs5_5_320)))) (concat (concat (concat bs5_5_352 bs5_5_384) (concat bs5_5_416 (concat bs5_5_448 bs5_5_480))) (concat (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)) (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := (concat bs5_6_0 bs5_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_7_0 : Interval s5Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_7 : Interval s5Atlas 7 0 1 := bs5_7_0
theorem alls5 : ∀ k ≤ 7, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
  · exact alls5_7 i (by omega) hi
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
theorem bgb_4_256 : Interval gbAtlas 4 256 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 267 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256))))
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
theorem bgb_5_1504 : Interval gbAtlas 5 1504 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1513 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero,inputs.getD 4 zero,inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffeefffeffeeffffffeafffafaeaffffffeefffeffeeffffffe8fff8f8e8ffffffeefffeffeeffffffeafffafaeaffffffeefffeffeeffffffe8fff8f8e8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_15050.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.and,[8,7]⟩,⟨.or,[1,4]⟩,⟨.and,[10,6]⟩,⟨.or,[0,2]⟩,⟨.or,[5,6]⟩,⟨.or,[13,7]⟩,⟨.and,[12,14]⟩,⟨.or,[0,1]⟩,⟨.and,[16,4]⟩,⟨.or,[9,11]⟩,⟨.or,[18,15]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_15050

open PEqualNP.Outside.L_meta_15050 in
theorem PEqualNP.Outside.L_meta_15050 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
