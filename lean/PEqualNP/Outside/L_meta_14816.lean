import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_14816.Model
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


end PEqualNP.Outside.L_meta_14816.Model

namespace PEqualNP.Outside.L_meta_14816
open PEqualNP.Outside.L_meta_14816.Model
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

def SB : Nat := 5

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

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

end PEqualNP.Outside.L_meta_14816

namespace PEqualNP.Outside.L_meta_14816
open PEqualNP.Outside.L_meta_14816.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x9d43
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | 3 => packedAt s0K3 (i*16) 16
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s0K3 (17+((h/1+packedAt s0K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffc1f87fe0ffff0ff070ff8387fc1fff71c39f
  | 2 => 0x7ffff83fff83ff07fff07fff83ffc0f9e7cf3
  | 3 => 0xf801fffc00ffc3ff807ff803ffc01ff0e78f1c
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x2112891109522102b4204c910264854c30c185
  | 2 => 0x10801008400040100091010888084822021432
  | 3 => 0x52a52228d2a40675085a902ad48152a2c70e18
  | 4 => 0xe539c5429836aba9dd08c443673380c4f80bc0
  | 5 => 0x863186731cc733ce6e6ce67046220308fde000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcf0fcf0fcf0ccc0fcf0fcf0fcf0ccc0fcf0fcf0fcf0ccc0fcf0fcf0fcf0ccc0fcf0fcf0fcf0ccc0fcf0fcf0fcf0ccc0fcf0fcf0fcf0ccc0fcf0fcf0fcf0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_14816
namespace PEqualNP.Outside.L_meta_14816
open PEqualNP.Outside.L_meta_14816.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf87f87c7fe1fffe1f87f0fe0c3f87fff59c27f
  | 2 => 0xff87fff83fe1e1fe1f87f0fffc3f8707a67d93
  | 3 => 0xfff807ffc001fe3fe007ff00ffc007f8c78e1c
  | 4 => 0x7fffffe003ffff80000fffff800f80fe0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xa00084110208000480a01240048214408c025
  | 2 => 0x10110080840202020081104244110212021492
  | 3 => 0xa13355128d55506ea445aa0aea8314b2c70e18
  | 4 => 0x85646624291054b535508810b3265020f00b40
  | 5 => 0xc646443731999939de66cc9c220460c4fde000
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfafafaf0fafaaaa0fafafaf0fafaaaa0fafafaf0fafaaaa0fafafaf0fafaaaa0fafafaf0fafaaaa0fafafaf0fafaaaa0fafafaf0fafaaaa0fafafaf0fafaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_14816
namespace PEqualNP.Outside.L_meta_14816
open PEqualNP.Outside.L_meta_14816.Model
def s2K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x802902001802f995d32be6374c6f185c30
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x60a00009541cca350b318d420c2550430
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*4) 4
  | 3 => packedAt s2K3 (i*15) 15
  | 2 => packedAt s2K2 (i*26) 26
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (5+((h/1+packedAt s2K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s2K3 (98+((h/2+packedAt s2K3 (90+(h % 2)*4) 4) % 12)*4) 4
  | 2 => packedAt s2K2 (107+((h/1+packedAt s2K2 (104+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 27 s2Pos s2Neg, 0xeeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88eeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_14816
namespace PEqualNP.Outside.L_meta_14816
open PEqualNP.Outside.L_meta_14816.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xd531
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | 3 => packedAt s3K3 (i*16) 16
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s3K3 (17+((h/1+packedAt s3K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffc387f8f0fff0ff187fe1c3e1c7ff1f9d31cf
  | 1 => 0xc7fc07ff00f0ff1fe0787e03fe0787e7d23933
  | 2 => 0x7fff8ffff00ffe1ff807ffc3ff807f863ce3c
  | 4 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 5 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x40500808412041000810a0484040a112051045
  | 1 => 0xb48952922a49a831642c5212b21512c5522912
  | 2 => 0x1000020000200020080048004800400004228
  | 4 => 0x142a66c4a8882a55b54d102239365041780d80
  | 5 => 0x26334486cceccc99de76793b102460967fb000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xfafaf8f8fafae8e8fafaf8f8fafae8e8fafaf8f8fafae8e8fafaf8f8fafae8e8fafaf8f8fafae8e8fafaf8f8fafae8e8fafaf8f8fafae8e8fafaf8f8fafae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_14816
namespace PEqualNP.Outside.L_meta_14816
open PEqualNP.Outside.L_meta_14816.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*1) 1
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
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xfef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_14816
namespace PEqualNP.Outside.L_meta_14816
open PEqualNP.Outside.L_meta_14816.Model
def s5K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (6+((h/1+packedAt s5K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf3cfe3c7fc7e3f1f8c63c70fe3f0fc78474cf
  | 1 => 0xf03f1fc063f9fc7e3f07c780e3c7f1f99a4b33
  | 2 => 0xffc01fff83fe007fc7f807ff03f801fe638c3c
  | 3 => 0xffffe00003ffff8007fff80003fffe007c0fc0
  | 4 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1040200804004020000081020090040001045
  | 1 => 0x10888411049080c042024484484240a10a4112
  | 2 => 0x22024888090049200948012202902514208c28
  | 3 => 0x441241aa5225402495d4900a1324ac14740e80
  | 4 => 0x88a091304035924926a7264c9800c8215f6000
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xfefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_14816
namespace PEqualNP.Outside.L_meta_14816
open PEqualNP.Outside.L_meta_14816.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x8605030001a188e52007a0a004a00000000004c020048821e6e0c007078427e00140086000054468800000074662e5800280000000076343c002a1c325e042200008a6c004024008038000000000012000000720000005a640000440068003a106a004e7c560e160600366200002c008426005c000000000000203e8c020400100040010010002000820300101000604000007fd50017f54007f95001fd54005f55001fc54007fd4c01fe53007f54c01fc53007fd0c01fe43007f50c01fc43007fd4801fe52005f94801fd52007f148017c52007fd0801fe42007f50801fc42007fcc801df32007f8c801fd3200774c801fc32007fd44017f51007f94401fd51005f54401fc51007fd0401bf41007f90401fd41006f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd40017f50007f94001fd50005f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x204005bf990200177cc810002be64080017eb204002ef590200057ac81000afc6408001bfaa04000df55020015fec610012fe6308005ef3184000b798c20005fac61000bdd63080016eb184002bf18c2001dfcc41000f7e5208007be2904003f7cc82001fba6410006fe6108005fb3084000bd98420005fac21000bf561080017ab084000dfd4420006faa210003bf4108001dea084002bf98020016fea01000b7d5008005f79004002fe88020017da401000ff920080037fb2e2006bf9971000efccb880027e65c40017eb2e2001df59710004facb88006fc65c40037fb262005bf9931000f7cc988002be64c40017eb262001ef593100057ac988006fc64c4001bfaa62000df5531000dfec788012fe63c40017eb1e2001bf18f1000dfec58800efe62c40017eb162001bf18b10006fca5880037c52c4001ef9962000f74cb1000efea3880077d51c4003dfa0e2001fd9071000f7a8388003f541c4001daa0e2001fd8c710007ea6388007f621c4001fa90e2000dfd4310006faa18800aff658400d7f32c2002df99610004fccb08002fd6584005beb2c20009f59610015f8cb0800aff648400b7f3242000bf59210015f8c9080037f5484001beaa42002bfd8e10025fcc708002fd63840057e31c2002bfd8a1001dfcc508002fd62840057e3142000df94a10006f8a508003df3284001ee9942000bf58610006fea3080037d5184001dfa0c2000ef50610015fcc10800b7f5084005bea842002fe8c210007f2610800bfa2084001fc9042002fdc421000ff62108002ff654400d7f32a2000df99510004fcca88002fd6544001beb2a20009f59510035f8ca88002ff644400b7f3222000bf5911002df8c8880037f5444001beaa22000bfd8d10007bec688002df63440097f31a2000bf58d10025f8c688003dc63440016e31a2000bfd891001dfcc488002fd62440077e3122000df94910006f8a488003df3244001ee9922000dfd4510006faa288003bf4144001fb20a2000ef50510007ea8288003b54144001fb18a2000fd4c510007ec4288003f52144001bfa822000df54110007f46088003f93044001fd1022000fe4811000ff6208800bf610440057fb282006bf99410016fcca080027e65040017eb282002df59410004faca0800afc65040057fb202005bf990100177cc808002be64040017eb202002ef590100057ac80800afc6404001bfaa02000df55010015fec608012fe6304005ef3182000b798c10005fac60800bdd63040016eb182002bf18c10015fec40800efe6204005f73102000bb98810005fac40800bed620400176b102002bf18810006fca4080037c5204001ef9902000f74c81000dfcc2080077f5104003bea882001efd041000f7a820800afe6004005bfa802002df54010017ee200800bfa1004005fa8802001fe44010
  | 1 => 0x3de318c001ee18c6002bf98230016fea11800b7d508c005ef9846004fecc230005feca9801afe654c0017eb2a6006bf19530005fec898016fe644c0017eb226005bf19130006fea8980037d544c001ef21a6000f750d30005fec49800efc624c001bf2926000df14930007be6498003dd324c0017fb0a6001bf18530006fea2980037d514c001dfa0a6000ef50530007be6298003dd314c001bfa826000df54130027f6609800bde304c0057fb286006bf99430016fcca180027e650c0017eb286002df59430004faca1800afc650c0057fb206005bf990300177cc818002be640c0017eb206002ef590300057ac81800afc640c001bfaa06000df55030025fcc61800efe620c005f73106000bb98830005fac41800bed620c00176b106000df94830006f8a418013df320c001ee9906001bf98430017ecc218002f6610c0017eb086002fd58430005eac2180037f510c001bea886000efd04300077a8218003de310c009ee1886002bf98030016fea01800b7d500c005ef9806002fe8c030017ba6018013f9300c0077fb2e4003dfd972001cfecb9001afe65c80017eb2e4003bf1972001ef8cb9000e7c65c80077fb264005bf99320005fac99000efc64c8001bfaa64000df5532001dfec790012fe63c8007ef31e4000b798f20005fac79000fdd63c80016eb1e4003bf18f2001efca59000f7c52c8007f72164000fb50b2001fbe659000fee32c8007ee9964000fb4cb200079a6590006fe61c80017eb0e4000dfd4720006faa390003bf41c8001dea0e4003fbc8720007da43900037f50c8001bea864002bfd9620035fccb1000b7e65880013f32c4000bf59620016facb100027d65880057e32c4002bfd922002dfcc910002fd64880057e3244000dfd5220006faa91000aff63880097f31c4000bf58e20015f8c710002fd6288007bf2944003df14a20007be6510003dd32880037f30c4000bf58620006fea3100037d5188001dfa0c4000ef50620015fcc11000b7f5088005fd2844002df54220007f2a110003795088005fd2044000fe50220017de411000ffb20880017fb2a4000dfd9520004feca9001afe65480017eb2a4006bf19520006f8ca900027c65480017fb224000efd91200057ec890016fe64480017eb224005bf1912000778c890002bc6448001bfaa24000df55120005fec690012fe63480017eb1a4004bf18d2001efca49000f7c5248001f72124000fb50920007be6490003ee3248001ee9924000fb4c9200079a6490002ff61480037e30a4000dfd4520006faa290003bf4148001dea0a4000fbc8520007da42900037f5048001fd2824000df54120007f2a090003795048001fd2024000fe5012001ff6409000bee20480057fb284006bf99420016fcca100027e65080017eb284002df59420004faca1000afc65080057fb
  | 2 => 0x50006faa828012fe63140017eb18a003bf98850005fac4280037e521400dbe290a000f7cc850007ba6428006fe61140017eb08a006dfd4450006faa228003bf4114001dea08a002bf98050016fea02800bfa5014005bea80a006fe5405002dfecba001afe65d000bbf32e80009f99740005facba00177d65d00013eb2e8005bf1974002efea9a00177d54d00097f31e8000bf58f4002f7e87a0003bd43d00077f3168000bf58b40006fca5a00037c52d000bdfa168000ef50b40007be65a0003dd32d00037f30e8000bf58740006fea3a00037d51d000bdfa0e8000ef50740006fea1a00037d50d00057fb2c8006bf99640016fccb200027e65900017eb2c8002df59640004facb2000afc65900017eb248000dfd52400077ca9200037d5490001deaa48000cf55240025fcc720002fd63900077f3148000bf58a40006fca5200037c5290001df2148000ef10a40007be6520003dd32900037f30c8000bf58640006fea3200037d5190001dfa0c8000ef50640015fcc12000b7f5090005bea848002efd024002ff68120002ff655000d7f32a8000df99540004fccaa0002fd6550001beb2a80009f59540035f8caa00037f5450001beaa28000bfd8d40025f8c6a0003bf4350001dea1a8000bfd894001df8c4a00037e5250001be2928000efd09400077a84a0003df3250001ee9928000bfd854000df8c2a00037f5150001bea8a8000efd05400077a82a00037f5050001bea828005fed01400177c80a000aff651000d7f3288002df99440004fcca20002fd6510005beb2880009f59440015f8ca20016fe641000bbfaa08005ef9504002efaa820003bd54100019eaa08004bf98c40017bcc620002de63100017eb188002f758c40005bac62000efe6210005f73108000bb98840005fac42000bed621000176b108000df94840006f8a420003be421000bde2108000f7cc840007ba6420006fe6110005fb3088000bd98440005fac22000bf561100017ab088000dfd4440006faa220017bf4110001dea088002bf98040016fea02000b7d5010005dfa008002fe900400177a8020017f940100097fb2e6006bf99730005facb98012fc65cc0097fb266005bf99330005fac998012fc64cc001bfaa66000df55330027bc8798003dd43cc0077f3166000bf58b30006fca5980037c52cc009ef9966000f74cb3000dfcc398002fd61cc001bfa8e6000df547300077e8398003bd41cc009ef98e6000f74c730006fea1980037d50cc0057fb2c6006bf99630016fccb180027e658c0017eb2c6002df59630004facb1800afc658c0057fb246005bf99230005fac91800afc648c001bfaa46000df55230005fac71800efe628c0017eb146000df94a30006f8a518003df328c001ee9946001bf98630005fac3180037f518c001bea8c6000efd06300077a831800
  | 3 => 0xeb204200af5902100df8c8108037f5408401beaa04201bfd8c21025fcc610807de63084016f3184200bf58c2100fbac610802dd63084037e3184203bf9882101efca41080f7c5208407ef9904203f74c82100dfcc2108077f5108403bea884201efd042100f7a8210807ef2108403fb1084201fb4842101fea421080afe6008403fd3004200be98021005fac010807f960084017cb004205bf993500377cc9a8002be64d40017eb26a006ef593500057ac9a801b7f54d4001bf2a6a000df55350036f8a9a8012fe63d40017eb1ea006dfd4f50006fca7a80037d53d400dbe29ea003bf98b50005fac5a801b7f52d4001bf296a000df54b50036f8a5a8003df32d4001ee996a001bf98750005fac3a801b7f51d4001bf28ea000df54750036f8a3a8003bf41d4001dea0ea006dfd9350006fcc9a80033e64d4001beb26a0009f593500067ac9a80023d64d400dbe326a006dfd8f50006fcc7a80037d63d400dbe31ea000dfd0f50006fc87a80037d43d4001be21ea006dfd8b50006fcc5a800e7e62d4001beb16a006df18b50006fe85a80037e42d4001bea16a000df10b50006fe65a80035f32d4001bf196a000df4cb50006ba65a80037c32d400dbfb0ea000df98750006fac3a80027d61d400dbe30ea000dfd07500067e83a80037e41d4001bea0ea000cf50750006f883a80037f31d4001bf18ea000df4c750006f863a80037f21d4001bf10ea000df48750006f843a8002fd65940013eb2ca005bf99250005fac9280037f5494001beaa4a004bf98e50005fac72800efe62940017eb14a000df94a50006f8a528003df3294001ee994a001bf98650005fac3280037f5194001bea8ca000efd06500077a832800afe6094005bfa84a006fed4250005fec8a8016fc6454001bfaa2a000df95150006faa8a80037c54540017fb1aa004bf18d50006fea6a80037e5354001bea9aa000df14d50005fec4a800efc6254001bfa92a000df94950006faa4a80037c5254001ef992a000f74c950005fec2a8006fc6154001bfa8aa000df94550006faa2a80037c5154001dfa0aa000ef50550037f6a0a800b7e5054001bfb22a0009fd9150006fcc8a80037d6454001be322a000dfd8d50006fcc6a80037d6354001be31aa000dfd0d50006fc86a80037d4354001be21aa000dfd8950006fcc4a80037d6254001be312a0039f18950006fe84a80037e4254001bea12a000df10950006fe64a80035f3254001bf192a000df4c950006ba64a80037c3254001bfb0aa0009fd8550006fcc2a80037d6154001be30aa000dfd05500067e82a80037e4154001bea0aa000cf50550006f882a80037f3154001bf18aa000df4c550006f862a80037f2154001bf10aa000df48550006f842a80037f6054001bdb02a006bf99450004fcca28016fe64140017eb20a006dfd50
  | 4 => 0x8037d548c4017eb1c6200f790e31007ba871880efe628c4017eb146200df94a31006f8a518803df328c401ee9946201bf9863100efea3188077d518c403dfa0c6201ef5063100fbe6318813f7318c4057f3046200bf58231005feca9881afe654c4017eb2a6206bf19531005fec898816fe644c4017eb226205bf19131006fea8988037d544c4017fb126203bf18931006fca4988037c524c401ef9926200f74c931006fea2988037d514c401dfa0a6200ef50531027ee6298807de314c4017fb026202bf1813100dfeca1881afe650c403bf32862009f99431005faca188077d650c4013eb286201bf1943100dfec818816fe640c403df3206200af99031005fac818807bd640c4015eb206201bf19031006fea8188037d540c4097f3186204f790c31007ba861880efe620c403f73106200bb98831005fac418807ed620c40176b106200df94831006f8a418813df320c401ee9906201bf9843100efea2188077d510c403dfa086201fd9043100f7a8218803f5410c401daa086201f7cc43100fec6218807dd310c409fa9886202bf9803100ff4c018802fa600c4017eb006201fe58031005f2c01880eff65c8407bfb2e42039fd9721035fccb90802fd65c84077e32e4203df1972101cf8cb9080eff64c840b7f3264200bf5932101df8c9908037f54c8401beaa64203bfd8f21025fcc79080fde63c84016f31e4200bf58f2101fbac790802dd63c84077e31e4203df94b2101ef8a59080fdf32c8407f71964203f74cb21007da6590803cd32c8401bfa8e4200df547210077e8390803bd41c84057f3064200bf5832100dfecb1081afe6588403bf32c42009f99621005facb108077d65884013eb2c4201bf1962100dfec910816fe6488403df3244200af99221005fac910807bd64884015eb244201bf19221006fea9108037d54884037fb1c4204bf98e21005fac710806fc63884017eb144203df94a2101ef8a510803df3288401ee9944201bf9862100efea310807f65188403bea8c4200fd54621006eaa310807bf4188403fb20c4201ef50621007ea8310803b54188403f790c4203fdc8621015fcc110802fd60884017fb2a4200dfd9521004feca9081afe65484017eb2a4206bf19521006f8ca908027c65484017fb224205bf99121005fac890816fc6448401bfaa24200df55121005fec690812fe63484017eb1a4204bf18d2101efca49080f7c5248401ef9924200fb8c921007ba6490803ed3248401e69924200dfd4521007eca2908037d5148401faa8a4200dd545210077e8290803f64148401dea0a4200fd505210076a829080ff72148403f710a4200bfd8121015f8c090806ff650840d7f3284201df99421004fcca10802fd6508403beb2842009f5942100df8ca10806ff640840b7f3204201ef990210057cc810802fd6408403d
  | 5 => 0x8341005fac1a0817bf65d0401df32e8200cf997410077acba08033d65d040bde32e8205efd8f410077cc7a08039e63d0401deb1e8200e758f4102f78c7a0803bf53d0401df29e8200ef54f4100778a7a0817bf62d0401df3168200ef58b4102f78c5a0803bf52d0401df2968200cf94b410077aa5a0803bc52d04019e2968200efccb410073e65a0803be32d0401de9968200e74cb410077865a0803bf51d04019fa8e8201ef947410077aa3a08033d51d0403de28e8205efd83410077cc1a0803bd60d040bde3068201bfd9641035fccb208077e65904013f32c8200bf5964100efacb208027d65904037e32c8200bf592410057ac9208037f5490401beaa48204bf98e41005fac72080efe62904017eb148200df94a41006f8a520803df3290401ee9948201bf9864100efea3208077d5190403dfa0c8205fdd0641015fcc120802fd60904017fb2a8206bf99541006fccaa08027e65504017eb2a8200df59541004facaa081afc6550401bfaa28200efd51410067ea8a0803be5450401beaa28200ef551410067aa8a0803bc54504017fb1a8204bf18d410077e86a0803be4350401dea1a8200ef10d41005fec4a080efc6250401bf2928200df149410077e84a0803be4250401dea128200ef10941007be64a0803dd3250401bfa8a8200df5454102fee82a0807be41504017fb028202bf181410077ecaa0803be65504019f32a8200ef595410067acaa0803bc6550401dfb1a8200ef98d410077ac6a0803bc6350401dfa9a8200ef94d410077aa6a0803bc5350401dfb128200ef989410077ac4a0803bc6250401dfa928200ef949410067ca4a0803bd5250401de2928200cf149410077e64a08039f3250401df1928200ef4c9410073a64a0803bc3250401dfb0a8200edd85410077ea2a08033f5150403df28a8200ef545410067aa2a0807bc5150401dfb028200ef981410077ac0a0803bc60504037fb288206bf9944100efcca208027e65104017eb288201df59441004faca20806fc651040b7f3208200af9904102efea8208177d54104097f3188200bf58c4101dfcc420802fd6210401bf2908200df14841007be6420803dd32104037f3088201dfd444100efaa220807bf4110403fb2088201ef5044102fea822080afe60104017eb008204bfd9731035fccb98802fd65cc4097e32e6204bfd933102dfcc998802fd64cc4097e3266200dfd5331006faa99880efe62cc4017eb166200df94b31006f8a598813df32cc401ee9966200dfd4731006faa398803bf41cc401fb20e6200ef50731007ea8398803b541cc4057f3066200bf5833100dfecb1881afe658c403bf32c62009f99631005facb188077d658c4013eb2c6201bf1963100dfec918816fe648c403df3246200af99231005fac918807bd648c4015eb246201bf19231006fea918
  | 6 => 0x17eb286403bf1943201dfec819016fe640c8017eb206403bf19032006fea8190037d540c8097f3186400b798c3201dfcc41900f7e520c807be2906403f7cc83201fdc641900fdd320c809f69906401bf98432005fac21900afe600c8017eb006405bf99351005fac9a881b7f54d4401bf2a6a200df55351036f8a9a8812fe63d44017eb1ea206dfd4f51006fca7a88037d53d440dbe29ea203bf98b51005fac5a881b7f52d4401bf296a200df54b51036f8a5a8803df32d4401ee996a202bf98351005fac1a881b7f64d4401bf326a200df59351004fac9a881b7c64d440dbfb1ea200df98f51006fac7a881b7c63d4401bfa1ea200df90f51006fa87a88037c43d440dbfb16a200df98b5101cfcc5a88037d62d440dbe316a200dfd0b51006fc85a88037d42d4401be216a200dfccb51006be65a88037e32d4401be996a200d74cb51006f865a881b7f60d4401bf306a200df58351004fac1a881b7c60d44017eb2ca2009f5965102dfcc928807be64944015f324a200bf5925100f7ac928802bd6494401bfaa4a200df55251025fcc728802fd63944077f314a200bf58a51006fca5288037c5294401ef994a200f74ca5100dfcc3288077f519440dfba8ca202bf98251005fac128802ff645440b7e322a200dfd5151006fca8a88037d5454401be2a2a200bfd8d51025f8c6a88037f5354401bf29aa200df54d51006f8a6a8802ff62544077e312a200dfd4951006fca4a88037d5254401be292a200f7cc951007ba64a881bf75154403bf28aa200bfd8151015f8c0a88037f64544013fb22a200df99151006fac8a88037c6454401bfb1aa200df98d51006fac6a88037c6354401bfa1aa200df90d51006fa86a88037c4354401bfb12a200df98951006fac4a88037c62544073e312a200dfd0951006fc84a88037d4254401be212a200dfcc951006be64a88037e3254401be992a200d74c951006f864a88037f6154401bbb0aa200dfd8151004fec0a88037e6054401beb02a200df18151035fcca288027e651440b7f320a201ef990510057cc828802fd6414403deb20a200af59051036fea8288037d54144097f318a200bf58c5101dfcc428802fd6214401bf290a206df14851007be6428803dd32144037f308a201dfd445100feca2288077d511440dfaa88a202bf98051005fac028816ff65d040d7f32e8205df99741004fccba0802fd65d040bbeb2e82009f5974102df8cba08177f54d0401dfaa68200cfd534102f7ca9a08177d54d0401deaa68200cf5534102f78a9a0812fe63d040bef31e8200b798f41005fac7a0817dd63d04016eb1e8205efd0f410077c87a0803bd43d040bde21e8203bf98b41005fac5a08037e52d0401be2968205efd0b410077c85a0803bd42d040bde2168200f7ccb41007ba65a08037f51d0401bea8e8202bf9
  | 7 => 0x21002fd61908057f3048400bf58242005fecaa10037f65508013fb2a8406bf99542005facaa101afc6550801be32a84009f19542006fea8a1003be5450801beaa28400ef551420067aa8a1002ff63508097e31a8403df9494201ef8a4a1017ef4250807df2128400bfd854200df8c2a1002ff60508057e3028403bfd9442035fcca2100f7e65108013f3288400bf5944201efaca210027d65108077e3288405bf9904202efea8210177d54108097f3188403f798c42005bcc621002fd6310807eeb188400b758c4202f7e8621003bd43108077f3108403df9484201ef8a42100fbf4210807f72108403ef5084202fda8421006fe6110807fb3088400bd98442005fac22100ff561108017ab088402bf9804201ff4c021002fa60108017eb008403fe58042005f2c021012ff65cc80d7f32e6404df99732004fccb99002fd65cc809beb2e64009f59732025f8cb99012ff64cc80b7f3266404ef993320057cc999002fd64cc809deb266400af59332025f8c9990037f54cc801beaa66400f7d4f32027bca799003dd53cc809ee29e6400f7d0f32027bc8799003dd43cc809ee21e6403df94b3201ef8a599006fe61cc8017eb0e6402bf98332005fac199013df65cc801ef32e6400d799732007bacb990035d65cc809ee32e6404f7d9332007bcc9990039e64cc801eeb266400e759332027b8c999003df54cc801afaa66400f795332007baa9990035d54cc801ee2a66400f7d4b3201fbca59900f5e52cc801eea966403f714b3201eb8a599003df42cc807ef2166400f750b3201fb88599013df61cc801ef30e6400f758732027b8c399013df60cc801ef3066400f758332027b8c19900eff658c80d7f32c6400bf5963201df8cb1900eff648c80b7f3246400bf5923201df8c9190037f548c801beaa46400bf58e32005bac71900efe628c807bf2946403df14a3201fbe6519013ef328c8037f30c6400bf58632015fcc119002fd608c8017fb2a6400dfd9532004feca9901afe654c8017eb2a6406bf19532006f8ca990027c654c8017fb226405bf99132005fac899016fc644c801bfaa26400df55132007bea699003de534c801eea9a6400f714d32007be8699003de434c801eea1a6400f710d3201efca49900f7c524c809f79926403f78c932005fec299006fc614c8017fb026402bf18132007beca990035f654c801ef32a6400f759532007b8ca990035c654c801efb226400f799132007bac899003dc644c801efaa26400d7d5132007bca899003dd544c801aeaa26400f715132007bec499003cf624c801efa926403f79493201ebca499003dd524c807ee2926403d714932007be849900fde424c801eea126403f710932007bec299003de614c801eeb0a6400f718532007bec099003de604c801eeb026400f71813201dfeca1901afe650c80
  | 8 => 0xf90d43005fec4a180efc6250c017fb0a8601bf18543005fec0a180afc6050c097fb288606bf99443026fcca218027e6510c017eb288604df59443004faca21812fc6510c0b7f3208605dfd504302efaa821812fe6310c09dfa188604f790c430277a8621817dd4310c077f3108600bf5884300dfcc221802fd6110c057f3008600bf5804302dfcc9a9002fd64d480dbfaa6a400df55352025fcc7a9002fd63d48037f30ea400bf58752015fcc1a9002fd60d48017eb2ca405bf99252005fac9290037f5494801bf2a4a400df55252006f8a929012fe6394807ef31ca400b798e52005fac72900fdd63948016eb1ca400dfd4e52006fca7290037d5394801be29ca403bf98a5201efea52901bef52948037f30ca400bf58652015fcc129002fd6094807bfb24a403df9925201efac9290027d6494807be324a403dfd8e5201efcc72900f5e6394807beb1ca403d758e5201ef8c7290037f4394801bf21ca400df50e52006f8872900e7e6294807bfb0ca403df9865201efac3290027d6194807be30ca403dfd825201efcc12900f7d60948013eb04a403df18252005fec8a9016fc6454801bfaa2a400df55152005fec6a9012fc635480df7a92a403df94952005fec2a9006fc61548017fb02a402bf18152035fcca29016fe6414807df320a400af99052005fac82900fbd64148015eb20a406dfd5052006fca8290037d541480dbe2a0a404bf98c5201fbcc629002de63148017eb18a403f758c52005bac62901b7f5314801bf298a400df54c52036f8a62900efe6214807bfa90a403fb9485201efaa42901bed52148037f308a403fd98452005ecc229002fd6114807fab08a400bd58452015fcc02900ffa60148017d300a400bf5805201ff2c029002f96014807bfb20a403df9905201e7cc82900f7d64148013eb20a403cf590520047ac82900f7c6414807bfb18a403df98c5201ebcc62900f7d6314807aeb18a403df18c52006fe86290037e4314801bea18a400df10c5201efcc42900e7e6214807b7310a403dfd845201efcc22900f766114807beb08a4009f5845201eeac229002756114807be308a403dfd805201efcc02900f7a6014807beb00a4009f5805201ef2c029002796014807be300a405bfd9742035fccba10177e65d08013f32e8400bf5974202efacba10027d65d080b7e32e8405dfd534202f7ca9a10177d54d0801deaa68400cf55342025fcc7a1002fd63d0807bf2968403df14b4200dfcc3a1002fd61d08057f3068400bf5834201dfecb2100f7f65908073fb2c8406bf99642005facb2100efc6590807be32c84039f19642005fac9210037f5490801beaa48404bf98e4201fbcc721002de63908017eb1c8403f758e42005bac721003bf4390801dea1c8403bf98a4201efca52100f7c5290807dfa148405fbd0a4200dfcc3
  | 9 => 0x601a00200600400000001a00001000400000200600401000200400000000800800001e00000600800000000400000000800801003400000000204001e00600000000a00a01600000200000600000400400600400601000000400200801000201200800401600000000600a00000800001200200800800400600000000200000000400600000004bf98f54005fac7aa00efe62d50017eb16a801bf98754005fac3aa00afe60d50017eb06a806dfd8f54006fcc7aa0037d63d500dbe31ea806dfd8b54006fcc5aa00e7e62d5001beb16a806df18b54036fec3aa0037e61d5001beb0ea8009f58754036f8c3aa01b7f60d5001bf306a800df58354004fac1aa01b7c60d50017eb2ca8009f5965402dfcc92a0177f549500ddfaa4a800cfd5254025fcc72a002fd63950077f314a800bf58a5400dfcc32a002fd61950057f304a800bf582540377ea8aa0177e54550017fb1aa804bf18d54005fec4aa00efc62550017fb0aa801bf18554005fec0aa00afc6055001bfb22a800cfd9154006fec6aa0037e6355001beb1aa800df18d54006fec4aa0037e6255001beb12a800df1895401cf8c4aa0037f61550013fb0aa800df98554006fac2aa0037c6155001bfb02a8009fd8154006fcc0aa0037d6055001be302a806bf99454004fcca2a016fe641500bbfaa0a805ef9505402efaa82a01bbd54150097f318a800bf58c5401dfcc42a002fd62150037f308a800bf58454015fcc02a002fd601500b7f326a600bf59353036fea9a98037d54d4c077f316a600bf58b5300dfcc3a9802fd61d4c057f306a600bf58353005facb29816fe6494c017eb24a600dfd5253006faa929812fe6394c09bfa9ca606f7d4e5301dfcc529802fd6294c037f30ca600bf58653015fcc129802fd6094c017fb22a605bf19153006fea8a98037d5454c0defa9aa604df94d53005fec4a980efc6254c017fb0aa601bf18553005fec0a980afc6054c0d7f328a605bf990530277cc829802be6414c017eb20a604ef590530057ac82981b7f5414c01beaa0a604bf98c53026fea629813de5314c09bea98a606f754c5301dfcc429802fd6214c037f308a600bf58453015fcc029802fd6014c0b7fb2e8606bf9974302efccba18027e65d0c017eb2e8605df59743004facba1816fc65d0c0bbfaa68605ef9534302efaa9a1803bd54d0c019eaa68603bf98b43005fac5a1806fe61d0c0bfb30e8600bd98743005fac3a1817f561d0c017ab0e8602bf98343005fac1a1812ff6590c0d7f32c8600bf59643025f8cb21802fd6490c01bfaa48600df55243025fcc721813bf4390c0befa1c8603bf98a43005fac521806fe6190c017eb0c8602bf98243005fac121802ff6550c0d7f32a8600bf59543035f8caa18037f5450c01df2a28600df551430077aa8a18033d5450c0befa1a8604e
  | 10 => 0x1bc8000000000000000051877a0000000f787bf000038cb1c00005597cc8ea0002838e7800075300000002ba11300010a02c82a1047866400001001200e00a00400200c00000002000000600000a00000c00600000400400201200000001000200201a00000000000000c00000800e00000600201601600000001000600800200401200200601601200200000000002000000800000c00200200200c00402800c00800000000800000000000000001602a00400000200c00000000802000401001200400a01600200800601200402203600600200000800a01e00200400200200200000000200a00000a00600a00a00000200600a00200a00000600000200000e00200200a00600001400200802c00600000000000000800000200200e00200600c00000c00400200200000400000a01200000e00600000800e00c00600000200800000001000000000000800200001000000600201200c00c00200001a01600400000c01800400000000400800400600a01e00c00200000200000001000000000000400000600000000000800c00001400000400000e00000600c00000c00401e00000c00e00200400000000800e00200000000c00201400000200001800000001200200000000c00400000400201800800200400200a03001000200e00a00000800002400e00400000400800800000000c00a02200000000200202e00600400400400000000000000400000000000600600e00200200400201a00600400200603200600000800000a00200001400e00400000000400000000e00200600000600000a00001200001c00400200000402401800200a00200001001800200601e00400e00000000600200600200000000600c00600000000000000a00000400000601200000400c00000201200800400400800401a00800000000400200000600200200801000000000200000000200200000600000000600001c00000c00000000200000000602e00000200200800200200400003400200e00000200600a00000200200400601800600e00400000000200000000e00600000200200200a00000401c00000001800200a00200200000a00e00600200e01e00200200200600000000200400200000200600400400000000000001003400800000000000c00000200400000a01600000200600000c00000000200200000c00e00800200200000000600000000001200200201800401000000000600000000000200c00000600800002600800000000200000601200000000200000202e00000000600400200600000001400a00000200200000200200000000000000400601200600600e00400600000000c00000000000c00000c00002000600000c00400200c00400601000800000801a00200200800a01e00000000a00400200a0000
  | 11 => 0x76c00011e032218430e05044983880001e583763f039b07e01e47272518fa42982cd0000000582000417000000045416e800062a60e367800000029200011d00001f44148b500000170001e6c0007c20000000aae2c911c1e80ee82573ed046c0002a5054000081600000000000000002ac000000000019f18b45f606b0000a2c8ee59d05e800051a07713e1fb44824c606e8834e8c6752d196d82f485418a0761010418000135d08421a1688c84b4a3de239a130a0262701791805046984098f00b064e01ab000077000026380000000001158000d5680900001d08800000d000000000000001ae40000f62fa9af400081a35f0c308ac4bb00000000002051820c640000000000000000000143000110048624500000002f5189a08012400000000000006e3000000000053539714440000000001900dd806e27180006560003fd12110fe7ea179211825a6ca00000009b83f823708c8dfc03f0000000000000000000000001a2f68c04bb400000021840ec6201c79a880006d129c127110e0000000c980000002ea00000000002c593400001f700008406c65e92f0053d0d41c43fb1418a2068f3c51db80002133e480001e000030a00000005a409900004525463258c4000000004f00000000000c38000b2e0000001434ea80003980000cb47160941ff04001d12479fd4c1e1432029ffc5fc84834686f48aa5fd3cd05b8ce665f3da95d85480ca19880000003f23a88230a884f44030000000000317000000000042f21280000000000000da600014a8000000000382108000077719b800015c77e000021c00000027e9e60f3c03900000004e00000eb0000b54000000000000000000002fc00000023d12a491c05c2770e243a600034518dc0002fd00000000002c8000153058029c0cb9e1cc826d5061856c0000000000000000090402882cb120003048000f900003279e84ab63ce2d40e9848a67c0dc000000044300002e4bdc7df000000000079c1b4000101a00029f8ea000072c00000f442a0000001d340007ca000000000046500000007b60002d9000000000043b21c03f278900003609aa000243a11483454830c8bd800044b0af8000ee60000248010dd2000000000000035200000000000000001a5494a00000000000000002d300000005ce0310f680007180001b381d243b28a10944cc7e93e9a16800000021d19dc00000011f000000000028b0f4053e4152ee205c13810e000000000060800000004c43cb04980002423b1000000100400015d0000f8a0000002060a3832302d8000a2646300000000f8000000148493c2230001ec032c00023880000000000200000cca0000e500006480000000568b30255000000000019200017e0dc400033f9d5400028f00000010b04af3fc8000cb26df383989072e0000b4a058e0c00028d8
  | 12 => 0x93800000000000007de4b61d08000000000436000000035c235800000000020e8fb000056035080003283f921b9f18e0224b02381308f80001bf800000000027e00000004b01900000d5800000000000000000000000cd60000c0981463a00c12000000004d2000017c00005100000004ac1e900016d4f206391c580000003ac0001830a24000000000000051d3c2845434c0bc00000284dc0000d602c8114779380203c9401780000000c08000402000000036400010d8a76000163125400000043d80000002b800009acc446cb30d0054000565072a07c0000003919d846c425c056000000066e000000070a36f0da000000000240800000000eb202173c9ce0002c20ad00005c31f587a0a7c16700000003f479d2b6000000000000000003ce00000001387a60003f297fc0002bb000000000000024d9daca6000023b0db4e36287010800086200000000006243771800acc96a8721a5800000038215712dc4b40000001a145f000024480000005a7000000000000013d863406a00017580001087db1dc838412a12c1b91d8c0007910000000ebc25403d80003c20001e5125c0001df2ca0000aba6db00008905467c03708ba8df43b73de902033610d00894240004592ff008052648300012e80842f10000000cd210f00013340000c438f055c0d40000001f3c00059f2b4171c00000013d0df800000012780003a05180000000000655000000000059e000040400000043c0dc40006341180f7400000013a07b0cc21a4000166c0000000000000b2000000000000000000001be4660000328000000000008403440000003b500010fc3800000cf400000d2851c083646172271ebc78622635a0ef82143ed00000010c400000003f80000000000b0c70684d1050000aa800038b800010663232618784de00008a05e40000000000000fe86073ea20048541b719d0d9427c4e435f83645fe289295191cd8a3dc3598000bd000032189780004da2ea800000067120085c86aa4580000000bf80000000f64f242a90000000b586351e10000be02b700000000000000001ba80000002df8dd805c2da361800073430e00000000005bc05d8000000000439829893a0003910000b5a3333b38fcca526063b0110423800000008f40000000000e8800000027b0db80a816d1940de078e5a015b07f897a0002aa81b02aa0753420b8800034e00011b40364512130000db025b000000000000000020e4eda4e600900007740000c29a8c00000027f000000046c30021f40a46bb1f5000000071a000000076800038698e800082f00c80003de461405a1d00003aa2bf0bf0a841830ce8ca400039b0000000dcc000000000039a00020e0d309d432207e8000d18227172827c5be80c3841388eba3cd000000000000000019b00000002f085a0986886000100004a
  | 13 => 0xe6254419ab485c000150000025621c0ba88ec03a0000000fec69030637b99bca104ca1111fa0e722a800004e40520000000ad4a9e344000188c84e000276090879e2532de8dd026e000000000046200032400007605ba08910589921dc000187507000042e00000000000000000ce4332000060024c4142e620c42bc000000000000000004a0000e825e7000070c78a0000a700000004a63d21e20fba7190000000c84000091800000000029280000000000000000d0200012507d801e00000000c4b966f41850a2858404100017bc38e00000c1e34f4a000000151c0006a800015d4c1400000011ec0007ee292058481427321f8ab00560c900000006ce85f0000000f2e4f30001384fb87c10331188a060000000f1000000034d038801200000000006d258234402a501412a3779cbc000000000000070e29604589a804609d3ae1ca40000133528cd41f079540e91082602be12f8000b1400040f0804cfa0cc00001b40002d21b098f02de4ae0c611fc2a66210608d6400000041200000000382f50000b607e01eb0000afe4dd25c80002304e50001f90a8a0f741b9a18bac1630001124d32693262000000085b1f1800033475a2d700d83e63c93941b3060400011a89f90240000bf02002a23bc000045800012f0001ad488e000387800000000011405340000001fa87b4ee4000000000077e611000038000067a3fc0000c207b101402bd0460000001a0c00000017d129006880700010f8b561b136a180869a4cb00000003781420000fb83960002871c148d07830001f40de00b81da800000000010f8dd40000ce0001ee00000000001ea4efe674000123400021b000049ccb80912c68a382060002dc800011a30b00000001b605d3178bb46ba57736220b4d90145000114c6921363c1000000000005f00001126971a28000c5600001f00009da000130196c0581af01d0000b8452f00000000000000000000e6845e36481780000000001d2400054015e0d04c260003db95340005b82561ea0d3c8032b721a0cb039600000000007b43b4000000000001210ac2f80000ff8000b24000328800034200018780007c00002241148e660000001f60f547940000000000000000114000000000017ac00000000a000067000010b0e3000043012212ccf9600000000000000000000000000000197800000059a0000000d4e171000000078c00033c0000a926912fc9fb05f20000cc20d47b0000000081ceec42f2d10398e5a25100016c400070b00021b800000026f20fc00045c00000000001e00000000a7244a00000005d80a1000000000005035204d06e60000a31c488e000000001e80003d200000008ba7860a003b02200000000fe83ba00035c00000000000001ed8e6a0002400bbc00026400000000000000000d181ac00004d0ff80006ae000
  | 14 => 0x1b31d6a174000692000069c87229b38a1a980000003be9a70acc45f01b8a046d60000000000a5079f109015441e00000014d00001f00001b00c581ad26a000096200023517780000000f70000000000000000000048800004f00002f700012840003f100013fc0001b50ab1c750da0600598a148880ef07d1d3c9a20992c400000000001730000fc20000002070ede2bf1179ee8e060000001a4000078b041000070240d2afa1dc486000184000000004624a068800072b030855000066200000000000000000940ab200043a80000001290ca800099058c000000047884b40a80000000000cf99d8a2a6fd29182d0e3e57c1011f54f2668e01380003ae7f20e2800031c0f90c300000d2000000210ce787700001b68b320000000000000765000000000000000000002440003d91eac0001b000015c8a3c0003a283d00000001a199a80ce57b000219c00000000000007c80002d49b80b420000000cf0bc6246000113c9242180000000eb0429000000000000034f8640f9a00027d800022e7fe0998000eea2840f58ef435660339f8b6044a1003588b1ca043e22a584750546f819d81940000002b68e484e253c0001c440000003ab04d50a00003bd8e9c00a2bd1a520b00003343c78000e7432d03c06d8ea008609e8b542fa0001fa0bc039c5693d196cc4660880828ebc00013a3768e449046f613391306ae47e000000000000036e0e8c0003031d58079028000000199c00058628f891c1541aa2161860fbc72028297c4e840e82ce00009f05dd0d49c2863c00020815d09820dc37a82e8b264912ca8aa80003e100000010925cd36b946400000032694b888c01c000000000000000000000000000738768c36000000172458810400000000000003f5800000000033180003162e92e8000000000000000006a26f300012f802c00b000000000000000004444b0585000068cfee000000142c0000002b111c8b900002d792f0e380000000000000000000092103600005b000000000000001c060a0004238000790633136800000000000000000007262048bcd0745df000174c0006c70e0042d09e2e739503eca566e80000000000000000194c00000000016f80006452039f1c62c29100000000005bb00000000000074221d646e04962f217480004eb13402890560000000000e2006440008d825c22c1db106c00000000000c02045c037280003cc3110001abc6b042108305dca400003141c4c71400000000cc65c35f0191918e886c642899580000000000e900000000000ac099c02202991341462d921980000006663221e9c732834000000000086f3fe8994c7c00020f8000aa086303994b00004670000000000000274000082e70e00009f4a0029d00014d83a400000000000000000000000e7c3402ec12fc0001e300005ac1a
  | 15 => 0x37a0ac983510871500020a0000000000192800040f3772204a5a0003fd954800000000021c4fce87c0000a0c85a46400000000002cf13f80000001090000000f861d4047189847283036f01680b04c0183a1480e400000000000000d500002d49340570df93e800000000010780000002e8934ce7a1e51c308783b675f0d40b4039082709d84642b00002fa000000003b00000000000002db9f5800000000010640007f100000000001de0000000000000000007c000000000000000000000000000000001a98000aa61cc1dd8000000826000058000022e0630e50b8c3ff25a092484800006a00009b0000207120400000000013309f200035b800000000037d86942b82d610480000006b230080000007782330ecc38414b2f312a0e1800043200000003273290214fde0002f9000107800000000000b28552cb000046e7d942b1e0499e1f50040000dac43517400b50a600013b05fc00004a36c8a50d6c000000116c6fa0ff3e21a2494e7370cf09a50f410c31c0e4cb8800007200001900001030c34000000000063c0006f121c13c8f0068b1100d8094474c1670cfc54e1933a39b3472031b2e5104800069d3f1900c0002612a18b14a6e00034a000000000000000003fa2e000000001e667e07a80005dc0001b61d2c23c86b00005ec234000000213816056300000000001073438d1c2ca3a518d000000058111f8b710663df3400000a822033a911f400000031e80002c4000000000000000000000000000001b50000000724000000000064e2998a0098a58f15589e03f80ed3f3176c0005d73180e7400082126f80000000000000000cf665e00000a800000000006245a60002990ec81624d900002800000060538000d7800000000008221ba0000000a4e0001fe80001300b700001e40000000000ac48ae5fb26b088400000000018ec00000000011bc00050f3c70000314000062957800000004b89d482629910c800008a43d19292647827091ce0d08df82cb26d84e0a4c57d00019b42e865d00000000007992ae0ce49d20000221f38c3e3fc3f109740002af0f8a2141a47d72bc80000003e60000c246bc29a3500000e6480e2558fa096454e256818cd6020c0f90b84b007f00001dc45bc8692b7800000016c0001e98c240cb00012300001201ea88d01bc0260681030dc85c50a42198af075744105409543360001a08ae22170001cc4f5c1cf0529fccc544b81ca995c0000000000000f98517000000065817600005c00000000000e34000000000159c57254a0ea80000006151eb847c28e35000013d40ac522156800090a6a920300000007d200000006a800040880008440003d10000000000000000000000027b8000f180000001ee4b2200010a084400000000000010806c21021c8400000005206085e8000000178800075b00
  | 16 => 0x3188000ac80003d68e3893e7d10001b40f6600000015e87ec000000000000053d000054875200000014687406dd01e20941848881590f30e7649300000000e20001cf80000002080001a5800050c1ad9df10c06aa000192498450407704c40000ea0ec8528ad443241f000000084109f81bc88a53a4190838ca88360279eb049a298000000000035a1bd8000da481941ea1950b24341f38000c2c2630001bfc0000000000000e941fb0000000000587000000000027900016d00000000001d982e609b11699c00001e21fb95c0a6200002695ac000000000000000000016600009e00df06789dc35c3e512c8a2053c000000158400022a3a011a452e2e439c1794ae61c10240e1029247916da0888783d41cc05a812c07e001a0ec75c1ea03f9ef8d747bb0000000de44022a8894819a0ad3a40a8837c12402585100002e32f617dc0000003a7087400000022d00002cc5562ad00000020000000df000000000000000000430ce036824a31c000031c00000006986210ae6eb30593c49204980001980d820003341d9000000e3a198d86301e400001a09160c03738a404d88793b1170447463f03e8c7c69e4ef33c80000001b934d8ca8c524230081da4e4a5fa16500004e40f100000000007840e300001f80001530204bec5d916b8c5ccc83661e887240
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x7635051003eb6635051003eb46350510007946350510006946350510006b76250510006b56250510007365250510007345250510007973250510007953250510007b37050510007b0705051000eb7605051000fb36050510005b5748c510026d4638c510014f4764c510006756588510005b57488510014f47648510006756548510007c532485100053d74d41100065f63d41100065c63d41100057571d41100073541d41100347f76541100047d76541100065f63541100065c6354110005777154110007354154110017701054110026d8638c110007b1418c110007d2318c11000cf8764c110007b1414c110007d1314c110006796588110007b1418811000cf87648110006796548110007c93248110007b14148110007e121481100047d749941001c7e729941000e3f419941000e3d41994100047f745941001c7c725941000c7f715941000c7d715941000e3f415941000e3d41594100147f70594100147d705941002e3e759901002e3d759901000e3f519901000e3d51990100163f50990100163d50990100063e75590100063d755901000cbf715901000cbd715901000e3f515901000e3d51590100163f50590100163d5059010016b71059010016b510590100347f76d50100047d76d501002e3e64d50100063d64d50100047f76550100047d765501002e3e64550100063d64550100065f5498c100065d5498c10004dd7298c1000e5f5198c1000e5d5198c1000e9f4198c1000e9d4198c100165f5098c100165d5098c100065f5458c100065d5458c10004df7258c1000e5f5158c1000e5d5158c1000e9f4158c1000e9d4158c100165f5058c100165d5058c10016d71058c10016da1058c10016d51058c1000ed91058c1001e6f759881001e6c75988100066f54988100066d549881001ece739881001ecd739881000e6f519881000e6d519881000eaf419881000ead41988100166f50988100166d50988100047f75588100347c75588100066f75588100066c75588100066f54588100066d5458810006ce7358810006cd735881000e6f515881000e6d515881000eaf415881000ead41588100166f50588100166d5058810016e71058810016ea1058810016e5105881000ee9105881001c7f76948100047d76948100063e64948100063d64948100065e63948100065d639481001e6e62948100066d629481001c7f76148100047d76148100053d74148100063e64148100063d64148100065e63148100065d631481001e6e62148100066d6214810005757114810005797014810024df76cc810004dd76cc8100065e65cc8100065d65cc8100069e64cc8100069d64cc81001ece62cc810006cd62cc810004df764c810004dd764c8100065e654c8100065d654c8100069e644c8100069d644c81001ece624c810006cd624c810
  | 1 => 0x8710007c532487100053d74d43100063e64d43100063d64d43100057571d43100073541d43100063e64543100063d64543100057771543100073541543100363e74996100047d74996100363d74996100043d749961001c7e72996100047f745961001c7c72596100167a20596100347f76d52100047d76d52100047f76552100047d76552100463f645521002e3c64552100047f7558a100347c7558a10004bf7458a1002cbc7458a1001c7f7694a100047d7694a10005797094a1001c7f7614a100047d7614a100053d7414a10005757114a10005797014a100065e65cca100065d65cca100065e654ca100065d654ca1001ece624ca10006cd624ca100057970d46100057b70546100063e65d06100063d65d06100063e65506100063d6550610006796548210007c932482100053d74995100363e74995100047d74995100363d74995100043d74995100365e73995100365d739951001c7e72995100047d71995100367571995100047d7099510036797099510004df7359510024dc73595100047f74595100065f73595100065c735951001c7c72595100047f71595100067771595100047f70595100067b70595100347e75d91100047d75d9110004df7359110024dc73591100347f76d51100047d76d51100047f76551100047d76551100063f645511002e3c64551100347e75d8d100047d75d8d10024de76d8d100065e65d8d100065d65d8d100065e75d8d100065d75d8d100065f54d8d100065d54d8d10004dd72d8d10004de7618d100065e6518d100065d6518d10005cd7218d100265e7518d100265d7518d100269e7418d100269d7418d100065f5418d100065d5418d10026ce7218d10004dd7218d10026cd7218d10004cd7218d10026d57118d10026d97018d100347e75d89100047d75d89100047f75589100347c7558910004bf745891002cbc7458910004df7358910024dc735891001c7f76949100047d76949100065f63949100065c639491000575719491000579709491001c7f76149100047d76149100053d74149100065f63149100065c6314910005757114910005797014910004de76cc910024dc76cc9100065e65cc9100065d65cc910004de764c910004dc764c9100065e654c9100065d654c91001ece624c910006cd624c9100065f63d45100065c63d45100057970d45100065f63545100065c63545100057b705451000f7010545100063e65d05100063d65d05100069f63d05100069c63d051000fb010d0510005b57490510006d463905100063e65505100063d65505100069f63505100069c6350510007375150510007355150510014f47650510007375450510007355450510006d46350510015f0705051002eb77650510006b476505100073675505100073575505100073665505100073565505100079
  | 2 => 0x163f50990200163d50990200063e75590200063d755902001e3e525902001e3c525902001e9f325902001e9d3259020004bf71590200163f50590200163d5059020016af2059020016ba2059020016ad205902001eb920590200347f76d50200047d76d502002e3e64d50200063d64d50200047f76550200047d765502002e3e64550200063d64550200065f5498c200065d5498c2001e5e5298c2001e5c5298c200165f5098c200165d5098c200065f5458c200065d5458c2001cdf7258c2001cdd7258c2001e5e5258c2001e5c5258c200165f5058c200165d5058c20016cf2058c20016cd2058c2000e76759842000e75759842000eb6749842000eb5749842000677549842000675549842001e76529842001e74529842001ed7329842001ed53298420016775098420016755098420006767558420006757558420006b67458420006b5745842000677545842000675545842001e76525842001e74525842001ed7325842001ed53258420016775058420016755058420016e72058420016f22058420016e5205842001ef120584200347f76d44200047d76d44200063e64d44200063d64d44200065e63d44200065d63d442000e7661d44200067561d44200047f76544200047d76544200063e64544200063d64544200065e63544200065d635442000e76615442000675615442002cbf76d0420004bd76d04200063e65d04200063d65d04200069e63d04200069d63d042000eb661d0420006b561d0420004bf7650420004bd76504200063e65504200063d65504200069e63504200069d635042000eb66150420006b561504200047d749971001c7e729971000e3f419971000e3d41997100047f745971001c7c725971000e3f415971000e3d415971000e76215971002e3e759931002e3d759931002e9e739931002e9d739931000eb6719931000e3f519931000e3d51993100063e75593100063d755931000e3f515931000e3d515931000eb621593100347f76d53100047d76d531002e3e64d53100063d64d53100047f76553100047d765531002e3e64553100063d64553100047f7558b100347c7558b1001c7f7694b100047d7694b100063e6494b100063d6494b10005757194b1001c7f7614b100047d7614b100053d7414b100063e6414b100063d6414b10005757114b10005797014b100065e65ccb100065d65ccb100069e64ccb100069d64ccb100065e654cb100065d654cb100069e644cb100069d644cb1001ece624cb10006cd624cb1002eb6645071000737545071000735545071000db77650710006b7765071000736755071000735755071000f36655071000f35655071003eb6635071000eb4635071000eb76250710006b56250710007365250710007345250710007973250710007953250710006756548710006b5644
  | 3 => 0xc72195200047d711952003679701952002cbe76d91200063f65d91200063c65d91200063f75d91200063c75d91200563e52d91200563c52d9120004bd71d91200047f75591200347c7559120004be76191200063f65191200063c6519120005b5711912002e3e751912002e3d751912002e9e731912002e9d731912002ead721912004e3e521912004e3c521912002eb67119120004bd711912002eb57119120004b5711912002eb970191200047e76d51200347c76d51200063f64d512002e3c64d51200057970d51200047e76551200047c76551200063f645512002e3c64551200047f7558d200347c7558d20004bf7458d2002cbc7458d20004f77158d2000cf47158d2002eac6490920005cd7390920014ec76509200072d54509200065f65cc9200065c65cc9200069f64cc9200069c64cc920005cd738c9200065f654c9200065c654c9200069f644c9200069c644c92001f4e524c92001f4c524c920014ec764c920026cf764c920006cc764c9200074f754c9200074c754c9200074f654c9200074c654c9200078f644c9200078c644c9200074f544c9200074d544c920007cb704c920007c8704c92001ecf604c92001fcb604c920006cd32d85200047e76d45200347c76d45200063f64d45200063c64d45200074d32d45200057970d45200047e76545200047c76545200063f64545200063c64545200074d3254520004be76d052002cbc76d05200063f65d05200063c65d05200078d32d0520004be7650520004bc76505200063f65505200063c65505200078d3250520005cd73c8520014ec7648520007655148520007a5414852001c7e76d41200053d74d41200063f64d41200063c64d412001d6e72d41200074d32d4120005797594120036786594120007c9329412001c7c76541200063f64541200063c645412001d6c72541200074d325412001cf87654120007c932541200367b765412001d78765412000678765412001c7876541200057b74541200073b64541200073864541200076b725412001d7a725412001d7872541200076872541200167b62541200176b62541200076a42541200076942541200075b32541200076a32541200075932541200076932541200074932541200057b71541200073b41541200073941541200076b215412000769215412000579759012002eb86490120007395490120007aa4290120007c9329012001cf87650120005797550120007a94250120007c932501200047d749942001c7e729942001c7c729942001e5f329942001e5d32994200047d71994200047f745942001c7e725942001c7c725942001e5f325942001e5d32594200047f71594200167a205942001e79205942002e3e759902002e3d759902001e3e529902001e3c529902001e9f329902001e9d3299020004bd7199020
  | 4 => 0x8430006d53258430016775058430016755058430016d73058430016f23058430016d53058430026f130584300347f76d44300047d76d44300063e64d44300063d64d44300066e62d44300066d62d443000e7661d44300067561d44300047f76544300047d76544300063e64544300063d64544300066e62544300066d625443000e76615443000675615443002cbf76d0430004bd76d04300063e65d04300063d65d0430006ae62d0430006ad62d043000eb661d0430006b561d0430004bf7650430004bd76504300063e65504300063d6550430006ae6250430006ad625043000eb66150430006b5615043003f943150430004dd768c4300069d648c430006cd628c430006d5618c4300047f75593200347c755932001c7e76d532001c7c76d532001c7e765532001c7c765532002e3e64553200063d64553200265e7598f200265d7598f200269e7498f200269d7498f200065f5498f200065d5498f2001ece7298f2001e5e5298f2001e5c5298f200047f7558f200347c7558f200065f7558f200065c7558f200065f5458f200065d5458f2001e5e5258f2001e5c5258f2001ecf2158f200072d5450b20026ce634cb2001dcf764cb20006cf764cb200074f754cb200074c754cb2001f4f654cb2001f4c654cb200074f544cb200074d544cb200047f75587200347c7558720006cd325872001c7e76d47200065e63d47200065d63d47200074d32d472001c7c76547200065e63547200065d63547200074d325472000e7661547200067561547200663f65d07200663c65d07200069e63d07200069d63d07200078d32d072005e3f655072005e3c65507200069e63507200069d63507200078d325072000eb66150720006b56150720006cd6348720007655148720007a541487200053d74d43200065e63d43200065d63d432001d6e72d43200074d32d43200065e63543200065d635432001d6c72543200074d32543200363e74996200047d74996200363d74996200043d74996200047d71996200167a70996200047f74596200047f71596200347f76d52200047d76d52200057970d52200047f76552200047d76552200463f645522002e3c64552200473a40552200065e65cca200065d65cca200065e654ca200065d654ca20004df7358620024dc73586200347f76d46200047d76d46200057970d46200047f76546200047d76546200063e65d06200063d65d06200063e65506200063d655062000eb66150620006b561506200367a65542200157b76542200067b76542200057b745422001d7a725422001d7872542200075b32542200075932542200057b71542200073b41542200073941542200057975502200347e76d95200047d74d95200047d71d9520004bf745952002cbc74595200047e76195200047d741952001c7e721952001c7
  | 5 => 0xeb6615044002e3e64553300063d64553300071d5450f300047f7558b300347c7558b30026cf3258b300053d7414b30005757114b30005797014b3003f9731507300053d74d43300363e74996300047d74996300363d74996300043d749963001c7e72996300047d71996300047f745963001c7c72596300047f71596300347f76d52300047d76d52300047f76552300047d76552300463f645523002e3c64552300047f7558a300347c7558a30004bf7458a3002cbc7458a3001c7f7694a300047d7694a3001c7f7614a300047d7614a300053d7414a30005757114a30005797014a300065e65cca300065d65cca3001cdf764ca300065e654ca300065d654ca3001ece624ca30006cd624ca300347f76d46300047d76d46300047f76546300047d76546300063e65d06300063d65d06300063e65506300063d655063000eb66150630006b56150630005cd720c63000795410c630005d9700c6300063f645513002e3c6455130014dc7650d300071d5450d300347e75d89300047d75d89300053d74149300057571149300057970149300059d74cc930014dc764c930006cf624c93000677615453000e746154530006b7615053000eb46150530004de76cc5300079541cc530014dc764c5300053d74d41300175830541300047d749943001c7e72994300265f32994300047d71994300047f745943001c7c72594300265f32594300047f715943002e3e759903002e3d75990300269f3299030004bd71990300163f50990300163d50990300063e75590300063d75590300269f3259030004bf71590300269c31590300163f50590300163d50590300169f30590300169d30590300347f76d50300047d76d503002e3e64d50300063d64d50300047f76550300047d765503002e3e64550300063d645503001e6f759883001e6c75988300066f54988300066d54988300166f50988300166d50988300047f75588300347c7558830026cf32588300066f75588300066c75588300066f54588300066d5458830026ce7358830026cc31588300166f50588300166d5058830016cf3058830016cd305883001c7f76948300047d76948300063e64948300063d649483001e6e62948300066d629483001c7f76148300047d76148300053d74148300063e64148300063d641483001e6e62148300066d62148300057571148300057970148300065e654c8300065d654c8300069e644c8300069d644c83001ece624c83000e76759843000e75759843000eb6749843000eb57498430006775498430006755498430006765298430006745298430026d73298430006d53298430016775098430016755098430026d43158430006767558430006757558430006b67458430006b57458430006775458430006755458430006765258430006745258430026d7325
  | 6 => 0xf76545400063e65d05400063d65d05400059d73d0540014bc76505400063e65505400063d6550540006b761505400053d74d41400347f76541400047d76541400053f745414002e3e749944001c7e72994400047d719944002e3f419944002c7f745944002c7d745944001c7c72594400047f715944002e3f41594400363e655504002d3f76550400063f765504002f1e635504002f1d635504004d3c725504002f2e625504002f2d62550400053f715504002f36615504002f3561550400453f70550400453d70550400463e605504002f3a605504002e5f5498c4002e5d5498c40004dd7298c4002e9f4198c400165f5098c400165d5098c400063d5458c4002e5f5458c4002e9e5458c4002e5d5458c400069d5458c400061d5458c40004df7258c4002e9c4258c4002e9f4158c400165f5058c400165d5058c400169f4058c400169d4058c4001e6f759884001e6c759884002e6f549884002e6d549884001ece739884001ecd739884002eaf41988400166f50988400166d50988400047f75588400347c75588400063d545884002eac42588400066f75588400066c755884002e6f545884002eae545884002e6d5458840006ad54588400062d5458840006ce7358840006cd735884002eaf41588400166f50588400166d5058840016af4058840016ea4058840016ad405884002ee9405884001c7f76948400047d76948400065e63948400065d639484001e6e62948400066d629484001c7f76148400047d76148400053d74148400065e63148400065d631484001e6e62148400066d6214840005757114840005797014840004bd769084004d3f75908400069d6390840006ad6290840024df76cc840004dd76cc8400065e65cc8400065d65cc8400071d54cc84001ece62cc840006cd62cc840004df764c840004dd764c8400065e654c8400065d654c8400071d544c84001ece624c840006cd624c84000e76759844000e75759844002e77549844002e755498440006765298440006745298440006d73298440006d532984400167750984400167550984400063d545844002eb7415844000676755844000675755844002eb6745844002e77545844002eb6545844002e755458440006b55458440006355458440006765258440006745258440006b6425844002eb44258440006d73258440006d53258440016775058440016755058440016b74058440016b540584400347f76d44400047d76d44400053d74d44400065e63d44400065d63d44400066e62d44400066d62d444000e7661d44400067561d44400047f76544400047d76544400065e63544400065d63544400066e62544400066d625444000e7661544400067561544400053d75504400063e65504400063d65504400069e63504400069d6350440006ae6250440006ad6250440
  | 7 => 0x85500053e74085500053d74085500055e73085500055d73085500157a70085500057970085500053e74d81500053d74d81500373a74d81500373974d81500057972d81500075b32d81500075932d81500073b41d81500073941d81500363e74994500363d74994500367970994500363f54590500047f76550500047d76948500065e65cc8500065e654c85001ece624c850006cd624c8500367751584500047f76544500063e65d04500063e655045000eb66150450006b5615045001c7e72997400047d719974002e3f419974002e3f435974001c7c725974002e3f42597400047f715974002e3f41597400463e405974002e3c40597400063d6550f400047f7558b400347c7558b4001c7f7694b400047d7694b400053d7494b4001c7f7614b400047d7614b400053d7414b40005757114b40005797014b400063d6550b400065e65ccb400065d65ccb400065e654cb400065d654cb4002eb741587400347f76d47400047d76d47400047f76547400047d76547400063e65507400063d65507400053d74d43400053f74543400173a40543400363d749964001c7e72996400047d719964001c7c72596400047f71596400167a20596400057970d52400363e65952400057b705524002f3b4055240034bf76552400453f76552400063f76552400363c76552400553c72552400053f71552400453f70552400073b705524004738705524002e3e60552400063d5458e400047f7558a400347c7558a400063d5458a4001c7f7694a400047d7694a40005797094a4001c7f7614a400047d7614a400053d7414a40005757114a40005797014a400553f7590a400053d7510a40005b57110a40005b97010a400065e65cca400065d65cca400071d54cca400065e654ca400065d654ca400071d544ca4001ece624ca40006cd624ca400063d5458640004df7358640024dc73586400347f76d46400047d76d46400053d74d46400047f76546400047d76546400053d75d06400063e65d06400063d65d064000cbf76506400053d75506400063e65506400063d655064000eb66150640006b561506400047d74995400363d74995400043d749954001c7e72995400047d71995400047d70995400367970995400047f74595400063f745954001c7c72595400047f71595400047f70595400067b70595400463e40595400057970d51400057b70551400347e75d8d400047d75d8d400063d65d0d40005b571d0d40014bc7650d400063d6550d400347e75d89400047d75d89400047d76949400053d74949400057970949400047d76149400053d7414940005757114940005797014940004be76d09400063d65d0940014bc76509400063d65509400065e65cc9400065d65cc9400065e654c9400065d654c9400347e75d85400047d75d85400047d76d45400047
  | 8 => 0x47e76151500147e7694d500147c7654d500053e7414d500053d7414d500047e76d49500147e76949500055e73949500055d739495001e6c62949500157a70949500147c76549500053e74149500053d74149500055e73149500055d73149500057671149500057571149500157a70149500147e76945500053e74945500053d74945500147c76545500067761545500047e76145500053e74145500053d741455001c7e72d91500047d71d91500063f64991500057970991500057b70591500063d6419150005797098d500057b7058d500053e7418d500053d7418d500047e76d0d500047d76d0d500057671d0d500057571d0d500047e7610d500047d7610d500055e73989500055d73989500057970989500053f74589500053c74589500057b70589500053e74189500053d74189500055e73189500055d731895001e6e62189500057671189500057571189500047e76d09500047d76d095001c7c76909500063f64909500055e73909500055d73909500157a70909500057970909500047f76509500047c76509500047e76109500047d76109500063f64109500055e73109500055d73109500057671109500057571109500157a70109500057970109500047e76cc9500047d76cc9500053e74cc9500053d74cc9500065e76cc9500065d76cc9500071e74cc9500071d74cc9500065f64cc95001e5e62cc95001e5c62cc9500055d738c9500157a708c95000579708c9500047f764c9500047c764c9500065f764c9500065c764c9500065f644c9500074f724c95001e5e624c95001e5c624c9500055e730c9500157a700c95000579700c9500047d74d855001c7e72d85500065f32d85500065d32d85500053e74985500053d74985500057970985500055f73585500055c73585500057b70585500053e74185500053d74185500047e76d05500047d76d05500063f64d05500055e73d05500055d73d05500063e76d05500063d76d05500071e73d05500071d73d05500663c62d05500071f32d05500071d32d05500063f61d05500047e76905500047d76905500053d74905500047e76505500063f64505500063e76505500063d765055005e3c62505500071f32505500071d32505500073771505500063f61505500047e76105500047d76105500053e74105500073541cc5500047e768c5500047d768c5500053e748c5500053d748c5500047e760c5500047d760c5500053e740c5500053d740c5500056e720c5500056d720c55000735410c5500157a700c55000579700c55001c7c76c85500055e73c85500055d73c85500074d32c85500157a70c85500057970c85500047e76885500047d76885500053e74885500053d74885500073541885500047f76485500047c76485500074d32485500073541485500047e76085500047d760
  | 9 => 0xd64d0f500057671d0f500057571d0f500063d6490f500063d6450f500347e7610f500047d7610f500063d6410f500063e6498b500063d6498b500055e7398b500055d7398b5001e6c6298b500063d6458b500347e76d0b500047d76d0b500063d64d0b5001c7f7690b500063d6490b500055e7390b500055d7390b500047f7650b500347c7650b500063d6450b500347e7610b500047d7610b500063d6410b500055e7310b500055d7310b50005767110b50005757110b500157a7010b50005797010b500347e76ccb500047d76ccb500053e74ccb500053d74ccb500063d64ccb500065e76ccb500065d76ccb500071e74ccb500071d74ccb500071e64ccb500065d64ccb500071d64ccb500061d64ccb5001e5e62ccb5001e5c62ccb500063d648cb500047f764cb500347c764cb500063d644cb500065f764cb500065c764cb500071e644cb500065d644cb500071d644cb500061d644cb500074f724cb5001e5e624cb5001e5c624cb500063d640cb500053e74987500053d74987500063d64987500063e64587500063d64587500047f74587500063e74587500063d745875001c7c72587500065f32587500065d32587500347e76d07500047d76d07500063d64d07500055e73d07500055d73d07500053f76d07500063e76d07500053d76d07500063d76d07500043d76d07500071e73d07500071d73d07500663e62d07500071f32d07500071d32d07500063d61d07500347e76907500047d76907500063d64907500047d76507500063d64507500053f76507500063e76507500053d76507500063d76507500043d765075005e3e62507500071f32507500071d32507500073771507500063d61507500347e76107500047d76107500063d64107500063d64cc7500067561cc7500073541cc7500347e768c7500047d768c7500053e748c7500053d748c7500063d648c7500063d644c7500347e760c7500047d760c7500053e740c7500053d740c7500063d640c7500056e720c7500056d720c75000675610c75000735410c7500157a700c75000579700c75001c7f76c87500063d64c87500055e73c87500055d73c87500074d32c87500347e76887500047d76887500053e74887500053d74887500063d64887500067561887500073541887500047f76487500347c76487500063d64487500074d32487500067561487500073541487500347e76087500047d76087500053e74087500053d74087500063d64087500055e73087500055d73087500157a700875000579700875002c7f76552500063d645525001e6e6294a500053d7414a50005757114a50005797014a5001ece624ca50006cd624ca5000c7f765465000675615465000eb66150650006b561506500147e76951500063f64951500147c76551500063f645515002e3c6455150
  | 10 => 0x942101e5f329942101e5d329942100e3f419942100e3d41994210047d70994210047f745942101c7e725942101c7c725942101e5f325942101e5d325942100e3f415942100e3d415942100e76215942101e7521594210047f705942102e3e759902102e3d759902101e3e529902101e3c529902101e9f329902101e9d329902100e3f519902100e3d51990210063e75590210063d755902101e3e525902101e3c525902101e9f325902101e9d325902100e3f515902100e3d515902100eb6215902101eb521590210347f76d50210047d76d502102e3e64d50210063d64d50210047f76550210047d765502102e3e64550210063d64550210065f5498c210065d5498c2101e5e5298c2101e5c5298c2100e5f5198c2100e5d5198c2100e9f4198c2100e9d4198c210065f5458c210065d5458c2101e5e5258c2101e5c5258c2100e5f5158c2100e5d5158c2100e9f4158c2100e9d4158c2100ecf2158c2100ecd2158c210167a75980210167975980210067b549802100679549802101e7a529802101e78529802101edb329802101ed9329802100e7b519802100e79519802100ebb419802100eb941980210067a75580210067975580210067b545802100679545802101e7a525802101e78525802101edb325802101ed9325802100e7b515802100e79515802100ebb415802100eb9415802100eeb215802100ef2215802100ee9215802101ef121580210363c5299350004bd71993500363f51993500147c75593500363f54593500363c54593500363e75593500363f53593500363c53593500363f52593500363c5259350004bf71593500363f51593500363c51593500463e50593500363c50593500063d649535002e3e64553500147c7558f500063d6494f500063d6454f500147c7558b500063e6494b500063d6494b500055e7394b500055d7394b500063d6454b500069e64ccb500069d64ccb500069e644cb500069d644cb500147c75587500367751587500053e74947500053d74947500063d64947500063e64547500063d645475002cbf76d0750004bd76d0750004bf7650750004bd76507500363f64993500363c62993500053d71993500363f61993500363c645935001c7c72593500047f71593500063f76593500363f63593500363c63593500363f62593500363c62593500053f71593500363f61593500363c61593500063f73593500063e73593500063d73593500063c73593500063f72593500063e72593500063d72593500063c72593500063f71593500043f71593500063e71593500063d71593500063c71593500063f70593500063d70593500463c70593500463e30593500463c30593500463e20593500463c20593500463e10593500463c10593500063d6498f500063d6458f500347e76d0f500047d76d0f500063
  | 11 => 0x663e52992210663c529922100eb6719922100e3f519922100e3d51992210063e75592210063d755922105e3e525922105e3c525922100e3f515922100e3d515922100eb710592210347f76d52210047d76d522102e3e64d52210063d64d52210057571d52210047f76552210047d765522102e3e64552210063d64552210065e65cca210065d65cca210069e64cca210069d64cca210065e654ca210065d654ca210069e644ca210069d644ca2103676655462100d77765462100677765462100577745462100f36645462100f35645462101d76725462101d74725462100757325462100755325462100577705462100575755062102eb6645062100737545062100735545062100db77650621006b7765062100736755062100735755062100f36655062100f35655062103eb6635062100eb4635062105f36525062105f345250621007973250621007953250621004df7358221024dc7358221006b541582210347e76d95210047d74d95210047d70d95210047e76195210053d74195210363e74195210047d74195210363d74195210043d74195210367571195210047d70195210047f75591210347c75591210047e76d51210347c76d51210057571d51210047e76551210047c765512102e3e64551210063d64551210047f7558d210347c7558d210065f65cc9210065c65cc921005cd738c9210065f654c9210065c654c92101f4e524c92101f4c524c92100cec764c921026cf764c921006cc764c9210074f754c9210074c754c9210074f654c9210074c654c9210074f544c9210074d544c921007c7714c921007c4714c92101ecf614c92101fc7614c92101c7e76d452101d6e72d45210074d32d4521005757594521036746594521005b57494521007c5329452101c7c765452101d6c72545210074d325452101cf47654521007c5325452103677765452101d74765452100674765452101c74765452100577745452100767725452101d76725452101d74725452100764725452100e77625452100f6762545210075732545210076632545210075532545210076532545210074532545210057770545210063f65d05210063c65d05210078d32d05210073551d0521005757590521005b57490521007c532905210063f65505210063c65505210078d325052100737515052100735515052101cf47650521005757550521007375450521007355450521007c5325052102eb77650521006b4765052100736755052100735755052100737655052100734655052103eb6635052103eb46350521007a77250521007a4725052100eb7625052100fa7625052105f36525052105f345250521007973250521007a63250521007953250521007a53250521007853250521006cd32d8121006b541d81210047d749942101c7e729942101c7c729
  | 12 => 0xd41988310047f75588310347c7558831026cf32588310066f75588310066c75588310066f54588310066d5458831026ce7358831026ce4358831006cd435883100e6f515883100e6d515883100eaf415883100ee6415883100ead415883100ecf315883100ecd3158831026cc305883101c7f76948310047d76948310063e64948310063d649483101e6e62948310066d629483101c7f76148310047d76148310053d74148310063e64148310063d641483101e6e62148310066d62148310057571148310057970148310065e654c8310065d654c8310069e644c8310069d644c83101ece624c83102eb6645043100737545043100735545043103f964350431007954350431006e5625043100db77650431006b7765043100736755043100735755043100f36655043100f35655043103f96735043100795735043103eb6635043100f96635043100fa66250431006b5625043100fa56250431006a5625043100736525043100734525043103f97325043100795325043100fb2605043100fb160504310167a75980310167975980310067b54980310067954980310067a5298031006785298031026db3298031006d9329803100e7b519803100e79519803100ebb419803100eb94198031006b54158031026d830580310067a75580310067975580310067b5458031006795458031026da4358031006d943580310067a5258031006785258031026db3258031006d9325803100e7b515803100e79515803100ebb415803100ef2415803100eb94158031006f14158031006b1415803100edb315803100ef2315803100ed93158031026f131580310047f75593210347c755932101c7e76d532101c7c76d532101c7e765532101c7c765532102e3e64553210063d64553210265e7598f210265d7598f210269e7498f210269d7498f210065f5498f210065d5498f2101ece7298f2101e5e5298f2101e5c5298f210047f7558f210347c7558f210065f7558f210065c7558f210065f5458f210065d5458f2101e5e5258f2101e5c5258f2101ecf2058f21026ce634cb2101dcf764cb21006cf764cb210074f754cb210074c754cb2101f4f654cb2101f4c654cb210074f544cb210074d544cb210065e63d47210065d63d472101d6e72d47210074d32d47210065e63547210065d635472101d6c72547210074d32547210663f65d07210663c65d07210069e63d07210069d63d07210078d32d072105e3f655072105e3c65507210069e63507210069d63507210078d32507210047f75583210347c7558321004bf745832102cbc7458321006cd32583210047d749962100e76719962100e3f419962100e3d41996210047d70996210047f745962100e3f415962100e3d41596210047f705962102e3e759922102e3d759922102e9e739922102e9d7399221
  | 13 => 0x94410047d709944101c7c725944100e3f415944100e3d41594410047f705944102e3e759904102e3d759904102e9e739904102e9d739904102eb5719904100e3f519904100e3d51990410047f75588410347c755884101c7f76948410047d76948410663e649484101c7f76148410047d76148410053d74148410663e64148410057571148410057970148410065e65cc8410065d65cc8410069e64cc8410065e654c8410065d654c8410069e644c84101ece624c841006cd624c84102e3e64553310063d64553310047f7558b310347c7558b31026cf3258b310053d7414b31005757114b31005797014b3100737515073100735515073102cf77650731007375450731007355450731006b7765073102eb4765073100736755073100735755073100797735073103f94735073100eb66350731006b5625073100736525073100734525073103f973250731007953250731006b541583310047d749963101c7e729963100e3f419963100e3d41996310047d70996310047f745963101c7c725963100e3f415963100e3d41596310047f705963102e3e759923102e3d759923102e9d739923100e3f519923100e3d51992310063e75592310063d755923100e3f515923100e3d515923103eb7315923100eb4315923100eb710592310347f76d52310047d76d523102e3e64d52310063d64d52310047f76552310047d765523102e3e64552310063d645523102e9e6490e3102cdf7650e310071d5450e310047f7558a310347c7558a3101c7f7694a310047d7694a310063e6494a310063d6494a3101c7f7614a310047d7614a310053d7414a310063e6414a310063d6414a31005757114a31005797014a310065e65cca310065d65cca310059d74cca310069e64cca310069d64cca3101cdf764ca310065e654ca310065d654ca310069e644ca310069d644ca3101ece624ca31006cd624ca3102e3e64551310063d64551310347e75d89310047d75d893102cbe74d8931004bd74d89310053d741493100575711493100579701493100cdc764c931006cf624c93100dd4714c93100f54315453100f9431505310047d749943101c7e72994310265f329943100e3f419943100e3d41994310047d70994310047f745943101c7c72594310265f325943100e3f415943100e3d41594310047f705943102e3e759903102e3d75990310269e73990310269f329903100eb6719903100e3f519903100e3d51990310063e75590310063d75590310269f325903100e3f515903100e3d51590310347f76d50310047d76d503102e3e64d50310063d64d50310047f76550310047d765503102e3e64550310063d645503102e9e6450c310071d5450c3101e6f759883101e6c75988310066f54988310066d549883100e6f519883100e6d519883100eaf419883100ea
  | 14 => 0x73571995410053571995410053d7099541005b771595410063f765954105d3c72595410053f71595410073771595410053771595410053f70595410053e75d8d410053d75d8d410063d65d8d41005b57198d410063d6558d41005b77158d410053e7518d410053d7518d4100db671d4d41005b571d4d41005b77154d4100db47154d41004be7614d41004bd7614d410053e75d89410053d75d89410063d65d89410059e73989410059d7398941005b571989410053f75589410053c75589410063d6558941005b771589410053e75189410053d75189410059e73189410059d7318941005ba7018941005b970189410059e73949410059d739494100db67194941005b5719494105d3f76949410053d769494105f1e739494105f1d739494105d3e729494105f3671949410053d719494105f3571949410053571949410053d7094941004be7614941004bd76149410059e73149410059d731494100db67114941005b57114941005ba7014941005b9701494105d3f761494105e3e76149410053d761494105e3d76149410043d761494105f1e731494105f1d731494105d3e721494105f2e721494105f3671149410053d711494105f35711494100535711494105f3a70149410053d701494105f397014941005397014941004be76cc941004bd76cc9410053e75cc9410053d75cc9410069e76cc9410069d76cc9410071e75cc9410071d75cc9410071e65cc9410071d65cc94105f1e52cc94105f1c52cc94103f9771cc94103f9471cc9410059d738c94100db6718c941005b5718c9410053f754c9410053c754c941005b7714c94100db4714c9410071f754c9410071c754c9410071e654c9410071d654c9410078f724c94105f1e524c94105f1c524c94100797714c94100794714c9410059e730c94100db6710c941005b5710c9410053e75d85410053d75d85410063e65d85410063d65d85410059e73d85410059d73d854102f3675d854102f3575d85410073665d85410073565d854103db673d854102f9673d85410059673d854102f9573d8541005b572d85410073652d85410073452d85410079732d85410079532d8541005b570d854100f3651d454105d3e72d45410071f32d45410071d32d454100d3d71d45410073761d454100f3431d454100f3621d45410053d70d454100f3710d45410053f76545410053d765454105d3c72545410071f32545410071d325454100d3f715454100737715454100737615454100f34315454100f3621545410053f705454100f3710545410053e75d81410053d75d81410053e75981410053d75981410063d65981410059f73581410059c73581410053e75181410053d75181410063d65181410059e73181410059d7318141005ae7218141005ad721814101c7e729944100e3f419944100e3d419
  | 15 => 0xe75ccb410053d75ccb410059f76ccb410069e76ccb410059d76ccb410069d76ccb410049d76ccb410071e75ccb410071d75ccb410071e65ccb410071d65ccb410671e52ccb410671c52ccb410053f754cb410053c754cb410059f764cb410059d764cb410071f754cb410071c754cb410071e654cb410071d654cb410078f724cb410671e524cb410671c524cb410053d76d47410071e63d47410071d63d47410653e72d47410071f32d47410071d32d47410053d70d47410053f76547410071e63547410071d63547410653c72547410071f32547410071d325474100737715474100f3621547410053f70547410053e75983410053d75983410063d65983410069d635834101c7e729964100e3f419964100e3d41996410047d709964101c7c725964100e3f415964100e3d415964100e7621596410047f70596410057571d524100577715524102f37415524100cf47158e410047f7558a410347c7558a4101c7f7694a410047d7694a41005757194a4101c7f7614a410047d7614a410053d7414a41005757114a41005797014a410065e65cca410065d65cca410065e654ca410065d654ca4101ece624ca41006cd624ca410047d74995410363d749954101c7e72995410047d71995410367571995410047d70995410047f74595410063f745954101c7c72595410047f71595410067771595410047f70595410057571d514100cbe76d51410063f65d51410063e76d51410063d76d514105d3e72d51410073671d51410073571d514102e3f61d514102f3761d51410053d70d51410053d75951410363e659514100577715514100cbc76551410363f76551410063c765514105d3c725514100737715514100734715514102e3f615514102f3761551410053f70551410463c60551410053e75151410347e75d8d410047d75d8d410063d54d8d410053e75d0d410053d75d0d410063d65d0d4100db671d0d4100cbe7690d4100cbc7650d410063d6550d4100db47150d410053e7510d410053d7510d410347e75d89410047d75d89410063d54d89410047d76949410053d74949410057571949410047d76149410053d74149410057571149410057970149410053e75d09410053d75d09410063d65d094100cbe769094105d3f759094105d3c75909410059e73909410059d739094100db6719094100cbc76509410053f75509410053c75509410063d65509410053e75109410053d75109410059e73109410059d731094100db67110941005ba7010941005b970109410065e65cc9410065d65cc9410071f54cc9410071d54cc9410065e654c9410065d654c9410071f544c9410071d544c9410053d74d45410347f76545410047d76545410053f74545410347e75d81410047d75d81410063f6599541005b5719954105d3e72995410053d7199541
  | 16 => 0x90510047f765505102e3e64550510047d76948510063e64948510063d64948510065e65cc8510069e64cc8510069d64cc8510065e654c8510069e644c8510069d644c85101ece624c851006cd624c8510367b505805102e3e749974101c7e72997410047d709974100cbc745974102e3c745974102e3f435974101c7c725974102e3f42597410047f705974102e3c405974102e3f65d53410063d65d534102d3d76d53410063d76d534102f1e63d534102f1d63d53410653e72d53410053d70d53410363e655534102d3f76553410063f765534102f1e635534102f1d63553410653c72553410053f70553410463e605534102e5f5498f4102e5d5498f41004dd7298f4102ed64198f4102ed54198f4100cbc7458f410063d5458f4102e5f5458f4102e9e5458f4102e5d5458f410069d5458f410061d5458f41004df7258f4102e9c4258f4102e9f4058f410069d6390f410063d6550f410269e6350f410047f7558b410347c7558b4100cbc7458b410063d5458b4101c7f7694b410047d7694b410053d7494b410065e6394b410065d6394b4101c7f7614b410047d7614b410053d7414b410065e6314b410065d6314b41005757114b41005797014b410653f7590b410653c7590b410059e7390b410059d7390b410069d6390b410053f7550b410053c7550b410063d6550b41024df76ccb41004dd76ccb410065e65ccb410065d65ccb410071f54ccb410071d54ccb41004df764cb41004dd764cb410065e654cb410065d654cb410071f544cb410071d544cb410053d74d47410065e63d47410065d63d47410053f74547410065e63547410065d635474100f36415474100cbc745834102e3f65997410653e72997410053d70997410063f765974102e3f63597410653c725974102e3f62597410053f705974102e3c605974102f1e6598f4102f1d6598f410059d7298f410063d6558f410069f7658f4102e9f6558f4102f1e6558f410069d6558f4102f1d6558f410061d6558f410059f7258f4102e9c6258f4102e9f6058f4102cbe7614f41004bd7614f410059e7398b410059d7398b410069d6398b410053f7558b410053c7558b410063d6558b410059e7394b410059d7394b410653f7694b410053d7694b410671e7394b410671d7394b410071e6394b410071d6394b410053d7194b410053d7094b4102cbe7614b41004bd7614b410059e7314b410059d7314b4100db67114b41005b57114b41005ba7014b41005b97014b410653f7614b410663e7614b410053d7614b410663d7614b410043d7614b410671e7314b410671d7314b410071e6314b410071d6314b410672e7214b41067367114b410053d7114b41067357114b41005357114b410673a7014b410053d7014b41067397014b41005397014b4102cbe76ccb41004bd76ccb410053
  | 17 => 0xd767110b51005757110b510057a7010b51005797010b510347e76ccb510047d76ccb510053e74ccb510053d74ccb510065e76ccb510065d76ccb510071e74ccb510071d74ccb510065d64ccb5101e5e62ccb5101e5c62ccb510047f764cb510347c764cb510065f764cb510065c764cb510065d644cb510074f724cb5101e5e624cb5101e5c624cb510047f745835101c7c72583510065f32583510065d325835100e3f519925100e3d51992510063d755925100e3f515925100e3d515925100eb6215925102e3e64d525102c7f765525102e3e64552510063d64552510063e6494a510063d6494a5101e6e6294a510053d7414a510063e6414a510063d6414a51005757114a51005797014a510069e64cca510069d64cca510069e644ca510069d644ca5101ece624ca51006cd624ca5100c7e76951510063f649515100c7c76551510063f64551510047e761515100c7e7694d5100c7c7654d510053e7414d510053d7414d510047e76d495100c7e76949510055e73949510055d739495101e6c629495100d76719495100c7c76549510053e74149510053d74149510055e73149510055d731495100d7671149510057a701495100579701495102cbe74d8151004bd74d815101c7e72d91510047d70d91510063f64991510055e73991510055d7399151005757199151005777159151005757198d51005777158d510053e7418d510053d7418d510047e76d0d510047d76d0d5100d7671d0d510057571d0d510047e7610d510047d7610d510055e73989510055d73989510057571989510057771589510053e74189510053d74189510055e73189510055d731895101e6e62189510057a70189510057970189510047e76d09510047d76d095101c7c76909510055e73909510055d739095100d7671909510057571909510047f76509510047c76509510047e76109510047d76109510055e73109510055d731095100d7671109510057571109510057a70109510057970109510047e76cc9510047d76cc9510053e74cc9510053d74cc9510065e76cc9510065d76cc9510071e74cc9510071d74cc9510065f64cc95101e5e62cc95101e5c62cc9510055d738c95100d76718c95100575718c9510047f764c9510047c764c9510065f764c9510065c764c9510065f644c9510074f724c95101e5e624c95101e5c624c9510055e730c95100d76710c95100575710c9510057572d85510075732d85510075532d85510053e74d81510053d74d81510063e74d81510047d74d81510063d74d81510043d74d815101c7e72d81510065f32d81510065d32d81510055f73581510055c73581510367571994510363c529905100e3f519905100e3d51990510363f50990510363f54590510363e75590510363c525905100e3f515905100e3d51590510363f505
  | 18 => 0xc765513202e3e64551320063d645513201d6c725513201cde76d4d320365c6594d3201cdc7654d320065f6514d320059e7414d320059d7414d3201cde76d0d320055e75d0d320055d75d0d320071d54d0d32005d671d0d32005d571d0d3201cdc7650d320071d5450d320055e7510d320055d7510d320055d74d95320055d71d95320055d70d95320055e7599532005cd7299532005cf72595320059e74195320059d74195320055e76195320065e76195320071e74195320055d74195320071d74195320051d74195320055d71195320055d70195320055e75991320055d7599132005cd7299132005d67199132005d571991320055f75591320055c7559132005cf72591320055e75191320055d75191320055e76d51320055c76d513201d5e72d513201d5c72d51320055d71d51320055d70d51320055d75951320071f5495132005cf725513201dcc72551320055e76551320055c76551320071f74551320071e64551320071d64551320074f725513201d5e725513201d5c72551320074c725513201d4c72551320055f71551320055f70551320055e75151320055e75d89320055d75d89320065f65d89320065c65d89320059e74d89320059d74d893201f4e52d893201f4c52d89320274e75d89320274d75d89320074f65d89320074c65d89320278e74d89320278d74d89320074f54d89320074d54d8932005cd71d8932005cd70d893201d5e75d493201f4e52d493201d5f75549320055e75d09320055d75d09320071d54d093201f4c52d09320055f75509320055c75509320071d545093201f8c42509320055e75985320055d75985320059e74985320059d74985320055f75585320055c75585320055e75185320055d75185320059e74185320059d7418532006d56118532005da7018532005d970185320055e75981320055d75981320055f75581320055c75581320059f74581320059c7458132005d77158132005d471581320055e75181320055d75181320059e74181320059d7418132005d67118132005d5711813202e3e64550320063d64550320265e7598c320265d7598c320269e7498c320269d7498c320065f5498c320065d5498c32026cd7298c3201e5e5298c3201e5c5298c3200c7c75593510363f545935100c7c7558f5100c7c7558b510055e7394b510055d7394b5100c7c75583510367b50583510363f649935101c7c72593510047f70593510347e76d0f510047d76d0f510063d64d0f5100d7671d0f510057571d0f510063d6450f510347e7610f510047d7610f510055e7398b510055d7398b5101e6c6298b510347e76d0b510047d76d0b510063d64d0b5101c7f7690b510055e7390b510055d7390b510047f7650b510347c7650b510063d6450b510347e7610b510047d7610b510055e7310b510055d7310b51
  | 19 => 0x844202e77545844202e75545844202eb74358442006b5435844201e76525844201e74525844201eb7425844201eb5425844201ed7325844201ed5325844202eb440584420167a759804201679759804202e7b549804202e79549804201e7a529804201e78529804201edb329804201ed9329804202ebb419804202eb840580420067a755804200679755804202e7b545804202e79545804202ebb4358042006b9435804201e7a525804201e78525804201ebb425804201eea425804201eb9425804202ee9425804201edb325804201ed9325804202ebb41580420047d74997320265e73997320047d71997320047d709973201cdc73597320047f74597320265c73597320047f71597320047f705973202e3e759933202e3d75993320269e73993320763e52993320763c529933202eb67199332004bd719933202eb57199332004b5719933201cdc73593320063e75593320063d75593320269c735933206e3e525933206e3c5259332004bf71593320269c31593320269f30593320347f76d53320047d76d533202e3e64d53320063d64d53320047f76553320047d765533202e3e64553320063d64553320065d65d4f320365e6554f320055e75d0f320055d75d0f320069d64d0f320071d54d0f32005d671d0f32005d571d0f3202e9e6450f320071d5450f3201cdc7358732026d4315873201cdc73583320055d74997320055d71997320055d70997320065f76597320055f74597320055f71597320055f70597320055e75993320055d7599332005d67199332005d571993320071e75993320071d75993320271e65993320271d65993320771e52993320771c52993320079671993320059d71993320079571993320059571993320069f76593320071e75593320071d75593320271e65593320271d655933206f1e525933206f1c52593320059f71593320269c61593320269f60593320055f76d53320055d76d53320071e64d53320071d64d533201d5e72d533201d5c72d53320055d71d53320055d70d53320071f54953320055f76553320055d76553320071f74553320071e64553320071d645533201d5e725533201d5c72553320055f71553320055f70553320055e75d0b320055d75d0b320071d54d0b320055f7550b320055c7550b320071d5450b320055e75987320055d75987320059e74987320059d74987320069d6498732026d461587320055e75983320055d75983320069d645833202e3e64552320063d645523201d6c72552320347e76d95320047d74d95320065d73d95320047d71d95320047d70d95320047e76195320053d74195320363e74195320047d74195320363d74195320043d74195320365d73195320047d71195320047d70195320047f75591320347c75591320047e76d51320347c76d51320047e76551320047
  | 20 => 0x1e57325845201e76325845201e75325845201e55325845201e74325845200677705845200676705845200675705845200674705845201e77205845201e76205845201e75205845201e7420584520047f745805201e5f325805201e5d32580520047f715805201e7b705805201e7b205805201e7820580520067b74580520067a74580520067974580520067874580520067b73580520067a73580520067973580520067873580520067b43580520067a435805200679435805200678435805201e7b725805201e7a725805201e78725805201e7b425805201e7a425805201e79425805201e78425805201e7b325805201e5b325805201e7a325805201e79325805201e59325805201e7832580520067b71580520067a715805200679715805200678715805201e7b215805201e7a215805201e79215805201e78215805202e3e74997420047d719974202e3f41997420047d70997420047f715974202e3f41597420047f70597420363e655534202d3f76553420063f765534201d3e725534201d3c72553420053f71553420053f70553420463e60553420063d5458f420063d545874202eb7415874201d6e72d524201d6c725524202f2f42552420265e7598e420265d7598e420065f5498e420065d5498e4201e5e5298e4201e5c5298e420047f7558e420347c7558e420065f7558e420065c7558e420065f5458e420065d5458e4201e5e5258e4201e5c5258e4201ecf2058e420763f65d0e420269e63d0e42005b571d0e42024bf7650e4206e3f6550e420047f75586420347c75586420047f75582420347c75582420347e76d95420047d71d95420047d70d95420047e76195420363d74195420047d71195420047d701954201c7e76d514201d6e72d51420053d75951420363c659514201c7c765514201d6c725514201cbc76551420363f765514201d3c76551420063c765514201c3c76551420072f725514201d3e725514201d3c72551420072c725514202e3f625514202f2f62551420053f71551420053f70551420463c60551420063d54d8d420063d54d8542024de73d8542004dd73d854201c7e729944201c7c729944201e5f329944201e5d32994420047d719944202e3f41994420047d709944202e3f435944201c7e725944201c7c725944201e3f425944201e3d425944201e5f325944201e5d32594420047f715944202e3f41594420047f705944202e3c405944202e5f5498c4202e5d5498c4201e5e5298c4201e5c5298c4202e9f4198c4202e5f5458c4202e5d5458c4201e5e5258c4201e5c5258c4202e9f4158c420063d6550c420269e6350c4200e76759844200e75759844202e77549844202e75549844201e76529844201e74529844201ed7329844201ed5329844202eb7415844200676755844200675755844202eb6745
  | 21 => 0xf54590520363c54590520363e75590520363f53590520363c535905201e3f525905201e3e525905201e3d525905201e3c525905201e9f325905201e9d3259052004bf71590520363f51590520363c51590520363f50590520363c50590520047d76950520063d649505202e3e64550520365f5498c520065d5498c5201e5e5298c5201e5c5298c520365f5198c520365f5098c520365f5458c520065d5458c5201e5e5258c5201e5c5258c520365f5158c520365f5058c520063d6494c520065d6394c520063d6454c520265e6354c5200eb6749845200eb5749845203677549845200675549845201e76529845201e74529845201ed7329845201ed53298452036775098452036775158452036745158452036767558452006b67458452006b5745845203677545845200676545845200675545845203674545845203677535845200676535845200675535845203674535845201e77525845201e76525845201e75525845201e74525845201ed7325845201ed532584520367750584520367450584520367b549805200679549805201e7a529805201e78529805201edb329805201ed932980520367b51980520367b50580520367850580520367a75580520367b54580520067a54580520067954580520367854580520367b53580520067a535805200679535805203678535805201e7b525805201e7a525805201e79525805201e78525805201edb325805201ed932580520367b515805203678515805201e3f745905201e3e425905201e3c425905201e5f325905201e5d32590520047f71590520047f70590520063f73590520063e73590520063d73590520063c735905201e3f725905201e3e725905201e3c725905201e3f325905201e1f325905201e3e325905201e3d325905201e1d325905201e3c32590520063f71590520043f71590520063e71590520063d71590520063c715905201e3f215905201e3e215905201e3d215905201e3c21590520063f70590520063e70590520063d70590520063c705905201e3f205905201e3e205905201e3d205905201e3c205905201c7e76d0c520047d76d0c520063d64d0c520057671d0c520057571d0c520063d6490c5201d6e7290c520056d7290c520063d6450c5201c7e7610c520047d7610c520063d6410c520047f74584520063e74584520063d745845201e5f325845201e5d325845201e77715845201e77215845201e7421584520047f705845200677745845200676745845200636745845200675745845200635745845200674745845200677735845200676735845200675735845200674735845200677435845200676435845200675435845200674435845201e77725845201e76725845201e74725845201e77425845201e76425845201e75425845201e74425845201e773258452
  | 22 => 0x8a530247c76551530063f64551530363c52990530269f3299053004bd71990530363f51990530363f50990530363f54590530363e75590530263f53590530263d53590530363c52590530269f3259053004bf71590530363f51590530363f505905302e3e6455053026cf32588530367751584530367b505805302e3e749974301c7e72997430047d719974302e3f41997430047d709974301c7c72597430047f715974302e3f41597430047f70597430363e655534302d3f76553430063f76553430753c72553430053f715534302f36615534302f3561553430053f70553430463e60553430047f7558b430347c7558b43024bc7458b430063d5458b4300e76759874300e75759874302e77549874302e75549874302ed6439874302ed543987430063d545874302eb7415874300676755874300675755874302eb6745874302e77545874302eb6545874302e755458743006b5545874300635545874303eb6435874302eb4435874302eb4425874302eb7405874302f1f43552430047f7558a430347c7558a43026cf3258a43024dc73586430053d7595143024bc76551430363f76551430063c76551430071f73551430071c735514302e3f635514302f1f635514306d3c72551430053f71551430053f70551430463c60551430347e75d89430047d75d89430063d54d89430063d54d854301c7e72994430265f32994430047d719944302e3f41994430047d70994430263f43594430263d435944301c7c72594430265f32594430047f715944302e3f41594430047f70594430047f75588430347c7558843026cf325884302eb741584430363f54593520367751587520367b50583520063d649525201d6e72952520056d729525202c7f765525202e3e64552520063d645525201d6c72552520269e7498e520269d7498e520065f5498e520065d5498e5201e5e5298e5201e5c5298e520065f5458e520065d5458e5201e5e5258e5201e5c5258e520265e63d4e520065d6394e5201d6e7294e520056d7294e520247f7654e5201d6c7254e520053e7414e520053d7414e520065d6314e52004bf745825202cbc745825201e3f745925201e3e425925201e3c425925201e5f325925201e5d32592520047f71592520047f705925201c7e76d0e520047d76d0e520057671d0e520057571d0e5201c7e7610e520047d7610e520047f745865201e5f325865201e5d325865201e77715865201e77215865201e7421586520047f70586520047f74582520063f74582520043f74582520063c745825201e5f325825201e5d32582520047f715825201e7b705825201e7b205825201e7820582520047e76d515201c7c76551520063f645515201e3e529905201e3c529905201e9f329905201e9d3299052004bd71990520363f51990520363f50990520363
  | 23 => 0x20034002000000001003200000100080000020008008000000002000c0000000030004002000000000000e009001000c00000200180000000000020000006000000001c0000020018008006001001000000200000180000000020000000002005000000800e006001000000000100100000060000028000004000000000400000200180040020070008034000000002800800e000001000400200000000080120020038010004000000800c000000000800000a00f0000008000018000001000e00a001000800600200d800800e0020020000000001000800000001d002001000000100080080000010018000016004001000c0020000040008002005000002001a0050008000000004000000c00000100080080040000000004000000005000c0020000018038000004000800c01600000100200060010000020006000000000001a000000000400c002000800c000001000001c00e000000000000400200000000040010010004000007001000000c0010020004000001000806400a000000001000a000001802c000000000801400200300080000000020000020000005001800000000400c800800000100000100060040010004004003003001400000100400000020010018004016004001801c000007000000c0020000000030004011001802000200c000000001600800080000020000018030000000001000c000004001800c004001000000000600700400040020000000008000000001801800400e0010010018003001000c00000400480000000030028020000001000800c0000020000004002000002800000000100f001400e0000018000000006000800000400000000000000000050020002013000000400c007000000000e00000080300100000008004010000004000c000006002001c00200300200100020010018014000000001800400200100280000040020018010002006000000400000f000000001000302c7c7558f5402c7c7558b5402c7c755875403677515875402c7c75583540367b50583540055e7398b540055d7398b5401e6c6298b540063d745875401c7c72587540047f705875401c7c72583540047f715835402d3d76d52540363d76d52540053d71d52540063f545865402eb7415865402cbc74582540053d73d91540053d72d91540053d71d91540453e70d91540056e7298d540056d7298d540055e73989540055d73989540055e73189540055d731895401e6e62189540057671189540057571189540057a70189540057970189540063f64d85540063f74d855401c7e72d85540047d70d855401c7e72d81540047d71d81540363d749945403677515845402eb741584540367b50580540363f54593530247c7558b530367751587530367b505835302c7f765525302e3e64552530063d6455253026cf325
  | 24 => 0x4003000000801200600000080000130000000000000004000c000004002000000000900000000080000030008000009001000801a0000008000002000002000800a006000800400200000000140000030010004000000000000800c000003808800200000180080000020000008002000000000400400000000080000050048004000000000000c004003003000401200e00000140080000000010000009000000c000000005001400000000200000180060000000000004000000000600000000040080120038000000001001000c00e001001000001c000003000400600800000000000010000000002002000802401e0030040004004000004801400000e0000004000004002003000600c003001400000400400000020020028000012002005800000000f000803c018001000000000000100280240020030018000012000000000800c0040048014008002000800c002009005801c00000000600040040010000004000001000000800000500080040060080010004002001000800c0000030000000002001000000c00e00700200140060010020010000004000006800201100000000060020000010000001004001c00000200000140040040028000004005002000002e004002800c006000005002400c00d000003400a0020018000000000000000802400200080180140040020034002000000000800000100000000000020000008018002000001c000004000003000c000000000000a002003000400e004000002c016004000001c01000200080080000020020010028000000000c004003000801c00a00600100000020010008018002000000800400000600200180120030028004000000003001000a000000800802a000000000c00a0010000008010000000001c008001000000000800200000080040150020000032000000000000000900000040000020088004004002000000000c003000004401a002002800800000b000000000200200300000020000018030006005006800c00800e0020050000003003002c00200000380000080040008054000008000800401200900080000000010038008002002000800001600100500000020030018000002004000000800400100100080240000028000002000000800000200300080140000000008000024002000800800000200380100060000000014000000008001800a008000801400200200080100000020008000000001000801400000b001800400000700000000000000008000002000000000000e004000800c00000200080000020000070000000002000800800000200700000000000000000000001004000001c0030018010002003002003800000200000000040000008008016002000800000000000000240020000018000000001000000800800000080000300000
  | 25 => 0xd7200584c80000822ad3435124ab615ea518d780006a68ff53c24c1000078c0000000001cfc0000000001ef80001d038a1960ecc64100017f8112d710018000000d5a00000002c8000000189927cf4400000017fa77078e0000c2e0595758000438e635c933e439e0000000001cb0f3c0000d0000000000000000000006ac92b1d08000345804cac03af6208001b301250000001d2297e0002cbc0003042a880000005b300000000009d46e393f4000a5d39d000168c0ab00000000000000002b240001b946980009a66d770600000003434be8000a7a4400000000000f3138ab680000000000000000000000004f58300141eba01d75cb031fba5ec95243969b21c03ec0004bd032d6924485e9000000000041698f065c000000000164051a6eeaa49750de721f800000000000025f184279b0000f78a94000000000047801c4a41c28ada45f5e800006b400023d26edde6b737730e30e9cd5f0ec3bf45d643804d8950e760001a5000000000074c0000000000000000004c0006dcb89d768e1d3f0187da6a3844138f11a940003e2af800000006958f640003a91ce894c00000000e8fec594000000207800069978580000000000000000f748150d53c100006ca4dba6adda2b0061800007acb3800000013fc0000000000000a33000000000000000029ec00000078c06a000000000011d8000e790002c38000df357d00014640000000990b7826306cb550ea087a000000000000072e00017ee0004cd0001412da22310001e58647764a0b0000000000000000028e00000000000000ac8ad000000000036b517600014f000000023700000160020028000004001000000400000000200240000000010000008003000000002200a000000400000500180000000040000010002000005801c0000000018000000001002002000400b000002c00a0100040000024006000000400800300380240000010008010014000001000400200100100000060000020010002000003000c000000000800000200e000800000c0010060008020009000803000400300400040020000000008002006000000c0000000010004006001000000000200000000100040040010000000002000002000c002000800400000000200000000010000014008003001803400000500080000000000048004000005000801001000b0000014000003000001000400100100200060020010028016001001001c000005005000000000100100080000020000000000007000800401a000005000001800a0000008000003000000c00000100080080020030008000000001006000404c0000010000000004002000400400300100040000000008004000000000003400600000000180000000018004002002002800800200b00a800c004005000001c002000000800c
  | 26 => 0x7bc3cc000000000000000000022080008ab1f901ec470e2f17428c4a4200067b2c180000a35402ef562a9f71fe0f7088cdc154880009ae4c40002b4dae60000001f01e3e000351240c000000000000174ce7e3c288f9732000000000032e956000195c000b7d00023e029c3ed0000c70000bfe150a51d6e42ba68900015583b61330000e422f84efa6451140000000dcdcd6d294aa34bc00068c0900000108d7f46000019f800001a1ecca5600000000000007010bb0001bc60003c200000003622a73420a2000057922c04409166d5800000000072c88343fc669239ac91bf4dd100000000009d945194a91a825e6478000ae2902284b27544036106d3dd00001db791275942ad8035a01c424e000124a59893400000038cc0001982ae02505444e62373549bd60004b01131342e7a61480000004590000de80000000000ee538eae6412a9dc4106dd5df28ac000af40000000000e08000000000000058f37ec1f6000763000000000063084f0eee14d7121b1c00000032ebc3c0000003d8000151e00000003200000000000cd8000b3036b054cc5e5be55e92f9df8bc500024cc00000057617d00000006b6ba9caf45cf000000167815e0489c580000003fe3d20000d9a55c000000086d234218577077f000000139e5795fe0e6c000c172299f1d3e49ed0000000000ea50003284000d5516598914080002f38000c2a00043618416820002f90e2c8405d2316b4180000004751a2800000001e8000000000000000146800025a8000000000000000029881a50800000b800055980007fe72c5d4bbc8adcc2864d8eac1da00047280006108d7000000000000000000019a60003b2969c0001d4350a98c996a0c631a365a045f90001bd968e04c3e6bd418c0d5e27b1720f1057c57b26e8e78a987bf000060c0002b634ece08e2d000195591c000285937800000050b39540006d375d800106ac6c00006759ea2b5210aef04660001af1f1810a8e95262a8c34ea0657433e85be30d0000000000db345fafc000054d0001bd03c00003340000000ce30000000000000000004000092d5990000000f4c79389298702464723338434b540000000f48000000000000057455900000001df07a91c80000000002ad4c7a000000000192280c32900000a035b5ef064400000000029f4000856501000189e0003938b612e80000002c31116d2000037603aeb9c364904947c000000000000000065180019126b2204a5bc5780000001851656ad43073908c402613d600000000c15238000000caf00015008d800045513080002f96ea80000000006ed00000000000000000000cca0a43db0000e1100000013a400000020e82caf6f000000000055700000000007cf491b8280000005968001f0600000000000000004aab128000d210001fe800010f0000000ea4
  | 27 => 0xae0460f8b15ca060d0000000000000101940c0000087110000000cbc61380000005a033c0001e4a0000002178000a1237f877400057f6f32cd85520000e50c8108a69572680002f6eed3fb80003200000002720000aaf7278b0122e0006330000000000178800000000000000000000002648000000000000000000000052700001604601269db8000efe000000000000000024b8000378000000000006c13e1408dce42c26da5dc2e820b0000000000b3a19686d8000000622157c88e0681023bc19987a05ad079d3d48c828c31640d4758203bd4c27cb4e4f31bbd34a1de1053e257fe4bd3d7a7e1b9a2fe059000000034f0599a9839c0003fc1479c26c4c00003ac0000bb0000000df468d0000000244b4b48d000132a00000000005c85c100025d892ab6a71622f8d207d65b714700009b50003a89b4200000009a53e0c080000001dea4a46df80000002213a3b5dcb740c30001c880885930bd07c110a1c115b1195b2439e3221bdc000b09000358d59e69716700000e40000000000000000000000093000056700003249a600000004de8a500014382fea7800027f17b000016a9c91892be40a3ac50000ac434a0b3170c0002ce90040000001950001bae00000022382209960003a90000dbe36e17400008491590b1c09c9dd56eb69400000062c00002249e24013d94de6e3639986900f20000bc8a190b4dd42868000b94c5b0002f88000eba1228184558e3f267a4117dc3c81c718155f85855caaf2922a83c0000b1904600065b01f49ac89e189800067856a00000000001180003ae42844d43e08dc128028028019080000000000001ba04862c218a58fea196768eb48560000000498b02ec0000068dec02a3000000112a000000000000084e0000000d1200061280000000005a680017a600016eab8d386c3f000000000000031b0000da200000000914a8c1c50995648faf7b2e6861db1400049321e401af6d000124d0206e60000000cf40005a50854c54e326408000000803000388d512ddb4dea3a091c0003dd8f4dba40003af80019542874a200146cc0007469c40000cee000000000000000013380000000000000fa200000000000000000000001d50e8b362b5a0000ae71ae000034a000746000020c9a4471abcc0002677172a992cad9375b38ecf1e3d876380fc0000000f28000000b3900000000004ab00029280000001d7344c07200000000000000001fa828846200000000008480001eaa0f8e6c00072f0b6841286a18590387c0c8200034246debcd000366c000000000000000000000000000000000288000b5e82a1939d800000000000000000352466000009200000018254a0d2c0000000e4000000300002220001538000d8000000005f000000071b901936600054400000000000001ba80001680000000000f4d765
  | 28 => 0xd8001746f05000000193e9e82e710c129800055f00010624ed4a70000000c430000000eaecb245d00014bc00000000000006590000c08ab600016b2f1c00025f2458a2400000005f800000055200023718324ea404000000000000011ac00091900005a4b2800055d8001c9825a4e080006b00001fb0b6474400000000010288f700035a5ef40001e62701182ebe0e2ac745fe65c000237d62085f0001b21636d310000e24000000725bb7000093450e075531e71b0001050532b5200010c4000b821731edcb32000000000145ab453eb9d18a1e00017b297101a8e00899b60efc26d13c80009046fe00002a07668ce2cc094930e45609ba50ddb402d1450f85dca3a666d000000000000000552100004a4800000055e13a00000000002aa00012781812ab0001bbc00000000005d2d6a0000000b6cd577aeaf98a406c60e30db402c95c3d719fd73aa9e63ba718356a935b3000186a0a71a3b23127216178a17b4e880c272fb7b15f6eb41aeb0edc68cd63762231b485e85f2a9c86c01f73d594911e46843399ad800011400000019601ea0002680f3400000000000ba0000001ed00007ed5588784000c70539b8380f400041985c40004a8000116003c0003f5ba6d7a2bf90faa1645227720001860064a560000f0400000000000002da0d8000000000000006dbc48f4400000f8000000bcf0001184000000343800153e0000003a1d5047c450d29e4c008a02701b2c0009b22c786c0e4a3ea24a2240ba2000000224c8da00000029a9e6e180638bc7800000005b2a5195000004ea0000000000000000000000018000000061d7a33cbd9be3694baa8987509d100018e141c39c6528e4500a661294966dcf60000000000000000000000000000025c000000000000000009740007a280010900000001458f78f7c38f02b0c5ca0a000000013e9c46099bb890090e1d621040000002960a69dfeb3b78bb6341dc5431df024cc7476b2c90000af630075f91044ee2161a613ccb9200035400011a2bf800004a04b60000002b7c00000000000006ac5db00000010e80000f60001af800000000005ce000000193cd0c000000000048222e44409c80000007838f50000d410000001c2a74c4f210e8d7c2a60000435580000729b91d814d7b0003b054608b5228095c000c0700000000006a0642b6e800090a00012894c0a0145c1f681143413f08000e960000001a588cea4f729347c000cde14110340008535539781502a374f001d084e8c900031b423e0006ab1f64c72cfb00026106ae50541005d599298a58b96e4bee0003e1a639db6ed908700000000700bf22c800000000000015c2da633281fc1920004200000000000000290400000005c0000000207429189cb565ff04917c5e1a8683caaba46426fd48c0fac8168a900028ec8bce160c780000e
  | 29 => 0x1200000000008f200000009ac0c60000000000000a871210000000000103000000000038d1b38f96457394a945d0a49629d84e800022a42880000004524560000ca00000001d08fa40000000764000a595432fe9478ee06b318dc000000272000053ae19720b85d3b462c45980000000000000001b0e6a55230001a88d0714a80018060003718001ccc0000003b11e7e000297ba5882e000000134800060878b0000058e3e3fa0001b1c0003a2b2f52c480f00000019380000000001bc000018b8001d86bf50002129a284f816db21dba66af6e1907905000001418ad0f80000fd000000000000000001d49b80002065cea3ce4940540e166822c88000e8600023d8000000ef800029b87867ad00033c939c2f044e25c0bfacba688831deb694f2c4048476848a00000000000006a2930c26a24b00022c400000042e85600000007339a157867aa73880004b0ba02f7192d44299f3daa50400000000016dc0000006ccad7400000031a8000cb4ea600016ec510ee77b980002ae00000019dd8dc000349800000000056300006e8432000287800000000013180002be0000000000b5b00007ec0004e35b21e851009d366414f00000000000cf8000ac345e80000005490000f880000007a880008440001688194536df539a0a480004645fa0f080000000000000000000361a4c91fa0003198001024f580003bd1d02548537a89016a31d6510000668d6b0000000000a7534082e438e0000000000000000184800089c87b673a4485ca2bb1540084ba6b8f3203d71d0058b1bd9de9ef0f0c2993878b4a8de0000ac10e20000000000dea19c000000176a00000000000001da00000012b60001f8313431a0007ab00019d8000000022d37e0195822170da40005a7810800000026680000003f100020f40aaaae00000000006e80000000000b8d0000000000000000163986eefa13f0000aba53f00000016980005b1b0a8db256702b96d5598707585bb7998079e0d92bf44b2ee86b22018f287d31c300000000007080000000ef6757847942e53e45703d847ec0d5b12bc00001af5179ad4e0ccbe3ee1fa98c8ac157b800000064e3faba5048e0002998679d520003680000000eae0000000f300002b283716aed5800013554285865af800072e0003f335e0000a081770000000de200034582163e668e3cc8000c963d38ac4c3885b00019d56aa49100000000000000000000000d6e536b340312131000000000000000012e4000d657c40001dbe000000362c734a1f00008500007bf00016f400000077b800000000000025b887a000000319c0007e20000000000000007000076000062bb118710e9527390100000000002ca4000000000211c0003c500000012da08300010d9a16d1000017855a2d180da1be00002222b9a948bb20232ef9d751940005d
  | 30 => 0x336000023600000006d4b331eea0e0456d8655093b97ce3371d5269c0006b300035e80003bb61580019f000049b1708398a22663800198a24f285104400000061d0db94ec99807129d152ea533d1af7c8b469d55b8d08ade2c164ab7d174ec6553880000006da22e000000018b480800000006f6560000000e6e0003088000c52483b48801ed4f3610204868e9908d266d14890b0000219820f092b127b89b400060324a53620000df2e403f89000000001e600000461a6000000059f8001c8600011900000003f30003710000000000264859246a10780000000000002aa00000004e50000000000046a68800000000000000000000003428fa872a0002b289fe41d0b03a280005231e00e288e000000002700000000000d202823b80000000000ef17382dbc0000006c83c2051e0fe263b27981246f70c13d4aea41c0002cdc6fad50661b4dc0000000000001568dfe2ed000000000038b800000000079180000008993768294cf20001c12fa0000b0d3ba0b49b9e000000000000000000032c4b460004c623540002f52d60ddc0d22cf0002e2de823e51a589405fa0d65e001dc0c000036680000000000000001c500001960000998a9d0e68e91890f75166b8e0e90b7a01f1689d1211b0ab1cb561431500016e0b380000002ee9e340003ff00005c073028a21900000005d62110c4a0000000001d34d7563a00001620006a334e0c144c85838000a0e00056939a0602c92702aefd7d60007b1a35809aa7058900002125780000f2c0003e840e8470b860005b611d000076903300014229e3000187800e876199b714ce0000674800000000006eb4b97c21cb453928464a4b462e01b5ce800040b800000047c00000016d68220f4b2d0daaa0d41db33d4b0df660b03000440007941b6c0007ff3550000f4a9612f59db4f1200006227fc0001c03a780000006e969ca194c504350568000bb800000005f58a00003558000000000000000000000062000000000000001020000000000345c66a0df0000bbc5202d000000000000cf0002d655400003bc335db78ce40001ab512269f000000000000013f820080600048f80000000001c914d483000000000000000002b20ed40000000001c4c7a2b2c0000000000cdb00000000000000002e311d800000000000008162440299a5a4232aaa47040ad266b7aa58fe60000d68d3817ac1e79f00016c0b9e38931e0f940000b3038c4b83db0002398000728000236c000345000112c3ac0000d3000000000000000000126e5000127c4860000000000154f2b08bb61065eea369529fcf3a73947a3d7c5e600000000000000006c60001ca28cd00020851b031a5cc03284d00013078b79240052079893800000000000012626010000001cc400039c00000305f00000cf498a000000000000017358400011
  | 31 => 0xcc87765bc1db00008c77430000000bce641a9ac6a00006d495600005e50002c155b49730df83300740007508000ede00032680015e200047a800000000000000000007370000000556c3d76a000020ab9b3aa21cca5c000562800006c0000000000000000750265c400000000231818a00059f000000000030b07a0ff604a3d3256063c67604b0001602a5b4e49d4c22a9240000378a4a1990003a4000011905a0e940003950000001d980002e000000000000230a10f1a0172d4231102612306900000008605c38b0d1de4df00000001ee0000000000000f350003220000f81000000000000000000003a20000002218bead5b6690ab9b2ebb354c9c8c0000001de05140000000003154dc2e6a00000003e4c140002ab400000074e80000000005c7000000000006a8000000bb144c0000000c6b000129800093b7249d34d5291067b8000dbe64829380012fe00000000000007d83cb00019feac72589c01b6000000002a4000000000000004021b53480016ee66600036ed2700001918ff99a2930171000121800057aa8b03a4d0c00029e895e07c6538001b2214a4828000516bd60001e48c36380240ac69ab8e4a4eb8000000c8a0001978000c680000e3d19e0000aa800096e0007b080001d00004b91015662f1304b80000000000001ee4000a1871a9dec000cc64960000000000000000000075e3782600000c330a1853dcee0956a9b6c52ba6ac0701d2400000003c00004222c84e1000000000000002400003bd000000174200000000000008343ae2eb40004f261a25a0e4cdb400013ad88a40a3f71231e742101afa0d80000000003ab4000cf323fb3f9e9e00000003c56c25ec050800000000031f80019e800000000000000005ed2134a6c0000c313a13cab917760001e843990003d38f9875b2cd21f58249ef1e680002760a000027c40ec00000013bd7440006071a780000000000cecb6460739eb900000cad3110001cfe0003288bc80000000000000000000790000000000075e1d580000000000000132aba635058c00000000038f56463290003d2d6880290bc379506e0000000001daaa3d0000001d1c0002221cf901600000000000000000fa0179a90000000000000000000003bc00000000000000000002133364000b8800000006ec7990000000bba60c5db80000000002fd8bd03580002b4056de32bf6382b8245ae0000001fb0000000241b7704f02a07953335e041a16742b6d0aeeac00021998eaf2169e00009ba21f3aaaf5dc023223c998455de5d700019f444c570000286d3d600042321304e68260b8318989c000755866cd7e1b12cab7a5e8081b171b3800004d17478dacb624630000104ce21401a208e4000d4e4b20001c9c0000b600000000007bb1455926f2e53093ec00000000000004260004ef00000000000
  | 32 => 0x12e800019cc2d000254c74e00000022040000000000d64a6ef43000160d2d40001a480017284bb0000f90000c7e00000011fe6de122000088600a5be0000000504128b894bf047e1c6bc75dd222f0003b2c76e00000008ede4c8e16d62755cb6000000000000000059a907c26683f400800826c31b4a909942ba1f35b8b439eee0000002a6c0000005462aac00000009220457c65465151e08cbe77d00024fc47441544239c80006916d73884a247dd5ba8c41cae41349e88d0000000000000000000000019a80000000c29135b6e47500032fc92e00007cab5d52a0000001ab938a4ca3ad2e7c95adaa25980008ee93a000000000000044b2770000b280000000b884d9000281400019a47f000136099d0001a9c9f29cc000207c0000002128000000499081959800000000034c072000040c0e0c0002af6c4b7e43dce600002d000000000001ac10484f16ef8000ed00000000000f0c00000004bd70a1e24b60c44b960fa2249394becb670000fe0000d820001cb8fe036300000000004c00000001afc00022a000000000021400006561622078a30a189a301394e025a0004b38000000cb52d70000e0441911ea6b5ed6000033b4fcc06c840000000f14d850c2123c05c7ef175106c000000000000181e0004f480013e80000002fc8000000691a0246aabb90002f2400000000039200a8ed00003044c080000000000000000000283dac0c7c00000000000000000000000bea00000006a85172beab40f7a34d5720b716d00001b2288de76b794683adc7ce5b4662000000049b7c1144c23aa0b02c00019763f46191cd53f66cf6bca8fc0000000000001c560002f339d8f0e00075529240002a575a80003a60007af0000e94f690003700000d5d7a4800159a40068eb49157e9425d7afc50dce1b0b7800000030500000014740000c9890000056b000000000000076692415082ed00016b5c4c05f6929b505c213400035f4762be965305ad4728f164d38680005e92780001b64b165200001cf8d886c79b8800000000022e49780005932fcc63000044f8428cf884f1011361a32ad91381fc80000000000001c4021e5450ae0000d96000358400063022a81f98fa0005f63455e706e00003b580000006db0804cde6b1246913cdf22f77c01f9d0de00065731680007327bc9e3056e0005ee0001952a2800000000000000000e85712000000000114c0006d400a8000000000000000059e526bb200000003f1a3d9134a1d0000cc1b948f000033bc000000000198c0000004ac800000000030c85b94ce31915509c552000068d3a20aeed492d480018f6000000000000000000000018ba0003888000b4ca625d9198800024c1dd3bbc00083900019594ca16a00000001a000000000001ae000000292d654ec2000165cf9cc8d30900018629510d4b5d0
  | 33 => 0x40000000002da4c460000000fa40000000000001358b1c5e10001a7c5de0fc04e184c000000087400098915cb055a00ee37b880003140000003a5d0a8b1f43c264052833f7bea65129a5bf00000000000002a7b1d9920b810000001b065220001df12f20007b70545f0a58a00000000000003c817cc7400001610000afc0003bca6a44f620c0000000ee2000000243c5a8cdd0002b55cac6460000000000aea69d00012f0dce40230bc00000000037c57080000001211bac00000000006d800074f00000000000000048f3e00063d000148a65b3228d9d0d6df00000001e0054b64599240009e767800000000004c294c1378e9c0000001c16000276223c0005197aa0000000855000000000066b037151cece0000003261ce6a5f70900012d600000000000009710001d64ae428122d96c10640006ca93a40004330000000000b2144d9ee078e95a5e22b092d28c243b8000000bc600028958e615c00000000006f258897311f80004e82fbc3660001bf2f74000000000246c036c0c5af238800000031a000174a6b867533c4aec6604868001b4e00000000008cc0000801bc40002270000000f6c0000000000000d6c17e09a897ec2031db87ca681c80000000000cdc660ae0ca88e3c72d0955e0c8a80002528018b18319041c44a88d0000000000dc26f6a670000000000339572ec7900005dd0968d229c8860d10ecf00000015c012b54180000000041819c39142a0072280000000002a10000000aa9381a44c000e3910900000965c75c98e059c22282ea8c480ac64c1e7bcb4000224488ad45e686cc0ca0001d9c0001930ab521201a333800101405b24280010fc4874928001e2a0000000001406073000000000000000000015fc0370000001900000637800000002500000007466b73b9a25103830e351800126a00000000000008af0deb08d4aef6800019b59cc2b31c38318000af80001f4000000051727f400061a0002369e66b2e0000f7c11c000000011c0660000000000000ce20dc314c7b400000000000006c40000001cde0000000001eb245d00016902be36505ba54085e78b65c8001ae000000016840b40ff250079000000043aa60800051147d3d69e489880733791808ae53863cf4ffaae207a023ce3042e52aaf30288000008add9b387a87aa8000000c245ac17a985800000000000000000f58000318a3638f958c4c09cd44b85c9a1e8dd75e9d889b80000000000000000000034dc6200027e25140000000e201ac000b427ab80018a2116309911400000014b80016fc00018394c400000000000000009db176380161e416000070c35c2484fb08b0000a426e4800052c00000000017147610002ec1b96f110002dd05f40004c58f280000f2605b718000f6a634b7f493c8fb19c1dd5872e0235d8001dba7a97870000000b50
  | 34 => 0x27853be4062000600a6f800095f0000000a0c0000a30000ac21b500020c0000c2e6e63d900000005d5a6a000000060d9c254528ee2150709ec48b6252b25d14444a4951a3c7a428d79ca32d01c000234b10841ceb15ae27cd3320ec73e8001b70c3672236513f2ed80708000000000080abfc00000000000000000007308000000000000088da0a0006f90c2910e053000035130c0000dd961c0000000001f54000f86395abe57da8bc41595400000fc68dbacc8e28ed000220c0000000001659c60cfd47cadfd25e064027800000086905f2a38cfc7e800032dc000a6800000009c42c400000000000002c686890c68e700022b40c4ee4699b01551a68307296244c40003f2068050a10c32a3ca48a267200000010c4aa24c080d400063170380013266b933da57820812925b1a6d0fe00000034c800003c2a9b3ac000000643000042e69a329800129600068f0a6000000000009e80000001b92dc0a100001148000cdc00055c8000000e5d0003a7c728bc86cf1cc408a3ee000000000051b0000000000c1a52427b0c04a850002b704ea0001878c59a6898d00000007f2b7b000351c0000007068000e3837561f000000089d00016080000007348000f1cb430000000000000000034569085818613f8c7cdc80001cbc0008b70002b2c0000000000000bf40000000000548000000381800000000000010e4dff0c19fe40000003b1976019a9fa2581e458a83792f10001bee0005ab24780000e400000000001ed0001885804000000210d9280000003604a509f50c400018bc00000037f0730000681800005e76a0003ba895c6eb00024740007b14d780009c200053300006f80000000b4c7decd509fbe1cf9243e198929d7aa9b4000000068c58c3878dc5228a8b4cf02604606fc0000f246484420ca800000000041737e14c80000003dc00000000001f200004291a9800198400030580016440000570e5886e4fa2a6000000014b0003784000bfb000021c0000006820268000bd40000000000000000000173400055200e0f8400062f8001e8eabc000000000000000013415dcdd91990000a7436820107240009ae64cb290a8226e4abad4c0001f100000000000005b6b80d5dabd90000638000000000276026004000035440000a400000000000003a08120378000417a30c000c3c00017f00000000001a480000000a90dfc0008b400000000000000000000000ee26a19e5c25ccd417d82f04fa9213a00000df65ef70786e9cca2190003ae07c6000149aa95b3e0000000000c0c000000000000000020600000005450000001df6d4235d04a8000c47000000000000029686dc000e644628001bd01ff54d0001b3a0000000001e6c29f3fb39e1590a3811a8001956e5400002bd20c1f900038700000000ee2b600000000003dfdc74d670003b8
  | 35 => 0x4d5067c7a03280000000000e46096258c000000000000000071d0000000204b3d00000000000000000000ba8b023efbbb94d80006d79ec8a020002593b485387de5d52c4d782def34e1af47f40e960eb85180058012b0000000000021800136c0fd00026e43fa0006f70001e2000032189b00005e44910c7c57ef52762a9f000000020d1b91b6a4aa0000000f0668e3253c6d44ee93592859c0000006a029f82b400018a00012560000003a0976c6803b2000164e22d293249c000000000171800078119cb32c1e05c574902e870aa4300000ec0000003eda81cbacab000034044ecad61a8a72c0006740000001b4600021d9a9000000062586595bc9370442a709248eb0a49fc4b200000003d2878c0007b3800197000008421418e43bf433b5d8fd2d3d3c03b5c00000000038a97483ec27a3b4cea28291c98001306e2927b8000cd80007b900000000000000000e320005cb3281ac4e8319d2c64304dbd693947cfca43c1cf8001084d28386b9b5ecca3514191e15547084798000d820000000000000d4c09c96a800000000000ac00000000010400000e752d0001d6051d00005517005e300039b0000bcb5b280000000000001e71dd60006a5acd18ac0002448000b3e00024e90b40000005220001bd400000003e00000002b4800013c00000000017b60000000001e0600024e32cc946eb2780be100003b
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xe85624c941c4001c8aca9924388003a159132487100041fc32e9a86200083d8799350c400126b0ea0ea18801a0f61376552100041fc22ed2942003877865c4528400143b0932e650800287612654ca100041ec3ccba0c2000e49654c9208400107b09b82ca8800e1b20976551100341f43ec8aa22000a1d84997634400143b093aec6880021761e6518d100050ec24ca31a200085f87594634400189ccab90c688003135957218d1000627c2ae431a2000c4c855c8634400189ea8b90c688003135517218d100041fc22ed292200085d87d8e52440010bb0e31ca4880029360863949100042ec3ec62922000c1d74d8c52440010bb0e318a488003075d0631491000526c10c62922000c57635c452440018a8c6b88a48800316d8d70149100062c31ae0292200085d87997324400143b0932e648800217e1d65cc9100042f43cca9922000a1d8499532440010b90eb2a64880123321d624c91000526c10c7a8a2000a4d8218d514400107b0f32e82880022761c63d051000546c10c7a0a2000ac58218e414400107b0f32a8288002a360863505100070a31ea2a0a2000e1463545414400b868ecaa282880234c1c154505100070baa0c6a0a2000e155418d414400158b0431a82880028d61a755051000598c04eaa0a2000a37865d54144001868ecbaa8288002cce01755051000598c04caa0a2000b3380595414400f52d0db1a82880038599463505100070ab28c6a0a2000b858218d414400f92d0e31a828801f2561c635051003f0b428c6a0a2007e158518d4144001c2cea31a8288003855d4635051003f43410c6a0a2000a958218d414400fd0b0431a8288002a1608635051003f48c00c6a0a20058b487589414400f52906b1282880028d61a52505100070a31ca4a0a2000b3180949414400126b0e29282880028d61852505100070a318a4a0a2000b3180149414400f5290d9928288002a5219325051000742b1264a0a2000d31751c14144001723063828288002e8608705051003e4a31ae918a2003874875952144001c8aca9924288003075d363d41100060eba0c7a822000a4d8218f50440018a8c6b8ea0880024d61d41d41100070a31a83a822000a4d8218d5044001c28c6a0aa08801fa418d418c11000e583b2829822003878875952044001c92ca99240880026c21d4148110007c0992829022000e6165485204400145b083aac40800e1d605761481001c3cc02ec290200083f865d0520400785cc4ba0a4080020f61e64148100041ec3ac82902000c1d7498c520400183ae8b18a4080030b5d162148100061b322e22902000c35645c452040018acc6b88a4080031558d711481001e33312e22902000c65625c45204001874c8b80a4080030e59170148100062d31ae02902000c59635c052040078d4c4b80a4080031a5897014810
  | 1 => 0xb0932e651800287612654ca300041ec26eca8c600083d87997418c00107b0f32a8318003615c9410c630006c8a0ae018c6005c1c76551434c00192ceca0e62980028b610755883000532c08eab10600083f865d0520c00785cc4ba0a4180020f61e64148300041ec3ac82906000c2d74588520c0010ef0cb88a4180030d99171148300061ab22e22906003c66625c4520c0018cac4b88a4180030e99170148300061cb22e02906003c6a625c0520c0018d2c4b80a4180021d61c52984300051ac20a53086000a718014a610c0010eb0e292c2180028d610525843000538c00a4b086007c94315d9410c00fd0862b12821800e0f21d64553200050ec20eab1e4000b0d841d532c80074990caa26590003914c961547200044ec3cc7a0e4000e853258541c8001c8ac6a8a4390003a158d41487200060eba4c7a864000c1d7458f50c8001a1ae8996a1900020fe0574996200341ec26ecaa44000a1d84997328800143b0932a65100020f61376546200041ec3ccba0c400083d87995418800f52906b0a831002a8e60075d91200061bb2ae23224000c34655c4644800186d0ab88c8900030d61571191200061b292e23224000c34525c464480070f10cb86a8900030ed9170d512002e163b2a8a12400089d87193324800152b02326649002783148644c9200054ac08c89924000b0d841d53248001693003aa649000383194644c920005c2c08c89924000b4980d5132480014990caa26490002d2614704c920005c4c20e09924000bc1811c1324800146b02326a290003524c970d45200051ac08c8a8a4000a3581d95414800146b0232a82900260f21974d41200541fc3ec9a82400083d87193504800146b02326a090003435d132d41200051ac08c8a82400ac3876d915048013870ec322a090002cc604645412000594c20e4a824000b49831c950480016c302392a0900034add24254120005a4c1c84a824003c5876cc95048007a90e5992a090002d260e325412001e2c3b264a824000968874c95048001a970e992a0900035221d325412001ea53b264a824003d48764c95048001a96e8992a090003c2d9132541200078432264a824000d4932dc55048019870eda0aa090003c24cb415412005e1c3b282a824000f093250550480016930790aa090003c850521541200051c432a92024000d49754ca4048001e12a8994809000e1e219755012000694baa84a024000d49754c9404800186ac8b8ca5880020fe197414b100041ec3cc8296200083d8759052c400186cc8b88a5880030d5917114b1001c3dc32e02962000c3a645c052c4001872c8b80a5880022761e64ccb100051ac36a8a0e2000a378655141c400f52d07bb283880028d61a75507100051bc32eaa0e2000a358694941c400126b0e29283880028d618525071000598c00a4a0e2000
  | 2 => 0xf32d07500060ebb665a0ea000c1d764cb41d400146f02bb283a80030de0576507500060ebb664a0ea000c1d764c941d400162d07b8a83a80028d61941cc7500041ec34e918ea00083f8759231d400107b0eb2463a80020f61a740c7500041fc3ac818ea00083d8759031d4011874e0b2063a80030b592720c75000616b22e418ea000c657258431d400146b0ca0863a8003495c9410c7500061cb22e018ea000c71615c031d4001a6282b8063a80030759273c87500060eb22e790ea000e0d644cb21d400107b0d3a443a80020fe1d64887500041ec3ac910ea000a358650621d4001c1ac899243a8003914c961487500051ac328290ea000f053250521d400107b0d3a043a80020fe1d64087500041ec3ac810ea008c3a7059021d400183ac939843a80030759173087500061cb22e010ea00083f87590645400186ec8b8884a80030ed9170109500049ac0ce9992a000b15819d3325400107b083b264a800287610764c9500060ebb2e7a0aa00091d87ccb415400146b033b282a802e8b20976505500058b41ee2a0aa000d25725043154001a6282b8062a8003524c970c85500041ec20ec90aa000f0532505215400107b09bb2a2280020f61e65d045004c1fc32e92968003a4c8259532d000146b0332a83a00028de0565507400441ec36e8a86800ab0c825513290001c1aa8b1265200030755373586400041ec3ccba0c8007a9483585419000d07b09b82caa00030d59571d0d400041fc3acba12800383c87595425000143b0932e64a000287612654c94001d26412ca992800083d87997415000183acab9e82a00028d60665505400051bc0acaa0a8000a1c82551631000143f02aa2c62002287e015458c400450ec02a8b188000c1d54dc963100130790eaa2c4200268b209545884000532c08eab108000a2c87551621000145f02aa2c4200228be01545884004516c02a8b108000e0d549cd6210001c1aa8b9ac42000e0f611761484001e17312e82908000c1d7498c521000183ae8b18a4200030b5d162148400043bc32e22908000c56635c452100018aac6b88a42000f19989711484000632b12e22908000c5a635c052100018b2c6b80a42000f1a989701484000634b12e02908000c1f7558e421001385eeab148420003075d954cc84000706aa2c59908000c1d76551321001361904aa2642000383551624c8400043ac38a53088000a358414a61100014e300294c2200028de0554584400051bc3aa8b088000a3482551611001146f00aa2c2200228d60154584400043ac38a4b088000a358414961100014e300292c2200028de1642584400070aaa664b088000e15544c9611000183ae8b1ea2200030b5d162d44400061aba2c3a888000c1d7558d411000185aeab1282200020fe0574996300341ec26ecaa4600083f845da528c00143
  | 3 => 0x2b006207e9283505600c401d2306a0ac0188038c94941580310071829282b006207e9332505600c401d2264a0ac01880e0f21d64553210050ec20eab1e4200b0d841d532c84074990caa265908022761e63d07210041ec26e0b2c4200c35645c7548840113b0f32665108024d61370546210051ac36a8a0c4200a3786551418840f52d07bb283108028d61a75506210051bc32eaa0c4207c9473505608840107f08b86ca908320fe05741952101c3a432e3aa2420683c87591544840143b0832e649080287610654c92100586c20ea9924200b45811d5324840161b0832a6490802d1607544c92100526432a89924200b45851c5324840170b0838a6490802f0600714c921006c2ba26528a4200b45831c951484016c300392a29080f151db3254521005a2c1c64a8a4203c54764c95148401a8f0e992a2908035121d325452101ea33b264a8a4203d44764c95148401a8ee8992a2908024d6137054521006a2996e0a8a420083d8719741484194690ca8e8290803c14c951d0521006a2baa6520a420b83d87195414841746d0da8a829082ec9a0b515052100782996a2a0a420ba34865454148401e0a64a8a829080e1d2197550521006a2baa64a0a4200f07544c94148401e0aa8992829082e8da1a755052105d93414eaa0a420ba34865d5414841764904baa829082e4d61c655052100692baee4a0a4200b85831c94148401743003928290802e160e325052105f8329264a0a420bf04524c941484035490c992829081fa1e1932505210074243264a0a4200f07854c94148401e090a9928290803c19d5325052100782baa64a0a4200f07654c94148401e08ca9928290803a14c941d81210041ec26e0b284200a39849d5600840183ac939ca5a8003075917394b500051ac0cc8a8ea000a3681dcd64d400146b03b9ac9a80028ba0a735935000516c14e6b26a000a1e839c964d400143b07392c9a800287a0c72593500050ec18e4b26a000a36811c964d400146b02392c9a80028e60072593500050f41ee2b26a000a1d83dc564d400183d07b8ac9a80030760f71593500061ab24e3a1ea000c35645c743d400183ac939cc5a8003075917398b500060eb24e7216a000c1d645ce42d4011874e0b2085a8003075927310b500060eb22e6216a000c35649c442d400186ac8b8885a80030e5917010b500041ec34e9996a000935819d332d400107f0eb2665a80020f61d64ccb500050ec24ed996a000a55819db32d400143b0d3a665a8002c560674ccb500050fc3ac9996a000a1d8759332d400143f02b2665a800287610764cb5001d26412c8996a000e0f8259132d4001c1904b2265a800287e05644cb5000706b26e4996a000a35819d161d400146f02ba2c3a80030759273d07500060eb22e7a0ea000c1d769cf41d400183aecb9e83a80024761
  | 4 => 0x35040126f02ba8c6a08024d60675d89410049bc0aebb12820ba2c82595625040f32d07b8ac4a08024de05769494105e8b992e3292820bd15325c6525040126f00b8ca4a08020fe1970949410049bc0aec292820bc1f325d8525041783a64bb0a4a08030de05761494105e1b10aec292820cc36865c4525041786b0cb88a4a082f45cc9711494105e8a992e22928200937805c45250417a3664b80a4a082f464c970149410069940ae02928200d31815c05250417a6442b80a4a082f4c485701494102c5ac0ced9928207c94315db325040126b033ae64a08024de0575cc94103d4ac0ced9928207c94715db325040162b033ae64a0802c5e0575cc9410058ac0ccb9928200b1781597325040107b0c3aa64a080287618754c9410058ac0cca992820bb0c82595325040162f02b2a64a0802e4600714c9410060eb2ae7b0a8200d16659cf6150401a2acb39ec2a08026560a73d85410049ac3ca5b0a8200d167394b615040126b0e296c2a08028d61852d85410068b398a5b0a8200b318014b615040f32f0f996c2a080265e1d32d85410058b41ec3a8a8200937815d9515040126d0fb0aa2a0802c5a0f61545410060eb2ae63028200c2d655c8605041907f0cba0a4208022761e64cc84102e1bbb2a8a0e6200c37765d541cc40fd0e64b1283988024d61c525073100598c00a4a0e620083d84dc1658c40b83eecaa287188020fe197414a310041ec3cc8294620083d87590528c40186cc8b88a5188030d5917114a310061d322e02946200c39645c0528c40113b0f32665188020f61370594310050fc32a8a186200a2d841d5620c4014d3003aac4188038355143588310041fc32e82906203c2e625d0520c40107b0f320a4188020f61d641483100616ba2c42906200c36645c4520c40186ac8b88a41880f19989711483100632b12e2290620087b865c0520c401874c8b80a4188030e591701483101e35312e02906200c69625c0520c40146b0daa282188028de19545043100713aa2c4a086200e2554589410c40fd0c86b128218803a150d625043102d4b41eeca086200a35869d5410c40146f0cbaa8218802a5e1973504310068abaae6a086207e8732589410c401c4f0ab128218803892156250431007133aac4a086200e2575589410c40fd0d06b12821881fa19cd625043100742b9ac4a086207e8430589410c40146b0d29282188038958a52504310049ac38a4a086200a3586149410c401c4ac42928218802cc60052504310043cc38a53006200a398414a600c4014e302294c01881fa40c141580310051cc24eab006200e195450d600c4010f30e292c0188028e610525803100538c08a4b006200e3354505600c401c62a8a0ac01881fa490d415803100748a1a82b006200e3285505600c401c630aa0ac0188038c9d5415803100718baa8
  | 5 => 0x9003459d571993320068abaae33266400d16855c664cc801a2b0ab8cc99901f45995719933203e8ab2ae33266407d85625c664cc801a2ca4b8cc9990034514971993320054b40eecb266400b158199354cc80183aecb26a999002c560664553320060fbb2c8aa6640391c8755142cc80123b093acc1990020fe1170d95320041fc0ae832a640683c87591544c81d61904aa686990034555171d0d3206d86412a8a1a640091f845c3654c801a1f04ba0ca990034320974195320048fc0ae832a6400b0d82991544c81da18e5322a899002c560664551320048e43ac8aa26400b0f82591544c81ba18e4b22a89900e53a1f7255132005a2c08e4aa26400b49801c9544c8070bb0fb2ec49900e1761c65d89320050ec20cbb12640ed0c529d3624c80132b033a6c499002c361065d8932004a7c3aa9b126403b0c82553424c8072390eaa2849900ec320954509320048ec20eab0a6400cd1615c0614c80123b093acc0990030d59171d0f510049ac0ce9996a200b15819d332d440183aecba665a880287610764cb5101d26412c8996a200c36645c4529440186ac8b88a5288030e9917014a510061cb22e0294a20083d849db525440126b033a0c6a88024d60674cc9510058ac0ce9992a200c1e765d3325440107b083b264a880287610764c9510051ac0ce9b02a200c1d74ccb605440183ae8996c0a88220f61b70553410050e412a8b1e8200a1f8055163d040183aa9b92c7a08320f21d5458b4106516412a8b168200c1d7498c52d040149b05318a5a0803075d16314b410062b31ae22968200c55635c452d04018b4c6b80a5a08031658d7014b410060fbaac7216820083c8759542d040183aedaa665a0803075d954ccb4101d26412ca9968200c1d7655132d041961904aa265a0803075d163d47410050e412cab1e8200a1f8059563d040183acbb92c7a08024d6047558b410641e43acab16820ca2c8259562d040113b0d39ca5a080307dd96394b410041fc32e12968200c1e835d852d040183b06bb0a5a083307cc97614b410660e992ec296820cc36815d852d040186b02bb0a5a0803075da6314b4100586c14c62968200c1d7658c52d041926f0cb88a5a08034598d7114b410068ab1ae2296820cd17325c452d0419a2a64b88a5a08034698d7014b410068cb1ae0296820cd1b325c052d0419a3264b80a5a080307a1576ccb410060ec2aed9968200c1e525db32d0401838a4bb665a0803075da75ccb410060ebb2eb9968200c1d7699732d040183aecb2e65a08020f618754cb410050ec30ea9968200c1d7659532d041961904b2a65a0803075d963d47410050ec3665a8e8200a1d86cc951d040107b0db82a3a080e0f21d655094101d16412caa128203a4c82595325041761904aa264a08024de0171995410049ac06e2b2a8200935819d46
  | 6 => 0x200d0000200200000001c00805000054010090040000380100602c0301100400c00802000004030090020080200101e0000000c00009c028050000040300900a040030080020100200800a0041d80b02e03c0100106e0041683f00e0000400700a04002806056000050170100080000c02801c05002000018060000000040000200203c1200900600400800018038010060460241d0000040401480301a0000002500400412006008000000000000040100a0280040200000a000028080080000780303003c0100700a018010200051ac0ea8b0ca803c4c625ce625500146b03ba6c2aa0220f61b70553430741e43aa8b168600a378155161d0c0146f0eaa2c3a18028d20954587430051bc02a8b0e8603a4c82551639480183ae8b18a72902b07ccb74582520560e996e8b04a40083d81dd1609480146b023a2c1290028da0773590520051ac0ee6b20a403a2e829cd641480143d07b8ac8290028760f71590520060f41ee2b20a400c1d83dc5641481983e65b8ac829033074cb71590520050f418e0b20a400a1d831c1641480745d04382c8290028da0470590520051ac08e0b20a400875869c7431480186ac938e86290030d59171d0c5201e17392c9218a400c2d645ca431481746b033a2c2290328de0574584520041ec26e0b08a400a56839d161148014ab073a2c22900385a0e74584520070ac1ce8b08a40ce17329d16114819c2a653a2c2290030de1d745845205f0b992e8b08a40be15325d1611480146d09b9ac2290028d61373584520061aba4e6b08a400a36841cd611480146b0839ac2290030d5d0735845201d33410e6b08a400a72801cd61148014e30039ac2290021da1f43584520043ac3e86b08a403a668290d61148014cb0521ac2290028da1370584520051ac26e0b08a400c3574dc1611480186ae8b82c22900295e0d70584520052a41ae0b08a400a36841c1611480146b08382c22900295a0c70584520052ac18e0b08a403a66821c161148014b5063a2c0290029660c745805201d35410e8b00a400a72811d160148014e3023a2c0290028ea1073580520051cc20e6b00a403a6a821cd60148014e50239ac0290029c60473580520053940e86b00a400a7181d0d60148074d50521ac0290029a60a43580520051d424e2b00a400a39849c560148014b706b8ac0290029620d71580520051d420e2b00a400a39841c560148014b50638ac0290029660c715805201d35410e2b00a40883d86dc154d080146f02aa2c3a1002876107558e4201d26412a8b1c8400c37655c7439080f92cc6b8e8721002ca600725514204c1f436e0aa28400c1d545cf615080107b09b82cb990030da1571993320061ac2ae33266400c36525c664cc801868a4b8cc9990032559271d0f320068aaa2e3a1e6400a1f8655143cc80123b09b82cb9
  | 7 => 0xe0a41e2930928007149a42c9662acd24150004549e4039bb7501c0799fc1d47dc000e404877c8a1f1372000002ff6a4000000104b881d6613c616150a51e55dce38938d30e60010babc0009f4c38002360485d800626001b51bd3460a0000000006710c92d100d412f0004c2000791c32409485019160c000cb9fb1bc0ad162b80007680000072097ceb07e514134aa08a00058404b765d4158f804a2e852c892c031ad953d94617a000000000005cc003293b8b599827f518d040026f00091000000000001cd1ad0005b880b371d0a410f9f3104701393170720715f0006ce778dc1474e2ae8558a160872dcf094000248003985b6000002a20006604e84800039ce72f95260004ca23000c1c0013b70050c6cae103ae880038564e2a98115f630d4c002580001742933a0de8fd1b36c0cc00077af107e561571bf000859791722bc86d4098b14ae587a1ef0007ac442b921a04c65a1056c6689c058452029cb9c70003594d10a186001bf00040c9ac0423c000c3d680ae36a0001a1761a81d12a0b41f80000000060600158285152afc97018064c2917a392a48085c1294e80e955800464001052d31989f867326312c341483805a4107336f07a1ed7b0b2162628a6a7366ad3d05a64532d00540f91fcb091f0403da438231cd0a623d68afc0da2459898f00c0eca022763ce504a93a000098249c220e9200580038898db82800fae90f930e486aa4759490e20885b0bc3b2df550162450278768d71906bc9591e4d8dac0b921308be8b39457241e43fb23740b392816c6322e4bf9d3036c84e8830448b94e5245342cadd31680ce4e431996398d99d692a466c1529ab4318000ae38265a424ae82c4066a860ae8524878bc0af3041847112333cea8078ad0ea000930005889dc002ef52c000002e06f6000002ec63e1711ea4b0006391ba9800040d9920c000a546d16f226c00511dd0d87844d8003f4001c9afe26e6b1d79f8548e1c0007700024c0000046000000375000eace800009c0000d32569415c910005cc0012d8000009d5a6a2d4ce0003402030ce25588003d0898bd12f480000001710ec4201b1170008e0313620a05300029c1b600000000000210000120000180040c8010060180a8030300340400300e0900080300009002834000000088080200680000100004400000004034008020000300300100003000802004000000000000100180200800c0080d04a0180a800000000038000020180800000805c018200001980300003c044038000100d00480f0020000000004400011000022000008030060100700b0000040780300002004801008024038000000000000e06c0140080800a008010010060040980f0420242682201a000048040040280380100407000003016054000010480000780902c018100020380100080105007c
  | 8 => 0x1ec54e5b5332f7000adc4180130633dad0f000031000000000000d20000005655db142600014ea2059695db4b4306ec587011d000cd156897302a51ab800000000001a82a64456e8006f4a3c00259184b1c600006a24c904b8b11c944001440c0b6035b5d000001caae3000db45f179522d8c001d80000011db9d332928002460622306c000000908d98031ea24107214000dcc7b0ec640698ca9241585a48e1ee0220548a8d52fc0b898ba756a3f434b7458aa0c002e2000001d714f69c00197a874c47fd44180102000aa80000067574aac09664da417d378224f19e236eca8fa800174e84b2b42718c404b10b644d112ea053e87253437210a884eba8b41a0382a864456849c687238ac24f233b54c56ce9000000d6cbda4f5ea0d421b8f3d4bad798d1000c68ca31d50c00000150000131368003fc4d00010600037011b541ca0107d185000051af800732df16e01e5e0c70f38470049542d2ed58255dd19c1340460db09f43a58159ad45bcde05a89a6c02cd842c859e3a4dd28e19a7e446afb0f81e00c87a5b46f87b8005508899f2c9116b35d2b2845c5a96bb58000d140038457a8609f81f51ab6557b4c09e7d8810ee0d49949421117e31cf021a5be76d449362006d02880070c6c52d0d26dc0bd923914263ec0299b0be0f94daf46b229c8d241702755ce05e35203410aa34f08550220f1309b82132e4c0a95650b0564d18d120158cb9d249cf6c828d6a97c360328e305b3fac542223a758750b23365fa001bf8f814c43dbc9b2018640003a926addd9e1635a491d88b4708a7993d24e1a0a1070833232ce18099253eccc373715f0195380000009a8001e90000008b1a7000538000000004f9ab28223e8946312c04ad2c0039f02caa94f000192b0dcd9ae1fe430000c50000000032c62421c4e2974ec0006f80016ea84c41330007218614200000000000672d5420800000c6c71b5c2b4000a8800462e0db090546a09c002342ee000d593d410219c41482ea935b42000000019f9105c867cb8000000cf4a096b4ac3741e000000d78d28000008713
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x12319020954587430050364a83dc5641480160592a0e745845200505a4f875d16114801831746007358452006055d0835c161148010359814971993320050c640525c664cc80141596949719933200445660525c664cc80141596149719933200544640525c664cc8015049255171d0d3200541644825d0654c801509902097419532006411c981991544c8019045260674d893207443e5d84197624c801219902095458f41006035d18298c52d04014459298d7114b410051264a635c052d040180c825d9544cb41004856448259563d0401219902096558f4100605a0d815d852d040180d7660a6314b410054164a635c452d04015099298d7014b4100407660525db32d04014159114976ccb4100506640525db32d040180c825d9654cb4100505a4f815d852504015109360570149410060561a7314b6150401505929cc52d8541006449cd8014b6150401621902156250431007015d573589410c4018258758852504310068858980149410c401a118560d41580310048c66052505600c40143197149415803100541650874c95148401905844cb705452101d11259754c9414840150597215325052105d81259754c941484175059719532505210048364a83dc564d400140d92a0f71593500040d6478759332d400121591e1d64ccb500040765f8159332d400160591209644cb50005826408259132d400120f98593724cb5000505a4f815d941d4001825865c9410c7500050c659415c031d4001a05864c9414875000485644825516310001219902095458c40004896448755162100132299021d54588400050325d545cd621000180c825d9544c84004c8326154589321000123190209545844000581249544c961100010359814971191200068114981191324800120c96610754c9200068119581191324801340c965d132d41200060c1d98119150480011299421d325412000542650874c95048013c08761913254120005c0644644c9504800160896551329012001d12259754c9404800140d949957218d1000503650855c86344001445912157218d1000512640855c8634400180d74608631491000511648635c452440014499218d70149100058164863d4541440016059218d515051000681d518218d4144001a05546086350510006819958218d4144001a05656086350510005846427518d4144001a07956086350510006812558218d4144001a06756086350510006815d58218d41440012159818e5250510005816486394941440012159818c52505100060561c6314941440016059218c52505100068418d80149414400f284985893250510006445d5831c14144001921756087050510006035d18218f50440014459218d71d41100060561c6350750440016059218d41d411000581648635055044001248985953248110
  | 1 => 0x32af0089881a35a80004369980000180220494002280001fa50d802110b980000013382d0030118000238000341daa8000001e29002080001800000000168a02001c0c800007b8862cb9278d1ca3011f3489002ea6b724afa41783a5859d1592948c16310e338f93b31eab8bac203a1b308035288697318737828e922e271895190f0021a6360008802b1b800a8029802d8010110b03052a001ab20380c14102000280c000c24045c0800040c181c0400746c4010003810006004003c5c204008702
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x88000028002a12809849600eb06b9c02481440079a3002260000001c00400c0004a0340492a8b8e8699002901a01c981991544c801082d48a4c0ce9b126400a406805260674d893200501340412ecaa265a0802805a12097659532d0401404d0104bb2ca9968200c01619929cc52d85410052034539b00296c2a0802205a1e6164dc932d4001202d1527c0aeca0ea00090168497551735884000500b42412ecaa26420002809a0209765513210001300d0124aa264b0880008816a452604644c92000440b424b3083aa649000340076644644c95048001402d392ac10c6a0a2000a80680956086350510005403413ab0431a828800300587648631494144001500d10c6c00a4a0a2000c0161d9218d41d4110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x1
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0xb8c
  | 8 => 0x1049
  | 9 => 0x10b
  | 10 => 0x130b
  | 11 => 0xb8b
  | 12 => 0x184b
  | 13 => 0xe8b
  | 14 => 0x18cb
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 72
  | 6 => 2185
  | 5 => 3978
  | 4 => 944
  | 3 => 117
  | 2 => 24
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*15) 6
  | 7 => packedAt gbK7 (i*26) 17
  | 6 => packedAt gbK6 (i*37) 28
  | 5 => packedAt gbK5 (i*48) 39
  | 4 => packedAt gbK4 (i*59) 50
  | 3 => packedAt gbK3 (i*70) 61
  | 2 => packedAt gbK2 (i*81) 72
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 8 => gbHint (packedAt gbK8 (i*15+6) 9)
  | 7 => gbHint (packedAt gbK7 (i*26+17) 9)
  | 6 => gbHint (packedAt gbK6 (i*37+28) 9)
  | 5 => gbHint (packedAt gbK5 (i*48+39) 9)
  | 4 => gbHint (packedAt gbK4 (i*59+50) 9)
  | 3 => gbHint (packedAt gbK3 (i*70+61) 9)
  | 2 => gbHint (packedAt gbK2 (i*81+72) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (16+((h/1+packedAt gbK8 (15+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (2040+((h/24+packedAt gbK7 (1872+(h % 24)*7) 7) % 125)*8) 8
  | 6 => packedAt gbK6 (89581+((h/728+packedAt gbK6 (80845+(h % 728)*12) 12) % 3490)*13) 13
  | 5 => packedAt gbK5 (208182+((h/1326+packedAt gbK5 (190944+(h % 1326)*13) 13) % 6353)*13) 13
  | 4 => packedAt gbK4 (59150+((h/314+packedAt gbK4 (55696+(h % 314)*11) 11) % 1133)*11) 11
  | 3 => packedAt gbK3 (8502+((h/39+packedAt gbK3 (8190+(h % 39)*8) 8) % 155)*8) 8
  | 2 => packedAt gbK2 (1992+((h/8+packedAt gbK2 (1944+(h % 8)*6) 6) % 34)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe0fc381e30c1f0e0ffc7e07f87f138698474cf
  | 1 => 0xff0fc01fc0fe1f00f078ff83f8f6a1919a4b33
  | 2 => 0xfffe1ff001fff007f0003ff08c61e638c3c
  | 3 => 0xfff00001ffffe000007ffffc000f07e07c0fc0
  | 4 => 0x1ffffffffff800000000ff8007ff000
  | 5 => 0xfffffffe0000000000000000000fffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x20140882000020201401202084400828801045
  | 1 => 0x490a411480521904a1084a0160a2a0910a4112
  | 2 => 0x9040510002420052010a12000202208c28
  | 3 => 0x92a002417aa5400a02649558120d0740740e80
  | 4 => 0x18820411acf99c9ccb000610202ff0005f6000
  | 5 => 0xfccf2798083108108c00186044cffdfd800000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfefafef8fefaeee8fefafef8fefaeee8fefafef8fefaeee8fefafef8fefaeee8fefafef8fefaeee8fefafef8fefaeee8fefafef8fefaeee8fefafef8fefaeee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_14816
namespace PEqualNP.Outside.L_meta_14816
open PEqualNP.Outside.L_meta_14816.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 6 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1 := bs5_4_0
theorem alls5 : ∀ k ≤ 4, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 24 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 117 := (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 bgb_3_96))
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
theorem bgb_4_256 : Interval gbAtlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_320 : Interval gbAtlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_352 : Interval gbAtlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_416 : Interval gbAtlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_448 : Interval gbAtlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_704 : Interval gbAtlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_736 : Interval gbAtlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_800 : Interval gbAtlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_832 : Interval gbAtlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_896 : Interval gbAtlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_928 : Interval gbAtlas 4 928 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 944 := (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat (concat bgb_4_224 bgb_4_256) (concat bgb_4_288 bgb_4_320)) (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 bgb_4_448)))) (concat (concat (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)) (concat (concat bgb_4_576 bgb_4_608) (concat bgb_4_640 bgb_4_672))) (concat (concat (concat bgb_4_704 bgb_4_736) (concat bgb_4_768 bgb_4_800)) (concat (concat bgb_4_832 bgb_4_864) (concat bgb_4_896 bgb_4_928)))))
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
theorem bgb_5_1504 : Interval gbAtlas 5 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1568 : Interval gbAtlas 5 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1600 : Interval gbAtlas 5 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1664 : Interval gbAtlas 5 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1696 : Interval gbAtlas 5 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1760 : Interval gbAtlas 5 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1792 : Interval gbAtlas 5 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1856 : Interval gbAtlas 5 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1888 : Interval gbAtlas 5 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1952 : Interval gbAtlas 5 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1984 : Interval gbAtlas 5 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2048 : Interval gbAtlas 5 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2080 : Interval gbAtlas 5 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2144 : Interval gbAtlas 5 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2176 : Interval gbAtlas 5 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2240 : Interval gbAtlas 5 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2272 : Interval gbAtlas 5 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2336 : Interval gbAtlas 5 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2368 : Interval gbAtlas 5 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2432 : Interval gbAtlas 5 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2464 : Interval gbAtlas 5 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2528 : Interval gbAtlas 5 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2560 : Interval gbAtlas 5 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2624 : Interval gbAtlas 5 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2656 : Interval gbAtlas 5 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2720 : Interval gbAtlas 5 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2752 : Interval gbAtlas 5 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2816 : Interval gbAtlas 5 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2848 : Interval gbAtlas 5 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2912 : Interval gbAtlas 5 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2944 : Interval gbAtlas 5 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3008 : Interval gbAtlas 5 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3040 : Interval gbAtlas 5 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3104 : Interval gbAtlas 5 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3136 : Interval gbAtlas 5 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3200 : Interval gbAtlas 5 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3232 : Interval gbAtlas 5 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3296 : Interval gbAtlas 5 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3328 : Interval gbAtlas 5 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3392 : Interval gbAtlas 5 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3424 : Interval gbAtlas 5 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3488 : Interval gbAtlas 5 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3520 : Interval gbAtlas 5 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3584 : Interval gbAtlas 5 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3616 : Interval gbAtlas 5 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3680 : Interval gbAtlas 5 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3712 : Interval gbAtlas 5 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3776 : Interval gbAtlas 5 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3808 : Interval gbAtlas 5 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3872 : Interval gbAtlas 5 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3904 : Interval gbAtlas 5 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3968 : Interval gbAtlas 5 3968 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3978 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 bgb_5_576)) (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704))) (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832)) (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960))))) (concat (concat (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184))) (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)))) (concat (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696))) (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 bgb_5_1952)))))) (concat (concat (concat (concat (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 bgb_5_2176))) (concat (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 bgb_5_2304)) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432)))) (concat (concat (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560)) (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688))) (concat (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816)) (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944))))) (concat (concat (concat (concat (concat bgb_5_2976 bgb_5_3008) (concat bgb_5_3040 bgb_5_3072)) (concat (concat bgb_5_3104 bgb_5_3136) (concat bgb_5_3168 bgb_5_3200))) (concat (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328)) (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456)))) (concat (concat (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 bgb_5_3584)) (concat (concat bgb_5_3616 bgb_5_3648) (concat bgb_5_3680 bgb_5_3712))) (concat (concat (concat bgb_5_3744 bgb_5_3776) (concat bgb_5_3808 bgb_5_3840)) (concat (concat bgb_5_3872 bgb_5_3904) (concat bgb_5_3936 bgb_5_3968)))))))
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
theorem bgb_6_2176 : Interval gbAtlas 6 2176 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2185 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))) (concat (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896)) (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)))))) (concat (concat (concat (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312))) (concat (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600))))) (concat (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728)) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)))) (concat (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 bgb_6_2016)) (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 72 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 5 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 1 zero,inputs.getD 4 zero,inputs.getD 7 zero,inputs.getD 5 zero,inputs.getD 3 zero,inputs.getD 6 zero,inputs.getD 2 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffefefffffefefefafef8fefafef8fffffefeffffeeeefefafef8fefaeee8fffffefefffffefefefafef8fefafef8fffffefeffffeeeefefafef8fefaeee8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) SB :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) SB :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) SB :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) SB :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) SB :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,4,132)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,4,132)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_14816.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.or,[8,7]⟩,⟨.and,[9,6]⟩,⟨.or,[0,1]⟩,⟨.or,[5,6]⟩,⟨.or,[12,7]⟩,⟨.and,[11,13]⟩,⟨.or,[0,7]⟩,⟨.or,[4,5]⟩,⟨.and,[15,16]⟩,⟨.or,[10,14]⟩,⟨.or,[18,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
    exact ⟨mono,19,monoShape,by change 12 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_14816

open PEqualNP.Outside.L_meta_14816 in
theorem PEqualNP.Outside.L_meta_14816 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
