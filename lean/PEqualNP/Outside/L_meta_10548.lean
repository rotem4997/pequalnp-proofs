import Mathlib
import PEqualNP.Defs

-- The signed circuit search follows the merged L_meta_10856 and L_meta_8453,
-- which adapts the live-wire argument from L_meta_1667 (Apache-2.0).
-- In the six-input search, a row lists the live wires after a sequence of binary gates.
-- A row either expands to checked children or fixes one input and uses a five-input bound.
-- Hashing locates a candidate row. The checker compares its complete set of wire values.

namespace PEqualNP.Outside.L_meta_10548.Model
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
  (n*(n+971)) % 2305843009213693951
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


end PEqualNP.Outside.L_meta_10548.Model

namespace PEqualNP.Outside.L_meta_10548
open PEqualNP.Outside.L_meta_10548.Model
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

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d 7 k cs.length pool ws)

def mirrorSteps : List Move := [swapRows 32]

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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) 7

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

end PEqualNP.Outside.L_meta_10548
namespace PEqualNP.Outside.L_meta_10548
open PEqualNP.Outside.L_meta_10548.Model
def g0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g0K5 : Nat → Nat
  | 0 => 0x70c20a963284d0e22a408200005802e10a231290c203a4090026a0680386c000187852a3e955804e000261e14180000002200451bcc58000401801f510ed32fd43fd42fd41fd40fd32fd31fd30fc43fd21fd20fc42fc32fd10fc41fc31fc21fc40fc30fc20fc10ff40ff30ff20f710ff10ff41ff31ff21fe10ff42ff32fe21fe20ff43ee32fe32fe31fe30fe43fe42fe41fe40
  | _ => 0
def g0K4 : Nat → Nat
  | 0 => 0x1a90288b0e0011800d0880071219970021078519000a8413001c981f260000012980209c0027a30d9282200004800c1680000e8000a70388069a2c22251b2917a682989b9da1ab8f00228000030993941eaa9d0610aa01a39115a80c80240b9625ad248014890f85951f802d802cab1e0a004832600042080081410002400810140040005831814caf888281f1104c2f2a021de54042bca808379500c6f20b10dd54443baa8885e5104caea2b085d45440ba8a8617515082ea2b105d45632ba8ac6175159039a64a1f34c930b69ac656d5210eda4a20db49431b6928816d250c2da4b985b49710b692e636d2590eba6a21574d441ae9a8815d35082ba6b90cf514319ea28613d45082d8a4a05bc9643af9ae43745150eee2b205dc5630bb8ac65cd320c6ee2b105bc9731b792e217b05886de4b987c440209fa28415f350827e8a1857cd440e6996616f250c2de4a207c44320bb8a84177150c2ee2a207c44310f299621e525c42ee2a0879c97109fa2863775150ebe6a20dbc9431b7928837a500c6f4a020dbd4940af9a885765110af4a0215b94843f288465e5158cb9a65195bc9432f38ac65e7108caeca221f34ca31bd28087f1108c39a6521fc44240
  | _ => 0
def g0K3 : Nat → Nat
  | 0 => 0x6a56f10c0a2800c4100171cc029003f0441324c3513544020cc515100836110149409c5805150e7160c5632d2541320c76105c9710c3515320c64d3614940934db25c43453214543d14d7158ca6565c4232b14db25c42e160c5632
  | _ => 0
def g0K2 : Nat → Nat
  | 0 => 0x2004c1c82209b0a4a0641054db25c4320b026428a87904d560c5632
  | _ => 0
def g0N (k : Nat) : Nat :=
  match k with
  | 2 => 4
  | 3 => 16
  | 4 => 92
  | 5 => 44
  | 6 => 1
  | _ => 0
def g0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g0K2 (i*49) 49
  | 3 => packedAt g0K3 (i*38) 38
  | 4 => packedAt g0K4 (i*27) 27
  | 5 => packedAt g0K5 (i*16) 16
  | 6 => packedAt g0K6 (i*5) 5
  | _ => 0
def g0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g0K2 (198+((h/2+packedAt g0K2 (196+(h % 2)*1) 1) % 8)*3) 3
  | 3 => packedAt g0K3 (632+((h/6+packedAt g0K3 (608+(h % 6)*4) 4) % 19)*5) 5
  | 4 => packedAt g0K4 (2670+((h/31+packedAt g0K4 (2484+(h % 31)*6) 6) % 113)*8) 8
  | 5 => packedAt g0K5 (779+((h/15+packedAt g0K5 (704+(h % 15)*5) 5) % 57)*7) 7
  | 6 => packedAt g0K6 (6+((h/1+packedAt g0K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g0Pos : Nat → Bits
  | 0 => 0x0
  | 1 => 0xbaecf3d5b555fa45b96965a52f6cbfc58925e7
  | 2 => 0xcd755566dab48aeadab18aee57b3f2ca125cf8
  | 3 => 0x99ba7ab493e6b3536cdb3375fd255550a71f21
  | 4 => 0x6e5c5cf8fcf8dc7c771ddfc69a3a69a347e84a
  | 5 => 0x8f9f9f3f1f3f1f9f87fe1c78e3c38e3c7c9294
  | _ => 0
def g0Neg : Nat → Bits
  | 0 => 0x0
  | 1 => 0x1fc01fe00000000003fc0fc00000e7
  | 2 => 0x1fc01fffe0000000007f03fff000001cf8
  | 3 => 0xfe01fffe0000000001fe07ffc000000071f00
  | 4 => 0xfffe00000000000001fff800000000007e000
  | 5 => 0xf00000000000000007e0000000000000780000
  | _ => 0
def g0Atlas : Atlas := ⟨6,rawDecor 62 g0Pos g0Neg, 0xfffffffcfcfccc00fffffffcfcfccc00fffffffcfcfccc00fffffffcfcfccc00fffffffcfcfccc00fffffffcfcfccc00fffffffcfcfccc00fffffffcfcfccc00, g0N, g0R, (fun _ _ => 0), g0I⟩
end PEqualNP.Outside.L_meta_10548
namespace PEqualNP.Outside.L_meta_10548
open PEqualNP.Outside.L_meta_10548.Model
def g1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g1K5 : Nat → Nat
  | 0 => 0x90000161891e3aa0504388018e0e000002e00001000148522000001a001003400c005cb00004c3c00032acd94460002a2054b2f1200000424d6804430025109cf80000cf8400010050001c2040006ed32ed21ed20fd43fd42fd41fd40fd32fd31fd30fc43fd21fd20ec42fc42fc32fd10fc41fc31fc21fc40fc30fc20fc10ff40ff30ef20ff20ff10ff41ff31ef21ff21fe10ef42ff42ff32fe21fe20ff43ee32fe32fe31fe30fe43fe42fe41fe40
  | _ => 0
def g1K4 : Nat → Nat
  | 0 => 0x3738154b201148005e1604800e40604000c07a0801cb63500088da662b8e0007b221240000000640a0d398d8e8002f8b09840411e07e311312042123e12c46713f9348e000000000000000000643719c005e298000032311a400630007c9c003513c74180003c0015000a03c00229b04002001bc003400108000e00149020000104145830974fc2d2e000005a12044ea513b80054433b0ccfa00000ac2e001f0e43a040d128ac3b1e1e4060b2a04d0600000944e300a030a0000da00ca1c23000d668170007a03c40d80022a8c30a1b100000498000a0a80148401400300c50bc22f490281695010af2a021de54042f4a80857950106f2a018f948541b2a8885755110eeaa2217954442ba8a88175150c39a64a1d34d442b6a92636d524c2da6b195b4d442b6a90876c454cada6b905b4d721b69ae856f458cada4a885b49621b6928836d5110ad88a90db49431b692c416d25102daa0215b11520b6928616d25042da4b985b49710b692e636d25842da4b18db49630b692c876d25906da4b20574d442ae9a8835d35102ba6a084f514319ea28613d45042d8a4a1db14941b6292816f25902de4b20dbc9643e69a8856f2590ade4b185bc9631b68ae416f25842da2ba15bd1721b68ac65d5310c6de4b98db41721b792e216d05d0ade8b905b41632ec980616f25cc3e220084fd1410af9a8216f250427e8a185bd4132af9a8816f50486de4a185bc9440f4906416f25082d88b905dc5430bb8a8813f450c6dea29957cd441b7a8a416f250c6de4a20f948721b7928436c45c86f4a018de94041b702e436f5250edea4a0dbd4940b7a2885ac42d0abe6a2173cd442bb28885e65110af4a0217a94042b702e856e15d0adc6a90db8d520b729087cd328cade4a195b11632bb288877a5010edc0b195b85632b712e87cd3290fca4320fa48240
  | _ => 0
def g1K3 : Nat → Nat
  | 0 => 0x8a05160000c20347952260e831c5c3161078c892670020002910046043a1246c01f080001a00e2c0109801028a0d85415110b513544010cc5151004351154c030d4541310c66960115329a5804548749504d4429a55a5010b294011520c6515300c26906117219a418458ca69068563299584454ca656111520d15453510a655694442c95044548715454c4319945845c826516116329945a058ca4d3611521934d8454824d3611632c350c454ca4d3611720934d845c864d3681721d25433510b4551cd442d85425110b453594442d85465010b493594042
  | _ => 0
def g1K2 : Nat → Nat
  | 0 => 0x800a624c310a02c222a41885814111521c12809b08a906096050c454cb02a0a6c22a43815854311532
  | _ => 0
def g1N (k : Nat) : Nat :=
  match k with
  | 2 => 6
  | 3 => 36
  | 4 => 132
  | 5 => 48
  | 6 => 1
  | _ => 0
def g1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g1K2 (i*49) 49
  | 3 => packedAt g1K3 (i*38) 38
  | 4 => packedAt g1K4 (i*27) 27
  | 5 => packedAt g1K5 (i*16) 16
  | 6 => packedAt g1K6 (i*5) 5
  | _ => 0
def g1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g1K2 (300+((h/2+packedAt g1K2 (294+(h % 2)*3) 3) % 8)*4) 4
  | 3 => packedAt g1K3 (1428+((h/12+packedAt g1K3 (1368+(h % 12)*5) 5) % 44)*7) 7
  | 4 => packedAt g1K4 (3784+((h/44+packedAt g1K4 (3564+(h % 44)*5) 5) % 176)*9) 9
  | 5 => packedAt g1K5 (864+((h/16+packedAt g1K5 (768+(h % 16)*6) 6) % 76)*7) 7
  | 6 => packedAt g1K6 (6+((h/1+packedAt g1K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g1Pos : Nat → Bits
  | 0 => 0xeebb3cfaaadabe916e5a52d2ef2cbfc589278f
  | 1 => 0x0
  | 2 => 0x775d5d59f36e92bab6ac6577a557f2ca925cb9
  | 3 => 0xa26e96ad5a44d4d4db36c9ba74fd5550271fc0
  | 4 => 0xdb97173e7c771f1f1dc77fe3469a69a347e912
  | 5 => 0xe3e7e7cf9f87e7e7e1ff8e3c78e38e3c7c9264
  | _ => 0
def g1Neg : Nat → Bits
  | 0 => 0xfe00007f8000000007f000fc0000387
  | 1 => 0x0
  | 2 => 0x7f00007f8000000003f8003f000001c38
  | 3 => 0x3f807fffff800000007f03ffffc0000071fc0
  | 4 => 0x3fff800000000000007ffc00000000007e000
  | 5 => 0xfc0000000000000001f8000000000000780000
  | _ => 0
def g1Atlas : Atlas := ⟨6,rawDecor 61 g1Pos g1Neg, 0xfffffffafafaa0a0fffffffafafaa0a0fffffffafafaa0a0fffffffafafaa0a0fffffffafafaa0a0fffffffafafaa0a0fffffffafafaa0a0fffffffafafaa0a0, g1N, g1R, (fun _ _ => 0), g1I⟩
end PEqualNP.Outside.L_meta_10548
namespace PEqualNP.Outside.L_meta_10548
open PEqualNP.Outside.L_meta_10548.Model
def g2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g2K5 : Nat → Nat
  | 0 => 0x6104e24005261000a10652951a591a23a441a9001d000380109e3e000011e6cd002800c06165d30e009152b04494059434c4003002341080040f910ed32fd43fd42fd41fd40fd32fd31fd30fc43fd21fd20fc42fc32fd10fc41fc31fc21fc40fc30fc20fc10ff40ff30ff20ff10ff41ff31ff21fa10fe10ff42ff32fe21fe20ff43ee32fe32fe31fe30fe43fe42fe41fe40
  | _ => 0
def g2K4 : Nat → Nat
  | 0 => 0x290000158028991f1b822c270dab97a8241c130000171c80908291129e8023091a80000000098ea28000218d27859b2a80250f88a6941181038c84adab1f922c818a0aa3882d2498a2040b259e0b8013a1001007969a0726050f20000c0e0029999d951d1816208600000306aa148a3c10c930268b1c02c000000748a3e7002006040842102f888283f1104c6f2a021de54042f4882657915842f2a020de54031bca8043f110086f20b10de41632bc82c637905906eaa221dd54442ba8a88175150c2ea2b10734c943e6992636d358cadaa421db49441b6928636d25102da4a185b49730b692e636d25842da4b21d74d442ae9a8835d35086ba6a20574d7209ea28633d450867a8a185b14941b792c876f25842ee2b105bc9731af9ae41785050ef60b20dec1631bd82c65cd320c2f60b10dbc97309fa28617b5050ebe6a205bc9430b79288177150c2ee2a204fd1421af9a8433f450c6be6a20f34cb31b7928636f25107e22190de94021bd280637a50107e221087a4ca10f492c217b05043d64b085bd4941af9a885765110af4a0215b94843f488465e9058cb9a65195bc9432f582c65ea108caeca221fc44231bd28087cd328c39a6521fc44241
  | _ => 0
def g2K3 : Nat → Nat
  | 0 => 0x26401cd000005112b2898f00ce005a1df0441324c751104d421cc441450876110149419c4585050e7116c1632d84572584345154c830c3515320c24d3614941934db25843493214143d24d7058ca696584232b24db25842e116c1632
  | _ => 0
def g2K2 : Nat → Nat
  | 0 => 0xa600c82209b0a4a0e41154db25843208b26428287904d516c1632
  | _ => 0
def g2N (k : Nat) : Nat :=
  match k with
  | 2 => 4
  | 3 => 16
  | 4 => 92
  | 5 => 44
  | 6 => 1
  | _ => 0
def g2R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g2K2 (i*49) 49
  | 3 => packedAt g2K3 (i*38) 38
  | 4 => packedAt g2K4 (i*27) 27
  | 5 => packedAt g2K5 (i*16) 16
  | 6 => packedAt g2K6 (i*5) 5
  | _ => 0
def g2I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g2K2 (198+((h/2+packedAt g2K2 (196+(h % 2)*1) 1) % 6)*3) 3
  | 3 => packedAt g2K3 (632+((h/6+packedAt g2K3 (608+(h % 6)*4) 4) % 21)*5) 5
  | 4 => packedAt g2K4 (2670+((h/31+packedAt g2K4 (2484+(h % 31)*6) 6) % 110)*8) 8
  | 5 => packedAt g2K5 (794+((h/15+packedAt g2K5 (704+(h % 15)*6) 6) % 53)*7) 7
  | 6 => packedAt g2K6 (6+((h/1+packedAt g2K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g2Pos : Nat → Bits
  | 0 => 0xaaecd555b555f485b96945ee2f68bfc5093ce3
  | 1 => 0xdd7573e6dab495eadab1aaa557b7f2ca9245fc
  | 2 => 0x0
  | 3 => 0x99ba7ab493e6a6b36cdb3375fd255550a71f24
  | 4 => 0x6e5c5cf8fcf8f8dc771ddfc69a3a69a347e849
  | 5 => 0x8f9f9f3f1f3f3f1f87fe1c78e3c38e3c7c9292
  | _ => 0
def g2Neg : Nat → Bits
  | 0 => 0x1fc01fc03fe00000007f03fc0fc0001ce3
  | 1 => 0x1fffc0000000000003fff0000000fc
  | 2 => 0x0
  | 3 => 0xfe01fffe0000000001fe07ffc000000071f00
  | 4 => 0xfffe00000000000001fff800000000007e000
  | 5 => 0xf00000000000000007e0000000000000780000
  | _ => 0
def g2Atlas : Atlas := ⟨6,rawDecor 59 g2Pos g2Neg, 0xffffffeeeeeecc00ffffffeeeeeecc00ffffffeeeeeecc00ffffffeeeeeecc00ffffffeeeeeecc00ffffffeeeeeecc00ffffffeeeeeecc00ffffffeeeeeecc00, g2N, g2R, (fun _ _ => 0), g2I⟩
end PEqualNP.Outside.L_meta_10548
namespace PEqualNP.Outside.L_meta_10548
open PEqualNP.Outside.L_meta_10548.Model
def g3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g3K5 : Nat → Nat
  | 0 => 0x2914911804a4d5961e5ce8906000003284e01000139f182cc0836009004c5500e0088210341c0110a5141e041950d0509019204f080039c2f521f510fd43fd42fd41fd40fd32fd31fd30fc43fd21fd20fc42fc32fd10fc41fc31fc21fc40fc30fc20fc10ff40ff30ff20f710ff10ff41ff31ff21fe10ff42ff32f621fe21fe20ff43fe32fe31fe30fe43fe42fe41fe40
  | _ => 0
def g3K4 : Nat → Nat
  | 0 => 0x45004c312d00000023245e00614d3832600f1528021d5c005518060b172500132200194b424439035f4900205d4e140012263e005a3356410c58100001374630091a363d533407112708510000000a005943001f521c540d404f005b002c5700000029040047350e0000163f003b4a2f50052a3c212e3a001b1e2b480000004440080065d8404806008cc0180a01380b7b8a0183e220a07c44130bca8087795010af2a0195e54041bca80637105886f20b10f948542f290a656525c42eaa221dd54520ba92c43755110aeaa2195d49710ba8ac217515102ea2a185d45420ba8ae417515882ea2b195d45630ba8ac857515902daa421db49441b6928636d25102da4a185b49710ae9a8855d35106ba6a20574d4209ea28653d450c67a8a184f51420cea1887745150eee2b205dc5642bb8ac6177158caee2b105bc9710ba82c437b05887e220107a48020f2908417715c827e8a1057cd4209fa28615f35102eea090dbc9430b792881f110c82ee2a105dc5430bb8a881f110c43ca4b885dc5410f392e213f450c6eea2a1d7cd441b7928636f25106f4a018de940419fa28655f3510aec4a885d94432bb28885f105887ca4310ddc5421f982c437a500caf4a0217948620bb02c436e5210fca43195d94443bd28087f1108c3ca43217c44240
  | _ => 0
def g3K3 : Nat → Nat
  | 0 => 0x4c028d4802c00010001404441832503c02023000073898404d44d5100833145440209c5805150e7160c56429c583158cb493548020ca51520083195050c43d841725c42710681621d14d521083254548420994985150e6526c56409949b158c2652681621c55454310f0d5250c43d849705886e16048420
  | _ => 0
def g3K2 : Nat → Nat
  | 0 => 0x23209aac090841885156048420
  | _ => 0
def g3N (k : Nat) : Nat :=
  match k with
  | 2 => 2
  | 3 => 20
  | 4 => 98
  | 5 => 44
  | 6 => 1
  | _ => 0
def g3R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g3K2 (i*49) 49
  | 3 => packedAt g3K3 (i*38) 38
  | 4 => packedAt g3K4 (i*27) 27
  | 5 => packedAt g3K5 (i*16) 16
  | 6 => packedAt g3K6 (i*5) 5
  | _ => 0
def g3I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g3K2 (100+((h/2+packedAt g3K2 (98+(h % 2)*1) 1) % 4)*2) 2
  | 3 => packedAt g3K3 (781+((h/7+packedAt g3K3 (760+(h % 7)*3) 3) % 29)*6) 6
  | 4 => packedAt g3K4 (2811+((h/33+packedAt g3K4 (2646+(h % 33)*5) 5) % 127)*8) 8
  | 5 => packedAt g3K5 (779+((h/15+packedAt g3K5 (704+(h % 15)*5) 5) % 53)*7) 7
  | 6 => packedAt g3K6 (6+((h/1+packedAt g3K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g3Pos : Nat → Bits
  | 0 => 0xf73679eadaaade90b72cb492f6cbfc4c449e7
  | 1 => 0xf7b4aaab36d5a42b55b555da57b3f2c908b8f8
  | 2 => 0x7bd9d3d5a49f36cda6d9a6edfd255552513f21
  | 3 => 0x0
  | 4 => 0xbdeee2e7c7e7c771f8ee3f8e9a3a69a3a3d24a
  | 5 => 0xdef0fcf9f8f9f87e3f0ff8f0e3c38e3c3e2494
  | _ => 0
def g3Neg : Nat → Bits
  | 0 => 0xe000000000fe007fc000000003fc0fc00000e7
  | 1 => 0xfe00ffff80000000ff03fff0000038f8
  | 2 => 0xffff000000000000fffc000000003f00
  | 3 => 0x0
  | 4 => 0xff000000000000003f000000000003c000
  | 5 => 0xff000000000000000fc000000000003c0000
  | _ => 0
def g3Atlas : Atlas := ⟨6,rawDecor 55 g3Pos g3Neg, 0xfffffefefefea0a0fffffefefefea0a0fffffefefefea0a0fffffefefefea0a0fffffefefefea0a0fffffefefefea0a0fffffefefefea0a0fffffefefefea0a0, g3N, g3R, (fun _ _ => 0), g3I⟩
end PEqualNP.Outside.L_meta_10548
namespace PEqualNP.Outside.L_meta_10548
open PEqualNP.Outside.L_meta_10548.Model
def g4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g4K5 : Nat → Nat
  | 0 => 0x46900060e1400000012952e580000000f080038c27000ca0000305a2007c002002468026100011e00d113a48c9b2000e0a409800042f3010000a10120fd43fd42fd41fd40fd32fd31fd30fc43fd21fd20fc42fc32fd10fc41fc31fc21fc40fc30fc20fc10ff40ff30ff20ff10ff41ff31ff21fe10ff42ff32fe21fe20ff43fe32fe31fe30fe43fe42fe41fe40
  | _ => 0
def g4K4 : Nat → Nat
  | 0 => 0x2e1a00fa344740896a6003710a0a8000b1e8560bc20226941a16241c9170acd241c7999b000000014016994c58927647152028180001eed4b4745c03618005800e01e00000cf14038508303804c2c01410c05820ef2a021de54042bca808379500c6f20b995e41621baa8887755110aea2a205d45420ba8ac6575158c2daa421db49441b6928636d25102da4b985b49710ae9a8855d35106ba6a20574d420ae9ae435d358427a8a18cf51420ae29a836c52502be6b0857cd721ba28a8777158c2ee2b19754c431b792e21785050af60b10dbc9730bd82e65e9200827e8a1057cd420bda82855f35102de4a205dc5420bb8a8813f450c6eea2a1d7cd441b7928636f25106f4a018de94041b7a92815f3510aeca2215e94042afa9a836e5210eeca221de94043
  | _ => 0
def g4K3 : Nat → Nat
  | 0 => 0x20ca5152008315454c431
  | _ => 0
def g4N (k : Nat) : Nat :=
  match k with
  | 3 => 2
  | 4 => 62
  | 5 => 40
  | 6 => 1
  | _ => 0
def g4R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt g4K3 (i*38) 38
  | 4 => packedAt g4K4 (i*27) 27
  | 5 => packedAt g4K5 (i*16) 16
  | 6 => packedAt g4K6 (i*5) 5
  | _ => 0
def g4I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt g4K3 (78+((h/2+packedAt g4K3 (76+(h % 2)*1) 1) % 7)*2) 2
  | 4 => packedAt g4K4 (1800+((h/21+packedAt g4K4 (1674+(h % 21)*6) 6) % 81)*7) 7
  | 5 => packedAt g4K5 (696+((h/14+packedAt g4K5 (640+(h % 14)*4) 4) % 61)*7) 7
  | 6 => packedAt g4K6 (6+((h/1+packedAt g4K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g4Pos : Nat → Bits
  | 0 => 0xcd679ead555f48b72d2ed2d297b4bfc513c2f3
  | 1 => 0xd7aaab37ab495d5b563265772bdbf2ca245e7c
  | 2 => 0xebd3d5a53e6e6a6d9b6c59bafe9555514e8f91
  | 3 => 0x72e2e7c7cf8b8f8ee3b76fe34d1a69a28ff424
  | 4 => 0x0
  | 5 => 0x7cfcf9f9f3f3f3f0ffc78e3c71e38e3cf9294a
  | _ => 0
def g4Neg : Nat → Bits
  | 0 => 0x7f000001fc03fc000007f00001fc0fc001c073
  | 1 => 0xfe01fffc00000000003f81fff000000e7c
  | 2 => 0x8000fffe0000000003f8003ffe0000000e0f80
  | 3 => 0xffff00000000000003ffffc0000000000ff000
  | 4 => 0x0
  | 5 => 0xfc00000000000000f00000
  | _ => 0
def g4Atlas : Atlas := ⟨6,rawDecor 47 g4Pos g4Neg, 0xfffefffeeca0eca0fffefffeeca0eca0fffefffeeca0eca0fffefffeeca0eca0fffefffeeca0eca0fffefffeeca0eca0fffefffeeca0eca0fffefffeeca0eca0, g4N, g4R, (fun _ _ => 0), g4I⟩
end PEqualNP.Outside.L_meta_10548
namespace PEqualNP.Outside.L_meta_10548
open PEqualNP.Outside.L_meta_10548.Model
def g5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def g5K5 : Nat → Nat
  | 0 => 0x70100543821d1a6111556400000078b005231217220048f0c00c810000d25104c3a350840144c6c28a3e481a01601386c5f14610200005f000040dd43fd43fd42fd41fd40fd32fd31fd30fc43fd21fd20fc42fc32fd10fc41dc31fc31fc21fc40fc30fc20fc10ff40ff30ff20ff10ff41ff31ff21fe10ff42ff32fe21fe20ff43fe32de31fe31fe30de43fe43fe42fe41fe40
  | _ => 0
def g5K4 : Nat → Nat
  | 0 => 0x382d2800003253002a00030e3a000c111f180055520041124b00001000191c0027002e00500a09434c2429004d3435053d4657401b0b3c2b000402224a47513e25361401133756151d4e491a1733063031590f4f44200d451e07422f5421230826003b5a163f000058392c480900449700ee840064064020800801864061aa4160021c3795010af2a020de54031eca80637905886eaa2215d45440ba8a84175158caea2b185b49441b6928636d25102da4b886750d418ea28635d4590eba8a18d751631ae9a8855d35106ba6a20574d420ae9ae815d35d06ba6b90d74d610ae9ae853d450c67a8a105714d41ae1aa436c52502be6ba1570d510af9ac215f35c87a8a2a1d514543ba28a875c5150ebe2b21ddc5630bb8ac655f35d07aa4218f544031e6928639d450c6be2b18f510431b792e21785050abe6ba05ec1621f4900413f45082be6a105ed4142af9a8816f25102ee2a105dc5440ea18e213f450c73e8a18f5d4543bba8a879d43d07a863a0d7cd441b792863cf250c6de4a20de94031ed280637a50106dea4a057cd442bb28885d431886f4a02157d4d41af1aa435e35442be2a18f50c631cea1c875f3510eb86b20d78d641
  | _ => 0
def g5K3 : Nat → Nat
  | 0 => 0x2269228cb28026c0e80011c58000252e180780610000a88000900403c0483294548020d2541250c7195051431d45805150ed16010431d441431887154548431c5515100c70d25514318751835907452614543c55185150e57168d6419518535d0254614d742b1498410c745250c710a551831c4295460c741a518543d070d45c9431d1c985150f194594031d49805150e95460c621
  | _ => 0
def g5K2 : Nat → Nat
  | 0 => 0x2100340000001905812614543c22c0a30a2a1e110551831887029328c28a8781495460c710
  | _ => 0
def g5N (k : Nat) : Nat :=
  match k with
  | 2 => 5
  | 3 => 25
  | 4 => 91
  | 5 => 44
  | 6 => 1
  | _ => 0
def g5R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g5K2 (i*49) 49
  | 3 => packedAt g5K3 (i*38) 38
  | 4 => packedAt g5K4 (i*27) 27
  | 5 => packedAt g5K5 (i*16) 16
  | 6 => packedAt g5K6 (i*5) 5
  | _ => 0
def g5I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g5K2 (247+((h/2+packedAt g5K2 (245+(h % 2)*1) 1) % 16)*4) 4
  | 3 => packedAt g5K3 (986+((h/9+packedAt g5K3 (950+(h % 9)*4) 4) % 34)*6) 6
  | 4 => packedAt g5K4 (2643+((h/31+packedAt g5K4 (2457+(h % 31)*6) 6) % 108)*8) 8
  | 5 => packedAt g5K5 (794+((h/15+packedAt g5K5 (704+(h % 15)*6) 6) % 54)*7) 7
  | 6 => packedAt g5K6 (6+((h/1+packedAt g5K6 (5+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g5Pos : Nat → Bits
  | 0 => 0x359e7b6aadf916ec8b57d2d297b4bfca49e2f3
  | 1 => 0x5eaaadbd5c9bab75559965772bdbf2d4923e7c
  | 2 => 0xaf4f5729f6ed4dba26f659bafe955563274f91
  | 3 => 0xcb8b9e3e78b1f1dc78db6fe34d1a6985c7f424
  | 4 => 0xf3f3e7cf9f3e7e1fbfe38e3c71e38e39fc894a
  | 5 => 0x0
  | _ => 0
def g5Neg : Nat → Bits
  | 0 => 0xfc00000fe03f80000003f00001fc0fc000e073
  | 1 => 0x3f80fffc000000000003f81fff000000e7c
  | 2 => 0x3fff00000000000fc003ffe000000070f80
  | 3 => 0xfffc00000000001fc0ffffc000000001c7f000
  | 4 => 0x1fff00000000000001f80000
  | 5 => 0x0
  | _ => 0
def g5Atlas : Atlas := ⟨6,rawDecor 31 g5Pos g5Neg, 0xfefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0fefeeca0, g5N, g5R, (fun _ _ => 0), g5I⟩
end PEqualNP.Outside.L_meta_10548
namespace PEqualNP.Outside.L_meta_10548
open PEqualNP.Outside.L_meta_10548.Model
def g6Hint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x209
  | 8 => 0x249
  | 9 => 0x24e
  | 10 => 0x289
  | 11 => 0x28c
  | 12 => 0x2c9
  | 13 => 0x3c9
  | 14 => 0x409
  | 15 => 0x449
  | 16 => 0x589
  | 17 => 0x58a
  | 18 => 0x5c9
  | 19 => 0x5ca
  | 20 => 0x5cd
  | 21 => 0x749
  | 22 => 0x74a
  | 23 => 0x74c
  | 24 => 0x94c
  | 25 => 0x94d
  | 26 => 0x94e
  | 27 => 0x98a
  | 28 => 0x98c
  | 29 => 0x98d
  | 30 => 0x98e
  | 31 => 0x9ca
  | 32 => 0x9cb
  | 33 => 0x9cd
  | 34 => 0x9ce
  | 35 => 0xa0a
  | 36 => 0xa0b
  | 37 => 0xa0c
  | 38 => 0xa0e
  | 39 => 0xa4a
  | 40 => 0xa4b
  | 41 => 0xa4c
  | 42 => 0xa4d
  | 43 => 0xb09
  | 44 => 0xb0c
  | 45 => 0xb0d
  | 46 => 0xb0e
  | 47 => 0xb49
  | 48 => 0xb4d
  | 49 => 0xb4e
  | 50 => 0xb89
  | 51 => 0xb8c
  | 52 => 0xb8e
  | 53 => 0xbc9
  | 54 => 0xbcc
  | 55 => 0xbcd
  | 56 => 0xcc9
  | 57 => 0xcca
  | 58 => 0xccd
  | 59 => 0xcce
  | 60 => 0xd09
  | 61 => 0xd0a
  | 62 => 0xd0c
  | 63 => 0xd0e
  | 64 => 0xd49
  | 65 => 0xd4a
  | 66 => 0xd4c
  | 67 => 0xd4d
  | 68 => 0xe89
  | 69 => 0xe8a
  | 70 => 0xe8b
  | 71 => 0xe8e
  | 72 => 0xec9
  | 73 => 0xeca
  | 74 => 0xecb
  | 75 => 0xecd
  | 76 => 0x1049
  | 77 => 0x104a
  | 78 => 0x104b
  | 79 => 0x104c
  | 80 => 0x124c
  | 81 => 0x124d
  | 82 => 0x124e
  | 83 => 0x128a
  | 84 => 0x128c
  | 85 => 0x128d
  | 86 => 0x128e
  | 87 => 0x12ca
  | 88 => 0x12cb
  | 89 => 0x12cd
  | 90 => 0x12ce
  | 91 => 0x130a
  | 92 => 0x130b
  | 93 => 0x130c
  | 94 => 0x130e
  | 95 => 0x134a
  | 96 => 0x134b
  | 97 => 0x134c
  | 98 => 0x134d
  | 99 => 0x1409
  | 100 => 0x140c
  | 101 => 0x140d
  | 102 => 0x140e
  | 103 => 0x1449
  | 104 => 0x144d
  | 105 => 0x144e
  | 106 => 0x1489
  | 107 => 0x148c
  | 108 => 0x148e
  | 109 => 0x14c9
  | 110 => 0x14cc
  | 111 => 0x14cd
  | 112 => 0x15c9
  | 113 => 0x1609
  | 114 => 0x1649
  | 115 => 0x1789
  | 116 => 0x178a
  | 117 => 0x178b
  | 118 => 0x178e
  | 119 => 0x17c9
  | 120 => 0x17ca
  | 121 => 0x17cb
  | 122 => 0x17cd
  | 123 => 0x1949
  | 124 => 0x194a
  | 125 => 0x194b
  | 126 => 0x194c
  | 127 => 0x1c0a
  | 128 => 0x1c0c
  | 129 => 0x1c0e
  | 130 => 0x1c4a
  | 131 => 0x1c4c
  | 132 => 0x1c4d
  | 133 => 0x1d09
  | 134 => 0x1d49
  | 135 => 0x1d4d
  | 136 => 0x1d4e
  | 137 => 0x1d89
  | 138 => 0x1d8c
  | 139 => 0x1d8e
  | 140 => 0x1dc9
  | 141 => 0x1dcc
  | 142 => 0x1dcd
  | 143 => 0x1ec9
  | 144 => 0x1eca
  | 145 => 0x1ecd
  | 146 => 0x1ece
  | 147 => 0x1f09
  | 148 => 0x1f0a
  | 149 => 0x1f0c
  | 150 => 0x1f0e
  | 151 => 0x1f49
  | 152 => 0x1f4a
  | 153 => 0x1f4c
  | 154 => 0x1f4d
  | 155 => 0x2089
  | 156 => 0x208a
  | 157 => 0x208b
  | 158 => 0x208e
  | 159 => 0x20c9
  | 160 => 0x20ca
  | 161 => 0x20cb
  | 162 => 0x20cd
  | 163 => 0x2249
  | 164 => 0x224a
  | 165 => 0x224b
  | 166 => 0x224c
  | 167 => 0x94256
  | 168 => 0xa4954
  | 169 => 0xb8b11
  | 170 => 0xbcb11
  | 171 => 0xd0412
  | 172 => 0xd0b14
  | 173 => 0xd4b14
  | 174 => 0xd4cd2
  | 175 => 0xe8411
  | 176 => 0xe8b11
  | 177 => 0xe8b91
  | 178 => 0xe8b96
  | 179 => 0x104751
  | 180 => 0x104752
  | 181 => 0x104754
  | 182 => 0x104e91
  | 183 => 0x104e92
  | 184 => 0x104e93
  | 185 => 0x128b14
  | 186 => 0x130954
  | 187 => 0x160e91
  | 188 => 0x178b11
  | 189 => 0x178e91
  | 190 => 0x178e92
  | 191 => 0x178e96
  | 192 => 0x194e91
  | 193 => 0x194e92
  | 194 => 0x1d0b11
  | 195 => 0x1d0e91
  | 196 => 0x1d1791
  | 197 => 0x1d4b11
  | 198 => 0x1d8256
  | 199 => 0x1d8e91
  | 200 => 0x1d8e96
  | 201 => 0xe8b8b19
  | _ => 0
def g6K9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def g6K8 : Nat → Nat
  | 0 => 0x233d7916423669990624a07252832110407811d2c910b1974ac54127e7000000001000002e0022884013000068e0c00888a535384c00034a8056000005000e980a00d96be370163c28c11cb8e80008648a28168028002a01dd4300feaa007f54c03faa201fd5000fea1807f50403fa800bfc5400fe98807f4c013f8a609fc4300fe90007f4400bf8a205fc4102fe1880ff14007f88003fc3001fe1000ff0401bfea20bff4104ff9880ff8401bfea40bff4204ff99017fc4807fc400dff5305ffa1817f8c407fc600dff5400ef21827f90c0bfc8203fe4005ff2a027f94c0bfca203fe50
  | _ => 0
def g6K7 : Nat → Nat
  | 0 => 0x5064305f75024304f7d5a4305f71524304f790d3104f790d3004ef90d434fff90d5404ff90d5336ff90d5129ff90d5004bfd914304ff90d4333ff90d4125ff90d4004ff90d3104ff90d3000f7482431cff90d2000f74424318ff90d1004f745a4374f71464374f7c5a4374f71064304f741a4373f71424373f7c1a4373f71024373f70824373f70424376f7d464305f7d064373f78424376f7d4a4305f7d0a4374f7c4a4373f78824305f7d524304f715a4300bf9192000ff9192000bf9191000ff9191002fd9055102fd9051045f79054302ef905414dff9055449ff9055302ff9055127ff9055002bfd914145ff9054302ff9054123ff9054002ff905311fff905301bff9052002ff9051074f79064374f705a4301fe9015001fe9012001fe9011044f79014301ef901404cff9015448ff9015340ff9015235ff9015101ff9015001bfd914044ff901433cff9014232ff9014101ff9014038ff901322fff9013101ff901302bff9011201ff9012001ff9011073f79024373f701a4306bfd594134ffd594104bf98d4133ff98d4104f785a4301bf9814132ff9814106bfd59423fffd594204bf98d423eff98d4204f789a4302bf985423dff9854201bf981423cff9814247f7d594306bfd594347ffd594345f79854302bf9854345ff9854344f79814301bf9814344ff9814300f79594300bf9594300ff9594300bf9594100ff9594100bf9594000ff9594005e79514305f79514305ef9514305ef9514105ef9514005df9515405ff951544bff9515337ff951512aff9515005bfd955405ff9514305ff9514105ff9514030ff9513121ff951301dff9512019ff9511005f79524300bf9593100ff9593100bf9593000ff9593004f794d4304f794d3104f794d3004df94d534fff94d5404ff94d5336ff94d5129ff94d5004bfd955304ff94d4333ff94d4125ff94d4004ff94d3104ff94d301cff94d2018ff94d1000bf9592000ff9592000bf9591000ff9591002fd9454102fd9453102fd9451045f79454302df945514dff9455449ff9455302ff9455127ff9455002bfd955145ff9454302ff9454123ff9454002ff945311fff945301bff9452002ff9451074f79464301fe9414001fe9413001fe9412001fe9411044f79414301df941504cff9415448ff9415340ff9415235ff9415101ff9415001bfd955044ff941433cff9414232ff9414101ff9414038ff941322fff9413101ff941302bff9411201ff9412001ff9411073f79424337ff9915105bf9915136ff98d5104bf98d5135ff9815101bf9815143ff9915205bf9915242ff98d5204bf98d5241ff9855202bf9855240ff9815201bf981524bff9915305bf9915349ff9855302bf9855348ff9815301bf981534fff98d5404bf98d5404f795a434dff9855402bf985544cff9815401bf98154
  | 1 => 0x237ffd09512affd095003bfd894205ffd094303ffd094205ffd094105ffd094003ffd093230ffd093121ffd093003ffd091203ffd090219ffd091000bfd893100ffd893100bfd893000ffd893004fbcc93204f7cc95304f7cc94304f7cc9304fffcc95404ffcc95303ffcc95236ffcc95129ffcc95003bfd893204ffcc94303ffcc94233ffcc94125ffcc94003ffcc93204ffcc93104ffcc93003ffcc91203ffcc90218ffcc91000bf8991000ff8991002fdc495102fdc494102fd8851002fbc491245f7c49434dffc495449ffc495341ffc495202ffc495127ff8855002bfd891245ffc49433dffc494202ffc494123ff8854039ffc493202ffc49311fff8853002ffc49121bffc490202ff8851001fe8815001fe881402bfbc091201fb8812044f7881434cff8815448ff8815340ffc095235ff8815101ff8815001bfd890244ff881433cffc094232ff8814101ff8814038ffc09322fff8813101ff881302bffc091201ff8812001ff8811006bfd59201effd592005bfd19201dffd192004bfcd9201cffcd92002bf985201bff9852006bfd59122effd591205bfd19122dffd191204bfcd9122cffcd91201bfc19122bffc191200ffd8d5400bfd8d5400f7d8d5100b7d8d5100ffd8d5100bfd8d5100ffd8d5000bfd8d5006f7d4d5347f7d4d4306dfd4d5106ffd4d5404ffd4d5306ffd4d5106ffd4d5004bfd8d5304ffd4d4334ffd4d4126ffd4d4004ffd4d3104ffd4d301effd4d201affd4d1000bfd8d4100ffd8d4100bfd8d4000ffd8d4005f7d0d4305efd0d5405efd0d4105ffd0d5404ffd0d5337ffd0d512affd0d5004bfd8d4304ffd0d4305ffd0d4105ffd0d4004ffd0d3104ffd0d301dffd0d2019ffd0d1000bf8d92000ff8d92000bf8d91000ff8d91002fd8c55145f78c54302f78c5311ff78c5304dff8c55449ff8c55302ff8c55127ff8c55002bfd8d3145ff8c54302ff8c54123ff8c54002ff8c5311fff8c5301bff8c52002ff8c51001fe8c15001fe8c11044f78c14301f78c1304cff8c15448ff8c15340ff8c15235ff8c15101ff8c15001bfd8d3044ff8c1433cff8c14232ff8c14101ff8c14038ff8c1322fff8c13101ff8c1302bff8c11201ff8c12001ff8c11006bfd593131ffd593105bfd193130ffd193101bf981312fff9813106bfd59323bffd593205bfd19323affd193202bf9853239ff9853201bf9813238ff9813200ffd915300bfd915300ffd915100bfd915100ffd915000bfd915005f7d514306efd515406dfd515106dfd515005ffd515406ffd515306ffd515106ffd515005bfd915405ffd514305ffd514105ffd514031ffd513122ffd51301effd51201affd511000bf9193100ff9193100bf9193000ff9193004e751a4305f75524304f790d5300f75464300f75424304f755a4304b7d914304f751a4305f7
  | 2 => 0xf1815101fe1415044f71414301df141504cff1415448ff1415340ff1415235ff1415101ff1415044ff141433cff1414232ff1414101ff1414038ff141322fff1413101ff141302bff1411201ff1412001ff1411044f71814301bf1814344ff1814301bf181423cff1814201bf1814132ff1814101fe1014044f71014301ef101404cff1015448ff1015340ff1015235ff1015101ff1015044ff101433cff1014232ff1014101ff1014038ff101322fff1013101ff101302bff1011201ff1012001ff1011001bf1813238ff1813201bf181312fff1813101fe0c13044f70c14301f70c1304cff0c15448ff0c15340ff0c15235ff0c15101ff0c15044ff0c1433cff0c14232ff0c14101ff0c14038ff0c1322fff0c13101ff0c1302bff0c11201ff0c12001ff0c11001bf019122bff0191201fa081202bfb0091201fb0812044f7081434cff0815448ff0815335ff0815101ff0815044ff0814332ff0814101ff081402fff0813101ff0813001ff0812001ff0811001fe0411001fd0411044f7041434cff0415448ff0415340ff0055235ff0415101ff0415044ff041433cff0054232ff0414101ff0414038ff005322fff0413101ff041302bff0051201ff0412001ff0411000ffd855400bfd855400ffd855300bfd855300ffd855000bfd855006fdd455147f7d454306dfd455406dfd455306ffd455406ffd455302ffd455106ffd455002bfd855147ffd454302ffd454126ffd454002ffd453122ffd45301effd452002ffd451000f7d854300bfd854300ffd854300bfd854000ffd854005fdd054105e7d054305f7d054305efd055405efd054305ffd05544bffd055302ffd05512affd055002bfd854105ffd054302ffd054105ffd054002ffd053121ffd05301dffd052002ffd051000bfd853000ffd853004fdcc53118fdcc51004f7cc55304f7cc5434fffcc55404ffcc55302ffcc55129ffcc55002bfd853104ffcc54302ffcc54125ffcc54002ffcc53104ffcc5301cffcc52002ffcc51000bfd852000ffd852001fe8415001fe8414001fe8413001fd8411044f7841434cff8415448ff8415340ffc055235ff8415101ff8415001bfd851044ff841433cffc054232ff8414101ff8414038ffc05322fff8413101ff841302bffc051201ff8412001ff8411000ffd895400bfd895400ffd895300bfd895300ffd895100bfd895100ffd895000bfd895006fbd495247f7d494306dfd495406dfd495006ffd495406ffd495303ffd495206ffd495106ffd495003bfd895247ffd494303ffd494234ffd494126ffd494003ffd493231ffd493122ffd493003ffd491203ffd49021affd491000f7d894300bfd894300ffd894300bfd894100ffd894100bfd894000ffd894005fbd094205f7d094305efd095405efd094005ffd09544bffd095303ffd095
  | 3 => 0x4102ff5454100ff5414100ff58d4105ff50d4100ff5814106bf1594134ff1594100ff5594005ff5514000ff54d4000ff5494000ff5454001ff5414000ff58d4005ff50d4000ff5894005ff5094000ff5854005ff5054006bf1594026ff159404bff1915305bf1915337ff1915105bf191512aff1915005bf1915005cf1515405ef1515405df1515405ff151544bff1515337ff151512aff1515005ff1514305ff1514105ff1514000bf4d92000bf4d91000ff5513100ff5593104ff54d3102ff5453100ff5413100ff5193104ff50d3102ff5053100ff5013130ff1513100ff5813106bf1593131ff1593105bf1193130ff1193100ff5513000ff5593004ff54d3000ff5493000ff5453001ff5413000ff5193004ff50d3000ff5093000ff5053001ff5013021ff1513000ff5893004ff4c93000ff5853004ff4c53006bf1593022ff1593005bf1193021ff119304fff18d5404bf18d5400f718d5104b718d5136ff18d5104bf18d5129ff18d5004bf18d5004f714d5304f714d4304df14d534fff14d5404ff14d5336ff14d5129ff14d5004ff14d4333ff14d4125ff14d4004ff14d3104ff14d3004bf18d4133ff18d4104bf18d4025ff18d4004f710d4304ef10d434fff10d5404ff10d5336ff10d5129ff10d5004ff10d4333ff10d4125ff10d4004ff10d3104ff10d3000bf4991000f750d2000ff5512000ff54d2000ff5592000ff5452001ff5412000ff50d2000ff5192000ff5052001ff501201dff1512000ff4d92000ff4c52001ff4c1201cff14d201cff10d2000ff5852006bf159201eff1592005bf119201dff1192004bf0d9201cff0d92000f750d1000ff5511000ff54d1000ff5491000ff5591002ff5451001ff5411000ff50d1000ff5091000ff5191002ff5051001ff5011019ff1511000ff4c91000ff4d91002ff4c51001ff4c11018ff14d1018ff10d1000ff4991002ff4851001ff4811006bf159101aff1591005bf1191019ff1191004bf0d91018ff0d9104dff1855402bf1855449ff1855302bf1855327ff1855002bf1855002fd1455145f71454302df145514dff1455449ff1455302ff1455127ff1455045ff1454302ff1454123ff1454002ff145311fff145301bff1452002ff1451045f71854302bf1854345ff1854302bf1854023ff1854002fd1054145f71054302ef105414dff1055449ff1055302ff1055127ff1055045ff1054302ff1054123ff1054002ff105311fff105301bff1052002ff1051002bf185301fff1853002fd0c53102fd0c51045f70c54302f70c5311ff70c5304dff0c55449ff0c55302ff0c55127ff0c55045ff0c54302ff0c54123ff0c54002ff0c5311fff0c5301bff0c52002ff0c51002bf185201bff185204cff1815401bf1815448ff1815301bf1815340ff1815201bf1815235ff1815101b
  | 4 => 0x44ba5374b6fd55356d8cf2000127f67000001e15f749dbb2fc800303501c2800268003bc000540001a77aa000000143870595f894927b382b2c75b3d1eb8a8bc71a57409ef9909abdd85954ebdf8796b06c468c7dd1b74001dc2888009a82fafebf70bf108002d485b1db2a2c4265ef4aa55d00000287e5a8e9a090a26c06041f02010039062738196908010700230004250d2f1201180c11040a0005124b01413e072d389e00980a14012403350716003506380b150117002d00000e0101074f0513010a1500000801073a0004091f10131105200000010028100009002f14002504030301063c04021602120d010006160603001a38451003000425000b3900001d010c080804020603180004300b031f0b91120f0301021a3417007a6e0814280600000301004803020002e4100007030308000f00100117090202080019051103000200050102000300000b1f330d3a1a771f2b0a00090004000022051103100300190000060202000c00010015050902010005170a000100300c2e0e02040200021668240600001313170906021402000004010c690600110d101b0802074d0005000105070e050012070500010617640219005e030d030003040f041100000001000074030b070001072322040200011306080521000c12041a08002900050b01000b010200110101020f0003090436000a030705060e0100012c00390f1a0431010017000b020a3507010b011b020300010148030203080200000200000008000609180105090307001d130a04260017130009053009000c030712000700230119000003005901020c0600280509000d00020301020a190707011e03000a02070210030111010b02000004030901000005200001050300010d00060205220009010a00030102010000fd5454100fd5453100fd5451000fd5051000fd4851000fb5494200fb5493200fb5491200fb5091200fb4c91200fb5490200fb5090200e750d5400e750d4100f75594305f750d5400f754d4300f750d5100f750d5005b751a4300f75854300f75814347f71594305f750d4105f750d4005f71514300f754d3100f750d3100f754d3000f750d3000f74c93000ef5514300ef5514100ef50d4100ef5514000ef5094000df5515100df54d5100df5515000df5495000bf5594300bf5594100bf5594000ff58d5400ff5855400ff5815400bf5593100bf5593000ff5915306ff5515300ff5855300ff5815300bf5592000bf5591000ff5915106ff5515100ff58d5106ff54d5100ff5815100ff5915006ff5515000ff58d5006ff54d5000ff5895006ff5495000ff5855006ff5455000bf5193100bf5193000ff5594305ff5514304ff54d4300ff5454300ff5414300ff5854300ff5814306bf1594347ff1594300bf5192000bf5191000ff5594105ff5514100ff54d
  | 5 => 0x672c6d258008b0cbf3226a6d419b5b0005cd1880f50aa0eff487ea0001ac8e36d2132fd6ad18eb806c14900074b9730e6283c49d2ae078a91eb00037263552b7b76ca66b3c6e69eccb5da886d609d112635f1cd00020100000000006254335294a07141e96e8cf800000c05f98003b60000006243e10e19c3c20861401dbe3b15fd37174279b12b849dd464fb2c044f3a2c68768b83db4cc31fa2abe8b9b03631603bd038b5297a31c6bc17fbdeba39372296bb249f880d9c006070012288e0007b20482500f3390458ccfe37c1a15c2434856ec005710004444aaed472003a684700085c00000904001fdbefd8083d24cf3a44001230ba7adbf2aba44046404a85531e0c7289a0c4370f42440a93386219508ed146e8cb0e97d3427933a34de9b4a000476241b9caf7f0efe43661198001691620fcb6af3e99d7bc192b1714ed7d06a838b4d2e19f4146494872b2de0b028ba218c810fb9cb76df5e8d6d73cee80b3af87488a4b437ee9d3083514430c082eacd60bc8592f1afa22b6ed56d22ae4152e4136a621533b8404233017a483e97e949f46f1ac489346c78973abdefc5ee3a5c28e7fbc292751b2824adb0694046e2a555afe19453324fca2ca2e70e6e71dce68b339972f9034518f434cd8b636d6d07e4381cc2846df6ca758926e07bb5a215af0d5e654e6b560615373a03ef9e30e91a38517263ddad1ac2789a85f70582e70316c46ae15644330c248b667809853370b57caa8f0c2a9c600384a6450237e51cde76a00106ac6038c5045057f64d458100045e0000000068111acd5f21d814272855a625d827e469c9403bf000925d614b77276d88989774c55929538003043c400679d8d6d37c4b55f137f6517c773ce03a62e6692b10eb9745abd489000656003d419671400031becddc80eca4e2ad4ef00049a000001f12fe001662265cfaa0000002e074c00352c5e000cc1f2a4166532c33800c8f192580e4040c5cf213da580e9fd380219abeacc36b2b23cd99b8d560013eafc6b4ee8c069636c0037c800980d2c00000ec5d9ad560c8d5898a260a842487072106e39eb9355eb914bd883d7766e1899d52e7a001ccaa3de54ec0dad56a12523f757008f51e50002989e1a49ea7b547c9ab09d45c5968d3fc6137101426ea5554858c80b2d5981a2bbc5365c20b3dea57a1206a440a2ba70001da1870480000092b9cac27682a985b2153cd74a512f02351205834001967ae01099f35c7d0149920000000028eac321f7c6a85c0a889eac17a88c4b2001198000000000027cf829a5e729e3e41040b57b20e0002ec00000324002931e600000189800accf26a15919d3b0800138010c103863cbfd3a0005ec64b8d767091169758000ea2218e99fa7a71eea9e0c5a0014e5e38000012a3beee8d58bb3dc00047cd1dd3ca4240e6f272bd1c
  | 6 => 0xbe2fd344003de4809c14ffb0f18585df322531d50683ebe948446716610652050d893221028a90d9a777892562f66002f590e8748de2b1bd5792d20356ec7c174520a69ac6ab023cf3997b5bbf23001c899dc95dd4c014d68000000000000d420000070cc252ab45404de9082d81aed9ee579e1fc75d7ebd882a830daeec6a8d546825d5017e1ab9ffe6eabe34affb0764c9f34de6b5e08a8b40d6839c11a7ca94aad4f6f2bf2fb0659c0f2a356368b602e50b6f6c9ab7a67428c670db90397eb889c08c5314f8cb7eb9b2448e320955171ea3b1f2e271c6d336141358a47cc36676a07f719f0dc17a27f89ba50c00fe7d6f059e8bfd0c3bb6f1e63b1cddc68aa2a8dddba92da0091f895d8139e42348899e2c45aef5f1f50ff20582250e78af47590b0000ac48c295289c2c801eca043cba02a7ab94ed205416dbb764138a7e7a4be40062c1deae90074c760db99eaf200060e04800d8a219d12060a3c40006c800069c00000000003bd0009318c80018a770001a6a4777a0000045cf2c002fa800c90003899b4b598b6a4e72d102004733793d1c18b23fab0a93893b7ba00017d245dc0002cb37a000000055f633c418ecea7800d49c4a523e0cbac54c4ac6000006e98634d010cdb05cea1a5689bb800166bb23104da0ac68a5d36896e7c939c34421e897e5e000000f353086f488077eec003fc000d0d79cfc7fc000bd0000019123600100000296b820000000000049101c00126e58000001ec26200144e0662301608297c2264f0a375a82bd2c2f42375d27cb9e9683d1773000ebd6494628e6b64211e2f10ed50db1c696d8002569000000018c361001088003315c80000076e000da3128000000000000000000157bb11b49c982e1a345ed9162b4ea05a8004965653fe76000000df000536e001b8000fca7bb8832601bc0c9dd04f6e8dca8bfce715dc38fc5a99db3beadf80bcd3aa423e02576227758b7b01c9480001d00022700075eca400000000001a653e824002574fd00116494650448f10002eacbd9364665273c00987b7ff0d8d9e460b0000000e9ca646f0c000000dfae5843c6001195833a95de87185697a54b21d25a800128acdf8ece947934792eeb6800059e0007970b0000004c1edfb4000000d0c60bc20000b000000001170006dba19ea905000e0c6516029c450000000000022a74720f4dc84e030457290453800142413b924bc000007a471c30850390806780000000017ee39360bbe76ac10ab46c06b723ad170563ab1f28a044c9ca0428216a558c627fcac26adc2554369ada291c945af720eb7ed67ab621174904c6a42b80010d78a000000000007340000006b1f000000315000c75bed4799000266586a240027d89c072220e01bcf0830d00ef379822780e6adb0000001dee3000000000d34ca8acd204600000054c
  | 7 => 0x3c884c3ed748ca98f71920d6ca3a56ce04f8b44c41a4cfa3ac2d8250000007c6000000000000000000000056ab4800684001770000004ec2dc351880000003c6b951646d4d2dc003dbd4b7294eb49000e04001e58000007391c116000000003cd0000004d0fed1ccf000000be7c9000000000002858000008f5bde98dce47873000e5dee800000b00713a1800739411cfe605399eeb0c0c000dd99b000cec14c96213a617940007cd38cb599877bc600114f87de01e814800900cd400260dfc558e47071804967d09600040c003f60016dae8b467db432a35320c1b5333000000001acf88286fc4a347abb4f439f6fa8f15b0583e60000de58de42454a534c38001f00fc8f6c200fa4b9c54b0a18000309ee8c800379b7961000164a4a38560690743e789d6b8eb515f7fdcca0b0a019605cfd4192e54f87da7eb90001dce3424e84097cff07ad300000306c9b4981198680000c9e556000d18709140002853c10902b68b40f5d6626580016bbdc1180035480000052f5f32846632d2cc2e365900b90457d16e0007
  | _ => 0
def g6K6 : Nat → Nat
  | 0 => 0x64c0af7d2824c88227da5050d2001ef6eaa8240037e01e5648113ed282868800f7b755411001bf00f2b2216de794143552c7cf28286a0a275e5050d5044dbecaa1aa0033f01e56441337d286c0aa246fa50d815340df4a1b02a46bbe94360546277d286c2a0436fa50d853085df4a1b0a4127be943625023f7d286c49831efa508991069dbca1b1aa337be94363501c37d2846c9033efa508d91073df4a123260e7f69412090dcfed2822121b9f5e505424373bbeeaa8486e3be94246481ab7d2848c88225dc0795943019f80f2b286033f01e56508067e03caca080cfc0795932019f80f2b262033f01e5644802ef0bcaca1804fe1795943009fc2f2b2800b7d85e56504dfcf32286a882e9e6450d5105dbcc8a1aa20b6f9d15150c16bf2bec2aa3e4fe179594100dbcc831aa201b799363544df5f326c8a882dde7454643009fc2f2b260097d85e564c462fb39aa288025de735454304afcafb0aa6f13f85e564c4db6f31ec6a8804fe179592001bf4e0a8a80037e9c1514c006fb0bcac88226de6050d51019fc2f2b22001b798063544d77d306c0a8806de60d8d5173bbce0a8c86017789e5650c027f13caca1804fe2795941009fc4f2b2800b7b89e56508176f32286a902dbe745494005afcafb12a8fb3f89e565090f5f326c8a902dde7454a43009fc4f2b262013f89e564c012f713cac99025de735494304bbce6a9260f33f89e564c90b6f31ec6a9004fe279591002bece2a9282057d9c5524400af713cac8922ede6150d52029fc4f2b22483bd98761549d2ef38aa52180dfa70549402bbdce0a9224037b89e56409136f30286a900d7e57d8950019fc4f2b20481be98360549ceef382a52182cfe7455920049fce6ab240053f9c556480167f3a2ac89024fe7355912019fce0ab224013f8de56504027f1bcaca002dde379594305b7ce8a9a82fd3f8de5650d2f5f326c8a9804fe3795920009fc6f2b2208b779c55350c0aef1bcac988fdde7154d3002afcafb1aa2053f8de564c5277b30ec2a9d075e57d8d51a0dbcafb1aa2037e9c15344112ef382a6a180dde3795930019fc6f2b26091be9836054c167f3a2ac9880cfe7055931059fce8ab264053f9c5564c8067f382ac99004fe4795931009fc8f2b2609fe79cd5450c12cf23caca1825de479594304bbce6aa26209779cd544c012df23caca1824fe47959434fdbcc7b1aa8fde791e5650c027f23cac90004fe479591002bece2aa2216fe7985435500adf23caca08157e57d9151029fc8f2b2829bbd9876155006fd382a89000dfa7055110b6f3cc0a1aa8036f91e5650006bf2bec8a800cfe47959404cdf4c1b02a8093f9cd5650412ef3b2a32180cfe7055941049fce6ab28409779d95290c0a7f38aaca100cfe705594245bbce2ab286053f9c55650d12ef382aca180cfe7055943
  | 1 => 0x5450d1087f3ca9b0a870faf9536150d475f2a6c2a048f9e54d894391d7ca9b1286cbaf95362505575f2a6c4a034ede54d8d5168d7ca9b1a82b3af953635012f5f2a6c8a99bebe54d91512ad7ca9b22a0f5e711e5650c027f2ba6c90004fe574d91000eeaa32b26201b750e564c403aea9cac988067d56959316ecfaa72b262f19f546564c5e27fbaaac98bc67f51959316ecfea72b262639fd5a564c5bb6f21cac9882cfc479593100ef2a12b26001be442564c0036ea1cac98006dd329593000ebaa72b260019f55a564c1873ea9cac983be7d5095930779feeaab260ef9fd42564c1df7d084ac9830edf329593061cfea72b260459fd5a564c1876f21cac9802cfc479593036faca6a8a6285f394d524c8b3e729a648927f9e535514333f3ca6a1a8267b794d464c4976f29a8c980275f7554d4304bb86f2b28639b794d36480636f29a6c880275f7554d3178bb86f2b26209d7dd5534c1deee1bcac983bcfc37959308adbca7b0a86a1b794f614c2576f29ec4a1b26de53d893154dbca7b12609fb794f63550db6f29ec6a894ede53d8d506bdbca723262bbb794e464c0127e1bcaca0824fc3795940009fcae9322001bb50a5640803b6a94ac81006dd439592000cfaad2b240e59f54256481ca7fbaaac90397e8209592060cfea52b2043d9fd5a56480036f21cac90396fa4095920059f88f2b240093f0de56480037ca04ac88006f9309591000ef2a12b22001bd50656440037a90cac8800775519591000dba872b220019f55a564417f3ea8cac8836e7d50959106d9feeaab220db9fd42564417f3fa8cac880d67f56959105fdec432b220dbbe8c256440036f21cac882fef641959106ddf4812b2200b3f11e56440127e1bcac8820fe651549123dfcca2a122473f99453244917cb28a86a0a2fd6515854349faca2a9a628bf5945434c537db28aa8a0a2fb65150d4145deca2a326247bd945464400bbbbaaa2a0815f417959411fdeca29b22005dddd5514c40afa0bcac988def6514991045faca2a1a2005dddd551441b6fa0bcac885bf9e5150d5445f3ca2a1a828bd794543545176fb2a86a8b6cfc179591013ebca231aa227b7d9463545377b28ec2aa24ef651d855327deca3b0aa129bd94762506437b28ec498a9ef65189910a0ebca3b1aa341b794763546737b28ec6a0abef6518d91074deca323262e9f59451090dd3af28aa321ba5df75546435bdeca3232208b7705e5650c0a7e0bcaca1814fc1795940029f82f2b260053f05e56480d7f9282a288197f250505102bfe4a090a2081fa94152408f3f52828481227da505814348fb4a0a9a6089f6941434c0e3ed2826498267ba50551403cf74a0a128089be941464c0f37d2828c90196fa505191001ef6eaa8280037e01e56500e37d2826c9017efa504d91001ef6eaa8260037e01e5
  | 2 => 0x93f9cd4648012ef3b24121814fe7151920069feaea3224093f9cd4644812ef3b2252180cfe705191200bbc6fb22a201378df64544036fb3a86a8804fe37d915100dbc8fb1aa201b78df64544036fb3a86a8004fe37d915047f3eaea1aa965e7d5d435051f6fab2aca1835de37d915347ebeaea1aa34577dd95350c1adf23ec6aa0367f5654543a69fc6fb22a6edb78df6454c036f3b28690004fe379192000dbceca1a20013f8de4644117eb38a86a8816f66154543b7f3ce2a1aa88be79c543505176f30ac2a1806de615814345dbceca1a6205778de464c47eef38a8698015be47d8d41029fc6f232628bf59876150d177b30ec2a1a2ede61d854300dbcc3b1286e9b78de464c513ed38286a800efa605414344fb4e0a1a20037e9c143442dbcf38286aa58f9e7050d4144dbcc0b028689b79d9434c006ef1bc8c9800cfe379193044fb4c1b028689be9836050d136f306c0a1b9ede379193047bbeaeb0a860d3fd5d464c512ef382c2a180cfe705193147bbeaeb12860d3fd5d464c916ef38ac4a1814fe715193244bbce0b1286033f9c1464c802ef2bac2a1804fe575193100bbcaeb0286013f95d464c0038eaa4aca1a3f9d549594300f3a832b28601b75865650c036eb04aca18075d57959437aebaa92b28601d754e5650de9eea1caca1a3edf679594300dba632b28601b74c25650deb6e9bcaca18073d549594300d7a832b286019f55a5650deb3eaa4aca1bf67d53959437e9feeaab286fdb7cde5650c036fb0caca1bd79f41959437ad7e832b286fdb7cc65650c036fb14aca1bf6df329594347dbea72b2868fd7d4e5650dfb3fa9caca1bd75f54959437acfea92b286fde790e5650dfb6f21caca1a3edf569594347ebead2b2868f9fd5a5650c027f2ba8c90004fe575191000eeaa32b28201bd44256504034ea1caca08079d43959416fdba872b28201af50e56504039eaa4aca08067d56959416fcfaa92b282f99f54656505f27fbaaaca0be67f51959417cdee252b282dfafd0e56505bf3faa4aca0b7ede439594134cfead2b28201de54256500037c904aca0006f9109594062dba872b28001af50a56500039eaa4aca00067d569594062cfaa92b280f79f54256501ee7fbaaaca03de7f50959407bdf4212b280c5afd0a56501ef7d104aca03167f549594062dbc872b2804d9fd5a56500dfdb2a2a2a08cfb6545051043f5ca8a92845beb9514244877d72a2848102f1f6550d544bf3ca8ab2860be7d95435512fcf2a2a6a19bf9e5450d512af3ca8a1aa00b6711e5650cc3cf2a2c2a190f9e545814305bb88f2b28661e7951434c487cf2a28698186be545193121d7ca8a32600bcfdd55450dfade23caca18eebe545192019d7ca8a32200bcfdd554505f2de23caca082f3f75551407bb788f2b280f73f11e5650077cf2a286900cf9e
  | 3 => 0xa894ede43d8d5033dbc87b1a824bb790f63500736f21c6c900c6de438d910a6db86fb22a66f77dd15190caaefba2a1219bf5f54546432aebea8a8486e9b70de464c5cf6e1bc8c981b6dc7654643049b8eca8c86093f0df64544036e1bec8a8825dc7654643049f86fb22a009771d95090c027f23a4c88006ed529190200f5a852320401a750e46480776ea1c8c90006bd439192000d7a8d23240e3af50246481c67fba28c900079d439192071fd04123240b9afd0a46408775fa348c900eebf43919201ddbc87232400d3f15e46480127e1bc8c90025dc764824300df2a12322001ee50246440037aa8c8c88006f5219191000f6a832322033b750e46440035ea348c882debd41919106ad7a8123220d53fdd146441ab5fa048c882debf419191019d7e8d23220b7bd88646440676f21c8c88034fc5791910049f86f2322009771d91090d07f320aa4891efe6415091239fcc82992248bf5905435440bdbb22a2a0a6f76415515149eec82a9aa24fbd905564400afa0bec8a889fd64118d511bdec82932208bf5905434400bdbba28288355f417919106a9f82f232209bbd9076155117eb20ec2a1a2ef641d854323dec83b0a8131bd907625454f7b20c4c88507d641d8d51a0dbc83b1aa2e9f59055190dd3eb20a2121814fc17d9153029f82fb22a0053f05e464c1d3ea0b22121814fc179192035fe480a8a2065fc90141440aff92024288207ea40549023cfd480a120489f69014354007ddb22a0a02677a405515040ef480a92a081be90156480d77d202ac8800df807d91502bdf4809322089f69014348007ddba2809000df8079192044fb480a1a2003eedd14044006fc03c8c8800cfc07919104cdf481b02a889f69036050d137d206c0a19e6fa40d814232df481b028319be90361542177d206c2904befa40d895063df4811322001b790363545cfed202a121b9fda404824373fb48088486033f01f6454c067e03ec8a900cfc07d9151019f80f23264033f01e464c4067e03c8c89004fe17d9153009fc2fb22a00d7d85f64546cbcfab286a0835be47d8554a49fc2fb22a2013f85e464c062fb39a82880259e47d854333f3cc6a1a8209b798d5350412ef23ec2a1825be47d8543749fc2f2326315e791f6150ccf6f31ec6a08c7d61644243009fc2f2324003be9815050406fb0bc8c8858f9e6050d41019fc2f2322065be98360504027f13ec8a9804fe27d9151009fc4fb22a00d7b89f645481adf23ec4aa0367f5654142a59fc4fb22a4013f89e464c4027f13c8c98026de6354d4204bbc8fb128609779cd424c1d67f13c8c991f6de63d8d42009fc4f2322005bd985515080afb38a8488015ee2791912029fc4f232247bbd98761508077d302a0a115dee705091201bdc4f23204036f91f62500067f13c8c811e6fa60d8142069feaea32400
  | 4 => 0xfb22a013d7d50635454b3faa6c2a83367f54d895156cfea9b12a0d3d7d5363545a76faa6c6a8804fe474d920009fc8e9b22001bd546464c4034ea1c8c988079f745854300dbaa72326261b750e464c403cea1c8c98806bd46919316bd7a8723262e9af506464c5d27fba28c98ba6dc319193174d7e8323262d7afd0e464c5d36fb1c8c98986bf4691931069f8af2326201be542464c0037c8848c980069d439193000f3ee8b028601b754e464c0876ea1c8c98006dd329193000f3a872326001af51a464c1775ea1c8c9839ebd4091930739fee8a3260bbb70c6464c1cf6e1848c9839ebf409193073df42123260bbb7cca464c1775fa1c8c98006de319193073dbec72326043afd1a464c01a7e2bc8c981bfd5415464336fac86a8a6201f55451090c67eaa0a2121807d5214424336faa2ca8c8687f35095290d0be721aa499007cd5244a432df9a848948659f390d3244803e6a9205218efcd4240a4342f9a4ca948659f34991290d3fcf21aaca18279f6454d4336f3a8ca8c8653e75195090ccfcf21ac2a192f9e435814337ebaa8a8c866dd790d53544abaeaa2a1218075d525424336ebaaca8c869fb790d5650cdeeeba2a321955dd745424336dbc86ab26253b790d564c012ee1bec8a9805dd574824300bbaae884866d775d95190dd2efba286a894ddd765424373bbee8a1aa0e7370de464c0cf6f21a8c9892ede43519301dbba8e90486337751d1090cdaefbb2a32194ddf765424336ebeaca8c860b771d15190c16ee3a2a1218e6de434d92018dbc869b22009e7dd1434c5d2ee1bc8c988279f7450d3073bb86f23260e73f0de464c002ee93a21218e5dd76482431cf3a8c90486e777dd143481daee2ba41218e5df764824305bb88e9048631775d91090c63cea322121b9ddf7450d1076bb8ae884863177dd91090c16ee23a2121ba5dc715424374fa8a2a8c86e9d71455190dd3eb8b2a321ba5dc714824373bb8e0a9486e7771c15190dcfec282a121b9f5c505424373fb60ca8486e7f6c191090dceee03a2521b9fc82048243bcf980489486e7f30812090dcfec0822121b9fd410442438edbc87b0aa91bb790f6154c02efb8aa121bb7d7515464374bbee2a8c8715e790f6150e2b6f21ec2a1a8ede43d854050dbc87b0a600177dc52090dcfed082a121b9fd6104424373bbee28848735b790f62552676f21ec4a9805df725464300bbee4a8486edf3d495290ddbafa92a121baddf7254a4395f3c87b12872bb790f6250d976f21ec4a0aaede43d894064dbc87b1262a9b790f624c002ef13a2121ba7d7125464374fac4288486e9f3c491290dd2efb922521b9fda2054243bcf9e0489486e7f38812090dceefb920521bb5df574824305bbe8e90486e9779c52090ddaefaba252182ddf4744a4373bbe0e894869fb790f63550db6f21ec6
  | 5 => 0xbb18aa6a8815f417d8d5113face231aa35df38c5524c8e7e718a64895bf9e315514345f3c62a1a828bb7d8d464c4036f18a8c98006de314d9201fdbec6b0262cf3f05e36441277b18ec2a9a2fd631d854345dec63b0a868bb78c76150c7feb18ec2980fef631d85301fdbc63b0a6001b78c76250e436fb1ec498806de31d893000dbc63b1aa941f58c763546836f18ec6a8806de31d8d50029f82fb1aa8053f05f635400a7e0bec6a0014fc178d92036fb4e031aa26bfc8c151440cbf9182828815ff2304851044fb460a828603f6d8d504c133bd182a8a82077a305495035df460ab220037e01f6354113ed182868800fdb734c11001bf00f1b2216de78c15450ec7cf18286a0a26df6351930019f80f1b22091be8c36054d13ed186c0a1a26fa30d814344dbc61b028679be8c360508e37d186c09917efa30d81318cdf461b0aa001b78c363544067e03ec6aa00cfc07d8d52019f80fb1aa201b701f63544067e03ec6a100cfc07d8d41019f80f1b224013f85f63550027f0bec6a8035f617d8d5106bbc6fb0aa68fb7d59434c6827f0bec6a8b4fd617d8d51a0dbc2fb1aa2013f85f6350016ef1bec2a182ebf46551319c9fc2fb1a82013f85e36480077d302a098a26de6050d31019fc2f1b2205fbe983604c4027f13ec6aa004fe27d8d5100dbc4fb1aa2013f89f635401af713ec6a9035de37d895347dbeaca1a65433f89f63548027f13ec6a0804fe27d8d4005bbc6fb12860bafd19544ca767f13ec6a1004fe278d91002decc2a8a64057b89e36449176f30a86990fede614c132029fc4f1b22473bd987614c8077d302a09915dee704c91244dbcc0a1a6403778df624c0067f13c6c811c6fa60d8132069feae9b2400b3fd1d364800a7f38a6c90034ff574d912059fe8e9b224033f9c136448027fba2ac98804ff745593000f3ee8ab28601e750f6454c034ea1ec8a9a5edd43d915300dba63b22a601b74c36454c035ea3ec8a9bb6bd54d9153a6d7a87b22a6019f5476454e9a7fba2aca1d36dc53d915376cfea3b22a74db7cc76454e9b6f996c8a9bb6df53d9153a6d7e87b22a6013fdd156480027fba2ac88007b541d915100dea21b22a26fb750f64544039eaa6c8a8806bd47d91516cd7aa9b22a349af50764546927fba2aca0806dc63d9151a4d7e83b22a349bdc4b64544036fb1ec8a8807b940d915000df241b22a001be44364540ab6ea1ec8a80073d54d915000d7a8fb22a0bdaf553645428f5ea06c8a80067d52d9150a39fee8ab28147afd03645428f7d086c8a82f67f52d9150a3df441b22a06fddd5151504c7bbaa2a2988d777545451043edea8a928477dbd51524c8bbb7aa2a4890f76f545490237ebea8a1aa255d7d51435401b9fba2a8a88373f74551501ecfea8ab240359fd515644292be2bec8a8d1d7c57d9150a39f8a
  | 6 => 0x400dba6fb1aa93db754f635528b6ea1ec6aa006bd41d8d5400cfaa3b1aa89f3fdcd5650e8b9e2a6c6aa27edc31d8d549ecfea3b1aa945afd0763550027fb9aac90006df735591000bbee6b02a20177dcd61540026fb9aac88004ff735591000bbee6ab22001f55076354403ea98ec6a8807d510d8d5100ebaa9b1aa201d754f63544036eb26c6a8b4edd54d8d5100dba6fb1aa2d3b754f63544036eb06c6a8d03dd51d8d5169dbaa1b1aa341b755f63546826fb38c6a8806dd43d8d51a0dba83b1aa201b750363544036ea3ec6a8806dc64d8d5169db8a9b1aa341b74c763544036e986c6a8d04ff735593136db8c7b1aa26db714f63544036fa3ec6a89b6dc43d8d5100dba41b1aa341b744363546836e8bec6a8d07d451d8d51a0eb8a3b1aa341b714763546836e20ec6a8d06dc31d8d5100dba0fb1aa201b718363545a76e286c6a8806dc40d8d5100dbe0fb1aa26db70c363544036e106c6a8d06dc10d8d5169faea3b1aa341b7d4763546836fa0ec6a8d06df31d8d51a0dbc21b1aa201b7d8b63545a76fa96c6a8806df42d8d5136dbe65b1aa341f5c4b63546836f896c6a8806de20d8d5100fb261b1aa001be44363540036e9bec6a82d6dd53d8d5000dba87b1aa13fb74c3635427e7fb9aac9814edc31d8d509fdbe61b1aa13fbe84363540d3bba9aa2a09b77753545311aeeea6a8a208fe7d4d5450ecbcfa9a86a08375f7354d5147dbec6b22a68fd7d4d5150e82be2bec6a8cfcfc57d8d5036ebeae31aa341d7d4f63546836fa9ec6a8804ff7351920009fee6a322001bd5476350403cea1ec6a0806dd63d8d4168dba87b1a8339b74c763504036e986c6a0806bd54d8d419c9fee6a326267b714f63506736f98ec6a099edf32d8d4100dbea7b1a820d3f15f63504037ca86c6a0006f910d8d4000dbac7b1a80b3b750f635026f6e986c6a0006bd54d8d409b9fee6a326137b7cc3635026f7d086c6a0034fc57d8d4036f3e8e31aa26fedd0d5150467dba1a828802f9f635514305f3ee6a1a826fcfd0d54544ab9fa1aa8a81bebf43559414fb788fb1aa9396f11f635066e7e23ec6a0476bf43d855400dbe87b1aa20b3f11f63544036e23ec6a882cfc47d8d50009fc6e9322001bd45e364800376a946c81006dd438d92000dba6d1b240e1b74c236481c27fb9a6c90006f7178d92070fd0411b240b1b7cca36408736f9b46c90034fc578d920059f88f1b24001be5423644003ec9846c88006f5518d91067dea2f1b22001b750e36440036e9946c88006dd368d91057dba631b220cfb74c2364419e7fb9a6c880c6dc538d91057dee2f1b220cfb7cc236440637b98c6c880c7d7318d91057dbe631b22031b7cda36440636f9946c88006df538d910069f8af1b2200b3f11e3644117eb18aa2a1817d763545311ffac62a8a609bdd8c55454527
  | 7 => 0x43504dbaf992a6a8a7edf325594329dbe64ab26095770df6254c976f9928c98235dc37d89438fbb86fb12611f3f0df624c20f6f996c0a9c06df32d8143049f86fb12a8093f0df62544127e1bec4a8024fc37d8941049f86fb128001be54226440037ca044c8829ef9078991000deaa31322001bd5062644003f290c4c88006ed268991053dda4313220c7bb48226440036ea1c4c8831cff724191253de86313220c7bec1e26440037b98c4c8829eef2189910069f8af132200b3f11e26440127e1bc4c8813ff3125411023fe624a02203ffcc49304400bf3b12a289017e7625051245f2e24a1a828bf5c494354537db892a8a0a2fb71250d414deee24aa2a293ddc4953545377b892aca093ef6215591002be82fb12a247bd885464400afa0bec4a089fd71218d5102fcec480a248bf5885434418efa0bc4c8822fcf1250d12b7f3e24a1aa88be7c4943505176fb12868931cfc178991082dee25b02a2ffbdc4b60505277b896c2a9a0ef712d855245fae25b0a868bbdc4b6150cf77b896c2a11cef712d85321fdec43b0a6037bdc4b614080a7e0bec4aa014fc17d8953029f82fb12a08b7705f6250c0a7e0bec4a1814fc17d8940029f82fb126057fac0950448aff5812808900feb625412001fd6c4a024089f68814354133dd102a8a01e7ba20509404cef440aa2a081de88152541337d102aca000df807d895001bf00fb128155f9c095144aa7f3812828915fe620485102bddec4b0a0561f3c094344913e710286905b79e2050d54b1f3c40a1a8289b7d8943408067e03c4c88206fb02d81523cdf605b028471bec0b604c8aff58140c8915efb02819122bdde05032250bbbd8b614080377106c4aa00cfc07d8954019f80fb12a6033f01f6254512ee03ec4a180cfc07d8943019f80fb1282033f01f624c4027f03ec4aa004fe07d8953009fc0fb12a20d7b89f605491f6fab286900367f5655120979fc0fb12a0017781f6250c027f03ec4a1804fe07d894105bdc4fb02840bb7d1943480175fa32a89049cfe07d8940009fc0fb126209b7cd953480136f9b2869047cfe07d893002decc2a8a4005bd98541481176f30a869031cfe07899101bdecc3b0a40013f85f62550027f0bec4a9804fe17d895006bec2fb12a20d7b89f615491f6fab286890367f5655112989fc2fb12a2017785f6250c027f0bec4a1804fe17d894005bec2fb12820b7b89f61508176fa32868902ebf4655112949fc2fb1282013f85f624c0637b9b20289025ee27d853204dbe6ca9a2409b7cd94344a427f0bec49880efb065411201df60ca0224037d85e26441136f832868900cfe17899102bdf60d032240d3fd5d26440167fa3a4c88024ff374991000dbee6ab2820177dcd6155002efb9ac8a8804df735594100bbee6ab282013fdcd56504027fb9aaca00079d43d8d5
  | 8 => 0xf725594000f5a85b12a801db54b62550037693ec4aa4b6ed52d89549adda85b12a801e750f625526b6ea1ec4aa006bd40d895400cfaa1b12a89d3fdc95650a6b9e2a6c4aa276ec20d8954009fee4ab262013fdc9564c003e6996c4a9806ed27d895392ddaa5b12a733bb4cb6254c036ea1ec4a9806dd30d89534a9fee4ab264013fdc95644003f290ec4a8806f541d895100dea21b12a201bb49f625459b76a96c4a8cc6ed21d895100dba87b12a2019f55362546627fb92ac89006dc63d895198dde43b12a201fa48362540037ca06c4a80076d52d895000dda4fb12a0adbb54b62540037690ec4a84beed20d895000dba87b12a0019f553625425e7fb92ac81146ec42d895028dde43b12a04dded49505008bbda92a0981477b52541201aef6a4a82208ff3d49435481bb7b12a8a90376f625415247e3ea4a1aa88fe7d4943552cbcfa9286a0a3f5f5250d5046dbec4a1aa48fcfd495450d3b9fa92a8a11a73f525514126e7ea4aa2804d9fd49565013abe2bec4aa4bd7c57d8950979f8afb12a1039fd4b6055002efb92c2a1804ff725193100bbee4b0286013fdc9464c003e693ec4a1c8fcd42d894300f9a65b128601bb58b6250e4776a16c4a1caeed32d894300f3aa9b128601e75076250c036eab6c4a1806dd53d894300dbac1b12868cf750f6250c036e986c4a1a36dd37d894300d7aa9b12868d3fdc9464c91b6fb3ec4a1a36df37d894300db8c3b12872bb70c76250c036fb06c4a1c8f9f41d894347bb8afb12860d3f15f6250c027fb928c88007e521d894100deaa3b128201bd443625040376b16c4a0b2eed42d894194dda43b128201e750f62505976ea1ec4a0806bd54d8941949fee4a322529bbc87625041a7e2bec4a0807e920d894000df2a1b128001eb50b625000376b16c4a02aeed42d894000dda65b128001bb487625024f76906c4a02aedd43d894000d7aa9b1281273fdc9464089376296c4a0126ef21d894000ddea5b12800d3f15f62500abdda12a0a0127bb425012019f7684a02200bebd895450817d7b1280a1235dc47d89434ee7e84aa2a46fcfd0954544ab9fa12a8a8156bf42559404eb788fb12a9276f11f625024e7e23ec4a0426bf42d815400dde85b12a00b3f11f6254c167e23ec4a882cfc47d8950009fee49b22001bd547624c40376b16c498b26ed32d893190dda43b126201b754f624c4036ea1ec498c84ff724d91290de863b126321b70c7624c5937bb0ec498c86ef21d8931069f8afb12620b3f11f624c4037ca86c498007cd32d893000ddac5b1260a9bb4cb624c0037690ec49847eed20d893000dbaa7b126001b750f624c23e7fb926c812a6dc31d893020dde43b12600d3f15f624c0167e23ec49814fdb325413018fb6649822009f3d89534c813e7b128699027cf624c1324ff3e64aa28667e7cc9
  | 9 => 0x19f55361542327fb8aac8823fd75150d5106eeec2aa2a20dddd855354427eba88c6a8a3f1f5150d5447f3ea2a1aa88be7d45435051fafa8aaca1a3f5f5154d4345dbec2a1aa293d7d45534c48bafa8aa69823f3f51551434de7ea2aa2824dcfd45545011f3fa8aaca1a6d7c57d855449af8afb0aa7193f15f615404f6fb08c6a8805df7158143009fee2a326001e55076150c03ea8bec2a1c3fd541d854300faa63b0a8601ed5076150c037ab0ec2a1c3ef541d85438adea63b0a8601f54436150c037a886c2a18079d54d854345f3a83b0a8601b755b6150c036ea9ec2a1a2bdd43d854345dba6fb0a8601af5536150d167fb8a8c98a2fd451d854345de8a3b0a868bb7d9f6150d176f9bec2a1807d751d854300deea3b0a868f7715f6150c1a7e2bec2a1804ff715192000fe221b0a8001be54361500037ab0ec2a028ef541d854089dea21b0a80a3b750f61500036e9bec2a0006bd54d8540899fee2a322001b7cdf615001a7e2bec2a002f976150d4105f6ec2aa2820bedd85435052fcfa0aaca1a5f9f4154d4345f3e82a1aa255e7d054354116ce23ec2a1a2f9f415854321f3e82b02868be7d854350516ee23ec2a1a2f9f4150d3121f3e82a1a609bcfd0554544ab9fa0aa8a825ebf41559434db788fb0aa88b6f11f6150e267e23ec2a00ef9f4150d2045f3e82a1a2001bdd076154d17ce23ec2a182cfc47d8553059f88fb0aa0013fdc53648003f8886c298006f950d853000deac3b0a60a1bd4c7614c0037a90ec298436f510d853000dbaa7b0a6001b750f614c21b6e9bec298434ff714d9101fdbe6fb0a600d3f15f614c0167e23ec29856fe73154912acfce62a122459f9cc53244813ebb0aa698827d76150d3118deec2b026201bdcc52644063eb98aa6880c7d73150d104ff3e62aa2868be7cc54350527af98aa6a8a7edf315594349bb86fb0aa68b770df6150e1a7e1bec298006f731d8554049f86fb0aa8093f0df61540127e1bec2a0006f561d852085dea21b0a4001bb54b614080376a16c281006dd43d852000dba6fb0a410b3fdc526440036f9bec29042ee820d852085fd041b0a410bbb083614801a7e2bec29002cfc47d8520049f86fb0a4003fcd855044007f9b0a808800ff3614c11044fb420a1aa089f68416050d23ed082a698227da1050d3038fb4209926099ee84154500f3dd08284a02677a105515040ef420a92a099be84156501237d082ac9800df807d855044df420a3260037e01f6150006fc03ec298227d61050d10b6f3c20a1aa963e784143505136fb0a868800cfc07d8520019f80fb0aa8033f01f6154c067e03ec2a9225dc07d8543019f80fb0a86033f01f61508067e03ec299005df7255943009fee4ab286013fdc9565040377b92aca0005ef725815400bdee4b22a0013bdc95650002f7b92aca0004f
  | 10 => 0x6a880cff0795912019fe0f2b262033fc1e564c8067f83caca080cff079594244bbe0f2b286033fc1e5650d13ec28286a85b79c5050d54b1f38a0a1a8289d714143540067f83cac88225dc7058943019f8e0a326489771c16150c067e3828c98a27d8605814344fb0e0a1a6089be1816050edbce38286aa58f9c7050d4144db8c0b02868977d9f6050c06ee382869800cff67d8143019f8e0a3224037a1c142408f3f438284811e7b870509403cdf0c0b0284037e1c1424c006fc382848815dec705091201bd8e0a1204036f1c142500067fb3ec0a1197f0705051032df0c0b0282037d1c141442c7ce30286a080cff67d8141019fe0f23224033fc1e464c4067f83c8c9902cff47d8151059fe8fb02a40b3fd1f6054c067f83ec8a880cff07d9152019fe0fb22a68977d1f6050c067f83c8c8800cfc704d91238fb0e09926071be181604c806fc382648815dec704c91244db8c0a1a6403771c1324c0067fb3ec09917ef8605813144db8c0a1a62033fd9f604c4067f83c6c89024ff37d8141049fe6fb0284033fc1f63504067f83ec6a1024ff37d8151049fe6fb02a4033fc1f63544067f83ec6a9024ff37d8154019fe0fb1aa96de70c15450ec7ce18286a0a26dc305193044bbe6fb0286033fc1e36440aff8382428815ef8064191201be8e090a2089b701943448067fb3c0c8900cff07d8931019fe0fb12828977c1f6250c067f83ec4a180cff07d8951019fe0fb12a6033fc1f62550aff0102428815ee8204991044f9040a1a4099fa0815448123f4102a690207e8205592035fd040a8a4089fa08143480f3f41028c90197e8205052038fd0409b2405ffa08131480aff4102c29015fe82049910aafc804a8a2553f900941448aff2102428815eec2049910b0f9804a1a24577bc9e0644913e610286905b79c2050d54b1f3840a1a82033fc1e264400a7f8bec09900cff07d8532029fe2fb0284033fc1f6150916ef8bec0a1814ff17d814344bbe0fb0a86033fc1f6150c0a7f8bec0a900cff07d8552029fe2fb02a6033fc1f6154c0a7f8bec0aa00cff07d855444fb020a1a2089f504143442dbce08286aa58f9c1050d41019fe2f0322401f5dc55650c02ebb8aaca1806f7715594300beee2b1aa8017ddc56454c027bb8aaca1805f7715594300bbee2ab286013fdc55650c027fb8aaca0007b541d855400eeaa3b0aa801bd45f615522f7aa8ec2aa476f541d855400f3a87b0aa801a750f615523b6ea1ec2aa006bd43d85544d9fee2ab2831dcf15361551377a18ec2aa004ff715593000faa63b0aa601dd5476154c037a8bec2a9c46f551d85538ddea63b0aa601bd4436154c036ea1ec2a9a4cff715593149de883b0aa6013fdc55648003f8886c2a8006f940d855000df261b0aa001bd45f615414b7aa8ec2a8466f510d855000dba87b0aa0
  | 11 => 0xe2a1a628bed1c543505177a30ac2a1a2fd47150d1002be8e2a1a216fe71c54355117ce38a86a0a2edc615854300db8c2b02868b77d9f6150c0aee38a86988fddc7150d3002b78e2a1a82053fd9f6150c0a7e38a8c901efe4715091202bd8e2a122447bd185615002a7fb3ec2a0014ff1791920029fe2f232640b3fd1f61548167fa3ec2a9814ff17d9152029fe2fb22a68b77d1f6150c2a7f8bc8c88014fc714d92039fc8e299224057b1c5324487f7a30ac298015f4714c11245db8c2a1a6073b7185324c0227fb3ec298014f7178d9201bbee2f1b240053fc5e36480126f9bec2a11f5df37d8542049fe6fb0a84053fc5f63508127f9bec2a9014ff17d8d52049fe6fb0aa8053fc5f63550e7e218a648920fe431549123dfc862a122473f90c5324487fea18ac2980fef4314d9101bde862932208bf50c543440e7ea18a64880ffd4314d91008bee2f1b2215df30c5524c8e7e618a64895bf9c315514345f3862a1a828bb70c5464c4976e18a8c9822ddf37d85431cdb8629b2403fb70c53644022ef9bec298044ff178d9101bde8c2b0a408bb7185434801e7fb3ec290004fd07d8554009fa0fb0aa6013f41f6154a327e83ec2a8005dd07d8543009fa0fb0a86013f41f6150a267e83ec2a0004fd07d8532869fa0fb0a610b3f41f61480027e83ec4aa004fd07d8953009fa0fb12a32f3f41f6254002ee83ec4a1804fd07d8943009fa0fb1283273f41f62500027e83ec498c7cfd07d8930639fa0f132200d3fd5e06448167fa3c0c89024ff3781912009fa0fb1aa8013f41f63548027e83ec6a8cfcfd07d8d50009fa0fb1a84013f41f635066e7e83ec6a0004fd078d912709fa0f1b240cf3f41e364401a7fabec09882cff47d8131069feafb02640b3fd1f604c8027e83ec8a9804fd07d9152009fa0fb22a3473f41f64540027e83c8c99004fd0791931739fa0f23260013f41e46449c67e83c8c90354fd0791910069feafb02820d3fd5f605091eefabec0a1834ff57d814300bba0f2b286013f41e5650c027e83caca1004fd07959417b9fa0f2b280013f41e564c8027e83cac98bbcfd0795930009fa0f2b224e53f41e56481b67e83cac88225dc7055943019f8e0ab28601be1c15650932fc382c4aa205f87059152019f0e0ab284797e1c156508067e382aca100cfc70559414cf70e0aa28099de1c154541337c302c0aa5b79c6050d5401b78e0aa280035f1c154540067fb3ec0aa00cfc7055932019f8e0ab26291f61c1534c1237c302c0a9a25dc7054d4301bb8e0a9a60033fd9f6054c067e382ac89207e8705490201bd0e0a920481de1c152541037c302c0a900df870549102bbd8e0a9224037b1c152409136e30286a900d7c7054950019fecfb02a46bfc1c151440d77c302c0a880df4705451044db8c0a1aa2033fd9f60544036e300c
  | 12 => 0x76e31ac6a8025dc7354143129fecfb1aa0093fcde56480127f9bcac89024ff3795941049fe6f2b2849fe714d5450ccfce29a86a0a7edc535594304bbe6f2b286253fcde564c0127e39a8c90024fc735191033f38c6a1a8267b718d6350412ee39a8298026bc6350d41119fecfb1a824bb718d63500427fb3ec6a0024ff3791920049fe6f232240b3fd1f63544167fa3ec6a9024ff37d9151049fe6fb22a4213fcde464c0036e932868815cfd2789910069f8ae932200b3f11d26440127e1ba4c880079d435512000f3a86a0a4089b75192090c02ee9bec2900ef3c54551201cbb8e6a8a40013f1d954480027e3b2a690004fc765452047db8aca1a403d9f159564803e7fb3cac90006dc7650d20009f8eca1a40013f1d941480174e232869002edc4650d2005d788ca1a403baf119464803a7fb3c8c900ef9c4650d20009f8ec98a4009b70d943480736e1b26c9006cff678d92000f3a86aa2208be750543441136ea3221218cf3c545511018bb8e6ab220013f1d954440027e3b2a688004fc765491047db8aca1a20359f15956440327fb3cac88006dc7650d10009f8eca1a20013f1d942440176e23286880cebc46519100a9fecf23220013f1d932440136e1b28688026dc364c91018db86c9b220113fd9e36440027e8bec4aa004fd17d8953009fa2fb12a1313f45f6254402ee8bec4a1804fd17d8943009fa2fb1281293f45f62504027e8bec498484fd17d8931019fa2f132200d3fd5f61480167fa3ec290024df37d8520049fe6fb0a403977cdf61480027e8bec6aa004fd17d8d50a09fa2fb1aa2013f45f63502727e8bec6a0804fd178d920019fa2f1b2200d3fd5f614c8167fa3ec299004fd17d9153009fa2fb22a1493f45f64544027e8bc8c983a4fd1791931009fa2f23240033f45e464401a7fabec2a123ddf57d8543069feafb0a86017745e5650c027e8bcaca1804fd17959407c9fa2f2b282013f45e564c1e27e8bcac98804fd1795920019fa2f2b22001f51c55650d16ea38aaca1806f471559434dbe8e2b1aa8937d1c56454c0a7a38aaca1a2df4715594345bb8e2ab286053f1c55650c0a7e38aaca026fb471551414dee8e2aa2a29bbd18561552dfce30a86aa015bc715514102af8e2aa2a2053fd9f615500a7e38aac9824fd47154d3149ee8e2a9aa293bd1856154c0afa38aa68822ddc7154d4302bb8e2a9a623f771c5534c00abe38aa6a8814ff67d8553029f8e2ab24083f91c5524480af638aa48913ef4615855045db8c2a1aa0193fd9f615400a7f8bcac90014ff1795932029fe2f2b2848b77c5e5650c0a7f8bcaca1a2fd45150d5113fa8a231aa36fe71454355117ce28a86a0a2f5c5150d510c9fe2f2b22027d71446354516ee38ac0a1814fc715193045f28e2a1a828bb51856150d17ea30ac2a1815d47150d3145fa8
  | 13 => 0x31069f8aea3262893f51e464c01a7e2ba8c98004fc7654543009f8eca82868f9f1595650c5e7fb3caca1804fd76509103c9fa8f232400d3f15d46480ca7ea3c8c88034fc5751910009f8eca9a82013f1d950504d33e2b2aca08b4ff6795941009f8eca9a80013f1d952500027e3b2a2a01367c5655940159fecf2b280013f51f6154c027ea3ec2a826cfd47d8554009fa8fb0a608b3f51f6150c027ea3ec29000cfd47d8540009fa8fb12a6013f51f62544027ea3ec4a8274fd47d8954009fa8fb1262013f51f624c11a7ea3ec4a1804fd4789910029fa8fb1282033f51f625001a7fabc8c90034ff5791912009fa8fb1aa2013f51f635413e7ea3ec6aa004fd478d920009fa8f1b220053f51f63504067ea3ec6a0034ff5791931069feaf23264013f51e564c4027ea3cac98024fd4795943009fa8f2b240013f51e564400a7ea3caca080cfd4795940059f8e8ab2620b3f1d1564c12f5e322c8a98bcff67d9153059f8e8ab2400b3f1d156440171e322a8a89bf3c645515137d78c8b22a20b9f191545445a7fb3ec8a882e3c64551502ae78c8aa2a055af19164540173e322a8a80acff67d9150059fe8f2b2400b3fd1e56448167fa3cac9882cff47959324be78a8b1aa86fcf15161550ab9e2a2c0aa0acff4795940009faec99220713f4de364801a7e2ba6c9002cfc474d9202f9fa6f1b2200d3f15d36440167e23a6c881873c5455131009f8ecaa262013f1d9504c4c73e2b2ac9889cff6795931009f8eca026261af119464c4467fb3c8c9890f3c5455130009f8ecaa260013f1d9524c0027e3b2a2981167c5655930129fecf2b260013f1d9424c0027e3b2829810ebc4651930109fecf23260013f4df61550027e9bec2a824cfd37d8553009fa6fb0a808b3f4df6150c027e9bec29000cfd37d8530009fa6fb12a8013f4df62544027e9bec4a8254fd37d8953009fa6fb1282013f4df625011a7e9bec4a1804fd3789910029fa6fb1262033f4df624c01a7fabc6c9002cff478d920069feaf1b2240b3fd1e36448027e9bec8a8804fd37d9150a69fa6fb22a6013f4de46480027e9bc8c88014fd3791931019fa6f232600d3fd5f635041a7fabec6a1004fd3795941009fa6f2b280fd3f4de5650c027e9bcac90004fd3795910029fa6f2b262033f4de564c0036e39aaca0a7ddc735855436bb8e6b22a209371cd56504ceee39aaca0824fc7355941049f8e6ab2809fe71cd5450d3f6e31ac6aa025bc7355143049fecfb1aa8093f1cd56480036e39aac881b5dc735815129bb8e6b0aa009371cd56440127e39aac881b79d4718d5100ebaa831aa26dd718d535444faeab8c6a8806dd6418d5136db8c6b1aa201b7580635444eefb3ec6a889cdf67d8d5104bb8e6a8a864b771cd51500036e320c6a8825dc735453004cf8c6a9aa2273fd9f63544a
  | 14 => 0x95350c166e3b2a6a182ddc7654d4300bb8cea1aa2013719d43544036e33a86a8806dc6750d5047db8acab2860db71595350d1fae2b2aca1a3f5c5654d4314bbecf2b2863bb751943480676ea32868822ddd47d854346bba8fb1286017751f63544026ea3ec6a8806df7654643009beeca8c86097751e5650d2fce3a2a6a182ddc7454d4305db8c8a1aa20bb71914354016efa3caca1806dd3654d2000dba6ca1a4001b74d953440036e9b286880079d435513145f3a62a1a8293d74c55354402eeb9aa898a4edc7654d31029b8eca9a6205771d9534c41b6e2b2a698a3edc5650d3131eb8aca9a6205371d9434c5176e3b28698815dc7650d3105db88ca1a6261e7119434c403cea1aa8980079d435053000ebaa6a8a6001775cd544c002eeb9aa498005dd735093048db8eca9a6003371d9534c006ee3b2a698036dc5654d3047db8aca1a6045d7159534c0066e3b28698226dc7650d3001bb8eca1a600bb7119434c087ce232869800cdc764c93001bb8ec9926001374df6150002ee9bec2a022cdd37d854345bba6fb0a8601374df61480066e9bec29800ddd37d8530469ba6fb12868d774df6250c166e9bcaca182ddd379594300d7a8caa26201af519544c0039eaa2a2a18073d545414300b7ae8a8a869faf1d95450c125e3b2a8a1825bc765514306c78acaa2860daf1595450d1f9e2b2a8a1806bd465512000d7a8caa2209bcf50554544039eaa2a0a0805bd7454d414dd78ecaa282052f1d9545040ade3b2a8a08363c565514106d78acaa28269cf159545040a5e3b286a0a2ebc7650d4102b78eca1a8201cf55152500039eaa2a2a02673d405515000b7ae8a928099af1d954500065e3b2a8a000dbc765514006c78acaa2800daf159545009b9e2b2a8a000cbc765094001b78eca1280019f55954480033eab2a8880067d56545434dcf8ecaa2a2055f1d9545440a3e3b2a8a8a4e7c7654d5102af8eca9aa2051f1d953544033eab2a0a12667c765515001af8ecaa2a0031f1d95454006be3b2a4a800c7c7654950009faecaa262013f5d9544c13e7eabcaca1804fd7655120009faecaa2209b3f55e56505327eabcaca0004fd7654d20009faeca9a20933f55e564c5227eabcac98004fd7654910409faaf2b2406b3f55e56440027eabec2a1804fd57d85404d9faafb0aa8013f55f614c1267eabec2a9804fd57d8520019faafb0aa0013f55f6250c027eabec4a0804fd57d89404e9faafb12a8013f55f624c4027eabec498254fd57d8953009faaf13220053f55f62544067eabec4a8004fd57d8d41009faafb1a809f3f55f63550027eabc6c90004fd578d910029faafb1aa2033f55f63540027eabc8c98804fd5791930049faafb22a6013f55e46480027eabc8c88014fd57d9151019faafb22a0013f5d943480027ebb2868822cfd47919
  | 15 => 0xd54150d1000f6a82aa22001ed5054344003baa8aa888007755154d1000beae2aa220017d5c55244002fab8a8488007d51018d5118ba8e6a8a20317d1cd5144062fa39a8288007d52150d1035de8eca8a20033d1d95144006fa3b2a288036f456545101aee8aca8a20033d1d941440cb7a3b2828800df4765051005de88ca0a2033ed11941440b37a1b2428800cf4764851001be8ec90a20013d45e3648002fa8bc6c9000cf5178d91001bea2f1b22001f35496250d0fe6a1286a91dfcd5254d3200f9a64a928601f34c9524c00396a12a8a91ffad525514200f5a84a928001bb5895250c0376b12a4a0806ed625494043eda84aa2a401db5495050802f6b92a2a1005ed725414243dd8eca92840b3b1d95250816f63b2a4a1036ec56549423fed8aca928487eb1d15250816f63a2a4a1006ed625493100ddac4a926001db549544c803b6a92a099005ed725453242dd8eca9264093b1d9524c812f63b2a499036ec56549323bed8aca926485f31cd524c812f639aa4991b7cd7218d5100dda4ca922001bb4994244003e6a928689007cd7250d122df9a84a1a2401f34c95344803e69928689007cd324c11200f5a84aa22401eb5094044803b6a92a8890076d525411200bdae4aa224017b5c95344802f6b92868920eec7654912029d8eca9224057b1d9524481b762b2a4891776c5654912029d8eca12247bbb1d9424480af63b2848902eac465091205dd88ca12245beb119424480a763b264891ceec764c91202bd8ec9922409bb0d932448b3e61b26489007cd5250d021df9a84a1a0401eb50954408f3d690284a00076d525510240eda40a92a0017b5c95440903763b2a48100cec765490201bd8eca92040dbb159524087bb62b2a48100cec76509023cdd8eca1204037b1d942408177623284810efac46509022b9da4f03224577b49e06448038ea1aa8a88071d435515000d3a86ab2828fe750d6355003cea1ac2aa0079d435815447f3aa6aa28601e750d645451fceaa286a8a3f9d5450d5000f3aa8b0a8601e75516050c02cea38c6a8a3f9c6750d5404d38cea1aa88fc715d435511fce2ba86aa0079d415594300f3a86ab28201e750d5350517cea0a86a88079d435414145f3a86b1a8201e75056050ecbce2ba86a08079d4358141b2f38aca1a828ba71d94350517ce3b286a0806dd565854300dbac6a9a8201b75596050c036eb1aa6a0006dd625814300ebaaea1aa26fd750d5454403aea9aa2a19575d435515000eba86a92a0017755d6150c02eeabac0a1a5ddd579594337dba86ab28255b750d5650002eeb9aa2a1805dd735414300dbaaca1a4001b755943441176ea32a321a26dd465424300bbaafb0a86017755f6250c036ebb28690006dd7650d1045bba2fb0a868f7715d6150d12ee83ec0a1a3ddc575814300bba8e31aa297b71d
  | 16 => 0x4021701000000001a1701170710030402061101000b000b000601040600000003000402021b0709001006030a0f0104061a02410600000203000507000106031b04180202060500021904020422110002020039001c031319020f10000031080902002a001008010a0b010502040900080700080003003c14000c04180104171901080207000d060a0000030803010002070201051b010e020208130f0f022511060709010204070000033b001307020102010217123201020d00020104000704000003020003093f160f020104000e0003040e00000d120e0401052001000a001707020008000006040600070023170201030103220000010128000b0003030306002307000401010a00020007030116030d0203050000052e0f070103020c280009110309110900000f0100040005011102025305000f031502040130103b3844080b0000050200020c01010a0c05001644020008020a00010e000a03060019054e0202000202061e00060818000001040102020463010e040207000b0305052f40130f030d02170e0600060c01090112070205000008000519030108061010080c070007000800030304101500170019030900010b00150d04020803000500010004011b030400000503010a0702000405010c001200052300010200040002000b0613010030000300000c0004000307020405000a01010800050301000a00000402030f00010c060e000103010000030e0208010a00000604030c040200000003000402000002010600000b0b0001010f030e00070103000001010300011000000516110002000b0b0e0100070704030102050702110e0b0903000407030b01050d0500130300000100130014000200490400081d070b02081102000902020000000a0606021501180003020301010704040a0022180302000254020920074e00002f0200001702020000001a1f00030004040100010206091715010000070d0400060904062b0e03021b00000605022400f5240a128001da481525407bf4a82a481007e920549401dfd280a12045df95455244803f2892a2a1007e512549412dfca82a122401f9449514c803f28928299007954150d5100faaa2b0a866ff55054354403aa98aa6a898fd55154d3100faa62a8a8601cd50554544d3daa8aa8a0807b5415454300deac2a8a8601bd58551500dfbaa0aa8a8807755154d4100beae2a82826fbd1d951504167a3b2a2a082df4765454106de8aca8a8269dd15951504dfda3a2a2a082df4745454100deac2a8a6001dd545544c4dbba98aa6a89b6f47654531049e8eca8a62097d1d9514c41b7a2b2a29898f74565453100faa8231aa26df51cd514c4dbeab88c6a8825f4735453100deac2a8a4001bd5854148003f290aa488007e5215091000fca429922001e55054344003eaa8a86880cf
  | 17 => 0x824f8ed0942e3e431387115556313098e88b030419f33ac0013a593844b1bb600042386600006689bb22a0f9e00047ab3898b490a7e95046a260000004f7df6800000000003549be5d92d5468d2140b30399f28510613b13800129e95b9dd80085cf0f99cc0d365a85d8108d08aad63a6832a05c58966b5524fd896a2fc3f08000946000271e2448ac8f38ada7340001b55082ad0000491000154f22100043f29c114210588ed01447d99344e018a0004f9000237d50d0001fd046e26e0005171234000000000000000000026b893a42d0005604f960001c1b2a25010c021300020012120b430200002a033013031f4caa530304000401007f01185a052308700e5f014948014700020f031619060014091404040d080308013002410006084815150303000e73081d0006002f3d002802136d002f46010b57000002030300192700045514221400001c1e0409015b1904241a0018042b3f11113300000700002a011d1962070f01020304070d0918050166020001081f03080300020400055600051c0013000600001510001c4017c31c121703001421060b08080604000f4d5f0500051f03b01514471d140e1c001217140001150315001c020001000b071442280705045400032001070100003a040e103804680113044901190c010c0504121133020101110200080b04001a010324212202030d5f02001b000b000c0d0b0023212205051401070000020100000003000402020703180003020a000f1200000c3c2032010031000f0000010505200004020566051500021c12081b200e1c0a01010000071d20000e0401131105000107160400031e0c0207030033086b550e0b0035211112113600000100116a03140513020e080000032d0001073201011a5302002e000a0402104d001c001202010908010600071f1002020c01012b0b020005193a01080a0e0000060101000807000104060b000a2b09010311000a2f115a05070400310908260205022a090200bf150207150a0a0201050500000e2a000101010405000203120001150a030a0001031c050a0305100014000c0213780c020b010c03450000020301006a00020408031d011700002e2902270709000519020d4d5a383a01050900012b00010706120005000e000017040200001000011509040a0302040100030000000409020a06280205270125040307070c0c0c0c0a040c000e001c003702030700080600000401001d02010a1b260808100700010006000900010701060503082f1302060101000d100a03200d0000060b015d06030e2e000f0339060c200a0514000a020700142100050a0600001002550011002c050004150012030d0000100c0602090008050a01000207080202000c0002090306070a0605041c0000040007300f0b1b00091902169502200e00010106180e
  | 18 => 0x2a415325018122eb5aaf7025b3900000002ec000234f06a108ce2d566cbe5631a4dde689220e8c54934f524294548bf4ac891f43d8ada07e417550a89cf2a573b998f8211e2ce2688000f11560417a6b946295d47daaaf0a02d8c35221119336c3d80cba3507094f120240000000000144ccd204800109edf10003ab1786ef6500198e89466600051d0000036568b1e8000d4888d856022a000000588940b27633f3d312e92b40004efc001570abb142400000000036a952266c5e427500000000004dec0002e400044d4000ab0a0f00015a84b90003f41e7e2329150951f1071052c98900f88590a81178ba0bc75e6303c23aca099c1028a48a7541e2c5898f19c8ef4c2e68ee709d0a3b06b82e24041e0896b0da3f6ce88f6af5b3aa1f8e134674772ad6c2b74b14831e603a4980a481a5e964609ae156da0a20a83d44299ac44819f999ecbd53829db2c5e528234254ac5249ca11ab5923052494230b391ce6468213c852dab44c84031ed1b90be29313ed8504b821d3091686c0b01c895e2416a6b5339c79fd5117aae90f94f899819cb62a48c08d50426c2a200a908a1d457d20598933122a54171a70c739db072e1b64731a3c3005210574e141080421898370f415b94ff5612c63067c484af444caffb360c445728f610d8634c1b5125700cb2df22f809917220006df4640020b695d0ad02ad351c92956f4e046ea94c2579bf50f4484542606aaff00056b962a00042580012b8b410ee80009467d7a408af968a00047faee68e47cc2b41d6000000000000020f409e5313d0a4625c3b0215d1ce6f07542974c5a6bd7731800144a0000a0a1400011800ba1e8917074e68c48000014180003e164fcfbd286bb68e925d634a433a9a88426428002120c4a0003e2e90a000000294236caae0001af00005d480c00000004686583a061580006eb37882580007498002aea4abafc0000000000157cde40009ef8b15630000bcfa2a4b41dee5c6616000000081b52fa0f9dd08c20004b556c93f74224a75c4cbb5892a72178018a0002d7eb142a81c6d528000f9e1473b3c000e625e94a829787427f3d3d97ec0000000001cfc26b00013888d6b2c9c71a880000000000000000e9d55a9f286f629f32b2e6d848aac52a3e74fcef959cecdd097a1ce819586ddc80009e7013e8b03ccaef3a41d90f3596086b18bf26e736367494b17f76ea97139e000066cc8650aec175316f219115e5f8000088c0000dd26387dd2eb54ea296a4000000000000012fa62a8001738690986904137b10c000341d86c00039500000000004b200018b8bf28213ba4e9f0ff0ce07a87b124b0a31de88f06aa7f41db453200000040402e09107d6d61c34e3b17fb39a0da400002948b26372de00056783ee388a9dcd48b663b84791daa7f0c69564c1d1a65616ae52c415ea8d
  | 19 => 0xa8099b0a8b090e020358b04fa68b4e4995005d5ba785a3ecad44f08ecb0640000f00502279c8011132d3a253640b427faf517eae646385488000ea451e0c81a009a93d242c1bd54d65f98000b5a00086809c82a21bd6214f7a58a2b1921338c96159088b1bc6a2a41443282d681212f09a16e559e91f2513a55864dfd2b8d58645af39414136174016f14305ca6851d25559d8d1b40002d34fb4590e1b1b70001fdb0ae9012f1400030d0c62edcff0c772c30bb9d7e38fab2156e9315a75e814a03f13fc882b34211a8c7888800297c8519dc56a2b125934f02dedc58b6f000009205000000010022c153d4cd2650cc0556000474c0000000003a65f732ea39300000000002a680000006ec94600017b23b30002c7840b3130005515d98e28a6c0760fc467d919396081d30405b3e3c000e1a51ed04e4400fa71206f895535ea80415aada2a5ae700001dc1245851b640000000000aba8a4df400053a177824ca398001c1ef1e00023aa10758e7008000aec00000000000012b0000000074691500000006654221ed00000006b42744cb9c6cfa94519f393807e5593bfa51e654c5f61b788112f8a3f3550b681ff52b8e2a0c30f15c48eea834ede91d80026824d65524e4a8d8d7c59220520120557a3c43c4a43b67df1764c30e1e00000024ca3355cb98f00000005b30002a65278ab7803dd8c26f11500008795390000002874a8b89500010ac0cc65c56163b40008e52e051809020003e056b26e44410d792b0f6748a00012a8c5621fd29808834829e4da0a58ae17648240342ab42c7000000d426590800000000000029780005af4010000ec44e40000000dfa9cb000000164af440004df141cc5023dae943c0a6f13d57200007c42cd0000000000aac80000000004fa2da0b5688a9cbbae400058200000002d21e6727000011e000ab02610c20000af800009854f01e73fea7b00000000860ac478308d996c4b1488313ac61df40008a5392000041b3f510720c8efb43401282086f91c3bb54c40dfc02e01a0a368037898b4156cf0062bb0adbb4fbb2c188685d60519c81d94c503f98dca8ae4680000002df40003908b5059dd861399bd4111e1a0009d334c6644000973c25800091c0002498ec2a06601a474000d2600018be7840005c0004a2680bba8d29a58cc0660003d18474f7d000438cd4901949dd0f94551aa7b41684fcd61204cc8f18d887051937a26513a8619828cfb53f0aaac4dcf5800007f2af51ee00012e800060ac88a98987aa1032412d932ccc94eab10481dd1c3aa55f00000003eca232c661b8c3f0f400000008e80002289ab0d2d0003cd073000004600004484943785404226e385f030f26ac000132aa1000073e93e1940e300004778002058bee9544d5000050887609da2340000d21b39eb874626e000145800045740
  | 20 => 0x7d1e2c0007669cb1714d2b079143e5dc000521a93a0193b471a00000002fc60705ee71ee4b781a95a188492877481172c2f0395a8364473fb8d34a41bf0bd3aac07949b6c923a500029b345e000197902f5282812412ae8c1108927b81270c541c0fe0674d309dd0352c30b8842188a642e68362225a20521893033a7a510a6d043056912cc1e2db3752350fc316d12162a14aaa0756956a66a62b48be0000b858de3aa45ea11c9e803687e053e81c888090edf613c0feddc6fa725bb165440fb316f2c69db23362ef8e4907f3e615c3d903400d072b301c1344833f0871174800000023c48fef4e41da5125009a50000f2e17f5a0a85368037611700d01b936e0002238000de42536960000000f3e0001a56bfc96d1d2bc10f10d12000145965ef9600029b1e90c6e96940228172673c98000d58000000554000014a54488b800000000050180005cd0000000b5800000037b188d0de005ce780000bd1cad26650d06c3ba4104c524705d43ec4d10b1b321168abe8e8d052a5c53a533a0005028d5c01b611c5a056639a53fcdd69f300e775572e7e44590001ea800116c644a1b552709b00041ba90d0986f980005813965a347e5ebcf3ba420204d3d444384402d6949326881870f80cac7dfcd9c3bd300aa3a6e1f455f299a81a9e3910a2e63d89f70a864b839d4f1449c0ca10a800091e2392af27360007c80e84ea011668a1d727e8b0c2a4c4429de7b879b0000000621a8287903329289eb1720fbc8eda4533d80012e6000405800152f6ba29ddeea00088c44e64af34c56d80008a20002ae09d59500000000001fc800e373c9a1384acb69c5711fe52f60f5800079076f0fa15800000002f649aa21c17f963d3ec0580580000002984b2d1880000dfe00056c1b1c000000950bab40000000810001d005ce0000f01fb10d68812aca96c0c057b05355034b89ac04f649e0000004ad98d00085fc1188000422000030427d13c27ac4ec0000002cc800160c000a38c0f80003c200000000000000002ca0000b3c1c98002a0ce59b0f45001bb526aa68001082ec50000001c10a7059ed0e26144389564f88a8ecaa47e87322c8b502bdb5a9f00000a5120c0e8136e13157d98e6a1d73019a82c00113b24931efc918a8c3571fe2db41c624c1bf2e7463fa33940e4c673ba5ad24919e96d12b64a0ef204a83f19800549e405d9f344c5692a3780c93fe82e5464b3ea0aa06a261c00da73f5a9ba251540156222dfaa0a6899bc403ea634983b51000153e0ba842ab08911118ae6232cf220000000000000732a87cecec0d3be3941198b7f05d3831dac0007aa08002ae00019114840000008ec065a5b229e000544682c00020f84c96c4a5141a08b4b0b4406260000c00cdc76e2eed0aac2613f8000c293b04eb4bc059d5cd3edc9757209c1544129d9a43
  | 21 => 0x5ae1ebc000d8689f440102d2be52d00009a4e83574000101952c4e2396ded262a7d610bdbb018745a49290580009b68f510b738425007bcf6f53810641511cca8200010917d6c60adc334e798d364c4000034a0000004016544bb43269d817086f83e684ba9fee21a0008e000035a78097b87d439c131d3b2028c3b00002cdea35678a72178f6c1773bdade83691c000009a45d546a75d800000104a7e9c7d0c903c41a13308242000006976e4cc00000000021c8d4a681b4a52c114458180010002e65e3000230499f45d373a8e0c8e8420709d443547051c481563510002ae4000cde539149eaf46044da8a8a9285264a53bc40011eea7f058e584f2562485f4000042758000000000091f80000003f40003e6d7f6e20674822cbec38e018ad44472bc100032c80d851300056d0428ad50001e981ab0b6a30811eafee16a90ac8800085a24c35395e910d34e00016253bba9ac2d1c84d823390bb02209fc34d12440009361369cf442559100041f136677e2e500025900002cb16e00000000002be8ed760e19709cc00128977a80004d532000000017475a900000005793d12620345cc226616f995e1c55302d4d5206c40001b00b6190c8938b94891ff73eba798000caa0ad93000007580008f4237129c7ae78c007c2d600058980018e40009673cddf428a400024b26b600000000017ca07a7252f24000e760f82d51a35241a7885585fe1e90003a7d52c59e1853ede5034da17c92f1f0c0001c22ca8000597426c6c800000054dd56d4b71487b09299fee0003368002828c14955c0544153e15e6c87c0035d17ab4068bb47d972d000000160c96a21e6746630ad928e8c86000000528ded475a317000106400000054300000000000858000000000141dd6612d84056adc1a2fb0002ff4d6c2fd02700024529e20001059a66f84000530200649e8f021e08c0f1599780f16e0b7360c1009fe0c05adb8c70f869962602d823281b073926862565fc7ea133e194f406add54dbb8b36a3c81581106366a137b8efa6fcab15168bc4000a7134540000ea840be805e8aa10d11d6df32e0448b9cd8e3f25e7ba3438000000517838966e4905a21e4a0c6c651630b3c8773d417d037a1482b05552aa51dd3ee3718ebcb243e0a6512640002bf5ba3db8000a2e3e2bb82b82000412000000064ca890438164da8224d70d95afabaa333e89d80009bbce32904af8513027ebb52c900045527145b07943ad4704c5400017c574e29a775b149e9264a4f41ec18fb4b95710ee44782426359521f806588e4293dc2014922825ba9680988e8068eb009a746529745b85f229a4089eb4a04655cf0063cd0213dd6fa041393513bd742bc6b25d5c4babcc6fe59c53ba3cc4df2b30aadc60ee24feb3998008a129a8f722e8cce1b912252b4c5854d57beb480006111
  | 22 => 0xd5c8bb85ffbea0000f1d0004219b7455892480001720000003d541e87380fcb055fbcd3e0005190000a9900000002505be7cb9d791e0a31595b2064440008ff2e89b080001dabbe021e000221310083c0003f7000231aa9e94103180012560b6a448a2f2376f01642424aa30b2ba807c42ad7c607f5622a3072e86ca63c77faeb2d32a52c675ee3779b29536931aff9f60d96897829ec2942496fc9700b552567657493a082f335c0e9346bf75143418a8d2067c13576198db503a4cf69a279c446439a038e068d1134088000051b00313394cc7a98c0e2652dc5918000968f336052990aa800027312c800000046f9d7c5b2f0c3862fc635edab7d290c2b36cc1210000017e000000000000085c51480026a2d0a0003bc13484a809ac8a18961c72420001818000000097916ce3c53cb971c74b9e74d0284d4140700048740004dd0c92ef8000298000000292c04826f000000000006487f282000000000007775246530001d6937e4f63e9a4f400054728708660000002a3000032c0002c1d7aaa7b8123d7cd90b9395909b0000ec02c5461df92acd5d68000001336017aec5e1ce790bf038000003e0ed5450fc13242475539aec2844b380007bc0000002cd2b0cb9f6bc58b8df4b1c617800000000095552a00000008fd00025c00008ab00021bee2a00010b80010384d8b80d85c0003370000000a408bc0001f393dd27a11f1e74ce100042a8000e9c29b0001c9a000883ac2c83200000012f800117e29d1dc26c4b7c1d4ba2d68636d56526fe686000687bcf0000d6f1ca1bcc630000000335ddf911300f4ef930cd20765bbf67aaa985d32a7c00111261f04ac0009bb768241e1db11f000225170eb1d63dd00c48c3021fd38a52009de5308434298f2d24339ecd94c757453df27d52c05f0cf811f12e822909f9684cda9cc9b6800079d0b215b2c46ff4809d0f1c1290163547168905b2a5aa31872f5fa20d253c91557e0df9e1dafa13b8540ac8dde51208cd5125d2d9837ad2c19aad5e34604fd4823a726d10489d4070ad788c1138b00ade23e6124eed4f350ceba614853c0d59908fe27fc93a4000b5700028ec000c1659c80029e4f8a2cda830262da5093b48877e1f101c2f7d2a683d6e01948d0000aa8b41dd3a64af4d5aeb800007b67800007f8fca000571864d5eaaf60000a7b2879cf8000050000aa92d6a6c05f50618071d6e000481bb7e1440000001828fa751700000019b75ee00000023fe00097e0824000a4d7230001e0cb024580468a88d905c7a210618366000560c00000054a27608b40008faab72858fc140700013200000000001e411272321060f1e8d6a2631e248f2cf08c0000e120008fc05b9d5077325c39be7f4f79069c0be9a027009314010554ce0e500002187f075715c200d5c95b5890026efeeaca0002318
  | 23 => 0xb5b3ae85698dc2ae3529a015dfc675abc36b000000053035c4da20008595599002eff0a041a03be000000486285cd9a729058800042c00000019de0000000c7c0000001872d340000006703458d7e00000000021f43f20000d4c00109e7cc229c0003d00b630c13500000002d2cfd200000003ae7410172ff3e35a7463533b56b0b3093a9a2382cdab3390c1823ac109b40524d98000000a7a184d94a9ad0003dddddf2bc0004d369ccd666db21011561c65cacaccfaac8033c0d6109031400000001552453cf22195f68e081b41195be4ed42bb84d3b8a358c240c26e428c4371f4983409c82c537a0fb4ba0001b9800044340f1171134cfc5b0bf31e4caa53e3800262901b0201a58a0a5146643d6191a15587f05a800000948c800000032837b80008745a43c29dc400047600015de6c60007c3a5f909961f61d2a825b05ef2f9ccce598202adf8000ce10db7c93ae9e14ee180040983200001bf1099b7068600036900000008ae223899cb6d3fb401e8395aa1eb00004b800000046484069da0000000000810587bb46252c1f4094ffc89a0000004a0e334916382557d4702ba0001c8eb307778009e44a60e23178800237aaeb394053e5a62741df442492c1860004bc87ba24ea871b94b1af7200055f400000004d800000158b0004e558f86cc22a54fcd8104c6b0000000015f7438002a56ce5694041e926b659668ae652a4556573a118c447a7d7a70d76cabb00019017df54b7b8948cdd09452bf146a9912a5915aa1e51cf090000000a9421c0002e38000000733c5f1c44a46103cab91c8bda9632e1ac0a1823620e78df69cc79c419862660861ad80a28c0b78301eec7ed60033143952de000b140000f00000abcb4921933da61b8000000839a191235c300000000000000d506d800026773ecacb5840f7ab2005e24f8000000000292800071c0000000000b48000092c00002074937bde0400062980003a8bfa29280011a4ac75788001eec0001608001d36000798a02593149ca5200027eb2153f9af464b4129000292e0660007990000f62cf80001419969230188983e9fa1fa9e3324000149a0348000000ad95682e344ceb290001480000244ad0a530f1d4f500010c40006984b48dc10e851e57c9b428dd340403cea8624e8c0003c160fd50b0004b90000ff300043194b034a0002bf23d4000a7b8f4934d302538853a5f60c41693cb2ab954f01341480e42e8b0e0655b82b0d952184a2611ae28ab5b86ec5796638dd13549d12e0413a2dc14304021e8d96bbd16b1a11e9e2908dd3bb19eed6ca9393c828a8bc89e82c63062a45ac3e4cb1812007b279045076991319f14c75044114122c4af7aa6e328dc994897e2103645ccd93248002624eb13cb1199e36940a1eaae2b8a78da023c4918838641b1128d1e9f69578840390f63883
  | 24 => 0x90c00040c00020d4b1e7bc5d63a5c0000004a80000000f6c8c400015babaa0003d0c0000005fc800103884e6d1c356818e854e298e0ee430123746ceb8ea833fd008d7ba4bb9622b69ba4a498600ad2156c1288f4961fb50936622bf9b640ec46a4a998ed254150030a1d0a13297060191709c183a1faae27568da2161d284eb968af7958353322788886f89faa72d3e8936a1825b55cdcd32848f821c9d113e80ee00d00011ac3e49ff80009b679084198b70377b809800fe5eb89fcbb01df0d819523957ccb082ee0175e600ae06baf083354c42ee97922e01e38c34e52620b309c41b70190938aaa27180741e169a8a2965c67a3c80bd97f8f6b70119fe170f45abd981cbdabf462f484668d4ac1a64141bcca0f80fd475574bba0109c8294b4534642858f2905a99529cc89060c97125f09a71b006f9a755af456600b71a81f36c7f014762cca214de366ca1843456289dc2a4acc4d6394d5cceee977c4827589fe90736306c8de4627af2c44c3064bb311da5cf5014435c028eac29d219de388c0827e51e05549055771b82653626801005a3c868132716a9914781580a274fe508c1859c38254cdd5c61c88d8c2084254dcdfeabc429c439e44f61a50a8182ad8a903ac9782b9e79a72fbea82f8ec487c1eaeb24142adcb175cfaf2e3c24639a80b5d94e2bc15a718a37102be6f0a145e53f94e880942ef3a85a089cd179262c3811a41245674c355037a68eddfc734a661cf70e90f6635858840002710bcb6a4bae4bf65200015d53062be39b52c224a6738390f64f598450e8a2ec47e11f0c58900714af238145a827c54bc71a778a744a9389cd846be965d780000b6c220800069d53aab28d1000154c3772825e35248ace320c1b6e4599839c599ee829a29de40f00003809c1e1d497224a99941b80004975141f6a30f5eb504984b44291d0258f7e65f2d3d408732df5ada813430878ba9696b8ea4a664ab56214914fc048914ea86ece8d8a9a9d222e0579d3e11a0f654500000c7c00000c8001b4d2b81843af9d2ccea1d057a002e0009e9000173433000039798e229645f33190e646c8dc08d8446fe6a502f3aabc21d02b8002054a026d107d80c53642564eba79446a000000231640faea23f8ebb62a307000076020e72796e886e1367b99c15f8cbb361cc2097520004904e70ed0fdc53ebc9269000061a15900000003c644c64e4b055874fd9f5d5344968da03e4e5700010a1804000000191a33200014e368547352e0003874584000acf9bd08532510000001a100005b8d5ddb105a35f2373000000000052b92f00008ac4d7cc88bed00000000007a05262118000000996085c0002ca00031145005428bd53b5b840005a94f8df1289b2913b4ab1e7c650dd0d59dc01d65d0eb556f48c49a130cbd00d6891add472c59441d4dc299
  | 25 => 0xf1317ae62b3a8fb31843b18b00000000004cf9fd654f00013b81d000078f9621d8f5970004c2000144f703808800000047e000012e0005058001a8c12390f000183a0500aa4490872d720000698408f17743144622b30e93a000000131a000475c000b4e00000000010c2000000134000065e407888929a5a480c8000eca00000000005870000ec800042161880015ca309a0400004d00006082f8c001103000000000039b2a7243000059164b34d1816b5664e476d586ade712c23854c000037c87188200060486b8c3281880eb5e980cc870de3be5ede13097cbfb0000dbc28c87f9f8f36a5f3827698c68da471a24054aa278cb9a8b4a5c49322c12b60c4322b016dca2f7b00029968512ed0cf0402a3ef9f0c7413c170f2f247a174000fba5d793e8fa01ec4c52d1c000a3e0bd00023573809042c7d176e447578e929d20ac0002c9800000040d3c9d4f470d41bc40548a0001283ac847a44e9d9387d152f299083186b440003f40000000ea30fdc475d4a74c4403d5e57a504a1823e80044354321579944b6e0911336c145015bc8de8998a125478000001079534305e5e8a555af4a5a618cca697b8b8d330349362888856ed45081bd8864b3264133f83a15dc546942c79433403b49e5870b3302f1db01b0e6e6c1d60abf8c6facd162d852f4a30e90f53d48e736ec2e955e789249c75009927d5ec05849484ba474af6dca8477a8db679ff070012d480dbff34e66a288cfa93557d182fab461b6a692cc42b813808face935e82075ea5880013f9912ce60756b3f61037c09a907899a05e1a3922f5620050d0b0881f234f0b6effc5bc54788da18800002498da40ba3e00019184043e8b2689c0e32999056577f61d5ccbf38f7d57c4f8434cb011d547b2e74edd04069bcbf96d4a1e000500435068eb14b7f95fa7e40001f624e6000aec4cf20ecd0c413125d008df74480001434380aab0000904f83576a221da6000653ccdddcc86c51bba9c3c4dfb43041fd04b3e4921d1e8a387244c912c66381815ca4759cf0c7e0411f21f900007ff1f094a4e7c1a93330e06aad2651305b0082373d41c2b1ae4999f9ff2ae4f6d59a91d1e96b92aa899719e80835b39fd4a3eedb522032ebc555a66880f40307dd89b1a498430d20f752347be9f82993255afc89f8ad28cc9f06731f415489ec3fe570491039a7df90b1540cc310449e267969e0005452bbc5eee8f2e4d0d1706d520a236ba9d6b6300055b8000691259863dc22225100c7887a308538d33a00013ef000539df8a2ef4dc854c2d1062a010002008c4d78a43c00010f2000031d318ed72b74708ecc2ed6b4034939d60619e55047780002d0075992800083918c8000000000122000109454abc3d1650470000000000fd65169502216eab88ca3895d2e0e85f501670c602773ab49162cb68d
  | 26 => 0x1031748ff29ca4dd47f078c33897ac7c96ee97a66fd1a1304a3f28c1ee9d30c740674d6870a73c63cca48eea9d51161c18e681e710f157d4692d63f7a4a81b349ea83c8da25a4fe424a52157f50fa3b000183887c6c73ef1d6d48014a07b5efef082e100022390bcb123e4501713a2eab0f495cd238a600012d92d70000002a6f03c36485cdef14e4ab54a29ba07b347a0001808a92281bcf5d84d9f4b34661b8808a163b6486808667550b11cab49244c9ae90d4b3e3ee2bb027868a735a46e5c6679628be384acef467900006f059d791b2781f0b3b3eb48302748532cac9345fc000add912c0000001662bc9f6546602300007ccc2d2e5b0a14fca1742a2fa000000075c50a9a54000a9e2dd982690e1d73531c28aa8213d48d7d450a36b3f6cf0cd276e52a998c850e0000000dd2a76092c900e2d31645348691d71dc2b1be91cfed640001114d506d488a1798bd2000523c8e0e74000000000000000000000000000005404d41b3852a000000000000054e2ac4f726390001568d0ef2b816cb296fc0000005181432d560001ae1d784250000000e
  | _ => 0
def g6K5 : Nat → Nat
  | 0 => 0x90dce7521d5144243739d4874851090c033590d178d920749cc875491290dce7321d5240a43bc9cd2881d1290ef72721d43919307395c875495090dce370e2474d91073bc8805490290ef3f00812144243bcdc82049d1090c036590f715594300cd643dc55650f1372083714824300cce43dc9565001237219574424318ad4865451090c1237de237d915100c9d4391d26440039a541529190200e8d5250e4640aefe2081439192004c9c3750e464801237a1b71482436b99e4845e5650c03659054718d5100cd64119d43544033590776546435d99e4841f6150c02b6a006418d5100ada80193635457667921079594301ce80740b64548032750e17d915300d9648dc55650c1b4d85d54d915100c9d4385e464c0636591d10d8543bec9e1750e464c4032750e179192006d2e27553645481237a0c7654142028f6811d950508076a89d4091920008de38dd156440036550637d915100d1d548df64544032751e37d915100c9d548df645440327da14718d5100c9d418df64544032751e47d8d51008df780df645440327d1e47d8d5100c9f418df64546cbc5d5d4150d5100d1f5851c635440317d5c6750d5100cd7761c55650edfc5a05435515100d968151c6354403359c46750d5145e96685076150d12b6a006750d5100cda8019d43544063ea007654543b1f927050543442dbc6a01435515000d1d5495d6150c0347552575814300e1d545865650c0387551609594347e1c865525650d1f87d9d549594300e9541d865650c0387553619594300e1d54d8a5650c02c7e11539594347e1f865525650c03c5545439594100e951050e56504038750d56959416fd1f7550d6155307875454395941c1c9f7550d565070787d454395941c1e971250e56507072721d439594100ea92050a565018b47dd5435815405d1c875525650f0267122575814300c9e5419d43544032795137d854000d9654dc55650c032795237d915100ea94050a56408172711d439592000e954150e56440172e11d409591045f176550543545176505d439594100d1e5151c63545bb27d954718d51b7e965150f61552fba5945439193145d94175065650d173505d619594302cd4174c65650ec7e49414150d1000cf25045e36480033694137d854000cda504df61482f7a69414391930bbe9a5050e46480073a01d029594200d954185e5650c0347552179594305d961750e56504174d85d549594105d1e5750f615530667122179594300c9d47990635440327a106750d5100c9e4799363544135585d539593100c9d47980635440347552279594305d2e2755256508174795d43d895445d967150d52504075a89d509592002d5637546564c4032750e479593100c9d4391e564c0132795d43d915300c9d4391e564800b4d91d519594101d3a475425650012679221795943
  | 1 => 0x54d894000ea940d0b62540038b55342d895005c3c4755362544170f11d54d895000e555154f624c642b520543d8931b9ec431487624c003a5505438991000ad48354626440172e11d408991045f87625054344adfc5c494355151b7e971250d565040365c494718d5145d941750f625040335c486750d5113cd41718f62545176505d41d8943008ee2841f61552dbc68814355150c9f87025054344803aa50220d895400e695088362550033a08207d895406d6a0754b625411f87d59435512005daa0750b625001237ce07655120028f6811d95448117a5985435052047e1f5650d54448036550617d894305d961750f625041237ce07655112018fb081d95444802375e264d8d51008dd78983635440237e0d7655110008dd788c7635500347153735855400e35415476355002b520537d8d54008df835d95244002375e230d8d5100f154155363545a6b560464d8d5136ad4684c763545a6b546060d8d5100ad5181036354402b546020d8d5169ad51811f63545a6b546007d8d5100acd821936354402b34a040d8d5100acd2811f6354402a752020d8d51a0a5d5819363546829721953d8d5100a5d5810363544029756020d8d51a0a5d5811f6354682371a3735815100e1d5419363545a697d6047d8d51a0ad71809f6354682b5c6047d8d5100adb0811f6354403b248020d8d5169a5f580836354402a7d2020d8d51a0ad71808363545a697d6042d8d51a0ad71810b6354402b6c2042d8d51a8ed031443635400237e0d5791910a08df8355e464c6cbc5d4d415454300c5f531d95150c038d54554d8d4100ad518d4f6350402a752353d8d4100e5551d4f63504038e54154d8d4000e695054a3640802b6423538d91018ad4835463644002b5463538d91000e5551d4e3644002378e117d8954008de3845f62541a6378e117d8953008de3845f64541a6378e117d9153b7f16315515150c03358c4765454300cd6311d9514c0039554631d8d54008de3841f645440237a1f40d8d51b1f923050543442dbc68c15454143008de87083635441b5585d53d8d51008de8710b63544032750f745593100c9d43dd1564c003954c551d915300e1d435476454eff8716143d915300d9471dd15650c0365dc77455943bfe1f5150f6454c022fe11765491000c9d43dd15648002a752037d915100a9d488df64544039a48152d9150a699f8455f6150c0347d514718d5100c5f5419d435440317d53765464300c9d4391d36480032750e474d91000e955150e464c403955455391931bee9461dd16150efba5205439193100d9771dd16150dd23721d539193100e995050e464c003a64414391930baed031442464c2f7a6201439193000d9b70dd16050ef7a68414391930738dc8754e464c1ce3721d3291930008de484df61481ce37a1e319193000f49205495
  | 2 => 0x87050d54542dba618143581542bde07048552440af3a1c1265491044bc88054943408073ad9d02d815200c9d4718063544063ec2227919312bde07048542440af3a1c1265091001ceb6740b6050ac7e42014150d10b1e986050d605070267121079594305c9f4750f60544af781c1214c910738dc3841e464c412370e107d9151018f80849f614c0063e02127d8554008dd8708363544073cc1d10d894101cf30744362546abb80816154520a9ee02058541482c3f00812150d102bde307486264400378081178d920b0ec82049943440af3ac1d2689910b6f882050d54482c7e2081435052000dc8204df61480033a0807655120c9f840250543449123761f60d8943009d78155d6050c023de05765513000d9543dc56355003655077155943009d587d476150c023d5e331d855400d3454dc56355003c554543d855400e951750f6155323a554543d85548ed977150d5650402b520d17d8554c6ad78159063546df27dc54355941b7e948150f61552dfa50c543d855400e394055361540038750d54d855047f176150d545440365d454718d5100cd75119d43546df4715d43d85548dc9f6151c6354403655077158143458dd87d865650c03a550556d854345e94685076150c02e552351d854300ad568d476150c02b54e351d854300ab548d476150d16b520556d854345ad48154f6150d17a5d9d41d854300b97815536150c03c555351d854300e5556d476150c039554f51d854300e3554d476150e2a6721d54d854347d1c575536150c1b0f15d54d854300e3950553615014765dc54358141c7a9d48cdf615001b0f15d54d854045d94875076150f1e67123715814300c9f4119d435440365d07715594300e9543d076154c170f11d54d8550008f7814df62553173949f3181912c5ee020cc52644003a550f31d8554008dd86dc52090c03aa50142d850200e695054b6140802a752337d852085ae88054b6140a16ba20142d8502c2ee020587614830fb208143d852000ec8204df6148003b208337d852005c9c4750f6148112b6a006158143b6f1a1050d54540023761f42d8d51009cf8255d6050c023be097655130008ef825d954440036350f725815400ccd43dc956500023b5e220d895400d2c54dc960550038e50150d895400f0d5250f6255002ba20127d895400ec52118f6254403a550543d895100e354155362544038750d54d895100a9d4818f62544038e50154d895000e1d43553625411fc3d894355152b8d1c5750f6255003351877258543468dd87d8a5650c02b660061d894395a9d481876250c029756061d894300ad48155b6250d1f4715d54d894306c3c575536250c03e148543d894100e3551553625041b0f15d54d894100e39505536250002ba42352d894000aad48d4b62500039a54352d894000e2d54d4b625001b0f15d
  | 3 => 0x3274dd54d8540008dd3885f63502df274dd54d8543008dd3885e36482e3274dd54d8943058df8750e3648002374e217d8940058df8750e364480637e1d308d912008dd3885e4648006374e2179193005c9d375065650c02374e21795940058dd3885e5650c02375e26418d51008dd3885e5648006374e21795930058dd3889e5650c1a2f520765513106a3c58519544c41a2f520765513006a3c58519544c0122f610765454300c3d541d95150c030f5507654143b5c3f675525650c1a2f520765512006a3c58519544801a2f520765511006a3c58519544400a2f6107654d4100c3d541d950506d30fd9d5495941018bd841d952500030f550765494000c3d541d951502cf0fd9d5495940048bf8750e46480161f56076551200587d581d9544400a1f56076545430187d581d950508043fe1d5695910058bc845d952440168f211565512005a3c8455954442d30fd9d54d9151b3c3f6755364540123720d7655110048df78dcd56504123720d7654910008dd78980635441237de37355910048df3885e564801237ce2179594213a5d58190635444e37ce2179593000e1d5419063544123720d5791930048dc8355e464401327cdd4395941048df3885e464801727d1d43d8d5105a9c4849943440032750c765512000c9d431d941482bf27d9d4391920048df3885f605091a3761c61d8943908dc3845f624c012370e117d8954048dc3845f625400237e1d43d8520048df874df614802637e1d53d853200c9d1750f6454c032745d4391930bec9d1750e464c4032745d4391920008df8755b6150c2637e1d53d854300d1d175525650f072745d4395941459d48155d6050c0a3d205765513045d94715055650d16b5205565854300ad4815596050d1675de37155943029d4815cd544c47e752057355130028f778dc55650edfc51c54355151028f7188de56480e7711c53254d1200d945151c6354403351446750d5100d1c5151c6354517651c5415814345ad7189d9434800a3dc6237919200bc9f8750f6155003b1448615894339dc4714c94344adfa5185545854345d97675076150c03355c4615814345cd76745f6150c7f351c53650d1002cd7674c76150c033545c61d8943c199c4845e5650ce7711c5324c112028f4814de264400a3d20537d895445cd71750e3648003354df178d920028f78745e36481d2370e11791930048dc3845f64542b371cdd12d8542048df874df615081237ce3715192002ce71744b635081333cdd32d855202ce71744b635481327cdd43d8554acdc4315c943448e771c5d328d91200cd43145e464c0036541d41d8543c799c4841f6150c023761c40d8d5100d1d075525650d12762015758943018f8805d9544c8063e20176551122b9e8805c954448067a2017255102b6d987050d62550063ede37055942b6f1
  | 4 => 0x94000e2d4255954448038b509565510200e2d42559525013b8b1d9425515203d2c76509545493acb1e1425515203d2c7850954548168b1a1425515243b2c6850954548178b1a14255152008ed821d95150c1a3b6087654943068ed821d9525041a3b6087654940058ed821d951508163b6087654142059ac845c9515081a3b608765493106a6c58589524c41a3b6087654930048ed821d9514c802b36086418d51008ed281d9544401a3b4a07654910058ed281d94244016ab121265091000f0d5250d54448ae7321d324c1122b9ac8750940448ae5b21d5254112028ed821d954448032b5087655112028ed821d95344916b32195250d1200acd281856050d16b36087650d12028ed821d943448032b5087650112abcaf6750a4644916b32193250d121facc864c93044803c35494355102018ed821d95440912b32195250d02b0ccd2750e064480a3b4a2078d912008ed2881e464c4123b4a20791932028ed2881e464480a3b4a2079591200e1d5650d5448003875594355110b7e1c7650d54546db871d94355150b7c9d5750e56506d967e1d5495943b7c9d5750f61550032755d439193100c9d5750e464c0132755d43d915300c9d5750e464811e6721d545854347d1c575516150d1e6721d545814347d1c575516050c03475614718d5100d1d4755063544032751d6418d514f99c7850d61550032751d6018d513699d8419d4354412276106750d5104a9d8419d4354403075506750d5100d1d5419d4354403275906750d5100c9d5419d4354403875506750d5100c9d8419d4354403875506750d5017c9f8750e565045347d9d5495943b159f875076150cce671e1435594100c9d4119d4354516671e14155943b2e1c5650d5650516671e1415814325a9d481856050c032751d43d895104c9f8750e4648002a75236750d5100a9d48d9d4354002a75227650d2000a9d489d943441163721d5658543068dd831d9535040237e1d619594300a5d581856050d123721d5658143008dd831d9525001a3760c7654d40448dc875896050c023761d43d8520448df789856050d16975606750d514595c8754d5150d13171d94354950441df8754e5650c12376106750d51058dd831d95150c163760c7654143008dc875594344003175506750d5100c5d5819d435440237da21795943008dd48dcd56440023752237d9151008df8655d1090c03175537654643368dd871936354416a72115650d2000c9d4719063544032751c64d8d514599c8455f6150c02374e07655120068dd381d9534801a971613654d20058dd381d94348016a71213650d20008dd381d9544401a374e07654d10058dd381d9434400a3760c7655131138df874c65650c7e6721d43505301f95c8754d514c0063760c7655130018dd831d9524c0063760c7650930008dd38dc546480
  | 5 => 0x30d09010200010f0321001901070001134901010001031d060006020f0200070e0303001901000306360007010f0000001601010000fc1104c93044803e8441425011200f61105495044803d24c1525413200f294054950508036a501725414200e696054950508039a581525413200ea96050940448039a581525411200f492050d5254003ca481545494000da9205d152500072a1d9205094001da87648142500039a481565414201d687648152540071a1d9205495000ce9201d952500a2da1a1205495003e68684815254092ea1a1205094003ea8684814250003e1449435494100f85125056250c03e1449435053200f451254d514c803c9449545454200f251255152506b3711cd12545422cdc473449514c8b3711cd1250532aace5275460644aa73949d418191200f15515516150c03656054718d5100f154155d4354403c5505535454300e954155943440036555d41d854300d954151c6354403655046750d5100e954119d4354417a51a14150d51b2f14585054354403555c55750d5100e556154d5150d1eb56046750d5100cd57119d4354403356046750d5100cd54119d435440335507765464300e556154d514c003c54c5545454300e55315595150d27951d93154d5102d54764c55354403354c4765454349b54784c5535440b551e13154d5136b54684c55354412751e1315454304e54684c553544038d585545454300e356155151500038d505565511000e35415595150d378d1d9415515102d34765055454536cd1e1415515102d347850554544168d1a1415515137b346850554544178d1a14155151068f5811d95150c023d6047654940068f5811d951500163d6047654141068f5811d9514c003c55055418d5109ad5811906354403a5585435052000cd47358551480023d6047655120068f5811d9514801a9d1616154520058f5811d9414800a791e1214c91000f155150d5444003655c5435511000d951051c6354516e51e14150d1000cd51019d435440a6d1e14150d10029747854553440627520d7155110189d4835c5524404f35d9d10d8d51018f5811d954440063d604765491044ad4865454344026b54606018d5100e95411d943440063d6047650910b1e9486505434400339484764c9102cec4364853244112b52192150d1000cd517cdf61480033945d528d90200cd51750e36480023d462178d92003ce51754a36449133545d438d910018f51889e3644002b54627650d20008f5188de4648112b54627650d10018f5188de464429eb54626018d51008f5188de56480063d462379591000f0d525516250c02b36086750d5147acd8219d4354803336086750d5100f0d325515250c12731e1325494300ccd3754b6150803334dd52d8502aeccd3754b614c8038b589545494300e2d6255152504038b5895454
  | 6 => 0xc208003a446a9a0632f4358001d006a25eee25d12c4d8548b914e000358591088eb29abd3806c2fca785323dc93c003e154c0011c0951f283c000d80010409305ab02a3d7e11197a500002d4c910300000071c00295377a96f88ee16c0004e800000000235cf0000005e8001ddcf52943c25d000000002e2a680010d800000000001cdc09150000009c0000001da4aeaa0c90001cc000003460a95c711237000002bcd6c000e30001165293290480000000000033a70932f0b2e7d8d4c93d3d04494a4d26bac65ed9425e018000000000018eb00102ca505950a6591d9700000000000109a55bf2d310bb823eb190878008697200004c000b48001c4802000000de6a2002550cc000c2c83949c3cefb21c66cd99e044980812242f255221553e7b3bb55c9f4000301094d8000516b2622ad8008eca22ca80074a000001b81750881a98a8d5272522ad19a1ca122e527c0ba1c230c111259b800784d25881d3c80d7139d4d75a001168000017000000000c7bce5263c2c496195992312e2845506c4d94948c54cda3ab9acc4f70b29d522000000003681513b0a4387a937d5840001d05d0dfd92640a599f0007b414e96800bcc59a0f5bac659fb27800000003068006bc002a76554900029f984128879021e66be916f8000b46000b125bcc6001981d04df4007f000c4f589b8d57be6000000620000f1752230013580003a44a6159fb6643b872043ca001119154be23d25800000ca2000005975ecc6b32db8878002b90002a880b45516000304003317140021f0003f44768e55676d098de5d3b1cd818b4da5b14d43e1341e071ae75255857b1525ea6cf179ee4922445c295e6999125eed1a6ba5100e11f14ed029a3d23c99758250c2b0d6fe5452e60d2797727c5e555119cb36952b238b769bc7a2edbf8081c002d07010b180007050800130809a20b01020b0a033a210e001d121100050c112c3609000000012410061c0f6d0f00002e00133d0005090b0501100b02001e26410c103d0066054b11311101165b0100210000431735100a132916080202021b0005442f125e03030426092d0c0108020703021d05561b1a002b000309010331000000060326030b04001115030a000c000c150001010104090a2b010147050101020f6c3d010d042c171f280201041a05010100070102040703000300040e000000070138050e030505050f000000000503070000150308080f0b0c001d0c0301070d000209081a020b13090002020a0e053f0005020400002805020605110a010004000108001735020202030002000400050001021f0f04054702050a09060301000100000d0100060100011900070004163b010100210f010c20012b0b030305260a02150305000205000300011706000110000701040609010417000700020a020d001a0104010200
  | 7 => 0xb58302078366f6f6c3597601d7359ae1a4ef9aaff0e46b6c286da748f8e70221695b20d182bc6bd0d61e803e8f110523bb2077531e40311c52b9e6000c18480898002471661f95ccf2055fb65a2d48330819e7e6e14000003130e9b180060025b050009c8c780003d00193480000a910c1382425951b6b83eec487b0bfa1a7a2bc043529cce6940546ea792292b332000993464d280c6cd18c6134308d484d83e962ea10c73ac05801a340005ba4c1d8000000cd20e99cc3aa9e2e8051b2870b088f6827f32d569634345a5977282b75c10008bc00420a504b8244c7130ceaefa9a8068492fb1242d7792a4e6884722debfe1a58f2df455b10a770123b000000618008e94cc005770011300057cc6c0020d80079c0030a0009f2a7c004f200143ec298167622ac1bbc054c700845bc4c002f9373b193555e0ea69a158004213aad4800340bf0000000e04b8000000004440028f000a147c000000655990001e40e89886d672d001997658440e72cd71f86f17446e86c448e241422c46ca3191d0486d70e8834103d9bc67114b8eab16227f11ca18921c94814332a4bc5659111ea8a49b742e10d0338aa99491253cd10d04686fc4b6ba53b7a8d41f453135e1b8a62e85bd3956e24337515aa0b9aa048facd8f4aa204ec10aab937bb07a4a9d521a179ce4ea299734944a624809462254fc05244e2b55543f5919e95a65a2e00b91eb1c21c50289db845c3f80133156b74c880d95f658c5f47d28d8b120098014b788b9bd5a8a28676b2a3c69c68e983b0b952102f3e397364e305122702b1f21a8d088ac1be6b800a480e16d2c0639ee84e1f0c96bf0a06b534de0000c7ccad38c5db8b515ca65b7b00cb3340ec5400040060adea0800000888000002795919dc005193fca3a0a448001302e5e732211f5578004217f2bc000000002615d84fc002ce000001a1af057d1b8002bf9e24a000000000ab2919c8000001480000000002fccb5660016ac001f200159000668000618761e967957eec9be0ef0c5ba0007860000046f2aca12d910e67a688fbb880ec818001463d4af9922110002badb0f66a91cc0d97cc1cf108d4fa41061ed256d4d457877a80854ff2a0144628eb82065ea34d3c49e70492e580d3079a07d9ae94282e630ef182a0af5805d2420d9d8440171ee0e238008c316b928d440011ed914cc2d140f3e2619a9939dd64a9d0002af3ac0004d92cb450000000cc2e6099186fd460003ba5b0005a0000a80beb768fd39628307675cea196f365105c697e8a8a05a1564d63efd5cf3e747709348bee4f64841c768063372788fc2315b6592bef7cbf18d3480805c32f1e53467c49b2c68a62d4a20596607e418562e615d6826d4176a1ae719551c48c82ce91fed7b2cbe8c30003026ded56c514abc4e6c005067cc00012011a599407dd9a4d
  | 8 => 0x1048b9e5f669148ea55a4744316b2ceace96b30b569109e8cc0003540018c0003690e6ac5266722f2eb8b4264266dad899461fe90ab396014125aa033f69a023b58a20014e3fdaea10867800b8d2c96016f001140db4282500080062c00149eae26712f19f29a690cb976620c41aefaad6a9843f230001e0000000d80004896d0513a2ce2f48ac38dc60836cf54aa72e186a4272f0885722b80f54deaebd572561f2bbaa482b6a15ba86aedacb59d26c8981274fc0e1982ee561ad48e7032b06874bd7f000722000640007f400000000000d0a7700007200000000b2000000190000000290000000006cddd0008631a0007bc00000067451a22ea12b894be10013c429962cb39567009a7109a98ce119b26d001581f03336d271e128b60c88ca65d189b8590820006e411ae66426f8d2ed55d5cac0020d0005f49608e3c13995a1b619413d6010500044d2ff100000b14fad85c4af6272395a16dc464000003815d8f5da2
  | _ => 0
def g6K4 : Nat → Nat
  | 0 => 0x49c83546064480322b02ac28e31aa201195891454718d5147d0ac0aa833a86a8806256058419d435440292ed340a8e31aa201c15715506750d5100e0ac0aa833a86a8a2e855614119d435440382a82aa0cea1aa201495491446750d5100c4ac0a8e320c6a8805255275119d435440382a82aa6eca8c8601855585c4615814345c2aac2e233a86a8806156055819d43544021ab12288cea1aa201c1531550765454302c2aac2623b2a2a18360d605541d95150c0306b02aa0eca92800d83581550765454005c1ac0aa83b2a0a084e8560554190635440292a9239ac2a8a40018951752337d852000c4ac0a863b2a89002e25605431d9414806312b08880cea1aa201c15105506750d5100c4a8c28e300c6a88061545d581876250c0292a9218a2f2326001455590c5179193000c4a8c28f300c6a8806836095419d435451f41b04aa0cea1aa40188d826106750d5100e06c12a833a86a88062360947190635440309b04ac0cea1aa201c0d3754954d854200c16c12a83b2a2a18360b609541d95250c1b05b04aa0eca92820d82d82550765494005c16ac2843b2a88902e0b609541d9515081705b04aa0eca828401a0d825506418d510088ec48a2a38c6a880607e1d545865650c1703ab0a18ecaa2400181d845606750d5100c0eac28e320c6a8824276268419d435440303aa843aaca1a200141d945606750d5100c0fb42a90bcaca1805075668419d435441213f30a1c2f232400141d49d5c6750d5100e0a48aa833a86a8807055505119d43544021af2eb46a3b0a8793e8020585435052000e60100e6b0aa29000638604201d954480039822e1066fb0a4001c8943080765512000a4bb48a2a38c6a880507da45151c6354402a4b242a6e2b1aa8012954920d17d85540098a4c2a2a1ec2aa00525e455419d435440382aa9a88cea1aa2014579755b51d85434594a44a82ab6c2a18063208186dc52090c02d12921026fb0a40016495908137d85208595444a80a16c28142c9a2255054b6140802593121066fb0a40016894908337d852000b24ac8419bec290006a252020cdf6148002a53202a6e4b02a80152591153725815400d4290a9031ec4a88051556461dc96150c0345290a86a5b128001a290855352d89400094aa4906a8c4c88326256131219d435440382aa9890cea1aa2014a94908207d895400a34ac84103ec4aa0054564454dcd6155002a1b242a6e6b0aa801a894848020d8d5100d24ac240106c6a8b4e8560554193635440341b04aa0c9b1aa201a154854753d8d4100e0aaa4623b2a2a1b9e5221d205495090c03c12a0a92872320401c15549046750d5100c4ca3d00320c6a88044da6054dc5635500225d302a6e4b02a80109d9891e64d8d5100a0fcc2a833a86a8807055527119d435440313309400cea1aa201c1954a006750d51
  | 1 => 0x245d3cd229800458c89a4a230005e3a00116006237a58d46d0019c007400254b01580198bf000045ca12d9ba41307a2ccd0330124db8a3644052b2e0db60a47b83234f0c288110e4ea4142c203c631f814a6608e000001c858b0ec53bd652f752a21ed033049844ac0035800b42a2111f12002b43035178dc08f2230f8e000453295e9f1b3492eae58800d80000188d400800d1e200002a537148b8700c7c7e19986897d020842c77c3d401e86158b800262a0460b00468803b0000156000021801220003c00aa688c9fe31604716c000046256b85204a04f9869ea50264e249c8f87ec28402d7d921c4900026418032d2c8000e922f8ec00004393c3000000543a733b52cbc84465448e78000011e2734208e0280a0009d000689414403f9dc4004006b313672618408000c400200a9a01a20c00898031c00890408e3341061000088944900aa08410400018408609438050201a316579c087441324c1122bcd043a20a12808915e5821d10549504480358300890c2b1286735c079441324c11200e308baa0a946c81005685242045e3648002ac2b21022f1b240018c9806086750d5100e249baa0a96c28115e2a21d6050940448af0d10eb02a4a8224018a980508765511205c54c02843b28089227121d92050d5254002b12921026fb0a40015495908137d852001c54c22403b2a4a00070a481541d952500070d2b0810eca8284010e989080765512000a54a48403b2a8900051a564201d9544800350a82c10cea1aa359a8548448615894300d22ac22430ac4a19ce6121d1250d414c8e72890e892a6a8a6401585921454718d5100a62c90a233a86a8a2ea1609411d94344802b0a538828e31aa393c8527505438191200a6294e2033a86a889e31
  | _ => 0
def g6K3 : Nat → Nat
  | 0 => 0x1a0245180305ac40e0157266d73e010022e29931e000180480880a0200002a000000420a00012100930668201cd615452000b20528201cd615452000b10568201cd615452000c2852581080765512000c1856581080765512000c3045d8908337d852000d2045d4908337d852000d1045d5908337d852000e02601825506750d5100c2262543080765512000d0256543080765512000b01688915506750d5100d01649541446750d5100c2149d4920d518191200d014a554c406750d5100c05605945606750d5100c05625541446750d5100c03609945606750d5100d20524201cd615452000e2045d4808337d852000e2060543080765512000a225282061b714824300a125682061b7148243008a26a54808337d852000c825654808337d8520
  | _ => 0
def g6K2 : Nat → Nat
  | 0 => 0xc850004481ba524201cd615452000c802b4a484039ac2a8a400182045da952020cdf61480038008bab2a40419bec29000700159605430807655120
  | _ => 0
def g6N (k : Nat) : Nat :=
  match k with
  | 2 => 5
  | 3 => 25
  | 4 => 153
  | 5 => 840
  | 6 => 2840
  | 7 => 993
  | 8 => 45
  | 9 => 1
  | _ => 0
def g6R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt g6K2 (i*91) 83
  | 3 => packedAt g6K3 (i*80) 72
  | 4 => packedAt g6K4 (i*69) 61
  | 5 => packedAt g6K5 (i*58) 50
  | 6 => packedAt g6K6 (i*47) 39
  | 7 => packedAt g6K7 (i*36) 28
  | 8 => packedAt g6K8 (i*25) 17
  | 9 => packedAt g6K9 (i*14) 6
  | _ => 0
def g6H (k i : Nat) : Nat :=
  match k with
  | 2 => g6Hint (packedAt g6K2 (i*91+83) 8)
  | 3 => g6Hint (packedAt g6K3 (i*80+72) 8)
  | 4 => g6Hint (packedAt g6K4 (i*69+61) 8)
  | 5 => g6Hint (packedAt g6K5 (i*58+50) 8)
  | 6 => g6Hint (packedAt g6K6 (i*47+39) 8)
  | 7 => g6Hint (packedAt g6K7 (i*36+28) 8)
  | 8 => g6Hint (packedAt g6K8 (i*25+17) 8)
  | 9 => g6Hint (packedAt g6K9 (i*14+6) 8)
  | _ => 0
def g6I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt g6K2 (457+((h/2+packedAt g6K2 (455+(h % 2)*1) 1) % 7)*4) 4
  | 3 => packedAt g6K3 (2040+((h/10+packedAt g6K3 (2000+(h % 10)*4) 4) % 45)*6) 6
  | 4 => packedAt g6K4 (10989+((h/72+packedAt g6K4 (10557+(h % 72)*6) 6) % 256)*9) 9
  | 5 => packedAt g6K5 (52072+((h/419+packedAt g6K5 (48720+(h % 419)*8) 8) % 1483)*11) 11
  | 6 => packedAt g6K6 (145736+((h/1532+packedAt g6K6 (133480+(h % 1532)*8) 8) % 5424)*13) 13
  | 7 => packedAt g6K7 (39956+((h/526+packedAt g6K7 (35748+(h % 526)*8) 8) % 1866)*11) 11
  | 8 => packedAt g6K8 (1251+((h/21+packedAt g6K8 (1125+(h % 21)*6) 6) % 81)*7) 7
  | 9 => packedAt g6K9 (15+((h/1+packedAt g6K9 (14+(h % 1)*1) 1) % 1)*1) 1
  | _ => 0
def g6Pos : Nat → Bits
  | 0 => 0xc84b22bdf44b22512fbb44bffc250888f827c7
  | 1 => 0x549544c45895eee257ddbff12c4a11110be3f8
  | 2 => 0xa126efa89526f75ffc8949525491222791fc41
  | 3 => 0xc638f6dedbff44649911926499024787fe4088
  | 4 => 0xfbff8710e2388788e21e2388e21c87fa208912
  | 5 => 0x3c0f81f03c0f80f03e03c0f03e0fc44451224
  | _ => 0
def g6Neg : Nat → Bits
  | 0 => 0x1ffc00000003ffc00ffc0000007803c7
  | 1 => 0xfff003fffff00000000001e3f8
  | 2 => 0xffe00000fffffc0000000000000781fc00
  | 3 => 0xfc00ffffffff00000000000000000787fe0000
  | 4 => 0xffff00000000000000000000000007f8000000
  | 5 => 0xf800000000
  | _ => 0
def g6Atlas : Atlas := ⟨9,rawDecor 63 g6Pos g6Neg, 0xfffffffefefeeca0fffffffefefeeca0fffffffefefeeca0fffffffefefeeca0fffffffefefeeca0fffffffefefeeca0fffffffefefeeca0fffffffefefeeca0, g6N, g6R, g6H, g6I⟩
end PEqualNP.Outside.L_meta_10548
namespace PEqualNP.Outside.L_meta_10548
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_2_0 : Interval g0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem all0_2 : Interval g0Atlas 2 0 4 := b0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_3_0 : Interval g0Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem all0_3 : Interval g0Atlas 3 0 16 := b0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_0 : Interval g0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_32 : Interval g0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_4_64 : Interval g0Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem all0_4 : Interval g0Atlas 4 0 92 := (concat b0_4_0 (concat b0_4_32 b0_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_0 : Interval g0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_5_32 : Interval g0Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem all0_5 : Interval g0Atlas 5 0 44 := (concat b0_5_0 b0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b0_6_0 : Interval g0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all0_6 : Interval g0Atlas 6 0 1 := b0_6_0
theorem all0 : ∀ k ≤ 6, ∀ i < count g0Atlas k, checkRow g0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all0_2 i (by omega) hi
  · exact all0_3 i (by omega) hi
  · exact all0_4 i (by omega) hi
  · exact all0_5 i (by omega) hi
  · exact all0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_2_0 : Interval g1Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem all1_2 : Interval g1Atlas 2 0 6 := b1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_3_0 : Interval g1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_3_32 : Interval g1Atlas 3 32 4 := block_range (n:=4) (by decide +kernel)
theorem all1_3 : Interval g1Atlas 3 0 36 := (concat b1_3_0 b1_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_0 : Interval g1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_32 : Interval g1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_64 : Interval g1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_96 : Interval g1Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_4_128 : Interval g1Atlas 4 128 4 := block_range (n:=4) (by decide +kernel)
theorem all1_4 : Interval g1Atlas 4 0 132 := (concat (concat b1_4_0 b1_4_32) (concat b1_4_64 (concat b1_4_96 b1_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_5_0 : Interval g1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_5_32 : Interval g1Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem all1_5 : Interval g1Atlas 5 0 48 := (concat b1_5_0 b1_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b1_6_0 : Interval g1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all1_6 : Interval g1Atlas 6 0 1 := b1_6_0
theorem all1 : ∀ k ≤ 6, ∀ i < count g1Atlas k, checkRow g1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all1_2 i (by omega) hi
  · exact all1_3 i (by omega) hi
  · exact all1_4 i (by omega) hi
  · exact all1_5 i (by omega) hi
  · exact all1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_2_0 : Interval g2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem all2_2 : Interval g2Atlas 2 0 4 := b2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_3_0 : Interval g2Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem all2_3 : Interval g2Atlas 3 0 16 := b2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_4_0 : Interval g2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_4_32 : Interval g2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_4_64 : Interval g2Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem all2_4 : Interval g2Atlas 4 0 92 := (concat b2_4_0 (concat b2_4_32 b2_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_5_0 : Interval g2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_5_32 : Interval g2Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem all2_5 : Interval g2Atlas 5 0 44 := (concat b2_5_0 b2_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b2_6_0 : Interval g2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all2_6 : Interval g2Atlas 6 0 1 := b2_6_0
theorem all2 : ∀ k ≤ 6, ∀ i < count g2Atlas k, checkRow g2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all2_2 i (by omega) hi
  · exact all2_3 i (by omega) hi
  · exact all2_4 i (by omega) hi
  · exact all2_5 i (by omega) hi
  · exact all2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_2_0 : Interval g3Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem all3_2 : Interval g3Atlas 2 0 2 := b3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_3_0 : Interval g3Atlas 3 0 20 := block_range (n:=20) (by decide +kernel)
theorem all3_3 : Interval g3Atlas 3 0 20 := b3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_4_0 : Interval g3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_4_32 : Interval g3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_4_64 : Interval g3Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_4_96 : Interval g3Atlas 4 96 2 := block_range (n:=2) (by decide +kernel)
theorem all3_4 : Interval g3Atlas 4 0 98 := (concat (concat b3_4_0 b3_4_32) (concat b3_4_64 b3_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_5_0 : Interval g3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_5_32 : Interval g3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem all3_5 : Interval g3Atlas 5 0 44 := (concat b3_5_0 b3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b3_6_0 : Interval g3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all3_6 : Interval g3Atlas 6 0 1 := b3_6_0
theorem all3 : ∀ k ≤ 6, ∀ i < count g3Atlas k, checkRow g3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all3_2 i (by omega) hi
  · exact all3_3 i (by omega) hi
  · exact all3_4 i (by omega) hi
  · exact all3_5 i (by omega) hi
  · exact all3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_3_0 : Interval g4Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem all4_3 : Interval g4Atlas 3 0 2 := b4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_4_0 : Interval g4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_4_32 : Interval g4Atlas 4 32 30 := block_range (n:=30) (by decide +kernel)
theorem all4_4 : Interval g4Atlas 4 0 62 := (concat b4_4_0 b4_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_5_0 : Interval g4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_5_32 : Interval g4Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem all4_5 : Interval g4Atlas 5 0 40 := (concat b4_5_0 b4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b4_6_0 : Interval g4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all4_6 : Interval g4Atlas 6 0 1 := b4_6_0
theorem all4 : ∀ k ≤ 6, ∀ i < count g4Atlas k, checkRow g4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all4_3 i (by omega) hi
  · exact all4_4 i (by omega) hi
  · exact all4_5 i (by omega) hi
  · exact all4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_2_0 : Interval g5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem all5_2 : Interval g5Atlas 2 0 5 := b5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_3_0 : Interval g5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem all5_3 : Interval g5Atlas 3 0 25 := b5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_4_0 : Interval g5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_4_32 : Interval g5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_4_64 : Interval g5Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem all5_4 : Interval g5Atlas 4 0 91 := (concat b5_4_0 (concat b5_4_32 b5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_5_0 : Interval g5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_5_32 : Interval g5Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem all5_5 : Interval g5Atlas 5 0 44 := (concat b5_5_0 b5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b5_6_0 : Interval g5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem all5_6 : Interval g5Atlas 6 0 1 := b5_6_0
theorem all5 : ∀ k ≤ 6, ∀ i < count g5Atlas k, checkRow g5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all5_2 i (by omega) hi
  · exact all5_3 i (by omega) hi
  · exact all5_4 i (by omega) hi
  · exact all5_5 i (by omega) hi
  · exact all5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_2_0 : Interval g6Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem all6_2 : Interval g6Atlas 2 0 5 := b6_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_3_0 : Interval g6Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem all6_3 : Interval g6Atlas 3 0 25 := b6_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_4_0 : Interval g6Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_4_32 : Interval g6Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_4_64 : Interval g6Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_4_96 : Interval g6Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_4_128 : Interval g6Atlas 4 128 25 := block_range (n:=25) (by decide +kernel)
theorem all6_4 : Interval g6Atlas 4 0 153 := (concat (concat b6_4_0 b6_4_32) (concat b6_4_64 (concat b6_4_96 b6_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_0 : Interval g6Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_32 : Interval g6Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_64 : Interval g6Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_96 : Interval g6Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_128 : Interval g6Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_160 : Interval g6Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_192 : Interval g6Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_224 : Interval g6Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_256 : Interval g6Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_288 : Interval g6Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_320 : Interval g6Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_352 : Interval g6Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_384 : Interval g6Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_416 : Interval g6Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_448 : Interval g6Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_480 : Interval g6Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_512 : Interval g6Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_544 : Interval g6Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_576 : Interval g6Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_608 : Interval g6Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_640 : Interval g6Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_672 : Interval g6Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_704 : Interval g6Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_736 : Interval g6Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_768 : Interval g6Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_800 : Interval g6Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_5_832 : Interval g6Atlas 5 832 8 := block_range (n:=8) (by decide +kernel)
theorem all6_5 : Interval g6Atlas 5 0 840 := (concat (concat (concat (concat b6_5_0 (concat b6_5_32 b6_5_64)) (concat b6_5_96 (concat b6_5_128 b6_5_160))) (concat (concat b6_5_192 (concat b6_5_224 b6_5_256)) (concat (concat b6_5_288 b6_5_320) (concat b6_5_352 b6_5_384)))) (concat (concat (concat b6_5_416 (concat b6_5_448 b6_5_480)) (concat (concat b6_5_512 b6_5_544) (concat b6_5_576 b6_5_608))) (concat (concat b6_5_640 (concat b6_5_672 b6_5_704)) (concat (concat b6_5_736 b6_5_768) (concat b6_5_800 b6_5_832)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_0 : Interval g6Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_32 : Interval g6Atlas 6 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_64 : Interval g6Atlas 6 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_96 : Interval g6Atlas 6 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_128 : Interval g6Atlas 6 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_160 : Interval g6Atlas 6 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_192 : Interval g6Atlas 6 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_224 : Interval g6Atlas 6 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_256 : Interval g6Atlas 6 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_288 : Interval g6Atlas 6 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_320 : Interval g6Atlas 6 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_352 : Interval g6Atlas 6 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_384 : Interval g6Atlas 6 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_416 : Interval g6Atlas 6 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_448 : Interval g6Atlas 6 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_480 : Interval g6Atlas 6 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_512 : Interval g6Atlas 6 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_544 : Interval g6Atlas 6 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_576 : Interval g6Atlas 6 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_608 : Interval g6Atlas 6 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_640 : Interval g6Atlas 6 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_672 : Interval g6Atlas 6 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_704 : Interval g6Atlas 6 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_736 : Interval g6Atlas 6 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_768 : Interval g6Atlas 6 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_800 : Interval g6Atlas 6 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_832 : Interval g6Atlas 6 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_864 : Interval g6Atlas 6 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_896 : Interval g6Atlas 6 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_928 : Interval g6Atlas 6 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_960 : Interval g6Atlas 6 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_992 : Interval g6Atlas 6 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1024 : Interval g6Atlas 6 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1056 : Interval g6Atlas 6 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1088 : Interval g6Atlas 6 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1120 : Interval g6Atlas 6 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1152 : Interval g6Atlas 6 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1184 : Interval g6Atlas 6 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1216 : Interval g6Atlas 6 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1248 : Interval g6Atlas 6 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1280 : Interval g6Atlas 6 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1312 : Interval g6Atlas 6 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1344 : Interval g6Atlas 6 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1376 : Interval g6Atlas 6 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1408 : Interval g6Atlas 6 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1440 : Interval g6Atlas 6 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1472 : Interval g6Atlas 6 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1504 : Interval g6Atlas 6 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1536 : Interval g6Atlas 6 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1568 : Interval g6Atlas 6 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1600 : Interval g6Atlas 6 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1632 : Interval g6Atlas 6 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1664 : Interval g6Atlas 6 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1696 : Interval g6Atlas 6 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1728 : Interval g6Atlas 6 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1760 : Interval g6Atlas 6 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1792 : Interval g6Atlas 6 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1824 : Interval g6Atlas 6 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1856 : Interval g6Atlas 6 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1888 : Interval g6Atlas 6 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1920 : Interval g6Atlas 6 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1952 : Interval g6Atlas 6 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_1984 : Interval g6Atlas 6 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2016 : Interval g6Atlas 6 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2048 : Interval g6Atlas 6 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2080 : Interval g6Atlas 6 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2112 : Interval g6Atlas 6 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2144 : Interval g6Atlas 6 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2176 : Interval g6Atlas 6 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2208 : Interval g6Atlas 6 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2240 : Interval g6Atlas 6 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2272 : Interval g6Atlas 6 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2304 : Interval g6Atlas 6 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2336 : Interval g6Atlas 6 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2368 : Interval g6Atlas 6 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2400 : Interval g6Atlas 6 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2432 : Interval g6Atlas 6 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2464 : Interval g6Atlas 6 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2496 : Interval g6Atlas 6 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2528 : Interval g6Atlas 6 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2560 : Interval g6Atlas 6 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2592 : Interval g6Atlas 6 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2624 : Interval g6Atlas 6 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2656 : Interval g6Atlas 6 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2688 : Interval g6Atlas 6 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2720 : Interval g6Atlas 6 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2752 : Interval g6Atlas 6 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2784 : Interval g6Atlas 6 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_6_2816 : Interval g6Atlas 6 2816 24 := block_range (n:=24) (by decide +kernel)
theorem all6_6 : Interval g6Atlas 6 0 2840 := (concat (concat (concat (concat (concat (concat b6_6_0 b6_6_32) (concat b6_6_64 (concat b6_6_96 b6_6_128))) (concat (concat b6_6_160 (concat b6_6_192 b6_6_224)) (concat b6_6_256 (concat b6_6_288 b6_6_320)))) (concat (concat (concat b6_6_352 b6_6_384) (concat b6_6_416 (concat b6_6_448 b6_6_480))) (concat (concat b6_6_512 (concat b6_6_544 b6_6_576)) (concat b6_6_608 (concat b6_6_640 b6_6_672))))) (concat (concat (concat (concat b6_6_704 b6_6_736) (concat b6_6_768 (concat b6_6_800 b6_6_832))) (concat (concat b6_6_864 (concat b6_6_896 b6_6_928)) (concat b6_6_960 (concat b6_6_992 b6_6_1024)))) (concat (concat (concat b6_6_1056 b6_6_1088) (concat b6_6_1120 (concat b6_6_1152 b6_6_1184))) (concat (concat b6_6_1216 (concat b6_6_1248 b6_6_1280)) (concat b6_6_1312 (concat b6_6_1344 b6_6_1376)))))) (concat (concat (concat (concat (concat b6_6_1408 b6_6_1440) (concat b6_6_1472 (concat b6_6_1504 b6_6_1536))) (concat (concat b6_6_1568 (concat b6_6_1600 b6_6_1632)) (concat b6_6_1664 (concat b6_6_1696 b6_6_1728)))) (concat (concat (concat b6_6_1760 b6_6_1792) (concat b6_6_1824 (concat b6_6_1856 b6_6_1888))) (concat (concat b6_6_1920 (concat b6_6_1952 b6_6_1984)) (concat b6_6_2016 (concat b6_6_2048 b6_6_2080))))) (concat (concat (concat (concat b6_6_2112 b6_6_2144) (concat b6_6_2176 (concat b6_6_2208 b6_6_2240))) (concat (concat b6_6_2272 (concat b6_6_2304 b6_6_2336)) (concat b6_6_2368 (concat b6_6_2400 b6_6_2432)))) (concat (concat (concat b6_6_2464 (concat b6_6_2496 b6_6_2528)) (concat b6_6_2560 (concat b6_6_2592 b6_6_2624))) (concat (concat b6_6_2656 (concat b6_6_2688 b6_6_2720)) (concat b6_6_2752 (concat b6_6_2784 b6_6_2816)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_0 : Interval g6Atlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_32 : Interval g6Atlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_64 : Interval g6Atlas 7 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_96 : Interval g6Atlas 7 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_128 : Interval g6Atlas 7 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_160 : Interval g6Atlas 7 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_192 : Interval g6Atlas 7 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_224 : Interval g6Atlas 7 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_256 : Interval g6Atlas 7 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_288 : Interval g6Atlas 7 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_320 : Interval g6Atlas 7 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_352 : Interval g6Atlas 7 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_384 : Interval g6Atlas 7 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_416 : Interval g6Atlas 7 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_448 : Interval g6Atlas 7 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_480 : Interval g6Atlas 7 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_512 : Interval g6Atlas 7 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_544 : Interval g6Atlas 7 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_576 : Interval g6Atlas 7 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_608 : Interval g6Atlas 7 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_640 : Interval g6Atlas 7 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_672 : Interval g6Atlas 7 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_704 : Interval g6Atlas 7 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_736 : Interval g6Atlas 7 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_768 : Interval g6Atlas 7 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_800 : Interval g6Atlas 7 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_832 : Interval g6Atlas 7 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_864 : Interval g6Atlas 7 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_896 : Interval g6Atlas 7 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_928 : Interval g6Atlas 7 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_960 : Interval g6Atlas 7 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_7_992 : Interval g6Atlas 7 992 1 := block_range (n:=1) (by decide +kernel)
theorem all6_7 : Interval g6Atlas 7 0 993 := (concat (concat (concat (concat (concat b6_7_0 b6_7_32) (concat b6_7_64 b6_7_96)) (concat (concat b6_7_128 b6_7_160) (concat b6_7_192 b6_7_224))) (concat (concat (concat b6_7_256 b6_7_288) (concat b6_7_320 b6_7_352)) (concat (concat b6_7_384 b6_7_416) (concat b6_7_448 b6_7_480)))) (concat (concat (concat (concat b6_7_512 b6_7_544) (concat b6_7_576 b6_7_608)) (concat (concat b6_7_640 b6_7_672) (concat b6_7_704 b6_7_736))) (concat (concat (concat b6_7_768 b6_7_800) (concat b6_7_832 b6_7_864)) (concat (concat b6_7_896 b6_7_928) (concat b6_7_960 b6_7_992)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_8_0 : Interval g6Atlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_8_32 : Interval g6Atlas 8 32 13 := block_range (n:=13) (by decide +kernel)
theorem all6_8 : Interval g6Atlas 8 0 45 := (concat b6_8_0 b6_8_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem b6_9_0 : Interval g6Atlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem all6_9 : Interval g6Atlas 9 0 1 := b6_9_0
theorem all6 : ∀ k ≤ 9, ∀ i < count g6Atlas k, checkRow g6Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact all6_2 i (by omega) hi
  · exact all6_3 i (by omega) hi
  · exact all6_4 i (by omega) hi
  · exact all6_5 i (by omega) hi
  · exact all6_6 i (by omega) hi
  · exact all6_7 i (by omega) hi
  · exact all6_8 i (by omega) hi
  · exact all6_9 i (by omega) hi
end PEqualNP.Outside.L_meta_10548
namespace PEqualNP.Outside.L_meta_10548
open PEqualNP.Outside.L_meta_10548.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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

theorem bound0 (cert : Complete g0Atlas) : Lower true (roots g0Atlas) (target g0Atlas) 7 := by
  have ready : Ready g0Atlas (asRow g0Pos) (asRow g0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 16, 20),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bound1 (cert : Complete g1Atlas) : Lower true (roots g1Atlas) (target g1Atlas) 7 := by
  have ready : Ready g1Atlas (asRow g1Pos) (asRow g1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 32, 40),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bound2 (cert : Complete g2Atlas) : Lower true (roots g2Atlas) (target g2Atlas) 7 := by
  have ready : Ready g2Atlas (asRow g2Pos) (asRow g2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bound3 (cert : Complete g3Atlas) : Lower true (roots g3Atlas) (target g3Atlas) 7 := by
  have ready : Ready g3Atlas (asRow g3Pos) (asRow g3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bound4 (cert : Complete g4Atlas) : Lower true (roots g4Atlas) (target g4Atlas) 7 := by
  have ready : Ready g4Atlas (asRow g4Pos) (asRow g4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bound5 (cert : Complete g5Atlas) : Lower true (roots g5Atlas) (target g5Atlas) 7 := by
  have ready : Ready g5Atlas (asRow g5Pos) (asRow g5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bound6 (cert : Complete g6Atlas) (ss : ∀ v : Fin 6, Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD v.val zero)) 7) : Lower true (roots g6Atlas) (target g6Atlas) 10 := by
  have ready : Ready g6Atlas (asRow g6Pos) (asRow g6Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip g6Atlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfffffffefffefffefffffffefefeeca0fffffffefffefffefffffffefefeeca0fffffffefffefffefffffffefefeeca0fffffffefffefffefffffffefefeeca0
theorem fullBound (cert0 : Complete g0Atlas) (cert1 : Complete g1Atlas) (cert2 : Complete g2Atlas) (cert3 : Complete g3Atlas) (cert4 : Complete g4Atlas) (cert5 : Complete g5Atlas) (cert6 : Complete g6Atlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD 0 zero)) 7 :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bound0 cert0)
  have s1 : Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD 1 zero)) 7 :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bound1 cert1)
  have s2 : Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD 2 zero)) 7 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bound2 cert2)
  have s3 : Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD 3 zero)) 7 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bound3 cert3)
  have s4 : Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD 4 zero)) 7 :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bound4 cert4)
  have s5 : Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD 5 zero)) 7 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bound5 cert5)
  have allCuts : ∀ v : Fin 6, Slice true (roots g6Atlas) (target g6Atlas) (neg ((roots g6Atlas).getD v.val zero)) 7 := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := bound6 cert6 allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 64 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  exact lift
def posted (x : Fin 7 → Bool) := decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 7) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 7 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
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
  unfold PEqualNP.Outside.L_meta_10548.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[7,2]⟩,⟨.or,[8,3]⟩,⟨.or,[5,6]⟩,⟨.and,[9,10]⟩,⟨.or,[8,6]⟩,⟨.and,[4,12]⟩,⟨.and,[0,2]⟩,⟨.and,[1,3]⟩,⟨.or,[14,15]⟩,⟨.or,[16,13]⟩,⟨.or,[17,11]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,18⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
    exact ⟨mono,18,monoShape,by change 12 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_10548

open PEqualNP.Outside.L_meta_10548 in
theorem PEqualNP.Outside.L_meta_10548 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound all0 all1 all2 all3 all4 all5 all6)
