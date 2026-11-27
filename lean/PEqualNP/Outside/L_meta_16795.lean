import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_16795.Model
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


end PEqualNP.Outside.L_meta_16795.Model

namespace PEqualNP.Outside.L_meta_16795
open PEqualNP.Outside.L_meta_16795.Model
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

def SBf (j : Nat) : Nat := [7, 7, 7, 5, 5, 8].getD j 0

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

end PEqualNP.Outside.L_meta_16795

namespace PEqualNP.Outside.L_meta_16795
open PEqualNP.Outside.L_meta_16795.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x1036bd1960e342000000c003800000560512c509870000008803e243035c786242eb4a8f3a649294084d2704a82931628a084a00604024b0800001cc0417c0ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1d9a8361f3f0682432301d030442f10c4a633d0a822270120006553281072010a0000c5a22a14007d000c46e200005452723b0b4006f40800102b250000a001e8001a16000000079230b0128328974c87100000a86727a086a1e080d0000e2d9acb85f0390878192b89896001f800907b3682c8e590014c82613b884d80c340c0f05012130923605000660000000004e118b8004d371d4c428201c0003a111cca413000742e841f03cf8582b1a4002f33000fe380e0081810209098081804000018240410ac080828003c04300000002c082c00080098240808180c0c481000009e7ca721cf54a439ea8c873e5090e7ca621e794c439ea90873d5110e7ca021cf94f429ea8e853e50d0a7aa92157d4d42ae29a859f5350a78a6a16714d428e29a85af5250a7ea2a14f141429f2a0853f54cca78a9994f952329eaa4659c438caeca3195d546329faa2653c544ca7ca8194f55032ce218653e53d067aa5a0cf943419eaa4835f53506b8a6a0e7d4d419e29a839c5350638a6a0cfd4941dba8a833c505067ca820cfd53319e2a6633e548c67aa918e710e31b7294636d528c67ea898cf151319f2a0633d540c7388618cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cf951219eaa2433e540867aa810f948421af29c815d539027ca7206794e408f29c819d539027aa5204f546409f284813e531027aa4204f544409f28081ba501027ca9984f55330ce21e613e548c27aa9184fd51309e2a2619c434c2dea4985b14930bba8a6174514c27ea8184f150309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x68049e81602ec0002670090000628800088000e01402cc90304000600aa80800000080000c80c68718d51d0a1e63943428d58454ccb14439463287594430ca8d6210c328718d52d061e63943418b58854cc70c4394a3187594430c6956110c318718d544863860551218718d540861c63548408718d511030c4314930c510c514c21e63d50308b588540c23561150308718d54c821e63d52208718d54c421e63d5210
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (864+((h/16+packedAt s0K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s0K4 (3970+((h/44+packedAt s0K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s0K3 (1036+((h/8+packedAt s0K3 (988+(h % 8)*6) 6) % 45)*6) 6
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xc0ffffc0fff83fff07c1e0fffe1fe07fd13e73
  | 3 => 0xff03ffff03ffc1fff801ff07ffe1ff81e1cf9c
  | 4 => 0x3fffffc0001fffffe0007fffe0001fe0fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x44100888209000002942410900222a280650a5
  | 2 => 0x92299106492270cb0290a8d2b2154154d12652
  | 3 => 0xa4aa2121a46135550213a44d5419505618b18
  | 4 => 0x2cb344a49074a5a69cf4108769980619ba0de0
  | 5 => 0x30c38738e38739f8e739dce071111861fdf000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_16795
namespace PEqualNP.Outside.L_meta_16795
open PEqualNP.Outside.L_meta_16795.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x100009419240101b5e9d50e562c888285800918291802678380300c004441920f008402c029801c0000b9f1a954ad2a14eae348c0200100081382046045286ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x83098000000300a03a001180d0a151d9f4d8002e94028473b1a902683b8d42e063f17c0000219ec002b0d800004c21000123a3f800a671378f0626d001e40000001549c801c8a8e61a13178f8070f18c4a2c00000cc001e9d0000400000000b0c800884a0109c0000201700a6700000008200000005911000c4003d1e0a8453585800000f8205a0a008c0202100190660f348bc3052090b800201f10400462400096653913d08321a000ae002b000525b00000000030838220000000000c28890923f380e0dc00268d8385a0000000003a8001a3700160000000004080408040004040000140c101c0400380c000c0400001ce40c00180c08000020040824000000180c5804067ca5a1cf547439f286873d5490edea4a1db14943cfa9a87af5250e78a4a1eb1494396292873f5150e78a0a1cf950439ea9c853e5290a7aa3214f942429ea98853e5210b5ca4214f544429f280853e54cca7aa9996b10b32bb28e657551cca7ea9194f152329faa2653c544ca7ca8194f55032d6210653d53d067ca5a0cf943419eaa4836f52506d8a4a0cfd4d41d7a92833c5250758a4a0cb14941dba8a833c505067ca820cf953319eaa6636e52cc6daa598cf952319eaa4636e528c6daa518cf951319eaa2633e540c67aa818f54c4319faa6433c54c867ca910cf55221af29c435d53887588510cfd51219e2a2433e540867aa810eb10821b7294816d529027aa7204f94a40d7294812e529035aa5204f546409f284813d531027ca4204f544409f28081ba501027ca9984f553309faa4613c548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320d6216413e548827aa9104fd51209e2a2415f53482b8a6906b10920bba8a4174514827ea8104f150209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xa8080e4080009800247000000025000062806840000000000000280160306007800008b2012000b0cb800001000420000038b18951d0e2e6294343c910a51cca3561152328b594420ca8d63108328b18953d062e62943418b189544c63860551318b189540c61d6315321c394c428862d6510821a9584420862c6254c408b189511022c62553308b98b548c30c5310920c9108514822e62d50208758c540823561150208b18954c422e62d5210
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (864+((h/16+packedAt s1K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s1K4 (3970+((h/44+packedAt s1K4 (3618+(h % 44)*8) 8) % 194)*9) 9
  | 3 => packedAt s1K3 (1036+((h/8+packedAt s1K3 (988+(h % 8)*6) 6) % 58)*6) 6
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xe0ffffc0fe0fffff0783e0fffe1e07ffd23e4f
  | 3 => 0xff03ffff000fc1fff803ff07ffe00781e3cf8c
  | 4 => 0x3fffffff001fffffc0007fffff801fc0ff0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x20080888240200002904a108802290a404d095
  | 2 => 0x4a3191064894b0cb02a148d332142558d2264a
  | 3 => 0x865aa2921d29135558427a45d540560d634b8c
  | 4 => 0x14a344249181a5a694e8108669996011b80d60
  | 5 => 0x18c38738e1ce39f8e7739ce071118461ffb000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_16795
namespace PEqualNP.Outside.L_meta_16795
open PEqualNP.Outside.L_meta_16795.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1d8000008a36a019b04afdbbe00c9380003c33914d802c00002ab3abc2003e04000182498b005c03d1a00f2e00e80000ea4a942cb4000420101a3000d8078018801c0ce2248a8834100891950e13000f02081010000088040418008002840604082bda8287785050edca421db54843bba8a85745150abca6215754c429faa2653c544caeea2995d14532bda826578504ca7ca8194f55032b7a92836c52506f4a020de540419f2a6633d54cc6dca598db54b319f2a4633d548c6f4a118de542319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502eca2205d544409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f209f2a4413d54882eca3105d546209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (718+((h/13+packedAt s2K5 (640+(h % 13)*6) 6) % 53)*7) 7
  | 4 => packedAt s2K4 (1875+((h/21+packedAt s2K4 (1728+(h % 21)*7) 7) % 92)*7) 7
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 1 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 3 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 4 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x309118a290425014a849d0930194d21886315c
  | 1 => 0x52922864129212816942528510a154a8b284c5
  | 3 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 4 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_16795
namespace PEqualNP.Outside.L_meta_16795
open PEqualNP.Outside.L_meta_16795.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1ffc1fffff83f83fe0ff83fc3ffff03ec733f3
  | 1 => 0xe0ffe07c1ffc1fc3ff07fc1fc3c0ffc179cd9c
  | 2 => 0xffffff801ffffffc0007fffffc00ffff81fe1f
  | 4 => 0xffffffe0001ffffff8001fffff0001fe0fe0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4244451104250808a849a124065290944310b1
  | 1 => 0xca48c321292129416942a50c4286a584594594
  | 2 => 0x491080a5242129410844a52a8084a2980aa0a
  | 4 => 0x94a2124a034a54e65290421b312c0309ac0f40
  | 5 => 0x18c39c739c739f3b9ce7738222308c31f7f000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeee0e0eaeae0e0eeeee0e0eaeae0e0eeeee0e0eaeae0e0eeeee0e0eaeae0e0eeeee0e0eaeae0e0eeeee0e0eaeae0e0eeeee0e0eaeae0e0eeeee0e0eaeae0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_16795
namespace PEqualNP.Outside.L_meta_16795
open PEqualNP.Outside.L_meta_16795.Model
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
  | 0 => 0x3ffc0ffc1f83f87fe0ff83fc3fc0f07ecf3793
  | 1 => 0xc0fff07ffffc1f83ff07fc1fc3ffff8171c9fc
  | 2 => 0xffffff801ffffffc0007fffffc00ffff81fe1f
  | 3 => 0xffffffe0001ffffff8001fffff0001fe0fe0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8644631125250814e849a12c0646912c471391
  | 1 => 0x9248a121082129012942a5044292a5045140b4
  | 2 => 0x891040a524212a810844a52a8084a5180ac0a
  | 3 => 0x2ca2484a034a54ce5290421b312c0219aa0f40
  | 5 => 0x30c38e739c739f739ce7738222308c61fdf000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeee0eee0ece0ece0eee0eee0ece0ece0eee0eee0ece0ece0eee0eee0ece0ece0eee0eee0ece0ece0eee0eee0ece0ece0eee0eee0ece0ece0eee0eee0ece0ece0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_16795
namespace PEqualNP.Outside.L_meta_16795
open PEqualNP.Outside.L_meta_16795.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40dfa1681bd42d02fca3a05f54740beaa4817e53902faa7206f90e40de21c817e52902faa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a817c53502fea4a05f14940dfa1281bd42502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881bf411037a82205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef18e61dc31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c3eca3185d94630bea8c61f5518c2eaa3185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c3be6498774c930bfa8a617c514c3bc6298770c530fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42482fea2905f14520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa88417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10ef29c215e53842faa7087754e10aea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fda0421f840843f461087e4c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443ee62887d0c510fb10a21f521443f680887e10110fd18221f930443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7c87a16f10f42bf28e857d51d0afca1a15f54342beaa4857e5390bbca7215794e42bea9c85dd5390abaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332efa1e65dc43ccafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997710d32f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120fe94241bd284837d50907f2a120de54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f719643ed32c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f719243ed32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410df94421fb98843f431087de4210fd88421f690
  | 2 => 0x1ed198004da7c41b8380000001408c4a25307e9330009993421015621c3508a28a784c588f22a4613180030052927a0526071c9e04a1942e12fa550006d0fca213dc494151433d27652b9103224908010e24694caf1962b2780d80e32e42f5208ed2521d4c60000000005a0b02f836c000774906b4b70d82767000017503e83c430000c2624078522de1f9120012065a024a732686a4b803e46c208340bb2da11d231c106a5d0550002164bc631543209ac8685416e4d8fe00033a511378004700003594b00056c96a294122a07102027c9400025b364000000001862489ea6c2ca0ad3b0002c2138001aa00028d23a01000000f3a223bc1146d2171fe78d1a9ec4404e44980c00000004000042000b49a017e9844e244000730e48044ea00000042000088118001be0001e02d22c408a09ac000518d72080005000007324c0000000000000026a5c1ba0e800000098310970f511a6710c1a74b22453295a1c060d200883783b04589f47e8dc310002280010a08419c024a723c270298b122c4389743c0b31c86e02f9281345c42d87d0cc7442b94231c5d8472251b89b82b1a32cc10cee1d0212050321811a2754de8c81e20000a9cd4223e12d17a33e000aea314a86a04a11931e3d8000004a46d4fd15f08c855171eb2f02d52103d24e8345905a242654ff9732d461cc111c2a40bc4081c1ac164038d930c54c678f02223541721d1f2684c422b1365544f0fb1e61e40313a3d48785624d2926490b2674c05fcca1ed01a348e90e81781bc709773b076cb010f3363241f880184570b19e41ee51c5781e38a560fba4b4047cca69ab3082b8380511f86f8ef8893e839c0ba4c27e475392030f82f81a04112a4c42a99820c6bc2221f434768259a50ec90ccf1b6006430ee85c02c6145b16b2fa178962193e088c3291e2f67088d197120698d890748a03c0500c570dc25004020800e1e8020bc1900c020d00003800000000000405c0003c0a0000500000000192a006020000040200405024000542c0001e00009000000080b08840104010140001c00044030000d01c07000120000c008020000100c050402a0001101c07008230001d0000000001008220380c0400004c0002805008060040c00000058000c070008060000000404000000100308438000010000a00800000070000000803000000880200400000460340300c850140000c09024010100900c260201a0140d18c0500011004030000f01001074a500026000920000c024030000001c06024020080704007004000200201803000030000b034050240d0b00101001bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877
  | 3 => 0xd98003940c48d8f41de9dc6a09d00a075130a225470c7d097426041249bf40c3b81b1c409e06c000000008e4cc80006020c9b86c0b00000023b00000103871372100699d43c4334000002261408906d1bc9a4f4234396838fb00000082c098b10007f45682700062801000000000000004e88c00000019814c639483cc3940024a0000005225604c6ec910d014e1a4a78744bc060bf2124c4284001ba3e4404bc8002ce001350000242606288501c32c0018d0000b0000000000000000020a000aba2a3ae000000002640007f0000004d40016c39c410000002a00012c0ba00042805896000831271fb1520c91e8670228bc3d00a45a9c4fc1e52c8000128f2076304f780047464d320630003ac3f99a000295051c800006519000348264e300017247c0023e0ba3a839039000000001a23a6000000000000008b8003ac81000000034000000480004ad0da702407f8000002a2000148004007d48415636e3a5140e6140300120600661b9139cf1ae
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x831cc27661d52309d587548c26e62152309b588548c27661152309d584548c23e64946308f592518c3366494630cd592518c3726094630d5947308c23e64951308f994544c31d6315130c7152434c25c6550d30c7153324c31c544c930d3149324c2d4614c930c7152314c29d640c530c7150314c2cd620c530b6980314c2d6618c1309798c540c26e62150309b588540c27661150309d584540c25f654c0309ed95300c25e63d53209758f54c823e64d4f208f59353c82776154f209d18553c82e86050b2097d8d51c825c6354720ea50b40c82e96210320ea90840c825e63152209758c548827661152209d584548827661d4e209d587538823f6454e208f191538823e64946208f592518823e64951209ed81544823e6515120cb588544823e6494d208f592534823f6454d208f19153482776154d209d185534832c54909209b195424833854c81209798f540825d63d50209d987540827561d50208f596540833860550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209d98453082756114c20cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420ce553400837151d00209e59440083715110020cb553200837151880209bd95200832d54480209ed9520082b86448020dc545200833661953108f99353c423d64d4f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b108f99052c423d6414b109798c52c425d6314b10cd95141c42d46350710ad59031c42e5620c710b518d21c425e63d52109758f548425e63152109758c548426e62152109b588548435a6094e109798f528425d63d4a108f990528423d6414a109798c528425d6314a10b658c40842e96210210ae191308435a534c210ae191208435653c4210ae993108425f63551109718d544426f62551109b189544423f6454d108f191534426f6254d109b189534423f64549108f191524425f63549109718d524423e64149108f590524425e63149109758c52442f260905109d19541442d463505109d99731442b5640c510b958831442f2600c5109d19521442d463485109e99740442d96310110ba58840442f26110110ec50440442f2618c1109e19530442b8644c110f40c530442786548110ae19120442ba64c4110b598e104427a60d50109798c540425d63150109b988540426d62150109d984540427661d4c108f990530423d6414c109b988530426d6214c109e980530423e64148108f590520425e63148109758c520427661148109e980520423e64944108f592510425e63940109758e500427965840109dd95100427b6544010
  | 1 => 0xca3d64145329e980514ca796014532cd990514cb356414532d5d0c514cb544314532d58c8514cb726014532dc580514ca5e63d50329d984540ca7561150329e980540ca7960150328f992520ca3d649483297d95320cad4614c8329bd95320ca3f64540328f191500ca5e6394b419758e52d06b86050b419798e509065d6394241d698e50907596394241ced06509071c53d0d41c714f425071c5350941cb14942506b86050941ae982415063f65504419dd95411063e6494b318f59252cc6d4614cb318fd9150cc63c64543319e983548c67960d5231a7992328c66e62951319b58a544c65f635513197997324c6d4614c9319b98b540c66d62d50319e983540c67960d50318f596540c71c63550318f990540c66e62150319b588540c67a60150319e580540c71d54d0c3197594430c6d56110c31cb952520c72d5494831cb951520c72d5454831d3d0d520c74c4354831d9185520c65d658c831a7992320c74d528c831d3548320c74d52cc43197d95310c74d524c4319dd95310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c65e63d53219758f54c867b60553219e18154c863e64d4f218f59353c86e4614cb21f14cb31c86e5620c721f18c831c863f64543218f19150c867a60d52219e583548865f63552219718d548863e6414e218f590538867a6014e219e580538865e63942219758e508865e63951219758e544865f63551219718d544867b60551219e181544865e6394d219dd85534865e6514d21d3588534874c538c9219b195324875453c85219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c755153087546154c218f990530863d6414c219798c530866e6214c219e98053086796014c21d554f3108675650c421d354f210866f6548421d354d21086776548421b518d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50087733154021dc0c550087722154021dc485500865e6394b409758e52d02b86050b4097d8d51d025c6354740a798e429029c63506408f99742502b86050940c754e43102b96010c40d394e521034d5394840d394d521034d5354840cb90d521032c4354840da181521023d6590840a798e421032d5290840cb54842103565394440d554e51103665294440d954a51103726094440d594d51103555354440d994951103655254440c754f411032d52d0440a718d411031d5350440cb54941103365150440cb54b401023f6550040cb549401027b65500409b98b54cc26d62d53308f99252cc23d6494b30b518532cc29d640c730b358
  | 2 => 0x194001aa538000032c00220e0b68000000000010800001ba9d31aa0b720a000000009e800000fc97a98b69fc000000021c4a8006ba54c2a2e0027e3609a9220ae397a679cc2401812096cf18e9800078b5e3f910cc2e283b7034000000000019c4c000b51be77208dd2c817a4eb38000f89475b78e880000000001ee1e800000000000074332b81c2c49c4d4960002ca7ab6c00000929728506027020001880431ce2b9ce512ce9a96b996ad0000000001011400000d1b0800000003001fadcd5b1055000001f2000ac9b2b25a2b073a8800000001241f222000004dae4001e401000d600000174d403c00000a1000ce00037aa0900b609800002a40000000264de9a2a88000000000000000c47e800c8b96478007527c000000000000000000008e00600000d10e8142065e0000005854250559c0698008c080bbac40029035b4a8f80087800b080000158000000000030000000005f25600000b0102000a2388d2681b002b04001b2ce9f0e02be00000002340000000000000000000000142a30980000c39a443b04a000000000e002280037600000002d81c32661b2ed38c80cb02001440b000000f6000000019200000000000000000000000000035a000c646b900000086266cda2c0e86e0025cc504400000170000008e000a800000000005b2bc8a8a600000b30000023200000cf800001b607210c1998748003739a00000488000035c00212000000015c003a80000000000000722234c001387e09e00000c600020ab61d3a40011c088005180000236000000000000000961000018a9d8007d85200000133a0810fa80b1e002700000000200003aa0000000002db800000000d3549c8007a000e18001a15a719340017000c0801002000000000000400000000300200000000040080000416004000040200401010000000201c030000e0100000000004040540700809008000100001c000080700005004000000500c04004030000100002000020000100416004000040100402000000000801801028100040000401004000000300c030000302002008020000f00c00014000040100800018020040301c020080300817038000000000000018000000101800000020000002000000000000200400000000240000409008000067a60947439e58251d0e7661942439d5865090e3f6550c4397d954310e7a60947429e58251d0b1e53d0a42ab98a4350a9e63909429798c5050a5d63141429d9845050a756114142d698c5050b596314142ce90c5050b384314142ce9085050b726114142dc5845050a3f6550842ae1814210a6f655084297d8d5110a5c63544429e98354cca7960d53329d98650cca756194332c7953328ca7661951329d586544ca7761551329d185544ca7b60551329e181544ca5e65d0d32b398b434ca9e648c9328f990514
  | 3 => 0x933848330cd8224000b4a78006139e0028e7f980bf05a0014aba2aa86b6ac90b2640002e940000006a16ebe01e599bc368000008a000f091bae6e2fa000000017e00000002f6000002e0000000048000df000000002f04ea1976001080000000000cd000ca80059000002a60012641b0e001e0001f4000000013ce2000000004100076b620001a85a9200348b59c8ec2de2a8000a9e657b66531ca000000000000000a5000439a4000000000000000230121992e001b4000764f80000162000009e3163e2a800000000ea6b000000b0668861b038bf800001120026e002b80023cae8e03c800bb000000cc3bad20023a002b46300096800bd05418800bcaac0000002000d0800000f4000000000000000460002128a7780024800a713a1926200014003ac002681a8160029a00226002ae458000c00000280430002f800e30e4003204280000132b4046158a030b92001d800182b180000000d903600000292ea1e0ae548ce000ca908000b8000000094b284a02452000df8007b000350000000000000000000000000000000000026a002f0e619600
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xb54e05770530f00a0080c05192404c000401160735609b49a1900648c50029a79b4a9ca4314142a34e7210a0a1651635845050aa33968628a65459d23214532c62c8b00a299618531814250714290c0a1283515c44354831ac2e030aa418e0e6454a320c662bb46418e43541cd2154021a52e021aa42056171181521030731aa5210818318d5250440c28a830a649864452185324c20ebb0a818a6183151620c530952ed21081906306454520082c839a8220221a458d4110110d42c4a088088591740c530443483206298221705c8314c110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x8100000c8073589411011089187190314c110c80645c8314c110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 5 => packedAt s5K5 (19164+((h/210+packedAt s5K5 (17064+(h % 210)*10) 10) % 759)*11) 11
  | 4 => packedAt s5K4 (19544+((h/157+packedAt s5K4 (17974+(h % 157)*10) 10) % 829)*10) 10
  | 3 => packedAt s5K3 (1475+((h/9+packedAt s5K3 (1421+(h % 9)*6) 6) % 35)*6) 6
  | 2 => packedAt s5K2 (184+((h/1+packedAt s5K2 (180+(h % 1)*4) 4) % 11)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1ffff03fc7c70f1e3f1fffc7e0707c19f793
  | 1 => 0x1fe078ffc3fff8f01fc7e381f8ffff8066c9fc
  | 2 => 0x1fff80fffc07ffffe007fc01ff007fff870e1f
  | 3 => 0xe00000fffff800fffff80001ffff8003f80fe0
  | 4 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x42431011880888010609048cc1231118085391
  | 1 => 0x44490122890201200a4321144849250822c0b4
  | 2 => 0x88842244109500562004482112044a61850c0a
  | 3 => 0x819654892281929b54900049a4960232d80f40
  | 4 => 0x1118600e332624ec9926927000180c4377a000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_16795
namespace PEqualNP.Outside.L_meta_16795
open PEqualNP.Outside.L_meta_16795.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12d50f0b1a6a317110001c00007803660014b11284020000400f10a9ca63e19d2f6e41a2c3629115481d5bb062ccb20815e80289400000491b30060e0d2638b9d4e38146800038000000d080042c1802a04000027fd5009fe54027f55009fc54027fd4c09fe53027f54c09fc53007fd0c01fe43007f50c01fc43027fd48097f5201ff94809fd52005f54807fc52007fd0807fe42007f50807fc42007fcc807fe32007f4c807fc32027fd4405fe51027f54405fc51007fd0405fe41007f50405fc41007fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21027fd4003fe50027f54003fc50007fd0003fe40007f50003fc40007fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826001fe8413000ff82098023ff65480117fb2a4008ff99520025fcca90023fd65480117eb2a4008ff19520025f8ca90003ff64480017fb224000ff99120005fcc890003fd64480017eb224000ff19120005f8c890023ff5448011ff2a24008ff55120047f8a890003ff63480017fb1a4000ff98d20005fcc690003fd63480017eb1a4000ff18d20005f8c690023ff5348011ff29a4008ff54d20047f8a690003ff4348001ff21a4000ff50d20007f88690006ff6248007ffa924003dfd492001ffca49000ffd5248007bea924003ff1492001ffe849000ffe4248007f72124003ff50920007da849000ffc4248007ff9924003ff8c92001ffa649000ffc3248001ffb0a4000bfd852003ffcc29000afe6148001feb0a4007ff18520015f8c290023ff514800fff28a4008ff5452003ff8a290003ff414800fff20a4000ff5052003ff88290003ff314800fff18a4000ff4c52003ff8629000fff2148007ff10a4003ff4852001ff84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001ff9012000ffa8090007fc4048003ff9824001ff8c12000ffa6090007fc3048003ff9024003fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007ff1048003ff0824001fe8412000ff82090017ff654400b7fb2a2000dfd9510004feca88017fe65440097f32a2005ff5951002dfaca88017fc65440097e32a2005df19510024f8ca88003ff64440017fb222000ff99110005fcc888003fd64440017eb222000ff19110005f8c888017ff544400bff2a22005ff5511002ff8a888003ff63440017fb1a2000ff98d10005fcc688003fd63440017eb1a2000ff18d10005f8c688017ff534400bff29a2005ff54d1002ff8a688003ff4344001ff21a2000ff50d10007f88688003ff62440017fb122006ff9891001dfcc488003fd62440017eb122006ff1891001df8c488017ff524400bbfa922006ff9491002ffaa4880037d524400dfe2922000ffd0910037fc8488003fd424400dfe2122000ffcc910037fc6488003fd324400dfe1922001bfd8510017fea28800bfe5144005fb28a2002ff5451002feaa28800bfc5144005ffa0a2002ff90510017ec828800bfd4144001faa0a2002ff10510017fe6288003f73144005ff18a2002ff4c510017f8628800bf43144005ff90a2002ff88510017ec428800bfd2144001fa90a2002ff0851000dfec088007ff5044003ff2822001fe9411000ffaa088017f95044003fe2822001ffd0110007f68088007fe4044003fea022001ff1011000ff08088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fe2150001fe90a8010ff0854000dfec0a0007ff5050003ff2828001ff5414000ff8a0a0007ff4050001fda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffc60a0007fc3050003ff9028001ff8814000ff840a0007ff1050003ff0828001ff04140077fecb9803eff65cc01fff32e6004bf9973007efccb980127e65cc01ffeb2e600fbf59730006facb980027d65cc01dfe32e6004bf19730077fec998002ff64cc001ff3266000bf99330007fac998002fd64cc01dfe3266000bf1933007ffea99803ffe54cc01ffeaa6600fff1533000dfcc79803fff53cc01dff29e600fff54f30077f8a798003ff43cc01dff21e6000f790f30007fa8798003dd43cc01dfe21e600effd8b3006ffcc59800efe62cc001feb166000bf58b30077f8c59800efc62cc01fffa96600fdfd4b3006ffca59803ffd52cc001bea96600dff14b30007fe8598037fe42cc001fea16600dff10b30077fe6598003df32cc01bff1966000ff4cb30007ba659803bfc32cc01dffb0e600cff98730015fcc398003fd61cc0017eb0e600eff18730015f8c39803fff51cc019ff28e600fff54730067f8a398003ff41cc019ff20e6000ff50730067f8839803bff31cc019ff18e6000ff4c730077f86398037ff21cc019ff10e6000ff48730067f84398006fd60cc003ffa866001ff9433000ffaa198007fc50cc003ffa066001ff9033000ffa8198007fc40cc003ff1866001f78c33000ff46198007fc30cc003ee1866001ffc833000ffc4198007fc20cc003ff8866001ff8433000ff8219802fff654c0177fb2a600bff99530025fcca9802ffd654c0177eb2a600bff19530025f8ca98003ff644c0017fb226000ff99130005fcc898003fd644c0017eb226000ff19130005f8c89802fff544c017ff2a2600bff5513005ff8a898006ff634c017ffa9a600bff94d3005ffaa69802ffc534c001ffa1a6000ff90d30007bc8698003fd434c001eea1a6000ff10d30007fec498002ff624c015ff3126003bf98930007fac49802bfc624c0077e312600bffd493005efea49802bfe524c017fea926000df54930057f8a498003ff424c015ff2126000ff50930057f88498003ff324c001ef992600aff8c930007fa6498003dd324c015fe1926000ffd8530005fec298027fe614c0057f30a6000ff5853004ff8c29800afc614c017ffa8a6009ff9453005ffaa298027fc514c001ffa0a6009ff90530007fa8298027fc414c001ff98a6009ff8c530007fa6298027fc314c015ff90a6009ff88530007fa4298027fc214c0037fb026001ffd413000ffca098007fd504c003fe2826001ffd013000ffc8098007fd404c003fe2026001ffcc130007f66098007fe304c003ef1826001ff0c13000fb86098007f8304c003ff9026001ff8813000ff84098007ff104c003ff0
  | 2 => 0x2101ffaa49080f7d5248407fe2924203ffd092101ffc849080ffd4248407fe2124203ffcc92101ffc649080fee3248407fe9924200fb4c92101ff8649080aff6148405ffa8a4202ff94521017faa29080bfc5148405ffa0a4202ff90521017fa829080bfc4148405ff98a4202ff8c521017fa629080bfc3148405ff90a4203fdc8521017fc429080bee2148405fe10a4202fb08521017e84290803ff60484017fb024217ff9812100dfcc090803fd604842ffe3024201bf181210c7fea09085ffe5048431fea824217ff141210bffc809085ffc404842fff1824217ff0c12101ffe409080ffe2048407fe1024202ffc4121017ee209080bfe1048405fe0824215ffd97400b5fecba005bfe65d00097f32e8016ff597400b5facba0057fc65d00097e32e8001bf993400b7fea9a0057fe54d002dfeaa68015ff153400affec7a0003fe63d00017f31e8000ff58f40005fac7a0057fc63d002dffa9e8016ff94f400b7faa7a005bfc53d002bffa1e8000ff90f40007fa87a0057fc43d002bffb168014ff98b4001dfcc5a0003fd62d00017eb168015ff18b4001df8c5a005bff52d002dbfa968014ff94b400b7faa5a00037d52d0029fe2968015ffd0b400077e85a0053fe42d0001fea168000ef50b400aff885a0003ff32d0029ff1968000ff4cb400a7f865a0057ff61d0027ff30e8002bf98740007fac3a0002fd61d002bfe30e8002bf187400b7fea3a004ffe51d002dfea8e8013ff147400affe83a004ffe41d0001fea0e8015ff10740007fe63a004ffe31d0001fe98e8013ff0c7400a7fe43a004ffe21d0001fe90e8013ff0874000dfac1a0007ff50d0003ff2868001ff5434000ff8a1a0007fe40d0003df2068001fe9034000ff881a0007bc40d0003ff1868001ff0c34000ffe41a0007fe20d0003fe1068001ffc434000ffc21a0007fa10d0003fe0868012ffd9540095fecaa00037f65500013fb2a8012ff99540025fccaa004bfd65500257eb2a8012ff19540025f8caa004b7c65500093e32a8001bfd9140097fea8a004bfe5450025feaa28012ff15140007fec6a0002ff6350001ff31a8000ff58d40007f8c6a0002fc6350025ffa9a8012ff94d40097faa6a004bfc5350001ffa1a8000ff90d40007fa86a0003fc4350001ffb128000bfd894008ffcc4a000efe6250001feb128011ff1894001df8c4a004bff5250025bfa928011ff94940097faa4a00037d5250023fe2928000ffd09400077e84a0047fe4250001fea128000ef5094008ff884a0003ff3250023ff1928000ff4c94008ff864a0003ff61500017fb0a8010ff98540015fcc2a0003fd6150021fe30a8002bf18540097fea2a0043fe5150025fea8a8010ff14540007fe82a0043fe4150001fea0a8010ff10540007fe62a0043fe3150001fe98a8010ff0c54008ffe42a004
  | 3 => 0xeb2e620eff19731025f8cb9883bff64cc4017fb266200ff99331005fcc998803fd64cc4017eb26620eff19331005f8c99887bff54cc43dff2a6621eff553310f7f8a99880afe63cc43dffa9e620eff94f310f7faa79883bfc53cc401ffa1e620eff90f31007fa879883bfc43cc41dffb16621dff98b3101dfcc598803fd62cc4017eb16620eff18b3101df8c59887bff52cc43dbfa96621dff94b310f7faa5988037d52cc43bfe2966200ffd0b310effc8598803fd42cc43bfe216620effccb31007be6598877fe32cc401fe9966200f74cb31077f8659880afd61cc405ffa8e6202ff94731017faa39880bfc51cc405ffa0e6202ff90731017fa839880bfc41cc405ff18e6202f78c731017ec639880bfc31cc405ee18e6202ffc8731017fc439880bfc21cc41dffb06621cff9833100dfcc198803fd60cc4017eb06620eff1833100df8c19887bff50cc439ff286621eff543310e7f8a198873fe40cc439fe206621cff8c331077f86198877ff20cc439ff106621cff08331017fe219880bf710cc405ff0866202ff043310dffeca9886eff654c401bfb2a62009fd95310dffcca98812fe654c437feb2a621bbf595310dff8ca98812fc654c437be32a62049f19531007fec898802ff644c401ff3226200bf99131007fac898802fd644c401fe3226200bf191310dffea89886ffe544c437feaa2621bff15131015fec69886fff534c437ff29a621bff54d310dff8a698803ff434c401ff21a6200ff50d31007f88698803ff624c4017fb12621aff9893101dfcc498803fd624c435fe3126203bf189310dffea49886f7f524c435ff292621bff54931006faa49886bfc524c401ffa12621aff90931007fa849886bfc424c401ff9926200f7cc9310d7fc6498803fd324c401ee992621aff0c931015fec29880bff514c405ff28a6202ff54531017f8a29880bff414c405ff20a6202ff50531017f8829880bff314c401fb98a6202ff8c531017bc629880bfc314c405ee18a6202fd0c531017fe429880bfe214c405fe10a6200ffd8131005fec098867fe604c4037f3026200ff581310cff8c098806fc604c437ffa826219ff941310dffaa098867fc504c433ff2026219ff101310cffc6098867fc304c435ff9026219ff881310cff8409880bff104c405ff0826202ff041310c7feca90862ff6548431ff32a4204bf995210c7faca90862fd6548431fe32a4204bf19521007fec890802ff6448401ff3224200bf99121007fac890802fd6448401fe3224200bf191210c7fea890863fe5448431feaa24218ff15121007fec690802ff6348401ff31a4200bf98d21007fac690802fd6348401fe31a4200bf18d210c7fea690863fe5348431fea9a4218ff14d21007fe8690803fe4348401fea1a4200ff10d21015fec49080fff5248407bfa924203ff949
  | 4 => 0x9fff514c84dff28a6427ff54532137f8a29909bfe414c84dfe20a6426ff8c532137f8629900fff214c807f790a6403ff8853201ff84299003ff604c8017fb026425ff9813200dfcc099003fd604c84bfe3026401bf1813213ffea099097fe504c84ffea826425ff1413212ffc8099097fc404c84bff1826425ff0c13201ffe409900ffe204c807fe1026426ffc413212ffc2099097fc104c82bffb2e8224bfd9741127fccba0812fe65d0449bf32e82049f99741127facba0892fd65d0401beb2e82009f597410aff8cba0812fc65d04057f3268224ffd53410affca9a0893fd54d042bfe2a68215ffd8f41007fcc7a0802fe63d0401feb1e8200bf58f410aff8c7a0893ff53d0449ff29e8224ff54f41127f8a7a0857ff43d0401dfa1e8200ff90f41007fa87a0803bd43d042bfe21e8215ffd8b4111ffcc5a080efe62d0401feb168200bf58b410aff8c5a080efc62d0449ffa968224dfd4b4111ffca5a0893fd52d0401bea968223ff14b410affe85a0803bf42d0447ff2168200ff50b410077a85a0857fc42d0401ff9968223ff8cb41007fa65a088ffc32d04057eb0e8202ffd4741017fca3a080bfd51d0405fe28e8202ff907410177c83a080bf641d0405fe20e8202ef10741017fc63a080bfc31d0405ff90e8202ff88741017f843a0857ff60d0445ff3068201bf98341007fac1a0802fd60d042bfe3068201bf18341127fea1a088bfe50d0449fea868222ff14341117fc81a0857fc40d0445ff1868222ff0c34111ffe41a088bfe20d0445fe1068202ffc4341017fc21a080bfc10d0443ffb2a8221bfd954110ffccaa0812fe6550443feb2a8221bf5954110ff8caa0812fc65504057fb228221ffd514110ffca8a0887fd5450443fe2a28200ffd8d41005fec6a0803fe6350401feb1a8200ff18d41005f8c6a0887ff5350443ff29a8221ff54d4110ff8a6a0803ff4350401dfa1a8200ff90d41007fa86a0803bd4350401fe21a8200ffd8941005fec4a0883fe62504077f3128200ff58941107f8c4a080efc6250443ffa928221dfd4941107fca4a0887fd5250401bea928220ff14941007fe84a0803bf4250441ff2128200ff509410077a84a0883fc4250401ff9928220ff8c941007fa64a0883fc32504057fb0a8202ffd4541017fca2a080bfd5150405fe28a8202ffd0541007ee82a080bfe4150405df20a8202ff105410177882a080bf44150405ff18a8202ff0c541017fe42a080bfe2150405fe10a8200ffd8141005fec0a087ffe60504037f3028200ff581410fff8c0a0806fc6050443ffa82821fff9414110ffaa0a087ffc505043fff202821fff101410fffc60a087ffc3050441ff902821fff881410fff840a080bff1050405fb8828202ff84141017f820a083bff65cc43d7fb2e621eff99731025fccb9887bfd65cc43d7
  | 5 => 0x954216ff8caa1012fc65508077fb22842dffd514216ffca8a10b7fd545085bfe2a28400ffd8d42005fec6a1003fe6350801feb1a8400ff18d42005f8c6a10b7ff535085bff29a842dff54d4216ff8a6a1003ff4350801ff21a8400ef90d42007fa86a1003fc4350801de21a8403bfd894201ffea4a100f7f5250807ff2928403ff5494201efaa4a100ffc5250807ffa128400fbd094201ffc84a100fbe4250807fe2128403ef1094201fd884a100ffe3250807fe1928400ffd8542005fec2a10b3fe61508057f30a8400ff58542167f8c2a100afc615085bffa8a842cff9454216ffaa2a10b3fc5150859ff20a842cff10542167fc62a10b3fc3150807ff90a8403ff8854201ff842a1003ff60508017fb02842bff9814200dfcc0a1003fd6050857fe3028401bf1814216ffea0a10affe505085bfea82842bff1414215ffc80a10affc4050857ff182842bff0c14201ffe40a100fef2050807ff1028403ff08142167fe20a10affe1050857fe082840effd9732155fecb990abfe65cc8097f32e642aff59732155facb9903bfc65cc8097e32e640effd9332005fec999003fe64cc8017f3266400ff59332005fac99903bfc64cc8017e326642affd5332157fca9990abfd54cc855fe2a66403bf98f32157fea79903bfe53cc855fea9e640eff14f32007fe8799003df43cc81dff21e6400ff50f32077f88799003dc43cc8077eb166403ffd4b3201efea59900ffe52cc807fea966403df54b3201ff8a59900fff42cc807ff2166403ff50b3201ff8859900ffe32cc807ef1966403fb8cb3201ff8659900fdc32cc81dffb0e6429ff98732015fcc399003fd61cc8017eb0e640eff18732015f8c3990abff51cc853ff28e642aff5473214ff8a3990a7fe41cc853fe20e6429ff8c732077f8639900fff21cc807ff10e6403ff08732077fec1990a3fe60cc8037f3066400ff58332005fac19903bfc60cc8037e306642affd4332147fca1990abfd50cc851fe2866428ff90332147f881990a3fe30cc81dfe1866403ffc833201ffc419900ffc20cc853ff8866428ff84332147f8219909fff654c84f7fb2a6427ff99532025fcca9909ffd654c84f7eb2a6427ff19532025f8ca99003ff644c8017fb226400ff99132005fcc899003fd644c8017eb226400ff19132005f8c89909fff544c84fff2a26427ff5513213ff8a89900eff634c84fffa9a6427ff94d3213ffaa69909ffc534c801ffa1a6400f7d0d32007fc8699003fd434c801fe21a6400f710d3201dfec49900fff524c807bfa926403ff9493201ffaa49900f7d524c807fe2926403ffd093201ffc849900ffd424c807fe2126403ffcc932007de649900ffe324c807ef1926403ff0c93201fb8649900fec324c801ffb0a6400bfd8532137fcc29900afe614c801feb0a6426ff18532015f8c299
  | 6 => 0x7ff9028639ff881431cff840a18ebff1050c73ff0828639ff04143077feca218daff6510c6dff3288604bf994431b6fcca218127e6510c6dfeb288636bf59443006faca218027d6510c1dfe3288604bf194431c5fcc8218dbff5410c2bff2a08636ff550430aff8a8218defe6310c6dffa98860eff94c431b7faa62183bfc5310c2bffa188600efd0c43077fc8621803de4310c01fea188600ef50c43007ba862183bff6210c6bff3108603bf98843007fac421802fd6210c1dfe3108603bf188431b7fea4218db7f5210c6bff2908636ff548431aff8a4218d7fe4210c2bfe2108635ff8c843077f8642183bff6110c69ff3088602bf98443007fac221802fd6110c1dfe3088602bf184431b7fea2218d3fe5110c6dfea888634ff144431a7fc8221857fc4110c69ff188860eff0c4431affe42218d3fe2110c69fe108860effd804319ffcc021806fe6010c01feb008600bf58043077f8c021806fc6010c6dffa808633ff940431b7faa0218cffc5010c67ff2008615ff1004319ffc602183bfc3010c6bff9008633ff8804319ff840218d3ff1010c67ff0808633ff04043006fec8a90037e6454801beb22a400df19152006fec6a90037e6354801beb1aa400df18d52006fe86a90037e4354801bea1aa400df10d5201efec4a900e7f6254809b7b12a403df9095201ef884a900f7e3254807be192a400dfd8552196fcc2a90037d6154865be30aa432df90552196f882a90cb7e3154865be18aa403dfc855201efc42a900f7c2154801bfb02a431df98152006fac0a90c77c6054863bf202a431df1015218efc60a90c77c3054807bf902a403df8815201ef840a90cb7f1054863bf082a431df041520affecba10c2ff65d0861ff32e8404bf99742187facba10c2fd65d082bfe32e8404bf1974201dfcc9a10c3ff54d082bff2a68430ff553420aff8a9a1057ff63d0801ff31e8400bf98f42007fac7a1002fd63d082bfe31e8430ffd4f42187fca7a10c3fd53d0861fe29e8415ffd0f42007fc87a1003be43d0801fea1e8415ff10f420077887a100efd62d0807ffa968403dfd4b4201ffca5a100ffd52d0807bea968403ff14b4201ffc85a100fbe42d0807f72168403ff10b4201f7885a100ffe32d0807fe1968415ffd874217ffcc3a100afe61d0801feb0e8400bf587420aff8c3a100afc61d0861ffa8e842fff94742187faa3a10bffc51d085fff20e8415ff1074217ffc63a10bffc31d0807ff90e8403ff8874201ff843a1057ff60d085dff3068401bf98342007fac1a1002fd60d082bfe3068401bf18342187fea1a10bbfe50d0861fea86842eff14342177fc81a1057fc40d085dff186842eff0c34201ffe41a100ffe20d0807fe106842fffc4342177fc21a10bbfc10d085bffb2a842dbfd954216ffccaa1012fe655085bfeb2a842dbf5
  | 7 => 0x80000000002bffb2e8638bfd97431c7fccba1812fe65d0c71feb2e8638bf597430aff8cba1812fc65d0c71ffaa68615ff953431c7faa9a1857fc54d0c71ffa9e8638ff94f431c7faa7a18e3fc53d0c2bffb168642ff98b4301dfcc5a1803fd62d0c017eb168615ff18b4301df8c5a18e3ff52d0c71bfa968642ff94b431c7faa5a190bfc52d0c85ff2168615ff10b43217fc65a190bfc32d0c2bffb0e8641ff98743015fcc3a1803fd61d0c017eb0e8615ff18743015f8c3a18e3ff51d0c83ff28e8638ff5474320ff8a3a1907fe41d0c2bfe20e8641ff8c74320ff863a190bff21d0c83ff10e8641ff087430affec1a1903fe60d0c037f3068600ff58343005fac1a1857fc60d0c037e3068638ffd4343207fca1a18e3fd50d0c81fe2868640ff903430aff881a1903fe30d0c81fe1868642ffc8343207fc41a1903fc20d0c83ff8868640ff84343207f821a183bff6590c6f7fb2c8637ff99643025fccb218dffd6590c6f7eb2c860eff19643025f8cb218f2fd6490c6fffaa48637ff952431bffaa9218dffc5490c6d7f31c8637ffd4e43077fca7218dffd5390c1dfe29c8600ffd0e430077e8721803df4390c1dffb14863fff98a4301dfcc521803fd6290c017eb14860eff18a4301df8c5218dfff5290c6fbfa94863fff94a431bffaa5218fffc5290c7fff214863fff10a431fffc652183bfc3290c1dffb0c863eff98643015fcc321803fd6190c017eb0c860eff18643015f8c3218dfff5190c7dff28c8637ff546431f7f8a3218fbfe4190c7dfe20c863eff8c643077f863218ffff2190c7dff10c863eff08643077fec1218f7fe6090c037f3048600ff58243005fac12183bfc6090c037e3048637ffd42431effca1218dffd5090c7bfe284863dff902431eff881218f7fe3090c1dfe184863fffc82431effc41218f7fc2090c7dff884863dff842431eff821218f3ff6550c797fb2a8600dfd9543004fecaa18f3fe6550c097f32a863cff595431e5facaa18f3fc6550c097e32a863cdf19543024f8caa18f3ff5450c79ff2a2863cff551431e7f8a8a18f3ff5350c79ff29a863cff54d431e7f8a6a1803ff4350c01efa1a8600ff90d430077c86a1803ff6250c017fb12863bff9894301dfcc4a1803fd6250c77fe3128603bf189431e7fea4a18f37f5250c77ff292863cff549431dff8a4a18effe4250c77fe212863bff8c9431dff864a1803ff6150c017fb0a863aff98543015fcc2a1803fd6150c75fe30a8602bf185431e7fea2a18ebfe5150c79fea8a863aff145431d7fc82a18ebfc4150c75ff18a863aff0c5431dffe42a18ebfe2150c75fe10a8600ffd8143005fec0a18e7fe6050c037f3028600ff581431cff8c0a1806fc6050c79ffa828639ff941431e7faa0a18e7fc5050c73ff2028639ff101431cffc60a18e7fc3050c7
  | 8 => 0x2af3610000330000002e40bd1c900000000000000024c00026f80029b8002bb1b20031722378a22968608578bf0000aa000088000339312b3faae2181739aa16e09700013835c80032c21e00000010c916905b1093a8a50258000f500027d0f000010785c8002a180000000021a8000001752911759bd800170b4f00032a845000000000237000318050800311ae8000006c00400405004400c05800001400400800000001000c01401001400400800000400405000000400401800800005c00802000002000400400000404000402801400401401401000801c00001000000400000404801c01c00000000400007000c00000400000000400000c00802400000000002402800000000400000400000800000400801000000400400000001403802403000003403c00000400001400002809401400000001400000400000400c13800001000001800003000c00000000400c00005404002002001c00000800c02001404801000400c02800400000802403000400000404000001402800000803404400400401000400403803400001000401c00800006000000000800000004400c00004c00000401400001c00c00002000c00802800002800400400000400c00c06c00000002400c00004803800001000400009800404000400400c00400003c01000800402400400000400800000001800000400000002003403800000000400c00c00c00401400000400800000c02800001000400400400400400400001000801800001400c00000000401409000000401400003001400c00000000000000000004001000403001800000000c00400000000000400400002c00400c00c00001000400c00400800800000401000400001000c00c00802400400800800800000001800401004000400403400000004401400c01000400800000400801800001000800000002c00402400c00004800000c00401401c00402000802c00000c00c00004000000401000806400c00000400002000000000803c00400401400000401c00800401001801c01c0000180040040a000401000001000400400401000800401805001802801000402400800000401803400000c00001800001400800000000400000400001800400803000002c00000800800000400000002000000005c05000800002000c00c02002401000c0080000000080200100140040040c400001004002400000001802c00006000c03000400001002801c00001800800400800400000403400000002c00401800000401800c00000001000400003801800c00c06000c00000800002801800400002000800001400000401c03000804401800001001801400000000803400803803c00000c00000001c04c01001400801c00000002c01009400c01c02400000000000402000403400400000c010000000000000
  | 9 => 0x90330e22813f00000028b9952c780011511a27e00011088ea9c27b22600009c951942b44a0f8000000000c327cb142dc00000026e80004e0ca28180009a229b2c8001530002270d18fe924a2f04a8841682e4a102dfb16afe2ac266800290914a8a80015d2b528716a1ed9d4a19839a618000000000191ef2a20542b085384c99f92921f8300751ad80009680000003c8000000000000002bd96101a8b1299ae000000000019a36698600002e3050000000001b08001daaf20720000de000000000113ab630095381eb4b0000002178000000aa8000000f68000002bca859be9b9a6a90095d908046a73b0d94903500000008a00000026600025f9579761f42f790d0000339e70000000000cb1d70089842752df2f420e8002119992cc8e185f8000003238001a280000020da4018a8000001f98002db820ab424c80000000000000017f8001bc000000000367b7399c82ca1d8680002f689f80003680000000000003f00000016999b8002641cf342945a0297c800000000102aff0440ff1ca832868aea16c00022f9ee00000000025a0000000000001e400f92e010a95af98ea8a18660000001cd07f3600fbaf52b89d197b2e900017f0ebb5e1d20a99f280009628410531b2c18620000a780000003c0000002420001be0668078000b780010c19035f19d9da04c2e7348b658f200010a2e2800238af1ae58000002cf372800000000289813a22a930878a81c48001193522740000b393235aa98992b02af090107102b05d00000012118a1818e790aac28b99ad0000000002fa00800000032180034a8001fa8f880019b07300000000035811c2110002bc0850001960000002290002700000000c283e25c8000000188000000898000000000a71a600000000000021500010980012404f00017c156037ad0ab18000001ff000196a218000000002243638a10000001f3abb8ac0000002d31d98000000e50001c297e94e1a80c1af3adc90480036a27f00000010e8000d3295048b6c80020a9ee9bb000340b0112380000000003a2de01f29280006a0c91b00002e19c680000000035600009783122480000000020200000025e8070c40f08001958000000001d3a192868000ce0001e18ef8f2978000000125b038b09922c514c8002af8000003191e916f0000000000000000fa07b08fab32c103b9131af9df0ad9dba1b000082a748000948000000bc8000002078000000ab0000000002540002fca1e9100f322380001c8002ed32b11f252341a8922080010d8000000340000001d003f800000291ac21b18cd8d68001f72a98c4878b3e0bb87e9500000478001a223025b2532e3031aa79462ec8458cc1471bc97a11e12602d0dba1f0000002160000002d424631a00033a23205489d19f0fc8370eea412dd17e1ab0002a8a0d33819c04622d92f00
  | 10 => 0x5335d9160c9b6a95131e30c8000272d78470018000002c5af300009b36e9798000000100000f59ff8001ce2538000600cead480db3312c2670c3b159633588000002e10000808e32ab03627580008e3071aa8000000000000000000f701e00000012534600021700020b0e012f8002a92f021a00ea4d8000998000000fd8ef3031e82be07a0838dda5baa39540690001338002a400000000000000002000000000003d0000000000003398001d40002b00002cc20e135333b4b8001e61fc2882cd8f60ee10b8001d516918d2e8a4902f1b11b5828ad3b298cca4f242a5dac325aa838670a6a8f06dae6a3b9db00c971aec1b780002522331db70a05984b4005682bb122ee29e8000001f6063803954b242cfae7881b35014298236b1d00026b8bd93b80036b800000000028347b4fb0bb45ab20bf8d48b90c59d10052da97732f1879571dd05b8dc8700cf00033d0ad1e7b188c83152808000169eb00011b00000016d8793411bd00d0000000d71f207700010fb6500002a2221639678000000002348002582e0b32ad600033eb07a7c0871748f780019781b00000000000000000000000000000e2c680014b1790778000000000fe0000001c605a2519340163198001f91a78003270002c81688230000000000000890128b19ed1bf0bb1580000002658000000000000001cb80000000000011d9f58000000fb0001550000d0aa72390991f0a3eaa312200000009202a8002708000220003528000000000002ba30b02dade8000000000000769fe9ababf8000002d980005d8001910b03378000000001f100001180018700006f8aca7b9f31e4b4a07bb34800371272800112b1f0ed0000349a995889120196d0001432630ae8d510f28c8a2ad6956ad90b63102768951dc91826f35b0b68b300033cb6f24e9558110d600600016718300000018e8000a020a35100034e118a5c111323268277042a7309380a0000be8001f0000af8948800326903ad893e0001a18000001b88002c7080000000044aac8001ec80000019e8002319713453472888a8abf0000001d813487d2a2800209b4c8002071202211520002eb80008c0570003689a48d790b07aa439a00001a522b0000e212c861314b6428ea6b0001cda8314aae98faa1497d1908000001c7259830a762b700032080004b20c09400000a88b3170a900025786c8000000000000000002720001fb9e21df9279778001b715f2e50001859972ae8000e9a13922a8d8001b331e82c08f3251f8ac900024d0000a60001e980000000000008d1dc000000204a338000000001f695298e36d18686b02100010933f0000000d58000000000000000068a400033580000029000031f8c0000059070800079800246ad1a2cb508ecada20c9741d0a03b4da8000000015f8ae009800000000317800000074a44
  | 11 => 0xe23300036829d0000000000db0002fda8d21c0002c48000000000002fd0830001142a58000000001942b59ea8588d12a080024b9a400016000032d80000018f041128a6d02184025d2eb3041a89419c0b5a2ca09a8000002593361892f292d0388740003310001988000000000000002a100020b9b91c200000b80000028b36496200000000000036b0ab87624ab5414f9bba62b0600001a0000002ed96a8001280000d820533180014d8001658c526e30e90e3558002f6000014af4b590003098002279e88000002470000a380000023c2b79268e6976b1c81d86980000000008898c88d9ccaa023f26216601d00007c84d81828f80035b8af1e5800144b0a06403a80229c8ea0000000e0ac88000e62309788000000002ff911800000000004a16b3099d2b682400000000013daea9808000002db115a6480037032d0559b2a690553200000f48810000ca80000012d80025480f30c00000000000000021c80022e80016500000005b2921d6a52ab923295b2009c7939b091018b88269c12baa2008aa601619aca189a08c798b8000420002aa000251180305800073a2d11ab5480012ba6a2612d5b6c34900000011b8000000000e3858130afbaa800000000003595e31c000000235ab4b3a80000026500025f2a680018c24400000000000000000000007f80018215ba878e400b13a0b51208dd338a6cab107c32200022b9333432409bab370002b99a7257203300172ab3a8c07193c8cb89f1b52f70e70001c50003130001ae17b8859179ce93688607e2ad96f800000004098b1b9e511702ea4815eb49a25b112fb34202486e96baf11482cbacaa8281723a80006d041ad800030f8000000d213724980035fa6d8000002f58001a39fb049a8636f9cb0001f78001d31e2982b0180017a9a314a1ba02900029d80028a07832280000031ab4d00000000005f0000a0ad29022978001fa062b661de8150d429f14f18b1361fda4e2129fe2589c186b800371b2e1042f92c40dc0002068392452ab8000001391eba140000da0001d604d27a00004fb7413fb2f9f1b55268a7fa2a81b988a9aa082679e314e89c132a7ea7d8e90b71628daa3800022a2c62a480000030d0c605200030680000023d8b40002cb36700000027aa131640758e4ae21919452beb62a3128501236192a3080ec23d3160c08000000000002710000002698002813020f8278ae3ac392307289e0cd28225e0650001508560000c20f400034c26c00000024886e00000003b0000000001440000d980000007d8000003340000000000000000001a5aad1b3819a778d3ab292e8000000de8bc29905129e1411ef98500113ea2e1ca14d0f38002ef256892a0f359b2498d88c8000000c10001070001e111e9af0000002d500000032a0002940178003469ea00000032e80594c3501880
  | 12 => 0x16080000002f83e80033224a14080004a06a949b048849c00002562fc34419337313005c239929a000001389c8166b518000000000278002a5063000121a1200030a8002bd0c713b201000194b3da970a58000001c897d8d00002288000002c0aee86c0500001c3a2c12b00029f85e0d924f800353a3e0130000000001318000000820382268002798000000fd04e8001d2a3535c29a3293302ddaf8236225000022852b571c41ae80032618380014b8ff8ba8a30f900280000004b9fd0492961f505a9e39d59f486f3578eb2efa6390611d1648cf9b4a0923a2609e68c8a3409e8dfa3b3723089c59b60000000b280015912700020600000000000028e00001c0f10000001de1b82782b805e8be33c059800023943b282d21c300000000015a02980000000034e80003d8000958001400001bf8869b6ad711f9a92552848000000003480001700000000000518000001469938000000000001dd9ec35680021b9479f81420af8000000b20eda938003438000902508000000002aa9813530003289310c693d21d000000159800108b210408480003698002c99120002e632580915a8d8800091aa612a9e016e8b4afa99833b06784318f937a5580000003223f80009b80c0000000001cf8b80e2a1080000000015c1ac1d89d900000036da71b60ac008b8df0fc1899cc0001198f980017333680016ca458000000659a1100090b748003139c9a08b27a3c8000e10a489dacd0619b40e80b581fa790e8800000369000000363215ad010696b35e8158ba24309829b0f1b6e0d29d7a4799ab0f35d1e0864843b621fc8260e580000000000033b8002501a695ca9491c8002ce8932d100000013c241935a4b00032b99980020419e2fe8002c
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x150505100fff040505100fff230505100fff2205051000df676cc5100e6f676cc51000cf676cc510265f775cc510265f575cc5100077765cc51025f7465cc510005f774cc510005f574cc510015f673cc510017d673cc510006f763cc510007d763cc510006f563cc510007d463cc510005f572cc51025f7752cc5100077552cc510007d732cc510007d532cc51000df670cc5100e7f270cc510007f170cc51000df470cc510016f760cc510017f360cc5100e7f250cc51025ff150cc5100e7f040cc5100e7f230cc5100e7f220cc51000df4764851001ef4764851000cf47648510255f77548510255f5754851000777654851024f746548510005f77448510005f57448510005f67348510005f47348510015f77248510017e77248510007e7624851001ef6624851001ef46248510037e46248510037775248510037755248510037e63248510007e53248510007f3704851000df6704851000df470485100bff07048510016f76048510017f360485100bff2504851024ff150485100bff040485100bff230485100bff22048510015fa76d011009efa76d0110014fa76d0110245fb75d0110245f975d01100077b65d011023f7865d011000dfa74d011000fba74d0110006fb64d0110007bb64d0110006f964d0110007b864d0110005f973d0110005f972d011023f7b52d01100077952d0110007bb42d0110007b942d0110015fa71d011009ff271d0110007f171d0110015f871d011000efb61d011000ff361d011009ff251d011023ff151d011009ff241d0110007f141d0110007f331d011009ff031d011009ff221d0110007f121d0110015f8764c11004ef8764c110014f8764c110235fb754c110235f9754c1100077b654c11022f78654c110005fa744c110005f8744c11000dfb734c11000fdb734c110007db634c110076fa634c110076f8634c110007d8634c110007da434c110007d9434c110005fb724c11022f7b524c11000779524c110007db324c110007d9324c110007f3714c110015fa714c110015f8714c11004ff0714c11000efb614c11000ff3614c11004ff2514c11022ff1514c11004ff2414c110007f1414c110007f3314c11004ff0314c11004ff2214c110007f1214c110015f8764811001ef87648110014f87648110225fb7548110225f975481100077b654811021f786548110005fa7448110005f87448110005fb7348110005f9734811000dfb724811000feb7248110007eb624811001efa624811001ef86248110037e862481100377b5248110037795248110037ea4248110007e94248110007f37148110015fa7148110015f8714811003ff0714811000efb614811000ff3614811003ff2514811021ff1514811003ff24148110007f14148110007f3314811003ff0314811003ff22148110037f12148110
  | 1 => 0x8910004fd73d89100bcfd72d89100367f52d8910036ec42d8910036ec32d891000cff71d8910014fe71d891000cfd71d8910014fc71d891029eef21d891029eed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d891028eef20d891028eed20d891001cff76589100057f755891002d7c75589100067f65589100067c6558910005bf7458910005bc7458910005df7358910005dc7358910036ec6258910285f77158910295fb7058910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf74589100acfc7458910006bc7458910004bc7458910004ff7358910006df7358910004df7358910074fc7358910006dc7358910004dc735891028cff7258910006ef72589100367f5258910284ff7158910006f771589100bcff7058910006fb70589100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c76549100067f64549100067e64549100067d64549100067c64549100067f63549100067e63549100067d63549100067c635491027d7f725491002f6f72549100367f625491001e7e62549100367d625491001e7c625491019776715491000775715491018e7f615491019776415491019774315491019776215491018f7a705491000779705491018e7f605491018f78405491018f7a305491018f7a20549101977b105491018f76105491018f74105491018f7810549100acff76d0910004fe76d0910004fd76d09100acfc76d09100067f65d09101867c65d09100aebe64d0910006bd64d0910006ef62d091001eec62d0910015f671d0910005f571d091000df870d0910004ff7650910004fe7650910004fd7650910004fc76509100067f655091016e7c6550910006be6450910006bd6450910015f67150910005fb705091000df87050910074ff76cc910004fe76cc910004fd76cc910074fc76cc9100067f65cc9101567c65cc910076de63cc910006dd63cc910006ef62cc91001eec62cc910015f471cc91000dfa70cc910005f970cc910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91013e7c654c910006de634c910006dd634c910005f7714c910015f4714c91000dfa704c91000df476505100fef4765051000cf47650510275f77550510275f5755051000777655051026f746550510015f77450510017b77450510007b764505100aef664505100aef46450510007b46450510005f47350510007b74350510007b54350510005f7725051026f775250510007755250510007b74250510007b54250510007f3705051000df6705051000df470505100fff07050510016f76050510017f360505100fff2505051026ff
  | 2 => 0x2b6f571d8d102bedf31d8d102bedd31d8d102bef431d8d10014ff70d8d10014fd70d8d102b6df30d8d102b6dd30d8d100ccfd7698d1002d7e7598d100057d7598d100067f6598d100067c6598d10006df6398d100cdf57198d1004df97098d10074ff7598d10024fe7598d100767e7598d100247e7598d10004fd7598d100767d7598d100047d7598d10074fc7598d100acfe7498d10004fd7498d10074fe7398d1001cfe7298d10004fd7298d1001cfc7298d100067f5298d100ccfd7198d10076f57198d100e4fd7098d10076f97098d10076fa3098d100057f7558d1002d7c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10005ef7258d10035ec7258d100e5f77158d10065fb7058d10004ff7558d100067f7558d100047f7558d10024fe7558d10004fd7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d100acfc7458d10006bc7458d10004bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1001cfe7258d1001cfc7258d10006ec7258d1001cec7258d100067f5258d100e4ff7158d10006f77158d1004ef43158d100ccff7058d10006fb7058d102b4fe7618d100067f6518d100067c6518d10006dd6318d10074ff7518d10024fe7518d10004fd7518d10074fc7518d100acfe7418d10004fd7418d10074fe7318d10076de7318d1001cfe7218d10004fd7218d1001cfc7218d100067f5218d10006de3218d10076dc3218d1000cff7118d10014fe7118d1000cfd7118d10014fc7118d10076df3118d102aedd3118d10014ff7018d1000cfe7018d10014fd7018d10076f97018d1000cfc7018d10076df3018d10076fa3018d102a6dd3018d100acff76d0d10004fe76d0d10004fd76d0d100acfc76d0d100067f65d0d101c67c65d0d10006df63d0d10006dc63d0d10015f671d0d10005f571d0d1000df870d0d10074ff7690d10004fe7690d10004fd7690d10074fc7690d100067f6590d101be7c6590d10006bf6490d10006bc6490d10015f47190d1000dfa7090d10005f97090d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d1002d7c7550d100067f6550d101e67c6550d10005f77150d10015f47150d10005fb7050d1000df87050d10074ff7610d10004fe7610d10004fd7610d10074fc7610d1002d7e7510d100057d7510d100067f6510d101b67c6510d10006bf6410d100aebc6410d10006df6310d10076dc6310d10015f67110d10005f57110d1000dfa7010d10005f97010d1001cfe76d891002d7c75d89100067f65d89100067c65d8910036ee62d8910004ff75d89100067f75d8910024fe75d8910004fd75d8910024fc75d89100067c75d89100247c75d89100acfe74d8910004fd74d8910074fe73d
  | 3 => 0xc71d95102ee7f41d95102ee7e41d95102ee7d41d95102ee7c41d95102ee7f31d95102ee7e31d95102ee7d31d95102ee7c31d95102ee7f21d95102ee7e21d95102ee7d21d95102ee7c21d95102e67f70d95102e67e70d95102e67d70d95102e67c70d95102e67f40d95102e67e40d95102e67d40d95102e67c40d95102e67f30d95102e67e30d95102e67d30d95102e67c30d95102e67f20d95102e67e20d95102e67d20d95102e67c20d95102e67f10d95102e67e10d95102e67d10d95102e67c10d95100067f65d91100067c65d9110004ff75d9110024fe75d9110004fd75d9110024fc75d9110074fe73d9110004fd73d911001cfe72d9110004fd72d911001cfc72d91100067f52d9110006be42d9110006bc42d911000cff71d911000cfd71d91102debf41d91102debd41d9110014ff70d9110014fd70d91102def970d91102d6bf40d91102d6bd40d91102d6f840d91100fcfd769911002d7e75991100057d75991100067f65991100067c6599110006bf64991100fdf57199110085f970991100acff7599110024fe75991100ae7e75991100247e7599110004fd75991100ae7d75991100047d75991100acfc75991100acfe7499110074fe7399110004fd739911001cfe7299110004fd729911001cfc72991100067f52991100fcfd71991100aef571991100aef64199110114fd70991100aef970991100057f755911002d7c75591100067f65591100067c6559110005df7359110005dc7359110005ef7259110035ec7259110115f7715911009dfb7059110004ff75591100067f75591100047f7559110024fe7559110004fd7559110024fc75591100067c75591100247c7559110006bf7459110004ff7359110006df7359110004df7359110074fc7359110006dc7359110004dc7359110004ff7259110006ef7259110004ef725911001cfe725911001cfc7259110006ec725911001cec72591100067f5259110114ff7159110006f771591100fcff7059110006fb70591100fef840591102d4fe76191100067f65191100067c6519110006bd64191100acff7519110024fe7519110004fd75191100acfc75191100acfe74191100aebe7419110074fe7319110004fd731911001cfe7219110004fd721911001cfc72191100067f5219110006be42191100aebc421911000cff7119110014fe711911000cfd71191100aef57119110014fc71191100aebf41191100aef641191102cebd4119110014ff701911000cfe7019110014fd701911000cfc70191100aebf40191102c6bd40191100067f65d8d100067c65d8d10004ff75d8d10024fe75d8d10004fd75d8d10024fc75d8d100acfe74d8d10004fd74d8d1001cfe72d8d10004fd72d8d1001cfc72d8d100067f52d8d10006de32d8d10006dc32d8d1000cff71d8d1000cfd71d8d10
  | 4 => 0x8d20014fe7158d20014fc7158d2012cff7058d20006fb7058d2012efa1058d2031cfe7618d20006dd6318d20074ff7518d20024fe7518d20004fd7518d20074fc7518d200acfe7418d20004fd7418d20074fe7318d20076de7318d2000cff7218d2001cfe7218d2000cfd7218d2001cfc7218d203167f5218d203167d5218d20076df3218d20316dd3218d20014fe7118d20004fd7118d20014fc7118d20006de3118d20076dc3118d2001cff7018d2001cfd7018d20076df3018d2030edd3018d200acff76d0d20004fe76d0d20004fd76d0d200acfc76d0d20006bf64d0d200aebc64d0d2001dee72d0d20005ed72d0d20074ff7690d20004fe7690d20004fd7690d20074fc7690d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d200457c7550d20006bf6450d20006bc6450d20074ff7610d20004fe7610d20004fd7610d20074fc7610d200457e7510d200057d7510d2001dee7210d20005ed7210d2000dfa7010d20005f97010d2000dec765092015eec765092000cec765092001def745092001faf7450920007af64509200aeee64509200aeec6450920007ac6450920007ae4350920007ac4350920007eb705092000dee705092000dec705092015fe8705092001eef605092001feb605092015faf405092015fad405092015fea1050920014fe76d852003ef661d8520004ff75d8520024fe75d8520004fd75d8520024fc75d85200acfe74d8520004fd74d8520074fe73d8520004fd73d852000cfd72d8520014fc72d85203067f52d85203067d52d852003ef621d8520306f521d852000cfe70d852001cfd70d852000cfc70d8520286f710d85200057f75585200457c7558520005bf7458520005bc7458520005df7358520005dc735852003ef461585202fdfb7058520004fe76d0520004fd76d05200acfc76d05200457e75d05200057d75d052001dee72d0520005ed72d0520007ad42d0520004ff7650520004fe7650520004fc7650520007ad4250520004fe76cc520004fd76cc520074fc76cc520004ff764c520004fe764c520004fc764c5200057f754c5200457c754c5202f57e76d951002e7e76d95100247e76d95100057d72d95100067e62d95100067c62d95102e77771d95102e77471d95102ef7641d95102ef7431d95102ef7621d95102ef7b70d95102e77870d95102e77840d95102e77a30d95102e77a20d95102ef7b10d95102e77610d95102e77410d95102e77810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067e42d95100067c42d95100067e32d95100067c32d95102e67f71d95102ee7e71d95102e67d71d95102e67
  | 5 => 0x3467f52d91203467d52d9120346bf42d9120346bd42d9120014fe71d9120004fd71d9120014fc71d9120006be41d9120006bc41d912001cff70d912001cfd70d912033ebf40d912033ebd40d912015cfd7699120006bf649912015ded729912008df970991200acff7599120024fe7599120004fd75991200acfc75991200acfe7499120074fe7399120004fd739912015cfd72991200aeed72991200a67f52991200a67d52991200aeee4299120014fe7199120004fd7199120014fc7199120174fd70991200aef97099120176fa10991200057f75591200457c7559120175ef72591200a5fb7059120004ff75591200067f75591200047f7559120024fe7559120004fd7559120024fc75591200067c75591200247c7559120006bf7459120004ff7359120074fc7359120174ff7259120006ef725912008e7f525912008e7d5259120004ff7159120014fe7159120014fc715912015cff7059120006fb705912033cfe76191200457e75191200057d7519120006bd64191200acff7519120024fe75191200ae7e75191200247e7519120004fd75191200ae7d75191200047d75191200acfc75191200acfe74191200aebe7419120006bf54191200aebc5419120074fe7319120004fd731912000cff721912001cfe721912000cfd72191200aeed721912001cfc72191203367f52191203367d52191200aebf42191200aeee4219120336bd4219120014fe7119120004fd7119120014fc7119120006be41191200aebc411912001cff701912001cfd70191200aebf401912032ebd401912032efa10191200457e75d8d200057d75d8d20004ff75d8d20024fe75d8d200067e75d8d200247e75d8d20004fd75d8d200067d75d8d200047d75d8d20024fc75d8d200acfe74d8d20004fd74d8d2000cff72d8d2000cfd72d8d203267f52d8d203267d52d8d20326df32d8d20326dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20006dc31d8d2001cff70d8d2001cfd70d8d2031edf30d8d2031edd30d8d2031efa10d8d2012cfd7698d200457e7598d200057d7598d20005be7498d20005bd7498d20006df6398d2012ded7298d20055f97098d20074ff7598d20024fe7598d200767e7598d200247e7598d20004fd7598d200767d7598d200047d7598d20074fc7598d200acfe7498d20076be7498d20004be7498d20004fd7498d20076bd7498d20004bd7498d20074fe7398d2012cfd7298d20076ed7298d2006e7f5298d2006e7d5298d20014fe7198d20004fd7198d20014fc7198d20144fd7098d20076f97098d20145ef7258d2006dfb7058d20004ff7558d20024fe7558d20004fd7558d20024fc7558d20004ff7458d200acfc7458d20006df7358d20144ff7258d20006ef7258d200567f5258d200567d5258d20004ff715
  | 6 => 0xc73d89300567f52d8930056ee32d8930014fe71d8930004fd71d8930014fc71d8930006ee21d8930056ec21d8930146ef20d8930146fa10d8930056ec62589300067f76549300067e76549300067d76549300067c76549300067f64549300067e64549300067d64549300067c645493018e7f63549300075e43549300075d435493027d7f725493005f6f72549300567f625493001e7e625493001e7c62549301967e61549301967c615493018e7f605493018f5e305493018f5c305493018f78305493018f7a1054930004fe76d0930004fd76d09300acfc76d0930006bf64d09300aebc64d0930005de73d0930005dd73d09300079e43d0930004ff7650930004fe7650930004fc7650930006bf6450930006bc64509300079e435093030cfe76cc93030dde76cc930326de76cc930005df74cc930005dd74cc930006de64cc930006dc64cc93012ddd72cc93001ede62cc93001edc62cc9300575f52cc9300575d52cc93000dde70cc93000ddc70cc930076df60cc930147da10cc93000cfc764c930006ef624c93001eec624c930005fb704c93000df8704c93000ddc764c93001edc764c93000cdc764c930005df744c930005dd744c930006de644c930006dc644c930145df724c930007cf724c930007cf624c93001ede624c93001edc624c930057cc624c93001ecc624c9300575f524c9300575d524c930057cf214c930007db704c93000dde704c93000ddc704c93012fd8704c93012edf604c93012fda104c930014fe76d853004ef661d8530004ff75d8530024fe75d8530004fd75d8530024fc75d85300acfe74d8530004fd74d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d85300067f52d85300067d52d8530006df32d8530006dd32d853004ef631d85300e6f710d85300057f755853005d7c7558530005bf7458530005bc7458530005ef7258530055ec725853004ef46158530004fe76d0530004fd76d05300acfc76d053005d7e75d05300057d75d0530005de73d0530005dd73d05300079d43d0530004ff7650530004fe7650530004fc76505300079d43505302a4fe76cc530016f661cc53000df870cc53000cfc764c5300057f754c53005d7c754c530006f7614c530016f4614c53004fd4314c530005fb704c53000df8704c530004ff7648530004fe7648530004fc7648530007cd324853000dfa76cc13000efa76cc13000cfa76cc1300777a75cc1300777975cc13000dfa73cc13000fda73cc13000efb63cc13000fdb63cc130077da43cc130007d943cc13034f7b52cc1300077952cc130077db32cc130007d932cc130005f971cc130004ff75d9120024fe75d9120004fd75d9120024fc75d9120006bf54d9120006bc54d9120074fe73d9120004fd73d912000cff72d912000cfd72d9120
  | 7 => 0x7300067d6550730006be6450730006bd64507300079d43507302b4ff764c7300057f754c73007d7c754c7300de7e654c7300067d654c730077d4314c730004ff7648730004fd7648730074fc76487300c67e65487300067d654873001eee6248730006ed6248730007cd3248730004ff75d9130024fe75d9130004fd75d9130024fc75d9130006bf54d9130006bc54d913001cfe72d9130004fd72d913001cfc72d91300067f52d9130014fe71d9130004fd71d9130014fc71d9130006be41d9130006bc41d9130074ff70d91301ecfd70d91301eebf40d91301eebd40d9130006bf64991301cddd73991300acff7599130024fe7599130004fd75991300acfc75991300acfe74991301ccfd73991300aedd739913001cfe7299130004fd729913001cfc72991300067f5299130014fe7199130004fd7199130014fc7199130204fd70991300aef97099130206fa10991300057f755913005d7c7559130205df7359130004ff75591300067f75591300047f7559130024fe7559130004fd7559130024fc75591300067c75591300247c7559130006bf7459130204ff7359130006df7359130004ff725913001cfe725913001cfc72591300067f5259130004ff7159130014fe7159130014fc71591301ccff7059130006fb70591301ecfe761913005d7e75191300057d7519130006bd64191300acff7519130024fe75191300ae7e75191300247e7519130004fd75191300ae7d75191300047d75191300acfc75191300aebe7419130006bf54191300aebc5419130074fe73191300aedd7319130074fc731913001cfe7219130004fd721913001cfc72191300067f5219130014fe7119130004fd7119130014fc7119130006be41191300aebc4119130074ff701913019cfd70191300aebf401913019ebd401913019efa101913000cfe76d0d3000cfc76d0d30006bf64d0d300aebc64d0d3000dfa70d0d30005f970d0d3019cfe7690d3019dde7690d30006de7690d301cddd7490d300aede6490d300aedc6490d30005dd7290d3035f5f5290d3000dde7090d3000ddc7090d30076df6090d301efda1090d300acff7650d3000cfe7650d301ccfd7650d3000cfc7650d300057f7550d3005d7c7550d30006bf6450d30006bc6450d30005fb7050d3000df87050d3000ddc7650d301cedc7650d3000cdc7650d300075f7550d303575c7550d300079f7450d300079f6450d300aede6450d300aedc6450d300079c6450d30005df7250d303575f5250d30007db7050d3000dde7050d3000ddc7050d301cfd87050d301cedf6050d301cfda1050d301ecfe7610d3005d7e7510d300057d7510d301edde7310d3001cfe76d8930056ee62d8930004ff75d8930024fe75d8930004fd75d8930024fc75d89300acfe74d8930004fd74d893000cfd73d893001cf
  | 8 => 0x77da7090f30077d97090f3000ddc7090f30204ff7650f300057f7550f3007d7c7550f301e67e6550f300067d6550f30205df7650f30006df7650f300075f7550f3036f5c7550f3036f5e6550f300075d6550f300779f7450f300aede6450f300aedc6450f30005df7250f3036f5f5250f3000dde7050f3000ddc7050f3001cff7658b3007d7e7558b300067e6558b300067d6558b30076ec6258b30004ff7558b30024fe7558b300067e7558b300247e7558b30004fd7558b300067d7558b30024fc7558b30004ff7458b300acfc7458b3001cfd7358b3000cfc7358b3006e7f5258b3006eec4258b30076ef3258b30076ec3258b30004ff7158b30014fe7158b30014fc7158b3006eef2158b3012eef2058b300057f7654b300067f7654b300047f7654b300067e7654b300057d7654b300067d7654b300047d7654b300067c7654b300067f6454b300067e6454b300067d6454b300067c6454b3018e7e6354b300075e4354b300075d4354b3027d7f7254b3007f6f7254b3001e7e6254b3006e7d6254b3001e7c6254b301967e6154b301967c6154b3018e7d6054b3018f5e3054b3018f7a3054b3018f5c3054b300acff76d0b30074fe76d0b30004fd76d0b301867e65d0b300067d65d0b30006bf64d0b300aebc64d0b30075de73d0b30005dd73d0b300079e43d0b3001eee62d0b30006ed62d0b30004ff7650b30004fd7650b30074fc7650b3016e7e6550b300067d6550b30006bf6450b30006bc6450b300079e4350b30005fb7050b3000df87050b3000ddd76ccb3001edd76ccb3000cdd76ccb300775e65ccb300775d65ccb30075df74ccb30005dd74ccb30006de64ccb30076dc64ccb3001ede62ccb30077ce62ccb30077cd62ccb3001edc62ccb3006f5f52ccb3006f5d52ccb3000dde70ccb30077da70ccb30077d970ccb3000ddc70ccb3031cff764cb3013e7e654cb300067d654cb3031ddf764cb30316df764cb303675e654cb300075d654cb30005df744cb30005dd744cb30006de644cb30006dc644cb30077cf724cb3001ede624cb3001edc624cb3006f5f524cb3006f5d524cb3006fcf214cb3000dde704cb3000ddc704cb30014ff76587300067e65587300067d6558730076f46158730004ff7558730024fe7558730004fd7558730024fc7558730004ff74587300acfc7458730014fd735873000cfc7358730004ff725873001cfe725873001cfc72587300067f52587300067d5258730006df3258730006dd3258730076f73158730076f431587300cefa30587300cef710587300acff76d0730074fe76d0730004fd76d073007d7e75d07300057d75d07301267e65d07300067d65d07300aebe64d0730006bd64d0730075de73d0730005dd73d07300079d43d0730004ff7650730004fd7650730074fc765073010e7e655
  | 9 => 0xf76597300767f64597300767c64597300057f72597300767f62597300067e62597300767c62597300767f61597300067e61597300767c615973037f5e30597300777a30597300775c30597300067f74597300067e74597300067d74597300067c745973007e7f73597300767e735973037e7d73597300767c73597300767e43597300767c43597300067f72597300047f72597300067e72597300067d72597300067c72597300067e42597300067c42597300767f32597300067e32597300767c32597300067f71597300067e71597300067d71597300067c71597300067e41597300067c41597300767f31597300067e31597300767c31597300067f21597300067e21597300067c215973037e7f705973037e7e705973037e7d705973037e7c705973037e7f405973037e7e405973037e7d405973037e7c40597300767f305973037e7e305973037e7d30597300767c305973037e7f205973037e7e205973037e7d205973037e7c205973037e7f105973037e7e105973037e7d105973037e7c1059730074ff75d9330024fe75d93300767e75d93300247e75d9330004fd75d93300767d75d93300047d75d9330074fc75d9330074fe73d9330076de73d933001cfe72d9330076ee72d933001cee72d9330004fd72d9330076ed72d9330004ed72d933001cfc72d93300067f52d9330014fe71d9330004fd71d9330014fc71d9330076f970d93301ccfd76993300067e65993300067d6599330076bf64993300acff7599330024fe7599330004fd75993300acfc759933000cfe73993300aede739933000cfc7399330076be4399330076bc439933001cfe7299330004fd729933001cfc72993300067f5299330006be42993300aebc4299330014fe7199330004fd7199330014fc71993300aebf4099330206bd40993300067e65593300067d6559330076bc6459330004ff7559330024fe7559330004fd7559330024fc7559330076bf74593300acff735933000cfe73593301ccfd735933000cfc7359330076be4359330076bc4359330004ff725933001cfe725933001cfc72593300067f5259330006be4259330006bc4259330004ff7159330014fe7159330014fc71593301cebf40593301cebd4059330074ff7519330024fe75193300767e75193300247e7519330004fd75193300767d75193300047d7519330074fc75193300acfe7419330076be7419330074fe7319330076de731933001cfe7219330004fd721933001cfc72193300067f5219330014fe7119330004fd7119330014fc7119330076f970193301ccfd76d0f301c67e65d0f300067d65d0f3000ddd7690f30076dd7690f3000cdd7690f300775e6590f300775d6590f300aede6490f300779e6490f300779d6490f30076dc6490f30005dd7290f303775f5290f3000dde7090f30
  | 10 => 0x8940004fd71d8940014fc71d8940006ee21d894008eec21d8940176ef20d89400057f75589400957c75589400067f65589400067c655894008eec62589400067f76549400057e76549400067e76549400047e76549400067d76549400057c76549400067c76549400047c765494018e7f64549400067f63549400067c635494027d7f72549400976f725494008e7f625494001e7e625494001e7c62549401967e61549401967c615494018e7f605494018f3e405494018f3c405494018f78405494032cfe76d09400067f65d09401867c65d094032dbe76d0940346be76d09400073f65d09403973c65d0940006bc63d094015dbd72d094001ebe62d094001ebc62d094008f3f52d094008f3d52d094000dbe70d094000dbc70d09400aebf60d094000cfc76509400067f655094016e7c6550940006ef625094001eec625094008fac4250940005fb705094000df8705094000dbc765094001ebc765094000cbc76509400073f655094038f3c6550940006bc6350940175bf7250940007af7250940007af625094001ebe625094001ebc625094008fac625094008f3f525094008f3d5250940007bb705094000dbe705094000dbc705094015fb8705094000db8705094015ebf605094015faf2050940004fe76cc940004fd76cc940074fc76cc9400067f65cc9401567c65cc940006df63cc940076dc63cc940004ff764c940004fe764c940004fc764c9400067f654c94013e7c654c940006df634c940006dc634c940006ef624c94001eec624c940014fe76d85400067f65d85400067c65d8540086f661d8540004ff75d8540024fe75d8540004fd75d8540024fc75d854000cfd74d8540014fc74d8540074fe73d8540004fd73d854001cfe72d8540004fd72d854001cfc72d85400067f52d85400067d52d8540006bf42d8540006bd42d8540086f641d8540116f840d8540116f710d85400057f75585400957c75585400067f65585400067c6558540005df7358540005dc7358540005ef725854008dec7258540086f461585402c4fe76d05400957e75d05400057d75d05400067f65d05401267c65d05400afb840d054000cfc76505400067f655054010e7c6550540006f76150540016f46150540005fb705054000df870505400ffb84050540004fe76cc540004fd76cc540074fc76cc5400067f65cc5400f67c65cc540004ff764c540004fe764c540004fc764c5400057f754c5400957c754c5400067f654c5400de7c654c540004ff7648540004fe7648540004fc76485400067f65485400c67c654854000dfa76d014000efa76d01400077b65d01403877865d014000dfa74d014000fba74d014000efb64d014000fbb64d01403877b52d01400077952d01400afbb42d0140007b942d0140006fb61d01400757f765973007e7f76597300247
  | 11 => 0x67f52587400067d5258740006bf4258740006bd42587400aef741587400aef441587400fef710587402d4ff7650740016f4615074000dfa7050740074ff76cc7400acfe76cc740004fd76cc740004ff764c740004fd764c7400acfc764c7400057f754c7400b57c754c740004ff7648740004fd76487400acfc76487403a57e76d95400967e76d95400247e76d95400057d72d95400067e62d95400067c62d95400067e61d95400067c61d954039f3e40d954039f3c40d954039f7840d954039e7f74d95400967e74d954039e7d74d954039e7c74d95400067f73d95400067e73d95400067d73d95400067c73d95400067f72d95400067e72d95400067d72d95400047d72d95400067c72d95400067e42d95400067c42d95400067e32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95400067e41d95400067c41d95400067e31d95400067c31d95400067f21d95400067e21d95400067c21d954039e7f70d954039e7e70d954039e7d70d954039e7c70d954039e7f40d954039e7e40d954039e7d40d954039e7c40d954039e7f30d954039e7e30d954039e7d30d954039e7c30d954039e7f20d954039e7e20d954039e7d20d954039e7c20d954039e7f10d954039e7e10d954039e7d10d954039e7c10d95400067f65d8d400067c65d8d40004ff75d8d40024fe75d8d40004fd75d8d40024fc75d8d4001cfe72d8d40004fd72d8d4001cfc72d8d400067f52d8d40014fe71d8d40004fd71d8d40014fc71d8d40006de31d8d40006dc31d8d40206df30d8d400957e7598d400057d7598d400067f6598d400067c6598d40006df6398d4008dee7298d40005ed7298d400057f7558d400957c7558d400067f6558d400067c6558d400067f6518d400067c6518d40006dd6318d40074ff7518d40024fe7518d40004fd7518d40074fc7518d4001cfe7218d40004fd7218d4001cfc7218d400067f5218d40014fe7118d40004fd7118d40014fc7118d40006de3118d40076dc3118d40076df3018d4019edd3018d4019cfe76d0d400067f65d0d401c67c65d0d400afb840d0d4000cfe7690d400067f6590d401be7c6590d40006df6390d40076dc6390d4000dfa7090d40005f97090d4000cfc7650d400057f7550d400957c7550d400067f6550d401e67c6550d40006df6350d40006dc6350d40005fb7050d4000df87050d401cfb84050d40204fe7610d400957e7510d400057d7510d400067f6510d401b67c6510d4001cfe76d89400957c75d89400067f65d89400067c65d894008eee62d8940004ff75d89400067f75d8940024fe75d8940004fd75d8940024fc75d89400067c75d89400247c75d894000cfd74d894001cfc74d8940074fe73d8940004fd73d894008e7f52d894008eee42d894008eee32d8940014fe71d
  | 12 => 0xc434c921007e7714c921015ee714c921015ec714c921137e4714c92101eef614c92101fe7614c921137cf314c921137cd314c921137e7104c92100cfe76d81210befa60d8121004ff75d8121024fe75d8121004fd75d8121024fc75d81210acfe74d8121004fd74d8121074fe73d8121004fd73d8121014fd72d812100cfc72d81212fe7f52d81212fe7d52d812101cfd71d812100cfc71d81210befa20d81210befa10d81210057f75581210c57c7558121005bf7458121005bc7458121005df7358121005dc73581210bef860581210aedf6398f40074ff7598f40024fe7598f40004fd7598f40074fc7598f4000cfe7498f400aedf4398f40076dc4398f4001cfe7298f40004fd7298f4001cfc7298f400067f5298f40014fe7198f40004fd7198f40014fc7198f40076df3098f401eedd3098f400057f7558f400b57c7558f400aedc6358f40004ff7558f400067f7558f400047f7558f40024fe7558f40004fd7558f40024fc7558f400067c7558f400247c7558f4000cfc7458f400aedf4358f400aedc4358f40004ff7258f4001cfe7258f4001cfc7258f400067f5258f40004ff7158f40014fe7158f40014fc7158f401cedf3058f401cefa1058f401ccfd7690f401ecff7650f400057f7550f400b57c7550f4001cff7658b400aeec6258b40004ff7558b40024fe7558b40004fd7558b40024fc7558b4001cfd7458b4000cfc7458b40004ff7358b40074fc7358b400a67f5258b400aeef4258b400aeec4258b40004ff7158b40014fe7158b40014fc7158b4015eef2058b4015efa1058b400067f7654b400067e7654b400067d7654b400067c7654b4018e7e6454b400067e6354b400067d6354b4027d7f7254b400b76f7254b4001e7e6254b400a67d6254b4001e7c6254b401967e6154b401967c6154b400077b7054b4018f787054b4018e7d6054b4018f3e4054b4018f7a4054b4018f3c4054b4018f7a1054b4000dbd76d0b4001ebd76d0b4000cbd76d0b40006be63d0b4001ebe62d0b400afae62d0b400afad62d0b4001ebc62d0b400a73f52d0b400a73d52d0b4000dbe70d0b400afba70d0b400afb970d0b4000dbc70d0b40177ba10d0b4033cff7650b4001eec6250b400afac4250b4033dbf7650b40336bf7650b40006be6350b400afaf7250b400afaf6250b4001ebe6250b4001ebc6250b400afac6250b400a73f5250b400a73d5250b4000dbe7050b4000dbc7050b4015faf2050b4015fba1050b40074ff76ccb400acfe76ccb40004fd76ccb40004ff764cb40004fd764cb400acfc764cb40005fb704cb4000df8704cb40014ff76587400aef46158740004ff7558740024fe7558740004fd7558740024fc7558740014fd745874000cfc7458740004ff7358740074fc7358740004ff725874001cfe725874001cfc7258740
  | 13 => 0x91213dcfe7619121006bd64191210acff7519121024fe7519121004fd75191210acfc75191210acfe74191210aebe7419121074fe7319121004fd7319121014ff7219121014fd72191213d67f52191213d67d52191210aebf42191213d6bd421912101cff711912101cfd71191210aebf41191213cebd411912100cfe7019121004fd701912100cfc7019121006be40191210aebc4019121004ff75d8d21024fe75d8d21004fd75d8d21024fc75d8d210acfe74d8d21004fd74d8d21006df53d8d21006dc53d8d21014ff72d8d21014fd72d8d213c67f52d8d213c67d52d8d213c6df32d8d213c6dd32d8d2101cff71d8d2101cfd71d8d213bedf31d8d213bedd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d21134fd7698d21006df6398d21135ed7298d210d5f57198d21074ff7598d21024fe7598d21004fd7598d21074fc7598d210acfe7498d21004fd7498d21074fe7398d21134fd7298d21076ed7298d210ee7f5298d210ee7d5298d21076ee3298d2114cfd7198d21076f57198d2100cfe7098d21004fd7098d2100cfc7098d2114ef71098d210057f7558d210c57c7558d2114def7258d210edf77158d21004ff7558d210067f7558d210047f7558d21024fe7558d21004fd7558d21024fc7558d210067c7558d210247c7558d21004ff7458d210acfc7458d21006df7358d2114cff7258d21006ef7258d210d67f5258d210d67d5258d21134ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d213bcfe7618d210c57e7518d210057d7518d21006dd6318d21074ff7518d21024fe7518d210767e7518d210247e7518d21004fd7518d210767d7518d210047d7518d21074fc7518d210acfe7418d21004fd7418d21074fe7318d21076de7318d21006df5318d21076dc5318d21014ff7218d21014fd7218d21076ed7218d213b67f5218d213b67d5218d21076df3218d21076ee3218d213b6dd3218d2101cff7118d2101cfd7118d21076df3118d213aedd3118d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d21076dc3018d213aef71018d210acff76d0d21004fe76d0d21004fd76d0d210acfc76d0d21074ff7690d21004fe7690d21004fd7690d21074fc7690d21006df6390d21076dc6390d2101dee7290d21005ed7290d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210c57c7550d21006df6350d21006dc6350d21074ff7610d21004fe7610d21004fd7610d21074fc7610d210c57e7510d210057d7510d2101dee7210d21005ed7210d21015f67110d21005f57110d21015ec764c921136ec764c921014ec764c92101def734c92101fcf734c921007cf634c921076ee634c921076ec634c921007cc634c921007cf434c921007c
  | 14 => 0x6bf6450931006bc6450931006ef625093101eec62509313acfe76cc9310067f65cc9311567c65cc9313adde76cc9313c6de76cc9310075f65cc9313ff5c65cc931006de64cc931006dc64cc931135dd72cc93101ede62cc93101edc62cc9310d75f52cc9310d75d52cc931015de71cc931015dc71cc931076df61cc931014fc764c9310067f654c93113e7c654c931006ef624c93101eec624c9310d7cc324c931005f7714c931015f4714c931015dc764c93101edc764c931014dc764c9310075f654c9313f75c654c931006de644c931006dc644c93114ddf724c931007cf724c931007cf624c93101ede624c93101edc624c9310d7cc624c9310d75f524c9310d75d524c931007d7714c931015de714c931015dc714c931137d4714c931015d4714c931136df614c931137cf214c9310077765cc5313ef7465cc531015f673cc531017d673cc531016f763cc531017d763cc5313ef7752cc5310077552cc531077d732cc531007d532cc53100cfe76d81310067f65d81310067c65d81310cefa60d8131004ff75d8131024fe75d8131004fd75d8131024fc75d81310acfe74d8131004fd74d8131014fd73d813101cfe72d8131004fd72d813101cfc72d81310067f52d81310067d52d8131006df32d8131006dd32d8131006f731d8131066f431d81310cefa30d81310cefa10d81310057f75581310dd7c75581310067f65581310067c6558131005bf7458131005bc7458131005ef72581310d5ec72581310cef860581310c57e75d91210057d75d9121004ff75d9121024fe75d91210067e75d91210247e75d9121004fd75d91210067d75d91210047d75d9121024fc75d9121074fe73d9121004fd73d9121014ff72d9121014fd72d91213e67f52d91213e67d52d91213e6bf42d91213e6bd42d912101cff71d912101cfd71d91213debf41d91213debd41d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d91213def710d9121164fd76991210c57e75991210057d7599121006bf6499121005de7399121005dd7399121165ed7299121105f571991210acff7599121024fe75991210ae7e75991210247e7599121004fd75991210ae7d75991210047d75991210acfc75991210acfe7499121074fe73991210aede7399121004de7399121004fd73991210aedd7399121004dd7399121164fd72991210aeed729912111e7f529912111e7d529912117cfd71991210aef5719912100cfe7099121004fd709912100cfc709912117def725912111df77159121004ff7559121024fe7559121004fd7559121024fc7559121006bf7459121004ff7359121074fc735912117cff7259121006ef72591211067f52591211067d5259121164ff7159121006f77159121004ff705912100cfe705912100cfc7059121166f7105
  | 15 => 0xc6599131006bf64991311d5dd73991310d5ee7299131005ed72991310acff7599131024fe75991310ae7e75991310247e7599131004fd75991310ae7d75991310047d75991310acfc75991310acfe74991311d4fd73991310aedd739913101cfe72991310aeee729913101cee7299131004fd72991310aeed7299131004ed729913101cfc72991310067f529913120cfd71991310aef5719913100cfe7099131004fd709913100cfc70991310057f75591310dd7c75591310067f65591310067c655913120ddf7359131004ff75591310067f75591310047f7559131024fe7559131004fd7559131024fc75591310067c75591310247c7559131006bf745913120cff7359131006df7359131004ff725913101cfe725913101cfc72591310067f52591311d4ff7159131006f77159131004ff705913100cfe705913100cfc70591311f4fe76191310067f65191310067c6519131006bd64191310acff7519131024fe7519131004fd75191310acfc75191310aebe741913101cfe7219131004fd721913101cfc72191310067f5219131074ff71191311a4fd71191310aebf41191311a6bd411913100cfe7019131004fd701913100cfc7019131006be40191310aebc4019131014fe76d0d31014fc76d0d310067f65d0d311c67c65d0d31006bf64d0d310aebc64d0d31015f671d0d31005f571d0d311a4fe7690d310067f6590d311be7c6590d31077d43190d310acff7650d31014fe7650d311d4fd7650d31014fc7650d310057f7550d310dd7c7550d310067f6550d311e67c6550d31006bf6450d31006bc6450d31005f77150d31015f47150d311d7d43150d311f4fe7610d310dd7e7510d310057d7510d310067f6510d311b67c6510d3101cfe76d89310dd7c75d89310067f65d89310067c65d89310d6ee62d8931004ff75d89310067f75d8931024fe75d8931004fd75d8931024fc75d89310067c75d89310247c75d89310acfe74d8931004fd74d8931014fd73d89310d67f52d89310d6ee42d89310d6ee32d893114eef21d893100cfe70d8931004fd70d893100cfc70d8931006ee20d89310d6ec20d89310057f75589310dd7c75589310067f65589310067c65589310d6ec62589310067f76549310057e76549310067e76549310047e76549310067d76549310057c76549310067c76549310047c76549310067f64549310067e64549310067d64549310067c64549311967f63549314057f72549310df6f72549310d67f625493101e7e625493101e7c62549311967f61549311975e31549311975c315493119774315493118e7e605493118e7c6054931004fe76d0931004fd76d09310acfc76d09310067f65d09311867c65d0931006bf64d09310aebc64d0931004ff7650931004fe7650931004fc76509310067f655093116e7c6550931
  | 16 => 0x8b31136f71058b310067f7654b310067e7654b310067d7654b310067c7654b310067f6454b310067e6454b310067d6454b310067c6454b311967e6354b314057f7254b310f76f7254b3101e7e6254b310ee7d6254b3101e7c6254b31007777154b31197747154b311967d6154b311975e3154b31197763154b311975c3154b3118e7e6054b3118e7c6054b31197771054b310acff76d0b31074fe76d0b31004fd76d0b31006bf64d0b310aebc64d0b31004ff7650b31004fd7650b31074fc7650b31006bf6450b31006bc6450b31005f77150b31015f47150b31015dd76ccb3101edd76ccb31014dd76ccb31006de64ccb31076dc64ccb3101ede62ccb31077ce62ccb31077cd62ccb3101edc62ccb310ef5f52ccb310ef5d52ccb31015de71ccb31077d671ccb31077d571ccb31015dc71ccb3114fd710ccb313bcff764cb3101eec624cb31077cc324cb313bddf764cb313b6df764cb31006de644cb31006dc644cb31077cf724cb31077cf624cb3101ede624cb3101edc624cb31077cc624cb310ef5f524cb310ef5d524cb31015de714cb31015dc714cb31137cf214cb31137d7104cb3100cff7658331076f86058331004ff7558331024fe7558331004fd7558331024fc7558331004ff74583310acfc7458331014fc7358331004ff725833101cfe725833101cfc72583310067f52583310067d5258331006df3258331006dd3258331076fb3058331076f830583310e6fa10583314157e76d95310de7e76d95310247e76d95310057d72d95310067e62d95310067c62d953140f5e31d953140f5c31d953140f7431d95310067e60d95310067c60d95310067f74d95310067e74d95310067d74d95310067c74d953140e7f73d95310de7e73d953140e7d73d953140e7c73d95310067f72d95310067e72d95310067d72d95310047d72d95310067c72d95310067e42d95310067c42d95310067e32d95310067c32d953140e7f71d953140e7e71d953140e7d71d953140e7c71d953140e7f41d953140e7e41d953140e7d41d953140e7c41d953140e7f31d953140e7e31d953140e7d31d953140e7c31d953140e7f21d953140e7e21d953140e7d21d953140e7c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067e40d95310067c40d95310067e30d95310067c30d95310067f20d95310067e20d95310067c20d953140e7f10d953140e7e10d953140e7d10d953140e7c10d95310067f65d91310067c65d9131004ff75d9131024fe75d9131004fd75d9131024fc75d913101cfe72d9131004fd72d913101cfc72d91310067f52d9131074ff71d91311f4fd71d91311f6bf41d91311f6bd41d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d91310dd7e75991310057d75991310067f65991310067
  | 17 => 0x1ebe625094101ebc6250941107ac625094101eac62509411073f52509411073d5250941007b77150941015be7150941015bc7150941167b47150941166bf6150941107af2050941167b71050941004fe76cc941004fd76cc941074fc76cc941005be74cc941005bd74cc941006df63cc941076dc63cc9410079f43cc941004ff764c941004fe764c941004fc764c941005be744c941005bd744c941006df634c941006dc634c9410079f434c9410af7675d05410af7575d0541015f674d0541017b674d0541016f764d0541017b764d05410afb743d0541007b543d054141f7752d05410077552d05410afb742d0541007b542d0541005f570d054100cfe76d81410fefa60d8141004ff75d8141024fe75d8141004fd75d8141024fc75d8141014fd74d8141074fe73d8141004fd73d814101cfe72d8141004fd72d814101cfc72d81410067f52d81410067d52d8141006bf42d8141006bd42d81410fefa40d81410fefa10d81410057f755814110d7c7558141005df7358141005dc7358141005ef7258141105ec72581410fef86058141074ff75d9331024fe75d9331004fd75d9331074fc75d9331074fe73d9331076de73d933101cfe72d9331004fd72d933101cfc72d93310067f52d9331076f571d933100cfe70d9331004fd70d933100cfc70d93311f6f710d93311d4fd7699331076bf64993310acff7599331024fe7599331004fd75993310acfc7599331014fe7399331014fc7399331076be4399331076bc439933101cfe7299331004fd729933101cfc72993310067f52993310aebf419933120ebd419933100cfe7099331004fd709933100cfc70993310057f75593310f57c7559331076bc6459331004ff75593310067f75593310047f7559331024fe7559331004fd7559331024fc75593310067c75593310247c7559331076bf7459331014fe7359331014fc7359331076be4359331076bc4359331004ff725933101cfe725933101cfc72593310067f52593311d6bf41593311d6bd4159331004ff705933100cfe705933100cfc70593311d6f71059331074ff7519331024fe75193310767e75193310247e7519331004fd75193310767d75193310047d7519331074fc75193310acfe7419331076be7419331074fe7319331076de731933101cfe7219331004fd721933101cfc72193310067f5219331076f5711933100cfe7019331004fd701933100cfc70193311d4fd76d0f31076bf64d0f31076bc64d0f3120cff7650f310057f7550f310f57c7550f31076bf6450f31076bc6450f3101cff7658b31076ec6258b31004ff7558b31024fe7558b31004fd7558b31024fc7558b31004ff7458b310acfc7458b31014fc7358b310ee7f5258b31076ef3258b31076ec3258b31136ef2158b31004ff7058b3100cfe7058b3100cfc705
  | 18 => 0xc7558341014fc7458341004ff7358341074fc7358341004ff725834101cfe725834101cfc72583410067f52583410067d5258341006bf4258341006bd4258341086f641583410aefb40583410aef84058341116fa1058341004ff75d8d41024fe75d8d41004fd75d8d41024fc75d8d41006df53d8d41006dc53d8d4101cfe72d8d41004fd72d8d4101cfc72d8d410067f52d8d4120edf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d41006df6398d410057f7558d4110d7c7558d4110d7e7518d410057d7518d41006dd6318d41074ff7518d41024fe7518d410767e7518d410247e7518d41004fd7518d410767d7518d410047d7518d41074fc7518d41076bd7418d41006df5318d41076dc5318d4101cfe7218d41004fd7218d4101cfc7218d410067f5218d41076df3118d411a6dd3118d4100cfe7018d41004fd7018d4100cfc7018d41006de3018d41076dc3018d411a6f71018d411a4fe76d0d411a5be76d0d41006be76d0d41076bc63d0d41005bd72d0d4142f3f52d0d41015be71d0d41015bc71d0d410aebf61d0d4120fb710d0d41014fe7690d411d5bd7490d41006df6390d41076dc6390d41015f67190d41005f57190d41014fc7650d410057f7550d4110d7c7550d41006df6350d41006dc6350d41005f77150d41015f47150d41015bc7650d411d6bc7650d41014bc7650d410073f7550d414273c7550d410079f7350d410079f6350d41076bc6350d410079c6350d41005bf7250d414273f5250d41007b77150d41015be7150d41015bc7150d411d7b47150d411d6bf6150d411d7b71050d4120cfe7610d4110d7e7510d410057d7510d4120dbe7410d4101cfe76d8941106ee62d8941004ff75d8941024fe75d8941004fd75d8941024fc75d8941014fd74d8941074fe73d8941004fd73d89411067f52d8941106ee42d894117eef21d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941106ec20d894117ef710d8941106ec62589410067f76549410067e76549410067d76549410067c76549411967f64549410067f63549410067c63549410073f43549410073d43549414057f725494110f6f72549411067f625494101e7e625494101e7c62549411967f61549411973e41549411973c415494119774415494118e7e605494118e7c60549411977710549413ccfe76d09413cdbe76d09413e6be76d0941005bd73d0941006bc63d0941165bd72d094101ebe62d094101ebc62d09411073f52d09411073d52d0941015be71d0941015bc71d09410aebf61d094117fb710d0941014fc7650941006ef625094101eec6250941005f77150941015f47150941015bc765094101ebc7650941014bc7650941005bf7350941006bc635094117dbf7250941007af7250941007af6250941
  | 19 => 0x8f41006de3298f41076dc3298f41076df3198f411f6dd3198f4100cfe7098f41004fd7098f4100cfc7098f410067e6558f410067d6558f410aedc6358f41004ff7558f41024fe7558f41004fd7558f41024fc7558f41014fc7458f410aedf4358f410aedc4358f41004ff7258f4101cfe7258f4101cfc7258f410067f5258f41006de3258f41006dc3258f411d6df3158f41004ff7058f4100cfe7058f4100cfc7058f41015bd76d0f410aebd76d0f41014bd76d0f410af3e65d0f410af3d65d0f41076be63d0f410af9e63d0f410af9d63d0f41005bd72d0f414473f52d0f41015be71d0f410afb671d0f410afb571d0f41015bc71d0f411d4fd7690f411be7e6590f410067d6590f411f4ff7650f410057f7550f411257c7550f411e67e6550f410067d6550f411f5bf7650f41006bf7650f410073f7550f4143f3c7550f4143f3e6550f410073d6550f410af9f7350f41076be6350f41005bf7250f4143f3f5250f41015be7150f41015bc7150f4101cff7658b411257e7558b410067e6558b410067d6558b410aeec6258b41004ff7558b41024fe7558b410067e7558b410247e7558b41004fd7558b410067d7558b41024fc7558b41014fc7458b41004ff7358b41074fc7358b4111e7f5258b410aeef4258b410aeec4258b4111eec3258b41166ef2158b41004ff7058b4100cfe7058b4100cfc7058b4111eef2058b410057f7654b410067f7654b410047f7654b410067e7654b410057d7654b410067d7654b410047d7654b410067c7654b411967e6454b410067e6354b410067d6354b410073f4354b410073d4354b414057f7254b411276f7254b4101e7e6254b4111e7d6254b4101e7c6254b411967d6154b411973e4154b41197764154b411973c4154b4118e7e6054b4118e7c6054b41015bd76d0b4101ebd76d0b41014bd76d0b410af3e65d0b410af3d65d0b41005bd73d0b41006be63d0b4101ebe62d0b410afae62d0b410afad62d0b4101ebc62d0b4111f3f52d0b4111f3d52d0b41015be71d0b410afb671d0b410afb571d0b41015bc71d0b413dcff7650b4116e7e6550b410067d6550b413ddbf7650b413d6bf7650b414373e6550b410073d6550b41005bf7350b41006be6350b410afaf7250b4101ebe6250b4101ebc6250b4111f3f5250b4111f3d5250b41015be7150b41015bc7150b4111faf2050b41074ff76ccb410acfe76ccb41004fd76ccb411567e65ccb410067d65ccb410adbe74ccb41005bd74ccb410079f43ccb4101eee62ccb41006ed62ccb41004ff764cb41004fd764cb410acfc764cb4113e7e654cb410067d654cb410adbe744cb41005bd744cb410079f434cb41005f7714cb41015f4714cb4100cff76583410067e65583410067d65583410aef86058341004ff7558341024fe7558341004fd7558341024f
  | 20 => 0x1dcfd7650d3201cfc7650d320057f7550d3213d7c7550d32006bf6450d32006bc6450d32005ef7250d3201dec7250d321dfcc3250d321fcfe7610d3213d7e7510d320057d7510d320aebe6410d32006bd6410d320079d4310d321fdde7610d32006de7610d324575e7510d320075d7510d32215de7410d320079e7410d32006df6410d320079e6410d32006dd6410d320079d6410d3201dde7210d3201ddc7210d32076df6210d321af5f5210d321af5d5210d321af9f4210d321af9d4210d32005dd7110d321afcf2110d32005dd7010d3201dee73cc93201fce73cc93201eef63cc93201fcf63cc932007cf43cc932077cc43cc932005ed71cc932014fe76d8532136f661d8532004ff75d8532024fe75d8532004fd75d8532024fc75d85320acfe74d8532004fd74d853201cfd73d85320ee7f52d85320ee7d52d8532006f751d8532136f451d8532136f441d8532136f631d8532136f621d853200cfe70d8532004fd70d853200cfc70d8532136f710d85320057f755853213d7c7558532136f4615853200cfe76d813213d7e75d81320057d75d813212efa60d8132004ff75d8132024fe75d81320067e75d81320247e75d8132004fd75d81320067d75d81320047d75d8132024fc75d81320acfe74d8132004fd74d813201cfd73d813206e7f52d813206e7d52d8132014fe71d8132004fd71d8132014fc71d813212ef840d813212efa30d813212efa20d813212ef860581320ad7f76597411267f76597410247f76597410ae7f63597410ae7c63597410057f72597410ae7f62597410067e62597410ae7c625974144f3e41597410af7641597410af3c41597410ae7f60597410067e60597410ae7c60597411267f74597410ae7e745974144e7d74597410ae7c74597410067f73597410067e73597410067d73597410067c73597410ae7f43597410ae7c43597410067f72597410047f72597410067e72597410067d72597410067c72597410ae7f42597410067e42597410ae7c42597410067e32597410067c325974144e7f715974144e7e715974144e7d715974144e7c71597410ae7f415974144e7e415974144e7d41597410ae7c415974144e7f315974144e7e315974144e7d315974144e7c315974144e7f215974144e7e215974144e7d215974144e7c21597410067f70597410067e70597410067d70597410067c70597410ae7f40597410067e40597410ae7c40597410067e30597410067c30597410067f20597410067e20597410067c205974144e7f105974144e7e105974144e7d105974144e7c10597410067e6598f410067d6598f410aedf6398f41074ff7598f41024fe7598f41004fd7598f41074fc7598f41014fe7498f41076be7498f410aedf4398f41076dc4398f4101cfe7298f41004fd7298f4101cfc7298f410067f529
  | 21 => 0xd7010f32014ff76587320057f75587321557c7558732076f46158732004ff75587320067f75587320047f7558732024fe7558732004fd7558732024fc75587320067c75587320247c7558732004ff74587320acfc745873201cfc73587320d67f52587320d67d52587320d6ee3258732076f73158732076f4315873214ef62158732004ff705873200cfe705873200cfc705873200cff7658332076f86058332004ff7558332024fe7558332004fd7558332024fc7558332004ff74583320acfc745833201cfc73583320567f52583320567d5258332004ff7158332014fe7158332014fc7158332076fb3058332076f83058332146fa2058332146fa1058332004ff75d9132024fe75d9132004fd75d9132024fc75d91321fedd73d9132074ff72d91321fcfd72d91321fe7f52d91321fe7d52d91321febf42d91321febd42d9132014fe71d9132004fd71d9132014fc71d913200cfe70d9132004fd70d913200cfc70d9132006bf64991321dddd73991320acff7599132024fe7599132004fd75991320acfc75991320acfe74991321dcfd73991320aedd7399132214fd72991320aeed72991322167f52991322167d5299132014fe7199132004fd7199132014fc719913200cfe7099132004fd709913200cfc70991320057f755913213d7c7559132215df7359132005f77159132135f47159132005fb705913212df87059132004ff75591320067f75591320047f7559132024fe7559132004fd7559132024fc75591320067c75591320247c7559132006bf7459132214ff7359132006df73591321dcff7259132006ef72591321de7f52591321de7d5259132004ff7159132006f77159132004f77159132014fe7159132014fc7159132006f47159132014f47159132004ff7059132006fb7059132004fb705913200cfe705913200cfc7059132006f8705913200cf870591321fcfe761913213d7e75191320057d7519132006bd64191320acff7519132024fe75191320ae7e75191320247e7519132004fd75191320ae7d75191320047d75191320acfc75191320aebe7419132074ff72191321acfd72191321ae7f52191321ae7d52191320aebf42191321aebd4219132014fe7119132004fd7119132014fc711913200cfe7019132004fd701913200cfc701913201cfe76d0d3201cfc76d0d32006bf64d0d320aebc64d0d3201dee72d0d32005ed72d0d3201dde76d0d32216de76d0d3201cde76d0d32006df64d0d320079f64d0d32006dd64d0d320079c64d0d3201dde72d0d32217ce72d0d3201dce72d0d32007cd72d0d3201ddc72d0d32216df62d0d322175f52d0d322175d52d0d32005dd71d0d32217cf21d0d32005dd70d0d321acfe7690d32006be6490d32006bd6490d321adde7390d32077cc3290d320acff7650d3201cfe7650d32
  | 22 => 0x85420057d75d8542166f661d8542004ff75d8542024fe75d85420067e75d85420247e75d8542004fd75d85420067d75d85420047d75d8542024fc75d854201cfd74d8542074fe73d8542004fd73d854211e7f52d854211e7d52d8542166f641d8542166f431d8542166f621d854200cfe70d8542004fd70d854200cfc70d8542166f4615854200cfe76d814215efa60d8142004ff75d8142024fe75d8142004fd75d8142024fc75d814201cfd74d8142074fe73d8142004fd73d81420a67f52d81420a67d52d8142014fe71d8142004fd71d8142014fc71d8142006fb50d814215ef850d814215efa40d814215ef830d814215efa20d814215efa10d81420057f755814216d7c755814215ef86058142074ff75d9332024fe75d9332004fd75d9332074fc75d9332074fe73d9332076de73d9332076ed72d93321fe7f52d93321fe7d52d9332014fe71d9332004fd71d9332014fc71d933200cfe70d9332004fd70d933200cfc70d93321dcfd7699332076bf64993320acff7599332024fe7599332004fd75993320acfc75993320aebe5499332006bd549933201cfe739933201cfc7399332076be4399332076bc43993322167f52993322167d52993320aebf4299332216bd4299332014fe7199332004fd7199332014fc719933200cfe7099332004fd709933200cfc7099332006be40993320aebc40993320057f75593321557c7559332076bc6459332004ff75593320067f75593320047f7559332024fe7559332004fd7559332024fc75593320067c75593320247c7559332076bf7459332006be5459332006bd545933201cfe735933201cfc73593321dedc7359332076be4359332076bc43593321de7f52593321de7d52593321debf42593321debd4259332004ff7159332014fe7159332014fc7159332004ff705933200cfe705933200cfc7059332006be4059332006bc4059332074ff7519332024fe75193320767e75193320247e7519332004fd75193320767d75193320047d7519332074fc75193320acfe7419332076be7419332074fe7319332076de7319332076ed72193321ae7f52193321ae7d5219332014fe7119332004fd7119332014fc711933200cfe7019332004fd701933200cfc70193321dcfd76d0f321dddd76d0f32006dd76d0f32006df64d0f32006dd64d0f3201dde72d0f3201ddc72d0f322175f52d0f322175d52d0f32005dd71d0f32005dd70d0f32214ff7650f320057f7550f321557c7550f320779c4350f3201ddd7610f32076dd7610f3201cdd7610f320775e7510f320775d7510f320779e7410f32076df6410f320779e6410f32006dd6410f320779d6410f3201dde7210f32077ce7210f32077cd7210f3201ddc7210f321af5f5210f321af5d5210f321af9f4210f321af9d4210f32005dd7110f32005d
  | 23 => 0x1ff3d5290f42005bd7190f42005bd7090f421fcff7650f420057f7550f421857c7550f420af9c4350f4201dbd7610f420aebd7610f4201cbd7610f420af3e7510f420af3d7510f420af9e7310f420af9e6310f42006bd6310f420af9d6310f4201dbe7210f420afae7210f420afad7210f4201dbc7210f421af3f5210f421af3d5210f42005bd7110f42005bd7010f42014ff76587420aef46158742004ff7558742024fe7558742004fd7558742024fc755874201cfc7458742004ff7358742074fc73587421067f52587421067d52587420aef741587420aef4415874217ef62158742004ff705874200cfe705874200cfc705874217ef7105874200cff76583420057f75583421857c75583420aef86058342004ff75583420067f75583420047f7558342024fe7558342004fd7558342024fc75583420067c75583420247c755834201cfc7458342004ff7358342074fc735834208e7f525834208e7d525834208eee4258342004ff7158342014fe7158342014fc71583420aefb40583420aef84058342176fa2058342004ff75d8d42024fe75d8d42004fd75d8d42024fc75d8d42216bd74d8d422167f52d8d422167d52d8d42216df32d8d42014fe71d8d42004fd71d8d42014fc71d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006df6398d420057f7558d4216d7c7558d42005f77158d42165f47158d42005fb7058d4215df87058d4216d7e7518d420057d7518d42006dd6318d42074ff7518d42024fe7518d420767e7518d420247e7518d42004fd7518d420767d7518d420047d7518d42074fc7518d421ae7f5218d421ae7d5218d42076df3218d421aedd3218d42014fe7118d42004fd7118d42014fc7118d4200cfe7018d42004fd7018d4200cfc7018d421acfe76d0d420afac42d0d4201cfe7690d42006df6390d42076dc6390d4201dee7290d42005ed7290d4201dbe7690d421febe7690d4201cbe7690d421adbe7390d42006bf6390d420079f6390d420079c6390d4201dbe7290d421ffae7290d4201dae7290d42007ad7290d4201dbc7290d421febf6290d421ff3f5290d421ff3d5290d42005bd7190d42005bd7090d421ffaf2090d4201cfc7650d420057f7550d4216d7c7550d42006df6350d42006dc6350d42005ef7250d4201dec7250d421dfac4250d42214fe7610d4216d7e7510d420057d7510d420079d4310d42215be7610d42006be7610d4245f3e7510d420073d7510d421fdbe7310d420079e7310d42006bf6310d420079e6310d420079d6310d4201dbe7210d4201dbc7210d420aebf6210d421af3f5210d421af3d5210d42005bd7110d42005bd7010d421afaf2010d4201dee74d094201fae74d094201eef64d094201faf64d0942007ae43d09420afac43d0942005ed70d0942014fe76d854216d7e75d
  | 24 => 0xc7110d5218d7e7010d520057d7010d5218d7c7010d521957e76d85520057e74d85520057d74d85520067e64d85520067c64d85520057e73d85520057d73d85520067f63d85520067d63d85520257f72d855201d7e72d85520257d72d855201d7c72d85524967f62d855249f6f62d85521957d71d85521967e61d85521977661d85521967661d85521967c61d85521977431d85521977621d85524977521d855218d7e70d85520057d70d855218d7c70d85521957f76585520057f74585520057c74585520067e64585520067c64585520057f73585520075f73585520055f73585520057c73585520075c73585520055c73585520067f63585520067d63585524857f72585520076f725855248d6f72585524867f62585520c76f62585521957f71585520077761585521967e61585521967c61585521977461585520057f705855218d7e705855218d7c705855219777105855218d7e76d81520057e74d81520057d74d81520067f64d81520067d64d81520057e73d81520057d73d81520067e63d81520067c63d81520257f72d815201d7e72d81520257d72d815201d7c72d81524767f62d815247f6f62d81521957e71d81520057d71d81521957c71d81520067f61d81520067d61d815218d7d70d815218e7e60d815218f7a60d815218e7a60d815218e7c60d815218f7840d815218f7a20d81524777920d815218d7f76581520057f74581520073f74581520053f74581520057c74581520073c74581520053c74581520067f64581520067d64581520057f73581520057c73581520067e63581520067c63581524657f72581520076f725815246d6f72581524667f62581520476f62581520057f71581521957e71581521957c71581520067f61581520067d615815218d7f70581520077b605815218e7e605815218e7c605815218f78605815218f7a10581520aedf6398f42074ff7598f42024fe7598f42004fd7598f42074fc7598f4201cfe7498f42076de5398f42006dd5398f420aedf4398f42076dc4398f421fe7f5298f421fe7d5298f42076df3298f421fedd3298f42014fe7198f42004fd7198f42014fc7198f42006de3198f42076dc3198f4200cfe7098f42004fd7098f4200cfc7098f420057f7558f421857c7558f420aedc6358f42004ff7558f420067f7558f420047f7558f42024fe7558f42004fd7558f42024fc7558f420067c7558f420247c7558f4201cfc7458f421debc7458f42006de5358f42006dd5358f420aedf4358f420aedc4358f421de7f5258f421de7d5258f421dedf3258f42004ff7158f42014fe7158f42014fc7158f42006de3158f42006dc3158f42004ff7058f4200cfe7058f4200cfc7058f421dcfd7690f421ddbd7690f42006bd7690f42006bd6390f4201dbe7290f4201dbc7290f421ff3f5290f42
  | 25 => 0x8d524cf6f62d8d524bf5f32d8d524bf5d32d8d521957e71d8d520057d71d8d521957c71d8d520075e31d8d520075c31d8d5218d7e70d8d520057d70d8d5218d7c70d8d520067e60d8d520067c60d8d524c57d7698d520057e7498d520057d7498d520067e6498d520067c6498d524a57e7398d520067f6398d520075f6398d520065f6398d524b57d7298d520076d7298d5213d6d7298d524b67f6298d521576f6298d521957e7198d520057d7198d521957c7198d520067e6198d520067c6198d5218d7e7098d520057d7098d5218d7c7098d520057f7458d520057c7458d520067f6458d520067d6458d520075f6358d520067e6358d524c57f7258d520076f7258d521556f7258d524c67f6258d5213f6f6258d520057f7158d52007777158d52005777158d521957e7158d521957c7158d52007747158d52195747158d520057f7058d5218d7e7058d5218d7c7058d520067e6058d520067c6058d524bd7e7618d520057e7418d520057d7418d520067e6418d520067c6418d524b57e7318d520067f6318d520075e6318d520067d6318d520075d6318d520257f7218d5201d7e7218d520257d7218d5201d7c7218d524a67f6218d524af6f6218d524a75f3218d524a75d3218d521957e7118d520057d7118d521957c7118d520067e6118d520067c6118d520075e3118d520075c3118d5218d7e7018d520057d7018d5218d7c7018d520057f76d0d520057e76d0d520057d76d0d520057c76d0d5201d7e72d0d522176e72d0d5201d6e72d0d522157d72d0d520076d72d0d520056d72d0d5201d7c72d0d522167f62d0d521c76f62d0d521957e71d0d520057d71d0d521957c71d0d5218d7e70d0d520057d70d0d5218d7c70d0d520057f7690d520057e7690d520057d7690d520057c7690d521dd7d7490d521ad7e7390d520073f4390d520075f4390d5201d7e7290d521ff6e7290d5201d6e7290d521fd7d7290d520076d7290d520056d7290d5201d7c7290d521fe7f6290d521bf6f6290d521957e7190d520057d7190d521957c7190d5218d7e7090d520057d7090d5218d7c7090d520057f7650d520067f7650d520047f7650d520057e7650d520057d7650d520057c7650d520067c7650d520047c7650d520075f4350d520073e4350d521dd7f7250d5201d7e7250d5201d7c7250d521de7f6250d521e76f6250d520057f7150d521957e7150d521957c7150d520057f7050d5218d7e7050d5218d7c7050d520057f7610d520057e7610d520067e7610d520047e7610d520057d7610d520067d7610d520047d7610d520057c7610d522157e7410d521fd7e7310d520073f4310d520075e4310d520073d4310d520075d4310d5201d7e7210d521ad7d7210d5201d7c7210d521ae7f6210d521b76f6210d521957e7110d520057d7110d521957
  | 26 => 0x75df7450c430779f7450c430aede6450c430af9e6450c430af9e5450c435079d5450c43005df7250c435075f5250c4301cff76588431b57e75588430067e65588430067d6558843076ec6258843004ff7558843024fe75588430067e75588430247e7558843004fd75588430067d7558843024fc75588431ae7f52588430aeef42588430aeec4258843076ef3258843076ec3258843004ff7158843014fe7158843014fc71588431aeef2158843004ff705884300cfe705884300cfc70588431aeef2058843014ff76584430067e65584430067d6558443076f46158443004ff7558443024fe7558443004fd7558443024fc7558443006bf4358443006bd4358443004ff725844301cfe725844301cfc72584430067f52584430aef741584430aef44158443076f73158443076f431584431a6f62158443004ff705844300cfe705844300cfc70584431a6f7105844300cff76580430067e65580430067d6558043076f86058043004ff7558043024fe7558043004fd7558043024fc7558043006de4358043006dd4358043004ff725804301cfe725804301cfc72580430067f5258043004ff7158043014fe7158043014fc71580430aefb40580430aef84058043076fb3058043076f8305804319efa205804319efa10580430057e73d91520057d73d91520257f72d91520257d72d91524ee7f62d91524ff6f62d91524ef3f42d91524ef3d42d91521957e71d91520057d71d91521957c71d91520067e61d91520067c61d915218d7e70d91520057d70d915218d7c70d91520073e40d91520073c40d91524f57d76991524d57e74991520067f64991520073f64991520063f64991520057e73991520057d73991524e57d72991520076d729915216d6d72991524e67f62991521876f62991521957e71991520057d71991521957c719915218d7e70991520057d709915218d7c70991520067e60991520067c60991520073f64591520067e64591520057f73591520057c73591524f57f72591520076f72591521856f72591524f67f625915216f6f62591520057f71591521957e71591521957c71591520067e61591520067c61591520057f70591520077b70591520057b705915218d7e705915218d7c705915200778705915218d7870591524ed7e76191524e57e74191520067f64191520073e64191520067d64191520073d64191520057e73191520057d73191520257f721915201d7e72191520257d721915201d7c72191524d67f62191524df6f62191524d73f42191524d73d42191521957e71191520057d71191521957c711915218d7e70191520057d701915218d7c70191520067e60191520067c60191520073e40191520073c40191520057e74d8d520057d74d8d520067f64d8d520067d64d8d520257f72d8d520257d72d8d524be7f62d
  | 27 => 0xe43d89431de7f52d89431deee42d89431deee32d8943014fe71d8943004fd71d8943014fc71d894300cfe70d8943004fd70d894300cfc70d89430057f75589431e57c75589430067f65589430067c65589431deec6258943005f771589431d5f47158943005fb70589431cdf87058943014fe76d85430067f65d85430067c65d85431d6f661d8543004ff75d8543024fe75d8543004fd75d8543024fc75d854301cfe72d8543004fd72d854301cfc72d85430067f52d85431d6f641d85431d6f631d8543006f721d85431d6f421d854300cfe70d8543004fd70d854300cfc70d85431d6f710d85430057f75585431e57c75585430067f65585430067c65585431d6f4615854300cfe76d81430067f65d81430067c65d81431cefa60d8143004ff75d8143024fe75d8143004fd75d8143024fc75d814301cfe72d8143004fd72d814301cfc72d81430067f52d8143014fe71d8143004fd71d8143014fc71d81431cefa40d81431cefa30d8143006fb20d81431cef820d81431cefa10d81430057f75581431e57c75581430067f65581430067c65581431cef860581430757f76594431b67f76594430247f76594430057f72594430767f62594430067e62594430767c62594430767f61594430067e61594430767c61594430767f60594430067e60594430767c60594431b67f74594430ae7e74594431b67d74594430ae7c74594431b67f73594430767e73594431b67d73594430767c73594430ae7f43594430767e43594430767c43594430067f72594430047f72594430067e72594430067d72594430067c72594430ae7f42594430067e42594430ae7c42594430767f32594430067e32594430767c32594430067f71594430067e71594430067d71594430067c71594430ae7f41594430067e41594430ae7c41594430767f31594430067e31594430767c31594430067f21594430067e21594430067c21594430067f70594430067e70594430067d70594430067c70594430ae7f40594430067e40594430ae7c40594430767f30594430067e30594430767c30594430067f20594430067e20594430067c20594430067f10594430067e10594430067c10594430773e65d0c430773d65d0c43075bd73d0c43076be63d0c43005bd72d0c435173f52d0c430775e6590c430775d6590c430addd7490c430aede6490c430779e6490c43005dd7290c4350f5f5290c43004ff7650c430057f7550c431b57c7550c431e67e6550c430067d6550c43075bf7650c43006bf7650c43004bf7650c430073f7550c435073c7550c430773e6550c430773d6550c43075bf7350c43076be6350c430779e5350c435079d5350c43005bf7250c435073f5250c430addf7650c43006df7650c43004df7650c430075f7550c435075c7550c430af5e6550c430af5d6550c43
  | 28 => 0x83430067f75583430047f7558343024fe7558343004fd7558343024fc75583430067c75583430247c7558343004ff725834301cfe725834301cfc72583430067f5258343004ff7158343014fe7158343014fc71583430aefb40583430aef84058343206fa3058343075bd76d0e43006bd76d0e430779e53d0e4352f9d53d0e43005bd72d0e4352f3f52d0e43005dd76d0e430aedd76d0e430af9e54d0e4352f9d54d0e4352f5f52d0e43005dd70d0e4301cff7658a43076ec6258a43004ff7558a43024fe7558a43004fd7558a43024fc7558a43006df4358a431fe7f5258a431feee5258a43006ed5258a431feee4258a43076ef3258a43076ec3258a43004ff7158a43014fe7158a43014fc7158a431feef2158a43004ff7058a4300cfe7058a4300cfc7058a43006ee2058a431feec2058a43014ff76586430057f75586431bd7c7558643076f46158643004ff75586430067f75586430047f7558643024fe7558643004fd7558643024fc75586430067c75586430247c7558643006bf4358643004ff725864301cfe725864301cfc72586430067f52586431f6f64158643076f73158643076f43158643004ff705864300cfe705864300cfc705864300cff7658243076f86058243004ff7558243024fe7558243004fd7558243024fc7558243004ff725824301cfe725824301cfc72582430067f5258243004ff7158243014fe7158243014fc71582431eefa4058243076fb3058243076f830582431eefa10582431e57e76d95431e67e76d95430247e76d95430057d72d95430067e62d95430067c62d95430067e61d95430067c61d95430067e60d95430067c60d95430067f74d95431e67e74d95431e67d74d95431e67c74d95430067f73d95431e67e73d95431e67d73d95431e67c73d95431e67d43d95430067f72d95430067e72d95430067d72d95430047d72d95430067c72d95430067e42d95430067c42d95430067e32d95430067c32d95430067f71d95430067e71d95430067d71d95430067c71d95430067e41d95430067c41d95430067e31d95430067c31d95430067f21d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95430067e40d95430067c40d95430067e30d95430067c30d95430067f20d95430067e20d95430067c20d95430067f10d95430067e10d95430067c10d95430067f65d0d431c67c65d0d430075f65d0d435275c65d0d435275f52d0d43005dd70d0d430067f6590d431be7c6590d430073f6590d4351f3c6590d430079f6390d4351f3f5290d43005bd7190d4301cfe76d89431e57c75d89430067f65d89430067c65d89431deee62d8943004ff75d89430067f75d8943024fe75d8943004fd75d8943024fc75d89430067c75d89430247c75d8943006df43d8943006b
  | 29 => 0x801004800d00000080000060030078000006000002801000000e800400400000080d40020020018024000000000800000000800000280020100028000012000000000000c03000680100040070010018042014000000c008000000002c000003003804400401a0020024004001000000c0000080010004050001002000800200b0008000002003000800001a00100280b401002d00b005400203e000800402a0060020004012001000000800e001001801401a004006800000400b006802c000000000008800000000000040240020038008002006000800c014004000000000a00300f80080000000050000006000006002c03400200880000000020148000004008008007400400a000000000400900f805400e001002800000000300d800000201000980040020010028008014001002000000000400380080020090038000004002000801003000100000040020020028038000000000808402e00100400040080010010000006004000801800a010008800000a0050008000000002000001c064003000000c002000002803402e000000000000e00200a803800400500c801c0040000010020000009002000801a005003001c00600000e8038002000001002c000001005800801e00a0040000006000000800000400000000000000170000028002000000802c0060040028020000000001000800e00900880000020000080000004027000000c00a00200900000220000000004004000000000c0120080008000000005000001c00000500e005000600200b000c00601000b800c0140060048000000002003806401000400b0038018003000801c000014005801c004006001000801801f0058018060009000000000000100100040020000030044010004007002c00a00900500100020060008028000001000000000200b00d800002a004000800001e000001803400c0060038000002003005002000e0050018008000015000003c00a001001000000a00b00300140020010000004008001001800c0040000018004002006006002400e0000000014010003000000000200101cff7658b430aeec6258b43004ff7558b43024fe7558b43004fd7558b43024fc7558b432167f5258b43216ee5258b43006ed5258b430aeef4258b430aeec4258b43216ee3258b43004ff7158b43014fe7158b43014fc7158b43006ee2158b43216ec2158b43004ff7058b4300cfe7058b4300cfc7058b43216ef2058b43014ff76587430aef46158743004ff7558743024fe7558743004fd7558743024fc7558743004ff725874301cfe725874301cfc72587430067f52587430aef741587430aef4415874320ef63158743004ff705874300cfe705874300cfc705874320ef7105874300cff76583430057f75583431c57c75583430aef86058343004ff755
  | 30 => 0x6800000100b001000001200680040180170058000000000000006c00200e000000001e006000000c010006001000000801600b001c01000000b800c010002000800400602000000100400070010004002015001000800c00000180680180040048014000002001800000c0020000008002006000800001600300000300000000000004008006008800c002000004800800200000000000080000050008006001007000000600a000001c00c001006001801a007004800000200200000000160000050020022000001802c000000013000001a0000060000008010005801800e0110010000000035003001c00000100c8008008002000000000c00000800000200010088008000008003002c006001000001c016000000801c0020130088020004003003003800c017000001800c004007006000000700080080000090060010008001003800401c00b0028020030004003800c01200a00000100020000030024000003000001400000000080000040000000004024000004802400000a001000000c000000000c0000070048014000003005803000600100000a00040100020028032016000000c00e002008001402a00000000040000000008044028007001001c000025000800400e000004000401c000001800800201a000001c000000000000001e00001600000000010058008004002000000400000f003006804000200480040020040080000008000000000800a000001000c006004003800800a00300a0018000000000800000e00e0060000008002000800c00600000100700000080010024004001000800000400100000400560010010004008000000802400a0050008028000004002801400c017006000801000700000000040000058014014004002007c000004000000000000b0010004010002003006000200f002000400c018002004400c004005001800200100000000140030020008002008001003800800300000240160000098000016000002001000000200080180000010000008018000000000c00600500080000080010028008002000000001000000b0030000008000000000800002e00100000000050000008000002004800400600d003000000e00600a0000004000002000001e000000800400400a000004000e0190040000000006001800c00c00100000380220000000000004000003004801600000000000000110018010012000000000000400e001009c0000020018034006000001003003c017003002401000f003805000a00c000000000200000a801000a005001804c00200000000000000010018010002006000000001600e000800c0000020038034016012001801400800b005000003800000080140080020000028000001000800000200301080000020030060000000007000801400002800200100200
  | 31 => 0x430000000000000008000674800035c0000183124c9919cb45f71cf0269800013b9640487156839f99644891580674140820523de16721be00000005e39cb00d2027086694384bb9ae207c04424998080615a3f0000152617e1bc485810dc2b4a33e1a080aa12e800000000003c8849200100140200070018020018001000000c00a000001000000a00c003801800a0020020004002002000003800000f00b000400200700800280020000010010004001002801c00402c00000040140190000028000000005000000a012000000c00000000080100100220000000002004000000c00201b005003c006000004000401200b001000400000400e8020008001000800000400200300500020020010014006004000002000a00500080480020000008000016001000001c008007002000001601c001800800600200000040000010000020002000005800001c000000004000400f0018000056009003807401e002001000000800000b80000000040000004000001002000000000d000005400e00000480000000040000004000003001001000200000080ac016009001801000c00d001800000c000002800400200200d006002401200c8008008006006000000400e0000000006003000003000000d000800c01e034000001c00a002002000003c0010070000002000000800c0000000058018002000000000002a0060048000000000002001400c0000048024000009000807406200000280080000000000004068000000007c02e004001002404e022007801002e01500180040000050030000004000000000800600000500000020170000000008003000000000200e004800800600a001006c0200270000010006000009800000a00c000000400a01400180400000000050004014001008800c00a0000008000016001002002000200900b000c0000010000000006006000800800001a006006c00000100000380140020018018008004000005800000200000640000020030014028007001001400e00000000480000260000020028001000806000e001000000c00600200700100060000000000002001000000401000800080440120030020020000013002000002e000000000000800500000080420010010004000000006000001c0040078034000000002800c0040010000004002003001000801000f000000402c0000018014000004001001800a002003805401000d002002c01e007003800003200a002000001400100100f400200000680180140000008018002018000802801c01a00200100060000000014000000000000c00400300400140060000008018008009000000800c00d000801c0080010010078006001005001000a0030048000000000005000800000000000100440000000080006000003000000e000001000000000000e0
  | 32 => 0x9b2a000000000001801478cde0000000000186409786000001e9e49214a40002014766923809f86bc9699eba079031c00002e891d9d501b61ad4000103279e0b6690e80000000000357870e90397d000006c400000000001ac800000004fb06dc23d18040d18fd04cb89c82788000000000082712f80c600006211076488883658f98cc1d1084e00004440001a9452e08cc747099e4b302c27061f8a544985086880000000e3299b1d648b205969ad1d380968e5a97a8eee96c02505c79706000000017f134a39e00000000aae446949e8ae0f1e09a000096e01fe6b2800084880000000000000000000000002f6080e95b06c063697ce6bba1f0000157a5d91cfe9700000000069c01e045657d9a366b39f427c28f5e51e00002d9007e8038d3a19c1a2433183d813a000059c101c39400000000cbc0a71d06438913e00000003e29dee8f300001712182026873478f00005e611bc98d832429b09520ca80002a424cc7732128000000080f04529201cf47d31b108ab0f7e36ea3b46da9bde6150be82041bb88328fc813813489068000000000000009f00000e3076983aa9b426589751c0063123a68c9847604b1bba14e07001d70be210c8cf4000242a07394b200019c020c8a9c1600db215411fe86d163a3428acc47b20ea3ec11a410003768b80a307dd16243a38bca212828e799934620ba6c28658992000000066209c62b8078e3ae00005808e4600000006ab9d28210a27452a1f826908f5c027035c00023ee4e499c800010c62570f5a8b186ae11f25e0000098e6d700006af8f1a0000000000000079500003ab25d00d69c225850000370800038300001ef1356000089e32504ac07f1952293081e84d241471f800025981aa0001dde00001220000a9a000235a0000a7a00000000002142000117600024a418080002f380003539c9e7d9800092e84fc784a2d68a29d9c0c4185a4112032000000094a9b3248f16f40002694982124461e0c0096a127e5981b306659dba56e901a20118284119eaa0000ad06208000000124042e963235624fc800087a86b80448c0992834d0f10050006800ca1c87a68be497780008c39afc24c9d6c74106287b701c285581664a1811e43b03f839103b00ad021445a26626711fa212e136874e82528079b742d1a53a94007b66460e586e2200a319204653e1cea2eb1c9677d90427310902606800019393204608bbc2a8a0e68429e1822594e012007800109412841800032001d270203001c618909329ffc613a2981241650000000083d14980001eac5f91ede3b39ef200000000438a2088080000001c62014000000000000000000000000030d800060000005d200000000af855c00008db000032412ec000029882e97fc236979e00024dc07400000000f0400d818a00000003c5800000000000000510
  | 33 => 0x64a7a1aa86312fe0e924467ba0f5215fa1801f41e9c49e1b7264e1e580000a6a30411dc0000e1e89192707db800000019a800000002ac9784000010a00016e04e900007c825503c5000000025c401e8f4000016fc17c0000000000000005c200019e60001b8090f8000302a0be7a380006699f0600015cc6d480003a080007118000000000089280008141cc000011746438000666124a00000006d690fa0000ef618680000001dd00000c6c000000000000003c19f2865f959a32c080224616e200021445241b4e7d80f748f21eb23bf800016426f81610fd639c171c8d419a291497a40c6865a921000097a00000580e741ac893400026ec000000088800001101bf400e9b221a6000076613f84a384e668b012e84f0c7426d80c85ae1e8a8ef1a56567a17020ea02e1cc99c21d5840e3f610ca1e48aa422401486d998885fa131a9160a9657a122c6a4a1d27a113b4910161a8d005ac6d621ec3de99b8268032800000005f1831693f941c1fe90ce3a780008d70234984955a99580000001ac64de19f23e194a61cea5c66e196b095d842e29712166de97fe0ae15dc5aa266e8569f62000191c9689cc80001efe04714e449d83ee54923f27078000316237a3bc81a07fb00e640092b0891256e0bd1a229268abe000000030c8164519838c73087049bc9d5c65a850a83491421551bf25459f765df00009470ad47e48c682c180004cd80000d8a4bc00021f67b30000000000023d800045217e6000162a000000002e9a4488b04027be800015615a27949f8413780002f100001d406465f280902cd00002ae8000000087016d902e96613a0116926e6d082440001906000124237498023f523061179ff48e700000001dac0350fb85ba250e47c942695680004bc0f4688926280000fb4843800028496aa91218140e20f88000245e343048438f81ee42fa4ce49a874a2031dc61c280004f4016a7c00398253000023a00007280ac4000226a3b002422b08d5a1848000000038400011ac28f871e1e280005ad88ce57f8eec3cd9ff81450c8426c1694513852275e8bee9828ce28728c9c5da948001487f08c2a14e78922920dba25a7ee1f2c6950b9a7f1978c901963c335102017d26225389c0a3dc937413e1b043e4872869f92de1a297f83aa96c83cf01f42511ba6629997876c8a269b880000ce265c8f697f686b18b290224a84b407dc0001dce00002024681e2e98b0fa200007ac4959b0000012881cf83ea0001f8000015e200017d840c20fc00026cc00017263ed8b8e0081f0e145800071203040000cd6000132c42d112635c972c79720381f2262078d883406121142219f408bb1598412851a3b706ee705130a01511106ef86143739bb45b923f63a48566150a6e633682ce5e4915e3401c6e809233097625802c69ee481c13fa8f614ac293
  | 34 => 0xd14b41499a405608cc2339a59a8bb9e167c41b845fb19946998d8e89c853603c179c5a41060066092e43783f042400e84ad23366770d9e546151a58290e406e87f80001ab000010ac18f83c615817028d213f20bf17383468696000000002d800098b80000000000000254e00000000002232653a24e2998f125339600531877c42e12307d1958444b800008b00000000fa62c382fe00001be000000020b26186e8114694f9ca826511da770951c5120bba81080006ba1cee41c84980361e942c480be1309588000075a2d8975670d12a0569800053a9aaa19b1062000070c8da80009af88ca81924b072c800050d05a86881f962488a50899093a231a09294d841c945068073991f883e21e4906216460725566f70d8c55004248fa9ef089007fe8761af8504030e59f18228818a0868b80000578df67701ed45e0885e0780f4850b000078a0860611000028e185879d800000023180970be000000000d4000000019e8000144476200006e618fc37780006248e9c00009fc4f28a2e755a4107f2043c0001b4c5bd9b0c000117c5c399425159d6a00022b60358ff04c6260c4b20a585b421fe835a38c0001cca552132665b08c06021caa1c51e4a0000000000000000018704061f4800018f0260800092a800025000ae44180001cb86e849500000f1213800016380001ae000000002df22ba0001b681b18b84416a0b6021086e65418c0707186c845a6d497317ee1db996000020e072d8ef02ce000001a85401331c440000cfe0001d025b6000013d800074d1c364c8940a5e187123861e3e00026380e005320000980000000086e08aa33c82e20000000000094872b0000000000000007e26ff038a6a31cd60481758501000090c0000000250c701090a52194dc2861a7c88499ee80301ea51c00000a98b76000000086495b462d14282f0a58448c89686f4011a00026b0000088a6a180007de80004a09fcc056926000000004ae98405c822d40001a3c31f0000652236054f800015f000644700ee64492d6465156a15b000051680009b22162072865000c11c69080b4e0000c602e5061c00016bc0000d5c6a208a6288949464507a800000000001fa61a8920a60aa5649088000721028200000002db9d540000a9400000000001ae4000245c46b8000248000038b80000000aee00000009b692808a4000000000008098dd883624664ec06226bb0f9a8e113c06829a70000120c38687a28d5800000004220001e0a53e871a47f00008ac1e7c927800022b9ade8530ac831785da0001ef6000030a44f00405cb80000001d789ae23fa000000000003f400019707391fe2000000011900006230000000000000012520001f1c5a90b4c5dd25fc1900d62673074c9b58bd688f1666466232400023b09360bfa9048000000184c012000072e89e676388d
  | 35 => 0xc255fa52846884a44c4000007180d000000000002148680800000000000000eda6971e4448fa2143e6260697924548e8143e7ce8c080000000029a6de23500001b5090e270038615b800010693240188a8a00006263ba8d2230996283a18ef819d0d2660c194c5419c0e109883e59788a865007d486612745441eb66c086b07331f7e000058e5e400006e695fa85293ae95115282fd90f864313625bb0aa029897b606d851241b00008b900006791038297800058ba40411b924e3260784478800044e92aa00006ce0000f2e6040bf23da0d5670f80fe13c06fe859a57c4cf123a1e219f84248ebe5bf84b657b808210515ce4c081d85fea3fc4f8874852090ee3dc01462b894647640c8c4ff260e35b8094238000000012a6368800000011ce00000003f0939600000009ba81f85d091f649e975a0000916304a52e1c7222623e80000000a6e0f9932a1df8c2800000760a1194666100001fb800096912125ef1ddc6ec8f2800015007a186ca9901e0c8da13ba986a69c8bf1fd816b823a4588f0e8a88cae793a0b031c80009a6913468a89981e5905e77b04b01fa947614a1d001f6985e8c5914a92d8ce886c137221321725f7914e7e70f3a1ae072c20c075e19f048c22d99f017700000001fd671980000000000253a38200000008c489622ac00005340a4491f00b4953092443812d448a2158052800069d8ab85ae838266309ec64f990200000c0308042a709a10251b00bc72f910435b145865a146a29c88a206a000067e8cee2670da070b84da0000caa14ba10c4021b54000012a4041b28000000000000000000000000116400000005ea92e44ae25901c900008df1ea0999000097b967a62800000002596000268c14013d46f91a8a93d0a3c3c9821c3de21c66e4a1e0466a06826f112c81a9fda938a0aa31480006e79b1a28d80004ef248e000219000018ba2c0800016d000000024de6e8a05c00000008aa86ac78a8c8e000170002a24741318a245fc0a06259003e56e254a00016a63b780007349ad80b78f3800000000000000000000050680005f580009b81b3c000000027d9fc400005be6ab00008cb9e0225c0000000000062f12108b69fe807785b856f06102bc0000000063800015222418000536a0102d71c5a66682282cfa210239918e1d080c4000034215da0442cb81a215e00000000000619943c44380008d9800010800000a4034e35215761bea460000000014f05e68e48dac3cc00664971ffe33f1a5a395010614e86561021e563fe817a820095a71a208486807e86b08c5a1891b465a2a1da53b9fca83189460cc806e06f01586f3100c0000d082c78cc8000166200000000000192830000099c1eb420183d23d11424883a2d06fa13665f68c228ee8008815158e1d4893840a1a6a48383be6c498aa0bb054c667013c22
  | 36 => 0xd10cb81bd24c4000190406425c206b0dfa657034c00020f000009d43f398d434c88ac72f11129608ec8833800000000004faa5ae7b2139c7810b202ca8f3e25f088e63900008eaa238792115c2e294ba30c020a88c12dc0db0c966e40d603640d940f7217a377032c56818d0692a57452d94d8044a41e7b126008448bec03e8cca39b10e62981f084c019da419897a5030000671856a7b3a0e46b680006eda63a00004ec80c0a2a51a044e9be8f0819901823e00b746cfa2080ae8000000268e789a3b600011a600011e60001a1056c0280000000059108483a0137e5ca225417c989e4aa174e22f183e125031412b854a3480ea034195ca3bd0c2c7a31a1461aa204000000000000000858000000147c0000000000125e79a8df81d88d8a000263c000000000000000001bae0002328000259c000164800000008f40ec60ff15c4869834400007e42e49d6600011e000780005a600001d180000000ace00000005b08000760800081d040a00000009480000000036685f000000d07c65d5000000000002268e365750000088868c7b1800085f9be2430a27674f1bfa000000023880007e18000000153a000000000004d600021c25ee20f2000134e000108604c89be90da48a09c8fec6d281c41af81b29a21ed68f98a0a5b011d630683b685a95d620e05ca05d108a66da5f6000201a0000ff21ed180c9931ea64d7264e6780bd200011c200011f01778bb033480001c40b484c380000001be662900005b48fa800000000001efc02596f86a910360001af60001b3a7f390267b88000648224c10a000029a228c0000000000232a84c00000000ff83331f8892fa062290269e2cf1c40389000087b8ebc9a58d8019e0e8a6e31e343bf000000000004db80008e9199e5ab1dae7db24b8922071632a1a84000107a57f0e1618785884da85082ee1dfa5b309c4514a0e211a927c00006d2000208875d15d20001c4c23f92f255815da000000000000000000fe46ea20409521da4013198e381000003198b6000103a89e8f965f026ac60e976e300872a00021e27cc81268cf1c9c4ba91441229296611a4823ac0d3694288b2028800056916de2ed9cb8076959c7e5266078e136061d0d2e44c8f7614083081d0162074a8ffe2809de03f78900065109427b961e7158c3805a1c1272b85ec5d008ea33d9c8806389b2772971200008b047282100eb91c82e614965088cc0635968e8be0efa32b267a4a119d860d8d7e8c69fae24b1b761f9973298f8b4a0000000080000089f8000000000000000000000142000000053080000daa3e200000000000a8686c9e2000010401259e0e8a502600000dc64cd17ea0400000000000000000008b015e60001226800940289980001e40e8c88599ca000000000017f465c808686a000000001340ec9e1c527000005103
  | 37 => 0xf6c33a9bce826000026e0a5667d80003a9000000013c252b8b544c122e26b100004a518b8950800055b97a246002a019c8ecc59919261bc0f0c04c1d9621614a20001f0c0fc9f122550bfe4a7030c37685e81cd8d2a162800050e82627ef14605fc8416088219e97e83d03f290a288d800024f95f400000001b900000000000000036400017300001aa24b81af20000b22000225c0000000499012815c80000000000590800000005f66649bb0000000035a847800019300ee9fa0390800099a000038e09d800019547878bd036f22c247a002600004501e3239a90a1a1c4d5000006b9d8677207740bc25466ce0000647800037b800000000000000000000000000000005d3000000005a23f49f1a0001e105229c904ce08280a4868839006e00001fdc2b01baa7de0000000215c43ca49292b98760000eca2ad80009b922ae4ce80000001d6e6c980008e015e481487584e314fc05408224d30fe26528fbe67b1b628f3931671281ec8eb0000582202a37f9736198a11a2f98ed893b03062f2000000025925478000694807084b9eee273051c13c8dfc37d16160000b564e680000001db853100ce78008b854b87fc337224862b8000000000000006547f0123441c000013618d89009b9654521ea000193687524863d39686000000036a8e0a00000000000000000006400013ce3b9026a69d05b02db054e3c80000556052458d0aa8339000076121861350afc000163040895345a697224f8164e1a98c3e1410e4867596e62eb93648c79c504e087380e9919c13e800000015ec00000000b1105c2bd800023f00003500fc45f521d6000000000025300001f6874600004010fa44fd93c4261068e6600000510a67e000236492702d83171ebc80604e2246887800008d0718000035ea558000208256490d0606111611517466801bd67c0893c3eb82a838d0d5291c828c59589aa1bf0f90746a56298c000000022823a683340001d32950079a3b1000012d07b047d046685b16184ea802c00007ae07e907836a03fe5231fa8935a0126b40afa898033a73ca61e0f680000000000409045c00000003b4000000000000001d100901a4e000000094c96f01120358000042c1a480001bc8d845b39e7e5558af44a682e659b9d0838e980a0069ad66bea6862c700000ac8c6e80e93e816e8d9a8498b5a25b1838000200814b0d682a3800019f8cec20700000001ea2000144c41220b8000000000008e41861c4242d98e62c024c66cb19903290000000000012788f048080000001a0884e800000012d200000002e7800000001cc0000f7c55916884bf22be7ac0f4242a08820b185c070902360d5997c000000000010fe80716d68e50e98798891099a8e14000018619a00000138000913802400025f86838c1e12800000001e46000086629f96ea46a84826
  | 38 => 0x72519000ea26a876d14c842c085043622b27e3a4e69a625ac00011144b620561f3998a33e84748d51fb06cd1a1a7681dfc75c1a12505959442c80cc8b7800042006f67c9912400000007c61c3a96e80004f78a4808c861659c8cf08eb945e00026bc31589dc46a000049400f400006846cd961200000001f3000010f853052c0000419018c08380000000000087800095807aa359195e000000064f000011e98206c3a1e6834226c00000006fb000076480002f01f3820900004c198f42800a326bd0cce00000006a805a671c8bfc0000b9c4c498f644e1d4669897081338000000152a0669f1e73800ec2ef89e82c60a4a2e3140e000027a43c00000000340427006c305888c8bd000000016267d6a288954a57e30180003a5108800000001bb1e907d60c8a2ca21de5da000000008d22dc1ca6000184219d80001d9947e4db1b6c9bc181200000049631a5e00018a28128c14661800013407f677589263cc80a4656000017595303a894be9498000089800071e833e00000f253c013852680001b9897e84a8c9e00000005ea000090700000001152448000014d000000020ec000000033e000000019d400000000000e0839ba200685901e00008de7909e7086700006b70000000000023213280ed13424f581c005895ae0378fb23fa994405d86aa5c924a0107a2d889c145413d000035980000c800000000000000000000018f23fd0e9043a9d2e6fc08545c60fc07df0018734142e41f12a277c8d983c7154200000008d8996e1e5011400000002fd00000000000000048e00014505ec000013480001ec810221da632000000000000000000000425966a3f1800000000001780b680001fd4000000050c0000000107400011cc0e780009250000000257a4130fa05429fe6000250400402760000000000207829e13e441a000015d000088712ce5a897c400015723ac800094189362cb0ae41049b781e98e0600000000000000000156200012fa00021fa68e822e34499341b21b2e77d07a407592b658889ba000000027d0000000000000000008d600001749ed0000098c48a80002d08000000000000000003a100006941c8a000116075f000097993cc82b957c00004e44ab08a06d590cc7eb160c0a689086a6a6a60000b601c89d800d79d44831000064587e015186b68089de446d1ab84f60a9832d06664ff82b600003926680000000205a000000088d23ec93917e0000000051c8000296a18e8c7094a00000000dd00008de1f2e38a10a09a280006a70904000048600003fa00022226d402ae60d08dc2ba989400b983c82c900e0002654281170a66f887200011584208e225ee80006f50bd40001dd200000006fba5c80000000462921a0000000378a0da61803ca0000dbe04e9a6e62fa2bc43a1e5e60b052a000000096fa3206c5838e0000
  | 39 => 0x1bda000247a00023e868a02ee1c1800057c119e1fd1dd42080afe000000086e80000000000000000000013407a91a300000bda00013b692d15aa000000091f9d948308000000246a932250800020fe0002512220000031c20a0000161c6c5000096780003198000046000099d000000011085c300005c401f600025f40001f9a5db03e235100000cc000075a078245000009a91aa897c238a6c290d2423015c8b3a6a000019fe5e696360df8000000021a3530b8008119b21299cf62b28ee85741fee24aa40a7c88ce07cf864c724809e2c50c7a2a788d803702be6c8000077c02f86930c0e14807a03220d7c1ee816c54117ae776980e8f714bc0000b444cc87308f10000543800000000004b69ed21e7000016f20b4000218813100002d41ec200000b298113a201d0d4254d89d03d5811648114aa7a09f2a3a9986261b988a626037c44781965c100003690000846000000008ec677a6f427c86044e40000000089455280007ed0568689946e0000000000102a0b919f447a84c839a89607cd0000196173c00500007c5251800018e200000006d800005d100008579a6474f8000000000079a00002c2116a23e00008d122e846c8ee60000e7224502941f4a6504de9c3210d8826171a21e64415d8847a15400017b43e780004ec860600003e81a510c872383d4172000007c84588711fd2166800053d0fda00001726fd8db61118d462b600006d904ca0b5a5ce28a000068100007a5800084926248c8800078ea22a90c9ad20001a9e02e00005779ee600000001b793f00e8251662c0ed427e80ca00000000f90c8664c96ee00018de0001c9a71d240c54f109800000001ba80006a012c428500004850d500000000230800043f0c4a09b20bc61c80007218000000123613f850c717895676da44a4700f8e163076c562955222725b60000db86338000000000034f180670b000056c91921548000000204e000211081d8abc8bca5d693b89e08500000217000071602b0826922013706da0000aec7dc8c7e7e7800078696ae5f891546df9590895916e748800020280000000570000000000020284599cce71f00003b080000001fe42de80006fe00006f0800000000000c987c004920c8054941431d93b80000fee3809c2a54b2100000243c03800000000d1c1b4000011c82246dc00003188e6000022d2000041857e05620f5a5bc5de00000000ed2000000063b91b80f300004c711720000b889b48fe61521ac000000002049f4e2728d0400026c07b69bd200015783011d7639e800000015322640e7c583800087016580000c445a1000096d26b678b1fd034b039004d8ffc0000b782a2101217a800045e0f64000001206900005351cde0000e767799b829b29d1290b8b1653a00005a7000010c22500001a0c431044c71a820c7431afe9b62534
  | 40 => 0x800018f800025fe5d802cc27680009bd8000000000000000000001c980001714708000025e0000873931e5ad26e876a19ac79b968c6fa9f5043524da000252c1da00000000370000000066aa390000000057198160000296000257200000009b38d740b5187a6c70c246ac8e3c4c315ac0001de821b000062396042628218656a2a00a2222805b92729091e30940a386750139e44623be79408465328a7411285180de1ec01d39af03361796205895e0771b5e215a53c31e1d5a75f937c57c950850d947a262078661f000093c02ea4f984a8000175000014e663b05cc77a988000000007549daa46122a40000000096107e95c24ac7ee8000000000053480008f8264a000000000007c215e8c2a21f223a0a1a1e800000000000000062236e93c8f588ec83ce25b89ce8d7800079300008bd80004af992c915817e000221a000000053c800001ca6c4012a44c8f9000081f80009108000000010866d0238565800000000008f18000930882a2c400005dd8c3a837815656f8ba42c11d244139a1e09510006ef066e0a90b728e89e6c99c9f6a6ff909a5e28cd06e5135e00000000000a16000068600011ee1b30b407c126788162304528226818c9cc626ba1cc4530d240f01cd80b701783c085a416192c28f513d26b300003ad0d0e8ff94206f0207270f1bac32d938a313a34a28313149a480da9b700005a5989a03da47084c8a3a4bda45030d17be72890145eb1df8028000044c000090980004711ffa0001832000036816495380cd8000000000021d0d4a7cf12ca4af0636000000032f80008228000000000073f01543b8a252000000045599ce2e98d547e61bca00596920001c807aa03948ce0c9a924013e3ef08520001ebe09e05aa000000007886f801581b48bf8a523c6049c30f181e34616f2530148894882aa59300000dc80008ee10a441b80002d61de26c184ea3c0175c37516543731bc662589ea65d88a48f59d4c6a383b86c624fa43d80000000a2c32084100b0234e06780007139d1e0ab1e8046da02c17525ec8d487f270e09742daa1bc1971eea8f29f645dc09d60990db008fa0a659a00004eb0fdc9922334365a4e89ac800000000000000000000173a06e07d60920cb200023720000a5408206ba00023c000016dc7c9000000023f89a4000000013847ed855e16c826646e85829620d888dd23764ea118c3458c2e0000000000221808aa1f296800002e8800000000001dc800018f0ada00000000000000841000093a8e564ac8092523805c47919a42ed0ba800013c80001d0e0000950427806010180000001400000000031a905809d00000000000000152095a80006d020cc11f89de6608e1c0cf1f3000000005d9974a28380000000000000208e5d480003ee80002878a1a000081a12f9e600698a7c000133e3c29dbe977
  | 41 => 0xc079e4c200e257080000000000219000000002c80001826000141855300006149cdc08c17a629080001de226e4400000000000049198c2934884071d8adc8c416a075788000430000141863044890a60ef0c405119ca491ba46485e24d05ac98c83120000023837a29d8000000000091886a4553800000020f60001d30000187e000102c18b8e888a39b8a361800000024a673685ee2619a6c8611c7802b00000000000000251e000005e98980004d4a17400004bc821929250a98a8000000034780003f8000005380001a4049a000000000000007be00004b1a2ca752000084d800076f00000000eb600000000000dc45c591be58b00005971c1022e94f63d413dc00000007589cd400026ee8cc90f44bd135a482226299d80000722614000232c0001ee00000000000113659f80008a7a16e000026e8bc11d2000000048609a2000000079e8720398938e53315446a59f44091a5b290e267c9749676581a4a262b03de90b0c429870b821661c02372a0e88f0982e9258bdc3930170865002a18e80ea98411700002684537935800013ee0bc8b26182800032e8000000000075c800000021762fc18dc0001d201c2000006700007f7886a0000862980a1b6000103e0001c1a6ae98c6632993a719255c12880000000000000158c9858462000177e000191a594800078180007689cf863800000001b4898a9d0a008862c000105431520964d1000000000000000d9c4e003960000000000126c1f2840c00000006df1c166588000000168200000000000000000000067f0d30000173e405824c6f80d9259d165a19e843a00000003740e265af80000000b962b180005598de070180000001780000205e000000000008680000000000164a00a112859e043839a265e8c31c5234400000d5203e5b28000000000000000006ad800040d000074522fa81313862d49762157000a6e724b25720de43451f520000000000005a8692108000000078ca4d448184aa331175e65e800000000001d900006920d822ab118806c032e0000faa22100008e38dc82faa1200001fea7e313504b884041788d3e7cd9b2489f18d227499661d510da835100a66f1f5c00000000000000555213e00000000b6a3700230000000000071b20667bd05647a48d28000144a29c22869578000000091c7170d765b100385ca8b321b583606421ce815122cc8a702fa8e59f54000155c000184a681a11c8240d020a2800068f82e00b48776000000001f0b2469600009a097a03fa22ea5a0069a039000000000000c4800000015b60fd8b5e6dba0fa0001a7a392800042b9150475156c04401e888fa0209bf986865580007a62644016129811c00000000e5247609722221e726e38000896117a7ec800034e19746491e0877f928c80d00006a99b08749800000024f69598000000246
  | 42 => 0xf28df990a2a09f4a2b98af25cd07267529bc800008be540a0dc93813702df8000521000067880002aa800000000004e207de00017cc14f950c2a31e5a3e700b018d1d2c4e6076a3f30a927d5a4f856a000064b8f243b5916c0f20000328891e13023148b115ea70a11de4158dea3119e743842300703239e42389c27711eca5a78aa600000003ae800087d000000000002448dd66a424006b9977a00020480000808790000024316fa2e18000000229620f000000022e687e1cfa26a125a4019ff081b92a40a8800018a9f903fd9a820001eae8ad000096193da00000005f225da8e200005578e5e496000002600002b7839c1de8000000092883b84b200003ac23b80001a79a7884b0000000000000017c2518a68046400004e9a4440000f6e49880000000db40000c9294e20ac801225e51d0f60265964663e99220000bf83280958000000051003e00a7a0a877625683ab80002cd85d0000000022600008ea203681b00007888a6418204880000a10000255485180005e51aea0000000996800000000f81e61586000251a55d000003080003aa000091b000017f86e200000004431a987c5985c38a8000000141e35e00003d89ba45b686c200003a200018fe5e212ae4ef8e4e0000ca63a58770183915a084a30876c18e85dca0602f31ed827906b42110000829000053b234c0001bd83d9800039700008f48f8c0031d4211a0206535800000009fe0001e645542478011a094079a18a0c08f6a0000000000000000007b8487825608f00fc4b01c826919eec584000025a92e67e900009b1a07a1678fac20622a87ef95e00000e66978a3f45ec8bde98d2652000220a384800038380001680b0c0e687c49230c500001a7200026aa00012681c0a278965064242f00002b5a16850c8e208e61f708a9a1fc723000040f24c068e087e3d5220c0c899b07d7928a00020a2306258a74d855a7a2000068d00008b700002ad000e82307be621a4341d80bb20d49d163cb0644000000037c80002e4222e3d3106a1fb1e1425d8000890831e26b000000000000410de667a8000000000061210d6303003c000000095e00000001abc155824e66e827c0bd8b304140df011b13768d08000250800000000002ce8000000085a63a864a0000460805800000019ae421189c00000003e089300000a349bf209e31300000000a467ea8e640000000000140600000002a0000026d00009a880004fd1a325b19fe00fb09a44ba1d5896385d82f1a5aa4a4154638b0f3473b0000000000000000005f496d481f171a53f8000000112a00005e48a0122e8ce86484148f94000000073893304f180003e120068d18f4a7ae024a2871ff62a125ca19481d497c9ff2369992a6ad21dc0001b1e36b8f2a944034a0001d600b29d4e7150000000000071c0000905a6421a8249846
  | 43 => 0x37000003070e004741c303b811fa7f08dec8a69d8c00000002ba059427e166c05308c499985fa2ea850e2c280006090de8022939419795c076782bc4408000000000042a85ce05f149269a2524000008800000d200002d0224a1522e811961aa00000000000698145c4429d8a1f6066a000001c9aea45a2668000000215018826ae10d117e874000000000001cf00008a1066000000004619a1848008
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc75211d952440018f5003b2a4880031e60076549100063c200eca922000c7a201d952440018f2403b2a4880021fa1e64549100043ec3cc8a92200087f8759152440010f90eb22a48800297e0d64549100052e41ac8a922000a6f8259152440074d904b22a48800e9ba08645491000536c10c8a92200087e8798d52440010fb0f31aa4880021fe1d63549100043e43ac6a922000a3f8458d524400147908b1aa4880029be09635491001d36412c6a922003a6e8218d52440014db0431aa4880c69d2197154910005aa41ae2a9220a7b67825c552440654f10cb82a488002ce2117054910535b5c12e0a922000d71715c1524400717d093b684880021fe1576d09100243e42aeda1220008bf87593424400153906b26848800eab20964d091000c7a432e3a12200487e85dd942440010fb0bbb284880021fe1576509100243e42aeca1220008bf845d942440011bf06bb2848803a3720d765091000477c12eca1220008be8799142440071790eb228488002a720d645091001d56412c8a1220028fa86dc142440018f0cbb82848800e37a0e76cc9100043fc2aed992200487c855db32440011bf0eb1e6488002a721163cc91001d66412c799220028f8865c332440090fd0bbb264880021f617764c9100043fc2aec992200487c855d9324400117f08bb264880562f211764c9100046fc1aec99220008ef825d932440011bd0f31a648800e3721d634c9100054e422c69922003acc8258d32440031ed0db8a64880031d197714c9102e63a3b6caa0a2000e376519141440012eb0a39a82880067ca007350510006e9180e6a0a20029b48750d4144001bc441b9282880c71d1d952505102e63b3b6cb98a20018f686dd331440012ef0aba662880067c20174cc51004c7ac3ec798a2000e5765d8f31440031ef0eb1e62880029d21952cc51018e3b3b2a598a205cc7476d952144001cc8c5b2a42880025d617744851000cf9406e890a2000db040dd121440031e90cba242880063da1a7348510004bac28e690a20019f2801cd2144001ba46039a428800a7921d3248510005724326490a205dc7a76d97404403f1f30fb2680880038ed9764d01100147dc3ac9a02200097b855cf40440053e102b9e80880029e21952d01101963d3b2a5a02205a9f38750740440013e30f98e80881771e1db654c1100147d434e89822000979851d130440053e5023a260880036c904744c11000cec43a869822000de221dc930440658f0eca9260880027c21d414c110007c8a1a8298220549f287cc53044001f826490a60881771e1db654811000734316ca90220028fa869d120440012f30a3a2408800a7ca047448110006d9208e8902200097985dcd20440053e503b9a4088003740c773481100147c432e690220019e88750920440015d10ca124088003e85094148110
  | 1 => 0xd0e3aac6880030fdd77458d100061e3aee8b1a2000c3f751d16344001878ea3a2c688003271d37358d1001c7743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000c6f85dc963440018d90bb92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100043f43ea4b1a200487c87d49634400187ee9a92c6880030f1d35258d1000637b96a4b1a2003c6c72d4963441518f2e0328c68800237e1d6318d100054e422c631a2000acc8258c63440010ff0aba0c6880121f2157418d104063cb86a431a2000a9e848c863440010ff0abb686880121f21576d0d1000c7a432e3a1a200087f855da43440090f90abb4868800a3e2197090d100243f42eeca1a200087d85dd943440090fd0b3b286880021f6167650d100043fc2aeca1a200487c855d9434400117f08bb2868800237e0d7650d1000477c12eca1a20038ec825d943440090f90a3b286880021fa1b7550d100043f43ecaa1a200087c87d9543440031ed0db8a868800a3ea1b7050d100243e42cec21a200087f855d843440090f90abb086880562f2117610d100746e41aec21a20008ef825d843440071d904bb086880021f2197510d100043fc3eca21a200087d87d9443440031e90cb88868803b3518d7110d100147c432e021a2015cb8645c043440014db05baec4880029b60875d89100043fc2ae9b12200487c855d362440011bf06ba6c48803a3720d74d89100043fc2ae7b12200487c855cf624400117f08b9ec4880562f21173d89100243f436eab12205c87c86dd562440010fd0fb2ac4880021fa1c65589100061fb2ee8b122000c3c65dd1624400187eca3a2c4880030f194745891000656310e8b122000c5f65dcd62440018b8cbb9ac48800317d9473589100062e328e6b122000ccc621cd62440090fd0fbaac4880022fe1175589100ac5e422eab1220008df835d5624401d1b906baac4880021fa1c75589100ac5f43ee8b122000c3f75dd16244001878ebba2c4880030fd4b74589100061ea96e8b122000c3f751d16244001878ea3a2c4880030fd4874589100061ea90e8b12200e8de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018bea5b9ac4880031754b73589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100062fa90e6b122000c5d521cd6244001958e9b92c488003331cf725891000c7d43ee0b12200087e869d952440014db053b2a4880021f60a765491000636c14eca922000a3f845d9524400147908bb2a48800297e0d76549100052e41aeca922000a6f825d952440010fd0c3b2a4880121fe0876549100243ec10eca922000c76811d952440018eb023b2a4880031d0c476549100063b108eca922000
  | 2 => 0x67650d200043ec2ceca1a400087f855d943480090f90abb286900023de057650d200147a40aeca1a40008fb805d9434801d17d0fb2286900030f1d76450d200061e3a8c8a1a40018ec865c843480071f10cb808690002aba1a4350920005d4c0086a12400087f855d361480090f90aba6c2900063e20174d852000c76432e5a0a400487e851d941480010fb0a3b282900032b1d942505200243f42ced98a400087d859db31480090fd0b3b262900021f616764c52002c3ec38c5b2a2000a3e8418b654400147b08316ca8800297a0c62d95100052ec18c5b2a2000c6d7218b65440b94f501ba6ca881769e60374d95100061eba0e9b2a205da76811d365440b94eb023a6ca881769da0773d95102e53ac0ee7b2a2000c5d731cf65440b94f50039eca881769e60073d95100051f420e5b2a2000a3d841cb65440014bd06396ca880029760c72d95102ed3b408e5b2a205ca75811cb65440b94f500396ca881769e60072d95100043f43c85b2a200087d8790b65440014bd07216ca880029760e42d95100043f43885b2a200087d8710b65440010fd0f196ca880021f61e32d95100051f42465b2a2000a3d848cb65440010fd0e196ca880021f61c32d95105463cb80cbb2220028f980dd764441018f2e1a96c888002a7a0e42d91100043fc12eb322200487f87d4a64440010fb0fa94c8880021fa1f655911000636396cab22200087e8719564440018d8e432ac88800317d9773591100062e32ee6b222000c5f651cd64440018b8ca39ac8880031bd9772591100063632ee4b22200487e87dd564440010fb05baac88800237e0d75591100746e41aeab2220008ef825d564440071d904baac8880021fa1c75591100062fbaee6b222000c5c75dcd64440018beea39ac888003171d473591100064fba0e6b2220038ee87dc964440018deebb92c8880031b1d7725911000667b9ee4b222000ccc73dc964440018df0bb92c8880031b217725911000637ba8e4b222000c6c751c9644400195ee8392c88800333dcc725911000666398e4b22200087e87d4964440090f90fa92c88800317dcf52591100062e39ea4b222000c6f72d4964440078d8e5a92c88817b1d5c465191100045fc3ac83222000a9c83590644400155904b20c8880021fe1573191100243e42ae6322204fc7571d48644400153d07210c88817b1d5c465d8d1000c7ac0eebb1a204fc7571d4b634400153d09196c6880021fe097598d100243fc3ea531a200087d87d4a63440010fd0fb2ac6880031b1cb6558d100043f438cab1a2000c6c72195634400187ecbba2c6880030f1977458d100061fb28e8b1a2000c3c651d163440018decbb92c6880031b1977258d100243f43eeab1a200087d82dd5634400117f08baac6880562f2117558d1000477c12eab1a20038ec825d563440010f
  | 3 => 0x899660008de8799132cc00759d0532265980063720d75587300243f42ee8b0e600087d85dd161cc0090fd0abb683980021fe1975d07300043fc3acba0e600087d8759741cc0051790eb22839806e1f61b754c7300043f43aca98e600f87c8759531cc01dca862b2a639800a3b21d62487300061ebaea9b22600087f855c7644c0090f90ab8ec8980028fa1641d91300243f43eeab22600087d82dd5644c00117f08baac8980021fa1c75591300061e3aee8b22600087e87d49644c0090f90fa92c8980022fe1d64191300051e42ac832260158bc845d4644c02b87908ba8c8980021fe0975191300063d082ea3226000c3d75d50644c0090ff0fa90c8980021f61f521913027e2eb9ea43226000a3e85904644c00157301208c8980030f1d76450d300061e3a8c8a1a6000c5c76dd5434c0010ff0aba6c4980121f21574d893001c6e41ae9b12600087f855c7624c0090f90ab8ec4980029b60a76549300051fc22eca926000a3c845d9524c0014df04bb2a4980029de0576549301953a40aeca926003a6e82991524c0014db05322a4980021fe1d64549300043e43ac8a92600087e87191524c0010fb0e322a498002d360a435493018d2e43286a92600087f855db424c0090f90abb6849800e2f21176d093000c6e432e7a12600487e851d9424c0010fb0a3b2849800e2fa1f645093001d57416c8a1260008dd87193324c0031b90cba2649800e37a1e644c93001d67414c89926064ace86dc9324c00759d0db1264980063760f75d85300043fc2ae9b0a600487c855d3614c007998e4996c2980063721973d05300243f428eca0a600087d851d9414c001938eca1a82980121fa1476485300043ec28ec90a6000ccc764c9214c0078f4eca9660980030f5d754d91200043fc2ae3b22400487c855c7644800147d0b20ec8900021fe1573991200243e42ae7322400487e87dd564480010ff05baac8900021f60b75591200045fc22eab2240008fb805d564480010fd0e3aac8900030f1d774591200063c3aee0b2240008bf8759064480014790ab20c8900562f21175191200ae1e422ea322404f87f825d464480630fb04ba8c8900031e84175191200061ebaea83224000a3e85904644800157301208c8900021f61e75d8d200243fc3aebb1a404f87f825d763480630fb04baec6900031e84175d8d2000566c1063b1a4000ad9800c763480010ff04bacc6900021f6097598d200061fa94e931a4000c3d529d2634800187ea4ba4c6900030f5497498d200045fc22eab1a40158bc845d563480011ef02baac69000a3d2057558d200046fc3ac631a400087f855d063480090f90aba0c6900021fe157118d200243e42ae231a400087f855db43480090f90abb6869003a2f21176d0d2000c76432e5a1a400487e859da43480010fb0b3b486900121fa1
  | 4 => 0x2500071b906bb664a00121fa17764c9400043ec2eec99280038de87d8d32500090fd0dbaac2a00021fa1f655854000636396cab0a800087e8719561500018d8e432ac2a000317d9773585400062e32ee6b0a8000c5f651cd61500018b8ca39ac2a00031bd9772585400063632ee4b0a802487c865d741500010ff0fb2e82a004a1f61f65d05400043fc2aed98a800487c855db31500090fd0bbb262a00021f617764c5400243f42cec98a800087d859d931500090f90a3b262a00021fa1b754c5400043f43eca98a800087c87d9531500090fd0bbb242a00021f617764854039e3d3b6cba028073e3b64d9740500014f10ca9680a019e6ee1d42d014007c3f43cc4b2e6000a3e8498965cc00147b09312cb9803a97a0e625973000637b94c4b2e600ee4f3298965cc00187ee93a2cb9803a97a0e745973055d2ec1ce8b2e6000a3e849c965cc00147b09392cb9803a97a0e72597305552ec1ce4b2e600087e8790965cc0010fb0f212cb9803a97a0e42597300052ec1c84b2e600087e8710965cc0010fb0e212cb9803e1fa1e32597300043ec3c64b2e6000a3e848c965cc00147b09192cb982a697e0d71597300752e41ae2b2e606fa7a801c565cc0014f30038acb980021fa1e41597300043ec3c82b2e606fa7a8090565cc0014f30120acb9803a97a0c41597300052ec1882b2e600087e87c8565cc0010fb0f90acb980021fa1c21597300043ec3842b2e6000a3e8408565cc00147b0810acb9803a97a0c21597300052ec1842b2e606fa7a8008565cc0014f30010acb980021fe0975d93300063742ae5b266000c6d855cb64cc0090ff0fa96c9980021f61f52d933001e37396a5b266000c6d72d4b64cc01d8bce732cc99803b179cd65993300770f21acb326604fc5e73d4a64cc01d53d07214c99803aa7a0e42593300243f42ee2b26600087d85dc564cc0010ff04ba8c9980121fe1f52193300043ec3ea4326603c87d86dd543cc0010fd0eb2a879803e1f21d6550f3000536c14eab166000a6f825d562cc0090fd0bba2c5980021f6177458b3001c6ec1ee8b16600487e85dc562cc0010fb0bb8ac5980121fe0b7654b300243ec16eca966000c5f32dd952cc0018ba65bb2a5980028fa127654b300051ec24eca966000a6d829d952cc0014df04bb2a5980031be097654b300043f438eca96600087e87d9152cc0010fb0fb22a59800e9ba0b6454b3000536c16c8a966003a6e8299152cc0014db05322a5980021fa1c6454b300043ec38c8a966031a5d8690d52cc00169b0521aa59800e2f21176d0b300762f39acba1660008bd87d9342cc00755d05b2685980031759573d0b3007477c3ac5a16600ecce7358b42cc0031bd07bb2859800e2fa1f6450b3001d57416c8a1660008be8719142cc0018f4cbb828598003275d264ccb3000cec402e
  | 5 => 0x80e3d2197110d2100567436869924200bc58110d32484010ff0ab9ec0908121f21573d812100c7a40ae7b02420087f855c663d00090f90ab8cc7a00121fa1f7558f400043ec16eab1e8000c7a10dd563d00010fd0e3aac7a00021fa1f5258f400243e43ea4b1e80038bd84dcd62d00090fd0bb8ac5a00021f6177158b400051f424eca968000a6d829d952d00014df04bb2a5a000e9ba0a6354b4000536c14c6a96800087f8758d52d00010f90eb1aa5a00031e5db7054b4001d57414c6a16800087f855db32d00090f90abb665a000e3720d76ccb400043fc2aec996800487c855d932d00011ef02bb265a000a3d205764cb400046fc1aeab0e800e8dc835d561d0007958e4a12c3a00021fe1576cc7400243e42aed98e800087f855d931d00090f90abb263a00121fa1776487400043ec2eec90e8000a5e8398b65500014bb07316caa004a1f61c62d954000636b90c5b2a8000c5d731cf655015d47d08396caa01ce8f61072d954039c3f43c85b2a800087d8790b65500014bd07216caa00029760e42d95400043f43885b2a801287d8710b65500010fd0f196caa00021f61e32d95400051f42465b2a8000a3d848cb65500010fd0e196caa00021f61c32d954039d3d404e3b2a8000a79809c765500018eae238ecaa01ce1fa1e41d95400043ec3c83b2a8073a7a8090765500014f30120ecaa00021fa1c31d95400043ec3863b2a8000a3e840c7655000147b0818ecaa00029ba0831d954000536c1063b2a8073a7a800c765500014f30018ecaa00021fa1f21d95400043ec3e43b2a800087e8708765500010fb0e10ecaa00028fa1021d95400051ec2043b2a8000a5e8308765500014bb0610ecaa01ce9ea0021d95400053cc0043b2a8000a9d840c7635000159b0418ec6a0002b660031d8d4000637396cb31a8000c6e7219663500018decab94c6a00031b1957298d4000667b1ae531a800eccc635ca63500010fd0fb2ac6a00021fa1c6558d4056e1fba0cab1a80008df8758c63500010ff0ab88c6a00121f2157118d400766a18ae231a807487e86dd543500010fd0fb2a86a01ce1f21f6550d401b43e432ea21a800087f87d9443500250fb0fb2886a00029b60b75d894000536c10ebb12800087f855cf62500090f90ab9ec4a000e2f21173d89400043fc2ae3b12800487c855c762500010fd0fb2ac4a00021fa1c65589405661fba0cab12800087e869d952500014db053b2a4a00031b60a76549400051fc22eca928000a6f825d952500014f700bb2a4a00121fe0876549400243ec10eca928000c3f421d9525000187a843b2a4a00030f90076549400061e200eca928000c78401d95250001c5885b2a84a00031e197705094039e1e3b6caa128000e2c62d9542500e7a70e1b2a84a00066ea1f70509400043fc2aed992800487c855db3
  | 6 => 0x46fc1aeab22620087e871d5644c4018b8ebb9ac8988021fa1f52591310243e43ea4b2262008bf87590644c4010ff0ab80c8988121f21570191310ae5c202e0322628287e86dd5434c401aa863baa86988021fa1f6550d3140c3e43ecaa1a623687c865d4434c4010ff0fb28869886e1f61f6510d3100536c16ebb126200a6d821d7624c4010ff0aba6c4988121f21574d89310043fc2ae1b12620487c855c3624c4010fd0fb2ac4988021fa1c655893157e2fb98cab12620087e869d9524c4014db053b2a4988031b60a76549310052fc1aeca926200a6f825d9524c4014ef02bb2a4988121fe0876549310243ec10eca926200c5f321d9524c4018ba643b2a498803178c476549310062e188eca926200c74311d9524c4010fd0f322a4988021f61e645493101d37414c8a926200a6d82991524c4010ff0eb22a4988021f21d64549310043fc2aeda12620487c855db424c40717908bb684988121fa1776509310043ec2eeca1262038be87d91424c42b1dd0fb1284988023761e64cc93101d67414c99926200e4c32d95324c4018e8cbb8a6498a07171db654c93100726316ca9926281d5471d95324c4071bd0f322649880eb3a0a644c931014eb43ee29926281e5763d97314c4014e90ca9662989de75e1d32cc5310243f436eab02628187c86dd5604c4010fd0fb2ac0988031b1cb65581310043f438cab026200c6c72195604c40187ecbba2c0988030f19774581310061fb28e8b026200c3c651d1604c4018decbb92c0988031b19772581310043ec3cebb22420487f875d764485010ff04baec8908ca1f60975d91210063b882ebb224200aad82103644840156b02206c8908021fe0975991210043ec12eb3224200c5f529ce64484018baa539cc89080317d4973991210062ea92e732242008df835d5644841d1b906baac8908023ee01755912100c7c402eab2242008bf8759064484010ff0ab98c8908121f21573191210043fc2ae0322420487c855c064484018baeba9ec6908021fe1570d8d210243e42ae1b1a4200a5e858c363484010ff0aba4c6908121f2157498d210243f43eeab1a420087f82dd563484010fb05baac69080237e0d7558d210047bc0aeab1a420087e871d563484018b8ebb9ac6908031d1d77158d210046fc3ac631a4200a5c8558c634841d1b906ba8c69083b1720d7518d214043fc12ea31a423287d825d463484018ee20ba8c690803175d75318d210052f42c6031a4200ad5818c063484090fd0b3b686908021f61676d0d210043fc2aed21a420487c855da434841d1b906bb4869080a3b2197290d210243f42ceca1a420087d859d943484010ff0abb286908121f2157650d210047bc0aeca1a42008fb805d943484031f100bb2869085637a1f6350d210062e3aec6a1a4200c5c7518d43484051d90cb90869
  | 7 => 0xd5818c063504018b8ebb1a86a0803171d46350d410061e3b6eaa1a8200d3471dd543504010ff0ab9ec4a08121f21573d89410043fc2ae1b12820487c855c362504014db053b2a4a080297e0d76549410052e41aeca928200a6f825d952504014f700bb2a4a08c69e20176549410043f438c6a92820087d8718d525040165b05a1aa4a08ca8f21943549410045ec38c7a12827caae86dc9425040755d0db1284a08021fe1576cc9410243e42aed99282038dc835db32504051790cba664a08121fa14764c9410043ec28ec99282028bc865d132504071bd0fb1a64a080eb3a0b634c9410145ec26ebb02820087f855cf60504090f90ab9ec0a080f2b1c942d81410043fc2ae1326620487c855c264cc4090fd0fbaac9988021f60b75593310063b886eab26620087e871d564cc4010fd0fa92c9988121f21f52593310043fc12ea326620487f87d4864cc4010fb0fa90c9988121fa177058b310043ec2ee0b166200a5e839d952cc4014db053b2a5988029be097654b3101d37416c8a966200a6d82d9152cc4074dd05322a5988029b60a6454b310043fc3ac8a96620087c8759152cc4010fd0e322a5988021f61c6454b310063abb6e2a96620087f855db42cc4090f90abb6859880e2f21176d0b310043fc2aeca16620487c855d942cc4011f700bb285988063e2017650b3101c5f43ec8a166203aae82d9142cc40759d05322659880237a1c644cb310045fc22eab0662158bc845d560cc407998e4992c1988028fa1262d95310051ec24c5b2a621b87d8718b654c4018dae4316ca988030f5d074d953158d2f418e5b2a6281a5d831cb654c4010fd0f216ca988021f61e42d95310052f41c85b2a6200a5d8390b654c4010fd0e216ca988021f61c42d953140c3f43c65b2a620087d878cb654c40147d09196ca988028f61232d95310043f43865b2a621b87d870cb654c5034ed03386ca988029d60670d95310063cb80e1b2a620087e87103654c4010fb0e206ca9880297a0c40d95310052ec1881b2a6200a6e82103654c4014db04206ca98a069da0440d95310053ac0881b2a628187e878c3654c4010fb0f186ca98a069da0630d95310053ac0c61b2a620087e87c83654c4010fb0f906ca988021fa1c20d95310043ec3841b2a6200a3e84083654c40147b08106ca9880297a0c20d95310052ec1841b2a6281a7681083654c4014eb02106ca98802a760c40d913100556c1081b226200ab581103644c4018dce5b2cc8988031b9c8659913100637b2ae53226200c6c655ca644c40195ec8b94c8988572b19172991310043fc12eb3226200c6e855ca644c4018db0ab94c8988121fe1f52991310043ec3ea53226203c6e72d4a644c4018dae5a94c8988021fa1f65591310043f438cab2262b0c5f73195644c4090fd0fbaac8988021f60b75591310
  | 8 => 0xa5b8ac8990031ddd471591320063a3a8e2b2264018fa87dc1644c8018f6ebb82c8990031e1d7705913200679b8ee0b226400cf071dc1644c8018f6a5b82c8990031e54b70591320063dba8e0b226400c78751c1644c8019e6e2382c8990033c1c470591320045fc3ac8322640087f825d4644c8010fb04ba8c89900e73e1d72d0d3201ce7412e3a1a6400d4c32dd5434c80117d0e32286990022fe1d6410d320062f3b2ea21a640399d87990434c80171b05320869900237e1d6410d32004cfc3ac821a6400b8f82590434c80739904b8086990ee7361f43cc932076e398ae3992640087f855d3614c8090f90aba6c2990023ee0174d853200c7c402e9b0a640087d879d7604c8090ff0ebaec0990921fa1e62597410ad1f424c4b2e8200a5e8398965d04014bb07312cba08031bdca62597410af17a14c4b2e8215a3e849cd65d056947b0939acba080317dce73597410ad1f424e4b2e82b3a3d849c965d04014bd07392cba08029760e72597411243f43c84b2e820087d8790965d04014bd07212cba08029760e42597410043f43c64b2e820087d878c965d042b47d09192cba08028f61232597410043f43864b2e820087d870c965d056547f08b82cba08568f211705974144d3b408e0b2e8200a75811c165d04010fd0f182cba08021f61e305974144d3b40c60b2e8200a75818c165d042b47d08182cba08028f61030597410043f43e40b2e820087d87c8165d04010fd0e102cba08021f61c20597410ad1f42040b2e8200a3d8408165d04014bd06102cba08029760c205974144d3b40840b2e8200a758108165d042b87ce932cc7a08570f9d16598f410af0fa1acb31e8280c3e74d4a63d042b53d09194c7a0856a7a123258f410243f42ee0b1e820087d85dc163d04790fb0dbaa87a08021fa1d6550f411243e43acaa1e8200a6d829d562d04014df04baac5a08121fa177358b410043ec2ee6b16820487e85dc162d04010fb0bb82c5a08121fe0b7654b410243ec16eca968200c3f42dd952d040187a85bb2a5a080297a0e7654b410052ec1ceca968200a6d829d952d04014df04bb2a5a08031be097654b410043f438eca968203a6e8298d52d04014db0531aa5a08ca8f61b4354b4100596c1686a968200c9d7398f42d040117d0f31a85a080eaba0a6350b4101c6e41aed9968215c3e7459732d040187acaba665a08572b9d162ccb410145f426ec99682029b4815d132d04018eccbb8a65a080a2f21175583410243f42ee6b06820087d85dcd60d04018baeba9ec6a08021fe1570d8d410243e42ae1b1a8200a5e858c363504011bf0eb18c6a0802972156318d410746e41aea31a820ec5c835d463504010ff04ba8c6a08031dc417518d410062ebaea631a820487f87d4863504010fb0fa90c6a0a030f5d35218d410052f42c6031a8200a
  | 9 => 0x64585520062fb16e6b0aa400d4f62dcd61548018bb0c39ac2a90031799073585520062e320e6b0aa400c5f621cd6154801a9ec439ac2a90031798473585520062e308e6b0aa400d54611cd6154801aae2039ac2a90021fa1f63585520062e39ec6b0aa400c5c7358d61548654e902b1ac2a900353dcf7258552006a639ee4b0aa432c7776d856154801aa8e7b0ac2a92db59dcb615855201cb7414e9b02a42d96d829d360548630fb0fb26c0a90030f9d364d815218d3d406c9b02a400e3840d9360548010ff0eb26c0a90c69e20164d815201cb7414e7b02a42796d829cf60548012ef02b9ec0a90ca5d20573d81520043ec3cc7b02a43187d8718f60548634f50031ec0a90c61f61f61d81521963b38ec3b02a431a7a80d8760548010ff0eb0ec0a90029720d61d81520061fb16e8b02a400d2f62dd1605480187b0c3a2c0a90030fd88745815200697b10e8b02a400c3e601d16054801878c03a2c0a90034e18074581520069d080e8b02a40087e87d916054801878e9b22c0a90030f1d1645815218d3c402c8b02a400c3c7498d60548018bee731ac0a90021fa1c63581520061e3a0c6b02a400d2f74dc96054801a58e9b92c0a90021fa1f61581520061e3a6c2b02a43187c875856054801878e8b0ac0a90029720d615815218e3dbb6c0b02a400d3874d81605496bad6e5b02c0a90021fe157198f420243e42ae331e840487e87dd563d0801878e9baac7a100e2f2117558f420043f438eab1e8400c3c741d563d08098b8eb29ac7a10563721d5358f420052ec2862b1e8415a9e840c563d080159b0418ac7a1002b66003158f420243f43eeab06840087e871d560d080717b09baec6a10021fe1570d8d420243e42ae1b1a84008df8758c635080735f0eb9486a100e6ba097090d4200696216eaa1a8400c3e765d4435080733b0f31886a1002e360a6310d42004cfc3ac621a8400b8f8258c435080735904b8886a10ee6b61e43d09420aed5a02e1a12840087d879d761508090ff0ebaec2a10021fe1573d81420243e42ae7b0284008f7815cf60508051e902b9ec0a10021fe1571d93320243e42ae3b26640087f855c264cc8090f90ab84c9990121fa1f75593320062e39eeab2664038dc835d564cc8010fd0e3aac999003171cc75593320261e3aca8b26640e8bc8755164cc80147b0a202c99903aa7a0c405933200556c1080b266400ab58110164cc8011bf0eb2087990121fa1f75587320043f438eab0e64038dd83dd7644c8010ff0ab8ec8990121f21571d91320043fc2ae1322640487c855c2644c8090fd0fbaac8990021fe0b75591320043ec16eab2264008f7815d5644c8051e902baac8990023ee01755913200c7c402eab22640087e871d5644c8051ed0fb8ac8990031ddd771591320063a3aee2b226400c7752dc5644c8018ea
  | 10 => 0x322a400c3d87d92645498387ae5b24c8a90038bd9172991520051ec24c1322a400c797098264548014eb02304c8a93034bdd372591520063bb8cc2b22a400c787098564548014f30030ac8a90031e1c0615915218cbd43ee0b22a400d6b72dc164548018f6c5b82c8a90035ad8b70591520063dbb0e0b22a400d3b741c16454801ad6e4382c8a92ff0f9da64191525f596c14c8322a40087f8759064548014f100b20c8a90024fe1d64191525ed97c12c8322a400b3880590645484f2db05398c8a90029d604601915200596c1080322a400e386010064548612df04ba6c6a90030f9d364d8d520052f41ec9b1aa400a788059363548014bb0d18ec6a90029761831d8d52005a6c1063b1aa400a5e8318363548014eb02306c6a90030f5d26498d520052ec1cc931aa4bcd4d72d8e63548014bb0fb1cc6a90031761f6398d525de2eb96c731aa400e4f635ca63548014bb0730cc6a90031d5c66198d520053cc00c331aa40087e87d9163548018e8e3b22c6a90031d1c56458d520053c402c8b1aa4bad4f73dc963548652ed0fb8ac6a900359dcb7158d520063bb16e2b1aa400d6762dc563548018eeec38ac6a900355dcc7158d52006b3b90e2b1aa400c747198163548018f6e1302c6a90029d6046058d520063a388c0b1aa42d96d829d063548010fb0f320c6a90030f5d06418d520052ec18c831aa4b9c5e7698c635497169b05318c6a90021fe1d6318d520053a40ac631aa40095f8758c635496f69f04b18c6a9002d52056318d520053cc00c231aa400b4d820c46354801ca8c2188c6a90025b60b76d0d52194bb40eeda1aa40097581ddb43548012df04bb686a900e5be1d72d0d52024b7432e5a1aa40496c865cb43548010ff0cb8686a90021f21970d0d52004b6c16ed21aa43197a80dda43548012f301bb486a90025be097690d5200596c168721aa40396f875ca43548092dd0cb9486a90125b2197290d52006a7a1ae521aa40087f865c643548010f90cb8c86a90025b60b7650d5200636c16eca1aa40087e869d943548012df04bb286a90025de057650d52194ba40aeca1aa40097b805d943548632f100bb286a90121fe087650d520243ec10eca1aa40096d82dd843548090ff053b086a90121f60a7610d520061fa14ec21aa400c3d429d843548018be653b086a9003174ca7610d52004b7c12ec21aa400c6f825d843548010fd0c3b086a9002cb60b4310d52005a6c148621aa40093f8750c43548012bf0ea1886a900e5ba0a74d855216cb6c14e9b0aa40097b805d361548632f100ba6c2a90021f61e64d85521943ec38c9b0aa432a768119361548072dd0539ec2a909e5b60a73d85521943ec3ec7b0aa400c5e73d8f61548654ed03b1ec2a9003950c763d85520043fc3ac7b0aa432a748158f615480187ee9322c2a90021fa1c
  | 11 => 0x50c014bb0610ecaa18029ea0021d95430053cc0043b2a8600a76819c36550c014eb03386caa19b697a0c70d95430052ec18e1b2a8600c79701c36550c010fd0e206caa18f21f61c40d95430052f41881b2a8600a6e821036550c014db04206caa18029da0440d95430053ac0881b2a860087d878c36550c014ed03186caa18029d60630d95430043f43e41b2a860087d87c836550c010fd0e106caa18021f61c20d95430051f42041b2a8600a3d840836550c014bd06106caa18029760c20d95430053b40841b2a8600a75810836550c010fd0e086caa18021f61c10d95430070fb2ec721a8600a6d82dd76250c014db043aec4a18021fe1571d89430243e42ae3b12860087f855c36250c090f90ab86c4a18021fa1f65589430063a38ecab128600c7870d956250c010fd0e32ac4a18031d1c465589430063c380cab128600c7765dc56250c018e8cbb8ac4a18031ed9770589430063c32ee0b12860087e87d956150c010fd0e32ac2a18121fa1b75581431e43e436eab02860087e87d956050c010fd0e32ac0a18da1fa1e625944300637b94c4b288615e2f429896510c1dc9e65312ca218568fa12725944345d1ec24e4b28860ea5e839c96510d154bb07392ca218da1fa1e42594430043ec3c84b28860ea5e839096510c014bb07212ca218da1fa1e32594430043ec3c64b288615a3e848c96510c0147b09192ca21b1297e0d71594430752e41ae2b288600a7a801c56510c014f30038aca218da1fa1e41594430043ec3c82b288600a7a809056510c014f30120aca218021fa1f21594430043ec3e42b28860087e870856510c010fb0e10aca218568fa1021594430051ec2042b28860ea5e830856510c014bb0610aca218029ea0021594430053cc0042b2886c3a3f845c16510c2b47908b82ca218029da0470594430053ac08e0b28863687e878c16510c010fb0f182ca218029da0630594430053ac0c60b28860087e87c816510c010fb0f902ca218021fa1c20594430043ec3840b288615a3e840816510c0147b08102ca2183a97a0c20594430052ec1840b288600a76810816510c014eb02102ca218021fa1c10594430043ec3820b28860487c85dd94310c790fb0dbaa86218021fa1d6550c431b43e43acaa188600c3c75dd94310c0187f0bbb286218030f2177650c430764f29eeca188600c9d53dd94310c0187ea5bb286218030fddb7550c430062e3aeeca188600c5f85dd94310c018b90bbb28621857279537650c430064eaa6eca188600c5f52dd94310c018beedbaa86218029b60a755884300537c12eab10860487e85dc56210c010fb0bb8ac4218121fa1770588430043ec2ee0b10862a96f825cf645480147d0830ec8a90029e60061d91520051ec3481b22a400a3d86103645480165b04206c8a930b4b5cb64991520051ec3ec9
  | 12 => 0x200800600a02c00400000000201c00604a00800000000800400000200000200400a00000200000800400400000002800401200000602000400600e00e00400002801000600c00000201801000400000800e00000800400000000601400400600c00a00600000a00001601600a00000202000804a00001200200a02a00000400000200200000000600a00200800400200000000000000405400000200a00400000000201801a01200200a00e00200602e00600200e00000000c04600200000600400800000400000400000000c00001000600000001000000200a00802600200200600400000800800000200600600002e04600800000200800201800e00400000000000000800600000000001000e00401a00200403201000802c00200800c00200202401a00000400000200000000600200a01e01000000003600000200400800001000c00400206e00800000000001400200800005201a00e00200400200202200000000000200000001400400400a01a01a00e00400400e01a00200000000c00000000001801000400200000200001400200000400001800403600801600200600e00000200000600000201e01000002400000a00000201200e00600200000800200401e02401600800600203401600401a00a00402000400001200a00200000c00e01401400401000001e02a00600002201400401001800e00000000001000c00200000403000000201200202600400805a00602201c00600000400800a00600001a00600a00401200600000000002c01a00004600400c00205200200000e00200001002400000001800200000200c00405000000000400800001a158ec8754962d0c090fd0bb8ac5a18021f6177158b430243f43eeab06860087d82dd560d0c010fd0e3aac1a18021fa1f52583430243e43ea4b06860e8ec875496290c090fd0bb82c5218021f6177058a430243f43eeab0c860087d82dd56190c010fd0e3aac3218021fa1f52586430243e43ea4b0c863c87d8718b6550c018dae4316caa18029ea0261d95430053cc04c3b2a8600a76819836550c014eb03306caa1a8297a0f74d95435051f426e7b2a8600c6d721cb6550c010fb0f216caa180297a0e42d95430052ec1c85b2a860087e8710b6550c790fb0e216caa18021f61e32d95430051f42465b2a8600a3d848cb6550c010fd0e196caa18f21f61c32d95430053d404e3b2a8600a79809c76550d0f47d0838ecaa18028f61071d95430063ab88e3b2a860087d879076550c014f50120ecaa18029e60241d95430043f43863b2a863c87d870c76550c0147d0818ecaa18029ba0831d954300536c1063b2a8600a7a800c76550c014f30018ecaa18021fa1f21d95430043ec3e43b2a860087e870876550c010fb0e10ecaa18028fa1021d95430051ec2043b2a8600a5e8308765
  | 13 => 0x2441789ccd186643d402c67c0000203208605fc4acad884c00170ce1c3c8ee00000000003a9318e991708200011751cc000634198388c68ed04182881c4618290000680001634000c280000000012e0629618e645ac00001c0a508ceb4000f057e8e218291e97ed8bc3bc93d474284000ae0a5c2c0ef4a098486255a19e153100d0f0ae8824e9d61c6c51edac000122ce1800156c000aa800165400000000003d7d46919bd40d7e0000b4cce40003c40003903819fdab4eb0a990e96996702fc000f44a49894ce09a00040000000004905740001757199101d82a00001d13d00004945b4000b5c060c3d664001a90b50000000f110780005dc2e034076cfe0d807a800000000046983800000000029c0009d80006cc000000000000000a20c38fdc0011280017b40000e8afc4f4651a68cecb214f4000888b1890162c8c52c80001b54b53280000012d80019e41a0d60638ad40000010200014c000125910dacd4ac0009215ac0011c01c0b014bd1695a9070941614f78000f20f7cf38000f84251050000bad6280007cc0010800015114204c434c0000014e00000011c400147c050000000c78000000000000ea8538b418ec97d1b127851d4f80014a425d2080009c0000cbd4d1324868a14ac98c84d00f56d00013419880009e40349045683000b8b14d70e6121439d36004c4e8738708d2d57d4c484806c0f19747b800018c7bcdc4ee4d8926cc198d07205e1539684ce82c981c6b812d23875ca04540f6c000001a4c0004c8000cb400195195c30c0016a5a04f585283c151469c8aca10bfd0080385ed91cf689915c164800141c00092c000d3cb9c4a50759b80ed2f98dd824171a5164c64857cb8da40358000789a20c6000000187400150597c9600008080011094647d12c54447d4000000000c900008319280000017f40000019a00000015705b15906d8000604000000001a14c5c00000094cb7c000cf02cd1a10919600000002550ed180fa99156800c0cb8794de19b05e51e4a44ab988d9410dc0000016596797c0d74000001884000000968018661289035784268fb02d400000000403400403602a00200200200a00401004600600000000000000a00000800400400c01a00200600a00a00200c00000603c00400400000e00800000600400800600200201000a00800401a01800200400800200c00201800200001000000400000c00004400a00000e00800e00e00c00800800200000400a00400800800000e01000601e00400201600600200604800200a00000000202c00c01800201c00600401000600600200800801000000200200200000001800c00e00400a00403c00600000800003800200400a00000000400202000000000400000000400400400002400e00200800a00200200600a00001200400800200000402801a00e00c00
  | 14 => 0x6cf357c40019a56100000005999084840009485a0c5800000000153c1dc00055c2253540084740000000001bc000b740000640006f04cc140000ea4000000000001754e54b581600008815cd8a40e072d0a0000000000000e69ae40002ac0805108a0d49150b0d0bc000000828000001605458be88a4001a00194c1c0011f4e7c7b4a6c4f0850818040338e50000001a64e35370b24000000264dbc83d028c559d4b44ec8ff824c730fd8a840d12b02617e59cc87d7f887501cc940000011f930c8f40015090a515550d5f8ba47c4d550b46fce45164000d1d85c000fa40008940011780018640009392c14b88cc000000001578000fcc9a42b41883a16b9a0c9f09552112ed0444f8351560fb4204e8cf8d5fcf2c0019f9048b1155c811768000b9905d31c2143e10540007f8cd40000000008e000171d830ecd55926527c49cbb041d859a880005893889881e80000000486ad0414794180899c94014d4b610157605c838c6709f48e80004e06404212355bc000bc54484143481c8780c659d9a28c485480011a8879330a380017440005345200000009280000000000000008714904880014d81b89703ec000000000d900012d40000016403aca6861dae919d9dd44cd018186f400166821d2ad9040000000000000ccea00003f527554423d89d240000bbcb346d160800132c00184d2a4000505160fa03315e56215813a13f4000af80000d49300018b81a51ac4c00018fc1e4dac1f889cb3000170911d8c078c1d4934000ffc8bd0f502c00115d74c0001080012553e52958998a0104000ed40015d4000d10f8840d60d3486e0d240009ac36463146c8d538d7140012ccdb9104bd805479c13928d2a94986bc09c000001aacd300015a4000f280003140005ccaf0000001188af40018900010113a54380008658cc43da311f1a2c7fda952814303b5a1d9f49e95dd3456ac000498758000b84dd00009d4000000d341f40006e87a400198ca0198167c000c14464c897dc7dcfe80f987cd640000019680000011b8000001820a818e4000000000001299794a700000018f91593ecd141a8839290360000bcc7500000014dd6603f9ab80e5568208308000000000dd80bcf645603dd90d9a94ccb64a7da380008140013b8000000098df4000754000000dc0cd80008c00017795994858a80005d55959b4aa00001fd7009840011016b48e5870db04100000006b4d280016a8000e900000010d000069413400000196d9c062cbdcbe080000097521c600001284778d054086a0dc8001314d5d36d93c000e70000278c40000000000000000c2c000f98000e94000000095135205064c000d903c000000a34000000b9159cca18b16940002e400033c000704000000001ad4aac344d8c14c4bcdf15c4790cf533976c0011849ed964a4c000aecabd5c9089
  | 15 => 0x8c751907ed2714057f00007d8000000d58f710cc000328000000cc5aa1ac8924edd1b563c0013949dc8d92e80c43240000000005e98b400000000068c0001cc0004d426c000fd0a4065cdec0a945d6cc000000c8d94c04408c000000000dd4bf8000a3cbe436c7c0ec4000d8437444c8982f474c000014274e312286a4ccd7b90996d98d4e840016e14e4744d0d3c84a890d880ef864cc21434000000f4d86c43400166cd389a8d511a51dda8c0002a895848da80451a2400085d24daa8000000c094103e4438001a70000f3088cad0c4d77c4dc0006895500000012fd7fc17c1ac42d5250e0614cc1124c998449657345a41593dc0013d8000148da0e0c0000000011942287e00004801800001843997313584700001444290e52e4e08128c50ef027c230e75094a6000001000000060d2f099954c3cc0011300016ec0016c1145ae00007a15d00a15f0e3c9b400114800000011d900000550765918a5000111847c500000000000d7c6ec69810000000000139c8b80840000000016dc7c8000000000000000ac00007719f0c3522485537cbd480d6240002bcfb8f950f89c8c113cc71835495c5781500000000019992bc5c4e6c66c6c0bc948cd09060b04295a61739574a293b55b172d6fc0016f944073d3b1a1986992d334cc8f000b00000000012683a40015b9300eac074000001954e88b0811856cfacf8063ced97b142c241374a9c000378b3da753e09808dce299e8f180018e925c001a999917100005bc000c040000000006e5588bf00011e16f15d8b80f503116e891cdb54282c46c8e2d704000f543f000197858d69c4044585b9790d98f410b94a00dc318804e594f00003fca2c2d0000001854001058724000000000911a7ccb00013ad788da96514714895200000014145582d8001938f3c000acc77d82c00025958534cebd0380004e4000000001a080005d81544a0ab4000a8898c001a9c581a107109090d945400000000032d7400007b028c0000000003d800060899c6218118d80012b52002f15ec00180d7d8761369030001840b2c728678d415e0090a199219348f07e46a94fd6c4cacd454506697bd6c93c50041b01310a8e48950e5c890a94e385944b51d4adc07d9440c9534ac4e791d09459c4aa4ec06dcd6cc4439598587952c6f8d95501554000000000334c313c17d00000010c98500000000017a0000000d200017a4001770ae4b48a1c2a52f4a756b02f8ff00007ad0196d4f153e9a84070e14031364d4cd9c835068bb943c02956443000081d12ce24585468368e053d5860bc00000000582197ad261a35114bec15c9c4915a6c6d4a54000cfd9d0a8c0012b8001a54740000000001600e002dd690918270001a5c6107e850ce10c7c19000052d8093914b113d1bc659ac40b524904c000eb80013f8124025798bd11
  | 16 => 0x1728000ba8000e40000408bb51c800000000129c7f00000004b8000280000000000000000001494000444000b282b12180000003b8238644000f25720df9800000448000c0cb54b1d07cbf4000eec0004600000000017cd75c00133c5152a00012dc00123000000053c0009bd024dfc000b78001924cf94c96f5120ff400000088496c168fc09945d00015489e0cdd31165c54d20d425a580000019ec00167413d18c00183447979c000001764f609d0001460efd774fed518f0d38473411530400000199c298c240006548f8000544001724f9059c00000000173cf4978c8fcf9d49cddc37d4ec200fe53f0e8193135c00000c0000794a85905c00012d03d13a8000a0c4fd7801f01640014e958d9598ad0c1a78d685f983c6758f010c2e80011fcde8845970000001630de420c8c8d788b0ba168c00097800046c8ec5f47749b15f4244564a90000841000c6c5a8110a309fc82c9b90ac858c81110a2517d085644ca4000cd0454000c840011d80019953fcf5d51cfbc16cfc48b43b0248f08530371add8f40000001eca65380000000a58768508384784001138525888120b704b1804c9cf1d814b387007155e93996a005d639abc1e1688424e4c31d3bc211540da48a8ca80adab0069a45351ad10b055514cc7019cee92502b80fd06c0000004d98e0001aa50fd0c537822c30445d7480004000008d02216bd30932000000000079914123d8c57c95296e4b6da48ab0b883e886c5f05197a8b9471c6842ed75870da3c2355b4f75198b690d44ed948dcc6b09f948035d09c5717519ac7f4fd5ad9220fc8000440748000000000a7
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x82210028c1aa036f80008000f28bb203400068ec0052c62673890003a01200000000041e0960820840c00000040050b64885dd94310c0144d922177650c430068a6086010064548016319118040191520061c1c4805916354801a45821843118d5200594640610c46354801645920c763d855200516640611cd6154801551901847358552006152047358d61548016299210364d81520050d644601d160548015319118074581520060e20074591605480181c7420d615815200515245321d9524c40144d920c47654931005136487518d43484014389050876549400050b648401d9525000142d921d46450d200041d660311d952440018718160076549100041e660401d95244001930845c570549100055424d715c152440015a19210374485100045ce5587cc740440011719521d414c1100066421d4350530440015c1920c77348110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x200a86400801910c132230080322a40081c6a4712016458d5200648304c80c2188c6a9002851a02047358d6154801418d09003a2c8b02a400c44210935c57054910
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x6
  | 5 => 0x94e
  | 6 => 0x94b
  | 7 => 0x98a
  | 8 => 0x98e
  | 9 => 0x9ca
  | 10 => 0x9cb
  | 11 => 0x9ce
  | 12 => 0x168a
  | 13 => 0x168b
  | 14 => 0x4
  | 15 => 0x168e
  | 16 => 0xa0a
  | 17 => 0xa0b
  | 18 => 0xa0e
  | 19 => 0x180a
  | 20 => 0x180b
  | 21 => 0x5
  | 22 => 0x180e
  | 23 => 0xb09
  | 24 => 0xb0e
  | 25 => 0xb49
  | 26 => 0xb4b
  | 27 => 0xb4e
  | 28 => 0x16c9
  | 29 => 0x16cb
  | 30 => 0x16ce
  | 31 => 0xb89
  | 32 => 0xb8b
  | 33 => 0xb8e
  | 34 => 0x1849
  | 35 => 0x184b
  | 36 => 0x184e
  | 37 => 0xcc9
  | 38 => 0xcca
  | 39 => 0xcce
  | 40 => 0x1709
  | 41 => 0x170a
  | 42 => 0x170e
  | 43 => 0xd09
  | 44 => 0xd0a
  | 45 => 0xd0e
  | 46 => 0x1889
  | 47 => 0x188a
  | 48 => 0x188e
  | 49 => 0xd49
  | 50 => 0xd4a
  | 51 => 0x589
  | 52 => 0x58a
  | 53 => 0x58b
  | 54 => 0x58e
  | 55 => 0x178e
  | 56 => 0x18ce
  | 57 => 0xe89
  | 58 => 0xe8a
  | 59 => 0xe8b
  | 60 => 0xe8e
  | 61 => 0x1789
  | 62 => 0x178a
  | 63 => 0x178b
  | 64 => 0x18c9
  | 65 => 0x18ca
  | 66 => 0x18cb
  | 67 => 0x98956
  | 68 => 0x94996
  | 69 => 0x9c956
  | 70 => 0x949d6
  | 71 => 0x180956
  | 72 => 0x95816
  | 73 => 0xb0956
  | 74 => 0x94b16
  | 75 => 0x16c956
  | 76 => 0x956d6
  | 77 => 0xb8956
  | 78 => 0x94b96
  | 79 => 0x1a09
  | 80 => 0x1549
  | 81 => 0x1409
  | 82 => 0x150a
  | 83 => 0x128a
  | 84 => 0x249
  | 85 => 0xca
  | 86 => 0x1449
  | 87 => 0x12ca
  | 88 => 0x289
  | 89 => 0x10a
  | 90 => 0x1489
  | 91 => 0x130a
  | 92 => 0x14c9
  | 93 => 0x134a
  | 94 => 0x2c9
  | 95 => 0x138b
  | 96 => 0x124b
  | 97 => 0x3c9
  | 98 => 0xcb
  | 99 => 0x15c9
  | 100 => 0x12cb
  | 101 => 0x409
  | 102 => 0x10b
  | 103 => 0x1609
  | 104 => 0x130b
  | 105 => 0x1689d6
  | 106 => 0xe89d6
  | 107 => 0x1789d6
  | 108 => 0xcd696
  | 109 => 0xe9696
  | 110 => 0x179696
  | 111 => 0xec9
  | 112 => 0x180a16
  | 113 => 0xd0a16
  | 114 => 0x188a16
  | 115 => 0x1949
  | 116 => 0x749
  | 117 => 0x3ca
  | 118 => 0x24b
  | 119 => 0x15ca
  | 120 => 0x144b
  | 121 => 0x40a
  | 122 => 0x28b
  | 123 => 0x160a
  | 124 => 0x148b
  | 125 => 0x16cb56
  | 126 => 0xccb56
  | 127 => 0x170b56
  | 128 => 0x1a0a
  | 129 => 0x17ca
  | 130 => 0x5ca
  | 131 => 0x184b96
  | 132 => 0xe8b96
  | 133 => 0x18cb96
  | 134 => 0xd1856
  | 135 => 0xe9856
  | 136 => 0x18d856
  | 137 => 0x104a
  | 138 => 0x58cd6
  | 139 => 0x58d16
  | 140 => 0xa4b
  | 141 => 0x128e
  | 142 => 0x198b
  | 143 => 0x150e
  | 144 => 0xbcb
  | 145 => 0x140e
  | 146 => 0x19cb
  | 147 => 0x154e
  | 148 => 0x5cb
  | 149 => 0x3ce
  | 150 => 0x17cb
  | 151 => 0x1a4b
  | 152 => 0xecb
  | 153 => 0x15ce
  | 154 => 0x74b
  | 155 => 0x40e
  | 156 => 0x194b
  | 157 => 0x1a8b
  | 158 => 0x104b
  | 159 => 0x160e
  | 160 => 0xe8596
  | 161 => 0x178596
  | 162 => 0x18c596
  | 163 => 0x178e96
  | 164 => 0x18ce96
  | 165 => 0x18d796
  | 166 => 0x95296
  | 167 => 0x95416
  | 168 => 0x14a
  | 169 => 0x169456
  | 170 => 0x168cd6
  | 171 => 0x168e96
  | 172 => 0x75611
  | 173 => 0x75791
  | 174 => 0xa1896
  | 175 => 0x5d5d2
  | 176 => 0x5d8d2
  | 177 => 0xb5716
  | 178 => 0x185316
  | 179 => 0x184d16
  | 180 => 0x184e96
  | 181 => 0x151296
  | 182 => 0x155416
  | 183 => 0x3d716
  | 184 => 0x3ccd6
  | 185 => 0x17da53
  | 186 => 0x1715d6
  | 187 => 0x1a57d3
  | 188 => 0x15ccd6
  | 189 => 0x41896
  | 190 => 0x40d16
  | 191 => 0x195a93
  | 192 => 0x189616
  | 193 => 0x1a9953
  | 194 => 0x160d16
  | 195 => 0x59316
  | 196 => 0x59456
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1770
  | 6 => 4992
  | 5 => 1723
  | 4 => 32
  | 3 => 6
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
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (72570+((h/590+packedAt gbK7 (65490+(h % 590)*12) 12) % 2570)*12) 12
  | 6 => packedAt gbK6 (261248+((h/1664+packedAt gbK6 (239616+(h % 1664)*13) 13) % 6590)*14) 14
  | 5 => packedAt gbK5 (108545+((h/574+packedAt gbK5 (101657+(h % 574)*12) 12) % 2274)*12) 12
  | 4 => packedAt gbK4 (2300+((h/10+packedAt gbK4 (2240+(h % 10)*6) 6) % 50)*6) 6
  | 3 => packedAt gbK3 (492+((h/2+packedAt gbK3 (486+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc3c0f0fe1ffffc3fc03c07f0b1b3cc19f793
  | 1 => 0xf03c00ff0fe1e01fc3fffff8015e5c7066c9fc
  | 2 => 0xffffff000ffe001ffc003ffffe60607f870e1f
  | 3 => 0x3ffffff000001fffffc0000f807f83f80fe0
  | 4 => 0x3fffffffffffe0000000000fff8003fff000
  | 5 => 0xffc0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x82404030120328cc0641a412601091c4085391
  | 1 => 0x92080051062141444294a9502016145022c0b4
  | 2 => 0x2c95990009540212a80212a586606029850c0a
  | 3 => 0x426eaaaa000049b312b0020cb806a82d80f40
  | 4 => 0x83b34cccd989700000c00c10deb000377a000
  | 5 => 0xcf00380881111802223023060ffdff7c000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeee0feeaece0feeeeee0feeaece0feeeeee0feeaece0feeeeee0feeaece0feeeeee0feeaece0feeeeee0feeaece0feeeeee0feeaece0feeeeee0feeaece0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_16795
namespace PEqualNP.Outside.L_meta_16795
open PEqualNP.Outside.L_meta_16795.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 26 := bs0_3_0
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
theorem bs0_4_128 : Interval s0Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 134 := (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128)))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 26 := bs1_3_0
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
theorem bs1_4_128 : Interval s1Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 134 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128)))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 64 := (concat bs2_4_0 bs2_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 40 := (concat bs2_5_0 bs2_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
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
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 29 := bs5_3_0
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
theorem bs5_4_448 : Interval s5Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 473 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 632 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 6 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 32 := bgb_4_0
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
theorem bgb_5_1696 : Interval gbAtlas 5 1696 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1723 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608))) (concat (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832))))) (concat (concat (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))) (concat (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)) (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)))) (concat (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696))))))
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
theorem bgb_6_3712 : Interval gbAtlas 6 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3776 : Interval gbAtlas 6 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3808 : Interval gbAtlas 6 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3872 : Interval gbAtlas 6 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3904 : Interval gbAtlas 6 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3968 : Interval gbAtlas 6 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4000 : Interval gbAtlas 6 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4064 : Interval gbAtlas 6 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4096 : Interval gbAtlas 6 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4160 : Interval gbAtlas 6 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4192 : Interval gbAtlas 6 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4256 : Interval gbAtlas 6 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4288 : Interval gbAtlas 6 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4352 : Interval gbAtlas 6 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4384 : Interval gbAtlas 6 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4448 : Interval gbAtlas 6 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4480 : Interval gbAtlas 6 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4544 : Interval gbAtlas 6 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4576 : Interval gbAtlas 6 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4640 : Interval gbAtlas 6 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4672 : Interval gbAtlas 6 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4736 : Interval gbAtlas 6 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4768 : Interval gbAtlas 6 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4832 : Interval gbAtlas 6 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4864 : Interval gbAtlas 6 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4928 : Interval gbAtlas 6 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4960 : Interval gbAtlas 6 4960 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4992 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))))) (concat (concat (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)))) (concat (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056))) (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)))))) (concat (concat (concat (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664))) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824))))) (concat (concat (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984))) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)))) (concat (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304))) (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464))))))) (concat (concat (concat (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)))) (concat (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912))) (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072))))) (concat (concat (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232))) (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)))) (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552))) (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712)))))) (concat (concat (concat (concat (concat bgb_6_3744 bgb_6_3776) (concat bgb_6_3808 bgb_6_3840)) (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000)))) (concat (concat (concat bgb_6_4032 bgb_6_4064) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160))) (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320))))) (concat (concat (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480))) (concat (concat bgb_6_4512 bgb_6_4544) (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)))) (concat (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800))) (concat (concat bgb_6_4832 bgb_6_4864) (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960))))))))
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
theorem bgb_7_1408 : Interval gbAtlas 7 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1472 : Interval gbAtlas 7 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1504 : Interval gbAtlas 7 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1568 : Interval gbAtlas 7 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1600 : Interval gbAtlas 7 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1664 : Interval gbAtlas 7 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1696 : Interval gbAtlas 7 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1760 : Interval gbAtlas 7 1760 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1770 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)) (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 bgb_7_416)))) (concat (concat (concat bgb_7_448 (concat bgb_7_480 bgb_7_512)) (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640))) (concat (concat bgb_7_672 (concat bgb_7_704 bgb_7_736)) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864))))) (concat (concat (concat (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312)))) (concat (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536))) (concat (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632)) (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760))))))
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
  · exact False.elim (Nat.not_lt_zero i hi)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeee0feeaece0feeeeee0feeaece0feeeeee0feeaece0feeeeee0feeaece0feeeeee0feeaece0feeeeee0feeaece0feeeeee0feeaece0feeeeee0feeaece0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
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
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071584 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample6 (r : Row) (i : Fin 6) := bit r (fullRoots.getD i.val zero)
theorem table6 : ∀ r, posted (sample6 r) = bit r fullWord := by decide +kernel
theorem raw6 : List.ofFn (fun i : Fin 6 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval6 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample6 r) = fullRoots.map (bit r) := by rw [←raw6,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample6 r)).trans (table6 r)
theorem binaryLower (low : Lower true fullRoots fullWord 10)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 10 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_16795.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,5]⟩,⟨.and,[2,3]⟩,⟨.or,[1,5]⟩,⟨.or,[0,1]⟩,⟨.or,[0,7]⟩,⟨.and,[3,8]⟩,⟨.or,[2,11]⟩,⟨.and,[9,12]⟩,⟨.or,[6,10]⟩,⟨.and,[4,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨⟨gs, o⟩, legal, hsize, correct⟩ := hs
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨⟨gs, o⟩, ?_, hsize, correct⟩
    intro g hg
    obtain ⟨op, len⟩ := legal g hg
    refine ⟨?_, len⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg)))
  · push Not at clean
    obtain ⟨a, ha, hop⟩ := clean
    have lo := binaryLower low gs o legal (fun x => correct x)
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot, hop] at e
    refine ⟨⟨mono, 16⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 11 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_16795

open PEqualNP.Outside.L_meta_16795 in
theorem PEqualNP.Outside.L_meta_16795 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
