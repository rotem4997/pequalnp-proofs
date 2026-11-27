import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15995.Model
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


end PEqualNP.Outside.L_meta_15995.Model

namespace PEqualNP.Outside.L_meta_15995
open PEqualNP.Outside.L_meta_15995.Model
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

def SBf (j : Nat) : Nat := [6, 6, 5, 5, 5, 5].getD j 0

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

end PEqualNP.Outside.L_meta_15995

namespace PEqualNP.Outside.L_meta_15995
open PEqualNP.Outside.L_meta_15995.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xa00300c19000d0401ce14008f1082c9004a0000df43be43bc43dc439c43be42bc42de32dc32be41bc41de31dc31bf40bd40df30dd30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40000050000000531c02c20000000000000000cf00000600030824d000291394412002080000821c794e438f290871e5110e3aa021c794e429b28c851e548caaca31947150328f29c832e529063ca918d394a318e2a0631c5350258a4a04d145408e2a6611c544c298a4985514530
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x30420859865210e0e6294443831895010e146154043
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (297+((h/5+packedAt s0K4 (272+(h % 5)*5) 5) % 23)*6) 6
  | 3 => packedAt s0K3 (609+((h/7+packedAt s0K3 (567+(h % 7)*6) 6) % 46)*6) 6
  | 2 => packedAt s0K2 (155+((h/1+packedAt s0K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffff03ffffffffffffff87ffff
  | 2 => 0xfc0fffc0fff80ffffc1ff03ff03ff81ff9ce73
  | 3 => 0xfff03fff03fff01fffe0ffc0ffc0ffe07e739c
  | 4 => 0x3ffffc00001fffff0000ffff00007f83e0
  | 5 => 0xffffc0000000001fffffffff000000007ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x844108482092040400a5245124510a8a0294a5
  | 2 => 0x2922948649215a8b2c0a522a522ad055394a52
  | 3 => 0x30a4a5121a4542b355409a889a88e5415c6318
  | 4 => 0xa2cb3a2490766cdd9a730c30ef3c41866f83e0
  | 5 => 0xc30c3c38e3878f1ee39cef3c0c30861877fc00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0fcc0ccc0ccc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15995
namespace PEqualNP.Outside.L_meta_15995
open PEqualNP.Outside.L_meta_15995.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x2002c740e2803400453022400000000001800003c00c400d00c20ef42ec42ef32ec32f741f441f731f431f721ee21ec21f421e421ef20ed20f710f510
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2440661268000e2a60002283047a281608001c01400880184045394f42b328e852e54ccacca3995594f41b3296833654cc6cca598d994621b32a0436454086cca610d914c21b2a80432c5448298a6905914520b2296213454442a8a6885914910
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x8b09198e54086266494c218919150086446354021
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (297+((h/5+packedAt s1K4 (272+(h % 5)*5) 5) % 31)*6) 6
  | 3 => packedAt s1K3 (602+((h/7+packedAt s1K3 (567+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s1K2 (155+((h/1+packedAt s1K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffff03ffffffffffffff87ffff
  | 2 => 0x1fc0fc07f03f01ffc3c1f03f03e07e07acccc
  | 3 => 0x1fff0007ffc001fffc01ffc003ff8007cf0f0
  | 4 => 0xfe0000007fffffffffffe000003fffffff00ff
  | 5 => 0xffffffff8000001fffffffffffc000007fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc0420820108208100442314518628a3005555
  | 2 => 0x54a9631ab23945af2c1d0d53629aa6c53acccc
  | 3 => 0xa930c5ab5450e9d755c216d9452db28a5cf0f0
  | 4 => 0x31a28a3468a28d1a9aab40820831c71c6f00aa
  | 5 => 0xc1c30c3870c30e1ce33398e38e01041077aa00
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaaaaa0000faaaaaaaaaaa0000faaaaaaaaaaa0000faaaaaaaaaaa0000faaaaaaaaaaa0000faaaaaaaaaaa0000faaaaaaaaaaa0000faaaaaaaaaaa0000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15995
namespace PEqualNP.Outside.L_meta_15995
open PEqualNP.Outside.L_meta_15995.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x9d43
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | 3 => packedAt s2K3 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s2K3 (17+((h/1+packedAt s2K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7ffff83ffff83f07fff07fff83fffc0f39f3f3
  | 1 => 0x87c1ffc3e0fffff8707f8783fc3c1fffd64c9f
  | 3 => 0xf801fffc00ffc3ff807ff803ffc01ff0e78f1c
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x800880400040008090088880444422009131
  | 1 => 0x2112910909522128342485112428894c524486
  | 3 => 0x12a52290d2a406538859502aca8152a2a58b18
  | 4 => 0x5539c42a9836ab9d5d0c4443733380c4f80ec0
  | 5 => 0x663187331cc733e66e6e667062220308ff6000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88eeaaeeaaeeaacc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15995
namespace PEqualNP.Outside.L_meta_15995
open PEqualNP.Outside.L_meta_15995.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x9d43
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
  | 0 => 0x7ffff83ffff83f07fff07fff83fffc0f39f3f3
  | 1 => 0x87c1ffc3e0fffff8707f8783fc3c1fffd64c9f
  | 2 => 0xf801fffc00ffc3ff807ff803ffc01ff0e78f1c
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x800880400040008090088880444422009131
  | 1 => 0x2112910909522128342485112428894c524486
  | 2 => 0x12a52290d2a406538859502aca8152a2a58b18
  | 4 => 0x5539c42a9836ab9d5d0c4443733380c4f80ec0
  | 5 => 0x663187331cc733e66e6e667062220308ff6000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8eaeaeaeaeaeac8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15995
namespace PEqualNP.Outside.L_meta_15995
open PEqualNP.Outside.L_meta_15995.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xcd32
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | 3 => packedAt s4K3 (i*16) 16
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s4K3 (17+((h/1+packedAt s4K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffff03e0f83f0ff0ff0ffff83c1e0f667e93
  | 1 => 0xf07c1ffffffffff07f07f0703fffffff9993ff
  | 2 => 0xff801ffc00ffc3ff8007ff803fc01ff0e1e31c
  | 3 => 0x1fffff0003fffff800003fffe000fe03e0
  | 5 => 0xffffe000000003ffffffffffc0000000fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2119011845115101902902919a245226222691
  | 1 => 0x4002221004000202102102200490488089026
  | 2 => 0x622b5448d6a5175688a5ab04aea09962e16318
  | 3 => 0xcb53989294359b9b5ab08a093732d044f603c0
  | 5 => 0x8c6210e318c622ec6cc6cc4e04030188ddd800
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaccc8ccc8eeeaeeeaccc8ccc8eeeaeeeaccc8ccc8eeeaeeeaccc8ccc8eeeaeeeaccc8ccc8eeeaeeeaccc8ccc8eeeaeeeaccc8ccc8eeeaeeeaccc8ccc8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15995
namespace PEqualNP.Outside.L_meta_15995
open PEqualNP.Outside.L_meta_15995.Model
def s5K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xcd32
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (i*5) 5
  | 3 => packedAt s5K3 (i*16) 16
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (6+((h/1+packedAt s5K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s5K3 (17+((h/1+packedAt s5K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffff03e0f83f0ff0ff0ffff83c1e0f667e93
  | 1 => 0xf07c1ffffffffff07f07f0703fffffff9993ff
  | 2 => 0xff801ffc00ffc3ff8007ff803fc01ff0e1e31c
  | 3 => 0x1fffff0003fffff800003fffe000fe03e0
  | 4 => 0xffffe000000003ffffffffffc0000000fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2119011845115101902902919a245226222691
  | 1 => 0x4002221004000202102102200490488089026
  | 2 => 0x622b5448d6a5175688a5ab04aea09962e16318
  | 3 => 0xcb53989294359b9b5ab08a093732d044f603c0
  | 4 => 0x8c6210e318c622ec6cc6cc4e04030188ddd800
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xeeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8eeeaccc8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15995
namespace PEqualNP.Outside.L_meta_15995
open PEqualNP.Outside.L_meta_15995.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x98504200000001c8a9c0000000387940020989f148000800f9283162105800000020e9216910881979a9b900f0906860d001d108b1e82801701071f951d800b880e219b13930a19848c1598190d9e1a0c9184082004a0022000091e14585001c480008c080007fd5001fe54007f55001fc54007fd4c01fe53007f54c01fc53007fd0c01fe43007f50c01fc43007fd4801fe52007f54801fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc32007fd44017f51017f94401fd51005f54405fc51007fd0401bf41017f90401fd41006f50405fc41007fcc405fe31007f4c405fc31007fc8405fe21007f48405fc21007fd4003fe50007f54003fc50007fd0003fe40007f50003fc40007fcc001df3000ff8c001fd3000774c003fc30007fc8001ef2000ff88001fd20007b48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x2e4003fbd9320007dcc990003ed64c8007f63264000fbd5320007dca990003ed54c8001f62a64003fbd8f20007dcc790003ed63c8007f631e4000fbd4f20007dca790003ed53c8001f629e4000fbd0f20007dc8790003ed43c8001f621e4003fbd8720047dcc390003ed61c8007f630e4000fbd4720006dea390023ee51c8001f6a8e4000db54720047d8a390003ef41c8001d7a0e4008fb90720007da8390003ad41c8011f620e4000fbcc720047dc6390003ed31c8011f618e4001bb5832000fdea190007ee50c8003f6a864001fb1432000fde8190007ee40c8003f6a064001fb1032000fde6190007cf30c8003f71864001fb4c32000f9a6190007ec30c8003f78864001fb8432000fd82190002ff6548001bfb2a40009fd9520035fcca90002fd654800d7e32a4000df19520004f8ca90002ff6448001dfb224000afd912002dfcc890002fd644800b7e3224000ef1912000578c890002ff63480097f31a4000bf58d20025f8c690006ff6248001f7a924000fb94920007daa490003ec5248001f7a124000fb90920007da8490003ec4248001f79924000fb8c920007da6490003ec32480017fb0a4002bf98520015f8c2900037f5148001bea8a4000efd05200077a8290003ef214800ff710a4000fb4852003fd84290006ff6048003ef9824001f74c12001ff64090007ee2048003f61024001fe0812000ff42090003ef6548001b7b2a4000fb99520007daca90003ec6548001b632a4000fbd91200075ec890003ee6448001f6b224000fb1912000758c890003ef5448001f72a24000fb55120007d8a890003ef6348001f731a4000fb58d20007d8c690003ef5348001f729a4000fb54d20007d8a690003ef4348001f721a4000fb50d20007d88690003ef614800ff730a4000fb5852003fd8c290003ef5148001b7a8a4007fb94520007daa2900036d514800ff628a4000fbd05200075e829001fee4148001f6a0a4000eb5052003fd88290003ef314800ff718a4000fb4c52003fd86290007ef604800377b024000fad812000fdea090007ee5048003f6a824001fb1412000fde8090007ee4048003f6a024001fb1012000fde6090007cf3048003f71824001fb4c12000f9a6090007ec3048003f78824001fb8412000fd42090007ec10480017fb2a2006bf99510005faca8801afc65440017fb222005bf99110005fac888016fc64440017fb1a2004bf98d10005fac688012fc63440017fb122003bf98910005fac48800efc62440037fb0a2002dfd4510017eca28800b7d5144001faa8a2000dd545100177e828800bf64144005dea0a2000fd505100076a8288006ff6044003ef9822001fe8c11000fba6088003f93044001ec9822001fbc811000ff44088007ed2044001fc9022000fa48110017f62088007f61044003fa0822001fe04110
  | 1 => 0x3dc31cc0037eb066001f78c33000ff46198007dc30cc009efb2e6000f799730007bacb98013dc65cc009efb266000f799330007bac998013dc64cc001efaa66000f795330007baa998003dc54cc009efb166000f798b30007bac598013dc62cc001efa966000f794b30007baa598003dc52cc001efa166000f790b30007ba8598003dc42cc009efb0e600af798730007bac398013dc61cc001efa8e6000d7d4730057bca398003dd51cc001aea8e600af714730007be83980039f41cc015ef20e6000f7507300073a839802bdc41cc001ef90e600af788730007ba439802bdc21cc0036eb066001f7d433000fbca198007dd50cc003ee2866001f7d033000fbc8198007dd40cc003ee2066001f78833000fb84198007df10cc003ef0866001f704330005feca980037f654c0013fb2a6006bf99530005faca9801afc654c001be32a60009f19530005fec898003bf644c0015fb226005bf99130005fac898016fc644c001de3226000af1913000dfec698003df534c001ef29a6000f754d30007b8a698003df434c001ef21a6000f750d30007b88698002ff624c0077e3126000f7cc930007bc6498003dd324c001ee1926000bfd8530015fcc29800afc614c001bfa8a6000df545300077e8298003bd414c001ef98a6009f78c530007ba6298027dc314c0037fb026004fecc13000fbc6098007dc304c003fc1826001fe84130007beca980035f654c001ef32a6000f759530007b8ca980035c654c001efb226000e7d9130007bcc898003dd644c001ee3226000e719130007bea898003de544c001eeaa26000f715130007bec498003de624c001eeb126000f718930007bea498003de524c001eea926000f714930007be8498003de424c001eea126000f710930007bec298027de614c001eeb0a6009f718530007bea2980035f514c013ef28a6000f754530006baa298027dc514c001efa0a6000e7d053004fbc8298003dd414c001cea0a6009f710530007be4298027de214c001ee90a6009f70853000fbec098006df604c001edb026001f7d413000fbca098007dd504c003ee2826001f7d013000fbc8098007dd404c003ee2026001f78813000fb84098007df104c003ef0826001f68413000fb8209800eff65c800d7f32e4000bf5972001df8cb9000eff64c800b7f3264000bf5932001df8c99000eff63c80097f31e4000bf58f2001df8c790006fe62c8001f7a964003fb94b20007daa59000fec52c8001f7a164003fb90b20007da859000fec42c8001f79964003fb8cb20007da659000fec32c80057f30e4000bf58720015f8c3900037f51c8001bea8e4000efd07200077a839000fef21c8011f710e4000fb4872001fd84390006fd60c8003ef9864001f74c32000fdc4190007fa20c8003f61064003fbd9720007dccb90003ed65c8007f63
  | 2 => 0x310177e839880bbd41cc405ef18e6202fd8c731017b86398806fe60cc4017eb066201bf18331005feca9881afe654c4017eb2a6206bf19531005fec898816fe644c4017eb226205bf19131015fec698802ff624c401f7b126200bbd893101df8c498803ec624c401763126200f7cc931007ba649880aff614c405bfa8a6202df545310177e829880bbd414c409fb98a6202f78c531017b8629880bf4314c4017fb026201bf9813100df8c09880eff65c840d7f32e4200bf5972101df8cb9080eff64c840b7f3264200bf5932101df8c99080eff63c84097f31e4200bf58f2101df8c79080afe62c8407f71964200fb4cb21015fac39080b7f51c8405bea8e4202efd07210177a839080bee21c8405fb10e4202fb0872100dfcc190802fd60c84037e3064200bfd9521035fcca90802fd654840d7e32a4200bfd912102dfcc890802fd644840b7e3224200bfd8d21007bec690802df63484097f31a4200bf58d21025f8c690803dc63484016e31a4202bfd8921007dc6490803ed32484057fb0a4202dfd4521016faa29080bbf4148405dea0a4203fdc8521017dc429080bec2148405fa10a4200bfd812100dfcc090806fc60484037f32ea005bf99350005fac9a801b7f54d4001beaa6a004bf98f50005fac7a800efe62d40017eb16a002bf98750005fac3a800afc61d400dbfa8ea000df547500077e83a8003bd41d40037eb06a001df9435000ff4a1a80077c50d40037fb2aa000bfd91500077ec8a8002bf645400b7e322a000ef1915000578c8a80037f5454001beaa2a000bfd8d50025f8c6a8002ff62540077e312a000bfd8550015fcc2a800afc6154001bfa8aa000df545500077e82a8003bd41540037fb02a006fed415000efca0a80077c5054003fc282a005bfd9740035fccba0002fd65d000b7e32e8001bf9934002f7ca9a0003bd54d00097f31e8000bf58f4001dfcc5a0002fd62d00057f30e8000bf58740015f8c3a00037f51d0001bea8e8005efd07400077a83a0006fd60d0003df2068001fe9034000f7881a0002ff6550001bfb2a80009fd9540035fccaa0002fd655000d7e32a8000df19540004f8caa0006ff6450001df2a28000ef55140005fec6a0012fc63500017fb128003bf18940005fec2a000afe61500057e30a8000dfd4540006faa2a0003bf4150001dea0a8001bfd814002ff680a0007be4050003de2028001fe10140025fecb9801afe65cc0017eb2e6004bf19730025fec998016fe64cc0017eb266004bf1933000dfcc798003df53cc009ef29e6000f754f30027b8a798003df43cc009ef21e6000f750f30027b8879800efe62cc0017eb166004f7ccb30007bc6598003dd32cc009ee1966002bf98730005fac39800afc61cc001bfa8e6000df547300077e8398003bd41cc009ef98e600af78c730007ba639801
  | 3 => 0xea12a200df10951006fe64a88037e3254401be992a200df0c951016fec2a880a7f6154401bbb0aa202df90551016f882a880b7e3154405be18aa202df88551016f842a88037f605441bbf302a200df5815106ef8c0a88377e405441bbe202a20ddf8c15106ef860a88377e205441bbe102a202dfc4151016ee20a880b7e1054405be082a205bfd9741035fccba0802fd65d040b7e32e8202bf993410077ea9a0817be54d0401deaa68205ef15341025fcc7a0802fd63d040bdfa1e8200ef90f410077a87a0817bc43d04077f3168200bf58b4102f7e85a0803be42d0401dea168205ef10b41015fac3a080b7f51d0405bea8e8202ef90741017ec83a080bbc41d04037f3068200bf5834100df8c1a0833be40d040bde2068205efd97410077ccba0803bd65d040bde32e8205efd8f410077cc7a0803bd63d040bde31e8200efd4f410077ca7a0803bd53d0401de29e8205efd8b410077cc5a0803bd62d040bde3168200efd4b410077ca5a0803bd52d0401de2968200efccb410077c65a0803bd32d0401de1968202af587410177ea3a080b3f51d0405df28e8202ef547410167aa3a080bbc51d0405df18e8202ef0c7410177c43a080bbc21d040bdfb06820cef983410077ac1a0817bc60d0419df286820cef143410677c61a0833bc30d0419df106820cef083410177e21a080bbe10d0405de0868200bfd9541035fccaa0802fd655040d7e32a8202bfd91410077ea8a0803be5450401deaa28200ef15141005fec6a0803df63504016fb1a8204bf18d41007b8c6a0802dc6350401dfa1a8200ef90d410077a86a0803bc43504017fb128200fbd8941005dec4a080efc6250401f63128200bb189410077e84a0803be4250401dea128200ef10941015fec2a080b7f5150405bea8a8205fdd05410177c82a080bbc4150405fa20a8200bfd814100dfcc0a0806fc6050417df202820bef10141017ee20a0803bf6550401df32a8200ef5954100778caa0803bf6350401cfb1a8200ef98d410077ac6a0803bc6350401ce31a8200efd4d410077ca6a0803bd5350401de29a8200efd89410075ec4a0803be6250401deb128200ef1894100758c4a0803bf5250401df2928200ef5494100778a4a0803bf3250401df1928200ef4c9410077864a080bbf61504055fb0a8200edd85410177ea2a080b3f5150405df28a8202ef545410167aa2a080bbc5150405df18a8202ef0c5410177c42a080bbc2150401dfb02820bef981410077ac0a082fbc6050417df282820bef1414105f7c60a082fbc3050417df102820bef081410177e20a080bb71050405df0828202ef04141025fecb9881afe65cc4017eb2e6204bf19731025fec998816fe64cc4017eb266204bf19331015fcc79880efe62cc4017eb166204f7ccb31007ba659880afd61cc405bfa8e6202df547
  | 4 => 0x12ff64cc80b7f3266400bf59332025f8c999003df53cc809ee29e6400f7d0f32027b8879900afe61cc8017eb0e6402bf1873208fdc4399047ec21cc8037f3066400bf5833200df8c19900eff658c80d7f32c6400bf5963201df8cb1900eff648c80b7f3246400bf5923201df8c919002fd638c8077f3146400fbd4a3201fd8a519003ef428c807f62146403f7cca32027de651900afe618c8017eb0c6402bf18632087bc6319043dc318c8037f3046400bf5823200df8c119002ff654c80d7f32a6400bf59532035f8ca99002ff644c80b7f3226400bf5913202df8c899003df534c801ee29a6400f7d0d32007b88699003ef524c801f62926400fbd0932007d88499013ef324c807ef1926400bfd8532015fcc29900afc614c8017fb026401bf9813200df8c09900eff650c80d7f3286400bf5943201df8ca1900eff640c80b7f3206400bf5903201df8c819012fe630c8077f3106403f7cc83201fdc641900fdd320c809f69906400f34c832015fcc219002fd610c8057e308640ff78c432027b8621903fee210c807f61086401bf98032005fac019006fc600c8057f32ea205bf99351005fac9a881b7f54d4401bf2a6a200df55351036f8a9a8812fe63d44017eb1ea206dfd4f51006fca7a88037d53d440dbe29ea203bf98b51005fac5a881b7f52d4401bf296a200df54b51036f8a5a880afd61d4405bf28ea202fd94751016f8a3a8806fe60d44017eb06a201bf18351076fca1a881b7c50d440dbfb26a200df99351006fac9a881b7c64d440dbfb1ea200df98f51006fac7a881b7c63d4401bfa1ea200df90f51006fa87a88037c43d440dbfb16a200df98b51006fac5a881b7c62d4401bfa16a200df90b51006fa85a88037c42d4401bf996a200df8cb51006fa65a88037c32d44053eb0ea202df90751016f883a880b7e31d4405be18ea202df88751016f843a881b7f60d441dbf306a200df58351036f8c1a883b7e40d441dbe206a20edf8c351076f861a883b7e20d441dbe106a202dfc4351016fc21a880b7c10d44057fb2aa200bfd915102df8c8a88037f5454401bf2a2a200df55151006f8a8a8802ff6354401efb1aa200b7d8d51025f8c6a8803dc63544016e31aa200dfd4d51006fca6a88037d5354401be29aa200bfd8951007dec4a8802ef62544077e312a200fb18951005d8c4a88037f5254401bf292a200df54951006f8a4a880aff615440dfba8aa202df94551016f8a2a880bf451544017fb02a201bf9815100df8c0a88377e505441bbe282a202fdc4151006fec8a88037e6454401beb22a200df19151006fec6a88035f6354401bf31aa200df58d51006f8c6a88035c6354401bfa1aa200df90d51006fa86a88037c4354401bfb12a200dbd8951006fcc4a88037d6254401be312a200db18951006fe84a88037e4254401b
  | 5 => 0xc74300dfcc1a1802fd60d0c037e3068604bfd9643035fccb21802fd6590c097e32c8600bf592430077ca921803bd5490c097f31c8604efd0e4302fbe872180efe6290c09f73148600bb98a43005fac521813ed6290c0176b148602bf98643005fac32180afc6190c037f3048600bf5824300df8c121873be4090c39de2048600bfd9543035fccaa1802fd6550c0d7e32a8605f7d0d430277c86a1802ff6250c077e3128600bfd8543015fcc2a180afc6150c017fb028601bf9814300df8c0a1812ff6510c0d7f3288600bf59443025f8ca21816fe6410c0bdf2a08600ef55043025fcc621813bf4310c09ef2188604ef50c4302fba862180efe6210c017eb108602bf98443005fac22180afc6110c37ef1888604f70c44300dfcc021802fd6010c037e300861aef9004302f788021816fe64d480ddf326a400af99352005fac9a901bbd64d48015eb26a404bf98f52005fac7a900afe61d48017eb0ea402bf187520cfdc43a9067ec21d48037f306a400bf5835200df8c1a9002fd659480b7f324a400bf59252006fea9290037d54948097f31ca403f798e52005bcc729002fd6394807eeb1ca400b758e5201dfcc52900f7f529480df7a94a402bf98652005fac32900afc61948037f304a400bf5825200df8c1290637e5094831be284a400bfd915202df8c8a9002ff63548097e31aa406fbd495201efca4a9002ff61548057f30aa402bf18552005fec0a9006fe60548037e302a406bf9945202dfcc829002fd641480dbfaa0a400df55052025fcc629002fd63148077f310a403dfd485201fdca42900f7d521480df6a90a402bf98452005fac22900afc611482ff7108a403fb0845200dfcc029002fd60148037e300a416df94052036f8a029016ff65d080d7f32e8405df99742004fccba1002fd65d080bbeb2e84009f5974202df8cba1012fe63d08017eb1e8402bf98742005fac3a100afc61d082bf710e8415fb0874200dfcc1a1002fd60d08037e3068403bfd9642035fccb21002fd65908077e32c8400bf592420077ca921003bd54908097f31c8403f798e42005bcc721002fd6390807eeb1c8400b758e4201dfcc52100fbf429080bf7a148402bf98642005fac32100afc61908037f3048400bf5824200df8c121053be4090829de2048400bfd9542035fccaa1002fd655080d7e32a8400bfd8d42025f8c6a1017ef4250807df2128400bfd8542015fcc2a100afc61508017fb028401bf9814200df8c0a100eff651080d7f3288400bf5944201df8ca21016fe641080bdf2a08400ef55042025fcc621002fd63108077f3108403efd084201fdc842100fbd421080bf6a108402bf98442005fac22100afc6110827f71088403fb0844200dfcc021002fd60108037e3008412ef9004202f788021012ff65cc80d7f32e6400bf59732025f8cb99
  | 6 => 0x400000403400c00402000002c00000800800800800000000400002000401c00401400001400000001c00801400000802807001c0140000000040180a000800800000000401c02000000409402800000800000000000000401001800000c00000c00400c04800001001400401c00000800800000001c02000005c03000400001000001004400401800800000000006c00800400800c01800401801c00c04c01000800c00400001402800001802c00001400c00400406404000401400c00000400400000801401400001400800000000400000800000c01803000001800400000000000000402401402800001402402007000c00400000400002400400800c00c00001404400c00803401000003800000004c00800000c00400c00000400c02001000400802400000002800c04000000000c01c00000000000800800800000800001c00001c097f31ea800bf58f5401dfcc5aa002fd62d50057f30ea800bf58754015f8c3aa006fe60d50017eb06a801bf183541277c81aa093bc40d50017eb2ca805bf9925402efea92a01bbf54950019faa4a804bf98e54005fac72a00efe62950017eb14a802bf98654005fac32a00afc61950037f304a800bf5825400df8c12a08f7e5095047be284a806efd515402efca8aa002ff63550097e31aa800bfd895401df8c4aa002ff61550057f30aa802bf18554005fec0aa006fe60550037e302a806bf9945402dfcc82a0177f541500bdf2a0a805df550540377aa82a0033d54150097f318a800bf58c5401dfcc42a002fd62150057f308a800bf58454015f8c22a006fe60150017eb00a801bf18054116fca02a01b7c5015045df200a805ef1005402dfcc9a981bbe64d4c015f326a600bf593530377ac9a9802bd64d4c077f316a600bf58b53015fcc3a9802fd61d4c057e30ea621f78c75310fb863a9806fe60d4c017eb06a601bf18353005facb29816fe6494c017eb24a600dfd5253006faa929812fe6394c09bfa9ca606f7d4e53006bea72980efe6294c09f7314a600bb98a53005fac529813ed6294c0176b14a602bf98653005fac32980afc6194c037f304a600bf5825300df8c1298837e5094c41be284a600bfd915302df8c8a981bdf5354c09bf29aa600bfd895301df8c4a9802ff6154c057f30aa602bf18553005fec0a9806fe6054c037e302a606bf9945302dfcc829802fd6414c0dbfaa0a600df55053025fcc6298137f5314c09ef298a604df54c53037baa62980efe6214c017eb10a602bf98453005fac22980afc6114c3fef188a604f70c45300dfcc029802fd6014c037e300a61edf94053036f8a029816ff65d0c0d7f32e8605df99743004fccba1802fd65d0c0bbeb2e86009f5974302df8cba180efe62d0c017eb168602bf98743005fac3a180afc61d0c3bef18e861df70
  | 7 => 0x8d1adc0ffa100001ab80000000c80000026918724a950a698000002840bd8000002bb2188001700a713c0ba80002f9eb2d080003e12294b2769df97d04501618d80000006780000003a1cc9410df2748000ee27d0e9093a289510002229a39478001ed2e21178002ce9e9a661661ae1a203d00009989800000018204a04000013e0000001da8001f08408000000c42c50000001ba8000000000b813a0000a400020c015aaa828a4d8232b599112e829160aa68852a8a0ea512578af13cad30000001f900000000000000003f98a2538000c4a5a80000000023b9140002c200000000014895ba449321ed80702380000005806d8000178001f400002794d2e18740460002ab0498000000002ae000000072816a480e72a99b3a4d2a1a572cc15198d2d416584d181ac6a121fd02006e0e225c0319bf99d1aea3205a8000002e0800043809a030930000898001f800000003400000006a00000580000000000000000000006b00000000023b27d85dad80f080000022419595227b2a52308c3a4e1168ae0002b480d8f6000264a7320080000019c8a09330001248cd94b8d8088a8e0380002a20001aaa83a2da290aaa942150280df80495c85503ba991deabe1cc25d0002df08da3a80007f0000001730bb00180025580000000002a1828000001e89338000001be8cd24c00009c26d0d60f800020216283880000022e2960000000002968000000001ea87722c0001960000788000ed96c8001d22cfaad84b00000010b0dc0000cca2b1432931fb88c80017c0001550001892d528026f06706696bada9c499491626b97b03280000018b8000e2a56ad7000000000000201ae100008f04592780014e2cb800400400000c03002800002000802800401400000800400c00800000001000004800000000c00c00000400c00401400400000801400800400400000c00001402c00402400000800c00000400000001401400401400800000c00400400000800000800403007400000c01001c02400400400400403400000000803800400000400400400400400003400000c01001400000000800400003000005401000000000402000400800c01400800000400001801800000403405000000000000401400400000406402800803800400400400003c00000400000800801801001400c00000000000000000801001c05005800800000400002803800000c00c00802c01400803800000402c02800c00c01001002001007401409000400000801800800c0380c000000401001001000000000000000c00000000001001000c01000002c01800803400800401800001800802c0c400800400c00000003400400000401401001001402003800000400401000000000000000400000006003001c01800000800004401008400001401802000800400000002002c0100
  | 8 => 0xa80fe1bb9920478001dd1f192815a0948000001ba08a19e1788000b012000c14611fa63032236873a058000001408000f5a0c8000c602d8000e99940001df0ec21d86500000000015800000018409b92080004e1b8800073234870a889f5a870d79e28780000171a314c80013424a1dc8000f28000000000992742350d680018e24980024395c0000961f8a0fabd8250e08000000000942249098f98002798002042592380000639808449868bb96788b0001710000000000000002858880430000000002708000000f480021d00029c07d8000000001b10001c98000000fa04d8000c10000eb94a99ea6813700b00012c8002bd0a301100000004193b0001979602a610e0de26890628797f03484885a0b48000000c78001e00002d000027e0c700000006800000020e0001b096fa619fcadba0d802a4312382e850a9780014c0000002980e38000b68002c2800000000059a161fe8f72658000000e0097000083a3a0000000000000000001fb11e80016ea5501b0000000000000001138e6928824969000168a970002af0000000e5a230140030000000002221a480029b80017d8000000b70fca420002de98800000010413f8000d980012127108e92c29dab51540d513f00008a85000000000000006d0000000000d10bea908f20a8a6f81a000081a2a0660000c680018c2280021fe0210368000b09b424b23f1790fb9e11490a92c5ad980000001996115f00029b0001bd80014f1e180021f1a880009d23700000000000025419f8a289e99b000129a8a1e413a8910000c88000001d70000000000000000000000001c380000000020900000005900010f19da39a3e80000029a000135a5d8000000002621240000002ce28c0000001108bd0001ea2db0c922c8001f212aad92ab9ff8002181390001e90000000d200000003c9250000540ea8f19459781570000002b02920bf2ba217807a7f0001f980006b8001b506f96f0dd80003d9d99d524c9f390c0000cf9019cf93122e95d80024f2d89b5a6528225b0f6a8f0312060002bc8641970ce2462bf177884196a7c2341989ca862054ac18b417627a94a1081b90b39d30001b18001c28000fa8000000000000000fd1590791a700000000000019c0001848000000000858001e2162143857abc1de2111c00610c511f0b89ad9bf01aa3880007aa5a19027000000023e2b78001aa1670000968001ec00000011d8002300000e6020a2f00128b80018f153a7e8bf82207ea939d5a048950219c7ad59101f480029580007c0001ad0001cb91ba8087119a2c997e8929da0000000000420f78000002bf80013086980013ea2680000000027f8002cca7715d1708000609349e5a679198092928088da944aa403780021b0000000000588b7a4112d21a9182d602a8719360ec8000000000f41899b6029
  | 9 => 0xd0a19f01268270c81bb28824bad78000000000001640000000000001d8892193a050f023da762ad04101300025989b2478002082a49859480000000000002c380010a08705600012585c2a913d8262d480001b8001af0428052e025e0a99a293680000000000000000005586c8ee80029496a09893980000024f8002208000000000ad0ea23288084680012221fa62a601ef16e1720000001d1a581f311e202a950002b191522aa29a73ac0a8b2440000002132848442998002d38ba00616d1148001e0a6c8b2278166a6420d1190471a58258a80e7a0f1270e80002c818b25f8002429e82c4aca25601c88e19a897a31ab70391fa28aaa08fc1379750000149260be29d0748d42cd2d284c80010d9402b327298612e2a7a5c9470118fb04e800220100277aa000008780000020a97c8758a38000000dba53233a1401000023100012180006c2c420796b03500002c8000000000002c10001c69fc0cc25f00000000000000000000000000f0000ad8001c18c9a3790700000000000021728d0da00000000000019317a86f2409718002cb00025889a8001b480000004c00026c00015891c04f0080d30002b614400000021e800003856ad19bc9ee8000002088000001d600000010e833974800035ab09f727a1f6a6d91c88280005b8b91319980001058ab05d0000002828b52608e485c9d3a6b0000db2afadf8a01c424881c14f8d929e83c0511d91ce80018113824697980007a03aa891159f60002c7a3d29a8000832670caa868b988c152ab2a3588103722f80015fab9a9127b94eadc81f8d08001ff0001a1aa29578000000002522da0cf0658000001ab0001188648001b20002818000300001bc1618229a114280022380021294d9d78002b40f3ae292323c0000000b30000002518761030e30fd95e86a8001a69d11631d08d8a6aa66a2727188d20a00005207d0001bd0000720008000ef80000000000000000000000000000000028c8000000001650190000d49c51ac8750000001888000000000139e78000000000001c59cd8000001dba471770ca2ca80029013b90c8a4a63983a78aa30a615aab385e2d683f2bba1190b9c319995e24eaae8c1ab900015000012b00008b80024900000680010927590d1029a0a792bea5b80e82c0e50a51e69569e51eb98a87002b80000000028f8001ac05ea720ab90520389d9418000539c21fda261d81a92a387e2012de077800000138a548000c080f85b0dea198150529e39b289f1952331599c600008020b1699d40001350002b80001b711117284b80000000000007ba0680000009c80000018f92a175a1c1451878000000ed1afa8d80000a117026a750330958a7aba80029f91b1048002ac0002cf03e9469909530240000f8a452c001080029f00018e8ae80000004aa5ea8e80007f96827c9c82
  | 10 => 0x22d11a22b9800000518cb9ef9008c21d0298ab68e400000000000015496380000012f0000002b88002aa0001a980016a8628000f510680009f8690000002a59010000000b60d280000012f9be00011d0000ac80002d0618000001831c10001b69088490769c08000002d200021685f0000000d000017f9fa8000001739421290000d728523900004f81d82f291ac30cb26e8000f90f11990002b22860001f10890000c30000000002070688000000000c000018c83612d9122831dc03980021581280000000029c9021cf0aa2610a219f12b9ce0821c70908001648001d2a811e309003b26a0000001dd9558000530000001078000001918e88002459e493d1f2a1b81f0000af8ff0f317e00025282b06300000020b8001769130000000000000600000ce8000ac0000000000000000001328001a626e0bc1b307c96c1f52c710fa2780000007b1d68b28001a50000000000002002b11128a69a7a898000b1a190001a80000000bc8eb1e60000000a119280001e1d499b9b780000011a80015b1b801d07989e1b00e19852508120b12138868002402418000dc81e89a00000b90a9118000a580022500000000000023c9db17b9c88e1130221a1a0180848c28c58002362cd88f9ca29e00015617a2dd9a40fe8d380016d9b98002109e71498000002c60481a02d1221209830aa100e2ac8d58001f78dd00000a9ec8000862148b59cb0918002c905f9cd05725022582e000103aa71741c90ef06e9ee00d23fa1e0042c8a1c818ad
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa10d4520004ef7654520004ec7654520005cf7354520005cc73545200066f76545200056e76545200056c76545200066c76545200046c76545200072f64545200072c64545200074f73545200074c73545200756f715452000767715452006e6f605452006f4f305452006f4d305452006f67105452006f6a1054520005ae76d0520005ac76d05200072f65d05200072c65d052005dad71d052003f2f51d052003f2d51d0520066af60d05200678f30d05200678d30d0520067aa10d0520004ef7650520004ec7650520005cf7350520005cc7350520006af7650520005ae7650520005ac7650520006ac7650520004ac76505200072f65505200072c65505200078f73505200078c7350520065af7150520007a7715052003f2f515052003f2d515052005eaf605052005f8f305052005f8d305052005fa7105052005faa1050520004ef764c520004ec764c52000dea76d812000eea76d81200076b65d81200076865d8120007ab64d8120007a864d8120005e971d81200076b51d81200076951d8120007ab41d8120007a941d8120004bf745951002cbc7459510004df7359510024dc7359510004ef725951001cec72595100047f75591100347c7559110004df7359110024dc7359110004ef725911001cec72591100047f7558d100347c7558d10004bf7458d1002cbc7458d10004ef7258d1001cec7258d100047f75589100347c7558910004bf745891002cbc7458910004df7358910024dc735891000cf4765451003677765451006e74765451000757735451000754735451000767725451000764725451000773705451006f70705451001677605451001773605451006f57305451006f72305451006f55305451006f67205451006f72205451006f65205451000cf4765051002eb7765051005eb47650510007977350510007947350510007a77250510007a47250510007b3705051005fb07050510016b76050510017b3605051005f97305051005fb2305051005f95305051005fa7205051005fb2205051005fa52050510014f8764c11000771514c110007b1414c110026db764c11004ed8764c1100075b754c11000758754c1100079b744c11000798744c110007d3714c11004fd0714c11000edb614c11000fd3614c11004f5b514c11004fd2514c11004f59514c110007d1514c11000751514c11004f9b414c11004fd2414c11004f99414c110007d1414c11000791414c110014f87648110007715148110007b1414811001eeb764811003ee876481100076b7548110007687548110007ab7448110007a87448110007e3714811003fe0714811000eeb614811000fe3614811003f6b514811003fe2514811003f695148110007e1514811000761514811003fab414811003fe2414811003fa94148110007e14148110007a14148110
  | 1 => 0x91200063f65d91200063c65d91200069e73d91200069d73d91200a6ad72d9120004bd71d91200a69f30d91200a69d30d91200047f75591200347c75591200a4be76191200063f65191200063c651912002ead7219120004bd7119120006ae2119120006ac21191200969f30191200969d30191200047f7558d200347c7558d20004bf7458d2002cbc7458d20004f77158d20014f47158d2000cee76d49200066f65d4920005ae74d4920005ad74d49200366c6594920005ce7394920005cd739492000cec76549200066f651492000cee76d09200056e75d09200056d75d092002eac6490920005ce7390920005cd739092000cec7650920006af641092000cee76cc9200066c658c920006ac648c92000cec764c9200066c654c920006ac644c920026cc634c920006cd630c92000ced72d85200047e76d45200347c76d45200063f64d45200063c64d45200047e76545200047c76545200063f64545200063c6454520004be76d052002cbc76d05200063f65d05200063c65d0520004be7650520004bc76505200063f65505200063c655052000cec7648520005cf7348520005cc7348520005ce73d9520005cd73d95200074e73d95200074d73d95200056d71d95200c66f60d95200c74f30d95200c74d30d95200c76a10d95200b56e75995200066f6599520005ae7499520005ad7499520005e97099520005af7459520005ac7459520005eb70595200c56e76195200066e76195200056d71195200066e61195200066c61195200b66f60195200b74f30195200b74d30195200b76a1019520005ce73d9120005cd73d91200072f65d91200072c65d91200078e73d91200078d73d9120005ad71d91200a6af60d91200a78f30d91200a78d30d91200a7aa10d91200056e75991200056d7599120095ae7499120005e970991200056f75591200056c7559120005eb70591200a5ae7619120006ae76191200072f65191200072c6519120005ad7119120006ae6119120006ac6119120096af60191200978f30191200978d3019120097aa10191200072f5495120005eb705512000de870551200072d54151200066c65d8d20006ac64d8d200056e7598d200056d7598d20005ae7498d20005ad7498d20005e97098d200056f7558d200056c7558d200066c6558d20005af7458d20005ac7458d20006ac6458d20005e77158d2003de47158d20005eb7058d20006cd6318d20005ae74d4d20005ad74d4d20004ee7694d20004ed7694d200074f5394d200056e75d0d200056d75d0d20004ee7690d20004ed7690d200056f75585200056c7558520005af7458520005ac7458520005cf7358520005cc7358520005eb70585200056e76d45200056c76d45200072f64d45200072c64d452006d6d71d45200766f60d45200774f30d45200774d30d45200776
  | 2 => 0x6cd62189300059e74d49300059d74d4930004de7694930004dd76949300055e75d09300055d75d0930004de7690930004dd76909300055f75585300055c75585300059f74585300059c7458530005cf7258530005cc7258530005db70585300055e76d45300055c76d45300071f64d45300071c64d453006d5d71d45300765f60d45300775a10d4530004df7654530004dc7654530005cf7254530005cc72545300065f76545300055e76545300055c76545300065c76545300045c76545300071f64545300071c64545300074f72545300074c72545300755f715453000757715453006e5f605453006f57105453006f5a10545300059e76d05300059c76d05300071f65d05300071c65d053005d9d71d053004f1f51d053004f1d51d05300669f60d05300679a10d0530004df7650530004dc7650530005cf7250530005cc72505300069f76505300059e76505300059c76505300069c76505300049c76505300071f65505300071c65505300078f72505300078c72505300659f715053000797715053004f1f515053004f1d515053005e9f605053005f97105053005f9a1050530004df7648530004dc764853000dda76d813000eda76d81300075b65d81300075865d81300079b64d81300079864d8130005d971d81300075b51d81300075951d81300079b41d81300079941d813000cec725972000cec725932000cec7258f2001ecc3258f20005ae74d4b20005ad74d4b200056e75d0b200056d75d0b2001ecc634cb20004df7358720024dc735872000cec7258720005cf7348720005cc734872001e6f6599720005ae7499720005ad74997200056e75993200056d75993200072f54953200072d541532001ecc6358f20005ae74d4f20005ad74d4f2001cee7694f20004ed7694f200074f5394f200056e75d0f200056d75d0f2001cee7690f20004ed7690f20005cf7358720005cc73587200774f30d47200774d30d4720004ef765472001cec7654720005cf7354720005cc73547200066f76547200066c76547200074f73547200074c735472000767715472006f4f305472006f4d305472006f6710547200472f51d07200472d51d07200678f30d07200678d30d0720004ef765072001cec7650720005cf7350720005cc7350720006af7650720006ac76507200078f73507200078c7350720007a771507200472f51507200472d515072005f8f305072005f8d305072005fa71050720004ef764c72001cec764c720024de73d9520004dd73d95200347e76d95200065e73d95200065d73d95200c66d72d95200047d71d95200c65f30d95200c65d30d9520004bf745952002cbc74595200c47e76195200366d72195200047d71195200066e21195200066c21195200b65f30195200b65d3019520024de73d9120004dd73d912002cbe76d
  | 3 => 0xf7250730005cc72507300069f76507300069c76507300078f72507300078c72507300079771507300571f51507300571d515073005f971050730004df7648730024dc764873001cee72d9530004ed72d95300347e76d95301065d73d95300066e72d95300066d72d95300047d71d95301066f20d95301066d20d9530004bf745953002cbc74595301047e76195300365d73195300047d71195300065e31195300065c31195300f66f20195300f66d201953001cee72d9130004ed72d913002cbe76d91300063f65d91300063c65d91300e69d73d9130006ae72d9130006ad72d9130004bd71d91300e6af20d91300e6ad20d91300047f75591300347c75591300e4be76191300063f65191300063c651913002e9d7319130004bd71191300069e31191300069c31191300d6af20191300d6ad201913000cde76d4d300065f65d4d300059e74d4d300059d74d4d300365c6594d30005ce7294d30005cd7294d3000cdc7654d300065f6514d3000cde76d0d300055e75d0d300055d75d0d3002e9c6490d30005ce7290d30005cd7290d3000cdc7650d300069f6410d300065c65cc9300069c64cc93000cde768c93000cdc764c9300065c654c9300069c644c93001ecc624c93000cdd73d85300047e76d45300347c76d45300063f64d45300063c64d45300047e76545300047c76545300063f64545300063c6454530004be76d053002cbc76d05300063f65d05300063c65d0530004be7650530004bc76505300063f65505300063c655053000cdc764c530005cf724c530005cc724c530005ce72d9530005cd72d95300074e72d95300074d72d95300055d71d95301065f60d95301074f20d95301074d20d95301075a10d95300f55e75995300065f65995300059e74995300059d7499530005d970995300059f74595300059c7459530005db70595301055e76195300065e76195300055d71195300065e61195300065c61195300f65f60195300f74f20195300f74d20195300f75a1019530005ce72d9130005cd72d91300071f65d91300071c65d91300078e72d91300078d72d91300059d71d91300e69f60d91300e78f20d91300e78d20d91300e79a10d91300055e75991300055d75991300d59e7499130005d970991300055f75591300055c7559130005db70591300e59e76191300069e76191300071f65191300071c65191300059d71191300069e61191300069c61191300d69f60191300d78f20191300d78d20191300d79a10191300071f5495130005db705513000dd870551300071d54151300065c65d89300069c64d89300055e75989300055d75989300059e74989300059d7498930005d970989300055f75589300055c75589300065c65589300059f74589300059c74589300069c6458930005d7715893004dd47158930005db7058930
  | 4 => 0x893108e6f51d893108e6d51d893108eaf41d893108ead41d8931004ed70d893101ecd731893107e6f511893107e6d511893107eaf411893107ead411893107ece311893107ecc3118931004ed701893107cde76cc93101ecc62cc931014dc764c93101ecc624c93108cef764cb2101ecc634cb210047f75583210347c7558321004bf745832102cbc745832101eeb2058321004df7359521024dc73595210ccef7259521004df7359121024dc73591210acef7259121024de76d8d210865f51d8d210865d51d8d210869f41d8d210869d41d8d21004dd70d8d2108cef7258d21084de7618d21026cd7218d2107e5f5118d2107e5d5118d2107e9f4118d2107e9d4118d2107ece2118d2107ecc2118d21004dd7018d2107cee768c921026cc638c921014ec764c921026cc634c92111c7f76553500147d7558750004df7358750024dc7358750004ef725875001cec725875003677515875002cbe76d9150004bd71d91501269f30d91501269d30d9150126af20d9150126ad20d915002e3d7519150004bd71191501163e50191501163c50191501169f30191501169d3019150116af2019150116ad20191501147e76d515002e3c64d515000c7c765515002e3c64551500147c75d85500063f64d45500063c64d455000c7c76545500063f64545500063c6454550006776154550004be76d055002cbc76d0550004be7650550004bc7650550124bf765534002e3c6555340014bd7458740004df7358740024dc7358740004ef725874001cec725874002eb741587400347e76d95400047d71d954011e5f30d954011e5d30d954011e6f20d954011e6d20d9540124bf745954011c7e76195400363d74195400047d71195401163e40195401163c40195401165f30195401165d30195401166f20195401166d2019540114be76951400363c659514000cbc76551400363c6555140014bc74d85400047e76d45400347c76d45400047e76545400047c76545400063f65d05400063c65d054000cbc76505400063f65505400063c6550540006b7615054000cdc735973000cdc73593300059e74d4f300059d74d4f300055e75d0f300055d75d0f3000cdc7358b30026cc3258b3000cdc7358730004ef725873001cec7258730005cf724c730005cc724c7300265f65997300059e74997300059d74997300055e75993300055d75993300071f54953300071d5415330026cc6258b300059e74d4b300059d74d4b30024de7694b30004dd7694b300055e75d0b300055d75d0b30024de7690b30004dd7690b30005cf7258730005cc7258730004df7654730024dc7654730005cf7254730005cc72547300065f76547300065c76547300074f72547300074c725473000757715473006f5710547300571f51d07300571d51d0730004df7650730024dc7650730005c
  | 5 => 0xcf87059541014be76d51410063f65d5141015b671d51410363e6595141014bc76551410363c65551410063d65151410347e75d8d410047d75d8d41024de76d8d410065e75d8d410065d75d8d410ee9d74d8d410ee5f51d8d410ee5d51d8d41004dd70d8d410269d7418d410069e5418d410069d5418d410de5f5118d410de5d5118d41004dd7018d410069e4018d410069c4018d410053e75d0d410053d75d0d410269c63d0d41014be7690d41005ae7290d41005ad7290d41014bc7650d410069f6310d410347e75d89410047d75d894101cee76d8941006cf63d8941006cc63d89410066e75d89410066d75d89410aead74d89410ae6f51d89410ae6d51d8941004ed70d8941006cf6318941006cc631894101ead7418941006ae5418941006ad541894109e6f511894109e6d5118941004ed7018941006ae4018941006ac40189410053e75d09410053d75d094101eac62d0941014be76909410059e73909410059d7390941014bc7650941006af6210941014bd74d81410063f65995410059e73995410059d7399541005ae7299541005ad7299541005b571995410059f73595410059c7359541005af7259541005ac7259541005b77159541005bb705954105db870595410063d65195410053e75d8d410053d75d8d410071e75d8d410071d75d8d410ee9f61d8d410ef1f51d8d410ef1d51d8d410059d70d8d410ef9710d8d410dd9e7398d41005ae7298d41005ad7298d41005b57198d41005af7258d41005ac7258d41005b77158d410ed9e7618d410069e7618d410069f6518d410069d6518d410de9f6118d410df1f5118d410df1d5118d410059d7018d410069e6018d410069c6018d410df971018d41004be76d4d41004bd76d4d410071f5394d41005ae7294d41005ad7294d410053e75d89410053d75d89410072e75d89410072d75d89410078f63d89410078c63d89410aeaf61d89410af2f51d89410af2d51d8941005ad70d89410afa710d89410059e73989410059d739894109dae7298941005b571989410059f73589410059c7358941005b771589410adae7618941006ae7618941006af6518941006ad65189410078f63189410078c631894109eaf611894109f2f511894109f2d5118941005ad7018941006ae6018941006ac601894109fa71018941004be76d4941004bd76d49410059e73949410059d7394941005b7714c941015b4714c9410078d320c9410079763d85410079463d8541007a762d8541007a462d8541005b570d85410053f75581410053c75581410059f73581410059c7358141005af7258141005ac7258141084df764cb310047f75583310347c7558331004bf745833102cbc7458331026db305833110cdf7359531004ef725953101cec72595310ecdf7359131004ef725913101cec725913101cee76d
  | 6 => 0xc5018d510053e74d4d510053d74d4d510265c63d4d510147e7694d510065f6394d510056e7294d510056d7294d510147c7654d510065f6314d5102cbe74d8951004bd74d895101cee76d8951006cf63d8951006cc63d89510ce6d75d8951006ae74d8951006ad74d89510ceaf41d89510cead41d8951004ed70d8951006cf6318951006cc631895101e6d75189510066f54189510066d54189510beaf41189510bead4118951004ed70189510066e50189510066c50189510053e74d49510053d74d495101e6c62d49510147e76949510055e73949510055d73949510147c76549510066f62149510147d75d81510063f64991510055e73991510055d73991510056e72991510056d72991510057571991510055f73591510055c73591510056f72591510056c72591510057771591510057b705915106d7870591510063d64191510053e74d8d510053d74d8d510071e74d8d510071d74d8d5110e5f61d8d5110f1f41d8d5110f1d41d8d510055d70d8d5110f5710d8d510fd5e7398d510065f6398d510056e7298d510056d7298d51005757198d510056f7258d510056c7258d51005777158d5110d5e7618d510065e7618d510065f6418d510065d6418d510fe5f6118d510ff1f4118d510ff1d4118d510055d7018d510065e6018d510065c6018d510ff571018d510047e76d0d510047d76d0d510056e7290d510056d7290d510053e74d89510053d74d89510072e74d89510072d74d89510074f63d89510074c63d89510ce6f61d89510cf2f41d89510cf2d41d89510056d70d89510cf6710d89510055e73989510055d73989510bd6e72989510057571989510055f73589510055c73589510057771589510cd6e76189510066e76189510066f64189510066d64189510074f63189510074c63189510be6f61189510bf2f41189510bf2d41189510056d70189510066e60189510066c60189510bf6710189510047e76d09510047d76d09510055e73909510055d739095100577714c95101574714c9510074d320c9510075763d85510075463d85510076762d85510076462d85510057570d85510053f74581510053c74581510055f73581510055c73581510056f72581510056c7258151014bc745974102e3c545974102e3f65d534102e3c6555341014bc7458f41005ae7290f41005ad7290f41014bc7458b410059e7390b410059d7390b410047f75583410347c7558341014bc745834102e3f659974102e3c6559741005ae7298f41005ad7298f4102cbe76d4f41004bd76d4f410071f5394f41005ae7294f41005ad7294f410059e7398b410059d7398b4102cbe76d4b41004bd76d4b410059e7394b410059d7394b410078d320cb410053f75583410053c7558341004df7359541024dc7359541004ef725954101cec7259541004fb7059541
  | 7 => 0x52430363e6555243006ae5498a43006ad5498a43004ed7098a43006ae4098a43006ac4098a43026cf3098a4312ecf4358a43026cc4358a43004ef7058a43026cf3058a43026db305824302e3c6555043004ef725844301cec725844302eb741584430047f75580430347c755804302eb84058043026db3058043004bd71993520363f5199352006ae2199352006ac219935213e3e52593520363c5259352004bf71593520363f51593520367751587520cee6215875202c7f765525202e3e64552520065f5498e520065d5498e52004dd7098e520065e5098e520065c5098e5201ecf2098e52136cf5258e5201ecc5258e52004df7058e5201ecf2058e5201eeb2058252004df7358452024dc735845203677515845201ee42158452004bf745805202cbc745805201eeb20580520047d719974202e3f41997420066e21997420066c219974213e3e425974202e3c42597420047f715974202e3f415974202eb74158742034bf76552420363e65552420069e5498e420069d5498e42004dd7098e420069e4098e420069c4098e4201ecf2098e4212ecf4258e4201ecc4258e42004df7058e4201ecf2058e4201eeb205824202e3c6555042004df7358442024dc735844202eb741584420047f75580420347c755804202eb8405804201eeb205804201cdc735973201cdc73593320059e74d4f320055e75d0f32026db305833201cec725963201cec725923201ecc3258e32005ae74d4a320056e75d0a3201eeb205823201cde76d4d320065f65d4d320059e74d4d3201dce72d4d3201cde76d0d320055e75d0d3201dce72d0d32024ee76d4932005ae74d4932025ce73d4932024ee76d09320056e75d0932025ce73d093201dcf764c832006cf764c832136ce654c83201ecc654c83212ece644c83201ecc644c83207dce714c83207dcc714c832005cf704c832006cd32584320047f75580320347c7558032004bf745803202cbc7458032006cd3258032026db305803201eeb20580320147c75593510363c54593510147c7558f510056e7294f510056d7294f510147c7558b510055e7394b510055d7394b510147c7558351004bf745835102cbc74583510363f64993510363c64593510365f6398f510056e7298f510056d7298f510347e76d0f510047d76d0f510056e7290f510056d7290f510055e7398b510055d7398b510347e76d0b510047d76d0b510055e7390b510055d7390b510074d320cb510053f74583510053c74583510147e76951510063f64951510147c765515102e3c645515102cbe74d8d51004bd74d8d51024de76d8d5110e5d75d8d510069e74d8d510069d74d8d5110e9f41d8d5110e9d41d8d51004dd70d8d510265d7518d510065f5418d510065d5418d510fe9f4118d510fe9d4118d51004dd7018d510065e5018d510065
  | 8 => 0x400600000000000000500300500100000000000000b00000400100400000000000000000000100000400000300000000000400600000100000100000000000000000000100000000000200200200000000100000300100000000100000300200000300700400700b00000200900000000000000300000100000000000000300a00a00000000200400100300200100000000000100200100000200000000000500000000200200500000000000100700100500000100000700200300000000200400000100000800000400000900100700200400300000800000500100100200100900000000000100100000000400300000700000300100000000400600100000000200000000000401600400500900100200100000000100000000200000500600000200100100100000000500000000000300100100400200000200500200000600000100200200000200000000100100000200000000100800000200200300600400000300000000300200b00400100000700000000100200000200000000800100000100900700200600000000100600200000c00100000200100900100000700000000000200000100500300100000200000200000000000000400000000200900500000200400100800300300a00100000300300100000600000100000100400000400100100f00100500000000100300000500200000100000100000000000300000000000000000500600000000100400400100200000200100800100100000100400000100000400100202c7c7558f5402c7c7558b54036775158754126ba405835402e3c545965402d3d76d52540363d76d52540053d71d525402cbc7458e5402cbc7458a540063f545865402eb7415865411e7a505825402d3f76550540063f76550540043f76550541463e635505413e3e62550540053f71550541153e70550541153c70550540063d5458454004df7358454024dc7358454004ef725845401cec725845403677515845402eb741584540063d5458054004bd71993530363f51993530069e31993530069c31993531463e53593530363c5359353004bf71593530363f515935303677515875310ed6315875302c7f765525302e3e64552530055f73552530255d76d4e530365d76d4e530371e74d4e530371d74d4e530274e62d4e530274d62d4e530066f5498a530066d5498a53004ed7098a530066e5098a530066c5098a53026cf3098a53136cf5358a53026cc5358a53004ef7058a53026cf3058a531067a5058253026db3058253004ef725845301cec7258453036775158453026d43158453004bf745805302cbc7458053026db30580530047d719974302e3f41997430065e31997430065c31997431463e435974302e3c43597430047f715974302e3f415974302eb74158743034bf765
  | 9 => 0x7180000000000000000004f07ee62200000000000000073654871e00000000098a0006d2134000a043720940000000000000001123aa91a00026c0002ec0000007a049844e00017625a00000092000000031c20679e6a231e0002b82841ac50000010c0006e6000270a0c1da32a1e698c80000478eafc0003dc000000000690000000000000000000200000000aec77620aa500000002f800000000076c0005fc14c74892400045822200054eb1c00024009a0000000000009ca000000a3828000000000000000086c00000003e00074a000156000000000a7c28c0000000000000000000000004840f69f60006a687c8d00000000de02c5de00000012458a45a0000002344e800000e4f481a8587f2af652c00092c00004e0000000000000000005940000000006100006380000008f00000000000000007e249a9e091c0000000000008c001e0000000004be1940000001e000000086e000000470174aa600000000096e000000000000aa493a9123f697400057c5ba4ca9260004a20000000000000008403740000000001660000000006d0000b0ea9800000043078a000034000060552000988406952574382ad61220006760000000003fc108000000000160b340000c8000a587080000006b25e400041c00084256e72e000b0aac80008e00000000000006da6dc52236ab005e00ae0000006c84600000000000006b08080000000004020004280006b800011869c0000000d00001fe0000000003ae0000000000000000000007982ca4ee0000000008660003e81be082000a80b2c00054400000015c0000004900000000006f000041400048291675473e00010e20c27c05a49c0006f68289e800000000000000075c530210000a00a283c085e8e454c00086035a732000182000b161c40000000000003f06ce3e0000000000000000a3e6920000005ec0000005ae0d411e0000000001dc6b64ba00062e38e1521c27baaca7dcb0c60e3a60002eea9c57e0000000006840000006aa0000000000000002380000000004fa000000000a6c0000000007120dc00047a0000002f00005c036438c0000000000000002bc000000000ace00000035e000ac65b8302a8e0004660000000002b696800000000000055000000000045c0000004e26340000001f60006981b20c62421a20508c200072800000000008e000000000a36aa200000000700300300800200300100000000200100900000400000900800100100001700000000700000500000400100000500000000100700300400100000200300000000000100000100300500300000100000000100100000000000400000700100500100600200100100000e00000100000000100000000200000300000100000000100100300400100100000700200100000100000700200300a
  | 10 => 0x7a400000020e0003e23840004102486c62dc0005540009b04541020d20002d404c5da5a829c15e3500c20a234400000000012e000000000b3c0007963ec5d6000000000000000000000000b285f000055a4423bca520008f613c23056a4d297c000ae885c4a090021c0000009b84a47c4494b040007f40000000009380009aa0000000000e80007a800073835c0000a810a6883da3986280009840000000000000000000000000000003009cc0000000000408fe01a714ab4000a480000004125585f6000a7251c00000000042271ab146e4512000b240000000000000009fe0000000000009768388be64e1ce4446d83b865c5be1e43180000000000001ea0000000008748ac000000a5a5b0000000000000af41ee000a4a00000000000000000000000000000000000068667e000000000000042648000000420adc0000000000000000ce00000000000000000081e756a080da4e0aa00003c677a0100669ea43c0000007269320700000000000000000000003cc000000000000000000000a32000aae00092e2ac5e89c4652a6e0000007bc6c00005a018498e9b42c00000000004f8000000a62ae22ce18ead400000000000000000000000058667a5ca9700000000008120005200000008825c64e4000a4c8340009900007063200000000002643b61d0a020360883120000000000002080000000000006249466649c8000ac00000000001684ae25c5dcac20009348308849569eca5ea6835422c0ea00043a9be0000000000ca450526a1c95c0060000f0000b2e00000000000000000000000000000000000046a27200000000000000000050a00034e000abe0000003a240c0002a400020400006400000000019e6320001f00000004b400082e0000007687e641eaf896030c0007a618a89a65466880a3ce342000b120004a6a180007f09de0000008b20000007d660c93e4d800012c56000031436e7940000000002e09724627ac8da0001325f80000000000000002287cc0000007ae00023e51aafa5685368480000008020002c80000000000000b49a000052e1d4000000000000086000b200000000000007f80003764f28ec1d883a16a4b08780000004d46580000007580005ea9c63802be0005d40000000000000000008b4acc90807c00000000051400012857600000000039a000000940020290000614596a4e00071c6420000006c40000005ac7400000000000007ea57a0000001700000008b800000000000028a0000000000000000000000002c43ee66e0f20006780003d08cc8c80000003b0000aaa2940009ce00000000000000070c0000000005160003680000000000000000003e600000000000000073029e8dc8e200038a9c2000760a9ea90ab293c00000043473c7106820009dc58e2f453a4aa0000000000008241780
  | 11 => 0x186303e4774894000a1268c08a46e0000007fe0000000000000009ba6c298011674466c9540008688e8ab68a077c00000000033600000011a0006400000007fc42a7828c44de000000a540000000006ee00034000000013000015a1883b45a200ab08058000784b420f400000088840899405246838695876600000084c0fc0e60009b28fa00048c82600000000019a8ca0006560001986b431a3585664ea1d674294eae024c25409260a5d20003564324da1f206a2c67e00000008f80000000000000000000005b2b1a2fa6625c496a2320a43deaba00000096699c1f80004740007222e6a8a9a490649633e1a67b60b800000000000069643697aa746004c03f20000000000007ce0001c84ec000a7a0000007907fa16e86aa665402c20002e80000006a80e2000000000000000226b1e3220000000000009f074e23c0000000120009d214008ca440000005fe000000000abc47e1b0b22000000b3e0001aa592000ad80000000b08860007e81b48c614a0002d200000000000059a0002d80000003620000d895e4f68565c217200069a11c9425a4000702000000000ae662000025200022a00037e0003fe7b0b3600009e5d80000000007d20000000000000000140000000001a8b1844c000000aa80000004a82d60000000000007040008deaf2000000b0600092a6605042565802ea07a114a7800000000090a0004cc2aa84a0001e8000000000ab02a84045820008222fc0004180000000004b8a220008440001cc6ca2b2000a40000000000000000000ab80000766ac30600000000000055600000091800000060850c00000000000006e0000003d20000000006a40000006ae21a6d6000000144986000000000220138a9a000b020080005460900000000006d40007da6ec0000006e06f264c426a7e0000005640000007d8ad20000000009acb325100001fc0006fe00048a388000850982000814a3c00078000000068a36600000000000005e0001b61ca00000000000000000000000000047800000026e8ba0d60000007860000001207207c63f40000005fa83e750602000000a4600000063e63a0000008fc21e0002ba0fe0000000a0a147927c8000000000000a9404490c000000000000438000000000a0600000000000000000000000000002e0003943780e417a00047c77040a00036000000070a7620002b4000000000080b3000000000000057800000000000030800000032c99a9620009fa00000000009800072a96c00000000000039c0000000bc0000000000000ec61644a5cc21400000000083651826692234801c2780000000004760fa7c012a16c000000000000a3a00051e05400077242e0009da0008540004006cc0388f448e00037a0000b23b200000000052400000079a80e000000000534000000000a2487a00053800
  | 12 => 0x7ea8837c00090e4c461800061e3be2e23d400064a86404a9f279c0000000000000000000003ba000000a6a00003c27635200000000000089833c00000047263c9147e400018019c00000000032600049e0006940000008ea00000000000032e6449ee0220002923101864560000009100008d600000c4c80007be55c7b252a0000002a200000282a62c8103d8a2a0000000000004dc000110000000000000b3830a2a6000000b404d00006f875e3a894a06cb2600000044831600073470e7c2a261a04fc2588a42163a473a6bc36c00077e4c60008bc23a6fc8047ec84e59c2a0a567b85a600071660627e92813669e9d04640000000003320003ea24a19000000048800076e0001b8000000000000000000000a4200000000090288082c3c40000000000000002740008180000000005429923046e80000000007780000000000005ce1a400039e0000003c24465286f414e8068aa026000000000000a760788a646c4bc0000003920c03d65320008d234c0008e68200000000000000000008b6000000000146000000260000a340008f20007520ba0000000000000003962da4160000ac0001fa29a2820004e6a1e4c27001c60000009bc74600000055e50800026845e0002027f665000000000041a43e8ae0008163a0000a860b6324164000604000000890000a103ca3ac0005724acb103f85f468e91eaac2509fc49250200000000000000053c9d81268920e08a89440002f6000a8200042c5902967d453e61c24400000017e0000000f87649ae0000a62fe0000000004b60000007aa000a2e88a6de9d42de000a2c89c3c8ade0000000009049509e20002367b42e400000000000010600059800028e00083c0000007d0440000000000000000000afe28609662aa5c00000000000000076a33a00088e6ba00018c00000061a0000001ec0aa0000000000000000000000000000001000000004ce00000000000066a00000000088c00000000021800000000040e0007de00000000058c154b3a000a648620000000623701d299800000000097e1f40009e40000004b20001580000000004fe00087626a00094c0000000000000006740005ee5e61ae2ae0000000000000000000004865b48ee5aa8460000009780000009f4000000832000000ada000000000a700000000000001c09f804800065a14200013a50ea0a75a0008cea9267200048085aaea1de81ca1600059e0000007a20680000002d061200000008400000000065e9302623380003900000001e200000000067c00078c000000870a20074288a8c80c33072c24eaee016000000000000000000a600009a29966a09640ee1485060720005840566fa89634600000000054a0000001920000c4000570000000298b2a0009a603a00099e0000009d68720306668b00009e66ea17c
  | 13 => 0x5bc00002856287e0006460000000004d60000000005d0000000a8400093689e22e30e7ca0000000009c000010425e0000000006360009b60000000009a81621ba000000a0e8d8a30000ac468058819600009c0000000001505f267034a0000000006e21bc5b605c328ad00002f200000078842445200000021200000062600000033494802456c3fa032a1a6be00000013e27a0005e200074c02a0000cc8d40462b0ae47240000000be0000000000000000000000005c80002240000000000000000000000000000002462cc00095a000000000000000000000000000000000a96000af00000008520000000008a20
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa8d820c4644c04d898cab94a698097231917290d3000526c14ec32a6000a4d82184654c0018aae2308ca98002a360a761913000546c10c2322600091f87550544c04563100aa0a898003151c465589300064a388c8b126000ac481588624c00183cec326a29800217a1a76545300060fa08eca8a6000c1d411d9514c00189e403b2a2980031348076545300062b880eca8a6000c5a101d9514c0018aa203b2a2980031644076545300060e3b6c8a8a6000c1c76191514c001898edb92a298003131d872545300060f3b0cba0a600089e869d9414c00183ea23b2829800307544765053000647900eca0a6000c8d201d9414c00192e203b282980032684076505300064a880eca0a6000c99101d9414c001838edb2a8298003071d86550530006463b6e4a0a6000c8c761c9414c00125f0eaa0a99000272600735872000627bb0e6a8e4000c8f761cd41c80010db0e108ca900029360c211952000632b884232a40008ad87084644800151b06108c89009b13195739492012e46322e7212400fac48158c324800149b073b0ca900029360c611952000632b88c232a4000a8d839d8644800151b06308c8900024be1d541512011594402a82a24000c64711956348001948e2322c690002b12056318d20006173b0c9a8a400086e869d9514800185e823b2a2900030b504765452000627980eca8a4000c4d301d951480018ce203b2a2900031a840765452000632880eca8a4000c69101d95148001858edb22a2900030b1d86454520006263b6e6a8a4000c4c761cd514800185cec32e82900022ba1a765052000617a88eca0a4000c2d511d9414800191e603b28290003234c0765052000653880eca0a4000caa101d9414800194a203b282900032a4407650520006163b6caa0a4000c2c761954148001918edb9a8290003231d873505200062a3b0e6a8a2000b51801cd51440018c8ec392a288002d860072545100064a3b0e6a0a2000b91801cd4144001948ec3928288002e860072505100062c3b0ea9822000b51811d53044001930ec3a26088002e4604744c110006a9c3aa29822000b528754530440016a10ea8a60880035421d514c11000789ba2a29822000f10745453044001e8704a8a6088003d0209514c110006c9c3a829822000b928750530440017210ea0a60880036421d414c11000789baa829822000f10755053044001f0704a0a6088003e0209414c110006343b0ea9022000b61811d52044001950ec3a24088002e86047448110006b1c3aa29022000b628754520440016c10ea8a40880035821d514811000791ba2a29022000f20745452044001e8706a8a4088003d020d5148110006d1c3a829022000ba28750520440017410ea0a40880036821d414811000791baa829022000f20755052044001f0706a0a4088003e020d4148110
  | 1 => 0x8878766e2321000260000000003a1244e241fa8c628709000303e05ad800c41e83c00230008406894e02804ab2b91436a852b40d2a200089988120871306c3c1e468065d30178b015200eacf2030cb4ce4d158be305098cba9563a14b87364110e4483296c7200271a0402f0001c5a002c8015c90001b4f8af3f8010c3547314fa054880000be269ec00250005400014f0009800001c01c920ba3c3ab8379f80077162cd52c128328c22e569ad28831c10954bd1e199404b4ea3400000000148995da6d9a004b840c4040ca2184b700324a6471599052b265800a87a3b2d066581bb44d46758a093eac000c8000006a2886001d0017e0029000c0000022c28a7289c4bc960d000aa8c000594cc609ae4180004ad45093250206c1f2780010001838041c00382000f41800280c441c1038080800101cd01c0004080c040410280010041c001c0c240010087c340c1010381804380c040430084404081800284c1000000146b03aa2c32a0020f60776550540041fc3aa8b08a828c1c73551611504f858e4aa2c22a0028de0554584541141e43aa8b00a822a3880551601500151b0418cc9a9802a6600319935300516c20a1314a600a65811426294c0149b0418ccba180296600319974300516c28813148600aa5811026290c0151b0610cc9a9002aa60021993520050ec20a131ca400a5581142639480149b0610ccba10029a60021997420050ec288131c8400a9581102639081f1990e992c21903eb12053258432136263aa64b006425c8c744c9600c80159700992c019002876105018d511460e31ae9a9aa200a2d84140625444f858c4ba6a4a88020fe1d64191510051c402c8322a200a1d849d863544014b100b20c6a8802876106018d5100516c24ec312a200a6880590625440145b08300c4a883ed1205320c9510041fc3aca2a28222a3880594545040143b0a200c6a0803265c04018d411460e31aeba1a8200a2d851006250401952e0200c4a089f0b18975d09410041fc3aca32a8200a3880594655040143b0b3b0c6a0802a62016518d410050ec28c031a8200c9970180635040145b0b3b0c4a0802aa201651894100516c28c03128200ca970180625041f7090299064a08028d60464d45500051ac08cba0a800091f8755054cc00139300392c39800313dd8725473000647bb0e4a0e600085d870c4654c00149b04188ca98003155c431195300044ec38623226000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x6404000006241d9801cd41440018a0766007250510006141d9811d53044001860766047548110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x98a
  | 8 => 0x150a
  | 9 => 0x9ca
  | 10 => 0x168a
  | 11 => 0xb89
  | 12 => 0x1849
  | 13 => 0xbc9
  | 14 => 0x19c9
  | 15 => 0x3ca
  | 16 => 0x15ca
  | 17 => 0x170a
  | 18 => 0x409
  | 19 => 0x40a
  | 20 => 0x1609
  | 21 => 0x188a
  | 22 => 0x449
  | 23 => 0x44a
  | 24 => 0x1649
  | 25 => 0x1a0a
  | 26 => 0x589
  | 27 => 0x58a
  | 28 => 0x1789
  | 29 => 0x18ca
  | 30 => 0x5c9
  | 31 => 0x5ca
  | 32 => 0x17c9
  | 33 => 0x1a4a
  | 34 => 0x749
  | 35 => 0x1949
  | 36 => 0x1a89
  | 37 => 0xccd
  | 38 => 0xcce
  | 39 => 0x104b
  | 40 => 0x104c
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 68
  | 6 => 1478
  | 5 => 1442
  | 4 => 210
  | 3 => 4
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*15) 6
  | 7 => packedAt gbK7 (i*26) 17
  | 6 => packedAt gbK6 (i*37) 28
  | 5 => packedAt gbK5 (i*48) 39
  | 4 => packedAt gbK4 (i*59) 50
  | 3 => packedAt gbK3 (i*70) 61
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 8 => gbHint (packedAt gbK8 (i*15+6) 9)
  | 7 => gbHint (packedAt gbK7 (i*26+17) 9)
  | 6 => gbHint (packedAt gbK6 (i*37+28) 9)
  | 5 => gbHint (packedAt gbK5 (i*48+39) 9)
  | 4 => gbHint (packedAt gbK4 (i*59+50) 9)
  | 3 => gbHint (packedAt gbK3 (i*70+61) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (16+((h/1+packedAt gbK8 (15+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (1922+((h/22+packedAt gbK7 (1768+(h % 22)*7) 7) % 82)*8) 8
  | 6 => packedAt gbK6 (60590+((h/492+packedAt gbK6 (54686+(h % 492)*12) 12) % 2146)*12) 12
  | 5 => packedAt gbK5 (74976+((h/480+packedAt gbK5 (69216+(h % 480)*12) 12) % 2786)*12) 12
  | 4 => packedAt gbK4 (12950+((h/70+packedAt gbK4 (12390+(h % 70)*8) 8) % 253)*9) 9
  | 3 => packedAt gbK3 (283+((h/1+packedAt gbK3 (280+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff0ff03fe07ffff81e03c07c09d99f667e93
  | 1 => 0x1e03f07fc0ff81e03ffffffffc36a6649993ff
  | 2 => 0xe003ff8000fffe003fe003ff83c73878e1e31c
  | 3 => 0x3ffffff0000003ffffc0003f83f80fe03e0
  | 4 => 0x3ffffffffffffc000000003ffc000fffc00
  | 5 => 0xfffc0000000000000000000003ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa219019005200a2199120a4118000889222691
  | 1 => 0x14202024404881420024a09460128224089026
  | 2 => 0xc04b568214b56c04af50132b09c53858e16318
  | 3 => 0x80939b5ab604280937995a0212e83d80f603c0
  | 4 => 0x1102ec6f38de719e0200600c237fc000ddd800
  | 5 => 0x19e0000c201841100401803043bff776000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfeeaeeeaeeeaccc8feeaeeeaeeeaccc8feeaeeeaeeeaccc8feeaeeeaeeeaccc8feeaeeeaeeeaccc8feeaeeeaeeeaccc8feeaeeeaeeeaccc8feeaeeeaeeeaccc8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15995
namespace PEqualNP.Outside.L_meta_15995
open PEqualNP.Outside.L_meta_15995.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 21 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 17 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 21 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 17 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bs4_3_0 : Interval s4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1 := bs4_3_0
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
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 1 := bs5_3_0
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
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 4 := bgb_3_0
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
theorem bgb_4_192 : Interval gbAtlas 4 192 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 210 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192)))
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
theorem bgb_5_1440 : Interval gbAtlas 5 1440 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1442 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864))) (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))) (concat (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))) (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440))))))
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
theorem bgb_6_1472 : Interval gbAtlas 6 1472 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1478 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 (concat bgb_6_384 bgb_6_416)) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))) (concat (concat bgb_6_544 (concat bgb_6_576 bgb_6_608)) (concat bgb_6_640 (concat bgb_6_672 bgb_6_704))))) (concat (concat (concat (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)) (concat bgb_6_832 (concat bgb_6_864 bgb_6_896))) (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)))) (concat (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280))) (concat (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 68 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 44, 60),(inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 56, 60),(inputs.getD 3 zero, 52, 60),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 5 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeaeeeaccc8feeaeeeaeeeaccc8feeaeeeaeeeaccc8feeaeeeaeeeaccc8feeaeeeaeeeaccc8feeaeeeaeeeaccc8feeaeeeaeeeaccc8feeaeeeaeeeaccc8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4008365256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
theorem binaryLower (low : Lower true fullRoots fullWord 9)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 9 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_15995.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[2,3]⟩,⟨.and,[2,5]⟩,⟨.and,[0,6]⟩,⟨.or,[0,7]⟩,⟨.and,[3,4]⟩,⟨.and,[8,11]⟩,⟨.or,[1,12]⟩,⟨.or,[9,13]⟩,⟨.and,[10,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008365256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008365256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
    refine ⟨⟨mono, 15⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 10 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_15995

open PEqualNP.Outside.L_meta_15995 in
theorem PEqualNP.Outside.L_meta_15995 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008365256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008365256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
