import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15727.Model
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


end PEqualNP.Outside.L_meta_15727.Model

namespace PEqualNP.Outside.L_meta_15727
open PEqualNP.Outside.L_meta_15727.Model
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

def SBf (j : Nat) : Nat := [5, 2, 5, 6, 6, 7].getD j 0

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

end PEqualNP.Outside.L_meta_15727

namespace PEqualNP.Outside.L_meta_15727
open PEqualNP.Outside.L_meta_15727.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x7fff00ffffffffc03fff80fffffff807f8ffc7
  | 3 => 0xffffff00ff807fffffffff01fc03ffffff18ff
  | 4 => 0x83ffffff00007fffc03ffffe0003fff80fe0f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x104b092124851444848a8b162d545b4a936b5b
  | 2 => 0xa095d84a4d4a28a3a915c0ab569aa8c5a8b5c5
  | 3 => 0x412652e88a534d293227558198c335974d18ae
  | 4 => 0x76389c8cec6c723223b9e6cd0313c6e18ee0f0
  | 5 => 0x7bc0e0f0f0707c3c3c3e78f1e3e207060fde00
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15727
namespace PEqualNP.Outside.L_meta_15727
open PEqualNP.Outside.L_meta_15727.Model
def s1K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s1K1 (i*3) 3
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt s1K1 (4+((h/1+packedAt s1K1 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffde73
  | 3 => 0x6f9c
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff8205
  | 2 => 0x2552
  | 3 => 0x1958
  | _ => 0
def s1Atlas : Atlas := ⟨1,rawDecor 13 s1Pos s1Neg, 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15727
namespace PEqualNP.Outside.L_meta_15727
open PEqualNP.Outside.L_meta_15727.Model
def s2K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x180a107731bc6370c7a18d431
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x2590631
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => packedAt s2K3 (78+((h/1+packedAt s2K3 (75+(h % 1)*3) 3) % 7)*4) 4
  | 2 => packedAt s2K2 (27+((h/1+packedAt s2K2 (26+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfc7fffe3fff1ff
  | 1 => 0xdbf87f3fc7e0e7c
  | 3 => 0xfffffffffffffffffffffffefff8ffff8fff8f
  | 4 => 0xf3fff03fff00ff0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff4071020a092a0b5
  | 1 => 0x24972456424665c
  | 3 => 0x110268249094b0a
  | 4 => 0xe244eb92418de0
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 27 s2Pos s2Neg, 0xee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15727
namespace PEqualNP.Outside.L_meta_15727
open PEqualNP.Outside.L_meta_15727.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x800409394602014602c40213be42bc42df32dd32be41bc41de31dc31bf40bd40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xc00815180401365190aa8a2995614132ca208632c5250268a2a05594630
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s3K3 (197+((h/2+packedAt s3K3 (189+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffc0fffffffffffe07fff80fffffffff1f8fff
  | 1 => 0xffff01fe03ffe03ff83ffff03e07ff80e7f27c
  | 2 => 0x3ffffffffc0fffffffc0fffffff80ffff8ff8f
  | 4 => 0xc00001fffff0003fffff00003ffff000ff03f0
  | 5 => 0xfffffe000000003fffffffffc0000000fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4852146248824c0c014b29064a8b18aa0b84b5
  | 1 => 0x92864ca43924855658155b521645ad0665b25c
  | 2 => 0x2308290890691122aa809468a5508654b05b0a
  | 4 => 0x3a2cb1d12241d9bb34e6064c39e6c418fe03e0
  | 5 => 0x3c30c1e1c38e1e3dc738e78f01870860dfec00
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xe8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0e8e8e0e0a8a8a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15727
namespace PEqualNP.Outside.L_meta_15727
open PEqualNP.Outside.L_meta_15727.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xb304024a144000a700c02004bf43bd43be42bc42be41bc41f721f421bf40bd40f710f510
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x60040109a28a871d5310a3aa7a05914910
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (208+((h/4+packedAt s4K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s4K3 (111+((h/1+packedAt s4K3 (108+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ffc1ffffffff03ffffc0ff83fffffe7e31ff
  | 1 => 0xf81ffe03f03f07fc3e07ff07fc3e0781b3cecc
  | 2 => 0xfffffffc003fffffc007ffffffc007ffc3ff0f
  | 3 => 0x1fffffffc007fffff80007fffff801fc0ff0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x90444448820841008a494848805294a4161055
  | 1 => 0x32cc8c3926524b2c16c2d943a434350cb2c6cc
  | 2 => 0x4191109068a484554104a2954a804259416b0a
  | 3 => 0x651a21224c06969a6590308673296011e80da0
  | 5 => 0x861c39c38f38e7e3b9e73ce062318461ffb000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeae0eae0eaa0eaa0eae0eae0eaa0eaa0eae0eae0eaa0eaa0eae0eae0eaa0eaa0eae0eae0eaa0eaa0eae0eae0eaa0eaa0eae0eae0eaa0eaa0eae0eae0eaa0eaa0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15727
namespace PEqualNP.Outside.L_meta_15727
open PEqualNP.Outside.L_meta_15727.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x410980063000289540d18026008191434da14e9521e007078022800142e1c9011c88d1f18000021600a8000a15800058e80520800c5280006002243001ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x58424aaeaa188e6c80b036924e001608a206a61e04002a3c56007884ac960000000000a0760014001c52b2005086005c006e94908c305e00224440002624a87200547e4638007c28989c20a4129a0c0074007000647a6a88662e681a0e3e6232829e2c104c8a5a02480a3a34600e0000144101800030208001c4010640c00001c101005c9800216eea2a1dd14543b7290876d5210e7ca3a14f55242bba8a85745150b5ea4a16dd45429e28a85b45150a68a2a14f950429f2a4653d548cb5a85195d94632baa8c65ad424ca7ca8194f550329ea94833e51906dca420db54841d7290833d521075aa420cb548419f28883b6511067ca998cf55331b7296636d52cc7688398cfd51319e2a263b4410c67ca990cf55321af29e435d53c875a8590ed107219faa4433c548867ea890cf15121d6a12433e540867aa810ed10421b7296816d52d02eca3205d546409faa2613c544c2dea4985b14930bba8a6174514c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c835a85104f950209eaa0415e53082baa6106b50820bb2884175510836883884f952109eaa4213f5444278a88857d4d10ae29a216f52442d8a4886d10510
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x3a60040008a862093078a01620c0101aca9409201a700ba0258000082a46150a32c9509518caa461509328d185540cb246154841a958841cc72652107318b588544c6a56210431c354d42c86a46150b21c594c41c86a562107218b195424863565104218d18554c82a46150a20c354d42082a46150820c950951082a562107108b58a54843145310510a958841443245210510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x460a80200a12bb4a420e638154c6150b21c0ca6b108390e0553185420830229ac420a21095d85210510
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 58)*7) 7
  | 4 => packedAt s5K4 (2640+((h/30+packedAt s5K4 (2430+(h % 30)*7) 7) % 109)*8) 8
  | 3 => packedAt s5K3 (990+((h/8+packedAt s5K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (300+((h/2+packedAt s5K2 (294+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffff83fffffff03fe0fffffc1fffffc8ff1ff
  | 1 => 0xf03fffc07e1f83fc3ff0f83ffe1c0f03727ecc
  | 2 => 0xffc1ffff801fffffc000ffc3ffe00fff838f0f
  | 3 => 0x1ffffffe003ffffff0003fffff003fc0ff0
  | 4 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x10800889100400008a0128444025214804b055
  | 1 => 0x258c91872429252c16905a29d2086a193256cc
  | 2 => 0x4315a2120d526355418896a2b5408cb3830b0a
  | 3 => 0xa29442449034a9a652a04032992c022d80da0
  | 4 => 0x8c318738719c73e3b9cce730310308c3efe000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15727
namespace PEqualNP.Outside.L_meta_15727
open PEqualNP.Outside.L_meta_15727.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x3a80006800224e14007c0018005600823078483c463428423e6674648c2e00445a0000002a70000050168e527e1058865c8440042632001a6e7a4a1c4c360888240c00768a0062120e546c72605e00061e0a2c3820026a6218204300040000e44070a10190020c000245000001ffd5005fe5401ff55005fc5401ffd4c077f5300ff94c07fd53005f54c03fc53017fd0c03fe43007f50c03fc4301ffd4807fe52005f94807fd5201ff148077c52017fd0801bf42007f90801fd42006f50805fc4200ffcc801fe32007f4c803fc3201ffd4407fe51005f94407fd5101ff144077c51017fd0401fe41006f90401fd41017f10401bc4100ffcc401fe31007f4c403fc31007fc8401fe21007f48401fc2101ffd40077f5001ff94007fd50005f54007fc50017fd0001fe40007f50005fc4000ffcc001fe30007f4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x24004fb88120025feca1000efe6508009bf32840039f99420065faca100137d65080013eb284004bf19420025fec81000afe6408009df3204002af99020005fac810013bd64080015eb204004bf19020025fec610006fe6308009ef3184001b798c20005fac610013dd63080016eb184004bf18c20066fea6100037d530800f7f3104007df9482003ef8a41001fbf420800fdea104000bf98420027ecc210002f661080017eb084004fd58420005eac2100037e5108019be2884000ef90420007788210003ee210800ff61084004bf98020026fea0100137d5008009f79004004fe88020027da401001ff9200800d7fb2e2000dfd9710004fecb8800efe65c400d7eb2e2003bf19710036f8cb8800e7c65c40017fb262002bf99310005fac98800afc64c40017fb1e2001bf98f10005fac788006fc63c400dbfa9e2000df54f10005fec58801efe62c40017eb162007bf18b10006fca58801b7c52c4001dfa162000ef50b10006fca38801b7c51c4017fba0e2000ef9071000778838802ff441c4001da20e2000fd8c710007ea6388003f621c4001fa90e2006dfd4310006faa188012ff65840077f32c2004df9961001cfccb0802afd6584009beb2c20009f59610025f8cb08012ff64840057f3242004ef992100157cc908002fd6484009deb242000af59210025f8c908012ff63840037f31c2000bf58e10025f8c70802b7f5384001bea9c2004bfd8a1003dfcc508002fd62840097e3142000df94a10056f8a508003bf4284001dea142008bf58610006fca30802b7c5184001df20c2000ef10610025fcc1080137f5084009bea842004fdc4210007f62108022ff6544001bfb2a20009fd951001dfcca88022fd65440077e32a2008df1951001cf8ca88002ff6444001dfb222000afd9110015fcc888002fd64440057e3222000ef1911001578c888002ff6344001efb1a2000b7d8d1000dfcc688002fd63440037e31a2000f718d1000db8c6880237f5344001bea9a2000bfd8910007dec488002ef624400f7f3122000bf5891003df8c488003ec6244001763122000df94910046f8a488003bf4244001dea122000df94510046f8a288027f74144001df20a2000ef1051004fe88288003b44144001fb18a2000fd4c510007ec4288003f52144011bfa822000df54110007f62088013f610440097fb282003bf99410026fcca0800e7e650400b7eb282004df59410004faca08012fc65040097fb202002bf99010005fac808012fc64040097fb182001bf98c10005fac608012fc630400bbfa982000df54c10025fec40801efe62040017eb102004bf18810006fca4080177c5204001dfa102000ef50810035fcc2080037e510400bbe2882000ef90410007788208012fe6004009bfa802004df54010027ee2008013fa1004009fa8802000fe44010
  | 1 => 0x2f56190001bf28c8013df146400077c832000bbc41900097f3048004dfd4240026faa120013bf4090005fda048004fe10240095fecaa000efe65500257eb2a8003bf19540025fec8a0002ff63500037f31a8001bf18d40096fea6a00037d5350005dfa1a8000ef50d40005fec4a001efc6250001bf2928012df149400177e84a0003bd42500017fb0a8000bf18540006fca2a004b7c5150001df20a8002ef10540015fec0a004b7f5050001bea828002fed01400277c80a0013bc4050005fc2028004bfd963001dfccb180137e658c0073f32c6011bf59630026facb180027d658c0097e32c6004bfd9230015fcc918002fd648c0097e3246001bf58e3000efea7180077d538c00f7f3146000bf58a30006fca5180477c528c001dfa146000ef50a30005fcc318002fd618c001bf28c6011df146300077c8318003bc418c001ef18c6001f70c630025fcc1180137f508c009bea846004f7cc23000ff66118013f8308c0217fb2a6003bf99530086fcca9800e7e654c0217eb2a6000df59530004faca9800efc654c0017fb226000efd91300057ec89800afe644c0017eb226002bf1913000778c89800abc644c0097fb1a6001dfd4d3000efaa698002ff624c00f7e3126000df94930086f8a498003bf424c001dea126001f7cc930007ba6498002ff614c0017e30a6000df94530086f8a298003be414c001de20a6001bfd8130086fea0980037d504c003fd9826004f78c130027b86098007f8304c00f7fb2e4007dfd972003cfecb9000efe65c801f7eb2e4007bf1972003ef8cb9001e7c65c800f7fb264002bf9932003f7cc99000abe64c80017eb264007ef593200057ac99001efc64c800f7fb1e4001bf98f20005fac79001efc63c801fbfa9e4000df54f2003efca59001f7c52c800fdfa164007ef50b2003fdc6590003ed32c80017f30e4000bf58720006fca39003f7c51c8001df20e4000ef1072007efea1900037d50c80097fb2c4003bf99620026fccb1000e7e658801d7eb2c4004df59620004facb10012fc65880097fb244002bf99220005fac910012fc64880097fb1c4001bf98e20005fac710012fc638801dbfa9c4000df54e2006dfac51001f7e528800fbe2944000efd0a200077a8510002fe61880017eb0c4000df94620076f8a310003be4188001de20c4000fb88620007d84310012fe6088009bfa844004df54220027de411001ffb208801b7fb2a4000dfd9520004feca9000efe654801b7eb2a4003bf1952006ef8ca9000e7c65480017fb224002bf99120005fac89000afc64480017fb1a4001bf98d20005fac690006fc634801bbfa9a4000df54d2003efca49001f7c5248001dfa124000ef50920007dc6490003ed32480017fb0a4000bf18520006fca2900377c5148001df20a4000ef1052006efea0900037d504800ffd9
  | 2 => 0x2103fbcc790806de63c84017eb1e4207f758f21005bac79081efc63c8437bfa9e4200df54f2103efca59081f7c52c840fdfa164207ef50b21006fca39086f7c51c8439fba0e4200ef90721007788390873f441c8401da20e4204bf98321005fac19086f7f50c84337fb2c4203bf996210cefccb1080e7e65884337eb2c4200df59621004facb1080efc65884017fb244200efd92210057ec91080afe64884017eb244202bf1922100778c91080abc64884017fb1c4201bf98e21005fac710806fc6388433bfa9c4200df54e210d5fac51081f7e528840fbe2944200efd0a210077a8510803ee3288401f69944207bf98621006fca3108677c5188401df20c4200ef10621007de431081ff721884097f3044200bf582210cefea11086aff6548401bfb2a42009fd952101dfcca9086afd65484077e32a421adf1952101cf8ca90802ff6448401dfb224200afd9121015fcc890802fd64484057e3224200ef1912101578c890802ff63484037f31a4200bf58d2100df8c69086b7f5348401bea9a4207df9492103ef8a490803bf4248401dea124200df945210d6f8a290803be4148401de20a4207fdc8521007dc4290802ff60484097e302421adfd412103dfeca1081f7f650840f3fb284203bf994210bdfaca1081efc650840fbe32842079f1942103dfec81080afe640840fdf3204202af99021005fac81081fbd64084015eb204207bf1902103dfec610806fe63084017eb184207bf18c210befea6108037d530840f7f3104207df9482103ef8a41081fbf420840fdea104207fb8c821007da6410866fe6108401bf2884217df144210c7ee8210803be4108401de2084218fd1042100768821081fef210840ffb1084200fb4842103fea4210812fe60084017eb004217dfd4021006fec8a805b7e6454001beb22a016df19150006fec6a80027f635402bbf31aa000df58d500aef8c6a805b7f435402bbf21aa000df50d500aef886a80037f6254001bf312a000df58950006f8c4a801e7c625402dbfa12a000cfd0950006fc84a80037d42540019ea12a016df109500aefe64a80037e3254001be992a015df0c950006fec2a80037e6154001beb0aa000df18550004f8c2a805b7f4154001bf20aa000cf90550006fa82a805b7c41540019e20aa015dfcc550006fc62a80037d315402bbe18aa000dfc8550006fc42a80037d2154001be10aa003dfd815001cfec0a800f7b605402dbfa02a004df101500aefe60a80137c30540097fb2c8003bf99640026fccb2000e7e65900277eb2c8004df59640004facb20012fc65900057eb248001bf98e40005fac720012fc6390027bfa9c8000df54e400a77c872000bbc439000f7f3148000bf58a40006fca52004f7c5290005dfa148000ef50a40005fcc320013f661900017b30c8000bf58640027eac32000
  | 3 => 0xfa048202ef1024110f7ecb20887be6590443deb2c8221ef196410077ec72088fbe6390401deb1c8223ef18e4110f7ea7208873f5390447df29c8221ef54e410067aa72088fbc5390401dfb148200ef98a410077ac520802bd6290401de3148221efd4a4110f7ca5208033e5290443dea948221ef14a4110e78a52088fbf3290401df1948200ef4ca4111f78652080abe6190443dfa8c8221ef946410067ca320887bd5190443de28c8221cf1464111f7e632088fbc3190401dfb048200ef982410077ac120803bc6090443dfa848221cfd424110f7ca120887bd5090443de2848223efcc24111f78612088aff6550401bfb2a82009fd954101dfccaa088afd65504077e32a8222df1954101cf8caa080aff64504017fb1a8201bf98d4100df8c6a088b7f5350401bea9a8200bfd894103df8c4a08037e5250445be2928202efd09410077a84a080aff6150401bf28a8222df14541017ee82a0803be4150405de20a8202fd10541005fec0a0812fc6050445bfa828202efd94410177cca2080bbd6510405de3288202efd8c410177cc62080bbd6310405de3188220efd4c411067ea62087fbe5310441dea988200cf54c410ff78a62080bbf6210405df3108202ef588410057ac42080bbc6210441dfa908220ef948410067ca420883bd5210441de2908220cf148410ff7e6420803be3210401de990821fef0c8410177cc220886be6110405db3088220efd44411077ca2208033e5110441dea888220ef1444110678a22087fbf311043fde1888202efd80410177cc02080bbd6010405de3008220efd40411067ea020883be5010441dea808220ef140410ff7e602087fbc301043d7fb2c6200dfd9631004fecb1880efe658c43d7eb2c6203bf196310f6f8cb1880e7c658c4017fb246202bf99231005fac91880afc648c4037eb1c6201dfd4e3100efaa71881efe628c4017eb146200df94a310f6f8a518803bf428c401dea146201f7cca31007ba6518806fe618c401bf28c621edf146310077c8318803bc418c403ef98c6201fdcc63100fe86318812fe608c4017eb04621edfd423100fb86118876ff654c401bfb2a62009fd953101dfcca98876fd654c4077e32a621ddf1953101cf8ca98802ff644c401dfb226200afd9131015fcc898802fd644c4057e3226200ef1913101578c898806ff634c403bfa9a6201df54d31005fec49881efc624c401bf292621ddf149310077e8498803bd424c4037fb0a6200df945310eef8a298803be414c401de20a6201fdcc531007bc6298807dc314c403fa18a6200bfd8131025f8c0988777f504c40f7fb2e4203bf9972103efccb9080e7e65c84377eb2e4207df59721004facb9081efc65c840f7fb264202bf9932103f7cc99080abe64c84017eb264207ef593210057ac99081efc64c840f7fb1e4201bf98f
  | 4 => 0xbec42508017fb0a8400fdd8542005eec2a1002fc6150801fa30a8400bd1854214ef8a2a100bbf4150805de20a8400bfd8142025f8c0a10a77f5050805dfa028402ef1014214f7ecaa10033f6550853df32a8429ef5954214f78caa10a73c6550801dfb1a8428ef98d420077ac6a10a3bc6350853dfa9a8429cfd4d421477ca6a10a7bd53508019ea9a8428ef14d420177ec4a100abf6250805d7b128429efd494203f7ca4a101f3e5250853dea928407ef1494203e78a4a10a3bf325080fde1928400efd85420076ec2a1003be6150801deb0a8400ef1854200578c2a1003b461508015a30a8429efd454214f7ca2a10a7bd5150853de28a8429cf145421477e62a10a3bc3150801dfb028400ef981420077ac0a1003bc6050853dfa828429cfd414214f7ca0a10a7bd5050853de2828428efcc1421477860a101eff658c80fbfb2c64079fd963201dfccb1909efd658c80f7e32c6407df1963203cf8cb1901eff648c8057f3246407ef992320157cc919002fd648c80fdeb246400af5923203df8c919006fd638c803bfa9c6401df54e3203dfcc51901f7e528c80fbe2946407efd0a3203fdc851901fbd428c801f6a146400eb50a3203fbe6519007ef328c80ff61946400bf98632005fac31909f7c518c8097f3046400bf5823213efea11909aff654c801bfb2a64009fd953201dfcca9909afd654c8077e32a6426df1953201cf8ca99002ff644c8057f3226400bf59132015f8c89901eff634c803bfa9a6401f794d3200efaa69909bdd534c801aea9a6401bfd893203efca49901f7c524c801dfa126400fb909320077a8499003ed424c801d6a126401fbcc93203fbc649901fdc324c803f61926400bfd8532005f8c29909b7c514c803ee18a6400bfd8132025f8c09909b7f504c803ef9826400dfd925112efcc9288037d649444bbe324a200dfd8e51126fcc7288037d63944013eb1ca224df18e5112efe87288937e4394401bea1ca224df10e51006fec5288037e629440f3f314a200df58a51006f8c5288977f42944019fa14a200df90a51006fa85288033d429444bbe214a224dfcca51006fc65288037d3294449be194a203df9865101cfcc32880f76619444bbfa0ca225df10651126fe63288937c3194401bfb04a200df98251006fac1288027d6094401be304a225dfd025112ef881288937f3094449be184a221bfd964101dfccb20886fd65904077e32c8202bf5924110f7ea92080bbe5490443deaa48202ef1524100dfcc720802fd63904037e31c8221dfd4e41006faa72080bbf4390447df21c8200ef50e4101778872081efe62904017eb148200df94a4110ef8a52080bbf4290401df2148200ef50a4101778852080afe6190401bf28c8221df146410177e832080bf74190405fa20c8204bf98241005fac1208877f5090405d
  | 5 => 0x100600100600000200100100000700600000000000400200100000000200500000500700000100000100c00200100100000000000100000000100300000000000000000500500200000200000100000100a003000004008003000004001006fec8a98c37e6454c01beb22a630df1915300efec6a98067f6354c07afb1aa601dfd0d5300efc86a98077c4354c01bfb12a600df98953006fac4a98037c6254c0f3e312a630dfd0953186f884a98077f3254c03af992a601df0c953006fec2a98037e6154c01beb0aa600df18553004f8c2a98c37f4154c61be20aa601dfcc55300ef862a98037f6054c013fb02a600df98153006fac0a98037c6054c61bfa02a630df1015300efe60a98077c3054c5f7fb2a8603bf9954317dfacaa180efc6550c037fb228601bfd8d4300efea6a18077d5350c05efa1a8601ef90d4300f7886a1807dc4350c017fb128607bf1894317ef8a4a180bbf4250c017fb0a8600bf1854317ef8a2a180bbc4150c017fb028604bf1814317efea0a180bbf4050c0fbfb24a407df9925203e7cc92901f7d649480f9eb24a407df1925203efec72901f7e639480fbeb1ca4009f58e5203ef8c7290bb7f439485bbf21ca400df50e5216ef8872901f7e629480f3f314a407db98a5203efe852901f7c429480fbf994a407df0ca5203efec32901f7e61948013f30ca407df5865203ef8c3290bb7f419485dbe20ca42ddfcc65216ef8632901f7f609480fbf304a407df58252004fac12901f7c609485dbfa04a42edf1025216efe61290b77c3094805dfb2e8402ef997420167ccba100bbd65d08059eb2e8402ef197420177ec7a100bbe63d0805deb1e8402ef18f421677ea7a10b33f53d0857df29e842cef54f420067aa7a10afbc53d0859dfa968407ef94b4203e7ca5a10b3bd52d080fde2968407cf14b4215f7e65a101fbc32d0805dfb0e8402ef987420057cc3a100bbd61d0805de30e842cefd47421677ca3a10b3bd51d0859de28e842ccf1474215f7e63a10afbc31d0805dfb068402ef983420177ac1a100bbc60d0859dfa86842ccfd43421677ca1a10b3bd50d0859de286842befcc34215f7861a101eff65908077f32c842abf5964203df8cb2100afd64908535eb248401bf98e42005fac72101efc6390855bfa9c8400df54e4203dfcc52101f7e529080fbe2948407efd0a42017de852101fec42908017f30c8400bf58642156f8a32100bbc41908097f3048400bf58242156fea1210a6ff6550801bfb2a84009fd954201dfccaa10a6fd65508077e32a8429df1954201cf8caa101eff6450853dfaa28402ef9514214f7aa8a100bbc54508017fb1a8401bf98d4200df8c6a10a77f5350801bea9a8402efd0d421477c86a1003bd4350805de21a8402bfd894203efca4a101f7c5250805f7a128407ef9094203f7884a1
  | 6 => 0x585bc24a82a15c00022653e0006ea0009de00091400079200019800017c8a200094400049e2a063a33220e9fe0003ae0000001d600000046a0008ec4f83740000009100004d400046012a60c0000000002d64e60000000009962de81e3962f085e3ea0000000009321a200000000000000073001200028400089e1360006d600000000000000000000029c49840c0f40004567480000009b8a300000009308300341b25e20000000f600009a6e296068200000000030200057e00047a0004100006265566b62da2c40bc1de03e6363c800000055e81800015a08200008e92600076090c00000009e00057c2a48be7be60e84c0000a800075a00026600000037010657a0000000000002040004946f4000352122676a0a00000025875800003c00097c00088a9c64ba000a360d000052e29840200000070200042a00000012c75000033c4080009da60a9ec0006fe2300004040004e80008ce1da27062894e9e89029660007968e05c250e42e6145be4da6b400000000047600035000000000055861259817e0000006a20008da18a00087250042694226e74c0000000000000005127e21b40000000000002aa00000020000000000000059079a00000031000000021800000050a0000009f800084a56a00e00000000200500000000400500300300000600200000300000200000600000100700000000000000100600000200300000000400000301d00300200000000000100600000000100000000100100000200100200300000300000200000100000200100100100300200000000100100000000100000000000000300200400000000400400b00900100500e00000000600000400300200000000200000200000000000000400800000100000001300100300000200100100200000100000000700000b00700000100000000000000000100300000000000000100200100200000000400200000100100000000300000000400100100000000000400000700000100100100000800000000700100500000100200100400000200600000200000300200000000100100400800500100000000000000300700400a00000800000000900400000000a00100100200400100100800000900000200000201200100100200200000200c00000100100d00000300000000100100601100000500100000200c00000000400000100000000102200000000000000000100000300300000300100800000800000000800300000300100100300000100300000000100000000000300400000000500400200000300000100000000100700100200f005008000000001000000002000004000005025001001000000005000000002001000003000003006006001000005003001001000005003002000005000000000007000000000005000005004005004000000001
  | 7 => 0x7a08600027200098c95e4e20005b40009ba0000001b80000000000006620009f45c050c0000000003ac2087de90a7ee0008280d290e3f018048086800037e7a88ac36c0000000009480000000000000000000000000000002dc84666e96e0000007e444e0000000000009c46fa9ea30a0000000000000000001523f415082c7a00000000006060004ac00047c8e618885c0da3a276a37a0001700000000a02906d40006507b40b80e408c00000000000000045884295a0004320000c86c84f00000005de00053a00000031800000000000000010800064013e14814a1fc9788a4000244a1e000a120007563b20b25168060000007c259425a46c32a14c9800000f075422e3da98a1460001903de46242c1f800072a0000000000f20000007c477000033e0002e60004fa4ea0000005d600000012606e0000000006b2a325308640007240005100000001c86105c80000000000000e20000006b018656272613c0002809a223265a00000070a54063400052695629400000040688600070e2020009a400000075e2ac3220000001a053278404a00000031e000000000000000000000a0800099c0004822143166224fc2e43208706e405e4f21c09406a065436200081a1b099800068a00074400a6243cc2c64c021c97681618200077e7000002762641625840000940006da00000032e0000000000000000000005aa0000000000000000000000008a095c00039a63c3ee3a00001dc2fe00000000043a2c80000000ac69c2423e801e2740008f00003d80000000000000000000000ae0007420005d80006420000000003e60000009be0b000051835c2243687ec2cc13200025c0000005b097058a93e7e88ca8c87a62ce16a3081f400000000000006831c1e400000072c92a2507a248a3400006780000000000008b283200000049c52400000049a10a00000099a0000000000000000000000c03860000002d00000009aa0000000007160000009fc0000000000626fca1a9a083865e0009d280e00063273204400000067c12e8d08222ae49269273c00000025200000000000000054a0007622220000009360000000000005924440008cc0000000002ea97a00000000000000019e79e0005a61ba8f600000093a6e08344ae8d67f89863d04685ee3067400fa68662e52000000000073a6be2e01023f602a7b00000ea7b60000000000000000000000008140000005a20005545380ec00000011c98435ea241ec6c63a40000008f2790a222065e04b000000000000077a23c00002400000000078261e00024e00038e0000000000000004aa7380000000009a800000066a0000009900000009620000007d40000005501be92c9d833658c57205a6ca7fe9ae9168ba3783920001924b60003c600039806a0002280000000000000002d41
  | 8 => 0x86a1d458802200000000066c8b80000004384240204d20006f861694c91871e9083764360400008bc36e4a80000005745486000000000000000008580001284741780002ca0000000000000d400000076600071032869a1ea9c838800000000000000000096c0000006a8216394000000000a000004308fc00000c94628a6de0000000009380002f60009ca00000000074a22c8c00002780000001740000000002f80000007dc1300000185146d84528ee14e0000009b600000060439e7940000aa2460000000000000967cc6720007b21ee63e000752a2623a9ac0006987ea32c38c0009f67a45346f667e88854e568448000312a287ce0000003140ce0000000005f40000000003b69d60007d20001a6000544a0e00000087a0002a800025e0840006580009720000009e66ae00000000000000000000082e0000000000005643808961440001c63426d2a1c27e69433829622088e4f63444c600000000000000000059e5f20540005868b40007641720000000004e483e0000003bc00000000000023800060230445a0006840004900d648400027c0005ec1c20000286c00002b40009540008845023d20000002b00062f40004c25ac5801e20000000000007040005ea00016e31a16600000000000000061c0001ac0009f00000000000000000000000000000000000000008080008480000005e68de3ba8944e000026800000062a3540000000000009825522bc43c00000072000062c0009b20001fa76800000039077819c00064e0000003e43c00000000008766dc06607451a0002e80c63e27f085239c00026234a6088dc3aa9dc84486e8f43fc2be7aa1049d456c3fe26a4f40000000000009940000000001565d454234e0005284d602e59a000000000000000000000000164508000000992a2c0005fc0880000c29c200018e00000000000033a70c0320003ce0000000006740000001d066000086026c9286d03f80004ce0000000003ec1160000000000009122b28001ae2b841c41a0008660001b600000087ea040001a80009b000000048664486225602c00011a0784c81403460000006300000000000008fe04e3c20002547ca9240004b879c1121966905825608c4a101ca6cc7bc0a270600027a5464420000000003247b800000000057858e00000061a7fc000a2000040a4a003600000000000000010e0000000fc00000024c3d689076e0000000003640006bc17600000020a13a43e0000000008fa0003dc0000005b80000fe3263340004662340000760009bc00038a07274e4d81d844a2ec7d82a272e7f26f272851c0ca00000000003034800000044c0007ac05000e1f287810ca185a00009045ce00000000021206c0e671c86c4b23b80384a615e00000081000000000029200000091a00029e7d0a2a00000055c42854c00
  | 9 => 0x2887c80000000000008560000026520002e25fe0000000002c000000037c4dc2fa0080009b40005e80009f20002600166ee8928ea0006a600001a0001ce0000000008d46560005660000002860004cc45e1cc7884be28234c76c42289a0009e23b00000000b40000004ca0000000000000000005a45fa2d21540008a89e000064c0dc00000000000000009c7800000000a68a64bc0008820002a61c40000000000002365360001fea2e0001240006e60003660005764c485408a2b600038200000000000000000000000000000000000013440095800000083a1609208040005b20ee98e8120480000000000004709cc00000000016c0008aa00000000092e0000000006a400000055a000000000a022ba00000000068e0007340000000004540000006460000be0606ec0001145ae2c23600006c492253c4120000009a600050675c5f000068c6ba00000016800000048800066800021a4a4064000000a0600068036a8f80000006880009067083d48501007e679841840e3a8a160000c40001f005c4ee4b46204ec8c22fc0e000013878e3586663caa145e424047200009200001c07e7d60001e60000005040000000003563e074605897400000078c5da1944140009643c40000005f893c84e0260004405f66aa78600004600000000000030c56e1420000000000009521f65dc11e5c40000000003b40000000000000009c051e5d22d87f400000000000000000000069e0000004647ae87483c0000008d877494a64a0561bc38452a4dea3482600071a1e81d272235a46e6963be23e77693499e88c5cc6481182480000de3f25ba4d00009ce0006c282400052c00000000000017a00089c85a4966f00b600048e00065c00000071200000000033000048c6640009fa00000000082018c0006ce00028e0002107146706ac0000000000008ae0001aa0000007c00000000a400000087c71800073e0007f69000004fe0008984166b845c1e00000002f26380425ca00000000000081c00000000098803a00000029aa0c00001497e0008400007c620c19a0007e030e08000009844680a0003a64200007da00004c00000007c21e0900005a861867a5d00ba9d03fa22a5b600000073696a2ee0f80008360e80007fa5220cc4504a25c60000524345960108e27ba00041e91c11078a5701840008b00000000008d28c677c0009500d81200000000009680040000000009ee3008020000003728e88800004786e800000000059c80c0000000008e40000008b60009e400028c91e07000047e7720001a4000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf6518d100065c6518d100069f6418d100069c6418d100047e7654d100047c7654d100063f6454d101863c6454d100065f6354d1000e5c6354d1001c7e75d89100047d75d89100066c52d891003cee76d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066e75d89100066d75d8910006af74d8910006ac74d89100066f53d89100066d53d89100066c51d89100066f50d89100047f755891001c7c7558910004bf7458910014bc7458910004df735891000cdc7358910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc631891003e6f751891003e6c751891003eae741891003ead74189100066f53189100066d531891003ee571189100066c5118910006e74118910006e441189100066f50189100047e769491003c7c76949100063f64949101763c64949100065f639491016e5c63949100066f629491003e6c6294910005767194910004be76d0910014bc76d09100063f65d09101663c65d09100069f63d091015e9c63d0910006af62d091003eac62d0910004be7650910004bc76509100063f655091014e3c65509100069f63509101469c6350910006af625091003eac6250910005b471509100547e76945100063f649451012e3c64945100065f63945101265c63945100066f62945100066c6294510004be76905100063f659051010e3c65905100069f639051011e9c6390510006af6290510006ac629051004db67190510004be76105100063f65105101063c65105100069f63105100fe9c6310510006af6210510006ac621051000736511051018f345110510005b6761051004eb6761051000737651051018f34651051000797631051000794631051018f375310510007355310510005b57210510007a76210510196b66210510196b46210510007a46210510006a4621051000736521051018f34521051018f37501051000ed4638c510024f4764c51004db4744c51000ed4634c51004db4748851003ee46288510024f4764851004db4744851001c7c76541100063f64541100b63c64541100065f63541100ae5c63541100066f62541100066c6254110005747154110007344154110027701054110024fa76c4110007b041c41100047f735941003c7c725941002c7c71594100247f70594100247d705941001c7e7558c10004bf7458c10014bc7458c100047f7654c100047d7654c10005747154c100047f755881001c7c755881003c7f76948100047d76948101663e65d08100063d65d081014e3e65508100063d655081003eae6250810006ad6250810005b471508100347f769441001c7d769441000579709441010e3e65904100063d65904101063e65104100063d651041005eb66110410004fb7644010007725144010
  | 1 => 0x842003eb542584200267750584200267550584200047f76944200047d769442012e3e64944200063d64944201265e63944200065d6394420006766194420006756194420004bf7690420004bd769042010e3e65904200063d659042011e9e63904200069d6390420006b66190420006b56190420014bf7610420004bd76104201063e65104200063d65104200fe9e63104200069d6310420006b66110420006b56110420197a42110420006cd6388420006e561884200047d73d971003c7e72d97100067671d97100067970d97100047f755931001c7c7559310024f4715931001c7c75d8f10014be74d8f10004bd74d8f100047f7558f1001c7c7558f100047e7654f100047c7654f1001c7e75d8b100047d75d8b100047f7558b1001c7c7558b100047e7694b1003c7c7694b10005767194b100063f65d0b101663c65d0b100063f6550b1014e3c6550b10005b47150b100057970947100063f659071010e3c65907100063f65107101063c651071000736511071019f34511071005eb6761071005eb5761071000737651071019f34651071019f375310710007355310710005b57210710196b66210710196b4621071000736521071019f34521071005fb2701071005fb1701071019f375010710024f5768c71005db4744c710024f5768871005db4748871005db4744871001c7c76543100057471543100073441543100277210543100047f735961003c7c72596100063f5359210004bf72592100063c52592100063c51592100263f50592100263d505921001c7e7558e100047f7654e100047d7654e101863e6454e100063d6454e10005747154e100047f7558a1001c7c7558a1003c7f7694a100047d7694a101763e6494a100063d6494a10014bf76d0a10004bd76d0a101663e65d0a100063d65d0a10004bf7650a10004bd7650a1014e3e6550a100063d6550a10005b47150a100447d769461012e3e64946100063d649461010e3e65906100063d65906101063e65106100063d65106100077251c421001c7e76d95100047d73d951003c7e72d951001c7e71d951001c7c71d95100447d70d9510024f571d9110014be76d91100063f65d91100063c65d91100063f53d9110004bd72d91100063c52d9110014be71d911004eb671d9110006b571d9110014bc71d91100063c51d91100063f50d91100047f755911001c7c7559110004df735911000cdc7359110004ef725911003cec7259110004be76191100063f65191100063c651911001c7c75d8d100065f53d8d1000cde76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100065f75d8d100065c75d8d100065c52d8d100065c51d8d100065f50d8d100047f7558d1001c7c7558d10004bf7458d10014bc7458d10004ef7258d1003cec7258d10004de7618d100065
  | 2 => 0x47f7558f2001c7c7558f2003c7e7654f2003c7c7654f201863e6454f200063d6454f2000e5e6354f200065d6354f20006ad644cb200074d534cb2001c7e75987200047d75987200047f755872001c7c7558720004bf7458720014bc745872003c7e769472012e3e64947200063d6494720004bf7690720004bd76907201a63f65907201a63c6590720014bf7610720004bd76107201963f65107201963c6510720005ad721072003c7c76543200b63e64543200063d645432003d6c72543200047f73596200047c715962001c7e7558e20004bf7458e20014bc7458e200047f7654e200047d7654e2003d6c7254e201663e65d0a200063d65d0a2014e3e6550a200063d6550a2003f2c5250a20005b47150a2001c7c75986200047f755862001c7c7558620004bf7458620014bc7458620004df735862000cdc73586200047f76946200047d769462010e3e65906200063d65906201063e65106200063d6510620006b66110620006b56110620007a4410862001c7e76d95200047d73d952003c7e72d952003c7c72d95200047e71d952003c7d70d95200047f755912001c7c7559120004df735912000cdc7359120004f77159120004f4715912001c7c75d8d200047f7558d2001c7c7558d20004bf7458d20014bc7458d20004f77158d20004f47158d200047e7654d200047c7654d200063f65d09201663c65d09200063f655092014e3c6550920005b47150920024ec764c9200074d534c92001c7e75d85200047d75d8520014be74d8520004bd74d852001c7c75185200047e76945200047c76945200063f659052010e3c65905200063f65105201063c6510520005ad7210520006b76110520006b4611052003c7c765412003d6c72541200276820541200047f735942003c7e725942003c7c725942003e3f425942003e3d42594200047c71594200063f535902003cbf725902003cbd725902003e3e525902003e3c5259020004bc71590200063c51590200263f50590200263d505902001c7e7558c200065f5358c200065e7558c200065d7558c2003e5e5258c2003e5c5258c2003e9f4258c2003e9d4258c200065c5158c2003ecc2158c200265f5058c200265d5058c20026cf2058c20026cd2058c200047f7654c200047d7654c201863e6454c200063d6454c2000e5e6354c200065d6354c2003d6c7254c2001c7c7598420006745198420006777598420006747598420006b77498420006b4749842000677539842000675539842003e76529842003e74529842003eb7429842003eb542984200267750984200267550984200047f755842001c7c7558420004bf7458420014bc7458420006745158420006777558420006747558420006b77458420006b4745842000677535842000675535842003e76525842003e74525842003eb7425
  | 3 => 0x47598640006b77498640006775398640006755398640006b6439864005eb4439864000676529864000674529864005eb74298640006b54298640026775098640026755098640026b74098640026b540986400047f755864001c7c755864000674515864000677755864000674755864004eb4745864000677535864000675535864000676525864000674525864004eb74258640006b542586400267750586400267550586400047f76946400047d769464000676619464000675619464010e3e65906400063d6590640006b661906400065f6354d4000e5c6354d40024bc7650d4001c7e75d89400047d75d8940024bc7650940006af625094003eac6250940005b4715094001c7e75d85400047d75d8540024be7690540006b4619054002738405414003c7c72596300047c71596300047f7558a3001c7c7558a3003c7f7694a300047d7694a301663e65d0a300063d65d0a3014e3e6550a300063d6550a30005b47150a3001c7c75986300047f755863001c7c7558630004bf7458630014bc7458630004ef725863003cec72586300047f76946300047d769463010e3e65906300063d65906301063e65106300063d6510630006b66110630006b561106300056c72595300057471595301ad7b70595300063f74595300063c74595300ac7f73595300065f73595300066f725953003c7c72595300066c725953003c6c72595300ae5f32595300067771595300047c71595300067471595300047471595301ac7f70595300067b705953001c7e75d91300047d75d9130014be76d91300063e65d91300063d65d91300063e75d91300063d75d91300a63f53d91300a63d53d9130004bd72d91300063c52d9130004be71d91300063c51d91300063f50d91300a4be76191300063e65191300063d651913001c7e75d89300047d75d89300066c52d89300047d76949300063f64949301763c64949300055d7394930004be76d0930014bc76d09301663e65d09300063d65d0930004be7650930004bc765093014e3e65509300063d6550930005b47150930024dc764c9300065d654c9300078d424c930025d8704c93001c7e75d85300047d75d8530014be74d8530004bd74d85300067451d853001c7e75185300047d75185300067451185300047d76945300063f649453012e3c6494530004be7690530004bc769053010e3e65905300063d6590530004be7610530014bc76105301063e65105300063d651053001c7f76541300ac7d76541300063f64541300b63c64541300055f73541300275830541300047f755932001c7c7559320004f77159320004f471593200063f75593200063c75593200063f535932003e3e525932003e3c525932003eae3259320006b77159320004bc7159320006b47159320004b471593200063c51593200063f5059320
  | 4 => 0x4211cf345110421196b67610421195b576104210c6b57610421004b576104211973765104211973465104211cf375310421007355310421195b77210421197a67210421195b572104210c7a57210421196b66210421197a66210421197365210421197345210421197a63210421007a532104211cf375010421004ef76484210047f755802101c7c7558021006b441580210b63e64d91501c57b70591500ae5e63d8d5003c7e72d8d500047e71d8d500ae5c31d8d5001c7d70d8d500ae5f30d8d500053f7458d500b53c7458d500056f7258d500056c7258d50005777158d50005747158d501bd7b7058d500b53e74989500053d74989500066f629895006d79709895007d7b70589500b53e74189500053d74189500ad5e73189500055d731895003e6e62189500b63e76d09500b63d76d09500063f63d095003e3e62d095003e3c62d09500053e71d09501b63f60d09501673b60d095014d3d749095003e6c62909500047f76509500047c765095003e6c62509500057771509500057471509500063f76509500063c76509500063f63509500b53f72509500b72f72509500072f625095003e3e625095003e3c62509500072c625095003e2c62509500073771509500053c715095000734715095000534715095014e3f605095014f3b605095003c7c768c9500b53e748c9500053d748c9500072d428c9500047f764c9500047c764c9500072d424c9500b53e74d85500053d74d85500067761985500457970985500053f74585500b53c74585500055f73585500ad5c73585500056f72585500056c72585500357b70585500047d731855003c7e72185500063f42185500063d42185500067731185500067431185500063f63905500053d72905501a63c62905500b53e71905500063c619055010e3f609055010f3b60905500047f76505500047c76505500063f63105500053d72105501963c621055010d3e71105500b73671105500063c61105501b63f60105501073b60105500047c768c5500065f638c5500047f764c5500047c764c5500053f744c5500b53c744c5500047e76c85500047d76c85500b53e74c85500053d74c85500ad5e73c85500055d73c85500073441c85500047e76885500047d76885500053f74885500b53c748855003e6c62885500047f76485500047c76485500053f74485500b53c744855003c7c76085500b53e74085500053d740855003e6c62085500073441085500257a70085500057970085500047f735964003c7c72596400b63f42596400047c71596400b63c415964001c7e7558e400047f7654e400047d7654e400047f7558a4001c7c7558a4003c7f7694a400047d7694a4003cbf7650a4014e3e6550a400063d6550a40006ad6250a40005b47150a4001c7c75986400067451986400067775986400067
  | 5 => 0x65d639472110e3e65907210063d659072111e9e63907210069d63907211063e65107210063d65107210fe9e63107210069d63107210073651107211d7345110721195b576107210e6b576107211973665107211973565107211979663107211979563107211d7375310721007355310721195b77210721195b572107211973652107211973452107211d737501072101c7e7558321006b4415832101c7f76596210063f74596210063c74596210047f735962103c7c71596210047f705962101c7e75d92210047d75d92210063e65d92210063d65d92210063e75d92210063d75d92210063f53d9221006ad72d92211a63e52d92211a63c52d9221006b671d92210063c51d92210063f50d92210063e65192210063d651922101c7e75d8e210047d75d8e2101c7e7558e21004bf7458e21014bc7458e210047f7654e210047d7654e210063f6454e211863c6454e21005747154e211663e65d0a210063d65d0a21005b671d0a2114e3e6550a210063d6550a21005b47150a21006af648ca2100cef764ca21006af644ca210074d534ca2103c7d76946210063f649462112e3c649462103d6e729462110e3e65906210063d6590621005ad72906211063e65106210063d6510621005ad7210621005cd73c86210076651c862101c7e7558221004bf7458221014bc745822101c7e76d95210047d73d95210047d70d9521014be76d91210063f65d91210063c65d91210063f53d91211a63e52d91211a63c52d91210063c51d91210063f50d91210047f755912101c7c75591210e4f77159121004be76191210063f65191210063c6519121196b7611912101c7c75d8d210047f7558d2101c7c7558d21004bf7458d21014bc7458d21004fb7058d21024f87058d210047e7654d210047c7654d210063f6454d211863c6454d21005747154d21004be76d09210063f65d09211663c65d0921005b671d0921014bc76509210063f655092114e3c655092103f2c5250921005b471509210dc7e76945210063f649452112e3c6494521004be76905210063f659052110e3c6590521004be76105210063f65105211063c651052101c7c75d81210047f755902101c7c75590210c4f471590210063f75590210063c75590210063f535902103e3e525902103e3c525902103eae32590210c6b77159021006b471590210063c51590210063f50590210047f7558c2101c7c7558c2103c7e7654c2103c7c7654c211863e6454c210063d6454c2100e5e6354c210065d6354c21006ad644c8210074d534c82103c7e769442103c7c769442112e3e64944210063d649442103d6e7294421004bf7690421014bd76904211a63f65904211a63c6590421005ad7290421195b67190421014bf7610421004bd76104211963f65104211963c6510421005ad721042100736511
  | 6 => 0xf655094114e3c6550941006af6250941005b471509411e47e769454112f3441945410063f659054110e3c659054101c7c75d81410fd3f7354c411071f7354c411953c7254c410ff1f3254c41007377154c410053c7154c41007347154c41005347154c4111e3e6154c41187366154c410053f7054c410063f75588410063c75588410063f53588410063d5358841016af7258841006af52588411963c5258841006ac52588410062c5258841006b471588410063c51588410063f50588411963e76948411963d76948410053d73948411953e72948411972e72948411963f62948411963d62948410053e71948411a63e61948411773661948410053d7094841014be768c841004bd768c8411953f758c8411953c758c841006ad628c8410053f754c8411053c754c8410071d534c841006ad624c841005b7714c841005b4714c8410053d73944411953e72944410063d62944411e53e719444110736719444110e3e619444112f3661944410053d70944411dd7671d96310065d73d963103c7e72d96311265f32d96311dc7e71d96310067671d96310047d70d96310047f755923101c7c75592310047f7558a3101c7c7558a310047e7694a310055d7394a310063f65d0a311663c65d0a310063f6550a3114e3c6550a31005b47150a3103cdf764ca310065f654ca310078d424ca3101c7e76946310055d73946311275731946310063f659063110e3c65906310063f65106311063c65106310047f755823101c7c755823101c7e76d95311247f73d95311247d73d953103c7e72d95310047d70d9531014be76d91310063f65d91310063c65d913111e3f53d913111e3d53d9131004bd72d91310063c52d91310063c51d91310063f50d91310047f755913101c7c755913111cbe76191310063f65191310063c651913101c7e75d89310047d75d89310047e769493103c7c76949310063f64949311763c6494931004be76d0931014bc76d09310063f65d09311663c65d0931004be7650931004bc76509310063f655093114e3c6550931005b471509311dc7e76945310063f649453112e3c64945311275431945310fcbe76905310063f659053110e3c659053111f94319053111cbe76105310063f65105311063c651053101c7c75d81310047f735972103c7c725972103e3f425972103e3d42597210047f70597210063f535932103e3e525932103e3c5259321006b771593210e6b471593210063c51593210063f505932101c7e7558f210065f5358f210065e7558f210065d7558f2103e5e5258f2103e5c5258f2103e9f4258f2103e9d4258f210065c5158f2103ecc2158f210065f5058f210047f7654f210047d7654f211863e6454f210063d6454f2100e5e6354f210065d6354f210d47d769472112e3e64947210063d64947211265e6394721
  | 7 => 0x93200cec765093200dcc73509320074d5350932005e47150932016af7650932016ac76509320072f75509321f72c75509320072f65509321f72c65509320078f73509321478c735093203eaf635093203f8f63509321472f53509321478e53509321472d53509321f78d53509320070d5350932007a77150932005ac7150932007a47150932005a471509321f72c51509321478c31509321f72f50509321478f305093201c7e75d85320047d75d8532014be74d8532004bd74d853201c7c751853201c7c75d81321057671d925112e3c64592511ed7671d8e511265c6358e5103c7c7258e5101c7c7158e511265c3158e510047f7058e510bd7671d8a5112d3e7498a510053d7498a511255e7398a510055d7398a5112d3e7418a510053d7418a5103e6e6218a510066d6218a510cd767118a5112e3e76d0a5112e3d76d0a510063d63d0a5103e3e62d0a5103e3c62d0a510053e71d0a511e63e61d0a511673661d0a5114d3d7490a5103e6e6290a510047f7650a510047c7650a5103e6e6250a51005777150a51005747150a510063f7650a510063c7650a510063d6350a5112d3f7250a5112f2f7250a5103e3e6250a510072e6250a5103e2e6250a510072d6250a5103e3c6250a51007377150a510053c7150a51007347150a51005347150a5114e3e6150a5114f366150a5103c7f768ca5112d3e748ca510053d748ca510072d428ca510047f764ca510047c764ca510072d424ca5102d7671d82510047f735825103c7c72582510063f42582510063d425825103576711825100679601825100cbf7650e410047f7558a4101c7c7558a4103cbf7650a410053f7550a4110d3c7550a4103eae6250a41006ad6250a4112f374194641005b671d8e4111d3f7354e4110f1f7354e411a53c7254e4111f1f3254e410053c7154e410fe3e6154e410053f7054e4110d3e75d8a410053d75d8a41005b671d8a41006af6298a41196b66198a410053f7558a4110d3c7558a410063f7558a410063c7558a410063f5358a410063d5358a411a63c5258a410063c5158a410063f5058a41005b67118a411a63e7694a411a63d7694a410053d7394a411a53e7294a411a72e7294a411a63d6294a410053e7194a411963e6194a410053d7094a41004be768ca41004bd768ca411a53f758ca411a53c758ca410053f754ca4110d3c754ca410071d534ca410053d73946411a53e72946410063d629464110d3e719464110f36719464112e3e61946410053d709464110d3e75982410053d759824104eb6615824110d3e75182410053d751824101c7e76d95410047d73d954103c7e72d954112e3f42d954112e3c41d95410047d70d954101c7c75d8d410047e7654d410047c7654d4101c7e75d89410047d75d89410047e769494103c7c769494103cbc76509410063
  | 8 => 0x63c6518542006b561185420073451185420063f75185420063c75185420063f53185420063d53185421963e52185421963c5218542006b75118542006b65118542006b551185420063c5118542006b45118542006345118542006b73118542006b431185420063f5018542005b67618542006b67618542007377518542007347518542006b76518542007376518542006376518542006b66518542006b56518542006b46518542007346518542006346518542006b76318542006b66318542006b56318542006b463185420073753185420073553185420c6b762185420c7a76218542197365218542197345218542007375018542006b77518542006377518542006b67518542006b57518542006b47518542006347518542006b77318542006b67318542006b57318542006b47318542006b75318542006375318542006b65318542006b55318542006355318542006b453185420c6b77218542196b67218542006b75218542196b65218542196365218542006b55218542196b45218542196345218542006b73218542196b63218542196b43218542006b77018542006b67018542006b57018542006b47018542006b75018542006375018542006b65018542006b55018542006b45018542006b73018542006b43018542196b72018542196b4201854214d3c75d8142006b461d814214d3e75981420053d7598142005b67198142005b57198142006b461981420053f755814214d3c75581420059f73581421459c7358142005b77158142005b47158142006b4615814214d3e75181420053d7518142006b461181420047f755923201c7c75592320063f75592320063c75592321463f53592321463d535923203e3e525923203e3c5259232004bc71592320063c51592320063f5059232016ae6450a32005e47150a3203daf7650a32006af7650a320072f7550a321ff2c7550a3203f2f6550a3203f2c6550a321472f5350a321472d5350a32007a77150a32005ac7150a32007a47150a32005a47150a321ff2c5150a321ff2f5050a3201c7e75986320047d75986320067451986320047f755863201c7c7558632004bf7458632014bc745863203cec72586320067451586320047f755823201c7c755823201c7e76d953203c7f73d953203c7d73d95320047e71d95320047d70d95320047f755913201c7c7559132004f77159132004f47159132004fb7059132024f8705913201e5f7654d3203d5c7654d3201e5c7654d3203c5c7654d320074f7254d3203d5e7254d3203d5c7254d320074c7254d3200e5f6254d3200f4f6254d320055c7154d320055f7054d320063f65d09321663c65d09320071d53d093203f8c32d0932145ad74909320074d53909320063f655093214e3c65509320071d535093203f2e525093203f2c5250932005b4715
  | 9 => 0xd73981530053f74581531853c745815308d5f73581530056f72581530056c725815300577715815300574715815301c7e75d89430047d75d894301c7e75d85430047d75d85430067451d854300674511854303e5f7358e5203c7e7258e5203c7c7258e5203e3f4258e5203e3d4258e5203e5e3258e5203e5c3258e520047c7158e5216e5c3158e520047f7058e5216e5f3058e520063f74986520063c74986520047d739865203c7e729865203e3f429865203e3d429865203e76719865200677319865200674319865203e77219865203e7421986520047d70986520047f735825203c7c725825203e3f425825203e3d42582520047c715825203e7b705825203e7b205825203e7820582521853f7654f421853d7654f4215d3f7354f421671f7354f4203d3e7254f4203d3c7254f4215f1f3254f420053c7154f420053f7054f420063f75987420063c75987420063f53987420063d53987421a63e52987421a63c5298742016b671987420063c51987420063f50987421463d6454e4200e5e6354e420065d6354e420047f755864201c7c755864201c7e76d95421763e74d954214e3d74d95420047d73d954214e3d42d95420047e71d95421763c41d95420047d70d954201c7c75d8d4203cbd74d8d420047e7654d420047c7654d4203cbc7650d4201c7e75d85420047d75d85420067451d85420067765d85420067465d85420067675d85420067575d85420e6b674d85420067753d85420067553d85422067652d85422067452d85420067750d854201c7c7518542006745118542006776518542006746518542006777518542006747518542196b774185420c6b67418542006b754185420c6b65418542006b554185420c6b454185420067753185420067553185420c6b74318542006b64318542006b543185420c6b44318542196765218542196745218542196b64218542196b442185420067750185420c6b740185420c6b4401854201c7c75d814214d3e76d954214e3e76d95420053d73d954203d3e72d954203d3c72d95421763f62d95421772f62d95420053e71d95420053d70d954214d3c75d8d420053f7558d4214d3c7558d42005af7258d42005b77158d42005b47158d42005bb7058d42005b87058d420053e7654d420053c7654d421453f7354d4214f1f7354d4203d3e7254d4203d3c7254d4215e3f6254d421872f6254d421471f3254d420053c7154d420053f7054d4214d3e75d85420053d75d85420073451d85420073675d85420073575d85420073765d85420073465d85420073753d85420073553d85420e6b762d85420e7a762d85422073652d85422073452d85420073750d854214d3e75985420053d75985420063f65985420063c6598542005b671985420053f755854214d3c755854214d3c75185420063f6518542
  | 10 => 0x900a00000000200601100600100000100300000200000000000200100000100000100000001600200000400300300100000100100200b01a01100a00000300800500102000b00100000000400600400200400200101000400300600b00200000000500a00500001500100000200100200000000900200e00500900000202600600000300000800e00e01100200300d00000300200000200000300000201500200000100900000700000500001101400000000100a00500100000500401000000400200500100101500000400100100100000100100400700302c00000000200100400000500100a00100100900100700200400000000701200200000000400000100201001001200500200000200300000500100000300300001600400600300000b00000f00000400000000100000200102300200100100c00501200000801400900200200e00300500000100100200f00200300700000701900000100000200000000200500c00100001400000700300202c00900300600200200000100700900300000100c00000100100000400100000300100500200000000000000100800400400101200500000500100000100000800700500000000300000000500300000300200400100000c00300300000000100000000300501400200700100000100000301100200000000100200000500300000000200200000000400500000300000000000100000401701900200e00d00200000000000800000100500000002d00600000700200600000100300300f00001a00102200300e00000f01200301500000000b00000300500b01400a00000400200600300300000000400300300300e00701500f00100600000500800c00100000000800000800000700500000100000900000000400600000000000000b00000c00300100100b00100700600501200500200700500500000100100300400400900b00900700000000200700100200200300100000b03300100100700000600d00301200000001100000300a00000300000201200a00001101700d00100100000000000700100400800100b00000300300600300200100100000100d00800900200800600500000d00100000100600700100600700800000300a0000080030090060090020011863e64d915320d5f735915300577715915300574715915303c7e76d89531853e74989530053d74989531355d739895300576719895300575719895313d5f73589531853e74189530053d741895303e6e62189531853e74d85530053d74d85530ed5d73985530067761985530053f74585531853c74585530f55f735855301c7d731855303c7e72185531de5f32185530067741185530067441185531de7531185530047d701855301c7d73d815303c7e72d81531ae5f32d81530047e71d81531ae7a30d81530855
  | 11 => 0xaf40008dabae09a000a1e00028458000017e366000000032aa859aadc8d82266b8c747fc3fcc6a0003c464e8de2a80008f60007ce4baade00005471628eca6000846000a9c9fe000000000000000000a320000000003e81da724000a2e00000000000000000067e4e40000001f253e696bb67aab0a6bed909087c400000000000000000000071e00091e89ab3800057e0009ea000d7aad46a025e098000b249c2cc00000000004c834c000a5e000ce82b83dcb0c48a000ce069aa8600034a51ec0896e8cc0b6490c8c4e0aec6da53831e4d2950000d823fe6b4b8412299e00089ea8ca2aa18000000402000c460b8000000000000d0c384518a9e00011200036e000a6cbb23ca1eab1e8ca0000000001140004ecc485ae000b788be90ac24bee2fa94ac9c7a24bc4ee1fa000cb0a240008a8000132000000000bd8d524609420006d00000009065165a40005da000000000c1800000021c3ec9e40000000004d8bdc7180003b2000706cf28ba8440007ca6186d2000a94d26cca59000056800081200083855c000c9a3440009920000000005be000d4a000a16ac600000000081e40835cb188945e4000000000c3a000d488560900000006907c804a00000000000000000000000000016858600072e8027cc1f87f26a4b4677e0006f6ca87ba0006c203c0008143104b6678a9a750d402b624e086230b8e93600041639480a00000000062e000c14a7478c3e642e9f493a37eaa6c2a0009ba0001368dc0007701b80f6c6e74020e000588b0e16405c6b239c0000f2000b7a22c7ea1c40000000000007440ac000000000816b2a6e67869f679841283e000632334000d70bfc7546c408a7420004dec120002de42cd449a60006665c61ceb2021e850c9ebf03427360380006e41fc30869e1763725f873c088734b80d1cc902927d6852c8e3f00001ba5320780522b02a26c60000003fa1c67ac10011c756d5eaca6165827a08b4d8ab428f0126b00c1a0000000000000005fc0000009a2c267f093c000a50d6caa20e2d46156cb8820a98a92cfcd4c3de87acb2d42b6e000af2a70000a3c000000000c5e3a01d86b08f8000b1063a41c3c8ce67a69be58427cb28140bda000c06084380d3a0009860d070e0e467a5d20b40420000002087e6c7e6287d85ce1d20008f48ee4cca1aba212abaa81c6aa57a56c8b031cc04b068889f8000000c1605e0a200060c0000000000004d019a000d2ab4a248bd6bd49fa7f632437c0008c20c00d2d76000ae20000000000000005a63b427433000081a040398cf8222a7c7dc7f4000af89260005460000000a40004c097e1ee32eaea8a078053ad6635a27e78e000c422d407ca7e6c00c27e831a47600400900000000000100100100000100100300000001600200d00100000300500000000200000100200000100900
  | 12 => 0x44d04a26286000be40000000000000009f20022a0000000000000000a3663c0003a47a82f09ca0000000002ca000000746000b2e48600000000076660e8f296cc229824989ec5d63ccb880009f01cab7415c00026882613c9d800058a0005966444a08d40000008e4566b08a086100000000000001e8b7097c00000000000080e3f8d0e4f20008661020000ca26ac4400018c00000048041e7889441789ee250000000000b4e000a380000009601e467400084e0009d6a4c4ae3c611eb3676c000634000be8a0a000000b6a2f285ebd217c3ee39e98412e37491a030b56c1e0006723a6000be019073e0000d6bbec0ca0caa4c5a966a145b60c80007c218a000bfe000000000000a58caa00089c7740007520000000a89380009e000055855e13000000075800000000074c000290000000b1c3f40c600051a8fe61ecc416c00000000000000000000000000812c00047e00009695800000053400000073250c0008d62e4000d56000d888eab98000000d1a91c1103e20009e8000000b8c0000000008e0cf611a4707b20003d214c000d220000009682e6000000ae8000000000000000000000a841a27600001160002040006fc95a0e09d4864b4c35e99c000000c3e232b9457c75eac260620ca4ab1442a478884280056c20d5a612000620d181f684c0000003b876200062cacc46a16082c000000afe0628620000000005ca7283705feccc85c0000000ce0006cc4a458c07000000016a0004b20005080000000000000004282e0890ad84b400083c2acc680a00000002e800036000000024004ea64654b582789fcd860f419eaa000017a0be7fa5aa328000466a0227abca4f678266e5a0c8aa285c81d0468234694a0e00000000083a5fabc82207720000007daa1c6e200055092a00000023c000ac84363042a6050708c0a1bc0000000000001ae000000d2445e07a0000002d20006300000000004640b01c89b67b06c85e6c720006429de332134ad661443452c0004febde3685f40aa15eb1a764d36000cd2b480007fe036c6454a9aabb45d800000000000039ab9a03445c40a0004541c021a0000000002ea0007a49da624000000000a10b40abc976576afa0b200092010e000000c6ccee1de000000336000000000000a48b5024488c00025a00000000098a6465dcb304189ce05ad6ecde7f8a3a6bc8368e8ab09c0b68d1079ca602c400000088e000ba8322d681aaac4b7e9006a8c328c4ad059887ea7a6222ae0dc9168409b000000039200028c000000276626496000ac03bed200000000005c09dca12594bb09902d6d3c25277800000032072a54c94e602b16cd885898e0006ac636000506692bcc4be3d80fa2aaab4b0446eb220000004f48e2000000b6c6f4000bea9ac0820000006ee0000001d40003b08c0000000000a524047765e2
  | 13 => 0x326a2209e9d0c2e00077caee000c0200046200000000000000009200000070002e0bc000022794000a000000001f41a46b6c96492202d920007ee000256000000000000686018442000b92000000ab8502000792000a048b20000000941c215a00000004800000000084ad601fe5f60e6c360008d2000000bc0000152000c56aae000640d2e00000000068a474a781f000091810a58e8d0d1e73ab12530000932c52000572000000abe00000000040eace1dccda1984b800000043000082ecd655a24c3d41720000000003ba6fe1e298c00000028200000061c0001620006f8000be230000000099ac4c000000426000ab22ecc947c69ae7bcbc27681b450a0005c200070a8228724e82b25f24008244ac66a0002e21b2bfacc800004c0003f60000000005000000000009784460f000000014800000091014a00044c0001e036a4a6a6e90c2f60004f8000000000000000000b34000000000670000000000000b52874000000cec57026654e00075a49c2ee00002800066865a00021243e0121d60000005148100005627be7b49ccb642f882800000041a020c80000d124140007260000000000ae000648c30bce3140d40000ea52a8489c400000072040c0d8000876d7200056400c00079ea34000000662000000000c0e0000a6246000338bd000096a06e57401c000000000000000d16b769280009800c42160007d264a458312c76000948d5c41071a66032a30e242cfa0005bcad2b9e272000a0688a06a7b6b824c200047c9540003027022ce4c6ce4000000000000b9665c80c5a22360000009c62280da2be9b48a255495c922b3c712cbe13e5b40002103d09647d023e0000004a20006ce0000000001a09e6bbcc86c1047abba0001b0000be61864b0730cd43e00682fe52e93069c026aba2c8000970000c7ccae0007de00026277a07ec922d8a4497a68c0f82883400003ead64b62000d84000000000000000000c6659c2dc000800000c7a5040006d4000258000000b2c2fc8b63828c84883b6ae0000000000a68000940ba028a0000806ae2a4c620000003e400000000010800600038c0000000008983168184aa36c00400001686868e5b8000c540000000006d600016665eb020000003780000000004fa9bc424af644a664000066b2609c0006fa38a00000020aafca5a50e56ad940002183880649346847d4c00000cac000000b72bc4a460004dc26e92ec58c282ba892c70924946356d8006c0fe2945922d030644400048407208e62abc621493ea5c6de1ac952b3e146000698806a4e000d5046ca30a3e33ad3ecd015400000086cd06000d08cdc1a8b5c608adacce988c4a000352376a8843c04474a000d620006f20001589980000002cc4505c42645ec1ec95e10c974a8e5e8bf4a208708ecc7889665292ccbaca2a9602aa6a174b
  | 14 => 0xc2c18e000000804000ce2b3a000b86bec3648786a2d96710cb6a901cc150cfe4ce396af05f0526748d2854063e1924ea71c9a87aeb904d4d54a424209b2b5eae6b5a23838679a0007b800000031878a000552d7e61a4c400044e704000bb894cb9c9046560761887e203e8c63c25d41707901be00076e000000714000000ae40006dc224886784d32520000c5c000880b32c4e350b66d8cba6452348000c88cc64820ecc842f400025400000000022a8329a43469a0b8a000000a56600000180d3051c99623a12000026c0002c200000040683000003a00000000000000072c73800000066c9948820ba8a430a3a2d0a2068ae9623da4324562608426f00000000000e80000002700004a842200000000ec4000082a0000005783bc000058000d6abf8000298a54bf63586eab54c820000000001a602c54800002456e00053c43a0002da0008fa000b608aad7c86a29a00048e33c4d6c605120000000003ce30cc5037a7e0680796a6285a5e04fc184354a802b4000000d784e6aaa56001445a0001385280ee000000000544b7c0000000003d60000001045d08bc00000075c6e074e4ca0006ca0000003f287c0000001286760005105de00067c20043859e0008a65360004e2060d340009e200000000000032c000bf2000542524000ca0c340468b800000076a00000086e1068fc7222c607400000000029c00000000000000000000000000048c0008340007c02c0a2c5ac0000000000000000000007e400049e000522000000c98124a720000006887eccf40008acaac13a6a600014290222e010000d8ea8201e70c6506e83ae9d29141b680890ed004400fc9564da556bac638a406ba0001e600a5cc08cd2c144a8a19444836229639024ac3c0de5b233e8ce6d83c0d14d5814e19c34e682604d383aa01a5a82bca76ba4196cc26ec85425c000d749723ac00000000000060ac1ccbc4f0ceaca45b0ab6000a66000d4e000912d0286064c6580005ee29e00047238e0008e69b80cc00016e000494cf09c800000000049a000000cb45ea000c383a80001820000005ba11800
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc2c625d0215400126b0e20842a80cb89188410855003c3c432e010aa000d30415c0215400186cca38a85200030d5947150a400052ac18a530c8000a558314961900651690ea12c32000329d88715094019652310e2a128007a2c82595428c00186cca38a85180030d5947150a3019552412c220c6000c2f741c9654c001858e8392ca98003191cb71595300061bba0e2b2a6000c34741c5654c0018aee638aca9800319dc8715953000632390e2b2a6000c37841c5654c0018690838aca9800315cc8715953000516412cbb226000a3481597644c00107b0e296c8980028760c52d91300041ec3cca3226000a1d83994644c00107f0eb28c8980028b20965191300051a40aca3226000a4d8314b624c00107b0fb24a4980020fe1d65d093003d16412cba126000a3481597424c00116d033b284980020f21d655093003d16412caa126000a3481595424c00186cca38a84980030d594715093003c2e43aca9926000a5481595324c0015190ca12649800383595424c930005c240a849926034a2c82596414c00146902b2c82980ca8b20965105300051a40aca20a6000c37751c564c8001868ea38ac9900030de1471593200061a428e2b264000c37531c564c806586ca438ac9900cb0d148715932019653190e2b264000c347114564c8001868e3a82c9900028d2056454f2003c2e43ac6a9e4000aa48159132c8001c1ac8a9a65900028d20564947201945a40aec20e4032c2c655c841c800f858e4b22a1900028d20564543200043a40aeca9c4000c36651c5428800186aca38a85100cb491487150a200061bb28e2a124000c34651c54248001858cab90829001e932097558c2003c36412eca984007c4c7258d5308065948e43a2c2100cb2908576104201974210ac6208400786e829d953c400f45d05b2a85880030dd947150b100061a328e2a162000b3180d9441c40014690ca9883880034914972107100050ec18a4b242000c36641c5538400f45904b2a85080030d9947150a100061ab28e2a142000a1d8314b64440010bd0e296c6880029360c52d891000526c1cebb122000c54639c6524400f8c8c538ca4880ca2d20476509100061bb28e2a122000c34651c5424400192ec638a84880032518c715091000653b10e2a122032ca4621c54244001c48a231082880038918a51105100070a328c620a2000a348654c41440651690cb90828800349149721051019553436c420a2000e27651884144001c48ca3108288003a1d8c621051000742318c420a2032ca687188414406594b0e31082880cb89e14621051019712428c420a2000e27531884144001c4aa6310828800389d40621051019712314a420a2000c54631c55044001c48c420aa0880021d6187154c100061b328e2a102000c35651c5420406594cc438a84080031cdda5144010
  | 1 => 0xf0638a84990036120c7150932196c3b18e2a126400d27531c5424c801b0ca638a84990034954c7150932006c2a98e2a126400d05531c5424c801a4ea038a849900361cc071509321049a40ae9314a207c2e625d062944658ccc438a8528802c360e6250a5103d17c32c4a14a240e2662dc5429446585cc438a85288030ddd87150a5119713310e2a14a200c35631c5429446586cc438a8528803499887150a5119613310e2a14a200d25621c54294465868c438a852881f0bdd9428ca510059240a85194a200c2f76509329440164902a1265288028d20542582511955340ec5314823491c8754d329040186eca38a84a08030d19471509411949b410e2a988244d17321c5531040126b0038aa6208ca8b20953588410051a40aa6b108232a2e85d49621040154d03a92c420802a360c525884117517438a4b108232c2e871496210465c1d06292c4208028b60c525884119706c18a4b108200a0d83149621040145d02292c4208cb89dc4525884100516c00a4b108200c37751c56210401868ea38ac4208cb8914871588411965210aed1908232c2c7558a32104652390ea9a6420802c5205534c841006163aac49908200e0d53589321040194ac438a64208cb0b9c9629444103d17416caa146200c37651c5428c401868ca38a851881e17a1f654ca3100707b2a849946200b8481509328c48746d03b2883188028760c52d913103d17416caa126200c37651c5424c401868ca38a84988cba108563107210051bc32a620e4200c36759c7648840186aeb38ec9108020f61e65192210041fc3aca3244207875861c55388401868c838aa7108020fe1d65d0a212141e43acaa144200c36651c5428840186aca38a851080383d91534ca21005a240aa69944234c2e72d92518840185ccab9083108030d1907154d211945b434e3a124200c37651c54248401868ca38a84908030ddd471590210061a3a8e2b20420785c8758d5308401c1ac8a9a641081f0b9c964944210061a28aec2084232c2c655c8410840186aed28882108cac9a0a511042100692b94a22084200c37855d841084018690abb082108030dd4d76104211961b292ec2084232c34525d8410846594c64bb082108ca8d21953104210061abb2a62084200ca5764c84108401e0aa6990821081f0b189749895019632310e2a12a007a2e86d89425400161b0631284a81038918b715095019616310e2a12a000c37761c54254001868ec38a84a80cb8918871509500061bc30e2a12a000c34861c5425400186ec638a84a800349d8871509501961b310e2a12a032c34621c54254001a48c438a84a80cb0918871509500061bb00e2a12a000d33601c5425400f858eca1464a8002c9205428c950006163b284992a000b2481509325400146902a10c2a80cb0b18972105501a616316e910aa007
  | 2 => 0x65185420051b42cc630a8400a358598c615080154b05318c2a10028de1563185420051a42ac630a8400ab38058c615080156100b18c2a10028da1463185420051ac28c630a8400a3686d4c61508014690da98c2a10028da1953185420051a432a630a8400a3686d40615086554d05ba8c2a1062a960b75185420051ac1eea30a8400e2682dd46150801c4b05ba8c2a10028d60375185420061bbacea30a8400c36871d4615080146b063a8c2a10ca8da0875185421951a410ea30a8400a35801d4615080146d0b398c2a10028d616731854219553414e630a8400aa5829cc615080146f0ab98c2a10028d21573185420051b428e630a8400a35851cc615080192ae6398c2a10caa9a0873185420c552c10e630a8400ab2801cc615080156300398c2a10028da1f53185420051a43ea630a8432a3682d4c615086546905a98c2a10028d60353185420070ba9ca630a8432aa68294c615080154b05298c2a10028da1d53185420051a43aa630a8400e178354c615086546d04a98c2a10ca8d20953185420051bc02a630a8432aa68214c615080154b04298c2a10028da1732185420051ac2e6430a8400e1553cc8615080146d0b380c2a10028d61670185420051bc2ae030a8400a34855c0615080152f06b80c2a1002a520d701854200553c12e030a8400a36851c0615080146b0a380c2a1002a5a0c70185420054ac18e030a8418aa5821c0615080146d0fa80c2a10028d21f50185420051ac1ea030a8432a3682d40615086546905a80c2a1002a9e09501854219552412a030a8400a3685cc0615080146b0b980c2a10caa9a0b301854200552c166030a84008b6870c0615080116b0e180c2a10028da1430185420051ac286030a8432aa6820c0615080154b04180c2a10030d1d461d81420061b3a8c33028400c3575186605080186eea30ac0a10030d1d461581420064bb98c2b028400c9473185605080186cea308c0a10030d5d4611814200692288e2a146400d27751c5428c801a48ea38a851900349e147150a3200692428e2a146432d27651c5428c865a48ca38a851900349d4c7150a3200692a98e2a146400d27501c5428c80161b08392a69901e8721953d093203d86412a7a126428d0d7454e424c80f4390ca9a84990030dd9471509320061a328e2a126400d15531c5424c865a4ca438a84990cb491487150932004a643aa6a126400d45531c5424c80161d0ea9a8499002c321d535093203d87432a6a126407b0c8654d424c80161902a9a8499002c3e01535093200782a9ee2a126400d0d531c5424c801a48a238a8499003610c471509320c6523b0e2a126400d27751c5424c801a48ea38a849900361dcc7150932006c2398e2a126400f05531c5424c801a4f0a38a849900349214715093200693b28e2a126400d24651c5424c801b0
  | 3 => 0xcc00280bea3600000000009b8f60f800000fe00072c200000000000000dae62c9b4978000000000196000e41e80000380002b60680000000d1240000000030e001740014687b665f9ce4ea444e0000483a749c20300015b6a7ea84000000388a002000030200000b7800b52863a9c4ba800000ba638b6488000000000000b30005712832000a0ae88c18c00ae4c99b08212c001d400270002fc00000511aa0019e00000000ee00090438000023a41000171760009a778e0b40b00b1a653a0ac88d0000000029000248359560033400046ce8000000000178cd8dc2899a7a000d0274000e8d901431000a5b5e4f31247a4600150000082f0d40026c3f34200204140000034a002a0782ca0a000000000022c00000ca80000000000000023ca611ad82e0000985a80044356c118a99800001546009ca7800d20007b800000000006a0000000000a70006901056000282c6da2accb9d6640000018800000001f64819c8338200362000226a0a42a816000008c9b600320c51f82982e001b885aaa000008628a492b0a48c2c9148b680000000591d800000853500009218800001425a31e128005f2c4ac83088096d680a49a5a4b92aa6a8e001f0002dc661841c28c54800d61346f3103483ca89be9f8001d8000000071b4e3b328000000000000000002c0001da0019446170cc800000000007c00000000000000000100002ae950880000020234000005caf200026000004faa68a000589123d032c000000182a50cc958820000000258940fa360007d000000589a000001928900070222af21c42000000740034cd7262c737c0000b000000040002000000000000000c000040400c0301402000000200000400000010080100000000010000501c01000000040100008004010180100c0100404038000100100800000050000200400004020080300002010000000c00c0100402014030000001c0000c05008010240000410008020000001c03000000180d0000e0040701000000000040c0040500009000000000100000004010180c03c02018020040001c0601001004000040000400000070280400001000030080126902ba0c4a981e1b20970185531951b40ee930ca434a36811d2619480f4cd0598cc3290f28da07759874212d1b408eb30e8400a368590c615080146b0b218c2a10caa9a0a43185420051bc2ac230a8400a3485584615080146d03ba8c2a10028da0475185420051b40ea630a8400a348154c615080146b06288c2a10028d60051185420051b42e6230a8400a3585cc4615080154b05988c2a10028da1431185420051ac286230a8400aa5820c4615080146d03a80c2a10028da1676185420051ac2cec30a8400a36861d4615080146b07b28c2a10028d60365185420051b42cca30a8400a3686194615080146b06328c2a10028d60
  | 4 => 0x1790c4da5caf80099372190de238e6318860018619800000001ba76253380196e2f84098000bb2128a8da81b3ead3780010a92966000009a800000002d31877000002101b374000000007e0005a0021a9e800b09c82e00000000001ac0000072800001fe001fc5001e1309e4c000ddad600000809ea001ec6e8000020e150ca001b23390221000de800bb800c1b2c001d00014a002f0002880030adb0002a0ac00042aeb6e4500013916b8878000ae001f2062ceb49e61111cc68000d27c182a8000f0001aeb217a0000000000c3000568380002a00000d52fe0924cc59e40024e1a0040033c302d800330002f4001a03e27200000dc226d4932bdb46a9106230f27881c9e16c8f80000000580000000014af853000000000822e120e268b7e0000000242ae00094800000000000057800000008e1
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x250e2050954900845c75e051ad5c8020017a05a3001b004c1a10000f26000000030011b30451b3474e030e56f49007c3c01f5068ba92a9c5916070b2276dccb158c81c383103420300041894204008002c68500080160593a0b751854219489249801d4615080189173600731854219489a4a87d4c615086522492603531854219489a4a87d406150801304916107254d3219505259531c5424c8015049154c71509320054164c511c5424c801505950c471509320054164c751c5424c801505951cc715093200541a5d531c5424c8015049754c715093200509a5b851c5424c80150593214715093200541654831c5424c8015819020c715093200541a61531c5424c8015049854c715093219541a59531c5424c8655049654c715093200541e41531c5424c80150593d40715093200541657301c5424c801505939887150a5119609dd88150a329440182776205424ca5119449249801c553104012249160c525884100681e45831496210401a049160c525884119681dc5831496210465a047160c52588411950325d5358932104016049154d624c84119509a4b651c5428c40f40e97d95424ca3100681d9481509328c46542692d94715093119509a4b855d84108401c057654d32104210054164c621c5425406582476205428c950006091d88150932540658246261c410855019509249651c5428c00103498594715093019509249651c5424c00120c98595424c93003d0325d65509324c00160491595424c9300068159481509324c06542692e147159320005812456454d32c806582472205645432019509a4b651c542c400150593149721071019509249651c542840658248614972105100054164c525c84144001521901497210510
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x500360214008ca806a7e4583149621046540353eca40a8499462008812a565205424c9301950094eb2902a126498002404a664c525c8414406580243326292e420a2032c08219901497210510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4e
  | 6 => 0x138e
  | 7 => 0x3
  | 8 => 0x94e
  | 9 => 0x94d
  | 10 => 0x124e
  | 11 => 0x138d
  | 12 => 0x8e
  | 13 => 0x98e
  | 14 => 0x128e
  | 15 => 0x150e
  | 16 => 0x9ce
  | 17 => 0x12ce
  | 18 => 0xa0e
  | 19 => 0x130e
  | 20 => 0x130c
  | 21 => 0xa4c
  | 22 => 0xa4d
  | 23 => 0x20e
  | 24 => 0x20d
  | 25 => 0x140e
  | 26 => 0xb0e
  | 27 => 0x154e
  | 28 => 0x154d
  | 29 => 0xb4e
  | 30 => 0x144e
  | 31 => 0x28c
  | 32 => 0x28e
  | 33 => 0x148e
  | 34 => 0xb8e
  | 35 => 0x148c
  | 36 => 0x14cc
  | 37 => 0x14cd
  | 38 => 0xcce
  | 39 => 0x15ce
  | 40 => 0xd0c
  | 41 => 0xd0e
  | 42 => 0x160e
  | 43 => 0x188c
  | 44 => 0x188e
  | 45 => 0x164c
  | 46 => 0x164d
  | 47 => 0xe8e
  | 48 => 0xecd
  | 49 => 0x28956
  | 50 => 0x28b
  | 51 => 0x29396
  | 52 => 0x148b
  | 53 => 0x198c
  | 54 => 0x198d
  | 55 => 0x168e
  | 56 => 0x180e
  | 57 => 0x28216
  | 58 => 0x29556
  | 59 => 0x2cc
  | 60 => 0x2cd
  | 61 => 0x24e
  | 62 => 0xd0cd6
  | 63 => 0xd15d6
  | 64 => 0x184b
  | 65 => 0x18ce
  | 66 => 0x44d
  | 67 => 0x282d4
  | 68 => 0x2c294
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 72
  | 6 => 1308
  | 5 => 1740
  | 4 => 450
  | 3 => 63
  | 2 => 7
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
  | 7 => packedAt gbK7 (2040+((h/24+packedAt gbK7 (1872+(h % 24)*7) 7) % 87)*8) 8
  | 6 => packedAt gbK6 (53628+((h/436+packedAt gbK6 (48396+(h % 436)*12) 12) % 2296)*12) 12
  | 5 => packedAt gbK5 (90480+((h/580+packedAt gbK5 (83520+(h % 580)*12) 12) % 2526)*12) 12
  | 4 => packedAt gbK4 (28050+((h/150+packedAt gbK4 (26550+(h % 150)*10) 10) % 719)*10) 10
  | 3 => packedAt gbK3 (4557+((h/21+packedAt gbK3 (4410+(h % 21)*7) 7) % 76)*7) 7
  | 2 => packedAt gbK2 (575+((h/2+packedAt gbK2 (567+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc07fe01fffffff01fffffffd18f9f8c8ff1ff
  | 1 => 0xff83ffe07c07fffe0f807c02e73ecf3727ecc
  | 2 => 0xffffc00007ff80ffff0007fff07c70ff838f0f
  | 3 => 0xffffffff80000fffffff8003f807f03fc0ff0
  | 4 => 0xfffffffffffff00000000003fff8003fff000
  | 5 => 0xf000000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x90008a008950b110014a94548085858404b055
  | 1 => 0x845816d202c45a7520d036818632acb13256cc
  | 2 => 0x2ead403044ad08ab5a00432b3058505b830b0a
  | 3 => 0xb366565500800ce9ca560023b007a02d80da0
  | 4 => 0xfc7b9b9e73e6c030801820c3dff0003efe000
  | 5 => 0xc20401c18030700c10c604303fefffec000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xeee8eae0eea8eaa0eee8eae0eea8eaa0eee8eae0eea8eaa0eee8eae0eea8eaa0eee8eae0eea8eaa0eee8eae0eea8eaa0eee8eae0eea8eaa0eee8eae0eea8eaa0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15727
namespace PEqualNP.Outside.L_meta_15727
open PEqualNP.Outside.L_meta_15727.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_1_0 : Interval s1Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_1 : Interval s1Atlas 1 0 1 := bs1_1_0
theorem alls1 : ∀ k ≤ 1, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_1 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 1 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 5 := bs2_3_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 7 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 12 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 4 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 12 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 6 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 90 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 7 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 63 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_448 : Interval gbAtlas 4 448 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 450 := (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat (concat bgb_4_224 bgb_4_256) (concat bgb_4_288 bgb_4_320)) (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 bgb_4_448))))
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
theorem bgb_5_1728 : Interval gbAtlas 5 1728 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1740 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608))) (concat (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832))))) (concat (concat (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 bgb_5_1056))) (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)))) (concat (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504))) (concat (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)) (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728))))))
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
theorem bgb_6_1280 : Interval gbAtlas 6 1280 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1308 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 2 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeee8eae0eea8eaa0eee8eae0eea8eaa0eee8eae0eea8eaa0eee8eae0eea8eaa0eee8eae0eea8eaa0eee8eae0eea8eaa0eee8eae0eea8eaa0eee8eae0eea8eaa0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 50 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008241888 * 2 ^ 32 + 4004047520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15727.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,3]⟩,⟨.or,[0,3]⟩,⟨.and,[4,7]⟩,⟨.and,[1,8]⟩,⟨.or,[6,9]⟩,⟨.or,[5,7]⟩,⟨.and,[1,11]⟩,⟨.or,[0,12]⟩,⟨.and,[2,13]⟩,⟨.or,[10,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241888 * 2 ^ 32 + 4004047520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241888 * 2 ^ 32 + 4004047520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15727

open PEqualNP.Outside.L_meta_15727 in
theorem PEqualNP.Outside.L_meta_15727 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241888 * 2 ^ 32 + 4004047520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241888 * 2 ^ 32 + 4004047520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
