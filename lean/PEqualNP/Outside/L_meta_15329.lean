import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15329.Model
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


end PEqualNP.Outside.L_meta_15329.Model

namespace PEqualNP.Outside.L_meta_15329
open PEqualNP.Outside.L_meta_15329.Model
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

def SBf (j : Nat) : Nat := [2, 3, 5, 6, 5, 7].getD j 0

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

end PEqualNP.Outside.L_meta_15329

namespace PEqualNP.Outside.L_meta_15329
open PEqualNP.Outside.L_meta_15329.Model
def s0K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s0K1 (i*3) 3
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt s0K1 (4+((h/1+packedAt s0K1 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffff8b
  | 2 => 0xffffffffffffffffffffffffffffffffffff95
  | 3 => 0x26
  | _ => 0
def s0Atlas : Atlas := ⟨1,rawDecor 14 s0Pos s0Neg, 0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15329
namespace PEqualNP.Outside.L_meta_15329
open PEqualNP.Outside.L_meta_15329.Model
def s1K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (i*4) 4
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (5+((h/1+packedAt s1K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffdf0ffc1fc7
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | 5 => 0x6ff0ffe0f8
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffff81222d295b
  | 2 => 0xffffffffffffffffffffffffffffa2e4571ac5
  | 4 => 0x4489a54ae
  | 5 => 0x188ee398f0
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 53 s1Pos s1Neg, 0xaaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a00000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15329
namespace PEqualNP.Outside.L_meta_15329
open PEqualNP.Outside.L_meta_15329.Model
def s2K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x8000022981006f185c30dc41b083b087410
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x140320c020d030043808010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
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
  | 3 => packedAt s2K3 (98+((h/2+packedAt s2K3 (90+(h % 2)*4) 4) % 11)*4) 4
  | 2 => packedAt s2K2 (81+((h/1+packedAt s2K2 (78+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 4 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 5 => 0xefff0fffc3f8
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff012222c444db
  | 1 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 4 => 0x244e89aa3346
  | 5 => 0x1888ee3323b0
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 51 s2Pos s2Neg, 0xaaaa888888880000aaaa888888880000aaaa888888880000aaaa888888880000aaaa888888880000aaaa888888880000aaaa888888880000aaaa888888880000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15329
namespace PEqualNP.Outside.L_meta_15329
open PEqualNP.Outside.L_meta_15329.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x20000c3016002407194205000000000011000020bf42ee42bd42ed42ad42be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x128cc000109008072040a5aa9214b1414296a90818d428c31a84184bd522096aa041a5428434a8408740c010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x280002886050830a81814204381420c010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 10
  | 2 => 3
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | 2 => packedAt s3K2 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (228+((h/4+packedAt s3K4 (208+(h % 4)*5) 5) % 28)*5) 5
  | 3 => packedAt s3K3 (282+((h/3+packedAt s3K3 (270+(h % 3)*4) 4) % 14)*5) 5
  | 2 => packedAt s3K2 (117+((h/1+packedAt s3K2 (114+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x7f807fffff00fffff80fe07ffff81ffe47e3f
  | 2 => 0xf80007f00ffff00fffff0007f03ffe0ff863c7
  | 4 => 0xfffff8000ffffff00ffffff8003ffff03f83f8
  | 5 => 0xfffffffff00000000fffffffffc000003ffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x9083010a1112121210b1648b245a21449acdb
  | 1 => 0x425552a94628ea4a46c0aa855caa91aaa4562d
  | 2 => 0x5746a4ca6b4a48ec8bd581466633748f386346
  | 4 => 0x6464c68d8c8c8c88ece6cd94083c59c23683b0
  | 5 => 0x8787070e0f0f0f0f0f78f1e78f20610c3f7800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xaaaa8888a8a88080aaaa8888a8a88080aaaa8888a8a88080aaaa8888a8a88080aaaa8888a8a88080aaaa8888a8a88080aaaa8888a8a88080aaaa8888a8a88080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15329
namespace PEqualNP.Outside.L_meta_15329
open PEqualNP.Outside.L_meta_15329.Model
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
  | 0 => 0x7fff00ffffffffc03fff80fffffff807f8ffc7
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffff00ff807fffffffff01fc03ffffff18ff
  | 3 => 0x83ffffff00007fffc03ffffe0003fff80fe0f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x904bd8292cc51463a48bc0972d5658c3986bc3
  | 1 => 0x20950942450a288489148b2a5698ab4ca3b55d
  | 2 => 0x412652e88a534d293227558198c335974d18ae
  | 3 => 0x76389c8cec6c723223b9e6cd0313c6e18ee0f0
  | 5 => 0x7bc0e0f0f0707c3c3c3e78f1e3e207060fde00
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xc888c888c080c080c888c888c080c080c888c888c080c080c888c888c080c080c888c888c080c080c888c888c080c080c888c888c080c080c888c888c080c080, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15329
namespace PEqualNP.Outside.L_meta_15329
open PEqualNP.Outside.L_meta_15329.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x2b000000a2e607003e00327228ceac000579a4008b135c9908f3c40d89484942a3864680161d10800314ad2a002830801280280055150cc25a0400c00c0001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x8000049000000051001740038000000000000000000000000000000000000000000000000a00000000000000001dcc08121824ec57000000000000b000003f0000a84410000000240000000000000000000c4000000000020000000007f0021c006c2d20c1c14139a8000d00000000000160725300000000000114ea0000000000000000000000000000000108440008000000000000002e0000000000000000002688400000b1e40000000005600001b4140000000940000000000000000b2000000000000000000001e800000000218f0000f094000000110004c40000000000000000000000006800000000000000e630330fc00710e90076000000000000000000001d0009e0011800000000000f8000000000002a188fa26318005a120017c0000390000000000002a00038000000000000000000007c000c9b80000000009c470017000850005c00000000000043580000130012c00321b00000643786c0000178000000000000400001ec00690000000000000000000000000000400000001a940000000000000000000000023154000000000380000000ce001509000000000000003a000b600000000000000000000058dcc200000000000001e8e0061e00000002900034000000000560007c0000000000000001940000000000034019780000000000000198000000000002200000000000000604000060001e410000005008000004000000201000000003000080000010000001008000000008000200000000200010100400008000005008040000bd28487795090ebca7a15754f42afa9a855c5350aeea2a15d14542bda8285785050abca5195794632aea84655e520cb9ca4195794432aea80655e53d06baa7a0d7d4d41ae29a836f52506d8a4a0ded4141bc282835e528c6bca318d754231af290635e510c7aca218d754031af29e435d53c86bca710d754e219faa2433c54486bea690d714d21bda824378504867ca810cf55021afa98435c53087ca4210d794e40aea9c819e539033aa720678ca40ce194819e319033863204f94240af298815d531033ca6206754c40cf190819c321033c6220670c4409f28081ba501027ca9984f55330cf2a6619d54cc2bca5985794730cf206619c40cc2baa7186e102309faa2613c544c2dea4985b14930bba8a6174514c370809867d5130ce2a261cf524c2b8a4987314930a629261d7514c2b8a2987514530aa28a61db504c3b680986790130ce20261d8404c33080985794c309f2a6413d54c82bea7905714f20dc206415e53882baa710730ca209faa2413c54482bea6905714d20bba8a417451482bca6105754c20e619041b8400827ca9884f55310afa9e215c53c437081885794e10aea9c21d4318427ea8884f15110afa9a215c53442dea4885b14910af298215d53043a862086e10010
  | 1 => 0x14
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1510b00018a9000090000b40000059700328ca8c1c6c000384c0204200000000001e000c0140c6051a5834000080000000003b0004579d50000090094780007d500100000220900974e015804c000088008040800000085021010395185500ca4c62540318e18154086596014c21a919121086e06048421a65803210299600c440a658e50103285210130cc144404c30f5414930c3150524c34452d4530c5d50514c3145414530d1d48514c3445214530a6993504c34852d0130d4147404c21e6590130c314a404c3145190130a6982404c21e6510130c3148404c3145110130d2148404c3505110130a6994404c31a6510130e2d48404c3185210130e2148404c3085210130e4d44404c3185110130e4144404c31051101309598753c831b53103209359432083195310020e20c8400824e62d4f10c6d4c40c4255650c410c654c40043903110010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xa20182002003390221241c5600c840910e4b00622070052d44404c381a90a220261c01485110130a24e3a988190509750c84008285396a620621445d43110010
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
  | 4 => packedAt s5K4 (4077+((h/45+packedAt s5K4 (3672+(h % 45)*9) 9) % 459)*9) 9
  | 3 => packedAt s5K3 (2012+((h/16+packedAt s5K3 (1900+(h % 16)*7) 7) % 88)*7) 7
  | 2 => packedAt s5K2 (453+((h/3+packedAt s5K2 (441+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ffffffffffc07ffc0fffffffffc03f1fffc7
  | 1 => 0xf80ffff01ffffffffff03ffc07ffffffe3c7ff
  | 2 => 0xfff01fffe03fffffffffc0fff80ffffffc78ff
  | 3 => 0xffffe000003fff80ffffff00000fffc0ff80f8
  | 4 => 0xffffffffffc00000fffffffffff00000ffff00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xc0912591428847122c02cb2d2a52c6190d9bc3
  | 1 => 0x4e8448a4c514892454b0155485655a6a62c55d
  | 2 => 0x922d114289a512489955409ab109acb4b468ae
  | 3 => 0xe4c99d8b163a240eee69a603264e3718df80f0
  | 4 => 0x70e1e0c183c3870f38e38e3c7803820fb7600
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xe8a8c080e8a8c080e8a8c080e8a8c080e8a8c080e8a8c080e8a8c080e8a8c080e8a8c080e8a8c080e8a8c080e8a8c080e8a8c080e8a8c080e8a8c080e8a8c080, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15329
namespace PEqualNP.Outside.L_meta_15329
open PEqualNP.Outside.L_meta_15329.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x864423820001e8e0012000a00507e005e0000520200002600860c00727c4c821816000000005a4e8a000000780036005c6a0000007a323e481c04243a62006e00008c00704a2c00844400000000740014000076000000606800000058000046106c005480220e1a062e4066003c34000030880028000000002a000056140000100040010010001000020300001040204080017fd5005fe54017f55005fc54017fd4c03fe53017f54c03fc53007fd0c03fe43007f50c03fc43017fd48057f52017f94805fd52005f54805fc52007fd0801fe42007f50801fc4200ffcc801fe3200778c801fd3200ff0c801dc32017fd4405fe51017f54405fc51007fd0401fe41007f50401fc4100ffcc401fe3100778c401fd3100ff0c401dc31007fc8401fe21007f48401fc21017fd4005fe50005f94005fd50017f140057c50007fd0001fe40006f90001fd40007f10001bc4000ffcc001df30007f8c001fd3000774c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x24007bfd9420015fcca1001f7e65080053f328400bbf5942003efaca100027d650800f7e3284007bfd9020045fcc810002fd640800f7e3204007bfd8c2000dfcc61001fde63080036f3184000bf58c2003fbac610002dd630800f7e3184007bf9882003efea41001f7d520801bf79904007f78c82003fb8641001fec320800fe61904000bf98420005fac210003de3108001ee1884000fb8842003fd84210032fe6008001bf280400bdf140200077c8010003bc4008001ef9804000f74c02003fde401001ffa2008001f69004007fe48020035fecb8800afe65c400dbf32e20029f99710035facb880037d65c40013eb2e2002bf19710005fec988022fe64c4001df3262000af99310005fac988003bd64c40015eb262008bf19310005fec788003df63c40016fb1e2001bf98f10005fac788006fc63c4001ee31e2001b718f10005fec58801efe62c40017eb162007bf18b10036fea5880037d52c4001ef1962000f70cb10007bc6388003dc31c4001bf2862006df14310007f68188003be40c4001de2062000fe10310007708188003df30c4001ee9862004bfd9610015fccb08012fd65840057e32c2000bfd9210045fcc908002fd64840117e3242000bfd8e1000dfcc708003de63840036f31c2000bf58e10007bac708002dd63840037e31c2000bfd8a1003dfcc508002fd628400f7e3142004dfd4a10006faa508003de3284001ee1942009bf58610057ee6308003de3184001ee18c200afd0c610007a86308003f72184001fa10c2003bf98210006fca1080137c5084001df2042000ef10210007be6108003dd3084001fb8842000fec421004dfeca880037f65440013fb2a2002bf9951004dfaca8800afc6544013be32a20029f19510005fec888003bf64440015fb222008bf99110005fac888022fc6444001de3222000af19110005fec688003df63440016fb1a2001bf98d10005fac688006fc6344001ee31a2001b718d10005fec488003ef624400177b122007bf98910005fac48801efc6244001f63122000bb1891004efea4880037d5244001ef1922000f70c910007bc6288003dc3144001bf2822009df141100077c8088003bc4044001ef9822000f74c110007f62088003f610440077fb282002bf9941001dfaca0800afc65040017fb202008bf99010005fac808022fc64040017fb182001bf98c10007bcc608006de63040017eb182000f758c10005bac608006fc63040017fb102007bf98810005fac40801efc6204007bfa902000df54810007bc6408003dc320400d7f3082005fdcc410007bc6208003dc310400bfa1882000f50c410007ee4208003f421040097f3002000df9401001ef8a008003fb4004001df2002000ef10010007f08008003b84004001ef9802000f74c010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x3de324c001ee9926001f70c930005fec298003f7614c0017bb0a6000bf18530007e8c298002f4614c003ef98a6000f78c530007ba6298007dc314c0037fb026000df9413008ef8a098003be404c001de2026001fecc130007bc6098007dc304c003fc1826011f7d9530006beca98047de654c023eeb2a6011f71953008eb8ca98003df644c001cfb226000f799130007bac898003dc644c001ce3226011f7d513008fbca898047dd544c023ee2a26000f7d89300079ec498003de624c001eeb126000f71893003db8c498003cc624c001663126011f7d493008ebea498047de524c023eea926000d75493008fb8a498003df424c001ef2126000f750930007b88498003df614c001ebb0a6000f798530007bac298003dc614c0016e30a6000f518530005a8c298047df514c023ef28a6011f75453008fb8a298003df414c001ef20a6000f750530007b88298003df214c001ef10a6000f748530007b84298007df604c0036fb026001f6d813008fbea098047de504c001af2826011f75413008fb8a0980475c504c001efa026000f7901300073c8098003dd404c001ee2026000e71013003dfecb9000afe65c800fbf32e40029f99720085facb9001f7d65c80013eb2e4007bf1972003dfec990022fe64c800fdf3264000af99320005fac99001fbd64c80015eb264007bf1932003dfec79001fdf63c800f6fb1e4001bf98f20005fac79001efc63c800fee31e4007b718f2003efea59001fee52c800fbea964010fb54b20006daa59001fde32c800fee1964000bf98720005fac390003de31c8001ee18e4000df94320086f8a190003be40c8001de2064000f7cc320007ba6190032ff6588001bfb2c40009fd9620015fccb10032fd65880057e32c400cdf19620014f8cb10002ff64880117f3244000bf59220045f8c910002ff63880037f31c4000f798e2000dbcc710002fd6388001eeb1c4000b758e2000df8c71003afd6288019bfa944000df54a2007fde651001fde328800fee194400ffb0ca20007986510002fe61880017eb0c4000f78c620007b86310003ee2188001f610c4007bf98220006fca1100337c5088001df2044000ef10220007be6110003dd3088001f79044007fec8220075feca900037f65480013fb2a4002bf99520075faca9000afc654801dbe32a40029f19520005fec890003bf64480015fb224008bf99120005fac890022fc6448001de3224000af19120005fec690003df63480016fb1a4001bf98d20005fac690006fc6348001ee31a4001b718d20076fea49003bee5248001bea92400efb54920006daa49001fde324800fee1924000bfd8520007eec290002f761480017e30a4000fd18520005e8c290003de3148001ee18a4000df94120076f8a090003be4048001de2024000f7cc120007ba609001ffb2048001f71
  | 2 => 0x400af7ea820023be541002bdeaa08008ef1504000dfcc620023de63100036f3188000bf58c40047bac620002dd63100037e3188008efd0c400a77c8620003bd4310011de2188007bf98840005fac4200577f5210001bea908008efd08400077c8420003bd4210011de2108000f78c840007b86420002fe61100017eb088008efd04400077c8220003bd4110011de2088000f78c440007b8622005afe6010001bf2808015df140400477e8020023fa4010001dea008008fe500400477eca20057be651002bdeb288008ef194400477ec620053be6310001cf3188000ef58c400073ac620023bc631002bdfa988014ef94c400af7aa620053bc5310011dfb108000ef988400077ac420023bc621002bdfa908015cfd48400af7ca420057bd52100019ea908015ef148400a77e6420003be3210001cf1908000ef4c8400a77864200039c3210011dfb088000ef984400077ac220023bc611002bdfa888015ef944400af7aa220057bc5110029df9888000ef8c4400073c6220003bd3110029de1888000e70c4400077e4220003be2110001de9088000ef084400077cc02005abe6010001dd3008015efd40400af7ca0200033e501002bdea808015ef140400ae78a020053bf3010029de1808001f7d973000fbccb980075e65cc003eeb2e6001d75973000fb8cb98007df64cc003ef3266001e79933000fbac9980079d64cc003ee3266013f7d533009fbca99804fdd54cc027ee2a66001f7d8b3000fbcc59801ede62cc003eeb166001f718b3009fbea59804f5f52cc027ef2966013f754b30006baa59804fdc52cc001efa166000f790b30007ba8598003dc42cc003efb0e6001f798730005bcc398007dd61cc003ee30e6013f7d473009fbca39804fdd51cc027ee28e6000f7d0730007bc8398003dd41cc001ee20e6000f7c8730007bc4398003dd21cc001ee10e6013f7d433009fbca1980035e50cc027eea866013f71433009eb8a198003df40cc001ef2066000e790330007ba8198003dc40cc001ce2066012bfd9630015fccb1804afd658c0057e32c6000bfd9230045fcc918002fd648c0117e3246001bf58e3008dbac71801efe628c0017eb146012dfd4a30006faa518003de328c003ee1946000bf98630005fac318003de318c003ee18c6001bf98230006fca11804b7c508c001df2046000ef1023000fbe6118007fb308c003fc1846011bfd9530006feca980027f654c0057f32a6011bf59530015f8ca980477c654c0053e32a6000bfd91300077ec898002bf644c0117f3226000bf59130045f8c898003bc644c0015e3226001bfd8d3008fbea698007de534c023eea9a6001f714d30007be8698007de434c001eea1a6001f710d30005fec498003ef624c00177b126007bf18930007d8c498002ec624c023bfa926000df5493000fbe649800
  | 3 => 0xea90421bfb54821006daa410803ef420840ff62104207f78c82103fb86410872fe6108401ef1884200f70c42103fde421081ff62108401f69084207fd48421005fcc010802fd6008437be2804200dfd9250006fcc9280037d6494001be324a000dfd8e500d6fcc7280035e6394001beb1ca000d758e500d6f8c7280037f4394035bf21ca000df50e500d6f887280037f6294001bf314a000df58a50004fac5280037c6294001bfa14a000df90a50006fa85280037c4294035bf994a000df8ca50006bc65280037d3294035be194a000d70ca50006fec3280037e6194001beb0ca000df18650006fe83280037e4194001bea0ca000df106500d6fe63280037e3194001af18ca000df4c6500d6f863280035c3194001bf90ca000df88650006fa43280037c2194005bf304a0029f98250016f4c12806b7f3094035be184a008bfd9740015fccba00237e65d00053f32e8019bf59740046facba00027d65d00117e32e8001bf98f40005fac7a0006fc63d000f7f3168000bf58b400cefea5a00037d52d0001ef1968000f70cb40005fcc3a0002fd61d0001ef18e8000f70c740006fca1a00677c50d002d7fb2c8002bf996400b5facb2000afc659002f7eb248016efd52400b77ca92005bbd549002dde2a48001bf98e40007bcc720006de63900017eb1c8000f758e40005bac720006fc6390001dfa1c8018ef90e400077a8720063bc439000f7f3148000bf58a400b6fea5200037d5290001dfa148000ef90a400077a8520003bc4290001ef1948000f70ca40005fcc320002fd6190001dfa0c8000ef906400077a8320003bc4190001ef18c8000f70c640045fcc1200037e509002dbe2848000efd0240047f6812005bbf659002ddf32c8016ef596400b778cb20003bf6390031df31c8000e798e400077ac7200039d6390031de31c8016efd4e400c77ca72005bbd5390031de29c8000efd8a400077cc520003bd6290001de3148016efd4a400b67ea52005bbe529002ddea948000cf54a400b778a520063bf3290001df1948000e78ca400077a6520063bc3290001ce1948000efd86400077cc320003bd6190001de30c8016efd46400b77ca32005bbd519002dde28c8018efcc6400077c63200039e3190001de98c8018ef0c640007386320003bf2190001df10c8000ef48640007784320056be609002ddfa848016ef942400067ca12005bbd509002dde2848016cf142400c77e6120063bc309002f7fb2a8000dfd9540004fecaa000afe655002f7eb2a8002bf195400bef8caa000a7c65500017fb1a8001bf98d4000df8c6a0002ff625000f7e3128017dfd4940006faa4a0003de3250001ee1928000bfd8540005f8c2a0003de3150001ee18a8000df941400bef8a0a0023fb4050001df2028008bfd9440015fcca20056fd65100117e3288008bf990
  | 4 => 0x81ede628c401eeb146200f718a31107bea5188835f528c441ef2946220f754a31006baa518883dc528c401efa146200f790a31007ba8518803dc428c4036f30c6220f7d4631107bca318883dd518c441ee28c6200f7d0631007bc8318803dd418c401ee20c6200f7d8231007bcc118803dd608c4016eb046200f718231107bea118883de508c441eea846220f714231106b8a118886ff654c4057f32a6221bf59531015f8ca98802ff644c4117f3226200bf59131045f8c898806ff634c4017fb126207bf1893110efea4988037d524c401ef1926201f70c93100dfec298807f7314c401ef18a6201f70c53100fe86298802ff604c4017e3026221df1413100fbe6098807df650c403ef3286201f75943100fb8ca18807df640c403ef3206201f75903100fb8c81887fdf540c43fef2a0621ff7550310ffb8a818807df620c403ef3106207b79883100fbac418807dc620c43fefa90621fd7d48310ffbca41887fdd520c401aea90621ff714831007be8418803de420c401eea106200f71083100fbcc218882de610c403eb308621ff7d44310ffbca21887fdd510c43fee2886200f7d0431007bc8218803dd410c401ee2086201f7d803100fbcc018807dd600c4016eb006201f7180310ffbea01887fde500c43feea80621ff7140310feb8a01881eff65c84057f32e4207df99721014fccb9087afd65c840fbeb2e42009f5972103df8cb9081eff64c84117f3264200bf5932103df8c99081eff63c84037f31e4207f798f2100dbcc790802fd63c840feeb1e4200b758f2103df8c79081f7f52c840fbea964207f78cb2103fb86590803de31c8401ee18e4200bf98321005fac19087b7c50c84397fb2c4202bf996210e5facb1080afc65884017fb244208bf99221005fac910822fc64884017fb1c4201bf98e21007bcc710806de63884017eb1c4200f758e21005bac710806fc638843b7eb14421cdfd4a210e7dca5108037d5288439f6a944200db54a21007de8510803ec428840fef1944207f70ca2103dfcc310803de3188401ee18c4200fbc862103fee4310802fe60884017eb04421cdf142210edfeca9080afe654843b7eb2a4202bf19521005fec890822fe64484017eb224208bf19121005fec690803df63484016fb1a4201bf98d21005fac690806fc6348401ee31a4201b718d210eefea4908037d524840fef1924207f70c921007bc6290803dc314840ffb90a4200fb88521005fec090802fc604843bbe2824207bfd9421015fcca1081f7e65084053f328421bbf5942103efaca108027d650840f7e3284207bfd9021045fcc81081fbe64084015f3204200bf5902103f7ac810802bd640840f7e3204207bfd8c2103fbec61081edf63084037f3184200bf58c2103df8c61081fdc630840f6e3184207bf9882103efea41081fee520840fb
  | 5 => 0x9132045f8c89901eff634c8037fb126427dfd4932006faa499007ef324c80fef1926407f70c93200fd86499002ff614c8017e30a6401f70c532005fec099002fc604c84fbe2826401f7cc13203fbeca1901fde650c80faf3286407f75943203ebaca1901fdc650c80fefb206407f79903203fbac81901fdc640c84defaa06426f795032137baa81909bdc540c80fef3106407b79883203f9cc41901fdf520c80fafa906407f79483203f9ca41901fdd520c80faea906426f3548320069aa41901fdc520c80fefa106407f79083203fba841901fdc420c80fefb086407f798432005bcc21901fdd610c80fee3086426f7d4432137bca21909bdd510c84dee2886407f7d803203fbcc01901fdd600c8016eb006407f718032137bea01909bde500c84deea806426f714032136b8a019022ff65d04057f32e8225bf59741045f8cba0823be54d044bdeaa68201bf98f41047bcc7a0806de63d04017eb1e8208f758f41005bac7a0806fc63d040f7f3168200bf58b4112efea5a08037d52d0411dfa168200ef50b41007bc65a0803dc32d04017f3068200bf5834112ef8a1a088eff65904057f32c8223bf59641015f8cb20892fd64904037f31c8200bf58e4100df8c72081efe62904017eb148223dfd4a41006faa520803de3290401ee1948208bf986410077e8320823f741904017f3048200bf5824111ef8a120892ff6550401bfb2a82009fd9541015fccaa0892fd65504057e32a8224df19541014f8caa0893be5450449deaa28200bfd8d41007bec6a0802df63504037f31a8201bf18d41007b8c6a0806dc63504017fb128200fbd8941005dec4a081efc6250401f63128200bb18941126fea4a08037d5250401dfa128200ef50941007bc64a0803dc3250411fba0a8200ef90541005fec0a0803fb60504017db028200bf18141007f0c0a0802f86050449be2828208bfd9441015fcca208237e65104053f3288222bf59441046faca208027d65104117e3288208bf9904100dfcc620802fd63104037e3188207bf98841005fac42088b7f5210401bea908200f78c841007b8642088efe6110411dfa088208fd904410077a8220823f541104017f3008200bf58041116f8a020882ff658c4057f32c6220bf59631015f8cb18802ff648c4117f3246200bf59231045f8c918806fd638c441efa9c6201f794e31107baa718807dc538c401efa1c6201f790e31007ba8718807dc438c40f7f3146200bf58a31106fea5188037d528c403ef9946200f78ca31007ba6518807dc328c4037f30c6201f7cc63100fee6318807f4318c4017f3046200bf58231106f8a118807df308c403ee1846220f7d9631107bccb18883dd658c441ee32c6200f7d9231007bcc918803dd648c401ee3246220f7d5231107bca918883dd548c441ee2a46200f7d8a31007bcc518
  | 6 => 0x37fb228601bfd8d43047be86a1807be4350c03de21a8601f710d43005fec4a181efc6250c5dbfa928601f70c943005fec2a1802fc6150c03ee18a8600bfd8143005f8c0a18bb7c5050c03ef9828600dfd9152006fcc8a90037d6454801be322a400dfd8d52006bec6a90b77e6354801beb1aa42ddf18d52006b8c6a90037f435485bbf21aa400df50d5216ef886a900b7f62548053fb12a402dbd895216efe64a90b76f325480fbe192a42ddb0c952006fec2a90037e6154801beb0aa400df1855216efe62a90b77c3154801bfb02a400df98152006fac0a90037c60548013e302a42ddfcc15216ef860a9022ff65d08057f32e842cbf59742045f8cba1006fe63d0811ef31e8401b798f42005fac7a1023dd63d08016eb1e8401bf18f42166fea5a10037d52d08017f30e8400bf58742005fcc1a1002fd60d0859be2868407bfd9642015fccb2101f7e65908053f32c842bbf5964203efacb210027d659080f7e32c842abf5924200dfcc721002fd639080f7e31c8407bf98a4203efea52101f7d529080fdfa148408fbd0a42005fcc321002fd61908017f3048400bf5824215ef8a1210aaff65508057f32a842abf59542015f8caa1002ff6350801efb1a8400b7d8d4200dfcc6a1006fc6350801ee31a8401b718d42156fea4a10037d5250811f7a128407ef90942005fec2a1002fc61508017fb028400bf18142156f8a0a101eff65108057f3288407df99442014fcca210a6fd651080fbeb2884009f5944203df8ca21022fe64108037f3188400bf58c4203df8c62101efe621080fbfa908407df5484203f7e842101fee421080fdea108408fb50842005fcc221002fd61108017f3008400bf5804214ef8a02101eff658c8057f32c6407df99632014fccb190a2fd658c80fbeb2c64009f5963203df8cb1901eff648c8117f3246400bf5923203df8c919006fd638c851efa9c6401f794e32147baa719007dc538c801efa1c6401f790e32007ba8719007dc438c80f7f3146407dfd4a3203efaa51901fdf328c803f79946407fb0ca32005fcc319002fd618c803ef98c6401f70c632005fcc119002fd608c851be2846401f7cc23200fb8611901fdf658c80fef32c6407d79963203fbacb1901f5d658c80fee32c6407f7d923203fbcc91901fdd648c80fee3246428f7d5232147bca9190a3dd548c851ee2a46407b798a3203fbea51901f5f528c80fef2946407f754a3203ebaa51901fdc528c80fefa146407f790a3203fba851901fdc428c80fefb0c6407f798632005bcc31901fdd618c80fee30c6428f7d4632147bca3190a3dd518c851ee28c6407f7d823203fbcc11901fdd608c8016eb046407f718232147bea1190a3de508c851eea846428f714232146b8a11909eff654c8057f32a6427bf59532015f8ca99002ff644c8117f3226400bf5
  | 7 => 0xd313d8ce2950000001f18002dd80d16e2ae2da2d482680015b25023780026680020e8000000000000000000000001c5800298a8708b0000860000000c1a801d23081c28000001c600000017f0002169c09e4a2aad39b20000d787580014289800001c94d0370ee00029c0000002cd81f9629b39a01d1ab4a5a9b8281000010401000800400c00000800400403800400c00001c00000002401800c00400801401000400800000406402000002800000000801400800c00400001c00000003403000000000400000001800800800000c00001000000806c01001003400400404801c01400400002000801406801800001402c00c00c03400001000000000c00c00c0140340000240000000000000000040940f401403805000800400000801400000000401801800403400001001c00004c00002400800000000c00400000805800400400401800002001001801006801009000800801000801400c00400001800400c00000000800800c00000801402400001400000000c02c00002801000001000c0140000c800000000c00002000800404401400400000006c00001000805001c00401c00000407000000400c02801001400400c00003000001400001c02c00400404801404003006801400c00000800000000000400002000003803400400400400001400c01400801000001800008000000400801000401400800000800000c00c01800400000801000400400c00002400000001400000002402c00000c00001000400c00001000001800401000800000809800800801000c03400000c00000c08000402000400401c00000800400000001001000803800000401000c01808000001000400400401801801000800002c00400800400c00002401400001400802000c00000001400c00804800404000004001000c01400c00000000001800400001001400000803c0180000340240080000000000080000080040040640080000240000000000a400800001c00000001000800000800400001c00001402000000800000006003000000802400800800803000800000400000002000800800400000000400c00004800c00400402c01000800400000801400000000001804000400000003401c00000c00c02c01c00400005800000800800000000400800000001401800000001400400802c00400000400400400000401800000800c00403002800800001400000000c00002400800000800800400c00c01c00400801804003400008c0040b800001400800001c028117fb2e8602bf9974317dfacba1822fc65d0c037f3268601bf58f4300f7c87a1807de43d0c03de21e8607bf98b43005fac5a18bf7f52d0c03ee1968600bf98743005fac3a1807dc31d0c017f3068600bf5834317ef8a1a1807df30d0c5d7fb2a8602bf99543175facaa180afc6550c0
  | 8 => 0x8316d13fa8091c800057ae918287e0000000001338002bc238a47a600392f390c94c8001c42d2aa22959ada860000912110000000560d2afa1cd3040002c58bb937847aab9989b091a80b92eaf000000004ba2d0178d210802e0001648002ada930000000002b39c20002f21139ce26883b80000004e9942e28001e893e9a718e0029f7a7c9409a2a349af8848bd99e1ec82ea4b878a362a605485f21810a2c98282c52ab2558b89ed26f9869230000002171608cc1658002660231821479b9a290bc80000000000023101e2a598a10c0000000000000002df07f11323a9da301a608002f9846ab081427d800000044af100000028ab1082aaaca1881524f30100000010b8a10001ee0000002e48001959f58000000ca1d7a8f0001eeb120001af0002470791b105c82b1a622512b00023985b20691026ea54acb2228000000003110000001a909c0000000001270001d70001ec2f40d400018580008f1990000002f791b0000220058001ad0000600e98001ca1160000f39f0146000275087a5d01826a823a0b28f82f2028b39e506a0001f70320a914e819808a0f258830ae72152be8d89ac0b1231a1b95ca780b79f918826c95fa3b96406f2d9a7b92c19501c1e91eda2f036a4f98eace1198750db1452cf92a8f51a5867091a33152a8e0869d2ac91010aca2e8b61b78af84e0eb80029625ca6b0c880c27498f0001fc14f26e2838ef9fb03327a8fb8000ce8001cd9fb8fcae0096a540000d500015200000019c8000000e40001168c480009d80000024e0dc17099716c8128eb1690a52c28081f2a3708cabd9122f51872dd21980000000015880000001206400010980000028500000d931879ae512180018d9c70890f8a288f40d09399b4ad32e111e0ac0389c78000000aa1fe9ff07e9fa8000c095900000000005f8000000000000001ce8df05d1400000000000000000000000000000000001be0bc0000002050001bf8a28da23c8b18001651dbad80000002a88000000002cd0000000001b0196b000fd0000208cf21b0f10cfa6a27d225a6c0a400000000000020a26706b81111b90e9f2168a0789000023a0002938002f600000000028c8000850e60000e70000000a7000067aa080015f0000000002d78200000000000000002710000dd800000000041afd16b0a330387b0c6a2021f0ab0beb030f9a9210680007c0ae80021f8780001921f09cb1328999a20000000002e78002040000000000002ed0000001da8000ec8f5afc80012c80011d8a00000000000b217d8002ac0000000002a198c0000000001ac80021daca80006a80017597e1459038b40000000000001668fa0000000cc95d13a00007280011406680000c90783980013d00000000000021e90a8002fd9eb9a09a11b91a1afc000177a78a9f17993e22a0c807a0c6000003
  | 9 => 0x8003052ff00004d06f82286613a8000000002b7826071063000193917000257a148000000000000000db8001ca80029b8003070000000ed20c80000012d8002e0a919e5876b100000002ee0000001d930c252800288249a630002f922fa9a8ff827a2180022c0000d7000000000000000010000001aa00000001622e88000001091818002033078000001961368b6973abc9a38531252481ef8001e69b52592c316f00009aaa32720000000e82f81db1e3a8b04c18d1e70651a99aea9d0001e82a791eaad0ada160f6a4ca4302702c8510000e20000002840002928a89f9983250aba1bc00019c000258101ad692124414c13090d8000002400002620002eea3f94b8002f312615597d0a60000c30000002761809fd1aa115000025b0f02c0000002539618eea6d8000000000fc01b8691560000352650e50400002c887f8a180021a1731661ea8bd155171a82a340001511052598001b699100010605e0bf8cba138001059ae2e200016eae680200000027b01722d98999a00002b80000027e00480025119f9e09892380f702103593903d93527f2300592e8163832974a8a1d68970a99b8849ac080b0d02b52460319e32eca158d804383f8df8a78c29f31800cb00501a997a5f824a822428192c7a3b29a03012022606d19a9c49048c21502b801699b11c063807a3515492497a13880026791585692f80000007d1cf9f812f05397f80021d0001862898000000002570000001f6abe1e40000000001f40000002aa8001e224d30680028180000030d00009bafa8000002af2619df8ef04f24e883a6ba0609d2521349740d62680000000000a09128000d480027c2048942450a685522105d828a4a2691a4a0983c9631310c708712d2949982e412826380030e929888b028000001cc8001d82f88000001f52a90002000000000bf0440000000000ae0000002efa902c680000000000000008e800000000103232a100000000002281f890f0540b4a6f00ea4198c80025500008d3049e10001f380012891800022e2658772368000000000002b62d524480026418b8d3a438610000b0000047125a9b0000000f085095d8000000000001879c313314900000000007029f9eb1d41a40001bd9e28000000f4a9119180002980013000000024b00000012921797a85eab400014d8000000000000000002142ce8000000000d12d02d8a4680025e89780021a93403a0840000000000000000000000000002072d18000001a696795980030b0f909297692b9579b5a908001518002878002772c00000002d40609dc30b9fa1c884d9582279751c12308002b900023d86e9bc800251abd0d90000000000000000b086c9cf09604f9de8e091f85184a9792f6a232020000fa80000030098509b06c0000002108002dc20c2a68c52b6800062800071aec0002d58
  | 10 => 0x2709ab1d4b0db0c8001e00d1a490e28c10000c3a6294f80028c14980001a0a22700000312080000002d225c0000002a100016b98380000000000000016a2ea1b2aef0362832db872136073806a0087080011483400030e2fb0cd8003020001071dd83b21199480018a9438000002f28250951d9a992d60fb0fe29e9c800023ea3900fa0aaa280000000000012288e24a89e8000d5a562b5a059d00001e1ab00000689b18000e499da998002249f127301d07b8948378b92b71e78002f18589713129278001489611b31538f80b294328e8b583e25b24108b9ba9781d38e900013f15ea3c06981f0ab82a0002220001178000001e9acb96700000030a80000018f8338001a319017ea79ab8a2bae58292769448001ab8098002db00000000000003d00000100007a8000000000ec0de23200029c96800008daaf8000ad0000000002a39a88fe83aacf000000000ac40da8b319d0f286812227583e893a6994225680015c1bb2e1993100a242f480000e00a0001190f78002a9a2b2b180727388f852a778001320af00000000011f000011a8d9700000c9126800000223a5b8000ea0002de8001de0060ea9442aa14690f80014b0002e60810040e5aa5233a0d21c1f4918a3f0aa9c02c70000000001720000000410c421289321c8b509f1480000000000000000000001d100000015e10b0002c616c2c180019f1d52980001a81240e329680020d800000141a190002791a780004880018414a800284992a4c00000013b8002ff9be88c178af0aae9e608280015a1c68000ba1118001410000ba8000a48000bb09880000000000020380004300017b86200013b17c80000000018b00f00015aaa497c0002f580000001489e00000000026d14700004c9c1ac109ca5309230881d8000e6acc0381bf0002648003119359dcab21bd05a80019e95406d8f32ba9fc8001bb800000000123a859998001810e000007d8000000880898000000e894e0f2000065977000000248b090b98002c38000740000000a81aa80000017600017b00000005980000000000000000010880020e0e12a72b9821a611d8ade2090000000de8000002458d98778000001fd8162f70570000000002d900005823d00000005020f84090d0748002ed8002fe8f180000027e83f0462728f00ca91d0003059d58000138000000000000000000990e7ab10001888002da8648000c7ac800000000aa5f08587c81eadfa3e2bfa7f8000b800013c2b2800000055ae3a8900005c2130000000000000000002bba979ba0dc9ea1d31382268000000000c9b0f9908c029729d9698000000c588a1ef30980000004a0001600be00004901316d80000006e0522d0904172ae98000002940002eaa8b9c99df0ff1020d681b0001cc00003480016fa71a8d25a1f6306286a209b61110000001c515
  | 11 => 0x25d84213c9530000001d600000022c8000000a38188808cd2fb90002fa12042a358000000a580000000000000021e015adc8fdaa40760452421cb8001570001028000000958ed9b7003a271108002fe137201a4080000002d00000000027a048000090ae30001c900000004b0dd00000005a00002407309a05b94a00016a845aa822986b2bb30a20baeb1fe11a0000001c380000000002da4d8b700003c0091b40821d08002c4a88a088619848002eb8e395bad71dd0001a50f62b3010aca10e00000000012080012a25e00009f8e199b8801ffac2081accabf20127408a92e29e156ad1
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf648c9100069c648c910006cf628c91003ecc628c910004de760c91003cdc760c9100065f650c9101365c650c9100069f640c9100069c640c910006cf620c91003ecc620c9100074d520c910005d9700c910004de768c5100065f658c5101065c658c5100069f648c5100069c648c510006cf628c510006cc628c510004de760c5100065f650c5100fe5c650c5100069f640c5100069c640c510006cf620c510006cc620c5100347e76941100063f64941100063c64941100065f63941100d65c63941100066f62941100066c6294110004be76901100063f65901100b63c65901100069f63901100c69c6390110006af6290110006ac6290110004be76101100063f65101100ae3c65101100069f63101100a69c6310110006af6210110006ac6210110004de76cc1100065f65cc11009e5c65cc1100069f64cc1100069c64cc110006cf62cc110006cc62cc110005d671cc11000cdc764c1100065f654c11008e5c654c1100069f644c1100069c644c110005cc724c110006cf624c110006cc624c110005d4714c110006b864c4110056d46384110006e4628411000cde73d9010004dd73d90100047f75590100147c7559010004dd7698c1002cf47158c1000cdf7658c1003cdc7258c100065f5258c1002ed77158c10006d47158c1000cdf7058c1000cdd7058c100065c5058c1000cde73d8810004dd73d8810004df735881000cdc735881016e5e63548100065d635481003e6e62548100066d625481000578705481003cdf768c810004dd768c810005d6718c81003cdf760c810004dd760c8100074d520c810004df768c41000cdd768c41002dd6718c410005d9708c41000cdf760c410004dd760c410005d9700c41002ed6760c41002ed5760c410004d5760c4101a5d6720c4101af57520c41000755520c41002fd2700c410005d5700c41002fd1700c410056d6600c4101af54500c41002dd673c8410004f576084101a5d473084100076552084100d65e63940100065d6394010007543194010007d031d00100c69e63900100069d639001000794319001019dba70900100a69e63100100069d63100100079431100100073a5010010197385010010004f97610010007d03110010006ba7610010006b976100100079a73100100079973100100079a63100100079963100101973b52100100073952100100079a3210010007983210010007b27110010007b1711001018eba6110010187b331100100079a3110010007983110010187b03110010007903110010007b32110010007b02110010004dd76cc0100079840cc010004df764c010005cc724c010005d4714c01000798404c01002dd473c4010007b040c401003cf97684010007d03184010004f7764401002dd47344010005e47244010007725044010004fb7644010005b87444010
  | 1 => 0x310006b96410310005b97610310006b9761031018f3a65103100073965103100079a73103100079973103100079b631031000798631031018f3b52103100073952103100079a32103100079832103100079a311031000798311031009e5e65cc3100065d65cc3100069e64cc3100069d64cc310005d671cc3100079840cc31008e5e654c3100065d654c3100069e644c3100069d644c310005cc724c310005d4714c31000798404c3100147e75d92100047d75d921000cde73d9210004dd73d921003cee72d9210004ed72d9210004dd7698e1000cdf7658e1003cdc7258e100065f5258e10006d77158e10056d47158e100065c5058e1000cde73d8a10004dd73d8a10004df7358a1000cdc7358a1016e5e6354a100065d6354a1003e6e6254a100066d6254a1003cdf768ca10004dd768ca10005d6718ca1003cdf760ca10004dd760ca100074d520ca10005d9700ca10005d5760c610056d5760c6101b5d6720c6101bf57520c61000755520c610005d5700c6101bf54500c610055d673c86101b5d473086100076552086100d65e63942100065d63942100075431942100c69e63902100069d63902100079431902100a69e63102100069d6310210007943110210005cc724c210005d4714c210055d473c42100147e76d95100047d72d95100147e70d95100147c70d9510044be76d91100063f65d91100063c65d91100063f52d91100063c50d91100047f75591100147c7559110004df735911000cdc7359110004ef725911003cec7259110004fb7059110004be76191100063f65191100063c65191100063f52191100c4be7019110044bc70191100063c501911000cde76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d1003cde72d8d100065f52d8d1000cde71d8d1000cdc71d8d100065c50d8d100047f7558d100147c7558d10004bf7458d10044bc7458d10004ef7258d1003cec7258d10054f77158d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d100147c75d891000cde73d8910004dd73d89100066f52d891003cee76d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066f75d89100066c75d8910006ce73d8910006cd73d89100066c50d89100047f75589100147c7558910004bf7458910044bc7458910004df735891000cdc7358910004f77158910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc631891003e6e751891003e6d751891003ecf731891003ecc73189100066c50189100047e76549100047c76549100063f64549100063c64549100065f635491016e5c63549100066f625491003e6c6254910004de768c91003cdc768c9100065f658c9101465c658c9100069
  | 2 => 0x3c7d72594200066f325942003e5e325942003e5c325942003e6c325942003e4c325942003e6c215942005c7c705942003e6f205942003cec7258c2006ecf7258c2003cde7258c2003cdc7258c2003ecc7258c2003ccc7258c2003e5f5258c2003e5d5258c20004dc7158c200065c5058c20004df735842000cdc7358420004df768c420004dd768c4201065e658c4200065d658c42003dce728c42000cdf760c420004dd760c4200fe5e650c4200065d650c42003dcc720c4200066d658842006dce73884200647f76940200147d76940200d65e63940200065d63940200056d72940201df4c32940200b63e65900200063d65900200c69e63900200069d63900201d78c32900200ae3e65100200063d65100200a69e63100200069d63100201cf8c32100201c7385010020004dd76cc02009e5e65cc0200065d65cc02003dcc72cc020004df764c02008e5e654c0200065d654c02003dcc724c020005d4714c020004ef76480200066d654802006dcc7348020005e471480200147f76597100065f73597100065c73597100047f72597100147e75d93100047d75d9310004bd76993100063e65993100063d65993100469e73993100469d73993100063f52993100063c5099310004df735931000cdc7359310044bf76593100063e65593100063d65593100069f73593100069c73593100063f5259310006bb70593100063c50593100147e75d8f100047d75d8f10044be74d8f10004bd74d8f1003cee72d8f10004ed72d8f100065e65d8f100065d65d8f100069e64d8f100069d64d8f10005ce72d8f100065e75d8f100065d75d8f100069e74d8f100069d74d8f1003cde72d8f10006ce72d8f1003cce72d8f10006cd72d8f100065f52d8f10006d671d8f10006d970d8f100065c50d8f100065e6518f100065d6518f100069e6418f100069d6418f100147e75d8b100047d75d8b10044be74d8b10004bd74d8b1000cde73d8b10004dd73d8b100147e7558b10004df7358b1000cdc7358b100047f7654b100047d7654b100063e6454b100063d6454b100065f6354b1016e5c6354b100066f6254b1003e6c6254b10005787054b10004de768cb1003cdc768cb101465e658cb100065d658cb100069e648cb100069d648cb10004de760cb1003cdc760cb101365e650cb100065d650cb100069e640cb100069d640cb1003ece620cb10006cd620cb100074d520cb101065e658c7100065d658c7100069e648c7100069d648c710005d9708c7100fe5e650c7100065d650c7100069e640c7100069d640c710005d9700c71004c7d76943100063e64943100063d64943100065f63943100d65c63943100b63e65903100063d65903100069f63903100c69c63903100ae3e65103100063d65103100069f63103100a69c63103100073a501031018f38501
  | 3 => 0xe32d95201de5c32d9520044be76d91200063f65d91200063c65d91200063f52d91201d69e32d91201d69c32d91200063c50d91200047f75591200147c7559120004df735912000cdc7359120004f77159120004f47159120004be76191200063f65191200063c65191200063f52191201ce9e32191201ce9c32191200063c501912000cde76d8d200065f65d8d200065c65d8d200069f64d8d200069c64d8d2003cde72d8d2003cdc72d8d200065f52d8d20004de71d8d200065c50d8d200047f7558d200147c7558d20004bf7458d20044bc7458d2007cef7258d20004f77158d20004f47158d20004de7618d200065f6518d200065c6518d200069f6418d200069c6418d200147c76549200063f64549200063c64549200065f635492016e5c635492003f4e325492003f4c32549200057870549200166f76549200756c76549200166c76549200146c76549200072f64549200072c64549200074f73549200074c73549200074f635492016e6e635492016e6c63549200074c635492016e4c63549200076b70549200056c705492000768705492003e6f605492003f6b605492000cde73d8520004dd73d85200067765d85200067465d8520006b764d8520006b464d8520006d763d8520006d463d85200076552d8520006d673d8520006d573d85200067752d85200067552d85201b6d632d85201b6d432d85200067450d85200066d5218520006776518520006746518520006b76418520006b46418520006d76318520006d46318520007655218520006d77318520006d47318520006775218520006e65218520006755218520006e552185200066552185201a6d632185201a6d43218520006745018520004de768c520004dc768c5200065f658c5201065c658c5200069f648c5200069c648c5200074d528c520006d7618c520006d4618c520004de760c52000cdc760c5200065f650c5200fe5c650c5200069f640c5200069c640c5200074d520c520006d7610c520006d4610c520005d9700c5200847e76941200063f64941200063c64941200065f63941200d65c6394120006776194120006746194120004be76901200063f65901200b63c65901200069f63901200c69c63901200072d5290120006b76190120006b46190120004be76101200063f65101200ae3c65101200069f63101200a69c63101200072d5210120006b76110120006b4611012003cde76cc12003cdc76cc1200065f65cc12009e5c65cc1200069f64cc1200069c64cc12003dce72cc1200074d52cc120006d761cc120006d461cc12003cdc764c1200065f654c12008e5c654c1200069f644c1200069c644c12003dcc724c1200074d524c120005d4714c120006d7614c120006d4614c12000798404c1200056f758812007ecc6388120006e4618812003c7f7259420
  | 4 => 0x93200469d739932003e3f529932003e3d529932003e9e329932003e9c32993200063c5099320004df735932000cdc73593200069f73593200069c735932003e3f525932003e3d525932003e9e325932003e9c32593200063c505932003d6f7654b2005e6f7654b2003f2e6454b2003f2d6454b200074f7354b200074c7354b2003f4f6354b2016e6e6354b2003e6c6354b2003f4c6354b2003e4c6354b200056c7054b2000cde7398720004dd73987200066d5298720004df735872000cdc735872003cde768c7201065e658c7200065d658c7200069e648c7200069d648c7200074d528c72003cde760c7200fe5e650c7200065d650c7200069e640c7200069d640c7200074d520c720006d6610c720006d5610c7200747d76943200063e64943200063d64943201de5f63943201de5c63943200b63e65903200063d65903201d69f63903201d69c63903200072d52903200ae3e65103200063d65103201ce9f63103201ce9c63103200072d52103201ef38501032009e5e65cc3200065d65cc3200069e64cc3200069d64cc32003dce72cc3200074d52cc32008e5e654c3200065d654c3200069e644c3200069d644c32003dcc724c3200074d524c320005d4714c3200065e73d96200065d73d96200066d72d96200066f32d96201de5e32d96201de5c32d96200066c32d96200067a70d962000cde73d9220004dd73d92200047f75592200147c7559220004dd7698e200065f6598e200065c6598e200047f7558e200147c7558e2000cdf7658e200065f6558e200065c6558e2003dcc7258e200065f7558e200065c7558e20006cf7258e2007ecc7258e200065f5258e20004dc7158e200065c5058e2016e5e6354a200065d6354a200766d6254a2003f4c3254a20005787054a20005cd760ca2003ecd760ca2003f4e750ca2003f4d750ca201e6cf650ca200074f650ca200064f650ca201e6cd650ca201e74c650ca20005ce710ca20005cd700ca2003ece600ca2003fca600ca201e74c500ca200147e75986200047d7598620044be7498620004bd74986200047f75586200147c7558620004df735862000cdc7358620004df768c620004dd768c6200065f658c6201065c658c62003dce728c62000cdf760c620004dd760c6200065f650c6200fe5c650c620005d9700c6200066f658862007dce73886200066f650862003dcc73086200147e76942200d65e63942200065d63942200056d72942200074c32942200063f65902200b63c65902200c69e63902200069d63902200078c32902200063f65102200ae3c65102200a69e63102200069d63102200078c32102200065f65cc22009e5c65cc2200065f654c22008e5c654c22003dcc724c220005d4714c22000798404c2200066f65c822003dcc73c82200147e76d95200747d72d95201de5
  | 5 => 0x6d56218530006d46218530007c46218530006c4621853000757521853000755521853002ed7601853002fd36018530007545018530006d77518530006d67518530006d57518530006d47518530006d77418530006d67418530006d57418530006d47418530006d75418530006d65418530006d55418530006d45418530006d77218530006d67218530006d57218530006d47218530006d75218530006575218530006d65218530006d55218530006555218530006d45218530006d74218530006d64218530006d54218530006d4421853002ed77018530006d57018530006d75018530006d65018530006d55018530006d45018530006545018530004de76d0530004dd76d0530006cc62d0530006d461d0530006cc6290530006d46190530004df7650530004dc76505300055f755053008d5c7550530005cf7250530005cc7250530006cc6250530006d46150530005db7050530005d8705053008d5e75105300055d7510530006cc6210530006d46110530004de76c8530004dd76c853008d5e75c85300055d75c853003ecc62c8530006d461c8530004de7688530004dd768853003ecc62885300074d5288530006d46188530004df7648530004dc764853003ecc6248530006d4614853003cdc760853008d5e75085300055d75085300059e74085300059d740853003ecc62085300074d5208530006d46108530005da7008530005d970085300055e769413009e5e769413009c5e76941300071f64941300071c64941300055d72941300074f62941301de5c62941300074c62941300064c62941300075761941300065c619413000754619413000654619413008d5e709413008f5a70941300d65f60941300d75b609413008d5e75d01300055d75d0130006cc62d0130006d461d01302175850d0130004de7690130006cc6290130006d461901300059e76901300069e76901300049e76901300071f65901302071c65901300078f62901301d69c62901300078c62901300068c62901302071f52901300071d52901300079761901300069c619013000794619013000694619013020d9e70901300c69f60901300c79b60901300071e50901302071c50901300055f755013008d5c7550130006cc6250130006d46150130004de7610130006cc6210130006d461101301f75850101300079940101300059e76101300069e76101300049e76101300071f65101301f71c65101300078f62101301ce9c62101300078c62101300068c62101301f71f52101300071d52101300079761101300069c61101300079461101300069461101301fd9e70101300079a70101300a69f60101300a79b60101301f79b50101300071e50101301f71c50101301f79850101301f71850101300065f73597200065c735972003e5e325972003e5c32597200469e739
  | 6 => 0xf74589300059c7458930005d77158930005d47158930005db705893008d5e75189300055d75189300065f65189300065c65189300069f64189300069c641893003ece6218930006cd62189300074f5218930005ce7618930006ce76189300074e75189300074d7518930006cf65189300074f65189300064f6518930006ce6518930006cd6518930006cc65189300074c65189300064c6518930006cf64189300078f64189300068f6418930006ce6418930006cd6418930006cc64189300078c64189300068c641893006ecf601893006fcb60189300074c501893003ecf751893003ece751893003e4e751893003ecd751893003e4d751893003ecc751893003ecf741893003ece741893003ecd741893003ecc7418930006cf5418930006ce5418930006cd5418930006cc541893003ecf711893003ece711893003ecd711893003ecc7118930006cf5118930006ce5118930006cd5118930006cc511893003ecf701893003ecd7018930006cf5018930006ce5018930006cd5018930006cc50189300064c50189300065f76549300055e76549300055c76549300065c76549300045c76549300071f64549300071c645493008d5f725493008f4f72549300074f625493003e5e625493003e5c62549300074c625493003e4c62549300055c705493016e5f605493016f5b6054930004de76d0930004dd76d093003ecc62d093008d5e75909300055d759093003ecc6290930005da7090930005d97090930004df7650930004dc765093003ecc625093008d5e75109300055d751093003ecc6210930006cc62d85300075765d85300075465d85300079764d85300079464d8530007c762d8530006d662d8530006d462d8530007c462d8530006c462d85300075752d85300075552d8530056d760d8530057d360d85300075450d853008d5e75985300055d75985300065f65985300065c65985300059e74985300059d74985300069f64985300069c6498530005ce7298530005cd7298530006cf6298530006cc6298530005d67198530005d970985300055f755853008d5c75585300059f74585300059c7458530005cf7258530005cc7258530006cc6258530005db70585300065f65185300065c65185300069f64185300069c6418530006cf6218530006cc6218530006d5611853003cde72185300065f52185300065d5218530006d75118530006d65118530006d55118530006d451185300065c5018530005d67618530006d67618530006d76518530007576518530006576518530006d66518530006d56518530006d46518530007546518530006546518530006d76418530007976418530006976418530006d66418530006d56418530006d46418530007946418530006946418530006d76218530007c76218530006c76218530006d66218530
  | 7 => 0x893007ece73d893007ecc31d89300066c50d89300066f65189300066c6518930006af6418930006ac641893003e6e751893003e6d751893003ecf731893003ece731893003ecc7318930006cf531893006ece5318930006cd531893006ecc5318930006cf431893006ece4318930006cd431893006ecc431893006ecf311893006ecc31189300066c501893006ecc30189300047e76549300047c76549300063f64549300063c64549300066f625493003e6c625493016f4f325493016f4c325493008d5e758c9300055d758c9300065f658c9301465c658c9300069f648c9300069c648c93003ecc628c93003cdc764c93003ecc624c9300067765d85300067465d8530006b764d8530006b464d8530006e762d8530006e462d8530056d673d85300067752d85300067552d8530006d632d8530056d432d85300067450d8530006776518530006746518530006b76418530006b46418530006e76218530006e46218530006d7731853002ed67318530006d7531853002ed65318530006d5531853002ed45318530006d7431853002ed64318530006d5431853002ed4431853000677521853000675521853002ed73218530006d63218530006d5321853002ed4321853000674501853002ed430185300065f658c5301065c658c5300069f648c5300069c648c530006cf628c530006cc628c530006d4618c530006cc624c530006d4614c53021c7e76941300063f64941300063c64941300066f62941300066c62941300067761941300067461941300a4be76901300063f65901300b63c6590130006af6290130006ac6290130006b76190130006b461901300c4be76101300063f65101300ae3c6510130006af6210130006ac6210130006b76110130006b461101301f7385010130006cc628c130006d4618c13008d5e76d953008e5e76d95300055d72d953008d5c70d95300d65f60d95300d75b60d95300071f65d91300071c65d91300071f52d91300c69f60d91300c79b60d91300071c50d913008d5e75991300055d75991300059e7499130005ce7299130005cd7299130005d67199130005d57199130005d970991300055f755913008d5c7559130005cf7259130005cc7259130005d77159130005d47159130005db70591300059e76191300069e76191300071f65191300071c65191300071f52191300a69f60191300a79b60191300071c501913008d5c75d89300074f52d89300074f75d89300074c75d89300074f65d89300074c65d89300078f64d89300078c64d893007ecf60d893007fcb60d89300074c50d893008d5e75989300055d75989300065f65989300065c65989300059e74989300059d74989300069f64989300069c6498930005ce7298930005d67198930005d57198930005d970989300055f755893008d5c75589300059
  | 8 => 0xa59e73980400059d73980400c69e63980400069d63980402473850980400079a73980400079973980400479a63980400479963980402473b52980400073952980400079a3298040007983298040005ba71980400079a31980400079831980400071e73940400071d73940400071e63940400071d63940400053d72940400071e32940400071c32940400071e31940400071c31940400ad3e70940400af3a70940400b63e60940400073a609404016d5f7654b300065f7654b300045f7654b3016d5d7654b3016e5c7654b3016f1e6454b3016f1d6454b3023d5f7254b3009f4f7254b3016f4f6254b3003e5e6254b3003e5c6254b3016f4c6254b300055c7054b3000cde76d0b30004dd76d0b3009d5e7590b300055d7590b30004df7650b3000cdc7650b3009d5e7510b300055d7510b3003cde72987300065f52987300065d529873000ed671987300065c509873000cde76d0730004dd76d0730004df765073000cdc76507300055f755073009d5c7550730005cf7250730005cc7250730005db7050730005d8705073009d5e75107300055d751073000cde76c8730004dd76c873009d5e75c87300055d75c8730006d661c873000cde7688730004dd768873003ece62887300074d5288730004df764873000cdc764873003cdf760873009d5e75087300055d75087300059e74087300059d740873003ece62087300074d5208730006d661087300d55d769433008e5d769433008c5d76943300d71e64943300d71d64943300055d72943301de5e62943300065e619433021d5e709433009f5a709433009d5e75d03300055d75d03300c59d76903300069d76903300c71e65903300c71d65903301d69e62903302371f52903300071d52903300069e61903300071e50903302371c50903300055f755033009d5c75503300a59d76103300069d76103300a71e65103300a71d65103301ce9e621033022f1f52103300071d52103300069e61103300079a70103300071e501033022f1c501033008e5d6354a3003e6e6254a300066d6254a3016f4c3254a3003ece628ca30006d6618c6300d75b30942302273850102300147e76d95300d65e73d953008e5d73d95300047d72d95300d65c32d95300d65c31d953008e5d30d9530044be76d91300063f65d91300063c65d91300c69e73d91300069d73d91300063f52d91300c69c32d91300c69c31d91300063c50d91300047f75591300147c7559130004ef725913003cec7259130004f77159130004f471591300c4be76191300063f65191300063c65191300469e73191300469d73191300063f52191300a69c32191300a69c31191300063c5019130004de76d0d30044dc7650d300147c75d89300066f52d89300066f65d89300066c65d8930006af64d8930006ac64d89300066f75d89300066c75d
  | 9 => 0xf620c94003ecc620c9400074d520c94000cde73d8540004dd73d85400065f658c5401065c658c5400065f650c5400fe5c650c540006d7610c540006d4610c5400cc7e76941400063f65901400b63c65901400a69f7458c4003cdc7258c400065f5258c40004dc7158c400065c5058c4000e9e6350c40004df735884000cdc7358840046ac425884016e5e63548400065d635484003e6e62548400066d62548400057870548400ad3e75908400053d75908400059f73508400a59c735084003cdf768c840004dd768c84003cdf760c840004dd760c8400074d520c840005d9700c8400047f75584400147c7558440004df735844000cdc7358440004ef725844003cec7258440046b441584400053f75504400ad3c75504400059f73504400a59c7350440005af7250440005ac7250440005bb7050440004df768c440004dd768c44000cdf760c440004dd760c4400d65e63940400065d6394040004bf76500400053f75500400ad3c75500400459d7698c401cd9e7298c400071f5298c400059e7198c400071c5098c400459f7658c400a69f7658c401cd9c7258c400071f5258c400059c7158c400071c5058c400ad3e75988400053d75988400059f73588400a59c7358840046ac62588400071f73548400071c73548400071e63548400071d63548400ad3f72548400af2f72548400072e62548400072d625484027f2f325484027f2c32548400073b70548400053c70548400073870548400053870548400b63e60548400ad3e758c8400053d758c8401cd9f768c8400059d768c8401cf1e758c8401cf1d758c8401cd9e728c8401cf1f528c8401cf1d528c8400059e718c8400059d708c8401d69e608c8402771c508c8401cd9f760c8400059d760c8401cf1e750c8401cf1d750c8401cd9e720c8401cf8e720c8401cf1f520c8401cf8e520c8401cf1d520c84026f8d520c8400070d520c8400059e710c8401cf9a700c8400059d700c8401cf99700c84000599700c8401d69e600c84026f1c500c8400053f75584400ad3c75584400059f73584400a59c7358440005af7258440005ac7258440046b461584400059f768c4400059d768c4401cd9e728c44025f1f528c4400071d528c4400a59e718c4400059d708c4402669e608c44025f1c508c440005bb704c440005b8704c4400a59f760c4400059d760c4401cd9e720c44024f1f520c4400071d520c4402559e710c4400a796710c4400059d700c4400c69e600c44024f1c500c4400ad3e75c84400053d75c84400a59e73c84400059d73c8440005ba70c8440005b970c84400a59e73884400059d73884400072d52884400059f73484400a59c7348440005bb7048440005b87048440044be7608440004bd76084400ad3e75084400053d75084401cd9f73084401cd9c73084400072d5208440
  | 10 => 0x4a400066d6254a400c59e73d0a400059d73d0a400b53e7590a400053d7590a4003cbf7650a400059f7350a400c59c7350a4003eae6250a400b53e7510a400053d7510a4003cdf768ca40004dd768ca4003cdf760ca40004dd760ca400074d520ca400147e75986400047d7598640004df735864000cdc73586400c59e73d06400059d73d06400053f75506400b53c75506400059f73506400c59c7350640005af7250640005ac7250640006b661506400b53e75106400053d7510640004df768c640004dd768c64000cdf760c640004dd760c6400d65e63942400065d63942400b53e75d02400053d75d02400073a50d0240005ba70d8e400059d7698e401d59e7298e400071f5298e400059e7198e400071c5098e400c59f7658e400c69f7658e401d59c7258e400071f5258e400059c7158e400071c5058e400c59e73d8a400059d73d8a40005ba70d8a400b53e7598a400053d7598a40006af6298a400059f7358a400c59c7358a400b53e7518a400053d7518a400c59e7318a400059d7318a40005ba7018a400071f7354a400071c7354a400071e6354a400071d6354a400b53f7254a400b72f7254a400072e6254a400072d6254a4029f2f3254a4029f2c3254a400053c7054a400ae3e6054a400b53e758ca400053d758ca401d59f768ca400059d768ca401d71e758ca401d71d758ca401d71f528ca401d71d528ca400059e718ca400059d708ca402971c508ca401d59f760ca400059d760ca401d71e750ca401d71d750ca401d78e720ca401d71f520ca401d78e520ca401d71d520ca4028f8d520ca400070d520ca400059e710ca400059d700ca4028f1c500ca400b53e75d86400053d75d86400c59e73d86400059d73d8640005ae72d8640005ad72d8640005ba70d86400b53e75986400053d7598640006b761986400059f73586400c59c73586400c59e73186400059d7318640005ba70186400059f768c6400059d768c6401d59e728c6402671f528c6400071d528c6400059d708c6402671c508c6400c59f760c6400059d760c6401d59e720c6402871f520c6400071d520c6400c796710c6400059d700c6402871c500c6400b53e75c86400053d75c86400c59e73c86400059d73c86400c59e73886400059d73886400072d52886400059f73486400c59c7348640004be7608640004bd76086400b53e75086400053d75086401d59f73086401d59c73086400072d52086400071e73942400071d73942400071e63942400071d63942400053d72942400071e32942400071c32942400071e31942400071c31942400b53e70942400b73a70942400ae3e60942400147e76d95400047d72d95400147c75d894000cde73d8940004dd73d89400047e76549400047c76549400065f658c9401465c658c9400065f650c9401365c650c940006c
  | 11 => 0x44bc7458021004df735802100cdc73580210066d52580210d55e73d92500055d73d92500ad7a70d92500063d64192500d55e73192500055d73192500b57a70192502ad7a70d8e5008d5d7698e501dd5e7298e500055e7198e5021e5e6098e5009f5a6098e500056f7258e500056c7258e500d55f7658e500d65f7658e500074f7258e501dd5c7258e500074c7258e500054c7258e500055c7158e5008e5e6058e5008f5a6058e500d55e73d8a500055d73d8a500065e63d8a500065d63d8a5005d7a70d8a500066f6298a500055f7358a500d55c7358a500065e6358a500065d6358a500065f7358a500065c7358a500d55e7318a500055d7318a500657a7018a500d55e73d0a500055d73d0a500047e7690a500047d7690a500055f7350a500d55c7350a500047e7610a500047d7610a500047e768ca500047d768ca501dd5f768ca501de5e768ca500055d768ca501de5d768ca500045d768ca501dd5e728ca501de5d628ca500055e718ca500055d708ca502a65e608ca501475a608ca501dd5f760ca501de5e760ca500055d760ca501de5d760ca500045d760ca501dd5e720ca501df4e720ca500074f620ca501de5d620ca501df4c620ca500055e710ca500055d700ca502a65e600ca501375a600ca500d55e73d86500055d73d865001d7a70d86500053e74986500053d74986500055f73586500d55c73586500056f72586500056c72586500d55e73186500055d73186500257a70186500d55e73d06500055d73d06500047f76506500047c76506500055f73506500d55c73506500056f72506500056c72506500057b70506500057870506500047e76106500047d76106500055f768c6500055d768c6501dd5e728c6500065d628c6500d55e718c6500055d708c6501065e608c6501075a608c6500d55f760c6500055d760c6501dd5e720c6500065d620c6501055e710c6500d756710c6500055d700c65021e5e600c6500ff5a600c6500047e76c86500047d76c86500d55e73c86500055d73c86500d55e73886500055d73886500055f73486500d55c73486500047e76086500047d76086500053e74086500053d74086501dd5f73086501dd5c73086500047f72597400463c40597400147e7558b40004df7358b4000cdc7358b400047f7654b400047d7654b40005787054b401465e658cb400065d658cb401365e650cb400065d650cb4003ece620cb40006cd620cb400074d520cb40005d9700cb40004df735874000cdc73587401065e658c7400065d658c7400fe5e650c7400065d650c740006d6610c740006d5610c7400bc7d769434000cdf7658e400c69c7458e4003cdc7258e400065f5258e40004dc7158e400065c5058e4000e9e63d0e4000cbf7650e40004df7358a4000cdc7358a4016e5e6354a400065d6354a4003e6e625
  | 12 => 0xd76d0431004df76504310055f75504310fd5c7550431005cf7250431005cc7250431005db7050431005d870504310fd5e75104310055d75104310079541104310065f75580310065c75580310069f74580310069c7458031006cf725803103cdc7258031006cc725803103ccc72580310065f52580310065d525803100edb70580310065c505803103e5e325972103e5c325972103e6c21597210047c705972103cdc7258f2103e5f5258f2103e5d5258f21004df7058f210065c5058f211065e658c7210065d658c7210fe5e650c7210065d650c7210147c759832100cde7398321004dd73983210047f75583210147c7558321004bf7458321044bc745832100cde73d9221004dd73d92210047f75592210147c7559221004dd7698e2100cdf7658e210065f5258e21004df7058e210065c5058e2116e5e6354a210065d6354a2103f4e3254a2103f4c3254a210166f7654a210166c7654a210074f7354a210074c7354a2116e6e6354a210074e6354a2116e4e6354a210074d6354a2116e6c6354a21007677154a21007647154a2103e6e6154a210056c7054a210056d7510a2103cdd768c62103dce728c6210074d528c62103cdd760c62103dce720c6210074d520c6210056d75c862100cde7398221004dd73982210047f75582210147c7558221004bf7458221044bc74582210066d52582210047f75591210147c7559121004df735912100cdc7359121004ef7259121004fb7059121004f8705912100cde76d8d210065f52d8d21004dd70d8d210065c50d8d21004de7618d210065f635492116e5c635492103f4c3254921004de768c521004de760c5210147e75d81210047d75d8121044be74d8121004bd74d81210067850d812100cde7318121004dd73181210067850181210065f73594210065c735942103e5e325942103e5c32594210047c70594210469e73990210469d739902103e3f529902103e3d529902103e9e329902103e9c3299021004be70990210063c5099021004df735902100cdc735902103cec72590210069f73590210069c735902103eac725902103e3f525902103e3d525902103e9e325902103e9c3259021004bc70590210063c505902103d6f76548210f66f765482103f2e645482103f2d64548210074f73548210074c735482103f4f635482116e6e635482103e6c635482103f4c635482103e4c63548210e66e615482103f6661548210056c7054821006ad64d08211065e658c4210065d658c4210069e648c4210069d648c42103dce728c4210074d528c42103cde760c42103cdc760c4210fe5e650c4210065d650c4210069e640c4210069d640c42103dce720c4210074d520c421004ef7648421007c631484210147c759802100cde7398021004dd73980210047f75580210147c7558021004bf7458021
  | 13 => 0x8141006e862d81410067a75d81410067975d8141006db73d8141006d873d81410067b52d81410067952d8141006da32d8141006d832d81410147c751814100cde7318141004dd73181410067850181410067b6518141006786518141006db6318141006d86318141006eb6218141006e862181410067b7518141006787518141006bb7418141006ba5418141006b95418141006da7318141006d973181410067b5218141006795218141006bb4218141006b94218141006da3218141006d83218141006ba41181410047f72594410463f41594410047c70594410463c40594410147e7558841004df735884100cdc73588410047f76548410047d76548411465e658c8410065d658c8411365e650c8410065d650c84103ece620c841006cd620c8410074d520c841004bf76504410063d6550441005b870504410147c759804100cde7398041004dd7398041046b840980410047f75580410147c7558041044df7650e3103e6e6254a310066d6254a3116f4f3254a3116f4c3254a311055e758ca310055d758ca3103ece628ca3103cdf764ca310047f75582310147c7558231004bf7458231044bc7458231005d671d92311055e75192310055d7519231005ce7219231005cd7219231005d67119231005d671d8a311055e7598a310055d7598a311055e7518a310055d7518a310059e7418a310059d7418a3103ece6218a31005d67118a310065f7654a310065c7654a311055f7254a311074f7254a3103e5e6254a310074e6254a3103e4e6254a310074d6254a3103e5c6254a3116e5e6154a310055c7054a31004de76d0a31004dd76d0a311055e7590a310055d7590a3103ece6290a31004df7650a31004dc7650a3103ece6250a311055e7510a310055d7510a310055f75506311055c7550631005cf7250631005cc7250631005db7050631005d870506311055e75106310055d75106311055e75d82310055d75d82310059e74d82310059d74d8231005ce72d8231005cd72d8231056d661982310055f75582311055c75582310059f74582310059c74582310065f75582310065c75582310069f74582310069c745823103cdc72582310065f52582310065d52582310065c50582310047f75591310147c7559131004df7359131004ef725913103cec7259131004fb7059131004f870591310066f625493103e6c625493116f4c325493103ecc628c9310147e75d81310047d75d8131044be74d8131004bd74d81310065f765483116e5c765483123d5f72548310ff4f725483116f4f625483103e5e625483103e5c625483116f4c62548311065e615483116f5661548310055c705483100cde76d0831004dd76d08310fd5e75908310055d7590831004df765083100cdc76508310fd5e75108310055d7510831005d67110831005d57110831004d
  | 14 => 0x69f74582320069c745823203cdc725823203e5f525823203e5d5258232004dc715823203edb70582320065c505823203edb205823203ed82058232004df735913203e5f635493216e6f625493203f4c32549320147e75d81320047d75d8132044be74d8132004bd74d813203f4f765483203d4f76548321464f76548320074f74548320074e74548320074d74548320074c745483203f4f645483203f4e645483203f4d645483203f4c64548320074f71548320074e71548320074d71548320074c715483203f4f615483203f4e615483203f4d615483203f4c61548320074f70548320074e70548320074d70548320074c70548320054c705483203f4f605483203f4e605483203f4d605483203f4c605483203e5f529843203ece529843203e5d5298432006cd52984320064d529843203ed6719843203ed7219843203ed42198432004dd70984320065c509843203ecc20984320065f75580320065c75580320069f74580320069c745803203e5f525803203ece525803203e5d5258032006cd52580320064d5258032006d77158032004dc7158032006d47158032004d4715803203edb70580320065c505803203edb205803203ecc205803203ed8205803203cdc7258f410065f5258f41004df7058f410065c5058f410469c4058f41004df7358b4100cdc7358b4116e5e6354b410065d6354b4103e6e6254b410066d6254b4103cdf768cb41004dd768cb4103cdf760cb41004dd760cb410074d520cb4100cde7398341004dd7398341046b840983410047f75583410147c7558341046b84058341004df7358a4100cdc7358a41005d6718ca410074d520ca4100cde7398241004dd73982410047f75582410147c75582410147e76d95410047d72d95410047e70d954100cde76d8d410065f65d8d410065c65d8d4103cde72d8d410065f52d8d41004dd70d8d410065c50d8d410065f6518d410065c6518d410147c75d894100cde73d8941004dd73d89410066f52d89410066f65d89410066c65d8941006cf63d8941006cc63d89410066f75d89410066c75d8941006ce73d8941006cd73d89410066c50d89410066f65189410066c6518941006cf6318941006cc631894103e6e751894103e6d751894103ecf731894103ecc73189410066c50189410047e76549410047c76549410065f635494116e5c63549410066f625494103e6c625494103eac62d094103cbc765094103eac6250941005b47150941004de768c94103cdc768c9410065f658c9411465c658c941006cf628c94103ecc628c941005d6718c941004de760c94103cdc760c9410065f650c9411365c650c941006cf620c94103ecc620c9410074d520c9410147e75d81410047d75d81410067850d81410067b65d81410067865d8141006db63d8141006d863d8141006eb62d
  | 15 => 0xe73991520055d73991521556d72991520055f735915216d5c73591521656f72591520057771591520057471591520057b70591520057870591520063d641915203d6e72d8d520156d72d8d5216f4f32d8d5216d5e76d8d5216f4e72d8d521474d72d8d521465f62d8d521474f62d8d520055e71d8d520055d70d8d522b56f7258d5216f4c3258d521455e7618d5216e5e7618d5216f4f7218d5203d5c7218d5216f4c7218d5203d4c7218d5223e5f6218d521374f6218d520055e7118d520055d7018d5203d6e72d0d520056d72d0d5216f4c32d0d520056f7250d5203d6c7250d5216f4c3250d5216d5e73d85520055d73d855216d5e73985520055d73985520ed6d72985520053f74585520053c74585520055f735855216d5c73585520e56f72585520057b70585520057870585520053e74185520053d74185520067561185520053e74d81520053d74d815216d5e73981520055d73981520065f63981520065c63981520756d72981520053f74581520053c74581520055f735815216d5c73581520656f725815200577715815200574715815216d5e73181520055d73181520065f63181520065c63181520065e73181520065d731815205e6d72181520066f32181522a65e32181522a65c32181520066c32181520065f5258f42004dc7158f42004df7058f420065c5058f420469c4058f4216e5e6354b420065d6354b4203f2e4254b4203f4c3254b4203cbe74987420047f75587420147c7558742004df735874200cdc735874200cde7398342004dd7398342046b840983420047f75583420147c755834203cbc745834203e5e325964203e5c32596420047c7059642004df735864200cdc73586420147c759824200cde7398242004dd73982420047f75582420147c755824200cde76d8d420065f52d8d42004de71d8d42004dd70d8d420065c50d8d420065f635494216e5c635494203f2c425494203f4c325494200cde73d8542004dd73d85420147e75185420047d75185420147e75d81420047d75d81420067850d814200cde7318142004dd731814200678501814203e5e325944203e5c325944203e6c21594420047c70594420463c4059442004df735844200cdc735844203ee421584420147c759804200cde7398042004dd7398042046b840980420047f75580420147c75580421465f735963216e5c735963216e6f325963203e5e325963203e5c325963203e6c325963203e4c325963216e5c31596320047c705963216e5f305963203dce72d0e32044df7650e3203dcc7250e320147c759823203ecc32982320047f75582320147c7558232004bf7458232044bc745823203cde729863203e5f529863203e5d529863203ed6719863203ed7219863203ed42198632004dd70986320065c50986320065f75582320065c7558232
  | 16 => 0xe00300001600600200300203601200000f00501800500100e00c00203101200700000100000400000000d01e01600000000400000500f00200000600800000a00700500100200500400e00b01401000100c01301000202c00400d00400d00a00000501700102700400100600100901900702201100400200700100100200000100300000100800400000d00300300000000000000000402500900000600a00400f00700000300000300400600002800000700100000000600000301000200002600100000002e00301200100700100300001c00001200d00000100e00701101a01800200200900403800000300f00a00400900d00200100500503b00100200100000000100700700400000100a00300f00100000100400400100500100200200100000900100200b00000100300000500200d00801300000000000100300000601800602101500400200500001501500000200002600700200500f00200200d00300000000000400301700000100100100e00201b00102600200400700100200000b00901200100300500000d00000c00100000400a02301700900000700100900100000700500500400b00900200200000100000000300000100200200100000000000400b00100200600300600700800400302800000000b00200100800001a00f00200100600000000400100200100300100b00000000000200000000100000000000500100002301801000000000000900200001501701b00100000a00000000400000000600500700001100002300100300900000903400501900400700b00000000900400a00102401100c00100104200600300a00400300100400100000101101801300300501200000400500000500000a00700c00f01001a00a00000000000d00a00000200900100301900600601601100300100100400400000000100000200100400800000800001903400a01101b00101900300600a00100300000100102b00200000100800200b00302500001f00100b00b00100100100000500000501500100100000500000000201500002000100700400f00b00500000000001000001100000100000400200000002100200000200600000100800100200101b03a00700600100700101400100300000000500f00302101401900c00100000701400900100700000600700600500500400500100902800200000000002700201500400000400100000a00a00101000000100000c00c02700300100000000000200600700601a00100b00000200000000400100000000601000b00200300000200a00200500600001100400f01000000300000e00200600100001200c004011003006027000000000007012000009007001037046b840983430047f75583430147c755834300cbc74583430147e75d81430047d75d81430063f649915216d5
  | 17 => 0x12ed1964e5842824f23d000000037d28586a0a3f00000480744f10ab29dc00015d2de1c40f864e6000199800088b4b58cf942400019180011660003e7a800a8e86c0f99094a2a6a93828b7461850715e2a344000003de009116400000007a80008ac30b89b0dd6000000214400049b234879926aa540de0628d368da0559cecd28760224a7e00089741b18004e784be1dd04306c05fd3ac10fc4dc9cc0cb0b801d4179280157c69623b0d2185523a4d13201b3c6ee01e205156ca42480269989483a3d81a41c0c84650c0d70000000374328813800090f00000fc0e600009d00006ac1314250000c5a29e4a90478cb4000515800032e0002bf1f94000a9423f088c0002be34394e80b40002f123f000000049f172153c00000000000004700000000000000000299843e0000ba8f0c9760002d580000ca04d000082cd040000d3800103c000349100400000016d96bd44e59c2ea0a2c22c464115285464e3e40000000000a4e51d04e0cf08dc5160000000000479800000000007d0000e3a9d631c8000bb80e40000000e8e1d3417236091c4002b68de836a20113c8000c666db264a2b94d495f45d201859a03d1d083593c01d9101867000094d0a829147a00d849faa2815200010f000000017c0001ae0000a902c6000105e08000000014aa48d4ef81b000058d4428faceaa8280000c48fee5633bb92404a23f251718585a800013e27a80000aa47d000128c3091b0800cc840000a79e311388df4e58ab00389fd2c38e6d26e10b35ca314b980000001710480a5640b121118c8f641300009b600026c891828c78903884489540004418724000000263874400007c29526b84ba98c13f01d10be4ec473172400043c0ba0e602867c1000264826400100700500203800d01900000900400700100f00901f02400000300300400000c00603100300300700000500100300000000000000000400000202600000000000401200400001200200000800600401700400100000100000000700100000801800000500100000100200000000100804b00000400000600200100800001101600800800700000400300300000500000e00100103801400400101500000200200200001a01800e00b00200000001c00400401200100900000800501b00400000000000100400700e00500700000000300300501600300000000300000300100101101300500000c00000b00000000f00000000100700401300403a00000001000600000000100702c00501a00001700000100000000401e00800000500000100000000300501101600000000900000000300001300700200300500501800600501200800300300300400b00300000200001200900100000100300c00100400100000a00400f00600100000800c00000000300200d03200900002000100e00300000000
  | 18 => 0xd40007781238614bd64e23ee8f1c0c613b0e001b443000038f9f3503a00000000010688b7197800050a0002fd86ac000988000135800098900023bce6c0004be8000d987753cd0ba0fd2000076957000006e0630aac6b210a22280000000001d708bcfc60475348ad80000000e1084000068e2198b9c0105571ce0a106b82310d1962c0006d6000045443a0000001b9c00000005d24f13fc0000000000e7e0000001e7c66e00000000e07ca00002600005ea0002820000aaa0b00e18000e4039a1f7098ca2216412686a807816d2ed8000306000000000059c3d4141800124a7542dd9c284c41ce00000000b6000000289000095b4000f4493e6a0040800144a000494a0100000000000000f0a1dd2d40000000a780001dec0000003fd0a8cf2c5680000ea81e447821900003204b94019bed0e415f000240000032b00000009aea7c000000000000031b8000cce00055018f4f022612f717fc50e9c535600008c47630dc8e7c82c64d1c19530bee761363058c2dc6863541f311e202f3f893f0f843ec00013d140c3da1218c0c4840a74df85709d258e075914cfb8a8e3ac9c4c5da0004209ebc00034d0001fccb42000000200400024c38a90b4926000265a5100000002a8aa24000000147000042c94553da3e0c0a07029283b0c429ce00025a50d65e013d000000000000004b5146a1b1c980014e03c100000000005f34040000220a1026a94f412a7d719611d074c000423a25c0009c90001c2c0000000000b006e078700012f4b26a91000000117e0001b780ecb8000044404bd4448911a4a7644582731a100009b434f0db205c0000e63639248a864222871c5000099b0001795292a5a49697910b637618d00009ce000000196ceb87f6000182c512a7e0e602087089141f01c60c8a02c1761a2c42a0004c180000001713b80c1800076f4c2000106c6191ee0160e841b724a005d04267d29000006509b41050000fda8454b887d11d6000434a2986688194379a4d0a097251e8028b6019100021840007ee1949ad0bd428a3090cb51ea0000002438c500001568000ca400000011f4d8a1f500026740000001fe1470e949734a426e01500000d6800029a0000001cc52dc0001eb800074a95545a0abcfaa6f81599ee8cec17842c9221242a0f00013bc5b22440000f154c61f80598eb467400035d00001dc1d7000272129c6f702882e057a10900016b4ae4000163851c89c0003c900010f218d0000de400011a1280000cc2000443000043400000002954dc00000015f10c400017fa7a4ac00b400028a800083b23e233401e168095a0a51ae00011200008ce91100800000000000000fdc0007a800000015029b33e923a4000529000234010a8c819d91206da6f63d50ec879897e4ae0ef14f455a0618dac00043853b07f4f1c1cf4448b694ca4c
  | 19 => 0xb500000014600003c200000000003ef00010e82713f38000b960330970164d3022e1640b5c4b411d1e70fc4a9a0e51b60150d664f612f209c3742cb28688487500a2000000000000045117c400072a39a800000096800000013dc3651d88000f4400000018c000040400000006e200008c9a893762193d98f0136489324e149816c98b454a83498c532111297945e1fb23705152de7340d022e000027544080004046081469350a3c63520319813cea4309524548f20431fc2404ebe0000002089322a5823680008529021c513800005a500000000007681838fd80cc0002d180d400009c0ea0e20000295000000026c5e338785a914e7883b39338d2c0264db80000000002ec00000003a70000000a6c00000000013b8962210011400000000000000008964d48e504ae00000000000002e6000038c00035d000000000041a2e9191c0003fd00000000fa0002740a008a20004ac000024c7250000000da800000000000004684602a9c9c653705e9940e3203408782c427a06b2ff282c7008553ed90d54908c154203649bc68f1bf29183da1c43bf8024ae09ed22a8000052a3906f0bc44748320b085f45c26dd000000106a0000001eb000012900009a871e0a4000000000055e00000005266e300000000004b6000000000090800000003fc47f000033800000000016980003a22758000f9694b1d80184dde7ff0de80000007ae2258000000aab011000000000000018d0000ab0000089cc006414e9800000039d18d8000a3057f0000000df875d00000006040000100000a9c6f500027741be1c707eaa0126433152008d445298a12a184ce724e535391a8c6c769107284c1f60250e2a07cd106c84338a4854270d000052c00000000022100000002e700009ee00043a99880007f40001a8c000170000000000000029389c95521d800000010c80004fb8a5941000044a8b309c876c03110e80a0000394089855409d26780685a26fd0000d9000059800001bc0002202cf800000000039398393580004b2a4d0cf276a0669218da631c5571c2000000018c0cc94f214025197e01a08e44e32a091aa59432e05bd2f00c40458c944e042e2cc8c3460810e3e8800000026939822ac40e5f042e2040c9613e057a4a0b0485248e063000000035095d03502a24bb80003aca532d9984035e0834ed93290a84f3355800077a00026e00c55380001a007fcc0226602e133000088a3da1a241f224e0ab80000005462e1800000040200000000003540000000dd4000233248101c6e43f795acc1200019c244950a43e4b000007b225927c86745ca3693609e7123e5b84cca014c88624461974c0887660ad0594baa30829c1a7c0227650c088e410e01f20888e0f6a0000001d30a5c3784f1923d3de84f0f8a6e8b128e01591cc91ce46b2bb23b8e1c2081998d
  | 20 => 0x42d5441ac3010a3c00026b13b8000b100d704d85d800000000000007227e63ed00000000004340ca800075b02010c40000005438aa00000000001b3800088f07a1fd42ce0000000a9924493b370930898802b361846cc8c3920000ae942885d40780000002f40ad91ccaa800042ba4114e86fe00006c88de7484b3040000041c0001b24bd898e3ab9e08c643862c0910d3e81de528a694d181d02319b60f364fd1ac29bcf4c66e4d520e41a82f62cf0ab849415e2ce8000000142000000000000036e1a140547df19712d000000000000000008f22d380008ee0001320000e3c000338aa0d28e95621b14b53a40004fa8e4047a00035a9af4cf8a59000255cb2a00040e22900bea680f200000002331068cd8e38015165000104642b2f480000300002d2083c12253c00000005180001248f280007d35358000a5e0002690d18a56540520942421a9e24f422f86be0cb3c021f49dc2bb0bd0dec1406691342658ea22d00b9024901478f48183a444a3532cb9f145dc61f0000000e18413000238c00069c000000045a5560a50000c280e10000000ebc1c83d826f438c7c422f15f4b0600051b8cfcf2e000000000000020c503a9fd31a0160001a90000476013a61800005d000000000000000016d913c44200000000c82533ea04d4f1477c41d0000ef414c000276800000018ca8a496044700000000000004e10f986d400021ba7545e60000a90f7cab29c425d1cb53bc9a029201793e29e509014751d04120d98c5039a6f309812c5134a9849d2a2d1543b30fe25d8fc415138d03c0ad895a00007a42502172e8109c2a6606104876ce4c6c017780000009d13e80000c860000000000a0c8991291834000a500000000e0c7e83f200c8e8a04a1d78000b3400007f002d3200003f5216800000000020940000000002440000276000000154a000000000127a9c1000288c5360003b99d2c4da00005191d50f47c94588000ade66f3350ac119e27f24090f422e258324823800000018aa93cc702e20000250b545be1fd800083e2fc2cd800000098754d800000035a4e81180e420001a38bf8000590285000046017e0bf80006e60fc0b995988d801953e92588ba41950c80004ce4570000e5cfac5b900000000000003ad2364000000000000000000032f9adcdca791002819c0000f51f78a7c00000000015ec788ab100000000000004c10c7c0008601f4000000088e0001ef826e89f2daa7e4d9623e3a6a8b4dfe8ff4a1000020a6950000404cc64a007c00000008b62c50000daa5130000c890986b039f19390c64c85551de47c21272e0a87cac49643d295907d49e11d00f892706bf22c89e004241e3fe27f0e6637f29a9a944683d235e0c580006d00000bdc0000003848c44000000000052402856e47601a830e5423e011ec5100a14a62a740000
  | 21 => 0xa364e39eac1b68941f9a7d8af48db253899400000045e00001806ee000007400019a00008a10282d30c70a50fe463f0d4a118ad462708a04b07e82d2475092c0000002751208000000083041c9800005260000d5c00022a00002b266830e096c00008936c87c00608a10000588eac2b70f399d548435229f19c016434317216a4b2c35b3399d3d4ce4e150e1c1c3ca36228a19293300600cf26845fa31733d20f8a207ad1f820c54348c2109a80ceec49800017e8be867b16e28f0e920004d113345ac6df3971c5895a9c34869cbcc227f940380380a440743f8fb530208f3118e253388562e797150484a937023850706644a18aa47489935430784a3609a0caa33053a49900684d13fe86d10d8cd43442b929d8bc933e00019ca4611365234e026692722b53dc8a680003e3074000049e50152e25785865bd00019dd3a882d19800007042fa498800064c9ab3b71148b22000378000000000024b9c9076800005f12890ee92c2998b102d80002a78bacee43b7137800101a0c93b880002ee8704e7987444287c06e8d108200f737684080000002a9a06c45600034c913000012400000007900d300002fd49450b0ed120d41862f00000300000004d8988800000045800000000002328a64fc251701f14a14e40f633a11000008534eb9708c5c96d47baa994c83dd3dc0000d0840c3b58c907bc3fa0fd17992e01b800000000004f844c00000002b1394800152c0001b903200f24ab46592745842454a882dcbda5841300df0d0672b3730000e029262a49e84e7000004c08f01081392f38b3d3d80000000e642088e520c20cc8e47a022b195c0000000002abd21867200000000002414998ee08760423ec800000000052f800111a96c4090000958186152a4141320002d8aa903000900001ec52f88b90000598f0c02d0001e5400000000006942a84051e6a0f0c406915300b24aa4000000064c00000000018f800092e0df98290925441df0000d1a1ec39100011fc00025225fc6dc0003d1800000045a0000d448b656729c93c93000d1374a1953f68480cc8be40fe4263ce82307a6a993789b09018793000202400066d10a0c810961e046ea2b49660000f9000000000000015dc75219200003051fa04940c0348bb208d3a21f1ca327bb2e5249d02267e379200815c77d25700000006d10001f194080000000000bec4af0f100002f63f5000288400012151da9b4a940002f901c800044f00000011a455d13d9e5040c44608c0000000a4d291065097e2ea000164891236800029b126c62c2b9832800055801b8b180004340da192054e979000186c0003811ab80000002fb000000084800052b8000b1e00051a1af8126a9a02ba6f0a0a73a2458000aa009f1c623c000000000011854222d524398980000000000c84d0231d4b52824fb064f3892
  | 22 => 0x3be65822081a000000043892308f47412eb00011920004cb80000002de48324280000003f60000a2442f55406eceda3bb1ff16c91180cc00015e00006a600000000000000e58000f2000000000011200004848000a1e0000000d28000a470aa9f80c622040c59830a600002810b7d55a6b249827ac40a7992ef8e14cd640f46980008b00ac00005a45203005461b5c5e00004d3027846400000000014040002d11a5c00000030d26c10f60003a9000000000640981dc0004951c6800085478b51f06f800000046500007729af00017e531e3c90001c445c66de12e0c38a583e92db80000007ca000121424a66c45ea0c00001111d5800089433c00019515585483a18000d881dc4df2468ea6a61189a0807f20cf54f862554244d03d0a08bae9534d6800892214422e15941149cd1809c00b8c4fa078931552400008426e4e0899e4d40b151ac54b5478afd29e8fb07998a81aa6af39b8000b00a180f71df800000000028789da8c72ef000000011c31592950548ed14b92c83aa4713d480010ec8e225c0560e9c919495a9d46cc69d30209f44aa01b507001cb7414107f85380008ce54980000008c43a328cd1047a750ea7e8cba02e14099fc9fc00016c0eb00000a65258000000000518800082a680000000000048a3298c151a20393550ffc0004f039e997842292a25326512360000000d0478c0000240ad050c76230c25ed4c400003a8c3d2f45bf35da458bc29071850e38f64a97457a82846e2c13e4145906e78339182582903cf356a7900000004a099540ec1c13de96191f20e22ba8efc8885dd27a96b076a0e7091a1cd34e3451eda274da437d40d257514a0004da97d51a89f20000000860a884f828c800056935b268c8280dc3d213fcdc462937628a0000000201a7cc0000004b0a9100000000c400007ac0bb4b3905c6ce81503d878c0500c50c221e0ae25b43e7224946a00028194c52a851a52e8c7846c2743df80003f25a00000f2c244000089800087230b0000220f3058526f9ff469810302b1d0034c84e1880e1c184a203328d7808c880250a28006c2a00f586c400082b54a80000005791488f08d340003ff00000000000c100000004b73b22134c069ca063800000087e513134000060f4a82654e3600000019310584501cf000107e91732b00000008bb2e8808d08804b000000034263c36694fc2c004f22f89589f63d5497a9ccfe00002f42108336a0500000003a49753fd863cc767eb1db0ae000077400000008360004058cf400068a204a4780000002541a78d203553c6897c5d209726c04fd4b62f8034a10ce041b04db13751bc2484a50000b8e7b60fba6902d60da10e00013cc013205a85c0f06f44a010212266b100000000004b500000000004c32108a600009630001c5c00063a1d181f90dc9235008a90978
  | 23 => 0x2100ac205529a21603940b92072178538a49538947cdb40bc4921be400000043525650cc0411ca9edc3de607454038072c83d0568e2c1de42c3651d414701f609e08fcdd011f0f41fe0bde9d82a2800110e34e00015055463e724d22d433e79e2d714200a661e0432948bf81334c29034b9a198000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc4e7214363c40010bb0f328c7880029360a6518f100042fc3aca31e200089d8799063c400113f0eb20c78800217a1f6354b1003d27416c6a96200286e87d8952c405b49d07b12a5880030e9907054b100042fc3acb196200085f8759432c400149f0ca90658800293619520cb10006273b2a41962007c4c7654832c4001c1cc8a90658800383591520cb10005a4402a4196200085d87d8e50c407749d05b1ca1880022761f63903101d547416c7206200089d87d8c40c407351d05b188188003861436310310004ccc3ec62062000e1a65d8c40c400171505b1881880026661c63103100051dc32a42062000a9a860c840c4001e12a4190818800217e1d65cc3100044ec3cc9986200089f8759330c4001b24e2206618810e1721d654c3100c44f43cc8986201489c8759130c400189cca392618800313594724c31000647320e49862000c8d641c930c40018acca38a618800315594714c3100064b320e29862000c95641c530c407dc34ca2026188003621c8404c310006c8388809862000a4d82141638400f49904b1aa5080b69320d6254a1003e27bb2a41942000c4d765483284001a92a4b80650800274205700ca101b4e2412e018c2036d4473548218400145b04286c8880028b608501911000526c10a1b1a2000c4f759cf62440010dd0e286c4880021b61c501891003d27416c6a92202da4e83d89524400149d0ca90648800293219520c910006273b2a41922007c4c765483244001c1ec8a90648800383191520c91003c6c432e01922000c98645c0324400f990c4b80648800352549700c91000662314e398220008ce861c9304400189eca392608800313194724c11000647b20e49822000c8c641c9304401b19d0fb12608801e3321c624c1100062bb28e29822000c54651c5304400192ec838a608800325190714c11000663b10e29822000cc4621c5304400149b04282c60801e93209635481016d2641ac4a9020078d5869c632040691a902bb0640801f13dd9520c81000626bb2a41902000b4880548320400f19d05bb4620800315d49760c4100062a282ec1882000c557654831040016a100a90620802a35e19700c4101a4e2412e01882000c65765482104069a88e6a904208002d820152084100052ac30632802000b51800c6500400152b0c18c8008002e460031900100070c282c62002000a95860c440040b1e20a01888008003c40c65010010004e8c38622002000b90815cc4004001725031908008002a6618321001000784a90642002030b90835c4400400174104b8880080c2e4a063110010185c9c38622002000b91870c440040af725041888008163c4d48311001000788a90622002030b9283c8440040af721061088008003c8548211001002c6a40aed9802000d88721013004001b20e220260080c3641cc40c4010
  | 1 => 0xb0e194a1100ef131d8329422000707b28652044000e0f650c840880017130019081100021761f65cc2200042f43eca984403bc4c72d9530880018aeca38a611000315194714c2201f70c328809844039d88721013088001b20e220261100ef131cf65c82201d706196c8a924039e0c32191524800f49d05b1aa4900030e1907054920006163b6c8a924000c2c76191524800149d0db9aa4900a3131db735492016d26430e6a924026c4c761cd524805b49d0db1aa490003131db6354920006263b0c6a924000e0f6418d5248001c18c831aa4900031318c70549200072231aa5b0a4036e443254b61480014cb04286c29000389d91521852000712322a430a4000e47635486148001c88c6a90c2900d2b460073185201a723192a430a4034e443254861480014e100a90c29000391e0d52185200072241aa430a4000e47735486148001c88e6a90c29000398e01521852000532402a430a4000e608054861480014cb04280c29008293219528c520006273b2a518a4000e4552186314803f4990ca9062900b7131d9520c52000722a90c218a4000d49525c031480019a0c2b80629005a8b2195290120006173b2a52024053e0c6354a4048001c4aa430c80900568b2195210120006173b2a4202404fe0c635484048001c4aa4308809000253e1d52cc12009d26432a59824007c4c7654b304806998ce430e60900039154861cc1201de26396ca982403ac8c72d913048073918e432260900025321d524c12008d26432a49824007c4c76549304806d1ad0c38a609000315d94714c1200062a328e29824000c97641c53048001928c838a609000351548714c12002c6b43ec29824036cc472d853048069988e430a609000391548614c1201ce4c3b080982403ee18651013048001e12a42026090003641c4404c1200074830880982400286e86dd62048001898c7bac409000319dd4618812003d2741e64b284000a4d8214163080a9898e4282c61001f139c9658c42003e26392ca1884000c4e73596210807749904b1ca0100021be1972940201d706192cb200403aa8c8258e4008073c1864b2880100e28e20165100201cd46412c62004000e185058c400800f19904bb6601001f131c965cc02003e26392ca9804000c56651c530080018aaca38a6010003131cd654802000632b28e29004000a4e82dcd65c400145b0532cc9880028b608509931000516c14cab262000a2d8214164c400149b0532ec7880031399672d8f1000626b2ce5b1e2000c8e649cb63c400191ac9396c788003139d672d8f1000626bace5b1e2000c8e749cb63c400191ae9396c7880021761f52d8f1003e27396a5b1e2000c56759c763c40018aaeb38ec788003259d271d8f100064aba4e3b1e2000cc6729c763c400198ae538ec7880021761c50d8f1000526c10a1b1e2054
  | 2 => 0x62d01300062b3a8c3a026000c5575187404c001ca0a030e80980030719676901300060fa94ed2026000c1c509da404c00183cedb2c8098003239db6290130006473b0c52026000e0f6518a404c001c18ca31480980eb83a1462901301d706c28c52026000e0c5018a404c0014390ca948098003079d952901301d706312a52026000c9676d86404c001d08c5b0c8098003259d861901300070bb28c32026000e1465186404c001d0ec430c8098003a118861901300070ba90c32026000e1552186404c001c28a030c809811a87a1a50901300060f3b4a12026000e0c62942404c001c28c3284809800313dd46250130006263a8c4a026000c5775185404c0018a8ea30a809800392140621013000728280c2202603eb1885500404c001d20c2a0080980030719676101300068c284ec2026000e18509d8404c00183ea53b080980030714276101300060f3b6ca2026000c8e76d88404c001e10a1b108098003239d8621013000707b28c42026000e0c65188404c001e10a031080980e783a1462101301cf06c28c42026039e8980188404c001d16a0310809800383140621013000744280c42026000e0850188404c0014390ca908098003079d952101301cf06312a42026000b1880548404c00192cedb088098003a118b611013000788286c22026000e1850184404c00192cec308809800385d9461101300070a328c22026000e8762184404c001d08c4308809816ba4d80611013000788280c22026000e1752184404c001c2aa4308809816ba4e00611013000749a80c22026000e1450184404c001d20a0308809800384140611013000744314e02026000e90619c0404c08b43d0d2808098003079da501013000706314a02026000e1461940404c07d63501280809801e93a0b735972000516c10a13264000a2d8214164c80b389eec39aa5901531318c7054b2016e2739aa530e4007c4e7654a31c8001c8aa530863900eb8318d52903201cf0631aa42064000b288054840c80010bf0eb2e61900022761e64cc3200044fc3ac9986400094f8754b30c80870b90eb2a619001f131c9654c3200c44f43cc89864007c8c7299130c80291390eb22619001f231c9644c320004a643aa49864000c56651c530c80018aaca38a619000325990714c3200064ab20e29864000d45521c530c800149906b96cb10002936086598e200042f43ecab1c400085e871956388001898e5baac71000217a1f5258e200042f438a0b1c4000a4d82141638804d0b90eb1aa5100025361f650ca2000626bb6ca1944054b4a80d94328807749b0fb2865100031361f650ca202a527406ca1944000e4a80d94328800189ecb388651000313d95700ca20004e240ae0194403bc4e72d96318800f39104b806310003139cf65886201de2639eca10c401385f8758e508800129
  | 3 => 0x430a6000a5685188614c0014ab0a310c298002b1a186218530006633b0c430a6000e4765188614c001c88ca310c298003a1d90621853000742320c430a6000e4685188614c001c8b0a310c29800295a1b52185300052a436a430a6000e1764d48614c001c28c9a90c29800391d8b521853000722316a430a6000a5686548614c0014a90ca90c29800385d9152185300070a322a430a6000e4762548614c001c88c4a90c29800295a1850185300070bb20a030a6000e1464140614c00168b04280c29800391d88501853000722310a030a6000ac6829d4614c00158b053a8c298002a5a1075185300054ac20ea30a6000a57855d0614c0014a90aba0c298002b1e09741853000562412e830a6000ad3805d0614c0014ad0a3a0c2980029561474185300070baa4a830a6000ad380550614c0015a100aa0c29800295a1672185300052ac2ce430a6000a56851c8614c0014ab0a390c298002a5a1072185300054ac20e430a6005ad1801c8614c0014ad01a90c29800391e09521853000723b92a430a6000e4472548614c0014a900a90c29800295a1642185300052ac2c8430a6000ad280908614c0015a301210c29800295a1442185300052ac288430a6000a57855c0614c0014a90ab80c298002a5e1170185300054a422e030a6000ac7825c0614c00158904b80c298002a5a1350185300054ac26a030a6000a9784540614c00152908a80c298002b1a08501853000562c10a030a6000e4682140614c0014ab04280c29800391608501853000522c10a030a60078cc825db414c00f19d05bb2829800233a1b725053000467438c4a0a60078cc87189414c00189eea3128298003131d462505300062bba8c2a0a6000c5475185414c00198ee430a8298003311c8615053000664316e0a0a6000cd061dc1414c001990c43828298003341847050530006273a8c420a6000c4d75188414c0018acea3088298003155d4611053003e26312eb90a6000c5675187214c0018aaea30e4298002932195288530006273b2a510a6000e4552186214c0010b90cba8429801f1318975085300044f434e810a6007c8c629d0214c0011390cba0429801f23189740853000526432a410a6007c4c76548214c0018acea3084298003155d461085300064b3a0c210a6000c9574184214c001c8aa4308429801f3218a70085300066830ce010a6000d49525c0214c00183cedb24a098003079d864941301dc2e432e5282603bc4c625ca504c00189cedb14a098003139d8629413000707b20c52826000e0c6418a504c07789b0e314a098003929c062941300062b3b6c32826000e4462d86504c0018acec30ca09800385d9061941300070a320c32826000e4762186504c001c88c430ca098003155c8619413000729380c32826000c4e7518b404c00189aea31680980039214
  | 4 => 0x24c001c1ecbb20c498003831976418930007073aec83126000e0d75d90624c00149d0b320c49800293616641893000547424c83126000ac681990624c00158b03320c49800293e1564189300052642ac83126000ac781590624c00158902b20c498002a3a18641893000707b28c83126000e0c65190624c001c1cea320c498003835d46418930004a6c38a03126000a4e86140624c001c1ec8280c49800383190501893000707aa4a83126000acb80550624c00159100aa0c49801e33a1f511893000466c3ea23126000a8e84144624c00151b08288c498002a3a13501893000546c26a03126000a8f84540624c00151908a80c49801e33a1c501893000466c38a03126054a4f87140624c0a989d0e280c4981529361c501893000626c38a0312600084d87140624c0014ad03bb2a49800217a1a765493000627b90eca926000c4f821d9524c001838edb22a498003071d8645493003d27436c4a926000c4c76d89524c00189cec312a498003131d8625493000707b20c4a926000e0c64189524c0a9898c4382a4980023520576d093003e26312eb2126007cc8629c2424c0011ad03bb2849801f13189751093000723b28c5b0a6000e446518b614c001d0ec8316c298003a119062d853000723428c5b0a6000e458518b614c0014ad0da96c2980039118b52d85300052a432a5b0a6000e446254b614c0014ad0c286c298002d160850d853000722310a1b0a6000c4f659ca614c001898cb394c29800323d92729853000646324e530a6000c4e7518a614c00189aea314c298003239d0629853000646ba0c530a60008ce87189614c00189eea312c298003131d4625853000647ba0c4b0a6000c8c74189614c0014af0ab08c2980029521561185300054bc22c230a6000a9484584614c00158f04b08c298002b1209611853000563416a230a6000ac582d44614c00152d08288c298002a5610511853000526c10a030a6000a5582d94614c0014ad0b328c298002a5a1265185300054ac24ca30a6000ac682994614c00158b05328c298002a5e1165185300054a422ca30a6000ac782594614c00158904b28c29800295a1865185300052ac10ca30a6000e1765d90614c001c28cbb20c29800295a1664185300052ac2cc830a6000a9684990614c00158d05320c298002b160a64185300052bc2ac830a6000a5485590614c00158f04b20c298002b1209641853000569c02c830a6000a9686190614c001c2eca320c29800385194641853018749b00c830a6000e4765d88614c001c88cbb10c298003a1d93621853000742326c430a6000e4785d88614c001c890bb10c29800295a1662185300052ac2cc430a6000a9684988614c00152b09310c298002b1a0a62185300046bc3ac430a6000a5785588614c0014a90ab10c298002a5e1162185300054a422c
  | 5 => 0x183460c8705484000694190e0a908039d0c325d6321000127100bac64200ea27e19708c8401cd87c3aa4190805fd0f875483210073a1eeca906420003435d9520c84000785c02a41908000b0c805483210001e1100a906420002c2201520c8401cf85382a41908039f09705483210075c1cc0a9064200034354a710c8401d44fc32e01908000d0d525c0321000132902b80642000346141700c840004cdc32e0190803ac9b865c03210001a370ab80642000346215700c8401ce8da92e01908039d8a525c03210073a32a4b80642000362549700c84000684a92e01908000d93815c0321000133102b80642000364205700c840004c840ae01908039d0e7254a311000163100a946220002c6201520c4400c44fc32e0188803998c825c03110001a30a0b80622013f439cd528844000594402a51088000938805d4211000185aeca9042200e7431cd520844000594402a4108801889f865ce6010001a30a0b9cc02005227e1d6398040004ccc38653008000f09520ca601000161904b9ca020107469c173940400048ec3c65280800091d870ca501000163300194a0200b713a0b7654b3016e26c16eca966007c4e7254a61cc00149b04284c39800293e19528873016e273b2a510e600085f865d421cc00113b0d3a0439800227e19740873000527c32a410e6000e455298421cc0770bf0cb94a1980ef1398972943300050fc32a52066040a1d8694240cc00143f0ca908198002c620152103301f50ec34a02066000a2d82143644c00145b04280c8980021ba1c50d893003c6743ea6312600086d87140624c001898653b2a49800313cc8765493000626190eca92605ee0c32d91524c0bbc1864322a49801f13189758c9302e722192a5b0a6000a6582143614c00158d05a98c298002b160b53185302df23992a430a605be4432548614c0014ad0b190c29800295616321853000532c10a030a6000e2850188404c001c60a0308809800287a1b52d91300050f430a1b226000b0d82143644c00143d0da90c89800287a18501913000586c10a03226007c4e76d4b624c00149d0c3aec49800253a1c50d893000527430a1b126007c4c625d6624c00f918c53a4c49801f2318974989300062bb2ce33126000c54659c6624c00192ec938cc49800325192719893003e62314e33126007cc4625c6624c00f898c4ba8c4980461761f651893000526c16ca3126000a4d82194624c00149f0ab10c49800293215621893000547c22c43126000a8c84588624c00158f02b10c498002b1205621893000707b26a43126000e0c64d48624c00149b0fb28c49800293a16651893000547424ca3126000a8d84994624c00158d03328c498002b1606651893000547c22ca3126000a8c84594624c00158f02b28c498002b1205651893000527430ca3126000a4f871946
  | 6 => 0x724a9064302820086d821c165104010f100bb2a42080293e19520c84100526c32a41908200c39651c1411040f19904b9cc02081f13989758ca3103e27312ea3146207c8e625d0628c40f49f0cb12a518953139887054a3103e27312eb2146200a4d821d5608c4010bd0fa92c1188021721d525823100526c10a0b046200d1575504410c40172100a08821880313dd47258031006263a8e4b006200c8f741c9600c401918e8392c01880217a1f525803103e26396a4b00620085c87549600c40f898e4a92c01886a17a1c505803100526c10a0b006254c4c72141600c40149b04282c790802936085058e2100526c36e6a94422da4f861cd528845b49f0cb1aa5108031398c7054a2103e26bb2a518c4200a4d8214363484014d304286c0908029a608501812103d27416e6b284200a2d82142640840145b04282c8108030e1c050590212a626318e0a904207c4e72596310840f91ce4b24621081f131d9520c42116e2639aa4b004200c4f76dc963940a989cc0392c728003529807258e501dd26412c7b14a03b85e8798d629407749d0531ac5280ee1721d6358a501de26194ed194a05485f865c2329407729904bb065280ef13189760ca501de26412ec194a03bc4c205d8329407789eedb106528003135db620ca502cda5406c4194a05485f865c032940012a902b8065280ef52081700ca500ac9c402e930ca03b94e82dda319407729904bb0632810e17e19700c6501dca6412e018ca000a4f8654832d000149b0ca9065a0002d2201520cb4003e65312e01968000d49525c032d00013a102b8065a0002936085058e4003d26412c6a94802da4c83589529000f89eeca906520003135d9520ca4003c67416ed18c8000b0d82142639000161b04282c7200eac32096354a4029d8641ac4a94803ad0c325d6329007313f0cb8465200eac3e1d520ca4031687c3aa4194803ad0f765483290001a1aeca906520002c3201520ca4000686a94e2194803989f865c03290001a1aa4b80652000265205700ca401d6c4102e01948000ab280d86619007531d05bb463200eb439c9528c6400a44fc32e018c803a98c825c031900a7a1ce6a9443200030b5d952086401d68639aa410c8000b0c825ce509000123b0f194a1200024761c329424000527432a41928000a4c86548325000149b04282c62001e93209635484016d2641ac4a908007c4f76548321000189aeca906420002d2201520c840006a4a92e019080009d0815c0321000161b04284c620002c36085058c400049c402eb3108039b0c821cd521007361904b1aa42013ec320d62548400068db98e0a908000d18731c15210001a3506382a4200034660c70548400068d318e0a908000d19631c152100c3a5304382a4200034a988705484000694b10e0a908000d2b321c152100c1a3464382a42
  | 7 => 0xd40c80402a0340480000604c05800000000020150000000c80900005c1200101801c0f8000180100000800000c0080000c0000180501000c01005004000000060140740000701004c0f800002000060090100100480505a00009002000008128170000000000101c0000182401200000031004018000060000040000000a008018050140040b80600c02003803026064018060240040a0060160100000600c01403005024000038020040080200201002c000020040140107f0eb20c8a90028d20564191520051c402c8322a400954815c0635480127100ba0c2a90028d211611855200538402c230aa42d85d87d8c605480189ae5398c0a9003135c9731815200526c10a0b1e8400a4d8214363508014d304286c0a10023520573980422a626190e0b2c6400a4d82142618c8770bd0e282c11900293608505823200526c34e8a906400a4f865d1520c80168f02ba2a419002d12057454832005a5c02e8a906400b48805d1520c801a1ae83a2a4190029361a715483200527c32e2a906400b0f845c5520c80161908b8aa419002d2e017154832005a4402e2a906400b0e841c5520c80161b0838aa419003515c4715483200587426e0a906400b0d84dc1520c80149b0d382a41900293e19705483200587c22e0a906400b0c845c1520c80168f02b82a419002d120570548322a4a7c30e0a90645494d861c1520c80189b0c382a4191535298070548322a6a4b00e0a906400c4f8754a610c8018990ea94c21900391e0552984320072240aa53086407e467154a610c80149900a94c21900313549709843200526c10a1308643bc4c72dd5600c8a9898e43aac0190eb231cb74580321ce46390e8b006400c4f87549600c8014990ea92c0190031321d525803200707ba2a4b006400e0c74549600c801c9700a92c01900293201525803200724402a4b006407e4b70549600c86d988e5b8ac0190039154b715803200626a90e2b006400c57751c5600c8018a8ea38ac01900325dd071580320064a3a0e2b006434cc4721c5600c801c8aa438ac0190d315d4871580321a663290e2b006434c55521c5600c80198aa438ac0190031154871580321a668c00e2b006434cc4201c5600c8770bd0e282c0190029360850580320062a388a0b006400a4d8214163d040f49904b1aa5a08b69320d6254b4103e27bb2a41968200c4d7654832d04010db05386caa08029360850d8d4100627bace7b12820086e8714362504010db0e280c4a081e93a0b635494116d2741ec4a928207cc4629c6325040149d0ca9064a080293219520c941006273b2a41928207c4c7654832504014d304286c0a08029a60a75d814100565416e7b028200e49520cb605040f19904b98c0a08029a608501814100534c10ea3028200ac8825cc605040156102a10c0a0802b4a0632181410
  | 8 => 0xf83d01de00e5b06324540481960000005f81e014c19e1f23c866020458a4ac71040c26859a84459045e86813646424e2486e24d60b83607cc48c4461884204b47c685011285e0a60c25dc6ac08c79449e00057669e85410a3e221c2b07fc2145d000079000000027a2ee3d842c7aa6dc6e05985f680e0663c60004d800000044800047c5826582247d603a0be0700000fa3243f22107748183ae03838e7a80005e20008265f06a035c3920947f22d83d281083c75064a00028200031e2b600057a7ae1be4dc00044c0000000ce4980004b20005a003e6a823e70615e41c25603c0003300007d842200072c00000035e4327583022c47483de5522802d235800000068e4b60001526f47866864520bc0006da25e7126288027841661905a20846267203a83d60004f46786900004422ce2e00aa0a266a3521382785401e88320000007e845a0000ba66e6f657c6ca00063484665a6240f257821a4a041a6427bc2124685d80005a675a2765047087d407a28a2de10800019c54400060a06431a54230022023844015430a1342ac67c5002745d20b62222ca3940000201d600056052600000075c00034e7521c62da7b650638a4007ce78e6d230c7a217806c6a229241679e7a060229a1ae20a0001440002d67dc3381d20f01720002340000b47620002646fa6720fe05834635034204a07e3804ee8206044cc8644e800000000020021e04c2a613200046000600055450a0000001b40004881bc7ba4f01da7f648a0001ba0003c446a08a6ea6527c274a58e2a24247360f65461b874c5020ee18400020e7fa4a66bc0fc6c827000a39c1a287200000049c0005c80002ba16200000002606e0006740e442e3c085c4f20002b81e44d080870c1aa18c4286082fc01614642666c28872864800008005483670e6568426d459e0ac61665e86c03063e48e15672e43000000000036c3366961b638484e0002982ae8307ac0602364f640e00000003000c0300000200401800000000060040060ac0180b0000000b0070060081c00400001c0281804000406813002008000000000000100a00c050000000280000281100a0100300301c0380281900a0140100400601c04001028004058040000000680101c0000b0080880000400002a07c0000000e0000100000a030038000aa0300580200002c0000d00e03c0581b0020040280402a04c000010000240401600c014028100020040780001201c048000060100280c00e0180b80400001c078050200301c0020060740204502a01c078060260c005004008048000060340340980d0000080081a0680040101b0020241381907a02c070000480a8058010020180100e0080600380001402c048000140000200c01000000006002028048000000300380f0020200480000600c0300003a00c0600100000002001004
  | 9 => 0xc00051e0000e200038c66802c37618028c1102f41e60006ee1c03e07da50c00001c4ca7180001f000062c0de00000009c0004d259400400039e0d40000004383f80b04c086e00000081a44e8006b000000041e54c2f60008288787f07ea3621144ae19a3b00460a001413029646e68a75622609e63a06a3f00f864e24c12400068472652e61432842a27c2161064100c423c22e0441403bc49081e60e62a83a67e7ca7723145b22c270a0f400056887a26059c4c433e47007600000000c6367be3a657e6a61940004e271c74617447605a0003e65727b26b40006660000006c00006be48255a8065e88148384c65d66760c62900906803885f236479201a1c201e4744c211639a3ec32e6202be2d00867822c67c813c7222f21fa6c480c12e14e4fa6f81226406d078a6825845ac54a0006ae00000220c0d200000000000000000032c0000005284fc76e05071e0000d07700003d453e4800425fc5a82fe0da47856c3ac77e67a23218a0ae15a3224961500000d830e6e429481200058627e2585663b62060007a42e41f479862e00000000000067007c0006b68407e02843be34061e1420a80cc4bc4923703263ce5ae2727323a43080d65ca80a76685a00077c0003b80003fc0983544a81fc00052481611a01863800000000016051a0001d819200017600000074200000000017064c54e17a2e269a40858c3783482c01585c64a42a44be3ee18e22a31855656a4ba73482c3a213a14a2bc7547605107144ce2aa52c64402451413e46610453a76c3162d409686058043a5b624005e6de4507fe6cc7043e475e5320123681ea18643e1ee6544065486d83c21b22fa2cc4de12846217e2f03b482407474e51209a15c5fe65c6ba4a23066fe10286a73e5bc43c29e4e482a1cc7682445de02e73c2661180005e06e60005925640007640000005ba23033a00000036a0000001d05881d41f83661ac7444121b00e835a1488700e063c61a6947167400005c426a7d01680408042182280c853c52a00069800000036e00000000000051c62279c0000345f447a1a85586e86b260c6fc5c00b200079605c00000077676a1f65b45303340000000005e47de0000ec00012a6c23cc18240225a82e5227d244a11e4aa5964da3907020c000055e3a000032046c0000005740284940000004b061c66428e1c410e7f44564186625aa3822ea2a07b00003f629c40a2080004840a400000000073886207269271a3fe8480001fe0000002545500e677a0000320003100007b42500000000521a645c0003b20003da3ba00000034c6a47ee3960005b83723867e400000049a00006881c5346460007c00000005a400040451653600056e3dc02a5c216c25204e5be5202dc8761dc3ca1ce2e64862b46b84445d45182465da68c22c07850861208843683e30431c12610c4
  | 10 => 0xca0004141ca6502861e25ce5cc0004c825c3f48665707a67885ea33c4e624a7b88568523743568587008220007c44e00006f268811c78c2f84721ec16a4343e826e6ec0007784ec37e0927e22023aa5ee37a6108744d400000016400812c84a23a5ec08260008e72a45853879a16e50e2623ea7e647e0001c85626300224b83320561a473032a2a834406226c2ec0005e62e861831239817c7ec24283469c0001200ea0364ea72400034a0100004fe7f80006ce78073a0000002b21a00dc84c1002c86f03fa55c5fa6066aa6d61980000000000000006c637
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x190b98549700c84000542261525c0321000190898549700c84000642e19525c03210075c0b86549700c8400074054b815c0321000190952205700c84000644e14815c0321000191085205700c84032e60208815c03210001d0152205700c84032e44d48815c032100cb98252205700c84032e44548815c0321000198152205700c84000640548815c032100c190a72201528c44000542648505c031100c190882141700c440006429cc8054a21100c190873201520844000542648505ce6010001909875483298040326429c0825ce50100013109160032940400048a66050188404c0016219214061101300060361f64140624c00180d871905018930004a224184144624c0012459818850d853000681d9182140614c001a0464608501853000491e6362140614c001245981885018530004a4241841d4614c0b7641901c95218530004926605018b404c0016419214061d013000503648509da404c00120d9814062901300058164850186404c0012499814062101300059064850184404c001a1085185401013000542648509d8404c00160992142761013000503648509d8404c00130a981436210130004c266050188404c00120d981406210130004a266050188404c0c960b98140621013030682a6050188404c0c96099814062101300068266050188404c0012099814062101303068218880548404c0017019214361101300078018850d84404c00160992140611013000584a5850184404c00170192140611013000780d8850184404c001e006214061101300058424152184404c001605921406110130005a064850184404c001e029214061101300058464850184404c001e019214061101300058064850184404c0c1a0863201521032000611d94815c032880c960a90d94321022000682d95800c8408800138091600321022000704194711013088069641901cd521852000710548615c0314807704e96e1d52cc12000511e5d5218730480a904c9621d524c1200051125d52185304800150897548404c1201f582259521013048073c0876548404c12000704194711013048001d01521c4404c120007805486110130480c1a088214163100202a413e5d8214363c400104e989d9520cb10006829908054832c400160992143631031030682a0850d8c40c40016099299763103100068299682d8c40c400160b96548321031000682a19520c840c400104d98994724c3100051164a651c530c4001c0a651c8404c310007049947110130c400194152205700ca1000512259525c0324400f84886549700c91000702191525c03244069444915d9520c81000511648505d831040c79407320152084102d464e5d800c6400400160992141631001000684141860c440040af29091618321001000682619520c840040afb00835482110010
  | 1 => 0x53c0009e00388a84e004c9c8ca0007800008d001105e502b8d100000707c001e34001224933031389b4112c0000370050264000a4e80047230006235000004a1a8450a00000000000000009800002292402191513e5e168012e003b8f800190d0b8003122800ac1314028580018108003c1c1a400000b800d61600000003b00000b08f0000000410017000001f8013a001ea1c004000000000000000e600000e80000119f410000000000002920cc2002d18cf415000ac8c212883448000a24c9a094480128483d800be003c8180000001d800000000000900014c00104b16c00000009916002e800720003a206c18361548e0038000ce37002103843101d400603f000da4e431fc4a220e848365901810160000268de9500278000019a60f8050301030200030000010200010001010211040a000200100200000100000005030301000b0d00000104000601070100010500000200541245741d1520c801508905d07454832004c2241841c5520c801504945c4715483200550241711c5520c80144691e1d52580320060321f74549600c80180c871d1525803200582a5380549600c8014449754b71580320051125d521c5600c801c07745487158032007011d1521c5600c801c4390548715803200511241521c5600c801c409054871580321a710601521c5600c801845821c45058032004922418654832104019117520141104312a41325d82141600c40144b96549700cb4000650548815c032d007380f86549700ca4000542241525c0329000190552205700ca40006125d880548321000194152205700c84000642609831c152100c15089258c70548400054224d621c152100c190832201758c840324c2e5c8054832100c930997201520c8400064265c8054832100c190b76201520c840006425d88054832100015089054a710c8401d603e19525c0321000190552205700c84000644204505c0321000150992215700c84030642208855c03210
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x92602859c02000e01400000800430a69819e412882100a310d800b00a939054871580320050874ca9102b8065a018300b86241525c03290001480502a440ae01948000a40a8798549700c84000520150a9702b806420002901a2214815c03210001480542a440ae019080648422a192141700c440004c0352310a1b088098002603a9d8850184404c001300d48c4280c22026000c80d949160032102203248114c4baa42026090002c00a75486110130480c9105d4324286c62062000882aa686548321031000481353328e42026188002c01a29947110130c4001500d10a0c30622002057a80285865483210010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x6
  | 3 => 0x4e
  | 4 => 0x124e
  | 5 => 0x4c
  | 6 => 0x138e
  | 7 => 0x3
  | 8 => 0x5
  | 9 => 0x94e
  | 10 => 0x124c
  | 11 => 0x8e
  | 12 => 0x128e
  | 13 => 0x8c
  | 14 => 0x98e
  | 15 => 0x128c
  | 16 => 0x150e
  | 17 => 0x9ce
  | 18 => 0x12ce
  | 19 => 0x168e
  | 20 => 0x10c
  | 21 => 0x10e
  | 22 => 0x130e
  | 23 => 0xa0e
  | 24 => 0x130c
  | 25 => 0x180e
  | 26 => 0x134c
  | 27 => 0x20e
  | 28 => 0x140e
  | 29 => 0xb0e
  | 30 => 0x154e
  | 31 => 0x24e
  | 32 => 0x144e
  | 33 => 0xb4e
  | 34 => 0x28e
  | 35 => 0x148e
  | 36 => 0xb8e
  | 37 => 0x184e
  | 38 => 0x3ce
  | 39 => 0xcce
  | 40 => 0x15ce
  | 41 => 0x40e
  | 42 => 0xd0e
  | 43 => 0x160e
  | 44 => 0x188e
  | 45 => 0xd4c
  | 46 => 0xe8e
  | 47 => 0x18ce
  | 48 => 0x10054
  | 49 => 0x11396
  | 50 => 0x10056
  | 51 => 0x4116
  | 52 => 0x4b
  | 53 => 0x24056
  | 54 => 0x124b
  | 55 => 0x25256
  | 56 => 0x10096
  | 57 => 0x10b
  | 58 => 0x130b
  | 59 => 0x134b
  | 60 => 0x3d296
  | 61 => 0x11516
  | 62 => 0x109d6
  | 63 => 0x9d316
  | 64 => 0x1309d6
  | 65 => 0x9c116
  | 66 => 0x1809d6
  | 67 => 0x14c
  | 68 => 0x112d6
  | 69 => 0x11696
  | 70 => 0x131696
  | 71 => 0x1a0c
  | 72 => 0x130116
  | 73 => 0x24116
  | 74 => 0x11456
  | 75 => 0x144116
  | 76 => 0x145316
  | 77 => 0x3c116
  | 78 => 0x15c116
  | 79 => 0xd4114
  | 80 => 0x25316
  | 81 => 0x3d316
  | 82 => 0x15d316
  | 83 => 0xd5314
  | 84 => 0x14b
  | 85 => 0xce
  | 86 => 0x170e
  | 87 => 0x10053
  | 88 => 0x241005e
  | 89 => 0x3c096
  | 90 => 0x4114
  | 91 => 0xd4054
  | 92 => 0xd5254
  | 93 => 0x10d54
  | 94 => 0x130d54
  | 95 => 0x115d6
  | 96 => 0x14113
  | 97 => 0x8116
  | 98 => 0x1315d6
  | 99 => 0x14053
  | 100 => 0x10153
  | 101 => 0x4113
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 72
  | 6 => 1574
  | 5 => 2738
  | 4 => 1086
  | 3 => 160
  | 2 => 21
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
  | 6 => packedAt gbK6 (64526+((h/524+packedAt gbK6 (58238+(h % 524)*12) 12) % 2284)*12) 12
  | 5 => packedAt gbK5 (142368+((h/912+packedAt gbK5 (131424+(h % 912)*12) 12) % 3614)*13) 13
  | 4 => packedAt gbK4 (68056+((h/362+packedAt gbK4 (64074+(h % 362)*11) 11) % 1304)*12) 12
  | 3 => packedAt gbK3 (11624+((h/53+packedAt gbK3 (11200+(h % 53)*8) 8) % 256)*9) 9
  | 2 => packedAt gbK2 (1736+((h/7+packedAt gbK2 (1701+(h % 7)*5) 5) % 28)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffffffc01fffffffffff800ff1fff8ff1fffc7
  | 1 => 0xffffffffe01fff803ffffffffe448fffe3c7ff
  | 2 => 0x1fe00fffffe03fffc03fffffff870f18fc78ff
  | 3 => 0xe0000fffffffc000003ffff00ff80fe0ff80f8
  | 4 => 0xfffffffffffffc000000ffff000ffff00
  | 5 => 0xfffff00000000000000000000fffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x696552c00962c5a9496581859099386b0d9bc3
  | 1 => 0xb2ba655960156a84358ab69aa64483b562c55d
  | 2 => 0x1cc309aabaa0337584335b2f4b870d18b468ae
  | 3 => 0xc80c4ef4dcd98019193c6dc18df80ee0df80f0
  | 4 => 0x10100f3f171e3c5e3e000e020f6ed000fb7600
  | 5 => 0x1f1f8038181020602020700c0ff7efde000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xeaaac888e8a8c080eaaac888e8a8c080eaaac888e8a8c080eaaac888e8a8c080eaaac888e8a8c080eaaac888e8a8c080eaaac888e8a8c080eaaac888e8a8c080, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15329
namespace PEqualNP.Outside.L_meta_15329
open PEqualNP.Outside.L_meta_15329.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_1_0 : Interval s0Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_1 : Interval s0Atlas 1 0 1 := bs0_1_0
theorem alls0 : ∀ k ≤ 1, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_1 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
theorem alls1 : ∀ k ≤ 2, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 10 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 13 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
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
theorem bgb_2_0 : Interval gbAtlas 2 0 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 21 := bgb_2_0
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
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_128 : Interval gbAtlas 3 128 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 160 := (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128)))
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
theorem bgb_4_928 : Interval gbAtlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_992 : Interval gbAtlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1024 : Interval gbAtlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1086 := (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 (concat bgb_4_480 bgb_4_512))))) (concat (concat (concat (concat bgb_4_544 bgb_4_576) (concat bgb_4_608 bgb_4_640)) (concat (concat bgb_4_672 bgb_4_704) (concat bgb_4_736 bgb_4_768))) (concat (concat (concat bgb_4_800 bgb_4_832) (concat bgb_4_864 bgb_4_896)) (concat (concat bgb_4_928 bgb_4_960) (concat bgb_4_992 (concat bgb_4_1024 bgb_4_1056))))))
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
theorem bgb_5_2720 : Interval gbAtlas 5 2720 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2738 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)))) (concat (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152))) (concat (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)) (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)))))) (concat (concat (concat (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504))) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664)))) (concat (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824))) (concat (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)) (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016))))) (concat (concat (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176))) (concat (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)))) (concat (concat (concat bgb_5_2400 bgb_5_2432) (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528))) (concat (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)) (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)))))))
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
theorem bgb_6_1568 : Interval gbAtlas 6 1568 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1574 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))) (concat (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344))) (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 2 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaaac888e8a8c080eaaac888e8a8c080eaaac888e8a8c080eaaac888e8a8c080eaaac888e8a8c080eaaac888e8a8c080eaaac888e8a8c080eaaac888e8a8c080
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 49 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 10 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 12 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3937061000 * 2 ^ 32 + 3903373440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15329.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,1]⟩,⟨.or,[2,5]⟩,⟨.and,[0,7]⟩,⟨.and,[4,8]⟩,⟨.and,[1,2]⟩,⟨.or,[6,9]⟩,⟨.and,[3,10]⟩,⟨.or,[4,7]⟩,⟨.and,[11,13]⟩,⟨.or,[12,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937061000 * 2 ^ 32 + 3903373440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937061000 * 2 ^ 32 + 3903373440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15329

open PEqualNP.Outside.L_meta_15329 in
theorem PEqualNP.Outside.L_meta_15329 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937061000 * 2 ^ 32 + 3903373440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937061000 * 2 ^ 32 + 3903373440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
