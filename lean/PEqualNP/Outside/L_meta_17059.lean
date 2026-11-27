import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_17059.Model
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


end PEqualNP.Outside.L_meta_17059.Model

namespace PEqualNP.Outside.L_meta_17059
open PEqualNP.Outside.L_meta_17059.Model
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

def SBf (j : Nat) : Nat := [7, 7, 7, 7, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_17059

namespace PEqualNP.Outside.L_meta_17059
open PEqualNP.Outside.L_meta_17059.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xa2e00026262100b080110746181210060a8e340009b000000000012802078f941e14e8324000000000c9100000244e34000002400018000160000e00020200002023400d0000101ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xe50171a000194e01b80144963800689a900001b200ada1b009860000b40284a740091000a00000001800000000000030003de0442fc0066a5400000143960038fbe000119066ec58074c5e9e00bd50000d8000000000000440005c00001009011c000000000011000304040000600082021000212000030020082bda8287785050edca421db54843bba8a85745150abca6215754c429faa2653c544caeea2995d14532bda826578504ca7ca8194f55032b7a92836c52506f4a020de540419f2a6633d54cc6dca598db54b319f2a4633d548c6f4a118de542319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502eca2205d544409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f209f2a4413d54882eca3105d546209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (731+((h/13+packedAt s0K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s0K4 (1875+((h/21+packedAt s0K4 (1728+(h % 21)*7) 7) % 122)*7) 7
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 2 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 3 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 4 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x309118a290425014a849d0930194d21886315c
  | 2 => 0x52922864129212816942528510a154a8b284c5
  | 3 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 4 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_17059
namespace PEqualNP.Outside.L_meta_17059
open PEqualNP.Outside.L_meta_17059.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x520029a2c30480221c8002a000201e4c00b306d431247c022560002d4cc000000856004a0000402011863c7579748504005c9c0001c0d50000000001a28c82380000700000800406101120010001ff43df43fe43fd43fc43dc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x26c4a641c80000680000002002789c5e99390c852941b8012a00000000021430f0fe5500098b807000008200000011023000000000269f9344e080707e874806d02003c1681e512180000834fa446a9d3c8ec0000001c44000308000000000000000002582c0015800001200000cc004c031448c03001462d1c000e80000000f8001524c000000001240324800981729000d2003b800007036800000000200000041000666f000000000001500000228c43c003d06800440000142000023400360000000000980000651f2288c0d2f000006b00000000044980d42c200448e052f8883000000003275001b800000e9b0009c0000116000000000000000000283b128e69e00000a06750000a6000200000000f9891c000580060000415800000000012003180090840000000000000000001200800002e9f400a40012d1e0000160747b070540000000005c5b00000000000000005921214ae0a0025c00001e80068000a002000200000000080004020001008020180400030281802050080c000000000020403804060401800000400000000001800060801800140503800020000d754b43af28e875d50d0ebca721db94843b6a90875e5410f3ca821f394843aea9087cd5210e9aa421d794443aea80879f43d0b3887a167d4f42ce29e853d5490abca7215754e42afa9a855c5350b3e86a16710d42cfa9a859c5350b5ea4a14f95042af298855d5310abca9995715332cfa16659d42ccabca39957543329f2a4653d548cabaa7196b50a32d6a12655e544cab8a89973d4932cfa1265ce424cb3a84997350932c6a12655c514cabea0994f950329eaa0655e530cabca7a0d754f41ce21e836e52d06daa5a0d794e41aea9c835f53506b8a6a0e710d419f2a4633d548c6bca918e7952318f2a4639d548c6b8a918d754a31cfa14639d428c6bca318d754231af2a0635c540c6baa418e7d0831cea10635e510c7aca218d7540319f2a6433d54c86bca790d754f21afa9c435c538875a8510d7d4d21ae29a433e540867aa810d794c21aea9843ad42086f4a010de54021af29c815d5390338872057d4d40ae29a815e53102baa6206710c40b7290816d52102eca2205d54440af2a6615c54cc2baa59867d0b30cea16615e51cc2baa7184fd51309e2a2619f544c2bca8985715130ce2a2611c544c2bea49867d0930cea12615c514c3b6a0985794c309f2a6413d54c82bca7905754f20d6a16415e53882baa7105794d20aea9a41ad424827ca8104f55020af298415d53082eca2105d54420afa9e215c53c42bca7085754e109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x3978c00008b54041713509801b000002c4400016685db9d28cca8614d922d5668e0b0800380000002300c40300a7948000e1080107dd3b4aa86b91e00c8200c8c0900481a70206043000414013020070402040120400000c39515210f0e6454843a358b53d0a9661d4f42a358853d0a1e64947328719150cca566195132a3592424ca4c6550932c3d95424cb0c6550932c3508514cb0d42d4132a358843d070c4354b41a3588435062d62952319358a548c68d6295231c398a548c61d6295231c358a548c60d629523187d97428c61f6550a3193588540c6596015031c3549420c61e649443187191500c61e64d4e21c3d4d428861e64d4d21c354d42087294254021a3588439028d6210c40c310d521031443544409358854cc30d5250b308799251cc22d621513087992544c24d6215130a3588544c30e621513087588544c30d621513083588544c21c65d093087195424c30d5350b2087191538821c6454d2095185534830d53509208799353c421c6454e10
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x2a00718120208060850282b8cc8a9087419c7655093281ae4322a018c0d729935348682b9086a8881035ca6494730818eca9a84905047154d4248206b94c9a9e21035c86454e10
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => packedAt s1K5 (912+((h/16+packedAt s1K5 (800+(h % 16)*7) 7) % 73)*7) 7
  | 4 => packedAt s1K4 (4950+((h/55+packedAt s1K4 (4455+(h % 55)*9) 9) % 316)*9) 9
  | 3 => packedAt s1K3 (2420+((h/20+packedAt s1K3 (2280+(h % 20)*7) 7) % 80)*7) 7
  | 2 => packedAt s1K2 (502+((h/3+packedAt s1K2 (490+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf0ffffe0fffc3fc1fe1f87fff0ffc1fe8cf3cf
  | 2 => 0xff07c3ff0fffc3fe1fe1f8707f0ffe1f734cf3
  | 3 => 0xfff803fff0fffc7fe001ff807ff1ffe1838f3c
  | 4 => 0x3ffff00007ffffe00007ffe0001fc0fc0
  | 5 => 0xfffffc000000007fffffffff80000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x10108022000840002202009110124044041145
  | 2 => 0x224104442450040a0c20882221049418314492
  | 3 => 0x44222a8842a220d4c11155044aa12981828a28
  | 4 => 0xeb5b312aa3aa967775444097cc80ccddc0fc0
  | 5 => 0x88c6221cccc332799999e64e08803111ebe000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0fafafaaafaa0faa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_17059
namespace PEqualNP.Outside.L_meta_17059
open PEqualNP.Outside.L_meta_17059.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x4a000000000000000000b0c00000000132400014000001083106d58000600000010100004cea30000629004000000009271a00287540000e0000f802c540000001019007049e2800b9a1e880000000000222808103041418000000020020000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x190e2a9ea88f02228311180c04801981800a8029088b1a0ca8071f8690970e8126002b130d80001b1c880000242d94ad12a20d25211a8fab80269d000000a5959b89000027a98b9885802c90001602a0800516a3839180002c1200000007801f270000230017802000000000001e1c1da18a06138994152a0424800a0810107321808e1a0000106009080600380121c216000850eb7290876d5210ebca6215754c42d6a10853e540ca7aa8195794f41aea9e836e52d06daa5a0db94a41b6a94835f53506b8a6a0d794631aea84633e540c67aa818db94831b6a90637a500c6f2a018e795031ceaa063ce520c79aa418d794431eb28863da500c6baa018f654031aca80633e54c867aa990d794f21aea9e433e548867aa910d7d4d21ae29a435e53902baa7205bd4940b6292815e53102baa6205b94840b6a90817651102eaa2204f953309eaa6616e52cc2daa5986795330ceaa661ce52cc39aa5985794730aea9c615c514c3b6a0985794c30af29c415d538827ea8904f151209f2a0413d54082bca6105754c20bb288417551082bea7885714f10af29c215d53843b261084fd51109e2a2215f53442b8a6885bd4910b629221d9304427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x6000008020ca0e0402c354d4210b0d5454831c6951500c7195454031d2949500c7495254031c355152cc258654c110
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (802+((h/14+packedAt s2K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s2K4 (2694+((h/30+packedAt s2K4 (2484+(h % 30)*7) 7) % 122)*8) 8
  | 3 => packedAt s2K3 (312+((h/2+packedAt s2K3 (304+(h % 2)*4) 4) % 16)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc7ffff83fe1fff07f0fe1fffc3f81ffe98f39f
  | 1 => 0xf81f0ffc3fff0ff87f0fe1c1fc3ffc1f674cf3
  | 3 => 0xffe00fffc01ff1ff800ffe01ffc01fe1878f1c
  | 4 => 0xfffffe001fffff00001ffffe001f80fe0
  | 5 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x40840088002200009010024480488488081185
  | 1 => 0x82421110940810282106208844124854234432
  | 3 => 0x114aaa218d54835b088b54116a815345858e18
  | 4 => 0x3594cc4a2906a595daa11025b3258189d80bc0
  | 5 => 0x261888733198c9e66ccd993822060211f6e000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88eeeeeeaaeeccaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_17059
namespace PEqualNP.Outside.L_meta_17059
open PEqualNP.Outside.L_meta_17059.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x6870a6cb1f002c00024814811eac02100545272291300509401946a84000000a131c3002d0061100061800200b0b900824e9e38680000c000018900c195040104ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x57000300000000212200404664672811070026702474710048610a59002a002c6e1a4b120030650c415142063600171e1018372335504f344e0b313800132e00022968000e1b0060580000003c3300001400001900726d0009000000003e000000004d01520066540f320056495500001508006c00004c1d6a00006b000000005b634500052f1f5c3d2553005a040d5e162b396f623a441c5f3b205d002700470000002d693f0000000073000000000000430000004a0000000101010108000203808000828081800181040486000080018005818000800004030281068100005b94b43b6a96877651d0eeaa3a1eb50842bb28885755110a7ca9194f55232bb28c6575518ca7aa920db94a41b6a94835f53506b8a6a0e7d4d41ce29a83b7515067ca820db94841b6a9083b541cc67ca918cf55231b7294636d528c67ca818cf55031b7290636d520c76a8218de94031bca8063af41c875a8390cf952219eaa4436d528876a8310d7d4d21ae29a43b5414879ea690f314d21f3a8a43af41487cc8290eb50521f2a0a43a541487ce6290f90c5219f2a0433d54086dca410d794e40aea9c816f52502d8a4a05794c40aea98816e52102daa4205d94440baa88819f41cc33a839873c8730e690e615d538c27ea8984f15130b7a92616c524c2eea2985d14530cfaa2619c544c39ea4987314930eba8a61d4514c33e82986750530e790a61cd214c3b6a0985794c30af29c415d538827ea8904f151209f2a0413d54082bca6105754c20bb2884175510827ca9884f55310b7296216d52c436a83887948710af29c215d53843b261086d50510f290a21d9304427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x16b12b8000a180008a0010002a81e30038201469802600088001c424043200001000c95095110b255250431cc505500c7145350521a959241486c46350521e1d8d41487846350521e1d4d41487845350521a959031486e1600c5219958452503854148730c5150514c344521453087195414c24c6548530e1505214c2356115120c954941c43255448710e450530443c1214c110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x1000b0a0cebb1a8290c8676d4d41486823aa8290a61811954148530
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s3K5 (826+((h/15+packedAt s3K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s3K4 (3471+((h/39+packedAt s3K4 (3159+(h % 39)*8) 8) % 187)*8) 8
  | 3 => packedAt s3K3 (960+((h/8+packedAt s3K3 (912+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s3K2 (199+((h/1+packedAt s3K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffff07fc3fff07870fffffc3f03ffe07f39f
  | 1 => 0xf03e1ff87ffe1ff807f1c3c1fc7ffc1f194cf3
  | 2 => 0xffc01fff803fe1fff801fc01ff803fe1e18f1c
  | 4 => 0x1fffffc001fffffe0001ffffc001fe0fe0
  | 5 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x11080110004400008102044480910488021185
  | 1 => 0x248532212a1131284290e2886424a855094432
  | 2 => 0x429554431aa9135b48816a116902b345618e18
  | 4 => 0xb288894500c449595240025924b0188b60bc0
  | 5 => 0x8c3110e6633199e666c9b338200c2211dde000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefeaaaaececa8a8fefeaaaaececa8a8fefeaaaaececa8a8fefeaaaaececa8a8fefeaaaaececa8a8fefeaaaaececa8a8fefeaaaaececa8a8fefeaaaaececa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_17059
namespace PEqualNP.Outside.L_meta_17059
open PEqualNP.Outside.L_meta_17059.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x7800a007c0000080a192a70000084c0270000000000000000000004800000000000012000000000380000000c4c88d01005c018461840b3a8402922155921a387800000b280000800360c02500095010100041040a0000a0200000ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21f621fd21f521fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe617d51cc3be6398774c730fb10e61f521cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461bf428c37a85185f94630bea8c61f6218c3ea43185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa9261ef524c2dea4985f14930f6292616c524c37e84986f50930ef99261dd324c2fea2987dd4530bba8a617c514c3e8a2985d14530ef98a61dd314c3ec42987d48530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6185f94830f7290616e520c2faa4187b54830b6a9061bf420c37a84185f94430fb2886176510c2faa2187d54430baa8861f6210c3ea42185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20dfa1641ee42c837a85907b50b20d6a1641ee32c83da65905f94720fb28e417651c82faa3907d54720baa8e41ef21c83ec43907b48720fa90e41e521c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5106fd0a20dea1441ef32883d865105f94620bea8c41f621883ea43105f94220fd18441f930883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20dfa1241ee424837a84907b50920d6a1241ee32483da64905fd4520be28a41ef21483ec42907b48520fa90a41e521483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea1041ef32083d864105f94420fb288417651082faa2107d54420baa8841f621083ea42105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43ec83887d50710fb18e21f531c43ec43887d48710bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10dfa1421bd42842faa3087dd0610fa20c21f731843e863087d88610fa90c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910dfa1221bd42443ec82887d50510fb18a21f531443ec42887d48510fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810bf28821f741043e882087dcc410fa18821f621043ea42085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd548c77aa918cf55231be2a4637d538c6fca518fb94a31b7294637d528c7daa518db54a31dfa1463bd428c6fca318fdd0631fa20c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a2637f524c6f8a498efd0931dea1263f7414c7e88298fdcc531ef18a637f504c6f8a098dfd5031bf2a0637d540c6f8a818df94c31bf290637d520c77e8418ef50831bf28863f6410c7ea8218f7cc431fb18863dd310c7ea6218df94031bea80637f54c86fca990ef953219f2a6437d54c877aa990cf55321be2a6437f53c86fca790df54f21be29e43bf42c87dc8590ef50b21f6a1643ad42c87de6590fb0cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21dea14437e51887ee8310fd90621faa0c43f441887ee6310fd8c621fa98c43f431887de4310fdc8621bf284437d50887eea910fd95221faaa443f454887eea710fd94e21faa9c43f453887ee8710fd90e21faa1c43f443886eaa510fdd0a21dba1443f642887ea8510ed50a21fa21443f732887ec6510fd4ca21fa19443f750887eca110fd54221fa284437f54486fca890df55121be2a2437f53486fca690df54d21be29a43bf42487dc8490ef50921f6a1243ad42487de6490fb0c921fba0a43f641487ea8290fd10521fb98a43f631487ea6290fd0c521fb90a43ee21486fea090df14121fbaa243f654487eaa890fd15121fba9a43f653487eaa690fd14d21fba1a43f643487ea8690fd10d21fba9243e752487ee8490edd0921fb21243e642487ea8490ed50921f2a1243a542487e88490fdcc921f399243f632487ea6490fd0c921f219243f750487eca090fd54121fa282437f54086fca810ef950219f2a0437d540877aa810cf55021be2a0437f53086fca610df54c21be298437e520877e8410ef50821bf288437651087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740fb10e81f521d02faa9205f94e40bea9c81be439037887205f94a40bea9481bf429037a85205f94640bea8c81be419037883207d88640fa90c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fb10a81f521503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206fd0840dea10817e51103eca2205d94440bea8881f551102eaa2206f90440de20881f621103ea42205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28
  | 2 => 0xe00800814000000000000020080180000201c0100800000008802010004050020060080002e00600c0000200a0080100003a0040100200a004018020000000000103203afca5a1fb94b43b7296877d52d0fdaa5a1db54b43bf28e87f651d0eeca3a1df54743faa8e877551d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321fd94643bb28c877d5190feaa321dd54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85be43d0b7a87a16f10f42bf28e857d51d0afca1a15f54342dfa9e85be53d0b7aa7a16f14f42dfa8e85be51d0b7aa3a16f14742dfa8685be50d0b7aa1a16f14342beaa4853d5490afca7215f54e42bf29485bf4290bde85215f94642fb28c85765190afaa3217d54642baa8c857e5090afaa1215fd4d42be29a85bf4350b7c86a16f50d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a16fd4d42df29a85bd5350b78a6a16fd4942d7a9285bf5150b7ca2a16f54542de28a85bf5050b7ca0a16f54142de282857e5410a7ca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2217d94442bb288857d5110beaa2215d54442bf280857d5010afea9995f95332beaa6657c54ccb7e85997b90b32dea1665ed42ccb5a85995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32bf29465bf428cb7a851977cca32f7994657e518cbeca3195d94632bea8c65f5518caeaa3195f94232bea84657f544cafca8995f55132be2a265bf424cb7a84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cafca4196fd0832f721065bd420cbda84196b50832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c83bf439077a8720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52107dca420db94841bea9083ed52106daa420efd0841dea10837e511077e8220fd90441dea0883f5411076a8220df94041bea80837f54cc6fca998ef953319f2a6637d54cc77aa998cf55331be2a6637e52cc6faa598efd0b31dea1663f641cc7ea8398df94331bea86637f548c6fca918ef952319f2a4637
  | 3 => 0x16f0000ac6ec000000000000001c000bbc00000000000002a2000838840001b67907b1ed070a9c000661a610800000000730000000000803eaf74e8cb00000000000000000000000001d867cd400000011a3186a23000094c0000000036419a711bc000000005762b8001b02600014c0004ac5892c26e0000000024b57400127800388000fe000000314002360000000000041e0000f83f326510ba800000bd9b50003dea380013f5820004d800000000000d858ab2852000662d512d000166000000005f800000024000000be8e064cd7c00000000000080000004040004e2fc0016389e5da000000002226cc861ac2a43d5b3a122986c5558fe00068ce7800000a20e980065c3e80000006c000cb8005d04519f800000810000000009dc0032b1a2748000746c427c7a13338e608aa80000003c003761f62400002800000128800118a10002b35208bd09800132980000000005740000000000000000000000e1ad90820000016552294800000000b08000006a62f400103108890dc8006100010d369000b68350c0000b5cef8001be514c3ad20006f40027e000000001780000000000026809c001423d841c661480000000009643a001403105020013e8000005c00026f000584000000ce6a19a3016cc00029986116001b292b000000000001ce0e58c0000b87b84aa281f22a58e023634b8c0000043c0013614b178cbc001e60009215aa936b05ad1c28762e7a07e10b02694126a4607acdc3033d0e65b83108006e4c88680e4f415ca731d6767e4f102b5fa5a497ad62b627524a3e1764091f8496d8a807f9fd0442c0c7ac80000011e19f2ec88cd10002b0000b600014e728b88033bc8e4d9229000674000000a4000000003f0000000001e60480003c000001a130a0006d42fb726224a1102865cc44800000000670001a1000dad68800000d397380000000045000002002000030000020040080500005003004000000008070040040480301000c0000000201c060070060000000000c004008000000080200000400c0000002a01c00007000008000060000000000000400c000010040000080301600000002000014000010000040000100600004001002000010000000040100403602c050000000100180502c00c03800006000000050000000180000400000005002010000000020080000201800800006008040010130000000100000800400000000004008030000200180300200401003012004008000040300480502000c000030000000300e00e000018070040000000f02c0080180000a00c000000000300081503e0040100100403402004002004020020000040280002001400801000000000040000000080f002014008050000000000400e0080100000a0040480300c05c000000000140000501400000001000008000040
  | 4 => 0xcf61600032000000034000340a02c56e2dd00012887979262000d486e0e03a55a3705520254a0894426601f245192a4839295134680e02b10d05dc0000038a9f194a076948505c2272a231000000000000000006540000031e282d000030900000000000368a1400377000a0dad800028000001f53b841118a5716e1eda22690fc0019e2e20000000030c27845c001aa0003206ba8c68cd452200018624c0012a1846dc0000000000091000596bed209643ec00096b5c000000000a8110121910460ba018002f1000d254d8c100000000000670000000000008cc00000000000000000000000020c00087c0028f000000000070000000013e00000013235000000001ad5e88197f0000183bd159a732c0c0bd8cd5723489232855ed347615a0005fc000000008a8fb80021c4f400275000060f48006c07c8278004f676c8a9d70009954581b3c0bd4001f40000015e00000080c559364beab800000000c905000022c0000011e4d6b40900006c2cc8000002e4c10e5800000805ab02c000be5a58be45a0598f80057eb840006f3f4a5c0b81e5aa341b400039244d7706c486718c281a642c18a68001e2b94b38b510ea256d8002bc4856323b4c449c000630104140001d01400000000000000000005fe00189ac040420582947000864002fa3f6000000d60009a09720b54ad8c00ab80009cd7594a2f897908b790b0000720003d40014d29d54c2192ca155c815400000000001969892acd90178000987211a0832e69e021a3d00023c708000000006a8000006318da103240015600000000000000000000000001743ad202b7000418c8900484a8d79800000c3400352000ce4772180ea000000000000003b800000000001ba3340009c00028c0002a34531c0a800000000001581e7000db4a4871000000f5b48080298000f8000001028004127441d1630004e4f080000000000222000000000004c800000000302820eb000000328df800234d3ce10f760e0018918359c6bc1d89161c0a40014357c95000000000c0c3495c1e499da62a40001e94fa32000000000006ea7640023a0002500033045c000c510900054c4100b532085238002a8620001f00b6be18c96a1b4b800289c0000000002e0082fca0000000000001f3238460a7851000134000006deb10ac800414000719da2c00018a0003fe001800000001d8e82c966c6aca8000554b34470000004280000000018400000000375128791d06940012964a970f8897000dcd74b20336d74f18000005b4560000006f000166000000e698b35c001ba19e14a00956aea0002d1af2a15d8284001be000999a1b15348000550000000000029623a0007e80062c00000000000001591263bacd400355000000000000000016f8a3436db8000650640d52500044cbc07801905a31d938ed00
  | 5 => 0x1001195385e825a2c36c248088ea3aa000001a60003709d3576b2000001995a62b4368470009a991acc5140c587a55000000880000002e4002f223e6102d2d426a000002370000000000002a0000015f000001ad29e0006e0001c1000000962724c61ad0e21731a1fc9b8006741f0000000000000028d236000510004982d8591250000006580010a600918001ca001b8800000640730002d0000000590f07513f8004ecb0c57995276000003470000015b26d6f0b3d2da822de338ba270088af5069ce000c08710980000012ea610009e4002d8682000ca1fe0000000033304a7940024e0000000000042c55c2285e00000154000
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x5200832d5448020d354d200836551480209ed95200835953480209b98854c426d62153108f99353c423d64d4f109b98b53c426d62d4f108f99253c423d6494f108f99252c423d6494b108f99052c423d6414b10cb94942c432d5250b10cd15141c42b5648c710b958a31c43655288710d9d4921c43a542487109798c548425d63152109b988548426d62152108fd91538423c6454e109bd89538426c6254e108f990538423d6414e109b988538426d6214e108f992528423d6494a108f990528423d6414a109798c528425d6314a10cb949428432d5250a10cdd5041842e56210610ad99331843665248610d954921843a542486108f58b544423e64951109dd85544426e62151109b588544423e6515110ab588544432e62151108f588544432d62151108b588544433561151108f992534423d6494d108fd91534423c6454d109bd89534426c6254d109dd85534423e64949108f592524427561949108fd91524423c645491097d8d524425c63549108f990524423d64149109d984524423e65d09108f197424423e65509108f195424432e5250910cb54942442766590510cd15241442746550510cd1514144276658c510ad5923144334548c510b958a3144274654c510cd15131443375488510cd15221442746548510cdd5121443345448510d9d4921443a54248510cd152104425e63d50109758f540426e62d50109b58b540423d65950108f58a540423f6255010cd185540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d5185530423e6414c108f590530425e6314c109b988530426d6214c109d984530423e64d48108f593520425e63d48109758f520423e64948108f592520426d6594810cb952520432d5494810d394e520434d5394810cb992520432d6494810d998652042756154810cb951520432d5454810d394d520434d5354810cb991520432d6454810d9985520423e64148108f590520425e63148109758c520426e62148109d984520423f65d08108f597420431e53d0810c754f420432e52d0810cb54b420423f65508108f595420431e5350810c754d420432e5250810cb549420427565d0410cd553410435553d0410d954b41042756510410cd55041043555310410b9588410436552104109d59731042b664cc410cd553310435553cc410d954b3104275650c410cd5503104355530c410d954831042756588410cd95221043355488410d594e21043555388410d954a21043365448410cd55121043565348410d554d21043665248410d954921043a54248410cd553100435553c4010d954b100427965840109dd9510042b46444010cd55110043555344010d9549100427b6544010
  | 1 => 0xc3355448430d9949210c3655248430e9509210c31d54cc030d354b300c35551cc030da54a300c25f654c030c7551300c34d524c030d5545300c27b654c030da549300c27661d53209d58754c832e62953209d98454c827561153208f99353c823d64d4f209d98753c827561d4f208f99053c823d6414f209d98453c82756114f20b958642c832e5450b20abd9542c832f6550b20cb94d42c832c5350b20ab59232c82e5618cb20cd95251c83355494720e950a51c83374294720cd50a51c832d4254720cd95151c83355454720e950951c83374254720d990951c83354254720d950951c83254254720ab59321c832d54c8720cd95221c83355488720e950a21c832d5448720d994521c83365448720cd55121c83a74248720e950921c82e76548720d9d9521c83675448720e995121c83655448720e955121c83255448720d994d21c836453487209dd85548827461552209798c548825d63152209d984548827561152208fd91538823c6454e209dd8553882746154e208f990538823d6414e209d98453882756114e20ba580328823f64546208f19151883a54248620ba18930883cb324c22097d8d544825c63551209dd85544827461551209d984544827561151208fd91534823c6454d209bd8953482776154d209d185534823e6414d208f59053482766114d209d58453482ad6490920b9586424826c6550920cbd95424832c6550920cb94d424832c5350920ead8142483a860509209b99632482ad648c920b9586324826c654c920cb50b514823e64145208f59051482ad64c8520b958a21483a54288520e9d0921483a54248520d9d5121483655448520d994d21483645348520f8d8121483e06048520ea50a30483e1218c1209e19530483a9424c120f24c930483e1214c120ea50b20483e121c81209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c20d3189530823e6414c208f590530825e6314c209b98853082766114c209d584530827a6014c208f992520823d64948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb949420826d65cc820cb553320834d53cc8209b594320832d540c820d354c32082e9600c820cd95251083355494420d594e51083555394420cdd0a51083354294420cd95151083355454420d594d51083555354420cdd0951083354254420d9cc9510836432544209d59621083365488420cd55221083565388420d554e21082776548420cd95121083355448420d594d21083555348420d994921083a54248420cb553200834d53c8020d9547200835953880209bd9
  | 2 => 0x5250840d594e51103555394440d994a511036552944409d58a51103374294440cd50a51103565354440d554d51103665254440d954951103364354440cd10d51102776254440cdd09511033542544408f596411031d5390440cb54a41103355190440c754c41102ad6210440cb548411033551104409dd9621102756588440d594e21103555388440d994a211036552884409dd9521102756548440d594d21103555348440d994921103655248440e9509211031d53d0040cb54b401033551d00408fd95401031d5350040cb54940102b46150040cd545401027b65500409d98754cc27561d53309b98a54cc26d62953309d98654cc2756195330b558643cc23e6494b308f59252cc2766194b309d58652cc38d42ccb308f99251cc23d64947309b98a51cc26d6294730a759331cc3a54248730f1cc921cc27761552309d185548c26e62152309b588548c27661152309d584548c23e6494a308f592528c2766194a309d586528c32e5250a30cb549428c23f64546308f191518c3665248630d9549218c3a542486308f58b544c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c31d63151308f588544c31c5490d30b5586434c25c6550d30cbd53524c32c54d4930cbd93524c32c64d4930d9d87524c36461d49308f990524c23d64149309d984524c2756114930cbd50524c32c5414930cb990524c32d6414930d9984524c3656114930da580524c23e65d09308f197424c32f52d0930cb14b424c23e65509308f195424c32f5250930cb149424c34c52cc930e350b324c33754d4530cd153514c36752d4530d914b514c27562d4530cdd0b514c33542d4530cdd50514c3345414530d9d48514c36452145309d588514c3374214530cd508514c29d64cc530d5147314c27665885309d196214c3375488530cd152214c3675288530d914a214c27665485309d195214c3375448530cd151214c3675248530d9149214c3a54248530f1cc9214c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c23f62550308f990540c25e63150309b988540c26d62150309d984540c27561150308f992520c23d64948309d986520c2756194830cb952520c32d5494830cb992520c32d6494830d9986520c3656194830cb951520c32d5454830cb991520c32d6454830d9985520c36561548308fd97420c23d65d0830cb94b420c32d52d08308fd95420c23d6550830cb949420c32d5250830cd952510c3355494430d994a510c36552944309d58a510c3374294430cd50a510c3365454430cd551510c3665254430d9549510c2776254430cdd09510c33542544309dd96210c2756588430cd952210c3355488430d994a210c36552884309dd95210c2756548430cd951210
  | 3 => 0x121cd55054486b664d4d21ad59353486b66494d21ad59253486e56294d21b9d8953487555314d219d997434867565d0d21b998b43486e562d0d219d99643486756590d21b9d8943486e46250d21b998843486e56210d21b959352486e663d4921b958352487a752d09219d99642486b56490921b999642487666590921b959242486a56490921b998e42486e56090921e9d8942487a75250921b999542486e46550921e9d9142487a75450921e915142486e46350921e9d0d42487a64350921e950d42487a44350921b9d8142487a76550921e999542487a56550921e919542487a76350921e998d42487a56350921e918d42487a75350921e994d42487a55350921e914d42487a76050921e998142487a56050921e918142486766510921ad99042486e66210921e950842487a742cc921e950b32486e665cc921b919732486e764cc921b959332487c753cc921f114f32486e560cc9219d99632486b6648c921ad59232486e6628c921e950a32487a5424c9219d99432486b6640c921ad59032487a7420c921e950832486f2600c921bc58032486e6650c921d999432486e7640c921e999032486e5640c921e959032486a5640c921b998c32487c6630c921f898032486e5600c921f858032486e1600c921e950b50487a54294121add9150486b46454121b5d8d50486d46354121e950950486b66414121ad59050486d66314121b558c50487a542141219d987540863d65950218f990540866e62150219d984540863e64d4c218f593530866e62d4c219d987530863e6414c218f59053086766114c219e98053086796014c218f992520863d64948218f597420863f6550821cb94942087374294421cd50a510872d54c8421cd952210873554884219bd95210872d5448421d994521086776548421cd95121087355448421e950921086766194f409d58653d02ad62d0f40ad58743d02766194b409d58652d032d52d0b40d994921d03655248740e950921d026f6254e409b18953902776154e409d18553902b66190e409d98652902756194a40cb949429032d5250a40ab58841903665248640d954921903a542486408f99743502ad62d0d40ad587435027661149409d584525032f52509409d58b515033742d4540cd50b515026e62145409b58851502e56214540cdd0c51503354314540d998851502756214540d958851502656214540cdd08515033542145408f997415033451d0540cd145415027665885409d196215027665485409d19521503a54248540cd146405023d6590c40c754e43102b66190c40c754c431027661948409d586521034e5394840d354e52103666194840d9586521034e5354840d354d521032e6454840cb90d521032c4354840d998552103656154840c794f421031d53d0840cb54b421031e5350840c754d421032e
  | 4 => 0x954941106b46050441cd505501066e62953319b58a54cc6ad6295331cb98a54cc63d6295331cb58a54cc62d6295331cd58654cc63f62553318f99252cc63d6494b318fd9742cc63d65d0b318fd9542cc63d6550b31cd95241cc73654507319b98b548c66d62d52318f58a548c63f6255231cd185548c66e62152319b588548c63e6494a318f592528c72e5494a31cb552528c72e6494a31cb592528c7666194a31cb951528c72d5454a31cb991528c72d6454a31d9985528c63f65d0a318f597428c72e52d0a31cb54b428c63f6550a318f595428c72e5250a31cb549428c73554d0631d954b418c7355410631b9588418c7655210631ad993318c73554cc631d954b318c66e62951319b58a544c67561951318f990524c63d6414931cbd49424c72c52509319d997414c6766510531cd550414c6e56210531ad993314c63e64141318f590504c66e62141319b588504c67661d50319b988540c66d62150319e980540c67960150318f992530c63d6494c318f992520c63d6494831cb949420c72d52508318f992510c63d64944319d596410c6776550431cd151410c6b5648c431b958a310c65f654c4319dd95310c63f64540318f191500c72e62953218f99353c863d64d4f218f99053c863d6414f219e98053c86796014f21cb95142c86af6550b21cbd9542c872e5350b21cb14d42c872d54ccb21ab59032c872d540cb21d354c32c86e9600cb21cb50950c865e63d52219758f548863e64d4e218f593538863e6494e218f59253887345450621cd55041886b664cc621ad59331886b6648c621ad5923188755530c621ad99321886b564c86218fd91508863c6454221b598f54886d563d5221b958b54887355415221b958854886b664d4e21ad59353886e562d4e21ad99253886b56494e21d554c53886e56214e219d997438867565d0e21b998b43886e562d0e219d99643886756590e21e9d8942887a542cca21ad99232886b5648ca21ad99032886b5640ca21e950832887c5320ca21bc98032886f1600ca21add9150886b46454221ad99050886b56414221b598c50886d563142219798e544865d63951218f993534863d64d4d218f992534863d6494d21ab59242486e661909219b195424872f6550921cb195424872e5350921cb14d42487a76150921e9185424866e65cc921ab59032486e6610c921ba580324867665d0521b998b41487a542d0521e950a41486746550521cd15141487a54250521cd55041486e66210521e9508414867665cc521ad99331486b564cc521e950b31486b6648c521ad59231486e6628c521e950a3148674654c521d514d31486e4624c521e950931487a5420c521ad99321486b564c8521e950b214872d42d41218f990504863d64141219798c504865d6314121b598e54486d56395121b958a54486e76255
  | 5 => 0x43d0b1d5310f429dd8550d0a746154342ab58b53d0ab661d4f42ad58753d0ab66194f42ad58653d0b1d5314f42ab58853d0a9e63d4742a758f51d0b355114742add8550d0ab46154342a798c50d0a9d6314342ad98450d0ab56114342cdd0a5190b3742546429d9875350a7561d4d42ab98b4350ab661d0d42ad5874350ab66190d42ad5864350b1c5350d42ab1894350ab66190942ad5864250a5e63141429758c5050a7661141429d5845050ab661d4d42ad5875350aad6294d42ad9865350ab56194d42abd895350b1d5314d42ab98f5250aad61d4942ab5835250a9e6394542a758e5150b355114542a7d8d5050a9c6354142add855050ab46154142a798c5050a9d6314142ad9845050ab561141428fd954210a6f6550842cb9514210b374294442cd50a5110b374254442d99095110b354254442d95095110a7661d53329d58754cca7661953329d58654ccae56190b32cbd9542ccb2c6550b32e3d8d42ccb8c6350b328f99251cca3d6494732cb50951cca3f64543328f19150ccb2d42543329dd8550cca7461543329d987548ca7561d52329d984548ca756115232cb553328cb365494632cd552518cb374294632cd50a518cb365454632cd551518cb374254632cd509518cb6732546329d987544ca7561d51329b58a544ca7661951329d586544ca3e64d45328f593514ca3e64141328f590504ca7661141329d584504ca7661d50329d587540ca7a60d50329e583540ca3d6595032cb98a540ca3e64150329d984540ca7561150329e980540ca7960150328f992520ca3d64948328f597420ca6d6590832ab592420cacd6390832b9586420ca3f6550832cb951420caaf6550832cbd95420cb2e5350832e350b320caad648c832b9586320ca5f654c832e3d09320ca6f654c832cd952510cb355494432e950a510cb374294432cd50a510cb2d4254432cd951510cb355454432e9509510cb374254432d9909510cb354254432d9509510cb254254432ce952500cb395494032ea50a500cb725194032dc546500cb3b4294032ce50a500cb2d4254032ce951500cb395454032ea509500cb725154032dc545500cb3b4254032da909500cb394254032da509500cb294254032d6cc9500cb6a3254032d64c9500cb693254032ad98643d072d52d0b41ab58b43906b561d0e41cb949429072d5250a419b98b535066d62d4d41ad986435063e6510d41cbd4942506b461509419798c505065d63141419b988505066d6214141ab58b43106b561d0c418fd9543107666194841cb991521072f4354841cb50d52107666154841cb54b42106b561d0841cb949421072d52d0441ad592411076552904418fd95411072d52504419dd9541107655250441add9541107376550441add8d41107365350441add8941107a65250441cd54941107a55250441c
  | 6 => 0xb1dfa10a2229999813124600029c02714a81521913e8f30001c00000da92a0eca498899f80d01972639f022f974a2128d86887203a000217a7619e02991185a0000ae0000fe01ea4e80000010aa0508c0cb8e68e70001be1031278001489870e983689711d84e8f91339baa4b27198498e1aba1300c2918f3a9b02115b09d80c9a080028180022c0618b625a939000211800000000080a1f0000fb04da9d03d9eda6100000000018500000013626509293a939a0c1d61780ae8ef14425600000100c0380080a0040040c00a0040780301a00001806002006000070330060041681400208c0002c00e028018010040000900e0160b4020120240040183901a0080300004c000020080000140001d006014008100020080501902e08800806004030008050000000180103601c038010180200700002e000090030020341b00500405c0380000e010128050040200700b00401c000010060080180200203006815002010000070060040000100001c0780600800000001056014000060000780000901201800015004000040050140c8108020160101600000802c0700701400003807002034000020040000a02202e0400d8080080100d00500c0000786507800c0180001c090018100140a800800000000008010400541f0060080001280107e0000c00300200c07800004034010000340140400000a00c040120180040381d00600c000000040280a80c0340000300101420802008000000008060060680200000601403015038000058180000080080b018008178160620000501500000c000090060b40480400a028008010020000080004400003004000014008000000540701103c02c0300800000000002002004008370000240200b006088028010000100200004a07c0000301e0000000a01c0140100800a01c0000d0080400c01200a0140800100c0001f0020040000d0000000200183b00000c0100900005c078010100e00300000400c1200701c0240600202e0200680204c0100480700c01c0000000c0100f80200c0000000400200401023000010060020120000000903e0080280a0000300900401400c000000040cc0e80700c0280f80100602800003000004038009d98652d0e756194b43d998652d0f656194b43cb99152d0f666154b43d958552d0f665294743d954a51d0e756294743d994951d0f6552547439dd8951d0ead62d0e43ad5874390e766194a439d5865290e6e62946439b58a5190ee56294643cdd0e5190f6662946439d58a5190f6562946439958a5190e776254643ad9864350e7661149439d5845250e6e62141439b5885050e7661141439d5845050ead62d0c43ad5874310e3f6550c4397d954310e7661948439d5865210e7761540439d1855010e766194f429d58653d0ab661d0f42ad58743d0ab66190f42ad586
  | 7 => 0x1b80c691e0001370360398b11eb1bf27da50266a4a82d1a00c51451991ed1ae8000b681a27797596100019013423222ca0e0000001348000a69530000e094e00000025480019195295b9378411268f6989a772618b7193800245264a7f19c8788a80600c625517689c2808000002249b89d88d09b0877a3723111e95fa7505e0930698478a28000de86d85f28c91b1cf97d1e90838fd98d8492470aa9b61d71ac12f1400ad2909cd12700010680b843a3187706a22d22b0b521e117a16063a688000c10708579b288496d02e0f785507f2981df1f503500014680024ba3b8a49fa9cd9a80001040b40a511409d0701ff10918d0e28001f312ea83a948000001a405d09a85b800000093a920db9cf12f8810bc2631be9520001cca4f16280013e00a8c0a271bf93d8bd9950749fe8422629499a71e693c025a6785026417e24f99d97628802c8ab1c8936a7b000219a7d26e0169a59dca4d90615918098117f0320241380a784c87a9ad26a80d84824096592b1fb25e2840179788230a624405b08014d9bd073a8887a1b310f02a15e1ab14d11022aa8f010a9b90ba1823f0a38170d31b914b8fc2721940ba1f58c40be83f22d8f71018a18a706d24904d0668761731211c280016da438aa1e383d0a21b40329668c797396808c996852a4d1ef2138e38158b30450bb80f26d813183a100e48221ec2990881ca24006f00000005481389682d90c8000fd0888e30ab9c587b2369651a61358991f72988541ca8e609e90a16083b8000d2823a2f15180012e20a0f609f9c21c1102a3d96998a07c0000e0094a1c01c2608000000cf00304499d0640dd0000000df1de9a1273a3a90fa9580400022281d00480000016f9da9f49a918e80014ca8f88300000023d0da1efa91065053a9ca7b80018b21b8001b520fa4e20607915700001616b0ec28c19ba3620c90380000025888a8fe9582001af1dba529078680e9082a7083306704084693b1fe21d2150e88319548628b5a6d1c323a28327023c8caa7a92180000014320b0a0a869550d6806a5097080021594f99f82921b1250a101b1c70f8950a570078002242810960000000001288001351da06213f0d1000285a9600017a2480d61c480020b80013880029d800221a0287b94b2861e518622e8ca00014905c2600f00f21b68000000000001bc0001c80ad9750bf08e8a02302039cba332791b9a5b8b91fc800a519008f5024a7e8001a39298000cc1b79161ae1108000900001b18000f282b1842378fba8a8d410e0268000001a49088000000000f0a7400001b8000000f115688185c8000bc8001b584995380000717d8678002428dc98890c00019b24580028b00025780000005da0d80006c1e30608d89d58000979a98102798b0a7c99992ba171318a889e0bd1300001aa8959c61f411f83022597
  | 8 => 0x9a8e1890a6b9ada2b81e04716e2660d81e000021c88210704595d0000c88370e582f1a31e78189fd25803b1e80d491c8e11eb96a1a89e58cd0999791bc80014396a81f8f1a538db09225b22e0e504e26e95d90e9dd88704283e11809b0f40852729cb06a9e49e9932a188312730c91159051eea5319a9292129d520691f09c88a0c2898019957912a289d00f98c980006c9830559f09bb8ef84a05092c0002899110001e880007812290d00015aa5428a28ba168599d80ea1ba05ea0f0000000000001e616e80007d18f1148a404c0d72558000000000c00b20001171719801e085929700b0190340020001e700006ea940000400489d90a994e93f93b9fd8ac95a16f1d481c8251200730faa82a1a0d1a4221f8cda418000000ce0b88002250001f6a01a758000000000728b79721d6944a352590ac01410227e04f9428001ff9ce000262239223a2311a12224888b11a9b20660ee8c59679fa235963a9385119f11c1882822058c80e813082183793200018207f8ff82094a0de1599bda008580859d7956028a3e89f033a399f784624105a9f8a8700006b97726919200fa3415888f0dda7a1c08000000530000000000918000eaa3488d2599b71f9a5f80000000100022829791899480195c00025ea381cc00000022680004f0589740cf80014c1f2a4a000238a208c382798ba339f3a5f2711b01c500002b9aa28d0a90b980000023e10119c1199d99dc247800000109856a65a890001a523f81482612826c9de28787407c80009a13a1481a1812a0a800189071a929f10ba9c99c1a0912d1ec876a0ea261928000181828ed1e204a80000018c80017b80000001114224c81180009b904a430630000d797e9c3a5120d27f9fb93d187a290eb0001d08000050000348b01bb00006f8000000af91900014780000026b25d17f8df98c00000380008e0fa000038a5c82a9661d30000000000002279e10b38b81728001d11910000000fc8228e4185996000181a74a1d8cea3c12a88f800168a1216498f80000011300021416b99e9c69511f900000000003c1d42040000c18520000000f800000010d8bf9a282e9459a20d204324c16ca6c04b80000001d83c9959d29d19f20121e18798690ed80592ca2a0090d99208af25c10598a9778be11b8c212380a0519b38441c78d580000014600000012400000002c12d8000000e21ee1230d90002968d521a90b094075967280140a7c20311d13c9db0571a6a900861711fc00d03f8989640f59558f4a788000000390000000001258659b125680025a0001138c70000b180015e9470000002099330002671af9ea000124a5200017c0000000000e78000001f18000ee169000035800190970115000179800089000009a6a0612010c48cc80000000028e1d383e8a30dc0c305f954198800000000002800000
  | 9 => 0x15011202f8ff1e284b06b1dd186a5d88b8b49080b280000020780017a808941864a3b1ea8082308001410d395f26f8bb02026822981f17c92620719302821126980001a8cb20887e2850911c40950a5800161800284a951ac94f086a6f1b49f621ea048000001601ce80615ca93208278116a44841a7683a9c921480e07d87e88400000ea8e9001d21978000308750eb800202163162000246a9a08786e03800019a00022016c08d8561a78712329e42
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x90c2e7694d42486923aa84a0a43295d2628c52194eeca146290ca574189314871232a8498a43c114d424c52194ae5326a690ca57498f5248653ba2c1a9243319ce6550921a4ceba1a8490e846350d42486c339ecaa1243615cf6550921b0ce732a8490d85739954248712b28caa1243499d76350921a4aebb1a8490d267598d4248692bacc6a1243a158c635092194ceda9a8490ca67694d4248652bb4a6a1243c154c5350921b0ee6b028490d847358142486933a8c0a1243619cc6050921b0ae63028490ca57499732486333aec99924329dd160cc921c4ccaa146490ca576d083248750a14c019243a8d09600c921d4284b006490ce170d903248652bb4c819243a8592600c921cc4cab006490ea2645803248750b22c019243b098d600c921d0ec6a12a090e84635095048653bb28428243a198d4214121d0ac6a10a090c657298653d0252b94c321c81495c65250a40a4ae5a18a2a0626745885150312ba2c428a8189d0d6214540c4a86b10a2a062562d085150312b128428a81495c851d0540a4ae428a82a0626655092150292b90a3202818554e6190c4094ae530c86205267190d5210292b8ca4a1081895894294440c1aa6b108220625625444110313b2a8490881c194d4248440e0aa6a124220615531854010252b90c2a00818954861500408cae530ea99846572185548c292b8ca4a14610b5c86454630a4ae9292431862764d87524c312b22c2292618a5916014930cc2c2b00a49852571149424c2863aa8599261895894214530a4ae42a2429852574149214c2933aa8490a61491d54248530c4ccaa12429862465509214c32232e6490a61895916194830c4ac8b0aa41852571949420c312b128528861495ca5448430a4ae9292421852775509210c292baa849086189d954248430c4acaa1242185257114d42c8292ba0a690e41495c46550920a4ae229a84905897318142482a239aa890a41495d05348520b82e6302429062865509304833032a42982418a551600c820c92a6b006410561700c95108292ba4a49084149dd54248420c4ecaa124210706535092108382a9a84908410b5ca6494f10a4ae42a28388627545884184252b94c998c21495d25248610c4ce2b10a888625715885444312b12c22a2210b5ca6494d10a4ae3292848842c76549424428639aa4a1221495c85490510a4ae42a28288435761523144292b90a918a2189151628c510a4ae42a26288525721522144292b90a890a21499d54248510a4ae42a42088525721855404292b8aa4a1021895516210410c8aa6b108208465765484104252b94c9988210ddd954cc410c2cc8a9e62086266454b3104292b94a890821495d25248410a4eeaa12420852575509210438329a8490821c154d424841094ae4322200843476551100430a322a688021891915244010
  | 1 => 0x100be4e00300f04a002740000589e40000468000030549e800001314000310c06400015b00000bc02a8400004b25c26de350a8ea006099436b73f09446766a33866b9529b160bd689c098bb109983e410181cf6b81b834bcca0718058841a33d12d33b8bd20c26a845b4450005906175f0880048590001832643607e0f10184928b5526914a25a8013e00002b0000000001306d00001c2cb398013ca0578f138812ba54d63a0f0f526635580118a6171884ed253a8c002b0000166002a8000000000b400926699c008608000e80800001b20014050007d000010e00020d800562130cb0005216d9800321fdac020009150002200000000000136515a00000dd27b24d00005388dcd02a165b8d71aa3c340b1d8e012714431cf8c52396896800331024152e2fc5291702380099001bc3a3e631495cad00070d2df4114c720026ae800004a215b6720000000000011886002e832020003802060180814000702c3201018000008000100406038000a05008340200028000404050080231128000a02008101401028040601040180a00090a40204030000205000040204060082600008280c000052572d0e5190f133a2c528c87895d16294643c4e86b14a321ca5729864350e32b90c2a8087295ca6194f4294ae331686a14a5711894350a52b94c3a9a85295c663d494294ee2b06a4a162542d8550ccb90a12a3280654add54254032e428528aa01972142545500caa4b9c84a8065585c64254032e1285992a019529748c9500cab0b8c64a8065c2d09325403294ae530c87a0ca5729864350686b9cc8a9083495c74354841a8ae730aa420e25525874210652b96c6a088389d895250441c4ecaa928220e26765494110713b1aa4a0883255cc605044194ae43028220e2552181411071338ac52a663895c56295331c4ac4b0ca998d257295241cc692b94a8a0e63495c86155231c4aa8b108318ca572993318c61bbb2a998c638999152cc631c4aa8b108298ca572993314c692b90a8a08634c5c0545043185ae4322a018d297014d42c8714aa2c0196439254d600cb21c4aa8b10a910ca5729925388750a12c019443b04c9600ca21a1ce7b2a84
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1a00808502866000080000c4ac0010000380000423a05839d16294643a05839d95250441c05735486050441a05839c562953318258799152cc631a05839d16214540c05535ca6190c40c05535c86150040a05839c5621511082587151628c510a058299153cc4108258799152cc410a05821915344010825871915244010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 227
  | 2 => 14
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (i*5) 5
  | 6 => packedAt s4K6 (i*16) 16
  | 5 => packedAt s4K5 (i*27) 27
  | 4 => packedAt s4K4 (i*38) 38
  | 3 => packedAt s4K3 (i*49) 49
  | 2 => packedAt s4K2 (i*60) 60
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (802+((h/14+packedAt s4K6 (704+(h % 14)*7) 7) % 90)*7) 7
  | 5 => packedAt s4K5 (27286+((h/296+packedAt s4K5 (24030+(h % 296)*11) 11) % 1421)*11) 11
  | 4 => packedAt s4K4 (55826+((h/446+packedAt s4K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s4K3 (11798+((h/75+packedAt s4K3 (11123+(h % 75)*9) 9) % 300)*9) 9
  | 2 => packedAt s4K2 (860+((h/4+packedAt s4K2 (840+(h % 4)*5) 5) % 30)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3ffffff0f87ffff830e1ffffe1c1ffff03f0ff
  | 1 => 0xc3c3e1ff0078f0ffc0fe38787e01c78f9d4c93
  | 2 => 0x3fc01ffff80ff0fff003f807ffe07f0e18f1c
  | 3 => 0xfc0001ffffff000fffffc0007ffff800fe0fe0
  | 5 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x400010008000000000408800404080001025
  | 1 => 0x9898d32235316989c8721c51720c952e8d4c92
  | 2 => 0xa10955445412889a59102d4234940662a18518
  | 3 => 0x8228888a0402224a2a4800449293004560ac0
  | 5 => 0x3233110ec664cccf3cd9366710302448fbe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfeaafeaafaa8faa8feaafeaafaa8faa8feaafeaafaa8faa8feaafeaafaa8faa8feaafeaafaa8faa8feaafeaafaa8faa8feaafeaafaa8faa8feaafeaafaa8faa8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_17059
namespace PEqualNP.Outside.L_meta_17059
open PEqualNP.Outside.L_meta_17059.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x388000a1ea0c25004008e0058000268400d362c1064e009290e10a2a4c68f1522011800a2159744252003a7cc8c0604000608002404d240040ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xdd550000008818e8500000011564e40000005400000000013c0000994c000034011c4cf4004150012cd9100044fc00000000000000d40080300038ad3548009cecc128cc5804000121596000000000680168009400000000f0b86400000000007000200000000104000000004828011800006cf94400910800015c0010140000742d241c60d0e1310cb03c008c007c00a45c0024000000c8000000080000000001400000000000000000a00cb538a80000840000000000000078000000c4bc00020800060c0204000004040a04000002000000020e0404000000020205765190eeaa321dd94642baa8c853e540ca7aa819734c832bb2886575510caf4a0195e540329f28c833d50906bca620d754c41b7290836d52106f4a020de54041cf298839d531075ca420eb548419f28883b65110774a020cf54041dca808339501067ca998cf55331b7294636d528c7688318cfd51319e2a263b4414c67ca990cf55321af29c435d53887688310cfd51219e2a243b4414867ca3a04f55240bba8a8174515036ea2a04f14540da28a81345150376a0a04f950409f2a4613d548c2dea4985b149309f2a0613d540c2dca4185b54830bb2886175510c27ca9104f55220afa9a415c534827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f55210da20c21b9408427ea8884f15110dca02213e540427aa8085794c10aea98216e52042daa4086d10410
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xb0e72e006c0c00081a0000148a4212a80616a0a98401e09000200004504327493254032c354d521071a5354041c654d501072a5254041ca54950107255210631ac580418c6b16010531c554c41886b16010621ac58041487166314540c558c51503266214540c9588515033160145408d185548c2346155220ac58041842b061502108e19540442356510410c554c41043255210410
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xc0840000101885496010631c22a6b008310e05635885150308b1ac028a81885896014540
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s5K4 (2697+((h/30+packedAt s5K4 (2457+(h % 30)*8) 8) % 193)*8) 8
  | 3 => packedAt s5K3 (998+((h/8+packedAt s5K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (249+((h/1+packedAt s5K2 (245+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1fe3c7e3fffe1c71f8fc0c707fffe19c0ff
  | 1 => 0xf1fe3fff803c78fe07e3f1fff8070e1e667c93
  | 2 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 3 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 4 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4028004410502000420502480101429008c025
  | 1 => 0x24448c080c88910601209086c832244c221c92
  | 2 => 0xa88094912409402a8802a41252500944870518
  | 3 => 0x41529224820125515480024a4a4a009700ac0
  | 4 => 0xc919300371326499e693493800c0c191dde000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_17059
namespace PEqualNP.Outside.L_meta_17059
open PEqualNP.Outside.L_meta_17059.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x13154f12987a317912001c2c00d40000001ca2128d2006c0402b402c02836190b06e21a2e3a505334c1c93b06007322e00fad2c9ccba00702801a68f042a3c980520664f011830000240cc000c081800c00a0002ffd500bfe5402ff5500bfc54037fd4c09fe53007f54c09fc5302ffd0c09fe4302ff50c09fc43037fd4807fe52007f54807fc5202ffd0807fe4202ff50807fc42027fcc807fe32007f4c807fc32037fd4405fe51007f54405fc5102ffd0405fe4102ff50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd4003fe50007f54003fc5002ffd000bbf4000ff9000bfd40006f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826001fe0c13000ffe4098007fe204c003fd1026001ff0813000ffe2098007fe104c003fe0826000ffd9520005feca9003bfe654800d7f32a4000ff59520005faca9003bfc654800d7e32a400dffd912006dfec890037fe644800b7f322400dff5912006dfac890037fc644800b7e322400dffd512006ffca890037fd544801bfe2a24000ffd8d20005fec690033fe63480097f31a4000ff58d20005fac690033fc63480097e31a400effd4d20067fca690003fd5348019fe29a400dffd0d20067fc8690037fd4348019fe21a4001bfd892001ffea49000ffe5248007f72924003ff54920007daa49000ffc5248007ffa124003ff9092001ffa849000ffc4248007ff9924003ff8c92001fdc649000ffd3248001f69924003ff0c920007fec290002ff6148017ff30a4002bf98520007fac29002ffc61480057e30a400effd452005ffca290003fd5148017fe28a400dffd052005ffc8290037fd4148017fe20a400cffcc52005ffc6290003fd3148017fe18a4003ffc852001fde429000ffe2148007fe90a4000fb4852001ff84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001efd012000ffc8090007fd4048003dea024001ff1012000ffe6090007fe3048003fd1824001ff4c120007f26090007fc3048003ff9024003fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007ff1048003ff0824001ff04120007feca88002ff6544015ff32a2006bf99510007faca88002fd6544015fe32a2006bf1951003ffec88801eff644400fff3222005bf9911003ffac88801efd644400ffe3222005bf1911003ffea88801ffe544400ffeaa22007ff15110007fec688002ff6344013ff31a2004bf98d10007fac688002fd6344013fe31a2004bf18d10057fea688027fe5344001fea9a2009ff14d1003ffe8688027fe434400ffea1a2009ff10d10007fec488002ff6244011ff3122003bf98910007fac488002fd6244011fe3122003bf18910057fea488023fe5244001fea922008ff1491003ffe8488023fe424400ffea122008ff1091004ffe6488023fe3244001fe9922008ff0c91000dfec28800bff5144005ff28a2002fd94510017faa288003f55144005fe28a2002ffd0510017fc828800bfd4144005fe20a2002ffcc510017fc628800bf63144005fe98a2000fd4c510017f8628800bff2144005ff10a2002fd88510017fa4288003f52144005fe10a2001bfd811000ffea088007fe5044003fea822001ff1411000ffe8088007bf4044003ff2022001fe9011000ffa8088007bd404400ffca022000ee5011000ff88088007ff3044003ff1822001ff4c11000ff86088007ff2044003ff1022001ff4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x7fe4354035fea1aa019ff10d50007fec4a8002ff6254031ff312a003bf98950007fac4a8063fc62540077e312a006ffd4950036fea4a801bfe525400dfea92a000df54950037f8a4a806bff4254031ff212a01aff509500c7f884a8067ff3254031ff192a000ff4c9500c7f864a8003ff61540017fb0aa017ff98550015fcc2a8003fd615402ffe30aa002bf18550037fea2a801b7f515400dff28aa006ff54550006faa2a801bfc5154035ffa0aa017ff905500d7fa82a805ffc4154033ff98aa017ff8c550007fa62a805ffc3154031ff90aa017ff88550007fa42a805ffc21540037fb02a001ffd4150037f6a0a8007fe5054003bf282a001ff1415000ef8a0a8007f85054003ffa02a001efd015000ffc80a8007fd4054003fe202a001ffcc15000ffc60a8007fc3054003ff902a001ff8815000ff840a8007ff1054003ff082a001ff041500077ecaa005bbe6550001deb2a8016ef195400077ec6a0057be6350001deb1a8015ef18d400b77ea6a0057be5350001dea9a8015ef14d400077ec4a0053be6250001deb128014ef189400b77ea4a0053be5250001dea928014ef149400af7e64a0053be3250001de9928014ef0c9400077ec2a004fbe6150001deb0a8013ef185400b77ea2a004fbe5150001dea8a8013ef145400af7e62a004fbe3150001de98a8013ef0c5400a77e42a004fbe2150001de90a8013ef0854000f7ec0a0006bf605000bddb028001efd414000f7ca0a0007bd5050003de2828001efcc14000f7c60a0007bc3050003df9028001ef8814000f7840a0007bf1050003df0828001ee8414000f7820a0003ff654c0017fb2a6012ff99530035fcca98003fd654c0017eb2a6012ff19530035f8ca98047ff644c0237fb226011ff9913002dfcc898047fd644c0237eb226011ff1913002df8c898047ff544c023ff2a26011ff5513008ff8a898006ff634c009ffa9a6004ff94d30027bca698013fd534c001eea9a6004ff14d30027fe8698013fe434c009fea1a6004ff10d30007fec498002ff624c021ff3126003bf98930007fac498043fc624c0077e3126012ffd4930087fca498003fd524c021fe2926011ffd0930087fc8498047fd424c021fe2126004ffcc930027be6498013fe324c009fe9926000f74c930027f86498003ff614c0017fb0a600fff98530015fcc298003fd614c01ffe30a6002bf18530097fea29803ffe514c001fea8a600fff1453008ffe829803ffe414c023fea0a600fff10530027fe6298013df314c009ff18a6004ff4c530007ba6298013fc314c021ff90a600fff88530007fa429803ffc214c0037fb026001ffd413000ffca098007fd504c003fe2826001ffd013000f7e8098007fe404c003fea026001ef5013000ff88098007ff304c009fd9826001ff8c13000fbc6098007fc304c003ee1
  | 2 => 0x3110dfac898887fc644c40b7e3226221ffd513110ffca898887fd544c443fe2a26202bfd8d31027fea698813fe534c409fea9a6204ff14d31027fe8698813fe434c409ef21a6204ff50d3110fba8698813fc434c401ffb126200bfd8931107fcc49880efe624c401feb126220ff1893101df8c49888bff524c441ff2926200ff54931107f8a498887ff424c441ff2126221ff50931107f88498813ff324c409ff1926204ff4c931027f8649880aff614c405ffa8a6202ff94531017faa29880bfc514c405ffa0a6202ff90531017fa829880bfc414c405ff98a6204fdcc531017fc629880bde314c405fe18a6202f70c531017e8629880bff214c405ff10a6202fd88531017f84298803ff604c4017fb02621fff9813100dfcc098803fd604c43ffe3026201bf18131117fea09887ffe504c43ffe2826221ffd013110f7e809887ffe404c443fea02621fff10131027fe6098813df304c409ff1826204ff0c131107fe409887ffe204c43ffe1026202ffc4131017ee209880bfe104c405fe0826200ffd9521005feca9087bfe654840d7f32a4200ff59521005faca9087bfc654840d7e32a421dffd91210edfec890803bf64484015fb22421dff9912102dfcc890877fd644843b7eb22421dff1912102df8c890877bc644840b5e322421dffd51210effca890877fd544843bfe2a24200ffd8d21005fec690873fe63484097f31a4200ff58d21005fac690873fc63484097e31a421effd4d210e7fca690803fd5348439fe29a421dffd0d210e7fc8690877fd4348439fe21a4202bfd892101ffea49080ffe5248407f72924203ff54921007daa49080ffc5248407ffa124203ff9092101fdc849080ffd424843bf6a124203ff1092101ffe6490873ef3248407ff1924203ff4c92101ff8649080fec32484057fb0a4202ffd4521017fca29080bf65148405fea8a4200fd54521017f8a29080bff414843bfba0a4202ff90521017fa829080bfc4148405fa20a4202ffcc521017fc629080bf63148405fe98a4200fd4c521017f8629080bff2148407fb90a4202ff88521017dc429080bfc2148405f610a4202fd08521007fec090802ff6048437ff3024201bf98121007fac09086ffc60484037e302421effd41210dffca09086ffc504843bffa02421defd01210dffc8090877fd4048437fe202421cffcc1210dffc609086ffc3048407ff9024203fbc812101ffc409080ffc2048405ff8824202fdc4121017fc209080bfc10484037fb2aa01affd91500d5fec8a806bfe645400b7f322a01aff591500d5fac8a806bfc645400b7e322a006ffd5150037fca8a801bfd545400dfe2a2a000ffd8d50005fec6a8067fe63540097f31aa000ff58d500cff8c6a8012fc635400dffa9aa006dfd4d50037fca6a801bfd5354001bea9aa006ff14d500d7fe86a806
  | 3 => 0xfa02a42eefd015215ffc80a90bbfd4054857fe202a42dffcc15215ffc60a90affc3054807ff902a403fbc815201ffc40a900ffc2054859ff882a42bff8415215ff820a9003ff654c8017fb2a642aff99532035fcca99003fd654c8017eb2a642aff19532035f8ca990a7ff644c8537fb226429ff9913202dfcc8990a7fd644c8537eb226429ff1913202df8c8990a7ff544c853ff2a26429ff5513214ff8a89900eff634c809ffa9a6404ff94d32027faa699013fc534c809ffa1a6404ff90d32027fa8699013fc434c8077fb126403ffd493201ffca49900ffd524c807fe2926403ffd093201ffc849900ffd424c807fe2126403ffcc932027de649900ffe324c807ef1926403ff0c93201fb8649900fec324c807e61926400ffd8532005fec2990a3fe614c8057f30a6400ff58532147f8c29900afc614c855ffa8a6428ff94532147f8a2990a7ff414c851ff20a6429ff50532147f88299013ff314c809ff18a6404ff0c53201ffe429900ffe214c807fe10a6400ffd8132005fec09909ffe604c8037f3026400ff5813213ff8c099006fc604c855ffa826427ff9413213ff8a0990a7ff404c853dfa026427ff9013214ffa809909ffc404c809ff9826404f7cc132027fc6099013fc304c807ff9026403fbc813201ffc409900ffc204c851ff8826427ff8413213ff8209900aff655444dffb22a226bfd91510077ec8a8802bf645444dff322a205bf99151137fac8a889afd645444dfe322a205bf1915113778c8a8816bc645440dffaa2a206dfd5151037fca8a881bfd545444dbeaa2a206ff15151007fec6a8802ff635444bff31aa204bf98d51007fac6a8897fc63544097e31aa206ffd4d51037fca6a88977e535440dfea9aa206ff14d51036f8a6a889bff435444bff21aa226ff50d5112ff886a8803ff62544017fb12a224ff9895101dfcc4a8803fd6254449fe312a203bf18951037fea4a881b7f525440dff292a206ff54951006faa4a881bfc525444dffa12a224ff90951137fa84a8893fc425444bff992a224ff8c951007fa64a8893fc32544057fb0aa202ffd4551037eea2a880bfe5154405bf28aa202ff14551016f8a2a880bf45154405ffa0aa202ff90551017fa82a880bfc4154405ff98aa202ff8c551017f862a880bff2154405ff10aa202fd88551017f842a8803ff60544017fb02a223ff9815100dfcc0a8803fd6054447fe302a201bf18151037fea0a881b7f505440dff282a206ff14151137fe80a889bbf4054447ff202a226ff5015111ff880a8897ff3054447ff182a223ff0c151127fe40a888ffe2054447fe102a202ffc4151017ee20a880bfe1054405fe082a200ffd9531005feca9888bfe654c40d7f32a6200ff59531005faca9888bfc654c40d7e32a6221ffd913110dfec898887fe644c40b7f3226221ff591
  | 4 => 0x600000000600000c00200400400400200c01400400000200800000000600200e00200400400000600200200600000600000800400000200200000400000600800000000200200000000000000000000000000400200200000000000600000400200200600000200000200a00400600200c00200000600000000000002200200a00400200000200001000400200000200400000000000000000800c00000200600000800400600800000600000200a00000200000000000000000200000000000600000000200200000000000c01200000400200604bfd9553197fec8a98caff6454c65ff322a605bf99153197fac8a98cafd6454c65fe322a605bf19153037fea8a981b7f5454c0dff2a2a606ff55153196faa8a981bfc5454c097fb1aa604ffd4d53037bea6a9813fe5354c09bf29aa604ff14d53026f8a6a9813dc5354c09ffa1aa604ff90d53027bc86a9813fd4354c65eea1aa604ff10d53007fec4a9802ff6254c63ff312a603bf98953007fac4a98c7fc6254c077e312a606ffd4953036fea4a981bfe5254c0dfe292a632ffd095318ffc84a98cbfd4254c63fe212a604ffcc953027fc64a9813fc3254c01ffb0aa600bfd8553187fcc2a980afe6154c01feb0aa630ff18553015f8c2a981bff5154c0dff28aa630df94553037f8a2a981b7c5154c65ffa0aa630ff90553197fa82a98c3fc4154c09ff98aa604ff8c553027f862a98c7ff2154c61ff10aa630ff08553007fec0a9802ff6054c5fff302a601bf98153007fac0a98bffc6054c037e302a606ffd4153036fea0a981bfe5054c0dfe282a632ffd01531977e80a98bffe4054c65fea02a62fff10153027fe60a9813df3054c09ff182a604ff0c15318ffe40a98bffe2054c5ffe102a630ffc415317ffc20a98bffc1054c077fb2aa42effd9152175fec8a90bbfe645480b7f322a42eff59152175fac8a90bbfc645480b7e322a406ffd5152037fca8a90bb7e545480dfeaa2a406ff15152036f8a8a9003ff63548017fb1aa42dff98d52025fcc6a9003fd635485bfe31aa404bf18d52037fea6a901b7f535480dff29aa406ff54d52006faa6a901bfc535485dffa1aa42dff90d52177fa86a90b7fc43548077fb12a403ffd4952037dea4a900ffe5254807bf292a403ff1495201ef8a4a900fec5254807ffa12a403ff9095201ffa84a900ffc4254807ff992a403ff8c95201ff864a9003ff61548017fb0aa42cff98552015fcc2a9003fd6154859fe30aa402bf18552037fea2a901b7f515480dff28aa406ff14552177fe82a90b3fe415485dfea0aa42cff1055216ffe62a90b3fe3154859fe18aa403ffc855201fde42a900ffe2154807fe10aa400ffd8152005fec0a90affe60548037f302a400ff5815215ff8c0a9006fc605480dffa82a406dfd4152037fca0a901bfc505485df
  | 5 => 0x58e38234000000000af800009c4209ec0003cc224fb8b64000000000e706702445586d08ec0008b4000000848000dac00088c0000000000000003280000007640000000008a0e90000000000874b1c0002740000005e4000fc80006390608e4fb4000000770000000000a1c7f41c862cdd4c44000c146484c4000000021014000a70b98ca092c000830dbc000c789949a8210f047e41e4d70d64af027c0e457ccac1601380003746840004c817c23cdd0018dc0bd8000000000000000fc4000d94e80bd4120520000000000000000078ed44f40007d00003ec4e4df4000064000fe0000cdc000000000000e54000618000000b847000000000000007e83947840d43d8de0f6018100c6400004e8c70094000000f1c59c0000000005b43009588b0000000000000e14000000001068000778ca40001d07a4db400099c3047442dc29c0000004acbb00840000000000000001b8860000000710390000000000e200000000005b00000002c400009800000003c0004b00000000002f096c00000000000020cae80000000000007f00000002200008940006a04885ac6fca9472400076000002c3f00002888445d84a4000734b44238000000b2c000d08000000d40d4c0f4e8c6e00009e074c0000008e0a44ddca38c34920eb8cd10501a00003fccd4ae014ca04228001028d28a10000e1898cc40d60a180140008800a07e0c80b60c28000000690dec0004f0000aa81f063c2f40000000010105c4000000318000000000000000000000910000000b7c4a00003f887c9d0e78000fe4144be46300008d01d8ff0b34000a6800101c0003200007cc000190000834a7cacc0000002b0000000000000000c9800012c3400905f4984768000000ab4268d24000f9c000e6cee0000eb40000000000008c8ab8000000c58da4000940000000240ac85e8d848fcb68128624e9815c0800004300ccdb00000000008c00000000006b4000000a0c85c00000000200000000400200200400200a00000c00000c00000000400000000a00200200200600000400000001600400200000200800000000000000000200a00001400c00400200000000200000000000400200200600602600000400200000000200000000201400600000400800801c00000800000800a00200001600000000a00800000e00000200200c00000a00200000000400000000000e00001600800200000600c00400000000001200200000600400a00000200000000000c00600800400000600000600800601000000000400600000200600000400000000602400801200000000200800800200200000000000000000200000600200000400000200400600200e00600000e00000000000800a00400800400000200600000800001000a00000c00200a010000000000000000000000000004004000002
  | 6 => 0x46cf38d000002fc6200007fc0000009d8c1c5d44d8bf80000000000000000000000000000007bc000000d88001090c74000918c3108417895c0e00700000001e00ec89cee4000e3400000000000000000000000000000043849103449cffc35c0005902ec000d5c0000004bc00000000000c154bb85780000000002e00004700a80000007b4000000c880000010304fc70c3482c845ce4c00107c3a84c0000000000a6400000000000000000000000065c000000000000fdc000000000000000000424e640000000000003d000056087060cb240007acf24000704000298000bdc000000000ec80000002a4de4e480006e4000000da000000053c000d441043140003c0884000000a3d06cdfc000000000000ac0d2c570000a208acd90a0800000040024840c000000ecc38c00000000000000000000000000069c31c338f8811c6a800000000000000010cce461c00033c404410554758740000378264fd8d04ef4000000000fa09e89dcd10588148000000000ccd08800013064c0005144480001dccfc000f7c9c8000000000f680004dc000b6c5c8bb4000d74f48000b30408beccb0a5cefca8ce849ac00000037cff819c4e03dcf10000000000ebcf548500000000010800001400008dc00800000076c000e9c000000530000b4000000000100800000000000000000086c00026c000000000000000000000000000000000000000ae4000000000000000000e68000000794000f800000002d4000000be8e7459800090c000000b3800047c0000000e907815877c0000000000000000000000000240008cc000000000000000000000d48780000000790000a740000fc000478e24858a000000000000001b00000000000000006f0000000000000bcc0004548c442800000000005cd80000000000000000000000000000000000d38000360370035044b54a30000000000000000fcc4589086780000000006800000000000000000380000585d0000b88000adc0000000002a00f00006f4a985c07740008240004a87dc1cc000000000960c2c974000000000000bf0c08000914000b287f82bc000000000000000fa41147143c4000000000000000000c8c0000000001aca584cc000668000f6441c2040000046a40003e8000000000b3cf7835084c5e0f14000f440000000001e800002800008c0004d0000000d0c6c0000ea800007c9e43f48f4b8c000c3c1ec6c400079c3982009280a40000000000002a800044d004000d20a845a40006049f85503a40006dc7ec8d400056c000000c20bc000000095048c5ec000000000000ba0000d9cbc8c682e8720000000000000000000000000000e40eac5f060055cfacc4c000000ee86ac00106493400102c000c180000000003b8000000068c5400000000094cec0c641d4d1493cb
  | 7 => 0x434c38280c040000001500009244408f000058c24c000000000000000000000730000074000fec0000003347b8000000000000000000000000f2800000000052c7d4c10258d583e4b94bfc634ea4000a500001fc8e8fb1000c9cb5cbbcaec50c2b8be000000000068c00105caa02086500009985108280009a0000b9cbd0988000000ea0f509647b0000810978cf0580718cb40008089cc0000000009b0660100f34e60000f740005fc000fc0c900000000000006b8000000f3c000864b80e7cb4c9fcf4cda821c6101bcff40009bc000000484c601180006c8788000948d1c28c1080000000000000000009f4c6c000000000050000000954614f5c1c0d7cef00000b8000504000b040000000005400000b00000007c000104c000000000534000a88628460abc000000000fd07a90247c4e10000000000000000000000000480f2c000000000c94198000e5cf8c04c67cbace2897c000000464000000000888000000ab000080c000000f981840008bc22c000000000000000000000000568000b706d4524000674000a54000000354048dcc000000000898000e8800051c000820000000000000000dd8000000000000000000000000000250548000b14000000000000000000000000134000a9c0000000000002c00000000b40002b4000f5816800000000042c0000001f8000e948b800000081c00043c000000f90000000000000804688000e04368ce8000608000000654e44c7c0c8000000000000000000000ba84506d8000000d6800000041434c1f4001074498000b78cb80009b41a4f7071c000d98ec4fbcf6c0005f80005a83a00000003b40001645644f8ba4418000528000b000c4000c5c380000ce000083c0002d800000025400000094400000030c000000518fe8b51058389048edc00004439c0004449007a00005ccf2011075c7482e4001020aa4000000e0c9045740010382601a81940000000000005440000000000000000400006b00000000006f8000658000000000000f08bf4a6c72c0dc000218000000000000000000000000d3ce2c000538000000000cbc000000a34d6cd543089b836c25c06ca24000a4c97066c010738b08ed83c80002f8000000000324dc8df8b48cf40003bcc0c000750b20e580003e0f84270cc40000000000000000009c400000000036400018c000508000000594818000000000000000f40728000664000000cd8890000000000584000000ac4000000878754b7427903c000000a14294d50000000cc0000ad0a48a40f309c0000000b900000000300008a800000000000000054c3ac000214000000eb00000001b4de8000e30000000000000eec8400003d40c0cec000c24000384468854c0033000000108c13c4d5070698000000174a80000afc838f94000000124000000000e3c00
  | 8 => 0xc486cc0d80000000000000009300000003b000032c000000d183580007d800000018801cad8000000000e509f000000000000000064482cc840000004b40000008000000000000000000002d0000968000aac00000000000000000016cca8e08b0c2840000009a40000000004b85a0d78814c50708000938000a9091cb1878c000a602cc000000000000868000dc40000880000000000000008f8798000000000e000010402900006ec0d0f0d0545b80006bc0ac000000000ed0170bc4db80000000008d84ec1c4344000000d34000d8c000000000fd4000000000a2c4940006e8df00bc0000008a4ef8000000000054000ad40000007c80004740000000f8000694d30060310f18000000000990b10a280009805bce1caf40002acfa80000000005dccc8000000cf89d4f0000073c231018a78000000500000000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd764c910004fc764c910047cc324c910015f6714c91000df47654510036f4765451000cf47654510015f77554510017777554510007776554510036f66554510036f46554510057746554510007b774545101cfb474545100577754545101cf755454510005f773545101d7765354510057745354510005f77254510006f76254510006f56254510057775254510007755254510007f3705451000df6705451000df4705451011ff07054510016f76054510017f3605451011f77505451011f75505451011fb7405451011ff2405451011fb540545101cff1405451000df4764c510026f4764c51000cf4764c510005f7754c510005f5754c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c51004fd4634c51004fd6434c5101c7d5434c510005f7724c510006f7624c510006f5624c510007f3704c51000df6704c51000df4704c5100fff0704c510016f7604c510017f3604c5100ffb7404c5100fff2404c5100ffb5404c5101c7f1404c5100ffd7304c5100ffd5304c51000df4764851001ef4764851000cf47648510005f77548510005f57548510006f76548510006f56548510007b774485101b7b474485100eef664485100eef46448510005f77348510005f57348510006f76348510006f56348510015f77248510017e77248510007e7624851001ef6624851001ef46248510047e46248510047e65248510007e55248510047e642485101b7e542485101bfe73248510047e43248510007f3704851000df6704851000df470485100dff07048510016f76048510017f360485100dfb740485100dff240485100dfb540485101b7f140485100dfe720485100dfe5204851003fbb765011002ebb765011009fb8765011002eb87650110007bb75501101afba7550110007b975501101afb87550110007bb65501101afba6550110007b965501101afb86550110007bb73501101a7ba7350110007b973501101a7b87350110007bb63501101a7ba6350110007b963501101a7b863501101afbb53501101a7ba5350110007b953501101a7b85350110007bb725011019fba7250110007b9725011019fb87250110007bb625011019fba6250110007b9625011019fb862501101afbb525011019fba5250110007b9525011019fb852501101a7bb325011019fba3250110007b9325011019fb8325011009fbb7150110007b3715011009fba715011009fb9715011009fb8715011009fb0715011000fbb615011000ebb615011000fb3615011009fbb515011009fba515011009fb2515011009fb95150110007b1515011009fb8515011009fbb315011009fba315011009fb2315011009fb93150110007b1315011009fb8315011009fbb215011009fba215011009fb2215011009fb92150110007b1215011009fb82150110
  | 1 => 0x951021df7715951022dfb7059510224ff75595100067f7559510004ff7459510006bf7459510004bf745951002cfe7459510004fd745951002cfc7459510006bc745951002cbc7459510004ff7359510024fe7359510024fc7359510004ff725951001cfe725951001cfc72595100567f525951021cff7159510006f771595100bef6215951011cff7059510006fb705951011ebf405951011ebd4059510024fe76d8d1004ede63d8d10034fe75d8d10004fd75d8d10034fc75d8d10004ff74d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100fcfd73d8d1001cfe72d8d10004fd72d8d1001cfc72d8d10006de32d8d1004edc32d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d10216df31d8d10216dd31d8d10216f621d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d10206bf40d8d10206bd40d8d10206df30d8d10206dd30d8d10024ff7658d1004edc6358d101fdf77158d1020dfb7058d10004ff7558d10034fe7558d10034fc7558d10004ff7458d1002cfe7458d10004fd7458d1002cfc7458d10204ff7358d10006df7358d10004ff7258d1001cfe7258d1001cfc7258d101fcff7158d10006f77158d1007ef62158d100fcff7058d10006fb7058d100febf4058d100febd4058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100367c6554d10015f67154d10187765154d1001cfe76d8910046ee62d8910034fe75d8910004fd75d8910034fc75d8910004ff74d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100dcfd72d891000cff71d8910014fe71d891000cfd71d8910014fc71d89101f6f651d89101f6f631d89101f6ef21d89101f6ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d89101e6bf40d89101e6bd40d89101e6ef20d89101e6ed20d891001cff76589100057f75589100557c7558910005bf745891003dbc7458910005df735891004ddc7358910046ec62589101ddf771589101edfb7058910004ff75589100067f75589100047f7558910034fe7558910034fc75589100067c75589100347c7558910004ff7458910006bf7458910004bf745891002cfe7458910004fd745891002cfc7458910006bc745891002cbc7458910004ff7358910006df7358910004df7358910024fe7358910024fc7358910006dc7358910024dc73589101e4ff7258910006ef7258910046ee52589101dcff7158910006f7715891005ef6515891005ef631589100dcff7058910006fb70589100debf40589100debd4058910004ff7654910004fe7654910004fd7654910004fc76549100367e65549100067d655491001eee6254910006ed6254910015f67154910004ff764c910004fe764c910004f
  | 2 => 0xcec764c920005ef754c920005ed754c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920067cc634c920026cc634c920005ef714c920007eb704c92000dee704c92000dec704c92013fe8704c92001eef604c92001feb604c92013faf404c92013fad404c92013fcf304c92013fea304c92013fcd304c920014fe76d852005ef661d8520034fe75d8520004fd75d8520034fc75d8520004ff74d852002cfe74d8520004fd74d852002cfc74d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d852024eee52d8520006ed52d852005ef621d852024ef521d852000cfe70d852001cfd70d852000cfc70d85201debf40d85201debd40d85201def710d85200057f75585200757c7558520005bf745852006dbc7458520005df7358520065dc735852005ef46158520245fb7058520004ff7654520004fe7654520004fc76545200367e65545200067d6554520005bf745452006dbc745452001dee72545200076d5254520016f66154520004ff764c520004fe764c520004fc764c52001dee724c520016f6614c52000dec7648520016ec764852000cec7648520005ef7548520005ed7548520006ef6548520006ed6548520007af744852023fac744852023eef644852023eed6448520005ef7348520005ed73485200e6ee63485200e6ec634852001def714852001fe77148520007e76148520016ee6148520016ec614852005fe4614852005fe65148520007e5514852023fe7414852005fe4414852005fe63148520007e53148520007eb704852000dee704852000dec70485200dfe8704852001eef604852001feb60485200dfaf40485200dfad40485200dfea30485200dfe7104852001df8764c120026f8764c12001cf8764c12000dfb734c12000fdb734c120007db634c120026fa634c120026f8634c120067d8634c120067da534c120007d9534c120007eb724c12001dfa724c12001df8724c120087e8724c12000efb624c12000feb624c120087ea524c120007e9524c120087db324c120087ea324c120087d9324c120067e9324c120007c9324c120067db314c120007d9314c120087eb214c120007e9214c120034fe76d95100567e65d951011cfd75d9510004ff74d951002cfe74d9510004fd74d951002cfc74d95100067e54d95100567c54d9510024fe73d9510004fd73d9510024fc73d95100567f53d951001cfe72d9510004fd72d951001cfc72d95100067e52d95100567c52d951000cff71d9510014fe71d951000cfd71d9510014fc71d95102367f51d95102367d51d9510236f621d9510014ff70d951000cfe70d9510014fd70d951000cfc70d95102267f50d95102267d50d9510226bf40d9510226bd40d9510034ff76595100567c6559510005bf745951003dbc745
  | 3 => 0x7104c530004ff7648530004fe7648530004fc7648530005bf744853008dbc7448530025de7348530005dd7348530006ef624853001eec62485300e7cf3248530016f66148530007d53148530034fe76d95200767e65d952015cfd75d9520004ff74d952002cfe74d9520004fd74d952002cfc74d95200767f54d95200067d54d9520024fe73d9520004fd73d9520024fc73d95200067e53d95200767c53d952000cff72d952001cfe72d952000cfd72d952001cfc72d95202967f52d95202967d52d9520014fe71d9520004fd71d9520014fc71d95200067e51d95200767c51d9520296ef21d952001cff70d952001cfd70d95202867f50d95202867d50d9520286bf40d9520286bd40d9520034ff76595200767c6559520005df7359520065dc735952027def725952028dfb7059520284ff75595200067f7559520004ff745952002cfe7459520004fd745952002cfc7459520004ff7359520006df7359520004df7359520024fe7359520024fc7359520006dc7359520024dc73595200767f535952027cff7259520006ef7259520004ff7159520014fe7159520014fc71595200767f51595200c6ef215952015cff7059520006fb705952015ebf405952015ebd4059520024fe76d8d20066de63d8d20034fe75d8d20004fd75d8d20034fc75d8d20004ff74d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2013cfd73d8d20006df53d8d20066dc53d8d20066de43d8d20006dd43d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d20276df32d8d20276dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20066dc31d8d2001cff70d8d2001cfd70d8d20266bf40d8d20266bd40d8d20266df30d8d20266dd30d8d20024ff7658d200057f7558d200757c7558d20066dc6358d2025def7258d2026dfb7058d20004ff7558d200067f7558d200047f7558d20034fe7558d20034fc7558d200067c7558d200347c7558d20004ff7458d2002cfe7458d20004fd7458d2002cfc7458d20264ff7358d20006df7358d2025cff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d2013cff7058d20006fb7058d2013ebf4058d2013ebd4058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200367e6554d200067d6554d2001dee7254d2000dec7654920036ec765492000cec765492001def755492001f6f75549200076f6554920036ee6554920036ec65549200776c65549202576e54549200776c5454920005ef73549200776f53549200076d5354920005ef71549200776f5154920007eb705492000dee705492000dec705492015fe8705492001eef605492001feb605492015f6f505492015f6d505492015faf405492015fad405492015fea305492000dec764c920026ec764c920
  | 4 => 0x9530004fd745953002cfc74595302d4ff7359530006df7359530004ff7259530006ef7259530004ef725953001cfe725953001cfc7259530006ec725953001cec72595300967f5259530004ff7159530014fe7159530014fc715953017cff7059530006fb705953017ebf405953017ebd405953000ddc7654d30036dc7654d3000cdc7654d30025df7554d300275f7554d300075f6554d30036de6554d30036dc6554d300975c6554d302cedf6454d302cedd6454d300975f5454d302cf5d5454d30005df7254d300975f5254d30005df7154d302c75e5154d300975c5154d30007db7054d3000dde7054d3000ddc7054d3017fd87054d30026df6054d30027db6054d3017f5f5054d3017f5d5054d3017f9f4054d3017f9d4054d3017fda2054d3001cfe76d8930086ee62d8930034fe75d8930004fd75d8930034fc75d8930004ff74d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d8930006ef52d8930086ec52d8930006ef42d8930086ec42d8930086ee32d89302beed32d8930014fe71d8930004fd71d8930014fc71d8930086ef21d8930024fd70d893025ebf40d893025ebd40d893025eef20d89300057f75589300957c7558930086ec62589302b5fb7058930004ff7654930004fe7654930004fc76549300367e65549300067d6554930025de73549300075d535493000ddc764c93001edc764c93000cdc764c930005df754c930005dd754c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930087cc624c93001ecc624c930005df714c930007db704c93000dde704c93000ddc704c93013fd8704c930026df604c930027db604c93013f9f404c93013f9d404c93013fcf204c93013fda204c930014fe76d853008dbe74d8530005bd74d853007ef661d8530034fe75d8530004fd75d8530034fc75d8530004ff74d853002cfe74d8530006be74d853002cbe74d8530004fd74d8530006bd74d8530004bd74d853002cfc74d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d8530006f741d853007ef441d853007ef631d85302aef531d8530024fd70d85301febf40d85301febd40d85301fef710d853007ef461585302a5fb7058530004ff7654530004fe7654530004fc76545300067f65545300367c6554530005bf745453008dbc7454530025de735453012f5e535453000ddc764c530016dc764c53000cdc764c530005df754c530005dd754c53029edf644c53029edd644c530005df724c530025df714c530027d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007fd6214c530007db704c53000dde704c53000ddc704c5300ffd8704c530026df604c530027db604c5300ff9f404c5300ff9d404c5300ffda204c5300ffd
  | 5 => 0x5bf75585400073f75585400053f75585400b5be75585400b5bc75585400073c75585400b53c7558540005bf73585400adbe73585400adbc7358540005bf72585400a5be72585400a5bc7258540315bf7158540007b7615854009ebe615854009ebc615854009fb4615854009eb46158540305bf7058540007bb705854030dbb7058540306bf605854003fbb6058540307ba1058540005bf7654540006bf7654540004bf7654540005be7654540005bd7654540005bc7654540006bc7654540004bc7654540225bf75545400b73e65545400073d6554540005bf73545400adbe73545400adbc73545402ff3e53545400b73c5354540005bf72545400a5be72545400a5bc72545400b73f52545400073d525454021dbf71545400b7b7515454009f3e515454009f3c515454009fb4515454009fb6215454011dbf705454000dbe705454000dbc705454011ebf6054540137bb605454011f3f505454011f3d505454011fb7105454011fba1054540005bf764c540005be764c540005bd764c540005bc764c540005bf754c5400b5be754c540005bd754c5400b5bc754c540205bf734c5400af9e634c5400079d634c540005bf724c5400a5be724c5400a5bc724c5401fdbf714c5400afb7314c54009f9e314c54009f9c314c54009fb4314c54009fb6214c5400fdbf704c54000dbe704c54000dbc704c5400febf604c54010fbb604c5400ff9f304c5400ffb7104c5400ffba104c540005bf7648540006bf7648540004bf7648540005be7648540005bd7648540005bc7648540006bc7648540004bc7648540005bf75485400b5be7548540005bd75485400b5bc7548540005bf73485400adbe7348540005bd73485400adbc73485401e5bf72485400a7ae6248540007ad62485400a7ae5248540007ad52485402f7af32485400a7ac32485401ddbf7148540007b7614854009fb4614854009fb65148540007b5514854009fb63148540007b531485400a7b7214854009fae214854009fac214854009fb421485400ddbf704854000dbe704854000dbc70485400debf60485400efbb60485400dfaf20485400dfb710485400dfba1048540034fe76d95300967e65d953017cfd75d9530004ff74d953002cfe74d9530004fd74d953002cfc74d95300067e54d95300967c54d953000cff73d9530024fe73d953000cfd73d9530024fc73d95302ee7f53d95302ee7d53d953001cfe72d9530004fd72d953001cfc72d95300067e52d95300967c52d9530014fe71d9530004fd71d9530014fc71d95300967f51d9530024ff70d9530024fd70d95302de7f50d95302de7d50d95302debf40d95302debd40d9530034ff76595300967c65595302d5df7359530005ef7259530085ec72595302e5fb70595302dcff75595300067f7559530004ff745953002cfe745
  | 6 => 0xa1058d40005bf7654d40005be7654d40005bd7654d40005bc7654d402ddbf7554d400b73e6554d400073d6554d402d5bf7354d400af9e6354d400079d6354d400b79f5354d400af3e5354d400af3c5354d400af9c5354d40005bf7254d400a5be7254d400a5bc7254d400b73f5254d40005bf7154d4009dbe7154d4009dbc7154d403673e5154d400b73c5154d4017dbf7054d4000dbe7054d4000dbc7054d4017ebf6054d40197bb6054d4017f3f5054d4017f3d5054d4017f9f3054d4017fba1054d4035dbe76d89400b5be75d8940005bd75d89400b5bc75d89400adbe73d8940005bd73d89400adbc73d8940006bf63d8940006bd63d8940335bd72d89400a6be62d89400a7ae62d89400a6bc62d8940007af32d89400a7ac32d894009dbe71d8940005bd71d894009dbc71d894002dbf70d894000dbe70d894002dbd70d894000dbc70d8940346bf60d8940357bb60d8940347af20d8940347ad20d8940347ba10d894034dbf7658940005bf75589400b5be75589400b5bc7558940005bf73589400adbe73589400adbc7358940006bf6358940006bd6358940345bf7258940007af62589400a6be62589400a6bc62589400a7ac6258940005bf715894009dbe715894009dbc71589400a7af2158940335bf7058940007bb705894033dbb7058940336bf605894006fbb6058940337ba1058940005bf7654940005be7654940005bd7654940005bc7654940285bf75549400073f65549400b73c6554940005bf73549400adbe73549400adbc73549400b73f53549400073d535494027dbf72549400b7af52549400a73e52549400a73c52549400a7ac5254940005bf715494009dbe715494009dbc71549400b73f51549400a7af215494015dbf705494000dbe705494000dbc705494015ebf6054940177bb605494015f3f505494015f3d505494015faf205494015fba1054940005bf764c940005be764c940005bd764c940005bc764c940005bf754c9400b5be754c940005bd754c9400b5bc754c940265bf734c94025dbf724c9400afaf324c9400a79e324c9400a79c324c9400a7ac324c9400a78c324c940005bf714c94009dbe714c94009dbc714c94013dbf704c94000dbe704c94000dbc704c94013ebf604c94014fbb604c94013f9f304c94013faf204c94013fba104c94032dbe76d85400b5be75d8540005bd75d85400b5bc75d85400adbe73d8540005bd73d85400adbc73d85400a5be72d8540005bd72d85400a5bc72d8540305bd71d854009ebe61d854009fb661d854009ebc61d8540007b751d854009fb451d8540007b731d854009fb431d854009fb621d854002dbf70d8540327bb70d854000dbe70d854002dbd70d854000dbc70d8540316bf60d8540327bb60d8540317b710d8540317ba10d8540317b510d854031dbf7658540
  | 7 => 0x855021ebd40d855021ef710d8550005bf74585500d5bc74585500bef461585503d5fb705855000d7c76545500167c765455000c7c76545500073f74545503cf3c74545503ce7f64545503ce7d64545500057f735455012e7e635455012e7c63545500057f72545500067f62545500357f71545500377771545500077761545500167e61545500167c61545500bf7461545500bf7621545500077b705455000d7e705455000d7c705455011f7870545500367f60545500377b605455011f3f405455011f771054550004ff764c550004fe764c550004fc764c5500357e754c5500057d754c550004ff7648550004fe7648550004fc76485500357e75485500057d7548550005bf74485500d5bc744855001eee62485500076d5248550016f661485500077551485503c5be76d954039dbd75d95400b6be65d95400b73e65d95400b63e65d95400b6bc65d95400adbe73d9540005bd73d95400adbc73d95400073e53d95400b73c53d95400a5be72d9540005bd72d95400a5bc72d95400b73f52d954009dbe71d9540005bd71d954009dbc71d95400073e51d95400b73c51d954002dbf70d954000dbe70d954002dbd70d954000dbc70d95403aebf60d95403bfbb60d95403af3f50d95403af3d50d95403afba10d95403b5bf76595403adbf75595400073f65595400b6be65595400b6bc65595400b73c6559540005bf73595400adbe73595400adbc73595400b73f5359540005bf72595400a5be72595400a5bc7259540005bf7159540007b77159540005b7715954009dbe715954009dbc7159540007b4715954009db471595400b73f515954039dbf7059540007bb70595403a5bb705954039ebf60595400d7bb605954039fba1059540395be76d8d400b5be75d8d40005bd75d8d400b5bc75d8d40006bf65d8d40006bd65d8d4036dbd73d8d400aebe63d8d400af9e63d8d400aebc63d8d400a5be72d8d40005bd72d8d400a5bc72d8d4009dbe71d8d40005bd71d8d4009dbc71d8d40006be61d8d40006bc61d8d4002dbf70d8d4000dbe70d8d4002dbd70d8d4000dbc70d8d4037ebf60d8d4038fbb60d8d4037f9f30d8d4037f9d30d8d4037fba10d8d40385bf7658d40005bf7558d400073f7558d400053f7558d400b5be7558d400b5bc7558d400073c7558d400b53c7558d40006bf6558d40006bd6558d4037dbf7358d400079f6358d400aebe6358d400aebc6358d400af9c6358d400af9e5358d40005bf7258d40007af7258d40005af7258d400a5be7258d400a5bc7258d40007ac7258d400a5ac7258d40005bf7158d40007b77158d40005b77158d4009dbe7158d4009dbc7158d40007b47158d4009db47158d40006be6158d40006bc6158d400af9f3158d4036dbf7058d40007bb7058d40375bb7058d4036ebf6058d4008fbb6058d4036fb
  | 8 => 0xedbc74d8121006bf64d8121006bc64d81210defa60d8121034fe75d8121004fd75d8121034fc75d8121004ff74d8121006bf74d812102cfe74d8121004fd74d812102cfc74d8121006bc74d812102cbc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d8121246ee52d8121006ed52d812101cfd71d812100cfc71d81211eef651d8121006f551d81211eef631d8121006f531d81210debf40d81210defa20d81210defa10d81210057f75581210f57c7558121005bf74581210edbc7458121006bf6458121006bc6458121005df73581210e5dc73581210def86058121024fe76d8d500cede63d8d5000cfd75d8d50024fc75d8d50004ff74d8d5002cfe74d8d50004fd74d8d5002cfc74d8d500cede53d8d50406dd53d8d5001cfe72d8d50004fd72d8d5001cfc72d8d504067f52d8d50006de32d8d500cedc32d8d50014fe71d8d50004fd71d8d50014fc71d8d50034fd70d8d502d6bf40d8d502d6bd40d8d502d6df30d8d500cedc6358d50005ef7258d500c5ec7258d503fdfb7058d5000d7c7654d500267c7654d5000c7c7654d503f67f6454d503f67d6454d500357f7354d500375f7354d500075f6354d500267e6354d500267c6354d500cf5c6354d500cf5e4354d503f75d4354d500057f7254d500057f7154d501867e6154d501867c6154d500077b7054d5000d7e7054d5000d7c7054d5017f787054d500367f6054d500377b6054d5017f3f4054d5017f5f3054d5001cfe76d89500c6ee62d895000cfd75d895001cfc75d8950004ff74d895002cfe74d8950004fd74d895002cfc74d8950024fe73d8950004fd73d8950024fc73d89503ee7f53d89500067d53d89500c6ee52d89503eeed52d8950006ef32d89500c6ec32d8950014fe71d8950004fd71d8950014fc71d89503ee7f51d8950034fd70d895027ebf40d895027ebd40d895027eef20d8950005df73589500cddc73589500c6ec62589503e5fb705895000d7c765495001e7c765495000c7c76549501767e64549501767c64549500057f73549500067f63549500357f72549500376f72549500076f625495001e7e625495001e7c62549500c76c62549500057f71549500c76f21549500077b705495000d7e705495000d7c705495015f7870549500367f60549500377b605495015f3f405495015f6f2054950004ff764c950004fe764c950004fc764c9500357e754c9500057d754c9500c7cc324c950014fe76d85500bef661d855000cfd75d8550014fc75d8550004ff74d855002cfe74d8550004fd74d855002cfc74d8550024fe73d8550004fd73d8550024fc73d855001cfe72d8550004fd72d855001cfc72d85503de7f52d85500067d52d85500bef651d85503def551d8550006f741d85500bef441d8550034fd70d855021ebf40d
  | 9 => 0xd32d8d2144eec32d8d2101cff71d8d2101cfd71d8d2143edf31d8d2143edd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006bf40d8d21006de30d8d210e6dc30d8d2144eef20d8d2143ef710d8d21024ff7658d21005bf7458d210edbc7458d21006bf6458d21006bc6458d210e6dc6358d21435ef7258d21445f77158d21004ff7558d21034fe7558d21034fc7558d21004ff7458d21006bf7458d21004bf7458d2102cfe7458d21004fd7458d2102cfc7458d21006bc7458d2102cbc7458d2143cff7358d21006df7358d21434ff7258d21006ef7258d210e6ef3258d21106ec3258d21144ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21006bf4058d210e6df3058d21106ef2058d21146f71058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d210367c6554d21006bf6454d21196bc6454d21006df6354d21026dc6354d21005ef7254d2101dec7254d21015f67154d21187765154d21015ec7654921036ec7654921014ec765492101def755492101f6f75549210076f6554921036ee6554921036ec65549210f76c655492142def745492142ded7454921007af6454921427ac64549214276e54549210f76c54549210e5ee73549210e5ec73549210f76f53549210076d5354921007e77154921015ee7154921015ec7154921167e4715492101eef615492101fe761549211676f5154921167e651549211676d5154921427e74154921167e44154921167e63154921005ef70549210f76f5054921427af4054921167e7105492101df47654521036f4765452101cf47654521015f77554521017777554521007776554521036f66554521036f465545210f7746554521007b774545210edf674545210edf47454521417b474545210edb47454521007b76454521417b464545210f7775454521417755454521005f7735452141f7653545210f7745354521007e7725452101df6725452101df47254521127e47254521016f76254521017e76254521127775254521127e652545211277552545210f7e55254521007655254521127e64254521417e5425452141fe73254521127e43254521005f770545210f7775054521417b74054521127e7205452101df4764c521026f4764c52101cf4764c521005f7754c521005f5754c5210edf6744c5210edf4744c521007b7644c52140fb4644c521015f7734c521017d7734c521007d7634c521026f6634c521026f4634c5210e7d4634c5210e7d6434c52140fd5434c521007e7724c52101df6724c52101df4724c521107e4724c521016f7624c521017e7624c521107e6524c521007e5524c521107e6424c52140fe5424c5210e7e7324c521107e4324c521005f7704c52140fb7404c5210e7d7304c521107e7204c52100cfe76d8121
  | 10 => 0x81310fefa10d81310fef86058131034fe76d95210f67e65d9521006bc64d9521164fd75d9521004ff74d952102cfe74d9521004fd74d952102cfc74d9521024fe73d9521004fd73d9521024fc73d95210f67f53d9521014ff72d9521014fd72d95214867f52d95214867d52d952101cff71d952101cfd71d95214767f51d95214767d51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210f67c50d9521006bf40d9521486ef20d9521476f710d9521034ff76595210f67c6559521005bf74595210edbc7459521006bc645952146def725952147df77159521474ff75595210067f7559521004ff7459521006bf7459521004bf745952102cfe7459521004fd745952102cfc7459521006bc745952102cbc7459521004ff7359521024fe7359521024fc735952146cff7259521006ef7259521164ff7159521006f77159521004ff705952100cfe705952100cfc70595210f67f5059521006bf4059521126ef2059521166f71059521465be76d91210eebe76d912102cbe76d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121006be63d9121006bc63d9121457af72d9121457ac72d912145fae52d9121007af32d912145fac32d9121457b671d912145fb571d9121457b651d9121457b631d912145fb721d9121457ae21d9121457ac21d9121457b421d9121005bd70d9121006be60d9121006bc60d912145faf20d9121457b710d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bc53d9121456bf72d912145ebe72d9121456bd72d9121456bc72d912145ebf52d912145ebe52d912145ebd52d912145ebc52d912145ebf32d912145ebe32d912145ebd32d912145ebc32d9121456bf71d9121456be71d9121456b671d9121456bd71d912145eb571d9121456bc71d9121456bf51d9121456be51d9121456bd51d9121456bc51d9121456bf31d9121456be31d9121456bd31d9121456bc31d9121456bf21d9121456be21d9121456bd21d9121456bc21d9121006bf70d9121006be70d9121006bd70d9121004bd70d9121006bc70d9121006bf50d9121006be50d9121006bc50d9121006bf30d9121006be30d9121006bc30d912145ebf20d912145ebe20d912145ebd20d912145ebc20d9121456bf10d9121456be10d9121456bd10d9121456bc10d9121024fe76d8d21006bf64d8d21006bc64d8d210e6de63d8d2101dee72d8d21015ed72d8d210e7cf32d8d21034fe75d8d21004fd75d8d21034fc75d8d21004ff74d8d2102cfe74d8d21004fd74d8d2102cfc74d8d21144fd73d8d210e6de53d8d21014ff72d8d21014fd72d8d2143eed72d8d21014ed72d8d2144edf32d8d210e6ef32d8d2144ed
  | 11 => 0x1e7e625495101e7c62549511276c62549510077771549510157e71549510157c71549511677471549510367f61549510377761549511676f21549511677621549510057f70549514bf3f40549511276f2054951167771054951004ff764c951004fe764c951004fc764c9510057f754c9510357c754c951006bf644c95114ebc644c951127cc324c95100cfe76d8151135bc74d8151006bf64d8151006bc64d815111efa60d8151014fd75d815100cfc75d8151004ff74d8151006bf74d815102cfe74d8151004fd74d815102cfc74d8151006bc74d815102cbc74d8151024fe73d8151004fd73d8151024fc73d815101cfe72d8151004fd72d815101cfc72d81513d67f52d81510067d52d8151034fd71d815122ef621d815111efa50d815111ebf40d815111efa10d8151005bf7458151135bc7458151006bf6458151006bc645815111ef86058151034fe76d95311167e65d9531184fd75d9531004ff74d953102cfe74d9531004fd74d953102cfc74d9531014ff73d9531014fd73d95314b67f53d95314b67d53d95314b6de43d9531006dd43d953101cfe72d9531004fd72d953101cfc72d9531024ff71d9531024fd71d95314a67f51d95314a67d51d95314a6f621d953100cfe70d9531004fd70d953100cfc70d9531006bf40d95314b6df30d95314a6f710d9531034ff76595311167c6559531005bf745953110dbc745953149ddf73595314adf771595314a4ff75595310067f7559531004ff7459531006bf7459531004bf745953102cfe7459531004fd745953102cfc7459531006bc745953102cbc74595311167f54595310067d545953149cff7359531006df735953112e7e535953112e7c535953112ede4359531006dd4359531004ff725953101cfe725953101cfc72595311167f5259531184ff7159531006f771595311867e51595311867c5159531186f62159531004ff705953100cfe705953100cfc70595311167f5059531006bf405953112edf3059531186f7105953101cfe76d8931106ee62d8931034fe75d8931004fd75d8931034fc75d8931004ff74d893102cfe74d8931004fd74d893102cfc74d8931014fd73d8931106ee32d8931496ed32d8931024fd71d8931436ef21d893100cfe70d8931004fd70d893100cfc70d8931006bf40d8931496df30d8931436f710d8931005bf745893110dbc7458931106ec625893148df77158931004ff7654931004fe7654931004fc76549310367e65549310067d6554931005df7354931025dc735493100cfe76d81310fefa60d8131034fe75d8131004fd75d8131034fc75d8131004ff74d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d813101cfe72d8131004fd72d813101cfc72d8131024fd71d813120ef621d81310febf40d81310fefa30d
  | 12 => 0xa30d813213efa20d81320057f75581321557c7558132087cc325813213ef860581324fdbe76d9151136be76d915102cbe76d91514ef3f75d91514ef3c75d9151006be63d9151006bc63d91510073e53d91514f73c53d9151006be62d9151006bc62d91514f73f52d91514f7b751d91514ef3e51d91514ef3c51d91514efb451d91514efb621d9151005bd70d9151006be60d9151006bc60d91514f73f50d91514efb710d91514eebf75d9151136be75d91514eebd75d91514eebc75d9151006bf73d9151006be73d9151006bd73d9151006bc73d91514f6bf53d91514f6be53d91514f6bd53d91514f6bc53d9151006bf72d9151006be72d9151006bd72d9151006bc72d91514f6bf52d91514f6be52d91514f6bd52d91514f6bc52d9151006bf32d9151006be32d9151006bc32d91514eebf71d91514eebe71d91514eebd71d91514eebc71d91514eebf51d91514eebe51d91514eebd51d91514eebc51d91514eebf31d91514eebe31d91514eebd31d91514eebc31d91514eebf21d91514eebe21d91514eebd21d91514eebc21d9151006bf70d9151006be70d9151006bd70d9151004bd70d9151006bc70d91514f6bf50d91514f6be50d91514f6bd50d91514f6bc50d9151006bf30d9151006be30d9151006bc30d9151006bf20d9151006be20d9151006bc20d91514eebf10d91514eebe10d91514eebd10d91514eebc10d9151024fe76d8d510357e75d8d510157d75d8d51006bf64d8d51006bc64d8d5112ede63d8d5112f5e53d8d51014fd75d8d5149e7d75d8d510147d75d8d51004ff74d8d5102cfe74d8d51004fd74d8d5102cfc74d8d514e67f54d8d510067d54d8d5112e7e53d8d5112ede53d8d514e6dd53d8d5112e7c53d8d5101cfe72d8d51004fd72d8d5101cfc72d8d514e67f52d8d51034fd71d8d5149e7e51d8d5149e7c51d8d5149edf31d8d5149ef621d8d5100cfe70d8d51004fd70d8d5100cfc70d8d514e67f50d8d51006bf40d8d5149ef710d8d51005bf7458d51135bc7458d51006bf6458d51006bc6458d5112edc6358d514ddf77158d5101cfe76d8951006bf64d8951006bc64d8951126ee62d8951014fd75d8951004ff74d895102cfe74d8951004fd74d895102cfc74d8951024fe73d8951004fd73d8951024fc73d8951126ee52d89514d6ed52d8951034fd71d895146eef21d895100cfe70d8951004fd70d895100cfc70d89514d67f50d8951006bf40d895146ef710d8951005bf7458951135bc7458951006bf6458951006bc6458951126ec62589514cdf771589510157c765495101e7c76549510147c76549514c57f74549514c57d74549510073f64549511767e64549511767c64549514bf3c64549511763c645495112d7e735495112d7c73549510067f63549510357f72549510376f72549510076f6254951
  | 13 => 0x4d5201c7c7654d521757e7454d521757c7454d525267f6454d525267d6454d520357f7354d520375f7354d520075f6354d520267e6354d520267c6354d5216f5c6354d520265c6354d5216f5e4354d525275d4354d520076f7254d5201d7e7254d5201d7c7254d5218f6c7254d5201d6c7254d520367f6254d520376f6254d520057f7154d521867e6154d521867c6154d5218f6f2154d520057f7054d525273f4054d5216f5f3054d5218f6f2054d52014fe76d8552166f661d855201cfd75d8552004ff74d855202cfe74d8552004fd74d855202cfc74d8552024fe73d8552004fd73d8552024fc73d8552034fd72d8552166f651d8552166f621d855200cfe70d8552004fd70d855200cfc70d85524ce7f50d8552006bf40d855247eef20d8552005bf7458552175bc7458552166f4615855200cfe76d815215efa60d815201cfd75d8152004ff74d815202cfe74d8152004fd74d815202cfc74d8152024fe73d8152004fd73d8152024fc73d81523e67f53d81520067d53d8152034fd72d8152014fe71d8152004fd71d8152014fc71d81523e67f51d815228eef21d815215efa50d815215ebf40d815215efa20d8152005df735815216ddc735815215ef86058152034fe76d95321567e65d953250fcc32d953218cfd75d9532004ff74d953202cfe74d9532004fd74d953202cfc74d953201cff73d953201cfd73d953251e7f53d953251e7d53d9532024ff72d9532024fd72d953250e7f52d953250e7d52d9532014fe71d9532004fd71d9532014fc71d95321567f51d953200cfe70d9532004fd70d953200cfc70d95320067e50d95321567c50d9532006bf40d953251edf30d953250eef20d9532034ff76595321567c6559532505df7359532515ef725953218fcc325953250cff75595320067f7559532004ff745953202cfe7459532004fd745953202cfc7459532504ff7359532006df735953218cff7259532006ef7259532004ff7159532014fe7159532014fc7159532004ff705953200cfe705953200cfc70595321567f5059532006bf405953216edf305953218eef2059532014fe76d8532447cc32d8532146f661d8532034fe75d8532004fd75d8532034fc75d8532004ff74d853202cfe74d8532004fd74d853202cfc74d853201cfd73d8532024fd72d853248eef32d8532446ec32d8532146f631d8532146f621d853200cfe70d8532004fd70d853200cfc70d8532006bf40d853248edf30d8532446ef20d8532005bf745853214dbc7458532107cc3258532146f4615853200cfe76d813226fcc32d813213efa60d8132034fe75d8132004fd75d8132034fc75d8132004ff74d813202cfe74d8132004fd74d813202cfc74d813201cfd73d8132024fd72d8132014fe71d8132004fd71d8132014fc71d813213ebf40d813213ef
  | 14 => 0x2000500400500100d00301500500300b00202e00000404102f00800b01c00400200000500200e00100100002d00002300201c00000100300000000d00000500700600000301801100d00600600000000700300a00700a00000300d00600f00900000700300001d00200c00000000703600d00600f00100100700500100000300400000c00100000c00000000000100000406200000c00d00500501406e00200d00200203900100600000000100000000100001001d01701101800200000500000300200700000101903d00500100100100000100100000200100300700400d00602300000800100000000101200200000500e00700000001600000000000f00000200303400300300000000300800e02a00300001000001000300100000000400100203400002000601102500100701100d00000000000000000600000300000300000e00501600700700100e00700402500800900001b00300a02200f00600002700000701600f01100100e00000000400200000001000000100402e00901cfe76d895318eee62d8953024fd75d8953004ff74d895302cfe74d8953004fd74d895302cfc74d8953034fd73d895318eee52d895318eee32d8953014fe71d8953004fd71d8953014fc71d895318eef21d895300cfe70d8953004fd70d895300cfc70d895352e7f50d8953006bf40d8953516df30d8953006ee20d895318eec20d895318eec6258953014fe76d85530357e75d85530257d75d8553186f661d85531877651d8553024fd75d85531867d75d85530247d75d8553004ff74d855302cfe74d8553004fd74d855302cfc74d85534de7f54d85530067d54d8553034fd73d85534ae7e53d85534ae7c53d85534aede43d8553006dd43d855301cfe72d8553004fd72d855301cfc72d85534de7f52d85531867e51d8553186f651d85531867c51d8553186f631d855300cfe70d8553004fd70d855300cfc70d85534de7f50d8553006bf40d85534aedf30d8553005bf7458553195bc7458553186f4615855300cfe76d815317efa60d8153024fd75d8153004ff74d815302cfe74d8153004fd74d815302cfc74d8153034fd73d815301cfe72d8153004fd72d815301cfc72d81533fe7f52d8153014fe71d8153004fd71d8153014fc71d815317efa50d815317ebf40d815317efa30d8153005ef725815318dec725815317ef86058153024fe76d8d5216ede63d8d5201cfd75d8d52004ff74d8d5202cfe74d8d52004fd74d8d5202cfc74d8d5216ede53d8d52536dd53d8d52034fd72d8d52506df32d8d52014fe71d8d52004fd71d8d52014fc71d8d5216edf31d8d5200cfe70d8d52004fd70d8d5200cfc70d8d525367f50d8d52006bf40d8d52006de30d8d5216edc30d8d52506ef20d8d5216edc6358d5252def7258d5201d7c7654d520267c765
  | 15 => 0xe10c0cc43dd4c61ed872642225799b0eae0004061b0027a1e14248000a1c2f946b03acc34028361945c12269b2700a40eb01bb176a3e062c0ef2ca8dd01f254e4031fa505a55a1e59c0c7ea5631f7000000084643f8000cf80001459b2125a0000df22d8172000414a0942b674800003510e890c25b8bb91c20000000d6137499f27d95651966e1167000000000040d83544d21f90061efc3869084390fe88f600200c00300200000500000000501200e00000900000600700000b01a00100101900100a00c00400100c01501000100000000400f00800302500c00300000000600400100b00000500900302100400000201805a00001100200f00d08100000700000200a01201201701100f00300401300000100001100000000200700600100500d02000200000601900100f00000001400001401d00d00400300300001200d00400100000306100e00000200800802500001903700c00000203300100b01700000000000800700500401300b01e01d00900000100000600404500600100300300c00000900000d02300100900000c00200900000400700a00101100300e00501200501800000100400100000b00400700000100600500302300001200200005300000400000001602000000900000400300100600101100100c01701300600101400400100000200000900000d01d00100900200800d00001000100200503400700300a00600000b00802200100000b00000000400603000202100000000800000400800000000000000f00001900400500000700000100e00800300502101003000100a00005900300200500000200300100500300300800000a00500300300000b00c00000100b00103000000503300601500000502c01400000200c00100000000500000001500200400100700000100300000000800000500300500100000000c00100904401101d00301200500300600a00600200000b01b00a00102c00a02900000700200400300400900001d02d00300000e00000600000800900002900000b02d04906b00001400200200600000300300000000202400d00200700c00100000000300700401a00100501800000300a00201600800100000400100100600200300600200401100003f00400500600b00401d00000100000f00300c01704207000300d03000400300300300000401400200000200000900502500c04000500e00300002500700000700001100200300000100101f00501700000b01300200a02400100900002200000a00800201500800000000000000000300602000000300700000000800100a00300b00600600c00200c00200100900100300100000700a00600000909100100600f00000301300200400300000c00200b00200000d00300000100900c00900201301000000300201700b01200700800802300e
  | 16 => 0xbe79f07e8a14dc099d338071c3a06303e997108e84d53a62554076128223088c0e632a39a8f64bd60000071ad095400012c1170f404c90899b781bc03f0a324d010a8584a098b45001db36ea550ac057d16417ecf522b304e0e24eb65a61651bbc6669ae3e51100b2c31a1610eb87a80003ca8000c248971061d752a00a921e10189ec069095950ce1600016f00003d62fb04903a087a00000000080004661ca85ec7e86a81c302c0ee42072e58ac89003f800018e04c82da40b25e87641f029e0c4ce3871b46b953d1de4e22f9261c31a00332011885d60003dc8cd934c2243f609106da7e700000006826d538a00005ec6ca000000039e84c00000010a80001ed12485d200044495f93420e5000181800020b42e255816238700021d4f4671600000002a0000455139874a79943083746903d74daa66417e6250c90adc7927641c010008920ad35c005820a6ba17109a87c44b22f6a4c47e282b07615c84ba7d71270f4c2aa6f703f00010d600021487544c493205120008342d83c016f42120003728f1c09a00022405707a2000388864505c28d0e0825411c0073e4a6c528695a2788efc1b029e1921468adc73a45619a92e449b37f1a801401273c608f907c7a120507d479034e41c0b040c632247509540007692a49ff0e4e9423478c14ede211309800127e0003bc88005c020e0001ee058819a000254468a4a44378000c2272d035937c6145932459ef44a66ce0b307cc7020531df223000039c4579fe52b050718d9c744ae8532ec0d88000000151000094499007c244d36636b26680000006a700011d900466b0000000c025840000000e7264f1f391442980000001fc52040003cd000000016b2f322409a601c29a844000084835696289048364888c0c2442f831506952c280b4161a00e9c00000020c40462c93f4000033c39820ca0751c06e70c7846817c6342178c240140c30e687f8ace33509d1e3d26c8841a207dc00057f4c88ce85ae0e000013e800001e2938cd118e5024b6106056c74400024f02b20000d226ad0d81ad3780cacdb40db0001d3c00059e3810b50c3a2f33429d2c8028853d3a69522e8470c180000004840000640da26f907b0000dd289b105175446c8e907d0b7cbfe5754c29a34a222bf38691b8ef00e71800ff0a2c39742a800103853900000000000002d80d7ca840000c0259c0005c900011c06a60003ea800106638400017080000000e921341166aa00003a4cb200000018e8f783f03f806ac00096a4088000fac6b21378818f662680b880000009680b00000cac58d1aa89340005a5351a52c0000000000000a5439642092b8546000304085c84283d3a51b1d0f84bc0c1098073e27f121a2a42a40f2313147c00004e3301c6461a55b2dc19282ac26d0001b483de6b53561aed20831434b805034c5313b
  | 17 => 0x9f154848e0564bb875c3b27fe4a01cd90443300000998b2875f000219ce007604d90d70ea81a72442690c3097c000109c97000014989300003e44a517592d67073bf80f0b8a00048f10e8f8e00000000006f04f80048724a248340e003846e63282d8a0511ca0710ee800000063b2118ec496004321c81780002aa2b500007bc00006387e0bd4442000000065c000000220800000021a0000000000364a34079a53b2919fcc97e95c295a418bb28b7485a304be05ce458901c00066130780144dc4f549300dd0780000d100005f814a0000e440987be478a4ec00000018ba6e49ce7ac0001b346f600036b84480005f1399a3283260000002020c3e000000162079c49c2d5976820844c0da8b9c0000000b780000009604ca9ac000000000018a00001b4101000000000024b00000000611d9a4ccc3859226b0e786ac0000000f400009be25022e801644e14098245ca25e4648000ad82081e2925509e29800018c80008b91d1a19400040b34f9fd000016417b92190962d631791f85e20004322354ff05ae39621011ee5be3021b6c05481f3b8188c9820121f08fec3d88f00ea06bc9da22d262a04800000015e840400000013b129c25c54c0001d143fe0001cd800096200040480000000a53b1013c0007104452374c2e7860ba1074150939000000043200027724bc6583b03b98b485404dd1ae800114e64b0cb23ec33a82a08518542a863e1bf97bc0606a42b88e5030c02c2a28ae04923e50001f050020004a79cbc9423b50d40f6cc6a5d30f3848504294d0be8cdc00c31015c8710d3a0000ab9af8eee6a6000155cce809e0d905f935010e1b700008c662e00d16a49ee8564ab8001328000000033c05a5980120000db07aa27e000006c51e19e000000000047e9ca49c62c50a3800000068e000221d1be0002f190b42bc8920a59c4c4a46bd00017746a83ea18102bcde627e378890859887627f18e40de7db3608b404be56f0f486a40ae07221619e87482590cb8258b0a541326800000027b0301aa4bc475239c0f040f00003da98fc8e43a71390000e0c000000062c3361b017fa3781a689d3c10a8516a000000127400000030f19c84a83590100bb0e808b20a7a1dc6ce8204699e14258473340800023c0000979e6c7743cc2238ff40ec0002d10e150463c00001bacd627590a2863093065f25d000027259f000224ca9a85200018850f07e200000010bc48f4bf83f885c00023c0000d265042471cb8b368ce39183a8a7e1aa1a59f001f622011a841c9680641d689dc90658641d037c45c5e8107a5a4d182fa10a1f142480903a9a028a4a3b60e89e0d18074720216e883e35114d85883e234d15599a0bce240299951cfca22f3e718349a826c0f008d00e032720a1ec8dea2822a9a3b120e55004c00000003663f1901416e0101288fbc0
  | 18 => 0xcfa53e24c99d81186751be1e201ee8154c4819525000037b07785808a4041118061e2b100000011902321630000bd800000b94e914a6f83ae00008881e818386550488c200000003146194a6093c9860002468a2128c000219a3690d04eb3419464b8e930000165c0002e81e78e0c26c7673851690ee211c2bb8e30d287981a01a843a675129e872c0922a74cc1f4090e3eb0cca3880b003d169853504e2f50001c8000005d1a609c4e689bb14e0cfcf242f41c5931c4309921a180002e0000000000000093700000000000004330940a44000109a6d10d436c3aa9e74f200001048000a9450d4de2200c0a4d83b590f92c49141d480005e445f219217c3ca3923a192b4e0a2843fb97a4000347100a6fce4200047a80000007fd28600002d43fe0fa0c70a2a0000dc8b913385823ad0000e8c000000000000026347c89d4b5052849295e85123633139fc871e5cd1a486d8a1443b3d2268917e9734d000000001263f303300000f04222564aa232911c80000f464643da3a00f67d220b83201700bd38f8a4800023834309f0be841e436942c59e21e1f424d401e77b1f69c905fa00006481b40000000a0000000000023e174924400032f00353004f21b211b4d0409a42803b8d8c3b402d264c4667a539902e87d22910d707f0624000000248471a12304e800055e481476800099c0000001c60f5c0003e5a6e118658f36100c882a23a23297d877a650000127caaa0004770000f2845d0ae9cfc0a853840180007326d31af0000cdc1dc00000000002ea0001da0c626cb2ba11f40000003721908b3a12500016fc2f252447e257c00206c00023d83dc91227e80000005b346c00007e62611e308a823688340294500007ea34c1268c440b539519ec5140002bb1c9831c41c1930b3537a56d296841821800043f15712745bc0001e70a4c6910611dd8dcc4931ea8304cca2d52d017204945ee23881a869e3f627501e52da8170d61470fea01b2071cf93102d91ce98dc9b840847fa2ac6e227903705d8b762ba152a440ee83f24bd994c8b60b6263119119e01525297450762fe4cd80c418823b44582d04fa82f2e19308d5c8b30c21a1118a2e33679668fb04113d69a700000000000000bfa4d206c8000c1c92b0001e4ceca9162d900000001322460000714000152115ca0665b0001158000982000000000000005994dd24625a2ab08f0fde28600000012024b53c38ea00000002488210000436207800136000000009d0aba00014e800026200000004080000001a914740000001d08958b6e25c0e2a52522a0002af9330fb48880001a2c6164de3620a7c63a90d020000049643109519fd11e00029822e00004e443e8000b9476e03e89aca4003332e8b84b687421ad0dc082c5de090269c0000f1040829021a6713148000e1c00000000000004691
  | 19 => 0x49506f4ed82c70f19600ba00001d7800106a5fe270917857c7eb3241e389528d92af1a58e344e92ce0ee00963323988010bc000032e0000dac00021324687c000031e8000aca89427a1a249906af47d04e05de86e3248c448a698f23616d813267e10814b8a0006828285a11ce1e43ef831436e40c0fb265830a08d3c098b0f2c4f040c068d30c37a30a09c0da00c634a94bd0f423130025f839428c39814048265e518a8000d728eb0001f30b5e0003ba8e407b87fa07a00008de0cb0591f44e186ea0e700001cc6cc16e1440a1049e00f969d21e5fa10f835caa815120d95ec1b80a121a8de4a0c98100412d8cee4b30000da430e9a93f0856892014e3fd983021e9631dc94b0d3c00038b9104a267372ef8128ea03883a09e9847a2bc15a0c1000000000011681f89651e1133c00085a48191e91a853432907b4db20803ef1d240ea975245227889660a2fa80e03b413f00005e00007b700006709507ed48c850c7ee8263229fb80008a641f8000fb86b64a418ac0264682e022688f200000000003b058e2f210090ae00000022340a4548000121400045401315886c00744581adc9a2000000054cacc6bc3529c24d2454646e0460072000015800076e31f2e3000013e0002b9a16c84a8ad4a70f590c617c28d87988ce0224bb11352382302c8994467a76a3bd07300006021928a5c0685643f215ac61c14137915606d01fb4c20188e7800000019540000001540000e5600032200000006ed32ba27d03400019680001b445546207a8b468324d6009c7b04372fc84210728704a28c60f884384519d84ba897d3e7a49d2ba69a2d6a28923e89c24a25e106e0000000ea800000027981dc3900512f9999d084000337a2646021b146310a93169b74399a1ccb04bb1d609ccf1a92e0b491dd0c03a61e51cec4903ec1dd88688247011d5a0c09de8bb1781cf52a65aa4251a411cc7842bc9f64f868d12ed8ddc23e7ff0c4a38cc824db15685c844e722448a47442c2b012da5bc5969702c094d871c03503f86f0fa832f21fa2389800894a38aec2780410e317f114042829086e02520003af08100004090001d8ca300f53dda490b168a80c09ea055c6241ada2f0d7e02133208a52cc1344b209e80000590d9800116800000004dd0260bb07224e06ea7cd2a2221864600004b80001ac0481ab97e042a84304a263478636a2d61bb097a29425580002ce85918c82985b67a20a41bfc66209322800002847af3081624000643000086c000569000051000005b4c18f489ae2460968a68f904ac227a4a52a45cc23f8fe4d662222229eacc9857035126bcdf400004782b81a47dd13380002220000d00a3c000666221800050e99a43c80000008ae25c9bf40000001be909023a64e265026c0000003710000e4a2e601f15e11c8633161a2f400076600c9298
  | 20 => 0x17a2b09df86ec2ac10e8ad422a909076a6280007890418000e084f90000a5815827833ca25501a0d0201a400458871113021c2c67f600004ecdb800008a0000e9a01847919a40002034140c8431099e3039c78bae0d1000000000061600004640ce00010e07e8df619f19da2582669050001424ca898e0000d840009aa19c94a41c60001f1800026a0251ff95003280000af8c18c8e00000004f838401106500bc0000000dd000014e0001470000df878b0b680010d281e055811921c85d31e22600008db305868400054b2c6010924058722525785064be1b299ccdbe9b604308fd1e88810551f082dc4e522c198c0aa30c0519364f685903f0180c4244a3000203927a00022c9ee90080000001d58e2a0000668000c360001549c483c4000000122400002e1efa2842ee0000000000ddc78a2ee08ac19c1df2c191d4b8290a00000011982990a491ac63c05000000006e46f4000256c3fa2251b7845c0006c52990ef02ea797000000132e8be02281f092e00049f030123080700025d0cda599208000000000000000009960881d0103403a1d60ac1ca109c22133c1ec46404da00025b81fe0bc42280e800000021013fc0cc69926223f80008510b608a02fe1613b690ac9d857c268168411439a0cc1ba0b9e8101228a981e61654b888dc00050f2dc800040a00000000011a48190000000000000230a5e45ba0001a500010c43c40f909948a45b508184c074480f3100d0852a04716898d8bee02902e0ce068c3820000000ad00003c893a135a5e11069df4cb41bf2350110e1079e3d81a284821160711b8c6a08f30b9842c2006ab1f30df92887c6184268d2588cd36a246ce1e688
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc9d40dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd62440031f50fb82c4880021fe1576549100045fc22eca9220058bc845d952440011bf06bb2a4880123720d765491001c3e43acaa92202ea3c84595524400d1d90eb12a4880021fe15764c9100343e42aec99220008bf845d9324400b17908bb2648800237e0d764c9104f65a3b6e8a8a200297585dcd514400d1e90eb12a28800399589525451000c7a432ea98a20048f48758931440031e90cbaa42880039994b654851001c7a43aca90a201dab4845952144117968edba2428800a7960b734851000c7a432e690a2003ae682d8d2144159d8865b1a428800e3d21d634851000732b2aa490a2013bb081dd54044001e64a3baa8088002aee19755011009d5c432eaa022000bb3815d5404402776102baa80882af8e9976550110004ddc3acaa0220079b887595404408776702b2a80881c72e1db735011009dd840ee6a022000abb865cd40440275710cb9a80880472e1d973501100059dc2ae6a022035b38855cd404400175704b9a80880ceea2097350110005d9c0ae6a022013bb0815cd4044155d30c6b1a80880feece05635011009dd940aa6a02206cf325154d404402776103b928088002aee19725011009d5c432e4a022000bb3815c9404402776102b9280880026ee1d625011003cdc43ac4a022000b3b85589404406b6710ab128088002e6e0d62501101a5cc41ac4a0220a9ea862589404407776702b12808804eeca05525011019fc419264a022013bb2814c940440cb7650fb8a808804f6ca1f715011000dd9436e2a022001bb086dc54044027b64edb8a808804f6c1db7150110005d8c2ee2a022000bb183dc5404400176305b8a80880036ce1d5150110005d943aa2a022000bb0875454044001b610ea8a8088006eca19515011000dd8432a2a022044bb3855454044027e670aa8a80880d7cc9d5515011000798baaa2a022000f3365545404406be60caa8a8088002ece0d51501105479929aa2a022035f3053545404400176704a8a80880d7ccd49515011000798a92a2a022000bb2874c540440017610e98a8088006eca19315011000dd843262a022000bb3854c540440017630a98a8088102ece0d315011009fc9c1a62a022034f92734c54044001f22e698a8088003e4d8d31501101a7c831a62a022000bb3824c54044001b670e90a8088002eca1d2150110005d843a42a022000db08748540440037650c90a8088006ec21921501100ef59bb242a022013eb07648540440017670a90a8088002ec6152150110005d9c1a42a022000bb18348540440797670490a808804fe8e09215011019fd139242a022000fa1724854044001f46c490a80880cfe8189215011019fd129242a022000fa152485404414ff466490a80880cfe80c92150110
  | 1 => 0x902ba6c2982ba2fe0174d85300ac5ec02e9b0a60058be849d9514c00117b093b2a29800a1fa1f65545300061e3a6caa8a60018dc865d5314c0033b100baa62980162fa1276485300045ec24ec90a60018dc865cd214c0051dd0fb1242980032b1d3624853002c3fc3aa9b2a4000a6d8294f65480014db0528eca9000237e0d74595200246e41ae8b2a40008f7815d165480051e902ba2ca9001237a1f73595200064fa06e6b2a4000c9d40dcd65480018beea39aca902b71bdd772595200066639ee4b2a4000acd82d4f634800b1bf0ea1ec6900021fe1571d8d200343e42ae3b1a40008bf845c7634800b17908b8ec69000297a1631d8d200343f43eeab1a4000c3f40dd5634800187a81baac6900021fe157458d200343e42ae8b1a40008ef825d163480011ef02ba2c69000a3d2057458d200062e3aee6b1a4000c6c75dc963480010ff0abb2a69000237e0d7654d2000477c12eca9a40028f6811d953480011eb023b2a6900121f21d6554d200252e41acaa9a4000dca30dcd52480014d90ca9aa4900063b219754c92002567436c6992400087f855cf614800d0f90ab9ec29000a3b20973d852002c5f424eca8a40008bd849d951480050f90eb2aa2900969720d6554520256963a2a4a8a400687e851d931480010fb0a3b262900063b219754852000cf4402ea90a4000e6651d9521480051d90eb2a4290072b320d6548520456563b6e890a4000da870dd12148039998c7b9a4290003728c3734852000c76432e690a4000e6565545214808f74908a8a4290003d254d524c12000de443a649824003dc8874c930480037950c9926090006f2219324c12002764432649824004ecb764c93048007b94ec992609000f721d9324c120027643b2649824003cc8764c930480017970a9926090002f2615324c120005e5c0a649824003ce87648530480017930690a6090003f04c5214c1200061eba4a9b2a2000a798095365440014eb03296ca880162fa1f74595100045fc06e8b2a20008bd80dd165440010ff0aba2ca880023de0574595100045f438e8b2a2000c3f751d16544001968e9b8aca880021fe157458d100343e42ae8b1a20008ef825d163440071d904ba2c6880023de057458d100045fc22eca9a20058bc845d953440011df04bb2a68800e3b2097654d100243f43ecaa9a200087f855d3624400d0f90aba6c48800a3d20574d89100343f43eeab122000c3f40dd5624400187a81baac4880162fa1f74589100061fbaee8b122000c3c75dd1624400117f01ba2c4880022f60374589100043fc2ae8b12200687c855d162440011bf06ba2c4880123720d74589100045f438e8b122000c3f751d16244001878ea3a2c48801237a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100064fa06e6b122000
  | 2 => 0x573d8540004d7c12e7b0a80149ac825cf61500dd37700b9ec2a00066e20173d854033cddc02e5b0a80019b8805cb615000156b0da8ec2a0002cda1731d85400b49f43eeab0a8000e3461dd5615000187ec1baac2a00034ed8375585400069d086eab0a8000d3910dd5615000187eec3aac2a00038d184755854009d5b436c2b0a8000d3475d8561500033750fb82c2a00034edd770585400069c3aee0b0a80b4db371dc16150167d60c3b82c2a00026e60376545400065cc06eca8a8000cba10dd9515000117d0d3b2a2a00024fe157654540004dbc0aeca8a80009bb805d9515002b33d063b2a2a00026760c76545400061f428eca8a8000c3d851d9515000193d063b2a2a00032760c76545400061f298eca8a8000c3c531d9515000187ea43b2a2a00032dd4476545400061f288eca8a8000c3c511d95150001968a23b2a2a00032d884765454002c5fc00eca8a80058bd801d9515000187ea03b2a2a00030f54076545400065b880eca8a8000cba101d9515000196a203b2a2a00032e440765454009c9e43acaa8a8000c3c76595515002766902b2aa2a02cacee01655454009c9ec2ee6a8a801393c875495150001878eca92a2a00026e603764c5400049fc2aec98a801693c855d9315000135f04bb262a00526b209764c540004dbc0aec98a80009bb805d9315002d27d0a3b262a00024f614764c5400045fc32ea98a80008bc865d531500273390eb1a62a02c6e6e01634c540004dcc06ec90a8000cb681dd9215000196b03bb242a00032e60376485400065d086ec90a80008be869d9215000127f0abb242a005a4f2157648540004cfc1aec90a801599c835d9215000137700bb242a00032ba08764854000656c10ec90a8000caf321d92150001958643b242a00162fe00764854002c5ec00ec90a8000caf201d9215000195a403b242a00032dc4076485400065d080ec90a8000cb5101d92150001972203b242a00022fe1975485400045e432ea90a80139ad82dcd215000117f0cb9a42a00022f219734854009cd643ac490a80b0bab8058921500273590ea9242a00526da1f61485400a4da43aa290a8000ab4865452150001e4aa4a8a42a00526d21d31485400061eba4a9b2a6000a5d8394b654c0010ff0aba2ca980023be09745953001c76412e8b2a60008f7815d1654c0051e902ba2ca9800e3ba1f725953000657a06e4b2a6000cad40dc9654c0018deea392ca9800333dcc7259530006e5106e4a9a600495d85dc5534c0010ff0aba6c49801a1f21574d89300047bc0ae9b1260028f4815d3624c00159b07a96c4980162fa1076549300045ec20eca92600387c87595524c0074d904b2aa498003171d9535493000c6e432ea9926003ace86d89324c00117b0f3a6c2982beae60274d853002c5fc3ae9b0a6000cb7815d3614c00196
  | 3 => 0x8b024200c3c75d916048401938e7b22c0908022fa1c64581210061fba8c8b024200c3c751916048401938e6322c09080327d9373581210064e326e6b024200a5d858cb63540090f90ab8ec6a80022fe1171d8d5002c5e422e3b1aa00387c855d362540011ef02ba6c4a800a3d20574d895000536c2e65b12a000ccc329d93254001998643b264a80061f219754c9500143e42ae7b0aa0008ef825cf61540071d904b9ec2a82770f1db745455000c3e432ea98aa0058be849d9215400117b093b242a80061f21975485500051ec34a7b2a8000a3d8694765500016730128ecaa005b0fddb655954009cdb43ee2b2a8000db380dc56550001b6101b8acaa00032dd837159540006d9b06e2b2a8000cb7761c56550001a6eea38acaa02e74edd77059540006d9b8ee0b2a8000db071dc1655002b17b0fb2ec6a005b0f9d765d8d400055a40acbb1a800093f855c7635002d2790ab8ec6a00562f61c61d8d400051ec28c3b1a8000aad82187635000196ae230ec6a005a4fa1f7558d400061fb06eab1a8000d3b60dd56350001a7421baac6a005b0f1d76558d400070f29ecab1a80158bc87595635000156902b2ac6a00526ba1f7258d4000697baee4b1a8000d2c75dc9635000195ec1b92c6a00036ad837258d40006d5086e4b1a8000d2f751c96350001a58ea392c6a004e6da1f7158d400069bbaee2b1a8000d3475dc56350001b4ee5b8ac6a0003691cb7158d400065ac36e2b1a8000db380dc56350001b6101b8ac6a00032dd837158d40006d9b06e2b1a8000d37751c56350001a68ea38ac6a000369dc87158d40006d2390e2b1a8000c3c759856350001958e530ac6a00028f6146158d400061e3a8c2b1a8015a9e83185635000155b0430ac6a00032b1c86158d400065bb88c2b1a8000e97311856350001a76ebb82c6a00034e1d77058d405c6cdb9ee0b1a8000dab72dc16350001b50e5b82c6a00036cdc77058d40006d838ee0b1a80009b980dd9535000127f0abb2a6a00026be097654d400a4d6412eca9a80009b7815d9535002736902bb2a6a00026ee017654d400ac9e43acaa9a806cb3481595535016f67700b2aa6a005a6721d6354d400070eb2ac6a9a80b6b9b8058d535002b27b0bb8aa6a00522f61f63d89400a556412c7b1280148bc8758d625000337101b8ac4a02d76adcb7058940004dcc06eca92800099f835d9525002b33906bb2a4a00026de05765494009cda40aeca9280009bb805d9525002927d0fb2aa4a00030fddb65549400a49e43aa6a928015d1c7354d525002965904a9aa4a00026e603764c9400049fc2aec992801693c855d9325000135f04bb264a00026de05764c94009cda40aec99280009bb805d9325000137700baa64a00066e201754c9403a4ddc02ebb0a80019b8805d7615000127f0ab9ec2a005a4f21
  | 4 => 0x44840117f0eb2ec8908028fa1663d91210051ec2cc7b22421d8bd87183644840147d0a306c8908028f61460d91210054f418c1b224200a9d831836448401972e0306c890a2aada0775d912145d5ac0eebb224200a9e839d7644840153b073aec8908030f5d475d912145d57410ebb22428aaad821d7644851556d023aec890a2ead60475d91210051f42ee7b224200a3d85dcf644851755d05b9ec890a2aab60b73d91214555b40ee7b22428bab581dcf644840147d0b39ec8908028f61673d91214555b408e7b22428bab5811cf644840117d0e29ec8908022f61c53d91214555b40ee1b22428bab581dc3644840196ae3b86c8908032d5c570d91210051f428e1b224200a3d851c3644840153d06386c890802a760c70d912145d57410e1b22428aaad821c3644851556d02386c890a2ead60470d91210045f43ca1b2242008bd87943644840117d0e286c8908022f61c50d91210054f418a1b224200a9d83143644851755d04286c890802ab60850d91214555b408a1b224200ab581143644840117d0f186c8908022f61e30d91210045f43861b2242008bd870c3644840147d0a186c8908028f61430d912145d5741061b224200aad820c3644851556d02186c890802ad60430d912145656b96c9b1a428ccad72193634840d0fd0bba6c6908021f61774d8d2101476c16e9b1a42038f581dd3634857b95ae5a06c6908022fa1f6458d210045f438c8b1a42058be87dd1634840117b01ba2c6908022fa1c7458d210045f43e80b1a42058bc87d01634840b17d09bb2a6908022f6137654d210045fc22eca9a42058bc845d953484011f700bb2a6908063e2017654d210243f43ecaa9a42068de87d8d53484051dd0db92a690a2b2b1db645492101cb643aa6a924200a6c8654d524840d8d8eca9aa490873531cd53549214fcdb43ee8a8a429ecb476dd1514857936d0fb22a290a2f2d1db6454521014bac2ee6a8a42039e682dcd5148401b48e9b92a29080ad921d525452101eb243aa4a8a4202b668654951484056c90ca92a29081b99219525452103733bb2a4a8a4203d66765495148407ac8eca92a29081b991d952545215ddb3c22a4a8a42bbb65845495148401e4ee8a92a290a13599d15254521426b23a2a4a8a42baf24745495148509a48e8a92a290803c9d9152545215d792322a4a8a4283b668354951485076c906a92a29080359dcd5254521005b3c02a4a8a42baf2740549514843b36909b82a2908035954b705452101c7a432ea98a421d9b4845d53148517968edb226290803595d5524c5210e5e241aa498a42008bf845d7604840b17908baec09080e3d60774d81210055cc06e9b024200ab9801d3604840117f08b9ec0908162f21173d812100732a92a3b0242058be86dd160485151790dba2c0908022fa1f64581210061fbaec
  | 5 => 0x90023d60774d8d520045fc22e3b1aa4058bc845c763548094bd0db1aa6a900e5ba1f7254d524ae2e31ee2a9aa40396c82dc553548072d905b82a6a900e1f61774d855201c3ec2ee9b02a404c5c7354f605480117f08b8ec0a90162f21171d81520147b40ee9b2a64008f581dd3654c80d0fd0bba6c2990021f61774d8532006c6196e8b0a64008bf845c7604c80b17908b8ec099003530cb755813260d1ec2cc7b22a2268bd87183645440153d06306c8a8802a760c60d915100557410c1b22a200aad821836454401972e0306c8a8a7a8fa1773d91514ed1ec2ee7b22a200aae82dcf645440155b05b9ec8a8a76ada0773d91514f55ac0ee7b22a226a3e859cf645458347b0b39ec8a8a7a8fa1472d91514ed1ec28e5b22a29dab6811cb645453d56b02396c8a88022fa1c32d91510045ec3865b22a29ea3e850cb645440147b0a196c8a8a76ada0432d91510055ac0865b22a200aba800cb645440157300196c8a8a7a8fa1470d91514ed1ec28e1b22a200a9e831c3645440153b06386c8a8802aba0870d915100556c10e1b22a29dab6811c3645453d56b02386c8a88022fa1e30d91510045ec3c61b22a2008be870c3645440117b0e186c8a8a7a8fa1430d91510051ec2861b22a200aae820c3645440155b04186c8a8a76ada0430d91510055ac0861b22a2008be87883645440117b0f106c8a88022fa1c20d91510045ec3841b22a29ea3e85083645440147b0a106c8a8802a7a0c20d91510054ec1841b22a29dab681083645440156b02106c8a8a770f5d764d8d510070f29ec9b1aa29fc3d7519363544050fb0bba6c6a880e3ba0b74d8d5100476c16e9b1aa2068f581dd363545274e902aa6c6a8af70f5d740d8d510045f43ec8b1aa2008be871916354581878ea326c4a8a7f2d1c464d89510045f43ec8b12a2008be87191625445d47d0db22a4a8a770f1db645495100716326c4a92a2058be84dd9325440117b09bb264a880a1fa1b754c95100746196c8992a200ab980dd36054401573003a6c0a88022fe1173d815102c5e422e7b02a2008bf845cb605440b17908b96c0a88bb0f1d152d815102c5f436e8b02a29d8bc86dd1605440117d0fb22c0a88022fa1c64581515fe1fba8c8b02a2becb77119160544091eb03ba6ca988162fa1f74595310045ec06e8b2a62008be871d1654c40b0f90eaa2ca988c29d205545953102c6e43a86b2a6200e1d5450d654c40117d0fa02ca988162f21f405953101c3e43acaa92622ea3c84595524c44b8b8e6b2aa49880e9b20965549310146f436e6a9262008bf845d7604c40b17908baec0988022fe1172d813102c5e422e5b0262038f581dd3654840b17d0fba2ca908022f60374595210045f438e8b2a42008be87d01654840b1790fa02ca908022f61e65d91210054f41ccbb224200a9d839976
  | 6 => 0x1820428198002da3785387f16534a0000028400059cd206d23c00000000192adc500002800013f80041a5c40000005cbb40024932c0e0fc00000038c570000aa000c1a696266d91fa431b808d4c3445ce6840eacb2d085c918002a2178b480025075c79000000a34002b23f25f4861084de841430000007dc000000000004693a52a0017c91c000000b11533e65cd15311184000bd0b7000000000eb0ea5f0778e552e4e4f30d70004b09f2481040c923121668254ae054362184df19217c5b82624a5d4d0cce80002a748ada7004c000a100018aa694d90231a7180005b28a001158001646c8258003b8a38001545fca28b81a000053083299000c5cc31773f8c9d4ea1e3040019d8000007640c8d54b88113381763800000000000cace58495b6968000006902ed19a0562a00011329000000000004502e168029468b4c618002be51016a5e00076c002b300019c3b08a5f0000a400013c1755609c296aa8f78470003d58d9d30eead8b032e45e7555a80f1a4000e880059000039000266330b5ac158e0000000003e3b00000033caa00021b22e9152696a4dc95d499fa1a68609e83c26a00000000648240000000ac18898b162682d8c70051d21f0a49f53d40444624731e0c1002cf52044800000592000000001944c17ab0f00006d662a100020c0022561c400bc0731f4cd80c2e03b47d865a532440018c18c0564fc0100006aa44000000dc6ec360000ca000f69465a8000a500038804d4406a074c4800000000a7c4cae248046857800146a8d0ab0a5e00000280000a0000040280e0000440480000001800017000000000020320240000b000050088000060040000d002020000000020000001f000004010020100040181300000001803000000020010060280000100a00c0300300200801808000004020010000100a801000034010040020340300100000c0000900803c0300b000004050000040040001300a0080000a00e000000030000180001700005803002000004040010040200000200401c0001300c0080180000c0080000600408400000002004020010120000480f006000008050160000080b0080580400201800000000004058018190000000000400004c0480000402c0280400a000038040020200c8060000140000a00200000006010020020000000200481100001c1b0000120000900000600000803002000008010000180000000400018801000000010040020000000000802c010000000080100600600800004004000000130160040480b0000400001600c028030010040000c8020140040001a0000780001502c0000100000e0487d85dd36154c098baeaa1ec2a9817279d143d85530070eaa287b0aa6aec3d75d036154c0117f08b8ec0a98162f21171d815301c3ec2ee9b1aa4068ed82dd363548051ed03ba6c6a
  | 7 => 0x1f8b359a94f4c883080b221447755c09f0766a88ca6c5cc00076800000000c292f368b90f8800286020c41a310e1805e00032a0017d979000d05130005f8a5019a22000000880000009f49589663a86403997344c51601fe1660483f2ad00033530a364262a8702df26eb44ba9ff000758421bd5ba000d7b380000001219a22cab8298db5eccf8000000006280000052423863a78394bf49c0440181086faf744e00000000000001950003d02f4000000003904d2832304341b2c42fc938dc0000000012b2a661a3615d8c04c69ac6a000424c1c79a325689e9652504b6d08d39fd236c9931308000cc08fae839c93d36b4907223d3da594f8029761f21e23fd07abc4023100e06f38626d1bb1e1dc2e8f59c90008c0ce2f31b443d300254a2000001c85403ec849cd68a3f400208016000000006949757700044264068a77082a900000041c0013f1cf63e00000176000000f600029ac943822d002000000005ca704e1120090a3d84b0621caac0007d60acc4712b900079d1ea0224c700c9b280006cc83a555de560588401e85650b16c54e2194f32133e134319661ec39d1c1c75860000033c0009c4568005449d5901a83280a80023b46292ca92664bece45f9ac000000db8000be5400033a0d00000000000061c828ea5b8b38aa831000890000ac4f2000001131ba4a4b08980b0000001984400017888013a000073322228b09dae33dcc1191ad867a2443d2c2488298c89640680bd4e0f900cccc818524140000001a0000002e0000003c1461f44744745c9e055e000ae9255744291c9d031200096800438139088e8116a244a0e6000000002de000000af05a5c2bfd0480043a6c17a0285162201ba87208084f1810000948f489208676068203000819580004982c1628001901c4608000ae1ec4080047c0002883e3f660569016000c30dd0b460214103b0b2b4000b91a90949084b8642160000000057eb182c8006040000000047800181800000000f100000000196273248050000891560000007f19c000df8a40000003c9565e4000001801f0034d30d9000000cc8002da9a800045006cdc001b9316284f2b194166116b1f0000454002bd0002140003d4ecd1c000003bc4a92c000398504002543a80015f0000001a49917f2786b40012e0004d80000016a8b93900000033d4000009e0018800908ca940f29665ed00529745049d01fa812ae45158a412c67840021a2de358002850d68d40017b3c83196a8000002a00032d1bc38400000000be8539ae24e000160000001e19fb460000003a1b55d60000019b000b64138a93bec016b9ab4d0ba4000f743ec68001c5452011549471269951
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2c0000a101a8150006c001150106000a951181c8cbb21e7921f0c849315a685893854d810eb840a26bc0270000e960001482320132b00cc54862034020190010c00460c01589900cb74585320055264032dd5604c801689900cb644c95161d852455450d654c58552697dd152545215e549a5f6454951485099248454b705452101d19259755493148509524945d5524c52141e5120d7554931484014c9900ca764c95000532640321d93254001434955c461d8d400060e6007518563500018a9801c86158d40005852456558d53500010b79761b51d85400050da5c61dd56150001836861d7615854000607615831d9515000103d9814c76545400050e642511d9515000142d9214476545400050e640511d951500014a59214476545400052c640511d95150001c315044076545400050764c765955150001834811d965545400042b660321d921500014a9900c8764854000728481101d92150001a24865495148540005076507654d524c0012659121953549200056264c70dd12148107644935955148520425892516554921440018b076e057350110004cce5583dc540440013a39260f7150110004e464c8754540440019338521d515011009ccc261755454044001930875d5515011009d8c25975545404402733195e0d5150110004cc654874c54044027390985cd315011009ce864b8348540440273a0985c92150110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x40418000602b26408ecb2aa2a0002825a22047659551500018184b10ebaaa2a022000a4468c875d55150110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x2000600593688811d965545400060109668c875d55150110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x94d
  | 8 => 0x94b
  | 9 => 0x94c
  | 10 => 0x94e
  | 11 => 0x98a
  | 12 => 0x98c
  | 13 => 0x98d
  | 14 => 0x98e
  | 15 => 0x9ca
  | 16 => 0x9cb
  | 17 => 0x9cd
  | 18 => 0x9ce
  | 19 => 0xa0a
  | 20 => 0xa0b
  | 21 => 0xa0c
  | 22 => 0xa0e
  | 23 => 0xa4a
  | 24 => 0xa4b
  | 25 => 0xa4c
  | 26 => 0xa4d
  | 27 => 0xb09
  | 28 => 0xb0c
  | 29 => 0xb0d
  | 30 => 0xb0e
  | 31 => 0xb49
  | 32 => 0xb4b
  | 33 => 0xb4d
  | 34 => 0xb4e
  | 35 => 0xbc9
  | 36 => 0xbcb
  | 37 => 0xbcc
  | 38 => 0xbcd
  | 39 => 0xcc9
  | 40 => 0xcca
  | 41 => 0xccd
  | 42 => 0xcce
  | 43 => 0xd49
  | 44 => 0xd4a
  | 45 => 0xd4c
  | 46 => 0xd4d
  | 47 => 0xec9
  | 48 => 0xeca
  | 49 => 0xecb
  | 50 => 0xecd
  | 51 => 0xa0953
  | 52 => 0xa0954
  | 53 => 0xa0956
  | 54 => 0xb0955
  | 55 => 0xb0954
  | 56 => 0xb4955
  | 57 => 0xbc955
  | 58 => 0xbc954
  | 59 => 0x1549
  | 60 => 0x1409
  | 61 => 0x150a
  | 62 => 0x128a
  | 63 => 0x16c9
  | 64 => 0x1449
  | 65 => 0x168a
  | 66 => 0x12ca
  | 67 => 0x19c9
  | 68 => 0x14c9
  | 69 => 0x198a
  | 70 => 0x134a
  | 71 => 0xb0995
  | 72 => 0x138b
  | 73 => 0x124b
  | 74 => 0xd4995
  | 75 => 0x1709
  | 76 => 0x15c9
  | 77 => 0x168b
  | 78 => 0x12cb
  | 79 => 0x1a09
  | 80 => 0x1649
  | 81 => 0x198b
  | 82 => 0x134b
  | 83 => 0xb49d5
  | 84 => 0x138c
  | 85 => 0x124c
  | 86 => 0x150c
  | 87 => 0x128c
  | 88 => 0xec9d2
  | 89 => 0xec9d5
  | 90 => 0x1a49
  | 91 => 0x17c9
  | 92 => 0x198c
  | 93 => 0x134c
  | 94 => 0xb0a14
  | 95 => 0xbca14
  | 96 => 0xb89
  | 97 => 0x138d
  | 98 => 0x1849
  | 99 => 0x1489
  | 100 => 0x124d
  | 101 => 0x289
  | 102 => 0xd09
  | 103 => 0x150d
  | 104 => 0x1889
  | 105 => 0x1609
  | 106 => 0x128d
  | 107 => 0x409
  | 108 => 0xeca12
  | 109 => 0xe89
  | 110 => 0x168d
  | 111 => 0x18c9
  | 112 => 0x1789
  | 113 => 0x12cd
  | 114 => 0x589
  | 115 => 0x1049
  | 116 => 0x198d
  | 117 => 0x1949
  | 118 => 0x1a89
  | 119 => 0x134d
  | 120 => 0x749
  | 121 => 0xbca55
  | 122 => 0x138e
  | 123 => 0x124e
  | 124 => 0x150e
  | 125 => 0x128e
  | 126 => 0xeca55
  | 127 => 0x168e
  | 128 => 0x12ce
  | 129 => 0xb4b15
  | 130 => 0xbcb15
  | 131 => 0xbcb14
  | 132 => 0xd4b15
  | 133 => 0xb0d55
  | 134 => 0x170a
  | 135 => 0x15ca
  | 136 => 0x16cb
  | 137 => 0x144b
  | 138 => 0x160a
  | 139 => 0x148b
  | 140 => 0x40a
  | 141 => 0x1a0a
  | 142 => 0x164a
  | 143 => 0x19cb
  | 144 => 0x14cb
  | 145 => 0x154c
  | 146 => 0x140c
  | 147 => 0x1a4a
  | 148 => 0x17ca
  | 149 => 0x19cc
  | 150 => 0x14cc
  | 151 => 0xd4bd5
  | 152 => 0xbcd55
  | 153 => 0x154e
  | 154 => 0x140e
  | 155 => 0x16ce
  | 156 => 0x144e
  | 157 => 0x1a8a
  | 158 => 0x148e
  | 159 => 0x74a
  | 160 => 0x1a4b
  | 161 => 0x17cb
  | 162 => 0x1a0c
  | 163 => 0x164c
  | 164 => 0xecd55
  | 165 => 0x170e
  | 166 => 0x15ce
  | 167 => 0xb0a095c
  | 168 => 0xbca095c
  | 169 => 0x94a13
  | 170 => 0x94a14
  | 171 => 0x94a16
  | 172 => 0x94b14
  | 173 => 0x1a1651
  | 174 => 0x180c
  | 175 => 0x124a14
  | 176 => 0xb1515
  | 177 => 0xb5695
  | 178 => 0xbd995
  | 179 => 0x180a12
  | 180 => 0x139255
  | 181 => 0x151295
  | 182 => 0xed695
  | 183 => 0xed995
  | 184 => 0x1692d5
  | 185 => 0x199355
  | 186 => 0xd4bcb1d
  | 187 => 0xbcb0d5d
  | 188 => 0xb0296
  | 189 => 0x180a
  | 190 => 0x29256
  | 191 => 0x75352
  | 192 => 0x1a0d
  | 193 => 0x1a8ed2
  | 194 => 0xd4752
  | 195 => 0xe8ed2
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1061
  | 6 => 2496
  | 5 => 843
  | 4 => 51
  | 3 => 4
  | 2 => 2
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
  | 7 => packedAt gbK7 (43493+((h/353+packedAt gbK7 (39257+(h % 353)*12) 12) % 2050)*12) 12
  | 6 => packedAt gbK6 (129792+((h/832+packedAt gbK6 (119808+(h % 832)*12) 12) % 2996)*13) 13
  | 5 => packedAt gbK5 (52828+((h/281+packedAt gbK5 (49737+(h % 281)*11) 11) % 1113)*11) 11
  | 4 => packedAt gbK4 (3672+((h/17+packedAt gbK4 (3570+(h % 17)*6) 6) % 62)*7) 7
  | 3 => packedAt gbK3 (327+((h/1+packedAt gbK3 (324+(h % 1)*3) 3) % 8)*3) 3
  | 2 => packedAt gbK2 (186+((h/1+packedAt gbK2 (184+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ffffe1c387f0fc030e03fffff20607e19c0ff
  | 1 => 0xc38781e03f87f1ffff00383c1f5193a8667c93
  | 2 => 0x3f801ffc007fe003fffc03fe09e1c31878f1c
  | 3 => 0xfc0001fffff800003fffffc000e01fc1f80fe0
  | 4 => 0x1ffffffffffc000000000ffe001fff000
  | 5 => 0xfffffe00000000000000000000fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4088404100a0242002009048800200208c025
  | 1 => 0x41c5086008819091b90190a8561091a8221c92
  | 2 => 0x2d410a84005a4049a4a803342161430870518
  | 3 => 0xa8002152ad5000092495268004e00ac1700ac0
  | 4 => 0x2000459f3666492e0006030188eb6001dde000
  | 5 => 0x33667802044080300818042210fddf7c000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefeaafeecfaa8fefefeaafeecfaa8fefefeaafeecfaa8fefefeaafeecfaa8fefefeaafeecfaa8fefefeaafeecfaa8fefefeaafeecfaa8fefefeaafeecfaa8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_17059
namespace PEqualNP.Outside.L_meta_17059
open PEqualNP.Outside.L_meta_17059.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 64 := (concat bs0_4_0 bs0_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 40 := (concat bs0_5_0 bs0_5_32)
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 10 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 60 := (concat bs1_3_0 bs1_3_32)
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
theorem bs1_4_128 : Interval s1Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_160 : Interval s1Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 165 := (concat (concat bs1_4_0 (concat bs1_4_32 bs1_4_64)) (concat bs1_4_96 (concat bs1_4_128 bs1_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 50 := (concat bs1_5_0 bs1_5_32)
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
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 92 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := (concat bs2_5_0 bs2_5_32)
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
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 24 := bs3_3_0
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
theorem bs3_4_96 : Interval s3Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 117 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 46 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 14 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_128 : Interval s4Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_160 : Interval s4Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_192 : Interval s4Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_224 : Interval s4Atlas 3 224 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 227 := (concat (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 bs4_3_96)) (concat (concat bs4_3_128 bs4_3_160) (concat bs4_3_192 bs4_3_224)))
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
theorem bs4_4_128 : Interval s4Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_160 : Interval s4Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_224 : Interval s4Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_256 : Interval s4Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_320 : Interval s4Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_352 : Interval s4Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_416 : Interval s4Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_448 : Interval s4Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_512 : Interval s4Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_544 : Interval s4Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_608 : Interval s4Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_640 : Interval s4Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_704 : Interval s4Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_736 : Interval s4Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_800 : Interval s4Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_832 : Interval s4Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_896 : Interval s4Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_928 : Interval s4Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_960 : Interval s4Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_992 : Interval s4Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1024 : Interval s4Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1056 : Interval s4Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1088 : Interval s4Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1120 : Interval s4Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1152 : Interval s4Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1184 : Interval s4Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1216 : Interval s4Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1248 : Interval s4Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1280 : Interval s4Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1312 : Interval s4Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 bs4_4_192) (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)))) (concat (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 (concat bs4_4_416 bs4_4_448))) (concat (concat bs4_4_480 (concat bs4_4_512 bs4_4_544)) (concat bs4_4_576 (concat bs4_4_608 bs4_4_640))))) (concat (concat (concat (concat bs4_4_672 bs4_4_704) (concat bs4_4_736 (concat bs4_4_768 bs4_4_800))) (concat (concat bs4_4_832 bs4_4_864) (concat bs4_4_896 (concat bs4_4_928 bs4_4_960)))) (concat (concat (concat bs4_4_992 bs4_4_1024) (concat bs4_4_1056 (concat bs4_4_1088 bs4_4_1120))) (concat (concat bs4_4_1152 (concat bs4_4_1184 bs4_4_1216)) (concat bs4_4_1248 (concat bs4_4_1280 bs4_4_1312))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_64 : Interval s4Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_128 : Interval s4Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_160 : Interval s4Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_224 : Interval s4Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_256 : Interval s4Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_320 : Interval s4Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_352 : Interval s4Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_416 : Interval s4Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_448 : Interval s4Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_512 : Interval s4Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_544 : Interval s4Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_608 : Interval s4Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_640 : Interval s4Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_704 : Interval s4Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_736 : Interval s4Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_800 : Interval s4Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_832 : Interval s4Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_864 : Interval s4Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 890 := (concat (concat (concat (concat bs4_5_0 (concat bs4_5_32 bs4_5_64)) (concat (concat bs4_5_96 bs4_5_128) (concat bs4_5_160 bs4_5_192))) (concat (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)) (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 bs4_5_416)))) (concat (concat (concat bs4_5_448 (concat bs4_5_480 bs4_5_512)) (concat (concat bs4_5_544 bs4_5_576) (concat bs4_5_608 bs4_5_640))) (concat (concat bs4_5_672 (concat bs4_5_704 bs4_5_736)) (concat (concat bs4_5_768 bs4_5_800) (concat bs4_5_832 bs4_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := (concat bs4_6_0 bs4_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_7_0 : Interval s4Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_7 : Interval s4Atlas 7 0 1 := bs4_7_0
theorem alls4 : ∀ k ≤ 7, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
  · exact alls4_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
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
theorem bs5_4_64 : Interval s5Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 91 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 2 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 4 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 51 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_832 : Interval gbAtlas 5 832 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 843 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608))) (concat (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832)))))
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
theorem allgb_6 : Interval gbAtlas 6 0 2496 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))))) (concat (concat (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)))) (concat (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056))) (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)))))) (concat (concat (concat (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664))) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824))))) (concat (concat (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984))) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)))) (concat (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304))) (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)))))))
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
theorem bgb_7_1056 : Interval gbAtlas 7 1056 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1061 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))) (concat (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)) (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 36, 52),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefeaafeecfaa8fefefeaafeecfaa8fefefeaafeecfaa8fefefeaafeecfaa8fefefeaafeecfaa8fefefeaafeecfaa8fefefeaafeecfaa8fefefeaafeecfaa8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124202 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_17059.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.or,[2,6]⟩,⟨.and,[0,7]⟩,⟨.or,[0,4]⟩,⟨.and,[2,6]⟩,⟨.or,[5,10]⟩,⟨.and,[3,11]⟩,⟨.or,[9,12]⟩,⟨.or,[1,10]⟩,⟨.or,[8,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_17059

open PEqualNP.Outside.L_meta_17059 in
theorem PEqualNP.Outside.L_meta_17059 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
