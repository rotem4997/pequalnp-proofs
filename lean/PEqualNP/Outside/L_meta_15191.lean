import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15191.Model
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


end PEqualNP.Outside.L_meta_15191.Model

namespace PEqualNP.Outside.L_meta_15191
open PEqualNP.Outside.L_meta_15191.Model
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

def SBf (j : Nat) : Nat := [2, 2, 4, 5, 5, 7].getD j 0

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

end PEqualNP.Outside.L_meta_15191

namespace PEqualNP.Outside.L_meta_15191
open PEqualNP.Outside.L_meta_15191.Model
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
end PEqualNP.Outside.L_meta_15191
namespace PEqualNP.Outside.L_meta_15191
open PEqualNP.Outside.L_meta_15191.Model
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
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffff8b
  | 2 => 0xffffffffffffffffffffffffffffffffffff95
  | 4 => 0x26
  | _ => 0
def s1Atlas : Atlas := ⟨1,rawDecor 21 s1Pos s1Neg, 0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15191
namespace PEqualNP.Outside.L_meta_15191
open PEqualNP.Outside.L_meta_15191.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffd7e0f83fff801ff803ffff00ff007fe38f
  | 4 => 0xffffe7ff003fffffe00003ffffff00007ffc0f
  | 5 => 0x7bffffc1fffffffffc01ffffffff807ff0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffff802211042592a4ca28a2574b4b56a5adb7
  | 1 => 0xffff804422084aa4c9545144ab9595a74ad6db
  | 3 => 0xffffa89e4750937691a69a693dc0e63273638d
  | 4 => 0x1908f7a11c471dc76391cee6c0c47c7c0e
  | 5 => 0x610843de0781e0783e1f0f8f8f8607b60
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0x88888888880000008888888888000000888888888800000088888888880000008888888888000000888888888800000088888888880000008888888888000000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15191
namespace PEqualNP.Outside.L_meta_15191
open PEqualNP.Outside.L_meta_15191.Model
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
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x7fff00ffffffffc03fff80fffffff807f8ffc7
  | 2 => 0xffffff00ff807fffffffff01fc03ffffff18ff
  | 4 => 0x83ffffff00007fffc03ffffe0003fff80fe0f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x104b092124851444848a8b162d545b4a936b5b
  | 1 => 0xa095d84a4d4a28a3a915c0ab569aa8c5a8b5c5
  | 2 => 0x412652e88a534d293227558198c335974d18ae
  | 4 => 0x76389c8cec6c723223b9e6cd0313c6e18ee0f0
  | 5 => 0x7bc0e0f0f0707c3c3c3e78f1e3e207060fde00
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xa8a88888a0a08080a8a88888a0a08080a8a88888a0a08080a8a88888a0a08080a8a88888a0a08080a8a88888a0a08080a8a88888a0a08080a8a88888a0a08080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15191
namespace PEqualNP.Outside.L_meta_15191
open PEqualNP.Outside.L_meta_15191.Model
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
end PEqualNP.Outside.L_meta_15191
namespace PEqualNP.Outside.L_meta_15191
open PEqualNP.Outside.L_meta_15191.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x400000060a7000954000002a4889614381a34e98c9e20807a52630017361ca0100911211a0001d1608c0010a00005668f80520800c020004628e005001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1ba180000025858c000b8000200000061f8000001d148000000009800d238000000000000010800ca1002b8000001e800000002500001c000013800001a48000000007000000000000000000000d8000001422802b04802c9780002d000000240000000e0f80000000000000000000000680000000000000000000000a091188030080000000001f00000003a9952a99171d80001600011a000010001e000027ad920000000a802800000012800000000000021c80001b2c00000002802900002213000004000000000000000000000000000028800018a308a600002a0f0000001a8000208007800e800b0000168000001980158027001805000000268000110000000000000000018040200000140201000080400008040201000000000008000001bb28e877551d0ef4a121de54243afa9a855c5350aeea2a15d14542bda8285785050a7ea8994f15132bba8a6574514caf6a0995e14132af29e835d53d06bea6a0d714d41b7a92836c52506f6a0a0de141419f2a4633d548c73ca918e755231af28c635e510c7aca218f590431eaa08635e53c86baa790f50c7219faa2433c54486bea690d714d21bda824378504867ca810cf55021ea188435e53902baa7206794e40cea9c819e319033863204f94240cf188819c311027ca0206e940409f2a6613d54cc37081184fd51309e2a2616f524c2d8a4985dd4530ba28a61b8404c27ca9904f55320dc206413f5448278a89057d4d20ae29a417751482e8a2905794c20aea9841b8400827ca9884f55310dc206215e53842baa708750c6109faa2213c54442bea6885714d10b7a92216c52443a862086e10010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x6a8090946821d6070180018000004f0002210048e181548c6986055231a5592510c6c46250431b4181410c6386055021c555031086546154e40a5185539021d658c640a658e50103285210130cc144404c2546154c20c654c40083903110010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xc100040000920e0b24a218d1070550310864838ac728081441c55310020
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 16
  | 2 => 4
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
  | 4 => packedAt s5K4 (2754+((h/30+packedAt s5K4 (2484+(h % 30)*9) 9) % 257)*8) 8
  | 3 => packedAt s5K3 (633+((h/5+packedAt s5K3 (608+(h % 5)*5) 5) % 26)*5) 5
  | 2 => packedAt s5K2 (200+((h/1+packedAt s5K2 (196+(h % 1)*4) 4) % 14)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe01fffffffffe03fff03fffffffc03f8fffc7
  | 1 => 0xfffe01fffe03ffffffffc0fff00ffffff1f8ff
  | 2 => 0xfffffe03ffffffffffffff03fffffffffe1fff
  | 3 => 0xfffffffc0003fffc07fffffc000fffc07fe0f8
  | 4 => 0xfffffffffffc000007fffffffff000007fff00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x97b05224b228a23891700b2cb552c61c86ebc3
  | 1 => 0x2a93d0891499644922d2c05553055a7531785d
  | 2 => 0x4c2485a22852489244a555026a69acaa5a15ae
  | 3 => 0x71391933b16391207739a6980c4e370c6fa0f0
  | 4 => 0x81c1e1c3c183e1c387ce38e38f8038307dde00
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xe8a0c080e8a0c080e8a0c080e8a0c080e8a0c080e8a0c080e8a0c080e8a0c080e8a0c080e8a0c080e8a0c080e8a0c080e8a0c080e8a0c080e8a0c080e8a0c080, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15191
namespace PEqualNP.Outside.L_meta_15191
open PEqualNP.Outside.L_meta_15191.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x6ca0ac181cc814d05cd4e4390894c01098e06879140064005800011028b084f454dcc4002c0c8cbc20f800048834b8000000400044600000a800fcd8007cb47024a400084ce8cd0c0030804904743ced00f090509c4401a0c6c03600000801010018020038a340408000ffd5003fe5400ff55003fc5400ffd4c03fe5300ff54c03fc53007fd0c01fe43007f50c01fc4300ffd48037f5200ff94803fd52005f54803fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc3200ffd4403fe51005f94403fd5100ff144037c51007fd0401fe41007f50401fc41007fcc401fe3100778c401fd31007f0c401dc31007fc8401fe21007f48401fc2100ffd4003fe50005f94003fd5000ff140037c50007fd0001fe40006f90001fd40007f10001bc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x8a4000f70c520006fca09002f7c5048001df2024000ef10120007f64090003ee20480117fb284001bf99420046fcca100067e65080117eb284000df59420004faca10006fc65080017fb204006bf99020005fac81001afc64080017fb184005bf98c20007bcc610002de63080017eb184000f758c20005bac610016fc63080157f3104008dfd4820006faa410003ef3208001f61904000bf98420005fac2100037e5108011be2884000f78c420007b86210003ee2108001f61084009bf98020006fca0100237c5008001df2004000ef10020007de4010003fa2008001f69004000fe48020025fecb88006fe65c4009bf32e20019f99710025facb880037d65c40013eb2e2001bf19710005fec98801afe64c4001df3262000af99310005fac988003bd64c40015eb262006bf19310005fec788016fe63c40017eb1e2005bf18f10005fec588002fe62c40017eb162000bf18b10026fea5880037d52c4001bf28e2004df14710007bc6388003dc31c4001bf2862004df14310007f68188003be40c4001de2062000fe10310007708188003fb20c4001fc1062003bfd961000dfccb0800f7e65840033f32c2003bf59610006facb080027d65840037e32c2000bfd9210035fcc908002fd648400d7e3242000bfd8e1002dfcc708003de63840016f31c2000bf58e10007bac708002dd638400b7e31c2000bfd8a10005fcc508002fd62840017e3142003dfd4a10006faa50801efd6184001bf28c2003df14610007ee6308003de3184001ee18c2000fd0c610007a86308003f72184001fa10c2002bf98210006fca10800f7c5084001df2042000ef10210007ee2108003fb108400f7fb2a2000dfd9510004feca88006fe654400f7eb2a2001bf1951003ef8ca880067c65440017fb222000efd91100057ec88801afe64440017eb222006bf1911000778c888002bc64440017fb1a2000f7d8d10005bec688016fe63440017eb1a2005bf18d10007b8c688002dc63440017fb122000fbd8910005dec488002fe62440017eb122000bf18910007d8c488002ec624400fbfa922000df54910006fca28801f7c5144001ef18a2000f70c510006fca08801f7c5044001df2022000ef10110007f62088003f610440057fb282000dfd9410004feca08006fe65040057eb282001bf19410016f8ca080067c65040017fb202006bf99010005fac80801afc64040017fb182005bf98c10005fac608016fc63040017fb102000bf98810005fac408002fc6204005bfa902000df54810025fcc2080037e5104005be2882000fdcc410007bc6208003dc3104001fa1882000f50c410007ee4208003f421040077f3002000df94010016f8a008003fb4004001df2002000ef10010007f08008003b84004001fd9002000fe08010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x2fd62cc01fbfa966000df54b3002fbe6598003dd32cc0017f30e6000bf58730006fca39803f7c51cc001ef18e6005f70c730006fca19803f7c50cc001df2066000ef1033006dfecb18006fe658c01b7eb2c6001bf19630005fec91801afe648c0017eb246006bf19230075fac718002fe628c0017eb14600ddfd4a30006faa518003de328c001ee1946000bf98630005fac3180037e518c01bbe28c6000f78c630007b86318016fe608c001bf284600ddf142300077c8118003bc408c001ef9846005fecc230075feca980037f654c0013fb2a6001bf99530075faca98006fc654c01dbe32a60019f19530005fec898003bf644c0015fb226006bf99130005fac89801afc644c001de3226000af19130077bca69803bdd534c001efa1a6000f710d30005fec498003ef624c00177b126000bf18930007d8c498002ec624c01dbfa926000df54930007be6498003dd324c0017fb0a6000fdd8530005eec298002fc614c001fa30a6000bd18530006fca29803b7c514c001ef18a6000f70c530006fca09803b7c504c001df2026000ef1013002ff66098003de304c00b7fb286001bf99430065faca18016fc650c00b7fb206006bf99030005fac818016fc640c00b7f3186000bf98830005fac4180337f520c001bea906000f78c83002fb86418002fe610c0017eb086000df94430066f8a218003de310c00bee188600dbf98030006fca0180337c500c001df2006000ef1003002fbe6018017fa300c001ee9806005fe4c030055fecb90006fe65c8015bf32e40019f99720055facb900037d65c80013eb2e4001bf19720005fec99001afe64c8001df3264000af99320005fac990003bd64c80015eb264006bf19320005fec790016fe63c80017eb1e4005bf18f20056fea5900037d52c80017f30e4000bf58720006fca39002b7c51c8001ef18e4000f70c720006fca19002b7c50c8001df2064000ef1032004dfecb100037f65880013fb2c4001bf9962004dfacb10006fc6588013be32c40019f19620005fec91001afe64880017eb244006bf19220005fec710016fe63880017eb1c4005bf18e2005dfac5100277f5288001bea944000fbcca20007d86510002fe61880017eb0c4000df9462004ef8a310003de3188001ee18c4000fb88620007d84310022fe6088001bf2844009df142200077c8110003bc4088001f79044000fec822005dfeca900037f65480013fb2a4001bf9952005dfaca90006fc6548017be32a40019f19520005fec890003bf64480015fb224006bf99120005fac89001afc6448001de3224000af19120005fec690003df63480016fb1a4005bf98d20005fac690016fc6348001ee31a4000b718d2005efea4900037d52480017fb0a4000fdd8520005eec290002fc6148001fa30a4000bd18520006fca29002f7c5148001ef1
  | 2 => 0x400077c8720003bd4390001de21c8000bf98a40005fac5200477f5290001bea948000efd0a400077c8520003bd4290001de2148000bf98640005fac3200037e5190023be28c8000efd06400077c8320003bd4190001de20c8000f78c640007b8632001afe6090001bf2848011df142400077e812001bfb4090023dfb2c8011ef9964008f7acb20047bc6590001dfb1c8000ef98e400073cc720003bd6390001ceb1c8000ef18e4008f7ea720047be5390023dea9c8011ef14e400077ec520003be6290001deb148000ef18a4008f7ea5200473f5290023df2948011ef54a400067aa520047bc5290001df9948000ef8ca400077a6520003bc3290001dfb0c8000ef986400077ac320003bc6190023dfa8c8011ef946400067ca320047bd5190023de28c8011cf146400077e6320003be3190001cf18c8000ef4c6400077863200039c3190001df90c8000ef886400077a4320003bc21900215f3048011efd424008f7ca1200033e5090023dea848011ef1424008e78a12004aff6550001bfb2a80009fd954000dfccaa004afd65500037e32a8012df1954000cf8caa0002ff635000b7e31a8000bfd8940005f8c4a004b7f5250001bea928000bfd8540005f8c2a00037e5150025be28a8000f78c540007b862a00037e5050025be2828006fed01400077c80a001aff65100037f3288010bf59440035f8ca2001afe6410021dfaa08006ef950400877aa82001bbc541000b7f3188000bf58c400377e8620003be4310001dea188006ef10c40005fcc420002fd6210021bfa908000df548400377e8420003be4210001dea108006ef10840005fcc220002fd6110001bf2888010df144400377e8220003be4110001dea088006ef10440007bc6220003dc31100237f3008000df94040086f8a02001bbf401000dfd2008000ef50040037f2802001bbf6510021df3288010ef5944003778ca2001bbf6310001df3188000ef58c4003778c620043bf5310021df2988010ef54c4008778a62001bbf6210001df3108000ef5884003778c420043bf52100219fa908010ef948400877aa4200033d5210021de2908000efcc8400077c6420003bd3210001de1908006efd84400077cc220003bd611000dde3088010efd44400877ca2200033e5110021dea888010ef1444008678a220003bf3110001df1888000e78c4400077a6220003bc3110001ce1888000efc84400077c4220003bd2110001de1088000ef9804008d7cc020003ba6010021dfa808010ef940400067ca020043bd5010021de2808010cf1404002dfecb98006fe65cc00bbf32e60019f9973007dfacb980177d65cc0013eb2e6005bf1973002dfec99801afe64cc00bdf3266000af99330005fac998017bd64cc0015eb266005bf1933002fbca79803fdd53cc001efa1e6005f710f30005fcc59800
  | 3 => 0xe2806216bfd972100dfccb9085b7e65c84033f32e4216bf59721006facb908027d65c84037e32e4200bfd9321035fcc990802fd64c840d7e3264200bfd8f2102dfcc790803de63c84016f31e4200bf58f21007bac790802dd63c840b7e31e4216dfd4b21006faa5908037e51c842dbe28e4200f78c721007b86390802fe60c84017eb064216df143210adfecb108037f65884013fb2c4201bf996210adfacb10806fc658842bbe32c42019f19621005fec91081afe64884017eb244206bf19221005fec710816fe63884017eb1c4205bf18e210bdfac5108577f5288401bea944200fbd0a21007d88510852fe6188401bf28c4215df14621007bc6310803dc3188401f790c4200fdc8621005fcc110802fd608842bbe2844217bfd9521006feca908027f65484037f32a4217bf5952100df8ca9085f7c65484033e32a4200bfd91210077ec890802bf644840d7f3224200bf59121035f8c890803bc64484015e3224200bfd8d21007bec690802df634840b7f31a4200bf58d2102df8c690803dc63484016e31a4217dfd4921006faa4908037e514842fbe28a4200f78c521007b86290803f72148401f710a4200bfd8121007f6c090802fb60484017e3024200fe18121005f0c09085f7c50484297fb284201bf994210a6fcca108067e65084297eb284200df59421004faca10806fc65084017fb204206bf990210077cc810802be64084017eb204200ef590210057ac81081afc64084017fb184205bf98c21005fac610816fc630842d7f3104214dfd4821006faa410803ef4208401f62104215bf98421006fca2108537c5108401ef1884200f70c421007de4210803f62108401f69084200fd48421005fcc010802fd6008429be2804200dfd9250006fcc9280037d6494001be324a000dfd8e50006fcc7280037d6394001be31ca000dfd0e50006fc87280037d4394001be21ca000dfd8a50006fcc5280037d62940013eb14a000df18a50006fe85280037e4294001bea14a000df10a50006fe65280037e3294001be994a000df0ca50006fec3280037e61940013f30ca000df58650006f8c3280037f4194001bf20ca000df50650006f883280037f3194001bf18ca000d78c650006fa63280037c3194001ae18ca000dfc8650006fc43280037d2194001be10ca001df9825000cfcc1280077a609400d7fb2e8001bf99740036fccba00067e65d00277eb2e8006df59740004facba001afc65d000b7f31e8000bf58f40005fcc5a0002fd62d0027bfa968000df54b40005fcc3a0002fd61d0001bf28e8013df14740007bc63a0003dc31d0001bf2868013df1434008dfecb20006fe65900237eb2c8001bf19640095fac920047bf5490023df2a48011ef5524008f78a920016fe6390001ef31c8000b798e40005fac720003dd63900016eb1c8000efd0e
  | 4 => 0x876fe6110401bf288821cdf144410377e822081bf64110401dea088206fd50441005fcc020802fd6010439be2808205bfd973100dfccb988177e65cc4033f32e621bbf5973102efacb988027d65cc40b7e32e6205bfd9331035fcc998802fd64cc40b7e3266200bf98b31005fac59886f7f52cc401bea966200df947310def8a398802fe60cc4017eb06621bdf143310cdfecb18806fe658c4337eb2c6201bf19631005fec91881afe648c401df3246200af99231005fac918803bd648c4015eb246206bf192310d5fac718867df538c433ef29c6219f754e310cfb8a718803df438c401ef21c6200f750e31007b88718802fe628c4017eb146219dfd4a31006faa518803df328c401ef1946200f74ca31007b86518816fe618c401bf28c6219df14631007be6318817f7318c4017f3046200bf582310cef8a118867df658c433ef32c6219f7596310cfb8cb18803df648c401ef3246200e799231007bac9188039d648c401ee3246219f7d52310cfbca918867dd548c433ee2a46200f7d8a31007bcc518803dd628c401ee3146219f7d4a310cebea518867de528c433eea946200d754a310cfb8a518803df428c401ef2146200f750a31007b88518862de618c433efa8c6219f794631006bca318867dd518c433ee28c6219d714631007be8318803de418c401eea0c6200f710631007bec118803de608c401eeb046200f7182310cfbea118867de508c433eea846219f7142310ceb8a11886aff654c401bfb2a62009fd953100dfcca9886afd654c4037e32a621adf1953100cf8ca98802ff644c40d7f3226200bf59131035f8c898802ff624c4017e312621adfd4931006faa4988037e514c435be28a6205fdcc531007bc6298802ff604c4017e302621adf1413102dfeca18806fe650c4317eb286205bf1943102dfec81881afe640c4017eb206205bf1903102dfcc618863df530c40bef2986218f754c3102fb8a618803df430c40bef2186200f750c3102fb88618802fe620c4017eb106218dfd4831006faa418817df320c401ef1906200f74c83102fb86418866fe610c401bf2886218df1443102fbe6218817f6310c401ee9886205fd4c431005fcc018802fd600c431be2806205f7d94310c7bcca18863dd650c40bee3286205f7d9031007bcc818803dd640c40bee3206218f7d50310c7bca818863dd540c431ee2a06205f7d8831007bcc418803dd620c40bee3106218f7d48310c6bea418863de520c431eea906200d7548310c7b8a418803df420c401ef2106200f750831007b88418803de610c4336f3086200f5984310c7bea218863de510c401af2886218f7544310c7b8a2188635c510c401efa086200f790431007ba8218803dc410c40befb006200f798031007bac018817dc600c431efa806218f7940310c7baa018863dc500c431a
  | 5 => 0x4b32005fcc399002fd61cc847be28e6400bf98332005fac19908f7c50cc8437fb2c6401bf9963210efccb190067e658c8437eb2c6400df59632004facb19006fc658c8017fb246406bf99232005fac91901afc648c8457eb1c6421f794e3210fbaa719003df438c801ee21c6405bf98a3210efea5190037d528c801ef9946405fbcca32005fcc319002fd618c843be28c6400bf98232005fac1190877c508c8457fb2a6401bf99532115faca99006fc654c8017fb226400efd91320057ec89901afe644c8017eb226406bf1913200778c899002bc644c845bfa926400df5493202fde6499003de324c8017fb0a6400bf18532116f8a299002ff604c8017e3026422df1413202dfeca19006fe650c80bbf32864019f99432105faca190177d650c8013eb286405bf1943202dfec81901afe640c8017eb206405bf1903202dfcc619017de530c841eea986400f7d0c3202fb88619086fe620c841bfa906400df5483202fbe6419017ee320c801ee9906405fb4c832005fcc219002fd610c841be2886400bf98032005fac0190837c500c801bfb24a200df99251006fac9288037c6494401bfb1ca200df98e51006fac7288037c6394401bfa1ca200df90e51006fa87288037c4394401bfb14a200df98a51006fac5288027d6294401be314a200dfd0a51006fc85288037d4294401be214a200dfcca51006fc65288037d3294401be194a201df9865100cfcc328807766194401bfb04a200df98251004fcc1288037d6094401be304a206bfd974100dfccba081b7e65d04033f32e821fbf59741036facba08027d65d040d7e32e8206ef953410ff7aa9a0816fe63d040def31e8200b798f41005fac7a081bdd63d04016eb1e8200ef90f410377887a0802fe62d04017eb16821fdfd4b41006faa5a081bbf42d0401dea168200df947410fef8a3a0802fe60d04017eb06821fdf143410edfecb20806fe659043b7eb2c8201bf196410f5fac920816fe63904017eb1c8200bf98a41005fac5208777f5290401bea948200ef90a4100778852081afe6190401bf28c821ddf146410077e832081bf741904017f3048200bf582410eef8a12087aff6550401bfb2a82009fd954100dfccaa087afd65504037e32a821edf1954100cf8caa087bbe545043ddeaa28200bfd8d41007bec6a0802df635040b7e31a8200f718d41005b8c6a0803be4350401de21a8200bfd8941007dec4a0802ef62504017e3128200fb18941005d8c4a087b7f5250401bea928200efd09410077a84a08037e515043dbe28a8206fdd05410077c82a0802ff6050401fdb028200bed8141005f8c0a0803f860504017c302821edf14141035feca20806fe65104397eb288206bf19441035fcc820816fe63104017eb188200bf98841005fac4208737f5210401bea908200ef90841037788420
  | 6 => 0x2c0180000000e00404410800000000030180160040f80f0080080800000201c340180020000001300002c028070000040180b00e008000010040240000000c004018000000040381400807c0100000001c060120101100000700204c010020300080000201a010000000040080500100400807801020010058000000000680702a0000202606607c130000220000081aff65d0c037f32e862bbf59743035f8cba1802fe62d0c017eb16862bdfd4b43005fcc3a1802fd61d0c57be28e8600bf98343005fac1a18af7c50d0c0b7fb2c8601bf99643155facb21816fc6590c537eb248605bf98e4302f7e872181bdf4390c017f3148600bf58a43156fea521802fe6190c017eb0c862adf14643005fcc121802fd6090c55be2848629bfd954300dfccaa18a6fd6550c037e32a8606f7d0d4302f7c86a1802ff6250c017e3128629dfd4943005fec2a1802fc6150c53be28a8600bfd8143005f8c0a18a77c5050c0b7fb288601bf9944302efcca218067e6510c517eb288605df59443004faca21816fc6510c0d7f3208605bf98c4302f7e8621817de4310c0bdea188606f750c43005fcc421802fd6210c51bfa908600bf98443005fac2218a37c5110c017f3008600bf58043146f8a0218037f6454801bf322a400df59152006f8c8a90037f6354801bf31aa400df58d52006f8c6a90037f4354801bf21aa400df50d52006f886a90077f62548033fb12a401dbd8952006fec2a90037e6154801beb0aa400df18552004f8c2a90037f6054801bf302a400df58152006f8c0a90027c605480d7fb2e8401bf9974213dfacba101afc65d080b7f31e8400bf58f4213efea5a10037d52d08017f30e8400bf5874213ef8a3a1002fe60d08017eb068427df1434212dfecb21006fe659084bbf32c84019f9964212dfacb210037d65908013eb2c8401bf19642135fac921097be549084bdeaa48405bf98e42005fac721003be4390801de21c8406bf98a4212efea5210037d5290801dfa148406fbd0a42005fcc321002fd619084bbe28c8400bf98242005fac1210977c509084d7fb2a8401bf99542135facaa1006fc65508017fb1a8400f7d8d42005bec6a1016fc6350801ee31a8400b718d42136fea4a10037d525080df7a128400ef90942005fec2a1002fc615084dbe28a8400bfd8142005f8c0a109b7c505080d7fb288401bf99442036fcca210067e65108497eb288406df59442004faca2101afc651080d7f3208406ef950421277aa821016fe63108017eb188400ef90c42037788621096fe6210849bfa908400df548420377e842101bee4210801dea108406fb50842005fcc221002fd6110849be2888400bf98042005fac0210937c501080b7fb2e6401bf9973211dfacb99016fc65cc80b7fb266406bf99332005fac999016fc64cc847bfa966400df5
  | 7 => 0x5809d05e94a092d25cdc8c20001280c1902c00151c9b02d4830fd804074c7bcb381691c45c0ab4c71530acc0007554f80009657000000000000016183600008948500fcaa478d3fc0c918d654d3906164899c560a45138000f0c6b91042844c527c64cd7d330ab0708f547354b8f2c00172c0015c978c01000000029c1f53251e4b98614a497089a9300a1963061c668d800f80000b9084000d149cc0015cd0d40003b87f4e5425d3d00f40000008640001cd0f552c7788184cc0001fd255524914bb4000b4050c000d180000006556b03a400145800062950c0e8c891a8cb03540000002a4504700179425284f7d41c00000000000165959d178f783980000000016c945c1f08c400047c000b305fc00154c40888080862c66488c0005a02f80008a039cc60f5c18458c4741d80001d000129c3185291fc1440002e00011a41052c071413c0000000000000005b8000d4800000000098400171c0001500003507e4c693a8fc4490c30ad15b179d2b1130ecc8355203d0ebc005694000000a50cf40005f165d5946d4bac23d4e9415578af86c089d67c5f48590f94a81dd550f49584ed15a4ced0d07eccc49187e86fc86d2a45492bc02d118a784440d157d3a119475d0116882210a139d614bf4a4c21d1acb7048d6f80000a80504200c2280b0040242580d00a0200280000c1180300b0040080301801403c0600901207c000130301740084d000014028020000500501b00001c008080140040100000e0000300200c014040000000081402600801c00002000010100010180140100000000000000002030048000060200001603e02000823002008018030e600c1302a00c000000000080080080300603c0400001401c04011010010068010000000080001e0100000e00a04c0300200c0280680c010098100000200000001100000000805006004078160080200000700c0680003d00c00000004000000060010380400000c0001640380000402c05032060050238010020e40080d0020100000600c02c108010300001780500a0085401300c020020070000c80181202200001002006038018000a2014000090020140000208803c1a00801e0080000005800801001014000010000000700200000e000048180080040000000002c1f00f00c05c020010000000100000e030018020100000001402a0441a02e00001019802050038000030000340380f0000400300000a0044b001000060028060000042081c0380000480500603c098090000040000003a0200000202a008100010180000900101001c0701000205c0080a008020020010060080082100600400002000000000020020ac0480d004000000020220c80083a00202c088060000a4098010300180103500c01404807002000000020040080400306400c0600400403c0180000c000048
  | 8 => 0xc1720000020000b7400125074850886046567806c0015dc0011640001acfe12f00005152d4bf08990f0f588acb2c660fa48e4e157b47c068c3bc1b0cf93594917482891601b4dd97b92f564cfec2800004980011000007c56ec3dc3d4ec48114710e5098000b1514054c5543a88e9588000000de40000000ec0014680006356242980000ace60000000e08558d583713890c887927940c290000d240014612080002113c45f8000000c4884922400000047961011c1645cd53c594f517596200016e921804400051d5106a0bb800014146400122d514000bcc0002a00013f51291d01a8ef45654f0061260a64f213e15ad3a4bc0000000214dcc0014c0c4c34d38d0e8988000000724e3172807857c0005ac00006532c0000000014d4000000ed80000000000006854c484c000d64e6c0000007f977459c000001744828001108a592486f8d09304a6846c0c4df50ccd4cc0c79c9d5760c146dc8155e06b42580003d8edd7912f85a92453f8090424000ee94880012c544c001078750e74e2443cb5137c0357a54181556b566163c5c4b4d3741e503c174c0515d780e910ec9bc6cc0dc7a518919c0cca8c1bc0007d44587913e41304a16989a12ec324158c9d5088702c89383f47c81286589ac32c3203312e8fe9598000648630138954b886bd4e067128ca1058933cd0d73cb49014ac11c0080eec8751ecd708453d80d8e695f4ca8000a98000a7d2988bd354fd46c9450000230805290000f315d0c6c71cbdc824000340e38758000ac52140013b8000000efcc840000005245b03e01a4cfc18041d73495cfbcb04968ac84c8f81714698cdd4fc67c2ec9f8000ec0f8d6f12acc388d93f13ac17c000000ea4c54b20f9d528000541064000bd88c95f862526416d381798f654d117052cd2cd308b0674db89243749f12040000012b8a341a0e84fb116c2f10485003f00006811246111b4ee4e988d40245dc45c9c4f0446902499410d5600003f800177d02000000131438cdbc0003091493bc000000e8d1b8dd550000099800031104053c115185448644381328bc50e1094014000000e28c94be8e7d240001044000000a080580016d4b60000d9cd88ccd7693100016d80000011bc0011e869cb29638b5cfd0000000934000e1c2dd2d0030ba8084a1d0dd76466c18c44107406800c90907d4f42f447000000015d2103e4000cf000005428c000d846888a8ab8db0f4c14c0004287a90a500d361088dc40bd4b57a88b56ccd8d24d0aca90c511200010302380009e43b00007612343b40005740000007d0000b44d500012a8770000000570ed42504a4000598a20c588681343343a04b0b34a316080895680012752ccc445449fc4fce7098150566c390df92307989712008556a01112b460476c9e94ec00108c55c070530745369675008e88384e9d
  | 9 => 0x14992707852210d84d114c4ec930aa162c364001640d04b68c80e111b0c347dd059400f3c000a25384f40050960000094d74900c9012175c2c15ec0008b94e4000d98b0c58130d174ddd5b46acb017544201e0001404000000e2cec80000007a10a8ef09f4260f25444000480ead6845a4e64f0037cad943029490cd00048ea86d89c8b58d3c35c0017715b86901085842242d094d3649794403590704f036c000000e3c728000ae40017400015c149512d0351d86516a46a9168a390c533947cf1d06c37905cdeca84a6087c8dce788a54bd5713448ec30518062073cf28bb0f714744b5724cc0cb4ba0270eb5664840a544602fd268c24e0040d49c56c450c11738694ce020c348d113180d4008c64b195d45d86c41184e93788f44e15383004c142174cbe4ba48f11dd5e8b650c05b4d1c400bd4fe55f0d5ccb920c77513cc084306eceb09057ac4dd5344d4248f60d28494d4012c148ae0cd56348382641246d1080b855643393716b842c24cb94e05294ff00010380b0ff47ac4152dca6c9c0678b901b9548720000001258a8109caa80015404ad48000000119956c0000013cc0015e4e180003c8a413486e8a2d79493cb7c198cc8950000de13352280a891049cb9cf108d00b5154ce4484ae94114295c540881c1c880d6f4404e4147831cffc1f84f8bfc5e16e063cc007056fc5694dc98ce582b15755d88909d8f18e0cafc5391144a800070cd453202d9544dd1691158c79650730fb91343c164464097d10cf092d865cad459000104cb6cb1ceb8df02a860c5781d4074608b08600f688c158c0005bcdfce4d308cd0b78f38a5cef971032961c418fcc000b545e4d354b0f856dc0013e872c2b404cc747e0a010690907b4c3c91ca71005434000098d6033d110e80000a940000000015a8000da80000000009580013c14d93ed4ac0012e4fdc001340000af4f3400000001d1cc0c0000c2805cbc8c2cb8c0180000014c800134c2c42b84557b0000b3c0000006b000000155400000007cc8ca741600009dc5d01881c00000000289ec001054974000001000000fa800135c5d47194397507102e960c5191a00000010b40008840016703fcf6d3b4b24368228000000000e94f956c0c987803c568c7cd390aac0003cd05030c000f9808c7640002cc000000f1548cadd71800000123800155800000143c5ec83d55d5fd3947d84e4170fac0e0a880000002ac2e47b0f9117cff8cac618244ca542c000278fc94cc3ec0017788204d86e02190bc52000079400094800043400101c0002342bc85ca1536c0000000e4204cd8fc01ecdb576c4880a403c3e90196bd23c0017046e47f0000d90f44100d54c41680f755bc240f88e491f169c411150bed3d4d6ce215908e0bf88fd6aca0c788cbc000fb4000e351c81901e9484000001144c1c001788d
  | 10 => 0x12c93dd2e09b8768af1518000be0000de80000f14a44496a8000201288038394ee0000e5c0016c4000510da422c3891d40011f877d7a019c2686385503acdac7b800000009c8f800027c0000002746f0c5cfa0e440009a4000bbc4b8944da0bd07384389e121c6f425400088800111d398a3c26ca9d6289b560535146ce516013b01c4344d20195784d944bc44d0296d0800740a28d6894096c20882d2fd73126d668ce89207fcaec4f48ccca0d7931d2a0ea00005c80a03150b15a0b113c86a4c7d0b8928b814551e11f50fca04000abd70c5351916e499
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf5218910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc63189100066e75189100066d75189100066c51189100066c50189100047e76549100047c76549100063f64549100063c64549100065f63549100065c63549100066f62549100066c625491001c7e76945100063f64945100063c64945100065f63945100065c63945100066f62945100066c6294510004de768c5100065f658c5100ce5c658c5100069f648c5100069c648c510006cf628c510006cc628c510004de760c5100065f650c5100c65c650c5100069f640c5100069c640c510006cf620c510006cc620c5100247e76941100063f64941100063c64941100065f63941100065c63941100066f62941100066c6294110004be76901100063f659011008e3c65901100069f63901100069c6390110006af6290110006ac6290110004be76101100063f65101100863c65101100069f63101100069c6310110006af6210110006ac6210110006b864c4110006e862c4110006d46384110006e462841100047d72d94100247e71d94100067671d941001c7e70d94100067a70d941002cde73d9010004dd73d90100047f755901000c7c7559010034be74d8c10004bd74d8c100047f7558c1000c7c7558c1000c7c75d881000c7e75988100047d75988100047f755881000c7c7558810004bf7458810034bc7458810004df735881002cdc735881000c7e75188100047d7518810034be7418810004bd741881002cde7318810004dd73188100047e76548100047c76548100066e62548100066d62548100057471548100057870548100057a70944100065f658c4100ce5c658c41018dd6718c4100065f650c4100c65c650c41000756510c41017f54510c410004f5760c410006d6760c410006d5760c41000757650c41017f54650c41017f57520c41000755520c410007d2700c410007d1700c410186d6600c41017f54500c410005d673c8410004f5760841000c7e76940100147c7694010005767194010007543194010007d031d00100063f659001008e3c6590010007943190010175ba70900100063f65100100863c65100100079431100100073a5010010167385010010004f97610010007d03110010006ba7610010006b976100100073b65100101673865100101673b5210010007395210010007b27110010007b1711001016eba61100100073a5110010167385110010007b331100100079a3110010007983110010007b03110010007903110010007b32110010007b02110010005ba74c8010007d031c8010004f97608010007d03108010007e02108010007b040c401002cf97684010007d03184010004f77644010005d47344010005e47244010007725044010004fb7644010005b87444010005e87244010007725144010
  | 1 => 0x31016f3a651031000739651031016f3b52103100073952103100073a511031016f3851103100079a3110310007983110310005ba74c831000c7f76596100047f725961000c7e75d92100047d75d921002cde73d9210004dd73d9210004ee72d9210004ed72d921000c7e75d8e100047d75d8e10004dd7698e100065e6598e100065d6598e100065f5298e100065c5198e100065c5098e10004bf7458e10034bc7458e1002cdf7658e100065e6558e100065d6558e100069f7458e100069c7458e100065f5258e10006d77158e100065c5158e100065c5058e1000c7e75d8a100047d75d8a10034be74d8a10004bd74d8a1002cde73d8a10004dd73d8a1000c7e7598a100047d7598a10034be7498a10004bd7498a1000c7e7558a1000c7e7518a100047d7518a1002cde7318a10004dd7318a100047f7654a100047d7654a100065e6354a100065d6354a10005747154a1003c7d76946100065e63946100065d63946100ce5e658c6100065d658c6100c65e650c6100065d650c61000756510c61018754510c610006d5630c610005d5760c610006d5760c61018756650c61000755650c61018757520c61000755520c61018754500c610005d673c861000c7d76942100065e63942100065d639421000576719421000754319421008e3e65902100063d65902100069e63902100069d63902100079431902100863e65102100063d65102100069e63102100069d631021000794311021000c7e76d95100047d72d951000c7e71d951000c7c71d951000c7e70d951000c7c70d9510034be76d91100063f65d91100063c65d91100063f52d91100063c51d91100063c50d91100047f755911000c7c7559110004df735911002cdc7359110004ef7259110004ec7259110004fb7059110004be76191100063f65191100063c65191100063f52191100063c511911008cbe7019110034bc70191100063c501911002cde76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100065f52d8d100065c51d8d100065c50d8d100047f7558d1000c7c7558d10004bf7458d10034bc7458d10004ef7258d10004ec7258d10004f77158d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d100065f5218d100ccde7118d1002cdc7118d100065c5118d100065c5018d1000c7c75d89100066f52d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066f75d89100066c75d89100066c51d89100066c50d891000c7e75989100047d7598910034be7498910004bd749891002cde7398910004dd7398910004ee72989100047f755891000c7c7558910004bf7458910034bc7458910004df735891002cdc7358910004f77158910004fb705891000c7e75189100047d75189100066
  | 2 => 0x6d7610c520006d4610c5200547e76941200063f64941200063c64941200065f63941200065c6394120006776194120006746194120004be76901200063f659012008e3c65901200069f63901200069c6390120006b76190120006b46190120004be76101200063f65101200863c65101200069f63101200069c6310120006b76110120006b46110120006f061c8120006cc6388120006e4618812000c7f765942000c7f725942000c7d72594200047c71594200447c705942000c7e75d90200047d75d902002cde73d9020004dd73d902000c7e75d8c200047d75d8c20004dd7698c200065e6598c200065d6598c200065f5298c20004de7198c200065c5198c200065c5098c20004bf7458c20034bc7458c2002cdf7658c200065e6558c200065d6558c200069f7458c200069c7458c20006cc7258c200065f5258c20004dc7158c200065c5158c200065c5058c200547f76548200065e63548200065d6354820006cd63cc820004ed760c82000c7c75984200047f755842000c7c7558420004bf7458420034bc7458420004df735842002cdc73584200047f76944200047d76944200065e63944200065d6394420004df768c420004dd768c4200ce5e658c4200065d658c42002cdf760c420004dd760c4200c65e650c4200065d650c42004c7f769402000c7d76940200065e63940200065d63940200056d729402008e3e65900200063d65900200069e63900200069d63900200863e65100200063d65100200069e63100200069d6310020197385010020004ef7648020005cc7348020005e47148020007aa4048020004fb7648020005f0714802000c7f76597100047f725971000c7e75d93100047d75d9310004bd76993100063e65993100063d65993100063f52993100063c51993100063c5099310004df735931002cdc7359310034bf76593100063e65593100063d65593100069f73593100069c73593100063f52593100063c5159310006bb70593100063c505931000c7e75d8f100047d75d8f10034be74d8f10004bd74d8f10004ee72d8f10004ed72d8f1000c7e75d8b100047d75d8b10034be74d8b10004bd74d8b1002cde73d8b10004dd73d8b1000c7e7598b100047d7598b1002cde7398b10004dd7398b1000c7e7558b1000c7e7518b100047d7518b10034be7418b10004bd7418b100047f7654b100047d7654b100063e6454b100063d6454b10005787054b1000c7d76947100063e64947100063d64947100057a70947100ce5e658c7100065d658c7100069e648c7100069d648c7100c65e650c7100065d650c7100069e640c7100069d640c71003c7d76943100063e64943100063d649431008e3e65903100063d65903100863e65103100063d65103100073a501031016f385010310006b96410310005b97610310006b9761
  | 3 => 0xd74d8f20004f671d8f20004f571d8f200447f7654b200063e6454b200063d6454b2000c7c75987200047f755872000c7c7558720004df735872002cdc73587200047f76947200047d76947200063e64947200063d64947200ce5e658c7200065d658c7200069e648c7200069d648c7200c65e650c7200065d650c7200069e640c7200069d640c720006d6610c720006d5610c72005c7d76943200063e64943200063d649432008e3e65903200063d65903200863e65103200063d651032019f3850103200066d72d96200047e71d96200067a70d962002cde73d9220004dd73d92200047f755922000c7c7559220034be74d8e20004bd74d8e200047f7558e2000c7c7558e20005787054a2000c7e75986200047d7598620034be7498620004bd74986200047f755862000c7c7558620004df735862002cdc73586200047e76946200065f658c6200ce5c658c6200065f650c6200c65c650c62000c7e76942200056d72942200063f659022008e3c65902200063f65102200863c651022000c7e76d952005c7d72d95200047e71d9520034be76d91200063f65d91200063c65d91200063f52d91200063c51d91200063c50d91200047f755912000c7c7559120004df735912002cdc7359120004f77159120004f47159120004be76191200063f65191200063c65191200063f52191200063c51191200063c501912002cde76d8d200065f65d8d200065c65d8d200069f64d8d200069c64d8d200065f52d8d20004de71d8d200065c51d8d200065c50d8d200047f7558d2000c7c7558d20004bf7458d20034bc7458d20004ef7258d20004f77158d20004f47158d20004de7618d200065f6518d200065c6518d200069f6418d200069c6418d200065f5218d20004de7118d200065c5118d200065c5018d2000c7c76549200063f64549200063c64549200065f63549200065c635492000578705492000c7e75d85200047d75d852002cde73d8520004dd73d85200067451d85200067765d85200067465d8520006b764d8520006b464d8520006d763d8520006d463d85200067675d85200067575d8520006d673d8520006d573d85200067752d85200067552d85200067450d852000c7c7518520006745118520006776518520006746518520006b76418520006b46418520006d76318520006d46318520006777518520006747518520006d77318520006d473185200067752185200067552185200067450185200047e76945200047c76945200063f64945200063c64945200065f63945200065c6394520006776194520006746194520004de768c520004dc768c5200065f658c5200ce5c658c5200069f648c5200069c648c520006d7618c520006d4618c520004de760c52002cdc760c5200065f650c5200c65c650c5200069f640c5200069c640c520
  | 4 => 0x91300063c51d91300063c50d91300047f755913000c7c7559130004ef7259130004ec7259130004f77159130004f47159130004be76191300063f65191300063c65191300063f52191300063c51191300063c5019130004de76d0d300055d7510d300069f6410d3000c7c75d89300066f52d89300066f65d89300066c65d8930006af64d8930006ac64d89300066f75d89300066c75d89300066c51d89300066c50d893000c7e75189300047d75189300066f52189300066f65189300066c6518930006af6418930006ac64189300066e75189300066d7518930006ce5318930006cd5318930006cf4318930006cc43189300066c51189300066c50189300047e76549300047c76549300063f64549300063c64549300066f62549300066c6254930004de76cc930006cc62cc9300059c744c930006cc624c93000c7e75d85300047d75d85300067451d85300067765d85300067465d8530006b764d8530006b464d8530006e762d8530006e462d85300067675d85300067575d85300067752d85300067552d85300067450d853000c7c7518530006745118530006776518530006746518530006b76418530006b46418530006e76218530006e46218530006777518530006747518530006d77318530006d65318530006d55318530006d74318530006d44318530006775218530006755218530006d73218530006d532185300067450185300047e76945300047c76945300063f64945300063c64945300066f62945300066c62945300067761945300067461945300065f658c5300ce5c658c5300059e748c5300069f648c5300069c648c530006cf628c530006cc628c530006d4618c5300065f650c5300c65c650c5300069f640c5300069c640c530006cf620c530006cc620c530006d7610c53007c7e76941300063f64941300063c64941300066f62941300066c6294130006776194130006746194130004be76901300063f659013008e3c6590130006af6290130006ac6290130006b76190130006b46190130004be76101300063f65101300863c6510130006af6210130006ac6210130006b76110130006b461101301a7385010130006cc628c130006d4618c13000c7e75988300047d7598830004bf7458830034bc7458830005787054830004dd768c830034be7498430004bd749843002ed431984300047f755843000c7c7558430004df764c030005cc724c030005d4714c03000c7f76597200047c715972000c7e75d93200047d75d9320004bd76993200063e65993200063d65993200063f52993200063c51993200063c5099320004df735932002cdc7359320034bf76593200063e65593200063d65593200069f73593200069c73593200063f52593200063c51593200063c505932000c7e75d8f200047d75d8f20034be74d8f20004b
  | 5 => 0xc7c7558440004df735844002cdc7358440004ef7258440004ec72584400053f75504400853c75504400059f73504400059c7350440005af7250440005ac7250440005bb7050440004bf76500400053f75500400853c75500400853e75988400053d75988400059f73588400059c73588400853f72548400872f72548400053c71548400073b70548400053c705484000738705484000538705484008e3e60548400853e758c8400053d758c840004bf764c840034bc764c8400853e750c8400053d750c840005ba700c840005b9700c8400053f75584400853c75584400059f73584400059c7358440005af7258440005ac72584400053d72944400853e71944400873671944400053e709444008e3e60944400853e75cc4400053d75cc440005ba70cc440005b970cc440034be768c440004bd768c4400069e768c4400069d768c4401d71f528c4400071d528c4401e59e718c4400071e518c4401d71c518c4401de9e608c4401d71c508c4400053f754c4400853c754c440005bb704c440005b8704c4401bf1f520c4400071d520c4401cd9e710c44000796710c4400071e510c4401bf1c510c4401c69e600c4401bf1c500c4400853e75c84400053d75c84400059e73c84400059d73c8440005ba70c8440005b970c84400053f75884400853c7588440004bf7648440034bc76484400053f75484400853c75484400059f73484400059c7348440005bb7048440005b87048440034be7608440004bd76084400853e75084400053d75084400059e73980400059d73980401b73850980400079a73980400079973980401b73b5298040007395298040005ba71980400073a51980401b73851980400079a31980400079831980400053d72940400053e71940400071e31940400071c31940400853e70940400873a709404008e3e60940400073a60940400047f72597300047c715973002e5c31597300063f52993300063c519933002e9c31993300063c509933002cdc735933002e9c73593300063f52593300063c515933002e9c31593300063c50593300069d64d0f3000c7e7598b300047d7598b3000c7e7558b300047f7654b300047d7654b300063e6454b300063d6454b30005787054b300059c744cb3000c7c759873002ed431987300047f755873000c7c755873002ed431587300047f76947300047d76947300063e64947300063d64947300ce5e658c7300065d658c7300059e748c7300069e648c7300069d648c7300747d76943300063e64943300063d649433008e3e65903300063d65903300863e65103300063d651033000c7e7598a300047d7598a300047f755863000c7c7558630006d6618c6301af38501023000c7e76d95300047d72d95300047e71d9530034be76d91300063f65d91300063c65d91300069d73d91300063f52d
  | 6 => 0xe73d06400059d73d06400069e63d06400053f755064008d3c75506400059f73506400059c73506400069e6350640005af7250640005ac7250640004df768c640004dd768c64002cdf760c640004dd760c6400065e63942400065d639424008d3e75d02400053d75d02400073a50d0240005ba70d8e4008d3e7598e400053d7598e400059d7698e400071e7598e400071d7598e400071f5298e400059e7198e400071c5198e400071c5098e400069f7658e400071f5258e400059c7158e400071c5158e400071c5058e400059e7318e40005ba7018e400059e73d8a400059d73d8a40005ba70d8a4008d3e7598a400053d7598a400069e6398a4008d3e7518a400053d7518a400059e7318a400059d7318a400069e6318a40005ba7018a400071e6354a400071d6354a4008d3f7254a4008f2f7254a400072e6254a400072d6254a400053c7154a400053c7054a400863e6054a4008d3e758ca400053d758ca40004bf764ca40004bc764ca4008d3e750ca400053d750ca4008d3e75d86400053d75d86400059e73d86400059d73d86400069e63d8640005ae72d8640005ad72d8640005ba70d86400053f755864008d3c75586400059f73586400059c73586400069e63586400059e73186400059d7318640005ba70186400071e63946400071d63946400053d729464008d3e719464008f3671946400053e70946400863e609464008d3e75cc6400053d75cc640004be768c640004bd768c6400059f768c6400069e768c6400059d768c6400069d768c6400049d768c6401df1f528c6400071d528c6400071e518c6401df1c518c6401df1c508c6400053f754c64008d3c754c6400059f760c6400059d760c6401c71f520c6400071d520c64000796710c6400071e510c6401c71c510c6401c71c500c64008d3e75c86400053d75c86400059e73c86400059d73c86400053f758864008d3c7588640004bf7648640004bc76486400053f754864008d3c75486400059f73486400059c7348640005bb7048640005b87048640004be7608640004bd760864008d3e75086400053d75086400071e63942400071d63942400053d72942400053e71942400071e31942400071c319424008d3e709424008f3a70942400863e609424000c7e76d95400047d72d95400047e71d954000c7c75d894000c7e75189400047d75189400047e76549400047c765494000c7e75d85400047d75d854002cde73d8540004dd73d854000c7c75185400047e76945400047c76945400065f658c5400ce5c658c5400065f650c5400c65c650c540006d7610c540006d4610c54009c7e76941400063f659014008e3c659014000c7e75988400047d7598840004df735884002cdc73588400057870548400853e75908400053d75908400059f73508400059c73508400047f7558440
  | 7 => 0xc4210065d650c4210069e640c4210069d640c4211ef54510c421004ef7648421005ac7448421007c63148421005e87048421004f77648421005f0704842100c7c75980210047f755802100c7c7558021004bf7458021034bc7458021004df735802102cdc73580210055e73d92500055d73d92500857a70d92500063d641925008d7a70192500657a70d8e5006d7a7018e500047e7610e500047d7610e500457a70d8a500053f7458a500053c7458a500055f7358a500055c7358a500063f7458a500063c7458a500065f7358a500065c7358a500047c7158a500055e7318a500055d7318a5004d7a7018a500047e7690a500047d7690a500055f7350a500055c7350a500047e7610a500047d7610a500047e768ca500047d768ca500053f744ca500053c744ca500047e760ca500047d760ca500055e73d86500055d73d86500157a70d86500053e74986500053d74986500063e74986500063d74986500047d72986500055f73586500055c735865001d7a70186500047e76d06500047d76d06500055e73d06500055d73d06500047f76506500047c76506500055f73506500055c73506500056f72506500056c72506500057b70506500057870506500047e76cc6500047d76cc6500053e748c6500053d748c6500071e748c6500071d748c6500065d628c6500c55e718c6500065e618c6500ce5e608c6500cf5a608c6500047f764c6500047c764c6500065d620c6500cd5e710c65000756710c6500065e610c6500c65e600c6500c75a600c6500047e76c86500047d76c86500055e73c86500055d73c86500047f76886500047f76486500047c76486500053f74486500053c74486500055f73486500055c73486500057b70486500057870486500047e76086500047d76086500053e74086500053d74086500047f72597400047c71597400363c405974000c7e7598b400047d7598b4000c7e7558b400047f7654b400047d7654b40005787054b4000c7c75987400047f755874000c7c7558740004df735874002cdc73587400047f76947400047d76947400ce5e658c7400065d658c7400c65e650c7400065d650c740006d6610c740006d5610c7400947d769434002e5e7598e4002e5d7598e400065f5298e40004de7198e400065c5198e400065c5098e400065f5258e40004dc7158e400065c5158e400065c5058e4002e9e63d0e4002cbf7650e4008d3e7510e400053d7510e400069d6310e4000c7e7598a400047d7598a400065e6354a400065d6354a400066e6254a400066d6254a4008d3e7590a400053d7590a400069e6390a400059f7350a400059c7350a4008d3e7510a400053d7510a400069e6310a400047f755864000c7c7558640004df735864002cdc73586400065e63946400065d639464008d3e75d06400053d75d06400059
  | 8 => 0x34be74d8e21004bd74d8e210047f7558e2100c7c7558e21005747154a2100c7e76946210056d72946210065f658c6210ce5c658c6210065f650c6210c65c650c62100c7e75982210047d759822102cde7398221004dd73982210047f755822100c7c7558221004bf7458221034bc745822100c7e76d95210bc7d72d95210047e70d9521034be76d91210063f65d91210063c65d91210063f52d91210063c51d9121004be70d91210063c50d91210047f755912100c7c7559121004df735912102cdc7359121004ef7259121004fb7059121004f87059121004be76191210063f65191210063c65191210063f52191210063c5119121004be70191210063c501912102cde76d8d210065f65d8d210065c65d8d210069f64d8d210069c64d8d210065f52d8d210065c51d8d210065c50d8d210047f7558d2100c7c7558d21004bf7458d21034bc7458d21004fb7058d21004f87058d21004de7618d210065f6518d210065c6518d210069f6418d210069c6418d210065f5218d210065c5118d210065c5018d2100c7c76549210063f64549210063c64549210065f63549210065c63549210057471549210b47e76945210063f64945210063c64945210065f63945210065c6394521004de768c5210065f658c5210ce5c658c5210069f648c5210069c648c521004de760c5210065f650c5210c65c650c5210069f640c5210069c640c521006ac648852100c7e75d81210047d75d8121034be74d8121004bd74d81210067850d81210067b65d81210067865d8121006bb64d8121006b864d8121006db63d8121006d863d81210067a75d81210067975d8121006ba74d8121006b974d81210067b52d81210067952d81210067a51d81210067851d8121006da31d8121006d831d812100c7c75181210067850181210067b6518121006786518121006bb6418121006b86418121006db6318121006d863181210067b7518121006787518121006bb7418121006b874181210067b52181210067952181210067a5118121006785118121006da3118121006d83118121006f32118121006ea211812100c7f76594210a47c71594210047c705942100c7e75d90210047d75d9021004bd76990210063e65990210063d65990210063f52990210063c5199021004be70990210063c5099021004df735902102cdc7359021034bf76590210063e65590210063d65590210069f73590210069c7359021006ac72590210063f52590210063c5159021004bc70590210063c505902100c7e75d8c210047d75d8c21034be74d8c21004bd74d8c210b47f76548210063e64548210063d6454821006ad64d0821004ed76108210ac7f769442100c7d76944210063e64944210063d64944210056d72944210ce5e658c4210065d658c4210069e648c4210069d648c4210c65e650
  | 9 => 0xd72946310cd5e71946310cf5671946310c65e61946310055e70946310cd5e75d06310055d75d06310055f75506310cd5c7550631005cf7250631005cc7250631005db7050631005d870506310cd5e75d82310055d75d82310059e74d82310059d74d82310069e64d8231005ce72d8231005cd72d82310055f75582310cd5c75582310059f74582310059c74582310069e64582310059e74182310059d741823100c7e76d95310047d72d95310047e70d95310047f755913100c7c7559131004df7359131004ef7259131004ec7259131004fb7059131004f8705913100c7c75d893100c7e75189310047d75189310047e76549310047c76549310dc7e76945310065f658c5310ce5c658c53100c7e75d81310047d75d8131034be74d8131004bd74d813100c7c751813102cdc735903100c7e75988310047d7598831004bf7458831034bc74588310057471548310c55e758c8310055d758c8310059f744c8310059c744c831004df764c4310055f754c4310c55c754c4310047f755803100c7c7558031004bf7458031034bc7458031004ef7258031004ec72580310c55e75988310055d75988310059f74588310059c74588310c55f72548310c74f72548310075771548310055c71548310075471548310055471548310ce5e61548310055c70548310c55e75908310055d7590831004df765083102cdc76508310c55e75108310055d7510831005d67110831005d571108310059e74984310059d749843120f54519843100796749843100795749843120f575298431007555298431005d6709843120f5450984310055d72944310c55e71944310c75671944310ce5e61944310075661944310055e7094431004dd76d04310c55e75d04310055d75d0431207545190431004df76504310055f75504310c55c7550431005cf7250431005cc72504311ff545150431005db7050431005d870504310055f75580310c55c75580310059f74580310059c7458031005cf7258031005cc725803100c7f76597210047c705972100c7e75d93210047d75d932102cde73d9321004dd73d9321004fa70d9321004f970d932100c7e75d8f210047d75d8f21004dd7698f210065e6598f210065d6598f210065f5298f210065c5198f210065c5098f21004bf7458f21034bc7458f2102cdf7658f210065e6558f210065d6558f210069f7458f210069c7458f210065f5258f210065c5158f210065c5058f210a47f7654b210065e6354b210065d6354b210bc7d76947210065e63947210065d63947210ce5e658c7210065d658c7210c65e650c7210065d650c7211f754510c72100c7c75983210047f755832100c7c7558321004bf7458321034bc74583210066d72d96210067671d96210047e70d962102cde73d9221004dd73d92210047f755922100c7c7559221
  | 10 => 0x89410066c50189410047e76549410047c76549410065f63549410065c63549410066f62549410066c6254941004be76d0941006ac62d09410059c7350941006ac62509410fc7e76945410065f63945410065c63945410066f62945410066c6294541006ac629054100c7e75d81410047d75d81410067850d81410067b65d81410067865d8141006db63d8141006d863d8141006eb62d8141006e862d81410067a75d81410067975d81410067b52d81410067952d81410067a51d81410067851d814100c7c75181410067850181410067b6518141006786518141006db6318141006d86318141006eb6218141006e862181410067b7518141006787518141006bb7418141006ba5418141006b95418141006ba4318141006b843181410067b5218141006795218141006bb4218141006b942181410067a5118141006785118141006ba411814100c7e75988410047d7598841004df735884102cdc7358841005747154841004bd7690841004bf7650441005ac7250441005b8705044102cde7398041004dd7398041036b840980410047f755804100c7c75580410047f725973102e5c31597310047c705973100c7e7598b310047d7598b3100c7e7558b310047f7654b310047d7654b31005747154b310d47d769473100c7c75983310047f755833100c7c7558331004bf7458331034bc7458331004bd76992310363e75992310363d75992310369d73992310063f52992310063c5199231004be70992310063c5099231034bf76592310069f73592310063f52592310063c5159231004bc70592310063c50592310369e6490e31034df7650e310cd5e7510e310055d7510e310069d6410e3100c7e7598a310047d7598a310063e6454a310063d6454a310066e6254a310066d6254a310cd5e758ca310055d758ca310069e648ca310059f744ca310059c744ca310cd5e750ca310055d750ca310069e640ca310063e64946310063d64946310cd5e75cc6310055d75cc6310047f755823100c7c7558231004bf7458231034bc7458231005d671d92310cd5e75992310055d75992310059d76992310071e75992310071d75992310071f52992310071c51992310059e70992310071c50992310069f76592310071f52592310071c51592310059c70592310071c50592310059e7419231005d671192310059e74d8a310059d74d8a31005d671d8a310cd5e7598a310055d7598a310069e6498a310cd5e7518a310055d7518a310059e7418a310059d7418a310069e6418a31005d67118a310071e6454a310071d6454a310cd5f7254a310cf4f7254a310074e6254a310074d6254a310055c7154a310c65e6154a310055c7054a310cd5e7590a310055d7590a31004df7650a31004dc7650a310cd5e7510a310055d7510a310071e64946310071d64946310055
  | 11 => 0xc7c75986320047f755863200c7c755863200c7c75982320047f755823200c7c7558232004bf7458232034bc7458232034be76d91320063f52d91320063c51d9132004be70d91320063c50d9132004df7359132004be76191320363e75191320363d75191320063f52191320063c5119132004be70191320063c50191320063f64549320063c64549320069c648c93200c7e75d85320047d75d85320067451d853200674511853200c7e75d81320047d75d8132034be74d8132004bd74d81320067850d81320067850181320047c715943202e5c31594320047c705943202cdc735903210c7f7654832004df764c8320059c744c8320074d524c83200c7c759843202ed431984320047f755843200c7c755843200c7c75980320047f755803200c7c7558032004bf7458032034bc7458032004f77158032004f471580320e57671d92510063d64192510ed7671192510053e74d8e510053d74d8e510c57671d8e510cd767118e510047e7610e510047d7610e510a57671d8a510053f7458a510053c7458a510055f7358a510055c7358a510063f7458a510063c7458a510065f7358a510065c7358a510047c7058a510053e7418a510053d7418a510ad767118a510047e7690a510047d7690a510055f7350a510055c7350a510047e7610a510047d7610a510047e768ca510047d768ca510053f744ca510053c744ca510047e760ca510047d760ca510053e74d82510053d74d82510157671d82510055e73982510055d73982510065e73982510065d73982510047d72982510053f74582510053c74582510257671182510047f72597410047c70597410363c40597410065f5298f410065c5198f410065c5098f410369c4098f410065f5258f410065c5158f410065c5058f410369c4058f410069d6390f4100c7e7598b410047d7598b4100c7e7558b410047f7654b410047d7654b410065e6354b410065d6354b41005747154b410059c7350b410f47d76947410065e63947410065d639474100c7c7598341036b840983410047f755834100c7c7558341036b8405834100c7e7598a410047d7598a410073651d06410047f755824100c7c755824100c7e76d95410047d72d95410047e70d95410065f65d8d410065c65d8d410065f52d8d410065c51d8d410065c50d8d410065f6518d410065c6518d410065f5218d410065c5118d410065c5018d410053d7510d410069f6310d4100c7c75d89410066f52d89410066f65d89410066c65d8941006cf63d8941006cc63d89410066f75d89410066c75d89410066c51d89410066c50d894100c7e75189410047d75189410066f52189410066f65189410066c6518941006cf6318941006cc63189410066e75189410066d7518941006ae5418941006ad5418941006ae4318941006ac43189410066c511
  | 12 => 0xc745834300c7e7598a430047d7598a4302ed431986430047f755864300c7c755864302cdc73586430067850982430047f755824300c7c755824300678505824300c7e75189430047d751894300c7e75d85430047d75d854300c7e75d81430047d75d81430047f72594430363c425944302e5c32594430047c71594430363f415944302e5c31594430047c70594430363c405944302e5f305944300c7e75988430047d759884300c7e755884300c7c759844302ed431984430047f755844300c7c755844302ed4315844300c7c7598043036b840980430047f755804300c7c7558043036b840580430063f64991521356d72991520055f73591520055c735915213d6f72591520057771591520057471591520057b70591520057870591521156d7298d520053f7458d520053c7458d5211d6f7258d52005777158d52005747158d520057b7058d52005787058d520056f7250d520056c7250d520047e7610d520047d7610d520055e73d85520055d73d85520bd6d72985520053f74585520053c74585520055f73585520055c73585520ad6f72585520057b70585520057870585520053e74185520053d74185520063e74185520063d74185520047e70185520053e74d81520053d74d815205d6d72981520053f74581520053c74581520055f73581520055c735815204d6f72581520057771581520057471581520055e73181520055d73181520065e73181520065d73181520047e71181520047f755874200c7c7558742004df735874202cdc735874202cde7398342004dd7398342036b840983420047f755834200c7c755834200c7f76596420047c71596420047c70596420053d7510e421247f7654a420072d52d0a4200c7c75986420047f755864200c7c7558642004df735864202cdc735864200c7c75982420047f755824200c7c75582420065f52d8d42004de71d8d420065c51d8d420065c50d8d4202e5e7518d4202e5d7518d420065f5218d42004de7118d420065c5118d420065c5018d420065f63549420065c63549420069c639094200c7e75d85420047d75d854202cde73d8542004dd73d85420067451d854200674511854200c7e75d81420047d75d81420067850d81420067850181420047c71594420047c70594420363c405944212c7f7654842004bf76508420059c73508420072d525084200c7c75984420047f755844200c7c7558442004df735844202cdc7358442004fb7058442004f8705844200c7c7598042036b840980420047f755804200c7c7558042034be7498732004bd749873202ed431987320047f755873200c7c75587320047f755833200c7c7558332004bf7458332034bc745833200c7f76596320047c71596320047c705963200c7e75d92320047d75d92320055d7510e321047f7654a320074d52cca32
  | 13 => 0x700100100100000e01400300000800500200100400700100000001500100b00002800000100200000002400c00300501200003500000800801e00300400701400200001900900100800000f00200e00000800100100500100002002100300000600000500400100000000700a00902800600000500800d00200000100301200f00400100100000700000000001300400300800600000c00101a00800700d00900200901200000200500100000200a00000401100001400500000500700200600e00b00500500300000000000600400800000900000000400500301300200000300000c00000001100700000100000300f00501300002000000b02200500100000300200700100000d00600500000000b00000f00200202f00000200000301801601800000a00100004300000000202e00400100500100400000300f00401000c00600e00b00200201300000000b00000800300000000300301900000101600501200000000000001f00100000000400000000000400300801a01200301800c00200600800300400200b00000300301100100400100300200200200200800200e00300000d00001800c00900600a00000000200200a00700200000400502100001500300200000800401600c00700000400200102b00900200000300100b00400800a00800200000000200000100100000100300001101300100601600100000200300100300000001500c00100600000100000400d00b00d00000000000d00000000000000100a00400c00100100100600300401500000300201801100200002400c00200500b00800200100b00100200001000000201201c00000600d00000102000200100100200000100600400000100b00300300700501900000500200000f01900401c00500900000b00200700c00000000500000500800100700000000500500d00700c00000000200000100500000100000100600800c00a01100900000300700000200400000b00301600000400000100400000600200000a00000b00200000900800900000000000200200600a00000200200500400000900000100100100b00200500000001a00500300b00100200600200000000100000e00200e00000200000c01400a00300900100200700200e00000000100000100002a01200200001a00600000000b00900200300700000c00000200100100100000200102300100100100000300000500000000200200100101900300100000102100602600800000300100400700500000801900100300000401600400e00000300100000000301500400800100000100000800201f00000500300001e00600100000100000100a00900700800c7e7598b430047d7598b430067451987430047f755874300c7c7558743006745158743036b840983430047f755834300c7c755834302cb
  | 14 => 0xd7815f2d001c400000000014607ba00022c88c904879f00001248a200027a124400081a00000010267a30989d04d625fe26b1a18e5837d00a8dccaca642073979c4ec2880eb0938cf44d543a0a74806578330125c2923071b89390d7c7ae38f0448c7e6e1163800060008e2d78000e1800013a167ce4820b0f703d474209e3150d784d855b000000000000000001e057201003909e800021422600003ba5413981fb00005c22f306040000003578000934628065848ce1056a1e502ecec000004603885a800030e00000004af28e800056423d3050a8cb0c4653b292e400000024a2214a7800024c80002967691b50ea81586f924f9750e5083036f800113000044a8000522064000127800026e1b687d400007d0000dc8f1656938d81e4d161fe36e9f3c0000004469b6cb9036310017a09164dd41105e813e3d00aa038cbf47bb40b20c80000000000b000006f616d800077e6bd08a800056200010109206327c01df000014673b0ca9b0c68820910f90c800067d43d0000d066d82ec8a949267d617f818827283d000000085483b3a5a09c00069800005acea46152be030803a8a10bb00002284683b69bd46ca7c812c82fc71261132d1de88245ec110a1748a66a61f90284f065cc441051c68e03835800008843290ff974840808a26485a4bb004706e0db0ec600003716e51123a0009962000002f000042c32684129d8bcd02e0000c383c80001dc30c1ea49e036929b8c551003d343709cce3427928680004d62f60381b943c841a1171a303864cc16c000063000000000000001d300000000008192f905900000002e7a16400017e0000a5400070210f102c4a24b22330e141642300000000bb4000000000000001239318100ea1de33f800055200016f81080005f63001660c622c500d9e60dce456129800001e5524028f0867e00036a17ec6ea00044a00007c674342a026c7640b403b8248e4626d3af9328b660001a094110aa55903d0e58cb640c38e8e00ba63931d21b2004484314b83a40000000000000dc631200000004c8000000194025400000000000000001168f809cc000239155cd1000042885042660c9250205000084f31900003cc0250d900009de535216029c7f04463a48a0cfbe45b38f8000e946ec2dd0318c802c315100008e024a45780004887b923c9a3c0004250d2126d0740000001fac000000214093c9c44183be84e800033627d18c0fb400000000000400900000000700200100200d00f00501700000400100100900200100a00100900000300c00000801f00100100e00501a00800000000500000300200300000000c00500200100800400200200600b00100a00000e00900200000c00000701700100000300400100600200800100200200100101500600100702000500f00000200000000300200000500800
  | 15 => 0x3ae8c803041f312c0e68f7a2bb3a3224818a7e018b8d581b000042d85a8daa4e33e1a00428a00541197b8b5a68d0001cf43607e73600e5000031b0549f08ef249200000002ba28c1a40e7c186794283037c7a25ef1e71a486988b24160000f087640e58a6c3980000328e643946de31c09c0eb01fd41c944831238b26f0344c9800019c121c63a02c3f899f05001ce06e800077a43807500000002ae43e000cd48227261207856e79b4141b5c01642600000000004d7000000000062100016706727d100019a8a0472d00000002587aa3c39c009a20fc336007072a3c0303800000025000000d0c1c00000012b800000025e84600001cf1b08170fc80002de1458f220ff1470000a22454000022115269b0000440d4457f0b3163c27687f220a1b40005031fc89a45742b62879e6400000020695ec0004ab00000000005f414500000001e330197f47665001eb8e449963140fd8000d140002598904f024a810e840413856b2b8800084e00000000000900001ae8208f561f73799dcc0001532d20000b763060308000e240001bd1b382a010402d904c4860002910000d1c7a20dd04bc3a233d0608afca8e2d231e989c9b84a642e14b90240e10258004dee1ac0ce04fc0780ed20c9c7036269001e9fb4c1a3c61ac023c8724fb296000000052b0000000eac42340f80008bc00006695380000001b40000cd20413428000000000280853c0008561199ab00007c600008b0a684981e28bac72485700008ec3f063b3850e5ce9876710d1b40d3a275000000021c000000008c0008770b093800de1850000bb400000037d00005985bf0fd130066058e00011243c47d93689df88424891d695d40b0709323217c0000000000c8469a86c000002800000030082603280003100e9400000000007400ac6991940a402c6000000097800000d0000a1c3a441d2120000cdc5361c718647bc0000001ae801c7470000ce88906da353963413422b29199780005a13f501d80006b216400009ce000000000000013c28a80007b21ab3a20dfc0000000000d6c8084b10001ab80006f22d70000000000000079c41c00000021c80d035f260800000000038b2230be08212a6800042464728f8d3829077000000000000002d800000005df00000000000001448000e7e6a005892080002bd0001b980003cb09b80007ea507000154040a00017e92e8bda4bb0de80000000552e18000f400b8403888c4ae3d63551b4c00057928e1e1461061e25a80000860003d90cac37000034b191046856e337800000037042d108079e54a2278000198562094863800020f0000418ca40002428000ea286f0730704ecc3e93c687240005fc00000010c4000331862c29a6623c7a0dc00083c0e300d89ca38a3341284c9e8ad3358000c3a0fa108a0d011a000075800049600000002b4
  | 16 => 0x10663da0000568d8e000263202800027e2cb105c7d44a219f0aa81746c541f0db8b8e0002ea9ad40bc5823228000f101781c68df887a81022a93c4a647b01f0871c36636405503900005b416f000109853d22b8d48f883401f321781a07973250c4cbc40f007b8164dc02a642102740ae8182b80d80f96000191a1e000045f1f10e888b46a91eaa24c65c22829f97342b87290700e08df63030c30fb80000ce1379584ca630b1cd80000a850c000000000000018f84d50ea0000000c588e80811b31bf10525c01e90a507da89e372000080a39d0001a009b22fa2450420ff000000006f105400038180009540001a48000ce41cd05580000008ae3b58ccc00011b25f80000000000000000000000244226c0000000c51bac00089a0001160cbe78a0000128a3200031c94982fe33513105386768470001be00000000000d140003fd43d9d0000000000000000006c42b78708a3c00009e800000058114f87e514e00000013480004ea0001e986120000000434c6658929518d8f68000000000000005341580000008872af938400000014280001781742ed9b5800067605b8f6c0007ff30485bd1447dc05b05805f273c1e694a020e35335c11d81a60c01f581ecba279a36502c0a421880001bfcbd627d2f0107cc180d92ca185113a7772a21fcce4e00033b933400067300022a00008ab1d300010ce0000df1efc2426dc19621ac0000000bd91845c208422900000000000000000000229000000000088a1f78000bd487029380000000000001fe8000000000000000084503300000006c10000000ff23f70930a48e0a3f023b80085ca50e1e383ec60255a39b000000000009683cd00065c3f70aa09e438f0000a78f241730001ee80c065138b88182bc21c1828820c5211708d08d452c0002401cc40007a73ea07a42880292b21df0fa633c002184c5080000a90d88e720000001cd400059b1e495d00e62ab00000010ec0003ba00ed1161d42f48c34b9620a0d7931468c00004ca148bea5ca06a84c87701ed07a129056876a429849015e22410800005d416d0dd9b48c364c82e800000000003e48eec00e2fe28a1820e2a0092010dac8961a30691ec4c1606a35983a0000811000067509c268428035c3e04f71f402cc79858a2e3081c61e00000000008f400000008f898864e0f5202c9385be2d6153cd6c4cf000000000023c0fa0000000090407905106256300019500000000cd00008801ec000105428c0c4000207400055d3c00cbc694789399a2700004b74398000d6e000000069c0002663ea95c8a2e58b00005300002c617b94cc2d00002a01dc4cc20a010c9a448e604f0ad86fc1bc29917480000000000000644dda52417d96f40001f10228d3c4b63b037798090d21980bc863462227c3a716481dc0280aca1846485f83780860aac7fe
  | 17 => 0xc0001d6400000026a000000000005e8000a168631680764d2a3271ce07a03887e53e61bd00280003c10684e9e16e00015f46a84d332c0f10bee5490000b586ee6cc0d11da08dc3af178968818e0000f00368fea47d2980d0cc3e46028d8de0b544083ad02e44e42032a19468e205453b713ac09c08702e8000000431000111051a44e08280001fc10c27f96e0436000065000000080319680000006cb2b38ba0f8a73233c11bc444000042800086e8022cc80008125b110a89684c20000a021f4f6e88e29d0eac000000356944d04c7ce00000000003830c903940007cd41015700000003a4000006438c3c601485882dd2b60b28c2e41e1338000b8800026812f8a6228f45884740007070819cb88ba6b933c9c880007fc1ba09ec37270f00000000000001150bc0c4a3ec0000000aec23f135168c0002d5000000000077521985f46f85200ab80000008043ab98b459c46937e88c49ea01140e00000005c10001fc805c1da343880496848c05f00009b400000007543de8aa38680000000000f08b24b4c80e00000000002540da00000000000a10000fd27210ab02b800060543316c80001a5208000044077f1d600000004f644411e0dd234200604a092000016e020cdd426534fa1f848a30a00f8544b3a0004418000ea613e0000b641903f42e2a0308c676107e8bb0e288b03f103bcf783c82f89d78c8662444b80008380002c29c8086a4ce3f32094a52016138866c3b605f4250bb88fc6702761f2835219915a80e82706bb0c81f40cba046207152064400015685f085c67e21a18bcfb00d639581fc0005c9018211078204d3d29998abc63541f9840c5869a31595e891c0001179e1876c7113cf1610cda16c0000d69120713435108800017000004083d644a0e019c49f888612300004ee5802281e744a45422b30294b343373498c1080200043405c4000000000000000000000000009fa29c380955433e06b08e205514c6b43339e54a1044516080009da00000014bc9b600009810f011279c00010a40005391301d400da0002f1954c00056d0001848f1c1b60201f780008ac11b9d50c1e00027f000055e5f33421ea072086005106d43e4278351a1948f600042012d85de0000000fe876a496172085c06a0670000b4cbac65611d0b3c34c25f23f9a04c44738438800000076c000211800000000000000e83d8022042407e89119500000000000138e60f707b535086100001343bd8000c0c2f212e12187f618f04b169c7ec1c500018d0a7c0002aa00005ae4431f99d3500c6260000a4c2ca12b1ee20bc0c664b1dba2805ea2da2c99f8c9e64a72cb844c6f618001980005ce64131b94b419e1aa3541cbc87673a33d80007a830c1718000000226000000025c28220b2034ffa024000103d0c824004a00000560000b3800000000011c800
  | 18 => 0x7625a81aa8018d9a75b17103503064a3424937c66825524790d87ca15823698690366d908b036c1ec5580001fd8a8c82d0938c981000a81988000c780001e1858894a3a30041dc82ee11f2db877cd3c4ee17a05d43ec64d0000d9c0000003a29a940000000001c180006c231f00006641a834e0080d9e70b27c02d40007ad00f0a1841a0000531ed800000020880000000000000a900006f100000000000001f8979513e5a53aa958111e000284800093a48d00003b000084b2ee80000006822c1a1e4fc203e0f28000958573121000088e120215a0240002ac1d38e040008351cf08d80000001fe1fa04181fc44b00dc0003ae34a11900620000000000f825772fc80000003251dd1dd89b04952c606dc09831a2ef0d64e322bc205120ca700001bb152c49200044c977032e7931ae048898619e27c80000003503b780000007d20001000f420000eb8af863805a00c01f000000002821600002d11238ee40000002a61bf885e0000000b9800000000000000002980001d88e6e4ad28296d8fe07f412b11704ba2160000a0400000021f81f80000001ff1fbc90852537415447c846200b906cbfe1d83d980007688b342404d832c2b313f92a434072a2409cf85f00002bf131c54211107c00985840003170b34e4a5d704a964014811e01091a80001ae21f00000000002daa2900007d70e420e106c5a9085161c00018c32480000008a51b780000000001c40c3870e31e32c80008ce71825c1428e8465732a88941f2000000000000061600000001e247121680006204e90000000000475000113480e7342031738ff638621d1c1054e14331d1ebc49a02a11c0e100000002d59b8905c1720000a80d7e7be00013a02940001ef9990b2a34b3ae00000000001d41f740d87903fb8de4a202cb00000004260000001e5800035744206b4c9012536300002aa08b3870000000000000043ccca2b800000000000972cf0000b2200000000000320003770000bc800033a80009785e10000000d2e00033a228c0340000348ef0d122b013180000000001810b80ad00913d20d4400084d440a0208f83e73e3800096046c0000000fb60000001b248602fc3bc00b400000014581448d66ab043188c2327ac14d00002000001ff80e4752000000024c00024
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x85d87140635080185eeca928421003431cd52508420041ec3ea4322640083d87144644c80189eeca926419003431d1524c8320060fba6e6b14a218954815ce609448b4a902b9cc1288031598c7154b4100516c28863128200c8c73189425040153507ba0c0a08028e61443181410054c41a84302820083d87d4a648c40107b0e28cc9188030e1c050592310048ec3ea5324620091d87146648c401a30e0282c918803839926254a3100647324e5b046200954815d6620c401a2d0838aa418803456107154831004ab400e2a906200954815d6420c4013a100b888418803451457498431006a2288e4a086200d50511c1410c40145b04280c8908030d19071549210062a318e2a924200a698214060484014d3043a8c0908029ca0752181210053840aa43024200c8c731c96408401870e0282c81080227e1d648c4211ed2a40aca1884200e14515903108401b8462382421080307dd37358a500849c402e930ca044a38805d261940010bb0fa94c7200021761c5098e400062a388a2b1c8000c8e631c9419000123b0fa94c7200024761c5098e400068a388a2b1c8000e0e63989529000191cc7396c3200032698e70d86400044ec3ced18c8000c1f855da31900018390abb4632000307d49768c6400060e28aed18c8000c1c505da319000183aeca946320003075da518c6400058a40aa418c800089f865cf219000143b0d18ca1200024e20175988400068d418e0a908000d19831c1521000127502382a4200024e201758c840004d840ae01908000b188054a311000162902a906220002c6201520c4400049d406eb1088000938805d42110001a30a0b9cc0200030e9907054b300044fc3ac918e6000a4d8510c624c001918e83126498002a5a1373185300052ac288630a6000a94844c8614c00191ce83146298003259d0618c53000714280c42026000e3050184404c00113f0eb24639000295a07650c62000526c10a231a4000c38641c152480018b0c6382a49000299608511852000532c10ea30a4000a7280d4861480014e100a90c290003231d07258c200062a388a2b184000a5481594310800113f0eb1c80100ca8e20165100200070c282c62004000da0719012008001874c8382a58800227e1d648c7100051dc32a42062000c56631c552840014af0ca90630800227e1d639021000c3643ac4a902000b5280d9431040014a90ca906208002d4201520c410005c8422e01882000bc0825c03104085e20a01888008003c40c650100100059940eca2002000a3886548400400166102a908008002e420d7110010005d0412e22002043b92818c44004001e24a2188800810bc4144311001000789b28622002042f10650c44004085e26a41888008003c45483110010005c941e422002000d92740c72004001ac0e52822008003581ca5144010
  | 1 => 0x430ec2400260b8440000188ea0000144d05e24228664e00114884a00018d42d16000421500000006120a449a5a00174da1832890b8691b86cd600001c428000000000001e208c80200000260006800008b002303a00200000000001c02e81238d40819469dc6023018710a0a3ca10000000000686744000e87300001120007800007d2497c404f0000000461d0000000000f40008219e11c0000000c6553d8000000000000036000bcf85000000005900000e4001c0004c7e00000543f25878d8873f99800392b0ac3e90000000052000000000001bc0029400c8006000150ec000296c4e0e0880050420023c62533d024166e0801d065800000340012858ae0c1f0000200000000c100c0c04080008000040000c000000000c0038041400041838140020000400043808080c44000828000400040000010e902bb086a90021e2017610d520049c402e830aa400a38805d061548012a902b98c0a90029520573181520042ec3ea431a8400
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x18000100a0000151090610715483100503648855da319000101e98d49768c64000544245831c15210001610965483110010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x6
  | 2 => 0x4e
  | 3 => 0x124e
  | 4 => 0x138e
  | 5 => 0x4
  | 6 => 0x5
  | 7 => 0x94e
  | 8 => 0x8e
  | 9 => 0x128e
  | 10 => 0x150e
  | 11 => 0x98e
  | 12 => 0xce
  | 13 => 0x12ce
  | 14 => 0x9ce
  | 15 => 0x168e
  | 16 => 0x10e
  | 17 => 0x130e
  | 18 => 0xa0e
  | 19 => 0x180e
  | 20 => 0x20e
  | 21 => 0x140e
  | 22 => 0x154e
  | 23 => 0xb0e
  | 24 => 0x24e
  | 25 => 0x144e
  | 26 => 0xb4e
  | 27 => 0x16ce
  | 28 => 0x28e
  | 29 => 0x148e
  | 30 => 0xb8e
  | 31 => 0x184e
  | 32 => 0x3ce
  | 33 => 0x15ce
  | 34 => 0xcce
  | 35 => 0x170e
  | 36 => 0x40e
  | 37 => 0x160e
  | 38 => 0xd0e
  | 39 => 0x188e
  | 40 => 0x58e
  | 41 => 0xe8e
  | 42 => 0x178e
  | 43 => 0x18ce
  | 44 => 0x10056
  | 45 => 0x11396
  | 46 => 0x4116
  | 47 => 0x24056
  | 48 => 0x25256
  | 49 => 0x4256
  | 50 => 0x10096
  | 51 => 0x11516
  | 52 => 0x109d6
  | 53 => 0x112d6
  | 54 => 0x130116
  | 55 => 0x24116
  | 56 => 0x25316
  | 57 => 0x11456
  | 58 => 0x144116
  | 59 => 0x145316
  | 60 => 0x10256
  | 61 => 0x24216
  | 62 => 0x25556
  | 63 => 0xb8256
  | 64 => 0x148256
  | 65 => 0x144256
  | 66 => 0x241005e
  | 67 => 0x100425e
  | 68 => 0x138116
  | 69 => 0x124256
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 70
  | 6 => 1519
  | 5 => 2228
  | 4 => 146
  | 3 => 5
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
  | 7 => packedAt gbK7 (1981+((h/23+packedAt gbK7 (1820+(h % 23)*7) 7) % 85)*8) 8
  | 6 => packedAt gbK6 (61769+((h/506+packedAt gbK6 (56203+(h % 506)*11) 11) % 1823)*12) 12
  | 5 => packedAt gbK5 (115848+((h/742+packedAt gbK5 (106944+(h % 742)*12) 12) % 2941)*13) 13
  | 4 => packedAt gbK4 (8998+((h/48+packedAt gbK4 (8614+(h % 48)*8) 8) % 233)*9) 9
  | 3 => packedAt gbK3 (354+((h/1+packedAt gbK3 (350+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffffe00ffffffffffc007fc7ffc7f8fffc7
  | 1 => 0xffffffffff007fff001fffffff8e3ffff1f8ff
  | 2 => 0x7f800ffffff807ffffffffffff3c78c7e1fff
  | 3 => 0xf80000ffffffff80001ffff803fc07f07fe0f8
  | 4 => 0xffffffffffffe0000003fff8007fff00
  | 5 => 0xffffff00000000000000000003ffffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x5a5aad2e0065a58b6ab2c0c2e434dc3586ebc3
  | 1 => 0xacad4e5acb004ad506055b4da98a29dab1785d
  | 2 => 0x730609555aa8066b4d9ad9752d3468c5a15ae
  | 3 => 0x320184e7a6f37300189e36e0637c07706fa0f0
  | 4 => 0x40608f9f8dc7c78df00070183efb8007dde00
  | 5 => 0xc7c7f001c0e06040e010380603fff7ef000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xe8a8c888e8a0c080e8a8c888e8a0c080e8a8c888e8a0c080e8a8c888e8a0c080e8a8c888e8a0c080e8a8c888e8a0c080e8a8c888e8a0c080e8a8c888e8a0c080, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15191
namespace PEqualNP.Outside.L_meta_15191
open PEqualNP.Outside.L_meta_15191.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_1_0 : Interval s1Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_1 : Interval s1Atlas 1 0 1 := bs1_1_0
theorem alls1 : ∀ k ≤ 1, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_1 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 16 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 92 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 5 := bgb_3_0
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
theorem bgb_4_128 : Interval gbAtlas 4 128 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 146 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128)))
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
theorem bgb_5_2208 : Interval gbAtlas 5 2208 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2228 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)))) (concat (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))))) (concat (concat (concat (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344))) (concat (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))))) (concat (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)) (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))))))
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
theorem bgb_6_1504 : Interval gbAtlas 6 1504 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1519 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))))) (concat (concat (concat (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928))) (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))) (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 70 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 2 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 2 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 26, 27),(inputs.getD 1 zero, 25, 27),(inputs.getD 3 zero, 19, 27),(inputs.getD 4 zero, 11, 27),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xe8a8c888e8a0c080e8a8c888e8a0c080e8a8c888e8a0c080e8a8c888e8a0c080e8a8c888e8a0c080e8a8c888e8a0c080e8a8c888e8a0c080e8a8c888e8a0c080
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 49 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 42 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3903375496 * 2 ^ 32 + 3902849152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15191.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,4]⟩,⟨.and,[1,3]⟩,⟨.or,[2,5]⟩,⟨.or,[6,7]⟩,⟨.and,[6,7]⟩,⟨.and,[2,9]⟩,⟨.and,[0,1]⟩,⟨.and,[8,12]⟩,⟨.or,[10,13]⟩,⟨.or,[11,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3903375496 * 2 ^ 32 + 3902849152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3903375496 * 2 ^ 32 + 3902849152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15191

open PEqualNP.Outside.L_meta_15191 in
theorem PEqualNP.Outside.L_meta_15191 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3903375496 * 2 ^ 32 + 3902849152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3903375496 * 2 ^ 32 + 3902849152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
