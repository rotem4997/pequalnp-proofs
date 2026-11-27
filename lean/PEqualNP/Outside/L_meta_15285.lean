import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15285.Model
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


end PEqualNP.Outside.L_meta_15285.Model

namespace PEqualNP.Outside.L_meta_15285
open PEqualNP.Outside.L_meta_15285.Model
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

def SBf (j : Nat) : Nat := [4, 4, 4, 4, 4, 4].getD j 0

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

def mirrorSteps : List Move := [swapRows 33,swapRows 67]

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

end PEqualNP.Outside.L_meta_15285

namespace PEqualNP.Outside.L_meta_15285
open PEqualNP.Outside.L_meta_15285.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | 5 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffff822596ef
  | 2 => 0xffffffffffffffffffffffffffffff844aab77
  | 3 => 0xffffffffffffffffffffffffffffff88934dbb
  | 4 => 0xffffffffffffffffffffffffffffff911c71dd
  | 5 => 0x21e07e1e
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xc000000000000000c000000000000000c000000000000000c000000000000000c000000000000000c000000000000000c000000000000000c000000000000000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15285
namespace PEqualNP.Outside.L_meta_15285
open PEqualNP.Outside.L_meta_15285.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfc0fc0fe07e07e07fe1e0f07c3c1f0f87d5293
  | 3 => 0xfff000fff8007ff81fe00ff803fe00ff86631c
  | 4 => 0xffffff80001ffff00003ffff000783e0
  | 5 => 0xffffff00000000001ffffffffc00000007fc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x4000002000000000000100840021008000425
  | 2 => 0xaaa99965354ad4ae8f168b468ad1a2d1755292
  | 3 => 0x326aaaa954d369a2b7710dd2137484e7166318
  | 4 => 0xa34d34d1a69a4d34dbbba88423b9ce422783c0
  | 5 => 0xc38e38e1c71c71c71dddcee73a21088447f800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0aaaaaaaaaaaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15285
namespace PEqualNP.Outside.L_meta_15285
open PEqualNP.Outside.L_meta_15285.Model
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
  | 1 => 0xfc0fc0fe07e07e07fe1e0f07c3c1f0f87d5293
  | 3 => 0xfff000fff8007ff81fe00ff803fe00ff86631c
  | 4 => 0xffffff80001ffff00003ffff000783e0
  | 5 => 0xffffff00000000001ffffffffc00000007fc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4000002000000000000100840021008000425
  | 1 => 0xaaa99965354ad4ae8f168b468ad1a2d1755292
  | 3 => 0x326aaaa954d369a2b7710dd2137484e7166318
  | 4 => 0xa34d34d1a69a4d34dbbba88423b9ce422783c0
  | 5 => 0xc38e38e1c71c71c71dddcee73a21088447f800
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xaaaaaaaaaaaaaa88aaaaaaaaaaaaaa88aaaaaaaaaaaaaa88aaaaaaaaaaaaaa88aaaaaaaaaaaaaa88aaaaaaaaaaaaaa88aaaaaaaaaaaaaa88aaaaaaaaaaaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15285
namespace PEqualNP.Outside.L_meta_15285
open PEqualNP.Outside.L_meta_15285.Model
def s3K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (6+((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xfc0fc0fe07e07e07fe1e0f07c3c1f0f87d5293
  | 2 => 0xfff000fff8007ff81fe00ff803fe00ff86631c
  | 4 => 0xffffff80001ffff00003ffff000783e0
  | 5 => 0xffffff00000000001ffffffffc00000007fc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4000002000000000000100840021008000425
  | 1 => 0xaaa99965354ad4ae8f168b468ad1a2d1755292
  | 2 => 0x326aaaa954d369a2b7710dd2137484e7166318
  | 4 => 0xa34d34d1a69a4d34dbbba88423b9ce422783c0
  | 5 => 0xc38e38e1c71c71c71dddcee73a21088447f800
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xaaaaaaaaaaaaa8a8aaaaaaaaaaaaa8a8aaaaaaaaaaaaa8a8aaaaaaaaaaaaa8a8aaaaaaaaaaaaa8a8aaaaaaaaaaaaa8a8aaaaaaaaaaaaa8a8aaaaaaaaaaaaa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15285
namespace PEqualNP.Outside.L_meta_15285
open PEqualNP.Outside.L_meta_15285.Model
def s4K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (6+((h/1+packedAt s4K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xfc0fc0fe07e07e07fe1e0f07c3c1f0f87d5293
  | 2 => 0xfff000fff8007ff81fe00ff803fe00ff86631c
  | 3 => 0xffffff80001ffff00003ffff000783e0
  | 5 => 0xffffff00000000001ffffffffc00000007fc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4000002000000000000100840021008000425
  | 1 => 0xaaa99965354ad4ae8f168b468ad1a2d1755292
  | 2 => 0x326aaaa954d369a2b7710dd2137484e7166318
  | 3 => 0xa34d34d1a69a4d34dbbba88423b9ce422783c0
  | 5 => 0xc38e38e1c71c71c71dddcee73a21088447f800
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xaaaaaaaaaaa8aaa8aaaaaaaaaaa8aaa8aaaaaaaaaaa8aaa8aaaaaaaaaaa8aaa8aaaaaaaaaaa8aaa8aaaaaaaaaaa8aaa8aaaaaaaaaaa8aaa8aaaaaaaaaaa8aaa8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15285
namespace PEqualNP.Outside.L_meta_15285
open PEqualNP.Outside.L_meta_15285.Model
def s5K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (6+((h/1+packedAt s5K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xfc0fc0fe07e07e07fe1e0f07c3c1f0f87d5293
  | 2 => 0xfff000fff8007ff81fe00ff803fe00ff86631c
  | 3 => 0xffffff80001ffff00003ffff000783e0
  | 4 => 0xffffff00000000001ffffffffc00000007fc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4000002000000000000100840021008000425
  | 1 => 0xaaa99965354ad4ae8f168b468ad1a2d1755292
  | 2 => 0x326aaaa954d369a2b7710dd2137484e7166318
  | 3 => 0xa34d34d1a69a4d34dbbba88423b9ce422783c0
  | 4 => 0xc38e38e1c71c71c71dddcee73a21088447f800
  | _ => 0
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xaaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15285
namespace PEqualNP.Outside.L_meta_15285
open PEqualNP.Outside.L_meta_15285.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x500225cc430050347804a1000030bdc1f00f0903765a101809c03466a4508003802400080070000280740062a0071f9000f5a807c01b4360020a33cad31a58256b2402c0004200e80000000000041020010000061c90102046010a00483007fd4c01fe53007f54c01fc53007f90c01fd43007f10c01ff51007f94401fd51007f14401ff41007f90401fd41007f10401ff31007f8c401fd31007f0c401fe21007f48401fc21007fd4001fe50007f54001fc50007fcc001fe30007f4c001fc30007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x8c6000bf98230007be6118003fb308c0017fb2a6000dfd9530004feca98002fe654c0017eb2a6000bf19530006f8ca980027c654c0017fb226000efd91300057ec898002fe644c0017eb226000bf1913000778c898002bc644c001ef29a6000f754d30007bc8698003dd434c0017fb126000fbd8930005dec498002fc624c001f63126000bb18930007be6498003dd324c0017fb0a6000fdd8530005eec298002fc614c001fa30a6000bd18530007be6298003dd314c001fd9826000f78c130005feca18002fe650c001bf32860009f99430005faca180037d650c0013eb286000bf19430005fec818002fe640c001df3206000af99030005fac818003bd640c0015eb206000bf19030005fcc618003df530c001ee2986000f7d0c30007b88618002fe620c001f73106000bb98830005fac418003ed620c00176b106000f78c830007b86418002fe610c001fb3086000bd98430005fac218003f5610c0017ab086000f78c430007b86218002fe600c001ef9806000fe8c030007ba6018003f9300c0017fb2e2000bf99710005facb88002fc65c40017fb262000bf99310005fac988002fc64c40017fb1e2000bf98f10005fac788002fc63c40017f3162000bf58b10005f8c588003f651c4001faa8e2000fd90710007ea8388003f631c4001fa98e2000fd88710007ea4388002ff65840017f32c2000bf59610005f8cb08002ff64840017f3242000bf59210005f8c908002ff63840017f31c2000bf58e10005f8c708002ff62840017f3142000bf58a10005fac308003f75184001fa28c2000fdd0610007e88308003f73184001fa18c2000fdc8610007e84308002fe6084001fb8842000fec4210005feca880037f65440013fb2a2000bf99510005faca88002fc6544001be32a20009f19510005fec888003bf64440015fb222000bf99110005fac888002fc6444001de3222000af19110005fec688003df63440016fb1a2000bf98d10005fac688002fc6344001ee31a2000b718d10005fec488003ef624400177b122000bf98910005fac488002fc6244001f63122000bb18910007eca288003f55144001fb20a2000fd50510007ec6288003f53144001fb10a2000fd48510007f62088003f610440017fb282000bf99410006fcca080027e65040017eb282000df59410004faca08002fc65040017fb202000bf990100077cc808002be64040017eb202000ef590100057ac808002fc64040017fb182000bf98c10007bcc608002de63040017eb182000f758c10005bac608002fc63040017fb102000bf98810007dcc408002ee62040017eb102000fb58810005dac408002fc62040017f3082000fdd4410007e8a208003f74104001fa2082000fdcc410007e86208003f72104001fa1082000bf98010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x3df534c401ee29a6200f7d0d31007b88698802ff624c4017e3126200f78c931007b86498803f7514c401fa28a6200fdd0531007e88298803f7314c401ef18a6200bfd8131005f8c098802ff650c4017f3286200bf59431005f8ca18802ff640c4017f3206200bf59031005f8c818802fe630c401ef2986200f754c31007bc8618803dd430c4017f3106200bf58831007be6418803dd320c4017f3086200fd94431007eaa218803f6410c401faa086200f7cc431007ec6218803dd310c401fa9886200f54c431005fcc018802fd600c4017fb2c4200bf99621006fccb108027e65884017eb2c4200df59621004facb10802fc65884017fb244200bf992210077cc910802be64884017eb244200ef592210057ac910802fc64884017fb1c4200bf98e21007bcc710802de63884017eb1c4200f758e21005bac710802fc63884017eb144200fb94a21007daa510803ee4288401f6a144200fb8ca21007da6510802fe6188401fba8c4200fd14621007ee8310803f44188401fb98c4200fd0c621007ee4310802fe60884017eb044200bfd9521005fcca90802fd65484017e32a4200bfd8d21005fcc690802fd63484017e31a4200fdd4521007e8a290803f74148401fa20a4200fdcc521007e86290803ee21484017fb024200bf18121005feca10802fe65084017eb284200bf19421005fec610802fe63084017eb184200bf18c21005fcc210803f65108401faa884200fd90421007ea8210803f63108401fa9884200fd88421007ea4210803e521084017f3004200bf58021005fcc7a8002fd63d4001bfa9ea000df54f50005fcc3a8002fd61d4001bfa8ea000df54750005facb28002fe63940017eb1ca000df94e50006f8a728002fe61940017eb0ca000df94650006f8a328002fe6094001bfa84a000fed4250005fec6a8003df63540016fb1aa000bf18d50007b8c6a8002dc6354001bfa9aa000df54d50005fec2a8003f761540017bb0aa000bf18550007e8c2a8002f46154001bfa8aa000df54550007f6a0a80037e50540017f328a000bf98c50007bcc628002de63140017eb18a000f758c50005bac6280037e5314001be298a000bf98450007ecc228002f661140017eb08a000fd58450005eac2280037e5114001be288a000bf98050006fea028003fa5014001bea80a000fe54050005fecb98002fe65cc0017eb2e6000bf19730005fcc998002fd64cc0017e3266000f794f30007baa798003de43cc001eea1e6000bf98b30005fac598003df32cc001ee9966000bf98730005fac398003df31cc001ee98e6000bfd9630005fccb18002fd658c0017e32c6000bfd9230005fcc918002fd648c0017eb1c6000f7d4e30007b8a718003df438c001ee21c6000bf98a30005fac518003de328c001ee1946000bf98630005fac318003de318c001ee1
  | 2 => 0x51006fea328803f751944017f304a200bf58251005fec8a8802fc6454401bf2a2a200df15151005fec6a8802fc6354401bf29aa200df14d51005fec4a8802fc6254401bf292a200fdd4551006fca2a8802ff60544017e302a200bf99451005fcc828802fd6414401bfaa0a200df55051005fcc628802fd6314401bfa98a200df54c51005fcc428802fd6214401bfa90a200df54851005fcc2288037f5114401fb288a200df54451007eaa2288037551144017f300a200bf58051005fecba0802fe65d0401bf32e82009f99741005facba08037d65d04013eb2e8200bf197410077ea9a0803bc54d04017f31e8200f798f41005bcc7a0802fd63d0401eeb1e8200b758f410077c87a0803bc43d04017f3168200fb98b41005dcc5a0802fd62d0401f6b168200bb58b41007eca3a0803f551d04017f3068200bf58341005fecb20802fe6590401bf32c82009f99641005facb208037d65904013eb2c8200bf19641005fac920803be5490401deaa48200bf98e41007bcc720802de63904017eb1c8200f758e41005bac720803bf4390401dea1c8200bf98a41007dcc520802ee62904017eb148200fb58a41005dac520802fe6190401fba8c8200fd146410077e8320803f741904017f3048200bf58241005fecaa0802fe65504017eb2a8200bf195410077ea8a0803bc54504017fb1a8200bf18d410077c86a0803bc43504017fb128200bf18941007eea2a0803f45150401fba0a8200ef90541005fec0a0802fc60504017fb288200bf99441005faca20802fc65104017f3208200ef950410077aa820802fe63104017eb188200efd0c410077a8620802fe62104017eb108200bf98441007eca220803f55110401dfa088200fd904410077a8220803f54110401daa088200bf98041005fac020802ff65cc4017f32e6200df99731004fccb98802fd65cc401beb2e62009f59731005f8cb98802ff64cc4017f3266200ef993310057cc998802fd64cc401deb266200af59331005f8c998803df53cc401ee29e6200f7d0f31007b88798802fe62cc401f73166200bb98b31005fac598803ed62cc40176b166200f78cb31007b86598803f651cc401faa8e6200fd90731007ea8398802fe60cc4017eb066200bfd9631005fccb188037e658c4013f32c6200bf59631006facb188027d658c4017e32c6200bfd9231005fcc918803be648c4015f3246200bf592310077ac918802bd648c4017e3246200bf58e31007bca718803dd538c401ef21c6200f750e31005fcc518803ee628c401773146200bf58a31007dac518802ed628c401ef9946200f74ca31005fcc318803f7518c401fa28c6200fdd0631007e88318803df318c401fb98c6200bf98231005fac118802ff654c4017f32a6200bf59531005f8ca98802ff644c4017f3226200bf59131005f8c89880
  | 3 => 0x802012000000010000040080000200000800010008040020000100700200200c0300000000801802002000008010000000080000001400804006008020040000040080200e0300080200a0000000100000c008000040000000d0000200000a002004028010020000080000000000003000020000010000000080100000008800000004040000000000000200400c00000002008000040020000080000c01000009006000000030040000000100000002803000010008010020000000000a00800801004000008000040000000200a00000801005fcc9a9803be64d4c015f326a600bf593530077ac9a9802bd64d4c017f316a600fb98b53005dcc5a9802fd62d4c01f6b16a600bb58b53005fcc3a9803f661d4c017b30ea600bf58753007eac3a9802f561d4c017f306a600bf58353005facb29802fe6494c01df324a600af99253005fac929803bd6494c015eb24a600dfd5253005fcc7298037f5394c01efa9ca600bf98a53007dcc529802ee6294c017eb14a600fb58a53005dac529802fe6194c01fb30ca600bd98653005fac329803f56194c017ab0ca600bf98253005fac129802ff6454c017e322a600df95153007bea6a98037e5354c017fb12a600bf18953005fec2a9802fc6154c017fb02a600bf18153005fcca29802fe6414c017eb20a600dfd5053006faa829802fe6314c01bfa98a600f794c53006faa629803dd5314c01aea98a600bf98853005fac429802fe6114c017eb08a600bf98053005fac029802ff6590c017f32c8600df99643004fccb21802fd6590c01beb2c86009f59643005f8cb21802fd6490c01df2a48600ef55243005fcc721803df5390c01ee29c8600f7d0e43005fcc521803ee6290c01773148600bf58a43007dac521802ed6290c017f30c8600fd98643005ecc321802fd6190c01fab0c8600bd58643005fcc121802fd6090c017fb2a8600bf99543005facaa1802fc6550c01efa9a8600f714d430077c86a1802ff6150c017e30a8600bfd8143005f8c0a1802ff6510c017f3288600bf59443005f8ca21802fe6310c01ef2988600f754c43007bc8621803dd4310c01cea188600bf98443005fac221802fe6010c017eb008600bf993510077cc9a8802be64d44017eb26a200ef593510057ac9a88037e54d4401be2a6a200bf98f51007bcc7a8802de63d44017eb1ea200f758f51005bac7a88037e53d4401be29ea200bf98b51007dcc5a8802ee62d44017eb16a200fb58b51005dac5a8802fe60d44017eb06a200bf59651005fcc928803be64944015f324a200bf592510077ac928802bd6494401bfaa4a200df55251005fcc728803de63944016f31ca200bf58e51007bac728802dd6394401bfa9ca200df54e51005fcc528803ee629440177314a200bf58a51007dac528802ed6294401bfa94a200bf986
  | 4 => 0x9f8ea00043e65d48e32bc81ca0001e800000cd40057c0004d80048800000000000a49929f545252c12800000000e98000000000000000066000098c0cae8000005ae000002d287c0010d00029e000000006589248b347000964002eb2bdc4c25a415a40000000012f1340026437400000000000000000000000001ca481428a98b02f0000fd0ba1b37c3fc0003b00013200000000000022c700000000013000a2c000000000000000000000000000000a7d1c800000000000000001200003a0000000fa160005a0ff0000f647c441c21c2926000004d4b94000000004c344a3c000000b3eb6000000000002de798003324bd0016d13600029c0033c215522000003d400118c25de9000001a51ca2891f8000000000018506ccb200000000c70b2137000001360000006a86782c364000f4000000000000000000002e80028b8556c006c550006180000058c875e20009e71b00006e51a001db0000015419e8000009f0000007ee0000044e00159802000000000002f24a76e0002b8001020000000000000000092800000000a037f0bf0880000000000000000000000080de40013f000000004862d068000000000002f0c380009e44545a0014a9b8d9d974d8157be03119bad08002bc9ddf42f89ac188000a20013f800614000000000000000000017c000f619c04c0000000000000000000000001664683f0bb491edd5fe566000000000000023800000086c00000000002254a7568b9c000000008aa7b1f40000000000000000129000840de2083be6046680000091d6186963c524f98795140000a19b0004d21729136800184a7851c226ba400000000a8800000b066e9ae000000000001be44a00136c760a83e3200001bc00000000528858004aa000e687a000000000000000006b4005aa6e0549b10009600019a1bc9d91f0ae3d200104b2f4c6000d7a663d60000028109c56000000000000002a300078c6b00000000000000602a9487800000a1000000000000001cc000abd3e226000b46b38002b6493864002b20011631b5a62b0e720e00100000000004010010000000000000080100600c008090080000000100800c058000040040000300003400003002000130010020000000300200000000008004018000040100000100a0080000100000c000030080000400a004008060000120000700e0080000080000000c0180000201c0001b00600002800002020000060000040000100000c000020000000000301e000000000000040100a004024000010000080000800000400800002008030020000080800000400001000002000000000000080400b01a00000007004000000000060000080200e0040000000600800801008028008050000280000100a01000003000008078010020380000000200002804000000008000000000
  | 5 => 0x6c9b7d72c680000029b00000000000270000000617bda294811a6385930c0001be3c11a238000aa80015700000029538698088000000014b1995e409a000000004140000000000029c0700000000000674430fbb070000006d000000298000aa12600000000000000001b50a800133971800000000000ca0000026100000000000000000000a0800456000006867f0a28151c5000000000000012b07500014c00121000000002f45820016d9b33480000016fb4033177281e60752000002ada98b6ac0112c44002fd1c355863657229b20a38a562a4d14686b1626dc121c4326504001430ee00000073255c2eeb15016e448d62d400078400080000000db24d1f23ad2e0001ed300001f0a30001718630000000022229a3dda0882000000a600013400000000610000001ef800c48f68620ac48c000000000007a00005b00000000000afc000001700000009750abb000000000000f70b0080004003444e65ad56000000000b053e834000000000008480021911809c0000000000000000386304000000002d80009f000000000001320000000043c0000005cbf69d4002bb64600000237000650951d1656000c8000000ca50987380000000000000000002e2000000700b9000533088ba504550302f5000a269440063200097cec2e8000471c645e000002a24f10000016900000000033000d014a000000774bf80052eaad3e8000004260003d1cb52f3cab7000000f9220000000870005f60009c4005522180016c6062ec45a428000016f29d0a9000c91e761e5b8b503801a85e1401b4180004a800000001500000004000000000014922986dbe00000006000bc00000060ccd80005e2720019680008e000000000000007adf7b5ab389ed8c0000014d80500000000000006498003041c80008806100047f5a00013c000c4b2155a3a8818004e44f0cdc5f02e0005e0000000000000000000106a60128001700bd0000000000000000110c000006f6675168004ac0000031a0000000000000047800000000000002ec0018bb380001a9368002895cb3400000000000000000000a3c000000000004b8000007c000000890000002bfa4d2f0c628c240e90000ec0000000019c00000000498000000005bb0000012f4e8000003271080000000046a83c9fe5b2040004b1782280740000021229000005aca7e53291c800b10000000000015800e0dc420000003bc00185800000000000002b110cdf921abe1c40c2a7000616971e568c3d800000217be46111d628000000001b61400024a800104add7b4ee82892f055920000000000000158aa980000000000000000001f1000000c50001aa3e6000000000000001230c000cf1c024853f7ac829ea608c3a053f457800000000ba0dda6e3720000b2530007690080040449e00000000000000002323c077
  | 6 => 0x1305105997027563c910003b2c8824a9e0002a134918a1a0003a2835efccc568000005499300c23d00000000000000c6c000000000000046244e50081000000000002e2000000000004c6001404425c8001a7000000158d910b0002e2d980032800218800600001610da0000000000000000000000b180021d5700000000055c16c0014980080c2ca8c00045f679330440019f0002fd000000fe5f44c400000631000436341f888c001768004443f8003c0b2800000000bf0001620007291800a000000000004e200000000000000737390000019880000091800000000314000cb60400088400000000000000000008080000081d37c0000000120c004cd00000000000ad4230000e44e8001a2000001a100055482c000001ce8502c000146078c22dbc644ceb329045c4180007d61a00000000000770fc4004de00063800000a6016911dac432000000000000000010a8bb1d3355422b34cc080d7000e4299000cecfb02300068c0000039e00000000000cf476800000000002e1620000001268d802c0000000067533c00350bbc2b8005b5c394d00f00035c00000551130960091d0000001d8000000000b5000000000000004f40004f000001920000004e6001ab000199658001f6000001e0b2c000001770000000021ccbe8be000005f0000002688000000019f4967374317538a3bc938420000013d20017f000000000000011e81c094000000d800000000000042000002d149945c000001a8000a99c90000000000059a62d2d17a000754002e757a621200f0b8e000000dc4a26f40000030600000000322508000000000000000000000000000000000000000000008f000000000000002b500037400265040e815d5b90f1210d12e6cfc00113000a90001b4e5cc0143a5226000000000668000ca800000bcc000002ae4fc0003c8003b6d9e1826442841b285783f4380ab241325750003475f600000000000002e9257000002c228700045000000bdc000f2000000001fd2450002a800000494ae435000000969380000008ec7e0004100012000038c000000000018c2800000000010729d00000000000000000000000010dd0f8005f8be8000000000000063a000e0800000b90001285eca3c00000000001380001d20009d8000008a00000000040315acc0ce06400000000b4049000000000e666256487b7f4d58645386924e000000000f1000000d08002360005f4000000000000000040e0000002b000d4a54000b14002330000004e8e20b7580439d98b4ca800000000b0b8faf12bb000001ff3ae0d00000049e000180000000000000000000000000000000002e626a24400000000399486cb96700128000000000000001e652a00000000000000d32e100032288000b3e9acc8396001
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x4644c510006d4634c510006e4624c510004f67688510005757588510006746588510005b57488510006b46488510005d57388510006d46388510006e46288510006746548510006b46448510006d46348510006e46248510006746584110006b46484110006d46384110006e46284110004be74d9410004bd74d9410004de73d9410004dd73d9410004ee72d9410004ed72d94100047d76994100067471594100047e7519410004be7419410004bd7419410004de7319410004dd7319410004ee7219410004ed7219410004f671194100047e75d90100047d75d9010004de73d9010004dd73d9010004ee72d9010004ed72d9010004bd76990100063e65990100063d65990100063e65590100063d6559010006b471590100047e75190100047d7519010004be7419010004de7319010004dd7319010004ee7219010004ed7219010004f671190100047e75d8c100047d75d8c10004be74d8c10004bd74d8c10004ee72d8c10004ed72d8c10004dd7698c100065e6598c100065d6598c100069e6498c100069d6498c100065e6558c100065d6558c100069e6458c100069d6458c10006d47158c100047e7518c100047d7518c10004be7418c10004bd7418c10004de7318c10004ee7218c10004ed7218c10004f67118c100047e75d88100047d75d8810004be74d8810004bd74d8810004de73d8810004dd73d8810004ed76988100066e65988100066d6598810006ae6498810006ad6498810006ce6398810006cd63988100066e65588100066d6558810006ae6458810006ad6458810006ce6358810006cd6358810006e471588100047e75188100047d7518810004de7318810004dd7318810004f67118810004f576d44100067565d4410005b674d4410006b564d4410005d673d4410006d563d4410005e672d4410006e562d4410004f57614410006756514410006b56414410006d56314410006e56214410004f576d04100057675d04100067565d0410006b564d0410005d673d0410006d563d0410005e672d0410006e562d0410004f57610410006756510410006b56410410006d56310410006e56210410004f576cc4100057675cc4100067565cc410005b674cc410006b564cc410006d563cc410005e672cc410006e562cc410004f5760c41000675650c410006b5640c410006d5630c410006e5620c410004f576c84100057675c84100067565c8410005b674c8410006b564c8410005d673c8410006d563c8410006e562c8410004f57608410006756508410006b56408410006d56308410006e562084100067565c4010006b564c4010006d563c4010006e562c4010004f97684010004f77644010005747544010006756544010005b47444010006b56444010005d47344010006d56344010005e47244010006e56244010004fb7644010
  | 1 => 0x9610004bd7419610004de7319610004dd7319610004ee7219610004ed72196100047f75592100047c7559210004df7359210004dc7359210004ef7259210004ec72592100047e75192100047d7519210004de7319210004dd7319210004ee7219210004ed72192100047f7558e100047c7558e10004bf7458e10004bc7458e10004ef7258e10004ec7258e100047e7518e100047d7518e10004be7418e10004bd7418e10004ee7218e10004ed7218e100047f7558a100047c7558a10004bf7458a10004bc7458a10004df7358a10004dc7358a10005b674d4610005d673d4610005e672d46100067765146100057675d0610005d673d0610005e672d0610006b764106100057675cc610005b674cc610005e672cc610006d7630c6100057675c8610005b674c8610005d673c8610006e762086100047e7599510004be7499510004bd7499510004de7399510004dd7399510004ee7299510004ed7299510004bf7459510004bc7459510004df7359510004dc7359510004ef7259510004ec7259510004f771595100047e76195100067571195100063f65d91100063c65d91100047e75991100047d7599110004be7499110004de7399110004dd7399110004ee7299110004ed72991100047f75591100047c7559110004df7359110004dc7359110004ef7259110004ec7259110004f77159110004be76191100063f65191100063c6519110006b571191100065f65d8d100065c65d8d100069f64d8d100069c64d8d100047e7598d100047d7598d10004be7498d10004bd7498d10004de7398d10004ee7298d10004ed7298d100047f7558d100047c7558d10004bf7458d10004bc7458d10004ef7258d10004ec7258d10004f77158d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d10006d57118d100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100047e75989100047d7598910004be7498910004bd7498910004de7398910004dd73989100047f75589100047c7558910004df7358910004dc7358910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc6318910004f67694510006746594510005b57494510006b46494510005d57394510006d46394510005e57294510006e46294510004f47654510006746554510006b46454510006d46354510006e46254510004f67690510005757590510006746590510006b46490510005d57390510006d46390510005e57290510006e46290510004f47650510006746550510006b46450510006d46350510006e46250510004f6768c51000575758c51000674658c510005b5748c510006b4648c510006d4638c510005e5728c510006e4628c510004f4764c51000674654c510006b
  | 2 => 0x4f571194300047e75d90300047d75d9030004ee72d9030004ed72d9030004f671d9030004f571d9030004bd76990300063e65990300063d65990300063e65590300063d65590300069c73590300047e75190300047d7519030004de7319030004f67119030004f57119030004dd76d4c300065d65d4c300059e74d4c300069d64d4c30005ce72d4c30005d671d4c30004dd7614c300065d6514c300069d6414c30004dd76d0c300055e75d0c300065d65d0c300069d64d0c30005ce72d0c30005d671d0c30004dd7610c300065d6510c300069d6410c300066e65988300066d6598830006ae6498830006ad64988300066e65588300066d6558830006ae6458830006ad6458830006cf5358830006cc5358830006cf4358830006cc4358830004dd768c8300055e758c8300065d658c8300059e748c8300069d648c830006cd628c830005d6718c8300065d650c8300069d640c830006cd620c830006766598430006756598430006b66498430006b56498430006e66298430006e56298430006766558430006756558430006b66458430006b56458430006e66258430006e56258430006d75358430006d45358430006d74358430006d44358430006d63258430006d43258430004dd768c4300055e758c4300065d658c4300059e748c4300069d648c430005ce728c430006cd628c430006d5618c4300065d650c4300069d640c430006cd620c430006d5610c4300065d65cc0300069d64cc030006cd62cc030006d561cc030004df764c0300055c754c0300065d654c0300059c744c0300069d644c030005cc724c030006cd624c030005d4714c030006d5614c030004fb764c030004be74d9710004bd74d9710004de73d9710004dd73d9710004ee72d9710004ed72d9710004be7499710004bd7499710004de7399710004dd7399710004ee7299710004ed72997100047e75d93100047d75d9310004de73d9310004dd73d9310004ee72d9310004ed72d93100047e75993100047d7599310004de7399310004dd7399310004ee7299310004ed72993100047e75d8f100047d75d8f10004be74d8f10004bd74d8f10004ee72d8f10004ed72d8f100047e7598f100047d7598f10004be7498f10004bd7498f10004ee7298f10004ed7298f100047e7598b100047d7598b10004be7498b10004bd7498b10004de7398b10004dd7398b10006766594710005b57494710005d57394710005e57294710006746554710005757590710006b66490710005d57390710005e57290710006b4645071000575758c710005b5748c710006d6638c710005e5728c710006d4634c710005757588710005b57488710005d57388710006e66288710006e46248710004bf7459610004bc7459610004df7359610004dc7359610004ef7259610004ec7259610004be741
  | 3 => 0xe7498730004bd7498730004ee7298730004ed72987300055d75cc7300059d74cc730005cd72cc730006d661cc730004bf7459630004bc7459630004ef7259630004ec7259630004f77159630004f47159630004be7419630004bd7419630004ee7219630004ed7219630004f67119630004f571196300047f75592300047c7559230004ef7259230004ec7259230004f77159230004f471592300059e74d4e30005ce72d4e30005d671d4e300065f6514e300055e75d0e30005ce72d0e30005d671d0e300069f6410e300047f7558a300047c7558a30004bf7458a30004bc7458a30004f77158a30004f47158a300055e758ca300059e748ca30005d6718ca300047f75586300047c7558630004bf7458630004bc7458630004ef7258630004ec72586300055e758c6300059e748c630005ce728c6300047e7599530004be7499530004bd7499530004ee7299530004ed7299530004f67199530004f57199530004bf7459530004bc7459530004df7359530004ef7259530004ec7259530004f77159530004f471595300047e76195300065d73195300063f65d91300063c65d91300047e75991300047d7599130004ee7299130004ed7299130004f67199130004f571991300047f75591300047c7559130004f77159130004f47159130004be76191300063f65191300063c6519130004de7694d300065c6594d300059d7494d300069c6494d30005cd7294d30005d57194d30004dc7654d300065c6554d300069c6454d30004de7690d300055d7590d300065c6590d300069c6490d30005cd7290d30005d57190d300065c6550d300069c6450d300066f65d89300066c65d8930006af64d8930006ac64d89300066f65189300066c6518930006af6418930006ac6418930006ce5318930006cd5318930006ce4318930006cd4318930004de76cc9300055d75cc9300065c65cc9300059d74cc9300069c64cc930006cc62cc930005d571cc9300065c654c9300069c644c930006cc624c9300067765d85300067465d8530006b764d8530006b464d8530006e762d8530006e462d8530006776518530006746518530006b76418530006b46418530006e76218530006e46218530006d65318530006d55318530006d64318530006d54318530006d73218530006d53218530004de76cc5300055d75cc5300065c65cc5300059d74cc5300069c64cc530005cd72cc530006cc62cc530006d461cc5300065c654c5300069c644c530006cc624c530006d4614c5300065c658c1300069c648c130006cc628c130006d4618c130004be74d9430004bd74d9430004ee72d9430004ed72d9430004f671d9430004f571d94300047d76994300065c73594300047e7519430004be7419430004bd7419430004de7319430004ee7219430004ed7219430004f67119430
  | 4 => 0x8421005e470484210047f75580210047c7558021004df7358021004dc7358021006e52158021004be7498f50004bd7498f50004ee7298f50004ed7298f50004f67198f50004f57198f500053d74d4f500065e63d4f500056d72d4f500057571d4f50004be7498750004bd7498750004de7398750004dd7398750004ee7298750004ed72987500053d74d47500055d73d47500056d72d47500067661d4750004bf7458e50004bc7458e50004ef7258e50004ec7258e50004f77158e50004f47158e500053e7494e500056e7294e50005767194e50004bf7458650004bc7458650004df7358650004dc7358650004ef7258650004ec72586500053e74946500055e73946500056e72946500069f64d8d500069f6418d500069c6418d500047e76d4d500053d74d4d500063c64d4d500065c63d4d500056d72d4d500057571d4d500063c6454d500065c6354d50006b764d8550006b464d8550006d763d8550006d463d8550006e762d8550006b76418550006b46418550006d76318550006d46318550006e76218550006e462185500067754185500067554185500067753185500067553185500047e76d45500053d74d45500063c64d45500055d73d45500065c63d45500056d72d45500066c62d45500067461d45500063c64545500065c63545500066c62545500067461545500065c63941500067461941500069e6498c500069e6458c500069d6458c500047d7694c500053e7494c500063d6494c500065d6394c500056e7294c50005767194c500063d6414c500065d6314c50006b66498450006b56498450006d66398450006d56398450006e66298450006b66458450006b56458450006d66358450006d56358450006e66258450006e562584500067654584500067454584500067653584500067453584500047d76944500053e74944500063d64944500055e73944500065d63944500056e72944500066d62944500067561944500063d64144500065d63144500066d62144500067561144500065d63d40500067561d40500047f76540500055c73540500065d6354050005747154050006756154050004fb7654050004be74d9730004bd74d9730004ee72d9730004ed72d9730004f671d9730004f571d9730004be7499730004bd7499730004ee7299730004ed7299730004f67199730004f571997300047e75993300047d7599330004ee7299330004ed7299330004f67199330004f571993300065e6594f300059d7494f30005cd7294f30005d57194f300065c6554f300055d7590f300069e6490f30005cd7290f30005d57190f300069c6450f300047e7598b300047d7598b30004be7498b30004bd7498b30004f67198b30004f57198b300055d75ccb300059d74ccb30006ce62ccb30005d571ccb300047e75987300047d7598730004b
  | 5 => 0x5ad7494a21006ae6494a21005cd7394a21006ce6394a21005e57194a210066e6554a21006ae6454a21006ce6354a210056d7590a210066e6590a21006ae6490a21005cd7390a21006ce6390a21005e57190a210066e6550a21006ae6450a21006ce6350a210056d758ca210066e658ca21005ad748ca21006ae648ca21006ce638ca21005e5718ca210066e654ca21006ae644ca21006ce634ca210067565d4621005b674d4621006b564d4621005d673d4621006d563d4621005e672d46210076652d4621006756514621006b56414621006d56314621005e672146210076552146210057675d06210067565d0621006b564d0621005d673d0621006d563d0621005e672d0621007a642d0621006756510621006b56410621006d56310621005e67210621007a542106210057675cc6210067565cc621005b674cc621006b564cc621006d563cc621005e672cc621007c632cc62100675650c621006b5640c621006d5630c621005e6720c621007c5320c6210057675c86210067565c8621005b674c8621006b564c8621005d673c8621006d563c8621004de73d9521004dd73d9521004de7399521004dd7399521004f571995210047e75d8d210047d75d8d21004be74d8d21004bd74d8d210047e7598d210047d7598d21004be7498d21004bd7498d21004ed7298d21004f57198d21004f676d4521005b674d4521005d673d4521005e672d4521004f67614521006756514521007675214521004f676d05210057675d0521005d673d0521005e672d0521004f67610521006b56410521004f676cc5210057675cc521005b674cc521005e672cc521007c432cc521004f6760c521006d5630c521007c7320c5210056e7588521005ae7488521005ce73885210047e75181210047d7518121004de7318121004dd7318121004de73d9421004dd73d9421004f671d9421004de7399421004dd73994210047e75d8c210047d75d8c21004be74d8c21004bd74d8c21004ee72d8c21004f671d8c210047e7598c210047d7598c21004be7498c21004bd7498c210047e75984210047d7598421004be7498421004bd7498421004de7398421004dd7398421004f57694421006766594421005b57494421005d57394421005e57294421004f77654421006746554421007665254421004f57690421005757590421006b66490421005d57390421005e57290421004f77650421006b46450421004f5768c42100575758c421005b5748c421006d6638c421005e5728c421007c5328c421004f7764c421006d4634c421007c6324c421005757588421005b57488421005d57388421005e57288421004f77648421005e77648421006e77648421005e77548421005e57548421006e66548421006e46548421005e77348421005e57348421006e66348421006e4634
  | 6 => 0x6718c931004de760c931004f676d4531005b674d4531005d673d45310075453d4531005e672d4531004f67614531006756514531007575314531004f676d05310057675d0531005d673d05310079443d0531005e672d0531004f67610531006b564105310079743105310057675cc531005b674cc531005e672cc5310055e758c5310059e748c531005ce728c5310047e75181310047d7518131004be7418131004bd7418131004ee7218131004ed7218131004be74d9431004bd74d9431004de73d9431004ee72d9431004ed72d9431004f671d9431004be7499431004bd7499431004ee7299431004ed72994310047e75d90310047d75d9031004de73d9031004ee72d9031004ed72d9031004f671d90310047e75990310047d7599031004ee7299031004ed72990310047e7598c310047d7598c31004be7498c31004bd7498c31004dd7694c310065e6594c310059d7494c31005cd7294c31005d57194c31004df7654c310065c6554c31004dd7690c310055d7590c310069e6490c31005cd7290c31005d57190c31004df7650c310069c6450c310047e75988310047d7598831004be7498831004bd74988310055d75cc8310059d74cc831006ce62cc831005d571cc831004df764c8310047e75984310047d7598431004be7498431004bd7498431004f57694431006766594431005b57494431005d57394431007555394431005e57294431004f77654431006746554431007565354431004f57690431005757590431006b66490431005d57390431007954390431005e57290431004f77650431006b464504310079643504310055d75cc4310059d74cc431005cd72cc43100575758c431005b5748c431005d5738c431005e5728c431004df764c431004f7764c431005d7764c431006d7764c431005d7754c431005d5754c431006d6654c431006d4654c431005d7744c431005d5744c431006d6644c431006d4644c431005d7724c431006d6624c431005d4704c4310047f75580310047c7558031004bf7458031004bc7458031004ef7258031004ec7258031006d53158031004be74d9621004bd74d9621004de73d9621004dd73d96210066d7299621006747159621004be7419621004bd7419621004de7319621004dd73196210047e75d92210047d75d9221004de73d9221004dd73d92210063e65992210063d6599221006ad72992210063e65592210063d6559221006b471592210047e75192210047d7519221004de7319221004dd73192210047e75d8e210047d75d8e21004be74d8e21004bd74d8e210065e6598e210065d6598e210069e6498e210069d6498e21006cd7298e210065e6558e210065d6558e210069e6458e210069d6458e21006d47158e210047e7518e210047d7518e21004be7418e21004bd7418e210066e6594a21
  | 7 => 0x8b31006cf5358b31006cc5358b31006cf4358b31006cc4358b310055e758cb310065d658cb310059e748cb310069d648cb31006cd628cb31005d6718cb310065d650cb310069d640cb31006cd620cb31005d6710cb31006766594731005b57494731006b66494731005d57394731007575394731005e57294731006e66294731006766554731006b66454731007545354731006e66254731005757590731006766590731006b66490731005d57390731007974390731005e57290731006e66290731006766550731006b66450731007944350731006e66250731004be74d9631004bd74d9631004ee72d9631004ed72d96310065d7399631006747159631004be7419631004bd7419631004ee7219631004ed72196310047e75d92310047d75d9231004ee72d9231004ed72d92310063e65992310063d65992310069d73992310063e65592310063d6559231006b471592310047e75192310047d7519231004ee7219231004ed72192310065e6594e310059d7494e310069e6494e31005cd7294e31005d57194e310065e6554e310069e6454e310055d7590e310065e6590e310069e6490e31005cd7290e31005d57190e310065e6550e310069e6450e310066e6598a310066d6598a31006ae6498a31006ad6498a31006ce5398a31006cd5398a31006ce4398a31006cd4398a310066e6558a310066d6558a31006ae6458a31006ad6458a31006e47158a310055d75cca310065e65cca310059d74cca310069e64cca31006ce62cca31005d571cca310065e654ca310069e644ca31006ce624ca310067565d4631005b674d4631006b564d4631005d673d46310075653d4631005e672d4631006e562d4631006756514631006b56414631005d67314631007555314631006e562146310057675d06310067565d0631006b564d0631005d673d06310079643d0631005e672d0631006e562d0631006756510631006b56410631005d67310631007954310631006e562106310055d75cc6310065e65cc6310059d74cc6310069e64cc631005cd72cc631006ce62cc6310057675cc6310067565cc631005b674cc631006b564cc631005e672cc631006e562cc631004be74d9531004bd74d9531004ee72d9531004ed72d9531004be7499531004bd7499531004dd7399531004ee7299531004ed7299531004f571995310047e75d91310047d75d9131004ee72d9131004ed72d91310047e75991310047d7599131004dd7399131004ee7299131004ed7299131004f57199131004de76d4d310059e74d4d31005ce72d4d31005d671d4d31004de7614d310065d6514d31004de76d0d310055e75d0d31005ce72d0d31005d671d0d31004de7610d310069d6410d310047e75d89310047d75d8931004be74d8931004bd74d89310055e758c9310059e748c931005d
  | 8 => 0x6d563d0641005e672d0641006e562d0641004de73d9541004dd73d9541004ee72d9541004ed72d9541004bd7499541004de7399541004dd7399541004ee7299541004ed7299541004f57199541004be76d51410063f65d51410059e73d5141005ae72d5141005b671d5141004be76151410063d65151410047e75d8d410047d75d8d41004ee72d8d41004ed72d8d410053e7590d41005ae7290d41005b67190d41004be7610d410047e75d89410047d75d8941004de73d8941004dd73d8941004f676d4541005b674d45410073454d4541005d673d4541005e672d4541004f676145410067565145410073754145410057675d0541005d673d0541005e672d05410053e75905410059e7390541005ae72905410047e75181410047d7518141004de7318141004dd7318141004ee7218141004ed7218141004be74d9441004de73d9441004dd73d9441004ee72d9441004ed72d9441004f671d9441004de7399441004dd7399441004ee7299441004ed72994410047e75990410047d7599041004bd76950410063e65950410059d7395041005ad7295041005b57195041004bf76550410063c65550410047e7598c410047d7598c41004ee7298c41004ed7298c410053d75d0c410069e63d0c41005ad72d0c41005b571d0c41004bf7650c410047e75988410047d7598841004de7398841004dd73988410047e75984410047d7598441004f57694441006766594441005b57494441007355494441005d57394441005e57294441004f776544410067465544410073654544410053d75d04410059d73d0441005ad72d0441005757590441005b57490441005d57390441005e57290441004bf7650441004f77650441005b77650441006b77650441005b77550441005b57550441006b66550441006b46550441005b77350441006b66350441005b77250441006b66250441005b470504410047f75580410047c7558041004df7358041004dc7358041004ef7258041004ec7258041006b54158041004be74d9731004bd74d9731004ee72d9731004ed72d97310067571997310065c7359731004be7419731004bd7419731004ee7219731004ed72197310047e75d93310047d75d9331004ee72d9331004ed72d93310063e65993310063d6599331006b571993310063e65593310063d65593310069c73593310047e75193310047d7519331004ee7219331004ed72193310065d65d4f310059e74d4f310069d64d4f31005ce72d4f31005d671d4f310065d6514f310069d6414f31005d67114f310055e75d0f310065d65d0f310069d64d0f31005ce72d0f31005d671d0f310065d6510f310069d6410f31005d67110f310066e6598b310066d6598b31006ae6498b31006ad6498b31006e57198b310066e6558b310066d6558b31006ae6458b31006ad645
  | 9 => 0xd7318151004ee7218151004ed7218151004de7399051004dd7399051004ee7299051004ed72990510063e64d50510055d73d50510056d72d50510057571d50510047f7655051004be7498c51004bd7498c51004ee7298c51004ed7298c510053d74d4c510065e63d4c510056d72d4c510057571d4c510047f7654c51004be7498851004bd7498851004de7398851004dd73988510053d74d48510055d73d48510066e62d48510057571d48510047f76548510053d74d44510055d73d44510056d72d4451005757594451005b57494451005d57394451005e572944510047f7654451004f77654451005777654451006777654451005777454451006766454451005777354451006766354451005777254451006766254451005747054451004bf7458051004bc7458051004df7358051004dc7358051004ef7258051004ec7258051006755158051004de73d9741004dd73d9741004ee72d9741004ed72d97410067571997410063c7459741004de7319741004dd7319741004ee7219741004ed72197410063d65d53410059e73d5341005ae72d5341005b671d53410063d6515341005b671153410065e6598f410065d6598f41006d57198f410065e6558f410065d6558f410069f5458f410069c5458f410053e7590f410063d6590f410069d6390f41005ae7290f41005b67190f410063d6510f410069d6310f41005b67110f410066e6598b410066d6598b41006ce6398b41006cd6398b410066e6558b410066d6558b41006ce6358b41006cd6358b41006af5458b41006ac5458b41006ae4358b41006ac4358b41006766594741005b57494741007375494741005d57394741006d66394741005e57294741006e66294741006766554741007345454741006d66354741006e66254741004de73d9641004dd73d9641004ee72d9641004ed72d96410063d7499641006747159641004de7319641004dd7319641004ee7219641004ed72196410063e65952410059d7395241005ad7295241005b571952410063e65552410065e6598e410065d6598e410069e5498e410069d5498e410065e6558e410065d6558e41006d47158e410053d75d0e410063e65d0e410069e63d0e41005ad72d0e41005b571d0e410063e6550e410069e6350e410066e6598a410066d6598a41006ce6398a41006cd6398a41006ae5498a41006ad5498a41006af4398a41006ad4398a410066e6558a410066d6558a41006ce6358a41006cd6358a410067565d4641005b674d46410073654d4641005d673d4641006d563d4641005e672d4641006e562d4641006756514641005b67414641007355414641006d56314641006e562146410053d75d06410063e65d06410059d73d06410069e63d0641005ad72d0641006ae62d06410057675d06410067565d0641005d673d0641
  | 10 => 0x4d43004de7614d430065d6514d430071f5414d430053e7590d43005ae7290d43005b67190d430047e75d85430047d75d8543004ee72d8543004ed72d85430047e75181430047d7518143004f67118143004f57118143004de73d9443004f671d9443004f571d9443004f67199443004f571994430047e7598c430047d7598c43004dd7694c430065e6594c430059d7494c43005cd7294c43005d57194c43004df7654c430065c6554c430071e5454c430055d7590c430059d7490c43005cd7290c43005d57190c43004df7650c430059f7650c430069f7650c430059f7550c430059d7550c430069e6550c430069c6550c430059f7150c430059c7050c430047e75984430047d75984430069d4398443004ee7298443004ed72984430047f75580430047c75580430069d4358043004f77158043004f47158043006b571993510063d64953510055e73953510056e72953510057671953510063d64153510057671153510069e6498f510069d6498f51006d57198f510069e6458f510069d6458f510065e5458f510065c5458f510053e7494f510063d6494f510065d6394f510056e7294f51005767194f510063d6414f510065d6314f51005767114f51006ae6498b51006ad6498b51006ce6398b51006cd6398b51006ae6458b51006ad6458b51006ce6358b51006cd6358b510066e5458b510066c5458b510066e5358b510066c5358b51006b471592510063e64d52510055d73d52510056d72d52510057571d52510063e64552510069e6498e510069d6498e510065f5498e510065d5498e510069e6458e510069d6458e51006d47158e510053d74d4e510063e64d4e510065e63d4e510056d72d4e510057571d4e510063e6454e510065e6354e51006ae6498a51006ad6498a51006ce6398a51006cd6398a510066f5498a510066d5498a510066f5398a510066d5398a51006ae6458a51006ad6458a51006ce6358a51006cd6358a51006e47158a510053d74d4a510063e64d4a510055d73d4a510065e63d4a510066e62d4a510057571d4a510053d74d46510063e64d46510055d73d46510065e63d46510056d72d46510066e62d4651005b674d4651006b564d4651005d673d4651006d563d4651005e672d4651006e562d4651004de73d9151004dd73d9151004ee72d9151004ed72d91510063f64951510055e73951510056e72951510057671951510047e7615151004be74d8d51004bd74d8d51004ee72d8d51004ed72d8d510053e7494d510056e7294d51005767194d510047e7614d51004be74d8951004bd74d8951004de73d8951004dd73d89510053e74949510055e7394951005767194951005b674d4551005d673d4551005e672d45510053e74945510055e73945510056e7294551004be7418151004bd7418151004de7318151004d
  | 11 => 0x6ad6498b53006ae6458b53006ad6458b53006b66498753006b56498753006e66298753006e56298753006b66458753006b56458753006e66258753006e562587530069c73592530063e64d52530055d73d52530056d72d52530057571d52530053d74d4e530063e64d4e530056d72d4e530057571d4e530059e74d4e530069d64d4e53005ce72d4e53005d671d4e53006ae6498a53006ad6498a530066f5498a530066f5398a53006ae6458a53006ad6458a53006cf5358a53006b66498653006b56498653006e66298653006e56298653006775498653006775398653006b66458653006b56458653006e66258653006e56258653006d75358653004ee72d9153004ed72d9153004f671d9153004f571d91530063f64951530055e73951530056e72951530057671951530059e74d4d53005ce72d4d53005d671d4d530053e7494d530056e7294d53005767194d53004be74d8953004bd74d8953004f671d8953004f571d8953004be74d8553004bd74d8553004ee72d8553004ed72d8553004be7418153004bd7418153004ee7218153004ed7218153004f67118153004f57118153004ee7299053004ed7299053004f67199053004f571990530063e64d50530055d73d50530056d72d50530057571d50530047f76550530053d74d4c530056d72d4c530057571d4c530055d7594c530059d7494c53005cd7294c53005d57194c530047f7654c53004df7654c530055f7654c530065f7654c530055f7454c530065e6454c530055f7254c530055f7154c530055c7054c53004be7498853004bd74988530065d5398853004f67198853004f57198853004be7498453004bd74984530065d5398453004ee7298453004ed7298453004bf7458053004bc74580530065d5358053004ef7258053004ec7258053004f77158053004f47158053004ee72d9643004ed72d9643004f671d9643004f571d96430063d74996430065c7359643004ee7219643004ed7219643004f67119643004f571196430063e65952430059d7395243005ad7295243005b571952430063e65552430065d65d4e430059e74d4e430071e54d4e43005ce72d4e43005d671d4e430065d6514e430059e7414e430071d5414e430055e75d0e430065d65d0e430066e6598a430066d6598a43006ae5498a43006ad5498a43006af4398a430066e6558a430066d6558a43006cf5358a43006cc5358a43006cf4358a43006766598643006756598643006e66298643006e56298643006b65498643006b55498643006b74398643006766558643006756558643006e66258643006e56258643006d75358643006d45358643006d743586430063f54d9543004f671d9543004f571d9543004dd7399543004f67199543004f57199543004de76d4d430059e74d4d43005ce72d4d43005d671d
  | 12 => 0xa00502901d01701702400200a02301a00500c00a00f01100300500300000100200000100600500000000400000900200007200000401600300000103800c01100202100c00500000002100000700400200800000800900a00100b00c00000800300404d00101100e00600300f00200003900700100600800c00100300100f00900201d01400e01200000e02202500b02600a00001600200000800100200000405402c00000000a00100000400300400001200800200b00300000400500400000500100000200a00100001a00000300101d00000200001c00500300500000800300200900000400800700200000000300300f00500800701300400500000100000800200000200701900300600400202700200000700000601000800701801001600100300100601b00300001201100100400000000101800c00200101104f05800000000003600100300100700900000c00202a00300500200105400000703a01000000700500400200200a00000402900201100601500400000000100100001300f00600000300002a00000e00600100800a00100000100300000900002800200300000200000b01d00900b00900800300100b00000000a00301200001c00500000000b00202400d00d00001000b00602000000400a00f00800100200200500400001000100d00300100001500100000300000000000200000001700001900600000500000803600302a00000400201b00401600400400000000000100000100000000001100401900402400300600001b00900000900500904400100102e00201a00602e00400001800000300a00400001d00400602801000201b00b00500602000000700600900501400600100100100801500a00200800000102a00000500301500001a00400000300800100400700100300500000000000800000000000500000200300001e00203500000a00300800200200000000001d00400000001600101000204200e00700402702700001f00b07000500202300400000c00400c00c00400100200200500f01b01001200a00200d00700101900000901c00100e00000e00301400000200000200a00000e01501f00101801400300402500a00200100000100000201000c00000500f01b00202e04b00d00a00000d00401b01400100400b00e00000000007700200100d00000a00000700100400400400100a00100000900100800000900a00100500000000100001200100400002900500a00300602e00101f00000c00400900500602100300000a00500800b00003000300000200700000100200900e0180ac00001400100000800000200501d00200700000600601005a00700800000001a00401600600100000100100a00000a01000b00900000c00400d00300301401001e00c00200700a01e001008013002006ae6498b53
  | 13 => 0x9f85426ec15280000006db17816ec7fb3a7800135cd902690000000b572563bf595415670721e1f70e683d12660cc82de65e2e11a689c00ec0f485f49674aabadc55cc8a0f703716106f244704a98e866e4ba06e80000001ef1e9cb66d223eca0a04366d61f508c8c680364ad11d8d403386e1187084c20a01520b17c4e1c00000019a42be0000569a8cc4e2fd1be1a70a0445e2d602884a87598e415a02c84e43b812fc2f00000001a4832c2fb85cc000f646b10000390ac67062d109b43660002bd901c68269e3a3992c0003c024d0c5271019a31c49800981492eb8a346be7218c98000fea00016d4000eac1083b408b87dc34514b97f00745f42be10f805c4d414643e03963ce2b81d120000b800003cc0005f71108e04e943590001a140825c50001c4c2441af1fbdb90ce008022e918072271f1b987c06a20000ac1ec4dce0ee0000000eb0000000000028a37b26701e63e22cf000000000020426f0b5c8387ee3f09f445ab0382c8000093a00017688e409a00017700000000002cf9a280003871dbda500000002f000680000002c10b202a200033517ec00020b3eb09608ed5d01d044300d454e86bce90a264623f5800058626200000007b61fb3918fc41f20000131684c662371ca917ea9e1993d807d0b400001ded6e6f063493820000bb000006986d813e38cbd48018a361481ed000077648a1b78000b7b6ab028941445628aafb07f46ee5ae00004508c21250000b7c0004178161018c50000000107c63b7b2bf0031ab6442b26e1f0000000000001d496c581000000000006b18a0b7050105a22983647430002c601f017a7e322c1c784e201804d13dc87418f3078ca00da1831c6800c4e43fe1fb8a545706d91f00498a0242a2c99ffc75d00e0d58d0c8cf40333b103c9181713091e986ab5c6a02d2dc9a412410f106403c5b1b851c7a64631830081085bc0a619e9858aeb3a604407e050622c1c013d43423e9bdf1e0074a6873ed0da44a351f3639ab823462a3689a5c7303fbbf3131c5e935c04481e8f6c67d39f0654f1241b01780005eb74b3af98c8f905fa3958000012546356000000033b35f0d580006ff06617c80000b33c580008b83f927f1dd4a0e0001be800000078800000002aa2e82ce00004ce00000004a80000000000c480003a111c075400040c00000005ac31900000000000001600fbc4b212b21b958ab9700100201000000900d00000100300000801e00000000200000000000200f00000500100300000400000a00000100201500000d00400600002400e00500000a00800f00100201200000100500000100801800102b00000600000501300000200400000000800100000100301300905600100200400000000600400000100400300900200b00100204e0000090060040060010040140030010060360010
  | 14 => 0x33e3f9800006609923299b802831293c00000007c5000000020c0002f94750da471228a993c00027e1c195b800026332091b0b10000000192400042d37dd7f808e24f19480000001673770000ff86c4b8812489692d50001d222d8376000000047c1de140cd288000000868000c610000628d5e3863cf3a880000007721ea0cd000077b1558e700000ac24580000001421d69c84aa23dd2980ec84665f00000e4a08c39a355000000073fa341fc80004ec19f84d4714631b0d0788d887b48000000fa87e91becf3ab883fa0b80000f7a000340919800000037900000000710001f10bce17f2ad800000040e1b9039cc2e2ea356800000000000008901f455a00012c44645141d0000038e4ee0a80674ccf00039d0000f9a4d113400006190002564ab87a6628a5498300000e62849a844822ec8550b8c73174225e0000504113065194885c0001860f9c3522dd19b15c4ea046b1018afc4a26918a398e00005ce29207b460a0963f68b609e64d61dfc5680046512940db2f5060439711200001f8ac8936471223f00001bc0000001c700000000003118250c32000316907860530414c07a09725f937b86ecb0a3ee8001798cf83611e280003a40003c11d94abe00000003f40001df0750388a20627a59994cdfa229000000004a48717c9394f3e266346005acd05d2173110caf25f812298080000550000a149ba6dd8008260f865113c255280002b50470ea02e67d51f917c2e020003b08ae472075c945ce08bbf50417a0db600065c05b9a08fbe0bf0001d54e303d9000089c11e3fc18fc2d09386710000d20dac58028009e421c26a081075c000000094090c2c40000ab1a82cc87962069bfa3fe32b0000000a5876305298e42ec0000001e78f227fd3f107e4e8500000012a01ca4f12acd5e07784270fe00e44ee78737180000000002750000b2e78c06d11f87f00af2a800000a4101b6f0dc6a5c2a000000000be00038193eef3a7ca3d986b4fb24890191774e605f33b68e3600037c95b95d40002872dc0a0a1a266338b89085ec45b15b148091a25d00010963947922680278cb26a039b0a58df500040000000000000f19e9c55f20a3e9000073e6340cf92d454400013800000005c12ea9968cc02ec00013c87c60000de980c5482c90c896d498c58300008d400062c14e93f600076b02980000001592411448dc041203e908c3541213d9c1d852830695841200000000001d0200000022717d46aa4b58b3060004465b386835000000011507305a874011d1854b543702558d7467810418a80000000c018c40000000102bf8000ccd0001898000dd45eb00009187944f60eb1b143ca27a26d954842834736c007c19c2200cf04dc3281443fd86e463e2c11ddc8741f84d33a31b340000000748d904f6000093927c72e0000000d8c00005b1d11
  | 15 => 0x4e00054239f86b800014d0cc0c22e0a4933c500000004be000174c6eb0970814900000000000057800058d36980000000000000ee800076680000005df7f804109b02d27cc1e1842cfe82f08a51d048ec07919604f4e4c3f5304961877000033d092c75442c2861a185000001490c0c8222230d30848f9c4753f2000000000006780001a05bb80000004ae0000f71d9813a7a33514c2cc201d91d7926425c58a1189ef092e45f01e8bc8a442fe16682a01962f322881dcf024fea8188a0e8a7ba3b51ae81e053514583f878440402b9ec6f2011f17fd6f2abc5c1b5b1c744882113db9bcca3236713e08d07cc3523f5066cbdd2e0165812475868da009d48a1049b0e202447ca7de0039094db467801a8230dc43c814f1e104e6450b124210e000110f090c83505381070e305f047307b00000003112f790c463c21f00000000461ee9d380009084f438581a0dda2a63bf8c468f250d35c0e1a552326368181418855d2511898d5e7712509d3c22e54793084e47980189cdce3a90278f2cd9d34000752ada0ee25c852b3c684448962db10091508c6743b7e431800000001500003700002440000e39746b23130c00076f3211e806427d839c1dcc16a75900012daa965e50000d340001dd3478bded2a3751128a404de5d1000041c5946202a285a01fd6a62da58c44380170000f485d54d520813340b82c730d971c01847b00000006e700019c95900006bd29280007ae2893f414cc00000027304aa0004240000d9ee1238b3915bd4f3872a02006380006c321c110096468e9ca158800000031106fcb9a3930b00fa44345a727081c87d60273f6133c3c835e00013a4cce00000011c4a425ee18b13bc2685ad2048e1e10c79804e1f04aaa71b255c000c7c65d1bc1558d9448e1298b1000062911305c873533a13a046c1265d40000bec2ca6df09f80000003ff33085b80000310001b627730002aa000060925a8989c82b0e0d6af60000e5e0163e74ac00006b50000e7492c20033280002522520da879e4044a039e8234000044800000000000000007040003ba80018387821181c042225ce4343d590f43141c621013e0d9816332c1d38ffc3508000000c781ac38d1b548e02af000172c68814f0000cb8e2a56b35f8a6822a3b91c789b801e3a8a8502f870c00000000002ee3531ffde4c2464df21309d8b7a12023384b007c56c3241d240000003d51d1ed6e2da14e0010bb27cf2209ae48c37d334e800010e0a30ff0cc00000439e0da86636536000143c0000000000000c9c79a00016c0df80cd3bc4000a820001d6c6f83bd6070881310d6d4223ca093468056f1ad14c4fee7433331b982d67763af0a4405a40811a4efc8c55e92640d30c9a08139a894000a59a098016028007f3a9848eb247b525e8c8840726520d1d88b484170000e0634e
  | 16 => 0x41fa28d12b80ce786085145c9633f31598000c002cc0e807a8dd05df0319724c8e2810f3876c00000001d58ac45e2bd1878ac4d323422739ce49c63fb1ee1114c3a0c70000ea40001430001460fe35530690c906c47281de8c9eef200039cce5800000000006307ac2082279df46d40ff2028ec086c3173da16944205b28e758d45d64212e614186a8782b64963cd80623ad419304446d731b8b3823a5659169510aec205341811431258903a1f24c223a58b69f7422c4781f11a1000038535416fc57635690d9a7cae625c3e31cb00420bc00002b898a00017085487bf3580271c64f0760b27d0ac87d828f1b24530e3b3b43f3990031a13e3f891fc2f856d2478ef86a344c17d035805231c107830888c0a128715e85de18b17e0e9a8b24eb2b296e8a8e37fb5a11f4dd665414f8248e5915d1611ba47e90000000122e9856729485705746de8d800008a052a2cc8584ac33c40e101288da7d735e05d0f5e6790bf1e6c00031cb5ac356bb453e2a5c00024b1463e39300b4c54e2010028acc00b053968c3b459424a040cb2a4a735d8000bfa1821849c44f961381c7c7dc76a7b90a088de93006c0a98990cc42d331b0dfc0000002d79d9ca9850b2e00c9c6fd6303cb8174df45a92d59d62cc9081bbb8e64ea805623a10a4cbe4a532b0fa88dc4e82cf182830a52f3218470c2821838e08c037405911cc0000f05ea15e1e548760f50758a18b662d796f5c50f1c0370001f3eb940620001da40005b10c393606620b20ee0ba400049e00000007e06f800014c80007c200000000004150cb94dccae00012d150067077a00015a80240002ae061000020916a4000e836a90000f785e20000d28c8ee625efaf1000000000027f94ec0000002b9085cbbc08b23e0000eb80003dd81d200039234852f62f65cf29a19d00000000001ca200000000000000004a600018bc0000003fa55345c91330e712b0d100ba26d0c289da0d538d4c20e881148f1c2a409e7f00328db47c27291ba5474cde4c11d889b6b3a44a1881bc46406250c80c081483e812d84f054649014c86d06fc13b3368b5aac0745972804cab066c29e00f060327d3df8280bac2a70e89b7403266f9cd87d8ebb7f0b39116816244d30314e476e06133f89244bc4fc0b5170cbda0e036dc9fcd1c36506d8f245ea01d1ba0eac41a0e116896580006c603800b6c3c0001fe80001da0443fd0e7855017900000007965f88001ee00000000001e84c100d833591a4d2000027c80002491c500000001ae34f3d680000355dc3b01b1678c25f1ac5d200002d90efdbbc16c3ae00000006e25233121db00005770f981f2b531ec09798845103c70d904c8e7d3d0000000000049539215d09c423d1d187c2000000265800039300021a800000000008780008887ef010115c00008a00006f01b824c06f
  | 17 => 0x37a053839e3600f301ccde06fe3d116dcef837bb0f8b48e786440891b9406c0001ea90bc0006a4000000072143934d8c1cfe55592969e64e7600027e9e908f468d00008d82020b907a07be8ee306359904c3e731d1b60858f152ff3e840003a634618086203920f13b954fc3b01a21db0b409543001868a6c302548174cda00003f638b13ec5684c920e94583994862c59c20ea707b0d180fc66a2552df16fe8ac75a3999b3c2f44910c303ec00028e0d0149c5142150000ab400078536e0f7c3481e02a856e41926f620c16d89682dca32040029657d2de03a06dc4300c911bc723000239000000000031f800009600000000009600002f18116e4a00034480008a424821f9eb86f52932141cc8bc84a424298f40003661ab8bdc17609025c0214d820003d29c9c69c53d3459b50d264ca02a152400002434000a00ab0343ad56600fc7ac1d98e7e39a35b334410c8160e3000081875951e2e400706543251250c5e8846cb0640e10d647370791f947e52e09969dd001006438112bc48e1b70618ab000057e0d89d6cd447780ba9f400c02c512dc0acec851c08f1ac0e7146a00009d4bc2207028000000000035a59ccb8106930682c08aa3f425d987094612d0608178b8c0df3879860fec1c039680002120001a59a9c81400000000005544f88f59928e400662ed8000bfe1f20001d74ff200d0000ccc2b62ada61026cd8d76e0aa14989006ce0181d5cd4a6130001940e4467512700004b95f3a198000e1853a00000001de37a1630000bd95690001f6c0000000000000bd075494607824d60000001a602cd1363195df827420c1f21a58b1c6772d540ec9e056124198ec7b02be2a19be465e6fb3610f3410667b3170000aae4491420fb400021911e00005c
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa96848c9610c0010bf0eb2c621800307596748c4300044fc3ac91886000c1e75592310c00189acb394621800323592728c430006273aac51886000c8e7458a310c0018aceab0c6218003259d1618c43000663392c3188600085c87595300c00183aca3a260180022721d644c0300060e3aac89806000c4d651c9300c00191ac83926018003131d5624c030006463a2c49806000c55651c5300c00192ac838a601800331588714c0300062a3aac29806000c9474585300c001988e4b0a60180021da1c65547100045b438c8a0e20008d68718d31c40011cd0e31243880030d19574945100045ac38c928a2000c54655ce5144001928c8b9ca2880023561c63945100064aba0c728a2000c64655ca5144001948c8b94a2880033118d729451000652ba0c528a2000cc57318a51440010eb0e32c82880030d5d464905100062a32ae720a2000c94645ce41440011ab0e31c8288003155d463905100063232ae520a2000ca4645ca4144001988c6b948288003195d4629051000662b98c520a2000875871963144001868caba462880022d61c648c5100061aba8c918a2000c557518e314400192ae831c628800319195728c51000652322e518a2000cc4635ca31440018caea3146288003295d0628c5100043ac38cb10a2000c34655d2214400116b0e32442880030d5d464885100062a32ae710a2000c94645ce21440011ab0e31c4288003155d463885100064aba0c710a2000c657518a214400194ae83144288003315cc62885100061ab2ce9a8820008b78759351040018aacb39ea2080032559273d44100046bc3ac7a882000c967458f51040018cacb396a2080032959272d441000662b1ce5a8820008e78758b510400194ce8b16a208003319cd62d44100043bc3acba082000c367559341040018aacb39e82080032559273d04100046bc3ac7a082000c567558f41040018cacb39682080032959272d041000662b1ce5a0820008e78758b41040018cceab168208003319cd62d04100043bc3acb9882000c35659d3310400116f0eb2662080030d9d564cc4100062b3aac79882000c967458f31040018cacb39662080032959272cc41000662b1ce598820008e78758b31040018cceab166208003299d162cc4100043bc3acb9082000c35659d3210400116f0eb2642080030d9d564c84100062ab2ce79082000c95649cf21040011af0eb1e4208003159d563c84100064b3a2c79082000c667558b210400194ce8b164208003319cd62c84100043a43aca8802000c35651d110040011690eb2220080030d1d564440100062ab28e68802000c95641cd10040011a90eb1a2008003151d563440100064a3a2c68802000c65651c9100400194ac839220080033158c72440100047243ac48802000c64755891004001948e8b122008003311cd6244010
  | 1 => 0xf0c994621080235a1c634c42100663bb464988420096585dd9210840138b07bb2421080299a1776484210056341eec90842009c583dd521084011cd0f32a421080319dd665484210056341cca90842008e68719521084018caea32a4210802596177348421004d2c26e690842008e68798d21084014cd0b31a4210802a9a12634842100663b9cc690842008e68718d210840198ae631a4210802596147048421004e2c18e09084200c64754856008401988e690ac010802b820121580210060eba0c7a9aa000c2c645cb5354001898c6b96a6a80030d19171d4d500062a31ae3a9aa000a5583d5061540014cb05aa0c2a80028d613531855000532c16a630aa000c1c645cf515400183ae831ea2a80030b19172d45500062631ae5a8aa000c2d7418b515400189ae6316a2a80030d5d061d45500062ab98c3a8aa000c6572187515400183ce8b1ca6280030b5927294c5000626b1ce5298a000c35649c653140018aac738ca62800295a0e545845000533414a8b08a000a368494d61140014cd0529ac2280030759273944500060f3a2c7288a000c2d649ca511400189ac7394a2280030b9d162944500062739ac5288a000c367458651140018ace6b0ca228003199c961944500060e3a2c6a80a000c35641c550140018aac638aa0280030d1d161540500062a39ac2a80a000c647258550140010bd0e32aa79800227a1c6450f300060e32ae929a6000c4c655ca534c001918c8b94a698003151957194d300064a322e329a600085d87196434c00183aea3248698003131957290d3000646322e521a6000c54655c6434c001928c8b8c8698002a3612531893000562c0ca63126000a4d8590c624c00158b03218c4980021761c65cc9300060e32ae99926000c1d75193324c00189aea3166498003235d062cc9300062a32ae39926000c94645c7324c001988c4b8e6498002a5612531853000562c14a630a6000a558590c614c00158b05218c2980029561732185300054ac266430a600085d87197314c001838caba66298003075d464cc5300062632ae598a6000c8c645cb314c00189aea3166298003235d062cc5300062aba8c398a6000c9574187314c00198ae430e62980030759674d4c300044fc3ac9a986000c4d659cb530c00191ac9396a6180031559671d4c300064ab24e3a98600085f87597430c00183ceab2686180031359672d0c3000646b24e5a186000c55659c7430c00192ac938e8618002a3a1353588300056340ea6b106000a4e85d0d620c00158d03a1ac41800217e1d658c8300060eb2ce9190600089f87592320c00183ceab246418003139d5628c830006473a2c51906000c55659c6320c00192ac938c64180033158a718c8300054b426a6b086000ac682d4d610c0014ad0ba1ac218002b1a0b43584300052b42c64b086000
  | 2 => 0x272d063100473c3ac5a0c6200c667558b418c40198ce6b16831880265e1d43106310042ec3ccb98c6200c1e655d3318c40113b0f3266318803075d664cc6310062732ae598c6200c8e645cb318c40189aeb3166318803235d262cc6310043bc3acb98c6200c35659d3318c40116f0eb2663188030d9d564cc63100632b2ce598c6200ca5649cb318c4018cceab166318803299d162cc6310052b430a7a8a6200c5676d4c514c40152d0c21e8298803259db43105310042f438caa98620089e87191430c4014af0ca9ca2188021da1c65544310062bbb4a6a886200a978650e410c40116d0e322821880325dda4350431004aac2eec988620099584dd9310c40138b05bb2621880295a17764c4310054b426ec9886200ac682dd9310c40132b09baa62188027160b754c4310046b43cca9886200c5775995310c40152d0932a6218802b1a0a654c4310046b438ca9886200c5575195310c4012ab0bba262188027160b744c4310046b43cc89886200a5685991310c40192ee93226218802b1a0a644c4310046b438c89886200c9574191310c4012ab0bb92621880265613724c4310052b42cc49886200a9684989310c40198ee5312621880255614704c431004cac20e098862009c5821c1310c4018a8ea98ac018803251d131580310066239262b006200ad0804c5600c40185ccaba4a5108022b61e6494a210062732ae72944200c8e645ce528840119b0f31ca510803235d26394a210063332ae32944200ca6645c6528840198cc6b8ca5108021b61e6590a2100616bacc92144200c4e655ce428840191cc8b9c85108023361e6390a2100626bacc72144200c66655c6428840194cc8b8c85108033198d7190a2100436c3ccb1944200c2e655d2328840115b0f32465108030b5d6648ca2100626bacc71944200c8d7498e32884018cccab8c651080329991718ca210066331ae31944200c35659d3518840116f0eb26a3108031559673d46210064ab24e7a8c42008d78758f518840192ce8b1ea3108031959672d462100652b24e5a8c4200cc5639cb51884012cf0ea90a3108021de1d65d06210061b3aac9a0c4200c55659cf418840192ac939e831080235e1d63d06210062b3aac7a0c4200c65659cb418840194ac939683108033158e72d0621004d3c3a8420c420087787597318840186acb3a663108022de1d64cc6210061b3aac998c4200c567558f318840192ce8b1e63108031959672cc62100652b24e598c4200cc5639cb318840138f0e99063108021de1d65c86210061ab2ce990c42008b787593218840186ceab2643108031559673c86210064ab24e790c42008d78758f21884018aceab1e4310803259d163c8621006333b6a428a4200ac6860cb314840198ced99062908021da1c655442100633bb4a4a8842008b687191410840158
  | 3 => 0x5a8c820093787550519040107b0f32e83208030799573d06410060ebacc7a0c8200c2e655cb419040191cc6b9683208030b5d662d064100646b9cc5a0c82008778759741904018aacb39e8320803159d563d064100632b2ce5a0c8200cc5639cb41904018cceab168320803319cd62d06410041fc3aca2a28200a3686153515040186cedaa0a2a08020fa1c65550410051bc32a9288820087687195511040186eed2a2a2208024d6177650441004cac1eeca0882009a582dd9411040146d0bbb28220802a5a0f765044100553416eca08820099583dd5411040134b05baa82208022da1e65504410061bbaccaa088200a9683995411040154d0532a82208022da1c65504410061aba8caa08820093585dcd411040134b05b9a82208028da1663504410064bb9cc6a088200aa68298d411040126b0bb9282208026560f72504410051b42cc4a088200a9683989411040194ee531282208024d6147050441004cac18e0a0882009a5821c14110401868eaa0ac020803251cd41580410065239282b008200ab080505601040183acb3a6a79880227e1d64d4f3100626b2ce5a9e6200c8d649cb53cc4018aacb38ea7988032559271d4f310042fc3acba1e6200c1e7559343cc40189acb39687988032359272d0f310062ab2ce3a1e6200c95649c743cc40151d09a9ac598802b1a075358b310052742e86b166200ac681d0d62cc4010bf0eb2c659880307596748cb310044fc3ac91966200c1e7559232cc40189ceab146598803239d1628cb310062ab2ce31966200c95649c632cc40198ac538c65988030d99574947310045ac3cc928e6200c56655ce51cc40192cc8b9ca39880319995729473100653322e528e62008e58798a51cc40194ae9314a398803315ce6294731004ab438a6a8e62008758799641cc40186aeb32483988031599573907310064b322e720e6200c66655ca41cc40194cc8b9483988023961e629073100632bacc520e6200cc57398a41cc40132d0e21a8398803079957494e310044ec3cc929c6200c4e655ca538c40191cc8b94a718803159957194e310064b322e329c620085d87996438c40183aeb3248718803139957290e3100647322e521c6200c56655c6438c40192cc8b8c8718802a36125398a3100562c0ca73146200a4d8590e628c40158b0321cc5188021761e65cca310060f32ae9994620089d87993328c40183aeb3266518803135d662cca3100646ba4c59946200c56655c7328c40192cc8b8e65188033198971cca310061ab2ce9a8c62008b787593518c4018aacb39ea3188032559273d463100632b2ce5a8c6200ca5649cb518c4011cf0eb16a318803299d162d46310066339ac5a8c62009578754c518c4010ef0eb2e83188030d9d564d06310062ab2ce7a0c6200c95649cf418c4018cacb39683188032959
  | 4 => 0x310c0152d03bb28621802656077550c430044f43ccaa188600c1f759954310c0152d0332a862180227a1c6550c430060eba8caa18860091d85dc54310c0131b05b8a8621802476147050c43004cac08e0a188600c1e7550e6110c0152f02a1cc2218032350e72984430060e3aa86b008600a988050d6010c0192a8638ac02180307592739535100616b24e52a6a200c35649c654d440149d052a2c7a880295a065458f510060f3a2c729ea200c2d649ca53d440189ac7394a7a88030d5927194f510062ab1ce329ea200a4e8395162d44014cd032a2c5a88028ba125358b510053340ca6b16a200c1e645cf549440185cc8b96a9288030d99171d525100526c16a931ca200a5581d52639440183ae931ea7288030b99172d4e510062731ae5a9ca200c36645c753944018acc6b8ea7288029360f5498a5100532c0ea9314a200a2d84d4e62944014cb03a9cc5288030799173d4a510060eba4c7a94a200c2d7498b529440189ae7316a5288030d99171d4a510062b31ae3a94a200c66625c7529440183cc8b9ea328803075d263d465100617322e5a8ca200c4e635cb519440185ae9316a328803135ce62d46510064ab24e7a8ca200c967458f519440194ac9396a3288033158e72d4651006533a2c5a8ca200cc67358b519440126b09bb2a2288025560f7654451004b2c16eca88a200a3684dd951144014ad07bb2a22880299a0b7654451004aac1ee8a88a20096582dd1511440186ee9322a22880295a0e645445100533414c8a88a20093584dcd51144012cb05b9aa2288028da1263544510062bb9cc6a88a200a668298d511440126b09b92a2288025560f72544510051b424c4a88a200a568398951144018cee5312a2288024d6107054451004aac18e0a88a200965821c15114401868e8a8ac028803151cd515805100632392a2b00a200a7080545601440183acb39ea9a08030b59672d53410061ab2ce3aa68200a8e82d5163d040152d03aa2c7a08020fe1d6590f410060f3aac721e8200c2d659ca43d040191ac739487a08030d5967190f410064ab1ce321e8200a8e83d5162d040154d03aa2c5a08028ba164358b410055340c86b168200c36655d251d04018accab9ca3a08023561e63947410064aba4c728e8200c66655ca51d040198cc6b94a3a0803295d2629474100662b9cc528e82009368715151d040183ccab9ca9208030b99572952410061b32ae32a48200a8d82952639040152b032a4c7208020f61e65d0e410060ebacc7a1c8200c2e655cb439040191cc6b9687208030d99571d0e410064b31ae3a1c8200a8d83952629040154b032a4c5208028b6174398a4100552c0e873148200c35659d351904018aacb39ea32080235e1d63d46410064b3a2c7a8c8200c65659cb519040198ac7396a320803299d162d46410066339ac
  | 5 => 0x4be000000001749393a000524001e514e214002492400004d9d68002c5769534406397094f0584d08e1f54ce3b8028000c24fd1da85364a8000066000392001a14320016893330285c00248006000010010070060080380500c0040100a0000080000900000c06000000020010000140280b80301000801803000000040000000000180100600401802012004040020000000600501e0140000100400c00004006004000060000580000f0020000380000200c0000600c00400001000008060050040140080400a000010040140000500a00c00000000000014000150040200080900002007000002034058000000200701701a0240180500a01400803000010018010000000380100e0000a8160000080080500600002000004000000000000040000300200403000000000008020020040682600a0000101200e0240581a01000c028000000000600300802c0980000e0000000701c01c0880000002800800030018040080240340200100001c010110020000000000201c00002000004000080000080100001c0280000000c0000100102003c02004028028000050280180300000000c00005000028008000020000000a006004018000120000f0010020140000700007c04800002000048020000040183cc8b9ea9298030b99172d52530061b322e3aa4a600c2e645cb5394c0186cc8b8ea7298032359272d4e530064ab24e3a9ca600a4d83d526294c014cb03aa4c5298028b6135398a5300532c0ea7314a600a8e84d4d6294c0158d03a9ac5298029560f549865300532c16a930ca600a3584d4e6194c014cb05a9cc329802a5a13535865300563416a6b0ca60091d84dd95314c0129b05bb2a629802556077654c530050f426eca98a600a4e82dd95314c014ad03bb2a6298025360b7454c53004aac0ee8a98a600c1f749915314c0149d05322a62980295a066454c530048ec26e4a98a60095581dc95314c0123b09b8aa6298025360b7154c530048ec20e0a98a60094d821c15314c012ab02382a629803079d1539885300527c12a7310a600c55539c66214c0183ce8a9cc22980295e05539845300626a9ce5308a600c1c7454d6014c014b100a9ac0298031354c72580530062aa98e2b00a600c1e655ce5490c0185ccab94a9218030d99571952430060eb2ce9a9c8600c4d659cb5390c018aacb38ea72180247e1d5414e430042fc3acba1c8600a8d839526290c0154b032a4c5218028b6174398a4300547426a6b148600ac681d4d6290c0149d0ba1ac521802b1a074358a430054ac1ca930c8600aa5829526190c0146b0ba1cc321802a5a13535864300563416a6b0c8600a5685d0d6190c0158d05a1ac3218020f61f54d95430060f3b6a829a860085e871955310c0183eed2a2a621802476177650c43004cac0eeca188600a1e85dd94
  | 6 => 0x1010000ee2dd7a2a60189dc00070000001482df0c01795c884000a040012b00077c0018a5ca000000004ecaa1120461340006283800000000000000001222374a233967a1d0000000000013c8303180004e0000019011e1af1088115c20800000000af8841ab47aa951a08b1589a8fe8980640e526800474450001c80a00006511f4a0195638000001d08493e1c8000de92145343c6941a4c68940022a3ce0000028f01a3890081f074000e00e300066c000004101f800000000000000000c35ed56078000001609f422ca45658000000000024528e76ccb01b9aeb136d1f3231520f82c9012000db8001a900037c0056f678000c60b250800189232264940c9480b807f0a937606c491132f81c9401650009b4b98f01bebb93000a20a64d21a055a4b75328072b6501722b3181bccf211bc3e9886c06211a7717e915ba42bd5b15c43c3d96a0c74227052a27f5570002c05700025436a2810c70870800260000a0c0b0a4000f60803ac8582004558a000000000004951166b2ce1205b11eb3e7980000017c00080eaa000001080002946500000037e0005c00009c6a6251592d686c07abb8000014100050c1252120f323000d2ab5000a20aa936000001448001204ec5315616a4b04b2000e6378da8cf0aa074af0000000705c80020eadc7e0005fc000c88004fc00150a9f47e9c11c2f70003fe1b5aa15a341644e821a4dc000c80002cc5a15f0000013600057b000000332fe6180000000025c001b8142000bb8000006917800034c960ec9da000899520003985e05f9d13ba0408f1d022e73c092b5d888b08ce2200042e00000000ad2b51c404a74cbb129056544b6aa32b0aa49524e000531158041b87c4102baae40ed070d20009f03a8002354faa68000000000028a2f23d40000028800000000078000001030005a0a1ac20f63f4821d753a3fd5fa2335e63c990ca8420fb0a03f272832b60430000662d0423b01b0d4a5a000000000004e4be0cd183000000498002d27888e80007a9f4d68cb055000001642a03a54f0e60a21e93ca5b0000004e9a800082d27aab3607b443c0000000068a1c2ea36d4d00dc300007ac000001f000000000000c41a753007a876de0000014b195000158bf24a528a9c0000055e000071f800014d19a6f0000c0978004c81bce180046a58c001e00000017180022408c012ca000440000002de088000002f478c000a40006d95686b1ba000279155ce00167033800000d180006240a000000000000000011cbf00029b0004049a6f13dc0000000000039d7a800282614000cc0d40440011a0004080019d0008284880025ab5800274524000000000520bc002f25b817c769c911495d25a270289e04c4c1259000500675b011c698a28003da002bb154818002d73f48b80000045a8c0000000000000029c00
  | 7 => 0x52ab88000d6000998001db86c12efb80000071c9743e5cc6b00002d000001290005747a852a410000189721509a00000000000400000000009c4000f7000000ad049800000b7d4b1afa88000e51847a000000000550c20004ac1c552e4618800129800000ac0002c8000000c3800000000b8273000001018001adba80019c000300001350005195e80000046d4b8000002e82e25d01000149800000738000001e600001982602000001cd1d600000000372000002ff00068853d381600dcab813000b54002b8000b340001e5689a57d8f40004305e0bd3aa0540c9b11fb000121de000492000f921400000000150588002e81a8000000000004f00002e000b403227b0004e200000371b65778ec04c6610900058c00088cfb4bc7ed66000000000c92f6144a64000001b41500025f00048c0b0ab05493114a8c000bb0000000008e4e328b583000000000f28345d9ff1e2060c6230aa46e89166822d634002fa118000c015d000be5098004b241a001310000011b1f629c000000350826b82a417000000000000fe0007c1bc3167bd1e1605869d5238341aa9b9421a03e4ac4ba09c000514000000005f43e8e380020c9104c1463640025c3d625b470892e22511f2c0000584000003a80000027a000419759fe563c00df025d783a9178cd39472ce94870968c8b72ae21f4988c12433244400000368220d9a55002824000000001109ead30000016da040000011880000086800000000001590001de7a565c000ec4394185b5d2a1c0010b000714590fa0d0000001661e47853080032e0a00006e1860010389f1c07e434a8d0007f000000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x6a01409800201000407e61751954310c01037985d4655044100415e6175195310c401097985d0644c43100419e617519521084010c7985cc6348421
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 34
  | 6 => 840
  | 5 => 2049
  | 4 => 770
  | 3 => 6
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
  | 7 => packedAt gbK7 (1024+((h/20+packedAt gbK7 (884+(h % 20)*7) 7) % 88)*7) 7
  | 6 => packedAt gbK6 (34919+((h/349+packedAt gbK6 (31080+(h % 349)*11) 11) % 2024)*11) 11
  | 5 => packedAt gbK5 (107748+((h/783+packedAt gbK5 (98352+(h % 783)*12) 12) % 2819)*13) 13
  | 4 => packedAt gbK4 (48543+((h/283+packedAt gbK4 (45430+(h % 283)*11) 11) % 1232)*11) 11
  | 3 => packedAt gbK3 (428+((h/2+packedAt gbK3 (420+(h % 2)*4) 4) % 12)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffff07ffffffff
  | 1 => 0xf03e07e0f07c0f81f83e07e0fc1ffaaaa55293
  | 2 => 0x3ff800ff800ffe003ff800ffe0fcccc6631c
  | 3 => 0xffc00000fffff000003fffff0000ff0f0783e0
  | 4 => 0xffffffffffc000000000fff007fc00
  | 5 => 0xffffffff00000000000000000000fffff80000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x400820000010020800082004000000080425
  | 1 => 0xb2364742746c8d91d0b64742e85e7aaaa55292
  | 2 => 0x843bd104bda10ef4413bd104f3c2bcccc66318
  | 3 => 0xde908208def7a420823de79e2084df0f0783c0
  | 4 => 0x8210410ef7bcf79e79082084108eff007f800
  | 5 => 0xef3de79e08420841042104108210f7fff00000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xeaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15285
namespace PEqualNP.Outside.L_meta_15285
open PEqualNP.Outside.L_meta_15285.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
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
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
theorem alls3 : ∀ k ≤ 3, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1 := bs4_3_0
theorem alls4 : ∀ k ≤ 3, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 1 := bs5_3_0
theorem alls5 : ∀ k ≤ 3, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 6 := bgb_3_0
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
theorem bgb_4_768 : Interval gbAtlas 4 768 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 770 := (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160))) (concat (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)) (concat bgb_4_288 (concat bgb_4_320 bgb_4_352)))) (concat (concat (concat bgb_4_384 (concat bgb_4_416 bgb_4_448)) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544))) (concat (concat bgb_4_576 (concat bgb_4_608 bgb_4_640)) (concat (concat bgb_4_672 bgb_4_704) (concat bgb_4_736 bgb_4_768)))))
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
theorem bgb_5_2048 : Interval gbAtlas 5 2048 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2049 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 bgb_5_992))))) (concat (concat (concat (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120)) (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248))) (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504)))) (concat (concat (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632)) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760))) (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)))))))
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
theorem bgb_6_832 : Interval gbAtlas 6 832 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 840 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608))) (concat (concat bgb_6_640 (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 34 := (concat bgb_7_0 bgb_7_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 60, 62),(inputs.getD 2 zero, 58, 62),(inputs.getD 3 zero, 54, 62),(inputs.getD 4 zero, 46, 62),(inputs.getD 5 zero, 30, 62)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 4 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8eaaaaaaaaaaaaaa8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3937053354 * 2 ^ 32 + 2863311528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15285.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.and,[4,6]⟩,⟨.and,[5,7]⟩,⟨.and,[1,8]⟩,⟨.or,[2,5]⟩,⟨.or,[3,10]⟩,⟨.or,[1,11]⟩,⟨.or,[4,12]⟩,⟨.or,[0,9]⟩,⟨.and,[13,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937053354 * 2 ^ 32 + 2863311528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937053354 * 2 ^ 32 + 2863311528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15285

open PEqualNP.Outside.L_meta_15285 in
theorem PEqualNP.Outside.L_meta_15285 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937053354 * 2 ^ 32 + 2863311528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937053354 * 2 ^ 32 + 2863311528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
