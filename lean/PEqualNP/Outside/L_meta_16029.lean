import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_16029.Model
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


end PEqualNP.Outside.L_meta_16029.Model

namespace PEqualNP.Outside.L_meta_16029
open PEqualNP.Outside.L_meta_16029.Model
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

def SBf (j : Nat) : Nat := [5, 7, 5, 5, 5, 7].getD j 0

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

end PEqualNP.Outside.L_meta_16029

namespace PEqualNP.Outside.L_meta_16029
open PEqualNP.Outside.L_meta_16029.Model
def s0K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40628a042f195c32bc6370c6f985d30
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xd1000096418ca390a318c424c2510530
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*4) 4
  | 3 => packedAt s0K3 (i*15) 15
  | 2 => packedAt s0K2 (i*26) 26
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (5+((h/1+packedAt s0K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s0K3 (96+((h/2+packedAt s0K3 (90+(h % 2)*3) 3) % 8)*4) 4
  | 2 => packedAt s0K2 (107+((h/1+packedAt s0K2 (104+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 2 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 3 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa0180202049440a5
  | 2 => 0x122324452122a652
  | 3 => 0x9416819484a2b18
  | 4 => 0x78a4eae920ccde0
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 30 s0Pos s0Neg, 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_16029
namespace PEqualNP.Outside.L_meta_16029
open PEqualNP.Outside.L_meta_16029.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1a2441000006539b5e0000e28ac5a52c2088c120110a464cf000e60003081802c1e990a4500400038a80173e354955a742825c0004840c0000381007003242ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x158284b06c44000395930005713058ab01a10da8849238163d4a0c08e900d2454c26449c4d05f001b8327d0699940b21e27cc4103aa04004e0892cbc82029d092544e9f824ad4e1081c00520b88a02542692e8c0fa6cf804348a81e8500800d836241400000190006820179dc0000220012667458009e3f2d2885a00000cd5eb600000de0000000006a32060ae0c15a9d420046adcba27302d0481e21ac56670001e862b8400a4767652a192a000e21c006310964000000001145c20918460000024d63e288d472065192906aa05264e637001953c083d855605526894c2000a04c3a402c05cfe720b0e96a790016ca6b93c00000001c148008f54828004c000000342c0c100c0c340494080800005c9c040404041404141864002c042c00381454140c008c00041000240400045000142c0cbc142000080c12dca5a1db54b43bb28e877551d0f5ca5a1cf54b43d6a96872d52d0f6ca3a1cf54743daa8e873551d0e7ca1a1cf55243cfa9a873f5250e7ea2a1cf141439f2a0875e53d0abaa7a15d94742baa8e859e53d0a7aa7a16754f428ea9e85b651d0a7aa3a16d547429aa8e853e50d0a7aa9214fd4d42d7a92853f5150a78a0a14f950429f2a6653d54ccb5a85995d94732baa8e653e548ca7aa9196750e32bb28c6575518ca7ca8994f551329f2a0653d540cb3a86196b50832e6990655e53d06baa7a0db94b41b6a96839e53d067aa7a0e754f418ea9e83ae52d067aa5a0eb54b4196a96833e50d067aa920cfd4d419fa9283b75150678a0a0cf950419f2a6633d54cc6dca598db54b31daa0e633e548c67aa918e750e31b7294636d528c67ca898cf551319f2a0633d540c73a8618ed50431ea988633e54c867aa990d794f21aea9e43b541c867ca910cf55221af29c435d538875a8510cf951219eaa2433e540867aa810eb50821daa0843e5210867aa7204f54a409ea8c813e50902bca6205754c40b7290816d52102eca2205d54440cf298813d531033aa6204754c40d7290813d521035aa4204b54840db288813d511036aa2204d544409f28081ba501027ca9984f55330cea1e613f548c278a9184fd51309e2a2619d434c2dea4985b14930bba8a6174514c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c835a85904fd52209e2a4413f5448278a89057d4d20ae29a41ad42482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9884f55310daa0e213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b629221b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2c1e846e007a943c222800901a4400006a58000464186c0078404c003e000000689850a0009a8e66060000002e4a006034a2760c12560082005e6210a4887c144808705a9c7e924602420000000a9e72745c5452368c4e1c0000302600160e243aa632800000008a862a38962000001c00201000ca160c140800818a820e0150600002820008080c954a51d0f265254743c954951d0e8e62d4d43a59875350e3561d49438b58b5150e2d62141438d5845050f155394742c594d51d0b1553547428d5875350a8e63d4942a99875250a1d63d45428758c5050a356114142c950a51ccb1543946328758e544ca2d62951328d586544ca356195032a3591320cb0d5394b41c394d52d070d5354b418b58b535061d63d4941a598f51506a662d45418758c505062d6214141c994941cc70d4394a318758e544c62d62951318d586544c62d6295031a5591310c7165350721c394d428861d63951218b58a544863561951218758e54086a564484218bd8953902376154e4087d8d52902376154a4087d8d519022f6254640c354e521030e5354840c354d52103155394440c954a51103165354440c554d51103265254440c9549511022d62953308d58654cc22d62152308d584548c21c6550d30c350c524c31543145308758e54c823561953208758c548823561152208b195424830c5350920c9508514821d63953108b58a54c421d63152108b58854842346550510c514d41443245250510
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 186
  | 3 => 84
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
  | 4 => packedAt s1K4 (5518+((h/62+packedAt s1K4 (5022+(h % 62)*8) 8) % 224)*9) 9
  | 3 => packedAt s1K3 (3388+((h/28+packedAt s1K3 (3192+(h % 28)*7) 7) % 111)*8) 8
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff87fffffffc0fffffffe07fffff8ff1ff
  | 2 => 0xc1f03ff83e0f83fff1c1c1f0ff878787f54e93
  | 3 => 0xfe003fffc00ffc1ffe01fe00fff807f8798f1c
  | 4 => 0x3ffffff0001ffffe0000fffff8007e0fe0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x40000080000000000002021000088080001025
  | 2 => 0x946659119495270cb0d0d1a26c851517354692
  | 3 => 0xcaaaa228d2a613556217484b5502671598b18
  | 4 => 0x294d344529834a5a6b742108da6670226e0dc0
  | 5 => 0x318e387631cc739f8db9b9ce1c4444447fe000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaaaaaa0faaaaaaafaaaaaa0faaaaaaafaaaaaa0faaaaaaafaaaaaa0faaaaaaafaaaaaa0faaaaaaafaaaaaa0faaaaaaafaaaaaa0faaaaaaafaaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_16029
namespace PEqualNP.Outside.L_meta_16029
open PEqualNP.Outside.L_meta_16029.Model
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
  | 1 => 0x83c1ffc1e0ffc3f8f07f8783fc3c1ff0d6cd9c
  | 3 => 0xfc01fffe00ffffff007ff803ffc01fffe70e1f
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x80008840000400010900888804444220050b1
  | 1 => 0x2892918c8952052874348519a428c96252c594
  | 3 => 0x1125221052a42253084950224a81128ca50a0a
  | 4 => 0x52b9c4295836ab9dad0c4443733380c4f80f40
  | 5 => 0x633187319cc733e6ce6e667062220308ffa000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaeeaaee00eeaaeeaaeeaaee00eeaaeeaaeeaaee00eeaaeeaaeeaaee00eeaaeeaaeeaaee00eeaaeeaaeeaaee00eeaaeeaaeeaaee00eeaaeeaaeeaaee00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_16029
namespace PEqualNP.Outside.L_meta_16029
open PEqualNP.Outside.L_meta_16029.Model
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
  | 1 => 0x83c1ffc1e0ffc3f8f07f8783fc3c1ff0d6cd9c
  | 2 => 0xfc01fffe00ffffff007ff803ffc01fffe70e1f
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x80008840000400010900888804444220050b1
  | 1 => 0x2892918c8952052874348519a428c96252c594
  | 2 => 0x1125221052a42253084950224a81128ca50a0a
  | 4 => 0x52b9c4295836ab9dad0c4443733380c4f80f40
  | 5 => 0x633187319cc733e6ce6e667062220308ffa000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeaeaeae0e0eaeaeaeaeaeae0e0eaeaeaeaeaeae0e0eaeaeaeaeaeae0e0eaeaeaeaeaeae0e0eaeaeaeaeaeae0e0eaeaeaeaeaeae0e0eaeaeaeaeaeae0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_16029
namespace PEqualNP.Outside.L_meta_16029
open PEqualNP.Outside.L_meta_16029.Model
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
  | 0 => 0xc3fffe0ff0ff0f87e1fc3fff0fe0fe0f49f673
  | 1 => 0xfc1c3ff0ff0ff0f8fe1fc383f0ff0ff0b6cb9c
  | 2 => 0xffe03fff000fffff001ffc03ff000fffc70c1f
  | 3 => 0x3ffffff000ffffe00003fffff000f80fe0
  | 5 => 0xffffc000000000fffffffffc00000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x48400222010010002024048901222222005231
  | 1 => 0x8940446240140110620c4119104a24a212c294
  | 2 => 0x108aa8842aaa88ab1112a822aa04494cc50c0a
  | 3 => 0x32933108a882aacd95422042cc94c044e80d40
  | 5 => 0x231a21ccccccccf6d99b327088188188ffa000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0eeeaeeeaeee0eee0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_16029
namespace PEqualNP.Outside.L_meta_16029
open PEqualNP.Outside.L_meta_16029.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x210a4c0000040a82000000d5000000006071b000000000004804c0000600000000000ca2180001c0028023520000428000242c0001102740000000903007800b000000000000004000000345d2804e7c0080e3c000000000001000c3810004001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x105a000004464200640076003812785420222c00007c7062586e0266147e7208740e3060241a444a0600005e0c00003a003e280040001856263234002e001e0068006c825c4c00001c3c80000a4e7a00506a162a00483652002828638480ac0424380000008000040091002dca521db54a43af29c855d5390a7ca9994f553329f2a4653d548caeea2995d14532e6990657a50906f2a120cf950319eaa0636e520c6daa418de94031bca80633e540867aa810d794c21aea98437a50086f2a010dd94640baa8c815e53102baa6205b94840b6a90817651102eaa2205d94630baa8c613f544c278a8984f950309eaa0616e520c2daa4185d94430baa88617651882eaa3104fd51209e2a2413e540827aa8105794c20aea98417651082eaa2104f953109eaa621b654c436aa9885d54610f9a8221f340443e080887c8c110f898221f220443e240885d94410
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2099002819c580514cab264d4110b458c40442e16210110ac19130442b06448110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 42
  | 4 => 66
  | 3 => 6
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (770+((h/14+packedAt s5K5 (672+(h % 14)*7) 7) % 96)*7) 7
  | 4 => packedAt s5K4 (1936+((h/22+packedAt s5K4 (1782+(h % 22)*7) 7) % 88)*8) 8
  | 3 => packedAt s5K3 (234+((h/2+packedAt s5K3 (228+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3fe1fffc1fe3f8e1c71f8fff8fc1fc1e09f673
  | 1 => 0xc1fe0e3fe1fc7f1e07e3f1c1f1fe1fe036cb9c
  | 2 => 0x1fff03ffe007ffff803fe01fe001fffc70c1f
  | 3 => 0xfe00003fffff801ffffc0001ffffe001f80fe0
  | 4 => 0xffffffc00000001ffffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x84242004440401000104824482444444005231
  | 1 => 0x9444a048c480a0240321908c9094494412c294
  | 2 => 0x288844910849500ac802241124089298c50c0a
  | 3 => 0x8194922114012535448002149298089680d40
  | 4 => 0x31118c039992649da693493800310311bfa000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeaeee0feeaeee0feeaeee0feeaeee0feeaeee0feeaeee0feeaeee0feeaeee0feeaeee0feeaeee0feeaeee0feeaeee0feeaeee0feeaeee0feeaeee0feeaeee0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_16029
namespace PEqualNP.Outside.L_meta_16029
open PEqualNP.Outside.L_meta_16029.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xf0949cc424c01c4c5c008c48b0b83c185400007514306400580068b4eca07ce40028d4143510d0aca8e80008803884cc0000400044610c00980000a4bd0800d80000780cf86c10e02cc88804fc7104dcf5002050904401b123441b0000380100450002007020a0c880017fd50057f54017f95005fd54005f55005fc54017fd4c057f53017f94c05fd53005f54c05fc53007fd0c01fe43007f50c01fc43017fd48057f52017f94805fd52005f54805fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc3200ffd4403fe5100ff54403fc5100ffd0403fe4100ff50403fc4100ffcc403fe3100ff4c403fc3100ffc8403fe2100ff48403fc21017fd4005fe50005f94005fd50017f140057c50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc2000ffc4003f71000ff84003fd10007d44003fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x1e400fdfd4f20006faa7900177f52c800bf72964005df54b2007fdaa5900036d52c800bf72164000fb50b2002fdc6590003ed32c800b7fb0e4001bf98720075fac390006fc61c8007bf2864003df14320077ee219000eff6588007bfb2c40039fd9620015fccb10036fd65880077e32c4003df1962001cf8cb1000eff64880137f3244000bf5922001df8c9100377f5488001beaa44003bfd8e20045fcc710002fd63880077e31c400ddfd4e20006faa71002afd628801bbfa944000df54a2001dfec310006fe6188007fb30c4001bd98620065fac31000ff561880017ab0c4003bf1862001dfcc11000f7e5088007be2844003fbc822002ff6411000ff71088007fd084400cfe4422005dfeca900037f65480013fb2a4002bf9952005dfaca9000afc6548017be32a40029f19520005fec890003bf64480015fb224009bf99120005fac890026fc6448001de3224000af1912005efea8900037d54480017fb1a4008bf98d20005fac690022fc6348017bfa9a4000df54d2005efea49002fee5248001bea92400bfb54920006daa490003ee4248001f6a124000fb8c920007da649002aff61480037f30a400abf5852000df8c29000f7e5048007be2824005fec812001fdc409002bf71048015fd082400afe4412001dfeca1000afe6508007bf32840029f9942003dfaca1000f7d65080013eb284003bf1942001dfec810026fe6408007df3204000af99020005fac81000fbd64080015eb204003bf1902003efea8100037d54080077fb184008bf98c2001fbcc610002de63080017eb184003f758c20005bac61000efc630800fbfa984000df54c2002dfcc4100177f520800bbea904003bfd842000dfcc21000ff661080037b3084006bf5842001feac210002f561080077e3084003bf9802001efca01000f7c5008007f79004003fe8802001fda4010017f92008007fb8804004fdd9510006eeca88013f66544009fab2a2004fd19510026e8ca88003f76444001fb3222000fd59110007e8c888013f75444009bbaa22004fd95110027eaa888003755444009fa2a22000fdd8d10007ecc688003f56344001fa31a2004fdd4d10026eea688013f65344009faa9a2000dd54d10027e8a688003f74344001fb21a2000fd50d10007e88688003f76244001fb3122000fd58910007e8c488013f75244009bba922004fd94910027eaa488003755244009fa2922000fdd0910007ec8488003f54244001fa2122000fdcc910007ec6488003f53244001fa1922001fdd811000deec088007f36044009fba822003fd9411001eeca088013f55044007fa2822003dd14110007ee808800ff64044001faa022003fd10110007ee608800ff63044001f91822000fd4c110007e2608800ff43044001fb9022003fd88110007e44088003f52044001f89022003fd08110
  | 1 => 0xa7e65100337eb288003df59440004faca2000efc65100137f3208009dfd504004efaa820022fe6310007ef3188000b798c40005fac62000fdd63100016eb188019dfd4c40006faa620003be4310013de2188005bf9884001fdcc420002ee62100017eb108003fb58840005dac4200677f5210001bea908000ef9084004f78842000eff61100037f3088003fd9844000decc220062fd6110007fab088000bd5844001df8c220027bf4110031dea088003bf9804001efca02000f7c5010007dfa008003fe9004001f7a8020027f94010007fb8808008bfd9730015fccb980237e65cc0053f32e6017bf59730046facb980027d65cc0117e32e6008bfd933004dfcc998002fd64cc0117e3266017dfd5330006faa9980237f53cc011ef29e6008df54f300bfbaa7980035d53cc011ef21e6000f750f3002dfcc598002fd62cc02fbfa966000df54b30047be6598003dd32cc0117fb0e6001bf987300b5fac398006fc61cc007bf2866003df143300b7ee219800eff658c007bfb2c60039fd9630015fccb18056fd658c0077e32c6003df1963001cf8cb1800eff648c0137f3246000bf5923001df8c9180577f548c001beaa46012bf58e300aefea7180037d538c00b7f3146000bf58a300aefea5180037d528c0077fb0c6001bf9863001fecc318006f6618c0297eb0c6003fd58630005eac31800efc618c0077f3046003df9423001ef8a11800fdf308c011fd9846003fdc423001ff42118053f9108c0277fb2a6000dfd9530004feca9800afe654c0277eb2a6002bf1953009ef8ca9800a7c654c0017fb226000efd91300057ec898026fe644c0017eb226009bf1913000778c898002bc644c027bfaa26000df5513009efea69804fde534c001bea9a6013f754d30006baa698003de434c001eea1a6000bfd893002df8c49804f7f524c001bea926000f7cc930007ba649804aff614c0037f30a6012bf5853000df8c29800f7e504c007be2826008fecc13001fbc609804bf7104c025fd0826012fe4413001dfeca1800afe650c007bf32860029f9943008dfaca1800f7d650c0013eb286003bf1943001dfec818026fe640c007df3206000af99030005fac81800fbd640c0015eb206003bf1903008efea8180037d540c0117f3186008dfd4c30046faa618016fe620c007f73106000bb98830005fac41800fed620c00176b106011dfd4830006faa41800eff610c0037f3086003fd9843000decc218042fd610c007fab086000bd5843001df8c21800efe600c007bf2806003df1403001fbe601800ffa300c007ee9806008fe4c03001fee2018016ff65c80057f32e4005df99720014fccb9003efd65c800bbeb2e40009f5972002df8cb90016ff64c80137f3264000bf5932002df8c99003f7f54c8001beaa64005bfd8f20045fcc790002fd63c800b7e3
  | 2 => 0x32006faa8990937f534c801bea9a6400f7d0d32007b886990937f524c801bea926400fbd0932007d88499023ef324c80bef1926423bfd8532007eec299002f7614c8037f30a6423bf5853200df8c29908ff4614c8037a30a6423f7cc53211fba629908fef214c847f690a6400bfd813201df8c0990937c504c847fb8826405bfd9432015fcca190177e650c8053f3286422bf5943202efaca190027d650c80b7e3286405bfd903204dfcc819002fd640c80b7e3206422dfd5032006faa819022fe630c811bfa986408df54c3202dfcc4190177f520c80bbea906405f7cc83202fdc6419017dd320c811f69906400f34c83202dfec219006fe610c8437eb086401bf1843201dfcc019002fd600c845be2806421fdc403201efec92800f7e6494007beb24a0009f5925001ef8c92800f7f6394007bf31ca003df58e50004fac72800f7c6394001bfa1ca000df90e50006fa87280037c4394007bfb14a003df98a5001efac5280027d6294007be314a000dfd0a50006fc85280037d4294001be214a000dfcca50006fc65280037d3294001be194a003dfd865001efcc32800f766194007beb0ca003dd5865001ef8c3280837f4194041bf20ca020df50650106f883280837f3194041bf18ca020df4c650106f863280837f2194041bf10ca020df48650106f8432800f7e60940073f304a003de9825001efe212800f771094007bf084a003df4425001ef82128026ff65d00057f32e8009df99740014fccba007efd65d0013beb2e80009f5974004df8cba00277f54d0013df2a68009df553400ff7aa9a00033d54d00117f31e8000bf58f400fefea7a00037d53d0013dfa1e8000ef50f4002dfcc5a0002fd62d003fbfa968000df54b4004f7e85a0003bd42d00137fb0e8001bf987400f5fac3a0006fc61d0007bf2868003df143400f7ee21a000eff6590007bfb2c80039fd9640015fccb20076fd65900077e32c8003df1964001cf8cb2006afd649003bbfaa48000df55240045fcc720002fd639003bbfa9c8000df54e400077c8720003bc439000b7f3148000bf58a400eefea5200037d5290001df2148000ef10a4001dfec320006fe6190007fb30c8001bd986400e5fac32000ff561900017ab0c8003bf186400e77e8320073bd41900077f3048003df9424001ef8a12000fbf4090013fda048003fdc42400ddfecaa00037f65500013fb2a8002bf995400ddfacaa000afc6550037be32a80029f195400defea8a006fbe5450001beaa2801bef551400067aa8a0002ff63500117e31a801bdfd4d40006faa6a0003bf4350001dea1a8000bfd894002df8c4a006f7f5250001bea928000efd09400077a84a006aff61500037f30a801abf5854000df8c2a000f7e5050007be2828009fed014001f7c80a006bf710500077fb288002bf9944001efcca2000
  | 3 => 0xe302a4039f1815218efe20a90c7771054863bf082a431df4415218ef820a9026ff65d08057f32e8409df99742014fccba10c2fd65d0813beb2e84009f5974204df8cba10277f54d0813beaa68408bf98f42005fac7a10c37f53d0801bea9e8400ef90f4204f7887a10c37f52d0801bea968409bfd874200dfcc3a10befd61d08037e30e8409efd074217f7a83a100efe60d08017eb068430df1434217fee21a1016ff65908057f32c8405df99642014fccb210bafd659080bbeb2c84009f5964202df8cb210aefd649085dbfaa4842eef95242006faa9210bbbd54908019eaa48408bf98e4202fbcc721002de63908017eb1c8405f758e42005bac7210bb7f5390801bea9c8400efd0e420077a8721016fe629080bbfa948405df54a4202f7e8521027ef429080b7fb0c8401bf9864216dfac321006fc61908077f3048400bf58242176f8a1210b7f710908597fb2a8402bf99542166fccaa100a7e65508597eb2a8400df59542004facaa100afc6550859bfaa28400df55142005fec6a1022fc6350859bfa9a8400df54d420077c86a1003bc4350859bfa928400df5494204fde84a1017be42508577fb0a8401bf9854215dfac2a1006fc6150857dfa0a842bef50542005fec0a100efc6050859be282842bfdc414202dfeca2100afe651080bbf32884029f99442155faca210177d65108013eb288405bf1944204dfcc8210277f5410813df2a08409df550421577aa8210033d54108117f3188400bf58c42156fea6210037d5310813dfa188400ef50c4202dfcc4210177f521080bbea908405efd084202fdc8421017bd4210813f6a108405bfd844200dfcc2210a6fd61108037e3088403bf98042005fac0210ab7c5010853fb8808408bfd9732015fccb990237e65cc8053f32e6428bf59732046facb990027d65cc8117e32e6408bfd933204dfcc999023be64cc8015f3266400bf593320477ac999002bd64cc8117e3266428dfd5332006faa9990237f53cc811bea9e6400f7d0f32047b887990a37f52cc801bea966408bfd873200dfcc39909efd61cc8037e30e6408f7cc73213fba639900efe60cc8017eb066428df1433213fee2199016ff658c8057f32c6405df99632014fccb1909afd658c80bbeb2c64009f5963202df8cb19016ff648c8137f3246405ef992320057cc919002fd648c80bdeb246400af5923202df8c91909b7f548c801beaa46423bf58e32136fea7190037d538c80b7f3146405dfd4a3202efaa519003ef428c80bf62146405f7cca32047de6519016ff618c8037f30c6425bf5863200df8c319017ef218c84bf690c6403bf98232005fac11909b7c508c84bfb8846424bfd9532015fcca990937e654c8053f32a6424bf59532006faca990027d654c8057e32a6400bfd913204dfcc899002fd644c8137e3226424dfd51
  | 4 => 0xef7f6155077bf30aa83bdf585541def8c2aa0277f41550779fa0aa83bdf905541defa82aa0ef3d4155013be20aa83bdfcc5541defc62aa0ef7d3155077be18aa83bdfc85541defc42aa0ef7d2155077be10aa800dfd8154006fcc0aa0037d6055001be302a8039f181541defe20aa0ef771055077bf082a83bdf441541def820aa0037f6454c013fb22a600df99153006fac8a98037c6454c05bfb1aa6029fd8d53016bec6a98037f6254c013fb12a600df98953006fac4a98037c6254c75bfb0aa63adf985531d6fac2a98eb7c6154c75bfa0aa63adf905531d6fa82a98eb7c4154c11bf98aa63adf8c5531d6fa62a98237c3154c75bf90aa63adf885531d6fa42a98eb7c2154c01bfb02a600df98153006fac0a98037c6054c073e302a63adfc41531d6ee20a98eb7e1054c75be882a63adf0415304dfecba180afe65d0c13bf32e86029f997431cdfacba18277d65d0c013eb2e8609bf1974304efea9a18277d54d0c73bfa9e8600df54f4302dfcc5a1802fd62d0c73bfa968609bfd874300dfcc3a18e2fd61d0c037e30e8609efd07431c77a83a180efe60d0c017eb068639df143431c7ee21a1822ff6590c057f32c8608df99643014fccb218defd6590c11beb2c86009f59643045f8cb218d2fd6490c6fbfaa48637ef95243006faa9218dfbd5490c019eaa48608bf98e43046fea7218237d5390c11dfa1c8609f7d0e4302dfcc521823ee6290c01773148600bf58a43047dac521802ed6290c6fbfa948608bfd864300dfcc3218dafd6190c037e30c8603bf98243005fac1218df7c5090c6dfb8848635bfd9543015fccaa18d77e6550c053f32a8635bf59543006facaa18027d6550c057e32a8635dfd5143006faa8a18d77f5350c01bea9a8609f7d0d430477c86a1802ff6250c0b7e3128635dfd49431a5fec2a1806fe6150c697eb0a8601bf185431a77e82a18d3bd4150c017fb028603bf181431aef8a0a18d3f71050c117fb288602bf99443046fcca2180a7e6510c677eb288608df59443004faca21822fc6510c137f3208609dfd504304f7ca8218277d5410c67deaa08600cf55043045fcc6218237f5310c11bea988608efd0c43047bc8621823bd4310c13eea188605bf98843005fac4218cf7f5210c117fb088601bf98443195fac221806fc6110c077f3008600bf5804319ef8a0218cbf71010c01bfb22a4009fd9152006fcc8a90037d6454801be322a400dfd8d52004fec6a90037e6354801beb1aa400df18d52006fe86a90037e4354801bea1aa400df10d52016fec4a900a7f6254805b7b12a431dfd855218efcc2a90c77d6154863be30aa431dfd055218efc82a90c77d4154863be20aa431dfcc55218efc62a90c77d3154863be18aa405dfc855218efc42a90c77d215480bbe10aa400dfd8152006fcc0a90037d6054801b
  | 5 => 0xe00e717525e3193a814a0d62d313512a0000001800d711f00039a0000fc0e00004361391bb1f63cf1cf2472690c12c83682f330536a39e2d61cb32f1a61a50a50b434f0004392dc1c232e0f70a02581f100000003500000023d1da0003511d800040c00024b00019a34d33c31240e1c10003b60000000000000000eb0001bf00036f1be2af3b81720bb2b40c330c33f2ba1272be32542831d0c42dd30e25b3a42773d41ce00002f2762ae27823c0ed1983cc05333a3573c40c53853e92613c13e42bd3070572f700019c3831843ea0000001d23653763dc3af1ba38900033643c04500000000018504635821e1cc2f642b16621125738e1a20e50003040430000681b13480700ac1bc15730f37a0550442fc37937800000028d26815e1b400000025f0000003920893b307905b3340e41c01c313a00015300008200000043d1232743b53ce18e3641d60d50000000df32600020f17919f33200021227f00042d39436b22100035b2553e836d19d00000041f0003d00000a70000e10f93f90003741ed2c34484500063162de0001c61082922fb3992c700032b12e00023400000000028e29831e2c900000000000019b4353963b90003ae0004430003a615400045906d000014010020020540040200902e0100300f01a00c028000000000300301000c010060140000180000400c04002004008080000160000001d00e0740580d0040080880100000c010000100081f80d0000040080d0260000101f00000c05010002000010080040100208201c0041a800004010008000020140084c02a00802000000000008040000400182200603c0180901e07c000000000580000800409c03000010000018020000001080100402807000022018068000000000280600e02c000070040000680101205c008030041000180000a00002001012018038010160180180300401800812000004008010040000780000000c00003002000040040260000000301403c000090040840400502e00412804058008000010000000480000e0300000604a0000200500008000800000004060130020600000b044000000020000940280400802800800008000020020260000080002200400000004000008030000280000001201c0080d01600c00801006000010080000880080b01201c0180f012008020030020140c8000380000381501a000000150000080000001e018228000240080380500c0000180f00201800001000004028010040840000b0000480100504e000010000000040000500a0000a80a008044008000060100100a00200000016004000010000040180200007607003011014034038020000000403a016fec8aa00a7f64550059fb22a800dfd8d54004fec6aa0037e6355001beb1aa800df18d54006fec4aa0027f6255001bf312a800df58954006f8c4aa
  | 6 => 0x741543814b2a72962e50f815c0040a418d1110190b12f81480002b10003a50002152b229b0da4470b031b2f52a441e41d1a41670de00000000000009a0e90e225a0a20000000002952623b015036e10920b03a4021dc3233a20b80773fa28803815800020d00344923223326d00003b43000018100000003927c00037e24233944017f0af0650d30b710d30a26e20c00000027e00000000026c00000031727d0943b234935a0d42e810400004a00013409c3882180002f100028409e0ae0aa02d0c226b2e635500021d1ca0a60ad35f3f02412db25c25d3f30a93fd1d70000003f541022d3143f233734a00033315118909006b23933129301743b07844b0021c83be0bc1ff0373ee23f4241a31441033e03903e720127934c18227a0ff00043431534e28f0001c42272b929018b2cf44e12414f27b3c20003242d218727143a3e63bf00011323e00019506308d1b541a1b21b809100141b1590003cb1e50000f611b00013e0000002ca0003d600000000013b3f129d0002863f408c2503220951401f219609d20e0000000b90590fe1261f721c0d223023b37722f3d538f1fb0290000001b340d02721415d0002870000f307e0003e50000000001120000000000f100007d0000000000000000000000003a70000a833507a1152992b80001370000004533d237000000000000000037f1910000000001172850000872190000000000003e300011a0000970000882c544524000011821344400000000000000034b00029700000032805000012b3811380221b70000561b92b542a4000000001ef0002ea00012c02306f0000000000000000000000742f04120000002bb3ec0000002d801539707600000017400000000000011d1293d70bd00000000045100026f00000044a2630000000692d440900000022901d00000000040b0002d528302034245800000000000000000000008e00000000010035900044d00009f00000037340f38210b00044c00000000000000000000043700028c17a0000ba3c72ff3ab04240828b2b33081433c80000000723eb08f3620053841453561de31c2590860b61ae31f39d3d115544129a05e3722fe13035c05a2ec38d3fe1f33d317320536116021a27218617144f1fd2640dc0674421882ab4010ce21b28a3933c61281101562454074563ef02b10235417b1141a100000012f29c1a71f03c02482ee00021003242f2ed39809200000000000014701f2c43da0001fa0e30003530000000002fd2c60db00000032732d1aa0000000000004210003aa32900000000008145700043300000000000000000d00017800033e0000cd00013600042e2b01d10d137c29416e12d0003a920241c02503d19900023645433d3d82df0cc0cb02637d18c0c03001621061ad29103e23124e39b2e92eb0b31760611ea1d03db0622
  | 7 => 0x8a24a00000004b1fe00031a0710600004260003470b50002ef2aa1f425407326a1b01b645e2040be38a33b3434170242703c33132c226037100e2062750000e83870001c718302102a10e1520002ce1a91071d502e0ea0000000280002a20002bc1051cd29f0000000f00001970003bc0000000000000001a00000000002801f90bf26745f0000000f543f0002d105d0000002200001bd4040ef0002a80f400000007c40509b2220000000000002ac0002661eb2a118f1f83dd10105c30200029e0003de2a30000000000000000000002a02e24293034180003ed36903f0002c10000000003440000003c52e32f443200000003c1e425604f0ee2241e30004522f92c024d1e908b42004e2260932513300001e035d0003f804928200841107f00b32c0002e439504132a2000003f73603a311c0331db30905830d30b06e0000d00000002a92ad03443e0000000000000f20003a100020a01c22841623500015f0fd1c52533df4220303f617008417e0180003ac0003450541330310850d83800000002651690000070000001252f217c3ad3523c91410fb0dd1160004460112371a801334601b0002da16d1310cf01e00001000037b45a12001438c0521e13bd14e41910f3b71194312491641901212d916f0164550ec02c3cd1221610123e14143381d335004037545d1c916c2232e714d1d42b700016b4230962440002bf22511e21f45b3210000004250d939c00f0362cc16a2cb18a04d09820336c3400000002b63ca1d92d000c00a22b2383671421af32014617d2810c741310a3011ac1e60990c80c91ee1770ab0a12893d938b1e81dd3ba19405116824313c3180a31ec0830640ca21723a1df3fb2a62460090803b138607513f15b45c13231122a2a540320922e10c3e22d71e72e13b43100e606a24f2161fc3ff1f535e2fa0b23fc3a01ab3bb15a04c0fa06636327330601a07b0002cd00004706c14936619e40613d0480c614c40a00000042c24c0004270000000001631e225205f16539122c20839f34119319220
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x57598910055f17098910005777558910025747558910005b77458910005b47458910005d77358910005d47358910075f37058910025767518910005757518910005b67418910005b57418910005d67318910005d5731891000576765491000574765491000577745491000577735491020577725491002767725491001d76705491001d74705491018e77605491018f7360549100257675d09100057575d0910025767590910005757590910007355490910005d67390910005d5739091001df27090910005f1709091002576755091000575755091002576751091000575751091000735541091001df27010910005f170109100257675cc9100057575cc910005b674cc910005b574cc91001df270cc910005f170cc91002576758c91000575758c910005b6748c910005b5748c91001df2708c910005f1708c910004f7764c910004f4764c91002576754c91000575754c91002576750c91000575750c910007c5320c91001df2700c910005f1700c9100257675d01100057575d01100073554d011001f7050d01100057775501100257475501100073554501100257675cc1100057575cc1100075553cc110085f2768c11001ef2768c11001f73758c11001f70758c11000773658c1101ff70658c1101ff73548c11000771548c110095f1738c1101ff73538c11000771538c110005f1728c1101ff73528c11000771528c11000577754c11002574754c110005b7744c110005b4744c11000755534c11001f72504c11001f70504c11000df2764c11000df0764c11000773754c1101f770754c11000773654c1101f770654c110007b3744c110007b0744c1101f773544c11000771544c11001df3734c11001fd3734c110007d3634c110007d0634c1101f773534c1101f7d2534c11000771534c1101f7d1534c11000751534c110007d2434c110007d1434c110005f3724c1101f773524c11000771524c110007d3324c110007d1324c1100257675c81100057575c81100076552c8110035f2768811001ef2768811001f73758811001f7075881100077365881101ef7065881101ef73548811000771548811001df37388110005f173881101ef735388110007715388110055f172881101ef735288110007715288110005777548110025747548110005b77448110005b4744811000765524811001f72504811001f70504811000df2764811000df076481100077375481101e77075481100077365481101e7706548110007b37448110007b074481101e7735448110007715448110005f37348110005f173481101e773534811000771534811001df3724811001fe37248110007e36248110007e062481101e77352481101e7e252481100077152481101e7e15248110007615248110007e24248110007e14248110007e23248110007e13248110
  | 1 => 0x9200056d75509200056d758c920005ad748c920006ac648c92001cec764c9200056d754c920006ac644c920046cc634c9200047f74594200047f735942002c7f725942002c7d725942001c7e705942001c7c705942001e6f205942001e6d205942001e77105942001e75105942004e3e759902004e3d75990200063f539902002e3f529902002e3d529902001e3e509902001e3c509902001eb7109902001eb510990200147e75590200063f54590200063e75590200063d75590200063f535902002e3f525902002e3d525902001e3e505902001e3c505902001eaf205902001ead205902001eb7105902001eb510590200047f76550200047d765502004e3e64550200063d64550201de7661550200465e7598c200465d7598c200065f5498c200065d5498c2002e5f5298c2002e5d5298c2001e5e5098c2001e5c5098c2001ed71098c2001ed51098c200147e7558c200065f5358c200065e7558c200065d7558c200065f5458c200065d5458c2002e5f5258c2002e5d5258c2001e5e5058c2001e5c5058c2001ecf2058c2001ecd2058c2001ed71058c2001ed51058c200047f7654c200047d7654c200063e6454c200063d6454c200465e6354c200065d6354c201d6766154c2000677545842000675545842000677535842000675535842002e77525842002e75525842001cf7705842001cf5705842001e76505842001e74505842001ef2205842002ef1205842021d7676d95100267676d95100057574d95100057573d95100057572d951001d7670d951001d7470d95101067760d95101077360d95100257475d91100257675991100057575991100d5f17099110005777559110025747559110005d77359110005d47359110005e77259110005e472591100f5f3705911002576751911000575751911000576765511000574765511021577745511002737745511000736645511000735645511000577735511000577725511000773705511001d76705511001d74705511000770705511001d7070551101de7760551101df7360551100257475d8d10025767598d10005757598d10095f17098d10005777558d10025747558d10005b77458d10005b47458d10005e77258d10005e47258d100b5f37058d10025767518d10005757518d10005b67418d10005b57418d10005e67218d10005e57218d10005767654d10005747654d10005777454d1020d777354d10027577354d10005777254d1001d767054d1001d747054d101d6776054d101d7736054d100257675d0d100057575d0d10025767590d10005757590d10007355490d10005e67290d10005e57290d1001df27090d10005f17090d10025767550d10005757550d10025767510d10005757510d10007355410d1001df27010d10005f17010d100257475d89100257675989100057
  | 2 => 0x4e3e64550300063d64550301de76615503002e6e759883002e6d75988300066f54988300066d54988300466f53988300466d539883001e6e509883001e6c509883001ee7109883001ee510988300147e75588300066f52588300066e75588300066d75588300066f54588300066d54588300466f53588300466d535883001e6e505883001e6c505883001ecf305883001ecd305883001ee7105883001ee510588300047f76548300047d76548300063e64548300063d645483002e6e62548300066d625483018e76615483000677545843000675545843004677535843004675535843000677525843000675525843001e76505843001e74505843001ef23058430046f130584300047f74597200047f73597200067710597200147e75593200047f76553200047d76553202463f645532004e3c64553202472e42553200147e7558f20004f77158f2000cf47158f200047f7654f200047d7654f2002d6f7654b2003e6f7654b200056f7454b200056f7354b2001d6e7054b2001d6c7054b2023f671054b200056d7550b200056d754cb2002ecc634cb200047f75592200147c755922001c7e765522001c7c765522004e3e64552200063d64552201de7661552200047f7558e200147c7558e20004bf7458e2004cbc7458e2001c7e7654e2001c7c7654e200465e6354e200065d6354e201d6766154e2001c7c7654a2005e6d6254a2018e766154a2001d787054a2000677755862000674755862000677545862000675545862000677535862000675535862000677525862000675525862001e76505862001e7450586200147e76d95200047d74d95200047d73d952001c7d72d952001c7e70d952001c7c70d95200067710d95200147c75d91200063f54d912004cbe76d91200063f65d91200063c65d91200063f75d91200063c75d91200063f53d91200063f52d91202363e50d91202363c50d9120006b710d91200047f75591200147c7559120004be76191200063f65191200063c651912004e3e751912004e3d75191200063f531912004ead72191200063f521912022e3e501912022e3c5019120006b710191200047e76551200047c76551200063f645512004e3c64551200147c75d8d200047f7558d200147c7558d20004bf7458d2004cbc7458d20004f77158d2000cf47158d200047e7654d200047c7654d200063f6454d200063c6454d2001c7c76549200063f64549200063c645492001d7870549200166f765492001d6c76549200166c765492001c6c76549200056f74549200072f64549200072c64549200056f73549200076b705492001d6e705492001d6c705492000768705492002e6f605492002f6b60549202276710549202276a10549202276910549200056d759092004eac64909200072d5490920005cd739092001cec765
  | 3 => 0xe73908400069d6390840006ad629084004e77545844004e75545844000677535844000675535844000677525844000675525844001e76505844001e7450584400047f74597300047f72597300067710597300147e75593300047f76553300047d765533026e3f645533004e3c645533026f1e43553300455f7654f3008e5f7654f300055f7454f300055f7254f3001d5e7054f3001d5c7054f30267571054f300055d7550f300147e7558b30004f77158b3000cf47158b300047f7654b300047d7654b300055d754cb300047f75592300147c755923001c7e765523001c7c765523004e3e64552300063d64552301de76615523001c7c7654e3009e5d6354e301d6766154e3001d787054e300475b3054e300047f7558a300147c7558a30004bf7458a3004cbc7458a3001c7c7654a3002e6e6254a300066d6254a3018e766154a3000677755863000674755863000677545863000675545863000677535863000675535863000677525863000675525863001e76505863001e7450586300147e76d95300047d74d953001c7d73d95300047d72d95300067710d95300147c75d91300063f54d913004cbe76d91300063f65d91300063c65d91300063f75d91300063c75d91300063f53d91300063f52d913025e3e50d913025e3c50d9130006b710d91300047f75591300147c7559130004be76191300063f65191300063c651913004e3e751913004e3d751913004e9d73191300063f53191300063f52191302563e50191302563c5019130006b710191300047e76551300047c76551300063f645513004e3c645513001c7c7654d300063f6454d300063c6454d3001d787054d300165f7654d3001d5c7654d300165c7654d3001c5c7654d300055f7454d300071f6454d300071c6454d300055f7254d300075b7054d3001d5e7054d3001d5c7054d30007587054d300465f6054d300475b6054d3024f571054d3024f5a1054d3024f591054d300055d7590d3004e9c6490d300071d5490d30005cd7290d3001cdc7650d300055d7550d300147c75d89300047e76549300047c76549300063f64549300063c64549300055d75cc9300059d74cc9300069c64cc93001cdc764c9300055d754c9300069c644c93002ecc624c9300047f74594300447f73594300447d73594300047f725943001c7e705943001c7c705943001e5f305943001e5d305943001e77105943001e75105943004e3e759903004e3d75990300463f53990300463d53990300063f529903001e3e509903001e3c509903001eb7109903001eb510990300147e75590300063f54590300063e75590300063d75590300463f53590300463d53590300063f525903001e3e505903001e3c505903001e9f305903001e9d305903001eb7105903001eb510590300047f76550300047d7655030
  | 4 => 0x53400147e7558f400047f7654f400047d7654f400053d7550f400147e7558b400047f7654b400047d7654b400053d7550b4001c7c76552400de3d64552401de76615524001d78705524004f3b40552400047f7558e400147c7558e4001c7c7654e400053f7454e400465e6354e400065d6354e401d6766154e4025e3f6590e40005ae7290e402563f6510e400047f7558a400147c7558a4001c7c7654a400053f7454a4002e6e6254a400066d6254a4018e766154a402363f6590a400059e7390a4022e3f6510a4000677755864000674755864000677545864000675545864000677535864000675535864000677525864000675525864001e76505864001e7450586400147e76d954001c7d74d95400047d73d95400047d72d95400067710d954001c7c765514001d7870551400163f765514001d3c76551400163c765514001c3c76551400053f735514026e3c63551400053f72551402463c62551402763f61551402763d61551400073b705514001d3e705514001d3c705514000738705514004e3f605514004f3b60551402773710551400147c75d8d400047e7654d400047c7654d40004be76d0d400053d75d0d4001cbc7650d400053d7550d400147c75d89400047e76549400047c7654940004be76d09400053d75d094001cbc76509400053d755094004c7f745944004c7d74594400047f735944004e3c43594400047f725944004e3c425944004e3f41594400063d415944001c7e705944001c7c705944001e3f405944001e3d405944001e77105944001e7510594400465e7598c400465d7598c4004e5f5498c4004e5d5498c400065f5298c4001e5e5098c4001e5c5098c4001ed71098c4001ed51098c400147e7558c400065f5358c4004e9c4358c400065e7558c400065d7558c4004e5f5458c4004e5d5458c400065f5258c4004e9c4258c4004e9f4158c400069d4158c4001e5e5058c4001e5c5058c4001e9f4058c4001e9d4058c4001ed71058c4001ed51058c400047f7654c400047d7654c400053f7454c400465e6354c400065d6354c401d6766154c40004bd7690c400063d6590c400069d6390c40005ae7290c4002e6e759884002e6d759884004e6f549884004e6d54988400066f53988400066d539884001e6e509884001e6c509884001ee7109884001ee510988400147e75588400066f525884004eac42588400066e75588400066d755884004e6f545884004e6d54588400066f53588400066d5358840006ae435884004eac435884004eaf4158840006ad415884001e6e505884001e6c505884001eaf405884001ead405884001ee7105884001ee510588400047f76548400047d76548400053f74548400065e63548400065d635484002e6e62548400066d625484018e766154840004bd76908400063d65908400059
  | 5 => 0x67461595320047f74595321347f73595320065f73595321447f72595320066f725953200677715953200674715953201c7c70595320067710595320147e75d91320047d75d91320147e7559132004f7715913200cf471591320047f76551320047d76551320063f645513204e3c64551320055f73551320056f72551321de7461551320056f7254d320474c3254d321d6746154d3202cde76d0d3202dce72d0d320071d5410d320147f76549321247d76549320055f735493202f4c325493218e746154932044ee76d0932045ce73d09322978c43d09320072d54109322978f431093200cf676d85320067665d85320067565d85320067675d85320067575d85320067754d85320067554d85320067753d85320067553d85320067752d85320067552d8532004f570d85320067450d85320147e75d81320047d75d813200cf471d81320047f745943201c7c70594320067710594320147e75590320047f76550320047d76550322463f645503204e3c645503202dcf764c832006cf764c83228f4e754c8320074d754c83202f4e654c83202f4d654c832296ce644c83202ecc644c83228f4f544c8320074d544c832007c7714c832287c4714c83202ecf614c832286cd614c83228f4c504c832287c7104c8320047f75580320147c7558032004bf745803204cbc7458032006cd325803201e3f74592500047f73592500047f725925001c7c705925001e3e405925001e3c405925001e77105925001e7510592500047f7458e500063f7458e500043f7458e500063c7458e5001e5f7358e500047f7258e5001c7c7058e5001e5e3058e5001e5c3058e5001e771058e5001e751058e5001c7e76d0e500047d76d0e500063d64d0e5001c7e7690e500047d7690e500065d6390e500056e7290e500056d7290e500047d7650e500063d6450e500065d6350e5001c7e7610e500047d7610e500047f7458a500063f7458a500043f7458a500063c7458a500047f7358a5001e6f7258a5001c7c7058a5001e6e2058a5001e6c2058a5001e771058a5001e751058a5001c7e76d0a500047d76d0a500063d64d0a5001c7e7690a500047d7690a500055e7390a500055d7390a500066d6290a500047d7650a500063d6450a500066d6250a5001c7e7610a500047d7610a5001c7e76cca500047d76cca500053e74cca500053d74cca500065d63cca5001c7e768ca500047d768ca500053e748ca500053d748ca500066d628ca500047d764ca500065d634ca500066d624ca5000577714ca5010574714ca5001c7e760ca500047d760ca500074d320ca500047f73597400047f725974000677105974004d3f76553400ce3f76553400053f735534026e3e63553400053f72553402463e625534004e3f615534027e3d615534001d3e705534001d3c705534027f37105
  | 6 => 0xe62552422463f61552422a63d61552422353c70552422a73710552420465e7598e420465d7598e420065f5498e420069e5498e420065d5498e420069d5498e420061d5498e4202e5f5298e4202e5d5298e4202e9f4298e4202e9d4298e420065c5098e42006d71098e420147e7558e420065f5358e420065e7558e420065d7558e420065f5458e420065d5458e4202e5f5258e4202e5d5258e42296cf4258e4202ecc4258e420065c5058e4202ecf2058e42006d71058e420047f7654e420047d7654e420465e6354e420065d6354e420053d75d0e420469e63d0e42044bf7650e420053d7550e420469e6350e420047f75582420147c75582420063d54582421747f74595420063f74595420047f73595421847f72595420066f72595422463e42595420063f41595420063d415954201c7c70595420067710595420056f725514204f2c42551420147e75d8d420047d75d8d420047f7654d420053f7454d4202cbe7690d420063d6590d4202dae7290d42004be7610d420063d6510d420147f76549421647d76549420053f745494202f2c42549420147e75d81420047d75d81420047f735944201c7c705944200677105944204d3f76550421863f76550420053f735504226e3e63550422453f72550422453d72550422463e625504204f2e625504204e3f615504229e3d615504222d3c705504229f3710550420147e7558c420047f7654c420047d7654c42004bf7650c420053d7550c420047f75580420147c75580420063d54580420047f745973201c7c70597320465f305973200677105973204e3e759933204e3d75993320463f53993320463d53993320063f5299332046ae3299332046ad32993320063c5099332006b710993320147e75593320063f545933202cdc73593320063e75593320063d75593320469c73593320463f53593320463d53593320063f52593320063c50593320469f3059332006b710593320047f76553320047d765533204e3e64553320063d64553320055f735533226f1c43553320069d64d0f320147f7654b320063e6454b320063d6454b320055f7354b3202f4e3254b320047f75583320147c75583320047f745963201c7c705963202e6f205963200677105963204e3e759923204e3d75992320063f539923202e3f529923202e3d529923202e9f329923202e9d32992320063c5099232006b710992320147e75592320063f545923202cec72592320063e75592320063d75592320063f535923202eac725923202e3f525923202e3d52592320063c505923202eaf2059232006b710592320047f76552320047d765523204e3e64552320063d64552320056f72552322472c42552320147f7654e320063e6454e320063d6454e320056f7254e320474f3254e32006ad64d0a320047f75582320147c7558232
  | 7 => 0x524304f1f435524326d3f76552430163f76552430143f76552430163c765524326d3f73552430071f735524326f1c735524304e3e63552430053f72552432463e625524326f2e625524326f2d625524326e3f61552432b63d615524325d3c70552432b737105524302e6e7598a4302e6d7598a430066f5498a43006ae5498a430066d5498a43006ad5498a430062d5498a430466f5398a430466d5398a43046af4398a43046ad4398a430066c5098a43006e71098a430147e7558a430066f5258a430066e7558a430066d7558a430066f5458a430066d5458a430466f5358a430466d5358a43296cf4358a43046cc4358a430066c5058a43046cf3058a43006e71058a430047f75582430147c75582430063d54582431bc7f74595430063f74595431cc7f73595430065f735954326e3e43595430047f72595430063f41595430063d415954301c7c70595430067710595430055f735514304f1c43551430147f7654d431ac7d7654d430053f7454d430471c4354d430147e75d89430047d75d89430147e75d81430047d75d81430047f725944301c7c705944300677105944304d3f76550431ce3f765504326d3f735504326d3d735504326e3e635504304f1e63550430053f72550432463e625504304e3f61550432ae3d61550432553c70550432af3710550430147e75588430047f75580430147c75580430063d54580430047d73d915201c7e70d91520067710d91520063f64991521656d72991521856f72591520063d64191520053e74d8d520053d74d8d520063e74d8d520047d74d8d520063d74d8d520043d74d8d5201c7e70d8d520067710d8d520053e7498d520053d7498d520065f6398d521256d7298d521456f7258d52005777158d5218d747158d520047e76d0d520047d76d0d520063f64d0d520047e7690d520047d7690d5202d6e7290d520056d7290d520047e7650d520063f6450d520047e7610d520047d7610d5205d6d729815218d7671981520057571981520053f74581520053c745815206d6f72581520053e74181520053d74181520055e73181520055d731815218d76711815200575711815201e7a60181520047f735974204e3c43597422463e425974204e3c425974204e3f41597420063d415974201c7c705974204e3f40597420067710597420147e7558f4202cbc7458f420047f7654f420047d7654f420053f7454f420063d6590f4202dae7290f420147f7654b420053f7454b4202f2e4254b420047f75583420147c75583420047f735964201c7c705964202e6f20596420067710596420147f76552420056f725524204f2f42552422453f76552420163f76552420143f76552420163c76552420053f735524226e3e63552422471e63552422471d63552422453f72552420072f72552422472c725524204e3
  | 8 => 0x1180507200008812000018000160040340000800803801008000050000000780000300201a00c1200601e01c030050000000187a08a01c0180501000000004088018000010560580a00605c0040980100a1600080400202804800000028020170160000180701200813004006020000030080280b80000008c0000401c000010030180140000400c000010060300140102803600400802000040268090320000000a040000000120100001d80502c104000010040080400801803406002020040010020000240080701800c000030020000000007e01c028240120980000203603c090470000040000001a004030010000400000300000c328020340180080e0140300007c000018128000020042902a00e0080083d000000000010100340c80002c0140300100a0480b0000000600081503a0dc050010280181d0000000040802300200c0c800028014050080040d80101d02401403806014020000040300040080401805008816036004140090160080000700001000000000000000010260001380205001c0000400400c0080005c018058000020080a00c0c40000002c0000380000704c0bc0080700e00c000090020100080103200002004016000000030020400c803048008040000120440480208600801011008010000180180140f0130040400200100400c01805002000180001ce3d74d8d540047d72d8d540063f41d8d540063d41d8d5401c7e70d8d540067710d8d541ad3d7498d540065f6398d540056e7298d540056d7298d541bd3f7458d541863d74d89540047d73d89540063f41d89540063d41d895401c7e70d89540067710d89541653d74989540055e73989540055d73989541753f74589540dd3d74981541dd7671981540057571981540ed3f74581540055e73181540055d73181540056e72181540056d72181541dd76711815400575711815401e7a60181540047d72d915301c7e70d91530067710d91530063f64991531ad5d73991531cd5f73591530063d64191530053e74d89530053d74d89530063e74d89530047d74d89530063d74d89530043d74d895301c7e70d89530067710d89530053e74989530053d74989531255d73989531355f73589530057771589531d574715895309d5d73981531d57671981530057571981530053f74581530053c74581530ad5f73581530053e74181530053d74181530056e72181530056d72181531d576711815300575711815301e7a601815326e3e435974304e3c43597430047f725974304e3c425974304e3f41597430063d415974301c7c705974304e3f40597430067710597430147f7654f430053f7454f430471e4354f430147e7558b43044bc7458b430047f75583430147c75583430047f725964301c7c70596430465f30596430067710596430147f76552430055f735
  | 9 => 0x74c0002e41100009c0a1245665c23850c8020003366c49f69bab3c73678c5489624206e0b34924474a0a87c88845e8c820e148886682964644a041823dc37c48697e92295c7084c24389ac8ac3684b0536a2c4ca49005c624526226996ae839e7003645eea0284e6e85d691c5140fc9d632cacca9414e34cb540f01ec1ba3102046569d03e80c03566da5d23740b495a5da65086cab2818b408828940000007d44d80000004d0776a9294e00000000000089000000000000046a6ae00027025459898869600039207ea2057caba3de8daaae9543a600216631e40282c39404e966a1e4f48e418a3707f2a30ae66987dc8d082400018013aa4287012021c54244c6f220a9302f242a000000a74764b3e1465248567ce2b47184505e29ce80e4a41aaa5c70a5623049da12816e7eaa246b00002561ac822a6c0007ca15210a0a4b2449a86e7a65825ea18e49610c07c99413200050a2b241a000000820a9a08c02861e7e85dea0c054596a1c0004403f00007749f45d89e40000ca78405800000023e2e6b2088e42c0000000000000002840007443c8aa893600021a2000005aab58b0400077a000b280000000fa79c1f20006ca000a540d400095857a0009c409400000010e9e82b83aa9284ba0002d40003da14c57e11435e1249c89b06142ec1d40007aa6cc9a2454a70220b166345760484c629889853a2e88b46c0250ade2ca2c643c4666464b69727e2000090642ae20008927a2000000000af8a8827a24c0002824600000000009ee632a3a69a25290c8c07562d05500000004a29a80c6b446d20687bc00075e6684d401c45c3fc852b4ca6847268a00011862e000abe87e87a7605b883a0001d051a6f070200089c22e55a0000009340003d6076000b1085484a0000dca60a163b6a9cac495222c17e2ae354b4e860970b5093a99c46275472e74a00041ea32158574834228a0881273c52203e3621066ce30e08408657838c7d6a4609a4422125e62c49ca3f89e27fc83035040060c85e0527345685be2d293c00073aac88a4a8495e7b46b294aaf01a039c7985ca2f40d2072b2c666780006a866122c23720341fab3810867a610a5000021856029e91694cb3253071253271e6c27820cc0b25c02ba4aa0745eca2a1e619069031c0e271a68e98e8ca06e3a42723e62023883d474851ca7a728974792a48000126004044010080060000100005a00001000002018138110020140380b0100b00080e03c0f00480900202c010030000040085a00e0200000401c1d80000700c0000103b01e06c0100f0360100080e0040000086e06000c0000206c004048040040000000900e1140800000a004140000000040081301e00800803000004010030000000380800e008088000620380080205c0080000100800c010150580200000100003c0580200a00
  | 10 => 0x904449d86e60006dc8063c664eb42948722ada3d85e88f06540000006589f8ad84d60660008446d00006b6000468ae0a28b1c5467404060240006ac0005ac63e7e626c9de726826b1a02c2f060a66e0005441b26d624a4ce2f6214b122fc00005a08889e4b82ee8f40000e48001120000001f4a523baa2e26aab45403f628ca648a25d47de7f412a0623fe5a80000000008e2000512b1845a0006a400034e0006169e62ce76236a1567949ae8489120005a09beb0c4e67065c498c000aa255e000a100000d80009200006180006924088e83289184ee8500004e85ae2742086043a2ace8c60002608f25940000003f2ac08be0180002e20008642a494061a46c206a3c50222a8080007d255221eac21b68e00b885c5a20004581a832400017c4306520001fe07a63c0bc2e04140007e40000000000000080e600046e000ab833400000043699004c306600aea5008766c80003120007cc92c73e1884287709020000008f60004acb2e6f860e56a0007be91434a4e4000afc5a400027e5f80000008ba0301c85c24923585c60001985568ae00067027c60263819648a0002c08a652833a56486a0f69a42d6080738a4a7ac81c62c6de662626000af6b0e43e3ee92e2cc5dc278af40326b852a02231a57002688cb2200009e13e122000b4a8d4b5600047a1e058c82a0041d84a654e2487a08045d04246866bc3ca7feafe00035a6482863b80984f079e00091a1841fc7f6a6e00000055c9fc2b05f6b262ea3d05fea6205086644e0006fc0000000000000c479a99271619e1ae0f40005727d090a2a86740001dc5fa1de67e41cadc2249760003ec62064c3304be59e8de63a000000000a34a442c826e8c49ea3be0004b4056aac8a86f40000006e425a47c8fc0f81b413c3e20009fa0008e608e02e00087448c0007ae000154a8c01a0004769cc21041678a1da7b871c16a0b60008287ee0a85540003fa18c0000004d274e758216ad43660003d243a1f05040000003b40be8a00429d435c3080000000005b43380001a20000006a600062aa9e0006c60006aaa5e9b83760008ec28e81e00050882e26834856ead20000004ae0005ba404266a1866a6ea8fe8160c28c200ea262224b223414403c0008bc4e296040a0ceb0200058a70c038afa000174b0847849e00084ca3e00006026276800054c000660000070000a78000714516a96a2267696a2420007b03e40000004bc8b09680b07f0520000518a8a3ae3a80008b200069448861c9325887048d26285669045389089b2b4614a7244fe116380a1aaca41004644a4fa0640ea622b360007307a83028ea58498250e3c20002d875097a7ba3869a6aeca40000000138044b520000000000a0040000344000b000008103207b640c4fc55833e2fe80c6a000000a31600059c90e89a0000004de06a6ec470
  | 11 => 0xa008aa7fa2da1000fe78e06c96c00000042692664aa981e80006ee02aad6a824c800059272c3462de75a0008963c45b60123187428408ce09c0ec8b8a060001601868f80000004e00000003525f260841200072a4460001e40e8104398000000a4e42297c8320001785f430c0000007ec04a1a66be26465e0de2940000000000000000006b476a15a7da74600088a1620004c029a69e2928b64f83c012ca9037e31400092a23658600000054a8580002f83845b2a66510258000b1e00015c3320da6a87523ea0006800003900008840000a2000000aa60002320005c80002dc000418abc00023c000000aa000068c5bc910862ae4000172984000ab60ba0001c22769787c44480a66646fa3e08ee40e3008144a05e4b0a24059a4a8af216cab01d24647c053493e1361680002bc0000007780827663961c69aaa804329807f8000290b4898600094605ea6aa72a5601067296e1f89c603a20c5ce73200c32277c9dc2467b24c49c228a9e099836c0c8194b146881bc0d667c4f645238e81a11c9ec2a632a56c020b063b26f615052e01495651e1705fc3b080a68419c24449c8681640368385f037a08a7c2a0ea7e1407d81ea640b2a4849b4000092434b3a1b0a8e87253c7c89f200000025e75c49438278600000024e7889f05b04f26d40783ac8800002aa9a02800007c601e0ee9d285aaee000678796176a582fa6a200000037848000066c58e23a76c0001c40000003cc8dc0008786361a40f23a06063f40ae30a0001c0aa4842288a4c3600009bc000a140ac00042e29600015e98a130a5a0001d61e24cc0aa9383bc0000000008461be83c4827a43ce94449852c5e091e342016ac66e2710ad02be8fa230a385809066d84ea69c99e77277e2b695011e70ea3639a47ea7634053e17a25c9421028cc1346ba90076e1f6aaa38a48e3267e083e1ce63012e2a01cc9b636e4dc1b81ee1425a66fe2aca7c8d84ec99a19a59065a8d609611a1925060e032e9fe2a21ca29c4da0d0b305cc72083633c0007
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x83e87d4b644c00107b0fa98c8980020f61f521913025e0e3b6c8a9a604ac1c76191534c00123b09b92a698002d46047054d300050e432a921a6052c8c645ca434c0070b90cbaa86980022761c64cc93001c2e432ea992600083d84dc9650c00107b0fa94c8180020f61f525903000516c26a4b106000a2d849d5620c00146b09a92c2180020f61373597200141ec26ecaa6400083d84dd953c800125b09b9aa59000e0f21d645522001c2e43ac6a9c4000a35841d5618800146b09a9ac3100028d61352586200041fc22e7b2a4000a2d82d53644800143b063aec89011a8b60875d91200041f43ea7b22404683e87d4b644800107b0fa98c8900020f61f5219120236163b6c8a924045c2c76191524800125b09b9aa490002d8604705492000516432a92124052c8c645ce42480070d90cbaa84900022b61c648c92001c36432ea992400083d84dcd650800107b0fa9cc8100020f61f53590200050ec26a6b184000a1d849d5630800146b09a9ac2100024de1173d95100049bc22e5b2a204eb318099154440b1a60e1322a8880124d21d64551100058a41ac8aa22000b2482591544409f66700b22a88815f4c1c1645511001cb943ee0aa22000b51831c154440016c304382a8880024d6107654d100049ac26e4a9a2003970805d7434400926f0eaa4868812ecc2015490d1000692aa4e521a2000d31545c243440072e100baa868812acc2015410d1000698aa2e021a2000935841d9524400126b09b9aa48800e5c20175d09100249bc3aa92122046b30805524244001a2aa939c84880034c551709091001cb8402eaa122045b30805504244001a62a8b8084880021d219754c91000562432641922000dc1325c0324400766100aa6808800e4d21d545011001d98402a8a022003970875523044093aa2e6a9c6088003585c9528c11025698280e898220039548754d3044001a60ea3a260880025c21d544c110005a8c28c69822000b918418d30440017830431a608800ed4a1d534c11001da843aa69822000b528654d30440016a10ca9a6088002d4e11534c11000789ba2a69822000f107454d30440016a704a9a6088002d4616434c11000788aa4869822000bc18290d30440016a30aa1a6088002d4617324c110005c8c26649822000b51854c930440072e10eaa44088003545cd5388110226b0b92a51022045d30501d120440072c90ea9240880034c1d47448110004b843aa890220018f0865cd20440016c30a3124088002e86106248110005e0c18c49022003b628754920440076c10ea924088002d8a195248110005b0432a49022000b63845492044001e46e8a924088003c81d15248110005b1c1aa49022000b61859092044001e42a92124088002f060e4248110005b0c2a849022000b61858c92044001743091924088002d86153248110
  | 1 => 0xae9886c6a91230b9c96590f422441ec36e8a96840083d86dcd549089b83cc7b9aa92113687e1d5498e422450fc12a931c8448a1d82552639080143900aa4c7210021761c5098e420050ec20a131c8400a4d821426390801c2aa9884c721002876135358e420050ec24eab1c8400a4d82d51639080149f04aa2c721123831095458e420042ec38a0b1c8400a1d84141639080149b04282c7211370798d75d0e4226e0f31aeaa1c8448a2c82505655089185ce4b2c86a10020fe1d6510d4226c1ec36e6aa0840083f865d5431088b0790eaa2c0210020f61f52993320041ec38a13266400a1d8314264cc80145b04284c9990028760e755933226e0e39aeab26640083d87d4964cc80107b0e282c9990028760c505933200516c10a0b266448a1c8359154cc80183ac9b9aa9990020f61f53992320041ec38a13246400a1d83142648c80145b04284c9190028b60a755923224616392eab24640083d87d4d648c80107b0e282c9190028760c505923200516c10a0b246448a2c82591548c80185ac9b92a9190029c60061595320043b43e20b2a6403878805d9544c80507d0fb22a899002c3e095410d3200587c1aa8212640087587997614c80146b0932ec2990021de1d65d85320051ac24ebb0a6400a3584d4f614c80146b09a96c2990021d61c50d85320051ac20a1b0a6400a5583143614c8014cb04286c29900a0f613765503229547426ec9906400a4f865d5320c80189eecbaa6419003511c5754c83200527c32a89906448e0c64551320c8a5918e8992c01912f0dc437458e5025e1a886e8b1ca04a83f87593439400189ac6b94872811b0dc437458a502361a886e8b14a04583f87593429400189ae6b148528003075d163cca5000616ba2c5194a00083f845d932940010eb0db8a65280020fe11760ca5000626bb264194a04d83d86dcd54d009107b0db92a9a000e1721d6354e4000617b2ce521c800386c87589529000183ecb39c85200028d610755864001d38402a8b0c8000a3584d4d619000146b09a92c32012a0fa1b735514022c1f436e4aa2800383c865d543500070790cbaa84a000a0f61373594400141ec26e4b288000a1d84d4a631000143b093aac620002876135258c400041ec36e8a988000c1f7458d531000185acb39486200032358e7290c4000516c26a73108000a2d849d5621000145b09a9ac4200028be1153588400041ec36e8a908000c1f7458d521000185ee8b12a4200030759673908400064739ac52108000a3584d4d611000146b09a92c2200020f61372597300141ec26ecaa6600091d84dc953cc00107b09bb2a59800e0f21d645523001c3643ac4a946000a35841d5618c00146b09a9ac3180028d61352586300041fc22e5b2a6000a1d83d53644c09743b063aec8980028b60875d913025c1f43ea7b226000
  | 2 => 0x443f5200a83f170e609064490000000006c000000037910001310000015465488004a1360011b2c03d0200031083038ce4049f18c0035cf1000003180000000000343644e1e138200000010432829000d80008a49490000000011e000d6114000000000097000f903000001292741200000000da0c1270186f4cc0d1408d448390c45f2d06007ca146468340c70002d44521029353a9063009b48cdd0000045467000000000012c872b1320004d10c0029c000e11a000022807c000000bce92d87b100541d8d52189e11d14260ed168af4b4812b4131582e1fcae03c171e8e40010c2a400474104587e14c0b00000288fe0006d1e4c3248bd128890543b09c0038c000000034c7d1780000085149000dca3000a61b8df000ab00000000001d0000e8140100032c050d86941c1d00000000b30d400058773b8c91852b0009c4a8074dceb415080680000000000a8000c1000aa044d42f00000000000f300000198003d033000e800000000412311c0600000000210000000023c00000282f8824b826000000000000000000000000047d0b13c003d803348cd22cfc0000000000000a40000033c00000ba2d43e4d01e2c80008c00344593d488000f200000000004387143c00258000005d00000424000006c00022000b83880036c0044c1c12095434003b0001cc2c025301ac21268dc00000004a530903408000004c39c003800000093000620006a000000000012400000e12e45b00000000b1000003dc942fc461d470000003ec004bcff000003200000000394253c10a001261088e314000003c000000c8000ac1915cf814458000002647200091000b7000bb000203bccc3e917000000000000000000004612c000020e0180402120001400000382800060000c00020100402000080000000000c0402040000e0303000020106804080000004000d0380006050080006030201c0000008040604000000a04008080000048000807048100401000040002018240002000000e000200c0400000103801000000000001360f61f41d8d542ce1aba621b1aa800c4f635ca635509107b0fa0ec4aa1670d5d310d895401e38302e3302a80083f875906454c0183f06ba6c4a98030720d74d89530061aba621b12a64d83d86dd153d0c0107b0db92a9219230b98b725524324517c3aa9314864da2f835526290c9b45b06aa4c5218028b2015498a4300436c38a13148600a2d841426290c0149b06284c521803895531098a4300516c26a4b148600a2d849d56290c0149b07aa2c52180293e0d5458a4326f0621aa8b14860086d871416290c0145b08282c5218029360c5058a4326d0e41a82b2a864883d86dc95410c950790eaa2c0218020fe1d641915200617c12e9b1aa400c2c825d3635480186
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x889292e78a70c106a8ea1a0185800000a602c02051030ca1800a70040b65c805526290c0120d932015498a430040765c80552639080120d922015498e4200550640715d5320c80101c966137254d300040b25984dcd52480019107020d6455110006481c0825915444001520905527290d102544c261545c0434400151090552739091022c4c261545c042440014c0964c9700c910004c46508654d3044095910871d1534c110004c46538254d304400151097552434c11001c5425d8550d304400132194219524811022e4821c74549204400132194e0d52481100054825d549092044007160976154248110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x83a460000a201801220c001480d10e041ac8aa22000a4068c70209645511000424350482a93948688002501a3241549ca4344001088d4120aa4e721220009406889055273909100042214eca10ca9a6088002110a76538254d304400109053b28432a4902200084829d94e0d5248110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x6
  | 3 => 0x1
  | 4 => 0x94e
  | 5 => 0x3
  | 6 => 0x8a
  | 7 => 0x8e
  | 8 => 0x4
  | 9 => 0x5
  | 10 => 0x98a
  | 11 => 0x98e
  | 12 => 0x128a
  | 13 => 0x128e
  | 14 => 0x150a
  | 15 => 0x150e
  | 16 => 0xca
  | 17 => 0xce
  | 18 => 0x9ca
  | 19 => 0x9ce
  | 20 => 0x12ca
  | 21 => 0x12ce
  | 22 => 0x168a
  | 23 => 0x168e
  | 24 => 0x10a
  | 25 => 0x10e
  | 26 => 0xa0a
  | 27 => 0xa0e
  | 28 => 0x130a
  | 29 => 0x130e
  | 30 => 0x180a
  | 31 => 0x180e
  | 32 => 0x134a
  | 33 => 0x3ca
  | 34 => 0x3ce
  | 35 => 0xcca
  | 36 => 0xcce
  | 37 => 0x15ca
  | 38 => 0x15ce
  | 39 => 0x170a
  | 40 => 0x170e
  | 41 => 0x40a
  | 42 => 0x40e
  | 43 => 0xd0a
  | 44 => 0xd0e
  | 45 => 0x160a
  | 46 => 0x160e
  | 47 => 0x188a
  | 48 => 0x188e
  | 49 => 0xd4a
  | 50 => 0x58a
  | 51 => 0x58e
  | 52 => 0xe8a
  | 53 => 0xe8e
  | 54 => 0x178a
  | 55 => 0x178e
  | 56 => 0x18ca
  | 57 => 0x18ce
  | 58 => 0xeca
  | 59 => 0x104a
  | 60 => 0x98956
  | 61 => 0x128956
  | 62 => 0x9c956
  | 63 => 0x12c956
  | 64 => 0x1a0a
  | 65 => 0x1a4a
  | 66 => 0x1a8a
  | 67 => 0x14a
  | 68 => 0xd4992
  | 69 => 0x409
  | 70 => 0x1609
  | 71 => 0xd5512
  | 72 => 0x104b
  | 73 => 0xec9d2
  | 74 => 0x589
  | 75 => 0x1789
  | 76 => 0xed692
  | 77 => 0x104c
  | 78 => 0x104a12
  | 79 => 0x105812
  | 80 => 0xcc3d2
  | 81 => 0xcc3d6
  | 82 => 0xccd
  | 83 => 0x104412
  | 84 => 0x105612
  | 85 => 0x104592
  | 86 => 0x105792
  | 87 => 0xb89
  | 88 => 0x1849
  | 89 => 0x138e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 70
  | 6 => 1120
  | 5 => 1453
  | 4 => 313
  | 3 => 24
  | 2 => 10
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
  | 7 => packedAt gbK7 (1981+((h/23+packedAt gbK7 (1820+(h % 23)*7) 7) % 85)*8) 8
  | 6 => packedAt gbK6 (45543+((h/373+packedAt gbK6 (41440+(h % 373)*11) 11) % 1479)*12) 12
  | 5 => packedAt gbK5 (75068+((h/484+packedAt gbK5 (69744+(h % 484)*11) 11) % 1744)*12) 12
  | 4 => packedAt gbK4 (19403+((h/104+packedAt gbK4 (18467+(h % 104)*9) 9) % 499)*10) 10
  | 3 => packedAt gbK3 (1720+((h/8+packedAt gbK3 (1680+(h % 8)*5) 5) % 29)*6) 6
  | 2 => packedAt gbK2 (822+((h/3+packedAt gbK2 (810+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3fff870383f83fffc3f80ff01f04e93e09f673
  | 1 => 0xc1e07803fc3fc3c0fc3ff07fe01b56d836cb9c
  | 2 => 0xfe007ffc003ffc00ffc0007fffe398e1c70c1f
  | 3 => 0x7fffffc00000ffffff8000fc1f01f80fe0
  | 4 => 0x7fffffffffff0000000000ffe001fff000
  | 5 => 0xffff8000000000000000000000fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x221000080480442404821104200000a005231
  | 1 => 0x41431001a41a42864412a1254209425812c294
  | 2 => 0xb4042b640024a808aa80424a9c6298a0c50c0a
  | 3 => 0x10084daa4a800010b3254e0084b41d01680d40
  | 4 => 0x211076d37337333c0001840308dfe001bfa000
  | 5 => 0x399e00e0620622202206080c10fffff4000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafeeaeee0feeaeeeafeeaeee0feeaeeeafeeaeee0feeaeeeafeeaeee0feeaeeeafeeaeee0feeaeeeafeeaeee0feeaeeeafeeaeee0feeaeeeafeeaeee0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_16029
namespace PEqualNP.Outside.L_meta_16029
open PEqualNP.Outside.L_meta_16029.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 6 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_64 : Interval s1Atlas 3 64 20 := block_range (n:=20) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 84 := (concat bs1_3_0 (concat bs1_3_32 bs1_3_64))
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
theorem bs1_4_160 : Interval s1Atlas 4 160 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 186 := (concat (concat bs1_4_0 (concat bs1_4_32 bs1_4_64)) (concat bs1_4_96 (concat bs1_4_128 bs1_4_160)))
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
theorem bs5_3_0 : Interval s5Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 6 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 66 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 42 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 10 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 24 := bgb_3_0
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
theorem bgb_4_288 : Interval gbAtlas 4 288 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 313 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 bgb_4_192) (concat bgb_4_224 (concat bgb_4_256 bgb_4_288))))
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
theorem bgb_5_1440 : Interval gbAtlas 5 1440 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1453 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864))) (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))) (concat (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))) (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440))))))
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
theorem allgb_6 : Interval gbAtlas 6 0 1120 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafeeaeee0feeaeeeafeeaeee0feeaeeeafeeaeee0feeaeeeafeeaeee0feeaeeeafeeaeee0feeaeeeafeeaeee0feeaeeeafeeaeee0feeaeeeafeeaeee0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276809440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_16029.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,4]⟩,⟨.and,[0,5]⟩,⟨.or,[0,1]⟩,⟨.and,[2,4]⟩,⟨.and,[2,8]⟩,⟨.or,[8,9]⟩,⟨.and,[3,11]⟩,⟨.or,[10,12]⟩,⟨.or,[7,13]⟩,⟨.or,[6,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276809440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276809440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_16029

open PEqualNP.Outside.L_meta_16029 in
theorem PEqualNP.Outside.L_meta_16029 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276809440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276809440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
