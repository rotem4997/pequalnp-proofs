import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15965.Model
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


end PEqualNP.Outside.L_meta_15965.Model

namespace PEqualNP.Outside.L_meta_15965
open PEqualNP.Outside.L_meta_15965.Model
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

def SBf (j : Nat) : Nat := [5, 5, 6, 4, 5, 7].getD j 0

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

end PEqualNP.Outside.L_meta_15965

namespace PEqualNP.Outside.L_meta_15965
open PEqualNP.Outside.L_meta_15965.Model
def s0K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x400003102006f32bc6570cb6194c32
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x2390a32
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
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
  | 3 => packedAt s0K3 (79+((h/1+packedAt s0K3 (75+(h % 1)*4) 4) % 10)*4) 4
  | 2 => packedAt s0K2 (27+((h/1+packedAt s0K2 (26+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffffffffffffffffffbfc7fffe3fff1ff
  | 2 => 0xfffffffffffffffffffffffdff8ffffc7ffe3f
  | 3 => 0xebff0f3ff8e0fcc
  | 4 => 0xf3fff03fff00ff0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xfffffffffffffffffffffff4070220a092a0d5
  | 2 => 0x20864414425462a
  | 3 => 0x1512e8669086b4c
  | 4 => 0xe248eb92418db0
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 30 s0Pos s0Neg, 0xfcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15965
namespace PEqualNP.Outside.L_meta_15965
open PEqualNP.Outside.L_meta_15965.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xd431
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | 3 => packedAt s1K3 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s1K3 (17+((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffc0fffffc0ffffffffff80ffff1ffe3f
  | 2 => 0xe03f01fff03f03ff0f81e0fc0fff07c0ecb3cc
  | 3 => 0xffc001fffffffffff001ff000ffffffff0c3ff
  | 4 => 0x1ffffc003fffffe00000ffff800ff03f0
  | 5 => 0xfffffe00000003fffffffffff0000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2284100460821040118a211462884a4a051615
  | 2 => 0x498a72c8a39455cb06a8e8d8a5b946866cb2cc
  | 3 => 0x8512a5510528c29560415a4109529534b0c16a
  | 4 => 0x162cd9a24a0e9b66bb6c10924e6ce218df03b0
  | 5 => 0x1830e1c38c30e3b8cc719ce380708420fae800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafa00aa00faaaaaaafa00aa00faaaaaaafa00aa00faaaaaaafa00aa00faaaaaaafa00aa00faaaaaaafa00aa00faaaaaaafa00aa00faaaaaaafa00aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15965
namespace PEqualNP.Outside.L_meta_15965
open PEqualNP.Outside.L_meta_15965.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x28e0000ab4882801860010000c80bf42bd42de32dc32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x600c074248100002280266aa3a15594632c6a10652d52d069ca518e55043196a9081355110298a4985514530
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (212+((h/4+packedAt s2K4 (192+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s2K3 (282+((h/3+packedAt s2K3 (270+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffff83ffffffe07ffffffff03fffff1ff1ff
  | 1 => 0x3f03ffc1ffc1fff878383e0ffc3fc1fe94e73
  | 3 => 0xfc003fffe0ffe0fff803fc00fffc3fe0f18f9c
  | 4 => 0x3fffff0000fffffc0000ffffc000fe0fe0
  | 5 => 0xffffc000000000ffffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x104000880008000008840422200444840210a5
  | 1 => 0x48a65910ca5138658321a3445642a85a694652
  | 3 => 0x292aaa2146a309aab042e9089aa83342b18b18
  | 4 => 0xb2cd344a943a52d35de84212ed33018cde0de0
  | 5 => 0xc30e387318c39cfc6673739c0e222210fde000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaee88aa88eeaaaaaaee88aa88eeaaaaaaee88aa88eeaaaaaaee88aa88eeaaaaaaee88aa88eeaaaaaaee88aa88eeaaaaaaee88aa88eeaaaaaaee88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15965
namespace PEqualNP.Outside.L_meta_15965
open PEqualNP.Outside.L_meta_15965.Model
def s3K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*4) 4
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (5+((h/1+packedAt s3K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 2 => 0xebfc1f3fe03f8f1c
  | 5 => 0xf3ffe03fffc00fe0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 1 => 0x2088281109124486
  | 2 => 0x1523506a42a52b18
  | 5 => 0xe0a1ab493064ec0
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 39 s3Pos s3Neg, 0xeaeaeaeac8c8c8c8eaeaeaeac8c8c8c8eaeaeaeac8c8c8c8eaeaeaeac8c8c8c8eaeaeaeac8c8c8c8eaeaeaeac8c8c8c8eaeaeaeac8c8c8c8eaeaeaeac8c8c8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15965
namespace PEqualNP.Outside.L_meta_15965
open PEqualNP.Outside.L_meta_15965.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x9d43
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
  | 0 => 0x7ffff83ffff83f07fff07fff83fffc0f39f3f3
  | 1 => 0x87c1ffc3e0fffff8707f8783fc3c1fffd64c9f
  | 2 => 0xf801fffc00ffc3ff807ff803ffc01ff0e78f1c
  | 3 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x800880400040008090088880444422009131
  | 1 => 0x2112910909522128342485112428894c524486
  | 2 => 0x12a52290d2a406538859502aca8152a2a58b18
  | 3 => 0x5539c42a9836ab9d5d0c4443733380c4f80ec0
  | 5 => 0x663187331cc733e66e6e667062220308ff6000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeaeac8eac8eaeaeaeaeac8eac8eaeaeaeaeac8eac8eaeaeaeaeac8eac8eaeaeaeaeac8eac8eaeaeaeaeac8eac8eaeaeaeaeac8eac8eaeaeaeaeac8eac8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15965
namespace PEqualNP.Outside.L_meta_15965
open PEqualNP.Outside.L_meta_15965.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x360000026a000000895875a0c6202a7cb111e100020000b8000a4a000200000000000000b13235438021000048b2078c8014003000000900480041c3434c0000000004a7428000000004e000010002080070800200040c001ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x11c004c00bc00005ca000208cf80001888840014d3c00e00000b40008015c0000ed6c00cc00f0d80464011138952909301c000000dc0000c00018c93400a515484839780090b800ac25600000000169200155589d74e48400300070b11800d4000000110461458045000098a800006d70f400507c68012c00000058000c3c0150000000540001647400d0002834c57d0c782c8000fd418414000000e9240800000010020800000004000402020004000a0002020010000000060a08020a053e5390e7aa121cf94c43cf298873d5010ef4a0215e540429f2a4653d548caf4a1195e542329faa2653c544cabca720d754e41b7a92836c52507388798cf952319eaa4633f544c678a898e710d31b7a92636c524c6f6a098de141319faa2433c544867ca810cf55021af298435d53086f4a010de540219f29e813d54902dca5205b54a40afa9a815c535033ea6a04f14d40ce29a811c5350376a0a04f95040b7290816d521027ea9984f153309f2a4613d548c33887185b94a30b6a94613f544c278a8984f950309eaa0619c430c2dca4185b54830bb2886175510c35c87906b10f20d7a0641ad40c827ca9104f55220b6a9441b9408837280906b90d20d621a41eb504835e80907a90120d6a0241e9404835280907acc120f4182413e540827aa8105b948209f2a4213d54842dca5085b54a10f490421e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2200a2652441870018000c01601e0000004843a00006a200a0c12010401a696014941c610c504c61d6510c30c510d510c28c6350320a618d40882986350120aa58043482a96490120a318d40482c86350120e2d8d40482a86350120e218d40482886350120aad9330482a9640c120e210c30482e1610c1208718d54843295448210
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x14004897610c304834021ac218241421cd5448210
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s5K5 (841+((h/15+packedAt s5K5 (736+(h % 15)*7) 7) % 88)*7) 7
  | 4 => packedAt s5K4 (2937+((h/33+packedAt s5K4 (2673+(h % 33)*8) 8) % 157)*8) 8
  | 3 => packedAt s5K3 (840+((h/7+packedAt s5K3 (798+(h % 7)*6) 6) % 33)*6) 6
  | 2 => packedAt s5K2 (150+((h/1+packedAt s5K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf03ff07ffffc3e0f878ff0fe3fffe07e0733f3
  | 1 => 0xffffff83f0fffff007f0ffffc381fffc39fc9f
  | 2 => 0xffc1fffc00ffc3fff800ff0ffc01ff83c1cf1c
  | 3 => 0x1ffffff0003ffffff000ffffe0003fe0fe0
  | 4 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x14851110a8226202c109389224a5212a031131
  | 1 => 0x21082209014800500290412441084a50186486
  | 2 => 0x429545206a9226a5c8089a8aa815950ac18b18
  | 3 => 0xb28884a4018893914a2000d125806116c0ec0
  | 4 => 0x8c310e738ce333ce674cecc020611863b7f000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfec8eac8fec8eac8fec8eac8fec8eac8fec8eac8fec8eac8fec8eac8fec8eac8fec8eac8fec8eac8fec8eac8fec8eac8fec8eac8fec8eac8fec8eac8fec8eac8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15965
namespace PEqualNP.Outside.L_meta_15965
open PEqualNP.Outside.L_meta_15965.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x860385400201c8e0056000c7a004e00000084500200864c260e7e6c00784880000000180000584a8a000000720036665a0000000000743c441e32223a5e0400008c00106a462c0082400000240000001600006e00765c0064000000000070421468000a7c52121a06003e62002e3488003000002800000000002a0000000000100040010008001000820400081000808000017fd5005fe54017f55005fc54017fd4c057f53017f94c05fd53005f54c05fc53007fd0c01fe43006f90c01fd43007f10c01bc43017fd4803fe52017f54803fc52007fd0803fe42007f50803fc42007fcc803fe32007f4c803fc32017fd44057f51017f94405fd51005f54405fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc3100ffc8401fe21007f48403fc21017fd4005fe50005f94005fd50017f140057c50007fd0001bf40007f90001fd40006f50001fc40007fcc001fe30007f4c001fc3000ffc8001ef20007f88001fd20007b48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x9a4000db54d20057d8a690003ef4348001f721a4000eb90d20007da8690003ec4348001d621a4000fbd8520007dcc290003ed6148001f630a400afbd4520056dea29002bee5148015f6a8a4000db54520057d8a290003ef4148001f720a4000fb50520007d88290003ef3148001f718a4000fb4c520007d86290007ef604800377b024001fad8120057dea090013ee5048009b7282400afb54120027d8a0900136c5048001f7a024000ebd0120027dc8090003ed4048001d6a024004fb10120007de6090013ee3048001f69824004fb0c12001dfecb8800afe65c4007bf32e20029f9971004dfacb8800f7d65c40013eb2e2003bf1971001dfec98801afe64c40017eb262003bf1931001dfec788002fe63c40017eb1e2003bf18f1004efea7880037d53c4001df21e2000ef10f1001dfec588006fe62c40017eb162003bf18b1001efea38800ff651c4007bea8e2009fd54710006eaa38800ff631c4001fa98e2004df94310026f8a188003bf40c4001dea062000fbc8310007da4188012ff6584009bfb2c20049fd9610015fccb08022fd65840097e32c2004df19610024f8cb08012ff648400d7f3242004ef992100057cc908002fd6484009deb242000af59210025f8c908012ff63840017f31c2000bf58e10025f8c7080237f5384001bea9c2000ef90e10007788708012ff62840037f3142004fb98a1000ddcc508002fd6284009f6b142000bb58a10025f8c50801efd6184011bfa8c2000df54610025fcc1080137e5084009be2842004efd02100277a8108013ef2084009fd1042004fb48210007f24108003e92084009fb8842003fec421003dfeca880037f65440013fb2a2002bf9951003dfaca8800afc654400fbe32a20029f19510005fec88801afe64440017eb222006bf19110005fec688002fe63440017eb1a2000bf18d1003efea6880037d5344001df21a2000ef10d10005fec488006fe62440017eb122001bf1891003efea28801ff65144001bea8a2007fd54510006eaa288003f63144001fa98a2004df94110026f8a088003bf4044001dea022000fbc8110007f44088003ed2044001fc9022000fa4811001ff62088013f610440097fb282002bf99410026fcca0800a7e650400b7eb282004df59410004faca08012fc65040097fb202006bf990100277cc808002be64040017eb202004ef590100057ac808012fc64040097fb182000bf98c10027bcc608002de63040017eb182004f758c10005bac608012fc630400bbfa982000df54c100077c8608003bc43040097fb102001bf98810027dcc408006ee62040017eb102004fb58810005dac408012fc62040077f3082003dfd441001efaa208012fe6004009bf2802004df140100277e8008013bd4004009f79002004fb48010027ee2008013fa1004009fa8802003fe44010
  | 1 => 0x3bf404c001dea026000fecc130027bc6098012ff650c0057f3286004df99430014fcca18036fd650c009beb2860009f59430025f8ca18012ff640c00d7f3206004ef990300057cc818002fd640c009deb206000af59030025f8c81803efe630c01bbfa986000df54c30007be861803bbe430c01dde2186000f710c30007388618006fe620c009f73106001bb98830005fac418013ed620c00176b106004bf1883001dfcc218013f6610c0017b3086000bf58430027eac218002f5610c01bbfa886000df54430025fcc0180137e500c009be2806004efd00300277a8018013df300c009fd1806004f74c030007f26018007ef65c8003f732e4001db9972000fdacb900076d65c8003f632e4001fbd932000fdcc990007ed64c8003f6326400cfbd5320067dca990033ed54c8019f62a64001fbd8f2000fdcc790007ed63c8003f631e400cfbd4f20066dea790033ee53c8019f6a9e4000db54f20067d8a790003ef43c8001f721e4000eb90f20007da8790003ec43c8001d621e4001fbd872000fdcc390007ed61c8003f630e400cfbd4720066dea390033ee51c8019f6a8e4000db54720067d8a390003ef41c8001f720e4000fb50720007d88390003ef31c8001f718e4000fb4c720007d86390033ef50c8009f72864004db94320067daa190013ec50c8009b62864000fbd03200075e8190013ee40c8001f6a064000eb50320027d88190003ef30c8009f71864000fb4c320027d86190012ff65880057f32c400bbf59620025f8cb10012ff648800d7f3244004ef992200057cc910002fd6488009deb244000af59220025f8c910012ff63880017f31c4000bf58e20025f8c71002f7f5388001bea9c4000ef90e20007788710006fd628801576b144003bf98620005fac31002f7f5188001bea8c4004bf98220026fca1100137c5088009dfa044004ef50220027de4110007fb2088009fc104400abfd9520006feca900027f65480057f32a400abf59520015f8ca9002b7c65480053e32a4000bfd9120035fcc890002fd644800d7e3224000bfd8d20005fcc690002fd63480017e31a400adfd4d20006faa690003be4348001de21a4004bfd8920057dea490007ee5248015f6a924001fb14920007de8490007ee4248001f6a124001fb10920007de6490007ee3248001f69924001fb0c920005fec29000efc6148015bfa8a4000df5452000fde4290003ee2148001f690a4001fb0852000dfec0900137e5048009be2824000efd01200077a8090007fb2048009f71024004fb0812000ff0409002bef6548001b7b2a400afb99520057daca9002bec6548015b632a4000fbd9120007dcc890003ed6448001f6322400afbd5120057dca89002bed5448015f62a24000fbd8d20007dcc690003ed6348001f631a400afbd4d20056dea69002bee5348015f6a
  | 2 => 0x40005fec4a0006fe62500037e3128000efd09400a77c84a0003bd4250029de2128000bfd854001df8c2a00577f5150001bea8a8000efd05400077c82a0003bd4150001de20a8004df94140026f8a0a001bfb4050009df2028015efd95400067ecaa0057be655002bdeb2a8015ef195400ae78caa0003bf6350001cfb1a8000ef98d400077ac6a0003bc63500015e31a8000e718d4000538c6a0057bf535002b9fa9a8015ef94d400af7aa6a00033d535002bde29a8000efd89400a77cc4a0003bd6250029de3128015efd49400a77ca4a0057bd5250029de2928000efcc9400a77c64a0003bd3250029de1928000efd85400077cc2a0003bd6150001de30a8015efd45400ae7ea2a0057be515002bdea8a8000cf545400af78a2a0003bf3150001df18a8000ef4c5400077862a0053bf2150001df10a8000ef485400a77842a0003bf6050001ddb028015efd41400277ca0a00133e505002bdea828004ef1414002678a0a0053bf2050009de1028004bfd9440015fcca2004afd65100097e3288006bf9904009d7cc820002fe63100017eb188012dfd4c40006faa620003be431000dde2188001bf98840027dcc420006ee62100017eb108004fb58840005dac420012fc62100077f3088000bf58440096fea2200037d51100097f3008004df94040026f8a020013bf4010009fd2008004ef50040037f2802003eff65cc0057f32e600fdf99730014fccb9803efd65cc001beb2e60009f59730015f8cb98002ff64cc01ddfb266000afd9330035fcc998002fd64cc00d7e326600eef1933000578c99803f7f53cc01fef29e6000df54f3007fbaa7980035d53cc01ddf21e600eef10f3000dfcc598002fd62cc0037e3166003bf98730005fac39803f7f51cc001bea8e6000f7cc730007ba63980137e50cc009be2866000efd03300077a8198012ff658c009bfb2c60049fd9630015fccb18046fd658c0097e32c6004df19630024f8cb18012ff648c00d7f3246004ef992300057cc918002fd648c009deb246000af59230025f8c918042fd638c023bfa9c6000df54e30007be8718003be438c001de21c6000f710e30007388718006fe628c009f73146001bb98a30005fac518013ed628c00176b146004bf18a3001dfcc318002fd618c023bfa8c6000df54630025fcc1180137e508c009be2846004efd02300277a8118013df308c001fd9846010bfd9530006feca980027f654c0057f32a6010bf59530015f8ca980437c654c0053e32a6000bfd91300077ec898002bf644c00d7f3226000bf59130035f8c898003bc644c0015e3226010dfd4d30087bca6980037d534c021eea9a6000d754d300077c8698003bc434c0017fb126001bf9893000df8c498002ff614c0077e30a6010dfd4530006faa298003df314c001ee98a6004df94130026f8a09800
  | 3 => 0xf3224200bf59121035f8c890803bc64484015e3224200bfd8d21005fcc690802fd63484017e31a4219dfd4d21006faa690803be4348401de21a4203bfd892100dfec2908677f5148401bea8a4201fdc852101fdc429080fec2148403fa10a4200bfd8121025f8c0908677c5048403f79024204dfd9250026fcc9280133e6494009beb24a004cf59250026f8c9280137f6394009bf31ca004df58e50004fac7280137c6394001bfa1ca000df90e500067c87280037d4394001be21ca000cf10e50026fec5280137e6294009b7314a004df58a50026dac5280137c6294001bfa14a018df90a50006fa85280637c4294001bf994a018df8ca50006fa65280637c3294009bfb0ca004df98650026fac3280027d6194009be30ca000dfd0650006fc83280037d4194001be20ca000dfcc650006fc63280037d3194001be18ca018dfc8650006fc43280037d2194031be10ca004df98250024fcc1280137a6094009bf904a004df08250035fecba000afe65d000dbf32e80029f9974009dfacba001b7d65d00013eb2e8006bf1974009f7ea9a001bbe54d0027deaa68006ef15340005fcc7a0002fd63d0027bfa9e8000df54f400377e87a0003be43d0001dea1e8006ef10f4000dfcc5a0002fd62d00037e3168006efd0b400bf7c85a0003bd42d000dde2168003bf98740005fac3a004f7f51d0001bea8e8006efd07400077c83a0003bd41d000dde20e8004df94340026f8a1a001bbf65d0027df32e8013cf9974009f7acba00033d65d000dde32e8006efd8f400077cc7a0002be63d0001deb1e8006ef18f4009f7ea7a004f3f53d0027df29e8013ef54f400067aa7a004fbc53d000ddfb168017ef98b400077ac5a001bbc62d0027dfa968017ef94b4009f7aa5a005fbc52d0001df9968017ef8cb400077a65a005fbc32d000ddfb0e8000ef987400077ac3a001bbc61d0027dfa8e8013cfd474009f7ca3a004fbd51d00019ea8e8013ef147400077e63a0003be31d0001de98e8000ef0c7400bf7e43a0003be21d0001de90e8017ef0874009f7ea1a0013be50d00099f2868013ef5434002778a1a00133c50d002fdf9068004ef08340025fecb2000afe659002d7eb2c8004bf196400adfac920056bd64900017f31c8000bf58e400b6fea7200037d5390001df21c8000ef10e4000dfcc520013ee6290003773148000bf58a40027dac520002ed62900097e3148003bf98640005fac32005b7f5190001bea8c8004bf98240026fca1200137c5090009dfa048006fed02400adfecaa00037f65500013fb2a8002bf995400adfacaa000afc655002bbe32a80029f195400af7ea8a0057be545002bdeaa28015ef15140005fec6a0003df63500016fb1a8000bf18d40007b8c6a0002dc635002bbfa9a8000df54d400077e86a0003be4350001dea1a8000ef10d
  | 4 => 0x8037d5350401df21a8200ef10d41005fec4a0803ef625040177b128201bf9894100df8c4a0803ec6250403763128200efd09410077a84a08877f5150401bea8a8206fdd054101f7c82a0802ff60504097e3028221df1414101dfeca2080afe6510407bf32882029f994410fdfaca2080f7d65104013eb288203bf19441035fcc820802fe63104017eb18821fdfd4c41006faa620803be431040dde2188201bf98841005fac42080efc6210441df2108206ef1084101dfcc22080f7f5110407bea888203efd044101fec822080fbd411040dfaa088204bf98041005fac02087f7c50104397fb2e6202bf997310e6fccb9880a7e65cc4397eb2e6200df59731004facb9880afc65cc4017fb266206bf99331005fac99881afc64cc439bfa9e6200df54f31007be879883bbe43cc41dde21e6200f710f31007388798806fe62cc4017eb166201bf18b31007be6598803dd32cc439bfa8e6200df54731025fcc198802fd60cc439be2866203bfd9631015fccb1880f7e658c4053f32c621ebf5963101efacb188027d658c4077e32c6203bfd9231035fcc91880fbe648c4015f3246200bf5923101f7ac918802bd648c4077e324621dbf58e310f6fea7188037d538c401df21c6200ef10e3100dfcc518802fd628c4077e3146203bf9863101efea31880f7d518c407ef98c6200fdcc631025fcc118802fd608c43dbe284621dbfd9531015fcca988777e654c4053f32a621dbf59531006faca988027d654c4057e32a6200bfd91310077ec898802bf644c40d7f3226200bf59131035f8c898803bc644c4015e322621ddfd4d31006faa698803df434c401df21a6200ef10d31007b886988039c434c4017fb126200fbd8931005dec498806fe624c4037e3126200fb1893100dd8c498803df324c401ee992621ddfd4531006faa298803f7314c407ef18a6200bfd8131025f8c0988777c504c4077fb286202bf9943101efcca1880a7e650c4377eb286203df59431004faca1880efc650c4077fb206206bf99031005fac81880efc640c4397f318621bdfd4c31006faa61883bbe430c41dde2186201bf98831005fac41880efc620c4077f3086203dfd443101efaa21880fdf310c407fb1886203f74c431007ea6218812fe600c4017eb00621bdf1403101dfecb1080afe6588407bf32c42029f996210d5facb1080f7d65884013eb2c4203bf1962101dfec91081afe64884017eb244203bf1922101dfec710802fe63884017eb1c4203bf18e210d6fea7108037d5388401df21c4200ef10e2100dfac510803ef4288403f62144200fbcca2100fd8651080efe6188407bfa8c4203df5462101fde4310807f72188407fa10c4204bf98221005fac11086b7c5088403f79044219bfd9521015fcca90866fd65484057e32a4200bfd91210077ec890802bf644840d7
  | 5 => 0x844315f7ea2218af3f5110c57df288862bef5444315f78a2218abbf2110c55de108860eefd80430077cc021803bd6010c015eb00860eef1804315f7ea0218afbe5010c57dea80862bef1404315e78a0218abbf2010c55de1008606bfd9742015fccba10a6fd65d080d7e32e8401bf99342005fcc7a1002fd63d0853bfa9e8400df54f420077c87a101bbc43d08037eb168401ef90b4200fdc85a1007bc42d08077f30e8400bf5874214efea3a1007ec21d08097f3068400bf5834214ef8a1a1007ef20d08517fb2a8402bf99542145facaa100afc65508037fb228400bfd8d42005f8c6a10a37f5350801bea9a8400ef90d420077886a1006ff625080df7a128401ef9094200f7884a1007ec42508017fb0a8403bf18542146fea2a1002ff60508097e3028428df1414200fde40a109eff65cc8057f32e6427df99732014fccb9909efd65cc801beb2e64009f59732015f8cb99002ff64cc80d7f3266400bf59332035f8c999006fe63cc84fbfa9e6400df54f320777c879903bbc43cc8037eb166401f78cb3200fdc6599007dc32cc8077f30e6400bf5873213efea399007ec21cc8097f3066400bf5833213ef8a199007ef20cc84d7fb2a6402bf99532135faca9900afc654c8017fb226400efd91320057ec89901afe644c8017eb226406bf1913200778c899002bc644c8037fb1a6426dfd4d32006faa699003be434c801de21a6401bfd8932007de6499007de324c803ee1926401fb0c932005fec29900efc614c84dbfa8a6400bfd8132025f8c09909b7c504c803f79026400dfd9151006fcc8a88037d6454401be322a200dfd8d51004fec6a88037e6354401beb1aa200df18d51006fe86a88037e43544019f21aa200df50d51006f886a88033c4354401bfb12a225df98951006fac4a88977c6254401bfa12a225df90951006fa84a88977c4254401bf992a225df8c951006fa64a88977c3254405bfb0aa2029fd8551016eec2a88977f2154407be10aa200dfd8151006fcc0a88037d6054401be302a2049f1815112efe40a88977c205440d7fb2e8202bf99741125facba081afc65d04017f31e8200bf58f41126fea7a08037d53d0401df21e8206ef10f4100dfcc5a0802fd62d04037e3168206efd0b410077a85a08937f51d0401bea8e8204bf98341005fac1a08937c50d04077fb2c8202bf9964101efccb2080a7e65904457eb2c8203df59641004facb2080efc65904437eb248200bf98e4101fbcc720802de63904017eb1c8203f758e41005bac72088b7f5390401bea9c8200ef90e41007788720806fe62904017eb148203bf18a4111f7c852088fbc42904077f30c8203dfd464101efaa32080fbf419040dfba0c8204bf98241005fac12088b7c50904437fb2a8202bf9954110dfacaa080afc65504017fb1a8200bf18d4110efea6a0
  | 6 => 0x8060008008010008000008018000008000008068010030000020010048000040000000008008000018058010000020008000018018000018010040010078000037f6454c019fb22a600df99153006fac8a98037c6454c019e322a602dfd8d53014fec6a980b5f6354c01bfb12a630df98953006fac4a98c37c6254c61bf212a630df10953186fc64a98c37c3254c01bfb0aa6009fd8553006fcc2a98037d6154c01be30aa630dfc8553186f842a98037f6054c01bf302a600df58153006f8c0a98127c6054c61bf902a630df08153035fecba180afe65d0c5f7eb2e8606bf1974317efea7a18bfde53d0c01bea9e862ff754f43006baa7a1806fe62d0c017eb168601bf18b4301dfcc3a1802fd61d0c5fbfa8e8604bf98343005fac1a18bf7c50d0c597fb2c8602bf99643166fccb2180a7e6590c597eb2c8600df59643004facb2180afc6590c5b7eb24862cefd52431677ca9218b3bd5490c59de2a48606bf98e43166fea7218037d5390c01dfa1c8606f7d0e4300dfcc521802fd6290c037e314862eef90a4317778852180efe6190c017eb0c862cdfd4643025fcc121802fd6090c59be284860eefd96431677ccb218b33e6590c59deb2c8600cf5964307778cb218aebe6390c59dfa9c862ccfd4e430777ca7218b3bd5390c019ea9c860eef14e430777ec5218bbbe6290c01deb14860eef18a431677ea5218bbbe5290c59dea94862eef14a431777c652183bbc3290c1ddfb0c8600ef986430077ac32183bbc6190c59dfa8c862ccfd46431677ca3218b3bd5190c59de28c862eefc864317778432183bbf6090c01df3048600ef582430057ac12183bbc6090c59dfa84862cef942431677aa1218b3bc5090c599e284862eefc82431777841218b6ff6550c057f32a862dbf59543015f8caa18b77f5350c01bea9a8606f7d0d430077c86a1802ff6250c037f3128601bf18943005fec2a180efc6150c5bbfa8a8600bfd8143025f8c0a18b77c5050c0d7fb288602bf99443036fcca2180a7e6510c577eb288606df59443004faca2181afc6510c0d7f320862befd50430377ca8218afbd5410c0dde2a0862cbf98c4315efea6218afde5310c01bea98862bf754c43006baa62181bbf4310c0def2188600ef50c43037ba8621806fe6210c017eb108601bf188431577c842181bbc4210c077f3088600bf5844315efea221812fe6010c017eb00862bdf140430777eca218afbe6510c579f328862bef594430067aca2183bbc6510c1ddf318862caf98c430073cc6218afbf5310c579fa98860eef94c4315f3ca6218afbd5310c019ea98862be754c430063aa62183bbc5310c1ddfb10862aef988430077ac42183bbc6210c57dfa90862aef9484315f7aa4218abbc5210c55df190860eef0c8430777ec221803be6110c01deb08860eef1
  | 7 => 0xe0a547c00017f0003bb46459b1501014d32e30000000750001cf36c00000026900003833b0000005aa00000054903032b0000000000000000000005b14ee00000000000007f2942c10000cb0000000000005991a40601260003751f30f22bb5d14525f010311a4be13f4cf59c0ed5e45ba0002d35195132fa3625c900003447600000000027a0000b027057e00054a10e00041a0cc00000028f2750004082131700770000000002f80c83c700010800000040107e0000000000003180000660880843242860000002791743950001af5254ad17804a0000ec01e0000000005a815a00000000000000000000a35548328d0000005e612456550d4b818e2eb5343020000000b957823350049d4351ae11d3360001bd0361ba0004743e70f63420001940a30400000000000aa0005fc1e300000000014d4aa1f10000002b94711ab5fa5e343b30f00180700300000000000180280500080080180000380000100000100180080000100080180000180280100100000000080300100200000000080280100200000000000000080c00280100400080000000400000380080000680680000000080100000080100100380000200200000100300000200080200000000180100380080780000080080300080080100280100180080200200100080000300080000080300000200000000380580080000180000180180000080000080100080080400080000080300080400080380000000080000000200000000000200100100100000080000280080080100080c8000008008010020000008010000000040000038000008000000018020030000088018000008008018000048000000000010000000008018010010008008000028008010010050010010030028088010008000000000010008050000018000018000008000010020008008018000018000050018008000000010028000000020000000008010000010000008008018000000038000000010018008000000000000000038000018000028000008038018008028000010008008030008010018050018000000000000018018000000000000018000018000000000000000000000028000098010018010058010010008008000010000008008000010008000000030000008018008010000010010008000000000018020020000010000010000000070028010008020000020000000000010008000000000028020018048008010008000000030008030000040000010000030010000000008000000018000008000018000008000010030000000000018028000000008030008010008000068060008008008000000000000010000008010000000008030020008000000000020038010008010000038020008000028008000000008000018000008000008000008058000000000010000010008008
  | 8 => 0x45553932a5914a800000000000007426b4252f718b03d25c4a43f03d70000000000002a855900028a3e50000b82db3112914243881c104209858a26f21a0bb00000000016100012300014c05816b00059e0000000000000001a20004a95cc0000000500005f95d30004fb45106d0004db00000001f0004f05b700000056e00000036b25216f4b300000044b0002374665d016c0392d11720463c65220001b72e95e000032c0000004023a61e700039d3fd1c00002164160005cf08200000000049500024300027c3160000202e200000b3d60fd0001db0003c20491360000000000000000f400000000000000020c00000000000000000000046a4ae49013900000057d22058e0571fa38045e2900ee0002720af0000050003cd0000001774780000003ea5d21eb0000000000000134c400000033d4c90000cd2761b838732e0d71710000000000003280000000000000000b518425a5a540351f00000000000000038b22d08a32615900057413d36d00049f4ce0000db1a300012c28345b4875a90000003920000000de0000000971440003fe31c2630d84120000002e61140004445fb00000036100034e00021e06f11f0000004ef00000000024e3830000005e700000026804e00001800000030c0000000001e03d90555c50000000002c600000029a0003c415500039f00000000000035a00000037050840a0000fc5db34f0004df00000052b0042411fd27e0005b90730003b90000000000002d73f206500000000043d0000005480000803130000000000000dd0000270000000000000002c510f0000002ba00004d1a153842a3472014a63dc00048d0000250000c518d4502fd32d00e5d70002ca2d63a84fd55644000000900058056f00000000000000006c0000000000000002e10000000004ec0002400000003861691de0000672e80000004e50000891510001094eb45420e27b4130000002a459747b3e626531433338a3cf0000004480004f142100030350e0480002b15e51d74ca4d93e20be03b0000005a30000000000003520004f847235f0003a90003771df0002ea5c15ac00000037353059a00000022a0000000000000002fb3db3430680000000000000003101b60000000005732284d80993fc0540002af34a02f4650000002bd0001f220325651154154326d0002625bc51b15f12e0005dd3ca3f819000000032506236e0004bd4af3fb0000004450005fe5464602f600049e1ac0850003562fc0000000000005ed5900000000d53930004200000004110002550ba1ce5f300000014740516000000000000000000000000020626000015c4b900005e5ca0005cb0000000521802670000d43090002ff0000000000ea00039b19a38d0410000001a900000000029800000000000000054000000000028747e00059534c42e2854d
  | 9 => 0x4c47a5860000000000004c80000000001110e600000000000028e00000044e2c44790f91b05b600048f0c40003aa1f817543c1d432209012f4d700003741705f5cd00000051517c0000002125f24800ce2ab25443312d0000074982d455f0002493b55b400000d00000000045f00000055e3af0000005ce17b0001da18236f00000019d2f40000000000000000290c705a41036a41d44721c3321270ab2ed50a2262190000003c15830030002990d30000c33f44f72182da25d00049b15315d0000c05f40002aa00001a2c80000000000000004f200007242d00045c22700000045700000000000000000000000033523d4dc0b357b2710004b511e47d59227409200003530e57f00000000000033100056b00000022f2b80000004421005700005e10000000000000004610000001f90003c90002d218655d0000e85a40005a009b15e53b0eb1fb3ec3e10005a70000002b71354f921700000000000020a0000000000c235937a00046900f1b30001e54ab0e74cc0000000000000000002530230003b33da0061a63575522e529f23a0f50000000003ff00037800000000032154d0000000005540003c000026c0002110c92730bc4c318800016e50958f00031245907d0002483d800000032901755a53329e00000000025900011b44d0003ce0003a50fb0595a60001055793984633ba4860e21852ce04f52012b13b37b47300001b1dd59f0000001813852233392320000003ef1133f13dd00033728400001457c0220000001100002924d000000000019b0000ca4b00310004003710001cc0001f000000000000000042b0ef33f00014b19c0004893cc1fc39755324f0000004ba3ac5710000005da0000000000004fc5d90002b60000000000000003003f60000000004dd3ee1fe3691163f90f04815fd46e00035c4c731a33806458835e51d2dc17d0004e75b240c3891650000000da0000001c80000005bb00000050b0000fa00000000043a0000ad4370000000002ac2cb0001ec0000000000000003820000000005ae1202ec5de00013218c2dd00052c00005d0001be00055c39c3060000a000016856c23f22b57230d0000000000005d809f00000000024b35100000000000000000000049200000000000000000014f53e0003e409313a0000001210001cd2105440001520b456943826e4a213e4ed0000000003b60003ab41c00058500000048800000000000003a0000000003d40000000000000000000000002610000000000000000004930000000000000000005a10000003650000700000000000002365ad00048e00000046b00000000023018a0000000000005294ff4b725b0000000163df00000000000000000005606300800000000043407c35d2b41ed0000002a94280002515422f300000000000200041b2243963b00a95d4246
  | 10 => 0x5065230d20005c755b2d01253074e25c838e1a559340d0000001e200045300000000000000034b00000019325751a0000000000001190004490000000005ef52800000000053d2e718f0fe5623eb3c51452f91462054325610001a71730000005473305760000000d02340000000320002072c23ae00000000000000000000010631900000000000000000000012230836704b5372950000450d60003580000004f30a10003721c205148b03f21540e0f85eb1c62a70b732f2780a80000005141bb3765550000003cb0003911b20000f332043e4390001e900000010c00055724a0000003680000002773403460000000a22a60000000000000005c410b56000058200050300034d4c53d201031700012842723523939a4181871dc1372b318300002438158400028b0005c000000000000024d4945165c35e90004f60000000005100e10000000000df4151422314560810000001561340004234190000000000000000003450000000001ef0002662384685871410e400000000000022900000057a52e00031b00009c0000000004041962c94064fa1e608f4d528c0000ac00001c00022e29d00028200000000056d5f600048c4c205c5e20001bf0001c54e10000000000000000005665514a02a058b5d50f708620200058c1150005a20000003f55f70212971ea5bf3d00003e32ee0001483be1d10003bf4850001920005f501d00000000000000052d1b50000000000001180000001120000000000000000000004d600000000000000000000029b44154b3de07100000007900000000032300054e0000690001760bf0000004310000000000004e41b11ad4220a60000000000000000000000000003c83ad00047004413c3f75bd03330b3533a040b0003fa0001e82cf05b00019100000033c06b0000950003bc00000000044600000000002b4750004f50000000000001cb0002140005275581ca00020900036345d0001aa0001d60000002bc22c5310000150001634e900034800008c0000000000000003490005f100010d0000004cd3c330a0b15684e81f553c00000000000000043f06e00000004300000037c4b227f23e0000004b421d48a4f417a4e310a2a251e3012d50000000001670000000000005670000000000001582cc0000000000003d548200000000000050c0001330000001620001c942951c2a112a0001a05c61bc0002420000000001434671951d952145a32706138f3a70000000000004362de00054f0000005af09e5d61f63442e44c11b44a314031500000013015b00039e17e0000000280000000cf46d0000004771d300020d3b800050450115724c0004b600008b5b33790002bf4094912f200000000000049700000007b00009436000002a2f50005630000004da0003d30000004842640000002f000000014a2c34
  | 11 => 0x1e11541d85180000005240194d22963a10000002be05300008700000000000000000000000030400011c0003b70000000c100016d00007a5f803c52a0000000000004b10000005050004140dc0d100050f2502440003ed0120000000000001893f346f00021f19906a0005320001ff0000001a83900000e00110000000000000000000000000000005ea0000000c638c23c0470005893b20002224a50000004bf37e4cb29c2e000000108e52f42f4bb4fe0000000000000000000005df47f4e053521b49a3bd0ae02c1f727d5770004d40000000000e30000000000000000000001020000b600000026a5be44f55031d2c03341d523b0bd03e1b91e410744a1794ac00000037f2b22ae2d922519f0003a241f5ab1c40004263e953600000000000042c0001310d92933b10000000002df00059d0000000000000000001c700000014951249600028809a0001972ad36650700002600000009124500019e54c3e00000000000000003410000a70005b800030500035411709600058d2c746c00020000000035b5260003940005452d84bc0833a43500000004c000038450200000037400000000041e0000000002080000000004995645ee13824757502d28120b3e81c30004c649c0a420425f00059820f08d0000002b000000000000037d2fe1d21ee0000002a34a71980000003995b00000e50001f45dc04c1640001040000002b55174070002ef22153f09d5940000002a500059600000031f0000000004ea0e90002f156a00036400016a4580000003b42582800b24430000003a30005e82cd4624305b500014e40f4a100000000002e31e25e0000760000005c200000000000000053a33e00033a4e60001661294d12895ec0003d15810780ff0f100000000000000c1d
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc6510d100069f6310d100769c6310d100071d5310d10005b97010d100047f75589100147c7558910004bf7458910034bc7458910004df7358910004dc73589100247c765451002578705451001677765451002574765451001674765451002474765451000577735451000736435451000734435451000773705451002576705451002574705451000770705451001e77605451001f73605451000575758c510024f4764c51000575754c51000794434c5100063f65d011009e3c65d01100073551d01100063f65501100ae3c65501100059c73501100073551501100066f65c81100666c65c81100076551c8110195e972881100077151881100066f65481100566c65481100076551481100276a5048110027685048110007ab4048110007a9404811001cf8764811000771514811000eeb764811000ee876481100076b754811018f6875481100076b654811018f68654811018f6b5348110007695348110007aa4348110007a84348110007e37148110007e07148110026eb6148110027e3614811018f6b514811018fe2514811000769514811018fe15148110007615148110007e23148110007e131481100047f735941001c7f715941001c7d71594100247e70594100247c70594100263f40594100263d40594100266f20594100266d2059410026771059410026751059410074be73990100063f539901001e3f519901001e3d51990100263e50990100263c5099010026af2099010026ad2099010074bc73590100063f535901001e3f515901001e3d5159010024bf7059010024bd70590100263e50590100263c5059010026af2059010026ad20590100147e7598c100047d7598c100065f5398c100065e7598c100065d7598c100769f7498c100769c7498c1001e5f5198c1001e5d5198c100265e5098c100265c5098c100269f4098c100269d4098c10026cf2098c10026cd2098c100147e7558c10004bf7458c10034bc7458c100065f5358c100065e7558c100065d7558c100069f7458c100069c7458c1001e5f5158c1001e5d5158c100265e5058c100265c5058c100269f4058c100269d4058c10026cf2058c10026cd2058c10026d71058c10026d51058c100047f7654c100047d7654c100063e6454c100063d6454c100065e6354c100065d6354c101866e6254c10025787054c10074bf7690c10004bd7690c101663e6590c100063d6590c100769e6390c100069d6390c10176ae6290c10074bf7610c10004bd7610c1015e3e6510c100063d6510c100769e6310c100069d6310c100071d5310c10156ae6210c100066f53588100066d5358810006ae4358810006ac435881001e6f515881001e6d5158810024ef7058810024ed70588100266e50588100266c5058810026af4058810026ad4058810026ea105881001ee91058810
  | 1 => 0xc120005ac74cc1200074d53cc1200276850cc1200056f754c1200556c754c120005af744c120005ac744c1200074d534c120007a9404c1200047f7359710004ef725931000cec72593100147e7598f100047d7598f10024f67198f100147e7558f10004bf7458f10034bc7458f10004ef7258f1000cec7258f100047f7654f100047d7654f10025787054f101663e6590f100063d6590f1015e3e6510f100063d6510f100769e6310f100069d6310f100071d5310f10004bf7458b10034bc7458b1001d77765471002e77765471000577735471000736435471000734435471002576705471002574705471000575754c71000794434c71009e3e65d03100063d65d03100073551d03100ae3e65503100063d65503100059c73503100073551503100666e65c83100066d65c83100076551c83100566e65483100066d65483100076551483100363e75992100363d7599210074be73992100063f53992100063f51992100263e50992100263c5099210026af2099210026ad20992100047f75592100147c7559210004df7359210004dc73592100063f75592100063c75592100069f7359210074bc73592100069c73592100049c73592100063f53592100063f51592100263e50592100263c5059210026af2059210026ad20592100147e7598e100047d7598e100047f7558e100147c7558e10004bf7458e10034bc7458e100247e7654e100247c7654e100063e6454e100063d6454e100065e6354e100065d6354e101866e6254e10074bf7690e10004bd7690e101ae3f6590e101ae3c6590e10176ae6290e10074bf7610e10004bd7610e101a63f6510e101a63c6510e101a69f6310e100769c6310e100071d5310e10156ae6210e10005b97010e100047f7558a100147c7558a100066f7558a100066c7558a100066f5358a100066d5358a10006ae4358a10006ac4358a100066f5158a100266e5058a100266c5058a10026af4058a10026ad4058a100247c76546100063e64546100063d645461012e6e62546100066d625461003e75615461002578705461000eea6248210025eb7648210006eb76482100076b754821019f6875482100276b6548210027686548210027aa6448210027a9644821019f6b5348210007695348210007aa4348210007a8434821019f6b51482100076951482100147e76d95100047d73d95100247d71d95100247e70d95100247c70d95100047f75591100147c7559110004df7359110004dc7359110004ef725911000cec72591100147c75d8d10034be74d8d10004bd74d8d100147e7598d100047d7598d100047f7558d100147c7558d10004bf7458d10034bc7458d10004ef7258d1000cec7258d100147e7518d100047d7518d100047e7654d100047c7654d100063f6590d101663c6590d100063f6510d1015e3
  | 2 => 0x556e7518d200056d7518d200056e7654d200056c7654d200072f7454d200072c7454d200556f7354d200574f7354d200056f7154d200076b7054d200256e7054d200256c7054d20007687054d20025687054d201866f6054d201876b6054d200074d53d0d200556e7590d200056d7590d201d72e7590d200072d7590d200072f6590d201d72c6590d201ddae7390d201d72f5390d200072d5390d201d72f5190d20005ad7090d20176af6090d20177ab6090d201af2e5090d201af2c5090d200556e7510d200056d7510d200074d5310d20025ea7010d20005e97010d201c72e7510d200072d7510d200072f6510d201c72c6510d201cdae7310d200078e7310d200078f6310d200078c6310d201c72f5310d201c78e5310d200072d5310d201c78d5310d200070d5310d201c72f5110d20007aa7010d20005ad7010d20007a97010d20005a97010d20156af6010d20157ab6010d201a72e5010d201a72c5010d201a78e3010d201a78c3010d200556c75d85200556e75985200056d7598520005e970985200056f75585200556c7558520005af7458520005ac7458520005cf7358520005cc7358520005eb70585200556e75185200056d7518520005ae7418520005ad7418520005ce7318520005cd7318520006e561185200056e76545200056c76545200056f73545200072e43545200072c43545200556f71545200576771545200256e70545200256c705452012e6f605452012f6b60545200556e75905200056d7590520005ce7390520005cd7390520025ea7090520005e97090520004ef7650520004ec76505200556e75105200056d7510520025ea7010520005e970105200556e75cc5200056d75cc5200078c43cc5200556e758c5200056d758c520005ae748c520005ad748c520025ea708c520005e9708c520004ef764c520004ec764c5200556e754c5200056d754c520005af744c520005ac744c5200078c434c5200556e750c5200056d750c520025ea700c520005e9700c5200556e75d01200056d75d01201bf2e75d01200072d75d01200072f65d01201bf2c65d0120005ae73d01201bf2f53d01200072d53d01201bf2f51d01200072d51d0120025ad70d0120026af60d01200bfab60d01200272e50d01200272c50d0120027aa10d01200056f75501200556c7550120005cf7350120005cc7350120027685050120027a840501200072f75501201b72c75501200072f65501201b72c65501200078f7350120005ac73501200078c73501200058c73501201b72f53501200072d53501201b72f51501200072d5150120025af7050120007ab7050120026af60501200a7ab60501201b7ab50501200272e50501200272c5050120027a85050120027285050120027aa3050120027aa10501200556e75cc1200056d75cc120005af74c
  | 3 => 0xe75d03200056d75d03201ef2e75d03200072d75d03200bf2e65d03200bf2d65d0320005ae73d03201ef2f53d03200072d53d03201ef2f51d03200072d51d03200272e50d03200272c50d03200056f75503200656c7550320005cf7350320005cc73503200072f75503201e72c75503200a72e65503200a72d65503200078f7350320005ac73503200078c73503200058c73503201e72f53503200072d53503201e72f51503200072d5150320007ab70503200272e50503200272c50503200656e75cc3200056d75cc320005af74cc320005ac74cc3200074d53cc3200056f754c3200656c754c320005af744c320005ac744c3200074d534c320074be73992200063f53992200063f51992200263e50992200263c5099220026af2099220026ad2099220074bc73592200063f53592200063f51592200263e50592200263c5059220026af2059220026ad20592200147e7598e200047d7598e20004bf7458e20034bc7458e200063e6454e200063d6454e200065e6354e200065d6354e200566d6254e20025787054e20074bf7690e20004bd7690e20074bf7610e20004bd7610e200071d5310e20005b97010e200063e64546200063d64546200566d625462001e7661546200067561546200147e76d95200047d73d95200c66e72d95200566d72d95200047d71d95200566d20d95200047f75591200147c7559120004df7359120004dc7359120004f7715912001cf471591200147c75d8d20034be74d8d20004bd74d8d200147e7598d200047d7598d200047f7558d200147c7558d20004bf7458d20034bc7458d20004f77158d2001cf47158d200147e7518d200047d7518d200047e7654d200047c7654d20025787054d200063f6590d201663c6590d200063f6510d2015e3c6510d200069f6310d200769c6310d200071d5310d20005b97010d20024ee76d0920025ea70d0920024ec7650920024ee76cc9200556e75cc9200056d75cc920024ec764c920005af744c920005ac744c9200147c75d85200047e76545200047c7654520024ee76885200556e75885200056d7588520025ea7088520024ec7648520005af7448520005ac744852001ee461485200063f65d012009e3c65d01200063f65501200ae3c65501200059c7350120027385050120027a820501200556e76d95200566e76d95200056d73d95200056d71d95200256e70d95200256c70d95200c66f60d95200c76b60d95200556e75991200056d7599120005e970991200056f75591200556c7559120005cf7359120005cc7359120005e77159120005e47159120005eb70591200556c75d8d20005ae74d8d20005ad74d8d200556e7598d200056d7598d20005e97098d200056f7558d200556c7558d20005af7458d20005ac7458d20005e77158d20005e47158d20005eb7058d20
  | 4 => 0x90300069c73590300063f53590300063f51590300263e50590300263c5059030026af2059030026ad205903007c7f7654c300063e6454c300063d6454c3007e5e6354c300771c4354c301866e6254c300065d65d0c300759e74d0c300069d64d0c30004dd7610c300065d6510c300769e7610c300759d7610c300769d7610c300049d7610c300771e7510c300771d7510c300769f6510c300771e6510c302169d6510c300771d6510c300061d6510c300778e6210c300778d6210c30077966110c30077956110c302171f5110c300759f7010c300779a7010c301a59d7010c30077997010c301a69e6010c300779a6010c301a71e5010c301a71c5010c300066f53588300066d5358830076ae4358830076ac43588300066f51588300266e50588300266c5058830026af4058830026ad405883001e76759843001e757598430006775398430006755398430076b64398430076b44398430026765098430026745098430026b74098430026b54098430026e72098430026e520984300147e75584300069c4358430006775158430006767558430006757558430006775358430006755358430006d74358430076b64358430076b44358430006d44358430006944358430026765058430026745058430026b74058430026b54058430026d73058430026d53058430026e72058430026e520584300047f76544300047d76544300063e64544300063d64544300071c435443012e6e62544300066d625443001e766154430006756154430025787054430004fb764c0301856f7654f201856d7654f200072f7454f200072c7454f2020d6f7354f200674f7354f200056f7154f200256e7054f200256c7054f200074d53d0f200656e7590f200056d7590f202072e7590f200072d7590f201772e6590f201772d6590f202072f5390f200072d5390f202072f5190f20005ad7090f201af2e5090f201af2c5090f200656e7510f200056d7510f200074d5310f201ff2e7510f200072d7510f201572e6510f201572d6510f200078e7310f201578e6310f201578d6310f201ff2f5310f201ff8e5310f200072d5310f201ff8d5310f200070d5310f201ff2f5110f20005ad7010f201a72e5010f201a72c5010f201a78e3010f201a78c3010f2012d6f765472012d6d76547200056f73547200072e43547200072c43547201f56f71547200676771547200256e70547200256c70547200656e75907200056d7590720005ce7390720005cd7390720004ef765072000cec76507200656e75107200056d75107200656e75cc7200056d75cc7200078c43cc7200656e758c7200056d758c720005ae748c720005ad748c720004ef764c72000cec764c7200656e754c7200056d754c720005af744c720005ac744c7200078c434c7200656e750c7200056d750c7200656
  | 5 => 0x263c5099230026af2099230026ad20992300047f75592300147c75592300063f75592300063c75592300069f73592300063f53592300063f51592300263e50592300263c5059230026af2059230026ad20592300247c7654e300063e6454e300063d6454e300865d6354e301866e6254e30025787054e3022e5f65d0e301ae3f6590e301ae3c6590e30176ae6290e301a63f6510e301a63c6510e302271f5310e300071d5310e30156ae6210e301a65f6510e300069d6410e301a59d7610e300069d7610e302271e7510e300071d7510e301a69f6510e301a71f6510e301a61f6510e302269d6510e301a71c6510e301a78e6210e301a78d6210e302271f5110e301a59f7010e301a59d7010e301a71e5010e301a71c5010e300047f7558a300147c7558a300066f7558a300066c7558a300066f5358a300066d5358a30006ae4358a30006ac4358a300066f5158a300266e5058a300266c5058a30026af4058a30026ad4058a300047f75586300147c75586300069c43586300247c76546300063e64546300063d64546300071c435463012e6e62546300066d625463001e7661546300067561546300075953cc2300147e76d95300247d73d95300047d71d9530034be76d91300063f65d91300063c65d91300063f53d91300063f51d91301ae3e50d91301ae3c50d91300047f75591300147c7559130004df7359130004be76191300063f65191300063c6519130074be7319130074bc73191300063f53191300069e53191300069d53191300063f51191301a63e50191301a63c50191301a69e30191301a69c30191300247c7654d300063f6454d300063c6454d30025787054d300165f7654d300255c7654d300165c7654d300245c7654d300071f7454d300071c7454d300071f6454d3021e5e6454d3021e5c6454d300071c6454d300061c6454d300055f7154d300075b7054d300255e7054d300255c7054d30007587054d30004be7690d300063f6590d301663c6590d300071d5390d30004be7610d300063f6510d3015e3c6510d300071d5310d300147c75d85300047e76545300047c76545300063f64545300063c64545300055d75cc5300069c64cc530024dc764c5300055d754c5300069c644c530004be76d01300063f65d013009e3c65d01300059e73d01300071d53d0130004bc76501300063f65501300ae3c65501300059c73501300071d5350130024fa76cc1300075953cc1300147f73594300147d73594300763e43594300763c43594300047f71594300247e70594300247c70594300263f40594300263d40594300265f30594300265d30594300266f20594300266d2059430074be7399030074bc73990300063f53990300063f51990300263e50990300263c5099030026af2099030026ad2099030074be7359030074bc735
  | 6 => 0xe75985400053d75985400059e73985400059d73985400069c6398540005b970985400053f75585400ad3c75585400059f73585400059c73585400069c6358540005af72585400a5ac7258540005bb70585400ad3e75185400053d75185400069c63185400053e76545400053c76545400053f73545400071f63545400063c63545400071c63545400061c63545400ad3f71545400af3771545400253e70545400253c70545400ad3e75cc5400053d75cc5400769c63cc540004be768c540004bd768c5400ad3e758c5400053d758c5400069c638c540004bf764c540004bc764c5400ad3e754c5400053d754c5400069c634c540005af724c5400a5ac724c5400ad3e750c5400053d750c5400769c630c540025ba700c540005b9700c5400ad3e75885400053d75885400069c6388540004bf7648540004bc76485400069c63485400ad3e75d81400053d75d81400063f65d814009e3c65d81400069f63d81400069c63d81400273a50d81400273850d81400373a75d81400373975d81400073b65d81402373865d81400079b63d81400079863d81402373b53d81400073953d81402373b51d81400073951d81400147e7598c400047d7598c400769c4398c4009e3e6454c400065e6354c400065d6354c4021f1c4354c401866e6254c40004bd7690c40176ae6290c400066f53588400066d5358840006ae4358840036ac43588400066f51588400266e50588400266c5058840026af4058840026ad405884009e3e645444012e6e62544400066d625444001e7661544400067561544400147f76597300763f64597300763c64597300063f74597300063c74597300763e43597300763c43597300047f71597300147e75d93300047d75d93300763e75d93300763d75d93300769e73d93300763f53d93300063f51d9330076b970d93301ae3e50d93301ae3c50d93300763e75193300763d75193300769e73193300763f53193300769e53193300069d53193300063f5119330076b970193301a63e50193301a63c501933006c7f7654f300763f6454f300763c6454f300771e4354f300771c4354f300055f7654f3006e5f7654f300071f7454f300071c7454f300771f6454f3021e5e6454f3021e5c6454f300771c6454f300061c6454f300055f7154f300255e7054f300255c7054f30004bf7458b30034bc7458b300147e7558730004bf7458730034bc7458730004ef725873000cec72587300047f76547300047d76547300063f64547300063c6454730025787054730024dd76cc7300055d75cc7300769c64cc7300055d754c7300069c644c73009e3e65d03300063d65d03300759e73d03300071d53d03300ae3e65503300063d65503300759c73503300071d53503300363e75992300363d75992300063f53992300063f51992300263e5099230
  | 7 => 0x4d40004be76d0d400069c63d0d400071d53d0d40024be7690d400ad3e7590d400053d7590d400063f6590d401663c6590d400769c6390d40024bc7650d400069c6350d400ad3e7510d400053d7510d400063f6510d4015e3c6510d400069f6310d400071d5310d40024bd74d89400069c63d0940024bc76509400069c63509400147c75d85400047e76545400047c76545400065f63545400065c63545400069c63d0540024be76905400ad3e75905400053d75905400059e73905400059d73905400069c6390540024bc76505400069c6350540005af72505400a5ac72505400ad3e75105400053d75105400069c63105400ad3e76d95400ae3e76d95400053d73d95400053d71d95400253e70d95400253c70d95400ad3c75d8d400071f53d8d400071f75d8d400071c75d8d400071f65d8d400071c65d8d400071f51d8d4022f1e50d8d4022f1c50d8d400ad3e7598d400053d7598d400063f6598d400063c6598d400059e7398d40005b97098d400053f7558d400ad3c7558d40005bb7058d400ad3e7518d400053d7518d400063f6518d400063c6518d400069d6318d400071f5318d400763e7518d400763d7518d400763f5318d400069f5318d400061f5318d400769e5318d400069d5318d400769c5318d400069e3218d400769c3218d400063f5118d401a63e5018d401a63c5018d400059e7618d400069e7618d400071e7518d400071d7518d400069f6518d400071f6518d400061f6518d400069e6518d400069d6518d400069c6518d400071c6518d400061c6518d400069e6218d400069c6218d400071f5118d401a71e5018d401a71c5018d400769f7518d400069e7518d400061e7518d400069d7518d400061d7518d400769c7518d400769f7218d400069e7218d400069d7218d400769c7218d400069f5218d400069e5218d400069d5218d400069c5218d400769f7118d400069e7118d400069d7118d400769c7118d400069f5118d400061f5118d400069e5118d400069d5118d400069c5118d400069f2118d400069c2118d400769f7018d401a69e7018d400069d7018d400069f5018d401a69e5018d401a61e5018d400069d5018d401a69c5018d401a61c5018d400069f2018d401a69e2018d401a69c2018d401a69e1018d401a69c1018d400063f7654d400053e7654d400053c7654d400063c7654d400043c7654d400ad3f7354d400af1f7354d400071f6354d400763c6354d400071c6354d400061c6354d400053f7154d400253e7054d400253c7054d400069c63d89400053f75589400ad3c75589400059f73589400059c73589400069c6358940005b77158940005b47158940005bb70589400ad3e75cc9400053d75cc9400769c63cc940004bf764c940004bc764c9400069c634c9400ad3c75d85400069c63d85400ad3
  | 8 => 0x247e760c6500047d760c6500247e76886500047d76886500053f74486500053c744865009e3f74597400363c74597400047f73597400363c43597400047f71597400363f40597400147e7598f400047d7598f40024be7498f400769c4398f400147e7558f40024bc7458f400369c4358f400047f7654f400047d7654f4021f1f4354f4021f1c4354f4009d3e7590f400053d7590f401663e6590f400063d6590f40024bc7458b400147e7558740024bc7458740004ef725874000cec72587400047f76547400047d765474009d3e75907400053d75907400059e73907400059d7390740005af72507400bdac72507400353f765974009e3f76597400053f73597400363c63597400053f71597400253e70597400253c705974009d3e7598f400053d7598f400063e6598f400063d6598f400763e7598f400763d7598f400763f5398f400063f5198f401ae3e5098f401ae3c5098f4009d3e7558f400369c6358f400053f7654f400063f7654f400043f7654f400053d7654f400063c7654f4009d3f7354f4009f1f7354f4021f1f6354f400763e6354f4021f1c6354f400053f7154f400253e7054f400253c7054f4009d3e75ccb400053d75ccb40004bf764cb40034bc764cb4009d3e75987400053d75987400059e73987400059d739874009d3e7558740005af72587400bdac72587400053f76547400053d76547400053f73547400063e635474009d3f715474009f3771547400253e70547400253c705474009d3e75cc7400053d75cc740034be768c740004bd768c74009d3e758c7400053d758c740004bf764c740034bc764c74009d3e754c7400053d754c740005af724c7400bdac724c74009d3e750c7400053d750c74009d3e75887400053d7588740004bf7648740034bc76487400147e7598e400047d7598e400ae3d6454e400065e6354e400065d6354e401866e6254e400769e6390e40176ae6290e400071d5310e40156ae6210e400066f5358a400066d5358a40006ae4358a40006ac4358a400066f5158a400266e5058a400266c5058a40026af4058a40026ad4058a400ae3d645464012e6e62546400066d625464001e7661546400067561546400147e76d95400ae3e74d95400ae3d74d95400047d73d95400047d71d95400ae3d40d95400147c75d8d400065f53d8d400065f65d8d400065c65d8d400065f75d8d400065c75d8d400065f51d8d4022e5e50d8d4022e5c50d8d400147e7518d400047d7518d400065f5318d400065f6518d400065c6518d400065e7518d400065d7518d400769f7418d400069f5418d400069e5418d400069d5418d400069c5418d400069e4218d400069c4218d400065f5118d401a65e5018d401a65c5018d401a69e4018d401a69c4018d400047e7654d400047c7654d400065f6354d400065c635
  | 9 => 0xc764c9310059c744c93101dd4714c9310147f76545310ec7d76545310063f64545310063c64545310055f73545310071c43545310066f625453112e6c625453101f5431545310779443cc5310147e75d81310047d75d81310067850d81310763e43594310763c43594310247c70594310e47f7654c310771c4354c31004bf7458831034bc7458831004f7764c43100755534c43107796434c4310047f75580310147c75580310047f73596210247c705962112e6f20596210147e7598e210047d7598e210147e7558e21004bf7458e21034bc7458e210047f7654e210047d7654e211663e6590e210063d6590e2115e3e6510e210063d6510e210769e6310e210069d6310e210071d5310e210047f75582210147c7558221034be76d9121074be73d91210063f53d91210063f51d9121004bd70d91210063c50d912111eaf20d9121004ef725912111cbe7619121074be73191210063f53191210063f511912123eae211912123eac2119121004bd70191210063c5019121106af2019121034be74d8d21004bd74d8d210147e7598d210047d7598d21034be7498d21004bd7498d21004bf7458d21034bc7458d21004ef7258d210147e7518d210047d7518d210063f6454d210063c6454d210065f6354d210065c6354d21004be7690d21074bc7690d21004be7610d21074bc7610d210071d5310d210063f64545210063c645452101f6421545210147e75d81210047d75d81210063f7458e500063c7458e500265f7358e500047f7158e500247c7058e500263f4058e500263d4058e500265e3058e500265c3058e500266f2058e500266d2058e500247e7690e500047d7690e501ad3f7690e501ae3e7690e501ad3d7690e500063d7690e500043d7690e501a53e7390e500063d6390e501af2e6290e501af2d6290e501ad3d7090e501ae3e6090e501af3a6090e500247e7610e500047d7610e501a53f7610e501a63e7610e501a53d7610e500063d7610e500043d7610e501ad3e7310e500071e7310e501a71f6310e500063d6310e501a71c6310e501a72e6210e501a72d6210e501a53d7010e501a63e6010e501a73a6010e500247e76cca500047d76cca500053f744ca500053c744ca500047f73586500063e43586500063c43586500267771586500247c70586500263f40586500263d40586500266f20586500266d20586500267610586500267410586500247e76906500047d76906500055e73906500055d73906500056f72506500c56c72506500247e76106500047d76106500247e76cc6500047d76cc6500065d63cc6500071c43cc6500247e768c6500047d768c6500053e748c6500053d748c65000675618c6500047d764c6500053f744c6500053c744c6500065d634c6500071c434c6500056f724c6500c56c724c65000675614c650
  | 10 => 0x94410247c70594410363f40594410147e7598c410047d7598c410769c4398c410147e7558c410369c4358c410047f7654c410047d7654c4121f1c4354c411663e6590c410063d6590c410047f75580410147c7558041036bb40580410147f76597310763e43597310763c43597310247c70597310147e75d93310047d75d933100cee72d9331004ed72d93310dc7f7654f310771c4354f310065d65d0f3101cdd7610f310065d6510f310769e7610f310769d7610f310771e7510f310771d7510f310769f6510f310771e6510f312569d6510f310771d6510f310061d6510f31077967110f31077957110f312571f5110f310059d7010f311a69e6010f312571c5010f3101cdd76ccb310059c744cb310147f76547310055f73547310071c435473101f5631547310047f75583310147c75583310247c705963101e7710596310063f539923101e3f519923101e3d519923101e9f319923101e9d3199231004bd70992310063c50992310063f535923101e3f515923101e3d5159231004bf70592310063c50592310147f7654e310063e6454e310063d6454e31005777154e311663e6590e310063d6590e3115e3e6510e310063d6510e310071d5310e310075553cc6310047f75582310147c75582310057870595310063f74595310063c74595310f47f73595310065f73595310066f72595310066c72595310e47f71595310067771595310067b70595310247c70595310067870595310247870595310147e75d91310047d75d9131034be76d91310063e65d91310063d65d91310063e75d91310063d75d91310069d73d91310063f53d91310063f51d9131004bd70d91310063c50d9131004ef725913100cec7259131004be76191310063e65191310063d65191310363e75191310363d75191310063f53191310063f5119131004bd70191310063c50191310063f6454d310063c6454d311866c6254d31005777154d3101cde76d0d310065d65d0d3101dd671d0d31004be7690d311663e6590d310063d6590d3124d9e7390d31176ac6290d31004be7610d3115e3e6510d310063d6510d312471f5310d310071d5310d31156ac6210d310065d6510d310069f6410d310059e7610d310069e7610d312471e7510d310071d7510d312469f6510d312471e6510d312469d6510d310071d6510d310061d6510d310769f6110d312471f5110d310059d7010d311a69c6010d312471c5010d310147e75d89310047d75d893100cee76d89310066e65d89310066d65d8931006af64d8931006ac64d89310078c43d89310066e75d89310066d75d89310066f53d89310066d53d8931006ae43d8931006ac43d89310066f51d8931004ed70d89310066c50d89310066e65189310066d6518931006af6418931006ac64189310078c431893100ecc62cc93101cd
  | 11 => 0x20c7f7654f320771c4354f321874e3254f320147e75587320047f75583320147c7558332034be76d91320063f53d91320063f51d9132004bd70d91320063c50d9132176af20d9132174be76191320063f53191320063f5119132004bd70191320063c5019132156af20191320063f6454d320063c6454d321874c3254d32154be7690d32174be7610d320071d5310d320147e75d81320047d75d81320055e73d91510055d73d91510063f649915110d7571991510056f725915112d6c72591511257771591510053e74d8d510053d74d8d510063e74d8d510063d74d8d510247e70d8d510065f6398d510ed757198d510053f7458d510053c7458d510056f7258d5112d6c7258d510e5777158d510057b7058d51005787058d510047e7690d510047d7690d510063e7690d510063d7690d5115d3e7390d510063f6390d511663f6190d51167376190d510053d7090d511ae3c6090d510047e7610d510047d7610d510063e7610d510063d7610d511653e7310d510071e7310d510063f6310d510071e6310d510071d6310d5115e3f6110d5115f376110d510053d7010d511a63c6010d5112e6e62d89510053f74589510053c745895125d77715895100577715095101d7471509510047e76cc9510047d76cc9510053f744c9510053c744c95100577714c95101d74714c9510053e74981510053d749815112d6e72981510056d729815103d7571981510457771581510053e74181510053d74181510055e73181510055d731815112d6e72181510056d72181510267a60181510147e7598f410047d7598f410769c4398f4101cbc7458f4121f1c4354f41104bf7650b4101f3641547410047f75583410147c7558341036bb40583410047f73596410247c70596410147e7598e410047d7598e410065f5398e410065e7598e410065d7598e410769f7498e410069e4298e410069c4298e4101e5f5198e4101e5d5198e4101e9f4198e4101e9d4198e410065c5098e410147e7558e410065f5358e410065e7558e410065d7558e4101e5f5158e4101e5d5158e410065c5058e410047f7654e410047d7654e410065e6354e410065d6354e411663e6590e410063d6590e410769e6390e4115e3e6510e410063d6510e410069d6310e410071d5310e410047f75582410147c75582410147e7518d410047d7518d410065f6354d410065c6354d411866c6254d4101cbe7690d410769c6390d41176ac6290d4101db67190d410071d5310d41156ac6210d4100cee76d89410066f53d89410066d53d8941006ae43d8941006ac43d89410066f51d8941004ed70d89410066c50d894123eaf641894111cbe76d094100eac62d094101cbc765094100eac62509410066f625454112e6c625454101f3441545410147e75d81410047d75d81410047f73594410363c435
  | 12 => 0xf7154e431ad3c7054e431653e75986430053d7598643076b761986431653e75586431ad3c7598243175ae7298243005ad72982430053f75582431653c75582430063e65582430063d65582430063f75582430063c75582430063f53582430063d53582430063f51582431ae3c5058243076bb3058243076b830582430147e75d81430047d75d814315e3f74594430363c74594430763c43594430047f71594430247c70594430363f40594431647f7654c4321d5f7654c431665f7654c430071f7454c4321f1e7454c430071d7454c4321f1c7454c4321e5e6454c4321f1e6454c432671e4254c4321f1c4254c430055f7154c431a55c7054c43004bf7650c430071d5350c43036ac42588430147e7558443004ef725844300cec7258443036b441584430047f75580430147c75580430065d5358043036bb40580430753f765944315e3f76594430771e73594430753d735944315f1d735944315d1d73594430763e63594430053f71594431a53c70594430763f60594430759f7598c430771e7598c432759d7598c430771d7598c430051d7598c430771e6598c430771d6598c430059d7198c4326f1f5198c431a59e7098c4326f1c5098c430753f7654c431663f7654c431643f7654c430753f7354c4315f1f7354c430763e6354c430771e6354c432671e3254c430771c3254c430053f7154c431a53c7054c430071f7654c430051f7654c431661f7654c430071f7254c432671e7254c430071d7254c432671c7254c430771f6254c432671e6254c430771c6254c430071f7154c430051f7154c430071e7154c430071d7154c430071c7154c430771f6154c430771c6154c432671f2154c432671c2154c430071f7054c430071e7054c430071d7054c430071c7054c431a51c7054c430771f6054c430771c6054c432671f2054c432671c2054c430071d5358843076ac625884315d3e75984430053d75984430071d539844315d3e75584430071d5358443005af7258443155ac7258443076b461584431a53c75980430071d5398043155ae7298043005ad72980430053f755804315d3c75580430063e65580430063d65580430071d53580430063f75580430063c75580430063f53580430069e53580430063d53580430069d53580430061d53580430063f51580431a63c5058043076bb3058043076b830580430147e7598f420047d7598f420769c4398f4200cbc7458f4221f1c4354f420047f75583420147c7558342036bb40583420147e7518d420047d7518d420065f6354d420065c6354d4200cbe7690d420769c6390d4200dae7290d420071d5310d420147e75d81420047d75d81420147f76597320763e43597320763c43597320047f71597320247c70597321866f20597320147e75d93320047d75d933201cf671d9332004f571d9332
  | 13 => 0x501100100100100a00400000400000200f00000900200100100000000001500000200300100300000100400800100100200100600000000600000900002300a00400000000100000300100100000400e00500300400000200100200400400000600000100600400100300000400001300000000000000000001d00300200000000000100000000300000000400000400100000000000000000100000000400000000000000000100000400700000300000100000000000300f00000500000000800800000200000400000100600000800000600900000000400600600100400000100100000100900000300200200100000200300200500000200c00100200000200200000500000100200800000300200400000200000300000000300100000200200200000c00500400000000100500000000600600000300000400400400500400000200d00000300900000300000000000000000800400000000000100000400100000100800000300300000000000100100100000000000300100500100100100000400200300000200100200100100000100100000300100200800500100900100a00000200000200601100300000600100100000100200100400100800200400100000000000000500000400100001000400000000000100100300100200000b00501f0000030050010020050020031671d73d91531663f63d91531671f63d91530053d70d915315d3e74991530063f649915316d5d739915317d5f73591531653e76191530063e761915321f1f731915315e3f631915315f1f63191530053d70191531866e62d89530053f74589530053c745895327d5f73589530063f64d85530063c64d85530247e70d85530053e74985530053d74985530ed5d73985530053f74585530053c74585530063f64585530063c64585530f55f73585530056f72585531856c72585530057b70585530057870585530053e74981530053d74981530063f64981530063c64981530855d73981531856e72981530056d72981530053f74581530053c745815308d5f73581530053e74181530053d74181530063f64181530063c64181531856e72181530056d72181530057671181530057571181530267a60181530165f7654f430165c7654f430071f7454f4321f1c7454f430055f7154f4322d5c7054f430047f75583430147c75583430065d5358343036bb40583430147f76596431663f74596431663c745964321e5f43596430763e435964321e5c43596430047f71596430247c705964315c7f7654e4321e5e6354e430071d53d0e430147e75586430047f75582430147c75582430753f76596431663f76596430763e63596430053f71596431ad3c70596430763f60596430753f7654e4315e3f7654e4315c3f7654e430753f7354e431671f7354e430053
  | 14 => 0xd74278000000000000000018e00008e63a900800000000001f9800000000005f80001960000000774677000000000000038895c02b21e0000069d1360001c3a13400079f20c80000244900002034d0a00000000000a800019500000000002e5800000059f0000f184943922788ef040a2d0033000112423e00019891a253d17580007420003e01380000000000000000000046b99185340000000000000000000000000000028f0000d4a6ca00021080000004290000d6039d3c31e386286fb0001b8003a5ce2231418fc60000b492e853600025d9c9442e16d2fe8f8000048d0000a98e0075f00000007f65c8061000049e2322550ec4e440000000e300004301e1900000000000000000000000001d4c3b02bc1b714e0fc000933a132011e01838f876412a0002f89a9c29600009d171800000047f00000000000001ee80005303f716640b44294699e6c00063d34a00002925ab0000000a7228900000011440000000b48d7a54b000000000000000200900000f00200d00200100200000800000200100300100600000600200000000100500000000200000000000100100000000000000000200100000200600000000200100000300101a00500000100000000200100600900500100500100200000400000000200700300000200100100800000000500100700000200300300000100100400000000200100000100000300200000100200000100000000300300100000000301500400100000000100200300100c00000000200000100000100800700500200000000000001f00000100000000000000100600300000600000200500000200400c00a01c00900100a00000100500200100100a01100700500a01400800000000000900100000c00200000100100300200400100100600000100000000900100000000200000000000300500000000100000000900400200500200000000400a00700000100200100000200200400600200300000500000100300000000300001000300800200900100b00e00000400000000000200000100000200a00100100f00000300000100500000200700300900200000300000200100200300200300000100000000200100700300c00000600100200600000000200000000d00000000100000100200e00400200400000300801700200200400000300000100b00f01300000100500600000300800300000200000900100100000200000100300200600400000201200601000000000200000000600300200100100200300700000600100000100300400200100100000000300c00600000900501101000300300200000300100000000000200100000000200000500000000300400000200200000300100300000000000000000100200100000000200000800a00100300200400100000100
  | 15 => 0x1a20000000000025c31a00035a8ba48b248516688251aa5c319100000000003218000000000000000000000000000005de00000002c400016300007ecd3a00012919588be8561481434f003d726200000003c2000000000069a40500004b054e000207c00000028d8000c040000001cb000274745507790da00029a80000000003d0800000000000000005ae07f02f0338fb615b000087000016800015740007bc00000007280003b298201b800047c00000000000001b6c91c30d00015e00007f00001f940003463cb80010440000000000adc16a24980000008e1000000000000000001b80000000ba90891ce31c000154c0005550000000000000000000000000038280002621420f480000007de000206505261403f0e24ca46c411b8d68fb05562da86e43dc3a52ea918c9fa3b5044a3c8b0a36c1009d3cb9e309000000087e72806401483e87f14280d0c0005f900019bc00000044b0000a843a444209649440300001c08212000000000000043b35d9274bc62c02658d4400000022114c8dfe59800000010dc6c000019380004670000000b947c24221bbd0d21aa3f6175d0b8414000000086a00014290089243642ff9030f6c010000000000000036080008e64681a0974800028c00013b800009f32c0fc4e5441521a0cb8cd449f000128476400045f80010168b025b9aa400080c18b00000005ea2a610f80000620000ee0000366000005000033d0000000b202303f200000ee5dc33919b400000000000000008d400000000006eb00021949d236f07c92d4f7c138275039c0008db00000000000003d3810c0000460001aa0c54420000000000000000000000000002a49ebd1e04ab38c00009b674a3070000f6a5a60871b08ab8000000097c36a04213d0244cc64b803a029c0007c600000006f60001829fac7587df0000e883f000039c9c2cada00026d0000406000000000004e00032a800027c449000111400000000000000000000ac00000008f1000000047000033e000000000033283501d020d00000002280b6032800000000000019907366fd14ea2340004d606200000002ab2008ee4b468ae12f21a8d480bb2e68bc0c0840f2e496441681f206e9af0ba843204e9c34c4800000000007ba000000000000000026483d0bba74e1b98c0c0000001f9063ce7474d1178de01c6000000029838235823ea3b05623d623f80003401fa2779dc4be65bc0000530d546902ec2348e9064d11023fc8e842c34480007e0000401902020e0001b180000000000000cd400034f1738000eea00009112e4a4e0000350034c4000000018d80000000001ecc00000000000007d60002e9800007c0000001d680000002068000c7c6f70f40000aa40c60000000e2e00000005e4000000000000000000000011e0a6e00036818480000002e10000
  | 16 => 0x27879200020000000001ea8000dbc00007b93f90380c101b1f1d12e000000000031606300000000005741d7000000008234580e800055e0000000178000000000028c8cb0000000e844d738c872057a00033f9be80000000001ffc00000000000000001b21f200000001982d6884ce120260000000d307c300000010786601c508e47c65ec18a8a5807a1d22d716740007d007994cc2bc8bd0a69c5856e2a30cd90190a8659320115834a00000000007663de0000b8400047b0e8992c67200043100000000000000000d2c00000009c80008902f20cb0e1847500007b0d1c00000000000000000000000000630000000000000020e8000000000124800000037a000000000000009e912023c89500003a40000003cb00008800000ae21250241b30000000d6e0002298000ac20001b80000bf070638519d80007900000000b762db000000000000046400007b800024311c45300571bc988c0000001f499f852800000000000000000000140e5e0003fa01d40000000001e300000003aa800000039500005100006dc000000c00006d1f516dcaa251500009bc23007216e163c13c00000000001d400000023f4e8240936900000005070000000000589000000099e05b2d0a33031800000000000000000001df8a4676701a8654b6661e1ae0f000100003450c4016038500000000003d200000000000000000000c7256710b065c39a65a1648a9c00008116f00e40003a80dc042c54204009a19700001af2368e986a621d27200003e0000000000000000000000004d21872b880010b20000000c8c0002611cc800000000000000000007b900000000000000001e243a00d00bd8884000000000000000000015100000000002df80002062913e400003381431c5800000000000018e800000000010e400000017da128c4c57b43a08b40000000ed1768b1818a0001a04000000359848c00000000000001ea000000000058600044f092c000000000000000000000000001640000001de8b4800018500000000000000000f4600000000000006fe166000100e0000ad1e08d9c2703d505b90480000000164daa6b622d8e20fce2d92020000000000000000000000013286ec000569000001902c1b4296208c0001e22e280000003550f98df8e965ac00000000007f309900000000000001090ee87632680000c2c08c1ad80000001d418995cc00023f0001c751944b2001000083e000000224400078400000005ee00000004d81544f0085000080a01a00020140008ea27a000117635200013ec7920000000a0000066c1a61a10ecc22b0000490064000221a3e861e00039e8000c3a71a38a8d200007f24639b9059025d25b06845507040ff000000086745d1c20fec7d439383f038c8252d40a3cbe87953499f3cec079114f91a869633b2d8800025c234
  | 17 => 0x900000003445860c000000003ef3ad8be42526ec4538bfca1215f159937c8ee5683e700011645543460bf00000000000000d3c4e600000000fa67a2881b18b2684f06d86640000000001ef46365f600000000000000a78bf87402cf09615c86c20000000820cd000000a88b80000000002010e7600000006511564210001ab000084c000000056044f45f11e8b065d6471005c000000000000047400000000000000000000c80b680494390000a488351472400ea82f42660d50b8e08027180000000003da21549c20e200000000000000000ffc85e00010c0cf03ec3a9000000000027d0000b7c9025ef41712610ea00020f179cdb261a2141bd8d7e00000000000000843488a4c0008b72378000bbc02c00000000007bf3c699981ca19e2bc8000000000000000000000000000000000000001eec0003364519d702a42282ba9fdcb9847023f136052a7d105b982c35618431780001944be28217ad1b820c29d844491800000012900000a215f000000036d00000ec000210000000095c000000213800012629880000008a60418408a7871439193547463f52cf0000e6a82c1d68c184d448411e9e78f4c00041c05205640000000df00008392609fb4d0c2ee08b04b441e0000000bb10d645800000008167a9000000000039647a1b200008eb00000000006af0b3800000021f0ef800024a16b000000000000e241000000070f39300001ac00000007fcf60433108981cff40000000da058a2453d100000000e4000000000051c000000000063f00000000000000000000c840003a0058400000000020c8d98000000000000000038800000000003530000000518000000049c8852b30000f5c317054800000001b000158d1b4592000044c0000003bc0c0000000000015fc00000047c95dc9ea00015280000000000000f9400056a00023a01b46a346090681c20000eb0000000000000212c0005600aa811c00000012d8000000000000000000054f101205c0080000001f7018e00000003c40000000001930a3218900008d84b80003b500000003330001bd40000ed32803480002ca00020b44f68e4452218cb280000c28d7c00000000010980320002808bc42ae8734578000be049e41a000000000001408644ea45400000000000000001174000000109000000050312018940000000bb0d24a7c375000000000000026a14bd1300003e583603de00000003ed0b437d3a1800000000000022d8f9a3243780690140000000000048e853000230d04c0002be0cf8a287131b280003804ca00000000000001c1115c00077923021982804070000f6820a000444000000053f0000fcc000000000089c00088f075800000000000000005e600041796a4ed21a900000011ec0003c08efc21a000000104c1344c70f522a00001b600000000000003cc000
  | 18 => 0x89f0000000d8e44d2f1017000025344596bc0001c900004ad0d060600000000000002080ba000000011100000006ed00019ac67e00038080000003e21988618d96810162191cf48000000125ca880002ff1d24c1a0000000000d625ed12300004aa00000000000000000000000000000000000000000000000000000000a700000000000001b60000147000000114258b1a68ab80223d90000000d0e06b00016e4000000418800000000000000000004b400000000001500000000000000000000000000000018b000066900000000000000b623ec77a1e52fb800000062d15c9d402fe1cf038816024e5f218fa3b895a0000aa0b5874e48f1fe9d84c0662b1ab13346b2756300803c6100000000f209e68d848082645842480000a040001100000000de800030f8000c8a00000007991182d52c4000021000000020f898a7572ac80006a00000002038a4000002702e45d400017a800000000000000009d8000000000000044a00013000003cb000127000000039084bc0000c320194d117887c12b1a0c68461812d09fc37c0002e89140b1c7311909b2406e7ad1459c900000002610000000135443000000044c44195180d019341e8000066632000000104000000001cc00000040a000000000000000000005db404000000000002882501a66da0000000000000000002800000000004a072e51d356a38078280200010a80000003b993e80000d7000000000000008099ec00000000017406ec0001c683e903c794000017c00000000002b80000000000000f1624115785e000055b00000000006210000fdc000000437800056c65700000000000000001a540d280617c02b00000000000f28df0000059800000087d168800057048a35f12f48620000b79be400056c000197400072b000069800000000000010300000000000000000000000064e5410000000ac8584000095ca2259603805cc0001e100000000006dd0d6000063c04d2670000cdc00042ea3a514000016a000054000040e80010fc8110000000f0e09844a1fbcf327a82790fb878e0ef15d93b446a5582e023ccb0e55a13f1458eee5bd16ea068000000000166855a1534008001152347010a2080008b504e0000ed004f000147c0000000dd00b8000031000073000000000000bc45400000000001e461b38182a00002730731ba8c1882100000000000001371394bea0001858000ff644e4079a848e410c2cb94a05327c90b81840e5c37f3900000b7401f10580009f21e4000000000000000001100006ae000064800e00000015880000000000000f5600000000000000000558cb400082a03797649343f629b000081c8413e28c7460e59c0000000a0a00011d90583f21bc349000000000000022d00000ee22594306e20002bb109c00000000021e8ff0000000152871e88
  | 19 => 0xe300000000004bc3c5000000000046815402320000001d9000022c2f000007266d6103a1200004d200020d80000cb18609b00004ac34e0000bc200000006dd07667000000000000000000000000000179142000000000000007a6000000000000000024880000007300000158ee069f000026c2602043ac11b000058a0eba36457e3be00000009463914388f600000000a29b9800046e4361978a4c815000000000041819581e867400000000000007e218c22e00000000001904574861328a1780000160001a3cde40001ed8a0c4e20003d000002e80000d886200000000000000bcc2b50fb9c1c0005121b4a394af44523710000de65803e9047000000031880000004a7211882837e8b121d1f30b4000000000000000001810fe00000001ab80000004120000000000000000000031c08506f80011720003248000e6685800008a4000809000000118800000000000000d107f1ded16683f0e513189a21061a00d280004c343f8000c0089d0000d3800039e0000000052000000047c0000a106c917800076d000000000000000012980000c500000000000642a2800000039a259950cda87fc0000000ede00007b00000003d1000000000000000005880002500000aa51de4d316300000006750000ddc23a0000000000000000000000000000002a80000000000001280000000199000046600000000000000000001cc91ba0000000000000000000000094a75e0c88dd04c000000020e8bf80001b387c4bf41040518dac92a00000000000007b1378a0dc0ba000222045c00000001100004ce0000001d100000000e5809400064a20d8fb45c06df2d50114cfa1ed000000052400011200000004f705a84002e21fc0ee1dace5a60513c97a48383860001df07d8000000000000000000006f40007451cf80004cc6e31d51b94000000000000000000000000001d8172000000049a76c29080000488331469400000000000000000079d0000d880000000001cf00003340000000000729258000066e843000000000000035c00009125df0ce800000013700000000000003199f58000181000209c0006c54228f510f060f0000b68c320de35c9cd8eb200000004a84626c327390e0f100000f18000a745a50ab0a20a1c6131fd074c0008c20000300dae62e43b000000000000000000000000e71e4c7be0000000000e8c0000000fa0c680004158ab03ce0000001f840006e13ea800000020600000000006d3000000000006130b8aa8fa668003b1ee06c05b23d916345144e2322143c2f402326e0f3000000036699cc000034128867ce1c3830e2926c17c7fd17e914400000005f89500000000298a789506b200000000001fd3e08c045ec5250000bb4000851000000000000000022700000000000000000000000000108e2c11b5000000046100000
  | 20 => 0x11324473049a6c09600003e0580000846000000000052d0000c688aa0002348c9800000016700004da190000000000000000010d8d1a00042000002fa0931071ff914a75d0b3000040039000016c000000000014a51340d52c12314cf20600000000000000000000000000000000000000480001cd06520000001e0c00013b0001b4424043700015343504fc1889028a346e82ca8dc80004880001e700006ab000043c4d60000ed800000000000000004f800023b0000000344000192111411b12186680001c32850ec00160000000f98a444a905200ac17085f3be9dfcb6c0004648754e3871e00000008560002cd90948f814a14123d4756000000000052e0bd09f80007ce0000000000000000000000000000000000000007dd0001888000000000000073800000000000002841e8000000030e2970000000000000000044a71223300140000000000000e981330000b904368ad447033468a69727c000082e2d3152022cad67f900012007e8115314024050e3fe0001dc800023c1940f1424200000000000000000001f104d000037e000059671b00000000001ad00000000008700c189d80008ac172800000000000003e000007821e993c00000012605902ee000440955c7768f700018ed19c494000238ccf00000000f3c09400003c89090501eb0e2159400000000e0c94e700000000228c52000000218000045a00000000001f5036000023404101c1258d9e00028b8708488000000197c0001650000000fb239839f83c071c5b815a10b8c4e0002f41e680004eb257998400055f000000011a6371978000e6e877000000000000000000000000000002300c2a4dd0000000000000000099000046200011e40002150700c10cb67e83f49364a1638400023341fa0002d380006240001db000015a7b7000000000000000000000001c700000000003ce0000ebc00087922e00000004bf2419ba48d660a232000096289332995000f68cf3388ed00000c90000000000000000000063200001f93fc00000000000011bc00000000000001410000000eec00010d04e4000000009800012c6e72950edc6708642898850c6a8fc1fe14085f44652c09fa8d047f52e2019c15e2230001f28bca0cc3eb8a7058e43c17100001745480000d784c63301ae833c00000000000011005ee000068c1103cd00000000000000d80fe4cce3c400000000000002be800000000004393a0000000000089800085b0001d88d684872169cf82a20000000a180985be0000000000000000000070000000000a80008ed00005740006ee000000000008e00015bc4c40002fd800000075100018700000002a3800000049900016887c200000f09d11ac00034c80000000860528000f0a000000195082288742b800070200026f122cf5802d00021ec0008130891db80002
  | 21 => 0x15f8a5600c04913d85b021e41800004ee00040d800000063c0d70b980006a035107751be78f00000002f87a50c111040788c600018440000002e080001fe7da0000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x86c865d531480092d100baa62900026a600744c520006463b08698a4000d0d7510d31480017130021a62900024be1d53d012002594402a7a024034d48501cd404800965501b2a8090117c2143735012000687a98e6a024034d28501cd4048001a1eea39a8090003431d473501201a784280e6a024000d0e851cd4048001a1b0a39a809000343d94735012000686328e6a024000d0f511cd4048069b150039a80900036260073501201a647b00e6a024000d8b601cd4048001b16a039a80900d34394073501201a686280e6a024034d88501cd4048069a10a039a80900d36284073501200049643aa6a024000d0c7354d404800965100a9a8090003431cd515012002594402a2a024036b2a85dc1404806931d07ba660900d74a14374cc120006863a2a79824004b488054f30480092990ea9a6090003431d1534c120004d443a809824036d2875501304800171106a026090003c254d404c1200760e21aeb31e2000a1f8654c43c400143b0ca9887880d2c62015310f10024b8402ea98e2000d157510d31c400183cca39a81880030759473503100068a39aa2a06200083d87d4e648400183eea39ac908003071d473592100760f428e6b24200ec1d851cd648406983ca039ac9080d30714073592101a647900e6b242034c8d201cd648400107d0fa9ac90803b071cf53592100060e39ea2b24200083e8799153840010790eb22a70803a8720d6454e100242e43ac6a9c2043a1c8458d538401d13906bb087080d287a195310e101a50e432a621c200ec1f7654c438400183aeca988708133839895310e100068ca9ae021c2000e0d5310d62840015530021ac5080028720d645461002534432a69042000aa98610d2084001e12a621a410803b0710d7518d100050f432a621a2000a1c8654c4344001a32a6b8086880d70d1da43545101a61a3b086a8a2000b318010d51440016c304382a2880121d219754c5100764a3b08698a2000d157510d31440017230021a62880128d21951d01100060fb28e6a022000c1c651cd40440094690ca8a8088003451cd515011002532432a39022032d617254620440094c90ca8a4088003c854740481101b71432a809022000b88835012044001e42a2a0240880029a219534811000784a98869022000b61851c520440017830638a4088002d8a1d5148110005b043aa29022004b628654520440096c10ca8a4088002d8e0d51481100079121aa29022000f204354520440016c30b18a4088002d86153148110007c021a62902200ec1c435d6630401d838e8bacc608012962017558c100060eba8e8b182004878805d9530401d43906b22a60810e872116354c100050fc32a62182000a1d8654c430401d83eeca988608003075d95310c1026707312a62182034b188054c43040094d100a9ac4080038354c4358810
  | 1 => 0xea2bb086180d3079417610c301a60e282ec218600ea1f87594430c01d43b0eb28861800287e056510c301a50f402ca2186034a1c80594430c01d83ee0b2886180d3075c16510c301a707902ca2186034e0d20594430c01dc1886a9ac41803b8510d53984300070a21ea2b086004a70805d5610c01dc2887a9ac21803b8510d53584300770b42886b08600ee158510d610c001c2cea21ac218003855d443584300754bc0086b08600ee928010d610c06952b0021ac21803ba460043584301a70b28086b086034e145010d610c069d0e4021ac2180d3a148043584300050ec3086a886000c1d7610d510c069a30e021aa2180038510d615443029497c3aa721e4000b0d859cc43c80a325f0ea988790002c3e1d5310f2028e87c3aa621e4050b0f8654c43c80a161b0ca988790002c3e055310f201a587402a621e4034b0c8054c43c8001a1aa6b8087900d3620c17010f2000686ba88798e400086f865d531c80092d100baa639000323dd8434c72000686ba88698e400092f8754f40c8001a1ea639a819000343dd47350320006863a8e6a064000d0e851cd40c8001a1b0a39a819000343994735032000686b28e6a064000d0f511cd40c8069a1ca039a81900d34314073503200049643aa6a064000d0c7354d40c8001a18e6a8a8190003431d153cc320024a643aa69864000d0c7454d30c801d43906b22a71010e872116354e200760fbb2a621c4000c1d7654c438806963100a9887100034654d7010e200760e21aea31a4000a1e8654c43480014390ca9886900d2c62015310d200764c31ae021a4000d19535c0434808f948c23a2429000307d9473501200060e328e6a024034d18501cd4048029353013a6c6900125aa1f7054d2000695ba0e0a9a4000d28741c153480016c302382a690116d220153d0d20024b4402eb21a4035b28805d6434807725f0ea9c86900d6ca2015390d201a5a4402a621a4000d49535c0434807161b06ba88690002c36167310d2000586c28c621a403992f8754c434806965100a988690002c3e1d5310d201ce87c3aa621a4000b0e8654c43480016190ca988690002c3e055310d2000785c02a621a4034b0e8054c434806961900a988690003c22015310d201a584402a621a404ce0f6054c4348099e16c0a988690003c254e7010d2000686a9ae021a4034d2a505c04348069a50a0b8086900034a9d57010d2000694baae021a4000f09535c04348001a570ab8086900034a2157010d2000695b2ae021a4000d28655c04348069b1706b80869000362d8d7010d20006c431ae021a4000d2b535c04348001b14a6b8086900034a54d7010d20006c4a9ae021a4000d09535c04348001a56a2b808690002a921161185200056241ac230a4000b298010d51480092d100bae6290003435d443cc520005c4c008798a4000
  | 2 => 0x67118d400050ec2ce231a8000a8f825c4635000151904b88c6a003b251c57118d400050fc3ea231a8000a1d87d44635006943d01a88c6a00d2872035118d400744f4384231a800089d87084635000143d0a108c6a0002876142118d401a54d4004231a8000a9980084635000143f0ab80c6a0002872157018d400060ebaae031a8000a1e85c80635000143b0b900c6a00020fa1a7654d400060fb98eca9a8000c1f831d95350001838edb1aa6a0003079d86354d400060e3b0c6a9a8000a1e8718d535001d83d0e31aa6a00d3079c06354d401a60e380c6a9a8000c1c63dc5535000183eea31ac4a0003071d463589400064a31ee2b128000c94631c5625001d838c6bae64a0003071d463d85400060f3a8c730a8000c1d7518e615000183eea31ac2a0003071d4635854000646390c6b0a8000c8c63dc9615000183cea318c2a0003075d463185400041f436e6a8a8000c1f7318d515000183cec31aa2a0003071d863545400060f438c6a8a8000c1d8718d5150001c2ee231aa2a00d3079c063545401a60e380c6a8a800ec1c635d7315000183cea31c62a0003075d4638c5400041e432ea98a8004938805d5315000183cea31a62a0003075d4634c54000646390c698a8000c8c63dc9315001d838c6ba862a0003079d463885400060eba8c710a800e89e83dd921500090790cbaec0a00120f61f65d81400060f3a8c7b028000c1d7518f605001d83886bacc62010f8310d53588400750f41ee8b2e6000a1d83d4464cc01d838c9bb2a79810b07dd87454f300050f438c8a9e600ec1e8719153cc01dc3300322a7980d3079c06454f301a60e380c8a9e6000c1c64dc553cc01d838c8bae639801256201754c7300060eba8c898e600083f8759740cc00123f0ea9e81980020f21d65503300760e39acaa06600091c8754d40cc00107b0fa9cc9180020fa1f53592301641f43cc8a9c602b83c87591538c099c1cc4a9887180d2c62015310e300050fc2ac821c6000a1f855d8438c00183aecba887180129a2015358a3000706a9886b146000c1f7510d618c0090e90eb0aa3180038510d61546300050ec1ea2322600ea1c83191534c00143d0dba2a6980b3071db7454d3015e0e3b0e8a9a6043a1e86d91534c06b838edb22a6980d3071d86454d301650f438c8a9a6043a1c87191534c06983ce0322a6980d3071c06454d300060e326e2a9a6035a1c8654e434c00183ceca9c86980d2872195310d300060eba8c998a600485c865d5314c00183aea32262980d227a1a73d01300048fc3aa7a026004a1c8654f404c00183eca39a80980030719473501300048e43aa6a026004a1c8654d404c001838eca9a809803b071cf53590300750e41cc8a98600ea1c83591530c01d83ce8b2e861803a27e1d64d0c300760f42aec218600ec1d855d8430c00183
  | 3 => 0xb21a620083f87594434c46947100b288698933831895310d311a52c402ca21a6200a1d85d90434c40143b0b3b0869880247e1d6510d310058bc0aca21a6200b1880594434c40143f0eb28869880307e1d6510d3100707c12ca21a6200e0c82594434c49543f02b28869880385e056510d310070dc02ca21a6234a1c80594434c401c3100b2886988d2862016510d311a44e432e021a6200c1d655c0434c4014d100b2ec4988038359443d893100706a9887b12620086d87143624c40149b06286c4988029960450d893100436c3cca3126200a4d83994624c4014cb03328c4988021be1d651893100534402ca3126200e0d6510c624c49183aec21aa2988029660c50d813100538c08a1b026200c577654d310c41d83886bacc7108121e2017654e210050fc32a621c4200a1d8654c438840143b06286c8908028d60450d91210744e41ae03224200a1d83140644840146b02280c89083a87a0f6454d2121d0f426c6a9a4200c1e7654c434841d838eca98869091f8908464545211a60fb98e8b1ca035c2f205da439406b85a40bb487280d20fe1d6390e501a60fc1aec21ca034c1c835d8439406983c60bb087280d3070c17610e501a617902ec21ca034c2d205d8439406943d0d39887280d60fe1d6310e500060fb9886b0ca000a1d8610f319406983cec21e63280020f61b744c6500041ec30e898ca000a1d8610d31940010db0db9263280038510d614c6500760e21aeb31e800285d83dd953d008783887bb2a7a010f0710d7654f401641fc32eb21e801383f8759643d00010bb07bb2a3a003b0718d7598f400050ec1ccb31e801383f8759663d008723b07bb2a7a010f07a0f7654f400060ec1eeca9e8043c1c635d953d000107d0e3b2a7a00024760f76547400041ec36e6a8e800083f865d531d000927100baa63a0133839895310e4000706a9886b14800e89e87d5063500014390ca9e86a0003079d953d0d400760e31aeb21a802b83c865d4435001d838c6ba886a00560f61f6510d400050f432a621a8000a1c8654c43500691390cb9c82a0003079d463905400060eba8c720a8000c8c7218d4150001918c7b9282a0003079d463105400060eba8c620a8000a1e861d7635001d838c6bacc6a00560f61f6518d400050ec1eca31a8000a1d83194635000143f0ab18c6a0002872156318d400750ec3ea631a8000c1d87d4c635000143b03a98c6a00028760f5118d400050ec3eca31a8000a1d81d94635000143d0b328c6a000287a186518d400050fc38ca31a8000a1d81194635000143d0b310c6a0002876166218d400050f436a231a800ec1f759d4635000143b033a8c6a00d287a027518d401a50e404ea31a8000c1f875d4635000143f02ba8c6a003b07dc17518d4000707a94a431a8034a9a80948635000153301290c6a000287a1
  | 4 => 0xe0a80604832000000110e8760e76191530061db20e0b0aa600c38641c16154c098d0c0b94c0a98030dd9171181530061a322e2302a643e1b4054d60d0c6b07d0f32ac1218d68ea0265582431ac1e43acab048635a1d831d56090c6b07d0fa9ac1218d68ea0353582431ac1e43aa6b048635a388054d6090c1dc3660a9ac12180287e197454c430060fbb2a6a18863485c8754d6010c87c3680a9ac02183a47e197598c430048fc0aeb318863491c805d66310c5983b0dbb2a621802476077654c431a48f406eca988600a1f865c95310c6923d01b8aa6218028761a7154c430050fc32e2a988600b0f825c55310c9961904b8aa621802c6e017154c430058c402e2a988600a1d869c15310c9961d05382a621802c360a7054c430050fc32e0a98864cb0e821c15310c0161b04382a621802c5a047054c430058ac08e0a988634d1a701c15310c1dc18c4a9ac42180247e1d53984430058bc0aa7308860091f8754d6110c99a18e4a9ac221802c5e0553584430770a30aa6b088600d0d53dc96110c692390ea9cc021933439c953980431a58c402a73008600d0d535ca6010c6907d0f32ac02183b071ce65580431a51d404cab00863483c875956010c1dc3060b2ac0218d24721d53580431a58c402a6b008634a1d831d56010c6907d0fa9ac0218d28ea0353580431a41e43aa6b008634a388054d6010c1dc3660a9ac02183b860c153580431a44e43aa6b008600c1f8754d6010c694390ea9ac0218030721d53580431a40e43aa6b008600a1f8154d6010c01c3700a9ac0218d287a0153580431a50e402a6b008600e188054d6010c0143b07a8ac02183b0710d7598f420050ec18a1b226400a3581143644c80143b06280c8990028d60450191320050ec34e621aa248b158198c435449562f02b1886a8802c62016310d510048e41ae9302a20ec1c435d663d04010bb0e284c720802956045098e410042ec38a0b1c8200a5581141639040143f0ca988720802876195310e4126706312a621a8200e0d5310f625040149b06286c4a08029960450d89410760e21aeb3188243c1c43dd9531048783886bb2a62083b0710d75d93310760f3a2cba1e620ea1f8759443cc41d43b0eb2887988d2872016510f310060eb2ae021e6200a1d83142648c40146b02284c9188028760c50592310051ac08a0b24622ba1f8654c438c40143d09b9aca988030edd070595310061c3a0e0b2a6200c6b721c1654c4018d0e4382ca988028e20165d91310041ec3ea7b22620083d87143644c40143b06286c8988028d60450d91310041ec3cca322620083f87594644c40147100b28c8988020f61f53191310050ec1ea2322620083d87140644c40143b06280c8988028d604501913115c1f43ec8a9a622c83e87191534c48b4b100b2e86988020fe1d6590d311ad1c402c
  | 5 => 0xc000e095c0000f8cd07f1409bc000c63480002b000340730002a7246aa85b000000364dfa9b27c0e4ed82c3a0424f08851da190559641c4124560be40c179388b70461d89b0001fcac0000003b266c7da9408a6a48629d30e9e9398070b6a94c59ca2825d8000800005d00201f27aa80001d614a4a085a603ee8555a29a224320001144b002d2209801e8dd429c324a000788e03b8aacf923c000748bf185000864972800743852508914445d4b177296930a295811a499349d50945b08f26a0e82ec00000124768b28bf31e9b9100c0502968000ec3261ec8e2141b4574de06e4448a1462ac3fa29cf581e012a454e1050003308c8461ec290001f5000001548993087e0771b00000000b8002fe2181480015c0000024e0004e8288963f8334eb9ab2b289ca21071b65a15907e50413894938098000001723685cc7285d3a6a904a9c2000000cf143122064002241702e90ea490605788a8584f667c0004b320a282aa4f07e798f4a8d0a695c0013f15a8f4d286f292018cc13b0c44b509000354270888440006c8a81cb2d28450b0000000004b8ff3ec948b5822000000bc0fc4fe6347186b38e8391c9f30001c4001e0202a2d1a10209e0003096e1780a08806c01485c4786a5240a8419312b47b42094043c2a90c13726a559599ce33a8c0d62411f0a4143003390000b105400000000263172974f19bd0785b4a895f00027c43a500689346b8362b6ab8e49572d45f46c14a000000e2aad2c2a88300000ca0011f11f0260e104a454003285a194466a84da8b338c3e8f8a8432481c60933000548d4063080278ca8000640dc0022b4165ec540d3000000ee80012619c002681ac0000021b0d0618c00001fa60c06a264047d0df1ec1f2530759bb29a0813081b0002849392400000082000226000840c933887c000bd0006b43c00000000000181000000aa00000031c00000000000f29c01e6828398d251299400a6b5067441384246c000fda2d020000ff1343187106a0661283991aa661182c48d25336633c6e0002581e40000001842020180004a0580000800050000180e000080a8000201600820050060b8000787205000030060101a260041786c000300180803808010000080e000020281a048500400a018100300600002010020e810008020380a1080a01802000060106e01802000020080e0280402804148000281e0000604808040040183e1380e008040000600000048000000203816040000404c000080080609006020000002809002010340101000000008000003c0081a000000080800028008020780000802018160f80004004028100c01c0700c028060300c1c8300981a060040000c0d026008061600000808118080180c0000206000028040180a08802018060000a00000000000e8180980a010140200000010000100000
  | 6 => 0x8794f104a3c7a81500069c002790003c80002f0629dc15a8e0001706aa1c4864f0000000f80f40002d06600051800000000001de41a6e8d18002c09912f06904a2a4d08c2116071019fa0be228909f93b04601a8cb0480004080053e5d42c9ee01ca4d2a0161e81c8002420184c80025f2540008d9d40001dd170000000012380031c000a39ff260958002b10000007b90045e88c738e84ce2393f00048084d391464e89b46ea0c4e0790369531c850800197370a5cd316f4b262910aa61be240092a81a06b8bc8d14b63a4088b5136688621702c68ec290af462664f100009a6444ea250000512aa3f030735029223728c80d0b0304000750000765c52e00041e140f78004524bd259203d04350813919c0008b005086074c4204000008aa87018a1e800106000001579b10000011c07510894404288434a64440262cc15c108003e09b02d1b6290000a717a36e8b10091d09040c6f17c5300013a99614ca1d231df4909e11512b4104388529e05c59cf523a1de001518003129f4001af4c49f14a8f00fa2c8239e739e0006189a4e
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x273c223542510d5400180000380000501a341c00410644104b3257472340430531304a4f2c2a12213e163600003a0703001e0037004d451d463f002d280c0a530013022411490f00000b000900002e3900083b0026191f0056520e4e00141b552f150025002901002b20044c333d000000004817000054708001c1821e008120000080020c083204838002002001a6421c1829c15310c695089054d7298043005826488054d6010c016119120153580431a40725d83d456010c01a0b822016510d310068220880594434c46901c985957010d31005822416510f624c4016089059443189311a4862418654c4388401289902097118d401a5062417518d3150001489901c8634c5401a5062417519131cc0696089054c4358a301a407a5b8754f404c06901c981d953501301a5842417510d610c06910c9854d7010f201a542241535c043c800140f965d4434c7201a5422417510d31c8069818805d95310e201a446261535c043880691189854d7010d2000506259535c04348001923746047054d20006481d1811c153480691489854d7010d201a4c2241859cc434806930a98e015310d20005c06448054c43480693089854e7010d201a443261535c043480693089854d7010d201a54264c855c04348001509931957010d2000542654635c043480691289854d7010d201a462261535c0434800190b9854d7010d201a542a61535c043480695089854d7010d2000642261535c043480691089854d7010d2000542a59535c043480015089654d7010d2000542e45535c0434800150993d457010d201a5422417510f31480019097560043cc520005032597510d3148069508905d4434c520006221d98010d314800190975600434c5201a542242851cd404806950890d44735012000542255801cd404800190985600735012000542a57601cd404806950a95d4073501201a6422007354d4048069908801cd51501201a6422007454f30480019087520d404c120004c22615350130480095089754d404c1200064221d535013048069510905d4434c7101a4072617654c4384001a09536004358a101a5822595310d2084001a098654c43482101a5052597510d314400191175600434c5101a605218735454044001a086520d404811002588259515012044001b00835454048110005822595310d204400116097615314811002498259854c52044001b018510d31481101a506241751d16304069218906195310c101a6062017654c43040696089054c4358810
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xa84e0026c0801a421150c9ea2b8086900d2108a95d58010d3148001404532eac008698a40348422a48754d404c1201a441152c32a621a41080d32009620d51501204400148053b0a21a629022034a802998510d3148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4e
  | 6 => 0x5
  | 7 => 0x94e
  | 8 => 0x124e
  | 9 => 0x138e
  | 10 => 0x98e
  | 11 => 0x128e
  | 12 => 0x150e
  | 13 => 0xce
  | 14 => 0x4
  | 15 => 0x168e
  | 16 => 0x9ce
  | 17 => 0x12ce
  | 18 => 0x10e
  | 19 => 0x180e
  | 20 => 0xa0b
  | 21 => 0xa0e
  | 22 => 0x130e
  | 23 => 0x180b
  | 24 => 0x134b
  | 25 => 0xb0e
  | 26 => 0x140e
  | 27 => 0x24e
  | 28 => 0x16ce
  | 29 => 0xb4e
  | 30 => 0x144e
  | 31 => 0x28e
  | 32 => 0x28b
  | 33 => 0xb8e
  | 34 => 0x148e
  | 35 => 0x148b
  | 36 => 0x184e
  | 37 => 0xbcb
  | 38 => 0xcce
  | 39 => 0x170e
  | 40 => 0xd0e
  | 41 => 0x188e
  | 42 => 0x58b
  | 43 => 0x58e
  | 44 => 0x178e
  | 45 => 0xe8e
  | 46 => 0x178b
  | 47 => 0x18ce
  | 48 => 0xecb
  | 49 => 0x98956
  | 50 => 0x94996
  | 51 => 0x99256
  | 52 => 0x589
  | 53 => 0x1789
  | 54 => 0xa0996
  | 55 => 0x180996
  | 56 => 0x58996
  | 57 => 0x99796
  | 58 => 0x178996
  | 59 => 0x98596
  | 60 => 0xa1516
  | 61 => 0x181516
  | 62 => 0x19cb
  | 63 => 0x59516
  | 64 => 0x179516
  | 65 => 0x1a4b
  | 66 => 0x580d6
  | 67 => 0xecd
  | 68 => 0x592d6
  | 69 => 0x18c9
  | 70 => 0x180a16
  | 71 => 0x40a
  | 72 => 0x58b56
  | 73 => 0xb4596
  | 74 => 0x596d6
  | 75 => 0x154e
  | 76 => 0xec593
  | 77 => 0x178596
  | 78 => 0x59796
  | 79 => 0x15ce
  | 80 => 0x58ed3
  | 81 => 0x151796
  | 82 => 0x150596
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 72
  | 6 => 1535
  | 5 => 2306
  | 4 => 693
  | 3 => 88
  | 2 => 8
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
  | 6 => packedAt gbK6 (62927+((h/511+packedAt gbK6 (56795+(h % 511)*12) 12) % 2696)*12) 12
  | 5 => packedAt gbK5 (119904+((h/768+packedAt gbK5 (110688+(h % 768)*12) 12) % 4050)*13) 13
  | 4 => packedAt gbK4 (43197+((h/231+packedAt gbK4 (40887+(h % 231)*10) 10) % 832)*11) 11
  | 3 => packedAt gbK3 (6363+((h/29+packedAt gbK3 (6160+(h % 29)*7) 7) % 116)*8) 8
  | 2 => packedAt gbK2 (656+((h/2+packedAt gbK2 (648+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe0f80f03fe07f83ffffc03f027ce7e0733f3
  | 1 => 0xe03f000ffc1fffffc1e03ffff1d9359039fc9f
  | 2 => 0x3ffff0001ff83ffe003ffc0e1e39e3c1cf1c
  | 3 => 0x3fffffffe0003fffffc0000fe03e03fe0fe0
  | 4 => 0x3fffffffffffc0000000000fffc003fff000
  | 5 => 0xffc0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x21a02882012642481224a408a0024026031131
  | 1 => 0x4205000564088c924141095340c91490186486
  | 2 => 0x4aa5b900113522cb402b2a826162962c18b18
  | 3 => 0x8139529aa400037299b00304b603e016c0ec0
  | 4 => 0x113ce6ced39de700100c20c18dbfc003b7f000
  | 5 => 0x9e000700e2018406211003020ffdbfd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfeeaeaeafec8eac8feeaeaeafec8eac8feeaeaeafec8eac8feeaeaeafec8eac8feeaeaeafec8eac8feeaeaeafec8eac8feeaeaeafec8eac8feeaeaeafec8eac8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15965
namespace PEqualNP.Outside.L_meta_15965
open PEqualNP.Outside.L_meta_15965.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 1 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 5 := bs0_3_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
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
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 10 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 99 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 8 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 88 := (concat bgb_3_0 (concat bgb_3_32 bgb_3_64))
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
theorem bgb_4_672 : Interval gbAtlas 4 672 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 693 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 (concat bgb_4_192 bgb_4_224)) (concat bgb_4_256 (concat bgb_4_288 bgb_4_320)))) (concat (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 (concat bgb_4_448 bgb_4_480))) (concat (concat bgb_4_512 (concat bgb_4_544 bgb_4_576)) (concat bgb_4_608 (concat bgb_4_640 bgb_4_672)))))
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
theorem bgb_5_2304 : Interval gbAtlas 5 2304 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2306 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))))) (concat (concat (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))))) (concat (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)))) (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)))))))
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
theorem bgb_6_1504 : Interval gbAtlas 6 1504 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1535 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))))) (concat (concat (concat (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928))) (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))) (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeaeafec8eac8feeaeaeafec8eac8feeaeaeafec8eac8feeaeaeafec8eac8feeaeaeafec8eac8feeaeaeafec8eac8feeaeaeafec8eac8feeaeaeafec8eac8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808426 * 2 ^ 32 + 4274580168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15965.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.and,[4,6]⟩,⟨.and,[1,2]⟩,⟨.or,[0,8]⟩,⟨.or,[1,5]⟩,⟨.or,[3,8]⟩,⟨.and,[7,11]⟩,⟨.or,[10,11]⟩,⟨.and,[9,13]⟩,⟨.or,[12,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4274580168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4274580168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15965

open PEqualNP.Outside.L_meta_15965 in
theorem PEqualNP.Outside.L_meta_15965 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4274580168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4274580168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
