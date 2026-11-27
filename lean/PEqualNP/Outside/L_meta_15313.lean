import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15313.Model
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


end PEqualNP.Outside.L_meta_15313.Model

namespace PEqualNP.Outside.L_meta_15313
open PEqualNP.Outside.L_meta_15313.Model
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

def SBf (j : Nat) : Nat := [2, 4, 5, 5, 5, 7].getD j 0

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

end PEqualNP.Outside.L_meta_15313

namespace PEqualNP.Outside.L_meta_15313
open PEqualNP.Outside.L_meta_15313.Model
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
end PEqualNP.Outside.L_meta_15313
namespace PEqualNP.Outside.L_meta_15313
open PEqualNP.Outside.L_meta_15313.Model
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
  | 2 => 0xf83fff803fe00ff803fffc03fc07f80ff98c7
  | 3 => 0xffc1ffffc0000ffffc01fffc0007fff01e0f8
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | 5 => 0xf0001fffffffff0000001fffffff800001ff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x41108259148a8618948a434acacca5a54aab5b
  | 2 => 0xd27504af512daa6953ac8de82d546a94ed98c5
  | 3 => 0xe423a9325ba9d4b25929d6ed6828737629e0e8
  | 4 => 0x884211c4623118c4623118b1b1b15c58b155b6
  | 5 => 0xf7bde0783c1e0f87c3e1f3e3e3e6060c1fe00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaa0000aaa00000aaaa0000aaa00000aaaa0000aaa00000aaaa0000aaa00000aaaa0000aaa00000aaaa0000aaa00000aaaa0000aaa00000aaaa0000aaa00000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15313
namespace PEqualNP.Outside.L_meta_15313
open PEqualNP.Outside.L_meta_15313.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x3fff007f807fffc03fff80fe01fff80ff9c7c7
  | 3 => 0xffffff80007fffffffffff0001fffffffe07ff
  | 4 => 0xc3ffffffff807fffc03ffffffe03fff00ff8f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4b249083048c4484868b166a2c5a9692db5b
  | 1 => 0x5095ec25552d34a3a91bc0aaa956a98ba9c5c5
  | 3 => 0x212649746a4a5929322d5581419b372d4e06ae
  | 4 => 0x36388e464c6c623223b1e6cd8d03c5c18d68f0
  | 5 => 0xbbc0f07870707c3c3c3e78f1f1e2060e0fb700
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xaaaa8800aa008800aaaa8800aa008800aaaa8800aa008800aaaa8800aa008800aaaa8800aa008800aaaa8800aa008800aaaa8800aa008800aaaa8800aa008800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15313
namespace PEqualNP.Outside.L_meta_15313
open PEqualNP.Outside.L_meta_15313.Model
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
  | 1 => 0x3fff007f807fffc03fff80fe01fff80ff9c7c7
  | 2 => 0xffffff80007fffffffffff0001fffffffe07ff
  | 4 => 0xc3ffffffff807fffc03ffffffe03fff00ff8f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4b249083048c4484868b166a2c5a9692db5b
  | 1 => 0x5095ec25552d34a3a91bc0aaa956a98ba9c5c5
  | 2 => 0x212649746a4a5929322d5581419b372d4e06ae
  | 4 => 0x36388e464c6c623223b1e6cd8d03c5c18d68f0
  | 5 => 0xbbc0f07870707c3c3c3e78f1f1e2060e0fb700
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xaaaa8080a0a08080aaaa8080a0a08080aaaa8080a0a08080aaaa8080a0a08080aaaa8080a0a08080aaaa8080a0a08080aaaa8080a0a08080aaaa8080a0a08080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15313
namespace PEqualNP.Outside.L_meta_15313
open PEqualNP.Outside.L_meta_15313.Model
def s4K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x10a01800280ef18dc31dc43b087d887810
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8800310c421d031043808410
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*4) 4
  | 3 => packedAt s4K3 (i*15) 15
  | 2 => packedAt s4K2 (i*26) 26
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (5+((h/1+packedAt s4K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s4K3 (98+((h/2+packedAt s4K3 (90+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt s4K2 (81+((h/1+packedAt s4K2 (78+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 3 => 0xefff0fffc3f8
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff41e222e2661b
  | 1 => 0xffffffffffffffffffffffffff0224454488ed
  | 2 => 0x244e89aa3346
  | 3 => 0x1888ee3323b0
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 15 s4Pos s4Neg, 0xc880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15313
namespace PEqualNP.Outside.L_meta_15313
open PEqualNP.Outside.L_meta_15313.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x248060a30a000302380071658000268489b34001064e00ba91e10a2a4c54e803c711900a215804a25200007cc8d4404001608968005f040042ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x254c183c95586cc07821345114d92cb905500058300000c548000000000000013c00f4000000000400013000b49cf0908518a1440000000c8cbcb00000c8004ca829200011416101112800656964141c748870e954440048cc08e0005c000138f800000000d4540060000000007ce524a4415c80dc00fcd0382d0cac0108ec0000991c68340004081c041c16001e00002e0c000000022a002604001400060a0a00060b7651d0eeaa3a1dd94742baa8e853f544ca78a8995dd4532ba28a657b504caf0a099734c8329f286833d54906bea6a0d714d41b7a92836c52506f6a0a0de14141cfa9a839c535075ea4a0eb14941dba8a83bb5050678a0a0ee141419c282833e54106dca598db54b31daa0e633e548c67aa918cf950319eaa063b5410c6bca790d754f21daa0e433e548867aa910cf950219eaa043b5410867aa3204f94240bb2888175511036ca2204f54440daa888135511027ca0206e940409f2a6613d54cc27ea8984f15130b7a92616c524c2eea2985d14530b7290616d520c27ca9904f553209faa2413c54482bea6905714d20bba8a417451482bca6105754c209f2a6213d54c436a83886e103109faa4213c548427ea8884f15110afa9a215c53442dea4885b14910daa0a213e540427aa8086e10010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xc106800282ae000002486222398aa678052c300724584814200087306c8604c832c314c525071b5314141c614c505072b5214141ca14850507265250731ac18141cc6b06050431c594d41c86b06050721ac18141087176354440c518d51103276254440c9189511033060544408d58654cc2356195320ac18141c42b161103108d19541443145350510c914941442396510010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x18020000000801001889486050731c24a63028390e04631895110308318c0a8881881886054440
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
  | 4 => packedAt s5K4 (2697+((h/30+packedAt s5K4 (2457+(h % 30)*8) 8) % 133)*8) 8
  | 3 => packedAt s5K3 (990+((h/8+packedAt s5K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (250+((h/1+packedAt s5K2 (245+(h % 1)*5) 5) % 19)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffffffffc07ffff03fffffffff01ffe3ffe3f
  | 1 => 0x3f80fe03fffffffffc0fc07e03ffffffcc63ff
  | 2 => 0xc000fffffff80ffffff0007fffffe07ff07fc7
  | 3 => 0xffff0003fffff01fffffff8003ffff81ff83f8
  | 4 => 0xfffffffc0000001ffffffffffc000001fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x448612284471224300b2ca9654b10cb215ae1b
  | 1 => 0x112a4499c892448e2c05582ac1563964cc60ed
  | 2 => 0xb45498529120e9155550224d9a6b4459705746
  | 3 => 0x2618d163224481d99a69b301138d9611ba83b0
  | 4 => 0x3860e183c3870e1ee38e3c71e00e1861ef7800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeaa0c880eaa0c880eaa0c880eaa0c880eaa0c880eaa0c880eaa0c880eaa0c880eaa0c880eaa0c880eaa0c880eaa0c880eaa0c880eaa0c880eaa0c880eaa0c880, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15313
namespace PEqualNP.Outside.L_meta_15313
open PEqualNP.Outside.L_meta_15313.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x9c1000000000050400f40048f85800a8003c68b05c00e090740098c50108a0d820e4240060282c0030540080ecd4cc6c00407000008c00000000f11408886400ac00847cc0184c50350ce8441cfc78d0a40c14b894dc3910bcb40000c8081091000633000000100000890200203060c00400ffd5003fe54005f95003fd5400ff150037c5400ffd4c037f5300ff94c03fd53005f54c03fc53007fd0c01fe43007f50c01fc4300ffd48037f5200ff94803fd52005f54803fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc3200ffd4403fe5100ff54403fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc2100ffd4003fe50005f94003fd5000ff140037c50007fd0001fe40006f90001fd40007f10001bc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x1a4006bf18d20007b8c690002dc6348017bfa9a4000df54d2005efea4900037d5248001f71924000fb4c920005fec290003f761480017bb0a4000bf18520007e8c290002f46148001bf282400bdf141200077c8090003bc404800bfd9024000fb8812002dfeca10006fe650800bbf32840019f9942004dfaca100177d65080013eb284005bf1942002dfec81001efe64080017eb204005bf19020006fca8100277c540800b7fb184006bf98c2002fbcc610002de63080017eb184005f758c20005bac610016fc6308013bfa984000df54c2002dfcc4100177f520800bbea904000fbcc82002fd86410002fe61080017eb084000fb8842002fd8421002afe6008001bf2804009df140200077c8010003bc400800bf79004005fe88020007da4010017f920080097fb2e2001bf99710026fccb880067e65c40097eb2e2000df59710004facb88006fc65c40017fb262007bf993100077cc988002be64c40017eb262000ef593100057ac98801efc64c4001bf2a62004df15310005fec78801afe63c40017eb1e2006bf18f10026fea7880037d53c40017fb162005bf98b10005fac588016fc62c4009bfa962000df54b10007ec8388003f541c4001bf2862004df14310007f68188003be40c4001de2062000fe1031000770818800eff65840037f32c2003bf5961000df8cb08002ff648400f7f3242000bf5921003df8c9080037e5484007be2a42000bfd8e10035fcc708002fd638400d7e31c2003dfd4e10006faa708002ff628400b7f3142000bf58a1002df8c50800f7f5284001bea942008bf58610007ee6308003f43184001fb90c2000fd08610015fcc1080037e5084007be2842000ef90210007788108003f71084001fd8842008bfd9510006feca880027f65440037f32a2008bf5951000df8ca880237c65440033e32a2000bfd91100077ec888002bf644400f7f3222000bf5911003df8c888003bc64440015e3222000df95110046f8a888002ff6344001efb1a2000b7d8d10035fcc688002fd634400d7e31a2000f718d10005b8c6880237f5344001bea9a2000bfd8910007dec488002ef624400b7f3122000bf5891002df8c488003ec6244001763122008dfd4910006faa488003f64144001faa0a2000df94110046f8a088003be4044001de2022000fec4110007ec208800aff65040037f3282002bf5941000df8ca08002ff640400f7f3202000bf5901003df8c8080037e5404005be2a02000bfd8c10035fcc608002fd630400d7e3182002dfd4c10006faa608002ff620400b7f3102000bf5881002df8c40800b7f5204001bea902004bf98410007ee6208003f43104001fb9082000fd0841001dfcc0080037e5004005be2802000fed00100077c8008003bc4004001fc2002000ee10010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0xb7d53cc00b7f3166000bf58b30086fea5980037d52cc00def9966000f74cb30005fcc398002fd61cc001bf2866010df143300077c8198003bc40cc01d7fb2c6000dfd9630004fecb18006fe658c01d7eb2c6001bf19630076f8cb180067c658c0017fb246007bf99230005fac91801efc648c001bf2a4600edf1523007dfac71803b7f538c001bea9c6005bf98a30005fac51803b7f528c001bea946000f78ca30007b86518002fe618c0017eb0c6000f78c630007b8631801afe608c001bf284600edf142300077c8118003bc408c001ef9846006fecc23007dfeca980037f654c0013fb2a6001bf9953007dfaca98006fc654c01fbe32a60019f19530005fec898003bf644c0015fb226007bf99130005fac89801efc644c001de3226000af19130006fca89803f7c544c01fbfa9a6000df54d30005fec498003ef624c00177b126005bf18930007d8c498002ec624c01fbfa926000df54930007be6498003dd324c0017fb0a6000fdd8530005eec298002fc614c001fa30a6000bd18530006fca09803f7c504c001df2026000ef10130037f66098003de304c00d7fb286001bf99430036fcca180067e650c01b7eb286006df59430004faca1801afc650c00d7fb206007bf99030005fac81801afc640c001bf2a0600ddf15030035fcc61801b7f530c00dbea986005bf98830037dcc418002ee620c0017eb106006fb58830005dac4180377f520c001bea906000f78c830037b86418002fe610c0017eb086000f78c430037b8621803afe600c001bf280600ddf140300077c8018003bc400c00def9806006fe8c030007ba601801bf9300c00b7fb2e4001bf9972002efccb900067e65c80197eb2e4005df59720004facb90016fc65c800b7fb264007bf9932002f7cc990002be64c80017eb264005ef593200057ac990016fc64c8001bf2a6400cdf1532002dfec79001afe63c80017eb1e4005bf18f20066fea7900037d53c800bbfa964005df54b2002fdc6590003ed32c80017f30e4000bf58720006fca1900337c50c8001df2064000ef10320055fecb100037f65880013fb2c4001bf99620055facb10006fc6588015be32c40019f19620005fec91001efe64880017eb244007bf19220006fca91002b7c54880017fb1c4006bf98e20005fac71001afc6388015bfa9c4000df54e2005dfac51002b7f5288001bea944000fbcca20007d86510002fe61880017eb0c4000fb88620007d84310016fe6088001bf284400adf142200077c8110003bc4088001f79044005fec822005dfeca900037f65480013fb2a4001bf9952005dfaca90006fc6548017be32a40019f19520005fec890003bf64480015fb224007bf99120005fac89001efc6448001de3224000af19120006fca89002f7c54480017fb1a4000f7d8d20005bec69001afe63480017eb
  | 2 => 0x40005fac52004b7f5290001bea948000efd0a400077c8520003bd4290001de2148000bf98640005fac320003bf4190001df20c8000ef5064000778832001efe6090001bf2848012df142400077e812001ffb4090025dfb2c8012ef996400967ccb2004bbd65900019eb2c8012ef196400077ec720003be6390001deb1c8000ef18e400977ea72004b3f5390025df29c8012ef54e400067aa72004bbc5390001dfb148000ef98a400077ac520003bc6290025dfa948012cfd4a400977ca52004bbd52900019ea948012ef14a400077e6520003be3290001de9948000ef0ca400077ec320003be6190001deb0c8000ef186400977ea32004bbe5190025dea8c8012ef146400077e6320003be3190001de98c8000ef0c6400077e4320003be2190001de90c8000ef0864008d7cc12004bbf5090025df2848000cf942400977aa12004bbc50900259e2848013bfd9540006fecaa00027f65500037f32a8013bf5954000df8caa004f7c65500033e32a8007df9514003ef8a8a0002ff635000d7e31a8013dfd4d40006faa6a0002ff625000b7e3128013dfd4940006faa4a0002ff61500017e30a8000df9414009ef8a0a001ffb4050001df2028007bfd944003efeca2001e7f65100037f3288011bf5944003df8ca2001f7c651000f3e3288007bf9904008f7ea82001f7e541000fdf2a08007cf9504008f7aa82001f7c541000fde2a08007cf15040035fcc620002fd6310023bfa988000df54c4003f7e8620003be4310001dea188007ef10c4002dfcc420002fd6210023bfa908000df5484003f7e8420003be4210001dea108007ef10840005fcc22001ff661100017b3088000bf5844003feac220002f5611000fdfa088000ef904400077a822001fbc41100257f3008000df9404008ef8a02001fbf401000ffd2008000ef5004003ff2802001fbf651000f9fb288011ef9944008f7aca2001fbc651000f9e3288007efd8c400077cc620003bd631000fde3188011efd4c4008e7ea620047be5310023dea988000cf54c4008f78a62001fbf6210001df3108000ef5884003f78c420047bf52100239fa908011ef9484008f7aa4200033d5210023de2908000efcc8400077c6420003bd3210001de1908007efd84400077cc220003b66110001deb088000ed5844003f78c220047bf5110023df2888011ef5444008f78a220003bf3110001df1888000ef4c440007786220003bf2110001df1088000ef48440007784220003be60100255f3008000ee9804008f7ea020047be50100019f2808011ef5404008f78a0200473c501000d7fb2e6001bf99730036fccb980067e65cc0217eb2e6006df59730004facb9801afc65cc00d7fb266007bf993300377cc998002be64cc0017eb266006ef593300057ac99801afc64cc001bf2a66010df15330036fea79801
  | 3 => 0xeb2e4205bf1972102dfec99081efe64c84017eb264205bf19321006fca9908637c54c840b7fb1e4206bf98f2102fbcc790802de63c84017eb1e4205f758f21005bac790816fc63c8431bfa9e4200df54f2102efea5908177d52c8401fb20e4200fd50721007ee6390803f431c84017f3064200bf583210c6f8a19085aff65884037f32c4216bf5962100df8cb10802ff648840f7f3244200bf5922103df8c9108037e548842dbe2a44200bfd8e21035fcc710802fd638840d7e31c4216dfd4e21006faa71085efd628842dbfa944216fb94a21006faa51085bed5288401b6a944200fbd0a21007d88510803ee3288401f69944205bf98621007de4310817f721884017f3044200bf582210b6f8a11085eff65484037f32a4217bf5952100df8ca90802ff644840f7f3224200bf5912103df8c8908037e544842fbe2a24200bfd8d21035fcc690802fd634840d7e31a4217dfd4d21006faa69085f7f5248401bea924205fdc8521007dc4290802ff60484017e3024217df1412102dfeca10806fe650840bbf32842019f994210adfaca108177d65084013eb284205bf1942102dfec81081efe640840bdf3204200af99021005fac810817bd64084015eb204205bf19021006fca8108577c540840b7fb184206bf98c21005fac610816fc630842bbfa984200df54c2102dfcc4108177f520840bf72904205df548210afdaa4108036d5208401f7a104205fb1082102fdc6410803ed320842d7f3084200fd90421007ea8210803f73108401fa1884205fbc842102fec4210803ed210840bfa9084200bf98021005fac0108577c5008401bfb24a000df9925003cfcc9280037d6494001be324a000dfd8e50006fcc7280037d63940013eb1ca000df18e50006fe87280037e4394001bea1ca000df10e50006fec5280037e6294001beb14a0009f58a50006f8c5280037f4294001bf214a000df50a50006f885280037f3294001bf194a000df4ca50006f865280037f6194001bf30ca000df58650006f8c3280037f4194001bf20ca000df50650006f883280037f3194001bf18ca000df4c650006f863280037f2194001bf10ca000df48650006f843280077e60940033f304a001de9825003dfecba0006fe65d000fbf32e80019f997400a5facba001f7d65d00013eb2e8007bf1974003efca9a001f7c54d000d7f31e8000bf58f400a6fea7a00037d53d000b7f3168000bf58b400a6fea5a00037d52d00017f30e8000bf58740006fca1a00537c50d00257fb2c8001bf99640096fccb200067e65900257eb2c8000df59640004facb20006fc65900277eb248012efd524003efca92004bbe54900019f2a48012ef5524003ef8a92004bbc54900259e2a48006bf98e40005fac72004b7f5390001bea9c8000efd0e400077c8720003bd4390001de21c8005bf98a
  | 4 => 0x802fe60d04017eb068220df143410f5fecb20806fe659043dbf32c82019f996410f5facb208037d65904013eb2c8201bf196410fdfac92081f7e549040fbe2a48206bf98e41005fac72087b7f5390401bea9c8205bf98a41005fac52087b7f5290401bea948207bf986410077e832081ff741904017f3048200bf582410f6f8a12087eff6550401bfb2a82009fd954100dfccaa087efd65504037e32a821fdf1954100cf8caa087fbf545040fbf2a28207df151410ff78a8a087f3c54504017fb1a8200f7d8d41005bec6a081afc6350401ee31a8200b718d410fefea6a08037d5350401dfa1a8200ef50d41005fec4a0803ef625040177b128205bf18941007d8c4a0802ec625043fbfa928200df549410077e84a0803bd425040ffba0a8200ef90541005fec0a0803fb60504017db028200bf18141007f0c0a0802f8605043fbe2828207bfd944100dfcca20876fd651040f7e3288207bf9904103efca82081f7c541040d7f3188200bf58c410eefea6208037d531040b7f3108200bf588410eefea4208037d521043d7f3088207efd044103fec8220803bd411040ffaa088200bf98041005fac0208777c501040d7fb2e6201bf99731036fccb988067e65cc4397eb2e6206df59731004facb9881afc65cc40d7fb266207bf99331005fac99881afc64cc401bf2a6621cdf15331036fea79881b7d53cc40b7f3166206fb98b31005dcc598802fd62cc40df6b166200bb58b310e6fea5988037d52cc401fb20e6200fd50731005fcc198802fd60cc439be286621abfd963100dfccb1886afd658c4037e32c6200bfd923103dfcc918802fd648c40f7e3246200df952310d6f8a91886efd638c435bfa9c621af794e31006faa71886bdd538c401aea9c6200f7d0e31007b88718816fe628c4017eb14621adfd4a31006faa518803df328c401ee9946206bf98631007be631881bf7318c4017f3046200bf582310d6f8a11886eff654c4037f32a621bbf5953100df8ca98802ff644c40f7f3226200bf5913103df8c8988037e544c437be2a2621bdfd4d31006faa698802ff624c40b7e312621bdfd4931006faa49881bf7314c401ef18a6200bfd8131005f8c09886f7c504c40d7fb286201bf99431036fcca188067e650c4337eb286206df59431004faca1881afc650c40d7fb206207bf990310377cc818802be640c4017eb206206ef590310057ac81881afc640c401bf2a06219df15031035fcc61881b7f530c40def2986206df54c310cfbaa6188035d530c401efa186206f710c3102dfcc418802fd620c433bfa906200df54831037be6418803dd320c4357f3086200fd90431007ea821881bdf310c40dfb1886200f74c431037ea6218802fe600c4017eb006219df1403102dfecb90806fe65c840bbf32e42019f997210c5facb908177d65c84013
  | 5 => 0x534203ef8a9a101afe63d08017eb1e8428dfd4f42006faa7a10a37f52d0801bea968400bf9874203fecc3a1002f661d08017eb0e8407fd58742005eac3a1002fe60d08017eb068428df1434202dfecb21006fe659080bbf32c84019f9964213dfacb210177d65908013eb2c8405bf19642135fac92101f7e549080fbe2a48406bf98e42005fac72109f7f5390801bea9c8405bf98a4202efea5210177d529080bdfa148407fbd0a42005fcc321002fd61908017f3048400bf5824213ef8a12109aff6550801bfb2a84009fd954200dfccaa109afd65508037e32a8426df1954200cf8caa101f7e545080fbe2a28400bfd8d42035f8c6a109b7f5350801bea9a8426dfd4942006faa4a101fef425080bdf2128400bfd8542005f8c2a1002ff60508017e3028426df1414202dfeca21006fe651080bbf32884019f9944212dfaca210177d65108013eb288405bf1944203dfcc82101f7e541080fbe2a08406bf98c42005fac6210977f5310801bea988405bf9884202efea4210177d521080bdfa108405fb9084202f7a842101fed42108017f3088400bf58442005fcc021002fd601084bbe2808406bfd973200dfccb9901b7e65cc8033f32e6424bf59732036facb990027d65cc80d7e32e6406bfd933203dfcc999002fd64cc80d7e3266400df95332126f8a99901b7f53cc80dbea9e6424dfd4b32006faa599002fe61cc8017eb0e6400bf98332005fac1990937c50cc80b7fb2c6401bf9963202efccb190067e658c8477eb2c6405df59632004facb19016fc658c80b7fb246407bf99232005fac919016fc648c801bf2a46423df15232115fac71908f7f538c801bea9c6405bf98a3202efea5190177d528c80bef9946406fbcca32005fcc319002fd618c8017f3046400bf5823211ef8a11908aff654c8037f32a6422df9953200cfcca9908afd654c801beb2a64009f5953200df8ca99002ff644c80f7f3226400bf5913203df8c8990037e544c845be2a26422dfd4d32006faa69908b7f524c801bea926406fbcc93202fbc6499002ff614c801fbb0a6400bdd8532005f8c299003f4614c8017a30a6400bfd8132005f8c09908b7c504c80b7fb286401bf9943202efcca190067e650c8437eb286405df59432004faca19016fc650c80b7fb206407bf99032005fac819016fc640c801bf2a06421df15032035fcc61901b7f530c80dbea986405bf9883202efea4190177d520c80bef9906405fb8c83202fba641901bed320c801e69906400bf98432005fac219002fe600c8017eb006421df1403203dfecba0806fe65d04417eb2e8207bf197411077ea9a081f7e54d040fbe2a68207ef1534103e78a9a081afe63d04017eb1e8220dfd4f41006faa7a081fbf43d0401dea1e8205bf98b41005fac5a08837f52d0401bea968207efd0b410077a85a0
  | 6 => 0x180502e02402800000000000070061000300200a018000000000040080200001c0c8030020200000100a0080180a00000002024028008008220000100180201800400800006060068020080042c8010000100880b0040081a800006010010050140040180a00e0000d8120020140200100400401010002008000080080280980100200c0280000401c000150000740b00000000c00007008008018000120000300b00e0300b8020040240080100400003800000008000000080141d8010060180000200e0000080601402400009008000040320040080101f7e649500f3f324a807cf9925403efec72a01f7e639500fbeb1ca8009f58e5403ef8c72a01f7f629500fbf314a807df58a54004fac52a01f7c629500fbfb0ca807df9865403efac32a01f7c619500fbfb04a807df98254004fcc12a01f7d609500fbe304a800dfd9153006fcc8a98037d6454c01be322a6079f1915300efec6a98067f6354c03afb1aa600dfd8953004fec4a98037e6254c01beb12a600df18953006fec2a98037e6154c01beb0aa600df18553006fec0a98037e6054c01beb02a600df18153004f8c0a981eff65d0c0fbfb2e86079fd974300dfccba18b2fd65d0c0f7e32e8607df1974303cf8cba181f7e54d0c0fbe2a6862cdfd4f43006faa7a1816fe62d0c017eb16862cdfd4b43005fcc3a181ff661d0c017b30e8600bf5874303feac3a1802f561d0c017f3068600bf58343166f8a1a181aff6590c037f32c8606df9964300cfccb218aefd6590c0dbeb2c86009f59643035f8cb218aafd6490c0fbf2a48607df15243035fcc72181b7f5390c0dbea9c8606efd0e4303fbe8721816fe6290c017eb14862bdfd4a43005fcc321802fd6190c017f3048600bf5824315ef8a1218aaff6550c01bfb2a86009fd954300dfccaa18aafd6550c037e32a862adf1954300cf8caa181f7e5450c0fbe2a2862adfd4d43006faa6a181fdf4350c0ddf21a8600bfd894302df8c4a18ab7f5250c017fb0a8600bf18543005fec0a1802fc6050c55be2828606bfd944300dfcca2181b7e6510c033f3288629bf59443036faca218027d6510c0d7e3288607bf9904303efca82181f7c5410c0d7f3188606dfd4c43036faa62181bbf4310c0def2188606ef50c4303fba8621816fe6210c017eb108629dfd4843005fcc221802fd6110c017f3008600bf5804314ef8a0218037f6454801bf322a400df59152006f8c8a901e7c6454801bfb1aa4009fd8d52006fcc6a90037d6354801be31aa400dfd0d52006fc86a90037d4354801be21aa401dfd895200cfec4a90076f6254801bfb0aa400df98552006fac2a90037c6154801bfb02a400df98152006fac0a90037c60548013e302a407bfd974203efecba101e7f65d08037f32e8428bf5974203df8cba101f7c65d080f3e32e8407df9
  | 7 => 0x8b000279a4f9039839669b29e72148e000019d80009080022fa4c8001e400000023a9e380000000001f08e80002aa2c2b40001f92d41f28f200021f0a1a290002b021fa9d8980000000000130000001ba00000022e0000898000800c30002e20001daa9c2dc0138a4ab90b400013194b00000000000019e044ae88eeae40400838001b30459040762df0910d58698000a3a0b0b083400680024382011c26ba1c96c0000319a98e81ba8f593d04100012c24e94ba208aa80000005d1659a71bc81da36a760422c287b8830650468001331f397b1f592b10d8f907d10d2ea00000000000000a00027b24287c93a1a487c2bb9dfa8e8dd9c01411eb00000000014e85f8f68000000002e01c50c48000000000002ab80007f11500000009b9d5a810232c80002930df0b28001a59320128000000001450fd1188000000000840001b00b38002b08bf8ad0002d19422198b317685aa462bea5d8c18558891932c00fc89a04a27d0648140329d01e98b79ca23eaeaa609d2acf17ea5b9d92da9050d20cb2e792aa061290289e02a8a0aa4a98f2a60001ce12481980016516d0c02790ba00000005a0000000078002910f19850002578000000fba0e2e60991fd11a00023c0001970740000811d200001d1f010c0c71bd254227050a218000002dd8002eb0ec26d2831cc18ba5625e8b8a829dd9a4290a98acb0ed0568c42b28001ee222ac38ab111847a00ae4968a8c92f15aacc8a59a28ea0938211e49b590885da668e5a4daa826b0c680000700600005801000010008040080040600402600006800008010000130000000000300e0100480100e00000000002050000040040040000700000c000000080241200e000004000230040380000100a0000180100000400000000018018000000000a0000040100580000400c01000004028050380000000000300a000060000000040c00201200c0900b00001c010030b601800009008004048030120000900c00a054020190320000100101202c0c80200200c03800000000008020040080000f010000000120000140080100c0080000e01800002800000008010020000280180001e0440000301400413001002004038000140000280001c004038010000000100a00c0080200c014078010000140200300500008c0580400000800016000018078010260040200402003c0400500200408800012000000000060000080100006c0000b00601c008040020400a8010440103800300000801002002014000050080040000104a0000080301800000800004008140020040080000101401001000002004048010020000080c0820001200200002c0082e0c600c0380400c0080101b00003c028000000080002d00a00005802002000040060000180200a000000030110320300001d0020000980a00400c018020000
  | 8 => 0x480000b862ac589f8001dd2ae80020c8e10a00a983d2be1c9a6f0bb85b13e0ae0a095fa011f40cc8000001cb2b4ade0000c628097f03ea0499483503e2ac98da7329e1d092525c00024d0cb8000fe0000001308001a627a9c69fd9b10119008001c6232800000234a268000002a51112af2d08000002898d08d628027e800181a2d15c0000000001990002a42522a2800097aaaa8bace9179e90000000000002b618280009ca2a9b7a35a110000000eda6ca450641dc0af18e97bad900027680004500026013788480018712e8001a1821a991722a18870c2ad50f52b18100af8000000309681019bb173193a819d302528a23112600003020793691a9c10002e804b0602128a527487990f99f98c8f48108021969b928d1cd89d04084d205856074a7a2dd186a6d83721c0679dc8268001ef16b8190da23201b00004e8000db2d9848882a5095280000023006e00019a0000000000000001f98000001000002b81789048001761fa04d8002020000000000a8a688000000001a6abb0888042ad80000008c000263aaa0de9f48fe9398000002ef1820519df1888bc8431bf80000e80010f00023b8b590805c17d052913006229a7ba070772610d685213920302d9d626a10a8868d4acfa1e2851de00017e219000110a141b68eb13d8f3962a6485b83fabaa121a809b2e0ad7a4808a9bba0b99400020f8fb04414d8290e399b1b39f180000027f2771f52eb9060001610001058000001eba6c1750be2ed81786fa4e0002c189980000006aab995400024000000006380000021600029b90a0000c580009200012e0000000000e08000000501d78721c717f8000002239e68ec87e967800000119947ac4822134a9a1be0470000000d32b799c243001020aab1c3832286134213823a2416e000055093041aad05719192292210280000002e80000000020d81e25c8000f100000000012700003b80025700000016dad6133800000000261925ac103a2341e88001dead700000006caed0b129600000000006f000008acd10e8000000001ac8002a59fe238ac40000000f98002ee8242459ff1f0800000146a7fa890fd8000001ec1561e61cfa6423385808c8000eb8779af83d8e9a9985c8000000000bb0aa14288d80f1f60460962b69db08d18d23d87b28da132098c91c49bf1a30591e5203a49000210ab38188ac96a800113a6e1ea80809e21b8002c697a94d2e1a332258b900020d00000000017795797496301c11200020c15d9b48002d80000000000000000000000000000b22d6a9f8000000f4144870a7880023980e00014402fa288c10ca2db80000013f1cb96180000019080021690b0002420cd8000000000cf0000599c800000003307a291a7105ea52a8c1d88001a784f07894019617a12d2350e90002a6a15a538e78120cc2498001b81c21
  | 9 => 0x8750000f8a051671d680019a9adaa3140aae121894a5e0a29312cda67a9599b9911db814a2c90214e0a7a5694ca4680016b17418900d85e1a02e100018c02614700c9759fc80006c14a9bea230fa8002a98a20851d50000000002bd00003aa5aa2b8028002408002281aaabd9481f115b87585314182c0a92889b8a71ab50001230fc0398f79d404388819c8a42ce2ec80014c153a9a8000a315682d2d10001a3a4c27202c8000000000349810bd1af12a2d30d926f91ea2ea84ada1288001ed8a68cd0000110000001268000cf8f61d70379950000d78fa0002180ff2bf0001b19168001070001510001928032a10d895d0f31a927787f9bc1d10d80ab80012f800054a001582260e18000002750702928002ca1690000000b9a3616c8000ae9ec9d483b0018ac2d20daaac21b2b58000000002bf8000729d80001ae8000d522b2708000e280000026599d0002a7a971490ce80002f1278971ad2510bf1981bd995a821b21d980018426600007a97004ba2790929c99780027803100a84f8f28b52c08000000001e791d2081011079f7a17a4b8809380002d39ea2de9ab2670730000000000e51c2923800154a4180000018984c2cbaaf8000152171b0a582b703f0000b18280b7000000187a2d8162a4a9f000286815871000085a5b0db8000ba98f8098002e511ba3a2978b80b02252ec2df80003c00008180000000021d1efa8a915a738608000588339638000002448000000001140b49798000001b40dc13b9cf1642d2887a222700429370000efa9e8000000002c20bd80006228e0a807e20280019f0002b892ba5915c9b51ab8000dd27c03584e00006a00027594f9358002e90928d3a9411289f0c0800027ac71fb80004915323816f2a000380015f1ae12125f0000000ff83c9f30000000000000000000e3178005145aa0a698d28000049cd26e9181da1c92470000000001880000499698c52d00181e09ee9fb0380002922a90f000000002589e8000e425d1e189507920a0000f819880000011f8d027c80fa4a27288f99008b8002552ba00007da0f15e2882842a727dadca47ae38002101cc9f68a117193280001f97c9b71e801b9a511f23b09c02714602a00006b18e18aa2a1f22a229492400000000000016a0e48ee23f18580000000000001ca06a1a8002caad48172c3007258ab122028709aa4f0001558001c88002b22622308000f70000719d180d038ac9ac7a9805f07684a9772e680023f9b98090000001ffa041998001c7800109891800000000000152068000000000000000036a2128b0688000000000000000d420e95e91600000015086100002e0000000000ca9a11300059f700022f1030002bc2d895b2e294f21a0001570ea8299b61a206d1fc12815a262acc2938de0000360002650ad8739c18958000c98512db26916
  | 10 => 0x11c8391351860f089889406911e01e910296ae98482248d123704cac62631f816212988227e11d96eaee10e0a606d8670008659e1057a8faa39f8a1897293894a06e8668782519fa9802d58dc9d382ba680e608a1fe93a8d197129006612094300c160a318b6abc81a149a412549c3285936170ac925315891708e2018002c89518bc20925010b9c405425988f2e300028393e9848000e893c800106a3d17902b2378e70002488000000001830861ed00000008b0ce0619601149c080009680000017c1ce8d701a8e20b600013c2151ca95000013f8c20dfab30000000168002c52e72390001e20ef28f1439a880006300009dae5a4b0000d980025a00012015515997d80000000000021180018080015902280000025580000000029d00000013b11900000023e24400029b23c90c8000c380000012c86ba951489a08000c780025f9c5a0885391b1aa1e31e28be82480026a89016f8002740c88000000001920c800012d98a16621ea8780b1738001e59ac21d8a719e8e6
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf725911002cec7259110004fb7059110004be76191100063f65191100063c651911003e3f751911003e3c75191100063f53191100063f521911003eb57119110094be701911003cbc70191100063c50191100047e769511003c7c76951100063f649511003e3c649511000c7c75d8d100065f53d8d10034de76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100065f75d8d100065c75d8d100065e54d8d100065c54d8d100065f52d8d100065c50d8d100047f7558d1000c7c7558d10004bf7458d1003cbc7458d10004ef7258d1002cec7258d10004f77158d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d100365e7518d100365d7518d100065e5418d100065c5418d100065f5218d100065c5018d100047e7654d100047c7654d100063f6454d100063c6454d100065f6354d100365c6354d1000c7c75d89100066f52d891002cee76d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066f75d89100066c75d89100066e54d89100066c54d89100066f53d89100066d53d89100066c50d89100047f755891000c7c7558910004bf745891003cbc7458910004df7358910034dc7358910004f77158910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc631891002e6e751891002e6d75189100066e54189100066c54189100066f53189100066d53189100066c50189100047e76549100047c76549100063f64549100063c64549100065f63549100065c63549100066f625491002e6c625491003eb46490510006d46390510006e4629051003cf4765051018f345450510006d46350510006e462505100247e76941100063f64941100063c64941100065f63941100065c63941100066f62941100066c6294110004be76901100063f65901100963c65901100069f63901100069c6390110006af6290110006ac6290110004be76101100063f651011008e3c65101100069f63101100069c6310110006af6210110006ac6210110006b864c4110006d46384110006e4628411000c7e75d90100047d75d90100047f755901000c7c75590100063c5459010005e672cc410004f5760c41000755530c410005d673c8410004f57608410007655208410185ba70900100073a5010010177385010010004f9761001017f3a541001017f385410010006ba7610010006b9761001017f3b751001017f3875100101773b53100100073953100101773b5210010007395210010007b27110010007b1711001016eba6110010007b33110010007b03110010007b32110010007b02110010007b040c401002cf97684010004f77644010005d47344010005e47244010007725044010004fb7644010005b87444010
  | 1 => 0x8c200065c5098c2000c7e7558c200065f5358c2002cec7258c2002ecc3258c20004f77158c20004f47158c200065e7558c200065d7558c200065e5458c200065c5458c2002ecc7258c2002e5f5258c2002e5d5258c20006d77158c20006d47158c2002ecc2158c200065c5058c2002ecf2058c200047f7654c200047d7654c200365e6354c200065d6354c200056f7254c20005787054c20004ed76cc820006cd63cc8200066d6588420006cd63884200547f769402000c7d76940200065e63940200065d63940200056d72940200963e65900200063d65900200069e63900200069d639002008e3e65100200063d65100200069e63100200069d6310020004ef7648020005cc7348020006cd6348020005e471480200076a5048020007a8404802000c7f765971003c7c74597100047f73597100047f725971000c7e75d93100047d75d9310004bd76993100063e65993100063d659931003e3f759931003e3c75993100063f53993100063f529931003eb671993100063c50993100047f755931000c7c75593100063c545931003cbf76593100063e65593100063d65593100063f75593100063c75593100063f53593100063f5259310006bb70593100063c505931003c7f76953100047d769531003e3e64953100063d649531000c7e75d8f100047d75d8f1003cbe74d8f10004bd74d8f1002cee72d8f10004ed72d8f1000c7e7558f100047f7654f100047d7654f100063e6454f100063d6454f1000c7e75d8b100047d75d8b1003cbe74d8b10004bd74d8b10034de73d8b10004dd73d8b1000c7e7558b100047f7654b100047d7654b100063e6454b100063d6454b1003cf5769071003eb6645071019f345450710005f070507100447d76943100063e64943100063d64943100963e65903100063d659031008e3e65103100063d65103100073a501031016f385010310006b964103101973a5410310197385410310005f17110310007b24110310007b14110310005b97610310006b976103101973b751031019738751031016f3a651031000739651031016f3b531031000739531031016f3b5210310007395210310007b27110310007b1711031000c7e75d92100047d75d92100063c54d9210034de73d9210004dd73d921002cee72d9210004ed72d92100047f755921000c7c75592100365e6354e100065d6354e1002e6e6254a100066d6254a10005e672cc61000755530c610005d673c861000765520861000c7e76d951003c7e74d95100047d73d95100047d72d951000c7e70d951000c7c70d951000c7e75d91100047d75d91100063c54d911003cbe76d91100063f65d91100063c65d91100063e75d91100063d75d91100063f53d91100063f52d91100063c50d91100047f755911000c7c7559110004df7359110034dc7359110004e
  | 2 => 0x47e7654e200047c7654e200056f7254e20005787054a20006cf630ca2000c7e75986200047d759862003cbe7498620004bd74986200047f755862000c7c7558620004df7358620034dc73586200066f65886200066f650862000c7e76942200056d72942200063f65902200963c65902200063f651022008e3c651022000c7e76d952003c7e74d95200047d73d952005c7d72d952000c7e75d91200047d75d91200063c54d912003cbe76d91200063f65d91200063c65d91200063e75d91200063d75d91200063f53d91200063f52d91200063c50d91200047f755912000c7c7559120004df7359120034dc7359120004f77159120004f47159120004be76191200063f65191200063c651912003e3f751912003e3c75191200063f53191200063f52191200063c50191200047e769512003c7c76951200063f649512003e3c649512000c7c75d8d200065f53d8d20034de76d8d200065f65d8d200065c65d8d200069f64d8d200069c64d8d200065f75d8d200065c75d8d200065e54d8d200065c54d8d200065f52d8d200065c50d8d200047f7558d2000c7c7558d20004bf7458d2003cbc7458d20004ef7258d20004f77158d20004f47158d20004de7618d200065f6518d200065c6518d200069f6418d200069c6418d200365e7518d200365d7518d200065e5418d200065c5418d20036cd7218d200065f5218d200065c5018d200047e7654d200047c7654d200063f6454d200063c6454d200065f6354d200365c6354d2000c7c76549200063f64549200063c64549200065f63549200065c635492000578705492002f682054920004ee768c920036cc638c920034ec764c920036cc634c920005e8704c9200067765d85200067465d8520006b764d8520006b464d8520006d763d8520006d463d85200067654d85200067454d85200067753d85200067553d85200067752d85200067552d85200067450d8520006776518520006746518520006b76418520006b46418520006d76318520006d46318520006765418520006745418520006775318520006755318520006775218520006755218520006e63218520006e532185200067450185200647e76941200063f64941200063c64941200065f63941200065c6394120006776194120006746194120004be76901200063f65901200963c65901200069f63901200069c6390120006b76190120006b46190120004be76101200063f651012008e3c65101200069f63101200069c6310120006b76110120006b46110120006cc6388120006e4618812003c7c74594200047f735942002c7f725942002c7d725942002e6c215942004c7c70594200047f755902000c7c755902003c7f76950200047d76950200365e7598c200365d7598c200065e5498c200065c5498c2002e5f5298c2002e5d529
  | 3 => 0xc6254930004de76cc93002ecc62cc93002cdc764c93002ecc624c930005d8704c9300067765d85300067465d8530006b764d8530006b464d8530006e762d8530006e462d85300067654d85300067454d85300067753d85300067553d85300067752d85300067552d85300067450d8530006776518530006746518530006b76418530006b46418530006e76218530006e46218530006765418530006745418530006775318530006755318530006775218530006755218530006d73218530006d532185300067450185300847e76941300063f64941300063c64941300066f62941300066c6294130006776194130006746194130004be76901300063f65901300963c6590130006af6290130006ac6290130006b76190130006b46190130004be76101300063f651013008e3c6510130006af6210130006ac6210130006b76110130006b46110130006cc628c130006d4618c13003c7c74594300347f73594300347d73594300047f72594300365c315943006c7c70594300047f755903000c7c755903003c7f76950300047d769503002e6e759883002e6d75988300066e54988300066c54988300366f53988300366d53988300066c509883000c7e75588300066f5258830036cc3258830004f77158830004f471588300066e75588300066d75588300066e54588300066c54588300366f53588300366d5358830006e77158830006e47158830036cc31588300066c5058830036cf30588300047f76548300047d76548300055f735483002e6e62548300066d6254830005787054830004dd768c830006cd628c8300065d658c430006cd628c4300747f769403000c7d76940300055d73940300066e62940300066d62940300963e65900300063d6590030006ae6290030006ad629003008e3e65100300063d6510030006ae6210030006ad6210030004df764c030005cc724c030006cd624c030005d4714c0300075a504c03000798404c03003c7c74597200047f735972003e3f759932003e3c75993200063f539932002e3f529932002e3d529932003eb6719932003eb571993200063c50993200047f755932000c7c75593200063c54593200063f75593200063c75593200063f535932002e3f525932002e3d52593200063c505932003c7f76953200047d769532003e3e64953200063d649532000c7e7558f200047f7654f200047d7654f200063e6454f200063d6454f20005787054f2002ecc634cb2005c7d76943200063e64943200063d64943200963e65903200063d659032008e3e65103200063d651032003c7e74d96200047d73d96200066d72d96200067a70d962000c7e75d92200047d75d92200047f755922000c7c75592200047e769522003c7c769522000c7c75d8e20004f671d8e20004f571d8e200047f7558e2000c7c7558e20
  | 4 => 0x8440005b8704844003cbe7608440004bd760844008d3e75084400053d75084400072d520844008d3e75980400053d759804003e3f659804003e3c6598040006b66198040006b561980401a73850980401a73a759804000739759804003f3b659804003f3865980401a73b53980400073953980401a73b5298040007395298040005ba719804003fb2619804003fb1619804003d3e769404003d3c76940400053d73940400053d729404000736619404000735619404008d3e709404008f3a70940400963e60940400073a609404003c7c74597300047f725973003e3f759933003e3c75993300363f53993300363d53993300063f529933003eb6719933003eb571993300063c50993300047f755933000c7c75593300063c54593300063f75593300063c75593300363f53593300363d53593300063f52593300063c505933003c7f76953300047d769533003e3e64953300063d649533000c7e7558b300047f7654b300047d7654b300063e6454b300063d6454b30005787054b3007c7d76943300063e64943300063d64943300963e65903300063d659033008e3e65103300063d651033003c7e74d96300065d73d96300047d72d96300067a70d963000c7e75d92300047d75d92300047f755923000c7c75592300047e769523003c7c7695230005787054e300375b3054e300047f7558a3000c7c7558a300047c7654a300055f7354a3000c7e75986300047d759863003cbe7498630004bd74986300047f755863000c7c7558630004ef725863002cec72586300065f658c6300065f650c63000c7e76942300055d73942300063f65902300963c65902300063f651023008e3c65102300075a50cc23000c7e76d953003c7e74d953007c7d73d95300047d72d953000c7e75d91300047d75d91300063c54d913003cbe76d91300063f65d91300063c65d91300063e75d91300063d75d91300063f53d91300063f52d91300063c50d91300047f755913000c7c7559130004ef725913002cec7259130004f77159130004f47159130004be76191300063f65191300063c651913003e3f751913003e3c75191300063f53191300063f52191300063c50191300047e769513003c7c76951300063f649513003e3c649513000c7c7654d300063f6454d300063c6454d30005787054d30037583054d3000c7c75d89300066f52d89300066f65d89300066c65d8930006af64d8930006ac64d89300066f75d89300066c75d89300066e54d89300066c54d89300066f53d89300066d53d89300066c50d89300066f65189300066c6518930006af6418930006ac641893002e6e751893002e6d75189300066e54189300066c54189300066f53189300066d53189300066c50189300047e76549300047c76549300063f64549300063c64549300066f625493002e6
  | 5 => 0x8d3e75908400053d75908400053f755084008d3c755084000c7e75984400047d759844000676759844000675759844003e76549844003e7454984400067753984400067553984400067752984400067552984400067450984400047f755844000c7c755844003e3c5458440004df7358440034dc7358440004ef725844002cec725844003eb44158440006777558440006747558440006b7545844003e76545844003e74545844003eb4545844003e345458440006d77358440006d4735844000677535844000675535844003eb74358440006b54358440006e77258440006e4725844000677525844000675525844003eb74258440006b54258440006f0705844000674505844008d3e75904400053d7590440006b561904400053f755044008d3c755044003e3c65504400059f73504400059c7350440005af7250440005ac7250440006b66150440005bb705044003c7e769404003c7c769404003d3e7494040006766194040006756194040004bf76500400053f755004008d3c755004008d3e7598c400053d7598c400053f7558c4008d3c7558c4003d3e7654c4003d3c7654c4008d3f7354c4008f1f7354c400071e6354c400071d6354c400053f7254c400053c7054c400963e6054c4008d3e75988400053d75988400053f755884008d3c755884003d3e765484003d3c76548400053f735484008d3f725484008f2f72548400072e62548400072d62548400053c70548400963e605484008d3e75cc8400053d75cc84008d3e758c8400053d758c84008d3e754c8400053d754c840005b7714c840005b4714c840005bb704c840005b8704c84008d3e750c8400053d750c8400078d320c840005ba700c840005b9700c84008d3e75984400053d759844003db5769844000736759844000735759844003f37659844003f346598440007375398440007355398440007375298440007355298440007b070984400073450984400053f755844008d3c755844003e3c65584400059f73584400059c7358440005af7258440005ac725844003eb4615844003db77658440006b7765844000737755844000734755844003f376558440006b6655844003eb4655844003f34655844003e34655844000797735844000794735844003eb76358440006b56358440007375358440007355358440007a77258440007a4725844003eb76258440006b56258440007375258440007355258440007b0705844000734505844008d3e75cc4400053d75cc440005ae72cc440005ad72cc440005ba70cc440005b970cc4400071d538c440005bb704c440005b8704c44003cbe760c440004bd760c44008d3e750c4400053d750c4400071d530c44008d3e75c84400053d75c84400059e73c84400059d73c8440005ba70c8440005b970c84400072d5288440005bb704
  | 6 => 0xc75d0e40005b671d0e40005b571d0e400953e7590e400053d7590e40034bf7650e400053f7550e400953c7550e400953e7510e400053d7510e4000c7e7558a40004f77158a40004f47158a400047f7654a400047d7654a4003d3c7454a4003d3f75d0a4003d3c75d0a40005b671d0a40005b571d0a400953e7590a400053d7590a4002cbf7650a400053f7550a400953c7550a400953e7510a400053d7510a400063c54586401063e65d06400953e75906400053d75906400053f75506400953c75506400fe3e65506400059f73506400059c7350640005af7250640005ac7250640006b6615064003c7d769424003d3e74942400953e75d02400053d75d02400073a50d02400953f76596400963f76596400053f73596400053f72596400953c70596400953e75d8e400053d75d8e40005ba70d8e400953e7598e400053d7598e400953e7558e40005b77158e40005b47158e400953e7518e400053d7518e40005ae7218e40005ad7218e40005ba7018e400053f7654e400053d7654e400953f7354e400971f7354e400053f7254e400053c7054e4008e3e6054e400953e75d8a400053d75d8a40005ba70d8a400953e7598a400053d7598a400953e7558a40005b77158a40005b47158a400953e7518a400053d7518a400059e7318a400059d7318a40005ba7018a400053f7654a400053d7654a400053f7354a400953f7254a400972f7254a400053c7054a4008e3e6054a400953e75cca400053d75cca400953e758ca400053d758ca400953e754ca400053d754ca40005b7714ca40005b4714ca400953e750ca400053d750ca400078d320ca400953e75d86400053d75d86400063e65d86400059e73d86400059d73d8640005ae72d8640005ad72d8640005ba70d8640006b761986400063e65586400953e75186400053d7518640005ba70186400953e75cc6400053d75cc640005ae72cc640005ad72cc6400071d538c640004be760c640004bd760c6400953e750c6400053d750c6400071d530c6400953e75c86400053d75c86400059e73c86400059d73c86400072d5288640004be7608640004bd76086400953e75086400053d75086400072d52086400953d76942400053d73942400053d72942400953e70942400973a709424008e3e609424000c7e76d954003c7e74d954003c7c74d95400047d73d95400047d72d954000c7c75d8d400047e7654d400047c7654d4000c7c75d89400047e76549400047c76549400a47e76941400063f65901400963c65901400047f7558c4000c7c7558c4003c7c7654c4003d3e7454c4003d3c7454c400365e6354c400065d6354c4008d3e7590c400053d7590c400053f7550c4008d3c7550c400047f755884000c7c755884003c7c765484003d3e745484003d3c745484002e6e62548400066d6254840
  | 7 => 0x902103c7f76950210047d769502103e3e64950210063d649502100c7e7558c210047f7654c210047d7654c210063e6454c210063d6454c2102d6f76548210c66f76548211b56c745482102f2e645482102f2d64548210056f73548210b66e615482102f6661548210056c70548211b56f75d0821006ad64d0821005e571d08210056d754c82102ecc634c821005e7714c82103cf5769042100765529042103eb664504211af345450421005d47350421005e77250421007655250421007a74250421005f07050421006b564cc421005e572cc4210076552cc421004f5760c421005b5740c421006b5640c42100755530c42100765520c421007c5320c421004ef764842100c7c75980210047f755802100c7c7558021004bf745802103cbc7458021004df7358021034dc735802102ee8205802108d7a70d925003e3e64192500063d64192500057671192500057571192500957a701925006d7a70d8e5003c7c7458e500047f7258e500056e7218e500056d7218e500757a7018e5003c7f76d0e500057671d0e500057571d0e500047e7690e500047d7690e500047f7650e500047c7650e500047e7610e500047d7610e5004d7a70d8a5003c7c7458a500047f7358a500055e7318a500055d7318a500557a7018a5003c7f76d0a500057671d0a500057571d0a500047e7690a500047d7690a500047f7650a500047c7650a500047e7610a500047d7610a500047e76cca500047d76cca500065d63cca500047e768ca500047d768ca500066d628ca500047d764ca500065d634ca500066d624ca5000577714ca5000574714ca500047e760ca500047d760ca500074d320ca500157a70d86500055f73586500055c73586500056f72586500056c72586500053e74186500053d741865001d7a701865003e3e64d06500047e76906500047d76906500047f76506500047c765065003e3e64506500055f73506500055c73506500056f72506500056c72506500057b70506500057870506500047e76cc6500047d76cc6500056e72cc6500056d72cc6500047e760c6500047d760c6500053e740c6500053d740c6500047e76c86500047d76c86500055e73c86500055d73c86500047e76086500047d76086500053e74086500053d740865003c7c74597400047f73597400047f725974003e3c405974000c7e7558f400047f7654f400047d7654f4000c7e7558b400047f7654b400047d7654b4009c7d769434000c7f765964003d3e745964003d3c74596400963f74596400963c74596400047f73596400047f725964003c7c70596400963e40596400053d769524003e3d76952400053d73952400053d729524003e3e609524003f3a609524000c7e7558e40004f77158e40004f47158e400047f7654e400047d7654e4003d3c7454e4003d3f75d0e4003d3
  | 8 => 0x47c705943103e3f759903103e3c75990310363f53990310363d53990310063f529903103eb67199031004be70990310063c50990310047f755903100c7c75590310063c5459031034dc73590310063f75590310063c75590310369c73590310363f53590310363d53590310063f5259031004bc70590310063c505903103c7f76950310047d769503103e3e64950310063d64950310355f7654c310e65f7654c311d55c7454c310371e6454c310371d6454c310055f7254c310d65e6154c31037566154c310055c7054c311d55f75d0c310069d64d0c31005d571d0c3100c7e75588310047f76548310047d76548310063e64548310063d64548310055d754c831005d7714c83103cf5769043100755539043103eb664504311cf345450431005d77350431007555350431007974350431005e47250431005f07050431004df764c43100c7c75980310047f755803100c7c7558031004bf745803103cbc7458031004ef725803102cec7258031036d8305803103c7c74597210047f735972102e6c21597210047c70597210047f755932100c7c755932103c7f76953210047d76953210365e7598f210365d7598f210065e5498f210065c5498f2102e5f5298f2102e5d5298f210065c5098f2100c7e7558f210065f5358f210065e7558f210065d7558f210065e5458f210065c5458f2102e5f5258f2102e5d5258f21006d77158f2102ecc2158f210065c5058f210047f7654f210047d7654f210365e6354f210065d6354f21006d6639072103cf776507211c7345450721005d47350721006d66350721005f07050721005b5740c721006d5630c72100755530c72100c7c75983210047f755832100c7c7558321004bf745832103cbc745832100c7e75d92210047d75d92210047f755922100c7c75592210063c545922100e6f7654a2100e6c7654a211bd6c7454a210056f7354a21007677154a21007647154a2102e6e6154a210056c7054a211bd6f75d0a210056d7510a210056d758ca21034ef764ca210056d754ca21036ce634ca210056d75c8621005cd73c86210047f755822100c7c7558221004bf745822103cbc745822100c7e75d91210047d75d91210047f755912100c7c7559121004df7359121034dc7359121004ef7259121004fb7059121004f87059121004f77158d210065f6354d210365c6354d2102f64215492100c7e75d81210047d75d812103cbe74d8121004bd74d812103c7c74594210047f73594210047c705942103e3f759902103e3c75990210063f539902102e3f529902102e3d529902103eb67199021004be70990210063c50990210047f755902100c7c75590210063c545902102cec72590210063f75590210063c75590210063f535902102eac725902102e3f525902102e3d5259021004bc70590210063c505
  | 9 => 0xc54d8941006cf63d8941006cc63d89410066f75d89410066c75d89411be6e54d89411be6c54d89410066f53d89410066d53d8941006e571d89410066c50d89410066f65189410066c65189410072c5418941006cf6318941006cc631894102e6e751894102e6d75189411b66e54189411b66c54189410066f53189410066d53189410066c50189410047e76549410047c765494103d3c74549410065f63549410065c63549410066f625494102e6c625494103d3c75d094102eac62d0941005b671d094102cbc76509410fd3c7550941005b471509410fd3e759054100c7e75d81410047d75d81410067850d81410067b65d81410067865d81410073854d8141006db63d8141006d863d8141006eb62d8141006e862d81410067a75d81410067975d81411967a54d81411967854d81410067b53d81410067953d81410067b52d81410067952d814100c7c75181410063c54181410067850181410067b6518141006786518141007385418141006db6318141006d86318141006eb6218141006e862181410067b7518141006787518141006bb7418141006bb541814117e7a541814117e785418141006b854181410063854181410067b5318141006795318141006bb4318141006b943181410067b5218141006795218141006bb4218141006b94218141006ba4118141004bf7650441005b8705044103eb840980410047f755804100c7c755804103c7c74597310047f72597310365c31597310047c70597310047f755933100c7c755933103c7f76953310047d769533102e6e7598b3102e6d7598b310066e5498b310066c5498b310366f5398b310366d5398b310066c5098b3100c7e7558b310066f5258b310066e7558b310066d7558b310066e5458b310066c5458b310366f5358b310366d5358b31006e77158b31036cc3158b310066c5058b310047f7654b310047d7654b3102e6e6254b310066d6254b31006e6629073103cf776507311e7345450731005e47250731006e66250731005f0705073100c7c75983310047f755833100c7c7558331004bf745833103cbc745833100c7e75d92310047d75d92310047f755923100c7c75592310063c5459231037573154e3100e5f7654e3100e5c7654e311dd5c7454e310055f7254e31007577154e31007547154e310365e6154e310055c7054e311dd5f75d0e310055d7510e310055d75cca3102cdf764ca310055d754ca3102ece624ca310055d75cc631005cd72cc6310047f755823100c7c7558231004bf745823103cbc745823100c7e75d91310047d75d91310047f755913100c7c7559131004df7359131004ef725913102cec7259131004fb7059131004f870591310066f625493102e6c625493100c7e75d81310047d75d813103cbe74d8131004bd74d813103c7c74594310047f7259431
  | 10 => 0x8232004bf745823203cbc74582320053c74595320057870595320063f745953203c7c74595320063c745953203c3c745953211c7f73595320065f73595321247f72595320066f72595320067771595320067471595320067b70595320047c705953200678705953200478705953200c7e75d91320047d75d91320063c54d91320047f755913200c7c7559132004f77159132004f47159132004fb7059132004f8705913203c7f76951320047d76951320056f7254d320374c3254d3200c7f76549321147d76549320055f735493202f4c325493200c7e75d85320047d75d85320067665d85320067565d85320067675d85320067575d85320067654d85320067454d85320067753d85320067553d85320067752d85320067552d85320067450d853200c7e75185320047d751853203cbe7418532004bd7418532006766518532006756518532006767518532006757518532006b67418532006b5741853200676541853200674541853200677531853200675531853200677521853200675521853200674501853200c7e75d81320047d75d813203cbe74d8132004bd74d81320067850d813200c7e75181320047d751813200678501813203c7c74594320047c70594320047f755903200c7c755903203c7f76950320047d769503202dcf764c832006cf764c8321ef4e754c8320074d754c83202f4e654c83202f4d654c8320074e544c8321ef4c544c832007c7714c832007c4714c832005cc704c8321ef4c504c832006cd329843200c7c75980320047f755803200c7c7558032004bf745803203cbc7458032006cd3258032004f77158032004f4715803203d3c7454f410365e6354f410065d6354f411053c7550f4103d3c7454b4102e6e6254b410066d6254b411053c7550b4103e3c549834103eb840983410047f755834100c7c755834103eb8405834100c7f76596410047f73596410047f72596410047c705964100c7e7558e410047f7654e410047d7654e4100c7e7558a410047f7654a410047d7654a411063e65d064100c7c75982410047f755824100c7c755824100c7e76d954103d3e74d95410fe3e74d95410fe3d74d95410047d73d95410047d72d95410047e70d954100c7c75d8d410065f53d8d410065f65d8d410065c65d8d410071c54d8d410065f75d8d410065c75d8d411de5e54d8d411de5c54d8d410065f52d8d41006d571d8d410065c50d8d410065f6518d410065c6518d410071c5418d410365e7518d410365d7518d411d65e5418d411d65c5418d410065f5218d410065c5018d410047e7654d410047c7654d4103d3c7454d410065f6354d410365c6354d4103d3c75d0d410369c63d0d41005b671d0d41034bc7650d410fd3c7550d41005b47150d4100c7c75d89410066f52d89410066f65d89410066c65d89410072
  | 11 => 0x3c7e745944303c7c74594430047f72594430365c31594430047c705944303e3c405944300c7e755884300c7c759804303eb840980430047f755804300c7c75580430063f64991521356d72991520057671991520057571991521456f725915203e3e641915203c7e74d8d520047e70d8d521156d7298d520053f7458d520053c7458d521256f7258d52005777158d52005747158d520057b7058d52005787058d5203c7c76d0d5202d6e72d0d520056d72d0d520057671d0d520057571d0d520047e7690d520047d7690d5203e3c6490d520047f7650d520047c7650d520047e7610d520047d7610d5203e3c6410d520055e73d85520055d73d85520053e74985520053d74985520bd6d72985520b56f72585520053e74d81520053d74d815205d6d72981520053f74581520053c74581520055f73581520055c73581520556f725815200577715815200574715815203c7e74181520047d73181520047f7558f4200c7c7558f4203c7c7654f420365e6354f420065d6354f4203c7c7654b4203d3c7454b4202f2e4254b4200c7e75987420047d759874202cbe749874200676759874200675759874203e76549874203e74549874200677539874200675539874200677529874200675529874200674509874203eb440987420047f755874200c7c7558742004df7358742034dc735874200677755874200674755874203e76545874203e745458742006d77358742006d4735874200677535874200675535874200677525874200675525874200674505874203eb4405874200c7e75983420047d759834203eb840983420047f755834200c7c755834202cbc74583420047f73596420047c705964200c7e7558e42004f77158e42004f47158e420047f7654e420047d7654e4203d3c7454e4200c7c75982420047f755824200c7c755824200c7e76d95420047d73d954203c7d72d95420047e70d954200c7c75d8d420047e7654d420047c7654d4203c7c765494203d3c745494202f2c425494200c7e75d81420047d75d814200c7c751814203c7e745944203c7c74594420047f735944202e6c21594420047c705944203e3c405944200c7e7558c420047f7654c420047d7654c4203d3c7454c4200c7c759804203eb840980420047f755804200c7c755804203c7c74597320365c31597320047c70597320047f755933200c7c755933203c7f76953320047d769533200c7f7654b320055f7354b3202f4e3254b3202cdc735873200c7c759833202cde73983320047f755833200c7c7558332004bf745833203cbc745833203c7c745963202e6c21596320047c70596320047f755923200c7c755923203c7f76952320047d769523200c7f7654e320056f7254e320374f3254e3202cec725863200c7c759823202cee72982320047f755823200c7c755
  | 12 => 0x500000100200100000500100902400100300000200100100100000300000500000200700500400000900400100200000000300700000000000000200100000000b00100200100000300300000100100e00200000300500200000400800100200000100000000d00200000000900000300000100000600000a00300000000000100000000e00c00000200500000600100000000200200000000100100101000400000300300300800000100700700b00000100600c00300000000500200100200200000000600700700200000000000700a00000100400400300000200100a00100300200100200000300200300200200500200000500400300000000000000000500000700100300000d00f00600200900000e00100d00100100000200300200000000000600100200000000f00200400200500400000000300000500400200300000000300000900100300000000200000400003c7c7458e5403e5f7358e5403e5f4358e5403e5c4358e540047f7258e540047c7058e5403e3c4058e5403c7c7458a540047f7358a5403e6f7258a5403e6f4258a5403e6c4258a540047c7058a5403e3c4058a5403c7e749825403e3c74982540047d73982540047d729825403e7a709825403e7b409825403e3c409825403e78409825403e3840982540063f64991531555d73991530057671991530057571991531655f735915303e3e641915303c7e74d89530047e70d89531155d73989530053f74589530053c745895311d5f73589530057771589530057471589530057b70589530057870589530056e72d85530056d72d85530053e74985530053d74985530dd5d73985530d55f73585530053e74d81530053d74d815307d5d73981530053f74581530053c74581530755f73581530056f72581530056c725815300577715815300574715815303c7e74181530047d721815303c7c7654f4303d3c7454f430371e4354f430047f7558b4300c7c7558b4300c7e75987430047d7598743034be749874300676759874300675759874303e76549874303e74549874300677539874300675539874300677529874300674509874303eb440987430047f755874300c7c7558743004ef725874302cec725874300677755874300674755874303e76545874303e745458743006775358743006755358743006e77258743006e4725874300677525874300674505874303eb4405874300c7e75983430047d759834303eb840983430047f755834300c7c7558343034bc74583430047f72596430047c705964300c7e7558a43004f77158a43004f47158a4300c7c75982430047f755824300c7c755824300c7e76d954303c7d73d95430047d72d95430047e70d954303c7c7654d4303d3c7454d430371c4354d4300c7c75d894300c7e75d81430047d75d814300c7c7518143
  | 13 => 0xa10740f6405c0000000b80860000035c000000000000000016400000007a230e19220b43a21922958a745444743c59dd8eb64200680000c1001e0000bc0000456357000066022b0a4825c00000013f1520e2600032900000000001c314f80006dd1699708000000000049400064933c8a58f981e42f61ad07c05031d915b0d267ac14f810cdaa5513140ce00000001d60000a7600032800004ee0000001da05fe1d7000000000000019594a400000000019740005ab000205800066000002c4bee5a000015a50cc000433994433019700000000000000001b2c64e5e70e200010602213f180000002fb0f9061c9500000000a2c0005d53b4800000000024681b02e85a200000010de61c1180000f3c000213800107a4390000bb025200000000200000100000000200000300200000200100000200000300300100000200000300600000300501100000000000700000000000000100600300000600200000100200c00001300000001300200100000300000000000200000400400100b00000500300000100000000300a00200600300000900e00500200200000000700200200000200000000300000600000000000100a00500000300c00000000c00000400100300800000000100000b00100000400400000000100200100800800400000000100000400400300000300100d00a00300200100000e00000100200000100000100200000d00000000000000100300000400200000200100000100500200100300500100000000100000100200600000400000200200200100100000c00000000a00100000000200100200100000100000000000000200200000100000700000200300100d00400000000200500300f00000000100000000300000300000000100100100100500000a01100400000000200200100f00300d00200000100900000600300b00100000000300400400500000500f00300300400800e00000000000000200000900200000000000100100100000200e00500700500000f00100000e00000600200200000000000300000000200100400d00000300000000e00b00001700700000300000000800200400100600000300000300000100000100000300801100100000200200e00300000300700700300100100300500000000100300000100500000000100c00200000100400000300200700c00100000a00000000000700500000000600100200200500000000300700000800000000000001900100500100200000200b00000100000000100402500000100700000000300000401200000100e00900000500000200100300200000200200200100000300200600000000000000200001200000000101000000000300000400300b00100100100300900200800500e00000800000000000200400200000000200401a00000b00a0
  | 14 => 0x63055d2af868035211715500000740002759d0400000000000000000001800fe0d9c05e00002500c479c000000063c50e000159400063500010b82ea3e905988d88600002000568fe033c3931534d3867a1c5868c00000000000010be0000001b0813426b06e000103e01c190800000000001905c000068f3640001022141126000031625528f0fbc64400000020ec6b62271e18000f340002a7a0346ba4ad1c8102c0002653aa04d43384ab3cc03d000000e085929816861a2c21d907c27592cf04dc0565b3000025400037e000176c2d20000a594d80003013e502a00002e4344993800000003500009e23840000000e380de0000000b6444f3f88d0c218000207000000000000003e8a080003db00000000fb4170a78d5822e00017142e613a00010242c400000019fca9600000009c400a62101880000002b919309bca628320000864d6268e000000088e00242a9e444a03a305a80006dc37333700003cc1ea00000000000000618000ec613809e9b140000000e5910c7e600000000000007df0b60a08c580f835b01ac36c662253800000051000013cc7e8000000033ce0c60700600001543990000000fee0002fc1f6cfa815b00013bc0902a82b41c101e640100000002265fc35c00000001ff3709cc00000000e78d880000000bda10cb7c22427480002fe40a0000ec05ca2d43a6907834c2d80690050000000000000052600015300000000000000000a864d70b780000001d32a10470a5808d0000564b0a6da000116c000000363000102617e178838800007519e8f600f0000169000036a5f52168ae87ec7fc0fb04d80001510002170000000004855448a2ca000000092456622985a0a3a66500000000000003c912683b400002c0000e6a627307a1500000000130bbcaea69d1de80009ce5730000c8c0004bc00000000000000000000f0e5542858d68db60b041980000001f815d8000e5a6291fe1e8c74e59a2929fb880607700017cc3342e3000000000000000000009c400000016e800000000000003720003a4000000008e3af000102000000017fc38600040193400001f9000000003a0cb000212c8b80002bd00008260000000000000148000193ca04000000204821a0000002194fb48001460368b3a00000003c827c84232c00004c41b4000041c0007c400008bc4e000014d0328054000415108c0005de0000a6d034000197a0acdea6801ac0adc0003c10621e0c8ea56a00002dd05e4960001a6100c37411a9c54f5a00000019a8aec00028a800067e00028d171cd9a00000004e4b4c3f53759f4c0000000001978672000000077504600003f0000000000000000000000000000000003ff00000000f472e0b280006681a70001aa400000013207809d054639c931c5e414a2ae1670690638000000100a1e100018e4c560183
  | 15 => 0x1fcc9bc00021e10a4de2632377887cdfa108000136cf960001b78ba40007930000000e1e27b000000069e6e80f69ce032000000000000000000000000bc000020d8000000084000092491815e228000000084f08d8a8c5ee2b62a800007122d70000b98ce007d22511c820027421096d801601b334199cc624582b7864c00000000000003d62720001cd0bba65c25900fc000000373964cf700000000f480000000000020a9c83a00009500da5772de0e9010486200000000001f70000e78000000000000000000019a8000000000000000014e468076a0280003c626c93750904572111e8070e6d60c280009980003bc1054b98526299989908e5350a9a01028c37623d9e1400007311c0d5400037d00018540007d8000000000000000000000007a8063000000011d1da80000000a03cc9514000105000000066c00018f800054e5a90000374eae00026a0f6c000083000000000000008f9ef401400000017a05b200019507f81e200000000009ac00000000008c82a420e000043a5d304294bc00069a0000000a0218a0c7a15d07269f1c5044090479700010b10c22c6236148cb1662004c00000000000720000000000000000093e0a93b68af0d1a25a00000000000001238000000093000000000000036a000000000000014b88e60ec0ea84a05b80003808000da28071e28000b7a359000134d098287000154800000000000001be00000013ec73a000000000000010200000003ac7440ae87ec0006ca000003c9b07f23a88c703f45dc000076000000000000000005180000001036000142000103c5600bc1424a6431400013d80000003e300000000001d88000df085b20f80008ba0000000af8d042c311a0000ef86591eb800000041727f00009e84691cb9b487c62de3eb0484d726372198a8509a23933a08044402eb1ab984c46209025a955c0440003ad19100f600000019345f80b9083000000000040a80005dc00000c80000e8000000000009e41d1a08ee04846c90ae13804163830de0878f683ad000217800000000002750b034200013dc0001aa3daa1ac8845d6230000029a00000021b840a36c4102100000538000000000066d03192e0ffc62306c1824e760000000000ffa0bf0000000d8e00025500000004512140fdc00000000010f50a080b3fb1bf0000760000000000000000000000000000001fa00000d31060ef8000000289000000000023e1fbc24e00700000000000001a69f080f800018400000000002ec800085e1ca26f8d440003a53bd21c00000000000000b1c5fa3df1d6000070700011dc0000000890ab4c987b729b80000000000001be80002232fd8000b422bd1fd0bd400000000000000000000000000c6c00004780004305bf0000d7017860b00000000005c13e082185c434b27d1998c220160000b34
  | 16 => 0x2e410900000002f200000000001b66e000000004bc5630000eac32a000000159000064a242000009c000233066506880c0000114b328560000000ee6000312189488a306000000000016318b80f000000000006bc0000000b596a800000031a1ba8dfe10f3c4800050c6e302d8538dda38d12880000c20a600000000002a9000000056a5cf000004c8c6115000000071c00025f0000be411100011500006a0000085cfe83793580d8400000000000000003753620000bc20001d480000003e820a10d8cb60000920000000000000000012c86840a0000a7a56e01f05b41e02c207585c4ce66633e7133cb7000013e8ea8000699000084907c211436077c0007790b088b44ba08a29414f000047637d80000c85b13d58c146ce44d4121c2432200036600008760000001f200000002ef912c0000ce0e680006da0003a31c3026816a0be16dc4ec33e2b889ccd20777186890cd643fb11f1510c0c2441f9076405221017415c87420be42216bcec420f261921ca280000001d940002370000000af00001418e7c0007840000b680000003a280000002481ea000082c00000010680c00000211104fb800037a00000001541fc80000000002f1068489c00000008e8e360000448f301b20004188284000000199125035677f4369e50c661a402807308d42031050530aa617a03b1650e8e68b02693000000000000a803ea04a1a91464dbe30a3aa8e886124403d116249b459229c86cc0000004010000b100003110ab0bcc0000001c7490c00024800000000000000bb44f4000000000000000000000007720000000820d240000ed9bb800040f2f480000000003a900001021450000000f7600020c1c440008510000000000000206195c0000000e0800104a3cb0459df4a3630b0260d14c081423a7074894a05223e84685120000000e3c00000001986b4000846342149011046f0002004db00003d800000004463781cd89227e503c97400006d700000007307cd38a14702dc0000001d58c6035315280009b86f2000000028e43424180000000001361d74c2426600011240587c00001adc00008712693d429e000000000000020636e1e34ff25343dd000000057e000059c00039c08f0000000349245134800052114c80000000001ed0fb0fc200000004c082000025c8000f360062a000000002d60770e6c0001e940b8afc0000000c69dbc00000022d00010d2863420992cf0237727e1bf84b67310d610c417a3940c7101479e00000000000000000001fd42580000000000c180002ba068832c5b5077925c9840013c80718000000000000012200000000000000ea00013140000002d280000000002e59fe000072417d10980000000000d78ca8000000000000000000000000000002c680000a200024f0c08bf20003d094801445a80001c0d0421e3
  | 17 => 0xe000000000000000000006320653ca8b84db200000000000000000001c2c4f84a93ff80007223560c000000000000c08be00006020959a0425c63e30f839c476372112800000085a1000000ac46a40001cfc0000c23e18000d0c000000062465c0000000720e203d90000ac88be51300009d40008280209cdc0000280000000b720003598000000156000015000000009100000003de00000000002cc2879ee4e9283631d9504e525ae0000b1c00013f0d883940000000000000dbc00008b0000fda2af033800000000000000009f04e53579cf800068a10b0000b2003b30d815cc820cd12b9e9000021b1338000124000000151c30633300000001a2000000104800000004e0000000471000175080c7a52829a5000000000003d43e60ac0000000b88000000168c00025c35400009fa24000000000000000ce800000042417c96040003e40001deca2e00012986180001d400000000003c0315055c0006722720a200002ab3df800051a0002e894300b20b200010fcc1c00012592fc03400000000000000001798fb80ba23c000000000048e147000067400000000000000002cd800000000035180004502f426a90449267502a50000e2c7e611912b00000003d480002c076a00a9d007ac03637c800000078f17f1c5c9664891348000ae015f0fe0000dc478230b991400068330e884ce0052700001fcaf27c90001554a7440d2c60b747fa3ae0001c080000000000000dee00000000000cc1b009889a8fc00000178000a1462e1069b040002023f11d703284ea40e00007ba000000093c000000148163c52a00025200003040000000000bd65e5000000018200032b00000001ef0001c890a47e701b879499a76b09680000000003fd80000000003eca03c5926a60249c644660000001f7815c13c00006c800031339e92f4f143df242801052440841f800000000016218346805b03890000faa0e31ca80009dc4c10180000f6602300000000002fd0cf21640001e71821b940006e43538000f786ab000000024668c00000000000002d600000000002e307c415a3ca2c18e480000000000810b302df0a81fa8f2c5a40001e2000072037600000007a60000000a220000000000ed843a00000003e80e9000000000063a0001dc800051f00007888d60001d4000000000038280000000001580850d220ba3d38ca437a6a100000000001ee123000000061600000006347330000000fae00018910dc0003ed00018507920532eb8cdc5b675330c02647102c800006b8e963b63ba800068e480270890444428f2651c949623c40001f3c0008490f611546f056d3a6026c0005ad407000058a1b840e98bcecc31002d00000003680000000a0e3c835d0294b043b3000094815656738c0000000000081800000000011e9320280000000000000067b000000
  | 18 => 0xec0005800bb8000000000000000077600034a8000cb46be273000000000000000000000000000ca0b2c822355000000000039d042800072b0000f0800000000000000003311a300000005083a500000000001c60e5845410e0081c781480bb00017f800049c0000c58cd86bd0000000b904a10000000f3a01100009640006f629111c08ca36b32f92e8caa1140001f148b200000014a85a047e000000000000000000000000001f89b0c726478000000036e479413882400029400000000004ed0001a5c00000000009fccea0c713403e506e4f00dd1fe80000000000000ab000000006200006460000d38cec000000198400000000000000000c5000153000000001c1734000653103940039c6f330c932c6880003c607084da4ae0dd9c7c3500000000b000007e913c005c00000033580000005ed09d8b04da030c35287a00000001df8000fd83ba00000008887d12f70edc91e0000460f889607e40950ba8b3e3543840404b940002c300000000003748158ad65bb0000b4400000004000001fc000000109400000002f92648fe02023385d89920d4324011ccf04ff2ec1a6c0965e40001a2000055e1130d9833e84e06a81a108a000188800cb0e4b700012d0a9200000000002325c300000009a200000017a906a5061da10a88f40af2761db8308280170180400009f000000103000000000000000fd0cd8b2c8c43ea0379010be80003ee80002660002c8945800030f32180010d449b4321a584f266f07f98f465885d00012d80007eb1eaa02459e3852440ef06e23e50df000000009e1a5178c0000001588c1c65a0000ac10c8e1c5f10a1800034a2f6130832400000025003800000003428090cfc4023678a0449c3af0e28330afe727399000000078e0be80480003823ba1064e783cd14c20a400045e000000070200039401c0bec00000000000000001afa0e0f5449512f80000002e7000000000000035d97f400000018180004580000001afc0005c9000000004a53f12b18fcd6a0f721a80d40005f03698000000000000000097657b3238770af855a05189b8cee7d00000000f3e0001ff10e037e4a21599dc44522b80000000438000000000104c5d2000165c0000002372020fa4448226000090272c33480006c829101719f4000000000000000018c00001100000c816a8000f5c0553950118d3c6872ca98b4bde0000000da4000000000181498c0001e380008da1c93568d30e344a31ee00000003a031e0e680005b412c0000d445560a200000006bc093000003e0000b310f80000001be0de80000000000000a1a3600001e00ee0000000169cec20d630f000000000d000083800042b203800000028519da14c4947670000000000000397982825e78611f800026446105c19c40e22601b280007ce07205b00000001c73af80007d64c
  | 19 => 0x1c01df8c0600000015f4e420000000000b9c0001e720f055c0002c500000000e10000a281d08190a90000f5e000308098c9885da00000000003d30001584d80034013922c64a0001b521287e00000000d4064012000001009e482c3e39c8c3e04983320a5c5382ce08c008474c6420370dfc9c621a18a99f06c600007e0854c000f60001c281cc55900000000003700000f9805a1042ad93e4dcc3d03a1990063600029801a4000000000000018074f18e92740001fd00012bc07270d29680005688710ef07008a403d3d88d
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xd51531c1410c401b26863828218802872117558f2103c1e422eca9e4200e145498d41c8401a60a838283908033498c70507211bc96422ea9944200968805d5328840145b05a9ac8108028b60850590211b496422ea9904200968805d5320846d64908a928210803511cd5250421006982a0e0a084200d61521c14108401b4684382821080385591530c42100692ba2a41884200b45854c8310840f86cc8b88c928003135d9320ca5017e1d320e0a0ca00083f865d5329000127100baa65200030e99670d864000559406c330c800785c8758d531000f0d90eb12a4200029560e759844000532c14eb3088007a3684dd5611000f469083aac22001e8da1754584401df0a2a6e6b08803ae14541cd611000f46909a9ac22001e8d21153584400051a42a86b088037e2454dc9611006dc48a8392c220003311cc725844003d1a426a4b088007a348454961100014690aa12c2200bf8c150705844000668398e0b088000ce0721c1611000186ceab0c822001f0d9d1619404003c8e43ac6a98800792c87589521000f0790cbaa64200024e201754c8400045ac30e29908000b88804c83210001b1264b8064200026c205700c8400049c402eb3088000b15839d6611000164b053acc220002cca02759844000598402eb3088000a3685dd96110077c28cbb9ac2200eb8519473584400051a42ac6b088007a3486d4d611000f4690ca9ac2200038558d53584401bf1232ee4b088036e24651c96110001b08e6392c2200028d215625844003d1a436a4b088007a34865496110001c4ac4a92c2200bf8c1947058440006c8398e0b088000da0721c1611000183aeca9862200030b5d9520844003c9c402eb3008000c3675586601000f86cecb0ca02001e4e61e609404000526c18a83126000a688054c624c0014ab062a0c2980029360e755883000516422eab106000a68805d5620c0018caea38ac4180029360c505883003c1e422eca906000c4f73589520c0014c902b12a418003135cd629403000662b10e29806000c5b76941300c001b10e42026018003a2588404c030006c838880980600783e849d9538800149b042a0c6900031618c705492000532c10a830a4000a4d829d5630800143908baac610002962017558c200062aba8e2b184000a4d82141630800f07908bb2a610002952056354c2000626b1ee4a984000879861c1530800189ac6b94a0100023321d634802000662b18e29004000d88731012008001d12c62024010003681c440480201961c202ed2a62000d30541c141c4065a60a8b8881880032c5da7110310196983aae22062000e145418d4144001c48a831282880bf0e151761001017e1c3aaec2002000cb1769c4400400172106b888008002e82097110010005d1416622002000f11530c44004001725079088008003c85482110010
  | 1 => 0x2001a05059a791c0032b980000001d400870000000006983d6a2249000d062002840000002c00000000d8a646391e080075d38896744b09da23b158013ec6260000000001d944af17000000037a44000e000007c0b0039410006900000000000000005b000667053000b609002e000b90000000df00000000d1800000000000000001e1540a59000015c00002f9b2000031db8000000000bb00000000a0000000003f800b80038a000000319e4000000384000067800000600001682a4cb0400000000000c8000680000558009a0000105107a000b4ba0000001027b000000031000019c000aa2940000035000846d00000004c00120000f20c000080400000000c04030000000000481000020000000000000400010580c04010181404010100800030281002010600802030000002030101c0201000040203000080e00028100e010000400000080c040000800020203e1a322e3322a60783c845c86054c014ab073acc3a18029960a759874303d1b426eab0e8607a348454d61d0c0f868c8b8cc8a901e1b21972d0d5203c1e422e6302a40785c8758d53d08014ab073acc3a10029960a759874203d1b426eab0e8407a348454961d080f07d0fba2ca990030d1d371595320061a3a0e2b2a6400c3874dc1654c801876e8382ca990030e1d070595320062db98e0b2a6400c6b721c1654c8018e6e2382ca990031c1c470595320061dc20e0b2a6400c38841c1654c80f07908baec2990028d21165d853200538402cbb0a6400a34845d7614c80117100ba0c2990021d61e65185320043bc3aca30a6400a3484594614c8014e100b28c2990029560e751853200532c14ea30a6400ab0805d0614c8014cb05a98c2990029560f52185320052ac18a030a6400a6582140614c80f07908ba8c0990029660c501813200534c10a03026400a4f865d5320c80189eecbaa6419002c3211754c832005a4402ea9906400d45751c5320c801a90a03826419002b2201325803200662990e2b00643bc1c74d8d5350401c18a8318c4a08da8b21153189411d60e3a0c6a928237c2c74d895250401475002a0c0a08028ea1854181410070c2a6c63028200e185418c6050401c50a9b10c0a08038a15062181410051d42ee83028200a3a871506050401473062a0c0a08028e608541814117d1c422a6302822fa3885d0c605040156503a18c0a08028e21543181410055840a86302822fa3884548605045f4710ba10c0a0802aca0742181410051c42a843028200ab08150860504014750b208c0a08028b2117558b3103c1e422eca966200e245498941cc401a60a838283988033898870507311dc8e422ea9946200958805d5328c40143b07a92c8188028760c50590311d48e422ea9906200958805d5320c47562908a9a82188035154c7250431006982a0e0a086200
  | 2 => 0x15d9897061acc0000000000000000536e0010900056568c84a7c0000154db22108580062800000000001c800000000077000e4000037150a485002f4000045800001f4a1845e0000308c847369283a00353016ed700000008f0007000c4018000000000019a1973a4d52340d80164000805800001c00000000000158006b000fc000028c000000001b0002480000180030c4600000800000000a592480000000000000000000000000001e800008933800006900139ba005400000000000000130016000004600000660017c0000000dc00ca0000000a4002691ad53ea0800000008474cb360000000000012a9c000514a4f0000000bf58898a25e39a9c0011002f000004e8000000000000000000007e5a718482e28000000000002180000003780045000d4004300000000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x80000000da0000e00018f2e00e12c000900c004806aa01400ac80786300e88a3442259c0260030040420001000801504945d4714c83200550241751c5320c80144996140704c83200708152621c141cc4875049454c72504310054464c541c1410c4855109454c705043100704152631c141c8481904841cd525042100548648541c14108483520945487050421204c1251854c8310840134090615320c42120701150731c9611007fc10541cc70584401f708150721c1611000198132205700c8400048564e85dd9611000122592a17765844003c852616354d6110081c04651cc725844003c8926162549611007fc10651cc70584401f708194721c16110001424945d4715883000518241751c5620c001c81621c4404c03000505251751c56308001450905d47158c200052225d631012008001c81631c44048020
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x6
  | 2 => 0x4e
  | 3 => 0x124e
  | 4 => 0x138e
  | 5 => 0x3
  | 6 => 0x4
  | 7 => 0x5
  | 8 => 0x94e
  | 9 => 0x8e
  | 10 => 0x128e
  | 11 => 0x98e
  | 12 => 0x150e
  | 13 => 0xce
  | 14 => 0x12ce
  | 15 => 0x9ce
  | 16 => 0x168e
  | 17 => 0x10e
  | 18 => 0x130e
  | 19 => 0xa0e
  | 20 => 0x180e
  | 21 => 0x20e
  | 22 => 0x140e
  | 23 => 0xb0e
  | 24 => 0x154e
  | 25 => 0x24e
  | 26 => 0x144e
  | 27 => 0xb4e
  | 28 => 0x16ce
  | 29 => 0x28e
  | 30 => 0x148e
  | 31 => 0xb8e
  | 32 => 0x184e
  | 33 => 0x3ce
  | 34 => 0xcce
  | 35 => 0x15ce
  | 36 => 0x170e
  | 37 => 0x40e
  | 38 => 0xd0e
  | 39 => 0x160e
  | 40 => 0x188e
  | 41 => 0x58e
  | 42 => 0xe8e
  | 43 => 0x178e
  | 44 => 0x18ce
  | 45 => 0x11396
  | 46 => 0x10056
  | 47 => 0x4d
  | 48 => 0x4116
  | 49 => 0xb8956
  | 50 => 0x138d
  | 51 => 0xb9396
  | 52 => 0x130116
  | 53 => 0xb8216
  | 54 => 0x20d
  | 55 => 0x140d
  | 56 => 0xb9556
  | 57 => 0xb8256
  | 58 => 0x24d
  | 59 => 0x144d
  | 60 => 0xb96d6
  | 61 => 0xcc3d6
  | 62 => 0x20055
  | 63 => 0x24055
  | 64 => 0x24215
  | 65 => 0x4215
  | 66 => 0x4255
  | 67 => 0x20255
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 70
  | 6 => 1503
  | 5 => 2162
  | 4 => 232
  | 3 => 31
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
  | 7 => packedAt gbK7 (1981+((h/23+packedAt gbK7 (1820+(h % 23)*7) 7) % 93)*8) 8
  | 6 => packedAt gbK6 (61122+((h/501+packedAt gbK6 (55611+(h % 501)*11) 11) % 1984)*12) 12
  | 5 => packedAt gbK5 (112416+((h/720+packedAt gbK5 (103776+(h % 720)*12) 12) % 3452)*13) 13
  | 4 => packedAt gbK4 (14381+((h/77+packedAt gbK4 (13688+(h % 77)*9) 9) % 489)*9) 9
  | 3 => packedAt gbK3 (2230+((h/10+packedAt gbK3 (2170+(h % 10)*6) 6) % 53)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff007fffffffffff003ffff1fffc7e3ffe3f
  | 1 => 0xffffff807f007f007ffffffffe49c7ffcc63ff
  | 2 => 0x1fffffff80007fffffffc01fff8e078ff07fc7
  | 3 => 0xe01fffffffff80007fffffe00ff007f1ff83f8
  | 4 => 0x1fffffffffffff800000000ffff801fffc00
  | 5 => 0xffe0000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x696300258b4a8b4acb021b2d9092dc3615ae1b
  | 1 => 0xb2ae658055185518156c6e572649c1dacc60ed
  | 2 => 0x1cd5aaea802266f366b6811acb8e068d705746
  | 3 => 0xc819d37366f3002278db35808df00761ba83b0
  | 4 => 0x101efc5c78bc78bc001c06030f6d6801ef7800
  | 5 => 0x1f00e06040c040c040e0381c0fffb7fe000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xeaaac880eaa0c880eaaac880eaa0c880eaaac880eaa0c880eaaac880eaa0c880eaaac880eaa0c880eaaac880eaa0c880eaaac880eaa0c880eaaac880eaa0c880, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15313
namespace PEqualNP.Outside.L_meta_15313
open PEqualNP.Outside.L_meta_15313.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 6 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
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
theorem bgb_3_0 : Interval gbAtlas 3 0 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 31 := bgb_3_0
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
theorem bgb_4_224 : Interval gbAtlas 4 224 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 232 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224)))
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
theorem bgb_5_2144 : Interval gbAtlas 5 2144 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2162 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))) (concat (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896)) (concat (concat bgb_5_928 bgb_5_960) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))))) (concat (concat (concat (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184)) (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312))) (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))))) (concat (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728)) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 bgb_5_1856))) (concat (concat (concat bgb_5_1888 bgb_5_1920) (concat bgb_5_1952 bgb_5_1984)) (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)))))))
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
theorem bgb_6_1472 : Interval gbAtlas 6 1472 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1503 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 (concat bgb_6_384 bgb_6_416)) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))) (concat (concat bgb_6_544 (concat bgb_6_576 bgb_6_608)) (concat bgb_6_640 (concat bgb_6_672 bgb_6_704))))) (concat (concat (concat (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)) (concat bgb_6_832 (concat bgb_6_864 bgb_6_896))) (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)))) (concat (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280))) (concat (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472))))))
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
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaaac880eaa0c880eaaac880eaa0c880eaaac880eaa0c880eaaac880eaa0c880eaaac880eaa0c880eaaac880eaa0c880eaaac880eaa0c880eaaac880eaa0c880
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 49 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) (SBf 4) :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3937060992 * 2 ^ 32 + 3936405632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15313.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,4]⟩,⟨.and,[5,6]⟩,⟨.or,[1,6]⟩,⟨.and,[0,2]⟩,⟨.and,[8,9]⟩,⟨.or,[7,10]⟩,⟨.or,[0,2]⟩,⟨.and,[3,12]⟩,⟨.and,[8,13]⟩,⟨.or,[11,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937060992 * 2 ^ 32 + 3936405632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937060992 * 2 ^ 32 + 3936405632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15313

open PEqualNP.Outside.L_meta_15313 in
theorem PEqualNP.Outside.L_meta_15313 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937060992 * 2 ^ 32 + 3936405632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937060992 * 2 ^ 32 + 3936405632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
