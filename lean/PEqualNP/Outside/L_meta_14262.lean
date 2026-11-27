import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_14262.Model
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


end PEqualNP.Outside.L_meta_14262.Model

namespace PEqualNP.Outside.L_meta_14262
open PEqualNP.Outside.L_meta_14262.Model
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

def SB : Nat := 5

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

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

end PEqualNP.Outside.L_meta_14262

namespace PEqualNP.Outside.L_meta_14262
open PEqualNP.Outside.L_meta_14262.Model
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
  | 1 => 0xf87fc3ffffffc3c3870387e0ffffffe1873ff
  | 2 => 0xff87ffc1ff87fc03f803f8fff0ff03f219e73
  | 3 => 0xfff803fe1ff87ffc0003ff00ff0ffc1c1e39c
  | 4 => 0xf000003ffe0007ffffffc0000fff0001fe03e0
  | 5 => 0xffffffc0000007fffffffffff0000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x10c210451090001428149012821115281830a5
  | 2 => 0xa5112a08c422a4c112810a84658aa095208652
  | 3 => 0xc6254a924d422f69420a2b2129a8ca85c1c318
  | 4 => 0x843633208873358d9b2382004ecc83196a03e0
  | 5 => 0x840400311844232244c344980000c20957800
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfffffcf0ccc0ccc0fffffcf0ccc0ccc0fffffcf0ccc0ccc0fffffcf0ccc0ccc0fffffcf0ccc0ccc0fffffcf0ccc0ccc0fffffcf0ccc0ccc0fffffcf0ccc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_14262
namespace PEqualNP.Outside.L_meta_14262
open PEqualNP.Outside.L_meta_14262.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xd531
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
  | 0 => 0xc3e1fc3fffffff870c38387e0fffffff0873ff
  | 2 => 0x3fe3ffc1e1f0ff80fc03f8ffe1e1e0f919e93
  | 3 => 0x3ffc03fe01ff0fff0003ff00fe01ff0e1e31c
  | 4 => 0xfc00003fffe000ffffffc0000fffe000fe03e0
  | 5 => 0xffffffc0000000fffffffffff0000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x430004510080002080a101280230288083025
  | 2 => 0xa9449a08c4a2549845408a8467145426908692
  | 3 => 0x3189aa924cd445ed51052b212b509962e1c318
  | 4 => 0xa10d1320888666b1659182004d98d044b203c0
  | 5 => 0x2102003111888468a263449800101884d7800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfffffaf0aaaaaaa0fffffaf0aaaaaaa0fffffaf0aaaaaaa0fffffaf0aaaaaaa0fffffaf0aaaaaaa0fffffaf0aaaaaaa0fffffaf0aaaaaaa0fffffaf0aaaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_14262
namespace PEqualNP.Outside.L_meta_14262
open PEqualNP.Outside.L_meta_14262.Model
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
  | 0 => 0xf8f0ffc7fffc7e1c71c0e3fc7ffc1fe10f3cf
  | 1 => 0xf00ff1ff878ff8fe07e00fc7f8e1fe1e633d33
  | 3 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x40118004220208008204820901304088105045
  | 1 => 0x52228891414810a0521244248449414612512
  | 3 => 0xaa444512412900354802489092092941828a28
  | 4 => 0x230064a01101924651486000e48c0c44a40f80
  | 5 => 0xcc088903664e2499a6938f24001031995bf000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xffffee88eeaaee88ffffee88eeaaee88ffffee88eeaaee88ffffee88eeaaee88ffffee88eeaaee88ffffee88eeaaee88ffffee88eeaaee88ffffee88eeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_14262
namespace PEqualNP.Outside.L_meta_14262
open PEqualNP.Outside.L_meta_14262.Model
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
  | 0 => 0x3c78f0e3f3fff8fc638e0c70f8fff87f1133cf
  | 1 => 0x3f80ff03fc78ff1f83f00f80ff1c3f8f623d33
  | 2 => 0xc000fffcff80ffe3fc000fff1fe03ff083ce3c
  | 4 => 0xffff0000ffff0003fffff0001fffc000fc0fc0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x6011804122041004102841420260844111045
  | 1 => 0x8852228a29419022829128884908950a622512
  | 2 => 0x1244440401220052400412212412220804a28
  | 4 => 0x9130065281103249a8a460021c918322a40f80
  | 5 => 0x224088800a64c49253498e4c8002044c5bb000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xfffff8f8eaeae8e8fffff8f8eaeae8e8fffff8f8eaeae8e8fffff8f8eaeae8e8fffff8f8eaeae8e8fffff8f8eaeae8e8fffff8f8eaeae8e8fffff8f8eaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_14262
namespace PEqualNP.Outside.L_meta_14262
open PEqualNP.Outside.L_meta_14262.Model
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
  | 0 => 0x1e3f878fc7f8fe3f1c71f1c1e3f0fe3f0d34cf
  | 1 => 0x1fc7f80ff8ff1fc7e07e3e01fc7f0fc7323b33
  | 2 => 0xe007fff3ff001ff8ff803ffe3f800ff8c3cc3c
  | 3 => 0xfff80003ffffe000ffffc0003ffff000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4300a010422108400810504840904222051045
  | 1 => 0x84210220904030084022221084240504122112
  | 2 => 0x921101001244012480048429022890404c28
  | 3 => 0x890554a24900492b5448024324aa090e80e80
  | 5 => 0xd124660836e49924da793939000cc126bfb000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xfef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_14262
namespace PEqualNP.Outside.L_meta_14262
open PEqualNP.Outside.L_meta_14262.Model
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
  | 0 => 0x7fc7fff87f0ff0ff0f87e1ffe1fc3f0fa4f4cf
  | 1 => 0x87f870ff8ff0ff0ff1f87e1c3e1fc7f1db4b33
  | 2 => 0x7ff80fff000fff1fe007fe03fe007fe638c3c
  | 3 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 4 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x400008001001000000802400240100001045
  | 1 => 0x20820111040140102088220882090241094112
  | 2 => 0x55112aa222aaa88356445541354094ac628c28
  | 3 => 0x14354cc44a882aa59b5511023992b024740e80
  | 4 => 0x662668876cccccc9ede67993910320c97fe000
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xeeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_14262
namespace PEqualNP.Outside.L_meta_14262
open PEqualNP.Outside.L_meta_14262.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x111719870e0a088f8189811e9887800b160209001b990a9c969a1e131280940498040e9d0280001f1503059c05001a800c1f83901d8008002091979b158d200f148b861200108d86800c80000000001383010a0810202002800a04407001c0841808000007fd5001fe54007f55001fc54007fd4c01fe53007f54c01fc53007fd0c01fe43007f50c01fc43007fd4801fe52007f54801fc52007fd0801bf42007f90801fd42006f50801fc42007fcc801df32007f8c801fd3200774c801fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd40017f50007f94001fd50005f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x844002fbc822001ff64110002ff654800d7f32a4000bf59520035f8ca90002ff644800b7f3224000bf5912002df8c890002ff63480097f31a4000bf58d20025f8c690003bf4248001f72124000ef50920007da8490003ad4248001ef9924000fb8c920007ba6490003ed3248001e69924000bfd852000df8c290003ef2148001f690a4000dfd4120007f4a0900037d5048001fca824000de5412001ff6409000bee20480057fb284006bf99420016fcca100027e65080017eb284002df59420004faca1000afc65080057fb204005bf990200177cc810002be64080017eb204002ef590200057ac81000afc64080057fb184004bf98c20017bcc610002de63080017eb184002f758c20005bac61000afc63080077f3104003efd082001f7a841000fdf3208007ee9904001bf98420017ecc210002f661080017eb084002fd58420005eac21000afe6008005bfa804002df54020017de401000bfa2008005f69004003fe4802000dfecb8801afe65c40017eb2e2001bf1971000dfec988016fe64c40017eb262001bf1931000dfec788012fe63c40017eb1e2001bf18f1000dfec58800efe62c40017eb162001bf18b100077e8588003bd42c4001ef9962000f74cb1000fec8388003f541c4003fb18e2000fd4c71000fec4388003f521c4001bfa862000df54310015fecb0801afe6584005bf32c20009f99610005facb0800b7d65840013eb2c2002bf19610015fec908016fe64840017eb242002bf19210015fec708012fe63840017eb1c2002bf18e10015fec50800efe62840017eb142002bf18a100077e8508003bd4284001ef9942000f74ca10005fac30800afe6084005bfa842002df54210017f46108003f93084005fd1042000fe48210017ee2108007fb10840017fb2a2006bf99510005faca8801afc65440017fb222005bf99110005fac888016fc64440017fb1a2000f7d8d10005bec688012fe63440017eb1a2004bf18d10007b8c688002dc63440017fb122003bf98910005fac48800efc6244001dfa122000ef50910007be6488003dd3244001fb20a2000fd50510007ec6288003f53144001fb10a2000fd48510006fea0880037d5044001fd1822000fe4c110007f44088003f92044003fd8822002fd84110015feca0801afe6504005bf32820009f99410005faca0800b7d65040013eb282002bf19410015fec808016fe6404005df3202000af99010005fac80800bbd64040015eb202002bf19010015fec608012fe6304005ef3182000b798c10005fac60800bdd63040016eb182002bf18c10015fec40800efe6204005f73102000bb98810005fac40800bed620400176b102002bf188100077e8408003bd4204001ef9902000f74c81000dfcc20800afe6004005bfa802002df54010017ee200800bfa1004005fa8802001fe44010
  | 1 => 0xbbe40500057fb288006bf99440016fcca200027e65100017eb288002df59440004faca2000afc651000b7f3208000efd504002f78a820012fe6310005ef3188000b798c40005fac62000bdd63100016eb188003bf98840017dcc420002ee62100017eb108002fb58840005dac420017bf4210001dea108000f7cc840007ba6420006fe6110005fb3088000bd98440005fac22000bf561100017ab088002bf98040016fea02000b7d5010005dfa008002fe900400177a8020017f940100097fb2e6006bf99730005facb98012fc65cc0097fb266005bf99330005fac998012fc64cc009ef21e6000f750f3001dfcc598002fd62cc001dfa166000ef50b30027be6598003dd32cc0037f30e6000bf58730027be6398003dd31cc001bfa866000df54330015fecb1801afe658c005bf32c60009f99630005facb1800b7d658c0013eb2c6002bf19630015fec918016fe648c0017eb246002bf19230005fac71800efe628c0017eb146000efd0a300077a8518003df328c001ee9946001bf98630005fac318003de318c001ee18c6002bf98230016fea11800b7d508c005ef9846004fecc230005feca9801afe654c0017eb2a6006bf19530005fec898016fe644c0017eb226005bf19130007bc8698003dd434c0017fb126003bf189300077e8498003bd424c001ef9926000f74c930005fec298006fc614c001ef98a6000f74c530006fea0980037d504c009fd9826002f78c130015feca1801afe650c005bf32860009f99430005faca1800b7d650c0013eb286002bf19430015fec818016fe640c005df3206000af99030005fac81800bbd640c0015eb206002bf19030025fcc61800efe620c005f73106000bb98830005fac41800bed620c00176b106000efd08300077a8418013df320c001ee9906001bf98430017ecc218002f6610c0017eb086002fd58430005eac218003de310c009ee1886002bf98030016fea01800b7d500c005ef9806002fe8c030017ba6018013f9300c0077fb2e4006bf99720005facb9000efc65c80077fb264005bf9932001f7cc990002be64c80017eb264003ef593200057ac99000efc64c80077fb1e4004bf98f2001fbcc790002de63c80017eb1e4003f758f20005bac79000efc63c8007dfa164003fb90b2001f7a8590003ed42c8001d6a164003f7ccb2001fdc659000fdd32c8001f69964000f34cb2000dfcc390002fd61c8007f790e4000fb48720006fea1900037d50c80057fb2c4006bf99620016fccb100027e65880017eb2c4002df59620004facb1000afc65880057fb244005bf99220005fac91000afc64880057fb1c4004bf98e20005fac71000afc63880017eb144000efd0a200077a8510003df3288001ee9944001bf98620005fac31000afe6088005bfa844002fe94220016faa110003f95088001bca
  | 2 => 0x50006fac5a801b7c62d4001bfa16a000cfd0b50006fc85a80037d42d40019ea16a000df10b50006fe65a80035f32d4001bf196a000df4cb50006ba65a80037c32d400dbfb0ea000df98750006fac3a801b7c61d4001bfa0ea000df90750006fa83a80037c41d4001bf98ea000df8c750006fa63a80037c31d4001bf90ea000df88750006fa43a80037c21d40017eb2ca0009f5965002dfcc928002fd64940097f31ca000bf58e5001dfcc528002fd6294001dfa14a000ef50a50007be6528003dd32940037f30ca000bf58650015fcc12800b7f509400dfda84a000bfd91500077ec8a8002bf645400b7e322a000ef1915000578c8a80037f5454001bf2a2a000df55150006f8a8a8002ff63540097e31aa000dfd4d50006fca6a80037d5354001be29aa000bfd895001df8c4a80037f5254001bf292a000df54950006f8a4a8003bf4254001dea12a000f7cc950007ba64a8002ff61540037e30aa000dfd4550006fca2a80037d5154001be28aa006fed4150016fca0a80037f64540019fb22a000df99150006fac8a80037c64540019e322a000dfd8d50006fcc6a80037d6354001be31aa000dfd0d50006fc86a80037d4354001be21aa000dfd8950006fcc4a80037d6254001be312a000dfd09500067e84a80037e4254001bea12a000cf50950006f884a80037f3254001af992a000df8c950006fa64a80035d3254001be192a000dfd8550006fcc2a80037d6154001be30aa000dfd0550006fc82a80037d4154001be20aa000dfcc550006fc62a80037d3154001be18aa000dfc8550006fc42a80037d2154001be10aa000dfd8150006f6c0a801afe65140013f328a005bf99050005fac828012fe63140017eb18a003bf98850005fac428003bf4214001dea10a000f7cc850007ba6428006fe61140017eb08a002bf98050016fea02800bfa5014005bea80a006fe5405002dfecba001afe65d00017eb2e8005bf19740025fcc7a0002fd63d000bdfa1e8000ef50f4001dfcc5a0002fd62d000bdfa168000ef50b40007be65a0003dd32d00037f30e8000bf5874002f7e83a0003bd41d0001bfa868000df54340015fecb2001afe6590005bf32c80009f99640005facb2000b7d65900013eb2c8002bf19640005fac920003bf5490001de2a48004bf98e40005fac72000efe62900017eb148000efd0a400077a8520003df3290001ee9948001bf98640005fac32000afe6090005bfa848002fe94240016faa120003f95090001bca848002efd024002ff68120002ff655000d7f32a8000bf59540035f8caa0002ff63500097e31a8000efd0d400077a86a0002ff62500077e3128000efd09400077a84a0003df3250001ee9928000bfd854000df8c2a0003bf4150001dea0a8000dfd4140007f4a0a00037d5050001fca828000de5414002ff680a000
  | 3 => 0xeb2a6206bf19531005fec898816fe644c4017eb226205bf19131005fec49880efc624c401dfa126200ef50931007be6498803dd324c409fb98a6201f78c531005fec09880afc604c4037fb286206bf9943100efcca188027e650c4017eb286201df59431004faca18806fc650c4037fb206205bf9903100f7cc818802be640c4017eb206201ef590310057ac818806fc640c4097f3186204f790c31007ba861880efe620c403f73106200bb98831005fac418807ed620c40176b106200efd08310077a8418813df320c401ee9906201bf9843100fbe6218807f6310c403ee9886204fd4c431015fcc018807fa600c4017d3006200bf5803100ff2c018802f9600c4077fb2e4206bf99721005facb9080efc65c84077fb264205bf9932101f7cc990802be64c84017eb264203ef593210057ac99080efc64c84077fb1e4204bf98f2101fbcc790802de63c84017eb1e4203f758f21005bac79080efc63c8407dfa164203ef50b2101fbe659080fee32c8407ee9964200fb4cb210079a659080afe60c84017eb064201bfd9621035fccb10802fd65884037e32c4201bfd922102dfcc910802fd64884037e3244201bfd8e21025fcc710802fd63884037e31c4200bf58a210077e8510803ee4288401dea144200fb50a210075a8510803df3288401ee9944201bf9862100feca310803f55188403f790c4203fdc8621015fcc110802fd60884017fb2a4206bf99521005faca9081afc65484017fb224205bf99121005fac890816fc64484017fb1a4204bf98d21005fac690812fc6348401dfa124200ef50921007be6490803ee3248401ee9924200fb4c9210079a6490803f65148401faa8a4203fdc852100fdc4290802ff60484057e3024201bfd9421035fcca108077e65084013f3284200bf5942100efaca108027d65084037e3284201bfd902102dfcc810807be64084015f3204200bf5902100f7ac810802bd64084037e3204201bfd8c21025fcc610807de63084016f3184200bf58c2100fbac610802dd63084037e3184203bf9882101f7e841080fee4208407dea104200fb508210075a841080fdf3208407ee9904201bf9842100fde4210807f62108403f69084203fd48421015fcc010807fa60084017d3004200bf5802100ff2c010802f9600840b7f326a000bf59350036fea9a80037e54d4001beaa6a006df15350025fcc7a8002fd63d400dbfa9ea000df94f50006faa7a801b7c53d40077f316a000bf58b50036fea5a80037e52d4001bea96a006df14b500077e85a8003bd42d4001ef996a000f74cb5000dfcc3a8002fd61d400dbfa8ea000df94750006faa3a801b7c51d400dbfb26a000df99350006fac9a801b7c64d400dbfb1ea000df98f50006fac7a801b7c63d4001bfa1ea000df90f50006fa87a80037c43d400dbfb16a000df98b
  | 4 => 0x12fe630c8016f3186403bf9883201f7e841900fbd420c807ef9906403fb8c83201fba6419013ed320c8037f3086400bf58432015fcc019002fd600c80b7f326a200bf59351006fca9a881b7c54d44097f31ea200bf58f51036fea7a88037d53d44077f316a200bf58b51036fea5a88037d52d4401dfa16a200ef50b51007be65a8803dd32d44057f306a200bf58351005facb28816fe6494403df324a200af99251005fac928807bd64944015eb24a204bf98e51005fac72880efe62944017eb14a200efd0a510077a8528803df3294401ee994a201bf9865100efea32881bf751944057f304a200bf58251005fec8a8816fc6454401bf2a2a200df15151005fec6a8812fc6354401bfa9aa200df54d51005fec4a880efc6254401bfa92a200df549510077e84a8803bd4254401ef992a200f74c951037eea2a88077e51544017fb02a202bf18151035fcca28816fe64144017eb20a204bf98c51005fac62880efe62144017eb10a200efd08510077a8428803df3214401ee990a201bf9845100efea228807f65114403bea88a206fd54451015fcc028802fd601440b7fb2e8206bf99741005facba0816fc65d0401dfaa68205ef15341025fcc7a0817de63d04016f31e8200bf58f4102fbac7a0802dd63d040bdfa1e8200ef50f4101dfcc5a0817ee62d0401773168200bf58b4102fdac5a0802ed62d040bdfa168200ef50b41007be65a0803dd32d04057f3068200bf5834100dfecb2081afe6590403bf32c82009f99641005facb208077d65904013eb2c8201bf19641005fac920812fe63904017eb1c8203bf98a41005fac520803bf4290401dea148200f7cca41007ba6520806fe6190403fb28c8200fd5464100f7e8320817f741904057f3048200bf58241005fecaa081afe65504017eb2a8206bf195410077ea8a0803bc54504017fb1a8204bf18d410077e86a0803bd43504017fb128203bf189410077e84a0803bd4250401ef9928200f74c941007eca2a0803f5515040bfba0a8201ef90541005fec0a080afc60504037fb288206bf99441005faca20806fc651040b7f3208204bf98c41005fac62080efe62104017eb108205efd08410077a8420803df3210401ee9908201bf9844100f7e8220807f64110403dea088205fd50441015fcc020802fd60104097fb2e6206bf99731005facb98812fc65cc4097fb266205bf99331005fac998812fc64cc4077f3166200bf58b310077e8598803bd42cc409ef9966200f74cb31015fcc198802fd60cc4037fb2c6206bf99631005facb18806fc658c4037fb246205bf99231005fac918806fc648c4017eb1c6200f790e31007ba871880efe628c4017eb146200efd0a310077a8518803df328c401ee9946201bf9863100fbe6318813f7318c4057f3046200bf58231005feca9881afe654c4017
  | 5 => 0x8d420077e86a1003be4350801dea1a8400ef10d42007dca4a1003ed525080bf7a128403ef90942005fec2a1006fc61508017fb028402bf181420077ecaa10033f6550801df32a8400ef5954200778caa10033c6550801dfb1a8400ef98d420077ac6a1003bc6350801dfa9a8400ef94d420077aa6a1003bc5350801dfb128400ebd89420077ea4a100fbe5250801d72928400ef549420075aa4a100fbc5250801dfb0a8400ef985420077ac2a1003bc6150801dfb028400ef981420077ac0a1003bc60508077fb288406bf99442005faca2100efc651080b7f3208400af99042025fcc62100fde63108016f3188400bf58c4201fbac621002dd63108077f3108403efd084201fdc842100fbd421080bf6a108401bf98442005fac22100afe60108017eb008404bfd9732035fccb99002fd65cc8097e32e6404bfd933202dfcc999002fd64cc8097e3266400f7d4f32027bca799003dd53cc809ee29e6400f7d0f32027bc8799003dd43cc809ee21e6400efd0b320077a8599006fe61cc8017eb0e6402bf98332005fac199013df65cc801ef32e6400f759732027b8cb99013df64cc801ef3266400f759332027b8c999003df54cc801ef2a66400f755332007b8a999003df52cc807ef2966400f754b3201fb8a599003df42cc801cfa166403f790b32007ba85990039d42cc807ee2166404f7d8732007bcc399003dd61cc809ee30e6404f7d8332007bcc199003dd60cc809ee3066403bfd9632035fccb19002fd658c8077e32c6403bfd923202dfcc91900fbe648c8015f3246400bf5923201f7ac919002bd648c8077e3246400bf58e32005bac71900efe628c801f7a946403fb14a3201f7e851900fee428c807dea146400fb50a320075a851900fdf328c809f79946401bf98632005fac31900afe608c8017eb046400bfd9532035fcca99002fd654c80d7e32a6400bfd913202dfcc899002fd644c80b7e3226400f7d4d32007bca699003dd534c801ee29a6400f7d0d32007bc8699003dd434c801ee21a6400fbd4932007d8a499003bf424c801f72126400ef50932007da8499003ad424c809f79926403f78c932005fec299006fc614c8017fb026402bf18132007beca99003de654c801eeb2a6400f719532007bec899003de644c801eeb226400f719132007bea899003de544c801eeaa26400f715132007bec499003cf624c801efa926400f3d493201fbca499003dd524c807ee2926400f314932007be84990039f424c807ef2126400f390932007ba84990039d424c801e6a126400e35093201fb88499003df614c801ef30a6400f758532007b8c299003df604c801ef3026400f758132007b8c09900eff650c80d7f3286400bf5943201df8ca1900eff640c80b7f3206403ef990320057cc819002fd640c807deb206400af5903201df8c819
  | 6 => 0x9ef298a604df54c53037baa62980efe6214c017eb10a601bf98453005fac22980afe6014c017eb00a605bfd9743035fccba1802fd65d0c0b7e32e8600efd534302f78a9a180efe62d0c017eb168601bf98743005fac3a180afe60d0c017eb068604bfd9643035fccb21802fd6590c097e32c8600bf59243025fcc721813de5390c01eea9c8604efd0e4302fbe872180efe6290c017eb148601bf98643005fac32180afe6090c017eb048600bfd9543035fccaa1802fd6550c0d7e32a8600efd514300778a8a1803de5350c01eea9a8605f7d0d430277c86a1802ff6250c077e3128600bfd854300df8c2a1802ff6050c057e3028604bfd9443035fcca21802fd6510c097e3288605bf99043025fcc621813bf4310c09ef2188604ef50c4302fba862180efe6210c09f73108600bb98843005fac421813ed6210c0176b108601bf98443005fac22180afe6010c017eb008605bf99352005fac9a9012fe63d48017eb1ea401bf98752005fac3a900afe60d48017eb06a400bf5965202dfcc92900fbe64948015f324a400bf5925201f7ac929002bd6494801bf2a4a400df15252025fcc72900fde63948016f31ca400bf58e5201fbac729002dd63948077f314a403dfd4a52037dea529006fe61948017eb0ca402bf98252005fac129002ff645480b7e322a400bfd8d52025f8c6a901bef5254807bf292a400bfd855200df8c2a9002ff60548057e302a406bf9945202dfcc82900fbe64148015f320a400bf5905201f7ac829002bd6414801bf2a0a406df15052025fcc62900fde63148016f318a400bf58c5201fbac629002dd63148077f310a403dfd485201fdca42900f7d521480df6a90a401bf9845201fecc229002f661148017eb08a403fd58452005eac22900afe6014807fd300a400be98052005fac02900ff960148017cb00a405bfd9742035fccba1002fd65d080b7e32e8400efd534202f7ca9a1003bd54d080bde2a68404bf98f42005fac7a1017bf43d0801df21e8400ef50f4202f7887a1006fe61d08017eb0e8402bf98342005fac1a1017bf65d0801df32e8400ef5974202f78cba1017bf63d0801df31e8400ef58f4202f78c7a1003bf53d0801df29e8400ef54f4200778a7a1003bf52d0807df2968400ef54b4201f78a5a1017bf61d0801df30e8400ef5874202f78c3a1017bf60d0801df3068400ef5834202f78c1a100eff659080d7f32c8400bf5964201df8cb21002fd64908015eb248404bf98e4201fbcc721002de63908017eb1c8403f758e42005bac72100efe6290807f72948400fb54a4201f7e8521017ef42908037f30c8400bf58642015fcc121002fd60908017fb2a8400dfd9542004fecaa101afe65508017eb2a8406bf19542006f8caa10027c6550801dfaa28400ef951420077aa8a1003bc54508017fb1a8404bf1
  | 7 => 0x1400c00c02c00803800400c00000402000000802800800800000000c00800002800402800800800c00000000003401400000000800800000c00400000002c00c00001401400800402001c00000001800000000000002401000001800801000400800400000400400001000000400000000000800000401c00801c00400000800400801c00000c01400801004404000000001400001402000000000006000000405c00400c00c00000c00000801c00000000400400400002000c02c00000403c02400000800400800800402000000c01800c00c00000c00400001801400000000000400000000400000800007c00001800c00000000000c01400400401400001c00400801400001800000400002001c00c00c00000800000401c04400800000400000801000c00002006400000c00002000000400000000800400400c00000801000001c00801401000000805c00800802400c00000000801001002000c00001000800000000000000000001000800800400000401802801000003000401400800c00c00000001000000800000403400000400800800000400000800c07c00c00001c00000007000002400001000000c01c01000000000800801c00000800003800800400000000000800000000000800000000006c03800001401002000000000400002400800000c00001001c00802401400800000000800c00001400800005000003400803c00401800002400402000000000400000400401400c000010097f31ea800bf58f5401dfcc5aa002fd62d50037f30ea800bf58754015fcc1aa002fd60d50017eb2ca805bf9925402efea92a01bbf54950019faa4a804bf98e54005fac72a00efe62950017eb14a801bf98654005fac32a00afe60950017eb04a806efd515402efca8aa002ff63550097e31aa800bfd895401df8c4aa002ff61550037e30aa800bfd8154015f8c0aa01afe651500b7f320a805dfd505402f7ca82a0177d541500ddeaa0a804bf98c5402fbcc62a002de63150017eb18a805f758c54005bac62a00efe621500bf7310a800bb98854005fac42a017ed621500176b10a801bf9845402fecc22a002f661150017eb08a805fd58454005eac22a00afe601500bfd300a800be98054005fac02a017f960150017cb00a805bf99353005fac9a980efe62d4c017eb16a601bf98753005fac3a980afe60d4c017eb06a600bf5965302dfcc929813be6494c015f324a600bf592530277ac929802bd6494c097f31ca604dfd4e53037bea72980efe6294c09f7314a600bb98a53005fac529813ed6294c0176b14a601bf98653005fac32980afe6094c017eb04a600bfd915302df8c8a981bdf5354c09bf29aa600bfd895301df8c4a9802ff6154c037e30aa600bfd8153015f8c0a981afe6514c0b7f320a600bf59053025fcc6298137f5314c0
  | 8 => 0x2d5a8f9bd2842640c9800000000000000098a090000000f6925b33000239a901820003248c21d214fb0288a0da8df0000b58a30000772f39808000000000001c090d14601b8db8b90000000001f3af48002e51992012a11318402d3aa191c1528002f50000328000000f511700010180025924b2dda301c50d30000000c90002fc80000a00016d1cd8000000000000c700032c0c511e8000000d5a3d0002ef16200000000022200020211531184b0e200024180019f2250001d72da8c4a340188002ec0b88108000001cd2438000000000ab2110000a61a425c0000001b4940b312fc0000460fb8002610592a00001fe0000000ea00000000000028e0000000b81be3150000000d18000d914900000005200000000008fa1a80000001980019a81b0000000000002178002052768ad00028b105a3600002a80011aab3a1b0fc8571e805590c0262408bb86380000024bb020000001a78cf0000298000000458000fa08e9f200000000015e8001399cc0001339ee0e9a2700000000004f80003819a0000000002c28002e78001e39e4b270ae81c0000002b7113affac00000ce0000052f61e90f18000001c2ac1aa98000002fa0000b08000e930ca1f1ec28911e2f200010a80018e0000000000cd00029580007300000012e0cb000330a9393aab60308002e3a1589aa219e605c87f1d2a3d8000d7981aa38289de8b22ce1bf31cac08000001d83260002c20001d0b0a22e8000002a531280013318b8a29a51ec80000b02e28b9eb8ad8a80741e18dd95800016c02180024325692f8000000000630002071780000360dc00000000029a3291c026bade00000000032f1482c81180002442e82db2cf18f0000dc992a4e27500000000e9a600000000004c8aa0bc2b9afe80001380000013d00000028580000010108f00014e0c880000000000000004b9d48001f40000000000000000000000000001b594413b2f887d8a68f413532d00000000025096e93e119000088b358002792712a781131333a00021700715d248800800000801000c00c00002000400001401804c00000c01000002001001000400004800000402000000000000001003800800800000000c00000000000400004000000000c01c00000001800800000401001403400401000402801000400400401002000000c07800400001801c01800001c05401001800001800c09800800000400400400000000400800000000401400c03001402400400801000403403c01002800000000000400800002000000000001000002000403800000000001c00000000000800c08405401400404801800801c00800000001002800000000401800400800402c01800000800400000800400400400000400000000800c00800803c00001c00400000c00003c01c01000002000000c0000040000100040
  | 9 => 0xfa0000000001bc84a1dd0000001f8114ae1241150ac730887a00000019b98c9e0304949876b319af0000268c0927a9520031380219480032500028800000026200006e2a41b02558228b300026988c2420bd9b10f39532f5aa582900012a975270a3c9ce80019798a0002cc2c792c09c0000b280000010b8000000002888000000000e6a290000000001618000000000002ff000000000000000171b33ab1b0f0000000002ed96b9cb8000e480012e8002b780009f12d0002e0a2f0000000000ef25795106d97b0002928c58000002a28000000700003299e2ae2800130a6c00022c80030ba9225298fa460002458550c003b99800980003e8000001ef0000a10000000f8b2f8c403930f9eeaa0a651bb0000000000000f030e0bf238833aef99f8000001918000002298000000a7a608001f596080000032bab30000000000000000001800001d880000003f9641858001f0a339f32131a300028da2012b90b015ac48248000908001422e70001048f9800000000102800166926249b348e31c93120dd0c80991cc85f0101e217b92d8002c980000019e8002b5aab8589baaa880009627d04784508121430818c0651ed8001390001bb93700018681e0001ed0b70002caaf28000950000001e58002ea00000014f0000e424280006200030012880017c8001ac8002913090000368001c58708000000002838000002478000000002700870420bd0001b90518000ed0000002a929980014009d866b200000000002320319430000d81788000000da0000000002e6ad9a3726db38a7da8211080000013f30a8001a20000b405a3188000acb360000000003228000002080002d802c1a90a52a69311f98000e18000000000c10000002dd0000000000000b48000000000000001568000000000003168000000000000808000000000000000002e900000000030c0000003328000000000e500011600020280010e2ad1798000f2012157ad00349fd8000000000002870000002538af2f6a0c27c9ae00023b04900000029880014d887ad509000000000a875a4ca1080013f8002720002cd80020ea7b1ca8bf8d6069a7a8f12740001e98541638002f0aaa00031c19897d11caf43268429b89a080000028196aa12000001968968297091a401c4159a550000d00000a03398899828000000000000002b90000000060000000001f6083083a5f21822497e8762b114193818898800000026780017430400000000000000000021a0000eba4a8f28002e5b1f10026329e8a081c8d12d28000001588000000000000000000000000f78068000000000000440c60000000000000d883a16ca6ea981f11900e62258ca04e86e8002bcaba91a0000000000001af93200000028a00011b00001531111285d0000000000000000000002f1004000000079800000000306
  | 10 => 0x10bb1778ae0f900000025894680018d80013eae61d6ad7014b23092a6e0711f89130002570000001fa80020b0002d21aea0980004e0c2a9922e11880000003cadc02d08007f8002f780001900000f8b60002619e78000000002bd8000000003280001da0002060000000001d584d0000001a70002c68d6b3a80000014d0000df8000002260000000000002eb0000000001ab80032893020a8000ed80000015d8000001ba1ff8cd8000310001c100000000000018d000000094b2a00005e2b41b1b2ca9426b09caa4b181f78cca8e868053093b25800072a5e0691e30011368ec8000002a60000000000002a820a00032aa758000000fda330438000350091be86d00027293c22b3350000000001a820180000025003a98300003c00000018380017017f80000000014a8001a48000000000000000001f1a5b94c0000002812f800000000004f25fab5000226a150000002af8003198000000002cf8000000000000001298000000c6a9180016007b2ec8001540000048378001f280000013485000003d30da4f1ad13590ca669721bd9178850720e00f6205a5b0ff307b22227a8d0000000748fc13d8002cc8001d50000000000000000001360000000000223211a391d80000000580014780000000000018b0002781dbab49770001fd24916786a9b507d0002730160f49b78002ae8001df2cd000000123b1900010d8b99458640d38828fd0e10000611e880000000026a868800000000187a68800000000067a7b92123a89680029b916a0ba932b00ba2e016900002a0472e486196280030091420da5132e0000000d480009b1080000001e71dc2d600000000000015a0230001ef80023180027f919abb8000002d100000008400015222d00300032b1890d22390b793a29f00000000000007387180007800000000000000008d0c312523f8002e18000000eab2ea2c0000002d090600031e0be2df9bfa1b8132f70000b100000000000000027380022816a06493b8001960000002230000000001a5800309a6d0001f5282ac40000000001c700000005b800000163000000000000206a9d00d2bf9072ceac30000179f92dca1c94e8a182b19ca9b17e0001eb0000448672482b0a748ce92180000000015c8001932600000002f98000958000000000000000000000000ee30d0000598000001c206f0cbb27aab196b108002078de2d93370869b08000001d795e2c39b800e04d9202d79091d305100021d9aa1f688c80007a8a38001b99728000000000000000002968001a10001b60cc0a880000006082e974a03a6931b190a861c38f300000001180027723e94880000019c31d2868001c801a12c999a1d24d9612209d41d98a9853803a1680018aaed126a898002809232358978c796b2e32df18406c19382f9a6a5322425d30b2bc06295a91201d1
  | 11 => 0x22da5c80021e266000285143a4d0258001fc26a0b190223781719da7e9aab1aaeaaf90000e5aa71dd97900000032399d0001d38f80278001e08002d30000000001fc8001c30000ac05e80000000000000000000023080000002daae1b702f2128001d629a8000a90000003179732ba1db00000024fa7e31e8001a18002e20000000002b220c89fa9d97a8e296f93c9c606a22f8e08000001118000000000000000002f0000040800000254800254336afd99427f00010523b9de0000003208000bc80c2eb80021ead18560c3857b3008809e80012092200023a1b380005280001400031f89a00000000004199520e00001800000016e29087c28f08d9ac0ab8000000000000750002470000000000000322960000f714483325188a99595b20494c86f8000001738001bc1ea0858000a20000d98000000002192778003058000000000001c882080010f8001088000000000000000002b680000014280004a80d81f00000000014500000000000010990e8002638000f5ad69a88ef80001a80008e1e400780001d87b95600017a002a7a0000000000000000000001c98b3aa3000000339303307211a448af9031ca00003f1281592e880000005d80000000000b9500d7294a8a9fe80005f9f711b9860001da8002560890002e981ea328302680a40000000002fd3050000002b280011f2310aa8999ad86b050886000213a4a155b381a01042d412915b9d11cb000000166315a0f1df976af1907a4c00030680015f11d00000010f00025eabb1ab0252be84c00f0eb09d1329658002fba288e38000000168ba8cfadb97c09410a0003100000002d492725a0002040000818d402426c87eb0e80026f98e99b00000000012b000091184a1604117d8001b280022380000023c0001e12801228000002bf00000032d8fab1b80011116d8002658002350002349c6a9c0789972da2848000000000e7000219a5980015180015522a86b9038a709b92a039aee29ca830003162ac05aa6289200000000015c154877b241fb2228d2808a878602eea101652ad8791ff2c12fa8002f31670dea188001ea80008b27180000001f80000000011fa36800000000000000000058023856acb00008223e00000027c17580026f0000001378002788000001870000e81570db0002bd0001912c8970b32337b010002a2000169ab884882bac631d80020089e0000a4a1f9c48000000000388001ce0000000003140fe0001158000848002cb8002de80001292f000138800000189a4e94103d8002452761cf00002000022b94b8000001f01c79812c92be02c9b41c1ac51cf88b800a8ca979b2264a5d95f8ec2fb2382210a59a2a0310087c964a14a088ff98533414b0359a986c84802831480007e0b69101f4a468430c185b1e680c8270fb1d19d01341240d09b30b50932d897
  | 12 => 0x1068000000000f0b0185c02119e03421c1470002c58000b00658662fe321a8c000303aaca5800000029f8001d9000124a0f97f20d0548498e8b170e7a671b6ab81fbaca0970fea2a04680000800000000000029e0000000000000000ee83b16f31a0d50370001dc9e500014a00000000000000027980017625aae40000000000002520000001920bea3f0ca95380003e2aaaaf098
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x5429842001ed7329842001ed5329842001677509842001675509842001eb7425842001eb5425842001ed7325842001ed53258420016775058420016755058420016e72058420016f22058420016e5205842001ef1205842003eaf6250b1001eac6250b1003fa62150b1001ece624cb10006cd624cb100078d424cb10007c53248710004bf745961002cbc74596100063f74596100063c74596100167a20596100063e65d0a100063d65d0a100063e6550a100063d6550a1001eae6250a10006ad6250a100065e65cca100065d65cca100065e654ca100065d654ca1001ece624ca10006cd624ca100078d424ca10006796548210007a94248210007c93248210004bf745951002cbc7459510004df7359510024dc7359510004ef725951001cec72595100347e75d91100047d75d9110004df7359110024dc7359110024de76d8d10004dd72d8d10004de7618d10005cd7218d100265e7518d100265d7518d100269e7418d100269d7418d10026ce7218d10004dd7218d10026cd7218d10004cd7218d10026d57118d10026d97018d10004df7358910024dc73589100069f63d09100069c63d09100069f63509100069c6350910006af625091001eac6250910004de76cc910024dc76cc910004de764c910004dc764c91001ece624c910006cd624c9100078d424c910014f47650510015f07050510026d4638c510014f4764c510007a54288510014f47648510007c532485100065f63d41100065c63d41100065f63541100065c6354110017701054110026d8638c110007d2318c11000cf8764c110007d1314c11000cf87648110007a94248110007c93248110007e121481100147f70594100147d7059410004bd72990100163f50990100163d5099010004bf72590100163f50590100163d5059010016b71059010016b51059010004dd7298c100165f5098c100165d5098c10004df7258c100165f5058c100165d5058c10016d71058c10016da1058c10016d51058c1000ed91058c1001eae749881001ead749881001ece739881001ecd73988100166f50988100166d5098810006ae7458810006ad7458810006ce7358810006cd73588100166f50588100166d5058810016e71058810016ea1058810016e5105881000ee9105881002cbf76d0810004bd76d08100063e65d08100063d65d08100069e63d08100069d63d081001eae62d0810006ad62d0810004bf7650810004bd76508100063e65508100063d65508100069e63508100069d635081001eae6250810006ad6250810024df76cc810004dd76cc8100065e65cc8100065d65cc8100069e64cc8100069d64cc81001ece62cc810006cd62cc810004df764c810004dd764c8100065e654c8100065d654c8100069e644c8100069d644c81001ece624c810006cd624c8100078d424c810
  | 1 => 0xb200072c7550b2001eaf6550b20006ad6550b2001eaf6350b2001f8e6350b20006ad6350b2001f8d6350b200068d6350b2003eae6150b20006ad644cb20026ce634cb2001dcf764cb20006cf764cb20046ce654cb2001ecc654cb2001ecf644cb2001f8e644cb20006cd644cb2001f8d644cb200068d644cb20006cd3258720006cd63487200063e64d43200063d64d43200065e63d43200065d63d43200072d42d43200074d32d43200063e64543200063d64543200065e63543200065d63543200072d42543200074d32543200167a7099620004bf745962002cbc74596200063f74596200063c74596200063e65d0a200063d65d0a200063e6550a200063d6550a200065e65cca200065d65cca200065e654ca200065d654ca200078d424ca20004df7358620024dc73586200367a65542200157b76542200067b76542200073b74542200073874542200167b64542200067964542200073b42542200073942542200075b3254220007593254220004bf745952002cbc74595200047f75591200347c7559120004f77158d2000cf47158d20005ad7490920005cd7390920014ec765092002eaf7650920006ac76509200072f75509200072c7550920006af6550920006ad6550920006af6350920006ad635092003eac6150920007ab7050920007a8705092001eaf605092001fab60509200078d42cc920005ad748c920005cd738c9200078f424c9200078d424c920014ec764c920026cf764c920006cc764c920046ce654c920046cc654c920006cf644c920006cd644c920007cb704c920007c8704c92001ecf604c92001fcb604c920006cd32d8520005ad74c8520005cd73c8520014ec76485200072d42d41200074d32d4120005797594120007a94294120007c932941200072d42541200074d325412001cf87654120007a94254120007c932541200367b76541200067876541200073b74541200073874541200067b64541200067964541200076b72541200076872541200167b62541200176b62541200073b42541200076a42541200073942541200076942541200072942541200075b32541200076a32541200075932541200076932541200074932541200076b215412000769215412001e3f429942001e3d429942001e5f329942001e5d329942001e3f425942001e3d425942001e5f325942001e5d32594200167a205942001e79205942001e9f329902001e9d32990200163f50990200163d509902001cbf725902001cbd725902001e9f325902001e9d32590200163f50590200163d5059020016af2059020016ad205902001e9f4298c2001e9d4298c200165f5098c200165d5098c2001cdf7258c2001cdd7258c2001e9f4258c2001e9d4258c200165f5058c200165d5058c20016cf2058c20016cd2058c2001eb7429842001eb
  | 2 => 0x169f4058c400169d4058c4001ece739884001ecd73988400166f50988400166d509884002eaf425884002eae7458840006af545884002eac5458840006ce7358840006cd73588400166f50588400166d5058840016af4058840016ad40588400053c75508400063e65508400063d65508400069e63508400069d635084001eae6250840024df76cc840004dd76cc8400065e65cc8400065d65cc84001ece62cc840006cd62cc840004df764c840004dd764c8400065e654c8400065d654c84001ece624c840006cd624c8400078d424c84002eb74298440006b54298440006d73298440006d53298440016775098440016755098440006b7545844002eb4545844002eb74258440006b54258440006d73258440006d53258440016775058440016755058440016b74058440016b54058440026cf3258b3001eae6250b30006ad6250b300078d424cb30004bf745963002cbc74596300063f74596300063c74596300063e65d0a300063d65d0a300063e6550a300063d6550a3001eae6250a30006ad6250a300065e65cca300065d65cca3001cdf764ca300065e654ca300065d654ca3001ece624ca30006cd624ca300078d424ca30005cd720c630005d9700c630004bf745953002cbc7459530014dc7650d30014dc764c930006cf624c9300078d424c930004de76cc530014dc764c5300175830541300265f32994300265f3259430004bd72990300269f32990300163f50990300163d5099030004bf72590300269f32590300269c31590300163f50590300163d50590300169f30590300169d305903001eae749883001ead74988300166f50988300166d5098830026cf3258830006ae7458830006ad7458830026ce7358830026cc31588300166f50588300166d5058830016cf3058830016cd305883002cbf76d0830004bd76d08300063e65d08300063d65d083001eae62d0830006ad62d0830004bf7650830004bd76508300063e65508300063d655083001eae6250830006ad62508300065e654c8300065d654c8300069e644c8300069d644c83001ece624c8300078d424c830006b74298430006b54298430026d73298430006d53298430016775098430016755098430026d43158430006b74258430006b54258430026d73258430006d53258430016775058430016755058430016d73058430016f23058430016d53058430026f13058430004dd768c4300069d648c430006cd628c430006d5618c43001eae729932001e9f329932001e9d32993200047f75593200347c75593200063f75593200063c755932001e9f325932001eae325932001e9d325932001ece7298f2001e9f4298f2001e9d4298f2001e9f4258f2001ece4258f2001e9d4258f2001ecf2158f2002eae6450b20006cd6350b2001daf7650b20006af7650b200072f755
  | 3 => 0xc644c9500074f724c9500074f624c9500074c624c9500071f424c9500074e424c9500071d424c9500074d424c9500070d424c9500053e740c9500053d740c9500055e730c9500157a700c95000579700c9500063c64d85500053e74985500053d74985500057970985500053f74585500053c74585500063c64585500055f73585500055c73585500056f72585500056c72585500057b70585500055e73d05500055d73d05500056e72d05500056d72d05500157a70d05500057970d05500047e76905500047d76905500157a70105500057970105500057b704c55001578704c5500047e760c5500047d760c5500053e740c5500053d740c5500056e720c5500056d720c5500157a700c55000579700c5500053e74c85500053d74c85500055e73c85500055d73c85500074d32c85500157a70c85500057970c85500072d42885500074d32485500047e76085500047d76085500053e74085500053d74085500055e73085500055d73085500072d42085500157a70085500057970085500063f64d81500063c64d81500057974d81500073b64d81500073864d81500057972d81500073b42d81500073942d81500075b32d81500075932d81500367970994500063e65d08500063e655085001eae6250850006ad62508500065e65cc8500065e654c85001ece624c850006cd624c8500078d424c8500047f7558b400347c7558b4002eaf4258b4001ece624cb40006cd624cb400078d424cb400173a40543400167a70996400063f74596400063d65d5240005b970d52400063d6515240005ad7215240005b970152400063e65d0a400063d65d0a4001cbf7650a400053c7550a400063e6550a400063d6550a4001eae6250a40006ad6250a400065e65cca400065d65cca400065e654ca400065d654ca4001ece624ca40006cd624ca400078d424ca40004df7358640024dc73586400367a655424002db874542400073b54542400073854542400157b76542400067b76542400073b74542400073874542400067962542400073b42542400073942542400075b3254240007593254240004bf7459540014bc7650d40014bc7650940006af62509400078d424c9400059d73d0540005ad72d0540014bc765054000579759414001738405414002cf876541400367b76541400067876541400073b74541400073874541400167b64541400173b64541400073b43541400073943541400067b62541400073b42541400073942541400075b32541400075932541400073b415414000739415414002e3f429944002cbc745944002e3c745944002e3f42594400167a405944002e7940594400063d65d5040004dd7298c4002e9f4298c400165f5098c400165d5098c400069f5458c4002e9c5458c40004df7258c4002e9f4258c400165f5058c400165d5058c40
  | 4 => 0x87500055e73087500055d73087500072d42087500157a700875000579700875001eae6250a50006ad6250a5001ece624ca50006cd624ca500078d424ca50004bd72d9150005ad721915002e9e731915002e9d731915002eae7219150004bd721915002ead7219150004ad721915002eb6711915002eb5711915002eb9701915002e3c64d51500147e76951500063f64951500157a70951500147c76551500063f64151500055e73151500055d73151500056e72151500056d72151500057671151500057571151500157a70151500147e7694d500053e7494d500053d7494d500056e7294d500056d7294d500147c7654d500147e76949500053e74949500053d74949500063c64949500055e73949500055d73949500157a70949500147c76549500053e74149500053d74149500063c64149500055e73149500055d73149500057671149500057571149500157a7014950004be76d095002cbc76d0950004be7650950004bc76509500072e52509500072d52509500069f64cc9500069c64cc9500069f644c9500069c644c950006cf624c95001ecc624c9500074f524c9500074c524c9500078d424c9500063c64d45500147e76945500053e74945500053d74945500147c76545500063c64545500053d72d91500073b70d91500053e74991500063f64991500057970991500057b70591500055e73191500055d73191500056e72191500056d72191500057671191500057571191500053e76191500063e76191500071e73191500071d73191500072e72191500053d72191500072d72191500052d72191500073671191500073571191500073970191500053e7498d500053d7498d500056e7298d500056d7298d50005797098d500053f7458d500053c7458d500057b7058d500157a70d0d500057970d0d500056e7210d500056d7210d500157a7010d50005797010d500053e74989500053d74989500063c64989500055e73989500055d73989500057970989500053f74589500053c74589500057b70589500053e74189500053d74189500063c64189500055e73189500055d73189500057671189500057571189500157a70d09500057970d09500053e76d09500053c76d09500073a70d09500073970d09500053d74909500055e73909500055d73909500157a70909500057970909500047f76509500047c76509500063f76509500053e76509500053c76509500063c76509500043c76509500072f72509500072e62509500072d62509500073a70509500073970509500053e74109500055e73109500055d73109500157a70109500057970109500071f64cc9500071c64cc9500071f42cc9500071d42cc9500053e748c9500053d748c9500055d738c9500072d428c9500157a708c95000579708c9500072d424c9500071f644c9500071
  | 5 => 0x347c7559121005cd738c9210078f424c9210078d424c92100cec764c921026cf764c921006cc764c921046ce654c921046cc654c921006cf644c921006cd644c921007c7714c921007c4714c92101ecf614c92101fc7614c921007c5329452101cf47654521007c53254521006cd32d812101e3f429942101e3d429942101e5f329942101e5d32994210047d709942101e3f425942101e6e425942101e3d425942101e5f325942101e5d325942100e76215942101e7521594210047f705942101eae729902101e9f329902101e9d329902101e9f325902101e9d325902101e9f4298c2101e9d4298c2101e9f4258c2101ece4258c2101e9d4258c2100ecf2158c2100ecd2158c210066d655082102eae6450821006cd635082101daf7650821006af76508210072f75508210072c755082101eaf655082101f2e6550821006ad655082101f2d65508210062d655082101eaf635082101f8e6350821006ad635082101f8d63508210068d635082103eae615082101fa6615082101faa605082101fa960508210167a759802101679759802101ebb429802101eb9429802101edb329802101ed93298021006ad42580210067a755802100679755802101ebb425802101eea425802101eb94258021006e94258021006a9425802101edb325802101ed9325802100eeb215802100ef2215802100ee9215802101ef121580210147c75593500147c7558f500053e7494f500053d7494f500056e7294f500056d7294f500147c7558b500053e7494b500053d7494b500055e7394b500055d7394b5001eae6250b50006ad6250b500072e5250b500072d5250b500474f524cb500474c524cb500078d424cb500147c75587500053e74947500053d74947500363f64993500053e7498f500053d7498f500056e7298f500056d7298f500056e7210f500056d7210f500053e7498b500053d7498b500055e7398b500055d7398b500055e7390b500055d7390b500047f7650b500347c7650b500063f7650b500063c7650b500072f7250b500072e6250b500072d6250b500055e7310b500055d7310b500071f42ccb500071d42ccb500053e748cb500053d748cb500072d428cb500072d424cb500074f724cb500474f624cb500474c624cb500071f424cb500074e424cb500071d424cb500074d424cb500070d424cb500053e740cb500053d740cb500053e74987500053d74987500055e73d07500055d73d07500056e72d07500056d72d07500347e76907500047d76907500347e760c7500047d760c7500053e740c7500053d740c7500056e720c7500056d720c7500157a700c75000579700c7500053e74c87500053d74c87500055e73c87500055d73c87500074d32c87500072d42887500074d32487500347e76087500047d76087500053e74087500053d740
  | 6 => 0xd624cb410078d424cb4100e76719964100e3f419964100e3d41996410047d70996410047f70596410063e65d0a410063d65d0a4101cbf7650a410063e6550a410063d6550a41006ad6250a410065e65cca410065d65cca410065e654ca410065d654ca4101ece624ca41006cd624ca410078d424ca4103676655464100cbe76d51410063f65d514100db671d51410059d7315141005ad721514100db67115141005b9701514100cbc7650d410269c6350d4100cbc76509410053c7550941006af625094101eac62509410078d424c94102db6749454102cf4765454100734545454102eaf425884101ece624c841006cd624c8410078d424c841026cf3258b3101eae6250b31006ad6250b310078d424cb3102cdf7650e3101cdf764ca3101ece624ca31006cd624ca310078d424ca3102cbe74d9531004bd74d9531006af625093101eac625093100cdc764c931006cf624c9310078d424c93100dd4714c9310265f32994310047d70994310265e43594310265f32594310047f70594310269e7399031004bd72990310269f3299031004bf72590310269f32590310065d6550c3102e9e6450c3101eae749883101ead7498831026cf3258831006ae7458831006ad7458831026ce7358831026ce4358831006cd435883100ecf315883100ecd3158831026cc305883102cbf76d0831004bd76d08310063e65d08310063d65d083101eae62d0831006ad62d0831004bf7650831004bd76508310063e65508310063d655083101eae6250831006ad62508310065e654c8310065d654c8310069e644c8310069d644c83101ece624c8310078d424c8310167a7598031016797598031006bb4298031006b94298031026db3298031006d93298031026d830580310067a7558031006797558031026da4358031006d94358031006bb4258031006b94258031026db3258031006d9325803100edb315803100ef2315803100ed93158031026f1315803101e9f329932101e9d32993210047f75593210347c75593210063f75593210063c755932101e9f325932101eae325932101e9d325932103eae215932101eac215932101eaf205932101ece7298f2101e9f4298f2101e9d4298f2101e9f4258f2101e9d4258f2101ecf2058f21006ad644cb21026ce634cb2101dcf764cb21006cf764cb21046ce654cb2101ecc654cb2101ecf644cb2101f8e644cb21006cd644cb2101f8d644cb210068d644cb21006cd325832102cef7650a21006af7650a2102eac7650a210072f7550a210072c7550a2103eaf6550a21006ad6550a2103eaf6350a21006ad6350a21007a77150a2103fa47150a2101eae6150a2103fa65150a210078d42cca210078d424ca21007a54254621004df7358221024dc7358221006ad425822102cbe74d9521004bd74d95210047f7559121
  | 7 => 0x93201f8c42509320071f75509320071c755093201d9f72509320078f72509320078f62509320078f525093201f8e52509320078d525093201f8c525093201f8f215093201f8c215093201f8f205093201f8c2050932025ce7650932005cc76509320074f7550932045ce7550932045cc75509320074c75509320054c755093201dcf745093201f8f74509320078f64509320078c64509320078f54509320078e54509320078d54509320078c5450932005cf7150932005cf70509320078f76509320078e76509320078d76509320078c76509320078f75509320070f75509320078e75509320078d75509320078c75509320070c75509320078f65509320078e65509320078d65509320078c65509320078f71509320078e71509320078d71509320078c71509320078f70509320078e70509320078d70509320078c70509320078d42d85320078d42985320078d42585320055e75185320055d75185320059e74185320059d74185320078d4218532006d56118532005da7018532005d970185320078d42d81320055e75981320055d75981320078d42981320078d4258132005d77158132005d471581320055e75181320055d75181320059e74181320059d74181320078d4218132005d67118132005d5711813201e9f329903201e9d329903201e9f325903201eae325903201e9d3259032026ad3259032026cd7298c3201e9f4298c3201e9d4298c3200c7c755935101eae6250b51006ad6250b510072d5250b510474f524cb510078d424cb510367b505835102e9e739925102e9d739925102eae7299251004bd729925102ead7299251004ad729925100eb6719925100e3f519925100e3d5199251004bf725925102cbf76d0a51004bd76d0a51004bf7650a51004bd7650a510069e64cca510069d64cca510069e644ca510069d644ca5101ece624ca51006cd624ca510078d424ca5100c7e76951510063f649515100d7671951510055d73151510056d721515100d76711515100579701515100c7c7654d5100c7c7654951006af625095101eac62509510072d5250951006cf624c95101ecc624c9510074f524c9510078d424c95101eae6250851006ad625085101ece624c851006cd624c8510078d424c8510367b505805100cbc7459741004dd7298f4102e9f4298f410069f5458f4102e9c5458f41004df7258f4102e9f4258f4102e9f4058f410269e6350f4101ece7398b4101ecd7398b4102eaf4258b4102eae7458b41006af5458b4102eac5458b41006ce7358b41006cd7358b4102eaf4358b41006ad4358b4103eae4158b4102eac4158b4102eaf4058b410053c7550b410069e6350b410069d6350b4101eae6250b41024df76ccb41004dd76ccb4101ece62ccb41006cd62ccb41004df764cb41004dd764cb4101ece624cb41006c
  | 8 => 0x53d75181420063c65181420059e73181420059d7318142005b67118142005b5711814202ead729904201e9f4298c4201e9d4298c4201e9f4258c4201ece4258c4201e9d4258c4202ecd4258c4201cdc735973201cdc735933201cdc7358732026d4315873201cdc73583320071f5495332024de7615332004dd761533201dce7215332005cd7215332005d67115332005d57115332005da7015332005d970153320055f7550b320055c7550b320071f7550b320071c7550b320078f7250b3201f8e5250b320078d5250b3201f8c2150b3201f8f2050b32026d461587320055e75983320055d759833201cec725963201eae729923201e9f329923201e9d329923201e9f325923201e9d325923201eaf20592320056c7550a3202eae6450a3201daf7650a32006af7650a320072f7550a320072c7550a3201eaf6550a32006ad6550a3203eae6150a32006ad425823202cbe74d9532004bd74d95320047f75591320347c755913201cde76d4d320059e7494d320059d7494d3201dce7294d3201cdc7654d3201dcc7254d3201cde76d0d3201dce72d0d3201cdc7650d3201dce7210d32024ee76d4932005ad7414932025ce7314932005e57114932005e97014932005ad7490932025ce739093201f8c3250932024ec76509320056c75509320078f43509320078e43509320078d43509320078c435093202eaf7650932006ac76509320072f75509320072c7550932006af6550932006ad65509320078f73509320078c735093201eaf635093201f8f63509320078f53509320078e53509320078d53509320078c535093203eac6150932006ad42d81320059e74d95320059d74d9532005cd7299532005cf7259532005cd7299132005d67199132005d571991320055f75591320055c7559132005cf72591320071f549513201dce7295132005cd7295132005cf725513201dcc7255132004de7615132004dd761513201dce7215132005cd7215132005d67115132005d57115132005da7015132005d97015132045ce75d8932005cd74d8932005cd71d8932005cd70d8932005ce76d4932025cc76d493201dce75d49320074f65d49320474c65d4932005cd74d4932005cd71d4932005cd70d493201f4c5254932005ce761493201ece7614932045ce751493201f4e751493201f8e7414932005cd741493201f8d74149320058d74149320074e54149320474c541493201fc67114932005cd711493201fc57114932005c5711493201fca7014932005cd701493201fc97014932005c9701493201f8e42d093201d9d72d09320078f62d09320078f52d093201f8c52d093201f8f21d093201f8f20d0932005ce769093201ece7690932045ce759093201dcc7590932005cd74909320058d7490932005cd7190932005cd70909320055f75509320055c755
  | 9 => 0x7509845200676545845203674545845201e77525845201e75525845201eb7425845201eb5425845201ed7325845201ee6325845201ed5325845203677505845201ebb429805201eb9429805201edb329805201ed932980520367b50580520367a75580520067a545805203678545805201e7b525805201e79525805201ebb425805201eb9425805201edb325805201eea325805201ed9325805201cbc745974201cbc7458f4201cbc745874201cbc745834202e3f659974202cbe7694f42004bd7694f4201dae7294f42005ad7294f420053e75987420053d75987420053e75983420053d759834201ece7298e4201e9f4298e4201e9d4298e4201e9f4258e4201e9d4258e4201ecf2058e4201cec72586420347e76d95420063d74d95420047d70d95420047e76195420057970195420363d74195420365e73195420365d73195420366d72195420367671195420367571195420367a70195420047d701954203679701954200479701954201cbe76d51420063f65d514201dae72d51420363c659514201cbc76551420063f65151420059e73151420059d731514201dae7215142005b67115142005b57115142005ba7015142005b970151420063c65d0d4201cbe7690d4201dae7290d4201cbc7650d420063c6550d4201dae7210d420366c659494202dae74949420072e54949420072c5494942005cd739494202cec7654942024de73d8542004dd73d85420072f72d95420053d70d95420053e75995420063f6599542005ad7299542005af72595420059e73195420059d7319542005b67119542005b57119542005ba7019542005b970195420053e76195420063e76195420071e73195420071d73195420072d72195420073671195420073571195420073a70195420053d70195420073970195420053970195420063c65d8d420053e7598d420053d7598d42005ad7298d420053f7558d420053c7558d420063c6558d42005af7258d4201dae72d4d42005ad72d4d42004be7694d42004bd7694d4201dae7294d42005ad7294d4201dae7214d42005ad7214d420063f65d89420063c65d8942005ad75d89420072f65d89420072c65d8942005ad73d894203dae71d8942005ad70d894201f2e52d4942005ae769494201eae7694942005ad75949420072f65949420072c659494201f8e7394942005ad739494201f8d73949420058d739494203dae7194942005ad709494201f2c525494202dae7654942005ac765494201daf755494201f2f75549420072f65549420072c6554942005af735494203dac7154942005af70549420063c65d85420059e73d85420059d73d85420053e75985420053d75985420053f75585420053c75585420063c65585420053e75981420053d75981420063c65981420053f75581420053c75581420053e7518142
  | 10 => 0xa00200000000400300000000100500800300000200000200001800400200700300900000300000000000200300201200000400100d00400000000100200d00000d00b00100000900200d00000400700000500d00200000002300400500000300b00000800000c00100c00301b00000000900100801200200800400c00400300100000500101600000100000100000800000100100700400900000000000100000300100400200000100000200001600900600000700100000100100000100100000100b00001300000301300200a00300200300600000000000800000800000000000a00002000000100b00100300000000200400100700000100200400a00900100101300000000300100d00100300000000200100300100000000f0367b505835402d3d76d52540363d76d525402eaf4258a54004dd7298c5402e9f4298c540365f5098c54004df7258c5402e9f4258c540365f5158c5402e9f4158c540365f5058c5401ece739885401ecd73988540366f50988540366c525885402eaf425885402eae745885402eae5458854036ad5458854006ce7358854006cd735885402eaf43588540366f515885402eaf41588540366f505885402eac405885402eb7429845403677509845402eb7435845402eb7425845403677505845402ebb42980540367b505805402eb840580540367a755805402e7b545805402e79545805402ebb435805403678525805402ebb42580540367b515805402ebb41580540367b50583530269e7399253004bd72992530269f3299253004bf72592530269f325925301eae7498a5301ead7498a53026cf3258a53006ae7458a53006ad7458a53026ce7358a53046cf5358a53026cc5358a53026ce4358a53026cf32588530367b5058053024bc745974302eaf4258b43026cf3258a43024dc7358643024be76d51430063f65d51430259e73d51430259e7315143005ad7215143005b57115143005b9701514302d9e7494d43005cd7294d4302cdc7654d4302eaf4258843026cf325884302eae7458843026ce7358843026af4358843026ce4358843026ad435884302ecd4358843004bf745835202cbc74583520367b505835201eae729925201e9f329925201e9d329925201e9f325925201e9d32592520063d64952520056d72952520063d64152520056d721525200579701525201e9f4298e5201e9d4298e52046cf5258e5201ecc5258e5201e9f4258e5201ece4258e5201e9d4258e5201e9f329905201e9d32990520363f509905201eae5259052036ad525905201e9f325905201eae325905201e9d32590520363f50590520063d649505201ece7298c5201e9f4298c5201e9d4298c520365f5098c5201e9f4258c5201e9d4258c520365f5058c5201eb7429845201eb5429845201ed7329845201ed532984520367
  | 11 => 0x8a46845766829989181feb00bea5e8802c76d740d8bc4af8bbee367a8ca4000940c8c41a000abc154d2cb60cd2ca63d65bea826bcbe291e7da082b388901c48c633ee120da0002f0000a7c34e00010caea49034216e1882f87ee000b4cc28ae88da7a0d7e000df6000000000000468000000a4200008c000000000000c066980005b4766aaa9aa0007260c0000c5aa36d8447200000058a3980007c4cb2cce3568802d47729a0a3263a700bfa608b28bb64d010a962000000b7a0004fc9f253095a6f40003467dc97e1dad9e8d4c903bc286e341a654e4341f613097466615c7f4000bde000b140a2d4e1065069906e830c1aed20a340000007b0000a840000000006a87fc0000000009e400006a650000000624b46d620000002ce7d6000dd6dace080000000003600000003a2b6c0000009d200000000014600000073200049e95c0009ba0000002560000c4d4265200022c93401a0fc17436ae2aa5c4b635c2bc5440a64e03b464c1be7921ca63e5e6dd05ca5e461206ee160e88180881ce584120964adc3f44e600000300e00000500200101400a00400100500300101900501600600200100000100100400200500000100000100200000100b00000000700000700100100300000000800200200000700000400000100000200000200500000000000a00000300201300000100100400c00000400000000000c00101100000000601100800100100401300200000f00300300100000100000200000400200000500000000400500100100000600000000100400300000000600600000200000601200400400001000000100500400200400200200400400100401600000001900000603300000300001100000200000000300100900000000000600000300300000300400000000000100000000900a00000100701700000000600b00000700300100500700100200000000400000000200000000200300001600100000000400300100000900300000500000700f00700002200000400000a00100100000700100000800000100000000200400b00000600102400200400f00100200300100000200100100501000000100501400000300000100000200000800000100d00101000701f00100001500000100100e00100100d00000200100000b00600000200100500400000000200b00b00001200000900400200300200000000900000000700600800000200100100600301000000100400101500000c00c00200000000000101500300000200100000a01700301000000c00200700200100000000000a00300500400200b00100100c00100000500300b00000001900000200000200100000c01d00200300000800100100000300000100300200000400600100100300100701300000000000000f01100200500900301000000500f00200d00000
  | 12 => 0x4a80d6000000c84534b5457077abf6b9ad724fe00080cb7e81029042c1fa214d5a3d403c000c12c92794784c4c000000000bd220c000768c16d865ee8f0d024f029c442268caa3528d0960000bf412e8fa000000e2c6389dc0000001e2a9cb50cc026a93c0009ac1e42160006ae402a26834000000502000bce00000000000014e000782aa4ab4b0a1d490e000a000008fe37a000000000de4aec3f0000bb090c0002e0b566ea1b00001ee1109045fc9727162e24f84a22402e6000d6a66452cb72000a5a6547eccfe98a394168a5400000032270e2fa6a052a7103120004dae1c308b6e0001647506f0000000000e3e5bccec000000000000000460000c3264e6182ccbc699a4200009b8c0823c7740b47f88e435800011ed14000002c20ce683e2960000000002f26f8cf800000000000000000000000000048200000032a564000000000e1405c0000000003c82c2b8a0000000000000004dc0000002c8000000000bd48a2b2601e2d0850afcc586fc14804400000000000021e7c00005ce00000025800000002a000640000000000000a706345dec004bc4703e23b6000cdc0003a40a0124b789c840a0004ea278d06000cd8bec9844ba000000000ab0000000b423808285a0e3a1c26d60009bc0b066c8e24c2d4656e7889380000caa78e04412504678dd8c0ae4a000000dcc7f2e2639c00000000044c0005467de5520e00700008529c229a7b4000000000000bc09d866820a0008ca0000009b600065ea244228b6a74a902927c238c000000000000000dfa0000de000bf265c00000000000000087c9a442e24419838a948a8ebb26d2908e0642489256000000000000017e0009fe00000000000000000076c2f42a8000020a7a4aa3ec50000069a8be47e4b873e00000031c9bee22000000000d26000686864a1ee4867cb9c2ea06682c050800d985744d847ccd46ce3c00003485fe72cc341cc25ec18d68208a9274e7228bc0320000002d60000000003aa000c523e0af00000000006c085400000000006045200061e000da80003e471c0001369ee7be000d887208d8bd6000b8c88c0ba79ad3a786832588baa0004d200066e00073c000884c7427eda6b3c846000b8e0000000001000000000007800007fe000820aeedae30e39a0e20480009b400039e0000009207a60fe458000000000410bcc000d4c9762322c0a6400000000000052062232600072eafa00037c436d927c8024362b4a73863c0009b278e010a8c0001b60006e0280a3ace08a680e4c89949e684a35a4a0000be433a00043a4980001a0752000dc4b12496262d16580000000c9c9020008b40009ae0b60001086d8894c80ac041860c000924000000b7c17aaaedb4a445680009da7b8822374b30ce8b2ed58000000d963cadf2b62ab24500622baa6ab0e6e20a8b80592
  | 13 => 0xa06c000c86a0c0000007aca2e2dc85a00033c000018000a6e000aa8b028fcbd00004cc7ea000d609420000000007303505e200075e00061400049aa401f0660000000000000b84cb4cb856a000826200000b044fa4621d821c0006e41aa99c6aa5badf4be623e00071e396c2adfe2500005d281c5cc6581a26ded548480001761140003f6ba660a0009c631aa560008e80003d05da332714242464906e28a9e804000202d6e1f41a4028000000000cc6000b1a736844b767e6000c5e000000ad4000688b6859acf40002a273a22238298e2d8000bfc7d2c5c046ce29f600029470a03441cdb870c2b46160e6000c8884ca0e46aac862e000d7a24e000b489147588165a65405ecb96af2970986bca11823a2fcbc289c000712de85ae000000ba2000bae0001c800069c000582beec8208e44a4405160005a89569b0ca0a50a10604dfc000b1c51e508c50b90a1a0009787240000000007e2084746000776000000166354316c6ee38116340b926b219c000c621baacc6f6000830000a96d0800000063632e1568b869221ab2440465a000946000000000000012368c560001bcc780007185429c0acacca0000004f600045e074df80800c266a3701c68060000f87702b21dc6d00e400014200034c00018c0002c6000c44d0c00000076a000000b5c3a68980007aa00000094a0005182d20000ee9f03b0d4400048ce40968b8800000000000000000000000069400071a000d4893ed94b82d1a83a00000035e6d49ca5720000000000421280000005220005ea5b09d687007c55800000059ce201d079e0000000003180001b26ec000000b32000000b740000000bc00067009e00000000086eba40004d4548df06264c40000008c24a40000005144267987d80004de5c200027200000000c0002b028e210e324c0b080000000000007f60000000000c803e25a43c88e000bb8092000000000000000c10a02000000d244862be00000000068c7e40ae000cde9cc0008ae000532000206a9800053ed288cce00000e24000238a0461c78c000378000b9e18a91c000a6000059e000ae00006ac0009ea000000086390000c228dc8c43cc5d60000000000b8daa866000000a722ec00000000038eb22d9a480000b2c000000642000c9e528c0e97c04a264d3cbbad1ca482260000aa000000dce00089ecda3ea4ae754cac8c877c28c6768428143c28860000fa0008ac1e026e60ed789a2c3e94cad0cc46b8ba019216046c6cca6c45a10ea0a3c6000c7c6b0270298856e1ea6833850a2340087cab86b109820004cabac0007a25c4026182d8a00009a30608adba94e1380000000003848ba7f0000000000a3cb5ebd8c30512d1e00000040c000e100000000000000008765540580000005b29000000000008ec00024c6ba000610cea00086a28a4788e687e5e00
  | 14 => 0xd70910a3e0000000000000000009300000000000003dc740ce400048ea5253c2480001d2a4ea9a25c858000000a4a0009525865d86fa04ed2a11a000000000a140000000005dc000cee000000000000000dbed7ccc8220a2a5fac1c12c92c5f8ada15246e6a6c9646693a5d0bc8000c3c0000009fa3fa0000000000007d0000a62d5eae200085e4e276400000036486c9c48d20006b4bf891630a526cf2d3ea7e8880ce254c1ade68aa5d4438484d9c0000003fe000000000760000aba282212e18320caebe880896adeee44c0c8b21f21ec0006e6e0ada245c6ca5c00904145b8ae6162c7eba8b44ccc8ceca24f2dd24760002366f200090a8b00c6d8ce0c1ac74c03613a0720000007ce59018033658e00000000026038815ac8a7b200020457adc80003341a8c140a4cbe144b9800074a0008385a4bb4b4e5c6c420000be00000000acc296e8f2c720005f04b41f8b941d657e3b2000056ab67d4000d6cda088a0009fc4f40000004ac6c6db64b22f6c98000c2c954d5c3720680001fc252a18000cb000600000036c310c94dc640898cde00000000dc0008d600017ccd07020007489a60000005780ea000d0400000000000000000017295e6a2000ac4bdc000a2c6288780000f4000d662e40008ea0000000223e62c4e02cfa73486200058c5102aa9d4bfe00022800000000055a3fcc66076e3000075a00000072869614c00085c400e2e0008c01940000002a400000000000000055c606a760f200054ac6c1e8000000d000000000000002469e0000a3057c0000004b00000003a031e868000cfc0006da000000000000cf613c18eb3ed344d60007ba662cf04320008e06728de3f834a0003d86dc000000d407fa000000000af464a79c0000006020004940000000000007e8926000000000000000674e46000a200005c8af6dea9ce0005627084c600032489a40677e1de872000000680a66474a380000cc00000032800022adca3e824a6fe92a000000000b2a00000014ac3ac7a56650e76e29ea9409400000062a03a00012a7063020000000004be0000000002a04283b80009e2184dec3ee81e2b609ce3c13e01cd900985980008f40007e041e0005aa000840000980444912a1c64400000032c67aa16000000d3626c69e43e004000524122b16556c4848a000ad83ac3441049589d0c6a824bbc51c0002ee0008600007cca087964889a80d216c3d23da00000000084e000b06996dc20000d4704416000000c4000049cc38abea46c70030cbaa86c2e00000031400000000061a68ad0a536ae4a88000000000bda00000000000019ab5a00053a0000780000000006c2d80dc0000000000b18000000600000b400009888f81b800000000078a00010215015e3ceb582ae00000072a762936000a80a129f4928aac8367421120009dec1e00087
  | 15 => 0x4eec02aa0ac62ca000c9a000000000d12038000000e0e00000082a000016000000596646000000132ab83bad2ec6896cd64000620386000ddc04cc2650c44ed10da481a0004461eaad643063005a000c4e00000000062c000000aa25380008125ac0000002acc60000000b6a00027a0009e800000000011c37e2fe47a6488a845400000000000000027c0f01e6690096d76190196c24d50000d22000000e42ade000c548a0594000000bf00b26320000003040000000007a47780000000009ecc04d1802e3de65683c2b8a2240e000cbcc4a00000075cb340004e80002da0001c0000b3a000ac23c4000b20000d38b363f27bc052c3630087428455000082eb6455e80ac640d00000008967900000006c4000000cb600028800000015897a8829f852eb1e99eace5f4dd4ca81b40005b6d520f6c8e000000456db03a891a42a36619e6b6000230274b0c20e00002c140392000950de2000000d0e330000d309920004920009320000002767c69443aead2a0622e376d4a6c8d820ac756040afecd60008f68ee00007e0004ce186000000448000dde000000dda0000002de000a5e00051a0000007b60000004e4000a8a1706be7aec4636e2e805407a4a674456c0146a40ec68e06454c16a67e05e5a26eedb2b66224922126b52000b70d56000178dbc2185f62a69663be00000092e000a4cd8e4ecd325f2000134e1abe0266000aa6a28000a5800e
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa2c8650a21540014590ca1042a80030b5d9420855000686b9a8410aa000d29425c0215400145b04326c0a8002ca60864d815000694b9285b02a000f09424cb6054001c1ccaa12642802293215624cb4000616b2ae42a48000939801d5429000751f0ca126520002c3215424ca400070732a849948000e0d655093290001653042a2a1200030eddb745424000594c10e8a848000938875095090001c52c4a12a12000392589325424000784a1264a848000c3876dd15050001633063a2a0a0002ca608745414000598c08e8a828000e2b625095050001e1284992a0a0002c660f415414000594c1682a828000939801d542100010790eb2a8420002a360a63508400060e3aac6a108000c8f7650932100016190aa12642000383995424c84000706b2a849908000e85424ca61100014690aa12c220003a1509325844000516c10e8b2c600083c87595428c00791eeca12651800383995424ca3000706b2a849946003a8d83589420c00151b053226418002a3e19424c8300070732a849906000e0d65509320c001d0a84994c218003a150932584300051cc00eab264000b29801d542c8001c1eeab1a8590003831d56350b200452642ac89964000e0f8559132c8001c190ab2265900038358d42d432000706b2265a86400083c8759150c80012590ea12a1900038358d425432000706b2264a864000a2d821d165880010790eb2a851000383995424ca2000706b2a849944000b29821d150880012710ea12a110003c2509325422000546c18eca124000c2c761d54248001653003aa84900162b21d655092003d5240ac6a124000b29851c14248001743023828490002a3610764c9200452642ac89924000b49851c132480017830238264900024b21d425412001e643b264a824000c38761d15048001653043a2a09001a1e21d645412000594c20e4a824000b49831c950480016c302392a090002ca6124254120005a4c1c84a824000938875095048001a570ea12a090002caa1d42541200059443a84a824000d28875095048001e1285992a090002ca6123254120005a4c1c64a824000f0b424c95048001e1284992a09002392dd93254120007243b264a824000f0b744c95048001e10e8992a09000392d91325412000724b2264a824000b2984c8550480016930790aa0900028b60874596100041e43acaa142000e0e655093284001c1acaa1265080038a595424821000724b2a649042000c8e845c8634400191b08b90c688002a360863d091000546c10c6a1220048cc87589324400191ceca126488003231d9424c91000526c10c7a822000a4d8218d5044007950eca124088003235d1735881000546c14c6a102000a8d82991320400151f0ca126408002a3619424c81000647bb2849902000c8d765093204001c1ccaa12640800383595424c810
  | 1 => 0xaa2b94c9288162b60b7650a5100546c14c9994a200a8d82991329440151f0ca126528802a3619424ca5101d16432a4a12a200939801d542d040151b0531a85a0803071d56350b4100647bb2849968200b0c8550932d040751f0ca12652080383995424ca4100706b2a849948200939801d542504016190aa1264a0802c560c545454100592c10a8a8a8200b31801515150407918eca12649881f611c5424c93100546c14c89906200a8f86509320c401c1ccaa12641880383595424c83100744a12653006200e89424c9600c401473003aac99082293215644cb2100707c2ac89964200e0c8559132c840151b07bb285108030bdd87550a2100594c00eaa144200c8f73509608840151b083b2649082293215644c921005a2c28e29924200bc1801c53248407988ec992a290802ca60075508210051743acaa104200a2c87595420840145f00b2a841080383dd56350821007063aac6a104200e2b855096008401c510aa12c0108038a9d5425802100714baa84b004200b0d8394942d400125b053a4a3a8002c360e6250b500452643284996a000e0f8650932d4001c190ca1265a80024b60a749875000686ba26590ea000c2d7650821d4001a1ae6a1043a80034a509700875000617c2ae4322a000c2c855c8645400191d06b90c8a80032360d721915000516c10c9292a000a2d821905254001868c8b88a4a80030b1da525095000586c1ca4a12a000a8d82193325400151b0432264a8002c3610524c95000706320a4992a000b4581149325400151d0ca1264a8002a3219424c95000516c10c9a8aa00092d829d2515400145b04322a2a8003439cd721915000686b9ae4322a000d0e835c86454001a1b06b90c8a80034aa01721915000694c02e4322a000d25729c46454001a2ae6b88c8a8003495c971191500068cb9ae0322a000d29725c06454001a62e2b80c8a80024b6087458d5000516c10c9312a000a2d821906254001868c8b88c4a80020fa1a76509500060f418eca12a000c1d831d9425400185b043b284a80030da0476509500061ac08eca12a000c39801d9425400165301b9284a80030b1da625095000586c1cc4a12a000b298098942540012590eb1284a8002cae0162509500061c3b4e0a12a000a38865c1425400161b0432664a80028721942cc9500051643285192a000d29425c232540014590ca1264a8002c3608644c95000586c20c4992a000e0c64189325400168b0231264a8002c3612424c950005a4c0484992a000a1c8650932540014990ca1264a800383e19424c9500058743284992a000b0c865093254001c190ca1264a800283219424c9500078540284992a000f0980509325400145b04326c2a80024b60a749855000516c10c8b0aa000c2c641c961540010790cba642a8003435d132c8550006a4992e190aa000
  | 2 => 0xd711954200692b92e232a8400d1a735c06550801a32e6b80caa10034a5c970195420069938ae032a8400d31715c06550801a5504b80caa10034a60970195420051cc00cbb1a8400a398019563508014730032ec4a1002ca60065d8942006173b6cb2928400b29801965250801a1ecab9ca4a1003431957394942006163b6caa928400b258119552508016530032aa4a10028e60065d85420060e32ae7b0a8400a398019561508014730032cc0a10028e60065181420060e32ae63028400c34655c460508012b3003aa8599002c66007550b32004b4c00eaa146400b29801d5428c8012d3003aa8499003431d74350932006863aa86a126400b29801d5424c801a18ebb9a849900ea3a1b5350932004c743ca6a12640098d829d3654c811a90a4b80a89900263e1170d4932046a5a82e1a926408d0f505d0524c801a1ae92a0a499003519517114932046a22a2e22926408d47505c4524c811a96a0b80a49902352a157014932006a52a2e02926408d48545c0524c8012b3003aa8499002c66007550932006863aee4a12640894e87dd5424c801693003aa849902313a18755093204626c30eaa126408d0d841d5424c811a8d023aa8499023516047550932046a5400eaa12640094d801d5424c811a93003aa8499002526007550932046863aca8a12640398c87551424c80151d0c2a28499002e1a045450932005c2c08a8a126400b8a80151424c801713002a28499002e1a077650932005c2c0eeca126400b0e859d9424c80161b0b3b28499002c3e1576509320058642aeca126400b0d80dd5424c80161d0b3aa8499002a3a18755093200546c30eaa126400b86811d5424c80170b023aa8499002e2a007550932005c4c00eaa126400b0e871d5424c801a1d0e3aa849900383a18755093200706c30eaa126400d0f761d5424c801a1aec3aa8499003c1a04755093200782c08eaa126400f0a801d5424c80161b003aa8499003c2600755093200584c00eaa12640098e87d95424c80131b0fb2a8499002a3a1b7150932006863aee2a126400b0e859c5424c80161b0b38a8499002c3e1571509320058642ae2a126400d0c755c5424c80161d0b3828499002c36167050932006863ace0a126400b0f855c1424c8016190ab828499002a3a18705093200587428e0a126400b0d851c1424c801a18ea3828499002e1a047050932005c2c08e0a12640098f87508614c801a1ceaa10c299003435d5421853200742a12c230a6400d89429c0614c801b1284b80c299003345857018532006873aa853026400d0d7550a604c801b0a85b8ac099003615087158132004c7c3a843026400d0e75508604c801a1aeaa10c0990036150a7118132006c2a12e23026400c2f855ca64944018590ab94c92880323a0d729925100646c1ae5324a207c2f515ca649440f85
  | 3 => 0x42047700000000c63200f6840000000258000006800185470000008d0009f60cde01c0037d5f000002848f5b814501133a99501859624b531da665cf366552000000009d001560f10000000000000057553ca93c0313f800000054b8002c59d59d435ed691085412c17000004157a1491f648a22950c000c02dce9209915fcce00000000e20002c0013d00000000003f4ae2c800505a02ac002bcec098005240000174094bc25151000ad42d0400127230f634c652454e1d8984eda81a4640a1090106b43942594002401e0007900196398480000017400518d861800000f55b4553ec000e0006880044976000000018a000d426c0e00103028f20c8004e55335c4307cc1584330014b2d02a000920813100000001541700020ce83640010511000c329d3e5f84541d90054a00001c61d3a46d721cd9b2914d66000000190e564040a34b4ba335260580018000000000000000000000000000000000468002cc000007000000491230007c075783110d678000010f000005885a4d0e5000213840000c003ac9c454e3000002d966000953bd6a23800134002f957100003480000000000f153000001790003458c9356d2f4b0004a0974fcc9000003e400000000019a6a87400133418e72a008000f7408fc2fc856956b3157364cb83d18d6015a5f5a41f47b1387869c47000000ec0000000000000001315c37001582a89a33c666a57c5bca606c0d4c86a4758c5204f4a98168cdc2018e478560000000035000272f584671190003e0000009011000000bd0862c004ac00608d54415d2e518309704882e3748a000ac36c4a00086210511302d1100967d3000000160003e0001bd5e2c12914ccc1b02b4283a1b91708c5e16d59264005141212537358003400b1fc000000051c0000000000005c40000863580000006d380003698f19c00620d1189010008921c3d0009e030ed4d8ca3b80032d77000001c800088000008800000000fa000181f994000002ec8b0fc29068000012500046000004e000000003fd21510751c40000000571501e8000c0004586117c004d55539168000365b1200000080200802090060000c00002000040a8000181e020020280202800000120203205000008020b806000040280000812000020700401804040000000c01012000000100e02802038000000000802000020180e0400c018100100200820008000100c0280c01000030020180c030240200804020000000c000000000180c0300002806000100281600018020020180a0100605000010000000002802000000080c0000c0180200000000000102c0180c0180000c39645c0549480f85ac4bacc3a10030ee1170195420061c422e032a8400a398019743508014730032a86a1002ca60054949420462632ae7292840098d829cc655080161b05398caa1003455c
  | 4 => 0x13c1414a0011
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x180488140027a60d1b959e0000031929028a902413ac8d81801d2a879680178b9b1721801223800c80050a05ab8e00001c800ea2248f84132086021fac091d800000119518802000298012ab2a000f070b0000271625009f1a03800000269ea119a82580002280088c23001c1101000009a89a869480108082000430002b008100000802a0860c04042010e10002161c1010050664c845c065508014319121170195420054264a735c0655080150993a09701954200542640655ce52508014199019573d854200506640655cc60508014319019571181420054264075d0d424c801509901d543509320054264075dcd424c801509901d7725093200642e51801d5424c80190894600755093200541647761d5424c801a0586604755093200682a19801d5424c801a09866007550932006c0a05801d5424c801b0181600755093200642dd9801d5424c8019097660075509320054264075dc5424c801509901d5715093200542640759c1424c801509901d47050932006411d5811c1424c801c81425857018532004432617550a604c8014259121572992510050a640855ca649440180c8560d7299251005066407558d42d040130990215424cb41004c264085509325040160990215644cb210050364f761d5428840182b766007550a21005826407558d42084014299721542580210048a26175509600840142591215721915000603215835c86454001425921917114950006031d9839494254001a0464604524c9500064260d805c864540014259219171189500050364a831d9425400181583604765095000609609811d942540018198360076509500060a609801d94254001831816007650950006031d983989425400142896509708c9500068119181189325400120e96a19424c95000603a5c86509325400180d97219424c95000681a44865093254001a0591219424c95000682640865093254001a0886a01424c9500058225980509325400140c965d132c85500040b26176508215400180c865cd42085500050a259425c0215400130990215424ca400054225d424c95090001419901d56350840004c264085509321000120c98595424c8400048c6408550961100016049550932584400048326165509328c001609901d56350b20005826408559132c800180c8758d42543200050325d644c950c800120c98595424ca200054225d424c9508800140d931d875509200060a1d9801d542480018287660874541200054225d42cc95048001c08761d132541200451225d644c9504800120c98595424ca10
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x32800002422301643a1400083005203424a3003aa8499002901a1dd9801d5424c801480d00eac08e0a126400a016848560d72992510050134042b06b94c928802809a3dd9801d54288401402d090ac1ae4322a000c0165d91219424c9500060132ec810ca1264a800320191640865093254001300d012aa1264b088000a0268c766007550920
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x1
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0xd0a
  | 8 => 0xcce
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 66
  | 6 => 1654
  | 5 => 1830
  | 4 => 427
  | 3 => 90
  | 2 => 12
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
  | 7 => packedAt gbK7 (1870+((h/22+packedAt gbK7 (1716+(h % 22)*7) 7) % 80)*8) 8
  | 6 => packedAt gbK6 (67810+((h/551+packedAt gbK6 (61198+(h % 551)*12) 12) % 2641)*12) 12
  | 5 => packedAt gbK5 (95160+((h/610+packedAt gbK5 (87840+(h % 610)*12) 12) % 2657)*12) 12
  | 4 => packedAt gbK4 (26613+((h/142+packedAt gbK4 (25193+(h % 142)*10) 10) % 620)*10) 10
  | 3 => packedAt gbK3 (6510+((h/30+packedAt gbK3 (6300+(h % 30)*7) 7) % 119)*8) 8
  | 2 => packedAt gbK2 (992+((h/4+packedAt gbK2 (972+(h % 4)*5) 5) % 18)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe1c7c703c3e1f87ffc3f81fe0ff02069a4f4cf
  | 1 => 0x1f8f803fc7e1f8707c3fe0ff0f0c191db4b33
  | 2 => 0xfe00fffc7f801ff807fc000fff09061e638c3c
  | 3 => 0xffff00007fffe00007fffff0000e07e07c0fc0
  | 4 => 0x7ffffffff8000000000ff8007ff000
  | 5 => 0xffffffff8000000000000000000fffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x40414120800020098004808208402028801045
  | 1 => 0x888841082208821041280540a0c091094112
  | 2 => 0x2a0012185591155026a80428a6090202628c28
  | 3 => 0xad12008866d5444047325560220e0740740e80
  | 4 => 0x80000107b799e6472201840c42b48007fe000
  | 5 => 0xd1e4e4e2000000008000618108c4b5fd800000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfffffef8eeeaeee8fffffef8eeeaeee8fffffef8eeeaeee8fffffef8eeeaeee8fffffef8eeeaeee8fffffef8eeeaeee8fffffef8eeeaeee8fffffef8eeeaeee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_14262
namespace PEqualNP.Outside.L_meta_14262
open PEqualNP.Outside.L_meta_14262.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_2_0 : Interval gbAtlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 12 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 90 := (concat bgb_3_0 (concat bgb_3_32 bgb_3_64))
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
theorem bgb_4_416 : Interval gbAtlas 4 416 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 427 := (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416))))
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
theorem bgb_5_1824 : Interval gbAtlas 5 1824 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1830 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768)) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896))))) (concat (concat (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344)))) (concat (concat (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696)) (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824))))))
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
theorem bgb_6_1632 : Interval gbAtlas 6 1632 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1654 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408))) (concat (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504)) (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 66 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 32, 48),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 5 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 2 zero,inputs.getD 7 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 1 zero,inputs.getD 5 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffffffffffffffffffffeeeaeee8fffffef8fefafef8fffffef8eeeaeee8ffffffffffffffffffffffffeeeaeee8fffffef8fefafef8fffffef8eeeaeee8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) SB :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) SB :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) SB :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) SB :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) SB :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,4,68),(inputs.getD 7 zero,32,160)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,4,68),(inputs.getD 7 zero,32,160)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 8) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 8 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_14262.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.and,[8,7]⟩,⟨.and,[3,6]⟩,⟨.or,[0,2]⟩,⟨.or,[5,7]⟩,⟨.and,[11,12]⟩,⟨.or,[0,1]⟩,⟨.or,[4,6]⟩,⟨.and,[14,15]⟩,⟨.or,[9,10]⟩,⟨.or,[17,13]⟩,⟨.or,[18,16]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ correct
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨gs,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg))),len⟩
  · push Not at clean
    obtain ⟨a,ha,hop⟩ := clean
    have lo := binaryLower low gs o (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal) correct
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot,hop] at e
    exact ⟨mono,19,monoShape,by change 12 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_14262

open PEqualNP.Outside.L_meta_14262 in
theorem PEqualNP.Outside.L_meta_14262 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
