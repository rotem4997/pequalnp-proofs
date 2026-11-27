import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_11970.Model
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
  (n*(n+971)) % 2305843009213693951
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


end PEqualNP.Outside.L_meta_11970.Model

namespace PEqualNP.Outside.L_meta_11970
open PEqualNP.Outside.L_meta_11970.Model
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

def SB : Nat := 4

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

end PEqualNP.Outside.L_meta_11970

namespace PEqualNP.Outside.L_meta_11970
open PEqualNP.Outside.L_meta_11970.Model
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
  | 1 => 0xe1e3c3c387f8fe1f311ce1e1e3f87f878a4e73
  | 2 => 0xfe03fc03f87f1fe1c1e0fe01fc7f87f80c739c
  | 3 => 0x3fffc007fe001fe00fffe007ff8004f83e0
  | 4 => 0xfffc0000007fffffffff0000007ffffff003ff
  | 5 => 0xffffffffff800001ffffffffff8000007ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xa4c458952a0e44a9110468a4ab1a2a930a4631
  | 2 => 0xcc48899a2292c88b4120aa88d92aa3310c5294
  | 3 => 0x9991331333249ccdf202ccdc927332664e83e0
  | 4 => 0x1100222044401000a44a00100044444450014a
  | 5 => 0x20000000001100890110100000000212800
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xfffffffcfcfc0000fffffffcfcfc0000fffffffcfcfc0000fffffffcfcfc0000fffffffcfcfc0000fffffffcfcfc0000fffffffcfcfc0000fffffffcfcfc0000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_11970
namespace PEqualNP.Outside.L_meta_11970
open PEqualNP.Outside.L_meta_11970.Model
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
  | 0 => 0x1e0e3c7c71fc7e3f318e31c71fc7e0ff4133cf
  | 2 => 0x1ff03f807e3f8ff8c1f03e07e3f8ffe009ccfc
  | 3 => 0xe0003fff803ff03ffe003ff803ff00ff8e0f0f
  | 4 => 0xffffc000003fffc0ffffc00003ffff00f00ff0
  | 5 => 0xffffffffffc00000fffffffffc000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x82a44528c20720501182904159412a2a4111c5
  | 2 => 0x446489192049640140903212c8c8464609445c
  | 3 => 0x4149125024904ca0e20124b0829214948a0e0a
  | 4 => 0x8988026249220832b525802013249818d00ba0
  | 5 => 0x1000200000000104084809040000000024a000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xfffffffafaf0aa00fffffffafaf0aa00fffffffafaf0aa00fffffffafaf0aa00fffffffafaf0aa00fffffffafaf0aa00fffffffafaf0aa00fffffffafaf0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_11970
namespace PEqualNP.Outside.L_meta_11970
open PEqualNP.Outside.L_meta_11970.Model
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
  | 0 => 0x1e0e3c7c71fc7e3f318e31c71fc7e0ff4133cf
  | 1 => 0x1ff03f807e3f8ff8c1f03e07e3f8ffe009ccfc
  | 3 => 0xe0003fff803ff03ffe003ff803ff00ff8e0f0f
  | 4 => 0xffffc000003fffc0ffffc00003ffff00f00ff0
  | 5 => 0xffffffffffc00000fffffffffc000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x82a44528c20720501182904159412a2a4111c5
  | 1 => 0x446489192049640140903212c8c8464609445c
  | 3 => 0x4149125024904ca0e20124b0829214948a0e0a
  | 4 => 0x8988026249220832b525802013249818d00ba0
  | 5 => 0x1000200000000104084809040000000024a000
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xffffffeeeeccaa00ffffffeeeeccaa00ffffffeeeeccaa00ffffffeeeeccaa00ffffffeeeeccaa00ffffffeeeeccaa00ffffffeeeeccaa00ffffffeeeeccaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_11970
namespace PEqualNP.Outside.L_meta_11970
open PEqualNP.Outside.L_meta_11970.Model
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
  | 0 => 0xf0e3c78787f870e1631ce1e3c7f878784a4ecc
  | 1 => 0xff03f807f87f80ff83e0fe03f87f807f8c730f
  | 2 => 0x3fff8007fff01fc00fffc007fff800f83f0
  | 4 => 0xfffc0000007fffffffff0000007ffffff003ff
  | 5 => 0xffffffffff800001ffffffffff8000007ffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x5ac4752d2a0f254b630668a9575a2d2d4a46cc
  | 1 => 0x66489332229166898120aa91b12aa2330c5305
  | 2 => 0x44912223332244cda400ccd9223333220e8350
  | 4 => 0x88000444444400004a4a0000044444445000aa
  | 5 => 0x20000000008101090110200000000212800
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xfffffefefcfc0000fffffefefcfc0000fffffefefcfc0000fffffefefcfc0000fffffefefcfc0000fffffefefcfc0000fffffefefcfc0000fffffefefcfc0000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_11970
namespace PEqualNP.Outside.L_meta_11970
open PEqualNP.Outside.L_meta_11970.Model
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
  | 0 => 0x7c3e0f0783fffff8c30e383c3c3fffff8293ff
  | 1 => 0x803ff007fc3c3c1f03f03fc03fc7c1f0531ccc
  | 2 => 0x3ffff8003fc01ffc003fffc007fe0063e0f0
  | 3 => 0xffc00000003fffffffffc0000007fffffc00ff
  | 5 => 0xffffffffffc0001ffffffffffff800007fff00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x18426229150488884102191494b0ca53029155
  | 1 => 0x2a94a6b6514b91bb1350ab511b9369655314cc
  | 2 => 0x53194ca3599139ddd441339b9125ad4a63a0f0
  | 3 => 0x621188c4622221169a6582020206318c7400aa
  | 5 => 0x200000000002002088042020000000084a00
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xfffefffeaa00aa00fffefffeaa00aa00fffefffeaa00aa00fffefffeaa00aa00fffefffeaa00aa00fffefffeaa00aa00fffefffeaa00aa00fffefffeaa00aa00, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_11970
namespace PEqualNP.Outside.L_meta_11970
open PEqualNP.Outside.L_meta_11970.Model
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
  | 0 => 0xe03e0f83fffff878787f0781e07ffffe0eccff
  | 1 => 0xffc00fffc0fc1f807f8ff801fffc1f01330fcc
  | 2 => 0xfffff003ff001fff800ffffe007fe001c3f0f0
  | 3 => 0x3fffffffffff00000007ffffffc00ff
  | 4 => 0xfffffffc00001fffffffffffff800001ffff00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2984511452488828281b22a4a90ca54c06cc55
  | 1 => 0x428d66508e11b9821a856a08c73696151305cc
  | 2 => 0x851943590439da9a8206731c825ad4294350f0
  | 3 => 0x16318c6228a1175353204050146318b1f800aa
  | 4 => 0x1820080030c2046464488461180000c0acaa00
  | _ => 0
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xfefcaa00fefcaa00fefcaa00fefcaa00fefcaa00fefcaa00fefcaa00fefcaa00fefcaa00fefcaa00fefcaa00fefcaa00fefcaa00fefcaa00fefcaa00fefcaa00, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_11970
namespace PEqualNP.Outside.L_meta_11970
open PEqualNP.Outside.L_meta_11970.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xf800100800000000000001106a0000009080f19000000000000000000000000178000118013129d9b0184968e1b9a0798000d800000000000070008800000000000000000000000001f800015020403800e8c000015800d0b80000000059600001380148a0506141080000b1c8002800c8a800018800000001d000000001e19801f00000000001c001200000300001a9e801017098000004080c081004000404040404000c000c00200c01ff54007f95001fd54007f15001ff53007f94c01fd53007f14c01ff43007f90c01fd43007f10c01ff52007f94801fd52007f14801ff42007f90801fd42007f10801ff32007f8c801fd32007f0c801ff51007f94401fd51007f14401ff41007f90401fd41007f10401ff31007f8c401fd31007f0c401ff21007bc8401fe21007d88401fd21007b48401f521007948401fc21007fd4001fe50007f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x2c4000bf59620005f8cb10002ff64880017f3244000bf59220005f8c910002ff63880017f31c4000bf58e20005f8c710002fd62880017f30c4000bf58620007de4310003f62188001f690c4000fd48620007ca4310002fe6088001fd2844000fe54220007f48110003f94088001fd9844000fe0c220007de4110003fb20880017fb2a4000bf99520005faca90002fc65480017fb224000bf99120005fac890002fc64480017fb1a4000bf98d20005fac690002fc6348001f72924000fb54920007de8490003ec4248001f71924000fb4c920005fec290002fc6148001f790a4000fd88520007da4290003f52148001f290a4000fe94120007f2a090003fa4048001fca024000fecc120007f06090003fb2048001f71024000bfd9420005fcca10002fd65080017e3284000bfd9020005fcc810002fd64080017e3204000bfd8c20005fcc610002fd63080017e3184000bf98820005fcc210003f661080017b3084000bf58420007eac210002f56108001f79084000fd88420007da4210003f52108001f29084000bf98020007de4010003fa2008001f69004000fe48020005fecb88002fe65c40017eb2e2000bf19710005fec988002fe64c40017eb262000bf19310005fec788002fe63c4001ef31e2000b798f10005fac788003dd63c40016eb1e2000bf18f10005fec588002fe62c4001f73162000bb98b10005fac588003ed62c400176b162000bf18b10007eca388003f551c4001fba0e2000fd10710007ec6388003f531c4001f790e2000fd88710007da4388003f521c4001f290e2000bfd9610005fccb08002fd65840017e32c2000bfd9210005fcc908002fd64840017e3242000bfd8e10005fcc708002fd63840017e31c2000bfd8a10005fcc508002fd62840017e3142000bf58610007de4308003f62184001f690c2000fd48610007ca4308002fe6084001fd2842000fe54210007f48108003f94084001fd9842000fe0c210007ee2108003fb10840017fb2a2000bf99510005faca88002fc65440017fb222000bf99110005fac888002fc64440017fb1a2000bf98d10005fac688002fc63440017fb122000bf98910005fac488002fc6244001fb28a2000fd54510007ee8288003f44144001fb18a2000fd4c510007de4288003f62144001f690a2000fd48510007ca4288003fa5044001fca822000fe90110007f28088003fb3044001fc1822000fec4110007ec2088002ff65040017f3282000bf59410005f8ca08002ff64040017f3202000bf59010005f8c808002ff63040017f3182000bf58c10005f8c608002ff62040017f3102000fb98810005dcc408002fd6204001f6b102000bb58810005f8c408002fe6104001f79082000fd88410007da4208003f52104001f29082000bf98010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x2f661900017eb0c8000fd58640005eac320003ef2190001fb10c8000fb48640007ea4320003e521900017f3048000fe94240007f2a120003bf4090001fda048000bfd9540005fccaa0002fd65500017e32a8000ef951400077aa8a0002ff63500017e31a8000efd0d400077a86a0002ff62500017e3128000bfd8540005f8c2a0003ef2150001fb10a8000fb48540007ea42a0003e52150001fd2828000fe54140007f680a0003be40500017fb288000bf99440005faca20002fc65100017f3208000bf98c40005fac620002fe62100017eb108000bf98440005fac220003ef2110001fb1088000fb48440007ea4220003e521100017f3008000efd0040007f48020003bd4010001fca008000bfd9730005fccb98002fd65cc0017e32e6000bfd9330005fcc998002fd64cc0017e3266000f794f30007baa798002fe62cc0017eb166000bf98730005fac398003ef21cc001fb10e6000fb48730007ea4398003e521cc001fda866000fe14330007f48198003f940cc0017fb2c6000bf99630005facb18002fc658c0017fb246000bf99230005fac918002fc648c0017eb1c6000f7d4e30007b8a718003de438c001eea1c6000bf98a30005fac518003df328c001ee9946000bf98630005fac318003df318c001ee98c6000fbc8630007ec4318003ed218c001fa90c6000f948630005fcc118003fa508c001fca846000f7cc230007f66118002ff654c0017f32a6000bf59530005f8ca98002ff644c0017f3226000bf59130005f8c898003de534c001eea9a6000bfd8930005f8c498002ff614c0017e30a6000fbc8530007ec4298003ed214c001fa90a6000f948530007f4a098003f9504c001fd9826000f78c130005feca18002fe650c001bf32860009f99430005faca180037d650c0013eb286000bf19430005fec818002fe640c001df3206000af99030005fac818003bd640c0015eb206000bf19030005fcc618003df530c001ee2986000f790c30007ba8618002fe620c001f73106000bb98830005fac418003ed620c00176b106000f7cc830007ba6418002fe610c001fb3086000bd98430005fac218003f5610c0017ab086000f7cc430007ba6218003ef210c001fb1086000fb48430007ea4218003e5210c0017f3006000fed4030007f0a018003fa400c001fca006000f7cc030007f46018003dd300c001fc9806000f64c030005fecb90002fe65c80017eb2e4000bf19720005fec990002fe64c80017eb264000bf19320005fec790002fe63c8001ef31e4000b798f20005fac790003dd63c80016eb1e4000bf18f20007dca590003ed52c8001f7a164000fb10b20007dc6590003ed32c80017f30e4000fd98720005ecc390002fd61c8001fab0e4000bd58720007de4390003f621c8001f690e4000fd48720007ca4390002ff65880017f3
  | 2 => 0x21007eaa890803f45448401fbb1a4200fd98d21007eac690803f46348401fba9a4200fd94d21007eaa690803f45348401fba1a4200fd90d21007ea8690803f44348401fbb124200f9d8921007eea490803e75248401fb2924200f994921007eaa490803e55248401fa2924200f914921007ee8490803e74248401fb2124200f990921007ea8490803e54248401fa2124200f910921007ee6490803e73248401fb1924200f98c921007ea6490803e53248401fa1924200f90c921007eec090803f66048401fab024200fd18121007ceca90803e66548401f2b2a4200f919521007cec890803e66448401f2b224200f919121007cea890803e65448401f2aa24200f915121007cec690803e66348401f2b1a4200f918d21007cea690803e65348401f2a9a4200f914d21007ce8690803e64348401f2a1a4200f910d21007cec090803e66048401f2b024200f918121005feca10802fe65084017eb284200bf19421005fec810802fe64084017eb204200bf19021005fec610802fe63084017eb184200bf18c21005fcc410802ee62084017f3084200bd98421007de4210803f62108401f69084200fd48421007ca4210802fe60084017eb004200bf99350005fac9a8002fe63d40017eb1ea000dfd4f50006faa7a8002fe62d40017eb16a000bf98750005fac3a8003ef21d4001fb10ea000fb48750007ea43a8003e521d40017eb2ca000bf99250005fac928002fe63940017eb1ca000bf98a50005fac528002fe61940017eb0ca000fbc8650007ec4328003ed2194001fa90ca000f948650005fcc1280037f5094001fda84a000bfd9150005f8c8a8002ff6354001efb1aa000b7d8d50005f8c6a8003dc63540016e31aa000dfd4d50006faa6a8002ff62540017e312a000bfd8550005f8c2a8003ef2154001fb10aa000fb48550007ea42a8003e52154001fda82a000df94150005fcca28002fe6414001df320a000af99050005fac828003bd64140015eb20a000bf98c50007bcc628002de63140017eb18a000f758c50005bac628002fe6214001f7310a000bb98850005fac428003ed621400176b10a000bf98450007ecc228002f661140017eb08a000fd58450005eac228003ef2114001fb108a000fb48450007ea4228003e521140017f300a000dfd4050007f4a0280037d5014001fca80a000bfd9740005fccba0002fd65d00017e32e8000ef953400077aa9a0002fe63d0001ef31e8000b798f40005fac7a0003dd63d00016eb1e8000efd0f400077a87a0002fe62d00017eb168000bf98740005fac3a0003ef21d0001fb10e8000fb48740007ea43a0003e521d00017fb2c8000bf99640005facb20002fc65900017eb248000bf98e40005fac720002fe6290001f73148000bb98a40005fac520003ed629000176b148000bf98640007ecc32000
  | 3 => 0x71964200fb4cb21007d86590802fe60c84017eb064200fbd9721007dccb90803ed65c8401f632e4200fbd9321007dcc990803ed64c8401f63264200fbd5321007dca990803ed54c8401f62a64200fbd8f21007dcc790803ed63c8401f631e4200fbd4f21007dca790803ed53c8401f629e4200fbd0f21007dc8790803ed43c8401f621e4200fbd4721007dca390803ed51c8401f628e4200fbd0721007dc8390803ed41c8401f620e4200fbcc721007dc6390803ed31c8401f618e4200fbd8321007dcc190803ed60c8401f63064200bfd9621005fccb10802fd65884017e32c4200bfd9221005fcc910802fd64884017e3244200bfd8e21005fcc710802fd63884017e31c4200bf58a21005dac510802fe6188401fba8c4200fd94621007eaa310803f45188401fba0c4200fd90621007ea8310803f44188401fb98c4200fd8c621007ea6310803f43188401f790c4200fdc8621005fcc110802fd6088401fbb2c4200fd99621007eacb10803f46588401fbb244200fd99221007eac910803f46488401fbaa44200fd95221007eaa910803f45488401fbb1c4200fd98e21007eac710803f46388401fba9c4200fd94e21007eaa710803f45388401fba1c4200fd90e21007ea8710803f443884017ab144200b958a21007eea510803f65288401faa944200fd14a21007ee8510803f64288401faa144200fd10a21007ee6510803f63288401fa9944200fd0ca21007eec110803f66088401fab044200fd18221005feca90802fe65484017eb2a4200bf19521005fec890802fe64484017eb224200bf19121005fec690802fe63484017eb1a4200bf18d21007dea490803ee5248401f6a924200fb14921007de8490803ee4248401f6a124200fb10921007de6490803ee3248401f69924200fb0c921007eea290803f65148401faa8a4200fd14521007ee8290803f64148401faa0a4200fd10521007ee6290803f63148401fa98a4200fd0c521007ee4290803ee21484017fb024200bf18121007deca90803ee6548401f6b2a4200fb19521007dec890803ee6448401f6b224200fb19121007dea890803ee5448401f6aa24200fb15121007dec690803ee6348401f6b1a4200fb18d21007dea690803ee5348401f6a9a4200fb14d21007de8690803ee4348401f6a1a4200fb10d21007dec290803e76148401f7a8a4200f9d4521007dca290803e65148401f6a8a4200f954521007d8a290803e45148401f7a0a4200f9d0521007dc8290803e64148401f6a0a4200f950521007d88290803e44148401f798a4200f9cc521007dc6290803e63148401f698a4200f94c521007d86290803e43148401f7b024200fb98121007dac090803ec6048401fbb2a4200fd99521007eaca90803f46548401fbb224200fd99121007eac890803f46448401fbaa24200fd951
  | 4 => 0x803be64144015f320a200bf590510077ac828802bd64144017f318a200f798c51005bcc628802fd6314401eeb18a200b758c51005fcc428803ee621440177310a200bf58851007dac428802ed62144017f308a200dfd4451007eca2288037d5114401faa88a200bf98051007f4c028802fa60144017eb00a200fe58051005f2c028802ff65d04017f32e8200bf59741005f8cba0803be54d0401deaa68200bf98f41005fac7a0802fe62d04017eb168200fdd4741007e8a3a0802fe60d04017eb068200bfd9641005fccb20802fd65904017e32c8200bf59241005fcc720802fd63904017f3148200fb98a41005dcc520802fd6290401f6b148200bb58a41005fcc320803f65190401faa8c8200efd0641007ee8320802fe60904017eb048200bfd9541005fccaa0802fd65504017e32a8200ef951410077aa8a0802ff63504017e31a8200bfd8941005f8c4a0803f65150401faa8a8200fdd05410077c82a0802ff60504017e3028200bfd9441005fcca208037e65104013f3288200bf59441006faca208027d65104017e3288200bf99041005fcc620803de63104016f3188200bf58c41007bac620802dd63104017f3108200fb98841005dcc420802fd6210401f6b108200bb58841005fcc220803f75110401fa2888200efd0441007ec8220803bd4110401faa088200bf98041007f4c020802fa60104017eb008200fe58041005f2c020802ff65cc4017f32e6200bf59731005f8cb98802ff64cc4017f3266200bf59331005f8c998803de53cc401eea9e6200f790f31007ba8798802fe62cc4017eb166200bf98331005fac198802ff658c4017f32c6200bf59631005f8cb18802ff648c4017f3246200bf59231005f8c918802fd638c4017f3146200fb98a31005dcc518802fd628c401f6b146200bb58a31005fcc318803f6518c401faa8c6200fdd0631007e88318803df318c401fb98c6200bf98231007f4c118802fa608c4017eb046200fe58231005f2c118802ff654c4017f32a6200bf59531005f8ca98802ff644c4017f3226200bf59131005f8c898803de534c401eea9a6200f790d31007ba8698802ff624c4017e3126200fd94531007eaa298803f7414c401fa20a6200fdcc531007bc6298802ff604c4017e3026200bfd9431005fcca18802fd650c4017e3286200bfd9031005fcc818802fd640c4017e3206200bf98c31005fcc418803ee620c401773106200bf58831007dac418802ed620c4017f3086200f7cc431007ec6218803dd310c401fa9886200bf98031005fac018802ff65c84017f32e4200bf59721005f8cb90802ff64c84017f3264200bf59321005f8c990802ff63c84017f31e4200bf58f21005f8c790803ef52c8401f72964200fb54b21007d8a590803ef42c8401f72164200fb50b21007d88590803ef32c8401f
  | 5 => 0x8452005fac229003f561148017ab08a400bf98052007f4c029002fa60148017eb00a400fe58052005f2c029002ff65d08017f32e8400bf59742005f8cba1003be54d0801deaa68400bf98f42005fac7a1003ef52d0801f62968400bf98742005fac3a1002fe60d08017eb068400bfd9642005fccb21002fd65908017e32c8400bf59242005fcc721002fd63908017f3148400fb94a42007daa521003bf4290801f7a148400bf98642007ecc321002f661908017eb0c8400fd58642005eac321002fe60908017eb048400bfd9542005fccaa1002fd65508017e32a8400ef951420077aa8a1002ff63508017e31a8400fb94942007daa4a1003ef4250801df2128400bfd8542005f8c2a1002ff60508017e3028400bfd9442005fcca210037e65108013f3288400bf59442006faca210027d65108017e3288400bf99042005fcc621003de63108016f3188400bf58c42007bac621002dd63108017f3108400fbd4842007d8a421003bf4210801f72108400ef50842007da8421002fe6110801fb3088400bd98442005fac221003f561108017ab088400bf98042007f4c021002fa60108017eb008400fe58042005f2c021002ff65cc8017f32e6400bf59732005f8cb99002ff64cc8017f3266400bf59332005f8c999003de53cc801eea9e6400f790f32007ba8799002fe61cc8017eb0e6400bf98332005fac199002ff658c8017f32c6400bf59632005f8cb19002ff648c8017f3246400bf59232005f8c919002fd638c8017f3146400fb94a32007daa519003ef428c801f62146400f7cca32007de6519002fe618c801fb30c6400bd98632005fac319003f5618c8017ab0c6400bf98232007f4c119002fa608c8017eb046400fe58232005f2c119002ff654c8017f32a6400bf59532005f8ca99002ff644c8017f3226400bf59132005f8c899003de534c801eea9a6400f790d32007ba8699003ee524c801f6a926400fbd0932007d88499003ef324c801ef1926400bfd8532005f8c299002ff604c8017e3026400bfd9432005fcca19002fd650c8017e3286400bfd9032005fcc819002fd640c8017e3206400bf98c32005fcc419003df320c801f71906400f74c832007da6419002fe610c801fb3086400bd98432005fac219003f5610c8017ab086400bf98032005fac019002fe64d44017eb26a200dfd5351006faa9a8802fe63d44017eb1ea200bf98b51005fac5a8802fe60d44017eb06a200bf59651005fcc928802fd64944017f31ca200bf58e51005fcc528803ee629440177314a200bf58a51007dac528802ed62944017f30ca200dfd4651007eea328802fe60944017eb04a200bfd9151005f8c8a88037f5454401beaa2a200bfd8d51005f8c6a8802ff62544017e312a200fdd4551006fca2a8802ff60544017e302a200bf99451005fcc828
  | 6 => 0x1df2a0a800df550540077aa82a002fe6315001ef318a800b798c54005fac62a003dd63150016eb18a800bf98854007dcc42a002ee62150017eb10a800fb58854005dac42a002fe6115001fb308a800bd98454005fac22a003f561150017ab08a800bf98054007f4c02a002fa60150017eb00a800fe58054005f2c02a002fe64d4c017eb26a600bf98b53005fac5a9802fe61d4c017eb0ea600bf98353005fac1a9802fd6594c017f324a600bf59253005fcc7298037f5394c01efa9ca600bf98a53005fac529802fe6194c017eb0ca600bf98253005fac129802ff6454c017e322a600f7d4d53006fca6a9802ff6254c017e312a600bfd8553005f8c2a9802ff6054c01fdb02a600bed8153005f8c0a9803f86054c017c302a600bf99453005fcc829803be6414c015f320a600bf590530077ac829802bd6414c017f318a600dfd4c53007bca6298037d5314c01eea98a600bf98853007dcc429802ee6214c017eb10a600fb58853005dac429802fe6114c01fb308a600bd98453005fac229803f56114c017ab08a600bf98053007f4c029802fa6014c017eb00a600fe58053005f2c029802ff65d0c017f32e8600bf59743005f8cba1803be54d0c01deaa68600bf98b43005fac5a1802fe61d0c017eb0e8600bf98343007f4c1a1802fa60d0c017eb068600fe58343005f2c1a1802ff6590c017f32c8600bf59643005f8cb21802fd6490c017f31c8600f794e43007baa721803bf4390c01efa1c8600bf98a43007dcc521802ee6290c017eb148600fb58a43005dac521802fe6190c01fb30c8600bd98643005fac321803f56190c017ab0c8600bf98243005fac121802ff6550c017f32a8600bf59543005f8caa1803be5450c01deaa28600f794d43007baa6a1803df4350c01df21a8600bfd8943005f8c4a1802ff6150c017e30a8600bfd8143005f8c0a1802ff6510c017f3288600bf59443005f8ca21802fe6410c017f3188600efd0c43007bc8621803bd4310c01eea188600bf98843005fac421802fe6110c017eb088600bf98043005fac021802fe64d48017eb26a400dfd5352006faa9a9002fe63d48017eb1ea400bf98752005fac3a9002fe60d48017eb06a400bf59652005fcc929002fd64948017f31ca400bf58e52005fcc5290037f5294801f7a94a400bf98652007ecc329002f661948017eb0ca400fd58652005eac329002fe60948017eb04a400bfd9152005f8c8a90037f5454801beaa2a400bfd8d52005f8c6a9003ef5254801bf292a400bfd8552005f8c2a9002ff60548017e302a400bf99452005fcc829003be64148015f320a400bf590520077ac829002bd64148017f318a400f798c52005bcc629002fd6314801eeb18a400b758c52005fcc4290037f5214801f7290a400df54852007daa429002fe6114801fb308a400bd9
  | 7 => 0xc289cbe400000000000000012a00016c9c055e6983da0008d40003b200000000000000000600300000000400000200000100000300100100000000400000000000100200000000400000000200000000100300100300000100000000000400000000000100000400000000000000000000300000000100000100300000000100100000000100800000000300400000000500000200000000000200300000000300400000100100400200000200000100100000000800000000100200200000000000000200400400100000000000300500000000000000000300000000000100100000300000000200000000000100000000000000000000000100200700100100400000000100000200000600400200200000000400100100000000100000000100100000000000100000000000100100000200d004001004001000000000003000001001001001001000003008000001000004000000004000002003000005000000000000006002001000002001001000005000000001000001001002002000000005000000000000002000008000005000000002000003000000000000005000001002001000000002002001001002001007000000004001001000006000000000001000005000000000000001001000000001000000008001000007000002000000000005000000000001000000001005000000000002000001000004001000001000002000003000000002000000008002006000001000001001000000003000005001000001000000000001000000007001004001003000005000000000001000004001001000001004000000000000003000000000001001000000004002003005000001000001000000002000004000000001003000000004003000000002001001000000001006002001000001007002000002000003000001000001000000000002003000001000006000001000002001000006000006000000000000000000001000003001001004002002000001000002000001000000001001000005000000000000001000004000002003000002003000000003000001000000009000000000000001000006000000000001001001003000000001000000000004000002000001002001001002001002001003003000000000004003005fcc7aa002fd63d50017f316a800bf58b54005fcc3aa002fd61d50017f306a800bf58354005facb2a002fe6495001bfaa4a800efd52540067ea92a002fe63950017eb1ca800bf98a54005fac52a002fe61950017eb0ca800bf98254005fac12a003bf5455001bf2a2a800bfd8d54005f8c6aa002ff6255001f7b12a800bbd8954005f8c4aa003ec625500176312a800bfd8554007eec2aa002f761550017e30aa800fd18554005e8c2aa002ff60550017e302a800bf99454005fcc82a0037f541500
  | 8 => 0xa4720000003680002d6b1e000000000000148000bc6abc00015636600028c0000005ec00000000033227a764154000ad6bb4000000b5c000000bc8000a20000000000000666000000000000b860000003e2246bfe0000000007e6000000abe1b669000000000000000041e27e9227d60009280003a445c75800000000000000000000000000000000038c22200089e592000b0e8ca5ac6f400025000000000000000000000000052618454093a0000002e20000000000000000000000000000000000000006520000001f4000000000000000000000000000000000b0c0000000009820000000008e2000000000000000af61f86f266c9c2000a7a0000000000000000008e00f60aa4922b6000000000c2c0000000000003e69f2c02a100000006a00007ea8d821429a00000000000095200000000023e000500172000226c0e2442bc00000000000000000014a28600069a30800048ca0287000000000049e24c000c1c66e00000010400000000000099600000073800000000000000000092600000000000056000000000000000000038a9de000b9c00000000000000000000000025e77000000082a000000000000000c107200000000000000008360001604bc70867cc300000000000f40000000000dc7f200000000000079c0002188240000000000000000002160005e000033ac2e2329462dc000000000000000000000000502000000000000000000bd6000000000000282182000664000b3800085c0000006368900004503f42c4a70aac0000007f0b1c56c000562000000000000000000806c260000000007ee0001b45c20008b200000000000000000000000032c0000140000000000000000000000865949ba0000000006dc00000000000000077897a0000005280f211a2e83babae91a00000000000077a0000000000000000000000005703be28e3282e06c43feaec000b680009789920000002de23619e0000000c871e0000000000000008162b000085400000001a7a4000000000712bde35e000ab0000748ad856ea8a00014e00000078a0003c80000000005c8258122000c2a000000000000000c4200000000062a9ac00000020a5b271a0000000000002b2000000000000bda0000000004523340006fac28a98a24000b8a000000000000000000000000000000000000a4c00000055c000572b3c8743d6ba0a760000920000000001bc000a1e0000000005ca0000007de0000003160da000000000408000000000000000c6e000000000412000000942b500007be0000000000006ae00084c2c8000000000000000000c0a12698013a0000006260000006320d80000000000000000000008de0000000000000006680008080000000000009542d4c648c03380000006eebcc000810ad44020000000006bcc4c00006c33600093c0
  | 9 => 0x4c4000c3422400000000000000000000031e9be0000002526f00000000000000000000000000008120000009cc0000000000008a4000000000000000000b745f83ac0003600004cc61a0007cc000ab23200000002a6150000000aa20000000000000000000008c6000386000000000000000898490000000ac65540000004ca0b444a0000000009d200000017c44c0000000003ca000000000b646b0000000000000000792b90a64c16ade96400096200000000000059c00000000093437e000000062b80550000106530a54000c608a0a14b9200000000087a0000000007567d2000000000340000000000000000af83b043e1b80560005a42ce0180ba3de9e40000000009b00000009c86fc0005383c00000000006b2468000bdc0009ea0007fa000000a908400006800000005560000006300005a2000000000a0c5bc076000000536000000000c180008780000000000000000000000000000000a20000000000001808206a80000003b623414c6e81dc31492e00089a190a180b6206bd0552ba842600000000063a5040000007daa820000002a05baac8000000a1a6d20002c030ab4276876c6d02ba0009e81620006e000000083e0002b80000000001a4a7200000001c07e0000000000009580000002ec8460000000000003d44744d046082200084a3f00008ae00000000000000000000000000000000000000000007c0000000003920007e8000bee00036a000000000000000000000000000158000000000000000000000000000000438c52a428e65ea07020879a5fc0000000005e20000000000000002960002a4000000000000506000000c6c0000000000002a200000073231c0007a000000000005a6c24b4000000000000000b080bc84200000072436e012bca0000000009f60000000008ec0005a8000000000000bc4000b700000000d40008ce53c0002e600089200000024ebeabf81f687200000040011c000058000000b3646a000000000000000000000be272a70c27800000078000000000000003c43c2d00000008f0a7800000000000095a00000000000043a0000000000000000000000260006ca000b9800035000042400000000000000000000000000000000000058c0000000000001e074c00000000020c372000000520000000a68728000000000146364b1ac140000008681400000001520d0ad07760009fc000498bfc000a4a796bd8c6a0007f6ba61200006ec852000a94000a480008da7440007f400029e000000000000000000000000000000000ab600000000072e0000001742484708a295e00000095c0000002f20008320000000000000008940000003f800023a000a749e60000003260000000009a639c7a80004ba0004d487684800089621a0009320000006d60004220000000000000006180006b
  | 10 => 0x6c000000071000000000000000000081c0000000000001946a60000000000004f80a600096828873a74a6543702920002ee0000000000003547000000000006040007c83ea0009380007b611055800045e0003442002da458000000000a5694a7ae00000084ea9200000013e456000118000b280ce1aaae85de0e40fc54c8a6c56acc9ae0000003e041c6020004fe8aa0000000000000004443c20000000000003520000007e000000019c000000970484000b480007c00000003ee000000000a6e1b27ac9f40000001fe000000b3e0000cc06e000a0e5dc000000000afe0000000000000000000000009a04fa0000009ec00000032e00000000055a000000b840362f600000000000092c00000000000048a21e0000005be0000ae00061cae4000000030a848d2694a3600088200054e4a40000000000000823fc000000000000000a3800088a5b800000000090c0000000000000000000000000000000000000000000006ea96a0000007e425400009e000000a220007524860000000000008e8bd4000000000000a12830670afc0003744b86cc00000026c00000000010e068bbe0000000000000001ea0000000000000009fe884a3c1120001a00007bc00002007265a0009d0b88c3e0009aa00000018865818600000061000000000000000062e000000000548b221960000008d60000002287fc0007024160004dc7ce000000000000b4600026000000000088e000000bb6000000000000000aa80000009300009d600000000000000049638000082600000000000000000070e00046e0000005901de378b9ab620006960000003c49902940286c8000000000524508c1e000000000000000000000116000000000000686000000000000000888c380001140000003420000000006e680c29c0003b47c600000043018a92400019a16eac40000000005f400029800000000022c00080a0001980000000000000000000000006400000000000000000005740000008ee6481a80000007c2722b180000005f2004000a347360000f8000000000000266000ba4000384000000c060000000001c61d885000086200000012eb7a0000004f057c5e48ac000000c32000000bd20004b250a0000fa000bf440a000794b40b06bb83a8000000000660a06000000000000ace000000c3cc440000000000000000000000000000000000000000fe9f8b66c3a00000000000098800000000000076ac22a0a000000000000000ab85760000003182f000000000000065e5cc0006b6000000000adc9b400000000046c00000000000000000000047e000000000000000000b60000000000000000000c48000000000bba000000c4a00057e5d80000000001b058a78e96e18c0008f63a65b64f2132bbc000c367b051eac000037aa60960a3221200000000000093e
  | 11 => 0x46feb4a00000068c9fa0000003fa0004f60000420000940009060008ea000000000090000000b4400004e0004d200021c00000000086600080200050c0009c60006f60004a8c0c000aa0000000000000798b168140001ce5f6ae2a4000000000000008064e74685a34c2c200097e000000420000000010000b7c0000000000000008d057a0007ca0e66a40000008f21d42200005ce000c04568432000c5c00000030c4e4900000b2c00000000000000000002298c9360002c6000000000000000000000684000afa276a4e0000000004bebf20000000004c60000441680525aa4640000246060005e6c660e81ecb720a4b5a96605020e2e453ea2c58050e87e63c76639e76e91015e0001d23cc514a5a00000000000068800035a0003aa646af00000000000000000000000000000000000000000000000006aa0000000000000000006000000009a80000000b856a3a2000000000be8b6a3100005d2000904000c085c6940c2432200060e1e430e4e6b30b7e0be00000026264a22a00070a0002aa000912596b26462bf67a2bce59e00000027c00000000052ab0a37c53200000071615cb760000006ac00000075e000bc000a000000000000000000a5e0002d83d013639a00000000000000000000088c0003ce00000000000000000075400000000000000076200020200000000062c000000a6c0004ce0000000000000007aa000406000b120002700e200000000096c00000000091604600000000000032400092a9d813400000073c000000000858b6e0163a033c35cb820000000008860004c07607d00000000000000000000009dc3f24347887e2b2a42e00000075c45a6a20001a200e6d4a8600067a00000000000000000000000000000000c8809029ca00061600000000000000000005e000302aca00000000000000099e00000000000082c7181d00004ec1ac5a6730000bb0000000a661ee27498e00000053a26aa5800000000003a0000d6634000000000000272000000000000000000786000614192000aae000000000290040000000b34000000598000000000000000b2000041800039452c0ca6621240002fc00000000000000000000000078c000be000078200000000000086a000000b003bc4b0a7c0009b8a04000ada65c0000000000008e4000908000000000ad20000000000000006b81e800012c99c0000005d6aba41a0000000640000001ae00000000000074e8f44eebac0000000000000000000006de000000b2e078a62210a2e0004040a8b020000000003000000000000000004540000007fe1dabec0000020000000e0a9630400000004a398b24000b9600049c4fc0000000000000009760000003963dc4147d877e0000001086560008345880009bc000000000000ae6000c5481a0002cc5e800000051c8bc6b418e0
  | 12 => 0x4a2000000a8090a0000005c400000000000000024a0008f89720000007a61cca0800000000000000000000000091c0000000000000000000ec99400000000000000000000000000068aaaa1700000000001444c8000000000a500009b200000000000000007471c000000b940000000000000000000001d6608864000000000000af20880000000000000006760001280006f84e80000000000d22a8000096a5c622000aa41ba54400000080e64c0000000005460007b80009ee1e6c584c2b8e4d817e0000008b64da00000083c0000000000008c200000000000000042c000000000c0000000022e44298aa3a0001c45103302f80000000000002ac0000000008b800000010a5a00004d61a60000000009b600000000000000053404c000aea00073e000000000000000000000000a8e000000142000c466744400000000000000000000000000000005d400000000009a08a7268b4c5a0004ea6780008dc00085e00000009800000000000094e000af400059a0000000006be0000000006280000000000000000003f652e00000000000000034800047ca26914bf09ce00017a00082e5b4740a2800072c00016a0000000000000000060004e05121ca5ae0000000009e20000000000000000000000000000005420000000003560007b40000ea0000000000000002568fa8040000000000000009d400031a0000000003c6000000692612000000000000948176000000000000000000000000000000000000c1a032b3295081e0008a80000008001be000c4e0000000000483460000000000000009a2264c1200036c2049da97c000000682000000000000000000000164c6210c03400015a00000000007a5d000042a000b4e0000000000000004e200033e0000000a07c4b1067200091e5fa08c00000000003e32a000000a884480000008fe000000b3a67e7900000009440000006440003060000003ae0009c44ac3d8000774000a7e00011e000a2a000b8c0000000000000004760000000001fc3b8a9c1000541c298600000000000000023061e1c01020007f8000baa13800026e97468e36262403800063800075a2ae0002800000000000000003e8000b9e0001e2000000000446000000000b580007065ee000000376000000c200000000009204667140009980000004f4000000428000000c6866a00000060a000860084b52312650b56000ae0b5400024243600000049a0000005840000000000000000006d8000000000a6a5182fa00000047a0b00000000000006422d225a000828000a440000004780000000000000000009180000000000000000000008cc000000000b780002f40000c07428fc3d238257800034eb4c000c408be0000000000000000008ba8443ecc5000001e000aee0000000000000009f099a5da00000044e00098
  | 13 => 0x34a5b05c000000028a0000000660000f00000000000000000000000000de0008b073400000000000023800000048e0004ae0000007b2000000000000b049e0480000000a3e0000000006c60000008182eabb200000000000000000008e0005f00006e2000a52000000268000000000000000a9a956b5e8567ec0b206039013c000000000000000b6c79e0000006da7ba0000004a60000c60007d41fa24048890ea30be6772b1486e0000080c440c0000006ce2ca178000000000000a461668c8ab438825c000000000000000000c5e94c4aa0000007dc000a004b6000000000000000586000000000a9e00000000000023c564000784a1600051a000bfa48200060c2b40000000001f009c0000000000000000000001c85fe83a02c00000000000086c0000008c40ee00063e69e00005c00000000087c0000000000000000001f275000028402aaa654a00038e0004940000000000001309a4ac2ba20003e40004104de000358000000a1c00000000006a00000000000040e000000000000a8c69c00002e2be6e458262077cbc258e2fe7040000000000000000ac0004a0000000516522000566000000838
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x77648610006e47648610006e76548610006e66548610006e56548610006e46548610006e76448610006e66448610006e56448610006e46448610006e76348610006e66348610006e56348610006e46348610007e37048610007e07048610007e12194210005d87354210007e12154210007e12190210007e12150210007e121cc21000579750c210005b9740c210006d9630c210007e1210c210005e572c4210005da73c4210004df7359510004dc7359510004be7419510004bd7419510004de7319510004dd7319510004ee7219510004ed7219510004ee72d9110004ed72d9110004de7399110004dd7399110004ee7218d10004ed7218d10004de7398910004dd7398910004f57198910004f67118910005e57294510004f47654510004f676d0510005757510510005d57310510005e57210510005f27010510005e5728c510005f2708c510004f4764c510005e57288510004f47648510006e76248510006e46248510006e77648510006e67648510006e57648510006e47648510006e76548510006e66548510006e56548510006e46548510006e76448510006e66448510006e56448510006e46448510006e76348510006e66348510006e56348510006e46348510007e37048510007e07048510007e12194110004f87654110005d87354110007e12154110005f27190110007e12190110004f87650110007e12150110004fa76cc110007e121cc11000579750c110005b9740c110006d9630c110005f2710c110007d1310c110007e1210c110005da73c4110007e121c4110004ee72d9410004ed72d9410004be7419410004bd7419410004de7319410004dd7319410004ee7219410004ed7219410004f67119410004fa7019410004ee72d9010004ed72d9010004f671d90100047e75190100047d7519010004de7319010004dd7319010004ee7219010004ed7219010004fa7019010004ee72d8c10004ed72d8c10004fa70d8c100047e7518c100047d7518c10004be7418c10004bd7418c10004ee7218c10004ed7218c10004f67118c10004ed7698810006e67198810004f57158810004ef7158810006e67158810004ed7158810004e57158810004ee7218810004f67118810004de7398410004dd7398410004ee7298410004ed7298410004ed76c8410004f57688410005e57288410006e56288410004ef7648410006e66148410006e76248410006e66248410006e56248410006e46248410005e77648410006e77648410006e76548410006e66548410006e56548410006e46548410006e76448410006e66448410006e56448410006e46448410006e76348410006e66348410006e56348410006e46348410006e52198010005e572c4010006e562c4010004f97684010007e12184010004f77644010006e56244010004fb7644010
  | 1 => 0xc12000579750c120005b9740c120006d9630c120005ea720c120007c9320c120007e1210c120005da73c8120007e121c8120004f671d9420004f571d9420004be7419420004bd7419420004de7319420004dd7319420004ee7219420004f67119420004f57119420004fa7019420004ee72d9020004f671d9020004f571d90200047e75190200047d7519020004de7319020004dd7319020004f67119020004f57119020004fa7019020004f671d8c20004f571d8c20004fa70d8c200047e7518c200047d7518c20004be7418c20004bd7418c20004ee7218c20004f67118c20004f57118c20004de7398820004dd7398820006e67258420006e561c8420004f57688420005e57288420006e66148420004f77648420006e66248420005e77648420006e77648420006e76548420006e66548420006e56548420006e46548420006e76448420006e66448420006e56448420006e46448420006e76348420006e66348420006e56348420006e46348420006e52198020005e571c8020006e561c8020007e12188020004ef7648020006e56148020004fb7648020004de73d9710004dd73d9710004ee72d9710004ed72d9710004be7419710004bd7419710004de7319710004dd7319710004ee7219710004ed7219710004de73d9310004dd73d9310004ee72d9310004ed72d93100047e75193100047d7519310004de7319310004dd7319310004ee7219310004ed7219310004ee72d8f10004ed72d8f10006d67198f10004ee7218f10004ed7218f10004de73d8b10004dd73d8b10006ce6398b10006cd6398b10006e67198b10006ce6358b10006cd6358b10006e67158b10004de7318b10004dd7318b10006d56394710005e57294710006e56294710006d56354710006e56254710006d563d0710006e562d0710005757510710005d57310710006d56310710005e57210710006e56210710005e5728c710006e5628c710006d6634c710006e5624c710006ce63c8710006cd63c8710006d66388710006d56388710006e56288710006ce6348710006cd6348710006d66348710006d56348710006e76248710006e66248710006e56248710006e46248710005e77648710006e77648710006e76548710006e66548710006e56548710006e46548710006e76448710006e66448710006e56448710006e46448710006e76348710006e66348710007c66348710006c66348710006e56348710007c56348710006c56348710006e46348710004be7419610004bd7419610004de7319610004dd7319610004ee7219610004ed7219610004ee72d9210004ed72d9210004de7399210004dd73992100047e7518e100047d7518e10004be7418e10004bd7418e10004ee7218e10004ed7218e10004be74d8a10004bd74d8a10006e66248610006e56248610006e
  | 2 => 0x7d1214c030007c1214c030004de73d9720004dd73d9720004f671d9720004f571d9720004be7419720004bd7419720004de7319720004dd7319720004f67119720004f57119720004de73d9320004dd73d9320004f671d9320004f571d93200047e75193200047d7519320004de7319320004dd7319320004f67119320004f57119320004f671d8f20004f571d8f20006ce7298f20004f67118f20004f57118f20006cd6394b20005e57194b20006cd6354b20006cd63d0b200056d7510b20005cd7310b20006cd6310b20005e57110b20005e5718cb20006ce634cb20006d66398720006d56398720006d66358720006d56358720006e67258720006e65258720006e55258720006e74258720006e44258720006e63258720006e53258720006ce63c8720006cd63c8720006e561c8720006d66388720006d56388720006ce6348720006cd6348720006e66148720006d66348720006d56348720005e77648720006e77648720006e76548720006e66548720006e56548720006e46548720006e76448720006e66448720006e56448720006e46448720006e76348720006e66348720007c66348720006c66348720006e56348720007c56348720006c56348720006e46348720004be7419620004bd7419620004de7319620004dd7319620004f67119620004f57119620004f671d9220004f571d9220004de7399220004dd73992200047e7518e200047d7518e20004be7418e20004bd7418e20004f67118e20004f57118e20006e66148620006e56148620006e76548620006e66548620006e56548620006e46548620006e76448620006e66448620006e56448620006e46448620006e76348620006e66348620006e56348620006e46348620007e37048620007e07048620007e12194220005d87354220007e12154220007e12190220007e12150220007e121cc22000579750c220005b9740c220006d9630c220007e1210c220005e571c8220005da73c8220004df7359520004dc7359520004be7419520004bd7419520004de7319520004dd7319520004f67119520004f57119520004f671d9120004f571d9120004de7399120004dd7399120004f67118d20004f57118d20005e57194920004ec7654920004ee76d09200056d7510920005cd7310920005e57110920005ea7010920005e5718c920005ea708c920004ec764c920005e57288520006e76148520006e46148520006e76548520006e66548520006e56548520006e46548520006e76448520006e66448520006e56448520006e46448520006e76348520006e66348520006e56348520006e46348520007e37048520007e07048520007e12194120004f87654120005d87354120007e12154120005ea7290120007e12190120004f87650120007e12150120004fa76cc120007e121c
  | 3 => 0xe4358830006cd4358830004ef7158830006e67158830006e571588300065d65cc8300069d64cc830005d970cc8300065d654c8300069d644c830006ce624c830004ee7298430004ed7298430006766598430006756598430006b66498430006b56498430005e57298430006e66298430006e56298430006e67298430004f57298430006e57298430004e57298430006f27098430006766558430006756558430006b66458430006b56458430006e66258430006e56258430006d64358430006d54358430004f77258430006e67258430006e572584300065d65cc4300069d64cc430005d970cc4300065d654c4300069d644c430006d6614c430004ef76c8430004ed76c84300066e65c84300066d65c8430006ae64c8430006ad64c8430006e661c8430006e561c8430004f77688430004f57688430006766588430006756588430006b66488430006b56488430005e57288430006e66288430006e56288430004ef7648430004ed76484300066e65484300066d6548430006ae6448430006ad6448430006e66148430006e56148430007c73148430007c53148430004f77648430004f57648430006766548430006756548430006b66448430006b56448430006e66248430006e56248430007c73248430007c53248430005e77648430006e77648430004e77648430006e67648430005e57648430006e57648430004e57648430006e47648430006e76548430006e66548430007666548430006666548430006e56548430007656548430006656548430006e46548430006e76448430006e66448430007a66448430006a66448430006e56448430007a56448430006a56448430006e46448430007c67348430007c57348430006e66348430007c75348430007c45348430007c64348430007c54348430007e27048430007e17048430006e52198030004f976d40300067965d40300075b53d4030007e121d4030004f97614030006796514030005b97414030005d97314030005e97214030005f17114030007e12114030004f97690030006796590030005d97390030005e97290030006e96290030005f17190030006f16190030007e12190030006796550030006ba6450030007994350030006e96250030006f16150030007e121500300065d65cc030007c521cc03000679658c030005d9738c030007e1218c030004df764c0300065d654c030007c5214c030004fb764c03000679654c030007e1214c030005db764c030006db764c030005da754c030005d8754c030006db654c0300075a654c030006d9654c03000759654c03000659654c030005db744c030005d9744c0300079a644c03000799644c030005db724c030007ca624c030007c9624c030005db714c030007d2614c030007d1614c030007cb214c030007d2214c030007c9214c030
  | 4 => 0x9630004bd7419630004ee7219630004ed7219630004f67119630004f57119630004ee72d9230004ed72d9230004f671d9230004f571d92300065d65d4e30005d970d4e300059d7414e30005cd7214e30005d57114e30005d97014e30005cd7290e30005d57190e30004f67198a30004f57198a30004ee7298630004ed7298630006e66148630006e56148630007c73148630007c53148630006e66248630006e56248630007c73248630007c53248630006e77648630006e67648630006e57648630006e47648630006e76548630006e66548630006e56548630006e46548630006e76448630006e66448630006e56448630006e46448630007c67348630007c57348630007c75348630007c45348630007c64348630007c54348630007e12194230005d873542300075b5354230007e12154230007c521cc230007e121cc230004df7359530004fb7059530004be7419530004bd7419530004ee7219530004ed7219530004f67119530004f57119530004ee72d9130004ed72d9130004f671d9130004f571d9130004dd7399130004f97099130004de7694d30004dc7654d30005d87054d30004f67118930004f57118930004ee7218530004ed7218530005e57288530006e76148530006e46148530006e76248530006e46248530006e77648530006e67648530006e57648530006e47648530006e76548530006e66548530006e56548530006e46548530006e76448530006e66448530006e56448530006e46448530007c65348530007c55348530004fa7694130007e12194130004f87654130005d87354130007595354130007e12154130007e121cc130007c5218c130004be74d9430004bd74d9430004ee72d9430004ed72d9430004f671d9430004f571d94300047d76994300065c73594300067870594300047e7519430004be7419430004bd7419430004de7319430004ee7219430004ed7219430004f67119430004f57119430004fa70194300047e75d90300047d75d9030004ee72d9030004ed72d9030004f671d9030004f571d9030004bd76990300063e65990300063d65990300069e7399030006ba70990300063e65590300063d65590300047e75190300047d7519030004be7419030004ee7219030004ed7219030004f67119030004f57119030004dd76d4c300065d65d4c30004dd7614c300065d6514c300059d7414c30005cd7214c30005d57114c30005d97014c30004dd7690c300065d6590c30005cd7290c30005d57190c30005d97090c300065d6550c300069e6450c30004f67198830004f571988300066e65988300066d6598830006ae6498830006ad6498830005e57198830006e67198830004ed7198830006e57198830004e57198830006ea70988300066e65588300066d6558830006ae6458830006ad6458830006c
  | 5 => 0x6e561c8640004f77688640004f57688640006e66288640006e56288640004ef7648640004ed7648640006e66148640006e56148640004f77648640004f57648640006e66248640006e56248640005e77648640006e77648640004e77648640006e67648640005e57648640006e57648640004e57648640006e47648640006e76548640006e66548640006e56548640006e46548640006e66348640006e56348640007e27048640007e17048640006e96294240006f16194240007e12194240005d87354240006e96254240006f16154240007e12154240007a521d0240005da73d0240007e121d0240004df7359540004dc7359540004ef7259540004ec7259540004f77159540004f47159540004de7319540004dd7319540004ee7219540004ed7219540004f67119540004f57119540004bc7655140005ba70d0d40004f67118940004f57118940004ee7218540004ed7218540005e57288540006e76148540006e46148540006e76248540006e46248540006e77648540006e67648540006e57648540006e47648540006e76548540006e66548540006e56548540006e46548540007a77448540007a47448540007a65448540007a55448540006e76348540006e46348540007a74348540007a54348540007e27048540007e17048540007e12194140004f87654140005d87354140007e12154140005da73d0140007e121d0140007a52190140004be7419440004de7319440004dd7319440004ee7219440004ed7219440004f67119440004f57119440004fa7019440004f67198840004f57198840004ee7298440004ed7298440005e57288440006e66148440006e56148440006e66248440006e56248440006e77648440006e67648440006e57648440006e47648440006e76548440006e66548440006e56548440006e46548440006e66448440006e66348440006e56348440006e52198040007a521d0040007e12190040004bf7650040007a52150040004fb7650040007e12150040004be7419730004bd7419730004ee7219730004ed7219730004f67119730004f57119730004ee72d9330004ed72d9330004f671d9330004f571d9330005d87054f30004f67198b30004f57198b30004ee7298730004ed7298730006e66148730006e56148730006e66248730006e56248730006e77648730006e67648730006e57648730006e47648730006e76548730006e66548730006e56548730006e46548730006e76448730006e66448730006e56448730006e46448730007c65348730007c55348730007e27048730007e170487300067965d4330005d973d43300075953d4330007e121d4330005b97414330005d97314330005e97214330005f17114330007e12114330005e97290330005f17190330007e12190330007e12150330004be741
  | 6 => 0xe63c8450006cd63c8450006e661c8450006e561c8450004f77688450004f57688450006b66488450006b56488450006d66388450006d56388450005e57288450006e66288450006e56288450004ef7648450004ed7648450006ae6448450006ad6448450006ce6348450006cd6348450006e66148450006e56148450004f77648450004f57648450006b66448450006b56448450006d66348450006d56348450006e66248450006e56248450005e77648450006e77648450004e77648450006e67648450005e57648450006e57648450004e57648450006e47648450006e66548450006e66448450007a66448450006a66448450006e56448450007a56448450006a56448450006e66348450007c66348450006c66348450006e56348450007c56348450006c56348450006e521980500065d63d40500076521d4050006b96494050006d96394050006e96294050006f16194050007e121940500047f76540500065d6354050007652154050004fb7654050006b96454050005d87354050006d96354050006e96254050006f16154050007e12154050004de73d9740004dd73d9740004de7319740004dd7319740004ee7219740004ed7219740004f67119740004f571197400063e6595340004ee7298f40004ed7298f40004f67198f40004f57198f40006ce7298f40006cd7298f40006d67198f40006d57198f400069e5458f400069d5458f400069e6350f40004f67198b40004f57198b40004ee7298740004ed7298740006ce63c8740006cd63c8740006d66388740006d56388740006ce6348740006cd6348740006e66148740006e56148740006d66348740006d56348740006e66248740006e56248740006e77648740006e67648740006e57648740006e47648740006e76548740006e66548740006e56548740006e46548740007a77448740007a47448740007a65448740007a55448740006e66348740007c66348740006c66348740006e56348740007c56348740006c56348740007a74348740007a54348740004ee72d9640004ed72d9640004f671d9640004f571d9640004de7319640004dd7319640004ee7219640004ed7219640004f67119640004f57119640004de7398a40004dd7398a40004f67198a40004f57198a40005e57198a40006ce7398a40006cd7398a40006e67198a40004ed7198a40006e57198a40004e57198a40006ea7098a40004ef7158a40006e67158a40006e57158a40004de7398640004dd7398640004ee7298640004ed7298640005e57298640006e66298640006e56298640006d67398640006d57398640006e67298640004f57298640006e57298640004e57298640006f27098640006e66258640006e56258640004f77258640006e67258640006e57258640004ef76c8640004ed76c8640006e661c8640
  | 7 => 0x8c21004f67118c21005e57288421004ef7648421006e66148421004f77648421006e66248421005e77648421006e77648421006e76548421006e66548421006e56548421006e46548421006e76448421006e66448421006e56448421006e46448421006e76348421006e66348421006e56348421006e46348421006e52198021006e52158021004ef7259350004ec7259350004f77159350004f47159350005787054f50004f67198b50004f57198b50004ee7298750004ed7298750006e66148750006e56148750006e66248750006e56248750006e77648750006e67648750006e57648750006e47648750006e66448750006e56448750006e66348750006e56348750007675348750007655348750004de7399250004dd7399250004de7398a50004dd7398a50004f67198a50004f57198a50004de7398650004dd7398650004ee7298650004ed7298650006e66148650006e56148650006e66248650006e56248650006e77648650006e67648650006e57648650006e47648650006e66448650006e56448650006e66348650006e56348650007e27048650007e170486500076521d4250007e121d4250004be7418d50004bd7418d50004ee7218d50004ed7218d50004f67118d50004f57118d500069e7418d500069d7418d50006ce7218d50006cd7218d50006d67118d50006d57118d50006d97018d500065c63d4d50004f67118950004f57118950004ee7218550004ed7218550006cf63c8550006cc63c8550006d76388550006d46388550005e57288550006cf6348550006cc6348550006e76148550006e46148550006d76348550006d46348550006e76248550006e46248550006e77648550006e67648550006e57648550006e47648550006e76448550006e46448550006e76348550007c76348550006c76348550006e46348550007c46348550006c46348550007675348550007655348550007e27048550007e17048550006d863d4150007e121d41500076521941500069e6498c500069d6498c500069e6458c500069d6458c50006d87058c50004f67198850004f57198850006ae6498850006ad6498850006ce6398850006cd6398850005e57198850006e67198850004ed7198850006e57198850004e57198850006ae6458850006ad6458850006ce6358850006cd6358850004ef7158850006e67158850006e57158850004ee7298450004ed7298450006b66498450006b56498450006d66398450006d56398450005e57298450006e66298450006e56298450006e67298450004f57298450006e57298450004e57298450006b66458450006b56458450006d66358450006d56358450006e66258450006e56258450004f77258450006e67258450006e57258450004ef76c8450004ed76c8450006ae64c8450006ad64c8450006c
  | 8 => 0x7a67414d21005a67414d21005e57414d21007a57414d21005a57414d21005e67314d21007675314d21007c65314d21007655314d21007c55314d21005e67014d21007e27014d21005e27014d21005e57014d21007e17014d21005e17014d21005e776d0d21005e676d0d21005e576d0d21005e476d0d21005e775d0d21005e675d0d21005e575d0d21005e475d0d21007a764d0d21007a464d0d21007a654d0d21007a554d0d21005e670d0d21007e270d0d21005e270d0d21005e570d0d21007e170d0d21005e170d0d21005e77690d21005e67690d21006e67690d21004e67690d21005e57690d21006e57690d21004e57690d21005e47690d21005e77590d21005e67590d21005e57590d21005e47590d21005e57490d21005e67390d21007c66390d21007c56390d21007c65390d21007c55390d21007a74390d21007c74390d21005e67090d21005e57090d21005e77650d21005e67650d21005e57650d21005e47650d21005e77550d21005e67550d21005e57550d21005e47550d21007a76450d21007a46450d21007a65450d21007a55450d21007c66350d21007c56350d21007c65350d21007c55350d21007c74350d21007a64350d21005e77050d21005e47050d21005e77610d21005e67610d21005e57610d21005e47610d21005e77510d21005e67510d21005e57510d21005e47510d21005e67410d21005e67310d21007a74310d21007c64310d21007a54310d21007c54310d21005e67010d21005e57010d21005e675d8121005e575d8121006e765d8121006e565d8121005e674d8121005e574d8121006e664d8121006e464d8121005e673d8121007c673d8121005c673d8121005e573d8121007c573d8121005c573d8121006e763d8121006e563d8121005e67598121005e57598121005e67498121007a67498121005a67498121005e57498121007a57498121005a57498121005e67398121005e57398121005e67098121006e76098121007e36098121005e77558121005e47558121006e76558121006e56558121005e77458121005e47458121006e66458121006e46458121005e77358121005e47358121006e76358121006e56358121007e36058121006e66058121005e67618121005e67518121005e57518121005e67418121005e57418121005e67318121005e57318121006e76018121007e26018121006e56018121007e16018121004ee72d9421004f671d9421004be7419421004bd7419421004de7319421004dd7319421004ee7219421004f67119421004fa7019421004f97019421004ee72d9021004f671d90210047e75190210047d7519021004de7319021004dd7319021004ee7219021004f67119021004fa7019021004f97019021004ee72d8c21004f671d8c21004fa70d8c21004f970d8c21004ee721
  | 9 => 0x576d5121005e476d51210076665d51210076565d5121007a764d5121007a464d5121005e673d5121005e573d5121005e670d5121005e570d5121005e77695121005e67695121005e57695121005e47695121005e57595121005e67495121007a66495121007a56495121007675495121007a75495121007275495121005e67395121005e57395121005e67095121005e57095121005e77655121006e77655121004e77655121005e67655121005e57655121005e47655121006e47655121004e47655121007666555121007656555121007a66455121007a56455121007a75455121007665455121005e77355121005e47355121005e77055121005e47055121005e77615121005e67615121006e67615121004e67615121005e57615121006e57615121004e57615121005e47615121005e67515121005e67415121007a76415121007a46415121007675415121007a65415121007655415121007a55415121005e67315121007c67315121005c67315121005e57315121007c57315121005c57315121005e67015121007e27015121005e27015121005e57015121007e17015121005e17015121005e675d8d21005e575d8d21006e765d8d21006e565d8d21005e674d8d21005e574d8d21006e664d8d21006e464d8d21005e670d8d21007e270d8d21005e270d8d21005e570d8d21007e170d8d21005e170d8d21005e57698d21005e67598d21005e57598d21005e67498d21007a67498d21005a67498d21005e57498d21007a57498d21005a57498d21005e67398d21006e76398d21007c76398d21005e67098d21005e57098d21005e77558d21005e47558d21006e76558d21006e56558d21005e77458d21005e47458d21006e66458d21006e46458d21007c76358d21006e66358d21005e77058d21005e47058d21005e67618d21005e67518d21005e57518d21005e67418d21005e57418d21005e67318d21006e76318d21007c66318d21006e56318d21007c56318d21005e67018d21005e57018d21005e776d4d21005e676d4d21005e576d4d21005e476d4d21005e674d4d21005e574d4d21005e670d4d21005e570d4d21005e77694d21005e67694d21005e57694d21005e47694d21005e57594d21005e67494d21005e57494d21005e67394d21007c66394d21007c56394d21007675394d21007c75394d21005e67094d21005e57094d21005e77654d21005e67654d21005e57654d21005e47654d21005e77454d21005e47454d21007c66354d21007c56354d21007c75354d21007665354d21005e77054d21007e37054d21005e37054d21005e47054d21007e07054d21005e07054d21005e77614d21005e67614d21006e67614d21004e67614d21005e57614d21006e57614d21004e57614d21005e47614d21005e67514d21005e67414d21
  | 10 => 0xc921005e6728c921005f2708c921005f1708c921005e6768c921006e6768c921005e7758c921005e6758c921005e5758c921005e4758c921005e7748c921005e6748c921005e5748c921005e4748c921005e5738c921005e6708c921007e2708c921005e2708c921005e5708c921007e1708c921005e1708c921005e6764c921005e4764c921005e7754c921005e6754c921005e5754c921005e4754c921005e7744c921005e6744c921005e5744c921005e4744c921007c7734c921007c7634c921007c4634c921007c6534c921007c5534c921007c6434c921007c5434c921005e7704c921005e4704c921004f6760c921005e6720c921005e6760c921006e6760c921005e7750c921005e6750c921005e5750c921005e4750c921005e7740c921005e6740c921005e5740c921005e4740c921005e6730c921007c6730c921005e6700c921005e5700c921005d673d8121005d573d8121005b67498121005b57498121005e674d9521005e574d9521005e673d9521005e573d9521005e670d9521005e570d9521005e57699521005e67599521006e76599521007676599521005e67499521005e57499521005e67399521005e57399521005e67099521005e57099521007676559521006e66559521005e77459521007a77459521005a77459521005e47459521007a47459521005a47459521005e77359521005e47359521005e77059521005e47059521005e67619521005e67519521006e76519521007666519521006e56519521007656519521005e67419521007a67419521005a67419521005e57419521007a57419521005a57419521005e67319521007c67319521005c67319521005e57319521007c57319521005c57319521005e67019521007e27019521005e27019521005e57019521007e17019521005e17019521005e675d9121005e575d9121006e765d9121006e565d9121005e673d9121005e573d9121005e670d9121005e570d9121005e57699121005e67599121005e57599121006e66599121006e46599121005e67499121006e76499121007a76499121005e67399121005e57399121005e67099121005e57099121005e77559121005e47559121006e76559121006e56559121007a76459121006e66459121005e77359121005e47359121005e77059121005e47059121005e67619121005e67519121007667519121005667519121005e57519121007657519121005657519121006e66519121006e46519121005e67419121006e76419121007a66419121006e56419121007a56419121006a56419121005e67319121007c67319121005c67319121005e57319121007c57319121005c57319121005e67019121007e27019121005e27019121005e57019121007e17019121005e17019121005e776d5121005e676d5121005e
  | 11 => 0x5e77250d21005e47250d21005e67210d21005e57210d21005e675d8921005e575d8921005e674d8921005e574d8921005e673d8921005e573d8921005e670d8921005e570d8921005e676d4921005e476d49210076765d49210076465d4921005e674d4921005e574d49210076754d49210076554d4921005e673d4921005e573d4921005e670d4921005e570d4921004f67694921005e67294921005e67694921006e67694921005e57594921005e67494921005e57494921005e67394921005e57394921005e67094921005e57094921005e67654921005e47654921007677554921007676554921007646554921005e77454921005e47454921007675454921007655454921005e77354921005e47354921005e77054921005e47054921004f67614921005b67414921005b57414921005d67314921005d57314921005e67214921005f27014921005f17014921005e67614921006e67614921005e67514921007667514921005e67414921007a67414921005a67414921005e57414921007a57414921005a57414921005e67314921007c67314921005c67314921005e57314921007c57314921005c57314921005e67014921007e27014921005e27014921005e57014921007e17014921005e17014921005e676d0921005e476d0921005e775d0921005e675d0921005e575d0921005e475d0921007a764d0921007a464d0921007a654d0921007a554d0921005e673d0921005e573d0921005e670d0921005e570d0921004f67690921005e67290921005e67690921006e67690921005e77590921005e67590921005e57590921005e47590921005e57490921005e67390921005e57390921005e67090921005e57090921005e67650921005e47650921005e77550921005e67550921005e57550921005e47550921007a77450921007a76450921007a46450921007a65450921007a55450921005e77350921005e47350921005e77050921005e47050921004f67610921005767510921005757510921005d67310921005d57310921005e67210921005f27010921005f17010921005e67610921006e67610921005e77510921005e67510921007667510921005667510921005e57510921007657510921005657510921005e47510921005e67410921007a67410921005e67310921007c67310921005c67310921005e57310921007c57310921005c57310921005e67010921007e27010921005e27010921005e57010921007e17010921005e17010921005e676cc921005e476cc921005e775cc921005e675cc921005e575cc921005e475cc921005e774cc921005e674cc921005e574cc921005e474cc921007c763cc921007c463cc921007c653cc921007c553cc921007c643cc921007c543cc921005e670cc921005e570cc921004f6768
  | 12 => 0x67110521005ea7010521005e97010521005e67610521006e67610521005e77510521005e67510521007667510521005667510521005e57510521007657510521005657510521005e47510521005e67410521007a67410521005e67310521007c67310521005c67310521005e57310521007c57310521005c57310521005e67010521007e27010521005e27010521005e57010521007e17010521005e17010521005e676cc521005e476cc521005e775cc521005e675cc521005e575cc521005e475cc521005e774cc521005e674cc521005e574cc521005e474cc521007c763cc521007c463cc521007c653cc521007c553cc521007c643cc521007c543cc521005e670cc521005e570cc521004ee768c521005e6718c521005ea708c521005e9708c521005e6768c521006e6768c521005e7758c521005e6758c521005e5758c521005e4758c521005e7748c521005e6748c521005e5748c521005e4748c521005e5738c521005e6708c521007e2708c521005e2708c521005e5708c521007e1708c521005e1708c521005e6764c521005e4764c521005e7754c521005e6754c521005e5754c521005e4754c521005e7744c521005e6744c521005e5744c521005e4744c521007c7734c521007c7634c521007c4634c521007c6534c521007c5534c521007c6434c521007c5434c521005e7704c521005e4704c521004ee760c521005e6710c521005e6760c521006e6760c521005e7750c521005e6750c521005e5750c521005e4750c521005e7740c521005e6740c521005e5740c521005e4740c521005e6730c521007c6730c521005e6700c521005e5700c521005ce73d8121005cd73d8121005ae7498121005ad7498121005e57299521005b77459521005b47459521005e77259521005b67419521005b57419521005d67319521005d57319521005f27019521005f17019521005e57299121005e77259121005767519121005757519121006b56419121005d67319121005d57319121005f27019121005f17019121005e672d5121005e572d5121007375495121005e67295121005e57295121004f77655121004f47655121005e77255121005e47255121004f67615121004f57615121005d67315121005d57315121005e67215121005e57215121005f27015121005f17015121005f270d8d21005f170d8d21005b67498d21005b57498d21005e57298d21005e77258d21005e672d4d21005e572d4d21005e67294d21005e57294d21005e77254d21005e47254d21005f37054d21005f07054d21004f67614d21004f57614d21005b67414d21005b57414d21005e67214d21005e57214d21005f27014d21005f17014d21005e672d0d21005e572d0d21005f270d0d21005f170d0d21004f67690d21004f57690d21005e67290d21005e57290d21
  | 13 => 0x51210072f5495121005e67195121005e57195121004ef7655121004ec7655121005e77155121005e47155121004ee7615121004ed7615121005ce7315121005cd7315121005e67115121005e57115121005ea7015121005e97015121005ea70d8d21005e970d8d21005ae7498d21005ad7498d21005e57198d21005e77158d21005e671d4d21005e571d4d21005e67194d21005e57194d21005e77154d21005e47154d21005eb7054d21005e87054d21004ee7614d21004ed7614d21005ae7414d21005ad7414d21005e67114d21005e57114d21005ea7014d21005e97014d21005e671d0d21005e571d0d21005ea70d0d21005e970d0d21004ee7690d21004ed7690d21005e67190d21005e57190d21005e77150d21005e47150d21005e67110d21005e57110d21005e675d8521005e575d8521005e674d8521005e574d8521005e673d8521005e573d8521005e670d8521005e570d8521005e676d4521005e476d45210076765d45210076465d4521005e674d4521005e574d45210076754d45210076554d4521005e673d4521005e573d4521005e670d4521005e570d4521004ee7694521005e67194521005e67694521006e67694521005e57594521005e67494521005e57494521005e67394521005e57394521005e67094521005e57094521005e67654521005e47654521007677554521007676554521007646554521005e77454521005e47454521007675454521007655454521005e77354521005e47354521005e77054521005e47054521004ee7614521005ae7414521005ad7414521005ce7314521005cd7314521005e67114521005ea7014521005e97014521005e67614521006e67614521005e67514521007667514521005e67414521007a67414521005a67414521005e57414521007a57414521005a57414521005e67314521007c67314521005c67314521005e57314521007c57314521005c57314521005e67014521007e27014521005e27014521005e57014521007e17014521005e17014521005e676d0521005e476d0521005e775d0521005e675d0521005e575d0521005e475d0521007a764d0521007a464d0521007a654d0521007a554d0521005e673d0521005e573d0521005e670d0521005e570d0521004ee7690521005e67190521005e67690521006e67690521005e77590521005e67590521005e57590521005e47590521005e57490521005e67390521005e57390521005e67090521005e57090521005e67650521005e47650521005e77550521005e67550521005e57550521005e47550521007a77450521007a76450521007a46450521007a65450521007a55450521005e77350521005e47350521005e77050521005e47050521004ee76105210056e75105210056d7510521005ce7310521005cd7310521005e
  | 14 => 0x5d67319621005d57319621005e57219621005f27019621005f17019621005e572d9221005767519221005757519221006b56419221005d67319221005d57319221005e57219221005f27019221005f17019221007375495221004f77655221004f47655221005e77255221005e47255221004f67615221004f57615221005d67315221005d57315221005e67215221005e57215221005f27015221005f17015221005e572d8e21005f270d8e21005f170d8e21005e57218e21005f37054e21005f07054e21004f67614e21004f57614e21005b67414e21005b57414e21005e67214e21005e57214e21005f27014e21005f17014e21005f270d0e21005f170d0e21004f67690e21004f57690e21005e67290e21005e57290e21005b67414a21005b57414a21005d67314a21005d57314a21005f27014a21005f17014a21005767510a21005757510a21005d67310a21005d57310a21007a54210a21005f27010a21005f17010a21005f2708ca21005f1708ca21005d673d8221005d573d8221004bf7459521004bc7459521004be7419521004bd7419521004de7319521004dd7319521004fa7019521004f970195210047e75191210047d7519121004de7319121004dd7319121004fa7019121004f97019121004fa70d8d21004f970d8d21004be7498d21004bd7498d21004ee76d4921005e671d4921005e67194921004ec7654921005e47154921005ae7414921005ad7414921005ce7314921005cd7314921005e67114921005ea7014921005e97014921004ee76d0921005e671d0921005e67190921004ec7650921006ac6450921005e471509210056e75109210056d7510921005ce7310921005cd7310921005e67110921005ea7010921005e97010921004ee76cc921005e671cc921005e6718c921005ea708c921005e9708c921004ec764c921005e4714c921005e6710c921004f676d4521005e672d4521005e67294521004f47654521005e47254521005b67414521005b57414521005d67314521005d57314521005e67214521005f27014521005f17014521004f676d0521005e672d0521005e67290521004f47650521006b46450521005e47250521005767510521005757510521005d67310521005d57310521005e67210521005f27010521005f17010521004f676cc521005e672cc521005e6728c521005f2708c521005f1708c521004f4764c521005e4724c521005e6720c521004de73d8121004dd73d8121005e57199521005af7459521005ac7459521005e77159521005ae7419521005ad7419521005ce7319521005cd7319521005ea7019521005e97019521005e57199121005e771591210056e75191210056d7519121006ad6419121005ce7319121005cd7319121005ea7019121005e97019121005e671d5121005e571d
  | 15 => 0xa7099131004f97099131004dc7654d31005d87054d31005d67190d31004dc7650d31005e57294531004f47654531004f676d0531005757510531005d67310531005e57210531005f17010531005da708c531004ee7218131004ed7218131004ee72d9431004ed72d9431004be7419431004bd7419431004de7319431004ee7219431004ed7219431004f67119431004fa7019431004f97019431004ee72d9031004ed72d9031004f671d90310047e75190310047d7519031004de7319031004ee7219031004ed7219031004fa7019031004f97019031006e67198831006e67158831005e5728c431006e5628c431004df764c431004f7764c431006e5624c431004be7419721004bd7419721004de7319721004dd7319721004fa7019721004f970197210047e75193210047d7519321004de7319321004dd7319321004fa7019321004f97019321004fa70d8f21004f970d8f21005ae7414b21005ad7414b21005ce7314b21005cd7314b21005ea7014b21005e97014b210056e7510b210056d7510b21006ad6410b21005ce7310b21005cd7310b21005ea7010b21005e97010b21005ea708cb21005e9708cb21005e571d9721005ae7419721005ad7419721005ce7319721005cd7319721005e57119721005ea7019721005e97019721005e571d93210056e75193210056d7519321006ad6419321005ce7319321005cd7319321005e57119321005ea7019321005e970193210072f5495321004ef7655321004ec7655321005e77155321005e47155321004ee7615321004ed7615321005ce7315321005cd7315321005e67115321005e57115321005ea7015321005e97015321005e571d8f21005ea70d8f21005e970d8f21005e57118f21005eb7054f21005e87054f21004ee7614f21004ed7614f21005ae7414f21005ad7414f21005e67114f21005e57114f21005ea7014f21005e97014f21005ea70d0f21005e970d0f21004ee7690f21004ed7690f21005e67190f21005e57190f21005ae7414721005ad7414721005ce7314721005cd7314721005ea7014721005e970147210056e75107210056d7510721005ce7310721005cd7310721007a54110721005ea7010721005e97010721005ea708c721005e9708c721005ce73d8321005cd73d8321004be7419621004bd7419621004de7319621004dd7319621004fa7019621004f970196210047e75192210047d7519221004de7319221004dd7319221004fa7019221004f97019221004fa70d8e21004f970d8e21005b67414621005b57414621005d67314621005d57314621005f27014621005f17014621005767510621005757510621006b56410621005d67310621005d57310621005f27010621005f17010621005f2708c621005f1708c621005e572d9621005b67419621005b57419621
  | 16 => 0x9741004f970197410063e6595341005b47155341004ee7298f41004ed7298f410067565d4741005b574d47410073554d4741005b57414741005d57314741005e57214741005f17014741004ee7298341004ed7298341004ee72d9641004ed72d9641004de7319641004dd7319641004ee7219641004ed7219641004fa7019641004f97019641006e67198a41006e67158a41005e57294641006e56294641006e56254641006e562d0641004ef7259541004ec7259541004f77159541004de7319541004dd7319541004ee7219541004ed7219541004fa7019541004f97019541004bc7655141004fa70d8d41004f970d8d41004f67694541005e57294541004f47654541007355454541004de73d8141004dd73d8141004de73d9441004dd73d9441004ee72d9441004ed72d9441004fa70d9441004f970d94410047d76994410067471594410047e7519441004be7419441004de7319441004dd7319441004ee7219441004ed7219441004f67119441004fa7019441004f970194410065e6598c410065d6598c41006d67198c410065e6558c410065d6558c410066e65988410066d6598841006ce6398841006cd6398841006e671988410066e65588410066d6558841006ce6358841006cd6358841006e67158841004f576d44410067565d4441006e562d4441004f57614441006756514441005b57414441005d57314441005e57214441006e56214441005f170144410063d65d0441006756590441005e57290441006e56290441004bf76504410063d6550441004f77650441006756550441006e562504410067a6598041006796598041006da6398041006d96398041006ea6298041006e962980410067a6558041006796558041006da6358041006d96358041006ea6258041006e96258041004be7419731004bd7419731004ee7219731004ed7219731004fa7019731004f97019731004ee72d9331004ed72d9331004fa7099331004f97099331005d87054f31004ee72d9631004ed72d9631004fa70d9631004f970d9631004be7419631004bd7419631004ee7219631004ed7219631004fa7019631004f97019631004ee72d9231004ed72d9231004fa70d9231004f970d92310047e75192310047d7519231004ee7219231004ed7219231004fa7019231004f97019231006e67198a31006e67158a31005e57294631006e56294631006e56254631006e562d0631005757510631005e57210631006e56210631005f17010631006e562cc631006ea6298231006e96298231006db3198231006ea6258231006e96258231006f25158231006f15158231006f34158231006f04158231004fb7059531004f87059531004be7419531004bd7419531004ee7219531004ed7219531004fa7019531004f97019531004ee72d9131004ed72d9131004f
  | 17 => 0x6f16158042004be7419732004bd7419732004f67119732004f57119732004fa7019732004f97019732004f671d9332004f571d9332004fa7099332004f97099332005d87054f32004f671d9632004f571d9632004fa70d9632004f970d9632004be7419632004bd7419632004f67119632004f57119632004fa7019632004f97019632004f671d9232004f571d9232004fa70d9232004f970d92320047e75192320047d7519232004f67119232004f57119232004fa7019232004f97019232005e57194a320056d7510a32005e57110a32005e97010a32006e67258632006e65258632006e55258632006e74258632006e44258632006e73258632006f26198232006f16198232006db3298232006f26158232006f16158232006ea5258232006e95258232006eb4258232006e84258232004fb7059532004f87059532004be7419532004bd7419532004f67119532004f57119532004fa7019532004f97019532004f671d9132004f571d9132004fa7099132004f97099132004dc7654d32005d87054d32005ce7290d32004dc7650d32005e57194932004ec7654932004ee76d09320056d7510932005ce7310932005e57110932005e97010932005da708c932004f67118132004f57118132004f671d9432004f571d9432004be7419432004bd7419432004de7319432004ee7219432004f67119432004f57119432004fa7019432004f97019432004ee72d9032004f671d9032004f571d90320047e75190320047d7519032004de7319032004f67119032004f57119032004fa7019032004f97019032005e5718c832004df764c832004ef764c832006e67258432006e63258432006e53258432004ef7259351004ec72593510063e64d5351005747155351004fb7058f51004f87058f51004df7358351004dc7358351006e67198a51006e67158a51006e562d4651004de7319151004dd7319151004ee7219151004ed7219151004fa7019151004f97019151004ee7218d51004ed7218d51004ee7218151004ed7218151006b471590510069e6498c510069d6498c510069e6458c510069d6458c51006ae6498851006ad6498851006ce6398851006cd6398851006e67198851006ae6458851006ad6458851006ce6358851006cd6358851006e671588510063d64d4451006b56494451006d56394451005e57294451006e562944510047f76544510063d6454451004f77654451006b56454451006d56354451006e56254451006ba6498051006b96498051006da6398051006d96398051006ea6298051006e96298051006ba6458051006b96458051006da6358051006d96358051006ea6258051006e96258051006f25158051006f15158051004ef7259741004ec7259741004de7319741004dd7319741004ee7219741004ed7219741004fa701
  | 18 => 0x471593520063e64d53520056c7255352004fb7058f52004f87058f52004df7358352004dc7358352006e67258652006e75258652004de7319152004dd7319152004f67119152004f57119152004fa7019152004f97019152004f67118d52004f57118d52004f67118152004f57118152006ac72590520069e6498c520069d6498c520069e6458c520069d6458c520063d64d4852006ad6494852006cd6394852005e571948520047f76548520063d6454852004ef7654852006ad6454852006cd6354852006b66498452006b56498452006d66398452006d56398452006b66458452006b56458452006d66358452006d56358452006e67258452006e65258452006e55258452006ba6498052006b96498052006da6398052006d96398052006f26198052006f16198052006ba6458052006b96458052006da6358052006d96358052006f26158052006f16158052006ea5258052006e95258052004f77159742004f47159742004de7319742004dd7319742004f67119742004f57119742004fa7019742004f970197420063e6595342005ac7255342004f67198f42004f57198f420066d65d4b42005ad74d4b420072d54d4b42005ad7414b42005cd7314b42005e57114b42005e97014b42004f67198342004f57198342004f671d9642004f571d9642004de7319642004dd7319642004f67119642004f57119642004fa7019642004f97019642005e57194a42006e67258642006e65258642006e55258642006e74258642004ef7259542004f77159542004f47159542004de7319542004dd7319542004f67119542004f57119542004fa7019542004f97019542004bc7655142004fa70d8d42004f970d8d42004ee7694942005e57194942004ec76549420072d5454942004de73d8142004dd73d8142004de73d9442004dd73d9442004f671d9442004f571d9442004fa70d9442004f970d94420047d76994420066c72594420047e7519442004be7419442004de7319442004dd7319442004ee7219442004f67119442004f57119442004fa7019442004f970194420065e6598c420065d6598c42006ce7298c420065e6558c420065d6558c42004ed76d48420066d65d4842004ed76148420066d6514842005ad7414842005cd7314842005e57114842005e970148420063d65d08420066d6590842005e57190842004bf76508420063d6550842004ef76508420066d6550842006766598442006756598442006d66398442006d56398442006766558442006756558442006d66358442006d56358442006e67258442006e75258442006e45258442006e64258442006e542584420067a6598042006796598042006da6398042006d96398042006f26198042006f161980420067a6558042006796558042006da6358042006d96358042006f26158042
  | 19 => 0x8153006ba7418153006b97418153006db5318153006ea7218153006e97218153006f27118153006f171181530069d6494c530047f7654c53004df7654c530069d6454c53005d87054c53004f67198853004f57198853006ae6498853006ad6498853005e57198853006e67198853004ed7198853006e57198853004e57198853006ae6458853006ad6458853006ce5358853006cd5358853004ef7158853006e67158853006e57158853004ee7298453004ed7298453006b66498453006b56498453005e57298453006e66298453006e56298453006e67298453004f57298453006e57298453004e57298453006b66458453006b56458453006e66258453006e56258453006d65358453006d55358453004f77258453006e67258453006e57258453006ba6498053006b96498053006ea6298053006e96298053006f26198053006f16198053006ba6458053006b96458053006ea6258053006e96258053006f26158053006f161580530067b5358053006da5358053006795358053006d95358053004fa70d9743004f970d9743004ee7219743004ed7219743004f67119743004f57119743004fa7019743004f970197430063e6595343004f67198b43004f57198b43004ee7298743004ed7298743004ee7298343004ed7298343004f67198343004f57198343006ea7298343006e97298343006f27198343006f17198343006ba5458343006b95458343004ee72d9643004ed72d9643004f671d9643004f571d9643004ee7219643004ed7219643004f67119643004f57119643004fa7019643004f97019643005d87054e43005da70d0e43004f67198a43004f57198a43004fa7098a43004f97098a43005e57198a43006e67198a43004ed7198a43006e57198a43004e57198a43006ea7098a43006e97098a43006ce5358a43006cd5358a43004ef7158a43006e67158a43006e57158a43004ee7298643004ed7298643004fa7098643004f97098643005e57298643006e66298643006e56298643006e67298643004f57298643006e57298643004e57298643006f27098643006f17098643006e66258643006e56258643006d65358643006d55358643004f77258643006e67258643006e57258643004ef7259543004ec7259543004f77159543004f47159543004fb7059543004f87059543004ee7219543004ed7219543004f67119543004f57119543004fa7019543004f97019543004bc7655143004dc7654d43005d87054d43005da70d0d43004f67118943004f57118943004ee7218543004ed7218543004be7419443004de7319443004ee7219443004ed7219443004f67119443004f57119443004fa7019443004f97019443004bf7650c43004df7650c43004f67198843004f57198843004ee7298443004ed7298443004f77159352004f
  | 20 => 0x4001802001c004000800000000f00180180060020098018012009006003408e000004801800202800000080740010028034006007004002000601101a800404400f007802805801501000680300210060000032005000005400a004004000800400b0000008002032002803000200900a0004084006000003c02a003006000400000f004fb7058f54004f87058f54004f67198b54004f57198b54004ee7298754004ed7298754004df7358354004dc73583540053d76d52540063d76d5254004ee7298e54004ed7298e54004f67198e54004f57198e54004f67198a54004f57198a54004ee7298654004ed7298654004ee7298254004ed7298254004f67198254004f57198254006e771d8954004ed71d8954006e471d8954004de7318954004dd7318954004f67118954004f57118954004fa7018954004f97018954005e57118954006ce7318954006cd7318954006e67118954004ed7118954006e57118954004e57118954006ea7018954006e97018954006e762d8554006e462d8554006e772d8554004f572d8554006e472d8554004de7318554004dd7318554004ee7218554004ed7218554004fa7018554004f97018554005e57218554006e76218554006e46218554006d67318554006d57318554006e67218554004f57218554006e57218554004e57218554006f27018554006f170185540063e65950540047f7655054004bf76550540069e5458c540069d5458c54004f67198854004f57198854006ce6398854006cd6398854005e57198854006e67198854004ed7198854006e57198854004e57198854006ce6358854006cd63588540066f5458854006ae54588540066d5458854006ad5458854004ef7158854006e67158854006e57158854004ee7298454004ed7298454006d66398454006d56398454005e57298454006e66298454006e56298454006e67298454004f57298454006e57298454004e57298454006d66358454006d56358454006e66258454006e56258454006775458454006b65458454006755458454006b55458454004f77258454006e67258454006e57258454006da6398054006d96398054006ea6298054006e96298054006f26198054006f16198054006da6358054006d96358054006ea6258054006e96258054006f26158054006f16158054006ba5458054006b95458054004ef7259353004ec7259353004f77159353004f47159353004f67198b53004f57198b53004ee7298753004ed7298753004fa7099253004f97099253004f67198a53004f57198a53004fa7098a53004f97098a53004ee7298653004ed7298653004fa7098653004f97098653004f67118953004f57118953004ee7218553004ed7218553004be7418153004bd7418153004ee7218153004ed7218153004f67118153004f5711
  | 21 => 0x4807400c00d0000014002013002803006a00200400080020100010034004005000809c01402800180740540010038004000000002801800200500180100300040020000036006001800c00200200100a4000005004803400000c0018004010008000000401c000006803800000100000b0016003000800400200f00580080100110008018004009006802001201b000806c00400a000000000800e000005001a015002000400e0080030004004000001009001a000001003000800000280000240000190018002015001805411c00f0020024020002000000001e000001000400e03e00a8000076001000808001c0000160004008002000800800c03400180a805c005003000400200000a801400000a0008000004053008002400802d004800c00000e0030000000000003000404401500000000080000020024000004000000c0020010000024000009000000800c0000108000014001000001c0020040030010012001000805c0060000038000006003002800001600f00100300080080008008000003000001007a00a000000c00200400d0004002000004800800800100e0008000006014000400c007002802400002b000800003a00b00000a8002000000006c008024000003800008d006800000402100180d0030004000000000e000009800c016009000806c00400500880080380030048014004002000804801e010005000000601700e801c00602f000000400000000680000000020000008002006000000400e001000000403801400500240080020008010002008001000c00001d00000080020010000000000007005800000a002005003c03401f002800002000100d80400060060068030000000001000000000b00a0020000006004800802a024000800000000300e00080000120248018000012002000000e009005801402c003000807000002700500000000250028014014004002001c024001000001c000003001800c00e007025806804c02e00200b40400000000000006000000803400600b004002000200201d80380000000008004008003013000000200101a00000000000080028002006001002800002d00100180000000008184008002000000400e0000038000002006000000800001000200c401400000180180000020058030002000004003401000000200000240000008070006001000800400603600c8070000008001800400001200b002c00400500a003401c036004802000200000100000100050118010000004006000c02000700680d8018000000017c012004001000400200700000080020020038008018005001005003200301b800004e00a0010044024011000802401600300101d4002001001800000801600280800040090018000012001000000001a00c00d800000c006000800000203d002005c00
  | 22 => 0x98aacc930001c355e600004630006a85ee68c994da040af36cb21cb02db53ea009127c0001c380014aec4320e1ec02549b55ba0cc03ac2070b09069a3cd8152400001140000002e34e140004048000ffe0000003141b3e0006c383540009820000000000baf23b951d2dc000519000029865c1d42d7c4ee000000000189c0004351a24000a4500000000000000000000000000000000124200000023fd8ac0000000b740002583f19b6800000020cb0ccf5c0005b0a508dc000000000012105f920b8000c9a0000000000fa4000000089d44c00024620ac65e0000000d91120758059a2a016ca514521ca47ac71239c0be916e9711e6b4e5a3a2060018002004000800000800f0060040010009000001002a000000003c024015008801c00200000300e0000003002802c000018005000400601000000480000000000024004012001800c0040050000000002000002001c004030001000001a003000801c00003903b021812a002002000c00e0020008004054005008010c004004006801400a000000022000602100a00100020010008000024001014804800001000b8068022000000002402e0120000014014010002002c00800000a80000020000050008016001008801400003f0000000000009007800c022018012000800a0000010168048001001804000000802a004401a00100280f802e0050020008034001002800001200e007801c002005000800000000000100a00020010010008028003005009c00000204c000000a00000000040000010000000066011002800c00c00701e8020044001000004402000900300580180160010034012000014000000000b00f000000000d001003400e0020000000000008016000003000005e805c02400301000140e40000000000022000004000000c008009003404a013000800000000000400a40000000050004006001000801c0000030048024006002004000003c00d00400240080030038030008009006800000a005000800000000700780480020450010034010001003804000200f001025001200d000805800600300100080020030000000012009009000001c003005800c016003000800000a00100e000400200100080200160060178004000018014011000c001012800c002000000000002001000000000020010168000004004000007c004001001002c000000003005c00002d00b800001a00a0018008024025006800800802300a801c028002005800c0120020008000010009003000400200300000240e003100000b000401500380040000030080008000000005800000201000080300300000260000006007001804400600200080bc03e0010000074002014000000000000200000100000090058014026006003818803201000000440000040000000008001001006000001700
  | 23 => 0x8b1338dec65610521600000000000001d0872c0005a9000061860200017053a60000c9235000087460836e9a409176d194440a088e4ed95c0300af65b436e1bce58005a280537aa4f58d0db917874d00000000003244c41ef58b0c1454511f95b4abe57193ad2e05e35bda7a043e0001c9974c8de0005b83669b26c3e0002a99a8e00d2c3af39b1400027f09d9666ad946320440c204c41daa25a8219b2b6000117035916a17ecc78af7631000c6d80c730e9bac1108041fb98a944a2ee000060526819f0ae204142415d17f8b24e60bb403607ac96e6c16410f3ca2604e32ba9c9b8c0814283711af256027c1e987147cd450863939a2d200020f0d7e3d7673a4192b80003ca89b44a06714668adc8860e200001d142c9a0460002133ac543cb8c80b5cb00322a980e0a9684c0b654fac00000001940000000000000eb8000453a3a1ba8445179048164c034000337cca09430002c6c000851000000063ca0f36016409ea49021c2f509c698e26f05b934a7b82571d2c9249dd34f26ec00062419a800000000000015240001553d62d6ca0a00000f245143ac5b1e32ae4f32d0f380327d2f058b3e3001565097330c88d5aaaadc40985d5b00a913330000a6ad32668a4f17faa751438001bcac05435a2280145506431304000000226076533ca2a1569a6c97e0776532d0988a3766b2029d66256a64bb7799ca43c654b0191e885b57a238c624c4b587a6f1b0605702d8a60c126bb6b930c40761842de07dc0008b3139058915e18340101881f4b970d890e43baab40000c4c288d521af91615740000000000cbecf35f28000620ac708c8eec000dd73438f317b810122530456c627800010d03f0b4c0001fe000099c476a95093cb276d49c6c0006d10000264000cb546523896ea0000df213901030f54599bc2fc3446770c546f435160aae1c98e0000000000000000068890186469800009f4000a5f541179447cb4d43300ac19e00025f000052e0000bd2d18a6cb1101f18493f03ee6638a844b496c1da31d4000345468aca98cc03268b0d31b7ea312630000e4200022910740001086a2000102cacd41a8681b206780000000432000000000905a5bf5bd320c3e65eb5b228d80000001a73428bd261f00010600000bc0258bf19f46c8184004539cd67681963997eab26ab8a3c12a7d3419000078855f38b331415c14936b28bd474919082128819a92e000179983c50a0cf0d6c9feda733627286e258a686289c47a9580b9888c5b06b06f483d8e541351f08bd4926d6b413b47081690e1f18e25b4a00000023484f40001532d5134c7bb000251442e01f52e0ca8aaa21129d09640b21651c089444de77a32c9f38eb26ee6b18dad56c6352c32ffc7526694340c34a7c49923e13a136ea9965423a8b4299b5fb1f9540ab41261043916855b0c11f
  | 24 => 0xac0ec4000100b76d22042a0002d1c6349746bf326436e6c20ca320473651862a9b90eb6575137095400058c3e380007be000000000000000000004e0326d8b00016c14ce0001270000000d534210001b78058000028cfd871e1e184ec5243250f38de0a5a1954cf830511240d0418d0081851b00018040001ee35207f9a2e46b0002df124e0002d5279918e0005b50000000200207800017c4ad355b201742aab31280000003b000000002200bd13081fc000a690002c581a82094fe857c00040a0920000372000000135135cc6d2d11acc614d7d4ac85783300e52bfb38869035724a8bccf8a3fa0000fc14e62136c31814000cd65cd015961c5440002fe122cb6258417240000004bf0b6c2c0c4766f0f740000d20399fc9308ced34036a81baa853630f69046ce800022202e4a6d3fb1fa44760000001feccce76a4173281088b2e16680000007344a398558927d71ad0478b2c0001428000f5232300027480001d53ce800000000026a9538b4e06f00000016e60000000000000000000044c000b902870fa4c70a842eb225c41652f2e8800159276c0002fbc7802ce272b00400000000005ad6684321e88a2d4cc1f1000000000087e5a20001164daf05da9fc2f6c63244a8a40188d90468d814365a063916c4d7c6e13b918b814008e1968f618100c842d19955ca22125832e16b41cf042219526c02030181ad55068500015040000004112254f740003a488e5966701000158ca5cad60d1254c5860000002f99b72b4e3d50e70fe22e06d7233d4b6000397b3dc3cca1e3abab84000a8d00b0b3110c1e50000658a64b800620000fb0010000196119083e00000000000003a82964000000000297800009b25a0001074a6303e8d056264f26602fa0ae8d255e988c801ea686e98c102808e75e685a0134dd237d14a5a3423313002751cad4904e00259de63e2cf177d52e4726702f499aebe91451ac4d54cf95e5a70c5222834c492d85de03c19e0001596c0d0558dcc2daa1c5672768000dd600031b93da6e309d184c07a000000095cb3e6af000000092ec686b99a9858a4364a7061c00063a10296b0000000000007131aab828a88fc39678500000013c600000aaeac3f80000002aec000a1105c00006ce00000000014340004c88bf4e882bb16b11700000000001014000747000165550237925301c937483d5ab809c04c31f234ae4d18600031fb2a955e2df00000000002d75fba3a40003423b487e4a168f64ee16480fc4623efaf68976add55690409920000e4ae9036a78d6d2370131866869e8278bdece96b42400dd4301462acd845028152c35fd7309671e2875cba470203415988906f849ab6c50707c83c72dbd08ec9126224c8bd03a56b61ff8214dad39891c18043e864706743785fe61b15c9370a65637abc99d6b5e2af1a8986a1
  | 25 => 0xc386b88af9872bd7575106ca72dcd30b8001b8a0003ad28ac7c82d900011753ec000131913ce66bdf41a02600002d3505800167c48400000d51981454fb91349523e00c6b4dd1182bf18591a1a36d2e4202f8969081459a92d441e7182558529898c2227e90e86f8d1510f1f2c00071153b81b95fe5f540db6758bc29e45d1f0c2300254aba60d7bcd2d2789ab47f62ea0001e900008a22ee91c51be0000001791566d4525ca62c1f0a28090a2b80f401314dae79722cd56af2f0943e3a22402c884444510919ed9b902e16608fb4dc4d6e60daea85269f24680ec82a82a5310373d3c26cf5bfa91d8603392001aa400084a3cb00014046842fb98bd2809de13a81458ba9b617322f55b01144fc80007400005258000c9600056a000130a39a1a30214970af85e01de442c24221f215c5ca1bd4cb800137e43f26187a977c0003f7279cfbad6a69617b08ac48a3f233b06a454b6ce182174a91c112a6bce566b52a01a3063a00000019dc000000065275827a00030c0b1d520d0b12697fca104461361a658fc38811c179c2febcc5b61a7d69e695000274400006a00000000000005a80b4546e000000000000000036f00007788872a60fb10920002d924a10e43f9682b648d22d092b38c5926ea1059e2fcd1a6c8c33b304834a04004496617b087862334849c01374b0a4b49f85e156fa54540eb2432615dcdd21ef5bf054970c8631c3310438acbb543175152c6295db95ad72c39857722e582c7a1541b5e091c31b34500010bcacc21703a00006064999ae9792ac62b0b1840ce19a39b89048c05fc1e100012a08f5473080d1d83e70002e080008961c294f0baa00016506256462b314d2205830a41455a35c4d22c16e8a1748768f85da9344bdaad5256000178c41136c0001992cab0001fdcc721a166c052124009400012f02164d36c89edcc1cd044ea0591b3668f64e800106062644a0000000c530001c913ca2dc00029c400000016800000004b14e30200dbe949105120d2a4af16220001aee73a00000000008bb3e62b0d246b5613280001a640e2e3207400052a60e9ae47a84643c313899e249163385e0164408201982cc8800029eaadc0aa95b3cfacdc4ac17949494b08b2000486000000010f516000147024c054aa0000000000027c46aab0b30d04581b8c8d09e0ac4720aa43239db4000b2c00005687f8a1821085b0cc274e1dab1294068fb0002518cc8ccc440000037600049300015aeb9248c05d8e780004610000980b073bf8a6400000000026cc000000026aeb8000cb2318077ca3433a292a550c947150000000ec676f3b309fc000743603afc4d2cbfb07610c196895f6d9a28ca04cdd52812594a4447010a4fd79e9b12892ce45ce00040d326c00086943d2dd87c47e739c83f05c6c3458a8c0c61c3f12e200012aad3c0002
  | 26 => 0x1a38e64c3c34e85383d086226e16ad494a0a20f0fd828448d445a6284cc6f72781a343204873daa68c2ce0000002f149a422d483a155a024d924e1f3d8848fd63887300006a714494700cc89d00023240000000568d2cf5600068c00000003624e29f291fc00040f9bccfb6d262fd2ff991675d4a61b40e3891110d8aac74c7f533cb1e843a8ad437332c694d602b10a88564ca444f96e9b1e2343139c2d71cabc32119398584d0233172862e33b55e93b02b22b00e510a59f67940dc27099ec568307b1c16faa5d4cb0da55b684868a0e8d3687203b5a7215f61d82da8ce0e50d000000000b3acca1e829251dcad122f984005008f400a1d5a701275c0a114c185996bb0f05b580003300eb4ef8da64f608a40009aa4c82038e2e7fc6f20f6c76ebd93b215b4000672580971524800035083858400ed2a123396f20000000000e820000001870bc0ac21b1a665a207716d835883c60fe4b511411b8ce3657076cb864fb2e695ec0004071d09624486cbc0369b2c7bc27b3e21e31812db753b07345081e43bc11e0204cea67fab4c8aa00053100000003c71ec80000002f90000000c62000000000077c2884c900001605b72669f0149c4ed2bc07810fe3b82e3abf01be00000000013e6b710d2000182eba80c8b5313006f4081b3640000006582d60000a6a5ce304c2d243519b8001aa21d26152b157d4000000000000010d1ab21586448cb59f800108c08b0001d595dabb80003170ce86dc3fe87c00e292517221902363753e10f209023ab0002f8046e000000365d946a4c0001f8800036a000271000c00033e916842025300000011bc7480f6a02cea614100036603d25852dc86a4fe015b3f400c0000d840a3825c00078f55087b00000005478dd000082600000a9b4200063480019300000001bfcc86b325460f9599a0000000001736000000374141202e000000000000000b80000000001ae9da038cc7d3cc265400083f00000006bc0001ce80014d86d3315a1b530eb295571d80a6800057332790c200059db5f1182a4254aad24be49a943e3445b92cf0038000160620c340a2601cc39e02119e83b44e706336d0174c5f5032c70000ab50002cc00004dd2aa20340002cb000188893e5910002ba561457960f94ad7ea42408e0a41b98a2309b3764b80dc318c88c486e00429822a5024d5f0001490f2074f6018249ad2bad64800001dc4232e41359972d080ee3090dca0000000dbd76c60458b92c94802b444980057ce50f1ca00b1108bd10251e2946800000c31aca442a7096945053e53b5220e0c00001d6aa1e68000b1d63236314260005e22b3d47e00032b1d791602d500022803a6de340611e937cd4f1dd37894a656f37d800128867f09132bc000d2b60724f5554b1432486a15461d135a2085b84a35096329d4e05c26e5b5196ee
  | 27 => 0xe80600025fc0008ef0489e44c2c0826a400006a06d71e9000145c00000031dc89cd4300000000009151bb86d1086a882c782887e62305f09b257b64426f00000bb689234100016f0879000335000088d00012e8c589b20660000b6843d27a00000006cd00003d52600005d88000be000028c800113856e4c98bd018ab9d63e1fcca4000039f84bc1420003cd80000005103ba1cd553eb3d5b3193dbc22246c280000008155f909880006c707882a15c8a170001b116044af58f00009489ee10a988ca0c12543b95e92bad29094002cb76be322da884000ae741410512ec3bf54a3665a9c59b4100fd47b88b11de8ec531e8f7642b65075e4e40e016f42606325e39bb5a26c9a667afb98d44134ad1ad85509d04bea0143883a40bbb5e881277d182ac949dc2f108484f90fa0e3043194501e2f759c2000a8a72643396b43740ea5b6a5dcc2249b214372890416339710495408be2e6068cd348394b689294281174c327609ae72d4d69575054da06cf377589a07c3fc9f70a948760cca9f58142f82ae145cdfa77b14680c45d29a83e082fd656dc106d08e85046f96a69e0973287363028343e811256230b4e1865a0d7914cb7c59c5d62a88088a193a617e0382cdc66416cda68c4055488f14dec573a8a0a4e761b35760910e2884106ba0cc45cc895fd11d17d67736ac919c8ea44046e92a9856c8f0b7ae0c8c63295359d7d96e5f335e24c56ba0c02a990056122b6543b1fc5905dc425a505b640ef5dd23c4db62c026c2cbce329c11939e8c84030212918a00007b30dfa6e4722b843619c2030c0001620001b5073623e8a316869e4611b1659586416999694252a932dc0240c6e02d2c69019b762ed5690338d5821a6a801e01e40005e506c154a0000000bc0d0615031e80014f681e4e3a0dc000cf2242a26998817d0000c180868c4000027c71a88314b1c38afa00033f000034cae05c49fa94406211b31bd8000000000000148617159d03e4aca2ac0681f5479c4ef0348df8a5053f0ea03fc1ce76e4160e3d2deb4b66302b08c2a243672ab116a05a6b7b570e7ad3632aaa498f0a332d186b00007880000c1cd50a9c05aa660bb40004959b9c4a800013cb1496300000000af11b6d5b0000fac2a20000000fd0cc4000123800064c1aa3dfa7e996c26400031b151cd2f3d42f58910c0402280010a627161780011accfd54eb7700000005d99c680000000000bf83100db36ab5999240003c98eb8000000000000197c0001f7ae98000a9a0be27658f214d5e0973986e00033d9e1c7002e800019f0b0827c45b181d29a6e84e6309c0006ae3c9165d8a205346c07fc00e46569a9294de04ea6d5907cb6c0365539978b52da206183604e03c96aea9852760cb3b0915d3e078b14e81ecf1229451f1ed1b7c05441880000002b564e25c945a0a5482
  | 28 => 0xc9e04000675212a7ad59489b61724e8afcba0376000035c03a606000000000038e8000612c0f4b1000000012b27b139828675260e2c7c9665a41971950d6e1260862d1435a8a55b38915b04d0d4e491b80900aa32309a96ca709125a4055d0c6544f06c971034347c800000091b000153d030af50fb000000078445506d8ad2cd33b2a53cae22f64d237612240de000000194a7070b817f4622d2a32e8a71a7e0790001699a50b20000140c00000054d80012127765fe000071c0002c400000007770000000000b530971af53345161bf87e82e8b0d42a00000000004f13228d2e8915a8a9e86e07a209c9f81bcc6a3324132cfde11d6398ff40005460f924140721853ed2594bb04a8198b5692d6a4d00c94995d69cb3e8065c6b0a7c4038708dea7bc0720740ca463448d063d778b6e15502dc4927061e58b88c76b061a685594c80605d19e815c422662d3340888049438a6894f27eb014821ca1a7255021d51b7a9ef33708ac27e9f504983cd35638c60cac64fe8b6069f1b986e44f31a7a58068ed0715c3639984d8d18e2064d2611f3d92f5439c3361a9b52801c4025dc9ae0a3cb9535280000003e62fb000000000047d000000055869d06282aea30000355800000000012813c0000000136c000537151960c0001de3c02428000bf46ba92199429ff10e0001472cdb0002dc906c531075960805ebed1763258708ac063a00010dec4801f80493bea3c43600000003d33502cb4630ab143d8000000000000313d6b8c8407d8e48222ade00000000005ea0000e5d3e874a154b1ed39e14f15719ad2721a73069bbd2c6a151b6a4b1a8022c5d10975418d704eab5088960001940721a0cd894af0b6800034919f9c7d4ac6330000b18a4e88f274b6d8192b94000182970a93807a00010b200053c0000942d612f1006800097508d22087540000232ea52cc0c23791534a182c25fc83f4ff44a300014e00005de019856134e20e3df23694763ff199923cd641003ba9900c2881c6872d00000afa4b200011e08e100004c800084d02eb384e8a44928e87d498ab0c202176541061b21896bc46c05c3f0a1300003653960000930000000148d5f22bd13f04188fe24627b91e400090d02f3220cb649a6ba247c54000040b800000000000018d80001fb00000010e000025eb6209c2063058ae3c00042733980007668f21150c5000033d14300006b8000099a264d0c00027d000073ed30283800125e8ac1023658aec000656a9b95820965829ebcbae41503b06acf3c5523919dc0d3842b01b800038685819f275db9c1462be1cf85d6cf446ab0a198682f65d133c7f019c4a430fc6d000000000000000001990c8525497a54c35ec4405cf0000000000dc700011046584764e026c00005480f0b0847fc0475ac9d002cc00000025a5a6228014aa9f921
  | 29 => 0x1c896088605ee8000be2b8c57789a0fbcbec5df929c4e859448f1d9c85ea220000000000b5500003a40000001800e54efcd2263b0a380442de5b588bd5face40001401716521401937d2f669445327f0df80413d680000009020002f20000cce3c19b300000002168b3cb960005a5041cf4e0d942fa83959000005ca7a8a0825c69d8e6400000036a0000000d24578092079426b1c12b40a3e14b48e8290a02d4b5b4a9d13587b124590596428fc3a32afcae6cf860d1a21a3e72750003dc43049d4ca14247aacf56690808dba68b2abae28f388e022f1c3cd942fb03a893c8e675500a33f000092215d0820ab24c845f819099438b0b523cc0007d93318d85226cda0fea52c00066d4279bc475882500010980007ed3dcac40c5a000673097dbaa0d60290fc800018c61d8ed8000690442974000054347213315fc5930f1255874e0002672ef466871064ab0993d27d15e810893fcca2000000101400000000000000005f2000000005f00000000007043e4a40c6fa67000030948da4940000001a460002cd3769bd0d65523084921625b389ae9d9fcbb038194cd62400010a2fc19628eb2353448b505640a999a93f65f40702148572a5561d000192855a12f377d87a4546ac10cd53c0f04be209147a46c152006caa2d6d01c13e5a4e2af23d80012949796058fa93424da0001b48f4acbd5e180014b460000004c426861e00009cd76400034900018521c742e013c22a000011800041a6fe5ddae7c0006c5000000014c0001d
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xd61754843088001b42e89086110003b058d210c22000563c1aca90a4000ac483595214800154d0832a4290002a9610654852000563418ca90a4000ac583195214800158d073224290002b160e6448520005e141ee090a4000ce0764855048001b80e690aa09000278e1d2190120006703b242a024000ce27648730480018b2eab186090003525d5320c120006c4ba26418240009e3874843048001ac2ea9086090003685d1210c12000760b1a421824000dc273487204800158d073124210002b160e624842000473438ca9084000aa684195210800154b0832a4210002b1a0c654842000562c18ca9084000ae28019521080011cd0fb22421000299a14644842000532c28c89084000ac683191210800158b063224210002b8a00644842000571406c690840008e68718d21080014cd0a31a421000299614634842000553420c69084000aa58418d210800158b0538cc7880033158d72947100062abaac620e2000cc5635c841c40018caeab108388003315cd62107100056341ec490e2000ac583d8921c400158d063124388002b160c62487100056341eca90e2000ac583d9521c400154d0832a4388002a9610654871000563418ca90e2000ac58319521c400158d07b224388002b160f644871000533428c890e2000a658519121c400158d063224388002b160c644871000553420ca90c2000aa584195218400158d0632a4308002b160c65486100056341cc890c2000ac58399121840014cd0a31a430800299614634861000553420c690c2000aa58418d218400178507b824308003701cd21542100062cbaac61842000d61754843084001b42e89086108003b058d210c21000472c0ce432a20008e5819cb64440011cb03390c688002b1a0f764851000562c1eec90a2000aa6849d9214400154b093b24288002b1e0d65485100056241aca90a20008e587195214400154d0832a4288002a9610654851000563418ca90a2000ac58319521440011cb0fb224288002b1a0e644851000562c1cc890a20008e58718d214400178507b824288003381d92154110006e039a42a8220009e38748640440019c0ec90a8088003389d921cc1100062cbaac61822000d51754c43044001b22e8988608800278e1d210c110006b0baa421822000da1744843044001d82c69086088003709cd21c411000472c14e232820008e5829c764040011cb05388c608002b1a0e614841000562c1cc290820008e687195210400154d0832a4208002a9610654841000563418ca9082000ac58319521040015c50032a420800239a1f644841000533428c89082000a6585191210400158d063224208002b160c644841000571400c89082000ae280d8d21040011cd0e31a420800299a14634841000532c28c69082000aa68418d210400154b0831a4208003385d92184010
  | 1 => 0xacba9a42180027161c534843000562c30a69086000e456514d210c00170b0829a4218002f06005348430004e2c3c869086000ac58690d210c00198aed21a4218003915964348430005e0c04869086000cc57650d210c001c8acaa1a4218003a1991434843000570c34e09086000e61659c1210c001743093824218003a85927048430005e0c1ce09086000ce3765c1210c001cc2cab824218003a85917048430006e0b9ae09086000a5986d4f500c0018b2eda9ea018003385d921d403000730b2a43a806000f4353487500c001872caba0a01800316595731403000634b2ae42806000c71655c4500c0013c30e908a018003385d9211403000730b2a422806000da174484500c001b82e6908a01800316595739003000634b2ae52006000c71655c6400c0013c30e90c8018002b8619219003000670bb2432006000e6165486400c001b82e690c801800386595435003000744a1ac4a006000e9143585400c0015c30c90a80180039859521500300075132242a006000f8143485400c001c8aca90e601800398595218c03000663bb2429806000e4565485300c0019c6ec90a601800398595214c0300046cc34ea9806000999841d5300c001393043aa601800274604754c0300052cc34ca98060008d887595300c0018b0eab2a601800316dd9654c0300062dc3aca9806000c5887595300c0018b2cbba260180027260b744c030004e8c0ee89806000c59655d1300c001c32cb322601800386595644c0300062cb2ee49806000e4965989300c00178303312601800392595624c03000744b22c49806000c5965dc5300c001ca2cb30a6018002f060a614c03000728b2ac29806000e9164585300c001c92cb90a601800394596214c030005e0c14429806000e4965485300c001b86e290a601800394595214c030006e1b92429806000dc287485300c001b830e90a6018002f0e19214c030005e0c32429806000dc376485300c001d86ec90a6018003709d5214c030006e03aa429806000ec365485300c001e84ca90a6018003b0595214c030007a0b2a429806000e4165485300c001b86e890a6018003705d1214c030007c1322429806000f8164485300c00158b03394c7900033158d7194b2000626baac62164000cc5635c442c80014cb0a212c390002b160c42587200056341eca90e4000ac583d9521c800154d0832a4390002a9610654872000563418ca90e4000ac58319521c800158d07b224390002b160f644872000533428c890e4000a658519121c800158d063224390002b160c644872000553420ca90c4000aa584195218800158d0632a4310002b160c65486200056341cc890c4000ac58399121880014cd0a31a431000299614634862000553420c690c4000aa58418d218800178507b824310003701cd21542200062cbaac61844000
  | 2 => 0xf644863000472c3ec890c6000b85849cd218c001c8acba9a4318002f06035348630004e2c38a690c6000b858414d218c0017830029a43180027161e4348630006e039a42a846000f4353485508c0011cb03390ca980023960a711953000472c0ce5b2260008e5829c7644c00158b07bb24298002b8603764853000553424ec90a6000aa5849d9214c00158f06b2a4298002b8e01654853000473438ca90a60008e587195214c00154d0832a4298002a961065485300047343ec890a60008e587d91214c00158b073224298002b8602644853000563434a690a6000ac48654d214c00178100a9a4298003389d92194130006703b242a826000dc073485504c001e82a690aa0980023960672d943000472c14e3b286000a1d841cd650c00149b0439aca180029560473594300051cc20e0b286000a69821c1650c0014e302382ca1800239606721943000472c14e232860008e5819cb640c0011cb0538ec81800239606721903000472c14e23206000c1d655d0530c00189acab90a618003155957114c300062cb2ae02986000c4d655ca430c0018aacab8c8618003165957090c300063332ae33106000c65655c6620c00194cc8b8cc41800329591719883000670b8ce13106000c59655c3320c0018cccab94c21800319595729843000653322e53086000ca5645ca610c0019c2e5384c2180031659570cc43000722b2e629086000e8564cc5210c0017830198a421800331dd9314843000722b2a629086000e85644c5210c001c8acb9924218003a15933248430005e0c06649086000cc7764c9210c001c8aca9924218003a159132484300066341eec9086000ce280dd9210c0014cd0b3b2421800299616764843000553424ec9086000aa5849d9210c0011cd0e3b2421800299a14764843000532c28ec9086000aa6841d9210c00154b083b2421800239a1f654843000472c3eca9086000aa684d95210c00154b09b2a42180029961a654843000633bb4ca9086000c6576995210c0018ceecb2a4218003195d965484300072241aca9086000e6080595210c0011cd0e32a42180023961c654843000533428ca9086000aa684195210c00154b0832a4218002b1a0c654843000571400ca90860008e687d91210c0011cb0fb22421800299a17644843000532c2ec89086000aa586991210c00194eed3224218003295da64484300071332cc89086000e2565991210c001d0d073224218003a8a02644843000653bb2c89086000ca576591210c001c4ccab22421800389595644843000473438c890860008e587191210c0014cd0a322421800299614644843000553420c89086000ac5869cd210c001c8acb39a4218002e1612734843000742b24e69086000bc1809cd210c00198eecb9a421800391595734843000742b22e69086000ac586d4d210c001c8
  | 3 => 0x232e80008e5819ca63d00011cb0538cc7a0002b16067298f4000562c14e331e8000ac6839d921d000158b073b243a000299a14764874000532c28ec90e8000ac6831d921d000158b063b243a0002b1a0f654874000562c1eca90e80008e68719521d00011cb0e32a43a0002b1a0c654874000562c18ca90e8000ca5761d121d000164b0a3a243a0002e160c74487400071332ca890e80009a48755121d00011cd0f31a43a00023961e63487400066343cc690e8000cc58798d21d0001d0ee8b1a43a0003a11d16348740007432a2c690e8000e855458d21d0001d0cc6a1a43a00023960672d964000472c14e3b2c80008e5819c865900011cb05388cb20003319cd7198a4000662b9ae33148000ce1719c2629000198ce6b94c320003315cd729864000670b94e130c8000ac683985219000158b0730a4320002b1a0e624864000562c1cc490c8000ac683dd9219000158b07bb2432000331a0f764864000662c1eec90c8000ce280dd921900011cd0fb2a43200023961f654864000473438ca90c80008e587195219000158d0632a4320002b160c654864000671bb2e090c8000ae1864865090001990e6b12a120003341cd615424000570c3242a848000dc073485509000154f0c90e8120003709cd21d024000472c08e4b2a80008e5821c565500011cb03390caa00023960a71195400056341eec90a8000ac583dd921500011cf0eb2a42a00023921d654854000563c1aca90a8000ac48359521500011cd0e32a42a00023961c654854000563418ca90a8000ac583195215000194aec3a242a0002c96147448540005c2c18e890a8000ba2801d121500013490eaa242a0002a92195448540005d14068690a8000ba2849c121500015c10cb8242a0003681d17048540006703b242a828000dc0734855050001b84e690e80a000269e1d219014000472c0ce432880008e5829c465100014cd0a3b2422000299614764844000563418ec9088000ac5831d921100015c5003b2422000239a1c654844000472c38ca9088000aa684195211000158d0632a4220002b160c654844000571400ca90880008e787486601000194eec90a802000338dd9215004000472c0ce432e60008e5829c465cc0011cb03396c9980023960a71d933000553424ec90e6000aa5849d921cc0011cd0e32a43980023961c654873000553420ca90e6000aa58419521cc0011cd0fb2243980023961f6448730005e0402a690e6000ba1849c121cc001cc2ca90ea198003705cd21d4330007a0a9a43a8660009e18748450cc001b42e8908a198003705cd2114330004f0c3a4320660008e5819c8658c0011cb05388cb180023960672d923000472c14e3b246000aa6849d9218c00154b093b2431800239a1c654863000472c38ca90c6000aa684195218c00154b0832a431800239a1
  | 4 => 0x4840134b0939ec09080361a1273d8121006c2c24e7b024200cc7655cf604840198acab9ec0908033199173d812100662322e7b024200cc67358f604840138d073a4c0908027160e7498121006c341ce93024200d85839d26048401b45013a4c090803299d36098121005e141ec130242009a6841d5604840134b083aac09080271a0c7558121004e2c18eab024200aa48459560484014cb0a322c090802b160c645812100571400c8b024200ae280d8d604840178507b02c090802a9a12605812100473c3ac030242009e387580604840154d0832a4210802a9610654842100563418ca9084200ac58319521084015c50032a4210802b8600654842100533428c89084200a6585191210840158d063224210802b160c644842100571400c89084200ae18019121084015c501b1a4210802b8603634842100472c08e4b26a0008e5821c564d400154f08bb243a8002a9211764875000553420ec90ea000aa5841d921d400158d063b243a8002b160c764875000473c3ac890ea0008e48759121d40016c100a9a43a8002b1a0e614865000562c1cc290ca000ac683989219400158b073124328002b1a0f764865000562c1eec90ca000aa6849d9219400154b093b24328002b1a0e644865000562c1cc890ca000ba1849c121940011cb03390c6a80023960a7118d5000562c0ce431aa000c8d745c8635400158b05388c6a8003255d17118d500056341eec90aa000ac583dd9215400154f08bb242a8002a9211764855000563c1aec90aa000ac4835d921540011cd0e31a42a80023961c634855000553420c690aa000aa58418d215400198d0e31a42a80033161c634855000743420c690aa000e858418d2154001d830031a42a80039118f5348550005d0c24e090aa000ec0639c121540015c10cb8242a8002d821570485500076031ae090aa000ec063487505400194cc8b8cc4280032959171988500066331ae3310a000cc5635c6621400194cc8b94c2280032959172984500066331ae5308a000cc5635ca611400154d093b24228002a961276484500056341cec908a000ac5839d921140011cd0e3b24228002a9a10764845000552c20ec908a000ac6831d9211400158b063b24228002b8a00764845000653bb4c8908a000ca576991211400194eecb224228003295d9644845000663bb4c6908a000cc57698d2114001d0cc931a4228003a1592634845000663bb2c6908a000cc57658d2114001d0cc8b1a4228003a1591634845000760402c6908a000e456348750140015c30c90ca028003a8591219405000760b1a43280a000c67764855014001c8ac690aa0280032659073540500066439ac4a80a000cd07358550140015c30c90aa02800338dd9215405000750b2242a80a000dc0734855014001d82c690aa02800239606721974000472c14e
  | 5 => 0x80269e117654d21004d2422eca9a42009e3805d953484013c100bb2a690802e16126354d21004e243ac6a9a4200b448558d53484011cd0c382a690802396187054d21004d3420e0a9a42009a5841c153484019c50c382a690803386187054d21006d1420e0a9a4200da1841c15348401b84c6382a6908037058c7054d21006e1a98e0a9a42009a684dd8534840134b09bb0a69080278a037614d21004f0c06ec29a42008e5879d853484011cd0c3b0a69080269a107614d21004d2c20ec29a42009c6831d853484013c5003b0a690802786007614d21006533b4e829a4200ca5769d0534840194cecba0a690803295d97414d2100662bb4a629a4200d857494c53484012cf0ea98a69080271e1d5314d2100662bb2a629a4200d857454c534840178100a98a690803389da7014d2100670bb4e029a4200da2749c05348401b42e9380a690803389d97014d2100670bb2e029a4200da2745c05348401b42e8b80a69080358d4d7014d21006e129ae029a4200d61535c05348401b82a6b80a69080278a0376d0d21004f0c06eda1a4200966851db43484012cb0a3b6869080278a0076d0d21004f0c00eda1a42009e280dd743484013c301bae869080239a1875d0d2100472c30eba1a42009e2801d743484013c3003ae8690803295d864d0d2100592c28c9a1a4200ba1801934348401a4ceb2a68690802a921954d0d2100473434e1a1a42008e5869c343484019c50d38686908033861a70d0d21006d1b22e1a1a4200da0645c34348401b44a8b8686908036855170d0d21004f1404ed21a42009e1809da434840198d073b4869080338a027690d2100670c04ed21a42008e686dd643484011cb0dbac869080239a187590d2100472c30eb21a42009e2801d643484013c3003ac8690803319d96390d2100662bb4a721a4200cc57654e434840178100a9c8690803299db4390d21005e14068721a42009e2809d943484013c3013b2869080239e197550d2100472432eaa1a42009e3805d543484013c100baa869080239a187550d2100472c30eaa1a42009e2801d543484013c3003aa869080269a1f6450d2100652bb0c8a1a4200b2585191434840170d063228690802e86006450d21004d243aa8a1a4200aa486551434840170d0931a86908027121d6350d2100742322c6a1a42009c48754d434840178100a9a8690802f0a034350d210055343486a1a42009a684dd843484012cd0a3b08690802596147610d21004e3418ec21a42009e2801d843484013c3003b0869080239a187510d2100472c30ea21a42009a6841d4434840138d063a8869080278a007510d21004f0c00ea21a42008e6869cc43484011cb0d398869080269e1d4310d21004e3c3a8621a4200aa48459760484014cb0a326c090803295d064d812100562c18c9b0242009a6849cf6
  | 6 => 0x592422cbaa24200ca576d93544840164b0bb26a8908038959764d512100653bb0c9aa24200b25851935448401c4cca326a89080278e0173d5121004f0402e7aa242009c7835c3544840138906b86a89080271a0c7695121004e2c18ed2a242009e2801da54484013c3003b4a890802c9a166495121006523b2c92a24200b2587d525448401a4b0faa4a89080239a1a739512100472c34e72a242008e6869c254484011cb0d384a89080239a1a7655121004d3c22ecaa242009c6831d9544840138b063b2a89080278a007655121004f0c00ecaa242008e6871d954484018cb0a3b2a89080329610765512100663418ecaa24200cc5831d954484019c5003b2a890803386007655121006323b4caaa2420096487595544840134d0f322a890803291da64551210071332cc8aa242009a4875915448401948ecb22a890803895956455121006523b6a8aa242009c683dd8544840138b07bb0a89080278a037615121004f0c06ec2a242008e5879d8544840194908bb0a89080239a187615121004b3428ec2a242009a6841d8544840138d063b0a8908027160c7615121004f1400ec2a242009e1801d8544840134b0fb20a890803295db6415121004d2c38c82a24200ca576190544840164b0a320a890803195db541512100652bb4a82a24200d267595054484012cf0eaa0a890803195d95415121004d3c3aa82a24200aa486550544840194aecaa0a890803319da731512100662bb4e62a24200cc6765cc544840198aecb98a89080361d917315121006c2322e62a24200d86545cc5448401b0aa8b98a890803389da701512100670bb4e02a24200dc2739c05448401b82e7380a890803389d9701512100670bb2e02a24200dc2735c05448401b82e6b80a89080368d917015121006d0322e02a24200da2545c05448401b42a8b80a890802a921165d8d2100532c28c9b1a4200ca57419363484015c300326c69080269a1270d8d21004d2c24e1b1a4200da2849c36348401b4309386c69080338d9570d8d2100670b2ae1b1a4200ce2645c363484019c0c8b86c69080278a027498d21004f0c04e931a4200d86839d26348401b45013a4c690803686027498d21006533a6c731a4200bc280d8e634840134d083aac690802696107558d21004f1400eab1a42009e1801d5634840154908b2ac690802996146458d2100563418c8b1a4200ae180191634840178501b1ac690802a9a126358d2100473c3ac631a42009c78758c634840134f08bb6a6908026921176d4d21004d3420eda9a42009a5841db53484013c5003b6a6908027860076d4d2100473c32e9a9a42008e4865d3534840134d09bb4a690802696137694d21004f1404ed29a42009e1809da53484013c5013a4a690802786027494d21005c2c24c729a42009e2809d953484013c3013b2a69
  | 7 => 0xe180dd6324840134d083ac649080269610758c921004f1400eb19242009e1801d632484013c501ba4649080278603748c921004b3428e91924200965851d232484013c5003a4649080278600748c921004f1404ec99242009e1809d932484013c700baa649080278201754c921004d3420ea99242009a5841d532484013c5003aa649080278600754c921004f1404e899242009e1809d1324840178501b9a6490802f0a03634c921004e243aa69924200bc08054d324840158d0d21a64908027121d434c92100473430ea19242009a6841d4324840134b083a8649080271a0c750c921004f1400ea19242009e1801d432484011cd0dba0649080259a14740c921004b2c28e819242009c6831d032484013c5003a0649080278600740c921004d3424e7b2a42009a5849cf654840134d09386ca908026961270d9521004f1c02e732a42009e0805ce654840138f06b84ca908027120d7099521004e3418e8b2a42009c5831d165484013c5003a2ca9080278600745952100653328e8b2a4200d86831d16548401b0b063a2ca9080368a007459521006d0c00e8b2a42008e787594654840154908b28ca9080259e1d651952100653b2ae832a4200d26655d0654840194acaba0ca90803495957419521006c33a4e632a4200d85749cc6548401b0ce8b98ca90803615d1731952100663b2ae632a4200cc5655cc6548401b44e9380ca90803685d27019521006e139ce032a4200dc1739c06548401b44e8b80ca90803685d17019521006e139ae032a4200dc1735c065484019c6cab80ca9080338595701952100552422cbb224200c6575996644840154b0932cc890802a9610659912100562c18cb3224200ae180196644840138d063aac8908027160c7559121004f1400eab2242009e1801d564484011cd0fb2ac890802a92116559121004f1406e6b2242009e180dcd644840138d07b82c8908027160f705912100692422ea32242008e58799464484018caeb328c890803195d4651912100552c20ca3224200ac58319464484015c300328c890803195d7641912100552c34c83224200d257599064484011cf0eb20c890803195d56419121004d3c3ac83224200d2575590644840154f0eb20c89080329e1d64191210055242ac83224200e2675590644840194aeab20c890803895d5641912100612baac83224200aa783590644840154f00b20c890803519d67319121006a2bace63224200e85649cc6448401a8ceab98c890803515d5731912100742b22e63224200d62759c06448401ac2eb380c890803a85927019121006e139ce03224200dc1739c06448401ac4eab80c890803585d5701912100750b22e03224200dc2735c06448401b82e6b80c89080271a0c76d5121004e2c18edaa242009e2801db54484013c3003b6a890802c9a1265d51210
  | 8 => 0x13b2629080278e01754c521004f0402ea98a42009a6841d5314840134b083aa629080278a00754c521004f0c00ea98a42009e2809d131484013c3013a26290802f0a03734c521005e1406c698a42009c48754d314840178100a9a6290802b1a1a434c521004e243a8698a42008e6861d4314840134d083a8629080269610750c521004e3418ea18a42009e2801d431484013c3003a8629080239a1b740c521004b3428e818a4200965851d0314840138d063a0629080278a00740c521004f0c00e818a4200c3575590644840138d06392a8908027160c7255121004f1400e4aa242009e1801c954484013c501394a690802786027294d21004f1404e521a42009e1809ca434840134d083b6a4908026961076d4921004e3418eda9242009c5831db52484013c5003b6a4908027860076d492100592c20cba924200d2674d5352484014c90caa6a49080278e0173d4921004f0402e7a9242009c7835c3524840138906b86a490802c96106554921004e3418e8a9242009c5831d152484013c5003a2a490802786007454921006533b2e82924200d26755d05248401b0ce9398a490803615d27314921006633b2e62924200d86745cc5248401b0ae8b98a490803689d27014921006d0ba4e02924200dc2739c05248401b82e7380a490803389d97014921006d13a2e02924200da1745c05248401b84e6b80a490803705cd7014921004b3428eda124200965851db424840138d063b684908027160c76d0921004f1400eda1242009e1801db42484011cd0c3ae849080271a0c75d0921004e2c18eba1242009e2801d742484013c3003ae8490802c961464d0921006933aca9a124200aa48655342484011cd0dbac849080271a0c7590921004e2c18eb21242009e2801d642484013c3003ac8490802392197550921004e3418eaa1242009c5831d542484013c5003aa849080278600755092100553436e8a124200b258519142484013490eaa28490802a92195450921004f1406e6a1242009e180dcd424840138d07b8284908027160f7050921004e341eea21242009c583dd442484013c501ba88490802786037510921004b2c3cea2124200c66765d442484011cd0c3a8849080259a147510921004d3420ea21242009c6831d4424840138b063a8849080278a007510921004f0c00ea2124200d25759d04248401a8ceb3988490803515d67310921006a33aae62124200d45755cc4248401ac4eb3808490803585d67010921006e139ce02124200dc1739c04248401ac4eab808490803585d57010921006e139ae02124200dc1735c042484011cd0c3ae649080269a1075cc921004d2c20eb99242009e2801d732484013c3003ae649080239a1b74cc921004f1404e999242009e1809d3324840178501b1e6490802f020153cc921004f1406eb19242009
  | 9 => 0x621063100670b12e020c6200ae182945608c4014e30a20ac118802b8608415823100616baac82164200c2d7559064c840194ac8b88c990803495d541107210061abaac820c4200c3575590648840194ac8b90c910803495d54210a2100516c28c8a124200a3585191414840185aeab20c89080271a0c7155121004e2c18e2aa242009e2801c554484013c30038aa89080278a027194d21004f0c04e329a42009e2809c643484013c30138c869080269a1076d4521004d2c20eda8a42009c6831db514840138b063b6a29080278a0076d4521004f0c00eda8a4200b25841975148401a4ce9aa6a2908029921954d4521004f1c02e7a8a42009e0805cf514840138f06b86a2908027120d70d452100592c20caa8a42009c6831d1514840138b063a2a29080278a007454521004f0c00e8a8a4200ca6765d05148401a4ceaba0a290803619d27314521006c2ba4e628a4200cc6765cc5148401b0ce8b98a290803615d17314521006d13a4e028a4200da1749c05148401b84e7380a290803705ce7014521006713b2e028a4200da2745c05148401b42e8b80a290803709cd7014521006e0b9ae028a4200966851db41484012cb0a3b6829080271a0c76d0521004e2c18eda0a42009e2801db41484013c3003b6829080239a1875d0521004e3418eba0a42009c5831d741484013c5003ae82908027860075d052100592c28c9a0a4200d267595341484015490caa6829080239a1b7590521004e3418eb20a42009c5831d641484013c5003ac829080278600759052100472432eaa0a42009c6831d5414840138b063aa829080278a007550521004f0c00eaa0a4200aa686dd1414840164b0a32282908026921d545052100552432a8a0a42009e280dcd41484013c301b9a829080271a0f7050521004e2c1ee0a0a42009c683dd4414840138b07ba8829080278a037510521004f0c06ea20a4200965879d441484018ccecba8829080239a187510521004b3428ea20a42009a6841d4414840138d063a882908027160c7510521004f1400ea20a42009e1801d44148401a4aeb3a08290803519d67310521006a2bace620a4200d46755cc4148401a8aeab988290803589d67010521006b0bace020a4200dc2739c04148401b82e73808290803589d57010521006b0baae020a4200dc2735c04148401b82e6b80829080239a1875cc521004d3420eb98a42009a5841d731484013c5003ae62908027860075cc52100473436e998a42009e2809d331484013c3013a66290802f0a0363cc521005e0402a798a42009e280dd631484013c301bac629080269a10758c521004d2c20eb18a42009e2801d631484013c3003ac629080278a03748c521004f0c06e918a4200966851d231484012cb0a3a4629080278a00748c521004f0c00e918a42009e2809d931484013c3
  | 10 => 0x320100480001000c00812048000078150000200000000402c000020000000000d00007000000004010028050000180080002c02c00809010008000050100080080707e00c01001016000008160000040081c0020080000000804c0100f0000240d80a00402c0000102c000020000040480080100201401001002004058030000100000b0000000000300e0140000900c000020010060000000001a00c030000000180000000c0001100a0000000000d01000c0101400a000000030060600180800601400000000000000050100080181d0000100000600400c0180102e00008002396067298e5400472c14e331ca8008e5819ca60950011cb0538cc12a003319cd711895400662b9ae2312a800ce1719c06255001992e6b80c4aa003385c570189540066339ae430aa800cc5735c861550019c2e5380c2aa003345cd701855400670b92e030aa800cc6635c6621500198ac6b8cc42a0033198d729845400662b1ae5308a800ae18198a60150015c30530cc02a002b8606625805400570c14c2b00a8008e5811c964d4c011cb0438ac9a980239606721815300472c14e2302a600ae1819c86054c01952e8b90c0a9802b860a711815300658ba2e2302a600c99641c15314c0194cc8b8cc42980329591719885300564402a6b10a600ca6645ca6114c0194ac8b94c229802b4201535845300570c0cc5300a600ae1829866014c015c303312c029802b860a615805300472c0ce432e86008e5829c465d0c011cb03394c1a18023960a719834300570c0ce53068600ae1829c660d0c011cb03396cb218023960a71d964300472c0ce432c86008e5829c46590c019c2e3384c521803385c57098a4300564402a6b148600ce1729c26190c019c2e4b84c321802b4201535864300472c08e4b2a86008e5821c56550c011cb03390caa18023960a711954300472c0ce432886008e5829c46510c0154b09392c329002b160e725865200570c04e4b0ca400aa5811c9641480194ac8b8ca4290033158d719485200570c0ca4b00a400a65859c9619080149b06392ca2100299604725944200534c00e4b288400ac5819ca631080185acaba0a42100313595731484200632b2ae22908400c69655c052108018cacab8c8421002a9610525844200562c18a4b088400ae18014961108014cb0a212c319002b8600425863200570c0ca4b046400a6985109608c8015c302212c119002a96127158a5100562c1ce2b14a200ae1809c5629440154b0438ac82880329591729445100662b1ae5288a200ae18294560144014cb0b38ac5208029560c715944100532c10e2b288200a71801c5651040158b0538cc6208030d59574144410062ab2ae62888200c65655c8511040194ae8b10a220803315cd621444100638b2ae02888200ce1625c051104018cacab948220803195d5
  | 11 => 0x6a0c47412008264a25a3626728dc6b47704683ac00010c0000000000000000001cc000aba4ee4de73a58053e1ce0001a697a85a9c82161f2000b36a3856c7ec0005320003f839262a1343f08ce796000598a7aa24b9200000068a332a926622108260000000006fa000104b8c000000a1e8480c600000000032e77e7ba000a804b44965ac5b03c40ce33a7da000744ad258224e1c09383b495a73e5444e21f60769c05049ba5960fe000000b0871e0000008902de278356b9e6b20004860000000003960003c095407c40a82a7fa5fe9fc8ca000ab445e0681061e00009240004d85aa5c890ea6c6609560003e419c5b40000000001385424d09483a48aa1aa06a4fe74cb1820462231e1f063657c0786c252ca2634241a61418c0008981c8000baa00036e0741da7368629ae91651a2a23fc4e40006b043802e000000b2c10e0005a64ce32269459226a58e8161b62ca0006ae51c1c27c27a86f496888a3080000003b89f421c8e452680401a000a5a83415eaac85200049800a44800000052275e8dea745300007e26780000008c655875c00000093000000030a0009b814e548b441106388f87a45c24be45aa648305ea83a93c002742266460a982526c01b438466a466ba49fa7b03ea6d0a0626c324aa65ba8fc0000001ee2dc99600088476e96a37e59a41040e8fab520969da4063a62c80002240000000000000000000000000ca41e0007669be6a67e89bc32816016a7223a0000952000ac080a29a68e000000000218000000ac8000a2aae02b800604c0000700401400000002010018000320080000100c0000001a0020000000200e08802000030004060160220000b00400a0080680000c004020000120001a8000020480000b00000c0000e00000c07829006020020160200000300001c0240300900a0000280a0000340184002a00c1700600e000030000100000300401c000000010180000000500800000032000010000030020240c00100609c0001a002058000020060000380600000c0401800c004028000060480180400001800006002008030050020000200201602401802022000020100020240000202400800800000018000040000180300a00200c0980500000002814000004000010040100380000c0300180d002000000040160040901003802000004000044000020040100000000406801801002014008000040100380300003c028080060040000401000c02800006024058000000100000200401c06008000014000080000a40280101a0000000300a064028000000100400000202800000012000040000000000900a000000000050060180300d008000008070000000080400002c008020020300001c01806801014012004078010140000500800000808805008004010010200000000502a0100100600000c0201f0
  | 12 => 0x4ba39e8880009064c8000414a6000000000092c000000b020b0a768be000940000000b3e4b800015c000000000000b844dcb2242e2cc48e6f02da23228287c00008eaa000076c47e000a8cb320f840471091e31a00061061696e00064c16494c3660a60000006c800000003a4c6000000ad653c0d40001fe3e214460020e642b8e35cade4d42bc85e0ae7d000069a1a8000a9c896000000000b8a2ac0001de0000dc000b2438058443689400038a70cb582e407e86e4843e86ceba2b802842d0244360a900006245384726325fa00098ab740a4b3c5900002f0064376ad800044c5aebacb545e469884a4fa68017c7c035473c388acc1ea9d27309c42729a400072863a9a0000000a140007d4630a2891c0080008ee6703ccaaa71215a8a42609d878279c6c66882083d665034e14a5ca06c66c000870a204760be942b42b4e1f8a009109824b098e00067411814030eafa246566ab61ca49c69c6188445d88b22fc5ce6760b6b1427c7560340003ca84211400000e21e28e5d41b85025d00000007863362d439a0000007749aa984000ac602274a8200c467c00039470400089a0006e0998b9422602816e00027072687451400065e6f8a66b9608ab5a3ec0001740000009744c257eabeb12b7209807ab287200008fe280000a681301c44c01849f81467fe60c1f418e0000000002b450a1620008d41266de0006520067482402baa9a58cb5600080c508628000128b2e0000004e0042afe3c20e86120000004b2000ace4ac00025450c33c0000009b08e8000b5086a0007d800089e3a80000007f8a5628c0000000005c072e000a1c1166a41fc00021a8463d2860ac42e8150b6a0001080000000007400003de4a6b7c71c2948d09460005e86a2a5eb1ca3283e41c8320005f6b6840c586a7c2e63726d434c5067aa1e645c640988b485d2312000286a820005564ea8a80e47ea95e60e7b2aae44a4506680cc00069e0002aa00043a2483340409de2c68bc3200005f26e267a0240005f447877c6581d88d6a120f0b88b6400009c310a967ae8649dc8a04cc7c44022c26ba812a48ad48542f67d64b662e994302b38b2a010b3a97c7a07ee0005f036c4ca922a8a58a66451e61c000af011c2024300b200000000000000072a93400065a56218884ea3e000000ae200000028a6d6a6e0000009a20a20005b82c409084c00081a9002d2a2213e91409a7c63f43068767f2000000b0686c05c4421800566b89704f600013c8b623610aa8e8c891888e5203ce03e0002988d22f48b447a5709505106ec54e4903d0292574a42352102398274a547bea58b609e45e29b426889ca0a17894e9089cc0c045682e7948c28f60fc12e0d600042c1367cc454a2c000aa2afc00012a88038ea5216c8f401c7f404a6da2fa4da36a5009622f82f28ac04e65457222e62
  | 13 => 0x9425c148000000000b4a7580006466fc000368000a9e0522b69c671a18656847c7387729f009e19008688248c6827060b461ab626568a2762000058198458b989908020fa60607063e00022811e79a78a6f25340004f44d2364492920776428ac20ea35856e6bc1bc1b20000000e0a940000c800097e32a446000000000000a5c00059e0c27320e2288b0a70e31600093675a482ada0007de0006be6cc0004ec0001d200000000019415846e866000b460006ca0009e200017a1660d00005642ce72493e4fc0000004f000020a2766968f268687a7d223855aa70abc1e288c1e83d40de8e2ae86dc12c2a8a722b07a65b2a0e000a866aa6900000004640000006660001920ee4a8b5c37c902aee5e6452000b780001ec00013213a6d8af25785a26d25ee7f00003a2000000000000200054000000000ab000000001e0180009fe9660da0000000000007504940000009d47dc8cc8d8084aec000000aa4000ba800054078000000c81e0884f80000004227920000005a078400000000000000000000057a00025e00095852863c96c444a340000f433800000003822279800029c4e69860603f629664eb203bca10bb00f66e86ee3827ca23ab905dc19e35e1a29783b60d85a48b05ec7a256aa4450e06e97294a100b6c52442018a0000000009aca889ce0000005da9f65d64aa000a468102b20008184e8b009604a49ee7880005f86440001a000080e4a004ca3c7184c4b262e211aba0378808a783c80a8462000602ae4b767683189a87527ce4263ba9eaa0837a99e0bc0009649c2000af678e230b3082ca7e76a0006c400000000090a72c7640ec6e60003e0b0e81c54a7e025899226eb400008c4000b7a74608c77a7340aa1dcab85528da0000003b27fc5cc7e63b023c9121d06a03903fa00005aaea37092600000000000052e1c617e9048e0a4055c2ea2620007163484343d825683817600000093a00000049e000000048000000000000000000000000a6a88622c0006480000000000000008ec00014c2ec0000002209ec000708000af47b60005de8a630015600061e00027aa3a00074e00024c000000b1e8400000001249d6a5070000077860a54c0007026b6ba63ee56065ca0433e3c63f2432b8632c9328286f642a0000000e62129d000000055e0000009b20620003740725c4824092ad07545128ae30424a31c38c2a00000009a600000000000048a000000000000000000b9a000a4a2060000000000000003be000b34546000264a4c02c8ba0005c643e0008e6b104f204415400017287202602aa846848920000001ac0006fe1225944003fe08000091a5500004d600000000055400062c2425be000000ae63da6920007b453a6a80b867e78c00092a000000608a6292e00035051668c0000000002be1ba00000014299c000000000
  | 14 => 0x9e60008c00000140000000bab1a39c0008580006e4000000000b0c0005bc2e0b16b70000a4e634b4c03c8140000000009280a09f252a2c09e02340200000001bea160000007c88ea1520000004405361a48f095c5763dcadc4180000000665880042ae7145a84ae6ea3440007f6346000a361d422a0000000002a60002fe7ac8b8a3090c050976b8233001676066eb04620a028680009e880605e4bc1b0b5ebae7bc4245fc9caa1ab6e03298cb661d61961fa2ee9b61ae488af80ac20cb7e9447e423eaa83400008000003aa0000000000003e600083c5e0000000aca0302a400082235a214a1800070a32618227e000000046ab285c6ac250850000a2e11299a00031419a30c3ae00029e0d260400003600000043c00059c2d601248000000000000000000000000079e00000047017000038698000049a87800087e79085600000046c7b844e0f25184a20002d834a1684122904085b600046a1e4416000b9c8360
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x401824985d56419121006095d78359064484012a190e0d6419121006095d780590644840128593e016419121007015d5649cc6448401c05755917319121007085d5649c06448401c2175591701912100720591735c064484010a598dd864d512100609dd98519354484012259899464d512100609615841d954484018458560c765512100618615801d954484018c183600765512100609a1e659915448401424975956455121006095d98519054484010a4985d9541512100541654645cc544840148496551731512100548654645c054484014a0965517015121006096157419363484014a09459570d8d2100518654645c36348401341902156354d2100628619841c153484015819498c7054d21006305d88054c5348401981742015314d21006095d98519343484015219519170d0d2100528259545c343484018c1762015390d21006095d9851914348401605951916350d21005a06406458d4348401825855d064d812100521251655cf60484014459519173d81210062161d8418d2154001a818418e7048550004d064c855c121540018c1861cd215405000720590734855014001825766147448740005816547458d21d00014849755163487400063061873485509000182576614744854000548654745c12150001581931d170485400069059580cc5210c001a416560332484300051165c83595210c0016059420d65484300051865c80595210c00162194201654843000681595849cd210c001a416560273484300061161d6514d210c001a05656105348430006905958014d210c001845875964348430006905958090d210c001a2165612704843000690595839c1210c001c41655cd704843000720591735c1210c00164196d4d21d4030007105db53487500c0018618759521140300070859574484500c001c41655cd21140300061861d65486400c001c41655cd2190030006a061943485400c001e016550d21500300050665075595300c001449921d5654c0300051464475595300c0014199421d654c0300051264887595300c0014519121d654c0300061259582dd1300c00185165607744c0300069059581989300c001a416560a614c0300071059771485300c001c4165dc9214c0300056065287485300c0014c1969d5214c0300047066075485300c001581941d5214c0300059065a65485300c0014c097595214c030007101d565485300c001a4386595214c0300069061965485300c001c4376595214c03000710e5d65485300c001c4097595214c03000710a1d65485300c001c4187595214c0300047066374485300c001c4165dd1214c0300071059574485300c001e0165991214c030006a061964485300c001e0165591214c030007105d5634843088001c417558d210c120007105d5634843084001c417558d210c110
  | 1 => 0xb8f20052360000000000000070dc64f6d8000088f4f03800281ace12d0c000a24800a8000030d2ae0000c800007600fa002a2034ac60ecc42c2656aacc40fc7e668644000046429e0000001400223c180000ead600be9c9800b6e874a6061ce4000a78eefe000068001082005a0424000000000000007ca0c2ba5e6cca846280508a006af8b2163a727a026e3294e0d4de4abc8c001e3e0008a400582e8e000cb04e5c9a00c60000000e4ce2000000000000b49654e69092da0016040602060305010308000003030801051e0803000002080500100404000402000f010000010f00040066060d801d1654840148494595731952100528251655c0654840150593211751912100548640845d464484018457560c6519121006185d5801946448401285932156419121004a8640855906448401824855d5641912100609e1d755906448
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x1288802cc0180e02852101400500b4642aeab20c890802821a0215755906448401402d1930baac83224200a08680985d56419121006042eac8706b20c8908030057564f805906448401420d40eab2a429806000b0069075595214c030005083504baca90a6018002c01a425d65485300c001600d250eb2a429806000c1066165dd1214c030
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 65
  | 6 => 1592
  | 5 => 3562
  | 4 => 1497
  | 3 => 128
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
  | 7 => packedAt gbK7 (1858+((h/21+packedAt gbK7 (1690+(h % 21)*8) 8) % 149)*8) 8
  | 6 => packedAt gbK6 (65264+((h/530+packedAt gbK6 (58904+(h % 530)*12) 12) % 3721)*12) 12
  | 5 => packedAt gbK5 (186407+((h/1187+packedAt gbK5 (170976+(h % 1187)*13) 13) % 4275)*13) 13
  | 4 => packedAt gbK4 (93812+((h/499+packedAt gbK4 (88323+(h % 499)*11) 11) % 1976)*12) 12
  | 3 => packedAt gbK3 (9296+((h/42+packedAt gbK3 (8960+(h % 42)*8) 8) % 185)*8) 8
  | 2 => packedAt gbK2 (988+((h/4+packedAt gbK2 (972+(h % 4)*4) 4) % 16)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe0f0f0fc3c3c3f83c0f03fffff405260eccff
  | 1 => 0xff00ff0fc03fc7fc00fffe0f800a639330fcc
  | 2 => 0xffff000fffc007ffff003ff0000c7c1c3f0f0
  | 3 => 0xf0000000ffffff80000003fffff8f801fc00ff
  | 4 => 0xfffffffffffffc00000f0001ffff00
  | 5 => 0xffffffff0000000000000000000ffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x645252e414140d9152548652a64052206cc55
  | 1 => 0x2ad446e2cc10d42b504639b4b0a0a6291305cc
  | 2 => 0x4ce6e444d4d4103398e412d6a140c7414350f0
  | 3 => 0xe0808080ba9a99020280a318c588e801f800aa
  | 4 => 0x80000008232322442308c000060d0000acaa00
  | 5 => 0x1080800000000000000000000021094000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfffffffefefcaa00fffffffefefcaa00fffffffefefcaa00fffffffefefcaa00fffffffefefcaa00fffffffefefcaa00fffffffefefcaa00fffffffefefcaa00, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_11970
namespace PEqualNP.Outside.L_meta_11970
open PEqualNP.Outside.L_meta_11970.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 128 := (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 bgb_3_96))
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
theorem bgb_4_1056 : Interval gbAtlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1088 : Interval gbAtlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1120 : Interval gbAtlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1184 : Interval gbAtlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1216 : Interval gbAtlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1280 : Interval gbAtlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1312 : Interval gbAtlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1376 : Interval gbAtlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1408 : Interval gbAtlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1472 : Interval gbAtlas 4 1472 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1497 := (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 (concat bgb_4_192 bgb_4_224)) (concat bgb_4_256 (concat bgb_4_288 bgb_4_320)))) (concat (concat (concat bgb_4_352 (concat bgb_4_384 bgb_4_416)) (concat bgb_4_448 (concat bgb_4_480 bgb_4_512))) (concat (concat bgb_4_544 (concat bgb_4_576 bgb_4_608)) (concat bgb_4_640 (concat bgb_4_672 bgb_4_704))))) (concat (concat (concat (concat bgb_4_736 (concat bgb_4_768 bgb_4_800)) (concat bgb_4_832 (concat bgb_4_864 bgb_4_896))) (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat bgb_4_1024 (concat bgb_4_1056 bgb_4_1088)))) (concat (concat (concat bgb_4_1120 (concat bgb_4_1152 bgb_4_1184)) (concat bgb_4_1216 (concat bgb_4_1248 bgb_4_1280))) (concat (concat bgb_4_1312 (concat bgb_4_1344 bgb_4_1376)) (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472))))))
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
theorem bgb_5_2720 : Interval gbAtlas 5 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2752 : Interval gbAtlas 5 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2816 : Interval gbAtlas 5 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2848 : Interval gbAtlas 5 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2912 : Interval gbAtlas 5 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2944 : Interval gbAtlas 5 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3008 : Interval gbAtlas 5 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3040 : Interval gbAtlas 5 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3104 : Interval gbAtlas 5 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3136 : Interval gbAtlas 5 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3200 : Interval gbAtlas 5 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3232 : Interval gbAtlas 5 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3296 : Interval gbAtlas 5 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3328 : Interval gbAtlas 5 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3392 : Interval gbAtlas 5 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3424 : Interval gbAtlas 5 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3488 : Interval gbAtlas 5 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3520 : Interval gbAtlas 5 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3562 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat bgb_5_672 (concat bgb_5_704 bgb_5_736)) (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864))))) (concat (concat (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)))) (concat (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536))) (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)))))) (concat (concat (concat (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat (concat bgb_5_1888 bgb_5_1920) (concat bgb_5_1952 bgb_5_1984))) (concat (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)) (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 bgb_5_2656))))) (concat (concat (concat (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)) (concat (concat bgb_5_2784 bgb_5_2816) (concat bgb_5_2848 bgb_5_2880))) (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104)))) (concat (concat (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200)) (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328))) (concat (concat bgb_5_3360 (concat bgb_5_3392 bgb_5_3424)) (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552)))))))
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
theorem bgb_6_1568 : Interval gbAtlas 6 1568 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1592 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))) (concat (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344))) (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 65 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 16, 20),(inputs.getD 3 zero, 32, 40),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 16, 20),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 16, 18),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 32, 33),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 16, 20),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 32, 34),(inputs.getD 2 zero, 32, 36),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 4 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 16, 20),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 16, 20),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfffffffffefefefefffffffefefcaa00fffffffffefefefefffffffefefcaa00fffffffffefefefefffffffefefcaa00fffffffffefefefefffffffefefcaa00
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
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
  have lift := lift_ok (u:=true) (ms:=fixRows 64 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 7 → Bool) := decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 7) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 7 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 10)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 10 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_11970.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,4]⟩,⟨.and,[7,6]⟩,⟨.or,[1,2]⟩,⟨.or,[4,5]⟩,⟨.or,[10,6]⟩,⟨.and,[9,11]⟩,⟨.or,[0,6]⟩,⟨.or,[3,5]⟩,⟨.and,[13,14]⟩,⟨.or,[8,12]⟩,⟨.or,[16,15]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
    exact ⟨mono,17,monoShape,by change 11 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_11970

open PEqualNP.Outside.L_meta_11970 in
theorem PEqualNP.Outside.L_meta_11970 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
