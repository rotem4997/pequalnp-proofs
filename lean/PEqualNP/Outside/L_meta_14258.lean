import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_14258.Model
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


end PEqualNP.Outside.L_meta_14258.Model

namespace PEqualNP.Outside.L_meta_14258
open PEqualNP.Outside.L_meta_14258.Model
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

end PEqualNP.Outside.L_meta_14258

namespace PEqualNP.Outside.L_meta_14258
open PEqualNP.Outside.L_meta_14258.Model
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
  | 1 => 0x1f87fc3ff0fffc3c3c38f03f8ff03fff21339f
  | 2 => 0xe007ffc3fff87fc03fff003ff0fff83e3e3cf3
  | 3 => 0xfff87ffc00ff87ffc03fffc3ff003fc1c7cf1c
  | 4 => 0x7fffff0007ffffc00003ffffc001f80fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x824a4490895444160e10922509910d19211185
  | 2 => 0x91109092080814010690488902490a40e2432
  | 3 => 0x45011008622008c8400a2182a202a284424e18
  | 4 => 0x566662a2483556aea68089234ccb0309f00bc0
  | 5 => 0x984443338cc667333b34ce30088c0431bdb000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfff0ffc0fcf0ccc0fff0ffc0fcf0ccc0fff0ffc0fcf0ccc0fff0ffc0fcf0ccc0fff0ffc0fcf0ccc0fff0ffc0fcf0ccc0fff0ffc0fcf0ccc0fff0ffc0fcf0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_14258
namespace PEqualNP.Outside.L_meta_14258
open PEqualNP.Outside.L_meta_14258.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfe1f1fc7fe3ffe1c71f8e07c7e0fffe19327f
  | 2 => 0xf1fe01ff87fc78fe07e3f007f8ff0e1e663d93
  | 3 => 0x1fffe3ff8007f1ff803fff8ff000fe187ce1c
  | 4 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80280204210420008105024101204308091025
  | 2 => 0x2840a4891240c10a02229092484a0454262492
  | 3 => 0x6484609010c910264800a430d20628c4824e18
  | 4 => 0x441549224480125554480120a494a081d00b40
  | 5 => 0x8919810367126499a79349c40018c1197db000
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_14258
namespace PEqualNP.Outside.L_meta_14258
open PEqualNP.Outside.L_meta_14258.Model
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
  | 0 => 0xf83c3fc7fffe1fe1c3ff0e0fc3fff87f1d33cf
  | 1 => 0xffc03ff87c3fe3fe03c3f00ffc783f8f923d33
  | 3 => 0xffffc7ff803ffc3ffc03fff0ff803ff0e3ce3c
  | 4 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xa0040421010200080850241008a0844051045
  | 1 => 0x909294912265062a2162908a6450950a922512
  | 3 => 0x21080100088800444400242089012220204a28
  | 4 => 0x85ab36254a0d4ab76a688128f2658322f80f80
  | 5 => 0xc632243673319339b3b3c9cc2046044cdfb000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xffaaff88eeaaee88ffaaff88eeaaee88ffaaff88eeaaee88ffaaff88eeaaee88ffaaff88eeaaee88ffaaff88eeaaee88ffaaff88eeaaee88ffaaff88eeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_14258
namespace PEqualNP.Outside.L_meta_14258
open PEqualNP.Outside.L_meta_14258.Model
def s3K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x312004005f31ec6374c7a98d531
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x2550e31
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*4) 4
  | 3 => packedAt s3K3 (i*15) 15
  | 2 => packedAt s3K2 (i*26) 26
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (5+((h/1+packedAt s3K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s3K3 (79+((h/1+packedAt s3K3 (75+(h % 1)*4) 4) % 11)*4) 4
  | 2 => packedAt s3K2 (27+((h/1+packedAt s3K2 (26+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfd9f3e39fe71cf
  | 1 => 0xfffffffffffffffffffffffdbe13cfc1cfb933
  | 2 => 0xeffe3f3fe0fce3c
  | 4 => 0xf3ffc03fff00fc0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404204008420045
  | 1 => 0x249461244a52912
  | 2 => 0x110080490080228
  | 4 => 0xe102ab25212d80
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 23 s3Pos s3Neg, 0xfafae8e8fafae8e8fafae8e8fafae8e8fafae8e8fafae8e8fafae8e8fafae8e8fafae8e8fafae8e8fafae8e8fafae8e8fafae8e8fafae8e8fafae8e8fafae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_14258
namespace PEqualNP.Outside.L_meta_14258
open PEqualNP.Outside.L_meta_14258.Model
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
  | 0 => 0x1e1e3c7fc7f1fe3f1c63838fe3f1f87f10f4cf
  | 1 => 0x1fe03f8ff8fe3fc7e07c03f1fc7e3f87233b33
  | 2 => 0xe0003ff3ff003ff8ff8003fe3f803ff8c3cc3c
  | 3 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x42804600424208400820908240910822105045
  | 1 => 0x84088840908050084044211084281204212112
  | 2 => 0x15511292424a401b4804a242904a550c28c28
  | 3 => 0x8440122002004922509080032448110440e80
  | 5 => 0xd198224836c93924da7273c900090666bbf000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_14258
namespace PEqualNP.Outside.L_meta_14258
open PEqualNP.Outside.L_meta_14258.Model
def s5K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (6+((h/1+packedAt s5K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf3cfe3c7fc7e3f1f8c63c70fe3f0fc78474cf
  | 1 => 0xf03f1fc063f9fc7e3f07c780e3c7f1f99a4b33
  | 2 => 0xffc01fff83fe007fc7f807ff03f801fe638c3c
  | 3 => 0xffffe00003ffff8007fff80003fffe007c0fc0
  | 4 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1040200804004020000081020090040001045
  | 1 => 0x10888411049080c042024484484240a10a4112
  | 2 => 0x22024888090049200948012202902514208c28
  | 3 => 0x441241aa5225402495d4900a1324ac14740e80
  | 4 => 0x88a091304035924926a7264c9800c8215f6000
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xfefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_14258
namespace PEqualNP.Outside.L_meta_14258
open PEqualNP.Outside.L_meta_14258.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xe00003c006e00005c001200680000006400000000003600000000000600007e04520000000000465600160c2a0000001c000000000000027c00000024000000000000080000000074347800004826001a000000585a0a4a00800000003220000000000000000000382c00000000003e6200002e1800306c1e00701066001400000000000000760000008250008400603a004c54004e284200720000865e004000007a6a00002200004401010800000001000000000202020000010502000100007fd5001fe54007f55001fc54007fd4c01fe53005f94c01fd53007f14c017c53007fd0c01fe43007f50c01fc43007fd4801fe52007f54801fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc32007fd44017f51007f94401fd51005f54401fc51007fd0401bf41007f90401fd41006f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd40017f50007f94001fd50005f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x924000fb4c920005fec290006fc6148001bfa8a4000df545200077e8290003bd4148001f790a4000fb48520006fea0900037d5048001fd2024000fe5012001ff6409000bee20480057fb284006bf99420016fcca100027e65080017eb284002df59420004faca1000afc65080057fb204005bf990200177cc810002be64080017eb204002ef590200057ac81000afc64080057fb184004bf98c20017bcc610002de63080017eb184002f758c20005bac61000afc6308001bf2984000df14c2001dfcc410006fe6108005fb3084000bd98420005fac21000bf561080017ab084000dfd4420006faa210003bf4108001dea084002bf98020016fea01000b7d5008005f79004002fe88020017da401000ff920080037fb2e2006bf9971000efccb880027e65c40017eb2e2001df59710004facb88006fc65c40037fb262005bf9931000f7cc988002be64c40017eb262001ef593100057ac988006fc64c40037fb1e2004bf98f10005fac788006fc63c4001bf29e2000df14f1000dfec58800efe62c40017eb162001bf18b1000efea3880077d51c4003dfa0e2001fd9071000f7a8388003f541c4001daa0e2001fd8c710007ea6388007f621c4001fa90e2000dfd4310006faa18800aff658400d7f32c2002df99610004fccb08002fd6584005beb2c20009f59610015f8cb0800aff648400b7f3242000bf59210015f8c90800aff63840097f31c2000bf58e10015f8c7080037e5384001be29c2002bfd8a1001dfcc508002fd62840057e3142000bf58610006fea3080037d5184001dfa0c2000ef50610015fcc10800b7f5084005bea842002fe8c210007f2610800bfa2084001fc9042002fdc421000ff62108002ff654400d7f32a2000df99510004fcca88002fd6544001beb2a20009f59510035f8ca88002ff644400b7f3222000bf5911002df8c888002ff63440097f31a2000bf58d10025f8c6880037e5344001be29a2000bfd891001dfcc488002fd62440077e3122000dfd4510006faa288003bf4144001fb20a2000ef50510007ea8288003b54144001fb18a2000fd4c510007ec4288003f52144001bfa822000df54110007f46088003f93044001fd1022000fe4811000ff6208800bf610440057fb282006bf99410016fcca080027e65040017eb282002df59410004faca0800afc65040057fb202005bf990100177cc808002be64040017eb202002ef590100057ac80800afc64040057fb182004bf98c10017bcc608002de63040017eb182002f758c10005bac60800afc6304001bf2982000df14c10015fec40800efe6204005f73102000bb98810005fac40800bed620400176b102002bf1881000dfcc2080077f5104003bea882001efd041000f7a820800afe6004005bfa802002df54010017ee200800bfa1004005fa8802001fe44010
  | 1 => 0xbfa4010005dea008005fe50040025fecb980137f65cc0093fb2e6006bf99730005facb98012fc65cc009be32e60049f19730025fec998016fe64cc0017eb266004bf19330026fca7980137c53cc009ef21e6000f750f3001dfcc598002fd62cc009ef9966000f74cb3000dfcc398002fd61cc001bfa8e6000df547300077e8398003bd41cc009ef98e6000f74c730006fea1980037d50cc0057fb2c6006bf99630016fccb180027e658c0017eb2c6002df59630004facb1800afc658c0057fb246005bf99230005fac91800afc648c0017eb1c6004df94e30026f8a71800efe628c0017eb146001bf98630005fac3180037f518c001bea8c6000efd06300077a831800afe608c005bfa846002fe94230016faa118003f9508c001bca846002f7cc230027f66118002ff654c001bfb2a60009fd9530035fcca98002fd654c00d7e32a6000df19530004f8ca98002ff644c00b7f3226000bf5913002df8c8980137e534c009be29a6000f790d30007ba8698002ff624c0077e3126000f7cc930007ba6498002ff614c0037e30a6000dfd4530006faa298003bf414c001dea0a6000f7cc530007ba62980037f504c001fd2826000df54130007f2a09800379504c009fd9826002f78c130015feca1801afe650c005bf32860009f99430005faca1800b7d650c0013eb286002bf19430015fec818016fe640c005df3206000af99030005fac81800bbd640c0015eb206002bf19030025fcc6180137e530c009be2986003bf98830017dcc418002ee620c0017eb106002fb58830005dac418006fe610c005fb3086000bd98430005fac21800bf5610c0017ab086000dfd4430006faa218003bf410c001dea086002bf98030016fea01800b7d500c005ef9806002fe8c030017ba6018013f9300c0077fb2e4006bf99720005facb9000efc65c80077fb264005bf99320005fac99000efc64c80077fb1e4004bf98f20005fac79000efc63c8001bf29e4000df14f2001fdc8590003ed42c8007f71964000fb4cb2000dfcc390002fd61c8001bfa8e4000df547200077e8390003bd41c8007f790e4000fb48720006fea1900037d50c80057fb2c4006bf99620016fccb100027e65880017eb2c4002df59620004facb1000afc65880057fb244005bf99220005fac91000afc64880057fb1c4004bf98e20005fac71000afc6388001bf29c4000df14e20005fac510006fe61880017eb0c4000dfd4620006faa310003bf4188001dea0c4002bf98220016fea11000b7d5088005fd2044000fe50220017de411000ffb20880017fb2a4006bf99520005faca9001afc65480017fb224000efd91200057ec890016fe64480017eb224005bf1912000778c890002bc64480017fb1a4004bf98d20005fac690012fc6348001bf29a4000df14d20007dc8490003ed4248001f71
  | 2 => 0x50006fca7280037c53940077f314a000bf58a5000dfcc328002fd6194001bfa8ca000df546500077e8328003bd41940057f304a002dfd4250037f6a128002ff645400b7e322a000dfd5150006fca8a80037d5454001be2a2a000bfd8d50025f8c6a80037f5354001bf29aa000df54d50006f8a6a8002ff62540077e312a000dfd4950006fca4a80037d5254001be292a000bfd855000df8c2a80037f5154001bf28aa000df54550006f8a2a8003bf4154001dea0aa006fed4150016fca0a80037f6454001bf322a000df59150006f8c8a80037f6354001bf31aa000df58d50006f8c6a80127c6354001bfa1aa000df90d50006fa86a80037c4354001bfb12a000df98950006fac4a80037c6254001bfa12a000df90950006fa84a80037c4254001bf992a000df8c950006fa64a80037c3254001bfb0aa0009fd8550006fcc2a80037d6154001be30aa000dfd05500067e82a80037e4154001bea0aa000cf50550006f882a80037f3154001bf18aa000df4c550006f862a80037f2154001bf10aa000df48550006f842a80037f6054001bdb02a006bf99450004fcca28016fe64140017eb20a004bf98c50005fac6280037e531400dbe298a003bf98850005fac428006fe61140017eb08a006dfd4450006faa228003bf4114001dea08a002bf98050016fea02800bfa5014005bea80a006fe5405002dfecba001afe65d00017eb2e8005bf19740025fcc7a0002fd63d0001bf29e8000df14f4002f7e87a0003bd43d00077f3168000bf58b4002f7e85a0003bd42d00037f30e8000bf58740006fea3a00037d51d000bdfa0e8000ef50740006fea1a00037d50d00057fb2c8006bf99640016fccb200027e65900017eb2c8002df59640004facb2000afc65900017eb248004bf98e40005fac7200037e5390001be29c8003bf98a40005fac520003be4290001de2148001bf98640005fac3200037f5190001bea8c8000efd06400077a832000afe6090005bfa848002df542400177e8120017fb40900017fb2a8006bf99540005facaa001afc65500017fb1a8004bf18d40006fca6a00037c5350001dfa1a8000ef50d40005fec4a000efc6250001dfa128000ef50940005fec2a0006fc6150001bfa8a8000df545400077e82a0003bd4150001bfa828000df5414002ff680a000bbe40500057fb288006bf99440016fcca200027e65100017eb288002df59440004faca2000afc651000b7f3208004bf98c40017bcc620002de63100017eb188002f758c40005bac6200037e5310001be2988003bf98840017dcc420002ee62100017eb108002fb58840005dac420003be421000bde2108001bf98440017ecc220002f661100017eb088002fd58440005eac2200037f5110001bea888005efd04400077a822000afe6010005bfa808002df540400177e802000
  | 3 => 0x6b106200bb5883100dfcc2188077f510c403bea886201efd043100fec8218807bd410c401faa086200ed5043100fbe6218807f6310c403ee9886204fd4c431015fcc018807fa600c4017d3006200bf5803100ff2c018802f9600c4077fb2e4206bf99721005facb9080efc65c84077fb264205bf99321005fac99080efc64c84077fb1e4204bf98f21005fac79080efc63c8401bf29e4200df14f2101fdc6590803ed32c8401bfa8e4200df547210077e8390803bd41c84057f3064200bf5832100dfecb1081afe6588403bf32c42009f99621005facb108077d65884013eb2c4201bf1962100dfec910816fe6488403df3244200af99221005fac910807bd64884015eb244201bf1922100dfec710812fe63884017eb1c4201bf18e21006fca7108037c53884017eb144201bf9862100efea3108077d5188403dfa0c4201fd9062100f7a8310803f54188401daa0c4201fbc862101fee431080afe60884017eb044200bfd9521035fcca90802fd654840d7e32a4200bfd912102dfcc890802fd644840b7e3224200bfd8d21025fcc690802fd63484097e31a4200df94d21006f8a690803ee3248401f69924200dfd4521006faa290803bf4148401fb20a4200ef50521007ea8290803b54148407fb90a4201fb88521005fec09080afc60484037fb284206bf9942100efcca108027e65084017eb284201df59421004faca10806fc65084037fb204205bf9902100f7cc810802be64084017eb204201ef590210057ac810806fc64084037fb184204bf98c2100fbcc610802de63084017eb184201f758c21005bac610806fc6308401bf2984200df14c2101dfcc410806fe6108403bfa884201df5442100f7e8210807bd4108403f79084201fd8842100fda421080ff521084057f3004201fe98021005f4c010802fd6008403fcb004200be5802102dfcc9a8002fd64d400dbfaa6a000df95350006faa9a801b7c54d40097f31ea000bf58f50036fea7a80037e53d4001bea9ea006df14f5001dfcc5a8002fd62d400dbfa96a000df94b50006faa5a801b7c52d40037f30ea000bf58750036fea3a80037e51d4001bea8ea006df147500077e83a8003bd41d400dbfb26a000df99350006fac9a801b7c64d400dbfb1ea000df98f50024fcc7a80037d63d400dbe31ea000dfd0f50006fc87a80037d43d4001be21ea006dfd8b50006fcc5a80037d62d400dbe316a000dfd0b50006fc85a80037d42d4001be216a000dfccb50006fc65a80037d32d4001be196a006dfd8750006fcc3a80037d61d40013eb0ea006df18750006fe83a80033f41d4001bf20ea000df507500067a83a80037c41d4001bf98ea000df8c750006fa63a80037c31d4001bf90ea000df88750006fa43a80037c21d40017eb2ca0009f5965002dfcc928002fd64940097f31ca000bf58e
  | 4 => 0x80efe62904017eb148201bf9864100efea320807f65190403bea8c8200fd54641006eaa320807bf419040bfba0c8202bf98241005fac120802ff655040d7f32a8200bf59541035f8caa0803bf5450401df2a28200ef5514100778a8a0802ff63504097e31a8200df94d41006f8a6a0803bf4350401df21a8200ef50d410077886a0802ff62504077e3128200efd09410077c84a0803bd4250401de2128200dfd4541007eca2a08037d5150401faa8a8200dd5454102fee82a0807be41504017fb028202bf181410077ecaa0803be6550401deb2a8200ef195410077ec6a0803be6350401deb1a8200ef18d410077ea6a0803be53504019f29a8200ef54d4100778a6a08033c5350401dfb128200ef989410077ac4a0803bc6250401dfa928200ef949410077aa4a0803bc5250401df9928200ef8c9410077a64a0803bc3250401dfb0a8200edd85410077ea2a08033f5150403df28a8200ed945410077aa2a08033d5150401daa8a8200cd5454100f78a2a0803bf6050401df3028200ef5814100778c0a0806ff651040d7f3288201df99441004fcca20802fd6510403beb2882009f5944100df8ca20816fe64104015f3208204bf98c41005fac6208037e5310401be2988203bf98841005fac420806fe6110403bfa888201df5444100f7e8220807f64110403dea088205fd50441015fcc020802fd60104097fb2e6204dfd9731024fecb9881afe65cc4017eb2e6204bf19731026f8cb988127c65cc4097fb266205bf99331005fac998812fc64cc409bf29e6204df14f3101dfcc598802fd62cc409ef9966200f74cb31006fea3988037d51cc401dfa0e6200fd907310077a8398803f541cc401daa0e6202bf98331005fac198806ff658c40d7f32c6201df99631004fccb18802fd658c403beb2c62009f5963100df8cb18806ff648c40b7f3246201ef992310057cc918802fd648c403deb246200af5923100df8c918802fd638c409bf29c6204df14e3101dfcc518802fd628c4037f30c6201dfd463100feca3188077d518c401faa8c6200dd5463100f7e8318807bd418c403ef98c6204fdcc631015fcc118802fd608c4017fb2a6200dfd9531004feca9881afe654c4017eb2a6206bf19531006f8ca988027c654c4017fb226205bf99131005fac898816fc644c409bf29a6204df14d31005fec49880efc624c401ef9926200f74c931006fea298803f6514c401bea8a6200fd54531006eaa298803bf414c401dea0a6204fdcc53100fbc6298802ff604c4057e3026201bfd9431035fcca188077e650c4013f3286200bf5943100efaca188027d650c4037e3286201bfd903102dfcc818807be640c4015f3206200bf5903100f7ac818802bd640c4037e3206204bf98c31026fca6188137c530c4077f3106201fb98831005dcc418802fd620c403f
  | 5 => 0x8032005fac019016fe64d44017eb26a206dfd5351006fca9a88037d54d440dbe2a6a204bf98f51005fac7a881b7f53d4401bf29ea200df54f51036f8a7a880efe62d44017eb16a206dfd4b51006fca5a88037d52d440dbe296a202bf98351005fac1a881b7f64d4401bf326a200df59351036f8c9a881b7f63d4401bf31ea2049f98f51006fac7a881b7c63d4401bfa1ea200df90f51006fa87a88037c43d440dbfb16a200df98b51006fac5a881b7c62d4401bfa16a200df90b51006fa85a88037c42d4401bf996a200df8cb51006fa65a88037c32d440dbfb06a200df98351006fac1a88027d60d440dbe306a200bf59651004facb28816fe6494403df324a200af99251005fac928807bd64944015eb24a204bf98e51005fac7288037e5394401be29ca203bf98a51005fac528806fe6194403bfa8ca206fdd4651015fcc128802fd60944017fb22a205bf19151006fea8a88037e5454401beaa2a200df15151005fec6a8812fc6354401bfa9aa200df94d51006faa6a88037c53544017fb12a203bf18951006fea4a88037e5254401bea92a200df14951037eea2a88077e51544017fb02a202bf18151006fec8a88037e6454401beb22a200df19151006fec6a88037e6354401beb1aa200df18d51024f8c6a88037f4354401bf21aa200df50d51006f886a88037f6254401bf312a200df58951006f8c4a88037f4254401bf212a200df50951006f884a88037f3254401bf192a200df4c951006f864a88037f6154401bbb0aa200dfd8151004fec0a88037e6054401beb02a200df18151035fcca288027e651440b7f320a201ef990510057cc828802fd6414403deb20a200af59051025fcc628802fd6314401bf298a206df14c5101dfcc428802fd62144037f308a201dfd445100feca2288077d511440dfaa88a202bf98051005fac028816ff65d040d7f32e8200bf5974102df8cba0803bf54d040bdf2a68200ef5534102f78a9a0812fe63d04017eb1e8200df94f41006f8a7a0817bf43d0401df21e8200ef50f4102f7887a080efe62d04017eb168205efd0b410077c85a0803bd42d040bde2168200dfd4741006faa3a080afe60d04017eb068205efd97410077ccba0803bd65d040bde32e8205efd8f410077cc7a0803bd63d040bde31e8200efd4f410077ca7a08033e53d0401dea9e8200ef14f4100678a7a0817bf62d0401df3168200ef58b4102f78c5a0803bf52d0401df2968200ef54b4100778a5a0803bf32d0401df1968200ef4cb410077865a0803bf51d04019fa8e8201ef947410077aa3a08033d51d0403de28e8205efd83410077cc1a0803bd60d040bde3068201bfd9641035fccb208077e65904013f32c8200bf5964100efacb208027d65904037e32c8200bf592410057ac920812fe63904017eb1c8200df94e41006f8a720
  | 6 => 0x97f31ca403f798e52005bcc729002fd6394807eeb1ca400b758e52006fca7290037c53948077f314a403dfd4a52037dea529006fe61948017eb0ca402bf98252005fac129002ff645480b7e322a400dfd5152006faa8a9002ff63548097e31aa400df94d52006f8a6a901bef5254807bf292a400bfd855200df8c2a9002ff60548057e302a406bf9945202dfcc829002fd64148097f318a400bf58c52006fca62901b7c53148077f310a403dfd485201fdca42900f7d521480df6a90a401bf98452005fac22900afe60148017eb00a405bfd9742035fccba1002fd65d080b7e32e8404bf98f42005fac7a10037e53d0801be29e8401bf98742005fac3a100afe60d08017eb068403bfd9642035fccb21002fd65908077e32c8400bf59242025fcc721002fd6390801bf29c8400df14e420077e8721003bd43908077f3148403efd0a4202fde8521006fe61908017eb0c8402bf98242005fac121002ff655080d7f32a8400bf59542035f8caa1002ff63508097e31a8400df94d42006f8a6a1017ef4250807df2128400bfd854200df8c2a1002ff60508057e3028403bfd9442035fcca2100f7e65108013f3288400bf5944201efaca210027d65108077e3288405bf99042025fcc62100fde63108016f3188400bf58c4201fbac621002dd6310801bf2988400df14c4202f7e8621003bd43108077f3108403efd084201fdc842100fbd421080bf6a108401bf9844201fecc221002f661108017eb088403fd58442005eac22100afe6010807fd3008400be98042005fac02100ff960108017cb008404bfd9732035fccb99002fd65cc8097e32e6404bfd933202dfcc999013be64cc8015f3266400bf593320277ac999002bd64cc8097e3266400f7d4f32026fca7990137c53cc809ee29e6404d714f32027bc8799003dd43cc8037f30e6400bf58732015fcc199002fd60cc8077fb2c6406bf9963201efccb190027e658c8017eb2c6403df59632004facb1900efc658c8077fb246405bf99232005fac91900efc648c8017eb1c6404df94e32026f8a71900efe628c807f72946400fb54a32007de851900fec428c807ef9946404fbcca3200dfcc319002fd618c8057f3046400bf58232005feca990037f654c8013fb2a6406bf99532005faca9901afc654c801be32a64009f19532005fec899016fe644c8017eb226405bf19132007bea6990137e534c809be29a6400f714d32006b8a699003de434c801eea1a6400fb94932007daa499003ef424c801f62126404fbcc93201fbc6499002ff614c8037e30a6400bfd8132015f8c09900eff650c80d7f3286400bf5943201df8ca1900eff640c80b7f3206400bf5903201df8c819012fe630c809bf2986404df14c3201dfcc41900fdf320c807f71906403f74c832027da6419006fe610c8017eb086402bf9
  | 7 => 0x2a006fe611500bfb308a800bd98454005fac22a017f561150017ab08a802bf98054005fac02a016fe64d4c017eb26a603bf98b53005fac5a9806fe61d4c017eb0ea602bf98353005fac1a9802fd6594c0b7f324a600bf59253006fea9298037e5494c01beaa4a600df15253025fcc7298137f5394c0defa9ca603bf98a53005fac529806fe6194c017eb0ca602bf98253005fac1298137f6494c09bf324a604df59253026f8c9298127e6394c09bfb14a604df98a53026fac5298137c6294c09bfb0ca604df98653026fac3298027d6194c09be30ca604dfd8253026fcc1298137d6094c013eb04a604df18253005fec8a9816fc6454c0defa9aa604df94d53005fec4a980efc6254c017fb0aa601bf18553005fec0a980afc6054c0d7f328a605bf990530277cc829802be6414c017eb20a604ef590530057ac82981b7f5414c01bf2a0a600df55053036f8a829812fe6314c09bfa98a604f794c53026faa62981bdd5314c077f310a604fb98853005dcc429802fd6214c09f6b10a600bb5885300dfcc229813f66114c017b308a600bf58453027eac229802f56114c057f300a604fe98053005f4c029802fd6014c09fcb00a600be58053026fec8298137e6414c099f320a604df590530267ac8298137c6414c09bf318a6049f98c53026bcc6298137f6214c09bf310a604db98853026fac4298136d6214c09be310a604dfd8453026fcc229813766114c09beb08a6009f58453026eac229802756114c09be308a604dfd8053026fcc0298137a6014c09beb00a6009f58053026f2c029802796014c09be300a605bfd9743035fccba18177e65d0c013f32e8600bf5974302efacba18027d65d0c0b7e32e8605ef953430077aa9a18137e53d0c09be29e8603bf98b43005fac5a1806fe61d0c0bfb30e8600bd98743005fac3a1817f561d0c017ab0e8602bf98343005fac1a1812ff6590c0d7f32c8600bf59643025f8cb21802fd6490c097f31c8604df94e43026f8a721813bf4390c0befa1c8603bf98a43027dcc521802ee6290c017eb148604fb58a43005dac521806fe6190c017eb0c8602bf98243005fac121802ff6550c01bfb2a86009fd9543035fccaa1802fd6550c0d7e32a8600df19543004f8caa1803be5450c01deaa28604df94d43026f8a6a1817df4350c09df21a8600bfd894301df8c4a1802ff6150c037e30a8600bfd8143015f8c0a1812ff6510c0d7f3288600bf59443025f8ca21816fe6410c097f3188604df94c43026f8a621813bf4310c09ef2188604ef50c4302fba862180efe6210c017eb108601bf98443005fac22180afe6010c017eb008605bf99352005fac9a901b7f54d4801beaa6a404bf98f52005fac7a90037e53d480dbe29ea401bf98752005fac3a900afe60d48017eb06a400bf5965202dfcc929002fd649480
  | 8 => 0x100100100000500600000800100400400000301800000600100100200a00402400400700100500600000100700200100300000200500000100000800000000400000000000000300100000f00300c00200500100500800c00f01200000000100000601d00200000600000a00000200000200100401300300000000500100300400800000000300100000300300200100000100300100200000200000300100600a00000200f00000000000000400100100100100600100400000000000500900800300000100200000000500600900200000100200200000200100b00000000200200100000000700100000200000000b00b00500000000000000000300000000400000800200002100c00101100000400100600000300600400100201200700300500101a00400100001100000200100100f00000000000a00000400200700000000800000100300400100100300000000600001000b00800000200c00100000900100000000500000000200100100700100300300000400200300000000000a00100300000000000200003a00d00900400000200300800000e00200000600300f00100000600000000600000100200300500000200400000200000000100300000000701100000100000000000800300f00200500800200000100000300101300400100100b00000000700200200100000700100800500000300000200400000300d00000200200200501401100100000201800000000000400900501800000001400000000100000000200700200000500101000800000100000000200100200100200800100200d00201000600000100400000000c00600000500000400200400000600000100100300100100100000000000a00000300000901000000d00001200000001500400000100400000000b00400200400100400000200300600000400000000100400900500000800400500400100300100000e00300001200400000200300100100000000000500a00000900100301d00000000500000000001c00500000000f00100000000800500000000000500900100000000500000a00400700300300600200500000301100300001200800100100900400000900900900300000c00200400100a00000b00301700400000000100000c004008006004003001025fcc7aa002fd63d50077f316a800bf58b5400dfcc3aa002fd61d50057f306a800bf58354005facb2a016fe649500bbfaa4a806efd52540067ea92a012fe63950017eb1ca803bf98a54005fac52a006fe61950017eb0ca802bf98254005fac12a01bbf545500bbf2a2a800bfd8d54025f8c6aa002ff62550077e312a800bfd855400df8c2aa002ff60550057e302a806bf9945402dfcc82a0177f541500bdf2a0a805df550540377aa82a012fe63150017eb18a803bf98854005fac4
  | 9 => 0xf2142e22d901642ae336038000000d1a000000bfe0008ce000688000000000000650c1ee260ba0000002ce0000000000000008dc0b4448000000bfc00043edbad029b4126bf0000024b647c400000027600000006adf4ac476c0002e6000064b8cdbc184000d64698240878000d12000dec65c52e712130000d9c36e00000003cc2c946abe786956000a3a7bc000bb2374534000e0a2569f03488b655ed1ec42120b24008000bbacac000c50ae0000e14a4e1000000f60003a40006ae00079460ce1c39a00056c0004d69768be5c8490be666ce040c623e8de9367c2058000a180003b243a5b0000b9463810200087ed50d3ab1045e26e424b8e000000ca0000000cca0005c02185009b8798000690000000cf6888d540002f2000166dc40003581684a2606430318000732c84b7a6103f00000c26cc1fc7c64260004bc18e1e601438e042b58ddad92a42bee2c6000000000c4622c10eb1284a0000000006becfe00042a15a9c03600000000007664ea000000aa071aae2df20de5e472e52c376032b062968764da000000000868000000000626480000b8401000000054288c000c2a340810000a4800010a3cad7a000000528000a80000d8e000d2e0f0dd4d96000594c4e65e724db01f009c6c85d6b363e8388b46114000af24c60002b40003a255c67400000017463684e00000000021e506212b5c07ea2a4f03908f2c72000000000bb67480000004b49da586d34c20be4c9e1520004420002507fa0000000d685acd096863c000000000892afc6ec8b064cd0000002000054a460000a8c3b0750000dd69eabd61cc87ab0ece6c36be095a58c82623a98c2803d80000001a40000008d048e7d45163166d400098004eca2ace000602140c04298a1e51c38a0003fc0d47009bc33252a6b649c8406d882a4660003267103300008504ec324954b04510086a0c9cc00000000000000066a000b1886ee20396000000000210000000000000408c52dfc0007a800037e55492000000029e000a7a00070421632205ad3609a0007fe3aa02a000000b3a00075a0004e4238628000d2200011a2f41b29120fc0001869fc12a8726e4db2c92a9401e0000005cc11e0000006b400053cb820004f6268cee73a52495889e188cd65f200035a9f8d14bb0000ad06a00a0e0e1bc000a5847c0180006b0cfc12ea74d683d01ae7ba0000000000000000006f0000000bd40006e00003068949f480e692aee9967189400000900acab2b327b6760c5c0d00000000002caab071c8d400044c2aa99e82240a934000aae0008440d2cba0a6000c7627aa5ec689608082de4ac56e8fa00010400000400a00000000000100000000e002001002001014000000000000005002001000007016006000001004002001000003001000000002001003008001046006000001005000
  | 10 => 0x3706a600000000000000000075ed562ea6ce00071600000000000000000000ae0600000020667e000000daa30a272000bd00f8a84000b98000000c286eab90000000000668000400dcc000000c1c40697c7c0c167b80005462ec796290ce0ce8c30c3c686d98a5a4d29520002d274e3ea742000ca60001725140eed60000d429de5b23b8000c6c4285dc1a8000000000446b5600000050a0000002c00006a4ad8200000000000000000dee0006940000000000008520000000009d000041cdde0000000002fa00000074602cc0242c00000000068a7ca18007a64e192b4212259c05e0007309283f2ac200000094cc82c061827be33acc2000804cf0000000cf40000001e400060022400000000071eb8036472013e0000000000001160000009b00000008667e43d44bad5a0007cc000a88a5c000000000000a52aa4084de4150af6000a2657c8bcd480002360cc000000000000d0848a0c49d2000000000772cda00000040e00000000039e436284a2edfa00083e00031ee2400000048435e0007c87fc2b656a39400092e4140001f2614000ab6c54ca883a232950dd0b6000065a0000a200012c0005bad2a000000096ad647603614857414c0000127ae8560003ae000d384320001e0902c88000a12bda38c10cd0c1a6a16e0061edf85c487423c7d04aa4cecb63eca9a4f48c0000544000e16be85f42480000ea5ca72a22e0a888a7e60001fa052000552666bc22a04de3eeb740004f8000b2a5c249a59e92632ab0c94e9be918ae8706c4cc4ac74b3c000590880c64000000942d706420000009dc1dc0e684c0000000000000001967e2000386000aa21583f68c20004c400000012421a662646a6e7f20000003a8d8c596da203e000378c9cc8a77016219a98a9ac7f0c56000000000060da8ba48060000e0b8696c3dca3c91cbf84888200005a8154000000a364c8bced78d80b7029293c412834c8622a4588607eccfa23473e7a00008e0522000d26000b1cc96d940ca6243f4a40b4cdce0a4740c34c403e041e314000000b6ed32ae61d21d836c18c0e2000b3884270e990000e10a1c1d41ca51eadaafe58a8a065827c3842feba8630c6281ac2e44acb04e8bea7622a2a78c100004208e497edd2030af46e686c68c5629c40000004b2ab40000002660000aa11281e000000b68a200007d22420007e891e80a25c8aeb2e9e6138c08c7ae023803c0bf437c22000055aa7e00050865475c832bae000bbebb41b00000000006c431c0000000000000000000006e200062c0000000000000000001c600000000089a5849222bc3fe30c00000061200000000000097400066e6fc000af08c8a689ced065b4000000000e0c0006480001c8a7c000a0a5fe99a0000000009701a000047a000c240000000000000002b2d74bf2d46ce443816a3088e64
  | 11 => 0x2949f63a046c9780947528280007d80005bc004350a82034d3c0489d4000000cd20002da0f2000b7800000077c000764000486000000d0a0000ae0001ba7a2a76682cb49984d042e000dea478ad471447490c3c404a34e098022000a644dc80c000dac2fc30400068e40207600093adfe5f0000c5ac7e0002a4000000000000354a922260008d2000b9600080059200000030ed280502ee000000d2c64081c0005e2000000000570000000d10000000684000000000108bdc26ac8ca246b8da000008a6d05b80e80004524b86aa31acec0006960001b800017c00000078200000000093806c000540a30d44de25ce43c00000000000000000000090aad2000000000d04656bac5040008863e63b674c0002c234604c8b47ac34c000a606fa0000000000006180005de91a14e0004fc28ec9083c1ecc3ac981de0000009ec000000000b62b7600000000000067a472000000e1aa1ad52000000c9a000754000b2c0000009e0bca848b08baaa1089c92a5a600000033c000000b5a0000c8d4a0007b24ca9d85ec18a000a6ab5e27e00002e20ea98b2217a550db8000000000518b1a0000002ba000676cb200000025ecc65aaa4c9c81360d8a324700006526ca5a2916078d6e000000000cbc0000007261f800057a000000000ddc9baae45da6ac50c0000000000004340000000b241037a4d80009e8ba000039c6bacdc000244986d862046f20000008f8262da657ec222306a89a853e9a251a17ebc07f48ac2e8092310622a228f43e4a661f4de62604e63da8300000001ce0000000000008640000000009840006bc5360004b03ac79c8360003c600000000040c000a28462d841781da000000000924000000000000000882b9c6de0000000005ea4225d8000c7caeaa54a3405c30266400059a0000007b0000776b002cc670d76df009ea38b1e0da000c60aca000616b44d664a0000dca568214000000a9c7ce2a65e6000000530930b344a42a80009fa366000000948a0815613241a78e0000006d64162f60002784ae04649681879078445c0020000000000000000000003a6000000ade9b2000538d825a069c000000b9a418af83cc9fe01c4920008cac945f69c6000c78000070bde000b6c0e4736482aac5ee5d2000572dd8d6a85c0661ea0009885208da8ec3f80000008ee4986c0000b7e9100006f89b60004d4aa8dc2da4056d40000000288000c00aaa0dc8024507025a48ea00000000000098e37200000020289636200000064a000d6ca060007887da00038200032e9725e8908cf8194d2000078a146b6a96479e000b545d4c26558e1e0bc62e76867cd160b690000000000000008e0008aa000a0299296e000d9e576cc42523b429a25ab266722088d81607d67084a60000000004043208146ee000000d7cbcc0007ea00
  | 12 => 0x9e4d8acaac5e000000b9e63ea3e00000000021c0000000000ecde02642547a47563bc582db6d24000000000d58a9600063416e190000000000cbe0260006043005b60002d8d300008fe00000002800011876e0400001aa3baa6c60e15cc0a0000008e20000000001eeb16b52000c700008b80002d42b8000aec0000000000fa00050200003ac1aa44000000738cde6e800c134bb88a4000a04246b66b4a0003520008242b0000000000b72580dc0c1885e6d2d3e5ae0001a20000002700008cc1b695e0ce4c20006325883342d0b7cac82e0000d5c4be000000aa60c0176000000cd80005788b20008c6000bbc0000001c20000000008d69060000448a8a620be2f858e5fa6f67785e011c72813a016abc06826c46e2c8bc65be0629e2526dae07236aa4aaba44e77a34a660000444000512000000000000000000774000000274000c8e00e00000001a106c3800000088ea2ccc09ee074000d18ceacce000598db40000002e4cb80001d02c4a9024c0003429a04ee000e188bad7ebf65669047226780548f6cc8ba2c6ed0e4b68a2afa99c29c24a8c4adc4fa3120006800000009821b4838000c0eb40a506b20004fe00000078094a8e8b4845a7ee0006da080dc86c2c44b2077e33e08220cb145d050ec8015e0f4c32bc80005560000000000004564540000000009c2368000000000000000000bd8000000000000000a8e0000008fca9e14ab0270a6f41f61c0000812b4e9a656407cb3e3de0b087c1c42ac5f846a54c63a00053a5fc000a72000128000792a0e0008a6ca435c47ec3e000000ac6be295cd4e5483e28460000b8a46d4c62acd43c8b9200019e560b8a46800048c9942be28c7de69a000a5600039820a1be286e12d72e081e80000068703fa54e61c4e0000000000c58ba600000086a24e914000000000a144e24cc4408f05acd884a81e28620007f87449d6a8ab30000000464b0a1fe2dc9cac480fe00073cc0c9327f62e2644b2885876a16c338d6219c898110ccc82c000dc6000de87dc088000328a0000022817078c1989ae7e0ab8cae4943d6000a869667581acce200060a3929446a282e608c6ab5000013c0005c60006dc35674a9aa93e3d297a0001447b40008900000000000000008543446c679a000000000258000000000bfa70c8163c200088432c9f26201d6000000000d9a0000002820007aad5e69e000000c14df6a7028a000bc408c6fe2d6bec3ceb8872c06e92c0009a44c0000000000bd2000000c1200000000090edbe9623be000cf2acc73461a49ec6600096a0000000007a6ac00002f0000000532d1c222
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe73995100047d71995100367571995100047d7099510036797099510004df7359510024dc73595100055c73595100065f73595100247c73595100065c73595100245c73595100047f71595100067771595100047f70595100067b70595100347e75d91100047d75d9110004ef725911001cec72591100347e75d8d100047d75d8d100047f7558d100347c7558d100247f7694d100047d7694d10005757194d10005797094d100247f7614d100047d7614d100065f6314d100265c6314d10005757114d10005797014d100347e75d89100047d75d8910004bf745891002cbc74589100057970d45100057b705451000f7010545100063e65d05100063d65d051000fb010d0510006756590510005b574905100063e65505100063d6550510007375150510007355150510014f47650510006756550510015f0705051002eb77650510006b47650510006b76550510007366550510006b5655051000735655051000635655051003eb6635051003eb46350510007365350510007345350510006b76250510006b56250510007b37050510007b0705051000eb7605051000fb3605051000675658c510005b5748c510014f4764c51000675654c510005b57488510014f476485100057571d41100073541d41100347f76541100047d765411000577715411000735415411001770105411000679658c110007b1418c11000cf8764c11000679654c110007b1414c110007d1314c110007b1418811000cf87648110007b14148110007e121481100247e739941000e3f419941000e3d41994100247c735941000c7f715941000c7d715941000e3f415941000e3d41594100147f70594100147d705941000e3f519901000e3d51990100163f50990100163d509901000cbf715901000cbd715901000e3f515901000e3d51590100163f50590100163d5059010016b71059010016b510590100265f7598c100265c7598c1000e5f5198c1000e5d5198c1000e9f4198c1000e9d4198c100165f5098c100165d5098c100047f7558c100347c7558c100065f7558c100065c7558c1000e5f5158c1000e5d5158c1000e9f4158c1000e9d4158c100165f5058c100165d5058c10016d71058c10016da1058c10016d51058c1000ed91058c100247f7694c100047d7694c100063e6494c100063d6494c100265e6394c100065d6394c100247f7614c100047d7614c100063e6414c100063d6414c100265e6314c100065d6314c10005757114c10005797014c100066e53988100066c539881000e6f519881000e6d519881000eaf419881000ead41988100166f50988100166d50988100066e53588100066c535881000e6f515881000e6d515881000eaf415881000ead41588100166f50588100166d5058810016e71058810016ea1058810016e5105881000ee91058810
  | 1 => 0x120007aa429012001cf87650120007a942501200247e73994200047d71994200247c73594200047f7159420004bd71990200163f50990200163d5099020004bf71590200163f50590200163d5059020016af2059020016ba2059020016ad205902001eb920590200265f7598c200265c7598c200165f5098c200165d5098c200047f7558c200347c7558c200065f7558c200065c7558c200165f5058c200165d5058c20016cf2058c20016cd2058c200247f7694c200047d7694c200063e6494c200063d6494c200265e6394c200065d6394c200247f7614c200047d7614c200063e6414c200063d6414c200265e6314c200065d6314c20005757114c20005797014c2000e76759842000e75759842000eb6749842000eb57498420006765398420006745398420016775098420016755098420006767558420006757558420006b67458420006b57458420006765358420006745358420016775058420016755058420016e72058420016f22058420016e5205842001ef120584200347f76d44200047d76d44200063e64d44200063d64d44200065e63d44200065d63d442000e7661d44200067561d44200047f76544200047d76544200063e64544200063d64544200065e63544200065d635442000e76615442000675615442002cbf76d0420004bd76d04200063e65d04200063d65d04200069e63d04200069d63d042000eb661d0420006b561d0420004bf7650420004bd76504200063e65504200063d65504200069e63504200069d635042000eb66150420006b561504200073551504200247e739971000e3f419971000e3d41997100247c735971000e3f415971000e76415971000e3d415971000e76315971000eb6719931000e3f519931000e3d519931000e3f515931000e3d515931000eb621593100047f7558f100347c7558f100247f7694f100047d7694f100063e6494f100063d6494f10005757194f100247f7614f100047d7614f100063e6414f100063d6414f10005757114f10005797014f1000675655071002eb6645071000db77650710006b7765071000eb7655071000f366550710006b5655071000f35655071000635655071003eb6635071000eb4635071000736535071000734535071000eb76250710006b5625071000675654c710006b564487100063e64d43100063d64d43100057571d43100073541d43100063e64543100063d64543100057771543100073541543100247e73996100247c73596100167a30596100047f7558e100347c7558e100247f7694e100047d7694e10005797094e100247f7614e100047d7614e10005757114e10005797014e10004bf7458a1002cbc7458a100057970d46100057b70546100063e65d06100063d65d06100063e65506100063d655061000735515061000679654c2100247
  | 2 => 0x247e73594300247c73594300047f71594300167a30594300267930594300263e53990300263c5399030004bd71990300163f50990300163d50990300263e53590300263c5359030004bf71590300163f50590300163d50590300169f30590300169d30590300266e53988300266c53988300166f50988300166d50988300266e53588300266c53588300166f50588300166d5058830016cf3058830016cd305883000e76759843000e75759843000eb6749843000eb57498430026765398430026745398430016775098430016755098430006767558430006757558430006b67458430006b57458430026765358430026745358430016775058430016755058430016d73058430016f23058430016d53058430026f130584300347f76d44300047d76d44300063e64d44300063d64d44300066e62d44300066d62d443000e7661d44300067561d44300047f76544300047d76544300063e64544300063d64544300255c73544300066e62544300066d625443000e76615443000675615443002cbf76d0430004bd76d04300063e65d04300063d65d0430006ae62d0430006ad62d043000eb661d0430006b561d0430004bf7650430004bd76504300063e65504300063d6550430006ae6250430006ad625043000eb66150430006b561504300073551504300047f7558f200347c7558f200265e6314f200065d6314f20005757114f20005797014f200074c534cb2000eb66150720006b56150720007355150720007a541487200247e73996200047d71996200247c73596200047f71596200047f7558e200347c7558e200247f7694e200047d7694e200247f7614e200047d7614e20005757114e20005797014e200347f76d46200047d76d46200047f76546200047d76546200063e65d06200063d65d06200063e65506200063d655062000eb66150620006b56150620007355150620004bf745952002cbc745952002cbe76d9120004bd71d9120004be7619120005b5711912002e3e751912002e3d751912002e9e731912002e9d731912002ead721912002eb67119120004bd711912002eb57119120004b5711912002eb970191200347e75d8d200047d75d8d200047f7558d200347c7558d20004bf7458d2002cbc7458d20004f77158d2000cf47158d200063f6494d200063c6494d200063f6414d200063c6414d20005757114d20005797014d2002eac6490920014ec7650920006ac648c920014ec764c920006ac644c9200074c534c920015e8704c9200063f64d45200063c64d45200063f64545200063c645452000677615452000e746154520004be76d052002cbc76d0520004be7650520004bc7650520007355150520014ec7648520007a541485200063f64d41200063c64d41200063f64541200063c645412001768205412002eb8649
  | 3 => 0xf7614c400047d7614c400265e6314c400065d6314c40005757114c40005797014c400066e53988400066c539884002eaf41988400166f50988400166d509884002eac42588400066e53588400066c535884002eaf41588400166f50588400166d5058840016af4058840016ea4058840016ad405884002ee94058840004bd76908400069d6390840006ad629084000e76759844000e75759844000676539844000674539844001677509844001675509844002eb7415844000676755844000675755844002eb67458440006765358440006745358440006b6425844002eb44258440016775058440016755058440016b74058440016b540584400347f76d44400047d76d44400065e63d44400065d63d44400066e62d44400066d62d444000e7661d44400067561d44400047f76544400047d76544400065e63544400065d63544400066e62544400066d625444000e7661544400067561544400063e65504400063d65504400069e63504400069d6350440006ae6250440006ad625044000eb661504400073551504400047f75593300347c75593300047f7558b300347c7558b300265c654cb300047f75587300347c75587300247e76d47300247c765473000e7661547300067561547300463f65d07300463c65d073003e3f655073003e3c655073000735515073003f97315073000755514c7300255e73d43300255c73543300047d71996300167a70996300047f7159630004bf7458a3002cbc7458a300347f76d46300047d76d46300057970d46300047f76546300047d76546300255c73546300063e65d06300063d65d06300063e65506300063d655063000eb66150630006b561506300073551506300367a65542300157b76542300067b76542300257a73542300257873542300057b71542300073b41542300073941542300347e76d95300047d71d95300047e76195300247e73195300247c73195300047d71195300367970195300047f75591300347c7559130005cd7290d30014dc7650d300065c65cc9300059d74cc930014dc764c9300065c654c9300047e76d45300347c76d45300057970d45300047e76545300047c76545300063f65d05300063c65d05300063f65505300063c6550530006b7615053000eb461505300073551505300079541cc530014dc764c53000755514c5300247e76d41300255e73d41300057975941300367865941300247c76541300255c7354130024f876541300367b76541300257876541300067876541300247876541300075b73541300257a73541300257873541300075873541300167b63541300175b63541300075a43541300075943541300075b32541300075932541300057b71541300073b41541300073941541300075b31541300075931541300247e73994300247c73994300047d7199430
  | 4 => 0xd500047f7650d500047c7650d500157a7010d50005797010d500055e73989500055d73989500057970989500053f74589500053c74589500057b70589500047e76109500047d76109500055e73109500055d73109500057671109500057571109500157a70109500057970109500053e74cc9500053d74cc9500265c63cc9500157a70cc9500057970cc9500047e768c9500047d768c9500047f764c9500047c764c9500265c634c9500157a700c95000579700c9500247e73d85500053e74985500053d74985500057970985500055f73585500055c73585500057b70585500053e74185500053d74185500463c63d05500063f61d05500047e76905500047d76905500053d749055003e3c63505500073771505500063f61505500073661505500073561505500047e76105500047d76105500053e74105500247c76cc5500073541cc5500157a70cc5500057970cc5500047e768c5500047d768c5500053e748c5500053d748c5500265c638c5500047f764c5500047c764c5500047e760c5500047d760c5500053e740c5500053d740c5500265c630c5500056e720c5500056d720c55000735410c5500157a700c55000579700c5500047e76885500047d76885500053e74885500053d74885500073541885500073541485500047e76085500047d76085500053e74085500053d74085500055e73085500055d73085500157a70085500057970085500057973d81500073b41d81500073941d81500367970994500047d7694c500367751584500047f76544500063e65d04500063e655045000eb66150450006b561504500073551504500047f7558f400347c7558f40005757114f40005797014f4002eb7415874000e7661547400067561547400073551507400173a40543400247e73996400047d71996400247c73596400047f71596400047f7558e400347c7558e400247f7694e400047d7694e400247f7614e400047d7614e40005757114e40005797014e40005b57110a40005b97010a400347f76d46400047d76d46400047f76546400047d76546400063e65d06400063d65d064000cbf76506400063e65506400063d655064000eb66150640006b561506400073551506400347e75d8d400047d75d8d40005757114d40005797014d40005b571d0d40014bc7650d40004be76d0940014bc7650940014bc7650540006b761505400073551505400247e73994400047d719944002e3f41994400247c73594400047f715944002e3f41594400265f7598c400265c7598c4002e9f4198c400165f5098c400165d5098c400047f7558c400347c7558c400065f7558c400065c7558c4002e9c4258c4002e9f4158c400165f5058c400165d5058c400169f4058c400169d4058c400247f7694c400047d7694c400265e6394c400065d6394c400247
  | 5 => 0x67a539802100678539802100e7b519802100e79519802100ebb419802100eb941980210067a75580210067975580210067a535802100678535802100e7b515802100e79515802100ebb415802100eb9415802100eeb215802100ef2215802100ee9215802101ef121580210147c75593500147c7558f500147c7558b500055e7394b500055d7394b500147c75587500367751587500053e74947500053d749475000eb66150750006b561507500073651507500073551507500363f64993500265c6398f500347e76d0f500047d76d0f500057671d0f500057571d0f500056e7290f500056d7290f500047f7650f500347c7650f500055e7398b500055d7398b500347e7610b500047d7610b500055e7310b500055d7310b50005767110b50005757110b500157a7010b50005797010b500053e74ccb500053d74ccb500265c63ccb500347e768cb500047d768cb500047f764cb500347c764cb500053e74987500053d74987500247c73587500463e63d07500063d61d07500347e76907500047d769075000675619075000675615075003e3e63507500073771507500073661507500063d61507500073561507500063561507500347e76107500047d76107500247f76cc7500073541cc7500347e768c7500047d768c7500053e748c7500053d748c75000675618c7500047f764c7500347c764c75000675614c7500347e760c7500047d760c7500053e740c7500053d740c7500056e720c7500056d720c75000735410c7500157a700c75000579700c7500067561c87500347e76887500047d76887500053e74887500053d74887500073541887500073541487500347e76087500047d76087500053e74087500053d74087500055e73087500055d73087500067561087500157a70087500057970087500265e6394e50005757114e50005797014e5000c7f765465000675615465000eb66150650006b561506500073551506500147e76951500063f64951500147c76551500057671151500057571151500047e76d4d500147e7694d500265c6394d500157a7094d500147c7654d500053e7414d500053d7414d500056e7214d500056d7214d50005767114d50005757114d500157a7014d500147e76949500055e73949500055d73949500147c76549500147e76945500053e74945500053d74945500147c76545500067761545500047e76145500053e74145500053d74145500073651505500073551505500063f64991500057970991500057b7059150005767119150005757119150005797098d500057b7058d500053e7418d500053d7418d500265e6318d500056e7218d500056d7218d50005767118d50005757118d500047e76d0d500047d76d0d500057671d0d500057571d0d500056e7290d500056d7290d500157a7090d5000579709
  | 6 => 0xf315883100ecd315883100675655043102eb66450431006e5625043100db77650431006b7765043100eb7655043100f366550431006b5655043100f35655043100635655043103eb6635043100f96635043103f36535043103f34535043100fa66250431006b5625043100fa56250431006a5625043100fb2605043100fb160504310167a75980310167975980310267a539803102678539803100e7b519803100e79519803100ebb419803100eb94198031006b541580310067a75580310067975580310267a535803102678535803100e7b515803100e79515803100ebb415803100ef2415803100eb94158031006f14158031006b1415803100edb315803100ef2315803100ed93158031026f131580310047f7558f210347c7558f210265e6314f210065d6314f21005757114f21005797014f210074c534cb21007355150721004bf745832102cbc74583210247e739962100e3f419962100e3d41996210047d70996210247c735962100e3f415962100e76415962100e3d41596210047f705962100eb6719922100e3f519922100e3d519922100e3f515922100e3d515922100eb710592210047f7558e210347c7558e210247f7694e210047d7694e210063e6494e210063d6494e210247f7614e210047d7614e210063e6414e210063d6414e21005757114e21005797014e2100675655062102eb6645062100db77650621006b7765062100eb7655062100f366550621006b5655062100f35655062100635655062103eb6635062100eb46350621007365350621007345350621006b541582210347e75d8d210047d75d8d210047f7558d210347c7558d21005757114d21005797014d2100cec764c9210074c534c92100f642154521005b5749052100737515052100735515052101cf4765052102eb77650521006b47650521006b76550521006b5655052103eb6635052103eb46350521007365350521007345350521007a77250521007a4725052100eb7625052100fa76250521007a63250521007a53250521006b541d81210247e739942100e3f419942100e3d41994210047d70994210247c735942100e3f415942100e3d41594210047f705942100e3f519902100e3d519902100e3f515902100e3d515902100eb6215902101eb521590210265f7598c210265c7598c2100e5f5198c2100e5d5198c2100e9f4198c2100e9d4198c210047f7558c210347c7558c210065f7558c210065c7558c2100e5f5158c2100e5d5158c2100e9f4158c2100e9d4158c2100ecf2158c2100ecd2158c210247f7694c210047d7694c210063e6494c210063d6494c210265e6394c210065d6394c210247f7614c210047d7614c210063e6414c210063d6414c210265e6314c210065d6314c21005757114c21005797014c210167a7598021016797598021
  | 7 => 0x81410059d7318141005ae7218141005ad72181410073551181410247e739944100e3f419944100e3d41994410047d70994410247c735944100e3f415944100e76415944100e3d415944102e7541594410047f705944102eb5719904100e3f519904100e3d51990410047f7558c410347c7558c410247f7694c410047d7694c410463e6494c410247f7614c410047d7614c410463e6414c41005757114c41005797014c410047f75593310347c75593310047f7558b310347c7558b310265c654cb310255e73d47310255c73547310463f65d07310463c65d073104e77659073103e3f655073103e3c655073100737515073100735515073102cf7765073103e776550731006b7765073102eb4765073103eb7655073103f37655073103e376550731006b5655073103f34655073100797735073103f94735073100eb6635073103f36535073103f345350731006b5625073103f9732507310079532507310047f75583310347c7558331006b5415833100e76719963100e3f419963100e3d41996310047d709963100e3f415963100e3d41596310047f70596310463e53992310463c539923100e3f519923100e3d519923103e3e535923103e3c535923100e3f515923100eb6515923100e3d515923103eb7315923100eb4315923100eb71059231036766554631006b5645463100d77765463100677765463100e77645463100f36645463100675645463100f3564546310063564546310257673546310257473546310057770546310347e76d95310047d70d95310047e76195310363e74195310363d74195310367571195310047d70195310047f75591310347c755913102cbe74d8931004bd74d89310065c65cc93100cdc764c9310065c654c9310247e76d45310255e73d45310057575945310367465945310247c76545310255c7354531024f4765453103677765453102574765453100674765453102474765453100677645453100675645453100757735453102576735453102574735453100754735453100e77635453100f5763545310075732545310075532545310057770545310063f65d05310063c65d05310073551d05310063f65505310063c655053100735515053100f9431505310247e73994310247c739943100e3f419943100e3d41994310047d70994310247e73594310247c735943100e3f415943100e76415943100e3d415943100e7631594310267531594310047f70594310263e53990310263c539903100eb6719903100e3f519903100e3d51990310263e53590310263c535903100e3f515903100e3d51590310266e53988310266c539883100e6f519883100e6d519883100eaf419883100ead41988310266e53588310266c535883100e6f515883100e6d515883100eaf415883100ee6415883100ead415883100ec
  | 8 => 0x73443545410073742545410073642545410073542545410073442545410057770545410063f6599541005b57199541005b771595410053e75d8d410053d75d8d41005ae7298d41005ad7298d41005b57198d410053f7558d410053c7558d41005b77158d4100db671d4d41005b571d4d4103d3e7394d4103f377194d410053d7194d4103f347194d410053d7094d41005b77154d4100db47154d41004be7614d41004bd7614d41005ae7214d41005ad7214d4100db67114d41005b57114d41005ba7014d41005b97014d4103e3e7614d4103e3d7614d4103d3e7314d4103f1e7314d4103f2e7214d4103f2d7214d4103f367114d410053d7114d4103f357114d41005357114d4103f3a7014d410053d7014d4103f397014d41005397014d41005b57198941005b771589410053e75189410053d75189410059e73189410059d7318941006ad6218941005ba7018941005b9701894100db671d4941005b571d49410059e73949410059d739494100db67194941005b5719494100db67114941005b57114941004be76cc941004bd76cc94103f1c53cc9410053e758c9410053d758c94100db6718c941005b5718c9410053f754c9410053c754c9410071c534c941005b7714c94100db4714c94100db6710c941005b5710c941005b575d854103db673d85410073653d85410073453d8541005b572d8541005b570d854100f3651d454103d3e73d454100d3d71d45410073761d454100f3431d454100f3621d45410053d70d454100f3710d4541005b6769454100eb67694541005b5759454100535759454103db67394541007365394541007345394541005b57294541005b5709454100f34515454103d3c735454100d3f715454100737715454100737615454100f36315454100f34315454100f36215454100f3421545410053f705454100f37105454100f34105454102db67654541005b4765454100db7755454100f37755454100737655454100734655454103db47354541007375354541007365354541007355354541007345354541005b77254541007375254541007365254541007355254541007345254541005b7705454100737765454100736765454100735765454100734765454100737735454100736735454100735735454100734735454103d3473545410073763545410073663545410073563545410073463545410073772545410073672545410073572545410073472545410073762545410073662545410073562545410073462545410073732545410073632545410073532545410073432545410073770545410053770545410073670545410073570545410073470545410073551d81410053e75981410053d7598141007355198141005af7258141005ac72581410073551581410053e75181410053d75181410059e731
  | 9 => 0xd74cc9510265c63cc95100d7671cc9510057571cc9510047e768c9510047d768c9510047f764c9510047c764c9510265c634c95100d76710c95100575710c9510057574d85510057573d85510247e73d81510055f73581510055c73581510367571994510363c539905100e3f519905100e3d51990510363f50990510363c535905100e3f515905100eb6515905100e3d5159051036b551590510363f50590510047d7694c510063e6494c510063d6494c510367b505805100cbc745974102e3f65d53410047f7558f410347c7558f4100cbc7458f410265e6314f410065d6314f41005757114f41005797014f41005ae7290f41005ad7290f410053f7550f410053c7550f4100cbc7458b4102eac4258b4100f36415474100cbc745834102e3f6599741005ae7298f41005ad7298f410053f7558f410053c7558f410053d7194f410053d7094f4102cbe7614f41004bd7614f41005ae7214f41005ad7214f4100db67114f41005b57114f41005ba7014f41005b97014f410463e7614f410463d7614f410471e7314f410471e6314f410071d6314f410472e7214f410472d7214f41047367114f410053d7114f41047357114f41005357114f410473a7014f410053d7014f41047397014f41005397014f4102eac6258b410059e7394b410059d7394b4102cbe76ccb41004bd76ccb410471c53ccb410053e758cb410053d758cb410053f754cb410053c754cb410071c534cb410453e73d47410053d70d47410453c735474100737715474100f3631547410053f70547410053e75983410053d75983410247e739964100e76719964100e3f419964100e3d41996410047d70996410247c735964100e3f415964100e3d41596410047f70596410047f7558e410347c7558e4100cf47158e410247f7694e410047d7694e410247f7614e410047d7614e41005757114e41005797014e4103676655464100d77765464100677765464104d74735464100675635464100577705464100cbe76d51410063f65d514100db671d51410363e659514100cbc765514100db671151410347e75d8d410047d75d8d41005757114d41005797014d410053e75d0d410053d75d0d4100db671d0d4100cbe7690d41005ae7290d41005ad7290d4100cbc7650d410053f7550d410053c7550d4100db47150d4100cbe769094100db6719094100cbc765094101eac62509410053e75109410053d75109410059e73109410059d731094100db67110941005ba7010941005b9701094100575759454102db6749454100f34415454102cf4765454100737545454100736545454100735545454100734545454103677765454100674765454100737745454100734745454100e77645454100f37645454103d747354541006776354541007374354541007364354541007354354541
  | 10 => 0xf3202e9e6450f3201e6e729963201e5f329963201e5d32996320047d71996320047d70996320047f71596320047f705963201cec72592320366e6554a320347e76d95320065d73d95320047d71d95320047d70d95320047e76195320366d72195320047d71195320047d70195320047f75591320347c755913201cde76d4d320255e75d4d320065f6514d320059d7414d3201dce7214d32005d57114d32005d97014d320055e7614d320265e7614d320271e7414d320271d7414d320274e7214d320274d7214d320265f6214d320274f6214d32027567114d320055d7114d32027557114d32005557114d320275a7014d320055d7014d32027597014d32005597014d3201dce7290d3201cdc7650d320055c7550d320366c6594932025ce73949320074c5394932024ec76549320074c5354932024ee76d09320074c53d09320056d7510932025ce73109320074c53109320078d4310932005e57110932005e9701093200c7c755935100c7c7558f5100c7c7558b510055e7394b510055d7394b5100c7c75583510367b50583510363f64993510265c6398f510347e76d0f510047d76d0f5100d7671d0f510057571d0f510056e7290f510056d7290f510047f7650f510347c7650f510055e7398b510055d7398b510347e7610b510047d7610b510055e7310b510055d7310b5100d767110b51005757110b510057a7010b51005797010b510053e74ccb510053d74ccb510265c63ccb510347e768cb510047d768cb510047f764cb510347c764cb510247c735835100eb6719925100e3f519925100e3d519925100e3f515925100e3d51592510063e6494e510063d6494e510265e6394e510063e6414e510063d6414e51005757114e51005797014e5100c7e76951510063f649515100d76719515100c7c765515100d7671151510047e76d4d5100c7e7694d510265c6394d5100d767194d5100c7c7654d510053e7414d510053d7414d510056e7214d510056d7214d5100d767114d510057a7014d51005797014d5100c7e76949510055e73949510055d739495100c7c76549510063f64991510055e73991510055d7399151005757199151005777159151005757198d51005777158d510053e7418d510053d7418d510265e6318d510056e7218d510056d7218d510057a7018d51005797018d510047e76d0d510047d76d0d5100d7671d0d510057571d0d510265c6390d510056e7290d510056d7290d5100d767190d51005757190d510047f7650d510047c7650d510265c6350d5100d767110d51005757110d510055e73989510055d739895100575719895100577715895100d7671d09510057571d09510047e76109510047d76109510055e73109510055d731095100d7671109510057571109510057a70109510057970109510053e74cc9510053
  | 11 => 0x2e3f41997430047d70997430047f715974302e3f41597430047f70597430363e6555343024bc7458b4300e76759874300e75759874304e76539874304e74539874302eb7415874300676755874300675755874302eb6745874302eb65458743006b5545874303e76535874303e74535874303eb6435874302eb4435874302eb4425874302eb7405874301e6e7598a4301e6d7598a430266e5398a430266c5398a43026af4398a43026ad4398a430266e5358a430266c5358a43026cf3058a430347e76d95430047d71d95430047d70d95430047e76195430057571195430363d74195430367671195430047d71195430367571195430047571195430047d70195430363c6595143024bc765514302eb7415844301c7c7558f520367751587520367b50583520265f7598e520269e7498e520269d7498e5201ece7298e5201e5f5298e5201e5d5298e520265e6394e520265e6314e520065d6314e520056d7214e52005757114e52005797014e5201c7c765515201c7e7694d520265c6394d520053d7414d520265e6314d5201d6e7214d52005757114d52005797014d520365c5358c520367751584520367b50580520047f7558f420347c7558f42005757114f42005797014f4202eb741587420047f7558e420347c7558e420265e6314e420065d6314e42005757114e42005797014e42005b571d0e42024bf7650e420347e75d8d420047d75d8d42005757114d42005797014d420247e73994420047d719944202e3f41994420047d70994420247c735944202e3f435944201e6e32594420047f715944202e3f41594420047f70594420265f7598c420265c7598c4201ece7298c4202e9f4198c420047f7558c420347c7558c420065f7558c420065c7558c4202e9f4158c420247f7694c420047d7694c420265e6394c420065d6394c420247f7614c420047d7614c420265e6314c420065d6314c42005757114c42005797014c420063d6550c420269e6350c4200e76759844200e75759844200676539844200674539844202eb7415844200676755844200675755844202eb6745844200676535844200674535844202eb74358442006b5435844201eb7425844201eb5425844201ee6325844202eb440584420167a75980420167975980420067a539804200678539804202ebb419804202eb840580420067a75580420067975580420067a535804200678535804202ebb4358042006b9435804201ebb425804201eea425804201eb9425804202ee9425804201eea325804202ebb415804201cdc735973202e3e759933202e3d75993320269e73993320263e53993320263c5399332026ae3299332026ad329933202eb67199332004bd719933202eb57199332004b571993320263e53593320263c5359332004bf71593320269f30593320055c755
  | 12 => 0xf545865402eb7415865403674539845403677509845403677515845402eb7415845403676755845402eb6745845402e77545845402eb6545845402e755458454036b554584540367453584540367750584540367b50580540367751587530367b50583530063d64952530255e73952530055d739525302c7f76552530255c73552530057671152530057571152530265c5358a530267771586530267731586530267431586530047f70586530047f71582530267b70582530267b30582530267830582530263e53990530263c5399053004bd71990530363f51990530363f50990530263e53590530263c53590530363f52590530269f3259053004bf71590530363f51590530363f50590530063d649505302e3e64550530266e53988530266c53988530366f51988530366f50988530366f54588530066d54588530266e53588530266c53588530366f51588530366f505885300eb6749845300eb57498453026765398453026745398453036775098453036775158453036745158453036767558453006b67458453006b57458453036775458453006765458453006755458453036745458453026775358453026765358453026755358453026745358453036775258453036745258453026d732584530367750584530367450584530267a53980530267853980530367b51980530367b50580530367850580530367a75580530367b54580530067a54580530067954580530367854580530267b53580530267a53580530267953580530267853580530367b5258053036785258053026db32580530367b51580530367851580530063e74584530063d74584530265f32584530267771584530267731584530267431584530047f70584530067774584530067674584530063674584530067574584530063574584530067474584530267773584530267673584530267473584530267743584530267643584530267543584530267443584530067772584530067672584530067572584530067472584530267732584530265732584530267632584530267532584530267432584530067770584530067670584530067570584530067470584530267730584530267630584530267530584530267430584530265f32580530047f71580530267b70580530267b30580530267830580530067b74580530067a74580530067974580530067874580530267b73580530267a73580530267873580530267b43580530267a43580530267943580530267843580530067b72580530067a72580530067972580530067872580530267b32580530265b32580530267a32580530267932580530267832580530067b71580530067a71580530067971580530067871580530267b31580530267a315805302679315805302678315805302e3e74997430047d7199743
  | 13 => 0x100300100c01100000100200300100101700100100100100300000100c00200000700901400000600100b00200800402201100300300300500100001400100300101800300801300000b00001100500200300300d00000000000702100b00b00400e00204001a00200000001002300b00200000000001300000d00000300100500000a00100100800000000000200500000100000300100500000500d00400400000100100200200b00000100f01300000300100700000600000900200300000100000100000100400000000500000500100300100f00100000000500300000400100400f00200100200001403f00000100200300400700b01a00200200b00e00000000200000600200a00000400800500600500000200900400000001301500200e00200000a00300403200200100600000100e00700a02300100300000000300000001e00800300100000000000000100500000100400300000300700800000101d00a00200600300e01a00100000900200100600400100000100100500000000100200002500200c00200100400300101500300400c00101200000300400500400000200000300300600100f00100000500002f00a01100000500000200000000200000000000000200101301600000900100501a00700f00200000300000600c00901c00301600000000700600600100800100000200b00c00500001201500100900800700a00603400100000100d00d00000500101200200000000600200000000200c01000100300000100500100001000b00b00100a00100200200000300600300400000000100400600100803100400802200300000001500a00200000000000200000600a00600100600000400001700200403d00500500700000100100500000002700300101000300900400100b00100200000000300000000900100203100b00a00300700100000300001900400000000200300600201900800100000100000c00401100200100100b00100700400600300000200000000e00901000100700800000e00100300001603200200300600200000401e00000000400200a00400700001100200000900100800200400001000000b00000000300000900300202c04c00300400300100900700000100100302d00000100000000200900c01a00a00300100200c02e00000100200000000800001300703600100400300000200400a01000100a01a00000900100e00102500c00100300500800000d00000101900000100100000002500a00200300000000a00100000000200000601101900100e00700900100000d00300200100500f00400100000600500602902a00000400000600500000000001c00100500600001900000300a02c7c7558f540367751587540367b505835402d3d76d52540363d76d52540053d71d52540063
  | 14 => 0x1fdc00086b0001cdc5bc00000000003bc3a0370166450c7d113e10b4da45370db0a2c7583ba3348b843da2762630e910726c838891040d859419820ec5b43ec3c29fe4bde0fe3950434b1009f08411dce0867f1548c58e3627d3c79e50d964d50c48facab424644c12b400037f05a8294c0489431706a514c8180000a90852479000000107461527a8ae4daa2b64551c5c17e3ae1f5074c90a5ea3e08af40002ab17a8000eba6342cf1ae82742183161bc8ad648e2c78b6c4d87913000eec97e8373fea1c8a5c7ad02b8820cfc0ea27c1fcc398893000068d1141a62fe212908a65230b80000003bc00015103fe55735981084bc6bb1f0800000048b41a89b46e40db20d92a8ea6203000174cd6e3173eb03042b46510630a1c12e58c0620000e841f30558000f6648006999a0f505ab00015343dc1df0000e5464212321087dc17a71f0000758000000038010000085c15801b510e0001c921589360ba29c800000069d2e88b1485c43100000000000001a0000097a76d458211036672115a17dc03600000013b800026200003d0fc87b200012d10a66110dd00007d02450000238f740cc2638000a680000bd80011020001da80010e068023681fc28c0003008994ed87c719309e4a6403c00000000004c04152200e5265a2f60af81942261161f8c0000000000728ed20002d68c40f980cb00014647a881f2de8b0400047400000005be5a600022148f400041b00000000e30001c400540000000ae8e4428804884d80741af0f000005c4000310866cb0624308c1c9cf5e84e0ad85c914400043a01bcfae69f00004eca7c2eb34d9d481ce0740001180af84040d1018d0fa000092054485e1d71149c6000002624e19350461f91ec1c5800013f316a0950c00692ec965c7ec0000001c747104f10d89e60a5804640987f07860002d392a501408912c0920d722174111be07ca000000045066247e3568314fb04ed0e39e8cf2a02d03997388dc2820b39fa0a080c83e41a448920001fe0be40006750001658bae5db00001050e6181421a2205ec5923920a14aa02ec3750c7cb5c7bb00022bcb0a000151000000000000019f400010f12a14c47ea1632e215783922ff0e72048c504a81a20f0856629843610548107813cc93e80004010000f9ccc00001d8800065e4e90ba00010ea4590001f7400068f12f87e09262a8183800090416a0002294d5c85025320203f45264139b50000125096111d0c48972d107605dc00500100000800800700500700000000200100200600c00200b00100200800000100300800500100a00200600100000102400100500000100400100800800600200500000100200100001300100000301700200000000200200000100000500000700100002500a00100900200200000701800600000500500300500000
  | 15 => 0xc18000ac80000a200000f281a27b1abc00022a39c1bc4e320000f8800015a00010e80000008343a3948800076e2e814404024321e217d0c0609d39919c8ab849f19c9b99056396361993c25c27400b8e38d0250b04501d8fca54a02c826810c4973a215fc0bc00000014e0c6e346358800022c6c00d389d4e9600027c90b089439d000000000073d12b02c0e787d411380000007cd0a711cc0006e417c18240003863cb920440a2a00e2047cf7843d3149e8049449408e1ffcd2662b09e80000000000000000b540000000300b0c78c2580000000348000186c66a2ea0f400005623bd04180000006ff1f800001e414a2a1915419e1123740bf4bf675a2851b44b3e3850e19c3006a1382440dd425e0000000000dee0393328fa50c620f2cea038922533177800800054e1e59f380004163a8960005c000155015804478b0000a5cff02f33b7800000000009a1380a2c7c5087000000059a28094303d66623f300740000250ae1b9c0005522d205f0b5e83e22910142da7032500508eae0d039613d0330613257812c0006d61051f100e27c208080004464eb094156c00000000012f04500003119168c0a49020b80c8e72525199921c92c0000f91b8c93011d1e31608df644f089904059412a3c812548723ef3219470f1c00021800000000ed1c0854096200031c9768c2016811593101ec5761388b8ccb25ee00003f00ba3130c10b5067889f1df07a40000001e80000e9a4892958704a2861f1b2857883a6161e504d40004ab33c05e400049200000009485540c3164ca767c60000e100000611508a0cad48a703416e0428000000120c6944661e9000000067a0000000eb000027f00000000af00000007a61dd2e5939400065d1951234000000205824cc822b21059a88a040001080e290843781b1000063c5cc0000c38b6a5892b8917900e89d36c08f452814701005500005a822b1d70c7c2150e5a2648800920001068be41c80531c48000595000045435a0002b6000000076a2d48d74ae00000b618f4f941f410308587200003c2000000071500000006ee4482b0835000004f0f61398ab021f106136865211936e9cd01526fd0f5205c71a6841858594cee31b3a31880e0e000193800011a0f342381acb1a4e13bc10d0a128a81b58df038c7fe0839cbcf3e4143ce20b883e0d70e00de837e5813ac828c8ec0002b31d7c3640001970fb81aa3f4322075078e6eb339953c3ec00315185604a646b01088111421fe0b11decb926502af863ca5e1cd42f8000c081d53528000b8026f0c58488b862241d40a9cd9e7aa04384f0f7c1ab0c506a0f1a0004168c004e00003e9800059e00017f15f400067c00000000984993b3000113c00000000004ae07540e9294b4207a2bb8658e0483d3c38a10d0432301987d444a00000000010a48a40000000
  | 16 => 0xc6a400028685cc608546072a2110421fb19406f8e9c0002f9800000048a000116c3de661000000000000000000000007234018000dfc69e2d013086e674800000e00000072a587402406fa1d3800002887b0de862000031a00000000001a400013dc73242800020a00004e3000000053879e00000006a800022120c4f9627f1b493905b81da05c98d40c45743a50c60e666903b091f4bc688d28d93b00a00c24460d590a844d00011a832840f011800000047b437816c0000003fa0000aa67e11aa886d0d200036311a0bf40001f6891c00000010e0504870000000162800068827802e000033e00006dc0d485509381384c84e82a385dcb7683c3e81784000191000000076c00021515c873445133c82f84ee6ac00014740004cb389867ca4e0bc292042867045f28404c000047000000d0d8402c0001df46d86ec2e90000000000000000113600000000008e489000000000005ba0ec8250cda24018282ec3c4250306134088871e0180d446860000000648e1600021992e90ec25b0a40d8c7224ff18c9df000010620f08b46b035038300000000002e28000e865e50000000d6016e00000000000000000000ef463200019b10ca4ae2ac800000000f2460288aa269500011d400063b0561f8800000026e1d507cc3b83849c80cc60ec2430a240002cd08d061cdec3c12f68694c623471d8042c9e665424780008040661a7858000000009684c40000000000c3ccf630c23c12e4f4272e31100000003a10bc07f416c73e34a222c0006b506c8ad50805fd01f8bdc0000000001afc8b81aa032000065a42b000107015c24d000052c00059818680000000003d29e244c68001199b3462a0001529eb8a34810366000000017f43e16e400038031398a8d6846525d800000085d00018cc00000000000000005be00000006d44fd00000003348462ba8f5460200021b8ea8000111058800000080f34680000000003da000000000117d023c0000000000b9c0001c233897600004a300008e40000000000c210a20e42aa8524baa00017916c87c401a351935c13856800018350702c60f3179069a1331e694549ce0953770208e100d62e680900003da02e14d87922490550ebc0006d700019bc6c868a000143c062000355195800000042d97c40001e719b864ce4a54800000000006bc4331b1c0000000778e2443c0583ab03e400054000000000004710000000b84000000096400045d44d00007046553d88dd8cbe00000000000000003cd0e9400011b0001b88000368456990868200032509e01487700000f44b086853ec80006444d33d807480000000001ce8dea8200e2a09800033412e9de44822d81681b94e60896264a184b601f03f60000a1c61c24f05847448010a6167009a0000000f78000065106a1c4f4c5ff000076c0003a33e48000000000
  | 17 => 0x2e40e5000051f3d111bc0006300b58ff40008483a49cd51045fe1a61b781080c7000000080e0001039d910084060178df855a5a5000130c0001571850f6cd566d9434182d1522bb3ee000070e4c82ae800058000000014440007753132058e807ac11c02a07fe1563da8afc45e7310801338a0a2960000df4f5644c1309ed8db829100008ec1680000000000d38864000196000000000000000004db00011fc0140362ab1850e0200006d00007f4000323000094e46140a108c0000001a11344ae618000000004b40001ee8e6cee47d21ee223d066755000000000037b14e9e9cf7033200010946bc00026c800001a77127903b80ce467000028059200011f215c0000003bf80000000002e50000768000000000000000000020440000003b58cd81300001c180010360000001a5851c7f028918640000000de15e4000000000000081840d00001f4a821ac06e10ec61200010717d828600044a9cecd7a00900000009d42af0000000fda0000000000e4c00002295b800000000000004440000001b244f62d100002580004d637480000004cc360800000000017e1c3c00000000012cc6560fa129000000020200003f486a5cf00588c0fc08150001b402ea71c0000398eee64c232040c000280000216400087e00013ed1561450ac8edcba829e44e0f14c1e000000000069c3570408c8108264926f96c41d25c60001fd469271a0440018a927800000000000295000000036a000386800000081e0e8a1e00240002139facf2c000426800103200030c00a44d62d531f80000000001efa01897c0003c98000b8e00025c045c0a80e10001a64a0e00022980000000001e600005da000000000051e00011f8000000567000037cfdc1a0000199cd42454436800000000021e216094489121300000ee29918880002088050829a4800009e17808d8ff80000000c48e1c15200010fcad23bf3538000ec43d6294800053e000000000047882f3cd8000a0066b1a5800000046900021240222810000424000000323a168f047730c680001a41691fd95306e02191b68e787644580b893291061a126a00000004363fb22804b87e934c000000033f13d18680006a60cc9e741e25df305093800000000005001ea0003db804cc6c0f00c801e109e05243d0000c807fa31787946e20493039758fd462515c1c2857836719e9878f0c0850ce8000ec084b0bb0d6cf802cb1641e9052068e0700b90c100992899a689f85200070d7cbbc12b2509a30cb80001f220707720003c1857c1166fc0e78f644402f400008b8fe41e100020250fe23743700000003c80b301f800026a00016dc88c2e6000000000004a23e000000016f1220000c8a00020000000002662da00000000a10001bd000076500021e42040000001af81b000040580f89ba000412000000024b377a28
  | 18 => 0x145c0007502bf1774716000205099c58828a1d30dd0bc43f73670000424000039114016665e1a29088bf05e00cb9e288486a907b9a2c8402f103016f03760000d80adcf7e7631fc0b642ba2e501d90490bc3f23c916d910c3e33769f0cd0e7e7294146059807b066979833824c17018481ba75e19d0478ece56543507704341852f80c082e02d313f1c14d404184180c0cbd002709497ac6587bd29e0a480325e72d6000032a00008800200006893bb05e899e59b2b01f3ce9e6b61109d148c66a81288e7cc7088915620b06764c1262963905271400008446282730000c74bf2000000000000083f1f01064da658b1d680110ee3242b692d8a546f93d49bccac453a2d184c87564e222715bc35c0b22560f5c29a28c28308d111c1371d981b8a8a23130709b802a4d806f115c1d60f806492105344113dc81443725233ed8fc47180e84191998d943ce0218ea414e6c44010e4cfe210c1b786788c43613ad811cc0c1212ee1bc00006481300338000153000000003000043380007f239c00000000000001638000c480e229a8ba4fbc00011a9d304740000000000000000061993800066429f807c13600000022480000001c79ae006e4093c422b002c35924e9cb400000009f08002fa2321b0140c00000036d9b84fbe000048061087c5bf32d8554d063c021d00000004b51e7817c81c1e405b8000d8a0000001ca08860530000000000000000000101a2420000000ed05422e0893c00049a1bc9cac2fc01031e000007a0000001b680002c30000e6072e14f22286d06a60002fa97a400000002a8b5ca3c4b70000c18fb400035919c06b413931d078c4e4000236000005669706880000002e804614c0b2084c1099cfc00080c3ba00305f60ff3a0937800020900f15ec0001b81ff0b089647d5209995cca60003370000090578000112c0003f300009a0cd40fb002863800000035214840000800000db8b6628d26680005367ef09300705ac31c3431644a7a7fb00019d00f800033b00005ba64b0000000c3a25500022b80007360001b7c6b826926901106cc52d16700005260000000c942c80003bf0000b0e5630000ab8000000014100c00005a00013bc54c57a00006305a470
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xb498290d504c0098b0ed992a098002c661332541300262c3b264a826008c3876d05504c00f870eca0aa098003c450731541300252a41aeab086000c35755d1610c00146b03322a218013071cd64544300262639ac4a886004c5473585510c00146b0332a82180028de1951504300051ac32a2a086000c3776545410c00186aeca8a821801ec520d515043000713312a2a086000e2562545410c0098acc6b88a7900031558d7114f200262d31ae029e4000c59635c053c800168b0229a6590002d2600534cb200242e41aeca8c4000a3581995418800146f0ca8a83100028d61951506200061b42ae23224000c35855c4644800146b02324a6900020f61c6414d200051ac08c829a4000c37645c45348001868c8b88a6900030ed917014d200061c322e029a4000aa581192324800154b02322649000383190534c920005a2c08a69924000b498014d324800146b02326a2900028d60464545200061b3b2a2a0a4000c3476545414800146b02326a0900028d60464541200052ac08eab184000877865c4530800186cc8b88a6100030d5917114c200262b31ae22984000c55635c45308001874c8b80a6100030e5917014c200262d31ae02984000c59635c053080010eb0e29cc2100029c60053984200061abaae8b0840008758714d61080014e30029ac2100028d60664544200051ac0ccaa084000a3786545410800146b0ca8a82100030ddd951504200061abb2a2a084000e16635454108001c2ac6a8a82100030d9917114f100061ab22e229e200487b865c053c4001874c8b80a7880030e5917014f1003d1a41acaa0e2007a378694d41c400146b0c29a8388002cc60053507100061ab22e3a862004877865c453840018aec6b88a68800316d8d7014d100242e41aebb122008a1c8359741440134a906b2c82880028d606655051003d0e41acaa0a2007a5483595414400146b0a3b28288002cc602655051003d4a41acaa0a2000b1483595414400166700b2a828800385e0d655051003d1a41acaa0a2000e1483595414400f42906b2a82880028de01655051000719c02caa0a2007a378694d41440016630129a82880028d618535051003f0a318a6a0a2000b318014d414400146b0bb1282880162d21d6250510005c8c18e0a0a2000ba1821c141440094a906b2c62880030d595748c5100243a43aca98a200485c835d9504400186aeca0aa0880129620d658c11000718b2a831822004878875953044003960eca0a60880038c595414c11000728b2a6298220009b08750520440090eb02bb0a6080121e6017614c100061b322e22982000c35645c453040098acc6b88a6080031558d7114c100061d322e02982000c39645c053040098b4c6b80a6080031658d7014c1000532c08a73102000a698014e62040014cb0229ac4080029a6005358810
  | 1 => 0xd07b82a2a0802c5e0d70545410058a41ae0a8a8200d27725456050401a48e4a8ac0a08024de1d51181410068b39aa23028200d15735446050401a4ce4a88c0a0803495c9511814103d8b41ea2a0e6207b148354541cc40146b0bbb283988028de1562507310061bbaa82b066207c3673591518c40f868e6b22a3188030d59370546310051ac20eca8a620687487591514c40168b0439aa298802d460073545310262a3b664a8a6200954874c9514c4098a8ec992a2988228d21951d053103d1a432a2a0a6207b1483545414c40f46d06b2a821881e8d20d65504310051bc02caa086207e2653589410c40fc48a6b1282188129620d7558031007193aa82b006200e3175505600c40fc64a6a0ac01881f8c14d41580310262b31ae229e4200c55635c453c84098b4c6b80a7908031658d7014f21005a2c08a69964200b498014d32c840186cc8b88a7108030d5917114e210061d322e029c4200c39645c0538840f46906b2a83108028de01655062103d1bc34a6a0c4200a358614d41884016630029a8310802d1604534c921005a4c00a69924200a35851d941484016630029a8290802e160c7250521005d0c00e4a0a4201aa4864c94148401e08a69928290802966007558c210061b322e22984200c35645c453084098acc6b88a6108031558d7114c210043dc32e02984200c3a645c05308401872c8b80a6108131698d7014c210062cb1ae029842008798714e60084014e30229cc0108021e61c535802100538c08a6b004200935819d332d400f46906b0a83a801f0ddd941cc7500061aba2c318ea000c357650431d4001a4ae4a0863a80034c505700c7500061abb28310ea000c357458421d40018aae6b0843a80031c585700875000d1bc32a2a0ca000875811d9435400126b023a2c4a80024d60674cc95000598c04c2a0aa000b1483585415400166700b0a82a80034c50570cc5500262631ae418aa000c3576504315400fc28c6a0862a8003495c9410c5500262c31ae018aa000d31415c031540090b906bb442a80030d5d941885500051bc32a2a08a00485c835d9519000146b0332a83200028de1951506400051ac32a2a0c8000a55811d563100010ef0cb88a6200131598d7114c400062ab1ae22988004c5a635c053100018b2c6b80a62000299604539884000534c00a73108000a658114d62100014d30029ac4200021d61c539844000538c00a730880008758714d61100014e30029ac2200068d61161544400051ac0ccaa088000a37865454110001c2cc6a8a82200038558d515044000713312a2a088000e2562545411000f4690ca8a83980028d60665506300051bc32a2a0c6000a3586545418c00f62906a8a83180028d60465505300051b432a2a0a6000a3486545414c0016330839aa098002d26087354130005a8c08e6a826000
  | 2 => 0x53584420043cc38a73008400a718114e60108010f30e29ac0210029c60453580420061b42ae33266400c35855c664cc80f86ca6b8cc99901f0d14d719933203e53192e33266407ca5325c664cc8012ab023aa879900345a117114d320068ac22e229a6400d46825c4534c801a8b04b88a69901351d897114d32006a5412e029a6400d49825c0534c809a96c4b80a699002556047550d32005a2c08a72926400b498014e524c80161b0829aa499002d16045354932005a4c00a6a926400b458114f424c8016930029e84990025361c5310932005a2c08a62126400b498014c424c801a1aeaa1884990035114d7110932006c2a1ae22126400d48535c0424c801b1286b8084990024d60674ccb510061b322e229ca200c35645c45394401874c8b80a7288030e5917014e510049ac0ce831aa204c4c635ca435440126b033a664a88130718d74cc9510262a31ae3992a204c56635c453d04018aac6b88a7a08131698d7014f410062cb1ae029e8208d0c535ca63d040f94ac2b94c7a08024d6047558f410468b31ae229e8200d15635c453d0411a2e64b88a7a08234698d7014f410068cb1ae029e8208d1b325c053d0411838a6bb665a0802c5604534cb410058cc00a699682098748758d519040126d0fa1aa2a08068da1a435454103e8a39c86a8a8200b268290d515040164b0521aa2a08024d21d435454103e8a39a86a8a820093687109515040162d06212a2a0802c560c42545410059940084a8a8200b3180109515040126b033aec6a08024de057094d410461b432e229a8207c35865c4535040fa2e64b88a6a08024de017114d4103e8d992e029a8200d32815c05350401a6302b80a6a081f4ccc57014d4103e9818ae029a8200935819d46250401952c4b80c4a08162d60676cc9410049ac0ceb1928200935811d5325040162b0229a64a0802c6600534c94103e8b398a7b0a8200b318014f615040fa2ce729ca2a0802cc60053945410049b43ea6a8a8207d147394d51504032690ea9aa2a08028da18535454100593410a6a8a8200b258214d51504016650029aa2a0802cc600535454100c9b43ca4a8a8200b1683949515040162b07292a2a0802c5a0e76545410058ac1ceca8a8200a36861cd515040fa2ce639aa2a0802c9a08735454100592c10e6a8a8200b32801cd51504016630039aa2a08024da1f635454103e8a39cc6a8a8200b268298d515040164b0531aa2a08024de1d63545410049a43ac6a8a8207d147358d515040162d07392a2a0802c560e72545410049b438c4a8a8200b1683189515040162b06312a2a080389588625454100599400c4a8a8200b3180189515040146d0d992a2a08028d61b325454103e8a39e64a8a8200936878c9515040126b0f192a2a08024de1d32545410049a43a64a8a8207d14734c9515040f26
  | 3 => 0x7800448fe001ce00026000002202a00000e400043800002000000000000001ca00000001a4000ae000009d0aa0020c003026fa90a815e210f059aa20026aef0000000000242000000029455a860026400036a2b6ad89b400000000009f97a00186bf00000120003320000000000ce800000005ab5e00000000008daca00000ae1061e000000a67b0006a22c00364508ca0f2a60000035000d580000000000000000000182000002dace003920000012a48000000000023000c4000000005620471800b40000020e000000000000000001620000000000c91140006a000123a80000000c0000000000000000000000000014c00054003ac000000000000100000000808000000030000120080080100000c01800000004030000080000000100600c00001000004018000040000080200201c000040000100080000400000001002000000000000080000100000c00000002000010000020000200000000401000002000020020020000080000000400001004000000010000000200000000c000000000000000000000000000000000000000080000080200800000000000000008030020000000000000403000000000000000060100000400000000000000008008000000000000000000000000000010000000000000080200200a3581d51619500f46b033a2c2298228de0574584530252b41ce8b08a608e16839d16114c01c2b073a2c22982385cca74584530061bc3ae8b08a607c36735d16114c0f868e6ba2c22981f85cc974584530051b426e4b08a600a3584dc96114c0186ae9b92c22981295a0e72584530061aba2e4b08a600a36841c96114c0146b08392c22981295a0c725845300539400e4b08a600a71801c96114c0146d09b82c2298028d61370584530061aba6e0b08a600c35745c16114c094a906b82c2298028da1070584530051ac20e0b08a604a56831c16114c014cd04382c2298029960870584530252d418e8b00a600a6a821d16014c014d3043a2c0298029ca04745805300538c08e8b00a604a5a839c96014c0147708b92c0298028e21172580530051d420e4b00a600a39841c96014c094b506392c0298029ca04725805300538c08e4b00a600a3a849c56014c014730938ac0298129620d71580530051d420e2b00a600a39841c56014c094b50638ac0298029aa08715805300534c10e2b00a600c36845c46550c0186b08b88caa18131398d7214e520262b31ae229ca400c55635c453948098b4c6b80a7290031658d7014e520262b31ae229c8400c55635c453908098b4c6b80a7210031658d7014e420052ac08eab188400a59801d563108010ef0cb88a6210131598d7114c420062ab1ae2298840087b865c053108098b4c6b80a6210031658d7014c420043ac38a73088400a718014e61108010eb0e29ac2210029c60
  | 4 => 0x5c80000044a78000023200000000003780000000ea1f80004600000002880000000000cf80000000000003d102002b000074000000000094800b00000035a3e80000000000009d800278000d022b6800001105519ed13609c8006d80031800bd18c058ce09000e823a879f45c1fce511a743be000620000069800003b0d382e788000030e0001c888000017e000000037c000000000000000000000000000000000001a0e60000002800001d60000000194000cc0000000000002d200000000009391c4c0006b0a08a000000000000062800b2090e7000ba27000000999ba6f3cc002de7635c61316001c8e7800002b2000d8000fc000b8002980f80030ae0000e00000000000001983a2823c9e0000005380000000000001c000003a41680000372000000029cae80000000be96c00000b7000003047900089b5000042030000036ee1230000000000000092000000000000000001ee00118000002f8000000000000000001480030000002c400000000002600000000000004325e002a400000000000008acdba20012e0012a8923c0006c2b000000004f2ac000000013800072988000000000000001168226e6c0ee5d8b2bf800a021cad880138000000000000f0900000000019203af0af0005212800000000000009ad0800732ee93064be00079800d2000ce1b2000000001a8839ae2800000000000049800000009600000000c7000da216000000000017000808000031e75104abbca000000000032000e9acc000009f3c066800000f8161a200000000000001095882002c600000c980000178000000018ee000000000c5000d6000cb8002515c358000000000168a68000018800000cf00082800cd37600000950e45f000000000014a0180000000911de0000000000c3000000008e00029000b08007f800748000000092a6c5b800000300037e00000000f6d29fa0000000000000006b8000000000136000000000000000478bc00000000000000070000000004b00000000000000000000000002d80000019800ee108de3662e8000000000000002780000000000d50004e8000000000000f1800d187c001b800000c8b96000008a9221207e000005480000000510001e800980000016036840f523e143d04c8000006e00000342d40000051bbaea8000000071000a48b0000000021000000c22d68601800000311c2000000000000020ec9900021a0025000000850000000000000ad0000025a6700000370003c4af950ed0000028e5d0b449268e19f66a80000296000000000000000000081300000000e380000000000001800037000000000a0007a02c568000000000000000000013400000002a8003d2000007c000e234000000de80065bce000320035200000002f600004c49da0000000234c830a590000009c001800
  | 5 => 0x3300010a2a1a0000000000000000000000000025a46d300000000773987aae2a30000037400000000000000000000000860038c0000081940002e438bc80000000000000000e00000000002e600000002400000200328000009eaf217aaa002ec00000c68004f8009732a000000000000000c183a000eca10d20500000212edb188b80000056eb80000000db0001d800000000008eba8007cb8228b2c000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1e8c10024742a03e040000000180200000000006803444000268401636300080000b80007110a161c0150024f060850c0e320002400000000c200303d05a4f875d16114c0f814835d170584530048c644845c96014c01905846097114d3200542251825c0534c8011459814d711093200550640535c4424c8011499814d701093200550644535c0424c80f9047360a435454103d4424d815c0535040f9127360053d854103e411cd8298d5150401a2162600625454103e051cd86cc9515040f610935d54158031005c0640534c9414840fc04635c9410c55003f0418d415c0315400f414935d9418855003c8524d86545419000f414935d5745843003e0520d76545410c00fa0483589515043003c8524d865454188001035981917114d200050c644645c0534800120d98190534c920005816446414d3248001a0464604534c920006821918014d324800f21493617625051003d0524d655d2314400f414935d9415411003d8424d65506304400f43097595414c110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x1400002501a1251825c0534c801102d48c8c08a69924000a8068464600534c920
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x1
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0xb8c
  | 8 => 0x184c
  | 9 => 0x148c
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 68
  | 6 => 1812
  | 5 => 2225
  | 4 => 491
  | 3 => 36
  | 2 => 3
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
  | 7 => packedAt gbK7 (1944+((h/22+packedAt gbK7 (1768+(h % 22)*8) 8) % 170)*8) 8
  | 6 => packedAt gbK6 (74292+((h/604+packedAt gbK6 (67044+(h % 604)*12) 12) % 2631)*12) 12
  | 5 => packedAt gbK5 (115692+((h/741+packedAt gbK5 (106800+(h % 741)*12) 12) % 2938)*13) 13
  | 4 => packedAt gbK4 (30762+((h/163+packedAt gbK4 (28969+(h % 163)*11) 11) % 1146)*10) 10
  | 3 => packedAt gbK3 (2592+((h/12+packedAt gbK3 (2520+(h % 12)*6) 6) % 57)*7) 7
  | 2 => packedAt gbK2 (246+((h/1+packedAt gbK2 (243+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x18701c3f8c61e1c0ffc7e0fe0ff038878474cf
  | 1 => 0x1f801fc7f07e3e00f078ff0ff0f921199a4b33
  | 2 => 0xe0001ff87f803fff007f000fff01c61e638c3c
  | 3 => 0xffffe0007fffc000007ffff0000e07e07c0fc0
  | 4 => 0x7fffffffff800000000ff8007ff000
  | 5 => 0xffffffff8000000000000000000fffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8110408800040401401208204400882801045
  | 1 => 0x14820a4520323204a1085404c0a921090a4112
  | 2 => 0x2004509014800492005202292a004614208c28
  | 3 => 0x4120c0005d44800a02648a6022020220740e80
  | 4 => 0x40882046a79392ccb000c40402fb0005f6000
  | 5 => 0x9e4f1f26001010308c0010818ccdfddf800000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfffaffe8fefaeee8fffaffe8fefaeee8fffaffe8fefaeee8fffaffe8fefaeee8fffaffe8fefaeee8fffaffe8fefaeee8fffaffe8fefaeee8fffaffe8fefaeee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_14258
namespace PEqualNP.Outside.L_meta_14258
open PEqualNP.Outside.L_meta_14258.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 1 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 5 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
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
theorem bs5_4_0 : Interval s5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1 := bs5_4_0
theorem alls5 : ∀ k ≤ 4, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 3 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 36 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_480 : Interval gbAtlas 4 480 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 491 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 bgb_4_480))))
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
theorem bgb_5_2208 : Interval gbAtlas 5 2208 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2225 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)))) (concat (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))))) (concat (concat (concat (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344))) (concat (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))))) (concat (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)) (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))))))
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
theorem bgb_6_1792 : Interval gbAtlas 6 1792 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1812 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 68 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 1 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 7 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 6 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffffffffffffffffaffe8fefaeee8ffffffecffffeeecfffaffe8fefaeee8fffffffffffffffffffaffe8fefaeee8ffffffecffffeeecfffaffe8fefaeee8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) SB :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) SB :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) SB :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,64,192)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,64,192)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_14258.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,6]⟩,⟨.and,[2,5]⟩,⟨.or,[0,1]⟩,⟨.or,[4,6]⟩,⟨.or,[11,7]⟩,⟨.and,[10,12]⟩,⟨.or,[0,7]⟩,⟨.or,[4,5]⟩,⟨.and,[14,15]⟩,⟨.or,[8,9]⟩,⟨.or,[17,13]⟩,⟨.or,[18,16]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_14258

open PEqualNP.Outside.L_meta_14258 in
theorem PEqualNP.Outside.L_meta_14258 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
