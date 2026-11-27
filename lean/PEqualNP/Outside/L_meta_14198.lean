import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_14198.Model
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


end PEqualNP.Outside.L_meta_14198.Model

namespace PEqualNP.Outside.L_meta_14198
open PEqualNP.Outside.L_meta_14198.Model
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

end PEqualNP.Outside.L_meta_14198

namespace PEqualNP.Outside.L_meta_14198
open PEqualNP.Outside.L_meta_14198.Model
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
  | 1 => 0xe0fff07c1ffff8783fe1e07fc3c0fffeb3333f
  | 2 => 0xffff801fffff803ffe007ffc00ffff3c3c3f
  | 3 => 0xff03ffffe07c1fffc1ffff83ffff0701cfcfcc
  | 4 => 0x3ffffff801ffffe000003fffff801f00ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x892913212529083a0aa12525424a4954931315
  | 2 => 0x5252241a4a52138415520a4aa41492a92c2c2a
  | 3 => 0x401841080300208840644300c886040c05454c
  | 4 => 0x9ce38a53101b5d56a61110633338e031f00ab0
  | 5 => 0x18830c639c639e6739999c702220c0c1fab000
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_14198
namespace PEqualNP.Outside.L_meta_14198
open PEqualNP.Outside.L_meta_14198.Model
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
  | 0 => 0xf8787fc7c3ffffe187ff0e0fc387ffff3930ff
  | 2 => 0xff807ff803e1e3fe0787f00ffc07871fa63c93
  | 3 => 0xffff87fffc01fc3ff807fff0fff807e0c7cf1c
  | 4 => 0x7fffffe003ffff80000fffff800f80fe0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xa00804204808000810a02410080a188091025
  | 2 => 0x91353491a953462e42c590aae4351256a62c92
  | 3 => 0x20101100804400420801242049100442024518
  | 4 => 0x8546662522104ab554d08108b2665004f00ac0
  | 5 => 0xc664443633999339e766c9cc20446098fdb000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xffaaffa0ffaaaaa0ffaaffa0ffaaaaa0ffaaffa0ffaaaaa0ffaaffa0ffaaaaa0ffaaffa0ffaaaaa0ffaaffa0ffaaaaa0ffaaffa0ffaaaaa0ffaaffa0ffaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_14198
namespace PEqualNP.Outside.L_meta_14198
open PEqualNP.Outside.L_meta_14198.Model
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
  | 0 => 0xf8787fc7c3ffffe187ff0e0fc387ffff3930ff
  | 1 => 0xff807ff803e1e3fe0787f00ffc07871fa63c93
  | 3 => 0xffff87fffc01fc3ff807fff0fff807e0c7cf1c
  | 4 => 0x7fffffe003ffff80000fffff800f80fe0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xa00804204808000810a02410080a188091025
  | 1 => 0x91353491a953462e42c590aae4351256a62c92
  | 3 => 0x20101100804400420801242049100442024518
  | 4 => 0x8546662522104ab554d08108b2665004f00ac0
  | 5 => 0xc664443633999339e766c9cc20446098fdb000
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xffaaff88ffaaaa88ffaaff88ffaaaa88ffaaff88ffaaaa88ffaaff88ffaaaa88ffaaff88ffaaaa88ffaaff88ffaaaa88ffaaff88ffaaaa88ffaaff88ffaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_14198
namespace PEqualNP.Outside.L_meta_14198
open PEqualNP.Outside.L_meta_14198.Model
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
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 1 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 2 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 1 => 0x1224284484922512
  | 2 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 23 s3Pos s3Neg, 0xeaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_14198
namespace PEqualNP.Outside.L_meta_14198
open PEqualNP.Outside.L_meta_14198.Model
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
  | 0 => 0xf8f0ffc7fffc7e1c71c0e3fc7ffc1fe10f3cf
  | 1 => 0xf00ff1ff878ff8fe07e00fc7f8e1fe1e633d33
  | 2 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 3 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x40118004220208008204820901304088105045
  | 1 => 0x52228891414810a0521244248449414612512
  | 2 => 0xaa444512412900354802489092092941828a28
  | 3 => 0x230064a01101924651486000e48c0c44a40f80
  | 5 => 0xcc088903664e2499a6938f24001031995bf000
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8ffe8ffe8eae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_14198
namespace PEqualNP.Outside.L_meta_14198
open PEqualNP.Outside.L_meta_14198.Model
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
  | 0 => 0x1e3e3c7ffc7ffe3f0c63831ffc7ff83f00f3cf
  | 1 => 0x1fc03f8e3f8e3fc7f07c03e38f8e3fc7334d33
  | 2 => 0xe0003ff03ff03ff8ff8003fc0ff03ff8c38e3c
  | 3 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 4 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2004400040000400000800480120800001045
  | 1 => 0xc4148944492854085064292124849286314512
  | 2 => 0x1a912289244a801ac80524849212530c28a28
  | 3 => 0x488c032520240c92352918000e498192540f80
  | 4 => 0x9130204803493124ca52639260000624abe000
  | _ => 0
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_14198
namespace PEqualNP.Outside.L_meta_14198
open PEqualNP.Outside.L_meta_14198.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x99597818e1680070f8a01079d9c988b151702091b1d0a9a99801b930480938012841a0e9e8280201e03058005001f000c0003901c11960800209f990b8d068f141486120010800d80180c800000110885060e0808200000870210402009c0081608480007fd50017f54007f95001fd54005f55001fc54007fd4c01fe53005f94c01fd53007f14c017c53007fd0c01fe43007f50c01fc43007fd4801fe52007f54801fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd40017f50007f94001fd50005f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x44000fec8220005feca90002fe65480017eb2a4000bf19520005fec890002fe64480017eb224000bf19120006fea8900037d54480017fb1a4000bf98d20005fac690002fc6348001bf29a4000df14d20007dc8490003ed4248001f71924000fb4c920005fec290003f761480017bb0a4000bf18520007e8c290002f46148001f790a4000fb48520006fea0900037d5048001fd9024000fb88120005feca10002fe6508001bf32840009f99420005faca100037d65080013eb284000bf19420005fec810002fe6408001df3204000af99020005fac810003bd64080015eb204000bf19020006fea8100037d54080017fb184000bf98c20007bcc610002de63080017eb184000f758c20005bac610002fc6308001bf2984000df14c20005fcc410002fe6108001fb3084000bd98420005fac210003f561080017ab084000fb88420007d84210002fe6008001bfa804000df54020007de4010003fa2008001f69004000fe48020005fecb88002fe65c40017eb2e2000bf19710005fec988002fe64c40017eb262000bf19310006fea9880037d54c40017fb1e2000bf98f10005fac788002fc63c4001bf29e2000df14f10005fec588002fe62c40017eb162000bf18b10007ec8388003f541c4001fb18e2000fd4c710007ec4388003f521c4001bfa862000df54310005fecb08002fe6584001bf32c20009f99610005facb080037d65840013eb2c2000bf19610005fec908002fe64840017eb242000bf19210006fea9080037d54840017fb1c2000bf98e10005fac708002fc6384001bf29c2000df14e10005fec508002fe62840017eb142000bf18a10005fac308003f72184001fa10c2000bf98210006fea1080037d5084001fd1042000fe48210007ee2108003fb10840017fb2a2000bf99510005faca88002fc65440017fb222000bf99110005fac888002fc6444001bfaa22000df55110005fec688002fe63440017eb1a2000bf18d10006fca6880037c53440017fb122000fbd8910005dec488002fe62440017eb122000bf18910007d8c488002ec6244001fb20a2000fd50510007ec6288003f53144001fb10a2000fd48510006fea0880037d5044001fd1022000fe48110007f62088003f610440017fb282000bf99410006fcca080027e65040017eb282000df59410004faca08002fc65040017fb202000bf990100077cc808002be64040017eb202000ef590100057ac808002fc6404001bfaa02000df55010005fec608002fe6304001ef3182000b798c10005fac608003dd63040016eb182000bf18c10006fca6080037c53040017fb102000bf98810007dcc408002ee62040017eb102000fb58810005dac408002fc62040017f3082000fdc8410007e84208002fe6004001bfa802000df54010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x2fe6310001ef3188000b798c40005fac620003dd63100016eb188000df94c40006f8a620003be4310001de2188000bf98840007dcc420002ee62100017eb108000fb58840005dac420002fe6110001fb3088000bd98440005fac220003f561100017ab088000bf98040006fea0200037d5010001dfa008000fe900400077a8020003f940100017fb2e6001dfd9730004fecb98002fe65cc0017eb2e6000bf1973000ef8cb980027c65cc0017fb266000bf99330005fac998002fc64cc001bfaa66000df5533000efca7980077c53cc001ef21e6000f750f30005fcc598002fd62cc001ef9966000f74cb30005fcc398002fd61cc001ef98e6000f74c730006fea1980037d50cc0017fb2c6000bf99630006fccb180027e658c0017eb2c6000df59630004facb18002fc658c0017fb246000bf99230005fac918002fc648c001bfaa46000df55230005fac7180037e538c001be29c6000bf98a30005fac518002fe618c0017eb0c6000bf98230006fea118003fa508c001bea846000fe54230006f2a118003fa408c001fca046000f7cc230007f66118002ff654c001bfb2a60009fd9530005fcca98002fd654c0017e32a6000df19530004f8ca98002ff644c001dfb226000afd9130005fcc898002fd644c0017e3226000ef1913000578c8980037f544c001beaa26000df94d30006f8a698003de434c001eea1a6000bfd8930005f8c498003df324c001ee9926000bfd8530005f8c298003df314c001ee98a6000dfd4130007f4a0980037d504c001fca826000de54130007f48098003f9404c001fd9826000f78c130005feca18002fe650c001bf32860009f99430005faca180037d650c0013eb286000bf19430005fec818002fe640c001df3206000af99030005fac818003bd640c0015eb206000bf19030006fea8180037d540c0017f3186001df94c3000ef8a618002fe620c001f73106000bb98830005fac418003ed620c00176b106000bf98430007ecc218002f6610c0017eb086000fd58430005eac218002fe600c001bfa806000df54030007be6018003fa300c001ee9806000fe4c030005fecb90002fe65c80017eb2e4000bf19720005fec990002fe64c80017eb264000bf19320006fea9900037d54c80017fb1e4000bf98f20005fac790002fc63c8001bf29e4000df14f20007dc8590003ed42c8001f71964000fb4cb20005fcc390002fd61c8001f790e4000fb48720006fea1900037d50c80017fb2c4000bf99620006fccb100027e65880017eb2c4000df59620004facb10002fc65880017fb244000bf99220005fac910002fc6488001bfaa44000df55220005fec710002fe63880017eb1c4000bf18e20006fca7100037c53880017eb144000bf98620005fac310003ee2188001f610c4000bf98220006fea1100037d5088001f79
  | 2 => 0x50006fa65a80037c32d4001bfb0ea000df98750006fac3a80037c61d4001bfa0ea000df90750006fa83a80037c41d4001bf98ea000df8c750006fa63a80037c31d4001bf90ea000df88750006fa43a80037c21d40017eb2ca0009f59650005fcc928002fd6494001bfaa4a000df55250005fcc728002fd6394001bf29ca000df14e50005fcc528002fd62940017f30ca000bf58650005fcc1280037f5094001fda84a000bfd9150005f8c8a80037f5454001bf2a2a000df55150006f8a8a8002ff63540017e31aa000dfd4d50006fca6a80037d5354001be29aa000bfd8950005f8c4a80037f5254001bf292a000df54950006f8a4a8002ff61540017e30aa000dfd4550006fca2a80037d5154001be28aa000fed4150006fca0a80037f64540013fb22a000df99150006fac8a80037c6454001bfb1aa000df98d50006fac6a80037c63540013e31aa000dfd0d50006fc86a80037d4354001be21aa000dfd8950006fcc4a80037d6254001be312a000dfd0950006fc84a80037d4254001be212a000dfcc950006fc64a80037d3254001be192a000dfd8550006fcc2a80037d6154001be30aa000dfd0550006fc82a80037d4154001be20aa000dfcc550006fc62a80037d3154001be18aa000dfc8550006fc42a80037d2154001be10aa000dfd8150006f6c0a8002fe65140013f328a000bf99050005fac8280037f5414001beaa0a000bf98c50005fac6280037e5314001be298a000bf98850005fac428002fe61140017eb08a000bf98050006fea028003fa5014001bea80a000fe54050005fecba0002fe65d0001bf32e80009f99740005facba00037d65d00013eb2e8000bf19740006fea9a00037d54d00017f31e8000bf58f40006fca7a00037c53d0001dfa1e8000ef50f40005fcc5a0002fd62d0001dfa168000ef50b40005fcc3a0002fd61d0001dfa0e8000ef50740006fea1a00037d50d00017fb2c8000bf99640006fccb200027e65900017eb2c8000df59640004facb20002fc65900017eb248000dfd52400077ca9200037d5490001deaa48000cf55240005fcc720002fd6390001bf29c8000df14e400077c8720003bc43900017f3148000bf58a40005fcc320002fd61900017f3048000dfd4240006faa120003bf4090001fda048000bfd9540005fccaa00037e65500013f32a8000bf59540006facaa00027d65500017e32a8000dfd5140006faa8a0002ff63500017e31a8000df94d40006f8a6a0003bf4350001dea1a8000bfd8940005f8c4a0003bf4250001dea128000bfd8540005f8c2a0003bf4150001dea0a8000dfd4140006faa0a0003fb4050001df2028000bfd9440005fcca200037e65100013f3288000bf59440006faca200027d65100017e3288000bf99040006fea820003be5410001beaa08000ef550400067aa82000
  | 3 => 0xfb2a6200dfd9531004feca98802fe654c4017eb2a6200bf19531006f8ca988027c654c4017fb226200bf99131005fac898802fc644c401bfaa26200df55131006fca6988037c534c4017fb126200bf18931007be6498803dd324c401fb28a6200fd54531007ec8298803f5414c401fb98a6200f78c531005fec098802fc604c4017fb286200bf99431005faca18802fc650c4017fb206200bf99031005fac818802fc640c401bfaa06200df55031005fcc6188077e530c403be2986200bf98831005fac418802fe610c401ef9886200fd8c431007ba6218803f5310c4017f3006200bf58031005fecb90802fe65c84017eb2e4200bf19721005fec990802fe64c84017eb264200bf19321006fea9908037d54c84017fb1e4200bf98f21005fac790802fc63c8401bf29e4200df14f21007ec8390803f541c8401fb18e4200fd4c721005fcc190802fd60c84017fb2c4200bf99621005facb10802fc65884017fb244200bf99221005fac910802fc6488401bfaa44200df55221005fec710802fe63884017eb1c4200bf18e21006fca7108037c53884017eb144200fb90a21007da8510803ee3288401f69944200bf98621007de4310803f721884017f3044200bf58221005feca90802fe65484017eb2a4200bf19521005fec890802fe64484017eb224200bf19121006fea8908037d54484017fb1a4200bf98d21005fac690802fc6348401bf29a4200df14d21007ee4290803ee21484017fb024200bf18121005feca10802fe6508401bf32842009f99421005faca108037d65084013eb284200bf19421005fec810802fe6408401df3204200af99021005fac810803bd64084015eb204200bf19021006fea8108037d54084017fb184200bf98c21007bcc610802de63084017eb184200f758c21005bac610802fc6308401bf2984200df14c21005fcc410803ee4208401f6a104200fb8c821007da6410802fe6108401fb2084200fd50421007ec6210803f53108401f79084200fd88421007da4210803f52108401f29084200bf98021007f4c010802fa60084017eb004200fe58021005f2c010802fe64d4001df326a000af99350005fac9a8003bd64d40015eb26a000dfd5350006fca9a80037d54d4001be2a6a000bf98f50005fac7a80037f53d4001bf29ea000df54f50006f8a7a8002fe62d40017eb16a000dfd4b50006fca5a80037d52d4001be296a000bf98750005fac3a80037f51d4001bf28ea000df54750006f8a3a80037f64d4001bf326a000cf99350006fac9a80027d64d40019eb26a0008f59350006f8c9a80037f63d4001bf31ea0009f98f50006fac7a80037c63d4001bfa1ea000df90f50006fa87a80037c43d4001bfb16a000df98b50006fac5a80037c62d4001bfa16a000df90b50006fa85a80037c42d4001bf996a000df8cb
  | 4 => 0x3ed320c8017f3086400bf58432005fcc019002fd600c8017f326a200bf59351006fea9a88037d54d44017f31ea200bf58f51006fca7a88037c53d44017f316a200bf58b51006fea5a88037d52d44017f306a200bf58351005facb28802fe64944017eb24a200dfd5251006faa928802fe63944017eb1ca200df94e51006f8a728802fe62944017eb14a200bf98651006fea328803f751944017f304a200bf58251005fec8a8802fc6454401bfaa2a200df55151005fec6a8802fc6354401bf29aa200df14d51005fec4a8802fc6254401bfa92a200df54951007eea2a88037e51544017fb02a200bf18151005fcca28802fe6414401df320a200af99051005fac828803bd64144015eb20a200dfd5051006faa828802fe63144017eb18a200df94c51006f8a628802fe62144017eb10a200bf98451006fea228803f65114401bea88a200fd54451005fcc028802fd60144017fb2e8200bf99741006fccba08027e65d04017eb2e8200df59741004facba0802fc65d0401bfaa68200ef95341006faa9a0803bd54d04019eaa68200bf98f41005fac7a08037e53d0401be29e8200ef90f410077887a0802fe62d0401f73168200bb98b41005fac5a0803ed62d040176b168200efd0b410077a85a0802fe60d04017eb068200bfd9641005fccb20802fd65904017e32c8200bf59241006fea9208037d54904017f31c8200bf58e41006fca7208037c53904017f3148200bf58a41005fcc320803bf4190401fba0c8200bf98241005fac120802ff65504017f32a8200bf59541005f8caa08037f5450401df2a28200df551410077aa8a08033d54504017fb1a8200bf18d41006fca6a08037c5350401df21a8200ef10d41005fec4a0802fc6250401dfa128200ef50941007ee82a0803be41504017fb028200bf18141005feca20802fe6510401bf32882009f99441005faca208037d65104013eb288200bf19441005fcc8208037f5410401beaa08200bf98c41005fac6208037e5310401be2988200bf98841005fac420802fe6110401dfa088200fd904410077a8220803f541104017f3008200bf58041005fecb98802fe65cc4017eb2e6200bf19731005fec998802fe64cc4017eb266200bf19331006fea9988037d54cc403bf29e6201df14f31005fcc598803ee62cc401773166200bf58b31007dac598802ed62cc401ef9966200f74cb31005fcc198802fd60cc4017fb2c6200bf99631006fccb188027e658c4017eb2c6200df59631004facb18802fc658c4017fb246200bf992310077cc918802be648c4017eb246200ef592310057ac918802fc648c401bfaa46200df55231005fac7188037e538c401be29c6200bf98a31005fac518802fe618c401fb28c6200fd54631007ec8318803f5418c401ef98c6200fdcc631005fcc118802fd608c4017
  | 5 => 0x8252005fec8a9002fc6454801bfaa2a400df55152005fec6a9002fc6354801bf29aa400df14d52007dea4a90037e52548017fb0aa400bf18552005fec0a9002fc60548017f328a400bf990520077cc829002be64148017eb20a400ef590520057ac8290037f5414801beaa0a400bf98c52005fac6290037e5314801be298a400bf98852006fea429003ee5214801bea90a400fb54852005fcc229002fd61148017f300a400bf58052005fecba1002fe65d0801bf32e84009f99742005facba10037d65d08013eb2e8400bf19742006fea9a1003be54d0801beaa68400ef553420067aa9a1002fe63d08017eb1e8400df94f42006f8a7a1003be43d0801de21e8400bf98742007ecc3a1002f661d08017eb0e8400fd58742005eac3a1002fe60d08017eb068400bfd9642005fccb21002fd65908017e32c8400bf59242006fea9210037d54908017f31c8400bf58e42006fca7210037c53908017f3148400efd0a42007de8521002fe61908017eb0c8400bf98242005fac121002ff65508017f32a8400bf59542005f8caa10037f5450801df2a28400df551420077aa8a10033d54508017fb1a8400bf18d42006fca6a10037c5350801df21a8400ef10d42007de84a1003be42508017fb0a8400bf18542005fec0a1002fc60508017fb288400bf99442006fcca210027e65108017eb288400df59442004faca21002fc65108017f3208400dfd5042006faa821002fe63108017eb188400df94c42006f8a621002fe6210801dfa108400fb908420077a8421003ed42108017f3088400bf58442005fcc021002fd60108017fb2e6400bf99732005facb99002fc65cc8017fb266400bf99332005fac999002fc64cc801bfaa66400df5533200efca7990077c53cc8017f30e6400fd98732005ecc399002fd61cc801fab0e6400bd58732005fcc199002fd60cc8017fb2c6400bf99632006fccb190027e658c8017eb2c6400df59632004facb19002fc658c8017fb246400bf992320077cc919002be648c8017eb246400ef592320057ac919002fc648c801bfaa46400df55232005fac7190037e538c801be29c6400bf98a32007dca519003ed528c801f72146400fb50a32007be6519003ef328c8017f30c6400bf58632005fcc119002fd608c8017fb2a6400dfd9532004feca99002fe654c8017eb2a6400bf19532006f8ca990027c654c8017fb226400bf99132005fac899002fc644c801bfaa26400df55132006fca6990037c534c801f72926400fb54932007dc8499003ed424c801f79926400f78c932005fec299002fc614c8017fb026400bf18132005feca19002fe650c8017eb286400bf19432005fec819002fe640c8017eb206400bf19032006fea8190037d540c8017f3186401df94c3200ef8a619002fe620c801ef9906400fb8c832007ba6419
  | 6 => 0x3be324a6009f98e5300efec5298037e6294c01beb14a601df18a5300efec3298037e6194c01beb0ca601df1865300efec1298037e6094c01beb04a6009f5825300ef8c129802ff6454c017e322a600dfd5153006faa8a9803df5354c01bf29aa600bfd8953005f8c4a9802ff6154c017e30aa600bfd8153005f8c0a9802fe6514c017f320a600ef990530057cc829802fd6414c01deb20a600af59053006fea8298037e5414c01beaa0a600df15053005fcc6298037f5314c01ef298a600df54c53007baa629802fe6214c01f7310a600bb98853005fac429803ed6214c0176b10a600bf98453007ecc229802f66114c017eb08a600fd58453005eac229802fe6014c01fd300a600be98053005fac029803f96014c017cb00a601dfd9053006fcc8298033e6414c01beb20a6009f590530067ac8298023d6414c03be320a601df98c53004fcc6298035e6314c03bfb10a600df98853006dcc4298037d6214c01b6b10a601df1885300efec2298037e6114c01bb308a600df58453006eac2298077c6114c03bfb00a600df98053006f4c0298037d6014c013eb00a600de58053004f2c0298077c6014c017fb2e8600bf99743006fccba18027e65d0c017eb2e8600df59743004facba1802fc65d0c01bfaa68600ef95343006faa9a1803bd54d0c019eaa68600df94f43006f8a7a1802fe62d0c017eb168600bf98743005fac3a1802fe60d0c017eb068600bfd964300efecb218027f6590c017f32c8600bf59643005f8cb218077c6590c013e32c8600bf59243006fea9218037d5490c017f31c8601df94e4300ef8a721803bf4390c01efa1c8600bf98a43005fac521802fe6190c017eb0c8600bf98243005fac121802ff6550c01bfb2a86009fd9543005fccaa1802fd6550c017e32a8600df19543004f8caa18037f5450c01df2a28600df551430077aa8a18033d5450c01bf29a8600df14d43007be86a1803be4350c017fb128600bf18943005fec2a1802fc6150c017fb028600bf18143005feca21802fe6510c01bf32886009f99443005faca218037d6510c013eb288600bf19443005fcc8218037f5410c01beaa08600bf98c4300efca6218077c5310c01dfa188600f790c430077a8621803dd4310c017f3108600fb98843005dcc421802fd6210c01f6b108600bb58843005fcc221803f66110c017b3088600bf58443007eac221802f56110c017f3008600fe98043005f4c021802fd6010c01fcb008600be58043005fcc9a9002fd64d4801bfaa6a400df55352005fcc7a9002fd63d4801bf29ea400df14f52005fcc3a9002fd61d48017f306a400bf58352005facb29002fe64948017eb24a400dfd5252006faa929002fe63948017eb1ca400df94e52006f8a729002fe6294801bfa94a400fbd4a52005fcc329002fd61948017f304a400bf5
  | 7 => 0xc00200000600a01c00600600001000600a00c00000400200400000400600002200000c00200003001600600001a00401000800200600a00800400000000c00201800201200000000000000600200800800000200600400400001200000000800000400400800001000000a00200000000000600200000600600600200000800000001000800200e00801000800000402400e00400600200000400400600200201200600600200200200000000400000400001000800200800400000c00a00200200400200400400200200000200600a00801a00000000000600600200000000400000e00200000000400401000600200000200000801200000e00800200000200000000c00200000800000000000600600200000200c00200800400400002000000001200000400800000800001e00000600002000c00800000e00000000201200000000001000200800400001600200e00400e00000000a00000000000000000000200800002400400800200200000000800200201200000200200600803400000200000000200e00000000200200c02000200000200001800000200000002800000400400000600a01802000000000000000000200600000800000000000200000a00400e00600000000201200200000000200400000a00401a00400000800a00200e00200200400000e00bf98f54005fac7aa002fe62d50017eb16a800bf98754005fac3aa002fe60d50017eb06a800dfd8f54006fcc7aa0027e63d5001beb1ea800df18f54006fec5aa0037e62d5001beb16a800df18b54006fec3aa0037e61d5001beb0ea800df18754006fec1aa0037e60d5001beb06a8009f58354006f8c1aa002fd65950013eb2ca800bf99254006fea92a003bf54950019faa4a800bf98e54005fac72a002fe62950017eb14a800bf98654005fac32a002fe60950017eb04a800efd5154006fca8aa002ff63550017e31aa800bfd8954005f8c4aa002ff61550017e30aa800bfd8154005f8c0aa0037f64550019fb22a800dfd8d54006fcc6aa0037d6355001be31aa8009f18d54006fec4aa0037e6255001beb12a800df18954006fec2aa0037e6155001beb0aa800df18554006fec0aa0027f6055001bf302a800df58154006f8c0aa002fe65150013f328a800bf99054006fea82a003be5415001beaa0a800ef55054005fcc62a002fd63150017f310a800bf58854005fcc22a002fd61150017f300a800bf58054005fcc9a9802fd64d4c01bfaa6a600df55353005fcc5a9802fd62d4c017f30ea600bf58753005fcc1a9802fd60d4c017eb2ca600bf99253005fac9298037f5494c01bf2a4a600df55253006f8a929802fe6394c01bfa9ca600f7d4e53005fcc529802fd6294c017f30ca600bf58653005fcc129802fd6094c03bfb24a600df99253006fac9298027d6494c0
  | 8 => 0x111c000318001524000001460d683a4000ed84e80008800000000016e00000000016e4000000000000054000000d04c211a50009b8b5d050e980f998c88d2040f09d4d597819dcb9d9a0951764a780000007b8d440003d42580000000017400008488216400009145b00000018ac000fa00006c136101114cdf145ca146dcc9d9b48fc6a8000ba0bf0000001808000000000000e9508086c0003dc0000018b06e40c0ce150097030125c00028923055034139c2a000127c80c0000000000019912ed868bf42d59c00000004487f8000a6cab582000191c0000000000000000000000000000009813e92d44291b42b0ce80e844cae054c8e40000000011f47a489008cd3c0015519d0784000a600000000000000016c80000000017018bc6b81d8000974d940000018c40b87d5438e4ccfd60511851c290ed539189000008800016c3ecf14000384a25120f6893c0018492440000013000000015d800000024c7358e8000001440001154000000000b7904c00000000083cf2d7c100c0001a5488e704f800000000000000000000134c000000bdd63d83802891c000000000000000000f640000008f447d9c8000000dc515017822c0082f12cc654000368fd48886e8e0c0440016b937000185122912d7c8c1cec543c2700000000012b4ee80016d00e4000e358253990893c067c58c0000000007ec0010d94340008247099d4000000000fd8bc4e59920414cd50600004ec00140400000188c000000001818e20fe08a40000000790ec000b381e964c000e6800101c0012d14bc000001464bc959d76c000000000cf8f18000a5596d2a908c4d97f40008088319b000199d2c4001028000d7c000818a75424f940000000001b95f170800000087c918f60ac93ac00000000000000046c000f800000000f5030ae400015106429cad4e50b100007a8838764f4800001000600200001002e00600a00400800000e02000e00603000000000001000a00201800000200000600400a00400200401600200001000200800200c00000a00000601200000000600000e00000000000000000201002200400000000000401800000400200601200000c00200600000000000200000000000800e00200c00000200400000000400000600800000000600400600401201c00e00e00000600c00400200e01203201e00c00600400800200200800001400600800000200201a00800200000800600000200200200200600601000601600400400000000c00c02600200200001c00000000000000000200000000200000c00400003a00200601c00800401000000000000200602401000800000400000400401600000800000000a00000001400000400404600400000000200000400c00200200800000c02000600200000200000000000a0000080000060040040120
  | 9 => 0x5c8311748a9cb69169208da47487982c58a83911940000018447f43458a47b00000013088047100009900000000011d87d894595489d7e86ac00000000000149c0000019d8000424000000000000001528628cc40002b9908000eeca58000000000000e5c000f8c57865c43872c6c40018294a0000bb436c218000000484754000558d816a47a173d88428474c1b400123c35800073c0000001a88780001580000001903f05e461082800000000121c00075cdb4000514658000420000000000000bd9094000000000f011dcf4c1d4e612bc0000000000000000006700012740016800000000005a4000000180000000000d6c86953861c6e1880354f748716552015a13d8d08134be4000e112604a54b40000007180000000001605cd8d15214b916000000066c0000000000000005c4000000000000000d40efc3c80007700000000d0ee07393fc7c4968be977800195c2340000008ed364000af06f113c000a3102000000082c000000084001069374000250000000000000000164000c70000b3000019c00000000119d960001644d880ac204c619295ac0003d8df4000f88c54000000000375930b1c000000001104000001734ef90980002802ed7615840015e8a285d47ad9c4000728000e3c000e640a800000000000000000000000000000000000000000066922c000000000e08000000c38000adc0000001c960c0000016b490400039532d81c0000000005690700017bc7809ed6291c8f790fcdbc000000c50a9800000079c5b40000016248ad795514900230b754486a47754d4f9c0009a0000b2d52c0000000a0040000000d5400115d3282ac0e0c6c000000000000eb10e98748b07c05900000016ccd8d2fd2dcaf81d16f99984f1910000000000000d3800000047809ce2400050cff4000000000c69699664000fb85f80000000000000000000000011d4000000000000000000000000000000e2800000196403c200a680000010340000008b8edc001428000c5c864001768000000d780001f0b7c00d555128ee44515bc0016dd16d4093f4504000000b35164000038000000000000110001940000c8c0008dc000000f28db0928dd07e0999974f90740d0000000105cd100000000015580000000000001004d4000000c48001860ad800102d3457b03215f5648a38294e3894962c000e049c4c74d486d831593c00180cab000021d0f4f445f1510d740008d40d400000000013c6950c8000accaf567800179c0012680000000017892f0488c007940010bc0011cca913a88540013393d54517a80000000000000000000d82e40000000016d4000d340000000010380016840000000017d40000000000000000001b0000000001219968000d4c0006b16fc0017149cc000000e14a712e4b6c00088400005968800000000000
  | 10 => 0xecce44f7c18800000000000000150c0000006654e437c0017dc0014e00000000000bd8d4000fc5888a3c0000017a50d04648c0c580000000004180019fc2780000011c4bd40000000940019e000000000068400159034c0005940000000007684c4910000e886f40010b4cc16351e40000000800003c400153d638b14afc00000184c7e99796f4000000fa40000001380000000009f400117c00000174503c00007cec0dd81200012e89855046012987fca5000068c8c80a4338ff9540a34000e781fc000d3118d938001198c88000000d20000b4839c3f8cbc0000008f8e48aa0620001074ca0c90f3c1f84744a1614d505240689ad2402e027572c0ccc3c994000000440000000000c114f8001294000b205647dc62d1000004cc0014d17540014a948cda1710000b3d9f191586c00177c958b4d8a0cf4000000d6026d720a205ed2a40000016b00008457ccdfd9196c45614dc0000000002600013304bc2f4a84d144dd3886d0b4197149470197c790714f258b98c8f1c4e528896ca2ce8441d3b0000000000000350b08b24000834d0c000b880000000003d0604954494c2cb5969c0002080000000000013cd411270000f6c0358783785dc000db810cd8443d1591d0001544e1c9f085c7f08e9091859804000460000000b991ad775668624c7d9519042693181696f174d4f0528430d2d44d70ca9427cb8d6e8ac455d9e800096032c0000000003984c877c00185400000000049cf381485993801c57d82c94149bc2a53500300014b00009a49640000000015c0000a0c000000000d9d044b514ad8b5730000000000688000b558659e4cd8aa492d75ca0581400000002c6193c55cd1308e03602bcb857a000076c0015b0744000000b4400000000028cae8434000000000000b80000000e540017fc4b00007206a0ccc3fc0015683b41980c91150a800099c0001040000006ccbf8bfce815b4dccb71690f584ac0012647309c9610da96a80000013dc0010f91a97d0000000000000000000000800328000000b6582c5d00000000008cc0002dc10800000000000015c0000001407b4aac7bcb28238fed92c0000058dc0000005d80000017ad54800032411c3a13040001140000000000008d800078d78d2789dc0009b1008c785e18940007c8d655605ac40154d4a58c189d040e8d4d86fd49845d124fa80000000fc304f98000000000000000000000d98000000aa84540000014c46b42a8000001984000bb0001798124000ff12516304f47603ac14494165000000147530d17458400156400059c0001753250154815dc000858370a400015301840013591780006d40010cd87c000570000000254000000000000000b60000000c9458194848c64c00000000000000126c00029968c38c6159459bc0015196c0e18445534f3000051800056c
  | 11 => 0x40009fc0009256ec17d9355e5234a45335320001670000000000cb400119006c12d7855a853057c060000000000000000000000000000b0000000000000161d83c0001c00000019a8cec42d41c0000000010c00000012d91b00012589d07796ac050ec985d490e7c12852019400157400000020c0006417b8c99718000380000070000920544000000000000000000000000000ab88740000015b84b4000c080000005e8a0800097c3c000102400000000000098c000000f54c199a4b0c00000199529000000000000147060c33cdd53ec00114147cfe80003e451001489566c0016940000002110dcd18650000ed1618000de49393a1454480001594000000bb97e40000018d80009f80013400018cc0012208b556c000eb9420000000e740005bc0000009e40012840000000018f8ddc5fcf40ac00015e17706bc5000b46906f8648d240ec0009880011c00000004c0a1955c000001570eb42c0a893bc154fc0bc05a8fb000140c25c00014c00034805d0b8c418f12ad2f58408a8f0d2559ad0b00011e8e0002463c000ba40000000017291a00000000010f14687cc04c5419883880001a02b4f71600a5d1388f13102fcd7031d750dc9314a4d214ea82cc5a0458c842212b000000000000000151c94c69c678245980498ad171d5f800000111000000135c000000000000001898000000c049a8a4840c840000000eac588c0cfe4d1c00000081cabc5c0e9d0ac00047070c000000000b94d283092f88a01ed58c1cc554574364000724001484000248a80000000000b1967c001790000000000001144000000e6c0012c00000000000000009e12a0000ebcc4d5c51481311e04e18e09b509c000090fac001a018fd0c51bd7e16a0608000630df8000001184000490d90010508334535210000e4110c0017f800120c3b92b80003cd0a59ed355384a653e5004000decf34c81958ba8000ea16095080017258ecc281bd2c8638a103a80002d030cc250d400053c000048408000e913b524946d7f0000000000000660ef14780000016602280008bcbac001758000934f098701180014440008c50543bd4ed4c9578cb98316bc704000404a1c0001ad57d38cfc8000cc8ea536c00000000078800000165c000000000000000000bccbec0006c8000000a7d3b81711891ec000000b900013786755883f4b04644000000000e2c000aec9094c000007454983435c01d29ccb00007d02f93d0f04fcd4014cd394a0000095d5fc000000ce4000000c3497994d62023c00000009800000180068000018d0840000013f80000015d40018e40011b80019cc0000004b8000930cad1fc330c443b00008114e8dad4180003e04d106d738f219f89e90a09d8f51180c144a81e40000000009c0fdd238bbd1f96582d80011f159907d5ecbe133d170f5d42c0000b0bd00
  | 12 => 0x137cf840000017b4000ca528c75090d3a42e852c001430860fd1348000de94fc00124c634000a8d90c000c654f57c42650e5078fb40005380019010480000000000005f42240000003e80c4d5c8d00000000000000013e01f52240000012e19b95c80007e4000000000ef4000c300012800016d98f46993f000000071d705674000ca8cdc7599246ec000001109018f10814410898018cd084c0005b88500204fd5d00001dc000000ffcfbd810001458de10e00000000015813680000000000000000000015a40013c8240000000000dc00000000659f4e30cf131d7ec4681e00000010582140dd13
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xd72d94100047d76994100047d749941000c7e73994100047f745941000c7c73594100047f70594100047d70594100047e7519410004be7419410004bd7419410004de7319410004dd7319410004ee7219410004ed72194100047e75d90100047d75d9010004de73d9010004dd73d9010004ee72d9010004ed72d90100047e75990100047d7599010004bd76990100063e65990100063d65990100063e75990100063d75990100063e65590100063d65590100063e75590100063d75590100047e75190100047d7519010004be7419010004de7319010004dd7319010004ee7219010004ed7219010004f671190100047f76d50100047d76d50100063e64d50100063d64d50100047f76550100047d76550100063e64550100063d64550100047e75d8c100047d75d8c10004be74d8c10004bd74d8c10004ee72d8c10004ed72d8c10004dd7698c100065e6598c100065d6598c100069e6498c100069d6498c1000e5f7598c1000e5c7598c100065f5498c100065d5498c100047f7558c100047c7558c100065e6558c100065d6558c100069e6458c100069d6458c100065f7558c100065c7558c100065f5458c100065d5458c100047e7518c100047d7518c10004be7418c10004bd7418c10004de7318c10004ee7218c10004ed7218c10004f67118c1000c7f7694c100047d7694c100063e6494c100063d6494c1000e5e6394c100065d6394c1000c7f7614c100047d7614c100053d7414c100063e6414c100063d6414c1000e5e6314c100065d6314c10005797014c100047e75d88100047d75d8810004be74d8810004bd74d8810004de73d8810004dd73d8810004ed76988100066e65988100066d6598810006ae6498810006ad6498810006ce6398810006cd63988100066f54988100066d54988100066e53988100066c53988100066e65588100066d6558810006ae6458810006ad6458810006ce6358810006cd63588100066f54588100066d54588100066e53588100066c5358810006e471588100047e75188100047d7518810004be7418810004bd7418810004de7318810004dd7318810004ee7218810004f67118810004fa7018810004f576c8410006b564c8410006d563c8410006e562c8410004f57608410006b56408410006d56308410006e56208410005f170084100047e75980100047d75980100047d76d40100053d74d40100063e64d40100063d64d40100065e63d40100065d63d40100066e62d40100066d62d40100047f76540100063e64540100063d64540100065e63540100065d63540100066e62540100066d6254010006b564c4010006d563c4010006e562c4010004f97684010006e96284010004f77644010006b56444010006d56344010005e47244010006e56244010007715044010004fb7644010006e96244010
  | 1 => 0x8020004fb7648020006f16148020004be7419710004bd74197100047e75993100047d7599310004ee7299310004ed72993100047e75193100047d75193100063e64553100063d64553100047e75d8f100047d75d8f10004be74d8f10004bd74d8f10004ee7298f10004ed7298f100047f7558f100047c7558f100053d7414f10005797014f100047e7518b100047d7518b10004be7418b10004bd7418b10004de7318b10004dd7318b10007355450710005b5748c710006e462487100053d74d4310004be7499610004bd74996100053d74996100063e74996100047d74996100063d74996100043d749961000c7e73996100047f745961000c7c73596100047e75d92100047d75d92100047e75992100047d75992100047e75192100047d7519210004de7319210004dd7319210004ee7219210004ed72192100047f76d52100047d76d52100047f76552100047d76552100063f64552100063c64552100047e75d8e100047d75d8e100047f7558e100047c7558e10004bf7458e10004bc7458e100047e7518e100047d7518e10004be7418e10004bd7418e10004ee7218e10004ed7218e1000c7f7694e100047d7694e1000c7f7614e100047d7614e100053d7414e10005797014e100047e75d8a100047d75d8a100047e7518a100047d7518a10004be7418a10004bd7418a10004de7318a10004dd7318a10006e76208610005f170086100053d74d4210007e02188210005f07148210007e32148210004be7499510004bd7499510004ee7299510004ed7299510004ef7259510004ec72595100047e75991100047d7599110004ee7299110004ed7299110004ef7259110004ec72591100047e75191100047d75191100063f64551100063c64551100047e75d8d100047d75d8d10004ee7298d10004ed7298d100047f7558d100047c7558d10004bf7458d10004bc7458d10004ef7258d10004ec7258d100053d7414d10005797014d100066f54d89100066d54d89100066e53d89100066c53d8910004ee7298910004f771589100047e75189100047d7518910004be7418910004bd7418910004de7318910004dd7318910004ee76189100066e75189100066d7518910006ae7418910006ad74189100066f54189100066d5418910006ce7318910006cd73189100066e53189100066c5318910006e57118910006e97018910006e46290510004f47650510007355450510006e46250510005b5748c510006e4628c510004f4764c510006e4624c510004f67688510006e46288510004f47648510006e462485100053d74d41100066f62d41100066c62d41100066f62541100066c6254110006e86288110007e22188110004f87648110007e12148110006e46284110004be74d9410004bd74d9410004de73d9410004dd73d9410004ee72d9410004e
  | 2 => 0x6d67318520006d57318520006765318520006745318520006e64218520006e54218520006e63218520006e53218520006f17018520004ee76c8520006e461c8520006e461485200053d74d41200067761d41200067461d4120006776154120006746154120006e46188120004be74d9420004bd74d9420004de73d9420004dd73d9420004f671d9420004f571d94200047d76994200047d749942000c7e73994200047f745942000c7c73594200047e7519420004be7419420004bd7419420004de7319420004dd7319420004f67119420004f571194200047e75d90200047d75d9020004de73d9020004dd73d9020004f671d9020004f571d90200047e75990200047d7599020004bd76990200063e65990200063d65990200063e75990200063d75990200063e65590200063d65590200063e75590200063d75590200047e75190200047d7519020004be7419020004de7319020004dd7319020004ee7219020004f67119020004f571190200047f76d50200047d76d50200063e64d50200063d64d50200047f76550200047d76550200063e64550200063d64550200047e75d8c200047d75d8c20004be74d8c20004bd74d8c20004f671d8c20004f571d8c20004dd7698c200065e6598c200065d6598c200069e6498c200069d6498c2000e5f7598c2000e5c7598c200065f5498c200065d5498c200047f7558c200047c7558c200065e6558c200065d6558c200069e6458c200069d6458c200065f7558c200065c7558c200065f5458c200065d5458c200047e7518c200047d7518c20004be7418c20004bd7418c20004de7318c20004ee7218c20004f67118c20004f57118c2000c7f7694c200047d7694c200063e6494c200063d6494c2000e5e6394c200065d6394c2000c7f7614c200047d7614c200053d7414c200063e6414c200063d6414c2000e5e6314c200065d6314c20005797014c20006766598420006756598420006b66498420006b56498420006d66398420006d56398420006775498420006755498420006765398420006745398420006766558420006756558420006b66458420006b56458420006d66358420006d56358420006775458420006755458420006765358420006745358420004ed7688420006ad6488420006cd6388420006e56188420006ad6408420006cd6308420006e56108420005e970084200047e75980200047d75980200047d76d40200053d74d40200063e64d40200063d64d40200065e63d40200065d63d40200067661d40200067561d40200047f76540200063e64540200063d64540200065e63540200065d6354020006766154020006756154020006ad64c8020006cd63c8020006e561c8020006f16188020004ef7648020006ad6448020006cd6348020005e47148020006e5614802000769504
  | 3 => 0xf54588300066d545883000e6e535883000e6c5358830006766598430006756598430006b66498430006b56498430006e66298430006e5629843000677549843000675549843000e76539843000e745398430006766558430006756558430006b66458430006b56458430006e66258430006e5625843000677545843000675545843000e76535843000e7453584300047e75980300047d75980300047d76d40300053d74d40300063e64d40300063d64d40300066e62d40300066d62d40300067661d40300067561d40300047f76540300063e64540300063d64540300066e62540300066d62540300067661540300067561540300067a60540300069d64cc030006cd62cc030006d561cc03000679658c030006b9648c030004df764c0300069d644c030006cd624c030006d5614c030004fb764c03000679654c030006b9644c030004be7419720004bd74197200047e75993200047d7599320004f67199320004f571993200047e75193200047d75193200063e64553200063d64553200047e75d8f200047d75d8f20004be74d8f20004bd74d8f20004f67198f20004f57198f200047f7558f200047c7558f200053d7414f20005797014f200072d5450b20005ad748cb200053d74d4320004be7499620004bd74996200053d74996200063e74996200047d74996200063d74996200043d749962000c7e73996200047f745962000c7c73596200047e75d92200047d75d92200047e75992200047d75992200047e75192200047d7519220004de7319220004dd7319220004f67119220004f571192200047f76d52200047d76d52200047f76552200047d76552200063f64552200063c64552200047e75d8e200047d75d8e200047f7558e200047c7558e20004bf7458e20004bc7458e200047e7518e200047d7518e20004be7418e20004bd7418e20004f67118e20004f57118e2000c7f7694e200047d7694e2000c7f7614e200047d7614e200053d7414e20005797014e20005e970086200053d74d4220004be7499520004bd7499520004f67199520004f57199520004f77159520004f471595200047e75991200047d7599120004f67199120004f57199120004f77159120004f471591200047e75191200047d75191200063f64551200063c64551200047e75d8d200047d75d8d20004f67198d20004f57198d200047f7558d200047c7558d20004bf7458d20004bc7458d20004f77158d20004f47158d200053d7414d20005797014d20004ec76509200072d5450920005ad748c920004ec764c9200067754d85200067554d85200067653d85200067453d85200047e75185200047d7518520004be7418520004bd7418520004de7318520004dd7318520006767518520006757518520006b67418520006b57418520006775418520006755418520
  | 4 => 0x23000739549023000579755023000d7b75cc2300047d74d95300047e7599530004be7499530004bd7499530004bf7459530004bc74595300047e76195300047d741953000c7e731953000c7c73195300067970195300063f65d91300063c65d91300063f75d91300063c75d91300047e75991300047d7599130004be74991300047f75591300047c75591300047e75191300047d7519130004ee7219130004ed7219130004f67119130004f57119130004be76191300063f65191300063c65191300063e75191300063d75191300069d7319130006ae7219130006ad7219130006b67119130006b57119130006b970191300047e76d51300047c76d51300063f64d51300063c64d51300057970d51300047e76551300047c76551300063f64551300063c64551300047e7694d300063f6494d300063c6494d300047e7614d300053d7414d300063f6414d300063c6414d300069c6490d30004dc7650d300071d5450d30005d571cc930005cd72cc5300047e76d41300053d74d41300063f64d41300063c64d41300055e73d41300057975941300067865941300047c76541300063f64541300063c64541300055c7354130004f876541300067b76541300057876541300067876541300047876541300057b74541300073b64541300073864541300075b735413000d7873541300075873541300075a43541300075943541300075b32541300075932541300075b3154130007593154130005797590130006b864901300073954901300079a4390130004f8765013000579755013000799435013000d7b75cc13000759508c130004be74d9430004bd74d9430004ee72d9430004ed72d9430004f671d9430004f571d94300047d76994300047d749943000c7e73994300047f745943000c7c73594300047e7519430004be7419430004bd7419430004ee7219430004ed7219430004f67119430004f57119430004fa70194300047e75d90300047d75d9030004ee72d9030004ed72d9030004f671d9030004f571d90300047e75990300047d7599030004bd76990300063e65990300063d65990300063e75990300063d759903000e3e539903000e3c53990300063e65590300063d65590300063e75590300063d755903000e3e535903000e3c53590300047e75190300047d7519030004be7419030004de7319030004ee7219030004ed7219030004f67119030004f57119030004fa70190300047f76d50300047d76d50300063e64d50300063d64d50300047f76550300047d76550300063e64550300063d645503000d5c735503000c7f7598c3000c7c7598c300066e65988300066d6598830006ae6498830006ad64988300066f54988300066d549883000e6e539883000e6c53988300066e65588300066d6558830006ae6458830006ad64588300066
  | 5 => 0x66f54988400066d54988400066e53988400066c53988400063d54588400066e65588400066d65588400072d5458840006ce6358840006cd63588400066f5458840006ae54588400066d5458840006ad54588400062d54588400066e53588400066c5358840006ae4358840006ac4358840006766598440006756598440007355498440006d66398440006d56398440006e66298440006e562984400067754984400067554984400067653984400067453984400063d5458440006766558440006756558440007355458440006d66358440006d56358440006e66258440006e56258440006775458440006b65458440006755458440006b55458440006355458440006765358440006745358440006b64358440006b443584400047e75980400047d75980400063d54980400047d76d40400053d74d40400065e63d40400065d63d40400066e62d40400066d62d40400067661d40400067561d40400047f76540400065e63540400065d63540400066e62540400066d62540400067661540400067561540400053d75d00400069d63d0040006ad62d0040006b561d0040007395490040006d96390040004bf76500400053d75500400069d6350040006ad6250040006b56150040004fb7650040006d963500400047d74d973000e5e73d973000e7970d9730004be7419730004bd7419730004ee7219730004ed7219730004f67119730004f5711973000e3e74197300047d741973000e3d74197300043d741973000e5e731973000e6e721973000e6d721973000e76711973000e75711973000e7970197300047e75993300047d75993300047f75593300047c75593300047e75193300047d7519330004ee7219330004ed7219330004f67119330004f5711933000c7e76d533000c7c76d533000c7e765533000c7c76553300063e64553300063d64553300071d5450f300047e7598b300047d7598b30004be7498b30004bd7498b300047f7558b300047c7558b30005d571ccb300047e75987300047d7598730004be7498730004bd74987300047f75587300047c7558730005cd72cc7300053d74d433000d5e73d433000d5c7354330004be7499630004bd74996300053d74996300063e74996300047d74996300063d74996300043d74996300067a70996300047f74596300047e75d92300047d75d92300047e75992300047d75992300047e75192300047d7519230004ee7219230004ed7219230004f67119230004f571192300047f76d52300047d76d52300057970d52300047f76552300047d76552300063f64552300063c64552300055c73552300053d7414e30005797014e30004f77158a30004f47158a30004ef7258630004ec72586300053d74d42300067a65542300057b76542300067b76542300057b745423000d78735423000579759
  | 6 => 0xd6550b400063d65d0740005ad72d07400063d65507400053d74d43400053f74543400063d749964000c7e739964000c7c73596400057970d52400063e65952400057b70552400063f76552400063c76552400053c73552400053f70552400073b70552400073870552400047f7558e400047c7558e400063d5458e4000c7f7694e400047d7694e40005797094e4000c7f7614e400047d7614e400053d7414e40005797014e400053f7590e400053d7510e40005b97010e400063d5458a40004f77158a40004f47158a400063d5458640004ef7258640004ec72586400053d74d42400053d75d02400073950d02400073954d0240004bd74995400047d74995400063d74995400043d749954000c7e73995400047d7099540006797099540004df7359540004dc73595400055c73595400047f74595400063f74595400065f735954000c7c73595400065c73595400045c73595400047f70595400067b70595400057970d51400057b70551400047e75d8d400047d75d8d400047e7518d400047d7518d40004ee7218d40004ed7218d40004f67118d40004f57118d400047d7694d400053d7494d40005797094d400047d7614d400053d7414d400065f6314d4000e5c6314d40005797014d40004be76d0d400063d65d0d400063d6550d400047e75d89400047d75d89400047e75189400047d75189400063d65d0940005b571d09400063d65509400047e75d85400047d75d85400047e75185400047d75185400063d65d0540005ad72d05400063d65505400053d74d41400047f76541400047d76541400053f74541400063d6590140004de73d9440004dd73d9440004ee72d9440004ed72d9440004f671d9440004f571d94400047d76994400063e749944000c7e73994400047f74594400047d745944000c7c73594400047e7519440004de7319440004dd7319440004ee7219440004ed7219440004f67119440004f571194400047e75990400047d75990400047d76d5040004bd76950400053d75950400063e65950400047f76550400063e65550400053f76550400063f76550400053c73550400053f70550400065e6598c400065d6598c400071d5498c4000e5f7598c4000e5c7598c400065f5498c400065d5498c400047f7558c400047c7558c400063d5458c400065e6558c400065d6558c400071d5458c400065f7558c400065c7558c400065f5458c400069e5458c400065d5458c400069d5458c400061d5458c4000c7f7694c400047d7694c4000e5e6394c400065d6394c4000c7f7614c400047d7614c400053d7414c4000e5e6314c400065d6314c40005797014c40004bd7690c400053f7590c400069d6390c400053d7510c400069d6310c40005b97010c400066e65988400066d65988400072d5498840006ce6398840006cd6398840
  | 7 => 0x87500057a70087500057970087500063d645525000e5e6394e500053d7414e50005797014e500053d74d42500063f64951500063f64551500063c64551500047e7615150004be7418d50004bd7418d50004ee7218d50004ed7218d50004f67118d50004f57118d500047e76d4d5000e5c6394d500057a7094d500053e7414d500053d7414d500056e7214d500056d7214d50005767114d50005757114d500057a7014d50004be7418950004bd74189500053e74149500053d7414950004be7418550004bd74185500053e74145500053d741455000c7e73d91500063f64991500057970991500055f73591500055c73591500057b70591500063d6419150005797098d500053f7458d500053c7458d500057b7058d500053e7418d500053d7418d500056e7218d500056d7218d50005767118d50005757118d5000e3e7418d500047d7418d5000e3d7418d500043d7418d5000e6e7218d5000e6d7218d5000e767118d5000e757118d5000e797018d500047e76d0d500047d76d0d500065c63d0d5000c7c7690d500063f6490d500057a7090d50005797090d500047f7650d500047c7650d500047e7610d500047d7610d500063f6410d5000e5c6310d500056e7210d500056d7210d50005767110d50005757110d500057a7010d50005797010d500057970989500057771589500057471589500057b70589500053e74189500053d74189500047e76d09500047d76d09500057671d09500057571d09500047e76109500047d76109500057671cc9500057571cc9500057a70cc9500057970cc9500047e768c9500047d768c9500053e748c9500053d748c9500047f764c9500047c764c9500057a700c95000579700c9500057970985500056f72585500056c72585500057b70585500053e74185500053d74185500047e76d05500047d76d05500056e72d05500056d72d05500047e76105500047d76105500056e72cc5500056d72cc5500057a70cc5500057970cc5500047e768c5500047d768c5500053e748c5500053d748c5500047f764c5500047c764c5500057a700c55000579700c5500047e76085500047d76085500053e74085500053d74085500055e73085500055d73085500076521085500057a70085500057970085500053e74d81500053d74d81500073a74d81500073974d81500057973d81500063e74994500063d74994500063e64d50500063d64d50500047f76550500047d7694c500053d7414c5000e5e6314c50005797014c500053d74d40500047f7654050004fb76540500067a655405000c7e739974000c7c73597400047f7558f400047c7558f4000c7f7694f400047d7694f400053d7494f4000c7f7614f400047d7614f400053d7414f40005797014f400063d65d0f400063d6550f400063d65d0b40005b571d0b400063
  | 8 => 0x6f13158021006eb2158021006f22158021006e92158021006f12158021006e121580210063e75593500063e64d53500063d64d53500063d64953500063e64553500063d64153500057a70153500063d64d4f500063e6494f500063d6494f500063d6454f500053e7414f500053d7414f500063e6414f500063d6414f5000e5e6314f500056e7214f500056d7214f50005767114f50005757114f500063d64d4b500063d6494b500063d6454b500053e7414b500053d7414b500063d6414b500063d64d47500063d64947500063d64547500053e74147500053d74147500063d64147500057970d93500063f649935000c7c73593500063f76593500063f73593500063e73593500063d73593500063c73593500063f72593500063e72593500063d72593500063c72593500063f71593500063e71593500063d71593500063c71593500063f70593500063d70593500063d64193500057970193500053e74d8f500053d74d8f500063d64d8f500057970d8f500063e6498f500063d6498f500047d7498f500063d6458f500053e7418f500053d7418f500063e6418f500063d6418f500056e7218f500056d7218f50005767118f50005757118f50005797018f500047e76d0f500047d76d0f500063d64d0f5000c7f7690f500063d6490f500047f7650f500047c7650f500063d6450f500047e7610f500047d7610f500063d6410f500056e7210f500056d7210f50005767110f50005757110f500057a7010f50005797010f500053e74d8b500053d74d8b500063d64d8b500057671d8b500057571d8b500057970d8b500063d6498b500063d6458b500053e7418b500053d7418b500063d6418b50005797018b500047e76d0b500047d76d0b500063d64d0b500057671d0b500057571d0b500063d6490b500063d6450b500047e7610b500047d7610b500063d6410b500063d64ccb500057671ccb500057571ccb500047e768cb500047d768cb500053e748cb500053d748cb500063d648cb500047f764cb500047c764cb500063d644cb500063d640cb500053e74d87500053d74d87500063d64d87500056e72d87500056d72d87500057970d87500063d64987500063d64587500053e74187500053d74187500063d64187500057970187500047e76d07500047d76d07500063d64d07500056e72d07500056d72d07500063d64907500063d64507500047e76107500047d76107500063d64107500063d64cc7500056e72cc7500056d72cc7500047e768c7500047d768c7500053e748c7500053d748c7500063d648c7500047f764c7500047c764c7500063d644c7500063d640c7500063d64c87500063d64887500063d64487500047e76087500047d76087500053e74087500053d74087500063d64087500055e73087500055d730875000765210
  | 9 => 0xd7319421004fa7019421004f970194210047e75d90210047d75d9021004de73d9021004dd73d9021004fa70d9021004f970d90210047e75990210047d7599021004bd76990210063e65990210063d65990210063e75990210063d7599021006ae7299021006b671990210063e65590210063d65590210063e75590210063d75590210047e75190210047d7519021004be7419021004de7319021004dd7319021004fa7019021004f970190210047f76d50210047d76d50210063e64d50210063d64d50210047f76550210047d76550210063e64550210063d64550210047e75d8c210047d75d8c21004be74d8c21004bd74d8c21004fa70d8c21004f970d8c21004dd7698c210065e6598c210065d6598c210069e6498c210069d6498c2100e5f7598c2100e5c7598c210065f5498c210065d5498c21006ce7298c21006d67198c210047f7558c210047c7558c210065e6558c210065d6558c210069e6458c210069d6458c210065f7558c210065c7558c210065f5458c210065d5458c210047e7518c210047d7518c21004be7418c21004bd7418c21004de7318c21004fa7018c21004f97018c2100c7f7694c210047d7694c210063e6494c210063d6494c2100e5e6394c210065d6394c2100c7f7614c210047d7614c210053d7414c210063e6414c210063d6414c2100e5e6314c210065d6314c21005797014c21004ed7690821006cd6390821005e57190821006ae64508210072d5450821006cd6350821004ed768c8210066d658c821005ad748c821006ad648c821005e5718c8210066d654c821006ad644c821006ce634c821004f57690421006d56390421005e57290421006b66450421007355450421006d56350421007a54250421004f5768c42100675658c421005b5748c421006b5648c421005e5728c42100675654c421006b5644c421006d6634c421007c5324c421005e57288421004ef7648421004f77648421005e77648421006e77648421007666548421007656548421005e77448421005e57448421007a66448421007a56448421007675448421007655448421005e77348421005e57348421007c66348421007c56348421007665348421007645348421005e470484210047e75980210047d75980210067a6598021006796598021006ba6498021006b96498021006da6398021006d96398021007e121980210067a75980210067975980210067b54980210067954980210067a5398021006785398021006e521580210067a6558021006796558021006ba6458021006b96458021006da6358021006d96358021007e121580210067a75580210067975580210067b54580210067954580210067a5358021006785358021006ea4258021006e94258021006ea3258021006e93258021006f24158021006f14158021006f23158021
  | 10 => 0x52310047f76552310047d76552310063e64552310063d64552310063e6494e310063d6494e310053d7414e310063e6414e310063d6414e31005797014e31006766554631006b6645063100735545063100f5653cc631005e672cc6310047e75982310047d75982310047d74d95310047d70d95310047e7599531004be7419531004bd74195310047e76195310053d74195310063e74195310047d74195310063d74195310043d74195310067571195310047d70195310047e75991310047d7599131004ee7299131004ed72991310047f75591310047c75591310047e75191310047d75191310047e76d51310047c76d51310047e76551310047c76551310063e64551310063d64551310055c73551310047e7694d310047e7614d310053d7414d31005797014d31005d671cc931006746594531004f47654531004f47650531007355450531005e672cc5310047e75181310047d7518131004be7418131004bd7418131004ee7218131004ed7218131004be7419431004bd7419431004ee7219431004ed7219431004f67119431004fa7019431004f970194310047e75990310047d75990310047e75190310047d7519031004ee7219031004ed7219031004f67119031004fa7019031004f970190310063e64550310063d64550310047e75984310047d7598431004be7498431004bd7498431004df764c431004f7764c4310047e75980310047d7598031004be7419721004bd74197210047e75993210047d75993210047e75193210047d75193210063e64553210063d64553210047e75d8f210047d75d8f21004be74d8f21004bd74d8f210047f7558f210047c7558f210053d7414f21005797014f21007355450721005b5748c7210047e75983210047d7598321004be7419621004bd74196210047e75992210047d75992210047e75192210047d75192210063e64552210063d64552210047e75d8e210047d75d8e21004be74d8e21004bd74d8e210047f7558e210047c7558e210053d7414e21005797014e210072d5450a21005ad748ca210047e75982210047d7598221004be7419521004bd74195210047e75991210047d7599121004ed7299121004f571991210047e75191210047d75191210063e64551210063d64551210047e75d8d210047d75d8d21004be74d8d21004bd74d8d21004ed7298d21004f57198d210047f7558d210047c7558d210053d7414d21005797014d210047e75181210047d7518121004be7418121004bd7418121004de7318121004dd7318121004be74d9421004bd74d9421004de73d9421004dd73d9421004fa70d9421004f970d94210047d76994210047d749942100c7e73994210047d70994210047f745942100c7c73594210047f70594210047e7519421004be7419421004bd7419421004de7319421004d
  | 11 => 0x66e6598b410066d6598b410072d5498b410066f5498b410066d5498b410066e5398b410066c5398b410063d5458b410066e6558b410066d6558b410072d5458b410066f5458b41006ae5458b410066d5458b41006ad5458b410062d5458b410066e5358b410066c5358b41006ae4358b41006ac4358b410053d75d0b410063d65d0b410063d6550b41006ae6250b410047e75983410047d75983410063d5498341004de73d9641004dd73d9641004ee7298e41004ed7298e410047f7558e410047c7558e410053d7414e4100e5e6314e410065d6314e41005797014e410073554d0641005e672d06410047e75982410047d75982410053d7595141004bc76551410063f76551410063c76551410053c73551410073771551410073471551410053f70551410047e75d8d410047d75d8d410063d54d8d410053d7414d41005797014d410053f7590d410053d7510d41005ad7210d41005b67110d41005b97010d410063d54d89410047e75189410047d75189410053d75d0941005b671d09410073554d0541005e672d05410047e75181410047d75181410063d5418141004de7318141004dd7318141004ee7218141004ed72181410047d769944100c7e73994410047d709944100c7c73594410047f70594410047e7519441004be74194410047e75990410047d75990410047d76d50410047f76550410063e64550410047f7558c410047c7558c4100c7f7694c410047d7694c4100c7f7614c410047d7614c410053d7414c41005797014c410063d65d0441004bf76504410063d6550441004f776504410047e75980410047d7598041004ee72d9731004ed72d9731004be7419731004bd7419731004ee7219731004ed7219731004fa7019731004f97019731004ee72d9331004ed72d93310047e75993310047d75993310047e75193310047d7519331004ee7219331004ed7219331004fa7019331004f970193310063e64553310063d645533100d5c73553310047e7598b310047d7598b31004be7498b31004bd7498b310066e7598b310066d7598b31006ae7498b31006ad7498b310066f5498b310066d5498b3100e6e5398b3100e6c5398b310066f5458b310066d5458b3100e6e5358b3100e6c5358b31006ce624cb310047e75983310047d7598331004be74d9631004bd74d96310047d74996310067671996310047d70996310047f74596310047f7059631004be7419631004bd74196310047e75d92310047d75d92310047e75992310047d7599231004ee7299231004ed72992310063e65992310063d65992310063e75992310063d7599231006ae7299231006ad7299231006b671992310063e65592310063d65592310063e75592310063d75592310047e75192310047d75192310047f76d52310047d76d52310063e64d52310063d64d
  | 12 => 0xe65992320063d65992320063e75992320063d7599232006ae7299232006b67199232006b571992320063e65592320063d65592320063e75592320063d75592320047e75192320047d75192320047f76d52320047d76d52320063e64d52320063d64d52320047f76552320047d76552320063e64552320063d64552320063e6494e320063d6494e320053d7414e320063e6414e320063d6414e32005797014e320066e6554a32006ae6450a320072d5450a3200f4e53cca32005e671cca320047e75982320047d75982320047d74d95320047d70d95320047e7599532004be7419532004bd74195320047e76195320053d74195320063e74195320047d74195320063d74195320043d74195320066d72195320047d70195320047e75991320047d7599132004f67199132004f571991320047f75591320047c75591320047e75191320047d75191320047e76d51320047c76d51320047e76551320047c76551320063e64551320063d64551320055c73551320047e7694d320047e7614d320053d7414d32005797014d320066c6594932004ec7654932004ec76509320072d5450932005e671cc9320047e75181320047d7518132004be7418132004bd7418132004f67118132004f57118132004be7419432004bd7419432004ee7219432004f67119432004f57119432004fa7019432004f970194320047e75990320047d75990320047e75190320047d7519032004ee7219032004f67119032004f57119032004fa7019032004f970190320063e64550320063d64550320047e75988320047d7598832004be7498832004bd7498832004df764c832004ef764c8320047e75980320047d75980320063e64d53510063d64d53510053d7414f5100e5e6314f510056d7214f51005767114f51005797014f510063e64552510063d6455251004ee7298e51004ed7298e5100e5e6394e510065d6394e51005757194e510053d7414e51005757114e51005797014e510063f645515100e5c6394d510053d7414d510056d7214d51005767114d51005797014d51004be7418951004bd74189510063e75590510063e64d50510063d64d50510063e64550510063e6494c510063d6494c510053d7414c510063e6414c510063d6414c5100e5e6314c51005797014c510063d64d44510047f76544510063d6454451004f77654451004ee72d9741004ed72d97410063e749974100c7e73997410047d709974100c7c73597410047f7059741004ee7219741004ed72197410063e65953410063e65553410053f76553410063f76553410053c73553410053f70553410047f7558f410047c7558f410063d5458f4100c7f7694f410047d7694f4100c7f7614f410047d7614f410053d7414f41005797014f410053f7590f410053d7510f41005ad7210f41005b97010f41
  | 13 => 0x974200c7c73597420047f7059742004f67119742004f571197420063e65953420063e65553420053f76553420063f76553420053c73553420053f70553420047f7558f420047c7558f420063d5458f4200c7f7694f420047d7694f4200c7f7614f420047d7614f420053d7414f42005797014f420053f7590f420053d7510f42005b57110f42005b97010f420067665987420067565987420073554987420067754987420067554987420067653987420067453987420063d5458742006766558742006756558742007355458742006775458742006b65458742006755458742006b55458742006355458742006765358742006745358742006b64358742006b443587420047e75983420047d75983420063d5498342004de73d9642004dd73d9642004f67198e42004f57198e420047f7558e420047c7558e420053d7414e4200e5e6314e420065d6314e42005797014e420072d54d0a42005e671d0a420047e75982420047d75982420053d7595142004bc76551420063f76551420063c76551420053c73551420072f72551420072c72551420053f70551420047e75d8d420047d75d8d420063d54d8d420053d7414d42005797014d420053f7590d420053d7510d42005ae7210d42005b57110d42005b97010d420072d54d0942005e671d09420063d54d85420047e75185420047d75185420047e75181420047d75181420063d5418142004de7318142004dd7318142004f67118142004f571181420047d769944200c7e73994420047d709944200c7c73594420047f70594420047e7519442004be74194420047e75990420047d75990420047d76d50420047f76550420063e64550420047f7558c420047c7558c4200c7f7694c420047d7694c4200c7f7614c420047d7614c420053d7414c42005797014c420063d65d0842004bf76508420063d6550842004ef76508420047e75980420047d7598042004f671d9732004f571d9732004be7419732004bd7419732004f67119732004f57119732004fa7019732004f97019732004f671d9332004f571d93320047e75993320047d75993320047e75193320047d7519332004f67119332004f57119332004fa7019332004f970193320063e64553320063d645533200d5c73553320047e75987320047d7598732004be7498732004bd7498732006767598732006757598732006b67498732006b5749873200677549873200675549873200e76539873200e74539873200677545873200675545873200e76535873200e7453587320047e75983320047d7598332004be74d9632004bd74d96320047d74996320066e72996320047d70996320047f74596320047f7059632004be7419632004bd74196320047e75d92320047d75d92320047e75992320047d7599232004f67199232004f571992320063
  | 14 => 0x47d70195430047e76d51430055e73d51430053d75951430063c65951430047c76551430055c7355143004bc76551430059c73551430063f76551430063c76551430043c76551430071f735514300d3c73551430071c73551430051c73551430053f70551430047e7694d430047e7614d430053d7414d43005797014d430071d54d0d4300d3f7590d430063d54d8943004f671d8943004f571d89430063d54d8543004ee72d8543004ed72d85430047e75181430047d75181430063d5418143004ee7218143004ed7218143004f67118143004f57118143004ee72d9443004ed72d9443004f671d9443004f571d9443004fa70d9443004f970d94430047d769944300c7e73994430047d709944300c7c73594430047f70594430047e7519443004be7419443004ee7219443004ed7219443004f67119443004f57119443004fa7019443004f970194430047e75990430047d75990430047d76d50430047f76550430063e645504300c7f7598c4300c7c7598c430063d65d0c43004bf7650c430063d6550c4300f1c5350c43004df7650c430071f5450c430066e65988430066d65988430066f54988430066d549884300e6e539884300e6c53988430066e65588430066d65588430066f54588430066d545884300e6e535884300e6c5358843006766598443006756598443006e66298443006e5629844300677549844300675549844300e76539844300e745398443006766558443006756558443006e66258443006e5625844300677545844300675545844300e76535844300e7453584430047e75980430047d75980430067a6598043006796598043006ea6298043006e96298043006f26198043006f161980430067a75980430067975980430067b549804300679549804300e7a539804300e7853980430067a6558043006796558043006ea6258043006e96258043006f26158043006f161580430067a75580430067975580430067b545804300679545804300e7a535804300e785358043006bb4358043006da4358043006b94358043006d943580430063e64d53520063d64d53520053d7414f5200e5e6314f520056e7214f52005757114f52005797014f520063e64552520063d6455252004f67198e52004f57198e5200e5e6394e520065d6394e520056d7294e520053d7414e520056d7214e52005797014e520063f645515200e5c6394d520053d7414d520056e7214d52005757114d52005797014d52004be7418552004bd74185520063e75590520063e64d50520063d64d50520063e64550520063e6494c520063d6494c520053d7414c520063e6414c520063d6414c5200e5e6314c52005797014c520063d64d48520047f76548520063d6454852004ef7654852004f671d9742004f571d97420063e749974200c7e73997420047d709
  | 15 => 0xe639885300f4e639885300e6f60988530063d645885300d6f76588530066f765885300e6f645885300f2e64588530066d645885300f2d64588530062d645885300e6e635885300f4e635885300e6f615885300e6f60588530063d649845300e77619845300d75769845300e77649845300f36649845300675649845300f35649845300635649845300e76639845300f56639845300f66629845300f65629845300e7760984530063d64584530066d625845300d77765845300677765845300e77645845300f36645845300675645845300f35645845300635645845300e76635845300f56635845300e77625845300f66625845300675625845300f65625845300665625845300e7760584530063d649805300d79769805300e7b649805300f3a649805300679649805300f39649805300639649805300e7a639805300f5a639805300f6a629805300f69629805300f72619805300f7161980530063e64580530063d64580530066e62580530066d625805300676615805300675615805300e7860580530047f745805300e7b305805300e78305805300d7b76580530067b765805300e7b64580530067a645805300f3a64580530063a645805300679645805300f39645805300639645805300e78645805300e7a635805300f5a635805300e7b62580530067a625805300f6a62580530066a625805300679625805300f69625805300669625805300e78625805300e7b61580530067a615805300f72615805300672615805300679615805300f71615805300671615805300e7861580530067b74580530067a745805300679745805300678745805300e7a735805300e7a435805300e7843580530067b72580530067a725805300679725805300678725805300e7b325805300e7832580530067b71580530067a715805300679715805300678715805300e7b315805300e7831580530063e74997430047d70997430047f70597430063e65953430063e65553430053f76553430063f765534300d3c73553430053f70553430053d7414f43005797014f430063d5458b430063d54587430047e75983430047d75983430063d549834300e3d74d964300e5e73d96430047d70d9643004ee7219643004ed7219643004f67119643004f57119643004fa7019643004f9701964300e3d741964300e5e731964300e6e721964300e6d721964300e76711964300e75711964300e7a70196430047d701964300e79701964300479701964300d5e73d524300d5c735524300e3f65d0e4300f1e53d0e430071d54d0e430047e7598a430047d7598a430047f7558a430047c7558a430047e75986430047d75986430047f75586430047c75586430047e75982430047d75982430047f75582430047c75582430047d70d95430047e75995430047e76195430063d7419543
  | 16 => 0x8d54004f57118d54004fa7018d54004f97018d540053d73d91540053d72d91540053d71d91540053e70d91540056e7218d540056d7218d54005767118d54005757118d540057a7018d54005797018d5400e6e7218d5400e6d7218d5400e767118d5400e757118d5400e7a7018d540047d7018d5400e797018d54004797018d540055e73989540055d73989540055e73985540055d739855400c7e73d81540055f73581540055c73581540063e65950540047f7655054004bf76550540063e65550540063e64d53530063d64d53530063d649525300d5e73952530055d73952530063e64552530063d645525300d5c7355253004be7498a53004bd7498a53004be7498653004bd7498653004bf7458253004bc745825300e3f649925300e3c645925300e3e435925300e3c43592530047f70592530053e7498a530053d7498a5300e6c6258a530053e74986530053d749865300e74615865300e7b60982530053f74582530053c74582530047f74582530063f74582530043f74582530063c745825300e7b305825300e7830582530047e76d51530063f64551530063e75590530063e64d50530063d64d505300d5e73d50530047d76950530063d64950530063e64550530063d641505300d5e73150530063d64d4c530047f7654c530063d6454c53004df7654c53006ae6498853006ad64988530066f54988530066d5498853006ae6458853006ad64588530066f54588530066d5458853006b66498453006b56498453006e66298453006e56298453006775498453006755498453006b66458453006b56458453006e66258453006e56258453006775458453006755458453006ba6498053006b96498053006ea6298053006e96298053006f26198053006f161980530067b5498053006795498053006ba6458053006b96458053006ea6258053006e96258053006f26158053006f161580530067a75580530067b54580530067a54580530067954580530067854580530067b535805300679535805300e3f649905300d3d769905300e3e639905300e3f609905300e3c645905300e3e435905300e3c43590530047f705905300d3f76590530063f765905300e3e635905300e3f625905300e3c625905300e3f615905300e3c615905300e3f605905300e3c605905300e3e735905300e3c73590530063f72590530063e72590530063d72590530063c725905300e3f325905300e3c32590530063f71590530063e71590530063d71590530063c715905300e3f315905300e3c31590530063f70590530063e70590530063d70590530063c705905300e3f305905300e3c305905300e5e7398c5300f1e6498c5300f1d6498c530063d649885300e6f629885300d6d769885300e6f649885300f2e64988530066d649885300f2d64988530062d649885300e6
  | 17 => 0x80000020010000000002000000000c0060070000000000001000800c00c003001001c00000a0018008004002001002003800e005003c000004002000000600500000040000050020014004001000800400e0040000004004017002000000001400100080000000030004004008008000c0020000040010002002000000000400c0030000002000000001400000d0008000026002000801000200a001000800000300000240000000008004000003000000001000800100000080010000014000006000800000000c000800000400500900000060020008028000005001000000600100000180020000000004008002001800000400200000580080090000000004004004001000e007001800000202b001800000a002004000402c0000058000002006000000000000200700100000060058048000004000002c01a00400000000020030030000000003000800803a00100000000040060000004000001000800400c003000000c00c0030028014000006003000800a0000020008000001000800002e002001000400000000580040000020000008020002000000000c00000e80140000030030004000005001800800400500500040000000008000002000000000000000e000801000200100180000020010048014002000000800400800100000000000000010014000007003801c0040020000000004017000000c004006006800000400200e800800000700080000040060018004000017000000000a001000800000a0000028008002001000000c0020090008000008002001001c00c000000802000000100b8008008000005002002e0000010008002004001000800000600180000120000010004000001006000800600200100000020020068020006006000800000a005003800000c00300000000100000000000000001001000400c0020018004000007000800800e00000000400000010040000002000000800400001200000000000010018010004001001800002200100000000020010000000000004000800000400c000001c00a00600080240000000028000000004000002000600100000100000000010000000000001800800e00000200500180000008024002002000800000600a0008000000009000801c0020010000008006005000001400600c00100040040010000000000001003000000000300000040020010018004008002002800000a000002800800000400180180000020008004000000000000c00200100000040020000018000000002004800000c001000000000200100100200000090028004004000004800400c0010047d7098f540056e7218f540056d7218f54005767118f54005757118f540057a7018f54005797018f5400c7c73583540053d76d52540063d76d5254004ee7218d54004ed7218d54004f6711
  | 18 => 0x5563833821a800000031200024840009aa0810cf93c296e00000016a03352688a7c00000000000000005f313117a80005bb462000000085e12317500000003071a7c6c20001a3000000000008200000008bf00000000000000000000000af507f000000000010408ecdec187000138c00000000000014e83f235e006ce9a31f00001992b20000000000bec0000002d8481a8c10001b4400010b33e00000001fc51f00000000000001904cf00005842ad81da43f5a3a0a018c92002a854092400000010bcf140001710000000826000266075892b50e04c55862700001d449700000001e0d2e40005a0000000023200029c000000000000011541b359e283800094300000004c0a9f00011dcb26a7b0001bc400000000020c8000000000298074641300022d45ba2a4117800133200000027dd1968be55600000007c0000000000000054998f88d0000000027800034b0000000c480000000000000542000000000000000000000005c938b0000e0a000361242400025f0ba80002bc39c10100006a800000004d00004290028000007005000000a0030000004006000001800c0020020028018002000001000400200700200400020000008014014000000800805000100300080020020000000008002003803000200000000040040000088000002000000000000a001003803000e0030000004002000001800c0040000078010000003001807c00e005001000000c0000000000004001000002400600200480240000000000008004000000000000200b0010010000015000800000e003000000000000000100000000030000004000000003800c000000003000c000006001800000400000000000040090018024036011000000000000100280140020010008008000005012000800400300000040000050000000000005001000000400000380040000070020000006001000800000a0000010000004000002800400600d0000010000018001004c004004000005800400c000000400200000000000040010008000004003000800000200100080000060000000000000002000004400200500080040100000030000014002000801c002002001801c0020020018030000001001002000e000000800400200000080500000070010010000002000002000400800000040000060000004006003002800000e004012801401a000001800c016001001800001400100200200000080030010008014003001002e001000003c014000002002000400200180000020030020000002009005800400a00a000000802200a0008000008000000800400400700000000000000018004000000003002000000500080000040000058000000006000800c00200400180040000000000010018000000002400000000000140000000000014002000002800800200200
  | 19 => 0x48800000000006c87600003815378000bca4bc028827420239f005122000057a349ad79578062000000119a000000041ceb40003190248a76000000000000099b00000014080000000aec00041f30a8001132ab803800000000002639c8400000000026500004824ee8000000000000000025c0000000388000000000000000034a00000010ae838010000162e5092ef968144a8ad38d232491c28d2f019c0cd84c612e07241cc24d45b21dc84aa7e37113ac6f222c0159338b3274418a0000000596000219800073c000000000000007b00002920000000000c960004120d8ce8e31031ba53121e7cc43e837800000000000000007b341c83345e011b37ba5394d200030f0000d520002ac800050800000005e4000a7809b184506600001b97e40000003f6a498c1492e00000014ac000000000038c00000008400003c11eb08195540004b19c9c5f400000000000000000000000ae200000000012581e11720000000213366000000000020300013e6000000101c000096067800000c000000045854c56705d2cdcbf600019319ac0005b920c8ae101e71c25b800106890d28980000000001239a690f00000000000ff850b5408b98d800600e780000006cf40e000028a000000000000015106e80013b834f000000000038c000092400000046e00000000000002aac0100cc2d1800000000000000014ccb4c0dc2cd030236f00013b400060908c0000544000000000000046b33a80000000000001a3103412d0000001130115336ab940002de1b1065c17806836f80004a057650319a4f2a00016a80003361c1000082d69c7292fe8000ee87c100000010e600000000000003f70ff00000008d4435a6e80d20005a4a7b4d04000292105c000b3b5a5149863c7f82c3800098654708f971d48a000000062508cad90002180ff680a56d9524ac21a300015ac8de2b9000205404c00018e01fc000ad800002288300c100008c46026ba000268c7848cc0b50534f560000000000a940000000000000af3318000121c36a000000038a0004588000512256000232800000039680000008ac000000060c0b3000000000000052880000000002309994000000000000029000000019c40001d2000000135600000e000000000000016a85403cc5139b140000000000000bf80bd10b2a340005bd5351ac0000000000000000000000000000000003e58814000048005a514e660001d3a9b80009a500000000000000000960f1645b54594406900ea0d12d5c000837583a7acd3000016301240f66124928000a24000000000000037a4d1132c50c0004ce01781be0004eb800059c0000000a0445ab580000c000784ee273170d5ce30e1b380000006a621c90c45ae00024e092058a3933fb00001a89ad0108000eaa4011940d00cf455437486
  | 20 => 0xfd1366c60002a080d80004eb14b00000000001dd504e3fc0000000f9249d04d1c889484fd1d1299149e4432d8ad7d2a24d04c2049473293a0291c8cd32b1127cab3153a44600003f04522b237a2bf0912a8e00014c88500e133300016725fa20b00012be15800004ac00000008929fd63c54e5188744fc07d50000000058a9a09900006da68d00010400000a557b00014d04674aa918800044416c8a0125a0002daad442f864e31e8000e0c8822ce2d700000b42712cb0000a8a00028d40008a60001bb0000b4b0001ffc1a200042c80010b839e0198000a04000472800112e1f200000000006dd0001fd4000a620001ded486198592a1b495a5ec0001e9c4541a012d0a5c59600000000004282c00dd0200c6a22556e800000000013c274c63a9bc43f1acc6783682bb9d752720432f30ba5304000158800000001f00000000005f7295a9d91cc0000001e48000541282ac804da3ad25912640004710000000e689bd32c81102caa894ab89f09d0758345a2c08482f7563a23d05ea5903aa2747084e02cf9fc0594a3c48a05c0b504a00e80cb8000000379193c38e35f1d30c14a6a000035a36c4a494113a8000c369220000000aaa7ee01a8b5834e82e00012680006ee517a28000032200010e11067eb3bd26150a09733021e180ee6c900001840008311c429dc0003420002ce800000008000000f86fe5681c2542200000013087dc28b1f098300006fa234801477e13b000000000007200000010800000000d7400049e0000000f20a0000000007800c41e4212cd6c13522410c00009b915a0000436000000123c0e61b226200000008c80830000d0e0833cb800085a00000003ec3a800000000000008143e1a8a40000000000000000000243192400000048f0240000789000000000081e16d800000085d3d68d5c00014f11215e0b8a000000000000046000000016700000cf8000c6c0000001610e9c44100020fc0000000000000a6e0000338cd88c85cf0000000000349183a3655d40000000dd8e861c231e00e400080500023d0ae000013f01280000004350e580004bb427ab9800083e4c500008b4a0200021d53b0160000115cfd41e8000000052697725800e94aa6a115a8e6d370891264a37cc46b180c780a00003dd00000000007590001f48ea86b7031800084c0000000000000000430a0600000002eea8e87d2000111800086600035c29411aea6513580013e80000208afc0000001a98000f4800000027400007394ca80013c000057a000000000000000000000004ad00000007a1000000053265c1fd9d200000002888bd82a840f1848631500854213800079275020a1a3c0000000f100000000004541f9d0cab27257104800030c3df800000000000000006e41f000000003fa00034e800000000000023740006e71a380011200
  | 21 => 0xa5f00000012c22ec00000900000000000000d0a00000009e400093c05488d8000735309800000000052b80006cc4cf0000b30e640f93e82cd4be28814150000b6c00000000015440000c106bc14432132a05e8cfe51a34403d00006b100000003e80002248000aca00042a80000000b600000000000001d5000000000000000000000001112454348b00543870016a0000722a581a40002dc00000002430000000cc05ad0001ff800000026600000000000000000b160da0000000000b56104822c74200005c9eb00000005ad18191c20b200000000000001ae00000006fd02325d400000050a00004306e40001fbd4f80004572d3c0000000000e4400000047e10c9142b28000079c000000000000148200030e80000005571e180000000005878000000000000029c00000010600000007a90000dc4bb69f627200016a8b5318d85180009c6274800000000000002bd3aa45e00000000005a10000dc00000000001954a320002870000378000000000000094800008d0a5e0000002a6400032357c00004980362e013b000088a00000000000003ce11354c20004a31f280006c10000000b040000001c940001410ae834cfb88da409010908eabd00028c91469c139e800000000000000000000000000000e1aadc4d80190000000000080c0000005a31aa03c81f74fea390a2a00043a17444fe1c300008c0000b0a00018940000004e5000000000000000000000001e796f153c00000000013a800012e80000001d5049a10c8ca161305ab502e803e5ae823cb485ac3d000448ecb4413095a8d5640e44a242d56296b2838fc434a1b415e8dcca8617131c0a9c35a25554904156868510cb1d9c0001442368730f260b13901af86165031f79574000360000227c00000000025f40002944ae800056c000000240855600027d106800022b24f83e061478528401c46dc71f001a21969094413d0bcc10862d110257101c28300000003103d20001c28766000000000000002d47f12cc00000000000012d8a6745ba7bd2a605a00000011866791e315d123a11e000031c00000000022bcedc88c0fb27c0900983000000098200003ca8fc07a3c74eda0a40da35e0000000000352067122cba4b5b2af108410c23e47a80000004a24890be000000022b114c7141ac00015605fe43b3b0a5080001ce0c012f42500000000ea55fa00017a1e65380a470002cd89b24452da10d0214a583ef9b84b6400001c14c40006d60002c9804a913000185800000000025c07740002ff2c2c8aa70257b9d5ccfc00043709bcbc412727a00000000003f48000000ab90ec9d6d08400028e800075675f27b92d40009792e69f8c7408c24ef8000000000000000106c58e1370000ad06f800000014a81bd01a1868ed6b2d12100000001671698
  | 22 => 0x146cb4a00000000012464a859801b80000001e810b053a00043825c4e2a1df0001e1c6ea00000000004e600019524c46566ea15e00000000000002c654b86f550d00000003773e1000000000000004515740000000000f280005102c380000000be800054600048f8d68c40ac03e38b840000000000e14d3c4df0000834000000331800094a5d60000000000ae80c58bc400052e18b80001ee36c45480000246c748d260555a00000000000005ab0002c6c0001cd5a28e1ce9803023d11009944ac0119dbc11033b0002a142d89961da8d9036a00000029782480000000ce92a000000000000000000a18000000481000000139c00000000000000000001d2c9a40000000000000504243800000032506800000000002c302a8d245bf5081558ed844f35e98711785800db2010000ac600026c559a3da21f00010e21ae434a7d4b740001fc1ea00005b70001898a026500a000000000001f321bc0002260002c409684af4f400000000b8543173814000000019085fc00008786c40006e332c1f980000000001d2800000005b80000000003482afc000000000154c0001da4111888000a2c06b0aa09360001840001652a3d149163ca4e3f93d180007340783d111b8c0a562246030800050a4780000afe3f05712be40000001dc08780000004da881c0007b419e9020000000300a0ed0a438200020e90560000000698fbc00000000016461423a300010b40004319a90f1e6ff0001d0079443d56880000000003ab000000000000000002a400000019ed3d45c221183c4ae4000215177800081913a0774eec00000000000001380000804b94000000265cd5a000000000000000034b0728098770554800000000000020c000000051c1ef938881347d82b00002635250394f880001351374e002571dc8000c900004c310dc00026800000000007b804a9c7400039800011fc24275e0001008ce666e1999b980000000000f6c1f49781360000e740993be20b04a800019f803cf08000000000000000000000007ce000000000000000000029ac0000000ff80015ac9bf00001d050eacf000000065a75224180012e800052315d40000002832bfc00042200003ac5900001ea9f388e816e3dd85a0000000100205d22008c34d93d8030000161000080682008e25fc0005a600000000000000000000000afb1e980007fa0000000bd566400000000005d0b3d000125c00000000000004383200a385ec29657e2c480011bc78e1f1000000000038399909ea63a4b3072c0009542d9a00ce2067244589050fe0003a091c0d6ab012d3a1041369cc25596c0d4e70e471027c00048436f0a2846e00000000012c47283c4000110e0004a4800000000022a00001c600002017bc2404f051100003dc3923cb2ad0000288486000009637c000113800000000029c4000
  | 23 => 0x686248b1ef4c7e28f0c99c900008f737988b8e9e24e3dd1648b98000000013400058d2f385900008060000df4000aa345c88e96282fc1790000fe44754bf00007eca1b1688bf400072a3d7872021c0000a5000000000000000000000004c91710000807000165517a0004701bf00280002e4000099000054b8000b100004ab000000000000000000007f3000000138a27128b0ce476e0005222734000a79447000000040b00000000007e51c491485180000dca8603ea54000003a00009270002a94cbe2452ca00014800000000001134ac2000000037e9a44f8a09539e46625fa4141863bc51400000000000000360000b2e00000000002961ab0000b3454d00013fc00013c21e27984e40a838f1becf9e7824748dd04660000002b5cb2e8f20601ec913847d59094e15c20fd3e2827000094d00010e86061565609801358000088a828000598000000000000000000000000000000000000000000000095457d00000000006eb0000000000569000195c0000000000000d5e50f0001cdc59e00027f1a5d6a4aec0000ba85920190001b0c00010c000199c6f06e51da09f44cc29138a000000000000023d80008960070dfc76448d35186ecffa0002628b6021285f1b5836c5428f9575804d1744ea2000a5530eabe3e680001d264a13b28d005e4930642884ab402926e187c00000056f85881ea8560558440c3060700000014900000961c64af6000000157000077d3290f7800019d2d719113ce92943da7e92a46ac0f98e405d61dc39d8fa8be8000000000000069500010540000cb337abf80000000000fe8db62e5404800000055b00024f400071700002b400082135c82515f4a4b000196c00000053a80000003cd20600000000003ed2874e7c4f80001300ff20041efa6452763d400005fc00061951704a4e240005270cc814c01e4c01840da40003202d087d6157476804152023c5a094cd2960001f19ed4b3a5a923628a82da93e0000000000000567000000061702e8000abe628089800063251e3d80d0543e29a49521f00008eb29e8000af2000127a3a0a5a1f944f0000f720852a9000141800049923f4b3600000000008120a1301929c33286703b056d56634336c8e511d8a2b23c8e9400000000014f0260000000000000005800000000006512be283ca54b60387975d41a00000000012c8811389800000000058180002ec000242990d2948a454e011c62200046b0e2c000000173a3540006d8006800000018d00000011642ef279154009e4955aa960469c9de0c1935d2d20004bb1b2c78a9a0022a12551e000574a7953f8355434193400000000005cc000000000000000001643d000024439700000000000004c700009f800014d80008087e1142800126028e32380005f60001108000000ab548dac314460000000001350a170ce
  | 24 => 0x5267c0f40f04118fb53f02aa4b78000000af026b07813fe6940001cfc0007db3d29e3417c00000e97a4bc22c42df20311260001fa8000d5c5ff3d72224000ab02b18000000000000176800099d0002b2d14a000000000000012f0001dcc0000004c8298cdaa9d90001a00a28a370000d1071c90854626c80005cb000078c000aae40680000000004228000e3000000016bc3b6000315800000012300022ac0002df4000000000000000000000012a13491e076c00008ea0b400047c000028c0622535038b04cbca133ec0000000000000224967e8ff2d1146070c21a505a1900000000000b400127722b70aa43560004820fcc0000003a9917564446326d80002d630244683706a059100000007b800034484ccf909371c6a4a055e41c1020000aa24914f70324000ac8000000056e00055d80007d000056d0000000a5d0f30000000a5a3040000000000000000106a0002c2a62d17000000000000003f42c5000070047b000231d54e21700007ac0000002a58c9c000b1a159800000000000000002aa07e00026312f64d400000016b272f40b107533473800000000000000001b108a22cd29117b89b47360000eec496411086a0403603c40000ffc86c00002da634ef09f9497abb4000a83381a128a8a3a43fd07bc160000003839d3fc18a1638000f1800033101400000000001e048a083d156046937c1fb00003fc000022000000000000000018a93a49002e987115a697c2f580004ca000000014c00095e00004f51e200031880000007e404c0bb80006aa00000000000000000000000000000000000072c50ca220cb400026980000004421869da4e4c4201e71dc466200002f9c10660000286a40d28eb06037a53c898a30000147c000000000117c0007a648c83b960405c0000ff80004731ac2c4c2b87c6000040c0004a945a2790bf00000000668b202be22580006520000001a0c00001500000012800002909d7032800056a800000056f02b000000000012883c8c4e7912a200000009a10b480004ce0000000ab4dd0a913de2c58d4076649a2934856b053b517c8000777359000000015f26a80004320000001a2800000000013cd36c00000000007c0000000000030c7ec41e0900f3a0bb2980000c5e76414e14f8db8b4d29b067909891150b0fb0ec629e4d4aa6d1dc4a359f1c055de0d542d9678fe89170001834000b0d52480000000000a70cd00009072c62a9138e9680f48e3c3245e300017d4df200051b0b8c4bc66a3982110d022ba4d3ac7d59451c33b17700000001ca8c902de0171ad9a393a208729486a4000a983b014315505200d098e447e02a000202d3684b13a10224eda2984f617a000029040408d40d493f1a68da562400018b00003ae00011ca2001c00004682b150b04ef00026bcd0c00000000008148013eba8e41e
  | 25 => 0x96a47c19dc2e4a260191918e569181d88328e107b744a8b0d5407d3202976000015a0fc2a2011a6ca07608e139070b17694945f200025b1da04b69384c4800000013900021c800068400021388d417800000009e208e0b180015c854854a241943c2b022500009745d90000314c043133bfa9e80000004f481640000004240a083a64e14b02a980000000000a953960000001b684f68020000000450000000000000000018a842017e000000000000065600000000000005718c1043ea150000ef4c52ab73cf12f80000003b280008b871100017b49bc0004628000000a2d1e8800000008134880012b07b600011c8000621467a8207b22dc46982b931e14c1d71de50f26450d41ea83ac00000000015e4a530000000fb200027280000007624c40f940007e200000000ae935366acccf340d72f20000000b2f584885538400000100011ce93312c9df87500000000b50a4600040e8000be000009f000065800c1aca96d14411900000000000000c80e745b49a600000009b054600080000004cd000122800000043b0910cc200000005dcd7600000019f4dc00003cc00000000002e329b4a50000013829010456d55900012ce92400000003da000000000000088400000000008bb0000d300007d60000000a9e9ae2739a700000004b69260dde3d7536229d2b6a84000214c0000975008f9141200058a98cc30a8d200014d15a4a4200012855928b3000000077cb1d11398508367802b21fc44248d80000cbc00000000000000000004f18f6000041e0000000da80650000000000000000000092c1e51bf15cc9722ae38da1b07069e200026dcb0621d4719fdcd9c0004ed2724d9000035a000000023d000140024c0005822c9110a93647d2678920aee00000016543af0ac9ec4acc211253207c36e4fb2a614e52ca00018d0ec06a21370002b8000084d00000000000001e5911c000a730000d940006d000018d000000000000000007310f8983c2fc00022c11f800056c0001e6ce8a1840001d2441e9c30000000e186ed01700003f413a00029c8d7e6f051228ec0005c100027ec000000000194c0009bb000000000003b08b8928c761aa000000000000000000003d80005988000000000000000118c0005789a94a74000000054cce80000c701f542400035100000000002ea9fa0fa290150186f80000001702428000000595aa840a8000479800000051748e00000000003cfa5e91de2775620ded4a400000d28cccba2d256f07783d400018c1740ac00000001b4d36600000004fc00099353e8000c5ca954f918b00000005260000dae0005578c3c4c872e32600000008d13341f7441c7d400023009280000778000000000000000000000019b800000000022c800085c53f0c880010360004750000000a050b30138000000000000068a8ce10
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc1c76551434c0010790cba6a0980020fe1f64d41300041ec38c9a82600091d841cd504c001838c839aa0980030e1db64541300061c3b0c8a826000b19841cd504c0016930439aa098002d460473541300068dba486a826000b5181cc9504c0016930598aa0980028e219549013000c3c432eaa026000d197550d404c00343906baac8180061720d765503000e0e39ac8aa06001a4c83551620c0034a906aa2c2180020f61275980300041ec3cc9a80600083d87593500c00185ae9316a0180030b5d162d40300061aba4c3a806000c3574587500c00146b03322a9900020f6107558f2000c2e41aecaa44000a1d83191548800146b02322a9100020f61275d8e200041fc22ed29c400083d849d76348001858ecaa284900028d61053d852000538c00a7b0a4000c55755cc614800192ae8b98c2900021d61c53185200051ac20a630a4000a718014c6148001c4aa8a10c290002a9612321852000658ba2e030a4000cd1735c0614800186ae9b0ea0900030d5d061d41200041ec20eab184000a1d841d5630800107f0cba0a6100070798d7414c200041ec3cc8298400083d87590530800183ae8b18a6100030e9917014c200061cb22e02984001c5a635c053080018b2c6b80a6100028d610539842000538c00a73084000a358414d61080014e30029ac2100032a591700842000664b1ae0108400083d849d6600800107b0f326a0100020f61d64d40200060eba4c7a804000c1d7458f500800186ae930ea0100030d5d161d402000652b20e29004000cc5631c52008001c92c6a82401000398585504802000516c14c8aa6200083d841d563c40030b906bb2a9080028760c645521000516c10c8aa4200083d849d7638400107f08bb4a7080020f61275d8a1000671b12e010c20009e287c85208400107b093aec6880028b61053d891000534c00a7b122000c4d755cc624400191ae8b98c4880021b61c531891000516c20a63122000a698014c6244001952e8b80c488003325cd701891000670b8ae03122000c34765514144001c4aa83128288003295d0628c51000616ba6c5a822000c2d7418b50440015c50d10c4088003381d921481100041ec26e0b28200083d841d5630400143b083aac6080061e6017614c100041fc32e82982001c1e635d0530400107b0f320a6080020f61d6414c100060eba2c62982000c3a645c05304001872c8b80a6080071698d7014c100062cb1ae02982000a2d8414e62040014d30029cc4080028b610535881000534c00a6b102000cb1645c021040019a2c6b8042080033858970084100041ec24eb300200083d87993500400107b0eb26a008003075d263d40100060eba2c7a802000c2d7498b500400185ae8b16a00800329590724401000662b18e488020008e4875891004001ca2c6a822008003985895044010
  | 1 => 0xb093b463a80020f61a748c7500041fc3ac918ea00083d8759231d400107b083b263a80020f61276087500041ec34e810ea00083f8759021d400107b0eb2043a80030759273087500060eb22e610ea000e256448421d4001872c938043a80030e5917008750006b090ae010ea00083f87590645400143906b20c8a800707cc17418d5000e1d182e831aa001c39305d0635400143b0831e86a80030ed917010d5000e2c31ae021aa00083d841d9325400107b083b262a800358485700855000e0f31ae8298a001a1c8359543d000186acab8e85a00030b59572d07400041ec30e6aa48000939801cd549000186aa9b8ac5200030b55372586400061cba2e132a8000c1f741cd655000383b0839acaa000713a08735954000e26c10e6b2a8001c56811cd65500038ab0239acaa00071660073595400060eba6c629a8000c5b635c0535000107f0eb2e86a00068720d65d0d4000c1e43acaa1a8001a1c83595435000143906b2e84a00030d59571d09400050e41acaa128000a1c83597415000185acab9682a00028720d65505400050e41acb2028000939801cd541000143906aa2c62000287e195458c400050e43aa8b188000a1f80551631000307b08bb0a6200070798d7414c400060eba2c62988001c5a635c053100018b2c6b80a6200020f61b7590c400060fbaac72188000c1d7558c4310001c1aa8b1cc4200028b610539884000534c00a73108000a2f865516210001c1aa931ac4200038355163588400051641aa8b108000a2f80551621000145b0829ac4200029a600535884000517c2c86b108000a2d8510d62100015530021ac42000385551639844000712aa2c53088000a358414e61100014e30029cc2200028de1954584400070aaa4c6b088000e155458d6110001c4aa9312c2200038955162584400051a41aa8b088000a3780551611000146b0829ac2200029c60053584400051bc2c86b088000a358510d61100015630021ac220003075d263d40400060eba2c7a808000c2d7498b501000185ae8b16a0200030d5d261d40400061aba2c3a808000c1d7558f401000185aeab1680200030d5d561d00400070caa2c7200800083f865d5401000123906baa8020003075d5635004000616baac4a008000c357558540100030790eb22a998006872195450f300041ec20eab16600083d841d561cc001872e9384cb180028b60864552300051ac08c8aa46000c1f641cd548c0012b30039aa9180024e61376542300058c41aa92046001958835d5408c001473003aec898003075d5731913000616baae43226000c35755c4644c00194ae4b88c898003265cd701913000654b92e03226000cb1715c0644c0030f10cb86a8980030ed9170d513000516c10c8aa26000a3581191544c00107f0fb20a6980020f61c6414d300050e432a8a1a6000
  | 2 => 0x275982310041fc22e1b2a6200c35745c4654c40145b05322a8988020f21d64551310060eb20e6aa26200959801cd544c40107b093b4a698802c520d54505310041ec24eb300620083d841d563c840107b093acc1908020f6107558e210041ec24eb3044200a2d82991544840146b03322a8908020f6107558d210041ec26e0b28420083d841d563084010f3003aac610802876107558c210052cc00eab18420083f865d0530840383cc6ba0a6108020f61e6414c210041ec3ac82984200c1d7458c53084010f70cb80a6108030e9917014c210061cb22e02984201c5a635c053084018b2c6b80a6108028be19545082100706aa2c6a104200a37865514108401c2aa8b1a8210803a158d425042100722b2a649884200e85644c93108401a4ae8aa2421080269613734842100722b2ac69084200e856458d21084014cb0c29a4210802c96105348421005b0c00a690842009a5841c1210840138b0638242108020f61275980210051cc24eb30042008798714e60084014730829cc010802b820121580210073132a42b004200e61654856008401d44c890ac010803a859121580210076131a42b004200ec1634856008401473093aac0108021e61c53580210051cc20a6b004200ae1819096008401c52a8a12c010802aa612325802100570c0c64b004200ae1829056008401c62a8a0ac010803a8509415802100558c2462b004200ae1828c56008401d826498ac010802b821d2158021007313aa42b004200e617548560084015c70890ac010802b8611215802100731aa242b004200e615448560084015c70690ac010802b860d21580210073129a42b004200e6053485600840107b0d3a0a7a80020f61e6414f5000616b24e429ea000c2d645c853d400186ac9388a7a80030d5917114f500041ec34e8296a00083d869d051d400183ae639ac9a80028ba08735935000516c10e6b26a000a36811cd64d400146b0239ac9a80028e60073593500051b40ee4b26a000a3581dc964d400143d07392c9a80028760e725935000517416e2b26a000a2d82dc564d400143d0738ac9a80028760e71593500050fc1ae0b26a000a1c835c164d400107f0eb20c9a80020f61e6418f5000616b24e431ea000c2d645c863d400186ac9388c7a80030d5917118f500061d322e031ea000c39645c063d400343906b2287a80030b5927210f5000616b22e421ea000c35649c443d400186ac8b8887a80030e5927010f500061cb22e021ea000c35649c762d400186ac8b8ec5a80030d59271d0b500061ab22e3a16a000c35649c732d400186ac8b8e65a80020f612768cb500041ec34e9196a00083f8759232d400107b0eb2465a80020f610764cb5000616b24e5b0ea000c2d645cb61d400185ac939683a80030b59172d075000616b24e598ea000c2d645cb31d400107
  | 3 => 0x2b00a600a3a849d56014c01473093aac02980696a0c54580530051b40ee4b20a600a3581dc96414c0343d07392c8298028ba0b715905300516c16e2b20a601a1e839c56414c0343906b82c82980687a0c705905300517410e0b20a600a2d821c16414c0146d02382c8298028d604705905300d2c41ae8b00a601a5a831d16014c014d5043a2c0298029a608745805300539408e8b00a600a71811d16014c014e702b92c0298029c20572580530051d420e4b00a600a39841c96014c034b506392c0298029ca04725805300538c08e4b00a600a6b825c56014c014d104b8ac0298028ea1071580530051cc20e2b00a601a5a831c56014c014d50438ac0298029a6087158053004acc00e6aa28600999801cd5450c016330039aa8a180247a18735514300e0f430e6aa28601d0e821cd5450c03a1b0439aa8a180745a04735514300e8ac08e6aa28601d1a801cd5450c0123b0039aa8a18074660073551430048cc00e6aa2860083e86dc15450c03a3086b80a6a18028720d54d89430061aaa2e3b128600a1c835536150c0185aa8b96c2a18028720d541814300616aa2e43028600c35545c46050c0343906b2a86218028761b5450c4300d2c41aeab008601e185350d6010c01c36a8a1ac0218020f61e6414c520061d322e0298a400c39645c053148038b4c6b80a6290024e60073553420050e41aa8b1e8400a358414e61d08014e30029cc3a10028d20d54587420051bc02a8b0e8400a358414d61d08014e30029ac3a10028de1643587420051ac2886b0e8400ab18010d61d080383cc6ba0a721003075d16314e4200e2d31ae029c8400c59635c053908012730039aa8a10034955271d09420060eaa2e63028400c35545c46050803838e6b22a9990069520d54587320041ec24eb306640083d84dc1658c80186aeab8cc9190028d60664552320041ec3cc829c6400c3a645c0538c801872c8b80a7190028be195450a320041ec24eb304640083f845c3654c80185ae8b90ca990028d60664551320041e43ac8aa26400c1d641cd544c8012b30039aa8990020f6127694d320058641aa8a12640083d849d6600c80107b0f320a6288030e9917014c510061cb22e0298a201c5a635c053144012730039aa9a08028720d5458f4100516c20a73168200a698014e62d040145906aa2c5a08028be015458b4100516c20a6b168200a698014d62d040145f0b21ac5a08028b6144358b4100554c0086b168201c1e635d0539040183ae8b18a7208071698d7014e410062cb1ae029c8200939801cd5450401a4aa939682a080307551731814100616aa2e43028201c1c7359154cc40349906aa2c5988020f61275983310041ec26e0b2c6200c2d755ca648c40145b05322a9188020f61e6414e310061d322e029c6200c39645c0538c40146f0caa283188020f61
  | 4 => 0x20a50580000010a8001542140007c00000110082218000dc00008609000149202000000004306b8e90f23e4408a8a364221880a8681a64389e21227a7d49711807e0784e81942c424dca0d0d22f43592516a6a8339273fc330d61da0687aca60000005c4899e135a00000000000000f609e0424d0839ce016770cb93f1607f50e1193c4678fc8cd0008b8a906a37c2c8001a901a0010988a000824650930502f0420712c2154bf924040454119f700028c0015b000125059a7094031148001d82dc000b10fc5bc331b33968107b8cb2883a89c98e236099180590008ac00006462174000f53ae518000eb33683c0018d000000980892ea1104c00000060d0601414807c9a88f1a4000000990004e00001a0004690d82e0007bc541ca0703c0468e84143ed109a036a12d0a0a5356230fd8e52640c8e30ae0544341684c0b65e8619922508a0cf82c276800000d416c3d03608018a000c796c2f0000819b40ec640159502c8268000560008980000039e70c0507714c488560971563540997022c474fa06d2c481c001d811640030173402610c39e9000398d1017036370a18d709a0008219a01e388638fe2e8000138e71be0000810526e72050851000000879a43c60e8001c90ca3b8f39cc2b00003c00010c650a40000005b9128950723010f98129680c6c0b81c28646b0f82ca000c49792f6000b183c30c8cc049d60002e491a244467c0001e41520000b0000de8d02f05320c000000002d00010415943c550e00002667a0c12020000000005f0000007188839a000bb09f000140490f33420000013e18c5f8438fa0000008b84603a1390e9b634a1c0201bb06a150ea1d307664c000180086583a84500011cdb8c12847b4ca8ad3f87e1161bd360558539982da1680007b000148a2a323bc0000415a120271178003646e89d2221fe3d8fb0ce09e0c4678c207c89d0b9d00004d8471722541f41e9e50820bc12800044008060281a0002c06888030060b0001f8060583607000010020000000000060080c0260000a0180000800008ba0182c090020180e038060101a030040003a0000a000000304e010080800000004030160800004844060000101201802000700d016068000c806098120580000004180120101600096060200000a000100103004834070000782e098000c80400804050040000400802018000080c0a002000000000e0280a00830000000600e0200a04802000020100202808008020e80a0d81003830000020600607852010000003e048040000008012048040281e000100103e04808120521005e0080000c3b845c0635500187108b80c6aa0070ed0d7018d5400e2d21ae031aa801c39435c063550038b664b80c6aa00716cc57018d5400e0e39ac8aa4a601e46535896114c03c34a6b22c0298079294d625805300f2929ac
  | 5 => 0xd0144504a980000071c000002d21840022d1904a4a391c3cc8382ba1a060088000003c0000648002ee0008f95d2d6598de16a140044cc8de46a18cab8720005f05f19129a704df8002aa6700900e1c04c4fd0071b40003201c136258b017d240764c590a004170028ed2221d040a2a2204b0e28d90847fcf70b31fa1e4749af33a570e112b1b61b86e8333184bc399210007a85d0bf0007cd080830524507e15f3a2448f890b25a68caf0002ce6988f10840a76cc507f0006c4930af3be2d07894e122620c287a176710002063ba3bc008371f2600000000006a0a78e40065001b0003aa250688001881
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xc00c9d360090302004000000a8c2640d05283518a40248874a705982c793223e09204008470f2e2c00806000000480030401429922117018d540050c644845c0635500181896600735514300486640835536250c014149355171d894300486640835536150c0140c9355172d85430050324d545c86050c01414935517118143004866408355163d08012319020d545874200606591801cd544c8013099020d5450932004866408355163d04012299020d5458b4100606591801cd544c4013119020d5450531004a86508048560084012c1932012158021004a86508748560084012c19321d215802100588652754856008401a21845512158021004a86538348560084014619714d21580210058865053485600840181973600735935000708591215c021d40014149359571d09400050324d655cb41500012199021d5458c400048a6408355162100012319020d54584400050324d755894010001414935d5615004000606d91801cd548c0011199720d549023000407660641cd504c003418965d54350130
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x132000005013444b30039aa8a1802811a1259801cd5450c01208d0126aa2e3b1286009026809355172d8543
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 66
  | 6 => 1665
  | 5 => 2914
  | 4 => 567
  | 3 => 39
  | 2 => 4
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
  | 6 => packedAt gbK6 (68265+((h/555+packedAt gbK6 (61605+(h % 555)*12) 12) % 2658)*12) 12
  | 5 => packedAt gbK5 (152495+((h/971+packedAt gbK5 (139872+(h % 971)*13) 13) % 4653)*13) 13
  | 4 => packedAt gbK4 (35343+((h/189+packedAt gbK4 (33453+(h % 189)*10) 10) % 681)*11) 11
  | 3 => packedAt gbK3 (2808+((h/13+packedAt gbK3 (2730+(h % 13)*6) 6) % 47)*7) 7
  | 2 => packedAt gbK2 (327+((h/1+packedAt gbK2 (324+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe0383fc30c38183fff8fff80ffc1e10f00f3cf
  | 1 => 0x3fc3fc0fc01fc3c1f1c3ff07d68633334d33
  | 2 => 0x3ffc3ff0001ffc01fe03fff827183cc38e3c
  | 3 => 0xffc0003fffffe00001fffc0000381fc0fc0fc0
  | 4 => 0x3ffffffffffe000000003fe000fff000
  | 5 => 0xffffffc00000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x22080440000800045002608042002105001045
  | 1 => 0x49242940e414a428490892a05928612314512
  | 2 => 0x924a82b900294a809241254b0251828c28a28
  | 3 => 0x4180000d2490c00001c9180610800a40540f80
  | 4 => 0x10062232cb271f332c000018213fc000abe000
  | 5 => 0x9e3f33008204062230002060c63ff5bf000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xffeaffe8ffeaeae8ffeaffe8ffeaeae8ffeaffe8ffeaeae8ffeaffe8ffeaeae8ffeaffe8ffeaeae8ffeaffe8ffeaeae8ffeaffe8ffeaeae8ffeaffe8ffeaeae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_14198
namespace PEqualNP.Outside.L_meta_14198
open PEqualNP.Outside.L_meta_14198.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_2_0 : Interval gbAtlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 4 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 39 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_544 : Interval gbAtlas 4 544 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 567 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)))) (concat (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384)) (concat (concat bgb_4_416 bgb_4_448) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)))))
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
theorem bgb_5_2912 : Interval gbAtlas 5 2912 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2914 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864))) (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))) (concat (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))) (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)))))) (concat (concat (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))) (concat (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696)) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792)))) (concat (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))) (concat (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176))))) (concat (concat (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336))) (concat (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432)) (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)))) (concat (concat (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)) (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720))) (concat (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816)) (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912)))))))
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
theorem bgb_6_1664 : Interval gbAtlas 6 1664 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1665 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 4 := by
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
def fullRoots : List Sig := [inputs.getD 3 zero,inputs.getD 7 zero,inputs.getD 6 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffffffeeeeeeffffffffffeaeaeaffeeffeeffeeeeeeffeaffe8ffeaeae8ffffffffffeeeeeeffffffffffeaeaeaffeeffeeffeeeeeeffeaffe8ffeaeae8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_14198.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,6]⟩,⟨.and,[8,7]⟩,⟨.or,[2,3]⟩,⟨.or,[6,7]⟩,⟨.and,[10,11]⟩,⟨.or,[0,1]⟩,⟨.or,[5,7]⟩,⟨.and,[13,14]⟩,⟨.and,[0,4]⟩,⟨.or,[9,12]⟩,⟨.or,[17,15]⟩,⟨.or,[18,16]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_14198

open PEqualNP.Outside.L_meta_14198 in
theorem PEqualNP.Outside.L_meta_14198 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
