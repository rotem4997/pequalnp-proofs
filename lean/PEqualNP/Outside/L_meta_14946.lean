import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_14946.Model
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


end PEqualNP.Outside.L_meta_14946.Model

namespace PEqualNP.Outside.L_meta_14946
open PEqualNP.Outside.L_meta_14946.Model
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

def SBf (j : Nat) : Nat := [7, 8, 7, 6, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_14946

namespace PEqualNP.Outside.L_meta_14946
open PEqualNP.Outside.L_meta_14946.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xe95500400000d14993800c70c820800a9002a46231c6d58842589834468f145014e971290f8000480181e0088b000010020162c70001992ceff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fa20fd20f920fc20ff10fb10fe10fd10fc10f810
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x164014800ec00b968007c3068000040006c880410bce144505c011c00c054ac18249400a12920a400f8f1349800c4b40c0000008c2048000124cc70000000dc0829589cf40000007908013cc83800004d5c003ca914612c01306474e560d858d518e80000150081101cfc2d38b0009000440150d000008400000000010d05415400014c00340602000400160402020e000e020002101418000c0e00080604123c0006079d4310edca421db54843bb28887755110ef4a021de54043bd28485795090abea6a15714d42af298855d5310aeca2215d54442bd28085795010af4a1195e542329faa2653c544ca7ca8194f55032bb2886575510caf4a0195e54032bd286837950d06bca720d754e41bda82837850506f4a198de543319f2a4633d548c6f6a098de14131bd286437950c86f6a090de141219f2a0433d54086bca610d754c21bd280437950086eca3a05d54740bb28e617551cc2f2a5105e94620bba8a417451483d6a4907cd4520bc28a41f051482e0a2907ac8520f490a417a50082f6a5885e54b10bd284213e540427aa8085794c10aea98216e52042daa4086e95010dcaa021da53043b2a6085ed4810f5290217952043d2a4085a54810bd28821f251043e482087c50410f918821f131043e642087c08410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x2e198c00020aa2a0890a58000000000e79c31250098211ab004000021cb084230d43548439c1855090a706154232cc99051483316414520d498c51483516314520d814721483195454c109a596520432a5454810ca551520434a5354810d254d52043606154810b458e41043615290410d854941042b1648c410d854a3104361524c410d854b21042716508410ac59021042d16308410
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x10c000004008001845916314520a42e830aa408541731855204320b1aa52082188591528c410
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | 2 => packedAt s0K2 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (788+((h/14+packedAt s0K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s0K4 (2697+((h/30+packedAt s0K4 (2457+(h % 30)*8) 8) % 133)*8) 8
  | 3 => packedAt s0K3 (998+((h/8+packedAt s0K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s0K2 (249+((h/1+packedAt s0K2 (245+(h % 1)*4) 4) % 13)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xc78f0e3fc38ff8e71e3838e1f8e1f87e633673
  | 2 => 0xf80ff03ffc0ffff81fc03f01ff01ffff84387f
  | 3 => 0xfffc3fff0ff1fe0003ffe3ffe3f8007cf9c
  | 4 => 0xfff00003ffff001fffffc0003fffc001f80fe0
  | 5 => 0xfffffffc0000001fffffffffc0000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x7111a4585a1651070a0a982c582c492c631631
  | 2 => 0x862248a0a128a01814452110a1109651842846
  | 3 => 0x14420090802002120000a440a442104014298
  | 4 => 0x120045321100324a4691800034990218a80d60
  | 5 => 0x24088800224cc494992634990000046156b000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xffffffc0ffc0f0c0ffffffc0ffc0f0c0ffffffc0ffc0f0c0ffffffc0ffc0f0c0ffffffc0ffc0f0c0ffffffc0ffc0f0c0ffffffc0ffc0f0c0ffffffc0ffc0f0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_14946
namespace PEqualNP.Outside.L_meta_14946
open PEqualNP.Outside.L_meta_14946.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x23004d08d0a54d1f143c5841c304064a401803c00009007401200003802200a00000000048000190004000000002700000002e980182c01002007111b0e00080881e040030200001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x681bf42d037a85a05f94740fb28e817651d02faa3a07d54740baa8e81bf41d037a83a05f55240bf29c81de53902bca7205f54e40eea9c815d53902fca5205f54a40bf28c817d51902fca1206fd0240fda04817f53502f8a6a06f90d40de21a817f52502f8a4a06fd0940dea12817f51502f8a2a06fd0540dea0a81fb405037c80a05f95040bf298817d53102fca4205f54840bf288817d51102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a99877d0f30ee21e617e52cc2faa59877ccb30ee996617e51cc3eca3985d94730bea8e61f551cc2eaa39877cc730ee98e617f548c2fca9186f952309f2a4617d548c37aa9184f55230be2a4617d538c2fca5185f54a30bf28c617d518c2fca1187e90230fca0461df308c3f661185fd5130bf2a2617d544c2f8a89877d0d30ee21a617f524c2f8a49877cc930ee992617f514c2f8a29877cc530ee98a61fa404c3f280987ecc130ef182617f540c2fca8185f55030be2a0617e530c2fca4185f54830bf288617d510c2fca01877cc030fd18061dd300c3f260185fd5320bf2a6417d54c82f8a9905fd4f20bf29e417d53c82f8a7905f94720bea8e41ef21c83da43905fd5220bf2a4417d54882f8a9105fd4e20bf29c417d53882f8a7105f54a20bf28c417d51882fca1107e90220fca0441fa30883f261107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a417f51483eea2905dd4520be28a41f451482e8a2907bc8520f690a41fa40483f280907e8c120fc98241fb20483dc40905fd5020bf2a041be540827ca8105f55020deaa0413d54082f8a8105fd4c20bf29841de53082bca6105f54c20eea98415d53082f8a6105f94820bf28841f651082eca2105f54420faa88417551082fca0107bc8020fd10041ed20083f240105fd5310bf2a6217d54c42f8a9885fd4f10bf29e217d53c42f8a7885fd4b10bf296217d52c42f8a5887d88710fa90e21fa40c43f281887e8c310fc98621fb20c43f041885fd5210bf2a4217d54842f8a9085fd4e10bf29c217d53842f8a7085fd4a10bf294217d52842f8a5085f54610fb20c21f541843ec63087d4c610fb90c21f421842fca1087e88210fc90421f710843f621085fd5110bf2a2217d54442f8a8885fd4d10bf29a217d53442f8a6885fd4910bf292217d52442f8a4887d88510fa90a21fa20443f240887ec4110fb082217f54042fca8086f950109f2a0217d540437aa8084f55010be2a0217f53042fca6087794c10af298217d53043baa6085754c10be298217f52042fca4087b94810b7290217d52043daa4085b54810be290217e51043ec82087d50410fb18821f531043ee42087d08410bf28021fa40043f280087e8c010fc98021fb20043f040087dc4010fd08021f510043f220087c44010
  | 1 => 0xf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442fb28885765110afaa2217d54442baa88857e5010bf4a0215e94042bea8085f95010af2a0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465ee428cbda851977cca32f7994657e518cafaa3195f94232bea84657f544cb7ea8994fd5132bf2a2657d544caf8a8996f151329e2a265de434cbba86997b90932f6a1265ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32efa1865dc430cafca41977cc832f719065dd320cbda64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83be43d077887a0df94b41bea9683bf42d077a85a0df94341fd286837a50d06faa1a0fe54341bca86837d54906fca720f794e41af29c837d53907baa720d754e41bf294837d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a83be435077886a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d53106fca420df54841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f7d0f31ee21e637e52cc6faa598f7ccb31ee996637e50cc7f4a198de94331bea8663f950cc6f2a198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31bf294637d528c6fca318fd90631faa0c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263df434c7b88698dfd4931be29263df324c7ba6498fd90531faa0a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52886fca310fd90621faa0c43f631887ea6310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fd90521faa0a43f631487ea6290fdc8521f710a437f50487f6a090ded4121be28243f850486f0a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81be43d037887a05f94b40bea9
  | 2 => 0x4543b8b60002b4170001881c02700019f00028c002473b032c000000bc000002152b052c340800000005e800180478040001a48d4000000000005500011674cb91133e4000001f5000000da2a14f6194c98e90a42f8488000000013100032c8c8d90000002bc00000000000f615d032a6c00000044000000003120001e033000250001850007e44d0000000d0001c70246f4610400c43ed34a1854e000258000000000020900000000000050081010e42444c8000e50007c400000000948bb96e502a3c000001ee8b400000000000ef8fa3ac63c268003ae0000a8000000000000001ea206717e3c400000000000a4c0019c000000b51e30006e80000d18600000000000000002260000d4000002c0000001470e00000016742411c0000007c230730000000011f80026200140000000000000003920000024c000000001a5000000cb80000000000000000001101d500091026017000000591e40000000000036e81d3d0003300007587714c7bc568000003fc000002a20e0ce80050c000001da30e8a0000210009f0000002c690400000258500298410625e83d200394a9945a4a448650a080000000099a611de6000000027e260000fd1207dc001c236ca5c000000000001e800002008000038030020080000000600400002000000030000020000180400000001004000000000030000140000101a01400005004000098040040000000000400000000004014000020000000000000400000001002000000000000000080100001c000010040040080100000000000002004000020020040180100200800004000000010000040100180000000001000004014010000000040080c00400800000008010058000040040100000000c0080100001400805002038000010020000000500000400801000000000050000080100000201c01001008004008000000000000100400c0080000000400802008000010010020080000000002807001006020000020020080100100000000001004000008020080080000100200001000004008000030040000000400a000010030020000080100a00afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443fb28887765110efaa221fd54443baa88877e5010ff4a021de94043bea8087f95010ef2a021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855f5350af8a6a17714d42ae29a85b
  | 3 => 0x162000000878953024140000000035400000000000000ea0007b806253000000e29570000007991c3667d09e800000000000003ca0013b1760000008620317e0009d0003500000023e1a000000000000000001ae00050d44a6d0000000000004c1809a02310e4a14c1180e2000001c00009184b9ed0a2710cc965172370a521435455497000000000000000000000010005c000358001320012f04f000000000b400000000000452000f4000000000001d20000004b0000005b4838c41b69acbe8920000015229f4d80000001c0008048584400000000000000000152311d8a347c05a0000000010d16c9cc000c725a530000003582f0000933b6000001680009f4b980013a204000003f40012b800000000000003a2218001f30009bc000cd0000008710324c0002c8004b4384d4800000000000000000012e217000000000004360000000008482c17800000720cd8000007fc440002a0558000000fa0949ba100004440000041c0685d9eb0000010c9270001250280000020c000002c8000000004463c0ea1860be7780000052a0000000000000000000000000000f400090c002600dea58000003040014ea2c43c0000000013600113a1d4780000005524a0b0e595b2fe764c59a24340000000018a000fd9dd000000718003560001b00000000000240000000788b32023608f80a13c00000000260000af0670000014e0f90009943c1a10008ad170004ac0000000050e464000000000010fa110000008b23600015d2c1f63ceaa4012925324900007b246320b7809278001030002c20c00000003a0006d1120d48581b8002be001278000000003fa3900000000000000000001bf0000006088e0a0001282550009c09caa8000000538160004ac002a0000000399a30000000000049000097800000000000003c0000001dc320000df0000000413fa633982dc0000000000119800000000b5800000000001740360014d0a428a6280029100028424001318938000050720006ea3b4e49e48d80010a0011a000000000a705636a6551b80038200000285376468000000007a80006e0005d4f0800000000000001ec000000002b8000000000000002d93e2100000f0a5000344000d90b08942500033c0007100045e000001cf00007c0000004e8e05a8074d4798002210000000024b2cc3593a800000a500017c0560012125f0da000000000c805000000414000d800023a0003303a1a6000000001601b0d3000000820001713fc2c49520d0000009b12920413842000000000000ed000000f48000003c83180033496c1900000099c3f0001500a51e80000097400000340000002590ba914a10004a800000170000450469a408c00000000000000c900041839c74282000000000000000000007518c7f43a0000226380300407e83c7a8004d0a9545
  | 4 => 0x3620000000049a000002222f20000015934e001518002f635c9c0cf00023ce18a90000013880000000056000508410a40003720002a18d14400000000000000d694900000137045288a30a90004a2000001bc1146105c2040001c918213000000000000000011d043156000002904380001d9cd0001f0000000009d000000000000000002762b800178000534001830000000000032200000000000a0ca300051c224000000000000000000045c002784cc7c00012035e00000000000000000000000000000000000084861000000661060007386a0ca000000000000007e0000005449907e00e2202e800000000a78000fe104740851fc1401d86f000000000a796903002c0000000000c00000000000000003700000000000032400000000000000000009dc3c9212a67189a8002a8001248240000b434a7e1be0000009f22a00000000026000
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x540825e63150209758c540827661150209d584540827a60150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209d98453082756114c209e98053083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083706054420d954720083395488020d654e200837151880209bd95200836551480209ed9520083395448020d654d20082f06148020dc545200825e63d53109758f54c423e64d4f108f59353c423e6414b108f59052c425e6314b109758c52c42f06048710b658e40c42b9648c310f848720c42b96408310b658c20c42f161083109798f548425d63d52108f993538423d64d4e108f990528423d6414a109798c528425d6314a10b558e41842b5648c610ad59021842d56308610bc58021842f06148210f8c85208425e63d51109758f544427561951109e582544423e64d4d108f59353442756194d109e582534427761549109ed81524423e64149108f590524425e63149109758c524427665885109d19521442f060485109e99620442786548110bc18520443e121481109798f540425d63d50109b98b540426d62d50108f59654043366195010ce982540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c755253043566194c10d6982530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d52043646154810da181520423e64148108f590520425e63148109758c520426e62148109d984520427a60148109d59641042d56390410d554e41043655290410bc58241043365450410d554d410436552504109d59631042b5648c410cd5523104365528c410bc5823104335544c410d594d3104365524c4109d597210436552c84109d59421042b56408410b558c21043655208410bc58021042796590010b658e40043595390010da54a40042f16190010ce95140043595350010da54940043b141500109e59630042b9648c010ce5523004369528c010bc5863004339544c010d694d3004369524c010f44c5300427965c8010da54b20043e321c80109e59420042b96408010b658c20043695208010bc584200436552c40109e59610043695284010bc58610042776544010d9549100427b6544010da54910042f36544010dcd9510042f36444010bc59110043b25444010ec55110042f36344010bc58d10043d25344010f454d10042f26244010bc18910043735244010f894910043715244010f854910043615244010
  | 1 => 0x867a6094d219e582534863f6454d218f191534867b6054d219e18153486d563905219d19541486b5648c5219d195314863e64141218f590504865e63141219758c504873a6414121ce590504875a6314121d658c50487724114121dc50450487723114121dc4c4504877321141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219d984540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c218f990530863d6414c219798c53086766114c219e98053086796014c21cd552210875553884219bd9521086776548421cd55121087555348421bc181210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b2154021dc88550087692154021dc485500871d5310f40ab58843d02b56110f40a718d42d025e63947409758e51d03566394740d558e51d03364354740cd10d51d03374254740cd50951d033651507409d98653902756194e40d598653903556194e40d6982539031e53d0240bc98740902ad6210d40ad58443502ba6010d409798c525025d63149409d98452502756114940a718d42502ba60d0540bc987405029e63901408fd95401027b65500409d98754cc27561d53309b98854cc26d62153309d98454cc2756115330c755043cc2cd6210f30b558443cc29c644cb308f99251cc23d6494730cd99251cc3356494730d5d0d51cc3544354730d5cc951cc3553254730d594531cc27661952309d586548c3366195230cd586548c33a6095230ce951408c31e54cc230bc987308c27661951309d586544c25e65d0d30c7550434c2cd6210d30b5584434c2da6010d308f990524c23d64149309d984524c2756114930a7191324c2da60cc530b698e404c2786550130e610d404c2f261cc130a7992304c25e63d50309b988540c26d62150309d984540c27561150309e980540c23e64940308f592500c25f654c0309ed95300c25f63553209718d54c825e63153209758c54c827661153209d58454c823f6454f208f19153c823e6414f208f59053c82766114f209d58453c82e860487209798f548825d63d52209d986548827561952208f993538823d64d4e209d98653882756194e20b658e40882b9648c2209d9865448275619512097d8d544825c63551209dd85544827461551209d98653482756194d208fd91534823c6454d209dd8553482746154d208f990514823d64145209798c514825d6314520cd99051483356414520d598c51483556314520dc580514836451c8520b658e404837051901209e19540483705150120ae5923048370518c1209e1953048370514c120dc147204825e63d50209758f540827661d50209d587540823d65950208f99
  | 2 => 0x4354442cdd095110b354254442d694e5010b595394042dc9465010b715194042d694d5010b595354042dc9455010b715154042ce90d5010b384354042ced095010b3942540429d98454cca7561153329e98054cca796015332c715143cca3e64947328f59251cca3e64943328f59250cca7661152329d584548ca7a60152329e580548cb1f5410e32b3588438cb8c4390a32b318d428cb8f4350a329ed81518ca7860546329dd85508ca7461542328f992544ca5f63551329d984544ca7561151329e980544ca7960151328f994544cb1d6315132cb588544cb366115132cd584544cb3a6015132ce580544ca5e6590d32c7152434ca5c6550d32c7151434cb2c5490932e390e424ca6c6550932e350d424cb1c548c9329d987540ca7561d50329e983540ca7960d50328f596540cb1c63550328f990540ca5e63150329b988540ca7661150329d584540ca7a60150329e580540ca5d65d0c32c7553430ca5d6510c32c7550430cacd6210c32c7553320cb2d548c83297d95320ca9c644c832c7551320ca6f654c832cb551320cb365494432cd552510cb365454432cd551510cb574354432d510d510cb573254432d54c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500cb5b4354032d610d500cb5b3254032d64c9500cb1d5310f41ab58843d06b96010f41a718d42d065e63943419758e50d075a6394341d658e50d073a4354341ce10d50d073b4254341ce50950d067a6094e419e58253907566194e41d698253907596094e41c794f41906f260d0641ab58843506b66110d41ae580435065e63149419758c525067a60149419e580525069c6350941bc983415069e63905418fd95411067765504419e98354cc67960d53319b98854cc66d62153319e98054cc6796015331c755043cc6cd6210f31b658043cc69c644cb318f99250cc63d6494331ce99250cc7396494331d6d0d50cc7584354331d6cc950cc75932543319e982548c6796095231cd986548c73a6095231ce582548c7365450631c7953318c6f260cc6319e982544c679609513197997434c71d5410d31b3588434c6d66110d31b6580434c63e64149318f590524c67a60149319e580524c69c644c931b598e414c6746550531e510d414c6f260cc531a7992314c65e63d50319b988540c66d62150319d984540c67a60150319e580540c63e64944318f592510c65f654c4319dd95310c65f63553219718d54c865e63153219758c54c867a60153219e58054c863f6454f218f19153c863e6414f218f59053c867a6014f219e58053c865e63d52219758f548867a60952219e582548863e64d4e218f593538867a6094e219e58253886d56390621ad592318867a60951219e582544865f63551219718d544867b60551219e181544
  | 3 => 0xc808a000658e61be384a08000009fc738000003f40ea68106030002bf000765279712c6070e69c821c0bd2a0003cc7c08ca6434427c5e1e541e574f11a533a81915a8f20a4bcc90ad24e6802c12c48e9a50fa0b57c56c9e08f05c8743d80021e3b0d60a92248b81d84109e1b8d78fb2be9dce12ac2c07852081946a1a91982d142048030f63ec824770e90000992e1491fe7543827c12e4744a0c000018c0497d23e01c6098f0726eca40f50d8240000004bc16d3aa703bc3742f000574670b60000aa68d1102831696c0a2c72de5a55c0aa06c2f4e4805210450e38890c2488459861720c8691d34383dd1b0b13dca18ba06f59256084ab347a40d25a7e1b6000b5891000000000000000005602c284000000de3a20009fa07098000400000000014800000077c89800000001548000b27b0000000005412f9900602a0001b65461d0cf0003d65d4129292f8000001dd410a501e15e08c9640000048806c0101404000010041400001000000540000004000150002c018090041402c03000030240700000000150101a008020000a01c00004000040102c01000080040300c04034020000c00c02000020000001c190000100c02004000100202000014030080a0000800800000010001b000000100104000000000c0030080f0e4010000200c0200c040040c000000280101800000000240201403004030181a0100201c0802c0000009020020240a008040400100c020240c0381e00001000500240d018040000a05c0105403040000080800c1700000020030180100c0102811020021000301800000080000c000090000200405010080240201401004010000400003014040180600800000020c425028010081100001020000080210c060000301c0a004000103100002014020367661149439d5845250e7a60149439e5805250e7a60d45439e5835150e7661d41439d5875050e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9f6150c43a7d814310f8d4394843c750d5210f8d4354843cbd0d5210f4e4354843cb50d5210f4d4354843c350d5210f954394443d994a5110f655294443e550d5110f665254443d95495110f994394043da94a5010f695294043dc9465010f715194043e650d5010f6a5254043da5495010f725154043dc5455010e5e63947429758e51d0a5e63943429758e50d0aad6210e429ed815190a7860546429dd855090a7461542429d9845350a756114d429e9805350a796014d42d35885350b566114d42d55845350b5a6014d42d65805350a3e65d0d42c714f4350b1c5350d42c714e4250a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842a718d4210b1d53508429bd954210b4d5350842d594e5110b555394442d594d5110b555354442cd90d5110b34
  | 4 => 0x2120000000014f0007a4089f12047a15e2010002700007c44673c000004c29a8078480000d4001c52a28bd0600055c000570002084c50280218870c0026b00017c96800000000001ae0fc06d12acb37c5ed0703f5260000988536e3c09a0002300001e8002aa144631fa0000007104e33e0380017a0001e83397e0465cc001a75946c4ae06b000028ebab50ca190ad28d28e364c20720000009711a1fc06800000486000649372cc0013d00000000000000000934000ed4a076c529791c8001528004a49285c12418ea6c00000000020001330006e95323859c298a58884341d93712842a66cb51440c00010012a2728a0a29321b09d0cca0a1762110ca530427184d0f222c6040000056026d621110002589e8000000005b1101c06a8238e51ac0011500050ea056885d00000169879000528689f917e000000004cc3cc002324ba0000000053e0000010b58c0dcd40d01027800019a1985e025024242058c9a3c52e3f0aa029398000ab2510000000c24c00010815198000000001c14220000029152a338000001c6954a603a55412c0f1642e40006a2c84c0a2c2b00022a9d8c10153da0000000b3b4ac8022034ae000ea2b70000014c9c45086c80009d2564d8daa853b07c8758003e6000fc28311a00000075000a9cf50f453430c18800236519369ad1b48b1680002c26d01f0000001891028e5402acdc8003001f4d49cb0800e02d04455678d66a9d57a418c41e43940003480000079c001940b88e4e9245524000930531465005b8be104a715c80018a0011d2420004280025859e0013d80055a000698000000000000000061d400003ee0012493a000000000000200345d000286309201ab000000000004d8000669fd000858002821f0404de82047ea280029800024c580000ae000f79764e43a04c01f26a878c89d022e3540018d086478462b45760005380032a6e0000a23fe5dd542a44ca9390c2890cc6fd0228c1d486c13a4627c5653c00000060c7d10009a4950b96e00005c00279000000002480000003b91c000534838000a0000291960001fc0002211c264fa00039c6840020234889c450002ca84cff20d0008504f0005824e038989000280002b60006284315347c7d4982cc4ce65d612d21643e4aba2455e4353ea210027ed14967360968d32632468dcb6a3052c0d077a2d4c4480652261249bcc28682a48c40000029c6cc00000586430520000000000017f000a88001fc000000002c50008ece00003b80cc57800000959080870e62cc679703784ec788dc318b514f1d62c4a20368782d0b00000b45420000182b0a835d588950009cc5a8000001240000031c9c51a00000000
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xc28198a25ac00000000230ea430002086851e08941c80162730802200002f898c8d0000041f9b958018a53115128480170011af29060005818e00090f100b1a2e1f2626969ab2a290800114ad98238000001b001d8000318000002b8080000002aeaa8ba980002a2b000000288012210000002783a19c1380030000000000000013111ea00017821d0000000832000019000dac8fad00000007078a8000002480470100c00080c08002018000000000c0c0c0410040c0c100000300c0808041004164ab88c4a1887265c06250c43932e1b0a8621c9571d814310e863b286a908743dc54354843a1ee0a1aa421f054354a5110f82a1aa4a8887c250d5294043e1286a92a021f11435455010f22b12c229a85925896014d42ca2c2b00a6a15257210d5110a8a39a84a88854a5c84354042a30e6a12a02160f54588438ca473b686a14658358d6215132c4ac4b08a89962962580544cb18b0ac02a265439d64390932c18caa1a849960d54588430ca0e3b2a899065515c84354432a28e8992a2195497210d500ca8c3a264a80658354d6210f41a52e421aa1a0d187350950d0706aa2c421e63525c84354331a30e8992a198e0d54588434c6c2b9086a0a63645c04350531c32c8b18a090d51739045048698ba462282438c5506048421ca2a63024210e0d5358843d0292b9086a8e81451cd4254740c1aa8b1087985457210d51cc28a3a264a8e61835516210d30b12e421a80985917110d404c30ab22c628a419458c5190120c62c828c6090631541852008328a98c290041495d06154810a8ae630aa4085297418152042a4b98c0a90219158d5290410cc2a4b0482086256454a3104330a92c118821895915208410c8ac6a904208661525802104324b1aa520021985496190010e22a6a0a8008721525054004314b22a51802198549618c010e22a898a6008741524c530042b0bae43900219859721c8010c52c8a904008649635482004330a92c210021345cf6444010962e9b1a20087115454d1004258ba0c488021345cc6244010ac2eb29220084707654910043912a2a488021c85515244010e84a6a922008741535491004331bb2a488021981d95244010cc6c8a922008661645491004331b1aa4880219858d5244010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xe064200c8a0000905811d94354843909801d9435484390980dc5435484390581dc14354843a21841d95244010a41831d95244010a4183d915244010a2184d8d5244010
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 682
  | 4 => 725
  | 3 => 102
  | 2 => 8
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (i*5) 5
  | 6 => packedAt s1K6 (i*16) 16
  | 5 => packedAt s1K5 (i*27) 27
  | 4 => packedAt s1K4 (i*38) 38
  | 3 => packedAt s1K3 (i*49) 49
  | 2 => packedAt s1K2 (i*60) 60
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (6+((h/1+packedAt s1K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s1K6 (731+((h/13+packedAt s1K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s1K5 (20911+((h/227+packedAt s1K5 (18414+(h % 227)*11) 11) % 1316)*11) 11
  | 4 => packedAt s1K4 (29960+((h/241+packedAt s1K4 (27550+(h % 241)*10) 10) % 958)*11) 11
  | 3 => packedAt s1K3 (5270+((h/34+packedAt s1K3 (4998+(h % 34)*8) 8) % 162)*8) 8
  | 2 => packedAt s1K2 (488+((h/2+packedAt s1K2 (480+(h % 2)*4) 4) % 14)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x78e3c71fc71fe3f31e3831c7c71f8ff3134cf
  | 2 => 0x7f03f81ff81ffc7c1fc03e07f81ff1fc238f3
  | 3 => 0xf8003ffe3ffe3ff8fe0003ff8ffe3fe003cf3c
  | 4 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x50e046228542944030a0a905141448ca311445
  | 2 => 0xa10c89450a252808c144522228889614c22892
  | 3 => 0x11000100000010200004801202000004128
  | 4 => 0x32240129a1200c92546918000e4d0246540ec0
  | 5 => 0xc44822400249b124a992639340000498abb000
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xffffffa0ffa0faa0ffffffa0ffa0faa0ffffffa0ffa0faa0ffffffa0ffa0faa0ffffffa0ffa0faa0ffffffa0ffa0faa0ffffffa0ffa0faa0ffffffa0ffa0faa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_14946
namespace PEqualNP.Outside.L_meta_14946
open PEqualNP.Outside.L_meta_14946.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xb800000013523c1003400000060111f2801080006009e129d5003a38200104122300640062234a92006d426009461c5601016140028b0e0820010c00011000491c0ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21f621fd21f521fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10f610fd10fc10f410
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x5737520447021a0f3546124e4b00422040213e411b253930321023580700243a49222f134d533b05310111380b2c5a173f430036191f2a54000018144c1e00002e00440050082d4833454a4f260d000934003c15162b290000000056002700510a0628031d0e00550c3d59001c000e182025e201820818085002cb0a060822f08002130a000003d9d4310edca421db54843bb28887755110ef4a021de54043bb28c85755190abea6a15714d42af298855d5310aeca2215d54442bd28085795010aeca3195d546329faa2653c544ca7ca8194f55032bb2886575510caf4a0195e54032bd286837950d06f4a198de54331baa94437650886f6a090de14121f3a9243f350486e8a090fc14121b8282437651086eca3a05d54740af29c815d53902eea2a05d14540bb28e617551cc27ca9184f55230bba8a6174514c2eca3905d54720f290e417751482e8a29079485209f2a0413d54082bca6105754c20bb288417551082eea5085d54a10bb284213e540427aa8085794c10aea98216e52042daa4086d95010daaa021d653043aaa6085dd4810f3290217552043caa4085954810bb28021f250043e480087c50010f918021f130043e640087c08010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x980020a8000e70ab0091e4a21305020180001ae4160280086803000020410060cb0f0d43548439c1815190a706054632cc99050487316414121d498c50487516314121b818121c83155454c109959652043265454810c955152043465354810d154d52043606054810b458e40043615290010d854940042b1648c010d854a3004361524c010d854b20042716508010ac59020042d16308010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x68004201845916314121a42e8302a408541731815204320b1aa52002188591528c010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | 2 => packedAt s2K2 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (788+((h/14+packedAt s2K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s2K4 (2667+((h/30+packedAt s2K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s2K3 (998+((h/8+packedAt s2K3 (950+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s2K2 (248+((h/1+packedAt s2K2 (245+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc38f1e3fc78fffe31e3838e1f8e1fffe61327f
  | 1 => 0xfc0fe03ff80ff8fc1fc03f01ff01f87f863c73
  | 3 => 0xfffc3fff0ff1fe0003ffe3ffe3f8007cf9c
  | 4 => 0xfff00003ffff001fffffc0003fffc001f80fe0
  | 5 => 0xfffffffc0000001fffffffffc0000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x70118850541450030a0a902850284e28611225
  | 1 => 0x8b2254a8a32aa11c14452914a9149155862c52
  | 3 => 0x84404090102002420000a440a442104024498
  | 4 => 0x11004932120032494691800034990218a80b60
  | 5 => 0x22089000244cc492992634990000046155b000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffff88ff88aa88ffffff88ff88aa88ffffff88ff88aa88ffffff88ff88aa88ffffff88ff88aa88ffffff88ff88aa88ffffff88ff88aa88ffffff88ff88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_14946
namespace PEqualNP.Outside.L_meta_14946
open PEqualNP.Outside.L_meta_14946.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x200084600df43be43bc43dc439c43
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xc180854100d1e5390f1ca421e354843cb28887955110f34a021e654043
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x283055254443c25495010f115154043
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 5
  | 3 => 7
  | 2 => 3
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | 2 => packedAt s3K2 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (84+((h/1+packedAt s3K4 (80+(h % 1)*4) 4) % 9)*4) 4
  | 3 => packedAt s3K3 (197+((h/2+packedAt s3K3 (189+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt s3K2 (117+((h/1+packedAt s3K2 (114+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf8f0fff0fffe3f0f1e380e3fe3fe0ffc30f3cf
  | 1 => 0xff0fff0fffc7f01fc00fc7fc7ff07cc33cf3
  | 2 => 0xfff0fff0fff8ffe0000ff8ff8fff8303cf3c
  | 4 => 0xff0000ffff0000fffffff000fff00003fc0fc0
  | 5 => 0xffffff00000000ffffffffff00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1182212442440050a09220920920528305145
  | 1 => 0x5222842428480850144244424424a050c12492
  | 2 => 0xa4444848829001aa2004889089094a03028a28
  | 4 => 0x30066682221c92334690e000f2406319540fc0
  | 5 => 0xc088880ccce124cc99270f2400018c62abf000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xffffe8e8e8e8e8e8ffffe8e8e8e8e8e8ffffe8e8e8e8e8e8ffffe8e8e8e8e8e8ffffe8e8e8e8e8e8ffffe8e8e8e8e8e8ffffe8e8e8e8e8e8ffffe8e8e8e8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_14946
namespace PEqualNP.Outside.L_meta_14946
open PEqualNP.Outside.L_meta_14946.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x155a70000060000956bcf860e002a33ca08a40060b93000000000580005c012841e9c40240340002400000000110b00000805274000006d500426802c0000000000070a2064a2600000001800003000000401001c0010600000ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xb00124967c1795c2a77000a42c1c30a08144e000005633001aca8553c800306c0418854251f8986a80240e008072e8d05c6a390240050000009a0007000007e3480060860d1c4006e1196c9e450ca04da67429448c0c030503e3e07848427800000e80021801067b000c8940032000bc0000040841d1d88840661d1944800019a0000020210de0006800581b1b00000133e8b404173811c727f0f1486e53438f0824c00000c00000044000000000ac4400164503d02800005a1889c00583d000c65f3a9cc00762e0040001270000000700070a00060d1901060b000200030104000a09000002000100000217071300080c040201002110bb28c87755190e7ca721cf54a43db28c87b55190e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb948439ea9087ad5210e5aa421ed94443daa8887ba5010e7aa021ee540439ca80873e53d0a7aa1a14f552429e29a85af5250a7ea0a14f950429faa6653c54ccaeca3995d547329f2a4653d548cb5a85194fd51329e2a265ad424ca7ca8194f55032bb2886575510caf4a0195e54032af29c835d53907388798cf952319eaa463b6548c76aa918dd54e31db21c63b4438c76e8518ed50a319faa2633c544c7388698edd5131da2a263d7534c7ae8698ed90d31da21a63d4434c7288698edd0931daa1263d7324c7aa6498dd944319f2a6433d54c867ca810cf55021af298435d53086f4a010de540219f29e813d52d036c63a06d4c7409eaa4813c535027ea4a06d8c540da98a81bb505027ca8204fd53309e2a6617651cc2eaa398754c7309f2a4613d548c37281184fd51309e2a261d5314c37280984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9904f952209eaa4413e544827aa8905dd4520ba28a413e540827aa8105794c20aea98417651082eaa2107a480209f2a4213d548427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x420962202bc8801eb8013380150952000002c0021e3a000001c345a446aca804c94f80502819810b581a32018a028000074e1490000403002e30000000000036000868102340020000100162c181a55865310f255294443c95495110f295294043ca9495010f295254043cc9455010f3151540438e5805350a3960153328b195424ca8d6210f31a658043cc6a56210e31ac580438c68d6210d31a6580434c69664d4d318d996434c6966390d318d994434c6a56210d31ac580434c6c56210d31b4580434c6966510d31c5994434c7866210d31a5588434c7856210d31a1588434c7926010d31a5580434c7916010d31a4580434c6946350931a5193324c694644c931e1509324c62d6214d40c514d315022d6215330c515131cc314544c5308e195404c39131501308718d54482556314520d254d20083615148020
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x900280033000000000204e0041a058a6010d31d04c4b008698e8162580434c648b80c6a1263245c064cc931908eca126498d057214d3150282b90a898e61841953150130
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | 2 => packedAt s4K2 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (880+((h/16+packedAt s4K5 (768+(h % 16)*7) 7) % 90)*7) 7
  | 4 => packedAt s4K4 (4032+((h/45+packedAt s4K4 (3672+(h % 45)*8) 8) % 180)*9) 9
  | 3 => packedAt s4K3 (2012+((h/16+packedAt s4K3 (1900+(h % 16)*7) 7) % 73)*7) 7
  | 2 => packedAt s4K2 (456+((h/3+packedAt s4K2 (441+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf1e3c7fc78ffe3f18e3838fe38ff87f10f1cf
  | 1 => 0xfe03f9ff80e3fc7e0fc03f1fc0e3f8f633933
  | 2 => 0xf0003fe3fff03ff8ff0003fe3ff03ff083ce3c
  | 3 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x41404600421408400840908240830824105045
  | 1 => 0xa20c89489128540860a42910a424930a612912
  | 2 => 0x9110112400a0019100422409402440828228
  | 3 => 0x2404010a010004922229080032288102240d80
  | 5 => 0xc8d82250364d3924dcd273c90041066cdbf000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xffe8ffe8fae8fae8ffe8ffe8fae8fae8ffe8ffe8fae8fae8ffe8ffe8fae8fae8ffe8ffe8fae8fae8ffe8ffe8fae8fae8ffe8ffe8fae8fae8ffe8ffe8fae8fae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_14946
namespace PEqualNP.Outside.L_meta_14946
open PEqualNP.Outside.L_meta_14946.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x2a342540d00991803a50006007d029560488230b4f1c1c6510c009109b2c3d780009c580141d60800157002694a92065c2100014310400b5840010c014c006ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xcc000000000000000000000000000002e340000070001c40008248000000001140060288940000000001200000007e10000acde2300000d2002d99c000000130ec2c0207cf000000e08e463180000001f000000000000be270005c000000000ea2200000000000000263d00000000a24214b8644200000000011000032d00000000000000002780000362c0980001000a4ae503f0e40000001f4aa0000000f81a000007834000800000308004200001b8005200100b2000b10800000680000002e800000026800000000000c400070007653000000000001980000000000000000000000000300000411ecd80f1780004000e000d400000006e000000000000021800000000094142f000322a0009074000a80000830010c0e743f9cc0a00002000000000c8166d391383c871400000000012c60003d0b4007700000001100000ca8118848001b030600000000000000000000000358006a002b15000413c874000080000010100400000100802020000002000081c04000080000010000c0a04000000001020000202010040800000040002bb28c87755190e7ca721cf54a43db28c87b55190e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb948439ea9087ad5210e5aa421ed94443daa8887ba5010e7aa021ee540439ca80873e53d0a7aa1a14f552429e29a85af5250a7ea0a14f950429faa6653c54ccaeca3995d547329f2a4653d548cb5a85194fd51329e2a265ad424ca7ca8194f55032bb2886575510caf4a0195e54032af29c835d53907388798cf952319eaa463b6548c76aa918dd54e31db21c63b4438c76e8518ed50a319faa2633c544c7388698edd5131da2a263d7534c7ae8698ed90d31da21a63d4434c7288698edd0931daa1263d7324c7aa6498dd944319f2a6433d54c867ca810cf55021af298435d53086f4a010de540219f29e813d52d036c63a06d4c7409eaa4813c535027ea4a06d8c540da98a81bb505027ca8204fd53309e2a6617651cc2eaa398754c7309f2a4613d548c37281184fd51309e2a261d5314c37280984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9904f952209eaa4413e544827aa8905dd4520ba28a413e540827aa8105794c20aea98417651082eaa2107a480209f2a4213d548427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x90100c00000064000000132912011005e71180165c39328200045800b0e5c68e9e56b488214002803e0122a1e4100636618834a5540000846a7180650102001000a16245800204000a55865310f255294443c95495110f295294043ca9495010f295254043cc9455010f3151540438e5805350a3960153328b195424ca8d6210f31a658043cc6a56210e31ac580438c68d6210d31a6580434c69664d4d318d996434c6966390d318d994434c6a56210d31ac580434c6c56210d31b4580434c6966510d31c5994434c7866210d31a5588434c7856210d31a1588434c7926010d31a5580434c7916010d31a4580434c6946350931a5193324c694644c931e1509324c62d6214d40c514d315022d6215330c515131cc314544c5308e195404c39131501308718d54482556314520d254d20083615148020
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xa04030083394009a058a6010d31d04c4b008698e8162580434c648b80c6a1263245c064cc931908eca126498d057214d3150282b90a898e61841953150130
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => packedAt s5K5 (864+((h/16+packedAt s5K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s5K4 (4077+((h/45+packedAt s5K4 (3672+(h % 45)*9) 9) % 315)*9) 9
  | 3 => packedAt s5K3 (2012+((h/16+packedAt s5K3 (1900+(h % 16)*7) 7) % 67)*7) 7
  | 2 => packedAt s5K2 (453+((h/3+packedAt s5K2 (441+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf1e3c7fc78ffe3f18e3838fe38ff87f10f1cf
  | 1 => 0xfe03f9ff80e3fc7e0fc03f1fc0e3f8f633933
  | 2 => 0xf0003fe3fff03ff8ff0003fe3ff03ff083ce3c
  | 3 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 4 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x41404600421408400840908240830824105045
  | 1 => 0xa20c89489128540860a42910a424930a612912
  | 2 => 0x9110112400a0019100422409402440828228
  | 3 => 0x2404010a010004922229080032288102240d80
  | 4 => 0xc8d82250364d3924dcd273c90041066cdbf000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xffe8fae8ffe8fae8ffe8fae8ffe8fae8ffe8fae8ffe8fae8ffe8fae8ffe8fae8ffe8fae8ffe8fae8ffe8fae8ffe8fae8ffe8fae8ffe8fae8ffe8fae8ffe8fae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_14946
namespace PEqualNP.Outside.L_meta_14946
open PEqualNP.Outside.L_meta_14946.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x100540029c78317910069c0000d40200001100128d88a1e0570036e9ca80e18cb06e21a363a015a14c905bb06f40322a0022d289c916664002c4a60f0d2638b9f524208685000c00052004800e08800264c18002ffd5009fe54007f55009fc5402ffd4c01fe53007f54c0bfc53027fd0c01fe43007f50c09fc4302ffd4807fe52007f54807fc52027fd0807fe42007f50807fc42007fcc807fe32007f4c807fc32017fd4405fe51017f54405fc51017fd0405fe41017f50405fc41017fcc405fe31017d8c405fd31007d4c405fc31017fc8405fe21017f48405fc2102ffd4003fe50007f54003fc50027fd0003fe40007f50003fc40007fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10017f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x866001ff4433000ff82198003ff654c0017fb2a600dff9953002dfcca98003fd654c0017eb2a600dff1953002df8ca98003ff644c0017fb22600cff99130025fcc898003fd644c0017eb22600cff19130025f8c898037ff544c019ff2a26000ff55130067f8a898006ff634c01bffa9a6009ff94d30007faa698027fc534c019ffa1a6009ff90d30007fa8698027fc434c001ffb126000bfd893005ffcc49800efe624c001feb12600bff1893001df8c498037ff524c017ff2926000ff5493005ff8a498033ff424c017ff2126000ff5093005ff88498027ff324c001ef992600bff8c930007fa6498003dd324c013fe192600affd8530055fec29802bfe614c0057f30a600aff58530055fac29802bfc614c0057e30a600affd4530057fca29802bfd514c015fe28a600affd0530057fc829802bfd414c015fe20a6009ffcc530057be629802bfe314c015fb18a600aff4c530057ba6298003f5314c001ea98a6009ff0c530057fe429802bfe214c015fe90a600aff0853000dfec098007ff504c003ff2826001fe9413000ffaa098003f9504c003fe2826001ffd013000ffc8098007fa404c003fea026000fe5013000ff88098007ff304c013fd9826001ff8c13000fbc6098007fc304c003ee1826001fe0c13000ffe4098007fe204c003fd1026001ff0813000ffe2098007fe104c003fe8826001ff04130007feca90002ff6548011ff32a4005bf99520007faca90002fd6548011fe32a4005bf19520007fec890002ff644800fff3224004bf99120007fac890002fd644800ffe3224004bf19120047fea89001ffe5448001feaa24007ff15120007fec690002ff6348001ff31a4009bf98d20007fac690002fd6348001fe31a4009bf18d20047fea690003fe5348001fea9a4008ff14d2003ffe8690003fe4348001fea1a4007ff10d2000dfec49000fff5248007ff2924003ff5492001ff8a49000fff4248007ff2124003ff5092001ff8849000fff3248007ff1924003fb8c92001ffa6490003ed3248007fe1924006ffd8520035fec290003f761480017bb0a4006ff98520015fcc29001bfd614800d7eb0a4006ff18520015f8c29001bf461480057a30a4006ffd4520037fca29001bfd514800dfe28a4006ffd0520037fc829001bfd414800dfe20a4006ffcc520037fc629001bf6314800dfe98a4000fd4c520037f8629000fff2148007f790a4003ff8852001ffa429001bed2148007fe10a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fd1824001ff4c120007f26090007fc3048003ff9024003fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007e82048003ff8824001ff8412000ff42090007fd104800dfc8824001ff04120
  | 1 => 0x77c5054003fc282a001ffd015000ffc80a8007fa4054003fe202a001ff8c15000ff460a8007fc3054003ff902a001ff8815000ff840a8007ff1054003ff082a001ff4415000ff820a8003ff65500017fb2a8014ff9954002dfccaa0003fd65500017eb2a8014ff1954002df8caa0006ff6450009ffaa28014efd5140027fca8a0013fd5450009fe2a28004ef15140007fec6a0002ff6350001ff31a8000ff58d40007f8c6a0026fc6350029ffa9a8000ff94d40007faa6a0053fc5350009ffa1a8004efd0d40027fc86a0013fd4350001dea1a8004ff10d40007fec4a0002ff6250027ff3128003bf98940007fac4a004ffc62500077e3128014ffd494009ffca4a0003fd5250027fe2928004ffd09400277e84a0013fe4250009fea128000ef50940027f884a0003ff3250027ff1928000ff4c94009ff864a004bff61500257fb0a8012ff98540015fcc2a004bfd61500257eb0a8012ff18540015f8c2a004bff5150025ff28a8012ff54540097f8a2a0013ff4150009dfa0a8004ff90540027fa82a004bbd4150009fe20a8012ffcc540097fc62a004bf63150025fe98a8000fd4c540097f862a004bff2150025ff10a8012ff48540097f842a0006ff6050003ffa828001ff9414000ff4a0a0007fd5050001fca828001ff1414000ffe80a0013fb4050003ff2028001ef9014000ff880a0007bc4050003fc2028001ff8c14000ff460a0007fc3050003ff9028001ff8814000ff840a0007ff1050003ff0828001ff4414000ff820a0027ff65cc0137fb2e6009ff9973002dfccb98027fd65cc0017eb2e6009ff1973004df8cb98027ff64cc0137fb266009ff99330025fcc998027fd64cc0017eb266009ff1933004df8c998047ff54cc021ff2a66000ff55330087f8a998006fe63cc013ffa9e6009ff94f3004ffaa798027fc53cc013ffa1e6009ff90f3004ffa8798027fc43cc013ffb166009ff98b3001dfcc598027fd62cc0017eb166009ff18b3001df8c598047ff52cc01fff2966000ff54b3007ff8a598043ff42cc01fff2166000ff50b3007ff88598027ff32cc013ef9966009ff8cb3004ffa6598003dd32cc013fe1966009ffd873004dfec398027fe61cc0057f30e6009fd98730015ecc398027fd61cc01d7eb0e6009fd58730005eac398027fc61cc0057e30e600effd4730077fca39803bfd51cc01dfe28e600effd0730077fc839803bfd41cc01dfe20e6009ffcc73004fbe6398027fe31cc013fb18e6009ff4c730077ba6398027f531cc001ea98e6009ff0c730077fe439803bfe21cc01dfe90e600eff0873000dfac198007ff50cc003ff2866001ff5433000ff8a198007ff40cc003ff2066001ff5033000ff88198007fe30cc003ef1866001fe8c33000ff86198007dc30cc003ff9066001ff8833000ff84198007ff10cc003ff0
  | 2 => 0x320f7f8a89900eff634c83fffa9a6409ff94d32007faa699027fc534c83dffa1a6409ff90d32007fa8699027fc434c8077fb126403ffd493201ffca49900fee524c807fea926400fb5493201ff8a49900fff424c807ff2126403fb9093201ffa8499003ed424c807fe2126403ffcc93204fde649900ffe324c807ef1926403ff0c93201fb8649900fec324c83bffb0a641dbfd85320effcc29900afe614c83bfeb0a641dbf585320eff8c29900afc614c83bffa8a641dff945320effaa299077fc514c83bffa0a641dff905320effa8299077fc414c813ff98a641df7cc5320effc6299077f6314c83bfe98a641df74c53204ff8629900fff214c807ff10a6403ff4853201ff84299003ff604c8017fb02641cff9813200dfcc099003fd604c839fe3026401bf181320fffea099073fe504c839fe282641effd01320e7fc8099073fc404c839ff1826409ff0c13201ffe409900fef204c807ff1026403ff081320effe2099073fe104c83bfe882641cff04132007eeca9886ff6654c401fab2a621bfd19531007eec89886bf6644c401fab22621afd191310dfeea89886bf6544c401faaa2621afd15131017eec69880af7634c405ebb1a621bfdd4d3104feca698803f5534c413fa29a621afdd0d3104fec8698803f5434c413fa21a6200fdd89310cfecc498803f5624c433fa312621bfdd49310cfeca498803f5524c433fa292621afdd09310cfec8498803f5424c433fa2126209fdcc931007ae6498867f6324c401fa9926200f54c93104fe86498803f7604c431fb3026200fd581310c7e8c09886ff7504c431fb2826218fd141310d7ee8098863f6404c431fa2026218fd8c13104fe86098867f7204c431fb1026218fd0813100dfecaa8003ff64540017fb22a017ff99150025fcc8a8003fd645402ffe322a004bf1915002ffea8a8017fe545402fbf2a2a005ff5515002ff8a8a80177c5454001ffb1aa000bfd8d50007fcc6a8003fd6354001fe31aa009bf18d5002ffea6a80177f535400bff29aa005ff54d50006faa6a8017fc535402fffa1aa000ff90d50007fa86a805ffc4354001ffb12a000bfd89500b7fcc4a800efe6254001feb12a016ff1895001df8c4a8017ff525400bbfa92a005ff9495002ffaa4a80037d525400bfe292a017ffd09500b7fc84a8003fd425402dfe212a000ffcc9500b7fc64a8003fd325402dfe192a015ffd85500adfec2a8057fe61540057f30aa015ff585500adfac2a8057fc61540057e30aa005ffd455002efea2a8017fe515400bfea8aa015df5455002ff8a2a8057ff415402bff20aa015ff505500aff882a8057ff315402bff18aa015fd8c5500affa62a8003f5315402bfe18aa015ffc85500affc42a8057fd215402bfe10aa001bfd815000ffea0a8017fb5054003ff282a001df9415000ff8a0a800
  | 3 => 0xf182a427ff0c15201ffe40a900ffe2054807fe102a428ffc415213ffc20a90a3fd105484ffe082a400ffd9542005fecaa109bfe655080b7f32a8400ff59542005facaa109bfc655080b7e32a8403bfd9142027fea8a109bbf5450809ff2a28404ff55142027f8a8a1013bc5450801ffb1a8400bfd8d42007fcc6a1003fd6350801fe31a8409bf18d42137fea6a1003fe5350801fea9a8426ff14d42027fe86a1013bf4350809ff21a8404ff50d420077a86a1013fc43508077fb128403ffd494201ffca4a100fee5250807fea928400fb5494201ff8a4a100fff4250809f7a128403ff9094201f7c84a100ffc4250807de2128403fb1094201ffc64a100fee3250807fe1928425ffd854212dfec2a1097fe61508057f30a8425ff5854212dfac2a1097fc61508057e30a8425ffd454212ffca2a1097fd515084bfe28a8404ffd05420277e82a1013fe4150809fea0a8425ef50542027f882a1097ff315084bff18a8425fd8c54212ffa62a1097fc3150807ff90a8403ff8854201ffa42a100ffc2150801ffb028400bfd8142127fcc0a1006fe6050801feb028424ff1814200df8c0a109bff5050849ff2828424ff14142027fe80a1013bf4050809ff2028404ff10142127fc60a1093fc3050807ff9028403ff8814201ff840a1097ff1050849ff0828425ff44142127f820a1027ff65cc8137fb2e6409ff9973202dfccb99027fd65cc8017eb2e6409ff1973204df8cb99027ff64cc8137fb266409ff99332025fcc999027fd64cc8017eb266409ff1933204df8c99908fff54cc845ff2a66400ff55332117f8a99900efe63cc813ffa9e6409ff94f3204ffaa799027fc53cc813ffa1e6409ff90f3204ffa8799027fc43cc8077eb166403ffd4b3201ffca59900ffd52cc807fe2966403ffd0b3201ffc859900ffd42cc807fe2166403ff8cb3201fbc659900fee32cc807fe1966403f70cb3204ffec399026ff61cc813ff30e6402bf9873204fecc39900af661cc813feb0e6421bf5873204feac399002f561cc813fe30e6402bf1873210ffea399087fe51cc843fea8e6421ff1473210ffe8399087fe41cc843fea0e6421ff1073204ffe6399027df31cc813ff18e6409fd8c73204ffa6399087dd31cc813fe18e6403ffc873201ffc439900ffd21cc807fe10e6409ffd833204ffcc199006fe60cc813feb066400bf5833204ff8c199006fc60cc847ffa866420ff94332107f8a19908bff40cc841ff2066420ff1033204ffc6199027fc30cc807ff9066403ff8833201ff84199087ff10cc841ff0866421ff44332107f82199003ff654c8017fb2a641fff9953202dfcca99003fd654c8017eb2a641fff1953202df8ca99003ff644c8017fb22641eff99132025fcc899003fd644c8017eb22641eff19132025f8c89907fff544c83dff2a26400ff551
  | 4 => 0x8bffe5190c5ffea8c862fff14643027fe8321813fe4190c09fea0c8604ff1064304ffe6321827fe3190c13fb18c8609ff4c64304ff863218bfff2190c5fff10c862fff4864317ff84321827ff6090c13ff3048601bf9824304ffac121802fd6090c13fe3048601bf1824318ffea1218bbfe5090c5dfe2848604ffd0243027fc8121813fc4090c13ff1848609ff0c243187fe41218bbfe2090c5dfe104862fffc4243177fc21218bffd1090c5dfe0848600ffd9543005fecaa18037f6550c013fb2a862dff9954302dfccaa1803fd6550c017eb2a862dff1954302df8caa18037c6550c0b3e32a8609bfd9143027fea8a1813fe5450c09df2a28604ff551430077aa8a1813fc5450c097fb1a862dffd4d4304ffca6a1803de5350c01fea9a8600f754d4304ff8a6a1813ff4350c09efa1a8609ff90d4304f7c86a1827fc4350c13de21a8604f710d43007fec4a1802ff6250c59ff3128603bf98943007fac4a18b3fc6250c077e312862dffd4943167fca4a18b3fc5250c09ffa128604efd0943027fc84a1813fc4250c59ff1928609ff0c94315ffec2a18aeff6150c57ff30a8602bf9854315ffac2a18aefd6150c57fe30a8602bf1854315ffea2a18affe5150c57fea8a862bff14543027fe82a1813fe4150c09fea0a8604ff1054304ffe62a18affe3150c57fb18a862bff4c54304ff862a18afff2150c57ff10a862bff4854315ff842a1803ff6050c017fb02862aff9814300dfcc0a1803fd6050c55fe3028601bf1814316ffea0a18abfe5050c55fe2828604ffd01430277e80a1813fe4050c09fe202862aff8c14304ff860a18b3ff2050c55ff102862aff0814315ffe20a18abfe1050c57fe882862aff0414301dfecaa9003ff64548017fb22a429ff99152025fcc8a9003fd6454853fe322a404bf1915202ffea8a9017fe5454853bf2a2a405ff5515202ff8a8a90177c5454801ffb1aa400bfd8d52007fcc6a9003fd6354801fe31aa409bf18d5202ffea6a90177f535480bff29aa405ff54d52006faa6a9017fc5354853ffa1aa400ff90d52007fa86a90a7fc43548077fb12a403ffd495202fdea4a900ffe5254807bf292a403ff1495201ef8a4a900fec5254807ffa12a403ff9095201fdc84a900ffc4254807ff192a403fb8c95201ff864a90a3ff61548517fb0aa428ff98552015fcc2a90a3fd61548517eb0aa428ff18552015f8c2a9017ff515480bbfa8aa405ff9455202ffaa2a90a37d515480bfe28aa428ffd0552147fc82a90a3fd4154851fe20aa428ffcc552147fc62a90a3f63154851fe98aa428ff0c55201ffe42a900ffe2154807fe90aa403ff08552007fec0a9002ff605484fff302a401bf98152007fac0a909ffc60548037e302a405ffd415202efea0a9017fe505480bfe282a429ffd015213ffc80a909ffc405484ff
  | 5 => 0x525304dfcc729827ff5394c13bfa9ca605f7d4e5304ff8a729827dc5394c13ffa1ca609ff10e5304ffec529827fe6294c077f314a609ff58a53005fac529827fc6294c077e314a605ffd4a5302ffca529817fc5294c73ffa14a638ff90a531c7f88529827fe3294c13fe194a609ffd865304dfec329827fe6194c057f30ca609fd98653015ecc329827fd6194c6f7eb0ca609fd58653005eac329827fc6194c057e30ca605ffd465302ffca329817fd5194c0bfe28ca637ffd06531bffc83298dffd4194c6ffe20ca609ffcc65304ffc6329827f63194c13fe98ca609ff0c6531bffe43298dffe2194c6ffe90ca637ff0865304ffec129827fe6094c037f304a609ff58253005fac129827fc6094c037e304a605ffd425302ffca129817fc5094c73ffa04a636ff902531b7f88129827fe3094c13fe184a638ffc82531b7fc41298dbfc2094c6fff884a636ff842531bffa21298dbfc1094c137fb2aa600ffd9153005fec8a9803bf6454c015fb22a635ff99153025fcc8a9803fd6454c6bfe322a604bf1915300778c8a9812bc6454c0bffaa2a605dfd515302ffca8a9817fd5454c01beaa2a605ff1515302dfec6a9817ff5354c0befa9aa609ff94d5304efca6a9827fc5354c13be29aa605f714d531affe86a9827fc4354c01ffb12a600bfd89531a7fcc4a980efe6254c01feb12a634ff1895301df8c4a9817ff5254c0bbfa92a605ff9495302ff8a4a98d7ff4254c69ff212a634ff109531a7fc64a9827fc3254c67ffb0aa633bfd855319ffcc2a980afe6154c67feb0aa633bf5855319ff8c2a980afc6154c0bffa8aa605ff9455302ffaa2a9817fc5154c67ffa0aa633ff9055319ffa82a98cffc4154c13ff98aa633ff8c55319fec62a98cffd3154c13fe18aa633ffc855319ffc42a98cffd2154c67fe10aa600ffd8153005fec0a98cbfe6054c037f302a600ff58153197f8c0a9806fc6054c0bffa82a605dfd415302ffca0a9817fc5054c6bffa02a632ff90153197f880a98cbfe3054c13fe182a634ffc8153197fc40a98cbfc2054c67ff882a632ff8415319ffa20a98cbfc1054c13ffb2c8609bfd964304ffccb21816fe6590c13feb2c8600bf5964304ff8cb21826fc6590c097eb248604ffd524318f7ea921813fe5490c09feaa48604ff1524302778a921826fe6390c13ffa9c8609ff94e4304fbca721827fd5390c01eea9c8609ff14e4304ffe8721827bf4390c09efa1c8609ff10e4304fb88721827ff6290c13ff3148603bf98a4304ffac521802fd6290c13fe3148603bf18a4318ffea5218c3fe5290c61fe2948604ffd0a43027fc8521813fc4290c13ff1948609ff0ca4304ffec321826ff6190c13ff30c8602bf9864304fecc32180af66190c13feb0c862fbf5864304feac321802f56190c13fe30c8602bf1864317ffea321
  | 6 => 0x801800c0100040000100000040100d400000800c00000403401000c00800c00000003400000400000400400402c00800400c00c00c00000802001401801400000400000001800000000400002c00000400800000400000002001800000404000c00400000000400000000802000001802c01c00800800000400001c01400c01000000000400400001000800000c00402000402000400000000800001800000400000400000000000402c00005c00000000000c00400801000403c00000000400001400000000c00801800403400800400800c00000400400400000400c01400002800001800400001000003001c00000000c00000000000001800401803800804c00800001800001001000000800000c01000001400c02401c04000000000401400000801000000004400400403400000000001400000000800c00000000c01c04800801c00400400800c00400000000001c00c01401000000800001000400000c00c00400c01400001008000000000000000800c00800002800000c0000000000a800000001800400800001800400000401002400000800003c00c00003401000400c00400001400000403001400003800400000000004801000001001400800000802000400000400000c00001400000802001000001000c00000000400403801001000c02801800001000c00000402800000801400401405005001000800000003802400000401401c00800400000800003401800400003800000804800000c00c004004000010010000000000024000000008008008097fb2aa804bfd9154027fea8aa017bf5455009ff2a2a804df95154027f8a8aa0137c5455009de2a2a804cf15154007fec6aa002ff6355001ff31aa800ff58d54007f8c6aa026fc635500bffa9aa805dfd4d5402ff8a6aa013ff4355009dfa1aa804ff10d54007fec4aa002ff6255079ff312a803bf98954007fac4aa0f3fc62550077e312a805ffd495402ffca4aa017fc5255009ffa12a804ff90954027f884aa0f3fe3255079fe192a83bffd85541ddfec2aa0effe61550057f30aa83bff585541ddfac2aa0effc61550057e30aa805ffd455402ffca2aa017fd515500bfe28aa804ffd0554027fc82aa013fd4155009fe20aa83bffcc5541dffc62aa0eff63155077fe98aa83bff0c5541dffe42aa0effe2155077fe90aa83bff08554007fec0aa002ff6055075ff302a801bf98154007fac0aa0ebfc60550037e302a805ffd415402ffca0aa017fc5055009ffa02a804ff90154027f880aa0ebfe3055075fe182a83cffc81541d7fc40aa0ebfc2055077ff882a83aff841541dffa20aa0ebfc105500b7eb2ca609ffd925304ffcc929812fe6494c13feb24a600bf5925304ff8c929826fc6494c0bffaa4a605ff952531cefca929817fd5494c0bfe2a4a605df1
  | 7 => 0x38001301a6a7582683b23f8000e09de9a580000009b0000000000000000000000001c50000000001a3000000065a13a4280020ba2900005fa258b48861c980000000023a2909bea119501410d880000000000017f14500000000024c00027da132a08000be14614909b99d87b10d80000029185200010f19115710a02aa3daa40042700a2a6c0b79ba06b80e26d99e15a8bf8a58908000000000000530000000001d9800000134a9b0120e48deab613818880000024480000000011b86688aac68d808081d15280020700017c8678002c40bf0490000798000000000000000000000000c7a300000000400f99ff10797c0169c49272b200000000000000018c9698258002ae966000000154916811194a8489021f9c114f0ff9fe9f781b8001882a5000056a408a200004e80000015b8000001c280027fab91210000478000002bb17495b1d00a78001a82a4a71000182a462018bc1e493e1850000a0a360001189a410095e000051800200a148ae89a9a922f2202ad0b40002051e30000000000001100000000000e30001129d60000528f79640858fea5ea8c02a14d8000aaab121400010000000023b0c51fc1688000000c689a1110000000002120000000710001f18000000000000000000000000000f7296a7b1c60e78000c41ca245a398001d900000000000000011300001c8000fe1158e227d2a28001e900000000000000015900022c26a9718001140000b3a61a498000eb0ea80000018d949a6603c87b8000001e40000000000000000000002341989ef2518ac80006e80000001b25613b18e22a0000000000722982b29489ed0ca963992aac8001f50000000d08000000af80000000008f8000000001e89fb0000000002bd8001800000000c10000498021cf80000000880025a89401a08c8fd27c0d328b9090000002aa80000000003e8001612740f303917100021a8000001b280000000000000015f8000cd00018f0000000ce80018f8228a38000a1a7aa6f8000271b326d000215007a55abb80006e0000002b3800058a0580028e27c90c8000d511daba00000006000023c00009e1012c707387da4c8ab9089760898001288000998002c30001d49fc80000100000000000000000007926ca692ae29987fa5280011900000001fab1a739a0abf80000a1da03896596900f2370d69790000348002c19178a300000022d9bf92e81a80004b810263a778d983f8158c394a295000802401401000402c00400001000400400801400c01400003401800402c04000000000001402000000000000800400000800002000000800002001800000402800001c00000400400400401800800002002400000800400001002000000000400000c03000000800000401401404801000000c00800402001c02c00800c06400802000000800000400001c
  | 8 => 0x1148002978000002b0ac10001aa095a2680016800010b995199a492ab80003082d1e99b79620000a91f080000000000000000000021d8000c612d2b30000000000000000000949e38000000288001900880001908000000000001af0eea3c8ab2400bd93da23a4faa92441d20358ff061a682929ce00000014e9f41d81358830330928278000000000000000000000000b50bc80000000000026f17b0000001ad003800060a94a2e80012b8001e08f60001b723a86a8000002c000002ca591099f219e8c1a168bea188109fd94aa1f2b414d00023e1318000000000000000001ca8000000001bb0c026e8ed0000df1448f5a388000000000000000002c3800000000000073018a6513d1c30001e28000001c78000000000000000000000000000fc2641d3a5e1ee0002c51f02020920300ec96f12616b0ad80012400000980014b8cb13c80000000013a9d58090f680000028b000000000000000256a5da9eab50960b80fa80003f2099f59f92182770a496303e00009f00000000025ca1ba871aa8000000410352a00291dc80016e0001c900025b9568000002601f100020c8002108082720000000cc25f1c71b4a3f2a80d195208792c80000000000000016c8001162418ac0621a98000000000b19258002b818b1b50829be00002c00017380000023e8a400017800020380022992980000000009322623b9db83291c9e18de0002509c40002c60000510c708911a8000001fe00000021c80007629f88b80000000000000014c8000000da0002328c816d9560db02624826898180000008a1cf2a3a6290621c2a714c0baa8a88000000004595a16502180ca9405f1401388001b88000000850630439b69350002ab0002869dfa8daaf961a0e8fc92a82088c22496705505798981610588e8000918c580000028d00025424b8002288001eea3788d28414384e00010f8000b005624780000012a27280020d8220c49cd00000000000007780002480000000000009e8dc8001ab00000000000000020a80002300000028f80005812d80028921293305aa1a00007800028e83c17e1b818096a0b597001f059050a1e937aaf09c00022d211235a090f90000af1bb8001eb96680000003200000000000000007080000000ea6e1839cb8911ad8000f08662a624380015c95d00000000000000012829122427e04623d2bc9e12c080000000013e8002c78e70000ef806aac17a80017d00016291b0000000001a72920000001e0000000296000076a761a107d1cb1750002a783b80006c2220000001c6a2b8f10000700f414b0cda9ba2100000000000011a0000001328138f20001bc9d400d1510672621e59980002572c5884893aa119fa9f279a5c0681559579ea25b0058000002521dd97b9bc0002888002819c084b0a1044a7180000001c23380015
  | 9 => 0xd1000000000000257a2f85380000003180280b2081052bc269800000153098ac80729d098d0000001d19b19c8216118120239182274a042882368398ae13392b08b0d79ab8982780418d28ccaa31932630d5901a208821e692682f0001a48b31550031599ce87ea488001d500022e0ee0000000000000001d29ea80000006480029a07594782e80003d80000000005d90e81802113a13c0d019a88d8001139f2a990148001f70c20000ed94406407511998785018597a2861af8d485700019b00c0002829c21bf25300000004c80000007c8000f480006c82380005b8b22790002c20429cc8b6a2c8c900000b8000001810d70001518dba8f14e05ea51000081059a2316a97ea2803792c2789b9a9390aa4f0000000420002348000000000001108000ce01300022a8000a68838000000001840f883100010306a15d8001f68170d12be1dd28780024d28100004a97700000018718e8002b587180000026100000018aab7a851020f804f0f01ed8ea1c59bd17293705d2410002c89c18001219220e59b09311b90000870ec1228bb9f3ab020fa0c00713bab70000000dd80019b972167800204a76800146a581d7a5487c0f280000000026703d0000002b980019a00000000019c0002678dc1b00eb8a800000000000017317580000000000000000000000019580000020a2b8a0d18c1e517401280000005e0001e82ba8789e62502028000e418490d0000000ad00028093f9c000000009d1a380001e04a0e88b991c00020880000011f82000000018b8699de0cb8002aa03700f8000c280000000000000011d1151608000000000000000d38000c9a5d0000000000001a1a7ea4e08f046a9c8018001942598000000000000002a20d90c88000000000002179991588fb8000000000000000a00000000000000b89170d210807e0818001e782509500011e1c88000000000001eb03680012f0971c390480006900000029000000000000021e05b0002ad8002a58002319891320000e3a3526481400016481780015c20f0868280000002a18000000001040001250001580000001b5a43285800a8204c04fa9580015080000000006112382d80000000020e1b60e10000001bd9779f9a1717f80000000000000000020b1f60002bd193abe80001d8bb1fd21b07414280000024e9ae1a008890b1831ec94819ca658a61db00000015ea2b00029c033800203222a012271ae80019d15f1d309c8000000f529e29307a9ec00019180019f00a80001e91f00000012480000000000000000014f9b38050001960000000000001120ca000054a8c8688409291d680011e9f48000e520793406b0e90fb1b41ef8000001a51df0000360001f88000000000000002060000001a29309a604889f81900013613990c0000001b1000000000000000000242000000000000
  | 10 => 0x5590e19780027f0000000000a8ac49d880000004700027b8001f82472b4a3828380004d800000245000000270a6a1f32c28f18000001fa0000198000000002a98cf92e0000000fa186a3100000004302b9ac00000000000000000007f00029d8000000000000001ac96c2309fb9b22b68cf00022790280005c8000000bd0b71708000d62100770000001cd9470000b280000028a0150000000000000991a2000260a158aa0000e987a0da8969a88000001118000002330000ef14080028324684d0c080d80000008e00000023216d1420e18dd0a98001baa4a0000e682fa4da7a02993f136811aa68ba09d9860450001230002668c3000000176a06a219e229a854048034024065120a9726b8b1062a8016b98a00006f86d96f8000001418d41390978000001459da9430b600005a00000000000600010719219700000026b154000000000258800179800000000000000004a9d0002198b92550e802e00000000000000000025a00000016ea4b00003a02b2752bf0a71068e62731788a50380002a8a989a780006380025f80012fa899cc00017d8000df8000001dc0001e700024a8001faa0000000000000008400000000022500016021d06f06d1d704421910380005c0fd9278000748f38000e280000003a8000000000000002539968000b08e01ff9
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x9104c920215f676d8520036f676d8520014f676d8520006f765d8520006f665d8520006f565d8520006f465d8520006f764d8520006f664d8520006f564d8520006f464d8520005f573d8520006f763d8520006f663d8520006f563d8520006f463d8520207e772d8520207e472d852020fe632d8520007e532d852020ff370d8520207f070d8520207f230d852020ff320d8520207e620d8520207e420d8520207f020d8520207e020d8520006f775d8520006f675d8520006f575d8520006f475d8520006f774d8520006f674d8520006f574d8520006f474d8520006f754d8520006f654d8520006f554d8520006f454d8520006f773d8520006f673d8520006f573d8520004f573d8520006f473d8520006f753d8520006f653d8520006f553d8520006f453d8520006f743d8520006f643d8520006f543d8520006f443d8520206f772d8520036f672d8520206f572d8520206f472d852020ef752d852020ef652d852020ef552d852020ef452d852020ef742d852020ef642d852020ef542d852020ef442d852020ef732d852020ef632d852020ef532d852020ef432d8520206f770d8520206f670d8520206f570d8520206f470d8520206f750d8520206f650d8520206f550d8520206f450d8520206f740d8520206f640d8520206f540d8520206f440d8520206f730d8520206f630d8520206f530d8520206f430d8520206f720d8520206f620d8520206f520d8520206f420d8520006f7764c520005f6764c520006f6764c520004f6764c520006f5764c520005f4764c520006f4764c520004f4764c520006f7654c5200def6654c520006f5654c5200def4654c520006f7644c5200d6f6644c520006f5644c5200d6f4644c5201fdf7734c520037d7734c520006f7634c52004ef6634c520007d6634c52004ed6634c520006f5634c520007d5634c520006d5634c52004ef4634c5200cfe6724c520007e5724c5200c6f7624c5200cfd7324c5200cfe6324c5200cfd5324c520007e5324c520007c5324c5200c7f2704c520007f1704c5200c6f7604c5200c7d7304c5200c7f2304c5200c7d5304c5200cff3204c5200c7e6204c5200c7e4204c5200c7f0204c5200c7e0204c52001df8764c12004ef8764c12001cf8764c120006fb654c120006f9654c120006fb644c120006f9644c12000dfb734c12000fdb734c120007db634c12004efa634c12004ef8634c120007d8634c120007eb724c12001dfa724c12001df8724c12005fe8724c12001de8724c12000efb624c12000feb624c12005fdb324c12005fea324c12005fd9324c120007e9324c120007c9324c1201f5fb714c1201f5f9714c120007f3614c1201eff0614c1201efdb314c1201eff2314c1201efd9314c120007f1314c120007d1314c12005feb214c1201efe9214c120
  | 1 => 0x9120014fe7159120004fd7159120014fc7159120006f47159120014f4715912003ebf4159120006bd4159120006f63159120124ff7059120006fb7059120126fa3059120004ff7655120004fe7655120004fd7655120004fc765512003f3c54551201def461551201d7e8205512004cfe76d8d20035f471d8d20006f461d8d20237e820d8d2002cfe75d8d20004fd75d8d2002cfc75d8d20024fe74d8d20004fd74d8d20024fc74d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d2023edf32d8d2023edd32d8d20004ff71d8d20006f771d8d20014fe71d8d20004fd71d8d20014fc71d8d20006f471d8d20014f471d8d20006f631d8d2001cff70d8d2000cfe70d8d2001cfd70d8d2000cfc70d8d20236df30d8d20236dd30d8d200e4fd7698d20006df6398d200e5ed7298d20035f67198d20005f57198d20006f46198d2005df97098d20107e82098d2004cff7658d20105ef7258d20005f77158d20035f47158d20006f46158d2007dfb7058d200e7e82058d20004ff7558d2002cfe7558d2002cfc7558d20004ff7458d20024fe7458d20024fc7458d20006df7358d20104ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20014fe7158d20004fd7158d20014fc7158d20006f47158d20014f47158d20006df3158d20006f63158d20006dd3158d200e4ff7058d20006fb7058d20234fe7618d200457e7518d200057d7518d2003dbe7418d20005bd7418d2004ede6318d20006dd6318d20035f67118d20005f57118d20006f46118d2022fe82018d2004cff7694d20004fe7694d20004fd7694d2004cfc7694d2001dee7294d20005ed7294d20035f67194d20005f57194d201bef46194d2000dfa7094d20005f97094d201b7e82094d20004ff7654d20004fe7654d20004fd7654d20004fc7654d2002e7e6554d200067d6554d20005bf7454d2003dbc7454d2019ef46154d20197e82054d2004cff7690d20004fe7690d20004fd7690d2004cfc7690d2001dee7290d20005ed7290d20035f67190d20005f57190d2017ef46190d2000dfa7090d20005f97090d20177e82090d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d200457c7550d20026be6450d20006bd6450d2015ef46150d20157e82050d2000dec764c92004eec764c92000cec764c920006ef654c920006ed654c920006ef644c920006ed644c92001def734c92001fcf734c920007cf634c92004eee634c92004eec634c920007cc634c920225ef714c920225ed714c92021fe4614c92021fcf314c92021fe6314c92021fcd314c920007eb704c92000dee704c92000dec704c9200e7e8704c92000de8704c92001eef604c92001feb604c9200e7cf304c9200e7ea304c9200e7cd304c9200e7ea104c92021fe
  | 2 => 0x6f7b5154130297795154130297db3154130297f23154130297d93154130007f13154130007d1315413004df87650130026f8765013004cf87650130005fb7550130005f97550130006fb6550130006f9655013000dfb745013000fbb7450130007bb6450130026fa6450130026f86450130067b8645013028fbb5450130067b85450130007db735013004dfa735013004df87350130007d8735013000efb635013000fdb6350130067bb4350130007b94350130005fb7250130067bb4250130007b94250130007db3250130007d93250130067bb4150130287b94150130287db3150130287f23150130287d93150130007f13150130007d1315013002cfe76d95200467e65d952003dbe74d9520005bd74d9520006f461d952026fe820d952013cfd75d9520024fe74d9520006be74d9520024be74d9520004fd74d9520006bd74d9520004bd74d9520024fc74d952004cfe73d9520004fd73d952000cff72d952001cfe72d952000cfd72d952001cfc72d952027e7f52d952027e7d52d952027eee32d9520004ff71d9520014fe71d9520004fd71d9520014fc71d9520006f631d952001cff70d952000cfe70d952001cfd70d952000cfc70d952026e7f50d952026e7d50d952026efa30d952002cff76595200467c6559520265ef7259520005f77159520035f47159520006f46159520275fb705952013fe8205952026cff75595200067f7559520004ff7459520024fe7459520024fc74595200067e54595200467c5459520004ff735952004cfc73595200467f5359520264ff7259520006ef72595200b6ee3259520004ff7159520006f77159520004f77159520014fe7159520004fd7159520014fc7159520006f47159520014f471595200467f51595200067d5159520006f6315952013cff7059520006fb705952013efa3059520024fe76d91200457e75d91200057d75d912003ebe64d9120006f461d912024fe820d912002cfe75d91200067e75d912002c7e75d9120004fd75d91200067d75d91200047d75d912002cfc75d9120124fd74d912004cfe73d9120004fd73d912000cff72d912001cfe72d912000cfd72d912001cfc72d912025ebf42d912025ebd42d912025eee32d9120004ff71d9120014fe71d9120004fd71d9120014fc71d9120006f631d912001cff70d912000cfe70d912001cfd70d912000cfc70d912024ebf40d912024ebd40d912024efa30d9120024ff765912003ebc6459120245ef7259120005f77159120035f47159120006f46159120255fb7059120127e82059120004ff755912002cfe755912002cfc755912024cff7459120006bf7459120006bf545912003ebc5459120004ff735912004cfc735912003ebf4359120244ff7259120006ef725912009eee3259120004ff7159120006f77159120004f7715
  | 3 => 0xf60cc93004fdb60cc930107da50cc930107da40cc930107da20cc93000cfc764c930006ef624c93001eec624c93004fcc324c9302bfd6314c930005fb704c93000df8704c93004fd8304c93000ddc764c93001edc764c93000cdc764c93004ddf724c93004fcf724c930007cf624c93001ede624c93001edc624c93005fcc624c93005fce524c930007cd524c93005fce424c930007cd424c9302c5df714c9302c5dd714c9302bedf614c9302bedd614c930007db704c93000dde704c93000ddc704c9300e7d8704c93004edf604c93004fdb604c9300e7da504c9300e7da404c9300e7cf204c9300e7da204c930016f7764c5300c6f6764c5300c6f5764c530016f4764c530006f7654c5300def6654c530006f5654c5300def4654c530006f7644c5300d6f6644c530006f5644c5300d6f4644c53004df7734c530057d7734c53004ef7634c5302b7d7534c53004fd6534c530007d5534c53004fd4534c5302afd7434c53004fd6434c530007d5434c53004fd4434c530006f7624c5300cef6624c5300cef4624c53004fd7324c5302a7d6324c530007d5324c53004fd4324c530007f3704c5300c7f0704c53004ef7604c5300c7f2504c5300c7f2404c53004ff3304c5300c7d6304c53004fd4304c53004ff0304c5300c7f2204c530057d7764c530016d7764c5300c7d4764c530016d4764c530007d7754c5302b7d6754c530007d5754c5302b7d4754c530007d7654c5302b7d6654c530007d5654c5302b7d4654c530007d7744c5302afd6744c530007d5744c5302afd4744c530007d7644c5302afd6644c530007d5644c5302afd4644c5302b7d7544c5302afd6544c530007d5544c5302afd4544c530007d7724c5302a7d6724c530007d5724c5302a7d4724c530007d7624c530006d7624c5302a7d6624c530007d5624c5302a7d4624c5302b7d7524c5302a7d6524c530007d5524c5302a7d4524c5302afd7424c5302a7d6424c530007d5424c5302a7d4424c5300c7d7704c530007d3704c5300c7d6704c5300c7d5704c5300c7d4704c5300c7d0704c53004fd7604c53004ed7604c53004fd3604c5300c7d7504c5300c7d6504c5300c7d2504c5300c7d5504c5300c7d4504c5300c7d7404c5300c7d6404c5300c7d2404c5300c7d5404c5300c7d4404c5300c7d7204c5300c7d6204c5300c7d2204c5300c7d4204c53004df8765413002ef8765413004cf8765413000dfb755413000f7b75541300077b655413002efa655413002ef8655413006f786554130005fb7454130006fb6454130006f9645413029f7a545413006f785454130007db735413004dfa735413004df87354130007d8735413000efb635413000fdb635413006f7b5354130007795354130005fb725413006f7b5254130007795254130007db3254130007d93254130
  | 4 => 0x953001cfc72d9530004ff71d9530014fe71d9530004fd71d9530014fc71d9530006f631d953004cff70d953004cfd70d95301b67f50d95301b67d50d95301b6fa40d953006e7c6559530005bf7459530065bc74595302e5df73595301b4ff75595300067f7559530004ff7459530006bf7459530004bf7459530024fe7459530024fc7459530006bc7459530024bc74595302e4ff7359530006df7359530004ff725953001cfe725953001cfc725953006e7f5259530004ff7159530014fe7159530004fd7159530014fc7159530006f63159530194ff7059530006fb7059530196fa4059530024fe76d9130066be64d913002cfe75d9130004fd75d913002cfc75d9130006bf54d9130066bc54d913004cfe73d913000cfd73d913004cfc73d9130066bf43d913001cfe72d9130004fd72d913001cfc72d9130004ff71d9130014fe71d9130004fd71d9130014fc71d9130006f631d913004cff70d913004cfd70d9130176fa50d9130176bf40d9130176bd40d91300057f755913006d7c7559130066bc64591302dddf7359130004ff75591300067f75591300047f755913002cfe755913002cfc75591300067c755913002c7c7559130174ff7459130006bf74591302dcff7359130006df7359130004ff725913001cfe725913001cfc7259130066bf4259130004ff7159130014fe7159130004fd7159130014fc7159130006f63159130154ff7059130006fb7059130156fa5059130004ff7655130004fe7655130004fd7655130004fc76551300673c545513000dfa705513002cff7654d3000cfe7654d30194fd7654d3000cfc7654d300067f6554d3002e7c6554d30005bf7454d30065bc7454d30005fb7054d3000df87054d30024ff7650d3000cfe7650d30154fd7650d3000cfc7650d300057f7550d3006d7c7550d30006bf6450d30026bc6450d30005fb7050d3000df87050d3001cfe76d893005eee62d893002cfe75d8930004fd75d893002cfc75d8930024fe74d8930004fd74d8930024fc74d893000cfd73d893001cfc73d893005eee32d8930004ff71d8930014fe71d8930004fd71d8930014fc71d8930006df31d8930006f631d8930006dd31d8930006ee21d893005eec21d893000cfe70d893004cfd70d893000cfc70d8930106ef20d893005eec6258930005f77158930055f47158930004ff7654930004fe7654930004fc765493002e7e65549300067d655493000dfa7054930004ff7650930004fe7650930004fc7650930026be6450930006bd645093000dfa705093022dde76cc93004ede76cc9300e5dd72cc93001ede62cc93001edc62cc93004ddf71cc93004fd671cc9302d5dd71cc93004fd571cc930005d571cc9302cedf61cc9302cedd61cc93004fdb70cc93000dde70cc93000ddc70cc93004fd870cc93004ed
  | 5 => 0x4ef93058b300e6ef2058b30004ff7654b30004fd7654b3004cfc7654b3002e7e6554b300067d6554b3001eee6254b30006ed6254b30146f66154b30004ff7650b30004fd7650b3004cfc7650b30026be6450b30006bd6450b3001eee6250b30006ed6250b3012ef66150b3004ddf764cb3031edf764cb3004fcf724cb3004fcf624cb3001ede624cb3001edc624cb3004fcc624cb3007fce524cb30007cd524cb3007fce424cb30007cd424cb30315df714cb30315dd714cb3004edf614cb3004fd6614cb3030edd614cb3004fd5614cb3000dde704cb3000ddc704cb300e7cf204cb30006f77558730006f67558730006f57558730006f47558730006f77458730006f67458730006f57458730006f47458730006f75458730006f65458730006f55458730006f4545873004ef77358730014f7735873004ef6735873004ef57358730014f5735873004ef4735873004ef7535873004ef6535873004ef5535873004ef4535873004ef7435873004ef6435873004ef5435873004ef44358730006f77258730006f67258730006f57258730006f47258730006f75258730006f65258730006f55258730006f45258730006f74258730006f64258730006f54258730006f4425873004ef7325873004ed7325873004ef6325873004ef53258730006d5325873004ef432587300c6f770587300c6f670587300c6f570587300c6f470587300c6f750587300c6f650587300c6f550587300c6f450587300c6f740587300c6f640587300c6f540587300c6f4405873004ef7305873004ef6305873004ef5305873004ef430587300c6f720587300c6f620587300c6f520587300c6f4205873004fd7764c73004dd7764c730306d7764c730007d7754c7302ffd6754c730007d5754c7302ffd4754c73004fd7654c73004fd6654c73004fd5654c73004fd4654c730007d7744c7302f7d6744c730007d5744c7302f7d4744c73004fd7644c73004fd6644c73004fd5644c73004fd4644c7302ffd7544c7302f7d6544c730007d5544c7302f7d4544c730007d7724c7302efd6724c730007d5724c7302efd4724c73004fd7624c73004fd6624c73004fd5624c730006d5624c73004fd4624c7302ffd7524c7302efd6524c730007d5524c7302efd4524c7302f7d7424c7302efd6424c730007d5424c7302efd4424c7300c7d7704c7300c7d6704c7300c7d5704c7300c7d4704c7300c6d5604c7300c7d7504c7300c7d6504c7300c7d5504c7300c7d4504c7300c7d7404c7300c7d6404c7300c7d5404c7300c7d4404c7300c7d7204c7300c7d6204c7300c7d4204c73002cfe76d953006e7e65d9530024fe74d9530004fd74d9530024fc74d95300067e54d953006e7c54d953004cfe73d953000cfd73d953004cfc73d953006e7f53d953001cfe72d9530004fd72d
  | 6 => 0x571cc94000dfa70cc940005f970cc940004ff764c940004fe764c940004fc764c940025be744c940005bd744c94001eee624c940007ad424c940006f7764c540006f6764c540006f5764c540006f4764c540006f7654c5400def6654c540006f5654c5400def4654c5400d7b6744c540007b5744c5400c6f7644c54032fb7544c5400d7b4544c5401fdf7734c540097d7734c540006f7634c54004ef6634c54004ef4634c5400d7b7434c540007b5434c540006f7624c5400cef6624c5400cef4624c5400d7b7424c540007b5424c540007d7324c540007d5324c5400c6f7604c5400c7f2504c5400d7f3404c5400c7b6404c5400c7b4404c5400c7f0404c5400c7f2304c540025f8765414002ef87654140024f8765414000dfb755414000f7b75541400077b655414002efa655414002ef865541400a7786554140007bb7454140025fa7454140025f874541400bfb8745414000efb645414000fbb64541400a7bb54541400bf7a54541400bf7854541400bfb854541400bf385454140005fb7354140006fb63541400a77b53541400077953541400bfbb4354140007b943541400a77b52541400077952541400bfbb4254140007b942541400a77b51541403277951541400bfbb4154140327b94154140327f23154140007f1315414004e7f7559730004ff7459730006bf7459730004bf7459730024fe7459730024fc7459730006bc7459730024bc745973008e7f545973004cff735973000cfe735973004cfd735973000cfc735973004e7e535973004e7c5359730004ff725973001cfe725973001cfc725973008e7f5259730004ff7159730014fe7159730004fd7159730014fc715973004ef6315973004ef531597301967f50597301967d505973004efa305973004ef93059730004ff75593300067f75593300047f755933002cfe755933002cfc75593300067c755933002c7c755933004ebf7459330086be545933004cff735933000cfe735933004cfd735933000cfc735933004ebe435933004ebc4359330004ff725933001cfe725933001cfc7259330086bf4259330004ff7159330014fe7159330004fd7159330014fc715933004ef6315933004ef53159330156bf4059330156bd405933004efa305933004ef93059330004ff765533004cfe7655330004fd765533004cfc765533002e7e65553300067d6555330026be6455330006bd64553300873c54553301def66155330004ff7558b3002cfe7558b3002cfc7558b30004ff7458b30024fe7458b30024fc7458b3000cfe7358b3001cfd7358b3000cfc7358b3004eef7258b3007eee5258b3007eee4258b3004eef3258b3004eec3258b30004ff7158b30014fe7158b30004fd7158b30014fc7158b3004edf3158b3004ef63158b30006dd3158b3004ef53158b3004efa3058b30
  | 7 => 0x9540004ff725954001cfe725954001cfc7259540004ff7159540014fe7159540004fd7159540014fc7159540006f631595401d4ff7059540006fb70595401d6fa305954004cfe76d8d4002cfe75d8d40004fd75d8d4002cfc75d8d4000cfd74d8d40366de43d8d40366dd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d40366bf42d8d40004ff71d8d40014fe71d8d40004fd71d8d40014fc71d8d40006f631d8d40024fd70d8d402defa50d8d402dedf30d8d40006df6398d40095f67198d40005f57198d40065f97098d400057f7558d400a57c7558d40085fb7058d400a57e7518d400057d7518d4004ede6318d40006dd6318d4009dee7218d40005ed7218d40095f67118d40005f57118d40004fe7694d40004fd7694d4004cfc7694d400067f6594d4002e7c6594d40025be7494d40005bd7494d401cf3c5494d40095f67194d40005f57194d4000dfa7094d40005f97094d40004ff7654d40004fe7654d40004fc7654d4002e7e6554d400067d6554d40005bf7454d40025bc7454d400a73f5454d4000dfa7054d4000dbc7650d4004ebc7650d4000cbc7650d400073f7550d400a5be7550d400a5bc7550d400073c7550d400a53c7550d40006bf6550d40006bd6550d40025bf7350d400279f7350d400079f6350d4004ebe6350d4004ebc6350d400079c6350d400079e5350d400079d5350d40005bf7250d4035dbf7150d4035dbd7150d40357b63150d40007bb7050d4000dbe7050d4000dbc7050d40157b87050d40026bf6050d40027bb6050d40157ba5050d40157ba3050d4001cfe76d894009eee62d894002cfe75d8940004fd75d894002cfc75d894000cfd74d894001cfc74d8940006bf54d894034ebc54d894004cfe73d8940004fd73d894034ebf43d8940006bd43d894009eee42d894034eed42d8940004ff71d8940014fe71d8940004fd71d8940014fc71d894034ebf41d8940006bd41d8940006f631d8940024fd70d8940246fa30d8940246ef20d894009eec6258940005f77158940095f47158940345fb7058940004ff7654940004fe7654940004fc76549400067f655494002e7c6554940005bf7454940025bc745494014f3c545494000dbc765094001ebc765094000cbc76509400a5be75509400a5bc7550940136be6550940136bc6550940005bf7350940006bf6350940025bf7250940027af7250940007af625094001ebe625094001ebc625094009fac625094009fae5250940007ad525094009fae325094033dbf715094033dbd7150940336bf6150940336bd6150940337b63150940007bb705094000dbe705094000dbc7050940127b87050940026bf6050940027bb6050940127ba5050940127ba3050940004fe76cc940004fd76cc94004cfc76cc940025be74cc940005bd74cc940095f671cc940005f
  | 8 => 0x75d5350d5000dfa7050d5001cfe76d89500b6ee62d895000cfd75d895001cfc75d8950024fe74d8950004fd74d8950024fc74d89500067e54d89503ae7c54d895004cfe73d8950004fd73d89503ae7f53d89500067d53d89500b6ee52d89503aeed52d8950004ff71d8950014fe71d8950004fd71d8950014fc71d89503ae7f51d89500067d51d8950006f631d895002cfd70d8950266fa30d8950266ef20d89500b6ec6258950005f771589500adf471589503a5fb705895000d7c765495001e7c765495000c7c76549500bd7e74549500bd7c745495014e7e645495014e7c64549500057f73549500067f635495002d7f725495002f6f72549500076f625495001e7e625495001e7c62549500b76c62549500b76e42549500b76e325495039d7f715495039d7d71549503967f61549503967d61549503977631549500077b705495000d7e705495000d7c705495013f78705495002e7f605495002f7b605495013f7a405495013f7a3054950004ff7650950004fe7650950004fc76509500057f755095002d7c7550950006bf6450950026bc64509500bf3c54509500076d5250950004fe76cc950004fd76cc95004cfc76cc95002d7e75cc9500057d75cc9500adf671cc950005f571cc95000dfa70cc950005f970cc950004ff764c950004fe764c950004fc764c95002d7e754c9500057d754c95001eee624c9500076d524c950006f7764c550006f6764c550006f5764c550006f4764c5500df76754c55000775754c5500c6f7654c550006f7644c5500d6f6644c5500d6f4644c55038f76544c5500df74544c5501fdf7734c5500afd7734c550006f7634c55004ef6634c55004ef4634c5500df77534c55000775534c550006f7624c5500cef6624c5500cef4624c5500df77524c55000775524c550007d7324c550007d5324c5500c6f7604c5500dff3504c5500c776504c5500c774504c5500c7f0504c5500c7f2404c5500c7f2304c55002cfe76d95400a67e65d9540025be74d954000dbd74d95400a73f54d95401d4fd75d954000cff74d9540024fe74d954000cfd74d9540376bd74d954000cbd74d9540024fc74d95403867f54d95400a6bf54d95403867d54d9540386bc54d954004cfe73d9540004fd73d95400a67c53d9540386bf43d954001cfe72d9540004fd72d954001cfc72d95400a67f52d9540004ff71d9540014fe71d9540004fd71d9540014fc71d9540006f631d9540024ff70d9540024fd70d95403767f50d95403767d50d9540376fa30d954002cff76595400a67c655954036dbf74595400bf3c545954037dfb7059540374ff75595400067f755954036cff7459540006bf74595400a6bf54595400be7e54595400be7c54595400bebc54595400be3c5459540004ff735954004cfc73595400a67f53595400bebf435
  | 9 => 0x7204c9310cfc7204c9310cfd6204c9310cfd4204c9310c5f676d81310ddf675d8131005f575d81310ddf475d81310d5f674d8131005f574d81310d5f474d8131077d773d813104df673d8131015f573d8131076f763d8131077d763d81310cdf672d8131005f572d81310cdf472d8131006f762d8131006f562d8131007d732d8131007d532d81310c6f660d81310c7f260d81310c6f460d81310c7f230d8131007f320d81310c7f020d8131005f775581310ddf675581310ddf47558131005f774581310d5f674581310d5f474581313ddf77358131007d773581313ddd77358131056f76358131057d76358131005f77258131007e77258131005e772581310cdf672581310cdf47258131007e472581310cde47258131006f76258131006f56258131007d73258131007d532581310c5f77058131007f360581310c6f660581310c6f460581310c7f060581310c6f060581310c7f22058131024fe76d915002d7e75d915000d7d75d91500bebe64d91500bf3e54d915000cfd75d915036e7d75d915000c7d75d9150024fc75d91500be7e54d91500bebe54d91503d6bd54d91500be7c54d915004cfe73d9150004fd73d91503d67f53d91500bebc43d915001cfe72d9150004fd72d915001cfc72d91500bebf42d9150004ff71d9150014fe71d9150004fd71d9150014fc71d9150006f631d915002cfd70d915036ebf40d915036efa30d91500bebc64591500bf3c54591503cdfb705915004cfe76d8d5000cfd75d8d50024fe74d8d50004fd74d8d50024fc74d8d503c6de53d8d503c6dd53d8d5001cfe72d8d50004fd72d8d5001cfc72d8d503c67f52d8d50004ff71d8d50014fe71d8d50004fd71d8d50014fc71d8d50006f631d8d5002cfd70d8d502e6fa40d8d502e6df30d8d50006df6398d500adf67198d50005f57198d5006df97098d50005bf7458d500bdbc7458d5008dfb7058d500bdbe7418d50005bd7418d5004ede6318d50006dd6318d500b5ee7218d50005ed7218d500adf67118d50005f57118d5000d7c7654d5004e7c7654d5000c7c7654d500073f7454d500bd7e7454d500bd7c7454d500073c7454d500bd3c7454d500067f6454d5002d7f7354d5002f5f7354d500075f6354d5004e7e6354d5004e7c6354d500075c6354d500057f7254d503bd7f7154d503bd7d7154d503b7763154d500077b7054d5000d7e7054d5000d7c7054d50197787054d5002e7f6054d5002f7b6054d501977a4054d501977a3054d50004fe7690d50004fd7690d5004cfc7690d5002d7e7590d500057d7590d50006bf6490d50026bc6490d500bf3c5490d500075d5390d500adf67190d50005f57190d5000dfa7090d50005f97090d50004ff7650d50004fe7650d50004fc7650d500057f7550d5002d7c7550d50026be6450d500bf3e5450d50
  | 10 => 0x931005f7735093104df6735093104df4735093112ef7635093112fd763509310d7b74350931007b54350931425f772509310cfe65250931007e552509310d7e742509310cfb642509310cfb442509310cfe442509310cfe63250931005f770509310c5f670509310c5f470509310d7b7405093104fd676cc93141dd676cc93104ed676cc93104fd775cc93104fd675cc93104fd575cc93104fd475cc931007d765cc931417d665cc931007d565cc931417d465cc93104fd774cc93104fd674cc93104fd574cc93104fd474cc931007d764cc93140fd664cc931007d564cc93140fd464cc931417d754cc93140fd654cc931007d554cc93140fd454cc9310edd572cc93110fd762cc9310cfd662cc9310cfd562cc9310cfd462cc9310cfd752cc9310cfd652cc9310cfd552cc9310cfd452cc9310cfd742cc9310cfd642cc9310cfd542cc9310cfd442cc93104fd770cc93104fd670cc93104fd570cc931005d570cc93104fd470cc931407d660cc931407d460cc931417d750cc931407d650cc931407d450cc93140fd740cc931407d640cc931407d440cc9310cfd720cc9310cfd620cc9310cfd420cc9313fdf7764c931015f6764c9310edf5764c931015f4764c931005f7754c9310ddf6754c931005f5754c9310ddf4754c931005f7744c9310d5f6744c931005f5744c9310d5f4744c93104df7734c93104ef7634c9310efd7634c9313f7d7534c93104fd6534c931007d5534c93104fd4534c9313efd7434c93104fd6434c931007d5434c93104fd4434c93104df7724c931007e7624c9310cfe4624c9310cfe6524c931007e5524c9310cfe6424c931007e5424c93104fe7324c9310cfd6324c93104fd4324c93104fe4324c931005f7704c9310c5f6704c9310c5f4704c93104fd7304c9313e7d6304c93104fd4304c9310cfe7204c9310efd6764c931015d6764c9310efd4764c931015d4764c931007d7754c9313f7d6754c931007d5754c9313f7d4754c931007d7654c9313f7d6654c931007d5654c9313f7d4654c931007d7744c9313efd6744c931007d5744c9313efd4744c931007d7644c9313efd6644c931007d5644c9313efd4644c9313f7d7544c9313efd6544c931007d5544c9313efd4544c93104fd7724c93104dd7724c93104fc7724c9310cfd7624c931007c7624c9310cfd6624c9310efd5624c9310cfd4624c9310cfc4624c9310cfd7524c9310cfd6524c9310cfc6524c9310cfd5524c931007c5524c9310cfd4524c9310cfd7424c9310cfd6424c9310cfc6424c9310cfd5424c931007c5424c9310cfd4424c931007d7704c931005d7704c9313e7d6704c931007d5704c9313e7d4704c9313e7d6604c9313e7d4604c9313f7d7504c9313e7d6504c9313e7d4504c9313efd7404c9313e7d6404c9313e7d4404c9310cfd
  | 11 => 0x1def763551311dfd763551310df7753551310d7b74355131005f772551310cdf672551310cdf47255131005f770551310c5f670551310c5f4705513145df77654d31015f67654d3119df57654d31015f47654d3104df77554d31007776554d310df746554d31005f77454d31007b77454d31005b77454d310d5f67454d310d5f47454d31007b47454d310d5b47454d310df775454d31007755454d3104df77354d3104ef76354d3119fd76354d310dfd75354d3104f765354d3104f745354d3104fd45354d3104f545354d3104fd64354d31005f77254d310cdf67254d310cdf47254d310df775254d3104fd73254d31005f77054d310c5f67054d310c5f47054d310df775054d3104fd73054d31455f77650d31015f67650d3115df57650d31015f47650d31005f77550d31007777550d31005777550d310ddf67550d31005f57550d310ddf47550d31007747550d310dd747550d3104df77450d31007b76450d310d7b46450d310d7b65450d31007b55450d3104df77350d3104ef76350d3115fd76350d3104fd65350d31007d55350d310d7d74350d3104fb64350d3104fb44350d3104fd44350d3104f944350d31005f77250d310cdf67250d310cdf47250d310d7b74250d3104fd73250d31005f77050d310c5f67050d310c5f47050d310d7b74050d3104fd73050d3141df676d89310ddf675d8931005f575d89310ddf475d89310d5f674d8931005f574d89310d5f474d893110fd773d893104df673d8931015f573d893110ef763d893110fd763d89310cef662d89310cfe662d89310cef462d89310cfe632d89310c5f670d8931005f570d89310c5f470d8931007e620d89310cfe420d8931005f775589310ddf675589310ddf47558931005f774589310d5f674589310d5f474589313fdf77358931007d773589313fdd773589310eef763589310efd7635893110df77258931007e762589310cef662589310cef462589310cfe462589310cee46258931005f77058931007f37058931005f370589310c5f670589310c5f47058931007f070589310c5f070589310cfe72058931005f77654931005f67654931005f57654931005f4765493144df775549310df766554931007756554931005f774549310d5f674549310d5f474549314477654549310df745454931005f7735493104df6735493104df47354931146f76354931147d763549310df77535493100775535493143df772549310dfe752549310cf7652549310cf7452549310cfe452549310cfe642549310cfe63254931005f770549310c5f670549310c5f470549310df775054931005f77650931005f67650931005f57650931005f47650931005f775509310ddf67550931005f575509310ddf47550931435f774509310d7b66450931007b5645093142fb754509310d7b4545
  | 12 => 0xd3154932005ef70549320ff6f505493204dec7650932026ec765093204cec7650932005ef7550932005ed7550932006ef6550932006ed655093201def745093201faf7450932007af6450932026ee6450932026ec64509320f7ac645093248faf54509320f7ac5450932007cf735093204dee735093204dec7350932007cc735093201eef635093201fcf63509320f7af4350932007ad43509320f7af4150932487ad4150932487cf3150932487e63150932487cd3150932005ef70509320f7af405093200cfe76d81320e6fa60d813202cfe75d8132004fd75d813202cfc75d8132024fe74d8132004fd74d8132024fc74d813201cfd73d813200cfc73d813204cfd72d813200cfc72d8132004ff71d8132014fe71d8132004fd71d8132014fc71d8132006df31d8132006f631d8132006dd31d81320e6fa30d81320e6fa20d8132006fb10d81320e6f810d8132005f771581320edf471581320e6f8605813247df676d95310def665d95310df7665d95310def465d95310d5f674d9531005f574d95310d5f474d95310077654d95310df7454d953104df673d9531015f573d95311bef763d95311bfd763d95310df7753d95310cdf672d9531005f572d95310cdf472d95310c5f670d9531005f570d95310c5f470d95311bdf775595310077765595310def665595310def465595310df746559531005f77459531007b77459531005b774595310d5f674595310d5f47459531007b474595310d5b4745953145df77359531007d7735953145dd7735953119ef7635953119fd76359531005f772595310cdf672595310cdf472595310df775259531005f770595310c5f670595310c5f470595310df775059531475f676d91310ddf675d9131005f575d91310ddf475d9131006f765d9131006f565d91310d6f664d91310d7b664d91310d6f464d9131007b754d91310d7b454d913104df673d9131015f573d913117ef763d913117fd763d91310d7b743d91310cdf672d9131005f572d91310cdf472d91310c5f670d9131005f570d91310c5f470d9131005f775591310077775591310057775591310ddf675591310ddf475591310077475591310dd747559131006f76559131006f5655913117df77459131007b764591310d6f664591310d6f464591310d7b46459131455f77359131007d77359131455d7735913115ef7635913115fd76359131005f772591310cdf672591310cdf472591310d7b74259131005f770591310c5f670591310c5f470591310d7b74059131005f77655131005f67655131005f57655131005f4765513146df77555131465f774551310dfb754551310d77654551310d77454551310d7b454551310d7345455131005f77355131007d77355131005d7735513104df6735513104df47355131007d4735513104dd47355131
  | 13 => 0x8332024fc745833201cfe735833200cfd735833201cfc735833204eee325833204eed3258332004ff7158332014fe7158332004fd7158332014fc715833204edf315833204ef63158332006dd315833204ef5315833204efb7058332106fa5058332106fa405833204efb305833204ef83058332106fa205833202cfe76d95320fe7e65d9532024fe74d9532004fd74d9532024fc74d95320067e54d95320fe7c54d953201cfd73d95320fe7f53d953204cff72d953204cfd72d95321c67f52d95321c67d52d95321c6ee42d9532004ff71d9532014fe71d9532004fd71d9532014fc71d9532006f631d953200cfe70d9532004fd70d953200cfc70d95320fe7c6559532005bf74595320f5bc74595324addf73595321c4ff75595320067f7559532004ff7459532006bf7459532004bf7459532024fe7459532024fc7459532006bc7459532024bc74595324acff7359532006df73595321a4ff7259532006ef72595321a6ee4259532004ff7159532014fe7159532004fd7159532014fc7159532006f63159532004ff705953200cfe705953200cfc70595320fe7f5059532024fe76d91320f6be64d913202cfe75d9132004fd75d913202cfc75d9132006bf54d91320f6bc54d913201cfd73d91320f6bf43d913204cff72d913204cfd72d9132186ee52d9132186bf42d9132186bd42d9132004ff71d9132014fe71d9132004fd71d9132014fc71d9132006f631d913200cfe70d9132004fd70d913200cfc70d91320057f75591320fd7c75591320f6bc64591324a5df7359132004ff75591320067f75591320047f755913202cfe755913202cfc75591320067c755913202c7c7559132184ff7459132006bf74591324a4ff7359132006df7359132164ff7259132006ef7259132166ee5259132004ff7159132014fe7159132004fd7159132014fc7159132006f63159132004ff705913200cfe705913200cfc70591320f6bf4059132004ff7655132004fe7655132004fd7655132004fc76551320f73c545513201dee725513202cff7654d3201cfe7654d321a4fd7654d3201cfc7654d320067f6554d3202e7c6554d32005bf7454d320f5bc7454d32005ef7254d3201dec7254d32024ff7650d3201cfe7650d32164fd7650d3201cfc7650d320057f7550d320fd7c7550d32006bf6450d32026bc6450d32005ef7250d3201dec7250d3204dec765493202eec765493204cec765493201def755493201f6f75549320076f655493202eee655493202eec65549320ff6c6554932005ef7454932006ef6454932006ed645493249f6e54549320ff6c5454932007cf735493204dee735493204dec7354932007cc735493201eef635493201fcf63549320ff6f53549320076d53549320ff6f51549324976d5154932497cf3154932497e63154932497c
  | 14 => 0x14f6c545494214fac545494214f2c5454942005ef7354942006ef63549421376f53549420076d535494214faf4354942007ad43549421376f51549424b76d515494214faf41549424b7ad41549424b7e631549421376f505494214faf405494200cfe76d8142126fa60d814202cfe75d8142004fd75d814202cfc75d814201cfd74d814200cfc74d8142006bf54d8142346bc54d814204cfe73d8142004fd73d8142346bf43d8142006bd43d8142024fd72d8142256ee32d8142004ff71d8142014fe71d8142004fd71d8142014fc71d8142346bf41d8142006bd41d8142006f631d8142126fa40d8142126fa20d8142005f7715814212df47158142126f8605814204e7f7559732004ff7459732006bf7459732004bf7459732024fe7459732024fc7459732006bc7459732024bc745973211e7f545973201cfe735973201cfc735973204e7e535973204e7c53597321a67f52597321a67d525973204eee325973204eed3259732004ff7159732014fe7159732004fd7159732014fc715973204ef6315973204ef53159732004ff705973200cfe705973200cfc705973211e7f5059732004ff75593320067f75593320047f755933202cfe755933202cfc75593320067c755933202c7c755933204ebf7459332116be545933201cfe735933201cfc735933204ebe435933204ebc4359332166bf4259332166bd425933204eee325933204eed3259332004ff7159332014fe7159332004fd7159332014fc715933204ef6315933204ef53159332004ff705933200cfe705933200cfc7059332116bf4059332004ff765533204cfe7655332004fd765533204cfc765533202e7e65553320067d6555332026be6455332006bd64553321173c54553321def66155332006f77558732006f67558732006f57558732006f47558732006f77458732006f67458732006f57458732006f47458732006f75458732006f65458732006f55458732006f4545873204ef7735873204ef6735873204ef5735873204ef4735873204ef7535873204ef6535873204ef5535873204ef4535873204ef7435873204ef6435873204ef5435873204ef4435873210ef7725873210ef672587320cef5725873210ef472587320cef752587320cef652587320cef552587320cef452587320cef742587320cef642587320cef542587320cef4425873204ef7325873204ef6325873204ef5325873204ef43258732006f77058732006f67058732006f57058732006f47058732006f75058732006f65058732006f45058732006f74058732006f64058732006f4405873204ef7305873204ed7305873204ef6305873204ef5305873204ef430587320cef720587320cef620587320cef520587320cef42058732004ff755833202cfe755833202cfc7558332004ff7458332024fe745
  | 15 => 0xf51d81520067d51d8152006f631d815213efa50d815213efa20d8152005f77158152145f4715815213ef8605815202cfe76d95421367e65d9542025be74d954201dbd74d95421373f54d95421e4fd75d954201cff74d954201cfd74d95424debd74d954201cbd74d95424ee7f54d9542136bf54d95424ee7d54d95424eebc54d954204cfe73d9542004fd73d95421367c53d95424eebf43d9542024ff72d9542024fd72d95424de7f52d95424de7d52d95424deee32d9542004ff71d9542014fe71d9542004fd71d9542014fc71d9542006f631d954200cfe70d9542004fd70d954200cfc70d95421367f50d954202cff76595421367c65595424d5bf745954214f3c54595424e5ef72595424dcff75595420067f75595424d4ff7459542006bf7459542136bf545954214e7e545954214e7c545954214ebc545954214e3c5459542004ff735954204cfc73595421367f535954214ebf43595421e4ff7259542006ef72595421e6ee3259542004ff7159542014fe7159542004fd7159542014fc7159542006f63159542004ff705954200cfe705954200cfc705954204cfe76d8d4202cfe75d8d42004fd75d8d4202cfc75d8d4201cfd74d8d424cede43d8d424cedd43d8d42024fd72d8d424a6ee52d8d424a6df32d8d42004ff71d8d42014fe71d8d42004fd71d8d42014fc71d8d42006f631d8d4200cfe70d8d42004fd70d8d4200cfc70d8d424cebf40d8d42006df6398d420f5ed7298d4212df67198d42005f57198d420057f7558d421357c7558d42115ef7258d421357e7518d420057d7518d4204ede6318d42006dd6318d4212df67118d42005f57118d42125fa7018d42005f97018d42004fe7694d42004fd7694d4204cfc7694d420067f6594d4202e7c6594d42025be7494d42005bd7494d421cf3c5494d4201dee7294d42005ed7294d4212df67194d42005f57194d42004ff7654d42004fe7654d42004fc7654d4202e7e6554d420067d6554d42005bf7454d42025bc7454d421373f5454d4201dee7254d4201dbc7650d4204ebc7650d4201cbc7650d420073f7550d42135be7550d42135bc7550d420073c7550d421353c7550d42006bf6550d42006bd6550d42025bf7350d420279f7350d420079f6350d4204ebe6350d4204ebc6350d420079c6350d420079e5350d420079d5350d42007af7250d4201dbe7250d4201dbc7250d42167ac7250d42026bf6250d42027af6250d42167ae5250d42167ae3250d424c5bf7150d424c5bd7150d424bfb63150d42005bf7050d42025ec765494202eec7654942024ec765494201def755494201f6f75549420076f655494202eee655494202eec65549421376c6554942007af7454942025ee7454942025ec745494214fac745494201eef645494201faf6454942137af545494214f6e5454942
  | 16 => 0x8943004fd71d8943014fc71d8943006f631d894300cfe70d8943004fd70d894300cfc70d8943116bf40d89430057f755894316d7c75589430067f65589430067c6558943166ec625894300cfe76d81430067f65d81430067c65d8143156fa60d814302cfe75d8143004fd75d814302cfc75d814304cfd74d8143024fd73d814301cfe72d8143004fd72d814301cfc72d8143086bf42d8143004ff71d8143014fe71d8143004fd71d8143014fc71d8143006f631d8143156fa40d8143156fa30d81430057f755814316d7c75581430067f65581430067c6558143156f86058143024fe76d915202d7e75d915201d7d75d915214ebe64d915214f3e54d915201cfd75d91524d67d75d915201c7d75d915214e7e54d915214ebe54d9152516bd54d915214e7c54d915204cfe73d9152004fd73d91525167f53d915214ebc43d915202cfd72d91524d6bf42d91524d6ee32d9152004ff71d9152014fe71d9152004fd71d9152014fc71d9152006f631d915200cfe70d9152004fd70d915200cfc70d915214ebf40d915214ebc645915214f3c545915250def725915204cfe76d8d5201cfd75d8d52024fe74d8d52004fd74d8d52024fc74d8d52506de53d8d52506dd53d8d5202cfd72d8d524aeee42d8d524aedf32d8d52004ff71d8d52014fe71d8d52004fd71d8d52014fc71d8d52006f631d8d5200cfe70d8d52004fd70d8d5200cfc70d8d525067f50d8d52006df6398d520fded7298d52145f67198d52005f57198d52005bf7458d5214dbc7458d5211def7258d5214dbe7418d52005bd7418d5204ede6318d52006dd6318d52145f67118d52005f57118d5213dfa7018d52005f97018d5201d7c7654d5204e7c7654d5201c7c7654d520073f7454d5214d7e7454d5214d7c7454d520073c7454d5214d3c7454d520067f6454d5202d7f7354d5202f5f7354d520075f6354d5204e7e6354d5204e7c6354d520075c6354d520076f7254d5201d7e7254d5201d7c7254d521a76c7254d5202e7f6254d5202f6f6254d521a76e4254d521a76e3254d524fd7f7154d524fd7d7154d524f7763154d520057f7054d52004fe7690d52004fd7690d5204cfc7690d5202d7e7590d520057d7590d52006bf6490d52026bc6490d5214f3c5490d520075d5390d5201dee7290d52005ed7290d52145f67190d52005f57190d52004ff7650d52004fe7650d52004fc7650d520057f7550d5202d7c7550d52026be6450d5214f3e5450d520075d5350d5201dee7250d5200cfe76d815213efa60d815201cfd75d815200cfc75d8152024fe74d8152004fd74d8152024fc74d81520067e54d81523a67c54d815204cfe73d8152004fd73d81523a67f53d81520067d53d815202cfd72d8152276ee32d8152004ff71d8152014fe71d8152004fd71d8152014fc71d81523a67
  | 17 => 0x1ce7d41d95431ce7c41d95435467f31d95430067e31d95430067631d95430067d31d95435467c31d95430067f21d95430067e21d95430067d21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95431ce7f40d95431ce7e40d95431ce7d40d95431ce7c40d95435467f30d95430067e30d95435467c30d95430067f20d95430067e20d95430067c20d95430067f10d95430067e10d95430067d10d95430067c10d954316e7c655954353ddf73595431ccff75595430067f75595431acff7459543006bf745954318cbf745954353cff7359543006df7359543004ff725954301cfe725954301cfc7259543004ff7159543014fe7159543004fd7159543014fc7159543006f63159543004ff705954300cfe705954300cfc70595431cd7e761954316e7e76195431cc7e76195435273e741954316f3d74195435367f64195435363f64195435275d73195435267f63195435275f43195435373e43195435373c43195435275c431954316f6e721954316f6d72195430067e62195430067c62195435273f421954316f76711954316f7571195430067f61195430067e61195430067d61195430067c611954300776311954316f7a701954316f7970195430067e60195430067c60195435273f401954304dbc765514302ebc765514304cbc7655143025bf75551430273f75551430073f655514302ebe655514302ebc655514316f3c655514302e3c65551430079f735514304dbe735514304dbc73551430079c7355143026bf63551430279f635514316f3f5355143005bf725514352fb63155143005bf7055143525de7694d4304ede7694d431addd7594d431cf5f6594d4302ede6594d4302edc6594d4316f5c6594d4302e5c6594d4304f9f7494d43025de7494d4304ddc7494d4304f9c7494d4304edf6494d4304f9f6494d431cf5e5494d431cf9e5494d431cf1e5494d4316f9d5494d431cf5c5494d431cf9f4294d4304fd67194d4304fd57194d431cf9f4094d4302cff7654d43024fe7654d431acfd7654d43024fc7654d430067f6554d4302e7c6554d43005bf7454d43025bc7454d430073d5454d4304f5c5354d4304f9c4354d4351fd63154d43025dc7654d4302edc7654d43024dc7654d4304ddf7554d4304f5f7554d430075f6554d4302ede6554d4302edc6554d4316f5c6554d430079f7454d43025de7454d43025dc7454d431af9c7454d4304edf6454d4304f9f6454d431af5f5454d431af9e5454d431af5d5454d4316f9d5454d430071d5454d4316f5f5254d431af9f4254d4316f5f5054d431af9f4054d4301cfe76d89430067f65d89430067c65d8943166ee62d894302cfe75d8943004fd75d894302cfc75d894304cfd74d8943024fd73d8943166ee42d8943166ee32d8943004ff71d8943014fe71d
  | 18 => 0xe4258a4304eef3258a4304eec3258a43004ff7158a43014fe7158a43004fd7158a43014fc7158a4304ef63158a4304ef53158a43004ff7058a4300cfe7058a4300cfc7058a43186ef2058a43006f77558643006f67558643006f57558643006f4755864317ef7745864317ef674586430d6f5745864317ef474586430d6f754586430d6f654586430d6f554586430d6f4545864304ef7735864304ef6735864304ef5735864304ef4735864304ef7535864304ef6535864304ef5535864304ef4535864304ef7435864304ef6435864304ef5435864304ef44358643006f77258643006f67258643006f57258643006f47258643006f75258643006f65258643006f452586430d6f742586430d6f642586430d6f542586430d6f4425864304ef7325864304ef6325864304ef5325864304ef43258643006f77058643006f67058643006f57058643006f47058643006f75058643006f65058643006f450586430d6f740586430d6f640586430d6f540586430d6f4405864304ef7305864304ef6305864304ef5305864304ef43058643006f72058643006f62058643006f42058643004ff755824302cfe755824302cfc7558243006bf5458243066bc545824304cfe735824304cfc735824304ebf435824304ebd4358243004ff725824301cfe725824301cfc7258243004ff7158243014fe7158243004fd7158243014fc715824304ef6315824304ef5315824304efb7058243176fa5058243176fa405824304efb305824304ef83058243176fa205824302cfe76d954316e7e65d954304cff74d954304cfd74d95431ce7f54d95431ce7d54d9543024fd73d954316e7f53d954301cfe72d9543004fd72d954301cfc72d954316e7f52d95430067e52d954316e7c52d9543004ff71d9543014fe71d9543004fd71d9543014fc71d954316e7f51d95430067e51d95430067d51d954316e7c51d9543006f631d954300cfe70d9543004fd70d954300cfc70d954316e7f50d95430067e50d954316e7c50d95435257e76d954302c7e76d95435473f74d95431cf3c74d95431cf5f73d95431cf5f43d95435473e43d95435473c43d95431cf5c43d95430067e62d95430067c62d95431cf3f42d95430067f61d95430067e61d95430067d61d95430067c61d95430077631d95430067e60d95430067c60d95431cf3f40d95435467f74d95431ce7e74d95431ce7d74d95431ce7c74d95431ce7f73d95435467e73d95431ce7d73d95435467c73d95431ce7f43d95435467e43d95435467c43d95430067f72d95430067e72d95430067d72d95430067c72d95431ce7f42d95431ce7e42d95431ce7d42d95431ce7c42d95435467f32d95430067e32d95435467c32d95430067f71d95430067e71d95430067d71d95430067c71d95431ce7f41d95431ce7e41d9543
  | 19 => 0x9153566bf30d9153006be30d9153566bc30d9153006bf20d9153006be20d9153006bc20d9153006bf10d9153006be10d9153006bd10d9153006bc10d91531aebc645915355ddf735915318dbe76191531aebe76191531af3e75191531af3d7519153536bf65191535363f65191531af9d731915353ebf631915354f9f53191535373e53191535373c531915354f9c53191531afae72191531afad7219153006be6219153006bc621915354f3f52191531afb671191531afb57119153006bf6119153006be6119153006bd6119153006bc6119153007b631191531afba70191531afb97019153006be6019153006bc601915354f3f501915304d7c76551530267c765515304c7c765515302d7f745515302f3f74551530073f64551530267e64551530267c64551531af3c64551530263c64551530075f735515304d7e735515304d7c73551530075c735515302e7f635515302f5f63551531af3f43551530057f72551535577631551530057f705515301cfe76d8953006bf64d8953006bc64d89531a6ee62d895304cfd75d8953024fe74d8953004fd74d8953024fc74d895302cfd73d89531a6ee52d89531a6ee32d8953004ff71d8953014fe71d8953004fd71d8953014fc71d8953006f631d895300cfe70d8953004fd70d895300cfc70d895311e7f50d8953005bf74589531adbc7458953006bf6458953006bc64589531a6ec625895300cfe76d8153006bf64d8153006bc64d8153196fa60d815304cfd75d8153024fe74d8153004fd74d8153024fc74d815302cfd73d815301cfe72d8153004fd72d815301cfc72d815308e7f52d8153004ff71d8153014fe71d8153004fd71d8153014fc71d8153006f631d8153196fa50d8153196fa30d8153005bf74581531adbc7458153006bf6458153006bc6458153196f8605815304e7f755964318ebf74596431ae7f545964318ebf545964318e3f54596431ae7d54596431aebc545964304cfe735964304cfc735964304e7e535964304e7c535964304ebf435964304ebd4359643004ff725964301cfe725964301cfc725964318e7f5259643004ff7159643014fe7159643004fd7159643014fc715964304ef6315964304ef53159643004ff705964300cfe705964300cfc705964318e7f505964304ddf7654e4354edf7654e4304f5f7554e4304f5f6554e4302ede6554e4304edc6554e4304f5c6554e4318f9f7454e43025de7454e43025dc7454e431af9c7454e430259c7454e431af5f5454e4318f9f5454e4318f1f5454e431af5d5454e431af9c5454e4318f5f5254e4304fd66154e4304fd56154e4318f5f5054e43004ff7558a4302cfe7558a4302cfc7558a43006bf5458a430f6bc5458a4304cfe7358a4304cfc7358a4304ebf4358a4304ebd4358a4304eef7258a43186ee5258a43186e
  | 20 => 0x6f77458653006f67458653006f57458653006f474586530def754586530def654586530def554586530def4545865304ef7735865304ef6735865304ef5735865304ef4735865304ef7535865304ef6535865304ef5535865304ef4535865304ef7435865304ef6435865304ef5435865304ef44358653006f77258653006f67258653006f57258653006f472586530def752586530def652586530def552586530def45258653006f74258653006f64258653006f4425865304ef7325865304ef6325865304ef5325865304ef43258653006f77058653006f67058653006f57058653006f470586530def750586530def650586530def550586530def45058653006f74058653006f64058653006f4405865304ef7305865304ef6305865304ef5305865304ef43058653006f72058653006f62058653006f42058653004ff7458253024fe7458253024fc74582530067e545825306e7c545825304cfe735825304cfc735825304e7f535825304e7d5358253004ff725825301cfe725825301cfc7258253004ff7158253014fe7158253004fd7158253014fc715825304ef6315825304ef5315825304efb70582531b6fa50582531b6fa405825304efb305825304ef830582531b6fa2058253024fe76d91531aebe64d915304cfd75d91531aebe54d915318ebd54d915302cfd73d91531aebf43d915301cfe72d9153004fd72d915301cfc72d91531aebf42d9153006be42d91531aebc42d9153004ff71d9153014fe71d9153004fd71d9153014fc71d91531aebf41d9153006be41d9153006bd41d91531aebc41d9153006f631d915300cfe70d9153004fd70d915300cfc70d91531aebf40d9153006be40d91531aebc40d91531adbe76d9153024be76d91535673f75d915318f3c75d915318f9f73d915318f9f53d91535673e53d91535673c53d915318f9c53d9153006be62d9153006bc62d915318f3f52d9153006bf61d9153006be61d9153006bd61d9153006bc61d9153007b631d9153006be60d9153006bc60d915318f3f50d9153566bf75d91531aebe75d915318ebc75d915318ebf73d9153566be73d915318ebd73d9153566bc73d915318ebf53d9153566be53d9153566bc53d9153006bf72d9153006be72d9153006bd72d9153006bc72d915318ebf52d915318ebe52d915318ebd52d915318ebc52d9153566bf32d9153006be32d9153566bc32d9153006bf71d9153006be71d9153006bd71d9153006bc71d915318ebf51d915318ebe51d915318ebd51d915318ebc51d9153566bf31d9153006be31d9153006b631d9153006bd31d9153566bc31d9153006bf21d9153006be21d9153006bd21d9153006bc21d9153006bf70d9153006be70d9153006bd70d9153006bc70d915318ebf50d915318ebe50d915318ebd50d915318ebc50d
  | 21 => 0x60000020000000000005000400a0000038014002018006801400000000980040040040058000008000002800402800400200140060030020060006004002800c0000140160004002001002800000801000000040340000000000018001000800000e0030010000002000007000400200000000040040010010010004000000000001c001003800c0040000010020012006000000000000e0028028002004001800400c00204cfe76d8d5453f3c54d8d54024fd75d8d5402cfd74d8d5455ede53d8d5453ede43d8d5401cfe72d8d54004fd72d8d5401cfc72d8d54004ff71d8d54014fe71d8d54004fd71d8d54014fc71d8d54006df31d8d54006f631d8d54006dd31d8d5400cfe70d8d54004fd70d8d5400cfc70d8d545467f6598d54566bf6498d541cf3c5498d54006df6398d541ddf67198d54005f57198d541af3c5458d545467f6518d54566bf6418d545273c5418d5404ede6318d54006dd6318d541e5ee7218d54005ed7218d541ddf67118d54005f57118d541d5fa7018d54005f97018d5401cfe76d89544e73c54d89541e6ee62d8954024fd75d895402cfd74d895450ebf54d89544e67e54d89544e67c54d89544e6bc54d89544e63c54d895404cfe73d8954004fd73d895450e7f53d89544e6bf43d89541e6ee52d89541e6ee42d8954004ff71d8954014fe71d8954004fd71d8954014fc71d8954006f631d895400cfe70d8954004fd70d895400cfc70d895414f3c54589541e6ec625895400cfe76d815437f3c54d81541d6fa60d8154024fd75d815402cfd74d81543cebf54d815437e7e54d815437e7c54d815437ebc54d815437e3c54d815404cfe73d8154004fd73d81543ce7f53d815437ebf43d815401cfe72d8154004fd72d815401cfc72d8154004ff71d8154014fe71d8154004fd71d8154014fc71d8154006f631d81541d6fa50d81541d6fa40d81540bf3c54581541d6f8605815404ebf74592531ce7e54592531cebe54592531ce3e545925316ebd54592531ce7c545925304cfe735925304cfc735925304e7f535925304e7d535925304ebe435925304ebc4359253004ff725925301cfe725925301cfc72592531cebf4259253004ff7159253014fe7159253004fd7159253014fc715925304ef6315925304ef53159253004ff705925300cfe705925300cfc70592531cebf4059253004ff7458a53024fe7458a53024fc7458a530067e5458a530fe7c5458a5304cfe7358a5304cfc7358a5304e7f5358a5304e7d5358a5304eef7258a531c6ee5258a531c6ee4258a5304eef3258a5304eec3258a53004ff7158a53014fe7158a53004fd7158a53014fc7158a5304ef63158a5304ef53158a53004ff7058a5300cfe7058a5300cfc7058a531c6ef2058a531bef775586531bef675586530def575586531bef47558653
  | 22 => 0x300380040040020000084030000000802000000700580000000050008000020016000000400e00c004000c0040000018008008012005000000800200880080320040000020018002000000000c0010000004000006003800c0000000008010008009004800000400000480300020000008004004000002800400c007003007400001a00000340060020018000000002000000000200500680100180000010008072001000000000601100100140220030000004000004002001401400a0018000006000011001001c00000e0000004001000000800000d0058004014000000000000200100080040060000018004004009000000801000300180080260000000020002002000800000000f001809c0100070008018000003000003801000d003000c008000000800c00a000009004c00000a0000024000002004800c0040020018048008001016801003c0000008044018001006801800c0000050000010016000800c0020010028008002002000000c01c003001001c00000300180040000020008000000021007800000200a000000c00200100000400040080078000008001001800001000100100040000010078010004005004800c00c003000005c000001002803001400a000802000000400280000080000000000000000000000c022000003000000800e006000001400100400200560000008000006000003000001400a003000001600400000000040070030008000000000000801000200180000020050000034000006000000c000002000804c00200300600280040060010004018005005800000600c00100240000050038004004003001000800c0010028000010000000000c00a00a0010030000000000000400000f0098000000001009001000e000004800400000700c002400604a0000000000009000009c002000001000400400200280000000000008018006000001800001200300000000260000000008000003001000800000700000400000050018044010005003801000400000400600120010038008002000011800000a000000001000000000480000160000080000000007000002801a00b000001c00000e000000400a0010040014002003002800000a000004001c00e00e000003800e001001002403c00100780040800030030020000009000000800201000100000060050028028002002000002000c00a001001000000c0020008000000002000800000d0008000004000002000800201d0020004034004000800000600201300000140000038000002000001000400200d000806400200000080040020000028000008000001000c002001000800400400c000800000000100a000005800d00380000280040030060002000011801c000004004004c002000000800000000000080000040000048004000003002802
  | 23 => 0x79dd17200000000000dc43413cc031c3620cc00038500005cb5a10c61646cda39b929cc50a5e0000000000000691a4344ce6b95dd3009cc852273e3339c32c6a575305dcd0cdd11537a54982b841da258be88ef00000011244d83d0ba00f9cb112a680000001435a9800104800032f100843849400000000000000000000000c7b26a81c9ab42581832fcd53018e0498bf80ce2eb0001f6000034e0003181b38cc644eb2e45100006cf1c5800000016a8444418e010000000cec9d9000079561468949a0006002011802c002001008801c02200d001800801c00d0028018000001000001c010004004008c04c00000500b8006000002001000000100280140100000000074008004000000000200e0098018022000003000000e0020010000000003000800000c00100180040020010038014050003008000000400600a8000010001000800000200300380000020030018018006015001800401000000000040020090190014004000003001000601500180080020020000000000000002000001800100200040020080020024000023001001c00a000001005800a009002800802200400080540060020020044000000000800400000800000200040170018030002000000805c00a0040008020000001005002801c0140058000002010008000000400000580080100000068010004001001800000a0000018000000002005802402e00100580280020030000004012000001001001600000c80000a20020060004006000001000c00000100080400040040000014000019000803c0000000008000000005000003c02e00000900000000050038038006007008006c004002000000400e00a000001c00000000080000020180038004008003000000000e00600580000060150088038004009000005c02800000000000120030010024000004001000000c0000000000006002000004400000b000000401001a000000c0080000000064006001000000000c01f000000c06a001000001000000e001803000a0030000014002000000001c000000000801000e00f004003c00200200000000000010000000004004000002000200500080200000090018048000005000000000000100e001c0040000000000000008009000001200d003000400003100000240060000018008014000001000800402a00780040020000048008024001006800000000900500240080010080008004000000002c004000004000000000800180000080040000008000001000008c00000100100080080000018000018000002004800000400000140000040018010008001001000400a00d010000000400100100140060070000010006008001001c00200600c8028002004012802402a00500000100000000010000030003000001001c0010000010000005000002400001
  | 24 => 0x8455f00025a8000a540f30000000968707b595452ce7518814cd969cc3c438600002483818d8cb0e06459f12f1abca8a73b8000eda9260189e9c00027712c89c00009f3000192c344b394591d886060006e72a8173465b2242cb403a15d000316800035e53016d599e1675049f1400057c00017b133246c00002a400092f31123059c2ac81be80013a4d2b2d190880f275f6b9b9743a66b769786902f6e1a3781bfd5de6a7000209c00030a5deaa24000000441a1ec00000000009886324f33c280000000005d0a409a7aca664315a00000002beb0d830a7a22bd28185405fd5abaf447a825b328b658ee01cf399034c218dd00aba1b5cc20914b810ecc24a7100000000003ef000202d1d62af0432b9c00020200030b80006a910f9ed5bc22b03883894a5470619a29b03d600071e1a0d9ec33f00004e02468570002518000ad050c21700000003b90000380000680232c7ae1f446e1e100007ed5a9292c5ae69e5690569d1046033738e9882d3500027a42a80593bba260674c041b2a73ce8a7bf6fdaa3c8ce000000000126087429a000085449160000009ded2000013dd4fa4010001130296c9200000000000004218554214bc50b32bb06c04351bd0379b8ce46000381800053336ab8a85ac00050084d138c00019b2d39396c886eb00b400000016080010d8df900011240000006570001300e711ae90981682d113a000026a1a74ab8528f1cd1a116af68038a376d1a86869a0fa000143c0006150002a5059439b5f210348baaa23f11d289a8000716800180661700025ec0001590002644000000291a83893636e2d92fa109816a46110910187ca539235d3de5ed52117499ae20a0a89414dde0002ea04ed8a0168568acc9d081642898001d04b1e43b346c18a0220250a4d9e28095e135d05209105db9678fae4c74d3923883e9b96d9a29d262c3853b0f34da464d081b1a4b8608a3218f89b34cb41cd03ec758caf5d221f8c5cc162050115c56c5d00018a890c000000364971ac8e00025f4000000692b6802b03e52e40c84000ab563880000100c100007b4a946be4898ba0000c6b4ab271048a5803868000d320001a9a93c55074e6399845bcab13000036160c5ae30f9a51620542653898c0000000002da8000080000084088400026500000000000000ae455219200036254c46d10000001a9847b042000031855e1c29560e3029510d16ad3fe6632820291942d5009ba41c98214d4462ff8f24e873562bc4e92b975518000a825d0621810170c5ff23796ec4461414acafb4c2655052c00016d06862b5abd8000e2c0000a60000b4600021798d0cfe00007c4638a3365c018d9629bd15f26240007aa73d0000000b085533518b1ad6715a89a800071f01b205dcf274c02080546da87800035e52fe00002e24896dc0005822fdd4443685d
  | 25 => 0xfe000000000054300010300000000bb4cea20d0f19e1c000d294652350b2046e00000019ded621caaf2161c09a56c1b1c1806ce00033b0000e7b1180fe00004ec3512d8c62c51a6fa26bdc1c00028c97d518e1dd00017147e800000000000000000003654000dfd59137bdb7cc8d6e18018a7c0000a22a5497200000000012ba0000002495adacb000000000006f625d30504425310f731641b447e29838b8340e631cf2b5487c1950d5000080065814124751c629d4aa27e0bf400000000001c616e2900001054bd80000b0c714e2928610dc4700000000000000000012b4b000027600034dc0000003f61c2179c6e32090a159a0d3a5b98000c6c0001de80001be00061e92dc0000004110d1c604e2060080018f88df0001ea59dc96d000000000069d606a6517a888d00012bd68006f6899a28eb637864d0001602b365fa0e80312c820000000000c1e53784211a48fb10b1c4400007e7418000b301153fe8475662c0b3cf0001cca3b454400014b800066aa8b43e4dec52da67927e0c357da070ac2a5d0d81f04940a514a7a2295063992d41b018780004f080005960000000000000ceb60611a471edf640415949f681062f1ec15640000000001022000472000186000042080003723d100000003d4d325ae31c800000000035e94fec8b0002ef01fc9000001b9400057700000009c00000002069b84000495adfdbf00af6c30ba507868c422082000086926328f46b40000e719ac65e5d52b78000cb41f71d38b153f4e3465114e93b4af7223900cbac0001e780000007172dc8000fa23df0000000f223fe000028424249271aa1480004780000ab985628a126b4b547400000032cdb4243f4c9b0994f0a6551c9f9d358dee3e1a8900006656c5a5a400000000011a906e6d74c22280f48e396d3b66d3fc0003760000d3600016781d0c6e4d200034840002ad22836f08cc04b00000015080001c6ac31a043db000000000076e00000013a8a6756980003d859766dad9c000cd36d41f99408bfd0000000c7e23963d2855d124210002f48b165ee305355507c1720001024000e0824510780007af50280015c21da5551f24db43ee6298320000bf6340b3b4000a6d0531fa80fee5c4ee835156291f00013318ac00053e20052e472d0380b4c0006b30000de5b9e7804a996a40000dd00016744ac0000000000ae06b40000001880ca945d8000000000297a3d5a8203b40ab1d853e0005c228c0000c830000ce00000994fb13b5bae0bd3e30ee4ffeba755e8000c7054e4fc84618763960ed9dd80268454f899919e4851313b7454247570001a39a44a976781880240cf35409c14f2c7d65b8887566693a00000019127136c7805800043a30833200004430e530d400000047a000091000000000012361b40000000bb20005a28000bae4680b8a6089
  | 26 => 0x364e554620d5500a7397378000058d34000000071600000000005ea00031a9f90ac6823000000432e4580ffa11cc76ce94a08001cd836744b90c80b6e3e019030800019810296080000000002fecc82a0a00003880001fd2f0398000000027505f43ae579000181856e9a52f52168000e733b8b9b4154c943a42b6d72277f48a17c47d0dc70022968d9ab5e6211210ecab0358286d5ce4a6417533715fca2339f9ee52c60005ce92c035824f737099085817c257000155c7a51fd8a24d041af1e19be5a9ad646a7b1440000ff323370163600072791e47d82913ab236c000a6b5e796a989e8e751a82049dc4312d09d2c1acdc96619e69be619625686a13742603eab9a4ede7ab36c1c903700000000000000c6f0000000cba0000000fe80000000000000a880000002efc0000000002c9172602100000000fa45f537000000045900000000008462e500000041b738624052a20e82b98f8dc3c48164e9b581101df36080014f659f719a0280000000001a4cc980000003084000bd62a9b58cad2c4b264000000000000000017a68b100031380000001330001c420002fb92c96de92905d364038600041705098f24ab006800085a00051c0c50000a6915a2ad80008cd15b177d7dc3c01210000d5e59a00000014a000021598514002793d928ec0ccadf70e105800047f5412ab157879d189b0fc89c6e81c4af049fcccd40f269800050e33026dd5942170b0028843000014623e00003fd58d1f94cb251c17d09c8cf822e00029d47044d30000c6cba2e582880000000860000000000000048f0001ca80001288000000b8c00000004da0dc5bd9a4000053735038098ce23f01c940c0002811f538fd7de00029e198483ac99274ba380f66dd331186dbe22c42a38dbca5684b6ec293800000000012b038473125c34553163ce4599b98000e006e52a78124a9164f0f606fe93807a0ce453213c065ad30b9c3c26bf89f06b2db60000000eeaca303b0258f5ce781562884c6800053f08d0f502bd172a8440000002102fe8bde73300014b0000b9500021288b614f5059458000d7d1200238e4a60e5b680019ea4b1303a00d712c7700d21bc00000000035b07fe1070001b9c46a3eb00035c52ca54900001ac0004bd19337143b025721b13106e80001120e01a920006a280014280f804e80000008a130e26a4a7000035c0ec8342b6b0000000000d190002d50ce462d3ef800000006c3fdb3ed756e3b00000019503755ddb78141039f02e9ce9b30e0939e19246d24292c7942407e58a22691d00001bb40915ed8a8e04000334431a8d90000c48c660002d780000000005950000f980000000000b360004b7a3fc0006d00b60000aa85f8082b9004aa9b51d4341097c8fa2f580011fa6261afa13807a70700b91843ac1c600000000000003878e845ba8e63
  | 27 => 0x31e0000d7490f0d9000139a18350622d853c8140000d5813671200000001e234600025348160000001e30d220005ce3364000d77000321400044a000240c0000000881475c1abb805c355857800036c8000000dae523b2040000000c3253800090468880000008ec44880012ee6500000d6ccda00031f0000000000260065000032b0002b0c3f600030eab3955e0000002d5933690c00000009a05e1014b4f922ea4a0c3800057e0003b520d51200000001e240000002f1a3a000000059c07e00000000001fada1634537e00005b4000125000053489f35819b10c213a00024441406042138001032b850ec8001144c570001d8c0a41c800000ac888e5f00024f966a3000002b740000e013aad807c000026d37e9b5a0000002c3c00021b0000001550000403b7f89ac0000001a98dbc0000002915b48ac11eeaa6cfb8c660fc8710554000000164cb440004f58000cac0005490f1c00065345b84a00000000000000032ae651f047c0009e315301440005000002d686c458838481840000000000000000669000039cafc0000000254eaa8da00027c88660000001ef4ecc15c0e90800b8e0004ee0000000000000375000000064535c9768170318800cfd20000002468b800002dc21b80006cc4d81d7800047d54e1bcd7bcc9c5fa80000000002522b5800080e20d32f800065f493a7f5468a170002cfc00000000027c0e520004dd9a609cc000211800076a80d42c1c6d2b053f552a0b40000000001030000ba85a19b7d0720001508000b2800000000016cc0464679b216008c60000a10b7ad8c08a275894a012000000180addf3058240cf2d1f000000000000065da9a00002c666f000192c3204bc04c966e3302d391d4f8e6ea5962c2ccce0002ba8000b980a52d336956f03da1b0b6f522a7b405d8000f667266360a8c9300000003328d8854f50e9768000cc13440000000000000000173219a49da3249184a2242aaa4df48944798f14ce8ada6ee0a9040caff3aea0a0c589212e1316d9080503a38ea44a4000607a80d8e84e306d8a895267ef00000000003916143735aba8882f90c047920000001724a04a2f43982c4e4024c0000000000000393800000004d214149419c0005a880013820006c40ccc5c4000000000109200045e0cf8a5a9c200008807d2e4b00020e9c8a3324fa903c9c4721000257000093d3a880010a870100036e4d7602a0d283a8e282364390e3144e0003ad0000000d120000000000b580001f508b8a8500029982722316179ef0000bfc02d19fcb387fe0b08d98496be73a19f6c4fea1625a0b31bba9d55f286ac66e0000002b2c0da317267107110e0001bb1bdc000000000000125a7860000ecd302e5e00000008d600000005fc0002220000dc4000a55000000161235800011917b2bae0002ecd64aabe6148d2d
  | 28 => 0xc000e48000396d7ae31e50da618000781339920955a821562800000000001e18144b8b4b29eb260e3843c31589189a23722ee878530e5786930000bd27e30000000e5476b044800000000068b800000054c000188518600000025111d4c1533e9a3cca8b1c4f52e498eaa0f07a82d935c0000003959a8e48f000057c00000038d029c28a2e7112ab3c2c6b8b167021400024463f000070c6ee00020740000004280d44398ae012098e45e232925a9445b02c701a600001fa4a34670b84000de76188b248ec0a300038c995400073a00000000334c9382c00017372b9cd97d89c831235f06d405e30c043568200068e043904a0830000001a84a251c200000000002d81fc87905e40000e040000000000001b6e000000010d7fee166c280bc0008336dab2f4000a412bf99012dcc255d00000000d0d14680000004a15f30000aec0001c825f13386aa0001c380000005622a85b76b160c82addc061c736a18bd3f83d05791575a28b9645705ddd1ab5b32918c114c00017c3898fa4e3711e222563287a085afa888a000147054d0e28af708191d5d61242c6000187c7e81a48001150666075abd05de8ac0fd11483786571d2a42d0269830070001786b8a672127c0000001d5054800000068405adaa800008d8001b98db4703937419a062338027c3d20005b48000000000220355d95a1751ec96592726ed02408dcee613620db360ed8b765bbabe52fc13349710200008d10002fac00000000000010ce000000318d6f40004aab4300000b367a2490b4aae40cf2459888b59545a6a0e6a0053e6995464431d1a1a9e954e0a864037c023406e1bbb67d16ac094cc00000001560f237f12e8182683a5cc0001696a70bc137c85b462a03da6200017625e8000906000054061e9355efa63c00030b0000824c4600037200016e4b6218701312cc3b16a22df59929fb262ab50dea48d7261fd0ef8b651f80001890bc46a91a480004545249f79320cab0c9aa30f4cad970d8cd417e761000127059ac5c080883911688200008e844c00001a376825c00000010396fc00000000010709ec0000354c06ba32ad9eb000023e18808a47cecd25b60000b2ab2849e15000000003e220f4bec9e0000311d0009b30e5a52902c48943ab74910228617196d035239d4f2a74d7b673069c28acde899526fb844b122785d50c54dfcd532c1ba3090ecc4433137053620b1fc800000000031d07400002871c40000000cc500009516408e2543b57185a42e6c88000a6ada630b000000000000000011900000000f3130a12c3910000ef40000398000d6400000000017aa00019e8000476bdd34ab4ed31c6443211d4804e0e505e19a8de20000001cd000074f0001a7c72800047917e5736dba5f92c5593e1c567e8e5c00072f4cb8001b00a8e5908b900000005be115499a3ae
  | 29 => 0x3cd800177c8e54870000e8c0000001f080001b66e080019d0dff6bb28d946480445c0a48d50df21ea91c03c426c4ad9e5510010f3b3ab5da3000073f39d800000000012005b60002833309b040000fa9278000719000000011aaf0579955400001144a80016ba4f60ee23f0e5c000684800106000000017791f20000000bec0000752db325dbda0000000000df63e44cd24b025e11904c2c5d6aa9885b08b712b44d75308000000000000000000000000025013eec6d60402c8c02937094800176ace60cf9644e50d6972907cdb1c72c41a00000005480f035a80008620ef37898feb8f3c68b4880ad481842a400880f94fa090cc1a58e3e4251daead5859d8001bc62fc73e8000e84e8a08f0384d2c5e643f86cce8214c60c8fcc6120000000e0d09ad666ea821c27a26e720980017c3875221018efc15e3a22809758be23f880405000821dd8518000000680b8757c2000637002569accc55c21f1b1434a014287123000000000004fa12700000000000000002fe45a83283d69aac0eedeb00000000000001e5800054e000000144819e10401800011bc0001918520fee3ed0bf14851ec9d83190000000c131f90028c7a51b6602294aac0000002680aa47d90bc15991549b833423c4ce202427a9809706ab30911ec597417a314891d478c1d5fc29a9ae0b4f6479568ace52969206fc9e24105ba80000000005141d640003d25e521acec0e5a198a81c00066f04f1c2dc0a00028402d407c227000149ca3e3480989fd83f839c1eb1a14e4629460880001561090000000e9a82600030400008f03fc80003aa7996d594989f48863f80000bb805659e000000022b0000000000aab4329ac4314e4a611331c000000209ae0938a00030d3938d7e91952fa9d0bd0d3f02f8cec374b021f3179400000033daec1146ac01e230b06d62b268500006580006b08b81cd60fc02c2e60aa240700011941d200067d14b8000049101800090600037008459c6ba50001e7cef04aa43c9e7183ea1f1458000c101300000539b5800000000010c8de622f00012ea00035180dcfea32a28b800006a00012e8001480cb60e0832537e7b628a31e000014900000000000c671b1b840000001ab8000c1ed600003a055d2ce01ee1da579a00000030d173e4fd561307000e9bc3f03290622b2e0000154eb8497000098425400025d883cc9418f367abe88c4a0d20c8001bd000000015b00000000000e880000004b20000ea09c74d69cec4be9ce60d00000000000000fd4a7200009f8000000199248323068000000000016be37c12f06b4a1a8f740f8b64e70e5035ab04803e01b33d12a1b2649d57714559f080264392cd47e02e1529a68464a8070aa5217c03445959ab58fa2ff00020acae2d7e44da3751600e403485897a0586494015c00000007987f8ef678a593a24
  | 30 => 0x82e5b31968b6000016d499932d34422f00001f033a0007182238000d99000000000000037580000005072de0ef13148a436d8efcd4adc45f494edd0cb1225b045c0000006a0365176425073323605660000692878000af808b1f74ac4bdc2c9349dc14a775e311c80000181b808cc00000000003d892ac614901055a94a521a132f00003ab1e331255c42125c7234c52eb79403126978088f442ae50f76b9e652911963e56a000094d080d6b610115953a89c57e33f015a0006b781a80007680000dcdc440006bc34a8c4ac27000000000019b30611687820006c1a93400000068e8d4180c1790c016140008686c680000007642eda541254c621c990d1c70e236072ea4b622d032295b40001e85e5b87c5384f020200000000005dc80985620000b2b2fd6907e147094d9a0627139580000000003611c09c7a1137428ed915a228324011d67a70061c947800090a273955d9d4e426a880005bc0b003000007ec0006ac80000000004f680000002144102524f2e5cd0003790f468ba4b0800076e17403d28649f2ac63e9a2d12ecbb60f80db1668000427a52c74c9db62a92fd2465fc5a39460ea8000352166520a1020d7290c5be0003400000000000000000000065c342338907e23d1cc12a4ab8d0e6c380011520233d01691172e590df0df813816f18621a97625fe47f2eb5a501e742c8c9dba62f723e0a59a8667e239a70000000005b939400000000039c01aed6e5b209f80000000000000000e170001f2d6607c03e800004d0c4544d0000000ae5571800000000000000013863054c680000009e2000000000000f12d0000e2a0000001060b82dea0688001b0800047490f40000006dc2f25b6403856e35a0000c2300024d80004f42743131bea000648ab300d018818d13e1c4800000003658ca00000032b00000000059a1c000bf133b80000005ac095b26cf1e12d369a89996e1bd220800093264f270b17dc86b1d1ef268c00061e0002965392000442160411e8420002bf41289795a22ca49fe2c2000000000000066b0000de4832217b28117ac0a3bc99380008770000c9492cb4a0000001a72932509b134ff40000002918f703ba1fe04488c6b2f7141cf964c7ee1379491c8eb884f41b0dccec1b26f28a86b82f42ba2354000000173356c0008ee00000000000000d3136c000ddb07780000000001fb800161a000275800163020473f9e0c000a2e0adb8bdaf60204f300000001d100001e09c88bf0000ebc00000054fb8301dc00038500000001cd00007d9c9a00061d0001198b812e2377820ce7519216b40006dc35b081d88c0002e3061065c04e4ce8bc9628ab44d59325052176038a0d8000c320000b210a69526d82e9800027b6830000000a480002aec00043000017608ae00000030dc0009ca6999a5db7e71e00003c887000
  | 31 => 0x55900000008a295f682aae50be7b7141a159b2e7f81d1b848bc45bf27e1f6800000064a887952cd360e4abd4000307000000049c3b838eb4b9a78a630002dd157e2ab4b3b240a8ae2716015b882279326c80000a8c332b20be52380004e88eb52c48c0163b57c15837b0002790000c184d08d910e060900a0231926269364b4c09e446d3820d4861a9093468c7d4ae68b0a3a9cc402acd4cb0e389162f341636c5b900972df10e4f16cff2128bf53aedaa28089ad9ee584225974c748a560ea384d70e0000570995ca600067ca7415d00000002e0003c0007458000a640000c5b1900001254188a3c0005720001f3d8942ee33c25acdfa56022997c03deb073f9a34000095e1a7ad25a2ce6268f152d9be8be0000000a14000076a94d35454653cb09128a2bb0001ba40cabe33652bb443200036283b103694372491dcdf021555800e824c3e150800000000f055d39440003ca68780011da00053800017e09b4238924d0aacb55522264000e3107bb6896e0a8d285913d3627944db022cbcee6a00625b01720ca6fb8bd9b52d104a60000f046a1431ace8000bcc2619af1b9654343ea7781a0ce51f8a58034682f0001a706785a000017ec0009a4000277c0000003be97cc00085d2679b19bb200023d1ef823800008025c40008d644f04f8000cd45a82b1d2246bd00008b17448484a10310b9edaf00009258b0c07455a88000000000039102809080000000d5c0000001ee80000006151cf494c35454d0f4cea6d9d3a00108000a2c30ca67c4e65ba2db8c118a4a996590000eb05284c62b7809e00015d332c00021300000013dc0e600000011c07900c0b52c0003be0c88e493ceac913d000033800020a2f1c76000000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc76851d931480018eb0a3b262900032da10764c5200065ac20ec98a4000cd5831d931480019cd043b2629000339608764c5200066b990ec98a4000ce6321d931480019aa643b262900033ca00764c52000678c00ec98a4000cd7301d931480019e4603b26290003354c0764c52000679900ec98a4000ce6201d931480019c8403b262900033c080764c52000670100ec98a401aab684d95314800156b09b2a6290026b5a0f654c5200056ac1eca98a40008f78759531480011e90eb2a629006e9da17644c5200053ac2ec898a4009ad683d9131480015ab07b2262900023de1d644c5200047a43ac898a40028f487d8d31481655ab0d31a6290003359da634c5200066a3b4c698a40b2bc58298d31480a97a30131a6290203f0082634c5200047bc3ac698a40028f48758d314800d3a90eb1a6290026b5e19634c5200066a3b2c698a40b3bc78258d31480bb7a700b1a62901f3f0081634c5200066bc3ac698a4002ad68758d31480055a90eb1a62900033521d634c5200146a43ac698a40b3ad78258d3148001d8f04b1a62902cab5e01634c52000769c02c698a4018ae4865c931480019c8ecb9262902c6f1e0d724c5200c5f0402e498a4009ae4864c931480019c8ec9926290062f8201324c5203e7e11826498a4009ec7864c93148013d890c9926290003b1dd9324c520006e33b26498a4000dc4764c93148001d88ec9926290003b1d95324c52000762b2a6498a4000ec7644c93148001d8ac89926290003f0e01324c5203e7e04026498a407cfc2704c93148033d8ec09926290067f0d81324c5200cd78432e098a4000cf0765c131481617a706b826290066f8209704c520006f0b92e098a4000fc1325c1314800157309b2a60900263e21d654c1200053cc2ec898240098f88759130480017a30231a609000e7aa1f724c12000cf443a649824001ae8864c930480079d0ec9926090027b218d324c12056fe118a649824001bc8874c93048007b910e99260900067221d324c12000de5432649824001bc8864c93048013d910c9926090027b2dd9324c12001ee53b2649824003dc8764c93048013d90ec9926090003b2d95324c12000764b2a649824000ecb644c93048001d92c899260902bef2e05324c12057de4c0a6498240aedcb714c9304815db92e299260902b7f0185324c12020e783b6c29824041de072d853048001f8265b0a6090002bc219314c12004e783b2629824019de0724c530480a9f846498a6090003f04c9314c12000769c32629824000bd2864c530480017a10c98a6090003b4219314c12004f69bb2629824009ed0764c53048001da6ca98a6090003b4595314c12000769b22629824000ed1644c530480a9f850498a6090003f0609314c120007e1b92629824054fc0724c53048031da6c498a6090063f0d89314c120
  | 1 => 0xb06308c69010b395c86118d205ae78b80c231a40b4ee02018463480051e9033b4a6900023de057694d200147a40aed29a40018ec865ca53480033d100b94a6900023d2197194d20006f0102e329a40038f8865c253480073d104b84a69000a3da077654d200047ac0eeca9a40048be849d9534800117b093b2a6900022fe117654d200245e422eca9a40008f7815d953480051e902bb2a6900261f21d6554d200061e3a2caa9a4009a5c835955348001968c3ba2a6900036a0837454d200147a40ced21a40008f7815da43480051e902bb486900063b2197290d2000cf4402e521a40008f4865c64348001bc040b8c869000e3e2197090d2001cf4412e121a40028f681dd943480011eb03bb286900161fa167650d200043ec2ceca1a400087f855d9434800b0f90abb286900023de057650d200147a40aeca1a4000c7461dd54348001ad041baa86900262f21d6450d200061e3aac8a1a4009a9c83591434800155b09b2a64900263b21d654c92000536c2ec899240098ec87591324800178b0231a64900067aa1f704c9200055b426cbb0a4000ab584d9761480011eb0f32ec2900023de1d65d85200053b42ec9b0a4000a7585d9361480011eb0f326c2900023de1d64d8520006f0102e7b0a4000cd573d8f61480011eb0f31ec2900023de1d63d85200347ac38c7b0a4000a768518f61480014eb0a31ec290002ada1063d85200055ac20c7b0a4000cd57318f61480815c90c996c290102f820132d85200055b426ebb0a4000ab584dd761480014ed0bba6c2900029d61774d85200047b438a9b0a40008f5871536148001c6aa82a6c290002b5a0c54d85200056ac18a9b0a4041ae68215361480015cb042a6c290102bca0054d852000578c00a9b0a4000cd7739cf61480014ed0a39ec2900029d61473d85200055b420e7b0a4000ab5841cf61480835cd0439ec290102b960873d852020579400e7b0a4041af1801cf61480011ed0f29ec2900023d61e53d85200055bc22a7b0a4000ab48454f61480011ed0e29ec2900023d61c53d85200055b420a7b0a4000ab58414f61480835cd0429ec290002b960853d852020579400a7b0a4000af18014f61480011ed0f21ec2900023d61e43d85200053bc2a87b0a4000a748550f61480011ed0e21ec2900023d61c43d85200053b42887b0a4000a758510f61480835cd0421ec290002b960843d85202057940087b0a4000af18010f6148001dc041bb262900023da1a764c520006f0104ec98a4000ad5839d931480011eb073b262900033560e764c5200066b994ec98a4000cd5329d931480019ae613b26290003354c2764c5200056bc1aec98a4000ae7825d931480015e700bb2629000378080764c5200dd3b428ec98a4000a75851d9314803556d083b26290002ad610764c52000770100ec98a4000
  | 2 => 0x931541302b7a9a9a62a826000f51534c5504c001ba70e98aa0980037421d315413004ee93b262a826009dd0764c5504c0adea50a98aa098003d461531541300c6e9baa62a826018f53754c5504c001ea6ca98aa09815bd41953154130006e9ba262a8260c0f52544c5504c0adea0a898aa09800374dc931541302b7a9a9262a826000f51524c5504c00337309baa80980263e219755013029e9c2a2eaa026004aba84d95404c17fc70a9b2a80980123e21d6550130005e4c10e6a026000bd1811cd404c0033710ea1a80980272e1d9435013028d9c42a86a026009d987350d404c0017a3039928098003e2509325013004e783b262a026055f93434c5404c001f228698a809800374e1d3150130006e843a62a026009dd2764c5404c013ba0ec98a809800374dd53150130006e8baa62a026055f92844c5404c001f230898a809806374dd131501300c7c9ba262a026000f93644c5404c0abf20c898a80982fbe4d5131501302afc82a262a026000dd3724c5404c0abf268498a8098003e45093150130006d4102e9b2a4000cb674187654800196ae830eca90002b560c61d95205ef70100c3b2a40048bf875d3654800195c64ba6ca900032e8c174d95200245f426e3b2a40008bd84dc7654817996ce918eca900032d5d231d9520006f0106e2b2a4000ad5831856548177dc04030aca900028fa1375595200147b43ee2b2a40008f583dc565480011ed0e38aca9000a1f21d51595200047b43c62b2a40028f4878c56548001ad040baec8900031d9d461d91200063aba8c3b224000ad5831876448175dc04030ec8900161fe1d75d912000637192ebb224000c7a305d7644800b0fd0bb8ec8900021f61771d91205ce3b3ac63b224000c75758c76448001bc041b8ac890002b560c61591205c770100c2b224000a3e85dd164480051ed0fb8ac8900023d60f71591200047b438e2b2240028bc8750564480011ed0f18ac89000a3d21e31591200061e2a6ecaa240028f681dd954480011eb03bb2a8900021f61676551200045ec24ecaa24000c3c545d954480011bf06bb2a8900263720d76551200047bc0aecaa240028f4815d954480011ef02baec69000a3d20575d8d200047bc0ae9b1a40028f4815d363480015ab0638ec690003780817198d200056ac18c331a40b7ee02018663480051ed0db8ac6901023d21b7158d20006f0106e2b1a40b7ce772185634816d9e6e030ac69000a3da1f7158d2000477c12e2b1a40008fb805c563480011ed0e38ac69000339dc87158d200166a38e62b1a40028dc874c563480031f50fb82c6900033c1c77058d20006b4102ea31a4000da8205d063480011bf0eb18c6900273598d7118d200066ab1ae231a4000de0205c463480018ecea308c6900031d5d46118d200065b3a0c231a4000cb57418463480015a
  | 3 => 0x498e6009ec78258931cc001d8ee4b126398317b11c9624c73062f63292c498e60c5ec64258931cc0f9d8e40b126398003b1589524c73000762b128498e6000c3d74953654c0014f3012a6ca980122fa1f74595300061fba8e8b2a60008bf845c5654c00917908b8aca980023be09715953001c76412e2b2a6000cb7748c5654c179968e918aca980030f5d754d91300055cc06a9b22600587e87dd5644c001878ebba2c8980021fe15715913002c3e42ae2b2260008ef825c5644c0071d904b8ac8980031ddd631591305ce3a3ac62b226000c3c549d9544c0010ff0abb2a8980022fe1176551300061e2a0ecaa26000c3c74d95534c001878ebb2286980022fe1175d89300245e422ebb12600087f855d3624c00b0f90aba6c49800b359c531d89302a76210a63b126000ec531887624c0070f90eb2aa4980a68f211655493001c5e43ac8a126026a3c85591424c001ba700b8e64980037420171cc93004e6bb02e39926009dd3605c7324c001ba4a0b8e64980037490171cc9302a6e9102e39926054dd1205c7324c0315ab07b2a6298002ade11654c5300d55a422ca98a6018ad583d91314c0014ef0ab22629806e9d215644c5300c56a432a698a601be546554d314c00172f08a9a6298156e5211534c5300c56a4328698a6000b578550d314c0ad6a90aa1a629806ba5191434c5300c56ac1ec498a6009ad483d89314c0315a90c9926298003b1d89324c53001579436e098a6018bd080dd5314c0015af0cbaa6298062b5219754c530005cbc22ea98a6055b94845d5314c0017a700baa6298062f4201754c5306272a32aca98a6000b9784595314c0ab72908b2a6298002f4e01654c5300c5e8406e898a6000ad7865d1314c0315a90cba26298002d5e15744c5302b5aa42ae898a6000bd3805d1314c0317a100ba26298002d5e15644c5302b5aa42ac898a60c3e9464591314c0017a700b226298002b5e19544c5300056a432a898a6055f1454551314c0317a500aa26298062f4203724c530007e1106e498a6000ad7865c9314c0315a90cb926298153711c9724c530005e9c02e498a6018bd0805c9314c1075ad0fb126298086b521f624c53000763b96c498a60c2ec472d89314c0135ab01b126298203b1c83624c530054ea43ac498a6000bd380589314c0317a500a926298062f4a01424c5300c5e943ee098a6018dd287dc1314c0137a50db826298026f421b704c5300c6e93b6e098a6018dd076dc1314c0017a30bb826298002f4613704c530005e8c16e098a6000dd372dc1314c001ba2e5b8262980065e617745413002d3d42ec8a8260c1e3854d91504c00b1f10eb22a098002f26087354130005e8c08e6a8260019788754d504c0138f0eca9aa09814ece211535413004eac39aa6a826000bd181cc9504c001e92a4992a0980273c1d
  | 4 => 0x2500091f301b8ec4a000e1fa1f655494000c5f436e8a9280049ac87549425004dc58caa9284a00021fe1576cc94002c3e42aed99280018bc865d332500292790aba664a00263e21970cc94000c5e432e8992801493c855d132500015ab073b262a00029de15764c5400dd3a42aec98a8000ad7835d931500015cf04bb262a0066b9209764c5400c55ac26ca98a80c8e345459531500015af06b2a62a0026b520d654c5400c55a432e898a8065b34855d1315018f72f06ba262a0026ad219434c54032d9a42a8698a8009e946350d31500315690ca1262a0002f4603324c5400cf633126498a8000f85424c9315018d6750bba2a0a005ece21153541400a59c42a86a828000f195350d505000b8f0eca92a0a005ece21152541400265c3b284a828014b38855095050001e52a4a12a0a006b3c1d9315414038f982a262a8280048be87dd165cc15996c63ba2cb982b32d4c774597305665d186e8b2e60accb930dd165cc14d87eea3a2cb980022fe1171597300245e422e2b2e600587e87dd564cc1518ec63baac9982a31d4c775593305463d186eab2660a8c7930dd564cc14d87ee83aac9980021fe15715933002c3e42ae2b2660a887f855d954cc15917f08bb2a9980261f21d65553300251e422caaa660098bc8759154cc00b4790ab22a99800b359c53158b300045fc22eca9660048bc845d952cc0070f90eb2aa5980a68f2116554b3004c7643ac4a96600087f855d942cc00b0f90abb2859800e2f21d6450b301351e42ac8a1660098ec8758942cc00156f08baac398002ad21175587300053bc2ae8b0e6000a74855d161cc0011ed0e2a2c3980023d61c54587300071aaa0a8b0e6009ad68315161cc0015ab062a2c398002b9a08545873000572c10a8b0e6018af28015161cc0015e3002a2c398026b5a0e72587303156ac1ce4b0e6000af3805c961cc0315e100b92c3980029da1472587300053ac28e4b0e6000ab6841c961cc00156b08392c398026b5a0c72587300756ac18e4b0e6000ce5721c961cc0315e500392c398002bc60072587300055b424a4b0e6000ab58494961cc0135ad07292c398002b560e525873004d6b418a4b0e6000ad58314961cc0014ed0b212c3980029d616425873004d6b41c84b0e6000ad58390961cc0135ad06212c398002b560c425873004d6bc1264b0e6009ec7824c961cc001d8ee4992c398003b11c932587300076329264b0e6000ec5524c961cc001d8c84992c398003b150932587303e76390264b0e607cec5204c961cc0015af0cbaa6398002e5e11754c7302f5ca422ea98e6000ad7865d131cc0016af0aba2639817ed5215744c7300056bc32a898e6009ad48655131cc0bde28a8aa26398002b5e19724c7302eee2392e498e6000bd3805c931cc0317a100b926398002b5a1d624c7302ed6a43ac
  | 5 => 0x88267520d72d81310c47ac3ec5b026200ee020d8b604c4011ef0eb16c098867391c962d81310c578402c5b0262009d687ccb604c4017a301996c09883a7521d32d81310cee239265b026200ec7624cb604c4017a700996c098802f460f20d813100770b1641b026200fc132c83604c59bda0c1b9ac09886679a1f7258131006e3b9ee4b026200ee060dc9604c401b8f07b92c09880339d8f7258131006e3b1ee4b026200dc730dc9604c401b8a61b92c09880339dd87258131006e3b98e4b026200ee0601c9604c4011ed0fb12c098867391cb62581310c578406c4b026200ee220d89604c4311e90eb12c098867391c962581310c578402c4b0262009d687cc9604c401b8ee5992c098867711cb32581314076830664b0262009d6874c9604c4333a90e992c09880371dc932581310cee239264b026200ec7624c9604c4f9da0c0992c098862bca1b6058131666e9b9ec0b026200de072d81604c4030fb0bb8ec8a80ff1d5d631d91500047bc0ae5b1aa0028f4815cb63540011bf0eb18c6a805e4fa1f7454d505661e3b6e8a9aa0a6c3f761d1535414d878ec3a2a6a829a1fa1f6454d500be1e3a6c8a9aa000b1d8418d5354001a70e9b82a6a80061f2197590d500061ebaec921aa017b1c8454e4354001c3ec8a9c86a80263e2197090d5060e9c2a2e121aa00587c851d9435400187ca83b286a80061fa1b7550d5002cae43aa6a1aa00387c855d36254001878a8ba6c4a80028f21153d895002c7cc06e3b12a00187e86dd5425400717d0fb2284a80165b21d525095014f16322a4a12a0008bf845db325400917908bb664a80061f21975cc9500bc9e422eb992a0098f8865c332540030f90cbaa64a805e4f211754c9500056ac1cec98aa000ab7845d9315403556908bb262a8002b5e0d764c55000573c12ec98aa019ae4825d931540314e90cbaa62a81c6cd211754c55065dabc1aea98aa018a7585d9131540134e90ca9a62a81c6cd211534c55004f2a31aa698aa018a748654931540017a30199262a8067b1989324c550007a2a926498aa0018bd84dc7655007f96ae918ecaa005e8fa1774595400061e2a6e4b2a80cae34548c56550193c70a9b82caa00023de0572d8d400147a40ae5b1a80008df8758c63500031790cba4a6a00030fd957494d4004c7c432e129a80bfd38545c25350009179083b2a6a00030fd507654d4004c3e43acaa9a8017c3c74595535000317d0dba2a6a00066ea037454d405249f43eeaa1a80a8c3c76dd54350001a70e1baa86a029b0fdd87550d405361e3b0eaa1a80a68be87d954350029878ebb2a86a00262f21d6550d400a61e3aacaa1a8000b1d8518d4350029a38eb29a86a000387d965350d40024ce43aa6a1a8000e1d6554d4350001a70ebb8286a000e2f21175d89400061e2a2ebb128000a3c8550f6
  | 6 => 0xccbac2ee8a9262099748754d524c51166908a9aa498827551cd5354931004eac1eeca126200977855d9424c4372e90abb2849880275e0d7650931004f9c02eca1262189f0805d9424c43336b09baa8498a234d1517550931004ebc1aeaa1262099d4835d5424c4333690eb228498a16cd2156450931685cbc1ac8a1262099b48750d424c50b6690aa1a8498827651cd43509310d4f243aa4a126288f2454549424c4013af0eb2e6498802e5e1165cc93140dca422cb99262009d787593324c4016af0ab266498a0ad521564cc931004ebc3aa999262099d487553324c503e28a8aa66498ace7521970cc93104ee9c02e19926280dd0605c3324c501ba4a0b866498a037490170cc931406e9102e199262199d583dd5324c40136f08baa649886a6d211754c9310cceac1ee89926200977855d1324c4372e90aba264988667521d534c9310deaa3aaa69926200b978454d324c4fb72908a9a64988667521d434c931005abc2a86992627eb548550d324c435b28e8a1a64988267921d524c9313f7a3a9aa49926200f4553549324c4133c90ea1264989f7e1d0d424c931007c2a1a8499262199d583dc1324c4133a907b8264989fb551d5754c931005cbc22ea992627db94845d5324c40178f04baa6498866f120b654c931004ebc3aca99262199d487595324c40172f08b2a64989f6e5211654c931005e3c12ca9926219bc482595324c4016af0aba264989fad5215744c9313eeca3a2e89926200bc7825d1324c43378905b22649880275e1d644c9310ccea43ac89926200b5785591324c4fd6a90ab226498802f1e09644c9310cde2412c899262009d787551324c4013a90eaa264989f7c5151544c9310cde3412a89926209bc687d89324c4137890fb126498866f1a1b624c9310cf63436c49926219ec776d89324c433d88edb126498802f1617624c931005e2c26c49926200bc580d89324c41378d0ea926498826f121d524c931005e3432a49926200bc486549324c43378f0aa926498867d1e15524c931007a3baaa4992627ef4475549324c4fde8ccaa926498803d1595524c931005e3c22a499262cff4654549324c4fde88a8a926498802f1e01524c9313f7a3a82a49926209bc687509324c4137890ea126498802f1a19424c931005e2432849926200bc785509324c40178b0aa126498866f1e11424c9310cfc3c22849926200f8774509324c4fbf08e8a1264989f7e1991424c931007c2b228499262cef8754509324c4fbf08a8a126498802f1e01424c9313efc3a028499262609d686dc1324c4133ab05b8264989f374183704c9313e6e9106e0992621dad4865c1324c40136f08baec09886a6d21175d813145cebc1aebb0262099d4835d7604c4012ef0aba6c09886e5d21574d8131454ebc1ae9b0262099d4835d3604c4ff3af06b96c09
  | 7 => 0x2c54d91524c80b1d90eb22a499002f16047354932005e4c00e6a92640396c8754d524c8138d8eca9aa49924ecb211535493204ea639aa6a9264039ad84dd5424c8131d90cbaa849924f4b151755093202557426caa1264dbe2c54d95424c8091d90eb2a8499002f16047350932005e4c00e6a1264039ac8750d424c813958eca1a8499246cb215435093204ec639a86a1264008bf845d7604c80917908baec0990021fe1574d813202c3e42ae9b026402cd6714c7604c965da02098ec099003b44c710d81320053ac34a9b2a6200d3574953654c43536d0fba2ca988032dd8f7459531006cbb1ee8b2a6200d37751d1654c5b5aaeebb9aca9880365dd37359531006ca3a6e6b2a621a8f587d97644c401c68a9b2ec89886aad21165d91310055ac36a9b226200d3575d53644c4372ed0fbaac8988031dd8f7559131006abb1eeab22621bc7475d95644c4351e90eb2ac8988034d1d76459131006abbaee6b226200d5475dcd644c5b3b2ee9b9ac8988027560f76551310069a2a4ecaa26200977855d9544c40136f08bb2a89880275e0d76551310069a2a0ecaa262099d687dcd544c5b1e28a9b9aa89880a75a1b7355131014ea436e6aa262009d582dcd544c4013ab01b9aa898aa355dd47355131566cbba0e6aa262d4f14541cd544c40178b0439aa898802f460073551316be9a2a6e4aa262d6d3454dc1544c401a68e9b2aa698826d5a0f6554d31534db43ee8a9a62acf1453dd1534c55996ec7ba2a69880365d8f7454d31566cb996e8a9a62acd9730dd1534c54da6eea3a2a698b5765dcc7454d315378a298e8a9a620997487551534c435a68e8aa2a698826d520d5454d31534bb43eeaa1a62a8f1443dd5434c5518eec7baa869880355d8f7550d31546ab996eaa1a62a8d5730dd5434c55936f08baa8698b5675e0d7550d31544bb438eaa1a62a6d37741d5434c5a9aaee63aa8698a9bc510c7550d310069a3aec8a1a6209b9683d91434c4133690eaa2869886f4d1d55450d3104dca41aa8a1a621a9d48754d434c437aa8eaa9a869886ae52115350d310078aaa2a6a1a62009b7845d7624c43536908baec498a2e75e0d75d893104cea41aebb126200977855d3624c4372e90aba6c498a2a75e0d74d893104cea41ae9b12627b9d7835c3624c4133a906b86c498802f160e20d893169f62316e6b126219ae686d89624c5a5b8ee7b12c4988627ca1f7058931006e9b9ee0b126200ee062dc1624c401ba707b82c4988033cd8f7058931006e9b1ee0b126200dd332dc1624c401ba265b82c4988033cdd87058931006e9b98e0b126200de3721c1624c401dc0c4382c4988027560f7654931004dbc22eca92621a9b4845d9524c4013af06bb2a4988027ce0176549310c4f8402eca92621997487595524c51166908b2aa498b46d5e0d65549310
  | 8 => 0xa8b9486a90030f9507650d5201c3f436eaa1aa40396e82dd5435480b2b90ea9a86a90061f21574d81520061e2a2e9b02a400a3c8454f605480b1db05b8ec0a900e2f61371d95427065aba463b2a8429a3e85dd165509bfc58a9b92caa137b8d15231595420061e2a6e0b2a84008f7815c363508051e902b86c6a100237e1d6318d4201c5e432e929a8400c3f655d253508131d90cb94a6a136f4b1517294d420061faa0eca9a840987c875955350853878e8b2aa6a100e2fa1b7454d4201cd7416e8a9a84a493e87dd54350951878edbaa86a10034b1cb7550d425361fbb0eaa1a84a6c3c761d5435094d17d0fb2a86a109b0f1d76550d4204c5e43acaa1a8426c3c75595435080163b0a31a86a109b471d65350d420070fb2ca6a1a840499c8754d4350801c3acaa9a86a10034b1d77250d426ed9742ee8a928429b2c8454d525084d6590aa1aa4a1003c354d435494200c5e422ebb028400c3c545d760508014790aa1ec0a10123b60b71d81420245f43ee8b2e64accae32dd165cc95995a65ba2cb992b32d8c774597325665a98ee8b2e64a6c3f751d165cc80117f08b8acb990122f211715973202c3f43eeab2664a8c6e32dd564cc9518da65baac9992a31d8c775593325463a98eeab2664a6c3f741d564cc8010ff0ab8ac9990161f21571593325443fc2aecaa664ac8bf845d954cc8130f90eb2aa9990128f211655533204c5e43ac8aa66405a3c8559154cc80156f08baac399002ad21175587320053bc2ae8b0e6400a74855d161cc8011ed0e2a2c3990023d61c54587320071aaa0a8b0e6409ad68315161cc8015ab062a2c399066b9a08545873200572c10a8b0e6400af28015161cc8015e3002a2c399026b5a0e70587322cd6ac1ce0b0e6400ae7825c161cc8335c904b82c3990029da1470587320053ac28e0b0e6400ab6841c161cc80156b08382c399026b5a0c705873210d6ac18e0b0e6421ae6821c161cc8015cb04382c3990033c5c070587320055b424a0b0e6400ab58494161cc8135ad07282c399002b560e505873204d6b418a0b0e6400ad58314161cc8014ed0b202c3990029d616405873204d6b41c80b0e6400ad58390161cc8135ad06202c399002b560c40587320166b38a62b066400c3d74953654c8014db052a6ca990122fa1f74595320061fba8e8b2a64008bf845c5654c80917908b8aca990023ee01715953200c7c402e2b2a6400cb7748c5654c979968e918aca990030f5d754d913200556c16a9b22640587e87dd5644c801878ebba2c8990021fe15715913202c3e42ae2b2264008fb805c5644c8031f100b8ac8990031ddd631591325ce3a3ac62b226400c3c549d9544c8010ff0abb2a8990022fe1176551320061e2a0ecaa26400c3c74d95534c801878ebb22869900e5b617745493202d3742ec8a9264dce
  | 9 => 0x75586430055bc22eab0c861aab4845d56190c015e700b92c321802bc20172586430053b428e4b0c8600a75851c96190c5f56d08392c321802ad610725864304d6b418e4b0c862fad5831c96190c019cae4392c321802bca00725864300578c00e4b0c861aab6849496190c0156b09292c321826b5a0c52586430056ac18a4b0c8600ae7825c16190c015c904b82c3218029da1470586430053ac28e0b0c862fab6841c16190c0156b08382c321826b5a0c705864317d6ac18e0b0c8600ae6821c16190c015cb04382c3218033c5c070586430d55b424a0b0c8600ab5849416190c135ad06282c321802b560c50586430047b43840b0c86008f5870816190c014ed0a102c3218029d61420586430d55b42040b0c8600ab5840816190c135ad06102c321802b560c20586430061e2a6eab0486008ef825c56090c071d904b8ac1218028f61252d95430143fc3aa3b2a8600a3d849436550d4d8eced18ecaa18031bdca72d95431cd1f420e5b2a86a8a3d841cb6550c010fd0e10ecaa18021f61c21d95431cd1f42043b2a8600a3d840876550d514bd0610ecaa18029760c21d95430053d40043b2a8600a79800876550c7347d08386caa1aa28f61070d95430043f43841b2a860087d870836550c7347d08106caa18028f61020d95435452f41841b2a8600a5d830836550c014ed02106caa18029d60420d95430043f43821b2a860087d870436550c7347d08086caa18028f61010d95435452f41821b2a8600a5d830436550c014dd04086caa18029b60810d95430043fc2ae2b2a86008bf845c56550c0147b09310caa18021f61e61195430051ec24c232a86d4a5d839846550c010ff0eb08caa18028fe1161195435371bb246232a8600a3d849806550c0b47d0db2aa8a1aa30f1db65551435468fba8e6aa286a1c3c65dc95450cf3878cbb82a8a18e70f1d36554d4318e1e32ee8a9a860993c875515350c134790caa2a6a18130f1d95454d4304d8e41aa8a9a86e1f16315515350c738b8edb2aa6a18d7271db7454d4304d8e43aa8a9a8604d1c875515350c1363d0caa2a6a1826c72195454d4302f0e432a8a9a8605e1f765515350c09a3cecaa2a6a1813471d95454d4302f0e3b2a8a9a8604c1c765515350c0163f04aa2a6a1802c7e015454d435261e3a0cbb12860087e87d956250c010fd0e32ac4a1a930f1d065d81435443e436eab02860087e87d956050c010fd0e32ac0a180e1f61771d91527063abac63b22a4008f7815c363548051e902b86c6a900237e1d6318d5214c9f43ee8a9aa4acc3c76dd15354801a58e5ba2a6a929b0fdd87454d525361e3b0e8a9aa4a687e87d915354853878e9b22a6a9002c76106354d52006963a6e4a9aa40387c865d6435480187aebb2486a90a6c72115390d520070fb22a721aa4098ec865ca43549b9a58
  | 10 => 0x80000180080000380180300200080000080000000000001180100f80300180000080080000000500000380000200100000080000300400080000080500000100080480180000000300000200a37e1d31d8d540069a2a2e331aa800cd7635c663550139a8c6b8cc6aa00237e1d6318d545452fc2ac631aa8aca9f8458c63551518decab90c6aa2b32bd917218d54006962a2e431aa800d34545c463551518f6cab80c6aa2b32ed917018d540069c2a2e031aa8018fa80dc762550011f301b8ec4aa39b8d15231d89540061e2a2e1b12a800c3c545cb60550071dd05b8ec0aa0023b60b71d815472f1a2a463b02a800c3c54dd16294c011f700b8ac5298063e2017158a5304d6b41ce8b0ca6e4ad5839d16194c014ef0aba2c32986e9d215745865300579c02e4b0ca600af0805c96194c6f4ed0a392c3298029d61472586530055b420e4b0ca600ab5841c96194c135ad06392c3298deb560c725865300672b90e4b0ca600af2801c96194c015e300392c32986e9da1642586530053ac2c84b0ca609ad6831096194c015ab06212c329802b9e09705865300572412e0b0ca637a76851c16194c014eb0a382c329802ada1070586530055ac20e0b0ca609ad6831c16194c6f5ab06382c329802b9a08705865300572c10e0b0ca600cf1701c16194c374ed0b202c3298029d616405865304d6b41880b0ca600ad5831016194c011ed0e102c3298023d61c20586530dd3b42840b0ca600a75850816194c0156d08102c329802ad610205865304d6b41840b0ca600ad5830816194c01878a9ba2c1298023be09715825301c76412e2b04a600a3d8590b6454c0517f0ea0ec8a98028f61640d91535365b3b463b22a600caf729cb6454c6347d0a396c8a9ab28f61472d91530045f43843b22a6008bd870876454c6347d0a10ec8a98028f61421d91535654f41843b22a600a9d830876454c015750010ec8a9802ae60021d91530065db84e1b22a631a3e851c36454d5947b0a386c8a98022fa1c20d91530045ec3841b22a631a3e850836454c0147b0a106c8a9ab2a7a0c20d91530054ec1841b22a600ab6810836454c0156b02106c8a98022fa1c10d91530045ec3821b22a631a3e850436454c0147b0a086c8a9ab2a7a0c10d91530054ec1821b22a600aae820436454c0155b04086c8a98028f61662191530045ec3cc2322a600a3d859846454dc753b07308c8a98022fe1d61191530051fc2ac2322a6a6e37658c46454c0147b0b300c8a98128fa1b64551535661e3b6c8aa2a6acd1f741cd5454d39878c9b92a8a99bf0f19370551534e61e3a8c9b12a6008be87d916254c0117d0e322c4a99bf0f1d464d81535645e436e8b02a6008be87d916054c0117d0e322c0a98030f1537558a430047dc02e2b1486018f8805c56290c135ad073aac321b8ab560e
  | 11 => 0xc0001084310121b95e95b433702a5be4f318216b16e1fa1991bc3c72c800044900057800034451021c2881695760041a93bd42203f29411a0000ad1094c90005250410334671bf5c100040005e36230345a00000026a0001704ac00000000050e0900000000000000001663913750d13851134d857e0001d53a839033f17500009105121428329a36d4a825824300e53b2510004e806327f1795870000fe0380005b106f1e70004982a500022507e0b913546d38430a00000000010a0000000b358415a0001850000000000000002a40c421f3184cc36122948b5df5bf06600044000000041400754400000042b3540000003ab57443300001a3d45b55ce2090d20e40000000000005a033b1e208b00039d3920000003692414704780000000c70005173db1ce1d847c51d25555f1210005a94573e200000000000029c48156d0001af0002ba5ea49a09d1f600000048f57244f2b000000000300100080100100180000000580000000000000280000000000780e00100000180100100000000880000300000180400000080000580000a00181480080100000000000000280300000080400100001880000080180000501080000080380180500180000300700c80080100580100080000280000000000000280000000000380680100080000000080100000080580000080280100100000000200000300580e00400000600080280380000180000000200300000100000800280180280000000300200000000000000100280600180580000280700381480380180000300180000400380200000000000080000000080100600380200000000280780080000000080780080000000000280280a00680980280000e00100000280000080200000100000300000000400480300280000100800000080380000000580080000500180000500200280100200000000200000000080000600100100000000500000080100000180000080000100000d80100680000000680000200200180080000000000080100000180300280000080100100000d00280100100600000000100000200000100200000480080800180000280600100200080180180000200000780680000400080080580200000000480300300200000400300000080500100000800400180000000080200300000500180180000000080000180000380300500080100080100080000200000c00080000000380000100000000200580000600280101100000000080000500000080300200000100000180000000200000380080380200200c80000200000000180000180280200100000200080080200000080000000080001480280180080500101580100380000080080180080080180180500a00080500280000500000000080100100080700080480100000a8068030000000018010000000
  | 12 => 0xf301326149c2d90a500921903a10150206d2ed0002cc0000000000000002780000000005a600000002700040f0004440830003310001984df30c24d4a42371d142900017b52700006a0000000002ce20150b00000000027e30f0001340005a543c00000000025d41600000000025431141b0001e83221734b01333f62562da06e22b4234b34010005b900000000039a05a00000000000047f0003c924e4415d631958c32b0245360005410af51500024621a5702bf2d400058b1ba56c0002c203700000000046c2804135de35e4a03b20df09a5492525061245820265501dc14f26341137800037a47442737d44500000044a5c500000040728911e00038900000100049d44219c42c00000011654f49606550815404a00004013f0000000003ff0031b74aa1db5833162c30000001b20004e355900000000040815d0001b42021940003be3dc39911118625e3b500012b00008d24715e0b000054242f0003c450f22c1c93065660001cf2e75600bc00011d0560002dd32722d55b44c0b85263af14a5050230215910000781025d230b2f035141d2752f14580294843dd3590e70c11e52c43b14ee46b12c5e24830885850762170f146500040200045c0001425310000000003f32a836a2361950000005e11ac3d823b0282b94564ad3533d14e60d900035200055a3da2bc32820a23a32a0000b53d23655e04b50000000001c80000e00972d107315b5c700000000000000034d0000003df0000005530002b10000003ea2c00001284bf3583f050300036731e0000b10002083331884d00002cf45d3d548200037f3d62e200032f00004f0000000a01033a440d0d50000000001f52af0f80522ec5b80000005933ae01f27d59719d3b713b1e32f449500000000040400000039c1460002fd0004662053150314a244d1045c21141470d03420253ef03c0000000000840000000000002ee00000044b10d51633612700d00014818318d09c3e13350000ed5220003e343435f34135b4a700005048a1ee0000430000a71fc0000004ed0002cd0fa0985cb00014540b51a39f3f71e91384f024a14c00023c0320001fd0492ea0ce0000002594525d000000044e0000000003e800026f0004f43950000000005cf3880004c52a329b0000001f301641053013700000000030018e0000000005670000eb4860005c64283071df1d355759e4ef2b84051ca3c24fc5924a35aa1ef3c629221500c0001d000031f0000000000004b900000027a46800000000029e0005210005560000000000002ac57f0ee0000000003605ca0002f700f1642e60000001812f83fb0000005d30003134ae00053300055e00000052f28600033402b5295391c728434601d0000001f45d72f220f0002d300038f0540da3b80005d500007d1f73c51ab07a3e54d40000bd00016f31737
  | 13 => 0x2157a00000000042d0000000000001d70003435c34bb0721554154db1f108f00041c4623ed0a45282a04ff0005964893090894cd5005e34eb1534ca00037e0822b65ad28a5982a13470ca2c64600c90003d34bc2421d60001875e83bb00000010e25a0000004f653800009e0590003d900008a1e155400026b0003964f54d917a0003e72675b02b709600006031c00605d2f548c4b200041916000000000000000045f3862181394c733e0704f205c2ab3cc30811c11f54608628e2a702f27001c4371180000000003252161594900a90f25b759a32c4af0670004d10005811b51710005943f900038300013e2952264d634f4355da23f0000004f80990712641975a30fc5a143b1431f200043d0000001a403d0000002334e40fd2060004884de2aa3d728d47b00000000035c07c0000003b600000000005b21d0000001c00004fd0194e900017f0b649e0001b00005555bb1190000002eb0004c10cd3202ad0000e100000052c0c600033c4185ae35631d0224c458900000034a2e04595904170393e62625bc38204600039e56a25000054d00000000038c0000002812f31a11063f11d92f600000000000000000019f0005dc05700000053500000000002e0001a50000004a50003142b35e72e51440000005474870003ce1294d50004ea0000004730000e238124c41f00000000000023400031252317c5791eb10c59558d2312852211a72383c859c15131a3d02db4f10d80001ea49100016c3f454b00020300000020e05815204e0644c30003644e50003a00003730003450450001dd36b0001da51400016343229000000000043918c4430000004480005580005d859d18a32458030d04b0002fe52d4dd0020484e23500004cf0aa37016101848d5b30cc11200019e00000025c15f0000000000002d00001490d72721893231b32c13870000003cf38b1154241d44720680004a10002602d80000003380004b83cd0000000000000d607900000000000000049729100015600000051e4470002b420d2b50005115ec1c354837449333a0d40000000fb0de2933a55610530800944be0000000004360000000000000e355d46e0003ba00042a0002485653301225513102651074942a625b46953c15800001750912327300000000028200001e0000000000005af1a00004fe03536656e10f13d04c1100470000001500000000e80000b200000056b0000000000ef48e00012e1300c83572e857b34827750a52421318f29838d3e05e64e012f5bd3a20001c43725cc00047507400059b5770140001c64a61570000000a32d21e01250000001b104253a34002c0003a70005200005373aa54007549b5883a12271625195b22b21325681e600036c0001f90000002764761bb26e00000014d0000000000000004b70000000920000000001ed4e11410ec
  | 14 => 0x1a81805862be0b70004d300013a3ac0000f000053d00024f00000039445b2bb0000000000ff0be47700006200000000023e43a36800052e4534d73fd1de4261d212a0000003792744ce5995123fe4c047124552a1a20005c803b1cd2d600050d00051858e00000038a5c04cb09f27b21e0a24551c526d29610b5c43b90000003e90935a743817400034e21019326900047e5ba2230000000002c72205d40000004dc0002dc1be07f2ca1e400051b5d10f90000001200c20003a62971b846455c4c846147957c16716a42e3ee5e500049f0a101509b0003bc2350002570000005e400000056f39340c4da16847a0001903b05eb5ab03e0dc00b5073b42390ae07745140e29944619242030e21b17842514b57d22e20043f4f73ad54e3ec00045e4fb0000002e30004b400000008c00009519a0000002282d740646f3c300029d4a926800000048020c3f800000037b00000001b2bd46300054c2ff1b647d00000049900005500020441e0005a80300000005690000000000001c22320872fa0dd12d00036f0003020000001910000005db5c91ad0002fc0001c127929f0001f00a851c00001000015c23d51f1fe41200059f0e500000000053e0ac28b0000002ae0000000002ef3762a950c3c04f90bb0f522f4ec4544b656236e2711265cd19638e3f53de3cb19b57532943e25f3011fb0b402d13133953200a04d2443800c30205013265dd00000000000027c0000343e40362e917224000013c2c50000002120005642c91ec00000017600040a2f94ab0000f658f36300000000040900000000000021124b0000000000000000cb00000008100000006c0000000005040000000000bf0005a20a63214fa3710000440000001360005450003042660004d25340000f700020b0000003981172070f44503f254a0000000000000001ae1cb3fc5710001840691cc17e1a31000e635535d0e90000000000002300080004c253f34b5ac5132870000ea4ba00031b5a41a658a00034c07b11b2fb2220c500054341a26c00000000032e0ab00000056300000500000000035a1055733fa00000000005f00052b2240ba3eb0004bd0000000000002df0000001bd0d31ff4e734918b49232d5d95b62e448530500037728f4c600039700028c3a92d50002de39b1772e100040325314e0000850610000c03ca3c13b30000002490000004301401f846a0003bf00022a0cf0000000000005524b10db00000033d08e17d3a30000110002cb0003320000000001650002a216d1aa06b4
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x11e1980817198d200057064c205c66348001ac02060c6198d2000478a6020dc563480015c1930837158d200055264c205d46348001561910817518d200056264c205d063480015a1910817418d2000478660205c463480015c1930817118d2000718081751846348001ca0205d06118d20006159d58318463480018557560c6118d20006259d18318463480018957460c6118d20006315c98318463480018d17060c6118d2000478660205c653480018e0860817194d200057064c205c6534814d81c831d16554d200052564c61dd15348001589930837454d200056864420dd153480011e1980817190d2000638218205c643480015c1930817190d200051564c61dd54348001549930837550d200055864420dd5434814d81c831d56450d2000478a60205cf61480015c19308173d8520006855518315361480014e197083764c520005b064c20dd931480011e298082764c5200057064c209d931480011e198080764c5200057064c201d931481cf9c183080764c520004b8660201d931480014e197080764c520005b064c201d9314800183585610764c52000615a15831d931480018558560c764c52000625a11831d931480018958460c764c5200063160d821d931480018d183600764c52000638609801d931480014d193c80764c5200053164e201d931480014e290880764c52000439660201d931480014c593080764c52000730cc0201d931480010f198080764c5200053464c201d93148001cc332080764c52000538e60201d931480018e298080764c52000538660201d931480018e198080764c52000438660201d93148001c6295080764c52000718654201d93148001c6285080764c52000718614201d93148001ca294080764c52000728650201d93148001ca284080764c52000728610201d931480014e393080764c52000730a4c201d931480014e193080764c5200073064c201d931480014c193080764c5200073060c201d93148001cc0201da634c52000435a607658d31480018c7821d9634c52000634e007658d31480050d698e1d634c5200063121f8258d31480018d087e01634c52000638200765c931480018e0801d9324c52000730d80764c93148001645951d9324c520005a1650764c9314800168594d95324c52000591657644c931480018e0821d9704c5200c478261725c131480314e0965c9704c5200ce38219725c131480333c0984c9704c5200ceb0219325c13148001cc0764c9704c520005a2653654c9304800164995d91324c1202057025d32d8530480018e072219314c1200c57025d324c53048001ac0864c9314c120006b0d88864c5304800165195219314c120005a4650864c5304800169194d95314c12000594657644c530480315c097609314c1200c5b0259824c53048001ac086609314c120
  | 1 => 0x214e0721d6554d435085330c9854d43549420050764c545d76050801a155460c545873200638609701c161cc80103d9815276551320050764c549d9544c80141d9315076551325360b608541d9544c8016159315365d91310044d660549d9544c4015159315276551310054564c541d9544c54d91483150765513154651dd5821cd544c559987746087355131006c1151821cd544c55195375600735513156664dd1801cd544c401b1054600735513153645a0c74d95534c54d916831d76450d3104cc52615454d434c413514975515350d310d64521d5454d434c4012e29818b705893100538a5b721c1624c4012e198188705893104e5121d53549324c59f7049454d524c93104e6121d43509324c59d7049550d424c9310064515087551324c40138794617624c931004d1e5584d89324c43334498595524c93167dc125165549324c43334595e11524c9310cce165385509324c4131c497615424c93167ec115185509324c43338498591424c931675c125564509324c4016c19308362d8131004b8e6162c83604c4014e39758b20d8131004b8a6060dc9604c4012e198180725813100538a5e20d89604c4018e28788362581310ce3121f624c9604c4018e2861cb605813153487a636454e435400141d9315174d89500050764c54dc9655014d03e98d957494d4053507a5f6594d435002f81c875955350d400050764c545d7625002f3189854d43541400bcca261525095050053c28765494254140006855518315161cc0018e172600725873000591654724c961cc001685941c93258730005b0640724c961cc00168594949325873000591656424c961cc00103d9815276551300050764c549d9544c00141d9315076551305360e600541d9544c0015519520171cc93000564650805c7324c0015c19220171cc93000564652505c7324c0015519590171cc9300068515086551314c00139394617704c530004d4e5584dc1314c0314d0965cb704c53004f141d9534c5504c1817109454d31541300c55425d854c5504c1817109461531541300c554657744c5504c013c907650d31501305f5c4255434c5404c03159194dd5315013004d34259754c5404c1d1d10545d531501300c56425d844c5404c17d7109561131501300056264c205d365480015a19108174d95200042d662741876548001ca0205d061d9520006259d18318765480018957460c61d9520006b00818318765480011e29808371595200057064c20dc56548001ac02060c61595200055264c205d764480015619108175d91200041d662751876448001c60205d461d9120006159d58318764480018557560c61d9120006b00818318764480011e29808371591200057064c20dc56448001ac02060c61591200050764c54dd9544800141d9315176551205360720c545d95448
  | 2 => 0x7d9324b0002f9f00009a219124e8000b17c3f0003983240800191682799c110006418c0004a000ac7b14e2c81e180086f9367109077000000000000000000001783b1080b86a400006b97a2083e4196e000a65d0e42a8cc0296c5d8005984c7185a058ee2e0000016a41000060000011000000638c02c1ba4f9c86c8e2048362d8000e18465960700004f0881185c760001c1161b8002701c000000008a001506d9141c9226e1d2001ca139561e0200f0a0510fe3e07a290141007c28800359bc2b80025918669cc6a05e689f8709a0088d043892578d45c9e4039d60093426124808f6498002e87e0c1306b0244e03a4b81a7a8da1a11a57000000b4778ce00000811fa0311e789a6800f44a0566a9e831026011483496255188628d8381e06082a819f4430506c08e199d0679e6569583c1d4000e86011c50034690a8041642008c149427c8064292a379867f1b465076160842f0f2648743714c000005c000001da1b0947f9ee3194a1206200000000c25f8ea00054548fa32000000420a1ce000ca48146660020800850001f00884040a060203a000c1182a020002822001004800040000000010682804013c8401405000200c0200804080c0105c06100005832002904002010080804000180026440302c4e000c00002030980402030180802000101800190054564c545c6635514dc14631517198d540054364c545c86355001515931517118d540054664c545c0635500141d9315170d89540050764c545cb605500141d931537458a5300538241721c96194c018e172600725865300538249701c16194c018e1825c070586530050764c54dd16094c0141d931537558a4300538241721c96190c018e172600725864300538249701c16190c018e1825c070586430050764c54dd56090d3981c76e095454d4337e071db805515350d4d21e98d915390d520050764c545d3605480141d9315370595425340fa63655d2535094d41e97d965350d4
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1480001116801c960307921b9a989f800d1c1d8a0b971e109b0e128a81979d1f150f828b0c20141982211a000ea18c8489081581040080059e990983800d8005000000070f119393000686001000001808a080010000804006880438002050418082004cc075348294cc98a8b8cc6aa29b00d8264c541d9544c94d08bd43262a4ecaa262a6c416485421d544c93153603300c98a83b2a89829b2119015086551314c001450d4040ba0c3b2a4000b2068c205d061d9520004583521030630eca9000388174081831876548001160d4840c18c2b2a4000a186a0205d461d912000588346102ea30ec8900022c1a9081831876448001c20ba840c18c3b2240008b06a42060c615912053403950c98a8bb2a8900022c1a9081831866348001430d4040ba8c231a4000b1068c205d46118d2000514350102e8308c690002c81a3081741846348001070d490c102e329a4000c30219930817194d200041c35243040b8c86900030c08664c205c643480010e0d4326100ec98a4000c3066330080764c52000618331990403b262900024c1a3e60201d9314800183152b30100ec98a4000c1869598080764c52000614548cc0403b262900030a1a4660201d93148001860d1b30100ec98a4000c1866295080764c5200060c330ca8403b2629000306198a14201d93148001830cc30a100ec98a4000c2866294080764c52000614330ca0403b2629000342195650201d93148001850cc508100ec98a4000c2866184080764c5200070430ac20403b262900030c198a4c201d93148001860cc326100ec98a4000d10a5593080764c5200068832ac98403b262900034829464c201d93148001a40ca326100ec98a4000930ea193080764c5200068850ac98403b262900034418564c201d93148001a4142326100ec98a4000d2061193080764c52000498352c18403b262900030c19860c201d93148001c20c2b06100ec98a4000e2061183080764c52000498352100ed31a62900028c1a80807698d3148001461546c03b26498a4000c30260764c9704c5200041c3523910c98a60900030c097219324c5304800146153ec4432629824000c3025c86609314c120
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x2e6c800a403006081a95d02060c61d9520006041a95d42060c61d9120006021a569198080764c520006041a568d98080764c520006081a468d98080764c5200070018561193080764c520006041a961583080764c520006081a961183080764c520
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x98a
  | 7 => 0x98d
  | 8 => 0x98e
  | 9 => 0x4
  | 10 => 0x9ca
  | 11 => 0x9cb
  | 12 => 0x9cd
  | 13 => 0x9ce
  | 14 => 0x168a
  | 15 => 0x168b
  | 16 => 0x168d
  | 17 => 0x168e
  | 18 => 0xa0a
  | 19 => 0xa0b
  | 20 => 0xa0e
  | 21 => 0xa4a
  | 22 => 0xa4b
  | 23 => 0xa4d
  | 24 => 0xb49
  | 25 => 0xb4b
  | 26 => 0xb4d
  | 27 => 0xb4e
  | 28 => 0xcc9
  | 29 => 0xcca
  | 30 => 0xccd
  | 31 => 0xcce
  | 32 => 0x1709
  | 33 => 0x170a
  | 34 => 0x170d
  | 35 => 0x170e
  | 36 => 0xd09
  | 37 => 0xd0a
  | 38 => 0xd0e
  | 39 => 0xd49
  | 40 => 0xd4a
  | 41 => 0xd4d
  | 42 => 0xe89
  | 43 => 0xe8a
  | 44 => 0xe8b
  | 45 => 0xe8e
  | 46 => 0x1789
  | 47 => 0x178a
  | 48 => 0x178b
  | 49 => 0x178e
  | 50 => 0xec9
  | 51 => 0xeca
  | 52 => 0xecb
  | 53 => 0xecd
  | 54 => 0x17c9
  | 55 => 0x17ca
  | 56 => 0x17cb
  | 57 => 0x17cd
  | 58 => 0x1049
  | 59 => 0x104a
  | 60 => 0x104b
  | 61 => 0x9c992
  | 62 => 0x989d2
  | 63 => 0x1449
  | 64 => 0x1549
  | 65 => 0x124b
  | 66 => 0x209
  | 67 => 0xcc992
  | 68 => 0x98cd2
  | 69 => 0x3c9
  | 70 => 0x15c9
  | 71 => 0x12cb
  | 72 => 0x1889
  | 73 => 0x1609
  | 74 => 0x180b
  | 75 => 0x130b
  | 76 => 0x1a09
  | 77 => 0x1649
  | 78 => 0x198b
  | 79 => 0x134b
  | 80 => 0xa09d2
  | 81 => 0xa09d6
  | 82 => 0xa49d2
  | 83 => 0xa49d5
  | 84 => 0xb49d3
  | 85 => 0xb49d5
  | 86 => 0xb49d6
  | 87 => 0xcc9d2
  | 88 => 0x9ccd2
  | 89 => 0x1709d2
  | 90 => 0x9d712
  | 91 => 0x18c9
  | 92 => 0x1a49
  | 93 => 0xb5693
  | 94 => 0xb5695
  | 95 => 0xb5696
  | 96 => 0xca
  | 97 => 0xcd692
  | 98 => 0x168cd2
  | 99 => 0xcb
  | 100 => 0xa4a12
  | 101 => 0xb4a16
  | 102 => 0xd0a12
  | 103 => 0xa0d12
  | 104 => 0x150d
  | 105 => 0x128d
  | 106 => 0xe8a12
  | 107 => 0xa0e92
  | 108 => 0x12cd
  | 109 => 0x1a89
  | 110 => 0x1949
  | 111 => 0x198d
  | 112 => 0x134d
  | 113 => 0xb4a55
  | 114 => 0xd4a52
  | 115 => 0xa4d52
  | 116 => 0x150e
  | 117 => 0x128e
  | 118 => 0xeca52
  | 119 => 0xa4ed2
  | 120 => 0x12ce
  | 121 => 0x180e
  | 122 => 0x130e
  | 123 => 0x12ca
  | 124 => 0xccb51
  | 125 => 0xccb55
  | 126 => 0xccb56
  | 127 => 0x15ca
  | 128 => 0x170b51
  | 129 => 0x170b55
  | 130 => 0x170b56
  | 131 => 0x3ca
  | 132 => 0x188a
  | 133 => 0xd0b56
  | 134 => 0x160a
  | 135 => 0x1a0a
  | 136 => 0xd4b55
  | 137 => 0x164a
  | 138 => 0x18ca
  | 139 => 0x1a4a
  | 140 => 0x1a8a
  | 141 => 0x194a
  | 142 => 0x58a
  | 143 => 0x5ca
  | 144 => 0xd0cd2
  | 145 => 0xd0cd6
  | 146 => 0xd4cd2
  | 147 => 0xd4cd5
  | 148 => 0x18cb
  | 149 => 0x1a4b
  | 150 => 0xd4d12
  | 151 => 0xe8d12
  | 152 => 0xd0e92
  | 153 => 0x15cd
  | 154 => 0x1a8b
  | 155 => 0x194b
  | 156 => 0x1a0d
  | 157 => 0x164d
  | 158 => 0xecd52
  | 159 => 0xd4ed2
  | 160 => 0x15ce
  | 161 => 0x188e
  | 162 => 0x160e
  | 163 => 0xece92
  | 164 => 0x5cd
  | 165 => 0x104e92
  | 166 => 0x74c
  | 167 => 0x1a4d
  | 168 => 0x194c
  | 169 => 0x58e
  | 170 => 0x104ed2
  | 171 => 0x18ce
  | 172 => 0x1a8c
  | 173 => 0xcc9c99a
  | 174 => 0xcc989da
  | 175 => 0x9c98cda
  | 176 => 0x992d2
  | 177 => 0x995d2
  | 178 => 0xb4cd1
  | 179 => 0xb5711
  | 180 => 0x203d1
  | 181 => 0x4b
  | 182 => 0x5693
  | 183 => 0x21711
  | 184 => 0x20d11
  | 185 => 0x144e
  | 186 => 0x21611
  | 187 => 0x20d51
  | 188 => 0x144d
  | 189 => 0x21651
  | 190 => 0xb4a09de
  | 191 => 0x9ca16
  | 192 => 0xb4a49dd
  | 193 => 0x9ca55
  | 194 => 0x9cb53
  | 195 => 0x9cb55
  | 196 => 0x9cb56
  | 197 => 0x168b53
  | 198 => 0x749
  | 199 => 0xa18d2
  | 200 => 0xa4b55
  | 201 => 0x198a55
  | 202 => 0x144a55
  | 203 => 0xa5a52
  | 204 => 0x1692d2
  | 205 => 0x144b51
  | 206 => 0xd0ccb5e
  | 207 => 0xd4ccb5d
  | 208 => 0xd18d2
  | 209 => 0xd5a52
  | 210 => 0x1715d2
  | 211 => 0x144b53
  | 212 => 0x5cb55
  | 213 => 0xb5a55
  | 214 => 0x198b55
  | 215 => 0x1a0b55
  | 216 => 0x1a4b55
  | 217 => 0x18d792
  | 218 => 0x1a57d2
  | 219 => 0xccd16
  | 220 => 0xccd55
  | 221 => 0x74b
  | 222 => 0x144d55
  | 223 => 0x1a0d55
  | 224 => 0x144b
  | 225 => 0x104ece9a
  | 226 => 0x178ed2
  | 227 => 0x58b56
  | 228 => 0x17ce92
  | 229 => 0x145995
  | 230 => 0x145a15
  | 231 => 0x8992
  | 232 => 0xa4b49dd
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1426
  | 6 => 3727
  | 5 => 1517
  | 4 => 260
  | 3 => 68
  | 2 => 8
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
  | 7 => packedAt gbK7 (58462+((h/475+packedAt gbK7 (52762+(h % 475)*12) 12) % 2278)*12) 12
  | 6 => packedAt gbK6 (195042+((h/1242+packedAt gbK6 (178896+(h % 1242)*13) 13) % 4920)*13) 13
  | 5 => packedAt gbK5 (95563+((h/505+packedAt gbK5 (89503+(h % 505)*12) 12) % 2203)*12) 12
  | 4 => packedAt gbK4 (18974+((h/86+packedAt gbK4 (18200+(h % 86)*9) 9) % 313)*10) 10
  | 3 => packedAt gbK3 (5662+((h/22+packedAt gbK3 (5508+(h % 22)*7) 7) % 82)*8) 8
  | 2 => packedAt gbK2 (744+((h/2+packedAt gbK2 (736+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x638e0e3f18e3838fe387fe07ff0c10f10f1cf
  | 1 => 0x383f00fc7e0fc03f1fc070ff83f30633633933
  | 2 => 0x3fc000ff8ff0003fe3ff80fffc0c083c83ce3c
  | 3 => 0x3fffff000fffffc003ffff0000000fc0fc0fc0
  | 4 => 0xc00000000ffffffffc000000000ff000fff000
  | 5 => 0xfffffffff000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x821024209084090824081c202940c105105045
  | 1 => 0x18290a44260a42910a41224b02a30612612912
  | 2 => 0x244010890910042240960094500c0828828228
  | 3 => 0x88a4200022290800321420100200240240d80
  | 4 => 0x800000000dcd273c9002040618c55000dbf000
  | 5 => 0x37349cf24000000000040818630aadbf000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xffffffe8ffe8fae8ffffffe8ffe8fae8ffffffe8ffe8fae8ffffffe8ffe8fae8ffffffe8ffe8fae8ffffffe8ffe8fae8ffffffe8ffe8fae8ffffffe8ffe8fae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_14946
namespace PEqualNP.Outside.L_meta_14946
open PEqualNP.Outside.L_meta_14946.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 5 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 91 := (concat bs0_4_0 (concat bs0_4_32 bs0_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 8 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_64 : Interval s1Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_96 : Interval s1Atlas 3 96 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 102 := (concat (concat bs1_3_0 bs1_3_32) (concat bs1_3_64 bs1_3_96))
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
theorem bs1_4_160 : Interval s1Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_192 : Interval s1Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_224 : Interval s1Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_256 : Interval s1Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_288 : Interval s1Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_320 : Interval s1Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_352 : Interval s1Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_384 : Interval s1Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_416 : Interval s1Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_448 : Interval s1Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_480 : Interval s1Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_512 : Interval s1Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_544 : Interval s1Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_576 : Interval s1Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_608 : Interval s1Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_640 : Interval s1Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_672 : Interval s1Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_704 : Interval s1Atlas 4 704 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 725 := (concat (concat (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128))) (concat (concat bs1_4_160 (concat bs1_4_192 bs1_4_224)) (concat bs1_4_256 (concat bs1_4_288 bs1_4_320)))) (concat (concat (concat bs1_4_352 (concat bs1_4_384 bs1_4_416)) (concat bs1_4_448 (concat bs1_4_480 bs1_4_512))) (concat (concat bs1_4_544 (concat bs1_4_576 bs1_4_608)) (concat bs1_4_640 (concat bs1_4_672 bs1_4_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_64 : Interval s1Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_96 : Interval s1Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_128 : Interval s1Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_160 : Interval s1Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_192 : Interval s1Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_224 : Interval s1Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_256 : Interval s1Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_288 : Interval s1Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_320 : Interval s1Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_352 : Interval s1Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_384 : Interval s1Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_416 : Interval s1Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_448 : Interval s1Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_480 : Interval s1Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_512 : Interval s1Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_544 : Interval s1Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_576 : Interval s1Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_608 : Interval s1Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_640 : Interval s1Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_672 : Interval s1Atlas 5 672 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 682 := (concat (concat (concat (concat bs1_5_0 bs1_5_32) (concat bs1_5_64 (concat bs1_5_96 bs1_5_128))) (concat (concat bs1_5_160 (concat bs1_5_192 bs1_5_224)) (concat bs1_5_256 (concat bs1_5_288 bs1_5_320)))) (concat (concat (concat bs1_5_352 bs1_5_384) (concat bs1_5_416 (concat bs1_5_448 bs1_5_480))) (concat (concat bs1_5_512 (concat bs1_5_544 bs1_5_576)) (concat bs1_5_608 (concat bs1_5_640 bs1_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_32 : Interval s1Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 40 := (concat bs1_6_0 bs1_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_7_0 : Interval s1Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_7 : Interval s1Atlas 7 0 1 := bs1_7_0
theorem alls1 : ∀ k ≤ 7, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 5 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 91 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
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
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 7 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 5 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 9 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 50 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_128 : Interval s4Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 136 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 48 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 9 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 50 := (concat bs5_3_0 bs5_3_32)
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
theorem bs5_4_96 : Interval s5Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_128 : Interval s5Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 136 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 48 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_3_64 : Interval gbAtlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 68 := (concat bgb_3_0 (concat bgb_3_32 bgb_3_64))
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
theorem bgb_4_256 : Interval gbAtlas 4 256 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 260 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256))))
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
theorem bgb_5_1504 : Interval gbAtlas 5 1504 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1517 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504))))))
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2528 : Interval gbAtlas 6 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2560 : Interval gbAtlas 6 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2624 : Interval gbAtlas 6 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2656 : Interval gbAtlas 6 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2720 : Interval gbAtlas 6 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2752 : Interval gbAtlas 6 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2816 : Interval gbAtlas 6 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2848 : Interval gbAtlas 6 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2912 : Interval gbAtlas 6 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2944 : Interval gbAtlas 6 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3008 : Interval gbAtlas 6 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3040 : Interval gbAtlas 6 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3104 : Interval gbAtlas 6 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3136 : Interval gbAtlas 6 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3200 : Interval gbAtlas 6 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3232 : Interval gbAtlas 6 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3296 : Interval gbAtlas 6 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3328 : Interval gbAtlas 6 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3392 : Interval gbAtlas 6 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3424 : Interval gbAtlas 6 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3488 : Interval gbAtlas 6 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3520 : Interval gbAtlas 6 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3584 : Interval gbAtlas 6 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3616 : Interval gbAtlas 6 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3680 : Interval gbAtlas 6 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3712 : Interval gbAtlas 6 3712 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3727 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)))) (concat (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)))))) (concat (concat (concat (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)))) (concat (concat (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496))) (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624)) (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752))))) (concat (concat (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976))) (concat (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)))) (concat (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456))) (concat (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 bgb_6_3584)) (concat (concat bgb_6_3616 bgb_6_3648) (concat bgb_6_3680 bgb_6_3712)))))))
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
theorem bgb_7_1056 : Interval gbAtlas 7 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1088 : Interval gbAtlas 7 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1120 : Interval gbAtlas 7 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1184 : Interval gbAtlas 7 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1216 : Interval gbAtlas 7 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1280 : Interval gbAtlas 7 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1312 : Interval gbAtlas 7 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1376 : Interval gbAtlas 7 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1408 : Interval gbAtlas 7 1408 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1426 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 (concat bgb_7_448 bgb_7_480))) (concat (concat bgb_7_512 (concat bgb_7_544 bgb_7_576)) (concat bgb_7_608 (concat bgb_7_640 bgb_7_672))))) (concat (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832))) (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))) (concat (concat (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)) (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216))) (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 32, 48),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 4 zero,inputs.getD 2 zero,inputs.getD 6 zero,inputs.getD 7 zero,inputs.getD 5 zero,inputs.getD 3 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffeeffeefeeeffffffeeffeefeeeffffffeeffeefeeeffffffe8ffe8fae8ffffffeeffeefeeeffffffeeffeefeeeffffffeeffeefeeeffffffe8ffe8fae8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 12 := by
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
theorem binaryLower (low : Lower true fullRoots fullWord 12)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 12 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_14946.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.or,[8,3]⟩,⟨.or,[6,7]⟩,⟨.and,[9,10]⟩,⟨.or,[1,7]⟩,⟨.or,[5,6]⟩,⟨.and,[12,13]⟩,⟨.or,[0,4]⟩,⟨.and,[15,5]⟩,⟨.and,[0,4]⟩,⟨.or,[11,14]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
    exact ⟨mono,20,monoShape,by change 13 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_14946

open PEqualNP.Outside.L_meta_14946 in
theorem PEqualNP.Outside.L_meta_14946 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
