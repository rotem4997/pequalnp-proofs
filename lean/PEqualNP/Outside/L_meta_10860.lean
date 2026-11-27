import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_10860.Model
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


end PEqualNP.Outside.L_meta_10860.Model

namespace PEqualNP.Outside.L_meta_10860
open PEqualNP.Outside.L_meta_10860.Model
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

end PEqualNP.Outside.L_meta_10860

namespace PEqualNP.Outside.L_meta_10860
open PEqualNP.Outside.L_meta_10860.Model
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
  | 1 => 0xff83e1e1ffffffe1870f870e0fffffff044fff
  | 2 => 0xffc01fe3c1e1c3e07f1f80ff1e1e0f09a72cc
  | 3 => 0xffffe003fe01ffff801fff001fe00ffe3830f
  | 4 => 0xf00000003fffe03ffffe000001ffff00fc03f0
  | 5 => 0xffffffffc000003ffffffffffe000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x20884202044000000102810224222212004455
  | 2 => 0x6518d4d049c4a9662351a824e4f146a68a52cc
  | 3 => 0x86219054908cd12aa8413260415508cca2830a
  | 4 => 0xc4731999231899bdb66420c189999c88fc03a0
  | 5 => 0x8420100021102114488448908001000552800
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfffcfffccccccc00fffcfffccccccc00fffcfffccccccc00fffcfffccccccc00fffcfffccccccc00fffcfffccccccc00fffcfffccccccc00fffcfffccccccc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_10860
namespace PEqualNP.Outside.L_meta_10860
open PEqualNP.Outside.L_meta_10860.Model
def s1K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2003000004106f21ec43b487a90e521
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x2950a21
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*4) 4
  | 3 => packedAt s1K3 (i*15) 15
  | 2 => packedAt s1K2 (i*26) 26
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (5+((h/1+packedAt s1K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s1K3 (79+((h/1+packedAt s1K3 (75+(h % 1)*4) 4) % 11)*4) 4
  | 2 => packedAt s1K2 (27+((h/1+packedAt s1K2 (26+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfd99fe39cff07f
  | 2 => 0xfffffffffffffffffffffffd7e1e4fc1f73993
  | 3 => 0xe7fe073fe07ce1c
  | 5 => 0xfbfff83fff80fe0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff404220008410025
  | 2 => 0x289509244a2a892
  | 3 => 0x19115069424aa18
  | 5 => 0x60002921000540
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 45 s1Pos s1Neg, 0xfffafffaaaa0aaa0fffafffaaaa0aaa0fffafffaaaa0aaa0fffafffaaaa0aaa0fffafffaaaa0aaa0fffafffaaaa0aaa0fffafffaaaa0aaa0fffafffaaaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_10860
namespace PEqualNP.Outside.L_meta_10860
open PEqualNP.Outside.L_meta_10860.Model
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
  | 0 => 0x3c3f87c71fc3f1c738e3c71c7f1f838f193793
  | 1 => 0x3fc7f807e3fc7ff8c0fc781f87e3fff021c9fc
  | 3 => 0xc007fff803ff81ffff007fe007fc03ffc60e1f
  | 4 => 0xfff8000003fffe00ffff800007fffc00f80fe0
  | 5 => 0xfffffffffc000000fffffffff8000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8590918a205902880860c105330498a6091391
  | 1 => 0x89110900489000100244809112109220140b4
  | 3 => 0x2222200490025005100124004482248420c0a
  | 4 => 0x9320672692326192fac900c26692704cf80f40
  | 5 => 0x2004440400224824a492249240004000b4a000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xffeeffeeeeccee00ffeeffeeeeccee00ffeeffeeeeccee00ffeeffeeeeccee00ffeeffeeeeccee00ffeeffeeeeccee00ffeeffeeeeccee00ffeeffeeeeccee00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_10860
namespace PEqualNP.Outside.L_meta_10860
open PEqualNP.Outside.L_meta_10860.Model
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
  | 0 => 0xfe1f8f1fc3fc7e38e3e3870ff1f81fe3133cf
  | 1 => 0xf1fe00fe3fc3ff1c0fc7c07f0fe3ffc049ccfc
  | 2 => 0x1ffff003ffc07fff007ff800ffc01ff8e0f0f
  | 4 => 0xfe0000003ffff81ffff800000ffffe01f00ff0
  | 5 => 0xffffffffc000001ffffffffff0000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xa424514205880a00860a0812650494541111c5
  | 1 => 0x64443220489880240246412623210c8c09445c
  | 2 => 0x4888a0249011940d100493040a4829288a0e0a
  | 4 => 0x8819c4c92323065bac900608cc927031f00ba0
  | 5 => 0x111008002222092492124488000400164a000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xfefefefeececa0a0fefefefeececa0a0fefefefeececa0a0fefefefeececa0a0fefefefeececa0a0fefefefeececa0a0fefefefeececa0a0fefefefeececa0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_10860
namespace PEqualNP.Outside.L_meta_10860
open PEqualNP.Outside.L_meta_10860.Model
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
  | 0 => 0xf3c38f1e31fcfc7f911cc71c7c7e1ff81333f
  | 1 => 0xf03fc0fe03e3f1f8c61e0f81f9f8fe3809cdcc
  | 2 => 0xffc000fffc03fe00ffe00ffe01ff003fce0e0f
  | 3 => 0xffffff000003ffff07fff00001ffffc0700ff0
  | 5 => 0xfffffffffffc000007fffffffe0000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1049114442064080010441054412489011115
  | 1 => 0x10899224ca04ac810a120c84b4c84c9309454c
  | 2 => 0x22832449824909928720292c219219264a0e0a
  | 3 => 0x44122009109201009544a00801249104500aa0
  | 5 => 0x8820008000000024208902410000000024a000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xfffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0fffefffeeea0eea0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_10860
namespace PEqualNP.Outside.L_meta_10860
open PEqualNP.Outside.L_meta_10860.Model
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
  | 0 => 0xff87c3ff87ffc3f87f87f0387f07ffeb3c33f
  | 1 => 0xf07fffc0ff8787c3f87f87fff87f83814cfdcc
  | 2 => 0xff807fff0007fffc007ff803ff8003ff8f0e0f
  | 3 => 0x7ffffff807ffff800003fffffc01f00ff0
  | 4 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa100848a4082000980a80928809128a411c115
  | 1 => 0x2310088610080840881882198823090c04554c
  | 2 => 0x46355114355545d444555053550612598e0e0a
  | 3 => 0x4c466220a44156a655044082664c5011e00aa0
  | 4 => 0x88644338c666673b666664e044086061fba000
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xeeeceea0eeeceea0eeeceea0eeeceea0eeeceea0eeeceea0eeeceea0eeeceea0eeeceea0eeeceea0eeeceea0eeeceea0eeeceea0eeeceea0eeeceea0eeeceea0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_10860
namespace PEqualNP.Outside.L_meta_10860
open PEqualNP.Outside.L_meta_10860.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1d0a1390069c210217990300001b9580098f001b219f839208090b9e84019e0f919697010e80151d80208019a0180500000d8b0a9c9a10940007888e000c148706048d000c800598961a829f008012911300009c020001302180020454286042c2031ebc804007fd5001fe54006f95001fd54006f55001fc54007fd4c01fe53007f54c01fc53007fd0c01bf43007f90c01fd43006f50c01fc43007fd4801fe52007f54801fc52007fd0801fe42007f50801fc42007fcc801fe32007b8c801fd32007b4c801fc32007fd4401fe51007f54401fc51007fd0401fe41006f90401fd41007f10401bc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd4001fe50007f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xa24000ef55120005fec690012fe63480017eb1a4004bf18d200077e8690003bd4348001f72924000fb54920007dc6490003ed32480017fb0a4001bf185200077c8290003bc4148001fd2824000fe5412001ff6409000bee20480057fb284006bf99420016fcca100027e65080017eb284002df59420004faca1000afc65080057fb204005bf990200177cc810002be64080017eb204002ef590200057ac81000afc6408001df2a04000ef55020015fec610012fe6308005ef3184000b798c20005fac61000bdd63080016eb184002bf18c200077e8610003bd43080077f3104000fbd482001fd8a41000fee3208001f69904001bf98420017ecc210002f661080017eb084002fd58420005eac210003be4108001de2084003fbc8420007da421000afe6008005f79004002fe88020017da401000ff920080037fb2e2006bf99710005facb88006fc65c40037fb262005bf99310005fac988006fc64c4001df2a62000ef5531000dfec788012fe63c40017eb1e2001bf18f100077e8788003bd43c40037fb162003bf98b1000fdcc588002ee62c40017eb162001fb58b10005dac588006fc62c4001f71962000fb4cb1000feca388003f551c4001fba0e2001ef9071000f788388007f441c4003da20e2001fd8c710007ea6388007f621c4001fa90e2002bfd9610035fccb08002fd65840057e32c2002bfd921002dfcc90800bbe64840015f3242000bf592100177ac908002bd64840057e3242000ef952100077aa90800aff63840097f31c2000bf58e10015f8c708003bf4384001dea1c2002bfd8a1001dfcc508002fd62840057e3142000fb8ca10007da6508002fd6184003df20c2001ef10610015fcc10800bfa5084001fca842002fe90210007f2810800bfa3084001fc9842000fec8210017f0410800bf71084003fd8842000bfd9510035fcca88002fd654400d7e32a2000bfd91100077ec888002bf644400b7f3222000bf5911002df8c888003bc64440015e3222000ef951100077aa888002ff63440097f31a2000bf58d10025f8c688003bf4344001dea1a2000bfd891001dfcc488002fd62440077e3122000fb8c910007da6488003f65144001faa8a2000fdd051000f7c8288007bc4144001fa20a2000ed10510007ec6288003f53144001fb10a2000fd48510007f4a088003f95044001fd2022000fe50110007f46088003f93044001fd9022000fe0811000ff6208800bf610440057fb282006bf99410005faca0800afc65040057fb202005bf99010005fac80800afc6404001df2a02000ef55010015fec608012fe63040017eb182002bf18c100077e8608003bd43040057fb102003bf98810005fac40800afc6204001f71902000fb4c81000dfcc208007be4104003de2082002bf98010017ee200800bfa1004005fa8802001fe44010
  | 1 => 0x3bc415000bfda028002ef90140015feca2001afe65100017eb288002bf1944002dfcc820017be5410001deaa08004bf98c40005fac620017bf4310001dea188003bf98840005fac420003ee3210001f69908001bf98440005fac220003be411000bde2088002bf980400177e802000bfa4010005dea008005fe50040025fecb9801afe65cc0017eb2e6004bf19730025fec998016fe64cc009df3266000af99330005fac998013bd64cc0015eb266004bf193300077ca998003bd54cc009ef29e6000f754f300277e8798013bd43cc0077f3166004fb98b30005dcc598002fd62cc009f6b166000bb58b30027be6598013ee32cc001ee9966004fb4cb300079a6598006fe61cc0017eb0e6000ef9073000778839800aff658c00d7f32c6000bf59630015f8cb1800aff648c00b7f3246000bf59230015f8c918003be548c001deaa46000bf58e300077e8718003bd438c0077f3146000bf58a30007dc6518003ed328c0037f30c6000bf586300077c8318003bc418c0057f3046002fe94230007f2a11800bdf308c009fd9846000bfd9530035fcca98002fd654c00d7e32a6000bfd913002dfcc898002fd644c00b7e3226000ef951300077aa898003de534c001eea9a6000efd0d300077a8698002ff624c0077e3126000f7cc930007dc6498003dd324c001f69926000f34c930005fec298006fc614c001df20a6000ef10530007f4a098003f9504c009fd9826002f78c130015feca1801afe650c005bf32860009f99430005faca1800b7d650c0013eb286002bf19430015fec818016fe640c005df3206000af99030005fac81800bbd640c0015eb206002bf190300077ca818003bd540c0097f3186004efd0c300277a861800efe620c005f73106000bb98830005fac41800bed620c00176b106004fb8c830027da6418006fe610c005fb3086000bd98430005fac21800bf5610c0017ab086000ef9043000778821800afe600c005ef9806002fe8c030017ba6018013f9300c0077fb2e4006bf99720005facb9000efc65c80077fb264005bf99320005fac99000efc64c8001df2a64000ef5532001dfec790012fe63c80017eb1e4003bf18f200077e8790003bd43c8007f72964000fb54b2001fdc6590003ed32c80037f30e4000bf587200077c8390003bc41c80057fb2c4006bf99620005facb1000afc65880057fb244005bf99220005fac91000afc6488001df2a44000ef55220015fec710012fe63880017eb1c4002bf18e200077e8710003bd43880017eb144000fbd4a20007d8a510003ee3288001f69944001bf98620005fac310003be4188001de20c4000fbc8620007da431000afe6088005fd2844000fe54220017de411000ffb20880017fb2a4006bf99520005faca9001afc65480017fb224005bf99120005fac890016fc6448001df2
  | 2 => 0x21005fec690812fe63484017eb1a4204bf18d210077e8690803bd4348401f72924200fb54921007dc8490803ed4248401f71924200fb4c921007eca290803f55148403df20a4201ef1052101fee4290807ee21484017fb024202bf1812100dfeca1081afe65084017eb284201bf1942100dfec810816fe64084017eb204201bf190210077ca810803bd54084037fb184204bf98c21005fac610806fc6308401dfa184200ef50c2101dfcc41080fee3208401f69904201bf9842100f7c8210807bc4108403f79084201fd8842100fda421080ff521084057f3004200bf5802102dfcc9a801bbe64d40015f326a000bf593500377ac9a8002bd64d400ddf2a6a006ef55350025fcc7a8002fd63d400dbfa9ea000df54f500077e87a8003bd43d40077f316a000bf58b50036fea5a80037d52d4001f7196a000fb4cb5000dfcc3a8002fd61d4001df20ea000ef10750005facb28016fe64940017eb24a000ef952500077aa928012fe63940017eb1ca000efd0e500077a872800efe62940017eb14a000fb8ca50007da6528006fe61940017eb0ca000ef9065000778832800afe6094005bfa84a006fed4250005fec8a8016fc6454001df2a2a000ef55150005fec6a8012fc6354001bfa9aa000df54d500077e86a8003bd43540017fb12a000fbd8950005dec4a800efc6254001f6312a000bb18950006fea4a80037d5254001f7192a000fb4c950005fec2a8006fc6154001df20aa000ef10550037f6a0a800b7e505400d7f328a005bf990500177cc828002be64140017eb20a002ef590500057ac82801bbe541400ddeaa0a004bf98c50017bcc628002de63140017eb18a002f758c50005bac628003bf4314001dea18a003bf98850017dcc428002ee62140017eb10a002fb58850005dac428003ee3214001f6990a001bf98450017ecc228002f661140017eb08a002fd58450005eac228003be4114001de208a002bf98050016fea02800bfa5014005bea80a006fe5405002dfecba001afe65d00017eb2e8005bf1974002f7ca9a0003bd54d00097f31e8000bf58f4002f7e87a0003bd43d00077f3168000bf58b4002f7e85a0003bd42d0001f71968000fb4cb4000dfcc3a0002fd61d0001df20e8005ef10740015fecb2001afe65900017eb2c8002bf19640005fac920003be5490001deaa48004bf98e40005fac720003bf4390001dea1c8003bf98a40005fac520003ee3290001f69948001bf98640017ecc320002f661900017eb0c8002fd58640005eac320003be4190001de20c8002bf982400177e8120017fb40900017fb2a8006bf99540005facaa001afc6550001df2a28000ef55140005fec6a0012fc6350001dfa1a8000ef50d40005fec4a000efc6250001dfa128000ef50940007dc64a0003ed32500017fb0a8001bf185400077c82a000
  | 3 => 0xeb2e6204bf19731025fec998816fe64cc409df3266200af99331005fac998813bd64cc4015eb266204bf193310077ca998803bd54cc409ef29e6200f754f310277e8798813de43cc409dea1e6200f750f310073a879880efe62cc409f73166200bb98b31005fac598813ed62cc40176b166204fb8cb31027da6598807be41cc403de20e6202bf98331005fac198806ff658c40d7f32c6200bf5963100df8cb18806ff648c403dfb246201afd923102dfcc918802fd648c4037e3246201ef1923100d78c918803be548c401deaa46200bf58e310077e8718803bd438c4077f3146200bf58a31007be6518803ee328c401ee9946200fb4ca310079a6518806fe618c403fb28c6200fd5463100f7c8318807bc418c403ef98c6204fdcc631015fcc118802fd608c4017fb2a6206bf99531005faca9881afc654c4017fb226200efd91310057ec898816fe644c4017eb226205bf1913100778c898802bc644c401df2a26200ef55131007bca698803dd534c401dfa1a6200f790d310077a8698803dd434c401cea1a6200bfd893101df8c498803ee324c401f69926200fd94531007eaa298807be414c403de20a6204fdcc53100fbc6298802ff604c4057e3026201bfd9431035fcca188077e650c4013f3286200bf5943100efaca188027d650c4037e3286201bfd903102dfcc818807be640c4015f3206200bf5903100f7ac818802bd640c4037e3206200ef950310077aa818812fe630c409dfa186204ef50c3101dfcc418807ee620c401773106200bf5883100fdac418802ed620c409ef9906204fb8c831007ba6418813ed320c401e69906201bf9843100f7c8218807bc410c403ef9886201fd8c43100fba6218813f5310c4057f3006201fe98031005f4c018802fd600c403fcb006200be5803101dfecb9081afe65c84017eb2e4203bf1972101dfec990816fe64c8407df3264200af99321005fac99080fbd64c84015eb264203bf193210077ca990803bd54c84077fb1e4204bf98f2101fbcc790802de63c84017eb1e4203f758f21005bac79080efc63c8401dfa1e4200ef50f2101fdca590803ed52c8407f72164200fb50b2101fdc6590803ed32c8403df20e4201ef10721015fcc190802fd60c84037fb2c4206bf99621005facb10806fc65884037fb244205bf99221005fac910806fc6488401df2a44200ef5522100dfec710812fe63884017eb1c4201bf18e210077e8710803bd43884017eb144200fb8ca21007da6510806fe6188403fb28c4200fd5462100f7c8310807bc4188403f790c4203fdc8621015fcc110807fa60884017d3044200bf5822100ff2c110802f960884017fb2a4206bf99521005faca9081afc65484017fb224200efd91210057ec890816fe64484017eb224205bf1912100778c890802bc6448401df2a24200ef551
  | 4 => 0x807dd63144016eb18a200efd0c510077a862880efe6214403f7310a200bb98851005fac428807ed621440176b10a200fb8c851007da6428806fe6114403bfa88a201fd9445100efaa22881bf551144057f300a201fe98051005f4c028802fd6014403fcb00a200be5805102dfecba081afe65d04017eb2e8205bf1974102f7ca9a0803bd54d04097f31e8200bf58f4102f7e87a0803bd43d04077f3168200bf58b41007dc65a0803ed32d04057f3068200bf5834100dfecb2081afe65904017eb2c8201bf19641005fac920803bf5490401df2a48200ef5524100778a920812fe63904017eb1c8200efd0e410077c8720803bd4390401de21c8203bf98a41005fac520803bf4290401df2148200ef50a41007788520803ee3290401f69948201bf9864100f7e8320817f741904057f3048200bf5824100f7ecb20806bf6590403df32c8201ef596410057acb20807bc6590403dfb1c8201ef98e4100f7ac720802bd6390403de31c8200efd4e410077ca720803bd5390401de29c8201efd8a4100f7cc520807bd6290403de3148200efd4a410077ca520803bd5290401de2948200efcca410077c6520803ae3290401de9948200eb4ca41007786520806be6190403dfa8c8201ef9464100f7aa320807bc5190403dfb048201ef9824100f7ac120807bc60904017fb2a8206bf99541005facaa081afc6550401df2a28200ef55141005fec6a0812fc6350401dfa1a8200ef50d41005fec4a080efc6250401f71928200fb4c94102fee82a0807be41504017fb028202bf1814100dfeca2081afe6510403bf32882009f99441005faca208077d65104013eb288201bf1944102dfcc820803bf541040bdf2a08200ef5504102f78a820812fe6310403ef3188200b798c41005fac620807dd63104016eb188205efd0c410077c8620803bd431040bde2188203bf9884100fdcc420802ee62104017eb108201fb58841005dac420817bf4210401df2108200ef5084102f788420803ee3210401f69908201bf9844100f7e8220807f64110403dea088205fd50441015fcc020807fa60104017d3008200bf5804100ff2c020802f96010403dfb288201afd944100f7cca208073e6510403deb288200af5944100e7aca208023d6510403de3288201efd8c4100f7cc6208079e6310403deb188200af58c4100f3ac6208029d6310403de3188200efd4c410077ca620803bd5310401de2988201efd884100f7cc420807ae6210403deb108201eb5884100f78c420803bf5210401df2908200ef5484100778a420803bf3210401df1908200eb8c8410077a6420803ad3210401de1908201ef9844100d7cc220807b66110403dfa888201ef9444100f7aa220807bc5110403dfb008201ef9804100f74c020807bd6010403dcb008201ef18041025fecb9881afe65cc4017
  | 5 => 0x4a32007de851900fee428c801f6a146403fb10a3201fbe6519013ef328c8037f30c6400bf58632015fcc119002fd608c807f7b2c6400fb99632007dacb1900fec658c807f7b246400fb99232007dac91900fec648c801f7aa46400fb952320075ca919003ed548c801d6aa46400fb15232005dac719003ef538c809f729c6400fb54e32027d8a719003ef438c801d7a1c6404fb90e32007da8719003ad438c809f621c6403fbd8632007dcc319003ed618c807f630c6403fbd8232007dcc119003ed608c807f63046400bfd9532035fcca99002fd654c80d7e32a6400bfd913202dfcc899002fd644c80b7e3226400ef951320077aa899003de534c801eea9a6400efd0d32007bc8699003bd434c801eea1a6400e750d32007dea499003ee524c801f6a926400fb14932007de8499003ee424c801f6a126400fb10932027de649900fde324c8017fb0a6401bf18532005fec09900afc604c801f7b2a6400fb99532007daca99003ec654c801f7b226400fb99132007dac899003ec644c801f7aa26400fb951320075ca899003ed544c801d6aa26400fb15132007dec699003cf634c801f7a9a6404fb94d320079ca699003ed534c801e6a9a6404fb14d32007de8699003af434c809f721a6400f390d32007da8699003ad434c801e6a1a6400e350d32027d88699003ef614c801f730a6400fb58532007d8c299003ef604c801f73026400fb58132007d8c09900eff650c80d7f3286400bf5943201df8ca1900eff640c80b7f3206403ef990320057cc819002fd640c807deb206400af5903201df8c819003be540c801deaa06404bf98c320277e8619013bd430c8077f3106400bb9883201fbe641900fee320c807ee9906404fb4c83200dfcc219002fd610c8057f3006400bf5803202dfcc9a881bbe64d44015f326a200bf593510377ac9a8802bd64d440dbfaa6a206ef95351006faa9a881bbd54d44019eaa6a204bf98f51005fac7a881b7f53d4401bea9ea200efd0f510077a87a880efe62d44017eb16a200fb8cb51007da65a880afe60d44017eb06a200bf5965100f7ec928816fe64944017eb24a201ef192510077ca928803bd54944097f31ca200bf58e510077e8728803bd43944077f314a200bf58a51007dc6528803ed32944037f30ca201dfd4651037eea32880afe60944017eb04a200bfd91510077ec8a8802bf645440b7e322a200ef1915100578c8a88037f5454401df2a2a200df551510077aa8a88033d54544017fb1aa204bf18d51006fea6a88037d5354401dfa1aa200ef50d51005fec4a880efc6254401f7192a200fb4c951037eea2a88077e51544017fb02a202bf18151035fcca28816fe6414403df320a200af99051005fac828807bd64144015eb20a206ef950510377aa828812fe6314403ef318a200b798c51005fac628
  | 6 => 0x1dfb028600ef981430077ac0a1803bc6050c097fb288606bf99443005faca21812fc6510c0b7f3208600af9904302f7ca821803bd5410c097f3188604efd0c43027bc8621813bd4310c0beea188603bf98843027dcc421802ee6210c017eb108604fb58843005dac421806fe6110c017eb088602bf98043005fac021816fe64d480ddf326a400af99352005fac9a901bbd64d48015eb26a406ef953520377aa9a9012fe63d48017eb1ea400efd0f520077a87a9006fe61d48017eb0ea402bf98352005fac1a9002fd659480b7f324a400bf592520077ca929003bd54948097f31ca400bf58e520077e8729003bd43948077f314a403dfd4a52037dea529006fe61948017eb0ca402bf98252005fac129002ff645480b7e322a400ef951520077aa8a9002ff63548097e31aa400efd0d520077a86a901bef5254807bf292a400bfd855200df8c2a9002ff60548057e302a406bf9945202dfcc82900fbe64148015f320a400bf5905201f7ac829002bd641480ddf2a0a406ef55052025fcc62900fde63148016f318a400bf58c5201fbac629002dd6314801dfa18a400ef50c5201dfcc42900f7f5214807f7290a403df54852037daa429006fe6114807fb308a400bd98452005fac22900ff561148017ab08a402bf9805201ff4c029002fa60148017eb00a403fe58052005f2c029016ff65d080d7f32e8400bf5974202df8cba1017be54d0801deaa68404bf98f42005fac7a1017bf43d0801dea1e8401bf98742005fac3a100afe60d08017eb068403bfd9642035fccb21002fd65908077e32c8400bf592420077ca921003bd54908097f31c8400bf58e420077e8721003bd43908077f3148403efd0a4202fde8521006fe61908017eb0c8402bf98242005fac121002ff655080d7f32a8400bf59542035f8caa1003be5450801deaa28400bfd8d42025f8c6a1003bf4350801dea1a8405fbd094201f7c84a1002ff61508037e30a8400bfd8142015f8c0a100eff651080d7f3288400bf5944201df8ca21016fe641080bdf2a08400ef55042025fcc62100fde63108016f3188400bf58c4201fbac621002dd631080bdfa188400ef50c4201dfcc42100fbf4210807f72108403ef5084202fda8421006fe61108017eb088402bf98042005fac021012ff65cc80d7f32e6400bf59732025f8cb99012ff64cc80b7f3266404ef993320057cc999002fd64cc809deb266400af59332025f8c999003be54cc801deaa66404f794f32007baa799013bf43cc809ef21e6404ef50f32007ba87990039d43cc8037f30e6400bf58732015fcc199002fd60cc8077fb2c6406bf99632005facb1900efc658c8077fb246405bf99232005fac91900efc648c801df2a46400ef55232005fac719003bf438c801dea1c6403bf98a32007dea51900fee528c801f6a946403fb1
  | 7 => 0xaa0177e54550017fb1aa804bf18d54005fec4aa00efc62550017fb0aa801bf18554005fec0aa00afc6055001dfb2aa800cfd95540077ec6aa002bf6355001df31aa800ef58d5400778c6aa003bf6255001df312a800ef5895400778c4aa003bf6155001df30aa800ef5855400778c2aa006bc6155001dfb02a800ef981540077ac0aa003bc605500d7f328a805bf990540057cc82a0177f541500bdf2a0a805df550540377aa82a012fe63150017eb18a803bf98854005fac42a006fe61150017eb08a802bf98054005fac02a016fe64d4c0ddf326a600af99353005fac9a981bbd64d4c015eb26a606ef953530377aa9a980efe62d4c017eb16a601bf98753005fac3a980afe60d4c017eb06a600bf5965302dfcc929813be6494c015f324a600bf592530277ac929802bd6494c01df2a4a600ef55253025fcc7298137f5394c0defa9ca603bf98a53027dcc529802ee6294c017eb14a604fb58a53005dac529806fe6194c017eb0ca602bf98253005fac129802ff6454c01df322a600ef5915302df8c8a9803be5454c01deaa2a606f7d4d53026fca6a9802ff6254c077e312a600bfd855300df8c2a9802ff6054c057e302a606bf9945302dfcc829813be6414c015f320a600bf590530277ac829802bd6414c0ddf2a0a606ef55053025fcc6298137f5314c09ef298a604df54c53037baa62980efe6214c09f7310a600bb98853005fac429813ed6214c0176b10a601bf98453027ecc229802f66114c017eb08a604fd58453005eac22980afe6014c09fd300a600be98053005fac029813f96014c017cb00a605bfd9743035fccba1802fd65d0c0b7e32e8600efd534302f7ca9a1803bd54d0c0bde2a68603bf98b43005fac5a1806fe61d0c017eb0e8602bf98343005fac1a1817bf65d0c015fb2e8600ef997430077acba1802bd65d0c0bde32e8600efd4f430277ca7a1803bd53d0c09de29e8605efd8b430077cc5a1803bd62d0c0bde3168605efd87430077cc3a1806be61d0c01deb0e8605ef1874302f7ec1a1803be60d0c01deb068605ef18343025fecb2181afe6590c017eb2c8604bf19643005fac921802bd6490c01df2a48600ef55243025fcc721813bf4390c0befa1c8603bf98a43027dcc521802ee6290c017eb148604fb58a43005dac521806fe6190c017eb0c8602bf98243005fac121802ff6550c0d7f32a8600bf59543035f8caa1803bf5450c01df2a28600ef5514300778a8a1817df4350c09df21a8600bfd894301df8c4a1802ff6150c037e30a8600bfd8143015f8c0a1803bf6550c015fb2a8600ef995430077acaa1802bd6550c01de32a8600efd8d430073ec6a1803bf5350c09df29a8600ef54d4302778a6a1803bf6250c01df3128600ef5894300778c4a1803bf6150c01df30a8600ef5854300778c2a1806bc6150c0
  | 8 => 0x100300600000700500000000400000000200b02200b00500200000300401100205400000600302b00200800200500a00000401000100200000000003600000500300000003a00703000001b00001201100f01900000100900d03000e00000d00401100600502200000400000000e00100000800a02c00001000200000200200200100000500a01c00101900200600b00200e00d00600900900100300300300200100000100a00100500f00000000b00500000e00100400100000100900000900d00000100100100100000200300000d00000200201200100000500000500402900200000100e00b00601c00b01600000000300200700f00000000500400100000101700000500900100000000000b00000000200100100901900800001600200300000400000200200400000100100200300c01000700c00000300000a00200700300400200100a00400702400000300000f00e00e00000200000200900100100700600000600300000000f00300000000000100300502800500700000400400100000200200000000000500000100000000a00200702000000203b00001500000300700600100a00a00100002500000000500000000f00800900a00600000000000700100a00000600e00e00500000200000000600001101d00a00300100b00000400000500000100100000400500600100600100000a00100100001a00700000000001900300800101c00000000c00900000305900100002200200000000d00800600001b00001400300100200000900000d00100100000800100000000100600100a00002700000400701500300001500200000a00000601f00100000800900201e00500800000100000300000200400401400400300200100600300800200200004001b00100201400100000000100000000000700600300200200800000200000a00000400600000000200300000000101701b01100001400100d00e00400500900502a00200400000000600301100800b00300d00700001001801500000000103101100600000300000200700300000400200200100600300e00100800000100500b02400b00201d00000001000300100d00300200300900800001300200000200101500305800a00900d00201800000200800001f000003003000012009001025fcc7aa002fd63d50077f316a800bf58b5400dfcc3aa002fd61d50057f306a800bf58354005facb2a016fe649500bbfaa4a806efd52540067ea92a012fe63950017eb1ca803bf98a54005fac52a006fe61950017eb0ca802bf98254005fac12a002bd659500bdfb1ca800ef98e540077ac72a002bd639500bde31ca805efd8a540077cc52a003bd629500bde314a805efd86540077cc32a006be6195001deb0ca805ef1865402f7ec12a003be6095001deb04a805ef182540377ea8
  | 9 => 0xb8c14c3400000000034c00000000067e7d6000000d3655a0003ac50e9720000000003b6000bc061c48e5a4b9693478a7d0842000c4ace833ed04c90000640b3e55e4c86b8476d1088a3d8af832e86e11a46ad980000007b65902dc29400000053c000c283e8000d50000000ba2278444000bce25238661a000454810a5c12e000da60001526f00007260140fcc646202a620446e2620009703669d8000000244870000000a24000000b7e0002a83324fe0000000e8656d82456000d62a2e11252800000000050c00042c9640001d4d3200000000064e000000952742492d6cbdcb12a9e562000d92b4c892c0cb2c1c23f099ad8a268000b7812c9840004da5fe9c83ce3a2000000510d5a0000004fcc0471e1b4a5a8ec7d801e3c00002220000000000004de216a1e6a8c8a3720da1980007de0005d6798d2e94091ab926f8370db80a2352000a060009ce5b6000102c022c8000a88000000a8e0004b60001a64ce72a1be00077a0c0ba400030ca5e678ab81fca7081c44810e566424e2653e30e7f0b1a000000bb0a4c8363a00e4820508a42266cdee0c000b280002ba41805eaa869c01c390ac2c983aa4204d61845040001cc9e8000b74dc009600000039a4e070e0fab52d7aa28396000000000a967da64a06c0000006da03a0000000000000560000004580004b4000a84d563c44260000000344d2a3a09a532c3a87a4747dc9281281da0000a08443be00000043a4220000000004105f0c1207800082adf05f28a4000000000000d3edc234039e0000000002f07aab6e000000000cae684022762000bf2d0a71a3fa000ceed0e000064000472d46abe4e20b0646686922000826000000b5c00048a8c89f80007683ec2ea9782be9121326aab5e79470400055692613a3580009b2000000000000314136aaa0008220005642086c6b7c8fe16c936224dea7c60006b29181700002920008885f80000000009d60005a6000000000c4ead80008eec3231ad20b6acb6066a2c81e7880006f4da0000bb8c00dfc0008987e60008460007726f61fab0a34e00000029848816e2c4000960b2a00060c000a621b0000000000000150148c66c36000000af64bc06e00000000000029c0000b4bbe00000088e69873c7ca6283f2058c80146a667460002741bc000000c6ed3c7d20000000d00000000001d2664c9eb68abca6c3e212a57ebfca805fcc6259227c9a6d7e000d9e8940ea3621de43ecda000db222619638ae1c7700005ae9c040e8fa9ca5d4710aa000000085c0000009806666546d6c70648000c3ebc6be20ac78457830200000000000000000074ab722020f600000000000600300400100000300200502f00000100500100400200200400201200500200000800c00000300200000000200101b012002001003011026004009002005001003005
  | 10 => 0x5bca5424a1fe07c3d4d229163d09cc0169fc2d441c1e86622288e42b40ca0e25c64a21ee44c3921b8068000cb47ccb88dccc2e000000142324c9c0006e25ceb3a464ca655800000000040400000000001a33487457c2888ccdce76e000bb641a87618010ad16c16304000d48a48c3cbaecb20e097cd6abf67e4d2a644a100008907c20009ec2ee8720000004a40000000000000000000000009740c4212634ae21c60c60600006e6000000178000000bee00058a0000000000000001ecdd60000905dc66827a8c42707e27860000000003a88062ec00072200054400028c42abe6176a16606000c22b306ce9b68e8692a7660e5743eeade5c485e0003108d6000bb48607c034a25664c0009c60000003226ae0000100005f4000000000000e0ab560c27bcb16d3896ebec86ad681725824a80003162b09463360ae55cada0f4000000d9602e00066a2d2c1cbe480ccec0886384f05de4c463ea04c24d0c2d032a09800003600034200000036862e0008f673468a04490c6ca95458e000e1ea3c0005aaaee412000bfa00098a7f2a3094cb0c00049c280956dac42edd2a14d6ec4287caf4218442e1a9ee360c8283a0000001a8aacb14000c5e1b60844d40002aea2247c0004962c073e514afe116c38d9cb9e1646a258057663ac78db6df870881448277eb48ad4364b10b4a0000001c069a21e596a8a5c2092d9491eae800048c0001ae46cbd6ad22fa7b2024a82b3400010831ea40dae0004dc1624ec7eec9249a69008a6c457a0006fe000000000000586346db48ea0009a803e00061493c2aa042376000af2290160118bf48be000050a1c0002a0d060008aac9a500000a8cdf200031cd4a000000000cac37ad86d8c714d6652c000000d1421c0001143c8c186a60d64ca7c4b76d5cb8a00005c1301ac1740863b41245cc00014a126cd000000051ab32dc800000000000080e00011c6cc6bacb80000003f660200000084a78c6d8c2ab042406c233c9e04287aec2c58c0008e2000000000a3468e000000000e0094aa7c98e00038ca180006fc000a26000b384528f2192000c30000000000000b4ebba7fa4f62d6cd42fc992d743d21e6e08b7076a494bb2b50000c7a000624436000140d0026c2cc000bc8c5c0a8c7e0287e83f4018aba18e468c2074c14430625a6000009ae90698ca7ebac00082ecf862cc68a9cb62828850000c6076645e5480005d21d068c00018ccf2dbe732a0e37c77c7064c0000cb0254b028780ec0805da9a2220baa5ac588000b94000a12b080004903caba6cc49d21e4aa603c95ab98570948d40432000000000000000cbc38e9320000008a20000000000aa3c674e000572aceab011000017a00083eb46b5413e90400000004e0007baa648b070abd0190acc0005eac1a0000007fc0b86504b0796ce20000000001e09
  | 11 => 0x6a75c56c0000006d047a00000080a962d70b827923e0a4605a5ba87e5404ac0d2c967a42bc00000073800000000000000099829e000a1a11e000daa3cc0001e2c7424c498000a6e3a6000db04ea00090aba0dfaa4eae459813c4ae5e2c6cd8e2b28d2188aa4bca0008f87be7ce00076c000e2400000051e0009e44f28306588967b8bd8c767ec000000d3a6e8902672cc80006c00001860d40b692c0005a80740006a443c00083c000aea27eb6620ead6816a94cf028a84e000246cd20f8d1c8345b440cd4c000a56300e2037e19ede823203800000041e00a0006b60000000000000084e800045a000000d788e02728d016639c6e4c26000b580000000004a0000000c100dc51c0000f000018a0000000009c2cbac4c00054c0000000004d06160000c8384d1a9dc8f465e9c4ce4604804dc68a02a2a3800099e8ba900402320a900007401a017e930000ae6206d12156c8ed582da000758000000a00072000d763303c200014e84c0000fe9762f6ac65305e6866a022ce45c2de2e817c2389240a6b60ca861885ac94df6988642632d427564be00091cdfe7fe16ac403b8c0a3da75a000b9000000014c6768bc79026e9140007a29da2305ca89e000e1200070200002ab641f0000d0808c5e0e0498200036e16852a0000001543504704849bc54e99635e1000004c6ca4a581c83444c20000003fe43472e30895e52e2145604d86dcb209581a4e186fa538c885c09f67e09de8187d48da7f41f696c000000ca2d64adc7b07a661e864c8613877800010c0008b400ecca9fa808000000df42f4bc215a1ce752cdc59c0000000000f29421941ea000000a20da84800a426a67a4781f85b0000cbe9a481adbca7a052d8089c000be0a92000c501a292e2f88a623a65221a35400009e3fcd0271607a782bde9ba5a21aa880e22cc2000a0c96a8b6a86000bbcd28e027f895c7c8938000862000000d90ad0d600005065ec0ceb4066ec560000000005688c2bf0000aae23e0009f4c72000d52000b42000000bd2000000000680bd467c000000d9a6305be356724d84182da252065a0260bccd6000b86696000000000000ce0de00ba0307120006d40000cc0e6374dde8384cc00022ce060005a0000406b06dba7542c65e88fc000ce678e0000003bc000006ae0b0eb18526ddc8e644e1c494e000b1c0005d80000001f42b600050a0000000000000002820000be5fa000062000000986dee80082c000760b7a93e0009aa04acccb8c0003b00d8ca0b8ec069d02d821088c25c000430440000000486a0a852990082caa3ba854032c489e2d7c88433a4e490846608eaf02cada4cd8dcac468ca97e264c8c79a378d18248776276a727368a853639452424270c2ac9beafa28600c9e64007506d2bc40ee4385b8a328249d40708d49f012004cdc4c58134dd
  | 12 => 0x6a000020c000048000b1e0000000000000007a80008d819c000380a6acc02fe774a521b2bf80000000000002b84b200079ea086ea3980000008689fe2a4d5e00036cdda60a0008f0a3e3a4cce0003880000006e0000000000512de6cf4aca8dc0de002338b2299c542950382584250b846b0cc6a74d3062a61272cdd86368826888582362967ac9b0848b6c6be26079c6743e62e666097a502966afc6ee44acfa3122e04f4258460b005c8856552c1ebfea68d54a36158802d72012910d249eabea32cc5a22a4465e415e9ac8c63dc66c6f2aece145946de8de40a8ac8b8318234cea0460402e21041223f8dd46aca508ce73ad1ec083d600030a5163264aa1ba88625e2c2cfe3ae7ea09c000c44b3c000000000416d44000e0e0002e41064e63e4744414054a9a000ac053a6bc0001d84b8094000ab620ac0e462000de499407ecf600015c000000cfc000de2000c7c0000000003de1dc70078019a02cb5aa785f6ac8000d2c0040009f2a4a81259ebcc5540007303ea62200063c000b9a28e35c968c6a5184fa7b47483b2534000c8455000072054ae107f6000920000ac48ae5d089ad3447e0b2718000608764000000ba824e000b3600000000034856e22e0000005ee9b41cab80ab4694a2a56a000aa26c832892a71cb44decc52be81d67a068293a000944a986ec23c000b260209a00004508b24f82846260006b4bda00086c00007636a00072820075e69eb24000d2659a000e1665c35a000ab2522000d88b2e0000002f28c0000000b9c5466104eed4e4a61f25b290e8324ba67040849e000a44c54a6029a840
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xd6350f1000db47150f1001eae7498b1001ead7498b10006ae5498b10006ad5498b1001ece7398b10004ed7398b1001ecd7398b10004cd7398b10006af4398b10006ad4398b1000ee67198b1000eae4198b1000eac4198b1000eea1098b1000ee91098b10006ae5458b10006ad5458b10004ef7358b10006af4358b10006ad4358b1000ee65158b1000eae4158b1000eac4158b1001cef768cb10004ed768cb10047a4418cb10004ef764cb10004ed764cb1003ecf634cb10026cc634cb100078d434cb1003fa4414cb1003fc6314cb10005b47454710007355454710006e56254710005b4744c71000795434c710005b4744871001ee66248710004bd7599210004bd7399210016ba7099210016b71099210016b51099210004bf7559210004bf735921002cbf7695210004bd7695210004bf7655210004bd765521002cbf76d0e10004bd76d0e10004bf7650e10004bd7650e10014f87058a10006ae648ca10006ad648ca10006ae644ca10006ad644ca10026ce634ca10006cd634ca100078d434ca10005e8725421002eba6450210007c9324c210004bf745951002cbc7459510004df7359510024dc7359510004ef725951001cec725951002cbe76d9110004bd75d9110004bd73d9110006b571d9110004be7619110004bd7519110004bd731911000cbe711911000cbc711911002eb97019110004be769511002cbc7695110004be7655110004bc765511000db47155110004bf7458d1002cbc7458d10004be76d0d1002cbc76d0d10004be7650d10004bc7650d1000db47150d10004bf745891002cbc7458910006af648c910006ac648c910006af644c910006ac644c910006cf634c910026cc634c9100078d434c910014f47654510005b47454510007355454510014f676d051000db674d0510005757510510006b76410510005d57310510005e57210510015f27010510005b6761051000eb6761051000db7751051000f367510510005b5751051000f35751051000535751051000f967310510005b5731051000f95731051000595731051000fa6721051000fa57210510007a63210510007a5321051000fb2701051000fb1701051000eb7601051000fb3601051000db4748c510007c5328c510014f4764c510005b4744c51000795434c510015f27088510014f47648510005b47448510007b0419411000cf87654110036786554110005e87254110007b0415411002eb8649011000df27190110007b0419011000cf87650110007b04150110007b0418c11000cf8764c110007c9324c110007b0414c11000cfa76c8110007b041c8110005797508110005b97408110005d9730811000df27108110007b04108110007e121081100363e65550100063d65550100269e6350c100069d6350c10026ce634c810006cd634c8100078d434c810
  | 1 => 0x43000cbf7610430004bd76104300053d75104300063e65104300063d65104300059d7310430006ae6210430006ad621043000eb66110430006b5611043001ece3258f200269e6350f200069d6350f2001ecf634cb200078d434cb20004bf745872002cbc74587200053d75107200059d7310720005cd7314a20005e57114a20005e97014a20024ef764ca20026ce634ca20006cd634ca200078d434ca20004bf745862002cbc74586200053d75106200059d731062000eb66110620006b56110620005cd73c862000cef764862001de872542200076b5254220004ef725952001cec72d8d20004ee7694920014ec7654920014ec764c920006cf634c9200078d434c920015e8704c92002cbe74d8520004bd74d85200053d75105200059d731052001cf876541200076952541200363e74994200363d749942001e6e329942001cec725942001e6c52594200063e74594200063d745942001e6c725942001e6e325942001e6f21594200166f20594200167a20594200166d205942001e7920594200167a1059420004bd7599020004bd739902001eae329902000cbe7199020004bf7559020004bf735902001eae325902000cbc715902001eaf2159020016ba105902002cbf7695020004bd76950200363e65950200063d6595020004bf7655020004bd76550200363e65550200063d65550200269e7498c200269d7498c200069e5498c200069d5498c2001ece7298c20024ed7258c2001ece3258c200069e7458c200069d7458c200069e5458c200069d5458c2001ece7258c2001ecc5258c2001ecf2158c20016cf2058c20016cd2058c20016da1058c2002cbf76d0c20004bd76d0c200063e65d0c200063d65d0c200269e63d0c200069d63d0c20004bf7650c20004bd7650c200063e6550c200063d6550c200269e6350c200069d6350c20004ed76d48200066d65d4820006cd63d48200066e654c8200066d654c820006ae644c820006ad644c820026ce634c820006cd634c8200078d434c82000eb7749842000eb47498420006b65498420006b55498420006b74398420006b5439842001ee63298420006e53298420016f27098420004bf745842002cbc7458420006b77458420006b47458420006b65458420006b55458420006b74358420006b5435842001ee63258420006e5325842000cbf7690420004bd76904200063e65904200063d65904200069e63904200069d639042000eb66190420006b5619042000cbf7610420004bd76104200053d75104200063e65104200063d65104200059d73104200069e63104200069d631042000eb66110420006b561104200066d6548420006ad6448420006cd634842000ee66148420014f4715931000db471953100363e65553100063d655531000db4715531000db471d0f100269e6350f100069
  | 2 => 0x15ba7010540034bd745944002e3e545944002e9f4358c40026ce634c840006cd634c8400078d434c84002eb44158440004bd7599330026ae3299330026ad329933000cbe7199330004bf75593300269f3259330026ae3259330026ad325933000cbc715933002cbf7695330004bd7695330004bf7655330004bd7655330006ae5498b30006ad5498b30026af4398b30026ad4398b30006ae5458b30006ad5458b30026ce5358b30006cd5358b30026af4358b30026ad4358b300069d644cb3001ece624cb30025cf764cb30006cf764cb30026cf654cb30006cd654cb30026cf644cb300278e644cb30006cd644cb300278d644cb300068d644cb300078e544cb300078d544cb3003ece614cb30004bf745873002cbc745873000cbf7690730004bd7690730006ae6290730006ad62907300078d329073000cbf7610730004bd76107300053d75107300059d7310730006ae6210730006ad62107300078d3210730004ef725963001cec72596300059d73952300078d434ca30004bf745863002cbc74586300053d75106300059d731063000eb66110630006b56110630004ef725953001cec7259530005cd7294d30014dc7654d30005cd738c930014dc764c9300078f434c9300078d434c930006cf654c930006cd654c930006cf644c930006cd644c9300078e544c9300078d544c93003ecc614c930007cb704c930007c8704c930026cf604c930027cb604c93002cbe74d8530004bd74d85300078d32905300053d75105300059d73105300078d3210530007c93294130024f87654130007595354130007c932541300363e74994300363d74994300263f43994300263d43994300266e32994300266d32994300063e74594300063d74594300263f43594300263d43594300266e32594300266d32594300165f30594300167a30594300165d3059430026793059430004bd7599030026ae3299030026ad329903000cbe7199030004bf7559030024bf7359030024bd7359030026ae3259030026ad325903000cbc715903002cbf7695030004bd76950300363e65950300063d65950300059d7395030004bf7655030004bd76550300363e65550300063d6555030006ae5498830006ad5498830026af4398830026ad4398830006ae5458830006ad5458830026af4358830026ad4358830016cf3058830016cd305883000eb7749843000eb47498430006b65498430006b55498430026b74398430026b54398430026e63298430026e53298430004bf745843002cbc7458430006b77458430006b47458430006b65458430006b55458430026b74358430026b54358430026e63258430026e53258430016f23058430026f1305843000cbf7690430004bd76904300063e65904300063d6590430006ae6290430006ad629043000eb66190430006b5619
  | 3 => 0xd541895001ece7318950004ed731895001ecd7318950004cd7318950006af4318950006ad431895001ee6711895001ee5711895001ee9701895001e6c62d49500147c7654950004ee768c95001cec768c950004ee764c950004ec764c9500074d534c9500078d434c95002cbe74d8550004bd74d8550006af6290550006ac62905500053d75105500059d7310550006af6210550006ac6210550004bd739905000cbe7199050004bf735905000cbc71590500269e7498c500269d7498c500369e5498c500369d5498c50026ce7298c50026cd7298c500069e7458c500069d7458c500369e5458c500369d5458c50006ce7258c50006cd7258c500165f5058c50016da5058c500165d5058c50036d95058c5002cbf76d0c50004bd76d0c500269e63d0c500069d63d0c50004bf7650c50004bd7650c500269e6350c500069d6350c50036ae5498850036ad5498850004ed7398850006af4398850006ad4398850036ae5458850036ad5458850004ef7358850006af4358850006ad43588500166f5058850016ea50588500166d5058850036e9505885001cef768c850004ed768c850006ae648c850006ad648c850026ce638c850006cd638c850004ef764c850004ed764c850006ae644c850006ad644c850026ce634c850006cd634c8500078d434c85000eb7749845000eb47498450036b65498450036b55498450006b74398450006b54398450006e63298450006e53298450004bf745845002cbc7458450006b77458450006b47458450036b65458450036b55458450006b74358450006b54358450006e63258450006e53258450016f25058450036f1505845000cbf7690450004bd76904500069e63904500069d6390450006ae6290450006ad629045000eb66190450006b5619045000cbf7610450004bd76104500053d75104500059d73104500069e63104500069d6310450006ae6210450006ad621045000eb66110450006b5611045002e3e545974002e9f4358f40026ce634cb40006cd634cb400078d434cb40014bc7458740034bf76552400063d6555240024bf7650e400069d6350e40026ce634ca40006cd634ca400078d434ca4000eb77498640006b65498640006b55498640006b74398640006b5439864000ee6729864000ee57298640006e63298640006e53298640016f27098640016b74098640016b54098640006b65458640006b55458640006b74358640006b54358640006e63258640006e5325864000eb661906400053d75106400059d731064000eb66110640006b56110640005b9701064002cbc74d9540004ef725954001cec7259540014bc76551400063f6555140014bc7650d400069f6350d40014bc76509400078d434c940014be769054000eb461905400053d75105400059d7310540005ad721054000eb66110540
  | 4 => 0x932101eae729932101eae3299321004bf7559321004bf735932101eae325932102cbf7695321004bd7695321004bf7655321004bd76553210269e7498f210269d7498f210069e5498f210069d5498f2101ece7298f2104e9e4198f2104e9c4198f2101ece3258f210069e7458f210069d7458f210069e5458f210069d5458f2101ece7258f2101ece5258f2101ece4258f2103e9e4158f2103e9c4158f2103ece2158f2101ecc2158f2101ecc2058f2102cbf76d0f21004bd76d0f210269e63d0f210069d63d0f21004bf7650f21004bd7650f210269e6350f210069d6350f21006cd6354b2102eae6450b21006cd6350b21006ae644cb21006ad644cb21026ce634cb21006cd634cb210078d434cb2100cec72583210363e65552210063d65552210269e6350e210069d6350e2100db47150e21024ef764ca21006cd634ca210078d434ca21007355454621016ba7498221016b97498221006ba5498221006b95498221006bb4398221006b94398221006ea3298221006e9329822100eba419822100eb8419822100eeb219822100ee92198221006ba5458221006b95458221006bb4358221006b94358221006ea3258221006e9325822100ef25158221006f1515822100eba415822100eb84158221004bf745952102cbc745952102cbe76d9121004bd75d9121004bd73d9121004be76191210059d7319121004bd751912102e9e7319121004bd731912102e9d73191210049d731912102ead7219121004be769512102cbc7695121004be7655121004bc7655121004bf7458d2102cbc7458d21004be76d0d2102cbc76d0d21004be7650d21004bc7650d210269e6350d210069d6350d2100db47150d2100cec765492102eac649092100cec7650921006af648c921006ac648c92100cec764c921006af644c921006ac644c921006cf634c921026cc634c9210078d434c92101cf476545210073554545210363e65550210063d655502101ece3258c210269e6350c210069d6350c2101ecf634c8210078d434c821004bd739935000cbe7199350004bf735935000cbc715935002cbf76d0f50004bd76d0f50004bf7650f50004bd7650f50006ae648cb50006ad648cb50006ae644cb50006ad644cb50026ce634cb50006cd634cb500074d534cb500078d434cb50004bf745875002cbc745875000cbf7690750004bd769075000cbf7610750004bd76107500053d75107500059d73107500373b5055250026ce634ca50006cd634ca500078d434ca50004bf745865002cbc74586500053d75106500059d731065000eb66110650006b561106500373850551500147c7654d500069f6350d500269c6350d50006ae54d8950006ad54d8950004ed73d8950006af43d8950006ad43d8950005cd731895001eae741895001ead7418950006ae5418950006a
  | 5 => 0x3ecf654ca31006cd654ca3103ecf644ca3103f8f644ca3103e8f644ca31006cd644ca3103f8c644ca310078e544ca310078d544ca31007c7714ca3103fc4714ca31026ce614ca3103fc6514ca3103f8e414ca3103f8c414ca31007355454631007c53254631004bf745823102cbc7458231006cd3258231004bf745953102cbc745953102cbe76d9131004bd75d9131004be7619131004bd751913102e9d731913102eae721913102ead7219131004be769513102cbc76951310059d7395131004be7655131004bc76551310059d7494d3100cdc7654d3100cbe76d0d3100db671d0d310059d7490d3102e9c6490d3100cbc7650d3100db47150d3100cdc7650d3102e9f7650d3100d9c7650d310069c7650d3100c9c7650d310059f7550d310059d7550d31007977150d3100d9e7150d3100d9c7150d31007947150d310269f6150d31027976150d310069d43d8931006af648c931006ac648c9310078d438c931006af644c931006ac644c9310078d434c931007954394531024f4765453100735545453100755535453100795435453101cee72d8131004ed72d81310363e74994310363d74994310263f43994310263d43994310266e32994310266d329943100e3e419943100e3c41994310063e74594310063d74594310263f43594310263d43594310265f32594310266e32594310266d325943100e3e415943100e3c415943100e5f315943100e76315943100e5d3159431026753159431004bd7599031026ae3299031026ad329903100cbe719903100cbc7199031004bf75590310269f3259031026ae3259031026ad325903100cbe715903100cbc715903100e9f315903100e9d315903102cbf7695031004bd76950310363e65950310063d6595031004bf7655031004bd76550310363e65550310063d655503100db47155031006ae5498831006ad5498831026af4398831026ad439883100eae419883100eac4198831006ae5458831006ad5458831026af4358831026ad435883100eae415883100eac41588310065d654c8310069d644c83101ece624c831025cf764c831006cf764c831026cf654c8310274e654c831006cd654c8310274d654c8310064d654c831026cf644c8310278e644c831006cd644c8310278d644c8310068d644c8310078e544c8310078d544c83103ece614c831027c6614c83103f8e414c83103f8c414c831027ca604c831027c9604c831006ba5498031006b95498031026bb4398031026b94398031026ea3298031026e9329803100eba419803100eb84198031006cd3258031006ba5458031006b95458031026bb4358031026b94358031026db3258031026ea3258031006d93258031026e93258031006c9325803100eba415803100eb8415803100ef23158031026f13158031004bd7599321004bd739
  | 6 => 0xc5158c4100e9f2158c4100e9e2158c4100e9d2158c4100e9c2158c410069f7058c410069e7058c410069d7058c410069c7058c4100e9f1058c4100e971058c4100e9e1058c4100e9d1058c4100e9c1058c4100cbe76d4c41004bd76d4c410063d65d4c410069d63d4c4100cbe7694c41004bd7694c410063d6594c410069d6394c41005ae7294c41005ad7294c41004bd7654c410063d6554c410069d6354c41005b77154c4100db47154c4100cbe7614c41004bd7614c410063d6514c410069d6314c41005ae7214c41005ad7214c4100db67114c41005b57114c41005ba7014c41005b97014c4100cbe76d4841004bd76d48410063d65d48410069d63d48410063d65948410069d63948410063d65548410069d635484100cbe7614841004bd76148410063d65148410059e73148410059d73148410069d631484100db67114841005b57114841005ba7014841005b9701484100cbe76cc841004bd76cc8410063d65cc8410069d63cc8410063d658c8410069d638c84100db6718c841005b5718c841045af768c841045ad768c841046af658c8410472e658c841006ad658c8410472d658c8410062d658c84103dad738c8410478e638c841006ad638c8410478d638c8410068d638c841047a6718c841007a5718c841046ae618c841047a6618c841047aa608c841047a9608c8410063d654c8410069d634c84103daf764c84103dad764c84103eaf654c84103f2e654c841006ad654c84103f2d654c8410062d654c8410078f734c84103f8e634c841006ad634c84103f8d634c8410068d634c8410078e534c8410078d534c84103eae614c84103fa6614c84103faa604c84103fa9604c84100cbe760c841004bd760c8410063d650c8410069d630c841045ae720c841004bd75993310269e7399331026ae3299331026ad3299331004bf7559331026ae3259331026ad325933102cbf7695331004bd76953310059d7395331004bf7655331004bd765533100db4715533102e9e6450f310259f7650f310069f7650f310059f7550f310059d7550f310278e6250f310278d6250f3100d9e7150f3100d9c7150f31006ae5498b31006ad5498b31026af4398b31026ad4398b31046ae4198b31046ac4198b310069d4358b31006ae5458b31006ad5458b31026ce5358b31006cd5358b31026af4358b31026ce4358b31026ad4358b31006cd4358b310068d4358b3103eae4158b3103eac4158b3103ece3158b31026cc3158b31004bf745963102cbc745963100cbe769523100cbc769523100cbe765523100cbc76552310363e65552310063d655523100db671d0e3100db47150e31004bf7458a3102cbc7458a3104e9f64cca31046af648ca31046ac648ca3101cdf764ca3103e9f644ca3103eaf644ca3103eac644ca310078f434ca310078d434ca31
  | 7 => 0xc94102e3e749944102e3f439944100e3e419944100e3c419944102cbc745944102e3e545944102e3c545944102e3e745944102e3c745944102e3f435944102e3c435944102e3f425944102e3c425944100e3f415944100e3e415944100e3d415944100e3c415944102e3f405944102e3c405944100e771059441004bd76d50410063d65d50410363e65550410063d655504102e9e5498c410069d5498c41026ce7298c41026cd7298c4100e9e4198c4100e9c4198c4102e9f4358c4102e9c4358c4102e9e7458c410069f5458c4102e9e5458c410069d5458c4102e9c5458c41006ce7258c41006cd7258c4102e9f4258c4102e9c4258c4100e9f4158c4100e9e4158c4100e9d4158c4100e9c4158c4102e9f4058c4102e9c4058c4100ed71058c41004bd7690c410063d6590c410069d6390c41005ae7290c41005ad7290c410063e6550c410063d6550c410269e6350c4102eae5498841006ad5498841004ed739884102eaf4398841006ad439884100eae419884100eac419884102eae5458841006ad5458841004ef735884102eaf4358841006ad435884100eae415884100eac415884102eaf405884100ee710588410063d65908410069d6390841006ad62908410063d65508410069d635084101eae625084101cef768c841004ed768c8410066e658c8410066d658c841026ce638c841006cd638c841004ef764c841004ed764c8410066e654c8410066d654c841026ce634c841006cd634c8410078e434c8410078d434c84102eba5498041006b9549804102ebb4398041006b94398041006ea3298041006e9329804100eba419804100eb8419804102eba5458041006b9545804102ebb4358041006b9435804102ebb4258041006b94258041006ea3258041006e9325804100eba415804100eb8415804100cbf755944100e3f7559441004bf735944100cbe715944100cbc715944100e3e515944100e3c515944100eb710594410063f73594410063e73594410063d73594410063c73594410063f72594410063e72594410063d72594410063c725944100e3f715944100e3e715944100e3d715944100e3c715944100e3f315944100e3e315944100e3d315944100e3c315944100e3f215944100e3e215944100e3d215944100e3c21594410063f70594410063e70594410063d70594410063c705944100e3f105944100e37105944100e3e105944100e3d105944100e3c1059441004bf7558c4100e9f7358c41006ae7258c41006ad7258c4100e9e3158c4100e9c3158c4100eb71058c410069f7558c410069e7558c410069d7558c410069c7558c410069f7258c410069e7258c410068e7258c410069d7258c410068d7258c410069c7258c4100e9f7158c4100e9e7158c4100e9c7158c4100e9f5158c4100e9e5158c4100e9d5158c4100e9
  | 8 => 0xe3f515905100e3d51590510269e7498c510269d7498c510369e5498c510369d5498c51026ce7298c51026cd7298c5100e9e4198c5100e9c4198c510069e7458c510069d7458c510369e5458c510369d5458c51006ce7258c51006cd7258c5100e5f5158c5100ed65158c5100e5d5158c51036d55158c5100e9e4158c5100e9c4158c5102cbf76d0c51004bd76d0c510269e63d0c510069d63d0c51004bf7650c51004bd7650c510269e6350c510069d6350c5100db47150c51036ae5498851036ad5498851004ed7398851006af4398851006ad439885100eae419885100eac4198851036ae5458851036ad5458851004ef7358851006af4358851006ad435885100ee65158851036e5515885100eae415885100eac415885101cef768c851004ed768c851006ae648c851006ad648c851026ce638c851006cd638c851004ef764c851004ed764c851006ae644c851006ad644c851026ce634c851006cd634c8510078d434c851036ba5498051036b95498051006bb4398051006b94398051006ea3298051006e9329805100eba419805100eb84198051036ba5458051036b95458051006bb4358051006b94358051006ea3258051006e9325805100ef25158051036f1515805100eba415805100eb8415805102e3e545974102e3f655534102e9f4358f41026ce634cb41006cd634cb410078d434cb410063d65d524100db671d5241005b571d5241034bf76552410363e65552410063d655524100db47155241005ae7290e41005ad7290e4100db67190e41024bf7650e410269e6350e410069d6350e4100db47150e41005ae7210e41005ad7210e4100db67190a4101cbf7650a4100db47150a410059e7310a410059d7310a410078e434ca410078d434ca4100eb4415824100e3f7559641004bf735964100cbc715964100e3e515964100e3c5159641004bf7558e4100e9f7358e4100e9e3158e4100e9c3158e4100cbe76d4e41004bd76d4e410063d65d4e4100cbe7694e41004bd7694e410069d6394e41005ae7294e41005ad7294e41004bd7654e410063d6554e410069d6354e4100cbe7614e41004bd7614e41005ae7214e41005ad7214e4100db67114e41005b57114e41005ba7014e41005b97014e4100cbe76d4a41004bd76d4a4100cbe7614a41004bd7614a410059e7314a410059d7314a4100db67114a41005b57114a41005ba7014a41005b97014a4100cbe76cca41004bd76cca41046af658ca41006ad658ca41006ad638ca4103eaf654ca41006ad654ca410078f734ca4103f8f634ca41006ad634ca4103f8c634ca410078e534ca410078d534ca4100cbe760ca41004bd760ca41004bf7459541004be769514100cbc76551410063f6555141004be76d0d4100cbc7650d410069f6350d41006cf634c941026cc634c9410078d434
  | 9 => 0xf7550d32005ad7550d32025af7350d320078f7350d320078f6350d320078f5350d320278e5350d320078d5350d320278c5350d3203dac7150d320278f3150d320278c3150d320278f3050d320278c3050d3201dce7650d32005cc7650d32005cf7550d32005cd7550d32025cf7450d320278f7450d320078f6450d320078c6450d320078f5450d320078e5450d320078d5450d320078c5450d3203dcc7150d32005cf7050d320078f7650d320078e7650d320078d7650d320078c7650d320078f7550d320058f7550d320078e7550d320078d7550d320058d7550d320078c7550d320078f6550d320078e6550d320078d6550d320078c6550d320078f7150d320078e7150d320078d7150d320078c7150d3203d8c7150d320078f7050d320078e7050d320078d7050d320078c7050d32005ae74d8532005ad74d85320078d43d85320078d4398532005ea7098532005e97098532005af7458532005ac74585320078d43585320078d43185320078d43d81320078d43981320078d43581320056e75181320056d7518132005ae7418132005ad74181320078d4318132005e67118132005e57118132006e96018132004bd759903201eae3299032026ad329903200cbe7199032004bf755903201e9f325903201eae325903201e9d3259032026ad325903200cbc715903202cbf7695032004bd7695032004bf7655032004bd7655032006ae5498832006ad549883201ecd7398832026af4398832026ad4398832004bf745843202cbc7458432004bd7399351004bf735935102e3e64553510353f76553510063f76553510053f735535100d3e715535100d3c715535102cbf76d0f51004bd76d0f510053d75d0f51004bf7650f51004bd7650f510053d7550f5100db47150f51006ae648cb51006ad648cb510072d548cb51006ae644cb51006ad644cb510072d544cb51026ce634cb51006cd634cb510074d534cb510078d434cb51004ef725835101cec725835100db6719525100db47155251037375155251004bf7458e5102cbc7458e5100cbe76d0e5100cbc7650e510269e6350e510069d6350e51004bf7458a5102cbc7458a510078d434ca51004bf745825102cbc7458251004bd73d9151004bd731915102e3c64d515100cbe76951510053d759515100db6719515100c7c765515100cbc765515100db4715515100c3c76551510053f735515100737715515100d3e715515100d3c71551510073471551510363f61551510373761551510053d74d4d5100c7c7654d51004be76d0d5102cbc76d0d510053d75d0d51004be7650d51004bc7650d510053d7550d51006af648c951006ac648c9510072d548c951006af644c951006ac644c9510072d544c951006cf634c951026cc634c9510074d534c9510078d434c951004bd7399051004bf7359051
  | 10 => 0xf32004bf745873202cbc745873201cdc73587320069d435873201cec725963201cec7259232005ae74d4a32005ad74d4a32004bf745863202cbc745863201cec725863201cec725823201ee82058232005ae7499632005ad74996320072f5495232005ad7395232045ae71952320072f7555232005af7355232045ac7155232005ae74d4e32005ad74d4e320274c5354e32005af75d0e32005ad75d0e32045ae71d0e32005af7550e32005ad7550e320078f7350e32045ac7150e320278f3150e32005ea7098632005e97098632005af7458632005ac745863201ee86058232004fb7059532014f870595320059d73951320059d7494d3201dce7294d3201cdc7654d320365c6554d320059d7490d3201dce7290d320278c3250d3201cdc7650d3202e9f7650d320069c7650d320059f7550d320059d7550d320078f7250d320078c7250d320269f6250d320278f6250d3203d9c7150d32024ee76d4932005ae74d4932005ad74d4932025ce73d49320078d43d49320078d4394932024ec76549320078d4354932005ae7414932005ad7414932025ce73149320078d4314932005e67114932005e57114932005ea7014932005e97014932024ee76d0932025ce73d09320078d43d09320078d4390932024ec76509320078d4350932025ce73109320078d431093202cbe74d8532004bd74d85320069d43d8532005ae7499532005ad7499532005cd7399532005cf7359532005eb7059532005e87059532005ae7419532005ad7419532005e67119532005e57119532005ea7019532005e97019532005cd7399132005cf7359132025ce73d5132005cd73d51320072f5495132025ce7395132005cd7395132005ad75951320078e7395132005ad73951320078d73951320058d739513203dae71951320072f7555132005af73551320078e73551320078d735513203dac7155132005ae7415132025ce7315132005cd7315132005cd75d8d32005cd74d8d320078e54d8d320078d54d8d3203dce71d8d32005cd70d8d32005ae74d4d32005ad74d4d320274e53d4d32005ce7694d32026ce7694d32005cd7594d320278e7494d32005cd7494d320278d7494d320058d7494d320078e5494d320078d5494d3203dce7194d32005cd7094d3201dce7654d32005cc7654d32025cf7554d320274f7554d320074f6554d320074c6554d32005cf7454d320078e7454d320078d7454d320078e5454d320078d5454d3203dcc7154d32005cf7054d32005af75d0d32005ad75d0d32025ad73d0d320078f63d0d320278e53d0d320078d53d0d3203dae71d0d320278c31d0d320278f30d0d32005ce7690d32026ce7690d32025cf7590d32005cd7590d32005cd7490d320058d7490d320078e5490d320078d5490d3203dce7190d32005cd7090d320278c4350d32005a
  | 11 => 0xcbc7159543006b4715954300cb47159543004be76195430059d72d8d430059d71d8d43004be76d4d430063f65d4d430271e53d4d43004bd7654d430063f6554d430271c5354d43005b67198943005b571989430053e75185430053d7518543005ae7218543005ad721854300eb66118543005ba7018543005b97018543005b67198143005b5719814302e3e545944302cbf7599043004bd759904302e9d7399043004bf765504302eae5498843006ad5498843026af4398843026ad439884302eac419884302eae5458843006ad5458843026af4358843026ce4358843026ad435884302ecd435884302eac4158843004bd739935200cbe7199352004bf735935200cbc715935202cbf76d0f52004bd76d0f52004bf7650f52004bd7650f52004bf745875202cbc74587520372f525525201ece3258e520269e6350e520069d6350e52004bf745865202cbc74586520372c525515202cbe74d8552004bd74d8552004bd739905201eae329905200cbe7199052004bf735905201eae325905200cbc71590520269e7498c520269d7498c520369e5498c520369d5498c5201ece7298c5201ece3258c520069e7458c520069d7458c520369e5458c520369d5458c5201ece7258c5201ece5258c52036cd5258c5201ecc2058c5202cbf76d0c52004bd76d0c520269e63d0c520069d63d0c52004bf7650c52004bd7650c520269e6350c520069d6350c5200eb7749845200eb47498452036b65498452036b55498452006b74398452006b5439845201ee63298452004bf745845202cbc7458452006b77458452006b47458452036b65458452036b55458452006b74358452006b5435845201ee65258452036e5525845201ee6325845201ee42058452036ba5498052036b95498052006bb4398052006b9439805201eea329805201ee82058052036ba5458052036b95458052006bb4358052006b9435805201e7b525805201eea525805201e795258052036e9525805201eea325805202e3e545974202e9f4358f4201cbc7458742034bf76552420063d655524201ece3258e42024bf7650e420269e6350e420069d6350e4201cbc76551420063f655514201cbc7650d420069f6350d4202e3e545944202e9e5498c420069d5498c4201ece7298c4202e9c4198c4202e9f4358c4201ece3258c4202e9e7458c4202e9e5458c420069d5458c4201ece7258c4201e9f4258c4201ece4258c4201e9d4258c4202ecd4258c4202e9c4158c420269e6350c42004bd75993320269e7399332026ae3299332026ad329933200cbe7199332004bf7559332026ae3259332026ad325933200cbc715933202cbf7695332004bd76953320059d7395332004bf7655332004bd765533202e9e6450f320259f7650f320069f7650f320059f7550f320059d7550f3204d9c715
  | 12 => 0xd76d52540363d76d525402cbc7458e5402e9f4358e5402cbc7458a5402cbc745865402cbc7458254005ae7298e54005ad7298e5400cbc7158e5400eb46198654005b67198254005b571982540053d71d955400cbe71d8d54005ae7298d54005ad7298d54005b77158d54005b47158d54005ae7218d54005ad7218d540059e73189540059d73189540059e73185540059d7318554005ae7218554005ad721855400eb66118554005ba7018554005b97018554005b67198154005b57198154005af7258154005ac725815402e3d759905402e9f4358c5400cbe719935300cbc71593530363f5159353004bf745875302cbc7458753004ef725835301cec7258353026ae3299253026ad329925300cbe71992530269f3259253026ae3259253026ad325925300cbc71592530269f31592530059d73952530059f73552530371f5355253006ae5498a53006ad5498a53026af4398a53026ad4398a53006ae5458a53006ad5458a53026af4358a53026ad4358a53026cf3058a53004bf745865302cbc7458653005b471591530059d73951530059f73551530371c535515302cbe74d8953004bd74d895302cbe74d8553004bd74d855302cbe74d8153004bd74d8153026ae3299053026ad329905300cbe7199053026ae3259053026ad325905300cbc7159053036ae5498853036ad5498853026af4398853026ad4398853036ae5458853036ad5458853026ce5358853036cd5358853026af4358853026ad435885300eb7749845300eb47498453036b65498453036b55498453026b74398453026b54398453026e63298453026e53298453004bf745845302cbc7458453006b77458453006b47458453036b65458453036b55458453026775358453026d65358453026755358453036d55358453026b74358453026b54358453026e63258453026e53258453036ba5498053036b95498053026bb4398053026b94398053026ea3298053026e93298053036ba5458053036b954580530267b5358053026da5358053026795358053036d95358053026bb4358053026b94358053026ea3258053026e93258053024bc745974302e3e5459743024bc7458b43024bc7458743024bc745834302e9d73d974300cbe71d974302e3f659974302e3f755974300cbc71597430063d65d4f430063d6554f4300eb46198743005b67198343005b57198343034bf76552430063d6555243006ae5498a43006ad5498a43026af4398a43026ad4398a43006ae5458a43006ad5458a43026af4358a43026ad4358a43004f7715954300cf47159543024be76d51430063f65d5143024bc76551430063f6555143004be761514300cbe71d95430063f65995430059d73995430059f7359543005b77159543005b471595430063f7559543004bf73595430069f7359543006b77159543
  | 13 => 0x200100000000000400400000200100300000000000900d00000100000100400500200100000001000900900000100700100100700300800000200500200000200100100700200000000700000100000100700200500000300100100100600000000400300100100100500300100000000700300100400500100100500000200100200000900000000600000100a00000000700800c00100000100100500000000000c00000100800200200100000700000000000600200500e00200300200000200000100f01b00500400800200200000000100500700100500000000200000200400000100e00000000100000000600d00200100000100400100000000200200000000100200600900000100300000300500400100000700000300400100400100000401a00300000c00100700200900000000000002900400100000600300000000000000000500200200000200400100100000000000200200f00300100700200c00800400100300300000000800100400000400000700000100600100000100000e00300300000000200100700000000200100400000200200000000401400200000000100100500000200000100103900300100000000200300c00100300001100000200000600000700200300000000000000000200000700600000000000700000100000100000000f00700000400400700200300100000500200000400000200000000100300100000b00000500100501100100000200100000300000300000a00600100200500000601400100000000700700200500a01c00801100000100000000200100200300200500400200800000100000000100000300500300300d00400000200300000100500000100100200500300000400101600700000000000400000000400100200100200000100000700400100500101400700000000800000100200600300700500100000500000100000000000000500300000000000100200100501200100300000100000b01c00200000200000200100400000400000000201400000000100000300100100a00000100200100600100400000900200100300000000200400e00100000f00000000300400500500a00500000200000200400400400000100100100200000300000500100200100000400400400101f00900000100000200000100100800400000600000f00100a00300000900100600100700200100600400000000200400000000300000900400000b00100200300700600e00000000000600200600100600100000300200000700200000000700000400400000000100000200000400000000000100000e01700001000200200500100200000000100200e00700500200200200500600400300400100300500000300200000400400200100000100000000300200300800b00400000002d3
  | 14 => 0x1f022900000010dc2d43b9893827213433080011287b040f000017c75e346000114c460000000033a0b13d3827846670a20997e47385a5311000059c00003000009bc1a82a3994011017e0731cf025c3c1389939089465b01181f4b344470b79a9c90668b00001f00001bf42480009b86b03769040ed84920341e6d0d863c29c9c50b3a5d33e51d3c000000000000019009d0fd04ec00000000000000000e80ca1140e201100001f8814a2a23dc0eecb140004381e2c8c40003e20ee0000000000000048600030099540000002b21a9107a0002539a7c2c00003ef80010540c12ea9a4c138000000000000028900011f86402c8361800000079d00006649d4729000035c0008520d09d4901e0000000000f5e6cd0b508e40002eb0000c004ee6f80001264c1a39600002a4ad487f02584441080b70000bbc4b002125b0fa8f568a73d096800000000001fd10861c439d07ec9160000001fa881077b19b00007e00000001cc411c00025897280004eb042830110a54e28f8000d302180000f3103400021c92b8b6878c3d18330d1c3e500712d08844290000000f5c000063a2a40e684612f800072e00000013590ee2260001464e7e7f30ee12eccfe00000002000000b63e400bcc7a7690000254d7a7b722306f8a5a57800000001da6d32aea16c8360000f10000b5869a00016e049400037200007c200000011a506432210d0000dea0002ab000000000000000007a46b600012c083e7bc00011ac69641524205702ae3d32e3979c80226700000000001b22799b58a3887920700000000000000f287b266619a00002ea0000000000b38000000000000000035687c0000106000000000000003f80004fa0000f30000000000000000029a7dd000094841859332e85740002e4000000075a00000000003aa08b2f717ec0000000000aa4eb87d80002034000000000086c0003f83978000000145000098414286000007d43e60000001618ad83a51bd0d04000000000000093a000000000000076600015307d60483141e7c2a66c800000000000722a800000000000000000d4400033b12940000000000000000000348800000000027920000000003731200afa0000000decc4000000000000000001e3800000083e1e400000000003b000000004f70000c5c80485807e80003581bb31a8000c5e0002d816fcf800000001f545cc07600008fc0983fc00000ac000000278800094c36000000005b204312b00004c81c100006f0ee83bc3ed922508853f100800000000023880000000001c387b800000042f00000000000db187000000300300201000300000000400000200300000400100000100000400100000100300100000200900000000400100100b00100100000000200000700000100600200300100400200000100200000100500100000000300
  | 15 => 0x34180003fe00000003ec81254300000004ec69d079813c0020001ab1ce401479500019b0cc82ea00005e0a0000000000003ba00006a80000000004108c444b430729c1b2c2be53318f0000bea0000000000d5e5750000f90370689000165c00000000001dc00053b2f48000a264e939600003303851b700000000003a18000e080001bc8000ee05370001fec2f40002f285a4ace6fa0d81fe47100000001f080005fc00000000000000921e78c046b80321da81be0004420e1112a0002189d5800057b1ac0328000000000000000087e29710907fa05525f875c0008a51968b2509854138e84cc0fc0000000000b0403c00000000004383d90c845ca01b21390d80824651329e5d10e56110385fc0006d90000fd85ee48733100002aa6c105100007b07cd3439a210580002118c8cc620000001614c7474c0a0800031200036d962c8cc62a1db20ec3b283019322a89d015a1ea858c03000007a8000e0c44809b0ac44da00040700002ac15e10518fc6fc38200013bc00017c00005cc65c000000052c00000000000006ba0000000000b5e0000001d909ce16d000000000008f3f900000005223ed054405400011781b08da00000000940000002648530000143000173c5260003aea2580007b41fc843841a0002d700006fa84f000000000078a0270230368000051800062600022f927c0007ef1d60000cae6c700019d039e0000000f2c02e000250800042c6d72200f40ed66370e98b80e8451a21719f832e25b0001928b1a0b4152800000049e17080000000003cc1ef40000001288450a4c0490001d942807cf17f80000000003f8000008c31d00017749aa00000006b8700000000156456812508d13d40000002719f242300002078e2c5a685145180300220000b380000008562e6000000087c00000000003c91e20e389be2f50939798556033000000000000012a0000c06507122000062c000000045406e044389152cb7c000038000000017d1200e280000000000d105d81882f00eac6aa00023e8000000034000186c00026e00009782704a8131800000000000380004824ca0000e448f2000000134c4840ab3e380009c400000020480008553778000f0477e11b21d44e67e42f98ea85200002f892cc5060d2446155c92c34d000101099e000417800000054f000000113218b0079a98ba023700000006d420e0a3000047000000000002940133d69ac800058400000006a6000000000053a0001dfa2901d64c800021d8c4c000000000005c81439387a4e6c39f0e70c5491a3c64399f180002a83a396f4616718000202400035f0dc88b0346719000114c63411e33692501a230100019f00000002e1000055e2020001408cd688b0000db00000000000000fdc05100017bc4b889718a1ed838e60b029800058400000d16f00000d319799ec
  | 16 => 0x3ff16240b081d00014c82001172830000cb83db409a12863800000000000005722a28000ab47910d0000084a0001668d986fe6992110c34f2c73e19b93b0f9c0002af94800000000001d4c0ba6a300193386d60c200000000000000000000d880000cf8000f6a0b202500000000000001144e1c00000000001ee4b90b080000000000000d940000000000000c5677c096186400000023b9d1800050e2769ee80007070cd02e0b207e80f00ed48a41120780018df283a00022840001051b08810eec0002bf85ac000000000000000000039200007fc000000130400045d00000006484af05e88a00000002ba0000000000215115d0b43cd33c00000f000000000006843c50001cd4000119044960ca56634014800000000041b9f9887c3ec000000077200015b80000000002caa0310de00000012e01f400037700006c6610434000000000000000000005ed32f800000057000000000000000000000000883349124c0006f2000112cab865e000016912450d0000a5c0002153ce00e400000002f8000b0e000373800000000027c8000e228391da11d0000000115800000041e00000000000002bd1828000000000000000000038f800000039231c00000000000000000ac0000421000000038c0000000dd80003df0380aaa6470000000824609000000108e1fd1d980000000000000ca00004c700000000004863f880000007c51a7963cda433841297500000000000000000000135910c00019e37b971800000024514c0000459000000075e3710370000000000009000065200035982bc0007e903391e8e0468213800000000000001fdc572000000000000000013a994848e223401000000025900020c495a2322b989742506461a72014000219000036c02000008e80002a405e0348e84a2e5341d8a00ce427bb06208ec2a88080418c148562de0de90f000002035f8000420000084146c7a800040b000000001905387343b647816221c451e00000000003e4000000069ca2c32c112a028204357000079426000002696046301e70e615200ea00000002fcb807a004a0fc8bee6a100010cc17623c1bb9c0478600026a075030c00034796d40000000e30cf00003f700000000005fa068135c0000000000000a9a000000172d03046f000071466a000000021c000340281800000081f2fb1d640806052891c00c103f109793f00005580001b84ec40003fe800000000019d90c800000000002183da69b000000041e03f35a998000006f2260af000000000000000002780e51fd80000003c99d50e5a4970000000000343000000000000035e000000000017b0d2456c6be28480000000000000c3ca0a7d401401ec764000077945508a8013f01bed0900001b40b141e2684364827cde85a61fa08800007ed31c9ee40002ed0001c0c542000
  | 17 => 0x5000000000000000011b87447510001cc855c50100000000000000c70d1905200000000000004cb31221ece9670927c14404fc4da38f1958000000324a260e663483e9800000000006d168503289d000000070685909922408b05143070f3c59642d4369ea00006d032696a00003450000f0800012100022a0d4056f07187aca1e643284095cce400000000000006bb0000000f28000270a27c3047882a51430ce66583cd0c24e401c909f9dbcb2c0003ad9b447304d1000000000064f3c30a2cdbc0aa2c0000000031015e8000c580002399550d5c00000000001505272fa17fcdf83e80000000e560004170edc000000000000000030802a0000bc803027d0561078000000000043a6e00ef80006a843000000000000001151b740002b0181981c0000003af90bcc2c1791cf000000056b0002100000000096800000000000000000007891998d78c2410119c800054e3e0030981815c14e17c0f9886a0000000000292717094a2786ea2bb0000f8ccdc2ad41206dc00000004b800000000000000000000001ad80001d40002eb8cc902023d2d6800000065141391141d82b300000000b852541a885c00046300018b400088900000000746480d505986ec33d37ea234b367aa0000b690ca41a2cc80002382130001d00fea4e00000db4cf200028c1d407ce196000000000000007701c4fae1950e180007de000000000000043b013a1e0e922df0000000000000000039cc8477d07f995058200d0f09ab0b1026a35d0b5400035235b8f74d5662737b175827800011880000000000001c205a22cc2f19a783c81910ec184c91c0000001cd000000000000000004000000820500000031199400000000000000000001d711b05ba180198000020e0000c296a80000001430508000000000000050e000000000000000014d8bf000066712789c8dfc00036780001e83742ec80006980003e0971400000000013f40004910000694000000000154cec600000003f0c8a00043e80000002b83d216c50160003c69d84e9c0000d69900d2c33f10f8000eda0000369394b523512038768f062be193805808e295273219c000148000000018c1a201d8a0907e0000988d4012c3a41890000de63992590e685f67b1155000000012b20e976cb723fb000180000024b2628000edc00000000006ce5df37880c48745922fc0a44f1e6ca1820bc80000000000000f4c00005683707744a4000089d13857c00000000005c400000000a45da35500008a810900014d8000000000215045a2e700017acef051d0000264a8c41600000000007e500011f08421de1e88f380b272323504dc6f021c2f916ec7fe24d00014f40004881c3185000047600000000001fe411000000001e000000000000000000003740002f5168cdd00000000000a881ec00001ac97800024a800
  | 18 => 0xe80006971ca9d5c94000023a8f0057e00023900b400a23e43915d8eee09814c89d07dc000000043c000000000093084028420c8000b9a16804807a01243192dd226812211327a17040d477500000000003bd00000c8b441773930000a5460c01300f43e241734506907b423414f16c89b2000000223c00011b045000000007a00000000001830210000930531101894c00040b00000003f239d00000010e80002b400001ec08d3d600003ac2c3335056c6b8000294223912231b29787a834c12a35a0b483ec5c344100f90d400019d000000000000019c05e61d2444000000000000000007da29800010b035e59f311a18858c0003bc9fe800000000000000006da14e1e64f025294451aa00007f817a080000000000020d00f268122792a4d2a0000000b0053e2500ce1d04fc200000014280000a009f16ac000000000000083800037180200000000000c7c06c0001a3901891e39000018c00001a938e00003a20020b800000000000000ba44f40000000000d8037200000000000000000a8000000006b000045c1b137112e80000002661014fb24db000000000035a00000000000000000e980000003f191fcbc200016782e80e885f23d82980000001b1228800000000000004426d50000bf8416000000000000049a00000008ac10c14280000000381d018a4afc359145000000000000000000000002bc90f40000000001f48c4a081000036000000000003a4e5071a000032c36618f41400003f8838000000000000007110dc40c00013d8000f085fd0000000534000000000016a00000010505940000e5a1045fa40c2428b700002f92920e6c0004be15208787d27cc39c048d05a000000100d10c3be0000000000045000000046019300021740002810330480ab600000017700005ec1348caca923a30000334d0c88000000005b667a000000000000000000000000000000000abc00007c8000000000000163000000000021402086113e822042e8725000000067c27f05613409a47eb3a4226c5462e81eb9f2c0000000000000bc400015a800000002428f1f70944853419861c1047ff0679d603f07d1000169cfce01d16c000000000040d800000017239e973831400000000011262143bf9cb85c64b52601854d8c61826e81586541ab241204500c8690161d2827400038b19382ec13532c92dc29e7442821184e600001121de8e8a66f0f796784747873d10000d8a6d40000e4cf7e7de3aa891800064400000000000001b49a947504c232d169100e18d1089ea40000003749c3404463e0000df00006d808500000000e5000000000052c000000000000014700509ec8170000c3000061f12496dccd085708698840004812b6800095600033e8000000000000002cc2e000000148427a6cc0000e04d1a05b00009a0dd4000000000000025
  | 19 => 0xfb800000000011a800000000033a8000000000000000000000036e09800c600031920d80008260b290983185353eb1dc40002ee25614f0aee122425942c60c7850e4047cbbc49c41183c897a0000000000acc00034000000000000000000dca00000000000000001c480001ba09b1f100000004ff000001000000000000001b20003171ae40000002ca0b5c000000000000081a4671a51d34d5200000e0000a800003b3858889c20933882683c600000019a40007150e11c8909a000307800000019200009889dc0e114b10a054c19b0000f700006630000b1c00000006a0e9cc3c3a900000000000000001b082d83fa00000005640000000000012000000213802a78033b9dc8574000000000064a00000000000005fe00000000000001029a145240000000000a46164168000000064b00007d0e160ce39b800000001f0000000eb445b22f042c5ac4f006191703020003e18140528000000000000000000000005f45c8000194c00022207f08482dc4aa0001e4019269426200008220001eb0d9000072a00000008c80001229bac00058e000000087e1b51fa91343a00b927f0564c664413781c3018a70f3fe13190c26362b497c060439426180001c869040e15882e28150bd86409365d22a1040cb9282b0a380004f869c3020dc0e0a63b000000000000000019300000000001b3800038d000054024c864000000017800021a0dccbb05e830d16d81bc24823416440000000000000000000000128c00028d00000008920570000ab01601c02460dbc8e05d11788194000000000000006a000136000066271b00020100000000000ec07e62f005213ec9206df2889bfc8aa00000000010f40000000000ac68661ef8c2871e27100000000005520001ac499a8a013c8f790d62e22b70000c3a8202d995c4e7626600005105187ec3b41904a7c0003c91110000000205045800000000002cc00078e3d291690c600042e09bcaca0000c21660f664d82a8824c61c28820c14
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xcb2615c0419000316902bb2a998002a3e15644cb3003d4640ac89966000a8d8695132cc00151b0caa2659801f23dd9329073000616bacc420e6000c8d7398841cc00185aeab108398003235cd621073000646bb26420e6000d0d754c841cc00386cc2ba883180072598573106300061abaac220c6000c9573584418c0071990eb2a6498002d2614704c930005e0c08e09926000d0d754c8414c00183acab9ca818002a360e54588300051ac28e8b086000a9583951610c00313b06bb082180020fe19751043000e1b30aea208600083d87994410c00107b0eb2882180030799573104300060eb2ae62086001c96615cc410c00185aeb3108218003235ce621043000616baac42086000c8d73588410c00186aeab088218003255cd611043000e1b30aea20c4001c96615cc418800186aeab088310003255cd611062002546c12c6a184000a8d83991320800151f0ca1a6410002a3619434c8200070732a869904000e0d6550d3208001d0a86994c2100028d61474584200054ac18e8b084000e85434c9610800107f0cba882100070d98575104200041ec3cca208400083d87594410800113f0cb9882100030799573104200060eb2ae62084001c96615cc410800113b0f3188210003075d663104200044ec3ac62084000c1d7558c410800186aeab088210003255cd611042000e4a38ac6a1e2000c8e845ce62c400191b08b9cc588003239517398b1000646aa2e73162007c8e415ce62c400f91882b9cc58801f328417398b1003e64882e73162000c8d73d0e62c400191ae6a1cc588006a92054358b100465220aed19620038cd83dd932c400191eeca1a6588003235d9434cb1003dc240a869962000e255458951c400132b063a24388002a360e644ca1000547c32869942000a8d8650d328400139306392a108002a360c644c91000547432869922000a8c8650d324400f70902a1a64880064d21d545451000699402ea20a2000d31805d4414400386ec0ba882880074cd817510510006c3412e620a2000d85825cc4144001b2500b98828800364601731051000e4bb02e620a2001d93605cc4144001a4aeb1908288003615ce321051000692baa6420a2000d85734c841440033290ea1a6288002a5219434c510004cac18e890a2000b318510650440017230620ca0880027260c725411000598c2882a822000b91831055044001b40e420aa088002cc6144190110005c8c18832022000b318510540440017230620a8088002e8608415011000598c28831822000b91831063044009990ec9926088002cc614414c110005c8c18829822000f813210530440016630a20e4088002e460c41c8110004d8c38821022000b31851042044001a62ea2084088002e460c4108110006c8b98821022000d61754842044001b42e89084088003705cd2108110
  | 1 => 0xe20b2c6420823a19c5638c84104743882c71908200e25655c63210401d0ac6b8c642080383a0d654c84100706c1aca9908207e0e31595321040fc1862b2a642081f89c41654c84100706b2ee69908207b8681dcd321041191d0eb1a642081f2361d634c84100547c2ac69908207e871058d321040151b0d29a642080383596534c84100546c32a69908200e0d6554d321040f70902a9a64208230b9c9650c84100cca40aeaa1e6200a8d8395162cc40151f0aa1ac598802a36154358b3103d4740a86b166207a8c8150d62cc4030790eb2aa91881ee1a07434ca3103dc240a869946200a8f84595328c40f51d0d2a2651881ea3a19544ca3100706b2aa89946200f05544c9518c40191ee8992c11880627219739513100546c10eca1a620189c865d5434c40162b0a38a8698802e46007150d3104546432871926207a8c8650d324c40f70902a1a6498802c5615435453100d1a40ae8b2862018b4815d9540c403868e2b2aa81880383a11654c83100706c22ca9906207e0e41595320c40fc1882b2a6418802a3e15644c83103d4740ac89906207a8c81591320c40151b0d2a2641880383596544c83100546c32a89906200e0d65551320c40f70902aa26418806ac2055458031007452a264b006200e89544c9600c40fd1482992c01881fa2105325803100546c1cc89964200a8f8650d32c840151b0ca1a659081323dd9434ca2103dc240a869944200e89434ca608840356102a1ac110803a250d325822100718aa2a2b044200c8e825cc644840191b04b98c8908022760c765512102c4e43ac6a1a4200a8d83192324840151b063226490802a3a19434c92100546432869924207b848150d324840316902bb287a8002a360e644cb5000547c3286996a000a8d8650d32d400386cc2ba883280072598573106500061abaac220ca000c9573584419400191d08b98c4a8003236117318950006472a2e6312a000c8d545cc625400191ae7a18c4a8003235cd4318950006263b2a6992a000c8e7650d3254001918eca1a64a8002a360c629055000616baec420aa000c8d73d88415400115b0e31082a80030b5d4621055000546c18c420aa000c8d73188415400191ae8b92c628003235cd439885000546c1cc8990a000a8f8650d321400151b0ca1a642800323dd9434c85000646bb286990a000e85434ca611400152b063a2c228003a150d325845000c1ec2aec208a001c36615d4411400113f0cb9882280072598573104500044ec3cc6208a000c1d7598c411400113b0eb188228003075d5631045000616bacc4208a000c8d73988411400185aeab108228003235cd62104500061abaac2208a000c9573584411400951f0ca1a6520003a150d329864000742a1a64b0c8001c36615d4419000392cc2b9883200030d5d561106400064ab9ac220c8001
  | 2 => 0xe7118132006c2a1ae23026400c6975580604c801d1286b00c0990064d2057550f5100546c1cc8996a200a8f8650d32d440151b0ca1a65a8802c3615434cb5103dc240a86996a207a8c8650d329440162b0638aa8a8802c9608715515100598c00e2aa2a20183c865d5435440151b0632264a881293219534c9510054743286992a200a8c8650d325440161b0aa1a64a8806a52057458c5100646ba2e4b18a201c947158d431440191ae6a1cc428806a9205435885100546c1cc8990a200a8f8650d321440151b0ca1a642880323dd9434c85100646bb286990a207b848150d3214401d1286994c028806ac205435805100744a1a64b00a207b868190d329040f70902a1a6520802a3e0d654ca4103d47434a69948200e0d6554d32904095190ca1a64a08030b5967290c4100646b1ce52188200c2d655ca431040191ac6b948620803235cd439884100546c34869908200e0d6590d321040191eeca1a642080383995434c84100706b2a869908200e89434ca6010401d1286992c0208028ba0a735944100516c14e6b288201a34815cd651040145d0439aca208028b608735944100d1b408e6b288200a3a801cd65104014730039aca2080287a0c72594410050ec18e4b288201a36811c9651040147500392ca208028e600725944100d1b40ce0b288200a2f825c1651040145904b82ca2080287a0c70594410050ec18e0b288200a2e821c1651040145b04382ca208068da04705944103d46c1ce4b188208a8f835c9631040151d05baac620802a360b7558c4100d4a40aeab188200a8e821d5631040151b043aac620806a5a047558c410054d400eab188200a99801d5631040352d03392c620823a1a067258c4100742c0ce4b188208e87109c9631040191f0eb92c62080323dd57258c4100646baae4b188207c8e715c9631040f918e2b92c62081fa1c417258c4100547416e0b188200a8d82dc1631040191ae5b82c620806a5a067058c4100646b92e0b188200a1e851c1631040143b0a382c620802a3a087058c4100546c10e0b188201a96811c1631040185acb394a6208032358e7294c4100616b2ae52988200c8d635ca531040186acbb8aa6208032558f7154c4100e1b38aca2988201c967158c531040185acb390a6208032358e7214c4100616b2ae42988200c8d635c8531040186acab88a6208032558d7114c410061cb2ce02988200c99639c05310401872cab80a6208032658d7014c4100e1b38aca290820089d869cc521040183acb398a4208030759573148410044fc3ac6290820089d8758c521040392ce2b18a4208030d59571148410064ab1ae22908200c39659c05210401932c7380a4208030e59570148410064cb1ae02908201c3671596321040186acab8c64208032558d718c84103e16b9acb1908208e26715963210411c4
  | 3 => 0x318582f34ea0800342468dbb83036614800c3a6088aea7f8006723cbe9465d00090b28c611605aba8f8e6060382b25cca8c864b2c72060e3b4644000ba0729892811000e9a084906c7ca7064180f196eeba882986634aec362a2893c818bb2698c21314872acaa1b0a551eec728e548fef5086938e2ad800c32408d0ca00104d4084edace2e918da8502812ad207449a729a0e800176a29b4bf8f4eeba2978002626cb1800ef37671100ea9ecc815847800e8000d493e00254002d0d2a7e00000bc3a84b0001514092af8071064e0cc00162a4bd212800e2b708426a9127a7e96a19000dd02ab687a002b2e49d09bb02040be27b7a9d1c0a5b3c120b6e31083da56bba9c6807e0001e03001000040b4131c4000101e00000000000280a0000101c0201001054010f40c0002800c0a070000200000015010010241705800014090080e000080000200c140000b01c0f00c2401c05020350240a000260080c0001400000004000000300806000020000001c0001c120000100c08010030240002007018010001b024070480400800038030200313c080540000806000000340303c0206c00014360500301000094010080e00c0308002000010000200c020500d0181101c050540c01c020140404c100000100005004c6c18e4b02a800a8d839516294c0316902ba6c0a98062d2057650f520054ac18e8b08a409994815d543cc8131390ea1ac399022692057550e3203e64b1ae130c6408da0415c2618c80f32902baa869900263e1d43d4932004c7c3a862926400d85439c4524c801b0a86b88a4990036250e7014932006c4a1ae0292640098d839d0654c80f31902b9ca899002e1205735513203cc640ae929a6400b4581195534c8016930032aa699002e12057454d32004c6c26e0a9a6400d0d7554f434c801a1aeaaa4869901e692057550d32004c743ea6a1a6400d0f75d4d434c801a1eeaa9a869901e712057550d32024c743ea8a1a6400d0f75d51434c801a1eeaaa2869900263a1c5450d32005c340ceca1a6400b85819d9434c80f31d03baa86990026361e7550d3200687baceaa1a6400b87815d5434c80170902baa869900343e157550d32006c3c0aeaa1a640798c815d5434c801b0902baa869901e612057550d32004c7438eaa1a640098e87995434c80131b0f32a8699002e2e016550d32005c4402caa1a640098e87195434c80131b0e32a8699002e1a046550d32005c2c08caa1a6400b8a80195434c8017130032a8699002a3a187150d3200587428e2a1a6400b0d851c5434c80fb0ce238a8699002e2a007150d32005c4c00e2a1a6400b86819c1434c80170b03382869900263e1d43d853203dc240a8730a6400d89439c2614c801b1286b84c29901ee12054358532004c7c3a863026400d0e7550c604c801a1aeaa18c0990036150
  | 4 => 0x144df2e24d36c0c8ce80800078a2ce13ccd9024b8f85f9a8d02c2002f499290038002bb845f1d866360003080010a0036416800179e00486ee714aafac4c418c89ad8000409f3ac1709c622c00d19e870b0d6194a32b0cc1e6f0aac000003ea50220b43680099bd6000420008000000f39960023076800029e8b80a86e9560014222b326e0008a800002b4bc800b98008318ac53228a1e2003680f1b00000000248a00d48c800542d200132c925200000b79cc002d66c800e9000932aec7a06373c41d878738b2001dc001aa692202a8006b3cc000de000000b218c4b3e00166791bc002a80faa485ae406a76f01d6b706a5e22ca9b04e207c25800452bc00036000000815c56b9e000fc61800ec1827d130c0394a50eced02e4888ca7ac8a6354ae31a2939a5ca58382140132ec58eeb304e6d9f87f3be5eaa08021abf184d5800001d45b0000891ae63625789a0000005000e1b7e8b960de20ed6af63c8007193a003d0002840038200000000c42e33a59000b510e003804d8ea098001c1be2400296912aa800878082534c7780000024f2b0668882a6a04159d27a8001198ed714c00000001ae0011cdc83ae423a000003c000538000008e7c000d78d6cd0285a1f6d09c23921201a0ad10928e19a033964810c9e170db830c9868
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x781000000d073a39181006051700488964250499004111c1e0c9800054006007c005000000040000001030d8d000020b0008000208500000000f03c6124584dc1534c80f1849161e6550d3203d60245435c2614c801c097550d601813203cc12458550d32d440f20c96615434c95103d21245745c9631440f884815d9434c85103da0245434c9601440120d93209705944103d21a47875c9631040f484915d57258c4103d8124583595321040fa0681597734c84103ca12458550d62cc40f60491611654c83103ca124586551320c40fa0481595544c83103da0245544c9600c40f6809150d325822103ca12458650d32d400180d7560c62105500042366173188415400f28491619544cb3003e212057650d32c400152092601751051000660609805cc41440011a1981c8415411000648614721055044001581931c841541100066060c721055044001b01854c8414c1100044c6617510420440019117560c410811000464661731042044001911855cc4108110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x1080002501a3249805d44144001880c2b2639082a8220008606a5831c84154110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x1
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0xcca
  | 8 => 0x15ca
  | 9 => 0x170a
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 68
  | 6 => 1812
  | 5 => 2219
  | 4 => 492
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
  | 7 => packedAt gbK7 (1922+((h/22+packedAt gbK7 (1768+(h % 22)*7) 7) % 82)*8) 8
  | 6 => packedAt gbK6 (74292+((h/604+packedAt gbK6 (67044+(h % 604)*12) 12) % 2392)*12) 12
  | 5 => packedAt gbK5 (115380+((h/739+packedAt gbK5 (106512+(h % 739)*12) 12) % 3543)*13) 13
  | 4 => packedAt gbK4 (30668+((h/164+packedAt gbK4 (29028+(h % 164)*10) 10) % 591)*10) 10
  | 3 => packedAt gbK3 (2592+((h/12+packedAt gbK3 (2520+(h % 12)*6) 6) % 57)*7) 7
  | 2 => packedAt gbK2 (246+((h/1+packedAt gbK2 (243+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x38638387c3f87f87f01c3f83fff03026b3c33f
  | 1 => 0xc07c03f87c3f87f87fffc3fc1c0041394cfdcc
  | 2 => 0x7ffc007fc007ff801ffc001ff989c18f0e0f
  | 3 => 0xff8000007ffff800001fffffe00e0e01f00ff0
  | 4 => 0x7fffffffffe00000000ff001fff000
  | 5 => 0xffffffff8000000000000000000ffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x820809300980a80914404894520102211c115
  | 1 => 0x406409310408818820cc41184860012804554c
  | 2 => 0x14938205d444555029aa83092c889418e0e0a
  | 3 => 0x930010006a65504404133262808a0a01e00aa0
  | 4 => 0x600604673b666664f022043030ff001fba000
  | 5 => 0x24124244000000000800000000056494000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfffefffeeeeceea0fffefffeeeeceea0fffefffeeeeceea0fffefffeeeeceea0fffefffeeeeceea0fffefffeeeeceea0fffefffeeeeceea0fffefffeeeeceea0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_10860
namespace PEqualNP.Outside.L_meta_10860
open PEqualNP.Outside.L_meta_10860.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 5 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
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
theorem bgb_4_480 : Interval gbAtlas 4 480 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 492 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 bgb_4_480))))
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
theorem bgb_5_2208 : Interval gbAtlas 5 2208 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2219 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)))) (concat (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))))) (concat (concat (concat (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344))) (concat (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))))) (concat (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)) (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 bgb_5_2048)) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 32, 36),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 5 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 6 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xffffffffffffeea0fffefffeeeeceea0ffffffffffffeea0fffefffeeeeceea0ffffffffffffeea0fffefffeeeeceea0ffffffffffffeea0fffefffeeeeceea0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) SB :=
    slice_correct (ms:=fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
  have lift := lift_ok (u:=true) (ms:=fixRows 64 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,16,80)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,16,80)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 7 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_10860.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,6]⟩,⟨.or,[1,2]⟩,⟨.or,[5,6]⟩,⟨.and,[8,9]⟩,⟨.and,[1,4]⟩,⟨.or,[0,6]⟩,⟨.or,[3,4]⟩,⟨.and,[12,13]⟩,⟨.or,[7,10]⟩,⟨.or,[15,11]⟩,⟨.or,[16,14]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_10860

open PEqualNP.Outside.L_meta_10860 in
theorem PEqualNP.Outside.L_meta_10860 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
