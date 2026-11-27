import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- The live-wire extraction and restriction lemmas are adapted from the Apache-licensed
-- proofs of L-meta-1667 and L-meta-2768, including the work in pull request 8941.
-- The certificates below concern the eight-input graph in the statement.
-- A computation with a NOT has at most eleven binary gates in a twelve-gate circuit.
-- For that case the search permits free complements. Without a NOT it tests twelve binary gates.
namespace PEqualNP.Outside.L_meta_8511

open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 256
def zero : Sig := 0
def one : Sig := BitVec.allOnes 256
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

def bit (i : Fin 256) (a : Sig) : Bool := a.getLsbD i.val
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
lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

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

lemma extract {u target} (gs : List Gate) (w : List Sig)
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

lemma readSig (i) (w : List Sig) (j : Nat) :
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
  simp only [readSig]
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

lemma executeBits (gs : List Gate) (i) (w : List Sig)
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


abbrev Row := Fin 256
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
  if h : r.val < 256-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(256-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 256 (256-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 256-d.val <;> simp [shifted,h,r.isLt]

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

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def graph : Sig := 0xffffffffffffffffffffffe8ffffeae8ffffffe8ffffeae8ffe8ffe8ffe8eae8
def sample (r : Row) (j : Fin 8) := bit r (inputs.getD j.val zero)
def edge (x : Fin 8 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 4 && x 7) || (x 6 && x 7)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 8 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←readSig,executeBits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem lower_circuit (u : Bool) (L : Nat) (lo : Lower u inputs graph L)
    (C : Circuit) (legal : FanInTwo C) (mono : u=false → ∀ g∈C.gates, isNot g=false)
    (computes : ∀ x, C.eval (List.ofFn x)=edge x) :
    L ≤ C.gates.countP (fun g => !isNot g) := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply bit_ext
    intro r
    exact (table_eval C legal C.output r).trans ((computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (u:=u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 graph=false by decide +kernel)] at out
  obtain ⟨k,S,hk,run,hs⟩ := extract C.gates inputs legal mono graph_proper
    (out.resolve_right (fun hn => hn graph_proper))
  rw [nrm_map (show inputs.all plainWord=true by decide +kernel)] at hs
  have rr := list_run run S.toList S.nodup_toList (by simp)
  have sup : supply u (inputs.map observe) (S.toList.map observe) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
    exact Or.inl (List.mem_map_of_mem (hs _ (by simpa using hv)))
  obtain ⟨q,bank,hq,ha,hqk⟩ := contraction (observe_proper graph_proper) rr
    (inputs.map observe) Reach.start sup
  have hh := lo q bank hq ha
  omega

theorem from_modes (hm : Lower false inputs graph 13) (hs : Lower true inputs graph 12) :
    ∀ t, HasCircuitSize 8 edge t → 13 ≤ t := by
  rintro t ⟨C,legal,size,hf⟩
  change C.gates.length ≤ t at size
  by_cases h : ∀ g ∈ C.gates, isNot g=false
  · have hh := lower_circuit false 13 hm C legal (fun _ => h) hf
    exact hh.trans (List.countP_le_length.trans size)
  · have hh := lower_circuit true 12 hs C legal (by simp) hf
    have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
      by_contra! le
      have all := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length le)
      apply h
      intro g hg
      simpa using all g hg
    omega

abbrev Rule (u : Bool) (T : Sig) (k : Nat) :=
  {g : List Sig → Bool // ∀ ws, ws.Nodup → g ws=true → Impossible u T k ws.toFinset}

def failRule (u : Bool) (T : Sig) (k : Nat) : Rule u T k :=
  ⟨fun _ => false, by simp⟩

def rowRule (u : Bool) (T : Sig) (k : Nat) (r s : Row) : Rule u T k :=
  ⟨fun ws => bit r T && !bit s T && ws.all (fun w =>
    if u then bit r w == bit s w else !bit r w || bit s w), by
    intro ws _ h j _ run
    simp only [Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
    cases u with
    | false =>
      obtain ⟨a,ha,hr,hs⟩ := mono_row_difference run rfl h.1.1 h.1.2
      simpa [hr,hs] using h.2 a (List.mem_toFinset.mp ha)
    | true =>
      have ne : bit r T ≠ bit s T := by simp [h.1.1,h.1.2]
      obtain ⟨a,ha,hd⟩ := live_row_difference run ne
      apply hd
      simpa using h.2 a (List.mem_toFinset.mp ha)⟩

def linkRule {u T k} (xs : List Sig) (old : Impossible u T k xs.toFinset) : Rule u T k :=
  ⟨fun ws => ws.all xs.contains && xs.all ws.contains, by
    intro ws _ chk
    have e : ws.toFinset=xs.toFinset := by
      simp only [Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at chk
      ext w
      simp only [List.mem_toFinset]
      exact ⟨chk.1 w,chk.2 w⟩
    rw [e]
    exact old⟩

def cutRule {u raw T d L} (k : Nat) (prior : Slice u raw T d L)
    (cs : List Choice) : Rule u T k :=
  ⟨fun ws => match makePool u d raw cs with
    | none => false
    | some pool => poolCut u d L k cs.length pool ws, by
    intro ws nd ok
    cases e : makePool u d raw cs with
    | none => simp [e] at ok
    | some pool =>
      exact poolCut_sound prior cs e nd (by simpa [e] using ok)⟩

def choiceSlot (i j d : Nat) (a b : Bool) : Nat :=
  let op := if i < j then d else flipOp d
  let high := max i j
  let low := min i j
  let flags := if i < j then 2*a.toNat+b.toNat else 2*b.toNat+a.toNat
  16*(high*(high-1)/2+low)+4*op+flags

def opList (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]

theorem opList_mem {u d} (h : allowed u d) : d ∈ opList u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> decide
  · cases u <;> decide
  · decide
  · decide

def checkStep {u T k} (ws : List Sig) (rules : Nat → Rule u T (k-1))
    (idx : Nat → Nat) (i j d : Nat) (ka kb : Bool) : Bool :=
  let a := ws.getD i zero
  let b := ws.getD j zero
  let z := bin d a b
  let child := childTwo ws a b d ka kb
  a==b || ws.contains z || z==zero || z==one || decide (child.length>k) ||
    (decide child.Nodup && (rules (idx (choiceSlot i j d ka kb))).val child)

def checkNode {u T k} (ws : List Sig) (rules : Nat → Rule u T (k-1)) (idx : Nat → Nat) : Bool :=
  decide ws.Nodup && !ws.contains T &&
  (List.range ws.length).all fun i => (List.range ws.length).all fun j =>
    (opList u).all fun d => [false,true].all fun ka =>
      [false,true].all fun kb => checkStep ws rules idx i j d ka kb

theorem checkNode_sound {u T k ws rules idx} (h : @checkNode u T k ws rules idx=true) :
    Impossible u T k ws.toFinset := by
  simp only [checkNode,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
    List.contains_eq_mem,decide_eq_false_iff_not,List.all_eq_true] at h
  apply enum_step h.1.1 h.1.2
  intro a ha b hb d hd ka kb ne fresh hz len
  obtain ⟨i,hi,ai⟩ := List.getElem_of_mem ha
  obtain ⟨j,hj,bj⟩ := List.getElem_of_mem hb
  have hk (x : Bool) : x ∈ [false,true] := by cases x <;> decide
  have ok := h.2 i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) d (opList_mem hd)
    ka (hk ka) kb (hk kb)
  have ea : ws.getD i zero=a := by simpa [List.getD_eq_getElem?_getD,hi] using ai
  have eb : ws.getD j zero=b := by simpa [List.getD_eq_getElem?_getD,hj] using bj
  simp only [checkStep,ea,eb,beq_eq_false_iff_ne.mpr ne,List.contains_eq_mem,
    decide_eq_false fresh,beq_eq_false_iff_ne.mpr hz.1,beq_eq_false_iff_ne.mpr hz.2,
    decide_eq_false (Nat.not_lt.mpr len),Bool.false_or,Bool.and_eq_true,decide_eq_true_eq] at ok
  exact (rules _).property _ ok.1 ok.2

def raw (n : Nat) := inputs.take n
def setBitRow (j : Nat) (v : Bool) : Move :=
  let x := inputs.getD j zero
  let delta := Fin.ofNat 256 (1 <<< j)
  if v then (~~~x,zero,delta) else (zero,x,delta)
def exchangeRow (i j : Nat) : Move :=
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 256 ((1 <<< j)-(1 <<< i)))
def bitsAt (word width i : Nat) := (word >>> (width*i)) &&& ((1 <<< width)-1)

def supports (n : Nat) (samples : List Nat) :=
  ((raw n).zip samples).zipIdx.map fun ((w,r),i) =>
    (w,Fin.ofNat 256 r,Fin.ofNat 256 (r ^^^ (1 <<< i)))
def basicCheck (n : Nat) (T : Sig) (samples : List Nat) :=
  let xs := supports n samples
  (T != zero && T != one) && checkEssential T (raw n) xs && xs.map Prod.fst == raw n

theorem basic_data {n T hints} (ok : basicCheck n T hints=true) :
    proper T ∧ plainWord T=true ∧ (raw n).all plainWord=true ∧
      ∀ a∈raw n, Essential T (raw n) a := by
  simp only [basicCheck,Bool.and_eq_true,bne_iff_ne,beq_iff_eq] at ok
  obtain ⟨ht,hr⟩ := essential_plain ok.1.2
  refine ⟨ok.1.1,ht,hr,?_⟩
  intro a ha
  apply essential_ok ok.1.2
  rw [ok.2]
  exact List.mem_toFinset.mpr ha

theorem countBound {u n T hints L} (ok : basicCheck n T hints=true)
    (size : L ≤ ((supports n hints).map Prod.fst).toFinset.card-1) :
    Lower u (raw n) T L := by
  have pt := (basic_data ok).1
  simp only [basicCheck,Bool.and_eq_true] at ok
  have es := ok.1.2
  intro p b h q
  exact size.trans (lower_count pt _ es p b h q)

theorem finishBound {u n T hints k} (ok : basicCheck n T hints=true)
    (noRun : Impossible u T k (raw n).toFinset) : Lower u (raw n) T (k+1) := by
  obtain ⟨pt,ht,hr,es⟩ := basic_data ok
  exact lower_impossible pt ht hr es noRun

def codedRule {u T k} (cuts links : Nat → Rule u T k) (id : Nat) : Rule u T k :=
  if id<65536 then rowRule u T k (Fin.ofNat 256 (id/256)) (Fin.ofNat 256 id)
  else if id<131072 then cuts (id-65536) else links (id-131072)

def g0T : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8

def g0H : List Nat := [2,1,1]

theorem g0Ok : basicCheck 3 g0T g0H=true := by decide +kernel

def g0v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g0v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g0v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g0Cuts (k i : Nat) : Rule true g0T k := failRule true g0T k

def g0n0w : List Sig := [g0v0,g0v1,g0v2]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g0n0 : Impossible true g0T 3 g0n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g0Cuts 2) (fun i => failRule true g0T 2))) (idx:=(fun j => bitsAt 0x1810060201410050101400030200c040300 18 (bitsAt 0x18913c1be1091121ab12c1920681d00511ed 3 j))) (by decide +kernel)

theorem bound0 : Lower true (raw 3) g0T 4 := finishBound g0Ok g0n0

def g1T : Sig := 0xffffffe8ffe8e8e8ffffffe8ffe8e8e8ffffffe8ffe8e8e8ffffffe8ffe8e8e8

def g1H : List Nat := [2,1,1,16,8,8]

theorem g1Ok : basicCheck 6 g1T g1H=true := by decide +kernel

def g1v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g1v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g1v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g1v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g1v4 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g1v5 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000

theorem g1s0 : Slice true (raw 6) g1T 0x101010101010101010101010101010101010101010101010101010101010101 4 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

theorem g1s1 : Slice true (raw 6) g1T 0x1010101010101010101010101010101010101010101010101010101010101010 4 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

theorem g1s2 : Slice true (raw 6) g1T 0x404040404040404040404040404040404040404040404040404040404040404 4 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 true,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

theorem g1s3 : Slice true (raw 6) g1T 0x202020202020202020202020202020202020202020202020202020202020202 4 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 true,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

theorem g1s4 : Slice true (raw 6) g1T 0xff00000000000000ff00000000000000ff00000000000000ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

def g1Cuts (k i : Nat) : Rule true g1T k := (if i<2 then (if i<1 then (cutRule k g1s0 []) else (cutRule k g1s1 [])) else (if i<3 then (cutRule k g1s2 []) else (if i<4 then (cutRule k g1s3 []) else (cutRule k g1s4 []))))

def g1n0w : List Sig := [g1v0,g1v1,g1v2,g1v3,g1v4,g1v5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g1n0 : Impossible true g1T 8 g1n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g1Cuts 7) (fun i => failRule true g1T 7))) (idx:=(fun j => bitsAt 0x100044000d00024000500000c08030100b0302a0a0a42428200a020280009484250108c88232108c082301070501c0c068481a0a06444190906040180806000151105404131204c44130204c040d09034040b0a02c240b0202c04060401808052101444050901410050101400032200c84031200c44030a00c24030200c040300 18 (bitsAt 0xe3279ee2dcede32cf2e2d79ee2d7dfe32bace2dbade327dfd7128ad2daead71aced2d28adb0041d2da26db0a07d2d041def082d2da67defa48d2d082e1eb9de337dde1e7dee33baed6428ad1e71bd6470dd1e28ada2041d1e657da2645d1e041de0082d1e698de0686d1e082d6528ad1f595d6558cd1f28ada3041d1f4d1da34c3d1f041de1082d1f512de1504d1f082d0f041d0a40ad0f40fd0a041d0a082d0f2c9d0a2cad0f082d012c0d10080d01081d102cb 6 j))) (by decide +kernel)

theorem bound1 : Lower true (raw 6) g1T 9 := finishBound g1Ok g1n0

def g2T : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8

def g2H : List Nat := [2,1,1]

theorem g2Ok : basicCheck 3 g2T g2H=true := by decide +kernel

def g2v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g2v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g2v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g2Cuts (k i : Nat) : Rule true g2T k := failRule true g2T k

def g2n0w : List Sig := [g2v0,g2v1,g2v2]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g2n0 : Impossible true g2T 2 g2n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g2Cuts 1) (fun i => failRule true g2T 1))) (idx:=(fun j => bitsAt 0x60201410050101400030200c040300 18 (bitsAt 0x1004006001002003004002000000001005 3 j))) (by decide +kernel)

theorem bound2 : Lower true (raw 3) g2T 3 := finishBound g2Ok g2n0

def g3T : Sig := 0xffffffe8ffe8e8e8ffffffe8ffe8e8e8ffffffe8ffe8e8e8ffffffe8ffe8e8e8

def g3H : List Nat := [2,1,1,16,8,8]

theorem g3Ok : basicCheck 6 g3T g3H=true := by decide +kernel

def g3v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g3v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g3v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g3v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g3v4 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g3v5 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000

theorem g3s0 : Slice true (raw 6) g3T 0x101010101010101010101010101010101010101010101010101010101010101 3 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g2Ok).1 bound2

theorem g3s1 : Slice true (raw 6) g3T 0x1010101010101010101010101010101010101010101010101010101010101010 3 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g2Ok).1 bound2

theorem g3s2 : Slice true (raw 6) g3T 0x404040404040404040404040404040404040404040404040404040404040404 3 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 true,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g2Ok).1 bound2

theorem g3s3 : Slice true (raw 6) g3T 0x202020202020202020202020202020202020202020202020202020202020202 3 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 true,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g2Ok).1 bound2

theorem g3s4 : Slice true (raw 6) g3T 0xff00000000000000ff00000000000000ff00000000000000ff 3 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g2Ok).1 bound2

def g3Cuts (k i : Nat) : Rule true g3T k := (if i<2 then (if i<1 then (cutRule k g3s0 []) else (cutRule k g3s1 [])) else (if i<3 then (cutRule k g3s2 []) else (if i<4 then (cutRule k g3s3 []) else (cutRule k g3s4 []))))

def g3n0w : List Sig := [g3v0,g3v1,g3v2,g3v3,g3v4,g3v5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g3n0 : Impossible true g3T 7 g3n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g3Cuts 6) (fun i => failRule true g3T 6))) (idx:=(fun j => bitsAt 0x100044000d00024000500000c08030100b0302a0a0a42428200a020280009484250108c88232108c082301070501c0c068481a0a06444190906040180806000151105404131204c44130204c040d09034040b0a02c240b0202c04060401808052101444050901410050101400032200c84031200c44030a00c24030200c040300 18 (bitsAt 0xe3279ee2dcede32cf2e2d79ee2d7dfe32bace2dbade327dfd7128ad2daead71aced2d28adb0041d2da26db0a07d2d041def082d2da67defa48d2d082e1eb9de337dde1e7dee33baed6428ad1e71bd6470dd1e28ada2041d1e657da2645d1e041de0082d1e698de0686d1e082d6528ad1f595d6558cd1f28ada3041d1f4d1da34c3d1f041de1082d1f512de1504d1f082d0f041d0a40ad0f40fd0a041d0a082d0f2c9d0a2cad0f082d012c0d10080d01081d102cb 6 j))) (by decide +kernel)

theorem bound3 : Lower true (raw 6) g3T 8 := finishBound g3Ok g3n0

def g4T : Sig := 0xffececa8ffececa8ffececa8ffececa8ffececa8ffececa8ffececa8ffececa8

def g4H : List Nat := [2,1,1,2,2]

theorem g4Ok : basicCheck 5 g4T g4H=true := by decide +kernel

theorem g4s0 : Slice true (raw 5) g4T 0x505050505050505050505050505050505050505050505050505050505050505 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

def g4Cuts (k i : Nat) : Rule true g4T k := (cutRule k g4s0 [])

theorem bound4 : Lower true (raw 5) g4T 6 := finishBound g4Ok ((g4Cuts 5 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g5T : Sig := 0xeca8eca8eca8eca8eca8eca8eca8eca8eca8eca8eca8eca8eca8eca8eca8eca8

def g5H : List Nat := [2,1,1,2]

theorem g5Ok : basicCheck 4 g5T g5H=true := by decide +kernel

def g5v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g5v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g5v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g5v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g5Cuts (k i : Nat) : Rule true g5T k := failRule true g5T k

def g5n0w : List Sig := [g5v0,g5v1,g5v2,g5v3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g5n0 : Impossible true g5T 3 g5n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g5Cuts 2) (fun i => failRule true g5T 2))) (idx:=(fun j => bitsAt 0xa0c028080a0001430050901410050101400030900c18030200c040300 18 (bitsAt 0x6000b000800060001000a000400010002000b0009000200010006000c000100020005000300020000000000010007 4 j))) (by decide +kernel)

theorem bound5 : Lower true (raw 4) g5T 4 := finishBound g5Ok g5n0

def g6T : Sig := 0xffececa8ffececa8ffececa8ffececa8ffececa8ffececa8ffececa8ffececa8

def g6H : List Nat := [2,1,1,2,2]

theorem g6Ok : basicCheck 5 g6T g6H=true := by decide +kernel

def g6v0 : Sig := 0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc

def g6v1 : Sig := 0xffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc

def g6v2 : Sig := 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc

def g6v3 : Sig := 0xff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc

def g6v4 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g6v5 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g6v6 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g6v7 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g6v8 : Sig := 0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc

def g6v9 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g6v10 : Sig := 0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc

def g6v11 : Sig := 0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00

theorem g6s0 : Slice true (raw 5) g6T 0x5555555555555555555555555555555555555555555555555555555555555555 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

theorem g6s1 : Slice true (raw 5) g6T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g5Ok).1 bound5

theorem g6s2 : Slice true (raw 5) g6T 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff 4 :=
  slice_correct (ms:=[setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g5Ok).1 bound5

theorem g6s3 : Slice true (raw 5) g6T 0x505050505050505050505050505050505050505050505050505050505050505 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g2Ok).1 bound2

theorem g6s4 : Slice true (raw 5) g6T 0x505050505050505050505050505050505050505050505050505050505050505 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

theorem g6s5 : Slice true (raw 5) g6T 0x5050505050505050505050505050505050505050505050505050505050505050 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g2Ok).1 bound2

theorem g6s6 : Slice true (raw 5) g6T 0x5050505050505050505050505050505050505050505050505050505050505050 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

def g6Cuts (k i : Nat) : Rule true g6T k := (if i<3 then (if i<1 then (cutRule k g6s0 []) else (if i<2 then (cutRule k g6s1 []) else (cutRule k g6s2 []))) else (if i<5 then (if i<4 then (cutRule k g6s3 []) else (cutRule k g6s4 [])) else (if i<6 then (cutRule k g6s5 []) else (cutRule k g6s6 []))))

def g6n0w : List Sig := [g6v1,g6v4,g6v5,g6v6,g6v7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g6n0 : Impossible true g6T 4 g6n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g6Cuts 3) (fun i => failRule true g6T 3))) (idx:=(fun j => bitsAt 0x60001202048000d0c034240a0c028200a0602808050401404050000c24030600c080301 18 (bitsAt 0x5000700080005000700090003000300010007000c00010007000f0007000e00090005000a00050001000400020001000b0005000b00050006000100010006000000000009000d0001000600010006 4 j))) (by decide +kernel)

def g6n1w : List Sig := [g6v3,g6v4,g6v5,g6v6,g6v9]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g6n1 : Impossible true g6T 4 g6n1w.toFinset :=
  checkNode_sound (rules:=(codedRule (g6Cuts 3) (fun i => failRule true g6T 3))) (idx:=(fun j => bitsAt 0x60001514048401206048080e02028100a0202800050401404050000c44030600c080301 18 (bitsAt 0x5000b000c00050007000d000300030001000b000e00010008000f000b00080007000500090005000100040002000100080005000a0005000600010001000600000000000800070001000600010006 4 j))) (by decide +kernel)

def g6n2w : List Sig := [g6v4,g6v5,g6v6,g6v7,g6v8,g6v9]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g6n2 : Impossible true g6T 5 g6n2w.toFinset :=
  checkNode_sound (rules:=(codedRule (g6Cuts 4) (fun i => (linkRule g6n0w g6n0)))) (idx:=(fun j => bitsAt 0x800010002060401808048080d0c034240a0c028200a0602808051401444050401404050000c24030600c080301 18 (bitsAt 0xf000130000f00012000090000f0001000009000050000f00007000050000b000100000f0000b000010000f000080000100011000000000000000000050000d0000d00005000000000000000000000000600001000010000600005000090000a00005000090000b000000000300001000090000e000010000b000050000c000050000100004000020000100006000010000100006 5 j))) (by decide +kernel)

def g6n3w : List Sig := [g6v2,g6v4,g6v5,g6v6,g6v7,g6v9]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g6n3 : Impossible true g6T 5 g6n3w.toFinset :=
  checkNode_sound (rules:=(codedRule (g6Cuts 4) (fun i => failRule true g6T 4))) (idx:=(fun j => bitsAt 0x400150003060401808060001202034100d01028300a08028080a0001450051101430050901410050101400030600c080301 18 (bitsAt 0x11000100001200010000040001000008000040000c00012000100000c0000100010000090000100010000120001000012000040000e00006000040000a000000000c00013000010000f000070000100000000000000b000000000c000040000d000040000100003000020000100014000040001500004000050000100001000050000000000000000000000001000050000100005 5 j))) (by decide +kernel)

def g6n4w : List Sig := [g6v4,g6v5,g6v6,g6v7,g6v9,g6v10]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g6n4 : Impossible true g6T 5 g6n4w.toFinset :=
  checkNode_sound (rules:=(codedRule (g6Cuts 4) (fun i => (linkRule g6n1w g6n1)))) (idx:=(fun j => bitsAt 0x80001000106040180805450151104850121004818120202808050c01424050401404050000c44030600c080301 18 (bitsAt 0x1000000000000000000013000090000900012000050000e0000e000050000000000000000000000006000010000100006000090000a0001100009000050000a0000b000050000a0000c0000000003000010000a0000f00001000050000900007000050000900011000090000c000010000900008000010000c000050000d000050000100004000020000100006000010000100006 5 j))) (by decide +kernel)

def g6n5w : List Sig := [g6v0,g6v4,g6v5,g6v6,g6v7,g6v9]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g6n5 : Impossible true g6T 5 g6n5w.toFinset :=
  checkNode_sound (rules:=(codedRule (g6Cuts 4) (fun i => failRule true g6T 4))) (idx:=(fun j => bitsAt 0x400150003060401808060001504054041214048401202048000a0201450051101430050901410050101400030600c080301 18 (bitsAt 0xa00011000120000a000040000f00008000040000b000000000d000120000100010000090000100000000000000c00000000040000a00006000040000a000130000a0000d000010000a00007000010000a000130000a000130000d000040000e000040000100003000020000100014000040001500004000050000100001000050000000000000000000000001000050000100005 5 j))) (by decide +kernel)

def g6n6w : List Sig := [g6v4,g6v5,g6v6,g6v7,g6v9,g6v11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g6n6 : Impossible true g6T 5 g6n6w.toFinset :=
  checkNode_sound (rules:=(codedRule (g6Cuts 4) (fun i => failRule true g6T 4))) (idx:=(fun j => bitsAt 0x10001060401808054501511048401202034300d09028300a0802808050401404050000c18030200c040300 18 (bitsAt 0xc00000000000000000007000000000000000000050000a0000a0000500001000080000800001000020000b0000b0000200010000110000000012000050000e0000e00005000010000d0000d00001000020000f0000f00002000050000a0000a0000500001000080000800001000020000b0000b00002000010000500009000010000200004000030000200000000000000100006 5 j))) (by decide +kernel)

def g6n7w : List Sig := [g6v4,g6v5,g6v6,g6v7,g6v9]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g6n7 : Impossible true g6T 6 g6n7w.toFinset :=
  checkNode_sound (rules:=(codedRule (g6Cuts 5) (fun i => (if i<2 then (if i<1 then (linkRule g6n2w g6n2) else (linkRule g6n3w g6n3)) else (if i<3 then (linkRule g6n4w g6n4) else (if i<4 then (linkRule g6n5w g6n5) else (linkRule g6n6w g6n6))))))) (idx:=(fun j => bitsAt 0x200048000e0002800060000400190005400110003400090001400001911064241810060201606054501511048401202048000e0c038180d0c034240a0c028200a0202800051401444050c01424050401404050000c44030900c18030200c040300 18 (bitsAt 0x85b38e816716a9b71b81638e91a1c789661691a60b8961c7856041a5b5d5a165c585b0418dd0828966568dd64c8960829131c788e44e91344988e1c780e0419dc3cd98e3c481c0418de08288e48e8de48a88e0828a304190750792551088704188708289f20688720389f0828c120088f0808c108188f208 6 j))) (by decide +kernel)

theorem bound6 : Lower true (raw 5) g6T 7 := finishBound g6Ok g6n7

def g7T : Sig := 0xfff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8

def g7H : List Nat := [2,1,2,4,4]

theorem g7Ok : basicCheck 5 g7T g7H=true := by decide +kernel

theorem g7s0 : Slice true (raw 5) g7T 0x1111111111111111111111111111111111111111111111111111111111111111 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

def g7Cuts (k i : Nat) : Rule true g7T k := (cutRule k g7s0 [])

theorem bound7 : Lower true (raw 5) g7T 6 := finishBound g7Ok ((g7Cuts 5 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g8T : Sig := 0xf8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8

def g8H : List Nat := [2,1,2,4]

theorem g8Ok : basicCheck 4 g8T g8H=true := by decide +kernel

def g8v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g8v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g8v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g8v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g8Cuts (k i : Nat) : Rule true g8T k := failRule true g8T k

def g8n0w : List Sig := [g8v0,g8v1,g8v2,g8v3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g8n0 : Impossible true g8T 3 g8n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g8Cuts 2) (fun i => failRule true g8T 2))) (idx:=(fun j => bitsAt 0x30240c0002c080b0101828060401808060000c28030900c14030200c040300 18 (bitsAt 0x7000c000900070001000a000400010002000b00050002000100060003000100020007000d00020000000000010008 4 j))) (by decide +kernel)

theorem bound8 : Lower true (raw 4) g8T 4 := finishBound g8Ok g8n0

def g9T : Sig := 0xfff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8

def g9H : List Nat := [2,1,2,4,4]

theorem g9Ok : basicCheck 5 g9T g9H=true := by decide +kernel

def g9v0 : Sig := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0

def g9v1 : Sig := 0xfff00000fff00000fff00000fff00000fff00000fff00000fff00000fff0

def g9v2 : Sig := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0

def g9v3 : Sig := 0xff00f000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f0

def g9v4 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g9v5 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g9v6 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g9v7 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g9v8 : Sig := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0

def g9v9 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g9v10 : Sig := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0

def g9v11 : Sig := 0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00

theorem g9s0 : Slice true (raw 5) g9T 0x3333333333333333333333333333333333333333333333333333333333333333 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

theorem g9s1 : Slice true (raw 5) g9T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g8Ok).1 bound8

theorem g9s2 : Slice true (raw 5) g9T 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff 4 :=
  slice_correct (ms:=[setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g8Ok).1 bound8

theorem g9s3 : Slice true (raw 5) g9T 0x1111111111111111111111111111111111111111111111111111111111111111 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g2Ok).1 bound2

theorem g9s4 : Slice true (raw 5) g9T 0x1111111111111111111111111111111111111111111111111111111111111111 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

theorem g9s5 : Slice true (raw 5) g9T 0x2222222222222222222222222222222222222222222222222222222222222222 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g2Ok).1 bound2

theorem g9s6 : Slice true (raw 5) g9T 0x2222222222222222222222222222222222222222222222222222222222222222 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

def g9Cuts (k i : Nat) : Rule true g9T k := (if i<3 then (if i<1 then (cutRule k g9s0 []) else (if i<2 then (cutRule k g9s1 []) else (cutRule k g9s2 []))) else (if i<5 then (if i<4 then (cutRule k g9s3 []) else (cutRule k g9s4 [])) else (if i<6 then (cutRule k g9s5 []) else (cutRule k g9s6 []))))

def g9n0w : List Sig := [g9v1,g9v4,g9v5,g9v6,g9v7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g9n0 : Impossible true g9T 4 g9n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g9Cuts 3) (fun i => failRule true g9T 3))) (idx:=(fun j => bitsAt 0x60001404050000c09030200c0402c280b0901828060401808030200c040300 18 (bitsAt 0x8000900050005000100060006000100020007000700020008000d0008000c000100040004000100020009000a0002000300030009000b000000000001000400040001000400010007000200070002 4 j))) (by decide +kernel)

def g9n1w : List Sig := [g9v3,g9v4,g9v5,g9v6,g9v9]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g9n1 : Impossible true g9T 4 g9n1w.toFinset :=
  checkNode_sound (rules:=(codedRule (g9Cuts 3) (fun i => failRule true g9T 3))) (idx:=(fun j => bitsAt 0x180005040140404c481311034100c04030040c0001848060401808030200c040300 18 (bitsAt 0x6000d000500050001000a000a00010002000b000b00020008000e000c0008000100040004000100020006000700020003000300080006000000000001000400040001000400010008000200090002 4 j))) (by decide +kernel)

def g9n2w : List Sig := [g9v4,g9v5,g9v6,g9v7,g9v8,g9v9]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g9n2 : Impossible true g9T 5 g9n2w.toFinset :=
  checkNode_sound (rules:=(codedRule (g9Cuts 4) (fun i => (linkRule g9n0w g9n0)))) (idx:=(fun j => bitsAt 0x80001000206040180805010130204c040c09030200c0402c280b0901828060401808031200c44030200c040300 18 (bitsAt 0xf000130000f000120000a0000f000100000a0000b000100000f0000b000010000d0000300001000020000e0000400002000110000000000000000000500000000000000000001000060000600001000020000900009000020000a0000b0000000007000010000800008000010000200009000090000200001000060000600001000020000b0000c0000200000000000000100006 5 j))) (by decide +kernel)

def g9n3w : List Sig := [g9v2,g9v4,g9v5,g9v6,g9v7,g9v9]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g9n3 : Impossible true g9T 5 g9n3w.toFinset :=
  checkNode_sound (rules:=(codedRule (g9Cuts 4) (fun i => failRule true g9T 4))) (idx:=(fun j => bitsAt 0x100054000c181006020180005010130204c040c09030200c04030000b0202c04060401808031200c44030a00c24030200c040300 18 (bitsAt 0x120001100013000110000d00013000110000d000010000f000050000100002000100000600002000110001300011000130000b000000000d0001400001000090000300001000020000a000040000200000000000000c0000000001000080000800001000020000d0000e0000200007000000000000000000000000000001000080000800001000080000100015000020001600002 5 j))) (by decide +kernel)

def g9n4w : List Sig := [g9v4,g9v5,g9v6,g9v7,g9v9,g9v10]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g9n4 : Impossible true g9T 5 g9n4w.toFinset :=
  checkNode_sound (rules:=(codedRule (g9Cuts 4) (fun i => (linkRule g9n1w g9n1)))) (idx:=(fun j => bitsAt 0x80001000106040180805044141005010131204c440c0402c080b0101848060401808030a00c24030200c040300 18 (bitsAt 0x10000000000000000000130000a0000a000120000500000000000000000001000060000600001000020000c0000c000020000a0000d000110000a0000d0000e0000000007000010000b0000b00001000020000c0000c000020000a000110000a0000e000010000800003000010000200009000040000200001000060000600001000020000e0000f0000200000000000000100006 5 j))) (by decide +kernel)

def g9n5w : List Sig := [g9v0,g9v4,g9v5,g9v6,g9v7,g9v9]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g9n5 : Impossible true g9T 5 g9n5w.toFinset :=
  checkNode_sound (rules:=(codedRule (g9Cuts 4) (fun i => failRule true g9T 4))) (idx:=(fun j => bitsAt 0x100054000c181006020180005044141005010140004c081301030100b0202c04060401808031200c44030a00c24030200c040300 18 (bitsAt 0xb00012000130000b0000e000000001000013000010000c0000500001000020000d000060000200000000000000f000000000b000140000b0001000001000090000300001000020000a00004000020000b000140000b00014000010000800008000010000200010000110000200007000000000000000000000000000001000080000800001000080000100015000020001600002 5 j))) (by decide +kernel)

def g9n6w : List Sig := [g9v4,g9v5,g9v6,g9v7,g9v9,g9v11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g9n6 : Impossible true g9T 5 g9n6w.toFinset :=
  checkNode_sound (rules:=(codedRule (g9Cuts 4) (fun i => failRule true g9T 4))) (idx:=(fun j => bitsAt 0x1000106040180805040140404c481311030240c08030100b0a02c24060401808060000c14030200c040300 18 (bitsAt 0xe00000000000000000009000000000000000000050000a0000a00005000010000700007000010000200008000080000200010000110000000012000050000f0000f00005000010000c0000c00001000020000d0000d00002000050000a0000a0000500001000070000700001000020000800008000020000100004000030000100002000050000b0000200000000000000100006 5 j))) (by decide +kernel)

def g9n7w : List Sig := [g9v4,g9v5,g9v6,g9v7,g9v9]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g9n7 : Impossible true g9T 6 g9n7w.toFinset :=
  checkNode_sound (rules:=(codedRule (g9Cuts 5) (fun i => (if i<2 then (if i<1 then (linkRule g9n2w g9n2) else (linkRule g9n3w g9n3)) else (if i<3 then (linkRule g9n4w g9n4) else (if i<4 then (linkRule g9n5w g9n5) else (linkRule g9n6w g9n6))))))) (idx:=(fun j => bitsAt 0x200048000e0002800060000400190005400110003400090001400001a1206828181006020150505040140405000131204c44130204c040d09034140c09030200c04030000b0a02c240b0202c04061201828060401808060000c48031100c28030900c14030200c040300 18 (bitsAt 0x95f49291c81cb9f81f91c49295c249b5f75bb1c74c95f2499e104199c6579e164699c041a1e08299c698a1e68799c082912249ae04d1a924cb9202499e20419923cd9e23c4992041a1508299240ea154059920829c90419932889c9283993041a160829899c9a16a549890829818c098a08098108198a8ca 6 j))) (by decide +kernel)

theorem bound9 : Lower true (raw 5) g9T 7 := finishBound g9Ok g9n7

def g10T : Sig := 0xffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8

def g10H : List Nat := [2,1,1,1,8]

theorem g10Ok : basicCheck 5 g10T g10H=true := by decide +kernel

theorem g10s0 : Slice true (raw 5) g10T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

def g10Cuts (k i : Nat) : Rule true g10T k := (cutRule k g10s0 [])

theorem bound10 : Lower true (raw 5) g10T 6 := finishBound g10Ok ((g10Cuts 5 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g11T : Sig := 0xf8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8

def g11H : List Nat := [2,1,1,4]

theorem g11Ok : basicCheck 4 g11T g11H=true := by decide +kernel

def g11v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g11v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g11v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g11v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g11Cuts (k i : Nat) : Rule true g11T k := failRule true g11T k

def g11n0w : List Sig := [g11v0,g11v1,g11v2,g11v3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g11n0 : Impossible true g11T 3 g11n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g11Cuts 2) (fun i => failRule true g11T 2))) (idx:=(fun j => bitsAt 0x30280c0002c080b0101424050401404050000c28030900c18030200c040300 18 (bitsAt 0x7000c000900070001000a000400010002000b0005000200010007000d000100020006000300020000000000010008 4 j))) (by decide +kernel)

theorem bound11 : Lower true (raw 4) g11T 4 := finishBound g11Ok g11n0

def g12T : Sig := 0xffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8

def g12H : List Nat := [2,1,1,1,8]

theorem g12Ok : basicCheck 5 g12T g12H=true := by decide +kernel

def g12v0 : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a

def g12v1 : Sig := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e

def g12v2 : Sig := 0x2222222222222222222222222222222222222222222222222222222222222222

def g12v3 : Sig := 0x3232323232323232323232323232323232323232323232323232323232323232

def g12v4 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g12v5 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g12v6 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee

def g12v7 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g12v8 : Sig := 0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa

def g12v9 : Sig := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc

def g12v10 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g12v11 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

theorem g12s0 : Slice true (raw 5) g12T 0x3333333333333333333333333333333333333333333333333333333333333333 4 :=
  slice_correct (ms:=[exchangeRow 3 4,exchangeRow 2 3,exchangeRow 1 2,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g11Ok).1 bound11

theorem g12s1 : Slice true (raw 5) g12T 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f 4 :=
  slice_correct (ms:=[exchangeRow 3 4,exchangeRow 2 3,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g11Ok).1 bound11

theorem g12s2 : Slice true (raw 5) g12T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

theorem g12s3 : Slice true (raw 5) g12T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 3 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g2Ok).1 bound2

theorem g12s4 : Slice true (raw 5) g12T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

theorem g12s5 : Slice true (raw 5) g12T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000 3 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 true]) (by decide +kernel) (by decide +kernel) (basic_data g2Ok).1 bound2

theorem g12s6 : Slice true (raw 5) g12T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 true]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

def g12Cuts (k i : Nat) : Rule true g12T k := (if i<3 then (if i<1 then (cutRule k g12s0 []) else (if i<2 then (cutRule k g12s1 []) else (cutRule k g12s2 []))) else (if i<5 then (if i<4 then (cutRule k g12s3 []) else (cutRule k g12s4 [])) else (if i<6 then (cutRule k g12s5 []) else (cutRule k g12s6 []))))

def g12n0w : List Sig := [g12v1,g12v4,g12v5,g12v10,g12v11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g12n0 : Impossible true g12T 4 g12n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g12Cuts 3) (fun i => failRule true g12T 3))) (idx:=(fun j => bitsAt 0x6000150104c08130102c08091102404060a01820060001444050101400031200c44030a00c080301 18 (bitsAt 0xb000110000c0000b000000000e0000300000000010000f000040000100006000070001000006000000000b0000900000000010000d0000200001000060000a0000b00006000000000100000000050000000008000000000600001000050000100005 5 j))) (by decide +kernel)

def g12n1w : List Sig := [g12v3,g12v4,g12v7,g12v10,g12v11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g12n1 : Impossible true g12T 4 g12n1w.toFinset :=
  checkNode_sound (rules:=(codedRule (g12Cuts 3) (fun i => failRule true g12T 3))) (idx:=(fun j => bitsAt 0x6000150104c04130002c00091102404060c01820060001444050401404031100c40030800c040300 18 (bitsAt 0xb000110000c0000b00005000100000700005000000000e000030000000001000040000f00001000050000b0000900005000000000d0000200000000010000a0000b00001000000000600005000000000100008000050000100006000000000100000 5 j))) (by decide +kernel)

def g12n2w : List Sig := [g12v4,g12v5,g12v6,g12v7,g12v10,g12v11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g12n2 : Impossible true g12T 5 g12n2w.toFinset :=
  checkNode_sound (rules:=(codedRule (g12Cuts 4) (fun i => (linkRule g12n0w g12n0)))) (idx:=(fun j => bitsAt 0x20000400041a1206828181006020180005404130204c040b0202444090a02404060a01810060201444050401404031200c44030a00c080301 18 (bitsAt 0xb000120000d0000b0000500011000070000500015000130001500013000000000f000030000000001000100000400001000050000b0000a000050000b000140000b00014000000000b0001600000000010000e000020000100005000180000500017000000000500008000000000100008000050000100009000000000000000000060000000000000000000000001000000000c 5 j))) (by decide +kernel)

def g12n3w : List Sig := [g12v2,g12v4,g12v5,g12v7,g12v10,g12v11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g12n3 : Impossible true g12T 5 g12n3w.toFinset :=
  checkNode_sound (rules:=(codedRule (g12Cuts 4) (fun i => failRule true g12T 4))) (idx:=(fun j => bitsAt 0x100054000c181006020180005810150104c080b0202444090101850060c01828060401808060001444050401404031200c28030200c040300 18 (bitsAt 0xe000140000f0000e000050001200007000050000a000130000d0000a0000200011000040000200017000150001800015000050000e0000b000050000a0000e0000c0000a000020001000003000020000e000160000e000160000800005000090000500002000090000500002000050000900005000090000000000000020000a0000000000000010000000006000000000000000 5 j))) (by decide +kernel)

def g12n4w : List Sig := [g12v4,g12v5,g12v7,g12v8,g12v10,g12v11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g12n4 : Impossible true g12T 5 g12n4w.toFinset :=
  checkNode_sound (rules:=(codedRule (g12Cuts 4) (fun i => (linkRule g12n1w g12n1)))) (idx:=(fun j => bitsAt 0x20000400001c1407030181006020180005410150104c040d0402444090c02404060c01810060201450051101430050401404031100c080301 18 (bitsAt 0xb000120000d0000b0001500013000150001300003000100000600003000000000f0000200000000040001100007000040000b000140000b00014000030000b0001600003000000000b0000a00000000040000e0000500004000080000000000000000001800000000000001700001000000000000000000000000300009000000000300004000000000c00000000090000000004 5 j))) (by decide +kernel)

def g12n5w : List Sig := [g12v0,g12v4,g12v5,g12v7,g12v10,g12v11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g12n5 : Impossible true g12T 5 g12n5w.toFinset :=
  checkNode_sound (rules:=(codedRule (g12Cuts 4) (fun i => failRule true g12T 4))) (idx:=(fun j => bitsAt 0x100054000c181006020180005808150404c040d0402444090101848060c01828060401808060001450050c01410050101400031100c080301 18 (bitsAt 0xe000140000f0000e00009000130000d00009000000001100002000000000500012000070000500017000150001800015000090000e0000b00009000000000e0000c00000000050001000006000050000e000160000e00016000000000800009000000000300000000050000900000000000000400000000000000a0000000005000000000a000000000a00001000000000000000 5 j))) (by decide +kernel)

def g12n6w : List Sig := [g12v4,g12v5,g12v7,g12v9,g12v10,g12v11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g12n6 : Impossible true g12T 5 g12n6w.toFinset :=
  checkNode_sound (rules:=(codedRule (g12Cuts 4) (fun i => failRule true g12T 4))) (idx:=(fun j => bitsAt 0x400001a1206828180806000160405808130202444090802404090001850061201830060a01810060201410050100c48030a00c080301 18 (bitsAt 0xd000130000f0000d0001500014000150001400006000110000a0000600007000120000b0000700001000100000300001000160000d000160000d000060000d0000800006000070000d0000900007000010000c000020000100004000000000000000000000000000000000000000e00001000010000e000060000700000000170000100005000050000100005000010000100005 5 j))) (by decide +kernel)

def g12n7w : List Sig := [g12v4,g12v5,g12v7,g12v10,g12v11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g12n7 : Impossible true g12T 6 g12n7w.toFinset :=
  checkNode_sound (rules:=(codedRule (g12Cuts 5) (fun i => (if i<2 then (if i<1 then (linkRule g12n2w g12n2) else (linkRule g12n3w g12n3)) else (if i<3 then (linkRule g12n4w g12n4) else (if i<4 then (linkRule g12n5w g12n5) else (linkRule g12n6w g12n6))))))) (idx:=(fun j => bitsAt 0x200048000e0002800060000400190005400110003400090001400001c14070301a1206828181006020180005444150104c48131104c081301038300e0a02444090802404090001830060a01810060201444050401404050000c48031100c28030200c040300 18 (bitsAt 0x91b3cf92371a91b7119233cf91f1c799b65899f64991b1c791d04199b59499d58491b04192508299b5d59a75c591b0829201c794f48f96048c90f1c791e04194f4cf95e4cd90f04190f08295c40e94f40391c08288a0418472c7b0a2ca847041887082aca206a8720788a082841200a4b080a0108184b208 6 j))) (by decide +kernel)

theorem bound12 : Lower true (raw 5) g12T 7 := finishBound g12Ok g12n7

def g13T : Sig := 0xfffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeee

def g13H : List Nat := [0,0,8,4,4]

theorem g13Ok : basicCheck 5 g13T g13H=true := by decide +kernel

theorem g13s0 : Slice true (raw 5) g13T 0x1111111111111111111111111111111111111111111111111111111111111111 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

def g13Cuts (k i : Nat) : Rule true g13T k := (cutRule k g13s0 [])

theorem bound13 : Lower true (raw 5) g13T 6 := finishBound g13Ok ((g13Cuts 5 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g14T : Sig := 0xfffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeee

def g14H : List Nat := [0,0,8,4,4]

theorem g14Ok : basicCheck 5 g14T g14H=true := by decide +kernel

theorem g14s0 : Slice true (raw 5) g14T 0x1111111111111111111111111111111111111111111111111111111111111111 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g2Ok).1 bound2

def g14Cuts (k i : Nat) : Rule true g14T k := (cutRule k g14s0 [])

theorem bound14 : Lower true (raw 5) g14T 5 := finishBound g14Ok ((g14Cuts 4 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g15T : Sig := 0xfff8f888fff8f888fff8f888fff8f888fff8f888fff8f888fff8f888fff8f888

def g15H : List Nat := [2,1,8,4,4]

theorem g15Ok : basicCheck 5 g15T g15H=true := by decide +kernel

theorem g15s0 : Slice true (raw 5) g15T 0x1111111111111111111111111111111111111111111111111111111111111111 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

def g15Cuts (k i : Nat) : Rule true g15T k := (cutRule k g15s0 [])

theorem bound15 : Lower true (raw 5) g15T 6 := finishBound g15Ok ((g15Cuts 5 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g16T : Sig := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea

def g16H : List Nat := [0,4,2,2]

theorem g16Ok : basicCheck 4 g16T g16H=true := by decide +kernel

theorem g16s0 : Slice true (raw 4) g16T 0x5555555555555555555555555555555555555555555555555555555555555555 4 :=
  slice_correct (ms:=[exchangeRow 2 3,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

def g16Cuts (k i : Nat) : Rule true g16T k := (cutRule k g16s0 [])

theorem bound16 : Lower true (raw 4) g16T 5 := finishBound g16Ok ((g16Cuts 4 0).property (raw 4) (by decide +kernel) (by decide +kernel))

def g17T : Sig := 0xffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8

def g17H : List Nat := [2,1,1,0]

theorem g17Ok : basicCheck 4 g17T g17H=true := by decide +kernel

theorem g17s0 : Slice true (raw 4) g17T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 4 :=
  slice_correct (ms:=[setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g0Ok).1 bound0

def g17Cuts (k i : Nat) : Rule true g17T k := (cutRule k g17s0 [])

theorem bound17 : Lower true (raw 4) g17T 5 := finishBound g17Ok ((g17Cuts 4 0).property (raw 4) (by decide +kernel) (by decide +kernel))

def g18T : Sig := 0xffffffffffffffffffffffe8ffffeae8ffffffe8ffffeae8ffe8ffe8ffe8eae8

def g18H : List Nat := [2,1,1,1,8,8,16,16]

theorem g18Ok : basicCheck 8 g18T g18H=true := by decide +kernel

def g18v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g18v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g18v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g18v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g18v4 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g18v5 : Sig := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa

def g18v6 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000

def g18v7 : Sig := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000

def g18v8 : Sig := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000

theorem g18s0 : Slice true (raw 8) g18T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 9 :=
  slice_correct (ms:=[exchangeRow 5 7,exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g1Ok).1 bound1

theorem g18s1 : Slice true (raw 8) g18T 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff 8 :=
  slice_correct (ms:=[exchangeRow 5 7,exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g3Ok).1 bound3

theorem g18s2 : Slice true (raw 8) g18T 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff 9 :=
  slice_correct (ms:=[exchangeRow 5 7,exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g1Ok).1 bound1

theorem g18s3 : Slice true (raw 8) g18T 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 8 :=
  slice_correct (ms:=[exchangeRow 5 7,exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g3Ok).1 bound3

theorem g18s4 : Slice true (raw 8) g18T 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 9 :=
  slice_correct (ms:=[exchangeRow 5 7,exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g1Ok).1 bound1

theorem g18s5 : Slice true (raw 8) g18T 0x101010101010101010101010101010101010101010101010101010101010101 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g4Ok).1 bound4

theorem g18s6 : Slice true (raw 8) g18T 0x101010101010101010101010101010101010101010101010101010101010101 7 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g6Ok).1 bound6

theorem g18s7 : Slice true (raw 8) g18T 0x1010101010101010101010101010101010101010101010101010101010101010 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g4Ok).1 bound4

theorem g18s8 : Slice true (raw 8) g18T 0x1010101010101010101010101010101010101010101010101010101010101010 7 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g6Ok).1 bound6

theorem g18s9 : Slice true (raw 8) g18T 0x404040404040404040404040404040404040404040404040404040404040404 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 true,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g4Ok).1 bound4

theorem g18s10 : Slice true (raw 8) g18T 0x404040404040404040404040404040404040404040404040404040404040404 7 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 true,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g6Ok).1 bound6

theorem g18s11 : Slice true (raw 8) g18T 0x3030303000000000303030300000000030303030000000003030303 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,setBitRow 1 false,setBitRow 2 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g7Ok).1 bound7

theorem g18s12 : Slice true (raw 8) g18T 0x3030303000000000303030300000000030303030000000003030303 7 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,setBitRow 1 false,setBitRow 2 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g9Ok).1 bound9

theorem g18s13 : Slice true (raw 8) g18T 0xffff0000ffff 6 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g10Ok).1 bound10

theorem g18s14 : Slice true (raw 8) g18T 0xffff0000ffff 7 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g12Ok).1 bound12

theorem g18s15 : Slice true (raw 8) g18T 0xffff0000ffff00000000000000000000000000000000 6 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 false,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g10Ok).1 bound10

theorem g18s16 : Slice true (raw 8) g18T 0xffff0000ffff00000000000000000000000000000000 7 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 false,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g12Ok).1 bound12

theorem g18s17 : Slice true (raw 8) g18T 0xffff0000ffff0000000000000000 6 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 true,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g10Ok).1 bound10

theorem g18s18 : Slice true (raw 8) g18T 0xffff0000ffff0000000000000000 7 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 true,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g12Ok).1 bound12

theorem g18s19 : Slice true (raw 8) g18T 0x4444444400000000444444440000000044444444000000004444444400000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g13Ok).1 bound13

theorem g18s20 : Slice true (raw 8) g18T 0x22222222000000002222222200000000222222220000000022222222 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g14Ok).1 bound14

theorem g18s21 : Slice true (raw 8) g18T 0x22222222000000002222222200000000222222220000000022222222 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g13Ok).1 bound13

theorem g18s22 : Slice true (raw 8) g18T 0x2222222200000000222222220000000022222222000000002222222200000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g14Ok).1 bound14

theorem g18s23 : Slice true (raw 8) g18T 0x550055000000000055005500000000005500550000000000550055 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 false,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g15Ok).1 bound15

theorem g18s24 : Slice true (raw 8) g18T 0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 true,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g13Ok).1 bound13

theorem g18s25 : Slice true (raw 8) g18T 0x202020202020202020202020202020202020202020202020202020202020202 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 true,setBitRow 1 false,setBitRow 2 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g16Ok).1 bound16

theorem g18s26 : Slice true (raw 8) g18T 0x22002200220022002200220022002200220022002200220022002200220022 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g16Ok).1 bound16

theorem g18s27 : Slice true (raw 8) g18T 0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 1,setBitRow 0 true,setBitRow 2 false,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g16Ok).1 bound16

theorem g18s28 : Slice true (raw 8) g18T 0xff000000ff0000000000000000000000ff000000ff0000 5 :=
  slice_correct (ms:=[exchangeRow 3 7,setBitRow 3 false,setBitRow 4 true,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g17Ok).1 bound17

theorem g18s29 : Slice true (raw 8) g18T 0xff000000ff000000ff000000ff0000 5 :=
  slice_correct (ms:=[exchangeRow 3 6,setBitRow 3 false,setBitRow 4 true,setBitRow 5 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g17Ok).1 bound17

theorem g18s30 : Slice true (raw 8) g18T 0xffff0000ffff0000 5 :=
  slice_correct (ms:=[setBitRow 4 true,setBitRow 5 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g17Ok).1 bound17

def g18Cuts (k i : Nat) : Rule true g18T k := (if i<15 then (if i<7 then (if i<3 then (if i<1 then (cutRule k g18s0 []) else (if i<2 then (cutRule k g18s1 []) else (cutRule k g18s2 []))) else (if i<5 then (if i<4 then (cutRule k g18s3 []) else (cutRule k g18s4 [])) else (if i<6 then (cutRule k g18s5 []) else (cutRule k g18s6 [])))) else (if i<11 then (if i<9 then (if i<8 then (cutRule k g18s7 []) else (cutRule k g18s8 [])) else (if i<10 then (cutRule k g18s9 []) else (cutRule k g18s10 []))) else (if i<13 then (if i<12 then (cutRule k g18s11 []) else (cutRule k g18s12 [])) else (if i<14 then (cutRule k g18s13 []) else (cutRule k g18s14 []))))) else (if i<23 then (if i<19 then (if i<17 then (if i<16 then (cutRule k g18s15 []) else (cutRule k g18s16 [])) else (if i<18 then (cutRule k g18s17 []) else (cutRule k g18s18 []))) else (if i<21 then (if i<20 then (cutRule k g18s19 []) else (cutRule k g18s20 [])) else (if i<22 then (cutRule k g18s21 []) else (cutRule k g18s22 [])))) else (if i<27 then (if i<25 then (if i<24 then (cutRule k g18s23 []) else (cutRule k g18s24 [])) else (if i<26 then (cutRule k g18s25 []) else (cutRule k g18s26 []))) else (if i<29 then (if i<28 then (cutRule k g18s27 []) else (cutRule k g18s28 [])) else (if i<30 then (cutRule k g18s29 []) else (cutRule k g18s30 []))))))

def g18n0w : List Sig := [g18v0,g18v1,g18v2,g18v3,g18v4,g18v5,g18v6,g18v7,g18v8]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g18n0 : Impossible true g18T 10 g18n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g18Cuts 9) (fun i => failRule true g18T 9))) (idx:=(fun j => bitsAt 0x1001e40075001c4006d001a4006500184005d00164005500144004d00114003d000d40031000b40025000740015000332220c84830200c0402c0c0a88825050921224604911124404901124040898122404858121404838120c0471611c0c0684815050521214584514114444510114044501012504490111504450110d0443010ccc82c0c0a82828880a12028200a020280009484250108c842301070501a1206040180805450151105404133204c48131104c040e0c03828098102504092102444090101830060a01810060201604054101484051101404038100d04032100c48031100c080301 18 (bitsAt 0xcb39a34c9167c5cd3a7cec915a34cb353a7b916645bd3662acb153a7c316c45cb3accec316cc5cb3ac4ec915c38cb3a4c7c9164c5cb39c38cb40810c516243cb42214c514810cb2c387c316141a92e10bc314387cb28000c31603fab2a006c314000c320c99a716cc5c322cc6cb14c99c8f53a7b8d1e34bcf5e29c8d13a7c2d2c34c93ed4fc2d2d34c93ec4fc8d24b4c93dc36c8d1c34c93e4c9c944810c4d19b2c945993c4d0810c8ec387c2d18b0a8ed88ac2d0387c8e8000c2d17aeaae9785c2d0000c2dcc99a6d2d34c2ded35c8d0c99c386b57b89eda7c386dd2b89eb27c991c38bc9df27c991f39b89dc27b89c810c589426bc9d412c588810b8b0387c29d2a4bcb1289c29c387b8ac000c29d1a2b8ad184c29c000c384c99b89d6a7c38569ab89cc99c94e99e000000000000000000000c581428c374810c374810c57d428c35060cc34c387c350387c34c60cc35468dc34c000c354000c34c68dc362c01000000000000000000000c980810c4e0f9fc980f91c4e0810a950387c2e0e1bc950e08c2e0387ab54000c2e0c17c954c02c2e0000c2e2c38c94cc990000000a74ec03c484387c240a90c684a8ec240387c480000c240b10c480b0fc240000c240c90c47f01fc242e90c47cc99c230000c21c687c23068cc21c000c21cc87c230e8cc21ce87c230c8cc200e80c234c8dc200c80c234e8d 7 j))) (by decide +kernel)

def g18n1w : List Sig := [g18v0,g18v1,g18v2,g18v3,g18v4,g18v6,g18v7,g18v8]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g18n1 : Impossible true g18T 11 g18n1w.toFinset :=
  checkNode_sound (rules:=(codedRule (g18Cuts 10) (fun i => (linkRule g18n0w g18n0)))) (idx:=(fun j => bitsAt 0x80001001240041000e40031000a40021000640011000340009000140000c88832120c08030100b0302a220941424848911124200901024000898122404858121404838220e04830220c0470601c0c0684815050521214504511114180504014040500012504490111504450110d08434110c0843010b0302a0a0a22028480a08028080a000252109404232208c84230208c041c14070301a1206828188806120181006020180005444150104c48131104c081301038300e0a02604094102484091102420090102400060c01828060401808058101504052101444050401404050000e08038100d08034100c88032100c48031100c28030200c040300 18 (bitsAt 0xd97e2c5d963058d97f05fd9622c5d979b36d762ed8db7aeb9d761b36d9613a7d97ecd7d962caad97d3a7d984c18db62b55db86b1dd960c18d37068dd162a53d372a12d16068dd56c081d1628cfd56e88ad160081d968102d162950db6a90bd160102d935b36d716645dd36638d715b36d9153a7d982344d916329d9813a7d988c18dd161c2dd8a19cd914c18d32c68dd1160c0d32e091d11468dd528081d115f3cd529f08d114081d920102d115fbddd21f89d114102d7953a7d8da736cd9e747d6d93a7d6d8c18c98dbb5c8d9b9bd78cc18d2ec68dd0d9a33d2eda10d0d868dd4e8081d0d98afd4e9886d0d8081d794102d0d9930cd9d907d0d8102d89cc18c919426ca9d41ad918c18d2b468dd09d2a4d2b528fd09c68dd4ac081d09d120d4ad104d09c081d924102d09d1a1df25185d09c102d2b868dd060f18d2b8f15d06068dd4b0081d060f98d4b0f96d060081c860102d0a0c97ca60c83d0a0102d04c081d034a0dd04ca13d034081d034102d04c70cd03470dd04c102d004700d050100d004101d05070e 7 j))) (by decide +kernel)

theorem bound18 : Lower true (raw 8) g18T 12 := finishBound g18Ok g18n1

def g19T : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8

def g19H : List Nat := [2,1,1]

theorem g19Ok : basicCheck 3 g19T g19H=true := by decide +kernel

def g19v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g19v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g19v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g19Cuts (k i : Nat) : Rule false g19T k := failRule false g19T k

def g19n0w : List Sig := [g19v0,g19v1,g19v2]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g19n0 : Impossible false g19T 2 g19n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g19Cuts 1) (fun i => failRule false g19T 1))) (idx:=(fun j => bitsAt 0x60201410050100c080301 18 (bitsAt 0x4000000000002001000000000003 3 j))) (by decide +kernel)

theorem bound19 : Lower false (raw 3) g19T 3 := finishBound g19Ok g19n0

def g20T : Sig := 0xffffffe8ffe8e8e8ffffffe8ffe8e8e8ffffffe8ffe8e8e8ffffffe8ffe8e8e8

def g20H : List Nat := [2,1,1,16,8,8]

theorem g20Ok : basicCheck 6 g20T g20H=true := by decide +kernel

def g20v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g20v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g20v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g20v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g20v4 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g20v5 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000

theorem g20s0 : Slice false (raw 6) g20T 0x101010101010101010101010101010101010101010101010101010101010101 3 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

theorem g20s1 : Slice false (raw 6) g20T 0x1010101010101010101010101010101010101010101010101010101010101010 3 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

theorem g20s2 : Slice false (raw 6) g20T 0x404040404040404040404040404040404040404040404040404040404040404 3 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 true,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

theorem g20s3 : Slice false (raw 6) g20T 0x202020202020202020202020202020202020202020202020202020202020202 3 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 true,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

theorem g20s4 : Slice false (raw 6) g20T 0xff00000000000000ff00000000000000ff00000000000000ff 3 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

def g20Cuts (k i : Nat) : Rule false g20T k := (if i<2 then (if i<1 then (cutRule k g20s0 []) else (cutRule k g20s1 [])) else (if i<3 then (cutRule k g20s2 []) else (if i<4 then (cutRule k g20s3 []) else (cutRule k g20s4 []))))

def g20n0w : List Sig := [g20v0,g20v1,g20v2,g20v3,g20v4,g20v5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g20n0 : Impossible false g20T 7 g20n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g20Cuts 6) (fun i => failRule false g20T 6))) (idx:=(fun j => bitsAt 0x100044000d00024000500000c08430110a084280c0a028280906050181206044180c06028180901830060a01484051101430050900c88032100c48031100c280309 18 (bitsAt 0xe5af6e498c0000000000e4ab2e59ef0000000000cd129c48c60000000000d4c84c48000000000000dc8a5c48210000000000e31ece5eb50000000000cb908c30c60000000000d3442c30000000000000db063c30210000000000cc4c6c3cc60000000000d4000c3c000000000000dbc21c3c210000000000c296ac18000000000000c18e6c28210000000000c0020c2ce7 5 j))) (by decide +kernel)

theorem bound20 : Lower false (raw 6) g20T 8 := finishBound g20Ok g20n0

def g21T : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8

def g21H : List Nat := [2,1,1]

theorem g21Ok : basicCheck 3 g21T g21H=true := by decide +kernel

def g21v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g21v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g21v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g21Cuts (k i : Nat) : Rule false g21T k := failRule false g21T k

def g21n0w : List Sig := [g21v0,g21v1,g21v2]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g21n0 : Impossible false g21T 3 g21n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g21Cuts 2) (fun i => failRule false g21T 2))) (idx:=(fun j => bitsAt 0x1810060201410050100c080301 18 (bitsAt 0x12c08000000009a10900000000815b 3 j))) (by decide +kernel)

theorem bound21 : Lower false (raw 3) g21T 4 := finishBound g21Ok g21n0

def g22T : Sig := 0xffffffe8ffe8e8e8ffffffe8ffe8e8e8ffffffe8ffe8e8e8ffffffe8ffe8e8e8

def g22H : List Nat := [2,1,1,16,8,8]

theorem g22Ok : basicCheck 6 g22T g22H=true := by decide +kernel

def g22v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g22v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g22v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g22v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g22v4 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g22v5 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000

theorem g22s0 : Slice false (raw 6) g22T 0x101010101010101010101010101010101010101010101010101010101010101 4 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g22s1 : Slice false (raw 6) g22T 0x1010101010101010101010101010101010101010101010101010101010101010 4 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g22s2 : Slice false (raw 6) g22T 0x404040404040404040404040404040404040404040404040404040404040404 4 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 true,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g22s3 : Slice false (raw 6) g22T 0x202020202020202020202020202020202020202020202020202020202020202 4 :=
  slice_correct (ms:=[exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 true,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g22s4 : Slice false (raw 6) g22T 0xff00000000000000ff00000000000000ff00000000000000ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g22Cuts (k i : Nat) : Rule false g22T k := (if i<2 then (if i<1 then (cutRule k g22s0 []) else (cutRule k g22s1 [])) else (if i<3 then (cutRule k g22s2 []) else (if i<4 then (cutRule k g22s3 []) else (cutRule k g22s4 []))))

def g22n0w : List Sig := [g22v0,g22v1,g22v2,g22v3,g22v4,g22v5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g22n0 : Impossible false g22T 8 g22n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g22Cuts 7) (fun i => failRule false g22T 7))) (idx:=(fun j => bitsAt 0x100044000d00024000500000c08430110a084280c0a028280906050181206044180c06028180901830060a01484051101430050900c88032100c48031100c280309 18 (bitsAt 0xe5af6e498c0000000000e4ab2e59ef0000000000cd129c48c60000000000d4c84c48000000000000dc8a5c48210000000000e31ece5eb50000000000cb908c30c60000000000d3442c30000000000000db063c30210000000000cc4c6c3cc60000000000d4000c3c000000000000dbc21c3c210000000000c296ac18000000000000c18e6c28210000000000c0020c2ce7 5 j))) (by decide +kernel)

theorem bound22 : Lower false (raw 6) g22T 9 := finishBound g22Ok g22n0

def g23T : Sig := 0xf8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8f8c8

def g23H : List Nat := [2,1,2,4]

theorem g23Ok : basicCheck 4 g23T g23H=true := by decide +kernel

def g23v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g23v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g23v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g23v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g23Cuts (k i : Nat) : Rule false g23T k := failRule false g23T k

def g23n0w : List Sig := [g23v0,g23v1,g23v2,g23v3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g23n0 : Impossible false g23T 3 g23n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g23Cuts 2) (fun i => failRule false g23T 2))) (idx:=(fun j => bitsAt 0x3024060a01814030a00c240305 18 (bitsAt 0x4004000000001000000000002002000000000000000000005002000000000003 3 j))) (by decide +kernel)

theorem bound23 : Lower false (raw 4) g23T 4 := finishBound g23Ok g23n0

def g24T : Sig := 0xfff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8

def g24H : List Nat := [2,1,2,4,4]

theorem g24Ok : basicCheck 5 g24T g24H=true := by decide +kernel

def g24v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g24v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g24v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g24v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g24v4 : Sig := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0

def g24v5 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g24v6 : Sig := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0

def g24v7 : Sig := 0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00

theorem g24s0 : Slice false (raw 5) g24T 0x3333333333333333333333333333333333333333333333333333333333333333 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g24s1 : Slice false (raw 5) g24T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g23Ok).1 bound23

theorem g24s2 : Slice false (raw 5) g24T 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff 4 :=
  slice_correct (ms:=[setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g23Ok).1 bound23

theorem g24s3 : Slice false (raw 5) g24T 0x1111111111111111111111111111111111111111111111111111111111111111 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

theorem g24s4 : Slice false (raw 5) g24T 0x1111111111111111111111111111111111111111111111111111111111111111 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g24s5 : Slice false (raw 5) g24T 0x2222222222222222222222222222222222222222222222222222222222222222 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

theorem g24s6 : Slice false (raw 5) g24T 0x2222222222222222222222222222222222222222222222222222222222222222 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g24Cuts (k i : Nat) : Rule false g24T k := (if i<3 then (if i<1 then (cutRule k g24s0 []) else (if i<2 then (cutRule k g24s1 []) else (cutRule k g24s2 []))) else (if i<5 then (if i<4 then (cutRule k g24s3 []) else (cutRule k g24s4 [])) else (if i<6 then (cutRule k g24s5 []) else (cutRule k g24s6 []))))

def g24n0w : List Sig := [g24v0,g24v1,g24v2,g24v3,g24v4,g24v5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g24n0 : Impossible false g24T 5 g24n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g24Cuts 4) (fun i => failRule false g24T 4))) (idx:=(fun j => bitsAt 0x400081809050140c0903014060a01814031200c44030a00c240305 18 (bitsAt 0x9000b00000000000a00070000000000090006000000000003000000000000000400020000000000000000000000000000000000000000000000000000000000020002000000000000000600000000000100000000000000020002000000000000000000000000000800020000000000000005 4 j))) (by decide +kernel)

def g24n1w : List Sig := [g24v0,g24v1,g24v2,g24v3,g24v5,g24v6]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g24n1 : Impossible false g24T 5 g24n1w.toFinset :=
  checkNode_sound (rules:=(codedRule (g24Cuts 4) (fun i => failRule false g24T 4))) (idx:=(fun j => bitsAt 0x1000106044141103014061201814031200c44030a00c240305 18 (bitsAt 0x7000a0000000000000000000000000000000000000000000400020000000000090007000000000000000600000000000300000000000000040002000000000007000600000000000100000000000000020002000000000000000000000000000800020000000000000005 4 j))) (by decide +kernel)

def g24n2w : List Sig := [g24v0,g24v1,g24v2,g24v3,g24v5,g24v7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g24n2 : Impossible false g24T 5 g24n2w.toFinset :=
  checkNode_sound (rules:=(codedRule (g24Cuts 4) (fun i => failRule false g24T 4))) (idx:=(fun j => bitsAt 0x400040c0901848060a01814031200c44030a00c240305 18 (bitsAt 0x60006000000000001000000000000000200020000000000000009000000000007000600000000000300000000000000040002000000000006000600000000000100000000000000020002000000000000000000000000000800020000000000000005 4 j))) (by decide +kernel)

def g24n3w : List Sig := [g24v0,g24v1,g24v2,g24v3,g24v5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g24n3 : Impossible false g24T 6 g24n3w.toFinset :=
  checkNode_sound (rules:=(codedRule (g24Cuts 5) (fun i => (if i<1 then (linkRule g24n0w g24n0) else (if i<2 then (linkRule g24n1w g24n1) else (linkRule g24n2w g24n2)))))) (idx:=(fun j => bitsAt 0x2000280006000040019000540011000340009000140000181206044180a060241405030240c0501848060a01814031200c44030a00c240305 18 (bitsAt 0xc2dab829080000000000ba8e78acc600000000009b063928000000000000a2884928420000000000b20c6834c600000000009b821920000000000000a204292042000000000099800924000000000000a26a991842000000000090040915e5 5 j))) (by decide +kernel)

theorem bound24 : Lower false (raw 5) g24T 7 := finishBound g24Ok g24n3

def g25T : Sig := 0xf8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8

def g25H : List Nat := [2,1,1,4]

theorem g25Ok : basicCheck 4 g25T g25H=true := by decide +kernel

def g25v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g25v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g25v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g25v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g25Cuts (k i : Nat) : Rule false g25T k := failRule false g25T k

def g25n0w : List Sig := [g25v0,g25v1,g25v2,g25v3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g25n0 : Impossible false g25T 3 g25n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g25Cuts 2) (fun i => failRule false g25T 2))) (idx:=(fun j => bitsAt 0x3028050901418030a00c240306 18 (bitsAt 0x4004000000001001000000002000000000005001000000000000000000000003 3 j))) (by decide +kernel)

theorem bound25 : Lower false (raw 4) g25T 4 := finishBound g25Ok g25n0

def g26T : Sig := 0xffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8

def g26H : List Nat := [2,1,1,1,8]

theorem g26Ok : basicCheck 5 g26T g26H=true := by decide +kernel

def g26v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g26v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g26v2 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee

def g26v3 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g26v4 : Sig := 0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa

def g26v5 : Sig := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc

def g26v6 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g26v7 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

theorem g26s0 : Slice false (raw 5) g26T 0x3333333333333333333333333333333333333333333333333333333333333333 4 :=
  slice_correct (ms:=[exchangeRow 3 4,exchangeRow 2 3,exchangeRow 1 2,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g25Ok).1 bound25

theorem g26s1 : Slice false (raw 5) g26T 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f 4 :=
  slice_correct (ms:=[exchangeRow 3 4,exchangeRow 2 3,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g25Ok).1 bound25

theorem g26s2 : Slice false (raw 5) g26T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g26s3 : Slice false (raw 5) g26T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 3 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

theorem g26s4 : Slice false (raw 5) g26T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g26s5 : Slice false (raw 5) g26T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000 3 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 true]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

theorem g26s6 : Slice false (raw 5) g26T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 true]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g26Cuts (k i : Nat) : Rule false g26T k := (if i<3 then (if i<1 then (cutRule k g26s0 []) else (if i<2 then (cutRule k g26s1 []) else (cutRule k g26s2 []))) else (if i<5 then (if i<4 then (cutRule k g26s3 []) else (cutRule k g26s4 [])) else (if i<6 then (cutRule k g26s5 []) else (cutRule k g26s6 []))))

def g26n0w : List Sig := [g26v0,g26v1,g26v2,g26v3,g26v6,g26v7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g26n0 : Impossible false g26T 5 g26n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g26Cuts 4) (fun i => failRule false g26T 4))) (idx:=(fun j => bitsAt 0x1000106048181106028091102428060a01444031200c44030a 18 (bitsAt 0x6000600000000000300030000000000070007000000000001000100000000000200000000000000040003000000000006000800000000000900010000000000000000000000000003000a00000000000400010000000000030000000000000000000000000000000000000000000000000005 4 j))) (by decide +kernel)

def g26n1w : List Sig := [g26v0,g26v1,g26v3,g26v4,g26v6,g26v7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g26n1 : Impossible false g26T 5 g26n1w.toFinset :=
  checkNode_sound (rules:=(codedRule (g26Cuts 4) (fun i => failRule false g26T 4))) (idx:=(fun j => bitsAt 0x40000181406044180c06028091102430060c014500511014300311 18 (bitsAt 0x600060000000000080007000000000002000200000000000000000000000000030001000000000006000900000000000a0002000000000004000000000000000100010000000000000000000000000000000b0000000000000000000000000004000000000000000000050000000000000001 4 j))) (by decide +kernel)

def g26n2w : List Sig := [g26v0,g26v1,g26v3,g26v5,g26v6,g26v7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g26n2 : Impossible false g26T 5 g26n2w.toFinset :=
  checkNode_sound (rules:=(codedRule (g26Cuts 4) (fun i => failRule false g26T 4))) (idx:=(fun j => bitsAt 0x40000181206028091102428061401848060c01828050c00c48030a 18 (bitsAt 0x80008000000000009000900000000000500030000000000060004000000000001000000000000000a0008000000000003000300000000000400040000000000000000000000000000000000000000000000000000000000000007000000000000000b00000000000200000000000000000002 4 j))) (by decide +kernel)

def g26n3w : List Sig := [g26v0,g26v1,g26v3,g26v6,g26v7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g26n3 : Impossible false g26T 6 g26n3w.toFinset :=
  checkNode_sound (rules:=(codedRule (g26Cuts 5) (fun i => (if i<1 then (linkRule g26n0w g26n0) else (if i<2 then (linkRule g26n1w g26n1) else (linkRule g26n2w g26n2)))))) (idx:=(fun j => bitsAt 0x2000280006000040019000540011000340009000140000181406048181106030180a02444060c01828051101430031200c44030a 18 (bitsAt 0x820e783ce70000000000924848208400000000009202182021000000000094c428200000000000008b0a581c8400000000008acc681c21000000000089c00828000000000000b14c5690210000000000a9063714000000000000a040069863 5 j))) (by decide +kernel)

theorem bound26 : Lower false (raw 5) g26T 7 := finishBound g26Ok g26n3

def g27T : Sig := 0xfcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8

def g27H : List Nat := [2,1,2,2]

theorem g27Ok : basicCheck 4 g27T g27H=true := by decide +kernel

theorem g27s0 : Slice false (raw 4) g27T 0x5555555555555555555555555555555555555555555555555555555555555555 3 :=
  slice_correct (ms:=[exchangeRow 2 3,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

def g27Cuts (k i : Nat) : Rule false g27T k := (cutRule k g27s0 [])

theorem bound27 : Lower false (raw 4) g27T 4 := finishBound g27Ok ((g27Cuts 3 0).property (raw 4) (by decide +kernel) (by decide +kernel))

def g28T : Sig := 0xfcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8fcc8

def g28H : List Nat := [2,1,2,2]

theorem g28Ok : basicCheck 4 g28T g28H=true := by decide +kernel

theorem g28s0 : Slice false (raw 4) g28T 0x5555555555555555555555555555555555555555555555555555555555555555 4 :=
  slice_correct (ms:=[exchangeRow 2 3,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g28Cuts (k i : Nat) : Rule false g28T k := (cutRule k g28s0 [])

theorem bound28 : Lower false (raw 4) g28T 5 := finishBound g28Ok ((g28Cuts 4 0).property (raw 4) (by decide +kernel) (by decide +kernel))

def g29T : Sig := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea

def g29H : List Nat := [0,4,2,2]

theorem g29Ok : basicCheck 4 g29T g29H=true := by decide +kernel

theorem g29s0 : Slice false (raw 4) g29T 0x5555555555555555555555555555555555555555555555555555555555555555 3 :=
  slice_correct (ms:=[exchangeRow 2 3,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

def g29Cuts (k i : Nat) : Rule false g29T k := (cutRule k g29s0 [])

theorem bound29 : Lower false (raw 4) g29T 4 := finishBound g29Ok ((g29Cuts 3 0).property (raw 4) (by decide +kernel) (by decide +kernel))

def g30T : Sig := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea

def g30H : List Nat := [0,4,2,2]

theorem g30Ok : basicCheck 4 g30T g30H=true := by decide +kernel

theorem g30s0 : Slice false (raw 4) g30T 0x5555555555555555555555555555555555555555555555555555555555555555 4 :=
  slice_correct (ms:=[exchangeRow 2 3,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g30Cuts (k i : Nat) : Rule false g30T k := (cutRule k g30s0 [])

theorem bound30 : Lower false (raw 4) g30T 5 := finishBound g30Ok ((g30Cuts 4 0).property (raw 4) (by decide +kernel) (by decide +kernel))

def g31T : Sig := 0xffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8

def g31H : List Nat := [2,1,1,0]

theorem g31Ok : basicCheck 4 g31T g31H=true := by decide +kernel

theorem g31s0 : Slice false (raw 4) g31T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 3 :=
  slice_correct (ms:=[setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

def g31Cuts (k i : Nat) : Rule false g31T k := (cutRule k g31s0 [])

theorem bound31 : Lower false (raw 4) g31T 4 := finishBound g31Ok ((g31Cuts 3 0).property (raw 4) (by decide +kernel) (by decide +kernel))

def g32T : Sig := 0xffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8

def g32H : List Nat := [2,1,1,0]

theorem g32Ok : basicCheck 4 g32T g32H=true := by decide +kernel

theorem g32s0 : Slice false (raw 4) g32T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 4 :=
  slice_correct (ms:=[setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g32Cuts (k i : Nat) : Rule false g32T k := (cutRule k g32s0 [])

theorem bound32 : Lower false (raw 4) g32T 5 := finishBound g32Ok ((g32Cuts 4 0).property (raw 4) (by decide +kernel) (by decide +kernel))

def g33T : Sig := 0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8

def g33H : List Nat := [2,1,1,1]

theorem g33Ok : basicCheck 4 g33T g33H=true := by decide +kernel

theorem g33s0 : Slice false (raw 4) g33T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 3 :=
  slice_correct (ms:=[setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

def g33Cuts (k i : Nat) : Rule false g33T k := (cutRule k g33s0 [])

theorem bound33 : Lower false (raw 4) g33T 4 := finishBound g33Ok ((g33Cuts 3 0).property (raw 4) (by decide +kernel) (by decide +kernel))

def g34T : Sig := 0xffffffffffffeae8ffffeae8ffe8eae8ffffffffffffeae8ffffeae8ffe8eae8

def g34H : List Nat := [2,1,1,1,8,16,16]

theorem g34Ok : basicCheck 7 g34T g34H=true := by decide +kernel

def g34v0 : Sig := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000

def g34v1 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g34v2 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g34v3 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee

def g34v4 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g34v5 : Sig := 0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa

def g34v6 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g34v7 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g34v8 : Sig := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa

def g34v9 : Sig := 0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc

def g34v10 : Sig := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0

def g34v11 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000

def g34v12 : Sig := 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa

def g34v13 : Sig := 0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc

def g34v14 : Sig := 0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0

def g34v15 : Sig := 0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000

def g34v16 : Sig := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000

def g34v17 : Sig := 0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa

def g34v18 : Sig := 0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc

def g34v19 : Sig := 0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0

def g34v20 : Sig := 0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000

theorem g34s0 : Slice false (raw 7) g34T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 8 :=
  slice_correct (ms:=[exchangeRow 5 6,exchangeRow 4 5,exchangeRow 3 4,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g20Ok).1 bound20

theorem g34s1 : Slice false (raw 7) g34T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 9 :=
  slice_correct (ms:=[exchangeRow 5 6,exchangeRow 4 5,exchangeRow 3 4,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g22Ok).1 bound22

theorem g34s2 : Slice false (raw 7) g34T 0x303030303030303030303030303030303030303030303030303030303030303 7 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 5,exchangeRow 2 4,exchangeRow 1 3,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g24Ok).1 bound24

theorem g34s3 : Slice false (raw 7) g34T 0xffffffff000000000000000000000000ffffffff 7 :=
  slice_correct (ms:=[setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g26Ok).1 bound26

theorem g34s4 : Slice false (raw 7) g34T 0x101010101010101010101010101010101010101010101010101010101010101 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g27Ok).1 bound27

theorem g34s5 : Slice false (raw 7) g34T 0x101010101010101010101010101010101010101010101010101010101010101 5 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g28Ok).1 bound28

theorem g34s6 : Slice false (raw 7) g34T 0x1010101010101010101010101010101010101010101010101010101010101010 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g27Ok).1 bound27

theorem g34s7 : Slice false (raw 7) g34T 0x1010101010101010101010101010101010101010101010101010101010101010 5 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g28Ok).1 bound28

theorem g34s8 : Slice false (raw 7) g34T 0x404040404040404040404040404040404040404040404040404040404040404 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 true,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g27Ok).1 bound27

theorem g34s9 : Slice false (raw 7) g34T 0x404040404040404040404040404040404040404040404040404040404040404 5 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 true,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g28Ok).1 bound28

theorem g34s10 : Slice false (raw 7) g34T 0x202020202020202020202020202020202020202020202020202020202020202 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 true,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g29Ok).1 bound29

theorem g34s11 : Slice false (raw 7) g34T 0x202020202020202020202020202020202020202020202020202020202020202 5 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 true,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g34s12 : Slice false (raw 7) g34T 0x44004400440044004400440044004400440044004400440044004400440044 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g29Ok).1 bound29

theorem g34s13 : Slice false (raw 7) g34T 0x44004400440044004400440044004400440044004400440044004400440044 5 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g34s14 : Slice false (raw 7) g34T 0x22002200220022002200220022002200220022002200220022002200220022 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g29Ok).1 bound29

theorem g34s15 : Slice false (raw 7) g34T 0x22002200220022002200220022002200220022002200220022002200220022 5 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g34s16 : Slice false (raw 7) g34T 0x50005000500050005000500050005000500050005000500050005000500050 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 true,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g29Ok).1 bound29

theorem g34s17 : Slice false (raw 7) g34T 0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 1,setBitRow 0 true,setBitRow 2 false,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g29Ok).1 bound29

theorem g34s18 : Slice false (raw 7) g34T 0x30003000300030003000300030003000300030003000300030003000300030 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,setBitRow 1 false,setBitRow 2 true,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g29Ok).1 bound29

theorem g34s19 : Slice false (raw 7) g34T 0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,setBitRow 1 true,setBitRow 2 false,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g29Ok).1 bound29

theorem g34s20 : Slice false (raw 7) g34T 0xff00000000000000ff00000000000000ff00000000000000ff00000000 4 :=
  slice_correct (ms:=[exchangeRow 3 6,setBitRow 3 false,setBitRow 4 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g31Ok).1 bound31

theorem g34s21 : Slice false (raw 7) g34T 0xff00000000000000ff00000000000000ff00000000000000ff00000000 5 :=
  slice_correct (ms:=[exchangeRow 3 6,setBitRow 3 false,setBitRow 4 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g34s22 : Slice false (raw 7) g34T 0xff00000000000000ff00000000000000ff00000000000000ff0000 4 :=
  slice_correct (ms:=[exchangeRow 3 6,setBitRow 3 false,setBitRow 4 true,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g31Ok).1 bound31

theorem g34s23 : Slice false (raw 7) g34T 0xff00000000000000ff00000000000000ff00000000000000ff0000 5 :=
  slice_correct (ms:=[exchangeRow 3 6,setBitRow 3 false,setBitRow 4 true,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g34s24 : Slice false (raw 7) g34T 0xff000000ff0000000000000000000000ff000000ff0000000000000000 4 :=
  slice_correct (ms:=[exchangeRow 3 5,setBitRow 3 false,setBitRow 4 false,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g31Ok).1 bound31

theorem g34s25 : Slice false (raw 7) g34T 0xff000000ff0000000000000000000000ff000000ff0000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 3 5,setBitRow 3 false,setBitRow 4 false,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g34s26 : Slice false (raw 7) g34T 0xff000000ff0000000000000000000000ff000000ff0000 4 :=
  slice_correct (ms:=[exchangeRow 3 5,setBitRow 3 false,setBitRow 4 true,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g31Ok).1 bound31

theorem g34s27 : Slice false (raw 7) g34T 0xff000000ff0000000000000000000000ff000000ff0000 5 :=
  slice_correct (ms:=[exchangeRow 3 5,setBitRow 3 false,setBitRow 4 true,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g34s28 : Slice false (raw 7) g34T 0xff00ff00000000000000000000000000ff00ff0000000000000000 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g31Ok).1 bound31

theorem g34s29 : Slice false (raw 7) g34T 0xff00ff00000000000000000000000000ff00ff00000000 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g31Ok).1 bound31

theorem g34s30 : Slice false (raw 7) g34T 0xffff0000000000000000000000000000ffff0000000000000000 4 :=
  slice_correct (ms:=[setBitRow 4 false,setBitRow 5 false,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g33Ok).1 bound33

theorem g34s31 : Slice false (raw 7) g34T 0xffff0000000000000000000000000000ffff00000000 4 :=
  slice_correct (ms:=[setBitRow 4 false,setBitRow 5 true,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g33Ok).1 bound33

theorem g34s32 : Slice false (raw 7) g34T 0xffff0000000000000000000000000000ffff0000 4 :=
  slice_correct (ms:=[setBitRow 4 true,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g31Ok).1 bound31

theorem g34s33 : Slice false (raw 7) g34T 0x11001100110011001100110011001100110011001100110011001100110011 4 :=
  slice_correct (ms:=[exchangeRow 2 6,exchangeRow 1 5,exchangeRow 0 4,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g34s34 : Slice false (raw 7) g34T 0x5000500050005000500050005000500050005000500050005000500050005 4 :=
  slice_correct (ms:=[exchangeRow 2 6,exchangeRow 1 5,exchangeRow 0 4,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g34s35 : Slice false (raw 7) g34T 0x3030303000000000303030300000000030303030000000003030303 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,setBitRow 1 false,setBitRow 2 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g23Ok).1 bound23

theorem g34s36 : Slice false (raw 7) g34T 0x30303030303030300000000000000000303030303030303 4 :=
  slice_correct (ms:=[exchangeRow 3 5,exchangeRow 2 4,exchangeRow 1 3,setBitRow 1 false,setBitRow 2 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g23Ok).1 bound23

theorem g34s37 : Slice false (raw 7) g34T 0xff00000000000000ff00000000000000ff00000000000000ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g34s38 : Slice false (raw 7) g34T 0xff000000ff0000000000000000000000ff000000ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g34Cuts (k i : Nat) : Rule false g34T k := (if i<21 then (if i<10 then (if i<5 then (if i<2 then (if i<1 then (cutRule k g34s0 []) else (cutRule k g34s1 [])) else (if i<3 then (cutRule k g34s2 []) else (if i<4 then (cutRule k g34s2 [(1,g34v7,g34v11)]) else (cutRule k g34s2 [(1,g34v7,g34v16)])))) else (if i<7 then (if i<6 then (cutRule k g34s3 []) else (cutRule k g34s3 [(1,g34v1,g34v2)])) else (if i<8 then (cutRule k g34s3 [(1,g34v1,g34v4)]) else (if i<9 then (cutRule k g34s4 []) else (cutRule k g34s5 []))))) else (if i<15 then (if i<12 then (if i<11 then (cutRule k g34s6 []) else (cutRule k g34s7 [])) else (if i<13 then (cutRule k g34s8 []) else (if i<14 then (cutRule k g34s9 []) else (cutRule k g34s10 [])))) else (if i<18 then (if i<16 then (cutRule k g34s11 []) else (if i<17 then (cutRule k g34s12 []) else (cutRule k g34s13 []))) else (if i<19 then (cutRule k g34s14 []) else (if i<20 then (cutRule k g34s15 []) else (cutRule k g34s16 [])))))) else (if i<32 then (if i<26 then (if i<23 then (if i<22 then (cutRule k g34s17 []) else (cutRule k g34s18 [])) else (if i<24 then (cutRule k g34s19 []) else (if i<25 then (cutRule k g34s20 []) else (cutRule k g34s21 [])))) else (if i<29 then (if i<27 then (cutRule k g34s22 []) else (if i<28 then (cutRule k g34s23 []) else (cutRule k g34s24 []))) else (if i<30 then (cutRule k g34s25 []) else (if i<31 then (cutRule k g34s26 []) else (cutRule k g34s27 []))))) else (if i<37 then (if i<34 then (if i<33 then (cutRule k g34s28 []) else (cutRule k g34s29 [])) else (if i<35 then (cutRule k g34s30 []) else (if i<36 then (cutRule k g34s31 []) else (cutRule k g34s32 [])))) else (if i<40 then (if i<38 then (cutRule k g34s33 []) else (if i<39 then (cutRule k g34s34 []) else (cutRule k g34s35 []))) else (if i<41 then (cutRule k g34s36 []) else (if i<42 then (cutRule k g34s37 []) else (cutRule k g34s38 [])))))))

def g34n0w : List Sig := [g34v1,g34v2,g34v3,g34v4,g34v6,g34v7,g34v11,g34v15,g34v16]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n0 : Impossible false g34T 8 g34n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 7) (fun i => failRule false g34T 7))) (idx:=(fun j => bitsAt 0x100254003100064000c6021140443011060a81812060440941024a8092102444062a01848054101484051100d28034100ca8032100c480311 18 (bitsAt 0x1300016000000000000014000120000000000000130001100000000000000e0000b00000000000000800006000000000000013000130000000000000040000000000000000000500001000000000000000000000000000000000000000000000000000000b0000b000000000000006000060000000000000170001800000000000000000000000000000000001000010000000000000000001100000000000000c0000b0000000000000070000600000000000001200012000000000000002000000000000000000030000100000000000000b0000b0000000000000060000600000000000001100011000000000000000000000000000000000010000100000000000000a0000600000000000000b0000f000000000000010000000000000000000030000100000000000000600015000000000000009000000000000000000060000100000000000000000000000000000000000000000000000000000000000d 5 j))) (by decide +kernel)

def g34n1w : List Sig := [g34v1,g34v2,g34v3,g34v4,g34v6,g34v7,g34v11,g34v16,g34v20]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n1 : Impossible false g34T 8 g34n1w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 7) (fun i => failRule false g34T 7))) (idx:=(fun j => bitsAt 0x10025400310006400106041140443011061281812060440941024a8092102444062a01848054101484051100d28034100ca8032100c480311 18 (bitsAt 0x12000160000000000000000000000000000000000b0000b00000000000000600006000000000000017000180000000000000000000000000000000000100001000000000000014000120000000000000000001100000000000000e0000b000000000000008000060000000000000130001300000000000000400000000000000000005000010000000000000120001100000000000000c0000b0000000000000070000600000000000001200012000000000000002000000000000000000030000100000000000000b0000b0000000000000060000600000000000001100011000000000000000000000000000000000010000100000000000000a0000600000000000000b0000f000000000000010000000000000000000030000100000000000000600015000000000000009000000000000000000060000100000000000000000000000000000000000000000000000000000000000d 5 j))) (by decide +kernel)

def g34n2w : List Sig := [g34v1,g34v2,g34v4,g34v5,g34v6,g34v7,g34v11,g34v15,g34v16]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n2 : Impossible false g34T 8 g34n2w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 7) (fun i => failRule false g34T 7))) (idx:=(fun j => bitsAt 0x40099000a4001d00031808450110c044182c060a81814060440941024b0092102444062c01850054c01504052c01484051401444034100c840311 18 (bitsAt 0x1400017000000000000015000130000000000000140001100000000000000e0000b00000000000001400014000000000000007000030000000000000020000000000000000000800004000000000000000000000000000000000000000000000000000000b0000b000000000000018000190000000000000030000300000000000000000000000000000000004000040000000000000000001100000000000000c0000b0000000000000130001300000000000000500003000000000000001000000000000000000060000400000000000000b0000b0000000000000120001100000000000000300003000000000000000000000000000000000040000400000000000000b0000f0000000000000100000300000000000000a0000000000000000000600004000000000000000000000000000000000000001600000000000000000000000000000000009000000000000000000000000d00000000000000000004 5 j))) (by decide +kernel)

def g34n3w : List Sig := [g34v1,g34v2,g34v4,g34v5,g34v6,g34v7,g34v11,g34v16,g34v20]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n3 : Impossible false g34T 8 g34n3w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 7) (fun i => failRule false g34T 7))) (idx:=(fun j => bitsAt 0x40099000a4001d00041810450110c044184c061281814060440941024b0092102444062c01850054c01504052c01484051401444034100c840311 18 (bitsAt 0x13000170000000000000000000000000000000000b0000b00000000000001800019000000000000003000030000000000000000000000000000000000400004000000000000015000130000000000000000001100000000000000e0000b000000000000014000140000000000000070000300000000000000200000000000000000008000040000000000000130001100000000000000c0000b0000000000000130001300000000000000500003000000000000001000000000000000000060000400000000000000b0000b0000000000000120001100000000000000300003000000000000000000000000000000000040000400000000000000b0000f0000000000000100000300000000000000a0000000000000000000600004000000000000000000000000000000000000001600000000000000000000000000000000009000000000000000000000000d00000000000000000004 5 j))) (by decide +kernel)

def g34n4w : List Sig := [g34v1,g34v2,g34v3,g34v4,g34v6,g34v7,g34v11,g34v16]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n4 : Impossible false g34T 9 g34n4w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => (if i<1 then (linkRule g34n0w g34n0) else (linkRule g34n1w g34n1))))) (idx:=(fun j => bitsAt 0x80006000040095001140039000d40031000a400250008400190002181286041180a860211405050121404430210c05030120c044184a060b0182a060501812060440941024a8092102444062a01848054101484051100d28034100ca8032100c480311 18 (bitsAt 0x85c79c859555000000000000ad951485c492000000000000a1d38ea592cb00000000000091b208899186000000000000959999a598d900000000000095a104a590000000000000009d9145a59041000000000000a9549285e492000000000000a1f30ca552cb0000000000009171c7895186000000000000955995a558d5000000000000956082a550000000000000009d50c3a55041000000000000a122cba582cb000000000000913186892186000000000000952992a528d2000000000000952000a520000000000000009d8041a5204100000000000091128aa4b186000000000000a4b98ba4f8cf000000000000a50990a4b000000000000000a4b0c3a4f0410000000000008868c6a698e00000000000008898c9a460000000000000008868c6a49041000000000000000000000000000000000000000000000000000000000000000000a6334d 6 j))) (by decide +kernel)

def g34n5w : List Sig := [g34v1,g34v2,g34v4,g34v5,g34v6,g34v7,g34v11,g34v16]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n5 : Impossible false g34T 9 g34n5w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => (if i<1 then (linkRule g34n2w g34n2) else (linkRule g34n3w g34n3))))) (idx:=(fun j => bitsAt 0x80006000040099001340039000c4002d000a4002500084001d0002181286041180a860211405050121404430210c05030120c044184a060b0182a060501812060440941024b0092102444062c01850054c01504052c01484051401444034100c840311 18 (bitsAt 0x85c79c859555000000000000ad951485c492000000000000a1d38ea592cb000000000000919959a598d900000000000091b1c7a590c300000000000099a0828990000000000000009d9208a59104000000000000a9549285e492000000000000a1f30ca552cb000000000000915955a558d5000000000000917145a550c30000000000009960418950000000000000009d5186a55104000000000000a122cba582cb000000000000913953a528d20000000000009130c3a520c30000000000009920008920000000000000009d8104a52104000000000000a4b94ba4f8cf000000000000a51951a4b0c300000000000099028aa4b000000000000000a4b186a4f1040000000000000000000000000000000000008a3000a63a600000000000000000000000000000000000008a3249a43000000000000000000000a6334d0000000000008808c0a49104 6 j))) (by decide +kernel)

def g34n6w : List Sig := [g34v0,g34v1,g34v2,g34v4,g34v6,g34v7,g34v11,g34v16]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n6 : Impossible false g34T 9 g34n6w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => failRule false g34T 8))) (idx:=(fun j => bitsAt 0x1002a400a5002640095001d40071001940061001140031000a400250008181286041180a860211405050121404430210c05030120c044184a060b0182a060501812060440941024840911018b0062a01850061201504052101450051100d28034100ca8032100c480311 18 (bitsAt 0x9de81eb5b5d7000000000000b9b596b5e514000000000000b9f410adb38e00000000000091d249b1b18600000000000095c104adb000000000000000a5b145adb041000000000000b9ba9badb8db000000000000b57514b60514000000000000b613cfad738e000000000000919208b17186000000000000958082ad70000000000000009d70c3ad7041000000000000b57a17ad78d7000000000000b5438eada38e000000000000915186b14186000000000000954000ad40000000000000008da041000000000000000000000000000000000000000000b1330cace186000000000000ad234dace000000000000000ace0c3ad1041000000000000ace98eace8ce00000000000088a2caac6000000000000000b061c6aca041000000000000b068c6ac68c6000000000000ac0040acb1c7000000000000ac08c0ac08c0000000000000000000000000 6 j))) (by decide +kernel)

def g34n7w : List Sig := [g34v1,g34v2,g34v4,g34v6,g34v7,g34v8,g34v11,g34v16]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n7 : Impossible false g34T 9 g34n7w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => failRule false g34T 8))) (idx:=(fun j => bitsAt 0x100244007d001e4006d001a4005500134004900114003d000e40035000b400250000181286041180a860211410450141404850110c08430140c0483011060501812060440941024840911018b0062a01850061201504052101450051100d04032100c480311 18 (bitsAt 0xb1a71aa164920000000000008968d6a9aada000000000000a16656a9a555000000000000a9b38e95630c0000000000008181c78961040000000000008570c38960000000000000008968d6a960410000000000008928d2a1ca5c000000000000a12552a1c659000000000000a1d34d95230c0000000000008141868921040000000000008530828920000000000000008928d2a120410000000000000000000000000000000000008a330c9648de0000000000008a010489f2080000000000008a100089f249000000000000000000000000000000000000a2630c95530c000000000000a20104895104000000000000a210008950000000000000000000007d50410000000000009d128a88c1040000000000009502cb88c00000000000000088c8cc94f041000000000000888248884000000000000000884144888041000000000000880040889145 6 j))) (by decide +kernel)

def g34n8w : List Sig := [g34v1,g34v2,g34v4,g34v6,g34v7,g34v11,g34v12,g34v16]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n8 : Impossible false g34T 9 g34n8w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => failRule false g34T 8))) (idx:=(fun j => bitsAt 0x1002340085001f4006500184005500134004900114003d000e40035000b400246041180a860211405050121404430210c044184a060b0182a060501812060440941024840911018b0062a01850061201504052c01484051100d04032a00c840311 18 (bitsAt 0x817857a57a1700000000000099a71aa57555000000000000a9751499a492000000000000a5b38e8d730c0000000000007991c78171040000000000007d80c3817000000000000000817857a570820000000000000000000000000000000000008214929a749200000000000082130c8e23cf00000000000081e10481d20800000000000081f00081d24900000000000000000000000000000000000099549299c4920000000000009a434d8d530c00000000000099e14581510400000000000099f04181500000000000000000000075508200000000000099230c8d630c0000000000007931048121040000000000007d200081200000000000000081685699208200000000000095128a80c1040000000000008d02cb80c00000000000000080c0828cf082000000000000808248804000000000000000804184808082000000000000800080809186 6 j))) (by decide +kernel)

def g34n9w : List Sig := [g34v1,g34v2,g34v4,g34v6,g34v7,g34v11,g34v16,g34v17]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n9 : Impossible false g34T 9 g34n9w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => failRule false g34T 8))) (idx:=(fun j => bitsAt 0x1002240081001c4006d00194005500134004900114003d000e40035000b40024604a1810460211404430210c05030120c044184a060b0182a060501812060440941024840911018b0062a01850061201530054101484051100d28034100c840311 18 (bitsAt 0x821555a67555000000000000821514a2649200000000000082130c8e23cf00000000000081e10481d20800000000000081f00081d249000000000000000000000000000000000000a1a6daa59555000000000000a19514a1a492000000000000a2438e8d930c000000000000a1e186819104000000000000a1f0828190000000000000000000007590c3000000000000a95492a1b492000000000000a5c34d8d530c0000000000007971458151040000000000007d6041815000000000000000815855a550c3000000000000a1230c8d830c0000000000007931048121040000000000007d2000812000000000000000818858a120c300000000000095128a80c1040000000000008d02cb80c00000000000000080c0c38cf0c30000000000008082488040000000000000008041c48080c30000000000008000c08091c7 6 j))) (by decide +kernel)

def g34n10w : List Sig := [g34v1,g34v2,g34v4,g34v6,g34v7,g34v9,g34v11,g34v16]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n10 : Impossible false g34T 9 g34n10w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => failRule false g34T 8))) (idx:=(fun j => bitsAt 0x40091001f40079001b40069001740045001040035000c4002d0009181286041180a8602114050501214044302a0c05030120c044184a060a8181406048181102504092102444062a01850061201504052101450051100d28032a00c480311 18 (bitsAt 0xa5a71a9574d30000000000008178579daa1a0000000000009574929da4510000000000009db34d8972cb0000000000007d91c78171040000000000008188589d70000000000000008570c381704100000000000081385395c99c00000000000095345195c45100000000000095d30c8932cb0000000000007d51868131040000000000008148549530000000000000008530828130410000000000000000000000000000000000008212cb8a32cb00000000000081f10481e10400000000000000000000000000000000000082104181e1450000000000009512cb8962cb00000000000095f10481110400000000000000000079100000000000000096104181104100000000000091028a80b10400000000000080f84f88b00000000000000088b08280e041000000000000808248804000000000000000804144808041000000000000800040809145 6 j))) (by decide +kernel)

def g34n11w : List Sig := [g34v1,g34v2,g34v4,g34v6,g34v7,g34v11,g34v13,g34v16]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n11 : Impossible false g34T 9 g34n11w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => failRule false g34T 8))) (idx:=(fun j => bitsAt 0x100274008d00214007d001940061001740045001040035000c4002d000918128602a1808450141404850110c084301206128182c060a8181406048181102504092102444062c018a8061201504052101450051100d28032a00c840312 18 (bitsAt 0x7977d79969560000000000008d96d99965140000000000009d64d38d945100000000000099a34d8162cb0000000000007581c77961040000000000007977d79960410000000000007d60c379600000000000000000000000000000000000000079f4518e445100000000000079f30c8212cb00000000000079d18679c10400000000000000000000000000000000000079f00079c1450000000000008d44518db4510000000000008db30c8142cb0000000000008dd186794104000000000000000000a140410000000000008df0827940000000000000008d12cb8152cb0000000000007521047911040000000000007917d18d10410000000000007d500079100000000000000089024978b10400000000000078f28a80b04100000000000080b08278e00000000000000078828878404100000000000078414478800000000000000078100078a145 6 j))) (by decide +kernel)

def g34n12w : List Sig := [g34v1,g34v2,g34v4,g34v6,g34v7,g34v11,g34v16,g34v18]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n12 : Impossible false g34T 9 g34n12w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => failRule false g34T 8))) (idx:=(fun j => bitsAt 0x1002840089002040071001b40065001740045001040035000c4002d0009181286041180a850120c08430140c048301106128182c060a8181406048181102504092102444064c018a8061201504052101450051100d28034100ca80312 18 (bitsAt 0x79f5559a451400000000000079f45196345100000000000079f34d8212cb00000000000079d1c779c10400000000000000000000000000000000000079f00079c1450000000000009596999985140000000000009584d395945100000000000095934d8182cb00000000000095d1c7798104000000000000000000a1808200000000000095f0c37980000000000000009d445195a45100000000000099b30c8142cb0000000000007561867941040000000000007957d59940820000000000007d40417940000000000000009512cb8172cb0000000000007521047911040000000000007917d19510820000000000007d700079100000000000000089024978b10400000000000078f28a80b08200000000000080b04178e00000000000000078828878408200000000000078414478800000000000000078200078a145 6 j))) (by decide +kernel)

def g34n13w : List Sig := [g34v1,g34v2,g34v4,g34v6,g34v7,g34v10,g34v11,g34v16]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n13 : Impossible false g34T 9 g34n13w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => failRule false g34T 8))) (idx:=(fun j => bitsAt 0x100244007d001e4006d001a40059001440045000b400290009181286041180a8602114050501214044302c0c05030120c044184c060b0181406048181102504092102444062c01850061201450051100d28034100ca8032100c480311 18 (bitsAt 0xa1a71a9174d30000000000007d781799a9da00000000000091749299a45100000000000099b34d8972cb0000000000007d98199971860000000000008181047d70000000000000008171457d70410000000000007d381391c95c00000000000091345191c45100000000000091d30c8932cb0000000000007d58159131860000000000008140827d30000000000000008130c37d30410000000000000000000000000000000000007e02cb8a12cb0000000000000000000000000000000000007e00007de0000000000000007e00417de0410000000000009112cb8962cb0000000000000000007911860000000000009200007d10000000000000009200417d10410000000000007d081088b1860000000000008cf28a7cb00000000000000088b0c37ce0410000000000007c82487c60000000000000007c61c67c80410000000000007c00407c91c7 6 j))) (by decide +kernel)

def g34n14w : List Sig := [g34v1,g34v2,g34v4,g34v6,g34v7,g34v11,g34v14,g34v16]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n14 : Impossible false g34T 9 g34n14w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => failRule false g34T 8))) (idx:=(fun j => bitsAt 0x4009d002340085001f40065001840059001440045000b40029000918130602a1808450141404850110c084301406128182c060a8181406048181102504092102444062c018a8061401484051400d28034100ca8032100c480311 18 (bitsAt 0x7587989569160000000000008996d99565140000000000009964d389945100000000000095a34d8162cb0000000000007587989561c700000000000079710475600000000000000079614575604100000000000000000000000000000000000075e4518a345100000000000075e30c81f2cb00000000000000000000000000000000000075e08275c00000000000000075e0c375c04100000000000089445189b45100000000000089b30c8142cb0000000000000000009d41c700000000000089e08275400000000000000089e0c37540410000000000008912cb8152cb0000000000007527928911c700000000000079100075100000000000000079504175104100000000000075024980b1c700000000000084f28a74b00000000000000080b0c374e041000000000000749208747000000000000000747186749041000000000000740040748186 6 j))) (by decide +kernel)

def g34n15w : List Sig := [g34v1,g34v2,g34v4,g34v6,g34v7,g34v11,g34v16,g34v19]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n15 : Impossible false g34T 9 g34n15w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => failRule false g34T 8))) (idx:=(fun j => bitsAt 0x400a1002240081001c4006d001940059001440045000b400290009181286041180b050140c08430140c048301106128182c060a8181406048181102504092102444064a018b0061401504051400d28034100ca8032100c480311 18 (bitsAt 0x75e59696351400000000000075e49292245100000000000075e34d81f2cb00000000000000000000000000000000000075e10475c00000000000000075e14575c0410000000000009196999585140000000000009184d391945100000000000091934d8182cb0000000000000000009d81c700000000000091e10475800000000000000091e14575804100000000000099445191a45100000000000095b30c8142cb0000000000007567969541c70000000000007950827540000000000000007940c37540410000000000009112cb8172cb0000000000007527929111c700000000000079100075100000000000000079704175104100000000000075028a80b1c700000000000084f24974b00000000000000080b0c374e04100000000000074a20874700000000000000074718674a041000000000000740040748186 6 j))) (by decide +kernel)

def g34n16w : List Sig := [g34v1,g34v2,g34v4,g34v6,g34v7,g34v11,g34v15,g34v16]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n16 : Impossible false g34T 9 g34n16w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => (if i<1 then (linkRule g34n0w g34n0) else (linkRule g34n2w g34n2))))) (idx:=(fun j => bitsAt 0x800060000400a500224007d001e4006d001a40065001840045000f40035000b4002500054000c602a1808450141404850110c08430140c0483011060b0182a060501812060440941024840911018b0062a01850061201504052101450051100d28034100ca8032100c480311 18 (bitsAt 0x99a9dab6dae000000000000099d9ddb5a596000000000000a1aa5ab5d514000000000000a9e410b5a38e000000000000b1c249a9a186000000000000b1b104a9a000000000000000b1a145a9a041000000000000000000000000000000000000000000000000000000000000b6738eb6538e0000000000009a2186b611860000000000009a3000b610000000000000009a4041b61041000000000000000000b67514000000000000b673cfb5638e000000000000998208b56186000000000000997082b560000000000000009960c3b56041000000000000b5438eb5938e000000000000a15186b54186000000000000a14000b54000000000000000a19041b540410000000000009d330cb4e1860000000000009d234db4e0000000000000009ce0c3b510410000000000007ca2ca7c6000000000000000bc61c67ca041000000000000b800407cb1c7 6 j))) (by decide +kernel)

def g34n17w : List Sig := [g34v1,g34v2,g34v4,g34v6,g34v7,g34v11,g34v16,g34v20]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n17 : Impossible false g34T 9 g34n17w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 8) (fun i => (if i<1 then (linkRule g34n1w g34n1) else (linkRule g34n3w g34n3))))) (idx:=(fun j => bitsAt 0x800060000400a9002340071001b40069001940045000f40035000b40025000540010604a1810450411405050121404430140c048301106130184a060501812060440941024840911018b0062a01850061201504052101450051100d28034100ca8032100c480311 18 (bitsAt 0x9e6596ae8ae0000000000000000000000000000000000000ae838eae538e0000000000009e2186ae11860000000000009e3000ae10000000000000009e4041ae1041000000000000a6675dad9596000000000000000000ae6514000000000000ae8410ad938e000000000000a5b249ad9186000000000000a5a104ad9000000000000000a59145ad90410000000000009d6a16add5140000000000009de3cfad638e000000000000a982089d6186000000000000a970829d6000000000000000a960c39d6041000000000000ad438eadc38e0000000000009d5186ad41860000000000009d4000ad40000000000000009dc041ad4041000000000000a1330cace186000000000000a1234dace000000000000000a0e0c3ad10410000000000007ca2ca7c6000000000000000b461c67ca041000000000000b000407cb1c7 6 j))) (by decide +kernel)

def g34n18w : List Sig := [g34v1,g34v2,g34v4,g34v6,g34v7,g34v11,g34v16]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g34n18 : Impossible false g34T 10 g34n18w.toFinset :=
  checkNode_sound (rules:=(codedRule (g34Cuts 9) (fun i => (if i<7 then (if i<3 then (if i<1 then (linkRule g34n4w g34n4) else (if i<2 then (linkRule g34n5w g34n5) else (linkRule g34n6w g34n6))) else (if i<5 then (if i<4 then (linkRule g34n7w g34n7) else (linkRule g34n8w g34n8)) else (if i<6 then (linkRule g34n9w g34n9) else (linkRule g34n10w g34n10)))) else (if i<10 then (if i<8 then (linkRule g34n11w g34n11) else (if i<9 then (linkRule g34n12w g34n12) else (linkRule g34n13w g34n13))) else (if i<12 then (if i<11 then (linkRule g34n14w g34n14) else (linkRule g34n15w g34n15)) else (if i<13 then (linkRule g34n16w g34n16) else (linkRule g34n17w g34n17)))))))) (idx:=(fun j => bitsAt 0x80036000c8002e000a8002600088001e00068001600048000e0002800060000400150002400050000181286041180a860211405050121404430210c05030120c044184a060b0182a060501812060440941024840911018b0062a01850061201504052101450051100d28034100ca8032100c480311 18 (bitsAt 0x95e81e95b5d7000000000000cdb59695e5140000000000008df41095b38e000000000000c5d24991b186000000000000b9c10491b000000000000000adb14595b041000000000000c975149605140000000000008e13cf95738e000000000000c19208917186000000000000b58082917000000000000000a970c39570410000000000008d438e89a38e000000000000bd5186914186000000000000b14000914000000000000000a5a041a140410000000000008d330c90e1860000000000008d234d90e0000000000000008ce0c389104100000000000090a2ca9060000000000000009c61c690a04100000000000098004090b1c7 6 j))) (by decide +kernel)

theorem bound34 : Lower false (raw 7) g34T 11 := finishBound g34Ok g34n18

def g35T : Sig := 0xeca8eca8eca8eca8eca8eca8eca8eca8eca8eca8eca8eca8eca8eca8eca8eca8

def g35H : List Nat := [2,1,1,2]

theorem g35Ok : basicCheck 4 g35T g35H=true := by decide +kernel

def g35v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g35v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g35v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g35v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g35Cuts (k i : Nat) : Rule false g35T k := failRule false g35T k

def g35n0w : List Sig := [g35v0,g35v1,g35v2,g35v3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g35n0 : Impossible false g35T 3 g35n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g35Cuts 2) (fun i => failRule false g35T 2))) (idx:=(fun j => bitsAt 0x2830050c01424050600c240306 18 (bitsAt 0x3003000000001001000000004000000000005001000000000000000000000002 3 j))) (by decide +kernel)

theorem bound35 : Lower false (raw 4) g35T 4 := finishBound g35Ok g35n0

def g36T : Sig := 0xffececa8ffececa8ffececa8ffececa8ffececa8ffececa8ffececa8ffececa8

def g36H : List Nat := [2,1,1,2,2]

theorem g36Ok : basicCheck 5 g36T g36H=true := by decide +kernel

def g36v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g36v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g36v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g36v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g36v4 : Sig := 0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc

def g36v5 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g36v6 : Sig := 0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc

def g36v7 : Sig := 0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00

theorem g36s0 : Slice false (raw 5) g36T 0x5555555555555555555555555555555555555555555555555555555555555555 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g36s1 : Slice false (raw 5) g36T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g35Ok).1 bound35

theorem g36s2 : Slice false (raw 5) g36T 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff 4 :=
  slice_correct (ms:=[setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g35Ok).1 bound35

theorem g36s3 : Slice false (raw 5) g36T 0x505050505050505050505050505050505050505050505050505050505050505 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

theorem g36s4 : Slice false (raw 5) g36T 0x505050505050505050505050505050505050505050505050505050505050505 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g36s5 : Slice false (raw 5) g36T 0x5050505050505050505050505050505050505050505050505050505050505050 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

theorem g36s6 : Slice false (raw 5) g36T 0x5050505050505050505050505050505050505050505050505050505050505050 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g36Cuts (k i : Nat) : Rule false g36T k := (if i<3 then (if i<1 then (cutRule k g36s0 []) else (if i<2 then (cutRule k g36s1 []) else (cutRule k g36s2 []))) else (if i<5 then (if i<4 then (cutRule k g36s3 []) else (cutRule k g36s4 [])) else (if i<6 then (cutRule k g36s5 []) else (cutRule k g36s6 []))))

def g36n0w : List Sig := [g36v0,g36v1,g36v2,g36v3,g36v4,g36v5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g36n0 : Impossible false g36T 5 g36n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g36Cuts 4) (fun i => failRule false g36T 4))) (idx:=(fun j => bitsAt 0x400081809048180a0c02818051401444050c01424050600c240306 18 (bitsAt 0x9000b00000000000a00070000000000050003000000000009000100000000000600000000000000000000000000000003000300000000000000000000000000000002000000000003000300000000000000010000000000040000000000000008000100000000000000000000000000000002 4 j))) (by decide +kernel)

def g36n1w : List Sig := [g36v0,g36v1,g36v2,g36v3,g36v5,g36v6]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g36n1 : Impossible false g36T 5 g36n1w.toFinset :=
  checkNode_sound (rules:=(codedRule (g36Cuts 4) (fun i => failRule false g36T 4))) (idx:=(fun j => bitsAt 0x1000106044121402818051401444050c01424050600c440306 18 (bitsAt 0x7000a0000000000050003000000000000000000000000000000020000000000090007000000000005000300000000000000010000000000060000000000000003000300000000000700010000000000040000000000000008000100000000000000000000000000000002 4 j))) (by decide +kernel)

def g36n2w : List Sig := [g36v0,g36v1,g36v2,g36v3,g36v5,g36v7]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g36n2 : Impossible false g36T 5 g36n2w.toFinset :=
  checkNode_sound (rules:=(codedRule (g36Cuts 4) (fun i => failRule false g36T 4))) (idx:=(fun j => bitsAt 0x400040a0c01450051101430050901418031100c240306 18 (bitsAt 0x40004000000000001000100000000000500000000000000000009000000000006000400000000000200010000000000070000000000000004000400000000000100010000000000050000000000000008000100000000000000000000000000000003 4 j))) (by decide +kernel)

def g36n3w : List Sig := [g36v0,g36v1,g36v2,g36v3,g36v5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g36n3 : Impossible false g36T 6 g36n3w.toFinset :=
  checkNode_sound (rules:=(codedRule (g36Cuts 5) (fun i => (if i<1 then (linkRule g36n0w g36n0) else (if i<2 then (linkRule g36n1w g36n1) else (linkRule g36n2w g36n2)))))) (idx:=(fun j => bitsAt 0x8000a00018000100064001500044000d0002400050000060441809048180a0c028240a0601450051101430050901418031100c240306 18 (bitsAt 0xbb1ac7ad0800000000009acc68ac840000000000b2c42830210000000000930e78ac0000000000009a0848a0840000000000aa0217b4210000000000934a58a00000000000009d14a890210000000000890008b8000000000000904008a463 5 j))) (by decide +kernel)

theorem bound36 : Lower false (raw 5) g36T 7 := finishBound g36Ok g36n3

def g37T : Sig := 0xfff8ffa8f8f8f8a8fff8ffa8f8f8f8a8fff8ffa8f8f8f8a8fff8ffa8f8f8f8a8

def g37H : List Nat := [2,1,1,4,4,8]

theorem g37Ok : basicCheck 6 g37T g37H=true := by decide +kernel

def g37v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g37v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g37v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g37v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g37v4 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g37v5 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000

theorem g37s0 : Slice false (raw 6) g37T 0x5555555555555555555555555555555555555555555555555555555555555555 4 :=
  slice_correct (ms:=[exchangeRow 3 5,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g35Ok).1 bound35

theorem g37s1 : Slice false (raw 6) g37T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g25Ok).1 bound25

theorem g37s2 : Slice false (raw 6) g37T 0x1111111111111111111111111111111111111111111111111111111111111111 4 :=
  slice_correct (ms:=[exchangeRow 3 5,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g35Ok).1 bound35

theorem g37s3 : Slice false (raw 6) g37T 0x4444444444444444444444444444444444444444444444444444444444444444 4 :=
  slice_correct (ms:=[exchangeRow 3 5,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true]) (by decide +kernel) (by decide +kernel) (basic_data g35Ok).1 bound35

theorem g37s4 : Slice false (raw 6) g37T 0x333300003333000033330000333300003333000033330000333300003333 4 :=
  slice_correct (ms:=[exchangeRow 3 5,exchangeRow 2 3,exchangeRow 1 2,setBitRow 1 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g23Ok).1 bound23

theorem g37s5 : Slice false (raw 6) g37T 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g25Ok).1 bound25

theorem g37s6 : Slice false (raw 6) g37T 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g25Ok).1 bound25

def g37Cuts (k i : Nat) : Rule false g37T k := (if i<3 then (if i<1 then (cutRule k g37s0 []) else (if i<2 then (cutRule k g37s1 []) else (cutRule k g37s2 []))) else (if i<5 then (if i<4 then (cutRule k g37s3 []) else (cutRule k g37s4 [])) else (if i<6 then (cutRule k g37s5 []) else (cutRule k g37s6 []))))

def g37n0w : List Sig := [g37v0,g37v1,g37v2,g37v3,g37v4,g37v5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g37n0 : Impossible false g37T 6 g37n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g37Cuts 5) (fun i => failRule false g37T 5))) (idx:=(fun j => bitsAt 0x4001900054001100034000900014000028310a098281a0a0641426030980c1a03064053101498051900cc4032600c680319 18 (bitsAt 0x2d4a02d4a000000000002d29041290000000000054c602c8400000000000306302c00000000000002c4202c210000000000051ce0292900000000000288404c8400000000000280002800000000000004421028210000000000024840348400000000000240002400000000000003821024210000000000022480100000000000000104201c2100000000000002003ca5 5 j))) (by decide +kernel)

theorem bound37 : Lower false (raw 6) g37T 7 := finishBound g37Ok g37n0

def g38T : Sig := 0xfffffffffff8ffa8fff8ffa8f8f8f8a8fffffffffff8ffa8fff8ffa8f8f8f8a8

def g38H : List Nat := [2,1,1,4,4,8,8]

theorem g38Ok : basicCheck 7 g38T g38H=true := by decide +kernel

def g38v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g38v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g38v2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g38v3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g38v4 : Sig := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0

def g38v5 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g38v6 : Sig := 0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00

def g38v7 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000

def g38v8 : Sig := 0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0

def g38v9 : Sig := 0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00

def g38v10 : Sig := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000

def g38v11 : Sig := 0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0

def g38v12 : Sig := 0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00

def g38v13 : Sig := 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000

theorem g38s0 : Slice false (raw 7) g38T 0x5555555555555555555555555555555555555555555555555555555555555555 7 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 5,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g36Ok).1 bound36

theorem g38s1 : Slice false (raw 7) g38T 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff 7 :=
  slice_correct (ms:=[exchangeRow 5 6,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g37Ok).1 bound37

theorem g38s2 : Slice false (raw 7) g38T 0xffffffffffffffff0000000000000000ffffffffffffffff 7 :=
  slice_correct (ms:=[setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g37Ok).1 bound37

theorem g38s3 : Slice false (raw 7) g38T 0x1111111111111111111111111111111111111111111111111111111111111111 7 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 5,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g36Ok).1 bound36

theorem g38s4 : Slice false (raw 7) g38T 0x4444444444444444444444444444444444444444444444444444444444444444 7 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 5,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true]) (by decide +kernel) (by decide +kernel) (basic_data g36Ok).1 bound36

theorem g38s5 : Slice false (raw 7) g38T 0x333300003333000033330000333300003333000033330000333300003333 7 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 5,exchangeRow 2 3,exchangeRow 1 2,setBitRow 1 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g24Ok).1 bound24

theorem g38s6 : Slice false (raw 7) g38T 0x111100001111000011110000111100001111000011110000111100001111 5 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g28Ok).1 bound28

theorem g38s7 : Slice false (raw 7) g38T 0x1111000011110000111100001111000011110000111100001111000011110000 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false,setBitRow 4 true]) (by decide +kernel) (by decide +kernel) (basic_data g29Ok).1 bound29

theorem g38s8 : Slice false (raw 7) g38T 0x1111000011110000111100001111000011110000111100001111000011110000 5 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false,setBitRow 4 true]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g38s9 : Slice false (raw 7) g38T 0x444400004444000044440000444400004444000044440000444400004444 5 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g28Ok).1 bound28

theorem g38s10 : Slice false (raw 7) g38T 0x4444000044440000444400004444000044440000444400004444000044440000 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true,setBitRow 4 true]) (by decide +kernel) (by decide +kernel) (basic_data g29Ok).1 bound29

theorem g38s11 : Slice false (raw 7) g38T 0x4444000044440000444400004444000044440000444400004444000044440000 5 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true,setBitRow 4 true]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g38s12 : Slice false (raw 7) g38T 0x222200002222000022220000222200002222000022220000222200002222 5 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g38s13 : Slice false (raw 7) g38T 0x2222000022220000222200002222000022220000222200002222000022220000 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 4 true]) (by decide +kernel) (by decide +kernel) (basic_data g29Ok).1 bound29

theorem g38s14 : Slice false (raw 7) g38T 0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a 5 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 true,setBitRow 2 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g38s15 : Slice false (raw 7) g38T 0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a0000 5 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 true,setBitRow 2 false,setBitRow 4 true]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g38s16 : Slice false (raw 7) g38T 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g25Ok).1 bound25

theorem g38s17 : Slice false (raw 7) g38T 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g25Ok).1 bound25

theorem g38s18 : Slice false (raw 7) g38T 0x101010101010101010101010101010101010101010101010101010101010101 4 :=
  slice_correct (ms:=[exchangeRow 2 6,exchangeRow 1 5,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g38s19 : Slice false (raw 7) g38T 0x404040404040404040404040404040404040404040404040404040404040404 4 :=
  slice_correct (ms:=[exchangeRow 2 6,exchangeRow 1 5,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 true,setBitRow 2 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g38s20 : Slice false (raw 7) g38T 0x202020202020202020202020202020202020202020202020202020202020202 4 :=
  slice_correct (ms:=[exchangeRow 2 6,exchangeRow 1 5,exchangeRow 0 3,setBitRow 0 true,setBitRow 1 false,setBitRow 2 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g38s21 : Slice false (raw 7) g38T 0x11111111000000001111111100000000111111110000000011111111 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g35Ok).1 bound35

theorem g38s22 : Slice false (raw 7) g38T 0x111111111111111100000000000000001111111111111111 4 :=
  slice_correct (ms:=[exchangeRow 3 5,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g35Ok).1 bound35

theorem g38s23 : Slice false (raw 7) g38T 0x50500000505000005050000050500000505000005050000050500000505 4 :=
  slice_correct (ms:=[exchangeRow 2 6,exchangeRow 1 5,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g38s24 : Slice false (raw 7) g38T 0x505000005050000050500000505000005050000050500000505000005050000 4 :=
  slice_correct (ms:=[exchangeRow 2 6,exchangeRow 1 5,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false,setBitRow 4 true]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g38s25 : Slice false (raw 7) g38T 0x303000003030000030300000303000003030000030300000303000003030000 4 :=
  slice_correct (ms:=[exchangeRow 2 6,exchangeRow 1 5,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false,setBitRow 4 true]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g38s26 : Slice false (raw 7) g38T 0xff00ff00000000000000000000000000ff00ff 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g25Ok).1 bound25

theorem g38s27 : Slice false (raw 7) g38T 0xff00ff00000000000000000000000000ff00ff0000000000000000 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g25Ok).1 bound25

theorem g38s28 : Slice false (raw 7) g38T 0xff00ff00000000000000000000000000ff00ff00000000 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g25Ok).1 bound25

theorem g38s29 : Slice false (raw 7) g38T 0xffff0000000000000000000000000000ffff 4 :=
  slice_correct (ms:=[setBitRow 4 false,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g25Ok).1 bound25

def g38Cuts (k i : Nat) : Rule false g38T k := (if i<20 then (if i<10 then (if i<5 then (if i<2 then (if i<1 then (cutRule k g38s0 []) else (cutRule k g38s0 [(1,g38v3,g38v7)])) else (if i<3 then (cutRule k g38s0 [(1,g38v3,g38v10)]) else (if i<4 then (cutRule k g38s0 [(1,g38v7,g38v10)]) else (cutRule k g38s1 [])))) else (if i<7 then (if i<6 then (cutRule k g38s2 []) else (cutRule k g38s3 [])) else (if i<8 then (cutRule k g38s3 [(1,g38v3,g38v7)]) else (if i<9 then (cutRule k g38s3 [(1,g38v3,g38v10)]) else (cutRule k g38s3 [(1,g38v7,g38v10)]))))) else (if i<15 then (if i<12 then (if i<11 then (cutRule k g38s4 []) else (cutRule k g38s4 [(1,g38v3,g38v7)])) else (if i<13 then (cutRule k g38s4 [(1,g38v3,g38v10)]) else (if i<14 then (cutRule k g38s4 [(1,g38v7,g38v10)]) else (cutRule k g38s5 [])))) else (if i<17 then (if i<16 then (cutRule k g38s5 [(1,g38v3,g38v7)]) else (cutRule k g38s5 [(1,g38v3,g38v10)])) else (if i<18 then (cutRule k g38s6 []) else (if i<19 then (cutRule k g38s7 []) else (cutRule k g38s8 [])))))) else (if i<30 then (if i<25 then (if i<22 then (if i<21 then (cutRule k g38s9 []) else (cutRule k g38s10 [])) else (if i<23 then (cutRule k g38s11 []) else (if i<24 then (cutRule k g38s12 []) else (cutRule k g38s13 [])))) else (if i<27 then (if i<26 then (cutRule k g38s14 []) else (cutRule k g38s15 [])) else (if i<28 then (cutRule k g38s16 []) else (if i<29 then (cutRule k g38s17 []) else (cutRule k g38s18 []))))) else (if i<35 then (if i<32 then (if i<31 then (cutRule k g38s19 []) else (cutRule k g38s20 [])) else (if i<33 then (cutRule k g38s21 []) else (if i<34 then (cutRule k g38s22 []) else (cutRule k g38s23 [])))) else (if i<38 then (if i<36 then (cutRule k g38s24 []) else (if i<37 then (cutRule k g38s25 []) else (cutRule k g38s26 []))) else (if i<39 then (cutRule k g38s27 []) else (if i<40 then (cutRule k g38s28 []) else (cutRule k g38s29 [])))))))

def g38n0w : List Sig := [g38v0,g38v1,g38v2,g38v3,g38v4,g38v5,g38v7,g38v10]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g38n0 : Impossible false g38T 8 g38n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g38Cuts 7) (fun i => failRule false g38T 7))) (idx:=(fun j => bitsAt 0x1002740099002340089002140081001f40079001d40069001940044604618098481a1206428260a0682819051181426031180c26030680c1901498051900d44034600cc4032600c680319 18 (bitsAt 0x1351301138e00000000000001134d01130c0000000000000117d10137130000000000000112cb01328a0000000000000137d301118600000000000001214501100000000000000001110401104100000000000000e30c00e30c00000000000000e80e0146d400000000000000e28a01428a00000000000001481400e18600000000000000f0c300e00000000000000000e08200e04100000000000000c78c01675500000000000001779700c28a00000000000000c18601818600000000000000c00000c00000000000000001a04100c04100000000000000000000000000000000000000000000000000000000000001900001800000000000000001a04101804100000000000000000001018600000000000000a00000a00000000000000001a04100a04100000000000000958900600000000000000000608200804100000000000000004001d1c7 6 j))) (by decide +kernel)

def g38n1w : List Sig := [g38v0,g38v1,g38v2,g38v3,g38v5,g38v7,g38v8,g38v10]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g38n1 : Impossible false g38T 8 g38n1w.toFinset :=
  checkNode_sound (rules:=(codedRule (g38Cuts 7) (fun i => failRule false g38T 7))) (idx:=(fun j => bitsAt 0x4009d00264009500234008900214007d001e4007500194004460461809848461206848190a0c42826051181432050c41426031180c26014c4052600d44034600cc4032600c680319 18 (bitsAt 0x4fd304350000000000004e93043f00000000000041ad0414a00000000000412904d08000000000004fd3040e70000000000044a504000000000000004084040210000000000000000000000000000000714a06ff5000000000007d08076520000000000000000000000000000000606305c0000000000000644205c2100000000000714a0514a000000000007d0805108000000000000000050e70000000000050630500000000000000644205021000000000007def029080000000000028e705ce700000000000280002800000000000006421028210000000000023e8038e700000000000200002000000000000003c21020210000000000032cc01c00000000000001c4202c2100000000000002006cc6 5 j))) (by decide +kernel)

def g38n2w : List Sig := [g38v0,g38v1,g38v2,g38v3,g38v5,g38v7,g38v10,g38v11]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g38n2 : Impossible false g38T 8 g38n2w.toFinset :=
  checkNode_sound (rules:=(codedRule (g38Cuts 7) (fun i => failRule false g38T 7))) (idx:=(fun j => bitsAt 0x4009900254008d002240081001f40079001d4006500111811860260a0c428260a0682819051481451051181426031180c2601544052600d44034600cc4032600c680319 18 (bitsAt 0x7673065ce000000000006d4a06bb40000000000075080721000000000000000000000000000000005ca50580000000000000604205821000000000004a72075ce000000000006d6b0494a00000000000752904908000000000000000048e70000000000048a5048000000000000060840482100000000000394a0394a00000000000390804d08000000000004fb3038e7000000000003c630380000000000000384203821000000000007631029080000000000028e7058e700000000000280002800000000000006021028210000000000023a8040e700000000000200002000000000000004421020210000000000036ad01c00000000000001c4203021000000000000020068c6 5 j))) (by decide +kernel)

def g38n3w : List Sig := [g38v0,g38v1,g38v2,g38v3,g38v6,g38v7,g38v10]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g38n3 : Impossible false g38T 8 g38n3w.toFinset :=
  checkNode_sound (rules:=(codedRule (g38Cuts 7) (fun i => failRule false g38T 7))) (idx:=(fun j => bitsAt 0x100274009900254009100234007d001d4006900184005900154004860461809848511206848190a0c828310a0682819051181426030680c1901544053101498051900d44034600cc4032600c680319 18 (bitsAt 0x81559581238e00000000000079234d81530c0000000000008125128154100000000000008552497921860000000000006131457d200000000000000069210479204100000000000078e30c81630c00000000000080e40e81651400000000000089620878e18600000000000060f0c37ce00000000000000068e08278e04100000000000000000000000000000000000078c18679c18600000000000078c0007cc00000000000000079d04178c0410000000000006db1867901860000000000006110007d00000000000000006900417900410000000000007cb64b78600000000000000078608278a0410000000000005c004079e1c7 6 j))) (by decide +kernel)

def g38n4w : List Sig := [g38v0,g38v1,g38v2,g38v3,g38v5,g38v7,g38v9,g38v10]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g38n4 : Impossible false g38T 8 g38n4w.toFinset :=
  checkNode_sound (rules:=(codedRule (g38Cuts 7) (fun i => failRule false g38T 7))) (idx:=(fun j => bitsAt 0x4009d00254008d002240085001f40079001d4006d000f4002d000740015000118098481a1206428310a098281a0a0641446050980c26030680c1901544053101498051900d44034600cc4032600c680319 18 (bitsAt 0x1389301b7d70000000000000158950133cf00000000000001338e01334d00000000000001389301530c00000000000001524901318600000000000001414501300000000000000001310401304100000000000000000000000000000000000002134d02034d00000000000000000000000000000000000002318601c18600000000000001d00001c00000000000000001e04101c04100000000000000f34d00f34d00000000000000000002230c00000000000002320800f1860000000000000100c300f00000000000000000f08200f04100000000000002249200d30c00000000000000d18601a18600000000000000d00000d00000000000000001804100d04100000000000000c18601118600000000000000c00000c00000000000000001204100c04100000000000000b64b00600000000000000000608200a0410000000000000000400161c7 6 j))) (by decide +kernel)

def g38n5w : List Sig := [g38v0,g38v1,g38v2,g38v3,g38v5,g38v7,g38v10,g38v12]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g38n5 : Impossible false g38T 8 g38n5w.toFinset :=
  checkNode_sound (rules:=(codedRule (g38Cuts 7) (fun i => failRule false g38T 7))) (idx:=(fun j => bitsAt 0x4009900254008d002240081001f40079001d40071001040031000840011000218118485112118481a12064281a0a0641446050980c46030680c1901544053101498051900d44034600cc4032600c680319 18 (bitsAt 0x223cf01f6d700000000000002138e02034d00000000000000000000000000000000000002318601c18600000000000001d00001c00000000000000001e04101c0410000000000000225550113cf00000000000001138e01134d00000000000000000002230c00000000000002324901118600000000000001214501100000000000000001110401104100000000000000f34d00f34d00000000000000f88f01530c00000000000001520800f1860000000000000100c300f00000000000000000f08200f04100000000000002251400d30c00000000000000d18601a18600000000000000d00000d00000000000000001804100d04100000000000000c18601318600000000000000c00000c00000000000000001404100c04100000000000000b64b00600000000000000000608200a0410000000000000000400161c7 6 j))) (by decide +kernel)

def g38n6w : List Sig := [g38v0,g38v1,g38v2,g38v3,g38v5,g38v7,g38v10,g38v13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g38n6 : Impossible false g38T 8 g38n6w.toFinset :=
  checkNode_sound (rules:=(codedRule (g38Cuts 7) (fun i => failRule false g38T 7))) (idx:=(fun j => bitsAt 0x400a1002640095002340089002140081001f40079001d400350009400110003181446046180c460260a0c42826051181426031180c26030680c1901544053101498051900d44034600cc4032600c680319 18 (bitsAt 0x2038e01f38e00000000000002130c02130c00000000000002220801a18600000000000001b0c301a00000000000000001c08201a04100000000000000000001d7970000000000000133cf01238e00000000000002134d01230c00000000000001224901218600000000000001214501200000000000000001310401204100000000000001538e01438e00000000000002130c01430c0000000000000142080141860000000000000140c301400000000000000001508201404100000000000002145100e30c00000000000000e18602318600000000000000e00000e00000000000000001804100e04100000000000000c18601018600000000000000c00000c00000000000000001104100c04100000000000000b64b00600000000000000000608200a0410000000000000000400161c7 6 j))) (by decide +kernel)

def g38n7w : List Sig := [g38v0,g38v1,g38v2,g38v3,g38v5,g38v7,g38v10]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g38n7 : Impossible false g38T 9 g38n7w.toFinset :=
  checkNode_sound (rules:=(codedRule (g38Cuts 8) (fun i => (if i<3 then (if i<1 then (linkRule g38n0w g38n0) else (if i<2 then (linkRule g38n1w g38n1) else (linkRule g38n2w g38n2))) else (if i<5 then (if i<4 then (linkRule g38n3w g38n3) else (linkRule g38n4w g38n4)) else (if i<6 then (linkRule g38n5w g38n5) else (linkRule g38n6w g38n6))))))) (idx:=(fun j => bitsAt 0x8001a00058001200038000a00018000100194005d00144004d001140039000a4001900054001100001811860261206848190a0c428260a0682819051181426031180c26030680c1901544053101498051900d44034600cc4032600c680319 18 (bitsAt 0xa565d66544100000000000007d43cf79438e000000000000a1434d69630c0000000000009562498941860000000000008151457940000000000000008541047940410000000000007d038e79038e0000000000009d030c65730c0000000000009172088901860000000000008110c37900000000000000008500827900410000000000007e64d378e30c0000000000007ce18679d18600000000000078e00078e00000000000000079b04178e0410000000000008cc18689218600000000000080c00078c00000000000000085304178c04100000000000080b70b78600000000000000084608278a0410000000000007800407981c7 6 j))) (by decide +kernel)

theorem bound38 : Lower false (raw 7) g38T 10 := finishBound g38Ok g38n7

def g39T : Sig := 0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8

def g39H : List Nat := [2,1,1,1]

theorem g39Ok : basicCheck 4 g39T g39H=true := by decide +kernel

theorem g39s0 : Slice false (raw 4) g39T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 4 :=
  slice_correct (ms:=[setBitRow 3 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g39Cuts (k i : Nat) : Rule false g39T k := (cutRule k g39s0 [])

theorem bound39 : Lower false (raw 4) g39T 5 := finishBound g39Ok ((g39Cuts 4 0).property (raw 4) (by decide +kernel) (by decide +kernel))

def g40T : Sig := 0xffffffe8ffffeae8ffe8ffe8ffe8eae8ffffffe8ffffeae8ffe8ffe8ffe8eae8

def g40H : List Nat := [2,1,1,1,8,8,16]

theorem g40Ok : basicCheck 7 g40T g40H=true := by decide +kernel

def g40v0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g40v1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g40v2 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee

def g40v3 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g40v4 : Sig := 0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa

def g40v5 : Sig := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc

def g40v6 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g40v7 : Sig := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa

def g40v8 : Sig := 0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc

def g40v9 : Sig := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0

def g40v10 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g40v11 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000

def g40v12 : Sig := 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa

def g40v13 : Sig := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000

theorem g40s0 : Slice false (raw 7) g40T 0x3333333333333333333333333333333333333333333333333333333333333333 7 :=
  slice_correct (ms:=[exchangeRow 5 6,exchangeRow 4 5,exchangeRow 3 4,exchangeRow 2 3,exchangeRow 1 2,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g37Ok).1 bound37

theorem g40s1 : Slice false (raw 7) g40T 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f 7 :=
  slice_correct (ms:=[exchangeRow 5 6,exchangeRow 4 5,exchangeRow 3 4,exchangeRow 2 3,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g37Ok).1 bound37

theorem g40s2 : Slice false (raw 7) g40T 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff 7 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g26Ok).1 bound26

theorem g40s3 : Slice false (raw 7) g40T 0xffff0000ffff00000000000000000000ffff0000ffff 7 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g26Ok).1 bound26

theorem g40s4 : Slice false (raw 7) g40T 0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 7 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g26Ok).1 bound26

theorem g40s5 : Slice false (raw 7) g40T 0xffffffff000000000000000000000000ffffffff 7 :=
  slice_correct (ms:=[setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g26Ok).1 bound26

theorem g40s6 : Slice false (raw 7) g40T 0xff00000000000000ff00000000000000ff00000000000000ff0000 5 :=
  slice_correct (ms:=[exchangeRow 3 6,setBitRow 3 false,setBitRow 4 true,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g40s7 : Slice false (raw 7) g40T 0xff00000000000000ff00000000000000ff00000000000000ff000000000000 4 :=
  slice_correct (ms:=[exchangeRow 3 6,setBitRow 3 false,setBitRow 4 true,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g31Ok).1 bound31

theorem g40s8 : Slice false (raw 7) g40T 0xff00000000000000ff00000000000000ff00000000000000ff000000000000 5 :=
  slice_correct (ms:=[exchangeRow 3 6,setBitRow 3 false,setBitRow 4 true,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g40s9 : Slice false (raw 7) g40T 0xff00ff00000000000000000000000000ff00ff0000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g40s10 : Slice false (raw 7) g40T 0xff00ff00000000000000000000000000ff00ff000000000000000000000000 4 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g31Ok).1 bound31

theorem g40s11 : Slice false (raw 7) g40T 0xffff0000000000000000000000000000ffff 5 :=
  slice_correct (ms:=[setBitRow 4 false,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g39Ok).1 bound39

theorem g40s12 : Slice false (raw 7) g40T 0x1111111111111111111111111111111111111111111111111111111111111111 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g35Ok).1 bound35

theorem g40s13 : Slice false (raw 7) g40T 0x505050505050505050505050505050505050505050505050505050505050505 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g35Ok).1 bound35

theorem g40s14 : Slice false (raw 7) g40T 0x101010101010101010101010101010101010101010101010101010101010101 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g35Ok).1 bound35

theorem g40s15 : Slice false (raw 7) g40T 0x1010101010101010101010101010101010101010101010101010101010101010 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g35Ok).1 bound35

theorem g40s16 : Slice false (raw 7) g40T 0x404040404040404040404040404040404040404040404040404040404040404 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 true,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g35Ok).1 bound35

theorem g40s17 : Slice false (raw 7) g40T 0x3030303000000000303030300000000030303030000000003030303 4 :=
  slice_correct (ms:=[exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,setBitRow 1 false,setBitRow 2 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g23Ok).1 bound23

theorem g40s18 : Slice false (raw 7) g40T 0xff00000000000000ff00000000000000ff00000000000000ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g40s19 : Slice false (raw 7) g40T 0xff00000000000000ff00000000000000ff00000000000000ff00000000 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false,setBitRow 5 true,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g40s20 : Slice false (raw 7) g40T 0xff000000ff0000000000000000000000ff000000ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g40s21 : Slice false (raw 7) g40T 0xff000000ff0000000000000000000000ff000000ff0000000000000000 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false,setBitRow 5 false,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g40s22 : Slice false (raw 7) g40T 0xff000000ff0000000000000000000000ff000000ff0000 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 true,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

theorem g40s23 : Slice false (raw 7) g40T 0xff00ff00000000000000000000000000ff00ff00000000 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false,setBitRow 5 true,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g40Cuts (k i : Nat) : Rule false g40T k := (if i<17 then (if i<8 then (if i<4 then (if i<2 then (if i<1 then (cutRule k g40s0 []) else (cutRule k g40s1 [])) else (if i<3 then (cutRule k g40s2 []) else (cutRule k g40s2 [(1,g40v0,g40v1)]))) else (if i<6 then (if i<5 then (cutRule k g40s2 [(1,g40v0,g40v3)]) else (cutRule k g40s2 [(1,g40v1,g40v3)])) else (if i<7 then (cutRule k g40s3 []) else (cutRule k g40s3 [(1,g40v0,g40v1)])))) else (if i<12 then (if i<10 then (if i<9 then (cutRule k g40s3 [(1,g40v0,g40v3)]) else (cutRule k g40s3 [(1,g40v1,g40v3)])) else (if i<11 then (cutRule k g40s4 []) else (cutRule k g40s4 [(1,g40v0,g40v1)]))) else (if i<14 then (if i<13 then (cutRule k g40s4 [(1,g40v0,g40v3)]) else (cutRule k g40s4 [(1,g40v1,g40v3)])) else (if i<15 then (cutRule k g40s5 []) else (if i<16 then (cutRule k g40s5 [(1,g40v0,g40v1)]) else (cutRule k g40s5 [(1,g40v0,g40v3)])))))) else (if i<26 then (if i<21 then (if i<19 then (if i<18 then (cutRule k g40s6 []) else (cutRule k g40s7 [])) else (if i<20 then (cutRule k g40s8 []) else (cutRule k g40s9 []))) else (if i<23 then (if i<22 then (cutRule k g40s10 []) else (cutRule k g40s11 [])) else (if i<24 then (cutRule k g40s12 []) else (if i<25 then (cutRule k g40s13 []) else (cutRule k g40s14 []))))) else (if i<30 then (if i<28 then (if i<27 then (cutRule k g40s15 []) else (cutRule k g40s16 [])) else (if i<29 then (cutRule k g40s17 []) else (cutRule k g40s18 []))) else (if i<32 then (if i<31 then (cutRule k g40s19 []) else (cutRule k g40s20 [])) else (if i<33 then (cutRule k g40s21 []) else (if i<34 then (cutRule k g40s22 []) else (cutRule k g40s23 [])))))))

def g40n0w : List Sig := [g40v0,g40v1,g40v2,g40v3,g40v6,g40v10,g40v11,g40v13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g40n0 : Impossible false g40T 8 g40n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g40Cuts 7) (fun i => failRule false g40T 7))) (idx:=(fun j => bitsAt 0x4008500204007d001e40075001b4006500174003d000b4001d0003400045061141285034140c850310a130284a06130184a060d01832060c4096102528093101928063201584053100d84034a00cc80331 18 (bitsAt 0x1241001241000000000000001238e01838e00000000000001a28a0122080000000000000141450121040000000000000128920128520000000000000130c301200000000000000001208201204100000000000001959601038e00000000000001020801b2080000000000000111040101040000000000000108100107d000000000000001000001000000000000000001d04101004100000000000000e20801520800000000000000f10400e10400000000000000e8ce00e7ce00000000000000e00000e00000000000000001604100e04100000000000000d1c700810400000000000000878800b7cb00000000000000c78c00800000000000000000808200b04100000000000000474401c75700000000000000674600400000000000000000474400604100000000000000000000000000000000000000000000000000000000000000000001d249 6 j))) (by decide +kernel)

def g40n1w : List Sig := [g40v0,g40v1,g40v3,g40v4,g40v6,g40v10,g40v11,g40v13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g40n1 : Impossible false g40T 8 g40n1w.toFinset :=
  checkNode_sound (rules:=(codedRule (g40Cuts 7) (fun i => failRule false g40T 7))) (idx:=(fun j => bitsAt 0x4008500204007d001e40075001a40065001840041000c400210004400005061141285034140c850310a130284a06130184a060d01832060c4096102530093101930063401584054c014d0053100d840331 18 (bitsAt 0x1241001241000000000000001238e01838e00000000000001a28a0122080000000000000128920128520000000000000141450120820000000000000130410120000000000000000121040120c300000000000001959601038e00000000000001020801b2080000000000000118110107d000000000000001108201008200000000000001000001000000000000000001d0c30100c300000000000000e20801520800000000000000f8cf00e7ce00000000000000f08200e08200000000000000e00000e0000000000000000160c300e0c300000000000000878800b7cb00000000000000d78d00808200000000000000c1c700800000000000000000810400b0c300000000000000000000000000000000000001d00001d71700000000000000000000000000000000000001d18600200000000000000000000001d2490000000000000007400060c3 6 j))) (by decide +kernel)

def g40n2w : List Sig := [g40v0,g40v1,g40v3,g40v6,g40v7,g40v10,g40v11,g40v13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g40n2 : Impossible false g40T 8 g40n2w.toFinset :=
  checkNode_sound (rules:=(codedRule (g40Cuts 7) (fun i => failRule false g40T 7))) (idx:=(fun j => bitsAt 0x4008500204007d001e40075001b4006900194004d001114184504a140d05032140c4284c0a128184c06128183102584093101930064a018d0063201584054c014c4036100d280331 18 (bitsAt 0x45ef045ef0000000000045ad06dad0000000000047d1047b100000000000596b0454a000000000004ca5044630000000000048420440000000000000442104421000000000007eb503dad000000000003f8f05b76000000000003d4a0754a00000000000406303c63000000000003c0003c00000000000005f9703c210000000000037ed0537400000000000354a0514a00000000000386303463000000000003400034000000000000057f50342100000000000000000000000000000006463060c6000000000006800060e7000000000000000000000000000000065080286300000000000692902800000000000000000030210000000000018e600c00000000000000c830182100000000000002001c84 5 j))) (by decide +kernel)

def g40n3w : List Sig := [g40v0,g40v1,g40v3,g40v6,g40v10,g40v12,g40v13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g40n3 : Impossible false g40T 8 g40n3w.toFinset :=
  checkNode_sound (rules:=(codedRule (g40Cuts 7) (fun i => failRule false g40T 7))) (idx:=(fun j => bitsAt 0x1002240085001f40079001b400690019400550013400485061141285034140c850310a130284a06130184a060d01832060c40961024c4064c019280634018c80561014d0053100d88036100cc80331 18 (bitsAt 0x7d44928944920000000000006544107df41000000000000089a30c7d42cb0000000000006d61868941040000000000006d50828940000000000000006d40c38940410000000000007e16187d24100000000000007d22cb7e034d0000000000007d31047121c70000000000007d20007122080000000000000000000000000000000000007d02cb7d72cb0000000000006511047d01040000000000006500007d00000000000000006580417d004100000000000074f2497cb10400000000000078e28a7cb00000000000000068b68b7cd041000000000000707207704000000000000000704144707041000000000000700040708145 6 j))) (by decide +kernel)

def g40n4w : List Sig := [g40v0,g40v1,g40v3,g40v5,g40v6,g40v10,g40v11,g40v13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g40n4 : Impossible false g40T 8 g40n4w.toFinset :=
  checkNode_sound (rules:=(codedRule (g40Cuts 7) (fun i => failRule false g40T 7))) (idx:=(fun j => bitsAt 0x4008500204007d001e40075001c40069001940035000940015000014184504a140d05032140c4284c0a128184c061281834060c8183102584094a024c4064c019280634018c8053400d280332 18 (bitsAt 0x113cf0113cf00000000000001134d01734d0000000000000192490111c70000000000000128120117d10000000000000131450110c300000000000001218601110400000000000001104101100000000000000001855500f34d00000000000000f1c701c1c700000000000000f78f00f74f0000000000000100c300f0c300000000000000f10400f10400000000000001a00000f00000000000000000d1c70141c700000000000000d84d00d74d00000000000000e0c300d0c300000000000000d10400d10400000000000001500000d00000000000000000b6cb00774700000000000000c1450070c300000000000000b18600710400000000000000704100a00000000000000000000000000000000000000000000000000000000000000001a00001a20800000000000000000001a69600000000000001a08200300000000000000001a000004082 6 j))) (by decide +kernel)

def g40n5w : List Sig := [g40v0,g40v1,g40v3,g40v6,g40v8,g40v10,g40v11,g40v13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g40n5 : Impossible false g40T 8 g40n5w.toFinset :=
  checkNode_sound (rules:=(codedRule (g40Cuts 7) (fun i => failRule false g40T 7))) (idx:=(fun j => bitsAt 0x1002140081001f40079001d4006d001a40065001114184504a140d05032140c428620a130284a0a0c8184c06128183201930064a018c80561014d0053100d280332 18 (bitsAt 0x3d8c03d8c000000000003d290612900000000000437003f4f0000000000051ce03d0800000000000448403c420000000000040e703ce7000000000003c2103c000000000000072730312900000000000332c05f14000000000003108069080000000000034420304200000000000332c030e7000000000005c000300000000000000278904b120000000000025080496b00000000000284202442000000000002789024e7000000000004c0002400000000000000000000000000000000058a50544200000000000000000000000000000005c00054630000000000058c602042000000000000000020e7000000000005c21020000000000000014e500ae200000000000086201400000000000005c0001c63 5 j))) (by decide +kernel)

def g40n6w : List Sig := [g40v0,g40v1,g40v3,g40v6,g40v9,g40v10,g40v11,g40v13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g40n6 : Impossible false g40T 8 g40n6w.toFinset :=
  checkNode_sound (rules:=(codedRule (g40Cuts 7) (fun i => failRule false g40T 7))) (idx:=(fun j => bitsAt 0x4008500204007d001e40075001a40065001114184504a140d05032140c428640a130284a0a0d0184c06128183401930064a018d0053400d84034a00cc80331 18 (bitsAt 0x3d8c03d8c000000000003d2905d2900000000000475103f2f0000000000051ce03d080000000000044c603cc600000000000406303c00000000000003c4203c21000000000006e730312900000000000330c05af40000000000031080650800000000000370d030c6000000000003000030000000000000058210302100000000000276904af20000000000025080496b000000000002b6a024c600000000000240002400000000000004c210242100000000000000000000000000000000000000000000000000058a50540000000000000584205421000000000000000020c60000000000058e702000000000000005842020210000000000018a5058000000000000058840182100000000000002001484 5 j))) (by decide +kernel)

def g40n7w : List Sig := [g40v0,g40v1,g40v3,g40v6,g40v10,g40v11,g40v13]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g40n7 : Impossible false g40T 9 g40n7w.toFinset :=
  checkNode_sound (rules:=(codedRule (g40Cuts 8) (fun i => (if i<3 then (if i<1 then (linkRule g40n0w g40n0) else (if i<2 then (linkRule g40n1w g40n1) else (linkRule g40n2w g40n2))) else (if i<5 then (if i<4 then (linkRule g40n3w g40n3) else (linkRule g40n4w g40n4)) else (if i<6 then (linkRule g40n5w g40n5) else (linkRule g40n6w g40n6))))))) (idx:=(fun j => bitsAt 0x8001a00058001200038000a000180001001640051001340045000e400290006400090001400005061141285034140c850310a130284a06130184a060d01832060c40961024c4064c019280634018c80561014d0053100d84034a00cc80331 18 (bitsAt 0x8144927d44920000000000007d441089b41000000000000085d30c7d42cb0000000000008561868941040000000000008550c38940000000000000008540828940410000000000007dc6187d24100000000000007d22cb7de2cb0000000000008131047d21040000000000008120007d20000000000000008260417d20410000000000007d02cb7d72cb0000000000007d11048901040000000000007d00008900000000000000007d8041890041000000000000a4f2497cb104000000000000a0e28a7cb00000000000000094b0827cd0410000000000009c72076440000000000000009041446870410000000000008c0040648145 6 j))) (by decide +kernel)

theorem bound40 : Lower false (raw 7) g40T 10 := finishBound g40Ok g40n7

def g41T : Sig := 0xffececa8ffececa8ffececa8ffececa8ffececa8ffececa8ffececa8ffececa8

def g41H : List Nat := [2,1,1,2,2]

theorem g41Ok : basicCheck 5 g41T g41H=true := by decide +kernel

theorem g41s0 : Slice false (raw 5) g41T 0x505050505050505050505050505050505050505050505050505050505050505 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g41Cuts (k i : Nat) : Rule false g41T k := (cutRule k g41s0 [])

theorem bound41 : Lower false (raw 5) g41T 6 := finishBound g41Ok ((g41Cuts 5 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g42T : Sig := 0xffececa8ffececa8ffececa8ffececa8ffececa8ffececa8ffececa8ffececa8

def g42H : List Nat := [2,1,1,2,2]

theorem g42Ok : basicCheck 5 g42T g42H=true := by decide +kernel

theorem g42s0 : Slice false (raw 5) g42T 0x505050505050505050505050505050505050505050505050505050505050505 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

def g42Cuts (k i : Nat) : Rule false g42T k := (cutRule k g42s0 [])

theorem bound42 : Lower false (raw 5) g42T 5 := finishBound g42Ok ((g42Cuts 4 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g43T : Sig := 0xfff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8

def g43H : List Nat := [2,1,2,4,4]

theorem g43Ok : basicCheck 5 g43T g43H=true := by decide +kernel

theorem g43s0 : Slice false (raw 5) g43T 0x1111111111111111111111111111111111111111111111111111111111111111 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

def g43Cuts (k i : Nat) : Rule false g43T k := (cutRule k g43s0 [])

theorem bound43 : Lower false (raw 5) g43T 5 := finishBound g43Ok ((g43Cuts 4 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g44T : Sig := 0xfff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8fff8f8c8

def g44H : List Nat := [2,1,2,4,4]

theorem g44Ok : basicCheck 5 g44T g44H=true := by decide +kernel

theorem g44s0 : Slice false (raw 5) g44T 0x1111111111111111111111111111111111111111111111111111111111111111 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g44Cuts (k i : Nat) : Rule false g44T k := (cutRule k g44s0 [])

theorem bound44 : Lower false (raw 5) g44T 6 := finishBound g44Ok ((g44Cuts 5 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g45T : Sig := 0xffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8

def g45H : List Nat := [2,1,1,1,8]

theorem g45Ok : basicCheck 5 g45T g45H=true := by decide +kernel

theorem g45s0 : Slice false (raw 5) g45T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g45Cuts (k i : Nat) : Rule false g45T k := (cutRule k g45s0 [])

theorem bound45 : Lower false (raw 5) g45T 6 := finishBound g45Ok ((g45Cuts 5 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g46T : Sig := 0xffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8ffe8eae8

def g46H : List Nat := [2,1,1,1,8]

theorem g46Ok : basicCheck 5 g46T g46H=true := by decide +kernel

theorem g46s0 : Slice false (raw 5) g46T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 3 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

def g46Cuts (k i : Nat) : Rule false g46T k := (cutRule k g46s0 [])

theorem bound46 : Lower false (raw 5) g46T 5 := finishBound g46Ok ((g46Cuts 4 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g47T : Sig := 0xfffafaeafffafaeafffafaeafffafaeafffafaeafffafaeafffafaeafffafaea

def g47H : List Nat := [0,4,2,4,4]

theorem g47Ok : basicCheck 5 g47T g47H=true := by decide +kernel

theorem g47s0 : Slice false (raw 5) g47T 0x1111111111111111111111111111111111111111111111111111111111111111 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

def g47Cuts (k i : Nat) : Rule false g47T k := (cutRule k g47s0 [])

theorem bound47 : Lower false (raw 5) g47T 5 := finishBound g47Ok ((g47Cuts 4 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g48T : Sig := 0xfffafaeafffafaeafffafaeafffafaeafffafaeafffafaeafffafaeafffafaea

def g48H : List Nat := [0,4,2,4,4]

theorem g48Ok : basicCheck 5 g48T g48H=true := by decide +kernel

theorem g48s0 : Slice false (raw 5) g48T 0x1111111111111111111111111111111111111111111111111111111111111111 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g48Cuts (k i : Nat) : Rule false g48T k := (cutRule k g48s0 [])

theorem bound48 : Lower false (raw 5) g48T 6 := finishBound g48Ok ((g48Cuts 5 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g49T : Sig := 0xfffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeee

def g49H : List Nat := [0,0,8,4,4]

theorem g49Ok : basicCheck 5 g49T g49H=true := by decide +kernel

theorem g49s0 : Slice false (raw 5) g49T 0x1111111111111111111111111111111111111111111111111111111111111111 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

def g49Cuts (k i : Nat) : Rule false g49T k := (cutRule k g49s0 [])

theorem bound49 : Lower false (raw 5) g49T 5 := finishBound g49Ok ((g49Cuts 4 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g50T : Sig := 0xfffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeee

def g50H : List Nat := [0,0,8,4,4]

theorem g50Ok : basicCheck 5 g50T g50H=true := by decide +kernel

theorem g50s0 : Slice false (raw 5) g50T 0x1111111111111111111111111111111111111111111111111111111111111111 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g50Cuts (k i : Nat) : Rule false g50T k := (cutRule k g50s0 [])

theorem bound50 : Lower false (raw 5) g50T 6 := finishBound g50Ok ((g50Cuts 5 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g51T : Sig := 0xfff8f888fff8f888fff8f888fff8f888fff8f888fff8f888fff8f888fff8f888

def g51H : List Nat := [2,1,8,4,4]

theorem g51Ok : basicCheck 5 g51T g51H=true := by decide +kernel

theorem g51s0 : Slice false (raw 5) g51T 0x1111111111111111111111111111111111111111111111111111111111111111 3 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

def g51Cuts (k i : Nat) : Rule false g51T k := (cutRule k g51s0 [])

theorem bound51 : Lower false (raw 5) g51T 5 := finishBound g51Ok ((g51Cuts 4 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g52T : Sig := 0xfff8f888fff8f888fff8f888fff8f888fff8f888fff8f888fff8f888fff8f888

def g52H : List Nat := [2,1,8,4,4]

theorem g52Ok : basicCheck 5 g52T g52H=true := by decide +kernel

theorem g52s0 : Slice false (raw 5) g52T 0x1111111111111111111111111111111111111111111111111111111111111111 4 :=
  slice_correct (ms:=[exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g52Cuts (k i : Nat) : Rule false g52T k := (cutRule k g52s0 [])

theorem bound52 : Lower false (raw 5) g52T 6 := finishBound g52Ok ((g52Cuts 5 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g53T : Sig := 0xffe8e8e8ffe8e8e8ffe8e8e8ffe8e8e8ffe8e8e8ffe8e8e8ffe8e8e8ffe8e8e8

def g53H : List Nat := [2,1,1,16,8]

theorem g53Ok : basicCheck 5 g53T g53H=true := by decide +kernel

theorem g53s0 : Slice false (raw 5) g53T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 3 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

def g53Cuts (k i : Nat) : Rule false g53T k := (cutRule k g53s0 [])

theorem bound53 : Lower false (raw 5) g53T 5 := finishBound g53Ok ((g53Cuts 4 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g54T : Sig := 0xffe8e8e8ffe8e8e8ffe8e8e8ffe8e8e8ffe8e8e8ffe8e8e8ffe8e8e8ffe8e8e8

def g54H : List Nat := [2,1,1,16,8]

theorem g54Ok : basicCheck 5 g54T g54H=true := by decide +kernel

theorem g54s0 : Slice false (raw 5) g54T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g54Cuts (k i : Nat) : Rule false g54T k := (cutRule k g54s0 [])

theorem bound54 : Lower false (raw 5) g54T 6 := finishBound g54Ok ((g54Cuts 5 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g55T : Sig := 0xffffffe8ffffffe8ffffffe8ffffffe8ffffffe8ffffffe8ffffffe8ffffffe8

def g55H : List Nat := [2,1,1,0,0]

theorem g55Ok : basicCheck 5 g55T g55H=true := by decide +kernel

theorem g55s0 : Slice false (raw 5) g55T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 4 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g21Ok).1 bound21

def g55Cuts (k i : Nat) : Rule false g55T k := (cutRule k g55s0 [])

theorem bound55 : Lower false (raw 5) g55T 6 := finishBound g55Ok ((g55Cuts 5 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g56T : Sig := 0xffffffe8ffffffe8ffffffe8ffffffe8ffffffe8ffffffe8ffffffe8ffffffe8

def g56H : List Nat := [2,1,1,0,0]

theorem g56Ok : basicCheck 5 g56T g56H=true := by decide +kernel

theorem g56s0 : Slice false (raw 5) g56T 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff 3 :=
  slice_correct (ms:=[setBitRow 3 false,setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g19Ok).1 bound19

def g56Cuts (k i : Nat) : Rule false g56T k := (cutRule k g56s0 [])

theorem bound56 : Lower false (raw 5) g56T 5 := finishBound g56Ok ((g56Cuts 4 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g57T : Sig := 0xfefaeeeafefaeeeafefaeeeafefaeeeafefaeeeafefaeeeafefaeeeafefaeeea

def g57H : List Nat := [0,4,2,2,4]

theorem g57Ok : basicCheck 5 g57T g57H=true := by decide +kernel

theorem g57s0 : Slice false (raw 5) g57T 0x5555555555555555555555555555555555555555555555555555555555555555 4 :=
  slice_correct (ms:=[exchangeRow 3 4,exchangeRow 2 3,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 false]) (by decide +kernel) (by decide +kernel) (basic_data g35Ok).1 bound35

def g57Cuts (k i : Nat) : Rule false g57T k := (cutRule k g57s0 [])

theorem bound57 : Lower false (raw 5) g57T 5 := finishBound g57Ok ((g57Cuts 4 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g58T : Sig := 0xfffff8a8fffff8a8fffff8a8fffff8a8fffff8a8fffff8a8fffff8a8fffff8a8

def g58H : List Nat := [2,1,1,4,0]

theorem g58Ok : basicCheck 5 g58T g58H=true := by decide +kernel

theorem g58s0 : Slice false (raw 5) g58T 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff 4 :=
  slice_correct (ms:=[setBitRow 4 false]) (by decide +kernel) (by decide +kernel) (basic_data g25Ok).1 bound25

def g58Cuts (k i : Nat) : Rule false g58T k := (cutRule k g58s0 [])

theorem bound58 : Lower false (raw 5) g58T 5 := finishBound g58Ok ((g58Cuts 4 0).property (raw 5) (by decide +kernel) (by decide +kernel))

def g59T : Sig := 0xffffffffffffffffffffffe8ffffeae8ffffffe8ffffeae8ffe8ffe8ffe8eae8

def g59H : List Nat := [2,1,1,1,8,8,16,16]

theorem g59Ok : basicCheck 8 g59T g59H=true := by decide +kernel

def g59v0 : Sig := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000

def g59v1 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g59v2 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc

def g59v3 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee

def g59v4 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g59v5 : Sig := 0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa

def g59v6 : Sig := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc

def g59v7 : Sig := 0xff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00ff00aa00

def g59v8 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00

def g59v9 : Sig := 0xffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00

def g59v10 : Sig := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa

def g59v11 : Sig := 0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc

def g59v12 : Sig := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0

def g59v13 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000

def g59v14 : Sig := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa

def g59v15 : Sig := 0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc

def g59v16 : Sig := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0

def g59v17 : Sig := 0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00

def g59v18 : Sig := 0xffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaa

def g59v19 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000

def g59v20 : Sig := 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa

def g59v21 : Sig := 0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000

def g59v22 : Sig := 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaa

def g59v23 : Sig := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000

def g59v24 : Sig := 0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa

def g59v25 : Sig := 0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc

def g59v26 : Sig := 0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0

def g59v27 : Sig := 0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00

def g59v28 : Sig := 0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000

def g59v29 : Sig := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000

def g59v30 : Sig := 0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa

def g59v31 : Sig := 0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc

def g59v32 : Sig := 0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def g59v33 : Sig := 0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00

def g59v34 : Sig := 0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000

def g59v35 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000

theorem g59s0 : Slice false (raw 8) g59T 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff 11 :=
  slice_correct (ms:=[exchangeRow 6 7,exchangeRow 5 6,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g34Ok).1 bound34

theorem g59s1 : Slice false (raw 8) g59T 0x3333333333333333333333333333333333333333333333333333333333333333 10 :=
  slice_correct (ms:=[exchangeRow 6 7,exchangeRow 5 6,exchangeRow 4 5,exchangeRow 3 4,exchangeRow 2 3,exchangeRow 1 2,setBitRow 1 false]) (by decide +kernel) (by decide +kernel) (basic_data g38Ok).1 bound38

theorem g59s2 : Slice false (raw 8) g59T 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f 10 :=
  slice_correct (ms:=[exchangeRow 6 7,exchangeRow 5 6,exchangeRow 4 5,exchangeRow 3 4,exchangeRow 2 3,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g38Ok).1 bound38

theorem g59s3 : Slice false (raw 8) g59T 0xffffffffffffffff0000000000000000ffffffffffffffff 10 :=
  slice_correct (ms:=[exchangeRow 6 7,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g40Ok).1 bound40

theorem g59s4 : Slice false (raw 8) g59T 0xffffffffffffffffffffffffffffffff 10 :=
  slice_correct (ms:=[setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g40Ok).1 bound40

theorem g59s5 : Slice false (raw 8) g59T 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff 9 :=
  slice_correct (ms:=[exchangeRow 5 7,exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g22Ok).1 bound22

theorem g59s6 : Slice false (raw 8) g59T 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff 8 :=
  slice_correct (ms:=[exchangeRow 5 7,exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g20Ok).1 bound20

theorem g59s7 : Slice false (raw 8) g59T 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff 9 :=
  slice_correct (ms:=[exchangeRow 5 7,exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g22Ok).1 bound22

theorem g59s8 : Slice false (raw 8) g59T 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 8 :=
  slice_correct (ms:=[exchangeRow 5 7,exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g20Ok).1 bound20

theorem g59s9 : Slice false (raw 8) g59T 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 9 :=
  slice_correct (ms:=[exchangeRow 5 7,exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g22Ok).1 bound22

theorem g59s10 : Slice false (raw 8) g59T 0x1111111111111111111111111111111111111111111111111111111111111111 7 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g36Ok).1 bound36

theorem g59s11 : Slice false (raw 8) g59T 0x505050505050505050505050505050505050505050505050505050505050505 7 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g36Ok).1 bound36

theorem g59s12 : Slice false (raw 8) g59T 0xffff0000ffff00000000000000000000ffff0000ffff 7 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g26Ok).1 bound26

theorem g59s13 : Slice false (raw 8) g59T 0xffff0000ffff0000ffff0000ffff 7 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g26Ok).1 bound26

theorem g59s14 : Slice false (raw 8) g59T 0x101010101010101010101010101010101010101010101010101010101010101 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g41Ok).1 bound41

theorem g59s15 : Slice false (raw 8) g59T 0x101010101010101010101010101010101010101010101010101010101010101 7 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g36Ok).1 bound36

theorem g59s16 : Slice false (raw 8) g59T 0x1010101010101010101010101010101010101010101010101010101010101010 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g42Ok).1 bound42

theorem g59s17 : Slice false (raw 8) g59T 0x1010101010101010101010101010101010101010101010101010101010101010 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g41Ok).1 bound41

theorem g59s18 : Slice false (raw 8) g59T 0x1010101010101010101010101010101010101010101010101010101010101010 7 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 true]) (by decide +kernel) (by decide +kernel) (basic_data g36Ok).1 bound36

theorem g59s19 : Slice false (raw 8) g59T 0x404040404040404040404040404040404040404040404040404040404040404 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 true,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g42Ok).1 bound42

theorem g59s20 : Slice false (raw 8) g59T 0x404040404040404040404040404040404040404040404040404040404040404 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 true,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g41Ok).1 bound41

theorem g59s21 : Slice false (raw 8) g59T 0x404040404040404040404040404040404040404040404040404040404040404 7 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 5,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 true,setBitRow 2 false]) (by decide +kernel) (by decide +kernel) (basic_data g36Ok).1 bound36

theorem g59s22 : Slice false (raw 8) g59T 0x3030303000000000303030300000000030303030000000003030303 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,setBitRow 1 false,setBitRow 2 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g43Ok).1 bound43

theorem g59s23 : Slice false (raw 8) g59T 0x3030303000000000303030300000000030303030000000003030303 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,setBitRow 1 false,setBitRow 2 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g44Ok).1 bound44

theorem g59s24 : Slice false (raw 8) g59T 0x3030303000000000303030300000000030303030000000003030303 7 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,setBitRow 1 false,setBitRow 2 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g24Ok).1 bound24

theorem g59s25 : Slice false (raw 8) g59T 0xffff0000ffff 6 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g45Ok).1 bound45

theorem g59s26 : Slice false (raw 8) g59T 0xffff0000ffff 7 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g26Ok).1 bound26

theorem g59s27 : Slice false (raw 8) g59T 0xffff0000ffff00000000000000000000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 false,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g46Ok).1 bound46

theorem g59s28 : Slice false (raw 8) g59T 0xffff0000ffff00000000000000000000000000000000 6 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 false,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g45Ok).1 bound45

theorem g59s29 : Slice false (raw 8) g59T 0xffff0000ffff00000000000000000000000000000000 7 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 false,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g26Ok).1 bound26

theorem g59s30 : Slice false (raw 8) g59T 0xffff0000ffff0000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 true,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g46Ok).1 bound46

theorem g59s31 : Slice false (raw 8) g59T 0xffff0000ffff0000000000000000 6 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 true,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g45Ok).1 bound45

theorem g59s32 : Slice false (raw 8) g59T 0xffff0000ffff0000000000000000 7 :=
  slice_correct (ms:=[exchangeRow 4 5,setBitRow 4 false,setBitRow 6 true,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g26Ok).1 bound26

theorem g59s33 : Slice false (raw 8) g59T 0xffffffff 5 :=
  slice_correct (ms:=[setBitRow 5 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g46Ok).1 bound46

theorem g59s34 : Slice false (raw 8) g59T 0xffffffff 6 :=
  slice_correct (ms:=[setBitRow 5 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g45Ok).1 bound45

theorem g59s35 : Slice false (raw 8) g59T 0xffffffff 7 :=
  slice_correct (ms:=[setBitRow 5 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g26Ok).1 bound26

theorem g59s36 : Slice false (raw 8) g59T 0x44444444000000004444444400000000444444440000000044444444 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g47Ok).1 bound47

theorem g59s37 : Slice false (raw 8) g59T 0x44444444000000004444444400000000444444440000000044444444 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g48Ok).1 bound48

theorem g59s38 : Slice false (raw 8) g59T 0x4444444400000000444444440000000044444444000000004444444400000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g49Ok).1 bound49

theorem g59s39 : Slice false (raw 8) g59T 0x4444444400000000444444440000000044444444000000004444444400000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g50Ok).1 bound50

theorem g59s40 : Slice false (raw 8) g59T 0x22222222000000002222222200000000222222220000000022222222 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g49Ok).1 bound49

theorem g59s41 : Slice false (raw 8) g59T 0x22222222000000002222222200000000222222220000000022222222 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g50Ok).1 bound50

theorem g59s42 : Slice false (raw 8) g59T 0x2222222200000000222222220000000022222222000000002222222200000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g49Ok).1 bound49

theorem g59s43 : Slice false (raw 8) g59T 0x2222222200000000222222220000000022222222000000002222222200000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g50Ok).1 bound50

theorem g59s44 : Slice false (raw 8) g59T 0x50505050000000005050505000000000505050500000000050505050 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 true,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g47Ok).1 bound47

theorem g59s45 : Slice false (raw 8) g59T 0x50505050000000005050505000000000505050500000000050505050 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 true,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g48Ok).1 bound48

theorem g59s46 : Slice false (raw 8) g59T 0x5050505000000000505050500000000050505050000000005050505000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 true,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g49Ok).1 bound49

theorem g59s47 : Slice false (raw 8) g59T 0x5050505000000000505050500000000050505050000000005050505000000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 true,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g50Ok).1 bound50

theorem g59s48 : Slice false (raw 8) g59T 0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 true,setBitRow 2 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g50Ok).1 bound50

theorem g59s49 : Slice false (raw 8) g59T 0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a00000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 true,setBitRow 2 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g49Ok).1 bound49

theorem g59s50 : Slice false (raw 8) g59T 0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a00000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 true,setBitRow 2 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g50Ok).1 bound50

theorem g59s51 : Slice false (raw 8) g59T 0x550055000000000055005500000000005500550000000000550055 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 false,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g51Ok).1 bound51

theorem g59s52 : Slice false (raw 8) g59T 0x550055000000000055005500000000005500550000000000550055 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 false,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g52Ok).1 bound52

theorem g59s53 : Slice false (raw 8) g59T 0x55005500000000005500550000000000550055000000000055005500000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 false,setBitRow 3 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g51Ok).1 bound51

theorem g59s54 : Slice false (raw 8) g59T 0x55005500000000005500550000000000550055000000000055005500000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 false,setBitRow 3 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g52Ok).1 bound52

theorem g59s55 : Slice false (raw 8) g59T 0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 true,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g49Ok).1 bound49

theorem g59s56 : Slice false (raw 8) g59T 0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 true,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g50Ok).1 bound50

theorem g59s57 : Slice false (raw 8) g59T 0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa00000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 true,setBitRow 3 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g49Ok).1 bound49

theorem g59s58 : Slice false (raw 8) g59T 0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa00000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,exchangeRow 0 1,setBitRow 0 true,setBitRow 3 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g50Ok).1 bound50

theorem g59s59 : Slice false (raw 8) g59T 0x3030303000000000303030300000000030303030000000003030303000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,setBitRow 1 false,setBitRow 2 true,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g49Ok).1 bound49

theorem g59s60 : Slice false (raw 8) g59T 0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c00000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 3,setBitRow 1 true,setBitRow 2 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g49Ok).1 bound49

theorem g59s61 : Slice false (raw 8) g59T 0x330033000000000033003300000000003300330000000000330033 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,setBitRow 1 false,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g52Ok).1 bound52

theorem g59s62 : Slice false (raw 8) g59T 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,setBitRow 1 true,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g50Ok).1 bound50

theorem g59s63 : Slice false (raw 8) g59T 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc00000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,setBitRow 1 true,setBitRow 3 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g49Ok).1 bound49

theorem g59s64 : Slice false (raw 8) g59T 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000cc00cc00000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,exchangeRow 1 2,setBitRow 1 true,setBitRow 3 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g50Ok).1 bound50

theorem g59s65 : Slice false (raw 8) g59T 0xf000f00000000000f000f00000000000f000f00000000000f000f 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,setBitRow 2 false,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g52Ok).1 bound52

theorem g59s66 : Slice false (raw 8) g59T 0xf000f00000000000f000f00000000000f000f00000000000f000f0 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,exchangeRow 2 4,setBitRow 2 true,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g50Ok).1 bound50

theorem g59s67 : Slice false (raw 8) g59T 0xff00000000000000ff00000000000000ff00000000000000ff 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,setBitRow 3 false,setBitRow 4 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g53Ok).1 bound53

theorem g59s68 : Slice false (raw 8) g59T 0xff00000000000000ff00000000000000ff00000000000000ff 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,setBitRow 3 false,setBitRow 4 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g54Ok).1 bound54

theorem g59s69 : Slice false (raw 8) g59T 0xff00000000000000ff00000000000000ff00000000000000ff00000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,setBitRow 3 false,setBitRow 4 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g53Ok).1 bound53

theorem g59s70 : Slice false (raw 8) g59T 0xff00000000000000ff00000000000000ff00000000000000ff00000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,setBitRow 3 false,setBitRow 4 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g54Ok).1 bound54

theorem g59s71 : Slice false (raw 8) g59T 0xff00000000000000ff00000000000000ff00000000000000ff0000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,setBitRow 3 false,setBitRow 4 true,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g55Ok).1 bound55

theorem g59s72 : Slice false (raw 8) g59T 0xff00000000000000ff00000000000000ff00000000000000ff000000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,setBitRow 3 false,setBitRow 4 true,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g56Ok).1 bound56

theorem g59s73 : Slice false (raw 8) g59T 0xff00000000000000ff00000000000000ff00000000000000ff000000000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 6,setBitRow 3 false,setBitRow 4 true,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g55Ok).1 bound55

theorem g59s74 : Slice false (raw 8) g59T 0xff00ff00000000000000000000000000ff00ff 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g53Ok).1 bound53

theorem g59s75 : Slice false (raw 8) g59T 0xff00ff00000000000000000000000000ff00ff 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g54Ok).1 bound54

theorem g59s76 : Slice false (raw 8) g59T 0xff00ff00000000000000000000000000ff00ff0000000000000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g55Ok).1 bound55

theorem g59s77 : Slice false (raw 8) g59T 0xff00ff00000000000000000000000000ff00ff00000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g53Ok).1 bound53

theorem g59s78 : Slice false (raw 8) g59T 0xff00ff00000000000000000000000000ff00ff00000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g54Ok).1 bound54

theorem g59s79 : Slice false (raw 8) g59T 0xff00ff00000000000000000000000000ff00ff000000000000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g56Ok).1 bound56

theorem g59s80 : Slice false (raw 8) g59T 0xff00ff00000000000000000000000000ff00ff000000000000000000000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g55Ok).1 bound55

theorem g59s81 : Slice false (raw 8) g59T 0xff00ff0000000000ff00ff 5 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g53Ok).1 bound53

theorem g59s82 : Slice false (raw 8) g59T 0xff00ff0000000000ff00ff 6 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g54Ok).1 bound54

theorem g59s83 : Slice false (raw 8) g59T 0xff00ff0000000000ff00ff00000000000000000000000000000000 6 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g55Ok).1 bound55

theorem g59s84 : Slice false (raw 8) g59T 0xff00ff0000000000ff00ff00000000 5 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g53Ok).1 bound53

theorem g59s85 : Slice false (raw 8) g59T 0xff00ff0000000000ff00ff00000000 6 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g54Ok).1 bound54

theorem g59s86 : Slice false (raw 8) g59T 0xff00ff0000000000ff00ff0000000000000000000000000000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g56Ok).1 bound56

theorem g59s87 : Slice false (raw 8) g59T 0xff00ff0000000000ff00ff0000000000000000000000000000000000000000 6 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 4,setBitRow 3 false,setBitRow 5 true,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g55Ok).1 bound55

theorem g59s88 : Slice false (raw 8) g59T 0xffff0000000000000000000000000000ffff000000000000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,setBitRow 4 false,setBitRow 5 true,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g56Ok).1 bound56

theorem g59s89 : Slice false (raw 8) g59T 0xffff0000000000000000000000000000ffff000000000000000000000000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,setBitRow 4 false,setBitRow 5 true,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g55Ok).1 bound55

theorem g59s90 : Slice false (raw 8) g59T 0xffff0000000000000000000000000000ffff0000 6 :=
  slice_correct (ms:=[exchangeRow 4 7,setBitRow 4 true,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g55Ok).1 bound55

theorem g59s91 : Slice false (raw 8) g59T 0xffff0000000000000000000000000000ffff000000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,setBitRow 4 true,setBitRow 5 true,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g56Ok).1 bound56

theorem g59s92 : Slice false (raw 8) g59T 0xffff000000000000ffff0000000000000000000000000000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 6,setBitRow 4 false,setBitRow 5 true,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g56Ok).1 bound56

theorem g59s93 : Slice false (raw 8) g59T 0xffff000000000000ffff0000000000000000000000000000000000000000 6 :=
  slice_correct (ms:=[exchangeRow 4 6,setBitRow 4 false,setBitRow 5 true,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g55Ok).1 bound55

theorem g59s94 : Slice false (raw 8) g59T 0xffff000000000000ffff0000 6 :=
  slice_correct (ms:=[exchangeRow 4 6,setBitRow 4 true,setBitRow 5 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g55Ok).1 bound55

theorem g59s95 : Slice false (raw 8) g59T 0xffff000000000000ffff000000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 6,setBitRow 4 true,setBitRow 5 true,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g56Ok).1 bound56

theorem g59s96 : Slice false (raw 8) g59T 0xffffffff0000000000000000000000000000000000000000 5 :=
  slice_correct (ms:=[setBitRow 5 true,setBitRow 6 false,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g56Ok).1 bound56

theorem g59s97 : Slice false (raw 8) g59T 0xffffffff000000000000000000000000 5 :=
  slice_correct (ms:=[setBitRow 5 true,setBitRow 6 true,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g56Ok).1 bound56

theorem g59s98 : Slice false (raw 8) g59T 0x202020202020202020202020202020202020202020202020202020202020202 4 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 true,setBitRow 1 false,setBitRow 2 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g29Ok).1 bound29

theorem g59s99 : Slice false (raw 8) g59T 0x202020202020202020202020202020202020202020202020202020202020202 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 true,setBitRow 1 false,setBitRow 2 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g59s100 : Slice false (raw 8) g59T 0x44004400440044004400440044004400440044004400440044004400440044 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g59s101 : Slice false (raw 8) g59T 0x22002200220022002200220022002200220022002200220022002200220022 4 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g29Ok).1 bound29

theorem g59s102 : Slice false (raw 8) g59T 0x22002200220022002200220022002200220022002200220022002200220022 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 2,setBitRow 0 true,setBitRow 1 false,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g59s103 : Slice false (raw 8) g59T 0x11111111000000001111111100000000111111110000000011111111 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g28Ok).1 bound28

theorem g59s104 : Slice false (raw 8) g59T 0x1111111100000000111111110000000011111111000000001111111100000000 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g59s105 : Slice false (raw 8) g59T 0x444444444444444400000000000000004444444444444444 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 5,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g57Ok).1 bound57

theorem g59s106 : Slice false (raw 8) g59T 0x44444444444444444444444444444444 5 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 5,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 2,setBitRow 0 false,setBitRow 1 true,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g57Ok).1 bound57

theorem g59s107 : Slice false (raw 8) g59T 0x50005000500050005000500050005000500050005000500050005000500050 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 true,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g59s108 : Slice false (raw 8) g59T 0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a 4 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 1,setBitRow 0 true,setBitRow 2 false,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g29Ok).1 bound29

theorem g59s109 : Slice false (raw 8) g59T 0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 1,setBitRow 0 true,setBitRow 2 false,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g59s110 : Slice false (raw 8) g59T 0x5050505000000000505050500000000050505050000000005050505 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g28Ok).1 bound28

theorem g59s111 : Slice false (raw 8) g59T 0x505050500000000050505050000000005050505000000000505050500000000 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g59s112 : Slice false (raw 8) g59T 0x505050505050505000000000000000005050505050505050 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 5,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 true,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g57Ok).1 bound57

theorem g59s113 : Slice false (raw 8) g59T 0x50505050505050505050505050505050 5 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 5,exchangeRow 2 4,exchangeRow 1 3,exchangeRow 0 1,setBitRow 0 false,setBitRow 2 true,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g57Ok).1 bound57

theorem g59s114 : Slice false (raw 8) g59T 0x30003000300030003000300030003000300030003000300030003000300030 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,setBitRow 1 false,setBitRow 2 true,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g59s115 : Slice false (raw 8) g59T 0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,setBitRow 1 true,setBitRow 2 false,setBitRow 3 false,setBitRow 5 false]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g59s116 : Slice false (raw 8) g59T 0x303030300000000030303030000000003030303000000000303030300000000 5 :=
  slice_correct (ms:=[exchangeRow 3 7,exchangeRow 2 6,exchangeRow 1 4,exchangeRow 0 3,setBitRow 0 false,setBitRow 1 false,setBitRow 2 false,setBitRow 5 true]) (by decide +kernel) (by decide +kernel) (basic_data g30Ok).1 bound30

theorem g59s117 : Slice false (raw 8) g59T 0x333300003333000000000000000000003333000033330000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 5,exchangeRow 2 3,exchangeRow 1 2,setBitRow 1 false,setBitRow 4 false,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g58Ok).1 bound58

theorem g59s118 : Slice false (raw 8) g59T 0x333300003333000033330000333300000000000000000000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 5,exchangeRow 2 3,exchangeRow 1 2,setBitRow 1 false,setBitRow 4 false,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g58Ok).1 bound58

theorem g59s119 : Slice false (raw 8) g59T 0xf0f00000f0f000000000000000000000f0f00000f0f0000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 7,exchangeRow 3 5,exchangeRow 2 3,setBitRow 2 false,setBitRow 4 false,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g58Ok).1 bound58

theorem g59s120 : Slice false (raw 8) g59T 0xf0f00000f0f00000f0f00000f0f00000000000000000000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 4 6,exchangeRow 3 5,exchangeRow 2 3,setBitRow 2 false,setBitRow 4 false,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g58Ok).1 bound58

theorem g59s121 : Slice false (raw 8) g59T 0xff000000ff0000000000000000000000ff000000ff0000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 3 7,setBitRow 3 false,setBitRow 4 false,setBitRow 5 false,setBitRow 6 true]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g59s122 : Slice false (raw 8) g59T 0xff000000ff0000000000000000000000ff000000ff0000 4 :=
  slice_correct (ms:=[exchangeRow 3 7,setBitRow 3 false,setBitRow 4 true,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g31Ok).1 bound31

theorem g59s123 : Slice false (raw 8) g59T 0xff000000ff0000000000000000000000ff000000ff0000 5 :=
  slice_correct (ms:=[exchangeRow 3 7,setBitRow 3 false,setBitRow 4 true,setBitRow 5 false,setBitRow 6 false]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g59s124 : Slice false (raw 8) g59T 0xff000000ff000000ff000000ff00000000000000000000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 3 6,setBitRow 3 false,setBitRow 4 false,setBitRow 5 false,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g59s125 : Slice false (raw 8) g59T 0xff000000ff000000ff000000ff0000 4 :=
  slice_correct (ms:=[exchangeRow 3 6,setBitRow 3 false,setBitRow 4 true,setBitRow 5 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g31Ok).1 bound31

theorem g59s126 : Slice false (raw 8) g59T 0xff000000ff000000ff000000ff0000 5 :=
  slice_correct (ms:=[exchangeRow 3 6,setBitRow 3 false,setBitRow 4 true,setBitRow 5 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g59s127 : Slice false (raw 8) g59T 0xff00ff00ff00ff00000000000000000000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 6 false,setBitRow 7 true]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g59s128 : Slice false (raw 8) g59T 0xff00ff00ff00ff0000000000000000 5 :=
  slice_correct (ms:=[exchangeRow 3 4,setBitRow 3 false,setBitRow 5 false,setBitRow 6 true,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g59s129 : Slice false (raw 8) g59T 0xffff0000000000000000000000000000ffff 5 :=
  slice_correct (ms:=[setBitRow 4 false,setBitRow 5 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g39Ok).1 bound39

theorem g59s130 : Slice false (raw 8) g59T 0xffff0000000000000000000000000000ffff00000000 5 :=
  slice_correct (ms:=[setBitRow 4 false,setBitRow 5 true,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g59s131 : Slice false (raw 8) g59T 0xffff000000000000ffff 5 :=
  slice_correct (ms:=[setBitRow 4 false,setBitRow 5 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g39Ok).1 bound39

theorem g59s132 : Slice false (raw 8) g59T 0xffff000000000000ffff00000000 5 :=
  slice_correct (ms:=[setBitRow 4 false,setBitRow 5 true,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g59s133 : Slice false (raw 8) g59T 0xffff0000ffff0000 4 :=
  slice_correct (ms:=[setBitRow 4 true,setBitRow 5 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g31Ok).1 bound31

theorem g59s134 : Slice false (raw 8) g59T 0xffff0000ffff0000 5 :=
  slice_correct (ms:=[setBitRow 4 true,setBitRow 5 false,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

theorem g59s135 : Slice false (raw 8) g59T 0xffffffff00000000 5 :=
  slice_correct (ms:=[setBitRow 4 false,setBitRow 5 true,setBitRow 6 false,setBitRow 7 false]) (by decide +kernel) (by decide +kernel) (basic_data g32Ok).1 bound32

def g59Cuts (k i : Nat) : Rule false g59T k := (if i<110 then (if i<55 then (if i<27 then (if i<13 then (if i<6 then (if i<3 then (if i<1 then (cutRule k g59s0 []) else (if i<2 then (cutRule k g59s0 [(0,g59v1,g59v13)]) else (cutRule k g59s0 [(1,g59v1,g59v2)]))) else (if i<4 then (cutRule k g59s0 [(1,g59v1,g59v2),(1,g59v13,g59v23)]) else (if i<5 then (cutRule k g59s0 [(1,g59v1,g59v2),(1,g59v13,g59v29)]) else (cutRule k g59s0 [(1,g59v1,g59v4)])))) else (if i<9 then (if i<7 then (cutRule k g59s0 [(1,g59v1,g59v4),(1,g59v13,g59v23)]) else (if i<8 then (cutRule k g59s0 [(1,g59v1,g59v4),(1,g59v13,g59v29)]) else (cutRule k g59s0 [(1,g59v1,g59v13)]))) else (if i<11 then (if i<10 then (cutRule k g59s0 [(1,g59v1,g59v23)]) else (cutRule k g59s0 [(1,g59v1,g59v29)])) else (if i<12 then (cutRule k g59s0 [(1,g59v2,g59v13)]) else (cutRule k g59s0 [(1,g59v2,g59v23)]))))) else (if i<20 then (if i<16 then (if i<14 then (cutRule k g59s0 [(1,g59v2,g59v29)]) else (if i<15 then (cutRule k g59s0 [(1,g59v4,g59v13)]) else (cutRule k g59s0 [(1,g59v4,g59v23)]))) else (if i<18 then (if i<17 then (cutRule k g59s0 [(1,g59v4,g59v29)]) else (cutRule k g59s0 [(1,g59v13,g59v23)])) else (if i<19 then (cutRule k g59s0 [(1,g59v13,g59v29)]) else (cutRule k g59s1 [])))) else (if i<23 then (if i<21 then (cutRule k g59s1 [(1,g59v8,g59v13)]) else (if i<22 then (cutRule k g59s1 [(1,g59v8,g59v23)]) else (cutRule k g59s1 [(1,g59v8,g59v29)]))) else (if i<25 then (if i<24 then (cutRule k g59s1 [(1,g59v13,g59v19)]) else (cutRule k g59s1 [(1,g59v13,g59v23)])) else (if i<26 then (cutRule k g59s1 [(1,g59v13,g59v29)]) else (cutRule k g59s1 [(1,g59v23,g59v29)])))))) else (if i<41 then (if i<34 then (if i<30 then (if i<28 then (cutRule k g59s2 []) else (if i<29 then (cutRule k g59s2 [(1,g59v8,g59v13)]) else (cutRule k g59s2 [(1,g59v8,g59v23)]))) else (if i<32 then (if i<31 then (cutRule k g59s2 [(1,g59v8,g59v29)]) else (cutRule k g59s2 [(1,g59v13,g59v19)])) else (if i<33 then (cutRule k g59s2 [(1,g59v13,g59v23)]) else (cutRule k g59s2 [(1,g59v13,g59v29)])))) else (if i<37 then (if i<35 then (cutRule k g59s2 [(1,g59v23,g59v29)]) else (if i<36 then (cutRule k g59s3 []) else (cutRule k g59s3 [(1,g59v1,g59v2)]))) else (if i<39 then (if i<38 then (cutRule k g59s3 [(1,g59v1,g59v4)]) else (cutRule k g59s3 [(1,g59v1,g59v8)])) else (if i<40 then (cutRule k g59s3 [(1,g59v1,g59v19)]) else (cutRule k g59s3 [(1,g59v2,g59v4)]))))) else (if i<48 then (if i<44 then (if i<42 then (cutRule k g59s3 [(1,g59v2,g59v8)]) else (if i<43 then (cutRule k g59s3 [(1,g59v4,g59v8)]) else (cutRule k g59s4 []))) else (if i<46 then (if i<45 then (cutRule k g59s4 [(1,g59v1,g59v2)]) else (cutRule k g59s4 [(1,g59v1,g59v4)])) else (if i<47 then (cutRule k g59s4 [(1,g59v1,g59v8)]) else (cutRule k g59s4 [(1,g59v1,g59v19)])))) else (if i<51 then (if i<49 then (cutRule k g59s4 [(1,g59v2,g59v4)]) else (if i<50 then (cutRule k g59s4 [(1,g59v2,g59v8)]) else (cutRule k g59s4 [(1,g59v4,g59v8)]))) else (if i<53 then (if i<52 then (cutRule k g59s5 []) else (cutRule k g59s6 [])) else (if i<54 then (cutRule k g59s7 []) else (cutRule k g59s8 []))))))) else (if i<82 then (if i<68 then (if i<61 then (if i<58 then (if i<56 then (cutRule k g59s9 []) else (if i<57 then (cutRule k g59s10 []) else (cutRule k g59s10 [(1,g59v13,g59v23)]))) else (if i<59 then (cutRule k g59s10 [(1,g59v13,g59v29)]) else (if i<60 then (cutRule k g59s10 [(1,g59v23,g59v29)]) else (cutRule k g59s11 [])))) else (if i<64 then (if i<62 then (cutRule k g59s11 [(1,g59v13,g59v23)]) else (if i<63 then (cutRule k g59s11 [(1,g59v13,g59v29)]) else (cutRule k g59s11 [(1,g59v23,g59v29)]))) else (if i<66 then (if i<65 then (cutRule k g59s12 []) else (cutRule k g59s12 [(1,g59v1,g59v2)])) else (if i<67 then (cutRule k g59s12 [(1,g59v1,g59v4)]) else (cutRule k g59s12 [(1,g59v2,g59v4)]))))) else (if i<75 then (if i<71 then (if i<69 then (cutRule k g59s13 []) else (if i<70 then (cutRule k g59s13 [(1,g59v1,g59v2)]) else (cutRule k g59s13 [(1,g59v1,g59v4)]))) else (if i<73 then (if i<72 then (cutRule k g59s13 [(1,g59v2,g59v4)]) else (cutRule k g59s14 [])) else (if i<74 then (cutRule k g59s15 []) else (cutRule k g59s15 [(1,g59v8,g59v13)])))) else (if i<78 then (if i<76 then (cutRule k g59s15 [(1,g59v8,g59v23)]) else (if i<77 then (cutRule k g59s15 [(1,g59v8,g59v29)]) else (cutRule k g59s15 [(1,g59v13,g59v23)]))) else (if i<80 then (if i<79 then (cutRule k g59s15 [(1,g59v13,g59v29)]) else (cutRule k g59s15 [(1,g59v23,g59v29)])) else (if i<81 then (cutRule k g59s16 []) else (cutRule k g59s17 [])))))) else (if i<96 then (if i<89 then (if i<85 then (if i<83 then (cutRule k g59s18 []) else (if i<84 then (cutRule k g59s18 [(1,g59v13,g59v23)]) else (cutRule k g59s18 [(1,g59v13,g59v29)]))) else (if i<87 then (if i<86 then (cutRule k g59s18 [(1,g59v23,g59v29)]) else (cutRule k g59s19 [])) else (if i<88 then (cutRule k g59s20 []) else (cutRule k g59s21 [])))) else (if i<92 then (if i<90 then (cutRule k g59s21 [(1,g59v13,g59v23)]) else (if i<91 then (cutRule k g59s21 [(1,g59v13,g59v29)]) else (cutRule k g59s21 [(1,g59v23,g59v29)]))) else (if i<94 then (if i<93 then (cutRule k g59s22 []) else (cutRule k g59s23 [])) else (if i<95 then (cutRule k g59s24 []) else (cutRule k g59s24 [(1,g59v13,g59v23)]))))) else (if i<103 then (if i<99 then (if i<97 then (cutRule k g59s24 [(1,g59v13,g59v29)]) else (if i<98 then (cutRule k g59s24 [(1,g59v23,g59v29)]) else (cutRule k g59s25 []))) else (if i<101 then (if i<100 then (cutRule k g59s26 []) else (cutRule k g59s26 [(1,g59v1,g59v2)])) else (if i<102 then (cutRule k g59s26 [(1,g59v1,g59v4)]) else (cutRule k g59s26 [(1,g59v1,g59v8)])))) else (if i<106 then (if i<104 then (cutRule k g59s26 [(1,g59v2,g59v4)]) else (if i<105 then (cutRule k g59s27 []) else (cutRule k g59s28 []))) else (if i<108 then (if i<107 then (cutRule k g59s29 []) else (cutRule k g59s29 [(1,g59v1,g59v2)])) else (if i<109 then (cutRule k g59s29 [(1,g59v1,g59v4)]) else (cutRule k g59s29 [(1,g59v2,g59v4)])))))))) else (if i<165 then (if i<137 then (if i<123 then (if i<116 then (if i<113 then (if i<111 then (cutRule k g59s30 []) else (if i<112 then (cutRule k g59s31 []) else (cutRule k g59s32 []))) else (if i<114 then (cutRule k g59s32 [(1,g59v1,g59v2)]) else (if i<115 then (cutRule k g59s32 [(1,g59v1,g59v4)]) else (cutRule k g59s32 [(1,g59v2,g59v4)])))) else (if i<119 then (if i<117 then (cutRule k g59s33 []) else (if i<118 then (cutRule k g59s34 []) else (cutRule k g59s35 []))) else (if i<121 then (if i<120 then (cutRule k g59s35 [(1,g59v1,g59v2)]) else (cutRule k g59s35 [(1,g59v1,g59v4)])) else (if i<122 then (cutRule k g59s36 []) else (cutRule k g59s37 []))))) else (if i<130 then (if i<126 then (if i<124 then (cutRule k g59s38 []) else (if i<125 then (cutRule k g59s39 []) else (cutRule k g59s40 []))) else (if i<128 then (if i<127 then (cutRule k g59s41 []) else (cutRule k g59s42 [])) else (if i<129 then (cutRule k g59s43 []) else (cutRule k g59s44 [])))) else (if i<133 then (if i<131 then (cutRule k g59s45 []) else (if i<132 then (cutRule k g59s46 []) else (cutRule k g59s47 []))) else (if i<135 then (if i<134 then (cutRule k g59s48 []) else (cutRule k g59s49 [])) else (if i<136 then (cutRule k g59s50 []) else (cutRule k g59s51 [])))))) else (if i<151 then (if i<144 then (if i<140 then (if i<138 then (cutRule k g59s52 []) else (if i<139 then (cutRule k g59s53 []) else (cutRule k g59s54 []))) else (if i<142 then (if i<141 then (cutRule k g59s55 []) else (cutRule k g59s56 [])) else (if i<143 then (cutRule k g59s57 []) else (cutRule k g59s58 [])))) else (if i<147 then (if i<145 then (cutRule k g59s59 []) else (if i<146 then (cutRule k g59s60 []) else (cutRule k g59s61 []))) else (if i<149 then (if i<148 then (cutRule k g59s62 []) else (cutRule k g59s63 [])) else (if i<150 then (cutRule k g59s64 []) else (cutRule k g59s65 []))))) else (if i<158 then (if i<154 then (if i<152 then (cutRule k g59s66 []) else (if i<153 then (cutRule k g59s67 []) else (cutRule k g59s68 []))) else (if i<156 then (if i<155 then (cutRule k g59s69 []) else (cutRule k g59s70 [])) else (if i<157 then (cutRule k g59s71 []) else (cutRule k g59s72 [])))) else (if i<161 then (if i<159 then (cutRule k g59s73 []) else (if i<160 then (cutRule k g59s74 []) else (cutRule k g59s75 []))) else (if i<163 then (if i<162 then (cutRule k g59s76 []) else (cutRule k g59s77 [])) else (if i<164 then (cutRule k g59s78 []) else (cutRule k g59s79 []))))))) else (if i<193 then (if i<179 then (if i<172 then (if i<168 then (if i<166 then (cutRule k g59s80 []) else (if i<167 then (cutRule k g59s81 []) else (cutRule k g59s82 []))) else (if i<170 then (if i<169 then (cutRule k g59s83 []) else (cutRule k g59s84 [])) else (if i<171 then (cutRule k g59s85 []) else (cutRule k g59s86 [])))) else (if i<175 then (if i<173 then (cutRule k g59s87 []) else (if i<174 then (cutRule k g59s88 []) else (cutRule k g59s89 []))) else (if i<177 then (if i<176 then (cutRule k g59s90 []) else (cutRule k g59s91 [])) else (if i<178 then (cutRule k g59s92 []) else (cutRule k g59s93 []))))) else (if i<186 then (if i<182 then (if i<180 then (cutRule k g59s94 []) else (if i<181 then (cutRule k g59s95 []) else (cutRule k g59s96 []))) else (if i<184 then (if i<183 then (cutRule k g59s97 []) else (cutRule k g59s98 [])) else (if i<185 then (cutRule k g59s99 []) else (cutRule k g59s100 [])))) else (if i<189 then (if i<187 then (cutRule k g59s101 []) else (if i<188 then (cutRule k g59s102 []) else (cutRule k g59s103 []))) else (if i<191 then (if i<190 then (cutRule k g59s104 []) else (cutRule k g59s105 [])) else (if i<192 then (cutRule k g59s106 []) else (cutRule k g59s107 [])))))) else (if i<207 then (if i<200 then (if i<196 then (if i<194 then (cutRule k g59s108 []) else (if i<195 then (cutRule k g59s109 []) else (cutRule k g59s110 []))) else (if i<198 then (if i<197 then (cutRule k g59s111 []) else (cutRule k g59s112 [])) else (if i<199 then (cutRule k g59s113 []) else (cutRule k g59s114 [])))) else (if i<203 then (if i<201 then (cutRule k g59s115 []) else (if i<202 then (cutRule k g59s116 []) else (cutRule k g59s117 []))) else (if i<205 then (if i<204 then (cutRule k g59s118 []) else (cutRule k g59s119 [])) else (if i<206 then (cutRule k g59s120 []) else (cutRule k g59s121 []))))) else (if i<214 then (if i<210 then (if i<208 then (cutRule k g59s122 []) else (if i<209 then (cutRule k g59s123 []) else (cutRule k g59s124 []))) else (if i<212 then (if i<211 then (cutRule k g59s125 []) else (cutRule k g59s126 [])) else (if i<213 then (cutRule k g59s127 []) else (cutRule k g59s128 [])))) else (if i<217 then (if i<215 then (cutRule k g59s129 []) else (if i<216 then (cutRule k g59s130 []) else (cutRule k g59s131 []))) else (if i<219 then (if i<218 then (cutRule k g59s132 []) else (cutRule k g59s133 [])) else (if i<220 then (cutRule k g59s134 []) else (cutRule k g59s135 [])))))))))

def g59n0w : List Sig := [g59v1,g59v2,g59v4,g59v7,g59v13,g59v14,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n0 : Impossible false g59T 9 g59n0w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 8) (fun i => failRule false g59T 8))) (idx:=(fun j => bitsAt 0x4036900d34034900d04033d00c1402ed00ba402e500b8402dcc08a3012890a1240d09032240c45061140d05032140c42831060d01832060c409a1025840931018d00632016840561014d0053100e84036100cc80331 18 (bitsAt 0x9596998554510000000000006d57158d99190000000000008556158d95140000000000008df30c79528a0000000000007171c76d51040000000000007160c36d50000000000000006d57158d50410000000000006d171185a89a00000000000085151185a61800000000000085f2cb79128a0000000000007131866d11040000000000007120826d10000000000000006d17118510410000000000000000000000000000000000006dc28a79d4100000000000006dc1046dc2080000000000006dc0006dc24900000000000000000000000000000000000085f28a79428a00000000000085c1046d410400000000000085c0006d400000000000000000000071404100000000000080f7cf6ca10400000000000078e7ce6ca0000000000000006ca70a78d0410000000000006c82486c40000000000000006c41446c80410000000000006c00406c9145 6 j))) (by decide +kernel)

def g59n1w : List Sig := [g59v1,g59v2,g59v3,g59v4,g59v8,g59v13,g59v17,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n1 : Impossible false g59T 10 g59n1w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d34034500d04033900bf402f900bd402f100bb402e500b84026900984025900934023d008e402350089401e90071401ad005740141004840070c08a301289034240c89031141285034140c850310a228284c0a128188a06130184a060d01832060c4094a024c4064a018c805a101584053100e84038a00d84034a00cc80331 18 (bitsAt 0x1d79d01a59600000000000001a55501a4d300000000000001a8da01dd1d00000000000001a49201d41000000000000001d8dd01a2cb00000000000001c20801a18600000000000001adda01ae1a00000000000001b14501a00000000000000001a10401a0410000000000000164d30164d300000000000001691601ecde00000000000001641001e41000000000000001e91e0162cb0000000000000181c7016186000000000000016d56016d960000000000000170c3016000000000000000016082016041000000000000013c93027c65000000000000029a290134100000000000000132cb02f2cb000000000000014186013186000000000000013b53013b1300000000000001300001300000000000000003004101304100000000000000000000000000000000000000000000000000000000000002118602e18600000000000002eda2031d6000000000000002f00002e00000000000000002e04102f0410000000000000000000192cb000000000000011186010186000000000000010d90010d5000000000000001000001000000000000000003004101004100000000000000f28a00b18600000000000000b9cb00dd4d00000000000000e9ce00b00000000000000000b08200d0410000000000000069c6027adf000000000000009a890060000000000000000069c600904100000000000000000000000000000000000000000000000000000000000000000002630c 6 j))) (by decide +kernel)

def g59n2w : List Sig := [g59v1,g59v2,g59v3,g59v4,g59v8,g59v13,g59v19,g59v23,g59v27,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n2 : Impossible false g59T 10 g59n2w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d54035100d04033900cc402fd00bd402f100bb402e500b840289009f4024d008f40239008d40225007a401c5006b40191005740141004840074c08c30228c04a242289034240c8903114184504a0a22828640a18828610a130284a06228184c06128096102528064a018c805a101584053100e84038a00d84034a00cc80331 18 (bitsAt 0x1c91c018cd800000000000001c75c0189580000000000000185550184100000000000000183cf01c34d00000000000001c91c01830c00000000000001a208018186000000000000018dd8018e18000000000000019145018000000000000000018104018041000000000000000000000000000000000000032410031a2600000000000002534d0236db0000000000000000000000000000000000000211c702e18600000000000002ed62031da000000000000002f0c302e00000000000000002e08202f04100000000000002941001d41000000000000002534d01d34d00000000000000000001d30c00000000000001e1c701d18600000000000001dd5d01dd9d00000000000001d0c301d00000000000000003008201d04100000000000002a5d701034d00000000000001030c02f30c000000000000011186010186000000000000010b50010b1000000000000001000001000000000000000003004101004100000000000000d94d01630c00000000000000e18600d18600000000000000dd8d00dd4d00000000000000d00000d00000000000000001704100d04100000000000001428a00c18600000000000000ca0c012d52000000000000013a1300c00000000000000000c082012041000000000000006a06028d1f000000000000009ac9006000000000000000006a060090410000000000000000000000000000000000000000000000000000000000000000000272cb 6 j))) (by decide +kernel)

def g59n3w : List Sig := [g59v1,g59v2,g59v3,g59v4,g59v8,g59v13,g59v19,g59v23,g59v29,g59v33]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n3 : Impossible false g59T 10 g59n3w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d54035100d34034500cd402f900bd402f100bb402e500b8402a500a64024d008f40239008d40225007a401ad00644015d005040121001e30228c04c301285061141285034140c850310a29028a20a284288a0a130284a06228184c0612809a102528064a018c805a101584053100e84038a00d84034a00cc80331 18 (bitsAt 0x2375d03159600000000000003041002f9a400000000000002334d02265900000000000000000000000000000000000002020802c18600000000000002cce102fd1f00000000000002d14502c00000000000000002c08202d04100000000000001b75b02359600000000000002749201b4100000000000000233cf01b34d00000000000000000001b30c00000000000001c20801b18600000000000001bcdb01bd1b00000000000001b14501b00000000000000002e10401b04100000000000001641001641000000000000001634d01d34d00000000000001d8dd01630c0000000000000181c7016186000000000000016d96016d560000000000000170c301600000000000000001608201604100000000000002869a01034d00000000000001030c02d30c000000000000011186010186000000000000010ad0010a9000000000000001000001000000000000000002e04101004100000000000000d8cd01930c00000000000000e18600d18600000000000000dd0d00dccd00000000000000d00000d00000000000000001a04100d04100000000000001528a00c18600000000000000c98c013cd300000000000001499400c00000000000000000c082013041000000000000006986026c9e000000000000009a490060000000000000000069860090410000000000000000000000000000000000000000000000000000000000000000000252cb 6 j))) (by decide +kernel)

def g59n4w : List Sig := [g59v1,g59v2,g59v3,g59v4,g59v8,g59v13,g59v21,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n4 : Impossible false g59T 10 g59n4w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4034d00d0402f500b9402e1008f40239008740219008440201007f401f1007b401bd00694019100624007cc08a3012890a1240d09032240c45064141885061140d05032140c4288a0a130284a060d01832060c409a102584094a024c4064a018c805a101584053100e84038a00d84034a00cc80331 18 (bitsAt 0x8df81f8db555000000000000c5b5149df4920000000000008db79b8df618000000000000b9f38eb5b2cb000000000000a9d208adb18600000000000099b91bc5bcdb00000000000099c145c5b000000000000000a1b104c5b041000000000000c554929e04920000000000008d56158e079e000000000000ba034db552cb000000000000a971c7ad5186000000000000995955c55c950000000000009960c3c55000000000000000a15082c55041000000000000000000000000000000000000c522cbb702cb000000000000c53186ad2186000000000000c52c92c529d2000000000000c52000c52000000000000000c6f041c52041000000000000bae2cbb582cb000000000000a9a186ad8186000000000000998c98c58898000000000000999000c58000000000000000a18041c58041000000000000a9128aacb18600000000000098b9cbc4fc8f0000000000009909d0c4b000000000000000a0b082c4f0410000000000009869c6c71b210000000000009899c9c46000000000000000a06a46c49041000000000000000000000000000000000000000000000000000000000000000000c6730c 6 j))) (by decide +kernel)

def g59n5w : List Sig := [g59v1,g59v2,g59v3,g59v4,g59v8,g59v13,g59v19,g59v23,g59v28,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n5 : Impossible false g59T 10 g59n5w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4035d00d64034d00d04033900cc402fd00bd402f100b9402e10071401a1006440165005740141004d401210041400e5002c400810003301289034240c8903114184504a140d05032140c4288a0a130284a06130184a060d01832060c409a102584094a024c4064a018c805a101584053100e84038a00d84034a00cc80331 18 (bitsAt 0x1ca9c024c6200000000000001fa9f01c5d700000000000001c59601c51400000000000001ca9c01f49200000000000001f38e01c2cb00000000000001e20801c18600000000000001cadc01cd5c00000000000001d14501c00000000000000001c10401c04100000000000000000000000000000000000003051402f51400000000000000000000000000000000000002c2cb02e2cb00000000000002718602d18600000000000002dce802fda500000000000002e00002d00000000000000002d04102e04100000000000001751401751400000000000000000002a49200000000000002c34d0172cb0000000000000191c7017186000000000000017cd7017d170000000000000180c301700000000000000001708201704100000000000002a6db0144920000000000000142cb0202cb000000000000015186014186000000000000014dd4014d940000000000000140000140000000000000000260410140410000000000000122cb01a2cb000000000000013186012186000000000000012d12012cd200000000000001200001200000000000000001b04101204100000000000001128a00b18600000000000000ba4b00fccf000000000000010a5000b00000000000000000b08200f041000000000000006986023ca100000000000000998900600000000000000000698600904100000000000000000000000000000000000000000000000000000000000000000002630c 6 j))) (by decide +kernel)

def g59n6w : List Sig := [g59v1,g59v2,g59v3,g59v4,g59v8,g59v13,g59v19,g59v23,g59v29,g59v34]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n6 : Impossible false g59T 10 g59n6w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4036500d84034d00d14034100cd402f900bd402f100b9402e1006e401ad006440169005740141004e401210045400e900244008500043022890a1242289034240c89031140d05032140c4288a0a130284a06230188a060d01832060c409a102584094a024c4064a018c805a101584053100e84038a00d84034a00cc80331 18 (bitsAt 0x2a5d703192200000000000003059602f51400000000000000000000000000000000000002b2cb02e2cb00000000000002718602d18600000000000002dce802fda500000000000002e00002d00000000000000002d04102e04100000000000002a7df01a5d700000000000001a59601a51400000000000000000002a49200000000000002b38e01a2cb00000000000001c20801a18600000000000001ad1a01ad5a00000000000001b14501a00000000000000001a10401a041000000000000017514017514000000000000017a9701f49200000000000001f34d0172cb0000000000000191c7017186000000000000017b17017cd70000000000000180c301700000000000000001708201704100000000000002a79e0144920000000000000142cb0202cb000000000000015186014186000000000000014dd4014d940000000000000140000140000000000000000260410140410000000000000122cb01d2cb000000000000013186012186000000000000012cd2012d1200000000000001200001200000000000000001e04101204100000000000001128a00b18600000000000000ba4b00fccf000000000000010a5000b00000000000000000b08200f041000000000000006986023ca100000000000000998900600000000000000000698600904100000000000000000000000000000000000000000000000000000000000000000002630c 6 j))) (by decide +kernel)

def g59n7w : List Sig := [g59v1,g59v2,g59v3,g59v4,g59v8,g59v13,g59v19,g59v23,g59v29,g59v35]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n7 : Impossible false g59T 10 g59n7w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100dc4036d00d54035100d14033900cc402fd00be402f500bc402e500b8401dd0074401ad00644016d005740141004f40121003b40091002230284c08c30228c06130130c04a14184504a0a228284c0a128188a06130184a060d01832060c409a102584094a024c4064a018c805a101584053100e84038a00d84034a00cc80331 18 (bitsAt 0x2f55502e55500000000000002849202849200000000000002934d02d2cb0000000000000251c702c18600000000000002cce602ede300000000000002d0c302c00000000000000002c08202d041000000000000000000030c6100000000000001c5d701a55500000000000002851401a49200000000000001a38e01a2cb00000000000001b20801a18600000000000001ad1a01ad9a00000000000001a14501a00000000000000001c10401a04100000000000001f55501d55500000000000002849201d49200000000000001d34d01d2cb00000000000001e1c701d18600000000000001dcdd01dd5d00000000000001d0c301d00000000000000001f08201d0410000000000000286590154920000000000000152cb02b2cb000000000000016186015186000000000000015e15015a950000000000000150000150000000000000000240410150410000000000000122cb0182cb000000000000013186012186000000000000012dd2012cd200000000000001200001200000000000000001904101204100000000000001128a00b18600000000000000b9cb00fccf0000000000000109d000b00000000000000000b08200f041000000000000006906022ca000000000000000990900600000000000000000690600904100000000000000000000000000000000000000000000000000000000000000000002430c 6 j))) (by decide +kernel)

def g59n8w : List Sig := [g59v1,g59v2,g59v4,g59v5,g59v8,g59v13,g59v17,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n8 : Impossible false g59T 10 g59n8w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d34034500d04033900c64031500c44030d00c0402ed00b84026900984025d00924023d008e402350089401f90072401b1005640145004840050c08a301289034240c89031141285034140c850310a228284c0a128188a06130184a060d01832060c4094c024c4064c018d005a1016300561015300534014c403a100d840331 18 (bitsAt 0x1d79d01a59600000000000001a55501a4d300000000000001a8da01dd1d00000000000001a49201d41000000000000001d8dd01a2cb00000000000001adda01ae1a00000000000001c20801a0c300000000000001b08201a00000000000000001a1c701a1040000000000000164d30164d300000000000001691601ecde00000000000001641001e41000000000000001e91e0162cb000000000000016d56016d960000000000000181860160c3000000000000017041016000000000000000016145016104000000000000013c93027c65000000000000029a290134100000000000000132cb02f2cb000000000000014b54013b130000000000000140c30130c300000000000001300001300000000000000002f10401310400000000000000000000000000000000000000000000000000000000000002eda1031d600000000000000300c302e0c300000000000002200002e00000000000000002e1040301040000000000000000000192cb000000000000011d91010d500000000000000110c30100c300000000000001000001000000000000000002f10401010400000000000000b9cb00dd4d00000000000000f9cf00b0c300000000000000e28a00b00000000000000000b14500d10400000000000000000000000000000000000002700002a9df00000000000000000000000000000000000002b24900300000000000000000000002630c0000000000000009c0009104 6 j))) (by decide +kernel)

def g59n9w : List Sig := [g59v1,g59v2,g59v4,g59v5,g59v8,g59v13,g59v19,g59v23,g59v27,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n9 : Impossible false g59T 10 g59n9w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d54035100d04033900ca4031900c44030d00c0402ed00b840289009f4025d008f40239008d40225007e401c9006c40195005640145004840054c08c30228c04a242289034240c8903114184504a0a22828640a18828610a130284a06228184c06128096102530064c018d005a1016300561015300534014c403a100d840331 18 (bitsAt 0x1c91c018cd800000000000001c75c0189580000000000000185550184100000000000000183cf01c34d00000000000001c91c01830c000000000000018dd8018e1800000000000001a2080180c30000000000000190820180000000000000000181c7018104000000000000000000000000000000000000032410031a2600000000000002534d0236db00000000000000000000000000000000000002ed61031da000000000000003018602e0c300000000000002204102e00000000000000002e14503010400000000000002941001d41000000000000002534d01d34d00000000000000000001d30c00000000000001ed5e01dd9d00000000000001e18601d0c300000000000001d04101d00000000000000002f14501d10400000000000002a5d701034d00000000000001030c02f30c000000000000011b51010b100000000000000110c30100c300000000000001000001000000000000000002f10401010400000000000000d94d01630c00000000000000ed8e00dd4d00000000000000e0c300d0c300000000000000d00000d00000000000000001710400d10400000000000000ca0c012d52000000000000014a1400c0c300000000000001328a00c00000000000000000c145012104000000000000000000000000000000000000028000034a1f00000000000000000000000000000000000002b2490030000000000000000000000272cb000000000000000a00009104 6 j))) (by decide +kernel)

def g59n10w : List Sig := [g59v1,g59v2,g59v4,g59v5,g59v8,g59v13,g59v19,g59v23,g59v29,g59v33]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n10 : Impossible false g59T 10 g59n10w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d54035100d34034500cb4031500c44030d00c0402ed00b8402a500a64025d008f40239008d40225007e401b1006540159005140121001630228c04c301285061141285034140c850310a29028a20a284288a0a130284a06228184c0612809a102530064c018d005a1016300561015300534014c403a100d840331 18 (bitsAt 0x2375d03159600000000000003041002f9a400000000000002334d02265900000000000000000000000000000000000002cce002fd1f00000000000002e20802c0c300000000000002108202c00000000000000002c14502e10400000000000001b75b02359600000000000002749201b4100000000000000233cf01b34d00000000000000000001b30c00000000000001ccdc01bd1b00000000000001c20801b0c300000000000001b08201b00000000000000002d1c701b10400000000000001641001641000000000000001634d01d34d00000000000001d8dd01630c000000000000016d96016d560000000000000181860160c300000000000001704101600000000000000001614501610400000000000002869a01034d00000000000001030c02d30c000000000000011ad1010a900000000000000110c30100c300000000000001000001000000000000000002d10401010400000000000000d8cd01930c00000000000000ed0e00dccd00000000000000e0c300d0c300000000000000d00000d00000000000000001a10400d10400000000000000c98c013cd300000000000001599500c0c300000000000001428a00c00000000000000000c14501310400000000000000000000000000000000000002600003299e0000000000000000000000000000000000000292490030000000000000000000000252cb000000000000000980009104 6 j))) (by decide +kernel)

def g59n11w : List Sig := [g59v1,g59v2,g59v4,g59v5,g59v8,g59v13,g59v21,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n11 : Impossible false g59T 10 g59n11w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4034d00d04031100bb402e1008f4023900844020d0080401fd007c401bd00694019500624005cc08a3012890a1240d09032240c45064141885061140d05032140c4288a0a130284a060d01832060c409a102584094c024c4064c018d005a1016300561015300534014c403a100d840331 18 (bitsAt 0x8df81f8db555000000000000bdb514a1f4920000000000008db79b8df618000000000000b1f38eadb2cb0000000000009db91bbdbc5b000000000000a5d208bdb0c300000000000099c0829db0000000000000009db1c7bdb104000000000000bd5492a204920000000000008d56158e079e000000000000b2034dad52cb0000000000009d5955bd5c15000000000000a57186bd50c30000000000009960419d50000000000000009d5145bd5104000000000000000000000000000000000000bd22cbaee2cb000000000000bd3c13bd2a12000000000000bd30c3bd20c3000000000000bd20009d2000000000000000bed104bd2104000000000000b2c2cbad82cb0000000000009d8c18bd8898000000000000a5a0c3bd80c30000000000009990009d80000000000000009d8104bd81040000000000009cba0bbcfc0f000000000000a51a91bcb0c300000000000099028a9cb0000000000000009cb145bcf1040000000000000000000000000000000000009e6000be8be1000000000000000000000000000000000000a66249bc3000000000000000000000be630c0000000000009c0a00bc9104 6 j))) (by decide +kernel)

def g59n12w : List Sig := [g59v1,g59v2,g59v4,g59v5,g59v8,g59v13,g59v19,g59v23,g59v28,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n12 : Impossible false g59T 10 g59n12w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d74035900d34034100ce4032900c64031100c34030100bb402e10072401a1006540159005340145004d401210042400f5002d400610006301289034240c8903114184504a140d05032140c4288a0a130284a06130184a060d01832060c409a102584094c024c4064c018d005a1016300561015300534014c403a100d840331 18 (bitsAt 0x1ca9c024ca200000000000001fa9f01c5d700000000000001c59601c51400000000000001ca9c01f49200000000000001f38e01c2cb00000000000001cadc01cd9c00000000000001e20801c0c300000000000001d08201c00000000000000001c1c701c10400000000000000000000000000000000000003151403051400000000000000000000000000000000000002c2cb02e2cb00000000000002dd27030de500000000000002f0c302d0c300000000000002900002d00000000000000002d10402f10400000000000001751401751400000000000000000002a49200000000000002c34d0172cb000000000000017d17017d570000000000000191860170c300000000000001804101700000000000000001714501710400000000000002a6db0144920000000000000142cb0202cb000000000000015e15014dd40000000000000150c30140c30000000000000140000140000000000000000261040141040000000000000122cb01a2cb000000000000013d53012d120000000000000130c30120c300000000000001200001200000000000000001b10401210400000000000000ba0b00fd0f000000000000011a1100b0c300000000000001028a00b00000000000000000b14500f1040000000000000000000000000000000000000260000338e100000000000000000000000000000000000002624900300000000000000000000002630c000000000000000980009104 6 j))) (by decide +kernel)

def g59n13w : List Sig := [g59v1,g59v2,g59v4,g59v5,g59v8,g59v13,g59v19,g59v23,g59v29,g59v34]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n13 : Impossible false g59T 10 g59n13w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d94036100d34034500d04032d00c54031100c34030100bb402e1006e401b1006540159005440145004e401210046400f900254006500073022890a1242289034240c89031140d05032140c4288a0a130284a06230188a060d01832060c409a102584094c024c4064c018d005a1016300561015300534014c403a100d840331 18 (bitsAt 0x2a5d703292200000000000003159603051400000000000000000000000000000000000002b2cb02e2cb00000000000002dd27030de500000000000002f0c302d0c300000000000002900002d00000000000000002d10402f10400000000000002a7df01a5d700000000000001a59601a51400000000000000000002a49200000000000002b38e01a2cb00000000000001ad5a01ad9a00000000000001c20801a0c300000000000001b08201a00000000000000001a1c701a104000000000000017514017514000000000000017a9701f49200000000000001f34d0172cb000000000000017b17017d170000000000000191860170c300000000000001804101700000000000000001714501710400000000000002a79e0144920000000000000142cb0202cb000000000000015e15014dd40000000000000150c30140c30000000000000140000140000000000000000261040141040000000000000122cb01d2cb000000000000013d13012d520000000000000130c30120c300000000000001200001200000000000000001e10401210400000000000000ba0b00fd0f000000000000011a1100b0c300000000000001028a00b00000000000000000b14500f1040000000000000000000000000000000000000260000338e100000000000000000000000000000000000002624900300000000000000000000002630c000000000000000980009104 6 j))) (by decide +kernel)

def g59n14w : List Sig := [g59v1,g59v2,g59v4,g59v5,g59v8,g59v13,g59v19,g59v23,g59v29,g59v35]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n14 : Impossible false g59T 10 g59n14w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4037100db4035500d44034500ce4032900c64031500c44030d00c0402ed00b8401e10074401b1006540159005540145004f40121003f40095001a30284c08c30228c06130130c04a14184504a0a228284c0a128188a06130184a060d01832060c409a102584094c024c4064c018d005a1016300561015300534014c403a100d840331 18 (bitsAt 0x3055502f55500000000000002849202849200000000000002934d02d2cb00000000000002cd2502fe2300000000000002e18602c0c300000000000002704102c00000000000000002c14502e104000000000000000000031ca100000000000001c5d701a55500000000000002851401a49200000000000001a38e01a2cb00000000000001bd5b01adda00000000000001b20801a0c300000000000001a08201a00000000000000001c1c701a10400000000000001f55501d55500000000000002849201d49200000000000001d34d01d2cb00000000000001ed1e01dd9d00000000000001e18601d0c300000000000001d04101d00000000000000001f14501d1040000000000000286590154920000000000000152cb02b2cb000000000000016e56015a950000000000000160c30150c30000000000000150000150000000000000000241040151040000000000000122cb0182cb000000000000013e13012d120000000000000130c30120c300000000000001200001200000000000000001910401210400000000000000b98b00fd0f00000000000001199100b0c300000000000001028a00b00000000000000000b14500f1040000000000000000000000000000000000000240000338a000000000000000000000000000000000000002424900300000000000000000000002430c000000000000000900009104 6 j))) (by decide +kernel)

def g59n15w : List Sig := [g59v2,g59v4,g59v8,g59v10,g59v13,g59v14,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n15 : Impossible false g59T 10 g59n15w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d34034100c2402ed00b8402350085401fd007e401f5006f401a500664018d003630228c04a242849034240c89031141845034140c850310a228284c0a1282831026840961024c4064c019280634018c805a101584054c014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0x89e7deb5a5960000000000009da555b9a4d3000000000000a9a104b9e082000000000000b5a75ab9e659000000000000a9a8dab9a041000000000000b9e451ada3cf000000000000a1c28aa9a18600000000000099b145a9a0000000000000009d64d3b564d3000000000000a96082b5f082000000000000b56656b5f75d000000000000a96916b56041000000000000b5f410ad63cf000000000000a18249a961860000000000009970c3a96000000000000000aaa9a0953082000000000000b6d659953653000000000000a930419660410000000000009d33cfaeb3cf0000000000009d4186a93186000000000000953000a93000000000000000000000000000000000000000a82041aa69a1000000000000a823c2ac2482000000000000a88186a822c2000000000000a82000a88308000000000000a99041999041000000000000b693cfad93cf000000000000b68186a99186000000000000b66000a99000000000000000000000000000000000000000a87186a812c1000000000000a81000a87307000000000000b2834da8f186000000000000ae638ea8f000000000000000a8b30ba86000 6 j))) (by decide +kernel)

def g59n16w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v18,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n16 : Impossible false g59T 10 g59n16w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100db4034d00d04030900bb402e10085401fd007e401f5007c401bd006940189005e40175005740145004830228c04a240d09032240c45061141285034140c850310a228284c0a128188a06130184a060d01832060c409a102584093101930064a018d00632016840561014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0xda28e2d1f69a000000000000bdf659d5f5d7000000000000c5fa9fd62a62000000000000d1f596d62514000000000000d62410c9f38e000000000000c21249c5f186000000000000ba0145c5f000000000000000c5f104d5f041000000000000bda5d7d1a5d7000000000000c5aadad23a63000000000000d1a514d23514000000000000d233cfc9a38e000000000000c1c208c5a186000000000000b9b0c3c5a000000000000000c5a082d1a041000000000000c57b17b6e9e8000000000000d3479eb57514000000000000bd738ecb238e000000000000bd8186c57186000000000000b57000c57000000000000000c71041b57041000000000000000000000000000000000000000000000000000000000000c65186c6428a000000000000c66000c642cb000000000000000000000000000000000000d1438ec9d38e000000000000d15186c54186000000000000d14000c54000000000000000c5e041b94041000000000000cd330cc4e186000000000000c9234dc4e000000000000000c4e082c91041000000000000c4a2cac46000000000000000c461c6c4a041000000000000c40040c4b1c7 6 j))) (by decide +kernel)

def g59n17w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v10,g59v13,g59v19,g59v23,g59v28,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n17 : Impossible false g59T 10 g59n17w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d74035900d34034100ce4033100ca4030100b9402e100a740285009e40275009c40265007f401f5006f401a10062401650053400b8c04a240d09032240c45061141285034140c850310a228284c0a128184c061281831026840961024c4064c019280634018c805a101584054c014c403a100e28036100d280331 18 (bitsAt 0x1ba1b028b1f00000000000001eade01b59600000000000001b55501b4d300000000000001ba1b01e45100000000000001b8db01bd1b00000000000001e3cf01b34d00000000000001d20801b14500000000000001c10401b00000000000000001b0c301b0410000000000000000000000000000000000000264d30254d300000000000000000000000000000000000002dca402ed6200000000000002834d02e34d00000000000002f14502d14500000000000002e00002d00000000000000002d04102e0410000000000000164d30164d3000000000000000000027451000000000000016c96016cd600000000000002838e01634d0000000000000181c701614500000000000001708201600000000000000001604101604100000000000003369a013451000000000000013d93028d6800000000000001334d03234d00000000000001414501314500000000000001300001300000000000000002aa6a013041000000000000011cd1019c9900000000000001134d01934d00000000000001214501114500000000000001100001100000000000000001acda01104100000000000000000000000000000000000002014503124900000000000002100003028a0000000000000000000000000000000000000202cb00d14500000000000002130c00d00000000000000000000001004100000000000000928900500000000000000000518500904100000000000000004000a186 6 j))) (by decide +kernel)

def g59n18w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v10,g59v13,g59v19,g59v23,g59v29,g59v34]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n18 : Impossible false g59T 10 g59n18w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d94036100d34034500d04033500cb4030100b9402e100a840281009e40275009c40265007f401f5006e401a5006240169005440098c08a24284908a240d09032240c45034140c850310a228284c0a128188c062281831026840961024c4064c019280634018c805a101584054c014c403a100e28036100d280331 18 (bitsAt 0x2859602ba1f0000000000000265550254d300000000000000000000000000000000000002dca302ed6200000000000002834d02e34d00000000000002f14502d14500000000000002e00002d00000000000000002d0c302e04100000000000002c79e0195960000000000000195550194d3000000000000000000027451000000000000019cd9019d190000000000000283cf01934d00000000000001b20801914500000000000001a1040190000000000000000190c30190410000000000000164d30164d3000000000000016a1601e451000000000000016916016c9600000000000001e38e01634d0000000000000181c701614500000000000001708201600000000000000001604101604100000000000003275d013451000000000000013d93028d6800000000000001334d03234d00000000000001414501314500000000000001300001300000000000000002aa6a013041000000000000011c9101ccdc00000000000001134d01c34d00000000000001214501114500000000000001100001100000000000000001dc9d01104100000000000000000000000000000000000002014503124900000000000002100003028a0000000000000000000000000000000000000202cb00d14500000000000002130c00d00000000000000000000001004100000000000000928900500000000000000000518500904100000000000000004000a186 6 j))) (by decide +kernel)

def g59n19w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v10,g59v13,g59v19,g59v23,g59v29,g59v35]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n19 : Impossible false g59T 10 g59n19w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4037100db4035500d44034500ce4033100ca4030100b9402e100a84029d00a54029100a140281009c40265007f401f50075401d100694019900624016d005540098c0a130230c08a30184c04c30128506114128288a0a130284a06228184c061281831026840961024c4064c019280634018c805a101584054c014c403a100e28036100d280331 18 (bitsAt 0x2851402751400000000000002a451029451000000000000031da4032ea200000000000002c38e03234d0000000000000331c703114500000000000003208203100000000000000003104103204100000000000000000002bbdf00000000000001b5960195140000000000000304d3019451000000000000019dd9019e590000000000000193cf01934d00000000000001a20801914500000000000001910401900000000000000001b0c301904100000000000001e51401c51400000000000002c45101c45100000000000001cd9c01ce1c00000000000001c38e01c34d00000000000001d1c701c14500000000000001c08201c00000000000000001e04101c04100000000000002e618014451000000000000014ed402c96600000000000001434d03634d00000000000001514501414500000000000001400001400000000000000002eb6e014041000000000000011e91017d9700000000000001134d01734d0000000000000121450111450000000000000110000110000000000000000188d801104100000000000000000000000000000000000002014503524900000000000002100003428a0000000000000000000000000000000000000202cb00d14500000000000002130c00d00000000000000000000001004100000000000000928900500000000000000000518500904100000000000000004000a186 6 j))) (by decide +kernel)

def g59n20w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v9,g59v13,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n20 : Impossible false g59T 10 g59n20w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d14033900c0402e500994022d008a402250088401f9007c401bd006940189005e40175005740145004830228c04a240d09032240c45061141285034140c850310a228284c0a128188a06130184a060c4093101930064a018d00632016840561014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0xc5e7de95b596000000000000c9b555a9b4d3000000000000c9b492c5e410000000000000c9b99bbdb95b000000000000c9e99ebdb38e000000000000c1d24981b186000000000000bdc14581b000000000000000c9b104bdb041000000000000c564d3a964d3000000000000c56410c5f410000000000000c569d6bd6956000000000000c5f9dfbd638e000000000000c18208816186000000000000bd70c3816000000000000000c56082bd6041000000000000b2d69ac53410000000000000a93a13bef8e4000000000000a9338ebef38e000000000000c14186a93186000000000000bd3000a93000000000000000aab041bd3041000000000000c50b90bd9959000000000000c5038ebd938e000000000000c11186c50186000000000000bd0000c50000000000000000ada041bd0041000000000000000000000000000000000000c21186be0186000000000000be2000be0000000000000000be9082be0041000000000000c2130cbce186000000000000be234dbce000000000000000bce082bcf041000000000000bca2ca806000000000000000c061c6bca041000000000000bc0040bcb1c7 6 j))) (by decide +kernel)

def g59n21w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v14,g59v20,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n21 : Impossible false g59T 10 g59n21w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4030500bb402e900b8402dd00b4402c100ae402a900a340275003630228c04a242849034240c89031141845034140c850310a228284c0a1282831060d01832060c409a102584093101930064a018d00632016840561014d0053100e84036100cc80331 18 (bitsAt 0x91e7de95a5960000000000009da555a1a4d30000000000009daa1aa1e8de00000000000085a75a99e659000000000000a9e38ea5a30c000000000000a1c1c79da104000000000000a1b0c39da0000000000000009daa1aa1a0410000000000009d64d3a164d30000000000009d6a16a1f89f00000000000085665695f75d000000000000a9f34da5630c000000000000a181869d6104000000000000a170829d60000000000000009d6a16a160410000000000009e8a209d3a130000000000009e8659a136530000000000009d330ca6a3cf0000000000009d41049d32080000000000009d30009d32490000000000000000000000000000000000000000000000000000000000009e830ca6a4920000000000009e81049e82080000000000009e80009e8249000000000000000000000000000000000000aaa30ca5930c000000000000a281049d9104000000000000a280009d9000000000000000000000a19041000000000000ad128a9cc104000000000000a502cb9cc0000000000000009cca0ca4f0410000000000009c82489c40000000000000009c41449c80410000000000009c00409c9145 6 j))) (by decide +kernel)

def g59n22w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v14,g59v17,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n22 : Impossible false g59T 10 g59n22w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4036d00d34034100c2402ed00b3402bd009940239008d40231008b40225005740145004a40125003630228c04a242849034240c8903114184504a140d05032140c4288a0a130284a0a0c4188a06130184a060d01832060c4093101930064a018d00632016840561014d0053100e84036100cc80331 18 (bitsAt 0xce0860c5c5d7000000000000adc596c9c514000000000000c5c7dcca06db000000000000bdc492ca0410000000000000ca0ba0bdc30c000000000000b9e1c7c1c104000000000000b9d0c3bdc000000000000000bdca9cc9c041000000000000ad7514c57514000000000000c576d7c617df000000000000bd7410c61410000000000000c61b61bd730c000000000000b59186c17104000000000000b58082bd7000000000000000bd7a97c57041000000000000c546d4a6a6db000000000000befa22a54410000000000000a5430cbef30c000000000000ad5104c14104000000000000ad4000bd4000000000000000bef041a54041000000000000bdb410c6ab23000000000000000000000000000000000000c65104c1b104000000000000c66000bdb000000000000000bdb0419db041000000000000bd030cbda4d3000000000000bd1104c10208000000000000bd0000bd0249000000000000000000000000000000000000c0f28abcc104000000000000bce2cbbcc000000000000000bcca8cbcd041000000000000908248bc4000000000000000bc4144c08041000000000000bc0040bc9145 6 j))) (by decide +kernel)

def g59n23w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v14,g59v21,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n23 : Impossible false g59T 10 g59n23w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100da4034d00d24034100cf402ed00b84021d008640201007f401f1003630228c04a242849034240c89031141845034140c850310a228284c0a1282831060d01832060c409a102584093101930064a018d00632016840561014d0053100e84036100cc80331 18 (bitsAt 0xb1e7dea1a596000000000000a1a555a9e4d3000000000000a1aa5aa9eade000000000000a1a75aa9e659000000000000a9e38ea1a30c000000000000adc1c7a9a104000000000000adb0c3a9a000000000000000adaadaa9a041000000000000a164d3a1f4d3000000000000a16a56a1fa5f000000000000a16656a1f75d000000000000a1f34da1630c000000000000a58186a16104000000000000a57082a16000000000000000a56a56a16041000000000000a26a60a13a53000000000000000000000000000000000000a1330ca2730c000000000000a14104a53104000000000000a13000a53000000000000000a26041a53041000000000000000000000000000000000000a2930ca29492000000000000a29104a65208000000000000a29000a63249000000000000000000000000000000000000a2930ca1930c000000000000a29104a59104000000000000a29000a59000000000000000000000a59041000000000000a5128aa0c104000000000000a502cba0c000000000000000a4ca4ca0f041000000000000848248884000000000000000884144908041000000000000880040889145 6 j))) (by decide +kernel)

def g59n24w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v14,g59v22,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n24 : Impossible false g59T 10 g59n24w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => (linkRule g59n0w g59n0)))) (idx:=(fun j => bitsAt 0x200004036900d34034900d04033d00c1402ed00ba402e100b730228c04a242849034240c89031141845034140c850310a228284c0a1282831060d01832060c409a102584093101930064a018d00632016840561014d0053100e84036100cc80331 18 (bitsAt 0xa5e7de95a59600000000000081a5559de4d300000000000081a85a9dea1e00000000000095a75a9de6590000000000009de38e89a30c00000000000085c1c781a10400000000000085b0c381a00000000000000081a85a9da0410000000000008164d395f4d300000000000081685695f99f00000000000095665695f75d00000000000095f34d89630c00000000000085818681610400000000000085708281600000000000000081685695604100000000000000000000000000000000000000000000000000000000000081330c8a386a00000000000081410481320800000000000081300081324900000000000000000000000000000000000000000000000000000000000082130c8a349200000000000082110482120800000000000082100082124900000000000000000000000000000000000096330c89930c00000000000096110481910400000000000096100081900000000000000000000085904100000000000091128a80c1040000000000008902cb80c00000000000000080c84c88f041000000000000808248804000000000000000804144808041000000000000800040809145 6 j))) (by decide +kernel)

def g59n25w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v20,g59v23,g59v24,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n25 : Impossible false g59T 10 g59n25w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100c1402ed00ba402e100b7402d900ae402b500aa40291009b30284c04a240d09032240c450611412850310a228284c0a128188a06130184a060d01832060c409a102584093101930064a018d0063201684056401584053100e84036200d840331 18 (bitsAt 0x99b9db9db89b00000000000085e7de95b61800000000000099b5d79db55500000000000091b5148de492000000000000a5e38ea1b30c0000000000009dd1c799b1040000000000009dc0c399b00000000000000099b9db9db0820000000000000000000000000000000000009a75559a75550000000000009a74929e04920000000000009a730ca293cf0000000000009a71049a72080000000000009a70009a72490000000000000000000000000000000000009985559d85550000000000008584928df492000000000000a6934da1830c0000000000009e71459981040000000000009e70419980000000000000000000009d80820000000000009a769a9d549200000000000099530ca293cf000000000000996104995208000000000000995000995249000000000000000000000000000000000000a5230ca1930c0000000000009d31049921040000000000009d200099200000000000000099a9da9d2082000000000000a9128a98c104000000000000a102cb98c00000000000000098c9cca0f082000000000000988248984000000000000000984184988082000000000000980080989186 6 j))) (by decide +kernel)

def g59n26w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v20,g59v23,g59v29,g59v30]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n26 : Impossible false g59T 10 g59n26w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100c1402ed00ba402e100b7402d500b2402c500ab4028d009b30228c061240c45061141285034140c850310a228284c0a128188a06130184a060d01832060c409a102584093101930064a018d006320169005a101584053100e8803a100d840331 18 (bitsAt 0x9a76189e16180000000000009a75d79a75550000000000009a75149e04920000000000009a730ca293cf0000000000009a71049a72080000000000009a70009a724900000000000000000000000000000000000089e7de95d61800000000000099d5d79dd55500000000000089d5148de492000000000000a6938ea1d30c0000000000009e718699d1040000000000009e708299d0000000000000000000009dd0c30000000000009985559d85550000000000009184928df492000000000000a5f34da1830c0000000000009da1459981040000000000009d90419980000000000000009989d89d80c30000000000009a771c9d549200000000000099530ca293cf000000000000996104995208000000000000995000995249000000000000000000000000000000000000a5230ca1b30c0000000000009d31049921040000000000009d200099200000000000000099c9dc9d20c3000000000000a9128a98c104000000000000a102cb98c00000000000000098c9cca0f0c30000000000009882489840000000000000009841c49880c30000000000009800c09891c7 6 j))) (by decide +kernel)

def g59n27w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v20,g59v23,g59v28,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n27 : Impossible false g59T 10 g59n27w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d74034100ce402ed00b8402d100b2402a900a540291009e40275009b401e9005740145004d40121002f301289034240c8903114184504a140d05032140c4288a0a130284a06130184a060d01832060c409a102584093101930064a018d00632016840561014d0053100e8803a100d88036100cc80331 18 (bitsAt 0xa5ea9ed34b62000000000000ae1b21d1e659000000000000d1e618bde596000000000000a5ea9ed21514000000000000aa1410a5e38e000000000000ba0249bde186000000000000b9f104bde000000000000000b9e145bde041000000000000000000000000000000000000d30596d27596000000000000000000000000000000000000a6a38ed3138e000000000000a65186d30186000000000000a66000d30000000000000000a70041d23041000000000000d19596d19596000000000000000000d28514000000000000aea3cfd1938e000000000000adb208d19186000000000000ada082d19000000000000000ad90c3d19041000000000000d3375dd16514000000000000d1638ea72451000000000000d17186a9628a000000000000d16000a962cb000000000000000000000000000000000000a5438ed1c38e000000000000a55186d14186000000000000a54000d14000000000000000a5d041d14041000000000000a9330ca4e186000000000000a9234da4e000000000000000a8ea8ea5104100000000000090a2ca9060000000000000009061c690a04100000000000090004090b1c7 6 j))) (by decide +kernel)

def g59n28w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v20,g59v23,g59v29,g59v34]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n28 : Impossible false g59T 10 g59n28w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4036500d0402ed00b8402c100ae402b100ab4028d009e40275009b401e9005740145004e4012100273022890a1242289034240c89031140d05032140c4288a0a130284a06230188a060d01832060c409a102584093101930064a018d00632016840561014d0053100e8803a100d88036100cc80331 18 (bitsAt 0xa6a659cebce2000000000000cf0618ce7596000000000000000000000000000000000000a6a38ecf138e000000000000a65186cf0186000000000000a66000cf0000000000000000a70041ce3041000000000000b2d861cdc659000000000000cdc618cdc596000000000000000000ce8514000000000000b2a410cdc38e000000000000b1e249cdc186000000000000b1d104cdc000000000000000b1c145cdc041000000000000cd9596bd9596000000000000a59a99ce1514000000000000aa13cfa5938e000000000000b9b208bd9186000000000000b9a082bd9000000000000000b990c3bd9041000000000000cf2820cd6514000000000000cd638ea72451000000000000cd7186a9628a000000000000cd6000a962cb000000000000000000000000000000000000a5438ecdf38e000000000000a55186cd4186000000000000a54000cd4000000000000000a60041cd4041000000000000a9330ca4e186000000000000a9234da4e000000000000000a8ea8ea5104100000000000090a2ca9060000000000000009061c690a04100000000000090004090b1c7 6 j))) (by decide +kernel)

def g59n29w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v20,g59v23,g59v29,g59v35]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n29 : Impossible false g59T 10 g59n29w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100dc4036d00ce402ed00b8402b900ad402b100ab402a900a54029100a340279009b401e9005740145004f40121002730284c08c30228c06130130c04a14184504a0a228284c0a128188a06130184a060d01832060c409a102584093101930064a018d00632016840561014d0053100e8803a100d88036100cc80331 18 (bitsAt 0xdb25d7da75d7000000000000ae9514da8514000000000000aec3cfdb338e000000000000ae5208db2186000000000000ae6082db2000000000000000af20c3da3041000000000000000000daab62000000000000d9e659d9c5d7000000000000baf596d9c514000000000000b9c410d9c38e000000000000b9d249d9c186000000000000b9c104d9c000000000000000b9e145d9c041000000000000da15d7d9f5d7000000000000aec514d9f514000000000000adf3cfd9f38e000000000000ae0208d9f186000000000000adf082d9f000000000000000ae10c3d9f041000000000000db56dbc17514000000000000d9738eaf4451000000000000d98186b1728a000000000000d97000b172cb000000000000000000000000000000000000b1438eada38e000000000000c55186c14186000000000000c54000c14000000000000000c5b041c14041000000000000b1330cace186000000000000b1234dace000000000000000b0eb0ead104100000000000090a2ca9060000000000000009061c690a04100000000000090004090b1c7 6 j))) (by decide +kernel)

def g59n30w : List Sig := [g59v1,g59v2,g59v4,g59v6,g59v8,g59v13,g59v17,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n30 : Impossible false g59T 10 g59n30w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4034d00d14034100ce4032500c0402fd00be402e500b84026900984025d00964025500944024d0092402350089401cd006d40175005c40145004a40121001430228c04a240d09032240c4504a140d05032140c4288a0a130284a06228184c061281834060c8183102528093101a30068a01930064a018d00632014d0038a00d280332 18 (bitsAt 0x1c75c01955500000000000001951401949200000000000001991901ccdc00000000000001945101c3cf00000000000001c91c01928a00000000000001ae1a019e5900000000000001b20801910400000000000001a24901914500000000000001908201900000000000000001549201549200000000000001595501dc9d0000000000000153cf01d3cf00000000000001d95d01528a000000000000016d96015dd50000000000000171860151040000000000000161c7015145000000000000015041015000000000000000012d520298a300000000000002baab0123cf00000000000001228a03128a000000000000012bd2012b9200000000000001310401210400000000000001214501214500000000000002b000012000000000000000000000000000000000000000000000000000000000000000031de1030d9f00000000000003410403010400000000000003114503014500000000000003000003100000000000000000000001828a00000000000000fdcf00fd8f00000000000001010400f10400000000000000f14500f14500000000000002000000f00000000000000000da4d00ad8a00000000000000e18600a10400000000000000d1c700a14500000000000000a04100c0000000000000000000000000000000000000000000000000000000000000000270000262cb000000000000000000028b1e00000000000002d0c30040000000000000000290000050c3 6 j))) (by decide +kernel)

def g59n31w : List Sig := [g59v1,g59v2,g59v4,g59v6,g59v8,g59v13,g59v19,g59v23,g59v27,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n31 : Impossible false g59T 10 g59n31w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4035500d44034100ce4033100ca4032500c0402fd00b9402e100a24027d00974025500944024d008d402250073401b5006740175005c40145004b40121001530230c08a30128908a240d09032240c4506114128288a0a19028620a184284c0a128188a06130184a02584094a01a30068a01930064a018d00632014d0038a00d280332 18 (bitsAt 0x1b95b017c5700000000000001b71b0179970000000000000175140173cf00000000000001738e01b30c00000000000001b95b0172cb000000000000018e18017e570000000000000192080171040000000000000182490171450000000000000170820170000000000000000000000000000000000000000333cf022a6300000000000002630c02469a000000000000000000000000000000000000030da102fddf00000000000003218602f1040000000000000301c702f14500000000000002f04103000000000000000002a3cf01c3cf00000000000002630c01c30c00000000000000000001c2cb00000000000001cd9c01cddc00000000000001d18601c10400000000000001c1c701c14500000000000002004101c00000000000000002b59600f30c00000000000000f2cb0302cb00000000000000fb8f00fb4f00000000000001010400f10400000000000000f14500f14500000000000002b00000f00000000000000000c98c0152cb00000000000000cdcc00cd8c00000000000000d10400c10400000000000000c14500c14500000000000001600000c000000000000000012a5200bd8b00000000000001318600b1040000000000000121c700b14500000000000000b04101100000000000000000000000000000000000000000000000000000000000000002800002728a000000000000000000034d5e00000000000002c0c30040000000000000000290000050c3 6 j))) (by decide +kernel)

def g59n32w : List Sig := [g59v1,g59v2,g59v4,g59v6,g59v8,g59v13,g59v19,g59v23,g59v29,g59v33]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n32 : Impossible false g59T 10 g59n32w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4035500d44034d00d14033500cb4032500c0402f900b9402e100a94029900974025500944024d008d40225006d4019d005d40171005140131004840058c08a30130c04a14184504a140d05032140c428a40a28828a10a228284c0a128188a06130184a02684094a01a30068a01930064a018d00632014d0038a00d280332 18 (bitsAt 0x2471c02f5550000000000000313cf0219e200000000000002430c02361800000000000000000000000000000000000002ed2002dd5e00000000000003018602d10400000000000002e1c702d14500000000000002d04102e00000000000000001a71a02455500000000000002845101a3cf00000000000002438e01a30c00000000000000000001a2cb00000000000001ad1a01ad5a00000000000001b20801a10400000000000001a24901a14500000000000001f08201a0000000000000000153cf0153cf00000000000001530c01c30c00000000000001c91c0152cb000000000000016dd6015d950000000000000171860151040000000000000161c701514500000000000001504101500000000000000002965900f30c00000000000000f2cb02e2cb00000000000000fb0f00facf00000000000001010400f10400000000000000f14500f14500000000000002900000f00000000000000000c90c0182cb00000000000000cd4c00cd0c00000000000000d10400c10400000000000000c14500c14500000000000001900000c0000000000000000139d300bd0b00000000000001418600b1040000000000000131c700b14500000000000000b04101200000000000000000000000000000000000000000000000000000000000000002600002528a000000000000000000032cdd00000000000002a0c30040000000000000000270000050c3 6 j))) (by decide +kernel)

def g59n33w : List Sig := [g59v1,g59v2,g59v4,g59v6,g59v8,g59v13,g59v21,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n33 : Impossible false g59T 10 g59n33w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4034d00d04032500b9402e100954025100844020d007c401ed006f401a5006740189001730228c04a242849034240c89031141905062141845034140c850310a228284c0a1281834060c8183102684096102528093101a30068a01930064a018d00632014d0038a00d280332 18 (bitsAt 0x89e7de89a514000000000000b5a4d399e45100000000000089a75a89e5d7000000000000a9e34da5a28a00000000000095b8dbb5abda0000000000009dc208b5a10400000000000095b249b5a14500000000000099a08295a000000000000000b5445199f4510000000000008945d489f75d000000000000a9f30ca5428a000000000000955915b54b940000000000009d6186b541040000000000009551c7b54145000000000000994041954000000000000000000000000000000000000000b5128aa6c28a000000000000b51b91b51991000000000000b52104b51104000000000000b51145b51145000000000000b6b000951000000000000000aaa28aa5728a000000000000958b98b578570000000000009d9104b57104000000000000958145b5714500000000000099700095700000000000000094f98fb4ab8a0000000000009d0186b4a10400000000000094f1c7b4a14500000000000098a04194e000000000000000000000000000000000000000000000000000000000000000966000b662cb000000000000000000b66a200000000000009e60c3b44000000000000000966000b450c3 6 j))) (by decide +kernel)

def g59n34w : List Sig := [g59v1,g59v2,g59v4,g59v6,g59v8,g59v13,g59v19,g59v23,g59v28,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n34 : Impossible false g59T 10 g59n34w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d74035900d34034100ce4033100ca4032500c0402fd00b9402e10073401a100674017d005c4014d00514013500484010d003040060c04a240d09032240c45061141285034140c850310a228284c0a128184c061281834060c8183102684096102528093101a30068a01930064a018d00632014d0038a00d280332 18 (bitsAt 0x1ba1b021b6000000000000001ea1e01b59600000000000001b55501b4d300000000000001ba1b01e45100000000000001e34d01b28a00000000000001ca5c01bd1b00000000000001d20801b10400000000000001c24901b14500000000000001b08201b00000000000000000000000000000000000000002f4d30264d300000000000000000000000000000000000002a28a02c28a00000000000002cca402bd6200000000000002e10402b10400000000000002c14502b14500000000000002b00002c0000000000000000164d30164d300000000000000000002845100000000000002a30c01628a000000000000017c97016cd60000000000000181860161040000000000000171c701614500000000000001604101600000000000000002869a01345100000000000001328a02728a000000000000013d93013d5300000000000001410401310400000000000001314501314500000000000002300001300000000000000001128a01928a000000000000011cd1011c9100000000000001210401110400000000000001114501114500000000000001a00001100000000000000000f94f00ac8a00000000000001018600a10400000000000000f1c700a14500000000000000a04100e0000000000000000000000000000000000000000000000000000000000000000230000232cb000000000000000000030c5f0000000000000230c30040000000000000000230000050c3 6 j))) (by decide +kernel)

def g59n35w : List Sig := [g59v1,g59v2,g59v4,g59v6,g59v8,g59v13,g59v19,g59v23,g59v29,g59v34]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n35 : Impossible false g59T 10 g59n35w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d94036100d34034500d04033500cb4032500c0402f900b9402e1006e401b5006740181005c4015100514013900484011d002840064c08a24284908a240d09032240c45034140c850310a228284c0a128188c062281834060c8183102684096102528093101a30068a01930064a018d00632014d0038a00d280332 18 (bitsAt 0x2859602d86000000000000002f5550264d300000000000000000000000000000000000002928a02c28a00000000000002cca402bd6200000000000002e10402b10400000000000002c14502b14500000000000002b00002c00000000000000002879e0195960000000000000195550194d300000000000000000002845100000000000002934d01928a00000000000001acda019d1900000000000001b20801910400000000000001a2490191450000000000000190820190000000000000000164d30164d3000000000000016a1601e45100000000000001e30c01628a000000000000017a97016c960000000000000181860161040000000000000171c701614500000000000001604101600000000000000002875d01345100000000000001328a02728a000000000000013d93013d5300000000000001410401310400000000000001314501314500000000000002300001300000000000000001128a01c28a000000000000011c91011cd100000000000001210401110400000000000001114501114500000000000001d00001100000000000000000f94f00ac8a00000000000001018600a10400000000000000f1c700a14500000000000000a04100e0000000000000000000000000000000000000000000000000000000000000000230000232cb000000000000000000030c5f0000000000000230c30040000000000000000230000050c3 6 j))) (by decide +kernel)

def g59n36w : List Sig := [g59v1,g59v2,g59v4,g59v6,g59v8,g59v13,g59v19,g59v23,g59v29,g59v35]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n36 : Impossible false g59T 10 g59n36w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4037100db4035500d44034500ce4033100ca4032500c0402fd00be402e500b8401d1006d4019d006140171005540145004f40121002840068c0a130230c08a30184c04c30128506114128288a0a130284a06228184c061281834060c8183102684096102528093101a30068a01930064a018d00632014d0038a00d280332 18 (bitsAt 0x2f51402551400000000000002745102745100000000000002830c02b28a00000000000002bca302ada100000000000002e18602a10400000000000002b1c702a14500000000000002a04102b00000000000000000000002cb6000000000000001b5960195140000000000000274d301945100000000000001934d01928a000000000000019cd9019d5900000000000001a20801910400000000000001924901914500000000000001b08201900000000000000001e51401c51400000000000002745101c45100000000000001c30c01c28a00000000000001cc9c01cd1c00000000000001d18601c10400000000000001c1c701c14500000000000001e04101c00000000000000002761801445100000000000001428a02628a000000000000014dd4014a5400000000000001510401410400000000000001414501414500000000000002200001400000000000000001128a01728a000000000000011d91011c9100000000000001210401110400000000000001114501114500000000000001800001100000000000000000f90f00ac8a00000000000001018600a10400000000000000f1c700a14500000000000000a04100e0000000000000000000000000000000000000000000000000000000000000000220000222cb000000000000000000030c5f0000000000000220c30040000000000000000220000050c3 6 j))) (by decide +kernel)

def g59n37w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v11,g59v13,g59v19,g59v23,g59v28,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n37 : Impossible false g59T 10 g59n37w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4035d00d64034d00d04033900cc4032100c7402fd00bb402e500a140279009d402710099401ed0079401a100624016500574014d004d400c4c04a240d09032240c45061141285034140c850310a288288a0a188284c0a128283206130184a060c8068c01930064a018c805a1015840534014c4038a00d280332 18 (bitsAt 0x199d9027b5d00000000000001ca9c0195140000000000000194920193cf0000000000000199d901c30c00000000000001a8da019cd900000000000001c4d30192cb00000000000001b1860190c300000000000001a28a0192490000000000000190820190000000000000000000000000000000000000000253cf0243cf00000000000000000000000000000000000002bc6002cd220000000000000272cb02b38e00000000000002e0c302f0c300000000000002b24902c24900000000000002c00002b0000000000000000143cf0143cf00000000000000000002630c000000000000015c55014c940000000000000274510142cb0000000000000161450140c300000000000001524901424900000000000001404101400000000000000003261800f30c00000000000000fd4f027d2700000000000000f2cb0312cb0000000000000100c300f0c300000000000000fa0f00f24900000000000002900000f00000000000000000cc8c017c5700000000000000c2cb01738e00000000000000d0c300c0c300000000000000cc8c00c24900000000000001800000c00000000000000000000000000000000000000001f1c70300c300000000000000000000000000000000000002100001e10400000000000001f20800b0c300000000000000000000b24900000000000002104100b000000000000000007247003843000000000000003103007000000000000000021000009104 6 j))) (by decide +kernel)

def g59n38w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v11,g59v13,g59v19,g59v23,g59v29,g59v34]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n38 : Impossible false g59T 10 g59n38w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4036500d84034d00d14034100cd4032100c7402f900bb402e500a840279009d402710099401ed0079401b9006240169005740151004e400a4c08a24284908a240d09032240c45034140c850310a288288a0a188284c0a128283206230188a060c8068c01930064a018c805a1015840534014c4038a00d280332 18 (bitsAt 0x2751402d9dd0000000000000254920243cf00000000000000000000000000000000000002bc6002cd220000000000000272cb02b38e00000000000002e0c302f0c300000000000002b28a02c24900000000000002c00002b00000000000000002a71c0175140000000000000174920173cf00000000000000000002630c000000000000018c98017cd70000000000000274d30172cb0000000000000191860170c300000000000001828a0172490000000000000170820170000000000000000143cf0143cf0000000000000149d401c30c0000000000000158d5014c5400000000000001c4510142cb0000000000000161450140c30000000000000152490142490000000000000140410140000000000000000316db00f30c00000000000000fd4f027d2700000000000000f2cb0312cb0000000000000100c300f0c300000000000000fa0f00f24900000000000002900000f00000000000000000cc4c01ac9a00000000000000c2cb01a38e00000000000000d0c300c0c300000000000000cc4c00c24900000000000001b00000c00000000000000000000000000000000000000001f1c70300c300000000000000000000000000000000000002100001e10400000000000001f20800b0c300000000000000000000b24900000000000002104100b000000000000000007247003843000000000000003103007000000000000000021000009104 6 j))) (by decide +kernel)

def g59n39w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v11,g59v13,g59v19,g59v23,g59v29,g59v35]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n39 : Impossible false g59T 10 g59n39w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4037100db4035500d44034500ce4033100c84031d00bf402f900bb402e500a84029500a440285009c40265007b401e50075401d100624016d005740155004f400a4c0a130230c08a30184c04c3012850611412828a20a22828620a130284a0a0c8188a06130184a060c8068c01930064a018c805a1015840534014c4038a00d280332 18 (bitsAt 0x2641002541000000000000002830c02730c00000000000002dd2002ee2200000000000002949202d2cb0000000000000311450320c300000000000002d24902e24900000000000002e04102d00000000000000000000002fc1d0000000000000194d301741000000000000002c38e01730c000000000000017d57017dd70000000000000175140172cb0000000000000181860170c300000000000001728a01724900000000000001908201700000000000000001c41001a41000000000000002930c01a30c00000000000001ad1a01ad9a00000000000001a49201a2cb00000000000001b14501a0c300000000000001a24901a24900000000000001c04101a00000000000000002b59601030c000000000000010e500298e40000000000000102cb0342cb0000000000000110c30100c3000000000000010a9001024900000000000002b00001000000000000000000ce0c015d1500000000000000c2cb0153cf00000000000000d0c300c0c300000000000000c84c00c24900000000000001600000c00000000000000000000000000000000000000001f1c70330c300000000000000000000000000000000000002100001e10400000000000001f20800b0c300000000000000000000b24900000000000002104100b000000000000000007247003843000000000000003103007000000000000000021000009104 6 j))) (by decide +kernel)

def g59n40w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v15,g59v21,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n40 : Impossible false g59T 10 g59n40w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x4036900d34034900d04033d00b9402450087401f1007b30228c04a242889034240c89031141885034140c850310a228284c0a1281834060c81831026840961024c4064a018d00632016840561014d0053100e28034a00cc80331 18 (bitsAt 0x9dc75c8d85140000000000008d84d395c4510000000000008d891895c99c0000000000008d86d895c5d700000000000095c34d8d82cb00000000000099a1c79581040000000000009999999580000000000000009980c39580410000000000008d44518dd4510000000000008d49148dd91d0000000000008d45d48dd6db0000000000008dd30c8d42cb0000000000009161868d41040000000000009159158d40000000000000009140828d40410000000000008d19118d19110000000000000000000000000000000000008d12cb8e22cb0000000000008d21049111040000000000008d10009110000000000000008e40419110410000000000000000000000000000000000008e42cb8e42cb0000000000008e41049201040000000000000000000000000000000000008e404191f1450000000000008e42cb8d72cb0000000000008e41049171040000000000000000009170000000000000008e404191704100000000000091028a8cb10400000000000090f90f8cb00000000000000090b0828ce0410000000000007882488440000000000000007c4144788041000000000000780040789145 6 j))) (by decide +kernel)

def g59n41w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v12,g59v13,g59v19,g59v23,g59v28,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n41 : Impossible false g59T 10 g59n41w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d74035900d34034100ce4032900c84031d00c64030900c040285009e40275009c40265008340205006840189005340145004d400c8c04a240d09032240c45061141285034140c850310a290288a0a190284c0a128283406130184a060d0068a01930064a018d0053400e84038a00d84034a00cc80331 18 (bitsAt 0x19999026b1d00000000000001ca5c0195140000000000000194920193cf00000000000001999901c30c00000000000001b89b019c9900000000000001c4d30192cb00000000000001b28a01920800000000000001a1450190000000000000000191040190410000000000000000000000000000000000000243cf0233cf00000000000000000000000000000000000002ac1f02bce10000000000000262cb02a38e00000000000002a20802b20800000000000002e00002d00000000000000002b04102a0410000000000000143cf0143cf00000000000000000002530c000000000000016c16014c540000000000000264510142cb0000000000000162080142080000000000000150c301400000000000000001408201404100000000000003161800f30c00000000000000fd0f026ce600000000000000f2cb0302cb0000000000000109d000f20800000000000000f00000f00000000000000002804100f04100000000000000cc4c017c1700000000000000c2cb01738e00000000000000dc4d00c20800000000000000c00000c00000000000000001804100c0410000000000000000000000000000000000000000000000000000000000000201c702f00000000000000002008201e04100000000000000000000b20800000000000002024900b00000000000000002008200b0410000000000000081c7020000000000000000020186008041000000000000000040007186 6 j))) (by decide +kernel)

def g59n42w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v12,g59v13,g59v19,g59v23,g59v29,g59v34]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n42 : Impossible false g59T 10 g59n42w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100d94036100d34034500d04032d00c84031d00c54030900c0402a1009e40275009c40265008340205006e40189005440145004e400a8c08a24284908a240d09032240c45034140c850310a290288a0a190284c0a128283406230188a060d0068a01930064a018d0053400e84038a00d84034a00cc80331 18 (bitsAt 0x2651402c99d0000000000000244920233cf00000000000000000000000000000000000002ac1f02bce10000000000000262cb02a38e00000000000002a28a02b20800000000000002e00002d00000000000000002b04102a04100000000000002971c0175140000000000000174920173cf00000000000000000002530c000000000000019c59017c970000000000000264d30172cb00000000000001928a0172080000000000000181450170000000000000000171040170410000000000000143cf0143cf00000000000001499401c30c000000000000016896014c1400000000000001c4510142cb0000000000000162080142080000000000000150c30140000000000000000140820140410000000000000306db00f30c00000000000000fd0f026ce600000000000000f2cb0302cb0000000000000109d000f20800000000000000f00000f00000000000000002804100f04100000000000000cc0c01ac5a00000000000000c2cb01a38e00000000000000dc0d00c20800000000000000c00000c00000000000000001b04100c0410000000000000000000000000000000000000000000000000000000000000201c702f00000000000000002008201e04100000000000000000000b20800000000000002024900b00000000000000002008200b0410000000000000081c7020000000000000000020186008041000000000000000040007186 6 j))) (by decide +kernel)

def g59n43w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v12,g59v13,g59v19,g59v23,g59v29,g59v35]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n43 : Impossible false g59T 10 g59n43w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100dc4036d00d54035100d14033900ca4032100c74031900c54030900c0402a100a54029100a14027100994020d0081401d5007440189005540145004f400a8c0a130230c08a30184c04c3012850611412828a40a22828640a130284a0a0d0188a06130184a060d0068a01930064a018d0053400e84038a00d84034a00cc80331 18 (bitsAt 0x2541002441000000000000002730c02630c00000000000002ccdf02dde100000000000002849202c2cb00000000000002c20802d2080000000000000310c303000000000000000002d08202c04100000000000000000002ebdd0000000000000194d301741000000000000002b38e01730c000000000000017d17017d970000000000000175140172cb00000000000001828a01720800000000000001714501700000000000000001910401704100000000000001c41001a41000000000000002830c01a30c00000000000001acda01ad5a00000000000001a49201a2cb00000000000001b20801a20800000000000001a0c301a00000000000000001c08201a04100000000000002a59601030c000000000000010e100288a30000000000000102cb0332cb000000000000011a5101020800000000000001000001000000000000000002a04101004100000000000000cdcc015cd500000000000000c2cb0153cf00000000000000d80d00c20800000000000000c00000c00000000000000001604100c0410000000000000000000000000000000000000000000000000000000000000201c703200000000000000002008201e04100000000000000000000b20800000000000002024900b00000000000000002008200b0410000000000000081c7020000000000000000020186008041000000000000000040007186 6 j))) (by decide +kernel)

def g59n44w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v16,g59v21,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n44 : Impossible false g59T 10 g59n44w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 9) (fun i => failRule false g59T 9))) (idx:=(fun j => bitsAt 0x100da4034d00d24034100cf40301009040211008340201007c30228c04a242909034240c89031141905034140c850310a228284c0a1281834060c81831026840961024c4064c018d00632014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0xa1c75c9185140000000000009184d399c45100000000000091895899c9dc0000000000009186d899c5d700000000000099c34d9182cb0000000000009da9da9981860000000000009d91459980000000000000009d810499804100000000000091445191d45100000000000091495491d95d0000000000009145d491d6db00000000000091d30c9142cb0000000000009569569141860000000000009550c39140000000000000009540829140410000000000009129529119510000000000000000000000000000000000009112cb9232cb0000000000009121869511860000000000009110009510000000000000009250419510410000000000000000000000000000000000009252cb9252cb00000000000000000000000000000000000092500095f00000000000000092504195e0410000000000009252cb9172cb00000000000000000095718600000000000092500095700000000000000092504195704100000000000095095090b18600000000000094f28a90b00000000000000094b08290e0410000000000008082488860000000000000008061c68080410000000000008400408091c7 6 j))) (by decide +kernel)

def g59n45w : List Sig := [g59v1,g59v2,g59v3,g59v4,g59v8,g59v13,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n45 : Impossible false g59T 11 g59n45w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<3 then (if i<1 then (linkRule g59n1w g59n1) else (if i<2 then (linkRule g59n2w g59n2) else (linkRule g59n3w g59n3))) else (if i<5 then (if i<4 then (linkRule g59n4w g59n4) else (linkRule g59n5w g59n5)) else (if i<6 then (linkRule g59n6w g59n6) else (linkRule g59n7w g59n7))))))) (idx:=(fun j => bitsAt 0x200068001600048000e000280006000040235007e401f1007a401610057401450049401210038400b100244006d000230228c04a240d09032240c45061141285034140c850310a228284c0a128188a06130184a060d01832060c409a102584094a024c4064a018c805a101584053100e84038a00d84034a00cc80331 18 (bitsAt 0xda086091d618000000000000b5d5d7b1d555000000000000d5d514960492000000000000ca038ebdd2cb000000000000a5f2089dd186000000000000a9dadd9dda1d000000000000a9e1459dd000000000000000b9d1049dd041000000000000b58555b18555000000000000d18492921492000000000000c6134dbd82cb000000000000a5a1c79d8186000000000000a98ad89d8a18000000000000a990c39d8000000000000000b980829d8041000000000000b7371cb15492000000000000b552cbb222cb000000000000a561869d5186000000000000a95ad59d5a15000000000000a950009d5000000000000000b280419d5041000000000000c122cbbdb2cb000000000000a531869d2186000000000000a92ad29d2a12000000000000a920009d2000000000000000b9c0419d2041000000000000a5128a9cb186000000000000a8bacb9cfa0f000000000000a90ad09cb000000000000000b8b0829cf0410000000000009c6a069e6a230000000000009c9a099c60000000000000009c6a069c90410000000000000000000000000000000000000000000000000000000000000000009e830c 6 j))) (by decide +kernel)

def g59n46w : List Sig := [g59v1,g59v2,g59v4,g59v5,g59v8,g59v13,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n46 : Impossible false g59T 11 g59n46w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<3 then (if i<1 then (linkRule g59n8w g59n8) else (if i<2 then (linkRule g59n9w g59n9) else (linkRule g59n10w g59n10))) else (if i<5 then (if i<4 then (linkRule g59n11w g59n11) else (linkRule g59n12w g59n12)) else (if i<6 then (linkRule g59n13w g59n13) else (linkRule g59n14w g59n14))))))) (idx:=(fun j => bitsAt 0x8001a00058001200038000a000180001008d40201007e4015d005240145004940121003c400b500254004d000530228c04a240d09032240c45061141285034140c850310a228284c0a128188a06130184a060d01832060c409a102584094c024c4064c018d005a1016300561015300534014c403a100d840331 18 (bitsAt 0xd6086091d618000000000000b5d5d7b1d555000000000000d1d514960492000000000000c6038eb9d2cb000000000000a5da9d9dda1d000000000000a5f2089dd0c3000000000000ade0829dd000000000000000b1d1c79dd104000000000000b58555b18555000000000000cd8492921492000000000000c2134db982cb000000000000a58a989d8a18000000000000a5a1869d80c3000000000000ad90419d8000000000000000b181459d8104000000000000b7271cb15492000000000000b552cbb222cb000000000000a56a969d5a15000000000000a560c39d50c3000000000000ad50009d5000000000000000b281049d5104000000000000bd22cbb9b2cb000000000000a53a939d2a12000000000000a530c39d20c3000000000000ad20009d2000000000000000b1c1049d2104000000000000a4ba8b9cfa0f000000000000a51a919cb0c3000000000000ad028a9cb000000000000000b0b1459cf1040000000000000000000000000000000000009e80009e89a30000000000000000000000000000000000009e82499c30000000000000000000009e830c0000000000009c0a009c9104 6 j))) (by decide +kernel)

def g59n47w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v10,g59v13,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n47 : Impossible false g59T 11 g59n47w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<2 then (if i<1 then (linkRule g59n15w g59n15) else (linkRule g59n16w g59n16)) else (if i<3 then (linkRule g59n17w g59n17) else (if i<4 then (linkRule g59n18w g59n18) else (linkRule g59n19w g59n19))))))) (idx:=(fun j => bitsAt 0x200048000e000280006000040225008540201007e401c1006a4018d005e401610052401250037400d90035400cd002e40098c08a301289034240c8903114184504a140d05032140c4288a0a130284a06228184c061281831026840961024c4064c019280634018c805a101584054c014c403a100e28036100d280331 18 (bitsAt 0xd9f81f85c5d7000000000000bdc596b9c514000000000000d5c4d389f451000000000000b9cb1cc5cadc00000000000091f3cfc5c34d000000000000a1e208c1c145000000000000a5d104b9c000000000000000b9c0c3c5c041000000000000bd7514b97514000000000000d17451860451000000000000b97b57c57ad700000000000092038ec5734d000000000000a191c7c17145000000000000a58082b97000000000000000b97041c57041000000000000be66dbb94451000000000000b94954ba4aa4000000000000bd434dba334d000000000000bd5145b94145000000000000b94000b94000000000000000ba6966b94041000000000000b91cd1c5aada00000000000091134dc5a34d000000000000a12145c11145000000000000a51000b91000000000000000b9bc9bc51041000000000000000000000000000000000000ba8145c27249000000000000ba9000ba728a000000000000000000000000000000000000a282cbc0d145000000000000a6930cb8d000000000000000000000c500410000000000009c9289b85000000000000000b85185c09041000000000000b80040b8a186 6 j))) (by decide +kernel)

def g59n48w : List Sig := [g59v0,g59v1,g59v2,g59v4,g59v8,g59v13,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n48 : Impossible false g59T 11 g59n48w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (linkRule g59n20w g59n20)))) (idx:=(fun j => bitsAt 0x80001009940225007c401e9006f401a50063401890057401450049401210037400d9000130228c04a240d09032240c45061141285034140c850310a228284c0a128188a06130184a060d01832060c409a102584093101930064a018d00632016840561014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0xae28e2adf69a000000000000b5f659adf5d7000000000000adf596ae2514000000000000b62410adf38e000000000000a612499df186000000000000aa01459df000000000000000b5f1049df041000000000000adfb1f9dfa1f000000000000b9a5d7ada5d7000000000000ada514ae3514000000000000ba33cfada38e000000000000a5c2089da186000000000000a9b0c39da000000000000000b9a0829da041000000000000adab1a9daa1a000000000000c2c79ead7514000000000000c1738ebe438e000000000000a581869d7186000000000000a970009d7000000000000000be80419d7041000000000000be89669d7a17000000000000c9438eadd38e000000000000a551869d4186000000000000a940009d4000000000000000a1e041000000000000000000000000000000000000000000a5330c9ce186000000000000a9234d9ce000000000000000c4e0829d1041000000000000c4ecce9cea0e0000000000009ca2ca9c60000000000000009c61c69ca0410000000000009c6a069c6a060000000000009c00409cb1c70000000000009c0a009c0a00000000000000000000000000 6 j))) (by decide +kernel)

def g59n49w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v14,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n49 : Impossible false g59T 11 g59n49w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<3 then (if i<1 then (linkRule g59n15w g59n15) else (if i<2 then (linkRule g59n16w g59n16) else (linkRule g59n21w g59n21))) else (if i<4 then (linkRule g59n22w g59n22) else (if i<5 then (linkRule g59n23w g59n23) else (linkRule g59n24w g59n24))))))) (idx:=(fun j => bitsAt 0x8001600048000e0002800060000402cd00af40271008d402150080401f90070401a90063401790058401490049400dd0036400d1000830228c04a242849034240c89031141845034140c850310a228284c0a1282831060d01832060c409a102584093101930064a018d00632016840561014d0053100e84036100cc80331 18 (bitsAt 0xa1e7dec1a596000000000000b1a555ada4d3000000000000adaa5ac5ea1e000000000000bda75ac5e659000000000000a5e38eb9a30c00000000000095c1c7b5a10400000000000099b0c3ada000000000000000adaa5ac5a041000000000000b164d3ad64d3000000000000ad6a96c1fa1f000000000000bd6656c1f75d000000000000a9f34db9630c000000000000958186b56104000000000000997082ad6000000000000000ad6a96c16041000000000000af78a3ad39d3000000000000b36659ad3653000000000000b1330cae030c000000000000b14104ad3104000000000000ad3000ad3000000000000000af4041ad3041000000000000000000000000000000000000af330cba1492000000000000ae5104b64208000000000000ae6000ae4249000000000000000000000000000000000000bf530cb9930c000000000000be5104b59104000000000000be6000ad900000000000000000000091904100000000000095128ab4c1040000000000009902cbacc000000000000000accc8cb8f041000000000000908248ac4000000000000000ac4144b48041000000000000ac0040ac9145 6 j))) (by decide +kernel)

def g59n50w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v20,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n50 : Impossible false g59T 11 g59n50w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<3 then (if i<1 then (linkRule g59n21w g59n21) else (if i<2 then (linkRule g59n25w g59n25) else (linkRule g59n26w g59n26))) else (if i<4 then (linkRule g59n27w g59n27) else (if i<5 then (linkRule g59n28w g59n28) else (linkRule g59n29w g59n29))))))) (idx:=(fun j => bitsAt 0x8001600048000e0002800060000401610052401250037400d90033400bd002730228c04a240d09032240c45061141285034140c850310a228284c0a128188a06130184a060d01832060c409a102584093101930064a018d00632016840561014d0053100e8803a100d88036100cc80331 18 (bitsAt 0xc628e291f69a0000000000009df659a1f5d7000000000000c1f596962514000000000000a224109df38e000000000000aa1249a5f186000000000000ae0104a5f000000000000000b9f145a5f0410000000000009da5d7a1a5d7000000000000bda514923514000000000000a233cf9da38e000000000000a9c208a5a186000000000000adb082a5a000000000000000b5a0c3a5a0410000000000009e879ea175140000000000009d738e9e6451000000000000a98186a5728a000000000000ad7000a572cb000000000000000000000000000000000000a1438e9dd38e000000000000a95186a54186000000000000ad4000a54000000000000000b1e041a54041000000000000a9330ca4e186000000000000ad234da4e000000000000000a0ea0ea51041000000000000a4a2caa46000000000000000a461c6a4a041000000000000a40040a4b1c7 6 j))) (by decide +kernel)

def g59n51w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v19,g59v23,g59v24,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n51 : Impossible false g59T 11 g59n51w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (linkRule g59n25w g59n25)))) (idx:=(fun j => bitsAt 0x80001008d402150080401f90070401bd006a4018d005e40161005240125003440024c0a1301289034240c8903114184504a140c4288a0a130284a06228184c061281834060c81831026840961024c4064c019280634018c805a101584054c014c403a100d88036100d280331 18 (bitsAt 0xa5ca1ca5c9dc000000000000a5f81fa5c659000000000000b1c618a5c596000000000000a5c555a5f4d3000000000000a1f3cfa5c34d00000000000091e208a5c14500000000000095d104a5c000000000000000adca1ca5c041000000000000000000000000000000000000a6a596ae6596000000000000a6a4d3a674d3000000000000a6a34dba2410000000000000a64145b63249000000000000a65000ae328a000000000000000000000000000000000000a59596ad9596000000000000a594d3a604d3000000000000a6a38eb9934d000000000000a641c7b59145000000000000a65082ad90000000000000000000008d9041000000000000b2a6dba564d3000000000000b1634dae134d000000000000b17145ad6145000000000000ad6000ad6000000000000000aef0c3ad6041000000000000a9334da5a34d000000000000914145a53145000000000000953000a53000000000000000adba9ba530410000000000009122cbb4d14500000000000095130cacd000000000000000acd041b900410000000000008c9289ac5000000000000000ac5185b49041000000000000ac0040aca186 6 j))) (by decide +kernel)

def g59n52w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v19,g59v23,g59v29,g59v30]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n52 : Impossible false g59T 11 g59n52w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (linkRule g59n26w g59n26)))) (idx:=(fun j => bitsAt 0x2000040235008540201007e401a900694018d005e40161005240125003440028c08a30184903114184504a140d05032140c4288a0a130284a06228184c061281834060c81831026840961024c4064c019280634018c805a1016300561014c403a200e84038a00d840331 18 (bitsAt 0xa29659a27659000000000000a29618aa6596000000000000a29555a274d3000000000000a2934db62410000000000000a24145b23249000000000000a25000aa328a000000000000000000000000000000000000a1f81fa1e659000000000000a1e618a9e596000000000000a1e555a1f4d3000000000000a293cfb5e34d000000000000a24208b1e145000000000000a250c3a9e0000000000000000000008de082000000000000ad9596a19596000000000000a194d3a204d3000000000000a6038ea1934d00000000000091b186a1914500000000000095a041a19000000000000000a99a59a19082000000000000ae975da164d3000000000000ad634daa134d000000000000ad7145a96145000000000000a96000a96000000000000000aae104a96082000000000000a5334da1c34d000000000000914145a13145000000000000953000a13000000000000000a9da5da130820000000000009122cbb0d14500000000000095130ca8d000000000000000a8d082b500820000000000008c9289a85000000000000000a851c5b09082000000000000a80080a8a1c7 6 j))) (by decide +kernel)

def g59n53w : List Sig := [g59v1,g59v2,g59v4,g59v6,g59v8,g59v13,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n53 : Impossible false g59T 11 g59n53w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<3 then (if i<1 then (linkRule g59n30w g59n30) else (if i<2 then (linkRule g59n31w g59n31) else (linkRule g59n32w g59n32))) else (if i<5 then (if i<4 then (linkRule g59n33w g59n33) else (linkRule g59n34w g59n34)) else (if i<6 then (linkRule g59n35w g59n35) else (linkRule g59n36w g59n36))))))) (idx:=(fun j => bitsAt 0x200068001600048000e00028000600004024d007c401e9005e401750057401490051401250048400c100284004cc08a301289034240c8903114184504a140d05032140c4288a0a130284a06228184c061281834060c8183102684096102528093101a30068a01930064a018d00632014d0038a00d280332 18 (bitsAt 0xd1f81f89c5d7000000000000b1c596a5c514000000000000cdc4d38df451000000000000c1f34db5c28a00000000000099d9dd91c95c00000000000099e20891c104000000000000a1d24991c14500000000000095c08291c000000000000000b17514a57514000000000000c974518a0451000000000000be030cb5728a0000000000009989d8917957000000000000999186917104000000000000a181c7917145000000000000957041917000000000000000b316dba54451000000000000b1428aa6a28a0000000000009949d4914954000000000000995104914104000000000000a14145914145000000000000ae5000914000000000000000b9128ab5a28a0000000000009919d1911951000000000000992104911104000000000000a1114591114500000000000095b00091100000000000000098f9cf90a94a00000000000099018690a104000000000000a0f1c790a14500000000000094a04190e0000000000000000000000000000000000000000000000000000000000000009250009252cb0000000000000000009259610000000000009250c39040000000000000009250009050c3 6 j))) (by decide +kernel)

def g59n54w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v11,g59v13,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n54 : Impossible false g59T 11 g59n54w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<1 then (linkRule g59n37w g59n37) else (if i<2 then (linkRule g59n38w g59n38) else (linkRule g59n39w g59n39)))))) (idx:=(fun j => bitsAt 0x8000a0001800010092401f1007a4018d005e401610057401490049400dd0035400cd0031400a4c08a301289034240c8903114184504a140d05032140c428a20a22828620a130284a0a0c8188a06130184a060c8068c01930064a018c805a1015840534014c4038a00d280332 18 (bitsAt 0xbdd79d7da555000000000000ada4d3a9a410000000000000b9a38e81d30c00000000000099b9dbb1aa5a00000000000089d514b1a2cb00000000000095c18699a0c300000000000099b28ab1a2490000000000009da08299a000000000000000ad5410a95410000000000000b5530c7de30c0000000000009969d6b15a5500000000000089e492b152cb0000000000009571459950c3000000000000996249b152490000000000009d5041995000000000000000ae3659a9030c0000000000009909d0aa7a22000000000000ad02cbaa12cb000000000000ad10c39900c30000000000009909d0a90249000000000000aa700099000000000000000098c9ccb18a5800000000000088c2cbb183cf00000000000094d0c398c0c300000000000098c9ccb0c2490000000000009d900098c0000000000000000000000000000000000000009a51c79a40c30000000000000000000000000000000000009a70009a410400000000000096520898b0c3000000000000000000b0b2490000000000009e704198b0000000000000009872479839c30000000000009831039870000000000000009a7000989104 6 j))) (by decide +kernel)

def g59n55w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v15,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n55 : Impossible false g59T 11 g59n55w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (linkRule g59n40w g59n40)))) (idx:=(fun j => bitsAt 0x20000402cd00af402710093401f1007a401c1006a4018d005e401610057401490049400d1000b30228c04a240d09032240c45062141285034140c850310a228284c0a128188a061281834060c81831026840961024c4064a018d00632016840561014d0053100e28034a00cc80331 18 (bitsAt 0x9de7deb9b596000000000000adb555a9b4d300000000000091b95bbde9de000000000000b5b492bde451000000000000a1e34db1b2cb0000000000008dd1c791b10400000000000091c95cbdb00000000000000095b0c391b041000000000000ad64d3a964d3000000000000916956b9f9df000000000000b56451b9f451000000000000a5f30cb162cb0000000000008d8186916104000000000000917957b96000000000000000956082916041000000000000913953a93993000000000000af069aa93451000000000000ad32cbaa02cb000000000000ad4104913104000000000000913000a93000000000000000aa50419130410000000000000000000000000000000000009252cbb212cb000000000000923104922104000000000000000000000000000000000000925041922145000000000000b512cbb192cb000000000000b63104911104000000000000000000891000000000000000b650419110410000000000008d028a90b10400000000000090f94fb0b00000000000000094b08290e041000000000000908248904000000000000000904144908041000000000000900040909145 6 j))) (by decide +kernel)

def g59n56w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v19,g59v23,g59v25,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n56 : Impossible false g59T 11 g59n56w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => failRule false g59T 10))) (idx:=(fun j => bitsAt 0x10093401f1007a401c1006f401a900634017900584015d005240125003440030c08a301289034240c8903114184504a140c8288a0a130284a06228184c061281834060c81831026840961024c4064c019280632016840561014d0053100e28036100d280332 18 (bitsAt 0x8db91ba1a99a000000000000a1d79da1a5d7000000000000ada596a1a514000000000000a1a4d3a1d4510000000000009dd34da1a2cb00000000000089c1c78da1040000000000008db91ba1a08200000000000091a0c38da0000000000000000000000000000000000000008e4514aa55140000000000008e4451a264510000000000008e430cb202cb0000000000008e21868e11040000000000000000000000000000000000008e40008e1145000000000000a17514a97514000000000000a17451a1e451000000000000a1e30cb172cb000000000000a221868d7104000000000000000000857082000000000000a240418d7000000000000000ae9659a14451000000000000ad42cba9f2cb000000000000ad51048d41040000000000008d4082a94082000000000000aa40008d4000000000000000a512cba182cb0000000000008921048d11040000000000008d1911a110820000000000009190008d10000000000000008902498cb1040000000000008cf28ab0b08200000000000090b0418ce0000000000000008c82888c40820000000000008c41448c80000000000000008c20008ca145 6 j))) (by decide +kernel)

def g59n57w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v19,g59v23,g59v29,g59v31]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n57 : Impossible false g59T 11 g59n57w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => failRule false g59T 10))) (idx:=(fun j => bitsAt 0x4024d007c401e9006a401a500634017900584015d005240125003440034c08a30128903214184504a140d05032140c4288a0a130284a06228184c061281834060c81831026840961024c4068c019280632016840561014d0053100e84038a00d280332 18 (bitsAt 0x8e46189e65d70000000000008e4514a655140000000000008e44519e64510000000000008e434dae02cb0000000000008e21c78e11040000000000000000000000000000000000008e40008e11450000000000009dd79d9dc5d70000000000009dc596a5c5140000000000009dc4d39dd4510000000000009dd34dadc2cb0000000000009e21c78dc10400000000000000000085c0c30000000000009e40828dc000000000000000a975149d75140000000000009d74519de451000000000000a1e30c9d72cb0000000000008991868d71040000000000008d89189d70c30000000000009170418d7000000000000000aa86db9d4451000000000000a942cba5f2cb000000000000a951048d41040000000000008d40c3a540c3000000000000a640008d4000000000000000a112cb9da2cb0000000000008921048d11040000000000008d19119d10c300000000000091b0008d10000000000000008902498cb1040000000000008cf28aacb0c300000000000090b0418ce0000000000000008c82888c40c30000000000008c41448c80000000000000008c30008ca145 6 j))) (by decide +kernel)

def g59n58w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v12,g59v13,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n58 : Impossible false g59T 11 g59n58w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<1 then (linkRule g59n41w g59n41) else (if i<2 then (linkRule g59n42w g59n42) else (linkRule g59n43w g59n43)))))) (idx:=(fun j => bitsAt 0x20002800060000402590084402090063401790052401450049400dd0035400cd0032400a8c08a301289034240c8903114184504a140d05032140c428a40a22828640a130284a0a0d0188a06130184a060d0068a01930064a018d0053400e84038a00d84034a00cc80331 18 (bitsAt 0xb9d79d7da555000000000000a9a4d3a5a410000000000000b5a38e81d30c00000000000095c99cadaa1a00000000000089d514ada2cb00000000000095c28aada20800000000000099b14595a00000000000000099a10495a041000000000000a95410a55410000000000000b1530c7de30c000000000000957997ad5a1500000000000089e492ad52cb000000000000957208ad52080000000000009960c3955000000000000000995082955041000000000000aa3659a5030c000000000000950990a669e2000000000000a902cba612cb000000000000951991a50208000000000000a90000950000000000000000a6604195004100000000000094c98cad8a1800000000000088c2cbad83cf00000000000094d98dacc20800000000000098c00094c00000000000000099904194c0410000000000000000000000000000000000000000000000000000000000009661c7964000000000000000966082964041000000000000000000acb2080000000000009a624994b0000000000000009a608294b0410000000000009481c7966000000000000000966186948041000000000000940040947186 6 j))) (by decide +kernel)

def g59n59w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v16,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n59 : Impossible false g59T 11 g59n59w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (linkRule g59n44w g59n44)))) (idx:=(fun j => bitsAt 0x8000100b3402bd009c4025d0084402090070401a90063401790052401450049400d1000e30228c04a240d09032240c45064141305034140c850310a228284c0a128188c061301834060c81831026840961024c4064c018d00632014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0x99e7deb5b596000000000000a9b555a5b4d30000000000008db91bb9e99e000000000000b1b492b9e4510000000000009de34dadb2cb0000000000008dd91db9b18600000000000091c1458db00000000000000091b1048db041000000000000a964d3a564d30000000000008d6916b5f99f000000000000b16451b5f451000000000000a1f30cad62cb0000000000008d8918b561860000000000009170c38d60000000000000009160828d60410000000000008d4914a53953000000000000aaf69aa53451000000000000a932cba602cb0000000000008d4186a53186000000000000a930008d3000000000000000a640418d30410000000000000000000000000000000000008e42cbae12cb0000000000000000000000000000000000008e40008e20000000000000008e40418e2041000000000000b112cbad92cb000000000000000000891186000000000000b240008d1000000000000000b240418d10410000000000008d0910acb18600000000000090f28a8cb00000000000000090b0828ce0410000000000008c82488c60000000000000008c61c68c80410000000000008c00408c91c7 6 j))) (by decide +kernel)

def g59n60w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v19,g59v23,g59v26,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n60 : Impossible false g59T 11 g59n60w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => failRule false g59T 10))) (idx:=(fun j => bitsAt 0x4025d0084402090070401bd006a4018d005e4014900514012500344003cc08c301289034240c8903114184504a140d0288a0a130284a06228184c061281834060c81831026840961024c4064c01928063401584053400e84038a00d84034a00cc80331 18 (bitsAt 0x89c8dc9da95a0000000000009dd79d9da5d7000000000000a9a5969da5140000000000009da4d39dd45100000000000099d34d9da2cb00000000000089c8dc9da1c70000000000008db14589a0000000000000008da10489a0410000000000000000000000000000000000008a3514a645140000000000008a34519e54510000000000008a330cae02cb0000000000000000000000000000000000008a30c38a10000000000000008a30828a10410000000000009d7514a575140000000000009d74519de4510000000000009de30cad72cb0000000000000000008571c70000000000009e30c38970000000000000009e3082897041000000000000aa86599d4451000000000000a942cba5f2cb0000000000008951c7a541c7000000000000a94000894000000000000000a63041894041000000000000a112cb9d82cb0000000000008928d29d11c70000000000008d10008910000000000000008d9041891041000000000000890249acb1c70000000000008cf28a88b0000000000000008cb08288e041000000000000889208887000000000000000887186889041000000000000880040888186 6 j))) (by decide +kernel)

def g59n61w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v19,g59v23,g59v29,g59v32]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n61 : Impossible false g59T 11 g59n61w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => failRule false g59T 10))) (idx:=(fun j => bitsAt 0x10097402110082401a900694018d005e40149005140125003440040c08a30130903414184504a140d05032140c4288a0a130284a06228184c061281834060c81831026840961024c4068a01930063401684053400e84038a00d84034a00cc80331 18 (bitsAt 0x8a36599a55d70000000000008a3555a245140000000000008a34929a54510000000000008a334daa02cb0000000000000000000000000000000000008a31458a10000000000000008a31048a104100000000000099d79d99c5d700000000000099c596a1c51400000000000099c4d399d45100000000000099d34da9c2cb00000000000000000085c1c70000000000009a314589c0000000000000009a310489c041000000000000a5751499751400000000000099745199e4510000000000009de30c9972cb0000000000008998d99971c70000000000008d80c38970000000000000008d7082897041000000000000a676db994451000000000000a542cba1f2cb0000000000008951c7a141c7000000000000a54000894000000000000000a230418940410000000000009d12cb99a2cb0000000000008928d29911c70000000000008d10008910000000000000008db04189104100000000000089028aa8b1c70000000000008cf24988b0000000000000008cb08288e04100000000000088a20888700000000000000088718688a041000000000000880040888186 6 j))) (by decide +kernel)

def g59n62w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v17,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n62 : Impossible false g59T 11 g59n62w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<2 then (if i<1 then (linkRule g59n1w g59n1) else (linkRule g59n8w g59n8)) else (if i<3 then (linkRule g59n16w g59n16) else (if i<4 then (linkRule g59n22w g59n22) else (linkRule g59n30w g59n30))))))) (idx:=(fun j => bitsAt 0x8001200038000a00018000100b3402bd009c4026d0099401c1006a4018d005e401610052401250037400d90035400cd001c40050c08a301289034240c89031141285034140c850310a228284c0a128188a06130184a060d01832060c4093101930064a018d00632016840561014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0xadf81fc5c618000000000000bdc5d7b9c555000000000000c1cb1cb9fadf000000000000c1c514b9f492000000000000b1fb1fb9c38e000000000000b1e249c9c186000000000000b1d145c9c000000000000000b1c104c9c041000000000000bd8555b98555000000000000c18b58ba0ae0000000000000c18492ba0492000000000000b60b60b9838e000000000000b5a208c58186000000000000b590c3c58000000000000000b58082c58041000000000000b95955ba4aa4000000000000ba6966b95492000000000000b9538eba338e000000000000bd6186b95186000000000000bd5000b95000000000000000be6041b95041000000000000000000000000000000000000000000000000000000000000c28186ba7186000000000000c29000ba7000000000000000c35041ba7041000000000000000000b9b38e000000000000c13186b92186000000000000c12000b92000000000000000c36041b9204100000000000091130cb8e18600000000000091034db8e00000000000000090e082b8f041000000000000dca2ca846000000000000000d061c688a041000000000000cc004084b1c7 6 j))) (by decide +kernel)

def g59n63w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v19,g59v23,g59v27,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n63 : Impossible false g59T 11 g59n63w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<1 then (linkRule g59n2w g59n2) else (if i<2 then (linkRule g59n9w g59n9) else (linkRule g59n31w g59n31)))))) (idx:=(fun j => bitsAt 0x200028000600004028d00a0401c1006f401a90063401790058401490049400dd0035400cd001d40054c08c30228c04a242289034240c8903114184504a0a22828640a18828610a130284a06228184c06128096101930064a018d00632016840561014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0xb1eadeb1aa9a000000000000b1e7deb1ab5a000000000000bda5d7b1a492000000000000b1a451b1e3cf000000000000adeadeb1a38e000000000000adc249b1a186000000000000adb145b1a000000000000000ada104b1a041000000000000000000000000000000000000b2d492ba9b64000000000000b2d3cfb2a75d000000000000000000000000000000000000b27208ba6186000000000000b280c3ba6000000000000000b2d082ba6041000000000000b2d492b9f492000000000000b2d3cfb1f3cf000000000000000000b9f38e000000000000b20208b9f186000000000000b1f0c3b9f000000000000000b2d082b9f041000000000000bed659b123cf000000000000b9238eba338e000000000000bd3186b92186000000000000bd2000b92000000000000000be5041b92041000000000000b4fb4fb1838e000000000000b50186b0f186000000000000b4f000b0f000000000000000b59041b0f04100000000000091630cb8e18600000000000091534db8e00000000000000090e082b94041000000000000c8a2ca846000000000000000c461c688a041000000000000c0004084b1c7 6 j))) (by decide +kernel)

def g59n64w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v19,g59v23,g59v29,g59v33]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n64 : Impossible false g59T 11 g59n64w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<1 then (linkRule g59n3w g59n3) else (if i<2 then (linkRule g59n10w g59n10) else (linkRule g59n32w g59n32)))))) (idx:=(fun j => bitsAt 0x20002800060000402a900a7401a900694018d005e401610052401250037400d5003340079001630228c04c301285061141285034140c850310a29028a20a284288a0a130284a06228184c0612809a101930064a018d00632016840561014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0xaab7dfaa9618000000000000aab492b28ae3000000000000aab3cfaa96db000000000000000000000000000000000000aa6249b25186000000000000aa7145b25000000000000000aab082b25041000000000000a9d7ddaab618000000000000aab514b1d492000000000000aab451a9d3cf000000000000000000b1d38e000000000000a9e249b1d186000000000000a9d145b1d000000000000000aab104b1d041000000000000b58492a98492000000000000a983cfa9f3cf000000000000adfadfa9838e000000000000ada208a98186000000000000ad90c3a98000000000000000ad8082a98041000000000000b6b71ca923cf000000000000b1238eb2238e000000000000b53186b12186000000000000b52000b12000000000000000b64041b12041000000000000acfacfa9b38e000000000000ad0186a8f186000000000000acf000a8f000000000000000adc041a8f0410000000000008d730cb0e1860000000000008d634db0e0000000000000008ce082b15041000000000000c0a2ca806000000000000000bc61c684a041000000000000b8004080b1c7 6 j))) (by decide +kernel)

def g59n65w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v21,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n65 : Impossible false g59T 11 g59n65w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<3 then (if i<1 then (linkRule g59n4w g59n4) else (if i<2 then (linkRule g59n11w g59n11) else (linkRule g59n23w g59n23))) else (if i<4 then (linkRule g59n33w g59n33) else (if i<5 then (linkRule g59n40w g59n40) else (linkRule g59n44w g59n44))))))) (idx:=(fun j => bitsAt 0x200058001200038000a0001800010070401a90063400dd0036400cd001f4005cc08a3012890a1240d09032240c45064141885061140d05032140c4288a0a130284a060d01832060c409a102584093101930064a018d00632016840561014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0xa218a1a1d5d7000000000000a5d596a21514000000000000a1d81da2169a000000000000a61410a1d38e000000000000a5f249a1d186000000000000a5e145a1d000000000000000a5d104a1d041000000000000a97514a22514000000000000a17697a22820000000000000aa23cfa1738e000000000000a99208a17186000000000000a980c3a17000000000000000a97082a1704100000000000000000000000000000000000099438e9a538e0000000000009951869d41860000000000009940009d40000000000000009a70419d40410000000000009e738ea1a38e000000000000c1c186a1a186000000000000bdb000a1a000000000000000b5a041a1a0410000000000009d330c98e1860000000000009d234d98e0000000000000009ce082991041000000000000b8a2ca8c6000000000000000b061c690a041000000000000ac00408cb1c7 6 j))) (by decide +kernel)

def g59n66w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v19,g59v23,g59v28,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n66 : Impossible false g59T 11 g59n66w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<3 then (if i<1 then (linkRule g59n5w g59n5) else (if i<2 then (linkRule g59n12w g59n12) else (linkRule g59n17w g59n17))) else (if i<5 then (if i<4 then (linkRule g59n27w g59n27) else (linkRule g59n34w g59n34)) else (if i<6 then (linkRule g59n37w g59n37) else (linkRule g59n41w g59n41))))))) (idx:=(fun j => bitsAt 0x200068001600048000e000280006000040279009c401c1006f401a5006340189005e401610052401250040400ad0020400610011301289034240c8903114184504a140d05032140c4288a0a130284a06130184a060d01832060c409a102584093101930064a018d00632016840561014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0xadeb1eae6b25000000000000ae1b21ade659000000000000b5e618ade596000000000000adeb1eae1514000000000000b61410ade38e000000000000b60249ade186000000000000b5f145ade000000000000000b5e104ade041000000000000000000000000000000000000baf596aea596000000000000000000000000000000000000baf38eaec38e000000000000ba8186ae7186000000000000ba9000ae7000000000000000baf041ae7041000000000000b99596ad9596000000000000000000aec514000000000000baf3cfad938e000000000000b9b208ad9186000000000000b9a0c3ad9000000000000000b99082ad9041000000000000c2c75dad6514000000000000c1638ec2238e000000000000c57186c16186000000000000c56000c16000000000000000c75041c16041000000000000c1438eadc38e000000000000c15186ad4186000000000000c14000ad4000000000000000c1d041ad4041000000000000e1330cc0e186000000000000dd234dc0e000000000000000d0e082c11041000000000000d8a2ca8c6000000000000000cc61c690a041000000000000c800408cb1c7 6 j))) (by decide +kernel)

def g59n67w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v19,g59v23,g59v29,g59v34]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n67 : Impossible false g59T 11 g59n67w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<3 then (if i<1 then (linkRule g59n6w g59n6) else (if i<2 then (linkRule g59n13w g59n13) else (linkRule g59n18w g59n18))) else (if i<5 then (if i<4 then (linkRule g59n28w g59n28) else (linkRule g59n35w g59n35)) else (if i<6 then (linkRule g59n38w g59n38) else (linkRule g59n42w g59n42))))))) (idx:=(fun j => bitsAt 0x200068001600048000e000280006000040279009c401bd006a401a5006340189005e4016100524012500444008d00214006500123022890a1242289034240c89031140d05032140c4288a0a130284a06230188a060d01832060c409a102584093101930064a018d00632016840561014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0xaec659aec9a5000000000000b6e618aea596000000000000000000000000000000000000b6e38eaec38e000000000000b68186ae7186000000000000b69000ae7000000000000000b6e041ae7041000000000000aec861adc659000000000000b5c618adc596000000000000000000aec514000000000000b6e410adc38e000000000000b5e249adc186000000000000b5d145adc000000000000000b5c104adc041000000000000bd9596ad9596000000000000ad9b19ae1514000000000000be13cfad938e000000000000bdb208ad9186000000000000bda0c3ad9000000000000000bd9082ad9041000000000000c2c820ad6514000000000000c1638ec2238e000000000000c57186c16186000000000000c56000c16000000000000000c75041c16041000000000000c1438eadf38e000000000000c15186ad4186000000000000c14000ad4000000000000000c20041ad4041000000000000e1330cc0e186000000000000dd234dc0e000000000000000d0e082c11041000000000000d8a2ca8c6000000000000000cc61c690a041000000000000c800408cb1c7 6 j))) (by decide +kernel)

def g59n68w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v19,g59v23,g59v29,g59v35]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n68 : Impossible false g59T 11 g59n68w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 10) (fun i => (if i<3 then (if i<1 then (linkRule g59n7w g59n7) else (if i<2 then (linkRule g59n14w g59n14) else (linkRule g59n19w g59n19))) else (if i<5 then (if i<4 then (linkRule g59n29w g59n29) else (linkRule g59n36w g59n36)) else (if i<6 then (linkRule g59n39w g59n39) else (linkRule g59n43w g59n43))))))) (idx:=(fun j => bitsAt 0x200068001600048000e00028000600004029500a1401d90075401bd006a401a5006340189005e40161005240125002340089001a30284c08c30228c06130130c04a14184504a0a228284c0a128188a06130184a060d01832060c409a102584093101930064a018d00632016840561014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0xaec5d7a685d7000000000000a6a514a6a514000000000000aec3cfa6a38e000000000000ae6208a65186000000000000ae70c3a65000000000000000aec082a65041000000000000000000a6aaa4000000000000ade659a5c5d7000000000000a6a596a5c514000000000000adc410a5c38e000000000000add249a5c186000000000000adc145a5c000000000000000ade104a5c041000000000000b615d7a5f5d7000000000000a6a514a5f514000000000000b5f3cfa5f38e000000000000b60208a5f186000000000000b5f0c3a5f000000000000000b61082a5f041000000000000c6a6dba57514000000000000c1738ebaf38e000000000000c58186b97186000000000000c57000b97000000000000000c75041b97041000000000000a9438ea5a38e000000000000a95186a54186000000000000a94000a54000000000000000a9b041a54041000000000000e1330cc0e186000000000000dd234dc0e000000000000000d0e082c11041000000000000d8a2ca886000000000000000cc61c68ca041000000000000c8004088b1c7 6 j))) (by decide +kernel)

def g59n69w : List Sig := [g59v1,g59v2,g59v4,g59v8,g59v13,g59v19,g59v23,g59v29]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem g59n69 : Impossible false g59T 12 g59n69w.toFinset :=
  checkNode_sound (rules:=(codedRule (g59Cuts 11) (fun i => (if i<12 then (if i<6 then (if i<3 then (if i<1 then (linkRule g59n45w g59n45) else (if i<2 then (linkRule g59n46w g59n46) else (linkRule g59n47w g59n47))) else (if i<4 then (linkRule g59n48w g59n48) else (if i<5 then (linkRule g59n49w g59n49) else (linkRule g59n50w g59n50)))) else (if i<9 then (if i<7 then (linkRule g59n51w g59n51) else (if i<8 then (linkRule g59n52w g59n52) else (linkRule g59n53w g59n53))) else (if i<10 then (linkRule g59n54w g59n54) else (if i<11 then (linkRule g59n55w g59n55) else (linkRule g59n56w g59n56))))) else (if i<18 then (if i<15 then (if i<13 then (linkRule g59n57w g59n57) else (if i<14 then (linkRule g59n58w g59n58) else (linkRule g59n59w g59n59))) else (if i<16 then (linkRule g59n60w g59n60) else (if i<17 then (linkRule g59n61w g59n61) else (linkRule g59n62w g59n62)))) else (if i<21 then (if i<19 then (linkRule g59n63w g59n63) else (if i<20 then (linkRule g59n64w g59n64) else (linkRule g59n65w g59n65))) else (if i<22 then (linkRule g59n66w g59n66) else (if i<23 then (linkRule g59n67w g59n67) else (linkRule g59n68w g59n68))))))))) (idx:=(fun j => bitsAt 0x200178005a00158005200138004a001180042000f8003a000d80032000b8002a00098002200078001a00058001200038000a0001800010037400d5002b4008d001b4004d000030228c04a240d09032240c45061141285034140c850310a228284c0a128188a06130184a060d01832060c409a102584093101930064a018d00632016840561014d0053100e84038a00d84034a00cc80331 18 (bitsAt 0x84891a24e7cd1a00000000000000547cc99527cb9700000000000000827cb165088a14000000000000007c88810527c70e0000000000000076844894c7c306000000000000006e802854a7c00000000000000000647c204507c081000000000000005468b975268b97000000000000008068a144e8ca14000000000000007a8c78f526870e0000000000000074704084c68306000000000000006c6c1834a680000000000000000062681024e680810000000000000054fcf1e525ca1400000000000000525c70e529070e000000000000005460306525c30600000000000000545c000525c0000000000000000054c0081525c08100000000000000785070e527470e0000000000000072543064c50306000000000000006a500004a50000000000000000005e780815c5008100000000000000704c60c523830600000000000000684868d5238000000000000000005a38102524408100000000000000662858a4a180000000000000000058183864c280810000000000000056000804a2c387 7 j))) (by decide +kernel)

theorem bound59 : Lower false (raw 8) g59T 13 := finishBound g59Ok g59n69

end PEqualNP.Outside.L_meta_8511

theorem PEqualNP.Outside.L_meta_8511 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 4 && x 7) || (x 6 && x 7)) t → 13 ≤ t := by
  exact PEqualNP.Outside.L_meta_8511.from_modes PEqualNP.Outside.L_meta_8511.bound59 PEqualNP.Outside.L_meta_8511.bound18
