import Mathlib
import PEqualNP.Defs

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- The bound below specializes dsgallups’s proof from open-goat/pequalnp-proofs pull request 8897.
-- Source revision f89b7e67bb82580a58b7db69af1bcc8b72754161, Apache-2.0.
-- Mode true is retained for shared bounds on restricted subgraphs.
namespace PEqualNP.Outside.L_meta_4463.FullBound
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
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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

private lemma extract {u target} (gs : List Gate) (w : List Sig)
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

private lemma b_read (i) (w : List Sig) (j : Nat) :
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
  simp only [b_read]
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

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := inputs.getD 0 zero ||| inputs.getD 3 zero
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 || sample r 3) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

theorem initial_live (C : Circuit) (monoC : PEqualNP.MetaComplexity.Monotone2 C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k S, k ≤ 14 ∧ Live false graph k S ∧ ∀ a ∈ S, a ∈ inputs++[seed] := by
  have legal : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨kind,arity⟩ := monoC g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at kind ⊢
    exact ⟨kind.elim Or.inl (fun h => Or.inr (Or.inl h)),arity⟩
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply bit_ext
    intro r
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply bit_ext
    intro r
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at goalEq
    change (execute gs (inputs++[gv inputs g])).getD C.output zero = graph at goalEq
    rw [eq0] at goalEq
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    have mono : false=false → ∀ gate ∈ gs, isNot gate=false := by
      intro _ gate hg
      have member : gate ∈ C.gates := by
        rw [hgs]
        exact List.mem_cons_of_mem _ hg
      have kind := (monoC gate member).1
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at kind
      rcases kind with hand | hor
      · simp [isNot,hand]
      · simp [isNot,hor]
    have count : gs.countP (fun g => !isNot g) ≤ 14 := by
      have h := List.countP_le_length (p:=fun g => !isNot g) (l:=gs)
      omega
    have out := get_rep (u:=false) (execute gs (inputs++[seed])) C.output
    rw [goalEq] at out
    unfold Repr at out
    have pg : bit 0 graph=false := by decide +kernel
    rw [nrm_id pg] at out
    have targetIn := out.resolve_right (fun hn => hn graph_proper)
    obtain ⟨k,S,hk,run,hs⟩ := extract gs _ tailLegal mono graph_proper targetIn
    have ns : (inputs++[seed]).all plainWord=true := by decide +kernel
    rw [nrm_map ns] at hs
    exact ⟨k,S,by omega,run,hs⟩

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
def varsX (m : Nat) : List Sig := if m.testBit 9 then vars m ++ [seed] else vars m
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
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

def supportPairs (w : Bool) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if w && i==0 then 8 else if w && i==3 then 1 else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {u m hints L} (h : assertSize m hints L = true) :
    Lower u (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m ^^^ (m &&& (c.1 &&& 512))
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (free.testBit 9) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (free.testBit 9) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem relabel_of {u old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


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


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
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

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
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
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
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

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut g.mode (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (varsX (rawMask g.mask ci)) (vars g.mask)=true) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {u old L m relabels} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known u (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (u : Bool) (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m) ||
    (u && (p.wires.map (masked p.domain)).any (fun v => v==(p.domain ^^^ m)))
theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
theorem available_mask (u) (p : BoundPool) (x : Sig) :
    availableB u p.domain p.wires x = availableMasked u p (masked p.domain x) := by
  simp only [availableB,availableMasked,masked_comp]

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (u : Bool) (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB u p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b kb + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (al : allowedB u op=true)
    (h : fastCost (summarizePool u ws p) k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB u p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB u p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl (Or.inl zc)
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB u p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB u p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b ka kb).subset hw)
    have opOK : choiceOK u p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb,al]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.2.1.2 c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (al : allowedB c.2.2.2.1.2 op=true)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) al ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
      ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if (i<c.2.2.1.length ∧ j<c.2.2.1.length) ∧ allowedB c.2.2.2.1.2 op=true then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1.1 yes.1.2 yes.2 h
    next => contradiction
  · exact h
def batchMove (u : Bool) (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at {u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u)
    (pass : batchMove u (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (u : Bool) (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove u b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (u : Bool) (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair u b xs i j))
def batchRows (u : Bool) (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow u b xs i js && batchRows u b xs js

theorem batchRows_at {u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows u (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode pass.1.1.1,check hi hj' hq budget arity mode pass.1.1.2⟩,
      check hi hj' hq budget arity mode pass.1.2⟩,check hi hj' hq budget arity mode pass.2⟩

def runBatch (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows u (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow g.mode b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow g.mode (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows g.mode (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {u} {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut u one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible u (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

def rootB (m : Nat) : List Sig := vars m ++ [seed]

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

def splitPairs (l : List (Nat × Nat)) : List (Sig × Row × Row) :=
  l.map fun (i,r) => (inputs.getD i zero,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def splitOK (m : Nat) (l : List (Nat × Nat)) : Bool :=
  let xs := splitPairs l
  checkEssential (graphGoal m) (rootB m) xs && (xs.map Prod.fst == vars m) && properB (graphGoal m)

theorem strong_split {u} {m l} (ok : splitOK m l = true) {k : Nat} {S : Finset Sig}
    (h : Live u (graphGoal m) k S) (sub : ∀ v ∈ S, v ∈ rootB m) :
    S=(vars m).toFinset ∨ S=(rootB m).toFinset := by
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq] at ok
  obtain ⟨⟨ess,alls⟩,_⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := essential_ok ess v (List.mem_toFinset.mpr hv)
    exact raw_required h (rootB m) v sub r s hd hi
  by_cases hs : seed ∈ S
  · refine Or.inr ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨sub v,fun hv => ?_⟩
    rcases List.mem_append.mp hv with hv | hv
    · exact rest v hv
    · rwa [List.mem_singleton.mp hv]
  · refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨fun hv => ?_,rest v⟩
    rcases List.mem_append.mp (sub v hv) with hv' | hv'
    · exact hv'
    · exact absurd (List.mem_singleton.mp hv' ▸ hv) hs

theorem strong_low {u} {m l cap} (ok : splitOK m l = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset)
    (b : Impossible u (graphGoal m) cap (rootB m).toFinset) :
    Lower u (rootB m) (graphGoal m) (cap+1) := by
  have ok' := ok
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live (proper_of _ ok'.2) (essential_plain ok'.1.1).1 (essential_plain ok'.1.1).2 hr ha
  by_contra! small
  rcases strong_split ok run hs with e | e
  · exact a k (by omega) (e ▸ run)
  · exact b k (by omega) (e ▸ run)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower true (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def known3 := extendKnown [] 1 [(12,[49,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known true known3 := extendKnown_ok (m:=3) baseKnown low3 (by decide +kernel)
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,1,0,0,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xefe47cfaf79fcbe2267eff82033cfbeeb8ffe977f4f9cbdc18acec7fcf75aafdffdd73ef57ceff77f9f3c69fef3aba8bc60e65baef3608e7d155c295bd604db07a7fa33ff1da267d7faf155d5d3b284e7df8b57ed3ebf3d93ee7ca6f3c47473,0x362118ac45916a9d02222292091025e029311c08210147faa44c85bd94a89bfc029b3023630ad4268a551db8a04260300e6a101419c00907c94709580b244a221a32941f500020046b12be00c1022a20825c0800009d60c00c99dd6a5373652),(0xffdbfbffffb9fdacebfbfeffffbeb7fe5f7deee77ebffa7f9e57ed236c3ffedbeffff77ef65d33fcefdd1fffeb7fff7f9f0b7b4fa1eb7f7af7af7ef7f24f35ffde5d99797b9da1feda7bbde3c25aff4577f6cf7ff5776f3fd8da5daee9e97a7f,0xb890ec001102e9102c414c828844b900b84480200501228000a315802011224005c008494008000891022c00455200746b0910ee24210209030803400504ba0448100480000e41fb200a000f21a4085cb0980651e39620d1311200091888c829),(0xf7a5fe75d0eef75bdffe135fffeffac3fdff157aebf8ffcfffff7fffbfddf5f5bcc6fef31fa7ff9f977fffb6d5ac56d767ff9ffd5f1ddff7aafbffdfbff9fb64fffbfffe9eeedf9d7dbddebebfbfcdfbfeebfdff1fedf3e36f77f77b7eff8f9c,0x420000b6080008b10028125029302384439010200b840088c404824cda644328204061021844047682141908a00ea09801484018106f04240c45011988244d2800428011180860403800a600e11040302050082006844200000970041221714),(0x1034b7f7c54637fbbf9df36abcd7cdafbbbe77dff94045836dfe73fcdff3e726dd347ddfebbeffeb77f2f673bcadb4916efed7fcdf5eefcd8d5693fdeff6effafff6eedfefe3df1d759cc23cbfff64ffcb1d7ba06fbafdcb776db2d977d68de0,0xe98f99f410317a046ed922cabd2095808b842221ec47b15242be0242124188c855bab1620a23b88080900c22107e15922841688c74e9059c8c39a8864264210d3af003ea604c79f0246b0405b026fb8ca8c2dd69b1031955e4f520d92e1de8e0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : List ColumnInfo := []
def g15autos : List (List Nat) := [[],[48,33]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
set_option maxHeartbeats 0 in
theorem geomg15 : graphValid g15 (boundsBefore known3) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg15_3 : block g15 3 0 1=true := sg15_3_0
theorem tablesg15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact allg15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (vars 15) (graphGoal 15) 4 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g15) (i:=0) rfl rfl (before_sound known3 valid3) geomg15 tablesg15 (by decide +kernel))
def known15 := extendKnown known3 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(270,[131,115,99,83,50,33,16,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(420,[131,33,114,99,32,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known true known15 := extendKnown_ok (m:=15) valid3 low15 (by decide +kernel)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,0,0,0,0,g31d6)
def g31h6 (i : Nat) : Nat := 0x30be670208000065000016357504004755c084
def g31d5 (i : Nat) : Nat := 0x40828fd20fd10
def g31l5 : Packing := (2,1,3,0,0,3,0,g31d5)
def g31h5 (i : Nat) : Nat := 0x300
def g31d4 (i : Nat) : Nat := 0x5dd4520
def g31l4 : Packing := (1,2,3,0,0,0,0,g31d4)
def g31samples : Array (Bits × Bits) := #[(0x4cd435b1cff89bfcf3403d6ffb5e7b6fb6f0a252750d8f3e775f7a4b35bf17ffc1f1f68f49aff3f97ef5dcbffcecfb8b347fdad1b97ee9eab1fef35bbda93bdefe31d48e2e2a2deece0b774332650ab9592b7ca4c3cce37238ad15d16630b273,0x6412e45418036809b01888acb04128982824834415c30405900032d41009c80d02002180b020200430601201640641a1dc0065180e101002a04090026300c7840041c50020480001612a04d9391609200802d008345020001011525c6a12412),(0x73bc6673e6f7fb127e7edfbb35afbc3c7aeffeffb7b36ea15203b3fb0b23d71ae7293cfd7c6b76afff7f9f42ce524641ef74bc7775f5b7beeca9fab64d8d2f057df75fd7b06effadf147566865d776d67ddf9c9eb9cb59bcc3fa90c286464e7f,0x4806818a3a130032401c024400212c065450b14218830380207b40c01250613908c5d427709991c028a8485ce128038122240884600438f10480e460400470023480c0a07020209088601130006682403032d0b168a010b80406c2d009524869),(0xeffcdbd0ce5fec73cdbefbd7def1b1c3790e5bae99dff1cd23a5cdbe62c5eb058a465b7eeb5addf6c9bef153e11a35ff6fd5cffe7bafe6b6139b5cefe3db14c795e58371dbcbcdf57fd9ef3c55f2f3464a77dfd974753609f3f58c06d986cd9c,0x4b01000c04008000621253b644c50e809a00699020cd8131084993ead068806811a01c884244431950203000a8190020900540a0b5a4408737901010110004480543053884a8000640226cc4c080818cecc0800000c61443029290662058794),(0xfefbbd6efc554e65d6d32e9e9fc8c5f7fb2bc7bd6e78ffd4c9b6fe5fece47b85feefcd40df76eb99e3fb3fd3cb117c3cbbc927b8bed59f45ff184d509bdff7bf9d8ffb224ff7161ad1bfbf9e9d09ef7ea6dcdb5fcfb76f877dce7e6c59e90980,0x58028e420d9b06420152488082b0860302440920c440010ca45200404030002150200002090a92880845042a20140600940201002080830504028c00a6850d1a3023ca2055a006690040d9028207c2821022259824200c0a8056166995b04820),(0xb18f7a8e312b6eee7925dbddcc1fee96cd7fc4dd4f7ddebefdfa8c25bff986e3b4d8e33b16acabff13c446edb2bdfdc6fb8ffc188e9ad9615cc76daf377cf7ff5a7faa5f85f437c63e34eadbee7b7fedacedbfe7afdacfc62f3febbb2079b000,0xa03c4000a02001010084164514412920290832083a8244020024b0009ac3600405989c25c0540d2310a0a051892311c50039502e45183000409152a0594030840798200c00182012602d04806c600d6c895912670092f1752200e892284e92c0),(0,0),(0,0),(0,0),(0,0)]
def g31columns : List ColumnInfo := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def g31autos : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def g31levels : Nat → Packing
  | 6 => g31l6
  | 5 => g31l5
  | 4 => g31l4
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 15 3 9 1 4 g31h6
  | 5 => lookupWord 1 3 1 9 1 4 g31h5
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
set_option maxHeartbeats 0 in
theorem geomg31 : graphValid g31 (boundsBefore known15) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg31_6 : block g31 6 0 1=true := sg31_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg31_5_0 : block g31 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg31_5 : block g31 5 0 2=true := sg31_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg31_4_0 : block g31 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg31_4 : block g31 4 0 1=true := sg31_4_0
theorem tablesg31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact allg31_4
  · exact allg31_5
  · exact allg31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (vars 31) (graphGoal 31) 7 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g31) (i:=0) rfl rfl (before_sound known15 valid15) geomg31 tablesg31 (by decide +kernel))
def known31 := extendKnown known15 7 [(31,[]),(167,[115,67,100,83]),(313,[131,115,65,50,98,81]),(334,[131,115,100,50,33,16,80]),(355,[131,50,66,116,99,82]),(428,[130,50,116,49,32,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known true known31 := extendKnown_ok (m:=31) valid15 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (vars 47) (graphGoal 47) 5 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known31) (before_sound known31 valid31) (8,0,39,0,4) (by decide +kernel) (by decide +kernel))
def known47 := extendKnown known31 5 [(47,[]),(61,[50,65]),(94,[101,50,33,16,64]),(157,[117,101,33,32,65,48]),(173,[113,97,82,32,65,48]),(181,[114,81,98,50,65]),(188,[114,83,48,33,97,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known true known47 := extendKnown_ok (m:=47) valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (vars 55) (graphGoal 55) 5 := plain_low (hints:=257) (by decide +kernel) (cut_root (prior:=boundsBefore known47) (before_sound known47 valid47) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def known55 := extendKnown known47 5 [(55,[]),(79,[101,50,33,16,64]),(376,[128,80,84,66,16,114,97,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known true known55 := extendKnown_ok (m:=55) valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (vars 63) (graphGoal 63) 8 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known55) (before_sound known55 valid55) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))
def known63 := extendKnown known55 8 [(95,[101,66,16]),(159,[117,101,67,32]),(231,[83,82,114,99,66,16]),(335,[131,115,100,50,33,16,80]),(350,[132,116,84,48,33,96]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known true known63 := extendKnown_ok (m:=63) valid55 low63 (by decide +kernel)
def g111d6 (i : Nat) : Nat := 0x7213f
def g111l6 : Packing := (1,0,2,0,0,0,0,g111d6)
def g111h6 (i : Nat) : Nat := 0x8000
def g111d5 (i : Nat) : Nat := 0x17e51
def g111l5 : Packing := (1,1,2,0,0,0,0,g111d5)
def g111samples : Array (Bits × Bits) := #[(0x9da83de5fe85dcb1fb131acda7cb7fa6fdfff53ffdd1e39f470edae98ffa779fed3d49cfd7ff65f391fe43c4c2da557b3d0f9d8be4df9a25abffffe06fcbe9b6b53bd9766e67796e1eeaf292d828fb3adaf06cf9f65f62d506dc8c692839f653,0x99520888bc441a08808188400f9006aa38027780804108a42161480404a0859200848c260034430011281a00001040102808090028e048448151413038494402ef0282859485e014128040a031e08189c0242002180cb0f04d190d4828112652),(0x6f53eedf3e34f5ed54d6bf7e1fff0f7d43ff9f667beb1928ff77d9f5ed55ffb67fdcbbddf3e7bdfffefaea5d6eb4a6e7e6a7cf77d8cd6f9e6efafc7fdfdeb6fdcfbf3ddb8fe9ff16e7f6fde5b7df4e2b3f7ab38deae871aa3b7e53917e26487f,0x481021100a000100108101780404041002808480c08a0020002124a0342680014000000844000232a0144083100240441210022000b043800080a8100060894002450004058086320280100000c0800154100100300000a02a6201004224829),(0x74d5ebbdd9eb9a5fb6bd77dfeba4bccb17df28cb12ed7fee19f56f97fa519e4bf2d75c34e8c49b0766e7bdbaf577997b977e76cf6b3ecf79f39a2c5e50376d1f6d65bbd375353bfb16bf97bf67b9f1c7fb85b75ebbe5dd44c503731eb1c38f9c,0xb12000680454a1c0c087a9606d1536a406041301012650455d3020a52438021a8344900a60298a04c004231000f110120a802b50ac0008815607500a1111106904088181288361005301861081a1a010a20cc180541841449d09c60531818514),(0x1dd56f6145df333f162dd2d77f55f59b1cd7a7e5040f75cd4be0664bd92ebe4d0eb327fbca83265c648d75abbbad8eb391fb79d777e660573e7923c237a7079d28f5bf281f3d5dfdb599030bc8722dc56dad83fbabc5bed8c223200ec1fc0fc0,0x40dab5921b2b1c0c3c004217906840189039604c20d18490028e874801c42925001345400102344b015084adb40e8244603e402703f8f54a880000d1a2864a0608a71c78072494aea88479a4385c166604622654280736bb62f6391ac07c0ac0),(0,0),(0xf12e51fe9df15d5afdd0233cf761e695b8e9777faf7ce3fb672f367982ef85f5e529cf3eeeb847a76de6ddb3265a731cacb7a2abf493f3688135a3826951fc8a3ee7cdaeef723df5ec7cad13a8e4df56a8264f25fdbbc71d0482cce001fff020,0x62d3466409165346f5872bf3026700142488812448c6140860a0029fa5d70408079439078c0388e844721ae876284270536d4f51410100a66a4a8c20326809d10003048687a0b014d0c2b1cc8080210140282d542c00f0fb0c6f2b181eed020),(0xf7c326c3fabb7b0765ec93ba313dac9b402a6356d93b6b34b7389b77043e973c1898ab9d236f96cd5df8f8cd0cb436c774f0b8fedc8023ff072ee8d5e4afb6700fccc6798ab99e23e7c6a9e292ee6cbdcefb92e6f289f7fe3c2000ee7f040020,0x9064ad20c50183c09a1704001d148a08a19293a273a447c8f1ac0da09c0d828d8ad36b8968a6a59c05121bd78a4a9808b68cdd91a9f0e843e4317020e8a87202230b20b0a70636001ec20c820b6063c8421e718af411cff5fd599feffb040000),(0,0),(0,0)]
def g111columns : List ColumnInfo := [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def g111autos : List (List Nat) := [[],[32,83]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | 5 => g111l5
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 1 6 1 1 g111h6
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
set_option maxHeartbeats 0 in
theorem geomg111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg111_6 : block g111 6 0 1=true := sg111_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg111_5_0 : block g111 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg111_5 : block g111 5 0 1=true := sg111_5_0
theorem tablesg111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact allg111_5
  · exact allg111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (vars 111) (graphGoal 111) 7 := plain_low (hints:=16785665) (by decide +kernel) (index_root (g:=g111) (i:=0) rfl rfl (before_sound known63 valid63) geomg111 tablesg111 (by decide +kernel))
def known111 := extendKnown known63 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(413,[134,117,33,32,65,48]),(427,[98,134,114,66,81]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known true known111 := extendKnown_ok (m:=111) valid63 low111 (by decide +kernel)
def g189d7 (i : Nat) : Nat := 0x163441bf
def g189l7 : Packing := (1,0,3,0,0,0,0,g189d7)
def g189h7 (i : Nat) : Nat := 0x42f9f28c08140000000020f801630c00d0
def g189d6 (i : Nat) : Nat := 0x420a3fa41fd10
def g189l6 : Packing := (2,1,3,0,0,3,0,g189d6)
def g189h6 (i : Nat) : Nat := 0x18000
def g189d5 (i : Nat) : Nat := 0xb7d8d20
def g189l5 : Packing := (1,2,3,0,0,0,0,g189d5)
def g189samples : Array (Bits × Bits) := #[(0xb1dc1ff7132a7ff6e7954acdad6bfbbb4172275f57d485efe917eeb71c7ff77e0f2710edeec09b154b6e1e5d7bf54df3f4dd5c7dd4938defdfccf59eee87375ef5552cb6bdff87f9e5f8848f37877351ffebb95fb54e1da64108012bd832f47c,0x68087423000a3a003112a000082c31440020146209e00a2443b08826a2c783c22a2018806d009402af4218903314000c10804096c64039005c40804a8011202bd030a10649200641113e224050005040170804503a1d85960021199906a42c),(0,0),(0xeb6f6506f1e2aa6dee226de156ddffe904e57beead59704513e2e966ffdb64a3f7b8db55bb1f1a9e751d7de33b4c6bc392f42ec374ecbbaf3654c836729be4baa8a1b0743f347b7afe536de5ff5b19289bf0a963347bac458a9750042f2dc84f,0x8c001201c00cc1400602117d41024270201114400481224201e24010180010022d208a08699a408210701c624230158998b14904166522504000040900a44c6294a080304188c2f28062010c468083210010d400081004c61e4544061425c84a),(0xf66bc486edbf6752992cfed2569e9459bf37bdf6868a4b581370516e15408dc4ead6b1da975dc462fef725ca8dda991ebd300aea78456370ee844f979859bc9f5deafd42e2387048ee48d79c7ef3f0ec585564e64ffb9958e417a60021ce0f8f,0x141086c23420024210c2e0290d88c82820ac202680cd018140488056065c915925900519600091c4b00c089b40a0022400aa272c09048ab84edc29000421199610c4d05046325013709168300783810a1650947c0cd1909e00a3a18e18a0685),(0x1be0dbb4733b3fdea539db5dc1e40d61ba397321deabaa5c9e79b42d6566bd396bf515996fe7f57983f51a71a1c9badeffcf76fe239904dffc789ed507f54ab9755fcbae7d5aee82615d191ef4348fdd8cad469fbbb1e7780400a62f50f10f70,0xf886400208099000c642c1096206000038a409a0950205800a30027081080008088082862810e023841034204100e14580a5518500089440510000452509ea42100302125980d25800a64140368043861e0852880700e27201f4c42600710950),(0x759515f9d7ee0bf78df1fe7ad5afa9eeb6e9dbe6bad8fb76e9e7bd41f896f6f2536247ecf382b95e96bd25e7fbf1effa33ed91b9f56ce6009f37fe8fd2fbfefc6ee8f4dccf1e8bf40aea3c197b6fe1aee129e4ecf84d2c2796909d080fbf080,0xe680c60358033181540c800939169140001cc0400dc000a449800201185038442c4008c00182424219509c4046080205b1a3722e08011b4068200a0191200c0590000b4630001261b08c0188068aa2ac082052898240c042684f5e8240f95000),(0,0),(0xfc3e2eb86c64e5fbbe7379bb3583650f2e89c5febf79f8f98fbf1cf7eff53fb3dbe9ffcbe6ffec89ecb8cf31f5e3fad6ef7bf308cfabf802587fcdf187b949b9272cda3b78452b96bae7ffe5cf4ddef209ee4bcee6cdfb3dbae059d52e010080,0x110000ac26800e3ea1d16e0284202c86df220182b02850109605b58242288018d2926115124094018005428c88860010424c8080e09a042f000c31240a4b3300091d04818606250c00111e2329000402254b002641093b3981b0a179ab000080),(0,0)]
def g189columns : List ColumnInfo := [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def g189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def g189levels : Nat → Packing
  | 7 => g189l7
  | 6 => g189l6
  | 5 => g189l5
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 9 13 2 9 1 4 g189h7
  | 6 => lookupWord 1 3 1 9 1 4 g189h6
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
set_option maxHeartbeats 0 in
theorem geomg189 : graphValid g189 (boundsBefore known111) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg189_7 : block g189 7 0 1=true := sg189_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg189_6_0 : block g189 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg189_6 : block g189 6 0 2=true := sg189_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg189_5_0 : block g189 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg189_5 : block g189 5 0 1=true := sg189_5_0
theorem tablesg189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact allg189_5
  · exact allg189_6
  · exact allg189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (vars 189) (graphGoal 189) 8 := plain_low (hints:=536879876) (by decide +kernel) (index_root (g:=g189) (i:=0) rfl rfl (before_sound known111 valid111) geomg189 tablesg189 (by decide +kernel))
def known189 := extendKnown known111 8 [(189,[]),(303,[135,50,65]),(347,[130,50,98,82,115,33,65]),(486,[115,83,82,130,99,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known true known189 := extendKnown_ok (m:=189) valid111 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (vars 127) (graphGoal 127) 9 := plain_low (hints:=16785665) (by decide +kernel) (cut_root (prior:=boundsBefore known189) (before_sound known189 valid189) (32,0,95,0,8) (by decide +kernel) (by decide +kernel))
def known127 := extendKnown known189 9 [(127,[]),(223,[117,67,32]),(239,[116,83,32]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known true known127 := extendKnown_ok (m:=127) valid189 low127 (by decide +kernel)
def g191d10 (i : Nat) : Nat := 0x8201ff
def g191l10 : Packing := (1,0,5,0,0,0,0,g191d10)
def g191h10 (i : Nat) : Nat := 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def g191d9 (i : Nat) : Nat := 0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40
def g191l9 : Packing := (12,1,5,0,0,10,0,g191d9)
def g191h9 (i : Nat) : Nat := 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def g191d8 (i : Nat) : Nat := (if i<1 then 0x50b30a062068860c1071620828188001141c88038918b140c61c40b1a0821c49040b10a18885a12900e2468610b144063043858908b143122d10c2a20e20596046182c82c608322160c8246088071094438590503146400c68a00c1a1022c6305831c01630640389281160c82460840710c140c6090090e404803892100e1864038618c162401c48c60b160180d111103182838b1239014302141c48b3a5181c5091708320507124c195160c316314389160c90448d187120c6110890e34514481802c80858c1c1041c48b281142c624708082122c8246892c61458c2b0610e2c48e44a0c1c5a2065c02c60d3011630900487244022858c10714310040020e2cc1c4884930e0c81c48b280ca8848b18a062002438c50b10c1620e2470c62616044871e70a1c08a2250e2c5421260c1d08b262102c626102022859800f12308301250228a0048b18c1621898487020210b4051306022161ce1858a1930e0c61c00d160ca0458a1c1121c1920890e0c8083a1122ca0500b0624a0a007244181c482424459c607122c82c087120cb00007164140c48060a1240e251001628c306c54c090413820f044901871630c3c38c2458d8309030a1a24597160142c9badb87b53b11aebaa9a75a41a0d9cb9a59559218df8b989385f82b7db79977373170b6e56a367d6496155e15ad5795535114eb4c549144f40d3d93a537f34b3252e32691fd1831330e30a106d02afdaf98f64f14ee0ebae78e52e2cd96d46d12cd0c8ec5ac26bc8ba2b60b10adcab6a82a5ca36a029969548f68b48808227e079075c7366bc65061c5e85985645224e04904403fe3923503002be2982561f818c14a1160d4092042001ff54930ffaa0a07fd71483feb1c21ff50120ffcc5207fd52503fe98221ff58e20ffac0987fd1058ffeb9a41ff58640ffa60907fd72443fe882a7ff50910ffee2907fd2058ffe98c41ff54131ffa20907fd21903feb1281ff48153ffa42a07fe72443fe90c41ffdcd20ffa65087fd32883feb0c61ff8ca10ffa43187fd2158ffeb9a21ff54931ffac098ffd62903feb1461ff58931ffac0a07fd204c7fa38a417f5c520bfae5107f920842ffb9281fddc520ff221105fd75902feb88417fdd110fba60b1fdd324c6feb94617f5ce10bfee0a9dfd7054efebac61fdc8610bfee2907f910482ffb9263fd48531bfee2b1fbf744c2ffbb2617f5c163bfaed185ff71502ffb92217f5c553bfae9105fd76902feb9c417f5cc20bfee2a9dff704c7dea14817f5ca10ff260905ff7258fee982637fdd531fea63087dd3054efeb92637f5c131bfae2b1dff724c2ffbb2817fdcd10ff261105fd718c2feb8c817fdcd20bfeeaa05ff7058efeb9a41fe48230bfae3107dd3258efeba4217fdd530bfee2987f5514c6feb94817f5c963bfeec98df771482eeb9c416fdd130 else 0x10410e24)
def g191l8 : Packing := (113,2,5,0,0,12,0,g191d8)
def g191h8 (i : Nat) : Nat := 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def g191d7 (i : Nat) : Nat := 0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163
def g191l7 : Packing := (116,3,5,0,0,11,0,g191d7)
def g191h7 (i : Nat) : Nat := 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def g191d6 (i : Nat) : Nat := 0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110
def g191l6 : Packing := (12,4,5,0,0,6,0,g191d6)
def g191samples : Array (Bits × Bits) := #[(0xbfd3579740f82be9fbed9f2bf55be3fafcb6662d6f7f3cf14bf08eabb46def1e662ae1c9f7512026ffb6ce8c845e43cb1e95bbd30ca37d5ffae27f269e3647fbee97e07ff865dd7312da8e80efa31334f8b77110a294fa2c140112476e217263,0x2080c4801a918000000788981094102182e064200041a20e01811088600a00000a0410200509a0288714001052345290240023261b0000084008020822302e042000004202000840001a8204e622010a10823154424006181028000900212202),(0xb37904ce7ff56953de81ac717d90a71034d3d5d4a6fc75cccee09986647d661c9fc7e2224bfadc359caaf0656b3911ffba9be216f65fa1c49dbf899874bee9c7f5c564fafbf649e0e6a550613dee46b171e50184200e13000163a237ccc4483f,0x865e2104050a72308a5004042641c980010283044b2040e124126c531835005500198c1aba02181140abc5678c0189468338d498806278908b5321e7c4c8810241a8c13849d59586812550c011dc22916965caaa243f59e4c1d3e726bcc44879),(0x7656b9ffaf7fbcd69696b5df89fd9fd9ae655747dd1dde16ff5d7744cf5357c78b75072e3bbcb52bd54454f9bc65746e7a9ed8397e009281987995e65ee4a7ee05d326f4f39716d75fcb8767821ad46b844808258e2a3253cf6ea13881040d8c,0x188100311060810400243a01002a004902001000008004128824000427886820c42250e000058040030408106142220830c2000001010662102c0c081004704100440000b0200040200287218002942c96181045804080031c00109841008504),(0x9e7ecfa1b663be289e4e66e85ebe769cf03a281c40aec59a531a89bdc2917cd75aa40958eacffcda90ffe7137ad9bff7c173ac63ed6d16faf510b9fc03b7f5f2d538ed592be83d129d6669d07e8c08ca07a98c101ac024d2c2804ca411f909a0,0x2020b0c60a9160431882c064a005031090c42e02006ae00c2440711a4040051813940a051c50163000124107860054800c0c2f44ea48411cc000b18200218c840512000a0e08838a406428c05eec0a4201a424385293645c4328c32710b10ae0),(0x48afe352529d9f71e7ba56c3df9455f86aec7ed231a4182f1e83909b5b57f4f8538abddc7c7bd3f1e1b9b703af0697bd7a206ddf91cebd2d1fe45a97aba9de0433ffdbc89b85911bb19554139111eda5cf49d49289dc948100804cc031fe5240,0x25d0110c02e0120e3281003064a88866903819d13801580523a06641510480140208540c08000c15820366000c9a90d0301d08104368a0114124404884a40038061e094010120253d8154130111e4b5ce49ca82ad2c98a38c923cd0654ed000),(0xbb71faf6e605e9fb69774f3f236affdec5b0f6fc6eeb31aaab9709ba59825f28b5e1b4c9a929ee60ce313e2861ba59e08d7b943cc731de5f7b3f26db622d793b8c1abc517578e53938e53ba84144b4c40e1226cad10169ac341018648a03a410,0x9053085ae00818282a703443c76b2b0c1000189e64880d00a862421010858634043845cc00044bd648405185014800014980040164a5632124140422c100414152debe81912c530410e509e8114094c4ae18468a9400a0a6cc00bdf6de028450),(0,0),(0x541bb2ba83ee7937935c70decb49594d47a4a4bbdac0cf1bb6dff7e75f8a6af2553074ec29c33f1ac9dfa1d5d1c59a7cfbcf815d0a96bfd0e7b6f0ad684c6c94849037d4150cbe2d31f8f01e2cfde810414683fb572913092a5d010800038410,0x440cb00009032480d08100bc3804041260f22640803472210689108b0060000019052801ae422029a0ab02480631d020022da000985a8898cbc3c1010c6808bc0020011c08418480cb1870162cbd68114126a930633d5f5823ff420120010200),(0,0)]
def g191columns : List ColumnInfo := [(160,0,31,0,7),(24,0,167,0,7),(2,0,189,0,8),(19,0,172,0,4),(0,16,166,9,6),(4,0,187,0,7),(1,0,190,0,7),(36,128,27,0,4),(136,0,55,0,5),(129,32,30,0,4),(9,16,166,0,4),(20,8,163,0,4),(14,0,177,0,4),(35,0,156,0,4),(56,0,135,0,4),(26,0,165,0,4),(134,0,57,0,4),(162,0,29,0,4),(152,0,39,0,4),(25,0,166,0,4),(168,0,23,0,4)]
def g191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def g191levels : Nat → Packing
  | 10 => g191l10
  | 9 => g191l9
  | 8 => g191l8
  | 7 => g191l7
  | 6 => g191l6
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 16 41 5 10 4 2 g191h10
  | 9 => lookupWord 67 277 6 13 7 2 g191h9
  | 8 => lookupWord 100 251 6 13 7 2 g191h8
  | 7 => lookupWord 4 19 2 10 4 2 g191h7
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
set_option maxHeartbeats 0 in
theorem geomg191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_10 : block g191 10 0 1=true := sg191_10_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_9_0 : block g191 9 0 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_9 : block g191 9 0 12=true := sg191_9_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_0 : block g191 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_3 : block g191 8 3 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_39 : block g191 8 39 31=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_70 : block g191 8 70 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_106 : block g191 8 106 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_8 : block g191 8 0 113=true := (@block_merge g191 8 0 106 7 (@block_merge g191 8 0 70 36 (@block_merge g191 8 0 39 31 (@block_merge g191 8 0 3 36 sg191_8_0 sg191_8_3) sg191_8_39) sg191_8_70) sg191_8_106)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_13 : block g191 7 13 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_49 : block g191 7 49 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_85 : block g191 7 85 31=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_7 : block g191 7 0 116=true := (@block_merge g191 7 0 85 31 (@block_merge g191 7 0 49 36 (@block_merge g191 7 0 13 36 sg191_7_0 sg191_7_13) sg191_7_49) sg191_7_85)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_6_0 : block g191 6 0 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_6 : block g191 6 0 12=true := sg191_6_0
theorem tablesg191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact allg191_6
  · exact allg191_7
  · exact allg191_8
  · exact allg191_9
  · exact allg191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (vars 191) (graphGoal 191) 11 := plain_low (hints:=536879361) (by decide +kernel) (index_root (g:=g191) (i:=0) rfl rfl (before_sound known127 valid127) geomg191 tablesg191 (by decide +kernel))
def known191 := extendKnown known127 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known true known191 := extendKnown_ok (m:=191) valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (vars 251) (graphGoal 251) 8 := plain_low (hints:=1358970881) (by decide +kernel) (cut_root (prior:=boundsBefore known191) (before_sound known191 valid191) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))
def known251 := extendKnown known191 8 [(251,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known true known251 := extendKnown_ok (m:=251) valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (vars 255) (graphGoal 255) 12 := plain_low (hints:=553656577) (by decide +kernel) (cut_root (prior:=boundsBefore known251) (before_sound known251 valid251) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))
def known255 := extendKnown known251 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48]),(510,[100,49,128])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known true known255 := extendKnown_ok (m:=255) valid251 low255 (by decide +kernel)
def g383d12 (i : Nat) : Nat := 0x1840804ff
def g383l12 : Packing := (1,0,6,0,0,0,0,g383d12)
def g383h12 (i : Nat) : Nat := 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109
def g383d11 (i : Nat) : Nat := 0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10
def g383l11 : Packing := (6,1,6,0,0,9,0,g383d11)
def g383h11 (i : Nat) : Nat := 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410
def g383d10 (i : Nat) : Nat := 0x2e1d818587821e221614a130f091146478584c0c3c2c10b0a7088561608c040207a04c442860211d1a16112300a10082e1c61311850b0a4746c2c1058458988a3028223838785a5041d141418442a102d2088a0a12225460ac2c10805040f40583c282820b0a1c4c45191c1c4824e230c8c09820a901e8c30705040d0e3618222878514342c181c14442810482548c140e0b08166420584040b0a30885c282a3030203e08a072c1610102428b860a11821e1464106058707110b382838984902d1c1d18284824e230c8c0e201c1670947074642040a0f0b4e183a3022286871d083210102c28c861e0f818409821c149061607c10ac2110440306e0e102e1e00585261c18170708242c1100c140a08406050d0ac1080438303848582821818242f042010c0f840a23821408711c2060407c3c0c10a0f503606183e08206e10587291c1814370b04281108e0d878209840b801412a07050418804020c561f04108080a20504121e003e160821ac3aa6695281e74a5d64a236e2ba1a60b1fbdea9dd5d21bcdaf9a258b17fd7296355a14ad3b92851910bcf88e74d40c2cb98aa49d08fc8086b456044c2f828421017c1280d4003ff5c530ffd73443ff5c130ffd73043ff1cc10ffd73843ffa0d10ffd718c3ff9c430ffd30443ff1ce10ffc83443ffcc110fff814c3ffa0530ffe718c3ff4c610ffd318c3ff9ce10ffe318c3ff60530ffd710c3ff1c430fff83443ffcc610ffd83443ff20530fff718c3efe1130ff9708c2ff60d10bfd818c2ff60c10bfd838c2ff60610bfd810c2ff61e30ff9704c2ffe0530bfd83842ffe0d10bde83042bf61830bed828c2fb60810bdd83042efe1130
def g383l10 : Packing := (47,2,6,0,0,12,0,g383d10)
def g383h10 (i : Nat) : Nat := 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def g383d9 (i : Nat) : Nat := (if i<1 then 0xb102c382e18141e0b0515081b05844813238441e0b28448e13e08641e68382b080b205c2c0a1814320a1f08220f1817080b05100a17058c081a0c8c160a1210200b0890220a14101e2a30128a0e230b820f0510240a048f81c10782c145e083b0a0a0214100fe082808592d490e4231f18e446c63231688a8c4ea2230fa871c33216b09e843c15606b0037f63ee9f46f8c7b63d0de34ef1768baa1d10e6871fb8a1c10ddf6dfb6a1afed5f6a4347d9fecd665b327d8fec6861fb0a1822bf15e8aee9710b685a8ac7d5fead655faa354c8a294fba75d35c98e4bba53926e920484a35d15c897437213905c7fc3ee1f14f1476139c1bd0da86b434a1964c846102f39740b4e5902b39540a6051927c934096049023390f883c3e31e60eb072a37e1af0d1c6602fe16a8a8c4d023f10f87fc3be1b60cb05d82be13608f84201be0b604b0190064000dfeb8b07186ff60573843f7f08b8a61bfc7360610bfecb902986ff606738437fb0fc1a21bff874c110bffcbb06885ffe5d304437fb0e98c217fd9720d10bffcba63085ff65f30442ffb2fc1a217fd97a0d10bfecbe63084ff66173443bf2e1b8c613fd981cc109fe4c2e6884ffe61730427fb30388613fc985c530ddfca307184ffe45878c27fb30b9821bed828c6309ffcbb06085fbe4983442efb2a40a61fd9315c130deec1a63085fe64073842dff2cb88613fd985c130dfb38b02187dee55708c27fb2fc0a61bf581e0530def41f06884ff66173842f7f28c0a61bf57160430bdeca502986f7e0f304427fb3039c21afd91618309fecc6e3185fee41318c27ff2ec1a21bee7360810ddfca307085fee41318437bb2ec18217df935c1309ffcbb07086ef247844c37bb07c1a2177d959c430bfcc8463186fb60a718c27fb3138c61bdd835cc10bfcc80e6084ffa61734427fd30b8a613ff9760630df6cbb05185bf65b318437dd22c1461fd8935c130df6c8b05186f725d830437dae6c10213ff985c630df6c10e6086fbdcd82042feb2398221bed825c630ddf48f08986efe47844c377f08c0a617f5911ce10fddc22e0986efe11704c35fb0cb8861bed9360a30bdeca0e2186efe11714c37f730b84616ff965c630df6c16e3186fda07814c35fb0d38861bdf9760c10bf7c9302986f760c834427fb3138861bf581205309fecc4e7084ff65d810c27ff30b9c217f990dc630dfcc1ae1186fd605318c27ff2ec08617bf944c110ddfc2702985fee41834427fb3198c21bdd83cc610ddfc2502985fe643318435fd22c3061bef9260d109fecc2e3185df65683442efb2b982217ef924c610def4bb06086fb609318c3fb662b82617ef924c6309ffcc2e2186fba5d828c3faa63c0a619fd875c6309fecbf06886f7e0d3044377f0840a61bbd91e11309fecc463184fbe498344277f28c1c213bf9460e30 else 0x730608110514260a15041e8407028a0f1182c7c30505c2240382841342a1060e054102240482c411050a0a840b04480b04881e0410241620582440905881e04103c0a0405828a0b05058605040102e0e284c12202828082509942609105c1c202038143058142c0a203c16110511080404828804050447470503c164e18381e3e083c14342010160a203c2c2c204416308810140f211412111844342e1090220f2010160a182416208810140f2010420a1c10081105900821050c160f101c1c0f182416202858160a202c142088284c6070646040703c60a058a0b040e0581450203c14305038407050118a0e2810160a19140a090890120a102c140411864a090882824442a10081c0b028c0a0c0202e0f28441409183c0a0b07101211090c141910470c0e0590162210441e20902c505020142c0a2c1042208290161c1014080e0b918e1a0b8c2304058e8219420281656283c1430785041fa17068a0f05188c060702c9c1038281e4e17040e0aa28101e70805c163040501430284c123e07081dc107828c13088a0c0508e101650ad60140b20281e202114121120281c2e1f041e0a211c162048442430503c404070287040d8441640f04c1e34202c143e081c140f2210080b05101211090f85c18e810140f303c282020641630785040f0a0a8a0f050c1e0)
def g383l9 : Packing := (136,3,6,0,0,13,0,g383d9)
def g383h9 (i : Nat) : Nat := 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804
def g383d8 (i : Nat) : Nat := 0xa10200000e0858408185082e10440a10000c840000161001e1030a10000000000504000000000141001e10108102819120810282002820c8400001e10283e0edf5ba3ccdeebb539ac5dcadb68acd529f4a9dcda4f2289c3a13047fbe9eaf070b71aed266b2186be57aa93696439b8be50258f05a28118781e00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630
def g383l8 : Packing := (53,4,6,0,0,9,0,g383d8)
def g383h8 (i : Nat) : Nat := 0x834601a000
def g383d7 (i : Nat) : Nat := 0xa295fdb2e3ca3070852bfb65c79460e30
def g383l7 : Packing := (2,5,6,0,0,3,0,g383d7)
def g383samples : Array (Bits × Bits) := #[(0x7bf3da45af3f8c085a5cb987177b99507674f4c937c6357ff7c7e09ce49beeecbf7777c878bea111faf6da326b91bcf4ee730cf4458d3f7279c9098db86383f541a14f4a486b2153ac6cc220d9a4c042882144400812c1a03824014a3e21f653,0x6c0c090884541000400081001004571001111584ccc2050082180001a00200048800100001140810814340242a00840000001e41a6804200410144118003835041a0c802027c003361601060690134460c209508104109022004008a24212652),(0xda7e816f3febb7859eb69321adfa95cb2d74d81a38e8c2993ff7c9dd4f4fdcfc37abafbfbba54cf8bb0babce157e577aab0a9e256f1eae7cb247b98d969c798b2d38f019ccd955a0208a2083da20800120c010a1d5456e25c86f4208c8c6481f,0x200340281060102045a2028208088a028404101004082010471440221a34022cc86840000420200840493000840180b1200280000b80480000922403c288328053019888301081491048f8080c08110c302d0c88414008862440588c44809),(0x52ade7ca8472a7a2b56b45b28960a5c8855d7bfc72374bde836b42ebf256bce2c89e0322188af5a96fcb796fb735d57e3a905ea1a25930bb344d14966b67f70482928ec6864892a7808c5443041003000306a901d5cd20440308a310f1078f9c,0xa3a4450a514a89fc8820001843cd690501c00eb41e050930160a86a871d844195d20280b969390c9c938d200449522e21481ab52f26044d05d2ac050b183d70482108ec6035cd2a7ca2c536061530706a304a029342b68660288a31871038514),(0xcf2b445e2c8f92ea37f69711935dc32d8ac9fba75f0b2f7fbdacff602b76c3137a977e4a5b3a7afe6df0f64bb3819165489d455d3f7e263153db4ef0e6c80a735fca4439b2e3869d91109444066714241006ab062288005b03d09cb601f80f80,0x101122848c00200004002802081012c00c02114a80101082802100010a0090020018000021040430120100132800000c02081029098d0105024030240068003b598a4030a023055011412c961ea430201c00594401409011095010a200b00a80),(0xfbaa4318baa57959542a280e640df39778b4d46b1f3c151bf3f0993bd0fe3df9e94e95428bc437eb34b11ff92c19ff03e6ba72ca35ff1343ff1f07fcbab67c86b44125c70c20a80cbc7ec00400020c06c00546400210005cf480fbe001fff020,0x8040d4706129c441b0475088a0e888071200a8201328086d4886b9f0058842e007632e164441220f2c88aa4885ca32b2c0c760840000bc8810be098871947c84a44125c50d00a80c8e1ec30880424881e00722b16ebe406cd4a0ef45014ed020),(0x7ef39cf81d5ebfdc6993b54fc7da086bed316d3dbd7f9d6ce832af685e8fd1cd19ce79faca95b97ac8e7c4c05d5e67a574ecf577efc3e7095e97adf781983c3ab81e2a648807c2c202060a2405bc40004ff800180a32b78004109b53fe000020,0x3b116c16a202824b0cc22038f088041884a8a1812009a5c2c8129c84ec854a2661c6038ac4b07a92e088c80c12a20362704402048320491046298482c58382ab81e02648903c2c012072c9614fe40a0d2916af00796b6a00c309b74da000000),(0x82936fa0d663c33f77e458ec25db297ecc3724c6a282d566f829f79a33da631af6febbbd2c61acfdfc6437c69f10522cfb1ae989294191c6906f60620fd19338998a1ec23330ce50600f619822183bd9200010a002102fddf75f600000000040,0x92e0cc00ec44880444e0840207441f201096061cea13905cbc41881041060826d5310928ed2f1538200888082860024204842842a113418046b620c484811338919a0e423320c650636e78101b5b3e708c0079280753abfc771d20a800000000),(0,0),(0xce927de0dc24ecd0970de7df73d2ffaa3a7fb3c39ffc6327e8d14647987af226336096189d5d227dd00d2c64c7fe7699f3e777dfda82d597d5b7da7ebf6fc4c4e66431b5758c1c33431509592059bbf857fc041ea02010020410640500000060,0x440c002011900401091151a01080401e02200080052040204210522410310308088004430210280280d20140100015010042050012008a48110844101106c4c406603181449c382f0c900368e000810f216e8403f82840020080440100000060)]
def g383columns : List ColumnInfo := [(32,0,351,0,11),(64,0,319,0,11),(4,0,379,0,11),(16,0,367,0,11),(49,0,334,0,7),(70,0,313,0,7),(256,0,127,0,9),(24,0,359,0,8),(28,0,355,0,7),(83,0,300,0,4),(276,8,99,0,4),(69,2,312,0,4),(260,0,123,0,7),(2,1,332,48,6),(57,0,326,0,4),(50,1,332,0,4),(65,0,318,0,7),(104,256,23,0,4),(39,0,344,0,4),(300,0,83,0,4),(29,0,354,0,4),(5,0,378,0,7),(321,32,30,0,4),(262,64,57,0,4),(352,0,31,0,7),(74,4,305,0,4),(305,0,78,0,4),(80,0,303,0,8),(290,64,29,0,4),(72,0,311,0,7),(328,0,55,0,5),(18,0,365,0,7),(273,32,78,0,4),(41,16,326,0,4),(26,4,353,0,4),(51,0,332,0,4),(36,0,347,0,8),(344,0,39,0,4)]
def g383autos : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def g383levels : Nat → Packing
  | 12 => g383l12
  | 11 => g383l11
  | 10 => g383l10
  | 9 => g383l9
  | 8 => g383l8
  | 7 => g383l7
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 8 37 4 10 3 3 g383h12
  | 11 => lookupWord 48 123 4 13 6 3 g383h11
  | 10 => lookupWord 79 299 8 15 8 3 g383h10
  | 9 => lookupWord 39 99 5 13 6 3 g383h9
  | 8 => lookupWord 1 5 1 8 1 3 g383h8
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxHeartbeats 0 in
theorem geomg383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_12 : block g383 12 0 1=true := sg383_12_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_11_0 : block g383 11 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_11 : block g383 11 0 6=true := sg383_11_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_10_0 : block g383 10 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_10_6 : block g383 10 6 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_10_19 : block g383 10 19 28=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_10 : block g383 10 0 47=true := (@block_merge g383 10 0 19 28 (@block_merge g383 10 0 6 13 sg383_10_0 sg383_10_6) sg383_10_19)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_0 : block g383 9 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_3 : block g383 9 3 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_39 : block g383 9 39 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_75 : block g383 9 75 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_111 : block g383 9 111 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_119 : block g383 9 119 17=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_9 : block g383 9 0 136=true := (@block_merge g383 9 0 119 17 (@block_merge g383 9 0 111 8 (@block_merge g383 9 0 75 36 (@block_merge g383 9 0 39 36 (@block_merge g383 9 0 3 36 sg383_9_0 sg383_9_3) sg383_9_39) sg383_9_75) sg383_9_111) sg383_9_119)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_8_0 : block g383 8 0 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_8_36 : block g383 8 36 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_8_44 : block g383 8 44 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_8 : block g383 8 0 53=true := (@block_merge g383 8 0 44 9 (@block_merge g383 8 0 36 8 sg383_8_0 sg383_8_36) sg383_8_44)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_7_0 : block g383 7 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_7 : block g383 7 0 2=true := sg383_7_0
theorem tablesg383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact allg383_7
  · exact allg383_8
  · exact allg383_9
  · exact allg383_10
  · exact allg383_11
  · exact allg383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower true (vars 383) (graphGoal 383) 13 := plain_low (hints:=12901687553) (by decide +kernel) (index_root (g:=g383) (i:=0) rfl rfl (before_sound known255 valid255) geomg383 tablesg383 (by decide +kernel))
def known383 := extendKnown known255 13 [(383,[]),(447,[98,118,81,130,50,65]),(495,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known true known383 := extendKnown_ok (m:=383) valid255 low383 (by decide +kernel)
theorem validF : Known false known383 := known_down valid383
def xdd14 (i : Nat) : Nat := 0x7185103081011ff
def xdl14 : Packing := (1,0,6,0,0,0,0,xdd14)
def xdh14 (i : Nat) : Nat := 0x72b600002081ca4000006212e80052e946141a6b20caf10a0204d
def xdd13 (i : Nat) : Nat := 0x120444871610b0c811142c38e283401298e1e2c486221400c9884400ffd20ffd10ffd30
def xdl13 : Packing := (3,1,6,0,0,8,0,xdd13)
def xdh13 (i : Nat) : Nat := 0x109240d604212c0006120005308000000911293a596c28d80302f5208823202b88c12000316a3a3082c842027b2180048d522f007822a0fe26300c000c0680280018400006438030e9c0003b708be08960e9038809415ec00000003c206e010a00261014100000020622012100001101000010000010
def xdd12 (i : Nat) : Nat := 0x3825958b0e9184b30c36ac54a868b10123652561a1e167ac4588246a50531f0e2117012a1941390902f87150c9e9712a128343c585451488864b4a16661e2e0090494371e1d1c531619296660416138e8e2f87090d80b09f12b8343c545170948868a4b165a3c361a1a2e00aa50a244c4a0d0f16151445212a2e1839a218889909187169f0c1ca47c5450dc0480c09461e2890325c51b282b230d3e2e18f878b859497306c808c3c58a864b0946383e1e2c460254322ad5259b120e173c9738cfd7128547072cbb1311f82fc45045001ffd53483ffb22907ff64d20ffec0a61ffd82443ffa42987ff64910ffea8a61ffd83443ffa64887ff64530ffe98a41ffd98483ffb26887fe48110bfecc241ff9204c2ffb24885ff64530
def xdl12 : Packing := (19,2,6,0,0,11,0,xdd12)
def xdh12 (i : Nat) : Nat := 0x5854805b80a40000000f0600000000290200000001c860000605d88185cc32b0b0550f36500901e427900bf59bb005504a6c03adb9096a0228069614304b97a2405841451310001ef0740e0000b441f05c0000bb560a00ccf98bc9550000e08ec248000000160d0c0680000000000000000001007f5284a0a013906a000008c1bcc9751d5240003a4ae0acae415ca484a04360000000000000000000000232af0aa000140af04e50560001120115700000000dd0b22140120743109a8c5658688b20dc6127fa98815c28d8000e06e000218f2b4c0001145ec0620140000000068a1a18d01e214d1d5e12ea72ac08042c3a040065822a01f1851946e44aac1628182602a8680002010c47a3440445c0010001c09c0000000483d2f242081844a0338ca300bdb3ad08e82c00007031421ee849daa8824a10530600007833621580fd88f2121000064508231910904514a2c26a8129077e2ccc013d18636fa4fc00000000001a8cc000283c303660e34201b11469c881400050485b9c0000022f00b8085a5300002a44262ccb3c427f33baa0000e541d7a36622e61338e9f137d1a0000051d9a00000100282508800d06ce5264073841803b8d120a38000500de10dc03b021104ca0f540473035133485900fb804c72fea2ac296345690e301ec508000185035b140500201000b21ca0004002804e00021488c301000080e0000a1300e08090309420014a0000640900020816100012a00010403
def xdd11 (i : Nat) : Nat := (if i<1 then 0x150a6182c1028382c4b09078b060b0407060b04061261b170d8a1185696250829b0450704084a6283820425a182816081694090b04094a048943c403058203430582a3c32182015212c3e101d208a101489b158604d2d212080b0c86080902a5c30182c10204e0745c3038b4a830242c102839941208119410128c90c5049141810321a8a2b0f12964b0f84098a1387c20411085121520244c8ac352c206c30182015205e0706085282a62dc24203a541812100a958a4507040986430402a467838203c3024201523142cc308629b14b3a1a8a24071314090b0408c5a462c3c4258242c1024198a090a840a06a2838204651281c10211428150811b021a5e284622081c2d43658682a210761a94962840414ba5660dc52286c1c102841961fac628a860b0406c8a29201c102a1c1c1e1d1420cb0b03b314a396d9e120811b016080d8a5dac06c20509040403a2f030c1bc50542080e32b17860f094c2f16f17174aac048e2ec58b44a1c09182d8b435282a1030169786156282a103f143d48459282586072286861462c205a56619615081529cba56604a103058974acc038206a2b6316150817d2bc63be3b87b4facfa2b9ab8e38637e376369b6636075ab54f4f34df41734f2cf24f0d302ef8aec2e1ed7acfac7abd6b569fe9a28da83676e6a66025824963f234e2aa20611a075f89f09e41d9dcf9c79bd5ac5a2197d8d983576d6c962558147131922d16509d01cf54ed4dc4d20ca0bd8b7ca4895c84c7606745644303682a01b40c8003ffd5260530fff609514c3ffda954d20fff65532443ffda960d10fff54983443ffda960530fff54d98483ffda254530fff61531483ffda54c910fff54d91483ffd9260530fff6a582443ffd8364520fff64983443ffd854c910fff54d92443ffca954d20fff655214c3ffda548530fff61593483ffd8264d10dff54d924437fd9366120bff6a191483ff92064530dff64d914837fda960530bff68d914837fda94c910dff689914c2ffda564910bff69532443ff93064520ff754d914c2ffda948530dff4c5984837fd9264530eff605984837fda166120dff66193443ff55164d10dff65592443ff9a548110dff6a583443ff5514c910bff695914c37fd8264530bff6a1924437fd9564530dff661914837fda564530dff6a1924437fda864530ffe54d20443fed5264d20ffe68d20443ff5814c520ffe481934437fd9864530bff68d98483ff91066120ffe601914c37fd8364910dff649814c3ff98048530bff69593483ff92060d10dff68d92443ff93066120ffe68131483ff92060530dff661924437fd9364910dff65593483ff551649109ff6a5834427fda1661209ff2a5314827fca954d20ff64c1314827fda364910ff948531483fd93054d20dfe481914c3bf98060530ffa481214c37f93066120 else 0x16a289465d2b0c6c3451281508141c100d8c3e1012242896587c6940f024204090382030fe1858940f143c0e0b0c9629070c1c16080c2b860485820544842c101058202848584160808)
def xdl11 : Packing := (89,3,6,0,0,12,0,xdd11)
def xdh11 (i : Nat) : Nat := 0xd10f6570be2a600bb4e232218be89e0e800000021e108b8dc0016960004848c098c7d7485adc3ecb272e00000340396b9915d40f61bc5b90b9c210010000b40a09c14a0ab31a41f219748113c0016183070a1c001c0d0005ab86e12ea000714f49b6280002bde2d000000000004efe060000000000e52410400c00000000000015866cdb670002045408000531169666c702905c59204b179f222013145e09f8324a2e250001858130492149993b88ee02305480189421c89721c01a2830416c501c64a218689009
def xdd10 (i : Nat) : Nat := 0x5810103c0702030983509434270c0a8663e1830d8400040201b40ed14102514080800b060251686102f8302030401e1416105b0605460f0202a182e283c20b03c4016160c3204040b062205410103c10982d078764020205a8b9298605411040fe0128a550c088206cbf0cb7ebcab69ea6694a168094e3a8d61c80de071db86557c5b55451522424f035cc82948c10400affb70a9b248857fdb54c5984833fec295298a413ff6e98254530bdfb6c54aa69067fca96a553483fecc2a6098a41ff64c0a954d20ffd240a9302987fe585485314827fe5d2a6cc241ff654d2060d10ffd240a93068867fda961532443ff2c12a299221dfb5498264530f7eb02c12a29877f985481914c2bfedab04c8a61ffc5452060530dfeb50a8a64887fd1814c131483fe4a9a4090a61dfa54920645308ffb66d0b309047fdb52a531483bec98a60cc241ff8485a04c520cfeb0254a629073f9814c198483fe09824298a41ef44c58060530
def xdl10 : Packing := (32,4,6,0,0,10,0,xdd10)
def xdh10 (i : Nat) : Nat := 0x162d60c000001a0b48548a00180640e804000000001a87a4ec1148fe71800a08483e03413640a0000081001041
def xdd9 (i : Nat) : Nat := 0x1e01c040605408080801e100186c2000008077d472d179f345480087fcca6d53166120ff61525452060530fb65526058254530ff49524c0a954d20ded9b64c0a954d20a6fdc62a5a954d20ffc130615214c520ff495254d2060d10e7e552604a94c520f3d1316053066120
def xdl9 : Packing := (10,5,6,0,0,7,0,xdd9)
def xdh9 (i : Nat) : Nat := 0x1c0
def xdd8 (i : Nat) : Nat := 0x7792549b64c0a954d20
def xdl8 : Packing := (1,6,6,0,0,0,0,xdd8)
def xdsamples : Array (Bits × Bits) := #[(0x843ba4f7cd61372491be76f436fd85df48f941b2e64e47cceed4b838ca94c7fab05f8e91fda2faee86adafd442fe500888001188800003a900013fc000802e7c4c10398cc00b1801080fc64c4481d3200821075b3090d9a33c9401c73e21f673,0x8628228204486c10181aa8a810940185390410c61000020428620228000401a0a816840aa42000080d1520a03800e31d5a4054495180c10554919114015504904c10118c800b1801080946484481532008210253200091222c94000224212652),(0x627262f7ac7d4180874aa332f3649ccea262ea7f57b2d0f5b7755305f01134eca684df9cbdad0316b0d416f59c0c4c200a420020803c040000000000037f7efe10a52610c040206430b2187c00061c3b30c6249c31632604c0ff66a4c8c6487f,0x7084400422a080282044030243411c4040400c11010de16a02000c410040e650162841004811cac040820a1480200462242b2b8288601e48a06c48e09e88600e10a526104040206430a218240004081330c6248c10420400804264a488c44829),(0xb5e7f8cf00ef5991e522c1af5fa45316e5cd0b8cbb66b0185498415ad783cdb41d40d352ae3afd7ac3a3deab5584801411630002151500000002003fdf3b40000001c01f2583c181c13c6072081863c4010038e7c98c38470f188738f1078f9c,0x30312388442000051b280302014620028205000c232081471f84002c6a0000700020e0210c400303200006a0101b99880c41050059c60950c92850c60050dd00000800a2583c181c11c60520810028401001002898838470a18831071038514),(0xdfee4b807f94aa5192d80bff96cb69f143232c12b9197a6fe8d1d930bf8b8c522c816ea8afd33123b8cb4e6f27200011159d060102c058001e14403ec8008100600607e0080c000601c07f8070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0xb8000884020150920240020984c001895180020210041042880308610900000001501010c108ac04009112905e0a46401319ee2bb8000c08414c1a41849ac02460000540080c00060000150070c07c003e0580f80407c03005e0502f00b00ae0),(0xdc6c4570ff80dfcf8fcda949aa3f0056f33d10c9bd336e626a3cafaaaf5e5b27db6967ff0cc7c79a36a76e55f3ec000884980480004000001e153fc00000000380c7f80031f001f801ff800380ff8007c007ff000ff0007ff000ffc001fff000,0x40164018a920020c01a551402b2bcc428200a028a6b828b0528875103683ea4406202ba4080542e300620005819118a2a4a60194067f32f2aa2264aa7a203b4b80c7e80031f001f801f68003803e8007c0027d000bf0004dd000afc0014ed000),(0xd72723a0b67c5a17dcb97c25986092c769e02e816cd3f1f9f3c7fdd5f16ec771123fe9b8f234a4e45d9a1cec5a9732c22000f948400283bf81a800002080000000f800003e0001fffe000003ff000007fff800000fffff800000fffffe000000,0x11d30408083a4400004500101b00840304200826f08190500cc01442812050100200110413b4040008019000b18e02597812024043c00216c06c15c82c06c000000003e000156a40000032a000006a59000000fff6e800000fffdda000000),(0xdd269fe53e82fb7a9ea3039ed6a68f10bdd8f7eace4d9941d67cfede716a734d6095a4775d16376acd3c89b5f0c80d2042000034282824406040800000441083ff0000003ffffe0000000003fffffff8000000000fffffffffff000000000000,0x90129e2000711c60f000458b40c201d31a02282c2520c80a891a2a64a21108440403a70036004242b6010cb034b5b901394c46d3707602343903703403392f16a0000003f2e940000000003fffbf7e8000000000fbdfbff7fbd000000000000),(0xcce3e2eedf7d3756385c4e2d4d305b0d5d651eaf5b2c8753b1bdfe5bf9ed2dc3230529ce52d66c9af9ec98c85e2c82c6002008021501801601a2000114000003ffffffffc000000000000003fffffffffffffffff00000000000000000000000,0xe08ce001081d785b08454382402005a3104e81751500a7e0020220781842a95084d0c0b80700c0008caa40042e3046075a286e8fda63836ad201783283783203ffff7ff5c000000000000000d5effd795a6feffd700000000000000000000000),(0xa3915662f2f3326f60675cc4d9def0e5166f5d9bbbac134338e38bf4de837236dc7f103cde6d83e3f748bbf5637d21016004e2556a827840e048c00020008103fffffffffffffffffffffffc0000000000000000000000000000000000000000,0x401a4201b8100c08102a49a44a304e220a069d590580802440601000a044891222ae400624840090800c24008024a00fc860109040f883d49c03c03c23442d0295fffabfc0d16aa95bffeafc0000000000000000000000000000000000000000)]
def xdcolumns : List ColumnInfo := [(128,0,383,0,13),(16,0,495,0,13),(64,0,447,0,13),(32,0,479,0,12),(2,0,509,0,12),(256,0,255,0,12),(17,0,494,0,11),(4,0,507,0,12),(8,0,503,0,12),(83,0,428,0,7),(66,0,445,0,11),(132,0,379,0,11),(196,2,312,1,5),(35,0,476,0,7),(202,4,305,0,4),(320,0,191,0,11),(114,1,396,0,4),(197,2,312,0,4),(7,0,504,0,7),(74,0,437,0,7),(25,0,486,0,8),(404,8,99,0,4),(31,0,480,0,4),(268,0,243,0,7),(24,0,487,0,11),(160,0,351,0,11),(322,0,189,0,8),(156,0,355,0,7),(56,0,455,0,7),(416,0,95,0,8),(85,2,424,0,4),(167,0,344,0,4),(297,16,198,0,4),(224,256,23,8,5),(344,0,167,0,7),(15,16,480,0,4),(49,0,462,0,8),(232,256,23,0,4),(257,32,94,128,6),(134,0,377,0,8),(340,8,163,0,4),(188,0,323,0,4),(176,0,335,0,8),(177,0,334,0,7),(178,1,332,0,4),(2,64,189,256,9),(296,0,215,0,7),(32,128,347,4,9),(120,256,135,0,4),(449,32,30,0,4),(208,0,303,0,8),(91,0,420,0,4),(290,64,157,0,5),(36,128,347,0,8)]
def xdautos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def xdlevels : Nat → Packing
  | 14 => xdl14
  | 13 => xdl13
  | 12 => xdl12
  | 11 => xdl11
  | 10 => xdl10
  | 9 => xdl9
  | 8 => xdl8
  | _ => emptyPacking
def xdindex : Nat → Nat → Option (Nat × Nat)
  | 14 => lookupWord 7 19 3 10 2 4 xdh14
  | 13 => lookupWord 47 59 4 13 5 4 xdh13
  | 12 => lookupWord 100 253 5 15 7 4 xdh12
  | 11 => lookupWord 22 113 6 13 5 4 xdh11
  | 10 => lookupWord 19 25 3 12 4 4 xdh10
  | 9 => lookupWord 1 3 1 9 1 4 xdh9
  | _ => fun _ => none
def xd : Forest := ⟨1535,14,fun j => xdsamples[j]?.getD (0,0),xdcolumns,xdautos,xdlevels,xdindex⟩
set_option maxHeartbeats 0 in
theorem geomxd : graphValid xd (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_14_0 : block xd 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxd_14 : block xd 14 0 1=true := sxd_14_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_13_0 : block xd 13 0 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxd_13 : block xd 13 0 3=true := sxd_13_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_12_0 : block xd 12 0 5=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_12_5 : block xd 12 5 14=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxd_12 : block xd 12 0 19=true := (@block_merge xd 12 0 5 14 sxd_12_0 sxd_12_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_11_0 : block xd 11 0 12=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_11_12 : block xd 11 12 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_11_48 : block xd 11 48 18=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_11_66 : block xd 11 66 23=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxd_11 : block xd 11 0 89=true := (@block_merge xd 11 0 66 23 (@block_merge xd 11 0 48 18 (@block_merge xd 11 0 12 36 sxd_11_0 sxd_11_12) sxd_11_48) sxd_11_66)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_10_0 : block xd 10 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_10_2 : block xd 10 2 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_10_11 : block xd 10 11 21=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxd_10 : block xd 10 0 32=true := (@block_merge xd 10 0 11 21 (@block_merge xd 10 0 2 9 sxd_10_0 sxd_10_2) sxd_10_11)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_9_0 : block xd 9 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_9_1 : block xd 9 1 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxd_9 : block xd 9 0 10=true := (@block_merge xd 9 0 1 9 sxd_9_0 sxd_9_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_8_0 : block xd 8 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxd_8 : block xd 8 0 1=true := sxd_8_0
theorem tablesxd : checkedTables xd 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block xd 0 0 0 = true)
  · exact (rfl : block xd 1 0 0 = true)
  · exact (rfl : block xd 2 0 0 = true)
  · exact (rfl : block xd 3 0 0 = true)
  · exact (rfl : block xd 4 0 0 = true)
  · exact (rfl : block xd 5 0 0 = true)
  · exact (rfl : block xd 6 0 0 = true)
  · exact (rfl : block xd 7 0 0 = true)
  · exact allxd_8
  · exact allxd_9
  · exact allxd_10
  · exact allxd_11
  · exact allxd_12
  · exact allxd_13
  · exact allxd_14
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseFA : Impossible false (graphGoal 1535) 14 (vars 1535).toFinset :=
  index_root (g:=xd) (i:=0) rfl rfl (before_sound known383 validF) geomxd tablesxd (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx15 : Lower false (varsX 1551) (graphGoal 1551) 4 :=
  strong_low (m:=1551) (cap:=3) (l:=[(0,10),(1,1),(2,2),(3,5)]) (by decide +kernel) (plainA (q:=15) (prior:=boundsBefore known383) (before_sound known383 validF) (by decide +kernel))
    (cut_root (prior:=boundsBefore known383) (before_sound known383 validF) (512,1,12,2,2) (by decide +kernel) (by decide +kernel))
def knownx15 := extendKnown known383 4 [(1551,[]),(1833,[130,114,33,97,82,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx15 : Known false knownx15 := extendKnown_ok (m:=1551) validF lowx15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx111 : Lower false (varsX 1647) (graphGoal 1647) 7 :=
  strong_low (m:=1647) (cap:=6) (l:=[(0,10),(1,1),(2,2),(3,5),(5,1),(6,2)]) (by decide +kernel) (plainA (q:=111) (prior:=boundsBefore knownx15) (before_sound knownx15 validx15) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx15) (before_sound knownx15 validx15) (512,8,99,4,5) (by decide +kernel) (by decide +kernel))
def knownx111 := extendKnown knownx15 7 [(1647,[]),(1901,[129,113,82,65,48]),(1963,[98,134,114,66,81])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx111 : Known false knownx111 := extendKnown_ok (m:=1647) validx15 lowx111 (by decide +kernel)
def x303d7 (i : Nat) : Nat := 0x105fd30
def x303l7 : Packing := (1,1,1,0,0,0,0,x303d7)
def x303h7 (i : Nat) : Nat := 0x1ef762040000000008400000011bce4000001439
def x303d6 (i : Nat) : Nat := 0x212180bf58530fe48130
def x303l6 : Packing := (2,2,1,0,0,4,0,x303d6)
def x303samples : Array (Bits × Bits) := #[(0x317e3fcd90ffb40b7d7ff6fe8d86be3a87e2e76fb2e33fefe16fe58aa26fce3c534717d6c460fd9d56469a36b86192628b7ee8c34ed834f3fd26997dec2ace94e7779f4f83df814eb5f5455e6104b0a385288bd64ccb4407021f21232639f673,0x40108040809012032e044ca4e020010840c005050a340400081d3928102382c0501c040c121541800187910df26090000303189c303680610800e24e80245016200011021080400077146bd4a052614281515040a821d184631212324112652),(0x7153e0a4fa3e38713f6b8b69a7d33f7aebb7be73bcc6f3eec799b87883896fe519c79bfe6b353bda9be74cb49f099afecaf66df29abe9d3ef20f723834969686bffe955eb67e1d87326d5537979c3ed4de371f1e2dbb800801ff860c3f26487f,0x59d4a23300a4c8dd0c14b821b1a0b94401a005220d502a96f1302800100446908800002938cc000494a0806400499615878ccc5004281540c35200c0106d22468183468d00a602a0c8060000a4ea8181c2ea48c9a52020c5b18c860c13244829),(0xa91bf2d90f83eff29f1e4ecf9cd38978f8649ec7074ce63736ff7576a8b865cfa6b39807f91a84627fd3ff9307bb139dfff689ff8137b6ad6b58e58cdf7ffe79f10c4934ff24dcb85f323ff5a6b383eddc273afc7b29c10879e0383039c78f9c,0x200a19c060011100b123421008090620844168c490a7040808088261689b096060e845144511983102446003633608c808003122c891c01008848e05c70040100e50b1209208440933403c8a430564163c04030008405a2a4a52383028838514),(0xeabac66ba5dcefbc0a25c594f084fc357f6b811c6f1d35353e079ec779b4364e44f58db364e8aecbedaaecd752fa4e4bbdc9d69bf5ad5f54955894d7fbbb6dd27947483f6eb2fa7fee77afd7a957ff5f5b32ebab3885c9a0fc00c03fc1f80fe0,0x20a23c0d4202c90c84b58817242149701815012608d004b2d10814006404808c0232222a442086600102780488050052cb4e00240a0e0fc300005a005b82c281ae02404082a3208410c0218860896800d8741a2004251194a5c00a81780ae0),(0,0),(0x64a6fd12ebe908f6e5b579664ebb31be169054b200e33bc075fadb0ee45797baefcb6799f2cff33e11d63f0f330d6b0b7ad86c3e55e52ae7ceedab75f9eec7ef40bb32db19bdee52cf8dfc6e52690e7cffe8af61fed2f6570200ffc001fff000,0xea20832a24e29609451282002044c44b7000880a84149894a31c200c40a443900ac21223004021615c26022000880200928b480608a00109c74160131148aa000191a885ca4281a030881102143a89c88008a232614ce22398c6d48001eed000),(0,0),(0,0),(0x46ac2ab6e3059f1cc4a6275863bfd2e7c8fbd59e5d75aaaffbb17ac7df0d372ee8edffbc3faf1aa5d03865cd5b777de7ad199f0efcab6b7fe793c26b99c66b3b39b5b3825e02ea3db7bc9b6b1b6c6c7ba7fad649aa5d3af08400fffffe000000,0x5e4040c209480090080050809912b48ea22270594320200820d022081b18214010c9cc84bb9c108188e082a262d81828101019c014e030201a87a42604003c6600112204091409416304d86301000300030980840218cc63182b757e000000)]
def x303columns : List ColumnInfo := [(288,0,1551,0,4),(6,0,1833,0,4)]
def x303autos : List (List Nat) := [[],[81,130],[16,82,131],[16,32,48,128,80],[32,83],[32,49,128,81],[48,33,133],[48,129,82],[80,16,33,50,131],[80,129,50],[128,49],[128,81,32,49]]
def x303levels : Nat → Packing
  | 7 => x303l7
  | 6 => x303l6
  | _ => emptyPacking
def x303index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 4 17 1 9 1 4 x303h7
  | _ => fun _ => none
def x303 : Forest := ⟨1839,7,fun j => x303samples[j]?.getD (0,0),x303columns,x303autos,x303levels,x303index⟩
set_option maxHeartbeats 0 in
theorem geomx303 : graphValid x303 (boundsBefore knownx111) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx303_7_0 : block x303 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx303_7 : block x303 7 0 1=true := sx303_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx303_6_0 : block x303 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx303_6 : block x303 6 0 2=true := sx303_6_0
theorem tablesx303 : checkedTables x303 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x303 0 0 0 = true)
  · exact (rfl : block x303 1 0 0 = true)
  · exact (rfl : block x303 2 0 0 = true)
  · exact (rfl : block x303 3 0 0 = true)
  · exact (rfl : block x303 4 0 0 = true)
  · exact (rfl : block x303 5 0 0 = true)
  · exact allx303_6
  · exact allx303_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx303 : Lower false (varsX 1839) (graphGoal 1839) 8 :=
  strong_low (m:=1839) (cap:=7) (l:=[(0,10),(1,1),(2,2),(3,5),(5,1),(8,8)]) (by decide +kernel) (plainA (q:=303) (prior:=boundsBefore knownx111) (before_sound knownx111 validx111) (by decide +kernel))
    (index_root (g:=x303) (i:=0) rfl rfl (before_sound knownx111 validx111) geomx303 tablesx303 (by decide +kernel))
def knownx303 := extendKnown knownx111 8 [(1839,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx303 : Known false knownx303 := extendKnown_ok (m:=1839) validx111 lowx303 (by decide +kernel)
def x127d8 (i : Nat) : Nat := 0x1948817fd30
def x127l8 : Packing := (1,1,3,0,0,0,0,x127d8)
def x127h8 (i : Nat) : Nat := 0x8e80
def x127d7 (i : Nat) : Nat := 0x4944490bc37eb0261df54530
def x127l7 : Packing := (2,2,3,0,0,4,0,x127d7)
def x127h7 (i : Nat) : Nat := 0x68
def x127d6 (i : Nat) : Nat := 0x641b788054530
def x127l6 : Packing := (1,3,3,0,0,0,0,x127d6)
def x127h6 (i : Nat) : Nat := 0x78000
def x127d5 (i : Nat) : Nat := 0x320cce6508054530
def x127l5 : Packing := (1,4,3,0,0,0,0,x127d5)
def x127samples : Array (Bits × Bits) := #[(0x33b53f8e4204ba7fde2f72e37efbbeafc351d8ff0e32f73fdf7deabdaccbfdf55cf581fadfe796e1065f0f3f3c8ff39a1bcfbee39edb3735d93ee943ff49ff4812e3dd7bb8fe9b6c3b39a07fd95471811c1fc403f090d9a33c9401c73e21f673,0x22400042128a080402a91004202800004252029301408200104a8144080310488094c8282082803084402c2101010085200104800011429800104c82702c002204a2212301044910000000a12240401219d20130c00091222c94000224212652),(0xdd8ff159b0dff7afb9a5fb4bb36f6fba9dff3fcef76ff8b3e3fb3e6bd13c4f7bc25fcd3f649ce1fdf9bc6ef112f93f74f4e08b8879c691feb7b206d663b7f52f36bf46cc19956ae1be475333a8e1e0e8a18000fff1632604c0ff66a4c8c6487f,0x4ca82800c8008048210080610082808119048844908001000220208000184103032200810a4810000102000630c8c65202642907014c0524000900000040019440040810280114080190201000800024c421c20c30420400804264a488c44829),(0x18538ed1fbbac554f3c15f7a8e5c22cbfc3d6a0d6cd6e28a5c8f3ae10dcf1c1ffbabe4446aab3d9ed036e2e6fd9049c5e550f5bcaf75d5c9e6572c7dc9b52c06ed5c26a79da7f2ef58e2a9579eaf1a56000032fc098c38470f188738f1078f9c,0xb200d43524865102821a0e024d2906542688728100208414c08888315780aab0a00014600401690b908cd92140101924b098420890a3e082f210c72c1b1784209f0a702404a04006524b02410a2e0d903ac82492498838470a18831071038514),(0x59ce4420bd6963a913f43f9de268d1efef8f2fb207da3a48ec97a9deffd57a77b706bbf8495d8ffae1e2b2cbd9bf79bd069768b783264df96e4dbbf880d771b7e983bc964ee8b79ff7df7db49e0ede9642603b000e0fc0780fe0f83f01f80fe0,0x7b298a9b700824680420dd20c29920d1008904220168433142418e0002104100c8499a31e28020200004900c2000db01002c01681c1669050c0813a028424420050ad0034e085829b0202a0401f00fc51659659407c03005e0502f00b00ae0),(0x2e5f27b2ccd3bf47449d32a4a0b9b016a4ef437de467ee7c1b5521f6ef0b4506d6f2fb4bb2fcfed933a0f1a6296ec8baa82f08bb45dbf867b824f46d3d610eded619983f42eff67db99c5e98b526e4404a6ec9000ff0007ff000ffc001fff000,0x900492102400975b9450cd204e00604c2005300054b4140004b52221b5d8201039010441800156480b389344924a01000412426a13a220000aa03308078024199a0044081490a427404bdc10119e01a02229a68a2bf0004dd000afc0014ed000),(0x58bb38549a7ec4578133e2306eb8ae1a824ad19e6d6f73c40501d6c911f0f7f7fa3e83b8a786cab91461641af6cc31d807de1e7ffff4ded66c7c7d084d5d09b4cb7d6132ac96ab1416ebc451dabd2381141104000fffff800000fffffe000000,0x4c1ac138a10172311050cf3282076191118cb50840327cbc81106a2063e4cf06792a06939350628a3a1bc29442f28a125f12005fb38e210408e8005c8093bac14258da983ce134cdcac82f1018ac9e2de62dfecf3fff6e800000fffdda000000),(0xd5004fa4c1bda1fae60eb2147d2b71bea81124af9dcbe8aaf1917ceaf73ec740ec24cf05bd7ddd64fe4985172bc495a1b1b698b947d941b7d1cc9393d623bf6bd3040ae3421bcb380f67abfea8b6a3a8a18000000fffffffffff000000000000,0x901592ad068c7cb7de817c16460d2d56c43807b00122ec9125954f72dc408c008c519f368091ae85c8c1f5104d3218a50593c6608490628102d2b7eec9bd8262b99022200084e9545e6546cb0967ff9b3bde3df3cfbdfbff7fbd000000000000),(0,0),(0,0)]
def x127columns : List ColumnInfo := [(532,8,99,0,4),(608,0,31,0,7),(528,0,111,0,7),(514,64,61,0,5),(546,64,29,0,4),(561,0,78,0,4)]
def x127autos : List (List Nat) := [[],[16,66,101]]
def x127levels : Nat → Packing
  | 8 => x127l8
  | 7 => x127l7
  | 6 => x127l6
  | 5 => x127l5
  | _ => emptyPacking
def x127index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 1 6 1 1 x127h8
  | 7 => lookupWord 1 3 1 6 1 1 x127h7
  | 6 => lookupWord 1 3 1 6 1 1 x127h6
  | _ => fun _ => none
def x127 : Forest := ⟨1663,8,fun j => x127samples[j]?.getD (0,0),x127columns,x127autos,x127levels,x127index⟩
set_option maxHeartbeats 0 in
theorem geomx127 : graphValid x127 (boundsBefore knownx303) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx127_8_0 : block x127 8 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx127_8 : block x127 8 0 1=true := sx127_8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx127_7_0 : block x127 7 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx127_7 : block x127 7 0 2=true := sx127_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx127_6_0 : block x127 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx127_6 : block x127 6 0 1=true := sx127_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx127_5_0 : block x127 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx127_5 : block x127 5 0 1=true := sx127_5_0
theorem tablesx127 : checkedTables x127 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x127 0 0 0 = true)
  · exact (rfl : block x127 1 0 0 = true)
  · exact (rfl : block x127 2 0 0 = true)
  · exact (rfl : block x127 3 0 0 = true)
  · exact (rfl : block x127 4 0 0 = true)
  · exact allx127_5
  · exact allx127_6
  · exact allx127_7
  · exact allx127_8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx127 : Lower false (varsX 1663) (graphGoal 1663) 9 :=
  strong_low (m:=1663) (cap:=8) (l:=[(0,10),(1,1),(2,2),(3,5),(4,1),(5,1),(6,2)]) (by decide +kernel) (plainA (q:=127) (prior:=boundsBefore knownx303) (before_sound knownx303 validx303) (by decide +kernel))
    (index_root (g:=x127) (i:=0) rfl rfl (before_sound knownx303 validx303) geomx127 tablesx127 (by decide +kernel))
def knownx127 := extendKnown knownx303 9 [(1663,[]),(1917,[129,82,113,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx127 : Known false knownx127 := extendKnown_ok (m:=1663) validx303 lowx127 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx239 : Lower false (varsX 1775) (graphGoal 1775) 9 :=
  strong_low (m:=1775) (cap:=8) (l:=[(0,10),(1,1),(2,2),(3,5),(5,1),(6,2),(7,4)]) (by decide +kernel) (plainA (q:=239) (prior:=boundsBefore knownx127) (before_sound knownx127 validx127) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx127) (before_sound knownx127 validx127) (520,0,231,0,8) (by decide +kernel) (by decide +kernel))
def knownx239 := extendKnown knownx127 9 [(1775,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx239 : Known false knownx239 := extendKnown_ok (m:=1775) validx127 lowx239 (by decide +kernel)
def x367d10 (i : Nat) : Nat := 0x10200ffd30
def x367l10 : Packing := (1,1,5,0,0,0,0,x367d10)
def x367h10 (i : Nat) : Nat := 0x163f67bd198c001891c5001c00e2488527e2a8085042063a29b8928f42fa534182920de480000180aa15cdf1a70dc23c840c63143800e22014001cc00000000000316a0bb22
def x367d9 (i : Nat) : Nat := 0x121070640e1418c604830a00704141a40850630908140000419c48703021033020e0c708100061ca202410c14103008162828484084830201420241041430300882083860a0cc002831848000103284840a00006618100c20414003440010838328d840008b06146200c20a0c01420180021030e718100c000083834783d3ec7a4e2772595514cb0d3bad7328b627a801b04d8e61e801ff18530ffae4987fd614c3fe38a61ff58130ffa82987fd754c3feb8a61ff54930ffa84987fd214c3fea8a61ff48130ffaa0987fd104c2feb9261fe58130bf8e2987f9204c2feb8a617f5d530
def x367l9 : Packing := (21,2,5,0,0,10,0,x367d9)
def x367h9 (i : Nat) : Nat := 0x6d1648d70732530b727c00229544f7e87253eacf8ff835304000089000044881f50f0e94149d6c0959458000e0e00000006213ec70a566201d5037046876455000095e08142ee8790a3a9a404c2c906e846000000242dc2a54f00058db44a8441a910ddc4e808e2a7314001b2f00010e1c85049c07b81ca30430d1d048984454cb0644fe0963191ad1065e89e09017f851c17135000505d4b8000d150003424a014968000001d47a27000000000000030cdab1311e189498000000b26000249e35c30c28ca014a456a000000000007000001e5d91e29dc8f4000d0dd0fb10688e04300012c0ca2920e29284c0000006a758780006390e2b85b8b030c295f48de3564df06ed040b582000038d64a1a5bbaa800141c2050000041278c03b15800144ca3410000d000500910800030302000234270a09211c0d0d0053061515010313010f010003
def x367d8 (i : Nat) : Nat := 0xa20702031880283c012000c406122400828188082000620003140050509006060c2118003181848a000c3c625000e30503104810281901e09006001010314001881c280c685000e1c403051028188140c5020620442800320281880c3c41c10309101080c40e0020603120c0018c181c400503102818a000c41406205018018184882c2060c241085860382a1019a002801010200032080188001c0c61812080a40c03091808003819014404020c063810510603818c440c412062010007032020188000c40e06210031048203810582819c24181460e000630c05010320306880c1c402062030710103818c05000c24800060e30c0710103818c1f080c6120e060c4020007182818804240c6020e203083068804001c0c8180c20120658e48c78a288d87886b85684983481f8127f57e07c37ae79177475f73a71d7106fb6e66c96a468f67a66565062b6166015f45df5da5c55b059b57e56956454f53a5255104f34de4d14bc4af47a46d46043b4264093e43c73a238d37035b33e3293142ef2da2c52b029b25e2412241ff1ea1d51c01ab18e16914c13711a0fd0d80bb0a608907406705202d000fed6248130dfd615d530ff96448130dfc7644130ff96050930dfd8754530bfd8518530ff55158530ff96054930dfd215c530ff96548130dfd8758530dfd515c530dfd655c530dfd641c530dfd545c530dfd645c530bfd8558530bfd8650530ff96058530f7d5354130fbd5450530f7d5154930dfd7150930ff96148130bfd8550530dfd515c930dfd655c930dfd651c530dfd615c530dfd645c930dfd545c930fdd3148530dfd541c530dfc8758530bfd851c530ff96048530fed5248530f7d5454930dfd215d530f7c8558530bfd861c530bfd8548530dfc7654130dfd7550930ff95448130ff56150530fdd3154930dfd525c530fdd3154530dfd615c930ff95148130ff960545309fd865c530fe92050930df971481309fc8758530dbd7450530df976481309fd821c5309fd87581309fc87509309fd825d5309fd815c930df88758130fd93158130df9605d530bf98018530ef96058530fe921481309fd861c5309fc8754530df9605c9309fc87505309fc8754930fd93148130df9601c530fd531485309fd8718530f9d43505309fd815d530ddd315c9309fd8750930dec825c5309fd851c5309fd8750530bbd841c5309fd841c530bdd8350530fb884581309fc8748530fd943481309bd841c530
def x367l8 : Packing := (93,3,5,0,0,12,0,x367d8)
def x367h8 (i : Nat) : Nat := 0x190a899872853cce0458ef0310d00618b04c00000000000060a4808460000007885c470bf81a8280000060ca0f290684c8f8002cbb8258108adcb483800000087a8070e10c4c0c06809305c0d80040890a00c10014c0648000000090000080
def x367d7 (i : Nat) : Nat := 0x141a008000004000380806300000000021000061000c2010804062000001000420901880e03100c209080c30001880e1bed9ac35ca752689248fc6a2b1085c19f0f377381b6cd5faa1469e4822cfa66279046625070023fb2a43a849865f2158758530cdec22ca38a611fd9521d614c23fb2c43aa49867e581851c530cfc43ac0a8a611fc98585754c33f10eb02c29873e5808758530af6c90eca82615ed921d9104c23fb2c43aa2987bc58151585308feca90ea0a619f960608714c32f90a43ac29863f595861c5308fecab0c38a6197d65614714c23fb2c43a829847f6448750930fe290a62a92619f887581214c23fb2c43a429879e5808558530cde43aa8a0a61f894250d204c3da2c298ac09866e611601c530cdc4830838a619b887211604c33d10e90284987f04853148130
def x367l7 : Packing := (34,4,5,0,0,9,0,x367d7)
def x367h7 (i : Nat) : Nat := 0x6a090000521407cc000028e2c04
def x367d6 (i : Nat) : Nat := 0xc200000700c40484030c682f1b9e1e0319d436448750930f944c560215614c3879602148758530f344c56021d614c2d88a75094348130a2e69890610714c21b8a9611601c530
def x367l6 : Packing := (7,5,5,0,0,7,0,x367d6)
def x367h6 (i : Nat) : Nat := 0x40
def x367d5 (i : Nat) : Nat := 0x1e14215315808758530
def x367l5 : Packing := (1,6,5,0,0,0,0,x367d5)
def x367samples : Array (Bits × Bits) := #[(0x71609fccfbf64ceebed9bcb8a8bf0c06d9b96735c14b627f5ab6ea754be8318a6efd99782f74d0f78ba5a6689bcc6c628e5877126bedcf2f3a55f84df57b3d5866df4c1db9e73fe105f2259633d480a2013b20002d0b1842464c36792839f673,0x630f8798e14000285000828050d0222f80c24fd000ab89335110001d0302162a6180c02a29448dd144501cb1410d322408d0103152e1290b48c02030e509001a4020114b0511000800041ca424c0b1b852a99b10b18424648245928112652),(0x40d8fffd9eec9f9d4cfb5c3dfd739a72513adaa0d195ac8fdd6d68d1aa5bedda1debff6ff63a3f06c63707ed9bb5897066800600885da82b94b716fa9debc855756daaf7f5cfb92faedf6bfe2065a3685120001fad80210c187cc981ff26487f,0x8d8000000000123040020311300400100000040002545010840000a28040804094004a210412804200a822004008104488020287000c00440082230288100460042498081402c214002c00015019370a06a04424000210c1824810085244829),(0x2e9e11abcd21af7bfba4e6d51a08e7993f45716605aacdd1cf0eee3c7e637bc5e1687acaf769eae1cb587d636fc7ee98fd8ef058acc2e7e47d8e67596eecbebb1412b37f74f576cfe346ffa1fab5830d44040c458023c07060730e1e31c78f9c,0xe20618ec108a525cda095188a880148410081e11000000029396341084598050d0058949460000005c400c1022225041167bc982810215d108660445c11c5981883110040090100ea084298fca224c895c01b8b0b5a3c07060520e1430838514),(0x6a6bc7ebed4d2a345b38574a16e98bba377069e69e359898dae3665a52330b2f361b089b7376dc27943e9f37f5e70ecb9f9f8f772f7243a2bf6afdfc734abbee770518f85fd356957615c7a350fd041586045cc0004c01807f83f01fc1f80fe0,0x1150c50005510423004620055345c1602f162048c8ca82650c60ca870000008b0d6202a489c143470383908b111000308000061510910804771848b03e62021826068752e64222d1045080102008a17603dc434d4a4c01801501f00bc1780ae0),(0,0),(0xd96a8401f93bd5d7e37ab2ae2086dddde99b7e7ce56ac636a362a86af3b5bd1ef1bc21122d3f017bb9d065ff3606bd9fade57876f3c3ddd43ee0a8656698f71d93bb75282d8bebbb7e3cf88f97be108208db2120107001ff8003ffe001fff000,0x749c505045081bf1968f31404ea40e5150321900280a44460886804a80dc11a8958c48050000a942082104214c12c0490a7124a00ca80cc6f0311046c2002284c1b81480b41aa86072d21ae201121f44458d1644ef001a90003dba001eed000),(0x6f5c35d76aafdebffb16ff0e459077190855a0e1f4f27fd741781bc5e7b7f553160ca7d7e8eac797654d2f851e3842889e53329e1c4713dfc69375ebe0945c3dcb2bc8f2b8aa8c59657363e02a4768403000821a42fffe000003fffffe000000,0x9424d1e762510c1451b8800088d501acc39d08b862823260873b6a014080119a44be8000488806c95180394290b4248ab27494d30a0638c807b50884563205a8cb90924d08040202243520024ac860875794f3ad9ffe940000037eff7a000000),(0,0),(0x8edf5f98f51ad2f61b75ef9bb5f47475b46e3b79ae3553ea63d3b78e054759a1eeaecc5bcb9d8a9c3f4bcb92203bf1cd93f5adbf3f3a9ff3fda9d1a90e252a4ac9c1f5dc3e78a8f8bb6edcba8d6edc10aac0d3a0527ffffffffc000000000000,0x48800a18180a004084010c0020003c0200600005150149981004140002320c2402010953041490008c2c4224400a11000008082064004012000020490188e04210604800000805001000400004241e08a8230c1220016a56eafc000000000000)]
def x367columns : List ColumnInfo := [(524,0,355,0,7),(545,0,334,0,7),(64,0,1839,0,8),(546,1,332,0,4),(256,0,1647,0,7),(525,0,354,0,4),(70,0,1833,0,4),(772,8,99,0,4),(0,4,353,10,6),(769,32,78,0,4),(556,0,323,0,4),(514,4,353,8,5),(2,0,1901,0,7),(553,0,326,0,4),(2,4,353,8,5),(609,0,270,0,4),(522,4,353,0,4),(832,0,47,0,5),(800,0,79,0,5)]
def x367autos : List (List Nat) := [[],[32,83],[48,129,82],[80,129,50]]
def x367levels : Nat → Packing
  | 10 => x367l10
  | 9 => x367l9
  | 8 => x367l8
  | 7 => x367l7
  | 6 => x367l6
  | 5 => x367l5
  | _ => emptyPacking
def x367index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 9 47 4 11 5 2 x367h10
  | 9 => lookupWord 35 179 8 13 7 2 x367h9
  | 8 => lookupWord 41 53 3 12 6 2 x367h8
  | 7 => lookupWord 3 13 3 9 3 2 x367h7
  | 6 => lookupWord 1 3 1 7 1 2 x367h6
  | _ => fun _ => none
def x367 : Forest := ⟨1903,10,fun j => x367samples[j]?.getD (0,0),x367columns,x367autos,x367levels,x367index⟩
set_option maxHeartbeats 0 in
theorem geomx367 : graphValid x367 (boundsBefore knownx239) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_10_0 : block x367 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx367_10 : block x367 10 0 1=true := sx367_10_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_9_0 : block x367 9 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_9_6 : block x367 9 6 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx367_9 : block x367 9 0 21=true := (@block_merge x367 9 0 6 15 sx367_9_0 sx367_9_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_8_0 : block x367 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_8_1 : block x367 8 1 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_8_37 : block x367 8 37 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_8_40 : block x367 8 40 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_8_76 : block x367 8 76 17=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx367_8 : block x367 8 0 93=true := (@block_merge x367 8 0 76 17 (@block_merge x367 8 0 40 36 (@block_merge x367 8 0 37 3 (@block_merge x367 8 0 1 36 sx367_8_0 sx367_8_1) sx367_8_37) sx367_8_40) sx367_8_76)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_7_0 : block x367 7 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_7_7 : block x367 7 7 27=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx367_7 : block x367 7 0 34=true := (@block_merge x367 7 0 7 27 sx367_7_0 sx367_7_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_6_0 : block x367 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_6_3 : block x367 6 3 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx367_6 : block x367 6 0 7=true := (@block_merge x367 6 0 3 4 sx367_6_0 sx367_6_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_5_0 : block x367 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx367_5 : block x367 5 0 1=true := sx367_5_0
theorem tablesx367 : checkedTables x367 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x367 0 0 0 = true)
  · exact (rfl : block x367 1 0 0 = true)
  · exact (rfl : block x367 2 0 0 = true)
  · exact (rfl : block x367 3 0 0 = true)
  · exact (rfl : block x367 4 0 0 = true)
  · exact allx367_5
  · exact allx367_6
  · exact allx367_7
  · exact allx367_8
  · exact allx367_9
  · exact allx367_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx367 : Lower false (varsX 1903) (graphGoal 1903) 11 :=
  strong_low (m:=1903) (cap:=10) (l:=[(0,10),(1,1),(2,2),(3,5),(5,1),(6,2),(8,8)]) (by decide +kernel) (plainA (q:=367) (prior:=boundsBefore knownx239) (before_sound knownx239 validx239) (by decide +kernel))
    (index_root (g:=x367) (i:=0) rfl rfl (before_sound knownx239 validx239) geomx367 tablesx367 (by decide +kernel))
def knownx367 := extendKnown knownx239 11 [(1903,[]),(1967,[118,130,81])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx367 : Known false knownx367 := extendKnown_ok (m:=1903) validx239 lowx367 (by decide +kernel)
def x383d12 (i : Nat) : Nat := 0x870a08027fd30
def x383l12 : Packing := (1,1,6,0,0,0,0,x383d12)
def x383h12 (i : Nat) : Nat := 0xe8900f505015106818000203000f8150c21070df9100000048f70438600070838a90b000000795984500000e94000000988000b80000807000a85214001f9750a000000000000d8ea8c383000000000102390913a1601171758711230900000069310e000088610000000600004200040000008003
def x383d11 (i : Nat) : Nat := 0x1c190824230b0f060120c1382820e1185870008a051207062610761a08682059c3818302423041f0c4a01081180c12100f8587000880908c343c141428010045070386040360a14026242423090b0504410e00141160e1810840d82870098983120508100b308870604842883e121c020833024230f05050f0a00104149d0212209900100880e06080f07c3c2418004507038406048360a121c0262c35330f070a001424112080a12981650a0908c10706c2800543045840184e161e0c01f06003061211848783000c70908c3c1428036160c0218314230f0b0600ba431de16bb35d297cda91b0c1f1bae692bd157a5a3fa6c0c19261d23304785a05a003ff5c530ffd704c3ff0c130ffd504c3ff58130ffd104c3ff61930ffd614c3ff60930ffd214c3ff1c130ffd524c3ff60530ffc714c3ff54530ffd624c3ff20530ffc104c3ff48130bfd814c2ff20530bfd824c2ff61930ff9204c3fe5c130
def x383l11 : Packing := (25,2,6,0,0,11,0,x383d11)
def x383h11 (i : Nat) : Nat := (if i<1 then 0x108c12584b6a01e9250702cf0cc0000c1740000c24ef200000082800000000000000000307a00000000d00c0001e262000130e30072f935c54d22220000c2cb0044000082192146e0514275c00f609461d4226d9072e165c2cd3249c12c9275d1e0094b4121c1563217729cb1136015a18c916cc9b5617ff180405a72408273128e215d82b4e2af5299a1aadc35411800000001020aa0edc0920001e178000001a331b9519f011b800c000000000000b0b9d1a1f2b49264000161d011180001323b287580c56115b0969051619a0001d289f2ce0000403cc23130c9ae13a0a6621626660062f2780000e01c0000025f61c80001c176d0ad506cd2b162bb503001961174e62e71400001c02ed9d16266011f8acf60de000040f931f4000112b29cc52276415e11e901f40000305e000040da00000000000000000001e048d23f6086842c50af2013101d00c200000001c1e751fa00000000b0daa13e00000206095c71b00000000192600001606661f60000a27c0000000000009a000000000000000000000042200000951000000000000000000001008e000000000001a0e40001d2c40000000000000001cd0e00008101e0d650b7c20ca1fad1ec022af220c4738056a03471d0029c61f8bd4b622e000062b00000205c000060bcb1d22074000020f3c162c04b40594dd1c029316581aea1074ec4607680246038414ace2e880ce26800000000000020b9610b623d403e4143426b20af1252a23b41820001821c6d3470dd221e629fc28c01f0000042266288a018b20c0001e0b6328da11000fe000000000001a1c60000000121bc0001c0b269b2a293c51e61cce017319b009e914e5122f13e20988239418a20a4c1e2e037008bb046355c20a921a750825001a0b1c127c05fa160426400003064000132b8000000000000112471ddb0a6c1d600d3a0cbe13b20dd418fb0e902b8326b90a942a5b2a481fcb05770f262a381b14214d255604c226071f3825c228a22c2d1f7029480cfd2184104f263a08d2a780001a2c600000001a290c054828501c3726c60bbd2c3044962c941ce124e42c0e13200000082852eb0c561c022035d7c4168616a000052ca0000a03ba2bef25c21ddb17a000000000000000000000000000041e80001b25e0000917d626e0001e212406fa139e2440000f0fe00000000206c81704812b001c78038082870c080030c00a950000600000c002000c100000838224003060004083001c01e0e2400a0e000050000302006400600300000a3008e2418005103890a00085020c0040002185860000287001c183062c0960e0448110000000a1c00c040801f023c0010c14682002e4870204000200170a28005170000087102c000020540500681000a04000120031800000800a005830a7418002005850c1cd800a080020400004 else 0x19176000090172191e030f1a7e1dad257e06400000001e008000061ee00000000000000018144000061de0000d188742de07ce005e1408040c1b400004195e51000000001c1be0001e0e20000203224c16228f14b8eb510f862012d39824942d301b620d990bf9c0df29622960000821ae534000051780001d04160c0409c11980000000000000001b09200000000000000008088000081fec2bc000181eba55e0000817c00007d5c0000bdd3e28e0001116a000171c0000000000000000081b200002286022dc0060000000041b8d212000120a27111e068c299a24782ce0000000041a120f7a1d3a0a19086d139a0f54c6640fa81c42128c053e13cf1513167b063e23f8e009282c1986172d0bc000000bfa2332096e154b1540000000051ea00900001d2080000000000000001f938e0cdc2a0000100e800016134000182085160000042500000b035b036008022b73095212bc23452ba0001d535402a20ee64a82271411cb29e42361236e2d682b39089427808c42103f27e00016166d02f80c9204202c5e1d800aa000092c71156020e81306253501082a9a1e4d12a0001c1490061a02771e2004751c6000050ba0000f0e4000090980000c192a0b4012fb134713c00000000000000000001c10e000010fc00000000820531e6d0840001629a0001e2d0202c31729e78027e0000019fdac400000000e04e816fd0fa297c0000419c60f1b29a0001b27cc0209078607e0001c1ec61a44185222500eb209bc070b4720000c0c79054a0e18011053fa15ac14e0000f2ad81e00000211261baf0a2a14d111c00011153255c0001407a2000e00a6243484862aae2119ece0000a0fc000001ac4002208460d46078e0d101f37103610c02404258218911ef8180c254000062560000000162820001c24ac0ac00000000000090d3024ca136303e00010186015021a8b2336116124c215800000001416c425a617a606bc0e6c2d501ca1149c2a67ab502ade123001b627a2022101bf202000194a93a12415200014)
def x383d10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xc4c2e0986ff245824c3ff24008261ff97548130dfecc2c4986ff481814c2ffb2c182617fd9254130bfe4c2c2986ff5d5814c2ffb2ea8261fed7248130ffcbb240987fe481864c37fb24c3261bfd9760930dfecbb02986ff61d504c2ffb2218261bfd9260530feea9b04987f74c5814c37faa2c1261bfc1061930ffcb8102986ff5c1814c3ff120a8a61bfd6160930fee988e0986ff441864c3fba62c12617fd9760930dfea830c987fe5c1814c3fba62b0261ff9700c130ffc48a40987bf585604c2ffb24b0261bfd7560930ffcb830c986ff1cc814c2ffb3038a61ff9205c530bfeca902987fe5c5704c3ff220b0261bfd861c530ffcb8304987fe25d204c37fae4c0a617fc9854530dfe4bb02986ff205864c37facac0a617fd9154130ffcb82c0985ff649864c3ff32ab8261bfd8720530ffc49ae0985ff645604c3ff2e6b8261ff9765c130bfe4c2e2987fb249814c2ffb2c40a617fd9148130dfec0b04986ff609504c3ff24038a61f7d5154130dfec10e2986ff615204c3ff2e690261bfd5320530ffccba40987fe480704c37fae6c1261bfd5020530ffaa8a20985ff658704c2ffb22c1261bfd8760930dfeb1302987fd585714c37f90218261efc965c530bfe4c2a4986ff645864c37fa40c3261bfc8160930dfecb304985ff655824c37fa42c32617fc9848530bfec8ac4986ff615604c37fb22c1261bfd7660930f7eb0ac4986ff4c5814c37fb3090a61ff9215c130dfec30e0986ff604304c2ffb2ca82617fd9154930bfecbac0986ff661614c37fae040a61bfc8720530feea9a40985ff640714c2ffb2238261bfd7061930feea9902986ff604704c2ffb2438a61bfc811c130dfec2b04986ff618304c37f92ec1261bfd8154930dfec0b0c986ff21d824c3efaa2a9261bfd5261930ffccb240985ff65c104c37fa20c0a61bfd8261930ff6b92c4986ff5d4814c2ffb22c32617fd9220530ffc902a0986ff609604c37facac1261bfc9161930dfe88304986ff655814c37fb0eb0261ff9515c130ff690ac4987fb5c9824c3ff24040a61ff95148130bfecbb02987f74c5204c3ff2eab8261bfc9844130bfec98e0985ff648104c3ff2e0a8261bfd9854530ffcb2a40987bf595604c3ff240c0a61bfd31609309fecbb02984ff261714c2efb2a40a61fd9315c1309fecc2e0985fb648704c3fb2a690261bf9855c1309fec9902985bf658304c27fb24c0a61bf92060530bfcc80e2985f764c104c27fb2a40a61fe97248130df6b9304986fe5c1864c2fdb24082613fc98545309fec8102987de255704c2f7b2838a61fe921481309fecb902987fa481524c3fb2a6b82617bd94041309fec930c984ff660714c2bfb2e08261df9755c130bbeca820984ff645864c2ff120a8a613fd9854930b7ecb020986fb249814c26fb2a40a613dd9320530 else 0xf95242a08536ca501441280c4f989d11382268e4c54964127224a448808f291c5230244f488e90c72118418c8068fb71f1c3ce077a0ec21cea390c7088de81b7e36106970d051994323c62a0c2b17f22ef85cf0b7e16742c445788ada15742a4452f8a2d13d226b84b9894111fa229c42d08310fec1eec3c007450e381bcc35c06860c8418642f385a30ad0149027904a508e610bc1ec839e06c60c7c17202b204ca08600f301a202e0048c07d00b6010800dc00b8000ffeb9a20987ff0c1864c3ffae2a9261ffd521c530ffe98aa0987ff661714c3ffae640a61ffd211c130ffeb9820987ff5c5504c3ffae6b8261ffd2144130ffeb8860987ff585504c3ffae488261ffd7258130ffe180e2987ff5c5204c3ffaa4c0a61ffd7558130ffecb2a4987ff5d5814c3ffb20b1261ffd9058530ffecb2e2987ff5c8814c3ffac2a8a61ffd7548530ffeb2b02987ff585714c3ffaca90261ffd810c130ffe882e2987ff585104c3ffac2c1261ffd2154530ffeb2902987ff5cd624c3ffac238261ffd610c130ffe4c2e2987ff485814c3ffaec90a61ffd9548530ffeb9020987ff5d9814c3ffb26b0a61ffd3158130ffecc2c2987ff595704c3ffaa4c3261ffd5348130ffe49ae0987ff548814c3ffae4a8261ffd9254530ffe90ae0987ff5d9504c3ffac0a9261ffd6154930ffebb304987ff5c1524c3ffb26a8a61ffd6148130ffebab04987ff5cd504c3ffa42c3261ffc905c530ffebaa20987ff4c5204c3ffb2eb1261ffd7558930ffec8242987ff589504c3ffae2c3261ffd9054930ffebaae0987ff545624c3ffb22a9261ffd9358930ffe882a4987ff485604c3ffaec90261ffd7254530ffeb82e2987ff485504c3ffb2ea8a61ffd9848530ffeb1302987ff65d214c3ffac4b8261ffd7348130ffeb10e0987ff661624c3ffa64a8261ffd7358130ffeb1820987ff585814c3ffae2c1261ffd9854930ffecb2a2987ff595824c3ff92e88261ffd6320530ffec9a42987ff65d614c3ffaea90261ffd7160530ffecaac4987ff655614c3ffaea40a61ffc9344130ffebb220987ff589714c3ffaec08261ffd1058930ffea9ac0987ff5c5604c3ffac6a8261ffd7620530ffebb2a2986ff61d814c37fae6c0a61ff97054930dfecc2a4986ff61c104c37fae2c3261efd6558930ff690a40985ff659524c2ffb2608261bfd7160930ffcb12e0987fe585204c37fb04082617fd965c530bfecbac4987fe441204c37fb2ac1261ff9655c130bfec90e0985ff65c814c3ff220b8261bfd5161930ffcb8020986ff605504c37fb02b0261dfd755c130dfec10e0987fe645204c2ff930b1261ff92058130ffc98a40987df255704c37fa42c0a61bfd7320530feea9b02987fe655204c3fbaa6b0261fed2054930bfecb0e2987bf58d604c2ffb2c08261fdd9354530ff) else (if i<3 then 0x3821080e10c26040a601286a105824130804700044a20181302102004260203618028241694342111038005008761c003a1002161206061083618086010078601300172d0b000602040a43c01300a461a0c0e0424211080a10180860c042861760817000e022700100d810888614021c06021986c1c0200281030201706a10300860704030042108090ec0130b0904603821308198613020c2143020f8580208408406021c19430a0109802706061a020b0005080c860b26014983a08381604281106800a064a18080158204a1e00e88c1b041c0b021b004c6181820043026020609840a18c002c181408010f800d8181c0d058302e05483c1a4c060270005022385800801080e0660030100219061202820200b37098380a184008607307001808010c0e0802c184028480e06230c1d800a04008661e0028100214124ec01301010021c98090802c8070ce00180f28188603e0e00201338301dc1c00402660d8383180a104008702014124c05940c0c0201f00170283d005070100c0c2c201dc3c0304300438989d8104814104c0801120606133001302180c1703e00300c30180651a0e002604386020c1c008c08602014124c05942e0e0604f0142080110092700700082604008802014124c05949c0ee1b070018021c0805049301650b83b0014035080810470808050590100c0b6002610021c0805049301650af0b82c3c00502004403f000c182c18291512246434484890511f923ddc79b8ee51d0238bc6e58d671a2a330c6268c1f172e2ccc5678a8f143227644d58947120e228c42887db0eee1c04369865d0c3a172c2b385150962120c221842707860dc419882f1051a08ec0d08161024202f4035802affb1fe1bf9a7eacfcb5f793ec97d40f9b9f1e3e137bc2f729ecc3d667a7af451e75bcc27944f1e5e1f3c1e77eaef31dd1bb8c76c6ecc5d7fbadf7548e9edd24ba2073eee715cc0b9617282e485c8538d87170e23dc25b8227004df41bd837876ecedd1db8ab6d16d62da45b34365a6c50d7fdaefb5b66b1ad56daa2352469f6d295a39b426680ccf519c8334c6622cb11952324563f0c73d8d331596206c2fd846b05b6052bf4d7d52f6f5e8cbc09763ae9e5ceab931711ade85b7eb5ed6a4ad055982b261637ac3d5816aeb15b8ab51561aab915622a80549ca8714ec299d52e8a45546d2872506ea0393f2a7aa4eba9cad373a6ac4cf498fd30225d24b5295952a7251349d49299235a43047ea8ee91c4237146908c3515ba261444c88190ea217e4298846906fa0b640f681910101fee3f667e28f911ee73d34797cf1b1dfb3bc876a4ec01d603a4a73f0e609c8f38a87088e011bd037606db0d9d1b1135ac6ad8d391a4934406794cd99966325663c0c63987130a2607cbf217bb2f125d5cb8996ea2d705a18b2a15fe2b865620aa else (if i<4 then 0x2a0c868c05840a0808130121b0286009804820301002101e10064002e043060200b0212820e41a011907021e840e400302804360c1c0b02120e80028408100604c084c003498052509861006018086a1818261020349dc3c183816043b0e1d0026050a1803600200414430ec12750f000405840e100884c0846081c46042018230e05810a100213b004c2c240e88e0f0c18020305f00a21238200405930c07020647c3c0094101808010e05c004c0840604c0830c01583430804f00726031001f0b961cc3030500850b860284203818247876009c0646010d80069300a40ba19821881840298007011583266001c0602182b09047048603470142013c02c301002d0c0980330c0c1002130080080108c1086010013021983c261e0100c202041141402320e042814264e048500e063b0f00802601020660d08160408141343260120010303c21000750c0860860037000b943010c00108c143402064c07010f8002081980070120013341c0e1408121c8608400980c021c1380801300810370899800584008607306190043810c08a150e00100218134206050085830604430604c0844403b000906010c098701a84c30860018044b0426170c043000507011342c0400101002181817028f0000081300850c508081402b0c218009a700c1038340856104300080c161d4221600180431304c1002128580800182004340c2020ac0409000a03020704e000e0502142a14026001c103042001b021030c24303182100d8530004072e1d80272300c0433060d0cc0508200e0220124cc0000200433081c86021030c108200180432183028701b001006010c0602060204c01383030b824118006814c10c0130084210402e04c0130c06c013818042d0e004c03010206a0a001d0702141813020c1c414602c0851384c08344419004ea183008702930080608143007860348c1818400c1302180e83080c0b0c26400080e081c0f0c0681088e0583008421230281005938d800004098042b068543264000c100220180e086000c14304018c20c05f0060c41d1805209425c1260602e1461601380a08146c3c020008102c210c4e618180868440026042133008008010bc2c007420042c04198008012001b3e001a4c0290210e02600985a1200182302170080260400850b06286100be001c05022420430203b004c313187000621c206472009814206d8606080630064005c20385a380c1420382180460180860390838100b04c0a040a60148820e0218060219004c0b8c30866081e180c021c1017028c1ac12750c0e04301b004c04010a09210142e080a0401680c219830380138101002240ec1020e0e8305850205c0e00084c06040c070b8147426150e000608010e8c4430829070c418f8002840706a185820130a60022044d0987000e810206034000a1020 else 0xe0608600085c040051128b0b004488103236184216360b0986100260100702e002004223300101817001002101b416142c085a0e000e082053004c06010a186160028052d05190b021019800801081b210330010021b000510258543c00500a043944218003010a23216009c04284c3819193a8610c04000862607c1830a080418616003c1428400a1f1d0409800e050a8e8613300460d0f010002138cc2c01303c142b0686050602c086c00184140450b000902189820020f0100260108c3c00700814281f001c02101d808604098510040414c00147800843010026010a8e266003640a0703e3080143e32750f01000214218026030812048198610c0030088c0200983c0138083288430100021686040281880d0221860702e000840842c1a04201c081c0c900e06a0a309980021f004e0701091128b08460b021a224cc004c9808001408488944320b02141ec30201c325c013018042043010002810a108588218080130085090240b800a151c4ec0010943028100c403600481b205f004c1210280c0f8e830b46010817210430100021808110c8c320e0c02c817c00102840981c3819205c44228e0042042053004c06010b43c040c0a042e0020041b06858003820086a0a321604201d84040b864a10262003e4c0400084c20500cc20d87ca0703507008c26010e05020187804604078040130604430a8502c0010245c0040243c0400084c202420c2c04000a04394408800c900e1c0c8d83800581408508010403616002004250c181f1e003c141d0f010302810a100430a878080010f800e06c7800e05060503e0008443051c4e06600085c005c9814223b00041e00980c0211820d0802c9800a05c2404284216202e000830be0008162021824ea1932008008011214030101c10281a86040750421800c210019098c3010058300852160020048006c2e70e04008c10bd0f00703e000c4c06010cc2a08400a041204f008c00142030c308181009e00281702811406023081cc3080630080213300132239000409903c100c0102e050a6010240350c20050d81031804d0c204cc001818043e01001308010a4e070130018)))
def x383l10 : Packing := (364,3,6,0,0,15,0,x383d10)
def x383h10 (i : Nat) : Nat := (if i<1 then 0xd0b02dc800311bf40cb600820279105e921aa83e2c2b8009ec0de80291c21c3041f0bcf880b81dfe103b00b80000000011ae78a000003842e0000b02c8000003de307e26c08c25e83340000c04710101e3b410240885484c462a0cdec70cef8354c019a08108f631084412f6033000000001c298e1b77047e41c000000000f0cf80001429a000010400000341ca000020c9a81cc0000c048f8f1f846400220000e096882c80001e0b100005117c0000a1be28ebf846c000000000000586f16111e0b9a0b4f83300000406b000000003b3d9417660fd4824fc26b4171507b805780000000090ec00000c09e0000988b1856f2067c0ee88c9000038389cdb1000000002c37621430000705440001a01a300200000028a803f70c50079c0000000030a7784dcc0a2e1b538073482a23600000c054d4590000000fd98f10000001e540940000487f8000181ee98fce86b5c3d60000f05c0e1c00001e17490aea83d2c0b9414408e8354600001a1a0b1098000000000000801d00002a36820da0000303efe2c4e0fcaad27c4a580fa00003088a9460a308000000000000242c9605f50155005760f8f155e82500000e17c0000f05f08347c397a009b06e20563a08bc17e08d43063b825e00006024a0496004c0000a03c4418782020000e0c7c8040a2b7c17a0000542d000000000500a5023362ff01f5a0d5788390401216b609ebc529c407e120e03458779a399806ca0909452f23740206000000001016a61c1700c6984a0393a0e9000044489237b403c0000000000000206f000000003400c000000007429484160000905dd01eb625f711e0000000000000000000007c5a288698061c4d1000000001f1b70000000010351c17808a0cc135808721db8452583dac2e6509980d380000000000000000704e000000000987e80002c08d30d3f8bab84fb03a40000b0e7800000951b1be0060782a00001408d90799051881a000003059944ac000040a300000000000000000987780001c1fe60ada823cc7a5437e201f40501077f43328096481dfc34a036950933011b073222b391b9d2520000203f00000b0bda80ad8346c16d00003045800010162588d841e140809c1870104082050cd00820a0850238485800b74102280010b42043800424085160439d081668b000048004747080039a8b062801302040366c10080261420002380020a0028400181857008081020000f303c20d042818000301010200a80060c5020a0000906006000608003000800e02e400220000800000002000419b1e0040326001010608385000009d080000404000000c040001200000020090100002041e4830f04002930200706160830a02ac09d04140000000081000c200002c1810a00200001020a180448900149010208002160400022040821a0408b020080e000c080 else (if i<2 then 0x620c6062b07c74201e05d00004b8188104a022f102663052264a15600b6281d6a22ae19b88f400003f25c0000d804a1459019ee016106c78218a2f62db20000743cca3016025d8c5000014255015f000068071406b98c378511030e017f610d4854000004847a210d8968a41201cc0000000034799dbbe00003829c87ec00016008708efc6cc0001d16b91078000202590112787b387b461b335ce50c00059a436c4117f83c084ac205bd612f83ad84cc81ac01a548f7d062da34a719f90f35f7400001f11066618c15f032281d7801bdc43c0000e0890000000000000301f000019693016d20dbe8c400003c0ef0188a0c90c08a441bc0cdb8b9c82984076a177b90280159642841a6a0feec42f414a2563609dc801fc17ab15a10b1fc46243aa90f9d2509032b61bd6186e833905950850c1f4b85bc806e814fe0aa10585046b8229207cc0eb68409228581b041042837de29c70e280ea10327840a21e0608ab086202b421c29887287aa82a131ac8033b87c84319008810f2d405388796216709cb87ffd3a1110138b31070d005805c650257c4c2c10fe113e04c04735013780e8d0d6600e7012420fe9841ac146013291e75017b400140abf1d928dc6c3b601d42036501880002e942e1420000000000000618498e548270405ce15700000000300260000f0350000063ee508798cd000002050000000005038203f2e021f82fb63e00000a1b9000000002a0da00000000000030305a10950ed4874c000000000000447210370000020c0a44ab418e600bd01ed04300001e019501a186bd8238013f60aae849dc295213268db00000000000001881c86ae611831f800000000000014027f8d380000420e0000800f000035ae5c084a0936c5b68352f06a208378856025c4108c05600002a1420000701f00002406420ed28245035280e2000000000000000000000d866604282338804cf03f503d5413e0000208c000014403608b78e1800000000000030480000000000000000009370000180de000078663216da0d900002409821ca612260b0000000897e0ae10e0000004a2200000000712a50247c1fcb0012026b60e4e0b42022f8507823fc06dd0c1a0655014540bc00003835c02c20000000000002408200001032586c9c42980e200000178c000000008069907cfe058802487016843f23fe801d808800003c2ff4129b0418818ce00480cbd02f2c06d41e2ddf790b50827482b2620990be0052081a4f1fb70d70464203d3f19910a7f030a628a604748428000240c08153d0075033800000000003a584d3c1f2ec68000000002c0cba1700072400c0000000005025881094363a11e0000507348248f19700003c7948a776050302728548000090d0180544164438e2104d06408014c09aa168d0f4043ee80ed71f5e0d9e024460ab71118 else 0x323f4000040e400000c0ae21d9384d0000162420000a071800000000195600003c83c0000000000ee9052cebef81e382b90000143efe0ba6057f0526c0cc0000c0d2552a4c2fa000050d100003802400005016d42d40001a0e1801c4071684148028787ac018b229081050000644d40001a0850000000000000000040a07802800000000000000000000070a3000068718000181f07827d814c0000c08a000000000032ec189104aa81ef43d80000509b00000000030a60000083afe1cc000062ddb81a703a2cd5d00e5000004260000000000000083ec000000007014b818db05aa0ba803e800000000d0c87c494401e0000403f80003238e10c956656016f0157c1e14000603b1c0a9215480dd2c4fea1e8b0ebc8332867942dcf17d7006d438ee42764d34039381e78339421260e8001696851c16fb0148b12e6bd1d4a8000000000000120f00000000000000917aa0c680001c0dc0000000000000000011580000201c0421740448856800000000c1dce062000000001c2110000584e800000000a8403c59c0001e1ce00000000000000000507380000c25040c15e8b8000041bb01e2ee3a80000000141e4b0c2b85c80000405800003851d42ce0000e10380000000080a160c3f0652800600000000000000))
def x383d9 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x9161930bee6909148130dde244955c130df664d2020530afe6a131481309fe2a551481308ff6859854930afe2a1105c130dd76555320530cdf660955c130afb6888760930dde648955c130cfb65892605309fe68890545308ff6a4810c130dee6512004130af72a13160930ede545855c130efa4812160530cf769d9320530cef651861c530fd654d755c130f5e5d5655c130cdf6557020530cfe641861c530c7f2a19704130f7a5c973481309ef2a1941c530dde2819520530cbf658810c130f5e5c4955c130cfe261105c130dde6552020530cf71cd93205308ff698985c530cef6a1941c530c7f65d7020530cdf65551619308ff6a55020530aef6901061930afe2a17060530bee6909054530dfa649201c130ff84853148130cdf6555320530e7e5c5855c130cbf660965c530df5645311c130afb6888720530dde254985c130b7e69c9054530af768c9161930cf729d93205308ff6a47320530bfa6897054930cdf54c9854530cdf1cd9520530cdf6558720530abf6981061930cbf6598204130ef54c49161930cdf6819520530df664d7004130ff44c5715c130bbe698935c130cfb649821c530dde6557020530cdf5459854930fd65455348130cfb649811c130cbf659810c130cdf6558204130cfe481981c530adf694811c130cf764d821c530cdf69d9520530dfa4809854930dde658955c130afd6847320530dbe6592004130fd35495348130cbf659860c130cfb28997605308ff6a19654130adf694810c130afe2a17061930dd754c9854530dde6552004130fd654c9054530cfb649821c1308ff6a57020530bfa6889054530bfa6897548130ede2957061930adf6948161930cdf65575205309fe2a5515c130cfb6498704130dde54c90545308ff2a19758930dfa48098485308ff6989854530dd768d9520530a7f69c1061930ef64c57061930dfa6497004130dee681941c530df64c49054530bde6949148130cbf619961c530dfa649201c530dfa6492020530aef6907320530afb6887320530d7e65d70205308ff6a575205308ff6a521619308ff6a570619308ff69c9854530bf66855348130adf6948160930cdf5949854530dee6517004130ef54c52161930cef65187041308ff6a19254130e7b5c97360930adf6949161930cfb6099204130cdf6555020530dee651201c530f7a5c57248130bf668c9148130efa5492060530bbe69891481309fe6a5201c530efa5c92060530af768c9160930df3649311c130bfa68951481308ff2a57160930c7f65d8204130cef6518204130adf6947320530afd2859660930cfb649861c130d7e65d20041308ff689981c530dbe659700c130cdf295985c130f745c5315c1308ef2a1941c5309ee690905453097e69c9054530fd25495348130bf228d72481309fa6889054530f5654d755c130 else (if i<2 then 0xdfe2a57054930d7f65d72041309ff6a552205309ff2a57344130dbf6597304130aff6956260530efb5d49260530d7f68d9704130bf728d7244130ddf6557604130aff2a15260530e7f5c57660930f7b5c57260930edf5957560930ddf6557320530dbf648965c5309ff6849854930dbf640965c530aff6857560930dfe2419354530d7f6899704130bfe69d6148130d7f65d7220530dfe5c09848530ff64c56548130ddf5949854530ddf6557204130df76495320530ebf5956260530fde2815154930dfe5c49054530ff64c57648130dfb649211c130df76595320530ebf61d6158930df764d7620530ff54c5215c130dfb649521c5309ff6989854530f7e5c17558930ff64c57054930dbf58d9758130aff2a16560530ff94853148130aff6a17054930bfe6849748130bfe69c9148130fbe480965c530ff35c93148130cff5cd95205309ff6a5621c130ffa5c92058130bfe6889054530aff6989760930aff69497605309ff6a57654530ddf6557304130aff6952161930df765d5320530dfe659201c130ddf6556320530efe589855c130aff6949760930b7f69d625c530aff6849760930edf6155158930bfb68971481309ff6a5611c130ebf6156158930fd754d7548130fd754d6154530f7e5c175485309ff69c98545309ff6a5211c130cff2a58154930aff2a17560530df728d9758930bf728d7258130cff65d8204130aff6848760930dbf659611c130dfb6497604130cff659821c130dfb69d9204130fde545655c130edf6156154530def6517204130edf5d55320530fd754d5220530cff6498720530def6517604130dfb6497220530cff65d810c130d7f65d7604130dfe5c09858930cff65d50205309ff6a57220530fb758d5358130dfe2419654530dbf6597204130efb5c92060530efd5c49160930cff6617648530fbe58d7058130aff2a17244130bfb688905c530fde5456548130cff645821c130dfd645611c1308ff6a57060530cef651821c5308ff68898545308ff688985c530fd654d70549308ff6a4811c1308ff6a487205308ff69d9320530b7e69c9148130dfa4819204130f7c5c5515c1308ff2a19154930e7b5c97160930cfb648811c1308ff2a57161930ff14853148130adf6949160930cfb2499760530adf6941061930cbf260965c5308ff2a1965c5308ff2a19654930df664d201c5308ff6959161930cf74c59261930bf328d7258930cdf6557320530cdf68d9520530df62419354530cfb24995605309fe69c9054530fda5495148130afe6808720530bfc2859648130afb68810619308ff6999854930f7c5c1615c530e7e5c171619308ff6a1961c530ff248553481308ff6a531609308ff6a57161930fd654d515c130abf6987320530f3e5c0965c530cfd2859261930cfe641821c530afd2859261930cfb289 else 0x56148130dbf685960c130bfe6949748130fde484955c130ddf6556520530ffa5c91048130dfe24161545309ff6a5521c530cff6617644130bfe2819548530f7e5c0905c5309ff6a56154930fb758d7358130efb5c91060930ff35c953481309ff6a57620530ff554d615c530bfe685655c130fbe5c16158930fde4c8955c130dfb685921c130efb6097254530dbf5d99604130aff69d6260530dbf69d9604130ff54c52154130f9f5957558130f9f5957558930cff660301c530cff6498704130fd754d1054930dfe0c1901c530df754d9158930fd754d5158930aff6948760930dfe2419254530f9f5957654530bbf6856558930cff261705c530efd5c55160930cff6159158930fdb5497254530f7b5c97358930cff548985c530ef74c57560930dbf6597620530bbf698301c5309ff69d9604130cff61d9158930dfd645710c130efb5d89260530fde54c9054530f7e5c1625c530bfe69c9054530ff54c5705c530bbf698935c130ddf6557520530ff654d61481309ff6a4301c530fde5457054930fd754d7544130dfe4c49054530f7d5c57654530ffa4817254530efb5c98254130dfe641521c530cff2617544130ddf6557620530dbf6596304130cff661625c1309ff6a5610c130dfe28d901c530fd754d7558930fde584955c130efb5c962605309ff6a57520530fdb5495348130dfe2819154930dfb5c99254130dfb5c99258130aff6a17558930dfe6457054930bfe2819558530dbf68d9604130fbd544965c5309ff69c9848530d7f65d7620530fdd5c55154130f9f5456558930aff2a17160530bfe2815158930f7b5c97348130aff2a57560530efe21d1048130efe585855c1309ff69c9858930bfe6989748130dbf258985c530dfb6496304130cff21d9148130dfe645201c130dfe5c09854930f7e5c0985c530ddf6557220530ff64c5700c130def6517304130fbd5857158130ff54c576485309ff69c9858530cff261105c530dfe6497020530dfe6597020530fd754d9548530fd754d6154930fd754d2154530ffa5489748130fde5949054530dfe5c09858530efb5c98548130dfe2417654530ddf6556304130dfb649625c530fde255625c130ffc5c49148130dfb699921c130cff6617548530fde5d56548130fd754d7520530f5f5d5655c130dfe2412154530f7b5c97148130fbe5c16558930ffa5c92054130bfe684935c130dfe2419754530efe5d52060530bfe6956148130dfb6497304130efb5c92061930ffa481211c130dfe65d2004130fb754d6158930bbf68d6558130d7f65d6304130cff645860c130ddf6899520530dfe65d2020530aff6956160930bbf6983061930dfb649621c130ddf5459654930efe5c15261930ffa4817548530cff2617254530ffa4849748130d7f65d73041309ff6a56520530dfe649700413)) else (if i<5 then (if i<4 then 0xa67e986a58e940a49e90ea3ae8c8a2be896a21e864a12e832a0667f69f9e7ce9eae7929de67609cf67249c567069b666c09a7667a998664898be60c97ce5e4970659e963e56c9526530940e4e0931e4a4918e440904e3f08f5e3be8ebe3968df63788d7e3468c8e3008b762a68a5e2748996242887e20687b61ca87161ac864e18485d615c850e12a84460f8837e0c682de09481ee062812603a80860087fe5fe07f45fb87e55f727d65f367c75f047b85edc7b5deb47a45e7879a5e5a78dde1e77edde276fdda67635d747595d4c74cdd1a73ddcd472edca271fdc70715dc3e706dc0c6fcdbd06eb5b946d75b3a6c35af46b6dac26a7da726965a40689da0e67d59d266bd98c65cd95064b590a63258b0620d85660cd7fc5f8d7c05e9d7845dad7345c1d6ee5b2d6a859ed6625925626580d5e0571d5ae562d568551552254254f053354aa521d464510541e50153e24efd3924de53604ccd3104bb52d44ac528e498523e48451ee472d1a8461516c454d130445d0fe43950cc427d07c413d02c4024ff03f5cfbe3e94f823da4f463c8cf0a3b9cec43aace88396ce4c38cce1037dcdd436ecd8e35d4d4834bcd02337ccb23264c80319cc4e30acc122fe4be02f1cb9a2ddcb4a2c9cb0e2bd4adc2ae4a9629f4a5a28dca1e27c49ce26d499225bc94c24cc91023b48d4229c88e21ac84820948021f547b21e647801d4c7301c5c6fe1b946cc1aa469019dc65e191462c187460417ac5c8169458c157c54614b451413c44d812fc49c11bc45610cc41a0fdc3d40ec43980dd43520ce43160bf42d00a8c28a097423a085c1f407441ae05dc140044c0e6026c06e0104000cff549981c530cff54997605309ff698985c530dfe5c19158930ebf608965c530efb5497260530f7e5c1615c530efd5c561609309ff6a5710c130aff69d6160930dfb649611c130efe59520605309ff6989854930ddf6999520530aff2a176605309ff69d9204130ddf69d9520530cff6598720530f7d5c57254530edf5495161930ffc5c55148130efb5c98258130cff5c59854930efe5d92060530cff261985c530edf5955160930f7b5c9625c530def651521c5309ff2a57161930dbf659810c130dfe2417254530dfe5c0985c530ff64c57548130ff64c5765c130dfb5c99204130aff6957260530ff62a55348130aff2a15261930aff69c8160930dbf259985c530fbd585625c530dbf659610c130ffa4817648530def6516304130ffa4817154930ddf6555220530aff2a56560530dfe5c19654930f3f5c0965c530aff6a16154930cff65c810c130aff6988760930dbf659710c130ebf58d8758130edf6152154530fdd5451054930d7f6999704130f7e5c17154930aff2a55261930aff69c9160930efb5949260530dfe645700c130ebf58d8558130bfb6897548130ffc5c else 0x606826020c0003804181c03008306404102e028814e00181f000800830400c0107c0020020c10e0004181809808302c0410180800830301001060583002808407410101802080b304190108c0318020f00014101860020810600041e820283e342c18230052018098083033000400420300700831300c050602838080c27040041830080b80060407832020c0c01040b80a201810100a02080be000501080582e028c0b0381801080281c020c13b0c04182e02881e05c412008203018101c0603230340412000d80830180e0406c0008220c130406218200f8c0c064407030020c0c0398005080804170145c001a020c180105c0020020c170144070180b80a40400410300702e029017014460d00060084c001b010609d0002808401010101a020b8001040c020201b800606060262e000410180c8b43010441d0007020423806050609d004700840301001060b80a203010102e0c8b8001404183007008305c0510180980831040406460302e2047800300420000a808306413160008008301c05010606026020c0406454000a080c0e088041826020ac10140607c8070082c001b0107430180c8c1301c04181606008306188e000520281200a31300410380b880f01c04064980036020c10010405808209c0410080a080c04c0418180b8810010409808205c05102e028804082e0c082701040700c020c0e05c181808080813c00050109c002e202c04102808080b03004184e09890c0405c0036020c136018e0108438082030100107c00262030100106060080f8c0c04c04181802080c0401f1f0002820301c10100e0203e305c0510274000a0210132028e01080b80a2033800400421180582030301301060001c020c06e00181f000e008304018e0014010a0f8080849c1317c20100502c80200a0c01641441350cc1e0023010e028200980c40140404c0b21822770008046021bd90f5dfd54f517d18f3d7ce6f30fc96f1cfc5af12fc28f017bf6ef77bbaee87b7eed97b4cecf7b10ec07ae8eb17aacea27a52e8e7a0ce7a79dae72f9b2e66798ae5ef958e4af908e3978e0e3478c2e27f886e1df854e0ef822e0277d2debf7a0de1f764dd57746dc8f700db776c4daaf692d9e7656d91f61ad8075e8d7175a2d627570d55f53ed4974f8d3574bcd28f48ad1ef458d0ff41ccfe73d6cf1f39acddf368cd3f336cc9f318cc272f0cb5f2b4ca47278c95723cc867200c79f1d8c6ff1a6c60f16ac51f124c42f0fcc3670c0c29f084c1d705cc10f02ac01efeebf56fc6beb6f94bdc6f58bcfef26bc5ef12bbe6ed6bacee9aba06e68b8eee22b84ee04b7d6dc8b696d8cb5ced50b506d1eb43ecf6b376cc4b286c92b20ec74b16ec42b0a6c1ab006bf2af8ebc0aeeeb98adfeb66ad36b3eacbeb16abf6ae4ab2eaa8a9eea6ca8fea26a80e9eaa7469b8) else (if i<6 then 0x1029c008190145c002424380c101b6091c0c9005e000418200c081803840700828382028200f8c1305c402f00020c2401206180bc0008301022101c0201641338009068004040bc42880828302870404080885881306440bf00020c0ce0004182e0208170101918180f881001019180c08081301448607800105c000a223b8001061702e206380040612700020c1901040a0419060041d8208080d218402832020c130832020819010427008204c05e007c0046204c101032104013101c020805013801f0009081f0704020402830200600e10998004830100506460300a204c19170008081b8278004080204420643c0060b089dc0030119004e00051809c008040644027000e0c2b08260270030182127002040131030070804e00051a181e00285841004c409828201410170010141f1028142c221009c00c002809c00c050105c00262e00171026104c361808204c101032020805e00406d00080c2306004e00885841b0538009480700820400c04c60f8282038191418260804064402016205013e007048280f8c0e010406a1c20600601060c5840c8c13830402818242c20ae00080c13040406026203804111160c16342c20203e2010050646060262014191701800b800408c1f0002080e0826106010010132026080805e00041f000b80a302c13103202080507c40200a0c8c04080485841c01206184802700382c20a021c00c8e01380180903081403004c00884821c00c4c0b4402809c00c2506c1804f80050dc000a020c250504ee00802e00098ec306440283e203020203e241b8010007e0040283e2066c10106026000e0c130101918300a38402700505024603e080ec10808c0038301404e007a08082064041009c000a30020020806e00415840608220c881305040602620501310260a080406440f918203020a026020c040a4412032206405121610701910320c088c0f0161080e081c0c8814013801f00028203030041029c000a3010201008830819010051801c000a020c102301f185802082b0f00108c14e0060c8262c00050406027002a3804e0060204020141f102e0c080c080a0f88860644020322b0404218747008c00c0407c402054223b80010683040701040283e2b040603860c840507c40a820030c10e00131808148888b050603b80291c08008304805e00142018020810080426700202c0c01061381808008401413100a09881006440b80a205c05100a0e020303013010606026020c0406040c038028c170301318160b80a304c0ce00100101730080a0813e0005010960d00060084c001b01061282409f000b943101440c038028c1001040700c080c0c0405848280c0200314040a019430806032205004064606500080c04e002b060808008205c051018098083c001b01060704c0c8f8006040c008200010010 else 0xe0080c8c19070402f00020d0e0828c002e09930001024182810330004c602899c00084017000106080402030202f00020c1706405185610141f1008028323080171021c00083c0004102802081708330002e09900c0864068817c000418280f880501019180a08099c00085e00061031c001a099005e00041826106020283e20901f10a21c00202e00098c4e13380a00826019c00c14e00051810b082610141901060e700203820a099c00c040b040c03220111d10240a00bc0030541a800386060780010402f00020c040f0010178004c7c00080e0c18018041a0d4008190144060262050201027818203838205f000e00840401f1027c0080501019181c0220c30501f)))
def x383l9 : Packing := (537,4,6,0,0,14,0,x383d9)
def x383h9 (i : Nat) : Nat := 0x3c43088e4114c1db833e418f8d4205aac42c84c06291440000835c03251a40004012000161bc000581af072000041b3c0a409b4163c2379201084f118000244380260002c1c08000000214f40d8000c8d60003a8288700000000084018186918a190000401de007121c000780710af1162c41101e0000e168000707a0000e08a0072827c0d60002c2180000000c02bc2ec331c012e05d441c06d00080000000588858b5e2260089615187e00a90316050e0fc000161dec01a906a0a0445d84a105600000002879a06e41b1011e851ba4ca0f34170000c82ac44f2011030e00400038066c8fa0c071e000000006088805082f0c10684dd18b833000000ab20bf627ab4210d1284c02ff0594064f00020d800000006d64c4868780001cd6901a380f2074823e02d800000c350b80124873610800000005532907a2205d10000010e8596922a001cd05861940001a23707781ed039004f8118303d446c01040d30ddb404786a00013966e028000d02ac080000483f52477141410b8450000a1590290000e09359d8000084cf07d01f5000c86e60e20001c42c85c2097e02c0001077a0fee851a1a3c4ca0c621f0e416829e29c007c0000087604c0002dab384170eb4153827000000010d774033805f8fb31da412f847a0902100000000db05a686b8198000d80fbc535020599b0605fbd001000012012cf700028204229111c0908e3e2230f000848000080290e1c1040400480
def x383d8 (i : Nat) : Nat := (if i<1 then 0x2afcdb920b0aa2985d79b72815154930fe92a6902e4a8a61b5e69d53241514c3bac482a6b0aa2985779b72819520530deb2a6d1120a8a615fa6c89064d514c37b4d12ca482a2987fc1214c57548130cebaa6d3930a8a61e795c971545824c3ee8b8a62b82a4987dd1315c17548530aef172b092ab8261bda68953241514c2bf4d9120cb2a29857b9b42419354530af736848242a8a6197e69d31241514c379cd22ca482a2986f58a054d9548530e1f930b812cb8a61d9e241655d9514c2b7cdb060c80e29855f9b72419254530afd364482eca8a613ee6d0a0545624c3b6c98b2cb8060984df9b72815158930af736848324a8a61f1d595715d9514c2bbc5caa2b2a409867e9a74809848530adf36c51b2038a619fc2a571545204c37b8b8b4a48a409857b9b42419654530cef140d332a40a61f78545715c9204c3eb8b8aa2b82a4985fc8b35c910481309ef174a8ae0a9261bbc5c5a6245204c2afcdb920cb2a29877589054d2154530cf734898920a8a617b66d8a954d204c2fe459ae4902c0986f58a054d51589309f9974b926290261f744c570261714c33f4d12e2482a2984f5db528d72441308ff174c8ae0a92617ce6d0a0545524c2bf45ca40b92a29857b9b42416154530c5fb4ccc06038a61d3e5c096261714c33dcd22e2482a29847f8b9685655c130cebaa6d0930a9261f595c5525c9514c2bbcd91224aae0986b75a55c49160930ff824298aec90261b5e69d65241514c2afcdb920c9aa2987f5131484955c130af9966b9324b02615de6d891255704c33ec98b4e482a2985778b9484955c130fec2e2a92a2902615fa6c89065d514c2bdcda120b92a2987fc1214c56548130aef172a8acab8261b7a5c1a2241714c3ee098ae2b924098636d956888720530ae73684892ab82613e36d0a35c9624c33ac54aa6a8ae09867c9a24c49054530ae73685032a40a610df6d5a91cc814c2bac5caa2a9a40986769536889054530de3348a9920a8a618fa2a1925c0104c3ba4a9a404c2a4986799a44c49054530f3a2e298ae0c326197669d31241514c23bc5d32ab81029863d8a864d7004130c6db2ad10e640a61bd268953241514c28f6d9150cb820985799b42419354530ceb2a6d1120a8a614f36c8a764c814c313ecab4c39902986f49536895148130abb36e48326a8a611ee6d0a9545204c3cb8a8ae2c2ae098535db529d9320530f9a262b812cb8a6155e6dca0654814c31bacab4239902984fc5b128d7258930c6f150caae040a619ce69153241514c32bcd3aa6482a2985769b22819520530c4fb2cd2902182619d654da7241514c319ecab48399029857c9b22419354530de92a4d0aa690261b5669d53241514c31dc54328b80209847b9b42a5515c130c6db24d29023826195654da7241514c33a4a9b44482a2984f89b428d7248130 else 0xa04080411b800083038008050ec203220261000d03004c604c02f8018190082b840604041c00bc00041000a0041013081900820261008064404c02080c805101400820005008202e04c4040020800032010406420140c880a38010050819008202610018f0001068302064208c2e0002080a0400643e002000a14181000c02620321f00102010200104050087801800601310190813080570020023028202601040143e0020500988006420100c880285c0068007c0040a5c27000108000be00020c0201910009f801000a004101900a20609029e006003010010008203204c4e00068800602053c00809810100020784818020018802c098191814008270002c020c002c0c005181303e200806440f00040020c02014101400820080505e0002080000806440008064404c0288000160100c8c020191005008201c08c40f000600a0fc000b00830018f0005060b10e00028c02818100b0082001803220004032202010080644000a01040f00064028180085f0004c0282300857000140981025fbdf3de0dde5d65ce5c0db8db65a3590582d75567d5a557d4a542534d2cd1f511d044f6cf44e6cd94cbcc94c6cb94b14a3c9648e480c78c7646345b45344b43dc35c3342b423420c18c10c0e400bf8bf0be8bdb3c83c5bb83b03a839ab9838ab7d37536d35fb5d355347b3fb37b2fb27b0f30caf9aec2e9adc2d9acc2beabc2a92a6a9ea9c28ea81273a7126925ba4e24ba43a2b21820a9f79f51e21d49c71c49b19a419698917b97917696916695914b94914693392611890b1088f58e28e00cd0ca8b78aa09c89a08c88a07c87486706485705483681880055f9b72412154530d7d240542e4882615ee6d0905d9514c3e3cbaae0b2ac4984f9db428d7258130fe92a454aa6902615ee6d09065d514c3fa4a9a40baa42987cf1615c1625c530eeb2a6482e4a8a61dd654d31241514c379cd22a6482a2987759535c490545309f3b6851ae48826179e2c151595624c)
def x383l8 : Packing := (145,5,6,0,0,12,0,x383d8)
def x383h8 (i : Nat) : Nat := 0x69cd0e58cc99c8f601011703000195b92786f04a09f1f785e0ff06e1d000488000491000000112e19b8e01401b71eb1a202b00c16d0ac1c77b00061069480d20b513000c0800060ca9e107b15000000000a17000000918405022714d38b0580403050900
def x383d7 (i : Nat) : Nat := 0x7c00417001005b80100985e000105c12f0020000000d08085c008000810050800643b841f800dc0002080008101908068401020081ddedb63acd3e5b2380b1d4a6b1889c3a130479b59a2c057aa932883b968aa44198882200fd4153545715c9204c35c654db42416154530d559536dc90585514c33b1595b128d7258930e5e1722a571545204c3d344c570258985c5309f89c42cd72481604c31ce699b42819520530e7195369131241514c39d254da25c49054530b639c4241655d9514c25e3710b35c99258130de49526d8a954d204c33d2481b528d7244130d719536d090485514c25ce710b95456548130d719536d0905c9514c33e2481b428d7244130d559536dc90485514c2bc6710a054d5158930e5593169d53241514c2b5671ca054d51589309739c42e551595704c39c654da45c49054530c579a66dca0654814c338e595b42815158930d749532e5205c9514c24ce321b4244955c13083b8c86d0a9545704c20ee321b42a55148130c719536d0a9545204c29c6710a954d515c130
def x383l7 : Packing := (32,6,6,0,0,9,0,x383d7)
def x383h7 (i : Nat) : Nat := 0xf090b26608180000002
def x383d6 (i : Nat) : Nat := 0x9840081a64480f2a0a9ae454ae2a8a409844ce361c42e551595204c28e91b4a9972902e4a8a610339da321b4244955c130
def x383l6 : Packing := (4,7,6,0,0,6,0,x383d6)
def x383h6 (i : Nat) : Nat := 0x1e0
def x383d5 (i : Nat) : Nat := 0x261d1505c4da54cb94817254530
def x383l5 : Packing := (1,8,6,0,0,0,0,x383d5)
def x383samples : Array (Bits × Bits) := #[(0x6962b51d723e7f33da25956c0db293cf8cc9e38f4eaf361f4bd9783fbfc3b64918aed47f3b8ad9f6e4eb63c72aff8ac7170ce23a8ceb35aaae751eb65dbfb7361c8842280242f80820f801813e002c6004203f193090d9a33c9401c73e21f673,0x10200570422c0241000210001e04008a1401a2109910250308200400000e1881100800204040200022c040800009001ad0600a408000002e4045a0002a0511408800a3495438702d4260241c04002c6004202519200091222c94000224212652),(0xa49dd959c645eaa2c4bfbb9dc4f31c57762f73bfe57bd4f0d6bafe6d31b7337207c7f038dc30367ddfb766fb7578fff05c1fd76710bc7d187788f9a508badb7b837e08a4a2301628080044793601008190c2c861f1632604c0ff66a4c8c6487f,0x898000010413b9804385201220400c1582145183040c800000061181a410820000060d08000018005000010212841c010005918424142600908048301402848060430c328a860442a41b48c20a01008190c2886090420400804264a488c44829),(0x35ef64a448465ba41b016ef7c73baa2cb7dc33325e69e9e002efddec17ce0efdcf69a9bbc01b28e93e1d8fddd589883fb25a0ec9defbe5137d9f06c488c5103a397c19c0200104600006483c00960f060704f181c98c38470f188738f1078f9c,0x362c6364010440220478120092b8016a5c6aaa60bb3341040dc8800840814810676032814b0e62e2230b98016449400e3342002b50400160281881874af1000d842872c971782bbd4924830d64960f0607047181498838470a18831071038514),(0xd72742ff3afe73d717ea03c3fc93b86d995305ebdd6bd869b73972b5ceee0fbbdb722b9dacdfc53ec160edfd9d22349074a85936a57613dd0d65f9dd06624a9cf01191524c0100c5c5061a0441203000180701fe0e0fc0780fe0f83f01f80fe0,0x40010c08c20086004002406808054600800051020040208942021000210c0103100404423080000000c443380a348cd04c0009542210220840034810240ebc20084381240c03d04212c9743091203000180000540407c03005e0502f00b00ae0),(0x2c01397b7777729cea499daf5e4d40845d8fcdf6433de78ef561155fe5d7ca2d203d0ea2b6503cc0c8b054ceba9aaabc2bfce93d7cb5d0ae92422487cc02ec7f6bb482020840080465f8100040c7c007e007fe000ff0007ff000ffc001fff000,0xa14430831c122122177d0e15401219054b9600c40427c840a05d0aec5a9146786a53d89d8a3d07dacc08200565825320201e80aa08a3cd90263014ac51b04095703c5c92a3c40f90ad168bc36ac7c007e007da000bf0004dd000afc0014ed000),(0xcfd16b34c654547997712cdffbfd2285c06f286d64d823d1dca1d81ea69eaf59ff7b574339ec0789cd7ad16bfb13a6397af702ff6892e09ea25e226aa9f9ce391e9c4408118ae1021200018008f80007fff800000fffff800000fffffe000000,0x230588070081c408a2b04250a162cf110942540322410a20e60a6820fa608314cc5402d0831642100107017902441c20208181124329065018021a3bd5f0e03b71535426a9078ed290995820fbf800055a9000000fff6e800000fffdda000000),(0xe750dd1ff78bb4b8261870e0c502df18c04b1365f18c65500e46cb5e1077d25795927cc27e1af469a91671a59fa5fd4fa384131ccb51eff4b74882943fa759675ec22005803402100801a44280fffff8000000000fffffffffff000000000000,0x426172941a840251880840251b2a61205100a6448a2125c5a6e9e004480d619e42280296901ae3f606ce02280041a0f805822a021222490f4211138240a473209200f14c2529da9152e03438f5fcba50000000000fbdfbff7fbd000000000000),(0,0),(0xc68117961b9b9d4a65b64086ef6d47863d3b3cef11bc2fc9fcf7199b2cf0e3a5e0d2a04d9967f69aeeaf50169aa6404fffd301c5efe1eb51333a4718b79c13a2de7d2411558c01939201a20281fffffffffffffff00000000000000000000000,0x808004004323120150518020400108a04980020158880120010030a001018200080c8084c400c0848201404300200060078140884048080010420040a0100c0008c0a9152d0212c2d0683c7000345aaa56fffabf00000000000000000000000)]
def x383columns : List ColumnInfo := [(16,0,1903,0,11),(544,0,351,0,11),(576,0,319,0,11),(516,0,379,0,11),(562,1,332,0,4),(525,16,354,0,4),(540,0,355,0,7),(545,0,350,0,8),(256,0,1663,0,9),(2,0,1917,0,9),(518,0,377,0,8),(561,0,334,0,7),(582,0,313,0,7),(569,0,326,0,4),(864,0,31,0,7),(546,0,349,0,7),(788,8,99,0,4),(548,0,347,0,8),(577,0,318,0,7),(586,4,305,0,4),(581,2,312,0,4),(772,0,123,0,7),(320,32,30,1,5),(802,64,29,0,4),(616,256,23,0,4),(785,32,78,0,4),(519,0,376,0,5),(774,64,57,0,4),(614,0,281,0,4),(80,0,1839,0,8),(834,0,61,0,5),(538,4,353,0,4),(595,0,300,0,4),(551,0,344,0,4),(604,0,291,0,4),(833,32,30,0,4),(868,0,27,0,4),(584,0,311,0,7),(18,0,1901,0,7),(784,0,111,0,7),(553,16,326,0,4),(848,0,47,0,5),(796,0,99,0,4),(541,0,354,0,4),(572,0,323,0,4),(880,0,15,0,4),(86,0,1833,0,4),(565,0,330,0,4),(552,0,343,0,7),(866,0,29,0,4),(838,0,57,0,4)]
def x383autos : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def x383levels : Nat → Packing
  | 12 => x383l12
  | 11 => x383l11
  | 10 => x383l10
  | 9 => x383l9
  | 8 => x383l8
  | 7 => x383l7
  | 6 => x383l6
  | 5 => x383l5
  | _ => emptyPacking
def x383index : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 44 67 3 12 5 3 x383h12
  | 11 => lookupWord 195 795 7 16 9 3 x383h11
  | 10 => lookupWord 265 1075 7 17 10 3 x383h10
  | 9 => lookupWord 51 259 7 15 8 3 x383h9
  | 8 => lookupWord 23 59 4 12 5 3 x383h8
  | 7 => lookupWord 2 9 2 9 2 3 x383h7
  | 6 => lookupWord 1 3 1 8 1 3 x383h6
  | _ => fun _ => none
def x383 : Forest := ⟨1919,12,fun j => x383samples[j]?.getD (0,0),x383columns,x383autos,x383levels,x383index⟩
set_option maxHeartbeats 0 in
theorem geomx383 : graphValid x383 (boundsBefore knownx367) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_12_0 : block x383 12 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_12 : block x383 12 0 1=true := sx383_12_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_11_0 : block x383 11 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_11_6 : block x383 11 6 19=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_11 : block x383 11 0 25=true := (@block_merge x383 11 0 6 19 sx383_11_0 sx383_11_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_0 : block x383 10 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_2 : block x383 10 2 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_38 : block x383 10 38 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_40 : block x383 10 40 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_76 : block x383 10 76 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_112 : block x383 10 112 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_148 : block x383 10 148 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_184 : block x383 10 184 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_220 : block x383 10 220 23=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_243 : block x383 10 243 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_279 : block x383 10 279 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_315 : block x383 10 315 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_351 : block x383 10 351 13=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_10 : block x383 10 0 364=true := (@block_merge x383 10 0 351 13 (@block_merge x383 10 0 315 36 (@block_merge x383 10 0 279 36 (@block_merge x383 10 0 243 36 (@block_merge x383 10 0 220 23 (@block_merge x383 10 0 184 36 (@block_merge x383 10 0 148 36 (@block_merge x383 10 0 112 36 (@block_merge x383 10 0 76 36 (@block_merge x383 10 0 40 36 (@block_merge x383 10 0 38 2 (@block_merge x383 10 0 2 36 sx383_10_0 sx383_10_2) sx383_10_38) sx383_10_40) sx383_10_76) sx383_10_112) sx383_10_148) sx383_10_184) sx383_10_220) sx383_10_243) sx383_10_279) sx383_10_315) sx383_10_351)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_0 : block x383 9 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_8 : block x383 9 8 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_44 : block x383 9 44 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_80 : block x383 9 80 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_116 : block x383 9 116 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_152 : block x383 9 152 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_188 : block x383 9 188 18=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_206 : block x383 9 206 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_242 : block x383 9 242 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_278 : block x383 9 278 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_314 : block x383 9 314 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_350 : block x383 9 350 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_386 : block x383 9 386 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_422 : block x383 9 422 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_458 : block x383 9 458 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_494 : block x383 9 494 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_530 : block x383 9 530 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_9 : block x383 9 0 537=true := (@block_merge x383 9 0 530 7 (@block_merge x383 9 0 494 36 (@block_merge x383 9 0 458 36 (@block_merge x383 9 0 422 36 (@block_merge x383 9 0 386 36 (@block_merge x383 9 0 350 36 (@block_merge x383 9 0 314 36 (@block_merge x383 9 0 278 36 (@block_merge x383 9 0 242 36 (@block_merge x383 9 0 206 36 (@block_merge x383 9 0 188 18 (@block_merge x383 9 0 152 36 (@block_merge x383 9 0 116 36 (@block_merge x383 9 0 80 36 (@block_merge x383 9 0 44 36 (@block_merge x383 9 0 8 36 sx383_9_0 sx383_9_8) sx383_9_44) sx383_9_80) sx383_9_116) sx383_9_152) sx383_9_188) sx383_9_206) sx383_9_242) sx383_9_278) sx383_9_314) sx383_9_350) sx383_9_386) sx383_9_422) sx383_9_458) sx383_9_494) sx383_9_530)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_0 : block x383 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_3 : block x383 8 3 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_39 : block x383 8 39 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_50 : block x383 8 50 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_86 : block x383 8 86 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_122 : block x383 8 122 23=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_8 : block x383 8 0 145=true := (@block_merge x383 8 0 122 23 (@block_merge x383 8 0 86 36 (@block_merge x383 8 0 50 36 (@block_merge x383 8 0 39 11 (@block_merge x383 8 0 3 36 sx383_8_0 sx383_8_3) sx383_8_39) sx383_8_50) sx383_8_86) sx383_8_122)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_7_0 : block x383 7 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_7_5 : block x383 7 5 27=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_7 : block x383 7 0 32=true := (@block_merge x383 7 0 5 27 sx383_7_0 sx383_7_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_6_0 : block x383 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_6_1 : block x383 6 1 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_6 : block x383 6 0 4=true := (@block_merge x383 6 0 1 3 sx383_6_0 sx383_6_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_5_0 : block x383 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_5 : block x383 5 0 1=true := sx383_5_0
theorem tablesx383 : checkedTables x383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x383 0 0 0 = true)
  · exact (rfl : block x383 1 0 0 = true)
  · exact (rfl : block x383 2 0 0 = true)
  · exact (rfl : block x383 3 0 0 = true)
  · exact (rfl : block x383 4 0 0 = true)
  · exact allx383_5
  · exact allx383_6
  · exact allx383_7
  · exact allx383_8
  · exact allx383_9
  · exact allx383_10
  · exact allx383_11
  · exact allx383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx383 : Lower false (varsX 1919) (graphGoal 1919) 13 :=
  strong_low (m:=1919) (cap:=12) (l:=[(0,10),(1,1),(2,2),(3,5),(4,1),(5,1),(6,2),(8,8)]) (by decide +kernel) (plainA (q:=383) (prior:=boundsBefore knownx367) (before_sound knownx367 validx367) (by decide +kernel))
    (index_root (g:=x383) (i:=0) rfl rfl (before_sound knownx367 validx367) geomx383 tablesx383 (by decide +kernel))
def knownx383 := extendKnown knownx367 13 [(1919,[]),(1983,[118,130,81])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx383 : Known false knownx383 := extendKnown_ok (m:=1919) validx367 lowx383 (by decide +kernel)
def x495d12 (i : Nat) : Nat := 0x406080802ffd30
def x495l12 : Packing := (1,1,6,0,0,0,0,x495d12)
def x495h12 (i : Nat) : Nat := 0x1c0fc9e0950441800000000003d3000030ae3140001100000000012a000c8b12f43811039050650c5c83a7644804d0000a28800000000012c00001980041200061000
def x495d11 (i : Nat) : Nat := 0x241c002202120a0e041540c12100f090502002014a090807058000848183820f5874183068296002830149010216140a50908070500848382810650040c1c1061424201e120a0e041500903060a4875c85ad3e464ec25c6a09400ffd714c3ff60530ffd414c3ff10530ffc214c3ff1c530ffd214c3fe48130bfd814c2ff20530
def x495l11 : Packing := (10,2,6,0,0,10,0,x495d11)
def x495h11 (i : Nat) : Nat := 0xc1a501962a489e8228000000584400000000000001c57c21e6310b462a2e1bec170000c08000089b8000000000160300012070000000000000000000000001428a0320000001e6d800000000006c6c06b60e602468479b32e12851cee086c620204aeeab236e1e0067255f041429e166830c982c14e1790aeb047023f00be0a209484f52b0e8ef09681d6005e15125b62b59a9470d0ab616108900fe09c85529946ee8bb7a2bca5ec0d481fa2633450830b0fc2d804d052a8b14cdf0b4a09c042c23409ae5c589381e906e85bf28369ef0566df036a8039901a0f68c740bb8baa05b8616e3f813291fb8a0aa411a06b388722e13a6c1f0000e8840bdce0503ae19613aa2f800101d800020af19262cb85a461f822cac8001a0c19c10e47036ad6000081cc92f8068000612000000012704a49a98a95d15a0007803e018001c0400000000242a2120638303315e0b00018003badcab88a421f800021380000003014ad71a3c856200808b80002285082e643890ca1d0704577a0b2178000a638000000000000026000000f8c000060000184060010000100800214000100400002000874230100021c00000080800c002000000a82000000400000000000000000408200000010600188060000500002030a002050000201000400000000010000000000000000002000018082020018000000000000000000400204000030000000000000002001000200080000010000001870000000000008000000000000000
def x495d10 (i : Nat) : Nat := (if i<1 then 0xc10058683c0019304014204000220f20181e204817060007940c0f121f041b0be102219c0801219c183c11810c61037824a0c0a0f0c902e07078688120ca202e0ec1604221507ab06830005f040f36080a060790260a160b0600079306000303c800028340c40303c4050883c6830883c6830305c6050883c782c0a002c40b8380b83c0a0c01820c029488c18002e10079812000303c80b0a838783002501e40982840605090611078c12080de0b021908029007040181e0c02981a0a028c0f810603c160a029c0e090ce0431820883d01e0782c14052e1304000d864200a3a001e0c02900e17c102433810883d181028010183c10601e8038243000c08380a7038641017c1604220f40201e0a029208044180f0400c08441e9c003c1805201c1200c1017021005200017c0e0f0406079f000f06014807046040c000b814e0804834140528670200c105c220f38241012006041c05383c0800c08380a6916c8123b71bb8c945ee2a5120877431613907382540aa014fe17e0bea9f02f6a7a9bc61df0ed8757ba19ccce347013789b4ed7e69d3445964c5c61530297b0baf5c32d9969eb2f5832b99556a94535a951444a0b4daa57d26c90d45721cd0948334051f84f707a13c09d84e8272137c1a64cbc63530a97b0baa5be2cf1544a2c4f625911948663ef1e30de46582e814d89c84381f30d305882720f506181fc076000ffeb9282987ff509714c3ffb24a0a61ffd421c530ffeba042987ff5d1214c3ffae290a61ffd925c530ffeb8a82987ff661714c3ffa8290a61ffd7210530ffeca242987ff5d1814c3ff924b8a61ffd4260530ffeb8b02985ff660414c37fb30a0a617fd9460530dfecc242986ff661714c37fb0ec0a61bfd8148530dfe4c282986ff605414c37fb0810a61bfd7420530ffcb82e2986ff609814c37fae440a61fdd9350530dfea1102985ff648714c37fa84c0a61ff9205c530ffc4ba40987f750d814c2ffb2810a61ff92010530ffcca240986ff65d814c37f93090a61bfc8210530dfec1082986ff611814c37fae2c0a61bfd9460530ffcb8302985ff649814c3ff122902617fd981c530bfeca242987fd5c5414c3fba62a0a61bfc7420530dfec2242987fe481414c37f928c0a61bfc9760530ffc4a240987fe645204c2ffb2420a617fd9808530dfec10e2987fe480714c3ff24090a617fd9760530dfe4c2e2987fe5c1214c37fb04a0a61ff92060530dfe410e2987fe65d204c37f924c0a61bfd9260530ffcb8042984ff661414c27fb3010a617dd93105309fecc0e2984ff65d814c2dfb2c38a617dd9350530bfcc8042986fe481814c3bf2e0b8a613fd97205309fecc242985fe640714c3fb2869026177d9508530deea1b02987fa481214c2f7b2810a613fd92205309fecc082987f64c5204c27fb2840a61bf97020530 else 0x15004003c90240c01004c2065000f2200360f182a008007920006101600060c90318202a00325802001e050c940a0f4004480f8001832480029000f206502800b901406078c0a16088c14090303c80f00044606078911840786481005080c191609020507860326028441e30001832302e0b060f2220000f0c900a10050e0817c0c141c50282800140c140a06078c310407c14001736100a0f0c903704442060a050b9f0200030448090d867041d0b818238107a8300f036050619c10442e904e0b060605140a10050c3600028241e5418140c0f260c220c07900a10050c2a0610702a0e1c140a0607900a10050)
def x495l10 : Packing := (100,3,6,0,0,13,0,x495d10)
def x495h10 (i : Nat) : Nat := 0x8014c2d587e562c008400050878237c1ee8048000b07d222ec40800000000001022007f10abe9488199036d321ecc0c12f993c12e21e88373078c044e1f71a1e95b40ef298f94719483080a12309c0000a027c180d45d0510001ea27089901700000001008f041c0b7e8f093c594be4c000000000000e50400000006807a4540001583383a8047c0ac44b383730d6407583a4093261600000006a270001a0bc00000000001018713de24b3656e1cd032688a000149d00280a380001ca230138b40e6102042442b98d4018ce20000382c409f82521c9406d90380001005880800c600000004815b0bc00000000000540e0000000504e22ec0e2e02b2875970aa01ac9428351062c0a4c1ff049f6d7e06bd48e81e663a459180b616eb01cc5bec4c00000000a10c000194ef0bb01a30026b35464000030aff06790846231505e80f6124c14a814605876e224f7032c862b133ace8903416dc078665c4c0410050d4a1bc084cb11f106e00ac0a3082844dc897816b07640d2e0b8800888654de85cd444ea2e0000460cc06e0592098edcf425d834b0bea23a9973838a08dc07f8b3a84766ae424119f80000000a211826d012e2a40000886804a8100e5f80000000241900e60975091b11081e4000000000000000446aa4cb0ae81c344d681990e5099243342040001cdd300c502a270cc1c5836036400010a104120000768c00000000000642005510af0000c07b809a8836a3104e6e1175330000c06080c8000715000000000000488f000000039897853e6caa17180579161036000000049889077200e810714a42e42151ca28000e0f8000384a99000002c007cb012c281003a1c8803a009880641900a421a007001211000c0800808001020038314140861c00106382000f063028d0604082023009d04043000628c0002242000a50001
def x495d9 (i : Nat) : Nat := (if i<1 then 0x82c613608e83e81c20b404d82300aa000cff5d198085309ff2a5425c530bfe69c9148130cff50997605309ff6a57210530ff65c543481309ff6a57250530ffa5089748130efd504985c530dfe6417408530f7d5c57250530cff6497420530efe609705c530ff65d13148130f7e5c17148530efe61d2048530ffc5c52050530fed505425c530ffa481425c530bfe69c9448130ef750d7160530dfb649421c530efe5c09848530dfe65d2010530ddf6557408530bfe6909748130aff68898505309ff6a57408530cff5d19848530efb5089260530aff6a0925c530def6517408530cff6517220530ffc5c49148130efd5c58250530cff2a19448530efe5c14220530ffa4817148530ff650d2048530cff65d8250530dfb6497210530cff261925c530cff65d42205309ff6a54148530ff64c5705c530cff65d8210530cff509981c530dfe509901c530def69d9408530dbf509961c530aff6909260530dfe65d2050530ef750d8148530ef721d3150530ffa4817448530aff6909848530f7e5c0925c5309ff6a5421c530cff2619448530cff2619250530efd5c49850530aff69c9460530bfe680925c530efe5d12060530cff1d19220530aff6909760530ff62a54348130aff688985c530cfe64184085308ff6a58460530cdf21195085308ff6899720530ef54c584485308ff6a58760530cf764c8210530cdf6119508530cef21194085308ff6a47420530cfe5c19808530ff44c57048530cf764d8210530bee6909148130cfe21190085309fe2a52050530cef21d9408530df648193105308ff2a58448530cfe21d9008530cef6517420530c7f5c99720530cbf658821c530cbf659821c5308ff6a4821c530fea5092050530ff44c52048530bf668c9148130e7e5c0985c5308ff6a582605308ff6899850530cef6514220530cfe641821c530df664d201c530efa48181485308ff6a54220530dee6517008530cdf61d9508530cfe481981c530afe6809260530df64819350530b7e69c9148130bde6949148130cf764d821c530cef61d94085308ff2a58250530cfe48198105308ff69198085309fe6a57008530dbe6597008530cef6a19408530cfb649821c530de768d9408530cfe65170205308ff689981c530cfe6497020530bf668c9448130cfe48197605308ff2a54260530efa5092060530dfa649201c530cef6119408530cbf6a1961c530bbe6989148130df55c593505309fe6a5201c530cef2a194085308ff6899810530dbe659201c530ef650d2060530d7e65d7008530bde6949448130dde6557008530dfa6492050530df664d7008530ff45c531481308ff6919720530e7e5c17420530cdf21d9508530cf764d8408530ff44c5705c530cfb6497220530ee750943605308ff6a48210530dfa6492010530ff04853148130fe25094348130 else 0x60280f1800078b8303c40540a0e81e403c00100a0c022303c1310140788184204052004001e40280f102e0308110584000419400403041903c40504100f060001e3014111014078814181e202a8003c60504a20640610140001e30180f101407880f0581118154001e34000e05c7c1814080c0f082fc0f06303c21100a0c881720c05180c08080f083209880ea0417180007881601440301e20280603c60d81e20298003c605300078c0602854180a030c050000f1800078880083203080a03c405000078c1f08008281e30140f100c078806040191c1203014303c17100c05081d0f040b03230141103c60281428140503c0620001382e303c11104c0788830540e180a050a050140f01880b82c0381e40240f13064182230280503c7c181e28140503c0620300001e360e0506c0621060788150384c18150280c40002210000c0a830540e180c07880e4140a182e0788170284c1814078f8205818180c07882402840f04420140f101e10280f1018028443a0c0f103207880903c40301e20000f0287c181e2e0c0f100a05081903c40c7040500007940903c40281420000f150607880502840001420140a10460784430180f10000784202902003c40481e20601307460482e078c0f08000881e303c11170607880a06440001e28140503c06200c078a8303c40480a0501e4a0c0f1706080a8303c40002e078c8303c40503220000e060682200080d83e0605018802814220c1804460002e20740903c0a202a07080f0c01c10140c81e5e0a8380304e049b0440f446522f716289ac4721f30e0863c2ba103068827c0da04f00e7ffbf99faefc87d2be31ee6f6e7aabcc9e32f0076ebb11d56e88732b909c3ee106f6b751b76d986bfb5c1aaed3468db4099d2cc6656b2298cec4e615b0217debe05e3aeb9716b7c5acad0164eb04570ab2155eaa053ea969482a144f8a76137e99c4c1a559252910476a329162884430a0d10368023ea9ef0f467803b39d10e567123779b30d6669a34099a0cb264030e9810bd65d22dc9658afa5642a594c89f64e226492c092e47e23291308524101f18f2876238e1b58d706723201838bb85aa2a814789d849223010b87f83b61c20d4861)
def x495l9 : Packing := (155,4,6,0,0,13,0,x495d9)
def x495h9 (i : Nat) : Nat := 0x16ce000c1c60f86c00184bc16001c0142c812000422828819610001408000426603620a0c000ac000000001b031e25e68001ac4005e1422b4472da24461fe57e06001c2e60acdc46be84016494001020c2
def x495d8 (i : Nat) : Nat := 0x500f101d08000f0603c403c280020f06040400400080a01e2f04064078c0781110000000a01e2f040600c8c0c840d840481d01e3c5deeed71b654683319644619077bb716c9b4b2451887361186c26007da5425c57250530beb36a54a86902614ef6dc84650214c29fcdb908c804298537db72119508530df62e2d2122902618fd5c4a9609414c3fe0ba24298a409853bdb72a19408530dee2e2d292290261cfa5c1925c8814c29fcda10ec8042987f89422a54348130ff42e2a1240a0a61a7e5c1a2261714c3fc4a12e2a1a409871f9706497420530a6fb6843b2a10a619fc5c4a9481414c3ee8ba262b8242987fc1425c53148130f3a262b8130b8a61d745c17164d414c38dcba328b8102987b89205094360530
def x495l8 : Packing := (25,5,6,0,0,9,0,x495d8)
def x495h8 (i : Nat) : Nat := 0x60
def x495d7 (i : Nat) : Nat := 0x37c26d5422a54348130
def x495l7 : Packing := (1,6,6,0,0,0,0,x495d7)
def x495samples : Array (Bits × Bits) := #[(0x790d706ea505afe9b0c724c9782cc1afc646cf5984b37bd127e6ba8f8b80875cf95dbb9c6ee35addedb9ba69b7fb95dd52a44f31bfb9a14e7b9dda437d612de436b4200b240000204d9000006e988c662c6109193894c84116cc36792839f673,0x13a841058412b50602106a612442c00d1700b348a09a68ca9b454abc0c149e2d0ba412b11180392072ac703b0642008c01de10a9941614451e539805d20ba6851838da5cc29300cdc773214762988c642c6109192894c84114c8245928112652),(0xbca3c9a2dacf584a5d67896a2af91be58c7aaf9a94913c7e2793f7d823ec38511dbdc3d1b7253577720cf20cb9721f78dd42c0a2b66bfef0fd15a9fc83bcadb4a8131286058212c000801746e21308600843061f0070f86270cc981ff26487f,0x40000810080140a0208a008c00800a9000040ca04041042120208002f1284150000204000a10400400000940401880010c0005000a20a8880088406028205140000724213828c520388c5ea00121308200843060900205862304810085244829),(0xa56fbd1c4a772884d845ed735ddf34a87a5ab37973cf8cce9456977c7ff53ad3e0ab8dd347f75886aa37365612d8d6bdd1fb7fd35116d7d46570a5652bbc46e9a7f419e401810580000745f4910000f88f01c181c118f00839f30e1e31c78f9c,0x20a0004412a20000480020015800000801c202000018085c0a0a2240004080294480220144009c01c860042200403290a20040800101400512421090801220185600db56011228168151a004560000508f01c1814100a00800a20e1430838514),(0xe3ca83d2beb67eb03a88694cc5df16115cdf31615e0b467f27be91f9f245758ec96374ff68c021a3ccee5f1329d38e4a7b3c2e588ea95f2845d6b4a4e7d4188692f44084132102429007440000c03f01300601fe0e1f01f03e03f01fc1f80fe0,0xa44c5834d108470019bd932034d47c21e148028dce273230164883e130149968200c54623222078211221182820042b09d01a734c12b1506c05270426c442c4804704a1f64d96a170a04e78a9c02a01300600540e1f01f03e01f00bc1780ae0),(0,0),(0x5cccd577a7616bebd77886df0ac45a6b93726f86ae73c88aabefcefb82befdacf58faed3b40ea7a31e8ba789b0f2f0ae52b67dbd3a5b827abc0ebfd79adfb52c3dbe04138c06c8016fd0a0090001c001c007fe000fe001ffc003ffe001fff000,0x2006306049c00041c90200904a002092687a0025042011044002800042ca2142400001000c2c00480502098001204c21a201a010492163880000440800404840e28005a3054cba3210008c189d000001c006a4000540012c8003dba001eed000),(0x8ed6473950be5929e46bb4c0b2120bb79bcf0857b17f7e4e528cbff6becf0260ef2d50a38dde412aeea3f84afe2613f88ea5fe970dccdeabec4f02d913deba947b4d82004058301c00281a0200fe0001fff800000ffffe000003fffffe000000,0x208164a611529c0516408910050d404ca061c00d0580699499420aa80241208610818834a4cf901a0c1520b22261370080d1c053440b0643ad07828c010c0a1722e88986c7573a93c030a05cbed40001fa5000000ffdfa0000037eff7a000000),(0x6fa947b752475253b3adc727431128c62573279f5cc473a0e2d1c6b4e566145d051e890bab09aebd9c5eaf7cee6eec57cce6f0d7f1d35ddc9aa75d2ed8b523115ff20c40888004800240a08891fffffe000000000ffffffffffc000000000000,0x1e48840b8005d2a806704f6a257296240204f0d8b88740018111180810115694190adc4492932206329c001c8c16810e44d41f67200080624538216122a9120008172008faa145c96eae53e320ffffae000000000abf5ed37f5c000000000000),(0xf978eff1b46327f0f91fb1a61f25f6bd8d4ae6a24897a6701e6c8f12f952dc727aa9ccb5d187bcce73703fb96f4bdf713c17e9b8c7b5883d0a2a3b5785041ee792acc2101226da53b0201a0300fffffffffffffff00000000000000000000000,0x55100808800903880000224520309800000038402005844026004501281406090c5c0008401006000048c000d41a00d0440801808204082412380852083280081010725808a0414c0f4f1183402bd5fe05a95babf00000000000000000000000)]
def x495columns : List ColumnInfo := [(521,0,486,0,8),(128,0,1903,0,11),(64,0,1967,0,11),(520,0,487,0,11),(513,0,494,0,11),(579,0,428,0,7),(527,0,480,0,4),(545,0,462,0,8),(256,0,1775,0,9),(524,0,483,0,8),(900,8,99,0,4),(776,0,231,0,8),(652,0,355,0,7),(673,0,334,0,7),(809,0,198,0,4),(674,1,332,0,4),(610,1,396,0,4),(836,8,163,0,4),(513,32,78,384,6),(587,0,420,0,4),(840,0,167,0,7),(198,0,1833,0,4),(778,64,165,0,4),(650,4,353,0,4),(616,256,135,0,4),(581,2,424,0,4),(841,0,166,0,4),(384,32,78,1,5),(522,0,485,0,7),(684,0,323,0,4),(130,0,1901,0,7),(681,0,326,0,4),(517,0,490,0,7),(769,32,78,128,5),(897,32,78,0,4),(769,0,238,0,7),(192,0,1839,0,8),(677,0,330,0,4),(68,0,1963,0,7),(737,0,270,0,4)]
def x495autos : List (List Nat) := [[],[81,130,118],[48,33,133,118],[48,129,82],[96,115,133],[96,129,82,115,33,48],[112,33,99],[112,81,130,99,33,48]]
def x495levels : Nat → Packing
  | 12 => x495l12
  | 11 => x495l11
  | 10 => x495l10
  | 9 => x495l9
  | 8 => x495l8
  | 7 => x495l7
  | _ => emptyPacking
def x495index : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 14 43 4 11 4 3 x495h12
  | 11 => lookupWord 177 223 7 14 7 3 x495h11
  | 10 => lookupWord 85 319 7 15 8 3 x495h10
  | 9 => lookupWord 19 49 3 12 5 3 x495h9
  | 8 => lookupWord 1 3 1 8 1 3 x495h8
  | _ => fun _ => none
def x495 : Forest := ⟨2031,12,fun j => x495samples[j]?.getD (0,0),x495columns,x495autos,x495levels,x495index⟩
set_option maxHeartbeats 0 in
theorem geomx495 : graphValid x495 (boundsBefore knownx383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_12_0 : block x495 12 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx495_12 : block x495 12 0 1=true := sx495_12_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_11_0 : block x495 11 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_11_3 : block x495 11 3 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx495_11 : block x495 11 0 10=true := (@block_merge x495 11 0 3 7 sx495_11_0 sx495_11_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_10_0 : block x495 10 0 23=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_10_23 : block x495 10 23 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_10_59 : block x495 10 59 24=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_10_83 : block x495 10 83 17=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx495_10 : block x495 10 0 100=true := (@block_merge x495 10 0 83 17 (@block_merge x495 10 0 59 24 (@block_merge x495 10 0 23 36 sx495_10_0 sx495_10_23) sx495_10_59) sx495_10_83)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_9_0 : block x495 9 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_9_2 : block x495 9 2 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_9_38 : block x495 9 38 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_9_74 : block x495 9 74 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_9_87 : block x495 9 87 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_9_123 : block x495 9 123 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx495_9 : block x495 9 0 155=true := (@block_merge x495 9 0 123 32 (@block_merge x495 9 0 87 36 (@block_merge x495 9 0 74 13 (@block_merge x495 9 0 38 36 (@block_merge x495 9 0 2 36 sx495_9_0 sx495_9_2) sx495_9_38) sx495_9_74) sx495_9_87) sx495_9_123)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_8_0 : block x495 8 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_8_4 : block x495 8 4 21=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx495_8 : block x495 8 0 25=true := (@block_merge x495 8 0 4 21 sx495_8_0 sx495_8_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_7_0 : block x495 7 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx495_7 : block x495 7 0 1=true := sx495_7_0
theorem tablesx495 : checkedTables x495 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x495 0 0 0 = true)
  · exact (rfl : block x495 1 0 0 = true)
  · exact (rfl : block x495 2 0 0 = true)
  · exact (rfl : block x495 3 0 0 = true)
  · exact (rfl : block x495 4 0 0 = true)
  · exact (rfl : block x495 5 0 0 = true)
  · exact (rfl : block x495 6 0 0 = true)
  · exact allx495_7
  · exact allx495_8
  · exact allx495_9
  · exact allx495_10
  · exact allx495_11
  · exact allx495_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx495 : Lower false (varsX 2031) (graphGoal 2031) 13 :=
  strong_low (m:=2031) (cap:=12) (l:=[(0,10),(1,1),(2,2),(3,5),(5,1),(6,2),(7,4),(8,8)]) (by decide +kernel) (plainA (q:=495) (prior:=boundsBefore knownx383) (before_sound knownx383 validx383) (by decide +kernel))
    (index_root (g:=x495) (i:=0) rfl rfl (before_sound knownx383 validx383) geomx495 tablesx495 (by decide +kernel))
def knownx495 := extendKnown knownx383 13 [(2031,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx495 : Known false knownx495 := extendKnown_ok (m:=2031) validx383 lowx495 (by decide +kernel)
def xmd14 (i : Nat) : Nat := 0x100e0c0a08060402009ffd30
def xml14 : Packing := (1,1,7,0,0,0,0,xmd14)
def xmh14 (i : Nat) : Nat := 0xe64a1800070b872000000b1321b162b06000e00a12119d10000f70000000a09360000961271d02617a04166e73c05965767077a07914b63c11b08b7490a503a1a000000001f853803a5000
def xmd13 (i : Nat) : Nat := 0x220982a160e8781a1a088880c0a00d82c1e088880404208a403c130542c21110481a190f0280c01b058441207004521cf06434150b084421c0e098140418c04812108883a1e07044321605018036110781c12008e451d108742a1a0102808351084441d0e0682a1413020640416c02402028a0494060781a1e0501801c0a0803c0e088681406009f1377bf6b9921ce6293d3309a15800ffec0a61ffc814c3ffa42987ff08530ffe90261ffd514c3ff8a2987ff64530ffe88261ffc914c3ff240985ff64530
def xml13 : Packing := (12,2,7,0,0,10,0,xmd13)
def xmh13 (i : Nat) : Nat := (if i<1 then 0x4827500f80001854691018b56301000b800000000000000018e2b8ccc024000060168000000000000000680e305bfb51c81320331094c3cb21438baddb13c308b0a66bbb804c2050a025284260428823c82c00000000705a000000004040783be0a900000000000000002d4b0816681ca835800000007848000000007825d038800000000000000000004006000000006802000020df8000093280548000000019d130cdc3df685200004047000038cef045e02d984f2851933f40308330483c49534034f00f000000004881800030db18ca80000000283f80005858f90180000000000003bc90150000181700000000000000002862f3900018800023823b2a00001b5b00002519800018187d14130d0d53631900006b3ea4102057800053acb919d0112855fa8e800000007859e80280002b00800068bf3341eb330000000038050844585d6853000348de7014d840d81b403ab0371309e032000050938000000018357817c839f81183a35395e3a508d300007060f82b4047983dc05ed32bb0b20049d399e8d59b5bf14b2d3c8000201ddb248b501829181d1b9deb92c13c9b5c8006884fb00c4028105cc8c0c8c7000008074048f01080c1c355800078d8f33ff84ad0212810702c983e883430d9c83b4813d10ed8d65804602e3000ebd1b021d0d2d098033888b872d3000040b4c15c783008dcc84a3b150000303a2099fb977b5153d8a05fcbdc68563b4c8014683e30233801881a2837b51068b16029b809e033a3b7d85c411400003028f84198624309385af00d901290202844e31400b98846b031d008d321702f80006b1f80005b3a20df301aa003c38f1001000078123832a8ada3d328d4e323684bd85160434804a0002849485e0344531f6d0ee81fb853e826401c7314dd5c331b80c5402a502090d1084b404e208d3b387b36682be00ee85dd019385753072856d82eeb1b4096538eeb560861f03c9bc2a015d89a9845035d501beb4b400b00279ba7782d0b4098097bc2082483a6981e45d15bc5404dd036d08e90313861004cb03f6838280a133a9808703d18079b491043e022409a5050584d105f704eb3b0c00ad354b8597b4afbdd682f6c5c034c000000005b44a8db909933159b3e5b2028607b25581ecbc4888dc3942baf801f300d605280c390268bbc202280367ba2603948058855482acb1ce85b3819b80c820000006041010218000091804100022400400267000017280000c00f16140110008000323420000ec0830000285000c4850000000260460200140050230181062c28e0004004080c1050000080043402708344830a001800c0400028003820200281021030500081000200009080011a00040802c0018004040800e100010000000021800002004810200100000c000002000c0200082020c6840a08000 else 0x68d388b8f33b00000000000000005046000000000000000000004c140000000000006041385800000)
def xmd12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x3ffd8254530fff6a1104c3ffda148130fff645514c3ffd5020530fff681514c3ffd9544130fff649914c3ffd8244130fff4c8514c3ffd2060530fff654214c3ffc5224530fff481914c3ffd8548530fff614214c3ffc8508530fff614914c3ffda960530fff4c9104c3ffca954530fff285204c3ffc9214530fff545214c3ffca264530fff4c5514c3ffda864530fff481514c3ffd5060530fff689514c3ffca564530fff648814c3ffd5224530fff655914c3ffd1048530fff661914c3ffd3148130fff601914c3ffd5348130fff289514c3ffda564530fff600214c3ffd3164530fff6a5214c3ffd9260530fff648514c3ffda548130fff6a1204c3ffd3144130fff148814c3ffca960530fff2a5214c3ffd5144130fff208514c3ffda954530fff2a1914c3ffc8524530fff608914c3ffd9244130fff601814c3ffca548130fff441814c3ffd9844130fff601214c3ffda544130fff540214c3ffd9144130fff645214c3ffd9548530fff681214c3ffda548530fff60d104c3ffca848130fff681814c3ffd5344130fff480814c3ffd8214530fff481214c3ffca548530fff480514c3ffda264530fff541214c3ffd9254530fff54d914c3ffda244130dff6a5514c37fd3164530ffe481104c37fd5164530dff541914c3ff99148130ffe281514c37fd2164530dff6a5814c3ff98044130dff2a5514c37fd9524530ff754c914c37fd3264530dff60d914c2ffda014530dff689914c37fda948530dff615914c3ff9a148130ffe661204c2ffda948530ffe4c9204c2ffda824530bff6a4214c3fed2048530dff649914c2ffda214530ffe295204c3fdda354530dff289914c3ff92020530bff688814c37fd8064530bff68c514c37fd9220530bff68d514c2ffda954530bff688914c37fd8264530dff655914c3ff98348130bff695104c37fd9224530dff695914c2ffda344130bff680214c2ffda048530ffe601204c37fda864530dff54d914c3ff9a548130ffe4c5204c3ff8a848130ffe649204c2ffda508530ffe600914c3ff95148130bff681814c3ff98008530dff661914c3ff92014530ffe2a5204c2ffda020530dff295914c3ff99548130ffe609204c3ff92048530dff648514c37fd9260530ffe601214c2ffda914530ffe54d204c3ff8a148130ffe480914c3ff9a848130bff6a4814c3ff92060530bff694914c37fd9824530ffe601814c37fca864530ffd545104c37fd9508530dff441914c37fd20645309ff6a5814c27fda9085309ff695914c2fdda314530bfe680214c2f7da508530bbf698214c2fbda420530ff64c5204c27fda944130b7f69c814c27fca9605309ff6a5214c3fd953481309ff6a4514c2fbda4085309ff2a5214c37f920645309ff6a4814c2ff9a020530efe601814c3fe92048530bf768d514c27fca954530 else 0x8881d87614054ab0203701055ac33118150f03a0780e000f824a051856208702702c052a07c1550200210f03e0180846d102a9c09856218a0552a21c12460882e10446060c0138011443824b01203c001ac0419a28094406c460604c0f43e0580602092809c1485a230721c114270243301049981a068450f80032135148026856168761c8622302c070009812603e81a0f8051c1183345201005300c081221c093e0b83828446020d01670ac2404b00c0814638ec3406c40138110f80e0013024a6180440d8502702c00870541f500942d1004e05800464383e907d08c028e08c19a28f42a0b4360808e074430f80e01812d030268542286c0d88a1f01c0b005a124410f8011c4504c0921866208702585c0b014a815483e0240e43e03800321431490480480c14c068a07c09430d81b0b43e0503a0780b458003e09310921487c0488c008a098124a0604d0a83d0d81d10c3e0381600bc00882148706b01228094408c2b0e0d6020cd1404a004a168702491c030128821484a1260180846d102a7c230782418c0b01830124608845158002a0950e70520881c18c050305c0b42064340ac2c10c402803e058082e86024d0af04a1b03a2301c0b00404981e004501643980801f04a1b0361702c07004e098011c451305c2303c008a02c8738578460780114438167c1708c0f002288702cf809104501a40100361a87c0b01c00e040570211580a54059f030ac1621b002880b3e0208812309304c0e86a1f02c0700400801b0b43e0580e00702007c0f002288e02ce4510e068c09078403d0d81b0f81603801c2bc0c86c03012880b3816446018082045180402286c0f01c0b00380803d0d81e0580e00701304a1a85c0b01c00e0200c02e0580838049e0ffc182824702c2037c0427fc6fe89fb0bf167dbef989f15bda47adaf4b1e7abcaa78bef0a1df3bb747652ebc9d58ba7a73d2e6c9ca4b91c718ee101bd7b7786e82dbd9b5fb67e6c8ed819ae2b5526a0ed391a4cb476687ecee19c0b322659aca81934b232641ec6e98c6b12e61dac2b1830b02a5f46bd89781aec25c9eb8616e6adaa5ad2b3b165aac245776ae1158daaa854cea7f94e3a99a52c6a501461a86e506ea0293d0a72e4d2698592cca51249b691a11ffa382466e8b89155a238437685e908da0b2407e7f30fb19efa3d727990f079dba3a7a73a0e499c3e37d26e28d909aa434626770caa98ec312e6090bd397482daa59d8b0b95b82aee5410a34940a27064c68958925223fa462889a90cc209e3fe87be8f281dba3a487238dde1aea34586658c5817ca2e405988ad214fa28004d0892e11b2221041287da0f0a1ce8372865e0c1217202b4853c09e2129822d842e07c60e601a6832a05aa0a2811f821c040606e00b6812c01c202580258000fff548814c3ffda354530fff549814c) else (if i<3 then 0x8280ce05803700a380b050122c13843114381243c0f06024982588420190260783012410d808160a130021c18098122e058060248a125c009e05070210c04e1183e02058248c00872bc14205c0b82b80200c430e0c824921b0162300050153409803100685a091a046170007f01a2a09390d800120a02450450961707a1d8702c2104809c04a2431b800284381a138246a1c170482c219040270102d243600c384c04824602705614124250806813c0b014317846018383009140dc228702e070601238160a0243c010002702c0414350c04b0ac450e0a8280d6058082580330003f01c0814281f8220981e10c430a0ba121483f8160380380b0681440f01098198330202558010e13b440a158561c1208509c041704702431405b100d0280a82481c1980e0404af0141c0d02c14048c818420a824102120fd1d80514a43009c0887050b8030a4f0284a150707414048b800280a8c1b027086201240d0506b0204f0143180ae0080310c38120c8248c001623809054b80028098244c13034210704b01c0b000cc17540ac2c10c440ec3829809148602ab21a03c1685c228841c0921c13c080cc0423049f81c10c440ec381202e02456000902ec21a086220761c184301dc0b01034126028c3406c2b114381243e0580e0013024d42702c050c048b02b0b043100480f80e00450460baf04c0d05a2107c0700c082105d501d0ac450e84018440178160206824c42504c0b01c0029060f02024c430e0d6034501288101ac068a024b02b0b043100580f81255808460aad108158581d87a192a04302c040d05598460e0d0284701666158861c17c0b01c001905538260682a100be01816021183ea81d8709304c0e8661588c0b01c0160a30ac440e81e05808278003e092e036198502487c0b01c002604954310a8491143e0580e0013024a0530221c1f05432310b80110438358091404a085424880570022887049182e1009e040a602860248a1585a21880508621f02c07000981266104402604e004511c0a20870101281f00c08146391822098160218e000b82480942b05f02057000c18742060fe034420f80032135149c148504c0905088c030122815510d02b0b03b0ec4218046058081a09301a053082230721d2a2280b23815583f80d1017e000c84d452206a1605c2088c1c8702509c0b014a8156d0c84d0a4410f81603800320aa885c008821c14c048a02518240ac2e060484b43605806020aac09a2188a1d8721885c0b01c00190558c330a43a20956058081a0aa409c2088c1c8782418c0a0cc04125c080930ac402980d140f81296158861c17c0b01c001905520910b8011043e021311404a705c21090488702cd8290b84110098138160180846092e8661a856158842088a1e0721c0cc0b01034127b0ac430e0be03816000c82a9a1886821 else 0x310552b07c1242688c0700a294c430e82024188300aa120be0580a54c4acab8449182509c0b01c013022061582304a120a82581603802d080270761c0b048d800260a024405c15c01006218702419049206a0b808160d0246c23074330106012310cc4600c384c048247c008702414048a05e0b42a1101824048278084d81418cc0107c0a8e050a4360ac28130892281829808320be048637000340b064152c098003406850091b0021c09050122c1e920340a60580e0070552404909a2b00a1cf8010e0884c09160402700c068a068cc2b0e109220b82a0921380e05802c0b40e0c02702c04143e0082602848245c001421c0d09c1232078010e4f034503d04c2288620870a60905c14c0419c008a710d8030e0a02a5c218861c1705418027012292a5205800320a910902708621070650c04900de0f43b0f0882448a060483180e04863429c1104c0d8861d090c41206302c0417c01c4331d800280917000340b098122c09803100fe034541272170002419054a8210c04e02058286c008802426048a81c1804e05808286c0088a1d8702412350cc40340a02a818250660580812b0601521b00c2187048f800320a8c0d42508a1c2702c123a180a02a3c0100c0b01050b4310c04b0b4430e0a9238))
def xml12 : Packing := (198,3,7,0,0,15,0,xmd12)
def xmh12 (i : Nat) : Nat := (if i<3 then (if i<1 then 0xe1f2d850bc1de5c198c04c6c048bb7d9812470916416f50fa68113e8c3d03d106f7e40461157dddad115d4c34f702bc000000001c013d0d37d945d6ca682cf715e640c350bca89b7811e958713053e4b9d50193454057d0b490860b8ec74f60cbe1f5b406d95a11d0555da5cb017bc0f4b7d9bc2630000247d3a0e985f6b0000000000000140e5602100000a7fad47734326ec3dc761c80000212a5c43222e0802c8e0f6e800800002c119016200000b0bb7c6e60000000000000103ebd029c0000000029cb3b07d80000b054608e66067581f2906b38309713d3df7790de7c023f2f1f5adaa0a061e25d0b26db600000182e640f97cbcb00001907190bec0000f033c01a2100139d3700002d5db50f740000000000000d020687e9864aa1be7c039f5e9b30ad38361d0de3c334700e941d57010d435107d1000007190c9acc632a6c16376204000052cc0408ad7d1c00000000000000000386c5a019801230000040b5c3c62817bc65d4c72671a0bc0f8400914394e0cf5410ee0b451f8510c99c3b8000000000571e00000702f006d59699ac38e000000000000000000b63b601010000281473145b839861e9c878496d5c1db650ea9595ab0c16c055116a38214f1cc7182400001819f00003c6a2c065381a500001ddd9f770b83bd20c3802525737a80a240608980af65aa1af39694c000087bd1c4a020f1c0000f6c8a033b1047b87ba06e99df3c107f80000b0edbda8f043304000c000026200a00002f00360f060218089f0d020513040706230a0901410408500c00070000010d310b00000cc60619202266011401350000500302001054003629010129000001270202095600081b7a1d06262303020b970303250005453d000c232b0008000e25003408026004200303062d12001905271604001c441c0d0a49102204190c06071e001600090200702234050814001e03170f03190001011210041518040002084a4f000004750103050303120a01190000000904003c08090900080500065923122501002200020200331e100805010704020400122c317c080c400b0105000a02010b071f270208070806025d00141e05000505000205010200050314081b010800090512060023070103071a4201000c0143120b2008052f09040107300a30100a000002001a83000b01160226214320ae052a00020a080016010c07000100000102021d07200a0c020c08021215040100000e091c0104051f041d00033e00070001052b0b10637301071c1333040004090a0e000005020108040001041d03130d422d0205002b01010a020902030e0207030e011b020800030203010201050100091501010c0306001505000a04002a0c03310f120000100501110b0e06380518000014010001020407330804306d0a180201001a0e0e073c050b0909120200 else (if i<2 then 0xc0000006d4000030c015d050000287b1f61dfc0cb40854000026c380000a789283ad62da40000308191abc00001c11f00000000000001edea58f40000000000000060cb40000000031b2e767fc000050094c086b43ae6e0271ee5185793c440000c043400000000263450000100ab00003c242d018b84bd00000df7b3723104a6400b50146003084090ba42000000000000000000340b1f1365c00540e72c367f0e9700dcc08700000e607c0000000011ca38071c000091e35006f703420202e0adfc0290000381e5000038044b1dc2025a33f60c366f076302a510ab00000f0dba830d00000062ff09600000c1c84d74c111e686ec705a800000000259fc00000412fd7ad40000a68ad9bbeb6f68c49ea024800007018442c630ac1c0e3005818211205b7c1d0e0c548234d6932409eb6886808d057cfcbd4f0dfa43d270e16c154e16ea837b00e9082550000140c7a0d222b7c000011f65421ad830210f400000d1558000056b00c3770000207900b9840000c01d7da77b07b55a2f564688190f10c2e3990000300eab08430632705f747e35023840780000042bbb0a500000205850336c046c830f911e000000000081d690a56191800000000000001c74c862340000b3eb800000000046da302fc000000000c1c965a83822d2136b80e2a0acc0b7f00000433500003834c2765e04e6000039adf207bc0000417bbc764905b39ddf268e00000000024732261372b40000000000827cd192f205a28679906185fc0f0d250bd58032901f467be301b921848000030150477fe647c0000503ddc3c880d8b02a600001c0e6e1296c6a492c3982c0c0a7d035890a6b2f9f8ae750074302cc9bdd803b1876e96926017c766e4000000002c2fa6b4c19ca547e761d8d41a1a000f000018d1341ab7028d9056c0000000012cf0001b0c23991f97c48920ae9839100000000090106c003061600063b0700000011df00000d0f52c2cc707e800004054840d3a07fd03d9200784135306fbc3b4c050a0291b703549ad46a16825b56a6304c9f0eb28706d8e960125e005162c5000008271ca4ec0d4db73a0825680f9a4138000010275e7b6400007ac3c000087c4c000027238000030fbf1e8560dc041da123fac3c050cdf4026000024729002f95a418031b81e4b07e1424070aa344ec86eac00003745e02d9000010303000024095e0d68000000dcc000780c2c8b7960f7e01e9503f0016780ac5df86a60c742d8000030aad969ac00009780f0179e6c69c359101b8c5ec0035718ad00000000027669c184a56b699273045118df112540000bb98d22adf07815f04e005940c0800cd03ae27b3dc51ee208c039261ad9079e0a291935f2a961451d76c53db2d574f4c1f036315c1d770f5995dae0385c1c51017700f3b03e7833e812afc304111f3050ed0c584034 else 0x16bb2c0200000205ad000000000109e9e2d100000000076a7c000066bac0000b1a50576c000000000b0de80000009f0000080aa985e40000007db179ae9b837711101b77052c0000000022da7909dc0000b0a0800000000000002b118abc00000183ab00003ead9a05ae008b90c300000c02eb1b62c0a39d046c63b8822471e0c0000a498c000000002c04b000011a4f00000c70461c2dda4a0000102033072886b1f02640000702d00000b73a949a346b75c09a9046bc0c5f2290000048dfccaa100001ab8686d000000d023c000034b640000304600000e67540000a1e0a8a9d000004132a02218c5d00001c27400002c13d000015cf8000020ee7709b90107000000000d08f40220b02140000e6e1c000000002437632de241dd00000010000002049334ab65ee1c01459aae466fdc7d5c0b4f80ed00f0c814910d404280d05921a1600001439df74b8000011404000001b38000036bd043cc00bd482f970d8d423a6727fc045b7f75c26fcb3d5dbd040b700000778b555caa012b9b5300003c04930b875ec37085cdb3460a800374ebb640000504e48145f7b04c208d66584674000000000b12f3cb1620a3feb4467a72042457ce38b3ad0541829ca666202f000ae000002272887ac60f9e400910a900080e011f8185503071acabafae82adb028cc2f6a0cc20299308ca5856f7b03c0cc17d8ec72361429024eb0475428700001afd8f0c46d900562401df3109cd5c242b955c18c9082b06bf506000000d20c7031000000000021564000022d2e4bd0000012b1511270c7c196d560195000000000b0e300000861e96f96f00640000000015af780f92c22cf05c0873b20e0c00000000080fd614bf04a7da89146f530831814010b898279000022aa1f6e48000017d5c0000d70ca069d10764035ec106e4057102581e91f2226020f76d600000a094d1d9c2061c000060737453200002c357d8b640000a1eb48021d09200000c1abc83c5e0c071fd5d04ed5ae781e2d8199068c580ae30d2f019ec28bb4296f0c689ae96040d5f49017002e8d052900000000000000f073c00000000000009b1d21a1bbbdd608df06010020e11a5b83ed80310184a80c9e017830378000000002c0020000281e7b18a44e2f71c680000000000000000014720000000000a7de8638900002836400003c2686100b69da3069d980e779b0822f47172109b0000202a3f6030421beacdc9ee0f0109c26d03dd5856b0000000000000386de0000280aa80425c2a100b140000000032d4746ed4815700000824f80d74000000000000000003446496eb98601813488780008a6096ce017c00002678b437d569388388f0bdd403f000035b7817f6e83690000000001149ad878a17459255000000000bb8500000880f40000760dedaff9a68c000000003173586b0)) else (if i<4 then 0xf4000000000000011408432b51dbc4082037cec24300bcf84b4000038027707040000608140000600ab42ca10af0db31419300000d00b04b61263ac0000608360112d71585d58f4e7c000007269017742228831920bab02c4e6cfb0ace97e8fc4f6a0e86c241812fc0000a2a500000d033643b301178000076b1c9f1ff01de01b4a63a483b520472808c50ad8000021d700000d0e82ab670000280b907d3b025476909e83210c7342e0b20f41a75000000000000000000e2d6d4a6400432df4fc0a16c13e00003039500002c14170b5541a60000181725177b99c2000011ae8e1e4c00005000503cde08f000006004301281718801ebd09f5c91a00000000096408000000000823e806c3d9e0104e945ea11c6e042d0000387c20143741af85b3b5e476645800009003643cf823ec0000503a25ee2901e5c1a3000028642513f4995b80964000031f364105000024cb400000000006a48000000000000010987ab7f206a60603000000000e02d8000080596038dc007c870d90d38dd79000000000b1fa0815c00001821d1045f097e6169e0006d6f20abd547bdc0000709d80000f62d4000031ce60250c049c00002670d8314e1d55c3e1e0299062ec4b31867a80f4c8153f05899ea1c6f5c0000a7a5282db7036e803d000021b51000018399a668b826b7776c524bb0691416edbc0f586fc1f1a83ba0000000001025c000010e01c771001ca07e400003825e768f3081bf17b70191b2d9c0000b0b0507462065981dbf683d98c266f8f836fc0bbcc7bc31882c24c000029a70e6ef60ac55155d437fa01300000d01f701ee20060000000001418110244c4e4d7efd1e45a60e102d0000010312f01b69c4680324000000003009d60a63190f202b0c4b600000000040c7a1dafc0b69dbcde0e280000f0f040000000030130206ab02abf0e2f004e46f6c0000b0c62eb3530998c2eb0019cc0a9a013c000000002d9e90000141223062da369d3e5842ce0088f195887ab75b5970227845c5742202fdfbbb08e55008e34534669940000c04fc0000f77680000670f140dde6def0098767900000781adc15f50fa80000000d4000081d529b75908af4183a01cc000031b24c663409ee82337016b187f00c85414eb0ea6056e30ad4433c6609d4fa9c9b64003c402878718c0cea98dcc08dc0000b0bf09f6da06e380871079902a936e6c9887f1923801236dcae13b1708143bf4118d072700000000011c90c39e0000281aed10bc5c87612e0000070a30000066cfd1c7f000000000a6d7ae77a000015e23f0fa09eb4a01340000374a800000000069dbc05100000f0f1bc3a300003424db03c8838fa04195a0c000020143b111a5b4d505680000000024355c1b665a61000028ed4000020ce3919000000d089bdede30e5b8192000015baf0000001bd70ce4000 else (if i<5 then 0xd780b4946ccd62940000972151cfb90639c3d700003c267c157000002174f05e877a3c0000d69fdc07a204aac2cb000000000f1be7cb0c769418052d66974371006b506c80000006bea617380d8a087a16d9b2cf61f29e72eadec2000005b81000031848e64b59d000000383b796b0403c9263a08270e0ec1c12956b6587ef7098b0aa2702b6810fa6eb640e460348c55000003c17e812b19eced0f0960df23906587e01db0dc3d372641dee80b909a7d60afc000072a838329203d7d81470f780000000015ba3e1ca3c13c1ad30cbc5101c000000000180b8f071000000000000000000140c870926c2dd000010e1486f4b1b04000024032000000000000000000b0b500000206700000b697958beb0ab901a8d7c06dec5a00c0045d803c2dba16176c838251a8143e2806ce04b50000283930000383af010e8000070ae4000070d83dd09c6453c599407f381ec0b1c4dab811b830ed98044000006151dc2bd40089400e800da4031f8cdfc0fea4877c3d5f0d7e44f01081e00d4b6dc1424a570440000b0e9cc3caf004400000000399c596c84000086d230736222a942c7060f5c36b0000340d920c9183ec00000035600002017500002447f5602d1e95000001ea2f09cb0ead91306d91300003de57e0e064b6dc65cc000021b2841c2883f80000b706000006015b8222219f8000000000821a803ead75b6084ac3e050ba6c060905988260c0bd00b72e0e13cbe0f33d6812c70e42ab6c105652b4540ba000003111747d890d49021f20a0c0000f0d1c020000002c23f8002883b270684400b362ffdb7f000035b7600ec7a37267e2c00004006cacc200f699b715161849dbe00b81b4542c239d7106b384068c1af611eac1bc1007bf0a8946fd902a181b110a2d0480000028e88114a2dc5b40c7c019330993983900d1b012650c751be10654919eb70abf41cca057765df416de4700d005d405040caa9ebbb6fa2c68761454029d6071b826c00bb9d432a03ed806b619be0197e04836978a00efc7a4d73128111d0412c2cdf7c6c0000000012d130000006fbe0055836a80bf90509a15769cfc81a68c14aa07a24218fa2abc3a890dc80000b03c4000020d6c00009095cc20b51cf5cf10016254037000018656b097c4487903690133c477d190e30d03067fc77fc8546e6a3b012140b9c000031b53df5452d0000004aab40000d042a0038b05d99dc3c762181bb00003c1a0201abc75744f2c58e1904dc50b5c0af95d44904d1c7107062001d3b0d961e06a0cc543bc117d8c28430b7e42d600778c1e310a6d05c4f0efa5829e633fc20492df3c174b1067189f1042d831b6672400006aae58519b0e5c0000000009c553025080a400383c0ff4066a41f1e7db1811500002003900000ca44939f800002034743687091aa5f6000000000600a2c0ce119 else 0x401df01fe425d568540000b03bd1bd600003035c91e3aa9ca50cba87cea664401d4e1a4923c730d4c000000002029e302ef1da396840000026be89cd633ce79aa6a2e6495780000283a2914c1c39bb7cc54bbea0c89029000003db1bd06fd4247000000000c7470c09300b5d5d6221c515f52e7faa01f5621e7d0f5f07dc0000603ae416917ac18acbb014e8602f06c800001026c000040c8001c88265fc32cc1c2884c27678c0000b05c781e136a8f0108109e14f0b6ab15c26a00f2cd93e3078ac20190b97818d311d00000464d34307f6eda456030f610b8611d215bd5467bc41f92144b820971ea94230608640000e0e1ec5e610e27596419ab505132669c000056b136fcd52b640504506271b0b00002986aa00ac1beca69da5b6e708d400b7f14e00000000019261c1967023b707aa04bbc08b800001651e0bc0000034342209fe800cf66ba18c9c0a20000000000877bf1cde839f115e29d76000035c39e0ee40000b5f2c0000f11c798fd70270000060c5f5a5210cfdc12e00003c1fb9063c00000000001df00d040000713b6d2d49664d80596074782de416d45caab72c10afbc2c5600b2e0d0d832541f6782516ae1142a7502c1c30a565550fcbf074a46e38170b8292607731e58902f74333d01015e6900002012d7040bc34a807cf43868072f411660c218306f089683c4a0535c14ce027e96ad477c880e9b4de80000c07f7c3ce408a0000000002c000e1e239846d0bfc037cb1a6f86d696b4b4638c01f8832320dd4000041be8000020d5002c300002439a0000244e3c18e400008056205b142f6fc67694e48822122c3d00eee089d197d80b08db130bab4d8f9a006a83bb000019b00c0db182f890738866bd2d110289317cf007120c4ceb89108d98244873bc0000a055a41ba50a2881bc803db82977016cd85b000000000bb3af005816d3f82ec070cddd8166b15427e40f8f814800001425ca0070002f000034136805fc0000705eb980f508c7ec8112fae052c000029eb6000009999e1a640000800f8c0dfe04ac9aaf9a6b65875d06ad4536f7e940000a1bd9ce02e61405a1c00003c05cf020e8173c0ce00000501940000166340000e1c17c6884369c9cdc00000d979508ab019b70d15df1ad6adecb8491ea5c7359790b0286f035ac558101d8c9461732900a040a4ec3ee90ca3d9d8c0bc40664578a0063070db4c332763fd99426706bdaad8057b4b9ab78e89be5501f18344c6ad0821630ac9c1c3801a698b31084c0000a099640a546139826900001424b1062a00)))
def xmd11 (i : Nat) : Nat := (if i<8 then (if i<4 then (if i<2 then (if i<1 then 0x648814c37bed2aa040a613ff2e92054530ddfb4cc0042984ffdba248514c33fed4b4a88261dfd54521645309ffb64d48a2986ff8ba545204c33fe54b52a8a61ff64c5a548130defb4ac2922987fd95154d204c33fed490428a61b7f6c1a7205309ffb6ad00429867fdb26a5814c3bfac0952a8a619ff2e1a944130bfeb6242842986fbd85690214c3bfacc2a2882619ff6a4a548130ffe302a8a409877f8a9655204c2bfedaa64c8a61bfe481a314530dfbb46c92a2987fd9514c5204c3bfcc8950902619ff2c9a564530cffb52d12209857fdb9540214c3bfac0b52a8a61bf768d9154530cffb6ad4a429857fdb52a1914c3bfc90324c8a61ffa5492024530ddfb4ca80429867fcb56a5214c3ff4a926290261ff94853148130efda40d4a42986feda2480814c3fec90a62902619ff2a1a564530ffe30298a40986fdd53680214c2bfed9150c8a61bfe6952024530bff37052a40985ff9b52a1204c37fcdd30010a61bfe6858048130dff240d1aa29867fd98681214c2bfeda944c8a61b7f6e5a720530cffb4aca8429867fc852a5214c33fed4b4a90261bbf6988508530ffb242a9a40987fe920441214c2ffcda942902619ff601a948530dfbb46c0042986fdd53681214c33fed4a4040a61dfe4815164530dff374900a2986ff9a0648814c3ff49034090a617fe6e12014530bff36654240986dfda7600214c2feed98a448a611ff6e998645308ffb74cab22987fd1214c5204c33ee5cb46a8a611ff6d5a908530dfb160d1aa2987fc95254d204c33fc9035228a6197f649a720530ddf300d3042984fddb3694914c2fbcda942902619df6e5a508530dfb140d1aa2986f7980694214c3fe8c0a62902619fe481a9205309ff374901029867dda3648514c3fe490aa690261afe6a18008530ff8a62902429847fdba649914c33bed2b2a10a61bfa6892014530dfb346901029873f995601814c23fed9352c0a611ff6c9a9145308ffb6454aa2985fb9b4285204c37ec9034628a619fe6819220530cff240d4a209877e920485914c337ecc34c10a611ff2e98264530cff330d00429857f9b0289914c37f4d124048a61bf6481a3545308ffb6454b02985ef9b6295204c2fecd994290261b7e481a720530cff300d4842985fb9b4295204c27fc5d2a2902617be6d8a148130dfab02d1aa29867dda3648814c2ff4d9140a8a619ef649a420530bfb36652a409867f995680214c337ecab4c10a61bee601a408530b7f37050a40986bf9a8600914c37dc9034840a61bfa6892020530dfb2a6d00429867bd95690214c23fed935240a611ff6d4a9485309ff370d0042986edd53698214c33f6d132440a613fe6e98048130bbf36e50a40986f5db3694214c2fdcda140a8a619df661a508530ff824298a40987f495254d204c23de5cb4810a611ef2e5a420530 else 0x61bf7485a354530defb66d28429877f980654214c33fe52b50c8a61ffa548a948130dfba64d1aa2987fd953661204c33fed432a10a6177f6dc8524530cffb52d02a29857fdb8648914c33fed1952a8a619ff4c9a914530ffaa62a8a209867fd95681214c33fec934040a61bfe2e98048530cffb44d4322987fe9216a1204c37fcdc34010a619ff6a19524530cffb44c9122986feda2608514c33fec935228a61bf768d2020530affb64d4322987fd531601814c3ff898b00c0a61df754d3264530cffb64d49029867fd32695914c37ded20a440a61ff66d53148130affb64cab229877f5106a5514c2feed994a90a61bfe284a948130cffb6ad48429857fdb56a5214c3fec90346a8a613ff6e98214530cffb64d48a29877f980654914c3ff4902a440a615ff6c59864530bff360512a2986ff9ba480814c3feca9b4a902619ff6959524530bff360513229867fd92695104c3bfca8240c8a617fe6e12024530dfbb46ca842987ff181285204c2bfed9352a8a61ff654ca148130efeb0298b22986fdda854c914c3bee99262c8a61fd754d8524530dfdb44c1122986fddb268c514c3fb6a9240a8a61dfe6458048130ffd24254a409857fdb9295214c37fc5094a90261ffa5499848130ffb2a6d0a40987fd531481214c33fe4ab5210a61bfe688a054530efdaa4c1322987fd9834c5204c3ff49035290a617fe6e13248130cff974c9302987bf581609514c3bfc90220c8a619ff649a014530feeaa4a8a209867fda92a5214c3bf6c1264c8a619ff6a59844130cffb02d4a42987fd953480914c33fedd32a10a615ff6e5a848130eff322d2a409877f985481914c33fe29152c0a61bfe6c1a220530dff344c01229877dd53660914c3bfcc8b0490261bfe6a0a948130efda4290322985ff9b0214914c37fca834040a619ff2d5a944130affb6ac1322986ff9a8295204c2bfed814ac8a613ff6c9a824530bdfb6c52a409867fda5648814c37fcc0346882619ff289a8645309ffb74901029857fdb02a1914c3feca9a64902619ff541a920530aff974c1322987fe952645204c3bfc9032ac8a615ff2e98564530cffb44cab229857fdb9480514c33fed4a4028a61bfe481a014530dfbb44d1aa2986dfdb269c814c2efedb942902617fe6c0a864530cffb44d2b229867fda22a5514c33fea9352882615ff6e5a548130ff9aa6902429857fdb2295914c37fcd295290261dfe4819864530cffb5254240985ff9b12a1204c33fed035290a61efe6018524530cffa4254aa29867fd206a5814c2fbedaa40a8a617fe6c4a948130eff32a90220985ff9b2281514c2ffcd930090261efe6011060530dfbaa6d01029877f9204c5914c33fed2b2448a61bfe280a254530affb64cc322987f7950481514c3bfcc894a90261bf72c9a314530fedaa4a9a40986dfda7) else (if i<3 then 0x66d29229867fda36a5514c37eed9b4a10a619ff6e5a220530bfbb66512a2987bf921601814c35fed430010a619ff2c9a944130cffb52d42209867fca2695914c3fec98a6490261bfe6a12014530cff924d4902986ff9a0148814c3bee5cb46a8a619ff215a948530cffb4ad4a429877f920695914c33fed132a48a61dfd5451064530dff350d2a40986ff9206a5514c377ec2b4c10a61bf76895324530cffb0254aa2986fdda3648814c37ee59346a8a619ff655a008530fef2a2d2a40986ff9b5680814c27fed934028a619ff6899220530eff330902209877f5214c5914c37fac0b46a8a615ff2e5a254530bff174c1a409877f92060d914c2bfedc144c8a617fe6c052245309ffb64d4aa2987fe920545214c37bed2b0a10a619ff2e5a354530cffaa0d4b029867fd506a4214c37eed2aa648a617fe6e0a148130bdfb6c512a2986f7da5540214c37fcd2b0048a613ff6c9a920530bfbb6650a409857fdb96a1104c3dfcc030a10a619ff601a908530efeaa2d4b02987fe921609204c3bfc5cb50902619ff6e99214530ffaa6252a42985ff9b3285204c2bfed934ac8a617fe2e95348130dff2a0d0042985ff9b3295204c2bfedca4040a613ff6e985245309ff974c92a2986f7cb8694214c3ff4a935090261ff654d8024530eff240a9b229857fdb22a5514c37fcd934040a61bfe6a18024530ffb140d1aa2984ffcba649814c2feed994ac8a61bfe6812020530cffb5254b02987bf9806a5814c37fc9035290a617fe6e0a948130defaa4d2922986efda6654214c3ff49030a90a61efe60580481309ffb74cab22987fd9532a5204c3fec98b0090261bfe2a5a148130cffb04d4a20987fd8b068d514c33fe5935240a613ff6e98508530dff350d0a409857fdb9695104c37fc5494a902619ff2c9a960530ffd2a090242987fd9312a1204c3bfcc8b4290261dfe2a59848130affb72a9b22986f7da5654214c37ee5cb46a8a619ff655a908530ffd17490242987fd9532a1204c37fcd414290261bf768d9214530cffb0ad4a42986ff9b5680214c2ffad890a48a619ff6a19214530cffb30d0042986dfda7540214c2f7edb0a440a617f76cd5144130cffb64d2b229877f595545104c3bf6a9144c8a61bdf6c1a508530dfdb44c9102987fd531681214c2ffcdab4290261bf76c9a354530eff322d42409867fda8648914c2bfedaa42c8a61bdf2e5a508530ffb2a690102985f7db5285204c27fedd0a448a615ff6cca264530bff36a99240985ff9b1601204c2ffcd810428a619ff649a920530affb6652b22986bfda8540214c37f6d124028a613ff6c9a314530eff24052b22986ff985680214c3fecd8aa6902615ff6d5a864530bff362c1240985bfdb8285204c2f7edb14290261dfb6552048530efdb30902429857fdb1655914c2ffcd894a902 else 0x14c27fedab4040a619ff609a914530ffd240c8a429867fda9685204c3fe698a4090a613ff6e99864530ffd2a4c9240987fe921655204c3bf6a9240c8a61bfe6a12024530cffb72d28429867fd822a5514c3ff490b4a90261ff64c59248130ffb37498a40985fddb3295204c37fc9035228a619ff6a19824530dff240d49029857fdb9548814c37f6d1240a8a619ff6a4a148130ffaa62d2a429867fd516a5214c27fedd10a10a615ff6e5a148130dfbb46a80429867fda9295214c33fe54344c8a61bfe601a948530df7aa4d2102986ff9806a4214c33fe5ab5210a619ff289a954530dbfb4e901029857fdb0289914c3feca9a4088261efe600a960530dfbb46490a2986ff9a0214214c3faea92a648a61bfe481a544130aff972d2a42987fe920695214c3bfcc8a6490261ffa48592481309ff974a9a40986ff9a5480814c33fec934628a61dfe60192645309ff974c0242987fd8ba4c5204c27fedd0a440a61dfe481a864530dff160d1aa2987fd9854c5204c33fea835290a61ffa548a148130affb6a90322987fd58168d514c3feca9b24902613ff6c9a524530d7fb50ca8429877f991481214c2ffcdc34a90261ff554d5144130ffe220902a2987fd8ba54d204c37eed1aa040a617fe6e13148130bdfb6c42922985fbdb4289514c2bfedcb4488261ffa548a848130affb7052b229867fdba648814c33fea935240a613ff6e1a008530dff350c0042984ffcba655214c37eed1b52a8a613ff2e93148130eff172d2a40986dfda7654214c27fedab5210a615ff6d592245309ffb74410a29867fda9248514c3fec9894a902615ff6c59264530ffd242cc240986ff9a2480514c37fcd2b0010a61ff64c4a948130affb72d0242987bf981609204c2ffc5d26290261bdf6958008530bff174a8a40986dfda7540814c2ffcda95290261dfe480a864530cffb0ad4a20987fe952655204c3fea88346a8a61bfe6812048530dfbaa6d1a209867fda2660914c3bfc5d240c8a61ffa4855348130ffd240d12a2987fd8b36a1204c27fedd324c8a61bfe281a954530ffd24254240985ff9b5609204c3ff49014a90a61bf7609a314530ffd240a9302985fddb3214914c3bfcc8952902619ff6899214530ffaa62a82429857fdb5660914c33fe9034ac8a61bf768d2014530cffb04d2b22987fe952481104c2bfedc32428a619ff2c9a914530cff94ad1322987fe921601204c33fed2b3048a61ff64c4a054530ffb262d0a40986fdd8268d514c3ff49094a90261ff64c59548130dff340a91029867fda26a5514c33fedcb4428a619ff6a59244130cffb02d2b229873fd806a5814c33fecab4040a61ff54c51048530defb72d2842986fdda3681514c2ffcd8a6490261bfe601a008530dfbb46512a29857fdb9289514c37de42b4810a61bfe6a18248130dfbb)) else (if i<6 then (if i<5 then 0xe4818254530ffdaa4c1122987ff9ba601214c3bfecc34a90a617ff6c9a354530ffb966c10a2987ff531545104c37fed4144a8a61ffe604a948130ffeb02d1aa29877fd9268d514c3bfec2b5290a61dff6153264530ffda42a9a40987ff980645214c3ffcd1140a8a61ff754d1048530dffb04d02429877fd80289914c3ffa90b22a8a61ffe481a354530fff30052a42985ffdb5681214c3ffcc022090a617ff6d53244130ffdb5090242986ffd826a0914c3bfea9150c8a61bff6a15008530fefaa4c8aa29877fc856a5214c3bfec2b44c8a61bff549a824530fff242502a29877fd98545214c3ffc9030688261bff615a344130dffb5052a42987f7d8554d104c37fed430010a61bff6898224530dffb44a91229877fd954c5204c3ffc902a4c0a61ffb6952048530fff174c0242987ff950481214c3bfecab4090a617ff6c95144130effb0452b229877fd826a5514c3ffcc0b24902617ff6d4a848130ffbaa654240985ffdb1615214c3bfec2b50c8a61dff5491064530ffeb02c92a2987ff932281514c3ffcc2b4a90261dff654a848130effb0490b22987ff953285204c2ffed8b04a8a617ff6e1a048530ffbaa698a209877fd98481214c3bfe90b30c8a61dff6498344130fff30a901229877fd85545914c37fed1152a8a61ff754da048530ffeaa2c1a20986ffdb8688914c3ffcc0b3090261dff5453264530bffb6ad4a42987ff985609204c3bfec2a62c8a61bff6898344130bffb7050a409877fcba615914c3ffa88346a8a61ff76095324530effb06c90a2986ffda5614214c37fed02a4c0a61ffe54da848130fff2a254240987ff982295204c2ffedc14a90a61dff2e99260530fff306d2a40987ff5514c9104c3ffc5c34a90261ffe540a848130effaa4d4322986ffd816a5514c2ffed8b0688261bff6a12054530ffbb04d1aa2987ff9514c5204c3ffac0952a8a61ff76c95324530fff30ac9240987ff980545214c3ffac2aa288261dff549a264530dffb6ad1102987ff9804c5514c3bfec132a48a61dff6059564530fff2a290242987ff980614214c3bfecc34090a61dff6091064530ffbaa690242987ff9514c9204c2ffed930a48a61dff540a864530cffb0ad4842986ff9a2480814c37eed1952a8a619ff548a960530cffb5242842987fe952685204c33fed4b50902615ff6e5a054530cffb4ad4322987fd953600214c35fec135048a61bfe281a354530cffb24d1aa29867fda9549814c2f7edb0a448a61dfe481a264530dff34490122986fdd3268c514c33fe90b4ac8a613ff6e88524530cff90454aa2986fdd316a5514c2ffcd8262902619ff614a948530ffb374a9a409857fdb32a1914c37bedc34a10a61ffa480a948530cffb5229102984ffcba609514c37fcd032a10a617fb6c88524530dfbb46902a2984ffcba6152 else 0x240987ff980689514c2ffedc262a8a61ffe2c1a254530effa42a9b22985ffdb8441214c2ffed9220c0a61dff540a264530dff950d2a40987f7d52649514c3bfec2b4ac8a617ff6cca254530bffb6a882429877fd524c5914c3ffcc034a90a61ffe5498024530dffb66d28429877fd52661914c3ffcc294290261bff6c9a524530fff30a98a409877fdba615914c3ffcc0b04902617ff6c8a954530dffb06d00429877fd922a5814c3ffcc0b2a90261ffd5458060530dffb4a99220987ff5816a5514c37fedd304a8a61ffe6098024530ffea62c0302986ffdb8688514c37fed434a90a61ffe4818060530dffb40c2a42986ffd52680814c37fed4322a8a61bff605a948530fff220a9a40987fdd5254c914c37fed1324a8a61bff6c9a824530dffb44d1aa29877fd92441814c3ffca826290261dff4c9a954530effb0a88322987ff9804c5104c37fed4324a8a61dff6558060530fff300c1a20986ffdba548914c3ffac094290261dff5412164530fff300883029877fd98441214c3bfecc344a8a61bff6a12014530effb3098a209877fd2160d914c2ffed9352c0a61dff601a948530dffaa4d4902987ff8a0609514c3ffcc1b4290261bff6a13214530effaa0d4b02986ffdb5688914c37fed295290a61ffe60d2048530fff240c2a42986ffda5681214c3fee99346a8a61ffe6153248130fff2a6902429877fd82660914c37fec134a88261ffe60ca148130effb22c12a29877fd85648914c3ff6c124090a61ffe5418060530bffb6454b02986ffdb8694214c3feec1a62a8a61bff549a344130effb30a9a20987ff921601204c37fed424090a61dff649a960530ffeb64a8a20985ffdb2214914c3ffcd295090261dff6498060530effb24d12a29877fd956a5214c3ffac0b40a8a61ffe5458348130fff2a4cc240987ff581289514c3ffca932a90261dff6455348130dffb50a82429877fd85481914c3dfec12a0c0a617ff6d4a948530bffb7052b22987ff5b8545104c2ffedaa6290261ffd6052054530effb74c93029877fd9254d104c3ff6a9144c8a61ffe601a048530dffb04d29229877fd80485914c3ffa88304a8a61bff689a954530dffb74c2a42987ff55154d104c3ffc5834a90a61dff6551048530fff30ac8a40987ff982601204c3ff6c126428a61dff6553154530effb3052a42987ff521545104c3ffca9b4a90261bff6888524530ffda40c2a429877fd91615214c3bfea8950c8a61fdf5495344130dffb04d00a2987ff581645514c3dfec1220c0a61dff6159508530dffb42a9a40986ffdba608914c3bfea932a48a61fdf5495144130dffb44883029877fd81649914c3ffc98940a8a61ffe605a548130dffb4a98a409877fd82541914c37fedd30a10a61ffe4811060530dffb44c29229877fd954c5104c3bfe90b2ac8a61ff) else (if i<7 then 0x3c5e3c383c073bcb3b843b5e3b383b073aaa3a373a0639e039ba397e390b38da38a938573831380037c4377d374c371b36ea36ae3651362035fa359d3561353b350a34d9349d346c343b33bd338c3366331432ee329c326b323a320931e331c831a23171311430cd3086305530242ffe2fc22f7b2f4a2f242ef32eb72e7b2e132dd72dbc2d752d392cf22cc12c902c6a2c2e2bfd2bcc2b902b542b182abb2a7f2a642a332a0d29bb297f294e292828ec28a52848281727f127aa276e2732270126db26aa2684263d260c25db25b52584253d250124c5249424632432240123d0239f232c22f022b4228322522237221121e021ba21892158212720f62078204720211fe51fb41f8e1f5d1f2c1f061ed51ea41e7e1e581e111de01d621d051cdf1cae1c881c4c1bd91ba81b771b511b151ae41a7c1a4b1a0f19de19a21971194b1925190a18ce18a818771851181517e41792173516ee1686163415f815b1155f14f7149a1474142213d0139f134212f01288122011ce1187112a10e3108610290fd70f7a0f280ecb0e790e1c0dd50d830d310cdf0c8d0c300be90b8c0b2f0ae80a8b0a4409fd09ab094308e608aa0858080607bf076d073106c90682062505d305a20550051404cd0470041303b60359032802cb026e021c01d50183012600ea008d0067004100260000bffb6ac0302986ffda8689514c37fed1b40a8a61dff608a954530fff240d4b029877fd984c5514c37fed1340a8a61ffe5499148130fff30054a42987ff953685204c3bfe99152a8a61dff6552048530fff30098a40986ffdba608514c3ffc90b3090261dff6059864530dffb0ad0042986ffd52694914c3feea9b2290a617ff6e0a548130dffb5098a209877fd506a5214c3ffcc026428a617ff6d52048530ffbaa6d2a42986ffda8681214c3ffac0b04a8a61ffd545a060530fff30ad42409877fd52695914c2ffedc144a8a61ffd6053148130fff174a9a409877fd52660914c3ffca930690261ffe60da848130effb52a93029877fcb968d514c3fee5cb46a8a61bff695a948530ffdb0290242987ff985685204c3bfec094ac8a61bff615a908530bffb6a513229877fd95695214c37fe90b52a8a61ffe480a960530effaa2c1b22985ffdb2601814c3bfeca95290a61dff6159264530fff30652a40987ff985481104c37fed2a6288261ffe4859548130bffb66d0302985ffdb84c8514c3ffcc026488261ffe481a254530fff140d1aa2987ff8b068d514c37fec2b5290a61dff60ca564530dffaa6d0042986ffda2645514c3bfecaa6488261ffe614a948130fff300d4a42985ffdb3545104c3ffca930088261dff614a264530dffb50c90a2987fdd324c5514c3ffcc0a6490261bff6898214530bffb7090242985ffdb52a1914c3bfec1240c8a61bff6895020530ffdaa454 else 0xa6b4a683a652a621a606a5f6a5c5a59fa579a548a522a4fca4cba49aa469a438a3fca3e1a3bba38aa34ea328a302a2dca2aba285a25fa22ea1f2a1e2a1bca1a1a170a14aa119a0dda0b7a086a055a0249fe89fb79f9c9f6b9f459f149ed89ea79e6b9e459e149dd89da79d819d509d1f9d049cf49cce9c879c569c309bff9bd99bb39b8d9b7d9b629b319b0b9acf9a889a579a3c9a0099cf99a999839973994d992798eb98ba988998639832980197db97b5978f9774974e971296ec96c6969596599633960295e795c19590955f9539951394ab947a9449940d93e793ab937a9349930d92f292ab924e921d919f91639132911790db909490589032900c8fd08fb58f8f8f698f0c8ef18ecb8e9a8e5e8e228dfc8dd68da58d5e8d2d8cfc8ccb8c9a8c5e8c228be68b948b6e8b068abf8a8e8a688a4d8a1189eb89af89898958891c88e088af88688842880687d587a48773872c86f086bf868e865d8637860685bf85838552850b84da84a98462843c840b83b983728341830582c982a382728241821081a8816c812580de80ad807c802a7ff97fc87fa27f7c7f407eb77e9c7e607e247df37dcd7d707cf27cc17c4e7c127be17ba57b7f7b387b077ad67aa57a697a437a0779e179b079747959791d78ec78c678a07864782877ec77bb778a775976f176b576847669763875d0759f7542751c74f674c5748974637432740c73d0735d732172f072bf726d7231720071da7188712b70fa70c970987051700a6fef6fc96f826f466f0a6ea26e5b6e356df96dbd6d8c6d5b6d406d0f6ce96cc36c876c566c0f6be96bb86b926b6c6b466b206aef6a876a4b6a1a69d369a2697c691468cd68a76881685b680967d86770673f670366d26680664465fd65c165906554652e651364e264a664756444640863d763b16380632362f262c1629b623e621861d16195616f60fc60b56079603260015fdb5fb55f845f535f175edb5eaa5e795e5e5e2d5dfc5db55d795d485d175cdb5c9f5c6e5c1c5beb5bba5b895b6e5b535b2d5af15ac05a845a485a1759e659aa5963593258d558835852581657e557bf576d573c56f5568d5651562b55e455b355825567554c551b54df54ae547d54415426540053b9537d52ff52c35287521f51ee51b25181515b512a50f950a7506b503a501f4fee4fc84fa24f3a4ef34ec24ea74e814e3a4e144dee4db24d814d454d1f4ce34cbd4c8c4c504bf34bc24b914b554b2f4b094acd4a9c4a6b4a3a49fe49cd49a749764950491448c248704834480e47d2478b4765473f46f846c7468b464f461345cc4585455f450244c644ab447a441243e143bb438a43594333430d42d142a0427a423e420d41c641ab4143411240cb40b0407f4059403e40023fdc3fab3f6f3f333ef73ebb3e743e4e3e073dd63d9a3d693d383cfc3cd63ca5))) else (if i<12 then (if i<10 then (if i<9 then 0x81550e049041f8028a046a380f8123903e0207d44700514098092202701011c03810190427043c078001d03fc08130124014e000424748a04c048fc040401fe040ac0f0290128025c040a18a03e034c40c0a70091d228130123f0151007f8028a04c048e07f8082ba55228130123807915c038082303e048fc1182c8ae0002c0ac870248013c0b807010600d0dc0d82c8ae0002c0ac8702480680ac0bf02e0061c0c8154012e020514501f012620605780809e0005c13012400503e05380811012602981f8018e050048c07f80e07e0062813012381960607e4402be01228130124832e0602243f0091409809238101402463806940a700e05c04068280247c0e0538098ae0007c091f81685e000cc0b815370151007f8028a04c048e42781700e02048a02c0ff019100bc06c8a04c0493c080a70031c098091b81b08915c000581590e0491c118470091521c0c815381a90f228069303814e0262b8001f0247e02069450410125e02066434a203e034ca208381fe03c0145026024881641243305e0005643812401a016c2006c8a90e0640aa00ff01911c000ec8a04c04900200d00903c402208404c87e01228130124704608c164570090e0640aa380a8803fc01450260247013c0010a8704c048c2ac15814315c000f812382b062c124570090e0640aa084f02219c0409140c703915c000581590e0491c0b80f001f02e03c0060c8058b808100163d2f7d2b0d295d27ad249d218d1e7d1b6d19bd15fd144d113d0e2d0bcd080d05ad029d003cfbccf96cf70cf4acf2fcef3cecdce9cce6bce2fcdfecdcdcd91cd6bcd45cd14cce3ccc8cc81cc71cc56cc25cbf4cbc3cb92cb56cb30cb0acad9cabeca8dca3bca2bc9e4c9b3c96cc946c915c8e4c8bec898c867c857c847c80bc7e5c7bfc78ec75dc737c711c6ebc6afc689c658c61cc5f6c5c5c594c56ec53dc501c4d0c4b5c479c453c422c3e6c3b5c384c35ec32dc2fcc2cbc29ac25ec243c212c1f7c1a5c174c143c11dc102c0d1c0a0c07ac05fc018bff2bfc1bf90bf6abf23befdbed7be85be3ebe0dbddcbdabbd7abd49bd23bcf2bcccbc9bbc6abc44bc1ebbf8bbddbbacbb7bbb55bb19bafebac2ba9cba6bba45ba14b9eeb9bdb997b971b935b90fb8e9b8b8b87cb856b83bb815b7efb7beb798b772b736b6fab6beb698b667b641b61bb5eab5aeb588b557b51bb4eab4a3b472b441b410b3dfb3c4b393b36db347b321b2fbb2b4b283b252b221b1f0b1bfb199b173b14db11cb0f6b0dbb0b5b084b05eb043b007afcbaf9aaf69af2daf1daef7aec6ae7fae59ae33ae0dadf2adc1ad90ad5fad2eacfdacd7acb1ac80ac44ac1eabe2abb1ab96ab65ab3fab0eaad2aab7aa7baa55aa2faa09a9d8a9a7a981a945a909a8e3a8bda897a87ca861a846a815a7e4a7a8a78da767a741a726a6f5a6da else 0x1c058140244064050090e42f0860e07409158210960205e82033370003c2ac13101f8140243311c000a012250060061c0c8152b01a09c000c0292b880620524570103f4a81581248152100c80f8122d040322e0061c15f0231c050ce2295409064048b2230050050e61c09198028702a050981f809a20284a00050090d02701e00068091409c05052050801c05817024410dc23800170325a060cb800140245610c024381e024502e05381109e020480ff00418840e0240f812280b024260b22009033220703e0d86a14c2d8803e06404812380d90dc00140122e00016098091004d070323809c0503814024510bc01c3813206054c0c40a81203f833817018128e014000a012200b034048621b8008701a0a0091a847000320d0091442f0013c0680a158432a03005c861c158171f000000500911027010243e0362280304b0e048d6224381f0244e01c054501a2015e0204860414701402a4157c0283814080048dc2380407030048bc0b8033970e048bc028203e0584e03c000a0152700c0e098091006c8a90e068802580307024460003414012202102e05701812e0262303f02e00ab10069438320245c00838c380b02a590ac1c0a83a2009a000640a9009036120704c0d87c001881702a4654050090c0680b0320548a168010802e40134024701527006760640a901281730a04818f0105e0980a1a2e00ba000504381224040240e87c2380207030048bc07800140244025c081d0f06702e020508c128001403e4016050090d4381703e050805e8003102a403f40c0a8e43818024304bc0780187028054dc040f809024403e0680a988043c0b03814e00048c72c0d014e0381cd101fe000550045190121d0850e040091013d0302a360121d03810024530a0480bf020560c40a015e0061d5c0180026024450e0c818812200d0340a4762018b2a064048bc0284026024402e8100a00902bc080970050e990c02c0a0192015c0e07f808122c074640400912840190160d009164381a60a04880c80a0121a070240d8604c090b80288016050091681814032304240c0f81226070280547c0284019068048a06b021870244057c0021832514098091e04808e000c94518e0320551c080a70003ea1c0a981c013e05c058601806605c0aa404031e0122a4381902a70300c58601702a5157c0b8003131c048c05003f0091d22813012382b03207e4402fe01228130124f03606c2243f0091409809224501503a3c0fc040a18ae0007c091d84031e0122a4381902a7062c300b8122703606c2243f00914098092201903e03c0b8001702a7021c064401fe000ae450260249027c040f809511c01450260249029c028028e514098091e02204e05c0380812350302a42145700042a1c092380f0202804a860173005813c014501030e098092284031515c0005) else (if i<11 then 0x500a900a0361188c0e0c8091180b0402a340e07c090c0a7015102acc404303ea2804a4c4187449800048173304e000a0091013012103f0280486068c3f0003a0a0091b8001402a30640541d0c81607e000c80917800af08404892220000b028048bc000a0151a11e0081c0c012280b02804860278001402a4057c078001402450420559201402522b80487403102e0640a938000b032054840b018090240e8a0fc0a012183f02804860518400b90c064a05005c860324c004000c81526070240500c9084b880330101b15820320300548420130121d87a7210c091380409032301221d8201902a540661643f00a00098091c18d0050c0480882602a70338138001a0245062ca80b8c10e0420007c09168238870e0f80e10930320280546048058361b0890ec000d01e024691002c0a012228650fc042401a29876014e413012298640940c0903a2b0390e02c0c834024651140380988514068d4000a01f181f02a0482202151dc01452242c00016050091409812170001609809101882102b6140970102f28a862644010042054861c158151f00600050091104832032054803413012181202e054661f0000b032054aa168450002e4e046380a0f8008701a0a00917803000320548054840120640d80f980903610150420482201f012a39457004f0060005009100d204e0262004812301f0322c0002c0c815201530e048604c09080f903b1121c09168001a062330fc000a01224886000c41901228097100acc381228218080240f8122a87e0002c0c815281503fc0703f00314603a048188c0f815e0321e0201236053100400b9004a88e02a280d140a1870640549813817010344e01c040fa8a4125e001080a8c15831a1806480248420760121c091b8040903232006144f01420218088101401228ab02a61780539032603e098090c0948706c360900014012203102e07c09702e0211e86201882102407f8118502bc038084450143100640a9280014032302a0d01d0d43700e05c040a140888602a2200970104205f80702520701605009124280b02804884ac18818e05c040be0c3b0013c05066230002104c450c2200482602456050148481202005cc07f80c040244e008000c815258820007c091004d8805721c09140b81fe0501f80815e00051011806845028460607c0a8c1081fe03c000d0195140251810c2f01024068a01c0a83a1887a5502409130400b02405c88138018e034048ac140581a0244e03c000a012203104205c0970203e05780f000880c16c0e020430244e00050090c09700043c040fc8a812707e050090f80a88a0007c0a82f0247110024130122585a7205c0a9004f000280489c000a012183202a203a068090f80f0002805482ac0ad88e0140043812032890b6228028730e048c614c4700e05c040a1a8001d03205486 else 0xa14c2f01a00068091809036101702804870100903102fc040a9a022040240500c94c5487a000640a941881503ea2380701034a2809258090920f4001b031330002807c6a2843809028048ac090481202005cac1005d07042491002c0d012200b06c2e00c000c81520120300d8607c210151c8709c0c8058122c8a6080640a900c015210400c3812300d04c048740d018150424012048198e8001702a36080c4090d8001403e3206054c3812202103f02044701213c000ca8a49080160641a0122b87e000500a91818090164200b8123031a0005c0a900f83202a304340c0ad07029c001d28e5149034c0dc3c00028054c82013012190906605c6040130121d08710a1e8010506c07cf622801870244b10a1c0d01fe020c4c3a8a01290138200e8172303a06622438122b039100c809100ab2461204a45487e007035c0418a8a0125808c0a02f018120b0ca238000b028054a04c1881702a461121c19018024531581c0c8c0c0121009e0005009100a28801607c0a9643b0003c04898000481402e44238384452a02a520fc088484c270122005060510381902a4068084c470002405c0a826401a40861c091380032032054807f80812184402b42409031515c0143a38090902a38044260381d04c048d02200407030048a02409033181531007f03821e03c00c5028024a0300578470030e048dc2005a07030048aa1780809e00068091b8000002804880501f812190781604860840ae8702440200641a01227025104169c8172d038126200903a2d8840e07c09138020002804882780a0b0388702a0e89c009d81902a404261404827e04050dc2005c07030048a61703815028401a02c130122700e020254501a2887e00024140122b08e0009809110258840f40cc281f0327809c040d012218702881c0a9083f00038130804c09084882110310240d8621f80701122050a05004f0002a4a0ea2005814024570bc05c3891212502b4e6c381222878000500913804870200c809178003103fc06454093700a000640a900fa0440fc0809701e00051024545687e0062b018123f000000640a938001a90e02409140a48704c0488ca80a012183480a04a0048a04c054e0c58201806c4020069c3f00028054c1100a83102408404a8a50fc012c0e43d03310048a42205817181ae0021c0682802460561280b81523057440500c900b81510130242034a1c19012218510a0240c8152f00016098091380b0c212054921e0000b032054a04c1d0818f0102a3042c0e0248703e048c0278000b028054a0c40b81f02bc0010f02e0208c178125f08e0101c0c0122e04e03c000d012281504207c08812e000514728a4c8700f02c09138470040e06009170470004c04880480c0361b87e00cec0a918381d062048805f81015024113801873f08e0101c0c0122888e000)) else (if i<14 then (if i<13 then 0x61140a0d8243b02a310fc0004814024583c0684cec130121f0002805461100a8140240c645487e00813c05040c8130121f0001a098091143f00016098091702701e0006809140481206c3e002bc0a0c04f0003404880d2000129152380a9b805000280648c0c058140244a0802c0b8122700016098091004d88a0007c0c940ad88a002780c970002b0634100c9410f010282ac0fa8a01270640c4090c10c0a808e1c1581fe0414a04a4c5503b1021c0903a318a25409809118002602430260484c0f80032028048b4000d0211b03e000c80a012285104c048613018d0c032410ec00068280245a08052c448706c581007409017270001a220438260246200050090f8470040e060091780b000280489c068001402a460721c08012203103f22380c8a81a6e01000190260245017c0014012228aa000640a9083f000280489c000a0121e8860b21c091381701e00048489093103e00051470152f0003009809101881fd1581380c09348860e0c809108280905205084100a58810e0481d180a84207430134000a0192085e01c0443f020a0050fc054450703e054091a4280b0280548a20c4487c00048bc004409e070050aa1c0f8361f0001a09809138053930e0489c078010902a48070100a012e05c040b81fe0090290200e82602458088110388703e064d8230011030e13c091942d040620d88616800260244111c001881fe0322a049f80500032054801c0f81402e4c0e0c8090c0e8310243013c238050702450420680b9034080240a70104dc0809700601802422040500ce0702a5c09c078001a024521a034c3812210002804860c60201502404f80f00b44804805c0a988043c082201431dc00092f802000280488057804880660ac0d48ae0207c092804f000320d009148428704205482178009e034050b61d86015188ae0021f81027028622081c190122700a000640a93800000320549810c413b03e048bc00578141d03028800168152c040320d878008001402a402bc028009e03251560e840868401550e048a0264381206c42000500f8e43f0003e3c0e62b810140745a11c000c834024531581c068280245a0bc000d0122188e000c809101a70102a050809018821e0205245044a54049205443d00b44064a4114281206c402604840278001d02a4b0aa1c0d01fe0210cc3a8a012930fc000a012201f01362381014e0204a9520820120323b1007c090f80000028048962380500b0e048bc0b8081419cdc060241d10090140323e0004a4548e02a51560840f90420e82781701e0004958138018e034048b21c19014024450a02c0a01f2017013c078101402b430f81380900034048b020190170244e0004c090c1a4000240c40b82602a72562af01f08d11c000f819402101607c09100a70005a0549c06800140244a11c000928a028064c else 0x14170002b02404812281780f8000a0122a09e004240913805002120648490188af412084a074207f808361c8690e050091301c87e014000a01530098180d06620108151b0002a06060480a09438120260d8807f038120644413c00068122209e00424091103b0002e05080cc0b8141f0002b0247216058140244812622800360245a060481b0c0d1088160c4091604d2a03404880850488c3d0006206480480c0361d030240c01b130001702802c09140bb2a1186a0781e438122e0c02809870740a81218310880846024090170164412a1f8001420150120606a1943e00028048b40c0a90702407cb813800121b02a10c0c721c14836181d06c20280844048058a43036028048805e950140244a06a168218806c50300d854000f8141c32028054604b060a43d0002a0508c041b0a4381702438120480a03a2015e0005009120498706c048804983898404098120640d88c200900b1d2a028064605e860122124812024108f8004404c3e000b00a8122187a000d809100bd0004607c9c02800140244812c064470003450240d8521c14836181441805404900af008000500914090140423e00056048f8001206834120242103a22090500e860540a012198720e2ac0f9009817a184240c96840603812028303e050580c1b0090324029c00090c18812a0005c86180a814a54048a0240903f183160b62243910f1020280d8861780539024402f80103814032502bc02800122012e00231004a4382b201590e050721803814074403f81c0a00d02a5c08424090362013204048848362f00024060602643812028450d80143814024502a82c0a01224048120486092430180664e014100481923050242c1818120241d0c0a809e014000801236000560480a900903206c3a0721c10815260002a05074a80a012183f0280487c002c3084880d0158120488050108151924024a1c0c0332a02412427800ab032603e024108122015026202a05103c040245034623800142286e040f4781c880261e0c0812e020f0781e438141985e0061e9c819290906c040091281a0b01204880d80a0121831a0805c09100a50302e07c9c02820121c09c080b46052950151b0890e20240e0198f8050030e0500c941482606e3610054048c0d604a00048980144036122048a07c0a01718152100840d100b81416000280486c1643812012402b01c0a01f260406a0a060cc0a01218310420540a024e0122a438124a8820e07c0a928270103004880c40ff01823024a040130121d0330b6200f8192b2a21007c09108410002405c862180539032054a098090810f00e0207e45409303102f62380702e0361c84a18002807c05480c40f82102fc080af00473c040902b581ac09c00140122814a0061c09100983a1009e0002c0a0152a09810e200903202e6e006380e81a024502) else (if i<15 then 0xc0b028048806604833181590fc028001402460280fc090c0581402a3a0007c0a0c28015140910e0480a03a2d0420b21c740c0901406c4a064200a821250230a0441b0122985c0f40c09138050030e06486238002c02a048a6200a836181501381c78128002903241560541901f201222021220878133925605cc4242425860b80500028064805c0a00b0244a06053038122014e0005c09100af0080005009140a70002a390e04c1b0c848360280489c08848804c1002a048922204021115024848123814081590f802800140246c0e048068152603a0f21f800140246e000540c0c0aa8702405084081b10902440280840a8d84012068302e07c82187252a0d2a0815e010000a012284b02a0487c000a8181f00a000500c920581502405094a80a0121815a000507c000a818180bc07422440192815e000507c02800140244a080540901406c502a0d00f8d428140840e8804a048140744029c000a8c038120280e8805404f00028048a826c40120664a020c4405484c090240d8ac138083618170640500a90814090280481b148481406c0488057800140244050048198c0af00a000488623805000244029c000a81824090280481b100f9870640500b95844871404813c000c9019818118502b22143e00a00064f01303c8702840250241683326070280547c019c8a81c87042054861c84f000244e000481a0f81049160302a62243d0002469100cc090e83d2a02804894001b188024459a824108c0a809311c0010812330391004060ac0a03a181f6074118118890e0d8e02604700042244091904f000280489220198140324e0140004812240006c05009100a20c02a0249024188191f00a000240c9204809042306d41013109248802e124091303812028302a4c8090f00014024302a0245c028001402440932201c012210802406860c7808874120e8a0d8090a03e0002e050091504012016391521c0a01225010520d8741f800140244914050048c0b83202a05080d8058121d0003e050605780400028064a427800121e07024440741f8001502841224140b80b02458120a01d0f80028101508407c681c0f8141d0306c4240c9282015030303e0d00a8c0a48703e0c80a940a987a00084091604f0002a82409142100d02a340ac000a817260409604870241d014181282224410938109121261f8014090440663a080240a8182015e000c80a019281503a068091004a8740fc0009014348706c0240910095391220d8805f06019412402bc000d012260705020132200904921870300d874000f81418120300d8781c09015181550fc02800191566030218090362015a0006455900a83202804894178001a024480f8000a0122505e000486617800141814e00048605f0620902440280541b0c1b0121700672054605505814024402a067800e818 else 0x2120840d0122504608c0a8098706c606c42454100908c3d390240d880540901806c4a060d8848192015028a1c1d100a700101f02981c048122d04024201321c0901420144180240a9022209042302aa1f800120285a00041450e43))))
def xml11 : Packing := (1008,4,7,0,0,16,0,xmd11)
def xmh11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x20ca0adc0000004f980f33191f4061c00e0009300003c2c5d06d8000000000982600000000050ae3642200000000000003027580795c135209e0c105342ec000066a6d0110c09600000d015f40155675c59e3206e00c22105e3c659802714008e005b1ec8a01708801f0321c1c616a2f40b8813cc80cce0504866be0882814f00002c05bc02829dadea57d00d1706df99ee5707b21bc372040000207700000e690812c73004c018a000000000f067d962990966c2b56134819a8928a48097900e65a44f6438c0fe00003d8f324b2ac182778d8413d000000000708fe804731789d067200e9067bc134000000000041e040650000090574000000003025e5a86a0136706c8000070670c1dba0144804f90525c1ebe0a20806f80a980000405cc000076058414e2059dc230b0a394a48e6007c481908500000000038120c005081a10000219c8c0703c29de0528001b773a0822ec17c2caa3a466dc0440062599d9d04200000901e2c196000024121000680000701b8c0b0939e9468ed0969c9500000081a070009458a10a680000b16b7a1a251a29096df6734818be651e58d00000289c76094581aac0aaaa156e064d5cd0805598276a663541040000158dff6041812b8676800003405241c1b0873456590a4bc24300003c102903c002b0a1770199bd026400003187e41e2d090800005096c417c0000000005298f00bb914cfc0faa08f400d7e69a38077f04b40000a08d3828900003e5e00000102c39003cc0ae89078000060536dac5617018056e007d02c660460000000002416a00003d8b0000014088020cc0000000000000e0a0dc0a900000425fb745c00002060e0205000012a72b074ac07420b2bc22821afb000700002c1e100002413b000000000a04dc00000000000006084601d101a88400b29a579a5210275806bc62d6c080f262c8a04b083c00004085f01910438800000000244d701050002c0e2c06a050000406190c000980a018040813008048203090040e061380806050480014035301412040e0600202040005600031542c020782800200106c29130c0044a05000090a2b0e00c94000600c020900810040a0302406000180c180d078148c0d0686534180d04442002081012010e0d0360104090040208818080b0080c0204050047c29068047a17072581409008081a03158001e100487086010105000032c804a0000683802033500c040701828000001804080007a887a000080c3c121284032000d8080c1f031101a02008284a03050000401031002603030181a01018740a07038240a0213808000b0589c100a198903c0a060180a021184402000104812000302cda1305854200d000840a0400020120a020000213010340c04050445004020000e08000146600018283a000080c30080505800061d80c0002050180201 else 0x34212208100885c49cb00d256aeb0106609e800000000000009a6f1c29e102474085000000000000028d2eb01d4000066a919a6a107d16247d7090c0460000180efc08040000108908001e15250050000029914a643c00006062000004004bd12ed61ebcaa8f07c8829b401f102a50000002c100000c0310000000007010101e7a05ad80df4073202a7a0107811480a29810d00000000000000000080ab0c11739759ddf20052342be60a63410e7046b00ca0000084a729090000070b1ec177d0263426a0000181f9467b40000471c140cebb7dc589bb133d591d603d54068705840000000000000407ec8164b13ad2ac8f04c5997550aec4471000000000b01e8000040afcc2440000141ac00000d91a93a555ce547a7c0073707b801d8c04550146000000000c071140b6602300000262768225d0079819ab07e8000000000da7d00000000040940000000000816f06250422900003c0e880178000000000000090665c254b654cc181000025ceb00001401ca64e814cf301c24691600b8015cf5789c1f30000000acc34ddcaa2013da0213005db5e396772c403d80123025220228000000001d20f5037704c5377d4403e0000000005074c0000391c000000000385cb000021d7e808c40000407f0000000000000000003c10c000001a01b04ff01c800000000000001a196b60c4c1e9366e0c21f90018000030024c04de09a4868957727859ee0365419b0000381d9e0206c155f611800007047bc169228440000613880000709ae05e800003c1bbb058b405800002c00e8009b1901000000000e024000000000040de26a7c0000516be416630a340000c2a30000000003597470ae7cddb404e5805f5039c8094706bbc45ee3a1980eec22ccc21d00642015a4668880e9005ee4063d00fc0000f0564000001610984ad0089402c801abc13c000000000000000000a065f5e4d8054f05f7a08294227242380000e093dc0cdd05480000305bbd05c10a580000d70a2022d00000000000003826c573f7812c904000000f61a0000000a7dc0059022f41d652a9a011b00001823bf0300c200c0a1999db541988079f08e124c151857c2715069ded6a975d12e72709338261602df8447804a844bd801240000501fbd85fa0972827000001c247f73500000c040c000000000002a509e4c09201a540000f06fc00005146f0dd0000000000b0013c299000025c36a008d2467404a48122312dac2b6e79fd42ae208f0412f30428e0f116b37da9de36380000217284021f857f58c10000001af20324000000001c2749093a423a36258652e902e40000b6830208080ac782077019711e0f63580000805081caa00157022c9a6a80255400a00000003a8d01a6051ec1ecc745641ffb07080000602fa413a0000201ddc00a5823200779588f70af) else (if i<3 then 0x700000c03f00000000021e90900824291006480000000000000360e00000e014e8ce28032ec1f000ab40000a000fdd123052e81431019800000000180450000380e08088dc27f6016a024de00d8000000000c0f8592e40000b05ff01be7190d0401a048c0a9de06ac0000e634bc0ff671eac1a64767ec0ebe0a8489aa318a7007df27efc2cbb0176425d67310d887000038165000000000d0a72c16cf6162d8555012e406d37a880000f0181c617400f129b8302d6995fd06c30030201c88ec20b306596ef7713d8ff3789b40d3000000095661f301e48a33c0000a6b0b404e969af90b930065c0b2e4339c19d0000281c7000000000526fe1a2680aa4800c000000000601a70264708ac81ad10905c4d9525ae1a3e71297012ed4aff4237f057f811900028199cf04a08a951014b406cf07c70226a03e782afd430741d4209dfca3d7027982876005ec8b477527c0b1c176d1ca7c09f545b9d151b40a510369822ac081842c0547bf569400a3151f7000b48116501c7c20326194000071ac542ba48a7501d570a8a00e24035bc02f3075e4285614838127e0a1059e9c094fc00d6125c9e9ba7493426fe2902c4214127cc956907d7011c0000180a2713f810247684b09dcc03da1ded80360e1c5d08cd594f50a5181a5a056341f6002ab58300083b40f173666121c90a0b619b41622026d4a22700a654212d83af02d0000081082c064206300000a092f82c9c1a7bc144506d09c69907685dbb5098321b8b1582c40220188851230226580ef11d245d9c1199527f205c1012416644822250a5d4215a00edcac2e15bfddd6c0af5420d9021a1a6c466aa81cb156b58054563f54067e572cde40e004600c4e068b416da63810561906038059d09021a9c6058dc27e117968651a055d411db042785c71763b018e205f601548179800003aa7400000000140839274581e8706c481df109c80a22006600000b659a5cbaa0a0581fd50714c235000031019000005a9712b23c1f7312d00000d168e028f709f00000c16c00000f13535da700003c186802115ce9a0867c500579e95eb9a76c50130000000000000000000000028236916c4c0fdf68b08a1af6929d85dc04c9c0e5ab83d421be04ce9e1ff9068850756013457417089c0d54261d4246c03d0c0e1861580000a063581a8000034076d01fc0000c24c00000c05c60113905fa00dbe64e042a0f028d41a4d136802a311a60198f4047f452ce0b4780ab0000245b4909cd4018772109a0b5031fc5667122400dca086b46c200000808d000000000d074291d6104e1c15142629c2b33082fc15ba28df40bfa0238000040825c0cfb186c000090292422f60b35c1cd9023d00c60098942165bb08ca539624d415000001427bc80e31489e183fc2b2213058160567de80c25645d401d50393c9a20000186b else 0xf7a095c000000003809ac009dc957f05d559980000341c9000020293000971dca803140000700ce028b767d0c19e00003c1b9306f008c700003821e909b80000e038d8221a222601400000342cc000000000000000000102cc000028b1e5a1a0000240bca0808014cc0a000000c270b59df90a5780ad0000041b3e26e0c087b030dc172a049941fe8072ad8c7d76f0000000002c15e50b100000703b0000060b425d5eb0b3d80a7378aa81a3a521581f8c078e4263f05d1009f100de00d0209295d46a26f082c2f0398409b305e4000030a90000080ad285ba741c00000d19158111d05e800004099cc0000000141bd906a798f6a0aac447ca0448e033e63c55a40270691e11419e6c2a8c061242493691f010b90b3a45a6c09a04218f035380241660dc24500000000000003004a715c2c239760e581ba514f7407b8095842c87043f042b20996454ef0406501e000000569060f00000304d0023e345d00000823c40000000000000307a80000c626400000000140fb00003c6bfb06d44034002e900c1f041f00a80000100100000000bd8079bc5d2672e48493f0615c0a1766de182e907b700ed90131624200821826600003c18f4061edaac507380000500c800007092241c307679002bd0a40419507064ddb8965280000000018042107bc0000612089d296051640960000341cf00001416800000c0af9a5180000a61e3c485268235879e71bc0082e102bc0f2879ac0000408409850300d6c043279c94125968))
def xmd10 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0xffc1216153148130afb9c42e95148130cfd8a06cca254530c7f9b06a4850853087fdcb214a948530c6fdb66a48508530ebb980615a408530ffc1314811048530edd953481a720530aef9c6284a5481308ff8ca6c0a254530bfc9c2281a354530af3dc42e1a508530ceddb668ca254530cbf9ba6058048130ff4953548a948130a7f9c9541a020530e6f980655a608530aef9c6284a948130a7f9c96e1a008530cfd9c32e951481309df9c72e93148130ff4953549a848130cfd9536e1a008530afe9c56892020530d7e9526c0a264530c7ddb968d8008530afd8ca5453148130afd8ca6c55348130e7d953601a908530a7f8ca481a564530eaf985601a608530afb5c1215a408530c7bdb96905220530c5fdb969d8008530ff61524412054530cfb9b46a0a548130cbf9ba6018524530eb79a560185245308efdc62e93148130afe9c2280a254530bed9c62e93148130cbf9806e98508530cfd9b36a0a548130ef69a55492024530cfe9c22e95148130a6fdc6289a954530ffc1314858048130cef8a06d8a254530ff49534818548530dfd1b14c4a8481309ef9c62e95348130dfc9b3480a548530cbf9856e1a008530dbd9536e0a148130cf9db468ca254530cef9b06988508530ffc131484a548130cf5db86cda5085308ff8cb6958024530cff0ba6055148130afb9c4281a954530ded9536d8a148130cfd9b068ca254530ebd9a854d8024530a77dc92e1a508530eb79b8601a508530e6dd53661a608530d7d9b3644a548130ffc1204c5a548530cfd5a36c48508530fbd1316058048130cebdb6690522053087fdcb6a52020530cef5b169885085309fd9c56cca148130def1816d8a148130afb9c4281a354530ffc131480a548530ceedb26988508530dfd1b14c4a548130ffc1314858248130a7f9c96d5a008530af9dc42c9a3145308efdc66e88508530ded9b64c4a548130df69c26d4a148130c7edb96892020530eb79806958508530eed98054da608530df59b554ca848130ff49535499548130a7f9c02c9a914530df59536d5824813087fdc96e98508530cbf9b8688a054530dee9b6484a548130c7edb56899220530c7f9b06a48214530aeddc62c9a354530ffc131480a948530ff49535492024530efa952481a420530a77cc96e1a508530cfb9b4284a548130c7f5b16a4850853087fdc52e98264530dfc9526cca148130ccfdb76988508530df59536d4a148130cfb9a86d0a148130c3fdb96a15008530dee9b6548a148130ee5d8554da608530a7bdc4289a954530cf78ca6d4a148130adddc72c9a314530dbd9b84c4a054530af9dc42c9a354530ef9953481a420530e3f9a86019524530df69c56c8a054530afe9ca5492024530ffc1214c59548130af99c4281a354530afc9c2281a354530ebd180605a35453097b8c96d0a548130 else 0xffc131484a948130afe9c2281a954530aebdc6215a408530afd9c02c9a3545309ef9c62e93148130dfc9b3484a54813087fdcb615a948530af79c5284a948130c7f9806d5a908530afb9c0215a40853087fdc56c9a92053087fdc86d4a948530a7f5c1214a948530cfd9a36c08214530dfd1316c58248130cbf9a86e120245308ff8cb481a354530efc9536892024530afd9c8481a314530cf5d526cda524530a6fdc8655a608530cfd9a86cca148130ff4953548a148130efc9536892020530c6fda96d85220530ae7dc62e1a508530ff495254ca848130afd8cb481a354530c7ddb968d2014530ff4952481a354530dfa9b4484a548130ffc131485a548130ef598554da0085308efdc62e95348130c7bccb649a4205308fdccb609a354530e7d953481a920530abf9c8280a25453087fdca6e4a54853087fdc56c8a960530afd9c2281a354530c77db96955008530abf9c8284a948130fb59536018524530efc920689a354530a7f9c0214a948530e779806959508530c77db86959508530efd1812c1a354530e7e952481a944130af79c02e1a508530e779806e5a508530af5dc32e1a508530abddc82c9a314530cef9b62a4a548130d7b9b4644a54813087fdcb601a94853097f8cb645a848130cfb9b4688a054530cef9a06d85220530df99536d0a148130afd8ca481a354530ef4d5268d2054530c6fda96d8a1481308ff8cb6952024530af5dc36958524530afb9c4280a25453087fdcb6a52014530a5fdc5649a720530afd9c568d2020530ff49535499848130cef9b66a0a148130aeddc62c9a314530afd9c22c1a35453087fccb649a354530efd0a0605a354530df71816d4a148130c7bc852e5a408530c7bccb655a408530ffc131485a848130ddd9536dca148130cdf8a96dca148130cff1a06c4850853087fdc92e982545309ef9c62e95148130c7f9b96812020530c7bc522e5a420530cfd8a96cca148130a7f9c8655a008530a7f8ca481a864530cbf9b86a12014530e7b980655a408530cef9c62e95148130afd8ca6d531481308ff9c82e95148130dfc9b24c4a054530c7ed826c8a954530c6fda96d8a548130ffc131481a048530cfe9526e92020530c6fdb9699800853097bcc96d0a254530a7f9c9601a0085308fdccb68d9254530afe9c2281a354530ffc13148592481309fe9c26c4a548130c7dda96cca148130cfd9316e98048130cfd9b32a4a548130c7ecba5498264530afd8ca5455348130f7e1214813164530dfa9526d0a148130a7f9c8481a914530cdf9a86dca148130c77da96d4a148130a77dc86e5a508530e7d5812e5a3545309fd9c32e95148130ffc1214c4a848130d6f9b6644a548130ebf180605a354530efc95268d2020530cef9b66a0a548130c7dcb96c9a354530c7f9b06a45220530dfd1816cca148130) else (if i<3 then 0x97fdc36c8a954530ff5953614a148130c7fda96e0a548130aff8ca5458348130def9b6614a148130ebeda85498224530d7ed526c8a864530bfb9c4281825453097fdc52e98264530ef5d526a15324530ffd131600a948530df6d526d53148130a7fdc52e1a9441308ffdc82e92054530ffc9532e92048530f7e952480a864530aff8ca615a848130bf9dc42cd8214530dfb5816d0a254530aff9c82e95148130eff181284a548130ff4d535498224530efe9206a1a254530cfdcc36e98214530a7fdca6099524530b7f9c0215a948530c7fdb8688a954530a7fdc52c9a944130dfe9c36c8a054530e7f985655a008530dbf9b8484a054530c7fdb268ca954530f3ed816093264530efd8a12e95348130cff4ba60592545309ff9c82e93148130df79b554ca148130e7eda26099824530ebdd53609a82453097fccb549a864530e7ed522c9a960530def5816d8a14813087fdc96c9a52453087fdc96e8850853087fdca6e4a25453087fdc96e88214530cfd9b36808508530ef5552605a354530e3f980615a908530cbf5a86c48508530ffc131481a948530cf75a56c4850853087fdc96e85220530fbd1316058248130fbd1834c58060530ef59806cda508530ffc1312e92048530ebd581609a354530dbe9b8548a148130a7ddc36959824530ef9953601a408530c7ddb868d921453087fdc86c8a954530df59c36d4a148130abf9c8284a54813087fdcb148a960530fb598554d8008530c7f8c96e98048130cfe9a26e120245308ff9c02e98254530e3f9956a1800853087fdc96d5a008530ff61526055148130c7bd522e5a420530cf79b56a0a148130d7e9b2480a564530fbd131600a960530cfd8c36e98048130c7bd852e5a408530fb65526058254530ff49534815220530ff49535492044130cfb8a56d0a148130a7bdc9615a408530ff49522e9534813087fdcb208a954530c5fdb969d5020530ffc1212e9314813087fdcb6a19214530cfb9c42e95148130df99b44c4a548130ff4953549a148130ccfda76d85220530f7e1205452164530d7f1b1644a548130fbd131601a960530afd9c02c9a31453087fdc92e98548530ebd9536a18008530bed9c62e95348130d7e9206d52164530efc920485a354530bf99c4281a3545308efdc62e92054530a6fdc6214a948530a77dc96cda508530ceddb36988508530ffc1315412048530c5fda96dca148130cfb9b0690522053087fcca6d58264530c7f9956e1a0085308ff9c06e885085308ff9c06e85220530cfd9b36805220530afd9ca4c4a054530e75db3661a5085309fd9c16cca5481308fdccb609a314530c3fda96e0a148130df99b44c4a054530ad7dc72e1a508530cfd9806cda5245309fe9c26d4a148130cfd9206cda524530afd9c0609a354530e7d953661a008530a7bdc9215a408530 else (if i<4 then 0xbfe9c22c1a254530cfddb36a0a548530dfd9536e0a148130cefdb66a0a254530dff1812e95148130c7fda96e0a148130ddf9b760ca148130a7fdc52a1a264530ff4d5254d2048530e77d856959224530ff5953615a548130eedd8554da608530e7ed52289a5645309ff8cb6059548130ef79b8601a508530aff8ca601a254530dfe9526cca848130ffd1315412048530d7f4b96058254530dfe9c16c8a054530d7f9b9600a548530a7fcca615a864530ffd131600a548530dfb9b4484a054530dfd9b54c4a848130d7edb2608a954530cff9b8688a054530d7edb2608a564530c7fcb96a1a548530ff71505458060530cf7da56c98524530ff69522e95348130c7fdb56a4a948530afedca5498224530c7fdba2e99260530ff71815412054530ff65524418254530dfd5316d4a948530bfd5c12cd8214530c7fdb2604a954530efd5316a0a548530f76d526455348130efd9536a12024530def9c26d8a5481308ffdc52e99260530e7f4a9605a354530def5816d8a254530aff9ca484a054530d7f9b5644a848130a7fdc86959224530f7e9204858364530dbf9c36e0a148130d3fdb96095060530f3f582604a954530ff5953615a848130efd8ca4c58048130eff0a0605a354530aff9ca5498024530dff0ba6053148130f75d5254d9824530d3fdb8608a564530d7f5816e4a254530d7f8ba6152064530aff9c2281a954530c7fdb26a4a960530d7f9b96153148130aff9c8284a948130dfd9536c58248130bfd9c12e95348130c7fda82e5a254530ff595254d8024530f7d53164980605308ffdc52e93148130def9b660ca148130efe9a26098024530efd5a3604a954530bfd8ca6c55348130dff1b1544a848130fb79806155344130dbf9b8688a054530cfdda36c8a9545309ff9c52e98348130c7fdb96a120545309ff8cb601a254530ddf9b754ca148130ffd1316011060530efe920694a948530ef5d8554da008530f7d5312e99260530dbf9b84c4a054530eff0a1604a948130a7fdc52e99260530dfb9b44c4a054530efd5316a15048530d7ddb3660a548530df79b5544a848130dfd9532e98348130ff59536152044130bef9c62e95348130c7fca96d5a948530ffd131481526053097fdc56c8a864530dfe9522e95348130dfd5316c98060530cfdda26cc8524530dfd5816cca14813097fdcb660a54853097fdcb608a564530dbf9856e0a148130efd8a0609a354530f7e5316612048530cff8a06e0a254530bfd9c52e93148130ff59535498044130e6fd85661a608530e7dda254d9824530df75816d4a148130dfd5316d58060530d7ed526e0a264530a7fdc8255a908530ffd1814c5a548130a7fdc82d5a948530f7e9204855364530dfb9b4688a054530ffd131601a548530dfd9b84c4a548130cfdd536c9a824530a7fcca6095064530 else 0xff692054953441309ff9cb544a848130efd98554da008530c7fda86e4a2545309ff8cb6015148530f775526615144130efd8a04c9a354530dbf9b860ca548130c7fda86d59224530ef79a56152024530e77db8661a508530dfe9b24c4a054530a7fdc8295a264530dfe9526e13148130efd9536892024530a7fdc82d5a908530def9c86d8a548130cfbdb46a0a25453097fdc86d4a264530c7fcba6553148130efd980485a354530ffd13148580481308ffdc26e88524530a7fcca549a564530e7f9a26019524530e7eca2549a864530dfe9b2484a054530dfe9206d4a948530dfd5316c8a960530a7fdc2295a864530c7fdb86a4a548530dfd9b3600a548530cdfda26dc8524530efe9a26152024530bfb9c4281a354530ffc953484a848130cfedca6c88524530c7fdba2e98564530a7fdca4c8a954530cff8a16e0a548130dbf9b860ca148130efe920689a354530e6fd85655a608530c7fdb96a0a548530dff1816c0a254530a7fcca549a864530bfe9c2281a354530a7fcca615a5645309ff9c56e0a148130dbf9c56e0a148130ffc9212e9534813097fccb609a954530cfeda26c88524530ffc5314855348130dbf9b8600a548530dbf5816e0a254530fbf1316058048130aff8ca481a354530cff8a06c9a354530ffd1312e98048530dfd9b84c4a054530cff4ba6053148130dfb9856d0a148130f7d531648a960530dfd9b554ca848130ffd131601a048530f77552604a954530dfe9b5484a848130af7dc82e5a508530ef5da254d8524530ff5953615a148130d7f9b8480a5645309ff8cb605a548130ff5953614a948130a7fdc26959824530dfd8cb54da148130ebf9a26018524530efd9a254d8024530dfe9b8480a548530dfb9b4608a548130ddf9856dca14813097fdcb608a954530dfe9526c4a848130cff8ba6013148130ef6da55498224530ff59534818548530fbf180605a354530cfdda86cca254530dfd5b84c4a548530ffc95348582481309ff8cb481a354530cff9c82e95148130dfe8c86c8a054530dfd5816cca254530c7fdba6153264530c7fdb96a12014530ef5d8554da048530cefda26d88524530dfd9856cca148130ffc9524c4a848130efccb36898214530ffd1314818060530e7ed522c9a944130dfe9b24c8a054530ebf9a86013214530def9b654ca148130dfb9b44c8a05453097fdc82e5a2545309ff8cb601a548530e3fda86159508530ffd131480a960530ebf9a85498024530f7e9524818364530d7f5b2604a954530def9b660ca548130efd9312e98048530dfd5316e12048530df79b5614a148130d7f9b8644a548130ffd1316e98048530aff9ca61520245309ff8cb54da848130cff9a26c08524530ff7181545a5481309ff9c52e93148130ef5d536895224530cfdcb36e98254530efe9a85492024530))) else (if i<7 then (if i<6 then 0x437b66ec8dca9b6c36866c98d729ac835566a38d209a24340e6778ce099a432c66518c94990c31de6318c4e987430ae60e8c0e97f42fae5eb8bce97802ec65d18b94970c2dde5b18b54968c2cde5918b14960c2b3655c8aa495202a065398a6494a0291e5198a24942c28064f989e493ac271e4dc89aa933826364bf897092b824d6490891291fc23be46d88cc917c22be450888c90fc21be4308852907c20be410880c8ffc1fbe3ea87ba8f581e763c187748ec01d463a1872e8e401c4637e86ee8da81b16358869c8d04199e32c864a8c8418ce30c860a8be017862e385be8b48166e2c685788ad415562a085328a30142627484da89a4132625a84a68930123e237845a889810f6217841a88180fae1d9839e87140dee1b6835e86a00cee196831886140bee17682e485a00aee153829884cc095e124823a8458087610481fa83d807460de81ae8340062e0be816e82c0051609b81288234042e07e80ee81c0034605e80a8811c01b602680268000dbf9806c8a960530c7fccb6a55260530c7fdb56a4a848130afddca2cd8214530ffd1314818548530e7eda26099524530d7ed522e982645308ffdca6c58254530a7fdc52c9a960530fbf1814818254530ffe1526053148130df79c36d4a148130d7f4b16e99260530ffe181548a14813097fccb6458254530ff655260582545309ff9c82e95148130cff5a26c48524530f7e952644a848130bfe9c22818254530d7f9b5480a864530df79b560ca148130df79c86d4a148130e7f985661a008530ff59536152024530dfe9526e0a148130fed9c62e95348130ef79a56018508530e77d526959824530dfe9b8484a548130def9c36d8a548130dfe9c56c8a054530a7fdc8484a954530aff9c8280a254530c7fda86d4a264530cfdcb36e982145308ffdca6c98524530e7f980615a9085309ff9cb281825453097fdc82e5a548530aff8ca481a254530cff5812e92054530ffc92054da548530dff1816d4a1481309fdccb609a354530ffe1215453148130c7fca96c9a960530fbf18128182545309ff9c82e95348130def9b6608a548130b6fdc6215a948530a7fdc22a5a954530fbd5316095060530ffc5314818548530a7fcca5499864530df5db554ca848130efcda26095324530dbf9b84c8a054530c7fcb96e98254530dfe9c86c8a054530df75816d52054530ebf9812e98048530d3fd856e0a264530cff9a86c0a254530aff8ca6013154530ff4d8554d20485308ffdc82e99254530aff9c2281a354530dbf9b854ca148130bbf9c8480a960530ffd1316011048530c7fdb8484a954530ebeda86093214530eef985601a608530a7fdc82d5a944130df5d536c98524530dfd9536c4a848130ef79a55498024530e3fda86099524530c7fda26d59824530f7e9206458548530aff8ca4818254530 else 0x380a93c08c300cc05c048be0461806602e0245f02015f00033017012301b00481ff8100a00e9ac60d8a4b10f61aac26d830b03f5fdabecd7b0af275daaba6d724ae0f5baab66d6a4ad2759aab2cd648ac57580aaf8d5e0abb756faac4d578aacf54faa90d4f8a9b7532aa56d490a8cf512aa16d3f8a7b74eca9c4d36ca6b74cfa990d304a5e74b5a962d2a8a5174a1a934d258a477484a8f4d1e4a38f46aa8ccd17ca2bf44da88cd114a207439a86ad0b8a13741fa836d050a067405a808cff49faf3f1a7d4cf809edf3d4a7a0cf249e0f3baa766ceb09d2739da732ce489c6f383a6f8cdc89b6f366a6becd6c9a9f349a67eccec999f32ca64acc9098cf318a628cc4c985f307a600cbe497a72f0a5cccb7096a72d0a598cb2096072b9a56acaac9507296a52aca38941f27fa4eac9d0934f262a4bcc95c929724ea48ec91891df23aa472c8c8916f226a438c86c90b7212a422c81c90171fba3f4c7c08f471e4a3c0c7648ea71cda38cc7148def1b6a35ec6a08d1f199a324c6388c3717fa2f0c5c48b7f165a2bcc55c8aaf14ba28ec50c89df137a266c4bc8957123a23ec460889f109a1fec3d487570e6a1acc34886570c3a17ec2d4853f0a0a138c254846f086a104c1ec839f06ca0d0c18482e7055a096c10481e7038a06ec0c0815f027a040c064808f00aa000bfe47f8efea9fccbf7c7ebefd39f98bf147e06fb99f6abec47d4efa29f30be387c4ef829f02bdf47b96f6e9edabd8c7ac6f4b9e82bce87996f289e3cbc5c787ef0b9e08bbf477c6ef19dd4bb9876f6eda9da0bb247626ebd9d6cbabc753eea39d32ba487456e839cfeb9e07386e699cbeb9607286e4c9c90b90471fee3b9c6eb8cc715ee219c2eb840702edfb9be8b7b46f2edde9baeb7406e46dc19b6eb6cc6d5eda79b40b6646c8ed8a9b0cb5fc6bd6d739ad8b5946aeed569a9eb5206a06d3c9a64b4a06906d1c9a36b45c687ed089a08b40067decf499dab39866f6cd799a0b3306626cc09972b2c86556ca09932b2486456c8098ecb1bc633ec6098acb13c6226c3d986cb0b06126c1a9820b024600ebf797daaf8c5ec6bd19794af0c5ddebb19748ae745caeb8e970eae005baeb6e96c8ad745ac6b519694ad0c5966b229636ac505806af995deab4c565eabe9568aab45486a899504a9e05386a6394b8a948523ea43947ea8d4516ea239438a82450269fd93eca7a44f0e9da93a0a7184dde9b4935aa6984cde9949320a6184bf697792d4a5804ac694e928ea50049c69319254a48048c690b9208a3f447ae8f191d4a38046c68d19194a30c45de8b49154a29844f689a912ca23c443e87d90daa19842de8519094a10041c6831904ea06840968028ff69fb83f367d68f9e9f143da67aa8f409e4c3c467818ef49dcc3b5e7618eae9d403a2e73e8e689cb4392e71e8e109c0) else (if i<8 then 0x6101880b80a8c02c05440240662a04014019180ac4380901d100480984093e03e000340285014012100681880b80a90054048401a0439140500245051012100381980f8c0c7c040500480d8a02a0640243f000140121d0278080900d10c100480d8783c03425080121019009080540d8402a00e0323f0004e01219840090bc000f805460a602a2f00014012181f8090815c048400e0242031017012f02f0104750c3b040090806807c048660802406c3012033138000a0090c084034048602404c200dc8a700028012282880908144048402a02420ab185f00d0001501935818090814c054406202e02a3014015101081b0bc0807fc0781fc00a04c0242019015100901d0807c0485e000280243f0004e01218000130090f81c04840100242026012101f80a00a8c0c80485a040640243012098400908050064402802a2014021100901b0802007c4e000280243014012100a80c880c8048401202406c3032012100480a880c405f62005004bc0bc0407f4a93a00028074300901203a1b800130090c054048407e02a201205510108068090c05c2c080240743034012138180909c0005004860640242038017100a8090805c050540e0242015021100a80c8ac0c048403a0622007012100970380a8fc0bc04057c0007c050c41be02024398701215038288090d078068540004c0243015012100a01b080540485808032202100d012180901b08098048560802a2015012178020480c8c02004846100242f000140121819009080500484157e05a06074402101501f019200a80908054064402be000880324032012100900681b0c0c4054402a0242d00019015180a80908098048401602802430320121215f8001880c92c0c04844120120243015f000121f8078086300a100372280a0048803e06c2015012100904054064401a0160500244032015160244380a009100fc0484a07409e03e0040150810f03f8080a10064202a024202101f0121d8200a8bc00138048780803206c3012026100ff8000680913c0bc005b10e00a01b0e024501f012100a84048260004c0243015012118280a880482a09b1002890e06c5f0003e015180b8090805004840a20242f00026012180900a8807fc0781c62bc00a06202e213b11e05e03b0e024a549f018870121f800130090c05c048402a0742054015102980a8bc00098048602e024260401203a180400a88054048402a02420150e8001880c8fc00050048601202a0743032012101881080bf81780009780823a0050064401002a2032012100980a8827805040258080743015019102200a080fc084034048940004c0243014031100a80c8bc00098048603e0242703012102a00a8a81281c07c064802404c2032015130200c8814c054402406c200d015100a80908620048402ed140743409009019180a68024 else (if i<9 then 0x180f80900b8c0503a721000901b0805420241043388178000a094140a440240662987f000151c0480a880500cc5e0002427390e838090bc000484028101f014100880f88050202406420120b03840cc050531002a2018036012180f9c3f800e81c202804220703840d14000487a081006300b8090c086623c00603450fe0003e401f015e0718c280a8bc0004840312000243014f00012180900a0807c050480e1014021100f80908054320e05220150121105040f00545c0e1988f000121e8200908048202a0262012409100bd80880480605c0e101450001218188090807d81c402402a20280e4380908054124402f6062015f00012180a0198805cca8401210140f0380a88190e1e070c190405c07c4029e000323809f000121e440090bc000a4048602a06c0243012014100a0108b81c050406202e2b0001217800108807c05459100242305b000151cc2840d804840241034f0012080090b21c048402804220150d8081b0b21c202402e201a409100a00908054048580802a2014021101080d0805381c40421034f000121884b800090c0500cc55101001b040500cc4028042201f081a040502028042203601210108090b010048402a024250401217800406808442201388043100a0198807c0484611016024301201712839c388057800404202a0343015f000121f038090b81c07c5a00024201a409012180901e08e1fc000a4606c024205101210000130090c0c805440000280243f0004e012180b80a880540485e0004c0243d000140121f800130090c000050048603e02a2010015100a8090807c0d8406202402a3a04a0701f01924c280a88054048401602a201d01f100f80908087010064608a0282021026012180f8090804820120242108012102a00a8808405405fc0bc0004bc04ee0208e0743b0301210158090bc04057c0004bc08424c8120242c8ac8701a1c08a1580a80900bf8178080ff80240c4064415660a02a032401a00d0191819009082ac08405e0240c7c0bc07c00049208a0282054015114380f80a0c0c8048407e01a0500244017012100f80a80c8fc00050048602e10120e9cec38090c14c05440000280243015012100d01080bf8080a78018064202e0322012036106378000a009100a406840a802a2f0003e015181300a0090dc000500486a0e024204401410088090bc0013804860120242012081880901b0c060054402a0242015f0000d014238000a0090c0480d85e0004c0243012015100e81d08048054402a024230501510058130090c0480d85b11a000500244026012100900a8804c0e840321057012178000a0090c020048409c0242051012100d010880a40685e000242009c8703a180904050054402410120809013080c8048460602a0243c0401588701f019280a809098000500487e0004c024303102 else 0xf02109f000122781780080500cc404202a201f88716800090bc003e000240503033029100f80900b8c07c054403e029c0e300b01515025038090c048424406204220140211304f800090c81c203e21202430340f038405381c460b01602a3015081084121002a2185701d0001525020781c203e0620323012017164500d0108c0cc0a45e001021028100400a8808407c048603e028201f987100af800090631141121c402bc0e024310d031017180a8090a02c204206c2e07012100a0108b40020240282012080a009080480504040901210090407c110421202403e308af00012183c000484024030200d0c0480908050084421203eb0e301f021100054203e0282f00098400a88050084402a0282015081980c8b40006840240282000a106880480e840261305012100a4800090c434360002420120f038090810c440481202a2018033100bd8188050084402a024201f08258090b81c206c0280243014021105580a0090c05c202402a201403a168006623400530ba72032301f012017180907c00054403e0282014021101827c000486052a0818240e84e721015387100d0108810822121308b00012180a2800090c05c0485a7210120e800405381c4029c0e2604081880900b8d827c000487e000240283000a8108bc00048084621a101f987f001800c405c0487e0018c201a080a824880c420281d04018100053c00048600015f800b81c3e00024201ad00019183c0020241001f80a0108e81c203e0242006302b0090c0540e8403e1012080c00908054203e0242f0001210005c048402e0242014021100a010880482c13e000243015e07100a84050084402402a2f00019100f80908003e029c0e3700012100b809080211a000243015080c8405481c40301e070d43840483c0e02a2a07098180a88068203fc0e0243f0002901218c57038090c07f81c054603e1031017015f0002828090405fc04402408420120f8000a0090c62805781c04880280422607080a0198804a0245a00024202609828090b4000645c060242031098268088054202510e2031015021))))
def xml10 : Packing := (722,5,7,0,0,15,0,xmd10)
def xmh10 (i : Nat) : Nat := 0x30a24424fc282c1bec2100001818ec0b80001405e82050131dc524139c25bd18a01e4c21bc27a81795897a0fac1ad9a8d05c8980941f059f6001f021e41f480db411cc12cc1d289a4410941fb8075c00d0011812b40575d0f41a5c1ef018800000002e58a054c0167c1ba4116095a98680003423d0168c25d0293c477408980e6902800000a43d97400000003d9950154d93800aac145c11800000001c07f49179d38000000000000000181c40003804ac1b0000301c981a200ac4a1c1dac0059c22800030260c2440000c17140fe40c080b1800b413dca2ade5c44cb00ec0000c23b410c000281d8003b423780849db4000000000003003cc0d0513c000140de899f009e8251c5e400038d114287c991057949aac24a098198240001415d016de0aec5a3c20b40700001043fc0fa01580002528654c2c14981d40003c277c22fc02061ee455900b6c27c0036026c00014181c294410208c1423000018127c0cfc08ec05145b80000000301c1c27040e1406e4135811280040001063c000341a880a40142c9fdc0979a05d01c000248ac40d605ffc217c02d44c388f0d0b240f79dcdc02ac1500002c2214192a210014f804e4198c1940001209fc12000000000c26b81ce984240f2ed3d59a10093817f889f614240c48104000281ff441c856800021a65c033420000000001c227186c0000000000000002c00000000000c0bc00018821c20d81b540780001c0240003099800000000428900140001c0cb001941e298f6828f91500000000341ebc045c2640240000000410255809a49200001c0800000000000a2817681620660406110079cddc0e8c1de1a1c898ec9e3019e6d0cc06b01858064000045c58c010faa86960c04d71140111052104760000493430290c406f0032832c500a7c804140394a00e90009b142
def xmd9 (i : Nat) : Nat := (if i<1 then 0x409876f46e131600a548530dfa4a93825d2a690261dbe181721b2281514c39ee3026536a50a409853f5744c36e98214530efb0c0b8ad9140a8a619ef1c6604ba545204c2dbb3ae65262c0240986ef8605c22818254530b7f0e9140c0b46a8a61be6952718ba54d204c33eb2a6e2b7050a409873bc281816d8a254530c7ece43865d2a2902612fb9d432980689514c31dbaa6e317498a4098775654d856dca148130a7bcec194da94290261cbd9a36e132281514c31fb366e4140512a29877c654d856d0a148130c7ec50196c1346a8a61bbb181710a0609514c39f9346e4364502a29877f0605526cca148130d5ead438259b0428a618ff181329b0289514c3be9242daaa6542409847f6371536c58248130d7e4a9194daa62902615fc8db54d21609204c3be92a6a937050a40986bbc605c6284a948130efa4a9196a9b42902618ef9b6720a0289514c3b6b2a6c2b7050a409873f4281816cca254530c7dce43885d2a290261eb598568953600914c3b7a262c036454b029862fe729b8484a054530efa4a92a65d30690261dfc1216e131295204c33fa19698b00d2a429863fa721c22e9514813097ecec194a8a6290261cbf1802e9814c5204c23fa9b898b64c0302986ef472131480a960530e7e4d1b6499140a8a610fd8db7018268d514c3b692a6dc2a450a409853ce750ca6d4a148130d7a4e2aa4d1a4040a61cb5953601ba614214c33e92a4e2b6650a409878d661553601a90853093dc6cb885d2a290261af495232d2068d514c31f3366e2140512a29877d06cd526055148130e5acd9b70c034a10a61be4952718ba54d204c24e79b2e2170d2842986bd254dc56892020530e578c0b6cd414290261cf49a3715b2281514c2bf83a4d8a6252a40984be6750ca481a354530e5e8c0b50d9942902618fc9b3708a0289514c30d7972e310ad20429862be6d9c8280a25453083deee0a45cb4840a619f49c3709b5285204c3bf0242da26252a4098779254db6548a148130c7cce536898940a8a616f49d369552480914c357a302e0304d1aa29862ee6d1c8284a548130f52cc030aa9b4c10a61bec121718ba4c5204c20f7bb842972d2042987ac654d80615a40853087f4e9196d2b0048a616b59d369580614914c31d738cda14252a40986bd2548ca6c55348130c5ecd9b9050144a8a618fc9c3708ba545204c3bd8262db24252a409861ed2e5c1215a408530c5ece537098940a8a618eb9c4718ba545204c397a37498b02c02409861af325b66905220530c75cdb38850144a8a61ef095254d20690814c356b386c034ac28429872dc605b56a0a148130d7a4a938458346a8a618ee9b6708a0289514c31dd38ce1174a8a409865ea484c96d0a548130cfa4a9b84da9429026187b8b970085690214c3be12a6a936850a409863e6711c32e95148130 else (if i<2 then 0xc20170e6202007c000242000cfa02200a04000090400018806802e301b0402e01f10054024200fb21c40003e001206840241f80004840000003f08002bf0012e1c2000000170fc0018c2009040012080540242010807c032301f8048401908048202608048201201b0802e02610048201700a880241010805fe03f002004820190804820330802c201201b0802410090402410090402410198406c100f8064401201b08032100a80484012080483f00080482012080482012080fc024201304024100904024100904024036100fc0242009040241b800048401908048201208098201208048200901b080741009040741009070a709307f06b02300efc6f4aeceebaea6e92e4adcedbad3ecf6caec9ac1ec0abf6baeb32aeaa6ea26a129ca98290688a8427c674a70265263e5c25ae59a58650a4c24463ca3823062be27622e1e61d21be1aa1620e60d208a00dfc5fb1f01e85e3ddf5dadd99d85d09cf5c79c31c1dc09bc1badb99ae9aa1a259a992d9199058f18a986181979d78977576174d7056f167562d6196055f15dd5955194d14bd4753f93492cd28523d1f51ad1310b506cff0fa8ec4e7ce34decda4d5cce0c98c50c08bc0b78b30ae8a6c9f09a892c8e489c85480c7c477c7346b86706285e05985504d44584103c834c3042bc27422c1e419c1200d8090048003bdc302db2a450a40987f92549c62e95348130dfe090b8a5d262902614ef9d6285b8295204c3bf82a4d8a62542409877f06e131480a548530e7e4d1b86d9140a8a61af9982710a068d514c23fa9b898b6454b029876d654dc56e0a148130e9f2c0b64c1152a8a614fe9d2281b8289514c3e6cb04a930254aa2986be3689c42cd8214530df64e32425d2a6902615fe1d1321b2281514c3be9362a92a6542409867ba719522e95348130cface1b90da94290261af7181714a12a5204c31df390e3174a8a40986afc604ca4818254530c5fce1b70d1140a8a614f78db69552600914c28dfbac5d32a98a409863f668dcb2818254530f5a6a92a6c135048a61cfd1d32e981545204c39f63a85d302a8a40987ad6549a854d8024530fdb0a930250304a8a61afc5a2704b3608514c31f3b74e2166c10a29857bc758ba6053148130afb4ea990d9140a8a61ef49a854d52480914c29f3ba859b74c12a2985bb6758a12e95348130b7d8ea140c0b46a8a613ed9d6329b154d204c3bf836a98a4054a42986bb6758ca6c55348130e37ad4b02db142902611ef9d632d536a1204c31f7394da264502a2986bbc605c6284a548130c7ecd9b905d2a2902612fb9d432920689514c29f73a850370512a29873d6369c36d4a148130dfa4a9194d8aa690261afc9a3708a0609514c3bcb2a6db30a50a409877f0485b54c4a848130f7a4a9b44c2a4048a61cf99a36d132281514c3de92a450974a9a else 0x681340e0121800000a840012080c402e200afc0040003a08100a80844000b804840150fc0020f8000484002e1c3b01f800b600100b807c401208006c10090403e0361007c02a2b8007c0e01f1005c02420090402af000140c1988780080003c000242f038570f70017010024200b8406d98713c002031080482017080000090404201510002a100b807c5604080d1401700f8fc0e0121005))
def xml9 : Packing := (166,6,7,0,0,12,0,xmd9)
def xmh9 (i : Nat) : Nat := 0x3012016803e050817421e11000000348700e900181ac05c2a0000000000e4f000403009de0f9105804000642f06d024810646522a81c0808618800001201040
def xmd8 (i : Nat) : Nat := 0xd8012100001b04015fc00400d002e00f8c03100680171803410068017007c60000241003700004840005c0121002a0090adb68b1d425f0068af91e8a429c8da68239084200e3ac605c4718ba545204c3ae49d6548ca6c55348130e3e4605c470cba545204c3bb2152605c42818254530a6f43b131601b22a5814c24fc8ed68dc86c8a054530a3e63ad82710a068d514c28fc8eb68dc2281825453083f63b5a372ca0609514c36e49d6548a12e95348130cf9275952329b154d204c38ee181719c22e95148130b3e4790a0605b3289514c38bd181721c32e95148130e3ac605b6710a0289514c34b7181760ca6d4a148130f2d06a1b354981545204c30bd18136dc0609a354530
def xml8 : Packing := (18,7,7,0,0,9,0,xmd8)
def xmh8 (i : Nat) : Nat := 0
def xmd7 (i : Nat) : Nat := 0xfe0200485c2d05498136dc0609a354530
def xml7 : Packing := (1,8,7,0,0,0,0,xmd7)
def xmsamples : Array (Bits × Bits) := #[(0x6c49d13344fd5b2f789387edc433e6ca1cefe8fb5145f970fced8a79734cf95696fe4683802fcdbcbdd7060d210404ca20244554400082e840013bc000000a784c10398cc00b1801080fc64c4481d3200821075b3090d9a33c9401c73e21f673,0x22840e0050080a04048a4841c0248a4849494308001c00901100808020b000a1848440018c0f00240029104723c4150c24214112a8447491d110c19524104c10118c800b1801080946484481532008210253200091222c94000224212652),(0x6ef38714e1dddef86f2a796a1bdaec0eccea51acf93a08f13740fbafabcb12497726ac9f63b4e75f5f5aa466c9480a010221d4e0403880020000000403bf0a7e10a52610c040206430b2187c00061c3b30c6249c31632604c0ff66a4c8c6487f,0x81080021a0070260109101052102004a0490822408145ac100078c275100c80214582010180200d0181212002118c03062f34bd08c60430b800e08e02e08018e10a526104040206430a218240004081330c6248c10420400804264a488c44829),(0x518e3fec35f89391ff3d3bf9cac441fcab1cb04db2fbbd4c2358ae5b349e618937ad676400a8ee33b135343a58b8a9010c802080013150030000043bfd3b00000001c01f2583c181c13c6072081863c4010038e7c98c38470f188738f1078f9c,0x1084400211203411220618f2400100304002089912002004200001882290014121000406442980200080812400a23dc39808102f309c90946c900508c0050c500000800a2583c181c11c60520810028401001002898838470a18831071038514),(0x2897e568f7b29bb4e9b5af8c1e7c18f7dc36ac9e27260bb93c6f5d9f2cfd23552fe0e9254c852f3cc4eeaaf9ff9420244d020a03124640011e18003a58408480600607e0080c000601c07f8070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0x28080c216c020208183944001c02018428456040688b100b80100800056004a68082900822400c84c10a3051cb55022c24b5ce0089026d0b010e1a41145a902460000540080c00060000150070c07c003e0580f80407c03005e0502f00b00ae0),(0x2ede127ab7fe93e2c86e4e6fdb8b3e46b5fb1bb7a2790a74a1fcb8dbdba3568737edcad303a33927b543b83b7fb8008600020816004000001e193bc00040000380c7f80031f001f801ff800380ff8007c007ff000ff0007ff000ffc001fff000,0x95f4c00890fca996a4c00b45a3b01442401010b680244d006345408f2a01520062544b00198871203040c70204a0dc13ca4211de36ed12b08a6024ae2a204bcb80c7e80031f001f801f68003803e8007c0027d000bf0004dd000afc0014ed000),(0xde5c82998a50c8690fcde966ee0e101bf0fa4b3e7b515f6673b17ea73d49a9b6c951c92e987916d619a8f5056a215458301401088c800ffc61a0c0000000410000f800003e0001fffe000003ff000007fff800000fffff800000fffffe000000,0x68248501110063141014011a700089a41830200006046a09044280b0810580381022028240040800080300222805c08aa02db8e88045402810402c13c4291ec000000003e000156a40000032a000006a59000000fff6e800000fffdda000000),(0x517298e4e1f3b567951c6634d13267a2df5ed360a9ea9c18bbde9760898ce6f0f45a311ee3f0931dd3cec0785af6020082499020200820008046000402843007ff0000003ffffe0000000003fffffff8000000000fffffffffff000000000000,0x2227680a49b8458a4228068a4e209984fa0748415148801091207010084801400384824644400c086729407210013e4c8c0c942e03073c2023f033079073d6716a0000003f2e940000000003fffbf7e8000000000fbdfbff7fbd000000000000),(0x631c7cd938b56d3cb0df8e0f723f4715e422067a2febe49709fdd30e92cd8fd558f4247092eb36dc69a434b492e99100009020000d01101401a04401a4000103ffffffffc000000000000003fffffffffffffffff00000000000000000000000,0x20391381828281008cc02400108ca2051208e124a89c1912078b5634114306b4586d524099962911f22844801c11823445f5245047632b69126bf83603b86203ffff7ff5c000000000000000d5effd795a6feffd700000000000000000000000),(0xd6dad8d86324e1de5a122f78edf8eb37f7e6e41d4dcfe4d129eb1b85c7d237e98ec972ffbef85665b3e167b6be464030d1480209b2862d00a04680000000f483fffffffffffffffffffffffc0000000000000000000000000000000000000000,0xd11092848241b840248620640005262100180526040400400a8000c4c2848200002940109923211208100788040281935140205174f882d45c01c4384384280295fffabfc0d16aa95bffeafc0000000000000000000000000000000000000000)]
def xmcolumns : List ColumnInfo := [(16,0,2031,0,13),(128,0,1919,0,13),(64,0,1983,0,13),(520,0,503,0,12),(513,0,510,0,12),(544,0,479,0,12),(514,0,509,0,12),(644,0,379,0,11),(768,0,255,0,12),(537,0,486,0,8),(578,0,445,0,11),(595,0,428,0,7),(529,0,494,0,11),(521,16,486,0,8),(672,0,351,0,11),(646,0,377,0,8),(856,0,167,0,7),(834,0,189,0,8),(626,1,396,0,4),(519,0,504,0,7),(543,0,480,0,4),(852,8,163,0,4),(130,0,1917,0,9),(709,2,312,0,4),(547,0,476,0,7),(690,1,332,0,4),(809,16,198,0,4),(673,0,350,0,8),(610,0,413,0,7),(689,0,334,0,7),(710,0,313,0,7),(714,4,305,0,4),(966,0,57,0,4),(632,256,135,0,4),(832,0,191,0,11),(527,16,480,0,4),(800,0,223,0,9),(772,0,251,0,8),(916,8,99,0,4),(645,0,378,0,7),(653,16,354,0,4),(742,0,281,0,4),(536,0,487,0,11),(548,128,347,0,8),(803,64,156,0,4),(697,0,326,0,4),(768,32,94,129,7),(992,0,31,0,7),(603,0,420,0,4),(961,32,30,0,4),(668,0,355,0,7),(913,32,78,0,4),(780,0,243,0,7),(658,4,353,8,5),(597,2,424,0,4),(144,4,353,10,6),(801,0,222,0,7),(80,0,1967,0,11),(666,4,353,0,4),(144,0,1903,0,11),(565,128,330,0,4),(786,64,173,0,5),(674,0,349,0,7),(533,0,490,0,7),(384,0,1663,0,9),(224,256,23,8,5),(526,0,497,0,7),(744,256,23,0,4),(996,0,27,0,4),(994,0,29,0,4),(770,64,189,0,8),(841,16,166,0,4),(833,0,190,0,7),(787,64,172,0,4),(596,0,427,0,7),(825,0,198,0,4),(551,128,344,0,4),(704,0,319,0,11),(900,0,123,0,7),(676,0,347,0,8),(808,0,215,0,7),(912,0,111,0,7),(614,128,281,0,4),(568,0,455,0,7),(658,0,365,0,7),(940,0,83,0,4),(794,64,165,0,4),(208,0,1839,0,8)]
def xmautos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def xmlevels : Nat → Packing
  | 14 => xml14
  | 13 => xml13
  | 12 => xml12
  | 11 => xml11
  | 10 => xml10
  | 9 => xml9
  | 8 => xml8
  | 7 => xml7
  | _ => emptyPacking
def xmindex : Nat → Nat → Option (Nat × Nat)
  | 14 => lookupWord 12 47 4 12 4 4 xmh14
  | 13 => lookupWord 181 453 7 16 8 4 xmh13
  | 12 => lookupWord 493 2467 8 18 10 4 xmh12
  | 11 => lookupWord 292 1463 9 18 10 4 xmh11
  | 10 => lookupWord 61 309 6 16 8 4 xmh10
  | 9 => lookupWord 26 33 3 13 5 4 xmh9
  | 8 => lookupWord 1 3 1 9 1 4 xmh8
  | _ => fun _ => none
def xm : Forest := ⟨2047,14,fun j => xmsamples[j]?.getD (0,0),xmcolumns,xmautos,xmlevels,xmindex⟩
set_option maxHeartbeats 0 in
theorem geomxm : graphValid xm (boundsBefore knownx495) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_14_0 : block xm 14 0 1=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_14 : block xm 14 0 1=true := sxm_14_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_13_0 : block xm 13 0 2=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_13_2 : block xm 13 2 10=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_13 : block xm 13 0 12=true := (@block_merge xm 13 0 2 10 sxm_13_0 sxm_13_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_0 : block xm 12 0 24=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_24 : block xm 12 24 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_60 : block xm 12 60 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_96 : block xm 12 96 14=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_110 : block xm 12 110 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_146 : block xm 12 146 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_182 : block xm 12 182 16=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_12 : block xm 12 0 198=true := (@block_merge xm 12 0 182 16 (@block_merge xm 12 0 146 36 (@block_merge xm 12 0 110 36 (@block_merge xm 12 0 96 14 (@block_merge xm 12 0 60 36 (@block_merge xm 12 0 24 36 sxm_12_0 sxm_12_24) sxm_12_60) sxm_12_96) sxm_12_110) sxm_12_146) sxm_12_182)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_0 : block xm 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_4 : block xm 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_40 : block xm 11 40 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_76 : block xm 11 76 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_77 : block xm 11 77 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_113 : block xm 11 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_149 : block xm 11 149 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_185 : block xm 11 185 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_221 : block xm 11 221 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_257 : block xm 11 257 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_293 : block xm 11 293 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_329 : block xm 11 329 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_365 : block xm 11 365 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_401 : block xm 11 401 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_437 : block xm 11 437 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_473 : block xm 11 473 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_509 : block xm 11 509 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_545 : block xm 11 545 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_581 : block xm 11 581 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_617 : block xm 11 617 35=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_652 : block xm 11 652 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_688 : block xm 11 688 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_724 : block xm 11 724 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_760 : block xm 11 760 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_796 : block xm 11 796 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_832 : block xm 11 832 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_868 : block xm 11 868 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_904 : block xm 11 904 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_940 : block xm 11 940 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_976 : block xm 11 976 32=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_11 : block xm 11 0 1008=true := (@block_merge xm 11 0 976 32 (@block_merge xm 11 0 940 36 (@block_merge xm 11 0 904 36 (@block_merge xm 11 0 868 36 (@block_merge xm 11 0 832 36 (@block_merge xm 11 0 796 36 (@block_merge xm 11 0 760 36 (@block_merge xm 11 0 724 36 (@block_merge xm 11 0 688 36 (@block_merge xm 11 0 652 36 (@block_merge xm 11 0 617 35 (@block_merge xm 11 0 581 36 (@block_merge xm 11 0 545 36 (@block_merge xm 11 0 509 36 (@block_merge xm 11 0 473 36 (@block_merge xm 11 0 437 36 (@block_merge xm 11 0 401 36 (@block_merge xm 11 0 365 36 (@block_merge xm 11 0 329 36 (@block_merge xm 11 0 293 36 (@block_merge xm 11 0 257 36 (@block_merge xm 11 0 221 36 (@block_merge xm 11 0 185 36 (@block_merge xm 11 0 149 36 (@block_merge xm 11 0 113 36 (@block_merge xm 11 0 77 36 (@block_merge xm 11 0 76 1 (@block_merge xm 11 0 40 36 (@block_merge xm 11 0 4 36 sxm_11_0 sxm_11_4) sxm_11_40) sxm_11_76) sxm_11_77) sxm_11_113) sxm_11_149) sxm_11_185) sxm_11_221) sxm_11_257) sxm_11_293) sxm_11_329) sxm_11_365) sxm_11_401) sxm_11_437) sxm_11_473) sxm_11_509) sxm_11_545) sxm_11_581) sxm_11_617) sxm_11_652) sxm_11_688) sxm_11_724) sxm_11_760) sxm_11_796) sxm_11_832) sxm_11_868) sxm_11_904) sxm_11_940) sxm_11_976)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_0 : block xm 10 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_4 : block xm 10 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_40 : block xm 10 40 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_76 : block xm 10 76 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_112 : block xm 10 112 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_148 : block xm 10 148 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_184 : block xm 10 184 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_220 : block xm 10 220 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_256 : block xm 10 256 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_292 : block xm 10 292 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_328 : block xm 10 328 14=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_342 : block xm 10 342 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_378 : block xm 10 378 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_414 : block xm 10 414 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_450 : block xm 10 450 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_486 : block xm 10 486 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_522 : block xm 10 522 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_558 : block xm 10 558 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_594 : block xm 10 594 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_630 : block xm 10 630 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_666 : block xm 10 666 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_702 : block xm 10 702 20=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_10 : block xm 10 0 722=true := (@block_merge xm 10 0 702 20 (@block_merge xm 10 0 666 36 (@block_merge xm 10 0 630 36 (@block_merge xm 10 0 594 36 (@block_merge xm 10 0 558 36 (@block_merge xm 10 0 522 36 (@block_merge xm 10 0 486 36 (@block_merge xm 10 0 450 36 (@block_merge xm 10 0 414 36 (@block_merge xm 10 0 378 36 (@block_merge xm 10 0 342 36 (@block_merge xm 10 0 328 14 (@block_merge xm 10 0 292 36 (@block_merge xm 10 0 256 36 (@block_merge xm 10 0 220 36 (@block_merge xm 10 0 184 36 (@block_merge xm 10 0 148 36 (@block_merge xm 10 0 112 36 (@block_merge xm 10 0 76 36 (@block_merge xm 10 0 40 36 (@block_merge xm 10 0 4 36 sxm_10_0 sxm_10_4) sxm_10_40) sxm_10_76) sxm_10_112) sxm_10_148) sxm_10_184) sxm_10_220) sxm_10_256) sxm_10_292) sxm_10_328) sxm_10_342) sxm_10_378) sxm_10_414) sxm_10_450) sxm_10_486) sxm_10_522) sxm_10_558) sxm_10_594) sxm_10_630) sxm_10_666) sxm_10_702)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_0 : block xm 9 0 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_36 : block xm 9 36 23=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_59 : block xm 9 59 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_95 : block xm 9 95 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_131 : block xm 9 131 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_9 : block xm 9 0 166=true := (@block_merge xm 9 0 131 35 (@block_merge xm 9 0 95 36 (@block_merge xm 9 0 59 36 (@block_merge xm 9 0 36 23 sxm_9_0 sxm_9_36) sxm_9_59) sxm_9_95) sxm_9_131)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_8_0 : block xm 8 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_8_2 : block xm 8 2 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_8 : block xm 8 0 18=true := (@block_merge xm 8 0 2 16 sxm_8_0 sxm_8_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_7_0 : block xm 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_7 : block xm 7 0 1=true := sxm_7_0
theorem tablesxm : checkedTables xm 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block xm 0 0 0 = true)
  · exact (rfl : block xm 1 0 0 = true)
  · exact (rfl : block xm 2 0 0 = true)
  · exact (rfl : block xm 3 0 0 = true)
  · exact (rfl : block xm 4 0 0 = true)
  · exact (rfl : block xm 5 0 0 = true)
  · exact (rfl : block xm 6 0 0 = true)
  · exact allxm_7
  · exact allxm_8
  · exact allxm_9
  · exact allxm_10
  · exact allxm_11
  · exact allxm_12
  · exact allxm_13
  · exact allxm_14
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseFB : Impossible false (graphGoal 2047) 14 (rootB 2047).toFinset :=
  index_root (g:=xm) (i:=0) rfl rfl (before_sound knownx495 validx495) geomxm tablesxm (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem bound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨k,S,hk,run,sub⟩ := initial_live C legal first h (by omega)
  have eg : graph=graphGoal 511 := by decide +kernel
  have er : inputs++[seed]=rootB 511 := by decide +kernel
  rw [eg] at run
  rw [er] at sub
  have ok : splitOK 511 [(0,10),(1,1),(2,2),(3,5),(4,1),(5,1),(6,2),(7,4),(8,8)] = true := by decide +kernel
  have g1 : graphGoal 1535=graphGoal 511 := by decide +kernel
  have g2 : graphGoal 2047=graphGoal 511 := by decide +kernel
  have v1 : vars 1535=vars 511 := by decide +kernel
  have v2 : rootB 2047=rootB 511 := by decide +kernel
  have ha := caseFA
  have hb := caseFB
  rw [g1,v1] at ha
  rw [g2,v2] at hb
  rcases strong_split ok run sub with e | e
  · exact ha k hk (e ▸ run)
  · exact hb k hk (e ▸ run)
end PEqualNP.Outside.L_meta_4463.FullBound

namespace PEqualNP.Outside.L_meta_4463.CNF

open PEqualNP.Defs.LratEncoding
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def value (model : ℕ → Bool) (v : ℕ) : Bool := model (v+1)

theorem positive (model : ℕ → Bool) (v : ℕ) : litVal model (P v) = value model v := by
  unfold litVal P value
  rw [show (2*v+2)/2 = v+1 by omega, show (2*v+2)%2=0 by omega]
  simp

theorem negative (model : ℕ → Bool) (v : ℕ) : litVal model (Q v) = !(value model v) := by
  unfold litVal Q value
  rw [show (2*v+3)/2 = v+1 by omega, show (2*v+3)%2=1 by omega]
  cases model (v+1) <;> decide

theorem literal (model : ℕ → Bool) (v : ℕ) (b : Bool) :
    litVal model (L v b) = true ↔ value model v = b := by
  cases b <;> simp [L, positive, negative]

theorem pick_nat (model : ℕ → Bool) (V : ℕ → ℕ) (bound : ℕ)
    (sat : ClauseSat model ((List.range bound).map (fun i => P (V i)))) :
    ∃ i < bound, value model (V i) = true := by
  obtain ⟨lit, mem, yes⟩ := sat
  obtain ⟨i, within, rfl⟩ := List.mem_map.mp mem
  exact ⟨i,List.mem_range.mp within,(positive model (V i)).symm.trans yes⟩

abbrev Picks (n s : ℕ) (model : ℕ → Bool) :=
  ((j : Fin s) → {op : Fin 3 // value model (ix n s 0 j.val op.val) = true}) ×
  ((side : Fin 2) → (j : Fin s) → {k : ℕ // k < n+j.val+1 ∧
    value model (ix n s (side.val+1) j.val k) = true}) ×
  {k : ℕ // k < n+s+1 ∧ value model (ix n s 6 0 k) = true}

def Picks.op {n s : ℕ} {model : ℕ → Bool} (p : Picks n s model) (j : Fin s) : Fin 3 :=
  (p.1 j).val

def Picks.src {n s : ℕ} {model : ℕ → Bool} (p : Picks n s model) (side : Fin 2)
    (j : Fin s) : ℕ := (p.2.1 side j).val

def Picks.output {n s : ℕ} {model : ℕ → Bool} (p : Picks n s model) : ℕ := p.2.2.val

theorem Picks.opOn {n s : ℕ} {model : ℕ → Bool} (p : Picks n s model) (j : Fin s) :
    value model (ix n s 0 j.val (p.op j).val) = true := (p.1 j).property

theorem Picks.srcOn {n s : ℕ} {model : ℕ → Bool} (p : Picks n s model) (side : Fin 2)
    (j : Fin s) : p.src side j < n+j.val+1 ∧
    value model (ix n s (side.val+1) j.val (p.src side j)) = true := (p.2.1 side j).property

theorem Picks.outOn {n s : ℕ} {model : ℕ → Bool} (p : Picks n s model) :
    p.output < n+s+1 ∧ value model (ix n s 6 0 p.output) = true := p.2.2.property

noncomputable def choose_samples (n s : ℕ) (f : ℕ → Bool) (rows : List ℕ)
    (model : ℕ → Bool) (sat : ∀ c ∈ enc n s f rows, ClauseSat model c) : Picks n s model := by
  classical
  have chooseOp (j : Fin s) : ∃ k : Fin 3, value model (ix n s 0 j.val k.val) = true := by
    have h := sat [P (ix n s 0 j.val 0),P (ix n s 0 j.val 1),P (ix n s 0 j.val 2)] (by
      have mem : [P (ix n s 0 j.val 0),P (ix n s 0 j.val 1),P (ix n s 0 j.val 2)] ∈ fOp n s :=
        List.mem_map.mpr ⟨j.val,List.mem_range.mpr j.isLt,rfl⟩
      simp [enc,mem])
    have ⟨k,hk,yes⟩ := pick_nat model (ix n s 0 j.val) 3 h
    exact ⟨⟨k,hk⟩,yes⟩
  have chooseSrc (side : Fin 2) (j : Fin s) :
      ∃ k < n+j.val+1, value model (ix n s (side.val+1) j.val k) = true := by
    have index : side.val+1 ∈ ([1,2] : List ℕ) := by
      have t := side.isLt
      simp
      omega
    have mem : (List.range (n+j.val+1)).map (fun k => P (ix n s (side.val+1) j.val k)) ∈
        fSrcAlo n s := by
      apply List.mem_flatMap.mpr
      exact ⟨side.val+1,index,List.mem_map.mpr ⟨j.val,List.mem_range.mpr j.isLt,rfl⟩⟩
    exact pick_nat model _ _ (sat _ (by simp [enc,mem]))
  have chooseOut : ∃ k < n+s+1, value model (ix n s 6 0 k) = true := by
    have mem : (List.range (n+s+1)).map (fun k => P (ix n s 6 0 k)) ∈ fOutAlo n s := by
      simp [fOutAlo]
    exact pick_nat model _ _ (sat _ (by simp [enc,mem]))
  exact ⟨fun j => ⟨Classical.choose (chooseOp j), Classical.choose_spec (chooseOp j)⟩,
    fun side j => ⟨Classical.choose (chooseSrc side j), Classical.choose_spec (chooseSrc side j)⟩,
    ⟨Classical.choose chooseOut, Classical.choose_spec chooseOut⟩⟩

def row (n r : ℕ) : List Bool := List.ofFn (fun i : Fin n => r.testBit i.val)

def table (n s : ℕ) (model : ℕ → Bool) (r j : ℕ) : Bool :=
  value model (ix n s 3 j r)

def sourceValue (n s : ℕ) (model : ℕ → Bool) (side : Fin 2) (j r : ℕ) : Bool :=
  value model (ix n s (side.val+4) j r)

def tape (n s : ℕ) (model : ℕ → Bool) (r j : ℕ) : List Bool :=
  row n r ++ (List.range j).map (table n s model r)

theorem tape_length (n s : ℕ) (model : ℕ → Bool) (r j : ℕ) :
    (tape n s model r j).length = n+j := by
  simp [tape,row]

theorem tape_input (n s : ℕ) (model : ℕ → Bool) (r j : ℕ) {k : ℕ} (lt : k < n) :
    (tape n s model r j).getD k false = r.testBit k := by
  rw [tape,List.getD_append _ _ _ _ (by simp [row,lt]), row,
    List.getD_eq_getElem _ _ (by simp [lt]),List.getElem_ofFn]

theorem tape_gate (n s : ℕ) (model : ℕ → Bool) (r j : ℕ) {k : ℕ}
    (lo : n ≤ k) (hi : k < n+j) : (tape n s model r j).getD k false =
      table n s model r (k-n) := by
  rw [tape,List.getD_append_right _ _ _ _ (by simp [row,lo])]
  simp only [row,List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

private theorem equal_from_rel (p q : Bool) (h₁ : p = false ∨ q = true)
    (h₂ : p = true ∨ q = false) : p = q := by
  cases p <;> cases q <;> simp_all

theorem source_eq (n s : ℕ) (f : ℕ → Bool) (rows : List ℕ)
    (model : ℕ → Bool) (sat : ∀ c ∈ enc n s f rows, ClauseSat model c)
    (picks : Picks n s model) (side : Fin 2) (j : Fin s) (r : ℕ) (inRows : r ∈ rows) :
    sourceValue n s model side j.val r = (tape n s model r j.val).getD (picks.src side j) false := by
  let k := picks.src side j
  let e := side.val+1
  have esc : e ∈ ([1,2] : List ℕ) := by
    have t := side.isLt
    simp [e]
    omega
  have satSrc (c : List ℕ) (cl : c ∈ srcEq n s e j.val k r) : ClauseSat model c := by
    have root : c ∈ fSrcEq n s rows := by
      apply List.mem_flatMap.mpr
      refine ⟨e,esc,List.mem_flatMap.mpr ⟨j.val,List.mem_range.mpr j.isLt,?_⟩⟩
      exact List.mem_flatMap.mpr ⟨r,inRows,List.mem_flatMap.mpr ⟨k,List.mem_range.mpr (picks.srcOn side j).1,cl⟩⟩
    exact sat c (by simp [enc,root])
  have chosen : value model (ix n s e j.val k) = true := (picks.srcOn side j).2
  change sourceValue n s model side j.val r = (tape n s model r j.val).getD k false
  have e' : e+3 = side.val+4 := by simp [e,Nat.add_assoc]
  by_cases raw : k < n
  · have h := satSrc [Q (ix n s e j.val k), L (ix n s (e+3) j.val r) (r.testBit k)]
      (by simp [srcEq,raw])
    rw [tape_input n s model r _ raw]
    simpa [ClauseSat,negative,literal,chosen,sourceValue,e'] using h
  · by_cases back : k < n+j.val
    · have negRel := satSrc [Q (ix n s e j.val k), Q (ix n s (e+3) j.val r),
        P (ix n s 3 (k-n) r)] (by simp [srcEq,raw,back])
      have posRel := satSrc [Q (ix n s e j.val k), P (ix n s (e+3) j.val r),
        Q (ix n s 3 (k-n) r)] (by simp [srcEq,raw,back])
      rw [tape_gate n s model r _ (by omega) back]
      simp [ClauseSat, positive, negative,chosen,e'] at negRel posRel
      change sourceValue n s model side j.val r = false ∨ table n s model r (k-n) = true at negRel
      change sourceValue n s model side j.val r = true ∨ table n s model r (k-n) = false at posRel
      exact equal_from_rel _ _ negRel posRel
    · have h := satSrc [Q (ix n s e j.val k), Q (ix n s (e+3) j.val r)]
        (by simp [srcEq,raw,back])
      rw [List.getD_eq_default _ _ (by rw [tape_length]; omega)]
      simpa [ClauseSat,negative,chosen,sourceValue,e'] using h


end PEqualNP.Outside.L_meta_4463.CNF

namespace PEqualNP.Outside.L_meta_4463.Decode

open PEqualNP.Defs.LratEncoding
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4463.CNF

def gateFor {n s : ℕ} {a : ℕ → Bool} (P : Picks n s a) (j : Fin s) : Gate :=
  if (P.op j).val = 0 then ⟨.and,[P.src 0 j,P.src 1 j]⟩
  else if (P.op j).val = 1 then ⟨.or,[P.src 0 j,P.src 1 j]⟩
  else ⟨.and,[]⟩

def circuitFor {n s : ℕ} {a : ℕ → Bool} (P : Picks n s a) : Circuit :=
  ⟨List.ofFn (gateFor P), P.output⟩

theorem circuit_mono {n s : ℕ} {a : ℕ → Bool} (P : Picks n s a) :
    Monotone2 (circuitFor P) := by
  intro g h
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
  unfold gateFor
  split
  · simp
  · split <;> simp

theorem gate_eq (n s : ℕ) (f : ℕ → Bool) (rows : List ℕ)
    (a : ℕ → Bool) (sat : ∀ c ∈ enc n s f rows, ClauseSat a c)
    (Picks₀ : Picks n s a) (j : Fin s) (r : ℕ) (inRows : r ∈ rows) :
    (gateFor Picks₀ j).op.eval ((gateFor Picks₀ j).inputs.map fun i =>
      (tape n s a r j.val).getD i false) = table n s a r j.val := by
  let k := j.val
  let va := ix n s 4 k r
  let vb := ix n s 5 k r
  let vo := ix n s 3 k r
  have litA : (tape n s a r k).getD (Picks₀.src 0 j) false = value a va :=
    (source_eq n s f rows a sat Picks₀ 0 j r inRows).symm
  have litB : (tape n s a r k).getD (Picks₀.src 1 j) false = value a vb :=
    (source_eq n s f rows a sat Picks₀ 1 j r inRows).symm
  have all (c : List ℕ) (member : c ∈ gateCl n s k r) : ClauseSat a c := by
    have inside : c ∈ fGate n s rows := by
      apply List.mem_flatMap.mpr
      exact ⟨k,List.mem_range.mpr j.isLt,List.mem_flatMap.mpr ⟨r,inRows,member⟩⟩
    exact sat c (by simp [enc,inside])
  let op := (Picks₀.op j).val
  have selected : value a (ix n s 0 k op) = true := Picks₀.opOn j
  have bounds : op < 3 := (Picks₀.op j).isLt
  change (gateFor Picks₀ j).op.eval ((gateFor Picks₀ j).inputs.map fun i =>
    (tape n s a r k).getD i false) = value a vo
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 by omega) with h0 | h1 | h2
  · have chosen : value a (ix n s 0 k 0) = true := h0 ▸ selected
    have hA := all [Q (ix n s 0 k 0),Q vo,P va] (by simp [gateCl,vo,va])
    have hB := all [Q (ix n s 0 k 0),Q vo,P vb] (by simp [gateCl,vo,vb])
    have hO := all [Q (ix n s 0 k 0),P vo,Q va,Q vb] (by simp [gateCl,vo,va,vb])
    simp [ClauseSat,positive,negative,chosen] at hA hB hO
    simp [gateFor, show (Picks₀.op j).val = 0 from h0, GateOp.eval]
    cases ha : value a va <;> cases hb : value a vb <;> cases ho : value a vo <;> simp_all
  · have chosen : value a (ix n s 0 k 1) = true := h1 ▸ selected
    have hA := all [Q (ix n s 0 k 1),P vo,Q va] (by simp [gateCl,vo,va])
    have hB := all [Q (ix n s 0 k 1),P vo,Q vb] (by simp [gateCl,vo,vb])
    have hO := all [Q (ix n s 0 k 1),Q vo,P va,P vb] (by simp [gateCl,vo,va,vb])
    simp [ClauseSat,positive,negative,chosen] at hA hB hO
    simp [gateFor, show (Picks₀.op j).val = 1 from h1, GateOp.eval]
    cases ha : value a va <;> cases hb : value a vb <;> cases ho : value a vo <;> simp_all
  · have chosen : value a (ix n s 0 k 2) = true := h2 ▸ selected
    have h := all [Q (ix n s 0 k 2),P vo] (by simp [gateCl,vo])
    have vt : value a vo = true := by
      simpa [ClauseSat,positive,negative,chosen] using h
    simp [gateFor,show (Picks₀.op j).val = 2 from h2,GateOp.eval,vt]

theorem output_eq (n s : ℕ) (f : ℕ → Bool) (rows : List ℕ)
    (a : ℕ → Bool) (sat : ∀ c ∈ enc n s f rows, ClauseSat a c)
    (Picks₀ : Picks n s a) (r : ℕ) (inRows : r ∈ rows) :
    (tape n s a r s).getD Picks₀.output false = f r := by
  let k := Picks₀.output
  have chosen := Picks₀.outOn.2
  have all (c : List ℕ) (member : c ∈ outEq n s f k r) : ClauseSat a c := by
    have inside : c ∈ fOutEq n s f rows := by
      apply List.mem_flatMap.mpr
      exact ⟨r,inRows,List.mem_flatMap.mpr ⟨k,List.mem_range.mpr Picks₀.outOn.1,member⟩⟩
    exact sat c (by simp [enc,inside])
  by_cases inp : k < n
  · rw [show Picks₀.output = k from rfl, tape_input n s a r _ inp]
    by_contra neq
    have h := all [Q (ix n s 6 0 k)] (by simp [outEq,inp,neq])
    simp [ClauseSat,negative,chosen,k] at h
  · by_cases gate : k < n+s
    · rw [show Picks₀.output = k from rfl, tape_gate n s a r _ (by omega) gate]
      have h := all [Q (ix n s 6 0 k),L (ix n s 3 (k-n) r) (f r)]
        (by simp [outEq,inp,gate])
      simpa [ClauseSat,negative,literal,chosen,k,table] using h
    · rw [show Picks₀.output = k from rfl, List.getD_eq_default _ _ (by rw [tape_length]; omega)]
      cases value : f r
      · rfl
      · exfalso
        have h := all [Q (ix n s 6 0 k)] (by simp [outEq,inp,gate,value])
        simp [ClauseSat,negative,chosen,k] at h

private theorem tape_step (n s : ℕ) (a : ℕ → Bool) (r k : ℕ) :
    tape n s a r (k+1) = tape n s a r k ++ [table n s a r k] := by
  simp [tape,List.range_succ,List.append_assoc]

private theorem trace_of_picks (n s : ℕ) (f : ℕ → Bool) (rows : List ℕ)
    (a : ℕ → Bool) (sat : ∀ c ∈ enc n s f rows, ClauseSat a c)
    (P : Picks n s a) (r : ℕ) (inRows : r ∈ rows) :
    (circuitFor P).wires (row n r) = tape n s a r s := by
  let gs := List.ofFn (gateFor P)
  have length : gs.length = s := by simp [gs]
  have h (k : ℕ) (bound : k ≤ s) :
      (⟨gs.take k,0⟩ : Circuit).wires (row n r) = tape n s a r k := by
    induction k with
    | zero => simp [Circuit.wires,tape]
    | succ k ih =>
      have kLt : k < s := by omega
      have idx : k < gs.length := length.symm ▸ kLt
      let j : Fin s := ⟨k,kLt⟩
      have current : gs[k]'idx = gateFor P j := by simp [gs,j]
      rw [List.take_succ_eq_append_getElem idx,current]
      simp only [Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
      change (⟨gs.take k,0⟩ : Circuit).wires (row n r) ++
        [(gateFor P j).op.eval ((gateFor P j).inputs.map fun i =>
          ((⟨gs.take k,0⟩ : Circuit).wires (row n r)).getD i false)] = tape n s a r (k+1)
      rw [ih (Nat.le_of_lt kLt),gate_eq n s f rows a sat P j r inRows,tape_step]
  have all := h s (le_refl _)
  rw [List.take_of_length_le (by rw [length])] at all
  exact all

/-- The clauses of the exact project encoding determine a monotone circuit
that matches the posted rows. Padding operations become empty-input ANDs. -/
theorem circuit_of_sat (n s : ℕ) (f : ℕ → Bool) (rows : List ℕ)
    (sat : FormulaSat (enc n s f rows)) :
    ∃ C : Circuit, Monotone2 C ∧ C.size = s ∧ ∀ r ∈ rows, C.eval (row n r) = f r := by
  obtain ⟨a,clauses⟩ := sat
  let P := choose_samples n s f rows a clauses
  refine ⟨circuitFor P,circuit_mono P,by simp [Circuit.size,circuitFor],?_⟩
  intro r hr
  change ((circuitFor P).wires (row n r)).getD P.output false = f r
  rw [trace_of_picks n s f rows a clauses P r hr]
  exact output_eq n s f rows a clauses P r hr



end PEqualNP.Outside.L_meta_4463.Decode

namespace PEqualNP.Outside.L_meta_4463.Rows

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def yesRows : List Nat := [515,6,524,536,529,545,66,132,776,160,320,288]
def noRows : List Nat := [554,50,581,616,116,650,713,208,773,276,897,402]

def sample {n : Nat} (r : Nat) (i : Fin n) : Bool := r.testBit i.val

def augment (x : Fin 9 → Bool) (i : Fin 10) : Bool :=
  if hi : i.val < 9 then x ⟨i.val,hi⟩ else x 0 || x 3

def edgeFun (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

private theorem get_input {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private def mask {n : Nat} (x : Fin n → Bool) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn x)).toNat

private theorem mask_lt {n : Nat} (x : Fin n → Bool) : mask x < 2^n := by
  simpa only [mask,List.length_ofFn] using (BitVec.ofBoolListLE (List.ofFn x)).isLt

private theorem mask_bit {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (mask x).testBit i.val = x i := by
  change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD i.val = x i
  rw [BitVec.getLsbD_ofBoolListLE,get_input]

private def covered (r : Nat) : Bool :=
  let x : Fin 9 → Bool := sample r
  let m := mask (augment x)
  if edgeFun x then
    yesRows.any (fun p => p &&& m == p)
  else
    noRows.any (fun q => m &&& q == m)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem finite_cover : ∀ r : Fin 512, covered r.val = true := by
  decide +kernel

private theorem mask_le {n : Nat} {x : Fin n → Bool} {r : Nat}
    (h : r &&& mask x = r) (i : Fin n) (hit : sample r i = true) : x i = true := by
  have equal := congrArg (fun a : Nat => a.testBit i.val) h
  change r.testBit i.val = true at hit
  simp only [Nat.testBit_and,mask_bit,hit,Bool.true_and] at equal
  exact equal

private theorem le_mask {n : Nat} {x : Fin n → Bool} {r : Nat}
    (h : mask x &&& r = mask x) (i : Fin n) (hit : x i = true) : sample r i = true := by
  have equal := congrArg (fun a : Nat => a.testBit i.val) h
  simp only [Nat.testBit_and,mask_bit,hit,Bool.true_and] at equal
  exact equal

theorem row_witness (x : Fin 9 → Bool) :
    if edgeFun x
    then ∃ p ∈ yesRows, ∀ i : Fin 10, sample p i = true → augment x i = true
    else ∃ q ∈ noRows, ∀ i : Fin 10, augment x i = true → sample q i = true := by
  have pack : (sample (mask x) : Fin 9 → Bool) = x := funext (mask_bit x)
  have check := finite_cover ⟨mask x,mask_lt x⟩
  change covered (mask x) = true at check
  simp only [covered,pack] at check
  cases h : edgeFun x
  · simp only [h,Bool.false_eq_true,ite_false,List.any_eq_true,beq_iff_eq] at check ⊢
    obtain ⟨q,hq,le⟩ := check
    exact ⟨q,hq,le_mask le⟩
  · simp only [h,ite_true,List.any_eq_true,beq_iff_eq] at check ⊢
    obtain ⟨p,hp,le⟩ := check
    exact ⟨p,hp,mask_le le⟩

-- The list monotonicity argument follows PEqualNP.Outside.L_meta_1701.
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def Ordered (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ t, u.getD t false = true → v.getD t false = true

private theorem step_order (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (u v : List Bool) (h : Ordered u v) : Ordered (step u g) (step v g) := by
  refine ⟨by simp [step,h.1],fun i hi => ?_⟩
  by_cases lt : i < u.length
  · have lt' : i < v.length := h.1 ▸ lt
    simpa only [step,List.getD_append _ _ _ _ lt'] using
      h.2 i (by simpa only [step,List.getD_append _ _ _ _ lt] using hi)
  · have past : u.length ≤ i := by omega
    have past' : v.length ≤ i := h.1 ▸ past
    have idx : i-v.length = i-u.length := by rw [h.1]
    rw [step,List.getD_append_right _ _ _ _ past']
    rw [step,List.getD_append_right _ _ _ _ past] at hi
    rw [idx]
    by_cases atEnd : i - u.length = 0
    · rw [atEnd,List.getD_cons_zero] at hi ⊢
      rcases hop with andOp | orOp
      · rw [andOp] at hi ⊢
        change (g.inputs.map _).all id = true at hi ⊢
        simp only [List.all_eq_true,List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,id_eq] at hi ⊢
        exact fun k hk => h.2 k (hi k hk)
      · rw [orOp] at hi ⊢
        change (g.inputs.map _).any id = true at hi ⊢
        simp only [List.any_eq_true,List.mem_map,exists_exists_and_eq_and,id_eq] at hi ⊢
        obtain ⟨k,hk,on⟩ := hi
        exact ⟨k,hk,h.2 k on⟩
    · have off : ([g.op.eval (g.inputs.map fun k => u.getD k false)] : List Bool).getD
          (i-u.length) false = false := List.getD_eq_default _ _ (by simp; omega)
      rw [off] at hi
      contradiction

private theorem fold_order (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (u v : List Bool) (h : Ordered u v) : Ordered (gs.foldl step u) (gs.foldl step v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun gate mem => hg gate (List.mem_cons_of_mem _ mem)) _ _
      (step_order g (hg g (List.mem_cons_self ..)) u v h)

theorem eval_order {n : Nat} (D : Circuit) (mono : Monotone2 D) {x y : Fin n → Bool}
    (le : ∀ i, x i = true → y i = true) (h : D.eval (List.ofFn x) = true) :
    D.eval (List.ofFn y) = true := by
  have input : Ordered (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp,fun t ht => ?_⟩
    by_cases lt : t < n
    · let i : Fin n := ⟨t,lt⟩
      exact (get_input y i).trans (le i ((get_input x i).symm.trans ht))
    · have out : n ≤ t := by omega
      rw [List.getD_eq_default _ _ (by simpa using out)] at ht
      contradiction
  exact (fold_order D.gates (fun g hg => (mono g hg).1) _ _ input).2 D.output h

/-- Agreement on the posted rows gives full correctness on the
nine inputs with the supplied tenth wire. -/
theorem extend (D : Circuit) (mono : Monotone2 D)
    (matchRows : ∀ r ∈ yesRows ++ noRows, D.eval (List.ofFn (sample (n := 10) r)) = yesRows.contains r)
    (x : Fin 9 → Bool) : D.eval (List.ofFn (augment x)) = edgeFun x := by
  have witness := row_witness x
  cases h : edgeFun x
  · simp only [h,Bool.false_eq_true,ite_false] at witness
    obtain ⟨q,hq,le⟩ := witness
    have agree := matchRows q (List.mem_append_right _ hq)
    have disjoint : noRows.all (fun r => !(yesRows.contains r)) = true := by decide
    have off : yesRows.contains q = false := by
      simpa using List.all_eq_true.mp disjoint q hq
    rw [off] at agree
    cases eval : D.eval (List.ofFn (augment x))
    · rfl
    · have on := eval_order D mono le eval
      rw [agree] at on
      contradiction
  · simp only [h,ite_true] at witness
    obtain ⟨p,hp,le⟩ := witness
    have agree := matchRows p (List.mem_append_left _ hp)
    have on : yesRows.contains p = true := by simpa using hp
    rw [on] at agree
    exact eval_order D mono le agree

/-- Add the supplied wire as the first gate and leave the old wire numbers unchanged. -/
def prependSeed (D : Circuit) : Circuit :=
  ⟨⟨.or,[0,3]⟩ :: D.gates,D.output⟩

theorem prependSeed_size (D : Circuit) : (prependSeed D).size = D.size + 1 := rfl

theorem prependSeed_monotone (D : Circuit) (mono : Monotone2 D) :
    Monotone2 (prependSeed D) := by
  intro g hg
  change g ∈ (⟨.or,[0,3]⟩ : Gate) :: D.gates at hg
  rcases List.mem_cons.mp hg with rfl | prior
  · simp
  · exact mono g prior

theorem augment_list (x : Fin 9 → Bool) :
    List.ofFn (augment x) = List.ofFn x ++ [x 0 || x 3] := by
  rw [List.ofFn_succ_last]
  rfl

theorem prependSeed_wires (D : Circuit) (x : Fin 9 → Bool) :
    (prependSeed D).wires (List.ofFn x) = D.wires (List.ofFn (augment x)) := by
  change D.gates.foldl step (step (List.ofFn x) ⟨.or,[0,3]⟩) = D.gates.foldl step _
  rw [augment_list]
  simp [step,GateOp.eval]

private theorem keep_wire (gs : List Gate) (w : List Bool) (i : Nat) (old : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ old

theorem prependSeed_wire9 (D : Circuit) (x : Fin 9 → Bool) :
    ((prependSeed D).wires (List.ofFn x)).getD 9 false = (x 0 || x 3) := by
  rw [prependSeed_wires,augment_list]
  change (D.gates.foldl step (List.ofFn x ++ [_])).getD 9 false = _
  rw [keep_wire _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem prependSeed_correct (D : Circuit) (mono : Monotone2 D)
    (matchRows : ∀ r ∈ yesRows ++ noRows, D.eval (List.ofFn (sample (n := 10) r)) = yesRows.contains r) :
    circuitFun 9 (prependSeed D) = edgeFun := by
  funext x
  change ((prependSeed D).wires (List.ofFn x)).getD D.output false = _
  rw [prependSeed_wires]
  exact extend D mono matchRows x


end PEqualNP.Outside.L_meta_4463.Rows

namespace PEqualNP.Outside.L_meta_4463.Connect

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Defs.LratEncoding
open PEqualNP.Outside.L_meta_4463.Rows

theorem unsat_of_bound
    (bound : ∀ C : Circuit, Monotone2 C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
      circuitFun 9 C = edgeFun → 16 ≤ C.size) :
    ¬ FormulaSat (enc 10 14 (fun r => yesRows.contains r) (yesRows ++ noRows)) := by
  intro sat
  obtain ⟨D,mono,size,matchRows⟩ :=
    PEqualNP.Outside.L_meta_4463.Decode.circuit_of_sat 10 14 _ _ sat
  have lower := bound (prependSeed D) (prependSeed_monotone D mono)
    (prependSeed_wire9 D) (prependSeed_correct D mono matchRows)
  rw [prependSeed_size,size] at lower
  omega


end PEqualNP.Outside.L_meta_4463.Connect

theorem PEqualNP.Outside.L_meta_4463 : have x1 : List ℕ := [(515 : ℕ), (6 : ℕ), (524 : ℕ), (536 : ℕ), (529 : ℕ), (545 : ℕ), (66 : ℕ), (132 : ℕ), (776 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)]; have x2 : List ℕ := [(554 : ℕ), (50 : ℕ), (581 : ℕ), (616 : ℕ), (116 : ℕ), (650 : ℕ), (713 : ℕ), (208 : ℕ), (773 : ℕ), (276 : ℕ), (897 : ℕ), (402 : ℕ)]; ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) (fun (x3 : ℕ) => x1.contains x3) (x1 ++ x2)) := by
  exact PEqualNP.Outside.L_meta_4463.Connect.unsat_of_bound PEqualNP.Outside.L_meta_4463.FullBound.bound
