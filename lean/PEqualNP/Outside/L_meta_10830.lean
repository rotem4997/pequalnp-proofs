import PEqualNP.Defs

-- This proof reuses the signed circuit certificate from L_meta_7306.
-- That certificate is adapted from L_meta_7794, whose root certificate
-- is adapted from benoitrazet, PR 12184.
-- The live-wire checker and the smaller graph certificates are adapted from the project proofs
-- L_meta_1667 and L_meta_1677, distributed under Apache-2.0.
-- Each root search considers all nine inputs. Restriction bounds and conflicting truth-table
-- rows eliminate children, and checked graph permutations identify equivalent states.
-- The signed search counts binary gates with complementation available for free.
namespace PEqualNP.Outside.L_meta_10830
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
def graph : Sig := 0xfffffffffffffffefffffffffffffffafffffffffffefffefffffffffffafff0fffffffefffffffeffffffeeffffffaafefefefefefefefeeeeeccccaaaa0000
def seed : Sig := inputs.getD 0 zero ||| inputs.getD 6 zero
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool := (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 || sample r 6) := by decide +kernel
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

theorem raw_signed (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C) (small : C.gates.countP (fun g => !isNot g) ≤ 14)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edge x) :
    ∃ k S, k ≤ 14 ∧ Live true graph k S ∧ ∀ a ∈ S, a ∈ inputs := by
  let result := (execute C.gates inputs).getD C.output zero
  have goalEq : result = graph := by
    apply bit_ext
    intro r
    rw [table_eval C legal, edge_table]
    exact computes (sample r)
  have rep := get_rep (u := true) (execute C.gates inputs) C.output
  change nrm true result ∈ _ ∨ ¬proper (nrm true result) at rep
  have pg : bit 0 graph = false := by decide +kernel
  rw [goalEq, nrm_id pg] at rep
  have targetIn := rep.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k, S, hk, run, hs⟩ := extract C.gates inputs legal (by simp) graph_proper targetIn
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at hs
  exact ⟨k, S, hk.trans small, run, hs⟩

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
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8)
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

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let hi := ((mask/512-1) >>> (4*i)) &&& 15
    let r := if mask >= 512 then (if hi = 0 then 0 else 1 <<< (hi-1)) else if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
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
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
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
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
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

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
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

abbrev Bits := BitVec 416
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 416 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 416 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 416 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 416 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 416) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 416) (j : Fin 9) :
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 416) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 416) :
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
  let n := v.toNat % 18446744073709551557
  (n*(n+971)) % 18446744073709551557
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
    if (rs ||| column d z.2) != BitVec.allOnes 416 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 416) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 416 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 416) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 416) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 416) &&
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
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^417*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^417 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<417 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<417 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<417 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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

def fullMarks (r packed : Nat) := ((packed+r) >>> 416) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (417*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^417)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 417*(i+1)-417=417*i := by omega
      have ge : ¬417*(i+1)<417 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 416 = (a==BitVec.allOnes 416) := by
  by_cases h : a=BitVec.allOnes 416
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^416-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^416 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (417*i) =
      (f xs[i]==BitVec.allOnes 416) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^417*u+x+(2^417*v+1)=2^417*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^417 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬417*(i+1)+416<417 := by omega
      have di : 417*(i+1)+416-417=417*i+416 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 417) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (417*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 417) (i:=i) (by simpa using hi) _ ok.2
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
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 18446744073709551557
  (n*(n+971)) % 18446744073709551557
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (packedAt data (i*(len+(selected g.mask).length+depth)) (len+(selected g.mask).length+depth)) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 416 then true
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
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 416
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
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
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
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

theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

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
-- Evaluate each packed column before sharing it across the row checks.
noncomputable def forceSignals {β : Type} (sigs : List PackedSig)
    (cont : List PackedSig → β) : β :=
  match sigs with
  | [] => cont []
  | (pos, neg)::tail =>
    force pos fun pos => force neg fun neg =>
    forceSignals tail fun rest => cont ((pos, neg)::rest)

theorem forceSignals_eq {β : Type} (sigs : List PackedSig)
    (cont : List PackedSig → β) : forceSignals sigs cont = cont sigs := by
  induction sigs generalizing cont with
  | nil => rfl
  | cons sig sigs ih =>
    obtain ⟨pos, neg⟩ := sig
    simp only [forceSignals, force_eq, ih]

noncomputable def forceBatch {β : Type} (b : Batch) (cont : Batch → β) : β :=
  let (k,n,count,sigs,any,once,twice) := b
  force count fun count => forceSignals sigs fun sigs =>
    force any fun any => force once fun once => force twice fun twice =>
    cont (k,n,count,sigs,any,once,twice)

theorem forceBatch_eq {β : Type} (b : Batch)
    (cont : Batch → β) : forceBatch b cont = cont b := by
  obtain ⟨k,n,count,sigs,any,once,twice⟩ := b
  simp only [forceBatch, force_eq, forceSignals_eq]

noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  forceBatch (makeBatch k ar xs) fun b =>
    forceLanes xs fun ys => (List.range len).all (fun d =>
      let i := lo+d
      batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceBatch_eq,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceBatch_eq,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
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
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

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

def neighbor10830 (i : Fin 9) : Nat := [4,5,6,7,0,1,0,0,2].getD i.val 0
def absentRow10830 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor10830 i)
def presentRow10830 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor10830 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRow10830 i) graph ≠ bit (presentRow10830 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRow10830 i) (inputs.getD j.val zero) =
      bit (presentRow10830 i) (inputs.getD j.val zero)) := by decide +kernel


theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 14) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 13 else 14) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 14 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 13 else 14) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode

  have out := get_rep (u:=u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow10830 i) (presentRow10830 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 14 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 13 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 edge 14 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run


def padSamples (n a : Nat) : Bits :=
  BitVec.ofNat _ (if a.testBit 0 then a ||| (((1 <<< 416)-1) ^^^ ((1 <<< n)-1)) else a)
def sampleAt (n : Nat) (data : Array (Nat × Nat)) (i : Nat) : Bits × Bits :=
  let p := data[i]?.getD (0,0)
  (padSamples n p.1,padSamples n p.2)
def mixTag (h : Nat) : Nat := (h*513158153883743911432465183)%618970019642690137449562111
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls17 : Lower true (vars 17) (graphGoal 17) 1 := size_of (hints:=4) (by decide +kernel)
def es17 := extendKnown [] 1 [(17,[]),(34,[84,16]),(65,[101,100]),(66,[101,100,16]),(68,[101,33,100,32]),(129,[118,117,116]),(136,[118,117,50,49,116,48]),(144,[118,117,115,114,113,116,64]),(260,[135,134,133,33,132,32]),(264,[135,134,133,50,49,132,48]),(288,[135,134,83,82,81,132,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs17 : Known true es17 := extendKnown_ok (m:=17) baseKnown ls17 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls67 : Lower true (vars 67) (graphGoal 67) 2 := size_of (hints:=102) (by decide +kernel)
def es67 := extendKnown es17 2 [(67,[]),(69,[33]),(70,[33,16]),(81,[67,66,100,97,64]),(98,[84,83,82,97,80]),(137,[50,118,49]),(152,[67,50,118,65,48]),(193,[117,116,115,114,113,96]),(268,[135,134,49,32]),(290,[135,133,132,131,130,101,129,16]),(292,[135,84,83,134,81,32]),(296,[135,84,83,50,134,81,48]),(324,[135,133,132,131,98,129,96]),(392,[117,116,131,114,99,129,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs67 : Known true es67 := extendKnown_ok (m:=67) vs17 ls67 (by decide +kernel)
def s145S := sampleAt 9 #[(0x3f,0x49),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x1c7,0x92),(0x0,0x0),(0x0,0x0),(0x1f8,0x124),(0x0,0x0)]
def s145C : List ColumnInfo := []
def s145D3 (_ : Nat) : Nat := 0x7
def s145L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,s145D3)
  | _ => emptyPacking
def s145I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s145 : Forest := ⟨145,3,s145S,s145C,[[],[116],[64],[64,112],[112,64],[112]],s145L,s145I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs145_3_0 : block s145 3 0 1 = true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs145_3 : block s145 3 0 1 = true := bs145_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts145 : checkedTables s145 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact bs145_3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs145 : graphValid s145 (boundsBefore es67) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls145 : Lower true (vars 145) (graphGoal 145) 4 := lower_forest (g:=s145) (i:=0) (hints:=4) (before_sound es67 vs67) gs145 ts145 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es145 := extendKnown es67 4 [(145,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs145 : Known true es145 := extendKnown_ok (m:=145) vs67 ls145 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls51 : Lower true (vars 51) (graphGoal 51) 3 := size_of (hints:=1048660) (by decide +kernel)
def es51 := extendKnown es145 3 [(51,[]),(163,[118,116]),(170,[118,50,116,117,49,16]),(178,[118,115,114,116,117,65,16]),(202,[50,100,117,49,16]),(204,[100,117,49,32]),(210,[99,98,100,117,65,16]),(212,[99,100,117,65,32]),(277,[135,134,133,33]),(281,[135,134,50,133,49]),(305,[135,134,131,130,133,81]),(329,[135,50,100,133,49]),(330,[135,50,100,133,49,16]),(353,[135,134,131,130,100,133,81]),(389,[135,118,116,133,33]),(404,[134,131,132,117,65,32]),(417,[134,131,130,116,133,81]),(432,[135,118,131,114,116,133,81,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs51 : Known true es51 := extendKnown_ok (m:=51) vs145 ls51 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls71 : Lower true (vars 71) (graphGoal 71) 3 := size_of (hints:=1638) (by decide +kernel)
def es71 := extendKnown es51 3 [(71,[]),(300,[135,84,83,134,82,49,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs71 : Known true es71 := extendKnown_ok (m:=71) vs51 ls71 (by decide +kernel)
def s83S := sampleAt 21 #[(0x60fff,0x221a3),(0x1bf060,0xa736a),(0x0,0x0),(0x0,0x0),(0x1c007f,0x1d4a5c),(0x0,0x0),(0x1fff80,0x158c10),(0x0,0x0),(0x0,0x0)]
def s83C : List ColumnInfo := []
def s83D3 (_ : Nat) : Nat := 0xf
def s83L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,s83D3)
  | _ => emptyPacking
def s83I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s83 : Forest := ⟨83,3,s83S,s83C,[[],[96,65]],s83L,s83I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs83_3_0 : block s83 3 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs83_3 : block s83 3 0 1 = true := bs83_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts83 : checkedTables s83 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact bs83_3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs83 : graphValid s83 (boundsBefore es71) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls83 : Lower true (vars 83) (graphGoal 83) 4 := lower_forest (g:=s83) (i:=0) (hints:=100) (before_sound es71 vs71) gs83 ts83 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es83 := extendKnown es71 4 [(83,[]),(85,[33]),(99,[84,16]),(102,[32,84,33]),(195,[117,116]),(197,[117,116,33]),(201,[117,50,118,100,49]),(294,[135,133,130,101,128,66]),(298,[135,133,131,130,101,128,67]),(325,[135,133,32,132,16]),(326,[135,133,32,132]),(332,[135,133,134,32,100,49]),(354,[135,83,82,80,132,97]),(356,[135,83,134,32,100,81]),(393,[135,133,50,118,48,132,16]),(396,[117,50,134,48,116,33]),(408,[135,133,131,50,118,48,132,65]),(424,[83,50,134,48,116,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs83 : Known true es83 := extendKnown_ok (m:=83) vs71 ls83 (by decide +kernel)
def s153S := sampleAt 21 #[(0x87ff,0x191a3),(0x0,0x0),(0x0,0x0),(0x10f860,0x15bb6a),(0x1f007f,0x16224c),(0x0,0x0),(0x0,0x0),(0x1fff80,0x84410),(0x0,0x0)]
def s153C : List ColumnInfo := [(8,0,145,512,4)]
def s153D4 (_ : Nat) : Nat := 0x2f
def s153L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,s153D4)
  | _ => emptyPacking
def s153I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s153 : Forest := ⟨153,4,s153S,s153C,[[],[64]],s153L,s153I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs153_4_0 : block s153 4 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs153_4 : block s153 4 0 1 = true := bs153_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts153 : checkedTables s153 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs153_4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs153 : graphValid s153 (boundsBefore es83) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls153 : Lower true (vars 153) (graphGoal 153) 5 := lower_forest (g:=s153) (i:=0) (hints:=28676) (before_sound es83 vs83) gs153 ts153 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es153 := extendKnown es83 5 [(153,[]),(209,[101,116,64,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs153 : Known true es153 := extendKnown_ok (m:=153) vs83 ls153 (by decide +kernel)
def s87S := sampleAt 36 #[(0x6820ffff,0x28a21aa3),(0x9b03f0660,0x8b1a7366a),(0xe3fc00780,0xa39c6378a),(0x0,0x0),(0xfc00007ff,0xfc514a55c),(0x0,0x0),(0xffffff800,0x54618c010),(0x0,0x0),(0x0,0x0)]
def s87C : List ColumnInfo := [(4,0,83,512,4)]
def s87D4 (_ : Nat) : Nat := 0x5f
def s87L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,s87D4)
  | _ => emptyPacking
def s87I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s87 : Forest := ⟨87,4,s87S,s87C,[[],[33]],s87L,s87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs87_4_0 : block s87 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs87_4 : block s87 4 0 1 = true := bs87_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts87 : checkedTables s87 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs87_4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs87 : graphValid s87 (boundsBefore es153) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls87 : Lower true (vars 87) (graphGoal 87) 5 := lower_forest (g:=s87) (i:=0) (hints:=1636) (before_sound es153 vs153) gs87 ts87 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es87 := extendKnown es153 5 [(87,[]),(103,[16,84]),(199,[117,116]),(302,[135,83,134,80,50,33,65]),(327,[135,133,32,16,132]),(364,[135,83,134,80,82,49,100]),(428,[134,48,82,33,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs87 : Known true es87 := extendKnown_ok (m:=87) vs153 ls87 (by decide +kernel)
def s115S := sampleAt 41 #[(0xb303f3c0ff,0x1128b1d253),(0x14dfc0cffc0,0x51c6447ca),(0x0,0x0),(0x0,0x0),(0x18e000f00ff,0x18e924e24ac),(0x1f0000fff00,0x1f0a28bb830),(0x1fffff00000,0x1eac3002020),(0x0,0x0),(0x0,0x0)]
def s115C : List ColumnInfo := []
def s115D4 (_ : Nat) : Nat := 0x1f
def s115L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,s115D4)
  | _ => emptyPacking
def s115I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s115 : Forest := ⟨115,4,s115S,s115C,[[],[16,84]],s115L,s115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs115_4_0 : block s115 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs115_4 : block s115 4 0 1 = true := bs115_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts115 : checkedTables s115 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs115_4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs115 : graphValid s115 (boundsBefore es87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls115 : Lower true (vars 115) (graphGoal 115) 5 := lower_forest (g:=s115) (i:=0) (hints:=1048660) (before_sound es87 vs87) gs115 ts115 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es115 := extendKnown es87 5 [(115,[]),(203,[115,96,113,83,65]),(205,[115,114,96,113,83,66]),(227,[16,117,84]),(333,[135,131,130,98,96,129,83,64]),(334,[135,131,98,96,129,83,65]),(341,[135,33,133]),(355,[135,134,96,129,133,64]),(357,[135,130,98,96,129,64]),(362,[135,131,130,128,101,67]),(397,[135,115,130,99,112,129,82,64]),(412,[135,115,130,99,128,113,82,66]),(425,[131,130,99,112,129,64]),(426,[115,114,134,112,49,117,65]),(440,[131,114,99,112,129]),(453,[33,133,116]),(457,[50,118,49,133,100]),(460,[135,134,32,49,117,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs115 : Known true es115 := extendKnown_ok (m:=115) vs87 ls115 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls171 : Lower true (vars 171) (graphGoal 171) 4 := size_of (hints:=1077335) (by decide +kernel)
def es171 := extendKnown es115 4 [(171,[]),(186,[66,67,48]),(206,[118,50,48,117,49]),(214,[66,118,50,64,117,65]),(218,[66,67,48,101]),(220,[66,67,48,101,33]),(234,[100,98,118,99,112,117,49]),(242,[66,116,99,112,117,65]),(285,[135,32,84,16]),(307,[132,116,131,84,16]),(309,[135,67,32,84,16]),(313,[66,135,67,48,84,16]),(331,[134,118,133,49]),(345,[134,100,98,116,99,64,133,49]),(361,[100,98,135,99,48,101,16]),(369,[132,130,116,99,64,133,81]),(419,[134,132,131,117,16]),(421,[134,132,135,115,32,117,16]),(434,[134,66,131,64,117,65]),(436,[134,135,115,32,117,65]),(458,[134,132,130,135,131,112,101]),(468,[134,98,114,131,96,117,65]),(481,[132,130,118,115,96,133,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs171 : Known true es171 := extendKnown_ok (m:=171) vs115 ls171 (by decide +kernel)
def s179S := sampleAt 50 #[(0x3003ff3c03ff,0x10250b1c4913),(0xcc0300cfff00,0x4d1746451f4a),(0x0,0x0),(0x0,0x0),(0x30ffc00f003ff,0x1045814e0922c),(0x3f00000fffc00,0x3b26098bae0b0),(0x0,0x0),(0x3ffffff000000,0x2eb82e00300c0),(0x0,0x0)]
def s179C : List ColumnInfo := [(0,32,145,514,5)]
def s179D5 (_ : Nat) : Nat := 0x5f
def s179L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,s179D5)
  | _ => emptyPacking
def s179I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s179 : Forest := ⟨179,5,s179S,s179C,[[],[116],[64],[64,112],[112,64],[112],[81],[81,116],[64,81],[64,81,112],[112,81,64],[112,81]],s179L,s179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs179_5_0 : block s179 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs179_5 : block s179 5 0 1 = true := bs179_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts179 : checkedTables s179 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs179_5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs179 : graphValid s179 (boundsBefore es171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls179 : Lower true (vars 179) (graphGoal 179) 6 := lower_forest (g:=s179) (i:=0) (hints:=1048660) (before_sound es171 vs171) gs179 ts179 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es179 := extendKnown es171 6 [(179,[]),(405,[134,133,33]),(433,[134,131,130,133,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs179 : Known true es179 := extendKnown_ok (m:=179) vs171 ls179 (by decide +kernel)
def s211S := sampleAt 50 #[(0x200ff980ffff,0x1418820683),(0xd80c06ff0180,0x5a5d32a74daa),(0x0,0x0),(0x0,0x0),(0x31ff0070001ff,0x108e06714291c),(0x0,0x0),(0x3e00007fffe00,0x3a4824558b050),(0x3fffff8000000,0x2f70b8060c060),(0x0,0x0)]
def s211C : List ColumnInfo := [(0,2,145,576,5),(2,0,209,512,5),(16,0,195,512,4),(66,0,145,512,4),(128,0,83,512,4)]
def s211D6 (_ : Nat) : Nat := 0x5191f
def s211H5 (_ : Nat) : Nat := 0xaa7b009441
def s211D5 (_ : Nat) : Nat := 0x84068140c920fe20fd20fd42
def s211H4 (_ : Nat) : Nat := 0xd40
def s211D4 (_ : Nat) : Nat := 0x4f91520
def s211L : Nat → Packing
  | 6 => (1,0,3,0,0,1,0,s211D6)
  | 5 => (3,1,3,0,0,5,0,s211D5)
  | 4 => (1,2,3,0,0,1,0,s211D4)
  | _ => emptyPacking
def s211I : Nat → Nat → Option (Nat × Nat)
  | 6,h => lookupWord 2 6 1 7 2 1 s211H5 (mixTag h)
  | 5,h => lookupWord 1 3 1 6 1 1 s211H4 (mixTag h)
  | _,_ => none
def s211 : Forest := ⟨211,6,s211S,s211C,[[],[116]],s211L,s211I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_6_0 : block s211 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_6 : block s211 6 0 1 = true := bs211_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_5_0 : block s211 5 0 3 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_5 : block s211 5 0 3 = true := bs211_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_4_0 : block s211 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs211_4 : block s211 4 0 1 = true := bs211_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts211 : checkedTables s211 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs211_4
  · exact bs211_5
  · exact bs211_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs211 : graphValid s211 (boundsBefore es179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls211 : Lower true (vars 211) (graphGoal 211) 7 := lower_forest (g:=s211) (i:=0) (hints:=100) (before_sound es179 vs179) gs211 ts211 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es211 := extendKnown es179 7 [(211,[]),(213,[33]),(409,[131,130,112,64,99,129])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs211 : Known true es211 := extendKnown_ok (m:=211) vs179 ls211 (by decide +kernel)
def s217S := sampleAt 39 #[(0x2041fffff,0xc4311a3),(0x0,0x0),(0x0,0x0),(0x4d07e0b060,0x452ce6b56a),(0x71f800c07f,0x513084c44c),(0x0,0x0),(0x7e0000ff80,0x7ea294ee18),(0x7fffff0000,0x2ac3180810),(0x0,0x0)]
def s217C : List ColumnInfo := [(64,0,153,512,5)]
def s217D5 (_ : Nat) : Nat := 0x5f
def s217L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,s217D5)
  | _ => emptyPacking
def s217I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s217 : Forest := ⟨217,5,s217S,s217C,[[],[112,99]],s217L,s217I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs217_5_0 : block s217 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs217_5 : block s217 5 0 1 = true := bs217_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts217 : checkedTables s217 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs217_5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs217 : graphValid s217 (boundsBefore es211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls217 : Lower true (vars 217) (graphGoal 217) 6 := lower_forest (g:=s217) (i:=0) (hints:=28676) (before_sound es211 vs211) gs217 ts217 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es217 := extendKnown es211 6 [(217,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs217 : Known true es217 := extendKnown_ok (m:=217) vs211 ls217 (by decide +kernel)
def s358S := sampleAt 50 #[(0x0,0x0),(0x680c0180ffff,0x2a1d10a246a3),(0x900ffeff0180,0x10543a870d8a),(0x0,0x0),(0x0,0x0),(0x31ff0070001ff,0x110e06714291c),(0x3e00007fffe00,0x3c4824558b050),(0x0,0x0),(0x3fffff8000000,0x2ef0b8060c060)]
def s358C : List ColumnInfo := [(2,0,356,512,4),(4,0,354,512,4),(32,0,326,512,4),(64,0,294,512,4),(256,0,102,512,4)]
def s358D6 (_ : Nat) : Nat := 0x234095f
def s358H5 (_ : Nat) : Nat := 0x235ab4c7465000db00e1321f0e1
def s358D5 (_ : Nat) : Nat := 0x30828fd10fd20
def s358H4 (_ : Nat) : Nat := 0x1a95840cbf8005
def s358D4 (_ : Nat) : Nat := 0x578d510
def s358L : Nat → Packing
  | 6 => (1,0,3,0,0,1,0,s358D6)
  | 5 => (2,1,3,0,0,3,0,s358D5)
  | 4 => (1,2,3,0,0,1,0,s358D4)
  | _ => emptyPacking
def s358I : Nat → Nat → Option (Nat × Nat)
  | 6,h => lookupWord 4 14 3 8 1 3 s358H5 (mixTag h)
  | 5,h => lookupWord 2 6 3 8 1 3 s358H4 (mixTag h)
  | _,_ => none
def s358 : Forest := ⟨358,6,s358S,s358C,[[],[130,101],[33,133],[33,81,97,129],[81,134],[81,98,129,33],[97,82],[97,130,81,82],[129,33,82,101],[129,98]],s358L,s358I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_6_0 : block s358 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_6 : block s358 6 0 1 = true := bs358_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_5_0 : block s358 5 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_5 : block s358 5 0 2 = true := bs358_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_4_0 : block s358 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs358_4 : block s358 4 0 1 = true := bs358_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts358 : checkedTables s358 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs358_4
  · exact bs358_5
  · exact bs358_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs358 : graphValid s358 (boundsBefore es217) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls358 : Lower true (vars 358) (graphGoal 358) 7 := lower_forest (g:=s358) (i:=0) (hints:=8607762000) (before_sound es217 vs217) gs358 ts358 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es358 := extendKnown es217 7 [(358,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs358 : Known true es358 := extendKnown_ok (m:=358) vs217 ls358 (by decide +kernel)
def s119S := sampleAt 75 #[(0xc60d0101fccf301fff,0x420515142c47324a93),(0x1093601fe0333fff980,0x1160d0e191150f98a),(0x671c7fe0003c3c01e00,0x251473e3c7bc3c6de3a),(0x0,0x0),(0x781f8000003fc001fff,0x781f8a8a953b80c956c),(0x7fe00000003ffffe000,0x7fe00b0b162eeaf0070),(0x7fffffffffc00000000,0x5aca8c0c18000080040),(0x0,0x0),(0x0,0x0)]
def s119C : List ColumnInfo := [(0,16,102,513,5),(0,32,85,514,5),(4,0,115,512,5),(17,0,102,512,4),(34,0,85,512,4)]
def s119D6 (_ : Nat) : Nat := 0x4632bf
def s119D5 (_ : Nat) : Nat := 0x1ef52
def s119L : Nat → Packing
  | 6 => (1,0,3,0,0,1,0,s119D6)
  | 5 => (1,1,3,0,0,1,0,s119D5)
  | _ => emptyPacking
def s119I : Nat → Nat → Option (Nat × Nat)
  | 6,_ => some (0,0)
  | _,_ => none
def s119 : Forest := ⟨119,6,s119S,s119C,[[],[16,84]],s119L,s119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs119_6_0 : block s119 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs119_6 : block s119 6 0 1 = true := bs119_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs119_5_0 : block s119 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs119_5 : block s119 5 0 1 = true := bs119_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts119 : checkedTables s119 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs119_5
  · exact bs119_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs119 : graphValid s119 (boundsBefore es358) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls119 : Lower true (vars 119) (graphGoal 119) 7 := lower_forest (g:=s119) (i:=0) (hints:=1050196) (before_sound es358 vs358) gs119 ts119 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es119 := extendKnown es358 7 [(119,[]),(231,[16,117,84]),(343,[135,33,133]),(430,[115,134,112,49,117,65]),(455,[33,133,116]),(492,[115,134,112,49,114,117,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs119 : Known true es119 := extendKnown_ok (m:=119) vs358 ls119 (by decide +kernel)
def s187S := sampleAt 80 #[(0x10c002403ff33cc03fff,0x1040264290b11cc49513),(0x32c0380300ccffff300,0x12d1791b4644551f34a),(0x0,0x0),(0x9c3003ffc00f0f003c00,0x943076c7c1ef0f0dbc3a),(0xe03ffc00000ff0003fff,0xa0345805014ee0092a2c),(0xffc00000000fffffc000,0xfec26026098bbaae00b0),(0x0,0x0),(0xfffffffffff000000000,0x4b8b81382e00003000c0),(0x0,0x0)]
def s187C : List ColumnInfo := [(8,0,179,512,6)]
def s187D6 (_ : Nat) : Nat := 0xbf
def s187L : Nat → Packing
  | 6 => (1,0,1,0,0,1,0,s187D6)
  | _ => emptyPacking
def s187I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s187 : Forest := ⟨187,6,s187S,s187C,[[],[64],[81],[64,81]],s187L,s187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs187_6_0 : block s187 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs187_6 : block s187 6 0 1 = true := bs187_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts187 : checkedTables s187 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs187_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs187 : graphValid s187 (boundsBefore es119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls187 : Lower true (vars 187) (graphGoal 187) 7 := lower_forest (g:=s187) (i:=0) (hints:=1077332) (before_sound es119 vs119) gs187 ts187 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es187 := extendKnown es119 7 [(187,[]),(497,[134,130,116,64,99,133,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs187 : Known true es187 := extendKnown_ok (m:=187) vs119 ls187 (by decide +kernel)
def s207S := sampleAt 68 #[(0x19240fffa4e8103f,0x9242543a4685083),(0x26e380cc0c7301fc0,0x22e392cd2c53254d2),(0x38fc00f00f83fe000,0x28fc12f12e83a6492),(0xc0ffff000ffc00000,0x40b6c7006ffc1428a),(0x0,0x0),(0x0,0x0),(0xff0000000ffffffff,0xd5002402412858b2c),(0xfffffffff00000000,0xbf4938ab800060c30),(0x0,0x0)]
def s207C : List ColumnInfo := [(8,0,199,512,5)]
def s207D5 (_ : Nat) : Nat := 0xbf
def s207L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,s207D5)
  | _ => emptyPacking
def s207I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s207 : Forest := ⟨207,5,s207S,s207C,[[],[33]],s207L,s207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs207_5_0 : block s207 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs207_5 : block s207 5 0 1 = true := bs207_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts207 : checkedTables s207 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs207_5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs207 : graphValid s207 (boundsBefore es187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls207 : Lower true (vars 207) (graphGoal 207) 6 := lower_forest (g:=s207) (i:=0) (hints:=30310) (before_sound es187 vs187) gs207 ts207 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es207 := extendKnown es187 6 [(207,[]),(335,[135,32,16]),(365,[84,134,80,118,82,16,48]),(429,[84,134,82,33,48]),(444,[134,64,82,33,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs207 : Known true es207 := extendKnown_ok (m:=207) vs187 ls207 (by decide +kernel)
def s215S := sampleAt 78 #[(0x4001fff068080fffff,0x2a8302828206a83),(0x9b3019809b00ff01980,0x8b34b9a68b26a74d9aa),(0xe3c01e00e3ff0001e00,0xa3c4be26a3a7264de2a),(0x0,0x0),(0x303ffe000fc000001fff,0x10151c00cfc14142951c),(0x0,0x0),(0x3fc000000fffffffe000,0x354090048545858b0050),(0x3ffffffff00000000000,0x2feae1570006060c0060),(0x0,0x0)]
def s215C : List ColumnInfo := [(4,0,211,512,7)]
def s215D7 (_ : Nat) : Nat := 0xbf
def s215L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s215D7)
  | _ => emptyPacking
def s215I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s215 : Forest := ⟨215,7,s215S,s215C,[[],[116],[33],[33,116]],s215L,s215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs215_7_0 : block s215 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs215_7 : block s215 7 0 1 = true := bs215_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts215 : checkedTables s215 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs215_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs215 : graphValid s215 (boundsBefore es207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls215 : Lower true (vars 215) (graphGoal 215) 8 := lower_forest (g:=s215) (i:=0) (hints:=1636) (before_sound es207 vs207) gs215 ts215 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es215 := extendKnown es207 8 [(215,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs215 : Known true es215 := extendKnown_ok (m:=215) vs207 ls215 (by decide +kernel)
def s219S := sampleAt 78 #[(0x400480ff93380fffff,0xc82418118206a83),(0x1ac0700c06dcff01980,0xad2f26d3254a74d9aa),(0x0,0x0),(0x263007ff0071f0001e00,0x22306d8f0771f162de1a),(0x383ff800007e00001fff,0x2834700c067e0142951c),(0x0,0x0),(0x3fc00000007fffffe000,0x3f424048245aa58b0050),(0x3fffffffff8000000000,0x15cb8270b800060c0060),(0x0,0x0)]
def s219C : List ColumnInfo := [(8,0,211,512,7)]
def s219D7 (_ : Nat) : Nat := 0xbf
def s219L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s219D7)
  | _ => emptyPacking
def s219I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s219 : Forest := ⟨219,7,s219S,s219C,[[]],s219L,s219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs219_7_0 : block s219 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs219_7 : block s219 7 0 1 = true := bs219_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts219 : checkedTables s219 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs219_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs219 : graphValid s219 (boundsBefore es215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls219 : Lower true (vars 219) (graphGoal 219) 8 := lower_forest (g:=s219) (i:=0) (hints:=28772) (before_sound es215 vs215) gs219 ts219 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es219 := extendKnown es215 8 [(219,[]),(221,[33]),(473,[133,130,112,99,129])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs219 : Known true es219 := extendKnown_ok (m:=219) vs215 ls219 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls222 : Lower true (vars 222) (graphGoal 222) 5 := size_of (hints:=822572640) (by decide +kernel)
def es222 := extendKnown es219 5 [(222,[]),(250,[101,117,100,83,66,49]),(377,[128,134,112,100,67,82,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs222 : Known true es222 := extendKnown_ok (m:=222) vs219 ls222 (by decide +kernel)
def s235S := sampleAt 75 #[(0x861c80ffb7380ff980,0x20c8643931860f98a),(0x1186700c049cff01fff,0x82722d1014a344aa3),(0x0,0x0),(0x66387ff0071f0001e00,0x222858f0771f162de1a),(0x0,0x0),(0x783f800007e00001fff,0x783d84c267e054a955c),(0x7fc0000007fffffe000,0x7f40048246ca58b0050),(0x7ffffffff8000000000,0x5dd7270b800060c0060),(0x0,0x0)]
def s235C : List ColumnInfo := [(0,8,99,640,5),(0,32,201,514,5),(8,0,227,512,5),(32,0,203,512,5)]
def s235D6 (_ : Nat) : Nat := 0xe123f
def s235L : Nat → Packing
  | 6 => (1,0,2,0,0,1,0,s235D6)
  | _ => emptyPacking
def s235I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s235 : Forest := ⟨235,6,s235S,s235C,[[],[96,113,83]],s235L,s235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs235_6_0 : block s235 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs235_6 : block s235 6 0 1 = true := bs235_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts235 : checkedTables s235 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs235_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs235 : graphValid s235 (boundsBefore es222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls235 : Lower true (vars 235) (graphGoal 235) 7 := lower_forest (g:=s235) (i:=0) (hints:=1077334) (before_sound es222 vs222) gs235 ts235 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es235 := extendKnown es222 7 [(235,[]),(349,[32,135,16,84]),(363,[134,128,118,129,80,48]),(371,[134,96,112,129,133,67]),(373,[130,98,96,112,129,67]),(427,[134,81,48]),(442,[132,130,100,128,116,113,84,49]),(459,[118,133,49]),(462,[134,32,118,117,49]),(476,[66,134,64,33,101,67]),(483,[132,134,96,112,129,133,115]),(485,[132,32,135,16,117,83]),(489,[132,130,134,96,135,16,101,83]),(490,[132,130,134,96,118,97,117,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs235 : Known true es235 := extendKnown_ok (m:=235) vs222 ls235 (by decide +kernel)
def s238S := sampleAt 76 #[(0x0,0x0),(0x930fcc0099c03fffff,0x1105cc8808c888d523),(0x31cccf0036e7fc03300,0x114ccf1992a59d9b36a),(0xc60f0ffff8f80003c00,0x42050543f8f8585bc1a),(0x0,0x0),(0xf80ff0003f000003fff,0xf80fa0333f035352adc),(0xfff000003ffffffc000,0xeea000222d526260090),(0xffffffffc0000000000,0xbdfafabc000383800e0),(0x0,0x0)]
def s238C : List ColumnInfo := [(0,128,102,520,5)]
def s238D5 (_ : Nat) : Nat := 0xbf
def s238L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,s238D5)
  | _ => emptyPacking
def s238I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s238 : Forest := ⟨238,5,s238S,s238C,[[],[115],[97,82],[97,82,115]],s238L,s238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs238_5_0 : block s238 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs238_5 : block s238 5 0 1 = true := bs238_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts238 : checkedTables s238 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs238_5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs238 : graphValid s238 (boundsBefore es235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls238 : Lower true (vars 238) (graphGoal 238) 6 := lower_forest (g:=s238) (i:=0) (hints:=823162448) (before_sound es235 vs235) gs238 ts238 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es238 := extendKnown es235 6 [(238,[]),(246,[67]),(311,[132,134,129,81,33,116,48]),(315,[132,128,96,129,80,33,116,48]),(347,[16,84,33,135]),(423,[134,129,81,33,48]),(438,[134,129,81,33,67]),(470,[133,33,67]),(474,[133,66,118,49]),(498,[132,134,129,133,98,67]),(500,[132,134,97,101,82,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs238 : Known true es238 := extendKnown_ok (m:=238) vs235 ls238 (by decide +kernel)
def s243S := sampleAt 84 #[(0x1086007feb300ff3c03ff,0x204a16110a0b1c4913),(0x2319806014dff00cfff00,0x109a2e8c054746451f4a),(0x0,0x0),(0x0,0x0),(0xcc61ff8018e0000f003ff,0x44208b0298e2424e0922c),(0xf07e00001f00000fffc00,0xf0764c131f0a8a8bae0b0),(0xff8000001ffffff000000,0xfe8048121eab0b00280a0),(0xffffffffe000000000000,0xbbdd705c000c0c00300c0),(0x0,0x0)]
def s243C : List ColumnInfo := [(32,0,211,512,7)]
def s243D7 (_ : Nat) : Nat := 0xbf
def s243L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s243D7)
  | _ => emptyPacking
def s243I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s243 : Forest := ⟨243,7,s243S,s243C,[[],[116]],s243L,s243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs243_7_0 : block s243 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs243_7 : block s243 7 0 1 = true := bs243_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts243 : checkedTables s243 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs243_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs243 : graphValid s243 (boundsBefore es238) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls243 : Lower true (vars 243) (graphGoal 243) 8 := lower_forest (g:=s243) (i:=0) (hints:=1048660) (before_sound es238 vs238) gs243 ts243 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es243 := extendKnown es238 8 [(243,[]),(413,[131,130,112,64,99,129,82]),(441,[131,130,112,64,99,129]),(469,[33,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs243 : Known true es243 := extendKnown_ok (m:=243) vs238 ls243 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls317 : Lower true (vars 317) (graphGoal 317) 5 := size_of (hints:=8598358020) (by decide +kernel)
def es317 := extendKnown es243 5 [(317,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs317 : Known true es317 := extendKnown_ok (m:=317) vs243 ls317 (by decide +kernel)
def s359S := sampleAt 78 #[(0x4eb019808e8080ff980,0x46b4b9a686a6a64f9aa),(0x70c01e001300ff01fff,0x50c43e220322a344aa3),(0x83001fffe3ff0001e00,0x300aa87a387060de0a),(0x0,0x0),(0x0,0x0),(0x303ffe000fc000001fff,0x10311c00cfc14142951c),(0x3fc000000fffffffe000,0x3a8090048585858b0050),(0x0,0x0),(0x3ffffffff00000000000,0x2fcee1570006060c0060)]
def s359C : List ColumnInfo := [(1,0,358,512,7)]
def s359D7 (_ : Nat) : Nat := 0xbf
def s359L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s359D7)
  | _ => emptyPacking
def s359I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s359 : Forest := ⟨359,7,s359S,s359C,[[],[33,133]],s359L,s359I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs359_7_0 : block s359 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs359_7 : block s359 7 0 1 = true := bs359_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts359 : checkedTables s359 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs359_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs359 : graphValid s359 (boundsBefore es317) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls359 : Lower true (vars 359) (graphGoal 359) 8 := lower_forest (g:=s359) (i:=0) (hints:=8590984790) (before_sound es317 vs317) gs359 ts359 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es359 := extendKnown es317 8 [(359,[]),(366,[134,81,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs359 : Known true es359 := extendKnown_ok (m:=359) vs317 ls359 (by decide +kernel)
def s435S := sampleAt 80 #[(0x1e2c03c3003ff3c03ff,0xa2c8941089231c9125),(0x99930030cc0300cfff00,0x999338304f83e04787e0),(0x0,0x0),(0x0,0x0),(0x1e1c003f0ffc00f003ff,0xa1c1129051444e1224a),(0xe01fffc3f00000fffc00,0x200443c3b05816b8781c),(0x0,0x0),(0xffe00003ffffff000000,0xf5402202ea6298024090),(0xfffffffc000000000000,0xdffbbc3c0380e00380e0)]
def s435C : List ColumnInfo := [(256,0,179,512,6)]
def s435D6 (_ : Nat) : Nat := 0xbf
def s435L : Nat → Packing
  | 6 => (1,0,1,0,0,1,0,s435D6)
  | _ => emptyPacking
def s435I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s435 : Forest := ⟨435,6,s435S,s435C,[[],[116],[64],[64,112],[112,64],[112],[129],[129,116],[64,129],[64,129,112],[112,129,64],[112,129]],s435L,s435I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs435_6_0 : block s435 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs435_6 : block s435 6 0 1 = true := bs435_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts435 : checkedTables s435 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs435_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs435 : graphValid s435 (boundsBefore es359) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls435 : Lower true (vars 435) (graphGoal 435) 7 := lower_forest (g:=s435) (i:=0) (hints:=21475885140) (before_sound es359 vs359) gs435 ts435 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es435 := extendKnown es359 7 [(435,[]),(437,[133,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs435 : Known true es435 := extendKnown_ok (m:=435) vs359 ls435 (by decide +kernel)
def s461S := sampleAt 78 #[(0x8c7603001901ff9c07f,0x4368b440944a38d123),(0x0,0x0),(0x1309803fe6e0180e7f80,0x101829162e2592a4992),(0x2431ffc018ffe00f8000,0x11a1c0c8b0e06f850a),(0x0,0x0),(0x0,0x0),(0x383e00001f00000fffff,0x383c11089d088445264c),(0x3fc000001ffffff00000,0x3f801209174b15802850),(0x3fffffffe00000000000,0x3eee5c2e000c06003060)]
def s461C : List ColumnInfo := [(65,0,396,512,4),(68,0,393,512,4),(129,0,332,512,4),(136,0,325,512,4),(260,0,201,512,4),(264,0,197,512,4)]
def s461D7 (_ : Nat) : Nat := 0x468d33f
def s461H6 (_ : Nat) : Nat := 0xce9900113e0667844400001140000430
def s461D6 (_ : Nat) : Nat := 0x5088643faa1fd10
def s461H5 (_ : Nat) : Nat := 0x2380000000018c0000400a4ccd1002
def s461D5 (_ : Nat) : Nat := 0xb78d910
def s461L : Nat → Packing
  | 7 => (1,0,3,0,0,1,0,s461D7)
  | 6 => (2,1,3,0,0,4,0,s461D6)
  | 5 => (1,2,3,0,0,1,0,s461D5)
  | _ => emptyPacking
def s461I : Nat → Nat → Option (Nat × Nat)
  | 7,h => lookupWord 3 14 1 9 1 4 s461H6 (mixTag h)
  | 6,h => lookupWord 2 13 1 9 1 4 s461H5 (mixTag h)
  | _,_ => none
def s461 : Forest := ⟨461,7,s461S,s461C,[[],[50,118],[32,135],[32,48,134,118],[48,32,118,134],[48,134],[96,114,131],[96,130,115,32,48],[112,98,131,32,50],[112,130,99],[128,98,115],[128,114,99]],s461L,s461I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_7_0 : block s461 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_7 : block s461 7 0 1 = true := bs461_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_6_0 : block s461 6 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_6 : block s461 6 0 2 = true := bs461_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_5_0 : block s461 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs461_5 : block s461 5 0 1 = true := bs461_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts461 : checkedTables s461 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs461_5
  · exact bs461_6
  · exact bs461_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs461 : graphValid s461 (boundsBefore es435) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls461 : Lower true (vars 461) (graphGoal 461) 8 := lower_forest (g:=s461) (i:=0) (hints:=8589964806) (before_sound es435 vs435) gs461 ts461 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es461 := extendKnown es435 8 [(461,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs461 : Known true es461 := extendKnown_ok (m:=461) vs435 ls461 (by decide +kernel)
def s223S := sampleAt 126 #[(0x800024901fff041a4e8080fffffff,0x64904a83000a46828206aaa83),(0x13566038e019809a6c7300ff0199980,0x11566978e4d9a68a2c5326a74d999aa),(0x1c67803f001e00e38f83ff0001e1e00,0x1467897f04de26a28e83a7264de1e2a),(0x26078003fffe000fc0ffc000001fe000,0x22078036db1e00efc0ffc16162dfe01a),(0x3807fffc0000000fff000000001fffff,0x2807aa38001800cfff0001414295551c),(0x0,0x0),(0x3ff800000000000fffffffffffe00000,0x3ea8012000900485551285858b000050),(0x3ffffffffffffff00000000000000000,0x15f855c124e15700000006060c000060),(0x0,0x0)]
def s223C : List ColumnInfo := [(8,0,215,512,8)]
def s223D8 (_ : Nat) : Nat := 0x17f
def s223L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s223D8)
  | _ => emptyPacking
def s223I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s223 : Forest := ⟨223,8,s223S,s223C,[[],[33]],s223L,s223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs223_8_0 : block s223 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs223_8 : block s223 8 0 1 = true := bs223_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts223 : checkedTables s223 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs223_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs223 : graphValid s223 (boundsBefore es461) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls223 : Lower true (vars 223) (graphGoal 223) 9 := lower_forest (g:=s223) (i:=0) (hints:=30308) (before_sound es461 vs461) gs223 ts223 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es223 := extendKnown es461 9 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs223 : Known true es223 := extendKnown_ok (m:=223) vs461 ls223 (by decide +kernel)
def s239S := sampleAt 132 #[(0x40643392403fff8e3a4e80403ff33300,0x241192419507861a46834181f3330a),(0x8980cce3803300104c73007fc03fffff,0x88044e388b322000c531148c8955523),(0x30e38f0fc003c00e38f83ff80003c3c00,0x10a38f0fc19bc66a28e83b39999bc3c6a),(0xc303f00ffffc000fc0ffc0000003fc000,0x4102d00b6c3c00efc0ffc0b0585bfc01a),(0x0,0x0),(0xfc03fff00000000fff0000000003fffff,0xfc03fbb003300ccfff0006a35352aaadc),(0xfffc00000000000ffffffffffffc00000,0xef54000002200885961284c2626000090),(0xfffffffffffffff000000000000000000,0xbefd2ee493c2af00000007038380000e0),(0x0,0x0)]
def s239C : List ColumnInfo := [(8,0,231,512,7)]
def s239D7 (_ : Nat) : Nat := 0x17f
def s239L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s239D7)
  | _ => emptyPacking
def s239I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s239 : Forest := ⟨239,7,s239S,s239C,[[]],s239L,s239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs239_7_0 : block s239 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs239_7 : block s239 7 0 1 = true := bs239_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts239 : checkedTables s239 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs239_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs239 : graphValid s239 (boundsBefore es223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls239 : Lower true (vars 239) (graphGoal 239) 8 := lower_forest (g:=s239) (i:=0) (hints:=1078870) (before_sound es223 vs223) gs239 ts239 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es239 := extendKnown es223 8 [(239,[]),(351,[16,135,33,84]),(431,[134,81,48]),(446,[134,64,81,67]),(508,[134,64,97,98,101,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs239 : Known true es239 := extendKnown_ok (m:=239) vs223 ls239 (by decide +kernel)
def s247S := sampleAt 148 #[(0x4040cc0003fffc6306801003ff33cc00ffff,0x440025502c21028150280b11cc125413),(0x89833330033000849b001ffc00ccffffcc00,0x8811332173218008b10d21c86445487cc8a),(0x30e33c3c003c00338e3ffe00000f0f000f000,0x10a33c3c677c67928a3b3e6799ef0f1b6f1ba),(0x0,0x0),(0xc303c03fffc0003c0fc00000000ff0000ffff,0x410140150d800d3c0fc0a815054ee0064a86c),(0xfc03ffc00000003ff0000000000ffffff0000,0xfc03eec0ce00ce3ff006b0d6358bbab780370),(0xfffc00000000003ffffffffffff0000000000,0xef5400008800882d6544c0982600002400240),(0xffffffffffffffc0000000000000000000000,0xbefebbaaf02af000000700e03800003800380),(0x0,0x0)]
def s247C : List ColumnInfo := [(0,32,213,514,8),(1,16,102,640,5),(1,128,102,528,5),(4,0,243,512,8),(16,0,231,512,7),(34,0,213,512,7),(64,4,179,512,6),(68,0,179,512,6),(128,0,119,512,7),(128,16,102,513,5),(145,0,102,512,4)]
def s247D9 (_ : Nat) : Nat := 0xf086a67f
def s247H8 (_ : Nat) : Nat := 0x964091e557930d004c0074005fa2470
def s247D8 (_ : Nat) : Nat := 0x4264314f5520223955531cc54d4e1342682542a38cb5328b0992a251b143d483554c4e6be9b7355321900ff8c3fd50ff54ffd30ff943fd63fbd4bed20
def s247H7 (_ : Nat) : Nat := 0xa50071895de300749a2c10928
def s247D7 (_ : Nat) : Nat := 0x907151209408c18b0cc2d49a8e2b729fae2203f7a9461fbd4930fdac7a95fd578c27f33a617b41f52
def s247H6 (_ : Nat) : Nat := 0xec148c01
def s247D6 (_ : Nat) : Nat := 0x28cef5299d309ed78d4a30
def s247L : Nat → Packing
  | 9 => (1,0,4,0,0,1,0,s247D9)
  | 8 => (8,1,4,0,0,8,0,s247D8)
  | 7 => (6,2,4,0,0,7,0,s247D7)
  | 6 => (2,3,4,0,0,3,0,s247D6)
  | _ => emptyPacking
def s247I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 4 14 3 8 3 1 s247H8 (mixTag h)
  | 8,h => lookupWord 4 12 1 8 3 1 s247H7 (mixTag h)
  | 7,h => lookupWord 2 5 1 6 1 1 s247H6 (mixTag h)
  | _,_ => none
def s247 : Forest := ⟨247,9,s247S,s247C,[[],[116]],s247L,s247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_9_0 : block s247 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_9 : block s247 9 0 1 = true := bs247_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_8_0 : block s247 8 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_8_2 : block s247 8 2 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_8 : block s247 8 0 8 = true := (@block_merge s247 8 0 2 6 bs247_8_0 bs247_8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_7_0 : block s247 7 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_7_2 : block s247 7 2 4 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_7 : block s247 7 0 6 = true := (@block_merge s247 7 0 2 4 bs247_7_0 bs247_7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_6_0 : block s247 6 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs247_6 : block s247 6 0 2 = true := bs247_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts247 : checkedTables s247 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs247_6
  · exact bs247_7
  · exact bs247_8
  · exact bs247_9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs247 : graphValid s247 (boundsBefore es239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls247 : Lower true (vars 247) (graphGoal 247) 10 := lower_forest (g:=s247) (i:=0) (hints:=1050196) (before_sound es239 vs239) gs247 ts247 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es247 := extendKnown es239 10 [(247,[]),(471,[33,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs247 : Known true es247 := extendKnown_ok (m:=247) vs239 ls247 (by decide +kernel)
def s251S := sampleAt 133 #[(0x40443000900ffd5b26700ff33cc03fff,0x4100990a42c090230a0b11cc49513),(0x8180cb00e00c02a4db9ff00ccffff300,0x804b45e46d18004a9474644551f34a),(0x0,0x0),(0x1326270c00fff00338e3e0000f0f003c00,0x1122250c1db1f07b38e3e2e2ef0f0dbc3a),(0x1c38380fff000003c0fc00000ff0003fff,0x1428280d16014053c0fc02424ee0092a2c),(0x1fc03ff000000003ff0000000fffffc000,0x1fc03fb098098263ff000a8a8bbaae00b0),(0x1fffc00000000003fffffffff000000000,0x1fff400090090243f6b54b0b00002800a0),(0x1ffffffffffffffc000000000000000000,0xad5d2e2e04e0b8000000c0c00003000c0),(0x0,0x0)]
def s251C : List ColumnInfo := [(32,0,219,512,8)]
def s251D8 (_ : Nat) : Nat := 0x17f
def s251L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s251D8)
  | _ => emptyPacking
def s251I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s251 : Forest := ⟨251,8,s251S,s251C,[[]],s251L,s251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs251_8_0 : block s251 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs251_8 : block s251 8 0 1 = true := bs251_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts251 : checkedTables s251 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs251_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs251 : graphValid s251 (boundsBefore es247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls251 : Lower true (vars 251) (graphGoal 251) 9 := lower_forest (g:=s251) (i:=0) (hints:=1077332) (before_sound es247 vs247) gs251 ts251 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es251 := extendKnown es247 9 [(251,[]),(505,[130,112,129,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs251 : Known true es251 := extendKnown_ok (m:=251) vs247 ls251 (by decide +kernel)
def s254S := sampleAt 130 #[(0x0,0x0),(0x413003eb300cc00926739c03fffffff,0x110016b322cc88002318c888d55523),(0x181cb3333c00f0036db9ce7fc0333300,0x814b3333c66f19924a94a59d9b3336a),(0x26260c3c3c000ffff8e3e0f80003c3c00,0x22220c143c00e543f8e3e0f8585bc3c1a),(0x38380fc03ffff0003f03ff000003fc000,0x28280d403d50f003bf03ff00585bfc01a),(0x3fc00fffc00000003ffc00000003fffff,0x3fc00ffe800cc0333ffc00035352aaadc),(0x3ffff000000000003ffffffffffc00000,0x3f7ea000000880222db54a52626000090),(0x3fffffffffffffffc0000000000000000,0x15d5f2abc2af0abc000000038380000e0),(0x0,0x0)]
def s254C : List ColumnInfo := [(16,0,238,512,6)]
def s254D6 (_ : Nat) : Nat := 0x17f
def s254L : Nat → Packing
  | 6 => (1,0,1,0,0,1,0,s254D6)
  | _ => emptyPacking
def s254I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s254 : Forest := ⟨254,6,s254S,s254C,[[],[67],[97,82],[97,82,67]],s254L,s254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs254_6_0 : block s254 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs254_6 : block s254 6 0 1 = true := bs254_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts254 : checkedTables s254 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs254_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs254 : graphValid s254 (boundsBefore es251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls254 : Lower true (vars 254) (graphGoal 254) 7 := lower_forest (g:=s254) (i:=0) (hints:=823621200) (before_sound es251 vs251) gs254 ts254 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es254 := extendKnown es251 7 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs254 : Known true es254 := extendKnown_ok (m:=254) vs251 ls254 (by decide +kernel)
def s319S := sampleAt 130 #[(0xaac0000facc033003333cccc03fffff,0xaad24005acd2b34a1111cccd4955553),(0x403002ccccf003c00ccccffffff33300,0x40330eccccf31bcc6444455571f333ca),(0x28cc0030f0f0003ffff0f0f0f003c3c00,0x28cc06f050f007951ff0f0f0f0dbc3c3a),(0x30f0003f00ffffc000ff00ff0003fc000,0x30f006f500f547c01eff00ff00dbfc03a),(0x3f00003fff00000000ffff000003fffff,0x3f0024bffa00250094eeee000292aaaac),(0x3fffffc00000000000fffffffffc00000,0x39fc47000000060018bbbbaaa8e000030),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffffff000000000000000,0x603b80aaf0ab82ae00000000300000c0)]
def s319C : List ColumnInfo := [(8,0,311,512,6)]
def s319D6 (_ : Nat) : Nat := 0x17f
def s319L : Nat → Packing
  | 6 => (1,0,1,0,0,1,0,s319D6)
  | _ => emptyPacking
def s319I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s319 : Forest := ⟨319,6,s319S,s319C,[[],[50],[64],[64,50]],s319L,s319I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs319_6_0 : block s319 6 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs319_6 : block s319 6 0 1 = true := bs319_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts319 : checkedTables s319 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs319_6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs319 : graphValid s319 (boundsBefore es254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls319 : Lower true (vars 319) (graphGoal 319) 7 := lower_forest (g:=s319) (i:=0) (hints:=8591018068) (before_sound es254 vs254) gs319 ts319 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es319 := extendKnown es254 7 [(319,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs319 : Known true es319 := extendKnown_ok (m:=319) vs254 ls319 (by decide +kernel)
def s367S := sampleAt 126 #[(0x9d5602b3019808e3a4e8080ff99980,0x8d5696b34d9a6861a46a6a64f999aa),(0xe018033c01e00104c7300ff01fffff,0xa018873c45e22000c5322a344aaaa3),(0x1066003c001fffe38f83ff0001e1e00,0x66017c00ca87a28e8387060de1e0a),(0x26078003fffe000fc0ffc000001fe000,0x22078037d51e00efc0ffc16162dfe01a),(0x0,0x0),(0x3807fffc0000000fff000000001fffff,0x2807e238001800cfff0001414295551c),(0x3ff800000000000fffffffffffe00000,0x3f50012000900485961285858b000050),(0x0,0x0),(0x3ffffffffffffff00000000000000000,0x15f81dc02ae15700000006060c000060)]
def s367C : List ColumnInfo := [(8,0,359,512,8)]
def s367D8 (_ : Nat) : Nat := 0x17f
def s367L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s367D8)
  | _ => emptyPacking
def s367I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s367 : Forest := ⟨367,8,s367S,s367C,[[],[48,81,134]],s367L,s367I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs367_8_0 : block s367 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs367_8 : block s367 8 0 1 = true := bs367_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts367 : checkedTables s367 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs367_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs367 : graphValid s367 (boundsBefore es319) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls367 : Lower true (vars 367) (graphGoal 367) 9 := lower_forest (g:=s367) (i:=0) (hints:=8591017558) (before_sound es319 vs319) gs367 ts367 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es367 := extendKnown es319 9 [(367,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs367 : Known true es367 := extendKnown_ok (m:=367) vs319 ls367 (by decide +kernel)
def s375S := sampleAt 148 #[(0x14c2b0003f30006306801003ff33cc00ffff,0x442b22417322821029152288b11cc925493),(0x6710c00333c000849b001ffc00ccffffcc00,0x2510c60f33c618008b30d61d86445587cd8a),(0x88230003c3ffff38e3ffe00000f0f000f000,0x23006d41507d28a383e0781ef0f036f03a),(0x0,0x0),(0xcf03c0003fc0003c0fc00000000ff0000ffff,0xcf03c0ccbe80cd3c0fc6a8d5354ee0364ab6c),(0xf003ffffc000003ff0000000000ffffff0000,0x5002710f00000e3ff000b016058bba8780070),(0xfffc00000000003ffffffffffff0000000000,0xfda800880000882d6544c0982600002400240),(0x0,0x0),(0xffffffffffffffc0000000000000000000000,0xaffd8ef02beaf000000700e03800003800380)]
def s375C : List ColumnInfo := [(0,16,358,513,8),(2,0,373,512,7),(2,32,85,768,5),(4,0,371,512,7),(4,256,83,544,5),(17,0,358,512,7),(32,0,343,512,7),(36,256,83,512,4),(64,0,311,512,6),(256,0,119,512,7),(258,32,85,512,4),(290,0,85,512,4),(292,0,83,512,4)]
def s375D9 (_ : Nat) : Nat := 0x272ca67f
def s375H8 (_ : Nat) : Nat := 0x4bcb3872fc806400aa000006f941cd800507801046
def s375D8 (_ : Nat) : Nat := 0x5880130b50a1303548b2c126a9166805032d4ea4410129eaa3c0d512cb008ca6aa8e81a4062d54884bad909b399545a00ffd47fd64ff587fd21ff547fd41ff553ff54
def s375H7 (_ : Nat) : Nat := 0x5e6d321da0000057546c2000032cdacd4471a8a0e0a0a9c664d3a03033e
def s375D7 (_ : Nat) : Nat := 0x180562c4000080c40011a8b0d4586a2dd76c539cf5c33444405fe57487fab0ea37f55d21bfc4eaa5fe27547faa8a437f49f54bfa4fa8cfd67d52fb0baa96f91d61
def s375L : Nat → Packing
  | 9 => (1,0,4,0,0,1,0,s375D9)
  | 8 => (8,1,4,0,0,9,0,s375D8)
  | 7 => (11,2,4,0,0,7,0,s375D7)
  | _ => emptyPacking
def s375I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 5 19 3 8 3 1 s375H8 (mixTag h)
  | 8,h => lookupWord 7 23 4 9 4 1 s375H7 (mixTag h)
  | _,_ => none
def s375 : Forest := ⟨375,9,s375S,s375C,[[],[33,133]],s375L,s375I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_9_0 : block s375 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_9 : block s375 9 0 1 = true := bs375_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_8_0 : block s375 8 0 8 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_8 : block s375 8 0 8 = true := bs375_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_7_0 : block s375 7 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_7_3 : block s375 7 3 8 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs375_7 : block s375 7 0 11 = true := (@block_merge s375 7 0 3 8 bs375_7_0 bs375_7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts375 : checkedTables s375 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs375_7
  · exact bs375_8
  · exact bs375_9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs375 : graphValid s375 (boundsBefore es367) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls375 : Lower true (vars 375) (graphGoal 375) 10 := lower_forest (g:=s375) (i:=0) (hints:=8590984788) (before_sound es367 vs367) gs375 ts375 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es375 := extendKnown es367 10 [(375,[]),(487,[116]),(494,[134,81,48,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs375 : Known true es375 := extendKnown_ok (m:=375) vs367 ls375 (by decide +kernel)
def s379S := sampleAt 138 #[(0x930ac001f98015b267007fccf3007fff,0x110ac920b9928090232512c473292a53),(0x31c4300199e002a4db9ff80333fffe600,0x1144318799e318004a963b1911563e6ca),(0x0,0x0),(0x24c608c001e1ffff38e3e00003c3c007800,0x244208c036a0a87f38e3e170bbc3c1b783a),(0x38f80f0001fe0003c0fc000003fc0007fff,0x38f80f0325f40653c0fc0d2693b80d255ac),(0x3f000ffffe000003ff00000003fffff8000,0x2d0009c438000063ff000140a2eea1c0030),(0x3ffff00000000003fffffffffc000000000,0x3feea00220000443f6b54984c0000900120),(0x0,0x0),(0x3ffffffffffffffc0000000000000000000,0x12bdf63bc15f578000000e0700000e001c0)]
def s379C : List ColumnInfo := [(16,0,363,512,7)]
def s379D7 (_ : Nat) : Nat := 0x17f
def s379L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s379D7)
  | _ => emptyPacking
def s379I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s379 : Forest := ⟨379,7,s379S,s379C,[[],[128,67,101]],s379L,s379I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs379_7_0 : block s379 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs379_7 : block s379 7 0 1 = true := bs379_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts379 : checkedTables s379 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs379_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs379 : graphValid s379 (boundsBefore es375) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls379 : Lower true (vars 379) (graphGoal 379) 8 := lower_forest (g:=s379) (i:=0) (hints:=12885983316) (before_sound es375 vs375) gs379 ts379 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es379 := extendKnown es375 8 [(379,[]),(478,[114,97,82,134,112,49]),(506,[114,113,101,135,16,100,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs379 : Known true es379 := extendKnown_ok (m:=379) vs375 ls379 (by decide +kernel)
def s381S := sampleAt 125 #[(0x8c156001d80c0133993380fffffff,0x4156880da2d10118811a246aaaa5),(0x0,0x0),(0x112998026600ffedce6dcff0199980,0x29981a260643a54a254870d9998c),(0x126631e00387ff0071f071f0001e1e00,0x122231e03a868f0771f071f162de1e1c),(0x1c783e0003f800007e007e00001fffff,0x1c783e0133f04c267e007e054a95555a),(0x1f803ffffc0000007fff8000001fe000,0x16803bfa3c000e077fff800162dfe01c),(0x1fffc000000000007fffffffffe00000,0x1fff8001200048245aa55aa58b000050),(0x0,0x0),(0x1fffffffffffffff8000000000000000,0x95dc405c15970b8000000060c000060)]
def s381C : List ColumnInfo := [(32,0,349,512,7)]
def s381D7 (_ : Nat) : Nat := 0x17f
def s381L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,s381D7)
  | _ => emptyPacking
def s381I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s381 : Forest := ⟨381,7,s381S,s381C,[[],[83]],s381L,s381I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs381_7_0 : block s381 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs381_7 : block s381 7 0 1 = true := bs381_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts381 : checkedTables s381 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs381_7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs381 : graphValid s381 (boundsBefore es379) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls381 : Lower true (vars 381) (graphGoal 381) 8 := lower_forest (g:=s381) (i:=0) (hints:=8598357508) (before_sound es379 vs379) gs381 ts381 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es381 := extendKnown es379 8 [(381,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs381 : Known true es381 := extendKnown_ok (m:=381) vs379 ls381 (by decide +kernel)
def s439S := sampleAt 150 #[(0x3c2b0001f980003300007fffccf3001ffff,0x142b2120b990a0110084aa42c473224a913),(0x133310c00199e0000cccc006600333ffff9800,0x133310ce4799e726044cfa2e7d19115e8f9f4a),(0x203c230001e1ffffcf0f00078003c3c001e000,0x20142300f6a0a87fcf0f06ef837bc3c1ede0fa),(0x0,0x0),(0x3c03c0001fe0000f00ffff80003fc0001ffff,0x1403c0425f40214500550b00853b80449522c),(0x3c003ffffe000000fff000000003fffffe0000,0x24002710b8000058fbb004c00262eea17000b0),(0x0,0x0),(0x3fffc00000000000fffffffffffc0000000000,0x3ebe8008c0000460aeeaa705538000098004c0),(0x3fffffffffffffff0000000000000000000000,0x1bebd8ef015f5780000038001c00000e000700)]
def s439C : List ColumnInfo := [(0,16,294,641,6),(0,128,294,529,6),(16,0,423,512,6),(34,0,405,512,6),(128,0,311,512,6),(260,0,179,512,6)]
def s439D8 (_ : Nat) : Nat := 0x50ba67f
def s439L : Nat → Packing
  | 8 => (1,0,3,0,0,1,0,s439D8)
  | _ => emptyPacking
def s439I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s439 : Forest := ⟨439,8,s439S,s439C,[[],[116],[64],[64,112],[112,64],[112],[33,133],[33,116,133],[64,33,133],[64,33,112,133],[112,33,64,133],[112,33,133]],s439L,s439I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs439_8_0 : block s439 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs439_8 : block s439 8 0 1 = true := bs439_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts439 : checkedTables s439 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs439_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs439 : graphValid s439 (boundsBefore es381) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls439 : Lower true (vars 439) (graphGoal 439) 9 := lower_forest (g:=s439) (i:=0) (hints:=8590985300) (before_sound es381 vs381) gs439 ts439 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es439 := extendKnown es381 9 [(439,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs439 : Known true es439 := extendKnown_ok (m:=439) vs381 ls439 (by decide +kernel)
def s443S := sampleAt 147 #[(0x3c2b0003f3000430002400fff33cc00ffff,0x142b22417322841022648a48b11cc925493),(0x4cb10c00333c0000cb003800c00ccffffcc00,0x4cb10ce0f33ce1804be17b86f86445787cf8a),(0x0,0x0),(0xc230003c3fffe70c003fff000f0f000f000,0x23006d41507e50c076c1f01ef0f036f03a),(0xf03c0003fc000380fffc000000ff0000ffff,0x503c044be8045280d458114114ee0124a92c),(0x7003ffffc000003ff0000000000ffffff0000,0x1002710f00000e3fb0160058058bba8780070),(0x0,0x0),(0x7ffc00000000003ffffffffffff0000000000,0x7ae8008800008812e2981260a600002400240),(0x7fffffffffffffc0000000000000000000000,0x6ffd8ef02beaf00000e003803800003800380)]
def s443C : List ColumnInfo := [(0,2,409,544,8),(1,0,442,512,7),(2,256,145,552,6),(16,0,427,512,7),(16,1,298,640,5),(34,0,409,512,7),(128,1,298,528,5),(128,16,298,513,5),(145,0,298,512,4),(264,0,179,512,6)]
def s443D9 (_ : Nat) : Nat := 0x4272a67f
def s443H8 (_ : Nat) : Nat := 0xf7927255854ec00868c
def s443D8 (_ : Nat) : Nat := 0x1495498b008ea641a03a9d05808292d5072d528218e5aa126a582643c2300ff483fd50ff4c3ff50ffd4bfd52
def s443H7 (_ : Nat) : Nat := 0xd66e00ee
def s443D7 (_ : Nat) : Nat := 0x186a2882fe93ea1778dd50
def s443L : Nat → Packing
  | 9 => (1,0,4,0,0,1,0,s443D9)
  | 8 => (6,1,4,0,0,8,0,s443D8)
  | 7 => (2,2,4,0,0,5,0,s443D7)
  | _ => emptyPacking
def s443I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 3 12 2 8 3 1 s443H8 (mixTag h)
  | 8,h => lookupWord 2 5 1 6 1 1 s443H7 (mixTag h)
  | _,_ => none
def s443 : Forest := ⟨443,9,s443S,s443C,[[],[64]],s443L,s443I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_9_0 : block s443 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_9 : block s443 9 0 1 = true := bs443_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_8_0 : block s443 8 0 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_8 : block s443 8 0 6 = true := bs443_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_7_0 : block s443 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_7_1 : block s443 7 1 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs443_7 : block s443 7 0 2 = true := (@block_merge s443 7 0 1 1 bs443_7_0 bs443_7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts443 : checkedTables s443 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs443_7
  · exact bs443_8
  · exact bs443_9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs443 : graphValid s443 (boundsBefore es439) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls443 : Lower true (vars 443) (graphGoal 443) 10 := lower_forest (g:=s443) (i:=0) (hints:=12885979220) (before_sound es439 vs439) gs443 ts443 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es443 := extendKnown es439 10 [(443,[]),(499,[116,64,99,129]),(501,[116,64,99,130,133,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs443 : Known true es443 := extendKnown_ok (m:=443) vs439 ls443 (by decide +kernel)
def s445S := sampleAt 132 #[(0xc156000ec0300024f000900ffffffff,0x41564406c8b22024502292248d55525),(0x0,0x0),(0x8329980133003ffb38cb00e00c0333300,0x8129981d130390fb38cb16e16c5b3331c),(0x431e001c3ffc00c3f0c00fff003c3c00,0x31e00d4341c06c2d0c06b0701bc3c0c),(0x183e0001fc00000fc00fff000003fffff,0x83e0089f811044d400d45044112aaa4a),(0xe03ffffe0000000ffff000000003fc000,0xa03bfa1e000380effff01601605bfc01c),(0x0,0x0),(0xffc000000000000ffffffffffffc00000,0xf78001100022088292a298498a6000090),(0xfffffffffffffff000000000000000000,0x5ec405e0acbc2f000000e00e0380000e0)]
def s445C : List ColumnInfo := [(32,0,413,512,8)]
def s445D8 (_ : Nat) : Nat := 0x17f
def s445L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s445D8)
  | _ => emptyPacking
def s445I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s445 : Forest := ⟨445,8,s445S,s445C,[[],[64],[82],[64,82]],s445L,s445I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs445_8_0 : block s445 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs445_8 : block s445 8 0 1 = true := bs445_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts445 : checkedTables s445 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs445_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs445 : graphValid s445 (boundsBefore es443) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls445 : Lower true (vars 445) (graphGoal 445) 9 := lower_forest (g:=s445) (i:=0) (hints:=8598353924) (before_sound es443 vs443) gs445 ts445 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es445 := extendKnown es443 9 [(445,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs445 : Known true es445 := extendKnown_ok (m:=445) vs443 ls445 (by decide +kernel)
def s463S := sampleAt 133 #[(0x103c4eb300cc00064900fffe93a0100ff,0x1446b322cc88024922548e91a452223),(0x6b30733c00f0009b8e00cc031cc01ff00,0x2b30533c6af1a88b8e72cdcb14ce57372),(0x83c083c000fffce3f000f003e0ffe0000,0x14003c00a542ca3f012f04ba0e261212),(0x10c0303ffff000303ffff0003ff0000000,0x103d507001902db07001bff0140a0a),(0x0,0x0),(0x0,0x0),(0x1f003fc00000003fc00000003fffffffff,0x1d003a80084021354008402104a1188c8c),(0x1fffc0000000003fffffffffc000000000,0x1ffe80000c80322fd24d8ab60001a0d0d0),(0x1fffffffffffffc0000000000000000000,0x1febefc2af0abc00000e00380001c0e0e0)]
def s463C : List ColumnInfo := [(2,0,461,512,8)]
def s463D8 (_ : Nat) : Nat := 0x17f
def s463L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s463D8)
  | _ => emptyPacking
def s463I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s463 : Forest := ⟨463,8,s463S,s463C,[[],[32,135]],s463L,s463I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs463_8_0 : block s463 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs463_8 : block s463 8 0 1 = true := bs463_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts463 : checkedTables s463 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs463_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs463 : graphValid s463 (boundsBefore es445) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls463 : Lower true (vars 463) (graphGoal 463) 9 := lower_forest (g:=s463) (i:=0) (hints:=8589964902) (before_sound es445 vs445) gs463 ts463 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es463 := extendKnown es445 9 [(463,[]),(493,[84,32,134,118,48,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs463 : Known true es463 := extendKnown_ok (m:=463) vs445 ls463 (by decide +kernel)
def s475S := sampleAt 148 #[(0x40f0930fcc00010002400fff267003ffffff,0x501105cc22000086422423023088235423),(0x1b2c31cccf00006b003800c00db9ffc00cc00,0xb2c114ccf16602b597966d664a959d66cd6a),(0x0,0x0),(0x2030c60f0ffff98c003fff000e3e00000f000,0x42050540f88c036c0f00ee3e05816f01a),(0xc3c0f80ff0000e0fffc000000fc000000ffff,0x4140f80fa00cca0d3380cc0ccfc0350d4a8dc),(0x0,0x0),(0xfc00fff000000ff0000000000ffffffff0000,0xf400eea000288fd0a20288288b54a62980290),(0xffff000000000ffffffffffff000000000000,0xbeba000000300572c41310b10000c03000300),(0xfffffffffffff000000000000000000000000,0xffffbdfafabf0000f803e03e0000f83e003e0)]
def s475C : List ColumnInfo := [(0,2,409,576,8),(0,256,211,520,8),(1,0,474,512,6),(16,0,459,512,7),(66,0,409,512,7),(128,0,347,512,6),(264,0,211,512,7)]
def s475D9 (_ : Nat) : Nat := 0x5cc57f
def s475H8 (_ : Nat) : Nat := 0x36c008c02e000010353c773480000024
def s475D8 (_ : Nat) : Nat := 0x4a83261f12654c19338920265c8d8a98932465ce4c492a3761a691ed48a403fe30ff943fc50ff543fd30
def s475H7 (_ : Nat) : Nat := 0xc0419281e530d02c3263369dca6f4e018004789144e0e0071c00505451a262b0825b5949001220d4208840
def s475D7 (_ : Nat) : Nat := 0x1462184030e42028c4028c4228800000a1e78452633cf132e170a5e7845270ebe9645f5cd552cb43c13ebc39b4a81b8c807f9508c3fd28261f7d4e30fbc6ea85fe574c2fe9bca1fe54130bfc6ea85fd57943eea9a617f55d30bfaaf187dc37542fe9b8a1de54050ef6a1285de37542f6938a1774dc50
def s475H6 (_ : Nat) : Nat := 0xd1a914da7a000001059140524a90000110003c
def s475D6 (_ : Nat) : Nat := 0x1431000000000e748de6543ca140f5a3854050f5a3554230f593554130f583854050d7a7854050d79504dc509de3855d30bd908d4e3097a7854050d59504dc50
def s475H5 (_ : Nat) : Nat := 0xf4039462395c2
def s475D5 (_ : Nat) : Nat := 0xcd1ea2832b112a826e28656a25504dc50cac1ccf0a80a195a399e1501432b4713c2a0286560e27854050
def s475L : Nat → Packing
  | 9 => (1,0,3,0,0,1,0,s475D9)
  | 8 => (5,1,3,0,0,8,0,s475D8)
  | 7 => (19,2,3,0,0,8,0,s475D7)
  | 6 => (10,3,3,0,0,6,0,s475D6)
  | 5 => (6,4,3,0,0,5,0,s475D5)
  | _ => emptyPacking
def s475I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 3 16 2 8 3 1 s475H8 (mixTag h)
  | 8,h => lookupWord 9 30 5 10 5 1 s475H7 (mixTag h)
  | 7,h => lookupWord 4 17 2 9 4 1 s475H6 (mixTag h)
  | 6,h => lookupWord 2 7 2 7 3 0 s475H5 (mixTag h)
  | _,_ => none
def s475 : Forest := ⟨475,9,s475S,s475C,[[],[112,129,99]],s475L,s475I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_9_0 : block s475 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_9 : block s475 9 0 1 = true := bs475_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_8_0 : block s475 8 0 5 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_8 : block s475 8 0 5 = true := bs475_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_7_0 : block s475 7 0 5 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_7_5 : block s475 7 5 14 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_7 : block s475 7 0 19 = true := (@block_merge s475 7 0 5 14 bs475_7_0 bs475_7_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_6_0 : block s475 6 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_6_2 : block s475 6 2 8 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_6 : block s475 6 0 10 = true := (@block_merge s475 6 0 2 8 bs475_6_0 bs475_6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_5_0 : block s475 5 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs475_5 : block s475 5 0 6 = true := bs475_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts475 : checkedTables s475 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs475_5
  · exact bs475_6
  · exact bs475_7
  · exact bs475_8
  · exact bs475_9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs475 : graphValid s475 (boundsBefore es463) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls475 : Lower true (vars 475) (graphGoal 475) 10 := lower_forest (g:=s475) (i:=0) (hints:=12884930660) (before_sound es463 vs463) gs475 ts475 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es475 := extendKnown es463 10 [(475,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs475 : Known true es475 := extendKnown_ok (m:=475) vs463 ls475 (by decide +kernel)
def s477S := sampleAt 142 #[(0x20c460ec0180004001200ffe4ce00ffffff,0x40206c85908000832424860464221aa43),(0x0,0x0),(0x4308933001ffc1ac01c00c01b73ff006600,0x10011302c85c0ac4bc26c4c9522713662a),(0x84331c3ffe00263001fff001c7c00007800,0x1114341e03a2301b60f01dc7c160b781a),(0x3183c1fc00000383ffe000001f8000007fff,0x1083c1f81182328351c08c119f80944a549c),(0x0,0x0),(0x3e03fe00000003fc000000001fffffff8000,0x3e03fc00310623f43101883116a998cc0190),(0x3ffc0000000003ffffffffffe00000000000,0x2f7800002204415ca60930a6000120900120),(0x3ffffffffffffc0000000000000000000000,0x3feeeeacbc1780003801c0380001c0e001c0)]
def s477C : List ColumnInfo := [(1,0,476,512,7),(1,16,332,640,5),(1,64,408,516,5),(5,64,408,512,4),(8,4,145,832,6),(12,256,209,512,5),(16,0,461,512,8),(20,0,457,512,5),(64,256,145,524,6),(68,0,409,512,7),(69,0,408,512,4),(72,0,405,512,6),(72,4,145,768,5),(72,256,145,516,5),(81,0,396,512,4),(128,0,349,512,7),(128,8,85,768,5),(128,16,332,513,5),(129,16,332,512,4),(145,0,332,512,4),(152,0,325,512,4),(256,4,153,576,6),(264,0,213,512,7),(268,0,209,512,5),(320,4,153,512,5),(324,0,153,512,5),(384,8,85,512,4)]
def s477D10 (_ : Nat) : Nat := 0x359237f
def s477H9 (_ : Nat) : Nat := 0x3f850019168c095c241095af00226003877080000169c3464bbbe00326c33800e2d670026b3410a80e2a003c891a6100044000c020010359793
def s477D9 (_ : Nat) : Nat := 0xf006982409350a9e42e723b06300a54f1885ce0760d3016780488930638854644f58968350061e34c02c40a73c018264d38941e312226c18f1a601740c590a8c910780bed4a6a3953c02115c6da94d6a1e02e31892c83c11994cd00941e34c01223075a640c5ca4ccb9a43c91834cc58041e48cb1098a7e1744bf6d4a1e5888dfa715844f50834ca4204640bc00ff50bfe30ff943fd31ff143fd60ff503fe10ff483fd50ff4c3fd32ff903fd10ff487fd61ff883fe60
def s477H8 (_ : Nat) : Nat := 0xe993b9d39ff2b461020e697bba392c3e6740fc50629190a0d457deebb3a548b6b6c7444e052e2c52eaee39a87702a4bb7d43516c352bdd2dad07edb84ca35aa4b50d7a822cf822000a3c000341808000c71d03f135c495e6d8bebdaff6f5cd29cb1cd3495d192bbc33b8a29211b89d4000fd979a000338506c0b702b116150003dd9e605b78304a48d156f58ab48b013df07c8cec911aa8b000519b46ad6a1bb5a6ce00068ff9570acec7e913ae59000086b6490c55cb23f2f7ef1e1e52f26fdc0e8e1062a1c01056474c2000000000d8700094f0000005ad0c8000da0000000404724bde000f963128da9e52492c1000345ed2048f4b914000000225cdb8d30008acc094317378e7a18ba10002ab601d1d000000b9ef8ae00f6a0004c6927dbf3e2000b65791000c4c00081e52c000000ca6836a60ce4e66e9835303f9a9fcab9976bad573e032028d6d568555c40c6ec178b24511812627cb4c7a30b5f61fc3304d394b4e842d631810d319d3800464f254000174335c03400fb1010000f38104e0d000410d14924f0653401d90032074814822c6347000710023000
def s477D8 (i : Nat) : Nat := #[0x821c3004498e3090c548953002c409947140231e5449320620508905801c04800893193043862c702264165080c98120352481932368c40b842922050991b152e409253150648c4c88e3172a0c80088e194264465ca831c94c181952261640518195105cada3152e40b253002604b24a831b68c5c8114c62e549954c62644830d0800220443133110158d1048d320c83019a2646c541092668c000860638a44988a8c2630c4498c3921562c04a1089a06300447d63450430bd62452cd890c984376d24c9d88931882a088171c6224c43c886264ac98a8f042409a4360c04603346146870ca822020b912674c082060268c443033442a003080440b934110c10a8329424220504001091c48a0820f2468a403082f2499860d2432a24d0e2651e008932142a089090c68e384102c289188931072a48690b0c2e689983031848d19316185cd143111a0c808d131912622a40888045c99c18c6c6884430c344eda498c985340c714a8c2430a3498c3921021c21a0ca0c712149223864498810e1080a4864498810e10e34480032861c00792340ca1f310105c998115184eda498c700283c89a064d020985195263062098518e283c880340c9a399f9538eb88381b77b7136ab6435a350349b41739330f2a723f1bb1530eb066fc6f42ebee3add2d4ece6c7ec16b5ab0ea6e9ce92e8c68427a271e6d261659250e48a3ce32e2e227a2121c61420da039f99f31f01e7de15d59d0dc89b95ad9a719998dd8597656c567962d58d4ed4313c93292a51cd1110c5040fbcf00e60ddcd74d28c50bccb48ae0a409d89709248d88708247bc7707246bc67062456849040c38832022c1c415c0f4003fea12a1ff55120ffa84987fe37483feb2261ff58150ffa80907fd50503feb0261ff54630ffaa0907fd32503fe8aca1ff54a30ffa86907fd30483ffa8281ffd4940ffaa4a07fd53483fe8baa1ff48630ffa4ea87fd21943fea8221ff54530ffac3187fd30443fea9261ff58650ffea6887fe47483feb08a1ff48550ffaa6887ff50443fe90a61ff58550ffac2987ed42483fca8461fe94120f7ac9205fd57882ff13aa1ef4d140bfa6f305fd57843fd282617f81d31bfc0e995fd474cbfca82417f8dd20fba47187df538c3ef1baa17f95d30bfcaea05fd37943fca82617f4dd20bfa4f285fe27502ff1baa1fb4c920bfa8e905fd57942ff2ba217f95d32bfa4e287dd434c3f6a92417f55e40fba86995fe274c3eea9a617f55d20bfc6ea05fd37842ff2bac1fb44920bfcae907ed32486ff23a41fe54220bfaae985fd578c2fe93c617f49e40fb86ea85fe474c2ff1ba217f55e60bfcae98dfd478c2ff23a657f51d30bfa6f205fd37142fea3ca17f8dd60bfa6f105fd47883bca80a1ded42509fcce90dbe47442ef1baa17b49c50bda4f305f517142fa8bcc1774dc50,0xa63021640a0880888e043201808d4990438c20016265044058c9][i]?.getD 0
def s477H7 (_ : Nat) : Nat := 0x1ec8fcb70adff3563f000008b65a2d001d4753f629246e1c577490be455a0d2cc176acf1cfeb0001046bdbcd987469eee5676f19b71aaf425dce5df3660a6f6a6aceb08db0002761a61e2efef00c640318e54003e357271ea8483494f2f0076e21303a42c75e104d8d27fac99651e0e928004c8000005df000002dd40c15d411ce416001b67d4eb5664b95124c362ae1ed180eea7de6b6de3141abce8077eaba6afd000001ec00000040802b16e10d180046069083b4b2c33450812d20c710100030100d
def s477D7 (_ : Nat) : Nat := 0x40204221c3c60804c044201110831829210308984082261008844c2cc0421308808898c4c2061020b3044c20020cb0b0aa41c4921560e484885026c2e2020e485a42220c2160bb044c200308001c1001844c2261b611141800883099002610e141a0313280444c4013089e488385044680c4cc1c28223406266f07a4e5f92df770d8f5ed4744cdf2ac7710c2efebc6dcb3eb2a9698a2e7e9c66c97e4a8d62886e067e5e475dca6f5a866d8e6057c5bd6a5955854d464e52c43cea394d82aca62448c1fc6a0d400f794554120f791854050afe6848630bdd28d4e30f793554120afe6848650ddd288dd50ddd428dd50afe6848550dbd6455e40f796154050b7e5859d50bbe4845d50fda3854120afe6848530bfa0845650bfa0851d50dbd5091d10ddd608dd509fc7855120bde3854140f7961d4250dbd3091d10dbf5391d10bde3854120dbd5391d10dbf5091d10bee084c921dde3745d50dbd644de40ded128dd20bfa0854d10dde3749d50fcd1248e30bf61859130bde3854110ddd188dd509fd5891d20bfa0850d20ddd218dd50fd83854120ddd618dd50ded6149c50ddd2351e309fe7854630ddc3745d50ddc3749d50ddd614dc50f5a3854050f5a3554230bda0848e30f59355413097e584dd20f583854050d7a78540509de3855d20d79504dc509de3855d30bd908d4e309de3855e4097a7854050d59504dc50
def s477H6 (_ : Nat) : Nat := 0x346105d2d3800cb502201f41168f8212890c00e540df4c0000310ac0b581fef6b3328a9f3a240acc694912aeb44565334baafa7000404250308d02028601d
def s477D6 (_ : Nat) : Nat := 0x1008882210016c100000208838602088386c90800030808220e180061098426109842610984261914521f0a7e3dde4ed66ab53e9a4aa1cce622a118702a0e038015787951550482af4f28c2a0285379a5218dd50ccf1bc908baa1bc912821238c2b3c72a848e88477e243749d508efc486e8baa1979189e150143ab232a826e286675923855e40acf24a311baa199c37921175432f2c33c2a02865e4667854050aae1ca0b2ba41d5961541371432b112a826e28656a25504dc50cac1ccf0a80a195a399e1501432b4713c2a0286560e27854050
def s477L : Nat → Packing
  | 10 => (1,0,5,0,0,1,0,s477D10)
  | 9 => (18,1,5,0,0,10,0,s477D9)
  | 8 => (114,2,5,0,0,12,0,s477D8)
  | 7 => (62,3,5,0,0,10,0,s477D7)
  | 6 => (23,4,5,0,0,9,0,s477D6)
  | _ => emptyPacking
def s477I : Nat → Nat → Option (Nat × Nat)
  | 10,h => lookupWord 11 42 4 10 5 1 s477H9 (mixTag h)
  | 9,h => lookupWord 70 241 6 12 7 1 s477H8 (mixTag h)
  | 8,h => lookupWord 36 123 6 11 6 1 s477H7 (mixTag h)
  | 7,h => lookupWord 13 42 6 10 5 1 s477H6 (mixTag h)
  | _,_ => none
def s477 : Forest := ⟨477,10,s477S,s477C,[[],[112,130,99]],s477L,s477I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_10_0 : block s477 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_10 : block s477 10 0 1 = true := bs477_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_9_0 : block s477 9 0 18 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_9 : block s477 9 0 18 = true := bs477_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_8_0 : block s477 8 0 10 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_8_10 : block s477 8 10 65 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_8_75 : block s477 8 75 39 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_8 : block s477 8 0 114 = true := (@block_merge s477 8 0 10 104 bs477_8_0 (@block_merge s477 8 10 65 39 bs477_8_10 bs477_8_75))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_7_0 : block s477 7 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_7_2 : block s477 7 2 12 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_7_14 : block s477 7 14 48 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_7 : block s477 7 0 62 = true := (@block_merge s477 7 0 2 60 bs477_7_0 (@block_merge s477 7 2 12 48 bs477_7_2 bs477_7_14))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_6_0 : block s477 6 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_6_6 : block s477 6 6 17 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs477_6 : block s477 6 0 23 = true := (@block_merge s477 6 0 6 17 bs477_6_0 bs477_6_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts477 : checkedTables s477 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs477_6
  · exact bs477_7
  · exact bs477_8
  · exact bs477_9
  · exact bs477_10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs477 : graphValid s477 (boundsBefore es475) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls477 : Lower true (vars 477) (graphGoal 477) 11 := lower_forest (g:=s477) (i:=0) (hints:=8589964804) (before_sound es475 vs475) gs477 ts477 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es477 := extendKnown es475 11 [(477,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs477 : Known true es477 := extendKnown_ok (m:=477) vs475 ls477 (by decide +kernel)
def s491S := sampleAt 140 #[(0x41e09d600cc002187200ffedce00ffe600,0xa08d645cc8c008324648e4c64623e64a),(0x1a580e1800f0004619c00c01273ff007fff,0xa580a18c1f1840209cc2d84052c3612ac3),(0x0,0x0),(0x2061306000ffff98e1fff001c7c00007800,0x110600d541e88a160f01dc7c160b781a),(0x0,0x0),(0xc381c07fff0001e0fe000001f8000007fff,0x408140621e0039e0f602c059f80341a543c),(0xfc01ff80000001ff00000001fffffff8000,0xf401f501180231fd00128251b29389c0130),(0xfffe0000000001fffffffffe00000000000,0xfff40001900321775c9b0b60001a0d001a0),(0xfffffffffffffe000000000000000000000,0xbf7eaf9de0abc000001c0380001c0e001c0)]
def s491C : List ColumnInfo := [(1,0,490,512,7),(2,0,489,512,7),(8,0,483,512,7),(32,0,459,512,7),(32,2,393,576,5),(64,0,427,512,7),(64,2,393,544,5),(67,0,424,512,4),(128,0,363,512,7),(128,1,298,576,5),(128,8,99,768,5),(256,0,235,512,7),(256,8,99,640,5)]
def s491D9 (_ : Nat) : Nat := 0xa7036477f
def s491H8 (_ : Nat) : Nat := 0x7040028a8da90320004471400f08da27000d4800c3000b64001280000315000898b36a8445400140d
def s491D8 (_ : Nat) : Nat := 0x1201288c31ca938ca1324e5c9e03fd21ff503fd10
def s491H7 (_ : Nat) : Nat := 0x4280000005cadc40cb5880000530
def s491D7 (_ : Nat) : Nat := 0x16f91d10
def s491L : Nat → Packing
  | 9 => (1,0,4,0,0,1,0,s491D9)
  | 8 => (3,1,4,0,0,6,0,s491D8)
  | 7 => (1,2,4,0,0,1,0,s491D7)
  | _ => emptyPacking
def s491I : Nat → Nat → Option (Nat × Nat)
  | 9,h => lookupWord 7 35 2 10 2 4 s491H8 (mixTag h)
  | 8,h => lookupWord 3 12 1 9 1 4 s491H7 (mixTag h)
  | _,_ => none
def s491 : Forest := ⟨491,9,s491S,s491C,[[],[49,133,118],[16,131,117],[16,128,48,83,101,118],[48,16,81,97,113,129],[48,81,134],[80,49,97,112,129,16],[80,97,135],[96,81,115,129,16,48],[96,113,83],[112,97,131,81,80,83],[112,129,99],[128,115,101],[128,113,49,80,99,101]],s491L,s491I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs491_9_0 : block s491 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs491_9 : block s491 9 0 1 = true := bs491_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs491_8_0 : block s491 8 0 3 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs491_8 : block s491 8 0 3 = true := bs491_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs491_7_0 : block s491 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs491_7 : block s491 7 0 1 = true := bs491_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts491 : checkedTables s491 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs491_7
  · exact bs491_8
  · exact bs491_9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs491 : graphValid s491 (boundsBefore es477) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls491 : Lower true (vars 491) (graphGoal 491) 10 := lower_forest (g:=s491) (i:=0) (hints:=12885979222) (before_sound es477 vs477) gs491 ts491 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es491 := extendKnown es477 10 [(491,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs491 : Known true es491 := extendKnown_ok (m:=491) vs477 ls491 (by decide +kernel)
def s502S := sampleAt 157 #[(0x0,0x0),(0xd3301b4400330000930fcc00099c003fffffff,0x53300945447351201105cd48808d48948d5523),(0x1203c2488003ffff31cccf00036e7ffc0033000,0x201400880d55037114ccf01992a419c19b306a),(0x0,0x0),(0x603c338f0003c000c60f0fffff8f8000003c000,0x2014338f0c37c30e4205054c3f8f8c58c5bc31a),(0x183c03c0ffffc0000f80ff00003f00000003ffff,0x8240140981b8006cf80fa00333f00350352a0dc),(0x1fc003ff000000000fff0000003ffffffffc0000,0x1f8003f6029200a48eea0002a22d52a62a600a90),(0x1ffffc00000000000fffffffffc0000000000000,0x1dfebc00031c00c70bdfafab3c00033833800ce0),(0x1ffffffffffffffff00000000000000000000000,0x17dbeabf67e02af800000003c00003c03c000f00)]
def s502C : List ColumnInfo := [(0,128,358,528,8)]
def s502D8 (_ : Nat) : Nat := 0x17f
def s502L : Nat → Packing
  | 8 => (1,0,1,0,0,1,0,s502D8)
  | _ => emptyPacking
def s502I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s502 : Forest := ⟨502,8,s502S,s502C,[[],[130,101],[33,133],[33,81,97,129],[81,134],[81,98,129,33],[97,82],[97,130,81,82],[129,33,82,101],[129,98],[116],[130,116,101],[33,116,133],[33,81,116,97,129],[81,116,134],[81,98,116,129,33],[97,82,116],[97,130,116,81,82],[129,33,116,82,101],[129,98,116]],s502L,s502I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs502_8_0 : block s502 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs502_8 : block s502 8 0 1 = true := bs502_8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts502 : checkedTables s502 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs502_8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs502 : graphValid s502 (boundsBefore es491) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls502 : Lower true (vars 502) (graphGoal 502) 9 := lower_forest (g:=s502) (i:=0) (hints:=9681962576) (before_sound es491 vs491) gs502 ts502 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es502 := extendKnown es491 9 [(502,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs502 : Known true es502 := extendKnown_ok (m:=502) vs491 ls502 (by decide +kernel)
def s255S := sampleAt 236 #[(0x801024330000092400ffff118e3041a4e801003ff3333cccc00ffffff,0x2411000099240a540b00861000a468150280b1111cccc12555413),(0x1026000ccacc00e3800cc00221049a6c73001ffc00ccccffffffcccc00,0x2200044acc85e3886cc86000008a2c5310d21c864444555487cccc8a),(0x6038b38f0cf000fc000f000cce38e38f83ffe00000f0f0f0f000f0f000,0x2028b38f0cf19dfc19ef19e44a28a28e83b3e6799ef0f0f0f1b6f0f1ba),(0x984c0c3f00f0000fffff0000f0fc0fc0ffc00000000ff00ff0000ff0000,0x88440c2d00f003db6c3f003ef0fc0fc0ffc0bc1785eff00ff0076ff007a),(0xe0700fc000fffff000000000ff000fff00000000000ffff000000ffffff,0xa0500d4000f5436000340034ff000fff0000a815054eeee000064aaa86c),(0xff800fffff00000000000000fffff00000000000000ffffffffff000000,0xff800fffbb00338003380338fffff0000006b0d6358bbbbaaab78000370),(0xfffff0000000000000000000fffffffffffffffffff0000000000000000,0xfdfd50000000220002200220bb5965551284c0982600000000240000240),(0xffffffffffffffffffffffff00000000000000000000000000000000000,0x57abf292ee0abc0493c0abc000000000000700e03800000000380000380),(0x0,0x0)]
def s255C : List ColumnInfo := [(8,0,247,512,10)]
def s255D10 (_ : Nat) : Nat := 0x2ff
def s255L : Nat → Packing
  | 10 => (1,0,1,0,0,1,0,s255D10)
  | _ => emptyPacking
def s255I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s255 : Forest := ⟨255,10,s255S,s255C,[[]],s255L,s255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs255_10_0 : block s255 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs255_10 : block s255 10 0 1 = true := bs255_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts255 : checkedTables s255 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs255_10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs255 : graphValid s255 (boundsBefore es502) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls255 : Lower true (vars 255) (graphGoal 255) 11 := lower_forest (g:=s255) (i:=0) (hints:=1078868) (before_sound es502 vs502) gs255 ts255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es255 := extendKnown es502 11 [(255,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs255 : Known true es255 := extendKnown_ok (m:=255) vs502 ls255 (by decide +kernel)
def s383S := sampleAt 236 #[(0x11302ab00000facc00cc00118e3041a4e801003ff3333cccc00ffffff,0x1102ab224005acc8acc8a00861000a469152288b1111cccc92555493),(0x61c100c002ccccf000f000221049a6c73001ffc00ccccffffffcccc00,0x214100c60eccccf186f186000008a2c5330d61d864444555587cccd8a),(0x820a3300030f0f0000ffffcce38e38f83ffe00000f0f0f0f000f0f000,0xa33006f050f001e541f44a28a28e8383e0781ef0f0f0f036f0f03a),(0x930c0c3c0003f00fffff0000f0fc0fc0ffc00000000ff00ff0000ff0000,0x91040c3c00ef500f543f003ef0fc0fc0ffc0bc1785eff00ff0076ff007a),(0xe3f00fc00003fff000000000ff000fff00000000000ffff000000ffffff,0xe3f00fc00ccbffa003340334ff000fff0006a8d5354eeee000364aaab6c),(0xfc000ffffffc000000000000fffff00000000000000ffffffffff000000,0xb4000e7f10f0000000380038fffff0000000b016058bbbbaaa878000070),(0xfffff0000000000000000000fffffffffffffffffff0000000000000000,0xffdea0000880000002200220bb5965551284c0982600000000240000240),(0x0,0x0),(0xffffffffffffffffffffffff00000000000000000000000000000000000,0x4afbf180ef00aaf0abc0abc000000000000700e03800000000380000380)]
def s383C : List ColumnInfo := [(8,0,375,512,10)]
def s383D10 (_ : Nat) : Nat := 0x2ff
def s383L : Nat → Packing
  | 10 => (1,0,1,0,0,1,0,s383D10)
  | _ => emptyPacking
def s383I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s383 : Forest := ⟨383,10,s383S,s383C,[[]],s383L,s383I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs383_10_0 : block s383 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs383_10 : block s383 10 0 1 = true := bs383_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts383 : checkedTables s383 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs383_10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs383 : graphValid s383 (boundsBefore es255) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls383 : Lower true (vars 383) (graphGoal 383) 11 := lower_forest (g:=s383) (i:=0) (hints:=8591017556) (before_sound es255 vs255) gs383 ts383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es383 := extendKnown es255 11 [(383,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs383 : Known true es383 := extendKnown_ok (m:=383) vs255 ls383 (by decide +kernel)
def s447S := sampleAt 242 #[(0xf02ab000007d6600330000486600000924007fffccccf333001ffffff,0x502ab212002d6642b32140482200109924852a42c4447333224aaa913),(0x132cc100c001666678003c0000019959800e3800660033333ffffff999800,0x132cc100ce47666679c9bce4c0008959f45e3ba367d191111555e8f999f4a),(0x200f0a330001878780003ffff671e19e000fc00078003c3c3c3c001e1e000,0x20050a3300f78287801f950ff671e19e0ddfc06f7837bc3c3c3c1ede1e0fa),(0x300c3c0001f807ffffc000187e01e0000fffff80003fc03fc0001fe0000,0xc3c0037a807aa07c003d85a01e001db6c0f8007bfc03fc006dfe003a),(0x3c00fc00001fff8000000001f8001fffff0000000003fffc000001ffffff,0x1400fc00425ffd0008500429a8001eaa160010a00853bbb800044955522c),(0x3c000ffffffe0000000000001ffffe000000000000003fffffffffe000000,0x24000e7f10b800000016000b1fff76000980004c00262eeeeaaa1700000b0),(0x0,0x0),(0x3ffff00000000000000000001fffffffffffffffffffc0000000000000000,0x3ebfa00008c000000118008c0525dc154e0492705538000000009800004c0),(0x3fffffffffffffffffffffffe000000000000000000000000000000000000,0x1bfaf180ef00557855e02af0000000007000038001c000000000e00000700)]
def s447C : List ColumnInfo := [(4,0,443,512,10)]
def s447D10 (_ : Nat) : Nat := 0x2ff
def s447L : Nat → Packing
  | 10 => (1,0,1,0,0,1,0,s447D10)
  | _ => emptyPacking
def s447I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s447 : Forest := ⟨447,10,s447S,s447C,[[],[64]],s447L,s447I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs447_10_0 : block s447 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs447_10 : block s447 10 0 1 = true := bs447_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts447 : checkedTables s447 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs447_10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs447 : graphValid s447 (boundsBefore es383) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls447 : Lower true (vars 447) (graphGoal 447) 11 := lower_forest (g:=s447) (i:=0) (hints:=8591013972) (before_sound es383 vs383) gs447 ts447 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es447 := extendKnown es383 11 [(447,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs447 : Known true es447 := extendKnown_ok (m:=447) vs383 ls447 (by decide +kernel)
def s479S := sampleAt 241 #[(0x400f044c00facc00660000080000249001ffff041a4e800800fffffffff,0x50044005acc21661080000010649084a843000a46842842086aaa843),(0x1b2cc1872ccccf00078000135660038e00198009a6c73000fff001999800,0xb2cc0852ccccf16b78b5811566b978e5cd9ae68a2c532e6ae75cd999aea),(0x200f020830f0f00007fffc1c678003f0001e000e38f83fff000001e1e000,0x500003050f000b2a05c14678097f004de026a28e8382702604de1e02a),(0x40300c303f00fffff8000260780003ffffe0000fc0ffc000000001fe0000,0x4103500f54078003a20780036db01e000efc0ffc01601602dfe001a),(0x183c00fc03fff0000000003807ffffc000000000fff000000000001ffffff,0x81400fc03ffa000c600632807aa63800318018cfff00019419432955519c),(0x0,0x0),(0x1fc000fffc0000000000003ff800000000000000ffffffffffffffe000000,0x1f4000f7a80000028401423ea80142000a100508555128518518a30000510),(0x1fffff00000000000000003fffffffffffffffff000000000000000000000,0x17ebfa000000000308018415f8558c124c615630000000620620c40000620),(0x1fffffffffffffffffffffc00000000000000000000000000000000000000,0x1fffafbefcaaf0abf055f8000001f0000f8007c00000007c07c0f800007c0)]
def s479C : List ColumnInfo := [(2,0,477,512,11)]
def s479D11 (_ : Nat) : Nat := 0x2ff
def s479L : Nat → Packing
  | 11 => (1,0,1,0,0,1,0,s479D11)
  | _ => emptyPacking
def s479I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s479 : Forest := ⟨479,11,s479S,s479C,[[]],s479L,s479I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs479_11_0 : block s479 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs479_11 : block s479 11 0 1 = true := bs479_11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts479 : checkedTables s479 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs479_11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs479 : graphValid s479 (boundsBefore es447) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls479 : Lower true (vars 479) (graphGoal 479) 12 := lower_forest (g:=s479) (i:=0) (hints:=8589964900) (before_sound es447 vs447) gs479 ts479 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es479 := extendKnown es447 12 [(479,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs479 : Known true es479 := extendKnown_ok (m:=479) vs447 ls479 (by decide +kernel)
def s495S := sampleAt 241 #[(0x400f02755800acc006600010190ce49001ffff8e3a4e800800fff999800,0x502355905acc836641800090464920ca907861a4690690620f99990a),(0x192cc03806000cf0007800022603338e0019800104c73000fff001ffffff,0x92cc02806311cf18978c4802201138e6459b22000c53322b23644aaab23),(0x220f004198000f00007fffcc38e3c3f0001e000e38f83fff000001e1e000,0x205000198035f001b2a0dc428e3c3f00cde066a28e838670660cde1e06a),(0x40300981e0000fffff800030c0fc03ffffe0000fc0ffc000000001fe0000,0x881e000df540780039040b402db01e000efc0ffc01601602dfe001a),(0x0,0x0),(0x183c00e01fffff0000000003f00fffc000000000fff000000000001ffffff,0x82400a01f886e00036001b3f00feec0019800ccfff0000d40d41a95550dc),(0x1fc000ffe000000000000003fff0000000000000ffffffffffffffe000000,0x1f4000fd4004480022401123bd50000009100488596128498498930000490),(0x1fffff000000000000000003ffffffffffffffff000000000000000000000,0x1ffffa0000067000338019c2fbf4bb924de156f00000006e06e0dc00006e0),(0x1ffffffffffffffffffffffc0000000000000000000000000000000000000,0x17dbaf57e077800abc055e00000000000e000700000000700700e00000700)]
def s495C : List ColumnInfo := [(0,128,358,521,9),(1,0,494,512,10),(2,64,424,517,6),(4,0,491,512,10),(4,256,195,552,6),(6,64,424,513,5),(8,0,487,512,10),(32,256,195,524,6),(34,0,461,512,8),(36,256,195,520,5),(64,0,431,512,8),(64,2,397,544,6),(66,0,429,512,6),(128,0,367,512,9),(256,0,239,512,8),(256,32,205,514,6)]
def s495D11 (_ : Nat) : Nat := 0x36058ccff
def s495H10 (_ : Nat) : Nat := 0x98211a4c360025000bb059e25453000021f0
def s495D10 (_ : Nat) : Nat := 0x300684d0e8d0a74cb1b260130d6f035188da6a739c0684c3876369a90d87540684c35ba71b110f8754e034261cd968950f87540684c35c6d3439d0e81a130d68c3a71b2550e8e1a80f05015401ff5d7fe3afff51ffae3ff547ffb8ffe75
def s495H9 (_ : Nat) : Nat := 0xc1e1d0a22f4e6304071bb4daf53398c80000000291f0f8969db100000ba800c8a25dcfe9249855b3e04b454f414f0012ec36f201328c08e08032500501804000a
def s495D9 (_ : Nat) : Nat := 0x6251011649b1a082c529c58a3c4f2c526201a08c1ec7044ab0f43c760893e3b66710598f245b00682362498830b11628b600d0460f11c54ec01a40230788e2ab0f71d8420b3b061632c5161e967e62e3b1c4ab32cf14ac763894985e67e3b144a38aaec3dc761494e1e9799f8ec4129d4b2fc62fbaea8b98a518720b7e9bf5f94f4e127398ab1d83b0037f55d71dfe575c6ff96171dfd57dc6ff5e275fee285d7fd5c751bfd489d6ff9e151bfd181d6ff86175bfd78d46ff5e151fbe485c6ff46275bfd58dc75f5d475d7f759d6ef52275bee285d6ef92171
def s495H8 (_ : Nat) : Nat := 0xc07e341900000083000000d73b002600000035f1f2dd000
def s495D8 (_ : Nat) : Nat := 0x1382085841c3ef3e20bb0938000e1f798b1e178f61299a8e89534e494400eb714aea3addd96571d467dc52bc2a397e895d4759f714af1a8cfb8a5789d677c92bc2a317e895d475
def s495D7 (_ : Nat) : Nat := 0xc5b8a6895d475
def s495L : Nat → Packing
  | 11 => (1,0,4,0,0,1,0,s495D11)
  | 10 => (7,1,4,0,0,9,0,s495D10)
  | 9 => (21,2,4,0,0,10,0,s495D9)
  | 8 => (8,3,4,0,0,8,0,s495D8)
  | 7 => (1,4,4,0,0,1,0,s495D7)
  | _ => emptyPacking
def s495I : Nat → Nat → Option (Nat × Nat)
  | 11,h => lookupWord 4 16 4 8 3 1 s495H10 (mixTag h)
  | 10,h => lookupWord 13 44 6 10 5 1 s495H9 (mixTag h)
  | 9,h => lookupWord 4 23 1 8 3 1 s495H8 (mixTag h)
  | 8,_ => some (0,0)
  | _,_ => none
def s495 : Forest := ⟨495,11,s495S,s495C,[[],[48,81,134]],s495L,s495I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_11_0 : block s495 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_11 : block s495 11 0 1 = true := bs495_11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_10_0 : block s495 10 0 7 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_10 : block s495 10 0 7 = true := bs495_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_9_0 : block s495 9 0 5 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_9_5 : block s495 9 5 16 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_9 : block s495 9 0 21 = true := (@block_merge s495 9 0 5 16 bs495_9_0 bs495_9_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_8_0 : block s495 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_8_1 : block s495 8 1 7 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_8 : block s495 8 0 8 = true := (@block_merge s495 8 0 1 7 bs495_8_0 bs495_8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_7_0 : block s495 7 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs495_7 : block s495 7 0 1 = true := bs495_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts495 : checkedTables s495 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs495_7
  · exact bs495_8
  · exact bs495_9
  · exact bs495_10
  · exact bs495_11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs495 : graphValid s495 (boundsBefore es479) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls495 : Lower true (vars 495) (graphGoal 495) 12 := lower_forest (g:=s495) (i:=0) (hints:=8591013462) (before_sound es479 vs479) gs495 ts495 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es495 := extendKnown es479 12 [(495,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs495 : Known true es495 := extendKnown_ok (m:=495) vs479 ls495 (by decide +kernel)
def s503S := sampleAt 275 #[(0x800780a61580000fcc000020206600000fffff8c60d00010001fffccf30001fffff,0x2802215840905cc205000002200409542058420508150814102c4730824a8413),(0x326660338860000ccf0000044c19998000cc000109360001fffe000333fffff98000,0x126660128862c43ccf162300440899ac85cd64300116590d590eb219115590f9ac8a),(0x440780441180000f0fffff98719e1e0000f0000671c7fffe00000003c3c0001e0000,0x402800011800db505406f88519e1e019df00cf25147033e033c067bc3c036de01ba),(0x0,0x0),(0x1807806781e00000ff000006181e01fffff00000781f8000000000003fc00001fffff,0x802806781e01832fa00c1a2080a00a983600c1a781f830a830a86153b8030c95186c),(0x6078007801ffffff00000007e01ffe00000000007fe00000000000003ffffffe00000,0x20480028013881bc00000dc7e01f76003380019c7fe0006b006b00d62eea06f000370),(0x7f80007ffe00000000000007ffe00000000000007fffffffffffffffc000000000000,0x7e80007ed4005120000289077aa00005220029105aca8a4c0a4c14980000a48005240),(0x7fffff800000000000000007ffffffffffffffff80000000000000000000000000000,0x77fd7d00000061c000030e05f7f5dd563c0ab1e000000c700c7018e00000c70006380),(0x7ffffffffffffffffffffff8000000000000000000000000000000000000000000000,0x5fb7d7d7fec77e00afabf00000000007c0003e0000000f800f801f000000f80007c00)]
def s503C : List ColumnInfo := [(0,6,145,864,7),(0,36,145,834,7),(0,258,145,612,7),(1,16,358,640,8),(1,128,358,528,8),(2,0,501,512,10),(2,32,213,768,8),(4,0,499,512,10),(4,256,211,544,8),(16,0,487,512,10),(16,1,294,704,6),(16,128,358,513,8),(17,128,358,512,7),(18,0,485,512,7),(20,0,483,512,7),(32,0,471,512,10),(36,256,211,512,7),(64,0,439,512,9),(64,2,405,544,7),(64,4,179,768,7),(64,6,145,800,6),(65,0,438,512,6),(66,0,437,512,7),(66,256,145,548,6),(68,32,145,770,6),(70,0,433,512,6),(96,2,405,512,6),(128,0,375,512,10),(128,1,294,592,6),(128,16,358,513,8),(129,16,358,512,7),(145,0,358,512,7),(178,0,325,512,4),(256,0,247,512,10),(256,32,213,514,8),(258,32,213,512,7),(260,2,145,608,6),(290,0,213,512,7),(292,0,211,512,7),(320,4,179,512,6),(358,0,145,512,4),(404,0,99,512,4)]
def s503D12 (_ : Nat) : Nat := 0x71616cf24cff
def s503H11 (_ : Nat) : Nat := 0x53538050c1b390d83a100000015e65800108d56a8822680826e2d83e0f00000285414523e38003d2b079ac0000058c001c3415b99a1565dd5000c35e48826031d5c97097a72c00078c0005380001611000000d4603010
def s503D11 (_ : Nat) : Nat := 0x110c244258f170cf3ea2208425125119e40610963c5c33c89e18a024438f307862344f0612d903f2429346088a868fb724c084a60c212c713170cf227946c4c78b867833e822084054a5119f40610963c5c33c89f4a11f6e4921094e4438930791984c78b867843e79e90882101529e4630a2c2910612dc93e403a304a1820305426c789221d2a83ec220c25b92148003e8c1286173018a084a7888c50a1f6e4810c6129c8870a3cc1f4670c6c42512a0f1c1840e14fdb923c09846b061108fb67e4934c451aef35a9abd48660c9288f029e6b896a6c917729c4867a8c894622036852052001ff8c3fe98ffd50ffa81ffd47feba7fd53ffa61ff843ff287fd71ffa87ff58ffe887fd21ff8a1ff547ffa87fd41ffc81ffd4ffeaa7ff54
def s503H10 (_ : Nat) : Nat := 0x75efb2d90c24e0fca9fc30e2f6a222bcc253a1cd3118d33c0000001913d4dc28c4a649cd132a20050f715a229b8ce2272e0a89b38432677e1185df4301d1c598afc892a7561261e15d337b4039fba4704d45d92e447724ca3cadc8c72068839670a8eec8bfc6286cd64e05248a8f583fd70f8f351229a0b1c23101c405382609a147d5506de55f559b82c2d52ee9824ecc5cf57f6200a6e220009163c5880461f9178002659cd96a29490000bab01138780000000004074001762d2168eb889218819ee9b4a8460e069c7d4323050004cb4000000b6b6986254000315948684805239a204b863a08719000296ef1bc2561044b5e0579f601ed9e93a5107cc8001123e47bb6dda7cb9de193630b204c8928142256200c8c1e4400183ec8d5b7783800084d9d6843721592b1d21a1442751c320364e919947490c40d963525e8b592022129abc48000c5b60d55440bfec9f5fb03176f037000154000000066b800108e83d000418f621e0b586000100324f000000061fbdd483785d994cc1a8be52d09a000caee8aba094d000000118229cf000004c6bf9c46dfdcf786a4466a37316a8366222000038a6bd30807400a0f4310000b0900060400000000010405010002350007050911030c060b1b0103090002000101000300160e162f060a090701210100030001a01100004403010e0a080801031700010506
def s503D10 (i : Nat) : Nat := #[0x2432cfa0467a3048a0ac29e253e5054f9e8c12282c28889af14151e6e2545140c7d418e0e7d689431e92105110bf4a94511139f28288892f14126e25440d15407d8e0e7d48b121c269e503e313ec6a614f890e18131d239d63155c3a4c8c2820fc851a22faa3c4978a0822253e5049b4f8925068346659f4a4c88242c80fd1a22fa53c4a7ca088a233d1830506030445171f9e8c1a2815145c7a48f825122101d14446278a0a8b37121c069e3f073ec6a619b890e4f031f83639f522888c4f94151624a4113c7e127d8d2c31252089e3f093ec69160b1d9f1a243118f8c0f6f244ca08502e283e345171814281f2a7ed92e494140c103c7e7c8c60e0b0a502e22283c183490d281e142678ac2858e8c010885002f9430907c687b792265041f281120f0a0c627c189c9b792305044f259f241a2920f0d0c067c9050826163abe505241f1418403140f8a1614507c68806083e3404513e2881e2816de492141054282c7460444d7c8d222060a093e48347131107dbc928309058eaf94144a7ca063222163b3e48347dbc913282030f938c8c786060c3c4e3241f1a1e3808162f0e785140a8fa8182c757ca0a06088a3f3e48347dbc9132826de488841194a03058f8bc39e3e5171814281f288940f8f6f2404608ca30463e311281f1940f8b6f24482094a503e2a5fd1aa7fb3c09c5cd3a6132dc93fc92a3cb1c08b1c45a19309c82fc0e9fbafb07adbc59dd2ebc747b989c0adb86c5b599a22cbc62fb0297cabc05b9ac99602acc537a8c940a9b04ada4b91c289442fa10903a7f03e19e58eb270c3739a08cca6403159838bd25c42cb95e8aaa528285937897247422f90e87da3b01bd8d386622f41678ac852a27812d88183b219c0bb852826a10806d82f812207402b810802a000ffd18543ff92150fff518c3ff5d230ffd50503ff52150ffd718c3ff5d150ffd218c3ff5c550fff514c3ff5d153ffd518c3ff5d130ffd50443ff48550ffd418c3ff5d250ffd63d47ff54d71ffd714c3ff5d163ffd15543ff5c650ffd41543ff54d21ffd214c3ff58d71ffd21943ff4d551ffd514c3ff55230fff548c3ff58d21ffd53507ff45650ffd414c3ff58d51ffd41943ff51550ffe18543ff58d41ffd4554fff55130fff544c3ff51650ffd5458fffd5163bfd58442ff56240bfe58487fe54210bfd58943fd5c751bfe58503fe54110bfe584c6ff42351bfd18942ff56121bfd18142ff8a131bfe28502ff8a154ff571442ff86153bfe28442ff82121bfd28842ff56210ffa50442ff96110bfd18d4eff8a151bfd08d53fd54510ff551486ff82151bfd18d42ff4a110bfd28d52ff4a240bfe5850eff8a143bfd188c2ff56230bfe08552ff86150bfd28d467f5e354afd68d4ebf9a130f7950142fd46050bf618552fd46240f7b50942ef52050bbe485c6f74e050,0x451a171c28140a3a781820fcf4614318c0aab3d2224084c1919987514a27455a9f120c5090cb3e71125a304180a322a7940e318c051d853e2448a1227d9509f3d1830505458906154702281f50639f5b0a7cf4609141b3d226e2519980d147e0d467d89e313c5048913064515025028631f9f5cda7c4c183142432cfa614445c5014a010682928b3d18265054f89012846659f3a78c4f94133e21261812987e1512457d7431e24bc505619b4f89830828489f6554227c48314][i]?.getD 0
def s503H9 (_ : Nat) : Nat := 0x169e39f01c58d4258ba46b3a2c31a8d43559d2451181f2643651d626b91b907bdf92d74973407c157f00ff902812e9bd667efd332429522d875dff8062d3bf1b848b71e9c38fbe18b91e4e9286bf9662c8397806619883ddf58038a8423c85b442be71ad11e114b39832f3966a25a190dbe31c5853adc8f830129c0e88c9313e8d14f4ec5cc2da3e6b8f2ce048c60f5d22f8a72e77ed9feb0e495c558001470f1e4c924c4dfc154c5f8c0032a386e1b0000f7fe49e3604140865b053f60c4761c0033700a6d43d70001a23e911dd19216d1ec000c2c0030cc0000004ec89c0003654fd54608b05db10000002f5aa28000e39c4fdab02a6b2c7ca640036ca09bdd73b244b13041800000058400138b3bb731215ee2126fc92a40034d75e00000000026b7738caeca3a3f8624bc000855f3f1bc0017e2eafac04f97000004009604800c28a019b16b00820a082090669680209c00e241d70106142510802d01000c01b046e0120c0010080081463c18b04
def s503D9 (_ : Nat) : Nat := 0xc26243213233f12123293120a020f120a020f3f83cde243213366d9f89329188c90c84c9890501079bc487c064a7b264a3c483832130a9737890f80c8c90f8107890c04c7890f81079bc487c064cde24a20e262430131b243e041e6f121f01919311148d9e25030f121f020dc2cf1284899bc487c064628642636487c083050544cf128186c5050547890a8040428cf9b3783cf8f9ec86339a3e1f62b450c6728b1384cf8d9f04643948c762b463e1f6838ce9f05060789008080c28cf998ad16807e3ee33051bc26339459f0a0b3d8c140c0404050508cf1408519e166f1383cf918a8e6787e3ee333851ccf8f87dc66cf8a048405054789c267c66211070280a2e2402651467cb9ec60a06286f0b3783cf8f3e28173d094505054ac96237c6010167c2840b860281f14142e180a07c50596393a91a8fa8bf89686d84d8248047d27a97897697497206f76d76b768e66e64e62e6055dc5bc59c58556554550a4ea49d48646643d3f93d939e36334c33531e2fe2d52be2a727e2432081f11d11b117f14d12d1160f60df0ad08d064032000bff2ca43187fd5c7518c2ffab290c617fe2955230bff2ca42987fd5c7514c37fac72c2437fe2954630bfeaca42987fd58d71d47feaa290c617fe2955130dfeb1ab090dff4a7548c2ffc52aa2c77fe2954530ffaa8a42985ff4a7518c37fac7142a37fd29d5130ffab1aa290eff5d1588c2ffa53aa2c7bfd7156230bfe94ea2986ff485588c37fac6946a3bfd1556230dfea0ab1186ff515588c2bfaf3aa4615fd79d5130d7fa8cd0986bf5d2684c2bfaf3aa2c7afd719a130d7e90cd0986df41658502fec32aa461afd519a130dbe9acb090ebf506684c2efcb290ca17f61951550dbe82cb0886fd5c508d46fec32a2aa77f61955130d7eaa4d0986bfd52684c2fec32a2ca13fd89d5230bfb0caa8b1dfd86548542f7c92b8c617be495c550ddea9c90b8def925714c2f7c92b8ca13fd89d4630ddeb1c90b8cdf965284436f512a80a137a8954050
def s503H8 (_ : Nat) : Nat := 0x25677470cdc6489f605401364b19cd87c2084033400810008522686e0978fb20036c00045002a2003656cc0855c28644554e146003756e4812c5dc26ba111f8abe8cc7a8b4b0d182a50b040745000043126e830030411c8
def s503D8 (_ : Nat) : Nat := 0x39e728800011c10000e784000034d0971a0b25aa11941e28280abf969219a130ebd5c7519a130abf569219a130abf8a9549a130abf8a9519a130ebd545219a130abf4ab549a130abf4ab519a130afd8694556230cfd5c589d4630aef9297156230a3f5eb549a130abd869549a130aaf929719a130
def s503L : Nat → Packing
  | 12 => (1,0,6,0,0,1,0,s503D12)
  | 11 => (23,1,6,0,0,11,0,s503D11)
  | 10 => (100,2,6,0,0,13,0,s503D10)
  | 9 => (64,3,6,0,0,12,0,s503D9)
  | 8 => (14,4,6,0,0,7,0,s503D8)
  | _ => emptyPacking
def s503I : Nat → Nat → Option (Nat × Nat)
  | 12,h => lookupWord 15 56 5 11 5 2 s503H11 (mixTag h)
  | 11,h => lookupWord 78 263 8 13 7 2 s503H10 (mixTag h)
  | 10,h => lookupWord 62 209 7 12 6 2 s503H9 (mixTag h)
  | 9,h => lookupWord 18 59 6 10 4 2 s503H8 (mixTag h)
  | _,_ => none
def s503 : Forest := ⟨503,12,s503S,s503C,[[],[116],[33,133],[33,116,133]],s503L,s503I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_12_0 : block s503 12 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_12 : block s503 12 0 1 = true := bs503_12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_11_0 : block s503 11 0 23 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_11 : block s503 11 0 23 = true := bs503_11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_10_0 : block s503 10 0 11 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_10_11 : block s503 10 11 41 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_10_52 : block s503 10 52 48 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_10 : block s503 10 0 100 = true := (@block_merge s503 10 0 11 89 bs503_10_0 (@block_merge s503 10 11 41 48 bs503_10_11 bs503_10_52))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_9_0 : block s503 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_9_1 : block s503 9 1 2 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_9_3 : block s503 9 3 31 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_9_34 : block s503 9 34 30 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_9 : block s503 9 0 64 = true := (@block_merge s503 9 0 1 63 bs503_9_0 (@block_merge s503 9 1 2 61 bs503_9_1 (@block_merge s503 9 3 31 30 bs503_9_3 bs503_9_34)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_8_0 : block s503 8 0 3 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_8_3 : block s503 8 3 11 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs503_8 : block s503 8 0 14 = true := (@block_merge s503 8 0 3 11 bs503_8_0 bs503_8_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts503 : checkedTables s503 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs503_8
  · exact bs503_9
  · exact bs503_10
  · exact bs503_11
  · exact bs503_12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs503 : graphValid s503 (boundsBefore es495) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls503 : Lower true (vars 503) (graphGoal 503) 13 := lower_forest (g:=s503) (i:=0) (hints:=8590984788) (before_sound es495 vs495) gs503 ts503 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es503 := extendKnown es495 13 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs503 : Known true es503 := extendKnown_ok (m:=503) vs495 ls503 (by decide +kernel)
def s507S := sampleAt 248 #[(0x1007801261580007e600004044300009000fffd5b267000fff33cc003ffff,0x2800221584482e61140000410089908a422c0902308a08b11cc2495093),(0x69960063886000667800008180cb000e000c002a4db9fff000ccfffff3000,0x299600228862c1e678b0c000804b585e586d618004a9587586445561f358a),(0x0,0x0),(0x8018498c118000787ffff326270c000ffff000338e3e000000f0f0003c000,0x488411800da82a03f122250c01db01f007b38e3e02e02ef0f00dbc03a),(0x301e071f01e00007f80001c38380ffff00000003c0fc0000000ff00003ffff,0x100a071f01e01897d00629428280d31603140c53c0fc0324324ee00c92a32c),(0xc0e007e001fffff8000001fc03ff000000000003ff000000000ffffffc0000,0x402005a0013881e0000071fc03fb005800580163ff000068068bba81e00070),(0xff0007fffe000000000001fffc00000000000003fffffffffff00000000000,0xfd0007fdd4005180001461fff4000a500a502943f6b54a70a7000029800a60),(0xfffff80000000000000001fffffffffffffffffc0000000000000000000000,0xeff5d00000006100001840ad5d2e2c604c60b18000000c40c4000031000c40),(0xfffffffffffffffffffffe0000000000000000000000000000000000000000,0xbfdffa57bec77e057d5f800000000f800f803e0000000f80f800003e000f80)]
def s507C : List ColumnInfo := [(0,2,409,608,9),(0,128,354,537,7),(0,256,211,552,9),(1,0,506,512,8),(2,0,505,512,9),(8,0,499,512,10),(16,0,491,512,10),(32,0,475,512,10),(64,0,443,512,10),(128,1,298,592,6),(128,16,362,513,6),(144,0,363,512,7),(256,0,251,512,9)]
def s507D11 (_ : Nat) : Nat := 0x30901d6190ff
def s507H10 (_ : Nat) : Nat := 0xd3c00c464
def s507D10 (_ : Nat) : Nat := 0xd48304439500bd7035bf923304439500a402b1deb8b268c110e54029048ef5c2df72a001ff183feb07ff60
def s507H9 (_ : Nat) : Nat := 0xf4000065ac4fa6a083488a70
def s507D9 (_ : Nat) : Nat := 0x3ccb4c0a0772f5e095ee60420e29006bc164b3ccb4c01df5e0b4e986faf01967f32d30063277d4ae17e65a61bf01968f32d30d780cb46986faf01967cbd2a1ee04c9905e00fde38582ff5a260ef960183bed8260bde38582fb4a060bbd48182f74e060
def s507H8 (_ : Nat) : Nat := 0x906bb8445
def s507D8 (_ : Nat) : Nat := 0x140458fe72e9c3bf5f02c4a41f3974e027bf5f02d3f3974e027bf5f02d3a31b108801eda3958060d7d44ac0304f78e5689825f512b00c1ad9604e060
def s507H7 (_ : Nat) : Nat := 0xa07804c
def s507D7 (_ : Nat) : Nat := 0x2c21610b0e9a0cb6a69604e060cb68ea8958060cb68e68958060
def s507L : Nat → Packing
  | 11 => (1,0,4,0,0,1,0,s507D11)
  | 10 => (3,1,4,0,0,8,0,s507D10)
  | 9 => (8,2,4,0,0,9,0,s507D9)
  | 8 => (5,3,4,0,0,8,0,s507D8)
  | 7 => (3,4,4,0,0,5,0,s507D7)
  | _ => emptyPacking
def s507I : Nat → Nat → Option (Nat × Nat)
  | 11,h => lookupWord 2 5 1 7 2 1 s507H10 (mixTag h)
  | 10,h => lookupWord 3 11 3 8 3 1 s507H9 (mixTag h)
  | 9,h => lookupWord 2 6 3 7 3 0 s507H8 (mixTag h)
  | 8,h => lookupWord 1 5 1 6 2 0 s507H7 (mixTag h)
  | _,_ => none
def s507 : Forest := ⟨507,11,s507S,s507C,[[],[112,129,99]],s507L,s507I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_11_0 : block s507 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_11 : block s507 11 0 1 = true := bs507_11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_10_0 : block s507 10 0 3 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_10 : block s507 10 0 3 = true := bs507_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_9_0 : block s507 9 0 6 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_9_6 : block s507 9 6 2 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_9 : block s507 9 0 8 = true := (@block_merge s507 9 0 6 2 bs507_9_0 bs507_9_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_8_0 : block s507 8 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_8_2 : block s507 8 2 3 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_8 : block s507 8 0 5 = true := (@block_merge s507 8 0 2 3 bs507_8_0 bs507_8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_7_0 : block s507 7 0 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs507_7 : block s507 7 0 3 = true := bs507_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts507 : checkedTables s507 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs507_7
  · exact bs507_8
  · exact bs507_9
  · exact bs507_10
  · exact bs507_11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs507 : graphValid s507 (boundsBefore es503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls507 : Lower true (vars 507) (graphGoal 507) 12 := lower_forest (g:=s507) (i:=0) (hints:=12885979220) (before_sound es503 vs503) gs507 ts507 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es507 := extendKnown es503 12 [(507,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs507 : Known true es507 := extendKnown_ok (m:=507) vs503 ls507 (by decide +kernel)
def s509S := sampleAt 232 #[(0x20180230558000ec00c000101024f0002400fff2673267003ffffffff,0x800105590406c82c8200000245020a482483023102320883555485),(0x0,0x0),(0x5060044a6600133000fff0606b38cb003800c00db9cdb9ffc00cccc00,0x1020000a6602d130164170202b38cb09b826c264a944a909c26cccc2c),(0x8084998c78001c3fff0009898c3f0c003fff000e3e0e3e00000f0f000,0x4888c7801d4340f00e8888c2d0c03ac0f00ee3e0e3e05816f0f01c),(0x303071e0f80001fc000000e0e0fc00fffc000000fc00fc000000ffffff,0x101071e0f80219f810c10ca0a0d400d43410c10cfc00fc045114aaa91a),(0xc1c07e00fffffe00000000ff00ffff0000000000ffff00000000ff0000,0x41405a00efe87e0003e03eff00ffff01b806e06effff0001d876ff007c),(0xfe007fff00000000000000ffff00000000000000ffffffffffff000000,0xfe007ffe00065000328328fdfd00000d20348348b54ab54d6358000350),(0xffff800000000000000000ffffffffffffffffff000000000000000000,0xefef0000000460002302305757292a29c1270a70000000098260000260),(0xffffffffffffffffffffff000000000000000000000000000000000000,0xbebda577101780acbc0bc0000000000e003803800000000e0380000380)]
def s509C : List ColumnInfo := [(32,0,477,512,11)]
def s509D11 (_ : Nat) : Nat := 0x2ff
def s509L : Nat → Packing
  | 11 => (1,0,1,0,0,1,0,s509D11)
  | _ => emptyPacking
def s509I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s509 : Forest := ⟨509,11,s509S,s509C,[[]],s509L,s509I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs509_11_0 : block s509 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs509_11 : block s509 11 0 1 = true := bs509_11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts509 : checkedTables s509 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs509_11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs509 : graphValid s509 (boundsBefore es507) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls509 : Lower true (vars 509) (graphGoal 509) 12 := lower_forest (g:=s509) (i:=0) (hints:=8598353412) (before_sound es507 vs507) gs509 ts509 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es509 := extendKnown es507 12 [(509,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs509 : Known true es509 := extendKnown_ok (m:=509) vs507 ls509 (by decide +kernel)
def s510S := sampleAt 250 #[(0x0,0x0),(0xd32c0063104002ccb000c0000413003eb3000cc000926739c003fffffffff,0x532c0021105446ccb512d44800110016b3522cd488002318d48948d555523),(0x1200f0084a280030fc000fffc181cb3333c000f00036db9ce7ffc003333000,0x20050000a280d705c03640dc0814b3333c066f019924a94a419c19b33306a),(0x200309318c30003f0ffff00026260c3c3c0000fffff8e3e0f8000003c3c000,0x9108c3003750d00f003a2220c143c000e5403f8e3e0f805805bc3c01a),(0xc03c0e3e0fc0003ff000000038380fc03fffff00003f03ff00000003fc0000,0x40140e3e0fc0c37ff030e0c3a8280d403d530f00c3bf03ff00c58c5bfc031a),(0x303c00fc00fffffc0000000003fc00fffc0000000003ffc0000000003ffffff,0x102400b400e781b800006c01b3fc00ffe8000cc00333ffc0000350352aaa0dc),(0x3fc000ffff0000000000000003ffff00000000000003ffffffffffffc000000,0x3f8000ffde002920000a482923f7ea000000a8802a22db54a52a62a60000a90),(0x3fffff00000000000000000003fffffffffffffffffc0000000000000000000,0x3bfebf00000031c0000c7031c15d5f2abc2acf0ab3c00000003383380000ce0),(0x3ffffffffffffffffffffffffc0000000000000000000000000000000000000,0x2fdbfa4af7187e00aa2f80be000000000000f0003c000000003c03c00000f00)]
def s510C : List ColumnInfo := [(16,0,494,512,10)]
def s510D10 (_ : Nat) : Nat := 0x2ff
def s510L : Nat → Packing
  | 10 => (1,0,1,0,0,1,0,s510D10)
  | _ => emptyPacking
def s510I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s510 : Forest := ⟨510,10,s510S,s510C,[[],[97,82]],s510L,s510I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs510_10_0 : block s510 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs510_10 : block s510 10 0 1 = true := bs510_10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts510 : checkedTables s510 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs510_10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs510 : graphValid s510 (boundsBefore es509) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls510 : Lower true (vars 510) (graphGoal 510) 11 := lower_forest (g:=s510) (i:=0) (hints:=9413555792) (before_sound es509 vs509) gs510 ts510 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es510 := extendKnown es509 11 [(510,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs510 : Known true es510 := extendKnown_ok (m:=510) vs509 ls510 (by decide +kernel)
def s511S := sampleAt 414 #[(0x200078008981558000003eb300019800000801024330000004920003ffffe231c608349d00010001fffccccf3330001fffffff,0x280008815584090016b308159840a0000002411000204c92102950816010c200148d08150814102c44473330824aaa8413),(0xc99660030e08060000b3333c0001e000001026000ccacc00071c0003300004420934d8e60001fffe00033333fffffff9998000,0x499660010a08062c43b3333c588de2c460002200044acd642f1cb21b3590c000011458a6590d590eb2191111555590f999ac8a),(0x1100780041051980000c3c3c00001fffff06038b38f0cf00007e00003c000199c71c71f07fffe00000003c3c3c3c0001e1e0000,0x1002800000519800dbc143c001bca80df02028b38f0cf00cefe0067bc033c89451451d07033e033c067bc3c3c3c036de1e01ba),(0x2001804986061e00000fc03fffffe00000984c0c3f00f000007fffffc00001e1f81f81ff8000000000003fc03fc00001fe00000,0x4882061e0003bd403d5007e0003e88440c2d00f0001edb600fc0007de1f81f81ff800bc00bc017bfc03fc000edfe0007a),(0xc01e0071f807e000000fffc00000000000e0700fc000ffffff800000000001fe001ffe000000000000003fffc0000001fffffff,0x400a0071f807e001832ffe800306801834a0500d4000f54c1b00060d003069fe001ffe00030a830a86153bbb800030c9555186c),(0x301e0007e0007fffffff000000000000000ff800fffff000000000000000001ffffe000000000000000003ffffffffffe0000000,0x10120005a00073f881bc0000000370001b8ff800fffbb00019c0000ce000671ffffe00000006b006b00d62eeeeaaa06f00000370),(0x3fe00007ffff80000000000000000000000fffff00000000000000000000001ffffffffffffffffffffffc000000000000000000,0x3fa00007fef500005120000000a24005120fdfd50000000291000148800a44176b2caaa250a4c0a4c149800000000a4800005240),(0x3ffffff8000000000000000000000000000fffffffffffffffffffffffffffe00000000000000000000000000000000000000000,0x3bff5fd00000000061c0000000c380061c057abf292ee0ab1e02498f02ac78000000000000c700c7018e000000000c7000006380),(0x3ffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000,0x2fedfd7a57df8c077e002abc2afc0157e000000000000003e00001f0000f80000000000000f800f801f0000000000f8000007c00)]
def s511C : List ColumnInfo := [(8,0,503,512,13)]
def s511D13 (_ : Nat) : Nat := 0x5ff
def s511L : Nat → Packing
  | 13 => (1,0,1,0,0,1,0,s511D13)
  | _ => emptyPacking
def s511I : Nat → Nat → Option (Nat × Nat)
  | _,_ => none
def s511 : Forest := ⟨511,13,s511S,s511C,[[]],s511L,s511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs511_13_0 : block s511 13 0 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs511_13 : block s511 13 0 1 = true := bs511_13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ts511 : checkedTables s511 13 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bs511_13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gs511 : graphValid s511 (boundsBefore es510) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ls511 : Lower true (vars 511) (graphGoal 511) 14 := lower_forest (g:=s511) (i:=0) (hints:=8591013460) (before_sound es510 vs510) gs511 ts511 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def es511 := extendKnown es510 14 [(511,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vs511 : Known true es511 := extendKnown_ok (m:=511) vs510 ls511 (by decide +kernel)
def m511S := sampleAt 143 #[(0x3ffe0000007ffc001fff,0x41420a105082841420a105082841420a105),(0xfff8003ffe000,0x2c8d646b23591ac8d646b23591ac8d646b23),(0x1fff0000000001fff0000000000000,0x1bc0de06f03781bc0de06f03781bc0de06f),(0x3ffe0000007ffc0000000000000000000,0x7c03e01f00f807c03e01f00f807c03e01f),(0xfff80000000000000000001fff,0x1868c3461a30d1868c3461a30d1868c3461a),(0x7ffc00000000000000000000000003ffe000,0x3701b80dc06e03701b80dc06e03701b80dc),(0x1fffffffffc000000,0x5242921490a485242921490a485242921490),(0xfffffffffe0000000000000000,0x63831c18e0c7063831c18e0c7063831c18e0),(0x7fffffffff00000000000000000000000000,0x7c03e01f00f807c03e01f00f807c03e01f00)]
def m511C : List ColumnInfo := [(0,36,153,834,8),(0,64,440,519,8),(0,258,145,620,8),(1,24,102,896,6),(1,64,440,518,7),(1,128,358,536,9),(3,0,508,512,8),(4,0,507,512,12),(4,258,145,616,7),(6,256,209,552,7),(7,64,440,512,5),(8,0,503,512,13),(9,128,358,528,8),(16,0,495,512,12),(16,128,358,521,9),(17,0,494,512,10),(17,64,424,518,6),(17,128,358,520,8),(18,0,493,512,9),(19,0,492,512,7),(19,64,424,516,5),(20,0,491,512,10),(21,0,490,512,7),(23,64,424,512,4),(32,64,408,519,7),(33,64,408,518,6),(34,0,477,512,11),(36,0,475,512,10),(36,64,408,515,6),(36,256,211,520,8),(48,0,463,512,9),(49,0,462,512,7),(64,1,302,656,7),(64,2,413,544,9),(64,36,153,770,7),(64,258,145,556,7),(65,2,412,544,6),(66,36,153,768,6),(68,0,443,512,10),(68,2,409,544,8),(68,258,145,552,6),(69,0,442,512,7),(69,2,408,544,5),(69,16,298,640,5),(70,0,441,512,8),(71,0,440,512,5),(72,0,439,512,9),(74,256,145,548,6),(81,0,430,512,7),(81,2,396,544,5),(84,0,427,512,7),(96,2,413,512,8),(96,258,145,524,6),(98,0,413,512,8),(98,256,145,524,6),(100,2,409,512,7),(102,0,409,512,7),(115,0,396,512,4),(128,0,383,512,11),(128,8,119,768,8),(129,16,366,512,8),(132,0,379,512,8),(136,0,375,512,10),(144,1,302,576,6),(145,0,366,512,8),(148,0,363,512,7),(162,0,349,512,7),(196,16,298,513,5),(208,1,302,512,5),(209,0,302,512,5),(212,1,298,512,4),(213,0,298,512,4),(256,0,255,512,11),(256,6,153,608,7),(256,32,221,514,9),(256,36,153,578,7),(257,128,102,536,6),(258,32,221,512,8),(264,0,247,512,10),(276,0,235,512,7),(290,0,221,512,8),(290,4,153,576,6),(292,0,219,512,8),(320,4,187,512,7),(320,6,153,544,6),(320,36,153,514,6),(324,2,153,544,6),(324,32,153,514,6),(326,32,153,512,5),(358,0,153,512,5),(392,0,119,512,7)]
def m511D14 (_ : Nat) : Nat := 0x71a68591ff
def m511H13 (_ : Nat) : Nat := 0x2340b8384f15f596301bf200077101f1c009748612650c528a77c1300195958c2000840012000192c000061400a62d196943278001ab9760008f
def m511D13 (_ : Nat) : Nat := 0x740e1e351a9d344d163aa12483e260f1a8b3c374a41f078d4d134588a2348528d53898c907c4c1e3516226e8269a3c8b152c3cd1f0790e898693a683e2c7502a943a4d1634367483e1a9a260f8b3a002a6a92707992098f86d283e2c6910e9c1a4c347935161880a3e260f8d528b1d1a424069f078d4d13459e245500466a2c3cd1a7c4c1e3a35169a6e91e48260f3e4a158b3c1a5241f130d07cd458e9e24983d386854366a2d00314907c1e340f344d1622948263e0f4a1b8b111a4a41f1307c58d1b9d20983cf854841c6a2ce1442800a4d16701e7483e1a079a260f8b424131f07c6908d459c25012134f148f8c587866807c4c60f3e1a9a071526528b1d50a939c459315202c983c68fa6a2c44754904d1a7c1e9516347098808337ee7b97747477226dd6a066362e5e959454f5024cd48042b3de38933c2ef2b225d2201db18e1591240cf0a204d000ffd86ffd41ffd76ffc86ffd71ffd42ffc70ffd80ffd52ffd60ffc80ffd50ffd70ffd85ffd64ffd40ffd81ffd54ffd84ffd74ffd72ffd75ffd10ffd21ffc60ffd20ffd61ffc87ffc76ffd82ffd62ffd87ffd65
def m511H12 (_ : Nat) : Nat := 0xeb32a828546242352ae4d6f140769cb92c798787241b12159741e8129768ea4a986f427441975c4ad14e362608bf5c590e5b4d315849ac7184e0f45689f742061aeb71bf4ec30dc72034354d04644b2a4a58c388999ed52c88c638aaef5d6c956db48234ce67e532b4845c929ab03a52f33ea84ea197ac1dcd1b8f9b5a5964ad8e60f5b129d196a8e1a90a1252d00ee4cd4a0ab0c88b73e37c0a5e6b2460ad543fe02c31fb74436b06700bbaa214b56917746b5dd2e900054bfa550f3e159b809decfe16c4489ec04b3b3828f5c31f2035d5dd151f8f008fa0a6a315218ad9a8a9f9a82978b53de74d01d871d1942a8c636b5bb51f40005129c500001243a99070223a57a5f000000111521b4279cdf6130aa0dc329551992e6bee268e22b8bf5dc6d180792f9cc38e4a0d6b1591c00001d25fc29a8104760006cf80012ce128fbb16d643177b39c7da5e144a6513868e456000000126b123c9680038f5e50871f3840000004130494000571140b0cad5c000e108003cb60000002c58001c5300009e420f809201bd40858000000147102d4bc0000d67eafaa8a34d4da60a0d50000c015220005429be02a2e06926e51004e880a25b19587c578c1ae2f7ccf2d4aaf15a603c0007140001194cc0f6c99b849f4c8c3d8003a56492000391004000000000020b4000ea70003a3c000d964d9ee78e7434beceec66000e210000000000836c0b40016ab0000002d0c0000000b1c07312e120c5200338cd118791654817663f6150001b64202f3dd1cd8cc30bc88e9a38d0e4561f11ae30cd609c9aedf555d887198c7569547fdb96de9a6ce85f272e10ec9f24cd26c7760afb1d5aace6437e716ac04c403fa49dc748ffc4cb05ab0f53f487075c8470006f28a2d8d326e004d41800282495f91793a1a37e5e757aaee137f396b9d15461f89af4a4c48000c98255150e18a8b20b6d163147d270400031a000c0000020104010f00080512063200040900000004160000460310140102060703000025010102196b061a00270c04020b020980551015070a0003080901130014262700010c020a0b3107008b2e0f0b0108190c0102000c05000143220003080248060427540004050009060223030820020443151e010805
def m511D12 (i : Nat) : Nat := #[0x20ffeb08e1ffd50483ffac2c07ff59181ffec0a81ffc89583ffae0887ff61574ffe8b2c1ffd855cbffac2407ff48570ffeb22e5ffd70483ff812c37ff5d564ffe43ac1ffd64443ffb0a307ff61520ffeb2243ffc76603ffa42a07ff52520ffeb2241ffd615c3ffae8c0fff60941ffeb9303ffd7660bffb04b8fff55172ffeb4a41ffd845cbff8eca87ff5d584ffe3ca21ffd84443ffa8cb0fff60870ffeb0a81ffd621c3ffb0ea0fff60520ffeba221ffd54483ffb0890fff58980ffec32cbffd72443ffaf2b07ff61120ffebb2cbffd74487ffb04b07ff61d42ffebca41ffd74483ffac4407ff59542ffec12a1ffd49583ffac4a87ff22510ffe3b30bffd75483ffa40887ff59470ffec22c3ffd65603ffb0eb07ff1a550ffeba2c3ffd72587ffb12907ff55960ffec3aa1ffd825c3ffac4b87ff61562ffeaca41ffd61483ffac8c17ff21d10ffec1281ffd62503ffacab87ff21d21ffe43a41ffd19483ffb0eb27ff55182ffeaa2c5ffd56593ffacaa07ff61162ffe43ac3ffd7460bffae8b17ff61d54ffe34aebffd7560bffb04887ff5d562ffe34b09ffd65613ffacaba7ff59572ffec3a21ffd87487ffb04b0fff61d20ffeb2a41ffc6961fff90eb17ff61d61ffec3ac5ffd6560bffb0eb2f7f59d71dfeb4301dfd675c3feae2a0f7f59d72f7ebb2c1bfd686077fa90c077f51d70ff614b0defd76593ff300a85ff5a542bfeb4a21efd46582ffaf2b15ff52486bfec4a81f7d8554bfea82887fd5c510fdeb22837fd79592ffb123b5ff42476fdeb22857fd7921affb12aa5ff62560dfeb43057fd89543ff2e0a05ff62470ff6b92857fd5921effad2a97df51550bfec4a837fd79596ffa92887fe58110fdec22857fd691c3ff300905ff46486ff6a1241ff960482ffaf2307df5d550bfeb4aa17fd6921effad290eff5e180bfeb49017fd89486ffaf2407fb54920bfeb4aa97fd49483dfb0cb15ff52521bfe8c8c17fd89596ffad2907ef59140bfea48ed7fd0921affaf2a95ff62552ffac0a217fd79586ffaf290fbf61965ffac0a437fd79552ffaf2885ff5e520bfea490f7fd59202ffb12a15ff46476efec3ae5fbd74502ffab2387df5d554bfe8c901dfd875d6ffa52385ff56486bfec4a417fd2921ff7b08aa5ff42487bfeac8c17fd895d37faf0c27fd58510ff6c12a57fd59482ffaf2a87fd58521ff6b92417fd1921effa52405ff62572fbeb2aa57fd591daffb12b25ff4a510fbeb2aa17fd89442ffaf2a15ff5e540bfe8c8e17fd69506ffb12b0dff62562bfebcac1fbc495c2ffb12305ff62576bfeaca817fd895c6ffad2a05ff62570bfec4aeb7fd5950affaf2a0ffb58921ff6b12415fd791827fb12385bf5a470bfa8c8c17dd39182fba72385fd46480bbeac8e13fd89182efab2305fb4a470bfa8c8e17bd49182fda52305ef52470,0x2ad3d55aa9d35272a30d3f0a7594da298dd2e9a55d488a8dd5152a1f9429a835d0309fd93ec67a4cf0e9d833a6270f4dc89b1b352667e4ca698b32f365b2caf49561298e50fc9ed932f25ba48c48d490eb1fca3ce476a8e5f1bd234f46368bf716de29ec4cc88ff10a61d3435086190b6a12741f88321059e08d40d681370182009bfb47f04fbd9f66be777be8f5c5e8dbcc57884efd5ddd3b887676ec25d62ba9374c2e82dccd39177194e23dc2137ec6f62dd6db82b6ca6d42d909af1b58d6a14d1d5a0fb3ed671ccd7198c32dd6532c931911b1e8637ec611889b0c660f2c0697f42f655e42bb7573aae315b26b44166aac9158acaee15beaafa5512a7f54e129905286a39145028534fe89dc538da6e04c9697452c225644a409371247a46648208e351a0230e45828a3d11821ec4374862109da0e54130810900c9fde3f587e0cfa41f163dc87ac8f401e3c3c027718ec59d473a187344e589c7f389a7090dfd9bd2371c6d4cd879ad435686a08d1619f1335a65c8c9b98f33182623cc2e982b2ff25f40bca97632e2c5b6cb5916772c5457e0ae315702a34537ca569469284a4fcc9ce9362263c4b8c95d127f245246e08c3114b21fc4354851905f206c40347ed8fa91eee3d1477c0ec61d1639647138df51b8636206ab0d2d19f632706398c2617d62f085c80b6716582be855f8a84148028144e5098612ba246446f08a310f420fc3f907b70ee61cbc38306d40d56199c30885cd0b36158028e04e1095e11ac21383ec07740e441ab030005780a4c135022603d607080c80167025803c406880b100da00a40007ff22571ffe44aedffc69603ffb0ca0fff46560ffec32edffd865c7ffaeca0fff1e586ffec3285ffd7650bffa84b8fff61870ffe430e1ffd41603ffaecc07ff5c580ffec32c1ffd7654bffa82b07ff5d960ffeb8ac1ffd42603ffb0ca87ff5d950ffea12c1ffc79603ffaa4387ff50950ffec4ac1ffd80583ffaa4b07ff61970ffec02a1ffc865c3ffac0a87ff5d985ffec32c9ffd86503ff912b27ff5d964ffeb22e3ffd805c3ffb0aa17ff21940ffea92e1ffd851c3ffae0b07ff56560ffe44ae5ffd70543ffb0caa7ff59180ffec2ac1ffd76607ffaecaa7ff59152ffea9281ffc79543ffa8cb07ff5d984ffec22e3ffd865d3ffa84c0fff4a560ffec32e5ffc865d3ffac8a87ff5c941ffec08e1ffd865d7ffb0c887ff55180ffebb221ffd86487ffb0ab87ff60560ffeaa2c1ffd76487ffb0c907ff5d542ffea1221ffd74603ffa82907ff61160ffeb9301ffd76483ffae2907ff5d152ffeba2c1ffd75603ffb08a87ff60110ffeb92c1ffc79483ffb0ab27ff48470ffec2a81ffc79583ffae8a87ff48580ffec32c3ffd75583ffae4a87ff58110ffebb2c3ffd80483ffb02b87ff48560ffe90901ffc89483ffa84b0fff581,0x163c1b901e0c088dc81ac58f06e407868a59a930f01870d0844c401f074c2c0e9284c3e1b900e271362caa381e189c38088c162c178747851306816400162e1e2f0ea62a271362c5e1d30b8818b879345e1d38381f15cd62c786cd08c583e07874c1b079241d8b2a8f0e3c201487c4d286a2b8b250e0a0fc595c784d2868161d1e0dca1a060e0224d2e2c9c3c1b90ac261183f1637309b16540e8f0b87109343b9a148f81e8288981f8b2a074d8d201386e40d854938b2a8f0c2c0e83c5226c58dcaa8108d4182620141e0c2b8449a58d06816400043f163826a49021079503a4d1e0f8b298a94c0421c58e0c0f0888c181d28e86e4d029381e593868171520077163738989a5227044a33028f0701d87e2c36544868178b1c134786289386a49c59547878a8b04f8b13074d8b270f06e4011001821078e0c260d02f1b8b200bc3a4d4874790f061004c4d2a8a7163728b01f9ac5a98785109004c3e1c0f0c051e1009a26181386e8060e09a112457162f29134a5607868058b878dce4a060446e4250381837206b1b8b0e934b150d8771637295c4c3c06134a4a0783022372944940f1a924185508a04c4d2913878527100185207934c0b160bc3a3c292804401f0dca262a0303a11283c2b9a060f0a9a2b8987c0f26981f8b2b8f09a5061401e372068184d0e844a510e884943524a1c7c0f2aab1a4a270e080b16100058b878bc3a810900ac3c1f148c1ac5960784109489a4e2014184a078e080b118b0781d06181c0f178f03a52b03c058b878dcc1a0a89b164d0e9816532043f1638269c1e5713030224d309a2a530162c6e66406c1e4906154227201407c372084804e2b0301e52382c462c070741861306a2b8b250e0c40250f870413068162f0e8f0c5313138800287e2c6e8078021f8b2b934c1a05903170f0e8dce51251246a152a830f15cd1001844d1287c0f1b97164e1e0dc80bc686c818b0e8dce1a05c571627200985e1d483c3452cd49818113a54819a06044a2f20030580f0e984c1a0588c1c1d061c178b1315c784d3068160c088dca1a0594b358b530f0e0f0588c580e06074e26059341c1d0618178b1c134785250f0183720682a2329e2c6e614814780013c3f162628a442401362c180f1c1f341d1f03c987cd0f81e4109004d8b0603c707200844c0c078e0d87cd0f81e4200149c0f1b970e4d1f03c840c5874180f1c184c4dc58301e3836687c0f18f81e3718848026c58301e3838848026c58301e383e1f343e07935ce6b61d629ab1f53d6a00d379a5e34a7e902d159a1c73fbe7bccef19caf381667fcc41972b2b5e527c9b5925b22963f3c7838daf19862adc467870b09260cec0a97fb2fb95ee6bcb5787eee05d73ba3b738ae465c09b7436d0ad71dabab4c9685ece0d947b1d1626ec19d7cbaf455d7ab8456d6ac8357d,0x271480b0fc5c44ac34442c3c3e128f0aa6c58fc92292a947c2cc58bca80e0e8f10be1f12880582e2c7c2f2b8749a3c3818058b200dca4e0602078342ae91a8f2b62c582f5e0dd2871f09c8400cd1003a294ec3e7cc645002a4901444182108103169a5c43dc2a2b8744eb887cf8528090f91608088d0c509f06c438b87944a88a404c1f268d10019371e26161e06094785532f09c2c5f23c798b0a8d1215028f04d3ec59183a284c683610c58d8b06060dc225423224c1c078d4539a0602822a060b05202130bf16540e8f142e1e23c6c578d62d22384d224c8f674840441060e3171a0aa3270e9d1483a211e0306a4087898ae2f14e2ca859862c2a8b288bca83c0e84520f0612422552d224c0f8d0ff34401585418a138169d0f2c95344ac5c5678382a9ca53e0ec3f165830c4380a1ce2c7830385494269f62c00462c219c27098d083e2530080be2c18700c0895481a200306e0f2a18723300074b40425100533e4d43d8ba478b078085e0bc6884d4f86b0f2562c3a364275908b149287036060a022a0283f161f2c151f4e90b005e4124844718b46c69193870b80a8fc5a4470543c3c1840c59247e55387802051e4f8ae9a1b62c60385a2c4657060749a113938784a4d057353c0121c18a6201660b8b4ed022ac170f20a280a95c0ab71c4f31646533894268ae2ca258343c1840c58007e543cf8438b878e0a865d23c5c151814842350715c5e3c1362ca8bc2cc57c3e109408056309c959a4d03222a60e854804fc5a761ee53918ae1d028f04f115c62d4d0f62985c1d6732a1a4b1e0467838c5a6a22b8794d80211e2f8b265f0f892402a961e0c1310316271f95509d07a2c9c38c58d8782808a91e525f62c3abc2c1c524a132fb16005e16110f4d03a7c571b437173c1c2991400a8003b11061287240c585d350f7038523c132fb16bc0e8a12211d300acbe2c9b348f2709c944093468183620e2c9f1d46056127170a4505702ce0718b0aa324c466e2c3c8b1795c3a4d08a018112c0c9c5247e2c3a912c1ca4219f62e1e561a1c5c4a1323f16004896102f278f06c487a6a7c35c592a781d1b261e2e0eb38824b65044718b86a6a18b872685c4a87e2e22382aa11608060446851623d1627c5a44123441492a2717964a8b1b0b052261195018110ea9353e2562e1e382a9c5c1d2d0446c513118a6be2c95162c02a3c1091178d10051e0991e8bc5a443a284a683b151a92b16362c22348f458d7164a488746c90d0302237203c050fc58bc3a607e694c0c08941f8b1e0dc82213898183808984c0fcd0302250d637161d1b97160f178f03a507a57340c1e14598d1389b162f0e9c4c0fcd62c1c3c315c340fc58749a61393b16551c0f0c5627100058b878dce301303f358b1e184e4a2a83070113138703c182c582f1e074b1529e2c364d283f,0x3a38c5a6a809b7348004a2d0a43a404ea6a1f3e5d224c0f8d0ff3440060a422a6443c780c1c100ab8b4d11940c24844aa4a407c1f2620118191a08a61e1e0dcfb161d9e16111d170849c381462c6c3c4948784a9f030809a14c3c458b11965a3e47c68a0562062c5e911ba9161ea70e3160e2c0f108f0a8383abe8e94c798b5e0e1711a0014949d53077169a4dc3d6225f1343e41603c4d8b1b8f06078e8f89c38c58d81c281e249c3e040f0685878b82a9a2ae6804a6061021a59c5d02189d8140363cc5a5578512a2056051e0fcab8b1b8a502e1343f16540ec44aa81481494a62d12478cd1c2dc8cce607c182ca762c6e581e2116121f0dc785431347c4910a74521d200aa7c9a87b05c1b87e2c3b112c1c4d3e2b62e1e271a1e161e2b8bf164d0e8f11482b030223728b02e1d13e2cb26000f1a53c86a985f0506100b38b4ed0134f9d04852ce4d140818b178c46eb8587858290eb38458b1b96078b458991e23298b316911ba6750f138985f8b0e85caa9458547c2508954d0b060546e3c2a1a4d1acd4748046061e1612060dc785432749c2b060c09438c58d8503c58b06c54088303a6a40a44e262a830701140306e112a124c8f0eb3a3a0520e2c70158d23236da4056343fcd100182b1e24465708934181d362c182f2b8749a3c3e2c421a20030100f1a21904614874440c2a0e0229000744e0f5f144802944361e2e180b0a53e070dc782211e2e785978903a5a14a1c430f202682f3e5d000111530303ad22062d3a9a87b04821078e57c40149e901f9303080468d0f102c9f09e1f8b048d0e1a0809c5e592b2058290e8886e0c2c04520c12844aa4a41584d8b11900180f1ba51e56c58b05e911b9c6c2c1189b1640061501e1d5124790d532745e0c20166798b4d4456ee0a8a67c53118b316171ba44205a743cb250289892ce0b154c3cc5a5578382a183a401362caa370603c529248a4045a02084809a9f2e21eb0d900182507954d3a160861e08178d0eba46a3c5c308d140ac40c58bd783769262340530313a1d2062d4e9a87b0b22102958b030670a51480303e4d1a200326e114c3c00d2530be1a0c2016717404ec3134e9d04802561662c5e301ba49c4a87e2e2252129c4205a743cb255333a9ca10a808788708cf0709ac5c4570f1f09c1f4ec59541c381e26912607c687f9a83900182908ac3b8b4796483e07b38718b071607881f084ae54671648070608e9c561e0dcc1d250bc810f2c18a44a134fb170f2895508f0a8997c23298b316bc1ba83a28179006c564500621718074182188854818b4d2e21ef0b12478552030534e1389b16551c0f12a6672861a2f248f0233c1c26b17115c391e49934745ec006100b38b46c69193774f0ac529f43c798b0a8d124e2806c0a8fc5a44a25448f8a421478d47857178444d8b2a244b2e,0x30ac111a1018211d338b21130c090051e0745e461b221e129f09f173c2b0d110f67100ac23c58fc6e8170f20b0f108d47c11c589868550bb45d0f13e2e22561a1c243c6753b16111b9d801d5f16493c138542f8b0ec54aa8458544f15c59541c381e2616151f0dc225436690e3e1095484290e9013a0a9f43da3910928605a149b170b09030103c1a1e3a21250e0500c1b04504004030684878a43b3e0608478350789b16342a85dc8b0e8f23a8f2981716911c2a161214b38ac23c58f06e9645205201078841835130454c814958460c088dcf0b0a8b3162f2a0747880d92a7d0f0ee2cb07a407c583706160227859182a1d4a88b16541c0f144211e2c801d2a746e2925075353e4dc3d30b060544a3c2a99910f0e0847826048306a4014e2c68467274424d1a874804814e2c1e0c1a119a290e814784a9f070a69d87e2c70c438b8790d4d15734029e29818402cc1717404ec446570d62c800c079343a9260b8423c869299a059e0e088ce5336901d2006b16382a83c191a232c9c3e161491e3c1b8444423c5a44b2d9d4361e0e170867835078f04d8b1a1542efcd05443404d154191153074809dc585e1ef19084b23c670c0cc8a40845c0fc58d41c261e287c230703e9c561e0dd00f5326b3446200313a11492b17159e1484a610816223c2529970ce182678a60e8f29d050a815][i]?.getD 0
def m511H11 (i : Nat) : Nat := #[0xb14d000153d66d5176e4f11f3a76800024c75011087c379448d8100000ff000398768809bad86819a811c00bd12392e024be4776c223f566c000a025e29886f22d845e905f5130e153f855ff261a33983bd61a5bac0592e0972446fd95372400f101a20d34245d586e292a090d9f4d87d165f6c48507468000b68e464c8b00afc504000000348436b0000d0e000098165f7b12ace20000000f802d86414dd8900000007068000a62393a589a0dbd08ecf2b1f3da1c4821fed4180000000000c736c9a000095cd6668ba0002542a6ba8ab27771bea104dd1000304ec1775f67833442681185201a897e18a897c525387937c68a0a7e7da9b22cd85730f42a674c130844457191dc00200019e0c27a9b3a5a1573a2440cd43196469716854c638e4bf9118b00000000e29fcef37a08dd0000000000203508dc00044634ee16cbc9733a8a13434c4a4a583d92c7288ed541d0cce2fd855b4361c61601cbca4dfd63717382073b000005ac00041e9d5249255e2c430e07373314960064cbf6e7dab142b46be0d2e12317bd3bc808545665c0670344dde73688b3e0e6a060000d8d0002d1ed900488433b1bbf529927000000003d0000000315800000000000000f5fd550b4b2418744264a28604f795300b200039afe73b1215072c430000000d209c3b475c00027f34b767c31c001ca58b00000000000000c8af95976f4000b5f547441b162e43815fb02fa024000245fb3530f9616b615522bd6ab3ae14e979ea41469092dc0ba91d8314d46053fc4b34bd88ed3e1c3698c30731306827b8a3dc8303606f4496d04f2f69f8c450000b42c00032360620001a27000264202159cb00000000003d8cd44c1e9882b0df0003956b277c3325d3017885ec560001014c18f59d0002639c24c00001449d42182a45e2679c3b54e880552160308d392be59000000000000002d33464193902194fba16c9efc459c2f877dc9b9651621c08822f92a9ca55054622c38dc2608260004361debd4a68c2c102058b847d34c0b39ecb7099fab5a4068b6a3e3248c763cf82c8b9057a16f367a5aa0003648613400084e3d98b3d5982e76c8a257b458f035813e150110821124ac00014cae207943074b02540f2503264e8e583908fdb59b225f78ce3b0002dc700028c900510101190386014120010013490e04031e00000e6102060403030d1d0204030d04000102000b14030004000221090807052e1d1e240102111202023e00180f000000015d0a2005044200001200045202100019050d00000845000d08140212050e0400013304030306000a1a03190adb062a000314062a85000a01001426014b001705030e010d14001b000206000a4c000807010e1503000029001613000006002e001d040005192505182727032700030107040501140a110e077700000a05020003,0x1cf3454795400018a1e2984ae22574f00001c9c0001d79d23d59c41fe175000000040eb876431c000c6940001711e08f07fd62000000020b41fd455f147047dd35e00e845813ec28c8fa10fa7cb47138e887dd21c978e87581b5785c16e65843273dacf10049e3dc8e3da773a2831d2d20bbd742e24b6b58b1248fcb6927e10e839ecd006d90e6b5c25ea6613983575adb41790c3e74ffc89e5b3902e045069637917a80c015af771d36402206144c8126504d2356761100f35d46e768011574660757706e1634894a94843083a3225eea35696db56ce19701386d1490e1cb042e0fe5ee223f6decfac2b555d10ac9e5c348c59a2a2614973c0dc66f344cb59c065c07b1557233cd9e807d91403303f08784a341c2cfc3767007f03984967fe057b303d9fa8d8da210764c496ff4b5d2401e620f7c46533d066902891cc1edd4b43a441974a09a6d5ddc78425bdf5862a429b1f][i]?.getD 0
def m511D11 (i : Nat) : Nat := #[0x37fd744a510bff62962503f7d7459550bff42887587ff98758120dff615695037fd7462510dff5e529583fbd8259140dff525295837fd7a42486dff60579583fbd8112570ffb589215c37fd875a520dff48579503fed625c120dff5d1895877fd815a540dff5d18958bfbd5659140bff5288758bfbd825d140ffb58921503fbd625d140dff48579583fbd2112570dff585795037fd215a540bff4288758bfbd655d140dff225795837fd165e560fef584495c3fed8458920ffb5d162487fed7458920dff459695037fd825e540dff589795037fd825e560fef608495c3fbd6212570dff595795037fd825a540dff55979583fbd6512570dff55969503fed8758920cff1a9891c33fc6862470dbf469691c36fd5a5a470d7f615791836fd865a470fbe5d9604436fc865a470fbe5d9604836fd525a470dfb1e42961aefd6a21d609ff26984583fe942601209ff269865cb3fd2162470dbf4a9691c3fe94258120dbf615691c37dd864e470dbf229691c37dc864e4709ff26971583ef94658110ffa549604827fd9a21d20cff585891c27fc9a61d64fbe519604837dd524e470dbf605691c27fc9a61172ddf619591c27fd9a218709ff269865437f58546460dbf629691c27fd6a4a480bfd4680961b7ed864a470dbf485691c37dd854e460dfb219291c3f6d8554920dfb469291c27fc9a61d509ff269864837dd5a4e460df7615391c33fd62624709ff269756036fd165a470dfb549291c27fd6a4a470dfd619191c27fc9a61d209ff26975483fe972601209ff668875827fc9a61d60ddf1a9591c33fd6562470ffa5c960482fed6a54920df7605391c27fc9a5c5809ff269865c67fc9a5c9609ff269765427fc9a5c9509ff269755937dd8a4e460dfb5a9291c37ed854a470df7485391c27fc9a61171fbb619624867fc9a5c5209ff269645c7eed8658920dbf609691c36fd265a4709ff269845437ec6a4a4709ff269865d67fc9a61d10df7585391c37ed814a470bbf5a88758b7ec29025869ff269645437f585464709ff269644436fd265a4809ff269766036fd565a470ddf485591c2ff51a225209ff269724437bd8652470dfb569291c37bc8652470bfe428874837ed124a4709ff269756127fc9a61910ffa5898048377d6156470bfb4a8874837bd52524709ff269726037ed614a4709ff269644837dd824e470df7589391c27fd9a21d629ff269766127fc9a591809ff269764427fc9a61120fdb595524837bd85524609ff269645ca7fc9a5d560dfb229291c27fc9a61110df7595391c37ed854a4609ff269764837bd8552470ddf609591c377d6256470dfb609291c37ed624a470def605491c37ed8a4a470dfb595291c37f48a46470dfd609191c37ed624a480def485491c37bd6152470def609491c37bd6252470def595491c3db9475c140,0xffe60170482ffd7a59181fdf5d18554affd8a55960fbf60976583fbd5259140bff629521c2ffd1a21970dff615691c3ff97058120bff5a952503fbd865d140fbf619651c37fd705a550ffd605211c3fbc865d140bff5a9215c2ffd8a54960fbf51916583ff96460120bff629215c37fd855e460ffb54970483ff9815c140fbf619565837fd7462560eff5d16860affd1a21940fbf5d9565837fd0a5a487fbf619625c37fd7462550dff5d989482ffd5a1e560bff5e964486ffd8a59570dff519695437fd891e560bff568895937fd705a520bff5a9215037fd815a470dff62479483fbd525d140bff62921502ffd0a21970ffb591524837fd745a552bff568861c3fed7660952bff629525c37fd7656520fef61564503ff5815c110f7f609475c3efd8658940bff62956593efd7659182ffe5d160443dfd6251d70bff528766177fd8a5a470bff62965503ff9215c140fbf619655c3ff97460120bff5e946587ff58148570ffe611604837fc7956520dff58189482ffd2a21d60ffe1e960442ffd1a21974ffb609521c3ff97458120bff269766037fc9a5d982bff629595837fd6462552bff629525037fd745a550dff485691c3ff56148470dff5d169487efd8655964fdf5d9655437fd7946560ffb609525837fd7462521fbf619655037fc7956560dff58159483dfd6551d70ffd60521503efd7655964ffb5d152483ff9615c140dff61979503f7d6554870fef60564503efd8251960bff5287961b7fc7946520dff611694837fc865e540dff26976607efd7461962dff52519583fbd855d140bff568865c2ffd8a59574dff5c1894837fd745a520dff485792037fd165a470bff428865d37fd7462552fdf559605437fd865e560fef618495c3ff5615c110ffb609525c3ff57460510dff5c159483efd5651960bff568865037fd6462520bff56889583fbc8612570bff5e80961b7fd525e540fbf619655d3fbd2159140ffd585215c3ff57460521dff61969503fbd815d140bff5e96460b7fd615e480bff26964603f7d6554970bff629611c3fed6460952bff629621c37fd6456520ffb609525037fd895e560bff4287961b7fd704a510fdf59570543ff56148540dff54979583fbd5212570dff5c189443fbd1659140dff62549582ffd4a21d21ffe60970502ffd5a21974fdf59552503ff9625c140dff5d1894837fd525a540dff55979593fbd215d140fdf51965543ff97a58110dff615795037fd825a470ffd5d161443fed7460952dff5d159482ffd4a21d61bff42887487ff94a58110bff629615c3ff97a58120bff629625c3ff57458521ffe595705037fd7956560bff5a879543fed6248470fef58574503ff94a58120fdf5d16554b7fd855e560fef614495c3fed6260120dff565495837fd625e480dff559691c37fd815e540bff6296150,0x83ffd525c160fff5d186583ffd865d150fff61576593ffd5462560fff61570583ffd7454960fff5d589583ffd8551960fff61970443ffd8648570fff60570583ffd865c120fff61159583ffd2160170fff619615c3ffd855d160fff48570583ffd851e560fff61974443ffd6160170fff61974487ffd165c160fff5d181583ffd865d120fff5d121603ffd7461961fff61570483ffd7448560fff5d161603ffd815c120fff619655c3ffd7445960fff60970583ffd8558870fff60970543ffd855e560fff61574483ffd6560170fff61549583ffd8756560fff55970583ffd815e560fff615625c3ffd874a560fff58570483ffd7460520fff619655d3ffd7460960fff5d182543ffd8558940fff59574603ffd7455960fff609611c3ffd825c110fff6157458bffd7458520fff609615c3ffd655c120fff60961503ffd7460910fff60979583ffd8252560fff595821c3ffd7460961fff59574483ffd6560970fff59582503ffd655d182f7f619675c3bfd765a180f7f549675c3bfd6860160fbf5d919583bfd6860170fbf61976583dfd8559d70eff51968603efd7662560fbf54976583bfd6860470f7f605675c3dfd8651d70fbf51919583efd865d964eff5d168603dfc8651d70ffe5d980543efd7656560f7f485675c3fec2a61870eff5a1815c3efd855d960f7f549475c3efd8651960fbf5d96454befd764a560ffe60160543dfd1659d70eff5a1815037fc791a580fbf51989583efd815d960fbf54946583f7d7661552bff56929583fec2a61970dff61979593ff9805c150bff5a879603dfd8551d70fbf61576593f7d8554870dff469691c2ffd5a22576bff62929583bfd745a181dff5d989583fec2a61940dff5d989543efd215d960fdf61552582ffd2a22576dff569691c37fd705a510ffe61970503ff96460150ffe21970503efd4656560bff5e96454bbfd6860870fbf61546583dfd8151d70dff619691c3efd7659181f7f609675c3efd7622560bff66980583efd7645960ffe5d9804837fd6062550fbf51929583f7d8554970ffb0a9865d2ffd6a54870ffe54970503ff9801e520dff5d969543ff97460150bff62879582ffd5a21d60f7f559675c37fd525a470fbf60546583dfd2151d70ffb5d952483efd7659121fdf5918554affd1a21870fdf61552503ff98a58120dff615795937fd7062560ffe60160483bfd6860970dff625595837fd7662565dff5d169443fbd8659140dff5c189543fed521e520bff5a9211c2ffd0a1d985bff629211c37fc9a5d985dff1e519583fec2a62560bff5a8875837fd7662552fbf619621c3dfd6151d70bff5a9525c37fd4662560fbf5d946586ffd8a59470eff5a1825037fd6462550ffe61570503fed5258120fbf485465837fd894a560fbf619765977fd805a520bff66887583ff9705811,0xd476897648761175c67599756c7549751274db74a4744f73fa73b9736e732d731472e772ba72837256720b71c071897148711170b27067703a700d6fcc6f816f406f276efa6ed76e826e4b6e0a6de76db06d6f6d426d156cd46c896c666c2f6bee6ba36b626b0d6acc6a956a546a1369dc69af698269556932690f68ce6879682e67ed67b6677f675c672f66f866c16676663565ea65bd6586653b650464cd6496644b640063c9637e6347631a62e362a26261623461f361c6617b6158612160fe60d160ae6077602c5fd75fa05f735f285ef15ec45e795e385e015dd45d9d5d705d575d165cd55c8a5c495c125bbd5b905b455b045a9b5a645a2359d85997594c590158d45889585c582557f85799576c572b56e056b3567c563155fa55c355aa555f5528550554d8548d541a53e3538e5361532a52f3529e5271523a51ef51c251955140510950c85087505a500f4fce4f8d4f564f1f4ed44e9d4e7a4e4d4e204dcb4d764d2b4cfe4cbd4c724c314c044bd74baa4b694b1e4abf4a9c4a794a564a2949f249b14970492f48ee48a34862483547ea47a9474a471346d246a54664462d45f645ab4560451f44ca4489442a43f343c6438f4362433f42f442c74286423b41dc419141644137410a40dd4092406f40243fd93fa23f573f0c3ecb3e943e5d3e303e033dd63da93d683d273cdc3c913c463c053bc43b793b4c3b293ad43a7f3a3439e939b23971392638f938a4386d383637eb37aa3769373c36fb36ce36833638360135de359d3552351134bc348f344e340d33ae3377332232eb32be3291326e320f31ce3165311a30cf307a304d300c2fc12f942f492efe2eb32e722e452e182de12da02d4b2cf62cb52c882c5b2c242bcf2b982b6b2b202afd2ada2a852a3a29ef29ae2959292228c32878281927d827ab27602729270626c52666261b25da25ad2562253524f4249f2468241d23f023c323822355230a22bf2288223d21de219d2148211120da20ad2080202b1fd61fa91f361eeb1ebe1e731e321e0f1dd81da11d741d3d1d101cd91cac1c571bee1bc11b941b5d1b1c1adb1aae1a811a4a1a0919c819691932190518c41897186a180117d4179d1770171116e416c1168a165d163015ef15c2156d1540151314be1491146e1437140013dd13b0136f132e130b12d412a7127a121b11f811cb1180113f111210db10ae108b105e0fff0fdc0fa50f820f4b0f140eb50e740e3d0dfc0dc50da20d4d0d160cdf0cb20c710c440c0d0be00b8b0b2c0b090adc0aaf0a460a1909ec09c9099c096f0938090108de08bb087a084d082007cb076c0735070806d106900663062c05f505c805870550050f04e2048d0460041f03ca03a703840357032a02cb029e025d023001f901cc016d011800b90082002d0000fff61970583ffd865c150fff615765,0x8802a90080be0f0d0825068190b418178b454371540a0f0cce852cd47d07b3660a83e0a4406760f66a3e0c53c58a80e8782795878fa0f1608108941e0722d05260178b07c59205e2cc1e2c139a61c3e108291020f6763e05d402c9d078b2409c05e2c8f164a2a47d078aa409187168291020f66a3e05d2178b3078b04168301446137178783a2a143e8f81315480e89a2d03e414c05e2c27058593076078182c11d2168291019d66a0f8f900ec7d0785040301d0444220522d08107b340bc7c1ca03e8f81f15091f052288c30158378f82828420883a2d05251081115462483a088aa402c56154ce1644030421e0941c8b4149a3e0c0581b340ec7d0786c51500c044552071c58282a902a0f8291019d83d9a8f8314884088503e2c02444592048110220107206052714c3a008580301f3034060222a901de2c5510830281e140181b123e0a451181f078b412902461c5a0a44083d9a8f81748841e0503074270538b164a210222a0c1de2c3c0dc30284dc58200e8a8561c3e03f9a108296760f8f921503a5c41f1f0526e2c1d0f04d07ca2487843c7c180aa60f01ae2d11164a2d022140c291684083d9a05e3e0e50cd0b5078a22a1426040532f859284fc582c2c905300b8b0f0580c0c1f03f1f05040778b0c03c0dca02c9d078b244743a118000a00c0d81140720e8b41488107b351f02e983e3e1606670a40b0a8402c37044542734c387c210522041ecec7c0ba83e8f81f15081e0722d05241244015461f47c098aa4e2c3c13c42204c02f16098b250778b11028154b1f41e2c0c49100551b3a14b351f41ecd98540740c10491d41e128a840e41d03c54e2c3c15416430e1f01fcd08414b3b07c7c90a9b883e3e0a4a080a65f0b2412b8b0d03c13ca0023bc58781406060740c04c372043c583a1e052526b8b0e017154a178b3078b048dc021578b0f430303a060222105251243c21c5a0585530161a078141039168291020f66a3e05d0178b3078b048dc02154110302933a42d0522033acd41f1f220f8f8581c7d078b0303e0f16825201f1f05228902a0f8291019d83d9a8f831481f078b412903e8e84066a0f154c01026210ac40dc5616a0f150a02c9d078b2409187168291020f66a3e05d2148b42041ecd02f1f072861c3e03f9a108296760f8f921537107c7c149439168291020f66a3e05d08af34060784873786f686c986888665862e860185de85a7857a8561853e850784da8499846c8453841c83ef83c2839f8372833182fa82cd82a08255822881fb81ce81a181748147810680d980b6807f8052801b7ff87fc17f767f5d7f3a7f0d7ecc7e957e727e457e047dcd7da07d697d3c7cf17cc47c8d7c567c297bfc7bc57b8e7b617b2a7b077aee7aad7a807a4979fe79bd797c793b791878e178be78877846780577c477977760771f76,0x3e124291344200817431e0a86a29f16df0b07cf83914c3e15c0205ce170609e0b023178b078d23370f274c9341e0c19c0e97c0b9c1d2f8c016491321e2d2181f0a31988c883c0f9014d118a18005c59340b941583138016111641c380acd4192033708990f0be1a03050118d1e41e1c82e4431260f0390c04630785f1802c900c05430e2d9a8463c38522019c2d0ae5b99a7e2c9a26cca05cbc582a230e1d100420310c118d058065c0791e0b20e1e0f66a0c1493505cd0782a1839d063341e47884f03015c17244c07b9d1986a2318400319a11e40830c12094ce87d078720147c14a50f0f2334f0462b1f1303c0af1657c9b0ea0409400c4f04628785f1802c90212f8c0164919860230c2f0fb8bc349b07440158b74c4c0e0188a88e231a150bc420f827e2c171003627540a852df06dc58ad1b9c1e11b8b73a1166a3c3d348621e2606c2517c0ba0051281911899f048148001182e683c03055ce6683c8f0fc58381808c486829e2dbe89858934e0f418998180b8b3089c400319a83047902113c180e81e148a223180f6683911881340a2888e46681a8f83905ca2001823b35204186e2c0c054570743c07c17444c8789e2001919a1823238b0309d0744005cc1e2792688c4084be300592316148aa0885054304ee2c0a2dc3c1663c40800f0189e08c50149511c172219c5967078880547872544711861808a230d9a13812030111660e4dd0200190608ecd481089c9a0bc150778b158b73880c58b488896141915130300304066a4083110602a0788e23143e0138b6fa1b0744015a374b34860a01e16f1e06271083e09f8b6f80a100368753c5b351e41e1c82e60982b14446241e06060cd4181e4787e2c30074b705ca01852230c150160c1653305cc4a8981801906080cd48108a44c0ac0c668409020c3f165c0581e0620b982e0985111890782ae74181e3351e1d210c20c11c80905c028a09602e6130468300c6684090211421813278258505048296f81de2c568dce148788608c40f01a0e4172060cd0182048106183c8305911880ac18998180b8b3089c306680c83040902113c18028802388c51302b0304066a40830e8606227716050721e0b31e241e66a0c1493505cc2608c0641820335204228e2c1a6683905ca133168889614143c168290d881e0b41486c40a45a1020f668178f83940722d0522041ecd47c0ba02f1660f1609cd30e1f0842585307880cec7c0bac5608c2603c0c0443738781c8b414900f0980c0dc5502811383814b351f41ecd99be1045918302a19c2c080512b8b0d03c0a4a2483a1e0aa414c26e2c41164a1f02d1f06840ab9a83e3e0a4bc582e1e0aa47485a0a4406759a83e3e4734c387c210522041ecec7c0ba83c0e45a0a481e0722d05240740c044420a4a1181e187161e06e683c1c0a78b0e054301624,0xa59a83e3e544c078182008c5e2c1d128132e017341e063350602a1e4787cf8423283412c17321e2d0950d07ca008c70c429cf84b0089a0a8e018521e08c40bf8b85402164a12e0f9d09e178b244f0120842c05ca130a61e08c42682f0fa150778b100562dd2178b3088b04055334751b8324030240671707086cd4787cf83515c172082210189e08c5054276f80ae2c36874e6701e0114e1c969a4310f0d417288a0b8a152982fe2c3705c9d3884200189e08c50882f11860297c2b87248988f0f08c1663305cf869341787c29f1653020200b066ad3c128120e4172d7d0787c2b8521c8042320528f0570e488780a1308e23178b03c022e0172b3acd07c14c7c1b16e18a2be0f851118907b3401b371e141e0338b0744027431380a1808a23110c0e13c15080905220716df0af1bc9a80d0290005a0e4a6706a29f16c78b06e2e150bc59348cd307c860b0231004e2dbe83d9a0ae3c3c1e8d01f064809b983e0c19a83c11830dc582a2b83a0b973a100380bc17285c0af1619814471787048408cc3c118a14c18230c4e164bc16080c07c1482e4e2c12030153284a10017422a0a861c5b9ccd4231e230d2682ee2c17274cd3c3a2081823108f0f08c1422c05cc17c2a4d83bc58ac5b9c0c0742c0f0550accdf07c2888c40982f0d846207c2b0aa2311be0900f08f1a118c2d0526705e2b19a5b9f3e274420744a3344934b0f48820608c30303611862c918230c1d0b02f1188dd31e8a85e2c978b1280fc3cd2334c27880090189e08c62e23e0a4490901730539f134110040b9829e2dbe00859886383f174d67c1c0ae0b98440985705c88785e0c59c2b06a231f8b0543514f3e160c0f0481f37c0ef16200ad1ba78b0784a328172b7c878841b08c1c980c0a458118815b9d07822cd41860778b26c9d0c4b4d03dc586a0b950f0f2338761b431403f160908ce733508c78766915030409020c367c4d0520e84e001940ba19a6fa0f2de3c0c4c1702a13716050521b8791e24410f0be300592b7c1482e2a910c0a53c1442b2879060a0231057230461a2a1782bc586e0543a70f00f0e446241e06335060571e182e12b0d33859328b8382429f179f018020822c19a98750f430420f851118e1e0801588c40160c9005920420d0720b903c1002b1188c7a2bc585e2cca5269c570a4171a4d07831060182902e7668950320c10240844f0781e99c802314a626b8b0552f3349d3a1f0d01e0d0ac8646e75010f9403e1444633340f7161a82e53380f000ca0e4a180441788c43385215c39239c0288a231005230c0164825080cd33720418607b8bcf80a274cd3717078611e0425982e72982f85436e2c562dce1237d0d83bc58ad1b9d0c298180f03005cd0781906056cd478623c3c8cc0c05c59230e02c19200b240d82f11869714c4d7170a8ae5b99a8cf8,0x39000d1089e2c8044669350a444000acd42a4e96a6506c2b9d9a3283605c000e4ccd23a9aa941b0ae6298190f82683017300a2202e309805832112e0a02052230d0f130be0cc462c184ec1e07c80231a0f030350984005cc2b81859c1c0bc1860bc3c11017221e1a84c5f02e58320f014388441c367c2a052268041202e76683e0860c102112dce1f3344ac1e08c1864f10f03c39118b1e41e1706a130800b9e1d0f10c1188148790608c40d40c11874d21e2617c0b94a6830212cc1728322be7c0102e52744ec34a60778b158b7404414c23078181982f06220c0559a00d9b8f0d1e41e1706a130800b9f8b0543c0e0bc070c1482e203035140462418131580b938b0c04a0c417285e0286c23113c43c2e0d426100173c1806335078610886e7054030e23c070a670a613716c78b060302c0a459118a8a958178adc588e0b86c4ea52683c180320c148173a34078802310050bc3611880f07ccd47815c1860782ee2c3302a0e8f0f9f1360400066e1e60e41714182cc222c102f0d8461c3a0537d1303bc58ad1ba0440983e0d817293a237162b83a0b984a0bc461c19078581982e5e2c1e09b3e14c5830a5060a823119a8f83905c88780b2907ca008c683c0ce2d9a456118f0e1a878230dce0c0050f0462d349e21e078720b988f016380f0592301c393b9f052010440b982e08b8b83c3f6682b8f100907d1e056cd41860601d0f82905cb8d0248611c5e06e60980c2ce0e05e0c30ac148428608e5030360a446221e108580b90530980c11882905e230c2b0a4171a9dc5c2a4d8b06698accf80415b8b11c3627519f0841383a2d0000b9f8b8399a83d9b8f0d5f0520e8a22314440b03e15c17283c1e08c30bc400a43620761f0b2200b0566826830b505cac38785c47c2b8520e1d9a049be8f0370c4c4a860e741ecd023061d0c0e11115080af16160660b958f4545309b8b6f85838b412804150725e2c1534b0f334a060502a85223160f0f133030171660c3c4c8780a2107ca008c70302815429118b0a94c277161a02e4e9d0c0bc380d8462858178b20b90409480c4f04628720ab7d1e41e0b990f0bc4203050118d5f0ae0b0a84cf80f000022e017305e2c9782c109d0fb3e008420003138424608c36f90f008460e4a1786c230c3e2f8591188c785e2c8f3e0a40812c17282415b9d063341e47874b89a1038b854572dccd40801c05e1802e52f0120b017208414e7c1f0000102e70c01de2c9d05ca180941788c40780ce2e0e668438f0fc5c0b07870148a860542ce2c3305ca860a21488c4c682e0e05705ca860522888c41144614340281f1988023191d4980c03c40118d8d11e060222c9191b9d8fe2dbe86c58934d9d058178b20b960f09a11030290dc148311078065c4784cf80f00002334d2c3cf8699c178ac6696e67499d168101441d,0xfc400a41022950783e0e8ae231a0583c45004902c1e1f88029a7060c0460046a503e0c89423163c0784400481c8522b8e0f0fe0511457287e208560e102915c507802180d26018560512729582982e53919a8151a115210c4c0b8522988c40e436141e2614e2c8045268a71641024811e0561f90290fc171c1e1f8ae14912604c400280249cd078981f8b201152c1640249c813040200204a6a21048244f02b0fce158a60508c4130410fc022025138b201120f548521188148141587e45004c0fc02223707852938b2231a9a26c59040818088008e0f0fe051145328081485000120f07c3f15c1d2c1e2280239020f0ac46000acd13b078945a86c101c010c04c58721b0d9a900400408cd242188522c8306854ca0a45115cac5802148c170942908090dc42158542309260069a0d89b15ca14a781587e41041f0fc3c15ca148a6080ae46691d9001e130440d8f4d2802000240e40414c58008b0780c1f8b201154a14c4615c815852220924454d228459008acd02e1c2701014100e4590088878822787e01160f11401180218099a3280a0d][i]?.getD 0
def m511H10 (_ : Nat) : Nat := 0x34ec4e165521e8000624d1bbabd514a3dd36da1c001a510005bb9c5aa0e20da033884000d1b38a7db6000a540002539103e11a3c402622031d3a384860004588b4e9464d5669087800066200000035074a4000000000000056c41050bd8f7a7d11190e24ca00042544a9cfe000431f0f1a30015d8985116dc122597c5ea706057720a49cc1a166124c964b0801893e2c142e310e30949d623e427e19d04fa560258b2091e64a7742ae291829d86b92f6d37efdb069afe557ea7d5bc90081147415b492100f466819c2b4d030ac059fbcb92d24790a73c307e01d80103254d606387e701b8eb4fbc65d0e25230f310933db4aeee5505e219431cea37252100c38bb7684800423ed69486a8292fce9e49540880ae3210190ab4fe90775cf97554de4910fda6b933a39a04836b80385cb52b1bb5ff055e3c8aa6dbd0a1e73e9c8d8c66cd3df9621b24edd3bda02445300c5f49f345fed1929d14901e2c3a60fb3717421072c93e54326b4c5ae415da9c3b63f6915d8a617c613131581894b2da991603021b34d2348e16dfc4280024a0a160580002512000e762bd3545a9873400038e70157268000000835f3e9980dc4e5a53578d000062e784e278001028e1e000353f0040000000000000332d3125de000482133ed7948b0001377dcd2ced37f8b15c0000820d00007b04000304470000700907001d0a020b0d0a180e011705003408160003454b110c0000102701021e10050032321101001520090d0c15081309211000000a000101190506000f0f080004075f080f02002600007800
def m511D10 (i : Nat) : Nat := #[0x54974502fdeb5a4224ae1fed585215d140edfb048b2d2385fbd8b484495c2bfec5aa4bca81ffa589215c140fe7acaa92e8a07ebd86588495c3b7ec32cabca81dfd605215e540bf7b16b2892b857fd8b54979582fdec5aa424ae1faf6196512570ff6b0290892b857fd8b54969502bfead90cbca81fdb5d16554920bf7b16b0ae8a05fbd8b58974503bf6c12a4bca817ef56c8612570efeac290af2a077dd82585391c3bbeb2aa4bca81dfb609525e560ff5b04a9092b876fd82559691c3fdab0a4224ae1dfb609525a540ff5ac490ae8a07f3d65548495c2bfead912bcac15ff62d615e540affb16b12f2a05fbd8b584495c2fdec5ac424ae1df7595824e470efdac490af2a077bd85589491c3fd6b124224ae1def6096152470ef7acac12923872fd18619691c3b3e92ab4b48e1f6e619475c140fb710ca3ae0a076ec2b619691c3f74a92ecb0241f6e549475c140edea428d2d23873dd68605391c3b3ec2aa4b48e1f6e615475c140adfa568d2d23877cc2b619391c397e9430cb48e1cbf4618a5a470fdd2a4a32c0907db98151d70502b7eada4cb48e19bf6295a5a470adfa36432d23856fd8b469691c2bf6cd854c30e1f6e485475c140adfa568b2d23856fd8b485691c3baec2aa49c8e15bf62d565a470fb72c2a3ae0a056fd8b4a9691c2b7e8d914b48e15bf62d525a470e7bad0c12723876f581485691c23feb5934b93011ff5ac9a5d580edda24952d23857dd6b549391c2bee8d90c9c8e15bf56c865a470adfab6952d23866fd8a4a9691c397e94314b48e15f75ad214e470afbb1690a72387db98251d70503edcb128eb82815bf56c8a5a470eddb04a92d23876dd86589391c2beec5aca9c8e1cef5a18152470edea428b2d238767d25559691c2beec5aa49c8e1f6e595475c140edbb0cb2a723877d581485391c3b7615b14b48e15bf62d5a5a4708ffa164d30cb977ac2b619491c23fe55aecaca415f756c864e470adfb168b2d23856fd8b499691c2bf64dac8a92411ff5ac9a61150ef9b04a92723877d561485391c23feb5934bab09dd7595524e4708ffa164d30cbaf73d85549491c33f614af404b0ddbb449265a470afd936bb2a49047fcab5d9894839deb4304a48e15fb42c790a586afbb16b0a723857dd8b589391c23feb5934c3aa15ef5ad5252470af7a36432923847fd6b269845cabdeb5a42a48e15ef62d21524708ff956bb312a876bd86589491c3be6b12429c8e15ef62d6552470af7b16a92923876bd86595491c3bdac0a42a48e15ef56c8652470ef5b04a92923877b561485491c3b9eb2aa4a48e15ef62d6152470af7b16b12923877ad62485491c2bb6ad914948e11fb2ad864a470a7db16352523856ed6b229291c2be69d914948e15f946c8a4a470afca36352523847dd3b26964482be69d8d4948e15db56c6a4a470,0x35b616c85a8969259dd65158d961057d55da56fd59955cd55854f5517541d4f7539d4c1526d48051c1460511542a50113e94f653c94eb939e4e0d3684d3533d4c052f14b852c64aad29049a924f48a520e47751cd46c91a2461d15644c110a430d09d41dd05c40ad0053f7cfb93df4f623cf0f163bc0eca3a38e683908e2737d8dd03624d63349cd013314c7e3160c3d3088bfc2f2cba52dfcb592cccb182bf4ad72af0a9629eca3f280c9e8273499c2604945247c8f9234c8b821f085620c080a1f3879d1ddc7511cd87051b7c6b91a4c66218f061617c05ca169057e156053d145c4f113584a511fc46410f84230ff43e20e983800d9433f0c0c2e80b0829c0a0425008a8204074c1ad061c16104ec11503bc0c9028c07d01300260003ebec2aa4b3ae1e7f5a18151d70fbd856c328eb87e7d8554976582efec5aa4b3ae1efe5a1815c140fafb0aa928eb87e7d765918554bcfeb4304a3ae1f9f6155251960ffd056c32e0a05dfd6b549475c3ef6c12a4b3ae17bf62d525d960bbfa364328eb85f7d7b5918554aefeb5a42a3ae177f62d2151d70f9fb0cb128eb85dfd8b595475c3fbcc2aa4b8281eef5a1815d140bbfb16a928eb876fd765918954bbbec2aa4b48e1f3f6196551d70fbeb0290a8eb87eed8254976583b7ec2a54b48e1efe5a1825c140ffd2a4b82c0907fac2b61974502f7ec5aa4a32c17fe5ad525c140bbfab64328eb86efd7656889583f9ec2aa4b22817fe46c865c140fbdb04a928eb876fd82469691c3f76bb2c8c12a5cff5a1815e540bff2d690ae0a05ff98b48570503efab0a42a3ae1fdb615525c120affaf6b2312a976fd82569691c3ff4ba2a4b0241fbe619625c140fafacaa928eb85ff98b59570503f9ec2aa4ba281eef5a18112570fddb04a928cb05ff98b54970503bf615b0cbca81fbe619655c140ffe30290ae0a057fd8b549691c3ddeb4304ba2817fb5ad525c120bbfb16b0a8eb85dfd8b589475c3fd615b0c24ae1fdb5d18554920bf7ad6a92e8a05fed7b5918254affcad90cb82817ef46c865d140fddb0cb1242b85fbd8b54964503ff4c12a4b8281fbb619625c120eefb0aa92f2a05fbd6b485745027fe55aeac4ac1ffc585215c140bf7b1690ae8a067fd5b269766037f6ba2d4a9241dbf615265a470efdb04a92d2387f796554970503f5ec32c4ba281f7b5892151d70bf7b16b2ae8a0777d8554979583f9ec2aa424ae1cff5a1825e540bf7b16a92e8a0777d8554969503f5ec32caba281fed605215d140affad6a92f2a07eed7461962487ddeb430424ae1fbb5d18658920ff5b04a92c8a05ff98b58570502ffcc5ac4b82815ff46c865e540bf7ad6a9092b857fd6b48579502fdead90cba2815ff62d215e540edfb0cb12f2a05fbd1b218495c2bfec5acabca81df7615624e470fedacaa92e0907fad82,0x601052102829c583c207c0a8808046102b082908570817060203c09040d820a41e080082903a33941280e039219a03c0c06054148818029101202a01060a427882304180707841481d101e008204866c404c250401c270830082908c207383c4040cd8808041e040101300a10060f0200814840f83c0803056100a100404c2002b180405223344980b8f0781e100508020600a440e400829181f00a100612820080a830119a0600a46118207c266c204c20046184f0a4128601420080f84cd842904a104a0802935098148c0219b1029081f080508020601072010466818080c04f101f0d9a3940e40e81c28300839083005223340c041281c880f8400563078100407c20046180508027347280503920300804052206010720104e68e500a0724052090050ccd02939a322a031cd02b023030c00c1e0461818c7c05c60702a09cd40c880e6c98f8148b718290146dc783ccd9cd180c022e6815c0c282d03220331680b8c14e3e33a3052090050e1e01c0a8301804415b9a81850841680a0c211ca01430720c440f81484202e4032cf80b8c8abce056045cd40c300f05a06478f85983e0840c4b83ccd9cd19ca0840a41f0172803056f39cd03c87860300f80a0c1c83111d239a20538f8ce8f1f0293340a8809800846180b06c05c60901480a18420b405060e41888e503910420b405060a4050814e3e33a305a06458f8ce83e0840c4a031cd02b023030a00c2308e50391042052728ce901480a11ca0840a41f01728290146dc78f8148b7199a0527346748e689e702b022e6a0614211ca0143c7c66cdb8c0c45a02e33941081483e02e50a602c2c84620198b405c60ec2c04619ca072207c0a421017201807c05064f0298391c3c07205c6108149ca33a4c7c0a4db8c0583602e33340a4e68c0585008c3c1e66ce68c2bc8508e30480a4050c13054102f06c11860a71f19d184708c207c0a421017203907c05060e40b882105a02830720c4409800846182d0322c7c6741f042062505e0d8230c1480a102405202867282102907c05ca748e688211ca0143c7c66cdb8ce50391042052728ce931f02936e33340a4e68c1f02908405c80e41f014182405202861680b055183d02c16478f818055185a02c15460ec0b055185a02c15478f818055183bc6f1561e101d8300aa3c7c0c02a8e14784b211c83da0e6832e0b0825607a815204480a600e7ff9fee7f21fb87e75f827d71f417c99f167c19ee07b15eaa7a3de747965e287861e0877b5ddd7735db27689d8775b1d517505d317459cfb7381cba7225c637121c226ff1be16f45bb66e99b8b6dc1b556ce9b1f6c11ae96b65abe6a8da886989a526909a27685d9fc67859d167059b1665997b65ad95064a98f9634d8b86275877617184c60f182c60457f65f6d7b55e957955de975f5d117345c656f,0x5214c4028180814870785304c30a610280c0407815880f0261030052203c14c130c080409829101904c2c1e1052131e0ac0e8c14840f824102b05220260ac020c0f046100a060209e109e133a074050c0f80410243362c1e0d4400414880b830140544d03c13101484278409810102908290829c1e2060103e05440e400880a83510300810084f03e20600a450541488c78520943b347281c81c201c07810461180808cd0300523026118080f078151030081506a209e10a6074407c08080919b100105220600a4404007880219b10290847020261e05440481488c78180a43][i]?.getD 0
def m511H9 (_ : Nat) : Nat := 0x3a5b4414c259c383236018b056b84e53004a21291004bc0000000010a00006930201c28
def m511D9 (_ : Nat) : Nat := 0xc02002b08180404c20000f840ac20260562000f84e6c2001f081804e680c0408e020239b0800c033095c6a12f879bb9bacc57aa93288419c8c244138582200f9b968605475c140fda82c619475c140fd3985549475c140f9b968609475c140bdb96c549475c140bdb91c219475c140bdb96c485475c140bdb98c485475c140fcb986589475c140bdb98c595475c140bdb98c549475c140fcb986595475c140fdb181485475c140bdb95c219475c140fda982549475c140fdb161485475c140fd3965549475c140afadac0ad8612570bdb98c585475c140bdb98c589475c140fda962485475c140
def m511L : Nat → Packing
  | 14 => (1,0,7,0,0,1,0,m511D14)
  | 13 => (33,1,7,0,0,12,0,m511D13)
  | 12 => (377,2,7,0,0,15,0,m511D12)
  | 11 => (588,3,7,0,0,16,0,m511D11)
  | 10 => (266,4,7,0,0,14,0,m511D10)
  | 9 => (21,5,7,0,0,9,0,m511D9)
  | _ => emptyPacking
def m511I : Nat → Nat → Option (Nat × Nat)
  | 14,h => lookupWord 11 42 4 10 6 0 m511H13 (mixTag h)
  | 13,h => lookupWord 126 424 8 13 9 0 m511H12 (mixTag h)
  | 12,h => lookupWord 196 667 8 14 10 0 m511H11 (mixTag h)
  | 11,h => lookupWord 89 298 8 13 9 0 m511H10 (mixTag h)
  | 10,h => lookupWord 7 29 3 9 5 0 m511H9 (mixTag h)
  | _,_ => none
def m511 : Forest := ⟨1535,14,m511S,m511C,[[]],m511L,m511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_14_0 : block m511 14 0 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_14 : block m511 14 0 1 = true := bm511_14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_13_0 : block m511 13 0 33 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_13 : block m511 13 0 33 = true := bm511_13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_12_0 : block m511 12 0 15 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_12_15 : block m511 12 15 130 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_12_145 : block m511 12 145 232 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_12 : block m511 12 0 377 = true := (@block_merge m511 12 0 15 362 bm511_12_0 (@block_merge m511 12 15 130 232 bm511_12_15 bm511_12_145))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_11_0 : block m511 11 0 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_11_1 : block m511 11 1 145 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_11_146 : block m511 11 146 370 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=6)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_11_516 : block m511 11 516 72 = true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_11 : block m511 11 0 588 = true := (@block_merge m511 11 0 1 587 bm511_11_0 (@block_merge m511 11 1 145 442 bm511_11_1 (@block_merge m511 11 146 370 72 bm511_11_146 bm511_11_516)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_10_0 : block m511 10 0 10 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_10_10 : block m511 10 10 101 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_10_111 : block m511 10 111 155 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_10 : block m511 10 0 266 = true := (@block_merge m511 10 0 10 256 bm511_10_0 (@block_merge m511 10 10 101 155 bm511_10_10 bm511_10_111))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_9_0 : block m511 9 0 21 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bm511_9 : block m511 9 0 21 = true := bm511_9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tm511 : checkedTables m511 14 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bm511_9
  · exact bm511_10
  · exact bm511_11
  · exact bm511_12
  · exact bm511_13
  · exact bm511_14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gm511 : graphValid m511 (boundsBefore es511) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lm511 : Lower false (vars 511) (graphGoal 511) 15 := lower_forest (g:=m511) (i:=0) (hints:=8591013460) (before_sound es511 (known_down vs511)) gm511 tm511 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fromLower {u : Bool} {k : Nat} (lb : Lower u (vars 511) (graphGoal 511) (k+1)) :
    Impossible u graph k inputs.toFinset := by
  have vr : vars 511 = inputs := by decide +kernel
  have tg : graphGoal 511 = graph := by decide +kernel
  rw [vr,tg] at lb
  intro s hs run
  have rr := list_run run inputs (by decide +kernel) rfl
  have sup : supply u (inputs.map observe) (inputs.map observe) := fun _ hm => Or.inl hm
  obtain ⟨q,bs,hq,hit,le⟩ := contraction (observe_proper graph_proper) rr _ Reach.start sup
  have hlow := lb q bs hq hit
  omega
end PEqualNP.Outside.L_meta_10830
open PEqualNP.Outside.L_meta_10830 in
theorem PEqualNP.Outside.L_meta_10830 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8)) t → 15 ≤ t := by
  intro t ⟨C,legal,small,computes⟩
  by_contra! low
  exact directSplit (fromLower lm511) (fromLower ls511) ⟨C,legal,by omega,computes⟩
