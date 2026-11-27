import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12098

-- The circuit semantics and the live wire restriction lemmas are adapted from
-- L_meta_10802 and its predecessors L_meta_1674, L_meta_670 and L_meta_1667.
-- Adapted from L-meta-10698 (PR 15033) to six-input truth tables.

open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 64
def zero : Sig := 0
def one : Sig := BitVec.allOnes 64
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

def bit (i : Fin 64) (a : Sig) : Bool := a.getLsbD i.val
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

lemma b_read (i) (w : List Sig) (j : Nat) :
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

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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


abbrev Row := Fin 64
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
  if h : r.val < 64-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(64-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 64 (64-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 64-d.val <;> simp [shifted,h,r.isLt]

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

-- A restriction is stored with its lower bound and the restricted signals
-- available at the stated cost. Constants among the live wires save gates.
abbrev Cut := Sig × Nat × List Sig

def cutTest (c : Cut) (k : Nat) (ws : List Sig) : Bool :=
  decide (k < c.2.1 + ws.countP (isMaskedConstant c.1)) && ws.all (availableB true c.1 c.2.2)

def CutGood (T : Sig) (c : Cut) : Prop :=
  ∀ k ws, ws.Nodup → cutTest c k ws = true → Impossible true T k ws.toFinset

theorem cut_good {T d raw L} (s : Slice true raw T d L) (cs : List Choice)
    {pool} (hp : makePool true d raw cs = some pool) (afford : cs.length ≤ L) :
    CutGood T (d,L-cs.length,pool) := by
  intro k ws nd checked
  simp only [cutTest,Bool.and_eq_true,decide_eq_true_eq] at checked
  apply poolCut_sound s cs hp nd
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (by omega),checked.2⟩

def properB (w : Sig) := w != zero && w != one
theorem proper_of (w : Sig) (h : properB w = true) : proper w := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h

def bothFlags : List Bool := [false,true]
theorem has_flag (b : Bool) : b ∈ bothFlags := by cases b <;> decide

def moves (ws : List Sig) (k : Nat) (a b : Sig) : List (List Sig) :=
  ([0,1,2,3] : List Nat).flatMap fun d =>
    let z := bin d a b
    if properB z && !ws.contains z then
      bothFlags.flatMap fun ka =>
        (bothFlags.map fun kb => childTwo ws a b d ka kb).filter fun v => decide (v.length ≤ k)
    else []

def children (ws : List Sig) (k : Nat) : List (List Sig) :=
  ws.flatMap fun a => ws.flatMap fun b => if a < b then moves ws k a b else []

theorem listed {ws : List Sig} {k a b d ka kb} (ha : a ∈ ws) (hb : b ∈ ws)
    (ab : a < b) (legal : allowed true d) (fresh : bin d a b ∉ ws) (pr : proper (bin d a b))
    (short : (childTwo ws a b d ka kb).length ≤ k) : childTwo ws a b d ka kb ∈ children ws k := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  rw [if_pos ab]
  have dm : d ∈ ([0,1,2,3] : List Nat) := by
    rcases allowed_four legal with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  apply List.mem_flatMap.mpr
  refine ⟨d,dm,?_⟩
  have ready : (properB (bin d a b) && !ws.contains (bin d a b)) = true := by
    simp [properB,pr.1,pr.2,fresh]
  dsimp only
  rw [if_pos ready]
  exact List.mem_flatMap.mpr ⟨ka,has_flag ka,List.mem_filter.mpr
    ⟨List.mem_map_of_mem (f:=fun kb => childTwo ws a b d ka kb) (has_flag kb),decide_eq_true short⟩⟩

theorem swapped {ws : List Sig} {a b d} (h : allowed true d) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Perm (childTwo ws b a (flipOp d) kb ka) := by
  unfold childTwo
  rw [bin_flip h a b,List.erase_comm a b]
  apply List.Perm.cons
  cases ka <;> cases kb <;> simp [kept,List.Perm.swap]

theorem by_children {T k ws} (nd : ws.Nodup) (absent : T ∉ ws)
    (h : ∀ w ∈ children ws k, Impossible true T (k-1) w.toFinset) : Impossible true T k ws.toFinset := by
  apply enum_step nd absent
  intro a ha b hb d leg ka kb ne fresh pr short
  rcases lt_or_gt_of_ne (show a.toNat ≠ b.toNat from fun e => ne (BitVec.eq_of_toNat_eq e)) with ab | ba
  · exact h _ (listed ha hb ab leg fresh pr short)
  · have p := swapped leg (ws:=ws) (a:=a) (b:=b) ka kb
    have e := bin_flip leg a b
    have other := listed hb ha ba (flip_flip leg).1 (e ▸ fresh) (e ▸ pr)
      (ka:=kb) (kb:=ka) (p.length_eq ▸ short)
    have eq : (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
      ext w
      simpa only [List.mem_toFinset] using (p.mem_iff (a:=w))
    rw [eq]
    exact h _ other

def sameWires (ws vs : List Sig) := ws.all vs.contains && vs.all ws.contains
theorem same_wires {ws vs} (ok : sameWires ws vs = true) : ws.toFinset = vs.toFinset := by
  obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp ok
  ext a
  simp only [List.mem_toFinset]
  exact ⟨fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp l _ ha),
    fun ha => List.contains_iff_mem.mp (List.all_eq_true.mp r _ ha)⟩

abbrev Cuts (T : Sig) := List {c : Cut // CutGood T c}
abbrev Links (T : Sig) (k : Nat) := List {ws : List Sig // Impossible true T k ws.toFinset}

-- Each child has one of three witnesses. Two rows can disagree on the target
-- and agree on every live wire. A restriction can exceed the remaining gate
-- budget. A previously checked state can have exactly the same live wires.
def closeCase (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) (ws : List Sig) (code : Nat) :=
  if code < 16384 then
    let r := Fin.ofNat 64 (code % 64)
    let s := Fin.ofNat 64 (code / 64)
    (bit r T != bit s T) && ws.all (fun w => bit r w == bit s w)
  else if code < 32768 then
    match cuts[code-16384]? with
    | none => false
    | some c => decide ws.Nodup && cutTest c.val k ws
  else
    match links[code-32768]? with
    | none => false
    | some v => sameWires ws v.val

theorem close_ok {T k cuts links ws code} (ok : closeCase T k cuts links ws code = true) :
    Impossible true T k ws.toFinset := by
  unfold closeCase at ok
  split at ok
  · simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at ok
    intro n _ run
    obtain ⟨w,hw,ne⟩ := live_row_difference run ok.1
    exact ne (ok.2 w (List.mem_toFinset.mp hw))
  · split at ok
    · split at ok
      · contradiction
      · rename_i c _
        obtain ⟨nd,good⟩ := Bool.and_eq_true_iff.mp ok
        exact c.property k ws (of_decide_eq_true nd) good
    · split at ok
      · contradiction
      · rename_i v _
        rw [same_wires ok]
        exact v.property

def checkMoves (T : Sig) (k : Nat) (cuts : Cuts T) (links : Links T k) :
    List (List Sig) → Nat → Bool
  | [],_ => true
  | ws::rest,data => closeCase T k cuts links ws (data % 65536) &&
      checkMoves T k cuts links rest (data / 65536)

theorem moves_ok {T k cuts links vs data} (ok : checkMoves T k cuts links vs data = true) :
    ∀ w ∈ vs, Impossible true T k w.toFinset := by
  induction vs generalizing data with
  | nil => simp
  | cons v vs ih =>
    obtain ⟨closed,tail⟩ := Bool.and_eq_true_iff.mp ok
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hm
    · exact close_ok closed
    · exact ih tail _ hm

def checkNode (T : Sig) (k : Nat) (ws : List Sig) (cuts : Cuts T) (links : Links T (k-1)) (data : Nat) :=
  (decide ws.Nodup && !ws.contains T) && checkMoves T (k-1) cuts links (children ws k) data

theorem node_ok {T k ws} (cuts : Cuts T) (links : Links T (k-1)) (data : Nat)
    (ok : checkNode T k ws cuts links data = true) : Impossible true T k ws.toFinset := by
  obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hn,hm⟩ := Bool.and_eq_true_iff.mp head
  exact by_children (of_decide_eq_true hn) (by simpa using hm) (moves_ok tail)

def inputs6 : List Sig := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def minorTarget : Sig := 0xfe80e800fe80e800

def goalfefee8e8fefee8e8 : Sig := 0xfefee8e8fefee8e8
def rootsfefee8e8fefee8e8 : List Sig := [(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)]

def goalfcfcc0c0fcfcc0c0 : Sig := 0xfcfcc0c0fcfcc0c0
def rootsfcfcc0c0fcfcc0c0 : List Sig := [(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)]

def node0gfcfcc0c0fcfcc0c0 : {w : List Sig // Impossible true goalfcfcc0c0fcfcc0c0 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x11400860086009204140092011404140114009200860086009201060106011404120012009204120092011401060106008604120006041401060006008601060086041404120412 (by decide +kernel)⟩

theorem lowerfcfcc0c0fcfcc0c0 : Lower true rootsfcfcc0c0fcfcc0c0 goalfcfcc0c0fcfcc0c0 4 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 1 zero), 4, 6), ((inputs6.getD 2 zero), 2, 6), ((inputs6.getD 4 zero), 2, 18)]
  have ok : checkEssential goalfcfcc0c0fcfcc0c0 rootsfcfcc0c0fcfcc0c0 tests = true := by decide +kernel
  have cov : tests.map Prod.fst = rootsfcfcc0c0fcfcc0c0 := rfl
  apply lower_impossible (L := 3) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node0gfcfcc0c0fcfcc0c0.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha

theorem fiber0gfefee8e8fefee8e8 : Slice true rootsfefee8e8fefee8e8 goalfefee8e8fefee8e8 0x5555555555555555 4 :=
  slice_correct (ms := [(zero, (inputs6.getD 0 zero), 1)]) (base := rootsfcfcc0c0fcfcc0c0) (G := goalfcfcc0c0fcfcc0c0)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowerfcfcc0c0fcfcc0c0

def goalfafaa0a0fafaa0a0 : Sig := 0xfafaa0a0fafaa0a0
def rootsfafaa0a0fafaa0a0 : List Sig := [(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)]

def node0gfafaa0a0fafaa0a0 : {w : List Sig // Impossible true goalfafaa0a0fafaa0a0 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x11400450045005104140051011404140114005100450045005101050105011404110011005104110051011401050105004504110005041401050005004501050045041404110411 (by decide +kernel)⟩

theorem lowerfafaa0a0fafaa0a0 : Lower true rootsfafaa0a0fafaa0a0 goalfafaa0a0fafaa0a0 4 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 0 zero), 4, 5), ((inputs6.getD 2 zero), 1, 5), ((inputs6.getD 4 zero), 1, 17)]
  have ok : checkEssential goalfafaa0a0fafaa0a0 rootsfafaa0a0fafaa0a0 tests = true := by decide +kernel
  have cov : tests.map Prod.fst = rootsfafaa0a0fafaa0a0 := rfl
  apply lower_impossible (L := 3) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node0gfafaa0a0fafaa0a0.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha

theorem fiber1gfefee8e8fefee8e8 : Slice true rootsfefee8e8fefee8e8 goalfefee8e8fefee8e8 0x3333333333333333 4 :=
  slice_correct (ms := [(zero, (inputs6.getD 1 zero), 2)]) (base := rootsfafaa0a0fafaa0a0) (G := goalfafaa0a0fafaa0a0)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowerfafaa0a0fafaa0a0

def goaleeee8888eeee8888 : Sig := 0xeeee8888eeee8888
def rootseeee8888eeee8888 : List Sig := [(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 4 zero)]

def node0geeee8888eeee8888 : {w : List Sig // Impossible true goaleeee8888eeee8888 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x9200430043005104120051009204120092005100430043005100830083009204110011005104110051009200830083004304110003041200830003004300830043041204110411 (by decide +kernel)⟩

theorem lowereeee8888eeee8888 : Lower true rootseeee8888eeee8888 goaleeee8888eeee8888 4 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 0 zero), 2, 3), ((inputs6.getD 1 zero), 1, 3), ((inputs6.getD 4 zero), 1, 17)]
  have ok : checkEssential goaleeee8888eeee8888 rootseeee8888eeee8888 tests = true := by decide +kernel
  have cov : tests.map Prod.fst = rootseeee8888eeee8888 := rfl
  apply lower_impossible (L := 3) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node0geeee8888eeee8888.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha

theorem fiber2gfefee8e8fefee8e8 : Slice true rootsfefee8e8fefee8e8 goalfefee8e8fefee8e8 0xf0f0f0f0f0f0f0f 4 :=
  slice_correct (ms := [(zero, (inputs6.getD 2 zero), 4)]) (base := rootseeee8888eeee8888) (G := goaleeee8888eeee8888)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowereeee8888eeee8888

def goale8e8e8e8e8e8e8e8 : Sig := 0xe8e8e8e8e8e8e8e8
def rootse8e8e8e8e8e8e8e8 : List Sig := [(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero)]

def node0ge8e8e8e8e8e8e8e8 : {w : List Sig // Impossible true goale8e8e8e8e8e8e8e8 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero)], node_ok [] []
    0x8600430043004501060045008601060086004500430043004500830083008601050005004501050045008600830083004301050003010600830003004300830043010601050105 (by decide +kernel)⟩

theorem lowere8e8e8e8e8e8e8e8 : Lower true rootse8e8e8e8e8e8e8e8 goale8e8e8e8e8e8e8e8 4 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 0 zero), 2, 3), ((inputs6.getD 1 zero), 1, 3), ((inputs6.getD 2 zero), 1, 5)]
  have ok : checkEssential goale8e8e8e8e8e8e8e8 rootse8e8e8e8e8e8e8e8 tests = true := by decide +kernel
  have cov : tests.map Prod.fst = rootse8e8e8e8e8e8e8e8 := rfl
  apply lower_impossible (L := 3) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node0ge8e8e8e8e8e8e8e8.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha

theorem fiber3gfefee8e8fefee8e8 : Slice true rootsfefee8e8fefee8e8 goalfefee8e8fefee8e8 0xffff0000ffff 4 :=
  slice_correct (ms := [(zero, (inputs6.getD 4 zero), 16)]) (base := rootse8e8e8e8e8e8e8e8) (G := goale8e8e8e8e8e8e8e8)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowere8e8e8e8e8e8e8e8

def cut0gfefee8e8fefee8e8 : {c : Cut // CutGood goalfefee8e8fefee8e8 c} :=
  ⟨(0x5555555555555555, 4, rootsfefee8e8fefee8e8), cut_good fiber0gfefee8e8fefee8e8 [] (by decide +kernel) (by decide)⟩

def cut1gfefee8e8fefee8e8 : {c : Cut // CutGood goalfefee8e8fefee8e8 c} :=
  ⟨(0x3333333333333333, 4, rootsfefee8e8fefee8e8), cut_good fiber1gfefee8e8fefee8e8 [] (by decide +kernel) (by decide)⟩

def cut2gfefee8e8fefee8e8 : {c : Cut // CutGood goalfefee8e8fefee8e8 c} :=
  ⟨(0xf0f0f0f0f0f0f0f, 4, rootsfefee8e8fefee8e8), cut_good fiber2gfefee8e8fefee8e8 [] (by decide +kernel) (by decide)⟩

def cut3gfefee8e8fefee8e8 : {c : Cut // CutGood goalfefee8e8fefee8e8 c} :=
  ⟨(0xffff0000ffff, 4, rootsfefee8e8fefee8e8), cut_good fiber3gfefee8e8fefee8e8 [] (by decide +kernel) (by decide)⟩

def node0gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 3 w.toFinset} :=
  ⟨[0xeeeeeeeeeeeeeeee, 0xfafafafafafafafa, 0xfcfcfcfcfcfcfcfc, (inputs6.getD 4 zero)], node_ok [cut1gfefee8e8fefee8e8, cut0gfefee8e8fefee8e8] []
    0x4300510092004300830092005100830043008300434001010301130051010300430103004340010083010300834000 (by decide +kernel)⟩

def node1gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xeeeeeeeeeeeeeeee, (inputs6.getD 2 zero), 0xfafafafafafafafa, (inputs6.getD 4 zero)], node_ok [cut1gfefee8e8fefee8e8, cut2gfefee8e8fefee8e8] [node0gfefee8e8fefee8e8]
    0x83009200510083004500510114004500860105011400510105008301050083400000450105004540010043005100920043008300430043400000430045800000430106 (by decide +kernel)⟩

def node2gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 3 w.toFinset} :=
  ⟨[0xeeeeeeeeeeeeeeee, (inputs6.getD 2 zero), 0xffffaaaaffffaaaa, 0xffffccccffffcccc], node_ok [cut1gfefee8e8fefee8e8, cut0gfefee8e8fefee8e8] []
    0x4300830043400100450043008600430086008300450083004304030043400100830403008340000403040700450403 (by decide +kernel)⟩

def node3gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xeeeeeeeeeeeeeeee, (inputs6.getD 2 zero), (inputs6.getD 4 zero), 0xffffaaaaffffaaaa], node_ok [cut1gfefee8e8fefee8e8, cut3gfefee8e8fefee8e8] [node2gfefee8e8fefee8e8]
    0x92008600830045008300450051041400450083010500834000005104110051400100450414004504110083004300434000004300518000004300430045008600430106 (by decide +kernel)⟩

def node4gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xeeeeeeeeeeeeeeee, (inputs6.getD 2 zero), 0xfcfcfcfcfcfcfcfc, (inputs6.getD 4 zero)], node_ok [cut0gfefee8e8fefee8e8, cut2gfefee8e8fefee8e8] [node0gfefee8e8fefee8e8]
    0x43005100920043008600510114008600450106011400510106004301060043400000860106008640010083009200510083004300830043400000830085800000830105 (by decide +kernel)⟩

def node5gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xeeeeeeeeeeeeeeee, (inputs6.getD 2 zero), (inputs6.getD 4 zero), 0xffffccccffffcccc], node_ok [cut0gfefee8e8fefee8e8, cut3gfefee8e8fefee8e8] [node2gfefee8e8fefee8e8]
    0x51004500430086004300450092041400450043010600434000009204120092400100450414004504120043008300434000008300918000008300830086004500830105 (by decide +kernel)⟩

def node6gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 3 w.toFinset} :=
  ⟨[0xfefe0000fefe, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero)], node_ok [] []
    0x4300450086004300830105004500830043008300430105004500140045005100430012004300510083001100830011 (by decide +kernel)⟩

def node7gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xfefefefefefefefe, (inputs6.getD 4 zero)], node_ok [cut3gfefee8e8fefee8e8] [node6gfefee8e8fefee8e8]
    0x51800000514000004500510114004504140043005100920043041200430045008600430083009200510083041100830105004500830043008300430105 (by decide +kernel)⟩

def node8gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[0xe0e0e0e0e0e0e0e, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x14005101140051004300510092004300430006010600430083009200510083008300050105008300430083004301050051011400510114004500430106004301060083010500830105 (by decide +kernel)⟩

def node9gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 3 w.toFinset} :=
  ⟨[0xf0f0e0e0f0f0e0e, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4300510092004300830411005100830043008300430005004500140051004500430006004300450083000500830005 (by decide +kernel)⟩

def node10gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero), 0xffffeeeeffffeeee], node_ok [cut2gfefee8e8fefee8e8] [node9gfefee8e8fefee8e8]
    0x114800000450045400000450051041400450106004300510092004300430045008600430105008304110051008300830086004500830043008300430411 (by decide +kernel)⟩

def node11gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[0xeeee0000eeee, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x45001401140045004300120412004300430045008600430083001104110083008300860045008300430083004304110051004504140045041400430106004304120083010500830411 (by decide +kernel)⟩

def node12gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 5 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xeeeeeeeeeeeeeeee, (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [cut0gfefee8e8fefee8e8, cut1gfefee8e8fefee8e8, cut2gfefee8e8fefee8e8, cut3gfefee8e8fefee8e8] [node1gfefee8e8fefee8e8, node3gfefee8e8fefee8e8, node4gfefee8e8fefee8e8, node5gfefee8e8fefee8e8, node7gfefee8e8fefee8e8, node8gfefee8e8fefee8e8, node10gfefee8e8fefee8e8, node11gfefee8e8fefee8e8]
    0x11400450045005104140051011404140114005100450045005140030051011480070114005180060051011440030114004540020045041480050414004580040045041440020414009200430043005140010051009280030092005100430043008600430043004540010045008680020086004500430043400040000106005100830083009240000092005180010051009200830083004500830083008640000086004580000045008600830083400040010105004340010043400000830083400040004000 (by decide +kernel)⟩

def node13gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xfafafafafafafafa, 0xffffaaaaffffaaaa, 0xfffff0f0fffff0f0], node_ok [cut2gfefee8e8fefee8e8, cut0gfefee8e8fefee8e8] []
    0x4501050045400100450405004540010083008301054000004300450106004301060043004301050407004300430405 (by decide +kernel)⟩

def node14gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xfafafafafafafafa, (inputs6.getD 4 zero), 0xffffaaaaffffaaaa], node_ok [cut2gfefee8e8fefee8e8, cut3gfefee8e8fefee8e8] [node13gfefee8e8fefee8e8]
    0x92008300830105400000510411005140010105004500454000004500518000004500860106004300430105004300510412004304120043004304110043004501060043 (by decide +kernel)⟩

def node15gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xfafafafafafafafa, 0xfcfcfcfcfcfcfcfc, (inputs6.getD 4 zero)], node_ok [cut0gfefee8e8fefee8e8, cut1gfefee8e8fefee8e8] [node0gfefee8e8fefee8e8]
    0x45005100920045008600920051008600450086004540000106005100920106004300860106008640010105009200510105004501050045400000830103010380000105 (by decide +kernel)⟩

def node16gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[0x3232323232323232, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x45005101140045001200510092005100060045008600450083009200510083008301050045008300030003008301050051009200510092004500860045008600430105008301050083 (by decide +kernel)⟩

def node17gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xfafafafafafafafa, (inputs6.getD 4 zero), 0xfffff0f0fffff0f0], node_ok [cut0gfefee8e8fefee8e8, cut3gfefee8e8fefee8e8] [node13gfefee8e8fefee8e8]
    0x51004500860045400001140414011440010043004501060043004304120412004304120043004304120045010500454000010501118000010500830043010600430105 (by decide +kernel)⟩

def node18gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 3 w.toFinset} :=
  ⟨[0x3333323233333232, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4500510114004500030411005100030003010500450003004300120051004300430006004500430105000300430003 (by decide +kernel)⟩

def node19gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero), 0xfffffafafffffafa], node_ok [cut1gfefee8e8fefee8e8] [node18gfefee8e8fefee8e8]
    0x92008600450051011400458000004300434000004300510412004300430045010600430083010504110051010500450105004504110043010600430105 (by decide +kernel)⟩

def node20gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[0xfafa0000fafa, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x45009204140045004300120092004300430045010600430105001104110105004501050045041100430106004301050051004500860045041400430412004304120083008301050411 (by decide +kernel)⟩

def node21gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 5 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xfafafafafafafafa, (inputs6.getD 4 zero)], node_ok [cut0gfefee8e8fefee8e8, cut2gfefee8e8fefee8e8, cut1gfefee8e8fefee8e8, cut3gfefee8e8fefee8e8] [node1gfefee8e8fefee8e8, node14gfefee8e8fefee8e8, node15gfefee8e8fefee8e8, node7gfefee8e8fefee8e8, node16gfefee8e8fefee8e8, node17gfefee8e8fefee8e8, node19gfefee8e8fefee8e8, node20gfefee8e8fefee8e8]
    0x5140030051009280070092005180060051009240030092011400450045005140010051011480050114005100450045400040000086009200430043005104120051009204120092005100430043800404120412400200430043800300430043400204120412400100430043004501060045800201060106004500430043005101050105009240000092005180010051009201050105400040010083004540010045400001050105400040004000004301050043010640000106004380000043010601050105 (by decide +kernel)⟩

def node22gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xffffaaaaffffaaaa, 0xffffccccffffcccc], node_ok [cut0gfefee8e8fefee8e8, cut1gfefee8e8fefee8e8] [node2gfefee8e8fefee8e8]
    0x51009200514000004500860086004500860045004500860043009204120092400100860045008600450051041100514000008300450086004500860403040380000411 (by decide +kernel)⟩

def node23gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[0x3333222233332222, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x45005104140045010600510092010600060045008600450083041100510083008300860045008300030003008301060051009200510092004500860045008600430105008304110083 (by decide +kernel)⟩

def node24gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xffffaaaaffffaaaa, 0xfffff0f0fffff0f0], node_ok [cut0gfefee8e8fefee8e8, cut2gfefee8e8fefee8e8] [node13gfefee8e8fefee8e8]
    0x51009200514000004501140414011440010043010601060043010600430043010600430106010600430051041100514000008304050405800004110043010600430106 (by decide +kernel)⟩

def node25gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[0xf0f0a0a0f0f0a0a, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x86005101140086004300510412004300430006008600430105041100510105000500050105008600430106004301050051009200510114004500430106004301060083008304110105 (by decide +kernel)⟩

def node26gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 5 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero), 0xffffaaaaffffaaaa], node_ok [cut0gfefee8e8fefee8e8, cut3gfefee8e8fefee8e8, cut1gfefee8e8fefee8e8, cut2gfefee8e8fefee8e8] [node3gfefee8e8fefee8e8, node14gfefee8e8fefee8e8, node22gfefee8e8fefee8e8, node10gfefee8e8fefee8e8, node23gfefee8e8fefee8e8, node24gfefee8e8fefee8e8, node19gfefee8e8fefee8e8, node25gfefee8e8fefee8e8]
    0x400040000092800700860086400300450045800600450045400300860086400100450045005104140051800504140414005100450045800401060106400200430043800300430043400201060106400100430043005104120051800204120412005100430043008600430043004501060045008601060086004500430043400040010083005140010051400004110411400040004000004504110045008640000086004580010045008604110086004304110043010640000106004380000043010604110106 (by decide +kernel)⟩

def node27gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[0x5454545454545454, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x45005101140045004300510092004300430045008600430011001100510092000500050045008600030003004301060092005100920051008600450086004501060043010600430083 (by decide +kernel)⟩

def node28gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xfcfcfcfcfcfcfcfc, 0xffffccccffffcccc, 0xfffff0f0fffff0f0], node_ok [cut2gfefee8e8fefee8e8, cut1gfefee8e8fefee8e8] []
    0x8601060086400100450045008640010043004301064000008301050105008301050083008301050407008300830406 (by decide +kernel)⟩

def node29gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), 0xfcfcfcfcfcfcfcfc, (inputs6.getD 4 zero), 0xffffccccffffcccc], node_ok [cut2gfefee8e8fefee8e8, cut3gfefee8e8fefee8e8] [node28gfefee8e8fefee8e8]
    0x51004300430106400000920412009240010106008600864000008600928000008600450105008300830105008304110411008304110083008304110083010501050083 (by decide +kernel)⟩

def node30gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xfcfcfcfcfcfcfcfc, (inputs6.getD 4 zero), 0xfffff0f0fffff0f0], node_ok [cut1gfefee8e8fefee8e8, cut3gfefee8e8fefee8e8] [node28gfefee8e8fefee8e8]
    0x51004500450086400001140414011440010086010600864000010601128000010600430083010501050083008304110411008304110083008304110105008300830105 (by decide +kernel)⟩

def node31gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 3 w.toFinset} :=
  ⟨[0x5555545455555454, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x500110114000500030011009200030003000500860003008300110411008300830005010500830105000300830003 (by decide +kernel)⟩

def node32gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero), 0xfffffcfcfffffcfc], node_ok [cut0gfefee8e8fefee8e8] [node31gfefee8e8fefee8e8]
    0x51004500860092011400860043010604120092010600860106008604128000008300834000008304110411008300830105010500830105008300830105 (by decide +kernel)⟩

def node33gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[0xfcfc0000fcfc, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x86005104140086010600510412010600860106008604120083001100510083008301050105008301050083008301050092004500450086041400430043010604120083041100830411 (by decide +kernel)⟩

def node34gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 5 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xfcfcfcfcfcfcfcfc, (inputs6.getD 4 zero)], node_ok [cut1gfefee8e8fefee8e8, cut2gfefee8e8fefee8e8, cut0gfefee8e8fefee8e8, cut3gfefee8e8fefee8e8] [node4gfefee8e8fefee8e8, node15gfefee8e8fefee8e8, node7gfefee8e8fefee8e8, node27gfefee8e8fefee8e8, node29gfefee8e8fefee8e8, node30gfefee8e8fefee8e8, node32gfefee8e8fefee8e8, node33gfefee8e8fefee8e8]
    0x9240030092005180070051009280060092005140030051011400860086005140010051011480050114005100860086400040000045009201060106005140000051009280040092005101060106400040010043008640010086400001060106400040004000005100830083009204110011005104110051009200830083800304110411400200830083800200830083400204110411400100830083008601050105800101050105008600830083400001050105010600830083800000830083010601050105 (by decide +kernel)⟩

def node35gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[0x5555444455554444, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x45005104140045004300510092004300430045008600430105001100510105000500050045008600030003004301050092005100920051008600450086004501060043041200430083 (by decide +kernel)⟩

def node36gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xffffccccffffcccc, 0xfffff0f0fffff0f0], node_ok [cut1gfefee8e8fefee8e8, cut2gfefee8e8fefee8e8] [node28gfefee8e8fefee8e8]
    0x51005100924000004501140414011440010092041200924000004304060406800004120083010501050083010500830083010500830105010500830105008300830105 (by decide +kernel)⟩

def node37gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[0xf0f0c0c0f0f0c0c, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x45009201140045010604120092010600060045010600450083041104110083008300050045008301050083008301050051005100920114008600430043041201060083010500830105 (by decide +kernel)⟩

def node38gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 5 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero), 0xffffccccffffcccc], node_ok [cut1gfefee8e8fefee8e8, cut3gfefee8e8fefee8e8, cut0gfefee8e8fefee8e8, cut2gfefee8e8fefee8e8] [node5gfefee8e8fefee8e8, node22gfefee8e8fefee8e8, node10gfefee8e8fefee8e8, node35gfefee8e8fefee8e8, node29gfefee8e8fefee8e8, node36gfefee8e8fefee8e8, node32gfefee8e8fefee8e8, node37gfefee8e8fefee8e8]
    0x400040000051800700450045400300860086800600860086400300450045400100450045009204140092800504140414009200450045400040010043009240010092400004120412400040004000008604120086004540000045008680040086004504120045800301050105400200830083800200830083400201050105400100830083009204110411800104110411009200830083004500830083008601050005004501050045008600830083400001050105041200830083800000830083041201050105 (by decide +kernel)⟩

def node39gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[0x5555505055555050, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x45005101140045004300510412004300430045010600430083001100510083008300050045008300030003004301060092005101140051008600450414004501060043010600430105 (by decide +kernel)⟩

def node40gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 4 w.toFinset} :=
  ⟨[0x3333303033333030, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x86009201140086004300120092004300430006008600430083041104110083008301050105008300030003004301050051005101140092004500450414008601060105008301050083 (by decide +kernel)⟩

def node41gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 5 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero), 0xfffff0f0fffff0f0], node_ok [cut2gfefee8e8fefee8e8, cut3gfefee8e8fefee8e8, cut0gfefee8e8fefee8e8, cut1gfefee8e8fefee8e8] [node17gfefee8e8fefee8e8, node24gfefee8e8fefee8e8, node19gfefee8e8fefee8e8, node39gfefee8e8fefee8e8, node30gfefee8e8fefee8e8, node36gfefee8e8fefee8e8, node32gfefee8e8fefee8e8, node40gfefee8e8fefee8e8]
    0x400040000051400040010045011440010114400004140414400040004000800700430043400301060106800601060106400300430043400100430043011404120412800504120412011400430043400000430043041401060106800401060106041400430043800300830083400201050105800201050105400200830083400100830083011404110411800104110411011400830083400000830083041401050105800001050105041400830083004301050003010600830003004300830043010601050105 (by decide +kernel)⟩

def node42gfefee8e8fefee8e8 : {w : List Sig // Impossible true goalfefee8e8fefee8e8 6 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 4 zero)], node_ok [cut0gfefee8e8fefee8e8, cut1gfefee8e8fefee8e8, cut2gfefee8e8fefee8e8, cut3gfefee8e8fefee8e8] [node12gfefee8e8fefee8e8, node21gfefee8e8fefee8e8, node26gfefee8e8fefee8e8, node34gfefee8e8fefee8e8, node38gfefee8e8fefee8e8, node41gfefee8e8fefee8e8]
    0x400301140045004540020051041400518005011404140114400200510045004540030092004300434001005104120051800400920412009240010051004300434002008600430043400100450106004580030086010600864001004500430043400300510083008340000092041100118002005104110051400000920083008340020045008300834000008601050005800100450105004540000086008300834001004301050003400001060083000380000043008300434000010601050105 (by decide +kernel)⟩

theorem lowerfefee8e8fefee8e8 : Lower true rootsfefee8e8fefee8e8 goalfefee8e8fefee8e8 7 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 0 zero), 2, 3), ((inputs6.getD 1 zero), 1, 3), ((inputs6.getD 2 zero), 1, 5), ((inputs6.getD 4 zero), 1, 17)]
  have ok : checkEssential goalfefee8e8fefee8e8 rootsfefee8e8fefee8e8 tests = true := by decide +kernel
  have cov : tests.map Prod.fst = rootsfefee8e8fefee8e8 := rfl
  apply lower_impossible (L := 6) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node42gfefee8e8fefee8e8.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha

theorem fiber0gfe80e800fe80e800 : Slice true (inputs6.take 5) minorTarget 0xff00ff00ff00ff00 7 :=
  slice_correct (ms := [(neg (inputs6.getD 3 zero), zero, 8)]) (base := rootsfefee8e8fefee8e8) (G := goalfefee8e8fefee8e8)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowerfefee8e8fefee8e8

def goalffa0fa00ffa0fa00 : Sig := 0xffa0fa00ffa0fa00
def rootsffa0fa00ffa0fa00 : List Sig := [(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)]

def node0gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xa0a0a0a0a0a0a0a0, 0xfafafafafafafafa, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49015504490049020902180155020900090009004904180055005501550218004d004901490049020d (by decide +kernel)⟩

def node1gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0xa0a0a0a0a0a0a0a0, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node0gffa0fa00ffa0fa00]
    0x49015504490049020c02180155020c000c0049010c00490209021801550209000900090049010c0209020c80000155021801550218014d0049014d004904550515 (by decide +kernel)⟩

def node2gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), 0xfafafafafafafafa, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node0gffa0fa00ffa0fa00]
    0x49015504490049015502180155021800490418004904180055005501550218010c004901490049020c01150115015502180049010c0049010c0209045505158000 (by decide +kernel)⟩

def node3gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffff0a0affff0a0a], node_ok [] []
    0x10c00490049010c020c00550055020c000c0049010c00490209020901550218004904090049010c020d020c0055020c (by decide +kernel)⟩

def node4gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), 0xf5f50000f5f50000, (inputs6.getD 3 zero)], node_ok [] []
    0x1550049050c0049000c004901490049020c00550155020c000900090049010c02090115015502090209020c05150209 (by decide +kernel)⟩

def node5gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0xa0a0a0a0a0a0a0a, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node3gffa0fa00ffa0fa00, node4gffa0fa00ffa0fa00]
    0x49015504490049020c02180155020c000c0049010c004901150115015502180049010c0049010c020d0515020c80010155800001550049010c0049010c04550209 (by decide +kernel)⟩

def node6gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffff5050ffff5050], node_ok [] []
    0x49010c04490049020c020c01550218010c0049014900490209011501150209000900090049010c0209020d01150209 (by decide +kernel)⟩

def node7gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xafaf0000afaf0000, (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc00490149004901550049044900490055020c0155020c000900090049010c0209020c045502090209011501550209 (by decide +kernel)⟩

def node8gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0x5050505050505050, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node6gffa0fa00ffa0fa00, node7gffa0fa00ffa0fa00]
    0x490155044900490055005501550218010c0049014900490209021801550209000900090049010c020d045502098001015580000155010c0049010c0049020c0515 (by decide +kernel)⟩

def node9gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xfaf0faf0faf0faf0, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x1490155050c0149020c00550155020c00490049014904550115011501550218010901090149010c020902090455020c (by decide +kernel)⟩

def node10gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0x50f050f050f050f0, (inputs6.getD 0 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x490155044900490209011501550209000900090049010c020c00550155020c000c004901490049020c020904550209 (by decide +kernel)⟩

def node11gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffffaa00ffffaa00], node_ok [] []
    0x4900490449010c020c00550155020c000c0449010c04490209020901550218040904090449010c0415020c0455020c (by decide +kernel)⟩

def node12gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0x55ff000055ff0000, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc004901490049000900090049010c0209020c0455020901550049044900490055020c0155020c0115020901550209 (by decide +kernel)⟩

def node13gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0xaa00aa00aa00aa00, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node9gffa0fa00ffa0fa00, node10gffa0fa00ffa0fa00, node11gffa0fa00ffa0fa00, node12gffa0fa00ffa0fa00]
    0x10c0155050c010c020c00550155020c000c000c010c045501150115015502180515010c014c0415020c0455020c800301558002015500498001020c8000020c0209 (by decide +kernel)⟩

def node14gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xf0a0f0a0f0a0f0a0, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49015504490049020c00550155020c000c0049014900490209021801550209000900090049014c0209020c04550209 (by decide +kernel)⟩

def node15gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xf0a0f0a0f0a0f0a, (inputs6.getD 0 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x490155044900490209001501550209004902090049000c020c01550055020c004901490049000c020904150209020c (by decide +kernel)⟩

def node16gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffaa0000ffaa0000], node_ok [] []
    0x49015504490049020c00550155020c000c0049014900490209011501550209000900090049010c0209020c04550209 (by decide +kernel)⟩

def node17gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xffaa0000ffaa, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x4d004901490049004902090049014c0209020c011502090049044900490155020c0155020c00550209011502090115 (by decide +kernel)⟩

def node18gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffaaffaaffaaffaa, (inputs6.getD 4 zero)], node_ok [] [node14gffa0fa00ffa0fa00, node15gffa0fa00ffa0fa00, node16gffa0fa00ffa0fa00, node17gffa0fa00ffa0fa00]
    0x1558003015580020049015504490049010c020c00550155020c8001020c020c8000004d0049014900490209021801550209051500490209014c0209020c04550209 (by decide +kernel)⟩

def node19gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0xaa00aa00aa00aa, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x10c0155050c010c020c00550155020c000c000c010c0455020902180155020900090209010c0209020c04550209015502180155021800490455020c0455020c0515 (by decide +kernel)⟩

def node20gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0x5500550055005500, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49015504490049020c00550155020c004d00490149004901150115015502180009004905150415020c0455020c0218015502180155010c020c0455020c04550209 (by decide +kernel)⟩

def node21gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xaaaa0000aaaa0000, (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffffaaaaffffaaaa], node_ok [] []
    0x900090049010c020c020904550209000c004901490049011501550049044900490055020c0155020c (by decide +kernel)⟩

def node22gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0xaaaa0000aaaa0000, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node21gffa0fa00ffa0fa00]
    0x490018050c0049020c04550455020c000c004901490049020902188000000900090049010c0209020c04550209015504590049045900490455020c0455020c0515 (by decide +kernel)⟩

def node23gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero), 0xffffaaaaffffaaaa], node_ok [] [node21gffa0fa00ffa0fa00]
    0x218010c00490049010c0049015504490049020c04550455020c020c00550155020c000c00490149004902090155051580000049010c0049010c0415020c0455020c (by decide +kernel)⟩

def node24gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xf0f0fafaf0f0fafa, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x490055050c0049020c04550055020c0049000c004904550055011500550218004901090049004c020902090455020c (by decide +kernel)⟩

def node25gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xf0f05050f0f05050, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49001804490049020c00550455020c000c0049010c00490209011505150209000900090049010c0209020c04550209 (by decide +kernel)⟩

def node26gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0xaaaa0000aaaa, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node24gffa0fa00ffa0fa00, node25gffa0fa00ffa0fa00]
    0x490018050c0049020c04550455020c000c0049014900490115051502180049010c0049010c0415020c0455020c01550049010c0049010c8001020c8000020c0209 (by decide +kernel)⟩

def node27gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xf5f5f0f0f5f5f0f0, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49015504490049020c00550155020c000c0049014900490209011501550209000900090049010c0209020c04150209 (by decide +kernel)⟩

def node28gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xa0a0f0f0a0a0f0f0, (inputs6.getD 0 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x490155044900490209011501550209000900090049010c020c00550155020c000c004901490049020c020904550209 (by decide +kernel)⟩

def node29gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0x5555000055550000, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node27gffa0fa00ffa0fa00, node28gffa0fa00ffa0fa00]
    0x49015504490049020c00550155020c000c004901490049011501550209000900090049010c0209020c04550209021804180049041800498001020c8000020c0515 (by decide +kernel)⟩

def node30gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 2 zero), 0xfaaafaaafaaafaaa, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49015504490049020901150155020900090009004905150055005501550218004c004901490049020c020904550209 (by decide +kernel)⟩

def node31gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xaaa0aaa0aaa0aaa, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49015504490049020c00550155020c000c0049014900490209011501550209000900090049010c0209020c04550209 (by decide +kernel)⟩

def node32gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xfffff000fffff000], node_ok [] []
    0x49010c04490049020c020c01550218040c0049014900490209011501550209000900090049050c0209041504550209 (by decide +kernel)⟩

def node33gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xfff00000fff0000, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc004901490049000900090049010c0209020c0455020901550049044900490055020c0155020c0115020901550209 (by decide +kernel)⟩

def node34gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xf000f000f000f000, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node30gffa0fa00ffa0fa00, node31gffa0fa00ffa0fa00, node32gffa0fa00ffa0fa00, node33gffa0fa00ffa0fa00]
    0x4901550449004900550055015502180455004901498003015580020155010c020c0209011501550209000900090049051502090415045502090209800180000209 (by decide +kernel)⟩

def node35gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xaaa0aaa0aaa0aaa0, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x10c0155050c010c020c02180155020c000c000c014901490209011501550209000900090209010c0209020c05150209 (by decide +kernel)⟩

def node36gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0x5550555055505550, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x9015504090009020c00150155020c010c0009014900090209015501150209010c00090209000902090415020c0209 (by decide +kernel)⟩

def node37gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xfff00000fff00000], node_ok [] []
    0x490155050c0049020c00550155020c000c0049014900490209011501550209000900090049010c0209020c05150209 (by decide +kernel)⟩

def node38gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xfff00000fff0, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x10c020c01490149010d02090209010c0209020c0055020900490049010c0155020c0055020c00550209015502090115 (by decide +kernel)⟩

def node39gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xfff0fff0fff0fff0, (inputs6.getD 4 zero)], node_ok [] [node35gffa0fa00ffa0fa00, node36gffa0fa00ffa0fa00, node37gffa0fa00ffa0fa00, node38gffa0fa00ffa0fa00]
    0x155800301558002010c0155050c010c0049020c02180155020c0455010c020c014902090115015502098001020902098000010d02090209010c0209020c05150209 (by decide +kernel)⟩

def node40gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0xf000f000f000f0, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49015504490049020c02180155020c000c020c0049020901150155020900090009004905150209020c051502090155021801550218010c04550515020905150209 (by decide +kernel)⟩

def node41gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0xf000f000f000f00, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x10c0155050c010c0055005501550218000c010c04550209011501550209010d02090209010c020904150455020902180155021801550049020c0209051502090515 (by decide +kernel)⟩

def node42gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xf0f00000f0f00000, (inputs6.getD 3 zero), 0xfffff0f0fffff0f0], node_ok [] []
    0x49000c01490049005501550049050c00490209020c05150209000900090049010c0209011501550209 (by decide +kernel)⟩

def node43gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xf0f00000f0f00000, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node42gffa0fa00ffa0fa00]
    0x49001804490049020c02188000000c0049014900490155051c0049051c004904550209051505150209000900090049010c0209020c051502090209051505150209 (by decide +kernel)⟩

def node44gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero), 0xfffff0f0fffff0f0], node_ok [] [node42gffa0fa00ffa0fa00]
    0x2180049010c010c004900490155050c0049020c015504558000010c0049010c004902090515051502090209011501550209000900090049010c0209041504550209 (by decide +kernel)⟩

def node45gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xaaaafafaaaaafafa, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x490115044900490055005501150218004c004901090049020905150115020900090009004905150209020c04550209 (by decide +kernel)⟩

def node46gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xaaaa0a0aaaaa0a0a, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49001804490049020c00550455020c000c0049010c00490209011505150209000900090049010c0209020c04550209 (by decide +kernel)⟩

def node47gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0xf0f00000f0f0, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node45gffa0fa00ffa0fa00, node46gffa0fa00ffa0fa00]
    0x49001804490049005504550218010c0049010c00490209051505150209000900090049010c02090415045502090155010c0049010c0049020c8001020980000209 (by decide +kernel)⟩

def node48gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xafafaaaaafafaaaa, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49015504090049020c00550155020c000c0049014900490209011501550209000900090049010c0209020c04150209 (by decide +kernel)⟩

def node49gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xa0a0aaaaa0a0aaaa, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x490155050c0049020c00550155020c000c0049014900490209011501550209000900090049010c0209020c05150209 (by decide +kernel)⟩

def node50gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0xf0f00000f0f0000, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node48gffa0fa00ffa0fa00, node49gffa0fa00ffa0fa00]
    0x490155050c004900550155020c000c0049014900490209011501550209000900090049010c0209020c051502090218041800490418004904558001020980000209 (by decide +kernel)⟩

def node51gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffaaaaaaffaaaaaa, (inputs6.getD 4 zero)], node_ok [] []
    0x2090115015502090049015504490049000900090049010c020c00550155020c020c020904550209000c004901490049 (by decide +kernel)⟩

def node52gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xaaaaaa00aaaaaa, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49015504490049020c00550155020c000c0049014900490209011501550209000900090049010c0209020c04550209 (by decide +kernel)⟩

def node53gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 3 zero), 0xfff0f0f0fff0f0f0, (inputs6.getD 4 zero)], node_ok [] []
    0x20c00550155020c00490155044900490049000c0149004902090115015502090209020c04550209000900090049010c (by decide +kernel)⟩

def node54gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xf0f0f000f0f0f0, (inputs6.getD 0 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x490155044900490209011501550209000900090049010c020c00550155020c000c004901490049020c020904550209 (by decide +kernel)⟩

def node55gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), 0xff000000ff000000, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node51gffa0fa00ffa0fa00, node52gffa0fa00ffa0fa00, node53gffa0fa00ffa0fa00, node54gffa0fa00ffa0fa00]
    0x490155044902180418020c00550155020c000c004901490049020c80038002020c0209011501550209000900090049010c02098001800002090209020c04550209 (by decide +kernel)⟩

def node56gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xaaaaaa00aaaaaa00, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x10c001804490449020c04550455020c000c000c010c04550209011505150209000900090209010c0209020c04550209 (by decide +kernel)⟩

def node57gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0x5555550055555500, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x9011504490009020c00150115020c000d0009010900090209011505150209010c00090209000902090455020c0209 (by decide +kernel)⟩

def node58gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xf0f0f000f0f0f000, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49001804490049020c00550455020c000c0049020c0049020905150515020900090009004905150209020c04550209 (by decide +kernel)⟩

def node59gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 3 w.toFinset} :=
  ⟨[0xf0f0f000f0f0f00, (inputs6.getD 0 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0xc0055044904490209001500550209000d02090209000c020c00550455020c00490049020c000c020904550209020c (by decide +kernel)⟩

def node60gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero), 0xffffff00ffffff00], node_ok [] [node56gffa0fa00ffa0fa00, node57gffa0fa00ffa0fa00, node58gffa0fa00ffa0fa00, node59gffa0fa00ffa0fa00]
    0x15500490218041804498003020c020c8002020c04550455020c0455020c020c04558001020902098000020905150515020905150209020905150209020c04550209 (by decide +kernel)⟩

def node61gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0xff000000ff00, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x1804180155020c00550155020c0455020c020c0455020901150155020905150209020905150209020c0455020902180049020c0455020c04550209051502090515 (by decide +kernel)⟩

def node62gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 4 w.toFinset} :=
  ⟨[0xff000000ff0000, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x1802180049020c04550455020c000c0049014900490209051505150209000900090049010c0209020c04550209015504180455020c0455020c0515020905150209 (by decide +kernel)⟩

def node63gffa0fa00ffa0fa00 : {w : List Sig // Impossible true goalffa0fa00ffa0fa00 5 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node1gffa0fa00ffa0fa00, node2gffa0fa00ffa0fa00, node5gffa0fa00ffa0fa00, node8gffa0fa00ffa0fa00, node13gffa0fa00ffa0fa00, node18gffa0fa00ffa0fa00, node19gffa0fa00ffa0fa00, node20gffa0fa00ffa0fa00, node22gffa0fa00ffa0fa00, node23gffa0fa00ffa0fa00, node26gffa0fa00ffa0fa00, node29gffa0fa00ffa0fa00, node34gffa0fa00ffa0fa00, node39gffa0fa00ffa0fa00, node40gffa0fa00ffa0fa00, node41gffa0fa00ffa0fa00, node43gffa0fa00ffa0fa00, node44gffa0fa00ffa0fa00, node47gffa0fa00ffa0fa00, node50gffa0fa00ffa0fa00, node55gffa0fa00ffa0fa00, node60gffa0fa00ffa0fa00, node61gffa0fa00ffa0fa00, node62gffa0fa00ffa0fa00]
    0x801702180049004980160155041801558015021804180449801401550049004980130155020c020c8012021804550055801101550455015580100218020c020c800f010c0455000c800e0049020c0049800d010c020c0149800c004904550049800b015502090209800a0218051501158009015505150155800802180209020980070049051500098006010c0209000980050049020900498004010c0515010c80030455020902098002020c0515020c80010455051504558000020c02090209 (by decide +kernel)⟩

theorem lowerffa0fa00ffa0fa00 : Lower true rootsffa0fa00ffa0fa00 goalffa0fa00ffa0fa00 6 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 0 zero), 8, 9), ((inputs6.getD 2 zero), 8, 12), ((inputs6.getD 3 zero), 1, 9), ((inputs6.getD 4 zero), 5, 21)]
  have ok : checkEssential goalffa0fa00ffa0fa00 rootsffa0fa00ffa0fa00 tests = true := by decide +kernel
  have cov : tests.map Prod.fst = rootsffa0fa00ffa0fa00 := rfl
  apply lower_impossible (L := 5) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node63gffa0fa00ffa0fa00.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha

theorem fiber1gfe80e800fe80e800 : Slice true (inputs6.take 5) minorTarget 0xcccccccccccccccc 6 :=
  slice_correct (ms := [(neg (inputs6.getD 1 zero), zero, 2)]) (base := rootsffa0fa00ffa0fa00) (G := goalffa0fa00ffa0fa00)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowerffa0fa00ffa0fa00

def goalffc0fc00ffc0fc00 : Sig := 0xffc0fc00ffc0fc00
def rootsffc0fc00ffc0fc00 : List Sig := [(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)]

def node0gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xc0c0c0c0c0c0c0c0, 0xfcfcfcfcfcfcfcfc, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196048a008a020a02180196020a000a000a008a04180096009601960218008e008a018a008a020e (by decide +kernel)⟩

def node1gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0xc0c0c0c0c0c0c0c0, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node0gffc0fc00ffc0fc00]
    0x8a0196048a008a020c02180196020c000c008a010c008a020a02180196020a000a000a008a010c020a020c80000196021801960218018e008a018e008a04960516 (by decide +kernel)⟩

def node2gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xfcfcfcfcfcfcfcfc, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node0gffc0fc00ffc0fc00]
    0x8a0196048a008a0196021801960218008a0418008a04180096009601960218010c008a018a008a020c0116011601960218008a010c008a010c020a049605168000 (by decide +kernel)⟩

def node3gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffff0c0cffff0c0c], node_ok [] []
    0x10c008a008a010c020c00960096020c000c008a010c008a020a020a01960218008a040a008a010c020e020c0096020c (by decide +kernel)⟩

def node4gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xf3f30000f3f30000, (inputs6.getD 3 zero)], node_ok [] []
    0x196008a050c008a000c008a018a008a020c00960196020c000a000a008a010c020a01160196020a020a020c0516020a (by decide +kernel)⟩

def node5gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0xc0c0c0c0c0c0c0c, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node3gffc0fc00ffc0fc00, node4gffc0fc00ffc0fc00]
    0x8a0196048a008a020c02180196020c000c008a010c008a0116011601960218008a010c008a010c020e0516020c8001019680000196008a010c008a010c0496020a (by decide +kernel)⟩

def node6gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffff3030ffff3030], node_ok [] []
    0x8a010c048a008a020c020c01960218010c008a018a008a020a01160116020a000a000a008a010c020a020e0116020a (by decide +kernel)⟩

def node7gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xcfcf0000cfcf0000, (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc008a018a008a0196008a048a008a0096020c0196020c000a000a008a010c020a020c0496020a020a01160196020a (by decide +kernel)⟩

def node8gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0x3030303030303030, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node6gffc0fc00ffc0fc00, node7gffc0fc00ffc0fc00]
    0x8a0196048a008a0096009601960218010c008a018a008a020a02180196020a000a000a008a010c020e0496020a8001019680000196010c008a010c008a020c0516 (by decide +kernel)⟩

def node9gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xfcf0fcf0fcf0fcf0, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x18a0196050c018a020c00960196020c008a008a018a04960116011601960218010a010a018a010c020a020a0496020c (by decide +kernel)⟩

def node10gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0x30f030f030f030f0, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196048a008a020a01160196020a000a000a008a010c020c00960196020c000c008a018a008a020c020a0496020a (by decide +kernel)⟩

def node11gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffffcc00ffffcc00], node_ok [] []
    0x8a008a048a010c020c00960196020c000c048a010c048a020a020a01960218040a040a048a010c0416020c0496020c (by decide +kernel)⟩

def node12gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0x33ff000033ff0000, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc008a018a008a000a000a008a010c020a020c0496020a0196008a048a008a0096020c0196020c0116020a0196020a (by decide +kernel)⟩

def node13gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0xcc00cc00cc00cc00, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node9gffc0fc00ffc0fc00, node10gffc0fc00ffc0fc00, node11gffc0fc00ffc0fc00, node12gffc0fc00ffc0fc00]
    0x10c0196050c010c020c00960196020c000c000c010c049601160116019602180516010c018c0416020c0496020c8003019680020196008a8001020c8000020c020a (by decide +kernel)⟩

def node14gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xf0c0f0c0f0c0f0c0, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196048a008a020c00960196020c000c008a018a008a020a02180196020a000a000a008a018c020a020c0496020a (by decide +kernel)⟩

def node15gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xf0c0f0c0f0c0f0c, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196048a008a020a00160196020a008a020a008a000c020c01960096020c008a018a008a000c020a0416020a020c (by decide +kernel)⟩

def node16gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffcc0000ffcc0000], node_ok [] []
    0x8a0196048a008a020c00960196020c000c008a018a008a020a01160196020a000a000a008a010c020a020c0496020a (by decide +kernel)⟩

def node17gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xffcc0000ffcc, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x8e008a018a008a008a020a008a018c020a020c0116020a008a048a008a0196020c0196020c0096020a0116020a0116 (by decide +kernel)⟩

def node18gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffccffccffccffcc, (inputs6.getD 4 zero)], node_ok [] [node14gffc0fc00ffc0fc00, node15gffc0fc00ffc0fc00, node16gffc0fc00ffc0fc00, node17gffc0fc00ffc0fc00]
    0x196800301968002008a0196048a008a010c020c00960196020c8001020c020c8000008e008a018a008a020a02180196020a0516008a020a018c020a020c0496020a (by decide +kernel)⟩

def node19gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0xcc00cc00cc00cc, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x10c0196050c010c020c00960196020c000c000c010c0496020a02180196020a000a020a010c020a020c0496020a0196021801960218008a0496020c0496020c0516 (by decide +kernel)⟩

def node20gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0x3300330033003300, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196048a008a020c00960196020c008e008a018a008a0116011601960218000a008a05160416020c0496020c0218019602180196010c020c0496020c0496020a (by decide +kernel)⟩

def node21gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xcccc0000cccc0000, (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffffccccffffcccc], node_ok [] []
    0xa000a008a010c020c020a0496020a000c008a018a008a01160196008a048a008a0096020c0196020c (by decide +kernel)⟩

def node22gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0xcccc0000cccc0000, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node21gffc0fc00ffc0fc00]
    0x8a0018050c008a020c04960496020c000c008a018a008a020a02188000000a000a008a010c020a020c0496020a0196049a008a049a008a0496020c0496020c0516 (by decide +kernel)⟩

def node23gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero), 0xffffccccffffcccc], node_ok [] [node21gffc0fc00ffc0fc00]
    0x218010c008a008a010c008a0196048a008a020c04960496020c020c00960196020c000c008a018a008a020a019605168000008a010c008a010c0416020c0496020c (by decide +kernel)⟩

def node24gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xf0f0fcfcf0f0fcfc, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0096050c008a020c04960096020c008a000c008a04960096011600960218008a010a008a008c020a020a0496020c (by decide +kernel)⟩

def node25gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xf0f03030f0f03030, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0018048a008a020c00960496020c000c008a010c008a020a01160516020a000a000a008a010c020a020c0496020a (by decide +kernel)⟩

def node26gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0xcccc0000cccc, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node24gffc0fc00ffc0fc00, node25gffc0fc00ffc0fc00]
    0x8a0018050c008a020c04960496020c000c008a018a008a011605160218008a010c008a010c0416020c0496020c0196008a010c008a010c8001020c8000020c020a (by decide +kernel)⟩

def node27gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xf3f3f0f0f3f3f0f0, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196048a008a020c00960196020c000c008a018a008a020a01160196020a000a000a008a010c020a020c0416020a (by decide +kernel)⟩

def node28gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xc0c0f0f0c0c0f0f0, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196048a008a020a01160196020a000a000a008a010c020c00960196020c000c008a018a008a020c020a0496020a (by decide +kernel)⟩

def node29gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0x3333000033330000, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node27gffc0fc00ffc0fc00, node28gffc0fc00ffc0fc00]
    0x8a0196048a008a020c00960196020c000c008a018a008a01160196020a000a000a008a010c020a020c0496020a02180418008a0418008a8001020c8000020c0516 (by decide +kernel)⟩

def node30gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 2 zero), 0xfcccfcccfcccfccc, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196048a008a020a01160196020a000a000a008a05160096009601960218008c008a018a008a020c020a0496020a (by decide +kernel)⟩

def node31gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xccc0ccc0ccc0ccc, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196048a008a020c00960196020c000c008a018a008a020a01160196020a000a000a008a010c020a020c0496020a (by decide +kernel)⟩

def node32gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xfffff000fffff000], node_ok [] []
    0x8a010c048a008a020c020c01960218040c008a018a008a020a01160196020a000a000a008a050c020a04160496020a (by decide +kernel)⟩

def node33gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xfff00000fff0000, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc008a018a008a000a000a008a010c020a020c0496020a0196008a048a008a0096020c0196020c0116020a0196020a (by decide +kernel)⟩

def node34gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xf000f000f000f000, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node30gffc0fc00ffc0fc00, node31gffc0fc00ffc0fc00, node32gffc0fc00ffc0fc00, node33gffc0fc00ffc0fc00]
    0x8a0196048a008a00960096019602180496008a018a8003019680020196010c020c020a01160196020a000a000a008a0516020a04160496020a020a80018000020a (by decide +kernel)⟩

def node35gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xccc0ccc0ccc0ccc0, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x10c0196050c010c020c02180196020c000c000c018a018a020a01160196020a000a000a020a010c020a020c0516020a (by decide +kernel)⟩

def node36gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0x3330333033303330, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0xa0196040a000a020c00160196020c010c000a018a000a020a01960116020a010c000a020a000a020a0416020c020a (by decide +kernel)⟩

def node37gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xfff00000fff00000], node_ok [] []
    0x8a0196050c008a020c00960196020c000c008a018a008a020a01160196020a000a000a008a010c020a020c0516020a (by decide +kernel)⟩

def node38gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xfff00000fff0, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x10c020c018a018a010e020a020a010c020a020c0096020a008a008a010c0196020c0096020c0096020a0196020a0116 (by decide +kernel)⟩

def node39gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xfff0fff0fff0fff0, (inputs6.getD 4 zero)], node_ok [] [node35gffc0fc00ffc0fc00, node36gffc0fc00ffc0fc00, node37gffc0fc00ffc0fc00, node38gffc0fc00ffc0fc00]
    0x196800301968002010c0196050c010c008a020c02180196020c0496010c020c018a020a01160196020a8001020a020a8000010e020a020a010c020a020c0516020a (by decide +kernel)⟩

def node40gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0xf000f000f000f0, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196048a008a020c02180196020c000c020c008a020a01160196020a000a000a008a0516020a020c0516020a0196021801960218010c04960516020a0516020a (by decide +kernel)⟩

def node41gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0xf000f000f000f00, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x10c0196050c010c0096009601960218000c010c0496020a01160196020a010e020a020a010c020a04160496020a0218019602180196008a020c020a0516020a0516 (by decide +kernel)⟩

def node42gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xf0f00000f0f00000, (inputs6.getD 3 zero), 0xfffff0f0fffff0f0], node_ok [] []
    0x8a000c018a008a00960196008a050c008a020a020c0516020a000a000a008a010c020a01160196020a (by decide +kernel)⟩

def node43gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xf0f00000f0f00000, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node42gffc0fc00ffc0fc00]
    0x8a0018048a008a020c02188000000c008a018a008a0196051c008a051c008a0496020a05160516020a000a000a008a010c020a020c0516020a020a05160516020a (by decide +kernel)⟩

def node44gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero), 0xfffff0f0fffff0f0], node_ok [] [node42gffc0fc00ffc0fc00]
    0x218008a010c010c008a008a0196050c008a020c019604968000010c008a010c008a020a05160516020a020a01160196020a000a000a008a010c020a04160496020a (by decide +kernel)⟩

def node45gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xccccfcfcccccfcfc, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0116048a008a0096009601160218008c008a010a008a020a05160116020a000a000a008a0516020a020c0496020a (by decide +kernel)⟩

def node46gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xcccc0c0ccccc0c0c, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0018048a008a020c00960496020c000c008a010c008a020a01160516020a000a000a008a010c020a020c0496020a (by decide +kernel)⟩

def node47gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0xf0f00000f0f0, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node45gffc0fc00ffc0fc00, node46gffc0fc00ffc0fc00]
    0x8a0018048a008a009604960218010c008a010c008a020a05160516020a000a000a008a010c020a04160496020a0196010c008a010c008a020c8001020a8000020a (by decide +kernel)⟩

def node48gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xcfcfcccccfcfcccc, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196040a008a020c00960196020c000c008a018a008a020a01160196020a000a000a008a010c020a020c0416020a (by decide +kernel)⟩

def node49gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xc0c0ccccc0c0cccc, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196050c008a020c00960196020c000c008a018a008a020a01160196020a000a000a008a010c020a020c0516020a (by decide +kernel)⟩

def node50gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0xf0f00000f0f0000, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node48gffc0fc00ffc0fc00, node49gffc0fc00ffc0fc00]
    0x8a0196050c008a00960196020c000c008a018a008a020a01160196020a000a000a008a010c020a020c0516020a02180418008a0418008a04968001020a8000020a (by decide +kernel)⟩

def node51gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffccccccffcccccc, (inputs6.getD 4 zero)], node_ok [] []
    0x20a01160196020a008a0196048a008a000a000a008a010c020c00960196020c020c020a0496020a000c008a018a008a (by decide +kernel)⟩

def node52gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xcccccc00cccccc, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196048a008a020c00960196020c000c008a018a008a020a01160196020a000a000a008a010c020a020c0496020a (by decide +kernel)⟩

def node53gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 3 zero), 0xfff0f0f0fff0f0f0, (inputs6.getD 4 zero)], node_ok [] []
    0x20c00960196020c008a0196048a008a008a000c018a008a020a01160196020a020a020c0496020a000a000a008a010c (by decide +kernel)⟩

def node54gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xf0f0f000f0f0f0, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0196048a008a020a01160196020a000a000a008a010c020c00960196020c000c008a018a008a020c020a0496020a (by decide +kernel)⟩

def node55gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xff000000ff000000, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node51gffc0fc00ffc0fc00, node52gffc0fc00ffc0fc00, node53gffc0fc00ffc0fc00, node54gffc0fc00ffc0fc00]
    0x8a0196048a02180418020c00960196020c000c008a018a008a020c80038002020c020a01160196020a000a000a008a010c020a80018000020a020a020c0496020a (by decide +kernel)⟩

def node56gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xcccccc00cccccc00, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x10c0018048a048a020c04960496020c000c000c010c0496020a01160516020a000a000a020a010c020a020c0496020a (by decide +kernel)⟩

def node57gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0x3333330033333300, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0xa0116048a000a020c00160116020c000e000a010a000a020a01160516020a010c000a020a000a020a0496020c020a (by decide +kernel)⟩

def node58gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xf0f0f000f0f0f000, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a0018048a008a020c00960496020c000c008a020c008a020a05160516020a000a000a008a0516020a020c0496020a (by decide +kernel)⟩

def node59gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 3 w.toFinset} :=
  ⟨[0xf0f0f000f0f0f00, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0xc0096048a048a020a00160096020a000e020a020a000c020c00960496020c008a008a020c000c020a0496020a020c (by decide +kernel)⟩

def node60gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero), 0xffffff00ffffff00], node_ok [] [node56gffc0fc00ffc0fc00, node57gffc0fc00ffc0fc00, node58gffc0fc00ffc0fc00, node59gffc0fc00ffc0fc00]
    0x196008a02180418048a8003020c020c8002020c04960496020c0496020c020c04968001020a020a8000020a05160516020a0516020a020a0516020a020c0496020a (by decide +kernel)⟩

def node61gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0xff000000ff00, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x1804180196020c00960196020c0496020c020c0496020a01160196020a0516020a020a0516020a020c0496020a0218008a020c0496020c0496020a0516020a0516 (by decide +kernel)⟩

def node62gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 4 w.toFinset} :=
  ⟨[0xff000000ff0000, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x180218008a020c04960496020c000c008a018a008a020a05160516020a000a000a008a010c020a020c0496020a019604180496020c0496020c0516020a0516020a (by decide +kernel)⟩

def node63gffc0fc00ffc0fc00 : {w : List Sig // Impossible true goalffc0fc00ffc0fc00 5 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node1gffc0fc00ffc0fc00, node2gffc0fc00ffc0fc00, node5gffc0fc00ffc0fc00, node8gffc0fc00ffc0fc00, node13gffc0fc00ffc0fc00, node18gffc0fc00ffc0fc00, node19gffc0fc00ffc0fc00, node20gffc0fc00ffc0fc00, node22gffc0fc00ffc0fc00, node23gffc0fc00ffc0fc00, node26gffc0fc00ffc0fc00, node29gffc0fc00ffc0fc00, node34gffc0fc00ffc0fc00, node39gffc0fc00ffc0fc00, node40gffc0fc00ffc0fc00, node41gffc0fc00ffc0fc00, node43gffc0fc00ffc0fc00, node44gffc0fc00ffc0fc00, node47gffc0fc00ffc0fc00, node50gffc0fc00ffc0fc00, node55gffc0fc00ffc0fc00, node60gffc0fc00ffc0fc00, node61gffc0fc00ffc0fc00, node62gffc0fc00ffc0fc00]
    0x80170218008a008a8016019604180196801502180418048a80140196008a008a80130196020c020c8012021804960096801101960496019680100218020c020c800f010c0496000c800e008a020c008a800d010c020c018a800c008a0496008a800b0196020a020a800a021805160116800901960516019680080218020a020a8007008a0516000a8006010c020a000a8005008a020a008a8004010c0516010c80030496020a020a8002020c0516020c80010496051604968000020c020a020a (by decide +kernel)⟩

theorem lowerffc0fc00ffc0fc00 : Lower true rootsffc0fc00ffc0fc00 goalffc0fc00ffc0fc00 6 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 1 zero), 8, 10), ((inputs6.getD 2 zero), 8, 12), ((inputs6.getD 3 zero), 2, 10), ((inputs6.getD 4 zero), 6, 22)]
  have ok : checkEssential goalffc0fc00ffc0fc00 rootsffc0fc00ffc0fc00 tests = true := by decide +kernel
  have cov : tests.map Prod.fst = rootsffc0fc00ffc0fc00 := rfl
  apply lower_impossible (L := 5) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node63gffc0fc00ffc0fc00.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha

theorem fiber2gfe80e800fe80e800 : Slice true (inputs6.take 5) minorTarget 0xaaaaaaaaaaaaaaaa 6 :=
  slice_correct (ms := [(neg (inputs6.getD 0 zero), zero, 1)]) (base := rootsffc0fc00ffc0fc00) (G := goalffc0fc00ffc0fc00)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowerffc0fc00ffc0fc00

def goalfc00c000fc00c000 : Sig := 0xfc00c000fc00c000
def rootsfc00c000fc00c000 : List Sig := [(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)]

theorem fiber0gfc00c000fc00c000 : Slice true rootsfc00c000fc00c000 goalfc00c000fc00c000 0xff00ff00ff00ff00 4 :=
  slice_correct (ms := [(neg (inputs6.getD 3 zero), zero, 8)]) (base := rootsfcfcc0c0fcfcc0c0) (G := goalfcfcc0c0fcfcc0c0)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowerfcfcc0c0fcfcc0c0

def cut0gfc00c000fc00c000 : {c : Cut // CutGood goalfc00c000fc00c000 c} :=
  ⟨(0xff00ff00ff00ff00, 4, rootsfc00c000fc00c000), cut_good fiber0gfc00c000fc00c000 [] (by decide +kernel) (by decide)⟩

def node0gfc00c000fc00c000 : {w : List Sig // Impossible true goalfc00c000fc00c000 4 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [cut0gfc00c000fc00c000] []
    0x29a018e018e4000049a009a029a049a058e4000018e018e031c028e028e029a061c029a031c061c031c029a028e028e018e4000008e049a028e008e018e028e018e049a4000049a029a030e030e031c061a021a029a061a029a031c030e030e018e4000010e051c030e010e018e030e018e051c4000051c028e061a020e061c030e020e028e030e028e061c061a061a (by decide +kernel)⟩

theorem lowerfc00c000fc00c000 : Lower true rootsfc00c000fc00c000 goalfc00c000fc00c000 5 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 1 zero), 12, 14), ((inputs6.getD 2 zero), 10, 14), ((inputs6.getD 3 zero), 6, 14), ((inputs6.getD 4 zero), 10, 26)]
  have ok : checkEssential goalfc00c000fc00c000 rootsfc00c000fc00c000 tests = true := by decide +kernel
  have cov : tests.map Prod.fst = rootsfc00c000fc00c000 := rfl
  apply lower_impossible (L := 4) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node0gfc00c000fc00c000.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha

theorem fiber3gfe80e800fe80e800 : Slice true (inputs6.take 5) minorTarget 0x5555555555555555 5 :=
  slice_correct (ms := [(zero, (inputs6.getD 0 zero), 1)]) (base := rootsfc00c000fc00c000) (G := goalfc00c000fc00c000)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowerfc00c000fc00c000

def goalff88ee00ff88ee00 : Sig := 0xff88ee00ff88ee00
def rootsff88ee00ff88ee00 : List Sig := [(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)]

def node0gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0x8888888888888888, 0xeeeeeeeeeeeeeeee, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d3044900490209021800d3020900090009004904180053005300d30218004b004900c90049020b (by decide +kernel)⟩

def node1gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0x8888888888888888, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node0gff88ee00ff88ee00]
    0x4900d304490049020a021800d3020a000a0049008a00490209021800d30209000900090049008a0209020a800000d3021800d3021800cb004900cb004904530493 (by decide +kernel)⟩

def node2gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xeeeeeeeeeeeeeeee, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node0gff88ee00ff88ee00]
    0x4900d30449004900d3021800d3021800490418004904180053005300d30218008a004900c90049020a0093009300d302180049008a0049008a0209045304938000 (by decide +kernel)⟩

def node3gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), 0xffff2222ffff2222], node_ok [] []
    0x8a00490049008a020a00530053020a000a0049008a00490209020900d30218004904090049008a020b020a0053020a (by decide +kernel)⟩

def node4gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xdddd0000dddd0000, (inputs6.getD 3 zero)], node_ok [] []
    0xd30049048a0049000a004900c90049020a005300d3020a000900090049008a0209009300d302090209020a04930209 (by decide +kernel)⟩

def node5gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0x2222222222222222, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node3gff88ee00ff88ee00, node4gff88ee00ff88ee00]
    0x4900d304490049020a021800d3020a000a0049008a00490093009300d302180049008a0049008a020b0493020a800100d3800000d30049008a0049008a04530209 (by decide +kernel)⟩

def node6gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), 0xffff4444ffff4444], node_ok [] []
    0x49008a04490049020a020a00d30218008a004900c900490209009300930209000900090049008a0209020b00930209 (by decide +kernel)⟩

def node7gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xbbbb0000bbbb0000, (inputs6.getD 1 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xa004900c9004900d30049044900490053020a00d3020a000900090049008a0209020a045302090209009300d30209 (by decide +kernel)⟩

def node8gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0x4444444444444444, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node6gff88ee00ff88ee00, node7gff88ee00ff88ee00]
    0x4900d3044900490053005300d30218008a004900c900490209021800d30209000900090049008a020b04530209800100d3800000d3008a0049008a0049020a0493 (by decide +kernel)⟩

def node9gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xeecceecceecceecc, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0xc900d3048a00c9020a005300d3020a0049004900c904530093009300d302180089008900c9008a020902090453020a (by decide +kernel)⟩

def node10gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0x44cc44cc44cc44cc, (inputs6.getD 0 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d3044900490209009300d30209000900090049008a020a005300d3020a000a004900c90049020a020904530209 (by decide +kernel)⟩

def node11gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), 0xffffaa00ffffaa00], node_ok [] []
    0x4900490449008a020a005300d3020a000a0449008a04490209020900d30218040904090449008a0413020a0453020a (by decide +kernel)⟩

def node12gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0x55ff000055ff0000, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xa004900c90049000900090049008a0209020a0453020900d30049044900490053020a00d3020a0093020900d30209 (by decide +kernel)⟩

def node13gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0xaa00aa00aa00aa00, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node9gff88ee00ff88ee00, node10gff88ee00ff88ee00, node11gff88ee00ff88ee00, node12gff88ee00ff88ee00]
    0x8a00d3048a008a020a005300d3020a000a000a008a04530093009300d302180493008a00ca0413020a0453020a800300d3800200d300498001020a8000020a0209 (by decide +kernel)⟩

def node14gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xcc88cc88cc88cc88, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d304490049020a005300d3020a000a004900c900490209021800d3020900090009004900ca0209020a04530209 (by decide +kernel)⟩

def node15gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0x3322332233223322, (inputs6.getD 0 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d3044900490209001300d30209004902090049000a020a00d30053020a004900c90049000a020904130209020a (by decide +kernel)⟩

def node16gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), 0xffaa0000ffaa0000], node_ok [] []
    0x4900d304490049020a005300d3020a000a004900c900490209009300d30209000900090049008a0209020a04530209 (by decide +kernel)⟩

def node17gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0xffaa0000ffaa, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x4b004900c9004900490209004900ca0209020a0093020900490449004900d3020a00d3020a00530209009302090093 (by decide +kernel)⟩

def node18gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), 0xffaaffaaffaaffaa, (inputs6.getD 4 zero)], node_ok [] [node14gff88ee00ff88ee00, node15gff88ee00ff88ee00, node16gff88ee00ff88ee00, node17gff88ee00ff88ee00]
    0xd3800300d38002004900d304490049008a020a005300d3020a8001020a020a8000004b004900c900490209021800d3020904930049020900ca0209020a04530209 (by decide +kernel)⟩

def node19gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0xaa00aa00aa00aa, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a00d3048a008a020a005300d3020a000a000a008a04530209021800d3020900090209008a0209020a0453020900d3021800d3021800490453020a0453020a0493 (by decide +kernel)⟩

def node20gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0x5500550055005500, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d304490049020a005300d3020a004b004900c900490093009300d302180009004904930413020a0453020a021800d3021800d3008a020a0453020a04530209 (by decide +kernel)⟩

def node21gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0xaaaa0000aaaa0000, (inputs6.getD 1 zero), (inputs6.getD 3 zero), 0xffffaaaaffffaaaa], node_ok [] []
    0x900090049008a020a020904530209000a004900c90049009300d30049044900490053020a00d3020a (by decide +kernel)⟩

def node22gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0xaaaa0000aaaa0000, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node21gff88ee00ff88ee00]
    0x490018048a0049020a04530453020a000a004900c90049020902188000000900090049008a0209020a0453020900d304590049045900490453020a0453020a0493 (by decide +kernel)⟩

def node23gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero), 0xffffaaaaffffaaaa], node_ok [] [node21gff88ee00ff88ee00]
    0x218008a00490049008a004900d304490049020a04530453020a020a005300d3020a000a004900c90049020900d3049380000049008a0049008a0413020a0453020a (by decide +kernel)⟩

def node24gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xcccceeeecccceeee, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x490053048a0049020a04530053020a0049000a004904530053009300530218004900890049004a020902090453020a (by decide +kernel)⟩

def node25gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xcccc4444cccc4444, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49001804490049020a00530453020a000a0049008a00490209009304930209000900090049008a0209020a04530209 (by decide +kernel)⟩

def node26gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0xaaaa0000aaaa, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node24gff88ee00ff88ee00, node25gff88ee00ff88ee00]
    0x490018048a0049020a04530453020a000a004900c900490093049302180049008a0049008a0413020a0453020a00d30049008a0049008a8001020a8000020a0209 (by decide +kernel)⟩

def node27gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xddddccccddddcccc, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d304490049020a005300d3020a000a004900c900490209009300d30209000900090049008a0209020a04130209 (by decide +kernel)⟩

def node28gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0x8888cccc8888cccc, (inputs6.getD 0 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d3044900490209009300d30209000900090049008a020a005300d3020a000a004900c90049020a020904530209 (by decide +kernel)⟩

def node29gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0x5555000055550000, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node27gff88ee00ff88ee00, node28gff88ee00ff88ee00]
    0x4900d304490049020a005300d3020a000a004900c90049009300d30209000900090049008a0209020a04530209021804180049041800498001020a8000020a0493 (by decide +kernel)⟩

def node30gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xeeaaeeaaeeaaeeaa, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d3044900490209009300d3020900090009004904930053005300d30218004a004900c90049020a020904530209 (by decide +kernel)⟩

def node31gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0x22aa22aa22aa22aa, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d304490049020a005300d3020a000a004900c900490209009300d30209000900090049008a0209020a04530209 (by decide +kernel)⟩

def node32gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), 0xffffcc00ffffcc00], node_ok [] []
    0x49008a04490049020a020a00d30218040a004900c900490209009300d30209000900090049048a0209041304530209 (by decide +kernel)⟩

def node33gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0x33ff000033ff0000, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xa004900c90049000900090049008a0209020a0453020900d30049044900490053020a00d3020a0093020900d30209 (by decide +kernel)⟩

def node34gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xcc00cc00cc00cc00, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node30gff88ee00ff88ee00, node31gff88ee00ff88ee00, node32gff88ee00ff88ee00, node33gff88ee00ff88ee00]
    0x4900d3044900490053005300d302180453004900c9800300d3800200d3008a020a0209009300d30209000900090049049302090413045302090209800180000209 (by decide +kernel)⟩

def node35gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0xaa88aa88aa88aa88, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a00d3048a008a020a021800d3020a000a000a00c900c90209009300d30209000900090209008a0209020a04930209 (by decide +kernel)⟩

def node36gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0x5544554455445544, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x900d304090009020a001300d3020a008a000900c90009020900d300930209008a00090209000902090413020a0209 (by decide +kernel)⟩

def node37gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), 0xffcc0000ffcc0000], node_ok [] []
    0x4900d3048a0049020a005300d3020a000a004900c900490209009300d30209000900090049008a0209020a04930209 (by decide +kernel)⟩

def node38gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0xffcc0000ffcc, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x8a020a00c900c9008b02090209008a0209020a0053020900490049008a00d3020a0053020a0053020900d302090093 (by decide +kernel)⟩

def node39gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), 0xffccffccffccffcc, (inputs6.getD 4 zero)], node_ok [] [node35gff88ee00ff88ee00, node36gff88ee00ff88ee00, node37gff88ee00ff88ee00, node38gff88ee00ff88ee00]
    0xd3800300d38002008a00d3048a008a0049020a021800d3020a0453008a020a00c90209009300d302098001020902098000008b02090209008a0209020a04930209 (by decide +kernel)⟩

def node40gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0xcc00cc00cc00cc, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d304490049020a021800d3020a000a020a00490209009300d3020900090009004904930209020a0493020900d3021800d30218008a04530493020904930209 (by decide +kernel)⟩

def node41gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0x3300330033003300, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a00d3048a008a0053005300d30218000a008a04530209009300d30209008b02090209008a0209041304530209021800d3021800d30049020a0209049302090493 (by decide +kernel)⟩

def node42gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xcccc0000cccc0000, (inputs6.getD 3 zero), 0xffffccccffffcccc], node_ok [] []
    0x49000a00c90049005300d30049048a00490209020a04930209000900090049008a0209009300d30209 (by decide +kernel)⟩

def node43gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xcccc0000cccc0000, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node42gff88ee00ff88ee00]
    0x49001804490049020a02188000000a004900c9004900d3049a0049049a004904530209049304930209000900090049008a0209020a049302090209049304930209 (by decide +kernel)⟩

def node44gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero), 0xffffccccffffcccc], node_ok [] [node42gff88ee00ff88ee00]
    0x2180049008a008a0049004900d3048a0049020a00d304538000008a0049008a004902090493049302090209009300d30209000900090049008a0209041304530209 (by decide +kernel)⟩

def node45gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0xaaaaeeeeaaaaeeee, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x490093044900490053005300930218004a004900890049020904930093020900090009004904930209020a04530209 (by decide +kernel)⟩

def node46gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0xaaaa2222aaaa2222, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49001804490049020a00530453020a000a0049008a00490209009304930209000900090049008a0209020a04530209 (by decide +kernel)⟩

def node47gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0xcccc0000cccc, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node45gff88ee00ff88ee00, node46gff88ee00ff88ee00]
    0x49001804490049005304530218008a0049008a00490209049304930209000900090049008a020904130453020900d3008a0049008a0049020a8001020980000209 (by decide +kernel)⟩

def node48gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0xbbbbaaaabbbbaaaa, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d304090049020a005300d3020a000a004900c900490209009300d30209000900090049008a0209020a04130209 (by decide +kernel)⟩

def node49gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0x8888aaaa8888aaaa, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d3048a0049020a005300d3020a000a004900c900490209009300d30209000900090049008a0209020a04930209 (by decide +kernel)⟩

def node50gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0x3333000033330000, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node48gff88ee00ff88ee00, node49gff88ee00ff88ee00]
    0x4900d3048a0049005300d3020a000a004900c900490209009300d30209000900090049008a0209020a049302090218041800490418004904538001020980000209 (by decide +kernel)⟩

def node51gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 3 zero), 0xffaaaaaaffaaaaaa, (inputs6.getD 4 zero)], node_ok [] []
    0x209009300d30209004900d304490049000900090049008a020a005300d3020a020a020904530209000a004900c90049 (by decide +kernel)⟩

def node52gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0xaaaaaa00aaaaaa, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d304490049020a005300d3020a000a004900c900490209009300d30209000900090049008a0209020a04530209 (by decide +kernel)⟩

def node53gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 3 zero), 0xffccccccffcccccc, (inputs6.getD 4 zero)], node_ok [] []
    0x20a005300d3020a004900d3044900490049000a00c900490209009300d302090209020a04530209000900090049008a (by decide +kernel)⟩

def node54gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0xcccccc00cccccc, (inputs6.getD 0 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x4900d3044900490209009300d30209000900090049008a020a005300d3020a000a004900c90049020a020904530209 (by decide +kernel)⟩

def node55gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xff000000ff000000, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node51gff88ee00ff88ee00, node52gff88ee00ff88ee00, node53gff88ee00ff88ee00, node54gff88ee00ff88ee00]
    0x4900d3044902180418020a005300d3020a000a004900c90049020a80038002020a0209009300d30209000900090049008a02098001800002090209020a04530209 (by decide +kernel)⟩

def node56gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0xaaaaaa00aaaaaa00, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x8a001804490449020a04530453020a000a000a008a04530209009304930209000900090209008a0209020a04530209 (by decide +kernel)⟩

def node57gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0x5555550055555500, (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x9009304490009020a00130093020a000b0009008900090209009304930209008a00090209000902090453020a0209 (by decide +kernel)⟩

def node58gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xcccccc00cccccc00, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x49001804490049020a00530453020a000a0049020a0049020904930493020900090009004904930209020a04530209 (by decide +kernel)⟩

def node59gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 3 w.toFinset} :=
  ⟨[0x3333330033333300, (inputs6.getD 0 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0xa0053044904490209001300530209000b02090209000a020a00530453020a00490049020a000a020904530209020a (by decide +kernel)⟩

def node60gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero), 0xffffff00ffffff00], node_ok [] [node56gff88ee00ff88ee00, node57gff88ee00ff88ee00, node58gff88ee00ff88ee00, node59gff88ee00ff88ee00]
    0xd300490218041804498003020a020a8002020a04530453020a0453020a020a04538001020902098000020904930493020904930209020904930209020a04530209 (by decide +kernel)⟩

def node61gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0xff000000ff00, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x18041800d3020a005300d3020a0453020a020a04530209009300d3020904930209020904930209020a0453020902180049020a0453020a04530209049302090493 (by decide +kernel)⟩

def node62gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 4 w.toFinset} :=
  ⟨[0xff000000ff0000, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0x1802180049020a04530453020a000a004900c900490209049304930209000900090049008a0209020a0453020900d304180453020a0453020a0493020904930209 (by decide +kernel)⟩

def node63gff88ee00ff88ee00 : {w : List Sig // Impossible true goalff88ee00ff88ee00 5 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] [node1gff88ee00ff88ee00, node2gff88ee00ff88ee00, node5gff88ee00ff88ee00, node8gff88ee00ff88ee00, node13gff88ee00ff88ee00, node18gff88ee00ff88ee00, node19gff88ee00ff88ee00, node20gff88ee00ff88ee00, node22gff88ee00ff88ee00, node23gff88ee00ff88ee00, node26gff88ee00ff88ee00, node29gff88ee00ff88ee00, node34gff88ee00ff88ee00, node39gff88ee00ff88ee00, node40gff88ee00ff88ee00, node41gff88ee00ff88ee00, node43gff88ee00ff88ee00, node44gff88ee00ff88ee00, node47gff88ee00ff88ee00, node50gff88ee00ff88ee00, node55gff88ee00ff88ee00, node60gff88ee00ff88ee00, node61gff88ee00ff88ee00, node62gff88ee00ff88ee00]
    0x8017021800490049801600d3041800d38015021804180449801400d300490049801300d3020a020a8012021804530053801100d3045300d380100218020a020a800f008a0453000a800e0049020a0049800d008a020a00c9800c004904530049800b00d302090209800a021804930093800900d3049300d3800802180209020980070049049300098006008a0209000980050049020900498004008a0493008a80030453020902098002020a0493020a80010453049304538000020a02090209 (by decide +kernel)⟩

theorem lowerff88ee00ff88ee00 : Lower true rootsff88ee00ff88ee00 goalff88ee00ff88ee00 6 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 0 zero), 8, 9), ((inputs6.getD 1 zero), 8, 10), ((inputs6.getD 3 zero), 1, 9), ((inputs6.getD 4 zero), 3, 19)]
  have ok : checkEssential goalff88ee00ff88ee00 rootsff88ee00ff88ee00 tests = true := by decide +kernel
  have cov : tests.map Prod.fst = rootsff88ee00ff88ee00 := rfl
  apply lower_impossible (L := 5) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node63gff88ee00ff88ee00.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha

theorem fiber4gfe80e800fe80e800 : Slice true (inputs6.take 5) minorTarget 0xf0f0f0f0f0f0f0f0 6 :=
  slice_correct (ms := [(neg (inputs6.getD 2 zero), zero, 4)]) (base := rootsff88ee00ff88ee00) (G := goalff88ee00ff88ee00)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowerff88ee00ff88ee00

def goalee008800ee008800 : Sig := 0xee008800ee008800
def rootsee008800ee008800 : List Sig := [(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)]

theorem fiber0gee008800ee008800 : Slice true rootsee008800ee008800 goalee008800ee008800 0xff00ff00ff00ff00 4 :=
  slice_correct (ms := [(neg (inputs6.getD 3 zero), zero, 8)]) (base := rootseeee8888eeee8888) (G := goaleeee8888eeee8888)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowereeee8888eeee8888

def cut0gee008800ee008800 : {c : Cut // CutGood goalee008800ee008800 c} :=
  ⟨(0xff00ff00ff00ff00, 4, rootsee008800ee008800), cut_good fiber0gee008800ee008800 [] (by decide +kernel) (by decide)⟩

def node0gee008800ee008800 : {w : List Sig // Impossible true goalee008800ee008800 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [cut0gee008800ee008800] []
    0x25900cb00cb4000045900590259045904cb400000cb00cb029a024b024b0259061a0259029a061a029a0259024b024b00cb4000004b0459024b004b00cb024b00cb0459400004590259028b028b029a06190219025906190259029a028b028b00cb4000008b049a028b008b00cb028b00cb049a4000049a024b0619020b061a028b020b024b028b024b061a06190619 (by decide +kernel)⟩

theorem loweree008800ee008800 : Lower true rootsee008800ee008800 goalee008800ee008800 5 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 0 zero), 10, 11), ((inputs6.getD 1 zero), 9, 11), ((inputs6.getD 3 zero), 3, 11), ((inputs6.getD 4 zero), 9, 25)]
  have ok : checkEssential goalee008800ee008800 rootsee008800ee008800 tests = true := by decide +kernel
  have cov : tests.map Prod.fst = rootsee008800ee008800 := rfl
  apply lower_impossible (L := 4) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node0gee008800ee008800.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha

theorem fiber5gfe80e800fe80e800 : Slice true (inputs6.take 5) minorTarget 0xf0f0f0f0f0f0f0f 5 :=
  slice_correct (ms := [(zero, (inputs6.getD 2 zero), 4)]) (base := rootsee008800ee008800) (G := goalee008800ee008800)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) loweree008800ee008800

def goalfe80fe80fe80fe80 : Sig := 0xfe80fe80fe80fe80
def rootsfe80fe80fe80fe80 : List Sig := [(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)]

def node0gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0x8888888888888888, 0xeeeeeeeeeeeeeeee, (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c7000900090049010c00c7020c00c702090147004900c901470047004700c7020c0107 (by decide +kernel)⟩

def node1gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0x8888888888888888, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node0gfe80fe80fe80fe80]
    0xc70049014900c7000a0049008a004900c7020c00c7020a000900090049008a00c7020c00c702090209020a800000cb004900cb004900c7020c00c7020c01470187 (by decide +kernel)⟩

def node2gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xeeeeeeeeeeeeeeee, (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node0gfe80fe80fe80fe80]
    0xc70049014900c70049010c0049010c00c7020c00c7020c0147004900c901470047004700c7020c020a0187008a004901870087008700c7020c0209014701878000 (by decide +kernel)⟩

def node3gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xf2f2f2f2f2f2f2f2, (inputs6.getD 3 zero)], node_ok [] []
    0xc7008a004900c700470049008a004700c700470047020a01870109004901870087008700c7020c004701070047020a (by decide +kernel)⟩

def node4gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xd0d0d0d0d0d0d0d0, (inputs6.getD 3 zero)], node_ok [] []
    0xc70049018a00c7000a004900c900490047004700c7020a01870009004901870087008700c702090107010701870209 (by decide +kernel)⟩

def node5gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0x2222222222222222, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node3gfe80fe80fe80fe80, node4gfe80fe80fe80fe80]
    0xc70049014900c7000a0049008a004900c7020c00c7020a0187008a004901870087008700c7020c01070187020a0049008a0049008a800100c7800000c701470209 (by decide +kernel)⟩

def node6gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xf4f4f4f4f4f4f4f4, (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c70147004900c901470047004700c7020c008700090049008700c70087008702090107008700870209 (by decide +kernel)⟩

def node7gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xb0b0b0b0b0b0b0b0, (inputs6.getD 1 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x147004900c9014700c70049014900c70047004700c7020a000900090049008a01070107014702090087008700c70209 (by decide +kernel)⟩

def node8gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0x4444444444444444, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node6gfe80fe80fe80fe80, node7gfe80fe80fe80fe80]
    0xc70049014900c70147004900c901470047004700c7020c000900090049008a00c7020c00c70209010701470209008a0049008a0049800100c7800000c7020a0187 (by decide +kernel)⟩

def node9gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0xa0a0a0a0a0a0a0a0, (inputs6.getD 1 zero), 0xfafafafafafafafa, (inputs6.getD 3 zero)], node_ok [] []
    0x900090049008a0147004900c90147020a01470147020900c70049014900c700870047004700c7020a (by decide +kernel)⟩

def node10gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0xa0a0a0a0a0a0a0a0, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node9gfe80fe80fe80fe80]
    0xc0049018a00490147004900c90147020a01470147020a000900090049008a0209020c80000147020a01470209014d0049014d004900c70147020a0147020a0187 (by decide +kernel)⟩

def node11gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xfafafafafafafafa, (inputs6.getD 3 zero)], node_ok [] [node9gfe80fe80fe80fe80]
    0x49008a0049008a00c70049014900c7020c0147004900c90147020a01470147020a0047004700c7020a0187008a00490187020900c701878000010701070147020a (by decide +kernel)⟩

def node12gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xcececececececece, (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x470049018a00470147000a00490147004701470047020a0187008900490187004700870047020c010701070147020a (by decide +kernel)⟩

def node13gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xc4c4c4c4c4c4c4c4, (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc00490149004901470049008a0147004700470147020a018700090049018700870087018702090107010701470209 (by decide +kernel)⟩

def node14gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0xa0a0a0a0a0a0a0a, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node12gfe80fe80fe80fe80, node13gfe80fe80fe80fe80]
    0xc0049018a00490147004900c90147020a01470147020a0187008a0049018700870187020c010701070147020a0049008a0049008a00c780010147800001470209 (by decide +kernel)⟩

def node15gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xdcdcdcdcdcdcdcdc, (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c70147004900c901470047004700c7020a01070009004901070087008700c702090147010701070209 (by decide +kernel)⟩

def node16gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0x8c8c8c8c8c8c8c8c, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c7000900090049008a0087008700c702090147004900c901470047004700c7020a0107010701470209 (by decide +kernel)⟩

def node17gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0x5050505050505050, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node15gfe80fe80fe80fe80, node16gfe80fe80fe80fe80]
    0xc70049014900c70147004900c901470047004700c7020a000900090049008a008700c702090147020a01470209010c0049010c0049020c80010147800001470187 (by decide +kernel)⟩

def node18gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xeecceecceecceecc, (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc700c9018a00c70147004900c901470047004700c7020a0187008900c901870087008700c7020c010701070147020a (by decide +kernel)⟩

def node19gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0x44cc44cc44cc44cc, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c701870009004901870087008700c702090147004900c901470047004700c7020a0107010701470209 (by decide +kernel)⟩

def node20gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xfaf0faf0faf0faf0, (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c701470149008a01470047004700c7020a01870109014901870087008700c7020c010701070147020a (by decide +kernel)⟩

def node21gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0x50f050f050f050f0, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x147004900c901470187000900490187010701070147020900c70049014900c70047004700c7020a0087008700c70209 (by decide +kernel)⟩

def node22gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0xaa00aa00aa00aa00, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node18gfe80fe80fe80fe80, node19gfe80fe80fe80fe80, node20gfe80fe80fe80fe80, node21gfe80fe80fe80fe80]
    0xc7008a018a00c70147000a008a01470047004700c7020a0187008a00ca0087008700c7020c010701070147020a0049800300c7800200c780010147800001470209 (by decide +kernel)⟩

def node23gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xcc88cc88cc88cc88, (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c70147004900c901470047004700c7020a00090009004900ca00c7020c00c702090107010701470209 (by decide +kernel)⟩

def node24gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0x3322332233223322, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c701070209004901070007000700c70209014700c900490147020a00c7004700470209010701470107 (by decide +kernel)⟩

def node25gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xf0a0f0a0f0a0f0a0, (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c70147004900c901470047004700c7020a000900090049008a0087008700c702090147020a01470209 (by decide +kernel)⟩

def node26gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0xf0a0f0a0f0a0f0a, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x147004900c901470087020900490087000700070087020900c70149004900c7020a00c7004700470209008700c70087 (by decide +kernel)⟩

def node27gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffaaffaaffaaffaa], node_ok [] [node23gfe80fe80fe80fe80, node24gfe80fe80fe80fe80, node25gfe80fe80fe80fe80, node26gfe80fe80fe80fe80]
    0x8a800300c700c7800200c70049014900c780010147014780000147004900c901470047004700c7020a01870049020900ca00c7020c00c702090147020a01470209 (by decide +kernel)⟩

def node28gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0xaa00aa00aa00aa, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc7008a018a00c70147000a008a01470047004700c7020a00090209008a00c7020c00c702090147020a01470209004900c7020c00c7020c0147020a0147020a0187 (by decide +kernel)⟩

def node29gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0x5500550055005500, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c70147004900c901470047004700c7020a0009004901870087008700c7020c010701070147020a008a020c00c7020c00c7020a0147020a01470209 (by decide +kernel)⟩

def node30gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xc0c0c0c0c0c0c0c0, 0xfcfcfcfcfcfcfcfc, (inputs6.getD 3 zero)], node_ok [] []
    0xa004900c9004900c70049018a00c70047018700090049018702090187018702090087008700c70209 (by decide +kernel)⟩

def node31gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xc0c0c0c0c0c0c0c0, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node30gfe80fe80fe80fe80]
    0xc004901490049000a004900c90049020a020c8000018e0049018e004900c701470187000900490187020901870187020902090187018702090209018701870209 (by decide +kernel)⟩

def node32gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xfcfcfcfcfcfcfcfc, (inputs6.getD 3 zero)], node_ok [] [node30gfe80fe80fe80fe80]
    0x8a0049008a004900c70049018a00c7020c01470049008a0147020a00c701478000018700090049018702090187018702090087008700c702090107010701470209 (by decide +kernel)⟩

def node33gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0xaeaeaeaeaeaeaeae, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x870049014900870147004900890147004700470087020c018700090049018700870187008702090107010701470209 (by decide +kernel)⟩

def node34gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0xa2a2a2a2a2a2a2a2, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc00490149004901470049008a0147004700470147020a018700090049018700870087018702090107010701470209 (by decide +kernel)⟩

def node35gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0xc0c0c0c0c0c0c0c, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node33gfe80fe80fe80fe80, node34gfe80fe80fe80fe80]
    0xc00490149004901470049008a014700470147020c018700090049018702090187018702090107010701470209008a0049008a004900c7020a8001018780000187 (by decide +kernel)⟩

def node36gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0xbabababababababa, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049010900c70107004900c901070047004700c7020a01870009004901870087008700c702090107018701070209 (by decide +kernel)⟩

def node37gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0x8a8a8a8a8a8a8a8a, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049018a00c7000a004900c900490047004700c7020a01870009004901870087008700c702090107010701870209 (by decide +kernel)⟩

def node38gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0x3030303030303030, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node36gfe80fe80fe80fe80, node37gfe80fe80fe80fe80]
    0xc70049018a00c7000a004900c90049004700c7020a01870009004901870087008700c702090209018701870209010c0049010c0049020c01478001018780000187 (by decide +kernel)⟩

def node39gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), 0xeeaaeeaaeeaaeeaa, (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c701870009004901870087008700c702090147004900c901470047004700c7020c0107010701470209 (by decide +kernel)⟩

def node40gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0x22aa22aa22aa22aa, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c70147004900c901470047004700c7020a01870009004901870087008700c702090107010701470209 (by decide +kernel)⟩

def node41gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xfcf0fcf0fcf0fcf0, (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c70147004900c901470047004700c7020c01870009004901870087008700c702090107010701470209 (by decide +kernel)⟩

def node42gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0x30f030f030f030f0, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x147004900c901470187000900490187010701070147020900c70049014900c70047004700c7020a0087008700c70209 (by decide +kernel)⟩

def node43gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xcc00cc00cc00cc00, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node39gfe80fe80fe80fe80, node40gfe80fe80fe80fe80, node41gfe80fe80fe80fe80, node42gfe80fe80fe80fe80]
    0xc70049014900c70147004900c90047004700c7020c008a800300c7800200c7020a01870009004901870087008700c7020901070107014702090187800180000187 (by decide +kernel)⟩

def node44gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0xaa88aa88aa88aa88, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc7008a018a00c7000a000a00c900c900c7020c00c7020a01870009020901870087008700c702090107010701870209 (by decide +kernel)⟩

def node45gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0x5544554455445544, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70009010900c70107000900c901070007000700c7020a0187000902090187020900c7008700870209010701870107 (by decide +kernel)⟩

def node46gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xf0c0f0c0f0c0f0c0, (inputs6.getD 3 zero)], node_ok [] []
    0xc70049018a00c7000a004900c900490047004700c7020a01870009004901870087008700c702090209018701870209 (by decide +kernel)⟩

def node47gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0xf0c0f0c0f0c0f0c, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x47020a00c900470187020902090187000700070047020900c70049008a00c7020a004700c70047020900c700870087 (by decide +kernel)⟩

def node48gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xffccffccffccffcc], node_ok [] [node44gfe80fe80fe80fe80, node45gfe80fe80fe80fe80, node46gfe80fe80fe80fe80, node47gfe80fe80fe80fe80]
    0x49800300c700c7800200c7008a018a00c70147008a020a00c900c7020c00c7020a800101870187800001870209020901870087008700c702090209018701870209 (by decide +kernel)⟩

def node49gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0xcc00cc00cc00cc, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c7000a020a004900c7020c00c7020a01870009004901870087008700c702090209018701870209008a00c7020c00c7020c01470187020901870209 (by decide +kernel)⟩

def node50gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0x3300330033003300, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc7008a018a00c7000a008a01470047004700c7020c01870209020901870087008700c7020901070107014702090049020c00c7020c00c7020a0209018702090187 (by decide +kernel)⟩

def node51gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xfaaafaaafaaafaaa, (inputs6.getD 3 zero)], node_ok [] []
    0x18700090049018700c70049014900c70087008700c702090147004900c9014701070107014702090047004700c7020a (by decide +kernel)⟩

def node52gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0xaaa0aaa0aaa0aaa, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c70147004900c901470047004700c7020a01870009004901870087008700c702090107010701470209 (by decide +kernel)⟩

def node53gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), 0xfcccfcccfcccfccc, (inputs6.getD 3 zero)], node_ok [] []
    0x147004900c9014700c70049014900c70047004700c7020a018700090049018701070107014702090087008700c70209 (by decide +kernel)⟩

def node54gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0xccc0ccc0ccc0ccc, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc70049014900c701870009004901870087008700c702090147004900c901470047004700c7020a0107010701470209 (by decide +kernel)⟩

def node55gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xf000f000f000f000, (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node51gfe80fe80fe80fe80, node52gfe80fe80fe80fe80, node53gfe80fe80fe80fe80, node54gfe80fe80fe80fe80]
    0xc700490149010c020c0147004900c901470047004700c7020a014780038002014701870009004901870087008700c7020901878001800001870107010701470209 (by decide +kernel)⟩

def node56gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0xaaa0aaa0aaa0aaa0, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc008a014901490147000a008a0147020a01470147020a018700090209018700870087018702090107010701470209 (by decide +kernel)⟩

def node57gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0x5550555055505550, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x870009014900870147000900890147000700070087020a018700090209018702090087018700870209014701070107 (by decide +kernel)⟩

def node58gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xccc0ccc0ccc0ccc0, (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc00490149004901470049020a0147004700470147020a018700090049018702090187018702090107010701470209 (by decide +kernel)⟩

def node59gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 3 w.toFinset} :=
  ⟨[0x3330333033303330, (inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0x47000a014900470187020902090187000700070047020901470049020a0147020a0047014700470209014701070107 (by decide +kernel)⟩

def node60gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), 0xfff0fff0fff0fff0], node_ok [] [node56gfe80fe80fe80fe80, node57gfe80fe80fe80fe80, node58gfe80fe80fe80fe80, node59gfe80fe80fe80fe80]
    0x4900c7010c020c014980030147014780020147020a020a0147020a01470147020a8001018701878000018702090209018702090187018702090107010701470209 (by decide +kernel)⟩

def node61gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0xf000f000f000f0, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc020c00490147004900c90147020a01470147020a018700090049018702090187018702090107010701470209010c00c70147020a0147020a0187020901870209 (by decide +kernel)⟩

def node62gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 4 w.toFinset} :=
  ⟨[0xf000f000f000f00, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] []
    0xc010c00c70147020a020a01470047004700c7020a01870209020901870087008700c7020901070107014702090049020c020a0147020a01470209018702090187 (by decide +kernel)⟩

def node63gfe80fe80fe80fe80 : {w : List Sig // Impossible true goalfe80fe80fe80fe80 5 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [] [node1gfe80fe80fe80fe80, node2gfe80fe80fe80fe80, node5gfe80fe80fe80fe80, node8gfe80fe80fe80fe80, node10gfe80fe80fe80fe80, node11gfe80fe80fe80fe80, node14gfe80fe80fe80fe80, node17gfe80fe80fe80fe80, node22gfe80fe80fe80fe80, node27gfe80fe80fe80fe80, node28gfe80fe80fe80fe80, node29gfe80fe80fe80fe80, node31gfe80fe80fe80fe80, node32gfe80fe80fe80fe80, node35gfe80fe80fe80fe80, node38gfe80fe80fe80fe80, node43gfe80fe80fe80fe80, node48gfe80fe80fe80fe80, node49gfe80fe80fe80fe80, node50gfe80fe80fe80fe80, node55gfe80fe80fe80fe80, node60gfe80fe80fe80fe80, node61gfe80fe80fe80fe80, node62gfe80fe80fe80fe80]
    0x8017010c00c700c780160049020c00498015010c020c01498014004900c700c78013008a0147014780120049020a00498011008a020a00c98010004901470147800f00c7020a0047800e020c01470047800d00c7014700c7800c020c020a020a800b004901870187800a008a0209000980090049020900498008008a01870187800700c7020900878006020c01870087800500c7018700c78004020c0209020980030147020901078002020a0187010780010147018701478000020a02090209 (by decide +kernel)⟩

theorem lowerfe80fe80fe80fe80 : Lower true rootsfe80fe80fe80fe80 goalfe80fe80fe80fe80 6 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 0 zero), 6, 7), ((inputs6.getD 1 zero), 5, 7), ((inputs6.getD 2 zero), 3, 7), ((inputs6.getD 3 zero), 1, 9)]
  have ok : checkEssential goalfe80fe80fe80fe80 rootsfe80fe80fe80fe80 tests = true := by decide +kernel
  have cov : tests.map Prod.fst = rootsfe80fe80fe80fe80 := rfl
  apply lower_impossible (L := 5) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node63gfe80fe80fe80fe80.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha

theorem fiber6gfe80e800fe80e800 : Slice true (inputs6.take 5) minorTarget 0xffff0000ffff0000 6 :=
  slice_correct (ms := [(neg (inputs6.getD 4 zero), zero, 16)]) (base := rootsfe80fe80fe80fe80) (G := goalfe80fe80fe80fe80)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowerfe80fe80fe80fe80

def goale800e800e800e800 : Sig := 0xe800e800e800e800
def rootse800e800e800e800 : List Sig := [(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)]

theorem fiber0ge800e800e800e800 : Slice true rootse800e800e800e800 goale800e800e800e800 0xff00ff00ff00ff00 4 :=
  slice_correct (ms := [(neg (inputs6.getD 3 zero), zero, 8)]) (base := rootse8e8e8e8e8e8e8e8) (G := goale8e8e8e8e8e8e8e8)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowere8e8e8e8e8e8e8e8

def cut0ge800e800e800e800 : {c : Cut // CutGood goale800e800e800e800 c} :=
  ⟨(0xff00ff00ff00ff00, 4, rootse800e800e800e800), cut_good fiber0ge800e800e800e800 [] (by decide +kernel) (by decide)⟩

def node0ge800e800e800e800 : {w : List Sig // Impossible true goale800e800e800e800 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero)], node_ok [cut0ge800e800e800e800] []
    0x14d4000004d00cb024d00cb014d024d01cb00cb400000cb00cb4000004b014d024b004b00cb024b00cb014d4000014d028e024b024b024d030e024d028e030e028e024d024b024b00cb4000008b018e028b008b00cb028b00cb018e4000018e024d028b028b028e030d020d024d030d024d028e028b028b024b030d020b030e028b020b024b028b024b030e030d030d (by decide +kernel)⟩

theorem lowere800e800e800e800 : Lower true rootse800e800e800e800 goale800e800e800e800 5 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 0 zero), 10, 11), ((inputs6.getD 1 zero), 9, 11), ((inputs6.getD 2 zero), 9, 13), ((inputs6.getD 3 zero), 3, 11)]
  have ok : checkEssential goale800e800e800e800 rootse800e800e800e800 tests = true := by decide +kernel
  have cov : tests.map Prod.fst = rootse800e800e800e800 := rfl
  apply lower_impossible (L := 4) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node0ge800e800e800e800.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha

theorem fiber7gfe80e800fe80e800 : Slice true (inputs6.take 5) minorTarget 0xffff0000ffff 5 :=
  slice_correct (ms := [(zero, (inputs6.getD 4 zero), 16)]) (base := rootse800e800e800e800) (G := goale800e800e800e800)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowere800e800e800e800

def goalfa00a000fa00a000 : Sig := 0xfa00a000fa00a000
def rootsfa00a000fa00a000 : List Sig := [(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)]

theorem fiber0gfa00a000fa00a000 : Slice true rootsfa00a000fa00a000 goalfa00a000fa00a000 0xff00ff00ff00ff00 4 :=
  slice_correct (ms := [(neg (inputs6.getD 3 zero), zero, 8)]) (base := rootsfafaa0a0fafaa0a0) (G := goalfafaa0a0fafaa0a0)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowerfafaa0a0fafaa0a0

def cut0gfa00a000fa00a000 : {c : Cut // CutGood goalfa00a000fa00a000 c} :=
  ⟨(0xff00ff00ff00ff00, 4, rootsfa00a000fa00a000), cut_good fiber0gfa00a000fa00a000 [] (by decide +kernel) (by decide)⟩

def node0gfa00a000fa00a000 : {w : List Sig // Impossible true goalfa00a000fa00a000 4 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [cut0gfa00a000fa00a000] []
    0x259014d014d40000459005902590459054d4000014d014d031c024d024d0259061c0259031c061c031c0259024d024d014d4000004d0459024d004d014d024d014d0459400004590259030d030d031c06190219025906190259031c030d030d014d4000010d051c030d010d014d030d014d051c4000051c024d0619020d061c030d020d024d030d024d061c06190619 (by decide +kernel)⟩

theorem lowerfa00a000fa00a000 : Lower true rootsfa00a000fa00a000 goalfa00a000fa00a000 5 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 0 zero), 12, 13), ((inputs6.getD 2 zero), 9, 13), ((inputs6.getD 3 zero), 5, 13), ((inputs6.getD 4 zero), 9, 25)]
  have ok : checkEssential goalfa00a000fa00a000 rootsfa00a000fa00a000 tests = true := by decide +kernel
  have cov : tests.map Prod.fst = rootsfa00a000fa00a000 := rfl
  apply lower_impossible (L := 4) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node0gfa00a000fa00a000.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha

theorem fiber8gfe80e800fe80e800 : Slice true (inputs6.take 5) minorTarget 0x3333333333333333 5 :=
  slice_correct (ms := [(zero, (inputs6.getD 1 zero), 2)]) (base := rootsfa00a000fa00a000) (G := goalfa00a000fa00a000)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) lowerfa00a000fa00a000

def cut0gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0x2222222222222222 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(2, (inputs6.getD 0 zero), (inputs6.getD 1 zero))] (by decide +kernel) (by decide)⟩

def cut1gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xcccccccccccccccc, 6, (inputs6.take 5)), cut_good fiber1gfe80e800fe80e800 [] (by decide +kernel) (by decide)⟩

def cut2gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xaaaaaaaaaaaaaaaa, 6, (inputs6.take 5)), cut_good fiber2gfe80e800fe80e800 [] (by decide +kernel) (by decide)⟩

def cut3gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0x4444444444444444 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(3, (inputs6.getD 0 zero), (inputs6.getD 1 zero))] (by decide +kernel) (by decide)⟩

def cut4gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0x5555555555555555, 5, (inputs6.take 5)), cut_good fiber3gfe80e800fe80e800 [] (by decide +kernel) (by decide)⟩

def cut5gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xf0f0f0f0f0f0f0f0, 6, (inputs6.take 5)), cut_good fiber4gfe80e800fe80e800 [] (by decide +kernel) (by decide)⟩

def cut6gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xf0f0f0f0f0f0f0f0, 5, 0x8888888888888888 :: (inputs6.take 5)), cut_good fiber4gfe80e800fe80e800 [(0, (inputs6.getD 0 zero), (inputs6.getD 1 zero))] (by decide +kernel) (by decide)⟩

def cut7gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xf0f0f0f0f0f0f0f, 5, (inputs6.take 5)), cut_good fiber5gfe80e800fe80e800 [] (by decide +kernel) (by decide)⟩

def cut8gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0x8888888888888888 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(0, (inputs6.getD 0 zero), (inputs6.getD 1 zero))] (by decide +kernel) (by decide)⟩

def cut9gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 7, (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [] (by decide +kernel) (by decide)⟩

def cut10gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xffff0000ffff0000, 6, (inputs6.take 5)), cut_good fiber6gfe80e800fe80e800 [] (by decide +kernel) (by decide)⟩

def cut11gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xffff0000ffff0000, 5, 0x8888888888888888 :: (inputs6.take 5)), cut_good fiber6gfe80e800fe80e800 [(0, (inputs6.getD 0 zero), (inputs6.getD 1 zero))] (by decide +kernel) (by decide)⟩

def cut12gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xffff0000ffff, 5, (inputs6.take 5)), cut_good fiber7gfe80e800fe80e800 [] (by decide +kernel) (by decide)⟩

def cut13gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xaaaaaaaaaaaaaaaa, 5, 0xf0f00000f0f00000 :: (inputs6.take 5)), cut_good fiber2gfe80e800fe80e800 [(0, (inputs6.getD 2 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut14gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0x3333333333333333, 5, (inputs6.take 5)), cut_good fiber8gfe80e800fe80e800 [] (by decide +kernel) (by decide)⟩

def cut15gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0xa0a0a0a0a0a0a0a :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(2, (inputs6.getD 0 zero), (inputs6.getD 2 zero))] (by decide +kernel) (by decide)⟩

def cut16gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xcccccccccccccccc, 5, 0xa0a0a0a0a0a0a0a0 :: (inputs6.take 5)), cut_good fiber1gfe80e800fe80e800 [(0, (inputs6.getD 0 zero), (inputs6.getD 2 zero))] (by decide +kernel) (by decide)⟩

def cut17gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0x5050505050505050 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(3, (inputs6.getD 0 zero), (inputs6.getD 2 zero))] (by decide +kernel) (by decide)⟩

def cut18gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0xa0a0a0a0a0a0a0a0 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(0, (inputs6.getD 0 zero), (inputs6.getD 2 zero))] (by decide +kernel) (by decide)⟩

def cut19gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xffff0000ffff0000, 5, 0xa0a0a0a0a0a0a0a0 :: (inputs6.take 5)), cut_good fiber6gfe80e800fe80e800 [(0, (inputs6.getD 0 zero), (inputs6.getD 2 zero))] (by decide +kernel) (by decide)⟩

def cut20gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xaaaaaaaaaaaaaaaa, 5, 0xcccc0000cccc0000 :: (inputs6.take 5)), cut_good fiber2gfe80e800fe80e800 [(0, (inputs6.getD 1 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut21gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0xaaaa0000aaaa :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(2, (inputs6.getD 0 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut22gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xcccccccccccccccc, 5, 0xaaaa0000aaaa0000 :: (inputs6.take 5)), cut_good fiber1gfe80e800fe80e800 [(0, (inputs6.getD 0 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut23gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xf0f0f0f0f0f0f0f0, 5, 0xaaaa0000aaaa0000 :: (inputs6.take 5)), cut_good fiber4gfe80e800fe80e800 [(0, (inputs6.getD 0 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut24gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0xaaaa0000aaaa0000 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(0, (inputs6.getD 0 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut25gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0x5555000055550000 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(3, (inputs6.getD 0 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut26gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xaaaaaaaaaaaaaaaa, 5, 0xc0c0c0c0c0c0c0c0 :: (inputs6.take 5)), cut_good fiber2gfe80e800fe80e800 [(0, (inputs6.getD 1 zero), (inputs6.getD 2 zero))] (by decide +kernel) (by decide)⟩

def cut27gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0xc0c0c0c0c0c0c0c0 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(0, (inputs6.getD 1 zero), (inputs6.getD 2 zero))] (by decide +kernel) (by decide)⟩

def cut28gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xffff0000ffff0000, 5, 0xc0c0c0c0c0c0c0c0 :: (inputs6.take 5)), cut_good fiber6gfe80e800fe80e800 [(0, (inputs6.getD 1 zero), (inputs6.getD 2 zero))] (by decide +kernel) (by decide)⟩

def cut29gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0xc0c0c0c0c0c0c0c :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(2, (inputs6.getD 1 zero), (inputs6.getD 2 zero))] (by decide +kernel) (by decide)⟩

def cut30gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0x3030303030303030 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(3, (inputs6.getD 1 zero), (inputs6.getD 2 zero))] (by decide +kernel) (by decide)⟩

def cut31gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xf0f0f0f0f0f0f0f0, 5, 0xcccc0000cccc0000 :: (inputs6.take 5)), cut_good fiber4gfe80e800fe80e800 [(0, (inputs6.getD 1 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut32gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0xcccc0000cccc0000 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(0, (inputs6.getD 1 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut33gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0xcccc0000cccc :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(2, (inputs6.getD 1 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut34gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0x3333000033330000 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(3, (inputs6.getD 1 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut35gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xcccccccccccccccc, 5, 0xf0f00000f0f00000 :: (inputs6.take 5)), cut_good fiber1gfe80e800fe80e800 [(0, (inputs6.getD 2 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut36gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0xf0f00000f0f00000 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(0, (inputs6.getD 2 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut37gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0xf0f00000f0f0 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(2, (inputs6.getD 2 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def cut38gfe80e800fe80e800 : {c : Cut // CutGood minorTarget c} :=
  ⟨(0xff00ff00ff00ff00, 6, 0xf0f00000f0f0000 :: (inputs6.take 5)), cut_good fiber0gfe80e800fe80e800 [(3, (inputs6.getD 2 zero), (inputs6.getD 4 zero))] (by decide +kernel) (by decide)⟩

def node0gfe80e800fe80e800 : {w : List Sig // Impossible true minorTarget 5 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), 0xf8f88888f8f88888, (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0xcb01d704cb00cb01d7025901d7025900cb014d00cb014d024d00d701d7024d004d00cb01cb00cb024d04d704d7024d030e055701d7030e00cb014d00cb014d024b024b0557030e020e024d028e024d030d059701d7030d00cb010d00cb018e028b028b0597030d020d020d024d028e030d030e0557030d (by decide +kernel)⟩

def node1gfe80e800fe80e800 : {w : List Sig // Impossible true minorTarget 6 w.toFinset} :=
  ⟨[0x8888888888888888, (inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xf0f00000f0f00000, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [cut4gfe80e800fe80e800, cut7gfe80e800fe80e800, cut5gfe80e800fe80e800, cut10gfe80e800fe80e800, cut12gfe80e800fe80e800, cut13gfe80e800fe80e800, cut2gfe80e800fe80e800, cut1gfe80e800fe80e800, cut14gfe80e800fe80e800, cut6gfe80e800fe80e800] [node0gfe80e800fe80e800]
    0xcb005904cb00cb024d02594009004d00cb01cb00cb01d7051c00cb051c00cb04d7030e0259029a030e00cb014d00cb014d020e024d028e024d030e40084007030e030d02190259030d00cb010d00cb018e020d020d024d028e030d40004006030d030d030e4005400402594003025900cb014d00cb014d4001024d4002024d4001400080004000024b028b (by decide +kernel)⟩

def node2gfe80e800fe80e800 : {w : List Sig // Impossible true minorTarget 7 w.toFinset} :=
  ⟨[0x8888888888888888, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [cut0gfe80e800fe80e800, cut1gfe80e800fe80e800, cut2gfe80e800fe80e800, cut3gfe80e800fe80e800, cut4gfe80e800fe80e800, cut5gfe80e800fe80e800, cut6gfe80e800fe80e800, cut7gfe80e800fe80e800, cut8gfe80e800fe80e800, cut9gfe80e800fe80e800, cut10gfe80e800fe80e800, cut11gfe80e800fe80e800, cut12gfe80e800fe80e800] [node1gfe80e800fe80e800]
    0x4008025900cb00cb400801d7045901d740080259045904cb400801d700cb00cb400601d7024d024d400b025904d700d7400601d704d701d780000259024d024d4008014d04d7004d400800cb024d00cb4008014d024d01cb400800cb04d700cb400101d7030e030e40010259061a0259400101d7061a01d740010259030e030e400800cb400800cb4008014d030e014d400800cb030e00cb4008014d4008014d4001028e061a020e4001024d030e024d4001028e030e028e4001024d061a024d400201d7030d030d4002029a06190219400201d7061901d74002029a030d030d400800cb400800cb4008018e030d010d400800cb030d00cb4008018e4008018e4002024d0619020d4002028e030d020d4002024d030d024d4002028e0619028e40024002030d030d4002030e4001030e4002400240024002400401d7400c01d7400b0259400a0259400b01d7400a01d74004025940040259400800cb400800cb4008014d4009014d400800cb400900cb4008014d4008014d400404d7400704d74006024d4005024d400604d7400504d74004024d4004024d400240024003024b400240014000028b (by decide +kernel)⟩

def node3gfe80e800fe80e800 : {w : List Sig // Impossible true minorTarget 5 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xececa0a0ececa0a0, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0xcb01d7054d00cb028e04d701d7028e014d00cb014d00cb01d7025901d70259014d00cb014d00cb024d024d04d7028e024b015701d7024b004b004b00cb014d024b020e028e024b024b05570557024b028b059701d7028b008b008b00cb018e028b028e04d7028b028b030d0597028b020b020b024b030e (by decide +kernel)⟩

def node4gfe80e800fe80e800 : {w : List Sig // Impossible true minorTarget 6 w.toFinset} :=
  ⟨[0xa0a0a0a0a0a0a0a0, (inputs6.getD 0 zero), 0xcccc0000cccc0000, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [cut4gfe80e800fe80e800, cut14gfe80e800fe80e800, cut1gfe80e800fe80e800, cut10gfe80e800fe80e800, cut12gfe80e800fe80e800, cut2gfe80e800fe80e800, cut20gfe80e800fe80e800, cut5gfe80e800fe80e800, cut7gfe80e800fe80e800, cut16gfe80e800fe80e800] [node3gfe80e800fe80e800]
    0xcb0059054d00cb028e0259031c028e014d00cb014d00cb024b02594009004b004b00cb014d024b020e028e024b01d7049a00cb049a00cb4008028e4007028e0557028b02190259028b008b008b00cb018e028b028e4006020b020b024b030e028b40004005028b4004025940030259014d00cb014d00cb024d4001024b4002024b4001400080004000030d (by decide +kernel)⟩

def node5gfe80e800fe80e800 : {w : List Sig // Impossible true minorTarget 7 w.toFinset} :=
  ⟨[0xa0a0a0a0a0a0a0a0, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [cut15gfe80e800fe80e800, cut5gfe80e800fe80e800, cut2gfe80e800fe80e800, cut4gfe80e800fe80e800, cut1gfe80e800fe80e800, cut16gfe80e800fe80e800, cut14gfe80e800fe80e800, cut17gfe80e800fe80e800, cut18gfe80e800fe80e800, cut9gfe80e800fe80e800, cut10gfe80e800fe80e800, cut19gfe80e800fe80e800, cut12gfe80e800fe80e800] [node4gfe80e800fe80e800]
    0x4008025900cb00cb400801d7045901d740080259045904cb400801d700cb00cb400101d7028e028e40010259061c0259400101d7061c01d740010259028e028e4008014d4008014d400800cb028e00cb4008014d028e014d400800cb400800cb400501d7024b024b400b025905570157400501d7055701d780000259024b024b400800cb0557004b4008014d024b004b400800cb024b00cb4008014d0557014d4005028e024b024b4001061c030e020e4005028e030e028e4001061c024b024b400201d7028b028b4002029a06190219400201d7061901d74002029a028b028b400800cb4008008b4008018e028b008b400800cb028b00cb4008018e4008018e40024002028b028b4002028e4001028e40024002400240024002024b0619020b4002030e028b020b4002024b028b024b4002030e0619030e400301d7400c01d7400b0259400a0259400b01d7400a01d740030259400302594008014d4008014d400800cb400900cb4008014d4009014d400800cb400800cb400240024007024d40030557400605574005024b4004024b40050557400405574003024b4003024b400240014000030d (by decide +kernel)⟩

def node6gfe80e800fe80e800 : {w : List Sig // Impossible true minorTarget 5 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xeaeac0c0eaeac0c0, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [] []
    0xcb01d7058e00cb024d04d701d7024d004d00cb014d00cb01d7025901d7029a018e00cb018e00cb028e024d04d7024d024b055701d7024b004b004b00cb014d024b024d04d7024b024b030e0557024b028b019701d7028b008b008b00cb018e028b020d024d028b028b05970597028b020b020b024b030d (by decide +kernel)⟩

def node7gfe80e800fe80e800 : {w : List Sig // Impossible true minorTarget 6 w.toFinset} :=
  ⟨[0xaaaa0000aaaa0000, (inputs6.getD 0 zero), 0xc0c0c0c0c0c0c0c0, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [cut4gfe80e800fe80e800, cut14gfe80e800fe80e800, cut1gfe80e800fe80e800, cut5gfe80e800fe80e800, cut7gfe80e800fe80e800, cut2gfe80e800fe80e800, cut26gfe80e800fe80e800, cut10gfe80e800fe80e800, cut12gfe80e800fe80e800, cut22gfe80e800fe80e800] [node6gfe80e800fe80e800]
    0xcb0459058e00cb024d029a031c024d004d00cb014d00cb024b021a029a024b004b004b00cb014d024b024d40094008029a4007029a018e00cb018e00cb028e030e028b029a4006008b008b00cb018e028b020d024d028b020b020b024b030d028b40004005028b01d7045900cb045900cb4004024d4003024d4001024b4002024b40014000800040000597 (by decide +kernel)⟩

def node8gfe80e800fe80e800 : {w : List Sig // Impossible true minorTarget 7 w.toFinset} :=
  ⟨[0xaaaa0000aaaa0000, (inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [cut21gfe80e800fe80e800, cut10gfe80e800fe80e800, cut2gfe80e800fe80e800, cut4gfe80e800fe80e800, cut1gfe80e800fe80e800, cut22gfe80e800fe80e800, cut14gfe80e800fe80e800, cut5gfe80e800fe80e800, cut23gfe80e800fe80e800, cut7gfe80e800fe80e800, cut24gfe80e800fe80e800, cut9gfe80e800fe80e800, cut25gfe80e800fe80e800] [node7gfe80e800fe80e800]
    0x400a029a00cb00cb400a400a04590459400a029a0459058e400a400a00cb00cb4008031c024d024d4001029a04d704d74008031c04d704d74001029a024d024d400a014d04d7004d400a00cb024d00cb400a014d024d01cb400a00cb04d700cb4005029a024b024b4001031c055705574005029a055705574001031c024b024b400a00cb0557004b400a014d024b004b400a00cb024b00cb400a014d0557014d4005028e024b024b4008024d030e024d4005028e030e028e8000024d024b024b40024002028b028b4002029a4001029a4002400240024002400a00cb400a008b400a018e028b008b400a00cb028b00cb400a018e400a018e4002024d028b028b4002028e030d020d4002024d030d024d4002028e028b028b4002024b030d020b4002030e028b020b4002024b028b024b4002030e030d030d40024002400c01d7400a0459400a0459400a00cb400b00cb400a0459400b0459400a00cb400a00cb400304d7400904d74008024d4007024d400804d7400704d74003024d4003024d40030557400605574005024b4004024b40050557400405574003024b4003024b4002400140000597 (by decide +kernel)⟩

def node9gfe80e800fe80e800 : {w : List Sig // Impossible true minorTarget 7 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xc0c0c0c0c0c0c0c0, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [cut4gfe80e800fe80e800, cut14gfe80e800fe80e800, cut2gfe80e800fe80e800, cut26gfe80e800fe80e800, cut1gfe80e800fe80e800, cut5gfe80e800fe80e800, cut27gfe80e800fe80e800, cut28gfe80e800fe80e800, cut29gfe80e800fe80e800, cut30gfe80e800fe80e800, cut9gfe80e800fe80e800, cut10gfe80e800fe80e800, cut12gfe80e800fe80e800] [node7gfe80e800fe80e800]
    0x4006025900cb00cb400601d7045901d740060259045904cb400601d700cb00cb400501d7024d024d40050259061c0259400501d7061c01d740050259024d024d4006014d4006004d400600cb024d00cb4006014d024d014d400600cb400600cb400401d7024b024b40040259061a0259400401d7061a01d740040259024b024b400600cb4006004b4006014d024b004b400600cb024b00cb4006014d4006014d40044004024b024b4004024d4005024d4004400440044004400101d7400c01d740070259400b0259400701d7400b01d740010259400102594006018e4006018e400600cb400a00cb4006018e400a018e400600cb400600cb400440044009028e400440054008030e400301d7028b028b4007029a05970197400301d7059701d78000029a028b028b400600cb0597008b4006018e028b008b400600cb028b00cb4006018e0597018e4003024d028b028b4005061c030d020d4003024d030d024d4005061c028b028b4003024b030d020b4004061a028b020b4003024b028b024b4004061a030d030d40034002028b028b4001400005970597400340020597059740014000028b028b (by decide +kernel)⟩

def node10gfe80e800fe80e800 : {w : List Sig // Impossible true minorTarget 7 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), 0xcccc0000cccc0000, (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [cut4gfe80e800fe80e800, cut14gfe80e800fe80e800, cut2gfe80e800fe80e800, cut20gfe80e800fe80e800, cut1gfe80e800fe80e800, cut31gfe80e800fe80e800, cut32gfe80e800fe80e800, cut10gfe80e800fe80e800, cut33gfe80e800fe80e800, cut5gfe80e800fe80e800, cut7gfe80e800fe80e800, cut9gfe80e800fe80e800, cut34gfe80e800fe80e800] [node4gfe80e800fe80e800]
    0x4006025900cb00cb4006400604590059400602590459054d4006400600cb00cb4005031c024d024d4007025904d704d74005031c04d704d740070259024d024d4006014d04d7004d400600cb024d00cb4006014d024d01cb400600cb04d700cb40044004024b024b40040259400702594004400440044004400600cb4006004b4006014d024b004b400600cb024b00cb4006014d4006014d4004028e024b024b4004024d030e024d4004028e030e028e4004024d024b024b40044004400c01d74006049a4006049a400600cb400b00cb4006049a400b049a400600cb400600cb400104d7400a04d74005024d4009024d400504d7400904d74001024d4001024d400440074008055740030259028b028b4007031c0597059740030259059705974007031c028b028b400600cb0597008b4006018e028b008b400600cb028b00cb4006018e0597018e4003024d028b028b4005028e030d020d4003024d030d024d8000028e028b028b4003024b030d020b4004030e028b020b4003024b028b024b4004030e030d030d40034002028b028b4001400005970597400340020597059740014000028b028b (by decide +kernel)⟩

def node11gfe80e800fe80e800 : {w : List Sig // Impossible true minorTarget 7 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), 0xf0f00000f0f00000, (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [cut13gfe80e800fe80e800, cut35gfe80e800fe80e800, cut4gfe80e800fe80e800, cut7gfe80e800fe80e800, cut2gfe80e800fe80e800, cut5gfe80e800fe80e800, cut36gfe80e800fe80e800, cut10gfe80e800fe80e800, cut14gfe80e800fe80e800, cut1gfe80e800fe80e800, cut37gfe80e800fe80e800, cut9gfe80e800fe80e800, cut38gfe80e800fe80e800] [node1gfe80e800fe80e800]
    0x4006025900cb00cb400640060459005940060259045904cb4006400600cb00cb40054005024d024d400502594007025940054005400540054006014d4006004d400600cb024d00cb4006014d024d01cb400600cb400600cb40054005400c01d74006051c4006051c400600cb400b00cb4006051c400b051c400600cb400600cb40054007400a04d74001029a024b024b40070259055705574001029a0557055740070259024b024b400600cb0557004b4006014d024b004b400600cb024b00cb4006014d0557014d4001028e024b024b4005024d030e024d4001028e030e028e4005024d024b024b40014009024b024b4003400805570557400140090557055740034008024b024b40000259028b028b4007029a0597059740000259059705974007029a028b028b400600cb0597008b4006018e028b008b400600cb028b00cb4006018e0597018e4000024d028b028b4005028e030d020d4000024d030d024d4005028e028b028b40004004028b028b4003400205970597400040040597059740034002028b028b4000024b030d020b4001030e028b020b4000024b028b024b8000030e030d030d (by decide +kernel)⟩

def node12gfe80e800fe80e800 : {w : List Sig // Impossible true minorTarget 8 w.toFinset} :=
  ⟨[(inputs6.getD 0 zero), (inputs6.getD 1 zero), (inputs6.getD 2 zero), (inputs6.getD 3 zero), (inputs6.getD 4 zero)], node_ok [cut2gfe80e800fe80e800, cut1gfe80e800fe80e800, cut5gfe80e800fe80e800, cut9gfe80e800fe80e800, cut10gfe80e800fe80e800] [node2gfe80e800fe80e800, node5gfe80e800fe80e800, node8gfe80e800fe80e800, node9gfe80e800fe80e800, node10gfe80e800fe80e800, node11gfe80e800fe80e800]
    0x4003025900cb00cb400301d7045901d740030259045904cb400301d700cb00cb400201d7024d024d4004025904d700d7400201d704d701d780050259024d024d4003014d04d7004d400300cb024d00cb4003014d024d01cb400300cb04d700cb400101d7024b024b4004025905570157400101d7055701d780040259024b024b400300cb0557004b4003014d024b004b400300cb024b00cb4003014d0557014d4001028e024b024b4002024d030e024d4001028e030e028e8003024d024b024b400001d7028b028b4004029a05970197400001d7059701d78002029a028b028b400300cb0597008b4003018e028b008b400300cb028b00cb4003018e0597018e4000024d028b028b4002028e030d020d4000024d030d024d8001028e028b028b4000024b030d020b4001030e028b020b4000024b028b024b8000030e030d030d (by decide +kernel)⟩

theorem lowerfe80e800fe80e800 : Lower true (inputs6.take 5) minorTarget 9 := by
  let tests : List (Sig × Row × Row) := [((inputs6.getD 0 zero), 10, 11), ((inputs6.getD 1 zero), 9, 11), ((inputs6.getD 2 zero), 9, 13), ((inputs6.getD 3 zero), 3, 11), ((inputs6.getD 4 zero), 7, 23)]
  have ok : checkEssential minorTarget (inputs6.take 5) tests = true := by decide +kernel
  have cov : tests.map Prod.fst = (inputs6.take 5) := rfl
  apply lower_impossible (L := 8) (by unfold proper; decide +kernel)
    (essential_plain ok).1 (essential_plain ok).2 _ node12gfe80e800fe80e800.property
  intro a ha
  apply essential_ok ok a
  rw [cov]
  exact List.mem_toFinset.mpr ha


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target6 : Sig := 0xfe80fe00fe80e800

def targetFunction (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4269866496 * 2 ^ 32 + 4269860864)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

private def sampleInput (r : Row) (i : Fin 6) : Bool :=
  bit r (inputs6.getD i.val zero)

private theorem inputList : List.ofFn (fun i : Fin 6 => inputs6.getD i.val zero) = inputs6 :=
  rfl

private theorem sampled (r : Row) : List.ofFn (sampleInput r) = inputs6.map (bit r) := by
  rw [← inputList, List.map_ofFn]
  rfl

private theorem targetTable : ∀ r : Row, bit r target6 = targetFunction (sampleInput r) := by
  decide +kernel

private theorem targetProper : proper target6 := proper_of _ (by decide +kernel)

private def essentialPairs : List (Sig × Row × Row) :=
  [(0xaaaaaaaaaaaaaaaa, 10, 11), (0xcccccccccccccccc, 9, 11),
   (0xf0f0f0f0f0f0f0f0, 9, 13), (0xff00ff00ff00ff00, 3, 11),
   (0xffff0000ffff0000, 7, 23), (0xffffffff00000000, 9, 41)]

private theorem allRequired (a : Sig) (ha : a ∈ inputs6) : Essential target6 inputs6 a := by
  apply essential_ok (xs := essentialPairs)
  · decide +kernel
  · have h : (essentialPairs.map Prod.fst).toFinset = inputs6.toFinset := rfl
    rw [h, List.mem_toFinset]
    exact ha

private theorem sampledEval (C : Circuit) (h : FanInTwo C) (r : Row) :
    bit r ((execute C.gates inputs6).getD C.output zero) =
      C.eval (List.ofFn (sampleInput r)) := by
  rw [← b_read, execute_bits _ _ _ (fun g hg => (h g hg).1), sampled]
  rfl

-- The execution model gives an AND/OR derivation with free complements.
private theorem physicalSigned (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetFunction x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true target6 k inputs6.toFinset := by
  have goalEq : (execute C.gates inputs6).getD C.output zero = target6 := by
    apply bit_ext
    intro r
    exact (sampledEval C legal r).trans ((computes _).trans (targetTable r).symm)
  have out := get_rep (u := true) (execute C.gates inputs6) C.output
  rw [goalEq] at out
  unfold Repr at out
  rw [nrm_id (by decide +kernel : bit 0 target6 = false)] at out
  obtain ⟨k, S, hk, run, sub⟩ := extract (u := true) C.gates inputs6 legal (by simp)
    targetProper (out.resolve_right fun h => h targetProper)
  rw [nrm_map (by decide +kernel : inputs6.all plainWord = true)] at sub
  have eq : S = inputs6.toFinset := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨sub a, fun ha => ?_⟩
    obtain ⟨r, s, diff, rest⟩ := allRequired a ha
    exact raw_required run inputs6 a sub r s diff rest
  exact ⟨k, hk, eq ▸ run⟩

private def fixedRows : List Move := [(zero, 0xffffffff00000000, 32)]

private def fixedDomain : Sig := 0x00000000ffffffff

-- The sixth live input turns into a constant under this restriction.
private theorem noNineBinary (minorLower : Lower true (inputs6.take 5) minorTarget 9) :
    Impossible true target6 9 inputs6.toFinset := by
  have slice : Slice true inputs6 target6 fixedDomain 9 :=
    slice_correct (ms := fixedRows) (by decide +kernel) (by decide +kernel)
      (proper_of _ (by decide +kernel)) minorLower
  have rule := cut_good slice [] (by rfl) (by decide)
  exact rule 9 inputs6 (by decide +kernel) (by decide +kernel)

-- The nine-gate core follows L-meta-8645 (PR 12833). Its fifth input is
-- replaced by x4 ∨ (x3 ∧ x5).
private def witnessEleven : Circuit :=
  ⟨[⟨.and, [3, 5]⟩, ⟨.or, [4, 6]⟩,
    ⟨.and, [0, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [8, 10]⟩,
    ⟨.and, [1, 2]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [12, 14]⟩,
    ⟨.and, [11, 15]⟩], 16⟩

private theorem witnessMonotone : Monotone2 witnessEleven := by
  simp [Monotone2, witnessEleven]

private theorem witnessEval : ∀ x : Fin 6 → Bool,
    witnessEleven.eval (List.ofFn x) = targetFunction x := by decide +kernel

theorem fromMinor (minorLower : Lower true (inputs6.take 5) minorTarget 9) :
    ∀ s : ℕ, HasCircuitSize 6 targetFunction s →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
        C.eval (List.ofFn x) = targetFunction x := by
  intro s hs
  rcases hs with ⟨C, legal, size, computes⟩
  by_cases enough : 11 ≤ s
  · exact ⟨witnessEleven, witnessMonotone, enough, witnessEval⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hg, hop⟩ := hasNot
    have short : C.gates.countP (fun q => !isNot q) < C.size := by
      exact List.countP_lt_length_iff.mpr ⟨g, hg, by simp [isNot, hop]⟩
    obtain ⟨k, hk, run⟩ := physicalSigned C legal computes
    exact (noNineBinary minorLower k (by omega) run).elim
  · refine ⟨C, ?_, size, computes⟩
    intro g hg
    obtain ⟨ops, arity⟩ := legal g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops ⊢
    rcases ops with h | h | h
    · exact ⟨Or.inl h, arity⟩
    · exact ⟨Or.inr h, arity⟩
    · exact (hasNot ⟨g, hg, h⟩).elim

end PEqualNP.Outside.L_meta_12098

theorem PEqualNP.Outside.L_meta_12098 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269866496 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269866496 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_12098.fromMinor PEqualNP.Outside.L_meta_12098.lowerfe80e800fe80e800
