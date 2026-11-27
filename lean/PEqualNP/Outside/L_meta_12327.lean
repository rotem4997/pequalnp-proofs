import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12327

-- The signed restriction checker builds on the proofs of L_meta_10694 and L_meta_10698.
-- The circuit semantics and the live wire restriction lemmas are adapted from
-- L_meta_10802 and its predecessors L_meta_1674, L_meta_670 and L_meta_1667.
-- Signals are truth tables on the 128 assignments to the seven inputs.

open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
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

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
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


abbrev Row := Fin 128
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
  if h : r.val < 128-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(128-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 128 (128-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 128-d.val <;> simp [shifted,h,r.isLt]

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
  decide (k < c.2.1 + ws.countP (isMaskedConstant c.1)) &&
    ws.all (availableB true c.1 c.2.2)

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
    let r := Fin.ofNat 128 (code % 128)
    let s := Fin.ofNat 128 (code / 128)
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
def input (i : Nat) := inputs.getD i zero
def selected (m : Nat) := (List.range 7).filter (fun i => m.testBit i)
def roots (m : Nat) := (selected m).map input

def ternaryFix (q t : Nat) : List Move :=
  ((List.range 7).filter fun i => !(q.testBit i)).map fun i =>
    if t.testBit i then (neg (input i),zero,Fin.ofNat 128 (1 <<< i))
    else (zero,input i,Fin.ofNat 128 (1 <<< i))

def ternaryDomain (q t : Nat) : Sig :=
  ((List.range 7).filter fun i => !(q.testBit i)).foldl (fun d i =>
    d &&& (if t.testBit i then input i else neg (input i))) one

def trials (m h : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun i =>
    let a := (h >>> (7*i)) % 128
    (input i,Fin.ofNat 128 a,Fin.ofNat 128 (a ||| (1 <<< i)))

abbrev CClaim (m : Nat) (T : Sig) (L : Nat) := Lower true (roots m) T L
abbrev Ex (T : Sig) (k : Nat) (ws : List Sig) := Impossible true T k ws.toFinset

def necessity (m : Nat) (T : Sig) (h : Nat) :=
  (properB T && checkEssential T (roots m) (trials m h)) &&
    ((trials m h).map Prod.fst == roots m)

theorem fromTable {m T k} (h : Nat) (ok : necessity m T h = true)
    (no : Ex T k (roots m)) : CClaim m T (k+1) := by
  simp only [necessity,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ no
  intro w hw
  apply essential_ok ok.1.2 w
  rw [ok.2]
  exact List.mem_toFinset.mpr hw

def countTest (m : Nat) (T : Sig) (h L : Nat) :=
  (properB T && checkEssential T (roots m) (trials m h)) &&
    decide (L ≤ ((trials m h).map Prod.fst).toFinset.card-1)

theorem initialCount (m : Nat) (T : Sig) (h L : Nat) (ok : countTest m T h L = true) : CClaim m T L := by
  simp only [countTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have lb := lower_count (u:=true) (proper_of _ ok.1.1) _ ok.1.2
  exact fun p b run out => ok.2.trans (lb p b run out)

def liftTest (m : Nat) (T : Sig) (q t : Nat) (G : Sig) (e h L K : Nat) :=
  ((checkLift (ternaryFix q t) T (roots m) (roots q) G (trials e h) && properB T) && properB G) &&
    decide (K ≤ L + ((trials e h).map Prod.fst).toFinset.card)

theorem liftTable {m T q G L} (t e h K : Nat) (lo : CClaim q G L)
    (ok : liftTest m T q t G e h L K = true) : CClaim m T K := by
  simp only [liftTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have lb := lift_ok ok.1.1.1 (proper_of _ ok.1.1.2) (proper_of _ ok.1.2) lo
  exact fun p b run out => ok.2.trans (lb p b run out)

def poolFor (q : Nat) (ex : Option Choice) : List Sig :=
  match ex with
  | none => roots q
  | some c => choiceVal c :: roots q

def restrictionTest (T : Sig) (q t : Nat) (G : Sig) (L : Nat) (ex : Option Choice) :=
  (((checkMap (ternaryFix q t) (roots q) T (roots q) G &&
    (movedWord (ternaryFix q t) (ternaryDomain q t) == one)) && properB G) &&
    (makePool true (ternaryDomain q t) (roots q) ex.toList == some (poolFor q ex))) &&
    decide (ex.toList.length ≤ L)

def rule (T : Sig) {q G L} (t : Nat) (lo : CClaim q G L) (ex : Option Choice)
    (ok : restrictionTest T q t G L ex = true) : {c : Cut // CutGood T c} := by
  refine ⟨(ternaryDomain q t,L-ex.toList.length,poolFor q ex),?_⟩
  simp only [restrictionTest,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  exact cut_good (slice_correct ok.1.1.1.1 ok.1.1.1.2 (proper_of _ ok.1.1.2) lo) ex.toList ok.1.2 ok.2

theorem certify {T k ws} (cs : Cuts T) (ls : Links T (k-1)) (data : Nat)
    (yes : checkNode T k ws cs ls data = true) : Ex T k ws := node_ok cs ls data yes

def unpack (width dict : Nat) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,data =>
    let i := data % (1 <<< width)
    ((dict >>> (16*i)) % 65536) + ((unpack width dict n (data >>> width)) <<< 16)

abbrev u0 := input 0
abbrev u1 := input 1
abbrev u2 := input 2
abbrev u3 := input 3
abbrev u4 := input 4
abbrev u5 := input 5
abbrev v6 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
abbrev v7 : Sig := 0x88888888888888888888888888888888
abbrev v8 : Sig := 0xf2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2
abbrev v9 : Sig := 0xd0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0
abbrev v10 : Sig := 0x22222222222222222222222222222222
abbrev v11 : Sig := 0xf4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4
abbrev v12 : Sig := 0xb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0
abbrev v13 : Sig := 0x44444444444444444444444444444444
abbrev v14 : Sig := 0xfafafafafafafafafafafafafafafafa
abbrev v15 : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
abbrev v16 : Sig := 0xcececececececececececececececece
abbrev v17 : Sig := 0xc4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4
abbrev v18 : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
abbrev v19 : Sig := 0xdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdc
abbrev v20 : Sig := 0x8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c
abbrev v21 : Sig := 0x50505050505050505050505050505050
abbrev v22 : Sig := 0xeecceecceecceecceecceecceecceecc
abbrev v23 : Sig := 0x44cc44cc44cc44cc44cc44cc44cc44cc
abbrev v24 : Sig := 0xfaf0faf0faf0faf0faf0faf0faf0faf0
abbrev v25 : Sig := 0x50f050f050f050f050f050f050f050f0
abbrev v26 : Sig := 0xaa00aa00aa00aa00aa00aa00aa00aa00
abbrev v27 : Sig := 0xcc88cc88cc88cc88cc88cc88cc88cc88
abbrev v28 : Sig := 0x33223322332233223322332233223322
abbrev v29 : Sig := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0
abbrev v30 : Sig := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
abbrev v31 : Sig := 0xffaaffaaffaaffaaffaaffaaffaaffaa
abbrev v32 : Sig := 0xaa00aa00aa00aa00aa00aa00aa00aa
abbrev v33 : Sig := 0x55005500550055005500550055005500
abbrev v34 : Sig := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
abbrev v35 : Sig := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
abbrev v36 : Sig := 0xaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeae
abbrev v37 : Sig := 0xa2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2
abbrev v38 : Sig := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
abbrev v39 : Sig := 0xbabababababababababababababababa
abbrev v40 : Sig := 0x8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a
abbrev v41 : Sig := 0x30303030303030303030303030303030
abbrev v42 : Sig := 0xfcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0
abbrev v43 : Sig := 0x30f030f030f030f030f030f030f030f0
abbrev v44 : Sig := 0xeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaa
abbrev v45 : Sig := 0x22aa22aa22aa22aa22aa22aa22aa22aa
abbrev v46 : Sig := 0xcc00cc00cc00cc00cc00cc00cc00cc00
abbrev v47 : Sig := 0xaa88aa88aa88aa88aa88aa88aa88aa88
abbrev v48 : Sig := 0x55445544554455445544554455445544
abbrev v49 : Sig := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0
abbrev v50 : Sig := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c
abbrev v51 : Sig := 0xffccffccffccffccffccffccffccffcc
abbrev v52 : Sig := 0xcc00cc00cc00cc00cc00cc00cc00cc
abbrev v53 : Sig := 0x33003300330033003300330033003300
abbrev v54 : Sig := 0xfaaafaaafaaafaaafaaafaaafaaafaaa
abbrev v55 : Sig := 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa
abbrev v56 : Sig := 0xfcccfcccfcccfcccfcccfcccfcccfccc
abbrev v57 : Sig := 0xccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc
abbrev v58 : Sig := 0xf000f000f000f000f000f000f000f000
abbrev v59 : Sig := 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0
abbrev v60 : Sig := 0x55505550555055505550555055505550
abbrev v61 : Sig := 0xccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0
abbrev v62 : Sig := 0x33303330333033303330333033303330
abbrev v63 : Sig := 0xfff0fff0fff0fff0fff0fff0fff0fff0
abbrev v64 : Sig := 0xf000f000f000f000f000f000f000f0
abbrev v65 : Sig := 0xf000f000f000f000f000f000f000f00
abbrev v66 : Sig := 0xfe00fe00fe00fe00fe00fe00fe00fe
abbrev v67 : Sig := 0xfefefefefefefefefefefefefefefefe
abbrev v68 : Sig := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
abbrev v69 : Sig := 0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e
abbrev v70 : Sig := 0xffeeffeeffeeffeeffeeffeeffeeffee
abbrev v71 : Sig := 0xee00ee00ee00ee00ee00ee00ee00ee
abbrev v72 : Sig := 0x33323332333233323332333233323332
abbrev v73 : Sig := 0xfffafffafffafffafffafffafffafffa
abbrev v74 : Sig := 0xfa00fa00fa00fa00fa00fa00fa00fa
abbrev v75 : Sig := 0x32323232323232323232323232323232
abbrev v76 : Sig := 0x55545554555455545554555455545554
abbrev v77 : Sig := 0xfffcfffcfffcfffcfffcfffcfffcfffc
abbrev v78 : Sig := 0xfc00fc00fc00fc00fc00fc00fc00fc
abbrev v79 : Sig := 0x54545454545454545454545454545454
abbrev v80 : Sig := 0xeeeecccceeeecccceeeecccceeeecccc
abbrev v81 : Sig := 0x4444cccc4444cccc4444cccc4444cccc
abbrev v82 : Sig := 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0
abbrev v83 : Sig := 0x5050f0f05050f0f05050f0f05050f0f0
abbrev v84 : Sig := 0xaaaa0000aaaa0000aaaa0000aaaa0000
abbrev v85 : Sig := 0xcccc8888cccc8888cccc8888cccc8888
abbrev v86 : Sig := 0x33332222333322223333222233332222
abbrev v87 : Sig := 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0
abbrev v88 : Sig := 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a
abbrev v89 : Sig := 0xffffaaaaffffaaaaffffaaaaffffaaaa
abbrev v90 : Sig := 0xaaaa0000aaaa0000aaaa0000aaaa
abbrev v91 : Sig := 0x55550000555500005555000055550000
abbrev v92 : Sig := 0xfcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0
abbrev v93 : Sig := 0x3030f0f03030f0f03030f0f03030f0f0
abbrev v94 : Sig := 0xeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaa
abbrev v95 : Sig := 0x2222aaaa2222aaaa2222aaaa2222aaaa
abbrev v96 : Sig := 0xcccc0000cccc0000cccc0000cccc0000
abbrev v97 : Sig := 0xaaaa8888aaaa8888aaaa8888aaaa8888
abbrev v98 : Sig := 0x55554444555544445555444455554444
abbrev v99 : Sig := 0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0
abbrev v100 : Sig := 0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c
abbrev v101 : Sig := 0xffffccccffffccccffffccccffffcccc
abbrev v102 : Sig := 0xcccc0000cccc0000cccc0000cccc
abbrev v103 : Sig := 0x33330000333300003333000033330000
abbrev v104 : Sig := 0xfafaaaaafafaaaaafafaaaaafafaaaaa
abbrev v105 : Sig := 0xa0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa
abbrev v106 : Sig := 0xfcfcccccfcfcccccfcfcccccfcfccccc
abbrev v107 : Sig := 0xc0ccccc0c0ccccc0c0ccccc0c0ccccc
abbrev v108 : Sig := 0xf0f00000f0f00000f0f00000f0f00000
abbrev v109 : Sig := 0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0
abbrev v110 : Sig := 0x55555050555550505555505055555050
abbrev v111 : Sig := 0xccccc0c0ccccc0c0ccccc0c0ccccc0c0
abbrev v112 : Sig := 0x33333030333330303333303033333030
abbrev v113 : Sig := 0xfffff0f0fffff0f0fffff0f0fffff0f0
abbrev v114 : Sig := 0xf0f00000f0f00000f0f00000f0f0
abbrev v115 : Sig := 0xf0f00000f0f00000f0f00000f0f0000
abbrev v116 : Sig := 0x7f7f00007f7f00007f7f00007f7f0000
abbrev v117 : Sig := 0x80808080808080808080808080808080
abbrev v118 : Sig := 0x70707070707070707070707070707070
abbrev v119 : Sig := 0x7070f0f07070f0f07070f0f07070f0f0
abbrev v120 : Sig := 0x88880000888800008888000088880000
abbrev v121 : Sig := 0x77770000777700007777000077770000
abbrev v122 : Sig := 0x4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c
abbrev v123 : Sig := 0x4c4ccccc4c4ccccc4c4ccccc4c4ccccc
abbrev v124 : Sig := 0xa0a00000a0a00000a0a00000a0a00000
abbrev v125 : Sig := 0x5f5f00005f5f00005f5f00005f5f0000
abbrev v126 : Sig := 0x2a2aaaaa2a2aaaaa2a2aaaaa2a2aaaaa
abbrev v127 : Sig := 0xc0c00000c0c00000c0c00000c0c00000
abbrev v128 : Sig := 0x3f3f00003f3f00003f3f00003f3f0000
abbrev v129 : Sig := 0x2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a
abbrev v130 : Sig := 0x7f7f7f7f000000007f7f7f7f00000000
abbrev v131 : Sig := 0x70707070f0f0f0f070707070f0f0f0f0
abbrev v132 : Sig := 0x88888888000000008888888800000000
abbrev v133 : Sig := 0x77777777000000007777777700000000
abbrev v134 : Sig := 0xcccccccc00000000cccccccc00000000
abbrev v135 : Sig := 0xaaaaaaaa00000000aaaaaaaa00000000
abbrev v136 : Sig := 0x4c4c4c4ccccccccc4c4c4c4ccccccccc
abbrev v137 : Sig := 0xa0a0a0a000000000a0a0a0a000000000
abbrev v138 : Sig := 0x5f5f5f5f000000005f5f5f5f00000000
abbrev v139 : Sig := 0xf0f0f0f000000000f0f0f0f000000000
abbrev v140 : Sig := 0x44444444cccccccc44444444cccccccc
abbrev v141 : Sig := 0x50505050f0f0f0f050505050f0f0f0f0
abbrev v142 : Sig := 0x2a2a2a2aaaaaaaaa2a2a2a2aaaaaaaaa
abbrev v143 : Sig := 0xc0c0c0c000000000c0c0c0c000000000
abbrev v144 : Sig := 0x3f3f3f3f000000003f3f3f3f00000000
abbrev v145 : Sig := 0x30303030f0f0f0f030303030f0f0f0f0
abbrev v146 : Sig := 0x22222222aaaaaaaa22222222aaaaaaaa
abbrev v147 : Sig := 0xa0a0a0aaaaaaaaa0a0a0a0aaaaaaaaa
abbrev v148 : Sig := 0xc0c0c0ccccccccc0c0c0c0ccccccccc
abbrev v149 : Sig := 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8
abbrev v150 : Sig := 0x8080808080808080808080808080808
abbrev v151 : Sig := 0x66666666666666666666666666666666
abbrev v152 : Sig := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0
abbrev v153 : Sig := 0x10101010101010101010101010101010
abbrev v154 : Sig := 0x20202020202020202020202020202020
abbrev v155 : Sig := 0x2020202020202020202020202020202
abbrev v156 : Sig := 0x40404040404040404040404040404040
abbrev v157 : Sig := 0x4040404040404040404040404040404
abbrev v158 : Sig := 0xecececececececececececececececec
abbrev v159 : Sig := 0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a
abbrev v160 : Sig := 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8
abbrev v161 : Sig := 0xcceecceecceecceecceecceecceeccee
abbrev v162 : Sig := 0xcc44cc44cc44cc44cc44cc44cc44cc44
abbrev v163 : Sig := 0xf0faf0faf0faf0faf0faf0faf0faf0fa
abbrev v164 : Sig := 0xf050f050f050f050f050f050f050f050
abbrev v165 : Sig := 0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c
abbrev v166 : Sig := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
abbrev v167 : Sig := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
abbrev v168 : Sig := 0xaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaee
abbrev v169 : Sig := 0xaa22aa22aa22aa22aa22aa22aa22aa22
abbrev v170 : Sig := 0xf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fc
abbrev v171 : Sig := 0xf030f030f030f030f030f030f030f030
abbrev v172 : Sig := 0xaafaaafaaafaaafaaafaaafaaafaaafa
abbrev v173 : Sig := 0xaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0a
abbrev v174 : Sig := 0xccfcccfcccfcccfcccfcccfcccfcccfc
abbrev v175 : Sig := 0xcc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0c

abbrev t38 : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c38 : Cuts t38 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p38x0 : Ex t38 3 (roots 7) :=
  certify c38 [] (unpack 3 0x28103020182018103040284 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l38 : CClaim 7 t38 4 := fromTable 16514 (by decide +kernel) p38x0

abbrev t41 : Sig := 0xee88ee88ee88ee88ee88ee88ee88ee88
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c41 : Cuts t41 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p41x0 : Ex t41 3 (roots 11) :=
  certify c41 [] (unpack 3 0x48105020182018105080488 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l41 : CClaim 11 t41 4 := fromTable 2097282 (by decide +kernel) p41x0

abbrev t45 : Sig := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c45 : Cuts t45 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p45x0 : Ex t45 3 (roots 13) :=
  certify c45 [] (unpack 3 0x48106040284028106080488 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l45 : CClaim 13 t45 4 := fromTable 2113540 (by decide +kernel) p45x0

abbrev t49 : Sig := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c49 : Cuts t49 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p49x0 : Ex t49 3 (roots 14) :=
  certify c49 [] (unpack 3 0x50206040304030206080508 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l49 : CClaim 14 t49 4 := fromTable 4227584 (by decide +kernel) p49x0

abbrev t54 : Sig := 0xeeee8888eeee8888eeee8888eeee8888
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c54 : Cuts t54 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p54x0 : Ex t54 3 (roots 19) :=
  certify c54 [] (unpack 3 0x88109020182018109100890 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l54 : CClaim 19 t54 4 := fromTable 268435586 (by decide +kernel) p54x0

abbrev t58 : Sig := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c58 : Cuts t58 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p58x0 : Ex t58 3 (roots 21) :=
  certify c58 [] (unpack 3 0x8810a04028402810a100890 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l58 : CClaim 21 t58 4 := fromTable 268451844 (by decide +kernel) p58x0

abbrev t62 : Sig := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c62 : Cuts t62 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p62x0 : Ex t62 3 (roots 22) :=
  certify c62 [] (unpack 3 0x9020a04030403020a100910 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l62 : CClaim 22 t62 4 := fromTable 536904192 (by decide +kernel) p62x0

abbrev t78 : Sig := 0xeeeeeeee88888888eeeeeeee88888888
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c78 : Cuts t78 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p78x0 : Ex t78 3 (roots 35) :=
  certify c78 [] (unpack 3 0x1081110201820181112010a0 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l78 : CClaim 35 t78 4 := fromTable 34359738498 (by decide +kernel) p78x0

abbrev t82 : Sig := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c82 : Cuts t82 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p82x0 : Ex t82 3 (roots 37) :=
  certify c82 [] (unpack 3 0x1081120402840281122010a0 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l82 : CClaim 37 t82 4 := fromTable 34359754756 (by decide +kernel) p82x0

abbrev t86 : Sig := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c86 : Cuts t86 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p86x0 : Ex t86 3 (roots 38) :=
  certify c86 [] (unpack 3 0x110212040304030212201120 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l86 : CClaim 38 t86 4 := fromTable 68719510016 (by decide +kernel) p86x0

abbrev t112 : Sig := 0xffffff00ff000000ffffff00ff000000
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c112 : Cuts t112 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x0 : Ex t112 3 (roots 56) :=
  certify c112 [] (unpack 3 0x140818100c100c0818201420 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l112 : CClaim 56 t112 4 := fromTable 277058945024 (by decide +kernel) p112x0

abbrev t113 : Sig := 0xfe80fe80fe80fe80fe80fe80fe80fe80
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c113 : Cuts t113 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x0 : Ex t113 3 [v6,v7,u2,u3] :=
  certify c113 [] (unpack 3 0x583038404810604060803830488 21 0x38e69a14558e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x1 : Ex t113 4 [v7,u0,u1,u2,u3] :=
  certify c113 [⟨_,p113x0⟩] (unpack 4 0x6040502048805088000058304810383060803850386 33 0xa4a494947237494982388765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x2 : Ex t113 4 [v6,u0,u1,u2,u3] :=
  certify c113 [⟨_,p113x0⟩] (unpack 4 0x508050203850386800004880481060403830608 33 0x232383831010938381010765432321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x3 : Ex t113 3 [v8,u0,u1,u3] :=
  certify c113 [] (unpack 3 0x385050804880383060804810502 24 0x41a9d208d7591a208) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x4 : Ex t113 3 [v9,u0,u1,u3] :=
  certify c113 [] (unpack 3 0x5020508038606080383048806040481 24 0xe38d1e1c75aa51a208) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x5 : Ex t113 4 [v10,u0,u1,u2,u3] :=
  certify c113 [⟨_,p113x3⟩,⟨_,p113x4⟩] (unpack 4 0x60403830384038605080481050280018000060803850488 33 0xb6b6565672a76565a2a29876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x6 : Ex t113 3 [v11,u0,u1,u3] :=
  certify c113 [] (unpack 3 0x5080386038506080383048805020481 24 0x208fdc0415aa51a208) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x7 : Ex t113 3 [v12,u0,u1,u3] :=
  certify c113 [] (unpack 3 0x5020385048806040481060803830508 24 0xefb7dfa35a8d8e3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x8 : Ex t113 4 [v13,u0,u1,u2,u3] :=
  certify c113 [⟨_,p113x6⟩,⟨_,p113x7⟩] (unpack 4 0x60403830384038504880502048180018000060805080386 33 0xb5b56565a2a2565672a79876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x9 : Ex t113 3 [v14,v15,u1,u3] :=
  certify c113 [] (unpack 3 0x4880685038503830508038204810502 21 0x20bf7c38d71a208) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x10 : Ex t113 4 [v15,u0,u2,u1,u3] :=
  certify c113 [⟨_,p113x9⟩] (unpack 4 0x6040502048806088000068504810385050803830386 33 0x94942732a4a4494982388765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x11 : Ex t113 4 [v14,u0,u2,u1,u3] :=
  certify c113 [⟨_,p113x9⟩] (unpack 4 0x604060803850508038303868000048804810502 33 0x10167566776919181010767654321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x12 : Ex t113 3 [v16,u0,u2,u3] :=
  certify c113 [] (unpack 3 0x5020488038504810604060803830508 24 0x71c9e728ada88e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x13 : Ex t113 3 [v17,u0,u2,u3] :=
  certify c113 [] (unpack 3 0x6040386048805020481060803850508 24 0xefb71cab5a0d8e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x14 : Ex t113 4 [v18,u0,u2,u1,u3] :=
  certify c113 [⟨_,p113x12⟩,⟨_,p113x13⟩] (unpack 4 0x60403850382038606080481050280018000050803830488 33 0x565627a2b6b66565a2a29876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x15 : Ex t113 3 [v19,u0,u2,u3] :=
  certify c113 [] (unpack 4 0x60403860385048805020481060803830508 24 0x838334345715506543430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x16 : Ex t113 3 [v20,u0,u2,u3] :=
  certify c113 [] (unpack 3 0x6040502048106080383050803850488 24 0xf7dbae118d7551a408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x17 : Ex t113 4 [v21,u0,u2,u1,u3] :=
  certify c113 [⟨_,p113x15⟩,⟨_,p113x16⟩] (unpack 4 0x50203850382038304880604048180018000050806080386 33 0xb5b52a8265655b5b72a79876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x18 : Ex t113 3 [v22,u0,u3,u2] :=
  certify c113 [] (unpack 4 0x58304880385060803830508048105020604 24 0x10145458181776335432210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x19 : Ex t113 3 [v23,u0,u3,u2] :=
  certify c113 [] (unpack 3 0x6040608038305020481050803850488 24 0xefb1a871c5aa8e3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x20 : Ex t113 3 [v24,u0,u3,u1] :=
  certify c113 [] (unpack 4 0x38505080685048803830608048106040502 24 0x10173478787606055432210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x21 : Ex t113 3 [v25,u0,u3,u1] :=
  certify c113 [] (unpack 3 0x3850502050806040481060803830488 24 0xcf317879e54d8e3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x22 : Ex t113 4 [v26,u0,u3,u1,u2] :=
  certify c113 [⟨_,p113x18⟩,⟨_,p113x19⟩,⟨_,p113x20⟩,⟨_,p113x21⟩] (unpack 4 0x6040383038503860502050380038002060880018000050804810488 33 0xd9d925c29d9dc5c5b2b2a987565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x23 : Ex t113 3 [v27,u0,u3,u2] :=
  certify c113 [] (unpack 3 0x6040385048806080383050205080481 24 0xe38b1d1c7a75319408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x24 : Ex t113 3 [v28,u0,u3,u2] :=
  certify c113 [] (unpack 3 0x383060804810502038504880508 24 0xd2c3718e31a88e3288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x25 : Ex t113 3 [v29,u0,u3,u1] :=
  certify c113 [] (unpack 3 0x5080385050203830488060406080481 24 0xa28e677f3145663408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x26 : Ex t113 3 [v30,u0,u3,u1] :=
  certify c113 [] (unpack 4 0x58303850508050204810604038304880608 24 0x846416714343626045431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x27 : Ex t113 4 [v31,u0,u3,u1,u2] :=
  certify c113 [⟨_,p113x23⟩,⟨_,p113x24⟩,⟨_,p113x25⟩,⟨_,p113x26⟩] (unpack 4 0x80038002058380018000050206080383050803850481048805030386 33 0x6373d77c5765b353a5598276225423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x28 : Ex t113 4 [v32,u0,u3,u1,u2] :=
  certify c113 [] (unpack 4 0x604048004880502038306080385050804810386 33 0x969624526969745772378765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x29 : Ex t113 4 [v33,u0,u3,u1,u2] :=
  certify c113 [] (unpack 4 0x583048004810386060803830508038505020488 33 0x475735439737454523238765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x30 : Ex t113 3 [v34,v35,u0,u3] :=
  certify c113 [] (unpack 3 0x5080386048803830706038105020481 21 0x20dd2dfac0c2208) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x31 : Ex t113 4 [v35,u1,u2,u0,u3] :=
  certify c113 [⟨_,p113x30⟩] (unpack 4 0x3860488060405020508060880000706048103830385 33 0x272795a996a99aa982827272654323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x32 : Ex t113 4 [v34,u1,u2,u0,u3] :=
  certify c113 [⟨_,p113x30⟩] (unpack 4 0x386048806040608038303858000050805020481 33 0x10189588948899870706101054321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x33 : Ex t113 3 [v36,u1,u2,u3] :=
  certify c113 [] (unpack 3 0x5020481060406080383050803850488 24 0xbaefbe71cd75118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x34 : Ex t113 3 [v37,u1,u2,u3] :=
  certify c113 [] (unpack 3 0x6040481050206080386050803850488 24 0xfbebae50ad75118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x35 : Ex t113 4 [v38,u1,u2,u0,u3] :=
  certify c113 [⟨_,p113x33⟩,⟨_,p113x34⟩] (unpack 4 0x38606040381038506080502048180018000048803830508 33 0x565627b22b82a5a565659876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x36 : Ex t113 3 [v39,u1,u2,u3] :=
  certify c113 [] (unpack 3 0x6040481050206080383050803850488 24 0xfbebae45ad75118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x37 : Ex t113 3 [v40,u1,u2,u3] :=
  certify c113 [] (unpack 3 0x6040481050206080383050803860488 24 0xfbebae51ad75118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x38 : Ex t113 4 [v41,u1,u2,u0,u3] :=
  certify c113 [⟨_,p113x36⟩,⟨_,p113x37⟩] (unpack 4 0x38605020381038305080604048180018000048806080385 33 0x5a5a2b8227b26565a5a59876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x39 : Ex t113 3 [v42,u1,u3,u0] :=
  certify c113 [] (unpack 4 0x386048803850706050803830608050206040481 24 0x10189788348706055432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x40 : Ex t113 3 [v43,u1,u3,u0] :=
  certify c113 [] (unpack 3 0x3850502048806040481060803830508 24 0x79ea3dcf354d8e3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x41 : Ex t113 3 [v44,u1,u3,u2] :=
  certify c113 [] (unpack 4 0x58305080385060803830488050204810604 24 0x10145458181736335431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x42 : Ex t113 3 [v45,u1,u3,u2] :=
  certify c113 [] (unpack 3 0x6040608038304810502050803850488 24 0xf3c5aa71c1a88e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x43 : Ex t113 4 [v46,u1,u3,u0,u2] :=
  certify c113 [⟨_,p113x39⟩,⟨_,p113x40⟩,⟨_,p113x41⟩,⟨_,p113x42⟩] (unpack 4 0x6040386800380020488038303850481048380018000060805020508 33 0xd6d692896d6d9c799ba98282765423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x44 : Ex t113 3 [v47,u1,u3,u2] :=
  certify c113 [] (unpack 3 0x6040608038304810502050803860488 24 0xefb5aa7df1a8903088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x45 : Ex t113 3 [v48,u1,u3,u2] :=
  certify c113 [] (unpack 3 0x383060805020481038505080488 24 0xceb3718e31a88e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x46 : Ex t113 3 [v49,u1,u3,u0] :=
  certify c113 [] (unpack 3 0x3860488050203830508060406080481 24 0x145cfec66a28663408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x47 : Ex t113 3 [v50,u1,u3,u0] :=
  certify c113 [] (unpack 4 0x58303850488048105020604038305080608 24 0x846461764343626055431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x48 : Ex t113 4 [v51,u1,u3,u0,u2] :=
  certify c113 [⟨_,p113x44⟩,⟨_,p113x45⟩,⟨_,p113x46⟩,⟨_,p113x47⟩] (unpack 4 0x80038002058303868001048880000481060803830502050804830385 33 0x4353d55c8548b38382a89887625423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x49 : Ex t113 4 [v52,u1,u3,u0,u2] :=
  certify c113 [] (unpack 4 0x604050005080481038306080386048805020385 33 0x969624526969273274578765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x50 : Ex t113 4 [v53,u1,u3,u0,u2] :=
  certify c113 [] (unpack 4 0x583050005020385060803830488038604810508 33 0x475735439737326345458765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x51 : Ex t113 3 [v54,u2,u3,u1] :=
  certify c113 [] (unpack 3 0x5080385068506080383048804810502 24 0x41f9feb266989a208) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x52 : Ex t113 3 [v55,u2,u3,u1] :=
  certify c113 [] (unpack 3 0x6040508038504810502060803830488 24 0x71cc8ef3c1a88e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x53 : Ex t113 3 [v56,u2,u3,u0] :=
  certify c113 [] (unpack 4 0x38603850488070606080383050805020481 24 0x10168366276305042321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x54 : Ex t113 3 [v57,u2,u3,u0] :=
  certify c113 [] (unpack 3 0x6040385048805020481060803830508 24 0x71ca8defb1758e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x55 : Ex t113 4 [v58,u2,u3,u0,u1] :=
  certify c113 [⟨_,p113x51⟩,⟨_,p113x52⟩,⟨_,p113x53⟩,⟨_,p113x54⟩] (unpack 4 0x80038002050803850502038680018000048803830481048506040608 33 0x9393ba4bbdcb5ba539395845576543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x56 : Ex t113 3 [v59,u2,u3,u1] :=
  certify c113 [] (unpack 3 0x6040508038504810502060803860488 24 0x7dfcaeefb1a8903088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x57 : Ex t113 3 [v60,u2,u3,u1] :=
  certify c113 [] (unpack 4 0x58303850508050206040481038306080488 24 0x836361264343076053430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x58 : Ex t113 3 [v61,u2,u3,u0] :=
  certify c113 [] (unpack 3 0x3860488060405020481060803850508 24 0x75dcbec0eaeb8c3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x59 : Ex t113 3 [v62,u2,u3,u0] :=
  certify c113 [] (unpack 4 0x58303850488048106040502038306080508 24 0x836361264343676055430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x60 : Ex t113 4 [v63,u2,u3,u0,u1] :=
  certify c113 [⟨_,p113x56⟩,⟨_,p113x57⟩,⟨_,p113x58⟩,⟨_,p113x59⟩] (unpack 4 0x80038002050803850685038680010488800004810604060804850383 33 0xa3b3b2abdbbc6ba693636286766543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x61 : Ex t113 4 [v64,u2,u3,u0,u1] :=
  certify c113 [] (unpack 4 0x502060006080481038505080386048806040383 33 0x969647542452696927328765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x62 : Ex t113 4 [v65,u2,u3,u0,u1] :=
  certify c113 [] (unpack 4 0x685060006040383050803850488038604810608 33 0x475754653543973732638765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x63 : Ex t113 5 (roots 15) :=
  certify c113 [⟨_,p113x1⟩,⟨_,p113x2⟩,⟨_,p113x5⟩,⟨_,p113x8⟩,⟨_,p113x10⟩,⟨_,p113x11⟩,⟨_,p113x14⟩,⟨_,p113x17⟩,⟨_,p113x22⟩,⟨_,p113x27⟩,⟨_,p113x28⟩,⟨_,p113x29⟩,⟨_,p113x31⟩,⟨_,p113x32⟩,⟨_,p113x35⟩,⟨_,p113x38⟩,⟨_,p113x43⟩,⟨_,p113x48⟩,⟨_,p113x49⟩,⟨_,p113x50⟩,⟨_,p113x55⟩,⟨_,p113x60⟩,⟨_,p113x61⟩,⟨_,p113x62⟩] (unpack 6 0x801780168015060480148013801280118010800f800e800d800c800b800a800904818008050280078006800503838004060880038002800103860385800005080488 96 0x81d29d7d021079d21d7102906ce0ce69005064e04e6100d05ca0415880c854a0ca5080414d011048e00e4500103ce10e34a0003081082ca10a2480001c3000181101143103081000) (by decide +kernel)
theorem l113 : CClaim 15 t113 6 := fromTable 2146950 (by decide +kernel) p113x63

abbrev t114 : Sig := 0xfee8fee8fee8fee8fee8fee8fee8fee8
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c114 : Cuts t114 := [
  rule t114 0 l45 none (by decide +kernel),
  rule t114 0 l41 none (by decide +kernel),
  rule t114 0 l38 none (by decide +kernel),
  rule t114 0 l49 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x0 : Ex t114 3 [v66,u2,u0,u1] :=
  certify c114 [] (unpack 3 0x2840302018101820502060402810481 24 0xa75b2f38cae8803288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x1 : Ex t114 4 [v67,u2,u0,u1,u3] :=
  certify c114 [⟨_,p114x0⟩] (unpack 4 0x508050201810284030201820488060402810608800004814002 31 0xa1baa48ac1b17a7a948476415431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x2 : Ex t114 4 [v68,u2,u0,u1,u3] :=
  certify c114 [] (unpack 3 0x5020481060401810304018202840281 37 0x4de46e6f9450a255d76bac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x3 : Ex t114 3 [v69,u3,u0,u1] :=
  certify c114 [] (unpack 3 0x2840502018101820302060404810281 24 0xa75b2f38cae8803088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x4 : Ex t114 4 [v70,u3,u0,u1,u2] :=
  certify c114 [⟨_,p114x3⟩] (unpack 4 0x608800040010304030202810181048805020481018202840604 31 0x73c7b77a67866346978726265343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x5 : Ex t114 4 [v71,u3,u0,u1,u2] :=
  certify c114 [] (unpack 4 0x3020604028106080304018105080284018204880481 37 0x879858a559458a82525129128787565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x6 : Ex t114 3 [v34,v14,v6,u3] :=
  certify c114 [] (unpack 3 0x6040284400101824000048105020181 24 0x5d69a5185454103088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x7 : Ex t114 4 [v14,u2,v6,u1,u3] :=
  certify c114 [⟨_,p114x6⟩] (unpack 4 0x30480000181400002844001060402810302050204810182 34 0x9129b94a90998151747460706415431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x8 : Ex t114 3 [v51,v31,v6,u2] :=
  certify c114 [] (unpack 4 0x302060802810488028403044002018201814000 24 0x977271917876252314131210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x9 : Ex t114 4 [v31,u3,v6,u1,u2] :=
  certify c114 [⟨_,p114x8⟩] (unpack 4 0x302030480000181400006080281048804810284018240020502 34 0x6476c66296c9b94a929986765454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x10 : Ex t114 4 [v34,u2,v6,u0,u3] :=
  certify c114 [⟨_,p114x6⟩] (unpack 4 0x28480000182400303044001030206040281048105020181 34 0x2129b95a90908242757560706524230210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x11 : Ex t114 4 [v51,u3,v6,u0,u2] :=
  certify c114 [⟨_,p114x8⟩] (unpack 4 0x302028480000182400306080281050805020304018140020481 34 0x647662c26c69b94a929286765454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x12 : Ex t114 5 [v6,u0,u1,u2,u3] :=
  certify c114 [⟨_,p114x1⟩,⟨_,p114x2⟩,⟨_,p114x4⟩,⟨_,p114x5⟩,⟨_,p114x7⟩,⟨_,p114x9⟩,⟨_,p114x10⟩,⟨_,p114x11⟩] (unpack 5 0x8007800603048005050280040302018140030182400002848003800204814002060480018000028140010608 99 0x1442380e5014e2145ce3acf1ac4ee73dce12c4fa3c4e72db33b0f16c4f23c58c1304f6bc5013d8c72dcd6316b5ad6a398e5494e8394c5104402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x13 : Ex t114 3 [v72,u3,u0,u2] :=
  certify c114 [] (unpack 3 0x6040302028102840182050204810181 24 0xa7dbab28b1a8803088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x14 : Ex t114 4 [v73,u3,u0,u2,u1] :=
  certify c114 [⟨_,p114x13⟩] (unpack 4 0x508800040000302030401810281048806040481028401820502 31 0x768773c7b77a6346978726265343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x15 : Ex t114 4 [v74,u3,u0,u2,u1] :=
  certify c114 [] (unpack 4 0x3040502018105080302028106080182028404880481 37 0x85a8879859458a82525129198787565433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x16 : Ex t114 3 [v63,v31,v14,u1] :=
  certify c114 [] (unpack 4 0x5080488030401810182028403024002050202814001 24 0xa77987757187665314131210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x17 : Ex t114 4 [v31,u3,v14,u2,u1] :=
  certify c114 [⟨_,p114x16⟩] (unpack 4 0x508030401810302800002814001048804810182028440020502 34 0xa7bacaa5a4cabaa2974872776454133210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x18 : Ex t114 4 [v63,u3,v14,u0,u1] :=
  certify c114 [⟨_,p114x16⟩] (unpack 4 0x508030401810182800002844003060806040302028140020481 34 0xcaaca4caa2baaba7974872726454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x19 : Ex t114 4 [v75,u1,u0,u2,u3] :=
  certify c114 [] (unpack 3 0x6040481050202810302028401820181 37 0x4de6b8c70a255d738e6bac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x20 : Ex t114 4 [v34,u1,v14,u0,u3] :=
  certify c114 [⟨_,p114x6⟩] (unpack 4 0x1828000028440030304030240000181048105020281 34 0x2121a86980807212505041212565430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x21 : Ex t114 5 [v14,u0,u2,u1,u3] :=
  certify c114 [⟨_,p114x14⟩,⟨_,p114x15⟩,⟨_,p114x7⟩,⟨_,p114x17⟩,⟨_,p114x18⟩,⟨_,p114x1⟩,⟨_,p114x19⟩,⟨_,p114x20⟩] (unpack 5 0x8007800680054000050880040604030280038002018103040281400302844001018280018000048140020502 99 0x16b144408804b5996b4a9355292b5d23192d735ae518bd291184f83c494990e11c404004d100e059d6a4296c5a8e74992839cc6318c5104402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x22 : Ex t114 4 [v28,u1,u0,u3,u2] :=
  certify c114 [] (unpack 4 0x608030402810302048105020284048801820181 37 0x7597767154512118676745457676545431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x23 : Ex t114 4 [v51,u1,v31,u0,u2] :=
  certify c114 [⟨_,p114x8⟩] (unpack 4 0x1828000048840030481030202810508050240000181 34 0x544546544545a839868676261545423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x24 : Ex t114 4 [v30,u2,u0,u3,u1] :=
  certify c114 [] (unpack 4 0x5080302018103040502048106040182048802840281 37 0x85a8879887815451291995458787565433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x25 : Ex t114 4 [v63,u2,v31,u0,u1] :=
  certify c114 [⟨_,p114x16⟩] (unpack 4 0x18103040182800004884003050204810608060440010281 34 0xabbabaabb4abbaba973874746454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x26 : Ex t114 5 [v31,u0,u3,u1,u2] :=
  certify c114 [⟨_,p114x9⟩,⟨_,p114x17⟩,⟨_,p114x4⟩,⟨_,p114x22⟩,⟨_,p114x23⟩,⟨_,p114x14⟩,⟨_,p114x24⟩,⟨_,p114x25⟩] (unpack 5 0x8007060880068005400180040508800380024000050280010281030280000181030404814003048840020182 99 0x52925095a50894cd088a5324a628420c6495282a126304c623c907bc86338a5618cd319852846b489281a12a4a048308c5194c731445204831082108420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x27 : Ex t114 3 [v76,u3,u1,u2] :=
  certify c114 [] (unpack 3 0x6040302028102840181018205020481 24 0xa3d77360b5758d3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x28 : Ex t114 4 [v77,u3,u1,u2,u0] :=
  certify c114 [⟨_,p114x27⟩] (unpack 4 0x284048880000182400302810302050806040502030401810481 31 0x96c9c99c93b9a998634676265343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x29 : Ex t114 4 [v78,u3,u1,u2,u0] :=
  certify c114 [] (unpack 4 0x2840481018204880281030206080181030405080502 37 0x85a8a88a97985949525129198787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x30 : Ex t114 3 [v63,v51,v34,u0] :=
  certify c114 [] (unpack 4 0x488028401820181030402814002048103024001 24 0x977987787187665344132210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x31 : Ex t114 4 [v51,u3,v34,u2,u0] :=
  certify c114 [⟨_,p114x30⟩] (unpack 4 0x488018202840281800003024001050805020181030440020481 34 0xb7abcbbcb4cbabba974872776454133210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x32 : Ex t114 4 [v63,u3,v34,u1,u0] :=
  certify c114 [⟨_,p114x30⟩] (unpack 4 0x488028401820181800003044000060806040281030240020481 34 0xbaabcaaca4caa2ba974872726454133210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x33 : Ex t114 4 [v79,u0,u1,u2,u3] :=
  certify c114 [] (unpack 3 0x6040502048103020281030401810182 37 0x3bd9b8970dd738e1456bac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x34 : Ex t114 5 [v34,u1,u2,u0,u3] :=
  certify c114 [⟨_,p114x28⟩,⟨_,p114x29⟩,⟨_,p114x31⟩,⟨_,p114x32⟩,⟨_,p114x1⟩,⟨_,p114x33⟩,⟨_,p114x10⟩,⟨_,p114x20⟩] (unpack 5 0x8007800602848005800401824003048880030604028180020302400003044001018180018000050240020481 99 0x200138407005081a104cd359cd30822733c214840f39c9ce7c211841ee731290180c6b0090190b11c404004a100e04992839cc6318c5104402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x35 : Ex t114 4 [v48,u0,u1,u3,u2] :=
  certify c114 [] (unpack 4 0x608028403020281050204810304050801810182 37 0x6496167114516767454512187676545431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x36 : Ex t114 4 [v50,u2,u1,u3,u0] :=
  certify c114 [] (unpack 4 0x4880281018202840481050206040181050803040302 37 0x85a8788797985451291995498787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x37 : Ex t114 4 [v63,u2,v51,u1,u0] :=
  certify c114 [⟨_,p114x30⟩] (unpack 4 0x28401820181800005084000048105020608060440010281 34 0xbaabbaababbaa4ba973874746554123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x38 : Ex t114 5 [v51,u1,u3,u0,u2] :=
  certify c114 [⟨_,p114x31⟩,⟨_,p114x4⟩,⟨_,p114x35⟩,⟨_,p114x11⟩,⟨_,p114x23⟩,⟨_,p114x28⟩,⟨_,p114x36⟩,⟨_,p114x37⟩] (unpack 5 0x8007060880068005400180040488800380028001018240030284048180000302028105024000050840020181 99 0x4a525095a50852cca5898d231a2529565324c5494cb5856b23c907bc8b58d2912d6e5ac494b52952d6c5ad4948468308c5194c731445204831082108420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x39 : Ex t114 4 [v60,u0,u2,u3,u1] :=
  certify c114 [] (unpack 4 0x5080182030401810502060404810302060802810284 37 0x74a7718714517978454912198787645431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x40 : Ex t114 4 [v62,u1,u2,u3,u0] :=
  certify c114 [] (unpack 4 0x4880181028401820481060405020281060803020304 37 0x74a7718797981451954992198787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x41 : Ex t114 5 [v63,u2,u3,u0,u1] :=
  certify c114 [⟨_,p114x14⟩,⟨_,p114x39⟩,⟨_,p114x18⟩,⟨_,p114x25⟩,⟨_,p114x28⟩,⟨_,p114x40⟩,⟨_,p114x32⟩,⟨_,p114x37⟩] (unpack 5 0x8007050880068005800440000181030480030488800280018000028440030182048106044001060840020281 99 0x5ef25095a508f78def139d37384f7c9ef839d173a0f7bd0f718cf33dc8404c62308d6308630cc61210b42046328c63a109420e630465204831082108420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x42 : Ex t114 6 (roots 15) :=
  certify c114 [⟨_,p114x12⟩,⟨_,p114x21⟩,⟨_,p114x26⟩,⟨_,p114x34⟩,⟨_,p114x38⟩,⟨_,p114x41⟩] (unpack 5 0x8005060806048004050880038002048804814002050280010281400103024003800001820181400003040284 96 0x64d294368dace936352962c631362d92e2b6346341c631242981c27424636348d32dcb7b5cd62c844248931c075240941c8410c033048428c8310400) (by decide +kernel)
theorem l114 : CClaim 15 t114 7 := fromTable 2113666 (by decide +kernel) p114x42

abbrev t115 : Sig := 0xfefe8080fefe8080fefe8080fefe8080
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c115 : Cuts t115 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x0 : Ex t115 3 [v6,v7,u2,u4] :=
  certify c115 [] (unpack 3 0x983038408810a040a1003830890 21 0x38e69a14558e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x1 : Ex t115 4 [v7,u0,u1,u2,u4] :=
  certify c115 [⟨_,p115x0⟩] (unpack 4 0xa0409020890091080000983088103830a1003850386 33 0xa4a494947237494982388765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x2 : Ex t115 4 [v6,u0,u1,u2,u4] :=
  certify c115 [⟨_,p115x0⟩] (unpack 4 0x9100902038503868000089008810a0403830a10 33 0x232383831010938381010765432321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x3 : Ex t115 3 [v8,u0,u1,u4] :=
  certify c115 [] (unpack 3 0x3850910089003830a1008810902 24 0x41a9d208d7591a208) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x4 : Ex t115 3 [v9,u0,u1,u4] :=
  certify c115 [] (unpack 3 0x902091003860a10038308900a040881 24 0xe38d1e1c75aa51a208) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x5 : Ex t115 4 [v10,u0,u1,u2,u4] :=
  certify c115 [⟨_,p115x3⟩,⟨_,p115x4⟩] (unpack 4 0xa04038303840386091008810902800180000a1003850890 33 0xb6b6565672a76565a2a29876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x6 : Ex t115 3 [v11,u0,u1,u4] :=
  certify c115 [] (unpack 3 0x910038603850a100383089009020881 24 0x208fdc0415aa51a208) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x7 : Ex t115 3 [v12,u0,u1,u4] :=
  certify c115 [] (unpack 3 0x902038508900a0408810a1003830910 24 0xefb7dfa35a8d8e3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x8 : Ex t115 4 [v13,u0,u1,u2,u4] :=
  certify c115 [⟨_,p115x6⟩,⟨_,p115x7⟩] (unpack 4 0xa04038303840385089009020881800180000a1009100386 33 0xb5b56565a2a2565672a79876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x9 : Ex t115 3 [v14,v15,u1,u4] :=
  certify c115 [] (unpack 3 0x8900a85038503830910038208810902 21 0x20bf7c38d71a208) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x10 : Ex t115 4 [v15,u0,u2,u1,u4] :=
  certify c115 [⟨_,p115x9⟩] (unpack 4 0xa04090208900a1080000a8508810385091003830386 33 0x94942732a4a4494982388765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x11 : Ex t115 4 [v14,u0,u2,u1,u4] :=
  certify c115 [⟨_,p115x9⟩] (unpack 4 0xa040a1003850910038303868000089008810902 33 0x10167566776919181010767654321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x12 : Ex t115 3 [v16,u0,u2,u4] :=
  certify c115 [] (unpack 3 0x9020890038508810a040a1003830910 24 0x71c9e728ada88e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x13 : Ex t115 3 [v17,u0,u2,u4] :=
  certify c115 [] (unpack 3 0xa0403860890090208810a1003850910 24 0xefb71cab5a0d8e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x14 : Ex t115 4 [v18,u0,u2,u1,u4] :=
  certify c115 [⟨_,p115x12⟩,⟨_,p115x13⟩] (unpack 4 0xa040385038203860a100881090280018000091003830890 33 0x565627a2b6b66565a2a29876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x15 : Ex t115 3 [v19,u0,u2,u4] :=
  certify c115 [] (unpack 4 0xa04038603850890090208810a1003830910 24 0x838334345715506543430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x16 : Ex t115 3 [v20,u0,u2,u4] :=
  certify c115 [] (unpack 3 0xa04090208810a100383091003850890 24 0xf7dbae118d7551a408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x17 : Ex t115 4 [v21,u0,u2,u1,u4] :=
  certify c115 [⟨_,p115x15⟩,⟨_,p115x16⟩] (unpack 4 0x90203850382038308900a0408818001800009100a100386 33 0xb5b52a8265655b5b72a79876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x18 : Ex t115 3 [v80,u0,u4,u2] :=
  certify c115 [] (unpack 4 0x983089003850a1003830910088109020a04 24 0x10145458181776335432210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x19 : Ex t115 3 [v81,u0,u4,u2] :=
  certify c115 [] (unpack 3 0xa040a10038309020881091003850890 24 0xefb1a871c5aa8e3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x20 : Ex t115 3 [v82,u0,u4,u1] :=
  certify c115 [] (unpack 4 0x38509100a85089003830a1008810a040902 24 0x10173478787606055432210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x21 : Ex t115 3 [v83,u0,u4,u1] :=
  certify c115 [] (unpack 3 0x385090209100a0408810a1003830890 24 0xcf317879e54d8e3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x22 : Ex t115 4 [v84,u0,u4,u1,u2] :=
  certify c115 [⟨_,p115x18⟩,⟨_,p115x19⟩,⟨_,p115x20⟩,⟨_,p115x21⟩] (unpack 4 0xa0403830385038609020903800380020a1080018000091008810890 33 0xd9d925c29d9dc5c5b2b2a987565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x23 : Ex t115 3 [v85,u0,u4,u2] :=
  certify c115 [] (unpack 3 0xa04038508900a100383090209100881 24 0xe38b1d1c7a75319408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x24 : Ex t115 3 [v86,u0,u4,u2] :=
  certify c115 [] (unpack 3 0x3830a1008810902038508900910 24 0xd2c3718e31a88e3288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x25 : Ex t115 3 [v87,u0,u4,u1] :=
  certify c115 [] (unpack 3 0x91003850902038308900a040a100881 24 0xa28e677f3145663408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x26 : Ex t115 3 [v88,u0,u4,u1] :=
  certify c115 [] (unpack 4 0x98303850910090208810a04038308900a10 24 0x846416714343626045431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x27 : Ex t115 4 [v89,u0,u4,u1,u2] :=
  certify c115 [⟨_,p115x23⟩,⟨_,p115x24⟩,⟨_,p115x25⟩,⟨_,p115x26⟩] (unpack 4 0x8003800209838001800009020a100383091003850881089009030386 33 0x6373d77c5765b353a5598276225423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x28 : Ex t115 4 [v90,u0,u4,u1,u2] :=
  certify c115 [] (unpack 4 0xa0408800890090203830a100385091008810386 33 0x969624526969745772378765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x29 : Ex t115 4 [v91,u0,u4,u1,u2] :=
  certify c115 [] (unpack 4 0x9830880088103860a1003830910038509020890 33 0x475735439737454523238765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x30 : Ex t115 3 [v34,v35,u0,u4] :=
  certify c115 [] (unpack 3 0x9100386089003830b06038109020881 21 0x20dd2dfac0c2208) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x31 : Ex t115 4 [v35,u1,u2,u0,u4] :=
  certify c115 [⟨_,p115x30⟩] (unpack 4 0x38608900a04090209100a1080000b06088103830385 33 0x272795a996a99aa982827272654323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x32 : Ex t115 4 [v34,u1,u2,u0,u4] :=
  certify c115 [⟨_,p115x30⟩] (unpack 4 0x38608900a040a10038303858000091009020881 33 0x10189588948899870706101054321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x33 : Ex t115 3 [v36,u1,u2,u4] :=
  certify c115 [] (unpack 3 0x90208810a040a100383091003850890 24 0xbaefbe71cd75118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x34 : Ex t115 3 [v37,u1,u2,u4] :=
  certify c115 [] (unpack 3 0xa04088109020a100386091003850890 24 0xfbebae50ad75118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x35 : Ex t115 4 [v38,u1,u2,u0,u4] :=
  certify c115 [⟨_,p115x33⟩,⟨_,p115x34⟩] (unpack 4 0x3860a04038103850a100902088180018000089003830910 33 0x565627b22b82a5a565659876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x36 : Ex t115 3 [v39,u1,u2,u4] :=
  certify c115 [] (unpack 3 0xa04088109020a100383091003850890 24 0xfbebae45ad75118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x37 : Ex t115 3 [v40,u1,u2,u4] :=
  certify c115 [] (unpack 3 0xa04088109020a100383091003860890 24 0xfbebae51ad75118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x38 : Ex t115 4 [v41,u1,u2,u0,u4] :=
  certify c115 [⟨_,p115x36⟩,⟨_,p115x37⟩] (unpack 4 0x38609020381038309100a0408818001800008900a100385 33 0x5a5a2b8227b26565a5a59876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x39 : Ex t115 3 [v92,u1,u4,u0] :=
  certify c115 [] (unpack 4 0x386089003850b06091003830a1009020a040881 24 0x10189788348706055432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x40 : Ex t115 3 [v93,u1,u4,u0] :=
  certify c115 [] (unpack 3 0x385090208900a0408810a1003830910 24 0x79ea3dcf354d8e3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x41 : Ex t115 3 [v94,u1,u4,u2] :=
  certify c115 [] (unpack 4 0x983091003850a1003830890090208810a04 24 0x10145458181736335431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x42 : Ex t115 3 [v95,u1,u4,u2] :=
  certify c115 [] (unpack 3 0xa040a10038308810902091003850890 24 0xf3c5aa71c1a88e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x43 : Ex t115 4 [v96,u1,u4,u0,u2] :=
  certify c115 [⟨_,p115x39⟩,⟨_,p115x40⟩,⟨_,p115x41⟩,⟨_,p115x42⟩] (unpack 4 0xa0403868003800208900383038508810883800180000a1009020910 33 0xd6d692896d6d9c799ba98282765423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x44 : Ex t115 3 [v97,u1,u4,u2] :=
  certify c115 [] (unpack 3 0xa040a10038308810902091003860890 24 0xefb5aa7df1a8903088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x45 : Ex t115 3 [v98,u1,u4,u2] :=
  certify c115 [] (unpack 3 0x3830a1009020881038509100890 24 0xceb3718e31a88e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x46 : Ex t115 3 [v99,u1,u4,u0] :=
  certify c115 [] (unpack 3 0x38608900902038309100a040a100881 24 0x145cfec66a28663408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x47 : Ex t115 3 [v100,u1,u4,u0] :=
  certify c115 [] (unpack 4 0x98303850890088109020a04038309100a10 24 0x846461764343626055431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x48 : Ex t115 4 [v101,u1,u4,u0,u2] :=
  certify c115 [⟨_,p115x44⟩,⟨_,p115x45⟩,⟨_,p115x46⟩,⟨_,p115x47⟩] (unpack 4 0x800380020983038680010890800008810a1003830902091008830385 33 0x4353d55c8548b38382a89887625423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x49 : Ex t115 4 [v102,u1,u4,u0,u2] :=
  certify c115 [] (unpack 4 0xa0409000910088103830a100386089009020385 33 0x969624526969273274578765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x50 : Ex t115 4 [v103,u1,u4,u0,u2] :=
  certify c115 [] (unpack 4 0x9830900090203850a1003830890038608810910 33 0x475735439737326345458765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x51 : Ex t115 3 [v104,u2,u4,u1] :=
  certify c115 [] (unpack 3 0x91003850a850a100383089008810902 24 0x41f9feb266989a208) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x52 : Ex t115 3 [v105,u2,u4,u1] :=
  certify c115 [] (unpack 3 0xa0409100385088109020a1003830890 24 0x71cc8ef3c1a88e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x53 : Ex t115 3 [v106,u2,u4,u0] :=
  certify c115 [] (unpack 4 0x386038508900b060a100383091009020881 24 0x10168366276305042321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x54 : Ex t115 3 [v107,u2,u4,u0] :=
  certify c115 [] (unpack 3 0xa0403850890090208810a1003830910 24 0x71ca8defb1758e3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x55 : Ex t115 4 [v108,u2,u4,u0,u1] :=
  certify c115 [⟨_,p115x51⟩,⟨_,p115x52⟩,⟨_,p115x53⟩,⟨_,p115x54⟩] (unpack 4 0x8003800209100385090203868001800008900383088108850a040a10 33 0x9393ba4bbdcb5ba539395845576543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x56 : Ex t115 3 [v109,u2,u4,u1] :=
  certify c115 [] (unpack 3 0xa0409100385088109020a1003860890 24 0x7dfcaeefb1a8903088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x57 : Ex t115 3 [v110,u2,u4,u1] :=
  certify c115 [] (unpack 4 0x9830385091009020a04088103830a100890 24 0x836361264343076053430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x58 : Ex t115 3 [v111,u2,u4,u0] :=
  certify c115 [] (unpack 3 0x38608900a04090208810a1003850910 24 0x75dcbec0eaeb8c3088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x59 : Ex t115 3 [v112,u2,u4,u0] :=
  certify c115 [] (unpack 4 0x9830385089008810a04090203830a100910 24 0x836361264343676055430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x60 : Ex t115 4 [v113,u2,u4,u0,u1] :=
  certify c115 [⟨_,p115x56⟩,⟨_,p115x57⟩,⟨_,p115x58⟩,⟨_,p115x59⟩] (unpack 4 0x80038002091003850a85038680010890800008810a040a1008850383 33 0xa3b3b2abdbbc6ba693636286766543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x61 : Ex t115 4 [v114,u2,u4,u0,u1] :=
  certify c115 [] (unpack 4 0x9020a000a10088103850910038608900a040383 33 0x969647542452696927328765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x62 : Ex t115 4 [v115,u2,u4,u0,u1] :=
  certify c115 [] (unpack 4 0xa850a000a040383091003850890038608810a10 33 0x475754653543973732638765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x63 : Ex t115 5 (roots 23) :=
  certify c115 [⟨_,p115x1⟩,⟨_,p115x2⟩,⟨_,p115x5⟩,⟨_,p115x8⟩,⟨_,p115x10⟩,⟨_,p115x11⟩,⟨_,p115x14⟩,⟨_,p115x17⟩,⟨_,p115x22⟩,⟨_,p115x27⟩,⟨_,p115x28⟩,⟨_,p115x29⟩,⟨_,p115x31⟩,⟨_,p115x32⟩,⟨_,p115x35⟩,⟨_,p115x38⟩,⟨_,p115x43⟩,⟨_,p115x48⟩,⟨_,p115x49⟩,⟨_,p115x50⟩,⟨_,p115x55⟩,⟨_,p115x60⟩,⟨_,p115x61⟩,⟨_,p115x62⟩] (unpack 6 0x8017801680150a0480148013801280118010800f800e800d800c800b800a8009088180080902800780068005038380040a1080038002800103860385800009100890 96 0x81d29d7d021079d21d7102906ce0ce69005064e04e6100d05ca0415880c854a0ca5080414d011048e00e4500103ce10e34a0003081082ca10a2480001c3000181101143103081000) (by decide +kernel)
theorem l115 : CClaim 23 t115 6 := fromTable 268485254 (by decide +kernel) p115x63

abbrev t116 : Sig := 0xe8e88080e8e88080e8e88080e8e88080
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c116 : Cuts t116 := [
  rule t116 1 l62 none (by decide +kernel),
  rule t116 2 l58 none (by decide +kernel),
  rule t116 16 l38 none (by decide +kernel),
  rule t116 4 l54 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x0 : Ex t116 3 [v116,u2,u0,u1] :=
  certify c116 [] (unpack 4 0x9910a94099203850b06038609830a850383 24 0x50853570306122542232010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x1 : Ex t116 4 [v117,u2,u0,u1,u4] :=
  certify c116 [⟨_,p116x0⟩] (unpack 4 0xb0609910a940b120a9109920a85800040020983038503860383 31 0x3636b89b3c3cb7ba898763635343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x2 : Ex t116 4 [v118,u2,u0,u1,u4] :=
  certify c116 [] (unpack 4 0xb0603830a8509830b14099103850a94099203860a91 37 0x787896957a7a5253939297898787654432110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x3 : Ex t116 3 [v119,u4,u0,u1] :=
  certify c116 [] (unpack 4 0xa940b06038509910386099209830a850383 24 0x212664682724600540030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x4 : Ex t116 4 [v120,u4,u0,u1,u2] :=
  certify c116 [⟨_,p116x3⟩] (unpack 4 0xa910b1203850a940b060a850386800040030383099109920983 31 0x3c733a3ca78a363ba6a978765343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x5 : Ex t116 4 [v121,u4,u0,u1,u2] :=
  certify c116 [] (unpack 4 0xb1209830a9103830b14099103850a94099203860a85 37 0x798774789694717a414393918787645431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x6 : Ex t116 3 [v35,v15,v7,u4] :=
  certify c116 [] (unpack 4 0x3864001038509910a85038340000a910b060983 24 0x50599867736505044321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x7 : Ex t116 4 [v15,u2,v7,u1,u4] :=
  certify c116 [⟨_,p116x6⟩] (unpack 4 0x800003850b124003038609920a8509830b1440010a940383 34 0x4545939b4545a698677265454545413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x8 : Ex t116 3 [v96,v84,v7,u2] :=
  certify c116 [] (unpack 4 0x400103850a91098340000a850b120b060383 24 0x70673877147603055432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x9 : Ex t116 4 [v84,u4,v7,u1,u2] :=
  certify c116 [⟨_,p116x8⟩] (unpack 4 0x800003850b064002099203860a9103830b1440010a940983 34 0x45944545939b4645a69866726545413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x10 : Ex t116 4 [v35,u2,v7,u0,u4] :=
  certify c116 [⟨_,p116x6⟩] (unpack 4 0x80000b140a9403860a9140030385400009910a850b0609830383 34 0x12128a8cab5a1313948746654313121210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x11 : Ex t116 4 [v96,u4,v7,u0,u2] :=
  certify c116 [⟨_,p116x8⟩] (unpack 4 0x80000b140a940a9103860a8540020991400003850b1203830983 34 0x197112127a7cab4a131983763354321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x12 : Ex t116 5 [v7,u0,u1,u2,u4] :=
  certify c116 [⟨_,p116x1⟩,⟨_,p116x2⟩,⟨_,p116x4⟩,⟨_,p116x5⟩,⟨_,p116x7⟩,⟨_,p116x9⟩,⟨_,p116x10⟩,⟨_,p116x11⟩] (unpack 5 0x8007800680050b0680040b120a940b1480034002098380020a8580014003038380000a910385400140000386 99 0x24c6591692256632c4b4b92b72d3549846238867189422c2b93e4b7ae539182683e0679a11805ef709c10856d5a5895b169524c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x13 : Ex t116 4 [v122,u1,u0,u2,u4] :=
  certify c116 [] (unpack 4 0xb06038509830a850b120a91038309920a9403860991 37 0x78788a8a56539392878969958787654432110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x14 : Ex t116 3 [v123,u4,u0,u2] :=
  certify c116 [] (unpack 4 0x9920b060383099103860a940a8509830385 24 0x612664681714606540031210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x15 : Ex t116 4 [v124,u4,u0,u2,u1] :=
  certify c116 [⟨_,p116x14⟩] (unpack 4 0x9910b14038309920b06098303868000400103850a910a940a85 31 0xa3ac7c73a78a363ba6a978765343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x16 : Ex t116 4 [v125,u4,u0,u2,u1] :=
  certify c116 [] (unpack 4 0xb140a85099103850b120a910383099203860983 37 0x3637687635836169313282817676534321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x17 : Ex t116 3 [v108,v84,v15,u1] :=
  certify c116 [] (unpack 4 0xb1440030b060383099103850a8540000983 24 0x386335545075561540030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x18 : Ex t116 4 [v84,u4,v15,u2,u1] :=
  certify c116 [⟨_,p116x17⟩] (unpack 4 0x800003830b0640020386099103850b12400309920983 34 0x54454584838a4645968766126545413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x19 : Ex t116 4 [v108,u4,v15,u0,u1] :=
  certify c116 [⟨_,p116x17⟩] (unpack 4 0xb1480000b120992038509910386098340020a91400003830a85 34 0x57588ca8898c595b9a2981176154113210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x20 : Ex t116 4 [v35,u1,v15,u0,u4] :=
  certify c116 [⟨_,p116x6⟩] (unpack 4 0x80000b120992038640010991038340000a910a850b0609830385 34 0x12127a7cab5a3131947876654131321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x21 : Ex t116 5 [v15,u0,u2,u1,u4] :=
  certify c116 [⟨_,p116x1⟩,⟨_,p116x13⟩,⟨_,p116x15⟩,⟨_,p116x16⟩,⟨_,p116x7⟩,⟨_,p116x18⟩,⟨_,p116x19⟩,⟨_,p116x20⟩] (unpack 5 0x8007800680050b0680040b1409920b12800340020a8580020983800140010385800009910383400340000386 99 0x24c9591692256633884118ce31aa422c4b4b92b72d344a42993e497a6539182683de679a11805ef709c10856d5a5895b169524c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x22 : Ex t116 4 [v81,u1,u0,u4,u2] :=
  certify c116 [] (unpack 4 0xb12099103830a910b060a8509830a94038609920385 37 0x8758828a56529223878965658787654423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x23 : Ex t116 4 [v83,u2,u0,u4,u1] :=
  certify c116 [] (unpack 4 0xb140a91038509910b060a850983038609920383 37 0x3637677672793532822153537676534321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x24 : Ex t116 4 [v96,u1,v84,u0,u2] :=
  certify c116 [⟨_,p116x8⟩] (unpack 4 0x8000038609924001098340000a8503850a910b120b0603830991 34 0x1b135b5cb27b4161a65958876151431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x25 : Ex t116 4 [v108,u2,v84,u0,u1] :=
  certify c116 [⟨_,p116x17⟩] (unpack 4 0xb1480000b060386099103850992400303830a85400009830a91 34 0x47487ca7797c494b9a2981176145413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x26 : Ex t116 5 [v84,u0,u4,u1,u2] :=
  certify c116 [⟨_,p116x4⟩,⟨_,p116x22⟩,⟨_,p116x15⟩,⟨_,p116x23⟩,⟨_,p116x9⟩,⟨_,p116x18⟩,⟨_,p116x24⟩,⟨_,p116x25⟩] (unpack 5 0x8007800680050b1280040b1403860b06800340030a9180020383800140010991800003850983400240000992 99 0x392912d6e5baa94a4c9590892256633884118ce33a842242993de97a6539102483de479211805ef709c10856d5a5895b169524c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x27 : Ex t116 3 [v126,u4,u1,u2] :=
  certify c116 [] (unpack 4 0x9910a850383099203850a940b0609830386 24 0x617664681714606540431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x28 : Ex t116 4 [v127,u4,u1,u2,u0] :=
  certify c116 [⟨_,p116x27⟩] (unpack 4 0xa940992800040000386038309910a85098303850b120b140b06 31 0x787b383c4b488a98745773764543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x29 : Ex t116 4 [v128,u4,u1,u2,u0] :=
  certify c116 [] (unpack 4 0xa940b06099203860a910383099103850983 37 0x3536151857653473313212716565434321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x30 : Ex t116 3 [v108,v96,v35,u0] :=
  certify c116 [] (unpack 3 0x9920a940386400303830a8540010983 24 0x75f1c559562368b088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x31 : Ex t116 4 [v96,u4,v35,u2,u0] :=
  certify c116 [⟨_,p116x30⟩] (unpack 4 0x9920386800003830a85400203850a91400309910983 34 0x399a494a6a699a19636874654412413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x32 : Ex t116 4 [v108,u4,v35,u1,u0] :=
  certify c116 [⟨_,p116x30⟩] (unpack 4 0x9920a940386800009910385098340020a91400103830a85 34 0x799a191b5b599a39575873276154113210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x33 : Ex t116 4 [v129,u0,u1,u2,u4] :=
  certify c116 [] (unpack 4 0xa85038609830b060a910b12038309910b1403850992 37 0xa8a88a8a36538789699539928787654432110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x34 : Ex t116 5 [v35,u1,u2,u0,u4] :=
  certify c116 [⟨_,p116x28⟩,⟨_,p116x29⟩,⟨_,p116x31⟩,⟨_,p116x32⟩,⟨_,p116x1⟩,⟨_,p116x33⟩,⟨_,p116x10⟩,⟨_,p116x20⟩] (unpack 5 0x800780060a9480054000038680040992800380020a8509910a91800140020b06800009830383400340010385 99 0x1204338c4710d0825c914209842ae72a6a0c20a842939c5ce94211841ee72c4b2248b4ac8d210245a9645116c5854a48921084c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x35 : Ex t116 4 [v93,u2,u1,u4,u0] :=
  certify c116 [] (unpack 3 0xa94038609920a850983038509910383 37 0x3af2cbddab8d148c71ebac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x36 : Ex t116 4 [v95,u0,u1,u4,u2] :=
  certify c116 [] (unpack 4 0xa91099203830b120a850b0609830b14038509910386 37 0x8a68828a26528789656529238787654423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x37 : Ex t116 4 [v108,u2,v96,u1,u0] :=
  certify c116 [⟨_,p116x30⟩] (unpack 4 0x9920a940386800003850991400303830a85400109830a91 34 0x797a1b19494b3a39474873276145413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x38 : Ex t116 5 [v96,u1,u4,u0,u2] :=
  certify c116 [⟨_,p116x28⟩,⟨_,p116x35⟩,⟨_,p116x31⟩,⟨_,p116x4⟩,⟨_,p116x36⟩,⟨_,p116x11⟩,⟨_,p116x24⟩,⟨_,p116x37⟩] (unpack 5 0x8007800680050a948004400009928003038680020a9103850a85800140030b12800003830983400240010991 99 0x248412d695a6a4211e4335a4690cf7a5a913de97a68d6aa4a0b5aa6aa72941ad8bdf07bdcd690245a9445116c5854a48921084c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x39 : Ex t116 4 [v105,u0,u2,u4,u1] :=
  certify c116 [] (unpack 4 0x9910a9403850b140b0609830a850b1203830a910386 37 0x5a58282a25628789565623238787565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x40 : Ex t116 4 [v107,u1,u2,u4,u0] :=
  certify c116 [] (unpack 3 0x99203860a9409830a8503830a910385 37 0x4f32cbddaa8d471a28ebac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x41 : Ex t116 5 [v108,u2,u4,u0,u1] :=
  certify c116 [⟨_,p116x15⟩,⟨_,p116x39⟩,⟨_,p116x19⟩,⟨_,p116x25⟩,⟨_,p116x28⟩,⟨_,p116x40⟩,⟨_,p116x32⟩,⟨_,p116x37⟩] (unpack 5 0x80078006099180054001800403850b14800380020992800140000a9480000386038309830a85400240030a91 99 0x11e414e64992af796650bde5796939c5ef939d173a0f7bd0f718cf33dc8410c412d64591a631565098c53158b5a4c652109420e6304a5208810842118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x42 : Ex t116 6 (roots 23) :=
  certify c116 [⟨_,p116x12⟩,⟨_,p116x21⟩,⟨_,p116x26⟩,⟨_,p116x34⟩,⟨_,p116x38⟩,⟨_,p116x41⟩] (unpack 5 0x800580040a8580030a9109914002098380020b064003038380010b120992400140000386038580000b140a94 96 0x5cd4a7ba2e5ce33ab94a3386e7ce1333a0ea4c6332a0a5c4633286a946102b88e7b0ec2b8ee6b0842a8ea5a0842a88a4a0e728c033048428c8310400) (by decide +kernel)
theorem l116 : CClaim 23 t116 7 := fromTable 805356166 (by decide +kernel) p116x42

abbrev t119 : Sig := 0xee88ee00ee88ee00ee88ee00ee88ee00
theorem l119 : CClaim 27 t119 5 := liftTable 16 16 807404552 5 l41 (by decide +kernel)

abbrev t120 : Sig := 0xffeeff88ffeeff88ffeeff88ffeeff88
theorem l120 : CClaim 27 t120 5 := liftTable 0 8 268435586 5 l54 (by decide +kernel)

abbrev t123 : Sig := 0xfaa0fa00faa0fa00faa0fa00faa0fa00
theorem l123 : CClaim 29 t123 5 := liftTable 16 16 1344405512 5 l45 (by decide +kernel)

abbrev t124 : Sig := 0xfffaffa0fffaffa0fffaffa0fffaffa0
theorem l124 : CClaim 29 t124 5 := liftTable 0 8 268451844 5 l58 (by decide +kernel)

abbrev t127 : Sig := 0xfcc0fc00fcc0fc00fcc0fc00fcc0fc00
theorem l127 : CClaim 30 t127 5 := liftTable 16 16 1614939136 5 l49 (by decide +kernel)

abbrev t128 : Sig := 0xfffcffc0fffcffc0fffcffc0fffcffc0
theorem l128 : CClaim 30 t128 5 := liftTable 0 8 536904192 5 l62 (by decide +kernel)

abbrev t130 : Sig := 0xe8e8e8e880808080e8e8e8e880808080
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c130 : Cuts t130 := [
  rule t130 1 l86 none (by decide +kernel),
  rule t130 2 l82 none (by decide +kernel),
  rule t130 32 l38 none (by decide +kernel),
  rule t130 4 l78 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x0 : Ex t130 3 [v130,u2,u0,u1] :=
  certify c130 [] (unpack 4 0x11a112a411a2038513060386118312850383 24 0x50853570306122542232010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x1 : Ex t130 4 [v117,u2,u0,u1,u5] :=
  certify c130 [⟨_,p130x0⟩] (unpack 4 0x130611a112a4132212a111a21285800040021183038503860383 31 0x3636b89b3c3cb7ba898763635343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x2 : Ex t130 4 [v118,u2,u0,u1,u5] :=
  certify c130 [] (unpack 4 0x1306038312851183132411a1038512a411a2038612a1 37 0x787896957a7a5253939297898787654432110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x3 : Ex t130 3 [v131,u5,u0,u1] :=
  certify c130 [] (unpack 4 0x12a41306038511a1038611a2118312850383 24 0x212664682724600540030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x4 : Ex t130 4 [v132,u5,u0,u1,u2] :=
  certify c130 [⟨_,p130x3⟩] (unpack 4 0x12a11322038512a413061285038680004003038311a111a21183 31 0x3c733a3ca78a363ba6a978765343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x5 : Ex t130 4 [v133,u5,u0,u1,u2] :=
  certify c130 [] (unpack 4 0x1322118312a10383132411a1038512a411a203861285 37 0x798774789694717a414393918787645431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x6 : Ex t130 3 [v35,v15,v7,u5] :=
  certify c130 [] (unpack 4 0x3864001038511a112850383400012a113061183 24 0x50599867736505044321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x7 : Ex t130 4 [v15,u2,v7,u1,u5] :=
  certify c130 [⟨_,p130x6⟩] (unpack 4 0x8000038513224003038611a2128511831324400112a40383 34 0x4545939b4545a698677265454545413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x8 : Ex t130 3 [v134,v135,v7,u2] :=
  certify c130 [] (unpack 4 0x4001038512a1118340001285132213060383 24 0x70673877147603055432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x9 : Ex t130 4 [v135,u5,v7,u1,u2] :=
  certify c130 [⟨_,p130x8⟩] (unpack 4 0x800003851306400211a2038612a103831324400112a41183 34 0x45944545939b4645a69866726545413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x10 : Ex t130 4 [v35,u2,v7,u0,u5] :=
  certify c130 [⟨_,p130x6⟩] (unpack 4 0x8000132412a4038612a140030385400011a11285130611830383 34 0x12128a8cab5a1313948746654313121210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x11 : Ex t130 4 [v134,u5,v7,u0,u2] :=
  certify c130 [⟨_,p130x8⟩] (unpack 4 0x8000132412a412a103861285400211a140000385132203831183 34 0x197112127a7cab4a131983763354321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x12 : Ex t130 5 [v7,u0,u1,u2,u5] :=
  certify c130 [⟨_,p130x1⟩,⟨_,p130x2⟩,⟨_,p130x4⟩,⟨_,p130x5⟩,⟨_,p130x7⟩,⟨_,p130x9⟩,⟨_,p130x10⟩,⟨_,p130x11⟩] (unpack 5 0x80078006800513068004132212a4132480034002118380021285800140030383800012a10385400140000386 99 0x24c6591692256632c4b4b92b72d3549846238867189422c2b93e4b7ae539182683e0679a11805ef709c10856d5a5895b169524c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x13 : Ex t130 4 [v122,u1,u0,u2,u5] :=
  certify c130 [] (unpack 4 0x1306038511831285132212a1038311a212a4038611a1 37 0x78788a8a56539392878969958787654432110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x14 : Ex t130 3 [v136,u5,u0,u2] :=
  certify c130 [] (unpack 4 0x11a21306038311a1038612a4128511830385 24 0x612664681714606540031210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x15 : Ex t130 4 [v137,u5,u0,u2,u1] :=
  certify c130 [⟨_,p130x14⟩] (unpack 4 0x11a11324038311a213061183038680004001038512a112a41285 31 0xa3ac7c73a78a363ba6a978765343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x16 : Ex t130 4 [v138,u5,u0,u2,u1] :=
  certify c130 [] (unpack 4 0x1324128511a10385132212a1038311a203861183 37 0x3637687635836169313282817676534321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x17 : Ex t130 3 [v139,v135,v15,u1] :=
  certify c130 [] (unpack 4 0x132440031306038311a10385128540001183 24 0x386335545075561540030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x18 : Ex t130 4 [v135,u5,v15,u2,u1] :=
  certify c130 [⟨_,p130x17⟩] (unpack 4 0x8000038313064002038611a103851322400311a21183 34 0x54454584838a4645968766126545413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x19 : Ex t130 4 [v139,u5,v15,u0,u1] :=
  certify c130 [⟨_,p130x17⟩] (unpack 4 0x13248000132211a2038511a103861183400212a1400003831285 34 0x57588ca8898c595b9a2981176154113210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x20 : Ex t130 4 [v35,u1,v15,u0,u5] :=
  certify c130 [⟨_,p130x6⟩] (unpack 4 0x8000132211a20386400111a10383400012a11285130611830385 34 0x12127a7cab5a3131947876654131321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x21 : Ex t130 5 [v15,u0,u2,u1,u5] :=
  certify c130 [⟨_,p130x1⟩,⟨_,p130x13⟩,⟨_,p130x15⟩,⟨_,p130x16⟩,⟨_,p130x7⟩,⟨_,p130x18⟩,⟨_,p130x19⟩,⟨_,p130x20⟩] (unpack 5 0x80078006800513068004132411a2132280034002128580021183800140010385800011a10383400340000386 99 0x24c9591692256633884118ce31aa422c4b4b92b72d344a42993e497a6539182683de679a11805ef709c10856d5a5895b169524c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x22 : Ex t130 4 [v140,u1,u0,u5,u2] :=
  certify c130 [] (unpack 4 0x132211a1038312a113061285118312a4038611a20385 37 0x8758828a56529223878965658787654423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x23 : Ex t130 4 [v141,u2,u0,u5,u1] :=
  certify c130 [] (unpack 4 0x132412a1038511a1130612851183038611a20383 37 0x3637677672793532822153537676534321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x24 : Ex t130 4 [v134,u1,v135,u0,u2] :=
  certify c130 [⟨_,p130x8⟩] (unpack 4 0x8000038611a24001118340001285038512a113221306038311a1 34 0x1b135b5cb27b4161a65958876151431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x25 : Ex t130 4 [v139,u2,v135,u0,u1] :=
  certify c130 [⟨_,p130x17⟩] (unpack 4 0x132480001306038611a1038511a24003038312854000118312a1 34 0x47487ca7797c494b9a2981176145413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x26 : Ex t130 5 [v135,u0,u5,u1,u2] :=
  certify c130 [⟨_,p130x4⟩,⟨_,p130x22⟩,⟨_,p130x15⟩,⟨_,p130x23⟩,⟨_,p130x9⟩,⟨_,p130x18⟩,⟨_,p130x24⟩,⟨_,p130x25⟩] (unpack 5 0x800780068005132280041324038613068003400312a1800203838001400111a18000038511834002400011a2 99 0x392912d6e5baa94a4c9590892256633884118ce33a842242993de97a6539102483de479211805ef709c10856d5a5895b169524c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x27 : Ex t130 3 [v142,u5,u1,u2] :=
  certify c130 [] (unpack 4 0x11a11285038311a2038512a4130611830386 24 0x617664681714606540431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x28 : Ex t130 4 [v143,u5,u1,u2,u0] :=
  certify c130 [⟨_,p130x27⟩] (unpack 4 0x12a411a2800040000386038311a1128511830385132213241306 31 0x787b383c4b488a98745773764543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x29 : Ex t130 4 [v144,u5,u1,u2,u0] :=
  certify c130 [] (unpack 4 0x12a4130611a2038612a1038311a103851183 37 0x3536151857653473313212716565434321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x30 : Ex t130 3 [v139,v134,v35,u0] :=
  certify c130 [] (unpack 3 0x11a212a4038640030383128540011183 24 0x75f1c559562368b088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x31 : Ex t130 4 [v134,u5,v35,u2,u0] :=
  certify c130 [⟨_,p130x30⟩] (unpack 4 0x11a203868000038312854002038512a1400311a11183 34 0x399a494a6a699a19636874654412413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x32 : Ex t130 4 [v139,u5,v35,u1,u0] :=
  certify c130 [⟨_,p130x30⟩] (unpack 4 0x11a212a40386800011a103851183400212a1400103831285 34 0x799a191b5b599a39575873276154113210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x33 : Ex t130 4 [v129,u0,u1,u2,u5] :=
  certify c130 [] (unpack 4 0x128503861183130612a11322038311a11324038511a2 37 0xa8a88a8a36538789699539928787654432110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x34 : Ex t130 5 [v35,u1,u2,u0,u5] :=
  certify c130 [⟨_,p130x28⟩,⟨_,p130x29⟩,⟨_,p130x31⟩,⟨_,p130x32⟩,⟨_,p130x1⟩,⟨_,p130x33⟩,⟨_,p130x10⟩,⟨_,p130x20⟩] (unpack 5 0x8007800612a4800540000386800411a280038002128511a112a1800140021306800011830383400340010385 99 0x1204338c4710d0825c914209842ae72a6a0c20a842939c5ce94211841ee72c4b2248b4ac8d210245a9645116c5854a48921084c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x35 : Ex t130 4 [v145,u2,u1,u5,u0] :=
  certify c130 [] (unpack 3 0x12a4038611a212851183038511a10383 37 0x3af2cbddab8d148c71ebac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x36 : Ex t130 4 [v146,u0,u1,u5,u2] :=
  certify c130 [] (unpack 4 0x12a111a2038313221285130611831324038511a10386 37 0x8a68828a26528789656529238787654423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x37 : Ex t130 4 [v139,u2,v134,u1,u0] :=
  certify c130 [⟨_,p130x30⟩] (unpack 4 0x11a212a403868000038511a14003038312854001118312a1 34 0x797a1b19494b3a39474873276145413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x38 : Ex t130 5 [v134,u1,u5,u0,u2] :=
  certify c130 [⟨_,p130x28⟩,⟨_,p130x35⟩,⟨_,p130x31⟩,⟨_,p130x4⟩,⟨_,p130x36⟩,⟨_,p130x11⟩,⟨_,p130x24⟩,⟨_,p130x37⟩] (unpack 5 0x80078006800512a48004400011a280030386800212a1038512858001400313228000038311834002400111a1 99 0x248412d695a6a4211e4335a4690cf7a5a913de97a68d6aa4a0b5aa6aa72941ad8bdf07bdcd690245a9445116c5854a48921084c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x39 : Ex t130 4 [v147,u0,u2,u5,u1] :=
  certify c130 [] (unpack 4 0x11a112a4038513241306118312851322038312a10386 37 0x5a58282a25628789565623238787565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x40 : Ex t130 4 [v148,u1,u2,u5,u0] :=
  certify c130 [] (unpack 3 0x11a2038612a411831285038312a10385 37 0x4f32cbddaa8d471a28ebac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x41 : Ex t130 5 [v139,u2,u5,u0,u1] :=
  certify c130 [⟨_,p130x15⟩,⟨_,p130x39⟩,⟨_,p130x19⟩,⟨_,p130x25⟩,⟨_,p130x28⟩,⟨_,p130x40⟩,⟨_,p130x32⟩,⟨_,p130x37⟩] (unpack 5 0x8007800611a1800540018004038513248003800211a28001400012a4800003860383118312854002400312a1 99 0x11e414e64992af796650bde5796939c5ef939d173a0f7bd0f718cf33dc8410c412d64591a631565098c53158b5a4c652109420e6304a5208810842118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p130x42 : Ex t130 6 (roots 39) :=
  certify c130 [⟨_,p130x12⟩,⟨_,p130x21⟩,⟨_,p130x26⟩,⟨_,p130x34⟩,⟨_,p130x38⟩,⟨_,p130x41⟩] (unpack 5 0x800580041285800312a111a14002118380021306400303838001132211a240014000038603858000132412a4 96 0x5cd4a7ba2e5ce33ab94a3386e7ce1333a0ea4c6332a0a5c4633286a946102b88e7b0ec2b8ee6b0842a8ea5a0842a88a4a0e728c033048428c8310400) (by decide +kernel)
theorem l130 : CClaim 39 t130 7 := fromTable 103079264902 (by decide +kernel) p130x42

abbrev t133 : Sig := 0xee88ee88ee00ee00ee88ee88ee00ee00
theorem l133 : CClaim 43 t133 5 := liftTable 32 32 103081313288 5 l41 (by decide +kernel)

abbrev t134 : Sig := 0xffeeffeeff88ff88ffeeffeeff88ff88
theorem l134 : CClaim 43 t134 5 := liftTable 0 8 34359738498 5 l78 (by decide +kernel)

abbrev t137 : Sig := 0xfaa0faa0fa00fa00faa0faa0fa00fa00
theorem l137 : CClaim 45 t137 5 := liftTable 32 32 171800920072 5 l45 (by decide +kernel)

abbrev t138 : Sig := 0xfffafffaffa0ffa0fffafffaffa0ffa0
theorem l138 : CClaim 45 t138 5 := liftTable 0 8 34359754756 5 l82 (by decide +kernel)

abbrev t141 : Sig := 0xfcc0fcc0fc00fc00fcc0fcc0fc00fc00
theorem l141 : CClaim 46 t141 5 := liftTable 32 32 206162756608 5 l49 (by decide +kernel)

abbrev t142 : Sig := 0xfffcfffcffc0ffc0fffcfffcffc0ffc0
theorem l142 : CClaim 46 t142 5 := liftTable 0 8 68719510016 5 l86 (by decide +kernel)

abbrev t144 : Sig := 0xeeee888888888888eeee888888888888
theorem l144 : CClaim 51 t144 5 := liftTable 32 32 592973922434 5 l54 (by decide +kernel)

abbrev t148 : Sig := 0xfafaa0a0a0a0a0a0fafaa0a0a0a0a0a0
theorem l148 : CClaim 53 t148 5 := liftTable 32 32 592973938692 5 l58 (by decide +kernel)

abbrev t152 : Sig := 0xfcfcc0c0c0c0c0c0fcfcc0c0c0c0c0c0
theorem l152 : CClaim 54 t152 5 := liftTable 32 32 627602129408 5 l62 (by decide +kernel)

abbrev t156 : Sig := 0xffaaff00ff000000ffaaff00ff000000
theorem l156 : CClaim 57 t156 5 := liftTable 1 1 277058945072 5 l112 (by decide +kernel)

abbrev t157 : Sig := 0xffffffaaffaaaaaaffffffaaffaaaaaa
theorem l157 : CClaim 57 t157 5 := liftTable 0 1 277058945024 5 l112 (by decide +kernel)

abbrev t159 : Sig := 0xffccff00ff000000ffccff00ff000000
theorem l159 : CClaim 58 t159 5 := liftTable 2 2 277058951168 5 l112 (by decide +kernel)

abbrev t160 : Sig := 0xffffffccffccccccffffffccffcccccc
theorem l160 : CClaim 58 t160 5 := liftTable 0 2 277058945024 5 l112 (by decide +kernel)

abbrev t162 : Sig := 0xfff0ff00ff000000fff0ff00ff000000
theorem l162 : CClaim 60 t162 5 := liftTable 4 4 277059731456 5 l112 (by decide +kernel)

abbrev t163 : Sig := 0xfffffff0fff0f0f0fffffff0fff0f0f0
theorem l163 : CClaim 60 t163 5 := liftTable 0 4 277058945024 5 l112 (by decide +kernel)

abbrev t164 : Sig := 0xfe808080fe808080fe808080fe808080
theorem l164 : CClaim 31 t164 7 := liftTable 16 16 2451620486 7 l113 (by decide +kernel)

abbrev t165 : Sig := 0xfee8fe80fee8fe80fee8fe80fee8fe80
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c165 : Cuts t165 := [
  rule t165 0 l116 (some (2,u0,u1)) (by decide +kernel),
  rule t165 0 l123 none (by decide +kernel),
  rule t165 0 l116 (some (3,u0,u1)) (by decide +kernel),
  rule t165 0 l119 none (by decide +kernel),
  rule t165 4 l120 none (by decide +kernel),
  rule t165 0 l116 none (by decide +kernel),
  rule t165 0 l116 (some (0,u0,u1)) (by decide +kernel),
  rule t165 16 l114 (some (0,u0,u1)) (by decide +kernel),
  rule t165 16 l114 none (by decide +kernel),
  rule t165 1 l128 none (by decide +kernel),
  rule t165 1 l62 none (by decide +kernel),
  rule t165 16 l45 none (by decide +kernel),
  rule t165 0 l127 none (by decide +kernel),
  rule t165 0 l116 (some (1,u0,u1)) (by decide +kernel),
  rule t165 0 l113 none (by decide +kernel),
  rule t165 16 l114 (some (1,u0,u1)) (by decide +kernel),
  rule t165 2 l124 none (by decide +kernel),
  rule t165 16 l114 (some (2,u0,u1)) (by decide +kernel),
  rule t165 16 l114 (some (3,u0,u1)) (by decide +kernel),
  rule t165 0 l116 (some (2,u0,u2)) (by decide +kernel),
  rule t165 0 l116 (some (3,u0,u2)) (by decide +kernel),
  rule t165 0 l116 (some (0,u0,u2)) (by decide +kernel),
  rule t165 16 l114 (some (0,u0,u2)) (by decide +kernel),
  rule t165 16 l41 none (by decide +kernel),
  rule t165 0 l116 (some (1,u0,u2)) (by decide +kernel),
  rule t165 16 l114 (some (1,u0,u2)) (by decide +kernel),
  rule t165 16 l114 (some (2,u0,u2)) (by decide +kernel),
  rule t165 16 l114 (some (3,u0,u2)) (by decide +kernel),
  rule t165 0 l116 (some (2,u1,u2)) (by decide +kernel),
  rule t165 0 l116 (some (3,u1,u2)) (by decide +kernel),
  rule t165 0 l116 (some (0,u1,u2)) (by decide +kernel),
  rule t165 16 l114 (some (0,u1,u2)) (by decide +kernel),
  rule t165 2 l58 none (by decide +kernel),
  rule t165 0 l116 (some (1,u1,u2)) (by decide +kernel),
  rule t165 16 l114 (some (1,u1,u2)) (by decide +kernel),
  rule t165 16 l114 (some (2,u1,u2)) (by decide +kernel),
  rule t165 16 l114 (some (3,u1,u2)) (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x0 : Ex t165 6 [v6,v7,u2,u3,u4] :=
  certify c165 [] (unpack 5 0xc910a91400b0a85400a058303850991400103840983048106040a940383400906080488 148 0x6b4c669e276b63169cc67b82179e077ba0e79c216946569826694256986649d674b94e49d474b96b4b16c499264b1ac4996648d434856148d63485414a44811c001088411c87108001188611405118061148510c001048110c8310400) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x1 : Ex t165 7 [v7,u0,u1,u2,u3,u4] :=
  certify c165 [⟨_,p165x0⟩] (unpack 5 0xc910a9106040b140b0605020a9404880508400c80004008098340070a850583400640050481400403834003060840020385400140000386 212 0x5ad295bf6f5af7b5bd29734a573f4f7374d73ca55e4f95a4a95e4b95a4e973e737370d73f0f736735db165a6695da765a70911e731170511f071167373e9475eb773eaf75e945a6a95da965a6895dab691e94916a591ea79169410a9414c531485173dcf7360d73e0f735cd5b14c5a5695b16c5a54911cc71144511d07114c51088310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x2 : Ex t165 7 [v6,u0,u1,u2,u3,u4] :=
  certify c165 [⟨_,p165x0⟩] (unpack 5 0xc910a910a8540100991400005080b060502099203850386400c800040024001048840080983400f400e0481400d4005060440040383400940030608 212 0x39d083afab39fbd3ad0856c0052f8b56f9b52c00394653a008394053a06852e6b56f3b52f2b56e733d6753a0e83d4f53a268d0f2370260d0e63703208e23752e4b55a9652e8b55a523a2483d4f53a0e83d65510e838824010e438828074dd38c652745d073dcd52d4b5298c52d8b509493a0c8394e53a0e8394c510c231008010c4310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x3 : Ex t165 7 [v10,u0,u1,u2,u3,u4] :=
  certify c165 [] (unpack 5 0xc91060440100b140b060383099203840386050840080a8540110983048140004005050240040a9140030608400c400d0385400140060488 212 0x631ad63b6e6337b639ad7c0c67b90e7c1107b8c666ada634cd668da636cd7ba527c3107bb0e7c25262b0a6364d62a4a6370dcda5211b06cdb1611a527ba6e7deb77baae7de736366d6298a6358d62a6a2dab629a662da7629aa61145429673148527c1f07ba2e7c2307b9ee6356d6298a6358d6296a2a0e8298a62a128298e62948310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x4 : Ex t165 7 [v13,u0,u1,u2,u3,u4] :=
  certify c165 [] (unpack 5 0xc910a9106040a85099140090a940383400c03840385048840080b0640120983050240024005048140040b1240030608400605084001400d0386 212 0x5ad295b78d5af9c5b529764a57376d76779734a55eaba5a4a95e8ba5a6a97364d767197370d766525b24c5a5695b16c5a649157151164515655117057363173ecf736cd73e315a6c95b22c5a6295b2ccbd631a16c5bd6d5a1631150531485210a3173dcf7360d73e0f735cd5b14c5a5695b16c5a54911cc71144511d07114c51088310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x5 : Ex t165 6 [v14,v15,u1,u3,u4] :=
  certify c165 [] (unpack 5 0xc91099140170a85400a0685038503830a91050840030382098304880481400909920502 148 0x6b463696256b63169463795087ba0e796057b9086816068d036810068d6310508111641056b111043b94a395253b92e3954a3b14a38ce33b1ac38d433ad2b3a1483ad4a3a12839c461148410821114251088410c231008010c8310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x6 : Ex t165 7 [v15,u0,u2,u1,u3,u4] :=
  certify c165 [⟨_,p165x5⟩] (unpack 5 0xc91099106040b120b060502099204880608400c800040080a85401609830685401540050481400140100385050840140383400340130386 212 0x5ad295b76d5af7b5b529734a573f4f7374d73ca55d8d65a4a95d8b65a4c9160a514cd3160c614ca573e737370d73f0f736735e7195a6695e6795a7097369475eb7736ad75e945a6a95da965a6895dab691a94916a591aa69169410a9414c531485173dcf7360d73e0f735cd5b14c5a5695b16c5a5491190611445118e6114451088310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x7 : Ex t165 7 [v14,u0,u2,u1,u3,u4] :=
  certify c165 [⟨_,p165x5⟩] (unpack 5 0xc9109914004401040010a910a850604401306080b0603850a94050803830386400c80004014400304884008098340094019400e0481401840050502 212 0x1086311fa710bbd11c6329e102df9729f872de101024010e031020010e4353e10de252dbe4f5621036a103665231a52366102ddef29f072df1729def159f610c431585610de36d5b429dc72ce3329e272cdce10dc31004010c43101c034a326c1d0349d26c23053d4f6b5ce5354c52d4929ca72950829d07298a410c231004010c4310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x8 : Ex t165 7 [v18,u0,u2,u1,u3,u4] :=
  certify c165 [] (unpack 5 0xc91400406040b120b0603850a9403820386060840080983401a0a8504814013400505024010099140010508400c40180383400340150488 212 0x631ad643706337b641ad7c0c67b90e7c1107b8c662aca634cd628ca636cd160c6d4ad2d62d6148c67ba527c3107bb0e7c252667196364d666596370d7c2707deb77c2b07de736366d6298a6358d62a6a2dab629a662da7629aa61145429673148527c1f07ba2e7c2307b9ee6356d6298a6358d6296a2a0e8298a62a128298e62948310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x9 : Ex t165 7 [v21,u0,u2,u1,u3,u4] :=
  certify c165 [] (unpack 5 0xc9109910a910a850502400909920385400c03820383048840080b06401b09830604401440050481400140100b14050840150608400340180386 212 0x5ad295b78d5af9c5b529734a5767797376d764a55e2b85a4a95e0b85a6a9148a516ab514ab2168a5766527374d76759736525b24c5a5695b16c5a6497363173ecf736cd73e315a6c95e2385a6295e2d8bd631a16c5bd6d5a1631150531485210a3173dcf7360d73e0f735cd5b14c5a5695b16c5a5491190611445118e6114451088310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x10 : Ex t165 6 [v34,v35,u0,u3,u4] :=
  certify c165 [] (unpack 5 0xc9109924017038604880b120b0640200706038340030381098305080502401009910481 148 0x528005162552a3151400795ad7ae0b796057adad501c050da3501a050dc33a1ad3b1ce3a1c83b1ad105ad111c4105ce111ad3ad08395853ad8b395083a508380e03a5493810039c461148410821114251088410c231008010c8310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x11 : Ex t165 7 [v35,u1,u2,u0,u3,u4] :=
  certify c165 [⟨_,p165x10⟩] (unpack 5 0xc910992400c40090386048806040a910a8505020991050806084001800040080b06401f09830706401e40050481401d03834003401c0385 212 0x39ca53a76939f7b3a4a5526d652f4b5274952ed6396e53cad2396c53caf2152d613eef152f713ed6746d6742f0746f7742d610ad6166f7162f710ad654def5268954e93525ef3d695395e53d5f5396855261054e335262954e103ca32396053ca123962510a1013c4f1384d52d4b5258952d8b525493a0c8394e53a0e8394c51088310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x12 : Ex t165 7 [v34,u1,u2,u0,u3,u4] :=
  certify c165 [⟨_,p165x10⟩] (unpack 5 0xc9109920b06400440090386400c04880b120604401c06080b140a850383038540018000401d400305084008098340104022400e0502402140050481 212 0x1080011fa710bbd11c0029ed62ef9b29f872eed61030010ec3102c010f0353ed6d5718d3f0f556d66bad63471833b0e6c6d6366d635f183671835ed62c1ef29ea72c2b029def151f41004015054101e06cdb229dc72c23029e272c1ce10dc31004010c43101c053d4f6b5ce5354c52d4929ca72950829d07298a410c231004010c4310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x13 : Ex t165 7 [v38,u1,u2,u0,u3,u4] :=
  certify c165 [] (unpack 5 0xc910b064004038606040a910b140381038506084008098340230a850502401c40050481400c4009099204884001402103834003401e0508 212 0x6314a643706337b6414a7c0c67e8fa7c0f07e8c662b0a634cd628ca6370d158c6ccb12cdb18148c62ccc62d7182cf132d4c67ba527c2d07bace7c25265ed762a4a65e5762aca7c2707baae7c2b07ba736366d6298a6358d62a6a1145429673148527c1f07ba2e7c2307b9ee6356d6298a6358d6296a29d27298a629d07298a62948310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x14 : Ex t165 7 [v41,u1,u2,u0,u3,u4] :=
  certify c165 [] (unpack 5 0xc9109920b06401003860b1205020991400103810383050840080a85402409830604401d40050481400c40090a940488401e0608400340210385 212 0x5ad295b78d5af9c5b529734a576b7a7376d768a55a7095d8b65a4a95db16148a515f1814b1215ca5a54a5cc711cd718a44a573e52736ed73eef736525b24c5a5695b16c5a6497363173eaf736ad73e315dab65a6295da365a6a9150531485210a3173dcf7360d73e0f735cd5b14c5a5695b16c5a5491190611445118e6114451088310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p165x15 : Ex t165 8 (roots 31) :=
  certify c165 [⟨_,p165x1⟩,⟨_,p165x2⟩,⟨_,p165x3⟩,⟨_,p165x4⟩,⟨_,p165x6⟩,⟨_,p165x7⟩,⟨_,p165x8⟩,⟨_,p165x9⟩,⟨_,p165x11⟩,⟨_,p165x12⟩,⟨_,p165x13⟩,⟨_,p165x14⟩] (unpack 5 0xc910a91060409910a85800b800a800980080992098340080b0604814005050280078006800503838004060880038002800103860385800005080488 160 0x7be107cfb37bfbd7ce109650894f939679994d087ed5b7c1107ed1b7c15094c219675994f53964217b86e7c0307b82e7c070c2821ba068b286aaa02194c009469194e93944007c0907b80e7c0107b88e6a800620885a88a4a00038c003048128c8310400) (by decide +kernel)
theorem l165 : CClaim 31 t165 9 := fromTable 807453318 (by decide +kernel) p165x15

abbrev t166 : Sig := 0xfe80fe8080808080fe80fe8080808080
theorem l166 : CClaim 47 t166 7 := liftTable 32 32 309306901126 7 l113 (by decide +kernel)

abbrev t167 : Sig := 0xfee8fee8fe80fe80fee8fee8fe80fe80
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c167 : Cuts t167 := [
  rule t167 0 l130 (some (2,u0,u1)) (by decide +kernel),
  rule t167 0 l137 none (by decide +kernel),
  rule t167 0 l130 (some (3,u0,u1)) (by decide +kernel),
  rule t167 0 l133 none (by decide +kernel),
  rule t167 4 l134 none (by decide +kernel),
  rule t167 0 l130 none (by decide +kernel),
  rule t167 0 l130 (some (0,u0,u1)) (by decide +kernel),
  rule t167 32 l114 (some (0,u0,u1)) (by decide +kernel),
  rule t167 32 l114 none (by decide +kernel),
  rule t167 1 l142 none (by decide +kernel),
  rule t167 1 l86 none (by decide +kernel),
  rule t167 32 l45 none (by decide +kernel),
  rule t167 0 l141 none (by decide +kernel),
  rule t167 0 l130 (some (1,u0,u1)) (by decide +kernel),
  rule t167 0 l113 none (by decide +kernel),
  rule t167 32 l114 (some (1,u0,u1)) (by decide +kernel),
  rule t167 2 l138 none (by decide +kernel),
  rule t167 32 l114 (some (2,u0,u1)) (by decide +kernel),
  rule t167 32 l114 (some (3,u0,u1)) (by decide +kernel),
  rule t167 0 l130 (some (2,u0,u2)) (by decide +kernel),
  rule t167 0 l130 (some (3,u0,u2)) (by decide +kernel),
  rule t167 0 l130 (some (0,u0,u2)) (by decide +kernel),
  rule t167 32 l114 (some (0,u0,u2)) (by decide +kernel),
  rule t167 32 l41 none (by decide +kernel),
  rule t167 0 l130 (some (1,u0,u2)) (by decide +kernel),
  rule t167 32 l114 (some (1,u0,u2)) (by decide +kernel),
  rule t167 32 l114 (some (2,u0,u2)) (by decide +kernel),
  rule t167 32 l114 (some (3,u0,u2)) (by decide +kernel),
  rule t167 0 l130 (some (2,u1,u2)) (by decide +kernel),
  rule t167 0 l130 (some (3,u1,u2)) (by decide +kernel),
  rule t167 0 l130 (some (0,u1,u2)) (by decide +kernel),
  rule t167 32 l114 (some (0,u1,u2)) (by decide +kernel),
  rule t167 2 l82 none (by decide +kernel),
  rule t167 0 l130 (some (1,u1,u2)) (by decide +kernel),
  rule t167 32 l114 (some (1,u1,u2)) (by decide +kernel),
  rule t167 32 l114 (some (2,u1,u2)) (by decide +kernel),
  rule t167 32 l114 (some (3,u1,u2)) (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x0 : Ex t167 6 [v6,v7,u2,u3,u5] :=
  certify c167 [] (unpack 5 0x14a112a1400b1285400a0583038511a14001038411830481060412a40383400906080488 148 0x6b4c669e276b63169cc67b82179e077ba0e79c216946569826694256986649d674b94e49d474b96b4b16c499264b1ac4996648d434856148d63485414a44811c001088411c87108001188611405118061148510c001048110c8310400) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x1 : Ex t167 7 [v7,u0,u1,u2,u3,u5] :=
  certify c167 [⟨_,p167x0⟩] (unpack 5 0x14a112a1060413241306050212a404880508400c800040081183400712850583400640050481400403834003060840020385400140000386 212 0x5ad295bf6f5af7b5bd29734a573f4f7374d73ca55e4f95a4a95e4b95a4e973e737370d73f0f736735db165a6695da765a70911e731170511f071167373e9475eb773eaf75e945a6a95da965a6895dab691e94916a591ea79169410a9414c531485173dcf7360d73e0f735cd5b14c5a5695b16c5a54911cc71144511d07114c51088310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x2 : Ex t167 7 [v6,u0,u1,u2,u3,u5] :=
  certify c167 [⟨_,p167x0⟩] (unpack 5 0x14a112a11285401011a1400005081306050211a203850386400c800040024001048840081183400f400e0481400d4005060440040383400940030608 212 0x39d083afab39fbd3ad0856c0052f8b56f9b52c00394653a008394053a06852e6b56f3b52f2b56e733d6753a0e83d4f53a268d0f2370260d0e63703208e23752e4b55a9652e8b55a523a2483d4f53a0e83d65510e838824010e438828074dd38c652745d073dcd52d4b5298c52d8b509493a0c8394e53a0e8394c510c231008010c4310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x3 : Ex t167 7 [v10,u0,u1,u2,u3,u5] :=
  certify c167 [] (unpack 5 0x14a10604401013241306038311a203840386050840081285401111830481400040050502400412a140030608400c400d0385400140060488 212 0x631ad63b6e6337b639ad7c0c67b90e7c1107b8c666ada634cd668da636cd7ba527c3107bb0e7c25262b0a6364d62a4a6370dcda5211b06cdb1611a527ba6e7deb77baae7de736366d6298a6358d62a6a2dab629a662da7629aa61145429673148527c1f07ba2e7c2307b9ee6356d6298a6358d6296a2a0e8298a62a128298e62948310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x4 : Ex t167 7 [v13,u0,u1,u2,u3,u5] :=
  certify c167 [] (unpack 5 0x14a112a10604128511a1400912a40383400c038403850488400813064012118305024002400504814004132240030608400605084001400d0386 212 0x5ad295b78d5af9c5b529764a57376d76779734a55eaba5a4a95e8ba5a6a97364d767197370d766525b24c5a5695b16c5a649157151164515655117057363173ecf736cd73e315a6c95b22c5a6295b2ccbd631a16c5bd6d5a1631150531485210a3173dcf7360d73e0f735cd5b14c5a5695b16c5a54911cc71144511d07114c51088310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x5 : Ex t167 6 [v14,v15,u1,u3,u5] :=
  certify c167 [] (unpack 5 0x14a111a140171285400a06850385038312a1050840030382118304880481400911a20502 148 0x6b463696256b63169463795087ba0e796057b9086816068d036810068d6310508111641056b111043b94a395253b92e3954a3b14a38ce33b1ac38d433ad2b3a1483ad4a3a12839c461148410821114251088410c231008010c8310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x6 : Ex t167 7 [v15,u0,u2,u1,u3,u5] :=
  certify c167 [⟨_,p167x5⟩] (unpack 5 0x14a111a1060413221306050211a204880608400c800040081285401611830685401540050481400140100385050840140383400340130386 212 0x5ad295b76d5af7b5b529734a573f4f7374d73ca55d8d65a4a95d8b65a4c9160a514cd3160c614ca573e737370d73f0f736735e7195a6695e6795a7097369475eb7736ad75e945a6a95da965a6895dab691a94916a591aa69169410a9414c531485173dcf7360d73e0f735cd5b14c5a5695b16c5a5491190611445118e6114451088310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x7 : Ex t167 7 [v14,u0,u2,u1,u3,u5] :=
  certify c167 [⟨_,p167x5⟩] (unpack 5 0x14a111a140044010400112a112850604401306081306038512a4050803830386400c80004014400304884008118340094019400e0481401840050502 212 0x1086311fa710bbd11c6329e102df9729f872de101024010e031020010e4353e10de252dbe4f5621036a103665231a52366102ddef29f072df1729def159f610c431585610de36d5b429dc72ce3329e272cdce10dc31004010c43101c034a326c1d0349d26c23053d4f6b5ce5354c52d4929ca72950829d07298a410c231004010c4310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x8 : Ex t167 7 [v18,u0,u2,u1,u3,u5] :=
  certify c167 [] (unpack 5 0x14a14004060413221306038512a403820386060840081183401a12850481401340050502401011a140010508400c40180383400340150488 212 0x631ad643706337b641ad7c0c67b90e7c1107b8c662aca634cd628ca636cd160c6d4ad2d62d6148c67ba527c3107bb0e7c252667196364d666596370d7c2707deb77c2b07de736366d6298a6358d62a6a2dab629a662da7629aa61145429673148527c1f07ba2e7c2307b9ee6356d6298a6358d6296a2a0e8298a62a128298e62948310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x9 : Ex t167 7 [v21,u0,u2,u1,u3,u5] :=
  certify c167 [] (unpack 5 0x14a111a112a112850502400911a20385400c03820383048840081306401b11830604401440050481400140101324050840150608400340180386 212 0x5ad295b78d5af9c5b529734a5767797376d764a55e2b85a4a95e0b85a6a9148a516ab514ab2168a5766527374d76759736525b24c5a5695b16c5a6497363173ecf736cd73e315a6c95e2385a6295e2d8bd631a16c5bd6d5a1631150531485210a3173dcf7360d73e0f735cd5b14c5a5695b16c5a5491190611445118e6114451088310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x10 : Ex t167 6 [v34,v35,u0,u3,u5] :=
  certify c167 [] (unpack 5 0x14a111a24017038604881322130640200706038340030381118305080502401011a10481 148 0x528005162552a3151400795ad7ae0b796057adad501c050da3501a050dc33a1ad3b1ce3a1c83b1ad105ad111c4105ce111ad3ad08395853ad8b395083a508380e03a5493810039c461148410821114251088410c231008010c8310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x11 : Ex t167 7 [v35,u1,u2,u0,u3,u5] :=
  certify c167 [⟨_,p167x10⟩] (unpack 5 0x14a111a2400c400903860488060412a11285050211a1050806084001800040081306401f11830706401e40050481401d03834003401c0385 212 0x39ca53a76939f7b3a4a5526d652f4b5274952ed6396e53cad2396c53caf2152d613eef152f713ed6746d6742f0746f7742d610ad6166f7162f710ad654def5268954e93525ef3d695395e53d5f5396855261054e335262954e103ca32396053ca123962510a1013c4f1384d52d4b5258952d8b525493a0c8394e53a0e8394c51088310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x12 : Ex t167 7 [v34,u1,u2,u0,u3,u5] :=
  certify c167 [⟨_,p167x10⟩] (unpack 5 0x14a111a21306400440090386400c048813220604401c0608132412850383038540018000401d400305084008118340104022400e0502402140050481 212 0x1080011fa710bbd11c0029ed62ef9b29f872eed61030010ec3102c010f0353ed6d5718d3f0f556d66bad63471833b0e6c6d6366d635f183671835ed62c1ef29ea72c2b029def151f41004015054101e06cdb229dc72c23029e272c1ce10dc31004010c43101c053d4f6b5ce5354c52d4929ca72950829d07298a410c231004010c4310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x13 : Ex t167 7 [v38,u1,u2,u0,u3,u5] :=
  certify c167 [] (unpack 5 0x14a1130640040386060412a1132403810385060840081183402312850502401c40050481400c400911a204884001402103834003401e0508 212 0x6314a643706337b6414a7c0c67e8fa7c0f07e8c662b0a634cd628ca6370d158c6ccb12cdb18148c62ccc62d7182cf132d4c67ba527c2d07bace7c25265ed762a4a65e5762aca7c2707baae7c2b07ba736366d6298a6358d62a6a1145429673148527c1f07ba2e7c2307b9ee6356d6298a6358d6296a29d27298a629d07298a62948310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x14 : Ex t167 7 [v41,u1,u2,u0,u3,u5] :=
  certify c167 [] (unpack 5 0x14a111a21306401003861322050211a1400103810383050840081285402411830604401d40050481400c400912a40488401e0608400340210385 212 0x5ad295b78d5af9c5b529734a576b7a7376d768a55a7095d8b65a4a95db16148a515f1814b1215ca5a54a5cc711cd718a44a573e52736ed73eef736525b24c5a5695b16c5a6497363173eaf736ad73e315dab65a6295da365a6a9150531485210a3173dcf7360d73e0f735cd5b14c5a5695b16c5a5491190611445118e6114451088310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p167x15 : Ex t167 8 (roots 47) :=
  certify c167 [⟨_,p167x1⟩,⟨_,p167x2⟩,⟨_,p167x3⟩,⟨_,p167x4⟩,⟨_,p167x6⟩,⟨_,p167x7⟩,⟨_,p167x8⟩,⟨_,p167x9⟩,⟨_,p167x11⟩,⟨_,p167x12⟩,⟨_,p167x13⟩,⟨_,p167x14⟩] (unpack 5 0x14a112a1060411a11285800b800a8009800811a211834008130604814005050280078006800503838004060880038002800103860385800005080488 160 0x7be107cfb37bfbd7ce109650894f939679994d087ed5b7c1107ed1b7c15094c219675994f53964217b86e7c0307b82e7c070c2821ba068b286aaa02194c009469194e93944007c0907b80e7c0107b88e6a800620885a88a4a00038c003048128c8310400) (by decide +kernel)
theorem l167 : CClaim 47 t167 9 := fromTable 103081362054 (by decide +kernel) p167x15

abbrev t168 : Sig := 0xe8e8808080808080e8e8808080808080
theorem l168 : CClaim 55 t168 8 := liftTable 32 32 662230319750 8 l116 (by decide +kernel)

abbrev t169 : Sig := 0xfefefefefefe8080fefefefefefe8080
theorem l169 : CClaim 55 t169 7 := liftTable 0 32 34628223622 7 l115 (by decide +kernel)

abbrev t170 : Sig := 0xee88ee00ee000000ee88ee00ee000000
theorem l170 : CClaim 59 t170 6 := liftTable 48 48 311689219096 6 l41 (by decide +kernel)

abbrev t171 : Sig := 0xffeeff88ff888888ffeeff88ff888888
theorem l171 : CClaim 59 t171 6 := liftTable 32 40 277058945154 6 l54 (by decide +kernel)

abbrev t172 : Sig := 0xfaa0fa00fa000000faa0fa00fa000000
theorem l172 : CClaim 61 t172 6 := liftTable 48 48 311689609240 6 l45 (by decide +kernel)

abbrev t173 : Sig := 0xfffaffa0ffa0a0a0fffaffa0ffa0a0a0
theorem l173 : CClaim 61 t173 6 := liftTable 32 40 277058961412 6 l58 (by decide +kernel)

abbrev t174 : Sig := 0xfcc0fc00fc000000fcc0fc00fc000000
theorem l174 : CClaim 62 t174 6 := liftTable 48 48 346319883264 6 l49 (by decide +kernel)

abbrev t175 : Sig := 0xfffcffc0ffc0c0c0fffcffc0ffc0c0c0
theorem l175 : CClaim 62 t175 6 := liftTable 32 40 277058978304 6 l62 (by decide +kernel)

abbrev t176 : Sig := 0xfee8fe80fe808080fee8fe80fe808080
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c176 : Cuts t176 := [
  rule t176 16 l167 (some (2,u0,u1)) (by decide +kernel),
  rule t176 16 l167 none (by decide +kernel),
  rule t176 16 l167 (some (0,u0,u1)) (by decide +kernel),
  rule t176 0 l172 none (by decide +kernel),
  rule t176 1 l175 none (by decide +kernel),
  rule t176 1 l152 none (by decide +kernel),
  rule t176 1 l159 none (by decide +kernel),
  rule t176 16 l137 none (by decide +kernel),
  rule t176 0 l174 none (by decide +kernel),
  rule t176 2 l148 none (by decide +kernel),
  rule t176 2 l156 none (by decide +kernel),
  rule t176 16 l167 (some (3,u0,u1)) (by decide +kernel),
  rule t176 0 l170 none (by decide +kernel),
  rule t176 0 l168 none (by decide +kernel),
  rule t176 8 l169 none (by decide +kernel),
  rule t176 0 l166 none (by decide +kernel),
  rule t176 0 l164 none (by decide +kernel),
  rule t176 32 l165 none (by decide +kernel),
  rule t176 16 l133 none (by decide +kernel),
  rule t176 32 l119 none (by decide +kernel),
  rule t176 4 l171 none (by decide +kernel),
  rule t176 16 l167 (some (1,u0,u2)) (by decide +kernel),
  rule t176 16 l167 (some (3,u0,u2)) (by decide +kernel),
  rule t176 16 l167 (some (1,u1,u2)) (by decide +kernel),
  rule t176 16 l167 (some (3,u1,u2)) (by decide +kernel),
  rule t176 4 l144 none (by decide +kernel),
  rule t176 20 l134 none (by decide +kernel),
  rule t176 3 l163 none (by decide +kernel),
  rule t176 0 l168 (some (0,u0,u1)) (by decide +kernel),
  rule t176 32 l165 (some (0,u0,u1)) (by decide +kernel),
  rule t176 17 l142 none (by decide +kernel),
  rule t176 33 l128 none (by decide +kernel),
  rule t176 32 l123 none (by decide +kernel),
  rule t176 1 l162 none (by decide +kernel),
  rule t176 4 l156 none (by decide +kernel),
  rule t176 17 l86 none (by decide +kernel),
  rule t176 33 l62 none (by decide +kernel),
  rule t176 48 l45 none (by decide +kernel),
  rule t176 2 l173 none (by decide +kernel),
  rule t176 16 l141 none (by decide +kernel),
  rule t176 2 l162 none (by decide +kernel),
  rule t176 3 l112 none (by decide +kernel),
  rule t176 16 l167 (some (0,u0,u2)) (by decide +kernel),
  rule t176 16 l167 (some (2,u0,u2)) (by decide +kernel),
  rule t176 16 l167 (some (0,u1,u2)) (by decide +kernel),
  rule t176 16 l167 (some (2,u1,u2)) (by decide +kernel),
  rule t176 0 l168 (some (1,u0,u1)) (by decide +kernel),
  rule t176 16 l167 (some (1,u0,u1)) (by decide +kernel),
  rule t176 32 l165 (some (1,u0,u1)) (by decide +kernel),
  rule t176 5 l160 none (by decide +kernel),
  rule t176 4 l159 none (by decide +kernel),
  rule t176 0 l168 (some (2,u0,u1)) (by decide +kernel),
  rule t176 32 l165 (some (2,u0,u1)) (by decide +kernel),
  rule t176 0 l168 (some (3,u0,u1)) (by decide +kernel),
  rule t176 32 l165 (some (3,u0,u1)) (by decide +kernel),
  rule t176 18 l138 none (by decide +kernel),
  rule t176 0 l168 (some (0,u0,u2)) (by decide +kernel),
  rule t176 32 l165 (some (0,u0,u2)) (by decide +kernel),
  rule t176 48 l41 none (by decide +kernel),
  rule t176 5 l112 none (by decide +kernel),
  rule t176 0 l168 (some (1,u0,u2)) (by decide +kernel),
  rule t176 32 l165 (some (1,u0,u2)) (by decide +kernel),
  rule t176 0 l168 (some (2,u0,u2)) (by decide +kernel),
  rule t176 32 l165 (some (2,u0,u2)) (by decide +kernel),
  rule t176 0 l168 (some (3,u0,u2)) (by decide +kernel),
  rule t176 32 l165 (some (3,u0,u2)) (by decide +kernel),
  rule t176 16 l167 (some (1,u0,u3)) (by decide +kernel),
  rule t176 32 l165 (some (1,u0,u3)) (by decide +kernel),
  rule t176 16 l167 (some (3,u0,u3)) (by decide +kernel),
  rule t176 16 l167 (some (2,u0,u3)) (by decide +kernel),
  rule t176 16 l167 (some (0,u1,u3)) (by decide +kernel),
  rule t176 16 l167 (some (3,u1,u3)) (by decide +kernel),
  rule t176 16 l130 (some (0,u0,u1)) (by decide +kernel),
  rule t176 32 l116 (some (0,u0,u1)) (by decide +kernel),
  rule t176 16 l130 (some (2,u0,u1)) (by decide +kernel),
  rule t176 32 l116 (some (2,u0,u1)) (by decide +kernel),
  rule t176 16 l167 (some (0,u2,u3)) (by decide +kernel),
  rule t176 16 l167 (some (3,u2,u3)) (by decide +kernel),
  rule t176 16 l130 (some (0,u0,u2)) (by decide +kernel),
  rule t176 32 l116 (some (0,u0,u2)) (by decide +kernel),
  rule t176 16 l130 (some (2,u0,u2)) (by decide +kernel),
  rule t176 32 l116 (some (2,u0,u2)) (by decide +kernel),
  rule t176 16 l167 (some (0,u0,u3)) (by decide +kernel),
  rule t176 16 l130 (some (1,u0,u1)) (by decide +kernel),
  rule t176 32 l116 (some (1,u0,u1)) (by decide +kernel),
  rule t176 16 l130 (some (3,u0,u1)) (by decide +kernel),
  rule t176 32 l116 (some (3,u0,u1)) (by decide +kernel),
  rule t176 16 l130 (some (1,u0,u2)) (by decide +kernel),
  rule t176 32 l116 (some (1,u0,u2)) (by decide +kernel),
  rule t176 16 l130 (some (3,u0,u2)) (by decide +kernel),
  rule t176 32 l116 (some (3,u0,u2)) (by decide +kernel),
  rule t176 32 l165 (some (2,u0,u3)) (by decide +kernel),
  rule t176 6 l112 none (by decide +kernel),
  rule t176 0 l168 (some (0,u1,u2)) (by decide +kernel),
  rule t176 6 l157 none (by decide +kernel),
  rule t176 32 l165 (some (0,u1,u2)) (by decide +kernel),
  rule t176 34 l124 none (by decide +kernel),
  rule t176 18 l82 none (by decide +kernel),
  rule t176 34 l58 none (by decide +kernel),
  rule t176 32 l127 none (by decide +kernel),
  rule t176 0 l168 (some (1,u1,u2)) (by decide +kernel),
  rule t176 32 l165 (some (1,u1,u2)) (by decide +kernel),
  rule t176 0 l168 (some (2,u1,u2)) (by decide +kernel),
  rule t176 32 l165 (some (2,u1,u2)) (by decide +kernel),
  rule t176 0 l168 (some (3,u1,u2)) (by decide +kernel),
  rule t176 32 l165 (some (3,u1,u2)) (by decide +kernel),
  rule t176 16 l167 (some (1,u1,u3)) (by decide +kernel),
  rule t176 32 l165 (some (1,u1,u3)) (by decide +kernel),
  rule t176 16 l167 (some (2,u1,u3)) (by decide +kernel),
  rule t176 16 l130 (some (0,u1,u2)) (by decide +kernel),
  rule t176 32 l116 (some (0,u1,u2)) (by decide +kernel),
  rule t176 16 l130 (some (2,u1,u2)) (by decide +kernel),
  rule t176 32 l116 (some (2,u1,u2)) (by decide +kernel),
  rule t176 16 l130 (some (1,u1,u2)) (by decide +kernel),
  rule t176 32 l116 (some (1,u1,u2)) (by decide +kernel),
  rule t176 16 l130 (some (3,u1,u2)) (by decide +kernel),
  rule t176 32 l116 (some (3,u1,u2)) (by decide +kernel),
  rule t176 32 l165 (some (2,u1,u3)) (by decide +kernel),
  rule t176 16 l167 (some (1,u2,u3)) (by decide +kernel),
  rule t176 32 l165 (some (1,u2,u3)) (by decide +kernel),
  rule t176 16 l167 (some (2,u2,u3)) (by decide +kernel),
  rule t176 32 l165 (some (2,u2,u3)) (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x0 : Ex t176 7 [v6,v7,u2,u3,u4,u5] :=
  certify c176 [] (unpack 5 0x4007199319a314a116284006400513a5158b0b950d8b0d93078d038519b1400303841489160c0c8914a80e0c0c910e141ab4038340040e180c98 228 0xe6d29e2f4be6f5be2d29b2ccbb6f39b2f2bb6cc6b2729b68c6b24c9b6b39ba863baf0bbab0abac63b9c63ba429b9c27ba463b1463b1826b1425b18636d1ef6aeab6d2b46adef6c9ef6a6696ca726a5ef6c5ef69a066c610699ef68dc3685ef68de3685c16b44c12c0b1290a12d0b1280a1250911c071240911d071188611405118061148510c031048110c8310400) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x1 : Ex t176 8 [v10,v7,u1,u2,u3,u4,u5] :=
  certify c176 [⟨_,p176x0⟩] (unpack 6 0x4007199319a314a11628160c0e0c400a0e14400915281b340d1813a6158b0b960d8b0d93078e038619b20e1803841489150a0c8914a80d0a0c910d121ab41ab10c980383400880004003400040024001 300 0x9e638e9d09509e69669d038e7902d07a69247909107a62cb78e90e7a52cb78e2ce7a59248221868108d08228e281018682118680e48e8214a180e18679f18678b48b79f49f78b1860cf6cf0d07500cf74f0d06d00cc74c0ce6ce0cc6cc0ce74e0ca70a0cb6cb0ca6ca0cb70b0c66c60d27120c67060d26db0d95140d06900d96990d05140d75140ce60e0d76170ce5140d65140cb54b0d65550cb5140c64c60d25140c65060d24d20c30d11501d014f34f15035014f1cf14e34e14c1cc14e1ce14c34c14b24b14a1ca14b1cb14a24a1481c71462461482481461c60c50c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x2 : Ex t176 8 [v13,v7,u0,u2,u3,u4,u5] :=
  certify c176 [⟨_,p176x0⟩] (unpack 6 0x4007199319a314a11628160c0e0c40060e14400514a81ab40c9813a5158b0b950d8b0d93078d038519b10e180384150a14890d0a15280c890d120c911b341b320d180383400880004003400b40024001 300 0x9e630c9cf94f9e69669cf30c78f28f7a692478f90f7a628a78c90c7a528a78c28c7a592482218680f8cf8228e280f18682118680c48c8214a180c18679f18678a48a79f49f78a18614f6cf15075014f74f1506d014c74c14e6ce14c6cc14e74e14a70a14b6cb14a6ca14b70b1466c61527121467061526db0d95140cf68f0d96990cf5140d75140cc60c0d76170cc5140d65140ca54a0d65550ca5140c64c60d25140c65060d24d20c31510d01d00cf34f0d03500cf1cf0ce34e0cc1cc0ce1ce0cc34c0cb24b0ca1ca0cb1cb0ca24a0c81c70c62460c82480c61c60c31440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x3 : Ex t176 8 [v117,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40131993401219a314a115281b341b32150a14a80d0a0d1219b219b10d181ab40c98160c0e0c16280e180e141ab14011401014894001400f0c89400e400d0c914003038540080386400c0383 300 0x8e42498cc88c8e48a48cc24994c18c96486194c84c9641868c98498e21868c91898e286115d5dd14c80c15d81d14c5cc15b81b1495c915b5db14980915a61a1465c615a5da14660605e5d70517d105e7de0515d70cc54c0dd71d0cc70c0dd55d0c97090db55b0c95490db71b0c66460da55a0c65460da65a15855515765715865815755504f55505159104f58f05155505445404c48c05449404c44c0534930494490534530494890503d00464460504500463c604134d04c38c04138e04c34c04128a0492c90412cb0492890411c70462060412080461c60411440410c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x4 : Ex t176 8 [v149,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x4007401a1993401919a314a11528400a4018401714a8150a0d0a0d12400603850d1840164015038640080c9813a30b93078b038340030e184011160c4010148940010e0c400f0c89400e0e144014400d0c91 324 0xa261459c9909a269269c91459490099668e39498c99660009458c59640009450059648e385d65938988985d89d38965985c65938560585c61c38565985b65938060085b61b38065908f60f38e65908f64f38e6180a061838e65909f65938e61868955551d79d68978951d55568555551c4dc6854c551c55568055551b4db6804c051b5553994d95185556995593984d308f4cf51455508f54f5144d30974d35145550965555144d308b3cf08948908b48b0893cf0873cf0854450874470853cf0833cf0804000834030803cf38e38d08b28b08930908b30b089289087187085205087207085185083043080100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x5 : Ex t176 8 [v150,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40071993401919a314a115281b3214a8150a0d0a0d1203850d1803860c98160c0e0c16280e180e141ab14011158b4010148940010d8b400f0c89400e0d93400d0c9119b1400819b2400340140383 300 0x9a528a98e8ce9a58e598e28a90e18e9258a290e88e92518690a88a92318690a18a9238a209e6db08e84e09e85e08e6db09d6db08a68a09d69d08a6db09c6db08668609c69c0866db0a069a0946db0a06db09469a10e65911e7de10e7ce11e65910a65911d61d10a60a11d65910665911c61c10660611c65909b61b09a65909b65b09a61811261811465911265911461805751704e54e05755704e50e05655604a50a05651604a54a0534930465060535130464860903d008e44e09045008e3ce08c2cc08a34a08c34c08a2ca0881c80862460882480861c6082085082103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x6 : Ex t176 8 [v118,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40131993401219a314a11528400a150a14a80d0a0d12400619b219b113a30b93078b03834011160c4010148940010e0c400f0c89400e0e14400d0c91400340181b3440170d180385400840161ab440150c980386400c0e18 324 0xa6a492a56a16a6aa2aa56492ad6396aea9e7ad69d6aea38ea529d2a6838ea52392a689e79642643569969649a43562569629a23522529622623529929617a134e24e96126134e78e05a25a04d2cb05a2da0412498160d61e48e48168d61e40e48128d21e20e28120d21e28e280e7ce1e10e180e0ce1e17e135e0c31c97c981e7de3490c305a0da04714505a15a0410c305869a05675605875805669a05469a05271205471405269a05069a04e6ce0506d004e69a0585d80566560586580565d60544d40525520545540524d20503d004e44e05045004e3ce04b34b04930904b2880490480451c5043183045102043042041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x7 : Ex t176 7 [v151,v6,u2,u3,u4,u5] :=
  certify c176 [] (unpack 5 0x4007401e199319a314a1162813a40b94078c038440040d980e1813a51489160c0b950c8940210e0c078d0c9140050e141ab10385400619b1038340030c98 228 0xf71adec370f737cec1ad441304735a44350471294374d46d294352d46f5a23c422433023f2f2404222c422364d22e4b2344241c424264941e4742442a42b0a3f0fa4310a3eafa36ada2eeba36eda2eaba26a9a1ec7a26c9a1ea7a0a62a4ab2a0aa2a4a72640a563e2f6423063ca5634a562dcb635cd62ca5424a541d474254941ca521863208a2218a52086208420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x8 : Ex t176 7 [v151,v7,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40201993400719a314a11628402213a4158b0b940d8b078c0d9303840d980e181489160c0c8914a80e0c0c9140050e1440211ab41ab140060c980383400440030385 228 0x79f38e79075079f75f79038e8102d029f71c81071029f2cb78e70e29d2cb78e2ce29d71c68f0c31506d068f6cf1500c368c0c314e44e68c44c14e0c32890c314b44b68944928b0c30584d80506500586580504d00564d604e5ce0565d604e4ce0544d404b54b05455404b4cb0434830514d10434c305149121011020f34f21035020f10f20e34e20c10c20e10e20c34c28b1cb20910920b10b2891c91461042031c32061c6143103042040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x9 : Ex t176 8 [v6,v7,u2,u3,u4,u5] :=
  certify c176 [⟨_,p176x7⟩,⟨_,p176x8⟩] (unpack 6 0x402540241993402319a314a11628402213a5158b0b950d8b0d93078d401b0385400319b1402180018000038440201489401f160c40070c89401e14a80e0c0c9140050e1440041ab4038340060e180c98 228 0x36530c4508d03658e59d030c9902101e58a24508901e520890c88c1e320834c20c1e38a280e0c309085080e84e0900c38090c308c04c80904908c0c31c60c30880488060461c80c365e6185d07d065e7de5d061865c6185cc74c65c75c5cc6181db6185c868865b69a5c86180835835c16186436035c15815544d215001044e28e1502903ce00e14c28c34900914c00c2c92891481081c60061480081c6106143003081101143103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x10 : Ex t176 7 [v151,u1,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x4007199319a314a11628400a400913a4150a0b940d0a078c0d120d980e1814a81489160c0c890e0c0c9140050e1440211ab14006038340040386400303840c980385 240 0x81f38e81079081f79f81038e6903102df75d6907502df30c68e74e2de30c68e30e2de75d6cf1861d07106cf70f1d01866cd1861ce48e6cd48d1ce1862ca1861cc48c68a48a2cc1860d80980d06500d86580d00900d60960ce5ce0d65d60ce08e0d40940cc54c0d45540cc08c0c64c60d20920c60860d24d225010424f44f25045024f10424e10424d04d24e04e24d1042cc10424a04a24c04c2ca1041c80412461062481041c60460c30410c21040c51000c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x11 : Ex t176 8 [v6,u1,v7,u2,u3,u4,u5] :=
  certify c176 [⟨_,p176x10⟩] (unpack 6 0x4007199319a314a11628400a40064009400513a6158b0b960d8b0d93078e038619b203858000150a0d0a0d12400340080d181489160c0c8914a80e0c0c910e1440041ab4038340260e180c98 300 0x96428a94c8cc9648e494c28a78c1cc7648a278c88c7641c778a88a7631c778a1ca7638a280b0c37cc84c80b84b7cc0c38080c37ca04a8080487ca0c37460c37c70477860467470c33db5963cc70c3db71b3cc5963d95963ca68a3d96993ca5963d85963c75c73d85d73c75963c35433c15963c35833c15413cf3d43cf0933d20923cc3cc3d20923cc3cc3d10913ca3ca3d10913ca3ca3d00903c73c73d00903c73c73c30833c13c13c30833c13c13cf38d14c00c08b24b14c24c08b00b14a24a08800814a00a088248147107086006147007086106143003081101143103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x12 : Ex t176 7 [v151,u0,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40074027199319a314a1162813a4150a0b940d0a078c0d120d980e1815281489160c0c8940210e0c0c9140050e141ab1400603830c98400340040385400803840d180386 240 0x85f41081279285f79f81241031235231f75d31275231f34d31075031e34d31035031e75d25120825271225171125220824e20825051024e50e25020830b20830d50d30b50b30d2080d20920da6da0d26d20da09a0d00900d86580d06500d80980cd08d0d65d60cd5cd0d60960c85480d40940c80880d45543d21043d14d13d24d23d11043d01043ce04e3d00503ce10430d10430b04b30d04d30b10424a04124810824a1042480481860471821040c51040c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x13 : Ex t176 8 [v6,u0,v7,u2,u3,u4,u5] :=
  certify c176 [⟨_,p176x12⟩] (unpack 6 0x40074027199319a314a116284006400513a5158b0b950d8b0d93078d038519b103868000150a0d0a0d12400840030c981489160c0c8915280e0c0c910e141b34038340040e180d18 300 0x8e124988b80b8e182188b24970b18b7217df70b7cb7211867097c97201867091897207df74a0c374b78b74a78a74b0c37470c37490497470477490c37050c37060467050457060c339a55534b6cb39a6da34b55539855534964939865834955539755534658639759634655538350334155538354334150138e39338e09238b08b39139138b08b39139138908939039038908939039038608638f38f38608638f38f38308338138138308338138134d34c08b00b08a20a08b20b08a00a089209087007089009087207086106085005086006085105083003081101083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x14 : Ex t176 9 [v7,u0,u1,u2,u3,u4,u5] :=
  certify c176 [⟨_,p176x1⟩,⟨_,p176x2⟩,⟨_,p176x3⟩,⟨_,p176x4⟩,⟨_,p176x5⟩,⟨_,p176x6⟩,⟨_,p176x9⟩,⟨_,p176x11⟩,⟨_,p176x13⟩] (unpack 6 0x199319a314a11628160c0e0c402940220e14152840281b34150a14a80d0a0d121ab40c980d1840218008800780064011158b401d148940010d8b40020c89400e0d93401c400d0c9180058004401b8003038380020e1840038001400b03854008800040000386 308 0x572514558c58572c725585146583d8672c30658c186723cf554c145713cf5543d4571c3066e28a658bd866ebee65828a56d28a55421456d22d55428a46a28ab0f20faea22a44f28a666826658a58666a66658818564a64554814564824554a544639e31cf80fa2382344f9cfa0a80a1c89c8a0a9ca1c882065885866696665895866686655495456486455485456496444f88f0e38637cf84f4638a37ca84a0c88887ca88a0c88611c68610e00a07de75c65a65a6586d865a6da6586585565565545d45565d65545544524121cf4cf3124d244f40f30a38a1c834830a2ca1c82481c61440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x15 : Ex t176 8 [v152,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40131993401219a314a115284021402d402c14a8150a0d0a0d124026038540060d18402b40040386402a0c98160c0e0c162840050e180e144011168d4010148940010e8d400f0c89400e0e95400d0c91400c0383 324 0x9e81869ca98a9e89a89ca186a4a08a428965a4a94a4280829c69464260829c608642696571f6db8ca90a71f91f8ca6db71e6db8c664671e65e8c66db71d6db8c264271d65d4026db04165904f6db05c6db04f6590416590626db05c6db0616595ca59669f81f5ca80a69f5965c659669e51e5c650669e5965c259641d51d5c250241d5965db51b7195965db59b69951404151404f59605759604f5140415140585960575960555140533d304a44a05345304a3ca0524520463c60523d204644604e40e0423c204e3ce04204204c2cc04a34a04c34c04a2ca0481c80462460482480461c60440c40421420441440420c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x16 : Ex t176 8 [v67,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x401e1993400519a314a113a50b95078d1ab119b140260d1813a6150a0b960d0a078e0d1203851b341ab403861b3219b20c9813a3160c0b930e0c078b0e14038340140e1840111489401040010c89400f400e0c914004400d 300 0xaea145ac8a08aeaa2aac8145a48088a6a9e7a489c8a6a082a459c5a68082a45085a689e785e65984898885e99e84865985c65984594585c95c84565985a65984290285a91a84265984c88c86365984c64c8638a206106004859605e7de0487c805e59604559605c75c04574505c59604259605a6da0426c205a5960595d90585960595990585d704c50c05559604c58c0555140410532d130c2c84882d14912c830c2cf30c2c54052cf40f2c530c2cd30c2c23822cd38d2c230c04b04a0481c80412490482480411c70451050411860451850411040420020410c30420c2041000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x17 : Ex t176 8 [v68,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x401e401a1993401919a314a113a50b954021078d13a6150a0b960d0a078e0d1240061b341ab416280e184005401114894010160c40010c89400f0e0c400e0c91400d0e14402c0d184008402619b1402d0385402a0c98400319b24014402b038640040383 324 0xc6f596c1ab5ac6fb6fc1a596b9a49a72fb2cb9ab1a72f492b96b1672d492b9649672db2c326249a5aada326ae6a5a249324249a56a96324aa4a56249322249a52a12322a2271224930c2cb11d24930c24911d2dd05a0828669e605a9da8660820560828649640569568640820520827228e20528d27220820497c93200820490898607df04114511d08204108211d15d11875811a79a11879811a75a11479411675611475411679611011011275211075011271211a65a1186d811a6da1186581165561145d41165d61145541124521104d01124d211045010b3ce30934930b30b1092891052070421820450451020c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x18 : Ex t176 8 [v153,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40121993400519a314a115281ab114a8150a0d0a0d1203850d1803861b320c9813a30b93078b03834011160c4010148940010e0c400f0c89400e0e14400d0c9140261b3440041ab4400c0e18 300 0x96428a94e88e9648a494e28a8ce18e8e48618ce84e8e41868ca84a8e21868ca18a8e286115d69a14e80e15d81d14e69a15c69a14a64a15c65c14a69a15b69a14664615b65b14669a05265205f69a05269205f6590ce6180dd79d0ce78e0dd6180ca6180dc59c0ca58a0dc6180c66180db59b0c65860db6180da59a0d96180da61a0d959605259205761805261205759605049204e54e05055004e49204c49204a50a04c50c04a4920484920464c60484c80464920503d004e44e05045004e3ce04c2cc04a34a04c34c04a2ca0481c80462460482480461c60411440410c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x19 : Ex t176 8 [v13,v6,u1,u2,u3,u4,u5] :=
  certify c176 [⟨_,p176x0⟩] (unpack 6 0x4007199319a314a116284006400513a50b95078d038519b10384160c14a80e0c0e141ab440040e180c9813a6150a14890b960d0a0c89078e0d120c911b32038619b2038380004003400b402f4001 300 0x9a530c98f90f9a592598f30c80f24f8258e380f8cf82524980c8cc82424980c24c8248e385914584f88f85989984f14585714584c4cc8574d784c1458161458094c98164d68091450d071c0cf7cf0d07d00cf71c0cd71c0cc78c0cd78d0cc71c0ca71c0c97490ca74a0c971c0c56c50d371c0c57050d36d30c351a50f48f51961950f60f51949950c60c51749750c48c5176175095495164965094895165565054855135535055455134920d01c70cf44f0d04500cf1c70cd1c70cc38c0cd38d0cc1c70ca1c70c92c90ca2ca0c91c70c81860c51c50c81c70c51850c30c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x20 : Ex t176 8 [v10,u0,v6,u2,u3,u4,u5] :=
  certify c176 [⟨_,p176x0⟩] (unpack 6 0x4027199319a314a1162840064005160c15280e0c0e141b340d1813a60b96078e038619b20e184004038413a51489150a0b950c890d0a078d0c910d121ab1038519b103834000402f400140088000 300 0x9a534d9909109a592599034d8102908258e38108d082528a80d8cd82428a80d28d8248e385f14585089085f89f85014585d14584d50d85d51d84d14581c14580a50a81c51c80a1454d06904df79f4d07904df69f4cd78d4dd69d4cd68d4dd79d4ca6ca4dc69c4ca68a4dc6dc4c56854d46d44c56c54d469a05059604f64f05065004f59604d59604c60c04d60d04c59604a5960495c904a5ca0495960455450545960455850545540414d20501c704f44f05045004f1c704d1c704c38c04d38d04c1c704a1c70492c904a2ca0491c70481860451c50481c70451850440c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x21 : Ex t176 9 [v6,u0,u1,u2,u3,u4,u5] :=
  certify c176 [⟨_,p176x15⟩,⟨_,p176x16⟩,⟨_,p176x17⟩,⟨_,p176x18⟩,⟨_,p176x19⟩,⟨_,p176x9⟩,⟨_,p176x11⟩,⟨_,p176x13⟩,⟨_,p176x20⟩] (unpack 6 0x199319a314a11628403113a50b95078d19b140000d1813a6150a0b960d0a078e0d1219b203854026800803864021800780068005400b80040c98401114894030160c40010c89402f0e0c4005400e0c91402e400d0e1480038002400480010383400680000e18 308 0x3f24103d4c543f2c723d44104d42d44f2c304d4c144f22cb3d0c103f12cb3d02d03f1c304d20c34d4bd44d2bd24d40c33ce0c33d00103ce00e3d00c32880c308b00bb8800828b0c34e68204d4b544e6b664d48203e48203d0b103e4b243d08202a282070bacb7e2ae228b8207c3a837008207c3803080a807e97a84d475d4e69e64d49d44e675d3d075d3e49643d09503e475d28b75d3628e214b8cb2a275d14384308075d1437430808401605e07de75d71b6991585d64d44d44d25524d45544d24d23d03d03ce44e3d04503ce3ce28b24b34830814b30b2882481431c3080180143103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x22 : Ex t176 8 [v154,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40121993400919a314a115281b3414a8150a0d0a0d1219b10d1803860c981628160c0e0c0e180e1403834011168d4010148940010e8d400f0c89400e0e95400d0c914026038540081ab4400c1ab1 300 0x9a528a98e8ce9a58e598e28a90e18e9258a290e88e92518690a88a92318690a18a9238a215e69e14e84e15e85e14e68e15d85d14a68a15d69d14a84a15c6dc14668615c69c1466c605269205481405281205469a0ce6590de7de0ce7ce0de6590ca6590dd61d0ca60a0dd6590c66590dc61c0c66060dc6590db6180da6590db6590da61805261205465905265205461805649204e5ce0565d604e49205549204a50a05551504a4920534920465060535130464920503d004e44e05045004e3ce04c2cc04a34a04c34c04a2ca0481c80462460482480461c60411440410c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x23 : Ex t176 8 [v8,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x4027401a19934019400919a314a115284021402d4004402c13a60b96078e4006402603851ab40d1840160c9840034015038619b2160c0e0c400a0e141ab140080383401114894010150a40010c89400f0d0a400e0c914014400d0d12 324 0xb6b1c7b0ba0bb6ba2bb0b1c7a8b0cba6b9e7a8b9cba6b0c3a879c7a680c3a870c7a689e774971c94b98b74998994b71c74571c94768774568594771c74071c94368374068094371c75d69a08f71c75d71c08f69a75d69a0a471c76371c0a269a78b55538984978b84b3895557875553858057878073855557835553807c07837c338055579c6dc39a55575c55c39a6da08f50f38e55508f55538e51409951839755509655538e51409309308b3cb0933d308b44b0920920873c70923d20874470903d00834430900900833c338e38d08b28b08930908b30b089289087187085205087207085185083043080100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x24 : Ex t176 8 [v155,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40271993400919a314a1152813a60b96078e03851ab40d18038619b21628160c0e0c0e180e140383401114894010150a40010c89400f0d0a400e0c91400d0d12402619b10c98400840141ab1 300 0x96430c9508909648a495030c8d02108e48618d08508e42088cc84c8e22088cc20c8e286114e71c15081014e80e15071c14a71c14c68c14a68a14c71c14671c14868814668614871c15269215471c15271215469a09065908e7ce0907d008e65908c65908a78a08c78c08a65908865908674608874808665909c6dc09a65909c65c09a6da0926120946590926520946140564920505d00565d605049205549204c50c05551504c4920534920485080535130484920903d008e44e09045008e3ce08c2cc08a34a08c34c08a2ca0881c80862460882480861c6082144082083082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x25 : Ex t176 8 [v9,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x401319934012400919a314a115284021402d03851b34402c14a8150a0d0a0d124006402619b10d1840164008401503860c9840321ab14011160c4010148940010e0c400f0c89400e0e14400d0c91400c0383 324 0x9a718698a90a9a792798a186a0a08a9678e3a0a8ca9670829868c69640829860869648e35db55b84a88a5db89b84a54a5da89a8465465da55a8468865d95998425425d955984258204155504e78e05779e04e55504155f06079f05779e05d55560a4514db71b60a70a4db4516064514da41a6064064da4516024514d94196024024d94516164104d54515d64514d541004e41005345104e45104141005441005345105245104141004c3cc04a38a04c38c04a04a0483c80463860483880460460443840420420443c404238204c2cc04a34a04c34c04a2ca0481c80462460482480461c60440c40421420441440420c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x26 : Ex t176 8 [v13,u1,v10,u2,u3,u4,u5] :=
  certify c176 [⟨_,p176x10⟩] (unpack 6 0x4007199319a314a11628160c400a0e0c400640090e14400514a81ab41ab140080c98400403854026800013a40b94078c03840d980e1813a6150a14890b960d0a0c89078e0d120c911b32038619b2038340030d18 300 0xa68249a4c9cca689e8a4c24980c18c7a89a680c98c7a81868099897a71868091897a79a68e408284c94c8e496484c0828e20828493c98e23e284908279f0828463c681f3df78608258c64c68d74d58c74c68d64d58974968a64a58964968a74a58670668764758664668770759b65968270259b71b68264205805705605504d44d04c50c04d50d04c44c04a44a0494c904a4ca04944904744704648604748704644604240204f44f04244204f40f04d10404c38c04d38d04c10404a1040492c904a2ca0491040471040462060472070461040450c30421020451040420c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x27 : Ex t176 8 [v13,u0,v10,u2,u3,u4,u5] :=
  certify c176 [⟨_,p176x12⟩] (unpack 6 0x40074027199319a314a11628160c0e0c40060e14400513a50b95078d1ab1038519b10c98800013a40b94078c03840d980e18150a14890d0a15280c890d120c911b341b3240030d180383400440080386 300 0x9e528a98d90d9e592598d28a74d20d7658e374d8cd76520874a8ca76420874a20a7648e37e10c37cd88d7e18a17cd0c37e00c37ca3ca7e03e07ca0c375e0c37483c875e3de7480c304d61804e70e04d70d04e61804a61804c6cc04a6ca04c6180486180496890486880496180595d70436030596180435c314515604109504d44d04e50e04d50d04e44e04a44a04c4cc04a4ca04c44c04844804948904848804944904340304f44f04344304f40f08e10e14d2cd08e2ce14d10d08c2cc14a10a08c10c14a2ca0891c91481080891091481c80861041431c30861c6143103042040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x28 : Ex t176 9 [v10,u0,u1,u2,u3,u4,u5] :=
  certify c176 [⟨_,p176x1⟩,⟨_,p176x20⟩,⟨_,p176x22⟩,⟨_,p176x23⟩,⟨_,p176x24⟩,⟨_,p176x25⟩,⟨_,p176x26⟩,⟨_,p176x27⟩] (unpack 6 0x199319a314a11628160c0e0c400a40320e1415281b3413a60b96078e19b20e1880078006038403860d18401114894034150a40010c8940000d0a400e0c914033400d0d1280058004402180031ab18002038340268001402f03854008800040020c98 308 0x57059655abda570bf055a59665a49a670bae65ab9a670492556b9656f49255649656fbae66c20865ab5a66cb6c65a20856b20855685656b86b556208468208a92852a6886845220865871865a9da6589d865a71a5549d45567165547145569d644f98f3127121cf70f4529921c87083219a11c898832171c65a75d65895865a95a65875d55675d55491455691655475d45275d0cf8cf3128d244f75d3088880e175d3087480e18a13207de1c675d0dc09c65a65a6586d865a6da6586585565565545d45565d65545544524120cf4cf3124d244f40f30a38a0c834830a2ca0c82481c61440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x29 : Ex t176 8 [v156,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40121993400519a314a11528150a14a80d0a0d1219b203850d181ab40c981628160c0e0c0e180e1403834011170e4010148940010f0e400f0c89400e0f16400d0c9140031b3440040386400c1b32 300 0x9a528a98e8ce9a58e598e28a90e18e9258a290e88e92518690a88a92318690a18a9238a21606db14e84e16086014e6db15e6db14a68a15e69e14a6db15d6db14668615d69d1466db0526920546db0526d205469a0ce60e0e07e00ce7ce0e06200ca7ca0de61e0ca60a0de7de0c67060dd61d0c66060dd71d15b61b15a71a15b71b15a61805261205465405265205461805649204e5ce0565d604e49205549204a50a05551504a4920534920465060535130464920503d004e44e05045004e3ce04c2cc04a34a04c34c04a2ca0481c80462460482480461c60411440410c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x30 : Ex t176 8 [v11,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x4007401a1993401919a314a113a50b95400a078d40180d18401719b114a8400503851b34402b40040386402a0c98160c0e0c40060e141b32400303834011150a4010148940010d0a400f0c89400e0d124014400d0c91 324 0xaa8145a49989aa89a8a491459c90096e89659c99496e80009c59456e60009c50056e696588b69a38990988b90b38969a88769a3858c58878c738569a6c369a38084088384338069a08f75d38e69a08f69a38e75d0a075f38e69a09e69a38e75d5c959644b70b5c970944b5965c55964475075c55054475965c05966c35035c05006c359639a51a4595965da59a3995145d751408f5965d759608f5145d75140985965d75960955140930930893c90933d30894490920920853c50923d20854450903d00804400900900803c038e38d08b28b08930908b30b089289087187085205087207085185083043080100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x31 : Ex t176 8 [v157,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40071993400519a314a113a50b95078d19b114a803851b3403860c981628160c0e0c0e180e1403834011150a4010148940010d0a400f0c89400e0d12400d0c910d18400419b2400340141b32 300 0x96428a94e88e9648a494e28a8ce18e8e48618ce84e8e41868ca84a8e21868ca18a8e28610906db08e80e09081008e6db08c6db08a7ca08c7cc08a6db0886db0867860887880866db0927520946db0926d209475410e65911071010e70e11065910a65910c60c10a60a10c65910665910860810660610865909b61b09a65909b65b09a61811261211465911265211461805649204e5ce0565d604e49205549204a50a05551504a4920534920465060535130464920903d008e44e09045008e3ce08c2cc08a34a08c34c08a2ca0881c80862460882480861c6082085082103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x32 : Ex t176 8 [v12,u2,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40131993401219a314a11528400a150a14a80d0a40050d12400619b2402b038640041ab4402a0c9840221b324011160c4010148940010e0c400f0c89400e0e14400d0c9140034018401703850d18400c0383 324 0x9a72cb98f94f9a796798f2cba0f1cf7a7924a0f90f7a71c798b90b7a51c798b1cb7a59248a10c318f8cf8a18e118f0c389f0c318b08b89f09f18b0c379d0c318708789d09d1870c30530820460c30530c304108260f54f72182160f80f72156160b80b71f55f60b54b71f81f6076c779d55d60754779d6dd1835437026c26036c31825550415550535d30585d705355504155905a5d90585d705655505151104f4cf0514d104f04f04d50d04b4cb04d4cd04b04b0494c90470470495090474c705141104f48f05149104f40f04d30d04b38b04d38d04b30b049209047287049289047207043183042142043103042042041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x33 : Ex t176 9 [v13,u0,u1,u2,u3,u4,u5] :=
  certify c176 [⟨_,p176x19⟩,⟨_,p176x2⟩,⟨_,p176x29⟩,⟨_,p176x30⟩,⟨_,p176x31⟩,⟨_,p176x32⟩,⟨_,p176x26⟩,⟨_,p176x27⟩] (unpack 6 0x199319a314a11628160c0e0c40220e1413a50b95078d402819b114a81ab40e18402180078006038403850c984011150a4036148940010d0a400b0c894005400e0d124035400d0c9180058004400680031b32800203834003800140020d1840048000402f0386 308 0x5b2555599c595b2c725995556993d96b2c30699c196b23cf595c155b13cf5953d55b1c306ae208699bd96aebee6992085ad2085958d55ad8ed59520846b20830f8cfb2b8eb44f20869b79e699a9969ba9b69979e59779e595a55597a5759579e45279e1cfa0f9d2a1244f79e3089881e379e9c87881e39a369975969b95b69995969b75b59595559775759575559795744f90f5127520cf74f4529120c87483239230c890832375d8a181f0de09e1c675d69b69b69971969b71b6996995975975956155976175955954524121cf4cf5124d244f40f30a38a1c834830a2ca1c82481c61440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x34 : Ex t176 7 [v14,v15,u1,u3,u4,u5] :=
  certify c176 [] (unpack 5 0x4012199319a314a115284021400513a3168d0b930e8d0e95078b038503831ab10d18400c03821489150a0c8914a80d0a0c980c91400419b20d12 228 0xe6ce7e2749e6f5be24e7b2469b6f39b2729b6c63b1f27b6863b1c67b6b39ba1efba709ba308ba5efb95efb9d87b9585b9defb01efb0d83b0180b0def1058c111ef105ef111845d1ce5a6a95d2b45a5ce5c9ce59e675ca7259dce5c5ce58e035c61058dce5bdaf5b1ce5bdce5b1ac5ac4a12489120c8124c91208811cc71148511c87114c510c231008010c8310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x35 : Ex t176 8 [v18,v15,u2,u1,u3,u4,u5] :=
  certify c176 [⟨_,p176x34⟩] (unpack 6 0x40121993401919a314a11528400a160c0e0c16280e180e141b3213a6168d0b960e8d0e95078e03861ab40d1803821489150a0c8914a80d0a0c910d1219b219b10c98038540088000400c402b402a4001 300 0x9e638e9d09109e69269d038e9502d09668e39508d09662cb94e8ce9642cb94e2ce9648e384f18685089084f88f85018684c18684e48e84c48c84e18684a18684b48b84a48a84b1860db4920dd1860db1860dd4920e07600d07900e07a00d07500df79f0ce74e0df75f0ce78e0dc6dc0cb74b0dc75c0cb6cb0d95140d06900d96990d05140d75140ce60e0d76170ce5140d65140cb54b0d65550cb5140c64c60d25140c65060d24d20c30d11501d014f34f15035014f1cf14e34e14c1cc14e1ce14c34c14b24b14a1ca14b1cb14a24a1481c71462461482481461c60c50c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x36 : Ex t176 8 [v21,v15,u0,u1,u3,u4,u5] :=
  certify c176 [⟨_,p176x34⟩] (unpack 6 0x4012199319a314a1152840214005150a14a80d0a0d1219b20c9813a3168d0b930e8d0e95078b03831ab10d180382160c14890e0c16280c890e140c911b341b320e18038540088000400c4016402a4001 300 0x9e630c9cf94f9e69669cf30c84f28f86692484f90f86628a84c90c86528a84c28c8659248a018688f8cf8a08e088f18689e18688c48c89e49e88c18685d18684a48a85d49d84a18614f6cf1607e014f7cf1606e014c7cc15e6de14c6cc15e7de14a70a15d6dd14a6ca15d71d1466c61527121467061526db0d95140cf68f0d96990cf5140d75140cc60c0d76170cc5140d65140ca54a0d65550ca5140c64c60d25140c65140d24d20c31510d01d00cf34f0d03500cf1cf0ce34e0cc1cc0ce1ce0cc34c0cb20b0ca1ca0cb1cb0ca20a0c91c70c62060c92080c61c60c31440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x37 : Ex t176 8 [v158,u1,u0,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40124037199319a314a11628160c400a0e0c40090e1414a84006400b402f038640080c9813a50b95078d03850d184011150a4010148940010d0a400f0c89400e0d12400d0c91402d402640170383400c0e18 324 0xa2628a9ce94ea269669ce28a7ce18e7e69247ce90e7e61867ca90a7e51867ca18a7e592486208204e8ce8628e204e08286008204a00a86002004a0827de0820460067de01e04608270e65961075070e74e61065970a65960c5cc70a5ca60c6597066596085c87065c66086590425c26006597026420405d71135d36186591136536185d711b5d761865911a6596185d71104d310e58e11059010e4d310c4d310a54a10c54c10a4d31084d31065061085081064d30420421004d31024c20400400410521103d010e44e11045010e3ce10c2cc10a34a10c34c10a2ca1081c81062461082481061c60420421001401020c2040040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x38 : Ex t176 8 [v122,u1,u0,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x4013402019934012400719a314a1160c0e0c1628400a0e1414a840061ab41ab113a50b95078d03854011150a4010148940010d0a400f0c89400e0d12400d0c91402d1b3240170e1803834008400b19b2402f0c9840030386400c0d18 324 0xaab492a56a16aaba2ba56492b16396b6b9e7b569d6b2b38ea529d2aa838ea92392a689e78e62a60569168e69260562968e59250522928e52a50529128e27a204e28e8e22a204e78e81611621885881685621811881285221411481211221485480e18e21011080e10e21019005e10420a7ca81e7de04a1040da11a0c81860da19a0c31040d869a0d67560d87580d669a0d469a0d27120d47140d269a0d069a0ce6ce0d06d00ce69a04c04c0ca69a0cc69a04a04a0d85d80d66560d86580d65d60d44d40d25520d45540d24d20d03d00ce44e0d04500ce3ce04c04c0ca34a0cc2c904a0490c62060c41c40c61420c40c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x39 : Ex t176 7 [v159,v14,u1,u3,u4,u5] :=
  certify c176 [] (unpack 5 0x4012401e199319a314a1152840210e980d1813a20b92078a4004038213a31489150a0b930c890d0a078b0c9140050d1219b1038340061ab10385400c0c98 228 0xf718cebf6ff737cebd8c43d2f4735a43f4f471294334c46d294312c46f5ac3842c3f2fc3b2ec3c42c2c42c32ccc2ecbc304241c42426c941ec742442946d695c429444295ed693e2f93aae93eaf93a2e9322c92e8b9328c92e2b9262991e679266991e2723ca523a0e23e0f238a5230a522dab231ac22ca5424a541d474254941ca521866208a5218a52086208420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x40 : Ex t176 7 [v159,v15,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40131993401219a314a115284021400a13a2168d0b920e8d078a0e9503820e980d181489150a0c8914a80d0a0c9140050d1219b219b140060c9803854004400c0383 228 0x79f34d78f74f79f75f78f34d80f28f25f71c80f70f25f28a78d70d25d28a78d28d25d71c64e0c368f6cf64e6ce68f0c364b0c368d40d64b40b68d0c32480c368a40a64840824a0c305749704f60f05761704f48f05549504d58d05559504d48d05349304a50a05351304a48a04344305049004348305045014f10f14e30e14f30f14e10e14d30d14b10b14d10d14b30b24a1ca14810814a10a2481c81461041431c31461c6143103042040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x41 : Ex t176 8 [v14,v15,u1,u3,u4,u5] :=
  certify c176 [⟨_,p176x39⟩,⟨_,p176x40⟩] (unpack 6 0x403a40241993402319a314a1152813a3168d0b930e8d40310e95078b4021400a03850383400c1ab10d18400680018000038240131489401f150a40120c89401e14a80d0a40040c980c91400519b20d12 228 0x2a524938d8cd2a58e59cd24998d0cd0a58a238d88d0a50c39098890a30c32890c90a38a260b5d764d84d60b84b64d5d76065d76494c96064c66495d70805d76434c36004c00835d76414d31445d71415d76444c471f59654d80d71f81f54d59671d59654978971d79d54959609b59654368371b69a54359665751755359661759655351349140f14d10d38b1cb14d1cd30b10b1491c92861061491092061c6143043080100143103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x42 : Ex t176 7 [v159,u2,u1,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40121993401919a314a115284021400a0e980d1813a2160c0b920e0c078a0e1414a81489150a0c890d0a0c9140050d1219b14006038540040386400c03820c980383 240 0x81f34d80f74f81f75f80f34d78f2cf29f71c78f70f29f2cb78d70d29d2cb78d2cd29d71c64e18668f6cf64e6ce68f18664c18668d5cd64c5cc68d18628918668b5cb6495c928b1860c25d70d81860c21860d85d70d50950cf58f0d55950cf08f0d30930cd50d0d35130cd08d0d10910cb48b0d14910cb08b1cf1041ce40e1cf40f1ce1041cd1041cc04c1cd04d1cc10428b1041c90491cb04b2891041c80411c61061c81041c60460c30410c21040c51000c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x43 : Ex t176 8 [v14,u2,v15,u1,u3,u4,u5] :=
  certify c176 [⟨_,p176x42⟩] (unpack 6 0x40121993401919a314a115284021400a400513a6168d0b960e8d0e95078e038603851ab40d1803838000160c0e0c0e14400c40080e181489150a0c8914a80d0a40040c980c91401419b20d12 300 0x96420894a88a9648a494a2088ca0ca7648618ca84a7640c38c88487620c38c80c87628617895557ca80a7898097ca5557865557c84c87864c67c85557405557c34c37804c074355534d4d334255534255534d4d30814d31445551415550844c435b59634a70a35b71b34a5963595963486883596993485963585963435c33585d734359635551535359635559535351334d35234d09135009034a34a35009034a34a34f08f34834834f08f34834834e08e34334334e08e34334334d30b14a10a0891c914a1ca0891091481c80861061481080861c6143043080100143103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x44 : Ex t176 7 [v159,u0,u1,u3,u4,u5] :=
  certify c176 [] (unpack 5 0x40124027199319a314a11528402113a20b92078a0e980d1816281489150a0c890d0a0c9140050d1219b1400603850c98400c40040383400803820e180386 240 0xf71efec771f737cec5ef645b16735a64751671ad63f4f66dad63daf66f5ac4108c4731c4330c4508c3908c3e6fc3a6ec3d0862d086366d62e6b635081c4511c2f01c6f11c0501bc4f1bace1becf1b84e1b44d1aeab1b6ad1ac4b1a2881cc531a0481ce934c4844c2504c6514c0844bc844b82e4bc2f4b8846348462c2b6342d62c844a8214a0844a8844a02831827308841948418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x45 : Ex t176 8 [v14,u0,v15,u1,u3,u4,u5] :=
  certify c176 [⟨_,p176x44⟩] (unpack 6 0x40124027199319a314a115284021400513a3168d0b930e8d0e95078b03831ab103868000038540080d18400c0c981489150a0c8916280d0a0e180c9140041b320d12 300 0x81e1c77c974981e75e7c91c76490c965e71c64970965e0c364770765d0c36470c765d71c68838e6896c96886c868938e68538e68730768530568738e64038e64330364030064338e08130c08438e08138e08430c3574922c96093576172c94923554922c75873555952c74923544922c34c33544d32c349234e44e2cc49234e4922cc44c34d35034d08f34908934834834908934834834708734534534708734534534308334034034308334034034e08e34c34c34e08e34c34c2cb2ca089109088188089189088108087187085105087107085185083043080100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x46 : Ex t176 9 [v15,u0,u2,u1,u3,u4,u5] :=
  certify c176 [⟨_,p176x35⟩,⟨_,p176x36⟩,⟨_,p176x3⟩,⟨_,p176x37⟩,⟨_,p176x22⟩,⟨_,p176x38⟩,⟨_,p176x41⟩,⟨_,p176x43⟩,⟨_,p176x45⟩] (unpack 6 0x199319a314a11528403b160c0e0c162840320e141b32150a14a80d0a0d1219b20c980e1840068008800780064011168d4039148940010e8d402a0c894031400e0e954038400d0c9180058004400a8003038580020d18400c80014016038340088000402b0386 308 0x5b2555599c595b2c725995556993d96b2c30699c196b23cf595c155b13cf5953d55b1c306a728a699bd96a7be769928a5a528a5952155a522559528a46428ab8f20f32422444f28a1e820832128a32828a1e12086ad86d699ad96adaed6998595acaec5958555ac86c595ad5469a291cf84faa986944fa0f6998996a79a76999996a78a75959955a58a55958955a59a544f8cf0e48a480f88f4648e480a88a0c88c880a8ca0c88a21c68a20e10a181f79d69b69b69971969b71b6996995975975956155976175955954524121cf4cf5124d244f40f30a38a1c834830a2ca1c82481c61440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x47 : Ex t176 8 [v21,v14,u2,u1,u3,u4,u5] :=
  certify c176 [⟨_,p176x34⟩] (unpack 6 0x4012199319a314a11528402140051ab10d1813a30b93078b03830382150a14a80d0a0c98400419b20d1213a6160c14890b960e0c0c89078e0e140c911b3403861ab403858000400c401640154001 300 0x9a530c98f90f9a592598f30c80f24f8258e380f8cf82524980c8cc82424980c24c8248e385814584f88f85889884f14585614584c78c85679684c1458121458097898127928091450da79a0df1450da15a0df79e51379e5151455131455157950d069a0cf74f0d07500cf69a0cd69a0cc70c0cd70d0cc69a0ca69a0c96c90ca6ca0c969a0c351950f54f5185d850f5cf51855850c5cc51655650c54c5165d65094c95125525095495124d20d01c70cf44f0d04500cf1c70cd1c70cc38c0cd38d0cc1c70ca1c70c92c90ca2ca0c91c70c81860c51c50c81c70c51850c30c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x48 : Ex t176 8 [v18,u0,v14,u1,u3,u4,u5] :=
  certify c176 [⟨_,p176x34⟩] (unpack 6 0x4027199319a314a115284021400516280e181b3213a60b96078e03861ab40d184004038213a31489150a0b930c890d0a078b0c910d1219b103831ab10385402b4015400140088000 300 0x8e234d8d08508e28628d034d75029076282075081076228a74d80d76128a74d28d76182078f1457907d078f7cf79014578c14578d50d78c50c78d14574914574a50a74950974a1454da5144db1454da1454db5144d06d04cf70f4d07104cf6cf4cd70d4cc6cc4cd6cd4cc70c4ca68a4c96c94ca6ca4c968905059604f64f05065004f59604d59604c60c04d60d04c59604a5960495c904a5ca0495960455450545960455850545540414d20501c704f44f05045004f1c704d1c704c38c04d38d04c1c704a1c70492c904a2ca0491c70481880451c70481c70451850440c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x49 : Ex t176 8 [v160,u1,u0,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40201993400719a314a11628160c0e0c0e1414a840214006400c40004004038640020c98150a0d0a152840050d120d184011158b4010148940010d8b400f0c89400e0d93400d0c91401840140383402c0e1840030385 324 0xa292cba0f9cfa299e9a0f2cba8f1cf5699a6a8f98f5691c7a0b98b5671c7a0b1cb5679a61641047cf94f1649647cf1041631047cb08b1630a37cb1041621047c70871620a254710470f6db81885870f84f8186db70b6db81765770b64b8176db7076db5546547076475546db7046441426db7046c47c26590416590536db05c6db05365905e65905d6db05c6db05a6590584d804f58f05859804f4cf05759704b4cb0574d704b58b0545540474c70544d40470470444c40420420441440424d305141104f48f05149104f40f04d30d04b38b04d38d04b30b0492090472870492890472070441840420420441440420c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x50 : Ex t176 8 [v75,u1,u0,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x401e40371993400919a314a113a3160c0b930e0c078b0e1413a60b964021078e40061b3219b2152840050d18401114894010150a40010c89400f0d0a400e0c91400d0d12402c0e18400840141ab14018038340020c98400c1ab440264000038640040385 324 0xc6f596c1ab5ac6fb6fc1a596b9a49a76fb2cb9ab1a76f492b96b1676d492b9649676db2c32a24985aada32aaea85a249328249856a56328a688562493262498529d23269e675224905a0828d895805a95a8d80820560828d49140569168d40820520827508900528927500820497c93200820490898607df04114511c08204108211c15c11871811a79a11879811a71a11479411671611471411679611011011271211071011275210970910b30b10910910b71c11a65a1186d811a6da1186581165561145d41165d61145541124521104d01124d211045010b3ce10934910b30b1092891052070421820450451020c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x51 : Ex t176 9 [v14,u0,u2,u1,u3,u4,u5] :=
  certify c176 [⟨_,p176x47⟩,⟨_,p176x41⟩,⟨_,p176x43⟩,⟨_,p176x45⟩,⟨_,p176x48⟩,⟨_,p176x49⟩,⟨_,p176x16⟩,⟨_,p176x31⟩,⟨_,p176x50⟩] (unpack 6 0x199319a314a11528401b1ab1800880078006800513a3160c0b930e0c078b0e14402b0e1813a60b96078e038540211ab40d1803834014800403864006800380028001401680000c9840111489403d150a40010c8940150d0a40054004400e0c91403c400d0d12 308 0x23224920dc4d232c7220d24930d0cd332c3030dc0d3320c3209c092310c32090c9231c3030b75d30dbcd30bbcb30d75d20775d20968920768720975d08075d703683b8068008375d55969962d75d61975956d69a72c69a16b75d16a75d72969a32765930da0d327a2730d6592256592099892259a52096590a36595439036239230836596225e130d59630b80b30d80d30b5962095962077c72097c920759608359618078014378308059615d6dd71a59615d59d71a6da1594196175965544d215140f30d30d30b38b30d38d30b30b209209207287209289207207083043180100143103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x52 : Ex t176 8 [v16,u1,u0,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40274037199319a314a1162813a60b96078e400619b2400b0c98400c402f03861ab4150a0d0a402240090d1219b140080385401114894010160c40010c89400f0e0c400e0c91400d0e1440184014400403834026402c0e18 324 0xae934da91a11ae9a29a9134d5d12515e99e75d19d15e92495cd9cd5e82495cd24d5e89e714f0c389199114f98f8910c314b0c388d00d14b00b88d0c31470c38890091470078890c389171c51a95a89195151a71c88d71c51991988d90d51971c88971c5168d68898c951671c88384350071c1437035008400956d551471c09571c5146db0a06df51e71c09d71c5146db09a09a09155109a55a09161109909908d54d09955908d60d0965560895c909609608954908354308014008308308054051451309141108f48f09149108f40f08d30d08b38b08d38d08b30b089209087287089289087207083183080140083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x53 : Ex t176 8 [v17,u1,u0,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x402019934007401919a314a1160c0e0c16280e1414a840061ab1400b4008402f0386400c0c98402819b14011150a4010148940010d0a400f0c89400e0d12400d0c914018038340141b32402c0e1840030385 324 0x9a730c9909109a792799030ca102109678e3a108d096720898c8cc96420898c20c9648e31620a275081016282275009016182174c08c1610a174c80c15f71f74808815f09f74870875061869279275079069261874c61868e58e74c58c68e61874861868a58a74858868a61875c59668261815c61868259605459605a61805461804159605b59605a61805961805759605255205051005251205005004e54e04c50c04e50e04c04c04a50a04804804a54a0485080445140420420441440425020524520504d00524d205045004e34e04c3cc04e3ce04c34c04a24a0482c804a2ca0482480441c60420460441440420c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x54 : Ex t176 8 [v21,u2,v18,u1,u3,u4,u5] :=
  certify c176 [⟨_,p176x42⟩] (unpack 6 0x40121993401919a314a115284021400a40050e980d18150a14a80d0a0d1219b219b140080c98400403834014800013a20b92078a038213a6160c14890b960e0c0c89078e0e140c911b3403861ab40385400c0e18 300 0xa68249a4c98ca689a8a4c2499cc18c8689659cc94c8681869c99498661869c918986696589e0828cc90c89e91e8cc08289c0828c97c989c7dc8c908285b0828c67c689b7db84608204f7df06008204f0820607df50c5cc61e75e50c74c61e5de50974961c5dc5095c961c75c50668661b5db5065c661b69b5195d76026825196996025c205605505405304d3cd04c48c04d48d04c3cc04a3ca04944904a44a0493c90473c70464060474070463c604d10404c38c04d38d04c10404a1040492c904a2ca0491040471040462060472070461040450c30421020451040420c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x55 : Ex t176 8 [v21,u0,v18,u1,u3,u4,u5] :=
  certify c176 [⟨_,p176x44⟩] (unpack 6 0x40124027199319a314a115284021400513a30b93078b19b103831ab10c98800013a2150a0b920d0a078a0d1203820e980d18160c14890e0c16280c890e140c911b341b32400c0e180385400440080386 300 0x9e528a98d90d9e592598d28a80d20d8258e380d8cd82520880a8ca82420880a20a8248e38560c384d88d85689684d0c38540c384a3ca8543d484a0c38120c38083c88123d28080c304d6db0567d604d7cd0566db04a6db05479404a78a0546db0486db0527520487480526db05c69c0436db05c6db04368314515904109804d44d0565d604d5cd05645604a44a05455404a54a0544540484480524d20484c805245204340304f44f04344304f40f08e10e14d2cd08e2ce14d10d08c2cc14a10a08c10c14a2ca089189148108089109148188087104143183087186143103042040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x56 : Ex t176 9 [v18,u0,u2,u1,u3,u4,u5] :=
  certify c176 [⟨_,p176x35⟩,⟨_,p176x48⟩,⟨_,p176x5⟩,⟨_,p176x52⟩,⟨_,p176x24⟩,⟨_,p176x53⟩,⟨_,p176x54⟩,⟨_,p176x55⟩] (unpack 6 0x199319a314a1152840224028160c0e0c16280e141b3213a60b96078e1ab40d1880078006038203860e1840111489403f150a40010c89402b0d0a400e0c91403e400d0d12800580044006800319b180020385401480014015038340088000402a0c98 308 0x57059655abda570bf055a59665a49a670bae65ab9a670492556b9656f49255649656fbae65820865ab5a658b5865a20855420855685655485455620844f208b12852acf84f4522083268611dc2081e620831c86166a72a65aa1a66aa2a65a71a569a29556716569729556a164679a73127121e772745299265a75d65895865a95a65875d55675d55491455691655475d45275d0cf8cf3128d244f75d3088880e175d3087480e18a13207de1c675d0dc09c65a65a6586d865a6da6586585565565545d45565d65545544524120cf4cf3124d244f40f30a38a0c834830a2ca0c82481c61440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x57 : Ex t176 8 [v19,u1,u0,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40124037199319a314a113a3160c400a0b930e0c4009078b0e1414a8400540061b3240004004038640020c9840211b3403854011150a4010148940010d0a400f0c89400e0d12400d0c91402d0e18402640170383400c1ab1 324 0xae92cba8fa0fae9a29a8f2cb84f1cf7699e784f9cf7691c784b9cb7681c784b1cb7689e792508204f98f9259a504f08292208204b8cb9228e204b08275f08204780785f81f04708264f61855179164f78f55161864b61854d58d64b58b54d61864761874958964758774961804258271b61864260205b59665959611461865961811459665959611a61865961811759611111110f50f11151110f54f10d10d10b50b10d50d10b54b10950910754710910910750704204210050010250204004004105311141110f48f11149110f40f10d30d10b38b10d38d10b30b1092091072871092891072070420421001851020c2040040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x58 : Ex t176 8 [v20,u1,u0,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x4020401319934007401219a314a11628160c0e0c0e14402114a8400540061ab4400a1b344011150a4010148940010d0a400f0c89400e0d12400d0c91402d401703830e1840000386400419b2400340020c98400c0385 324 0x9a84519d59559a89689d5451a95355768924a5591576834d9d191176534d9913517659246a228a0558d56a28e205528a6a128a0512516a126105128a76028a04d24d6a026004d28a1950957d77971957957d70971917917d30931910917d379318d14d74f08f18d08d74f14f04a08a7096c918a6ca04908210408211914510614511908211769711565511765711511511369311165111365311111110f64f10d10d10f68f10d64d04a04a10964910a64a04904911759711561511761711559511349311151111351311149110f38f10d40d10f40f10d38d04a04a10930910a2ca0490491052071021071051851020c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x59 : Ex t176 9 [v21,u0,u2,u1,u3,u4,u5] :=
  certify c176 [⟨_,p176x47⟩,⟨_,p176x36⟩,⟨_,p176x29⟩,⟨_,p176x57⟩,⟨_,p176x18⟩,⟨_,p176x58⟩,⟨_,p176x54⟩,⟨_,p176x55⟩] (unpack 6 0x199319a314a11528400a1ab113a30b934032078b150a14a80d0a0d1219b20d18400680078006038203830c984011160c4041148940010e0c40160c894005400e0e144040400d0c9180058004402180031b3480020385400c8001402a0e184004800040150386 308 0x5b2555599c595b2c725995556993d96b2c30699c196b23cf595c155b13cf5953d55b1c306a8208699bd96a8be86992085a62085958d55a68e659520846520830f8cfba58e544f2081de8de32d208b9e21e1ed8e369b79e699b1969bb1b69979e59779e595ad5597ad759579e45279e1cfa4fa92a5244f79e6997596a89e86999d96a87685959d55a67665957555a69e644f90f5257650cf74f4659250c87483239230c890832375d8a181f0de09e1c675d69b69b69971969b71b6996995975975956155976175955954524121cf4cf5124d244f40f30a38a1c834830a2ca1c82481c61440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x60 : Ex t176 8 [v27,u1,u0,u3,u2,u4,u5] :=
  certify c176 [] (unpack 6 0x1628160c0e0c199319a314a114a81ab40e14400440000386400d078e40020c9840061b344011150a40494010148940010d0a4048400f0c89401403834003400c0e1840470d120d93401c40460c91400e40350385 324 0x42638e41395342696641338e56830c553a53568a6855330c42730c40e24e42726740e30c16130c14324316126114330c1530d31669241539131660c314e90e1650c314e0ce1659245536935568d65538d355669640e8ce41169140e68e4118d180c68c64970980c70c64969a1438831616a11436831618a12cb69a2d871c2e071c15869a15d69e2df71e15d71c15b69a55655655361355661655355341141140e60e41161140e40e2cc64c2c96092cc60c2c92c91466061431431461461436035565165535d35565d65535134113d140e48e41149140e3ce2cc28c2c92c92cc34c2c9289146207143143146146143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x61 : Ex t176 8 [v28,u1,u0,u3,u2,u4,u5] :=
  certify c176 [] (unpack 6 0x1628160c0e0c0e95199319a314a114a8400440061b3440111489404b4010150a40010c89404a400f0d0a40140e18400c038340460c9140470d1240264002400d0c98403340000386400e402e0385 324 0x52255551a85a52286251a55566538e65a99a6659a565a38e52438e51541552442451538e16338e14c40c16341014c38e15a31a16282015a81a16230c15581516130c15531516182065a0c36577d765a7da6570c35150c35121925151955120c378e18e7500c378e0ce75018614c0c314a18a14c18c14a0c379e18615c0c379e0c325c18665765765a71a65771765a65a51251251571551271251551524e24e25071024e70e25075014a70a14c14c14a14a14c70c65a61a6576d765a6da6576175154d55125925155955124d22503d024e24e25045024e3ce14c34c14a14a14c14c14a2ca2462061431c31461c6143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x62 : Ex t176 8 [v29,u2,u0,u3,u1,u4,u5] :=
  certify c176 [] (unpack 6 0x1528402140034026199319a314a1150a14a80d0a038540060d1819b20d124004400c402b0386400d078e402a0c981b324011160c404f4010148940010e0c404e400f0c89404d0e140e954038404c0c91400e40400383 324 0x2e62492ce94e2e69662ce24942382040ea8e423aa340e8202e18202c97892e17a12c982015c82014378315c79c14382069379e6a982069382069a79e69a79e6a88206a782069a79e14e0ce16692414e90e1660c31499091650c31490c916592440e50e4238a340e88e4235232c98892e15212c95092e18a16e05207de59e6e05a07de51414374315c51c14350315c75c69a51469359669b59615351415751869959815759615551441141140e4ce4114d140e40e2cc2cc2c94c92cc4cc2c92c91464c61431431461461434c34113d140e48e41149140e3ce2cc28c2c93492cc34c2c9289146207143143146146143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x63 : Ex t176 8 [v30,u2,u0,u3,u1,u4,u5] :=
  certify c176 [] (unpack 6 0x15280d93199319a314a114a8150a0d0a400640041b324011148940514010160c40010c894050400f0e0c40260d1840030385404c0d120c91404d0e144014402a400d0c98403e402b0386400e403c0383 324 0x56559655b91b56592555b5966a13cf69b9db6a19e169b3cf5603cf5564565604605563cf1663cf14c44c16645114c3cf25d4512493cf25d3cf25f45115b31b1658e315b8db16530c1568d616430c1563161648e369b0c36a18a169b89b6a10c35560c35601a05561965600c378f18f7d10c378f0cf7d118614c0c314a18a14c18c14a0c379e18615d0c379e0c325d18669869869b75b69875869b69b55355355675655375355655614a74a14c14c14a14a14c74c69b65b69871869b71b6986585565165535d35565d655351325141124f48f25149124f40f14c38c14a14d14c14c14a2ca2462061431c31461c6143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x64 : Ex t176 9 [v31,u0,u3,u1,u2,u4,u5] :=
  certify c176 [⟨_,p176x60⟩,⟨_,p176x61⟩,⟨_,p176x62⟩,⟨_,p176x63⟩] (unpack 6 0x1628160c0e0c0e95800380021b321528401b0d93800180001b34199319a314a140450d12150a14a80d0a038340060e184004078e038540210d180c91400e0c9807074044400d03864011148940431b1640010c8940421b26 308 0x5e08204674605e75e04608216a596146ac616aaea14659606959604250206952904259626859624e50e26851424e59636796534d59634d5963669651594511469061599191464510574510423c20573d70424515563d64144518d64565543cf26245124e3ce2623cf24e4513617df34d45134d4513607df14638615e71c14670615e38e04270205d38e04238205d71c25b35a1463061596191466061593190426020573170423020576174d63165544944d649655430c4d131140f48f4d149140f30c24e24e24d30c24924b24a2481461461441c41461c61441440420420400c00420c2040040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x65 : Ex t176 8 [v161,u1,u0,u3,u2,u4,u5] :=
  certify c176 [] (unpack 6 0x1628160c0e0c199319a3152214a840050d934008400b402f0386400d0c9813a50b9519b103854033400e0d184011150a40544010148940010d0a4053400f0c89401403834026400c0e1840470d12402e0e1440460c91 324 0x3672cb3509903679a73502cb4a9249490a904a9aa949024936824934b18b3681a834b2490c22490c41840c21820c42490d01100e79650d09500e71040cb94b0e61040cb10b0e696549079e49391349091049379e34b79e34e70e34b70b34e79e8c970984679e8c978984671c0e279e0c47040e271c0c479e21871886179e0d879886171c22071c0dd79e0df79e0dd71c4936184906d04936d349061834e61834b68b34e68e34b6182096492066182096092066460c46180c20c20c40c40c261859759549345349051049351349045034e30e34b3cb34e3ce34b30b2091c92062862092092061c60c41440c20c20c40c00c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x66 : Ex t176 8 [v162,u1,u0,u3,u2,u4,u5] :=
  certify c176 [] (unpack 6 0x1628160c0e0c0e14199319a314a114a840051ab44008400b402f078e400d0c98038613a50b9519b10e1803854011150a40564010148940010d0a4055400f0c894014078b4003400c038340470d12403540460c91400e401c0d18 324 0x3e834d3d29d23e89e83d234d52b208512b1252bb2b5122083ea2083cd60d3ea62a3cd2081692081436031696291432081520d21689a61529921680c314d98d1670c314d0cd1679a65127525159555129525157553cd94d3d07503cd74d3d09509087488987d89087c889875d1438c31467461437431468c61577572a27df2977d728a75d16175d15e7df2a07dc15e75c5155d75126d25156d55125d73d05d73cd68d3d06903cd5d72886482985d72885c82986581465d71431431461461435d75154d55125925155955124d23d03903cd44d3d04503cd38d28b24b28828828b30b2882481461c6143143146146143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x67 : Ex t176 8 [v163,u2,u0,u3,u1,u4,u5] :=
  certify c176 [] (unpack 6 0x15281ab140264003199319a3152214a8150a0d0a400503850d180e9540084014401640150386400d0c9813a30b930383403e400e0e184011160c40584010148940010e0c4057400f0c89404d0e14403c0d12404c0c91 324 0x22618620b94b22696620b1863627df34ba8b362aa234b7df2217df2067862217a12067df0c27df0c47840c27820c47df6d37936e97df6d37d36e979e6e879e6e77df6e87df6e779e0cb08b0e69240cb90b0e60820c69060e50820c60860e592434b6183628e234b8cb3626182066182215a120658622161881f59f71e61881f61f71e5960dd6180c25820dd5960c26186d359371c6180d361371c5966da5960d76180d96180d759634e4d334b54b34e54e34b4d32094d32065062095092064d30c44d30c20c20c40c40c24d345245034e30e34b3cb34e3ce34b30b2091c92062862092892061c60c41440c20c20c40c00c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x68 : Ex t176 8 [v164,u2,u0,u3,u1,u4,u5] :=
  certify c176 [] (unpack 6 0x15281ab140034026078d199319a314a1150a14a80d0a400503850d1819b20d1240084016400c4015078e400d0c98038613a30b9303834011160c405a4010148940010e0c4059400f0c89404d0e144040404c0c91400e40380e18 324 0x2a720828d98d2a79a728d2083e48203cdb0d3e4b243cd8202a28202887c82a27e228882015d8201437c315d7dd1438206927d26ab8206928126ab7df69a8206aaa286a9a2869a82014d0cd16796514d94d1670c31489481660c31480c81669653cd58d3e48e43cd8cd3e45a42888c82a25a22885882a28e28605a071f61f86062071f59614378315d59d14358315d79d15259269c61869261269a59615b5961576186996151575953d04923cd50d3d05103cd49228b4922884c828b4cb2884921464921431431461461434923d03903cd44d3d04503cd38d28b24b28830828b30b2882481461c6143143146146143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x69 : Ex t176 9 [v32,u0,u3,u1,u2,u4,u5] :=
  certify c176 [⟨_,p176x65⟩,⟨_,p176x66⟩,⟨_,p176x67⟩,⟨_,p176x68⟩] (unpack 6 0x1628160c0e0c152840324028405c0e141522150a14a80d0a4005078e40080c900c980d1240111993405b1489400119a340450c898003800203830e188001800003850d18400e40420c91400d40520386 308 0x3d438e3d24123d44143d238e4e62cb4d29d24e69e64d22cb3e52cb3ce28e3e52a53ce2cb0a02cb0962960a02a00962cb4de1c74d29124de91e4d21c73dc1c73ce18e3dc19c3ce1c788b18b8ca1c788b1cb84a1860961c70a01a00961960a01c74d25924d47df4d27d24d45963ce7ce3d05963ce58e3d07df4d25d24de75e4d27524de5de3ce74e3dc5dc3ce5ce3dc75c6cb5cb64a68a6cb68b64a5d76c75c76466866c76876465d70820980855d70960964d44d44d25524d45544d24d23d03d03ce44e3d04503ce3ce14b34b14a14a14b30b14a14a147247146146147207146146085103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x70 : Ex t176 7 [v34,v35,u0,u3,u4,u5] :=
  certify c176 [] (unpack 5 0x40121993400919a314a114a840061b3203860c9813a3170e0b930f0e0f16078b0383400c0381150a14890d0a15280c890d180d12402619b10c91 228 0xe6ca5e2328e6f3be20a5d2008d6f18d2308d6c00d1705d6400d1405d6718b2294b26e9b22e8b2694b1694b1e67b1665b1e94b0294b0e63b0260b0e945b26c5d6945b28c5d673106731129410694112735c58c5a2485c6515a18c5bd8c596055be0f5958c5b98c581a05b9ad5818c5ac4a12489120c8124c91208811cc71148511c87114c510c231008010c8310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x71 : Ex t176 8 [v38,v35,u2,u0,u3,u4,u5] :=
  certify c176 [⟨_,p176x70⟩] (unpack 6 0x40121993401919a314a114a840061b340c98160c0e0c16280e180e141ab113a5170e0b950f0e0f16078d03850381150a14890d0a15280c890d120c9119b219b10d18038640038000400c402d402c4001 300 0x9e630c9cf90f9e69269cf30c94f28f9668e394f8cf96628a94c8cc96428a94c28c9648e384f18685089084f88f85018684c18684e7ce84c7cc84e18684a18684b7cb84a7ca84b1860d97df0db1860d91860db7df0d27d20e01860d21920e07df0de6de0cf70f0de71e0cf6cf0dd71d0cc6cc0dd6dd0cc70c0da65a0ca6ca0da6da0ca64a0d74920cf60f0d76170cf4920d54920cc58c0d55950cc4920d44920ca4ca0d44d30ca4920c30d11501d014f34f15035014f1cf14e34e14c1cc14e1ce14c34c14b20b14a1ca14b1cb14a20a1491c71462061492081461c60c50c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x72 : Ex t176 8 [v41,v35,u1,u0,u3,u4,u5] :=
  certify c176 [⟨_,p176x70⟩] (unpack 6 0x40121993400919a314a114a840061b320c98150a0d0a15280d180d1219b113a3170e0b930f0e0f16078b03830381160c14890e0c16280c890e140c911ab41ab10e18038640038000400c4018402c4001 300 0x9e630c9cf90f9e69269cf30c94f28f9668e394f8cf96628a94c8cc96428a94c28c9648e384f18685e89e84f88f85e18684c18685d7dd84c7cc85d18684a18685a7da84a7ca85a1861597df15b18615918615b7df0d27d20e01860d21920e07df15e6de14f70f15e71e14f6cf15d71d14c6cc15d6dd14c70c15a65a14a6ca15a6da14a64a0d74920cf60f0d76170cf4920d54920cc58c0d55950cc4920d44920ca4ca0d44d30ca4920c31510d01d00cf34f0d03500cf1cf0ce34e0cc1cc0ce1ce0cc34c0cb20b0ca1ca0cb1cb0ca20a0c91c70c62060c92080c61c60c31440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x73 : Ex t176 7 [v165,v34,u0,u3,u4,u5] :=
  certify c176 [] (unpack 5 0x40124037199319a314a114a840280f180c9813a10b9107894026038113a3150a14890b930d0a0c89078b0d1240090c91400619b20383400a1b320386400c0d18 228 0xff58cf3f8fff79df3d8c4bd0f4f77b4bf6f4f5084b36c4f1084b10c4f37b3bc42cc3503bf4fcc0423b042cb6ed3b2eccb4423a0424aaea3a2e84a8429caf79e0429c8429e2f79c2509becf9c2d09be4f9b64d9b2ac9b6ad9b24c9aa4a9a2889aa8a9a248240a523e2f2423023ca5234a5231cc235cd230a54a8a54a1684a96a4a0a521866388a5398a52086208420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x74 : Ex t176 7 [v165,v35,u0,u3,u4,u5] :=
  certify c176 [] (unpack 5 0x40131993401219a314a114a80f180c9813a1170e0b910f0e07890f160381150a14890d0a15280c89400a0d1240090c9119b219b140060d1803864026400c0383 228 0xef98cebf8fefb9eebd8cfbd0f4fb7bfbf6f4f908eb36c4f108eb10c4f37b2bc632c3502bf4f2c0632b0632bb0e2b30c2b8632a0632ab0a2a3082a8630c7180e4630c4630e7180da360beef0daf60be2f0d2340b2ac0d2b40b22c0ca320a2680ca720a2285c0905bdaf5c1b05bc8f5b9ae5b08c5b88e5b1ac4a8ca5a0885a88a4a0c829c8428cc329cc628c8308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x75 : Ex t176 8 [v34,v35,u0,u3,u4,u5] :=
  certify c176 [⟨_,p176x73⟩,⟨_,p176x74⟩] (unpack 6 0x403a40621993406119a314a114a81b324006038640280c9813a3170e0b930f0e405e0f16078b400c0383400a8001800003814013150a4060148940120d0a403715280c8940260d180d12400919b10c91 228 0x2a518638b8cb2a58e59cb18698b00b0a58a238b88b0a50009068860a30002860060a38a27cb79e74d84d7cb84b74d79e7c679e7497097c670674979e7c079e7437037c070008379e5137137e079e7d379352071c7c171c14479e14179e74471c5da4d350b6cb5da6da50b4d35d84d35066465d86585064d30964d35005405d65555004d349140f14d10d38b1cb14d1cd30b10b1491c92861061491092061c6143043080100143103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x76 : Ex t176 7 [v165,u2,u0,u3,u4,u5] :=
  certify c176 [] (unpack 5 0x40121993401919a314a114a80f180c9813a1160c0b910e0c07890e141528150a14890d0a0c89400a0d1240090c9119b24006038640260385400c03810d180383 240 0xff9adfbf8fffb9efbdadebd2f57b7bebf6f57929eb76d57129eb52d5737b3bcc63c3503bf4f3c0c63b4c63bb0e3b70d3b8c63a4c63af0b3a7093acc618b181e4c6188c61e7181d8561beef1daf61bc4f1d0541b6ad1d2b41b44d1c8521a6691ca721a4496408463e2f6423063c84638846342d6382e6348452c846242962c2b524843a021398843a0843982618c21188841948018820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x77 : Ex t176 8 [v34,u2,v35,u0,u3,u4,u5] :=
  certify c176 [⟨_,p176x76⟩] (unpack 6 0x401219934019400919a314a114a840061b3403860c9813a5170e0b950f0e0f16078d038503838000160c0e0c0e14400c40030e18150a14890d0a15280c8940260d180d12401419b10c91 300 0x9231869098099238239091868890098637df8897c98630008867c68600008860068607df7496db74a78a74978974a6db7466db7486887466867486db7406db7436837406807436db35369335c6db3536d335c69a34d69a3426db3426db34d69a08169a1446db1416db08469a3584d33496493586583494d33564d33465c63565d63464d33554d33405003555143404d334d35234d09135009034934935009034934934f08f34634634f08f34634634e08e34034034e08e34034034d30b14a10a0891c914a1ca0891091481c80861061481080861c6143043080100143103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x78 : Ex t176 7 [v165,u1,u0,u3,u4,u5] :=
  certify c176 [] (unpack 5 0x40124007199319a314a114a80f180c9813a10b9107891628150a14890d0a400a0c890d1240090c91400619b2402103860d18400c40260383400303810e180385 240 0xff5eff4b92ff79df49ef6c9926f77b6cb726f58c6bf6f6f18c6bd8f6f37b5c9084cf535cb524cd085bd084c7115bf0f4c5085b1084bb0e5b30c4b90818b181e508189081e7181cc531caf21cef31c8521c4511becf1c6d11bc4f1b84e1b2ac1baae1b04c84c8484a9284e93848848448483c2f8443183c846b8846b02c6b82e6b0844a8215a0845a8844a02831827308841948418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x79 : Ex t176 8 [v34,u1,v35,u0,u3,u4,u5] :=
  certify c176 [⟨_,p176x78⟩] (unpack 6 0x401240071993400919a314a114a8400640211b3203860c9813a3170e0b930f0e0f16078b0383038580004003400c0d18150a14890d0a16280c890e180d1240261ab10c91 300 0x85f14580874885f75f80814578800879f71c78870879f00078570579d00078500579d71c6885d76496c96886c86495d76855d76475876855856475d76805d76435836805806435d72cf58f3185d730f5cf2d859630c5963025d73025d730c5960815960845d70815d70845963143cf2c85483145542c83cf3123cf2c54c53124d22c53cf3113cf2c04003114102c03cf30c30e30c08d3090893083083090893083083070873053053070873053053030833003003030833003002cb2ca089109088188089189088108087187085105087107085185083043080100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x80 : Ex t176 8 [v166,u0,u1,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x4012401e199319a314a11628160c0e0c0e1415284021400540064000402f13a60b96078e0386038540030d180c98401114894010150a40010c89400f0d0a400e0c91400d0d12402b400440150383400c0e18 324 0xa2630c9d0950a269669d030c75021076692475091076620874c90c76520874c20c7659247220820508d07228e205008272108204c00c72102104c08276008204800876002004808278e5555107d078e7ce51055578a55550c4cc78a4ca50c5557465555084c87464c65085550424c25005557025420404d311b4d351455511a5555144d311059610e64e11065010e59610c59610a60a10c60c10a5961085961065c61085c81065960420421005961025820400405155151135961155955135130410521103d010e44e11045010e3ce10c2cc10a34a10c34c10a2ca1081c81062461082481061c60420421001401020c2040040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x81 : Ex t176 8 [v129,u0,u1,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x4013406319934012402719a314a1160c0e0c16280e141528402140061b341b3213a60b96078e0386401114894010150a40010c89400f0d0a400e0c91400d0d12402b1ab140150e1803834000400819b1402f0d1840030385400c0c98 324 0xaab514a58a18aaba2ba58514b18418b6b9e7b589d8b2b410a549d4aa8410a94414a689e78262a60589188269260582988259250542948252a50549148233230502908232a30503108561160d88988568960d81188528920d41148521120d489484e18e0d011084e10e0d019005e1040ca7ca81e7de04a1041d869a1d67561d87581d669a1d469a1d27121d47141d269a1d069a1ce6ce1d06d01ce69a04c04c1ca69a1cc69a04a04a0c60c61c469a1c669a0c40c41d85d81d66561d86581d65d61d44d41d25521d45541d24d21d03d01ce44e1d04501ce3ce04c04c1ca34a1cc2c904a0490c60c61c42041c61420c40c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x82 : Ex t176 9 [v35,u1,u2,u0,u3,u4,u5] :=
  certify c176 [⟨_,p176x71⟩,⟨_,p176x72⟩,⟨_,p176x75⟩,⟨_,p176x77⟩,⟨_,p176x79⟩,⟨_,p176x3⟩,⟨_,p176x80⟩,⟨_,p176x81⟩,⟨_,p176x29⟩] (unpack 6 0x199319a314a114a8405c40218008800740068006038680050c98160c0e0c162840220e141ab1150a0d0a15280d1219b10d180e18400a8004800380024011170e405f148940010f0e402c0c89405e400e0f16405d400d0c91400c80014018038340038000402d0385 308 0x3f338e3d2c923f3cb33d238e4d22124f3c714d2c524f32083cec4e3f22083ce20e3f2c714d2a694e0c204d2c124e0a693cea693df9df3ce9ce3dfa69288a69bdd9ddac89c829da691e19e7adaa69ae1a691da9e70dc9e7b9ba69adca690db9e71ed9e7aeca69aeaa691e89e74e66a64d29124e69264d26923e59253ce68e3e56a53ce90e2a28621c86888e26a22888484e06e04d27924e07a04d26d23df79f3ce6ce3df6df3ce78e29d71d0c86c865d6dd2887081c66db0da09a6585d64d44d44d25524d45544d24d23d03d03ce44e3d04503ce3ce28b24b1c830834b30b2882481c61440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x83 : Ex t176 8 [v41,v34,u2,u0,u3,u4,u5] :=
  certify c176 [⟨_,p176x70⟩] (unpack 6 0x40121993400919a314a114a840061b320c9813a30b93078b03830381150a0d0a15280d180d12402619b113a5160c14890b950e0c0c89078d0e140c911ab403851b3403868000400c401840174001 300 0x9a530c98f8cf9a58e598f30c90f24f9258a290f88f92524990c88c92324990c24c9238a280f14581885880f84f81814580c14581779780c78c8171458091458147948097898141450da79a0df1450da15a0df79e4d279e4d51454d21454d579e0d069a0cf74f0d07500cf69a0cd69a0cc70c0cd70d0cc69a0ca69a0c96c90ca6ca0c969a0c34d94d85584cf58f4d85984cf54f4d75974cc54c4d75574cc58c4d44944c95494d45544c94890d01c70cf44f0d04500cf1c70cd1c70cc38c0cd38d0cc1c70ca1c70c92c90ca2ca0c91c70c81880c51c70c81c70c51850c30c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x84 : Ex t176 8 [v38,u1,v34,u0,u3,u4,u5] :=
  certify c176 [⟨_,p176x70⟩] (unpack 6 0x40071993400919a314a114a840211b340c9816280e181ab113a50b95078d03854026038113a3150a14890b930d0a0c89078b0d120c9119b203831b320386402d4017400140038000 300 0x8e230c8cf80f8e28228cf30c84f24f8627df84f7cf86224984c7cc86024984c24c8607df74f14575079074f78f75014574c14574d6cd74c6cc74d14574914574a6ca7496c974a1454d86db4d91454d81454d96db0546d405c14505415405c6db4d06504cf68f4d06904cf64f4cd68d4cc64c4cd64d4cc68c4ca60a4c96494ca64a4c960905051404f5cf0505d004f51404d51404c58c04d58d04c51404a51404954904a54a0495140414d20501c704f44f05045004f1c704d1c704c38c04d38d04c1c704a1c70492c904a2ca0491c70481880451c70481c70451850440c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x85 : Ex t176 8 [v167,u0,u1,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40631993402719a314a11628160c0e0c0e14152840214006150a14a80d0a40090d120c984011158b4010148940010d8b400f0c89400e0d93400d0c914016400340140383402a0e18400b400c4026038540020d1840080386 324 0xa6a492a56a16a6aa2aa56492ad639672a9e7ad69d672a38ea529d272838ea523927289e72e528a8169962e59a581628a2e428a8122122e422481228a2e328a80e20e2e322380e28a15f10485689615f89f85610415d10485209215d09d85210415b10484e08e15b09b84e10414a08a2c810414a10a80808205669605f79f05679605f69f05279205d69d05269205d79d04e70e05b69b04e68e05b05b04a68a04804804a2ca04869a04468404204204414404269a0585d80566560586580565d60544d40525520545540524d20503d004e44e05045004e3ce04a34a04830804a2ca0482480441c40421820441440420c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x86 : Ex t176 8 [v79,u0,u1,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x401e199319a314a113a3160c0b930e0c078b0e1413a50b954021078d40061ab119b114a840050c984011150a4010148940010d0a400f0c89400e0d12400d0c91402a0e18400340141b324016038340020d18400c40261b34400b038540040386 324 0xbee514bd8b58beeb6ebd851475841876eb2c758b1876e410754b1476d41075441476db2c32a249858ad832aaea858249328249854a54328a688542493262497509d03269e675024915a0828d895815a95a8d80821560828d49141569168d40821520827508901528927500821497c93200821490898607df05871805a79a05879805a71a05479405671605471405679605005005271205071005275204970904b30b04904904b71c04270204414404204204471c05a65a0586d805a6da0586580565560545d40565d60545540524520504d00524d205045004b3ce04934904b30b0492890442070421820441440420c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x87 : Ex t176 9 [v34,u1,u2,u0,u3,u4,u5] :=
  certify c176 [⟨_,p176x83⟩,⟨_,p176x75⟩,⟨_,p176x77⟩,⟨_,p176x79⟩,⟨_,p176x84⟩,⟨_,p176x85⟩,⟨_,p176x16⟩,⟨_,p176x24⟩,⟨_,p176x86⟩] (unpack 6 0x199319a314a114a8401b1b321b348008800780060386402880050c9813a3160c0b930e0c078b0e14402d0e1813a50b95078d0383401480040385400a800380028001401880000d184011150a4065148940010d0a40170c8940094026400e0d124064400d0c91 308 0x2321c720bc4b232c7220b1c730b00b332c3030bc0b332000207c07231000207007231c3030ba2830dbcd30bbcb30da28207a28209949207947209a28080a289c3943b80940083a2855995962da28619a1956d9659d695616ca28156a169ec9659eb96516aa28169a289e696532365930b90b32392330b6592216592078872218a120765909f65954080061f81f08065961e5dd30d59630b70b30d70d30b5962095962076c72096c92075960835961806801436830805961594196175965544d215140f30d30d30b38b30d38d30b30b209209207287209289207207083043180100143103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x88 : Ex t176 8 [v36,u0,u1,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x4007401e199319a314a1162813a540210b95078d400619b1150a40320d0a40050d1219b20386401114894010160c40010c89400f0e0c400e0c91400d0e14401640140383402a0e18400c40000d184004402f038540031b34 324 0xae94d3a97a17ae9a29a974d37173d77299e77179d77293cf7139d37283cf7133d37289e72d528a8579972d599585728a2d128a8532132d121185328a2cd28a70f20f2cd20d70f28a91f08205795791f95f05708291d0820538d391d8dd05308271b08204f88f71b89b04f08284a80a0480822ca08a04880811711711f69f11769711f79f11311311d69d11369311d79d10f68f11b71b10f10f11b69b10a68a1082c810a10a10868804204210069a10268204004004105911759711561511761711559511349311151111351311149110f38f10d40d10f40f10d38d10a30a1082c810a10a1082480421c21001851020c2040040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x89 : Ex t176 8 [v37,u0,u1,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40634020199340274007401919a314a1160c0e0c16280e14152840061b32402119b2401114894010150a40010c89400f0d0a400e0c91400d0d124016038340141ab1402a0e1840004008402f0385400c0d1840030386 324 0x9a85149d89189a89289d8514a984189688e3a588d89684109d48d49644109944149648e32e22227588182e28227582182e18217542142e12217548142df29f7502102df21f7502906d61040587986d67960581046d21040540946d20920541046ce1040500906ce08e05010475c0820481042dc1040480821986d81966961986981961961946d419269219469419219219069018e18e1906d018e68e18a68a18818818a2ca1886880440441826821846840420421985d81966561986581965d61944d41925521945541924d21903d018e44e19045018e3ce18a34c18818c18a2ca1882480440441821c21841440420c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x90 : Ex t176 8 [v41,u2,v38,u0,u3,u4,u5] :=
  certify c176 [⟨_,p176x76⟩] (unpack 6 0x401219934019400919a314a114a840060f180c98150a0d0a15280d1219b219b140030d18402603834014800013a10b910789038113a5160c14890b950e0c0c89078d0e140c911ab403851b340386400c0e18 300 0xa27249a0c90ca27927a0c24998c18c9678e398c8cc9671869898c99641869891899648e384c08285e89e84c88c85e08284908285d7dd8497c985d08284608285b7db8467c685b08204f7df06008204f0820607df51e5de60c70c51e71e60c5cc51d71d6095c951d5dd60970951b65b6065c651b5db60664651a5d760264251a6596025c205605505405304d3cd04c48c04d48d04c3cc04a3ca04944904a44a0493c90473c70464060474070463c604d10404c38c04d38d04c10404a1040492c904a2ca0491040471040462060472070461040450c50421040451040420c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x91 : Ex t176 8 [v41,u1,v38,u0,u3,u4,u5] :=
  certify c176 [⟨_,p176x78⟩] (unpack 6 0x401240071993400919a314a114a8400640210f180c9813a30b93078b19b203831b320d18800013a1150a0b910d0a07890d120381160c14890e0c16280c890e140c911ab41ab1400c0e180386402640030385 300 0xa2628a9cd90da269269cd28a94d20d9668e394d8cd96620894a8ca96420894a20a9648e384d0c381489484d88d8140c384a0c381279284a78a8120c38480c38107908487888100c304f79e05f0c304f0c305f79e05465904d74d05475404d65905265904a70a05271204a6590506590486c80506d004865905a61a04365905a6590436031451570410960543d404d54d05455404d3cd0523d204a4ca0524d204a3ca0503d00484480504500483c808e10e14d2cd08e2ce14d10d08c2cc14a10a08c10c14a2ca089189148108089109148188087104143183087186143103042040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x92 : Ex t176 9 [v38,u1,u2,u0,u3,u4,u5] :=
  certify c176 [⟨_,p176x71⟩,⟨_,p176x84⟩,⟨_,p176x5⟩,⟨_,p176x88⟩,⟨_,p176x31⟩,⟨_,p176x89⟩,⟨_,p176x90⟩,⟨_,p176x91⟩] (unpack 6 0x199319a314a114a840321b340c98160c0e0c16280e141ab113a50b95078d80078006038103850e184011150a4067148940010d0a402d0c89400a400e0d124066400d0c91800580044021800319b280020386401480014017038340038000402c0d18 308 0x5b0555599bd95b0bf05995556993d96b0bae699b996b03cf595b955af3cf5953d55afbae69920869bb5b699b5969b208595208597a97595a9559720844f208b12a9230fa8f452208325aaa1dd2081e520851daaa0dea9e32b20831e21e0ebaaa6a97696999d96a99e96997595a89e85957555a87685959d546696650f74f1e676644f94f69b79e69991969b91b69979e59779e5958d55978d759579e45279e0cf88f51289244f79e52181f1c679e0dd09d69b69b69971969b71b6996995975975956155976175955954524120cf4cf5124d244f40f30a38a0c834830a2ca0c82481c61440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x93 : Ex t176 8 [v39,u0,u1,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x4012401e199319a314a113a3160c0b930e0c078b0e141528402140061ab1402840051ab40386401114894010150a40010c89400f0d0a400e0c91400d0d12402b0e1840150383400c1b32400b40260385400440020d18 324 0xaa8492a569d6aa89e8a564926963966a89a66969966a838e6929926a738e6923926a79a67642081d69567649641d62087622081d28d27628e21d22086a02081ce84e6a08601ce2081140c37967d61147d47960c31100c37920121100107920c310c0c368e00e10c00c68e0c31c800875c0c31080c81dc0000960960946540966560946d40920920906500926520906d008e64e08c68c08e08e08c64c1c81c80866460886481c61c60836430801000830830806401c71d80965560945d40965d60945540924520904d00924d209045008e34e08c3cc08e3ce08c34c1c81c80862ca0882481c61c6083143080100083083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x94 : Ex t176 8 [v40,u0,u1,u2,u3,u4,u5] :=
  certify c176 [] (unpack 6 0x40634013199340274012400919a314a11628160c0e0c0e14152840211b3440061ab4401114894010150a40010c89400f0d0a400e0c91400d0d12402b401503830e18400b0385402619b1400840020d18400c0386 324 0x9674d39978d79678e79974d3a573d79278a2a178979273cf9938939233cf9533d39238a26a028a0578576a086005728a69f28a05325369f25f05328a69e28a04f24f69e25e04f28a19509571775719575571709719175171309319109171375318d14d70f08f18d08d70f14f04a08a6896c918a6ca04908211769711565511765711511511369311165111365311111110f64f10d10d10f68f10d64d04a04a10964910a64a04904910564510210210518510264211759711561511761711559511349311151111351311149110f38f10d40d10f40f10d38d04a04a10930910a2ca0490491052071021071051851020c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x95 : Ex t176 9 [v41,u1,u2,u0,u3,u4,u5] :=
  certify c176 [⟨_,p176x83⟩,⟨_,p176x72⟩,⟨_,p176x22⟩,⟨_,p176x93⟩,⟨_,p176x18⟩,⟨_,p176x94⟩,⟨_,p176x90⟩,⟨_,p176x91⟩] (unpack 6 0x199319a314a114a81b3240280c9813a30b934022078b150a0d0a15280d1219b1400a80078006038103830d184011160c4069148940010e0c40180c894009400e0e144068400d0c9180058004400680031ab480020386400c8001402c0e184026800040170385 308 0x5b2555599c595b2c725995556993d96b2c30699c196b23cf595c155b13cf5953d55b1c306992086a7be7699bd96a72085952085a6b26595b155a620844f208b64b2430fb0f4642081deb1e32e20831e21e1eeb2c323b2c0dd2080e3208b5db2c69b79e699ad969badb69979e59779e595a95597a9759579e45279e1cfa0fa52a1244f79e6a77676999596a79676997595a69665957555a67665959554648e450f74f0e476444f8cf8a181f0de09e1c675d69b69b69971969b71b6996995975975956155976175955954524121cf4cf5124d244f40f30a38a1c834830a2ca1c82481c61440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x96 : Ex t176 8 [v47,u0,u1,u3,u2,u4,u5] :=
  certify c176 [] (unpack 6 0x1628160c0e0c199319a31522152840211b340e14400a40261ab44011148940494010150a40010c894048400f0d0a40140383400c0e1840440c910d9340520d124008400b0385400d078d401c40020d18400e40330386 324 0x5a75d759c99c5a79a759c5d76e94926dca9c6e9aa96dc4925a84925974175a842859749216149214b40b16142114b49215c2dc16796515c95c1672cb1579571662cb1572d71669656d90d96dc91c6d99196dc0dc5949145970d75940d45979177d20d28d01907d21928d00c314b88b1610e114b0cb1618a16dc6dc6d97996dc79c6d96d959759759479459779759459429281229079029279229029014d78d14b14b14d14d14b78b2867862832832867c61437836dc69c6d97596dc75c6d96995975575946145976175945542924522902902924d229045014d3ce14b14e14d14d14b30b2862481431c81461c6143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x97 : Ex t176 8 [v48,u0,u1,u3,u2,u4,u5] :=
  certify c176 [] (unpack 6 0x1628160c0e0c0e95199319a314a11528400640261ab44011150a40564010148940010d0a4055400f0c8940140e18400c038340520d1240440c9140044002400d0d184035400b0385400e402e0386 324 0x52249251785752286251749266538e6579976659a565738e52438e51241252442451238e16338e14a40a16341014a38e15729716282015781716228a15281216128a15229216182065a0c36577d765a7da6570c35150c35121925151955120c374e18e7900c374e0ce79018614c0c314a18a14c18c14a0c365765765a71a65771765a65a51251251571551271251551524e24e25071024e70e25079014a70a14c14c14a14a14c70c14370324674624324324670665a61a6576d765a6da6576175154d55125925155955124d22503d024e24e25045024e3ce14c34c14a14a14c14c14a2ca2462061431c31461c6143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x98 : Ex t176 8 [v49,u2,u1,u3,u0,u4,u5] :=
  certify c176 [] (unpack 6 0x14a840064008400403860c98199319a314a1150a0d0a15280d1219b14026400c402d0385400d078d402c0d181ab14011160c406e4010148940010e0c406d400f0c89404d0e140f16405d404c0c91400e40680383 324 0x2e32492ce88e2e38a32ce24940e965420a6040ea4e4209652c99652df91f2c99092df96514396515d91d14390315d965a169246d49656d6965a149246939246a896569396569a92469a9246a79656a696569a92414e0ce16386114e84e1630c31498491620c31490c916286142052040e78e4207a040e50e2df79f2c95092df51f2c978915d71d14350315d51d14370369a51469359669b59615351415751869959815759615551441141140e4ce4114d140e40e2cc2cc2c94c92cc4cc2c92c91464c61431431461461434c34113d140e48e41149140e3ce2cc28c2c93492cc34c2c9289146207143143146146143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x99 : Ex t176 8 [v50,u2,u1,u3,u0,u4,u5] :=
  certify c176 [] (unpack 6 0x14a80d93400a199319a315221528150a0d0a40261ab14011148940704010160c40010c89406f400f0e0c40040c9840080386404c0c910d12404d0e144014402c400d0d184066402d0385400e40640383 324 0x56459655b8db5648e455b59669b3cf6a09e069b9db6a03cf5563cf55f45f55645655f3cf1663cf14c44c16645114c3cf9434437863cf7833c394645125d4512493cf25d3cf26545115b31b1648a215b89b16430c15689616330c1563161638a26a00c369b85b6a086069b0c355f0c355619655f19f5560c314c0c314a18a14c18c14a0c379e18615d0c379e0c325d18669869869b75b69875869b69b55355355675655375355655614a74a14c14c14a14a14c74c69b65b69871869b71b6986585565165535d35565d655351325141124f48f25149124f40f14c38d14a14d14c14c14a2ca2462061431c31461c6143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x100 : Ex t176 9 [v51,u1,u3,u0,u2,u4,u5] :=
  certify c176 [⟨_,p176x96⟩,⟨_,p176x97⟩,⟨_,p176x98⟩,⟨_,p176x99⟩] (unpack 6 0x1628160c0e0c0f16800380021ab114a8401b0d9340280c988001038680001ab4199319a31522406c0c91150a0d0a15284026078d0383400a0e180d12400e0d1806874047400d038540111489406b1a9540010c89406a1aa5 308 0x5b08204668605b69b04608216a451146ac616aaea1464510694510423c20693e904245126845124e3ce2683cf24e45136796534d45134d45136696514679e15691614690615679e04279e05581504280205579e41181184f79e8d179140f82026279e24e80e26282024e79e8528204cc79e4d279e84c82035f71c34d79e34d79e35d71c14638615b65914664615b38e04264205a38e04238205a6592583571563161465061565161463060555150423020553150425024d131140f48f4d149140f30c24e24e24d30c24924b24a2481461461441c41461c61441440420420400c00420c2040040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x101 : Ex t176 8 [v168,u0,u1,u3,u2,u4,u5] :=
  certify c176 [] (unpack 6 0x1628160c0e0c199319a314a1152840060d9313a60b9619b2038640034035400e0c984011148940544010150a40010c894053400f0d0a40140383400c0e1840440c910e1440520d1240044000402f0385402e400d0d18 324 0x4a74d34989984a79a74984d35e938e5d8a985e9aa95d838e4a838e4933134a832849338e08938e08a30a08930908a38e0982980a79650989580a728a0939530a628a0932930a69655d50c35d89185d59155d80c34900c34930134900104930c38ce00e74c0c38ce0ce74c0000a20c308a00a0a200008a0c35d879e5d58555d88585d579e49379e49081049381349079e18e7ce18c79e18e78e18c7cc08a79e08908908a08a08979e74374318079e0837837407406dc6da5d85985d56555d86585d559549345349051049351349045018e34e18c3cc18e18e18c34c08a2ca08908908a08a089207083043180140083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x102 : Ex t176 8 [v169,u0,u1,u3,u2,u4,u5] :=
  certify c176 [] (unpack 6 0x1628160c0e0c0e14199319a314a1152840211b3413a60b9619b20e180386400340111489404b4010150a40010c89404a400f0d0a4014078b400c038340440c9140520d1240004008078d402f40330d18400d0385400e401c0c98 324 0x56859655b9db5689e855b5966ab3cf69bb1b6abb2b69b3cf56a3cf5567d656a7ea5563cf1a93cf18d7cd1a97e918d3cf19b35b1a89a619b99b1a834d1969961a734d1963561a79a669815869b95b69895869b15b55395355615655315355695690f14f75f21f90f20f75f14518b8cb18d14d18b14b18d8cd69b79e69889869b89b69879e55679e55385355685655379e24f80f25f79e24f78f25f81f18d79e18b18b18d18d18b79e74874818579e24879e74574569b65b69871869b71b6986585565165535d35565d655351325141124f24f25149124f40f18d38d18b18b18d18d18b30b1881081852852481c3185103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x103 : Ex t176 8 [v170,u2,u1,u3,u0,u4,u5] :=
  certify c176 [] (unpack 6 0x14a840211b324004038640080c98199319a314a11528150a0d0a0f1640034014401840170385400d0d1813a30b9303834066400e0e184011160c40724010148940010e0c4071400f0c89404d0e140d124064404c0c91 324 0x22318620b88b2238a320b18634b9a635fa9f34ba8b35f9a62069a621e91e20690621e9a60809a60849040809000849a6718918a569a6a589987169246d39136e89a66d39936e89246e79246e59a66e79a66e592408b00b0a386108b84b0a30000868460a20000860060a286135f61834b80b35f81f34b61821e61820658621e59e20661809d61808058009d5960806186d359371c61809361371c5966da59609761809961809759634e4d334b54b34e54e34b4d32094d32065062095092064d30844d30800800840840804d345245034e30e34b3cb34e3ce34b30b2091c92062862092892061c6084144080080084083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x104 : Ex t176 8 [v171,u2,u1,u3,u0,u4,u5] :=
  certify c176 [] (unpack 6 0x14a840061b320c9840084004078e0386199319a314a1150a0d0a15280d1219b140034018400c4017078d400d0d18038513a30b9303834011160c40744010148940010e0c4073400f0c89404d0e144068404c0c91400e405d0e18 324 0x2a420828d8cd2a48e428d2083cd9653e1b213cdb0d3e19652889652a0a60288a482a096514396515ea5e143a4315e965718a69ad6965ad8965716a69692a526aa9656929526aaa6969a9656a89a66a79a669a96514d0cd1648a214d88d1640c31488881630c31480c81638a23e15a13cd7cd3e17e13cd58d2a07e02885882a05a02887c815e75e14358315e59e14374315259269c61869261269a59615b5961576186996151575953d04923cd50d3d05103cd49228b4922884c828b4cb2884921464921431431461461434923d03903cd44d3d04503cd38d28b24b28830828b30b2882481461c6143143146146143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x105 : Ex t176 9 [v52,u1,u3,u0,u2,u4,u5] :=
  certify c176 [⟨_,p176x101⟩,⟨_,p176x102⟩,⟨_,p176x103⟩,⟨_,p176x104⟩] (unpack 6 0x1628160c0e0c14a84022403b0e14402114a1150a0d0a15284009078d40030d100d180c914011199340751489400119a3406c0c898003800203830e188001800003860c98400e406a0d12400d40460385 308 0x3d438e3d24123d44143d238e4e62cb4d29d24e69e64d22cb3e52cb3ce28e3e52a53ce2cb0a12cb0962960a12a10962cb4d21c74de91e4d29124de1c73ce1c73dd19d3ce18e3dd1c780b18b8ca1c780b1cb88a1860961c70a11a10961960a11c765a1868171c781a1c76571864d25924d47df4d27d24d45963ce7ce3d05963ce58e3d07df4de5de4d27124de71e4d25d23dd71d3ce5ce3dd5dd3ce70e6cb5cb64a68a6cb68b64a5d70820980855d70960964d44d44d25524d45544d24d23d03d03ce44e3d04503ce3ce14b34b14a14a14b30b14a14a147247146146147207146146085103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x106 : Ex t176 8 [v59,u0,u2,u3,u1,u4,u5] :=
  certify c176 [] (unpack 6 0x15284006199319a31522160c0e0c16280e141b324028401419b240111489404f4010150a40010c89404e400f0d0a4026038540030d1840440c910e9540520d12400840160383400d078b4038402a0e18400e403e0386 324 0x5a85d759c9dc5a89e859c5d76d94926dca9c6d9a996dc49259449259741759441459749214b49216242214b40b162492a464107c34927c6492a4341015c2dc1689a615c99c1682cb1579971672cb1572d71679a66e50e56dc8dc6e58e56dc0dc5a48e45970d75a40e45978d716286214b0cb1620e214b84b6dc6dc6d97996dc79c6d96d959759759479459779759459429281229079029279229029014d78d14b14b14d14d14b78b2867862832832867c61437836dc69c6d97596dc75c6d96995975575946145976175945542924522902902924d229045014d3ce14b14e14d14d14b30b2862481431c81461c6143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x107 : Ex t176 8 [v60,u0,u2,u3,u1,u4,u5] :=
  certify c176 [] (unpack 6 0x15280d934006199319a314a11628160c0e0c4021401419b24011150a405a4010148940010d0a4059400f0c8940260d184003038540520d120e1440440c914004402a400d0e18404040160383400e403c0386 324 0x5654d35589185659255584d369b3cf698a1869ba1b6983cf5563cf5534535564565533cf1673cf14a44a16745114a3cf9834437863cf7833c39864511582981658e31588d816528a1538d316428a1532931648e36a10c36988986a18a16980c35600c35531935601a05530c314c0c314a18a14c18c14a0c369869869b75b69875869b69b55355355675655375355655624f24f25175124f74f2517d114a74a14c14c14a14a14c74c14374324678624324324674669b65b69871869b71b6986585565165535d35565d655351325141124f24f25149124f40f14c38d14a14a14c14c14a2ca2462061431c31461c6143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x108 : Ex t176 8 [v61,u1,u2,u3,u0,u4,u5] :=
  certify c176 [] (unpack 6 0x14a840214008400403860c98199319a314a1160c0e0c16280e141ab1401419b14011150a406e4010148940010d0a406d400f0c8940470d120f1640460c91400340180383400d078b405d402c0e18400e40660385 324 0x4a34104958954a38a34954105d59655d8a585d5a555d896549096549391349091049396514b96515d91d14b90b15d965a069246c39656c6965a0392429a9242a896529a96528a92428a9242a79652a696528a9241552d51638611558551632cb1508501622cb1502d01628615e00e05d57955e07a05d50d549f79f4900d049f0df49079015d71d14b0cb15d0dd14b70b5d85d85d56955d86985d55d549349349069049369349049014d68d14b14b14d14d14b68b2866862832832866c61436835d85985d56555d86585d559549345349051049351349045014d3ce14b14b14d14d14b30b2862481431c81461c6143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x109 : Ex t176 8 [v62,u1,u2,u3,u0,u4,u5] :=
  certify c176 [] (unpack 6 0x14a80d93400a4028199319a315221628160c0e0c401419b14011148940744010150a40010c894073400f0d0a40040c984008038640460c910e1440470d124026402c400d0e18406840180383400e40640385 324 0x56459655b8db5648e455b59669b3cf698a1869ba1b6983cf5563cf5534535564565533cf1673cf14a44a16745114a3cf9834437863cf7833c398645125d4512493cf25d3cf26545115b29b1648a215b89b16428a15689616328a1562961638a26a00c369b85b6a086069b0c355f0c355619655f19f5560c314c0c314a18a14c18c14a0c369869869b75b69875869b69b55355355675655375355655614a74a14c14c14a14a14c74c14374324678624324324674669b65b69871869b71b6986585565165535d35565d655351325141124f48f25149124f40f14c38d14a14d14c14c14a2ca2462061431c31461c6143103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x110 : Ex t176 9 [v63,u2,u3,u0,u1,u4,u5] :=
  certify c176 [⟨_,p176x106⟩,⟨_,p176x107⟩,⟨_,p176x108⟩,⟨_,p176x109⟩] (unpack 6 0x15280f168003800219b114a8150a0d0a4031038540220d180e954014078b40320c9880010386800019b2162440780c91160c0e0c16280e14400e0e180587404d400d0383401114894077199340010c89407619a3 308 0x44082046006044004046082163820146a46163a631468200628200427820627a204282026882024e78e26879e24e8207db79e70c82071b8207cc79e36796534d82034d8203669651465d71639231469061635d70425d70626620426420625d77e066069e5d78605e07de65925d5d724e64e25d65924e5d769b65970c5d771b5d768c65935855534d5d734d5d735655514638614451414650614438e04250204038e0423820405142533521513111463c61513d11463060503d00423020503100423c224e24e24d30c24924b24a2481461461441c41461c61441440420420400c00420c2040040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x111 : Ex t176 8 [v172,u0,u2,u3,u1,u4,u5] :=
  certify c176 [] (unpack 6 0x15284006199319a314a11628160c0e0c0e9513a60b961ab40386400c4040400e0c984011148940584010150a40010c894057400f0d0a4026038540030d1840440c9140520d124004402b40150383403c400d0e18 324 0x4674924579974679a745749259434d597a57594a5459734d44f34d4522d244f2cf45234d08734d0892c90872c708934d7032c3a0034da033437002cb0972570a79650979570a72490929520a62490922520a69655a30c35979175a39235970c34620c34520124620224520c30a10c30890090a10000890c359775d59481459781759475d45275d44f7cf4527d244f75d18d78d18b75d18d74d18b78b08975d08708708908908775d70370318075d08374370070069b69959755759461459761759455445241244f4cf4524d244f40f18d30d18b38b18d18d18b30b089289087087089089087207083043180140083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x112 : Ex t176 8 [v173,u0,u2,u3,u1,u4,u5] :=
  certify c176 [] (unpack 6 0x15284006199319a314a1160c0e0c16280e141b3213a60b961ab40d180386400c4011148940514010150a40010c894050400f0d0a4026078d4003038540440c9140520d12402b4008078b4015403e0e18400d0383400e40380c98 324 0x56a59655ba5b56aa6a55b5966983cf69bb1b698b1869b3cf5533cf5567d65537d35563cf18b3cf18d7cd18b7cb18d3cf7487dfac53cfac83cf7457df19b35b1aaa2819ba1b1aa34d196a161a934d1963561a9a286a716769b95b6a796769b15b5669665561565661665569561a48e418d14d1a416418d8cd69b79e69889869b89b69879e55679e55385355685655379e24f80f25f79e24f78f25f81f18d79e18b18b18d18d18b79e74874818579e24879e74574569b65b69871869b71b6986585565165535d35565d655351325141124f24f25149124f40f18d38d18b18b18d18d18b30b1881081852852481c3185103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x113 : Ex t176 8 [v174,u1,u2,u3,u0,u4,u5] :=
  certify c176 [] (unpack 6 0x14a840061b344004038640080c98199319a314a11628160c0e0c0f1613a50b950385400c4068400e0d184011150a40724010148940010d0a4071400f0c8940470d1240460c914026402d401703834064400d0e18 324 0x3622cb3508503628623502cb490965493a53490a5049396534b96534e8ce34b8cb34e9650879650898c90878c70899656038c3a00965a039436008e31998d91a79651999591a78e31a68e31a49651a69651a48e30901d00a28200908100a21c708b80b0a11c708b1cb0a182049e0c34907d049e7de4900c335d0c334b00b35d01d34b0c309c0c308700709c0000870c34936594906d04936d349065934e65934b68b34e68e34b65908965908708708908908765960360318065908364360060059759549345349051049351349045034e30e34b3cb34e3ce34b30b089289087087089089087207083043180140083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x114 : Ex t176 8 [v175,u1,u2,u3,u0,u4,u5] :=
  certify c176 [] (unpack 6 0x14a840061b340c9840084004078e0386199319a314a1160c0e0c16280e141ab113a50b950385400c4011150a40704010148940010d0a406f400f0c8940470d1240460c91402d4003078b401740660e18400d0383400e405d0d18 324 0x4643cf4548d44648e44543cf594965597b17594b1459796544f965452a5244fa4f45296518b96518da4d18ba4b18d965648a69ac5965ac8965645a6925aa5a26a96525a95a26aa692499652689a62679a62499651942d41a48a21948941a42cb18f88f1a32cb18f2cf1a38a25a11615947d45a17e15941544607e044f14f46016044f7cf19e75e18b14b19e15e18b74b59769a59471459771759469a45269a44f6cf4526d244f69a18d69a18b18b18d18d18b69a64864818569a24869a64564559755759461459761759455445241244f4cf4524d244f40f18d38d18b18b18d18d18b30b1881081852852481c3185103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x115 : Ex t176 9 [v64,u2,u3,u0,u1,u4,u5] :=
  certify c176 [⟨_,p176x111⟩,⟨_,p176x112⟩,⟨_,p176x113⟩,⟨_,p176x114⟩] (unpack 6 0x152814a8150a0d0a400a40290d124006078b400c199319a314a1160c0e0c16280e100e180c9140111a954079148940011aa540780c898003800203850d188001800003860c98400e40760e14400d404c0383 308 0x3de38e3d27523de75e3d238e4e62cb4d2a124e6a264d22cb3e52cb3ce28e3e52a53ce2cb0a22cb0962960a22a20962cb7e028a9172cb9202cb7d728a4d21c74e69e64d29d24e61c73ce1c73e51a53ce18e3e51c784b18b90a1c784b1cb8ca1860961c70a21a20961960a21c77e01868571c78601c77d71864d25924de71c4d27124de5963ce70e3dd5963ce58e3dd71c4db5db4d26524db65b4d25d23da65a3ce5ce3da5da3ce64e0820980855d70960964d44d44d25524d45544d24d23d03d03ce44e3d04503ce3ce14b34b14a14a14b30b14a14a147247146146147207146146085103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p176x116 : Ex t176 10 (roots 63) :=
  certify c176 [⟨_,p176x14⟩,⟨_,p176x21⟩,⟨_,p176x28⟩,⟨_,p176x33⟩,⟨_,p176x46⟩,⟨_,p176x51⟩,⟨_,p176x56⟩,⟨_,p176x59⟩,⟨_,p176x64⟩,⟨_,p176x69⟩,⟨_,p176x82⟩,⟨_,p176x87⟩,⟨_,p176x92⟩,⟨_,p176x95⟩,⟨_,p176x100⟩,⟨_,p176x105⟩,⟨_,p176x110⟩,⟨_,p176x115⟩] (unpack 6 0x199319a314a11628160c0e0c801180100e141528800f800e800d800c800b800a14a814894011150a0c8940010d0a800980080c91400d0d12800780068005038380040e188003800280010386038580000d180c98 240 0x529555518a18529a295185555d84185e99e75d89d85e94105159d55284105154155289e75e528a5d89985e59a55d828a52428a51521552422451528a3e128a8d02108a12213d028a5d60c35d88185d68165d80c35130c35150555130535150c33ce0c37d005078e04e3d00c374a04a7080c36ca0ca6880415d81045d66565d86585d61045151045130135150155131043d010448e00e4500103ce10434a00a3081042ca10a2480001c3003181104143103081000) (by decide +kernel)
theorem l176 : CClaim 63 t176 11 := fromTable 311689265798 (by decide +kernel) p176x116
open PEqualNP.CircuitLowerBounds

def graph : Sig := t176
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276682368 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def smallCircuit : Circuit := ⟨[
  ⟨.and,[0,1]⟩,
  ⟨.or,[0,1]⟩,
  ⟨.and,[4,5]⟩,
  ⟨.or,[4,5]⟩,
  ⟨.or,[2,6]⟩,
  ⟨.and,[3,9]⟩,
  ⟨.and,[8,10]⟩,
  ⟨.or,[6,11]⟩,
  ⟨.or,[11,12]⟩,
  ⟨.and,[2,13]⟩,
  ⟨.and,[7,14]⟩,
  ⟨.or,[15,16]⟩],17⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 12 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim


def sixInputs : List Sig := roots 63
def sampleSix (r : Row) (i : Fin 6) : Bool := bit r (sixInputs.getD i.val zero)
theorem sixList : List.ofFn (fun i : Fin 6 => sixInputs.getD i.val zero) = sixInputs := rfl
theorem sixSampled (r : Row) : List.ofFn (sampleSix r) = sixInputs.map (bit r) := by
  rw [←sixList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sixTable : ∀ r : Row, bit r graph = target (sampleSix r) := by decide +kernel

theorem sixEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sixInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSix r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sixSampled]
  rfl

def lowRow (i : Fin 6) : Row := Fin.ofNat 128 (([6,5,3,17,9,9] : List Nat).getD i.val 0)
def highRow (i : Fin 6) : Row := Fin.ofNat 128 ((lowRow i).val ||| (1 <<< i.val))

set_option maxHeartbeats 1000000 in
theorem allSixRequired :
    (∀ i : Fin 6, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 6, i ≠ j →
      bit (lowRow i) (sixInputs.getD j.val zero) =
      bit (highRow i) (sixInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sixInputs.toFinset := by
  have goalEq : (execute C.gates sixInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sixEval C legal C.output r).trans ((computes (sampleSix r)).trans (sixTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sixInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sixInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sixInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sixInputs) : ∃ i : Fin 6, sixInputs.getD i.val zero = a := by
    rw [←sixList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sixInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sixInputs (sixInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSixRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSixRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 10 sixInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 6 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 6 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 12 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim

end PEqualNP.Outside.L_meta_12327

open PEqualNP.Outside.L_meta_12327 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_12327 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682368 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682368 * 2 ^ 32 + 4269834368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  obtain ⟨C,legal,bound,ev⟩ := h
  have fit : ∀ g ∈ C.gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal g hg
  obtain ⟨gs,o,mono,sz,correct⟩ := replaceShort p176x116 C.gates C.output fit ev
  refine ⟨⟨gs,o⟩,?_,sz.trans bound,correct⟩
  intro g hg
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using mono g hg
