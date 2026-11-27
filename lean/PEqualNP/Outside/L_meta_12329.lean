import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12329

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
abbrev v6 : Sig := 0x7f007f007f007f007f007f007f007f00
abbrev v7 : Sig := 0x80808080808080808080808080808080
abbrev v8 : Sig := 0x70707070707070707070707070707070
abbrev v9 : Sig := 0x70f070f070f070f070f070f070f070f0
abbrev v10 : Sig := 0x88008800880088008800880088008800
abbrev v11 : Sig := 0x77007700770077007700770077007700
abbrev v12 : Sig := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
abbrev v13 : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
abbrev v14 : Sig := 0x88888888888888888888888888888888
abbrev v15 : Sig := 0xcc00cc00cc00cc00cc00cc00cc00cc00
abbrev v16 : Sig := 0xaa00aa00aa00aa00aa00aa00aa00aa00
abbrev v17 : Sig := 0x4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c
abbrev v18 : Sig := 0x4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc
abbrev v19 : Sig := 0xa000a000a000a000a000a000a000a000
abbrev v20 : Sig := 0x5f005f005f005f005f005f005f005f00
abbrev v21 : Sig := 0xf000f000f000f000f000f000f000f000
abbrev v22 : Sig := 0x44cc44cc44cc44cc44cc44cc44cc44cc
abbrev v23 : Sig := 0x50f050f050f050f050f050f050f050f0
abbrev v24 : Sig := 0x2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa
abbrev v25 : Sig := 0xc000c000c000c000c000c000c000c000
abbrev v26 : Sig := 0x3f003f003f003f003f003f003f003f00
abbrev v27 : Sig := 0x2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a
abbrev v28 : Sig := 0x30f030f030f030f030f030f030f030f0
abbrev v29 : Sig := 0x22aa22aa22aa22aa22aa22aa22aa22aa
abbrev v30 : Sig := 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa
abbrev v31 : Sig := 0xccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc
abbrev v32 : Sig := 0xfe00fe00fe00fe00fe00fe00fe00fe
abbrev v33 : Sig := 0xfefefefefefefefefefefefefefefefe
abbrev v34 : Sig := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
abbrev v35 : Sig := 0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e
abbrev v36 : Sig := 0xffeeffeeffeeffeeffeeffeeffeeffee
abbrev v37 : Sig := 0xee00ee00ee00ee00ee00ee00ee00ee
abbrev v38 : Sig := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
abbrev v39 : Sig := 0xfafafafafafafafafafafafafafafafa
abbrev v40 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
abbrev v41 : Sig := 0xffccffccffccffccffccffccffccffcc
abbrev v42 : Sig := 0xffaaffaaffaaffaaffaaffaaffaaffaa
abbrev v43 : Sig := 0x33323332333233323332333233323332
abbrev v44 : Sig := 0xfffafffafffafffafffafffafffafffa
abbrev v45 : Sig := 0xfa00fa00fa00fa00fa00fa00fa00fa
abbrev v46 : Sig := 0xfff0fff0fff0fff0fff0fff0fff0fff0
abbrev v47 : Sig := 0x32323232323232323232323232323232
abbrev v48 : Sig := 0x33223322332233223322332233223322
abbrev v49 : Sig := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
abbrev v50 : Sig := 0x55545554555455545554555455545554
abbrev v51 : Sig := 0xfffcfffcfffcfffcfffcfffcfffcfffc
abbrev v52 : Sig := 0xfc00fc00fc00fc00fc00fc00fc00fc
abbrev v53 : Sig := 0x54545454545454545454545454545454
abbrev v54 : Sig := 0x55445544554455445544554455445544
abbrev v55 : Sig := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c
abbrev v56 : Sig := 0x55505550555055505550555055505550
abbrev v57 : Sig := 0x33303330333033303330333033303330
abbrev v58 : Sig := 0xfefe0000fefe0000fefe0000fefe
abbrev v59 : Sig := 0xf0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e
abbrev v60 : Sig := 0xffffeeeeffffeeeeffffeeeeffffeeee
abbrev v61 : Sig := 0xeeee0000eeee0000eeee0000eeee
abbrev v62 : Sig := 0xffffccccffffccccffffccccffffcccc
abbrev v63 : Sig := 0xffffaaaaffffaaaaffffaaaaffffaaaa
abbrev v64 : Sig := 0x33333232333332323333323233333232
abbrev v65 : Sig := 0xfffffafafffffafafffffafafffffafa
abbrev v66 : Sig := 0xfafa0000fafa0000fafa0000fafa
abbrev v67 : Sig := 0xfffff0f0fffff0f0fffff0f0fffff0f0
abbrev v68 : Sig := 0x33332222333322223333222233332222
abbrev v69 : Sig := 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a
abbrev v70 : Sig := 0x55555454555554545555545455555454
abbrev v71 : Sig := 0xfffffcfcfffffcfcfffffcfcfffffcfc
abbrev v72 : Sig := 0xfcfc0000fcfc0000fcfc0000fcfc
abbrev v73 : Sig := 0x55554444555544445555444455554444
abbrev v74 : Sig := 0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c
abbrev v75 : Sig := 0x55555050555550505555505055555050
abbrev v76 : Sig := 0x33333030333330303333303033333030
abbrev v77 : Sig := 0x7f7f00007f7f00007f7f00007f7f0000
abbrev v78 : Sig := 0x7070f0f07070f0f07070f0f07070f0f0
abbrev v79 : Sig := 0x88880000888800008888000088880000
abbrev v80 : Sig := 0x77770000777700007777000077770000
abbrev v81 : Sig := 0xcccc0000cccc0000cccc0000cccc0000
abbrev v82 : Sig := 0xaaaa0000aaaa0000aaaa0000aaaa0000
abbrev v83 : Sig := 0x4c4ccccc4c4ccccc4c4ccccc4c4ccccc
abbrev v84 : Sig := 0xa0a00000a0a00000a0a00000a0a00000
abbrev v85 : Sig := 0x5f5f00005f5f00005f5f00005f5f0000
abbrev v86 : Sig := 0xf0f00000f0f00000f0f00000f0f00000
abbrev v87 : Sig := 0x4444cccc4444cccc4444cccc4444cccc
abbrev v88 : Sig := 0x5050f0f05050f0f05050f0f05050f0f0
abbrev v89 : Sig := 0x2a2aaaaa2a2aaaaa2a2aaaaa2a2aaaaa
abbrev v90 : Sig := 0xc0c00000c0c00000c0c00000c0c00000
abbrev v91 : Sig := 0x3f3f00003f3f00003f3f00003f3f0000
abbrev v92 : Sig := 0x3030f0f03030f0f03030f0f03030f0f0
abbrev v93 : Sig := 0x2222aaaa2222aaaa2222aaaa2222aaaa
abbrev v94 : Sig := 0xa0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa
abbrev v95 : Sig := 0xc0ccccc0c0ccccc0c0ccccc0c0ccccc
abbrev v96 : Sig := 0xffffaa00ffffaa00ffffaa00ffffaa00
abbrev v97 : Sig := 0x55ff000055ff000055ff000055ff0000
abbrev v98 : Sig := 0xffffffffaa00aa00ffffffffaa00aa00
abbrev v99 : Sig := 0x55ff55ff0000000055ff55ff00000000
abbrev v100 : Sig := 0xffaa0000ffaa0000ffaa0000ffaa0000
abbrev v101 : Sig := 0xffaa0000ffaa0000ffaa0000ffaa
abbrev v102 : Sig := 0xffaaffaa00000000ffaaffaa00000000
abbrev v103 : Sig := 0xffaaffaa00000000ffaaffaa
abbrev v104 : Sig := 0xaa00aa00aa00aa00aa00aa00aa00aa
abbrev v105 : Sig := 0x55005500550055005500550055005500
abbrev v106 : Sig := 0xffffffff0000aaaaffffffff0000aaaa
abbrev v107 : Sig := 0xffff555500000000ffff555500000000
abbrev v108 : Sig := 0xaaaa0000aaaa0000aaaa0000aaaa
abbrev v109 : Sig := 0xffffffff55550000ffffffff55550000
abbrev v110 : Sig := 0xaaaaffff00000000aaaaffff00000000
abbrev v111 : Sig := 0x55550000555500005555000055550000
abbrev v112 : Sig := 0xffffffffaaaaaaaaffffffffaaaaaaaa
abbrev v113 : Sig := 0xaaaaaaaa00000000aaaaaaaa00000000
abbrev v114 : Sig := 0xffff0000ffffaaaaffff0000ffffaaaa
abbrev v115 : Sig := 0xffff000055550000ffff000055550000
abbrev v116 : Sig := 0xaaaaaaaa00000000aaaaaaaa
abbrev v117 : Sig := 0xffff5555ffff0000ffff5555ffff0000
abbrev v118 : Sig := 0xaaaa0000ffff0000aaaa0000ffff0000
abbrev v119 : Sig := 0x55555555000000005555555500000000
abbrev v120 : Sig := 0xffffffffff000000ffffffffff000000
abbrev v121 : Sig := 0xffffff0000000000ffffff00000000
abbrev v122 : Sig := 0xffaaaaaaffaaaaaaffaaaaaaffaaaaaa
abbrev v123 : Sig := 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa
abbrev v124 : Sig := 0xff000000ff000000ff000000ff000000
abbrev v125 : Sig := 0xffffff0000000000ffffff0000000000
abbrev v126 : Sig := 0xffffff0000000000ffffff00
abbrev v127 : Sig := 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00
abbrev v128 : Sig := 0x55555500555555005555550055555500
abbrev v129 : Sig := 0xffffff00ffffff00ffffff00ffffff00
abbrev v130 : Sig := 0xff000000ff000000ff000000ff00
abbrev v131 : Sig := 0xff000000ff000000ff000000ff0000
abbrev v132 : Sig := 0xffffff00ffff0000ffffff00ffff0000
abbrev v133 : Sig := 0xff0000ffff000000ff0000ffff0000
abbrev v134 : Sig := 0xffaaffaaaaaaaaaaffaaffaaaaaaaaaa
abbrev v135 : Sig := 0xaa00aaaaaaaaaa00aa00aaaaaaaaaa
abbrev v136 : Sig := 0xff00ff0000000000ff00ff0000000000
abbrev v137 : Sig := 0xaaaaaaaaaa00aa00aaaaaaaaaa00aa00
abbrev v138 : Sig := 0x55555555550055005555555555005500
abbrev v139 : Sig := 0xffff0000ff000000ffff0000ff000000
abbrev v140 : Sig := 0xffff0000ff000000ffff0000ff00
abbrev v141 : Sig := 0xffffffffff00ff00ffffffffff00ff00
abbrev v142 : Sig := 0xff00ff0000000000ff00ff00
abbrev v143 : Sig := 0xff00ff0000000000ff00ff00000000
abbrev v144 : Sig := 0xffffffffffff0000ffffffffffff0000
abbrev v145 : Sig := 0xffff000000000000ffff000000000000
abbrev v146 : Sig := 0xaaaaaaaaffffaaaaaaaaaaaaffffaaaa
abbrev v147 : Sig := 0xaaaaaaaa0000aaaaaaaaaaaa0000aaaa
abbrev v148 : Sig := 0xffff000000000000ffff0000
abbrev v149 : Sig := 0xaaaaffffaaaaaaaaaaaaffffaaaaaaaa
abbrev v150 : Sig := 0xaaaa0000aaaaaaaaaaaa0000aaaaaaaa
abbrev v151 : Sig := 0xffff000000000000ffff00000000
abbrev v152 : Sig := 0xffffcc00ffffcc00ffffcc00ffffcc00
abbrev v153 : Sig := 0x33ff000033ff000033ff000033ff0000
abbrev v154 : Sig := 0xffffffffcc00cc00ffffffffcc00cc00
abbrev v155 : Sig := 0x33ff33ff0000000033ff33ff00000000
abbrev v156 : Sig := 0xffcc0000ffcc0000ffcc0000ffcc0000
abbrev v157 : Sig := 0xffcc0000ffcc0000ffcc0000ffcc
abbrev v158 : Sig := 0xffccffcc00000000ffccffcc00000000
abbrev v159 : Sig := 0xffccffcc00000000ffccffcc
abbrev v160 : Sig := 0xcc00cc00cc00cc00cc00cc00cc00cc
abbrev v161 : Sig := 0x33003300330033003300330033003300
abbrev v162 : Sig := 0xffffffff0000ccccffffffff0000cccc
abbrev v163 : Sig := 0xffff333300000000ffff333300000000
abbrev v164 : Sig := 0xcccc0000cccc0000cccc0000cccc
abbrev v165 : Sig := 0xffffffff33330000ffffffff33330000
abbrev v166 : Sig := 0xccccffff00000000ccccffff00000000
abbrev v167 : Sig := 0x33330000333300003333000033330000
abbrev v168 : Sig := 0xffffffffccccccccffffffffcccccccc
abbrev v169 : Sig := 0xcccccccc00000000cccccccc00000000
abbrev v170 : Sig := 0xffff0000ffffccccffff0000ffffcccc
abbrev v171 : Sig := 0xffff000033330000ffff000033330000
abbrev v172 : Sig := 0xcccccccc00000000cccccccc
abbrev v173 : Sig := 0xffff3333ffff0000ffff3333ffff0000
abbrev v174 : Sig := 0xcccc0000ffff0000cccc0000ffff0000
abbrev v175 : Sig := 0x33333333000000003333333300000000
abbrev v176 : Sig := 0xffccccccffccccccffccccccffcccccc
abbrev v177 : Sig := 0xcccccc00cccccc00cccccc00cccccc
abbrev v178 : Sig := 0xcccccc00cccccc00cccccc00cccccc00
abbrev v179 : Sig := 0x33333300333333003333330033333300
abbrev v180 : Sig := 0xffccffccccccccccffccffcccccccccc
abbrev v181 : Sig := 0xcc00cccccccccc00cc00cccccccccc
abbrev v182 : Sig := 0xcccccccccc00cc00cccccccccc00cc00
abbrev v183 : Sig := 0x33333333330033003333333333003300
abbrev v184 : Sig := 0xccccccccffffccccccccccccffffcccc
abbrev v185 : Sig := 0xcccccccc0000cccccccccccc0000cccc
abbrev v186 : Sig := 0xccccffffccccccccccccffffcccccccc
abbrev v187 : Sig := 0xcccc0000cccccccccccc0000cccccccc
abbrev v188 : Sig := 0xfffff000fffff000fffff000fffff000
abbrev v189 : Sig := 0xfff00000fff00000fff00000fff0000
abbrev v190 : Sig := 0xfffffffff000f000fffffffff000f000
abbrev v191 : Sig := 0xfff0fff000000000fff0fff00000000
abbrev v192 : Sig := 0xfff00000fff00000fff00000fff00000
abbrev v193 : Sig := 0xfff00000fff00000fff00000fff0
abbrev v194 : Sig := 0xfff0fff000000000fff0fff000000000
abbrev v195 : Sig := 0xfff0fff000000000fff0fff0
abbrev v196 : Sig := 0xf000f000f000f000f000f000f000f0
abbrev v197 : Sig := 0xf000f000f000f000f000f000f000f00
abbrev v198 : Sig := 0xffffffff0000f0f0ffffffff0000f0f0
abbrev v199 : Sig := 0xffff0f0f00000000ffff0f0f00000000
abbrev v200 : Sig := 0xf0f00000f0f00000f0f00000f0f0
abbrev v201 : Sig := 0xffffffff0f0f0000ffffffff0f0f0000
abbrev v202 : Sig := 0xf0f0ffff00000000f0f0ffff00000000
abbrev v203 : Sig := 0xf0f00000f0f00000f0f00000f0f0000
abbrev v204 : Sig := 0xfffffffff0f0f0f0fffffffff0f0f0f0
abbrev v205 : Sig := 0xf0f0f0f000000000f0f0f0f000000000
abbrev v206 : Sig := 0xffff0000fffff0f0ffff0000fffff0f0
abbrev v207 : Sig := 0xffff00000f0f0000ffff00000f0f0000
abbrev v208 : Sig := 0xf0f0f0f000000000f0f0f0f0
abbrev v209 : Sig := 0xffff0f0fffff0000ffff0f0fffff0000
abbrev v210 : Sig := 0xf0f00000ffff0000f0f00000ffff0000
abbrev v211 : Sig := 0xf0f0f0f000000000f0f0f0f00000000
abbrev v212 : Sig := 0xfff0f0f0fff0f0f0fff0f0f0fff0f0f0
abbrev v213 : Sig := 0xf0f0f000f0f0f000f0f0f000f0f0f0
abbrev v214 : Sig := 0xf0f0f000f0f0f000f0f0f000f0f0f000
abbrev v215 : Sig := 0xf0f0f000f0f0f000f0f0f000f0f0f00
abbrev v216 : Sig := 0xfff0fff0f0f0f0f0fff0fff0f0f0f0f0
abbrev v217 : Sig := 0xf000f0f0f0f0f000f000f0f0f0f0f0
abbrev v218 : Sig := 0xf0f0f0f0f000f000f0f0f0f0f000f000
abbrev v219 : Sig := 0xf0f0f0f0f000f000f0f0f0f0f000f00
abbrev v220 : Sig := 0xf0f0f0f0fffff0f0f0f0f0f0fffff0f0
abbrev v221 : Sig := 0xf0f0f0f00000f0f0f0f0f0f00000f0f0
abbrev v222 : Sig := 0xf0f0fffff0f0f0f0f0f0fffff0f0f0f0
abbrev v223 : Sig := 0xf0f00000f0f0f0f0f0f00000f0f0f0f0
abbrev v224 : Sig := 0x22222222222222222222222222222222
abbrev v225 : Sig := 0x44444444444444444444444444444444
abbrev v226 : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
abbrev v227 : Sig := 0x50505050505050505050505050505050
abbrev v228 : Sig := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
abbrev v229 : Sig := 0x30303030303030303030303030303030

abbrev t37 : Sig := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c37 : Cuts t37 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p37x0 : Ex t37 3 (roots 7) :=
  certify c37 [] (unpack 3 0x28103020182018103040284 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l37 : CClaim 7 t37 4 := fromTable 16514 (by decide +kernel) p37x0

abbrev t40 : Sig := 0xee88ee88ee88ee88ee88ee88ee88ee88
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c40 : Cuts t40 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p40x0 : Ex t40 3 (roots 11) :=
  certify c40 [] (unpack 3 0x48105020182018105080488 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l40 : CClaim 11 t40 4 := fromTable 2097282 (by decide +kernel) p40x0

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

abbrev t50 : Sig := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c50 : Cuts t50 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p50x0 : Ex t50 3 (roots 14) :=
  certify c50 [] (unpack 3 0x50206040304030206080508 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l50 : CClaim 14 t50 4 := fromTable 4227584 (by decide +kernel) p50x0

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

abbrev t57 : Sig := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c57 : Cuts t57 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p57x0 : Ex t57 3 (roots 21) :=
  certify c57 [] (unpack 3 0x8810a04028402810a100890 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l57 : CClaim 21 t57 4 := fromTable 268451844 (by decide +kernel) p57x0

abbrev t60 : Sig := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c60 : Cuts t60 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p60x0 : Ex t60 3 (roots 22) :=
  certify c60 [] (unpack 3 0x9020a04030403020a100910 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l60 : CClaim 22 t60 4 := fromTable 536904192 (by decide +kernel) p60x0

abbrev t75 : Sig := 0xeeeeeeee88888888eeeeeeee88888888
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c75 : Cuts t75 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p75x0 : Ex t75 3 (roots 35) :=
  certify c75 [] (unpack 3 0x1081110201820181112010a0 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l75 : CClaim 35 t75 4 := fromTable 34359738498 (by decide +kernel) p75x0

abbrev t78 : Sig := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c78 : Cuts t78 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p78x0 : Ex t78 3 (roots 37) :=
  certify c78 [] (unpack 3 0x1081120402840281122010a0 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l78 : CClaim 37 t78 4 := fromTable 34359754756 (by decide +kernel) p78x0

abbrev t110 : Sig := 0xe880e880e880e880e880e880e880e880
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c110 : Cuts t110 := [
  rule t110 1 l50 none (by decide +kernel),
  rule t110 2 l45 none (by decide +kernel),
  rule t110 8 l37 none (by decide +kernel),
  rule t110 4 l40 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x0 : Ex t110 3 [v6,u2,u0,u1] :=
  certify c110 [] (unpack 4 0x589068c058a038507060386058306850383 24 0x50853570306122542232010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x1 : Ex t110 4 [v7,u2,u0,u1,u3] :=
  certify c110 [⟨_,p110x0⟩] (unpack 4 0x7060589068c070a0689058a0685800040020583038503860383 31 0x3636b89b3c3cb7ba898763635343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x2 : Ex t110 4 [v8,u2,u0,u1,u3] :=
  certify c110 [] (unpack 4 0x706038306850583070c05890385068c058a03860689 37 0x787896957a7a5253939297898787654432110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x3 : Ex t110 3 [v9,u3,u0,u1] :=
  certify c110 [] (unpack 4 0x68c0706038505890386058a058306850383 24 0x212664682724600540030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x4 : Ex t110 4 [v10,u3,u0,u1,u2] :=
  certify c110 [⟨_,p110x3⟩] (unpack 4 0x689070a0385068c0706068503868000400303830589058a0583 31 0x3c733a3ca78a363ba6a978765343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x5 : Ex t110 4 [v11,u3,u0,u1,u2] :=
  certify c110 [] (unpack 4 0x70a058306890383070c05890385068c058a03860685 37 0x798774789694717a414393918787645431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x6 : Ex t110 3 [v12,v13,v14,u3] :=
  certify c110 [] (unpack 4 0x386400103850589068503834000068907060583 24 0x50599867736505044321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x7 : Ex t110 4 [v13,u2,v14,u1,u3] :=
  certify c110 [⟨_,p110x6⟩] (unpack 4 0x80000385070a40030386058a06850583070c4001068c0383 34 0x4545939b4545a698677265454545413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x8 : Ex t110 3 [v15,v16,v14,u2] :=
  certify c110 [] (unpack 4 0x400103850689058340000685070a07060383 24 0x70673877147603055432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x9 : Ex t110 4 [v16,u3,v14,u1,u2] :=
  certify c110 [⟨_,p110x8⟩] (unpack 4 0x8000038507064002058a038606890383070c4001068c0583 34 0x45944545939b4645a69866726545413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x10 : Ex t110 4 [v12,u2,v14,u0,u3] :=
  certify c110 [⟨_,p110x6⟩] (unpack 4 0x8000070c068c0386068940030385400005890685070605830383 34 0x12128a8cab5a1313948746654313121210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x11 : Ex t110 4 [v15,u3,v14,u0,u2] :=
  certify c110 [⟨_,p110x8⟩] (unpack 4 0x8000070c068c0689038606854002058940000385070a03830583 34 0x197112127a7cab4a131983763354321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x12 : Ex t110 5 [v14,u0,u1,u2,u3] :=
  certify c110 [⟨_,p110x1⟩,⟨_,p110x2⟩,⟨_,p110x4⟩,⟨_,p110x5⟩,⟨_,p110x7⟩,⟨_,p110x9⟩,⟨_,p110x10⟩,⟨_,p110x11⟩] (unpack 5 0x80078006800507068004070a068c070c80034002058380020685800140030383800006890385400140000386 99 0x24c6591692256632c4b4b92b72d3549846238867189422c2b93e4b7ae539182683e0679a11805ef709c10856d5a5895b169524c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x13 : Ex t110 4 [v17,u1,u0,u2,u3] :=
  certify c110 [] (unpack 4 0x706038505830685070a06890383058a068c03860589 37 0x78788a8a56539392878969958787654432110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x14 : Ex t110 3 [v18,u3,u0,u2] :=
  certify c110 [] (unpack 4 0x58a0706038305890386068c068505830385 24 0x612664681714606540031210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x15 : Ex t110 4 [v19,u3,u0,u2,u1] :=
  certify c110 [⟨_,p110x14⟩] (unpack 4 0x589070c0383058a0706058303868000400103850689068c0685 31 0xa3ac7c73a78a363ba6a978765343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x16 : Ex t110 4 [v20,u3,u0,u2,u1] :=
  certify c110 [] (unpack 4 0x70c068505890385070a06890383058a03860583 37 0x3637687635836169313282817676534321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x17 : Ex t110 3 [v21,v16,v13,u1] :=
  certify c110 [] (unpack 4 0x70c40030706038305890385068540000583 24 0x386335545075561540030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x18 : Ex t110 4 [v16,u3,v13,u2,u1] :=
  certify c110 [⟨_,p110x17⟩] (unpack 4 0x8000038307064002038605890385070a4003058a0583 34 0x54454584838a4645968766126545413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x19 : Ex t110 4 [v21,u3,v13,u0,u1] :=
  certify c110 [⟨_,p110x17⟩] (unpack 4 0x70c8000070a058a038505890386058340020689400003830685 34 0x57588ca8898c595b9a2981176154113210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x20 : Ex t110 4 [v12,u1,v13,u0,u3] :=
  certify c110 [⟨_,p110x6⟩] (unpack 4 0x8000070a058a0386400105890383400006890685070605830385 34 0x12127a7cab5a3131947876654131321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x21 : Ex t110 5 [v13,u0,u2,u1,u3] :=
  certify c110 [⟨_,p110x1⟩,⟨_,p110x13⟩,⟨_,p110x15⟩,⟨_,p110x16⟩,⟨_,p110x7⟩,⟨_,p110x18⟩,⟨_,p110x19⟩,⟨_,p110x20⟩] (unpack 5 0x80078006800507068004070c058a070a80034002068580020583800140010385800005890383400340000386 99 0x24c9591692256633884118ce31aa422c4b4b92b72d344a42993e497a6539182683de679a11805ef709c10856d5a5895b169524c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x22 : Ex t110 4 [v22,u1,u0,u3,u2] :=
  certify c110 [] (unpack 4 0x70a058903830689070606850583068c0386058a0385 37 0x8758828a56529223878965658787654423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x23 : Ex t110 4 [v23,u2,u0,u3,u1] :=
  certify c110 [] (unpack 4 0x70c0689038505890706068505830386058a0383 37 0x3637677672793532822153537676534321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x24 : Ex t110 4 [v15,u1,v16,u0,u2] :=
  certify c110 [⟨_,p110x8⟩] (unpack 4 0x80000386058a400105834000068503850689070a070603830589 34 0x1b135b5cb27b4161a65958876151431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x25 : Ex t110 4 [v21,u2,v16,u0,u1] :=
  certify c110 [⟨_,p110x17⟩] (unpack 4 0x70c80000706038605890385058a400303830685400005830689 34 0x47487ca7797c494b9a2981176145413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x26 : Ex t110 5 [v16,u0,u3,u1,u2] :=
  certify c110 [⟨_,p110x4⟩,⟨_,p110x22⟩,⟨_,p110x15⟩,⟨_,p110x23⟩,⟨_,p110x9⟩,⟨_,p110x18⟩,⟨_,p110x24⟩,⟨_,p110x25⟩] (unpack 5 0x800780068005070a8004070c038607068003400306898002038380014001058980000385058340024000058a 99 0x392912d6e5baa94a4c9590892256633884118ce33a842242993de97a6539102483de479211805ef709c10856d5a5895b169524c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x27 : Ex t110 3 [v24,u3,u1,u2] :=
  certify c110 [] (unpack 4 0x58906850383058a0385068c070605830386 24 0x617664681714606540431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x28 : Ex t110 4 [v25,u3,u1,u2,u0] :=
  certify c110 [⟨_,p110x27⟩] (unpack 4 0x68c058a80004000038603830589068505830385070a070c0706 31 0x787b383c4b488a98745773764543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x29 : Ex t110 4 [v26,u3,u1,u2,u0] :=
  certify c110 [] (unpack 4 0x68c0706058a038606890383058903850583 37 0x3536151857653473313212716565434321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x30 : Ex t110 3 [v21,v15,v12,u0] :=
  certify c110 [] (unpack 3 0x58a068c038640030383068540010583 24 0x75f1c559562368b088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x31 : Ex t110 4 [v15,u3,v12,u2,u0] :=
  certify c110 [⟨_,p110x30⟩] (unpack 4 0x58a0386800003830685400203850689400305890583 34 0x399a494a6a699a19636874654412413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x32 : Ex t110 4 [v21,u3,v12,u1,u0] :=
  certify c110 [⟨_,p110x30⟩] (unpack 4 0x58a068c0386800005890385058340020689400103830685 34 0x799a191b5b599a39575873276154113210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x33 : Ex t110 4 [v27,u0,u1,u2,u3] :=
  certify c110 [] (unpack 4 0x6850386058307060689070a03830589070c0385058a 37 0xa8a88a8a36538789699539928787654432110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x34 : Ex t110 5 [v12,u1,u2,u0,u3] :=
  certify c110 [⟨_,p110x28⟩,⟨_,p110x29⟩,⟨_,p110x31⟩,⟨_,p110x32⟩,⟨_,p110x1⟩,⟨_,p110x33⟩,⟨_,p110x10⟩,⟨_,p110x20⟩] (unpack 5 0x80078006068c8005400003868004058a80038002068505890689800140020706800005830383400340010385 99 0x1204338c4710d0825c914209842ae72a6a0c20a842939c5ce94211841ee72c4b2248b4ac8d210245a9645116c5854a48921084c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x35 : Ex t110 4 [v28,u2,u1,u3,u0] :=
  certify c110 [] (unpack 3 0x68c0386058a06850583038505890383 37 0x3af2cbddab8d148c71ebac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x36 : Ex t110 4 [v29,u0,u1,u3,u2] :=
  certify c110 [] (unpack 4 0x689058a0383070a068507060583070c038505890386 37 0x8a68828a26528789656529238787654423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x37 : Ex t110 4 [v21,u2,v15,u1,u0] :=
  certify c110 [⟨_,p110x30⟩] (unpack 4 0x58a068c0386800003850589400303830685400105830689 34 0x797a1b19494b3a39474873276145413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x38 : Ex t110 5 [v15,u1,u3,u0,u2] :=
  certify c110 [⟨_,p110x28⟩,⟨_,p110x35⟩,⟨_,p110x31⟩,⟨_,p110x4⟩,⟨_,p110x36⟩,⟨_,p110x11⟩,⟨_,p110x24⟩,⟨_,p110x37⟩] (unpack 5 0x800780068005068c80044000058a80030386800206890385068580014003070a800003830583400240010589 99 0x248412d695a6a4211e4335a4690cf7a5a913de97a68d6aa4a0b5aa6aa72941ad8bdf07bdcd690245a9445116c5854a48921084c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x39 : Ex t110 4 [v30,u0,u2,u3,u1] :=
  certify c110 [] (unpack 4 0x589068c0385070c070605830685070a038306890386 37 0x5a58282a25628789565623238787565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x40 : Ex t110 4 [v31,u1,u2,u3,u0] :=
  certify c110 [] (unpack 3 0x58a0386068c05830685038306890385 37 0x4f32cbddaa8d471a28ebac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x41 : Ex t110 5 [v21,u2,u3,u0,u1] :=
  certify c110 [⟨_,p110x15⟩,⟨_,p110x39⟩,⟨_,p110x19⟩,⟨_,p110x25⟩,⟨_,p110x28⟩,⟨_,p110x40⟩,⟨_,p110x32⟩,⟨_,p110x37⟩] (unpack 5 0x8007800605898005400180040385070c80038002058a80014000068c80000386038305830685400240030689 99 0x11e414e64992af796650bde5796939c5ef939d173a0f7bd0f718cf33dc8410c412d64591a631565098c53158b5a4c652109420e6304a5208810842118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p110x42 : Ex t110 6 (roots 15) :=
  certify c110 [⟨_,p110x12⟩,⟨_,p110x21⟩,⟨_,p110x26⟩,⟨_,p110x34⟩,⟨_,p110x38⟩,⟨_,p110x41⟩] (unpack 5 0x8005800406858003068905894002058380020706400303838001070a058a40014000038603858000070c068c 96 0x5cd4a7ba2e5ce33ab94a3386e7ce1333a0ea4c6332a0a5c4633286a946102b88e7b0ec2b8ee6b0842a8ea5a0842a88a4a0e728c033048428c8310400) (by decide +kernel)
theorem l110 : CClaim 15 t110 7 := fromTable 6341254 (by decide +kernel) p110x42

abbrev t112 : Sig := 0xfee8fee8fee8fee8fee8fee8fee8fee8
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c112 : Cuts t112 := [
  rule t112 0 l45 none (by decide +kernel),
  rule t112 0 l40 none (by decide +kernel),
  rule t112 0 l37 none (by decide +kernel),
  rule t112 0 l50 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x0 : Ex t112 3 [v32,u2,u0,u1] :=
  certify c112 [] (unpack 3 0x2840302018101820502060402810481 24 0xa75b2f38cae8803288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x1 : Ex t112 4 [v33,u2,u0,u1,u3] :=
  certify c112 [⟨_,p112x0⟩] (unpack 4 0x508050201810284030201820488060402810608800004814002 31 0xa1baa48ac1b17a7a948476415431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x2 : Ex t112 4 [v34,u2,u0,u1,u3] :=
  certify c112 [] (unpack 3 0x5020481060401810304018202840281 37 0x4de46e6f9450a255d76bac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x3 : Ex t112 3 [v35,u3,u0,u1] :=
  certify c112 [] (unpack 3 0x2840502018101820302060404810281 24 0xa75b2f38cae8803088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x4 : Ex t112 4 [v36,u3,u0,u1,u2] :=
  certify c112 [⟨_,p112x3⟩] (unpack 4 0x608800040010304030202810181048805020481018202840604 31 0x73c7b77a67866346978726265343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x5 : Ex t112 4 [v37,u3,u0,u1,u2] :=
  certify c112 [] (unpack 4 0x3020604028106080304018105080284018204880481 37 0x879858a559458a82525129128787565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x6 : Ex t112 3 [v38,v39,v40,u3] :=
  certify c112 [] (unpack 3 0x6040284400101824000048105020181 24 0x5d69a5185454103088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x7 : Ex t112 4 [v39,u2,v40,u1,u3] :=
  certify c112 [⟨_,p112x6⟩] (unpack 4 0x30480000181400002844001060402810302050204810182 34 0x9129b94a90998151747460706415431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x8 : Ex t112 3 [v41,v42,v40,u2] :=
  certify c112 [] (unpack 4 0x302060802810488028403044002018201814000 24 0x977271917876252314131210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x9 : Ex t112 4 [v42,u3,v40,u1,u2] :=
  certify c112 [⟨_,p112x8⟩] (unpack 4 0x302030480000181400006080281048804810284018240020502 34 0x6476c66296c9b94a929986765454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x10 : Ex t112 4 [v38,u2,v40,u0,u3] :=
  certify c112 [⟨_,p112x6⟩] (unpack 4 0x28480000182400303044001030206040281048105020181 34 0x2129b95a90908242757560706524230210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x11 : Ex t112 4 [v41,u3,v40,u0,u2] :=
  certify c112 [⟨_,p112x8⟩] (unpack 4 0x302028480000182400306080281050805020304018140020481 34 0x647662c26c69b94a929286765454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x12 : Ex t112 5 [v40,u0,u1,u2,u3] :=
  certify c112 [⟨_,p112x1⟩,⟨_,p112x2⟩,⟨_,p112x4⟩,⟨_,p112x5⟩,⟨_,p112x7⟩,⟨_,p112x9⟩,⟨_,p112x10⟩,⟨_,p112x11⟩] (unpack 5 0x8007800603048005050280040302018140030182400002848003800204814002060480018000028140010608 99 0x1442380e5014e2145ce3acf1ac4ee73dce12c4fa3c4e72db33b0f16c4f23c58c1304f6bc5013d8c72dcd6316b5ad6a398e5494e8394c5104402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x13 : Ex t112 3 [v43,u3,u0,u2] :=
  certify c112 [] (unpack 3 0x6040302028102840182050204810181 24 0xa7dbab28b1a8803088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x14 : Ex t112 4 [v44,u3,u0,u2,u1] :=
  certify c112 [⟨_,p112x13⟩] (unpack 4 0x508800040000302030401810281048806040481028401820502 31 0x768773c7b77a6346978726265343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x15 : Ex t112 4 [v45,u3,u0,u2,u1] :=
  certify c112 [] (unpack 4 0x3040502018105080302028106080182028404880481 37 0x85a8879859458a82525129198787565433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x16 : Ex t112 3 [v46,v42,v39,u1] :=
  certify c112 [] (unpack 4 0x5080488030401810182028403024002050202814001 24 0xa77987757187665314131210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x17 : Ex t112 4 [v42,u3,v39,u2,u1] :=
  certify c112 [⟨_,p112x16⟩] (unpack 4 0x508030401810302800002814001048804810182028440020502 34 0xa7bacaa5a4cabaa2974872776454133210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x18 : Ex t112 4 [v46,u3,v39,u0,u1] :=
  certify c112 [⟨_,p112x16⟩] (unpack 4 0x508030401810182800002844003060806040302028140020481 34 0xcaaca4caa2baaba7974872726454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x19 : Ex t112 4 [v47,u1,u0,u2,u3] :=
  certify c112 [] (unpack 3 0x6040481050202810302028401820181 37 0x4de6b8c70a255d738e6bac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x20 : Ex t112 4 [v38,u1,v39,u0,u3] :=
  certify c112 [⟨_,p112x6⟩] (unpack 4 0x1828000028440030304030240000181048105020281 34 0x2121a86980807212505041212565430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x21 : Ex t112 5 [v39,u0,u2,u1,u3] :=
  certify c112 [⟨_,p112x14⟩,⟨_,p112x15⟩,⟨_,p112x7⟩,⟨_,p112x17⟩,⟨_,p112x18⟩,⟨_,p112x1⟩,⟨_,p112x19⟩,⟨_,p112x20⟩] (unpack 5 0x8007800680054000050880040604030280038002018103040281400302844001018280018000048140020502 99 0x16b144408804b5996b4a9355292b5d23192d735ae518bd291184f83c494990e11c404004d100e059d6a4296c5a8e74992839cc6318c5104402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x22 : Ex t112 4 [v48,u1,u0,u3,u2] :=
  certify c112 [] (unpack 4 0x608030402810302048105020284048801820181 37 0x7597767154512118676745457676545431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x23 : Ex t112 4 [v41,u1,v42,u0,u2] :=
  certify c112 [⟨_,p112x8⟩] (unpack 4 0x1828000048840030481030202810508050240000181 34 0x544546544545a839868676261545423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x24 : Ex t112 4 [v49,u2,u0,u3,u1] :=
  certify c112 [] (unpack 4 0x5080302018103040502048106040182048802840281 37 0x85a8879887815451291995458787565433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x25 : Ex t112 4 [v46,u2,v42,u0,u1] :=
  certify c112 [⟨_,p112x16⟩] (unpack 4 0x18103040182800004884003050204810608060440010281 34 0xabbabaabb4abbaba973874746454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x26 : Ex t112 5 [v42,u0,u3,u1,u2] :=
  certify c112 [⟨_,p112x9⟩,⟨_,p112x17⟩,⟨_,p112x4⟩,⟨_,p112x22⟩,⟨_,p112x23⟩,⟨_,p112x14⟩,⟨_,p112x24⟩,⟨_,p112x25⟩] (unpack 5 0x8007060880068005400180040508800380024000050280010281030280000181030404814003048840020182 99 0x52925095a50894cd088a5324a628420c6495282a126304c623c907bc86338a5618cd319852846b489281a12a4a048308c5194c731445204831082108420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x27 : Ex t112 3 [v50,u3,u1,u2] :=
  certify c112 [] (unpack 3 0x6040302028102840181018205020481 24 0xa3d77360b5758d3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x28 : Ex t112 4 [v51,u3,u1,u2,u0] :=
  certify c112 [⟨_,p112x27⟩] (unpack 4 0x284048880000182400302810302050806040502030401810481 31 0x96c9c99c93b9a998634676265343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x29 : Ex t112 4 [v52,u3,u1,u2,u0] :=
  certify c112 [] (unpack 4 0x2840481018204880281030206080181030405080502 37 0x85a8a88a97985949525129198787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x30 : Ex t112 3 [v46,v41,v38,u0] :=
  certify c112 [] (unpack 4 0x488028401820181030402814002048103024001 24 0x977987787187665344132210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x31 : Ex t112 4 [v41,u3,v38,u2,u0] :=
  certify c112 [⟨_,p112x30⟩] (unpack 4 0x488018202840281800003024001050805020181030440020481 34 0xb7abcbbcb4cbabba974872776454133210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x32 : Ex t112 4 [v46,u3,v38,u1,u0] :=
  certify c112 [⟨_,p112x30⟩] (unpack 4 0x488028401820181800003044000060806040281030240020481 34 0xbaabcaaca4caa2ba974872726454133210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x33 : Ex t112 4 [v53,u0,u1,u2,u3] :=
  certify c112 [] (unpack 3 0x6040502048103020281030401810182 37 0x3bd9b8970dd738e1456bac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x34 : Ex t112 5 [v38,u1,u2,u0,u3] :=
  certify c112 [⟨_,p112x28⟩,⟨_,p112x29⟩,⟨_,p112x31⟩,⟨_,p112x32⟩,⟨_,p112x1⟩,⟨_,p112x33⟩,⟨_,p112x10⟩,⟨_,p112x20⟩] (unpack 5 0x8007800602848005800401824003048880030604028180020302400003044001018180018000050240020481 99 0x200138407005081a104cd359cd30822733c214840f39c9ce7c211841ee731290180c6b0090190b11c404004a100e04992839cc6318c5104402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x35 : Ex t112 4 [v54,u0,u1,u3,u2] :=
  certify c112 [] (unpack 4 0x608028403020281050204810304050801810182 37 0x6496167114516767454512187676545431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x36 : Ex t112 4 [v55,u2,u1,u3,u0] :=
  certify c112 [] (unpack 4 0x4880281018202840481050206040181050803040302 37 0x85a8788797985451291995498787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x37 : Ex t112 4 [v46,u2,v41,u1,u0] :=
  certify c112 [⟨_,p112x30⟩] (unpack 4 0x28401820181800005084000048105020608060440010281 34 0xbaabbaababbaa4ba973874746554123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x38 : Ex t112 5 [v41,u1,u3,u0,u2] :=
  certify c112 [⟨_,p112x31⟩,⟨_,p112x4⟩,⟨_,p112x35⟩,⟨_,p112x11⟩,⟨_,p112x23⟩,⟨_,p112x28⟩,⟨_,p112x36⟩,⟨_,p112x37⟩] (unpack 5 0x8007060880068005400180040488800380028001018240030284048180000302028105024000050840020181 99 0x4a525095a50852cca5898d231a2529565324c5494cb5856b23c907bc8b58d2912d6e5ac494b52952d6c5ad4948468308c5194c731445204831082108420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x39 : Ex t112 4 [v56,u0,u2,u3,u1] :=
  certify c112 [] (unpack 4 0x5080182030401810502060404810302060802810284 37 0x74a7718714517978454912198787645431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x40 : Ex t112 4 [v57,u1,u2,u3,u0] :=
  certify c112 [] (unpack 4 0x4880181028401820481060405020281060803020304 37 0x74a7718797981451954992198787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x41 : Ex t112 5 [v46,u2,u3,u0,u1] :=
  certify c112 [⟨_,p112x14⟩,⟨_,p112x39⟩,⟨_,p112x18⟩,⟨_,p112x25⟩,⟨_,p112x28⟩,⟨_,p112x40⟩,⟨_,p112x32⟩,⟨_,p112x37⟩] (unpack 5 0x8007050880068005800440000181030480030488800280018000028440030182048106044001060840020281 99 0x5ef25095a508f78def139d37384f7c9ef839d173a0f7bd0f718cf33dc8404c62308d6308630cc61210b42046328c63a109420e630465204831082108420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p112x42 : Ex t112 6 (roots 15) :=
  certify c112 [⟨_,p112x12⟩,⟨_,p112x21⟩,⟨_,p112x26⟩,⟨_,p112x34⟩,⟨_,p112x38⟩,⟨_,p112x41⟩] (unpack 5 0x8005060806048004050880038002048804814002050280010281400103024003800001820181400003040284 96 0x64d294368dace936352962c631362d92e2b6346341c631242981c27424636348d32dcb7b5cd62c844248931c075240941c8410c033048428c8310400) (by decide +kernel)
theorem l112 : CClaim 15 t112 7 := fromTable 2113666 (by decide +kernel) p112x42

abbrev t113 : Sig := 0xfefee8e8fefee8e8fefee8e8fefee8e8
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c113 : Cuts t113 := [
  rule t113 0 l57 none (by decide +kernel),
  rule t113 0 l54 none (by decide +kernel),
  rule t113 0 l37 none (by decide +kernel),
  rule t113 0 l60 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x0 : Ex t113 3 [v58,u2,u0,u1] :=
  certify c113 [] (unpack 3 0x28403020181018209020a0402810881 24 0xa75b2f38cae8803288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x1 : Ex t113 4 [v33,u2,u0,u1,u4] :=
  certify c113 [⟨_,p113x0⟩] (unpack 4 0x9100902018102840302018208900a0402810a10800008814002 31 0xa1baa48ac1b17a7a948476415431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x2 : Ex t113 4 [v34,u2,u0,u1,u4] :=
  certify c113 [] (unpack 3 0x90208810a0401810304018202840281 37 0x4de46e6f9450a255d76bac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x3 : Ex t113 3 [v59,u4,u0,u1] :=
  certify c113 [] (unpack 3 0x28409020181018203020a0408810281 24 0xa75b2f38cae8803088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x4 : Ex t113 4 [v60,u4,u0,u1,u2] :=
  certify c113 [⟨_,p113x3⟩] (unpack 4 0xa10800040010304030202810181089009020881018202840a04 31 0x73c7b77a67866346978726265343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x5 : Ex t113 4 [v61,u4,u0,u1,u2] :=
  certify c113 [] (unpack 4 0x3020a0402810a100304018109100284018208900881 37 0x879858a559458a82525129128787565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x6 : Ex t113 3 [v38,v39,v40,u4] :=
  certify c113 [] (unpack 3 0xa040284400101824000088109020181 24 0x5d69a5185454103088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x7 : Ex t113 4 [v39,u2,v40,u1,u4] :=
  certify c113 [⟨_,p113x6⟩] (unpack 4 0x304800001814000028440010a0402810302090208810182 34 0x9129b94a90998151747460706415431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x8 : Ex t113 3 [v62,v63,v40,u2] :=
  certify c113 [] (unpack 4 0x3020a1002810890028403044002018201814000 24 0x977271917876252314131210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x9 : Ex t113 4 [v63,u4,v40,u1,u2] :=
  certify c113 [⟨_,p113x8⟩] (unpack 4 0x30203048000018140000a100281089008810284018240020902 34 0x6476c66296c9b94a929986765454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x10 : Ex t113 4 [v38,u2,v40,u0,u4] :=
  certify c113 [⟨_,p113x6⟩] (unpack 4 0x2848000018240030304400103020a040281088109020181 34 0x2129b95a90908242757560706524230210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x11 : Ex t113 4 [v62,u4,v40,u0,u2] :=
  certify c113 [⟨_,p113x8⟩] (unpack 4 0x30202848000018240030a100281091009020304018140020881 34 0x647662c26c69b94a929286765454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x12 : Ex t113 5 [v40,u0,u1,u2,u4] :=
  certify c113 [⟨_,p113x1⟩,⟨_,p113x2⟩,⟨_,p113x4⟩,⟨_,p113x5⟩,⟨_,p113x7⟩,⟨_,p113x9⟩,⟨_,p113x10⟩,⟨_,p113x11⟩] (unpack 5 0x80078006030480050902800403020181400301824000028480038002088140020a0480018000028140010a10 99 0x1442380e5014e2145ce3acf1ac4ee73dce12c4fa3c4e72db33b0f16c4f23c58c1304f6bc5013d8c72dcd6316b5ad6a398e5494e8394c5104402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x13 : Ex t113 3 [v64,u4,u0,u2] :=
  certify c113 [] (unpack 3 0xa040302028102840182090208810181 24 0xa7dbab28b1a8803088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x14 : Ex t113 4 [v65,u4,u0,u2,u1] :=
  certify c113 [⟨_,p113x13⟩] (unpack 4 0x91080004000030203040181028108900a040881028401820902 31 0x768773c7b77a6346978726265343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x15 : Ex t113 4 [v66,u4,u0,u2,u1] :=
  certify c113 [] (unpack 4 0x304090201810910030202810a100182028408900881 37 0x85a8879859458a82525129198787565433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x16 : Ex t113 3 [v67,v63,v39,u1] :=
  certify c113 [] (unpack 4 0x9100890030401810182028403024002090202814001 24 0xa77987757187665314131210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x17 : Ex t113 4 [v63,u4,v39,u2,u1] :=
  certify c113 [⟨_,p113x16⟩] (unpack 4 0x910030401810302800002814001089008810182028440020902 34 0xa7bacaa5a4cabaa2974872776454133210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x18 : Ex t113 4 [v67,u4,v39,u0,u1] :=
  certify c113 [⟨_,p113x16⟩] (unpack 4 0x9100304018101828000028440030a100a040302028140020881 34 0xcaaca4caa2baaba7974872726454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x19 : Ex t113 4 [v47,u1,u0,u2,u4] :=
  certify c113 [] (unpack 3 0xa040881090202810302028401820181 37 0x4de6b8c70a255d738e6bac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x20 : Ex t113 4 [v38,u1,v39,u0,u4] :=
  certify c113 [⟨_,p113x6⟩] (unpack 4 0x1828000028440030304030240000181088109020281 34 0x2121a86980807212505041212565430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x21 : Ex t113 5 [v39,u0,u2,u1,u4] :=
  certify c113 [⟨_,p113x14⟩,⟨_,p113x15⟩,⟨_,p113x7⟩,⟨_,p113x17⟩,⟨_,p113x18⟩,⟨_,p113x1⟩,⟨_,p113x19⟩,⟨_,p113x20⟩] (unpack 5 0x8007800680054000091080040a04030280038002018103040281400302844001018280018000088140020902 99 0x16b144408804b5996b4a9355292b5d23192d735ae518bd291184f83c494990e11c404004d100e059d6a4296c5a8e74992839cc6318c5104402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x22 : Ex t113 4 [v68,u1,u0,u4,u2] :=
  certify c113 [] (unpack 4 0xa10030402810302088109020284089001820181 37 0x7597767154512118676745457676545431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x23 : Ex t113 4 [v62,u1,v63,u0,u2] :=
  certify c113 [⟨_,p113x8⟩] (unpack 4 0x1828000089040030881030202810910090240000181 34 0x544546544545a839868676261545423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x24 : Ex t113 4 [v69,u2,u0,u4,u1] :=
  certify c113 [] (unpack 4 0x910030201810304090208810a040182089002840281 37 0x85a8879887815451291995458787565433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x25 : Ex t113 4 [v67,u2,v63,u0,u1] :=
  certify c113 [⟨_,p113x16⟩] (unpack 4 0x18103040182800008904003090208810a100a0440010281 34 0xabbabaabb4abbaba973874746454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x26 : Ex t113 5 [v63,u0,u4,u1,u2] :=
  certify c113 [⟨_,p113x9⟩,⟨_,p113x17⟩,⟨_,p113x4⟩,⟨_,p113x22⟩,⟨_,p113x23⟩,⟨_,p113x14⟩,⟨_,p113x24⟩,⟨_,p113x25⟩] (unpack 5 0x80070a1080068005400180040910800380024000090280010281030280000181030408814003089040020182 99 0x52925095a50894cd088a5324a628420c6495282a126304c623c907bc86338a5618cd319852846b489281a12a4a048308c5194c731445204831082108420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x27 : Ex t113 3 [v70,u4,u1,u2] :=
  certify c113 [] (unpack 3 0xa040302028102840181018209020881 24 0xa3d77360b5758d3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x28 : Ex t113 4 [v71,u4,u1,u2,u0] :=
  certify c113 [⟨_,p113x27⟩] (unpack 4 0x28408908000018240030281030209100a040902030401810881 31 0x96c9c99c93b9a998634676265343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x29 : Ex t113 4 [v72,u4,u1,u2,u0] :=
  certify c113 [] (unpack 4 0x284088101820890028103020a100181030409100902 37 0x85a8a88a97985949525129198787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x30 : Ex t113 3 [v67,v62,v38,u0] :=
  certify c113 [] (unpack 4 0x890028401820181030402814002088103024001 24 0x977987787187665344132210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x31 : Ex t113 4 [v62,u4,v38,u2,u0] :=
  certify c113 [⟨_,p113x30⟩] (unpack 4 0x890018202840281800003024001091009020181030440020881 34 0xb7abcbbcb4cbabba974872776454133210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x32 : Ex t113 4 [v67,u4,v38,u1,u0] :=
  certify c113 [⟨_,p113x30⟩] (unpack 4 0x8900284018201818000030440000a100a040281030240020881 34 0xbaabcaaca4caa2ba974872726454133210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x33 : Ex t113 4 [v53,u0,u1,u2,u4] :=
  certify c113 [] (unpack 3 0xa040902088103020281030401810182 37 0x3bd9b8970dd738e1456bac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x34 : Ex t113 5 [v38,u1,u2,u0,u4] :=
  certify c113 [⟨_,p113x28⟩,⟨_,p113x29⟩,⟨_,p113x31⟩,⟨_,p113x32⟩,⟨_,p113x1⟩,⟨_,p113x33⟩,⟨_,p113x10⟩,⟨_,p113x20⟩] (unpack 5 0x8007800602848005800401824003089080030a04028180020302400003044001018180018000090240020881 99 0x200138407005081a104cd359cd30822733c214840f39c9ce7c211841ee731290180c6b0090190b11c404004a100e04992839cc6318c5104402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x35 : Ex t113 4 [v73,u0,u1,u4,u2] :=
  certify c113 [] (unpack 4 0xa10028403020281090208810304091001810182 37 0x6496167114516767454512187676545431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x36 : Ex t113 4 [v74,u2,u1,u4,u0] :=
  certify c113 [] (unpack 4 0x890028101820284088109020a040181091003040302 37 0x85a8788797985451291995498787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x37 : Ex t113 4 [v67,u2,v62,u1,u0] :=
  certify c113 [⟨_,p113x30⟩] (unpack 4 0x28401820181800009104000088109020a100a0440010281 34 0xbaabbaababbaa4ba973874746554123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x38 : Ex t113 5 [v62,u1,u4,u0,u2] :=
  certify c113 [⟨_,p113x31⟩,⟨_,p113x4⟩,⟨_,p113x35⟩,⟨_,p113x11⟩,⟨_,p113x23⟩,⟨_,p113x28⟩,⟨_,p113x36⟩,⟨_,p113x37⟩] (unpack 5 0x80070a1080068005400180040890800380028001018240030284088180000302028109024000091040020181 99 0x4a525095a50852cca5898d231a2529565324c5494cb5856b23c907bc8b58d2912d6e5ac494b52952d6c5ad4948468308c5194c731445204831082108420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x39 : Ex t113 4 [v75,u0,u2,u4,u1] :=
  certify c113 [] (unpack 4 0x91001820304018109020a04088103020a1002810284 37 0x74a7718714517978454912198787645431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x40 : Ex t113 4 [v76,u1,u2,u4,u0] :=
  certify c113 [] (unpack 4 0x89001810284018208810a04090202810a1003020304 37 0x74a7718797981451954992198787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x41 : Ex t113 5 [v67,u2,u4,u0,u1] :=
  certify c113 [⟨_,p113x14⟩,⟨_,p113x39⟩,⟨_,p113x18⟩,⟨_,p113x25⟩,⟨_,p113x28⟩,⟨_,p113x40⟩,⟨_,p113x32⟩,⟨_,p113x37⟩] (unpack 5 0x800709108006800580044000018103048003089080028001800002844003018208810a0440010a1040020281 99 0x5ef25095a508f78def139d37384f7c9ef839d173a0f7bd0f718cf33dc8404c62308d6308630cc61210b42046328c63a109420e630465204831082108420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p113x42 : Ex t113 6 (roots 23) :=
  certify c113 [⟨_,p113x12⟩,⟨_,p113x21⟩,⟨_,p113x26⟩,⟨_,p113x34⟩,⟨_,p113x38⟩,⟨_,p113x41⟩] (unpack 5 0x80050a100a048004091080038002089008814002090280010281400103024003800001820181400003040284 96 0x64d294368dace936352962c631362d92e2b6346341c631242981c27424636348d32dcb7b5cd62c844248931c075240941c8410c033048428c8310400) (by decide +kernel)
theorem l113 : CClaim 23 t113 7 := fromTable 268451970 (by decide +kernel) p113x42

abbrev t114 : Sig := 0xe8e88080e8e88080e8e88080e8e88080
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c114 : Cuts t114 := [
  rule t114 1 l60 none (by decide +kernel),
  rule t114 2 l57 none (by decide +kernel),
  rule t114 16 l37 none (by decide +kernel),
  rule t114 4 l54 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x0 : Ex t114 3 [v77,u2,u0,u1] :=
  certify c114 [] (unpack 4 0x9910a94099203850b06038609830a850383 24 0x50853570306122542232010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x1 : Ex t114 4 [v7,u2,u0,u1,u4] :=
  certify c114 [⟨_,p114x0⟩] (unpack 4 0xb0609910a940b120a9109920a85800040020983038503860383 31 0x3636b89b3c3cb7ba898763635343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x2 : Ex t114 4 [v8,u2,u0,u1,u4] :=
  certify c114 [] (unpack 4 0xb0603830a8509830b14099103850a94099203860a91 37 0x787896957a7a5253939297898787654432110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x3 : Ex t114 3 [v78,u4,u0,u1] :=
  certify c114 [] (unpack 4 0xa940b06038509910386099209830a850383 24 0x212664682724600540030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x4 : Ex t114 4 [v79,u4,u0,u1,u2] :=
  certify c114 [⟨_,p114x3⟩] (unpack 4 0xa910b1203850a940b060a850386800040030383099109920983 31 0x3c733a3ca78a363ba6a978765343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x5 : Ex t114 4 [v80,u4,u0,u1,u2] :=
  certify c114 [] (unpack 4 0xb1209830a9103830b14099103850a94099203860a85 37 0x798774789694717a414393918787645431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x6 : Ex t114 3 [v12,v13,v14,u4] :=
  certify c114 [] (unpack 4 0x3864001038509910a85038340000a910b060983 24 0x50599867736505044321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x7 : Ex t114 4 [v13,u2,v14,u1,u4] :=
  certify c114 [⟨_,p114x6⟩] (unpack 4 0x800003850b124003038609920a8509830b1440010a940383 34 0x4545939b4545a698677265454545413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x8 : Ex t114 3 [v81,v82,v14,u2] :=
  certify c114 [] (unpack 4 0x400103850a91098340000a850b120b060383 24 0x70673877147603055432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x9 : Ex t114 4 [v82,u4,v14,u1,u2] :=
  certify c114 [⟨_,p114x8⟩] (unpack 4 0x800003850b064002099203860a9103830b1440010a940983 34 0x45944545939b4645a69866726545413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x10 : Ex t114 4 [v12,u2,v14,u0,u4] :=
  certify c114 [⟨_,p114x6⟩] (unpack 4 0x80000b140a9403860a9140030385400009910a850b0609830383 34 0x12128a8cab5a1313948746654313121210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x11 : Ex t114 4 [v81,u4,v14,u0,u2] :=
  certify c114 [⟨_,p114x8⟩] (unpack 4 0x80000b140a940a9103860a8540020991400003850b1203830983 34 0x197112127a7cab4a131983763354321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x12 : Ex t114 5 [v14,u0,u1,u2,u4] :=
  certify c114 [⟨_,p114x1⟩,⟨_,p114x2⟩,⟨_,p114x4⟩,⟨_,p114x5⟩,⟨_,p114x7⟩,⟨_,p114x9⟩,⟨_,p114x10⟩,⟨_,p114x11⟩] (unpack 5 0x8007800680050b0680040b120a940b1480034002098380020a8580014003038380000a910385400140000386 99 0x24c6591692256632c4b4b92b72d3549846238867189422c2b93e4b7ae539182683e0679a11805ef709c10856d5a5895b169524c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x13 : Ex t114 4 [v17,u1,u0,u2,u4] :=
  certify c114 [] (unpack 4 0xb06038509830a850b120a91038309920a9403860991 37 0x78788a8a56539392878969958787654432110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x14 : Ex t114 3 [v83,u4,u0,u2] :=
  certify c114 [] (unpack 4 0x9920b060383099103860a940a8509830385 24 0x612664681714606540031210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x15 : Ex t114 4 [v84,u4,u0,u2,u1] :=
  certify c114 [⟨_,p114x14⟩] (unpack 4 0x9910b14038309920b06098303868000400103850a910a940a85 31 0xa3ac7c73a78a363ba6a978765343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x16 : Ex t114 4 [v85,u4,u0,u2,u1] :=
  certify c114 [] (unpack 4 0xb140a85099103850b120a910383099203860983 37 0x3637687635836169313282817676534321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x17 : Ex t114 3 [v86,v82,v13,u1] :=
  certify c114 [] (unpack 4 0xb1440030b060383099103850a8540000983 24 0x386335545075561540030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x18 : Ex t114 4 [v82,u4,v13,u2,u1] :=
  certify c114 [⟨_,p114x17⟩] (unpack 4 0x800003830b0640020386099103850b12400309920983 34 0x54454584838a4645968766126545413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x19 : Ex t114 4 [v86,u4,v13,u0,u1] :=
  certify c114 [⟨_,p114x17⟩] (unpack 4 0xb1480000b120992038509910386098340020a91400003830a85 34 0x57588ca8898c595b9a2981176154113210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x20 : Ex t114 4 [v12,u1,v13,u0,u4] :=
  certify c114 [⟨_,p114x6⟩] (unpack 4 0x80000b120992038640010991038340000a910a850b0609830385 34 0x12127a7cab5a3131947876654131321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x21 : Ex t114 5 [v13,u0,u2,u1,u4] :=
  certify c114 [⟨_,p114x1⟩,⟨_,p114x13⟩,⟨_,p114x15⟩,⟨_,p114x16⟩,⟨_,p114x7⟩,⟨_,p114x18⟩,⟨_,p114x19⟩,⟨_,p114x20⟩] (unpack 5 0x8007800680050b0680040b1409920b12800340020a8580020983800140010385800009910383400340000386 99 0x24c9591692256633884118ce31aa422c4b4b92b72d344a42993e497a6539182683de679a11805ef709c10856d5a5895b169524c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x22 : Ex t114 4 [v87,u1,u0,u4,u2] :=
  certify c114 [] (unpack 4 0xb12099103830a910b060a8509830a94038609920385 37 0x8758828a56529223878965658787654423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x23 : Ex t114 4 [v88,u2,u0,u4,u1] :=
  certify c114 [] (unpack 4 0xb140a91038509910b060a850983038609920383 37 0x3637677672793532822153537676534321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x24 : Ex t114 4 [v81,u1,v82,u0,u2] :=
  certify c114 [⟨_,p114x8⟩] (unpack 4 0x8000038609924001098340000a8503850a910b120b0603830991 34 0x1b135b5cb27b4161a65958876151431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x25 : Ex t114 4 [v86,u2,v82,u0,u1] :=
  certify c114 [⟨_,p114x17⟩] (unpack 4 0xb1480000b060386099103850992400303830a85400009830a91 34 0x47487ca7797c494b9a2981176145413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x26 : Ex t114 5 [v82,u0,u4,u1,u2] :=
  certify c114 [⟨_,p114x4⟩,⟨_,p114x22⟩,⟨_,p114x15⟩,⟨_,p114x23⟩,⟨_,p114x9⟩,⟨_,p114x18⟩,⟨_,p114x24⟩,⟨_,p114x25⟩] (unpack 5 0x8007800680050b1280040b1403860b06800340030a9180020383800140010991800003850983400240000992 99 0x392912d6e5baa94a4c9590892256633884118ce33a842242993de97a6539102483de479211805ef709c10856d5a5895b169524c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x27 : Ex t114 3 [v89,u4,u1,u2] :=
  certify c114 [] (unpack 4 0x9910a850383099203850a940b0609830386 24 0x617664681714606540431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x28 : Ex t114 4 [v90,u4,u1,u2,u0] :=
  certify c114 [⟨_,p114x27⟩] (unpack 4 0xa940992800040000386038309910a85098303850b120b140b06 31 0x787b383c4b488a98745773764543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x29 : Ex t114 4 [v91,u4,u1,u2,u0] :=
  certify c114 [] (unpack 4 0xa940b06099203860a910383099103850983 37 0x3536151857653473313212716565434321210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x30 : Ex t114 3 [v86,v81,v12,u0] :=
  certify c114 [] (unpack 3 0x9920a940386400303830a8540010983 24 0x75f1c559562368b088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x31 : Ex t114 4 [v81,u4,v12,u2,u0] :=
  certify c114 [⟨_,p114x30⟩] (unpack 4 0x9920386800003830a85400203850a91400309910983 34 0x399a494a6a699a19636874654412413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x32 : Ex t114 4 [v86,u4,v12,u1,u0] :=
  certify c114 [⟨_,p114x30⟩] (unpack 4 0x9920a940386800009910385098340020a91400103830a85 34 0x799a191b5b599a39575873276154113210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x33 : Ex t114 4 [v27,u0,u1,u2,u4] :=
  certify c114 [] (unpack 4 0xa85038609830b060a910b12038309910b1403850992 37 0xa8a88a8a36538789699539928787654432110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x34 : Ex t114 5 [v12,u1,u2,u0,u4] :=
  certify c114 [⟨_,p114x28⟩,⟨_,p114x29⟩,⟨_,p114x31⟩,⟨_,p114x32⟩,⟨_,p114x1⟩,⟨_,p114x33⟩,⟨_,p114x10⟩,⟨_,p114x20⟩] (unpack 5 0x800780060a9480054000038680040992800380020a8509910a91800140020b06800009830383400340010385 99 0x1204338c4710d0825c914209842ae72a6a0c20a842939c5ce94211841ee72c4b2248b4ac8d210245a9645116c5854a48921084c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x35 : Ex t114 4 [v92,u2,u1,u4,u0] :=
  certify c114 [] (unpack 3 0xa94038609920a850983038509910383 37 0x3af2cbddab8d148c71ebac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x36 : Ex t114 4 [v93,u0,u1,u4,u2] :=
  certify c114 [] (unpack 4 0xa91099203830b120a850b0609830b14038509910386 37 0x8a68828a26528789656529238787654423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x37 : Ex t114 4 [v86,u2,v81,u1,u0] :=
  certify c114 [⟨_,p114x30⟩] (unpack 4 0x9920a940386800003850991400303830a85400109830a91 34 0x797a1b19494b3a39474873276145413210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x38 : Ex t114 5 [v81,u1,u4,u0,u2] :=
  certify c114 [⟨_,p114x28⟩,⟨_,p114x35⟩,⟨_,p114x31⟩,⟨_,p114x4⟩,⟨_,p114x36⟩,⟨_,p114x11⟩,⟨_,p114x24⟩,⟨_,p114x37⟩] (unpack 5 0x8007800680050a948004400009928003038680020a9103850a85800140030b12800003830983400240010991 99 0x248412d695a6a4211e4335a4690cf7a5a913de97a68d6aa4a0b5aa6aa72941ad8bdf07bdcd690245a9445116c5854a48921084c8310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x39 : Ex t114 4 [v94,u0,u2,u4,u1] :=
  certify c114 [] (unpack 4 0x9910a9403850b140b0609830a850b1203830a910386 37 0x5a58282a25628789565623238787565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x40 : Ex t114 4 [v95,u1,u2,u4,u0] :=
  certify c114 [] (unpack 3 0x99203860a9409830a8503830a910385 37 0x4f32cbddaa8d471a28ebac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x41 : Ex t114 5 [v86,u2,u4,u0,u1] :=
  certify c114 [⟨_,p114x15⟩,⟨_,p114x39⟩,⟨_,p114x19⟩,⟨_,p114x25⟩,⟨_,p114x28⟩,⟨_,p114x40⟩,⟨_,p114x32⟩,⟨_,p114x37⟩] (unpack 5 0x80078006099180054001800403850b14800380020992800140000a9480000386038309830a85400240030a91 99 0x11e414e64992af796650bde5796939c5ef939d173a0f7bd0f718cf33dc8410c412d64591a631565098c53158b5a4c652109420e6304a5208810842118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p114x42 : Ex t114 6 (roots 23) :=
  certify c114 [⟨_,p114x12⟩,⟨_,p114x21⟩,⟨_,p114x26⟩,⟨_,p114x34⟩,⟨_,p114x38⟩,⟨_,p114x41⟩] (unpack 5 0x800580040a8580030a9109914002098380020b064003038380010b120992400140000386038580000b140a94 96 0x5cd4a7ba2e5ce33ab94a3386e7ce1333a0ea4c6332a0a5c4633286a946102b88e7b0ec2b8ee6b0842a8ea5a0842a88a4a0e728c033048428c8310400) (by decide +kernel)
theorem l114 : CClaim 23 t114 7 := fromTable 805356166 (by decide +kernel) p114x42

abbrev t115 : Sig := 0xee008800ee008800ee008800ee008800
theorem l115 : CClaim 27 t115 5 := liftTable 8 8 2422211722 5 l54 (by decide +kernel)

abbrev t119 : Sig := 0xfa00a000fa00a000fa00a000fa00a000
theorem l119 : CClaim 29 t119 5 := liftTable 8 8 2426552332 5 l57 (by decide +kernel)

abbrev t129 : Sig := 0xee00ee0088008800ee00ee0088008800
theorem l129 : CClaim 43 t129 5 := liftTable 8 8 309243937930 5 l75 (by decide +kernel)

abbrev t131 : Sig := 0xee88ee88ee00ee00ee88ee88ee00ee00
theorem l131 : CClaim 43 t131 5 := liftTable 32 32 103081313288 5 l40 (by decide +kernel)

abbrev t133 : Sig := 0xfa00fa00a000a000fa00fa00a000a000
theorem l133 : CClaim 45 t133 5 := liftTable 8 8 309248278540 5 l78 (by decide +kernel)

abbrev t135 : Sig := 0xfaa0faa0fa00fa00faa0faa0fa00fa00
theorem l135 : CClaim 45 t135 5 := liftTable 32 32 171800920072 5 l45 (by decide +kernel)

abbrev t143 : Sig := 0xeeeeeeeeeeee8888eeeeeeeeeeee8888
theorem l143 : CClaim 51 t143 5 := liftTable 0 32 34628173954 5 l54 (by decide +kernel)

abbrev t146 : Sig := 0xfafaa0a0a0a0a0a0fafaa0a0a0a0a0a0
theorem l146 : CClaim 53 t146 5 := liftTable 32 32 592973938692 5 l57 (by decide +kernel)

abbrev t147 : Sig := 0xfafafafafafaa0a0fafafafafafaa0a0
theorem l147 : CClaim 53 t147 5 := liftTable 0 32 34628190212 5 l57 (by decide +kernel)

abbrev t150 : Sig := 0xfcfcc0c0c0c0c0c0fcfcc0c0c0c0c0c0
theorem l150 : CClaim 54 t150 5 := liftTable 32 32 627602129408 5 l60 (by decide +kernel)

abbrev t154 : Sig := 0xffaaff00ff00aa00ffaaff00ff00aa00
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c154 : Cuts t154 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x0 : Ex t154 3 [v96,u0,u3,u5] :=
  certify c154 [] (unpack 4 0x48114200c910c10048818a1140818910c08 24 0x272588071212656544300210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x1 : Ex t154 3 [v97,u0,u3,u5] :=
  certify c154 [] (unpack 3 0x1420140818910c1004810c0818a10488 24 0x7f31a861c5aa8d3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x2 : Ex t154 3 [v98,u0,u3,u4] :=
  certify c154 [] (unpack 4 0x1420048118a10c0814a10c10048818911408 24 0x501553587703656543432210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x3 : Ex t154 3 [v99,u0,u3,u4] :=
  certify c154 [] (unpack 3 0x18a10c100c0814200481140818910488 24 0x7ab17861e54d8d3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x4 : Ex t154 4 [v16,u0,u3,u4,u5] :=
  certify c154 [⟨_,p154x0⟩,⟨_,p154x1⟩,⟨_,p154x2⟩,⟨_,p154x3⟩] (unpack 4 0x1420189118a118b00c100c11800380021408800180000c0804810488 33 0x25c25d59292dc5c5b2b2a987565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x5 : Ex t154 3 [v100,u0,u3,u5] :=
  certify c154 [] (unpack 3 0xc100481142018a10488140818910c08 24 0xd56dc668bcf5623088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x6 : Ex t154 3 [v101,u0,u3,u5] :=
  certify c154 [] (unpack 3 0x1891140804810c1018a104880c08 24 0x9ac3718631a8823288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x7 : Ex t154 3 [v102,u0,u3,u4] :=
  certify c154 [] (unpack 3 0x142018a104810c100488140818910c08 24 0xb05bd5633aec68b408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x8 : Ex t154 3 [v103,u0,u3,u4] :=
  certify c154 [] (unpack 3 0xc9118a10c0804811420189104881408 24 0x9ec371863aa8823288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x9 : Ex t154 4 [v42,u0,u3,u4,u5] :=
  certify c154 [⟨_,p154x5⟩,⟨_,p154x6⟩,⟨_,p154x7⟩,⟨_,p154x8⟩] (unpack 4 0xc910c10189118a1048104880c1118b080031408800280010c088000 33 0x14b19b499d19c84b881a8987645431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x10 : Ex t154 4 [v104,u0,u3,u4,u5] :=
  certify c154 [] (unpack 4 0x1420048004880c101891140818a10c08048118b0 33 0x245249462629745772378765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x11 : Ex t154 4 [v105,u0,u3,u4,u5] :=
  certify c154 [] (unpack 4 0xc910480048118b0140818910c0818a10c100488 33 0x354374577937454523238765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x12 : Ex t154 3 [v63,v82,u3,u5] :=
  certify c154 [] (unpack 3 0x14200c9104810c88140818910488 21 0x4ca0931455963088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x13 : Ex t154 4 [v82,u0,u4,u3,u5] :=
  certify c154 [⟨_,p154x12⟩] (unpack 4 0x14200c1004880c088000189114080c91048118a118b0 33 0x2a4229727457845828298765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x14 : Ex t154 4 [v63,u0,u4,u3,u5] :=
  certify c154 [⟨_,p154x12⟩] (unpack 4 0x14200c0804810c1018a118b08000048818911408 33 0x790776679779101081010767654321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x15 : Ex t154 3 [v106,u0,u4,u3] :=
  certify c154 [] (unpack 3 0x4810c1018a10c08048818911408 24 0xd5e1b560bd758e3488) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x16 : Ex t154 3 [v107,u0,u4,u3] :=
  certify c154 [] (unpack 3 0x142004810c100c0818b0140818910488 24 0xd66dd688cc35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x17 : Ex t154 4 [v108,u0,u4,u3,u5] :=
  certify c154 [⟨_,p154x15⟩,⟨_,p154x16⟩] (unpack 4 0x142018910c8818b00c0880018000140804810c1018a10488 33 0x3b43327374a7a4a432329876454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x18 : Ex t154 3 [v109,u0,u4,u3] :=
  certify c154 [] (unpack 3 0xc0804810c1018b018a1140818910488 24 0xd6ed56fcac35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x19 : Ex t154 3 [v110,u0,u4,u3] :=
  certify c154 [] (unpack 3 0xc1018a1048814200481140818910c08 24 0x7c375fa35a8d8d3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x20 : Ex t154 4 [v111,u0,u4,u3,u5] :=
  certify c154 [⟨_,p154x18⟩,⟨_,p154x19⟩] (unpack 4 0x142018910c8818a104888001800014080c1004810c0818b0 33 0x2b422332a4a474a727239876454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x21 : Ex t154 3 [v112,v113,u3,u4] :=
  certify c154 [] (unpack 3 0x4880c1018a10c08189114a104811488 21 0x4f79d0f2758e3288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x22 : Ex t154 4 [v113,u0,u5,u3,u4] :=
  certify c154 [⟨_,p154x21⟩] (unpack 4 0x14200c1004881408800018a10c0814a10481189118b0 33 0x475429422a72845828298765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x23 : Ex t154 4 [v112,u0,u5,u3,u4] :=
  certify c154 [⟨_,p154x21⟩] (unpack 4 0x1420140818a10c0804810c10189118b080000488 33 0x673667765465599545548767654543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x24 : Ex t154 3 [v114,u0,u5,u3] :=
  certify c154 [] (unpack 3 0x142004810c10048818a1140818910c08 24 0xdd61b7d7528a918088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x25 : Ex t154 3 [v115,u0,u5,u3] :=
  certify c154 [] (unpack 3 0x142004810c1018b00488140818a10c08 24 0xdd6d46cf56a360b088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x26 : Ex t154 4 [v116,u0,u5,u3,u4] :=
  certify c154 [⟨_,p154x24⟩,⟨_,p154x25⟩] (unpack 4 0x142018a1148818b01408800180000c0804810c1018910488 33 0x47a432433b73a4a432329876454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x27 : Ex t154 3 [v117,u0,u5,u3] :=
  certify c154 [] (unpack 4 0x142004810c1018b018a10488140818910c08 24 0x788776077376351330430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x28 : Ex t154 3 [v118,u0,u5,u3] :=
  certify c154 [] (unpack 3 0x14200c100481140818910c0818a10488 24 0xbe5a2e118d5551a408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x29 : Ex t154 4 [v119,u0,u5,u3,u4] :=
  certify c154 [⟨_,p154x27⟩,⟨_,p154x28⟩] (unpack 4 0x18a10c10148818910488800180000c0814200481140818b0 33 0x4b842a42233274b7272a9876454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x30 : Ex t154 3 [v120,u3,u4,u0] :=
  certify c154 [] (unpack 4 0x18b0142004880c08189118a11c300c1014080481 24 0x794707087157665104300210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x31 : Ex t154 3 [v121,u3,u4,u0] :=
  certify c154 [] (unpack 3 0x18a10c10048818910c08142014080481 24 0xafd1461983652e3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x32 : Ex t154 3 [v122,u3,u4,u5] :=
  certify c154 [] (unpack 3 0xc9104811420140818910c0818a10488 24 0x71cd66dfe1b5118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x33 : Ex t154 3 [v123,u3,u4,u5] :=
  certify c154 [] (unpack 3 0x1420140818910c0818a1048804810c10 24 0x9ac3f12215aa51a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x34 : Ex t154 4 [v124,u3,u4,u0,u5] :=
  certify c154 [⟨_,p154x30⟩,⟨_,p154x31⟩,⟨_,p154x32⟩,⟨_,p154x33⟩] (unpack 4 0x18b080038002048818911420048118a108898001800014080c080c10 33 0xa29aad6a7a78acba92927827765423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x35 : Ex t154 3 [v125,u3,u4,u0] :=
  certify c154 [] (unpack 3 0x18b0048818910c100c08142014080481 24 0xcfe184c6e66b118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x36 : Ex t154 3 [v126,u3,u4,u0] :=
  certify c154 [] (unpack 4 0x18a10c910c10048818910c08048114081420 24 0x538575563630545134312210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x37 : Ex t154 3 [v127,u3,u4,u5] :=
  certify c154 [] (unpack 3 0x1420140818910c0818b0048104880c10 24 0x9acdf08273a9319488) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x38 : Ex t154 3 [v128,u3,u4,u5] :=
  certify c154 [] (unpack 3 0x1891140818a10c080c1004880481 24 0x7731a80983a9319408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x39 : Ex t154 4 [v129,u3,u4,u0,u5] :=
  certify c154 [⟨_,p154x35⟩,⟨_,p154x36⟩,⟨_,p154x37⟩,⟨_,p154x38⟩] (unpack 4 0x18b00c9180030488800218a118910c080c1008890481800114088000 33 0xa17aa6dacaa5baa961768171565431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x40 : Ex t154 4 [v130,u3,u4,u0,u5] :=
  certify c154 [] (unpack 4 0xc910c000c1018a114081891048818b00c080481 33 0x354332639337454554578765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x41 : Ex t154 4 [v131,u3,u4,u0,u5] :=
  certify c154 [] (unpack 4 0x14200c000c0804811891140818b0048818a10c10 33 0x245227326269745769468765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x42 : Ex t154 3 [v132,u3,u5,u0] :=
  certify c154 [] (unpack 4 0x18b018a104881c300c100481140818910c08 24 0x681636346076315334030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x43 : Ex t154 3 [v133,u3,u5,u0] :=
  certify c154 [] (unpack 3 0x142018a10488140818910c100c080481 24 0xb1d1421e0375319408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x44 : Ex t154 3 [v134,u3,u5,u4] :=
  certify c154 [] (unpack 3 0x14a104810c100c0818a1140818910488 24 0x8ccd66c7e1b5118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x45 : Ex t154 3 [v135,u3,u5,u4] :=
  certify c154 [] (unpack 3 0x14200c0818a114081891048804810c10 24 0xd1e2313e15aa51a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x46 : Ex t154 4 [v136,u3,u5,u0,u4] :=
  certify c154 [⟨_,p154x42⟩,⟨_,p154x43⟩,⟨_,p154x44⟩,⟨_,p154x45⟩] (unpack 4 0x18a118b08003800204880c10048118911089800180000c0814081420 33 0x2d6292d99c6979789ba97827765423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x47 : Ex t154 3 [v137,u3,u5,u4] :=
  certify c154 [] (unpack 3 0x14200c0818a1140818b0048104880c10 24 0xd2ec379e03a9319488) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x48 : Ex t154 3 [v138,u3,u5,u4] :=
  certify c154 [] (unpack 4 0xc91142018a10c08189114080c1004880481 24 0x534508500730165114312010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x49 : Ex t154 3 [v139,u3,u5,u0] :=
  certify c154 [] (unpack 3 0x18b0048814200c100481140818a10c08 24 0xcbe79dc0e753703088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x50 : Ex t154 3 [v140,u3,u5,u0] :=
  certify c154 [] (unpack 4 0xc91142018a104881891140804810c080c10 24 0x534585503730565114312210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x51 : Ex t154 4 [v141,u3,u5,u0,u4] :=
  certify c154 [⟨_,p154x47⟩,⟨_,p154x48⟩,⟨_,p154x49⟩,⟨_,p154x50⟩] (unpack 4 0x8003800218b014a1800104888000189118a10c081408142010890481 33 0x4354d44c845883b8a8829887645423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x52 : Ex t154 4 [v142,u3,u5,u0,u4] :=
  certify c154 [] (unpack 4 0x14a11400142018910c0818a1048818b014080481 33 0x546535433263933754578765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x53 : Ex t154 4 [v143,u3,u5,u0,u4] :=
  certify c154 [] (unpack 4 0xc1014001408048118a10c0818b0048818911420 33 0x475424522732626969468765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x54 : Ex t154 3 [v144,v145,u0,u3] :=
  certify c154 [] (unpack 3 0x1c3004810c1018910c0818b004881881 21 0x69f6af63a9509688) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x55 : Ex t154 4 [v145,u4,u5,u0,u3] :=
  certify c154 [⟨_,p154x54⟩] (unpack 4 0x14201c3004810c1018b004880c0814088000189118a1 33 0x8a3887488998858753655465566543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x56 : Ex t154 4 [v144,u4,u5,u0,u3] :=
  certify c154 [⟨_,p154x54⟩] (unpack 4 0x142004810c1018b004881408189118a180000c08 33 0x899887788778858756355625566543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x57 : Ex t154 3 [v146,u4,u5,u3] :=
  certify c154 [] (unpack 3 0xc1004811420140818910c0818a10488 24 0xd66dfe71cc35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x58 : Ex t154 3 [v147,u4,u5,u3] :=
  certify c154 [] (unpack 3 0x142004810c10140818b00c0818a10488 24 0xde6d5650ac35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x59 : Ex t154 4 [v148,u4,u5,u0,u3] :=
  certify c154 [⟨_,p154x57⟩,⟨_,p154x58⟩] (unpack 4 0x142018b0188118a114080c10048180018000048818910c08 33 0x5b755665525627a22a829876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x60 : Ex t154 3 [v149,u4,u5,u3] :=
  certify c154 [] (unpack 3 0x142004810c10140818910c0818a10488 24 0xdfed5645ac35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x61 : Ex t154 3 [v150,u4,u5,u3] :=
  certify c154 [] (unpack 3 0x142004810c10140818910c0818b00488 24 0xde6d5651ac35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x62 : Ex t154 4 [v151,u4,u5,u0,u3] :=
  certify c154 [⟨_,p154x60⟩,⟨_,p154x61⟩] (unpack 4 0xc1018b0188118910c0814200481800180000488140818a1 33 0x56655b75525b2a8227a29876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p154x63 : Ex t154 5 (roots 57) :=
  certify c154 [⟨_,p154x4⟩,⟨_,p154x9⟩,⟨_,p154x10⟩,⟨_,p154x11⟩,⟨_,p154x13⟩,⟨_,p154x14⟩,⟨_,p154x17⟩,⟨_,p154x20⟩,⟨_,p154x22⟩,⟨_,p154x23⟩,⟨_,p154x26⟩,⟨_,p154x29⟩,⟨_,p154x34⟩,⟨_,p154x39⟩,⟨_,p154x40⟩,⟨_,p154x41⟩,⟨_,p154x46⟩,⟨_,p154x51⟩,⟨_,p154x52⟩,⟨_,p154x53⟩,⟨_,p154x55⟩,⟨_,p154x56⟩,⟨_,p154x59⟩,⟨_,p154x62⟩] (unpack 6 0x801780168015801480138012801114208010800f800e800d800c800b800a800918918008140880078006800518a180040c0880038002800104880481800018b00c10 96 0x8102087ce28e79029074e20870e0c36d065968e64e6100c35c80c358a00054800850a0c34d010448e04e4500503ce10434a1043080482ca04a2481041c3043180104143103080040) (by decide +kernel)
theorem l154 : CClaim 57 t154 6 := fromTable 277027487752 (by decide +kernel) p154x63

abbrev t157 : Sig := 0xffccff00ff00cc00ffccff00ff00cc00
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c157 : Cuts t157 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x0 : Ex t157 3 [v152,u1,u3,u5] :=
  certify c157 [] (unpack 4 0x50214200d120c1005081922140819120c08 24 0x272588071212656544300210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x1 : Ex t157 3 [v153,u1,u3,u5] :=
  certify c157 [] (unpack 3 0x1420140819120c1005020c0819220508 24 0x7f31a861c5aa8d3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x2 : Ex t157 3 [v154,u1,u3,u4] :=
  certify c157 [] (unpack 4 0x1420050219220c0815220c10050819121408 24 0x501553587703656543432210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x3 : Ex t157 3 [v155,u1,u3,u4] :=
  certify c157 [] (unpack 3 0x19220c100c0814200502140819120508 24 0x7ab17861e54d8d3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x4 : Ex t157 4 [v15,u1,u3,u4,u5] :=
  certify c157 [⟨_,p157x0⟩,⟨_,p157x1⟩,⟨_,p157x2⟩,⟨_,p157x3⟩] (unpack 4 0x14201912192219300c100c12800380021408800180000c0805020508 33 0x25c25d59292dc5c5b2b2a987565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x5 : Ex t157 3 [v156,u1,u3,u5] :=
  certify c157 [] (unpack 3 0xc100502142019220508140819120c08 24 0xd56dc668bcf5623088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x6 : Ex t157 3 [v157,u1,u3,u5] :=
  certify c157 [] (unpack 3 0x1912140805020c10192205080c08 24 0x9ac3718631a8823288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x7 : Ex t157 3 [v158,u1,u3,u4] :=
  certify c157 [] (unpack 3 0x1420192205020c100508140819120c08 24 0xb05bd5633aec68b408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x8 : Ex t157 3 [v159,u1,u3,u4] :=
  certify c157 [] (unpack 3 0xd1219220c0805021420191205081408 24 0x9ec371863aa8823288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x9 : Ex t157 4 [v41,u1,u3,u4,u5] :=
  certify c157 [⟨_,p157x5⟩,⟨_,p157x6⟩,⟨_,p157x7⟩,⟨_,p157x8⟩] (unpack 4 0xd120c1019121922050205080c12193080031408800280010c088000 33 0x14b19b499d19c84b881a8987645431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x10 : Ex t157 4 [v160,u1,u3,u4,u5] :=
  certify c157 [] (unpack 4 0x1420050005080c101912140819220c0805021930 33 0x245249462629745772378765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x11 : Ex t157 4 [v161,u1,u3,u4,u5] :=
  certify c157 [] (unpack 4 0xd12050005021930140819120c0819220c100508 33 0x354374577937454523238765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x12 : Ex t157 3 [v62,v81,u3,u5] :=
  certify c157 [] (unpack 3 0x14200d1205020d08140819120508 21 0x4ca0931455963088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x13 : Ex t157 4 [v81,u1,u4,u3,u5] :=
  certify c157 [⟨_,p157x12⟩] (unpack 4 0x14200c1005080c088000191214080d12050219221930 33 0x2a4229727457845828298765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x14 : Ex t157 4 [v62,u1,u4,u3,u5] :=
  certify c157 [⟨_,p157x12⟩] (unpack 4 0x14200c0805020c10192219308000050819121408 33 0x790776679779101081010767654321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x15 : Ex t157 3 [v162,u1,u4,u3] :=
  certify c157 [] (unpack 3 0x5020c1019220c08050819121408 24 0xd5e1b560bd758e3488) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x16 : Ex t157 3 [v163,u1,u4,u3] :=
  certify c157 [] (unpack 3 0x142005020c100c081930140819120508 24 0xd66dd688cc35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x17 : Ex t157 4 [v164,u1,u4,u3,u5] :=
  certify c157 [⟨_,p157x15⟩,⟨_,p157x16⟩] (unpack 4 0x142019120d0819300c0880018000140805020c1019220508 33 0x3b43327374a7a4a432329876454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x18 : Ex t157 3 [v165,u1,u4,u3] :=
  certify c157 [] (unpack 3 0xc0805020c1019301922140819120508 24 0xd6ed56fcac35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x19 : Ex t157 3 [v166,u1,u4,u3] :=
  certify c157 [] (unpack 3 0xc101922050814200502140819120c08 24 0x7c375fa35a8d8d3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x20 : Ex t157 4 [v167,u1,u4,u3,u5] :=
  certify c157 [⟨_,p157x18⟩,⟨_,p157x19⟩] (unpack 4 0x142019120d08192205088001800014080c1005020c081930 33 0x2b422332a4a474a727239876454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x21 : Ex t157 3 [v168,v169,u3,u4] :=
  certify c157 [] (unpack 3 0x5080c1019220c081912152205021508 21 0x4f79d0f2758e3288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x22 : Ex t157 4 [v169,u1,u5,u3,u4] :=
  certify c157 [⟨_,p157x21⟩] (unpack 4 0x14200c1005081408800019220c081522050219121930 33 0x475429422a72845828298765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x23 : Ex t157 4 [v168,u1,u5,u3,u4] :=
  certify c157 [⟨_,p157x21⟩] (unpack 4 0x1420140819220c0805020c101912193080000508 33 0x673667765465599545548767654543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x24 : Ex t157 3 [v170,u1,u5,u3] :=
  certify c157 [] (unpack 3 0x142005020c1005081922140819120c08 24 0xdd61b7d7528a918088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x25 : Ex t157 3 [v171,u1,u5,u3] :=
  certify c157 [] (unpack 3 0x142005020c1019300508140819220c08 24 0xdd6d46cf56a360b088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x26 : Ex t157 4 [v172,u1,u5,u3,u4] :=
  certify c157 [⟨_,p157x24⟩,⟨_,p157x25⟩] (unpack 4 0x14201922150819301408800180000c0805020c1019120508 33 0x47a432433b73a4a432329876454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x27 : Ex t157 3 [v173,u1,u5,u3] :=
  certify c157 [] (unpack 4 0x142005020c10193019220508140819120c08 24 0x788776077376351330430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x28 : Ex t157 3 [v174,u1,u5,u3] :=
  certify c157 [] (unpack 3 0x14200c100502140819120c0819220508 24 0xbe5a2e118d5551a408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x29 : Ex t157 4 [v175,u1,u5,u3,u4] :=
  certify c157 [⟨_,p157x27⟩,⟨_,p157x28⟩] (unpack 4 0x19220c10150819120508800180000c081420050214081930 33 0x4b842a42233274b7272a9876454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x30 : Ex t157 3 [v120,u3,u4,u1] :=
  certify c157 [] (unpack 4 0x1930142005080c08191219221c300c1014080502 24 0x794707087157665104300210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x31 : Ex t157 3 [v121,u3,u4,u1] :=
  certify c157 [] (unpack 3 0x19220c10050819120c08142014080502 24 0xafd1461983652e3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x32 : Ex t157 3 [v176,u3,u4,u5] :=
  certify c157 [] (unpack 3 0xd1205021420140819120c0819220508 24 0x71cd66dfe1b5118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x33 : Ex t157 3 [v177,u3,u4,u5] :=
  certify c157 [] (unpack 3 0x1420140819120c081922050805020c10 24 0x9ac3f12215aa51a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x34 : Ex t157 4 [v124,u3,u4,u1,u5] :=
  certify c157 [⟨_,p157x30⟩,⟨_,p157x31⟩,⟨_,p157x32⟩,⟨_,p157x33⟩] (unpack 4 0x19308003800205081912142005021922090a8001800014080c080c10 33 0xa29aad6a7a78acba92927827765423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x35 : Ex t157 3 [v125,u3,u4,u1] :=
  certify c157 [] (unpack 3 0x1930050819120c100c08142014080502 24 0xcfe184c6e66b118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x36 : Ex t157 3 [v126,u3,u4,u1] :=
  certify c157 [] (unpack 4 0x19220d120c10050819120c08050214081420 24 0x538575563630545134312210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x37 : Ex t157 3 [v178,u3,u4,u5] :=
  certify c157 [] (unpack 3 0x1420140819120c081930050205080c10 24 0x9acdf08273a9319488) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x38 : Ex t157 3 [v179,u3,u4,u5] :=
  certify c157 [] (unpack 3 0x1912140819220c080c1005080502 24 0x7731a80983a9319408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x39 : Ex t157 4 [v129,u3,u4,u1,u5] :=
  certify c157 [⟨_,p157x35⟩,⟨_,p157x36⟩,⟨_,p157x37⟩,⟨_,p157x38⟩] (unpack 4 0x19300d12800305088002192219120c080c10090a0502800114088000 33 0xa17aa6dacaa5baa961768171565431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x40 : Ex t157 4 [v130,u3,u4,u1,u5] :=
  certify c157 [] (unpack 4 0xd120c000c10192214081912050819300c080502 33 0x354332639337454554578765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x41 : Ex t157 4 [v131,u3,u4,u1,u5] :=
  certify c157 [] (unpack 4 0x14200c000c080502191214081930050819220c10 33 0x245227326269745769468765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x42 : Ex t157 3 [v132,u3,u5,u1] :=
  certify c157 [] (unpack 4 0x1930192205081c300c100502140819120c08 24 0x681636346076315334030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x43 : Ex t157 3 [v133,u3,u5,u1] :=
  certify c157 [] (unpack 3 0x142019220508140819120c100c080502 24 0xb1d1421e0375319408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x44 : Ex t157 3 [v180,u3,u5,u4] :=
  certify c157 [] (unpack 3 0x152205020c100c081922140819120508 24 0x8ccd66c7e1b5118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x45 : Ex t157 3 [v181,u3,u5,u4] :=
  certify c157 [] (unpack 3 0x14200c08192214081912050805020c10 24 0xd1e2313e15aa51a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x46 : Ex t157 4 [v136,u3,u5,u1,u4] :=
  certify c157 [⟨_,p157x42⟩,⟨_,p157x43⟩,⟨_,p157x44⟩,⟨_,p157x45⟩] (unpack 4 0x192219308003800205080c1005021912110a800180000c0814081420 33 0x2d6292d99c6979789ba97827765423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x47 : Ex t157 3 [v182,u3,u5,u4] :=
  certify c157 [] (unpack 3 0x14200c08192214081930050205080c10 24 0xd2ec379e03a9319488) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x48 : Ex t157 3 [v183,u3,u5,u4] :=
  certify c157 [] (unpack 4 0xd12142019220c08191214080c1005080502 24 0x534508500730165114312010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x49 : Ex t157 3 [v139,u3,u5,u1] :=
  certify c157 [] (unpack 3 0x1930050814200c100502140819220c08 24 0xcbe79dc0e753703088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x50 : Ex t157 3 [v140,u3,u5,u1] :=
  certify c157 [] (unpack 4 0xd121420192205081912140805020c080c10 24 0x534585503730565114312210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x51 : Ex t157 4 [v141,u3,u5,u1,u4] :=
  certify c157 [⟨_,p157x47⟩,⟨_,p157x48⟩,⟨_,p157x49⟩,⟨_,p157x50⟩] (unpack 4 0x8003800219301522800105088000191219220c0814081420110a0502 33 0x4354d44c845883b8a8829887645423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x52 : Ex t157 4 [v142,u3,u5,u1,u4] :=
  certify c157 [] (unpack 4 0x15221400142019120c0819220508193014080502 33 0x546535433263933754578765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x53 : Ex t157 4 [v143,u3,u5,u1,u4] :=
  certify c157 [] (unpack 4 0xc1014001408050219220c081930050819121420 33 0x475424522732626969468765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x54 : Ex t157 3 [v144,v145,u1,u3] :=
  certify c157 [] (unpack 3 0x1c3005020c1019120c08193005081902 21 0x69f6af63a9509688) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x55 : Ex t157 4 [v145,u4,u5,u1,u3] :=
  certify c157 [⟨_,p157x54⟩] (unpack 4 0x14201c3005020c10193005080c081408800019121922 33 0x8a3887488998858753655465566543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x56 : Ex t157 4 [v144,u4,u5,u1,u3] :=
  certify c157 [⟨_,p157x54⟩] (unpack 4 0x142005020c101930050814081912192280000c08 33 0x899887788778858756355625566543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x57 : Ex t157 3 [v184,u4,u5,u3] :=
  certify c157 [] (unpack 3 0xc1005021420140819120c0819220508 24 0xd66dfe71cc35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x58 : Ex t157 3 [v185,u4,u5,u3] :=
  certify c157 [] (unpack 3 0x142005020c10140819300c0819220508 24 0xde6d5650ac35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x59 : Ex t157 4 [v148,u4,u5,u1,u3] :=
  certify c157 [⟨_,p157x57⟩,⟨_,p157x58⟩] (unpack 4 0x142019301902192214080c10050280018000050819120c08 33 0x5b755665525627a22a829876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x60 : Ex t157 3 [v186,u4,u5,u3] :=
  certify c157 [] (unpack 3 0x142005020c10140819120c0819220508 24 0xdfed5645ac35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x61 : Ex t157 3 [v187,u4,u5,u3] :=
  certify c157 [] (unpack 3 0x142005020c10140819120c0819300508 24 0xde6d5651ac35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x62 : Ex t157 4 [v151,u4,u5,u1,u3] :=
  certify c157 [⟨_,p157x60⟩,⟨_,p157x61⟩] (unpack 4 0xc101930190219120c081420050280018000050814081922 33 0x56655b75525b2a8227a29876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p157x63 : Ex t157 5 (roots 58) :=
  certify c157 [⟨_,p157x4⟩,⟨_,p157x9⟩,⟨_,p157x10⟩,⟨_,p157x11⟩,⟨_,p157x13⟩,⟨_,p157x14⟩,⟨_,p157x17⟩,⟨_,p157x20⟩,⟨_,p157x22⟩,⟨_,p157x23⟩,⟨_,p157x26⟩,⟨_,p157x29⟩,⟨_,p157x34⟩,⟨_,p157x39⟩,⟨_,p157x40⟩,⟨_,p157x41⟩,⟨_,p157x46⟩,⟨_,p157x51⟩,⟨_,p157x52⟩,⟨_,p157x53⟩,⟨_,p157x55⟩,⟨_,p157x56⟩,⟨_,p157x59⟩,⟨_,p157x62⟩] (unpack 6 0x801780168015801480138012801114208010800f800e800d800c800b800a8009191280081408800780068005192280040c0880038002800105080502800019300c10 96 0x8102087ce28e79029074e20870e0c36d065968e64e6100c35c80c358a00054800850a0c34d010448e04e4500503ce10434a1043080482ca04a2481041c3043180104143103080040) (by decide +kernel)
theorem l157 : CClaim 58 t157 6 := fromTable 277029585920 (by decide +kernel) p157x63

abbrev t160 : Sig := 0xfff0ff00ff00f000fff0ff00ff00f000
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c160 : Cuts t160 := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x0 : Ex t160 3 [v188,u2,u3,u5] :=
  certify c160 [] (unpack 4 0x60414200e140c1006081a2414081a140c08 24 0x272588071212656544300210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x1 : Ex t160 3 [v189,u2,u3,u5] :=
  certify c160 [] (unpack 3 0x142014081a140c1006040c081a240608 24 0x7f31a861c5aa8d3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x2 : Ex t160 3 [v190,u2,u3,u4] :=
  certify c160 [] (unpack 4 0x142006041a240c0816240c1006081a141408 24 0x501553587703656543432210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x3 : Ex t160 3 [v191,u2,u3,u4] :=
  certify c160 [] (unpack 3 0x1a240c100c081420060414081a140608 24 0x7ab17861e54d8d3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x4 : Ex t160 4 [v21,u2,u3,u4,u5] :=
  certify c160 [⟨_,p160x0⟩,⟨_,p160x1⟩,⟨_,p160x2⟩,⟨_,p160x3⟩] (unpack 4 0x14201a141a241a300c100c14800380021408800180000c0806040608 33 0x25c25d59292dc5c5b2b2a987565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x5 : Ex t160 3 [v192,u2,u3,u5] :=
  certify c160 [] (unpack 3 0xc10060414201a24060814081a140c08 24 0xd56dc668bcf5623088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x6 : Ex t160 3 [v193,u2,u3,u5] :=
  certify c160 [] (unpack 3 0x1a14140806040c101a2406080c08 24 0x9ac3718631a8823288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x7 : Ex t160 3 [v194,u2,u3,u4] :=
  certify c160 [] (unpack 3 0x14201a2406040c10060814081a140c08 24 0xb05bd5633aec68b408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x8 : Ex t160 3 [v195,u2,u3,u4] :=
  certify c160 [] (unpack 3 0xe141a240c08060414201a1406081408 24 0x9ec371863aa8823288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x9 : Ex t160 4 [v46,u2,u3,u4,u5] :=
  certify c160 [⟨_,p160x5⟩,⟨_,p160x6⟩,⟨_,p160x7⟩,⟨_,p160x8⟩] (unpack 4 0xe140c101a141a24060406080c141a3080031408800280010c088000 33 0x14b19b499d19c84b881a8987645431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x10 : Ex t160 4 [v196,u2,u3,u4,u5] :=
  certify c160 [] (unpack 4 0x1420060006080c101a1414081a240c0806041a30 33 0x245249462629745772378765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x11 : Ex t160 4 [v197,u2,u3,u4,u5] :=
  certify c160 [] (unpack 4 0xe14060006041a3014081a140c081a240c100608 33 0x354374577937454523238765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x12 : Ex t160 3 [v67,v86,u3,u5] :=
  certify c160 [] (unpack 3 0x14200e1406040e0814081a140608 21 0x4ca0931455963088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x13 : Ex t160 4 [v86,u2,u4,u3,u5] :=
  certify c160 [⟨_,p160x12⟩] (unpack 4 0x14200c1006080c0880001a1414080e1406041a241a30 33 0x2a4229727457845828298765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x14 : Ex t160 4 [v67,u2,u4,u3,u5] :=
  certify c160 [⟨_,p160x12⟩] (unpack 4 0x14200c0806040c101a241a30800006081a141408 33 0x790776679779101081010767654321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x15 : Ex t160 3 [v198,u2,u4,u3] :=
  certify c160 [] (unpack 3 0x6040c101a240c0806081a141408 24 0xd5e1b560bd758e3488) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x16 : Ex t160 3 [v199,u2,u4,u3] :=
  certify c160 [] (unpack 3 0x142006040c100c081a3014081a140608 24 0xd66dd688cc35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x17 : Ex t160 4 [v200,u2,u4,u3,u5] :=
  certify c160 [⟨_,p160x15⟩,⟨_,p160x16⟩] (unpack 4 0x14201a140e081a300c0880018000140806040c101a240608 33 0x3b43327374a7a4a432329876454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x18 : Ex t160 3 [v201,u2,u4,u3] :=
  certify c160 [] (unpack 3 0xc0806040c101a301a2414081a140608 24 0xd6ed56fcac35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x19 : Ex t160 3 [v202,u2,u4,u3] :=
  certify c160 [] (unpack 3 0xc101a2406081420060414081a140c08 24 0x7c375fa35a8d8d3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x20 : Ex t160 4 [v203,u2,u4,u3,u5] :=
  certify c160 [⟨_,p160x18⟩,⟨_,p160x19⟩] (unpack 4 0x14201a140e081a2406088001800014080c1006040c081a30 33 0x2b422332a4a474a727239876454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x21 : Ex t160 3 [v204,v205,u3,u4] :=
  certify c160 [] (unpack 3 0x6080c101a240c081a14162406041608 21 0x4f79d0f2758e3288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x22 : Ex t160 4 [v205,u2,u5,u3,u4] :=
  certify c160 [⟨_,p160x21⟩] (unpack 4 0x14200c100608140880001a240c08162406041a141a30 33 0x475429422a72845828298765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x23 : Ex t160 4 [v204,u2,u5,u3,u4] :=
  certify c160 [⟨_,p160x21⟩] (unpack 4 0x142014081a240c0806040c101a141a3080000608 33 0x673667765465599545548767654543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x24 : Ex t160 3 [v206,u2,u5,u3] :=
  certify c160 [] (unpack 3 0x142006040c1006081a2414081a140c08 24 0xdd61b7d7528a918088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x25 : Ex t160 3 [v207,u2,u5,u3] :=
  certify c160 [] (unpack 3 0x142006040c101a30060814081a240c08 24 0xdd6d46cf56a360b088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x26 : Ex t160 4 [v208,u2,u5,u3,u4] :=
  certify c160 [⟨_,p160x24⟩,⟨_,p160x25⟩] (unpack 4 0x14201a2416081a301408800180000c0806040c101a140608 33 0x47a432433b73a4a432329876454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x27 : Ex t160 3 [v209,u2,u5,u3] :=
  certify c160 [] (unpack 4 0x142006040c101a301a24060814081a140c08 24 0x788776077376351330430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x28 : Ex t160 3 [v210,u2,u5,u3] :=
  certify c160 [] (unpack 3 0x14200c10060414081a140c081a240608 24 0xbe5a2e118d5551a408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x29 : Ex t160 4 [v211,u2,u5,u3,u4] :=
  certify c160 [⟨_,p160x27⟩,⟨_,p160x28⟩] (unpack 4 0x1a240c1016081a140608800180000c081420060414081a30 33 0x4b842a42233274b7272a9876454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x30 : Ex t160 3 [v120,u3,u4,u2] :=
  certify c160 [] (unpack 4 0x1a30142006080c081a141a241c300c1014080604 24 0x794707087157665104300210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x31 : Ex t160 3 [v121,u3,u4,u2] :=
  certify c160 [] (unpack 3 0x1a240c1006081a140c08142014080604 24 0xafd1461983652e3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x32 : Ex t160 3 [v212,u3,u4,u5] :=
  certify c160 [] (unpack 3 0xe140604142014081a140c081a240608 24 0x71cd66dfe1b5118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x33 : Ex t160 3 [v213,u3,u4,u5] :=
  certify c160 [] (unpack 3 0x142014081a140c081a24060806040c10 24 0x9ac3f12215aa51a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x34 : Ex t160 4 [v124,u3,u4,u2,u5] :=
  certify c160 [⟨_,p160x30⟩,⟨_,p160x31⟩,⟨_,p160x32⟩,⟨_,p160x33⟩] (unpack 4 0x1a308003800206081a14142006041a240a0c8001800014080c080c10 33 0xa29aad6a7a78acba92927827765423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x35 : Ex t160 3 [v125,u3,u4,u2] :=
  certify c160 [] (unpack 3 0x1a3006081a140c100c08142014080604 24 0xcfe184c6e66b118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x36 : Ex t160 3 [v126,u3,u4,u2] :=
  certify c160 [] (unpack 4 0x1a240e140c1006081a140c08060414081420 24 0x538575563630545134312210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x37 : Ex t160 3 [v214,u3,u4,u5] :=
  certify c160 [] (unpack 3 0x142014081a140c081a30060406080c10 24 0x9acdf08273a9319488) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x38 : Ex t160 3 [v215,u3,u4,u5] :=
  certify c160 [] (unpack 3 0x1a1414081a240c080c1006080604 24 0x7731a80983a9319408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x39 : Ex t160 4 [v129,u3,u4,u2,u5] :=
  certify c160 [⟨_,p160x35⟩,⟨_,p160x36⟩,⟨_,p160x37⟩,⟨_,p160x38⟩] (unpack 4 0x1a300e148003060880021a241a140c080c100a0c0604800114088000 33 0xa17aa6dacaa5baa961768171565431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x40 : Ex t160 4 [v130,u3,u4,u2,u5] :=
  certify c160 [] (unpack 4 0xe140c000c101a2414081a1406081a300c080604 33 0x354332639337454554578765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x41 : Ex t160 4 [v131,u3,u4,u2,u5] :=
  certify c160 [] (unpack 4 0x14200c000c0806041a1414081a3006081a240c10 33 0x245227326269745769468765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x42 : Ex t160 3 [v132,u3,u5,u2] :=
  certify c160 [] (unpack 4 0x1a301a2406081c300c10060414081a140c08 24 0x681636346076315334030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x43 : Ex t160 3 [v133,u3,u5,u2] :=
  certify c160 [] (unpack 3 0x14201a24060814081a140c100c080604 24 0xb1d1421e0375319408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x44 : Ex t160 3 [v216,u3,u5,u4] :=
  certify c160 [] (unpack 3 0x162406040c100c081a2414081a140608 24 0x8ccd66c7e1b5118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x45 : Ex t160 3 [v217,u3,u5,u4] :=
  certify c160 [] (unpack 3 0x14200c081a2414081a14060806040c10 24 0xd1e2313e15aa51a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x46 : Ex t160 4 [v136,u3,u5,u2,u4] :=
  certify c160 [⟨_,p160x42⟩,⟨_,p160x43⟩,⟨_,p160x44⟩,⟨_,p160x45⟩] (unpack 4 0x1a241a308003800206080c1006041a14120c800180000c0814081420 33 0x2d6292d99c6979789ba97827765423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x47 : Ex t160 3 [v218,u3,u5,u4] :=
  certify c160 [] (unpack 3 0x14200c081a2414081a30060406080c10 24 0xd2ec379e03a9319488) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x48 : Ex t160 3 [v219,u3,u5,u4] :=
  certify c160 [] (unpack 4 0xe1414201a240c081a1414080c1006080604 24 0x534508500730165114312010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x49 : Ex t160 3 [v139,u3,u5,u2] :=
  certify c160 [] (unpack 3 0x1a30060814200c10060414081a240c08 24 0xcbe79dc0e753703088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x50 : Ex t160 3 [v140,u3,u5,u2] :=
  certify c160 [] (unpack 4 0xe1414201a2406081a14140806040c080c10 24 0x534585503730565114312210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x51 : Ex t160 4 [v141,u3,u5,u2,u4] :=
  certify c160 [⟨_,p160x47⟩,⟨_,p160x48⟩,⟨_,p160x49⟩,⟨_,p160x50⟩] (unpack 4 0x800380021a3016248001060880001a141a240c0814081420120c0604 33 0x4354d44c845883b8a8829887645423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x52 : Ex t160 4 [v142,u3,u5,u2,u4] :=
  certify c160 [] (unpack 4 0x1624140014201a140c081a2406081a3014080604 33 0x546535433263933754578765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x53 : Ex t160 4 [v143,u3,u5,u2,u4] :=
  certify c160 [] (unpack 4 0xc101400140806041a240c081a3006081a141420 33 0x475424522732626969468765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x54 : Ex t160 3 [v144,v145,u2,u3] :=
  certify c160 [] (unpack 3 0x1c3006040c101a140c081a3006081a04 21 0x69f6af63a9509688) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x55 : Ex t160 4 [v145,u4,u5,u2,u3] :=
  certify c160 [⟨_,p160x54⟩] (unpack 4 0x14201c3006040c101a3006080c08140880001a141a24 33 0x8a3887488998858753655465566543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x56 : Ex t160 4 [v144,u4,u5,u2,u3] :=
  certify c160 [⟨_,p160x54⟩] (unpack 4 0x142006040c101a30060814081a141a2480000c08 33 0x899887788778858756355625566543210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x57 : Ex t160 3 [v220,u4,u5,u3] :=
  certify c160 [] (unpack 3 0xc100604142014081a140c081a240608 24 0xd66dfe71cc35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x58 : Ex t160 3 [v221,u4,u5,u3] :=
  certify c160 [] (unpack 3 0x142006040c1014081a300c081a240608 24 0xde6d5650ac35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x59 : Ex t160 4 [v148,u4,u5,u2,u3] :=
  certify c160 [⟨_,p160x57⟩,⟨_,p160x58⟩] (unpack 4 0x14201a301a041a2414080c1006048001800006081a140c08 33 0x5b755665525627a22a829876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x60 : Ex t160 3 [v222,u4,u5,u3] :=
  certify c160 [] (unpack 3 0x142006040c1014081a140c081a240608 24 0xdfed5645ac35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x61 : Ex t160 3 [v223,u4,u5,u3] :=
  certify c160 [] (unpack 3 0x142006040c1014081a140c081a300608 24 0xde6d5651ac35118088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x62 : Ex t160 4 [v151,u4,u5,u2,u3] :=
  certify c160 [⟨_,p160x60⟩,⟨_,p160x61⟩] (unpack 4 0xc101a301a041a140c081420060480018000060814081a24 33 0x56655b75525b2a8227a29876565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p160x63 : Ex t160 5 (roots 60) :=
  certify c160 [⟨_,p160x4⟩,⟨_,p160x9⟩,⟨_,p160x10⟩,⟨_,p160x11⟩,⟨_,p160x13⟩,⟨_,p160x14⟩,⟨_,p160x17⟩,⟨_,p160x20⟩,⟨_,p160x22⟩,⟨_,p160x23⟩,⟨_,p160x26⟩,⟨_,p160x29⟩,⟨_,p160x34⟩,⟨_,p160x39⟩,⟨_,p160x40⟩,⟨_,p160x41⟩,⟨_,p160x46⟩,⟨_,p160x51⟩,⟨_,p160x52⟩,⟨_,p160x53⟩,⟨_,p160x55⟩,⟨_,p160x56⟩,⟨_,p160x59⟩,⟨_,p160x62⟩] (unpack 6 0x801780168015801480138012801114208010800f800e800d800c800b800a80091a14800814088007800680051a2480040c088003800280010608060480001a300c10 96 0x8102087ce28e79029074e20870e0c36d065968e64e6100c35c80c358a00054800850a0c34d010448e04e4500503ce10434a1043080482ca04a2481041c3043180104143103080040) (by decide +kernel)
theorem l160 : CClaim 60 t160 6 := fromTable 277033910272 (by decide +kernel) p160x63

abbrev t162 : Sig := 0xfe80e880fe80e880fe80e880fe80e880
theorem l162 : CClaim 31 t162 8 := liftTable 0 16 2422260358 8 l110 (by decide +kernel)

abbrev t163 : Sig := 0xfee8fe80fee8fe80fee8fe80fee8fe80
theorem l163 : CClaim 31 t163 8 := liftTable 16 16 807453318 8 l112 (by decide +kernel)

abbrev t164 : Sig := 0xfe80fe80e880e880fe80fe80e880e880
theorem l164 : CClaim 47 t164 8 := liftTable 0 32 309243986566 8 l110 (by decide +kernel)

abbrev t165 : Sig := 0xfee8fee8fe80fe80fee8fee8fe80fe80
theorem l165 : CClaim 47 t165 8 := liftTable 32 32 103081362054 8 l112 (by decide +kernel)

abbrev t166 : Sig := 0xe8e8808080808080e8e8808080808080
theorem l166 : CClaim 55 t166 8 := liftTable 32 32 662230319750 8 l114 (by decide +kernel)

abbrev t167 : Sig := 0xfefefefefefee8e8fefefefefefee8e8
theorem l167 : CClaim 55 t167 8 := liftTable 0 32 34628190338 8 l113 (by decide +kernel)

abbrev t168 : Sig := 0xee88ee00ee008800ee88ee00ee008800
theorem l168 : CClaim 59 t168 7 := liftTable 2 2 311659857034 7 l154 (by decide +kernel)

abbrev t169 : Sig := 0xffeeff88ff88ee88ffeeff88ff88ee88
theorem l169 : CClaim 59 t169 7 := liftTable 0 2 277027487874 7 l154 (by decide +kernel)

abbrev t170 : Sig := 0xfaa0fa00fa00a000faa0fa00fa00a000
theorem l170 : CClaim 61 t170 7 := liftTable 4 4 311664197644 7 l154 (by decide +kernel)

abbrev t171 : Sig := 0xfffaffa0ffa0faa0fffaffa0ffa0faa0
theorem l171 : CClaim 61 t171 7 := liftTable 0 4 277027504132 7 l154 (by decide +kernel)

abbrev t172 : Sig := 0xfcc0fc00fc00c000fcc0fc00fc00c000
theorem l172 : CClaim 62 t172 7 := liftTable 4 4 346294486528 7 l157 (by decide +kernel)

abbrev t173 : Sig := 0xfffcffc0ffc0fcc0fffcffc0ffc0fcc0
theorem l173 : CClaim 62 t173 7 := liftTable 0 4 277029618176 7 l157 (by decide +kernel)

abbrev t174 : Sig := 0xfee8fe80fe80e880fee8fe80fe80e880
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
def c174 : Cuts t174 := [
  rule t174 0 l172 none (by decide +kernel),
  rule t174 0 l170 none (by decide +kernel),
  rule t174 0 l168 none (by decide +kernel),
  rule t174 4 l169 none (by decide +kernel),
  rule t174 0 l166 none (by decide +kernel),
  rule t174 0 l166 (some (0,u0,u1)) (by decide +kernel),
  rule t174 8 l167 none (by decide +kernel),
  rule t174 8 l167 (some (0,u0,u1)) (by decide +kernel),
  rule t174 0 l164 none (by decide +kernel),
  rule t174 0 l164 (some (0,u0,u1)) (by decide +kernel),
  rule t174 16 l165 none (by decide +kernel),
  rule t174 16 l165 (some (0,u0,u1)) (by decide +kernel),
  rule t174 0 l162 none (by decide +kernel),
  rule t174 0 l162 (some (0,u0,u1)) (by decide +kernel),
  rule t174 32 l163 none (by decide +kernel),
  rule t174 32 l163 (some (0,u0,u1)) (by decide +kernel),
  rule t174 1 l173 none (by decide +kernel),
  rule t174 1 l157 none (by decide +kernel),
  rule t174 0 l133 none (by decide +kernel),
  rule t174 8 l147 none (by decide +kernel),
  rule t174 1 l150 none (by decide +kernel),
  rule t174 0 l119 none (by decide +kernel),
  rule t174 16 l135 none (by decide +kernel),
  rule t174 0 l166 (some (1,u0,u1)) (by decide +kernel),
  rule t174 8 l167 (some (1,u0,u1)) (by decide +kernel),
  rule t174 0 l164 (some (1,u0,u1)) (by decide +kernel),
  rule t174 16 l165 (some (1,u0,u1)) (by decide +kernel),
  rule t174 0 l162 (some (1,u0,u1)) (by decide +kernel),
  rule t174 32 l163 (some (1,u0,u1)) (by decide +kernel),
  rule t174 2 l171 none (by decide +kernel),
  rule t174 0 l166 (some (2,u0,u1)) (by decide +kernel),
  rule t174 8 l167 (some (2,u0,u1)) (by decide +kernel),
  rule t174 0 l164 (some (2,u0,u1)) (by decide +kernel),
  rule t174 16 l165 (some (2,u0,u1)) (by decide +kernel),
  rule t174 0 l162 (some (2,u0,u1)) (by decide +kernel),
  rule t174 32 l163 (some (2,u0,u1)) (by decide +kernel),
  rule t174 0 l166 (some (3,u0,u1)) (by decide +kernel),
  rule t174 8 l167 (some (3,u0,u1)) (by decide +kernel),
  rule t174 0 l164 (some (3,u0,u1)) (by decide +kernel),
  rule t174 16 l165 (some (3,u0,u1)) (by decide +kernel),
  rule t174 0 l162 (some (3,u0,u1)) (by decide +kernel),
  rule t174 32 l163 (some (3,u0,u1)) (by decide +kernel),
  rule t174 0 l166 (some (0,u0,u2)) (by decide +kernel),
  rule t174 8 l167 (some (0,u0,u2)) (by decide +kernel),
  rule t174 0 l164 (some (0,u0,u2)) (by decide +kernel),
  rule t174 16 l165 (some (0,u0,u2)) (by decide +kernel),
  rule t174 0 l162 (some (0,u0,u2)) (by decide +kernel),
  rule t174 32 l163 (some (0,u0,u2)) (by decide +kernel),
  rule t174 1 l160 none (by decide +kernel),
  rule t174 0 l129 none (by decide +kernel),
  rule t174 8 l143 none (by decide +kernel),
  rule t174 0 l115 none (by decide +kernel),
  rule t174 16 l131 none (by decide +kernel),
  rule t174 0 l166 (some (1,u0,u2)) (by decide +kernel),
  rule t174 8 l167 (some (1,u0,u2)) (by decide +kernel),
  rule t174 0 l164 (some (1,u0,u2)) (by decide +kernel),
  rule t174 16 l165 (some (1,u0,u2)) (by decide +kernel),
  rule t174 0 l162 (some (1,u0,u2)) (by decide +kernel),
  rule t174 32 l163 (some (1,u0,u2)) (by decide +kernel),
  rule t174 0 l166 (some (2,u0,u2)) (by decide +kernel),
  rule t174 8 l167 (some (2,u0,u2)) (by decide +kernel),
  rule t174 0 l164 (some (2,u0,u2)) (by decide +kernel),
  rule t174 16 l165 (some (2,u0,u2)) (by decide +kernel),
  rule t174 0 l162 (some (2,u0,u2)) (by decide +kernel),
  rule t174 32 l163 (some (2,u0,u2)) (by decide +kernel),
  rule t174 0 l166 (some (3,u0,u2)) (by decide +kernel),
  rule t174 8 l167 (some (3,u0,u2)) (by decide +kernel),
  rule t174 0 l164 (some (3,u0,u2)) (by decide +kernel),
  rule t174 16 l165 (some (3,u0,u2)) (by decide +kernel),
  rule t174 0 l162 (some (3,u0,u2)) (by decide +kernel),
  rule t174 32 l163 (some (3,u0,u2)) (by decide +kernel),
  rule t174 0 l166 (some (0,u1,u2)) (by decide +kernel),
  rule t174 8 l167 (some (0,u1,u2)) (by decide +kernel),
  rule t174 0 l164 (some (0,u1,u2)) (by decide +kernel),
  rule t174 16 l165 (some (0,u1,u2)) (by decide +kernel),
  rule t174 0 l162 (some (0,u1,u2)) (by decide +kernel),
  rule t174 32 l163 (some (0,u1,u2)) (by decide +kernel),
  rule t174 2 l146 none (by decide +kernel),
  rule t174 0 l166 (some (1,u1,u2)) (by decide +kernel),
  rule t174 8 l167 (some (1,u1,u2)) (by decide +kernel),
  rule t174 0 l164 (some (1,u1,u2)) (by decide +kernel),
  rule t174 16 l165 (some (1,u1,u2)) (by decide +kernel),
  rule t174 0 l162 (some (1,u1,u2)) (by decide +kernel),
  rule t174 32 l163 (some (1,u1,u2)) (by decide +kernel),
  rule t174 0 l166 (some (2,u1,u2)) (by decide +kernel),
  rule t174 8 l167 (some (2,u1,u2)) (by decide +kernel),
  rule t174 0 l164 (some (2,u1,u2)) (by decide +kernel),
  rule t174 16 l165 (some (2,u1,u2)) (by decide +kernel),
  rule t174 0 l162 (some (2,u1,u2)) (by decide +kernel),
  rule t174 32 l163 (some (2,u1,u2)) (by decide +kernel),
  rule t174 0 l166 (some (3,u1,u2)) (by decide +kernel),
  rule t174 8 l167 (some (3,u1,u2)) (by decide +kernel),
  rule t174 0 l164 (some (3,u1,u2)) (by decide +kernel),
  rule t174 16 l165 (some (3,u1,u2)) (by decide +kernel),
  rule t174 0 l162 (some (3,u1,u2)) (by decide +kernel),
  rule t174 32 l163 (some (3,u1,u2)) (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x0 : Ex t174 8 [v40,v14,u2,u3,u4,u5] :=
  certify c174 [] (unpack 5 0x401614a14015401440130c9140121628401113a5199319a30b9506850385068905894001038414a81489160c0c890e0c05831ab40e14068c038340100e180c98 228 0xed529cae8bfd695ead29eace7e57dedafcbed4e7ca4e7e535ada749cd0e7ba863baf0bbab0abac63ba063ba429ba028ba463bc863b9e07bca12b9c637563172ecb756d572e317523172669752737263171e27749f271de774a3170de37423170e23741ef7384d12c8b1298a12d8b128841248912008124091208411cc71148411c87114c510c031048410c8310400) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x1 : Ex t174 9 [v14,u0,u1,u2,u3,u4,u5] :=
  certify c174 [⟨_,p174x0⟩] (unpack 6 0x14a10c911628160c0e180e0c15281b340d1814a8150a0d0a1ab407060c98070a068c070c8000400f400e1993400d400c1489400b400a19a3400940080c8940074006058340054004068540030383400206890385400140000386 308 0x59738e4144544d745759438e5942cb297b2c354b145972cb40e2cb291aeb34eace4112cb5a9186654a94669aa95941864271864cea0e4e7a2740e18628818634b10b34810828b1865a26e26549946629a25946d44216e14ce90e4e192140e6ce28b94b3486c834b6cb2889480869060846c40866c60849045947146628e26548d45a272240e70e4e17a14ce78e42172128b80b35f71f34b70b29f81f04678605d71d04670605d79d08271c09b09b08109a5975576546146576175945544113d14ce48e4d149140e3ce28b24b34830834b30b2882480861460840840861c6084144082083082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x2 : Ex t174 9 [v40,u0,u1,u2,u3,u4,u5] :=
  certify c174 [⟨_,p174x0⟩] (unpack 6 0x14a119930c9119a3162813a50b950685401d06890589070c13a6150a0b960d0a0706070a058a03850386400080004001068c401c400e1489401b400c160c401a400a0c89401940080e0c401840060583401740040e1440030383401040020e18 308 0x4ee38e354b1442eb2e4d438e4d42081eebef294bd44ee20834e2081ecb6d28eb4e36c2084d10c3594ad4591ad14d40c334b0c340e00e40b00b34e0c31e80c32889882a89a81c80c34e271c594a945a2aa24d471c36071c40ea4e420a6034e71c1c87082a89682889481e871c9c394362671c9c370362696569a6a44d46db5a28e25948d44e26db34e6db42086040e84e3606db1c86c829f75f2887481df6db08374369e6db0836c369e75d61c61c69a6db61a6196186174d44945915515945544d149134e30e40b3cb40e3ce34b30b1c81882852452882481c5185083043080100083083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x3 : Ex t174 9 [v224,u0,u1,u2,u3,u4,u5] :=
  certify c174 [] (unpack 6 0x14a119930c9119a31628160c0e180e0c15281b34401d0d1813a60b960706070a058a03840386070c4023400e14894022400c150a4021400a0c89402040080d0a401f40060685401e4004058340030689400203834000401003854001068c 308 0x5ed492458ad852daed5d84925d82492edbae398b985ed2494522492ebb2c392b1246b2495e9145698a986a9aa95d8145467145512a12527a274521452cc1453891c938c1cc2c91455d56d56989986959955d86d844f6cf5128d250f8cf4526d22c994938c6cc3896c92cc94c9058c50476c79056c50478c75d871c6958956988985d571c45271c50f84f51285244f71c2c97093a07a03897892e071c10578511f71c10570511f79e04405d10471c05b05b5d85986956556986585d559545241250f4cf5124d244f40f2cc28c38934938c34c2c92891071871051051072071051851040c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x4 : Ex t174 9 [v225,u0,u1,u2,u3,u4,u5] :=
  certify c174 [] (unpack 6 0x14a119930c9119a31628160c0e180e0c13a50b9506850689058914a81ab40c98400003840385068c4029400e150a4028400c14894027400a0d0a402640080c894025400607064024400405834003070a40020383070c400140100386 308 0x5ac38e414a944ecaac59438e5942082acb6d354b545ac20840e2082aaaeb34eace42a2085a8104654a54668a685941044261044ce9ce4e69e640e1042a31043488883638a32881045976db6549546579575946db4116db4ce90e4d191140e6db2886c83638633488482a36db0848440a26db0846c40a286159469465781765481459769740e68e4d17914ce78e4116912887c834b68b34868828b7cb04478474668604468474678609d09c09b09b08269a5975576546146576175945544113d14ce48e4d149140e3ce28b24b34830834b30b2882480861460840840861c6084144082083082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x5 : Ex t174 8 [v39,v13,u1,u3,u4,u5] :=
  certify c174 [] (unpack 6 0x403414a140331993401440320c91403119a3152840300d1813a31a951aa50b93068503850383068905894002038214a81489150a0c980c890d0a058a0583401019b20d12 228 0x7de18668964985e65e7c91867c90c375e8207098097de0c36860c37596db7066c66990c35c84105c96095c86085c94105c54105c65865c55855c64105c34035d13515c33435d14100845840874100844100875873143cf3095493145543093cf3133cf3064863134923063cf3113cf3033833113913033cf31039030d3cf3103cf30d38d30c08b0891090882880892890881040861060851c50861c6085104083043080104083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x6 : Ex t174 9 [v13,u0,u2,u1,u3,u4,u5] :=
  certify c174 [⟨_,p174x5⟩] (unpack 6 0x14a119930c9119a315280d181628160c0e180e0c1b3214a8150a0d0a19b207060c98070c058a070a8000402f400e1a95402e400c1489402d400a1aa5402c40080c89402b40060685402a400405834001401d038505890383400240000386 308 0x5ad38e414ad44edaed59438e5942082adbae354b945ad20840e2082abb2c34eb0e42b2085a2145654a94662aa25941454211454cea4e4e1a6140e14528814834b10b34810828b14509b1040a614509b1450a61045a76db654a14667a275946d44256db4ce98e4e59a540e6ce28b90b3486c834b6cb2889085947146628e26548d45a271c40e70e4e17a14ce78e42171c28880835f71f34870829f81f04578505d71c04570505d79d08271c09b09b08109a5975576546146576175945544113d14ce48e4d149140e3ce28b24b34830834b30b2882480851c5084084085185084084082083082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x7 : Ex t174 9 [v39,u0,u2,u1,u3,u4,u5] :=
  certify c174 [⟨_,p174x5⟩] (unpack 6 0x14a119930c9119a3152840030589401d40010d1813a3160c0b930e0c06890685070a13a60b96070640100385070c068c03830386400080004002058a403a400e14894039400c150a4038400a0c89403740080d0a403640060583403540040d12 308 0x3ae24920fb0f2eeb2e38f24938f0c30aebef14fbcf3ae0c32090c30acb6d149b4922c0c338c69a44facf44cacc38f69a20669a2c99892c698620969a083683160a60143a430a069a4d7a57aa169aa976974e1a696e89a66e769a6db69a6e79a63a45d744f94f46496438f5d72225d72c98c92e28e22095d70a05d71438431608600835d755555f38f59644c78c44f78f38c5962095962c67462c974920659608358315c61c14360309c5966da61a5595966da59a5596184d74d75555964d54d44d34d238f34f44c40c44f40f38c34c2091c92c62862c92892061c6083043140100143103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x8 : Ex t174 9 [v226,u0,u2,u1,u3,u4,u5] :=
  certify c174 [] (unpack 6 0x14a119930c9119a315280d1840031628160c0e180e0c1b3213a60b960706070c068c03820386070a4040400e1489403f400c150a403e400a0c89403d40080d0a403c40060583403b40040685401d0589400103854000401003834002058a 308 0x5ed492458ad852daed5d84925d830c2edbae398b985ed30c45230c2ebb2c392b1246b30c5d5145698a98695a955d814544f145512a5250fa4f4521452cc14c3891c938c1cc2c914505b1c7a25145a1b1450651c75e66db6989d86a69e65d86d84646db5129525249644526d22c98c938c6cc3896c92cc8cc5d871c6958956988985d571c45271c50f84f51285244f71c2cc70c3a07a038c78c2e071c10578511f71c10570511f79e04405d10471c05b05b5d85986956556986585d559545241250f4cf5124d244f40f2cc28c38934938c34c2c92891071871051051072071051851040c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x9 : Ex t174 9 [v227,u0,u2,u1,u3,u4,u5] :=
  certify c174 [] (unpack 6 0x14a119930c9119a315280d18058913a30b930689068514a8150a0d0a19b20c98400003820383058a4046400e160c4045400c14894044400a0e0c404340080c894042400607064041400405834001401d070c0385070a400240100386 308 0x5ac38e414a944ecaac59438e5942082acb6d354b545ac20840e2082aaaeb34eace42a2085a1104654a54661a615941044201044cea0e4e0a2040e1042881083639e33489c82a310409b9db0a410409b11b0a49e75976db6549946579975946db4116db4ce94e4d195140e6db2a36db3489083639232886db5946946618a16548945a169a40e68e4e07a04ce78e42069a2887c834b68b34868828b7cb04478474569a04468474578509d09c09b09b08269a5975576546146576175945544113d14ce48e4d149140e3ce28b24b34830834b30b2882480851c5084084085185084084082083082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x10 : Ex t174 8 [v38,v12,u0,u3,u4,u5] :=
  certify c174 [] (unpack 6 0x403414a140331993404d4032403119a314a84011058a03860c9813a31b161b260b93070a07060383400203811528150a14890d180d0a0c8905890583401d19b10c91 228 0x79d14568864881d65d7881457880c371d7df6c87c879d0c36850c37190006c50056990c35c85555c96095c86085c95555c55555c65065c55055c65555c35435ce58e5c35835ce55530d58d30f55530d54d30f59608450408755508455508751431234d3084c83124d230834d31134d30540531141030534d30e34d3033c330e3ce30334d30c08b0891040882880892890881040861040851c50861c6085104083043080104083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x11 : Ex t174 9 [v12,u1,u2,u0,u3,u4,u5] :=
  certify c174 [⟨_,p174x10⟩] (unpack 6 0x14a119930c9119a314a80c98068c400040100386058a1628160c0e180e0c1ab11528150a0d180d0a19b10685058906898000404c400e1b16404b400c1489404a400a1b26404940080c894048400607064047400405830383400240010385 308 0x4ad28a310ad03edaed49028a4901041adbae250b904ad10430a1041abb2c24ab0a32b10449096555da9d550a9049d96530a9653dba5b3caa4a31b9651849442479072449041879650979170a19650979650a1924058a1805c96505896505ca280829240a79650a69650829244a25d75508d05628e24905d73205d73ca84a3e086030a5d71997d92445c42595d91847c449d61855079055d79d49061831b6183ca70a3db71b30a61818468425961924460419969908261809709708109649345355051055351349045030d2cd3ca38a3cd38d30a2ca187147244204247207184144082083082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x12 : Ex t174 9 [v38,u1,u2,u0,u3,u4,u5] :=
  certify c174 [⟨_,p174x10⟩] (unpack 6 0x14a1199319a314a807064003058a068c40100386401d40000c9813a3160c0b930e0c070a068913a50b95070c06850383038540018000400205894053400e150a4052400c14894051400a0d0a405040080c89404f40060583404e40040c91 308 0x3ad18620cb0c2edb2d38c18638c0c30adbae14cb8c3ad0c32060c30ac00014600622c0c338c96544facf44cacc38f9652069652c98892c688620996508394316aa2a143a030aa9654d7a17a5d965a579574dda285569d69199659169565599e79268a29239659269659238a23a05d744c84c46086038c5d721e5d72c67c62de7de2065d70985d71437431587580835d755555c38f59644c6cc44f6cf38c5962095962c66862c96892065960835831586581436430985964d74d75555964d54d44d34d238f34f44c40c44f40f38c34c2091c92c62862c92892061c6083043140100143103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x13 : Ex t174 9 [v228,u1,u2,u0,u3,u4,u5] :=
  certify c174 [] (unpack 6 0x14a119930c9119a314a80c9807064003068c1628160c0e180e0c1ab113a50b95070c0381038506894059400e150a4058400c14894057400a0d0a405640080c8940554006058340544004068540004010058a03864001401d038340020589 308 0x5ed3cf455ad552daed5d53cf5d530c2edbae395b955ed30c44f30c2ebb2c38fb0f46b30c5d5145698a98695a955d814544f145512a5250fa4f4521452cc14c3a81a838c18c2e814505b19b9e31459db14506318611c99c11e14511c15c11e9a65e46db6959556a49645d56db4626db50f8cf5228e244f6db2c984938c6cc3896c92cc84c5d871c6958156988185d571c45271c50f7cf5127d244f71c2cc70c38978938c78c2c971c04405d10471c05b05b5d85986956556986585d559545241250f4cf5124d244f40f2cc28c38934938c34c2c92891062061051051061c61051051040c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x14 : Ex t174 9 [v229,u1,u2,u0,u3,u4,u5] :=
  certify c174 [] (unpack 6 0x14a119930c9119a314a80c980706058a13a30b93070a1528150a0d180d0a19b14001038103830589405f400e160c405e400c1489405d400a0e0c405c40080c89405b40060685405a4004058340004010068c038606894002401d0385 308 0x5ac38e414a944ecaac59438e5942082acb6d354b545ac20840e2082aaaeb34eace42a208594104661a61654a545a110440e1044dfa1f4cea0e41f1042881083679a73489882a710409b99b0a310409b11b0a39a675a15a06010405a1047601455976db6549546579575946db4116db4ce90e4d191140e6db28b6db3488c834b8cb2886db5a169a6548946618a159469a41f69a4ce80e4df81f40e69a28878834b68b34868828b78b09d09c09b09b08269a5975576546146576175945544113d14ce48e4d149140e3ce28b24b34830834b30b2882480851c5084084085185084084082083082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p174x15 : Ex t174 10 (roots 63) :=
  certify c174 [⟨_,p174x1⟩,⟨_,p174x2⟩,⟨_,p174x3⟩,⟨_,p174x4⟩,⟨_,p174x6⟩,⟨_,p174x7⟩,⟨_,p174x8⟩,⟨_,p174x9⟩,⟨_,p174x11⟩,⟨_,p174x12⟩,⟨_,p174x13⟩,⟨_,p174x14⟩] (unpack 6 0x14a119930c9119a31628160c0e180e0c15280d180685800b800a8009800806890589400e14a81489400c150a400a0c980c8940080d0a400605834004070680078006800503838004070a058a800380028001038603858000070c068c 240 0x66c55551aa9a5ecaac65a55565a45142cb6d49ab5a66c45151545142aaeb495ad552a4516682cb71aa5a728a6865a2cb5262cb5d59d55e69e65152cb4232cb4917914a37a34112cb6580c371a95a71895865a0c35130c35d59155d39135150c34110d14a37634917514230c388b74b85e0c380b0cb7de75d65a1047186d871a6da6581045151045d35935d559551310441111148f20f49121140f10438b20b34910430b10b2892081c3003181104143103081000) (by decide +kernel)
theorem l174 : CClaim 63 t174 11 := fromTable 311659905670 (by decide +kernel) p174x15
open PEqualNP.CircuitLowerBounds

def graph : Sig := t174
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276682368 * 2 ^ 32 + 4269860992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def smallCircuit : Circuit := ⟨[
  ⟨.and,[0,1]⟩,
  ⟨.or,[0,1]⟩,
  ⟨.and,[4,5]⟩,
  ⟨.or,[4,5]⟩,
  ⟨.or,[3,8]⟩,
  ⟨.and,[3,9]⟩,
  ⟨.and,[7,10]⟩,
  ⟨.or,[6,11]⟩,
  ⟨.and,[2,12]⟩,
  ⟨.or,[2,12]⟩,
  ⟨.or,[13,14]⟩,
  ⟨.and,[15,16]⟩],17⟩

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

def lowRow (i : Fin 6) : Row := Fin.ofNat 128 (([6,5,3,3,9,9] : List Nat).getD i.val 0)
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

end PEqualNP.Outside.L_meta_12329

open PEqualNP.Outside.L_meta_12329 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_12329 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682368 * 2 ^ 32 + 4269860992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682368 * 2 ^ 32 + 4269860992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  obtain ⟨C,legal,bound,ev⟩ := h
  have fit : ∀ g ∈ C.gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal g hg
  obtain ⟨gs,o,mono,sz,correct⟩ := replaceShort p174x15 C.gates C.output fit ev
  refine ⟨⟨gs,o⟩,?_,sz.trans bound,correct⟩
  intro g hg
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using mono g hg
