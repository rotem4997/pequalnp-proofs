import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10698

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
    ws.all fun w => masked c.1 w == zero || c.2.2.contains (masked c.1 w)

def CutGood (T : Sig) (c : Cut) : Prop :=
  ∀ k ws, ws.Nodup → cutTest c k ws = true → Impossible true T k ws.toFinset

theorem cut_good {T d raw L} (s : Slice true raw T d L) (cs : List Choice)
    {pool} (hp : makePool true d raw cs = some pool) (afford : cs.length ≤ L) :
    CutGood T (d,L-cs.length,pool.map (masked d)) := by
  intro k ws nd checked
  simp only [cutTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
  apply poolCut_sound s cs hp nd
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true (by omega),List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases Bool.or_eq_true_iff.mp (checked.2 w hw) with hz | hm
  · simp [availableB,hz]
  · have mem := List.contains_iff_mem.mp hm
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp mem
    have yes : ((pool.map (masked d)).any fun z => z == masked d w) = true :=
      List.any_eq_true.mpr ⟨masked d v,List.mem_map_of_mem hv,beq_iff_eq.mpr eq⟩
    simp [availableB,yes]

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

-- Setting the missing vertices to zero gives the induced subgraph.
def goalAt (m : Nat) : Sig :=
  let x := fun i => if m.testBit i then input i else zero
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)

def fixes (q : Nat) : List Move :=
  ((List.range 7).filter fun i => !(q.testBit i)).map fun i =>
    (zero,input i,Fin.ofNat 128 (1 <<< i))

def domain (q : Nat) : Sig :=
  ((List.range 7).filter fun i => !(q.testBit i)).foldl (fun d i => d &&& neg (input i)) one

def tests (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun i =>
    let r := 1 <<< ((hints >>> (4*i)) % 16)
    (input i,Fin.ofNat 128 r,Fin.ofNat 128 (r ||| (1 <<< i)))

def Claim (m L : Nat) : Prop := Lower true (roots m) (goalAt m) L

def essTest (m hints : Nat) :=
  (properB (goalAt m) && checkEssential (goalAt m) (roots m) (tests m hints)) &&
    ((tests m hints).map Prod.fst == roots m)

theorem fromSearch {m k} (hints : Nat) (checked : essTest m hints = true)
    (no : Impossible true (goalAt m) k (roots m).toFinset) : Claim m (k+1) := by
  simp only [essTest,Bool.and_eq_true,beq_iff_eq] at checked
  have ok := checked.1.2
  apply lower_impossible (proper_of _ checked.1.1) (essential_plain ok).1 (essential_plain ok).2 _ no
  intro w hw
  apply essential_ok ok w
  rw [checked.2]
  exact List.mem_toFinset.mpr hw

def liftTest (m q a b e hints : Nat) :=
  ((checkLift (fixes q) (goalAt m) (roots m) (roots q) (goalAt q) (tests e hints) &&
    properB (goalAt m)) && properB (goalAt q)) &&
      decide (b ≤ a+((tests e hints).map Prod.fst).toFinset.card)

theorem fromLift {m q a} (b e hints : Nat) (lower : Claim q a)
    (ok : liftTest m q a b e hints = true) : Claim m b := by
  simp only [liftTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have lb := lift_ok ok.1.1.1 (proper_of _ ok.1.1.2) (proper_of _ ok.1.2) lower
  exact fun p bank hr ha => ok.2.trans (lb p bank hr ha)

def poolFor (q : Nat) (extra : Option Choice) : List Sig :=
  match extra with
  | none => roots q
  | some c => choiceVal c :: roots q

def ruleTest (m q L : Nat) (e : Option Choice) : Bool :=
  (((checkMap (fixes q) (roots q) (goalAt m) (roots q) (goalAt q) &&
    (movedWord (fixes q) (domain q) == one)) && properB (goalAt q)) &&
    (makePool true (domain q) (roots q) e.toList == some (poolFor q e))) &&
    decide (e.toList.length ≤ L)

def ruleFor (m : Nat) {q L} (lo : Claim q L) (e : Option Choice)
    (ok : ruleTest m q L e = true) : {c : Cut // CutGood (goalAt m) c} := by
  refine ⟨(domain q,L-e.toList.length,(poolFor q e).map (masked (domain q))),?_⟩
  simp only [ruleTest,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  exact cut_good (slice_correct ok.1.1.1.1 ok.1.1.1.2 (proper_of _ ok.1.1.2) lo)
    e.toList ok.1.2 ok.2

def signal0 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def signal1 : Sig := 0xeeee0000eeee0000eeee0000eeee
def signal2 : Sig := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def signal3 : Sig := 0xffaaffaa00000000ffaaffaa
def signal4 : Sig := 0xaa00aa00aa00aa00aa00aa00aa00aa
def signal5 : Sig := 0xcceecceecceecceecceecceecceeccee
def signal6 : Sig := 0xffffffffaaaaaaaaffffffffaaaaaaaa
def signal7 : Sig := 0xff00ff00aa00aa00ff00ff00aa00aa
def signal8 : Sig := 0xaaaaaaaa00000000aaaaaaaa
def signal9 : Sig := 0xcccccccceeeeeeeecccccccceeeeeeee
def signal10 : Sig := 0xffffffffff00ff00ffffffffff00ff00
def signal11 : Sig := 0xffffffffffffffffaaaaaaaaaaaaaaaa
def signal12 : Sig := 0xffffffffffffffffff00ff00ff00ff00
def signal13 : Sig := 0xffffffffffaaffaaffffffffffaaffaa
def signal14 : Sig := 0xffffffffffaaffaa
def signal15 : Sig := 0xffffffffffffffffffaaffaaffaaffaa
def signal16 : Sig := 0xffffffff00000000ffaaffaa
def signal17 : Sig := 0xffaaffaaffaaffaa
def signal18 : Sig := 0xffffffffffffffffffffffff00000000
def signal19 : Sig := 0xffffffffffffffffffffffffaaaaaaaa
def signal20 : Sig := 0xff00ff00ff00ff00ff00ff00aa00aa
def signal21 : Sig := 0xffffffffaaaaaaaa
def signal22 : Sig := 0xff00ff00ff00ff00aa00aa00aa00aa
def signal23 : Sig := 0xffffffff00000000aaaaaaaa
def signal24 : Sig := 0x55555555550055005555555555005500
def signal25 : Sig := 0xffffffffffffffffffffffffff00ff00
def signal26 : Sig := 0x55555555555555555555555555005500
def signal27 : Sig := 0xffffffffff00ff00
def signal28 : Sig := 0x55555555555555555500550055005500
def signal29 : Sig := 0xffffffff00000000ff00ff00
def signal30 : Sig := 0x55555555555555555555555500000000
def signal31 : Sig := 0xff00ff00ff00ff00ff00ff00000000
def signal32 : Sig := 0xffccffccffccffccffccffccffccffcc
def signal33 : Sig := 0xffffffffffffffffcccccccccccccccc
def signal34 : Sig := 0xffccffccffccffcc0000000000000000
def signal35 : Sig := 0xffffffccffffffccffff0000ffff0000
def signal36 : Sig := 0xffffffffffccffccffffffff00000000
def signal37 : Sig := 0xffffffffffffffffffccffccffccffcc
def signal38 : Sig := 0xffff0000ffff0000ffcc0000ffcc
def signal39 : Sig := 0xffffffff00000000ffccffcc
def signal40 : Sig := 0xffccffccffccffcc
def signal41 : Sig := 0x330033003300330000000000000000
def signal42 : Sig := 0xffffffffccccccccffffffffcccccccc
def signal43 : Sig := 0xffffffffcccccccc0000000000000000
def signal44 : Sig := 0xffffffffffccffccff00ff00ff00ff00
def signal45 : Sig := 0xffffffffffffccccffff0000ffff0000
def signal46 : Sig := 0xffffffffffffffffffffffffcccccccc
def signal47 : Sig := 0xff00ff00ff00ff00ff00ff00cc00cc
def signal48 : Sig := 0xffff0000ffff0000ffff0000cccc
def signal49 : Sig := 0xffffffffcccccccc
def signal50 : Sig := 0x333333330000000000000000
def signal51 : Sig := 0x33333333333333330000000000000000
def signal52 : Sig := 0xff00ff00ff00ff00cc00cc00cc00cc
def signal53 : Sig := 0xffff0000ffff0000cccc0000cccc
def signal54 : Sig := 0xffffffff00000000cccccccc
def signal55 : Sig := 0xff33ff33ff33ff33ff00ff00ff00ff00
def signal56 : Sig := 0xff33ff3300000000ff00ff00
def signal57 : Sig := 0xffffffff33333333ffffffff00000000
def signal58 : Sig := 0xff00ff0033003300ff00ff00000000
def signal59 : Sig := 0xffffff00ffffff00ffffff00ffffff00
def signal60 : Sig := 0xffffffffffffffffffff0000ffff0000
def signal61 : Sig := 0xffffff00ffffff000000000000000000
def signal62 : Sig := 0xffffffccffffffcccccccccccccccccc
def signal63 : Sig := 0xffffffffffffff00ffffffff00000000
def signal64 : Sig := 0xffffffffffffffffffffff00ffffff00
def signal65 : Sig := 0x33333333333333333333330033333300
def signal66 : Sig := 0xffffffff00000000ffffff00
def signal67 : Sig := 0xffffff00ffffff00
def signal68 : Sig := 0xff000000ff0000000000000000
def signal69 : Sig := 0x33333333333333333300330033003300
def signal70 : Sig := 0xff00ff00ff00ff0000000000000000
def signal71 : Sig := 0xffff0000ffff0000ff000000ff00
def signal72 : Sig := 0xccffccffccffccffcccccccccccccccc
def signal73 : Sig := 0xccff0000ccff0000cccc0000cccc
def signal74 : Sig := 0xffff00ffffff00ffffff0000ffff0000
def signal75 : Sig := 0x33330033333300333333000033330000
def signal76 : Sig := 0xffffffffffff0000ffffffffffff0000
def signal77 : Sig := 0xffffffffffff00000000000000000000
def signal78 : Sig := 0xffffffffffffcccccccccccccccccccc
def signal79 : Sig := 0xffffffffffffff00ff00ff00ff00ff00
def signal80 : Sig := 0xffffffffffffffffffffffffffff0000
def signal81 : Sig := 0x33333333333333333333333333330000
def signal82 : Sig := 0xff00ff00ff00ff00ff00ff00ff0000
def signal83 : Sig := 0xffffffffffff0000
def signal84 : Sig := 0xffff0000000000000000
def signal85 : Sig := 0x33333333333333333333000033330000
def signal86 : Sig := 0xff00ff00ff00ff00ff000000ff0000
def signal87 : Sig := 0xffff0000ffff0000000000000000
def signal88 : Sig := 0xffffffff00000000ffff0000
def signal89 : Sig := 0xff00ffffff00ffffff00ff00ff00ff00
def signal90 : Sig := 0xff00ffff00000000ff00ff00
def signal91 : Sig := 0xffffffff0000ffffffffffff00000000
def signal92 : Sig := 0xff00ff000000ff00ff00ff00000000
def signal93 : Sig := 0x33333333333333333333333300000000
def signal94 : Sig := 0xffff0000ffff0000ffff00000000
def signal95 : Sig := 0xffffffff0000000000000000
def signal96 : Sig := 0xccccccccffffffffcccccccccccccccc
def signal97 : Sig := 0xcccc0000ffff0000cccc0000cccc
def signal98 : Sig := 0xffff0000ffffffffffff0000ffff0000
def signal99 : Sig := 0x33330000333333333333000033330000
def signal100 : Sig := 0xffffffffffffff00ffffffffffffff00
def signal101 : Sig := 0xffffffffffffffffffffffffffffff00
def signal102 : Sig := 0x55555555555555555555555555555500
def signal103 : Sig := 0x33333333333333333333333333333300
def signal104 : Sig := 0xffff0000ffff0000ffff0000ff00
def signal105 : Sig := 0xffff0000ffffffffffff0000ffffff00
def signal106 : Sig := 0x33330000333333333333000033333300
def signal107 : Sig := 0xffff00ffffff00ffffff00ffffff0000
def signal108 : Sig := 0x33330033333300333333003333330000

def cuts27 : Cuts (goalAt 27) := []
def state27_0 : List Sig := roots 27
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude27_0 : Impossible true (goalAt 27) 3 state27_0.toFinset :=
  node_ok cuts27 [] 0x890091051200890012009101910091008b008901890089040900110c09040900090009008908110409040b05090409 (by decide +kernel)
theorem lower27 : Claim 27 4 :=
  fromSearch 67 (by decide +kernel) exclude27_0

def cuts41 : Cuts (goalAt 41) := []
def state41_0 : List Sig := roots 41
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude41_0 : Impossible true (goalAt 41) 3 state41_0.toFinset :=
  node_ok cuts41 [] 0x4280089008900a1102800a104281028042800a10089008900a10409040904281021002100a1102100a1042804090409008910210009102804090009008904090089102810211021 (by decide +kernel)
theorem lower41 : Claim 41 4 :=
  fromSearch 3 (by decide +kernel) exclude41_0

def cuts51 : Cuts (goalAt 51) := []
def state51_0 : List Sig := roots 51
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude51_0 : Impossible true (goalAt 51) 3 state51_0.toFinset :=
  node_ok cuts51 [] 0x9100a111120091081200a1181208120012009101910091081100211811081100110011009101120811081211210811 (by decide +kernel)
theorem lower51 : Claim 51 4 :=
  fromSearch 68 (by decide +kernel) exclude51_0

theorem lower57 : Claim 57 5 :=
  fromLift 5 16 3 lower41 (by decide +kernel)

def rule59_0 : {c : Cut // CutGood (goalAt 59) c} :=
  ruleFor 59 lower27 none (by decide +kernel)
def rule59_1 : {c : Cut // CutGood (goalAt 59) c} :=
  ruleFor 59 lower41 none (by decide +kernel)
def rule59_2 : {c : Cut // CutGood (goalAt 59) c} :=
  ruleFor 59 lower51 none (by decide +kernel)
def rule59_3 : {c : Cut // CutGood (goalAt 59) c} :=
  ruleFor 59 lower57 none (by decide +kernel)
def cuts59 : Cuts (goalAt 59) := [rule59_0,rule59_1,rule59_2,rule59_3]
def state59_4 : List Sig := [signal3,input 0,input 1,input 3,input 4]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude59_4 : Impossible true (goalAt 59) 4 state59_4.toFinset :=
  node_ok cuts59 [] 0x890091051a00890012009101910091008b008901890089040901120c0904090089040900890c110409040b05090409009101120091011200890028008900a10c1a08120c1a08120409081104090021 (by decide +kernel)
def state59_2 : List Sig := [signal1,input 0,signal0,input 3,input 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude59_2 : Impossible true (goalAt 59) 4 state59_2.toFinset :=
  node_ok cuts59 [] 0x8900a10428008900120428101200120089001a008900120509012100a10509008901090089112100110091111200a10091008905120089009140010509009105090111 (by decide +kernel)
def state59_8 : List Sig := [signal7,input 0,input 1,input 4,input 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude59_8 : Impossible true (goalAt 59) 4 state59_8.toFinset :=
  node_ok cuts59 [] 0x9100a108280091081200a101a108120012009101910091000910211811000900090112080900090009000b010900090089002800a10089008901120091008900890189008b00890811000900890009 (by decide +kernel)
def state59_10 : List Sig := [input 0,signal9,input 3,input 4,input 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude59_10 : Impossible true (goalAt 59) 4 state59_10.toFinset :=
  node_ok cuts59 [] 0x9100a311120091008900a3042800890089009105120089081204281812081200910012009140010089081a008908120509002110210509050901110091050900890109008910210409040905090812 (by decide +kernel)
def state59_6 : List Sig := [input 0,signal5,input 3,input 4,input 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude59_6 : Impossible true (goalAt 59) 4 state59_6.toFinset :=
  node_ok cuts59 [] 0x9100a111120091008b00a10428008b008b00910512008b08120428181208120091001200914001008b081a008900890409012100a10409040901110c09040900090009040911210409040b05090409 (by decide +kernel)
def state59_9 : List Sig := [signal8,input 0,input 1,input 3,input 4,input 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude59_9 : Impossible true (goalAt 59) 5 state59_9.toFinset :=
  node_ok cuts59 [⟨state59_10,exclude59_10⟩] 0x910428111200910089002804280089008900910512008908120428181208120012009101910091008b00890189008900211021042800910112009101120089102800891021102108121121081200a10091011200910112008910280089102840030812800008120409 (by decide +kernel)
def state59_5 : List Sig := [signal4,input 0,input 1,input 3,input 4,input 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude59_5 : Impossible true (goalAt 59) 5 state59_5.toFinset :=
  node_ok cuts59 [⟨state59_6,exclude59_6⟩] 0x9100a111120091002800a1042800a1011a009105120091081200a11812081200120091019100910812081a0c1208120409042800a10409040901120c0904090009040910280409040b0509040900a1042800a104280091011200910112008940030812800008120811 (by decide +kernel)
def state59_3 : List Sig := [input 0,input 1,input 3,signal2,input 4,input 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude59_3 : Impossible true (goalAt 59) 5 state59_3.toFinset :=
  node_ok cuts59 [⟨state59_4,exclude59_4⟩] 0x9100a11112009100a1800000a140000091011200910112008900a10428008900890091051a00891028081200a118120812001200910191009108120c1a0c1a0812008b0089018900890409042800a10409040901120c0904090811008904090c110409040b05090409 (by decide +kernel)
def state59_7 : List Sig := [input 0,input 1,input 3,input 4,input 5,signal6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude59_7 : Impossible true (goalAt 59) 5 state59_7.toFinset :=
  node_ok cuts59 [⟨state59_8,exclude59_8⟩] 0x4280112009100910112009100a1113200918000008900894002008900a11028008900890091051200890812183218320812081200a101a108120012009101910091008b008901890089040900a110211811009101120091011200891028008910211021081211210812 (by decide +kernel)
def state59_11 : List Sig := [input 0,input 1,input 3,input 4,input 5,signal10]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude59_11 : Impossible true (goalAt 59) 5 state59_11.toFinset :=
  node_ok cuts59 [] 0xa10091051a051a0091009104280c2800910089042810284000051a0091051a009108120c1a0c1a08120812042805280812001200910191009108120c1a0c1a081208110409040908110409102110210409040900110c09040908110409040908110409040b05090409 (by decide +kernel)
def state59_1 : List Sig := [input 0,signal0,input 3,input 4,input 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude59_1 : Impossible true (goalAt 59) 5 state59_1.toFinset :=
  node_ok cuts59 [⟨state59_2,exclude59_2⟩] 0xc380091009100a1113200a10c381132111200a10091009104280089008900a1102800a104281028042800a100890089051a00890089009118380091051a1838051200910089008900a10812081204281832042800a11832181204280812081200914001009180000812001200910812009140014001400100890812008910280c1a081a00890c1a008910280812081200a10509050904281121012100a1112100a1042805090509009105090509011240010111009140010091011205090509008911210089102805090109008905090089102811211121400340030409 (by decide +kernel)
def state59_0 : List Sig := roots 59
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude59_0 : Impossible true (goalAt 59) 6 state59_0.toFinset :=
  node_ok cuts59 [⟨state59_1,exclude59_1⟩,⟨state59_3,exclude59_3⟩,⟨state59_5,exclude59_5⟩,⟨state59_7,exclude59_7⟩,⟨state59_9,exclude59_9⟩,⟨state59_11,exclude59_11⟩] 0x40010c3800910091400100a1113200a140010c3811321112400100a1009100914000042800890089400200a1102800a18005042810280428400000a1008900894001051a0089008940010091183800914001051a183805124001009100890089400301a308120812400300a1183200a1400301a318321812400300a10812081240030112400100124003009108120091400301120812019140030091400300914003018b0812008b400300890c1a00894003018b0c1a01894003008908120089400000a1040904098004042810210021800300a1102118114000042804090409400100910409040940010112081100114001009108110c0940010112040904094002008908110009800210280409000980010089040900894002102808110811400340030409040940030812050b040b40038000050b05094003081204090409 (by decide +kernel)
theorem lower59 : Claim 59 7 :=
  fromSearch 67 (by decide +kernel) exclude59_0

def cuts73 : Cuts (goalAt 73) := []
def state73_0 : List Sig := roots 73
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude73_0 : Impossible true (goalAt 73) 3 state73_0.toFinset :=
  node_ok cuts73 [] 0x4480089008900c1204800c104482048044800c10089008900c10409040904482041004100c1204100c1044804090409008920410009204804090009008904090089204820412041 (by decide +kernel)
theorem lower73 : Claim 73 4 :=
  fromSearch 3 (by decide +kernel) exclude73_0

theorem lower75 : Claim 75 5 :=
  fromLift 5 2 99 lower73 (by decide +kernel)

def cuts81 : Cuts (goalAt 81) := []
def state81_0 : List Sig := roots 81
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude81_0 : Impossible true (goalAt 81) 3 state81_0.toFinset :=
  node_ok cuts81 [] 0x8500091009100c1205000c108502050085000c10091009100c10811081108502041004100c1204100c1085008110811009120410011205008110011009108110091205020412041 (by decide +kernel)
theorem lower81 : Claim 81 4 :=
  fromSearch 4 (by decide +kernel) exclude81_0

def cuts82 : Cuts (goalAt 82) := []
def state82_0 : List Sig := roots 82
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude82_0 : Impossible true (goalAt 82) 3 state82_0.toFinset :=
  node_ok cuts82 [] 0x85001120112014220500142085020500850014201120112014208120812085020420042014220420142085008120812011220420012205008120012011208120112205020422042 (by decide +kernel)
theorem lower82 : Claim 82 4 :=
  fromSearch 16842816 (by decide +kernel) exclude82_0

theorem lower83 : Claim 83 5 :=
  fromLift 5 2 68 lower81 (by decide +kernel)

theorem lower89 : Claim 89 5 :=
  fromLift 5 16 3 lower73 (by decide +kernel)

theorem lower90 : Claim 90 5 :=
  fromLift 5 8 16867392 lower82 (by decide +kernel)

def rule91_0 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower75 none (by decide +kernel)
def rule91_1 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower83 none (by decide +kernel)
def rule91_2 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower89 none (by decide +kernel)
def rule91_3 : {c : Cut // CutGood (goalAt 91) c} :=
  ruleFor 91 lower90 none (by decide +kernel)
def cuts91 : Cuts (goalAt 91) := [rule91_0,rule91_1,rule91_2,rule91_3]
def state91_0 : List Sig := roots 91
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude91_0 : Impossible true (goalAt 91) 6 state91_0.toFinset :=
  node_ok cuts91 [] 0x4000085000910091400000c1205000c14000085020500c48400000c1009100914001044800890089400100c1204800c14001044820480542400100c1008900894000051a0089008940000091400000914000051a4000051240000091008900894002014208120812400200c1204200c140020142204201c1400200c10812081240000112204200124000009108120091400001120812019140000091204200914001018b0812008b400100890c1a00894001018b0c1a01894001008908120089400300c1040904094003014220410041400300c1204100c14003014204090409400000910409040940000112081100114000009108110c0940000112040904094001008908110009400120480409000940010089040900894001204808110811400240020409040940020812050b040b40024003050b05094002081204090409 (by decide +kernel)
theorem lower91 : Claim 91 7 :=
  fromSearch 67 (by decide +kernel) exclude91_0

def cuts97 : Cuts (goalAt 97) := []
def state97_0 : List Sig := roots 97
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude97_0 : Impossible true (goalAt 97) 3 state97_0.toFinset :=
  node_ok cuts97 [] 0x106000a100a100c1206000c110602060106000c100a100a100c11021102110602041004100c1204100c110601021102100a12041002120601021002100a1102100a1206020412041 (by decide +kernel)
theorem lower97 : Claim 97 4 :=
  fromSearch 5 (by decide +kernel) exclude97_0

theorem lower99 : Claim 99 5 :=
  fromLift 5 2 101 lower97 (by decide +kernel)

def cuts104 : Cuts (goalAt 104) := []
def state104_0 : List Sig := roots 104
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude104_0 : Impossible true (goalAt 104) 3 state104_0.toFinset :=
  node_ok cuts104 [] 0x106004280428044820600448106020601060044804280428044810281028106020480048044820480448106010281028042820480028206010280028042810280428206020482048 (by decide +kernel)
theorem lower104 : Claim 104 4 :=
  fromSearch 53497856 (by decide +kernel) exclude104_0

def rule105_0 : {c : Cut // CutGood (goalAt 105) c} :=
  ruleFor 105 lower41 none (by decide +kernel)
def rule105_1 : {c : Cut // CutGood (goalAt 105) c} :=
  ruleFor 105 lower73 none (by decide +kernel)
def rule105_2 : {c : Cut // CutGood (goalAt 105) c} :=
  ruleFor 105 lower97 none (by decide +kernel)
def rule105_3 : {c : Cut // CutGood (goalAt 105) c} :=
  ruleFor 105 lower104 none (by decide +kernel)
def cuts105 : Cuts (goalAt 105) := [rule105_0,rule105_1,rule105_2,rule105_3]
def state105_9 : List Sig := [signal14,input 0,input 3,input 5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_9 : Impossible true (goalAt 105) 3 state105_9.toFinset :=
  node_ok cuts105 [] 0x8900a1042800890409102100a10409008904090089102100a1006000a100c100890048008900c10409004104090041 (by decide +kernel)
def state105_12 : List Sig := [signal16,input 0,input 3,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_12 : Impossible true (goalAt 105) 3 state105_12.toFinset :=
  node_ok cuts105 [] 0x8900c1044800890409204100c10409008904090089002100a1006000c100a100890028008900a10409002104090021 (by decide +kernel)
def state105_21 : List Sig := [signal20,input 0,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_21 : Impossible true (goalAt 105) 3 state105_21.toFinset :=
  node_ok cuts105 [] 0xa100c1106000a10009204100c100090009102100a100090089004800c100890089002800a100891021000900890009 (by decide +kernel)
def state105_34 : List Sig := [signal26,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_34 : Impossible true (goalAt 105) 3 state105_34.toFinset :=
  node_ok cuts105 [] 0x2100411060002100090041044800090009002104280009040900412041040904090021102104091021000904090009 (by decide +kernel)
def state105_31 : List Sig := [input 0,signal10,signal12,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_31 : Impossible true (goalAt 105) 3 state105_31.toFinset :=
  node_ok cuts105 [] 0x42810280428400100a100a1042840000089008910284000040910211021040910210409040910212029040904092028 (by decide +kernel)
def state105_16 : List Sig := [input 3,signal6,signal11,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_16 : Impossible true (goalAt 105) 3 state105_16.toFinset :=
  node_ok cuts105 [] 0xa1102100a1400100a1202100a140000409040910214000008900a11028008910280089008910212029008900892021 (by decide +kernel)
def state105_5 : List Sig := [signal2,input 5,signal11,signal12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_5 : Impossible true (goalAt 105) 3 state105_5.toFinset :=
  node_ok cuts105 [] 0x8904090089400200a10089042800890428040900a10409008920090089400004092009040940002009202900a12009 (by decide +kernel)
def state105_3 : List Sig := [signal2,signal6,signal10,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_3 : Impossible true (goalAt 105) 3 state105_3.toFinset :=
  node_ok cuts105 [] 0x8900c1044800890409044800c1040900890409008940021009104900c1100900891009008940010409100904094001 (by decide +kernel)
def state105_13 : List Sig := [signal17,input 0,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_13 : Impossible true (goalAt 105) 4 state105_13.toFinset :=
  node_ok cuts105 [] 0xa10060106000a10089004820480089008900a10428008904090041204104090409042800a10409008904090089204100c100a1206000a1206000891028008920480409102104092041 (by decide +kernel)
def state105_22 : List Sig := [signal21,input 0,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_22 : Impossible true (goalAt 105) 4 state105_22.toFinset :=
  node_ok cuts105 [] 0xa10448206000a10089004804480089008900a110280089102100412041102100a1102100a12041008910280089102100c100a1042800a1206000892048008920480409040910212041 (by decide +kernel)
def state105_35 : List Sig := [signal27,input 0,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_35 : Impossible true (goalAt 105) 4 state105_35.toFinset :=
  node_ok cuts105 [] 0x42800c120600428102800c12048102804281028042820480409004100c1040904091021102104091021040904091021044800a100a10428206000890089102820480409204104092041 (by decide +kernel)
def state105_10 : List Sig := [signal3,input 0,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_10 : Impossible true (goalAt 105) 4 state105_10.toFinset :=
  node_ok cuts105 [] 0x6000c1106000c1008900c10448008900890028102800890409044800c104090409002110210409008904090089102100c1106000c1106000a100891028008910280409102104091021 (by decide +kernel)
def state105_27 : List Sig := [signal23,input 0,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_27 : Impossible true (goalAt 105) 4 state105_27.toFinset :=
  node_ok cuts105 [] 0x42800c110600428008900c12048008900890028042800891021204100c110210021002110210428008910280089102100c1044800c1106000a100891028008910280409040920411021 (by decide +kernel)
def state105_39 : List Sig := [signal29,input 0,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_39 : Impossible true (goalAt 105) 4 state105_39.toFinset :=
  node_ok cuts105 [] 0xa10448106000a11028204804481028002800a1102800a104092041204104090409002100a10409102104090409102100c100c104481060042800890089204810280409102104091021 (by decide +kernel)
def state105_18 : List Sig := [signal7,input 0,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_18 : Impossible true (goalAt 105) 4 state105_18.toFinset :=
  node_ok cuts105 [] 0xa100c1106000a1004800c1044800c1002800a1042800a10409044800c104090409102100a10409000900090409102100c1044800c1044800a1042800a1042800891021040910210409 (by decide +kernel)
def state105_25 : List Sig := [signal22,input 0,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_25 : Impossible true (goalAt 105) 4 state105_25.toFinset :=
  node_ok cuts105 [] 0xa100c1206000a1102800c104481028002800a1042800a10409204100c104090409042800a10409000900090409102800c1044800c1044800a1042800a1042800891021040920410409 (by decide +kernel)
def state105_42 : List Sig := [signal31,input 0,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_42 : Impossible true (goalAt 105) 4 state105_42.toFinset :=
  node_ok cuts105 [] 0x4280448106004280089004804480089008900280428008904092041204104090409102110210409000900090089102100c100c11060044800a100a12060042810281021040910210409 (by decide +kernel)
def state105_29 : List Sig := [signal24,input 0,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_29 : Impossible true (goalAt 105) 4 state105_29.toFinset :=
  node_ok cuts105 [] 0xa100c1106000a1008900c104480089008900a1042800890041004100c104480021002100a104280009000900891028044800c1044800c1042800a1042800a110280089102800890409 (by decide +kernel)
def state105_37 : List Sig := [signal28,input 0,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_37 : Impossible true (goalAt 105) 4 state105_37.toFinset :=
  node_ok cuts105 [] 0xa100c1206000a1008900c104480089008900a1042800891021004100c110210021002100a104280009000900891021044800c1044800c1042800a1042800a110280089204800890409 (by decide +kernel)
def state105_41 : List Sig := [signal30,input 0,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_41 : Impossible true (goalAt 105) 4 state105_41.toFinset :=
  node_ok cuts105 [] 0xa100c1106000a1008900c120480089008900a1102800890409004100c104090409002100a104090009000900891028044800c1106000c1042800a1206000a110280089102800891021 (by decide +kernel)
def state105_8 : List Sig := [input 0,input 3,input 5,signal13,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_8 : Impossible true (goalAt 105) 4 state105_8.toFinset :=
  node_ok cuts105 [⟨state105_9,exclude105_9⟩] 0xc1800000c1400000a100c1106000a12060008900c1044800892048008900a1042800890409044800c1040920410409102100a104090089040900891021 (by decide +kernel)
def state105_11 : List Sig := [input 0,input 3,input 5,input 6,signal15]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_11 : Impossible true (goalAt 105) 4 state105_11.toFinset :=
  node_ok cuts105 [⟨state105_12,exclude105_12⟩] 0x1060800000a100a1400100a100c1206000a11028008900c104480089008900a10428008910210409204100c104090409042800a104090089040900892041 (by decide +kernel)
def state105_20 : List Sig := [input 0,input 3,input 5,input 6,signal19]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_20 : Impossible true (goalAt 105) 4 state105_20.toFinset :=
  node_ok cuts105 [⟨state105_21,exclude105_21⟩] 0x448042800a100c1106000a18000008900894002008900c120480089008900a11028008904091021204100c1102100a1102100a120410089102800891021 (by decide +kernel)
def state105_33 : List Sig := [input 0,input 3,input 5,input 6,signal25]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_33 : Impossible true (goalAt 105) 4 state105_33.toFinset :=
  node_ok cuts105 [⟨state105_34,exclude105_34⟩] 0xc100a104280448106004280089102820480448102804281028042820488000040904094003040920412041040904091021102104091021040904091021 (by decide +kernel)
def state105_24 : List Sig := [input 0,input 3,input 5,signal11,signal12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_24 : Impossible true (goalAt 105) 4 state105_24.toFinset :=
  node_ok cuts105 [⟨state105_5,exclude105_5⟩] 0xc1044800c1400200a10428042800a1042800a100a1042800890448204804484002042800a1042800a100c1204100c14003040900a1042800a104282009200980002041 (by decide +kernel)
def state105_26 : List Sig := [input 0,input 3,input 5,signal11,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_26 : Impossible true (goalAt 105) 4 state105_26.toFinset :=
  node_ok cuts105 [⟨state105_16,exclude105_16⟩] 0xc1044800c1400100a1106020601060400100891028102800891028008900891028008910281028008900c1204100c14003040920212021800020410089102800891028 (by decide +kernel)
def state105_38 : List Sig := [input 0,input 3,input 5,signal12,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_38 : Impossible true (goalAt 105) 4 state105_38.toFinset :=
  node_ok cuts105 [⟨state105_31,exclude105_31⟩] 0xc100c10448400100a110602060106040010448204804484002008920282028800020480409102110210409102104090409102104091021102104091021040904091021 (by decide +kernel)
def state105_17 : List Sig := [input 0,input 3,signal6,signal10,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_17 : Impossible true (goalAt 105) 4 state105_17.toFinset :=
  node_ok cuts105 [⟨state105_3,exclude105_3⟩] 0xa100c1044800a10428044800c1042800a1042800a14002102800c104481028008904281028042840021021044800c1102100a1102100a1400304091009100980001021 (by decide +kernel)
def state105_19 : List Sig := [input 0,input 3,signal6,input 6,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_19 : Impossible true (goalAt 105) 4 state105_19.toFinset :=
  node_ok cuts105 [⟨state105_16,exclude105_16⟩] 0xc100a1042800a140001060206010604000008900a1102800890089204820480089204800890089204800a1102100a14003102110418000102104090089102800891021 (by decide +kernel)
def state105_32 : List Sig := [input 0,input 3,signal10,input 6,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_32 : Impossible true (goalAt 105) 4 state105_32.toFinset :=
  node_ok cuts105 [⟨state105_31,exclude105_31⟩] 0xc100a100a10428400010602060106040000428102804284002102810488000102800890409102110210409040920412041040920410409040920411021040904091021 (by decide +kernel)
def state105_6 : List Sig := [input 0,signal2,input 5,signal10,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_6 : Impossible true (goalAt 105) 4 state105_6.toFinset :=
  node_ok cuts105 [⟨state105_3,exclude105_3⟩] 0x8900c104480089042800c11060042800a11028106000c11028008910280089400104281028042840010409044800c10409008904090089400304090421800004091021 (by decide +kernel)
def state105_7 : List Sig := [input 0,signal2,input 5,input 6,signal12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_7 : Impossible true (goalAt 105) 4 state105_7.toFinset :=
  node_ok cuts105 [⟨state105_5,exclude105_5⟩] 0xc100a100890428008900a10448206000a10089102800894000044820480448400000a1206000a12048008904090089400304090441800004090409042800a104091021 (by decide +kernel)
def state105_30 : List Sig := [input 0,input 5,signal10,input 6,signal12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_30 : Impossible true (goalAt 105) 4 state105_30.toFinset :=
  node_ok cuts105 [⟨state105_31,exclude105_31⟩] 0xc1008900891028400004482048044840001028042804284001042804488000042800a11021040904091021040920412041040920410409040920410409102110210409 (by decide +kernel)
def state105_2 : List Sig := [input 3,signal2,input 5,signal6,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_2 : Impossible true (goalAt 105) 4 state105_2.toFinset :=
  node_ok cuts105 [⟨state105_3,exclude105_3⟩] 0x409044800c1040900a100c1106000a104281021106000c11021040910210409400100a1102100a14001008900c1044800890409008900894002008900a1800000891028 (by decide +kernel)
def state105_4 : List Sig := [input 3,signal2,input 5,input 6,signal11]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_4 : Impossible true (goalAt 105) 4 state105_4.toFinset :=
  node_ok cuts105 [⟨state105_5,exclude105_5⟩] 0x4480428040900a1040900a100c1206000a1040910210409400000c1204100c1400000a1206000a120410409008900894002008900c180000089008900a1042800891028 (by decide +kernel)
def state105_15 : List Sig := [input 3,input 5,signal6,input 6,signal11]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_15 : Impossible true (goalAt 105) 4 state105_15.toFinset :=
  node_ok cuts105 [⟨state105_16,exclude105_16⟩] 0x448040904091021400000c1204100c14000102100a100a1400100a100c1800000a104281028008900891021008900c1204800892048008900892041008900a110280089 (by decide +kernel)
def state105_1 : List Sig := [input 0,input 3,signal2,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_1 : Impossible true (goalAt 105) 5 state105_1.toFinset :=
  node_ok cuts105 [⟨state105_2,exclude105_2⟩,⟨state105_4,exclude105_4⟩,⟨state105_6,exclude105_6⟩,⟨state105_7,exclude105_7⟩,⟨state105_8,exclude105_8⟩,⟨state105_10,exclude105_10⟩,⟨state105_11,exclude105_11⟩,⟨state105_13,exclude105_13⟩] 0x106000a100a100c1206000c110602060106000c100a100a100c1400000c110608007106000c1800600c110604000106000a1400100a120608005206000a1800400a120604001206004480089008900c1400200c104488003044800c10089008904280089008900a1400200a104288002042800a10089008940024003102800c10409040904484003044800c1800100c104480409040900a10409040904284003042800a1800000a1042804090409400240021021008940020089400304090409400240024002 (by decide +kernel)
def state105_14 : List Sig := [input 0,input 3,input 5,signal6,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_14 : Impossible true (goalAt 105) 5 state105_14.toFinset :=
  node_ok cuts105 [⟨state105_2,exclude105_2⟩,⟨state105_15,exclude105_15⟩,⟨state105_17,exclude105_17⟩,⟨state105_8,exclude105_8⟩,⟨state105_18,exclude105_18⟩,⟨state105_19,exclude105_19⟩,⟨state105_20,exclude105_20⟩,⟨state105_22,exclude105_22⟩] 0xc1400000c104488007044800c1800600c1044840000448106000a100a100c1400100c110608005106000c100a100a140014003042804480089008900c1204800c104482048044800c10089008980042048204840020089008980030089008940022048204840010089008900a1102800a180021028102800a10089008900c11021102104484003044800c1800100c104481021102140014001040900a1400100a1400310211021400140014001008910210089102840031028008980000089102810211021 (by decide +kernel)
def state105_28 : List Sig := [input 0,input 3,input 5,signal10,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_28 : Impossible true (goalAt 105) 5 state105_28.toFinset :=
  node_ok cuts105 [⟨state105_6,exclude105_6⟩,⟨state105_17,exclude105_17⟩,⟨state105_8,exclude105_8⟩,⟨state105_29,exclude105_29⟩,⟨state105_30,exclude105_30⟩,⟨state105_32,exclude105_32⟩,⟨state105_33,exclude105_33⟩,⟨state105_35,exclude105_35⟩] 0x4484000044800c1800700c104488006044800c1400000c110600428042800c1400100c110608005106000c1042804284001400200a104481028102800c1400200c104488004044800c11028102840014001008904284001042840021028102840014001400100c10409040904482041004100c1204100c1044804090409800320412041400304090409800204090409400320412041400104090409042810211021800110211021042804090409400210211021102804090409800004090409102810211021 (by decide +kernel)
def state105_23 : List Sig := [input 0,input 3,input 5,input 6,signal11]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_23 : Impossible true (goalAt 105) 5 state105_23.toFinset :=
  node_ok cuts105 [⟨state105_4,exclude105_4⟩,⟨state105_15,exclude105_15⟩,⟨state105_24,exclude105_24⟩,⟨state105_11,exclude105_11⟩,⟨state105_25,exclude105_25⟩,⟨state105_26,exclude105_26⟩,⟨state105_20,exclude105_20⟩,⟨state105_27,exclude105_27⟩] 0x400040030448800704280428400100a100a1800600a100a1400104280428400000a100a100c1206000c180052060206000c100a100a180041028102840020089008980030089008940021028102840000089008900c1204800c180022048204800c10089008904280089008900a1102800a104281028042800a10089008940004000040900c1400000c140032041204140004000400000a1204100a104284003042800a1800100a1042820410428008920410089102840031028008980000089102820411028 (by decide +kernel)
def state105_36 : List Sig := [input 0,input 3,input 5,input 6,signal12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_36 : Impossible true (goalAt 105) 5 state105_36.toFinset :=
  node_ok cuts105 [⟨state105_7,exclude105_7⟩,⟨state105_24,exclude105_24⟩,⟨state105_11,exclude105_11⟩,⟨state105_37,exclude105_37⟩,⟨state105_30,exclude105_30⟩,⟨state105_38,exclude105_38⟩,⟨state105_33,exclude105_33⟩,⟨state105_39,exclude105_39⟩] 0x4000400200c1800700a100a1400104280428800604280428400100a100a1400000a100a1044820600448800520602060044800a100a140004000008904484000044840022048204840004000400004282048042800a1400200a104288004042800a1204800a180031021102140030409040980020409040940031021102140000409040904482041204180012041204104480409040900a10409040904281021002100a1102100a1042804090409400210211021204804090409800004090409204810211021 (by decide +kernel)
def state105_40 : List Sig := [input 0,input 3,input 5,input 6,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_40 : Impossible true (goalAt 105) 5 state105_40.toFinset :=
  node_ok cuts105 [⟨state105_19,exclude105_19⟩,⟨state105_26,exclude105_26⟩,⟨state105_20,exclude105_20⟩,⟨state105_41,exclude105_41⟩,⟨state105_32,exclude105_32⟩,⟨state105_38,exclude105_38⟩,⟨state105_33,exclude105_33⟩,⟨state105_42,exclude105_42⟩] 0x4000400100c14000400000a1106040001060400120602060400040004000800700890089400210281028800610281028400200890089400000890089106020482048800520482048106000890089400100890089206010281028800410281028206000890089800304090409400310211021800210211021400304090409400004090409106020412041800120412041106004090409400104090409206010211021800010211021206004090409008910210009102804090009008904090089102810211021 (by decide +kernel)
def state105_0 : List Sig := roots 105
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude105_0 : Impossible true (goalAt 105) 6 state105_0.toFinset :=
  node_ok cuts105 [⟨state105_1,exclude105_1⟩,⟨state105_14,exclude105_14⟩,⟨state105_23,exclude105_23⟩,⟨state105_28,exclude105_28⟩,⟨state105_36,exclude105_36⟩,⟨state105_40,exclude105_40⟩] 0x4000106000a100a1400100c1206000c18005106020601060400000c100a100a14000044800890089400200c1204800c18004044820480448400000c1008900894001042800890089400200a1102800a18003042810280428400100a100890089400000c1040904094003044820410041800200c1204100c14000044804090409400100a1040904094003042810210021800100a1102100a140010428040904094002008910210009400310280409000980000089040900894002102810211021 (by decide +kernel)
theorem lower105 : Claim 105 7 :=
  fromSearch 3 (by decide +kernel) exclude105_0

theorem lower107 : Claim 107 8 :=
  fromLift 8 2 99 lower105 (by decide +kernel)

theorem lower113 : Claim 113 5 :=
  fromLift 5 32 4 lower81 (by decide +kernel)

theorem lower114 : Claim 114 5 :=
  fromLift 5 32 23134272 lower82 (by decide +kernel)

def rule115_0 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower83 none (by decide +kernel)
def rule115_1 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower99 none (by decide +kernel)
def rule115_2 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower113 none (by decide +kernel)
def rule115_3 : {c : Cut // CutGood (goalAt 115) c} :=
  ruleFor 115 lower114 none (by decide +kernel)
def cuts115 : Cuts (goalAt 115) := [rule115_0,rule115_1,rule115_2,rule115_3]
def state115_0 : List Sig := roots 115
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude115_0 : Impossible true (goalAt 115) 6 state115_0.toFinset :=
  node_ok cuts115 [] 0x4000106000a100a1400000c1206000c14000106020601142400000c100a100a14001085000910091400100c1205000c14001085020500850400100c1009100914000400000910091400000a1113200a14000400111321112400000a1009100914002014208120812400200c1204200c140020142204201c1400200c108120812400001a308120812400000a1183200a1400001a318321812400000a1081208124001011220420012400100910812009140010112081201914001009120420091400300c1081108114003014220410041400300c1204100c14003014208110811400000a1081108114000206010210021400000a110211811400020600811081140010091102100114001011208110011400100910811009140010112102101124002400208110811400208121123081240024003112311214002081208110811 (by decide +kernel)
theorem lower115 : Claim 115 7 :=
  fromSearch 68 (by decide +kernel) exclude115_0

theorem lower121 : Claim 121 8 :=
  fromLift 8 16 3 lower105 (by decide +kernel)

theorem lower106 : Claim 106 5 :=
  fromLift 5 2 19943520 lower104 (by decide +kernel)

theorem lower120 : Claim 120 5 :=
  fromLift 5 16 53891072 lower104 (by decide +kernel)

def rule122_0 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower82 none (by decide +kernel)
def rule122_1 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower90 none (by decide +kernel)
def rule122_2 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower104 none (by decide +kernel)
def rule122_3 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower106 none (by decide +kernel)
def rule122_4 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower114 none (by decide +kernel)
def rule122_5 : {c : Cut // CutGood (goalAt 122) c} :=
  ruleFor 122 lower120 none (by decide +kernel)
def cuts122 : Cuts (goalAt 122) := [rule122_0,rule122_1,rule122_2,rule122_3,rule122_4,rule122_5]
def state122_75 : List Sig := [signal90,input 1,input 3,input 4,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_75 : Impossible true (goalAt 122) 4 state122_75.toFinset :=
  node_ok cuts122 [] 0x11204480c4801120028204805420028051a0112051a01120812204220420812001200120112204208120c1a0c1a08120428014204480428051a0112051a011220480028042800280c1a08120c1a0812 (by decide +kernel)
def state122_31 : List Sig := [signal56,input 1,input 3,input 4,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_31 : Impossible true (goalAt 122) 4 state122_31.toFinset :=
  node_ok cuts122 [] 0x11201420c4801120028014204480028051a0112051a01120812004201420812001200120112205008120c1a0c1a08120428014204480428051a0112051a011220480028042800280c1a08120c1a0812 (by decide +kernel)
def state122_9 : List Sig := [signal39,input 1,input 3,input 4,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_9 : Impossible true (goalAt 122) 4 state122_9.toFinset :=
  node_ok cuts122 [] 0x11201420c4801120028014205420028011a0112051201120c1a204201420c1a0112041a01122042002a0c1a0c120c12042811420142042801121112011204282048002804280028081208120c1a0428 (by decide +kernel)
def state122_42 : List Sig := [signal66,input 1,input 3,input 4,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_42 : Impossible true (goalAt 122) 4 state122_42.toFinset :=
  node_ok cuts122 [] 0x51a04480c48051a0028204805420028051a0132051205120812204220420812041a0812081220420812081a0c120812042801420448042801120112051a042820480028042800280812181208120428 (by decide +kernel)
def state122_86 : List Sig := [signal97,input 1,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_86 : Impossible true (goalAt 122) 4 state122_86.toFinset :=
  node_ok cuts122 [] 0x42801421142042810280142054210280028002804282048001220420142001200120428101200120012001a04120012011204480142011201121112052a011201120512011a01122042001201120012 (by decide +kernel)
def state122_53 : List Sig := [signal73,input 1,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_53 : Impossible true (goalAt 122) 4 state122_53.toFinset :=
  node_ok cuts122 [] 0x42801421142042810280142054210280028002804282060001220420142001200120428101200120012001a04120012011204480142011201121112052a011201120512011a01122042001201120012 (by decide +kernel)
def state122_8 : List Sig := [signal38,input 1,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_8 : Impossible true (goalAt 122) 4 state122_8.toFinset :=
  node_ok cuts122 [] 0x428014211420428112a01420542112a0428012a04282048001220420142001200120428101200120012001a0c12001201120c4801420112011211120428011201120512011a01122042001201120012 (by decide +kernel)
def state122_20 : List Sig := [signal48,input 1,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_20 : Impossible true (goalAt 122) 4 state122_20.toFinset :=
  node_ok cuts122 [] 0x52a01421142052a1028014205421028012a102810282048001220420142001200120032181200120012001a04120012011204480142011201121112052a011201120512011a01122042001201120012 (by decide +kernel)
def state122_77 : List Sig := [signal92,input 1,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_77 : Impossible true (goalAt 122) 4 state122_77.toFinset :=
  node_ok cuts122 [] 0x280048114200280112004808480112011200280828011208122042204208120812002801280812001200120112204210280142204810282048002810280028102801121132011210280812102a0812 (by decide +kernel)
def state122_33 : List Sig := [signal58,input 1,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_33 : Impossible true (goalAt 122) 4 state122_33.toFinset :=
  node_ok cuts122 [] 0x280142185000280112014208480112011200280828011208120042014208120812002801280812001200120112205010280142204810282048002810280028102801121132011210280812102a0812 (by decide +kernel)
def state122_19 : List Sig := [signal47,input 1,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_19 : Impossible true (goalAt 122) 4 state122_19.toFinset :=
  node_ok cuts122 [] 0x2801421142002801120142084801120112002811120112081a20420142081a081a0028181218120112001a0112204210280542014210282048002810280028011205120112011a08120812102a081a (by decide +kernel)
def state122_64 : List Sig := [signal82,input 1,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_64 : Impossible true (goalAt 122) 4 state122_64.toFinset :=
  node_ok cuts122 [] 0x28004811420028011a00480c48011a011a00281112111208122042204208120812002818120812001a08120812204210280142204810282048002810280028011201121132011a08120c120812081a (by decide +kernel)
def state122_88 : List Sig := [signal99,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_88 : Impossible true (goalAt 122) 4 state122_88.toFinset :=
  node_ok cuts122 [] 0x428004210420428001200420c480012001204281012001210280042044210280028002804282048001a00120412001208120042204208120812181208320812204200120812001208120c12081a0812 (by decide +kernel)
def state122_55 : List Sig := [signal75,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_55 : Impossible true (goalAt 122) 4 state122_55.toFinset :=
  node_ok cuts122 [] 0x4280042104204280012004208500012001204281012001210280042044210280028002804282060001a00120412001208120042204208120812181208320812204200120812001208120c12081a0812 (by decide +kernel)
def state122_41 : List Sig := [signal65,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_41 : Impossible true (goalAt 122) 4 state122_41.toFinset :=
  node_ok cuts122 [] 0x428004210420428001200420c4800120012042810120012102a00420542102a0428002a04282048001a00120512001208120042204208120812181204280812204200120812001208120c12081a0812 (by decide +kernel)
def state122_63 : List Sig := [signal81,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_63 : Impossible true (goalAt 122) 4 state122_63.toFinset :=
  node_ok cuts122 [] 0x42a00421142042a001200420c4800120012042a111200121028004204421028002a102810282048001a00120412001208120042204208120812181208320812204200120812001208120c12081a0812 (by decide +kernel)
def state122_6 : List Sig := [input 1,input 3,input 4,signal36,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_6 : Impossible true (goalAt 122) 4 state122_6.toFinset :=
  node_ok cuts122 [] 0x42801421142042801121142085001120112042811120112102811420c5010280028002804282060011a0112051201120812104211420812081204281812081200120012011220500812081a0c120812 (by decide +kernel)
def state122_39 : List Sig := [input 1,input 3,input 4,signal63,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_39 : Impossible true (goalAt 122) 4 state122_39.toFinset :=
  node_ok cuts122 [] 0x4280142114204280112014218500112011204281112011210280142054210280028002804282060011a0112051201120812004201420812081204281812081200120012011220420812081a0c120812 (by decide +kernel)
def state122_5 : List Sig := [input 1,input 3,signal35,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_5 : Impossible true (goalAt 122) 4 state122_5.toFinset :=
  node_ok cuts122 [] 0x4280c4818500428011201420c4801120112042811120112102808480c4810280028002804282060011a0112051201120812084211600812081204281812081200120012011220500812081a0c120812 (by decide +kernel)
def state122_17 : List Sig := [input 1,input 3,input 5,signal45,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_17 : Impossible true (goalAt 122) 4 state122_17.toFinset :=
  node_ok cuts122 [] 0x11201420c480112042804481850042804280112111201121028004804481028011a01120512011200280028042820480812084205480812001200120112205008120428181208120812081a0c120812 (by decide +kernel)
def state122_16 : List Sig := [input 1,input 4,input 5,signal44,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_16 : Impossible true (goalAt 122) 4 state122_16.toFinset :=
  node_ok cuts122 [] 0x102801420542102804280542185004280028002804282048011205420c4801120112011a05120112011204281112011208120442054208120812081a0c12081208120428181208120012001201122050 (by decide +kernel)
def state122_61 : List Sig := [input 1,input 4,input 5,signal79,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_61 : Impossible true (goalAt 122) 4 state122_61.toFinset :=
  node_ok cuts122 [] 0x102801420542102804280142114204280028002804282048011201420c4801120112011a05120112011204281112011208120042014208120812081a0c12081208120428181208120012001201122042 (by decide +kernel)
def state122_38 : List Sig := [input 3,input 4,signal62,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_38 : Impossible true (goalAt 122) 4 state122_38.toFinset :=
  node_ok cuts122 [] 0x4280142114204280812004201420812081204281812081201120142186001120112042811120112001200120112204210280142054210280028002804282060081a08120c120812011a011205120112 (by decide +kernel)
def state122_60 : List Sig := [input 3,input 4,input 5,signal78,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_60 : Impossible true (goalAt 122) 4 state122_60.toFinset :=
  node_ok cuts122 [] 0x81200420142081204280142114204280428081218120812011201420c480112001200120112204201120428111201121028014205421028081a08120c1208120028002804282048011a011205120112 (by decide +kernel)
def state122_10 : List Sig := [signal40,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_10 : Impossible true (goalAt 122) 5 state122_10.toFinset :=
  node_ok cuts122 [] 0x42808501850042801120050085001120112042811120112112a00482048112a0428012a04282048011a0112051201120c1a004220420c1a0c1a042805280c1a0112041a01122042112a0c1a0c120c1201420428206004282060011220500112205010281028112a2048081208120c1a2042 (by decide +kernel)
def state122_43 : List Sig := [signal67,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_43 : Impossible true (goalAt 122) 5 state122_43.toFinset :=
  node_ok cuts122 [] 0x428014211420428051a01422050051a051a04280c28051a18380142204818380428083804282048051a18380512051208120042014208120812042818120812041a0812081220420812081a0c1208120448042820600428206001120112051a205010281028183820480812204208122042 (by decide +kernel)
def state122_21 : List Sig := [signal49,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_21 : Impossible true (goalAt 122) 5 state122_21.toFinset :=
  node_ok cuts122 [] 0x52a04482060052a011204480c4801120112052a111201121028004804481028012a102810282048011a0112051201121832004220421832052a1832181218120112103201122042102a102811281028014204280428052a2060011220500112205010282048102820480812081218322042 (by decide +kernel)
def state122_65 : List Sig := [signal83,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_65 : Impossible true (goalAt 122) 5 state122_65.toFinset :=
  node_ok cuts122 [] 0xc38014220600c3811320142205011320c381132111211121028014205421028083810281028204810281132182810280812004201420812081208321812081210320812081220420812081a0c1208120850042804280c382060011201121132205010282048102820480812204208122042 (by decide +kernel)
def state122_66 : List Sig := [signal84,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_66 : Impossible true (goalAt 122) 5 state122_66.toFinset :=
  node_ok cuts122 [] 0x4280850185004280112005008500112011204281112011210282048204810280028002804282048011a0112051201120812204220420812081204281812081200120012011220420812081a0c12081201422060205020481028204810282042081220420812 (by decide +kernel)
def state122_22 : List Sig := [signal50,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_22 : Impossible true (goalAt 122) 5 state122_22.toFinset :=
  node_ok cuts122 [] 0x4280142114204280112014220500112011204281112011210280142054210280028002804282048011a0112051201120812004201420812081204281812081200120012011220500812081a0c12081204482060205001122050011220481028204810282042 (by decide +kernel)
def state122_83 : List Sig := [signal95,input 1,input 3,input 4,input 6,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_83 : Impossible true (goalAt 122) 5 state122_83.toFinset :=
  node_ok cuts122 [] 0x600112042811120112011220502050011200280028042840001028204820481028011a0112051201120812042818120812081220422042081200120012011220420812081a0c12081240011142205001122050011220481028204810282042081220420812 (by decide +kernel)
def state122_28 : List Sig := [signal54,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_28 : Impossible true (goalAt 122) 5 state122_28.toFinset :=
  node_ok cuts122 [] 0x4280142106004280112014220500112011204280c28011210280142054210280028002804282048011a0112051201121832204201421832042a0428183204280112103201122042102a1028112810280142044801421060052a011211320112113220481028204810280812081220421832 (by decide +kernel)
def state122_49 : List Sig := [signal29,input 1,input 3,input 4,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_49 : Impossible true (goalAt 122) 5 state122_49.toFinset :=
  node_ok cuts122 [] 0xc58011201120448205004480c5820500c48044801120112044800280028006020482048044820480542006000280028051a0028051a011208380112051a0838051a011200280112054a08120812044820422042054a20422042044808120812011220420012205008120012011208120112205020422042012a0812081200280c1a0c1a012a0c1a0c1a002808120812044804280428006020600142044820600448006004280428051a0428051a01120c380112051a0c38051a0112042801122048206020480028042800282048042804280028206000280c1a04280c1a0812052a08120c1a052a0c1a081204280812 (by decide +kernel)
def state122_50 : List Sig := [signal29,input 1,input 3,input 4,input 6,signal12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_50 : Impossible true (goalAt 122) 5 state122_50.toFinset :=
  node_ok cuts122 [] 0x600112051a051a0112011204480c4801120028044820480542051a0112051a011208120c1a0c1a08120812204220420812001200120112204208120c1a0c1a081240010428206004480428051a0112051a011220480428042820600c1a08120c1a0812 (by decide +kernel)
def state122_72 : List Sig := [signal88,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_72 : Impossible true (goalAt 122) 5 state122_72.toFinset :=
  node_ok cuts122 [] 0x428085010600428113220500c48113201320428113204281028204820481028002800280428204810281132182810280812204220420812081204280528081210320812081220420812081a0c12081201420142085010600c38011201122050113220481028204810280812183208121832 (by decide +kernel)
def state122_44 : List Sig := [signal68,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_44 : Impossible true (goalAt 122) 5 state122_44.toFinset :=
  node_ok cuts122 [] 0x428044818500428011204480c480112011204281112011210280048044810280028002804282060011a0112051201120812204220420812081204281812081200120012011220420812081a0c12081201422060042820600428205020482042081220420812 (by decide +kernel)
def state122_71 : List Sig := [signal87,input 1,input 3,input 5,input 6,signal60]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_71 : Impossible true (goalAt 122) 5 state122_71.toFinset :=
  node_ok cuts122 [] 0x5004280112111201120428085018500428011a011205120112102820482048102800280028042820480012001201124002081220422042081208120428181208120812081a0c12081240010c48205004282060042820481028204810282042081220420812 (by decide +kernel)
def state122_26 : List Sig := [signal53,input 1,input 3,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_26 : Impossible true (goalAt 122) 5 state122_26.toFinset :=
  node_ok cuts122 [] 0x116204280428014220600142116220601142014204280428054a10281028014220480142054a20480542014210281028042820480028206010280028042810280428206020482048014200120012005020422042014220420142005000120012052a00120012042810320428052a10321012042800120012112a001200121028041a001a112a041a0412102800120012014201120112005020500448014220500142005001120112052a01120112042811321112052a1132052a042801120112112a011201121028051a0512112a051a011a102801120112204220502042001201120012204201120112001220500012 (by decide +kernel)
def state122_27 : List Sig := [signal53,input 1,input 3,input 5,input 6,signal33]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_27 : Impossible true (goalAt 122) 5 state122_27.toFinset :=
  node_ok cuts122 [] 0x500428052a052a042804280142114204281028112a112a1028102801420542102800280028042820480012014220420548052a0428052a0428112a1028112a10284003011220500142011201121112052a011201120512011a01122042011201122050 (by decide +kernel)
def state122_48 : List Sig := [signal71,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_48 : Impossible true (goalAt 122) 5 state122_48.toFinset :=
  node_ok cuts122 [] 0x4280448185004280112044808500112011204281112011218382048054218380428083804282048011a0112183801120812204220420812081204281812081200120012011220420812081a0c120812014201420448085004280c3804280c38051a10281028204818382042081220420812 (by decide +kernel)
def state122_82 : List Sig := [signal94,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_82 : Impossible true (goalAt 122) 5 state122_82.toFinset :=
  node_ok cuts122 [] 0xc38085011420c380112005008500112011201320c38011210282048204810280838102810282048011a0112051201120812204220420812081208321812081200120012011220420812081a0c12081201420142106008500428042820600c38113210281838102818382042081220420812 (by decide +kernel)
def state122_11 : List Sig := [signal41,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_11 : Impossible true (goalAt 122) 5 state122_11.toFinset :=
  node_ok cuts122 [] 0x428014211420428011201420c480112011204281112011210280142054210280028002804282060011a0112051201120812004201420812081204281812081200120012011220500812081a0c12081208502060042820600428205001122050011220482042 (by decide +kernel)
def state122_47 : List Sig := [signal70,input 1,input 4,input 5,input 6,signal12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_47 : Impossible true (goalAt 122) 5 state122_47.toFinset :=
  node_ok cuts122 [] 0x48002800280428400004280448206004280112011a05120112011204480c48011201120428111201120812081a0c12081208122042204208120812042818120812001200120112204240010542204804282060042820480112205001122042081220420812 (by decide +kernel)
def state122_25 : List Sig := [signal52,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_25 : Impossible true (goalAt 122) 5 state122_25.toFinset :=
  node_ok cuts122 [] 0x428014211420428011201420c480112011204281112011210280142044810280028002804282060051a0112051a01120c1a204201420c1a0c1a042805280c1a0112041a01122042081a081a0c1a1028014204480142044820600428206004280112051a0112051a112a0812081220420c1a (by decide +kernel)
def state122_70 : List Sig := [signal86,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_70 : Impossible true (goalAt 122) 5 state122_70.toFinset :=
  node_ok cuts122 [] 0x428044818500428051a04480c48051a051a04280c28051a10280048044810280028002804282060011a011a051a102808122042204208120812042818120812041a08120812204208120c1a0c1a081201420142085004482060042820600428011201122050051a183808120c1a08120c1a (by decide +kernel)
def state122_80 : List Sig := [signal31,input 1,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_80 : Impossible true (goalAt 122) 5 state122_80.toFinset :=
  node_ok cuts122 [] 0x106000280028004820600048106020601142004800280028085801120112004820500048085820500848004801120112083801120112002811320028083811320828002801120112014a08120812004820422042014a20422042004808120812012a08120812002818320028012a183201280028081208120112204200122050081200120112081201122050204220421060102810280048204801421060204820480048102810282060204820480028102800282060102810280028204800281132102810280112183801121132183811320112102801121832102810280812112a08121832112a102a081210280812 (by decide +kernel)
def state122_81 : List Sig := [signal31,input 1,input 4,input 5,input 6,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_81 : Impossible true (goalAt 122) 5 state122_81.toFinset :=
  node_ok cuts122 [] 0x4800281060206011420112113211320112011220502050011201121132113201120812183218320812081220422042081208121832183208120012001201122042400410282048204810282048102810282048102801121132011210280812102a0812 (by decide +kernel)
def state122_24 : List Sig := [signal51,input 3,input 4,input 5,input 6,signal33]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_24 : Impossible true (goalAt 122) 5 state122_24.toFinset :=
  node_ok cuts122 [] 0x4204280812181208120428014211420428001200120112400201120142205001120112042811120112081a08120c12081210280142054210280028002804282048011a01120512011240010548204204282060042820420112205001122042102820481028 (by decide +kernel)
def state122_46 : List Sig := [signal69,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_46 : Impossible true (goalAt 122) 5 state122_46.toFinset :=
  node_ok cuts122 [] 0x428014211420428011201420c4801120112042811120112112a01420542112a0428012a04282048011a0112051201120812004201420812081204281812081200120012011220500812081a112a081204480142044801420428052a0428052a2050011220500112102810282048112a0c1a (by decide +kernel)
def state122_68 : List Sig := [signal85,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_68 : Impossible true (goalAt 122) 5 state122_68.toFinset :=
  node_ok cuts122 [] 0x106204280428004220600042106220601042004204280428085000120012004220500042085020500c480042001200120c38001200120428103204280c3810321012042800120012044a10281028004220480042044a20480442004210281028042820480028206010280028042810280428206020482048041a1028001a001218380012041a183804120012102800120850081208120042204200420850204220420042081208120c38081208120428183218120c381832083204280812081220502042204200120812001220500812081200122042001218380812081210280c1a0c1218380c1a081a102808120812 (by decide +kernel)
def state122_69 : List Sig := [signal85,input 3,input 4,input 5,input 6,signal60]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_69 : Impossible true (goalAt 122) 5 state122_69.toFinset :=
  node_ok cuts122 [] 0x4204280c380c38042804280850185004280012085020500c480c3804280c3804281028183818381028102820482048102800280028042820481028183818381028400508122042204208120812181208320812204208120812204208120c12081a0812 (by decide +kernel)
def state122_79 : List Sig := [signal93,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_79 : Impossible true (goalAt 122) 5 state122_79.toFinset :=
  node_ok cuts122 [] 0x52a01421142052a01120142205001120112052a111201121028014205421028012a102810282048011a01120512011208120042014208120812042a052a081200120012011220500812081a0c1208120448014210600142042804282060052a20500112205001121028112a1028112a1832 (by decide +kernel)
def state122_85 : List Sig := [input 1,signal96,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_85 : Impossible true (goalAt 122) 5 state122_85.toFinset :=
  node_ok cuts122 [⟨state122_86,exclude122_86⟩] 0x4280142114204280112014220500112011204281112011210280142054210280028002804282048011a0112051201120142044801421060052a0428052a04280112800001124003112a1028112a10280142204201420548052a0428052a04280112205001122042112a1028112a10280812 (by decide +kernel)
def state122_52 : List Sig := [input 1,signal72,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_52 : Impossible true (goalAt 122) 5 state122_52.toFinset :=
  node_ok cuts122 [⟨state122_53,exclude122_53⟩] 0x428014211420428011201420c480112011204281112011210280142054210280028002804282060011a0112051201120142044801420448052a0428052a04280112800001124003112a1028112a10280142204201420448052a0428052a04280112205001122042112a1028112a10280812 (by decide +kernel)
def state122_74 : List Sig := [input 1,input 3,signal89,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_74 : Impossible true (goalAt 122) 5 state122_74.toFinset :=
  node_ok cuts122 [⟨state122_75,exclude122_75⟩] 0x428044818500428011204480c480112011204281112011201420142044808500428800004284001051a0112051a011204482048054205420428206004282048051a0112051a0112102808122042204208120812042818120812001200120112204208120c1a0c1a081208120c1a0c1a0812 (by decide +kernel)
def state122_30 : List Sig := [input 1,input 3,signal55,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_30 : Impossible true (goalAt 122) 5 state122_30.toFinset :=
  node_ok cuts122 [⟨state122_31,exclude122_31⟩] 0x428014211420428011201420c480112011204281112011204480142044801420428800004284001051a0112051a011204480142044801420428206004282048051a0112051a0112102808120042014208120812042818120812001200120112205008120c1a0c1a081208120c1a0c1a0812 (by decide +kernel)
def state122_4 : List Sig := [input 1,input 3,signal34,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_4 : Impossible true (goalAt 122) 5 state122_4.toFinset :=
  node_ok cuts122 [⟨state122_5,exclude122_5⟩,⟨state122_6,exclude122_6⟩] 0x42808501850042801120050085001120112042811120112014240010428800104284003011280000112102808500c5010280028002804282060011a011205120112102820484005102808120850116008120812042818120812001200120112205008122042400408120812081a0c120812 (by decide +kernel)
def state122_87 : List Sig := [input 1,input 3,input 4,signal98,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_87 : Impossible true (goalAt 122) 5 state122_87.toFinset :=
  node_ok cuts122 [⟨state122_88,exclude122_88⟩] 0x42808501850042801420142085010600c3804280c380428085020500c480c480c3804280c3804280112102820482048102800280028042820481028183818381028102818381838102808122042204208120812042818120812800008120812400520420812081220420812081a0c120812 (by decide +kernel)
def state122_54 : List Sig := [input 1,input 3,input 4,signal74,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_54 : Impossible true (goalAt 122) 5 state122_54.toFinset :=
  node_ok cuts122 [⟨state122_55,exclude122_55⟩] 0x42804481850042801420142085004480c3804280c38042808500448085004480c3804280c3804280112102800480448102800280028042820601028183818381028102818381838102808122042204208120812042818120812800008120812400520420812081220420812081a0c120812 (by decide +kernel)
def state122_37 : List Sig := [input 1,input 3,input 4,signal61,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_37 : Impossible true (goalAt 122) 5 state122_37.toFinset :=
  node_ok cuts122 [⟨state122_38,exclude122_38⟩,⟨state122_39,exclude122_39⟩] 0x42801421142042804484001042880010428011201421860011201120428111201120112205040040112102801420542102800280028042820601028204840031028011a01120512011208120042014208120812042818120812081240058000081200120012011220420812081a0c120812 (by decide +kernel)
def state122_76 : List Sig := [input 1,input 3,input 4,input 5,signal91,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_76 : Impossible true (goalAt 122) 5 state122_76.toFinset :=
  node_ok cuts122 [⟨state122_77,exclude122_77⟩] 0x14201421060085010600850114211420428011200500850011201121132113201120112113211320112102820482048102880001028102840042048102810282048011a01120512011208122042204208120812183218320812081218321832081200120012011220420812081a0c120812 (by decide +kernel)
def state122_32 : List Sig := [input 1,input 3,input 4,input 5,signal57,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_32 : Impossible true (goalAt 122) 5 state122_32.toFinset :=
  node_ok cuts122 [⟨state122_33,exclude122_33⟩] 0x44801421060014210600142185001420428011201422050011201121132113201120112113211320112102801420542102880001028102840042048102810282048011a01120512011208120042014208120812183218320812081218321832081200120012011220500812081a0c120812 (by decide +kernel)
def state122_15 : List Sig := [input 1,input 3,input 4,input 5,signal43,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_15 : Impossible true (goalAt 122) 5 state122_15.toFinset :=
  node_ok cuts122 [⟨state122_16,exclude122_16⟩,⟨state122_17,exclude122_17⟩] 0x14204280448185004280428206040050428011204480c48011201124003800101120112042811120112102800480448102810284004800010280028002804282048011a01120512011208120448054808120812204240010812081204281812081200120012011220500812081a0c120812 (by decide +kernel)
def state122_59 : List Sig := [input 1,input 3,input 4,input 5,signal77,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_59 : Impossible true (goalAt 122) 5 state122_59.toFinset :=
  node_ok cuts122 [⟨state122_60,exclude122_60⟩,⟨state122_61,exclude122_61⟩] 0x85004280142114204280428206040030428011201420c48011201122050400101120112042811120112102801420542102810284004800110280028002804282048011a01120512011208120042014208120812400580000812081204281812081200120012011220420812081a0c120812 (by decide +kernel)
def state122_7 : List Sig := [input 1,input 3,input 4,input 5,input 6,signal37]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_7 : Impossible true (goalAt 122) 5 state122_7.toFinset :=
  node_ok cuts122 [⟨state122_8,exclude122_8⟩,⟨state122_9,exclude122_9⟩] 0x850800104280428400104280142114204288000011201124003011201420c48011201120428111201121028112a01420542112a0428012a04282048011a01120512011208120c1a204201420c1a0c1a042805280c1a0112041a01122042112a0c1a0c120c12 (by decide +kernel)
def state122_40 : List Sig := [input 1,input 3,input 4,input 5,input 6,signal64]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_40 : Impossible true (goalAt 122) 5 state122_40.toFinset :=
  node_ok cuts122 [⟨state122_41,exclude122_41⟩,⟨state122_42,exclude122_42⟩] 0x142800104280428400104280448185004280112051a04480c48051a051a04280c28051a102818382048054218380428083804282048051a183805120512800008120812400508122042204208120812042818120812041a0812081220420812081a0c120812 (by decide +kernel)
def state122_18 : List Sig := [input 1,input 3,input 4,input 5,input 6,signal46]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_18 : Impossible true (goalAt 122) 5 state122_18.toFinset :=
  node_ok cuts122 [⟨state122_19,exclude122_19⟩,⟨state122_20,exclude122_20⟩] 0x4480428052a01421142052a800101120112400301120142205001120112052a1112011280001028102840041028014205421028012a102810282048011a01120512011208121832204201421832052a1832181218120112103201122042102a102811281028 (by decide +kernel)
def state122_62 : List Sig := [input 1,input 3,input 4,input 5,input 6,signal80]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_62 : Impossible true (goalAt 122) 5 state122_62.toFinset :=
  node_ok cuts122 [⟨state122_63,exclude122_63⟩,⟨state122_64,exclude122_64⟩] 0x14204280c38085011420c380112113220500c4811320c38113211121112800110281028400410282048204810280838102810282048102811321828102880000812081240050812204220420812081208321812081210320812081220420812081a0c120812 (by decide +kernel)
def state122_14 : List Sig := [input 1,input 3,input 4,signal42,input 6,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_14 : Impossible true (goalAt 122) 5 state122_14.toFinset :=
  node_ok cuts122 [] 0x14204280428052a400511422060114218500112052a1112011201121142205001122050011201122050012a10281028400010281142204810282048102810282048011a011205120112052a183218121812183210421142183208120112103201122050102a102811281028 (by decide +kernel)
def state122_58 : List Sig := [input 1,input 3,input 4,signal76,input 6,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_58 : Impossible true (goalAt 122) 5 state122_58.toFinset :=
  node_ok cuts122 [] 0x142042804280c38400318502060114211420c3811321112111211321050185011320112083810281028400010282048204810282048102810282048102811321828102808120832181208120812204220420812204208120812204210320812081220420812081a0c120812 (by decide +kernel)
def state122_36 : List Sig := [input 1,input 3,signal59,input 5,input 6,signal60]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_36 : Impossible true (goalAt 122) 5 state122_36.toFinset :=
  node_ok cuts122 [] 0x1420428051a0c28051a04280c481850042801120112051a40040c4820500c4818600428206004282050051a183805120512183808480c48183804280838042820601028041a0812081240020812204220420812081204281812081220420812081220420812081a0c120812 (by decide +kernel)
def state122_57 : List Sig := [input 1,input 3,input 5,signal76,input 6,signal60]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_57 : Impossible true (goalAt 122) 5 state122_57.toFinset :=
  node_ok cuts122 [] 0x1420112011211324001085020500c480c4811320c38111211120c38085018500c380428102811321828102810282048204810282048102810282048083810281028204810320812081240020812204220420812204208120812204208120832181208120812081a0c120812 (by decide +kernel)
def state122_3 : List Sig := [input 1,signal32,input 4,input 5,input 6,signal12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_3 : Impossible true (goalAt 122) 5 state122_3.toFinset :=
  node_ok cuts122 [] 0x142012a04280428400004280542206004280112011a05120112011205420c480112011204281112011210281028112a40050542204805420c5004282060042820480112205001122048112a0c1a0c120c120c1a044205420c1a0c1a042805280c1a0112041a011220500812 (by decide +kernel)
def state122_35 : List Sig := [input 1,input 4,signal59,input 5,input 6,signal12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_35 : Impossible true (goalAt 122) 5 state122_35.toFinset :=
  node_ok cuts122 [] 0x142083804280428400004280448206004281028102818384003044820480542054204282060042820481838051a05120512051a04480c48051a051a04280c28051a01120812081a0c120812081220422042081208120428181208122042081208122042041a081208122042 (by decide +kernel)
def state122_2 : List Sig := [input 3,signal32,input 4,input 5,input 6,signal33]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_2 : Impossible true (goalAt 122) 5 state122_2.toFinset :=
  node_ok cuts122 [] 0x44804280c1a05280c1a0428014211420428041a01120112400201120142205001120112042811120112081208120c1a40040142204201421160042820600428204201122050011220420c1a112a0c120c12112a01420542112a0428012a04282060011a0112051201121028 (by decide +kernel)
def state122_13 : List Sig := [input 3,input 4,input 5,signal42,input 6,signal33]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_13 : Impossible true (goalAt 122) 5 state122_13.toFinset :=
  node_ok cuts122 [] 0x448081208121832400101422042014205481832052a18121812052a01421142052a04281032011201124002011201422050011220500112011220420112052a111201121028102a1128102810280142054210282048102810282042012a102810282048011a011205120112 (by decide +kernel)
def state122_84 : List Sig := [signal95,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_84 : Impossible true (goalAt 122) 6 state122_84.toFinset :=
  node_ok cuts122 [⟨state122_85,exclude122_85⟩,⟨state122_22,exclude122_22⟩,⟨state122_87,exclude122_87⟩,⟨state122_66,exclude122_66⟩,⟨state122_83,exclude122_83⟩] 0x4001400100601060800410604001042804281870011201121060205020501870205020501060011201120c38011201120428113204280c3811321112042801120112400010281028106020482048400020482048106010281028042820480028400010280028042810280428400120482048051a1028011a011218380112051a18380512011210280112116208120812106020422042116220422042106008120812052a08120812042818320428052a18321812042808120812011220420012205008120012011208120112205020422042112a0812081210280c1a081a112a0c1a0c12102808120812400140010142800440012060205040032050011280030112205080022050011240030112204840042048102840001028204840002048102840041028204240052042081280010812204280002042081240050812 (by decide +kernel)
def state122_73 : List Sig := [signal87,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_73 : Impossible true (goalAt 122) 6 state122_73.toFinset :=
  node_ok cuts122 [⟨state122_74,exclude122_74⟩,⟨state122_44,exclude122_44⟩,⟨state122_71,exclude122_71⟩,⟨state122_76,exclude122_76⟩,⟨state122_66,exclude122_66⟩] 0x1870042804280850206008501870206018500850042804284003400300500850800208504003011201120c38011201120428113204280c38113211120428011201120c58102810280850204820480c5820482048085010281028042820480028206010280028042810280428206020482048051a1028011a011218380112051a18380512011210280112400208120812085020422042400220422042085008120812052a08120812042818320428052a18321812042808120812011220420012400208120012011208120112400320422042112a0812081210280c1a081a112a0c1a0c12102808120812400340030142206040012060042880040428206080032060042840010428800240032050204840042048102880011028204880002048102840041028204240052042081240020812204240022042081240050812 (by decide +kernel)
def state122_51 : List Sig := [signal70,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_51 : Impossible true (goalAt 122) 6 state122_51.toFinset :=
  node_ok cuts122 [⟨state122_52,exclude122_52⟩,⟨state122_11,exclude122_11⟩,⟨state122_47,exclude122_47⟩,⟨state122_54,exclude122_54⟩,⟨state122_44,exclude122_44⟩] 0x4000042804280448206004484000206020600448042804280c58011201120448205004480c5820500c480448011201120c38011201120428113204280c3811321112042801120112400440040048044880020448400410281028042840000028206010280028042810280428206040042060051a1028011a011218380112051a18380512011210280112054a08120812044820422042054a20422042044808120812052a08120812042818320428052a18321812042808120812011220420012205008120012011208120112205020422042112a0812081210280c1a081a112a0c1a0c12102808120812400440040142206040012060042840000428206040002060042840010428205040032050011280040112205080032050011240030112800240042048204240052042081280010812204280002042081240050812 (by decide +kernel)
def state122_29 : List Sig := [signal51,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_29 : Impossible true (goalAt 122) 6 state122_29.toFinset :=
  node_ok cuts122 [⟨state122_24,exclude122_24⟩,⟨state122_30,exclude122_30⟩,⟨state122_11,exclude122_11⟩,⟨state122_32,exclude122_32⟩,⟨state122_22,exclude122_22⟩] 0x1162042804280142206001421162206011420142042804284002011201120142205001424002205020500142011201120c38011201120428113204280c3811321112042801120112054a10281028014220480142054a20480542014210281028042820480028206010280028042810280428206020482048051a1028011a011218380112051a18380512011210280112400540050042014280000142400508120812052a08120812042818320428052a18321812042808120812011240020012205008120012011208120112205040052050112a0812081210280c1a081a112a0c1a0c12102808120812400540050448206040012060042880040428206080032060042840010428205040032050011240020112205040022050011240030112204840042048102880021028204880012048102840041028800040052042 (by decide +kernel)
def state122_1 : List Sig := [input 1,input 3,signal32,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_1 : Impossible true (goalAt 122) 6 state122_1.toFinset :=
  node_ok cuts122 [⟨state122_2,exclude122_2⟩,⟨state122_3,exclude122_3⟩,⟨state122_4,exclude122_4⟩,⟨state122_7,exclude122_7⟩,⟨state122_10,exclude122_10⟩,⟨state122_11,exclude122_11⟩] 0x106004280428014220600142106020601142014204280428085001120112014220500142085020500c480142011201120c38011201120428113204280c38113211120428011201120142800501420850800408500142800301420850800208500428400104282060400020600428400004282060400120600112400301122050400220500112400201122050400320500448112a112a0142400401420448800105420142112a112a0428400004282060112a012a0428112a0428206040042060051a112a011a011240040112051a400205120112112a011240044005102801420c1a0c1a04484005044801428000014204480c1a0c1a052a0c1a0c1a042840050428052a4000052804280c1a0c1a01124002011220500c1a041a01120c1a0112205040052050400440040812112a4004112a40050c1a0c1a400440040c12 (by decide +kernel)
def state122_34 : List Sig := [input 1,input 3,input 4,signal59,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_34 : Impossible true (goalAt 122) 6 state122_34.toFinset :=
  node_ok cuts122 [⟨state122_35,exclude122_35⟩,⟨state122_36,exclude122_36⟩,⟨state122_37,exclude122_37⟩,⟨state122_40,exclude122_40⟩,⟨state122_43,exclude122_43⟩,⟨state122_44,exclude122_44⟩] 0x1060042804280142206001421060206011420142042804280448800504480142800401420448800304480142800201420428400104282060400020600428400004282060400120600850051a051a014240030142085080010c480142051a051a0c38051a051a0428400304280c3840000c280428051a051a400340040112044818381838014240040142044880000448014218381838042840000428206018380838042818380428206040042060400340031028051a4003051a400418381838400340030512014208120812044820420042014220420142044808120812052a08120812042818320428052a18321812042808120812400220422042400508120812400208120812400520422042051a2042041a400208120812051a0812081240032042204240040812081218380c1a081a40020c1a0c12183808120812 (by decide +kernel)
def state122_12 : List Sig := [input 1,input 3,input 4,input 5,signal42,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_12 : Impossible true (goalAt 122) 6 state122_12.toFinset :=
  node_ok cuts122 [⟨state122_13,exclude122_13⟩,⟨state122_14,exclude122_14⟩,⟨state122_15,exclude122_15⟩,⟨state122_18,exclude122_18⟩,⟨state122_21,exclude122_21⟩,⟨state122_22,exclude122_22⟩] 0x142800501420448800404480142800301420448800204481060052a052a0142400101421060800111420142052a052a400140050428085001120112014220500142085020500c48014201120112400220502050400301120112400201120112400320502050400101120112052a1132052a400211321112052a01120112044810281028014220480142044820480542014210281028400020482048400410281028400010281028400420482048052a2048012a400010281028052a10281028400120482048051a1028011a011218380112051a18380512011210280112014218321832044840050448014280000142044818321832400140010812052a4001052a400518321832400140011812011240020112205018321032011218320112205040052050112a1832102a102840051028112a40001128102818321028 (by decide +kernel)
def state122_56 : List Sig := [input 1,input 3,input 4,input 5,signal76,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_56 : Impossible true (goalAt 122) 6 state122_56.toFinset :=
  node_ok cuts122 [⟨state122_57,exclude122_57⟩,⟨state122_58,exclude122_58⟩,⟨state122_59,exclude122_59⟩,⟨state122_62,exclude122_62⟩,⟨state122_65,exclude122_65⟩,⟨state122_66,exclude122_66⟩] 0x8508005085001428004014208508003085001428002014210600c380c3801424001014210608001185001420c380c384001400304280850113211320142400301420850800008500142113211324001400101120c3840010c384003113211324001400111120448102810280142204801420448204805420142102810284000204820484004102810284000102810284004204820480c38204808384000102810280c38102810284001204820484003102810281132183811324000183818281132102810280142081208120448204200420142204201420448081208124002204220424005081208124002081208124005204220424001081208120c38183208324002183218120c3808120812113220421032400208120812113208120812400320422042112a0812081210280c1a081a112a0c1a0c12102808120812 (by decide +kernel)
def state122_23 : List Sig := [input 1,input 3,input 4,input 5,input 6,signal33]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_23 : Impossible true (goalAt 122) 6 state122_23.toFinset :=
  node_ok cuts122 [⟨state122_2,exclude122_2⟩,⟨state122_13,exclude122_13⟩,⟨state122_24,exclude122_24⟩,⟨state122_7,exclude122_7⟩,⟨state122_25,exclude122_25⟩,⟨state122_26,exclude122_26⟩,⟨state122_27,exclude122_27⟩,⟨state122_18,exclude122_18⟩,⟨state122_28,exclude122_28⟩] 0x4005400504488008042804284001052a052a8007052a052a4001042804281162042804280142206001421162206011420142042804284002800680054003011201124002011201124003400240034002011201120142205001424002205020500142011201120c38011201120428113204280c38113211120428011201128004102810284004112a112a8003112a112a400410281028054a10281028014220480142054a20480542014210281028042820480028206010280028042810280428206020482048051a1028011a011218380112051a18380512011210280112400580020812014280020142400520422042400540050548052a2042052a042840050428052a8001052a042820420428011220420112205040052050011240020112205020422042112a2042112a102840051028112a8000112a102820421028 (by decide +kernel)
def state122_45 : List Sig := [input 1,input 3,input 4,input 5,input 6,signal12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_45 : Impossible true (goalAt 122) 6 state122_45.toFinset :=
  node_ok cuts122 [⟨state122_3,exclude122_3⟩,⟨state122_7,exclude122_7⟩,⟨state122_46,exclude122_46⟩,⟨state122_35,exclude122_35⟩,⟨state122_47,exclude122_47⟩,⟨state122_40,exclude122_40⟩,⟨state122_48,exclude122_48⟩,⟨state122_49,exclude122_49⟩,⟨state122_50,exclude122_50⟩] 0x4004400401424000800880074001042804284000042804284001400040014000042804280448206004484000206020600448042804288006011201124003051a051a8005051a051a4003011201120c58011201120448205004480c5820500c480448011201120c38011201120428113204280c3811321112042801120112400480041028044880040448400420482048400440040542042820480428206040042060042840000428206020482048051a2048051a011240040112051a8003051a01122048011280020812081240050c1a0c1a80010c1a0c1a400508120812054a08120812044820422042054a20422042044808120812052a08120812042818320428052a1832181204280812081201122042001220500812001201120812011220502042204240040812081220480c1a0c1a80000c1a0c1a204808120812 (by decide +kernel)
def state122_67 : List Sig := [input 1,input 3,input 4,input 5,input 6,signal60]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_67 : Impossible true (goalAt 122) 6 state122_67.toFinset :=
  node_ok cuts122 [⟨state122_68,exclude122_68⟩,⟨state122_69,exclude122_69⟩,⟨state122_36,exclude122_36⟩,⟨state122_40,exclude122_40⟩,⟨state122_70,exclude122_70⟩,⟨state122_57,exclude122_57⟩,⟨state122_71,exclude122_71⟩,⟨state122_62,exclude122_62⟩,⟨state122_72,exclude122_72⟩] 0x40034003014280080428042840010c380c3880070c380c38400104280428187004280428085020600850187020601850085004280428400380060112085080060850400320502050400340030c480c3820500c380428400304280c3880050c380428205004288004102810284004183818388003183818384004102810280c58102810280850204820480c5820482048085010281028042820480028206010280028042810280428206020482048400310281028205018381838800218381838205010281028400280018000400508120812400208120812400540024005400208120812085020422042400220422042085008120812052a08120812042818320428052a18321812042808120812400320422042205008120812400208120812205020422042112a0812081210280c1a081a112a0c1a0c12102808120812 (by decide +kernel)
def state122_78 : List Sig := [input 1,input 3,input 4,input 5,input 6,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_78 : Impossible true (goalAt 122) 6 state122_78.toFinset :=
  node_ok cuts122 [⟨state122_14,exclude122_14⟩,⟨state122_18,exclude122_18⟩,⟨state122_79,exclude122_79⟩,⟨state122_80,exclude122_80⟩,⟨state122_81,exclude122_81⟩,⟨state122_58,exclude122_58⟩,⟨state122_62,exclude122_62⟩,⟨state122_82,exclude122_82⟩,⟨state122_83,exclude122_83⟩] 0x400140010142400180080428106080081060400120602060400140011142800701120112400311321132800611321132400301120112187001120112106020502050187020502050106001120112400101120112206011321132800511321132206001120112400080048003400410281028400010281028400440004004400010281028106020482048400020482048106010281028400120482048206010281028400010281028206020482048051a1028011a011218380112051a18380512011210280112800208120812400518321832800118321832400508120812116208120812106020422042116220422042106008120812400108120812206018321832800018321832206008120812011220420012205008120012011208120112205020422042112a0812081210280c1a081a112a0c1a0c12102808120812 (by decide +kernel)
def state122_0 : List Sig := roots 122
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude122_0 : Impossible true (goalAt 122) 7 state122_0.toFinset :=
  node_ok cuts122 [⟨state122_1,exclude122_1⟩,⟨state122_12,exclude122_12⟩,⟨state122_23,exclude122_23⟩,⟨state122_29,exclude122_29⟩,⟨state122_34,exclude122_34⟩,⟨state122_45,exclude122_45⟩,⟨state122_51,exclude122_51⟩,⟨state122_56,exclude122_56⟩,⟨state122_67,exclude122_67⟩,⟨state122_73,exclude122_73⟩,⟨state122_78,exclude122_78⟩,⟨state122_84,exclude122_84⟩] 0x800b1060042804284001014220600142800a1060206011424001014204280428800908500112011240030142205001428008085020500c48400301420112011240010c3801120112400304281132042880070c38113211124001042801120112800604481028102840040142204801428005044820480542400401421028102840010428204800284004206010280028400004281028042840012060204820484003051a1028011a40040112183801128004051a18380512400301121028011280030142081208124005044820420042800201422042014240050448081208124001052a0812081240050428183204288001052a18321812400104280812081240030112204200124005205008120012400201120812011240032050204220424004112a08120812400510280c1a081a8000112a0c1a0c124004102808120812 (by decide +kernel)
theorem lower122 : Claim 122 8 :=
  fromSearch 20009024 (by decide +kernel) exclude122_0

def rule123_0 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower27 none (by decide +kernel)
def rule123_1 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower41 none (by decide +kernel)
def rule123_2 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower51 none (by decide +kernel)
def rule123_3 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower57 none (by decide +kernel)
def rule123_4 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower59 none (by decide +kernel)
def rule123_5 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower59 (some (1,input 3,input 5)) (by decide +kernel)
def rule123_6 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower73 none (by decide +kernel)
def rule123_7 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower75 none (by decide +kernel)
def rule123_8 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower81 none (by decide +kernel)
def rule123_9 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower82 none (by decide +kernel)
def rule123_10 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower83 none (by decide +kernel)
def rule123_11 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower89 none (by decide +kernel)
def rule123_12 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower90 none (by decide +kernel)
def rule123_13 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower91 none (by decide +kernel)
def rule123_14 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower99 none (by decide +kernel)
def rule123_15 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower107 none (by decide +kernel)
def rule123_16 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower107 (some (1,input 3,input 5)) (by decide +kernel)
def rule123_17 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower107 (some (1,input 3,input 6)) (by decide +kernel)
def rule123_18 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower107 (some (1,input 5,input 6)) (by decide +kernel)
def rule123_19 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower113 none (by decide +kernel)
def rule123_20 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower114 none (by decide +kernel)
def rule123_21 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower115 none (by decide +kernel)
def rule123_22 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower121 none (by decide +kernel)
def rule123_23 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower121 (some (1,input 3,input 6)) (by decide +kernel)
def rule123_24 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower121 (some (1,input 5,input 6)) (by decide +kernel)
def rule123_25 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower122 none (by decide +kernel)
def rule123_26 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower122 (some (1,input 3,input 6)) (by decide +kernel)
def rule123_27 : {c : Cut // CutGood (goalAt 123) c} :=
  ruleFor 123 lower122 (some (1,input 5,input 6)) (by decide +kernel)
def cuts123 : Cuts (goalAt 123) := [rule123_0,rule123_1,rule123_2,rule123_3,rule123_4,rule123_5,rule123_6,rule123_7,rule123_8,rule123_9,rule123_10,rule123_11,rule123_12,rule123_13,rule123_14,rule123_15,rule123_16,rule123_17,rule123_18,rule123_19,rule123_20,rule123_21,rule123_22,rule123_23,rule123_24,rule123_25,rule123_26,rule123_27]
def state123_21 : List Sig := [signal106,input 0,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_21 : Impossible true (goalAt 123) 5 state123_21.toFinset :=
  node_ok cuts123 [] 0xa10042104200a1001200420c480012001200a110120012008b00420542008b008b00a10528008b008b00120512008b04092041204104090409002118110409040908110c090409000b040904090811081200c1204208120812181204280812009100910812001200890089081a008b040905090409040b (by decide +kernel)
def state123_27 : List Sig := [signal108,input 0,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_27 : Impossible true (goalAt 123) 5 state123_27.toFinset :=
  node_ok cuts123 [] 0xa30042114200a30012004208500012001200a3111200120089004204420089008900a30428008900890012041200890409204120410409040910211811040904090811081104090009000900890811081200c1204208120812181208320812009100910812001208120089081a00890811040908110409 (by decide +kernel)
def state123_11 : List Sig := [signal103,input 0,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_11 : Impossible true (goalAt 123) 5 state123_11.toFinset :=
  node_ok cuts123 [] 0xa30042114200a3001200420c480012001200a311120012008b00420542008b008b00a30428008b008b00120512008b04092041204104090409102118110409040908110c090409000b040904090811081200c1204208120812181204280812009100910812001200890089081a008b040905090409040b (by decide +kernel)
def state123_10 : List Sig := [signal102,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_10 : Impossible true (goalAt 123) 5 state123_10.toFinset :=
  node_ok cuts123 [] 0x21004111420021001100410c4800110011002111120011000900410542000900090021042800090009001105120009081200410141081208120021181208120013001101110011000b0009010900090409004120410409040918111021040904090c0908110409081100090409000904090509040b0409 (by decide +kernel)
def state123_4 : List Sig := [input 0,input 1,input 4,signal100,signal12,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_4 : Impossible true (goalAt 123) 5 state123_4.toFinset :=
  node_ok cuts123 [] 0x42810280428400700a100a1042805420089008910281142051a0428111211121132051a05120512009108120428181208120812081a0c120812202a081208122028041a081208122042040910211811040908110409040908112029040904092028040908110c0904090409040b05090409 (by decide +kernel)
def state123_16 : List Sig := [input 0,input 1,signal59,signal76,signal12,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_16 : Impossible true (goalAt 123) 5 state123_16.toFinset :=
  node_ok cuts123 [] 0x82808280c284007051a00a10c28051a1828051a051205120c28113211121112008900891828113200910091051a204808120c28181208120812081a0c120812041a081208122042103208120812204204091021181104090811040904090811040908110c09040910210409040910210409040b05090409 (by decide +kernel)
def state123_22 : List Sig := [signal29,input 0,input 1,input 3,input 4,signal76,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_22 : Impossible true (goalAt 123) 6 state123_22.toFinset :=
  node_ok cuts123 [] 0xa104480c5800a1111204480c58111200911028204805421028002800a1102800a11028111208281112081220422042081200a30812081200a1101208120812204208120c1a0c1a081204092041204104090409081108110409040908110811040908110409040908110409040b050904090c3800c104480c38400f00a1042800a10c2811120c381112008900890c3810280c1a08120c1a08120409081104090811 (by decide +kernel)
def state123_12 : List Sig := [signal104,input 0,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_12 : Impossible true (goalAt 123) 6 state123_12.toFinset :=
  node_ok cuts123 [] 0x4280448114204280091044808500091009104280c3800911028204805421028042810280428204800990091183800910812204220420812081204281812081200120091019100910812081a0c12081204092041204104090409102118110409040900110091040908110409040908110409040b0509040900c100c10448085000a100a104280c38051a008900891028183820420812204208120409081104090811 (by decide +kernel)
def state123_28 : List Sig := [signal31,input 0,input 1,input 4,signal59,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_28 : Impossible true (goalAt 123) 6 state123_28.toFinset :=
  node_ok cuts123 [] 0x4280448114204280089004804480089008900280428008905120448084805120512042808280512009108122042204208120812042805280812008b008901890089041204120512204204092041204104090409102110210409000900090089102104090411080904090409040b05090409183800c11060183800a100a118380428400f008910280089182805121838051218320812183208121021040910210409 (by decide +kernel)
def state123_20 : List Sig := [input 0,input 1,input 3,input 4,signal105,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_20 : Impossible true (goalAt 123) 6 state123_20.toFinset :=
  node_ok cuts123 [⟨state123_21,exclude123_21⟩] 0xa10448185000a100c100c1044810600c3800a1042800a1051a04480c48051a051a00a10c38051a00911028204805421028002800a1102800a10089008918381028051a1838051205120812204220420812081200a1181208128000081208124016041a0812081220420812081a0c120812040920412041040904090021181104091021040904091021040908110c09040908110409040908110409040b05090409 (by decide +kernel)
def state123_26 : List Sig := [input 0,input 1,input 3,input 4,signal107,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_26 : Impossible true (goalAt 123) 6 state123_26.toFinset :=
  node_ok cuts123 [⟨state123_27,exclude123_27⟩] 0x42804481142042800c100c10850044800a100a10c38042811320448085011320c38042811121112009100890048044800890089002804280089008918381028008900891132183800890812204220420812081204281812081280000812081240161032081208122042008b008901890089040920412041040904091021181104090409081108110409040908110811040900090009008908110409040b05090409 (by decide +kernel)
def state123_9 : List Sig := [input 0,input 1,input 3,input 4,input 5,input 6,signal101]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_9 : Impossible true (goalAt 123) 6 state123_9.toFinset :=
  node_ok cuts123 [⟨state123_10,exclude123_10⟩,⟨state123_11,exclude123_11⟩] 0xc100a104280448114204280091051a04480c48051a051a042811121112008910282048054210280428102804282048051a113205120512800108120812401608122042204208120812042818120812041a0812081220420812081a0c120812800004090409400c04092041204104090409102118110409040908110c09040908110409040908110409040b05090409 (by decide +kernel)
def state123_17 : List Sig := [input 0,input 1,input 3,input 4,signal76,signal12,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_17 : Impossible true (goalAt 123) 6 state123_17.toFinset :=
  node_ok cuts123 [⟨state123_16,exclude123_16⟩,⟨state123_4,exclude123_4⟩] 0xc3800c10c38400700a100a10c38044818502060114211420c38113211121112113210501850113200910c3820480c380542008920282028800120482048113280001132081208321812081208120c1a0c1a08122042081208122042103208120812204208120c1a0c1a0812040910211811040908110409040908110409081108110409040908110811040908110409040908110409040b05090409 (by decide +kernel)
def state123_7 : List Sig := [input 0,input 1,input 3,input 4,signal100,input 6,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_7 : Impossible true (goalAt 123) 6 state123_7.toFinset :=
  node_ok cuts123 [⟨state123_4,exclude123_4⟩] 0xc100a100a1042840031850206011421142051a042811121112051a10501850051a0091042810280428400a10281048800010280089051a113205120512081204281812081208122042204208122042081208122042041a0812081220420812081a0c120812040910211811040904092041204104092041040904092041040908110c09040908110409040908110409040b05090409 (by decide +kernel)
def state123_15 : List Sig := [input 0,input 1,input 4,signal59,input 5,signal12,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_15 : Impossible true (goalAt 123) 6 state123_15.toFinset :=
  node_ok cuts123 [⟨state123_16,exclude123_16⟩,⟨state123_4,exclude123_4⟩] 0xc118381838400700a11838206018381142044820480542054200890089183810602028202880012048051a04480c48051a1838051a05120512051a20608000051a009108121832183208120812081a0c12081208121832183208122042081208122042041a0812081220420409102110210409081104090409081104091021102104091021040904091021040908110c0904090409040b05090409 (by decide +kernel)
def state123_3 : List Sig := [input 0,input 1,input 4,input 5,signal100,input 6,signal12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_3 : Impossible true (goalAt 123) 6 state123_3.toFinset :=
  node_ok cuts123 [⟨state123_4,exclude123_4⟩] 0xc1008900891028400304482048054205421028042804284007042804488000042800a11132051a05120512051a04480c48051a0091051a0428111211120812081a0c120812081220422042081220420812081220420812042818120812041a0812081220420811040904090811040920412041040920410409040920410409102118110409040908110c0904090409040b05090409 (by decide +kernel)
def state123_5 : List Sig := [input 0,input 1,input 4,signal10,signal12,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_5 : Impossible true (goalAt 123) 6 state123_5.toFinset :=
  node_ok cuts123 [⟨state123_4,exclude123_4⟩] 0x42840070428400a10281028042810280428400a400740070428400300a1400a202800a1042820280428400a400305421028400300894007202800891028202810284007400311420c38009100910428113204280c3811320c280428009100911838009100911028051a051a1838051a051a102800910091400a009100912028051a051a8000051a051a202800910091052a08120812042818320428052a18320528042808120812112a0812081210280c1a0c1a112a0c1a0c1a102808120812400a0812081220280c1a0c1a40080c1a0c1a202808120812011220420012009108120091011208120191009120420091400904090409042810211021400910211021042804090409400908110811102804090409400904090409102808110811400a08110811202804090409400904090409202808110811009104090409011208110011009108110c090112040904094008040904090812050b040b4009050b0509081204090409 (by decide +kernel)
def state123_19 : List Sig := [signal29,input 0,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_19 : Impossible true (goalAt 123) 7 state123_19.toFinset :=
  node_ok cuts123 [⟨state123_20,exclude123_20⟩,⟨state123_22,exclude123_22⟩] 0x106000a100a10448400a0448106040021060044800a100a10c58009100910448205004480c5820500c48044800910091400a0091009100a1113200a180011132111200a100910091044810281028106020482048044820480542106010281028400a2048002800a1102800a1400a1028102800a1204800a1051a1028051a009118380091051a1838051a009110280091054a08120812044820422042054a2042204204480812081201a30812081200a1183200a101a31832181200a108120812011220420012009108120091011208120191009120420091112a0812081210280c1a0c1a112a0c1a0c1a10280812081240090409040904482041204140092041204104480409040900a10409040940091021002100a110211811400a04090409009104090409011208110011009108110c09011204090409400a081108111028040904094009040904091028081108114008040904090812050b040b4009050b05090812040904090448400300c11060400a00c10448400a04481060400310604002400a0428051a400f051a009140020091051a8000051a0091400f00912048400700891028400300892048400320481028400710280c1a40160c1a0812400808120c1a40080c1a0812401608120409400c04090811400908110409400904090811400c0811 (by decide +kernel)
def state123_25 : List Sig := [signal31,input 0,input 1,input 3,input 4,input 5,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_25 : Impossible true (goalAt 123) 7 state123_25.toFinset :=
  node_ok cuts123 [⟨state123_26,exclude123_26⟩,⟨state123_28,exclude123_28⟩] 0x1060042804280448206004481060206011420448042804280c58009100910448205004480c5820500c480448009100910c38009100910428113204280c3811320c280428009100910448008900891060400a00480448400004481060008900890428008900892060400a00280428400a0428206000890089051a008900890091400a0091051a80010512009100890089054a08120812044820422042054a20422042044808120812052a08120812042818320428052a18320528042808120812011220420012009108120091011208120191009120420091018b0812008b00890c1a0089018b0c1a0189008908120089400904090409044820412041400920412041044804090409400a04090409042810211021400910211021042804090409009104090409011208110011009108110c09011204090409008908110009400904090009008904090089400a081108114008040904090812050b040b4009050b05090812040904091060400300c10448400700c11060400710600448400304482060400700a10428400300a12060400320600428400704281132400f11320091400000911132800011320091400f00914000400a10281832401618320812400808121832400818320812401608121021400c10210409400904091021400910210409400c0409 (by decide +kernel)
def state123_18 : List Sig := [input 0,input 1,input 3,input 4,input 5,input 6,signal12,signal25]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_18 : Impossible true (goalAt 123) 7 state123_18.toFinset :=
  node_ok cuts123 [] 0x4007400a106000a140020428400a04280448206004280091051a051a00910091051a051a0091009104480c480091009104280c280091400010280448204805420428206004282048051a0091051a009108120c1a0c1a081208120c1a0c1a081208122042204208120812042805280812001200910191009108120c1a0c1a08120811040904090811081104090409081104092041204104090409102110210409040900110c09040908110409040908110409040b05090409 (by decide +kernel)
def state123_24 : List Sig := [input 0,input 1,input 3,input 4,input 5,input 6,signal18,signal25]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_24 : Impossible true (goalAt 123) 7 state123_24.toFinset :=
  node_ok cuts123 [] 0x400a400a0448400204281060206011420091051a051a0091009111321132009100912050205000910091113211320091008940001028400a10282048204810282048102810282048051a0091051a009108120c1a0c1a0812081218321832081208122042204208120812183218320812001200910191009108120c1a0c1a08120811040904090811040910211021040904092041204104090409102110210409040900110c09040908110409040908110409040b05090409 (by decide +kernel)
def state123_8 : List Sig := [input 0,input 1,input 3,input 4,input 5,input 6,signal25]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_8 : Impossible true (goalAt 123) 7 state123_8.toFinset :=
  node_ok cuts123 [⟨state123_9,exclude123_9⟩,⟨state123_12,exclude123_12⟩] 0x400a400a00c1400a400200a1106004280428044820600448106020601142044804280428800100910091400f051a051a8000051a051a400f009100910c58009100910448205004480c5820500c480448009100910c38009100910428113204280c3811320c28042800910091400a40000089044810281028106020482048044820480542106010281028042820480428206010281028042810280428206020482048051a1028051a009118380091051a1838051a00911028009140080812081240160c1a0c1a40080c1a0c1a401608120812054a08120812044820422042054a20422042044808120812052a08120812042818320428052a18320528042808120812011220420012009108120091011208120191009120420091112a0812081210280c1a0c1a112a0c1a0c1a102808120812400908110811400c04090409400904090409400c08110811400904090409044820412041400920412041044804090409400a04090409042810211021400910211021042804090409009104090409011208110011009108110c09011204090409400a081108111028040904094009040904091028081108114008040904090812050b040b4009050b0509081204090409 (by decide +kernel)
def state123_14 : List Sig := [input 0,input 1,input 3,input 4,input 5,signal12,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_14 : Impossible true (goalAt 123) 7 state123_14.toFinset :=
  node_ok cuts123 [⟨state123_15,exclude123_15⟩,⟨state123_5,exclude123_5⟩,⟨state123_17,exclude123_17⟩] 0x448400700c1400a106000c1044810600448400a400740074003400300a11060400210604007206020601060206011424007400a11420c58009100910448113211320c58113211320448009100911870009100911060051a051a1870051a051a106000910091400a00910091206011321132800211321132206000910091044840000448400a20482048044820480542400a400a0542400340030089400a204820282060400a2028400a400a8001206020482048051a2048051a0091400a0091051a8000051a009120480091054a08120812044818321832054a1832183204480812081211620812081210600c1a0c1a11620c1a0c1a106008120812400a08120812206018321832400818321832206008120812011220420012009108120091011208120191009120420091400a0812081220480c1a0c1a40080c1a0c1a204808120812400904090409044810211021400910211021044804090409400908110811106004090409400904090409106008110811400a04090409206010211021400910211021206004090409009104090409011208110011009108110c09011204090409400a081108112048040904094009040904092048081108114008040904090812050b040b4009050b0509081204090409 (by decide +kernel)
def state123_6 : List Sig := [input 0,input 1,input 3,input 4,signal10,input 6,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_6 : Impossible true (goalAt 123) 7 state123_6.toFinset :=
  node_ok cuts123 [⟨state123_5,exclude123_5⟩,⟨state123_7,exclude123_7⟩] 0x4007400700c10428400300a1400a206000a1042820600428400a40034003106040031060400a20602060106020601142400a400311420c38009100910428113204280c3811320c28042800910091187000910091106020502050187020502050106000910091400a009100912060051a051a8001051a051a206000910091042840000428400a10281028042810280428400a400a400a400a102810281060400a1048400a40058000106010281028400740070089051a1028051a009118380091051a1838051a009110280091052a08120812042818320428052a18320528042808120812116208120812106020422042116220422042106008120812400a0812081220600c1a0c1a40080c1a0c1a206008120812011220420012009108120091011208120191009120420091112a0812081210280c1a0c1a112a0c1a0c1a102808120812400904090409042810211021400910211021042804090409400904090409106020412041400920412041106004090409400a08110811206004090409400904090409206008110811009104090409011208110011009108110c09011204090409400a081108111028040904094009040904091028081108114008040904090812050b040b4009050b0509081204090409 (by decide +kernel)
def state123_2 : List Sig := [input 0,input 1,input 4,input 5,signal10,input 6,signal12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_2 : Impossible true (goalAt 123) 7 state123_2.toFinset :=
  node_ok cuts123 [⟨state123_3,exclude123_3⟩,⟨state123_5,exclude123_5⟩] 0x400a400a00c1102840030089400720480089102820481028400740034003044840030448400a20482048044820480542400a400305421028400210284007042804281028042804284007400a4007400a042804280448400a0448400a40058001044804280428400a400a00a11838009100911028051a051a1838051a051a1028009100910c58009100910448205004480c5820500c48044800910091400a009100912048051a051a8000051a051a2048009100910c38009100910428113204280c3811320c28042800910091112a0812081210280c1a0c1a112a0c1a0c1a102808120812054a08120812044820422042054a20422042044808120812400a0812081220480c1a0c1a40080c1a0c1a204808120812052a08120812042818320428052a18320528042808120812011220420012009108120091011208120191009120420091400908110811102804090409400904090409102808110811400904090409044820412041400920412041044804090409400a08110811204804090409400904090409204808110811400a04090409042810211021400910211021042804090409009104090409011208110011009108110c090112040904094008040904090812050b040b4009050b0509081204090409 (by decide +kernel)
def state123_1 : List Sig := [input 0,input 1,input 3,input 4,input 5,signal10,input 6]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_1 : Impossible true (goalAt 123) 8 state123_1.toFinset :=
  node_ok cuts123 [⟨state123_2,exclude123_2⟩,⟨state123_6,exclude123_6⟩,⟨state123_8,exclude123_8⟩] 0x400a044840030448400a00c1400a00c1400a044880020448400a00c1400300c1400a106004280428400700c1400a00c1400a106080011060400700c104280428400a400a400a00a14010085000910091400700c1205000c14010085020500c48400700c100910091400a400a009100914007400f051a051a400a4010051a051a4007400f0091009140070c3800910091400704281132042840070c3811320c284007042800910091400a044810281028400a00c1400a00c1400a044880000448400a00c11028102840074007400700894007042840070428400a400a102810284007400a4007400d4007051a1028051a400a009118380091400a051a1838051a40070091102800914008014208120812400b00c1204200c140080142204201c1400b00c108120812400a400a08120812400a40160c1a0c1a400a40080c1a0c1a400a4016081208124007052a08120812400a042818320428400a052a1832052840070428081208124007011220420012400b00910812009140060112081201914007009120420091400a112a08120812400a10280c1a0c1a400a112a0c1a0c1a400a102808120812400900c104090409400c014220410041400900c1204100c1400c014204090409400a400a08110811400a400c04090409400a400904090409400a400a081108114007400a04090409400a042810211021400a40091021102140070428040904094007009104090409400c0112081100114009009108110c094007011204090409400a400a08110811400a102804090409400a400904090409400a102808110811400b400804090409400c0812050b040b40084009050b0509400b081204090409 (by decide +kernel)
def state123_13 : List Sig := [input 0,input 1,input 3,input 4,input 5,input 6,signal12]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_13 : Impossible true (goalAt 123) 8 state123_13.toFinset :=
  node_ok cuts123 [⟨state123_2,exclude123_2⟩,⟨state123_14,exclude123_14⟩,⟨state123_8,exclude123_8⟩,⟨state123_18,exclude123_18⟩,⟨state123_19,exclude123_19⟩] 0x400a400a400a00c14002800400a100a1400a4007042804288003800204280428400a400700a100a14003400400a100a1400a04482060044840048001206020604003044800a100a14002401100910091400e400f051a051a40114011051a051a400e400f0091009140030c5800910091400e04482050044840040c5820500c484003044800910091400a0c3800910091400e00a1113200a140110c3811321112400a00a10091009140034003400300894003044840030448400a400a204820484003400a40030542400a042820480428400a00a1401500a1400a042880000428400a00a1204800a1400e051a2048051a400a009140150091400e051a4011051a400a0091204800914002401708120812400340160c1a0c1a401740170c1a0c1a40034016081208124003054a0812081240030448204220424003054a204220424003044808120812400a01a308120812400300a1183200a1400801a318321812400300a108120812400e011220420012400300910812009140010112081201914003009120420091400a401508120812400320480c1a0c1a401340170c1a0c1a40032048081208124002401a081108114014400c04090409401a401a040904094014400c08110811400340040409040940140448204120414004401a204120414003044804090409400a00a1040904094014042810210021400900a110211811400a042804090409400e00910409040940140112081100114011009108110c09400e011204090409400a40150811081140142048040904094014401a04090409400a204808110811400340170409040940140812050b040b4017401a050b05094003081204090409 (by decide +kernel)
def state123_23 : List Sig := [input 0,input 1,input 3,input 4,input 5,input 6,signal18]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_23 : Impossible true (goalAt 123) 8 state123_23.toFinset :=
  node_ok cuts123 [⟨state123_6,exclude123_6⟩,⟨state123_14,exclude123_14⟩,⟨state123_8,exclude123_8⟩,⟨state123_24,exclude123_24⟩,⟨state123_25,exclude123_25⟩] 0x40074007400700c140034003400300a140031060400310604007400720602060400340074003114240004012009100914007400f1132113240124012113211324007400f0091009140031870009100914007106020502050400418702050205040031060009100914007400d009100914007206011321132400740121132113240072060009100914000800400890089400a400a102810288003800210281028400a400a008900894003400400890089400a106020482048400480012048204840031060008900894007400d00890089400a206010281028400a80001028102840072060008900894007051a00890089400a0091183800914012051a183805124007009100890089400040180812081240034016183218324018401818321832400340160812081240031162081208124003106020422042400311622042204240031060081208124007400d081208124003206018321832400b40181832183240032060081208124007011220420012400300910812009140010112081201914003009120420091400a018b0812008b400300890c1a00894008018b0c1a018940030089081200894000401b04090409400c400c10211021401b401b10211021400c400c040904094003400404090409400c1060204120414004401b2041204140031060040904094007400d04090409400c206010211021400c401b1021102140072060040904094007009104090409400c0112081100114012009108110c094007011204090409400a008908110009400c1028040900094009008904090089400a1028081108114003401804090409400c0812050b040b4018401b050b05094003081204090409 (by decide +kernel)
def state123_0 : List Sig := roots 123
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem exclude123_0 : Impossible true (goalAt 123) 9 state123_0.toFinset :=
  node_ok cuts123 [⟨state123_1,exclude123_1⟩,⟨state123_13,exclude123_13⟩,⟨state123_23,exclude123_23⟩] 0x4004106000a100a1400d00c1206000c18002106020601142400400c100a100a1400f085000910091400f00c1205000c1400f085020500c48400f00c100910091400f0c3800910091400f00a1113200a1400f0c3811321112400f00a1009100914004044800890089401500c1204800c18001044820480542400400c100890089400d042800890089401500a1102800a18000042810280428400d00a100890089400f051a00890089400f009118380091400f051a18380512400f0091008900894016014208120812401600c1204200c140160142204201c1401600c108120812401601a308120812401600a1183200a1401601a318321812401600a108120812400f011220420012400f009108120091400f011208120191400f0091204200914016018b0812008b401600890c1a00894016018b0c1a01894016008908120089401900c1040904094019014220410041401900c1204100c14019014204090409401900a1040904094019042810210021401900a1102118114019042804090409400f009104090409400f011208110011400f009108110c09400f0112040904094019008908110009401910280409000940190089040900894019102808110811401640160409040940160812050b040b40164019050b05094016081204090409 (by decide +kernel)
theorem lower123 : Claim 123 10 :=
  fromSearch 67 (by decide +kernel) exclude123_0

open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 127
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0,3,0,4,1,4,0,5,2,5,3,5,0,6,1,6,2,6,3,6,4,6,5,6]
def target (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

-- The three products cover all twelve edges.
def smallCircuit : Circuit := ⟨[
  ⟨.or,[0,1]⟩, ⟨.or,[2,3]⟩, ⟨.or,[3,4]⟩, ⟨.or,[0,6]⟩,
  ⟨.or,[4,6]⟩, ⟨.or,[5,6]⟩, ⟨.or,[9,5]⟩,
  ⟨.and,[13,10]⟩, ⟨.and,[7,11]⟩, ⟨.and,[8,12]⟩,
  ⟨.or,[14,15]⟩, ⟨.or,[17,16]⟩],18⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
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


def sevenInputs : List Sig := roots 127
def sampleSeven (r : Row) (i : Fin 7) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 7 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 7) : Row := Fin.ofNat 128 (1 <<< ([3,4,5,0,0,0,0] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 128 ((1 <<< i.val) ||| (1 <<< ([3,4,5,0,0,0,0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 7, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 7, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 10 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
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

-- Input 2 is essential and vanishes on this restriction. Any computation
-- using at most ten binary gates would give at most nine on the six inputs.
theorem lowerGraph : Impossible true graph 10 sevenInputs.toFinset :=
  (ruleFor 127 lower123 none (by decide +kernel)).property 10 sevenInputs
    (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_10698

open PEqualNP.Outside.L_meta_10698 in
theorem PEqualNP.Outside.L_meta_10698 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o fit _ correct
  exact replaceShort lowerGraph gates o fit correct
