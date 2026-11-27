import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10694

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

-- Setting the missing vertices to zero gives the induced subgraph.
def goalAt (m : Nat) : Sig :=
  let x := fun i => if m.testBit i then input i else zero
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6)

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


def ternaryFix (q t : Nat) : List Move :=
  ((List.range 7).filter fun i => !(q.testBit i)).map fun i =>
    if t.testBit i then (neg (input i),zero,Fin.ofNat 128 (1 <<< i))
    else (zero,input i,Fin.ofNat 128 (1 <<< i))

def ternaryDomain (q t : Nat) : Sig :=
  ((List.range 7).filter fun i => !(q.testBit i)).foldl (fun d i =>
    d &&& (if t.testBit i then input i else neg (input i))) one

def marked (r e : Nat) : Sig :=
  (selected e).foldl (fun w i => w ||| input i) (goalAt r)

def markTests (e : Nat) : List (Sig × Row × Row) :=
  (selected e).map (fun i => (input i,0,Fin.ofNat 128 (1 <<< i)))

def Red (q r e L : Nat) := Lower true (roots q) (marked r e) L

def markLiftTest (q r e L K : Nat) :=
  ((checkLift (fixes r) (marked r e) (roots q) (roots r) (goalAt r) (markTests e) &&
    properB (marked r e)) && properB (goalAt r)) &&
    decide (K ≤ L + ((markTests e).map Prod.fst).toFinset.card)

theorem markLift (q r e K : Nat) {L} (lo : Claim r L)
    (ok : markLiftTest q r e L K = true) : Red q r e K := by
  simp only [markLiftTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have lb := lift_ok ok.1.1.1 (proper_of _ ok.1.1.2) (proper_of _ ok.1.2) lo
  exact fun p b h a => ok.2.trans (lb p b h a)

def markCountTest (q e K : Nat) :=
  (properB (marked 0 e) && checkEssential (marked 0 e) (roots q) (markTests e)) &&
    decide (K ≤ ((markTests e).map Prod.fst).toFinset.card-1)

theorem markCount (q e K : Nat) (ok : markCountTest q e K = true) : Red q 0 e K := by
  simp only [markCountTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have lb := lower_count (u:=true) (proper_of _ ok.1.1) _ ok.1.2
  exact fun p b h a => ok.2.trans (lb p b h a)

def ternaryTest (m q t r e L : Nat) (ex : Option Choice) :=
  (((checkMap (ternaryFix q t) (roots q) (goalAt m) (roots q) (marked r e) &&
    (movedWord (ternaryFix q t) (ternaryDomain q t) == one)) && properB (marked r e)) &&
    (makePool true (ternaryDomain q t) (roots q) ex.toList == some (poolFor q ex))) &&
    decide (ex.toList.length ≤ L)

theorem ternaryCheck (m q t r e : Nat) {L} (lo : Red q r e L) (ex : Option Choice)
    (ok : ternaryTest m q t r e L ex = true) :
    CutGood (goalAt m) (ternaryDomain q t,L-ex.toList.length,poolFor q ex) := by
  simp only [ternaryTest,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  exact cut_good (slice_correct ok.1.1.1.1 ok.1.1.1.2 (proper_of _ ok.1.1.2) lo)
    ex.toList ok.1.2 ok.2

def ternaryRule (m q t r e : Nat) {L} (lo : Red q r e L) (ex : Option Choice)
    (ok : ternaryTest m q t r e L ex = true) : {c : Cut // CutGood (goalAt m) c} :=
  ⟨_, ternaryCheck m q t r e lo ex ok⟩

def initialCountTest (m h L : Nat) :=
  (properB (goalAt m) && checkEssential (goalAt m) (roots m) (tests m h)) &&
    decide (L ≤ ((tests m h).map Prod.fst).toFinset.card-1)

theorem initialCount (m h L : Nat) (yes : initialCountTest m h L = true) : Claim m L := by
  simp only [initialCountTest,Bool.and_eq_true,decide_eq_true_eq] at yes
  have lb := lower_count (u:=true) (proper_of _ yes.1.1) _ yes.1.2
  exact fun p b run out => yes.2.trans (lb p b run out)

def unpack (width dict : Nat) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,data =>
    let i := data % (1 <<< width)
    ((dict >>> (16*i)) % 65536) + ((unpack width dict n (data >>> width)) <<< 16)

abbrev Ex (m k : Nat) (ws : List Sig) := Impossible true (goalAt m) k ws.toFinset

theorem certify {m k ws} (cuts : Cuts (goalAt m)) (links : Links (goalAt m) (k-1))
    (data : Nat) (ok : checkNode (goalAt m) k ws cuts links data = true) : Ex m k ws :=
  node_ok cuts links data ok

abbrev u0 := input 0
abbrev u1 := input 1
abbrev u2 := input 2
abbrev u3 := input 3
abbrev u4 := input 4
abbrev u5 := input 5
abbrev u6 := input 6
abbrev v7 : Sig := 0xffffffffffccffcc
abbrev v8 : Sig := 0xffffffffffccffccffffffffffccffcc
abbrev v9 : Sig := 0xffccffcc00000000ffccffcc
abbrev v10 : Sig := 0xffffffff00000000ffccffcc
abbrev v11 : Sig := 0xffffffffffffffffffccffccffccffcc
abbrev v12 : Sig := 0xffccffccffccffcc
abbrev v13 : Sig := 0xffffffffff00ff00ffffffffff00ff00
abbrev v14 : Sig := 0xffffffffccccccccffffffffcccccccc
abbrev v15 : Sig := 0xffccffccffccffccffccffccffccffcc
abbrev v16 : Sig := 0xffffffffffffffffff00ff00ff00ff00
abbrev v17 : Sig := 0xffffffffffffffffcccccccccccccccc
abbrev v18 : Sig := 0xff00ff00ff00ff00ff00ff00cc00cc
abbrev v19 : Sig := 0xffffffffffffffffffffffffcccccccc
abbrev v20 : Sig := 0xffffffffcccccccc
abbrev v21 : Sig := 0xffffffffffffffffffffffff00000000
abbrev v22 : Sig := 0xff00ff00cc00cc00ff00ff00cc00cc
abbrev v23 : Sig := 0xff00ff00ff00ff00cc00cc00cc00cc
abbrev v24 : Sig := 0xffffffff00000000cccccccc
abbrev v25 : Sig := 0x33333333333333333333333333003300
abbrev v26 : Sig := 0xffffffffffffffffffffffffff00ff00
abbrev v27 : Sig := 0xffffffffff00ff00
abbrev v28 : Sig := 0x33333333330033003333333333003300
abbrev v29 : Sig := 0x33333333333333333300330033003300
abbrev v30 : Sig := 0xffffffff00000000ff00ff00
abbrev v31 : Sig := 0x33333333333333333333333300000000
abbrev v32 : Sig := 0xff00ff00ff00ff00ff00ff00000000
abbrev v33 : Sig := 0x33333333000000003333333300000000
abbrev v34 : Sig := 0xff00ff0000000000ff00ff00000000
abbrev v35 : Sig := 0xfafa0000fafa0000fafa0000fafa
abbrev v36 : Sig := 0xfafafafafafafafafafafafafafafafa
abbrev v37 : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
abbrev v38 : Sig := 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a
abbrev v39 : Sig := 0xffffaaaaffffaaaaffffaaaaffffaaaa
abbrev v40 : Sig := 0xaaaa0000aaaa0000aaaa0000aaaa
abbrev v41 : Sig := 0xfffff0f0fffff0f0fffff0f0fffff0f0
abbrev v42 : Sig := 0xfefefefefefefefef0f0f0f0f0f0f0f0
abbrev v43 : Sig := 0xffeeffeeffeeffeeff00ff00ff00ff00
abbrev v44 : Sig := 0xeeeeeeeeeeeeeeee0000000000000000
abbrev v45 : Sig := 0xf0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e
abbrev v46 : Sig := 0xff00ff00ff00ff00ee00ee00ee00ee
abbrev v47 : Sig := 0xffffffffffffffffeeeeeeeeeeeeeeee
abbrev v48 : Sig := 0xeeeeeeeeeeeeeeee
abbrev v49 : Sig := 0x11111111111111110000000000000000
abbrev v50 : Sig := 0xffffffffffffffffaaaaaaaaaaaaaaaa
abbrev v51 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
abbrev v52 : Sig := 0xffeeffeeffeeffeecccccccccccccccc
abbrev v53 : Sig := 0xfffafffafffafffaf0f0f0f0f0f0f0f0
abbrev v54 : Sig := 0xffaaffaaffaaffaa0000000000000000
abbrev v55 : Sig := 0x33333333333333333322332233223322
abbrev v56 : Sig := 0xf0f0f0f0f0f0f0f0f0a0f0a0f0a0f0a
abbrev v57 : Sig := 0xffffffffffffffffffaaffaaffaaffaa
abbrev v58 : Sig := 0xffaaffaaffaaffaa
abbrev v59 : Sig := 0x550055005500550000000000000000
abbrev v60 : Sig := 0xffaaffaaffaaffaaffaaffaaffaaffaa
abbrev v61 : Sig := 0x55555555555555550000000000000000
abbrev v62 : Sig := 0x33333333333333332222222222222222
abbrev v63 : Sig := 0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a
abbrev v64 : Sig := 0xff00ff00ff00ff00aa00aa00aa00aa
abbrev v65 : Sig := 0xdd00dd00dd00dd00cc00cc00cc00cc
abbrev v66 : Sig := 0xddddddddddddddddcccccccccccccccc
abbrev v67 : Sig := 0x33113311331133113300330033003300
abbrev v68 : Sig := 0xff55ff55ff55ff55ff00ff00ff00ff00
abbrev v69 : Sig := 0xfffcfffcfffcfffcff00ff00ff00ff00
abbrev v70 : Sig := 0xfefefefefefefefeaaaaaaaaaaaaaaaa
abbrev v71 : Sig := 0xfcfcfcfcfcfcfcfc0000000000000000
abbrev v72 : Sig := 0x55555555555555555454545454545454
abbrev v73 : Sig := 0xff00ff00ff00ff00fc00fc00fc00fc
abbrev v74 : Sig := 0xfffffffffffffffffcfcfcfcfcfcfcfc
abbrev v75 : Sig := 0xfcfcfcfcfcfcfcfc
abbrev v76 : Sig := 0x3030303030303030000000000000000
abbrev v77 : Sig := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
abbrev v78 : Sig := 0xfffffffffffffffff0f0f0f0f0f0f0f0
abbrev v79 : Sig := 0x33333333333333330000000000000000
abbrev v80 : Sig := 0x55555555555555554444444444444444
abbrev v81 : Sig := 0xf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c
abbrev v82 : Sig := 0xb0b0b0b0b0b0b0b0a0a0a0a0a0a0a0a
abbrev v83 : Sig := 0xbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaa
abbrev v84 : Sig := 0x51515151515151515050505050505050
abbrev v85 : Sig := 0xf3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0
abbrev v86 : Sig := 0xfffafffafffafffaaaaaaaaaaaaaaaaa
abbrev v87 : Sig := 0xfffcfffcfffcfffccccccccccccccccc
abbrev v88 : Sig := 0xfff0fff0fff0fff00000000000000000
abbrev v89 : Sig := 0x55555555555555555550555055505550
abbrev v90 : Sig := 0x33333333333333333330333033303330
abbrev v91 : Sig := 0xfffffffffffffffffff0fff0fff0fff0
abbrev v92 : Sig := 0xfff0fff0fff0fff0
abbrev v93 : Sig := 0xf000f000f000f0000000000000000
abbrev v94 : Sig := 0xfff0fff0fff0fff0fff0fff0fff0fff0
abbrev v95 : Sig := 0xf0f0f0f0f0f0f0f0000000000000000
abbrev v96 : Sig := 0x55555555555555555050505050505050
abbrev v97 : Sig := 0x33333333333333333030303030303030
abbrev v98 : Sig := 0xff00ff00ff00ff00f000f000f000f0
abbrev v99 : Sig := 0xcf00cf00cf00cf00cc00cc00cc00cc
abbrev v100 : Sig := 0xcfcfcfcfcfcfcfcfcccccccccccccccc
abbrev v101 : Sig := 0x33033303330333033300330033003300
abbrev v102 : Sig := 0xff0fff0fff0fff0fff00ff00ff00ff00
abbrev v103 : Sig := 0xff00ff00ff00ff0000000000000000
abbrev v104 : Sig := 0x55555555555555555500550055005500
abbrev v105 : Sig := 0xf0f0f0f0f0f0f0f0f000f000f000f00
abbrev v106 : Sig := 0xa0f0a0f0a0f0a0f0a0a0a0a0a0a0a0a
abbrev v107 : Sig := 0xaaffaaffaaffaaffaaaaaaaaaaaaaaaa
abbrev v108 : Sig := 0x50555055505550555050505050505050
abbrev v109 : Sig := 0xf0fff0fff0fff0fff0f0f0f0f0f0f0f0
abbrev v110 : Sig := 0xffffffff0000000000000000
abbrev v111 : Sig := 0xff22ff22ff22ff22ff22ff22ff22ff22
abbrev v112 : Sig := 0x22222222222222222222222222222222
abbrev v113 : Sig := 0xffffffffcc00cc00ffffffffcc00cc00
abbrev v114 : Sig := 0x33ff33ff0000000033ff33ff00000000
abbrev v115 : Sig := 0xcc00cc00cc00cc00cc00cc00cc00cc00
abbrev v116 : Sig := 0xeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaa
abbrev v117 : Sig := 0xcc00cc00cc00cc00cc00cc00cc00cc
abbrev v118 : Sig := 0x33003300330033003300330033003300
abbrev v119 : Sig := 0xffccffccff00ff00ffccffccff00ff00
abbrev v120 : Sig := 0x33003300ff00ff0033003300ff00ff00
abbrev v121 : Sig := 0xeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaa
abbrev v122 : Sig := 0xcccccccc00000000cccccccc00000000
abbrev v123 : Sig := 0xff00ff00cc00cc00ff00ff00cc00cc00
abbrev v124 : Sig := 0xcccccccc00000000cccccccc
abbrev v125 : Sig := 0xffaaffaaaaaaaaaaffaaffaaaaaaaaaa
abbrev v126 : Sig := 0xffccffccccccccccffccffcccccccccc
abbrev v127 : Sig := 0xcc00cccccccccc00cc00cccccccccc
abbrev v128 : Sig := 0xff00ff0000000000ff00ff0000000000
abbrev v129 : Sig := 0xcccccccccc00cc00cccccccccc00cc00
abbrev v130 : Sig := 0xff00ff0000000000ff00ff00
abbrev v131 : Sig := 0xfafa0000fafa0000fafa0000fafa0000
abbrev v132 : Sig := 0xffffffff0a0a0a0affffffff0a0a0a0a
abbrev v133 : Sig := 0x3b3b3b3b0a0a0a0a3b3b3b3b0a0a0a0a
abbrev v134 : Sig := 0xaff0aff0a0a0a0a0aff0aff0a0a0a0a
abbrev v135 : Sig := 0xcceecceecceecceecceecceecceeccee
abbrev v136 : Sig := 0xaa00aa00aa00aa00aa00aa00aa00aa
abbrev v137 : Sig := 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0
abbrev v138 : Sig := 0xffffffff0000aaaaffffffff0000aaaa
abbrev v139 : Sig := 0x3333bbbb0000aaaa3333bbbb0000aaaa
abbrev v140 : Sig := 0xffaaff0000aaaa00ffaaff0000aaaa
abbrev v141 : Sig := 0xeeeeeeeecccccccceeeeeeeecccccccc
abbrev v142 : Sig := 0xfafafafaf0f0f0f0fafafafaf0f0f0f0
abbrev v143 : Sig := 0xffaaffaaff00ff00ffaaffaaff00ff00
abbrev v144 : Sig := 0xffffaaaaffff0000ffffaaaaffff0000
abbrev v145 : Sig := 0xaaaaaaaa00000000aaaaaaaa00000000
abbrev v146 : Sig := 0xffffffffaaaaaaaaffffffffaaaaaaaa
abbrev v147 : Sig := 0xaaaaaaaa00000000aaaaaaaa
abbrev v148 : Sig := 0x55555555000000005555555500000000
abbrev v149 : Sig := 0xffffccccffffccccffffccccffffcccc
abbrev v150 : Sig := 0xfafaaaaafafaaaaafafaaaaafafaaaaa
abbrev v151 : Sig := 0xf0f00000f0f00000f0f00000f0f00000
abbrev v152 : Sig := 0xffffffffa0a0a0a0ffffffffa0a0a0a0
abbrev v153 : Sig := 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0
abbrev v154 : Sig := 0x5f5f00005f5f00005f5f00005f5f0000
abbrev v155 : Sig := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
abbrev v156 : Sig := 0x50505050505050505050505050505050
abbrev v157 : Sig := 0xffffffffaaaa0000ffffffffaaaa0000
abbrev v158 : Sig := 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0
abbrev v159 : Sig := 0x5050f0f05050f0f05050f0f05050f0f0
abbrev v160 : Sig := 0xaaaa0000aaaa0000aaaa0000aaaa0000
abbrev v161 : Sig := 0x55550000555500005555000055550000
abbrev v162 : Sig := 0xfffffffff0f00000fffffffff0f00000
abbrev v163 : Sig := 0xa0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa
abbrev v164 : Sig := 0xf0f00000f0f00000f0f00000f0f0
abbrev v165 : Sig := 0xf0f00000f0f00000f0f00000f0f0000
abbrev v166 : Sig := 0xbbbbbbbbaaaaaaaabbbbbbbbaaaaaaaa
abbrev v167 : Sig := 0xfffffffff0f0f0f0fffffffff0f0f0f0
abbrev v168 : Sig := 0xffff0f0fffff0000ffff0f0fffff0000
abbrev v169 : Sig := 0xf0f0f0f000000000f0f0f0f00000000
abbrev v170 : Sig := 0xffffff00ffffff00ffffff00ffffff00
abbrev v171 : Sig := 0xaaffaaffaaaaaaaaaaffaaffaaaaaaaa
abbrev v172 : Sig := 0xffffffffffff0000ffffffffffff0000
abbrev v173 : Sig := 0xf0f0fffff0f0f0f0f0f0fffff0f0f0f0
abbrev v174 : Sig := 0xffff000000000000ffff00000000
abbrev v175 : Sig := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
abbrev v176 : Sig := 0xffffffffffffffff0000fafa0000fafa
abbrev v177 : Sig := 0xfcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0
abbrev v178 : Sig := 0xffffffffffffffffcc00cc00cc00cc00
abbrev v179 : Sig := 0x33ff33ff33ff33ff0000000000000000
abbrev v180 : Sig := 0xcc00fefacc00fefacc00fefacc00fefa
abbrev v181 : Sig := 0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0
abbrev v182 : Sig := 0xffccffccffccffccff00ff00ff00ff00
abbrev v183 : Sig := 0x3300330033003300ff00ff00ff00ff00
abbrev v184 : Sig := 0xccccfefeccccfefe0000fafa0000fafa
abbrev v185 : Sig := 0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa
abbrev v186 : Sig := 0xcccccccccccccccc0000000000000000
abbrev v187 : Sig := 0xff00ff00ff00ff00cc00cc00cc00cc00
abbrev v188 : Sig := 0xcccccccccccccccc
abbrev v189 : Sig := 0x3333fbfb3333fbfb0000fafa0000fafa
abbrev v190 : Sig := 0xff00fffaff00fffa0000fafa0000fafa
abbrev v191 : Sig := 0xffaaffaaffaaffaaaaaaaaaaaaaaaaaa
abbrev v192 : Sig := 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0
abbrev v193 : Sig := 0xffccffccffccffcccccccccccccccccc
abbrev v194 : Sig := 0xcc00cc00cc00cccccccccccccccccc
abbrev v195 : Sig := 0xff00ff00ff00ff000000000000000000
abbrev v196 : Sig := 0xcccccccccccccccccc00cc00cc00cc00
abbrev v197 : Sig := 0xff00ff00ff00ff00
abbrev v198 : Sig := 0xfffaff00fffaff0000fafa0000fafa
abbrev v199 : Sig := 0xffffffffffffffffffff0000ffff0000
abbrev v200 : Sig := 0xfffffffffffffffffafafafafafafafa
abbrev v201 : Sig := 0xffff0000ffff0000fafa0000fafa
abbrev v202 : Sig := 0xffffffffffffffffa0a0a0a0a0a0a0a0
abbrev v203 : Sig := 0xfbfbfbfbfbfbfbfbfafafafafafafafa
abbrev v204 : Sig := 0xfafffafffafffafffafafafafafafafa
abbrev v205 : Sig := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
abbrev v206 : Sig := 0xf5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0
abbrev v207 : Sig := 0xffff5555ffff5555ffff0000ffff0000
abbrev v208 : Sig := 0x54545454545454545454545454545454
abbrev v209 : Sig := 0xffff3333ffff3333ffff0000ffff0000
abbrev v210 : Sig := 0x55505550555055505550555055505550
abbrev v211 : Sig := 0xafafafafafafafafaaaaaaaaaaaaaaaa
abbrev v212 : Sig := 0xffff0f0fffff0f0fffff0000ffff0000
abbrev v213 : Sig := 0xffff00ffffff00ffffff0000ffff0000
abbrev v214 : Sig := 0xffffffff00000000ffeeffee
abbrev v215 : Sig := 0xffffffffffffffffffeeffeeffeeffee
abbrev v216 : Sig := 0x55555555555555555544554455445544
abbrev v217 : Sig := 0xffeeffeeffeeffeeffeeffeeffeeffee
abbrev v218 : Sig := 0xaaffaaffaaffaaffaaeeaaeeaaeeaaee
abbrev v219 : Sig := 0xbbbbbbbbbbbbbbbbbbaabbaabbaabbaa
abbrev v220 : Sig := 0x44444444444444444444444444444444
abbrev v221 : Sig := 0x55005500550055005500550055005500
abbrev v222 : Sig := 0xfffcfffcfffcfffcfffcfffcfffcfffc
abbrev v223 : Sig := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
abbrev v224 : Sig := 0xf000f000f000f000f000f000f000f00
def c21 : Cuts (goalAt 21) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p21x0 : Ex 21 3 (roots 21) :=
  certify c21 [] (unpack 3 0x8810a04028402810a100890 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l21 : Claim 21 4 := fromSearch 2 (by decide +kernel) p21x0

def c42 : Cuts (goalAt 42) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p42x0 : Ex 42 3 (roots 42) :=
  certify c42 [] (unpack 3 0x110214080508050214201120 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l42 : Claim 42 4 := fromSearch 1052720 (by decide +kernel) p42x0

def c69 : Cuts (goalAt 69) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p69x0 : Ex 69 3 (roots 69) :=
  certify c69 [] (unpack 3 0x2081220402840281224020c0 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l69 : Claim 69 4 := fromSearch 2 (by decide +kernel) p69x0

def c74 : Cuts (goalAt 74) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p74x0 : Ex 74 3 (roots 74) :=
  certify c74 [] (unpack 3 0x210224080508050224402140 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l74 : Claim 74 4 := fromSearch 16781360 (by decide +kernel) p74x0

def c97 : Cuts (goalAt 97) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p97x0 : Ex 97 3 (roots 97) :=
  certify c97 [] (unpack 3 0x2081302010a01081304020c0 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l97 : Claim 97 4 := fromSearch 5 (by decide +kernel) p97x0

def c98 : Cuts (goalAt 98) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p98x0 : Ex 98 3 (roots 98) :=
  certify c98 [] (unpack 3 0x210230201120110230402140 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l98 : Claim 98 4 := fromSearch 17825872 (by decide +kernel) p98x0

def c104 : Cuts (goalAt 104) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p104x0 : Ex 104 3 (roots 104) :=
  certify c104 [] (unpack 3 0x240830201420140830402440 36 0x895361952aec128b1b4116d3440) (by decide +kernel)
theorem l104 : Claim 104 4 := fromSearch 53497856 (by decide +kernel) p104x0

def c39 : Cuts (goalAt 39) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p39x0 : Ex 39 3 (roots 39) :=
  certify c39 [] (unpack 4 0x1306038310811102028110a0112003860284 24 0x468456562474656540430210) (by decide +kernel)
theorem l39 : Claim 39 4 := fromSearch 82 (by decide +kernel) p39x0

theorem l43 : Claim 43 5 := fromLift 5 1 4149 l42 (by decide +kernel)

def c45 : Cuts (goalAt 45) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p45x0 : Ex 45 3 (roots 45) :=
  certify c45 [] (unpack 4 0x160c0689140810811420068c0284028110a0 24 0x656515811471565224321210) (by decide +kernel)
theorem l45 : Claim 45 4 := fromSearch 20482 (by decide +kernel) p45x0

def c51 : Cuts (goalAt 51) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p51x0 : Ex 51 3 (roots 51) :=
  certify c51 [] (unpack 4 0x1912098310811102088110a0112009920890 24 0x468456562474656540430210) (by decide +kernel)
theorem l51 : Claim 51 4 := fromSearch 84 (by decide +kernel) p51x0

theorem l53 : Claim 53 5 := fromLift 5 32 2 l21 (by decide +kernel)

def c57 : Cuts (goalAt 57) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p57x0 : Ex 57 3 (roots 57) :=
  certify c57 [] (unpack 4 0x1c180c8910811408088110a014200c980890 24 0x468456562474656540430210) (by decide +kernel)
theorem l57 : Claim 57 4 := fromSearch 20484 (by decide +kernel) p57x0

theorem l71 : Claim 71 5 := fromLift 5 2 98 l69 (by decide +kernel)

theorem l75 : Claim 75 5 := fromLift 5 1 4150 l74 (by decide +kernel)

theorem l77 : Claim 77 5 := fromLift 5 8 24578 l69 (by decide +kernel)

theorem l78 : Claim 78 5 := fromLift 5 4 16782896 l74 (by decide +kernel)

def c83 : Cuts (goalAt 83) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p83x0 : Ex 83 3 (roots 83) :=
  certify c83 [] (unpack 4 0x2912098320812102088120c0214009920890 24 0x468456562474656540430210) (by decide +kernel)
theorem l83 : Claim 83 4 := fromSearch 100 (by decide +kernel) p83x0

theorem l85 : Claim 85 5 := fromLift 5 64 2 l21 (by decide +kernel)

def c86 : Cuts (goalAt 86) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p86x0 : Ex 86 3 (roots 86) :=
  certify c86 [] (unpack 4 0x29122240210222040b060a0421400b120a10 24 0x368656563037656523432010) (by decide +kernel)
theorem l86 : Claim 86 4 := fromSearch 16909408 (by decide +kernel) p86x0

def c89 : Cuts (goalAt 89) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p89x0 : Ex 89 3 (roots 89) :=
  certify c89 [] (unpack 4 0x2c180c8920812408088120c024400c980890 24 0x468456562474656540430210) (by decide +kernel)
theorem l89 : Claim 89 4 := fromSearch 24580 (by decide +kernel) p89x0

def c92 : Cuts (goalAt 92) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p92x0 : Ex 92 3 (roots 92) :=
  certify c92 [] (unpack 4 0x2c180e0c220424080a04224024400e180a10 24 0x468456562474656540430210) (by decide +kernel)
theorem l92 : Claim 92 4 := fromSearch 33711104 (by decide +kernel) p92x0

theorem l99 : Claim 99 5 := fromLift 5 2 85 l97 (by decide +kernel)

theorem l101 : Claim 101 5 := fromLift 5 32 2 l69 (by decide +kernel)

theorem l102 : Claim 102 5 := fromLift 5 4 17827408 l98 (by decide +kernel)

theorem l105 : Claim 105 5 := fromLift 5 8 20485 l97 (by decide +kernel)

def c106 : Cuts (goalAt 106) := [
  ternaryRule 106 98 0 98 0 l98 none (by decide +kernel),
  ternaryRule 106 74 0 74 0 l74 none (by decide +kernel),
  ternaryRule 106 42 0 42 0 l42 none (by decide +kernel),
  ternaryRule 106 104 0 104 0 l104 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x0 : Ex 106 3 [v7,u5,u1,u3] :=
  certify c106 [] (unpack 3 0x11201408050205082408302011022102 24 0xa75b2f38cae8803288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x1 : Ex 106 4 [v8,u5,u1,u3,u6] :=
  certify c106 [⟨_,p106x0⟩] (unpack 4 0x2440240805021120140805082140302011023040800021024002 31 0xa1baa48ac1b17a7a948476415431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x2 : Ex 106 4 [v9,u5,u1,u3,u6] :=
  certify c106 [] (unpack 3 0x24082102302005021420050811201102 37 0x4de46e6f9450a255d76bac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x3 : Ex 106 3 [v10,u6,u1,u3] :=
  certify c106 [] (unpack 3 0x11202408050205081408302021021102 24 0xa75b2f38cae8803088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x4 : Ex 106 4 [v11,u6,u1,u3,u5] :=
  certify c106 [⟨_,p106x3⟩] (unpack 4 0x3040800040011420140811020502214024082102050811203020 31 0x73c7b77a67866346978726265343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x5 : Ex 106 4 [v12,u6,u1,u3,u5] :=
  certify c106 [] (unpack 4 0x14083020110230401420050224401120050821402102 37 0x879858a559458a82525129128787565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x6 : Ex 106 3 [v13,v14,v15,u6] :=
  certify c106 [] (unpack 3 0x30201120400105084000210224080502 24 0x5d69a5185454103088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x7 : Ex 106 4 [v14,u5,v15,u3,u6] :=
  certify c106 [⟨_,p106x6⟩] (unpack 4 0x142080000502400011204001302011021408240821020508 34 0x9129b94a90998151747460706415431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x8 : Ex 106 3 [v16,v17,v15,u5] :=
  certify c106 [] (unpack 4 0x1408304011022140112014204002050805024000 24 0x977271917876252314131210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x9 : Ex 106 4 [v17,u6,v15,u3,u5] :=
  certify c106 [⟨_,p106x8⟩] (unpack 4 0x1408142080000502400030401102214021021120050840022408 34 0x6476c66296c9b94a929986765454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x10 : Ex 106 4 [v13,u5,v15,u1,u6] :=
  certify c106 [⟨_,p106x6⟩] (unpack 4 0x112080000508400314204001140830201102210224080502 34 0x2129b95a90908242757560706524230210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x11 : Ex 106 4 [v16,u6,v15,u1,u5] :=
  certify c106 [⟨_,p106x8⟩] (unpack 4 0x1408112080000508400330401102244024081420050240022102 34 0x647662c26c69b94a929286765454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x12 : Ex 106 5 [v15,u1,u3,u5,u6] :=
  certify c106 [⟨_,p106x1⟩,⟨_,p106x2⟩,⟨_,p106x4⟩,⟨_,p106x5⟩,⟨_,p106x7⟩,⟨_,p106x9⟩,⟨_,p106x10⟩,⟨_,p106x11⟩] (unpack 5 0x8007800614208005240880041408050240030508400011208003800221024002302080018000110240013040 99 0x1442380e5014e2145ce3acf1ac4ee73dce12c4fa3c4e72db33b0f16c4f23c58c1304f6bc5013d8c72dcd6316b5ad6a398e5494e8394c5104402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x13 : Ex 106 3 [v18,u6,u1,u5] :=
  certify c106 [] (unpack 3 0x30201408110211200508240821020502 24 0xa7dbab28b1a8803088) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x14 : Ex 106 4 [v19,u6,u1,u5,u3] :=
  certify c106 [⟨_,p106x13⟩] (unpack 4 0x2440800040001408142005021102214030202102112005082408 31 0x768773c7b77a6346978726265343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x15 : Ex 106 4 [v20,u6,u1,u5,u3] :=
  certify c106 [] (unpack 4 0x14202408050224401408110230400508112021402102 37 0x85a8879859458a82525129198787565433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x16 : Ex 106 3 [v21,v17,v14,u3] :=
  certify c106 [] (unpack 4 0x24402140142005020508112014084002240811024001 24 0xa77987757187665314131210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x17 : Ex 106 4 [v17,u6,v14,u5,u3] :=
  certify c106 [⟨_,p106x16⟩] (unpack 4 0x2440142005021408800011024001214021020508112040022408 34 0xa7bacaa5a4cabaa2974872776454133210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x18 : Ex 106 4 [v21,u6,v14,u1,u3] :=
  certify c106 [⟨_,p106x16⟩] (unpack 4 0x2440142005020508800011204003304030201408110240022102 34 0xcaaca4caa2baaba7974872726454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x19 : Ex 106 4 [v22,u3,u1,u5,u6] :=
  certify c106 [] (unpack 3 0x30202102240811021408112005080502 37 0x4de6b8c70a255d738e6bac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x20 : Ex 106 4 [v13,u3,v14,u1,u6] :=
  certify c106 [⟨_,p106x6⟩] (unpack 4 0x5088000112040031420140840000502210224081102 34 0x2121a86980807212505041212565430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x21 : Ex 106 5 [v14,u1,u5,u3,u6] :=
  certify c106 [⟨_,p106x14⟩,⟨_,p106x15⟩,⟨_,p106x7⟩,⟨_,p106x17⟩,⟨_,p106x18⟩,⟨_,p106x1⟩,⟨_,p106x19⟩,⟨_,p106x20⟩] (unpack 5 0x8007800680054000244080043020140880038002050214201102400311204001050880018000210240022408 99 0x16b144408804b5996b4a9355292b5d23192d735ae518bd291184f83c494990e11c404004d100e059d6a4296c5a8e74992839cc6318c5104402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x22 : Ex 106 4 [v23,u3,u1,u6,u5] :=
  certify c106 [] (unpack 4 0x3040142011021408210224081120214005080502 37 0x7597767154512118676745457676545431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x23 : Ex 106 4 [v16,u3,v17,u1,u5] :=
  certify c106 [⟨_,p106x8⟩] (unpack 4 0x5088000214040032102140811022440240840000502 34 0x544546544545a839868676261545423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x24 : Ex 106 4 [v24,u5,u1,u6,u3] :=
  certify c106 [] (unpack 4 0x24401408050214202408210230200508214011201102 37 0x85a8879887815451291995458787565433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x25 : Ex 106 4 [v21,u5,v17,u1,u3] :=
  certify c106 [⟨_,p106x16⟩] (unpack 4 0x50214200508800021404003240821023040302040011102 34 0xabbabaabb4abbaba973874746454123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x26 : Ex 106 5 [v17,u1,u6,u3,u5] :=
  certify c106 [⟨_,p106x9⟩,⟨_,p106x17⟩,⟨_,p106x4⟩,⟨_,p106x22⟩,⟨_,p106x23⟩,⟨_,p106x14⟩,⟨_,p106x24⟩,⟨_,p106x25⟩] (unpack 5 0x8007304080068005400180042440800380024000240880011102140880000502142021024003214040020508 99 0x52925095a50894cd088a5324a628420c6495282a126304c623c907bc86338a5618cd319852846b489281a12a4a048308c5194c731445204831082108420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x27 : Ex 106 3 [v25,u6,u3,u5] :=
  certify c106 [] (unpack 3 0x30201408110211200502050824082102 24 0xa3d77360b5758d3408) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x28 : Ex 106 4 [v26,u6,u3,u5,u1] :=
  certify c106 [⟨_,p106x27⟩] (unpack 4 0x1120214080000508400311021408244030202408142005022102 31 0x96c9c99c93b9a998634676265343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x29 : Ex 106 4 [v27,u6,u3,u5,u1] :=
  certify c106 [] (unpack 4 0x11202102050821401102140830400502142024402408 37 0x85a8a88a97985949525129198787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x30 : Ex 106 3 [v21,v16,v13,u1] :=
  certify c106 [] (unpack 4 0x2140112005080502142011024002210214084001 24 0x977987787187665344132210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x31 : Ex 106 4 [v16,u6,v13,u5,u1] :=
  certify c106 [⟨_,p106x30⟩] (unpack 4 0x2140050811201102800014084001244024080502142040022102 34 0xb7abcbbcb4cbabba974872776454133210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x32 : Ex 106 4 [v21,u6,v13,u3,u1] :=
  certify c106 [⟨_,p106x30⟩] (unpack 4 0x2140112005080502800014204000304030201102140840022102 34 0xbaabcaaca4caa2ba974872726454133210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x33 : Ex 106 4 [v28,u1,u3,u5,u6] :=
  certify c106 [] (unpack 3 0x30202408210214081102142005020508 37 0x3bd9b8970dd738e1456bac71a288) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x34 : Ex 106 5 [v13,u3,u5,u1,u6] :=
  certify c106 [⟨_,p106x28⟩,⟨_,p106x29⟩,⟨_,p106x31⟩,⟨_,p106x32⟩,⟨_,p106x1⟩,⟨_,p106x33⟩,⟨_,p106x10⟩,⟨_,p106x20⟩] (unpack 5 0x8007800611208005800405084003214080033020110280021408400014204001050280018000240840022102 99 0x200138407005081a104cd359cd30822733c214840f39c9ce7c211841ee731290180c6b0090190b11c404004a100e04992839cc6318c5104402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x35 : Ex 106 4 [v29,u1,u3,u6,u5] :=
  certify c106 [] (unpack 4 0x3040112014081102240821021420244005020508 37 0x6496167114516767454512187676545431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x36 : Ex 106 4 [v30,u5,u3,u6,u1] :=
  certify c106 [] (unpack 4 0x21401102050811202102240830200502244014201408 37 0x85a8788797985451291995498787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x37 : Ex 106 4 [v21,u5,v16,u3,u1] :=
  certify c106 [⟨_,p106x30⟩] (unpack 4 0x112005080502800024404000210224083040302040011102 34 0xbaabbaababbaa4ba973874746554123210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x38 : Ex 106 5 [v16,u3,u6,u1,u5] :=
  certify c106 [⟨_,p106x31⟩,⟨_,p106x4⟩,⟨_,p106x35⟩,⟨_,p106x11⟩,⟨_,p106x23⟩,⟨_,p106x28⟩,⟨_,p106x36⟩,⟨_,p106x37⟩] (unpack 5 0x8007304080068005400180042140800380028001050840031120210280001408110224084000244040020502 99 0x4a525095a50852cca5898d231a2529565324c5494cb5856b23c907bc8b58d2912d6e5ac494b52952d6c5ad4948468308c5194c731445204831082108420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x39 : Ex 106 4 [v31,u1,u5,u6,u3] :=
  certify c106 [] (unpack 4 0x24400508142005022408302021021408304011021120 37 0x74a7718714517978454912198787645431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x40 : Ex 106 4 [v32,u3,u5,u6,u1] :=
  certify c106 [] (unpack 4 0x21400502112005082102302024081102304014081420 37 0x74a7718797981451954992198787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x41 : Ex 106 5 [v21,u5,u6,u1,u3] :=
  certify c106 [⟨_,p106x14⟩,⟨_,p106x39⟩,⟨_,p106x18⟩,⟨_,p106x25⟩,⟨_,p106x28⟩,⟨_,p106x40⟩,⟨_,p106x32⟩,⟨_,p106x37⟩] (unpack 5 0x8007244080068005800440000502142080032140800280018000112040030508210230204001304040021102 99 0x5ef25095a508f78def139d37384f7c9ef839d173a0f7bd0f718cf33dc8404c62308d6308630cc61210b42046328c63a109420e630465204831082108420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p106x42 : Ex 106 6 (roots 106) :=
  certify c106 [⟨_,p106x12⟩,⟨_,p106x21⟩,⟨_,p106x26⟩,⟨_,p106x34⟩,⟨_,p106x38⟩,⟨_,p106x41⟩] (unpack 5 0x8005304030208004244080038002214021024002240880011102400114084003800005080502400014201120 96 0x64d294368dace936352962c631362d92e2b6346341c631242981c27424636348d32dcb7b5cd62c844248931c075240941c8410c033048428c8310400) (by decide +kernel)
theorem l106 : Claim 106 7 := fromSearch 17829936 (by decide +kernel) p106x42

theorem l108 : Claim 108 5 := fromLift 5 4 36722176 l104 (by decide +kernel)

theorem l113 : Claim 113 5 := fromLift 5 16 4 l97 (by decide +kernel)

def c116 : Cuts (goalAt 116) := [
  ]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p116x0 : Ex 116 3 (roots 116) :=
  certify c116 [] (unpack 4 0x38301a243020220430401a300a100a042240 24 0x656515811471565224321210) (by decide +kernel)
theorem l116 : Claim 116 4 := fromSearch 39977984 (by decide +kernel) p116x0

theorem l31 : Claim 31 6 := fromLift 6 10 4146 l21 (by decide +kernel)

theorem r43x42x1x5 : Red 43 42 1 5 := markLift 43 42 1 5 l42 (by decide +kernel)
def c47 : Cuts (goalAt 47) := [
  ternaryRule 47 42 0 42 0 l42 none (by decide +kernel),
  ternaryRule 47 43 0 43 0 l43 none (by decide +kernel),
  ternaryRule 47 43 4 42 1 r43x42x1x5 none (by decide +kernel),
  ternaryRule 47 39 0 39 0 l39 none (by decide +kernel),
  ternaryRule 47 45 0 45 0 l45 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p47x0 : Ex 47 5 [v15,u1,u3,u0,u2,u5] :=
  certify c47 [] (unpack 4 0x1306070610a00583038602841408142003830281050205084003112011021081 53 0x60f665e6677601016a6da5c5a4baabba509081010467654321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p47x1 : Ex 47 4 [v22,u1,u5,u0,u2] :=
  certify c47 [] (unpack 4 0x13060386140803830281028410a010811102112005020508 40 0x73b77675635360a6078739301787165144312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p47x2 : Ex 47 5 [v14,u1,u5,u0,u2,u3] :=
  certify c47 [⟨_,p47x1⟩] (unpack 5 0x80004003070613060583038610a00284108114200502038302811102112010830508 53 0x619cd0319e4338841b48429489330c4491491a86912d295292831cc2110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p47x3 : Ex 47 5 [v33,u1,u5,u0,u2,u3] :=
  certify c47 [] (unpack 5 0x70613060583038603831100110205081420050240014002028110a0028410811120 53 0x7520e43c08453c823b8e41106250d424b44749d092308b5250741cc42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p47x4 : Ex 47 4 [v28,u3,u5,u0,u2] :=
  certify c47 [] (unpack 4 0x1306070605830689028110a00284108114081102112005080502 40 0x83c880b88687637360a003401898167655432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p47x5 : Ex 47 5 [v13,u3,u5,u0,u1,u2] :=
  certify c47 [⟨_,p47x4⟩] (unpack 5 0x160c06890383112080004004028105080386068c10a0028410811408142010890502 53 0xa1c14a13d4a7bd49539491b52d4a5ac4a56a2a8c54a0a5198a511ca5318a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p47x6 : Ex 47 5 [v34,u3,u5,u0,u1,u2] :=
  certify c47 [] (unpack 5 0x160c07060383038605831400140805024001400202811120050810a0028410811420 53 0x6540c64bcc4338c451489224a6118622344250c424b12b52506398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p47x7 : Ex 47 6 (roots 47) :=
  certify c47 [⟨_,p47x0⟩,⟨_,p47x2⟩,⟨_,p47x3⟩,⟨_,p47x5⟩,⟨_,p47x6⟩] (unpack 5 0x800480031408130606890706800280014004800014201120070c038310811102068c05834003050240020281400110a005890386400005080284 160 0xe692953a4edea5a5392e364e7338ce36519338e735ce73270935f17324e7b342da3a2eab62da382e52629a48219a42954a3133c2131e0733e0f31c271380e134ad138ae1340d52c001258912d8b5240931ca73200031c07318a511000104611106310400) (by decide +kernel)
theorem l47 : Claim 47 7 := fromSearch 4146 (by decide +kernel) p47x7

theorem r53x21x32x5 : Red 53 21 32 5 := markLift 53 21 32 5 l21 (by decide +kernel)
def c55 : Cuts (goalAt 55) := [
  ternaryRule 55 53 0 53 0 l53 none (by decide +kernel),
  ternaryRule 55 53 2 21 32 r53x21x32x5 none (by decide +kernel),
  ternaryRule 55 51 0 51 0 l51 none (by decide +kernel),
  ternaryRule 55 39 0 39 0 l39 none (by decide +kernel),
  ternaryRule 55 21 0 21 0 l21 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p55x0 : Ex 55 4 [v35,u0,u2,u1,u5] :=
  certify c55 [] (unpack 4 0x38313060386089011021081112009830281028408810a04 40 0x767653b336a36767259232381761154130312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p55x1 : Ex 55 5 [v36,u0,u2,u1,u4,u5] :=
  certify c55 [⟨_,p55x0⟩] (unpack 5 0x191209830383132413060a100a0411200386028102841221089010811102800008814003 53 0x12442320c8a0c02a43d0a73948235080ad0c20c830ac273a92741cc520c8308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p55x2 : Ex 55 5 [v37,u0,u2,u1,u4,u5] :=
  certify c55 [] (unpack 5 0x191209830b1213060386028002840a101081110208810a0440004001112002810890 53 0x6440c741d0233cc24b92943505314c83a0e62994a1314b5250741cc53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p55x3 : Ex 55 4 [v38,u0,u4,u1,u5] :=
  certify c55 [] (unpack 4 0x9831912038611021081112003830a040881089002810284 40 0x878763b337a37878069034301871165114312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p55x4 : Ex 55 5 [v39,u0,u4,u1,u2,u5] :=
  certify c55 [⟨_,p55x3⟩] (unpack 5 0x13068000400203830983193019120a040a10028111200992088108901821028410811102 53 0x80c5082a510421e008027439072b4a7630e50acaa080204250421cc42906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p55x5 : Ex 55 5 [v40,u0,u4,u1,u2,u5] :=
  certify c55 [] (unpack 5 0x130603830b0619120992088008900a041081110202810a1040004001112008810284 53 0x6440c62a4c741d0233cc24b929435083a0e62994a1314b5250741cc53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p55x6 : Ex 55 5 [v41,u2,u4,u0,u1,u5] :=
  certify c55 [] (unpack 5 0xb060b1213241102112003860890028410a0191208810a040a104003028113061081 53 0xd0340c2c0ac23c8c73980681a962d292a92a4a5484a50501c06200202906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p55x7 : Ex 55 6 (roots 55) :=
  certify c55 [⟨_,p55x1⟩,⟨_,p55x2⟩,⟨_,p55x4⟩,⟨_,p55x5⟩,⟨_,p55x6⟩] (unpack 5 0x1a2419121a3013068004193009831324038310a010814004110280038002088140030a0480018000028140020a10089040010386400011200284 160 0x8edad8cb928ef9b8c9ad8e5088cb528e7598c90862d083b4cdc2ccb635081409014832140301485215821136ed15af61342d15021122a8152b4120288c8128c2708ca728c0106340d7acab734ad62c003a0a8518004a008398a510800104611106310400) (by decide +kernel)
theorem l55 : Claim 55 7 := fromSearch 82 (by decide +kernel) p55x7

def c59 : Cuts (goalAt 59) := [
  ternaryRule 59 42 0 42 0 l42 none (by decide +kernel),
  ternaryRule 59 43 0 43 0 l43 none (by decide +kernel),
  ternaryRule 59 43 16 42 1 r43x42x1x5 none (by decide +kernel),
  ternaryRule 59 51 0 51 0 l51 none (by decide +kernel),
  ternaryRule 59 57 0 57 0 l57 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p59x0 : Ex 59 5 [v15,u1,u3,u0,u4,u5] :=
  certify c59 [] (unpack 5 0x191210a0058305890992089014080c89142005020508400311201102108109830881 53 0x1400218860581eb3b8eb334cb6316712847024081886230020398a41886208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p59x1 : Ex 59 4 [v22,u1,u5,u0,u4] :=
  certify c59 [] (unpack 4 0x19120589140809830881089010a010811102112005020508 40 0x73b77675635360a0078739301787165144312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p59x2 : Ex 59 5 [v14,u1,u5,u0,u3,u4] :=
  certify c59 [⟨_,p59x1⟩] (unpack 5 0x19120c89800040030583099210a00890108109830881142005021102112010830508 53 0x61c0c639cc433cc41948e211a649949230891a86912d2952928118e62148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p59x3 : Ex 59 5 [v33,u1,u5,u0,u3,u4] :=
  certify c59 [] (unpack 5 0x19120c890583058909831100110205084001400208811420050210a0089010811120 53 0x6540c433cc451486118622388250d424b529330c4490ab52506398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p59x4 : Ex 59 4 [v28,u3,u5,u0,u4] :=
  certify c59 [] (unpack 4 0x191205830c890881089010a0108114081102112005080502 40 0x83b88786736370a0089803401898176155432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p59x5 : Ex 59 5 [v13,u3,u5,u0,u1,u4] :=
  certify c59 [⟨_,p59x4⟩] (unpack 5 0x1c180983112080004004058905080c9810a0089010810c8908811408142010890502 53 0x41c0842948a23c8a1b94e529cd529843910752d471a067124e7420e6110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p59x6 : Ex 59 5 [v34,u3,u5,u0,u1,u4] :=
  certify c59 [] (unpack 5 0x1c180983058905830c891400140805024001400208811120050810a0089010811420 53 0x6540c433cc451489224a6118622388250d424b529330cb52506398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p59x7 : Ex 59 6 (roots 59) :=
  certify c59 [⟨_,p59x0⟩,⟨_,p59x2⟩,⟨_,p59x3⟩,⟨_,p59x5⟩,⟨_,p59x6⟩] (unpack 5 0x19128004800314080d120c89800280010d180983400480004003142011201081110240020881400110a00c980583050209920589400008900508 160 0x4f14a4b52d4f17c4b54ade4a5835edd65f9834ad4dca54ab0a4df174a8aab300c935cdab1cc9340d4cc004aa8a4ce934a80a815c593c008940583dce1342d1310c1350d1302c4a90a4ac214a82a4a50811821114e5118e61142510c211008010c8310020) (by decide +kernel)
theorem l59 : Claim 59 7 := fromSearch 4148 (by decide +kernel) p59x7

def c61 : Cuts (goalAt 61) := [
  ternaryRule 61 57 0 57 0 l57 none (by decide +kernel),
  ternaryRule 61 45 0 45 0 l45 none (by decide +kernel),
  ternaryRule 61 53 8 21 32 r53x21x32x5 none (by decide +kernel),
  ternaryRule 61 53 0 53 0 l53 none (by decide +kernel),
  ternaryRule 61 21 0 21 0 l21 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p61x0 : Ex 61 4 [v35,u0,u2,u3,u5] :=
  certify c61 [] (unpack 4 0x160c0689068c08901408108114200c890281028408810a04 40 0x767636b335a36762259232381761154130312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p61x1 : Ex 61 5 [v36,u0,u2,u3,u4,u5] :=
  certify c61 [⟨_,p61x0⟩] (unpack 5 0x1c180c89160c06890a100a04068c02810284122108901081140880000881400116241420 53 0x334465314c01c06a33d4a1b14a0394d314c91b0694816952507314c51906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p61x2 : Ex 61 5 [v37,u0,u2,u3,u4,u5] :=
  certify c61 [] (unpack 5 0x1c180c89160c0e18068c028002840a101081140808810a0440034002142002810890 53 0x6440c741d0233cc943905314c9135283a1462994a1314b5250741cc53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p61x3 : Ex 61 4 [v38,u0,u4,u3,u5] :=
  certify c61 [] (unpack 4 0xc891c18068c14081081142006890a040881089002810284 40 0x878763b337a37870069034301871165114312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p61x4 : Ex 61 5 [v39,u0,u4,u2,u3,u5] :=
  certify c61 [⟨_,p61x3⟩] (unpack 5 0xc891c30160c0689800040001c180a0414200c980a100281088108901821028410811408 53 0x80292c4a9841260bcc64b8c629ccd319850acaa080202250431cc42906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p61x5 : Ex 61 5 [v40,u0,u4,u2,u3,u5] :=
  certify c61 [] (unpack 5 0xe0c160c06891c180c98088008900a041081140840034002142002810a1008810284 53 0x741d044c12343c632386312469435083a0ea2314310d4b5250741cc42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p61x6 : Ex 61 5 [v41,u2,u4,u0,u3,u5] :=
  certify c61 [] (unpack 5 0xe0c16241408068c0890028410a01c18088114200e180a040a1040010281160c1081 53 0xe038072c0a77bce07016b3b56b2b16c5ad8a5ad45024082002021cc42906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p61x7 : Ex 61 6 (roots 61) :=
  certify c61 [⟨_,p61x1⟩,⟨_,p61x2⟩,⟨_,p61x4⟩,⟨_,p61x5⟩,⟨_,p61x6⟩] (unpack 5 0x1a241c181c300c891a30160c80041624068910a010814004140880038002088140010a044002068c40031420800180000284028140000a100890 160 0x8edad8cb928ef9b8c9ad44150448f2440f044912464e74374d46759434ed8dc638cb128df178c86362c631342db2c2b634634546341e874569441c638c8928c2708ca728c0846348d7ac0b7340d62c844208441d274292941c8410c033048428c8310400) (by decide +kernel)
theorem l61 : Claim 61 7 := fromSearch 20482 (by decide +kernel) p61x7

theorem l62 : Claim 62 6 := fromLift 6 20 1184816 l42 (by decide +kernel)

def c79 : Cuts (goalAt 79) := [
  ternaryRule 79 77 0 77 0 l77 none (by decide +kernel),
  ternaryRule 79 75 0 75 0 l75 none (by decide +kernel),
  ternaryRule 79 74 0 74 0 l74 none (by decide +kernel),
  ternaryRule 79 71 0 71 0 l71 none (by decide +kernel),
  ternaryRule 79 69 0 69 0 l69 none (by decide +kernel),
  ternaryRule 79 78 0 78 0 l78 none (by decide +kernel),
  ternaryRule 79 75 0 75 0 l75 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 79 71 0 71 0 l71 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 79 75 0 75 0 l75 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 79 77 0 77 0 l77 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 79 75 0 75 0 l75 (some (3,u0,u6)) (by decide +kernel),
  ternaryRule 79 71 0 71 0 l71 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 79 78 0 78 0 l78 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 79 71 0 71 0 l71 (some (3,u1,u6)) (by decide +kernel),
  ternaryRule 79 78 0 78 0 l78 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 79 77 0 77 0 l77 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 79 78 0 78 0 l78 (some (3,u2,u6)) (by decide +kernel),
  ternaryRule 79 75 0 75 0 l75 (some (0,u0,u6)) (by decide +kernel),
  ternaryRule 79 77 0 77 0 l77 (some (3,u3,u6)) (by decide +kernel),
  ternaryRule 79 71 0 71 0 l71 (some (0,u1,u6)) (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x0 : Ex 79 4 [v42,u6,u0,u1,u3] :=
  certify c79 [] (unpack 4 0x240824402306038305830508038624090284224005020706208122040281 40 0x41e4494d91c190b064a469866176060504300210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x1 : Ex 79 4 [v43,u6,u0,u1,u2] :=
  certify c79 [] (unpack 4 0x70603832206244002812240050803862204248902840583208124080502 40 0xa16aa0ea8ada86c6080ba4a94874465440302210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x2 : Ex 79 5 [v44,u6,u0,u1,u2,u3] :=
  certify c79 [⟨_,p79x0⟩,⟨_,p79x1⟩] (unpack 5 0x70624082440038322062140400505832240050803862204240920c0400002844003800105024001800002812081 57 0x45d48125821aac246928d0cc2d5c96d8c1a723c81385c76b0e75a8e74a0e62148308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x3 : Ex 79 4 [v45,u6,u0,u1,u3] :=
  certify c79 [] (unpack 4 0x2440058303862102070605020508214020c00284220420810281 40 0x71c17c75919137b735a319190870065040030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x4 : Ex 79 4 [v46,u6,u0,u1,u2] :=
  certify c79 [] (unpack 4 0x3832240038621020706028121400508028420c0220420810502 40 0x71b757c791917b7335a519197870600504301210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x5 : Ex 79 5 [v47,u6,u0,u1,u2,u3] :=
  certify c79 [⟨_,p79x3⟩,⟨_,p79x4⟩] (unpack 5 0x8001400307068000400124400383050805830502224002812140038620c02081210202842204 51 0x246d1c92989d3039c683bce7725a9318ec388621ac89524e8390862906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x6 : Ex 79 5 [v48,u6,u0,u1,u2,u3] :=
  certify c79 [] (unpack 4 0x706240803830583220405022440028122400508058921400284038620c02081 57 0xabea8af88eb8a9a448d85b4b1aca878114212b1ba9a98787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x7 : Ex 79 5 [v49,u6,u0,u1,u2,u3] :=
  certify c79 [] (unpack 4 0x70603830583050803860284208121022440050222400281214020c02204 51 0x586835e338435b56b3d3787895c539349ba9878765654343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x8 : Ex 79 5 [v50,u6,v51,u1,u2,u3] :=
  certify c79 [] (unpack 5 0x7064006038305082183058903860305244005022240028120812409028420c040002102 54 0x105495094a0c8898c53996634109425e6799cd2b4ab62d484a046398451148318820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x9 : Ex 79 5 [v17,u6,v51,u0,u2,u3] :=
  certify c79 [] (unpack 5 0x400707060583028421830589038603052440050222400281210222060508214040052081 54 0x1054a188444c8818c5398c7399e87a0c731dcd2b4ac5ad484a046398451148318820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x10 : Ex 79 6 [v51,u0,u1,u2,u3,u6] :=
  certify c79 [⟨_,p79x2⟩,⟨_,p79x5⟩,⟨_,p79x6⟩,⟨_,p79x7⟩,⟨_,p79x8⟩,⟨_,p79x9⟩] (unpack 5 0x2408068907068005400703830508800421020583400605894005038603054000028480038002800120818000220440040502400324404002028140012240 159 0x78c65115e2794652042501480214217042374dcef0c215a7653d56dd95351b4624c869989a2667913c591e45313e58545569595755a36ac6a691aa7a9a261504088051102809be728c5ef83dee535486214b52128314c4390c7310a4104401804310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x11 : Ex 79 4 [v52,u6,u0,u3,u2] :=
  certify c79 [] (unpack 4 0x7060383220c214002812240058305022183050803860284208121022204 40 0xa7eaa10aa5da71c7577ba3a93787316135432210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x12 : Ex 79 4 [v53,u6,u0,u3,u1] :=
  certify c79 [] (unpack 4 0x21400383260c070605080386058305022103210202842240208122040281 40 0x7a7e5151a0d075c770b04a944787456504030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x13 : Ex 79 5 [v54,u6,u0,u3,u1,u2] :=
  certify c79 [⟨_,p79x11⟩,⟨_,p79x12⟩] (unpack 5 0x7064001800103832140220440008000220c244040050281224005080386058305022103210220c0400302842081 57 0xb3596b2456bad1695cd6649a448922983d26238c66b0cb0ad414a02131cc12148118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x14 : Ex 79 4 [v55,u6,u0,u3,u2] :=
  certify c79 [] (unpack 4 0x7062408224005830383028121400502028420c0050820812102 40 0x75c771a751b17a73359510107872652544321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x15 : Ex 79 4 [v56,u6,u0,u3,u1] :=
  certify c79 [] (unpack 4 0x21402408038605832204038305080502244020c00284210220810281 40 0xd77d71d1c1c137b335a319130870065040030210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x16 : Ex 79 5 [v57,u6,u0,u3,u1,u2] :=
  certify c79 [⟨_,p79x14⟩,⟨_,p79x15⟩] (unpack 5 0x689800140010383214080004000050222400281058905082440058320c02081240802842102 51 0x24d24a46a4c52981d2f4b8e771c6e1b4e7608621ad2a4908741c862906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x17 : Ex 79 5 [v58,u6,u0,u3,u1,u2] :=
  certify c79 [] (unpack 4 0x689038322040589210202812240050821400502058324400284068c20c02081 57 0xa4faabda8aea7887bdbd5b4ba9a118c814512b1ba9a98787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x18 : Ex 79 5 [v59,u6,u0,u3,u1,u2] :=
  certify c79 [] (unpack 4 0x70603830386058305022408208102842240028121400508244020c02102 51 0x5ae5586535d5a3a43848a898575673c77aba898765654343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x19 : Ex 79 5 [v50,u6,v60,u3,u1,u2] :=
  certify c79 [] (unpack 5 0x68922404008038302812140050805022489068c0583050320812103028420c040032102 54 0x1a78b60d689a58350d6bd6d7358b5b18b589656156c62d472a4a839cc51148318820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x20 : Ex 79 5 [v16,u6,v60,u0,u1,u2] :=
  certify c79 [] (unpack 5 0x38321404009028122400589050802842489068c058305032408220c0502244040052081 54 0x1ae735c56b9cd6b96e8ba0b5c16582ceb5bdcd7358b62d492a4a741cc51148318820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x21 : Ex 79 6 [v60,u0,u3,u1,u2,u6] :=
  certify c79 [⟨_,p79x13⟩,⟨_,p79x16⟩,⟨_,p79x17⟩,⟨_,p79x18⟩,⟨_,p79x19⟩,⟨_,p79x20⟩] (unpack 5 0x2204068940024001070c0383400940002140800524080502800402814008224040040589050805834005068c050340030284800380028001208180002102 159 0x7a3113c5e7f85189e315f57cef5718f1efdc63c8c76f7818015840b004c1658c8ea39d662c8aed6c318b630f6b3ad6bb18e632f6b517411c54ad04b11d531244050052101208c22f4be298be0f6a5ac531ae6b12c59d6a4a4e741ce6114402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x22 : Ex 79 5 [v61,v50,u6,u1,u2,u3] :=
  certify c79 [] (unpack 4 0x706400a0383208102842080244005022240028120c02140050821034003 51 0x7b8b7a8757e55b65a55d727325c52b3b2a3a947874565423210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x23 : Ex 79 5 [v62,u1,u0,u6,u2,u3] :=
  certify c79 [] (unpack 4 0x706058322400508244005020281038320812102028420c003862140 57 0x859578d775b728c87b7254542a1a8a89a767454598987676545433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x24 : Ex 79 5 [v63,u0,u6,u1,u3] :=
  certify c79 [] (unpack 5 0x24892183068c05830589038606892440050203832140050821022081220420c0028122400284 120 0x929455964b595455214b39d4752d0889ce541628414e57800a829f07a80a7000769dcd69c00280a4190a3290005884a6296c5a8424084749d0941c4228844098a129042184601086210020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x25 : Ex 79 5 [v63,v50,u0,u6,u1,u3] :=
  certify c79 [] (unpack 4 0x220405830589210302840502244005082140208120c0028122404001 50 0x84748778868564546556d38c836b643a928722652214232210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x26 : Ex 79 5 [v64,u3,u0,u6,u1,u2] :=
  certify c79 [] (unpack 4 0x70603832240058905020281068921400508210220812408028420c0068c2440 57 0xa5daabfa7aea7585b7b8ada227c754542b1bb545a9a98787565433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x27 : Ex 79 6 [v50,u0,u6,u1,u2,u3] :=
  certify c79 [⟨_,p79x22⟩,⟨_,p79x8⟩,⟨_,p79x19⟩,⟨_,p79x5⟩,⟨_,p79x23⟩,⟨_,p79x24⟩,⟨_,p79x25⟩,⟨_,p79x16⟩,⟨_,p79x26⟩] (unpack 6 0x2489800880074003068907068006800540012440070c0383218380048003214040002102800205830502400202812240800105890508208120c02103400580000284 159 0x2030c1571605d714c15f30c7575de5d774c31b28a31c31b71b30a28b28a14914b24914a28b69960a28b28a60b60c44c5c618c18c5d145518629629559528629418615115445114615318641145245140618208f34410c08c34e34c10c28428908928b2891041c41060861c81c61061411421040820c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x28 : Ex 79 4 [v65,u1,u0,u6,u2] :=
  certify c79 [] (unpack 4 0x38603832240028121022081028420c0214005020508 40 0x75877478565640a4079765651787156514312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x29 : Ex 79 5 [v66,u1,u0,u6,u2,u3] :=
  certify c79 [⟨_,p79x28⟩] (unpack 4 0x7060583038620c0028424402140038305088000050240032240028121022081 57 0x50a025f22032b5e52b230101b9dbbdcb5a59928210107565432321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x30 : Ex 79 4 [v67,u3,u0,u6,u2] :=
  certify c79 [] (unpack 4 0x706210205832240028122042408208120c00284214005080502 40 0x859880c883895b5b30a005651898756513432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x31 : Ex 79 5 [v68,u3,u0,u6,u1,u2] :=
  certify c79 [⟨_,p79x30⟩] (unpack 5 0x689038321408000400002812240050803862440068c20c002840502210224082081 57 0xb0296b3c16b529695bd690380e4a5cd4a58b22d444a0800808439884314810040310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x32 : Ex 79 6 [v61,u0,u6,u1,u2,u3] :=
  certify c79 [⟨_,p79x22⟩,⟨_,p79x29⟩,⟨_,p79x7⟩,⟨_,p79x31⟩,⟨_,p79x18⟩] (unpack 5 0x248906890706070c03832183068c0583400a058903862080208102848004800324404003050240022240400102818002800121404000050821028000400520c0 159 0x7dad9be7f7be6d9f5296f9bdf75a94b1299ae6c5ae694b4cd7908d235e636c844f13be6d244e88499a7a31a649e2526e5b8ce1b26a6e95ca49925775da5225496ad4929043498a61949ee7b62d7c1ed7356a5a5895b169524c53110431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x33 : Ex 79 4 [v69,u6,u1,u2,u0] :=
  certify c79 [] (unpack 4 0x20c0038602840583260c070603830281208305082440050224082081 40 0x6b6db4cb010bb2a2609662864676405024232010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x34 : Ex 79 4 [v70,u6,u1,u2,u3] :=
  certify c79 [] (unpack 4 0x24080706240c20c024400383028121830508038605830502210220810284 40 0x31e183d881c8088b363a68986171605003431210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x35 : Ex 79 5 [v71,u6,u1,u2,u0,u3] :=
  certify c79 [⟨_,p79x33⟩,⟨_,p79x34⟩] (unpack 5 0x58320c0038624084005800102840706240c22404000244003830281208320812140400105084003800005022102 57 0x13ccf00d829826b02520799e10946090bd293b9296b121205644a9243a0e43148308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x36 : Ex 79 4 [v72,u6,u1,u2,u3] :=
  certify c79 [] (unpack 4 0x7062204244003830583050220c0028105082140028421022081 40 0x70a057c550b57a73359510107872652524321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x37 : Ex 79 4 [v73,u6,u1,u2,u0] :=
  certify c79 [] (unpack 4 0x38620c003832204058302840281224021400508208121020502 40 0xb77b73c771b1919135a319190870665040032210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x38 : Ex 79 5 [v74,u6,u1,u2,u0,u3] :=
  certify c79 [⟨_,p79x36⟩,⟨_,p79x37⟩] (unpack 5 0x800140030583038620c080000284400507060281244005022240038321402102220405082081 51 0x1c683c8e78b0f03b98c7308f6306e1b58c598ea388621a4e8390862906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x39 : Ex 79 5 [v75,u6,u1,u2,u0,u3] :=
  certify c79 [] (unpack 4 0x583038624080706208105022440028420c00281038322400508070c21402102 57 0xabdb8afa788781e8bdb84aca5b4ba9a114512b1ba9a98787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x40 : Ex 79 5 [v76,u6,u1,u2,u0,u3] :=
  certify c79 [] (unpack 4 0x58303860706050803830281210222042440050220c00284224021402081 51 0x586535e593943bd3384895c998795b56b9a9878765654343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x41 : Ex 79 5 [v17,u6,v77,u2,u0,u3] :=
  certify c79 [] (unpack 5 0x400b058320c00284070602812306070c0383028324400502210220830508214040012081 54 0xc539946345c6819ee73dee73dc5795cf7b926699892acaa4a506398451148318820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x42 : Ex 79 5 [v78,u6,v77,u1,u0,u3] :=
  certify c79 [] (unpack 5 0x583038620c00284400c05082306070c03830283244005022204240c0281224040002081 54 0xc5398c7399c6899d0839ee73dc57b92e734c731d8b2aca952506398451148318820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x43 : Ex 79 6 [v77,u1,u2,u0,u3,u6] :=
  certify c79 [⟨_,p79x35⟩,⟨_,p79x38⟩,⟨_,p79x39⟩,⟨_,p79x40⟩,⟨_,p79x41⟩,⟨_,p79x42⟩] (unpack 5 0x2408068c0583400c038640020284400520c080052204070602818004400b03834000070c0283400105088003800280012102800020814004050240032440 159 0x78422009e0788221304358c4b10d8373181745cef05813ed6de30fc6176b3b186eb59d69b8c66d6be319c62f6b51f422c94ad08f24def12c531cc4f12dd2334c4710d1311a4140406804d102007adee6b56b62d6a324c4410c7310a4104401804310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x44 : Ex 79 5 [v79,v17,u6,u0,u2,u3] :=
  certify c79 [] (unpack 4 0x400d070605832102050821002440050221402240028120c0028420834003 51 0x7b87a77e47d44b544a5427c742432b3b2a32967876454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x45 : Ex 79 5 [v80,u0,u1,u6,u2,u3] :=
  certify c79 [] (unpack 4 0x70624400383028405020583224002812102208105082140058920c0 57 0x94c469d664769c9226b65454a9896a674545a21a98987676545433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x46 : Ex 79 5 [v81,u2,u1,u6,u0,u3] :=
  certify c79 [] (unpack 4 0x5830386244002810502070620c0028420812102220405082140070c2240 57 0xa5ca7aea758572d7b7b8aca254542b1bba9bb54ba9a98787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x47 : Ex 79 5 [v23,u1,u6,u0,u2] :=
  certify c79 [] (unpack 5 0x2306218305890386070c0383070622400281058320c002842081210224082140050224400508 120 0x929455964b5954a5214b39d4752d0889ce541628414e581ce07820f780e76800a729ae6a80a280a4190a3290005884a6296c5a84a4084749d0941c42288c4098a129042184601086210020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x48 : Ex 79 5 [v23,v17,u1,u6,u0,u2] :=
  certify c79 [] (unpack 4 0x386240803832083050822400281028420c021022140050224404003 50 0x748778877675645463d66556c37b743a927872652214232210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x49 : Ex 79 6 [v17,u1,u6,u0,u2,u3] :=
  certify c79 [⟨_,p79x44⟩,⟨_,p79x41⟩,⟨_,p79x5⟩,⟨_,p79x45⟩,⟨_,p79x9⟩,⟨_,p79x38⟩,⟨_,p79x46⟩,⟨_,p79x47⟩,⟨_,p79x48⟩] (unpack 6 0x800880074003068907062306800680054001068c058322402183800403868003800220c0400502842081400405022440800103830281210221402083400080000508 159 0xb28a14914b24914a28b81f78a28b28a78b79c18629d29c75c28619b18615515b55514619a18661555955560619634d2972965d628d2863c654d34634654f3d434d14f1543cf14d14234d11211349210d35134d38f3d03cf38d34208c28428908928b2891041c41060861c81c61061411421040820c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x50 : Ex 79 4 [v82,u0,u1,u6,u3] :=
  certify c79 [] (unpack 4 0x583038605022440210220810508214020c002810284 40 0x85758487656508a8565604901871165114312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x51 : Ex 79 5 [v83,u0,u1,u6,u2,u3] :=
  certify c79 [⟨_,p79x50⟩] (unpack 4 0x70603830583224020c002842440050280000281400120812102058921400508 57 0x849468f664c6808906e63434b8d86c6b4343b020a9898676543432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x52 : Ex 79 4 [v84,u2,u1,u6,u3] :=
  certify c79 [] (unpack 4 0x21020383070624400502220420810508214020c002840281 40 0x75857478b5b540a0079005601787156514312010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x53 : Ex 79 5 [v85,u2,u1,u6,u0,u3] :=
  certify c79 [⟨_,p79x52⟩] (unpack 5 0x583038620c0800002844005070c2140050822400706028124400502208122042102 57 0x30106c1c06c0380c43d8e631cd6316340c80080283a90852507198610040520c8310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x54 : Ex 79 6 [v79,u1,u6,u0,u2,u3] :=
  certify c79 [⟨_,p79x44⟩,⟨_,p79x51⟩,⟨_,p79x7⟩,⟨_,p79x53⟩,⟨_,p79x40⟩] (unpack 5 0x68907062306068c0583218305890386400d070c03832100210205084004244040030502800480032240400102818002800120c0400502842081800040002140 159 0x45ce9c2718426e7792977ddeff9c94f5299ae7d5ae694ec84771dbe6dc4724c959089225663688499a7a31a649e48496259c624423aee84a4e93a17856524d935b55324843498a6194a0f83a2e8460e7b96a5a5a95b169524c53110431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x55 : Ex 79 4 [v86,u6,u2,u3,u1] :=
  certify c79 [] (unpack 4 0x2140038305080386248905830502070621060284028120c020812102 40 0x7b7db3c30101b4a4719174873763315343321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x56 : Ex 79 4 [v87,u6,u2,u3,u0] :=
  certify c79 [] (unpack 4 0x58320c0038602842089214005020706230605080383028121022081 40 0xa7d72a2c0101a4ba709047782762205224321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x57 : Ex 79 5 [v88,u6,u2,u3,u0,u1] :=
  certify c79 [⟨_,p79x55⟩,⟨_,p79x56⟩] (unpack 5 0x214003834000800105080386058320c0210240058000028420892440400105020706208121062240400302812204 57 0x791ed20d42e2b8b2a4e4b9456b3c0e1585e5715cb6b1672a8a74a0e1398212902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x58 : Ex 79 4 [v89,u6,u2,u3,u1] :=
  certify c79 [] (unpack 4 0x383214024080706038605080502244020c002840281210222042081 40 0xc88c83d380c0b0b036a330134984776453432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x59 : Ex 79 4 [v90,u6,u2,u3,u0] :=
  certify c79 [] (unpack 4 0x58320c0240807060386028421400502028122400508208122042102 40 0x86d6c88c80c060b646a610108983763655432210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x60 : Ex 79 5 [v91,u6,u2,u3,u0,u1] :=
  certify c79 [⟨_,p79x58⟩,⟨_,p79x59⟩] (unpack 5 0x70c21408001400005080386068c20c080000284400505022440070622402204240802812081 51 0x45ce8b892738711c1ce7a5cd4a4cc4ad295a46b4a9294086219c862906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x61 : Ex 79 5 [v92,u6,u2,u3,u0,u1] :=
  certify c79 [] (unpack 4 0x70c0386068c2102208105082140028420c00502070624400281068922402204 57 0x9aa9a1facbcb8ae884d87887bcbc5b4b14512b1ba9a98787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x62 : Ex 79 5 [v93,u6,u2,u3,u0,u1] :=
  certify c79 [] (unpack 4 0x38303860583050207062408220402812140050820c00284244022402081 51 0xb5b657e7586835d33bcb73743843b89b7ba7798765654343210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x63 : Ex 79 5 [v78,u6,v94,u3,u0,u1] :=
  certify c79 [] (unpack 5 0x214005080386068c20c00284400e0502260c068907060485220421060281224040032081 54 0x2308463084605896118c1907b187731ac635856b10c62d472a4a839cc51148318820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x64 : Ex 79 5 [v16,u6,v94,u2,u0,u1] :=
  certify c79 [] (unpack 5 0x70c2140400f0508038620c002840281260c068907060485240820890502244040012081 54 0x1c88ba0e741c5838ee73d6e6ad8b5b18b5b16562d6c62d482a4a741cc51148318820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x65 : Ex 79 6 [v94,u2,u3,u0,u1,u6] :=
  certify c79 [⟨_,p79x57⟩,⟨_,p79x60⟩,⟨_,p79x61⟩,⟨_,p79x62⟩,⟨_,p79x63⟩,⟨_,p79x64⟩] (unpack 5 0x400f070c4004400021402102058903860508068c400e40020284400520c08005240805028004070640010689048540030281800380028001220480002081 159 0x66d906819d641602f5af5acbb58fad2ad64f53cef536b735addadcb5b7ad0240cc32080332ce252b5ed8bded291e525d573ad57292610a4a499495084e108ca5394a308396e01c0e7b80b01d4d124405004c1012059d6a4a4e741ce6114402004310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x66 : Ex 79 5 [v95,v78,u6,u0,u1,u3] :=
  certify c79 [] (unpack 4 0x583038622040281401022002240244005022140050820c0028421064003 51 0x6c766b7b64654c5c4b5b26e624d22c32b2ba986765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x67 : Ex 79 5 [v96,u2,u6,u1,u3] :=
  certify c79 [] (unpack 5 0x24892183070c038306890706068c244005020386214005082102220420812240028420c00281 120 0x929445924b591445214b39d4752d0889ce441228410e479ce0801f0780e06800a729ae6a80028004190a3290005884a6296c5a84a4084749d0941c42288c4090a129044184201006210020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x68 : Ex 79 5 [v96,v78,u2,u6,u1,u3] :=
  certify c79 [] (unpack 4 0x70c2081070622402106028124400502050821402204028420c04011 50 0x63766776656453435ad55445ca6b63a9826762542213212210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x69 : Ex 79 5 [v97,u1,u2,u6,u0,u3] :=
  certify c79 [] (unpack 4 0x58320c00706050824400502028403862081220421020281224003832140 57 0x94a989e984d4d88d8b7829c954549b9a4545b21ba9a98787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x70 : Ex 79 5 [v98,u3,u2,u6,u0,u1] :=
  certify c79 [] (unpack 4 0x70c038620c005830502214005080284068c2081220424080281224006892440 57 0x95a592f9b9ba89e885d8d88d8bcb54542b1bb54ba9a98787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x71 : Ex 79 6 [v78,u2,u6,u0,u1,u3] :=
  certify c79 [⟨_,p79x66⟩,⟨_,p79x63⟩,⟨_,p79x67⟩,⟨_,p79x68⟩,⟨_,p79x38⟩,⟨_,p79x69⟩,⟨_,p79x42⟩,⟨_,p79x60⟩,⟨_,p79x70⟩] (unpack 6 0x260c800880074003244023068006070c8005800421404000068c058305890386050820c0800380020284400240052081800107060502220422402106400180000281 159 0x2018615c16071c14619f18675c71e71c74618658671040640671659b41015615b59615014241011911a65911041841055659759655041330c19419351318c19230c41141245140c30b30c14f14b3cf14c3023cf10c30b30c10f3cb38d28c30b30c28b2820891c41060861c81c61061411421040820c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x72 : Ex 79 4 [v99,u1,u2,u6,u0] :=
  certify c79 [] (unpack 4 0x38622040383028420c02081210222400281214005020508 40 0x8575383780b835a35a5a03931871665113432110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x73 : Ex 79 5 [v100,u1,u2,u6,u0,u3] :=
  certify c79 [⟨_,p79x72⟩] (unpack 5 0x583038620c002840706244021400508800005024003208121022204038322400281 57 0x722ced3c0ed23880681cd53dad739a03b00020c0759d441906a008093a0e62948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x74 : Ex 79 4 [v101,u3,u2,u6,u0] :=
  certify c79 [] (unpack 4 0x5832204070620c0028420812408210222400281214005080502 40 0x8595383980c035b330a305601898776513432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x75 : Ex 79 5 [v102,u3,u2,u6,u0,u1] :=
  certify c79 [⟨_,p79x74⟩] (unpack 5 0x38321408000400005080386068c20c0028424400689224002810502208124082204 57 0xc03c0c2408f631ee631a862d0802504411283a9084a5040808439884314810040310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x76 : Ex 79 6 [v95,u2,u6,u0,u1,u3] :=
  certify c79 [⟨_,p79x66⟩,⟨_,p79x73⟩,⟨_,p79x40⟩,⟨_,p79x75⟩,⟨_,p79x62⟩] (unpack 5 0x260c2306070c0383068c0583058903864010068907062200220402818004800324404003050280028001214040000508400220c0400502842081800040012240 159 0x7dad9be7f7be6d6b54d7a10d435ea579089aa7e52a689f1089765cef248968846edbade9a46e48446119c610421c8499a6731a64248d2b909224826356526d9b5b55b29043498a61949ee7b62d7c1ed735495218852d484a0c5310e431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x77 : Ex 79 5 [v103,v16,u6,u0,u1,u2] :=
  certify c79 [] (unpack 4 0x38340120386240805022400224002812140050820c0028420894003 51 0x6a76697646d64a54949c626324b22a322939876765454323210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x78 : Ex 79 5 [v104,u0,u3,u6,u1,u2] :=
  certify c79 [] (unpack 4 0x6890383214003860284224002810508058921022408208105022440058320c0 57 0x94a992f989e984d4d88d54549b9ab8cb454bb21ba9a98787645433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x79 : Ex 79 5 [v29,u3,u6,u0,u2] :=
  certify c79 [] (unpack 5 0x2306068907062183068c0583070c22400281058920c002842081240821022440050821400502 120 0x929445924b5914a82940882118014a5214b39d4752d0879ce4411e8410e469ce0701ae680e028004190a3290005884a6296c5a84a4084749d0941c47288c4098a129044184201006210020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x80 : Ex 79 5 [v29,v16,u3,u6,u0,u2] :=
  certify c79 [] (unpack 4 0x689068c21022440208905022240028120c002842408050821404013 50 0x63766ad66776646543544ac44554b3a9826762454213212210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x81 : Ex 79 5 [v105,u2,u3,u6,u0,u1] :=
  certify c79 [] (unpack 4 0x214003830386068c02810508070c20c002842081240822040502244007062240 57 0xa4f4faafabeb7ad7748772c7b7b85454b54bb21ba9a98787665433210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x82 : Ex 79 6 [v16,u3,u6,u0,u1,u2] :=
  certify c79 [⟨_,p79x77⟩,⟨_,p79x16⟩,⟨_,p79x78⟩,⟨_,p79x20⟩,⟨_,p79x79⟩,⟨_,p79x80⟩,⟨_,p79x60⟩,⟨_,p79x81⟩,⟨_,p79x64⟩] (unpack 6 0x260c80080689800780064001070c0383214080058004400440000281224005890386050824898003068c8002800120c0400502842081240824402089400380000502 159 0x204d31521604921534c24d311e11f79e1134dd4d36d249c4926d34d93cf4da4d96994cf4d53cf15815561814f3c261810f3d53cf1186155d650f3d53cf5155132534871d31d34892511c73d03d14103c71ce1c714914e2491471c21c710c10d30c1071cb1c720924a2492071c20861411421040820c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x83 : Ex 79 4 [v106,u0,u3,u6,u1] :=
  certify c79 [] (unpack 4 0x240803862204058305082140210220810502244020c002810284 40 0x8575484745c508b05a5004941871165114312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x84 : Ex 79 5 [v107,u0,u3,u6,u1,u2] :=
  certify c79 [⟨_,p79x83⟩] (unpack 5 0x70603832240058920c0028480000281400121400508210220812408058324400502 57 0x923929041264bd2621c80300e020c897258c334c41906c0080b4a928398e62148310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x85 : Ex 79 4 [v108,u2,u3,u6,u1] :=
  certify c79 [] (unpack 4 0x38324080706050821402102220420812440050220c002840281 40 0x9585393890c035b5056003a01981756513432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x86 : Ex 79 5 [v109,u2,u3,u6,u0,u1] :=
  certify c79 [⟨_,p79x85⟩] (unpack 5 0x70c214005080386058320c080000284400522400281208122042408070624400502 57 0xe23c80701ee3c1ce7bdc97352922d290300b4a56a4a50020c0419067008062948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x87 : Ex 79 6 [v103,u3,u6,u0,u1,u2] :=
  certify c79 [⟨_,p79x77⟩,⟨_,p79x84⟩,⟨_,p79x18⟩,⟨_,p79x86⟩,⟨_,p79x62⟩] (unpack 5 0x260c06890706070c03834012058903862489068c05832400240805028004800322404001028140042140400005088002800120c0400502842081800040032440 159 0x7dad9be7f7be6d6f5ad97a5df764d6ed296f1bbe6da96b1299ae6c5ae694c972d25324c82b5b4cd7908d235e6364844e139c612425c8499a7731a642548495a55b56449043498a61949ee7b62d7c1ed7356a5a5895b169524c53110431cc42902118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p79x88 : Ex 79 7 (roots 79) :=
  certify c79 [⟨_,p79x10⟩,⟨_,p79x21⟩,⟨_,p79x27⟩,⟨_,p79x32⟩,⟨_,p79x43⟩,⟨_,p79x49⟩,⟨_,p79x54⟩,⟨_,p79x65⟩,⟨_,p79x71⟩,⟨_,p79x76⟩,⟨_,p79x82⟩,⟨_,p79x87⟩] (unpack 6 0x800b800a2408800980082204800706890706800680054004244021408004070c038380038002208121028001068c058340030502400202814001224020c04005800005890386400005080284 160 0x96330c3526529236633523128a028a25221286022025228a35d28a24c78c7dd79d34c28a7110510926126d161109205234c60c09904168c04c35961825504108a58a5d559524a04a5120121911d14d21d219101134e00018c3cc40e3ce34c00c24a1ca1880002ca00a2481c70840001810c11440c3081000) (by decide +kernel)
theorem l79 : Claim 79 8 := fromSearch 4146 (by decide +kernel) p79x88

theorem r85x21x64x5 : Red 85 21 64 5 := markLift 85 21 64 5 l21 (by decide +kernel)
def c87 : Cuts (goalAt 87) := [
  ternaryRule 87 85 0 85 0 l85 none (by decide +kernel),
  ternaryRule 87 85 2 21 64 r85x21x64x5 none (by decide +kernel),
  ternaryRule 87 83 0 83 0 l83 none (by decide +kernel),
  ternaryRule 87 71 0 71 0 l71 none (by decide +kernel),
  ternaryRule 87 86 0 86 0 l86 none (by decide +kernel),
  ternaryRule 87 21 0 21 0 l21 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p87x0 : Ex 87 4 [v35,u0,u2,u1,u6] :=
  certify c87 [] (unpack 4 0x38322040386089021022081214009830281028408810a04 40 0x767653b336a36767259232381761154130312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p87x1 : Ex 87 5 [v36,u0,u2,u1,u4,u6] :=
  certify c87 [⟨_,p87x0⟩] (unpack 5 0x2912098303834000400122040a100a0421400386028102844002089020812102800008814003 53 0x12482320c8a0c42a4410a7b948235080ad0c20c830ac273a92741cc520c8308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p87x2 : Ex 87 6 (roots 87) :=
  certify c87 [⟨_,p87x1⟩] (unpack 5 0x29122240220429500983038320c0208140052102088140030a0440048000028140020a10089040010386400021400284 160 0x65dad6419065df7641ad7d5087c2d07d6d57c10862d08634cd62ccb635081388e140301382e1405064c216368d64e936342d148211204814892120287c0107ba2e7c2307b80e6340d62cab634ad62c003a0a8518004a008398a510800104611106310400) (by decide +kernel)
theorem l87 : Claim 87 7 := fromSearch 98 (by decide +kernel) p87x2

theorem r75x74x1x5 : Red 75 74 1 5 := markLift 75 74 1 5 l74 (by decide +kernel)
def c91 : Cuts (goalAt 91) := [
  ternaryRule 91 74 0 74 0 l74 none (by decide +kernel),
  ternaryRule 91 75 0 75 0 l75 none (by decide +kernel),
  ternaryRule 91 75 16 74 1 r75x74x1x5 none (by decide +kernel),
  ternaryRule 91 83 0 83 0 l83 none (by decide +kernel),
  ternaryRule 91 89 0 89 0 l89 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p91x0 : Ex 91 5 [v15,u1,u3,u0,u4,u6] :=
  certify c91 [] (unpack 5 0x291220c0058305890992089024080c89244005020508400321402102208109830881 53 0x1400218860581eb3b8eb334cb6316712847024081886230020398a41886208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p91x1 : Ex 91 4 [v23,u1,u6,u0,u4] :=
  certify c91 [] (unpack 4 0x29120589240809830881089020c020812102214005020508 40 0x73b77675635360a0078739301787165144312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p91x2 : Ex 91 5 [v17,u1,u6,u0,u3,u4] :=
  certify c91 [⟨_,p91x1⟩] (unpack 5 0x29120c89800040030583099220c00890208109830881244005022102214020830508 53 0x61c0c639cc433cc41948e211a649949230891a86912d2952928118e62148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p91x3 : Ex 91 5 [v79,u1,u6,u0,u3,u4] :=
  certify c91 [] (unpack 5 0x29120c890583058909832100210205084001400208812440050220c0089020812140 53 0x6540c433cc451486118622388250d424b529330c4490ab52506398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p91x4 : Ex 91 4 [v29,u3,u6,u0,u4] :=
  certify c91 [] (unpack 4 0x291205830c890881089020c0208124082102214005080502 40 0x83b88786736370a0089803401898176155432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p91x5 : Ex 91 5 [v16,u3,u6,u0,u1,u4] :=
  certify c91 [⟨_,p91x4⟩] (unpack 5 0x2c180983214080004004058905080c9820c0089020810c8908812408244020890502 53 0x41c0842948a23c8a1b94e529cd529843910752d471a067124e7420e6110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p91x6 : Ex 91 5 [v103,u3,u6,u0,u1,u4] :=
  certify c91 [] (unpack 5 0x2c180983058905830c892400240805024001400208812140050820c0089020812440 53 0x6540c433cc451489224a6118622388250d424b529330cb52506398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p91x7 : Ex 91 6 (roots 91) :=
  certify c91 [⟨_,p91x0⟩,⟨_,p91x2⟩,⟨_,p91x3⟩,⟨_,p91x5⟩,⟨_,p91x6⟩] (unpack 5 0x29128004800324080d120c89800280010d180983400480004003244021402081210240020881400120c00c980583050209920589400008900508 160 0x4f14a4b52d4f17c4b54ade4a5835edd65f9834ad4dca54ab0a4df174a8aab300c935cdab1cc9340d4cc004aa8a4ce934a80a815c593c008940583dce1342d1310c1350d1302c4a90a4ac214a82a4a50811821114e5118e61142510c211008010c8310020) (by decide +kernel)
theorem l91 : Claim 91 7 := fromSearch 4148 (by decide +kernel) p91x7

def c93 : Cuts (goalAt 93) := [
  ternaryRule 93 89 0 89 0 l89 none (by decide +kernel),
  ternaryRule 93 85 8 21 64 r85x21x64x5 none (by decide +kernel),
  ternaryRule 93 85 0 85 0 l85 none (by decide +kernel),
  ternaryRule 93 77 0 77 0 l77 none (by decide +kernel),
  ternaryRule 93 92 0 92 0 l92 none (by decide +kernel),
  ternaryRule 93 21 0 21 0 l21 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p93x0 : Ex 93 4 [v35,u0,u2,u3,u6] :=
  certify c93 [] (unpack 4 0x6892204068c08902408208124400c890281028408810a04 40 0x767636a335b36a62259232381761154130312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p93x1 : Ex 93 5 [v36,u0,u2,u3,u4,u6] :=
  certify c93 [⟨_,p93x0⟩] (unpack 5 0x2c180c8906890a1022040a04068c028102844000089020812408800008814003400240012440 53 0x43c886398e02448b3b96b2356b0416f3b8ea2348a5018a5a928398e62148310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p93x2 : Ex 93 6 (roots 93) :=
  certify c93 [⟨_,p93x1⟩] (unpack 5 0x2c1824082c500c892240068920c0208140052204088140030a044001068c40022440400480000284028140000a100890 160 0x65dad6419065df7641ad45956440f0458f644110650e7636ad652b4634ed7b8637c2707ba6e7c06362c636342d62c2b634634206341e4742a5241c637c0907ba2e7c2307b8846348d62c0b6340d62c844208441d274292941c8410c033048428c8310400) (by decide +kernel)
theorem l93 : Claim 93 7 := fromSearch 24578 (by decide +kernel) p93x2

theorem r78x74x4x5 : Red 78 74 4 5 := markLift 78 74 4 5 l74 (by decide +kernel)
def c94 : Cuts (goalAt 94) := [
  ternaryRule 94 74 0 74 0 l74 none (by decide +kernel),
  ternaryRule 94 86 0 86 0 l86 none (by decide +kernel),
  ternaryRule 94 92 0 92 0 l92 none (by decide +kernel),
  ternaryRule 94 78 0 78 0 l78 none (by decide +kernel),
  ternaryRule 94 78 16 74 4 r78x74x4x5 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p94x0 : Ex 94 5 [v15,u1,u3,u2,u4,u6] :=
  certify c94 [] (unpack 5 0x2912224007060b1224080e0c24400a10070c0502050840012140210222040b060a04 53 0x1c06218860481e93b8e96b5271b0e702cea188623002032506398a41886208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p94x1 : Ex 94 4 [v23,u1,u6,u2,u4] :=
  certify c94 [] (unpack 4 0x2912070c24080a040b060a10224022042102214005020508 40 0x83b386856353087806a039301871165114312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p94x2 : Ex 94 5 [v17,u1,u6,u2,u3,u4] :=
  certify c94 [⟨_,p94x1⟩] (unpack 5 0x29120e0c800040010706224022040b060a04244005020b120a102102214022060508 53 0x81c0684a50643cc619cce319a822164330c41ac645ac8a1212831cc2110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p94x3 : Ex 94 5 [v79,u1,u6,u2,u3,u4] :=
  certify c94 [] (unpack 5 0x29120e0c07060b06070c210021020508400340040a042440050222400a1022042140 53 0x65414433c8451486118622388250d49334c4490a91312b52506398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p94x4 : Ex 94 4 [v29,u3,u6,u2,u4] :=
  certify c94 [] (unpack 4 0x291207060e0c0a040a102240220424082102214005080502 40 0x83b38786736370a0089003401898176153432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p94x5 : Ex 94 5 [v16,u3,u6,u1,u2,u4] :=
  certify c94 [⟨_,p94x4⟩] (unpack 5 0x2c180e1822400b060a10070c214080000508400221020e0c0a0424082440220c0502 53 0x41c08429484611cc1b86c13d8c739882348862d081a90a42149420e6110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p94x6 : Ex 94 5 [v103,u3,u6,u1,u2,u4] :=
  certify c94 [] (unpack 5 0x2c1807060b06070c0e0c240024080502400340040a0422400a102140050821022440 53 0x6540c6218a4515444bd22338c22344250c49124693312b52506398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p94x7 : Ex 94 6 (roots 94) :=
  certify c94 [⟨_,p94x0⟩,⟨_,p94x2⟩,⟨_,p94x3⟩,⟨_,p94x5⟩,⟨_,p94x6⟩] (unpack 5 0x29128004800324080d120e0c400422400e18070680028001210222040d180b0640030a044002800005024001244021400b12070c40000a100508 160 0x6716b64190672dc64170de5083c0d0d64d93c10865d0862f0b65f1762d0813c2f142b013eaf1403062eab6582162c2b632b514c211228814e93120289401053caf8c0b053c0f6340062dcb635cd62c0b3a0a8518004a008398a511000104611106310400) (by decide +kernel)
theorem l94 : Claim 94 7 := fromSearch 16913456 (by decide +kernel) p94x7

def c103 : Cuts (goalAt 103) := [
  ternaryRule 103 101 0 101 0 l101 none (by decide +kernel),
  ternaryRule 103 102 0 102 0 l102 none (by decide +kernel),
  ternaryRule 103 99 0 99 0 l99 none (by decide +kernel),
  ternaryRule 103 71 0 71 0 l71 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p103x0 : Ex 103 6 (roots 103) :=
  certify c103 [] (unpack 5 0x304030202204130621401324038320c02081210210814003110202814002224010a040010386400011200284 160 0x5516b536ad552b45356b3cd083b4cd3ccd33b5085490852d4b5495252d081302c1362d1322c1342d5262952c2b5242952e2b3bc213a2083be0f3a0282340d231cc235cd2300c52c0b524a952cab524093a0a8398003a008398a510800104611106310400) (by decide +kernel)
theorem l103 : Claim 103 7 := fromSearch 82 (by decide +kernel) p103x0

theorem l107 : Claim 107 8 := fromLift 8 1 4149 l106 (by decide +kernel)

def c109 : Cuts (goalAt 109) := [
  ternaryRule 109 105 0 105 0 l105 none (by decide +kernel),
  ternaryRule 109 101 0 101 0 l101 none (by decide +kernel),
  ternaryRule 109 108 0 108 0 l108 none (by decide +kernel),
  ternaryRule 109 77 0 77 0 l77 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p109x0 : Ex 109 6 (roots 109) :=
  certify c109 [] (unpack 5 0x3040302024082440160c1624068920c0208122041081400314084002068c40011420028402814000224010a0 160 0x5516b536ad552b45356b34cb33364d34e53334ad5264952cab524a952e4b130631342d1302c134635446352d4b5455152c6334063315e5341ef314634348d431cc435cd4308452c8b5240952c0b5248431884314e5320e73148410c031048410c8310400) (by decide +kernel)
theorem l109 : Claim 109 7 := fromSearch 20482 (by decide +kernel) p109x0

theorem l110 : Claim 110 8 := fromLift 8 4 17831472 l106 (by decide +kernel)

theorem r99x98x1x5 : Red 99 98 1 5 := markLift 99 98 1 5 l98 (by decide +kernel)
def c115 : Cuts (goalAt 115) := [
  ternaryRule 115 113 0 113 0 l113 none (by decide +kernel),
  ternaryRule 115 98 0 98 0 l98 none (by decide +kernel),
  ternaryRule 115 99 0 99 0 l99 none (by decide +kernel),
  ternaryRule 115 99 16 98 1 r99x98x1x5 none (by decide +kernel),
  ternaryRule 115 83 0 83 0 l83 none (by decide +kernel),
  ternaryRule 115 51 0 51 0 l51 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x0 : Ex 115 4 [v31,u5,u6,u0,u4] :=
  certify c115 [] (unpack 4 0x2912191220c01930088110a00890208130202102108111201102 40 0x83c880b8868763a3607003401898767655432210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x1 : Ex 115 5 [v21,u5,u6,u0,u1,u4] :=
  certify c115 [⟨_,p115x0⟩] (unpack 5 0x3830385040024003098321408000400008811120099220c010a0089020813020304040051081 53 0xa1c94a1454a83d49539491b52d4a5ac4a56a2a8c54a0a519ca5318a5318a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p115x2 : Ex 115 6 (roots 115) :=
  certify c115 [⟨_,p115x1⟩] (unpack 5 0x8000304030202912191221401930098320c020814005210210814004110240030881400210a040010992400011200890 160 0x6d56b53acebd6d56b96b350e7338ce35114338e734ce732ccb34d1332ce71302c13a4e1324c1382e1264912c2b1242912e4b3402131e273423031c276b80e231ec239ee6b00c52c0b224a922cab5240931ca73200031c07318a510800104611106310400) (by decide +kernel)
theorem l115 : Claim 115 7 := fromSearch 84 (by decide +kernel) p115x2

def c117 : Cuts (goalAt 117) := [
  ternaryRule 117 113 0 113 0 l113 none (by decide +kernel),
  ternaryRule 117 101 0 101 0 l101 none (by decide +kernel),
  ternaryRule 117 85 0 85 0 l85 none (by decide +kernel),
  ternaryRule 117 53 0 53 0 l53 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p117x0 : Ex 117 6 (roots 117) :=
  certify c117 [] (unpack 5 0x3020383038501a2422401a3020c020814003220410a0108140023040088140010a040284028140000a100890 160 0x6d54a6b90e6d5156b94a6d0e76b9ae6d1b46b8e74cce74aa4a4ce524a8e76b0636ba2e6b22c6b8634a4634aa0a48a104a8633146331c273142531c636b88e6b1ec6b9ee6b0844a88a4a16b4a96a4a08431c873140531c073148410c031048410c8310400) (by decide +kernel)
theorem l117 : Claim 117 7 := fromSearch 2 (by decide +kernel) p117x0

theorem r102x98x4x5 : Red 102 98 4 5 := markLift 102 98 4 5 l98 (by decide +kernel)
def c118 : Cuts (goalAt 118) := [
  ternaryRule 118 98 0 98 0 l98 none (by decide +kernel),
  ternaryRule 118 102 0 102 0 l102 none (by decide +kernel),
  ternaryRule 118 86 0 86 0 l86 none (by decide +kernel),
  ternaryRule 118 116 0 116 0 l116 none (by decide +kernel),
  ternaryRule 118 102 16 98 4 r102x98x4x5 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p118x0 : Ex 118 5 [v14,u1,u5,u2,u4,u6] :=
  certify c118 [] (unpack 4 0x2912191222401306302030400b060a040b120a10110211204002214021022204 53 0x81f185e589980101868d65c5677651b5a10104898467654321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p118x1 : Ex 118 4 [v24,u1,u6,u2,u4] :=
  certify c118 [] (unpack 4 0x29120b1230200a040b060a10224022042102214011021120 40 0x83b386856353087806a639301871165114312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p118x2 : Ex 118 5 [v17,u1,u6,u2,u4,u5] :=
  certify c118 [⟨_,p118x1⟩] (unpack 5 0x8000400219122912130622402204304011020b060a040b120a102102214022061120 53 0x81a510421e6439061b46639cc443106219641ac645ac8a42502118e6110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p118x3 : Ex 118 5 [v79,u1,u6,u2,u4,u5] :=
  certify c118 [] (unpack 5 0x1912291213060b060b1221002102112030401102400140040a0422400a1022042140 53 0x7520e43c0e453d423b8e41106250d4749d09234891304b5250741cc42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p118x4 : Ex 118 4 [v31,u5,u6,u2,u4] :=
  certify c118 [] (unpack 4 0x2912191213061a240a0422400a10220430202102214011201102 40 0x83c380b08687637360a003401898167653432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p118x5 : Ex 118 5 [v21,u5,u6,u1,u2,u4] :=
  certify c118 [⟨_,p118x4⟩] (unpack 5 0x38301a241a3022400b060a040b120a10214080001120400321023020304022241102 53 0xb1c16b13d6b7bd6b4ada91b529139296b5265b1664a9261a0c831907318a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p118x6 : Ex 118 5 [v110,u5,u6,u1,u2,u4] :=
  certify c118 [] (unpack 5 0x3830191213060b060b12300030201102400140040a0422400a102140112021023040 53 0x6540c64bd26218a4514844b922334c22308250c491246b52506398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p118x7 : Ex 118 6 (roots 118) :=
  certify c118 [⟨_,p118x0⟩,⟨_,p118x2⟩,⟨_,p118x3⟩,⟨_,p118x5⟩,⟨_,p118x6⟩] (unpack 5 0x80048003302029121a2419121a30130640042240800280012102220440038000110240023040214019300b0640010a0413240b12400011200a10 160 0xe698c5c150de95a5c18c364a5340d036699340b035ca53330c35f17330ac13c0f1427013e6f140105d400132cc156d55b00c31665350003140531a739403073d2f8c13073c2f5b12c728216b02c5a92931c213150531d073142510c211008010c8310020) (by decide +kernel)
theorem l118 : Claim 118 7 := fromSearch 17957968 (by decide +kernel) p118x7

theorem r105x104x1x5 : Red 105 104 1 5 := markLift 105 104 1 5 l104 (by decide +kernel)
def c121 : Cuts (goalAt 121) := [
  ternaryRule 121 113 0 113 0 l113 none (by decide +kernel),
  ternaryRule 121 104 0 104 0 l104 none (by decide +kernel),
  ternaryRule 121 105 0 105 0 l105 none (by decide +kernel),
  ternaryRule 121 105 16 104 1 r105x104x1x5 none (by decide +kernel),
  ternaryRule 121 89 0 89 0 l89 none (by decide +kernel),
  ternaryRule 121 57 0 57 0 l57 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p121x0 : Ex 121 4 [v32,u5,u6,u0,u4] :=
  certify c121 [] (unpack 4 0x2c181c1820c01c30088110a00890208130202408108114201408 40 0x83c880b8868763a3607003401898767655432210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p121x1 : Ex 121 5 [v21,u5,u6,u0,u3,u4] :=
  certify c121 [⟨_,p121x0⟩] (unpack 5 0x38303850400240030c89244080004000088114200c9820c010a0089020813020304040051081 53 0xa1c94a1454a83d49539491b52d4a5ac4a56a2a8c54a0a519ca5318a5318a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p121x2 : Ex 121 6 (roots 121) :=
  certify c121 [⟨_,p121x1⟩] (unpack 5 0x8000304030202c181c1824401c300c8920c020814005240810814004140840030881400210a040010c98400014200890 160 0x6d56b53acebd6d56b96b350e7338ce35114338e734ce732ccb34d1332ce71302c13a4e1324c1382e1264912c2b1242912e4b3402131e273423031c276b80e231ec239ee6b00c52c0b224a922cab5240931ca73200031c07318a510800104611106310400) (by decide +kernel)
theorem l121 : Claim 121 7 := fromSearch 20484 (by decide +kernel) p121x2

theorem r108x104x4x5 : Red 108 104 4 5 := markLift 108 104 4 5 l104 (by decide +kernel)
def c124 : Cuts (goalAt 124) := [
  ternaryRule 124 104 0 104 0 l104 none (by decide +kernel),
  ternaryRule 124 108 0 108 0 l108 none (by decide +kernel),
  ternaryRule 124 108 16 104 4 r108x104x4x5 none (by decide +kernel),
  ternaryRule 124 92 0 92 0 l92 none (by decide +kernel),
  ternaryRule 124 116 0 116 0 l116 none (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p124x0 : Ex 124 5 [v13,u3,u5,u2,u4,u6] :=
  certify c124 [] (unpack 4 0x2c181c182240160c0e180a10302030400e0c0a04140814204003244024082204 53 0x60f665e6677601016a6da5c5a4baabba509081010467654321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p124x1 : Ex 124 4 [v30,u3,u6,u2,u4] :=
  certify c124 [] (unpack 4 0x2c180e1830200e0c0a040a10224022042408244014081420 40 0x73b77675635360a6078739301787165144312110) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p124x2 : Ex 124 5 [v16,u3,u6,u2,u4,u5] :=
  certify c124 [⟨_,p124x1⟩] (unpack 5 0x800040031c182c18160c0e1822400a102204304014080e0c0a0424082440220c1420 53 0x619cd0319e4338841b48429489330c4491491a86912d295292831cc2110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p124x3 : Ex 124 5 [v103,u3,u6,u2,u4,u5] :=
  certify c124 [] (unpack 5 0x1c182c18160c0e180e0c24002408142030401408400140020a0422400a1022042440 53 0x7520e43c08453c823b8e41106250d424b44749d092308b5250741cc42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p124x4 : Ex 124 4 [v32,u5,u6,u2,u4] :=
  certify c124 [] (unpack 4 0x2c181c18160c1a240a0422400a10220430202408244014201408 40 0x83c880b88687637360a003401898167655432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p124x5 : Ex 124 5 [v21,u5,u6,u2,u3,u4] :=
  certify c124 [⟨_,p124x4⟩] (unpack 5 0x38301a240e0c2440800040040a0414200e181a3022400a1022043020304022241408 53 0xa1c14a13d4a7bd49539491b52d4a5ac4a56a2a8c54a0a5198a511ca5318a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p124x6 : Ex 124 5 [v110,u5,u6,u2,u3,u4] :=
  certify c124 [] (unpack 5 0x38301c180e0c0e18160c300030201408400140020a042440142022400a1022043040 53 0x6540c64bcc4338c451489224a6118622344250c424b12b52506398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p124x7 : Ex 124 6 (roots 124) :=
  certify c124 [⟨_,p124x0⟩,⟨_,p124x2⟩,⟨_,p124x3⟩,⟨_,p124x5⟩,⟨_,p124x6⟩] (unpack 5 0x8004800330202c181a241c188002800140048000304024401c300e0c220424081a30160c4003140840020a044001224016240e18400014200a10 160 0xe692953a4edea5a5392e364e7338ce36519338e735ce73270935f17324e7b342da3a2eab62da382e52629a48219a42954a3133c2131e0733e0f31c271380e134ad138ae1340d52c001258912d8b5240931ca73200031c07318a511000104611106310400) (by decide +kernel)
theorem l124 : Claim 124 7 := fromSearch 36852736 (by decide +kernel) p124x7

theorem r61x21x40x6 : Red 61 21 40 6 := markLift 61 21 40 6 l21 (by decide +kernel)
theorem r59x42x17x6 : Red 59 42 17 6 := markLift 59 42 17 6 l42 (by decide +kernel)
theorem r55x21x34x6 : Red 55 21 34 6 := markLift 55 21 34 6 l21 (by decide +kernel)
theorem r47x42x5x6 : Red 47 42 5 6 := markLift 47 42 5 6 l42 (by decide +kernel)
theorem r29x21x8x5 : Red 29 21 8 5 := markLift 29 21 8 5 l21 (by decide +kernel)
theorem r58x42x16x5 : Red 58 42 16 5 := markLift 58 42 16 5 l42 (by decide +kernel)
theorem r46x42x4x5 : Red 46 42 4 5 := markLift 46 42 4 5 l42 (by decide +kernel)
theorem r23x21x2x5 : Red 23 21 2 5 := markLift 23 21 2 5 l21 (by decide +kernel)
def c63 : Cuts (goalAt 63) := [
  ternaryRule 63 61 0 61 0 l61 none (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 none (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 63 61 2 21 40 r61x21x40x6 none (by decide +kernel),
  ternaryRule 63 59 4 42 17 r59x42x17x6 none (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 none (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 63 55 8 21 34 r55x21x34x6 none (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 none (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 63 47 16 42 5 r47x42x5x6 none (by decide +kernel),
  ternaryRule 63 31 0 31 0 l31 none (by decide +kernel),
  ternaryRule 63 29 2 21 8 r29x21x8x5 none (by decide +kernel),
  ternaryRule 63 62 0 62 0 l62 none (by decide +kernel),
  ternaryRule 63 58 4 42 16 r58x42x16x5 none (by decide +kernel),
  ternaryRule 63 53 2 21 32 r53x21x32x5 none (by decide +kernel),
  ternaryRule 63 46 16 42 4 r46x42x4x5 none (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (2,u0,u1)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (2,u0,u1)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (2,u0,u1)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (1,u0,u2)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (1,u0,u2)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (2,u0,u4)) (by decide +kernel),
  ternaryRule 63 62 0 62 0 l62 (some (2,u2,u4)) (by decide +kernel),
  ternaryRule 63 43 4 42 1 r43x42x1x5 none (by decide +kernel),
  ternaryRule 63 42 0 42 0 l42 none (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (1,u0,u2)) (by decide +kernel),
  ternaryRule 63 53 0 53 0 l53 none (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 63 21 0 21 0 l21 none (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (1,u1,u5)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (3,u1,u5)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (1,u3,u5)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (3,u3,u5)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (2,u0,u2)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (2,u0,u2)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (2,u0,u2)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (2,u0,u5)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (1,u0,u5)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (3,u0,u5)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (1,u0,u5)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (0,u2,u5)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (2,u2,u5)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 63 23 8 21 2 r23x21x2x5 none (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (2,u0,u3)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (2,u0,u3)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (2,u0,u3)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (1,u0,u4)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (1,u0,u4)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (1,u0,u4)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (1,u1,u5)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (3,u1,u5)) (by decide +kernel),
  ternaryRule 63 62 0 62 0 l62 (some (3,u2,u4)) (by decide +kernel),
  ternaryRule 63 43 16 42 1 r43x42x1x5 none (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (1,u3,u5)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (3,u3,u5)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (2,u0,u4)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (2,u0,u4)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (2,u0,u5)) (by decide +kernel),
  ternaryRule 63 43 4 42 1 r43x42x1x5 (some (1,u0,u5)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (0,u0,u5)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (0,u0,u5)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (0,u0,u5)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (0,u0,u5)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (1,u0,u5)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (1,u0,u5)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (2,u0,u5)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (2,u0,u5)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (3,u0,u5)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (3,u0,u5)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (3,u0,u5)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 63 43 0 43 0 l43 none (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (1,u2,u4)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (1,u1,u4)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (1,u1,u4)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (1,u1,u5)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (3,u3,u5)) (by decide +kernel),
  ternaryRule 63 31 0 31 0 l31 (some (2,u1,u3)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (0,u0,u1)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (3,u0,u1)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (3,u1,u5)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (1,u2,u4)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (1,u2,u5)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (1,u2,u5)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (1,u2,u5)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (3,u2,u5)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (3,u2,u5)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (3,u2,u5)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (1,u4,u5)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (1,u3,u4)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (1,u3,u4)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (1,u3,u5)) (by decide +kernel),
  ternaryRule 63 31 0 31 0 l31 (some (3,u1,u3)) (by decide +kernel),
  ternaryRule 63 53 8 21 32 r53x21x32x5 none (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (0,u0,u3)) (by decide +kernel),
  ternaryRule 63 47 0 47 0 l47 (some (3,u0,u3)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (1,u4,u5)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (1,u4,u5)) (by decide +kernel),
  ternaryRule 63 61 0 61 0 l61 (some (3,u4,u5)) (by decide +kernel),
  ternaryRule 63 59 0 59 0 l59 (some (3,u4,u5)) (by decide +kernel),
  ternaryRule 63 55 0 55 0 l55 (some (3,u4,u5)) (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x0 : Ex 63 8 [v51,u0,u1,u2,u3,u4,u5] :=
  certify c63 [] (unpack 6 0x1a2419120d120c891a3013060689070609830383050811024010400f0583400e09920589400d0386030540000284400c1081400b1408400a0881400940080a0440070502400640051420400440030281400240010a10 308 0x4e938e352a924e9aa935238e4d02492121924d019021225236724920ea0e767a2734e24e4e50c30929924e59a50920c334b0c308e00e6cb00b34e0c32230c30899097639232090c355f65f55255255f11f55265236266254e54e56212234e64e2092095466465496492062060a16615435435611210836435556204d25d261f4df4d24d261f5df34e5ce60b68b78e68e34b5cb21c5dc60974975c75c2095c90836836005c06c35c30806805595595585d75555565555541124521104d011211211045034e30e10b3cb10e10e34b30b2091c91062861091092061c6083043100140103103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x1 : Ex 63 7 [v111,u0,u1,u2,u4,u5] :=
  certify c63 [] (unpack 5 0x1a2419121a301306400e07060d180983070c03831120400c0281400d09920a100589050840120284068c0583401303861420108111020d12088140070a040502 240 0xa7863a1be6a7bfea1863a7273a1ba6a73bca1a73d8673d8e03d8601d8e7316a101027316a7310200495c549aa6496a5499c64e1ce48f234e33848dc34d9ce4cef34daf64cdd3482a049dce481c069eb5919069164591a869150590d039062190e239050194e339411094d13942304bd6f4b90e4bd084b96e6a90c481604a96a4810011806114e5118e61140010c031048110c8310400) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x2 : Ex 63 8 [v112,u0,u1,u2,u3,u4,u5] :=
  certify c63 [⟨_,p63x1⟩] (unpack 6 0x1a24191214080d120c891a301306400e068907060d18098314201120070c0383400f05830992038403860508400c1081400b1102400a0881401440080a044007800040124005050240040281401140010a10400d058940000284 308 0x5ab451415b155abb2b4154515aa2492d58155aa82a2d52554282492d1a51728a684112515a61c71959d55a69e61951c740e1c719111194e10e4111c72e31c71899097239232c91c70535d30557d50537d30555d54215d70518910618a14115d12c97c90605d70495c92e07df19d5d704778705d79d1875c70d56150d30d30d55950d36134116110ce68e0d169140e60e2db61b0c90c90db71b2c96091876870c46040c76071846840410590436180570570d55150d30d30d55950d35134113d10ce0ce0d149140e3ce2c328a0c90c90c334c2c92891871470c40c40c7207184144043042041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x3 : Ex 63 4 [v15,v113,v35,u0,u2] :=
  certify c63 [] (unpack 4 0x706038308900386028102840a0411200983088105021081 40 0x70b774a776790101648675726225210224321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x4 : Ex 63 5 [v113,u1,u3,v35,u0,u2] :=
  certify c63 [⟨_,p63x3⟩] (unpack 5 0x68913060890068c038602840a040c8909830881050214080383028114208000112011021081 60 0x29245282252b4b0691ed689cd004012b0a96a52c491694894948409400e0114c51106208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x5 : Ex 63 5 [v114,u1,u3,v35,u0,u2] :=
  certify c63 [] (unpack 5 0x7060890038602840a04058309830881038305081120130602810502140811021081 60 0x20e042348f68d6369dcd230896a52c48d6949d49484093910419c66010a40800100c4000420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x6 : Ex 63 5 [v15,v115,v35,u0,u2,u5] :=
  certify c63 [⟨_,p63x3⟩] (unpack 5 0x130603830890038602840a0405831120098308818000050207060281050011021081 57 0x3040634bc600802360dcc2a8ac4b587080e358cec39d672a8e74a0e5018051906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x7 : Ex 63 5 [v116,u1,u3,v35,u2,u5] :=
  certify c63 [] (unpack 5 0x13060689098308810a041408038314201120050803861081110202810890050205830284 60 0x21a2422a04714ce2348e7282e725ee039cd61986298a6491644a829400e0314c52008310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x8 : Ex 63 6 [v115,u1,u3,v35,u0,u2,u5] :=
  certify c63 [⟨_,p63x4⟩,⟨_,p63x5⟩,⟨_,p63x6⟩,⟨_,p63x7⟩] (unpack 5 0x130606890890068c03864018800302840a040c890983400a4019088114081102038311201420800280018000108140174004028105020508 77 0x22ec424e84561582a0b344e29455e94b568e615c2989d473a6e4c9ce545ce83dcd2b4ac2b0aa12c4a4a0e53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x9 : Ex 63 6 [v15,u1,u3,v35,u0,u2,u5] :=
  certify c63 [⟨_,p63x6⟩] (unpack 5 0x130607060890038602840a040583098308811408142003830281050205088000112011021081 77 0x6048c62c4c639cc00802671a0e2b0ae23dce7bdca081466994e529aa2b14a22d4a5ad450240808020218e62906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x10 : Ex 63 6 [v117,u1,u3,v35,u0,u2,u5] :=
  certify c63 [] (unpack 5 0x130606890890068c0a040c8909830881140805000508142011021081038302810386028405021120 77 0x434c8444886398e4112224404248c4c3998479182631ec4398c4b58c6b58b32cc731cc92148a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x11 : Ex 63 6 [v118,u1,u3,v35,u0,u2,u5] :=
  certify c63 [] (unpack 5 0x13060706089003860a04058309830c890881110203830500050211201408108106890281068c028414200508 77 0x4354844d08661984112624c1224484d619a4891a26b62d4c1ad43dad739a931ccc330c822c8a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x12 : Ex 63 5 [v119,u1,u5,v35,u0,u2] :=
  certify c63 [] (unpack 5 0x160c07060890038602840a0409830583088103830281108305081420050214081081 60 0x30206309e6330ce0040c611ac6092232cc86210b404084114840928218e6200a01104310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x13 : Ex 63 5 [v120,u1,u5,v35,u0,u2] :=
  certify c63 [] (unpack 5 0x1306089003860a040983088103831102070602810284058314081081050805021120 60 0x38e07398ef1a469309c63b4eb32d6d5a46b5898b584ab11d4748d2309d07098a108c8310420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x14 : Ex 63 5 [v121,u1,u5,v35,u2,u3] :=
  certify c63 [] (unpack 5 0x706160c1408098308810a04142003831183050803860583050202810890110210810284 60 0x285e12162420604694cd2308d6bc2d6a1cd035ac2a0ab4114440521400e0014c52008308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x15 : Ex 63 6 [v122,u1,u5,v35,u0,u2,u3] :=
  certify c63 [⟨_,p63x12⟩,⟨_,p63x13⟩,⟨_,p63x14⟩] (unpack 5 0x706160c0890038640188002058302840a0414080983400a401908811420038305081081108380018000050240174004028111021120 77 0x54c5222e8424e4532d0a298b098a67355e73b566d2d1a2909b36b64d8a5ad541ad7b9a55158a12c4a4a0e53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x16 : Ex 63 5 [v123,u1,u5,v35,u0,u2] :=
  certify c63 [] (unpack 5 0x130607060890038602840a0409830583088103830281110205081120050214201081 60 0x30206309e6330ce0140560dac6092232cc86210b4140840d4840928198e6280a01104310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x17 : Ex 63 5 [v22,u1,u5,v35,u0,u2] :=
  certify c63 [] (unpack 5 0x1306089003860a041183098308811408038302810284058310811102112005020508 60 0x38e07398ef30d83301c63b4ea3294d50d8a5016a504aa01d071a46009d07098a12106110420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x18 : Ex 63 6 [v14,u1,u5,v35,u0,u2,u3] :=
  certify c63 [⟨_,p63x16⟩,⟨_,p63x17⟩] (unpack 5 0x800180000706130608900386058302840a04118309830881108114200502038302811102112010830508 77 0x619cd431a64348841c4842948d338c46920d1ac6d13dad7bda9339246112d4a5891ad29129295292831cc2110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x19 : Ex 63 6 [v124,u1,u5,v35,u0,u2,u3] :=
  certify c63 [] (unpack 5 0x706160c089005830a0414081100112010810502142003830281038602840983088111020508 77 0x9535464c8c6544c44bd2621a0a6a884594824bc4671844109c26a84258c494256b31ccc5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x20 : Ex 63 6 [v33,u1,u5,v35,u0,u2,u3] :=
  certify c63 [] (unpack 5 0x70613060890038605830a04118309831a2408810383110011020508142005021a30028112a4028410811120 77 0x649cc4354844d082344c4112624bd224484c34584811826320c4bd8c4398c6b586418e822c8a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x21 : Ex 63 5 [v125,u3,u5,v35,u2,u1] :=
  certify c63 [] (unpack 5 0x3831120038613060706089005080983028108810a04148902840583050210811102 60 0x52208004011284f511c4405a8409882210b3a92741907380273886721ce6104a11106208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x22 : Ex 63 5 [v126,u3,u5,v35,u0,u2] :=
  certify c63 [] (unpack 5 0x13060706038308900386028102840a04058309830881108905080502112011021081 60 0x5820b58deb591cb5a96d0040150d035118a5a566518c93040630d06310e6180a020c6208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x23 : Ex 63 5 [v127,u3,u5,v35,u0,u2] :=
  certify c63 [] (unpack 5 0x1306070608900a040583098308811408038302810386028411021081050805021120 60 0x38e07385e7394ee19064285813b4ea2a94d5106a5058a5096a08d2311d07114c520c8308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x24 : Ex 63 6 [v128,u3,u5,v35,u0,u2,u1] :=
  certify c63 [⟨_,p63x21⟩,⟨_,p63x22⟩,⟨_,p63x23⟩] (unpack 5 0x3831120800280011306070640174004038608904018800005080983028102840a0411020583400a4019088105021081108914081420 77 0xe669891a4647132ec5dcc1d98c2558ca4d8b7496c5b22348d2b2208b83d65734ac530ab2954548ca5220a5398a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x25 : Ex 63 5 [v129,u3,u5,v35,u0,u2] :=
  certify c63 [] (unpack 5 0x160c06890890068c02840a0414200c89058908811408070c028111021081050205081120 60 0x28e252ae052b4af19c6d6adcd6852d2b0a86a10c41c6842d484052838ce3094c520c0310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x26 : Ex 63 5 [v28,u3,u5,v35,u0,u2] :=
  certify c63 [] (unpack 5 0x1306070608900a041183058308810689028105890284108114081102112005080502 60 0x40e08401e84190e30d83301604350a3294d50d8a5016a504ea00c800a128098e62948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x27 : Ex 63 6 [v13,u3,u5,v35,u0,u2,u1] :=
  certify c63 [⟨_,p63x25⟩,⟨_,p63x26⟩] (unpack 5 0x383112080018000160c068903860890068c05080983028102840a0414890c89088110811408142010890502 77 0xc5554c1d194632936324a1c54a1414a8414963d2a4a9c919d29135296b52562caa428a92950519ca5118a5318a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x28 : Ex 63 6 [v130,u3,u5,v35,u0,u2,u1] :=
  certify c63 [] (unpack 5 0x38313060386089009830a0411021400142010810508112006890281068c02840c89088114080502 77 0x934ccd535484a506548c659cc44c48621a0a6a9a4594824bc4671844109c26a84258c4c5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x29 : Ex 63 6 [v34,u3,u5,v35,u0,u2,u1] :=
  certify c63 [] (unpack 5 0x383160c07060386089009830a04148905831a240881140014080502112005081a30028112a4028410811420 77 0x62548649cc8320e44d08444c8234844112224b8424350b34164791625adeb4b96b4356b6316a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x30 : Ex 63 7 [v35,u0,u2,u1,u3,u5] :=
  certify c63 [⟨_,p63x8⟩,⟨_,p63x9⟩,⟨_,p63x10⟩,⟨_,p63x11⟩,⟨_,p63x15⟩,⟨_,p63x18⟩,⟨_,p63x19⟩,⟨_,p63x20⟩,⟨_,p63x24⟩,⟨_,p63x27⟩,⟨_,p63x28⟩,⟨_,p63x29⟩] (unpack 6 0x800b800a8009140880088007800680058004800380028001800014201120070c03831a3013060689070612a4068c400e038640181a24108111020c890583050205890983400a050802810a10401602840881401708900a04 240 0xae830ca90790a687a89d031098f20f95075090f74f8d021088c74c85e20880c20c7de75d09b20808770709b71b0872070991c70906900996990901c70971c708c60c09761708c1c751011048f58f51059048f10f50d10448c54c50d54d48c10c50b1044884c850b4d34881040870470861040871070860412500c324f44f25045024f0c324d0c324c38c24d38d24c0c324b0c324828824b28a2480c31470c70860000870070860c31440040810c30840c3081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x31 : Ex 63 7 [v15,u1,u3,v36,u0,u2,u4,u5] :=
  certify c63 [⟨_,p63x9⟩] (unpack 5 0x191213060a1007060a0412210890038602848000401d058340044003401c14080c89142003830281058905020508401511201102108109830881 98 0x2e0122da520c27493e5295292218860c0289a5ed43c4f435694ad68218860982513c4f07bdc7134470300b18862300203254932106398a41886208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x32 : Ex 63 5 [v131,v22,u1,u5,u0,u2] :=
  certify c63 [] (unpack 4 0x130603860a04140803830281028410a01081112005080502098311021a240881 60 0xa2faa0daa9a8928295e90d095aba2c2550304aba49847724644540300210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x33 : Ex 63 6 [v22,u1,u5,v36,u0,u2,u4] :=
  certify c63 [⟨_,p63x32⟩,⟨_,p63x17⟩] (unpack 5 0x19120a1013060a041221089003868001800011830589140809830881038302810284058310811102112005020508 77 0x91d9274ccf538e874cd2639a5130da3302064bd2e68da30254901d07031801ac600a54909d07098a1094a12106110420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x34 : Ex 63 7 [v14,u1,u5,v36,u0,u2,u3,u4] :=
  certify c63 [⟨_,p63x18⟩,⟨_,p63x33⟩] (unpack 5 0x19120c898001401507060a1013060a0412210890038602848000401f0583118340044003401e108109830881142005020383028113241102112010830508 98 0x123f252a524e9ea4e341f873eca9b94a7d17251e0a5318a9ba6733c0e59dab31bc7315273a5269926303c0ef1bc6e6b58b125493a0e2114c51108218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x35 : Ex 63 7 [v33,u1,u5,v36,u0,u2,u3,u4] :=
  certify c63 [⟨_,p63x20⟩] (unpack 5 0x19120c8907060a1013060a0412210890038680004020058311830983038305891100110205081a240881142005024001028112a40284401a4004400b10811120 98 0x16efad2bf2d2e524ebd1ce9e9f8776cebd2ca54d1272e70574dc56dcabb2eb44d13374dcd5c9696a54d3c4ed841af7358b62d495250719cc53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x36 : Ex 63 5 [v131,v28,u3,u5,u0,u2] :=
  certify c63 [] (unpack 5 0x1306070605830a040689028110a00284108114081120050811021a2405020c890881 60 0x5920b589eb581ab5a56a49144489c203409110e22ad8b2a549420e4308a2280200106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x37 : Ex 63 6 [v28,u3,u5,v36,u0,u2,u4] :=
  certify c63 [⟨_,p63x36⟩,⟨_,p63x26⟩] (unpack 5 0x19120a10130607060a041221089080018000118305830c8908810689028102840589108114081102112005080502 77 0xa1d9485491540e88402685494741e3038da33818053d4e68da3601800296a00c800a96a0a12809cc7098c12948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x38 : Ex 63 7 [v13,u3,u5,v36,u0,u2,u1,u4] :=
  certify c63 [⟨_,p63x27⟩,⟨_,p63x37⟩] (unpack 5 0x1c1809830383058911208001401b0a10160c06890a0405080386028112210890068c0284800040211489162440074004401e10810c8908811408142010890502 98 0x83f908529284f1292eca9ce5283dd374a6f54a6644acb121de5215a52b5a44a91cea4dd27460e1adce13dce7bdc46918b1ac6a128484a0e6110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x39 : Ex 63 7 [v34,u3,u5,v36,u0,u2,u1,u4] :=
  certify c63 [⟨_,p63x29⟩] (unpack 5 0x1c180983038305890a10160c07060a0403861221089080004022148905830c891400140805021a240881112005084001028112a40284401a4004400b10811420 98 0x16efad2bf2d27e9d3ce252e525a96a8ebc1f67768e76e4ebc2ca54dca72daa5748a56c5aba2e72749d16c5ad5c16f7358b62d495250719cc53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x40 : Ex 63 8 [v36,u0,u2,u1,u3,u4,u5] :=
  certify c63 [⟨_,p63x30⟩,⟨_,p63x31⟩,⟨_,p63x34⟩,⟨_,p63x35⟩,⟨_,p63x38⟩,⟨_,p63x39⟩] (unpack 6 0x1a2419128005800414080d120c89800380020d180983800114201120070c0383400340001306068907060a1012a440190a04068c400e05890386401b05080281400d0284122140010890401a1081400b1102400a8000088140164008400740040583401540050502 308 0x7322081cdccd732cf21cd208c6f00008d9cdc2f9ef08d00d1ed000088b8872dbad1c8008b0b54b58d98dacb98b58d54d1e9555588a88729aa91c85480809805a7555a005400a79a64245554149544249644145541235555a26181236185a255542151440d40d42112140d5141db51440840841b11b1c851409f51440080041f81f0805144104de64d48d4cb74b64d74d4cb48b1c84884db71b7087081db4920834924c06806436830804805984924d55d56585d759549241441441349241041141040f10d30d10b38b10d10d10b30b1c81881042891081081c4186083043100140103103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x41 : Ex 63 7 [v132,u5,u0,u2,u1,u3,u4] :=
  certify c63 [] (unpack 6 0x40191a24400a40080d120c891489400740050d18098314200b12070c118340031120400040040e180706402b1a30402a028118b008810a04068c0583050205890386050840290a10108140280890402710a0400102844026400d1102 243 0x2d4d326c26db2c2534eb492a934eb4d3a924a83cf4e94e8a684cf4e73cf2622678a224f2663cf9628a68a294f3e330c4e44e39234cc4cf74f88c30f30f89d76130c2a02a182028c31f30c25d25f75d24c25e30c71d75e75d70c3126d24ca4d22924cb4d928a3da3d96993ca3cb28a25724b5d724a24b28a6175cb5d558a5530d34944935134830d00c33d13d04503c33ce0c330d30e34d3030cb1452830c10c32852890c90451491490430c80c31051c61451030c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x42 : Ex 63 7 [v15,u1,u3,v37,u0,u2,u4,u5] :=
  certify c63 [] (unpack 5 0x1912130607060b120280038602840a040281089005830589401c4003400d14080c8914200a10070c05020508402411201102108109830881 98 0x2d8122d0a80a0127c9d38c244310c14056f54d4f13d4d6ad6d6a886218280a4e513c4f0340cf6b9a71304702c0a188623002032506398a41886208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x43 : Ex 63 6 [v22,u1,u5,v37,u0,u2,u4] :=
  certify c63 [] (unpack 5 0x19121306028003860a040281089011830589070c1408098308810a1007060284058310811102112005020508 77 0x91d5314c5281d0698a4d3320c370cc0919314c60f70dc3681a002549021801ac600a5490a0e1098a1094a12106110420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x44 : Ex 63 7 [v14,u1,u5,v37,u0,u2,u3,u4] :=
  certify c63 [⟨_,p63x43⟩] (unpack 5 0x19120c8980004024070613060280038602840a0405830281089011834000401e4003400d108109830881142005020b120a101102112010830508 98 0x103e21094a0c8da0c339b46366689a086c1883b8c85291134528691ad42506f1d055a52b5a22689c8d23460f1bc6e1304d5b16a1212831cc2110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x45 : Ex 63 6 [v133,u1,u5,u0,u2,u3,u4] :=
  certify c63 [] (unpack 5 0x19120c8907061306058303860983070c08810a04142005021a300a100281089010a0028410811102058911200508 84 0x712ce5baae591846b9ae4ae8b49264735c52ae4b314a920c832822503a0e5816c025e019064735cd62d8b52508394c520c8310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x46 : Ex 63 7 [v33,u1,u5,v37,u0,u2,u3,u4] :=
  certify c63 [⟨_,p63x45⟩] (unpack 5 0x19120c8907061306028003860a0405830281089011830589400d8000400b0983070c1100110205081a240881142005021a300a1012a4028410811120 98 0x10bea0c8e20cb39ae8ba086d988bd2d1740846b1b222097358958122e8bd8d6356935cd725494f8c1ea43906518ea2354c5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x47 : Ex 63 6 [v28,u3,u5,v37,u0,u2,u4] :=
  certify c63 [] (unpack 5 0x19121306070602800a0402810890118305830c8908810a10070c05890284108114081102112005080502 77 0xa1d150541491cc690480a828d1324c368cc060150541ee68da360180384e10296a00c800a96a0a501098e62948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x48 : Ex 63 7 [v13,u3,u5,v37,u0,u2,u1,u4] :=
  certify c63 [⟨_,p63x47⟩] (unpack 5 0x1c180983070c112080004023160c0e18038602800a10068c02840a04058905080281089014894005401e4007400d10810c8908811408142010890502 98 0x83e9085291c4e11d3db9c3d3b4e76b2e7620481263b8e62b4e76b4c902462eac6919c46b8c4528c6528920483dcf7358b1ac6a120493a0e6110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x49 : Ex 63 6 [v134,u3,u5,u0,u2,u1,u4] :=
  certify c63 [] (unpack 5 0x1c180983070c160c070603860c8908810a04112005081a300a100281089010a00284110210811408058314200502 84 0x792cf63eaf62a8c611a40300d73dcf51264502407b9e633226398ca20c863004003e0f010647b9ee6b1ac5a929418e62148310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x50 : Ex 63 7 [v34,u3,u5,v37,u0,u2,u1,u4] :=
  certify c63 [⟨_,p63x49⟩] (unpack 5 0x1c180983070c160c0706038602800a04058902810890148905830c891400140805021a240881112005081a300a1012a40284400d8000400b10811420 98 0x16eead2be2d27da52e525a96aacbb2ceed38edcb576594a9c16e5395d2295b16aecbb55354d272749d16c5ad5c16f7358b62d495250741cc53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x51 : Ex 63 8 [v37,u0,u2,u1,u3,u4,u5] :=
  certify c63 [⟨_,p63x41⟩,⟨_,p63x42⟩,⟨_,p63x44⟩,⟨_,p63x46⟩,⟨_,p63x48⟩,⟨_,p63x50⟩] (unpack 6 0x1a2419128005800414080d120c89800380020d1809838001142011200b12070c1a3013060e18070612a44019068c0386028002840a1080001081400b1102400a0881402540080a044007058340244005050240030589402340000508400d028140010890 308 0x730451415c55730c70415451bed2492d5955bad96d2d525542b2492d1b1172bb2b411251a93113195915a53913195115427104191a11727a274111112c99091a51049891092e59240631040578970638a20571040605d70558550608600555d540e40e0515d104e5ce4114112de5d70497c905e7de2c95c90d56150d37530d57550d36134116110ce0ce0d171140e6182cc6180c96c90cc6cc2c96091876180c46840c769a1846180410590436180570570d55150d30d30d55950d35134113d10ce0ce0d149140e3ce2cc28c0c90c90cc34c2c92891871470c40c40c7207184144043042041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x52 : Ex 63 8 [v60,u0,u3,u1,u2,u4,u5] :=
  certify c63 [] (unpack 6 0x1a2419121a3013060689400440010d180983070c038340034000112014080c8905024010400e0281402e0c980a10400f0589401305080583400d068c050340050284402d1081400b1102400a40070881402c40080a04 308 0x2690c3088a88269aa90880c36275d7588a08627a275885d70805d75835036005000835d72cb5d72cf98f2c49a62cf5d71255145a45d71255d75a45144c64064487484c67464484080a24104438c34e28e20834035a04104578574e08605974172cf75d2d14102cf4102cb75d11f75d45e41011f41045e75d2dc3dc2c82c82dc11c2c83c809b3cf2c32c32db11b0833c32cb39a2483483862462482483863460833433805406435430803405975573943546173575945544523523904d04d24d24503502cf2cf2ce34d2cb2cc2cb2ca1081c81062461081081061c6083043100140103103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x53 : Ex 63 7 [v135,u0,u3,u2,u4,u5] :=
  certify c63 [] (unpack 6 0x1a2419121a301306400e068907060d120c89400c1102400d09920583402f028405890386068c108114080d1808810a04070c028140030a1005080502400614201120 240 0x5df28a5cd80d5df81f5cd28a5dd1c75cd78d5dd79d5cd1c77091c770a14a70914970a1c709a1c70836c309a6da0831c708c0c308d04d08c04c08d0cd0980c308a64a09865808a0ca54d3cd55655654d5cd5563d654a3ca54950954a50a5493c95475075453c55473c75455050933d30833830933930833c34903910843d10903cf08438418d10d18c00c18d00d18c10418a10a1892c918a2ca189109187107185205187207185104083003081104083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x54 : Ex 63 8 [v136,u0,u3,u1,u2,u4,u5] :=
  certify c63 [⟨_,p63x53⟩] (unpack 6 0x1a2419121a301306400e068907060d180983070c03831120142014080d120c890c98400f05890582068c0502402d1081400b1102400a0881403140080a0440040281403040010a1040038000402f40000508400d058340050284 308 0x5ab451415b155abb2b415451a2930c2d5a95a29aa92d530c40e30c2d1251a0e24e41130c06630c0579d70669e605730c6d31131958556d38531951154241041919516e49644111112e210418c8cc6e28e22cc10c05785706010405711706086105f5d705581505f81f0555d541d5d705179105d79d4115d10d56150d30d30d55950d36134116110ce70e0d171140e60e2cc70c0c96090cc60c2c970919a61a0c40c40da6da1846040410590436180570570d55150d30d30d55950d35134113d10ce0ce0d149140e3ce2cc28c0c90c90cc34c2c92891831450c40c40c3207184144043042041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x55 : Ex 63 4 [v113,v38,v15,u0,u4] :=
  certify c63 [] (unpack 4 0xd12038609830a0408810890028411200383050210810281 40 0x71b7787554a51212479721210870600504300210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x56 : Ex 63 5 [v115,v38,v15,u0,u4,u5] :=
  certify c63 [⟨_,p63x55⟩] (unpack 5 0x19120386098311020a040890028411200383058302818000108105020d1208810500 57 0x124024691a16054a4bd4a19c6d234890b826690c6604cb319464a0c619cc32148308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x57 : Ex 63 6 [v38,v15,u1,u3,u0,u4,u5] :=
  certify c63 [⟨_,p63x56⟩] (unpack 5 0x1912038614080c891420800011200983110210810a0408810890028405020583050803830281 77 0x74c8e95254741ca520c85144a58c4a44c1243bcee5254911d67209ac5254959d6702920020e030005010600082000420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x58 : Ex 63 7 [v15,u1,u3,v39,u0,u4,u2,u5] :=
  certify c63 [⟨_,p63x57⟩] (unpack 5 0x130680004035070619120a040a10182102840992089014080c890583142003830281058905020508403411201102108109830881400a4003401c 98 0x185e3183b336c6698acb18d6b065c0ee5314ccb32439569253d524ad329ce45314ca2c4aa1c06a7bd4e314c54b1ac48c834ad6952507314c520c8308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x59 : Ex 63 5 [v123,v38,u1,u5,u0,u4] :=
  certify c63 [] (unpack 5 0x19120386098305080a0408900284110211200383058302810d120881050214201081 60 0x182031b06a02409521ea508c240dc348120134482b065594aa2a4052a0e5288c510c8310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x60 : Ex 63 5 [v22,v38,u1,u5,u0,u4] :=
  certify c63 [] (unpack 5 0x1912038614080a040890118309830881028405831081110211200508050203830281 60 0x496094b5284156540de81a5492b8a303520600080156000c2012549120e2318a22084310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x61 : Ex 63 6 [v38,v14,u1,u5,u0,u4,u3] :=
  certify c63 [⟨_,p63x59⟩,⟨_,p63x60⟩] (unpack 5 0xc89800180001912038610811420098310830508050205830a0408810890028411021183112003830281 77 0xa3d0ea2395352a47244e76b4e55254741ca520c85140a5840af5394211da72098b02920020e030005010600082000420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x62 : Ex 63 5 [v137,v22,u1,u5,u0,u4] :=
  certify c63 [] (unpack 5 0x19120589028414080983089010a01081112005080502038308810a1011021a300281 60 0x20a0422c8a5894259de70380b3918413447380a03118432d464a446418c7300a00106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x63 : Ex 63 6 [v22,u1,u5,v39,u0,u4,u2] :=
  certify c63 [⟨_,p63x62⟩,⟨_,p63x60⟩] (unpack 5 0x8001800013060a0419120a101821028411830589140803830281098308810890058310811102112005020508 77 0x93c1354a6891cd3238e274c126399ee30da33018068da30254901d07031801ac600a54909d07098a1094a12106110420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x64 : Ex 63 7 [v14,u1,u5,v39,u0,u4,u2,u3] :=
  certify c63 [⟨_,p63x61⟩,⟨_,p63x63⟩] (unpack 5 0xc898001403407068000403613060a04191205830a1018210284099208901183400a4003401e108114200502038302810983088119301102112010830508 98 0x125f1535aa523527a94f0e9d9ce5a1f473e4e3c1ce841ee51d8a5318b04d527a1e0584e501bc70146108c60f1bc6e6b58b4a92211d07114c51108218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x65 : Ex 63 6 [v38,v33,u1,u5,u0,u4,u3] :=
  certify c63 [] (unpack 5 0xc89191203860983110014201a2412a410811120050205830a0408810890028411021183050803831a300281 77 0xb4550b2c1682d1065a9684a0c6290a61cccb1ae034491128e0b82de87a1c6719ac02d4002500380060148000c4000420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x66 : Ex 63 7 [v33,u1,u5,v39,u0,u4,u2,u3] :=
  certify c63 [⟨_,p63x65⟩] (unpack 5 0xc8907068000403713060a04191205830a10182102841183038309830589110011020508142005021a3002814008088118b00890401a400a400b10811120 98 0x167f1d77bad6e62d2bea527b27894ed2ed2727760e55dd69b24a72d68574dc56c1b374dcb6ad8d4c92d3c4ed841af7358b62d495250719cc53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x67 : Ex 63 5 [v113,u1,u3,v38,u0,u4] :=
  certify c63 [⟨_,p63x55⟩] (unpack 5 0x1912068c03860a04089002840689038302810c89050214080983088114208000112011021081 60 0x282452bcad6922d68a0d0040153caa7294d5118a5096a5040a21525400e0114c51106208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x68 : Ex 63 5 [v114,u1,u3,v38,u0,u4] :=
  certify c63 [] (unpack 5 0x3860a04089002840583038302810c89098305081120191208810502140811021081 60 0x23c8d68d8369e0d53c8a7294d50d8a51d6a5040a191243910419c66010a40800100c4000420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x69 : Ex 63 5 [v116,u1,u3,v38,u4,u5] :=
  certify c63 [] (unpack 5 0x191203830890028114080c8909831420112005080386108111020a040881050205830284 60 0x19a23714ce7106e7282e7260e7b9c0699a650d83298a648d634a829400e0314c51906010820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x70 : Ex 63 6 [v115,u1,u3,v38,u0,u4,u5] :=
  certify c63 [⟨_,p63x67⟩,⟨_,p63x68⟩,⟨_,p63x56⟩,⟨_,p63x69⟩] (unpack 5 0x1912068c0386403880030a04089002840689038340044039028114080c89110209831120142080028001800010814025400a088105020508 77 0x22ec4561582b0a944ea9456694c5e8f615efb09f57be8f4cdef549ef8c1ee2b8a91344c2b0aa12c4a4a0e53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x71 : Ex 63 6 [v117,u1,u3,v38,u0,u4,u5] :=
  certify c63 [] (unpack 5 0x1912068c0a040890068914080c890500050814201102108109830881038602840383028105021120 77 0x644cc84a1268988454884594824a042898501088253c4258c4e4390a334c94250b31ccc5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x72 : Ex 63 6 [v118,u1,u3,v38,u0,u4,u5] :=
  certify c63 [] (unpack 5 0x191203860a040890058303830689028111020983050005021120140810810c890881068c028414200508 77 0x43508661984910424c12244c4d619ad911b16b44d4c1ad43dad739a931cc92148c330c822c8a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x73 : Ex 63 5 [v119,u1,u5,v38,u0,u4] :=
  certify c63 [] (unpack 5 0x1c1803860a040890028403830583028109831083050814200c890881050214081081 60 0x182031b86c0040c619ec609424b8696a52c48409499694894930d03300e01184510c8310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x74 : Ex 63 5 [v120,u1,u5,v38,u0,u4] :=
  certify c63 [] (unpack 5 0x191203860a04089003830281098311020c8908810284058314081081050805021120 60 0x38e073b8e61a469309e65b8eb6ad665a46b5898b584ab11d4748d2309d07098a108c8310420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x75 : Ex 63 5 [v121,u1,u5,v38,u4,u3] :=
  certify c63 [] (unpack 5 0xc891c18140803830890028114200983118305080386058305020a040881110210810284 60 0x28e23285e118603614cc6106c63c2c621cc6b1802a0ab40d4340521400e0014c51906008820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x76 : Ex 63 6 [v122,u1,u5,v38,u0,u4,u3] :=
  certify c63 [⟨_,p63x73⟩,⟨_,p63x74⟩,⟨_,p63x75⟩] (unpack 5 0xc891c1803864038800205830a040890028414080383400440390281142009830508108110838001800005024025400a088111021120 77 0x5168454c5224e4522d4a2a0a498a65256252bda4d2d5ada09b36b64d8a5ad541ad7b9a55158a12c4a4a0e53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x77 : Ex 63 6 [v124,u1,u5,v38,u0,u4,u3] :=
  certify c63 [] (unpack 5 0xc891c1805830a04089014081100112010810502142009830881038602840383028111020508 77 0x9348c953546544c44c1267988a6a884594824c0427984e108826a84258c494256b31ccc5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x78 : Ex 63 5 [v125,u3,u5,v38,u4,u1] :=
  certify c63 [] (unpack 5 0x98311200386191205080383089002810c891489058305020a040881028410811102 60 0x60e03004012b0af609c2185a34b1694906948029494c95252228d03284e1288c51906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x79 : Ex 63 5 [v126,u3,u5,v38,u0,u4] :=
  certify c63 [] (unpack 5 0x191203860a04089002840583038302810c8910890502112005080983088111021081 60 0x102021384c0040161966611ec4b8496a52c48409499694914930902300e0218c52086208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x80 : Ex 63 5 [v127,u3,u5,v38,u0,u4] :=
  certify c63 [] (unpack 5 0x19120a04089005830c89140809830881038602840383028111021081050805021120 60 0x48e094bd2719064385a12bd25714a729065285a50a58908d631254911d07114c520c8308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x81 : Ex 63 6 [v128,u3,u5,v38,u0,u4,u1] :=
  certify c63 [⟨_,p63x78⟩,⟨_,p63x79⟩,⟨_,p63x80⟩] (unpack 5 0x9831120800280011912038640388000050803830a0408900284110205834004403902810c890502108110894025400a088114081420 77 0x121684d334c791f32c5e423584e955c2809c6699ae3b0eea4dc9945298092f4a5c9699293b1295a927120473148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x82 : Ex 63 5 [v129,u3,u5,v38,u0,u4] :=
  certify c63 [] (unpack 5 0x1c18068c0a040890028406890589028114200c8914080d18088111021081050205081120 60 0x28e252bcad19c6d6a60d6856d53caa7294d51c6a5258a5056a4950538ce3094c520c0310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x83 : Ex 63 5 [v28,u3,u5,v38,u0,u4] :=
  certify c63 [] (unpack 4 0x19120a0408901183058302810c89088105890284108114081102112005080502 60 0x83f88e8663c360b0ae8adaa6a3caa0baa17a089803401898167655432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x84 : Ex 63 6 [v13,u3,u5,v38,u0,u4,u1] :=
  certify c63 [⟨_,p63x82⟩,⟨_,p63x83⟩] (unpack 5 0x9831120800180001c180386068c050803830a040890028414890689028110810c8908811408142010890502 77 0xe2548e1d1d473a9373a441c4842948a741446114a1a54a13d4a7bd47734e7610eb39d471a4e7120e7420e6110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x85 : Ex 63 6 [v130,u3,u5,v38,u0,u4,u1] :=
  certify c63 [] (unpack 5 0x9831912038603830a0408901102140014201081050811200c890881068c02840689028114080502 77 0x934ccd535484a506548c44c4867988a6a9a4594824c0427984e108826a84258c4b31ccc5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x86 : Ex 63 6 [v34,u3,u5,v38,u0,u4,u1] :=
  certify c63 [] (unpack 5 0x9831c18038603830a040890148905830c89140014080502112005081a24088112a402841a30028110811420 77 0x8354c85a50a429265d0c444c86898845bc84539424484289850108825bc425384a334cc5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x87 : Ex 63 7 [v38,u0,u4,u1,u3,u5] :=
  certify c63 [⟨_,p63x70⟩,⟨_,p63x57⟩,⟨_,p63x71⟩,⟨_,p63x72⟩,⟨_,p63x76⟩,⟨_,p63x61⟩,⟨_,p63x77⟩,⟨_,p63x65⟩,⟨_,p63x81⟩,⟨_,p63x84⟩,⟨_,p63x85⟩,⟨_,p63x86⟩] (unpack 6 0x800b800a8009140880080d120c8980078006800580048003800280018000142011200d1809831a24191212a4068c400e038640381a3010811102068905830502058903834004050808810a0440330890028140250a100284 240 0xae830ca90710a687289d03100a530c0879870a59a508730790f20f8d06d088f6cf85021080c6cc7dc20878c20c75c6db0992080876870996990872070971c70906100976170901c751001048f58f51059048f00f50d00048c54c50d54d48c00c50b0004884c850b4d34880000870070861060871070860002500c324f44f25045024f0c324d0c324c38c24d38d24c0c324b0c324828824b28a2480c30870c30860460870470860c31440440800c30840c3080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x88 : Ex 63 5 [v137,v28,u3,u5,u0,u4] :=
  certify c63 [] (unpack 5 0x1912058302840c89089010a0108114081120050808810a1011021a30050206890281 60 0x31206330cb61164609e20380c119a611122399a63b16752924408e238020018a00106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x89 : Ex 63 6 [v28,u3,u5,v39,u0,u4,u2] :=
  certify c63 [⟨_,p63x88⟩,⟨_,p63x83⟩] (unpack 5 0x80018000130607060a0419120a101821028411830583068902810c89088108900589108114081102112005080502 77 0xa4415652aaa1d14a04d5240e285414741dee38da33818068da3021280318000c800a96a0a12809cc1098c12948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x90 : Ex 63 7 [v13,u3,u5,v39,u0,u4,u1,u2] :=
  certify c63 [⟨_,p63x89⟩,⟨_,p63x84⟩] (unpack 5 0x8001403a160c0689038309831120800040320a041c180a10028105890508182102840c9808901489400a4007401e10810c8908811c301408142010890502 98 0x2459cbd297643e4a42dca5bdca12d4a05c96118c203c4310862f085aa51d0a5318b29c98c8460563dcc1ac6c1358c6b58b1ac6a4a507114c51108218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x91 : Ex 63 7 [v34,u3,u5,v39,u0,u4,u1,u2] :=
  certify c63 [⟨_,p63x86⟩] (unpack 5 0x8000403b160c0706038309830a041c180a1005891821028414890c8905831400140805021a300281112005084008088118b00890401a400a400b10811420 98 0x167b2fcb5f56ee2d6ddad2bd2d27c9d35aa52e525a96ab0775cebb2ca54d5272d265749c56c1b2749cd3c4ed841af7358b62d495250719cc53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x92 : Ex 63 8 [v39,u0,u4,u1,u2,u3,u5] :=
  certify c63 [⟨_,p63x58⟩,⟨_,p63x64⟩,⟨_,p63x66⟩,⟨_,p63x87⟩,⟨_,p63x90⟩,⟨_,p63x91⟩] (unpack 6 0x8005800414080d120c89400740051a3013060689070680034004400180028001800014201120070c03830d1809834003400019120a0418b00c980583403405024019028140330a10401009920589403205080881400d0890182140080284401a1081400a400b1102 308 0xcf1514543883cb18b15435031af51418ac0a1afc2f18a50a0ae51456d5960ae59656d5144eb492443b034ebb2b443492569492454a944e9aa955449218649218a40a18241018a4920a70a84664920a74924660a69402c03038439008403032c35548543222cb8d42d456286145f2cb3128124df81f4522d219d2cb18a78a19d79d18a2ca09c2cb31b34d09c34d31b2cb19a28a18318319a09a18328a1862593c32032406003c36032402005562082545d43d65d65542144522122504d04d24d245020830d20824b38b3cd38d30b20b18a18a189208186187186185083043080100083083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x93 : Ex 63 7 [v138,u5,u0,u4,u1,u2,u3] :=
  certify c63 [] (unpack 6 0xd120e0c14894007400506890706400a403f1a30400440011420070c03830d180b0611834003112040001a2408810c980583050212a402810a100992058905080a04108140280284402710a040080890403e400d1102 243 0x294512aa2a9aa929146845125e26879e25126745199e7a779e9914643cf46546496444f3ca3cf8ce38a38a18f3e23cf26126286124f3e038e7cf3e03cf7ce3915d178b2d12d17975dc2cb3dd3dc75c3cb3da2cb29b29a6da28b2992cb2572595d724b2582cb5975d85d758b2c628a25524655524a24628a11554655410a5120c34534524d244344f0cf39038f40f3830cc0c32cd2cc34c2c32c61452832810c32852890c90451491490430c80c71051c61451030c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x94 : Ex 63 7 [v15,u1,u3,v40,u0,u4,u2,u5] :=
  certify c63 [] (unpack 5 0x1306070619120880099208900a100881028405830589401c4003400d14080e0c14200383028105020508403d1120110210810b060a04 98 0x102d211402107ca1094a002c084310d14456f5054f13d4d0356d6a88621a288a4e513c4f0340cf6b9a71304702cea188623212830020398a41886208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x95 : Ex 63 6 [v22,u1,u5,v40,u0,u4,u2] :=
  certify c63 [] (unpack 5 0x1306191208800a1008810284118305891408038302810a040b060890058310811102112005020508 77 0x9821291cd281c869824d1320c368cc0601304c1ee68da360180284a102549020e81ac600a5490a0e1098a12106110420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x96 : Ex 63 7 [v14,u1,u5,v40,u0,u4,u2,u3] :=
  certify c63 [⟨_,p63x95⟩] (unpack 5 0xe0c8000403d07061306191208800992089005830a100881028411834000401e4003400d108114200502038302810b060a041102112010830508 98 0x104e21034a368468c8c98d2218c3c18c739883b8c85292889a0d2352d42506f1d055a52b5a4d1341a469460f1bc6e1304d5b16a42502118e6110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x97 : Ex 63 6 [v139,u1,u5,u0,u4,u2,u3] :=
  certify c63 [] (unpack 5 0xe0c070613061912058303830b061420050202810a101a240a040881028410a0089010811102058911200508 84 0x6a6ad691c46368c62d2c6126c492442b62d62d85324a920c8328040681ae0320c025e919064735cd62d8b5250839cc520c8310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x98 : Ex 63 7 [v33,u1,u5,v40,u0,u4,u2,u3] :=
  certify c63 [⟨_,p63x97⟩] (unpack 5 0xe0c070613061912088005830a100881028411830589400d8000400b03830b06110011020508142005021a3002811a240a0418b0089010811120 98 0x104e210b4a0c8d98d6218cbd188bcac48ba0d630b02209735895255d1741ac6b56935cd725494f8c1e85212a338ca2348c5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x99 : Ex 63 6 [v28,u3,u5,v40,u0,u4,u2] :=
  certify c63 [] (unpack 5 0x13060706191208800a100881028411830583068902810e0c0a0408900589108114081102112005080502 77 0xa8214a1d14a04d481c86a828f13a0e368ce060150541ee68da360180304c10212000c800a96a0a12809cc12948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x100 : Ex 63 7 [v13,u3,u5,v40,u0,u4,u1,u2] :=
  certify c63 [⟨_,p63x99⟩] (unpack 5 0x160c068903830b0611208000403c1c1808800c98089002810a10058905080881028414894005401e4007400d10810e0c0a041408142010890502 98 0x23024623e4622dc63bdc5d1d45c4c91c3c3b0e762ee75883a9085292308ca4e7ba922486b1c85394a739461183dcf7358b1ac6a120493a0e6110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x101 : Ex 63 6 [v140,u3,u5,u0,u4,u1,u2] :=
  certify c63 [] (unpack 5 0x160c070603830b061c1805890e0c02810a10112005081a240a040881028410a00890110210811408058314200502 84 0x7b94f792cf782af63e8f62a6a611a40300d512447b9e63322c3a8ca20c833004002a00010647b9ee6b1ac5a929420e62148310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x102 : Ex 63 7 [v34,u3,u5,v40,u0,u4,u1,u2] :=
  certify c63 [⟨_,p63x101⟩] (unpack 5 0x160c070603830b061c1808800a1005890881028414890583400d8000400b0e0c1400140805021a300281112005081a240a0418b0089010811420 98 0x1162210be210ada0c8d20c4c90cb3994651c8bc111640846a9ae22097258951522c8b54d5352725c9715454e83dca2354c5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x103 : Ex 63 8 [v40,u0,u4,u1,u2,u3,u5] :=
  certify c63 [⟨_,p63x93⟩,⟨_,p63x94⟩,⟨_,p63x96⟩,⟨_,p63x98⟩,⟨_,p63x100⟩,⟨_,p63x102⟩] (unpack 6 0x8005800414080d120e0c1a3013060689070680038002800114201120070c03830d180b061a24191218b00c9840190992088008900a0480001081400b110240070583403d4005050240040281401740010a1040030589403c40000508400d088140080284 308 0xc6f38e415955c2f96f41539506d38e057b9706dbad05738e6eb30c2d5b156ebb2b2d530c42930c2cea8e6e9aa940e30c05730c04b24905725704130ca131131959159d391319511540e90e1a510498e10e4259242e210418c8cc6e28e22cc10c06010405785706086005711705e5d70557d505e7de0555d50d56150d37530d57550d36134116180ce70e0d171140e60e2cc60c0c90c90cc6cc2c96181876180c46840c76871846040410590436180570570d55150d30d30d55950d35134113d10ce0ce0d149140e3ce2cc28c0c90c90cc34c2c92891871470c40c40c7207184144043042041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x104 : Ex 63 7 [v141,u0,u5,u2,u3,u4] :=
  certify c63 [] (unpack 6 0x1a2419120d120c89400e06890706400f1a3013060a04068c05830a100890118305890386400d02840d180983088105021420070c0383400302814040108111201102400b14080508 240 0xa234d0838c30a28e208334d72030c70d84d72086070d30d08130c0832c30812c108330c7d91c77cd58d7d95997cd1c771d1c770c78c71d79d70c1c709a1c70836c309a6da0831c744d40d45955944d54d45941045741044c60c45761744c40c44754745641044740745655509441008308309409408340319341044048045349244041020e00020d3cd20e3ce20d00d20c10c20b00020c00c20b104209000207287209289207007083005181105083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x105 : Ex 63 7 [v142,u0,u5,u1,u3,u4] :=
  certify c63 [] (unpack 6 0x1a2419120d120c8940190d180983400c142011201408070c0383068c058305890386050812a40284400d08900a100a0408810689070640040502404110811a301306400b11020281 240 0xa22cb0818c10a28e20812cb7e01c77cb84b7e08607cb1cb0991c70816c10996d90811c771d49270b78b71d79d70b48b70768771b49270748771b69a0814810996990816810994922174922006002176172004803cb40b3cc38c3cb38b3cc4103d54103c75873d55953c74073d44103d24d23d44d33d241008241008144108f4510814011803803cd4103c04003cd38e20c00020b34b20c34c20b000209000207287209289207000083000181105083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x106 : Ex 63 7 [v143,u0,u5,u1,u2,u4] :=
  certify c63 [] (unpack 6 0x1a241912400e1a301306068907060d180983070c0383400c11200a0402810a1008900589038605081489068c0583400d02840d120c89400708814042108114201408400b11020502 240 0xa21c70818c10a28e20811c785655584750785651684755509f55508180109f81f08155521d55520078021d79d20055561b41060770761b71b6074076194106156956196996154150814010835c30815c10834102005c02044102004002045d73072c73164d63074c73162cb3154d53142cb3152d53144d33122cb3104503124513102cb08f2cb08108108f08f0812c118d2cb30038030d38d3002c0209000207287209289207007083005181105083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x107 : Ex 63 7 [v144,u0,u5,u1,u2,u3] :=
  certify c63 [] (unpack 6 0xd120c8906890706400e1a3013061420070c0383400c112014080d180983400a068c0583050202810a1005890386050818b00890400d0a040284404310811a241912400b11020881 240 0x974510817010977170814515224515008c05228e25004407e04107d18517e08607d141009d41008178109d79d0814105084105003c05083c850041065161165c30c65131165c61865a30c6506d065a6da65031008130109761708160109730c51530c5005805155955003002521c72514d12524d22511d125029024f1c72501d024f28a24e1c724c34c24e34d24c1c70821c70812c10892cb0811c11801c02482882402802481c7083000181105083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x108 : Ex 63 8 [v145,u0,u5,u1,u2,u3,u4] :=
  certify c63 [⟨_,p63x104⟩,⟨_,p63x105⟩,⟨_,p63x106⟩,⟨_,p63x107⟩] (unpack 6 0x1a241912402d0d120c89400e068907061a3013060d1809831420400c070c0383112014080a04068c05830a10089005890386028411021103400a80034043400808814007800240424005050240048001404140010281400380004040400005081081400b400d10a0 308 0xb24d3559cd90b2cf25594d356f38e413c13c6fc2f5533930a238e4199d90a29e241938e5612492d3793ba17a155324942c2492ceb4ebacb6c40e2490aa2492d9ad90aaaea2d9249568104193a539a8a6855311340e8ce1a710498e10e4278e32e41041899499a49642c91090991191a28e20998d91a210455369306176105375356169a41f69a04e80e05f81f40e68e2c974905e69a0496892de75d19c69a0446c405c6db18469a08269a0990990810985425140930930825d65535134023cf08e08e08249140e3ce2c228a08908908234c2c9289182145084084082207184144082083082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x109 : Ex 63 8 [v146,u0,u5,u1,u2,u3,u4] :=
  certify c63 [] (unpack 6 0x1a24400a40080d120c89148940074005068907061a30400440010d1809831420070c038311834003112040001102401018b0088140270a04402d058340450502400e12a4028140290a10400c058940440508108110a0400d1103400b0284 308 0x57555505b855d7bae5055555ed4d352c5555ed55552c4d352a3cf415ad54aaaea5153d50693cf4057c54a97df4053c54a83cf4277df4a87df4273cf51330c2d529539329351530c42530c2cf98f3a59a540f30c04e30c2c590538e9242c530c3a328a2e230c3a330c2e228a5201861d585526086051519540f68f1df18624f18f41f69a2dd1861cc78c25d79d2cc18c05c1861c568525c69a1c518525b1861d969a25b69a1d91860c30d85151150d35935d55955131134111040cf48f49149140f10f2cc10c0ca34a38c34c2ca10a1c81040c62462482481c61060450450c3104043042041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x110 : Ex 63 7 [v146,u5,u0,u1,u2,u3,u4] :=
  certify c63 [] (unpack 6 0x1a24402740080d120c8914894005068907061a30402940010d1809831420070c038311831120400018b008810a0440450583050212a402810a10404405890508108110a011034028400b0284403e400d1102 231 0x274d3228227a282134e74929934e74d39924a43cf4e54e49644cf4e33cf21a22369a20f2113cf89a69169a88f3d234d4cc4d23124cd36034d3e13e08603cd35e34d21f21e7df20d35e30c74d35e34d74c31b2494dc4db71b4c94cf58f68924f24f69659824935935865834935724921621759620920b24955658b5965492531d34944935134874901c73d13d04503c73cd1cd30e30d38d30730a1c724b24a2ca2472481080471c41061440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x111 : Ex 63 8 [v147,u0,u5,u1,u2,u3,u4] :=
  certify c63 [⟨_,p63x110⟩] (unpack 6 0x40101a2419120d120c8906890706400e1a3013060d1809831420070c03831120140818b0402d12a4400c108010a01102400a0881403e40080a044007058340474005050240040281402640010a1040030589404640000508400d80001081400b0284 308 0x6e5d7599bd9c2ebee5995d75ac3cf457b577acb6c5973d70603cf4599197a09204593cf59434d317297a5429459734d46a34d30facfa6aaea44f34d06734d319a19a67a2731934d5a51451d79977259a559715744f84f1e414570f14f4648613221451cd8cd7228e230d14d0591591e08607198591e01455976971147d41177d759469445269a10f10f11279244f68f30d68d10a74a10d74d30a68a1c869a1051051087081c568504405b10469a05905959755711411411761759455445241210f10f1124d244f40f30d2cd10a10a10d38d30a2ca1c81881051051082481c51851040c2041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x112 : Ex 63 8 [v148,u0,u5,u1,u2,u3,u4] :=
  certify c63 [⟨_,p63x110⟩] (unpack 6 0xd120c891489068907060d180983070c0383118340100a04402d068c0583400e0a100890400c05890386400d108010810284400a1a2440284008088140071420404a4005050240041a30404940010281400311204048400005081102400b800010a0 308 0x824d35595990a65965594d356f38e413c1392fc2f5533930ae38e4194590ae4514193995652492d381386582555324942c2492ceb4e86cb6c40e2490822492d93190a130c2d924956a104193ad37aaaea55311340e1ce19110478e10e4111c72e8104189a497a8a682c91090a71041991d90a71c71991195536136e57e59937d35656184226186ce8ce9228e240e60e2c97c96e06188496092e07df19d6186c470479d71c18461809b09a0990990826185565160930930965d65535134113d108e08e09149140e3ce2cc28c08908908c34c2c9289187147084084087207184144082083082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x113 : Ex 63 8 [v77,u1,u2,u0,u3,u4,u5] :=
  certify c63 [] (unpack 6 0x1a24191214080d120c8910a04019400f068c05830386400e0284400d089013060b124004070602810983132403834000070c028340010508400c1102400b1081400a0a04404c40080881400740030502404b40051420 308 0x3a918620ba8b3a9aa920b1863a80c308b00b3a802808b0cb2260c30869c68e69e62060c638b78b38d94d38b94b38d78d20678690970990670620979e0a179e8c38838e18a108378341471c41a79e41479e41a71c4d379e4d28204c48204d279e11f71c11d79e10479e11d71c41b51440b40b41b65b40b50b2095094066864096892065060985144034034186580835034104d74cd48d4cb54b4cd54d4cb48b2164964c64c64d61162064860835434c04804c348308054041441441349241041141040f10d30d10b38b10d10d10b30b2091c91062861091092061c6083043100140103103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x114 : Ex 63 7 [v41,u2,u4,v15,u1,u3,u0,u5] :=
  certify c63 [] (unpack 5 0x58303860890028410a0140814200e0c404e1120070c050811020b0640044003404d19120881070605020b120a040a10401d028113061081 98 0xf03f07d9f10d631ad6305ce338c66f8c5ce0b02a72d0e7420ef03c0784e502b8b0246108c60f03c0e2b8ac6b165028092002021d07218c42906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x115 : Ex 63 8 [v15,u1,u3,u0,u2,u4,u5] :=
  certify c63 [⟨_,p63x31⟩,⟨_,p63x42⟩,⟨_,p63x58⟩,⟨_,p63x94⟩,⟨_,p63x114⟩] (unpack 6 0x1a2419121a3013068004068907064004400110a0400c800380020a04800180000a100890068c058305890386400d0284400714080d120c8914200d18070c03834035028105024000050840051120401c1102400b1081400a40030983401d40080881 308 0x9af000086c069afc2f0860009ad3cf406b869adbad4063cf0a33cf400800b238230803cf2ea3cf2ceace2eaaea2ce3cf1293cf4284511044514283cf9866469889c89869c69886480806409637e39007c00a365940f7cf8a065984f64f4207df2dd6592ce78e2dd79d2ce64e35c65934c6cc35c6db34c65910965911a6db1046db11a6592d738e2c62c62d76172c638609538e2c05802d55950803802cb35434830834634634810834630608330c3404c03434c308030041130c34f48f35149140f30f2ce2ce2cd30c2cb2cb2cb2ca1081c81062461081081061c6083043100140103103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x116 : Ex 63 8 [v149,u1,u4,u0,u2,u3,u5] :=
  certify c63 [] (unpack 6 0x14080d12400740051a301306068907064004400110a0400f068c058340190a100b06038640100890400d0284400a1912088105024050193014200383404f0281098340000d18088340080508400c11024003400b1081 308 0x12a45140038012a3aa40044018645118aa4a194a6918a4510a838e42745108245142738e1252cb3009801259a53002cb4232cb3119117e39234112cb19a2cb18a6db19a6db18a2cb0a22cb3216db0826db3212cb10054010380310080010354341d5557d17917dd79d41155130b5cb71b55570b54b31b5d718a55519a5d718a5d719a5552495552486592426592485550985550965d70825d709655519328a1801801935131802801862522432032403c02433c32402004113d124e20e25121140e3ce30d20d24b24b24d08d30b20b18a18a189208186187186185083043080100083083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x117 : Ex 63 4 [v150,v22,v41,u1,u5] :=
  certify c63 [] (unpack 4 0x1408038613061081112005080383050211020284028110a0 40 0x3b36615162a21391883474464151420423031210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x118 : Ex 63 5 [v151,v22,v41,u1,u5,u0] :=
  certify c63 [⟨_,p63x117⟩] (unpack 5 0x386800014081306028410a0108111200508038302810b0605020a041a2411020a00 57 0xc0ac2c441866196c1bd817050831cc8194660b4c462c8a504892110431cc41948308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x119 : Ex 63 6 [v22,v41,u2,u4,u1,u5,u0] :=
  certify c63 [⟨_,p63x118⟩] (unpack 5 0x38608901408070c19120881800002811306028410a010811102112005080a040b060a1007060502 77 0xa3a4ea2cd4a2495252a495292789ca520c85140a5840a43bcee11d67209ac59d6702920420e030005010600082000420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x120 : Ex 63 7 [v41,u2,u4,v14,u1,u5,u0,u3] :=
  certify c63 [⟨_,p63x119⟩] (unpack 5 0x8000404e0e0c058303860890028410a010811420108305081324112019120b060881070605020b120a040a10401f02811306110240044003404d 98 0x1439ab8a56d48d294b5aacacaac3a8ecfc5ad5adac8bdaf6b5eb6b568a9a9e37ca2f4350f3a4ef841e81b8686b50c3a96a38c833a52741cc520c8310420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x121 : Ex 63 5 [v152,u0,u2,v22,u1,u4] :=
  certify c63 [] (unpack 5 0x1912070c1408098311200706108105020281130608810a04058905080a1012a40890028410a01102 60 0x48269326093164604406626097b186615cc60c2c6b40c425095ad404a128198e61948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x122 : Ex 63 5 [v153,u0,u2,v22,u1,u5] :=
  certify c63 [] (unpack 5 0x1408070c108111200706050209831306028110a0058905080a101221089002840a04110219120881 60 0x14c4841e48401a08c44e839c871dee7154e701a0389825ac60289422a12829cc50100300820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x123 : Ex 63 5 [v154,u0,u2,v22,u1,u5] :=
  certify c63 [] (unpack 5 0x14081081112003830502130610a003860890110219120508098302810a0408810284 60 0x3c0e528da37bcec7318560da36014c6048119d6301d47015201806809cc10948108c4310420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x124 : Ex 63 6 [v155,u0,u2,v22,u1,u5,u4] :=
  certify c63 [⟨_,p63x121⟩,⟨_,p63x122⟩,⟨_,p63x123⟩] (unpack 5 0x19121408070c09831081112007064007400f050213060a0410a0058908900a10122180028001088140538000110240524003050802810284 77 0x82ed0246105d14426645246117b965694852656526be52a4e504410c2c4a88220d2bcad1384d62d484a0e53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x125 : Ex 63 6 [v156,u0,u2,v22,u1,u5,u4] :=
  certify c63 [] (unpack 5 0x1912140809831081112003830706050210a005890280028108900a04088113061102070c05080a100284 77 0x6250c2348c4990424bd2d348d1891b06b44d4bd2d431ad739a931d2921526398e82308812c4a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x126 : Ex 63 5 [v157,u0,u4,v22,u1,u2] :=
  certify c63 [] (unpack 5 0x13061408038311200b06108105020881191202810a10050803860a0418b0028410a01102 60 0x41c8840228321e8311a4040065a1e872d66591ab5882b6300b5292040907118a21106210020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x127 : Ex 63 5 [v158,u0,u4,v22,u1,u5] :=
  certify c63 [] (unpack 5 0x1408108111200b0605020383191210a005080386182102840a101102130608810a040281 60 0x24489485c1481808408d7b5a9685cd6994d68180091643114432506304e6018050106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x128 : Ex 63 5 [v159,u0,u4,v22,u1,u5] :=
  certify c63 [] (unpack 5 0x14081081112009830502191210a00386110213060508038308810a04028402810890 60 0x44106311a47bd0c73186611a46094c604a122164121481192220c820a0e1098a10906110420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x129 : Ex 63 6 [v160,u0,u4,v22,u1,u5,u2] :=
  certify c63 [⟨_,p63x126⟩,⟨_,p63x127⟩,⟨_,p63x128⟩] (unpack 5 0x130614080383108111200b064007400f050219120a1010a0038602840a04182180028001028140538000110240524003050808810890 77 0x82e9088310246105c94426559246117b965694852656526be52a4e4c2c4a86a20d2bcad139ad62d484a0e53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x130 : Ex 63 6 [v161,u0,u4,v22,u1,u5,u2] :=
  certify c63 [] (unpack 5 0x1306140803831081112009830d12050210a003860880088102840a100281191211020d1805080a040890 77 0x6250c649cc2348c4990424bd2d348d1891b06b44d4bd2d431ad739a921526418e82308812d0a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x131 : Ex 63 5 [v162,u2,u4,v22,u1,u0] :=
  certify c63 [] (unpack 5 0x38608901408028410a0112005080983038310810502191208811a24110213060281 60 0x6aa0d23c8d0340f6898251124501001384a33586598ca311243010039c46208a40106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x132 : Ex 63 5 [v150,u2,u4,v22,u1,u5] :=
  certify c63 [⟨_,p63x117⟩] (unpack 5 0x140803861081112005080983038305021912130680000281089010a011020a0408810284 60 0x1c46d6858169966682007bc6a7294d50581519665008a08d2130d06304e6018c500c8308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x133 : Ex 63 5 [v163,u2,u4,v22,u1,u5] :=
  certify c63 [] (unpack 5 0x1408108111200983038305021912130610a01102050803860a040881028402810890 60 0x3c0e630da3305817bceb72d6658da3585815890b19d4309d2108c8111d07118a21906208820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x134 : Ex 63 6 [v151,u2,u4,v22,u1,u5,u0] :=
  certify c63 [⟨_,p63x131⟩,⟨_,p63x118⟩,⟨_,p63x132⟩,⟨_,p63x133⟩] (unpack 5 0x386089080038002140840524003028410a0108111200508098303834007400f0502191213060281088180014053800011020a040a10 77 0x13148537ea66c9a6799f33c5e62b09ef338cf3b4efad1ea9c95188950529ea338ca3b4ea62d46124c7120e73148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x135 : Ex 63 6 [v164,u2,u4,v22,u1,u5,u0] :=
  certify c63 [] (unpack 5 0x386140810a010811120098319120a000a1008810284089013061102070c0508070605020a040281 77 0x9344c924d2a429284a5069188453944594824c4508184f108825394258c4a3354b31ccc5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x136 : Ex 63 6 [v165,u2,u4,v22,u1,u5,u0] :=
  certify c63 [] (unpack 5 0x386140810a0108111200b0603830d12050213060a000a04028108900284191211020d18050808810a10 77 0x624886150c649cc8320e4990424bd224390c34991891906304c4bd8c4390c6b5892148822d0a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x137 : Ex 63 7 [v22,u1,u5,u0,u2,u4] :=
  certify c63 [⟨_,p63x124⟩,⟨_,p63x33⟩,⟨_,p63x43⟩,⟨_,p63x125⟩,⟨_,p63x129⟩,⟨_,p63x63⟩,⟨_,p63x95⟩,⟨_,p63x130⟩,⟨_,p63x134⟩,⟨_,p63x119⟩,⟨_,p63x135⟩,⟨_,p63x136⟩] (unpack 6 0x1a241912800b800a800980081a30130680078006800580040a0480038002800180000a100890400c11834053058903860d18070c0d1209830881070603830281058310a040070284108111021408405111200502405214200508 240 0x5eb410647b0766bb2b5c7410aa034da506d0a206e09d034d5e534d6479876659a55c734d9102508e06a08906908602497cd68d79b24974d24d71b69a5d82496472c76582cb5c724709624908054009655508024909100009051009151109001008e00008d4cd08e4ce08d00d0870070861060871070860002910c32904902914912900d028e0c328d3cd28e3ce28d0cd28b0c328930928b30b2890c31470c80860480870470860c31440440800c30840c3080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x138 : Ex 63 8 [v14,u1,u5,u0,u2,u3,u4] :=
  certify c63 [⟨_,p63x34⟩,⟨_,p63x44⟩,⟨_,p63x64⟩,⟨_,p63x96⟩,⟨_,p63x120⟩,⟨_,p63x137⟩] (unpack 6 0x1a241912400a40080d120c894007800540058004068907061a30130640044001800380020a04400f068c0583800180000a100890400c11830386401e10a0400d0284108119300983401f0881400305024051142013240383403602811102112010834000400b0508 308 0x7238e3c5cc5672cf23c538e37138e3f041034d4103f038e3ee30c2cebce82ebee3ce30e05930c2c528566028a2c530c36d36c2eb30c34d30c2eb36b3e11861ce6ceaa16e13ce1862e81861cca4c828a682cc1860661861c59c56669e61c51863651861e420834d2081e41863ce4ce8e16a188e68e3e14d32de4d380c7cc81e7de2cc4cc1c668675b4d37064c61db69a0584d36455456585550454c50824d30845c408d5d70844d33564d335455534d5553544d30820923d010408e44e0904503ce10e2cc10c08a08a08c34c2ca1041c81040862460882481c6106085045082104082083082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x139 : Ex 63 7 [v166,u0,u1,u5,u2,u3,u4] :=
  certify c63 [] (unpack 6 0x1a2419120d120c891489068907061a3013060d1809834003070c038318b0400f058312a410a04048400b0284400a088140080a0440071420400505024004028140010a10403e4027108140001102405505894044112040540508 243 0x2b55522c22bb2b2155693cf56a569aa954f5683cf21122845120f21334d54b5532d354d36634d3e73e69e63cd36434d22522496420d3620005635628e254054f84f44000f00f44345f00036035f81f3403460062032066062002156954de4d57954da4dc69a3dd3dc75c3da3cd68d2db2cd6cd2da2c860819a18868819818469a0030040c401a01961755455359355655351345044f48f45244f40f34c34b38b34e34b30b2072062862092061c61051000c0103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x140 : Ex 63 7 [v41,u2,u4,v33,u1,u5,u0,u3] :=
  certify c63 [] (unpack 5 0xe0c05830386089011000b06070c0508142010a00284108111201a241a30404d4004400b19120881070605020a040a104020028113061102 98 0xc0998c5d98c739a26d1a2090234cc625c47118e2518c8d434ee0a50b62d095a52b5a4cd334a328c1ee2b8ad2348c52d4502408218e6200202906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x141 : Ex 63 8 [v33,u1,u5,u0,u2,u3,u4] :=
  certify c63 [⟨_,p63x139⟩,⟨_,p63x35⟩,⟨_,p63x46⟩,⟨_,p63x66⟩,⟨_,p63x98⟩,⟨_,p63x140⟩] (unpack 6 0x19120d120c898005068907061306800480030a04400f068c0583800280010a1008901183058903860d180983070c0383110011020508400a1a244020400808814007142040564005050240041a30403740010281400d800010a002841081400b40001120 308 0xb14925185580b157151849252f34d3d2c129efc2f51235208234d3d84180a74103d834d528208292892ba88a85122083ec20828db4d9ecb6c3cd2080ab2082982d80ab2eb298208512112aa8868a528525281043e51049cd98d9e59a53cd10d2888489221048c81082a28610a01040981580a014509811805f10405779705f79e05710451c5d705275205c75c5125d23cd3cd0505d704d5cd3d03d029a5d70486c805a6da2885c80410590580980415d75154d50920920955955124d23d039008d08d0904503cd38d28b24b08808808b30b2882480851c5084084085185084084041043042040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x142 : Ex 63 8 [v94,u2,u3,u0,u1,u4,u5] :=
  certify c63 [] (unpack 6 0x1a2419120d180983070c40034000112010a011024019400f0589038640580508068c400e0284400d0890162440070c89050213060e18070640010689048540050281402d1408400b1081400a40040a04405740080881 308 0x829000086a86829aa90860007e16e17068c67e18e17066c60a76db700a007e7a270806c02cf8e32d56db2cf6db2d58e338e6db38d98d3849a638d6db1258e37246db1256db7248e36466066618a164688666162108060080358380058008361871e6187db75b7de75d71b6182cb6182cf68f2d469a2cf61838d59639061838d6183905961195961176181046181175962c83c82c65462c85482c63c60933cf2c02c02d35130803c02cb3923913513863863911113863460833433804003834030803402cf2cf2ce34d2cb2cc2cb2ca1081c81062461081081061c6083043100140103103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x143 : Ex 63 4 [v150,v28,u3,u5,v41] :=
  certify c63 [] (unpack 4 0x1306070606891081140811200508028110a01102028405830502 40 0x53c505b5038065a5998370606242525423432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x144 : Ex 63 5 [v151,v28,u3,u5,v41,u0] :=
  certify c63 [⟨_,p63x143⟩] (unpack 5 0x58380001306070610a002840689028110811408112005080a001a2411020a040e0c0502 57 0xa629ac1b46c0440c1418a1bd40539401a0066358652d494a067018061044510c8310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x145 : Ex 63 6 [v28,u3,u5,v41,u2,u4,u0] :=
  certify c63 [⟨_,p63x144⟩] (unpack 5 0x890058308811912800002811306070610a002840e0c0a040a10070c108114081102112005080502 77 0xa44d5352a6b5296a1ac6a0481140e0341dee38da33818068da3021200318000c800a96a0a12809cc1098c12948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x146 : Ex 63 7 [v13,u3,u5,v41,u2,u4,u0,u1] :=
  certify c63 [⟨_,p63x145⟩] (unpack 5 0xb06070c112080004059050803860890068c10a0028408811c18402102810e180a10160c40074004404d10810e0c0a0416241408142010890502 98 0x2e5e16ecddefbddee3d5f57beb37be257b4a45acab29567294e439ca42a4a539ca251c0a5318a563dcc1ac6c1358c6b58b1ac6952507114c51108218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x147 : Ex 63 7 [v34,u3,u5,v41,u2,u4,u0,u1] :=
  certify c63 [] (unpack 5 0xb06070c03860890058308811c1840220281160c0e0c07061400140805021120050810a002841a240a041a300a10404d4004400b10811420 98 0x167d9d65d2d7ad2d6e62dab6b12bca527c27094e1494a92e5252dbb6c7754e72d265749c56c1b2749cd3c5ad841af7358b62d495250741cc53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x148 : Ex 63 8 [v41,u2,u4,u0,u1,u3,u5] :=
  certify c63 [⟨_,p63x114⟩,⟨_,p63x120⟩,⟨_,p63x140⟩,⟨_,p63x146⟩,⟨_,p63x147⟩] (unpack 6 0x8004800314080d120e0c40074005800280018000142011200d180b060b124003070c40001102068c0583400e0589038640590508400a08900284400d10a01a24191208811a300e180706404e05020a0440010a1040080281404d13064004400b1081 308 0xc2e28a2c0980bee9ae2c02801ac28a189b491acb6c18928a0ab28a2ea30c08230c2ea28aa5e5de600940a1e95e6005c02ca94a6265d79ca5ca2e69651a35d71899091a39231895c92225d72078072228202075d70a15d761f8200a182061f5d76c05006de49e6c04806de51e2dc5146ca74a6dc75c2ca50a61a5146d76576da65961751418651418954919655518951420855520751420251420755508449209351408251409349219024918044019045018024018620f2031c72003802033832001c02cc1c720a34a20c34c2ca1ca1891891881c7186186186185083043080100083083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x149 : Ex 63 8 [v167,u2,u5,u0,u1,u3,u4] :=
  certify c63 [] (unpack 6 0x1a24400a40080d120c89402d400740050d1809831420160c070c4003112040004019068c0583400c05890386405c050810a0400e0284400d089010810a04405b088140040706405a050213061a3011064001400b0281 308 0x5a28a2c5a8569aaaa2c528a26928a2e830c24930c2e828a2e61861ca9ca6a69e62ca18a05f1861c582095f8201c51862641861e38202498201e31862e14d350a88a5e18a12ca4ca1c67065204d35c64c61e071c0454d351f71c5c571c51f4d30824d308479e08979e0844d325d4d351b71c25d71c51b4d32ca40a68c38c68a38a2cc4101d84104466464586581c64065164105d35535d655551341005141044549245149204541008238e08441008941008438e25138e24f41024941024f38e08208d2cc2cc08a10a08c10c2ca2ca1c81080860860882481c6106085045082104082083082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x150 : Ex 63 7 [v168,u2,u5,u0,u1,u3] :=
  certify c63 [] (unpack 6 0xc891420160c070c038309831120068c058305890386400c0508400e10a0400b0890400a02840689070605021a300a100a040281405f10811a241912406013060881 240 0x45e2cb4417df45e7df4412cb3e02cb3c07c03e07df3c02c054b68b55f51454b50b55f69a44151445e69a44169a45e51409c51408774709c75c0875073db5143c06803db69a3c05004d838e4cb64b4d86584cb38b55738e55459455759655438e45138e44149245349244138e08740708938e0873870894103c03803c84083c04003c838e08c1c708b34b08c34c08b1c70811c70832830812810831c70881c70802400882481801c7083000181105083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x151 : Ex 63 8 [v169,u2,u5,u0,u1,u3,u4] :=
  certify c63 [⟨_,p63x150⟩] (unpack 6 0x1a240d120c890d180983160c070c03834019068c0583400c0589038608900a100a0406890706128113060281400a8000405f4008088140071420405e4005050240031120405d40000508400d400e10a002841081400b40011a30 308 0x82492518b180a4b2c51849252a34d3d2ad292aaea5123520a734d3d84100a74103d834d528208292a52868a685122123cd2cd29020884d20d3d02cb0982082a72cb0982cb2a72080652080579970659a505721751211291c79c91279251c1043e210418d8cd1a28e23cd10d2a01048487c88607df28810408210409814508614509810405779705d10405711705d79e51c5d705275205c75c5125d73da5d704d6cd05a6da3cd5d70410590580980415d75024d30920920825955124d23d039008d08d0904503cd38d28b24b08808808b30b2882480851c5084084085185084084041043042040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x152 : Ex 63 8 [v170,u3,u4,u0,u1,u2,u5] :=
  certify c63 [] (unpack 6 0x1a301306068940044001070c03830d1840034000112010a011024019028140620a10400f05890386406105080e0c068c40100890400d0284400a191208811c300c8940050d12088940080502402d14084007400b1081 308 0x76971c6c0a80769aa96c071c19471c18a69a19469a18a71c24971c248a28242a2824871c0a771c6e669a0a769a6e671c65e55e58080065e81e5805406e455559c95c6649646dc55c18655518a8ca18e8e318a55524882024b55524855524b8200a28205a15550a25555a18201003c011e7de1007c011e3de6dc45c75a3cf75c3dc6da4515983cf6555d56585d75953cf18a3cf19445118a4511943cf2493cf2484d32424d32483cf0923cf0904510824510903cf18d28a18018018d38d18028018624c2432032402c02432c324020018a18a189208186187186185083043080100083083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x153 : Ex 63 5 [v152,u0,u2,v28,u3,u4] :=
  certify c63 [] (unpack 5 0x19120c891120070c05081081140807060281130608810a04058305020a1012a40890028410a01102 60 0x4826932649301a67a649899e67960f78c2f739a042509299865ad404a128198e61948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x154 : Ex 63 5 [v153,u0,u2,v28,u3,u5] :=
  certify c63 [] (unpack 5 0x108114081120070c05080c8913060706028110a0058305020a101221089002840a04110219120881 60 0x40a48401c09ce428a1e879e0f7954f781c0389a23a1885ac60289422a12829cc50100300820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x155 : Ex 63 5 [v154,u0,u2,v28,u3,u5] :=
  certify c63 [] (unpack 5 0x108114081120068905081306070610a0058308901102191205020c8902810a0408810284 60 0x29e058c607795a568dc3681406848119d831956301d47015251806809cc10948108c4310420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x156 : Ex 63 6 [v155,u0,u2,v28,u3,u5,u4] :=
  certify c63 [⟨_,p63x153⟩,⟨_,p63x154⟩,⟨_,p63x155⟩] (unpack 5 0x19120c89108114081120070c400340650508130607060a0410a0058308900a10122180028001088140648000110240564007050202810284 77 0x82ed02469022e05346919ce0b714c5365a736be73ad2704410c2c8ac144488220d2bcad1384d62d484a0e53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x157 : Ex 63 6 [v156,u0,u2,v28,u3,u5,u4] :=
  certify c63 [] (unpack 5 0x19120c891081140811200689070c050810a005830280028108900a04088113061102070605020a100284 77 0x6250c234cc22444d34cd2944901344d4bd2d431ad739a931d292152910d26398e82308812c4a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x158 : Ex 63 5 [v157,u0,u4,v28,u3,u2] :=
  certify c63 [] (unpack 5 0x7061306068911200e0c0508108114080881191202810a10058305020a0418b0028410a01102 60 0x4164841c8840228291c5281656a208795a5691c468822631605292040907114c51106210020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x159 : Ex 63 5 [v158,u0,u4,v28,u3,u5] :=
  certify c63 [] (unpack 5 0x1081140811200e0c05080689191210a00583182102840a10110213060502070608810a040281 60 0x21a24205e494a26811c4705e172168701a00998641966411444052802007018a00106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x160 : Ex 63 5 [v159,u0,u4,v28,u3,u5] :=
  certify c63 [] (unpack 5 0x1081140811200c8905080689191210a00583110213060502070608810a04028402810890 60 0x32206311c48c608799a6691c4689426858122164121481192620c820a0e1098a10906110420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x161 : Ex 63 6 [v160,u0,u4,v28,u3,u5,u2] :=
  certify c63 [⟨_,p63x158⟩,⟨_,p63x159⟩,⟨_,p63x160⟩] (unpack 5 0x1306070606891081140811200e0c40034065050819120a1010a0058302840a04182180028001028140648000110240564007050208810890 77 0x82ed0816908831022dc426545246518c5cb614852655926bdb2a4e4c2c4a86a20d2bcad1384d62d484a0e53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x162 : Ex 63 6 [v161,u0,u4,v28,u3,u5,u2] :=
  certify c63 [] (unpack 5 0x1306070606891081140811200c890d18050810a005830880088102840a100281191211020d1205020a040890 77 0x6254c6150c649cc2244424bd2d34cd2944901344d4bd2d4310d739a921526418e82308812c4a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x163 : Ex 63 5 [v162,u2,u4,v28,u3,u0] :=
  certify c63 [] (unpack 5 0x583089010a0028411200c89050806891081140819120502070608811a24110213060281 60 0x71a262408e03810709e231184309065b9ee6996659184581404a502208e4018a00106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x164 : Ex 63 5 [v150,u2,u4,v28,u3,u5] :=
  certify c63 [⟨_,p63x143⟩] (unpack 5 0x1081140811200c890689050819121306070680000281089010a01102058305020a0408810284 60 0x19623185e194a2580da3685e16a1c8680c0095814156840d484052802107014c500c8308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x165 : Ex 63 5 [v163,u2,u4,v28,u3,u5] :=
  certify c63 [] (unpack 5 0x1081140811200c890689191213060706110205830502050810a00a040881028402810890 60 0x3a60738dc38c60979cc730dc3305a11a5830a56109d4108c81124a911d07118a21906208820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x166 : Ex 63 6 [v151,u2,u4,v28,u3,u5,u0] :=
  certify c63 [⟨_,p63x163⟩,⟨_,p63x144⟩,⟨_,p63x164⟩,⟨_,p63x165⟩] (unpack 5 0x58308908003800210a002841081140811200c8906894003406505081912130607060281088180014064800011024056400705020a040a10 77 0x162dcb616c49d26cab2b56ce2c22d0424c92eb5ed5ad0b31384e4c92e5454e83dc92b52a2b14a12d4a4a0e53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x167 : Ex 63 6 [v164,u2,u4,v28,u3,u5,u0] :=
  certify c63 [] (unpack 5 0x58310a01081140811200c8919120a000a100881028408901306110207060502070c05080a040281 77 0x9348c924c8a429284a50434084539424c9318c0cf208825394258c4a3354b31ccb2148c5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x168 : Ex 63 6 [v165,u2,u4,v28,u3,u5,u0] :=
  certify c63 [] (unpack 5 0x58310a01081140811200e0c0689130607060a000a04028108900284191211020d1205020d18050808810a10 77 0x8350c8254885a50a42924348845c082451139c8d1208825c16253d4b31cca3394a2354c5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x169 : Ex 63 7 [v28,u3,u5,u0,u2,u4] :=
  certify c63 [⟨_,p63x156⟩,⟨_,p63x37⟩,⟨_,p63x47⟩,⟨_,p63x157⟩,⟨_,p63x161⟩,⟨_,p63x89⟩,⟨_,p63x99⟩,⟨_,p63x162⟩,⟨_,p63x166⟩,⟨_,p63x145⟩,⟨_,p63x167⟩,⟨_,p63x168⟩] (unpack 6 0x1a241912800b800a800980081a301306070680078006800580040a0480038002800180000a100890400c11834064068c05830d120d180c890881070c06890281058910a040030284406310811408110214200508405611200502 240 0x5ab410605b0562bb2b585410a9f34da50690a1f69f9d034d5a534d6059856259a558534d0a434d0803800a43a408034d8d025089f65f85065081f24978d64d75a24970d24d6da6595972496052c56172cb5852450942490805400945540802400910000904d00914d10900100860000851050861060850002910c32904902914912900d028e0c328d3cd28e3ce28d0cd28b0c328930928b30b2890c92060c70850470860460850c50840410800c00840c3080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x170 : Ex 63 8 [v13,u3,u5,u0,u1,u2,u4] :=
  certify c63 [⟨_,p63x38⟩,⟨_,p63x48⟩,⟨_,p63x90⟩,⟨_,p63x100⟩,⟨_,p63x169⟩,⟨_,p63x146⟩] (unpack 6 0x1a241c18400a400880051a30160c16244004068940010d180983070c0383400f1120800440034000800380020a04800180000281403a0a100890400c0589038640630508402d1489068c401e10a04007400d028410811c300c89402108811408142010894005400b0502 308 0x731861c5d054b3d331c51863721861f120834d2081f11861de6db686646c1e65e1c66db06e6db685bc54aebee6856db0ad6db084ac40adaeb0846db36c6db6aaaeb36caeb6aa6db1e84d3506a465e8a681c64c66a64d351b9db5e69e669b4db0654d35059055e59245054d30829240844d308d4d30849243623635214d33624d35213611c62c681e61e7c66061de2cb69b61b7592cb71b2db6996185162cb5d35535d65555132cb0512cb48538549138e0452cb0822cb08440408d4100842cb34f2cb34c38e34d38e34c2cb08208a1c81040862460882481c6106085045082104082083082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x171 : Ex 63 7 [v171,u0,u3,u5,u1,u2,u4] :=
  certify c63 [] (unpack 6 0x1a241c181a30160c068907060d180983070c0383118340070d120c8918b012a4400c058910a0404a400b0284400a088140080a044004028140010a104003112040000508403e11024027108140051408406705834045142040660502 243 0x2c59622d22cb6c2165944925905944145924aa49222b22aaea2124a8492029028a680124a630c5a75a69e658c5a430c4a54a496448c4a330c20e22338e20c20038088c3003000ce3a00005a15a08605805860002032066462002166d651f5167d651b5126d241e41279241b41c6db31d31c75c31b30864819b1886c81991846db0030040c401b01a6585955945d45975945544914904d049349045038d38c3cc38f38c34c2072062ca2092061c61051000c0103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x172 : Ex 63 8 [v34,u3,u5,u0,u1,u2,u4] :=
  certify c63 [⟨_,p63x171⟩,⟨_,p63x39⟩,⟨_,p63x50⟩,⟨_,p63x91⟩,⟨_,p63x102⟩,⟨_,p63x147⟩] (unpack 6 0x1c188005160c068907060d180983070c0383800480030a04800280010a100890400c058903861489068c05830d120c89140014080502400a1a2440224008088140041a30403b4001028140031120405240000508400d800010a002841081400b40051420 308 0xb14925185580b157151849252634d3d28d2c268e651234d0af34d3d84180af42f3d834d06d34d057b9706dbad05734d52b208292b1286bb2b5122123e920828da8d869aa93cd20d0822082982d80a12cb2982080572d704a2080572170412cb512112a268a69d28925261043cd88d96310490d10d3e38a22a01048487c88607df28810409e10409815809e14509810405c10405775705c75c05711751a5d70526d205a6da5125d20410590580980415d75154d50920920955955124d23d039008d08d0904503cd38d28b24b08808808b30b2882480851c5084084085185084084041043042040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x173 : Ex 63 8 [v172,u4,u5,u0,u1,u2,u3] :=
  certify c63 [] (unpack 6 0xd1240074005068907061a30400440011420070c03831c180d18400311204000402d068c0583406905024019028140600a10400c058903864068050810a040100890400a400d0284108119121a2411124008400b0881 308 0x5f5965c58a269f8a25c5596082596084aaa089aaa0845962695965e88a22698a25e85965e65144d69d65669e65d65140555144c59455559654c55140845140934920844920825142645144e34922644924e35145d67163a234d4563565e271c4e034d3948544608604d435404534d39f71c44571c39f34d08234d08479e08979e08434d25d34d39b71c25d71c39b34d5d81c76966566986585d61d64d42945521c75541d44d228a3901c744d3cd4503cf38d1c704b1c72c530c2cb30c0451c70821c708428a08928a0841c724b1c724828a24928a2481c7082086085045082104082083082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x174 : Ex 63 7 [v173,u4,u5,u0,u1,u3] :=
  certify c63 [] (unpack 6 0xd120c89160c0d18098303831120068c058305890386400c0508400e10a0400b028408901a240689142040040502406b10811a30130619120a100a04405b08810281 240 0x45e28a44630c45e30c44628a09f28a08180109f81f08128154a68a54c51454a50a54c69a44651445e69a44669a45e51409c51408174109c75c0815012db5142c06802db69a2c05004d84104ca64a4d86584ca40a5574105545945575965544104514104464924534924464100814010833c30813c10834102c03c02c44102c04002c43cf0850410863860853850860412cc0002ca34a2cc34c2ca0000860002451c80861c6085000083000081101083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x175 : Ex 63 8 [v174,u4,u5,u0,u1,u2,u3] :=
  certify c63 [⟨_,p63x174⟩] (unpack 6 0xd120c89068907061a30070c03831c180d180983402d068c058340190a10400c0589038608900a0418811912088140071420406c4005050240048000406b4001028140031120406a40000508400d401010a002841081400b40081a24 308 0xa64925185550a655551849206c492057b5706cb6c05749752a34d3d2ad282aaea51234d08234d3d8a580a0a693d834d05a34d0577d705a7da05734d5122d22952087922125152cb3e720828da0d7a7a273cd20d0982082a62cb0982cb2a62080642080579570649640572175211048d28928e18a15121123cd6cd81f10480d10d3df6db29d10478870879d71c28810408210409814508614509810405711705a6da0576d705a1040410590580980415d75154d50920920955955124d23c238e08d08d0824503cd38d28b24b08808808b30b2882480851c5084084085185084084041043042040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p63x176 : Ex 63 9 (roots 63) :=
  certify c63 [⟨_,p63x0⟩,⟨_,p63x2⟩,⟨_,p63x40⟩,⟨_,p63x51⟩,⟨_,p63x52⟩,⟨_,p63x54⟩,⟨_,p63x92⟩,⟨_,p63x103⟩,⟨_,p63x108⟩,⟨_,p63x109⟩,⟨_,p63x111⟩,⟨_,p63x112⟩,⟨_,p63x113⟩,⟨_,p63x115⟩,⟨_,p63x116⟩,⟨_,p63x138⟩,⟨_,p63x141⟩,⟨_,p63x142⟩,⟨_,p63x148⟩,⟨_,p63x149⟩,⟨_,p63x151⟩,⟨_,p63x152⟩,⟨_,p63x170⟩,⟨_,p63x172⟩,⟨_,p63x173⟩,⟨_,p63x175⟩] (unpack 6 0x801980181a24191280178016140880150d120c89801480131a30130680128011068907068010800f800e0d180983800d14201120800c070c0383800b800a800910a010818008110280078006088140080a0480058004068c05834005050280038002028140010a1008908001800005890386400005080284 240 0xef855551ae5aeb8e7851a555df534d39a8dadb58f539a35a53234d395cd5d32cf2515355c6e28a25abdac2ebee25a28a51328a255215b5321351528a3aa28a24dacdb2aaea38d28aa5805809a89aa1889809a05a5250410959959e59a551505538d88d0a304190d04d3a38a225f04108a80a85f81f24a04a79a01a7586d871a6da6580185150155d31d35951d551300038f00048d40d44f40f38d00d24a1ca3080002ca00a2481c70840001810c11440c3081000) (by decide +kernel)
theorem l63 : Claim 63 10 := fromSearch 4146 (by decide +kernel) p63x176

theorem r93x21x72x6 : Red 93 21 72 6 := markLift 93 21 72 6 l21 (by decide +kernel)
theorem r87x21x66x6 : Red 87 21 66 6 := markLift 87 21 66 6 l21 (by decide +kernel)
theorem r79x74x5x6 : Red 79 74 5 6 := markLift 79 74 5 6 l74 (by decide +kernel)
def c95 : Cuts (goalAt 95) := [
  ternaryRule 95 93 0 93 0 l93 none (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 none (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 95 93 2 21 72 r93x21x72x6 none (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (2,u0,u2)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (3,u0,u1)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (0,u0,u2)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (2,u1,u2)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (2,u0,u1)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (0,u1,u2)) (by decide +kernel),
  ternaryRule 95 87 0 87 0 l87 none (by decide +kernel),
  ternaryRule 95 87 8 21 66 r87x21x66x6 none (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 none (by decide +kernel),
  ternaryRule 95 79 16 74 5 r79x74x5x6 none (by decide +kernel),
  ternaryRule 95 31 0 31 0 l31 none (by decide +kernel),
  ternaryRule 95 29 2 21 8 r29x21x8x5 none (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (2,u1,u2)) (by decide +kernel),
  ternaryRule 95 93 0 93 0 l93 (some (2,u0,u2)) (by decide +kernel),
  ternaryRule 95 87 0 87 0 l87 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (3,u0,u1)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 none (by decide +kernel),
  ternaryRule 95 85 2 21 64 r85x21x64x5 none (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (2,u0,u1)) (by decide +kernel),
  ternaryRule 95 87 0 87 0 l87 (some (1,u0,u2)) (by decide +kernel),
  ternaryRule 95 74 0 74 0 l74 none (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (1,u0,u2)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (2,u0,u4)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (2,u2,u4)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (2,u0,u6)) (by decide +kernel),
  ternaryRule 95 75 0 75 0 l75 (some (3,u0,u6)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (3,u0,u6)) (by decide +kernel),
  ternaryRule 95 78 0 78 0 l78 (some (3,u2,u6)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (1,u0,u6)) (by decide +kernel),
  ternaryRule 95 75 16 74 1 r75x74x1x5 (some (1,u0,u6)) (by decide +kernel),
  ternaryRule 95 75 16 74 1 r75x74x1x5 (some (3,u0,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (3,u0,u2)) (by decide +kernel),
  ternaryRule 95 93 0 93 0 l93 (some (1,u0,u2)) (by decide +kernel),
  ternaryRule 95 87 8 21 66 r87x21x66x6 (some (1,u0,u6)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (1,u2,u6)) (by decide +kernel),
  ternaryRule 95 23 8 21 2 r23x21x2x5 none (by decide +kernel),
  ternaryRule 95 75 16 74 1 r75x74x1x5 none (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (1,u4,u6)) (by decide +kernel),
  ternaryRule 95 78 16 74 4 r78x74x4x5 none (by decide +kernel),
  ternaryRule 95 93 2 21 72 r93x21x72x6 (some (1,u0,u6)) (by decide +kernel),
  ternaryRule 95 79 16 74 5 r79x74x5x6 (some (1,u0,u2)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (1,u4,u6)) (by decide +kernel),
  ternaryRule 95 87 8 21 66 r87x21x66x6 (some (1,u2,u6)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (0,u0,u6)) (by decide +kernel),
  ternaryRule 95 93 2 21 72 r93x21x72x6 (some (1,u2,u6)) (by decide +kernel),
  ternaryRule 95 78 16 74 4 r78x74x4x5 (some (1,u2,u6)) (by decide +kernel),
  ternaryRule 95 85 0 85 0 l85 none (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 95 21 0 21 0 l21 none (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (1,u1,u6)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (1,u1,u6)) (by decide +kernel),
  ternaryRule 95 77 0 77 0 l77 (some (3,u3,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (3,u1,u6)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (3,u1,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (1,u3,u6)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (1,u3,u6)) (by decide +kernel),
  ternaryRule 95 71 0 71 0 l71 (some (3,u1,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (3,u3,u6)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (3,u3,u6)) (by decide +kernel),
  ternaryRule 95 87 0 87 0 l87 (some (1,u4,u6)) (by decide +kernel),
  ternaryRule 95 87 8 21 66 r87x21x66x6 (some (1,u4,u6)) (by decide +kernel),
  ternaryRule 95 93 0 93 0 l93 (some (1,u4,u6)) (by decide +kernel),
  ternaryRule 95 93 2 21 72 r93x21x72x6 (some (1,u4,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (3,u0,u3)) (by decide +kernel),
  ternaryRule 95 93 0 93 0 l93 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (2,u0,u3)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (3,u2,u3)) (by decide +kernel),
  ternaryRule 95 87 0 87 0 l87 (some (2,u0,u2)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (0,u2,u3)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (3,u2,u3)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (3,u0,u6)) (by decide +kernel),
  ternaryRule 95 93 0 93 0 l93 (some (1,u0,u6)) (by decide +kernel),
  ternaryRule 95 87 0 87 0 l87 (some (1,u0,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (1,u0,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (2,u0,u6)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (2,u2,u6)) (by decide +kernel),
  ternaryRule 95 79 16 74 5 r79x74x5x6 (some (1,u0,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (3,u2,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (0,u2,u6)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (3,u2,u6)) (by decide +kernel),
  ternaryRule 95 78 16 74 4 r78x74x4x5 (some (3,u2,u6)) (by decide +kernel),
  ternaryRule 95 79 16 74 5 r79x74x5x6 (some (1,u2,u6)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (0,u2,u6)) (by decide +kernel),
  ternaryRule 95 79 16 74 5 r79x74x5x6 (some (3,u2,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (0,u0,u6)) (by decide +kernel),
  ternaryRule 95 93 0 93 0 l93 (some (3,u0,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (1,u2,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (2,u2,u6)) (by decide +kernel),
  ternaryRule 95 78 0 78 0 l78 none (by decide +kernel),
  ternaryRule 95 87 0 87 0 l87 (some (3,u0,u6)) (by decide +kernel),
  ternaryRule 95 79 16 74 5 r79x74x5x6 (some (3,u0,u6)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (2,u4,u6)) (by decide +kernel),
  ternaryRule 95 87 0 87 0 l87 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (3,u1,u2)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (0,u0,u1)) (by decide +kernel),
  ternaryRule 95 93 0 93 0 l93 (some (3,u0,u2)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (3,u1,u3)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (2,u1,u3)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 95 87 0 87 0 l87 (some (1,u1,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (2,u1,u6)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (1,u1,u6)) (by decide +kernel),
  ternaryRule 95 93 0 93 0 l93 (some (3,u3,u6)) (by decide +kernel),
  ternaryRule 95 31 0 31 0 l31 (some (2,u1,u3)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (0,u1,u6)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (3,u1,u6)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (0,u1,u6)) (by decide +kernel),
  ternaryRule 95 93 0 93 0 l93 (some (1,u2,u6)) (by decide +kernel),
  ternaryRule 95 87 0 87 0 l87 (some (3,u1,u6)) (by decide +kernel),
  ternaryRule 95 85 0 85 0 l85 (some (1,u4,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (2,u2,u3)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 95 87 0 87 0 l87 (some (3,u0,u2)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (0,u0,u3)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (3,u0,u3)) (by decide +kernel),
  ternaryRule 95 93 0 93 0 l93 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 95 87 0 87 0 l87 (some (1,u2,u6)) (by decide +kernel),
  ternaryRule 95 75 0 75 0 l75 none (by decide +kernel),
  ternaryRule 95 93 0 93 0 l93 (some (3,u2,u6)) (by decide +kernel),
  ternaryRule 95 87 0 87 0 l87 (some (3,u2,u6)) (by decide +kernel),
  ternaryRule 95 91 0 91 0 l91 (some (2,u4,u6)) (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (2,u3,u6)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (1,u3,u6)) (by decide +kernel),
  ternaryRule 95 93 0 93 0 l93 (some (1,u3,u6)) (by decide +kernel),
  ternaryRule 95 31 0 31 0 l31 (some (3,u1,u3)) (by decide +kernel),
  ternaryRule 95 85 8 21 64 r85x21x64x5 none (by decide +kernel),
  ternaryRule 95 79 0 79 0 l79 (some (0,u3,u6)) (by decide +kernel),
  ternaryRule 95 94 0 94 0 l94 (some (3,u3,u6)) (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x0 : Ex 95 7 [v175,u2,u0,u1,u3,u4,u6] :=
  certify c95 [] (unpack 6 0x291224080d120c89098340112102068c05830386401022400e1807060a10400f2081400e2204400d0881400c0a04400b0502400a244040094008050805894007070c400608904005099240040284400340020281 243 0x2955565a6696a965556845164f6683e86516664515675669e65515632e36646630a364b6652e55645650a554b5510913cb3d12d13e43c12cb6c96e42496cb6d90d98df8d96998c38d50d54c54d51554c30e10c34624618a144344b0c326080b8202430c11456c30df0c36c56d76d765e65779765b65379355b5536d355e55c6db45d45c75c45b4596195da5d96995d85d55154d64d55954d44d14113d23d14913d03cb38c24d30b04b24a2452070c60c50450c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x1 : Ex 95 8 [v51,u0,u1,u2,u3,u4,u6] :=
  certify c95 [⟨_,p95x0⟩] (unpack 6 0x291224080d120c89224006890706098303834017050821024016058309920589401503860305401440000284400f2081400e220408814013400c0a04400b05024012400a2440800040030281400240010a10 308 0x36838e3513513684a835138e4a72492111914a71a721125136524934e98e3659a534e24e48f0c309191148f90f0910c334b0c334e00e34b00b34e0c32220c30898c97228e22090c351d65d51151151d11d51165136166134e34e36136134e64e2092095066465096492062060a066050350352012008364351f61e6115d161d61d61149161d5dd34e5ce34b68b34e68e34b5cb21b5db60960961b71b2095c90836836005c06035c30806805195195185d751451651551311141110f48f11111110f40f34e30e34b34b34e34e34b30b2091c91062861091092061c6083043100140103103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x2 : Ex 95 6 [v176,u6,u0,u2,u1,u3] :=
  certify c95 [] (unpack 5 0x24890c892440070c0383218309832140068907062240068c0583050205890386050802810a1020c0208122040284088108900a04400d2102 171 0x6dce3e4fbce4ee3e9ce2649ace48e23a8ecad6e5bb34a5d6b56157c5d4b5596b3d0f6a50eb3d56b25095a508b2494a74dd29c9ca5194a3c4e6898ea50922229425288923ca5741cf83dc5734a55b16d631652a86a494aa2a92319ca7320c741cc529064114a42904310420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x3 : Ex 95 5 [v177,u1,u3,v35,u0,u6] :=
  certify c95 [] (unpack 5 0x68c03860890028409830a04088124082102244021400508038320812204050207060281 60 0x224897222e71e0e0380f5a48b72d6c5a02b59dab0300b51144491243a027300a00106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x4 : Ex 95 4 [v15,v178,v35,u0,u2] :=
  certify c95 [] (unpack 4 0x2204038308900386028102840a0421400983088105022081 40 0x70b774a776790101648675726225210224321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x5 : Ex 95 5 [v178,u1,u3,v35,u0,u2] :=
  certify c95 [⟨_,p95x4⟩] (unpack 5 0x68922040890068c038602840a040c8909830881050224080383028124408000214021022081 60 0x29245282252b4b0691ed689cd004012b0a96a52c491694894948409400e0114c51106208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x6 : Ex 95 5 [v179,u1,u3,v35,u0,u2] :=
  certify c95 [] (unpack 5 0x7060890038602840a04058309830881038305082140220402810502240821022081 60 0x20e042348f68d6369dcd230896a52c48d6949d49484093910419c66010a40800100c4000420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x7 : Ex 95 5 [v15,v115,v35,u0,u2,u6] :=
  certify c95 [⟨_,p95x4⟩] (unpack 5 0x220403830890038602840a0405832140098308818000050207060281050021022081 57 0x3040634bc600802360dcc2a8ac4b587080e358cec39d672a8e74a0e5018051906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x8 : Ex 95 5 [v180,u1,u3,u0,u2,u6] :=
  certify c95 [] (unpack 5 0x220407060890038602842408038324402140210220810a04028105020583050809830881 60 0x29e252aa053a0e82b4af6a86d6a5cd0340661d8741d07495654a869020e0298a00106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x9 : Ex 95 5 [v116,u1,u3,v35,u2,u6] :=
  certify c95 [] (unpack 5 0x22040689098308810a042408038324402140050803862081210202810890050205830284 60 0x21a2422a04714ce2348e7282e725ee039cd61986298a6491644a829400e0314c52008310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x10 : Ex 95 6 [v115,u1,u3,v35,u0,u2,u6] :=
  certify c95 [⟨_,p95x3⟩,⟨_,p95x5⟩,⟨_,p95x6⟩,⟨_,p95x7⟩,⟨_,p95x8⟩,⟨_,p95x9⟩] (unpack 5 0x220406890890068c0386401c800502840a040c890983400d80040881240821020383214024408003800280012081401b8000028105020508 77 0x22ec424e84561582a0b344e29455e94b568e615c2989d473a6e4c9ce545ce83dcd2b4ac2b0aa12c4a4a0e53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x11 : Ex 95 6 [v15,u1,u3,v35,u0,u2,u6] :=
  certify c95 [⟨_,p95x7⟩] (unpack 5 0x220407060890038602840a040583098308812408244003830281050205088000214021022081 77 0x6048c62c4c639cc00802671a0e2b0ae23dce7bdca081466994e529aa2b14a22d4a5ad450240808020218e62906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x12 : Ex 95 6 [v117,u1,u3,v35,u0,u2,u6] :=
  certify c95 [] (unpack 5 0x220406890890068c0a040c8909830881240805000508244021022081038302810386028405022140 77 0x434c8444886398e4112224404248c4c3998479182631ec4398c4b58c6b58b32cc731cc92148a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x13 : Ex 95 6 [v118,u1,u3,v35,u0,u2,u6] :=
  certify c95 [] (unpack 5 0x22040706089003860a04058309830c890881210203830500050221402408208106890281068c028424400508 77 0x4354844d08661984112624c1224484d619a4891a26b62d4c1ad43dad739a931ccc330c822c8a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x14 : Ex 95 5 [v181,u1,u6,v35,u0,u3] :=
  certify c95 [] (unpack 5 0x386089005830284240809830a040881244023060508038305020706208122040281 60 0x20982691c41044d69a0d0340f491c96a52a4b049499690280921888308e2300a00106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x15 : Ex 95 5 [v182,u1,u6,v35,u0,u2] :=
  certify c95 [] (unpack 5 0x70608902204038602840a0409830583088103830281208305082440050224082081 60 0x301c630a06330cf0380c611ac6092232cc86210b404084114840928218e6200a01104310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x16 : Ex 95 5 [v183,u1,u6,v35,u0,u2] :=
  certify c95 [] (unpack 5 0x2204089003860a040983088103832102070602810284058324082081050805022140 60 0x38e07398ef1a469309c63b4eb32d6d5a46b5898b584ab11d4748d2309d07098a108c8310420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x17 : Ex 95 5 [v184,u1,u6,u0,u2,u3] :=
  certify c95 [] (unpack 5 0x24080706089022040386028424400383218305080983050205830a040281210220810881 60 0x3062119a03185c3618a61b06f0b82c621ac03004320cb40d4340521400e0018a01906000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x18 : Ex 95 5 [v185,u1,u6,v35,u2,u3] :=
  certify c95 [] (unpack 5 0x70622042408098308810a04244003832183050803860583050202810890210220810284 60 0x285e12162420604694cd2308d6bc2d6a1cd035ac2a0ab4114440521400e0014c52008308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x19 : Ex 95 6 [v186,u1,u6,v35,u0,u2,u3] :=
  certify c95 [⟨_,p95x14⟩,⟨_,p95x15⟩,⟨_,p95x16⟩,⟨_,p95x17⟩,⟨_,p95x18⟩] (unpack 5 0x706089022040386401c8004058302840a0424080983400d8003088124400383050820812083800280010502401b8000028121022140 77 0x54c5222e8424e0532d0a298b29c267355e73b566d2d1a2909b36b64d8a5ad541ad7b9a55158a12c4a4a0e53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x20 : Ex 95 5 [v187,u1,u6,v35,u0,u2] :=
  certify c95 [] (unpack 5 0x220407060890038602840a0409830583088103830281210205082140050224402081 60 0x30206309e6330ce0140560dac6092232cc86210b4140840d4840928198e6280a01104310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x21 : Ex 95 5 [v23,u1,u6,v35,u0,u2] :=
  certify c95 [] (unpack 5 0x2306089003860a042183098308812408038302810284058320812102214005020508 60 0x38e07398ef30d83301c63b4ea3294d50d8a5016a504aa01d071a46009d07098a12106110420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x22 : Ex 95 6 [v17,u1,u6,v35,u0,u2,u3] :=
  certify c95 [⟨_,p95x20⟩,⟨_,p95x21⟩] (unpack 5 0x800180000706230608900386058302840a04218309830881208124400502038302812102214020830508 77 0x619cd431a64348841c4842948d338c46920d1ac6d13dad7bda9339246112d4a5891ad29129295292831cc2110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x23 : Ex 95 6 [v188,u1,u6,v35,u0,u2,u3] :=
  certify c95 [] (unpack 5 0x7060890220405830a0424082100214020810502244003830281038602840983088121020508 77 0x9535464c8c6540c44bd2621a2a82884594824bc4671844109c26a84258c494256b31ccc5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x24 : Ex 95 5 [v189,u1,u6,u0,u2,u3] :=
  certify c95 [] (unpack 4 0x7062204058308900386038305022440028102840a0421022081050821400881 60 0x938379f773e769d9767c343462b6929827a7434309807570600504300210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x25 : Ex 95 6 [v79,u1,u6,v35,u0,u2,u3] :=
  certify c95 [⟨_,p95x24⟩] (unpack 5 0x70623060890038605830a0421830983400d800008810383210021020508244005022a50028128d0028420812140 77 0x649cc4358844d482348c4112824c12244c4c34984891826322c4c18c43d8c73586418e822c8a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x26 : Ex 95 5 [v190,u3,u6,u0,u2,u1] :=
  certify c95 [] (unpack 5 0x3832140098322040706050803860281089002840a04248905020583210220810881 60 0x5a6091044122c8f581c0485a949189325203ad4749d28088223906401c06204a12006000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x27 : Ex 95 5 [v191,u3,u6,v35,u2,u1] :=
  certify c95 [] (unpack 5 0x3832140038622040706089005080983028108810a04248902840583050220812102 60 0x52208004011284f511c4405a8409882210b3a92741907380273886721ce6104a11106208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x28 : Ex 95 5 [v192,u3,u6,v35,u0,u1] :=
  certify c95 [] (unpack 5 0x2140038303860890050809830284210205830a040881260c05020706208122040281 60 0x4892223090601e0531ca12449511040280d33166518c7324463110601c06208a22006000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x29 : Ex 95 5 [v193,u3,u6,v35,u0,u2] :=
  certify c95 [] (unpack 5 0x22040706038308900386028102840a04058309830881208905080502214021022081 60 0x5820b58deb591cb5a96d0040150d035118a5a566518c93040630d06310e6180a020c6208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x30 : Ex 95 5 [v194,u3,u6,v35,u0,u2] :=
  certify c95 [] (unpack 5 0x2204070608900a040583098308812408038302810386028421022081050805022140 60 0x38e07385e7394ee19064285813b4ea2a94d5106a5058a5096a08d2311d07114c520c8308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x31 : Ex 95 6 [v195,u3,u6,v35,u0,u2,u1] :=
  certify c95 [⟨_,p95x26⟩,⟨_,p95x27⟩,⟨_,p95x28⟩,⟨_,p95x29⟩,⟨_,p95x30⟩] (unpack 5 0x38321408004800322040706401b800203860890401c800105080983028102840a0421020583400d8000088105022081208924082440 77 0xe669891a4647132ec5dcc1d98c2558ca4d8b7496c5b22348d2b2208b83d65734ac530ab2954548ca5220a5398a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x32 : Ex 95 5 [v196,u3,u6,v35,u0,u2] :=
  certify c95 [] (unpack 5 0x68908902204068c02840a0424400c89058908812408070c028121022081050205082140 60 0x28de52ae252b4b01bc6d6adcd6852d2b0a86a10c41c6842d484052838ce3094c520c0310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x33 : Ex 95 5 [v29,u3,u6,v35,u0,u2] :=
  certify c95 [] (unpack 5 0x2306070608900a042183058308810689028105890284208124082102214005080502 60 0x40e08401e84190e30d83301604350a3294d50d8a5016a504ea00c800a128098e62948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x34 : Ex 95 6 [v16,u3,u6,v35,u0,u2,u1] :=
  certify c95 [⟨_,p95x32⟩,⟨_,p95x33⟩] (unpack 5 0x383214080018000260c068903860890068c05080983028102840a0424890c89088120812408244020890502 77 0xc5554c1d194632936324a1c54a1414a8414963d2a4a9c919d29135296b52562caa428a92950519ca5118a5318a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x35 : Ex 95 6 [v197,u3,u6,v35,u0,u2,u1] :=
  certify c95 [] (unpack 5 0x38322040386089009830a0421022400244020810508214006890281068c02840c89088124080502 77 0x934ccd535484a506548c659cc44c48621a0a6a9a4594824bc4671844109c26a84258c4c5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x36 : Ex 95 5 [v198,u3,u6,u0,u2,u1] :=
  certify c95 [] (unpack 5 0x38307060386089022040583240805082140028102840a0421022081050224400881 60 0x49e0748d031244838d87389e7325c6398ed1b0663096210d4302500394e0300050106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x37 : Ex 95 6 [v103,u3,u6,v35,u0,u2,u1] :=
  certify c95 [⟨_,p95x36⟩] (unpack 5 0x383260c07060386089009830a0424890583400d80000881240024080502214005082a50028128d0028420812440 77 0x62588649cc8320e44d4844508234c44112424bc424390b34564811625ae0b4bd6b4396b6b16a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x38 : Ex 95 7 [v35,u0,u2,u1,u3,u6] :=
  certify c95 [⟨_,p95x2⟩,⟨_,p95x10⟩,⟨_,p95x11⟩,⟨_,p95x12⟩,⟨_,p95x13⟩,⟨_,p95x19⟩,⟨_,p95x22⟩,⟨_,p95x23⟩,⟨_,p95x25⟩,⟨_,p95x31⟩,⟨_,p95x34⟩,⟨_,p95x35⟩,⟨_,p95x37⟩] (unpack 6 0x800c800b800a240880098008800780068005800480038002800124402140070c03832a5022040689070628d0068c0386401c8000208121020c890583050205890983400d050802810a10401b02840881401a08900a04 240 0xaa730ca50750a2776799031094f20f9107108cf70f89021084c70c81d2087cc20c79d71c15a2081476c715a6da1472071581c71506501586581501c71561c714c5cc1565d614c1c749011048f54f49055048f10f48d10448c50c48d50d48c10c48b1044884c848b4d34881041470471461040871071460412500c324f24f25045024f0c324d0c324c38c24d38d24c0c324b0c324828824b28a2480c30870c71460000870070860c30840041410c30840c3081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x39 : Ex 95 5 [v199,v96,v200,u2,u1,u3] :=
  certify c95 [] (unpack 4 0x383070602800890401e244005020508214020c00281291202840a040881 54 0x8b988090878674e47b67706048d4c40140b0a28982762542432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x40 : Ex 95 6 [v96,v200,u6,u2,u1,u3,u4] :=
  certify c95 [⟨_,p95x39⟩] (unpack 5 0x8000401e0c890983038308900706028020800a040881244005020508214020c00281028422042081400c 75 0x283453d4a9a152520290a1e941d51520e831c9021c2609de63914b2110e210222358352d43425033986520c8308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x41 : Ex 95 5 [v199,v63,v200,u0,u1,u3] :=
  certify c95 [] (unpack 4 0x583038602800a104020050224400508214020c0028429120a0408810281 54 0x9b89918197967b67716149e947d4c12141b1a09800760500430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x42 : Ex 95 6 [v63,v200,u6,u0,u1,u3,u4] :=
  certify c95 [⟨_,p95x41⟩] (unpack 5 0x800040200c8909830a1005830386028022000a040881050224400508214020c00284220420810281400c 75 0x28545414a9a552524481260849d51524e931c4611e063a96a2112f490ee20862235815a8214a021398250848118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x43 : Ex 95 6 [v201,v200,u6,u0,u2,u1,u3] :=
  certify c95 [] (unpack 5 0x38307060a100583038620c02204089029120502244005082140028102840a04402220810881400c 72 0x509225252a5214741a66408e241ce832a46309a6895505150f298a6709a22b1615242141c26218250848118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x44 : Ex 95 6 [v199,v200,u0,u2,u1,u3] :=
  certify c95 [⟨_,p95x39⟩,⟨_,p95x41⟩] (unpack 5 0xc892440070c03832c18098321400689070680010a10068c058305020589038605080281224040238000089020c00a04028440222102291208814019400c 162 0x35188fbdd77a38c7d188ba2f77a288a388f5ce8ba3dc636e7378ddf36d7346e76b181e31a73b2e70b02ce30270acd6c6f1b5ed16b4b5a1dad1304761c4d6c8c68ce329ca268c0c673dd07bdc63350d618cd3358842d491184741c4811cc6100451904310400) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x45 : Ex 95 6 [v199,u6,v200,u0,u2,u1,u3] :=
  certify c95 [] (unpack 5 0x24400383214007060a10224005830502050803860281089020c00a040284400d0881400c29122081 72 0x64e6c64e6c60e6362d915a6495c62b5c62b58e234b2097a5ce4a4664958d6156a2a4a93a0a7394661946418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x46 : Ex 95 7 [v200,u6,u0,u2,u1,u3,u4] :=
  certify c95 [⟨_,p95x40⟩,⟨_,p95x42⟩,⟨_,p95x43⟩,⟨_,p95x44⟩,⟨_,p95x45⟩] (unpack 6 0x4022800480038002400d400c0d120c892489400b400a0d1809832440070c038321834003214040002a5006890706402180010a1028d008810a04068c058305020589038605080281224020c0208122040284401f80000890401d40192102 225 0x2e4d320122eb6c2134eaaeaa534ea4d3a41a673cf4e84e7a274cf4e63cf22122686120f2253cf92186586190f3e230c4e34e28e24cc4cf70f84c30f30f85c71f30c2e02df81f2cc2de30c21c21e71c20c21d30c6dc71d71c6cc3122cb4da4d26924cb2d82cb3d93d86583cb2c72cb20a20728720b2d75954c64d25124d44d218640618f44f41140f18f38618c34c38d34c1862c92ca1862c62ca2492062072472092071861440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x47 : Ex 95 5 [v199,v63,v50,v36,u1,u3] :=
  certify c95 [] (unpack 4 0x589058321030284050224400508214020c00a1029120a0408810281 57 0x9a899181979674d77a6a716149c9a5a4141b121a09800760500430210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x48 : Ex 95 6 [v63,v50,u6,v36,u1,u3,u4] :=
  certify c95 [⟨_,p95x47⟩] (unpack 5 0x80000c89098305890583028422040a040881050224400508214020c00a104015208102814001 78 0x1429296a5352a8a9224092d424ea82927498e479ce2308ed335445148972445111a5691815a8214a021398250848118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x49 : Ex 95 6 [v78,v50,v36,u1,u3,u4] :=
  certify c95 [] (unpack 6 0x402940220a040d120c89068c06890d1809832440400f0589038603832140050828d00881401940280583050208902106400e0a1020c040272103401521020284028140214001 180 0x8a080345189144380385144280286080244278d3517d179f79135174d34364375964334d70d3426427196423426934d16d169b6914d13543594d33533595146134c85c86175c84d35934c35035945034c35534c25025545024c244845049245245020838820d3cd38f38d20d0ca0c020c0c80c004b08a0852090880851c60800850c4083081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x50 : Ex 95 5 [v199,v78,v50,v36,u1,u3] :=
  certify c95 [] (unpack 5 0x244005890508214005830502089028140a10281120c02005402a028408810a040281 60 0x58e0b5820058a025b96d719ee70da3701a0709a232d8b1a869020071184500c041044300820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x51 : Ex 95 6 [v78,u6,v50,v36,u1,u3,u4] :=
  certify c95 [⟨_,p95x50⟩] (unpack 5 0x401980000a040c892440098305890508214028d00881058305020890400e20c020050a10401502840281400122042081 78 0x2ad691b7b35a3a8d6da35649ad739ad6398e0d935705be088c2047920f7c20378dae6a10b62c8a2092841c661946418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x52 : Ex 95 6 [v199,v50,v36,u2,u1,u3] :=
  certify c95 [⟨_,p95x47⟩] (unpack 5 0x68c0c892440070c0383400f0589038609832140050806890706402e0a10800002814028058305020890400e20c04019402221032102291208810a040284 171 0x796b0701ee700b5f56b1705de704b12eabe528ba2f95aea9476ddade9d47669446119c6114a5e9405417ad41405a9415456ad454149ce5cd729c96e7463003c037380e70cc30b9c230826089ce6210b6ad8d62d0b024034280800d23118464204811cc5100411904310400) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x53 : Ex 95 6 [v199,u6,v50,v36,u2,u1,u3] :=
  certify c95 [⟨_,p95x50⟩] (unpack 5 0x2440038305890508214007060a10402280000281058305020890402a400e281120c040190a040881028429122081 75 0x2c565aed65ac761ae6b94db56ccd49cc5214e529cc721b5716c04d6a5af735a3234cb62c4a1250631c661946418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x54 : Ex 95 7 [v50,u6,v36,u2,u1,u3,u4] :=
  certify c95 [⟨_,p95x48⟩,⟨_,p95x49⟩,⟨_,p95x51⟩,⟨_,p95x52⟩,⟨_,p95x53⟩] (unpack 6 0x402280048003402d0d120c892489068c0d1809832440070c0383402c05892183038621400508402b0a04068907060a10800280018000028128d00881402605830502208140192103400e089020c0028440214001401d40152102 234 0xb0f3cb28bb2ba8b3cfa586053cfa4f3c56059cc30fa0f9e89cf30f98c30b88b9a288b30b94c30588596288530c8da68f90f8e48cf68f31b32269a31a3226db81a6918518218116917da6867867de78669a75a68b6cb75b6cb68b71a6856c571b6c568561144f10f61960f45159144c5cc59758c4511015444512c42c45132d14454850d14454510c40cf18f29040f40f28618d18630e30d38d30630b20b28618b18b2882452050c61c51850c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x55 : Ex 95 5 [v199,v96,v78,v36,u1,u3] :=
  certify c95 [] (unpack 4 0x589058321060281244005020508214022400890291202840a040881 57 0x8a9a8090878674d77a6a706048c8a5a4040ba01a28982762522432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x56 : Ex 95 6 [v96,v78,u6,v36,u1,u3,u4] :=
  certify c95 [⟨_,p95x55⟩] (unpack 5 0x80000c89098305890583028120810a0408812440050205082140224008904001220402844030 78 0x1429294d5b50a8a9024a10d4b4ea82907418e479ce2308ed335445148872045111a56918152d4142501398250848118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x57 : Ex 95 6 [v199,v78,v36,u0,u1,u3] :=
  certify c95 [⟨_,p95x55⟩] (unpack 5 0x6890c892440400f038309832140068c058903860508402a08908000403202844028058305020a10400e224040194029210629120a0408810281 171 0x714a0681cd680a06d4a0e83bd682a0aacad4a4a92b56b66523d0f9a50f29625205818b581205e520d837b58320adad5554baad4d551ad94e549ce4d6c63003c036b40d00dc30b42228825089ad59cea6296c5a8ea020033a40700d030942539c27098a4100011844310400) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x58 : Ex 95 6 [v199,u6,v78,v36,u0,u1,u3] :=
  certify c95 [⟨_,p95x50⟩] (unpack 5 0x244005892140050803860890403280000284058305020a10402e400e28142240401908810a04028129122204 75 0x2c5512eb55ac9522e4b9c8d49485314a73948932356c5b6516c04d125af73483234cb62c4a1250631c862144418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x59 : Ex 95 7 [v78,u6,v36,u0,u1,u3,u4] :=
  certify c95 [⟨_,p95x56⟩,⟨_,p95x49⟩,⟨_,p95x51⟩,⟨_,p95x57⟩,⟨_,p95x58⟩] (unpack 6 0x80048003402d0d120c89260c06890d1809832440403123060383214040290a04068c058903860508089080028001800002842a500881402f05830502220440192106400e0a10224002814027401540012081 234 0x68e38a24a6a89ca38e98e38464499964438490b2ce94e92590e2ce8cb2ca7ca8df7ca2cb88b2c47c489f7c42c481554e84e82180e54e2db2df5552d52df6db7955455c57975c555575554a6ca75b6ca54a7155446c471b6c45443903990d939a39941031040b60b31830b40b5d04155955d65954100415034102832834d229040444409040440408308e14e24f3ce3ce24514c1452cd2cc34c2c52ca1ca24514a14a2472041c4085184144083081040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x60 : Ex 95 7 [v15,u1,u3,v36,u0,u2,u4,u6] :=
  certify c95 [⟨_,p95x11⟩] (unpack 5 0x291222040a1007060a0440350890038602848000403405834003403324080c89244003830281058905020508401821402102208109830881 98 0x2d8122d2520ba7293e1295292218860b82699dab33c0f335273a526218860902303c0ee7bdc7134470300b18862300203254932106398a41886208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x61 : Ex 95 4 [v202,v23,u1,v36,u4] :=
  certify c95 [] (unpack 4 0x2912058909830881089020c0214005020508208121020281 40 0x80b087860101389837a310104898476454432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x62 : Ex 95 4 [v153,v23,u1,u6,v36] :=
  certify c95 [] (unpack 4 0x5892408089020c020812140050805020383210229120281 40 0x9282090859b52a25503049847724644540300210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x63 : Ex 95 5 [v155,v23,u1,u6,v36,u4] :=
  certify c95 [⟨_,p95x61⟩,⟨_,p95x62⟩] (unpack 5 0x2912058924080983089020c020812140050208818001028021028000050803830281 57 0x7240e761d6c22c823b4e263c44710483b4e862d0a511094204800400398050106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x64 : Ex 95 6 [v23,u1,u6,v36,u0,u2,u4] :=
  certify c95 [⟨_,p95x21⟩,⟨_,p95x63⟩] (unpack 5 0x29120a1023060a048001089003868000403921830589240809830881038302810284058320812102214005020508 77 0x91d9274ccf538e874cd2639a5130da3302064bd2e68da30254901d07031801ac600a54909d07098a1094a12106110420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x65 : Ex 95 7 [v17,u1,u6,v36,u0,u2,u3,u4] :=
  certify c95 [⟨_,p95x22⟩,⟨_,p95x64⟩] (unpack 5 0x29120c898001401807060a1023060a044038089003860284800040370583218340362081098308812440050203830281400040032102214020830508 98 0x143ea94b5a90ae29034a368468cab18c8c9b061dcc639ccab2a5243d06956921b87214e529ce4a8aa0f43d0e1b86d211ac1296a42502118e61148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x66 : Ex 95 6 [v203,u1,u6,u0,u2,u3,u4] :=
  certify c95 [] (unpack 5 0x29120c89070622040a100a04058320c0038602840890098303830281058921400508400d0881400c2440050220812102 78 0xa1b9445b14411854592942aa941a2a65915ce1444a72a010040e3bdcd3958511c433a96a004013a507298a41886208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x67 : Ex 95 6 [v83,u1,u6,v36,u2,u3,u4] :=
  certify c95 [] (unpack 5 0x29120c8907060a10230628d005830983038320c005890a0408812440050202810890400120812102050821400284 81 0xa25948555482248752ce7450f3392475454d6a20820c83129ea4090911dc7135821906452d4002128380e53000520c8300820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x68 : Ex 95 6 [v85,u1,u6,v36,u0,u3,u4] :=
  certify c95 [] (unpack 5 0x29120c8908902183038602842a50058309832240058921020508214008810a04050224400a104015208122040281 81 0x85d90645506594c83a23133cd48ae6b8aa51044034410d699e60ac2b521c8328c55358a5856150120020e0018a02000300820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x69 : Ex 95 7 [v79,u1,u6,v36,u0,u2,u3,u4] :=
  certify c95 [⟨_,p95x66⟩,⟨_,p95x67⟩,⟨_,p95x68⟩,⟨_,p95x25⟩] (unpack 6 0x29120c8907060a1023060a04403b089003868003403a05832183098303830589210021020508401a402908812440050240018002028140158001028440198000400e20812140 98 0x35188d2cd84d2d130b20d74820b8087c845e20d74d1452d72c815c6c545644541a14d64d6172d72d645645035534b40b3102142104d34124503cd38d30b30b2882481c51851020c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x70 : Ex 95 4 [v202,v29,u3,v36,u4] :=
  certify c95 [] (unpack 4 0x2912058321020c890881089020c0214005080502208124080281 40 0x80c0878673b30a0a389830104898476453432010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x71 : Ex 95 4 [v153,v29,u3,u6,v36] :=
  certify c95 [] (unpack 4 0x583089020c0208124082140050205080689210229120281 40 0xa292a5b50a09527550304a948872654540300210) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x72 : Ex 95 5 [v155,v29,u3,u6,v36,u4] :=
  certify c95 [⟨_,p95x70⟩,⟨_,p95x71⟩] (unpack 5 0x291205830c89089020c0208124082140050808818001028021028000050206890281 57 0x7240e769d8d2308d13c423b8e2228483b8e86b10b5a8891204800400398050106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x73 : Ex 95 6 [v29,u3,u6,v36,u0,u2,u4] :=
  certify c95 [⟨_,p95x33⟩,⟨_,p95x72⟩] (unpack 5 0x29120a10230607060a04800108908000403e218305830c8908810689028102840589208124082102214005080502 77 0xa1d9485491540e88402685494741e3038da33818053d4e68da3601800296a00c800a96a0a12809cc7098c12948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x74 : Ex 95 7 [v16,u3,u6,v36,u0,u2,u1,u4] :=
  certify c95 [⟨_,p95x34⟩,⟨_,p95x73⟩] (unpack 5 0x2c180983038305892140800140250a10260c06890a04050803860281403d0890068c02848000403c2489400a400b403620810c8908812408244020890502 98 0x83f108529264e9271e467bdce63d4f539eb339e224a46f11da3115631ad624a11ad9c9b16c1ed1a9ad139ad739a46116a1a86912047420e6110a418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x75 : Ex 95 6 [v204,u3,u6,u0,u2,u1,u4] :=
  certify c95 [] (unpack 5 0x2c1809830383214007060a100a0405080386028120c02204028408900c89400d0881400c210220812408058324400502 78 0xe4b9e07b1e0eaba04a101005214a41c78b9c4639c09ba4789d6b83d6e5b9a46116b0080a01d27010643a0e62148310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x76 : Ex 95 6 [v107,u3,u6,v36,u2,u1,u4] :=
  certify c95 [] (unpack 5 0x2c180983038305890a10260c070628d020c005830c8924080a0408810508214002810890400121022081028424400502 81 0xa1dd49559493d4e97d1291a0604810752cf338e47382275414f1b06c781c0029aa00d8352d4212502388e5308451906210020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x77 : Ex 95 6 [v109,u3,u6,v36,u0,u1,u4] :=
  certify c95 [] (unpack 5 0x2c18098305892140050803860890248902842a50224005830c89240808810a040a10401520812204050224400281 81 0x81d91245512652521cc6290a7204c083a1ce945d070dee70962038054350c1a469609621214810d22020e0300050106000820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x78 : Ex 95 7 [v103,u3,u6,v36,u0,u2,u1,u4] :=
  certify c95 [⟨_,p95x75⟩,⟨_,p95x76⟩,⟨_,p95x77⟩,⟨_,p95x37⟩] (unpack 6 0x2c180983038305890a10260c07060a040386404008908003403f248905830c89240024080502401a402908812140050840018002028140158001028440198000400e20812440 98 0x35188d2cd84d2c88082df7cb2d130b40b40c20d6c878845d20841c20d6cd1452da14815960545514541440d5cd5954554544144103533524503cd38d30b30b2882481c51851020c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x79 : Ex 95 7 [v199,u6,v36,u0,u2,u1,u3] :=
  certify c95 [⟨_,p95x44⟩,⟨_,p95x45⟩,⟨_,p95x52⟩,⟨_,p95x53⟩,⟨_,p95x57⟩,⟨_,p95x58⟩] (unpack 6 0xc892440070c0383404440432c18098321400689070640040a1080058004068c05890386050802814024402a089080038002402e402d0a040284404205834041050280018000400e2912400d088140294019401a2081 222 0x90a286a69929a4628aa8a284a44aa9a442842a22a96182982a98a29d8617a179e89d761799862569a99a6a56181986248a21a28a46188d86048848e28846048175ca84a82180a5d77d17955d719519575c1975cf5d711510f40f1175cc38e29b28c6cc28e29a38e61961a65960e39755744e39555559551138e1911914d218e3843843d13c44043ce38c2cc28d28c34c28b2821c71821822481871840c40c5144144083081040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x80 : Ex 95 8 [v36,u0,u2,u1,u3,u4,u6] :=
  certify c95 [⟨_,p95x38⟩,⟨_,p95x46⟩,⟨_,p95x54⟩,⟨_,p95x59⟩,⟨_,p95x60⟩,⟨_,p95x65⟩,⟨_,p95x69⟩,⟨_,p95x74⟩,⟨_,p95x78⟩,⟨_,p95x79⟩] (unpack 6 0x800929128008800724080d120c89800680050d180983800424402140070c038340034000800322040689070640040a1080020a04068c058903864025050802814015028440244001089080012081400e210280000881401a400c4019400b05834018400a0502 308 0x1f12081cc1cc1f1cb11cc208c2e00008c98cbee9ae08c00c1ec0001c8b481ecb6c1c8008aca50a54c94ca8a94a54c50c1e85141c8a481e8a681c85080809405665149c05000a69653e35143d39133e39233d35131625145615d71625d75615143df4d33cc3cc3df81f3cc4d31d94d31c81c81d91d91c84d309d4d33c07803dd79d0804d33dc49b48c44c48a48a48c68c48a44a1c84481d91d91c81c81d94510834514806004836030804405574514945944975965544513d33d33d24513cf3cf3d03ce14c2cc14a14a14c34c14a2ca1c81881c51c91c81c81c7186083043140100143103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x81 : Ex 95 7 [v205,u2,u0,u3,u1,u4,u6] :=
  certify c95 [] (unpack 6 0x29120d1809830b12070c24080c8905890386068c4048404d220422400a1040282081400e2102400d0881400c0a044003050840002140404c0502404b0583404a070640060890400a0c9840040284400b40180281 243 0x2955565a6696a965555745764f6573d7651667451568567a2755154b3cf09144b45130f3e64516e56e69656d14642e464c6640a464b6632cb54c5630a354b5590d95de5d96995c35d50d54c54d51554c30e20c34614628614430cb0c326024b80b2430df1456c30de0c36c56dd6dd65c65d71d65b65371355b5536d355c5496db2cc2c93092db6d96195da5d96995d85d55154d64d55954d44d14113d23d14913d03cb38d24c34b30b24a2452070c60c51850c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x82 : Ex 95 8 [v60,u0,u3,u1,u2,u4,u6] :=
  certify c95 [⟨_,p95x81⟩] (unpack 6 0x2912224022040689800040010d180983070c038340034000214024080c8940490502028140480c980a10401605894047050805834015068c05034046400a028440282081400b400e210208814045400c0a04 308 0xa80c30870870a82280870c32265d75879c72269e65875d70805d70835030805000835d728a5d728f94f28696528f5d71a45145a35d71865d75a35144c44044477074c47044474070a14100838830a18a108340359f4104578174df81f59741728f71c29141028f41028a71c19e71c45d41019e41045d71c29b3db28728729b19b2873c709a3cf08308309a09a0833c32993983873473843843872073843440833430805400835430803405975573943543973575945544523523903903924d245035028f28f28e34d28a28c28b289187147184204187187184144083043080080083083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x83 : Ex 95 5 [v199,v96,u2,v50,u1,u3] :=
  certify c95 [] (unpack 4 0x383070602802440050220c0214005082912089002840a10224002810a040881 60 0xb6cbb0c0b8b9869882f2809001012be2d2262012abcba898765542321010) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x84 : Ex 95 6 [v96,u2,v50,u6,u1,u3,u4] :=
  certify c95 [⟨_,p95x83⟩] (unpack 5 0x80000c89098303832204070602800a0408812440050221400508210320c02081400c089002840a1022400281 81 0xd355ae6b5cb6d1ab330cb231696cdab4ad49328c92292904811035c002e000182078004735cd3ad8b3a549418e62906310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x85 : Ex 95 6 [v199,v200,u2,v50,u0,u1,u3] :=
  certify c95 [⟨_,p95x41⟩,⟨_,p95x83⟩] (unpack 5 0x2440038321400583058905080284224020c08001291205020706800028140a100a040281405408814051 71 0x26944a6944a4340a5e993e527bc731be527bc320b1314b1f07b86d1b1612048a090241a50338cc51848308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x86 : Ex 95 7 [v200,u2,v50,u0,u6,u1,u3,u4] :=
  certify c95 [⟨_,p95x42⟩,⟨_,p95x84⟩,⟨_,p95x85⟩] (unpack 5 0x8002402b40510c892440098303832140220440530583058905082103028420c08001400108810a0405020706208122408000028140210a10 92 0x4976942528d25393a709396e53dee73dee77a6c93bcf4796857d28f78aa27d28f9c9284a18789d8f83cac734441316a1250211cc21148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x87 : Ex 95 5 [v199,v78,v63,u0,u1,u3] :=
  certify c95 [] (unpack 5 0x5830386028022402440050221400508089020c0028429120a10028120810a040881 60 0x5918b581805a56a491494814032e0b325e6718c4004066ad8b52549418e6290630040110020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x88 : Ex 95 6 [v78,u6,v63,u0,u1,u3,u4] :=
  certify c95 [⟨_,p95x87⟩] (unpack 5 0x80000c89098305830386028008810a042440050221400508089020c00284210622402204400c0a1002812081 81 0xf255ef739ec7d1ec2358c1358a7cdec5316a22c8a12d4f73ce764987544e7220f039c4f73dc56358b52d493a0e62148310420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x89 : Ex 95 6 [v199,v63,u2,u0,u1,u3] :=
  certify c95 [⟨_,p95x41⟩] (unpack 5 0xc890b12070c0983068c05830589038640580e1807060a102440050221402c1805080890400e20c00284800040220281405621022912088140550a04 171 0x76101445d8c450141f08b5b06c22f7f1ad96e5cdee4d6e9ad13c5a7bc4d1612986618ce20985d296d9b7b59a949d4a925354a64a9092202802508094ce5285213a4e12800e014840900471447183a117460383dcf68daf1bdae6a86c4ad2a5a9234a0e6114401904310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x90 : Ex 95 6 [v199,u6,v63,u2,u0,u1,u3] :=
  certify c95 [⟨_,p95x87⟩] (unpack 5 0x70c0583038607062a1080000a102440050221400508089020c0028402812912402e405508810a042081 78 0x18d6b1826898a62d4ea294b5a942588ec9b0ea91d073b8e841c4111dcc8b1d07b822089ac6b16a5a92741cc52906208820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x91 : Ex 95 7 [v63,u2,u0,u6,u1,u3,u4] :=
  certify c95 [⟨_,p95x42⟩,⟨_,p95x88⟩,⟨_,p95x89⟩,⟨_,p95x90⟩] (unpack 6 0x40194022800380020d120c8924890d18098321830b12070c28d0068c058305890386405740200e18070680010a10400d0881400c0a04400b2440400a050240032140400005084056401d210220814055220440060890401f20c040040284800040210281 243 0x306592f12f0bee2d966c4d366d66cb6c65366b4d32d52eb5552d32e93cf66a669aa964f65345354f3d33d35514683cf2d12e84512cf2e73cf6e66e79a66cf3d90d95e55d99595c30e30c34e44e39234c34e20c33e13e28613c30cb0cb24524b14b2430c11456c30e00c36c56d77d765b6576d764165d6db4de4dd79d4db4c96c92c12c97092db2d96195da5d96995d85d55154d64d55954d44d14113d23d14913d03cb38b24d30b04b24a2452070c60c50450c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x92 : Ex 95 6 [v78,v63,v50,u0,u1,u3,u4] :=
  certify c95 [] (unpack 5 0xc890983058305890284220408810a042440050221400508400e20c02240210620810a100281 78 0x16c62d825b12c9312d52522508ec8b1274a0ed434e24098b62ca9824a779dc2088226882c5b1644a9283a0e53148310400) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x93 : Ex 95 6 [v199,v63,u2,v50,u0,u1,u3] :=
  certify c95 [⟨_,p95x41⟩,⟨_,p95x47⟩] (unpack 5 0x70c058305890284800107062a1080000a102440050221400508400e20c0402e2912028108810a04 74 0x12a52521505274a0e841ceb99ce1404a9924a789e055bd61004010040b4b92d62c01005495250741ca62906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x94 : Ex 95 7 [v63,u2,v50,u0,u6,u1,u3,u4] :=
  certify c95 [⟨_,p95x42⟩,⟨_,p95x92⟩,⟨_,p95x48⟩,⟨_,p95x93⟩] (unpack 5 0x80030c890983070c2204058305892103028480020706800180000a1008810a04244005022140050840152081400e20c0402140010281 98 0x185d316c62d2ccb1255152a524ecc31274a0e5414e841cedb9ecc5b1634d5233d0e51ce436c5ab62d8d4c12d2bca27358b62d495250741ca62886418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x95 : Ex 95 6 [v96,v78,u2,v50,u1,u3,u4] :=
  certify c95 [] (unpack 5 0xc890983070c2081070602810a0408812440050221400508220408900284400e224020c02103 78 0x18b5b16f62d2b92d265252f53ceb8ad274a0e6418e281cef43de67958b62c49724c5315ac5b1614a9213a0e62908118820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x96 : Ex 95 7 [v78,u2,v50,u0,u1,u3,u4] :=
  certify c95 [⟨_,p95x92⟩,⟨_,p95x95⟩,⟨_,p95x49⟩] (unpack 6 0x405940540d120c89260c24890d18098324402306070c2183214028d00583400f05890508401f02848002800120c0402721034015210220812a500a040881402807060502800022402204400121064021400e0281 234 0xa4c3052cba4b2c530ca0b2ce30ea0c30e2cb98820b9cb9a798b20b94820584596184520890820e84e92184e20e89860b8cb8a388b60b21d22161821822175d81860574581d7456050986067c669f7c661879860e74e79d74e60e2d32cc70c2dc2cc4cc6d34c84886ca6c84c86534d849865a6584d85c15824d31821920951934ce50e4134ce4ce41244e10e4053ce14e08410c18c2cd2cc34c2c62c91862022092892062051c51061851851020c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x97 : Ex 95 6 [v199,v78,u2,v50,u0,u1,u3] :=
  certify c95 [⟨_,p95x87⟩,⟨_,p95x83⟩,⟨_,p95x50⟩] (unpack 5 0x2440070c214005830589050802848002800120c0281129124022402a07060502800022402814028120810a040881 78 0xf6b1cf6b1ce0b00f13d234a4625ac634a4620a01a799db19460d2bdae6b5800802b5a920080253a0e6294830802010020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x98 : Ex 95 7 [v78,u2,u6,v50,u0,u1,u3,u4] :=
  certify c95 [⟨_,p95x88⟩,⟨_,p95x84⟩,⟨_,p95x51⟩,⟨_,p95x97⟩] (unpack 5 0x401980030c8924400983070c2140058305890508028440278002800120c04015401d220420810a0408810706050280004001400e224040210281 98 0x1284251cda1094a0c8d20d9c98d9c98d9c9a68c20d335a76b4e76b4e62bce76b4d09425c6a99d3a4e43745c2839ee7348c0916a4a128118e62884418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x99 : Ex 95 7 [v95,u2,v50,u0,u1,u3,u4] :=
  certify c95 [] (unpack 6 0x405b0d120c89260c0d1809832306070c038328d040280583400f0589401f02840a04068907062204028140010a104054402b088124892440050221832140050820c02081405740152103401d405a2102400e40212240 225 0x2a69a5d146a4515da6a838e469468a6844e46738e5cf5e73cf5ce3a52cb4664659a544b44e30e3cb2ce2ce3cc3242cb5cc5e430c5cb5e22cb5a35a28e258b5912916a169185168a69f28a38839f81f38a39d28a2c82dd79d2ca2dc09b58a59405458159429469659151169469159661658e64e61960e5965d45d55965d65955140892510910934912513c924e40e3d03ce24930924b34b30d30b2492872822492892481c61440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x100 : Ex 95 7 [v199,v50,u0,u1,u2,u3] :=
  certify c95 [⟨_,p95x52⟩,⟨_,p95x44⟩,⟨_,p95x85⟩,⟨_,p95x89⟩,⟨_,p95x93⟩] (unpack 6 0xc890689070680048003800280012440070c0383402240362c18405409832140402805830502800002810a10400f05890508404e400e0284402b20c0402e2102291208814051400c0a04 228 0x51849264475d51875d6444925244925c37435e475d2034836624105128d25228e26924108603cf6844107de4106843cf6804105c33c35c03c068341039255251d30c39231265d55539b30c65071039b71b69031038430c65855538455565830c39630c5c35435d65552033031931c71921921935131921d21901d018f18f19045018f1cf18d1c718c18c18d38d18c1cc18b2891832031801c00831c3180180083043180105083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x101 : Ex 95 7 [v199,u6,v50,u0,u1,u2,u3] :=
  certify c95 [⟨_,p95x53⟩,⟨_,p95x97⟩,⟨_,p95x45⟩,⟨_,p95x90⟩] (unpack 6 0x404240410c890689070680038002402a4022800122402440070c03834044404309832140402805830502800002810a10400f05890508404e0284400e2811402b20c00881400c0a044052402e291240512081 222 0xa1452775da1d7675142d451675d59d74b51499450774799d7475079124949549259144928d14614928924a14512d24a079e7de78b49215248744715114749251751d38e50e51d5d76ce3927126dc6d239268e3995d76975d938e2ce3905d74175cb38e60e3875c76175c73875482140d45565542144884910d14934912113c820e0ce3d03ce20e34b3032cb0c82030ca1c91c52051c81c50c51c61c51051c11c5185103081040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x102 : Ex 95 8 [v50,u0,u6,u1,u2,u3,u4] :=
  certify c95 [⟨_,p95x54⟩,⟨_,p95x46⟩,⟨_,p95x86⟩,⟨_,p95x91⟩,⟨_,p95x94⟩,⟨_,p95x96⟩,⟨_,p95x98⟩,⟨_,p95x99⟩,⟨_,p95x100⟩,⟨_,p95x101⟩] (unpack 6 0x80098008400c0d120c892489400b400a068907068007800680052240800480038002800140010d1809832440070c038321834003214040004052210228d0088140510a0440280583405005028000028140210a10400f0589404f0508208120c021034015404e400e0284 308 0x514555506506514d335065555144d35325555145555324d35303cf515c55530c705153d506f3cf4067c64af7df4063c64ae3cf42d7df4ae7df42d3cf51334d5152d55132d351534d42b34d30fb0f4abb2b40f34d06a34d3069c6a689e730634d9a52cb32234d92334d3222cb5201c75158555208605151d540f68f21f1c728f1cf41f69a31d1c720d78d29d79d30d1cd05c1c720668629c69a2061c629b1c721969a29b69a2191c70d80d75151555135935155955131534111450cf0cf0d149140f14f30d14d0cb0cb0cd38d30b14b2091450c70c70c92892071470c60460c31450c30c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x103 : Ex 95 6 [v199,v206,u2,u0,u1,u3] :=
  certify c95 [] (unpack 5 0xc89400f070c09832140068c0583058903860508403240220890028440280706400e0281224040232c1824400502210229120a0440600881 171 0x6ca50181b31805016e534a45914d7bea524e53ace53290e523dee3bdcf29625205c18bdc12055ce2d8b5b54ae2d1ce94e549ce4e721ef4b9d17392f7a1ef1b9d07386f781c013c407804e731292b4ac6b0a92ad6a12040480491010030cc5394c731465104801804310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x104 : Ex 95 7 [v206,u2,u0,u6,u1,u3,u4] :=
  certify c95 [⟨_,p95x103⟩] (unpack 6 0x402380000d120c8924890d1809832183400f070c400321404000068c05830589038605084027400440210284400608902a50402807062240400e0281400d0a04400c0881400b2440400a050240302102405f405e2204401f2081 243 0x102cb01002c42b00b2e91c72ea2e9aa92c72e81c70090282490070266db2e72e69e62db2c784725b6c76c72618656db02102586101b0016db4634648e345b6e26db82186286181b6cb5cb35534b54b3575de5d71df1de7de1d71dd5d76dc6dd71c6d75c05c009a0804000975c15554575da5d74555415556575d85d759554d44d2d42cd50d2d12d24511c11d24d21d11c240201100244200100140f34c34b38b34e34b30b24824728724a247207086140100083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x105 : Ex 95 7 [v207,u0,u6,u1,u2,u3] :=
  certify c95 [] (unpack 6 0x24890c89068907064028402922402440070c0383400f2183400e09832140400d068c0583050202810a1005890386050828d008900a040284402e400c2912404e20810881 240 0x5613cf54168156169a5413c14a03cf4806804a069a4803c075e38e74f7cf75e7de74f38e55538e5416c155c6db54138e48738e48034048734748038e5cf4cf5da28a5cf28f5da4d35d828a5ce64e5d86585ce28e55628a5414c15564d354128149428a4804c04944d348028015018614f44f15045014f18f14e20e14d18614e18e14d20814c18614a2ca14c2cb14a186081181143243141241143186080180087207140200087186143000081101083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x106 : Ex 95 7 [v78,u2,v61,u0,u1,u3,u4] :=
  certify c95 [] (unpack 6 0x40620d120c8924890d180983400f070c2183068c0583058903864027028420814015089040594029260c2440230621400508402120c02204400121064053403021022a500a0408814028070622400502401f400e0281 225 0x2a1c76c86ea2086c71e80c31e91e8a681c31e70c36d56e75556c36e54921e61e59a51d21c34c35524834835534c24921231248e31124a24926d36e24d36d26c770721920764721c72071c0e10e08600dc0df71c49e49f79e49c70265911c71d71c11965b65b69c71b71b6996413cf1c11c16171cf1d53cf0d60d55950cf0d33cf49449351348f3c145010e1013cf10f3c238d30b2881081c91c82481c41c51040c20c51850c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x107 : Ex 95 7 [v199,v61,u0,u1,u2,u3] :=
  certify c95 [⟨_,p95x103⟩] (unpack 6 0xc890689070640284023070c038340620983400f068c05830a1005890386404e089008810a04028424400502800022400281291221402c180508402e405120c0400e4063405c2102 216 0x82338e7123d27233cf8123928212cb80e88e8218a180e2cb7d12cb7125d27115d17d22cb68e24e68f1c768e1ce68f24969d1c768b78b69d79d68b1cb69b1c771225271b2496921d219841018e64e19865818e40e18b4cb19741018b40b1974d31964101875471965551874105124121914d11924d21914100cf28f0ce20e0cf20f0ce28e0cc28c0cb0cb0cc34c0cb28b0c92090c72870c92890c72071831440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x108 : Ex 95 8 [v61,u0,u6,u1,u2,u3,u4] :=
  certify c95 [⟨_,p95x104⟩,⟨_,p95x105⟩,⟨_,p95x106⟩,⟨_,p95x107⟩] (unpack 6 0x80030d120c89248940280689070680020d180983400f070c038321830a04068c05830a100890058903862080208102848001404e400c0881400b24404061400a050280002240401f4001028140032140405d40000508405c21024015400e405120c0 308 0x5d75555da5da5d70b05da5555ee4105d5bd55eebee5d54150ad41049a4da0ad4d349a41a5e22cb5d57d55e27e25d52cb4aa2cb350ad0b2aaea4902cb0822cb35a39a0a938e35a2cb5e71865d5a155e7a275d519549025021318699019049324936418620b94b9a496434b18b0a318621a25a0a324921a19a5d56555e27a25d57955e26594a06590d08500e086049065034b78b0df6590cb64b35f79e21d6590c67060dd71c2066590c30db0da09a0c36595d75965d55d55c25d85d559549345309009009351349045034e30e08b08b08e3ce34b30b2091c90860860892892061c60c31440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x109 : Ex 95 7 [v208,u0,u1,u2,u3,u4,u6] :=
  certify c95 [] (unpack 6 0x291224080d120c892204068907060983038320c00c98058340690890400f2102400e2081400d0a04400c0881400b0502400a244040060a1040050b1240240281406805084001070c40140589400340020284 243 0x284d35da5e86a85d34e74515cf5e73e75d15e54514e64e59a54d14e42495cc5e46a45c92552494cb4d52d54c92622494634628e24492590d95dc5d90995c35e10e14dc4e10a14c34d10913c33d10d13dc3e00e02452601602432576d765f6577d765b6537d355b5536d355f55d6db45e45d79d45b4496c92cc2c93092db6c36db15c14370315b6d96195da5d96995d85d55154d64d55954d44d14113d23d14913d03cb38d24c24b30b24a2452070c61c51850c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x110 : Ex 95 8 [v77,u1,u2,u0,u3,u4,u6] :=
  certify c95 [⟨_,p95x109⟩] (unpack 6 0x291224080d120c8920c0068c058303868000028440674015089022040b124016070640070281098303834000070c0283406640010508400f2102400e20810a044065400c0881400b400305024064400a2440 308 0x22818620a20a22836820a1863670c308a00a36702708a0ca2250c32069862259a52060c634a7ca78c90c34a90a78c7cc2067c62097092067062097df0a27df7838c36628e20837c33d471c3da7df3d47df3da71c4d37df4d28614c48614d27df12071c79d7df1047df79d71c3db51b3ca3ca3db35b3ca50a2095092066862096892065060985143c33c33d86580835033d74d64cc48c4ca4ca4cc10c4ca48a2154952062062152152064860830834c04804c34830800803d43d43d34923cf3d13d03ce10c2cc10a34a10c10c10a2ca2091c92062062092092061c6083043100140103103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x111 : Ex 95 8 [v15,u1,u3,u0,u2,u4,u6] :=
  certify c95 [⟨_,p95x60⟩] (unpack 6 0x291222402204068907064001400f20c00a0480000a100890068c058305890386406c40150284400b24080d120c89406b24400d18070c038340350281050240000508406a400a2140403321024003400e208109834034400c0881 308 0xac0000840840ac9ac0840009aa3cf404ac49aaaea4043cf0a43cf0808800a48a40803cf2a83cf28ea4e2a8a6828e3cf1883cf4274511864514273cf9846847079479849447076870806800a48640808400a469a40f84f72269a8cf68f42286129f69a28e80e29f81f28e68e35e69a34c74c35e75d34c69a18869a71b75d18675d71b69a29838e28428429865828438409638e0805c00965d608038029535434730734434434718734430408330c0804c00834c308030041130c34f48f35149140f30f28e28e28d30c28a28a28b289187147184204187187184144083043080080083083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x112 : Ex 95 5 [v202,u0,u2,v23,u1,u4] :=
  certify c95 [⟨_,p95x61⟩] (unpack 5 0x2912070c240809832140208105020281224008810a04058905080a1080000890028420c02102 60 0x48249325e93162604006625e9731866154c60c2c6b40c425095ad404a128198e61948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x113 : Ex 95 5 [v153,u0,u2,v23,u1,u6] :=
  certify c95 [⟨_,p95x62⟩] (unpack 5 0x2408070c20812140050209832240028120c0058905080a108000089002840a04210229120881 60 0x1484841e28401a08404e7b9c871d8e7154e701a0389825ac60289422a12829cc50100300820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x114 : Ex 95 6 [v155,u0,u2,v23,u1,u6,u4] :=
  certify c95 [⟨_,p95x112⟩,⟨_,p95x113⟩,⟨_,p95x63⟩] (unpack 5 0x29122408070c098320812140400b4016050222400a0420c0058908900a10800240398001088140718000210240704003050802810284 77 0x82e90245d05c94426605245d16b165594852646526be52a4e504410c2c4a88220d2bcad1384d62d484a0e53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x115 : Ex 95 6 [v37,u0,u2,v23,u1,u6,u4] :=
  certify c95 [] (unpack 5 0x29122408070c0983208121400583050222400386028002840a1008810a04218321020589050802810890 77 0x7250e23c4e4990424484d3c4f0811af6b44d431ad4b9ad739a6398e82308731d292148912d2a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x116 : Ex 95 6 [v156,u0,u2,v23,u1,u6,u4] :=
  certify c95 [] (unpack 5 0x2912240809832081214003830706050220c005890280028108900a04088123062102070c05080a100284 77 0x6250c2348c4990424bd2d348d1891b06b44d4bd2d431ad739a931d2921526398e82308812c4a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x117 : Ex 95 6 [v39,u0,u4,v23,u1,u6,u2] :=
  certify c95 [] (unpack 5 0x383240822402081214009830583050229120a040a10028105890508088108902841028421832102 77 0x8045082a5114222644d00900c62b8a639ccc445108018f630cc2b8ac2358c6b58502caa4250420020218e62906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x118 : Ex 95 6 [v40,u0,u4,v23,u1,u6,u2] :=
  certify c95 [] (unpack 5 0x38324082240208121400b062912088008900a0402810a1021832102058905080583050208810284 77 0x934529429244cd2691884539424c5308184f108825384258c4a334c94256b31ccb2148c5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x119 : Ex 95 6 [v41,u2,u4,v23,u1,u6,u0] :=
  certify c95 [] (unpack 5 0x38608902408070c028420c02081214005080b0607060502291208810a040a102844028123062102 77 0xf0380f5cdef2c9f27be4e7bdc08816b2a8ab2416b841687b90d6810c421682a908225084a50501c06200202906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x120 : Ex 95 6 [v164,u2,u4,v23,u1,u6,u0] :=
  certify c95 [] (unpack 5 0x386240820c020812140098329120a000a1008810284089023062102070c0508070605020a040281 77 0x9344c924d2a429284a5069188453944594824c4508184f108825394258c4a3354b31ccc5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x121 : Ex 95 7 [v23,u1,u6,u0,u2,u4] :=
  certify c95 [⟨_,p95x114⟩,⟨_,p95x64⟩,⟨_,p95x115⟩,⟨_,p95x116⟩,⟨_,p95x117⟩,⟨_,p95x118⟩,⟨_,p95x119⟩,⟨_,p95x120⟩] (unpack 6 0x29128007800623068005800440390a0480038002800180000a100890400f21834071058903860d18070c03830d1209830881070622400281058320c0400b0284208121022408406d21400502407024400508 240 0x6284108876876a86a86074108a134d9d07109a172189034d62534d6873876a538e60734d8902509216e18d06d08a124980d6cd7dc24978d24d75c6db6192496872c76992cb60724709724908058009759608024909100009055009155109001009300008d50d09351308d00d0870070861060871070860002910c32904902914912900d028e0c328d3cd28e3ce28d0cd28b0c328930928b30b2890c31470c80860480870470860c31440440800c30840c3080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x122 : Ex 95 8 [v17,u1,u6,u0,u2,u3,u4] :=
  certify c95 [⟨_,p95x65⟩,⟨_,p95x121⟩] (unpack 6 0x2912400c0d120c89400b8001400a068907062306224040010a044016068c058380000a100890400f21830386403620c0406f40150284406e208129500983403708810502406d244040030383403802812102214020834000403a400e0508 308 0x3ee38e3c63c63ee6ee3c638e3cf38e3ed4103cf4103ed38e3eb34d3ceb0e3ebb2b3ce34e05b34d3062c66e12cb30634d2aa2a932834d28a34d3282a83e21c73ce74e3e27623ce1c73261c720d9cd8669e630d1c70651c72069066e59242061c72981c722392428a9242231c73ce50e3e27223ce70e3e251431f51458d80d85f81f30d50d20770759d51478750721d71c05a5145865c66da5d75865060c35140c56450ca6590c55142985145955d728a5d75955140d30d23d01453ce44e3d04503ce14e30d14d0cb0cb0cd28d30b1452091450c70c70c92892071470c60460c31450c30c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x123 : Ex 95 6 [v82,u2,u0,u1,u6,u3,u4] :=
  certify c95 [] (unpack 5 0x29120c890983070c058303860a100706220408810a042440050220812102058921400508089020c002840281 81 0xc45589651894290464d892254741d047c88c5b0214c5283a0e124022085eb62d8f4b92d4350c5b16a4a9283a0e62148308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x124 : Ex 95 7 [v83,u0,u1,u6,u2,u3,u4] :=
  certify c95 [⟨_,p95x66⟩,⟨_,p95x123⟩,⟨_,p95x67⟩] (unpack 6 0x29120d120c89248906890706230622400d1809834003070c038328d0401605838002407320c0405d400e0284400d0881400c0a04400b2440400a050280018000028140010a104052405120814000210240140589404f214040680508 243 0x2d59621922d66d2165ab4105ac5abb2b5905aa41021222a49221021434d58b5942d458d36834d429428a6840d36734d2262279a620d3640005a55a49645805908d04800100104834a10003623618a13403460062032066462002166d652051681651b51e6db41c41e7de41b40d6cd2dc2cd74d2db2c864819b1886c819c1846db0030040c401b01a6585955945d45975945544914904d049349045034c34b3cb34e34b30b2072062862092061c61051000c0103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x125 : Ex 95 6 [v84,u0,u2,u1,u6,u3,u4] :=
  certify c95 [] (unpack 5 0x29120c8909830383070605832102058908900a0408812440050222042081070c214005080a10224002810284 81 0xb3d5695d1693a8e45cd692254f3bce40c8215b0214c4213a02b62d8d4c12779ded23881105ac5b16a4a9283a0e62148308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x126 : Ex 95 7 [v85,u2,u1,u6,u0,u3,u4] :=
  certify c95 [⟨_,p95x66⟩,⟨_,p95x125⟩,⟨_,p95x68⟩] (unpack 6 0x29120d120c89260c068c0583218320c0058903868002800180000284401508900d1809834003407540074038070c2140400905082a50401607062240400e0281400d0a04400c0881400b2440400a05024074405f2081405e2204403b2102 243 0x2e2cb01002e42e00b2ec1c72ed2ecb6c2c72eb1c700902b2490071cb84b35f34b7cb3618698611ea1e9aa91e11e88610270289e70210268615655669655618417df46186486145f7e37df82186286181f7dd5552de2dd79d2d52c770725554754725b24054009b08040009508155545845b61845554155569861961759554d44d2d42cd50d2d12d24511c11d24d21d11c240201100244200100140f34c34b38b34e34b30b24824728724a247207086100144083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x127 : Ex 95 7 [v209,u1,u6,u0,u2,u3] :=
  certify c95 [] (unpack 6 0xc8906890706230622404016068c0583407740290a10218320c0400e058903860890400d0a04028405022440070c0383028129502c1809830d182140050840432081400c2912403a21020881 240 0x60b45160140160b41060145152545150040052541050044076334d81191182392375134d62234d60184162286160134d51334d5006c05136d350034d75e4928117d181e7de75149170d54d71b49270d48d71b55561a49260164161a6596014811974921875871975961874925004805135535005405134921913111901c71911d119031018e1c718d3cd18e3ce18d1cd0811c118b30b18130118b1c708a1c708024018a2480801c0183000081105083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x128 : Ex 95 8 [v79,u1,u6,u0,u2,u3,u4] :=
  certify c95 [⟨_,p95x124⟩,⟨_,p95x126⟩,⟨_,p95x127⟩,⟨_,p95x69⟩] (unpack 6 0x29120d120c890689070623060a044016068c058380030a1008902183058903860d180983070c03832100210205088002403a400c0881400b24404076400a050280012240403b40010281800020c0407340150284407220814000400e40372140 308 0x5ef5555da5da5ef0af5da5555ed4105d5b955edbad5d541508241049a4da0a84d349a4105e92cb5d59155e99295d52cb4ab2cb350b10a2bb2b4902cb0aa2cb35a39a0aa38e35a2cb5d51955e98e95d58d55e91864a61862109d0a269e649019034b8cb22418694b18b3648e30a218621a25a0a224921a19a0e11860d98190e18200d91865de6595d57d55de7de5d56554904900d36590d065049349335c6590cb74b0dc75c34b64b0c30db0da09a0c36595d75965d55d55c25d85d559549345309009009351349045034e30e08b08b08e3ce34b30b2091c90860860892892061c60c31440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x129 : Ex 95 7 [v210,u0,u2,u3,u1,u4,u6] :=
  certify c95 [] (unpack 6 0x29120d180983070c038324080c890689210220c009920589407d089040282204400e2081400d0a04400c08814003050840002140407c0502407b07064046058340060a10400a0e1840240281400b40180284 243 0x284d35da5e86a85d34e04605cf5e03e05d15e64514e74e69e64d14c93cf09144945130f3e44510e50e49640d10e32635cc5e30a35c95e22494cc4e20a24c94d90c35dc5d96995c30d50c34c54d51554c30cb0c326124b84b2430d76d781f8177d781b8137d355b5536d355f55d6db45e45d79d45b4496db2cc2c93092db6c36c315c14370315b6d96195da5d96995d85d55154d64d55954d44d14113d23d14913d03cb38d24c34b30b24a2452070c60c51850c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x130 : Ex 95 8 [v94,u2,u3,u0,u1,u4,u6] :=
  certify c95 [⟨_,p95x129⟩] (unpack 6 0x29120d180983070c40034000214020c02102401605890386407e0508068c80000284407a4015089024080c89407905020e180706400106890485404a400a028140282204400b400e20810a044078400c0881 308 0xa80000840840a82280840007e06e07048847e08a07046c40a66db0809c00a69e60806c028f8a229c6db28f6db28a8a238e6db38d94d39f96538d6db1a48a27236db1a46db7238a22046045e08602048445e062008060008354308054008361871e6185db75b7de75d71b61828a61828f68f28669a28f61838d55539061838d6183905551995555d66181866185d65552943d42842842941942843c40933cf0800800930930803c029239138734738438438720738434408334308040008340308034028f28f28e34d28a28c28b289187147184204187187184144083043080080083083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x131 : Ex 95 6 [v199,v200,u0,v78,u2,u1,u3] :=
  certify c95 [⟨_,p95x39⟩,⟨_,p95x87⟩] (unpack 5 0x2440070c2140224007060281800129122081058305020508038620c08000281108900a04028440590881405e 71 0x2eb55aeb55ac350ad4b9aa5452a7352a73528330c9715c1e40902e684811ad8b1a92340c6838cc50902308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x132 : Ex 95 7 [v200,u0,v78,u2,u6,u1,u3,u4] :=
  certify c95 [⟨_,p95x40⟩,⟨_,p95x88⟩,⟨_,p95x131⟩] (unpack 5 0x80024029405e0c8924400983070c2140208107062240210602818001401d0a0408810583050205080386220420c08000028440270890 92 0x5174a52d6aca95842aea416c845ac845ac83aaaa41d13396653c2873ce673ce679316a5aa088a0b07b9ac52d421212811cc2114822084418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x133 : Ex 95 6 [v199,v96,u0,u2,u1,u3] :=
  certify c95 [⟨_,p95x39⟩] (unpack 5 0xc89070c03830983068907060c98058309920589089040232440050221402c1805080a10400e22400281800040220284405c210229120a04404e0881 171 0x76100441d8c410041f08b5b06c22f7edad4f13be6d2d4e9ad03c1a7bc0d0612986618ce2094892902802508094da7385e16bda13852736d5b4ad1b36a66954949925539824014c40980521447183a117460383dcf68daf1bdae6a86c4ad2a5a9234a0e6114801804310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x134 : Ex 95 6 [v199,u6,v96,u0,u2,u1,u3] :=
  certify c95 [⟨_,p95x83⟩] (unpack 5 0x38307060583058928908000089024400502214005080a102240028102842912402a404e0a0408812081 78 0x18d6b1816858a62d47a1d4b5a941584ec99ce841ce111dcc931ca8a8e83b9d07b822089ac6b16a5a92741cc52906208820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x135 : Ex 95 7 [v96,u0,u2,u6,u1,u3,u4] :=
  certify c95 [⟨_,p95x40⟩,⟨_,p95x84⟩,⟨_,p95x133⟩,⟨_,p95x134⟩] (unpack 6 0x40194023800380020d120c8924890d1809832183070c03832a5006890706401e0c98058309920589402780010890400d0a04400c0881400b2440400a05024003214040000508405c210240012204404e208140060a10401f224040240281800040210284 243 0x305d7271270bee2575ec4d35ed5ecb6c5d35eb4d325526b5552532693cf5ea5e9aa95cf5d345354f3d33d35514683cf25126845124f2663cf0e70e69e60cf0d90c35e55d99595c30e30c34e44e39234c30cb0c324524b14b2430d789765b6576d765d6606db4e14e08604db4de6db3df3de7de3db3c96c92dd2c97092db2c36c314614318315b6d96195da5d96995d85d55154d64d55954d44d14113d23d14913d03cb38d24c24b30b24a2452070c60c51850c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x136 : Ex 95 6 [v199,v96,u0,v78,u2,u1,u3] :=
  certify c95 [⟨_,p95x39⟩,⟨_,p95x55⟩] (unpack 5 0x70c0706028120810583058980012890800008902440050221400508400e2240402a291202840a040881 74 0x12a52520501274a0e5a1ce841ce0400a99a641004110040b4c12b3bceb2b96d62c01005495250741ca62906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x137 : Ex 95 7 [v96,u0,v78,u2,u6,u1,u3,u4] :=
  certify c95 [⟨_,p95x40⟩,⟨_,p95x56⟩,⟨_,p95x95⟩,⟨_,p95x136⟩] (unpack 5 0x80030c890983070c208107062106028105830589800280014027800008900a04088124400502214005082204401f400e2240400140300284 98 0x166dad6c62d2bd2d265252a524ebcad274a0e6418e3c1ce841eec5b1634d9261d68b62d8d4cd2d3c8ed344cd1c1af7358b62d495250741cc23146418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x138 : Ex 95 7 [v199,v78,u2,u0,u1,u3] :=
  certify c95 [⟨_,p95x44⟩,⟨_,p95x131⟩,⟨_,p95x133⟩,⟨_,p95x136⟩,⟨_,p95x57⟩] (unpack 6 0xc892440070c2c1809832140068c05834036400f0589038605088004800380028001800040324059089002844028070605024055400e0281402922402081402a29120a04405e400c0881 228 0x3a130c7048e33a18e370430c3a430c4408c04648e32003006cc7cc3a36186cc60c7237df14561814788715b8a21476186c46187217df6c47df7216186e06184407c04607df20060071d3cf38c78c39d79d48c3cc71a3cf6d86586da6594983cf1454101473cf1573cf1474105954104843cf5133cf4844102003c04434034404002033cf14d1c714c14c14d38d14c1cc14b2891432031401c00831c3140140083046140100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x139 : Ex 95 7 [v199,u6,v78,u2,u0,u1,u3] :=
  certify c95 [⟨_,p95x97⟩,⟨_,p95x45⟩,⟨_,p95x134⟩,⟨_,p95x58⟩] (unpack 6 0x404240410c892440070c40444043400f09832140068c0583058903860508800380028001402e4032800020c00890028440280706050240550281400e2814402922400a04400c0881405f402a2912405e2204 222 0xa0e3a7965a2596738e2ce39096542594b38e98e3859459a594538539f3a569a39a3a57df0da68890886490869a8da6a27df8df7e269a2da6a17df85f7cb69a81a6857c581f7c568575144e78e75e74e44e71145a6da71b6da4510d24884516514484926124964515d14564922d14554d35134cb4511511474871521474513c820e0ce3d03ce20e34b3032cb0c82030ca1c91c52051c81c50c51c61c51051c11c5185103081040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x140 : Ex 95 8 [v78,u2,u6,u0,u1,u3,u4] :=
  certify c95 [⟨_,p95x46⟩,⟨_,p95x132⟩,⟨_,p95x135⟩,⟨_,p95x137⟩,⟨_,p95x59⟩,⟨_,p95x96⟩,⟨_,p95x98⟩,⟨_,p95x106⟩,⟨_,p95x138⟩,⟨_,p95x139⟩] (unpack 6 0x80098008400c0d120c89260c400b400a0d18098324402306070c400321404000068c0583400f058903864075050880078006800520c0800480038002800180000284402740150890405f20812a500a04405e088140280706407f050222042240210640014055400e0281 308 0x30c2cb30630630cd333062cb30c2cb33234d30c34d3322cb3301c730bc4b330c7030b1cb06f1c7206a862afaaa2061c72ae1c722daaa2aeaaa22d1c732b79e30bb0b32bb2b30b78b2079877ea79e88778722a9a606979e7c69868a99a67c67860c379e0c5a050e2a280c579e8a779e7e59a68a79a67e579e30b50b30d44d30b44b30d5142235144c79072a39232075077e15144de81e8a18207de51405d5144c668671b69a4c65140c34510c55140d95140c54516174514d25145955144d24510d00cf30d14d30b38b30d38d30b14b2091450c70c70c92892071470c60460c31450c30c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x141 : Ex 95 6 [v199,v211,u0,u2,u1,u3] :=
  certify c95 [] (unpack 5 0xc89070c038309830689070640280583400f0589400e028420c02440050221402c180508402202810a1021022912088140800a04 171 0x656b130596304b12d4b6210b42d8a55d08360d7c5cc8359081285652848150c65d574ad166300c61144028046349ad5cd729c96d5c1ad445108c10d419a629ca6398ad2bdee11c406804d100e060d8b4ad8962c6b525481a1435212830cc5394c731465104401904310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x142 : Ex 95 7 [v211,u0,u2,u6,u1,u3,u4] :=
  certify c95 [⟨_,p95x141⟩] (unpack 6 0x402280000d120c8924890d1809832183070c03830689070628d040280583400f0589405720c0401f400e0284400d0881400c0a04400b2440400a0502400321404000050840522102405120814001220440244021028140060a10 243 0x185551d81ec62b1d55693cf56a569aa954f5683cf1d11e84511cf1e62cb5675669e654b54f34f44b2cf2cf44d3652cb1cd1e534d1cb1e32cb0a40a392308b0930825405530135420a10823e23e18a13c20850821c31c56051c20956954e04d58154da4de69a3db3de7de3da3dc69a2db2dc75c2da2c760715a14768715b1426820030020c201a01961755455359355655351345044f48f45244f40f34c34b38b34e34b30b1c61c52891c81c51850840800c0083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x143 : Ex 95 7 [v212,u2,u6,u0,u1,u3] :=
  certify c95 [] (unpack 6 0x260c0c8924402306070c038309832140068c0583402805890386400f0508402b20c0400e0890400d02840689070605022a500a100a040281402a2081400c2912405522040881 240 0x4622cb4418014628204412cb3e12cb3c08003e18203c02c054b6cb56051454b50b5606db45f5144416c145f6db44150119d51418778719d79d1875073dc5143c06c03dc6db3c050061938e60b68b61969960b38b55738e55459455759655438e45138e44148145349244138e18740718938e1873871894103c03803c84083c04003c838e18c1c718b34b18c34c18b1c70811c71832831812811831c70881c70802401882480801c7183000081105083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x144 : Ex 95 7 [v199,v95,u2,u0,u1,u3] :=
  certify c95 [⟨_,p95x141⟩] (unpack 6 0xc89070c03830983068c0583402805890386400f405b089040290689070640550a100a04088102812440050221402c180508800020c029120284402a405e2240400e408340562081 216 0x76338e6513d16633cf75139168e34e68f2cb68e2ce68f34d1a12cb1908901a18a11902d06a02cb65135166034d6912d175e1c774e7ce75e7de74e1ce69c1c768b6cb69c6db68b1c71906101931c71901d01936185d11d16526126516115d21c719541018e58e19559518e4105124101914d11924d21914100cf20f0ce30e0cf30f0ce20e0cd30d0cb20b0cd20d0cb30b0c92090c70c70c92890c72071831440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x145 : Ex 95 8 [v95,u2,u6,u0,u1,u3,u4] :=
  certify c95 [⟨_,p95x142⟩,⟨_,p95x143⟩,⟨_,p95x99⟩,⟨_,p95x144⟩] (unpack 6 0x80030d120c89260c0d1809832306070c03834028068c0583400f05890386800208900a100a040689070622002204028180014055400c0881400b24404082400a050240032140408140000508800020c0405740150284405620814001400e405e2240 308 0x5d75555da5da5d70b05da5555ee4105d5bd55eebee5d54150ad41049a4da0ad4d349a4105eb2cb5d5b155ebb2b5d52d54903903532cb9102d049338e0aa2cb35a39a0aa38e35a2da0e82cb0d9a590e8a680d92d95d51955de81e5d58155de1864a51862109909e59a549019036318620b88b9238a234b18608218621a25a0a124921a1860d98190df1860d91990df8205de6595d57d55de7de5d565949c6590d07500dc75c4906590c30db0da09a0c36595d75965d55d55c25d85d559549345309009009351349045034e30e08b08b08e3ce34b30b2091c90860860892892061c60c31440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x146 : Ex 95 5 [v202,u0,u2,v29,u3,u4] :=
  certify c95 [⟨_,p95x70⟩] (unpack 5 0x29120c89214005082081240807060281224008810a04058305020a1080000890028420c02102 60 0x4824932629301a67a629819e67954f78c2f739a042509299865ad404a128198e61948310020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x147 : Ex 95 5 [v153,u0,u2,v29,u3,u6] :=
  certify c95 [⟨_,p95x71⟩] (unpack 5 0x20812408214005080c8922400706028120c0058305020a108000089002840a04210229120881 60 0x40a28401c094a22821e879daf7954f781c0389a23a1885ac60289422a12829cc50100300820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x148 : Ex 95 6 [v155,u0,u2,v29,u3,u6,u4] :=
  certify c95 [⟨_,p95x146⟩,⟨_,p95x147⟩,⟨_,p95x72⟩] (unpack 5 0x29120c89208124082140400340880508224007060a0420c0058308900a108002403e800108814087800021024076400b050202810284 77 0x82e902465022dc5346518c5cb614c5364a736be73ad2704410c2c8ac144488220d2bcad1384d62d484a0e53148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x149 : Ex 95 6 [v37,u0,u2,v29,u3,u6,u4] :=
  certify c95 [] (unpack 5 0x29120c8920812408214022400706028002840a1008810a0421832102058305020589050802810890 77 0x934d244c924340824c9318c0cf208825384258d684a12a338ca234894256b31ccb2148c5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x150 : Ex 95 6 [v156,u0,u2,v29,u3,u6,u4] :=
  certify c95 [] (unpack 5 0x29120c892081240821400689070c050820c005830280028108900a04088123062102070605020a100284 77 0x6250c234cc22444d34cd2944901344d4bd2d431ad739a931d292152910d26398e82308812c4a4a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x151 : Ex 95 6 [v39,u0,u4,v29,u3,u6,u2] :=
  certify c95 [] (unpack 5 0x70622402081240821400c890589050829120a040a10028105830502088108902841028421832102 77 0x80490834d082a51242246040c62b8a639ccc449118c00f330cc2b8ac2358c6b58502caa4250420020218e62906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x152 : Ex 95 6 [v40,u0,u4,v29,u3,u6,u2] :=
  certify c95 [] (unpack 5 0x70622402081240821400e0c2912088008900a0402810a1021832102058305020589050808810284 77 0x93492924d294292434084538824c9318c0cf208825394258c4a334c94256b31ccb2148c5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x153 : Ex 95 6 [v41,u2,u4,v29,u3,u6,u0] :=
  certify c95 [] (unpack 5 0x583089020c002842081240821400e0c070c050829120881070605020a040a102844028123062102 77 0x100441034cd02ca128425184226038c62b0c639cca8460f7b80d328ca2b0aa22d4a5ad450240820020218e62906208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x154 : Ex 95 6 [v164,u2,u4,v29,u3,u6,u0] :=
  certify c95 [] (unpack 5 0x58320c02081240821400c8929120a000a100881028408902306210207060502070c05080a040281 77 0x9348c924c8a429284a50434084539424c9318c0cf208825394258c4a3354b31ccb2148c5a9284a0e6398a42906218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x155 : Ex 95 7 [v29,u3,u6,u0,u2,u4] :=
  certify c95 [⟨_,p95x148⟩,⟨_,p95x73⟩,⟨_,p95x149⟩,⟨_,p95x150⟩,⟨_,p95x151⟩,⟨_,p95x152⟩,⟨_,p95x153⟩,⟨_,p95x154⟩] (unpack 6 0x29128007800623060689070680058004403e0a0480038002800180000a100890400f21834087068c05830d120d180c890881070c22400281058920c040030284408620812408210224400508407621400502 240 0x5a841080560562862858541081f34d9d069099f69f81034d5a534d60538562538e58534d0a334d0809000a392308034d81025089f65f85065081f24978d64d75a24970d24d6da6595972496052c56172cb5852450942490805400945540802400910000904d00914d10900100860000851050861060850002910c32904902914912900d028e0c328d3cd28e3ce28d0cd28b0c328930928b30b2890c92060c70850470860460850c50840410800c00840c3080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x156 : Ex 95 8 [v16,u3,u6,u0,u1,u2,u4] :=
  certify c95 [⟨_,p95x74⟩,⟨_,p95x155⟩] (unpack 6 0x2c18400c260c0689224040010d180983070c0383401621408001400340000a0480000281403d0a100890400f058903864086050840282489068c4036400b20c0408540150284408420812c500c89403c0881240824402089400a403f400e0502 308 0x22f1c720620622f56f2061c72081c722e24920824922e1c722079e20770722072020779e06d79e746ac656daeb74679e0c379e0c5b050d1b2c0c579e45279e76aaeb451aeb76a79e228596207a47228a682075877665965de9de6a69e675e59e0655965c69066a59245c65960c39240c55960d15960c59244624635e15964625965e14612073472206e02076c722034d75e6de3dc34d7de35e75c6db5d934d3d66166996185d634d05434d3c64065544103c634d0c334d0c54c50d14d30c534d45234d3ce4104514103ce34d0cc0cb2091452072872092892071470c60460c31450c30c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x157 : Ex 95 6 [v106,u2,u0,u3,u6,u1,u4] :=
  certify c95 [] (unpack 5 0x2c180983070c0c89240803860a10070608810a0421400508210220812204058324400502089020c002840281 81 0xd455aa6d1aa42d045116a7cd446c9a44450d63421540283a02121882085ec6b1a741d0f2388d6358b52d484a0e62148308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x158 : Ex 95 7 [v107,u0,u3,u6,u1,u2,u4] :=
  certify c95 [⟨_,p95x75⟩,⟨_,p95x157⟩,⟨_,p95x76⟩] (unpack 6 0x2c18260c2240068907060d180983070c03832183400b0d120c8928d08002400f0589408a20c04061400e0284400d0881400c0a0480018000028140010a1040032140400005084052210240512081400a24084046058340502440407c0502 243 0x2e5d721a22e6ae2175d54925d05d54155d24ad49222c22db2c2124aa49202b02aaea0124a830c5e95e8a685cc5e630c4a74a69e648c4a530c20e22538e20c20038090c3003000ce3a20005e35e28e25c05c600020320668620021771756155785755c55271241d41281241c41e71c31d31e7de31c30868819c18870819d18471c0030040c401c01b6995d65d56155d85d559549149051049349045038d38c3cc38f38c34c2072062ca2092061c61051000c0103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x159 : Ex 95 6 [v108,u0,u2,u3,u6,u1,u4] :=
  certify c95 [] (unpack 5 0x2c18098303830c8924080589058308900a040881214005082102220420810706244005020a10224002810284 81 0xc3d58a6518a3ace45116a0cc24649843c4e1634213a0212182c6b1ae5414741d0e23c81105cd6358b52d493a0e62148308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x160 : Ex 95 7 [v109,u2,u3,u6,u0,u1,u4] :=
  certify c95 [⟨_,p95x75⟩,⟨_,p95x159⟩,⟨_,p95x77⟩] (unpack 6 0x2c180d1809832306400b400f070c400321404000058903860508248920c0068c05838002800180000284401508900d120c892a50404022404082400e0281400d0a04400c0881405f2081405e2204400a2408404a0706407f2440404c0502 243 0x2e30c21122e46e20c32c8a232d32cb6c32232b8a222622b9a6222200980aa28808800e69948a24e84e9a284e28a78a29669a79a696288c68c39838c60c39a6a469a8a38a48e389a6a169a22022182021a69e69a01f01e7de01a0146184da69d69a4d861c61865a69b69a6586160003173165d630030600020320644620000e4ce31530e54e3133084481931884c81941844d30030040c401301245038d38c3cc38f38c34c2072862ca2092061c61051000c0103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x161 : Ex 95 7 [v213,u3,u6,u0,u1,u2] :=
  certify c95 [] (unpack 6 0x260c224006890706070c038309832140028140290a10400f0589038640770508248920c0400e068c05830890400d0a0402842c500c890d122440050240412081400c2912403f24080881 240 0x4a471c4818c14a48e348171c1a171c1878871a18a118771c38d71c38068038d68d38071c65f55559c81c65f81f59c55c48355548174148375d48155518774718b55518754718b75d39e55538074039e75d3805406dc3dc6da30c6dc31c6da3cf59830c6555d56585d759530c49430c4814c14944d348130c19030c18744719045018730738030038d3cd3803c038d30c0811c71832c31812c11831c708a1c708024018a2480801c0183000081105083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x162 : Ex 95 8 [v103,u3,u6,u0,u1,u2,u4] :=
  certify c95 [⟨_,p95x158⟩,⟨_,p95x160⟩,⟨_,p95x161⟩,⟨_,p95x78⟩] (unpack 6 0x2c18260c068907060d180983070c03830a0480030a100890400f058903862489068c05830d120c892400240805028002403f400c08818001224040404001028140032140407040000508800020c0408a4015028440892081400a400e403c2440 308 0x5ef5555da5da5ef0af5da5555e74105d59555e79675d54100ae41049a4da0ae4d349a4100ec4100d9b590ecb6c0d94105ea2cb5d5ad55eaaea5d52d54a82cb350a508e8a684902d00822cb35a39a0a338e35a2cb0d93990cd2cb0d92d90c338e5d51955e79275d59155e71864909102251869901904a592436218620b84b8e286134b1860a018621a25a0a024921a1860de1860d97d90de7de0d91995dc6595d57555dc75c5d56550c30db0da09a0c36595d75965d55d55c25d85d559549345309009009351349045034e30e08b08b08e3ce34b30b2091c90860860892892061c60c31440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x163 : Ex 95 8 [v199,u6,u0,u1,u2,u3] :=
  certify c95 [⟨_,p95x100⟩,⟨_,p95x101⟩,⟨_,p95x107⟩,⟨_,p95x79⟩,⟨_,p95x138⟩,⟨_,p95x139⟩,⟨_,p95x144⟩] (unpack 6 0xc8906890706800680058004224040292440070c03832c18098321404028068c05834041050280030281402a0a10400f0589038640430508400e80028001800020c02912402b400d08900881402e0a040284400c2081 228 0x39f6186498a271f8a264961872a6186458851ea8a2645605668596558a58728a686585963a75965499249a59245495968c35965455051c35035455966587584223cf4d83d866275d5603cf4168564e08605563d63893cf41f75d4c975d41f3cf4de3cf4057451de75d4053c565a0821186d871a6da6580985561961140825d609655418641208210f44f4d245140f08238d08210928a30b28a1090822050851031831c5185103082041040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p95x164 : Ex 95 9 (roots 95) :=
  certify c95 [⟨_,p95x1⟩,⟨_,p95x80⟩,⟨_,p95x82⟩,⟨_,p95x102⟩,⟨_,p95x108⟩,⟨_,p95x110⟩,⟨_,p95x111⟩,⟨_,p95x122⟩,⟨_,p95x128⟩,⟨_,p95x130⟩,⟨_,p95x140⟩,⟨_,p95x145⟩,⟨_,p95x156⟩,⟨_,p95x162⟩,⟨_,p95x163⟩] (unpack 6 0x800e2912800d800c24080d120c89800b800a22402204800906890706800880070d1809838006244021408005070c03838004800320c0208121020881400c0a048002068c0583400a05028001028140010a1008904015800005890386400005080284 240 0x4af4d34954954afc2f4954d3bac30c355755b6c76c3553154aa30c493ad34aaaea493313a6628a2559d5a269e625528a49128a49321349121149328a36328a24c90c96392334c28a89405409571585471409505549f04149381349f81f49305334c70c09d04178c04c35d71c25904108a68a6d969924a04a6150151945945d55951940144930134911d14931d349100034e00018c3cc40e3ce34c00c24a1ca1880002ca00a2481c70840001810c11440c3081000) (by decide +kernel)
theorem l95 : Claim 95 10 := fromSearch 4146 (by decide +kernel) p95x164

theorem r107x42x65x6 : Red 107 42 65 6 := markLift 107 42 65 6 l42 (by decide +kernel)
def c111 : Cuts (goalAt 111) := [
  ternaryRule 111 110 0 110 0 l110 none (by decide +kernel),
  ternaryRule 111 107 0 107 0 l107 none (by decide +kernel),
  ternaryRule 111 79 0 79 0 l79 none (by decide +kernel),
  ternaryRule 111 103 0 103 0 l103 none (by decide +kernel),
  ternaryRule 111 79 0 79 0 l79 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 111 47 0 47 0 l47 none (by decide +kernel),
  ternaryRule 111 47 0 47 0 l47 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 111 101 0 101 0 l101 none (by decide +kernel),
  ternaryRule 111 39 0 39 0 l39 none (by decide +kernel),
  ternaryRule 111 47 0 47 0 l47 (some (3,u1,u3)) (by decide +kernel),
  ternaryRule 111 69 0 69 0 l69 none (by decide +kernel),
  ternaryRule 111 109 0 109 0 l109 (some (1,u3,u6)) (by decide +kernel),
  ternaryRule 111 45 0 45 0 l45 none (by decide +kernel),
  ternaryRule 111 47 0 47 0 l47 (some (2,u1,u3)) (by decide +kernel),
  ternaryRule 111 103 0 103 0 l103 (some (1,u1,u6)) (by decide +kernel),
  ternaryRule 111 107 4 42 65 r107x42x65x6 none (by decide +kernel),
  ternaryRule 111 79 0 79 0 l79 (some (3,u1,u3)) (by decide +kernel),
  ternaryRule 111 109 0 109 0 l109 none (by decide +kernel),
  ternaryRule 111 107 0 107 0 l107 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 111 103 0 103 0 l103 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 111 43 4 42 1 r43x42x1x5 none (by decide +kernel),
  ternaryRule 111 107 4 42 65 r107x42x65x6 (some (1,u1,u6)) (by decide +kernel),
  ternaryRule 111 79 0 79 0 l79 (some (2,u1,u3)) (by decide +kernel),
  ternaryRule 111 109 0 109 0 l109 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 111 107 4 42 65 r107x42x65x6 (some (1,u3,u6)) (by decide +kernel),
  ternaryRule 111 110 0 110 0 l110 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 111 79 0 79 0 l79 (some (3,u1,u6)) (by decide +kernel),
  ternaryRule 111 107 0 107 0 l107 (some (1,u1,u6)) (by decide +kernel),
  ternaryRule 111 79 0 79 0 l79 (some (1,u1,u6)) (by decide +kernel),
  ternaryRule 111 79 0 79 0 l79 (some (2,u1,u6)) (by decide +kernel),
  ternaryRule 111 110 0 110 0 l110 (some (1,u1,u6)) (by decide +kernel),
  ternaryRule 111 109 0 109 0 l109 (some (2,u3,u6)) (by decide +kernel),
  ternaryRule 111 79 0 79 0 l79 (some (0,u1,u3)) (by decide +kernel),
  ternaryRule 111 79 0 79 0 l79 (some (3,u3,u6)) (by decide +kernel),
  ternaryRule 111 79 0 79 0 l79 (some (0,u3,u6)) (by decide +kernel),
  ternaryRule 111 77 0 77 0 l77 (some (3,u3,u6)) (by decide +kernel),
  ternaryRule 111 109 0 109 0 l109 (some (3,u3,u6)) (by decide +kernel),
  ternaryRule 111 79 0 79 0 l79 (some (1,u3,u6)) (by decide +kernel),
  ternaryRule 111 79 0 79 0 l79 (some (2,u3,u6)) (by decide +kernel),
  ternaryRule 111 110 0 110 0 l110 (some (1,u3,u6)) (by decide +kernel),
  ternaryRule 111 107 0 107 0 l107 (some (1,u3,u6)) (by decide +kernel),
  ternaryRule 111 103 0 103 0 l103 (some (2,u1,u6)) (by decide +kernel),
  ternaryRule 111 79 0 79 0 l79 (some (0,u1,u6)) (by decide +kernel),
  ternaryRule 111 103 0 103 0 l103 (some (3,u1,u6)) (by decide +kernel),
  ternaryRule 111 71 0 71 0 l71 (some (3,u1,u6)) (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x0 : Ex 111 5 [v214,u0,u6,u1,u3,u2] :=
  certify c111 [] (unpack 5 0x7062408038311202240058310a003860508210213060281140805022204208110811102 60 0x31226309a620a02499e62248e40902334cb591845a5491204831cc1094810800108c4100420) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x1 : Ex 111 6 [v215,u0,u6,u1,u3,u2,u5] :=
  certify c111 [⟨_,p111x0⟩] (unpack 5 0x30408000400213060706400f4001140824081420038321401120220410811102224002810583050220c003860508208121020284 72 0x58b2bc2d7742ec841aa840928a211332e4b30a228296a58d0f41866704411358b52d484a0a531cc51906208820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x2 : Ex 111 6 [v216,u0,u6,u1,u3,u2,u5] :=
  certify c111 [] (unpack 5 0x304013060706140824080383214010a0028411021081224002811420050205831120050805892102208120c0 81 0xb0d5695d1293cd290a9275c9670c42c5b1644c12721de20882b62d896a5cd398ed20da11044c5b16a4a92741cc42906208820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x3 : Ex 111 7 [v11,u6,u1,u3,u0,u2,u5] :=
  certify c111 [⟨_,p111x1⟩,⟨_,p111x2⟩] (unpack 6 0x304040021306068907062306400f4001224010a0068c05830589038621838001800020c040000284400e1408400d400c1420400b400a11021081070c03830281050224402140210224080508400940081120400640072081 225 0x23cf22b211aeb20f3d13cfa90411410a8f3e930c3d13e94693cc32730c2e82e7a272cc32630c2232268e320c32530c9238e58e390c30f60f42240f88f41840c88c8d860c60c8e28a06182e12e08602d82df61819e19f79e19861d61821a21d69a21821c61865a69b69a6586162cb3d73d64563cb3c72cb20a20728720b2d551340640f48f41140f18f34618c38c34e34c18c2c92ca1862c62ca2492062072472092071861440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x4 : Ex 111 5 [v217,u0,v16,v17,u2,u5] :=
  certify c111 [] (unpack 5 0x1408130620814013110202812240058903860583028430401081214011200508220c142005022206 57 0x77bce70ccee3c9ce235ce0b5cd738d18860779dee6b9ac22c8a0a8293a0e62148308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x5 : Ex 111 6 [v16,v17,v15,u0,u2,u5] :=
  certify c111 [⟨_,p111x4⟩] (unpack 5 0x1408130640140383070c07060281224010a0800003860589058320c002844007400a1102108111202089142021404006400520834011208105080502400e4003 180 0x7b5a3739ee70dad7b5a2f89fff89adf672d7b7cff373986729e27bce2739de723c0f78c0f39d6722c0b58c0b396c5aebb9b76ba2ecdf388c731ce2f784629aa6d5aa631a462390e9290e319c62290a7290a22725cd835cf7352d19c604b0691a0eb11c454a849120e6100851904310400) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x6 : Ex 111 6 [v217,u0,v17,u6,u3,u2,u5] :=
  certify c111 [⟨_,p111x4⟩] (unpack 5 0x130607061408800040131420208111020281224005830502218305890386028430401081214021022206112005084005 75 0x188731a1033cd77bd967bc8e7bc2e7b9ef2b0d5330946058c9ca2681a0f73dcd6358b22c8a0a42831cc52148308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x7 : Ex 111 7 [v17,u6,v15,u3,u0,u2,u5] :=
  certify c111 [⟨_,p111x5⟩,⟨_,p111x6⟩] (unpack 6 0x3040130606890706401503832306070c0281224010a0068c0583800103862183058920c002841408400d14208000400c0502400e400a1102108140072102208340031120214005084005400640112081 234 0x8b2c99c93679c92cb34b2c430c34c3042cb99f7cb34b98d98b7df91f7cf94f92590f7df8df7c58858e28857df85f7c978985e7897df81f7c478481e7847df2d52cc74c2dd2cc54c7dd7de5557d57de75d6d554f70f6dc6cf54f2955456456996455556155495896165895495d55445845d658455550f3cb38b50d50b3cb4c14823cf24224e09124f3c44041cf3c43cf1ce1cc14c2ca2cc34c2c52c90c92851491490832040c41c51841440830c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x8 : Ex 111 6 [v217,u0,v16,u6,u1,u2,u5] :=
  certify c111 [⟨_,p111x4⟩] (unpack 5 0x14081306038380004017112020811102028122400589050803862489058302843040108124402408220c142005024005 75 0x18873183733cd67bc8e7bc2e7b9ef740d0331f57b094605819ca2681a0f73dcd62d8b228890a42831cc52148308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x9 : Ex 111 7 [v16,u6,v15,u1,u0,u2,u5] :=
  certify c111 [⟨_,p111x5⟩,⟨_,p111x8⟩] (unpack 6 0x3040140813064018260c0706224010a00589800103862489058320c00284070c0383028140091120800040080508400b400a1102108140072408208940111420244005024005400640032081 234 0x8b2c99493659492cb34b2c49043649042cb8d450b34b8cd8cb5148945055458955455148545097c985f7c95148145047c481f7c45142d72cc78c2de2cc5cc51e51f5d751751f79e7575cf6cf75b6cf5d72975c56c571b6c55d76975c96096986095d76575c46046586045c430f30b38b30d30b3cb54f3d45945565543d44c14823cf24224e09124f3c44041cf3c43c41ce1cc14c2ca2cc34c2c52c90c92851491490832040c41c51841440830c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x10 : Ex 111 8 [v15,u1,u3,u0,u2,u5,u6] :=
  certify c111 [⟨_,p111x3⟩,⟨_,p111x7⟩,⟨_,p111x9⟩] (unpack 6 0x304030202204130606890706400120c0224010a0068c058305890386401940000284800224081408401614208001070c0383401202810502401105084010400311204007800021024006400520811102400440021081 308 0xa9000084a840a9aa90840004684104448844688a84444100a74100800800a70a708041046541044f98f4659a544f4104514104644924514924644107046847078c77048c470768708068008384308084008368345085046269a45069046286171f69a70f80f71f81f70f68f71e69a70d74d71e75d70d69a71c69a71b75d71c75d71b69a1983cf2c42c42d86581843c40973cf0800800970970803c02d639518734738438438750718434408334308008008308308034045234d4504d04524d24503502cf2cf2ce34d2cb2cb2cc2ca187147244244247207184144083043080080083083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x11 : Ex 111 7 [v11,u3,v17,u1,u6,u0,u2,u5] :=
  certify c111 [] (unpack 5 0x304013060706224010a00386058320c002842408401f11020383028120830508214040091408108121022440400c0502400e1420 92 0x31726339c6339c661b0c616cc65acc60aec65acc338ce64595896458a6918ca5188a628ca5183dc67192c6b0a95a84412508118e61148218820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x12 : Ex 111 6 [v218,u0,u3,u1,u6,u2,u5] :=
  certify c111 [] (unpack 5 0x3040130606890383110222402102038620c0028410811408400f02814001220420812408112021400508058314200502 81 0xd3ddaa6d94a3c94a0d5536cda3551513c4e418c2c6b1a6398ed9b66a929e789e2f1c06f0882e6b1ac52d493a0e628c8310400) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x13 : Ex 111 6 [v60,u0,v23,u1,u6,u2,u5] :=
  certify c111 [] (unpack 5 0x30401306038320811120214005030583068c4000142005020281224021830589050802841081110224082102 81 0x3054691d129021284a562188654cd20080b029562188684a132900312c0af739ac5a94310c494250701c06298a41886208020) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x14 : Ex 111 7 [v23,u3,u1,u6,u0,u2,u5] :=
  certify c111 [⟨_,p111x12⟩,⟨_,p111x13⟩] (unpack 6 0x3040130623061624068910a02183058903868001068c070c0383402440231408400e1420400a110240021081400f224040010281800020c04000028440222081400d210240212408402011204005214040160508400c40060502 243 0xc5d72ec2dab2c2d75eb4d35da5eb6ab5d34ea4d32d52ea5552d34e94d36e86e9a286d34d73d76676579d764f6539d354f3d33d35679e63cf2d12e64512cf2e53cf0e40e59240cf3dc3cf6e26e38a26cf3d90d95df5d96995c35e00c34e14e08604c34cb0cb24524b14b2430dc1456c30df0c36c56dd79d5db5dd6dd5dc5c96c92cc2c93092db2d96195c25d96995d85d55154d64d55954d44d14113c23d14913d03cb38d24c34b30b24a2452070c60c51850c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x15 : Ex 111 5 [v51,v60,v16,v17,u2,u5] :=
  certify c111 [] (unpack 5 0x130620814013110203050502244010811408224002810508240821020605028403862140 60 0x539ca5112a3aa27395073910741ce88408f5394e2acad63164525493a0e0318052008310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x16 : Ex 111 6 [v60,u0,v16,v17,u1,u2,u5] :=
  certify c111 [⟨_,p111x15⟩,⟨_,p111x4⟩] (unpack 5 0x1408130603830508208380012081400302812240068c80002140248905830284108111022408220c050224402102 78 0xc5298c0b19c6ab9c46b9c06b9ae734a62994ea3a605024a0c550801e6298ae6b9ac52d492248802007314c52048310820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x17 : Ex 111 6 [v51,u0,v16,u3,v17,u2,u5] :=
  certify c111 [⟨_,p111x4⟩,⟨_,p111x15⟩] (unpack 5 0x13060689208140132089050211020589038680012183028410811408224002810508240824408000214021022206 78 0x150829414a8eab1ce541ce4a9ce141e940cd2a4a8a42ca2a82a0741d0f2b8ae2348c0b02b525493a0e2318451106208820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x18 : Ex 111 7 [v16,u3,v17,u1,u0,u2,u5] :=
  certify c111 [⟨_,p111x5⟩,⟨_,p111x16⟩,⟨_,p111x17⟩] (unpack 6 0x1306260c06892306224010a08002038624898001068c218320c0028411024014038302810508800040082140400b2083401120812102400a14081081400c244024084003400e208940050502 234 0x2882055d72975c520828820b24b28924b20895450828894a9485149145058459218455140d45068c65a38c651489450b84b8a184b5142182178172202176175205216185185218203d86107907de7906187586056457596456180d86066c671b6c661869860b64b69964b60b5d05c83c85ca5c84085504143d45565544140414c341018318f0d219040b44b35040b40b34f38b10c34530b14b0c41091892032092892062051c5106185185103081040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x19 : Ex 111 8 [v17,u1,u6,u0,u2,u3,u5] :=
  certify c111 [⟨_,p111x7⟩,⟨_,p111x3⟩,⟨_,p111x11⟩,⟨_,p111x14⟩,⟨_,p111x18⟩] (unpack 6 0x30404002140880042440400c800380028001400313060689070623064001068c0583224010a02183038620c0401e40000284401d20811102401c108180000502400e14200383401b02812102401121402083401a40050508 308 0x3cf38e3c6ac63cfaeb3c638e3cf38e3ea4103cf4103ea38e3e930c3ce28e3e92a93ce30e04130c0469c60689e704630c9a528a2e230c92330c2e228a3e11c73ce3ce3e13e13ce1c721f1c720c80c21f81f20c1c721e1c720668621e69a2061c72081c721d69a20869a21d1c73ce4ce3d06503ce64e3d04d055b4d354c70c55b71b54c4cc20764721a4d32074c721a6595584d35465865585965464c65554d35445c45555d75444d35554d35545965555965544d30521513d01103ce3ce3d03d03ce10e2cc10c14a14a14c34c2ca10a209104207207209209207107046046045104041043042040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x20 : Ex 111 7 [v11,u1,v16,u3,u6,u0,u2,u5] :=
  certify c111 [] (unpack 5 0x304013060689224010a0068c038620c00284210240291408244020890502400d11021081038302812408214040080508400b1120 92 0x41728439c84252832306316c6336e635ac635ac642509344d5896518b6918ca5188a718ca5183dc8720ad62d4a4a128118e6114822084418820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x21 : Ex 111 6 [v219,u0,u1,u3,u6,u2,u5] :=
  certify c111 [] (unpack 5 0x3040130607061408240803832240058320c0028410811102400f0281400120812102142024400502058911200508 81 0xc3d989655293c1291d12364d833c8eb62d814c526398e320c2c5b169825c731cce1bc6e0882d62d8b4a928398e628c8310400) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x22 : Ex 111 6 [v51,u0,v29,u3,u6,u2,u5] :=
  certify c111 [] (unpack 5 0x30401306070620811420050905890386400005081102218305830284108114082240028121022408244005021120 81 0x825905454a5218a50d0a141d0120c2741d06298b398c92088317c1ee035a862185314cb22c8a0a82941d07298a020c8308820) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x23 : Ex 111 7 [v29,u1,u3,u6,u0,u2,u5] :=
  certify c111 [⟨_,p111x21⟩,⟨_,p111x22⟩] (unpack 6 0x3040130623060689070610a02183068c058380010386402c1102400b13240383402b1120400a140840021081400f224040010281800020c040000284402a208140092408401a2102402014204005244040100502400840060508 243 0xc5d726c25ab2c2575eb4d35da5eb6ab5d34ea4d325526a5552534e84d30e90e8a680d34d73d78278179d780f8139d354f3d33d35679e63cf25126645124f2643cf0e50e49640cf0df3cf6e26e38a26cf3d90c35dc5d96995c35cb0c324524b14b2430e08605db5e06e05df5dd6db4de4dd79d4db4c96c92cc2c93092db2c36c315c14370315b6d96195c25d96995d85d55154d64d55954d44d14113c23d14913d03cb38d24c34b30b24a2452070c60c51850c40c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x24 : Ex 111 8 [v16,u3,u6,u0,u1,u2,u5] :=
  certify c111 [⟨_,p111x3⟩,⟨_,p111x20⟩,⟨_,p111x23⟩,⟨_,p111x9⟩,⟨_,p111x18⟩] (unpack 6 0x304040021306260c06894001070c03838004214080034008800280018000400b40111120110202814028224010a00589038605082489068c20c0402740000284402620811408402510812408400324402089402140050502 308 0x2081c7206ac6208aeb2061c72081c722a24920824922a1c72296182072072292292076185e86185c65865e85965c66185d76185c49c45d79e75c46185d76185e65965d75965e66182194992076872196992074875e44925d89585e49645d84980414920468860638a204649214569a14449216149214469a81f69a71b49279d49271b69a2073072195592075472193195d85585d630c5d83185d655539430c3924d23944d339230c39130c3863c63913cf38630c38e30c38440438e41038430c38e30c38d3cf38e3cf38d30c04b14a209109207207209209207107046046045104041043042040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p111x25 : Ex 111 9 (roots 111) :=
  certify c111 [⟨_,p111x10⟩,⟨_,p111x19⟩,⟨_,p111x24⟩] (unpack 6 0x304030208002244024081408220413060689070680012140400540118000400314201120070c038320c020812102108140021102068c0583050202814001224010a005890386400005080284 240 0x36438e35095036496435038e6612495908908e18a165025036024934e54e36056034e24e1df2081d01901df19f1d020835e20834e34e35e35e34e2081dc2081c97491dc75c1c920864f04f6106906cf68f65005034c04c34e50e34c50c34e04e5895096150415c90495955141d20411c84c81d24d21c804809001008f44f09045008f00f34e00e34c14c34e14e34c00c08a0000892c908a2ca0890091c81481c60001c80081c61450840000810c10840c3081000) (by decide +kernel)
theorem l111 : Claim 111 10 := fromSearch 4146 (by decide +kernel) p111x25

theorem l119 : Claim 119 8 := fromLift 8 64 82 l55 (by decide +kernel)

theorem l123 : Claim 123 9 := fromLift 9 17 4148 l106 (by decide +kernel)

theorem l125 : Claim 125 8 := fromLift 8 64 20482 l61 (by decide +kernel)

theorem l126 : Claim 126 9 := fromLift 9 20 17962032 l106 (by decide +kernel)

theorem r111x106x5x9 : Red 111 106 5 9 := markLift 111 106 5 9 l106 (by decide +kernel)
theorem r125x21x104x7 : Red 125 21 104 7 := markLift 125 21 104 7 l21 (by decide +kernel)
theorem r119x21x98x7 : Red 119 21 98 7 := markLift 119 21 98 7 l21 (by decide +kernel)
theorem r110x106x4x8 : Red 110 106 4 8 := markLift 110 106 4 8 l106 (by decide +kernel)
theorem r117x21x96x6 : Red 117 21 96 6 := markLift 117 21 96 6 l21 (by decide +kernel)
theorem r123x42x81x7 : Red 123 42 81 7 := markLift 123 42 81 7 l42 (by decide +kernel)
theorem r107x106x1x8 : Red 107 106 1 8 := markLift 107 106 1 8 l106 (by decide +kernel)
def c127 : Cuts (goalAt 127) := [
  ternaryRule 127 126 0 126 0 l126 none (by decide +kernel),
  ternaryRule 127 123 0 123 0 l123 none (by decide +kernel),
  ternaryRule 127 123 0 123 0 l123 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 127 106 0 106 0 l106 none (by decide +kernel),
  ternaryRule 127 119 0 119 0 l119 none (by decide +kernel),
  ternaryRule 127 117 0 117 0 l117 none (by decide +kernel),
  ternaryRule 127 111 0 111 0 l111 none (by decide +kernel),
  ternaryRule 127 110 0 110 0 l110 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 127 111 16 106 5 r111x106x5x9 none (by decide +kernel),
  ternaryRule 127 95 0 95 0 l95 none (by decide +kernel),
  ternaryRule 127 87 0 87 0 l87 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 127 125 2 21 104 r125x21x104x7 none (by decide +kernel),
  ternaryRule 127 93 2 21 72 r93x21x72x6 none (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 none (by decide +kernel),
  ternaryRule 127 55 0 55 0 l55 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 127 61 2 21 40 r61x21x40x6 none (by decide +kernel),
  ternaryRule 127 124 0 124 0 l124 none (by decide +kernel),
  ternaryRule 127 126 0 126 0 l126 (some (2,u1,u3)) (by decide +kernel),
  ternaryRule 127 119 0 119 0 l119 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 127 119 8 21 98 r119x21x98x7 none (by decide +kernel),
  ternaryRule 127 126 0 126 0 l126 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 127 118 0 118 0 l118 none (by decide +kernel),
  ternaryRule 127 126 0 126 0 l126 (some (3,u1,u3)) (by decide +kernel),
  ternaryRule 127 125 0 125 0 l125 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 127 106 0 106 0 l106 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 127 93 0 93 0 l93 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 127 61 0 61 0 l61 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 127 110 16 106 4 r110x106x4x8 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 127 111 0 111 0 l111 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 127 95 0 95 0 l95 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (1,u0,u1)) (by decide +kernel),
  ternaryRule 127 125 0 125 0 l125 none (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (3,u0,u1)) (by decide +kernel),
  ternaryRule 127 110 0 110 0 l110 none (by decide +kernel),
  ternaryRule 127 117 8 21 96 r117x21x96x6 none (by decide +kernel),
  ternaryRule 127 117 2 21 96 r117x21x96x6 none (by decide +kernel),
  ternaryRule 127 110 16 106 4 r110x106x4x8 none (by decide +kernel),
  ternaryRule 127 29 2 21 8 r29x21x8x5 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (2,u0,u1)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (0,u0,u1)) (by decide +kernel),
  ternaryRule 127 123 0 123 0 l123 (some (3,u0,u1)) (by decide +kernel),
  ternaryRule 127 111 0 111 0 l111 (some (3,u0,u1)) (by decide +kernel),
  ternaryRule 127 95 0 95 0 l95 (some (3,u0,u1)) (by decide +kernel),
  ternaryRule 127 111 0 111 0 l111 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 127 95 0 95 0 l95 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (3,u0,u3)) (by decide +kernel),
  ternaryRule 127 123 0 123 0 l123 (some (1,u0,u3)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (2,u0,u3)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (0,u0,u3)) (by decide +kernel),
  ternaryRule 127 123 0 123 0 l123 (some (3,u0,u3)) (by decide +kernel),
  ternaryRule 127 111 0 111 0 l111 (some (3,u0,u3)) (by decide +kernel),
  ternaryRule 127 95 0 95 0 l95 (some (3,u0,u3)) (by decide +kernel),
  ternaryRule 127 115 0 115 0 l115 none (by decide +kernel),
  ternaryRule 127 107 0 107 0 l107 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 127 87 0 87 0 l87 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 127 55 0 55 0 l55 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 127 121 0 121 0 l121 none (by decide +kernel),
  ternaryRule 127 123 0 123 0 l123 (some (2,u1,u3)) (by decide +kernel),
  ternaryRule 127 119 0 119 0 l119 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 127 123 0 123 0 l123 (some (3,u1,u3)) (by decide +kernel),
  ternaryRule 127 123 0 123 0 l123 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 127 125 0 125 0 l125 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 127 93 0 93 0 l93 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 127 61 0 61 0 l61 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 127 123 4 42 81 r123x42x81x7 none (by decide +kernel),
  ternaryRule 127 107 16 106 1 r107x106x1x8 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 127 111 0 111 0 l111 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 127 95 0 95 0 l95 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (3,u1,u2)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (2,u1,u2)) (by decide +kernel),
  ternaryRule 127 107 0 107 0 l107 none (by decide +kernel),
  ternaryRule 127 59 4 42 17 r59x42x17x6 none (by decide +kernel),
  ternaryRule 127 107 16 106 1 r107x106x1x8 none (by decide +kernel),
  ternaryRule 127 126 0 126 0 l126 (some (1,u1,u2)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (0,u1,u2)) (by decide +kernel),
  ternaryRule 127 126 0 126 0 l126 (some (2,u1,u2)) (by decide +kernel),
  ternaryRule 127 111 0 111 0 l111 (some (2,u1,u2)) (by decide +kernel),
  ternaryRule 127 95 0 95 0 l95 (some (2,u1,u2)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (2,u1,u3)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (3,u1,u3)) (by decide +kernel),
  ternaryRule 127 123 0 123 0 l123 (some (0,u1,u3)) (by decide +kernel),
  ternaryRule 127 107 0 107 0 l107 (some (0,u1,u3)) (by decide +kernel),
  ternaryRule 127 107 16 106 1 r107x106x1x8 (some (0,u1,u3)) (by decide +kernel),
  ternaryRule 127 87 0 87 0 l87 none (by decide +kernel),
  ternaryRule 127 55 0 55 0 l55 none (by decide +kernel),
  ternaryRule 127 106 0 106 0 l106 (some (0,u1,u3)) (by decide +kernel),
  ternaryRule 127 111 0 111 0 l111 (some (0,u1,u3)) (by decide +kernel),
  ternaryRule 127 95 0 95 0 l95 (some (0,u1,u3)) (by decide +kernel),
  ternaryRule 127 103 0 103 0 l103 none (by decide +kernel),
  ternaryRule 127 79 0 79 0 l79 (some (0,u1,u3)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (0,u1,u3)) (by decide +kernel),
  ternaryRule 127 126 0 126 0 l126 (some (0,u1,u3)) (by decide +kernel),
  ternaryRule 127 110 0 110 0 l110 (some (0,u1,u3)) (by decide +kernel),
  ternaryRule 127 110 16 106 4 r110x106x4x8 (some (0,u1,u3)) (by decide +kernel),
  ternaryRule 127 111 0 111 0 l111 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 127 95 0 95 0 l95 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (1,u1,u3)) (by decide +kernel),
  ternaryRule 127 111 0 111 0 l111 (some (2,u1,u3)) (by decide +kernel),
  ternaryRule 127 95 0 95 0 l95 (some (2,u1,u3)) (by decide +kernel),
  ternaryRule 127 106 0 106 0 l106 (some (2,u1,u3)) (by decide +kernel),
  ternaryRule 127 111 0 111 0 l111 (some (3,u1,u3)) (by decide +kernel),
  ternaryRule 127 95 0 95 0 l95 (some (3,u1,u3)) (by decide +kernel),
  ternaryRule 127 106 0 106 0 l106 (some (3,u1,u3)) (by decide +kernel),
  ternaryRule 127 111 0 111 0 l111 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 127 95 0 95 0 l95 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (3,u2,u3)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (2,u2,u3)) (by decide +kernel),
  ternaryRule 127 126 0 126 0 l126 (some (1,u2,u3)) (by decide +kernel),
  ternaryRule 127 63 0 63 0 l63 (some (0,u2,u3)) (by decide +kernel),
  ternaryRule 127 126 0 126 0 l126 (some (3,u2,u3)) (by decide +kernel),
  ternaryRule 127 111 0 111 0 l111 (some (3,u2,u3)) (by decide +kernel),
  ternaryRule 127 95 0 95 0 l95 (some (3,u2,u3)) (by decide +kernel)]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x0 : Ex 127 9 [v217,u3,u0,u1,u2,u4,u5,u6] :=
  certify c127 [] (unpack 6 0x3020401b29121a24191222401a301306068907064001401a40190d1809834018070c0383401740164015112021021102028109920a1005890508068c058303864014028424084013140840120d120c8905024005401140101420400f2081400e400d2204400c400b1081400a4009304040080881400740060a04 412 0x37c2081ce14e3fc17c34e2080ba0c308e08e0baefa08e0c30b80c3088e480b8e780880c334b924b4edceb4bdcb34e9241f5924b48d88b75db51c89240809240838830808800839245f3924b54d14b73d335d4924b6d8a2b72924b6d924b728a2366826a8e4cec66266a8e80e1e5825a884c8c25265a888080ae820083bc30aebee083803b6b820aa4b24b6bb2baa48245d45d4aaa8207148145ea5e84e9a2770e74e72672670e3ce7267667087487257257082887257657037437008c07038c37007407248e47227627247647228e27217e172076072175d7207e071e75e7147d471e7de71475471c4db35a5145ce4ce35a65a5ce50e1d85145c84c81d86585c85080955140835830955950835034d245034e30e24b3cb24e24e34b30b1c81882452852482481c5185083043080100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x1 : Ex 127 9 [v60,u3,v51,u1,u2,u4,u5,u6] :=
  certify c127 [] (unpack 6 0x402530403020402429121a24191222401a3013060689401a40190983038305080589030522044023028140030c980a104010060540170284068c401f400424084005140840120c890583400005022081400e2102401540221081400a110209920881402103860a04 424 0x2f11c718cc8ccf1cb12cc1c70af0c308c08c0afc2f08c0c30ad0c3087b870adbad0870c32e17df78cb0c7a1b212cc7df1aa7df787ac77aaaea1877df0807df0837030807000837df45e7df78fa4f79ea6944f7df78171c7847df7817df78471c2ca8ca64c4cca0a80a64c8cc1858c56474c79c58056478c70a68e60830830a60a60838c37a58e565f79f7a57a565f8df38e3a444f44f6598e34cf8cf4594494c12416568e34c18c16564e22cc5cc6e16e16cc80c2e15e11875c76d26d26c78071925d20835c30807400837430805c079f75f79c5dc79f5df79c75c44f54f4db5d74cf5cf45355a4415586565d84c15c14d65552d43d444c4cc2d421444c3cc1923d24474c71922124473c70903cf0830830900900833c338e38d2cc04c24a24a24c20c2ca04a187047245245247207185045083043080100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x2 : Ex 127 10 [v51,u0,u1,u2,u3,u4,u5,u6] :=
  certify c127 [⟨_,p127x0⟩,⟨_,p127x1⟩] (unpack 6 0x3040302029121a241912244024080d120c8922401a30130606890706098340150383402605082102110280010583099205890386030540004020401f02842081401e400d22041081401d400914080881401c40060a0440108000050240054004142040030281400240010a10 420 0x574492556d56574d7455649257338e55655657357355638e47138e452c92471cb145238e56f208556c1656fc2f55621644f20845215244f14f45221236d20834eb8e36dbad34e20e5530c3556b16553b135560c346a0c3452ad246aaea4520c334b0c334e00e34b00b34e0c31280c3088a48128a680880c356276255655656256255675646176145245246146145275236776734e34e36736734e74e1c89886057451c87486059850a57656031031251250837436a46a355671656256255655656272245271246146145245246172134e70e34b78b34e78e34b70b69f71f68868869f81f68870808378368070068370308078069d61d69a71c69a69b69961755651655355355655655351345241244f44f45245244f40f34e30e34b34b34e34e34b30b1c81882852852882481c5185083043100100103103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x3 : Ex 127 10 [v220,u0,u1,u2,u3,u4,u5,u6] :=
  certify c127 [] (unpack 6 0x3040302029121a2419122440240814080d120c89224022041a301306068907060983038320c010a00a04068c05830a10089003840589028421024020400d20811102402a400910810b06402940060881400505024004142040030b12402840010281402705084000401f401e0386 420 0x6754d3657d97675db56574d36743cf6576576746746573cf5723cf553cd3572cf25533cf67034d657c57670c7065735756f34d5532d356f2ef55335346d34d44fb8f46dbad44f34f66b186657b1766bb2b657186569186553a93569aa955318646218644f7cf4627e244f1862a718620da0d2a7a2720d18665a71a65765765a65a65771755671655355355655655371346672644f44f46646644f70f08d38d08b70b08d70d08b08b2257250860860a52a52067066576d765a91a65791765a6da5536d35568d65538d35566d644f6cf4627a244f78f4626db0e06db0cd84d0e08600cd6cd2067860df6db0c66c621f79e0c30dd0dc09c0c36db65a61a65765765a65a65761755651655355355655655351345241244f44f45245244f40f08d30d08b08b08d38d08b30b2091c90860860892892061c60c31440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x4 : Ex 127 10 [v60,u0,u3,u1,u2,u4,u5,u6] :=
  certify c127 [⟨_,p127x1⟩,⟨_,p127x0⟩] (unpack 6 0x3040302029121a241912224022041a3013060689400121400d1809834003070c03834010401580014005401f1120240814080c89403005020281402f0c980a108000058905080583068c05034000402e400402842081402d400d21021081402c400911020881402b40060a04 420 0x2b41c728bd4b2b4d7428b1c72b30c328b28b2b32b328b0c31b10c3187c871b1cb11870c32af65928bc0b2afc2f28b6591ad659187b871adbad187659080659083583080580083659367659612b129e7b2c6126599e759662b6599e765962b5962884c828ba8b288a8828b4cb1844c41877c71847c41874c70a84d3083a430a8a680834c36254d39d99999e59a56194d93527df8644d38524d33637df8e37df8604d38e24d38607df29e49e28b28b29e29e28b48b19d49d18718719d19d18748709c49208308309c09c0834833db3da28b44b28828828b28b2884481874471841841871871844440834430805c00835c30804406195d93d64563d94596165d63d44543d33d33d45543d34533d23523cf4513cf3d03ce34c28b24b28828828b28b288248187147184184187187184144083043080080083083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x5 : Ex 127 10 [v221,u0,u3,u1,u2,u4,u5,u6] :=
  certify c127 [] (unpack 6 0x3040302029121a241912224022041a301306068921400d180983070c03830c8920c0210210a011020a040a100890058903860582058302842408402e400d208114084034400910810e0c40334006088140030e18403240010281401f4005050811204031050240004004402d068c 420 0x6754d3657d97675db56574d36743cf6576576746746573cf5723cf553cd3572cf25533cf67028a657c57670c7065728a56e28a553bd356ebee55328a46228a44f84f46286244f28a08228a31cb5c08eb6d31c28a6651e5657b17665b256571d75631e35531935631a35531d346a1c744facf46aaea44f1cf3281c738aa4a3a8a6830a1ca09c1860881c709c1c708218665a71a65765765a65a65771755671655355355655655371346771c44f44f46746744f70f6576d76659a56579976656e55536d35639235539135636e344f6cf46282244f80f4626db30a80a0e16db0ca6ca3218200df6db0c77870df79e0c76db0c30dd0dc09c0c36db65a61a65765765a65a65761755651655355355655655351345241244f44f45245244f40f30d2cd08a08a08d38d30a2ca0872470860860872070860860c31440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x6 : Ex 127 9 [v222,u3,u1,u2,u0,u4,u5,u6] :=
  certify c127 [] (unpack 6 0x30403020404229121a24191220c010a005890386068c058302844018400008902204404113060b120706028140054040403f0d180983070c03830689403e403d05081324403c11204013240816241408403b0d120c8905024035403a40391420400f21024038400d2081400c400b110240374009108140080a04403640060881 412 0x37e1451cbfcb3feffe34b1450bc00008b08b0bcf7c08b0000ba000085ec50baefa08500034bccbc8ee4ec8be4b34ecce1c5cc5c88e08c85e051c8cc8080cc0083c03080c00083cf3823c3082ccf3823cf382cc30877cf3c9fd9fcb7db685fcf35f4cf3c94d54cb4d745d4cd4cb2c30cb1cf3cb2cf3cb1c3082f8ef80b80b82fbaf80b8cb82d8e380580582dbad8058c58038c3800b00803b038008c082b8e381489482b8ab8148d4820a6a34e7ce84ba4ba0e24e84b7cb1c87c88457859c87888457c50a57df0809800a59a50807c08237df8229228239238227df5d47948597df8147d45d979e4dd4dc35a5145cb4cb35a6da5cb50b1d85145c56451d86585c55050955140805800955950805004d245034e30e24b3cb24e24e34b30b1c81882452852482481c5185083043080100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x7 : Ex 127 9 [v94,u3,v77,u1,u0,u4,u5,u6] :=
  certify c127 [] (unpack 6 0x30403020404a29121a24191220c010a00386068c028440030890400540404023403f098305081324070c0283210211020e1840390485403e02810689401f4004404924081624403b0c89070640010502220440382081403540411408403710810b120a04404803830881 424 0x2f314518ad0a533d332ca1450b100008a08a0b1cb108a0000af000085c050afc2f0850002caa8aa5eb9ea4ab8a2dea9e185a85a5db5da45b4519da9d080a80083a03080a00083aaa669aaaa60b2ca69b2c660aaaa57a28a5caaaa57aaaa5ca28469aaaa4facfa69aeb44faaaa41a28a44aaaa41aaaa44a282de81e64a9ca99e95e64a80a19d81d64584591d85d6458050a38230800800a30a308080038e3a244f84f65282024f80f45286124124165682024180165625f2de5de6ca6ca6de21e2ca5ca19d5dd6c56c56dd21d1855c50835c30807000837030805c044f54f25b5d724f5cf44955a4415586565d82415c12565552d33d344a24a2d351344a3ca1873c74454851874874453c50903cf0800800900900803c038e38d2cc04c24a24a24c20c2ca04a187047245245247207185045083043080100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x8 : Ex 127 10 [v77,u1,u2,u0,u3,u4,u5,u6] :=
  certify c127 [⟨_,p127x6⟩,⟨_,p127x7⟩] (unpack 6 0x3040302029121a2419122440240814080d120c8920c010a0068c0583038640030284404b40000890220413060b1280010706404702810983400513240383401f070c028340464001050821024045400d208111024044400910810a04404340060881403980000502403540041420 420 0x43528a40ed8e435db540e28a43418640e40e43443440e18633218630acca332cf230a1864300c340ec4e430c7040e0ce32f0c330a00a32f02f30a0ca22d0c3206b8622dbad2060c640e98e411b1140eb0e41199130a98a30dacd30aaca30d98d2069862098c92068c62099a69e99a6943a839e9aa99439834d88e34e09a64d89a64e08e35e79a6956a289e7a289569a69e78e39649a69e79a69648e342262240e40e42242240e60e32161830a30a32132130a60a2096092068062098092066064de6184c34c34de7de4c36034dd5dc41159140e40e41141140e58e30d58d30a64a30d64d30a58a21b59b20620621b21b2065860836435c05806835835c06404d84d84d75964d34d54d44d24113d140e40e41141140e3ce30d2cd30a30a30d30d30a2ca2091c92062062092092061c6083043140140143103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x9 : Ex 127 10 [v223,u1,u2,u0,u3,u4,u5,u6] :=
  certify c127 [] (unpack 6 0x3040302029121a2419122440240814080d120c8920c010a0068c058308900386224022041a3013060a100a040689070613240381070c028121024047400d20811102404f400910810983404e40060881400505024004142040030992404d40000284401f404503834001404c0508 420 0x6754d3657d97675db56574d36743cf6576576746746573cf5723cf553cd3572cf25533cf67034d657c57670c7065735756f34d5532d356f2ef55335346d34d44fb8f46dbad44f34f65719765ab1a657b1765a19a553193556ad6553ad355619644f18f461a2144fa0f4611862a918620da8d2a9aa920d18d09ba1b0a218609b19b0a2a2814518621c9e714a9e721c1866656db6579976659a56576db5636db5539135639235536db4616db44f88f4618a144f6db09f6db08d80d09f81f08d6db65a71a65765765a65a65771755671655379355679655371345271244f44f45245244f70f14d78d14b70b14d70d14b78b08209d08571c09b09b65a61a65765765a65a65761755651655355355655655351345241244f44f45245244f40f14d30d14b14b14d38d14b30b2091c91461461492892061c6085103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x10 : Ex 127 9 [v177,u1,u3,u0,u4,u5,u6] :=
  certify c127 [] (unpack 6 0x3040302029121a24191220c010a0068c4015038640350284405708902408140824401c300c89210211022140193009830508070c0383401f112022402204405620811a3013064055108140540a100a04405308814052050206890706400414200281 336 0x46f30c450c1046fc2f45030c2ee1c72104502ee46e2101c72ec1c720cb4c2ecb6c20c1c745095045dadd450ad045d95d34c94c35ca9c34ca8c35c95c2079472c98c92c78c7209965082965081a410a8a690819655559655549d45689e75549659808c090a96598094090a8e30a20620908100a28220900500a182108c04c0a106108c80c21e0410877c709e7de20704755d51d5506d055d6dd55051055c6dc54c50c55c51c54c6cc2195145476875596992075070835140815c10835c30815141965185405c05565d65405004520004504d04524d245000034e00034c3cc34e3ce34c0002090002c72872c9289207000083000181105083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x11 : Ex 127 8 [v15,v113,u0,u2,u4,u6] :=
  certify c127 [] (unpack 6 0x29121a240d12224022041a3007061324038320c00a04028140350a10089010a040150386400502843040302021024056208119300983405a088111200502405521401081 240 0x2a11452892892a12a128914509f14508080009f81f08014529d59628978929d79d28959619759618550519751718559609b59608070009b71b08059655a59654464455a65954459628938928b60b28960928b38b1853851974d71854c519738e5564d655438e5563965544d30803800834830804800833833cf38e3c44043d14103c438e28c00028934928c34c28900028b10b28904928b04b289109187104185205187207185105083043080100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x12 : Ex 127 9 [v113,u1,u3,u0,u2,u4,u6] :=
  certify c127 [⟨_,p127x11⟩] (unpack 6 0x29121a24191222402204162406891a30130620c0405a0a0440350a100890068c4015038610a04055028424081c300c89050214082440210219300983405b0881132403830281400480001420401f112011024059214030403020405620811081 336 0xaf4104410810af0af44141072d410440b8072dbad4404100ab34d081b010abb2b08134d46434d9508909648a445034d32a34d30aa4a32aa6930a34d72734d700a00727a2770034d0816c10949940819810946d44506d09648649508504646db8cd84d8e26db8cd6cd8e286130c6db30a80a31f82030a6db2496db24878825f79e2486db7006c07077477007407076c731a29a30154131a55a30128145828a3106503186584502901965573002801962961805402542142411412541542412014522082504d02524d245021024e20824d3cd24e3ce24d20d30c20830a30a30930b18a208187147240200187207180140083000081101083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x13 : Ex 127 8 [v15,v178,u0,u2,u4,u5] :=
  certify c127 [] (unpack 6 0x304030201a2419120d121a301306224022041324038310a00a04028140350a10089020c0401503864005028411024055108119300983405a088121400502405611202081 240 0xa02490808400a086008024929e1452897c929e7de28914509d14508008009d09d08014529b51428970929b71b2895141955141854851954951855140995140806800996990805144d85144c15c14d85d74c151428930928b58b28958928b30b18530519545518544519530c4d44544d230c4d43144d245108030008340308040008330334d30c34138134f38e34130c28b10b28904928b04b289109187041185205187207185045083043080100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x14 : Ex 127 9 [v178,u1,u3,u0,u2,u4,u5] :=
  certify c127 [⟨_,p127x13⟩] (unpack 6 0x304030201a24191229121a301306162406892240220410a04055405a0a0440350a100890068c4015038620c04056028414081c300c8905022440240811021081193009830881132403830281400480001420401f21402102405c11202081 336 0x62d3cf600b8062dbad6003cf8ab30c88fb0f8abb2b88f30c62a30c60060062a62a60030c8a824988fa4f8a8a6888f24986024984c78c8607a084c2492272492069862279a620624962424960094062496460024988f5cf8908d088f8cf8905d084c5cc86076084c74c8605d77c97497de5d77c95c97de75d2085d720670621b71c2065d71455d714168115b69a1415d76005c06036436006406035c321649620f18f21619620f48f21418620c54c21455420c18c09119320048009149108018015011014f04f15005014f10f14d04114c38c14d38d14c04c14a0411492c914a2ca149049208041206206205207086041083043140100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x15 : Ex 127 9 [v15,v115,u0,u2,u4,u5,u6] :=
  certify c127 [⟨_,p127x11⟩,⟨_,p127x13⟩] (unpack 6 0x3040302029121a241912224022041a3013061324038320c010a00a0440350a1008900583401503860284800180000d12070605020281400440050500210240562081110240552140108119300983405a11200881 324 0x2a8145289a492a8a682891452a70002892892a72a72890001e50001c59851e59a51c50002a33cf2899092a39232893cf1e13cf1c58851e18a11c53cf09c3cf08068009c69c0803cf6e03cf6c17c16e07df6c13cf28954928b78b28978928b54b1c55451c87481c57451c854808054009c65c08064009c5556cf64f6da5556cf54f6da65939855539039039839839055034d55534158135759634155538e41038938938e29438940938e41038538538e1d338540538e41038048038e49238040038e41038f44f38e45138f40f38e34c28b04b28918928b18b2890491c81881c50451c80481c5185083041080100083103080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x16 : Ex 127 9 [v116,u1,u3,u2,u4,u5,u6] :=
  certify c127 [] (unpack 6 0x3040302029121a241912224022041a301306162406892408140824401c300c8921401930098313240383050805890386401f112020c020814056210210a0108140551102405f0881405e0a044035028140570a100890405d0502068c0583400414200284 336 0x570492556c56570c705564923ef38e3565563ef56f35638e3ed38e352b923edbad35238e56b28a556b1656bb2b55628a46928a452a92469aa945228a34c28a3ce20e3cc20c34e28a0a828a0819c10a89e708128a0a60660969160a69260960560a59250920520a506509291236204108e8ce0a28e234e04e65461465685665485465661665085065261265061065285235f61864e80e65f81f34e60e65d61864a78a65d79d64a60a0836180816c10836c308161819a61c6406c065a6da6406005560165545d45565d65540144520124504d04524d245001034e00e3cc1cc3ce1ce34c00024a1ca2c80002ca00a2481c7083005181105083103081000) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x17 : Ex 127 10 [v115,u1,u3,u0,u2,u4,u5,u6] :=
  certify c127 [⟨_,p127x10⟩,⟨_,p127x12⟩,⟨_,p127x14⟩,⟨_,p127x15⟩,⟨_,p127x16⟩] (unpack 6 0x3040302029121a241912224022041a3013061624068920c010a00a0440570a100890068c038640158004405d400002842408140824401c300c89210211022140193009831324038311201420401f80038002405c400d2081800140594009108140084058400608814035800040524001028140510502400440500508 420 0x53c38e512f5253cf7c51238e53b28a51251253b53b51228a43928a40ee8e439eb940e28a537145512e12537e3751214543514540ed8e435db540e14533014530ab8a330bb030a1450b41451d8cd80b4cf31d8145512992520ca0512c925209a040e98e41fc5f40ec4e41f99f30a98a330b7030ab4a3309a61c5b45a2e9a6bc59851eeb6d0829a6a18b180aab2ca189a65d79a6a19ad95eaaeba199a60829a6a270a70aa0a9a279a65256255128d25258e55126124248e440e60e42462440e8ce32161830a88a3218a130a60a5206605127925207a051265241f79f40e64e41f65f40e78e31c65930a74a31c75c30a64a1da6595c56c55da6da1c56450826590980980970965144d35125125025155124d24103cf40e40e40241140e3ce30c2cb30a30a30230d30a2ca1c21860850850822481c5185082103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x18 : Ex 127 10 [v15,u1,u3,u0,u2,u4,u5,u6] :=
  certify c127 [⟨_,p127x15⟩,⟨_,p127x0⟩,⟨_,p127x6⟩] (unpack 6 0x3040302029121a241912224022041a3013064035068907068002400120c010a00a0440180a100890068c0583058980010386401440000284240814080d120c89405014200d184005070c0383403d028105020508401f800040514004112021024062400d208111024061400910810983406040060881 420 0x2b9104288e882b9eb92881042b80002882882b82b82880001b6000184dc41b6df61840002b44d3288d482b4d742884d31b24d3184cc41b2cf21844d30aa4d3080a000aaa2a0804d336f4d3512c12c6fc2f5124d35d74d352d5555ee55552d4d32887c828bb0b288b0828b7cb1847c4187ac7184ac41877c70807c00aa9ea0809c00aa7df5139d38687dfa537d35289e73657df8529925e59a58527d24247df8518915e48a28517df5d77df8608a25e38a28607df29e49228828829e29e28848819d49218418419d19d18448409b49208070009b71b08048041a41928b44b28828828b28b2884481874471841841871871844440834510806000836030804405154514135935d559551345335235241045135034f34e34c28b24b28828828b28b288248187147184184187187184144083043080080083083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x19 : Ex 127 10 [v117,u1,u3,u0,u2,u4,u5,u6] :=
  certify c127 [] (unpack 6 0x3040302029121a241912224022041a30130640351624068920c010a00a0440650a1008904005068c05892408140824401c300c890d18070c05000508142021024050400d20811102406440091081098340634006088140390383403a4001028140100386401140000284401f406205024004405c1120 420 0x6b9514698e986b9eb96985146b84106986986b86b86984105b6410594dd45b6df65944106b42cb698d586b4d746982cb5b22cb594cd45b2cf25942cb4ac2cb490a904acaac4902cb0b02cb35cbdcc70bef35c2cb69819869bb9b698b9869b19b594194597b57594b545971974901904aca6c490a504ac18634ba4b22a186acb18b36aa690a818621c9dca0a9e721c18616618621d25d16624921d1866a57256988d86a58e56987185a48e45947145a47245948d44a171c4908904a18a149071069b75b69869869b69b69875859775759459459759759475449375d49081049381349075034e75d14b7cb14e7ce34b74b08509e14575d09c09c69b65b69869869b69b69865859755759459459759759455449345349049049349349045034e30e14b14b14e3ce34b30b2091c91461461492892061c6145103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x20 : Ex 127 10 [v118,u1,u3,u0,u2,u4,u5,u6] :=
  certify c127 [] (unpack 6 0x3040302029121a241912224022041a301306070620c010a00a0440680a1008900583400503860d122102110221401930098313240383401f05000502112024084051400d208114084067400910810c8940664006088140350689403c400102814015068c401640000284405c1420400440620508 420 0x6784d3657e57678e786574d36773cf6576576776776573cf5753cf553d93575db55533cf67328a657d17673d3365728a57128a553c93571cb155328a46d28a44facf46daed44f28a0b028a31c35c0b037031c28a657157665be5657bd7665165553153564ba4553b9356416444f14f46daad44fa8f46d14530aa8a1eb145b0a14a32baaa0a91451dc21c0a92291dc15c7a81451db9dba099e71db14565a71c65765765a65a65771755671c55355355655655371345271c44f98f45299244f70f6656e56578d76658e56576d75648e45536d35646e45538d34616db44f88f4618a144f6cf31f6db78a80a39f81f30a6ca09e09d09c09c0826db65a61a65765765a65a65761755651655355355655655351345241244f44f45245244f40f30d2cd08a08a08d38d30a2ca1c81880850850882481c5185082103082040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x21 : Ex 127 10 [v94,u2,u3,u0,u1,u4,u5,u6] :=
  certify c127 [⟨_,p127x6⟩,⟨_,p127x7⟩] (unpack 6 0x3040302029121a24191221400d1809838001070c80004035401f112020c0210210a01102058903860508068c40030284406e40000890240816240c89406d050213060e180706068904854001406c400402812204406b400d20811408406a400910810a04406940060881 420 0x2b3104288d082b3d332881042b20002882882b22b22880001b0000184c441b0c701840002a5825288bc82a5be52888081a38231849c41a39e31848040ad820080b800adbad0808003529e7a58820a528203589e73cf8203d1ad13ecaeb3d1820a699e7a68820a6a820a689e72887482a59a52889882a57651847441a39231849041a376308074008368308068008375d7a275d7208607a286172075d35e75d7127d279e7df71275d3d169a3d375d3d175d3d369a79e69a71b75d79e75d71b69a2994992882882992992884881874871846041876071844840974920800800970970804803d63d528b44b28828828b28b2884481944541841841941941844440834430804c00834c30804403d23523cf4513cf3d03ce34c28b24b28828828b28b288248187147184184187187184144083043080080083083080040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x22 : Ex 127 10 [v224,u2,u3,u0,u1,u4,u5,u6] :=
  certify c127 [] (unpack 6 0x3040302029121a24191221400d180983070c038320c0210210a0110205890386068c08901624224022041a3013060a100a040681070602812408406c400d208114084072400910810c89407140060881401f40050508112040030c98407040000284406f050240014004406b0689 420 0x6754d3657d97675db56574d36743cf6576576746746573cf5723cf553cd3572cf25533cf66b32b657c5766bc6b6573175693295532d35692e955331346f30c44fc0f46fc2f44f30f09c2cb0a430c09c30c0a42cb0ed30c0dbb9b0edbad0db31b65719766bb2b657b1766b1ab553193569aa9553a935691a944f18f45e95e44f94f45e1862a818620c9cc2a89e720c18608218621c99c08a9a621c1860db95b0df1860db19b0df96565a71a65765765a65a65771755671655391355691655371345271c44f44f45245244f70f6626db6578d76628e26576db5606db5538535608605536db45e6db44f7cf45e7de44f6db0c30dd0dc09c0c36db65a61a65765765a65a65761755651655355355655655351345241244f44f45245244f40f08c38c08b08b08c34c08b08b2091c90860860892892061c60c31440c2040) (by decide +kernel)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem p127x23 : Ex 127 11 (roots 127) :=
  certify c127 [⟨_,p127x2⟩,⟨_,p127x3⟩,⟨_,p127x4⟩,⟨_,p127x5⟩,⟨_,p127x8⟩,⟨_,p127x9⟩,⟨_,p127x17⟩,⟨_,p127x18⟩,⟨_,p127x19⟩,⟨_,p127x20⟩,⟨_,p127x21⟩,⟨_,p127x22⟩] (unpack 6 0x3040302029121a2419122440240814080d120c89224022041a301306800b800a0689070621400d18098380098008800780061420112080058004070c038320c02081400d210210a0108140091102088140060a0480038002068c058305024003028140010a1008908001800005890386400005080284 336 0x67959665ae9a679eb965a5966784d365a65a67867865a4d35764d3556dd6576df65564d367430c65ad5a674d7465a31a57330c5568565738735563164b130c493c934b1cb149331366f28a65ac1a66fc2f65a28a56d28a556b9656dbad55628a49128a49321349121149328ab2928a24ca8cae9aa924c28a65805865aa1a658a1865a05a5540545568165548145560564a60414939d34a69e649305394c80c9210418cc04c8a182025c0417ca74a79c75c24a04a65a01a6586d865a6da6580185560165545d45565d65540144930134911d14931d349100040d00008c38c3cd38d08c00c24a1ca0880002ca00a2481c71840000810c11440c3081000) (by decide +kernel)
theorem l127 : Claim 127 12 := fromSearch 4146 (by decide +kernel) p127x23

open PEqualNP.CircuitLowerBounds

def graph : Sig := goalAt 127
theorem graph_proper : proper graph := by unfold proper; decide +kernel

def edgeList : List Nat := [0,2,1,3,0,4,2,4,0,5,1,5,3,5,0,6,1,6,2,6,3,6,5,6]
def target (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < edgeList.length / 2,
    (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
    (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)

def smallCircuit : Circuit := ⟨[
  ⟨.or,[0,1]⟩,
  ⟨.or,[0,2]⟩,
  ⟨.and,[1,3]⟩,
  ⟨.or,[2,5]⟩,
  ⟨.or,[0,6]⟩,
  ⟨.or,[5,6]⟩,
  ⟨.or,[3,7]⟩,
  ⟨.and,[4,8]⟩,
  ⟨.and,[10,11]⟩,
  ⟨.or,[9,12]⟩,
  ⟨.or,[14,15]⟩,
  ⟨.and,[13,16]⟩,
  ⟨.or,[17,18]⟩],19⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 13 := rfl

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

def lowRow (i : Fin 7) : Row := Fin.ofNat 128 (1 <<< ([2,3,0,1,0,0,0] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 128 ((1 <<< i.val) ||| (1 <<< ([2,3,0,1,0,0,0] : List Nat).getD i.val 0))

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
    (lower : Impossible true graph 11 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
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

end PEqualNP.Outside.L_meta_10694

open PEqualNP.Outside.L_meta_10694 in
theorem PEqualNP.Outside.L_meta_10694 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort p127x23 gates o fit correct
