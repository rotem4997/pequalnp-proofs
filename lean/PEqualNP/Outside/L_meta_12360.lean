import PEqualNP.Defs

-- The live-set and restriction lemmas follow L-meta-10554, L-meta-10802, L-meta-1674, L-meta-670 and L-meta-1667.
namespace PEqualNP.Outside.L_meta_12360
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


-- Natural-number words, and a search table checked level by level.
def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (o : Nat) : ∃ e, e < 4 ∧ ∀ a b, bin o a b = bin e a b := by
  by_cases h : o < 4
  · exact ⟨o,h,fun _ _ => rfl⟩
  · refine ⟨3,by omega,fun a b => ?_⟩
    have h0 : o ≠ 0 := by omega
    have h1 : o ≠ 1 := by omega
    have h2 : o ≠ 2 := by omega
    simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
theorem W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (R : List Nat) (T L : Nat) : Prop := Lower true (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice true (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

abbrev BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^128 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧ (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
theorem BaseP.lt {T R} (h : BaseP T R) : T < 2^128 := h.1
theorem BaseP.plain {T R} (h : BaseP T R) : plainWord (W T) = true := h.2.1
theorem BaseP.nodup {T R} (h : BaseP T R) : (rootsW R).Nodup := h.2.2.1
theorem BaseP.plainR {T R} (h : BaseP T R) : (rootsW R).all plainWord = true := h.2.2.2.1
theorem BaseP.ess {T R} (h : BaseP T R) : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := h.2.2.2.2.1
theorem BaseP.prop {T R} (h : BaseP T R) : proper (W T) := h.2.2.2.2.2

theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

theorem lowOf {T R E K} (hB : baseOK T R E = true) (h : Impossible true (W T) K (rootsW R).toFinset) :
    LowN R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

theorem mkSlice {R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def av (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || Nat.beq x (Nat.xor d m))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available true bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS f bank P)
    (h : av d P v = true) : Available true bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | h⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv rfl e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {f : Row → Row} {roots bank p P} (o a b : Nat) (hr : Reach true roots p bank) (hP : PS f bank P)
    (ha : Available true bank (RF f a)) (hb : Available true bank (RF f b)) :
    ∃ next, Reach true roots (p+1) next ∧ PS f next P ∧ Available true next (RF f (nb o a b)) ∧
      ∀ v, Available true bank v → Available true next v := by
  obtain ⟨e,he,heq⟩ := bin_four o
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) (Or.inr ⟨rfl,he⟩) ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {f : Row → Row} {bank P} (hP : PS f bank P) (i : Nat) : Available true bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach true roots p bank)
    (hP : PS f bank P) : ∃ next, Reach true roots (p+cs.length) next ∧ PS f next (mkPool P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
    have : PS f next (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h2 v hv
      · rw [List.mem_singleton.mp hv]
        exact h3
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av c.1 c.2.2.2) && keepB c.1 c.2.2.2 ka a && keepB c.1 c.2.2.2 kb b &&
  (bif av c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av c.1 c.2.2.2 a && av c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def sepEval (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  let e := fun v => (Nat.testBit v p.1 == Nat.testBit v p.2)
  e z && (!ka || e a) && (!kb || e b) && rest.all e
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && (T.testBit p.1 != T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach true (roots.map observe) c.2.2.1 bank ∧ PS f bank c.2.2.2 ∧
    ∀ p bank, Reach true (roots.map observe) p bank → Available true bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {R T c k rest a b o ka kb} (hc : CutP R T c)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval k rest a b (nb o a b) ka kb c = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach true (roots.map observe) q bank' ∧ PS f bank' c.2.2.2 ∧ Available true bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply true bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available true bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

theorem sep_sound {T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval rest a b (nb o a b) ka kb p = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,bne_iff_ne] at hT
  obtain ⟨⟨p1,p2⟩,hd⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  intro k' _ run
  obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W]; exact hd)
  apply hne
  rw [List.mem_toFinset] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · rw [bit_W,bit_W]; exact h1
  rcases mem_kept hv with rfl | hv'
  · cases ka
    · cases kb
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx
      · rcases List.mem_cons.mp hv with e | hv
        · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
        · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
          rw [←e,bit_W,bit_W]; exact h4 x hx
    · rw [bit_W,bit_W]; exact h2.resolve_left (by simp)
  · cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv'
      rw [←e,bit_W,bit_W]; exact h4 x hx
    · rcases List.mem_cons.mp hv' with e | hv
      · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx

abbrev StD := List Nat × List Nat × List Nat × List (List Nat)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool (initPool s.1 s.2.2) c.2)
def hintOK (k : Nat) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 100 then (match cuts[i]? with
    | some c => cutEval k rest a b z ka kb c
    | none => false)
  else (match seps[i-100]? with
    | some q => sepEval rest a b z ka kb q
    | none => false)
def kidOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK k cuts seps rest a b z kk.1 kk.2) ||
  next.any (beqL (kidN rest a b z kk.1 kk.2))
def pairOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  [0,1,2,3].all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK k next cuts seps p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (T : Nat) (K : List CutV) (P : List (Nat × Nat)) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK k next (st.2.1.filterMap fun i => K[i]?) (st.2.2.1.filterMap fun i => P[i]?) st.1) (pairs st.1) st.2.2.2
def levelOK (T : Nat) (K : List CutV) (P : List (Nat × Nat)) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK T K P k next)
def LevelN (R : List Nat) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible true (W T) k (st.1.map W).toFinset
theorem cutsGood {R T} {Z : List SliceD} {C : List (Nat × List (Nat × Nat × Nat))} (hZ : ∀ s ∈ Z, SliceN R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut Z), CutP R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=true) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

theorem stStep {R T E K P k next st} (hB : baseOK T R E = true) (hK : ∀ c ∈ K, CutP R T c) (hP : P.all (sepOK T) = true)
    (hn : ∀ s ∈ next, Impossible true (W T) k (s.map W).toFinset)
    (h : stOK T K P k next st = true) : Impossible true (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨ha,hT⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  have good : ∀ c ∈ st.2.1.filterMap (fun i => K[i]?), CutP R T c := by
    intro c hc
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hc
    exact hK c (List.mem_of_getElem? hi)
  have hs : ∀ q ∈ st.2.2.1.filterMap (fun i => P[i]?), sepOK T q = true := by
    intro q hq
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hq
    exact List.all_eq_true.mp hP q (List.mem_of_getElem? hi)
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have hd4 : d < 4 := by
    rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp
  -- one unordered pair serves both orders
  have core : ∀ (o : Nat) (ja jb : Bool), o < 4 → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible true (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (by
      have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      simpa using this)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with (hk | hk) | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      cases hb : Nat.blt i 100
      · rw [hb,cond_false] at hi
        cases hg : (st.2.2.1.filterMap (fun i => P[i]?))[i-100]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact sep_sound (hs q (List.mem_of_getElem? hg)) hi
      · rw [hb,cond_true] at hi
        cases hg : (st.2.1.filterMap (fun i => K[i]?))[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (good q (List.mem_of_getElem? hg)) nk hi
    · obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hk
      rw [←kid_fin]
      rw [beqL_ok e]
      exact hn s hs'
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd4 (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have f4 : flipOp d < 4 := by
      rcases hfl.1 with h | ⟨_,h⟩ <;> omega
    have r := core (flipOp d) kb ka f4 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {R T E K P k D' D} (hB : baseOK T R E = true) (hK : ∀ c ∈ K, CutP R T c) (hP : P.all (sepOK T) = true)
    (hI : LevelN R T k D') (h : levelOK T K P k (D'.map Prod.fst) D = true) : LevelN R T (k+1) D := by
  intro st hst
  refine stStep hB hK hP ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {T : Nat} {K : List CutV} {P : List (Nat × Nat)} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK T K P k next ((D.drop (i*c)).take c) = true) : levelOK T K P k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {R T E K D} (hB : baseOK T R E = true) (hI : LevelN R T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this


def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124160 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[
    ⟨.and, [0, 1]⟩,
    ⟨.and, [6, 2]⟩,
    ⟨.and, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [11, 2]⟩,
    ⟨.and, [10, 9]⟩,
    ⟨.or, [13, 5]⟩,
    ⟨.and, [12, 14]⟩,
    ⟨.or, [10, 9]⟩,
    ⟨.and, [15, 16]⟩], 17⟩
theorem witnessMonotone : PEqualNP.MetaComplexity.Monotone2 smallCircuit := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel
theorem witnessSize : smallCircuit.size = 12 := rfl
def w0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def w1 : Nat := 0xcccccccccccccccccccccccccccccccc
def w2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def w3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
def w4 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def w5 : Nat := 0xfafafafafafafafafafafafafafafafa
def w6 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def w7 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def w8 : Nat := 0xffccffccffccffccffccffccffccffcc
def w9 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def w10 : Nat := 0xfefefefefefefefefefefefefefefefe
def w11 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
def w12 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffee
def w13 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee
def w14 : Nat := 0x32323232323232323232323232323232
def w15 : Nat := 0xfffafffafffafffafffafffafffafffa
def w16 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa
def w17 : Nat := 0x33223322332233223322332233223322
def w18 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
def w19 : Nat := 0x54545454545454545454545454545454
def w20 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffc
def w21 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc
def w22 : Nat := 0x55445544554455445544554455445544
def w23 : Nat := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c
def w24 : Nat := 0x55505550555055505550555055505550
def w25 : Nat := 0x33303330333033303330333033303330
def w26 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe
def w27 : Nat := 0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e
def w28 : Nat := 0x33323332333233323332333233323332
def w29 : Nat := 0x55545554555455545554555455545554
def w30 : Nat := 0xffff0000ffff0000ffff0000ffff0000
def w31 : Nat := 0x88888888888888888888888888888888
def w32 : Nat := 0x22222222222222222222222222222222
def w33 : Nat := 0x44444444444444444444444444444444
def w34 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def w35 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def w36 : Nat := 0x50505050505050505050505050505050
def w37 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00
def w38 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa
def w39 : Nat := 0x55005500550055005500550055005500
def w40 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
def w41 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def w42 : Nat := 0x30303030303030303030303030303030
def w43 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00
def w44 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc
def w45 : Nat := 0x33003300330033003300330033003300
def w46 : Nat := 0xf000f000f000f000f000f000f000f000
def w47 : Nat := 0xf000f000f000f000f000f000f000f0
def w48 : Nat := 0xf000f000f000f000f000f000f000f00
def w49 : Nat := 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8
def w50 : Nat := 0x70707070707070707070707070707070
def w51 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88
def w52 : Nat := 0x77007700770077007700770077007700
def w53 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0
def w54 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee00
def w55 : Nat := 0xecececececececececececececececec
def w56 : Nat := 0x4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c
def w57 : Nat := 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0
def w58 : Nat := 0x5f005f005f005f005f005f005f005f00
def w59 : Nat := 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8
def w60 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa00
def w61 : Nat := 0xeecceecceecceecceecceecceecceecc
def w62 : Nat := 0x44cc44cc44cc44cc44cc44cc44cc44cc
def w63 : Nat := 0xfaf0faf0faf0faf0faf0faf0faf0faf0
def w64 : Nat := 0x50f050f050f050f050f050f050f050f0
def w65 : Nat := 0xcc88cc88cc88cc88cc88cc88cc88cc88
def w66 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0
def w67 : Nat := 0xff0cff0cff0cff0cff0cff0cff0cff0c
def w68 : Nat := 0xf300f300f300f300f300f300f300f300
def w69 : Nat := 0xff30ff30ff30ff30ff30ff30ff30ff30
def w70 : Nat := 0xcf00cf00cf00cf00cf00cf00cf00cf00
def w71 : Nat := 0xf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fc
def w72 : Nat := 0xf030f030f030f030f030f030f030f030
def w73 : Nat := 0xf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0
def w74 : Nat := 0xc0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0
def w75 : Nat := 0xccfcccfcccfcccfcccfcccfcccfcccfc
def w76 : Nat := 0xcc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0c
def w77 : Nat := 0xcfcccfcccfcccfcccfcccfcccfcccfcc
def w78 : Nat := 0xc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0cc
def w79 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000
def w80 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
def w81 : Nat := 0xcccc0000cccc0000cccc0000cccc0000
def w82 : Nat := 0xcccc0000cccc0000cccc0000cccc
def w83 : Nat := 0xf0f00000f0f00000f0f00000f0f00000
def w84 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0
def w85 : Nat := 0xf0f00000f0f00000f0f00000f0f0
def w86 : Nat := 0xf0f00000f0f00000f0f00000f0f0000
def w87 : Nat := 0xff000000ff000000ff000000ff000000
def w88 : Nat := 0xffffff00ffffff00ffffff00ffffff00
def w89 : Nat := 0xff000000ff000000ff000000ff00
def w90 : Nat := 0xff000000ff000000ff000000ff0000
def w91 : Nat := 0x80808080808080808080808080808080
def w92 : Nat := 0x8080808080808080808080808080808
def w93 : Nat := 0x88008800880088008800880088008800
def w94 : Nat := 0x880088008800880088008800880088
def w95 : Nat := 0x88880000888800008888000088880000
def w96 : Nat := 0xffff8888ffff8888ffff8888ffff8888
def w97 : Nat := 0x8888000088880000888800008888
def w98 : Nat := 0x77770000777700007777000077770000
def w99 : Nat := 0xa000a000a000a000a000a000a000a000
def w100 : Nat := 0xa0a00000a0a00000a0a00000a0a00000
def w101 : Nat := 0x5f5f00005f5f00005f5f00005f5f0000
def w102 : Nat := 0xc4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4
def w103 : Nat := 0xaa000000aa000000aa000000aa000000
def w104 : Nat := 0x55ff000055ff000055ff000055ff0000
def w105 : Nat := 0xcc44cc44cc44cc44cc44cc44cc44cc44
def w106 : Nat := 0x4444cccc4444cccc4444cccc4444cccc
def w107 : Nat := 0x5050f0f05050f0f05050f0f05050f0f0
def w108 : Nat := 0x5500ff005500ff005500ff005500ff00
def w109 : Nat := 0xcccc4444cccc4444cccc4444cccc4444
def w110 : Nat := 0x2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a
def w111 : Nat := 0xc000c000c000c000c000c000c000c000
def w112 : Nat := 0x3f003f003f003f003f003f003f003f00
def w113 : Nat := 0xc0c00000c0c00000c0c00000c0c00000
def w114 : Nat := 0x3f3f00003f3f00003f3f00003f3f0000
def w115 : Nat := 0xa2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2
def w116 : Nat := 0x22aa22aa22aa22aa22aa22aa22aa22aa
def w117 : Nat := 0x30f030f030f030f030f030f030f030f0
def w118 : Nat := 0xcc000000cc000000cc000000cc000000
def w119 : Nat := 0x33ff000033ff000033ff000033ff0000
def w120 : Nat := 0xaa22aa22aa22aa22aa22aa22aa22aa22
def w121 : Nat := 0x2222aaaa2222aaaa2222aaaa2222aaaa
def w122 : Nat := 0x3030f0f03030f0f03030f0f03030f0f0
def w123 : Nat := 0x3300ff003300ff003300ff003300ff00
def w124 : Nat := 0xaaaa2222aaaa2222aaaa2222aaaa2222
def w125 : Nat := 0xf0000000f0000000f0000000f0000000
def w126 : Nat := 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0
def w127 : Nat := 0xccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0
def w128 : Nat := 0xaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0a
def w129 : Nat := 0xffff00f0ffff00f0ffff00f0ffff00f0
def w130 : Nat := 0xff0f0000ff0f0000ff0f0000ff0f0000
def w131 : Nat := 0xa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aa
def w132 : Nat := 0xffff0f00ffff0f00ffff0f00ffff0f00
def w133 : Nat := 0xf0ff0000f0ff0000f0ff0000f0ff0000
def w134 : Nat := 0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0
def w135 : Nat := 0xccccc0c0ccccc0c0ccccc0c0ccccc0c0
def w136 : Nat := 0xaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0a
def w137 : Nat := 0xcccc0c0ccccc0c0ccccc0c0ccccc0c0c
def w138 : Nat := 0xff00fff0ff00fff0ff00fff0ff00fff0
def w139 : Nat := 0xff000f00ff000f00ff000f00ff000f00
def w140 : Nat := 0xa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaa
def w141 : Nat := 0xc0c0ccccc0c0ccccc0c0ccccc0c0cccc
def w142 : Nat := 0xff0fff00ff0fff00ff0fff00ff0fff00
def w143 : Nat := 0xf000ff00f000ff00f000ff00f000ff00
def w144 : Nat := 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00
def w145 : Nat := 0xcccccc00cccccc00cccccc00cccccc00
def w146 : Nat := 0xaaaa00aaaaaa00aaaaaa00aaaaaa00aa
def w147 : Nat := 0xcccc00cccccc00cccccc00cccccc00cc
def w148 : Nat := 0xf0f0fff0f0f0fff0f0f0fff0f0f0fff0
def w149 : Nat := 0xf0f000f0f0f000f0f0f000f0f0f000f0
def w150 : Nat := 0xaa00aaaaaa00aaaaaa00aaaaaa00aaaa
def w151 : Nat := 0xcc00cccccc00cccccc00cccccc00cccc
def w152 : Nat := 0xf0fff0f0f0fff0f0f0fff0f0f0fff0f0
def w153 : Nat := 0xf000f0f0f000f0f0f000f0f0f000f0f0
def w154 : Nat := 0xff80ff80ff80ff80ff80ff80ff80ff80
def w155 : Nat := 0x7f007f007f007f007f007f007f007f00
def w156 : Nat := 0xffff8080ffff8080ffff8080ffff8080
def w157 : Nat := 0x7f7f00007f7f00007f7f00007f7f0000
def w158 : Nat := 0x80008000800080008000800080008000
def w159 : Nat := 0x80800000808000008080000080800000
def w160 : Nat := 0xf800f800f800f800f800f800f800f800
def w161 : Nat := 0xf800f800f800f800f800f800f800f8
def w162 : Nat := 0xf8f80000f8f80000f8f80000f8f80000
def w163 : Nat := 0xf8f80000f8f80000f8f80000f8f8
def w164 : Nat := 0x70007000700070007000700070007000
def w165 : Nat := 0x8f008f008f008f008f008f008f008f00
def w166 : Nat := 0x70700000707000007070000070700000
def w167 : Nat := 0x8f8f00008f8f00008f8f00008f8f0000
def w168 : Nat := 0xf8f0f8f0f8f0f8f0f8f0f8f0f8f0f8f0
def w169 : Nat := 0x70f070f070f070f070f070f070f070f0
def w170 : Nat := 0xffff8800ffff8800ffff8800ffff8800
def w171 : Nat := 0x77ff000077ff000077ff000077ff0000
def w172 : Nat := 0x88000000880000008800000088000000
def w173 : Nat := 0xf080f080f080f080f080f080f080f080
def w174 : Nat := 0xf080f080f080f080f080f080f080f08
def w175 : Nat := 0xff880000ff880000ff880000ff880000
def w176 : Nat := 0xff880000ff880000ff880000ff88
def w177 : Nat := 0x80f080f080f080f080f080f080f080f0
def w178 : Nat := 0x77000000770000007700000077000000
def w179 : Nat := 0x88ff000088ff000088ff000088ff0000
def w180 : Nat := 0xf8f8f0f0f8f8f0f0f8f8f0f0f8f8f0f0
def w181 : Nat := 0x7070f0f07070f0f07070f0f07070f0f0
def w182 : Nat := 0xff88ff00ff88ff00ff88ff00ff88ff00
def w183 : Nat := 0x7700ff007700ff007700ff007700ff00
def w184 : Nat := 0xf0f08080f0f08080f0f08080f0f08080
def w185 : Nat := 0xf0f08080f0f08080f0f08080f0f0808
def w186 : Nat := 0xff008800ff008800ff008800ff008800
def w187 : Nat := 0xff008800ff008800ff008800ff0088
def w188 : Nat := 0x8080f0f08080f0f08080f0f08080f0f0
def w189 : Nat := 0x8800ff008800ff008800ff008800ff00
def w190 : Nat := 0x88808880888088808880888088808880
def w191 : Nat := 0x77707770777077707770777077707770
def w192 : Nat := 0x88f888f888f888f888f888f888f888f8
def w193 : Nat := 0x88088808880888088808880888088808
def w194 : Nat := 0x8f888f888f888f888f888f888f888f88
def w195 : Nat := 0x80888088808880888088808880888088
def w196 : Nat := 0x88888080888880808888808088888080
def w197 : Nat := 0x77777070777770707777707077777070
def w198 : Nat := 0x8888f8f88888f8f88888f8f88888f8f8
def w199 : Nat := 0x88880808888808088888080888880808
def w200 : Nat := 0x8f8f88888f8f88888f8f88888f8f8888
def w201 : Nat := 0x80808888808088888080888880808888
def w202 : Nat := 0x88888800888888008888880088888800
def w203 : Nat := 0x77777700777777007777770077777700
def w204 : Nat := 0x8888ff888888ff888888ff888888ff88
def w205 : Nat := 0x88880088888800888888008888880088
def w206 : Nat := 0x88ff888888ff888888ff888888ff8888
def w207 : Nat := 0x88008888880088888800888888008888
def w208 : Nat := 0x4c004c004c004c004c004c004c004c00
def w209 : Nat := 0xb300b300b300b300b300b300b300b300
def w210 : Nat := 0x4c4c00004c4c00004c4c00004c4c0000
def w211 : Nat := 0xb3b30000b3b30000b3b30000b3b30000
def w212 : Nat := 0x4ccc4ccc4ccc4ccc4ccc4ccc4ccc4ccc
def w213 : Nat := 0xa0000000a0000000a0000000a0000000
def w214 : Nat := 0x5fff00005fff00005fff00005fff0000
def w215 : Nat := 0x80cc80cc80cc80cc80cc80cc80cc80cc
def w216 : Nat := 0x5f0000005f0000005f0000005f000000
def w217 : Nat := 0xa0ff0000a0ff0000a0ff0000a0ff0000
def w218 : Nat := 0x4c4ccccc4c4ccccc4c4ccccc4c4ccccc
def w219 : Nat := 0x5f00ff005f00ff005f00ff005f00ff00
def w220 : Nat := 0x8080cccc8080cccc8080cccc8080cccc
def w221 : Nat := 0xa000ff00a000ff00a000ff00a000ff00
def w222 : Nat := 0x33330000333300003333000033330000
def w223 : Nat := 0xeca0eca0eca0eca0eca0eca0eca0eca0
def w224 : Nat := 0x20a020a020a020a020a020a020a020a0
def w225 : Nat := 0xececa0a0ececa0a0ececa0a0ececa0a0
def w226 : Nat := 0x2020a0a02020a0a02020a0a02020a0a0
def w227 : Nat := 0x40c040c040c040c040c040c040c040c0
def w228 : Nat := 0xb030b030b030b030b030b030b030b030
def w229 : Nat := 0x44cc000044cc000044cc000044cc0000
def w230 : Nat := 0xbb330000bb330000bb330000bb330000
def w231 : Nat := 0x8c0c8c0c8c0c8c0c8c0c8c0c8c0c8c0c
def w232 : Nat := 0x50f0000050f0000050f0000050f00000
def w233 : Nat := 0xaf0f0000af0f0000af0f0000af0f0000
def w234 : Nat := 0x44cccccc44cccccc44cccccc44cccccc
def w235 : Nat := 0x50f0f0f050f0f0f050f0f0f050f0f0f0
def w236 : Nat := 0x8800cccc8800cccc8800cccc8800cccc
def w237 : Nat := 0xa000f0f0a000f0f0a000f0f0a000f0f0
def w238 : Nat := 0xeac0eac0eac0eac0eac0eac0eac0eac0
def w239 : Nat := 0x2a002a002a002a002a002a002a002a00
def w240 : Nat := 0xeeccaa00eeccaa00eeccaa00eeccaa00
def w241 : Nat := 0x2200aa002200aa002200aa002200aa00
def w242 : Nat := 0x4040c0c04040c0c04040c0c04040c0c0
def w243 : Nat := 0xb0b03030b0b03030b0b03030b0b03030
def w244 : Nat := 0x4400cc004400cc004400cc004400cc00
def w245 : Nat := 0xbb003300bb003300bb003300bb003300
def w246 : Nat := 0x8c8c0c0c8c8c0c0c8c8c0c0c8c8c0c0c
def w247 : Nat := 0x5000f0005000f0005000f0005000f000
def w248 : Nat := 0xaf000f00af000f00af000f00af000f00
def w249 : Nat := 0x88cc00cc88cc00cc88cc00cc88cc00cc
def w250 : Nat := 0xa0f000f0a0f000f0a0f000f0a0f000f0
def w251 : Nat := 0xeaeac0c0eaeac0c0eaeac0c0eaeac0c0
def w252 : Nat := 0x2a2a00002a2a00002a2a00002a2a0000
def w253 : Nat := 0xeeaacc00eeaacc00eeaacc00eeaacc00
def w254 : Nat := 0x22aa000022aa000022aa000022aa0000
def w255 : Nat := 0xd500d500d500d500d500d500d500d500
def w256 : Nat := 0xd5d50000d5d50000d5d50000d5d50000
def w257 : Nat := 0x2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa
def w258 : Nat := 0xc0000000c0000000c0000000c0000000
def w259 : Nat := 0x3fff00003fff00003fff00003fff0000
def w260 : Nat := 0x80aa80aa80aa80aa80aa80aa80aa80aa
def w261 : Nat := 0x3f0000003f0000003f0000003f000000
def w262 : Nat := 0xc0ff0000c0ff0000c0ff0000c0ff0000
def w263 : Nat := 0x2a2aaaaa2a2aaaaa2a2aaaaa2a2aaaaa
def w264 : Nat := 0x3f00ff003f00ff003f00ff003f00ff00
def w265 : Nat := 0x8080aaaa8080aaaa8080aaaa8080aaaa
def w266 : Nat := 0xc000ff00c000ff00c000ff00c000ff00
def w267 : Nat := 0x55550000555500005555000055550000
def w268 : Nat := 0xd050d050d050d050d050d050d050d050
def w269 : Nat := 0xdd550000dd550000dd550000dd550000
def w270 : Nat := 0x8a0a8a0a8a0a8a0a8a0a8a0a8a0a8a0a
def w271 : Nat := 0x30f0000030f0000030f0000030f00000
def w272 : Nat := 0xcf0f0000cf0f0000cf0f0000cf0f0000
def w273 : Nat := 0x22aaaaaa22aaaaaa22aaaaaa22aaaaaa
def w274 : Nat := 0x30f0f0f030f0f0f030f0f0f030f0f0f0
def w275 : Nat := 0x8800aaaa8800aaaa8800aaaa8800aaaa
def w276 : Nat := 0xc000f0f0c000f0f0c000f0f0c000f0f0
def w277 : Nat := 0xd0d05050d0d05050d0d05050d0d05050
def w278 : Nat := 0xdd005500dd005500dd005500dd005500
def w279 : Nat := 0x8a8a0a0a8a8a0a0a8a8a0a0a8a8a0a0a
def w280 : Nat := 0x3000f0003000f0003000f0003000f000
def w281 : Nat := 0xcf000f00cf000f00cf000f00cf000f00
def w282 : Nat := 0x88aa00aa88aa00aa88aa00aa88aa00aa
def w283 : Nat := 0xc0f000f0c0f000f0c0f000f0c0f000f0
def w284 : Nat := 0xaaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa
def w285 : Nat := 0xccccccc0ccccccc0ccccccc0ccccccc
def w286 : Nat := 0x444c444c444c444c444c444c444c444c
def w287 : Nat := 0x222a222a222a222a222a222a222a222a
def w288 : Nat := 0x44c444c444c444c444c444c444c444c4
def w289 : Nat := 0x22a222a222a222a222a222a222a222a2
def w290 : Nat := 0x4c444c444c444c444c444c444c444c44
def w291 : Nat := 0x2a222a222a222a222a222a222a222a22
def w292 : Nat := 0x44444c4c44444c4c44444c4c44444c4c
def w293 : Nat := 0x22222a2a22222a2a22222a2a22222a2a
def w294 : Nat := 0x4444c4c44444c4c44444c4c44444c4c4
def w295 : Nat := 0x2222a2a22222a2a22222a2a22222a2a2
def w296 : Nat := 0x4c4c44444c4c44444c4c44444c4c4444
def w297 : Nat := 0x2a2a22222a2a22222a2a22222a2a2222
def w298 : Nat := 0x444444cc444444cc444444cc444444cc
def w299 : Nat := 0x222222aa222222aa222222aa222222aa
def w300 : Nat := 0x4444cc444444cc444444cc444444cc44
def w301 : Nat := 0x2222aa222222aa222222aa222222aa22
def w302 : Nat := 0x44cc444444cc444444cc444444cc4444
def w303 : Nat := 0x22aa222222aa222222aa222222aa2222
def w304 : Nat := 0x78787878787878787878787878787878
def w305 : Nat := 0x7fff00007fff00007fff00007fff0000
def w306 : Nat := 0x7f00ff007f00ff007f00ff007f00ff00
def w307 : Nat := 0x8f808f808f808f808f808f808f808f80
def w308 : Nat := 0x8f8f80808f8f80808f8f80808f8f8080
def w309 : Nat := 0x70ff000070ff000070ff000070ff0000
def w310 : Nat := 0x7000ff007000ff007000ff007000ff00
def w311 : Nat := 0x77887788778877887788778877887788
def w312 : Nat := 0x70f0f0f070f0f0f070f0f0f070f0f0f0
def w313 : Nat := 0x88f088f088f088f088f088f088f088f0
def w314 : Nat := 0x88ff880088ff880088ff880088ff8800
def w315 : Nat := 0x7f0f00007f0f00007f0f00007f0f0000
def w316 : Nat := 0x7000f0f07000f0f07000f0f07000f0f0
def w317 : Nat := 0x77778888777788887777888877778888
def w318 : Nat := 0x8888f0f08888f0f08888f0f08888f0f0
def w319 : Nat := 0x8888ff008888ff008888ff008888ff00
def w320 : Nat := 0x7f000f007f000f007f000f007f000f00
def w321 : Nat := 0x70f000f070f000f070f000f070f000f0
def w322 : Nat := 0x777f0000777f0000777f0000777f0000
def w323 : Nat := 0x77007f0077007f0077007f0077007f00
def w324 : Nat := 0x707070f0707070f0707070f0707070f0
def w325 : Nat := 0x4ccccccc4ccccccc4ccccccc4ccccccc
def w326 : Nat := 0x2aaaaaaa2aaaaaaa2aaaaaaa2aaaaaaa
def w327 : Nat := 0xeeee00e0eeee00e0eeee00e0eeee00e0
def w328 : Nat := 0xee0e0000ee0e0000ee0e0000ee0e0000
def w329 : Nat := 0xdd00dd00dd00dd00dd00dd00dd00dd00
def w330 : Nat := 0xbb00bb00bb00bb00bb00bb00bb00bb00
def w331 : Nat := 0xeeee0e00eeee0e00eeee0e00eeee0e00
def w332 : Nat := 0xe0ee0000e0ee0000e0ee0000e0ee0000
def w333 : Nat := 0xd0d0d0d0d0d0d0d0d0d0d0d0d0d0d0d0
def w334 : Nat := 0xb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0
def w335 : Nat := 0xee00eee0ee00eee0ee00eee0ee00eee0
def w336 : Nat := 0xeeee0000eeee0000eeee0000eeee0000
def w337 : Nat := 0xee000e00ee000e00ee000e00ee000e00
def w338 : Nat := 0xdddd0000dddd0000dddd0000dddd0000
def w339 : Nat := 0xbbbb0000bbbb0000bbbb0000bbbb0000
def w340 : Nat := 0xee0eee00ee0eee00ee0eee00ee0eee00
def w341 : Nat := 0xe000ee00e000ee00e000ee00e000ee00
def w342 : Nat := 0xe0e0eee0e0e0eee0e0e0eee0e0e0eee0
def w343 : Nat := 0xe0e000e0e0e000e0e0e000e0e0e000e0
def w344 : Nat := 0xe0eee0e0e0eee0e0e0eee0e0e0eee0e0
def w345 : Nat := 0xe000e0e0e000e0e0e000e0e0e000e0e0
def w346 : Nat := 0x6e006e006e006e006e006e006e006e00
def w347 : Nat := 0x6e6e00006e6e00006e6e00006e6e0000
def w348 : Nat := 0xee06ee06ee06ee06ee06ee06ee06ee06
def w349 : Nat := 0xeeee0606eeee0606eeee0606eeee0606
def w350 : Nat := 0x66ee000066ee000066ee000066ee0000
def w351 : Nat := 0xe0e6e0e6e0e6e0e6e0e6e0e6e0e6e0e6
def w352 : Nat := 0xeeee0066eeee0066eeee0066eeee0066
def w353 : Nat := 0x6060e0e06060e0e06060e0e06060e0e0
def w354 : Nat := 0xee88ee00ee88ee00ee88ee00ee88ee00
def w355 : Nat := 0xe0e0e6e6e0e0e6e6e0e0e6e6e0e0e6e6
def w356 : Nat := 0xee008800ee008800ee008800ee008800
def w357 : Nat := 0xee00ee66ee00ee66ee00ee66ee00ee66
def w358 : Nat := 0xffffffff00000000ffffffff00000000
def p1_T : Nat := 0x88888888888888888888888888888888
def p1_R : List Nat := [0, 1]
def p1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem p1_B : baseOK p1_T p1_R p1_E = true := by decide +kernel
theorem p1_L : LowN p1_R p1_T 1 := lowCount p1_B (by decide +kernel)
def p2_T : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def p2_R : List Nat := [0, 1]
def p2_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
theorem p2_L : LowN p2_R p2_T 1 := lowCount p2_B (by decide +kernel)
def p3_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def p3_R : List Nat := [0, 1, 2]
def p3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
theorem p3_S0 : SliceN p3_R p3_T (0x33333333333333333333333333333333,1,[0, 2]) := mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel)
theorem p3_S1 : SliceN p3_R p3_T (0x55555555555555555555555555555555,1,[1, 2]) := mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel)
theorem p3_S2 : SliceN p3_R p3_T (0xcccccccccccccccccccccccccccccccc,1,[0, 2]) := mkSlice (w:=2) p3_B p2_B p2_L (by decide +kernel)
theorem p3_S3 : SliceN p3_R p3_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]) := mkSlice (w:=1) p3_B p2_B p2_L (by decide +kernel)
theorem p3_S4 : SliceN p3_R p3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]) := mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel)
theorem p3_S5 : SliceN p3_R p3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1]) := mkSlice (w:=4) p3_B p2_B p2_L (by decide +kernel)
def p3_Z : List SliceD := [(0x33333333333333333333333333333333,1,[0, 2]),(0x55555555555555555555555555555555,1,[1, 2]),(0xcccccccccccccccccccccccccccccccc,1,[0, 2]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨p3_S0,p3_S1,p3_S2,p3_S3,p3_S4,p3_S5,by simp⟩
def p3_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def p3_P : List (Nat × Nat) := [(4,5),(1,3),(0,3),(2,3),(2,6),(1,5)]
def p3_K : List CutV := p3_C.map (mkCut p3_Z)
theorem p3_W : ∀ c ∈ p3_K, CutP p3_R p3_T c := cutsGood p3_Y (by decide +kernel)
theorem p3_Q : p3_P.all (sepOK p3_T) = true := by decide +kernel
noncomputable def p3_D3 : List StD := [
([w0,w1,w2],[0,1,2,3,4,5],[0,1,2,3,4,5],[[0,1,100,2,3,101,102],[4,1,103,5,3,100],[4,0,101,5,2,104,105]])]
def p3_D2 : List StD := []
theorem p3_I2 : LevelN p3_R p3_T 2 p3_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C3x0 : levelOK p3_T p3_K p3_P 2 (p3_D2.map Prod.fst) ((p3_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem p3_I3 : LevelN p3_R p3_T 3 p3_D3 := levelStep p3_B p3_W p3_Q p3_I2 (chunks 16 p3_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C3x0
  ))
theorem p3_L : LowN p3_R p3_T 4 := lowSearch p3_B p3_I3 (by decide +kernel)
def p4_T : Nat := 0xfefefefefefefefefefefefefefefefe
def p4_R : List Nat := [0, 1, 2]
def p4_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
theorem p4_L : LowN p4_R p4_T 2 := lowCount p4_B (by decide +kernel)
def p5_T : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def p5_R : List Nat := [0, 1, 2, 3]
def p5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
theorem p5_S0 : SliceN p5_R p5_T (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) p5_B p3_B p3_L (by decide +kernel)
theorem p5_S1 : SliceN p5_R p5_T (0x33333333333333333333333333333333,4,[0, 2, 3]) := mkSlice (w:=0) p5_B p3_B p3_L (by decide +kernel)
theorem p5_S2 : SliceN p5_R p5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) p5_B p3_B p3_L (by decide +kernel)
theorem p5_S3 : SliceN p5_R p5_T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]) := mkSlice (w:=0) p5_B p3_B p3_L (by decide +kernel)
theorem p5_S4 : SliceN p5_R p5_T (0x11111111111111111111111111111111,1,[2, 3]) := mkSlice (w:=0) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S5 : SliceN p5_R p5_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]) := mkSlice (w:=1) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S6 : SliceN p5_R p5_T (0x5050505050505050505050505050505,1,[1, 3]) := mkSlice (w:=0) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S7 : SliceN p5_R p5_T (0x550055005500550055005500550055,1,[1, 2]) := mkSlice (w:=0) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S8 : SliceN p5_R p5_T (0x3030303030303030303030303030303,1,[0, 3]) := mkSlice (w:=0) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S9 : SliceN p5_R p5_T (0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]) := mkSlice (w:=2) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S10 : SliceN p5_R p5_T (0x330033003300330033003300330033,1,[0, 2]) := mkSlice (w:=0) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S11 : SliceN p5_R p5_T (0xf000f000f000f000f000f000f000f,1,[0, 1]) := mkSlice (w:=0) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S12 : SliceN p5_R p5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3]) := mkSlice (w:=4) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S13 : SliceN p5_R p5_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,1,[0, 3]) := mkSlice (w:=2) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S14 : SliceN p5_R p5_T (0x30303030303030303030303030303030,1,[0, 3]) := mkSlice (w:=4) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S15 : SliceN p5_R p5_T (0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]) := mkSlice (w:=2) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S16 : SliceN p5_R p5_T (0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]) := mkSlice (w:=8) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S17 : SliceN p5_R p5_T (0x33003300330033003300330033003300,1,[0, 2]) := mkSlice (w:=8) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S18 : SliceN p5_R p5_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]) := mkSlice (w:=1) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S19 : SliceN p5_R p5_T (0x50505050505050505050505050505050,1,[1, 3]) := mkSlice (w:=4) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S20 : SliceN p5_R p5_T (0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]) := mkSlice (w:=1) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S21 : SliceN p5_R p5_T (0x55005500550055005500550055005500,1,[1, 2]) := mkSlice (w:=8) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S22 : SliceN p5_R p5_T (0xf000f000f000f000f000f000f000f0,1,[0, 1]) := mkSlice (w:=4) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S23 : SliceN p5_R p5_T (0xf000f000f000f000f000f000f000f00,1,[0, 1]) := mkSlice (w:=8) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S24 : SliceN p5_R p5_T (0x22222222222222222222222222222222,1,[2, 3]) := mkSlice (w:=1) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S25 : SliceN p5_R p5_T (0x44444444444444444444444444444444,1,[2, 3]) := mkSlice (w:=2) p5_B p2_B p2_L (by decide +kernel)
def p5_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3]),(0x33333333333333333333333333333333,4,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]),(0x11111111111111111111111111111111,1,[2, 3]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]),(0x5050505050505050505050505050505,1,[1, 3]),(0x550055005500550055005500550055,1,[1, 2]),(0x3030303030303030303030303030303,1,[0, 3]),(0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]),(0x330033003300330033003300330033,1,[0, 2]),(0xf000f000f000f000f000f000f000f,1,[0, 1]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,1,[0, 3]),(0x30303030303030303030303030303030,1,[0, 3]),(0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]),(0x33003300330033003300330033003300,1,[0, 2]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]),(0x50505050505050505050505050505050,1,[1, 3]),(0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]),(0x55005500550055005500550055005500,1,[1, 2]),(0xf000f000f000f000f000f000f000f0,1,[0, 1]),(0xf000f000f000f000f000f000f000f00,1,[0, 1]),(0x22222222222222222222222222222222,1,[2, 3]),(0x44444444444444444444444444444444,1,[2, 3])]
theorem p5_Y : ∀ s ∈ p5_Z, SliceN p5_R p5_T s := by
  unfold p5_Z
  simp only [List.forall_mem_cons]
  exact ⟨p5_S0,p5_S1,p5_S2,p5_S3,p5_S4,p5_S5,p5_S6,p5_S7,p5_S8,p5_S9,p5_S10,p5_S11,p5_S12,p5_S13,p5_S14,p5_S15,p5_S16,p5_S17,p5_S18,p5_S19,p5_S20,p5_S21,p5_S22,p5_S23,p5_S24,p5_S25,by simp⟩
def p5_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(2,[(1,0,1)]),(3,[(1,0,1)]),(4,[]),(5,[]),(1,[(1,0,1)]),(3,[(1,0,2)]),(6,[]),(1,[(1,0,2)]),(2,[(1,0,2)]),(7,[]),(0,[(1,0,1)]),(8,[]),(9,[]),(3,[(1,1,2)]),(0,[(1,0,2)]),(2,[(1,1,2)]),(10,[]),(1,[(1,1,2)]),(0,[(1,1,2)]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[]),(17,[]),(18,[]),(19,[]),(20,[]),(21,[]),(2,[(3,0,1)]),(0,[(3,0,1)]),(0,[(2,0,1)]),(1,[(2,0,1)]),(3,[(3,0,1)]),(0,[(3,0,2)]),(0,[(2,0,2)]),(1,[(2,0,2)]),(22,[]),(23,[]),(1,[(3,0,1)]),(24,[]),(25,[]),(2,[(2,0,1)]),(2,[(3,0,2)]),(0,[(3,1,2)]),(0,[(2,1,2)]),(2,[(2,0,2)]),(1,[(3,0,2)]),(3,[(2,0,1)]),(3,[(2,0,2)]),(3,[(2,1,2)]),(2,[(2,1,2)]),(3,[(3,1,2)]),(2,[(3,1,2)]),(1,[(3,1,2)]),(0,[(0,0,2)]),(1,[(2,1,2)]),(3,[(3,0,2)]),(3,[(1,0,1),(1,1,2)]),(3,[(1,0,1),(1,0,2)]),(2,[(1,0,2),(1,1,2)]),(2,[(1,0,1),(1,1,2)]),(2,[(1,0,1),(1,0,2)]),(0,[(0,1,2)]),(2,[(1,0,1),(3,2,3)]),(0,[(0,0,1)]),(1,[(1,0,2),(3,1,3)]),(1,[(1,0,2),(1,1,2)]),(1,[(1,0,1),(1,1,2)]),(1,[(1,0,1),(1,0,2)]),(0,[(1,1,2),(3,0,3)]),(0,[(1,0,2),(1,1,2)]),(0,[(1,0,1),(1,1,2)]),(0,[(1,0,1),(1,0,2)])]
def p5_P : List (Nat × Nat) := [(4,5),(2,3),(1,3),(1,5),(8,9),(1,9),(4,6),(2,6),(8,10),(2,10),(8,12),(4,12),(4,11),(7,8)]
def p5_K : List CutV := p5_C.map (mkCut p5_Z)
theorem p5_W : ∀ c ∈ p5_K, CutP p5_R p5_T c := cutsGood p5_Y (by decide +kernel)
theorem p5_Q : p5_P.all (sepOK p5_T) = true := by decide +kernel
noncomputable def p5_D6 : List StD := [
([w0,w1,w2,w3],[0,1,2,3],[0,1,2,3,4,5,6,7,8,9,10,11],[[0,1,100,101,102],[0,2,101,100,103],[0,3,100,104,105],[1,2,102,106,107],[1,3,102,108,109],[2,3,103,110,111]])]
noncomputable def p5_D5 : List StD := [
([w0,w1,w4,w2,w3],[0,1,4,5,6,2,7,3],[3,5,7,9,10,11],[[0,1],[1],[0,100,2],[0,101,3],[0],[1,102,2],[1,103,3],[2,4,5,6,100,104],[3,4,7,6,101,105],[3,2,100,104,105]]),
([w0,w1,w2,w5,w3],[0,8,2,9,10,1,7,3],[2,5,6,8,9,11],[[0,100,1],[0,2],[2],[0,101,3],[2,102,1],[4,1,5,6,100,103],[3,1,100,103,104],[0],[2,105,3],[3,4,7,6,101,104]]),
([w0,w1,w2,w3,w6],[0,11,12,3,13,1,7,2],[2,3,6,7,8,10],[[0,100,1],[0,101,2],[0,3],[3],[2,1,100,102,103],[3,104,1],[4,1,5,6,100,102],[3,105,2],[4,2,7,6,101,103],[0]]),
([w0,w1,w2,w7,w3],[1,14,2,15,0,16,17,3],[1,0,4,5,9,11],[[0,100,1],[2,101,1],[3,1,4,5,100,102],[6,1,100,102,103],[0,2],[2],[0,104,6],[0],[2,105,6],[6,3,7,5,104,103]]),
([w0,w1,w2,w3,w8],[1,18,19,3,20,0,16,2],[1,0,3,4,7,10],[[0,100,1],[2,1,100,101,102],[3,103,1],[4,1,5,6,100,101],[0,104,2],[0,3],[3],[3,105,2],[4,2,7,6,104,102],[0]]),
([w0,w1,w2,w3,w9],[21,22,2,3,23,0,24,1],[0,1,2,4,6,8],[[0,1,100,101,102],[2,100,1],[3,103,1],[4,1,5,6,100,101],[2,104,0],[3,105,0],[4,0,7,6,104,102],[2,3],[3],[2]])]
noncomputable def p5_D4 : List StD := [
([w1,w4,w2,w5,w3],[0,8,4,16,25,24,9,26,5],[11,9],[[0],[1,2],[1,2,3],[1,4],[2,1,5],[1,2],[6,4,100],[0],[2,7],[8,7,101]]),
([w1,w4,w2,w3,w6],[0,11,27,5,12,28,29,4],[10,7],[[0],[1,2],[1,3],[1,2],[4,2,100],[3,1,5],[1,2],[2,6],[7,6,101],[0]]),
([w0,w4,w2,w7,w3],[1,14,4,7,30,24,17,31,5],[11,5],[[0],[1,2],[1,2,3],[1,4],[2,1,5],[1,2],[6,4,100],[0],[2,7],[8,7,101]]),
([w0,w4,w2,w3,w8],[1,18,32,5,19,28,33,4],[10,3],[[0],[1,2],[1,3],[1,2],[4,2,100],[3,1,5],[1,2],[2,6],[7,6,101],[0]]),
([w0,w1,w2,w10,w3],[14,4,8,34,7,35,16,36,24,3],[],[[0,1,2],[0,2,1],[3],[0,4],[1,0,2],[5],[2,6],[7],[1,8],[9,4]]),
([w11,w0,w1,w2,w3],[0,4,34,14,3,25,24,36,37,30],[],[[0,1,2],[1,0],[3],[4,5,6],[7,1,8],[1,6],[7,9],[1,6],[8,5],[1,6]]),
([w0,w1,w2,w3,w12],[18,5,11,7,38,16,39,28,2,40],[],[[0,1,2],[0,3],[0,2,1],[4],[2,5],[1,0,2],[6],[1,7],[8,3],[9]]),
([w13,w0,w1,w2,w3],[0,5,38,2,32,28,18,40,41,27],[],[[0,1,2],[1,0],[3,4,5],[6],[7,1,4],[7,4],[1,5],[8,9],[1,5],[1,5]]),
([w1,w2,w5,w3,w6],[12,42,11,43,8,0,9],[8,6],[[0,1],[2,1,100],[1,3],[4,3,101],[5],[0,6],[0,1],[6,0,3],[0,1],[5]]),
([w0,w1,w5,w7,w3],[14,8,44,32,45,27,35,46],[9,5],[[0,1],[2],[0,1,3],[0,4],[1,0,5],[6],[1,7],[0,1],[5,4,100],[3,7,101]]),
([w14,w0,w1,w2,w3],[0,8,44,14,3,45,16,35,47,26],[],[[0,1,2],[3],[1,0],[4,5,6],[1,6],[7,1,5],[7,5],[1,6],[1,6],[8,9]]),
([w0,w1,w5,w3,w9],[22,32,2,9,21,33,8],[8,2],[[0,1],[2],[0,3],[0,1],[4,1,100],[1,5],[6,5,101],[3,0,5],[0,1],[2]]),
([w0,w1,w2,w3,w15],[22,32,12,9,48,24,28,1,49,50],[],[[0,1],[0,1],[0,2,3],[4],[2,5],[1,6],[7,1],[1,0,2],[8],[9]]),
([w16,w0,w1,w2,w3],[0,2,1,32,28,22,50,9,51,42],[],[[0,1],[2,3,4],[1,0],[5],[6,3],[6,3],[6,4,7],[8,9],[3,4],[3,4]]),
([w0,w1,w2,w6,w8],[18,11,45,52,46,39,19,12],[7,3],[[0,1],[0,2],[3],[0,1,2],[1,4],[1,0,4],[5],[6,2,100],[7,4,101],[0,1]]),
([w17,w0,w1,w2,w3],[0,11,52,18,2,45,46,16,53,29],[],[[0,1,2],[3],[4,5,6],[1,0],[1,7],[6,5],[6,1,5],[1,6],[1,6],[8,9]]),
([w0,w1,w2,w6,w9],[22,30,12,48,31,21,11,49],[6,2],[[0,1],[0,2],[3],[0,1],[1,4],[5,1,100],[6,4,101],[2,0,4],[7],[0,1]]),
([w18,w0,w1,w2,w3],[0,12,48,1,30,31,22,24,54,43],[],[[0,1,2],[3,4,5],[6],[1,0],[5,4],[1,7],[5,1,4],[1,5],[8,9],[1,5]]),
([w19,w0,w1,w2,w3],[8,14,35,3,31,45,30,46],[],[[0],[0,1,2],[1,0],[3,4,5],[1,6],[1,5],[1,5],[5,1,6],[5,7],[6,4]]),
([w0,w2,w7,w3,w8],[46,42,19,18,43,14,55,17,56],[4,0],[[0,1,2],[3,1,100],[0,4,1],[5,4,101],[6],[2,7],[2,0,1],[6,0,4],[2,1],[8]]),
([w0,w1,w7,w3,w9],[21,27,22,29,14,57,17,2],[4,1],[[0,1],[2,1,100],[1,3],[4,3,101],[5],[0,6],[0,1],[5,0,3],[0,1],[7]]),
([w0,w1,w2,w3,w20],[21,27,19,42,43,0,58,59,56],[],[[0,1],[2,3],[1,4],[5,1],[0,1],[0,2,3],[6],[1,0,2],[7],[8]]),
([w21,w0,w1,w2,w3],[0,27,43,2,60,1,19,61,42,29],[],[[0,1,2],[2,3,4],[3,1,5],[6],[7,1],[2,8],[1,2],[2,1,7],[7,2,8],[1,9]]),
([w22,w0,w1,w2,w3],[11,18,39,2,46,45,30,33,38],[],[[0],[0,1,2],[3,4,5],[1,0],[1,6],[1,5],[1,5],[5,4],[5,1,4],[6,7,8]]),
([w0,w1,w2,w8,w9],[21,25,26,22,18,19,58,59],[0,1],[[0,1],[1,2],[3,1,100],[4,2,101],[0,5],[6],[0,1],[5,0,2],[7],[0,1]]),
([w23,w0,w1,w2,w3],[0,25,42,19,21,59,43,26],[],[[0,1,2],[2,3],[4],[3,4],[5,1],[1,2],[2,6],[3,2],[2,1,5],[1,7]]),
([w24,w0,w1,w2,w3],[42,1,33,30,0,49,22,45,31,62],[],[[0],[1,2,3],[4,2,5],[3,6],[2,3],[2,7],[6,3],[3,8],[7,2,9],[3,2,8]]),
([w25,w0,w1,w2,w3],[0,26,25,42,35,21,59,57,29,46],[],[[0,1,2],[3],[4,5,6],[2,1],[1,2],[2,1],[7,8],[5,9],[1,2],[2,1]])]
noncomputable def p5_D3 : List StD := [
([w4,w5,w7,w3],[1,14,44,35,42,45,63,64,26],[12,9,5],[[0,1,2],[1,3],[4,5,100],[0,1],[6,5,101],[7,8,102]]),
([w4,w2,w6,w8],[65,45,1,18,52,66,67,46],[13,7,3],[[0,1,100],[2,3,4],[3,1],[5,1,101],[6,7,102],[2,1,3]]),
([w26,w0,w1,w2],[0,45,46,50,26,68,69,25],[],[[0,1],[1,2],[3,4,5],[4,6,7],[2,1],[1,2]]),
([w27,w0,w1,w3],[0,25,26,36,46,70,71,45],[],[[0,1,2],[3,4,5],[2,1],[2,1],[4,6,7],[2,1]]),
([w1,w5,w6,w9],[72,42,73,30,74,2,0],[13,6,2],[[0,1,100],[2,3,101],[4,1,102],[5,1],[6,3],[5,1]]),
([w28,w0,w2,w3],[0,30,45,46,75,26],[],[[0,1],[1,2,3],[3,2],[3,2],[3,1],[1,4,5]]),
([w0,w7,w8,w9],[76,26,77,25,78,2,1],[13,0,1],[[0,1,100],[2,3,101],[4,1,102],[5,1],[6,3],[5,1]]),
([w29,w1,w2,w3],[0,25,26,46,45],[],[[0,1],[0,2],[0,3,4],[4,3],[2,1],[1,2]])]
def p5_D2 : List StD := []
theorem p5_I2 : LevelN p5_R p5_T 2 p5_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C3x0 : levelOK p5_T p5_K p5_P 2 (p5_D2.map Prod.fst) ((p5_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem p5_I3 : LevelN p5_R p5_T 3 p5_D3 := levelStep p5_B p5_W p5_Q p5_I2 (chunks 16 p5_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C4x0 : levelOK p5_T p5_K p5_P 3 (p5_D3.map Prod.fst) ((p5_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C4x1 : levelOK p5_T p5_K p5_P 3 (p5_D3.map Prod.fst) ((p5_D4.drop (1*16)).take 16) = true := by decide +kernel
theorem p5_I4 : LevelN p5_R p5_T 4 p5_D4 := levelStep p5_B p5_W p5_Q p5_I3 (chunks 16 p5_D4 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C4x0
  · exact p5_C4x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C5x0 : levelOK p5_T p5_K p5_P 4 (p5_D4.map Prod.fst) ((p5_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem p5_I5 : LevelN p5_R p5_T 5 p5_D5 := levelStep p5_B p5_W p5_Q p5_I4 (chunks 16 p5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C6x0 : levelOK p5_T p5_K p5_P 5 (p5_D5.map Prod.fst) ((p5_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem p5_I6 : LevelN p5_R p5_T 6 p5_D6 := levelStep p5_B p5_W p5_Q p5_I5 (chunks 16 p5_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C6x0
  ))
theorem p5_L : LowN p5_R p5_T 7 := lowSearch p5_B p5_I6 (by decide +kernel)
def p6_T : Nat := 0xfee8e8e8fee8e8e8fee8e8e8fee8e8e8
def p6_R : List Nat := [0, 1, 2, 3, 4]
def p6_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,17,25),(4,9,25)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
theorem p6_S0 : SliceN p6_R p6_T (0xff00ff00ff00ff00ff00ff00ff00ff00,7,[0, 1, 2, 4]) := mkSlice (w:=8) p6_B p5_B p5_L (by decide +kernel)
def p6_Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff00,7,[0, 1, 2, 4])]
theorem p6_Y : ∀ s ∈ p6_Z, SliceN p6_R p6_T s := by
  unfold p6_Z
  simp only [List.forall_mem_cons]
  exact ⟨p6_S0,by simp⟩
def p6_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def p6_P : List (Nat × Nat) := []
def p6_K : List CutV := p6_C.map (mkCut p6_Z)
theorem p6_W : ∀ c ∈ p6_K, CutP p6_R p6_T c := cutsGood p6_Y (by decide +kernel)
theorem p6_Q : p6_P.all (sepOK p6_T) = true := by decide +kernel
noncomputable def p6_D7 : List StD := [
([w0,w1,w2,w3,w30],[0],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p6_D6 : List StD := []
theorem p6_I6 : LevelN p6_R p6_T 6 p6_D6 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p6_C7x0 : levelOK p6_T p6_K p6_P 6 (p6_D6.map Prod.fst) ((p6_D7.drop (0*16)).take 16) = true := by decide +kernel
theorem p6_I7 : LevelN p6_R p6_T 7 p6_D7 := levelStep p6_B p6_W p6_Q p6_I6 (chunks 16 p6_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_C7x0
  ))
theorem p6_L : LowN p6_R p6_T 8 := lowSearch p6_B p6_I7 (by decide +kernel)
def p7_T : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def p7_R : List Nat := [0, 1, 2]
def p7_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
theorem p7_L : LowN p7_R p7_T 2 := lowCount p7_B (by decide +kernel)
def p8_T : Nat := 0x80808080808080808080808080808080
def p8_R : List Nat := [0, 1, 2]
def p8_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
theorem p8_L : LowN p8_R p8_T 2 := lowCount p8_B (by decide +kernel)
def p9_T : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def p9_R : List Nat := [0, 1, 2]
def p9_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
theorem p9_L : LowN p9_R p9_T 2 := lowCount p9_B (by decide +kernel)
def p10_T : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
def p10_R : List Nat := [0, 1, 2, 3]
def p10_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
theorem p10_S0 : SliceN p10_R p10_T (0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]) := mkSlice (w:=2) p10_B p7_B p7_L (by decide +kernel)
theorem p10_S1 : SliceN p10_R p10_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]) := mkSlice (w:=1) p10_B p4_B p4_L (by decide +kernel)
theorem p10_S2 : SliceN p10_R p10_T (0x55555555555555555555555555555555,2,[1, 2, 3]) := mkSlice (w:=0) p10_B p8_B p8_L (by decide +kernel)
theorem p10_S3 : SliceN p10_R p10_T (0x33333333333333333333333333333333,2,[0, 2, 3]) := mkSlice (w:=0) p10_B p9_B p9_L (by decide +kernel)
theorem p10_S4 : SliceN p10_R p10_T (0x22222222222222222222222222222222,1,[2, 3]) := mkSlice (w:=1) p10_B p2_B p2_L (by decide +kernel)
theorem p10_S5 : SliceN p10_R p10_T (0x44444444444444444444444444444444,1,[2, 3]) := mkSlice (w:=2) p10_B p1_B p1_L (by decide +kernel)
theorem p10_S6 : SliceN p10_R p10_T (0x3030303030303030303030303030303,1,[0, 3]) := mkSlice (w:=0) p10_B p1_B p1_L (by decide +kernel)
theorem p10_S7 : SliceN p10_R p10_T (0x50505050505050505050505050505050,1,[1, 3]) := mkSlice (w:=4) p10_B p1_B p1_L (by decide +kernel)
theorem p10_S8 : SliceN p10_R p10_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]) := mkSlice (w:=1) p10_B p2_B p2_L (by decide +kernel)
theorem p10_S9 : SliceN p10_R p10_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,1,[0, 3]) := mkSlice (w:=6) p10_B p2_B p2_L (by decide +kernel)
theorem p10_S10 : SliceN p10_R p10_T (0x55005500550055005500550055005500,1,[1, 2]) := mkSlice (w:=8) p10_B p1_B p1_L (by decide +kernel)
theorem p10_S11 : SliceN p10_R p10_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,2,[0, 1, 3]) := mkSlice (w:=0) p10_B p9_B p9_L (by decide +kernel)
theorem p10_S12 : SliceN p10_R p10_T (0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]) := mkSlice (w:=8) p10_B p7_B p7_L (by decide +kernel)
theorem p10_S13 : SliceN p10_R p10_T (0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]) := mkSlice (w:=1) p10_B p2_B p2_L (by decide +kernel)
theorem p10_S14 : SliceN p10_R p10_T (0xff00ff00ff00ff00ff00ff00ff00ff,2,[0, 1, 2]) := mkSlice (w:=0) p10_B p9_B p9_L (by decide +kernel)
theorem p10_S15 : SliceN p10_R p10_T (0x330033003300330033003300330033,1,[0, 2]) := mkSlice (w:=0) p10_B p1_B p1_L (by decide +kernel)
theorem p10_S16 : SliceN p10_R p10_T (0xcc00cc00cc00cc00cc00cc00cc00cc00,1,[0, 2]) := mkSlice (w:=10) p10_B p2_B p2_L (by decide +kernel)
theorem p10_S17 : SliceN p10_R p10_T (0xf000f000f000f000f000f000f000f000,1,[0, 1]) := mkSlice (w:=12) p10_B p2_B p2_L (by decide +kernel)
theorem p10_S18 : SliceN p10_R p10_T (0xf000f000f000f000f000f000f000f,1,[0, 1]) := mkSlice (w:=0) p10_B p1_B p1_L (by decide +kernel)
def p10_Z : List SliceD := [(0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]),(0x55555555555555555555555555555555,2,[1, 2, 3]),(0x33333333333333333333333333333333,2,[0, 2, 3]),(0x22222222222222222222222222222222,1,[2, 3]),(0x44444444444444444444444444444444,1,[2, 3]),(0x3030303030303030303030303030303,1,[0, 3]),(0x50505050505050505050505050505050,1,[1, 3]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,1,[0, 3]),(0x55005500550055005500550055005500,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,2,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]),(0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff,2,[0, 1, 2]),(0x330033003300330033003300330033,1,[0, 2]),(0xcc00cc00cc00cc00cc00cc00cc00cc00,1,[0, 2]),(0xf000f000f000f000f000f000f000f000,1,[0, 1]),(0xf000f000f000f000f000f000f000f,1,[0, 1])]
theorem p10_Y : ∀ s ∈ p10_Z, SliceN p10_R p10_T s := by
  unfold p10_Z
  simp only [List.forall_mem_cons]
  exact ⟨p10_S0,p10_S1,p10_S2,p10_S3,p10_S4,p10_S5,p10_S6,p10_S7,p10_S8,p10_S9,p10_S10,p10_S11,p10_S12,p10_S13,p10_S14,p10_S15,p10_S16,p10_S17,p10_S18,by simp⟩
def p10_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[]),(17,[]),(18,[])]
def p10_P : List (Nat × Nat) := [(4,5),(12,14),(2,3),(1,3),(10,14),(1,5),(6,14),(8,9),(1,9),(5,6),(0,3),(3,6),(0,5),(3,10),(0,9),(1,7),(1,11),(1,13)]
def p10_K : List CutV := p10_C.map (mkCut p10_Z)
theorem p10_W : ∀ c ∈ p10_K, CutP p10_R p10_T c := cutsGood p10_Y (by decide +kernel)
theorem p10_Q : p10_P.all (sepOK p10_T) = true := by decide +kernel
noncomputable def p10_D5 : List StD := [
([w0,w1,w2,w3],[],[0,1,2,3,4,5,6,7,8],[[100,101,102,103],[102,104,100,105],[100,106,107,108],[103,105,101,104],[103,108,101,106],[105,108,104,106]])]
noncomputable def p10_D4 : List StD := [
([w31,w0,w1,w2,w3],[0,1,2,3,4,5,6,7],[9],[[0],[1],[2],[2],[100,2,3],[2,4],[2,4],[3,5],[3,5],[6,7]]),
([w0,w1,w4,w2,w3],[0,1,3,5,2,4,8,9],[9],[[100,0,1],[2],[3,1],[3,1],[4],[5,0],[5,0],[0],[0],[6,7]]),
([w32,w0,w1,w2,w3],[3,1,2,4,0,9,10],[10,5],[[0],[1],[2,3],[2,3],[2,4,100],[2,3],[2,3],[3,4],[3,4],[101,5,6]]),
([w33,w0,w1,w2,w3],[0,2,4,5,3,1,8],[10,6],[[0],[1],[2,3],[2,3],[4,5,100],[3,2],[3,2],[2,3],[2,3],[6,101]]),
([w34,w0,w1,w2,w3],[9,2,4,8,11,5,7,6],[11],[[0],[1],[2],[1],[1,3],[100,1,4],[1,3],[3,5,6],[7,5],[3,6]]),
([w0,w1,w2,w5,w3],[7,8,9,4,6,2],[11],[[0,1],[100,2,3],[4],[0,1],[1,0],[0],[3,2],[5],[1,0],[0]]),
([w35,w0,w1,w2,w3],[6,2,8,4,9,7,10],[12,3],[[0],[1,2],[3],[1,2],[1,2],[1,4,100],[1,2],[2,5],[101,4,6],[2,4]]),
([w36,w0,w1,w2,w3],[9,8,7,2,6,4],[12,6],[[0],[1,2],[3],[1,2],[2,1],[4,5,100],[2,1],[1,2],[4,101],[1,2]]),
([w37,w0,w1,w2,w3],[12,2,4,13,14,15,7,5,10],[13],[[0],[1],[1],[2],[1,3],[1,3],[100,1,4],[5,6,7],[3,7,8],[3,6,8]]),
([w0,w1,w2,w3,w6],[10,8,4,12,14,16,13,2],[13],[[0,1],[0,2],[100,3,1],[4],[1,5,2],[2,0,6],[0],[1,0,6],[0],[7]]),
([w38,w0,w1,w2,w3],[14,2,13,4,12,7],[14,3],[[0],[1,2],[1,2],[3],[1,2],[1,2],[1,4,100],[101,5],[2,4],[2,4]]),
([w39,w0,w1,w2,w3],[12,14,10,2,13,4],[14,4],[[0],[1,2],[1,2],[3],[2,4],[2,4],[1,5,100],[5,101],[1,2],[1,2]]),
([w0,w40,w1,w2,w3],[6,9,15,4,7,16,8],[14],[[0,1],[0,1],[0,1],[2,3,100],[4],[5],[0,1],[2,6],[0,1],[0,1]]),
([w0,w1,w2,w7,w3],[7,16,6,9,8,4],[2],[[0,1,2],[2,3],[2,1],[0,1,100],[0,1],[4],[2,3],[5],[2,0],[2,0]]),
([w41,w0,w1,w2,w3],[9,8,16,7,6,4],[2,15],[[0,100],[1],[2],[0],[3,0,4],[4,0],[3,5],[5,3,101],[4,0],[4,0]]),
([w42,w0,w1,w2,w3],[6,7,4,16,9,5,8],[0,15],[[0,100],[1],[2],[0],[0,3],[0,4],[5,3,6],[6,3,101],[0,4],[0,3,4]]),
([w0,w43,w1,w2,w3],[6,16,4,14,10,9],[12],[[0,1],[0,1],[0,2,100],[3,1],[4],[2,1],[5],[2,1],[0,3],[0,1,3]]),
([w0,w1,w2,w3,w8],[10,16,15,9,14,4],[2],[[0,1,2],[0,3,100],[2,1],[2,1],[2,1],[0,3],[4],[2,0],[2,0],[5]]),
([w44,w0,w1,w2,w3],[16,14,9,10,15,4],[2,16],[[0,100],[1],[0],[2],[3,0,4],[3,5],[4,0],[4,0],[5,3,101],[4,0]]),
([w45,w0,w1,w2,w3],[9,10,16,4,15,5,13],[7,16],[[0,100],[1],[2],[3],[4,0],[5,0,6],[4,2],[4,2],[6,0,101],[4,0,2]]),
([w0,w1,w46,w2,w3],[15,13,17,6,8,16,9],[10],[[0,1,100],[0,2],[3,1,2],[0,2],[1,2],[0,2,4],[1,2],[5],[6],[3,0]]),
([w0,w1,w2,w3,w9],[10,16,9,18,17,13,6],[10],[[0,1,100],[0,2,3],[3,1],[3,1],[3,1,4],[3,0],[3,0],[0,2],[5],[6]]),
([w47,w0,w1,w2,w3],[16,10,13,9,6,17,18],[0,17],[[0,100],[1],[2],[3],[1,0,4],[1,5,4],[6,0],[6,0,5],[4,1,6],[4,0,101]]),
([w48,w0,w1,w2,w3],[17,16,6,15,13,9,18],[7,17],[[0,100],[0],[1],[2],[3,4,5],[6,0],[3,0],[3,0,6],[4,0],[3,5,101]])]
noncomputable def p10_D3 : List StD := [
([w0,w1,w49,w3],[2,9,6,17,15,18],[],[[0,1,2],[0,1,2],[0,3,4],[4,3,5],[2,1],[2,1]]),
([w50,w0,w1,w3],[2,13,17,18,16,8,10],[],[[0,1],[1,2,3],[1,4],[0,5],[0,5],[3,6]]),
([w0,w1,w2,w51],[2,16,15,17,6,18],[],[[0,1,2],[0,3,4],[0,1,2],[2,1],[4,3,5],[2,1]]),
([w52,w0,w1,w2],[2,16,18,17,6,10,15,13,5],[],[[0,1,2],[2,3,4],[4,5,6],[0,7],[0,7],[2,8,6]]),
([w0,w1,w53,w3],[6,13,16,2,5,18,17],[],[[0,1,2],[0,1,3],[4,2,5],[5,2,6],[0,4],[0,2,1]]),
([w11,w0,w1,w3],[2,13,17,18,16,7,8],[],[[0,1],[2,0,3],[1,4],[5,1],[5,2,6],[1,2]]),
([w0,w1,w54,w2],[15,13,16,18,5,17],[],[[0,1,2],[0,2],[3,1,4],[1,4,5],[0,2],[0,2]]),
([w13,w0,w1,w2],[2,8,17,18,13,16,10],[],[[0,1],[2,0,3],[1,4,5],[6,1],[6,2,4],[1,2]]),
([w0,w55,w2,w3],[2,13,9,18,16,17,8],[],[[0,1],[0,2,3],[0,4,3],[1,4,5],[1,2,5],[6,2]]),
([w56,w0,w2,w3],[2,16,8,17,13,4,10,15],[],[[0,1,2],[2,1,3],[4,3],[0,5],[0,2],[2,6,7]]),
([w0,w1,w2,w57],[2,8,17,18,10,13],[],[[0,1],[0,2,3],[0,1],[1,2],[3,2],[1,4,5]]),
([w58,w0,w1,w2],[2,8,13,10,5,15],[],[[0,1],[2,3],[1,3,2],[0,1],[0,2],[1,4,5]]),
([w0,w59,w2,w3],[2,8,6,13,17,15,9],[],[[0,1],[2,3,4],[5,1,4],[1,0],[2,4,3],[1,6]]),
([w14,w0,w2,w3],[2,13,8,10,5,9],[],[[0,1],[2,0],[1,3],[4,1],[4,2],[1,5,2]]),
([w0,w1,w2,w60],[15,13,9,18,8,2,17],[],[[0,1,2],[3,1,2],[0,4,5],[0,6,3],[1,2,6],[0,2,4]]),
([w16,w0,w1,w2],[2,8,10,9,13,17],[],[[0,1],[2,3,4],[1,0],[2,1],[2,3,4],[1,5]]),
([w0,w61,w2,w3],[2,9,13,16,18,17],[],[[0,1,2],[0,1,2],[0,3,4],[4,3,5],[2,1,5],[2,1,3]]),
([w62,w0,w2,w3],[2,13,18,17,4,10],[],[[0,1],[2,3],[1,3],[0,1],[0,4],[1,5]]),
([w0,w1,w63,w3],[2,13,17,18,10],[],[[0,1],[0,1],[0,2,3],[3,2],[1,2],[1,4]]),
([w64,w0,w1,w3],[2,17,18,16,4,13,8,10],[],[[0,1,2],[2,3,4],[4,3],[0,5],[0,6],[2,7]]),
([w0,w65,w2,w3],[2,18,10,17,13,15],[],[[0,1],[2,3,4],[5,3],[1,3],[1,0],[4,2]]),
([w17,w0,w2,w3],[2,13,18,17,10,5,8],[],[[0,1],[2,3],[1,0],[4,1],[5,3,6],[1,4]]),
([w0,w1,w66,w3],[10,8,17,18,13],[],[[0,1],[0,2,3],[3,1,2],[1,2],[3,0],[1,0,4]]),
([w18,w0,w1,w3],[2,13,17,8,10,7],[],[[0,1],[2,3],[1,0],[4,1],[5,2,3],[1,2]]),
([w0,w40,w7,w3],[18,9,6,17],[15],[[0,1],[2,1],[0,3],[100],[2,1],[0,1,2]]),
([w0,w1,w2,w67],[10,9,6,2,17,8,15,16],[],[[0,1,2],[0,1,2],[3,4,5],[6,4,7],[2,0,1],[2,0,1]]),
([w0,w1,w2,w68],[15,9,6,17,18],[],[[0,1],[2,1],[0,3],[0,3,4],[2,1],[0,1,2]]),
([w0,w1,w2,w69],[10,9,6,2,17,18],[],[[0,1,2],[0,1,2],[3,4,5],[5,4],[2,0,1],[2,0,1]]),
([w0,w1,w70,w2],[6,9,2,8,16,15],[],[[0,1],[2,3],[0,1],[0,1],[3,4,5],[0,1]]),
([w0,w43,w2,w8],[6,16,9,15],[16],[[0,1],[0,2],[3,1],[3,1],[100],[0,1,3]]),
([w0,w1,w71,w3],[15,9,2,6,16],[],[[0,1],[2,1,3],[0,4],[0,4],[3,1],[0,1,3]]),
([w0,w1,w72,w3],[6,16,17,15,18],[],[[0,1],[0,2],[3,1],[3,1],[0,2,4],[0,1,3]]),
([w0,w1,w73,w3],[15,16,2,17,18],[],[[0,1],[2,3,4],[0,1],[0,1],[4,3],[0,1]]),
([w0,w74,w1,w3],[2,9,18,15,16,6],[],[[0,1,2],[3,1],[2,4],[2,4,3],[3,1,4],[2,1,5]]),
([w0,w1,w46,w9],[15,16,17,18],[17],[[0,1],[0,2],[3,1],[3,1,2],[0,2,3],[100]]),
([w0,w75,w2,w3],[2,16,6,17,18,9],[],[[0,1,2],[2,3],[4,1],[4,1,3],[2,3,4],[2,1,5]]),
([w0,w76,w2,w3],[2,16,6,17,18,15],[],[[0,1,2],[2,3],[4,1],[4,1,3],[2,3,4],[2,1,5]]),
([w0,w77,w2,w3],[2,16,15,18,17],[],[[0,1,2],[3,4],[2,1],[2,1],[3,4],[2,1]]),
([w0,w78,w2,w3],[2,9,15,18,17,6],[],[[0,1,2],[3,1],[2,4],[2,4,3],[3,1,4],[2,1,5]])]
def p10_D2 : List StD := []
theorem p10_I2 : LevelN p10_R p10_T 2 p10_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p10_C3x0 : levelOK p10_T p10_K p10_P 2 (p10_D2.map Prod.fst) ((p10_D3.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p10_C3x1 : levelOK p10_T p10_K p10_P 2 (p10_D2.map Prod.fst) ((p10_D3.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p10_C3x2 : levelOK p10_T p10_K p10_P 2 (p10_D2.map Prod.fst) ((p10_D3.drop (2*16)).take 16) = true := by decide +kernel
theorem p10_I3 : LevelN p10_R p10_T 3 p10_D3 := levelStep p10_B p10_W p10_Q p10_I2 (chunks 16 p10_D3 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C3x0
  · exact p10_C3x1
  · exact p10_C3x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p10_C4x0 : levelOK p10_T p10_K p10_P 3 (p10_D3.map Prod.fst) ((p10_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p10_C4x1 : levelOK p10_T p10_K p10_P 3 (p10_D3.map Prod.fst) ((p10_D4.drop (1*16)).take 16) = true := by decide +kernel
theorem p10_I4 : LevelN p10_R p10_T 4 p10_D4 := levelStep p10_B p10_W p10_Q p10_I3 (chunks 16 p10_D4 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C4x0
  · exact p10_C4x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p10_C5x0 : levelOK p10_T p10_K p10_P 4 (p10_D4.map Prod.fst) ((p10_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem p10_I5 : LevelN p10_R p10_T 5 p10_D5 := levelStep p10_B p10_W p10_Q p10_I4 (chunks 16 p10_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C5x0
  ))
theorem p10_L : LowN p10_R p10_T 6 := lowSearch p10_B p10_I5 (by decide +kernel)
def p11_T : Nat := 0xe888e888e888e888e888e888e888e888
def p11_R : List Nat := [0, 1, 2, 3]
def p11_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,9,13),(3,5,13)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
theorem p11_S0 : SliceN p11_R p11_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3]) := mkSlice (w:=4) p11_B p3_B p3_L (by decide +kernel)
def p11_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3])]
theorem p11_Y : ∀ s ∈ p11_Z, SliceN p11_R p11_T s := by
  unfold p11_Z
  simp only [List.forall_mem_cons]
  exact ⟨p11_S0,by simp⟩
def p11_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def p11_P : List (Nat × Nat) := []
def p11_K : List CutV := p11_C.map (mkCut p11_Z)
theorem p11_W : ∀ c ∈ p11_K, CutP p11_R p11_T c := cutsGood p11_Y (by decide +kernel)
theorem p11_Q : p11_P.all (sepOK p11_T) = true := by decide +kernel
noncomputable def p11_D4 : List StD := [
([w0,w1,w2,w3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def p11_D3 : List StD := []
theorem p11_I3 : LevelN p11_R p11_T 3 p11_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p11_C4x0 : levelOK p11_T p11_K p11_P 3 (p11_D3.map Prod.fst) ((p11_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem p11_I4 : LevelN p11_R p11_T 4 p11_D4 := levelStep p11_B p11_W p11_Q p11_I3 (chunks 16 p11_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C4x0
  ))
theorem p11_L : LowN p11_R p11_T 5 := lowSearch p11_B p11_I4 (by decide +kernel)
def p12_T : Nat := 0x80008000800080008000800080008000
def p12_R : List Nat := [0, 1, 2, 3]
def p12_E : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
theorem p12_L : LowN p12_R p12_T 3 := lowCount p12_B (by decide +kernel)
def p13_T : Nat := 0xe8888880e8888880e8888880e8888880
def p13_R : List Nat := [0, 1, 2, 3, 4]
def p13_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,3,19)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
theorem p13_S0 : SliceN p13_R p13_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,6,[1, 2, 3, 4]) := mkSlice (w:=1) p13_B p10_B p10_L (by decide +kernel)
theorem p13_S1 : SliceN p13_R p13_T (0xcccccccccccccccccccccccccccccccc,6,[0, 2, 3, 4]) := mkSlice (w:=2) p13_B p10_B p10_L (by decide +kernel)
theorem p13_S2 : SliceN p13_R p13_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 1, 3, 4]) := mkSlice (w:=4) p13_B p11_B p11_L (by decide +kernel)
theorem p13_S3 : SliceN p13_R p13_T (0xff00ff00ff00ff00ff00ff00ff00ff00,5,[0, 1, 2, 4]) := mkSlice (w:=8) p13_B p11_B p11_L (by decide +kernel)
theorem p13_S4 : SliceN p13_R p13_T (0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) p13_B p11_B p11_L (by decide +kernel)
theorem p13_S5 : SliceN p13_R p13_T (0xf000f000f000f000f000f000f000f000,4,[0, 1, 4]) := mkSlice (w:=12) p13_B p3_B p3_L (by decide +kernel)
theorem p13_S6 : SliceN p13_R p13_T (0xf0f00000f0f00000f0f00000f0f00000,4,[0, 1, 3]) := mkSlice (w:=20) p13_B p3_B p3_L (by decide +kernel)
theorem p13_S7 : SliceN p13_R p13_T (0xff000000ff000000ff000000ff000000,4,[0, 1, 2]) := mkSlice (w:=24) p13_B p3_B p3_L (by decide +kernel)
theorem p13_S8 : SliceN p13_R p13_T (0x55555555555555555555555555555555,3,[1, 2, 3, 4]) := mkSlice (w:=0) p13_B p12_B p12_L (by decide +kernel)
theorem p13_S9 : SliceN p13_R p13_T (0x8080808080808080808080808080808,1,[3, 4]) := mkSlice (w:=3) p13_B p2_B p2_L (by decide +kernel)
theorem p13_S10 : SliceN p13_R p13_T (0x33333333333333333333333333333333,3,[0, 2, 3, 4]) := mkSlice (w:=0) p13_B p12_B p12_L (by decide +kernel)
theorem p13_S11 : SliceN p13_R p13_T (0x50505050505050505050505050505050,2,[1, 3, 4]) := mkSlice (w:=4) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S12 : SliceN p13_R p13_T (0x55005500550055005500550055005500,2,[1, 2, 4]) := mkSlice (w:=8) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S13 : SliceN p13_R p13_T (0x55550000555500005555000055550000,2,[1, 2, 3]) := mkSlice (w:=16) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S14 : SliceN p13_R p13_T (0xf000f000f000f000f000f000f000f,2,[0, 1, 4]) := mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S15 : SliceN p13_R p13_T (0xf0f00000f0f00000f0f00000f0f,2,[0, 1, 3]) := mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S16 : SliceN p13_R p13_T (0x88888888888888888888888888888888,2,[2, 3, 4]) := mkSlice (w:=3) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S17 : SliceN p13_R p13_T (0x30303030303030303030303030303030,2,[0, 3, 4]) := mkSlice (w:=4) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S18 : SliceN p13_R p13_T (0x880088008800880088008800880088,1,[2, 4]) := mkSlice (w:=3) p13_B p2_B p2_L (by decide +kernel)
theorem p13_S19 : SliceN p13_R p13_T (0x50005000500050005000500050005000,1,[1, 4]) := mkSlice (w:=12) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S20 : SliceN p13_R p13_T (0x8888000088880000888800008888,1,[2, 3]) := mkSlice (w:=3) p13_B p2_B p2_L (by decide +kernel)
theorem p13_S21 : SliceN p13_R p13_T (0xff000000ff000000ff000000ff,2,[0, 1, 2]) := mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S22 : SliceN p13_R p13_T (0x33003300330033003300330033003300,2,[0, 2, 4]) := mkSlice (w:=8) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S23 : SliceN p13_R p13_T (0x33330000333300003333000033330000,2,[0, 2, 3]) := mkSlice (w:=16) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S24 : SliceN p13_R p13_T (0x50500000505000005050000050500000,1,[1, 3]) := mkSlice (w:=20) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S25 : SliceN p13_R p13_T (0x20202020202020202020202020202020,1,[3, 4]) := mkSlice (w:=5) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S26 : SliceN p13_R p13_T (0xc0c00000c0c00000c0c00000c0c,1,[0, 3]) := mkSlice (w:=2) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S27 : SliceN p13_R p13_T (0xc000c000c000c000c000c000c000c,1,[0, 4]) := mkSlice (w:=2) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S28 : SliceN p13_R p13_T (0x22002200220022002200220022002200,1,[2, 4]) := mkSlice (w:=9) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S29 : SliceN p13_R p13_T (0xcc000000cc000000cc000000cc,1,[0, 2]) := mkSlice (w:=2) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S30 : SliceN p13_R p13_T (0x22220000222200002222000022220000,1,[2, 3]) := mkSlice (w:=17) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S31 : SliceN p13_R p13_T (0x40404040404040404040404040404040,1,[3, 4]) := mkSlice (w:=6) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S32 : SliceN p13_R p13_T (0xa0a00000a0a00000a0a00000a0a,1,[1, 3]) := mkSlice (w:=1) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S33 : SliceN p13_R p13_T (0xa000a000a000a000a000a000a000a,1,[1, 4]) := mkSlice (w:=1) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S34 : SliceN p13_R p13_T (0x44004400440044004400440044004400,1,[2, 4]) := mkSlice (w:=10) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S35 : SliceN p13_R p13_T (0xaa000000aa000000aa000000aa,1,[1, 2]) := mkSlice (w:=1) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S36 : SliceN p13_R p13_T (0x44440000444400004444000044440000,1,[2, 3]) := mkSlice (w:=18) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S37 : SliceN p13_R p13_T (0x30003000300030003000300030003000,1,[0, 4]) := mkSlice (w:=12) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S38 : SliceN p13_R p13_T (0x30300000303000003030000030300000,1,[0, 3]) := mkSlice (w:=20) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S39 : SliceN p13_R p13_T (0x55000000550000005500000055000000,1,[1, 2]) := mkSlice (w:=24) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S40 : SliceN p13_R p13_T (0x33000000330000003300000033000000,1,[0, 2]) := mkSlice (w:=24) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S41 : SliceN p13_R p13_T (0xa000a000a000a000a000a000a000a000,1,[1, 4]) := mkSlice (w:=13) p13_B p2_B p2_L (by decide +kernel)
theorem p13_S42 : SliceN p13_R p13_T (0xa0a00000a0a00000a0a00000a0a00000,1,[1, 3]) := mkSlice (w:=21) p13_B p2_B p2_L (by decide +kernel)
theorem p13_S43 : SliceN p13_R p13_T (0xaa000000aa000000aa000000aa000000,1,[1, 2]) := mkSlice (w:=25) p13_B p2_B p2_L (by decide +kernel)
theorem p13_S44 : SliceN p13_R p13_T (0xc000c000c000c000c000c000c000c000,1,[0, 4]) := mkSlice (w:=14) p13_B p2_B p2_L (by decide +kernel)
theorem p13_S45 : SliceN p13_R p13_T (0xc0c00000c0c00000c0c00000c0c00000,1,[0, 3]) := mkSlice (w:=22) p13_B p2_B p2_L (by decide +kernel)
theorem p13_S46 : SliceN p13_R p13_T (0xcc000000cc000000cc000000cc000000,1,[0, 2]) := mkSlice (w:=26) p13_B p2_B p2_L (by decide +kernel)
theorem p13_S47 : SliceN p13_R p13_T (0xf0000000f0000000f0000000f0000000,1,[0, 1]) := mkSlice (w:=28) p13_B p2_B p2_L (by decide +kernel)
theorem p13_S48 : SliceN p13_R p13_T (0xf0000000f0000000f0000000f0,1,[0, 1]) := mkSlice (w:=4) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S49 : SliceN p13_R p13_T (0xf0000000f0000000f0000000f00,1,[0, 1]) := mkSlice (w:=8) p13_B p1_B p1_L (by decide +kernel)
theorem p13_S50 : SliceN p13_R p13_T (0xf0000000f0000000f0000000f0000,1,[0, 1]) := mkSlice (w:=16) p13_B p1_B p1_L (by decide +kernel)
def p13_Z : List SliceD := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,6,[1, 2, 3, 4]),(0xcccccccccccccccccccccccccccccccc,6,[0, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff00,5,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]),(0xf000f000f000f000f000f000f000f000,4,[0, 1, 4]),(0xf0f00000f0f00000f0f00000f0f00000,4,[0, 1, 3]),(0xff000000ff000000ff000000ff000000,4,[0, 1, 2]),(0x55555555555555555555555555555555,3,[1, 2, 3, 4]),(0x8080808080808080808080808080808,1,[3, 4]),(0x33333333333333333333333333333333,3,[0, 2, 3, 4]),(0x50505050505050505050505050505050,2,[1, 3, 4]),(0x55005500550055005500550055005500,2,[1, 2, 4]),(0x55550000555500005555000055550000,2,[1, 2, 3]),(0xf000f000f000f000f000f000f000f,2,[0, 1, 4]),(0xf0f00000f0f00000f0f00000f0f,2,[0, 1, 3]),(0x88888888888888888888888888888888,2,[2, 3, 4]),(0x30303030303030303030303030303030,2,[0, 3, 4]),(0x880088008800880088008800880088,1,[2, 4]),(0x50005000500050005000500050005000,1,[1, 4]),(0x8888000088880000888800008888,1,[2, 3]),(0xff000000ff000000ff000000ff,2,[0, 1, 2]),(0x33003300330033003300330033003300,2,[0, 2, 4]),(0x33330000333300003333000033330000,2,[0, 2, 3]),(0x50500000505000005050000050500000,1,[1, 3]),(0x20202020202020202020202020202020,1,[3, 4]),(0xc0c00000c0c00000c0c00000c0c,1,[0, 3]),(0xc000c000c000c000c000c000c000c,1,[0, 4]),(0x22002200220022002200220022002200,1,[2, 4]),(0xcc000000cc000000cc000000cc,1,[0, 2]),(0x22220000222200002222000022220000,1,[2, 3]),(0x40404040404040404040404040404040,1,[3, 4]),(0xa0a00000a0a00000a0a00000a0a,1,[1, 3]),(0xa000a000a000a000a000a000a000a,1,[1, 4]),(0x44004400440044004400440044004400,1,[2, 4]),(0xaa000000aa000000aa000000aa,1,[1, 2]),(0x44440000444400004444000044440000,1,[2, 3]),(0x30003000300030003000300030003000,1,[0, 4]),(0x30300000303000003030000030300000,1,[0, 3]),(0x55000000550000005500000055000000,1,[1, 2]),(0x33000000330000003300000033000000,1,[0, 2]),(0xa000a000a000a000a000a000a000a000,1,[1, 4]),(0xa0a00000a0a00000a0a00000a0a00000,1,[1, 3]),(0xaa000000aa000000aa000000aa000000,1,[1, 2]),(0xc000c000c000c000c000c000c000c000,1,[0, 4]),(0xc0c00000c0c00000c0c00000c0c00000,1,[0, 3]),(0xcc000000cc000000cc000000cc000000,1,[0, 2]),(0xf0000000f0000000f0000000f0000000,1,[0, 1]),(0xf0000000f0000000f0000000f0,1,[0, 1]),(0xf0000000f0000000f0000000f00,1,[0, 1]),(0xf0000000f0000000f0000000f0000,1,[0, 1])]
theorem p13_Y : ∀ s ∈ p13_Z, SliceN p13_R p13_T s := by
  unfold p13_Z
  simp only [List.forall_mem_cons]
  exact ⟨p13_S0,p13_S1,p13_S2,p13_S3,p13_S4,p13_S5,p13_S6,p13_S7,p13_S8,p13_S9,p13_S10,p13_S11,p13_S12,p13_S13,p13_S14,p13_S15,p13_S16,p13_S17,p13_S18,p13_S19,p13_S20,p13_S21,p13_S22,p13_S23,p13_S24,p13_S25,p13_S26,p13_S27,p13_S28,p13_S29,p13_S30,p13_S31,p13_S32,p13_S33,p13_S34,p13_S35,p13_S36,p13_S37,p13_S38,p13_S39,p13_S40,p13_S41,p13_S42,p13_S43,p13_S44,p13_S45,p13_S46,p13_S47,p13_S48,p13_S49,p13_S50,by simp⟩
def p13_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(1,[(0,0,1)]),(5,[]),(6,[]),(1,[(2,0,1)]),(1,[(0,0,2)]),(7,[]),(1,[(2,0,2)]),(1,[(0,0,3)]),(1,[(2,0,3)]),(0,[(0,0,1)]),(0,[(2,0,1)]),(0,[(0,0,2)]),(0,[(2,0,2)]),(0,[(0,0,3)]),(0,[(2,0,3)]),(0,[(0,1,2)]),(1,[(0,1,2)]),(0,[(1,1,2)]),(1,[(1,1,2)]),(0,[(2,1,2)]),(1,[(2,1,2)]),(0,[(3,1,2)]),(1,[(3,1,2)]),(0,[(0,1,3)]),(1,[(0,1,3)]),(0,[(1,1,3)]),(1,[(1,1,3)]),(0,[(2,1,3)]),(1,[(2,1,3)]),(0,[(3,1,3)]),(1,[(3,1,3)]),(0,[(0,2,3)]),(1,[(0,2,3)]),(0,[(1,2,3)]),(1,[(1,2,3)]),(0,[(2,2,3)]),(1,[(2,2,3)]),(0,[(3,2,3)]),(1,[(3,2,3)]),(0,[(3,0,1)]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(6,[(0,0,1)]),(14,[]),(5,[(0,0,1)]),(15,[]),(6,[(2,0,1)]),(0,[(1,0,1)]),(16,[]),(17,[]),(18,[]),(1,[(3,0,1)]),(19,[]),(20,[]),(0,[(3,0,2)]),(21,[]),(7,[(0,0,1)]),(1,[(1,0,2)]),(0,[(1,0,2)]),(22,[]),(5,[(2,0,1)]),(1,[(3,0,2)]),(0,[(3,0,3)]),(1,[(1,0,3)]),(0,[(1,0,3)]),(23,[]),(1,[(3,0,3)]),(24,[]),(25,[]),(26,[]),(27,[]),(6,[(0,0,2)]),(28,[]),(29,[]),(5,[(0,0,2)]),(30,[]),(7,[(0,1,2)]),(31,[]),(32,[]),(33,[]),(6,[(0,1,2)]),(34,[]),(35,[]),(5,[(0,1,2)]),(36,[]),(37,[]),(38,[]),(39,[]),(40,[]),(7,[(2,0,1)]),(5,[(3,0,1)]),(6,[(3,0,1)]),(41,[]),(7,[(0,0,2)]),(6,[(3,0,2)]),(42,[]),(1,[(0,0,1),(0,1,2)]),(1,[(3,1,2),(0,0,1)]),(1,[(0,0,1),(0,1,3)]),(1,[(3,1,3),(0,0,1)]),(1,[(1,0,1)]),(7,[(3,0,1)]),(7,[(3,0,2)]),(43,[]),(1,[(0,0,2),(0,1,2)]),(1,[(2,1,2),(0,0,2)]),(1,[(0,0,2),(0,2,3)]),(1,[(3,2,3),(0,0,2)]),(1,[(0,0,3),(0,1,3)]),(1,[(2,1,3),(0,0,3)]),(1,[(0,0,3),(0,2,3)]),(1,[(2,2,3),(0,0,3)]),(44,[]),(6,[(3,1,2)]),(45,[]),(5,[(3,1,2)]),(0,[(0,0,1),(0,1,2)]),(0,[(3,1,2),(0,0,1)]),(0,[(0,0,1),(0,1,3)]),(0,[(3,1,3),(0,0,1)]),(7,[(3,1,2)]),(46,[]),(0,[(0,0,2),(0,1,2)]),(0,[(2,1,2),(0,0,2)]),(0,[(0,0,2),(0,2,3)]),(0,[(3,2,3),(0,0,2)]),(0,[(0,0,3),(0,1,3)]),(0,[(2,1,3),(0,0,3)]),(0,[(0,0,3),(0,2,3)]),(0,[(2,2,3),(0,0,3)]),(47,[]),(0,[(0,1,2),(1,1,2)]),(1,[(0,1,2),(1,1,2)]),(0,[(0,1,3),(1,1,3)]),(1,[(0,1,3),(1,1,3)]),(0,[(0,2,3),(1,2,3)]),(1,[(0,2,3),(1,2,3)]),(0,[(0,0,1),(1,2,4)]),(0,[(0,0,1),(1,3,4)]),(0,[(1,0,1),(2,0,1)]),(0,[(0,0,1),(1,0,1)]),(1,[(3,0,1),(2,0,1)]),(0,[(3,0,1),(2,0,1)]),(0,[(3,0,1),(0,0,1)]),(1,[(2,0,1),(3,0,1)]),(0,[(2,0,1),(3,0,1)]),(0,[(0,0,1),(2,2,4)]),(1,[(0,0,1),(2,2,4)]),(0,[(0,0,1),(3,1,3)]),(1,[(0,0,1),(2,3,4)]),(0,[(0,0,1),(2,3,4)]),(1,[(0,1,2),(2,0,1)]),(0,[(0,1,2),(2,0,1)]),(0,[(0,0,1),(3,1,2)]),(1,[(3,1,2),(2,0,1)]),(0,[(3,1,2),(2,0,1)]),(1,[(0,1,3),(2,0,1)]),(0,[(0,1,3),(2,0,1)]),(0,[(3,1,3),(2,0,1)]),(0,[(1,0,1),(0,0,1)]),(0,[(0,0,1),(3,0,1)]),(1,[(3,0,1),(0,0,1)]),(0,[(1,1,2),(1,0,1)]),(0,[(1,1,2),(3,0,1)]),(0,[(3,0,1),(2,1,2)]),(0,[(3,0,1),(1,1,2)]),(0,[(2,1,2),(3,0,1)]),(0,[(3,0,1),(1,1,3)]),(0,[(3,0,1),(2,1,3)]),(0,[(0,0,2),(1,1,4)]),(0,[(0,0,2),(2,1,4)]),(0,[(0,0,2),(1,3,4)]),(0,[(1,0,2),(2,0,2)]),(0,[(0,0,2),(1,0,2)]),(1,[(3,0,2),(2,0,2)]),(0,[(3,0,2),(2,0,2)]),(0,[(3,0,2),(0,0,2)]),(1,[(2,0,2),(3,0,2)]),(0,[(0,0,2),(2,0,2)]),(0,[(2,0,2),(3,0,2)]),(0,[(0,0,2),(1,0,1)]),(1,[(0,0,2),(2,1,4)]),(1,[(0,0,2),(2,3,4)]),(0,[(0,0,2),(2,3,4)]),(1,[(0,1,2),(2,0,2)]),(0,[(0,1,2),(2,0,2)]),(0,[(0,1,2),(0,0,4)]),(0,[(0,0,2),(2,1,2)]),(0,[(2,1,2),(2,0,2)]),(0,[(0,2,3),(2,0,2)]),(0,[(0,0,2),(3,2,3)]),(1,[(3,2,3),(2,0,2)]),(0,[(3,2,3),(2,0,2)]),(1,[(1,0,2),(0,0,2)]),(1,[(1,0,2),(2,0,2)]),(0,[(1,0,2),(0,0,2)]),(0,[(0,0,2),(3,0,2)]),(1,[(3,0,2),(0,0,2)]),(0,[(3,0,2),(1,1,2)]),(0,[(3,0,2),(3,1,2)]),(0,[(3,0,2),(1,2,3)]),(0,[(3,0,2),(2,2,3)]),(0,[(2,2,3),(1,0,2)]),(0,[(2,2,3),(3,0,2)]),(0,[(0,0,3),(1,1,4)]),(0,[(0,0,3),(2,2,4)]),(0,[(1,0,3),(2,0,3)]),(0,[(0,0,3),(1,0,3)]),(0,[(0,0,3),(3,0,3)]),(1,[(3,0,3),(2,0,3)]),(0,[(3,0,3),(2,0,3)]),(1,[(2,0,3),(3,0,3)]),(0,[(2,0,3),(3,0,3)]),(0,[(2,0,3),(0,0,3)]),(0,[(0,0,3),(3,0,1)]),(0,[(0,0,3),(2,1,4)]),(0,[(0,0,3),(1,0,1)]),(1,[(0,0,3),(2,1,4)]),(0,[(0,0,3),(1,2,4)]),(0,[(0,0,3),(1,0,2)]),(1,[(0,0,3),(2,2,4)]),(1,[(0,1,3),(2,0,3)]),(0,[(0,1,3),(2,0,3)]),(1,[(0,0,3),(0,1,4)]),(0,[(0,0,3),(2,1,3)]),(0,[(2,1,3),(2,0,3)]),(0,[(0,2,3),(2,0,3)]),(1,[(0,0,3),(0,2,4)]),(0,[(0,0,3),(2,2,3)]),(0,[(2,2,3),(2,0,3)]),(0,[(1,0,3),(0,0,3)]),(1,[(3,0,3),(0,0,3)]),(0,[(3,0,3),(0,0,3)]),(0,[(3,0,3),(1,1,3)]),(1,[(3,0,3),(1,1,3)]),(0,[(3,0,3),(3,1,3)]),(1,[(3,1,3),(3,0,3)]),(0,[(3,0,3),(1,2,3)]),(1,[(3,0,3),(1,2,3)]),(0,[(3,0,3),(3,2,3)]),(1,[(3,2,3),(3,0,3)]),(1,[(0,0,1),(0,2,4)]),(1,[(0,0,2),(0,1,4)]),(1,[(0,0,1),(0,3,4)]),(7,[(0,0,2),(0,1,2)]),(7,[(0,0,1),(0,1,2)]),(7,[(0,0,1),(0,0,2)]),(48,[]),(49,[]),(1,[(0,1,3),(0,0,1)]),(50,[]),(1,[(0,0,2),(0,3,4)]),(5,[(3,0,2)]),(14,[(0,0,1)]),(6,[(0,0,2),(0,1,2)]),(1,[(0,2,3),(0,0,2)]),(1,[(0,2,3),(2,0,2)]),(0,[(0,0,1),(0,2,4)]),(0,[(0,0,1),(0,3,4)]),(0,[(0,1,2),(0,0,1)]),(0,[(0,1,3),(0,0,1)]),(0,[(0,0,3),(0,2,4)]),(0,[(0,1,2),(0,0,2)]),(0,[(0,0,2),(0,1,4)]),(0,[(0,2,3),(0,0,2)]),(0,[(0,1,3),(0,0,3)]),(0,[(0,0,3),(0,1,4)]),(0,[(0,2,3),(0,0,3)]),(0,[(2,0,1),(0,0,1)]),(0,[(2,0,1),(0,2,4)]),(0,[(2,0,1),(0,3,4)]),(5,[(2,0,2)]),(0,[(2,0,1),(0,1,2)]),(0,[(2,0,1),(3,1,2)]),(0,[(3,1,2),(0,0,4)]),(0,[(2,0,1),(0,1,3)]),(0,[(2,0,1),(3,1,3)]),(0,[(3,1,2),(2,1,2)]),(0,[(2,1,2),(3,1,2)]),(0,[(3,1,2),(1,0,2)]),(0,[(0,2,3),(3,1,4)]),(0,[(3,1,2),(0,2,3)]),(0,[(3,1,2),(3,2,3)]),(0,[(3,1,3),(2,1,3)]),(0,[(2,1,3),(3,1,3)]),(0,[(2,1,3),(0,1,3)]),(0,[(0,1,3),(0,0,4)]),(0,[(3,1,3),(1,0,3)]),(0,[(3,1,3),(2,2,3)]),(1,[(0,0,1),(3,1,2)]),(1,[(0,0,1),(3,1,3)]),(5,[(1,0,1)]),(6,[(1,0,1)]),(0,[(3,1,2),(2,3,4)]),(1,[(2,0,2),(0,0,2)]),(0,[(2,0,2),(0,0,2)]),(0,[(2,0,2),(0,1,2)]),(0,[(2,0,2),(2,1,2)]),(0,[(2,1,2),(0,0,4)]),(0,[(2,0,2),(0,2,3)]),(0,[(2,0,2),(3,2,3)]),(0,[(3,2,3),(0,0,4)]),(0,[(2,1,2),(1,0,1)]),(0,[(2,1,2),(0,1,3)]),(0,[(3,2,3),(2,2,3)]),(0,[(2,2,3),(3,2,3)]),(7,[(2,0,2)]),(0,[(3,2,3),(1,0,3)]),(0,[(3,2,3),(0,1,3)]),(0,[(3,2,3),(2,1,3)]),(1,[(0,0,2),(2,1,2)]),(1,[(0,0,2),(3,2,3)]),(7,[(1,0,1)]),(0,[(0,2,3),(0,0,4)]),(0,[(2,1,2),(2,3,4)]),(1,[(2,0,3),(0,0,3)]),(0,[(2,0,3),(0,1,3)]),(0,[(2,0,3),(2,1,3)]),(0,[(2,1,3),(0,0,4)]),(0,[(2,0,3),(2,2,3)]),(0,[(2,0,3),(0,2,3)]),(0,[(2,2,3),(0,0,4)]),(0,[(2,1,3),(1,0,1)]),(0,[(2,2,3),(0,1,2)]),(0,[(2,2,3),(2,1,2)]),(1,[(0,0,3),(2,1,3)]),(1,[(0,0,3),(2,2,3)]),(1,[(0,2,3),(2,0,3)]),(1,[(2,2,3),(2,0,3)]),(1,[(2,1,3),(2,0,3)]),(0,[(2,2,3),(2,1,4)]),(7,[(1,0,2)]),(1,[(3,1,2),(2,1,2)]),(1,[(2,1,2),(3,1,2)]),(7,[(2,1,2)]),(5,[(1,1,2)]),(0,[(0,2,3),(1,0,2)]),(1,[(3,1,3),(2,1,3)]),(1,[(2,1,3),(3,1,3)]),(0,[(0,2,3),(3,0,3)]),(1,[(3,1,3),(2,2,3)]),(1,[(2,1,2),(3,0,1)]),(0,[(0,1,3),(1,0,1)]),(1,[(2,1,2),(0,1,3)]),(1,[(3,2,3),(2,2,3)]),(1,[(2,2,3),(3,2,3)]),(1,[(0,1,3),(0,0,3)]),(1,[(2,1,3),(0,0,4)]),(1,[(0,2,3),(0,0,3)]),(1,[(2,2,3),(0,0,4)]),(1,[(2,1,3),(1,0,1)]),(1,[(2,1,3),(3,0,1)]),(0,[(0,1,2),(1,0,1)]),(0,[(0,1,2),(3,0,1)]),(1,[(2,1,3),(3,1,2)]),(1,[(2,2,3),(3,0,2)]),(0,[(0,1,2),(1,0,2)]),(5,[(2,1,2)]),(1,[(1,1,2),(0,1,2)]),(1,[(1,1,3),(0,1,3)]),(1,[(1,2,3),(0,2,3)]),(7,[(1,1,2)]),(5,[(0,0,1),(2,2,3)]),(0,[(0,0,1),(2,0,3)]),(0,[(1,0,1),(0,3,4)]),(0,[(0,0,1),(0,0,2)]),(0,[(0,0,1),(0,0,3)]),(0,[(1,0,1),(0,2,4)]),(6,[(0,0,1),(1,0,1)]),(5,[(0,0,1),(1,0,1)]),(7,[(0,0,1),(1,0,1)]),(5,[(1,0,2)]),(0,[(0,0,2),(2,3,4),(1,1,4)]),(7,[(0,0,1),(2,2,3)]),(0,[(0,0,2),(2,1,4),(1,3,4)]),(0,[(0,0,2),(2,1,4),(2,3,4)]),(0,[(1,0,2),(0,1,4)]),(0,[(1,0,2),(0,3,4)]),(0,[(0,0,2),(0,0,1)]),(0,[(1,0,3),(0,1,4)]),(0,[(1,0,3),(0,2,4)]),(0,[(0,0,3),(0,0,1)]),(0,[(0,0,3),(2,0,1)]),(7,[(0,0,2),(0,0,1)]),(5,[(0,0,2),(0,1,2)]),(5,[(0,0,1),(0,0,2)]),(5,[(3,0,2),(0,0,1)]),(5,[(3,1,2),(3,0,2)]),(7,[(0,1,2),(0,0,1)]),(7,[(0,1,2),(0,0,2)]),(1,[(0,0,1),(1,2,4)]),(1,[(0,1,2),(0,0,1)]),(7,[(0,0,2),(0,1,3)]),(0,[(3,1,2),(2,0,4)]),(0,[(0,0,2),(0,3,4)]),(7,[(3,0,2),(0,0,1)]),(7,[(3,1,2),(3,0,2)]),(5,[(0,0,2),(0,0,1)]),(5,[(0,0,1),(0,1,2)]),(1,[(0,0,3),(1,2,4)]),(5,[(0,1,2),(0,0,2)]),(5,[(0,1,2),(0,0,1)]),(5,[(0,0,2),(0,1,3)]),(5,[(0,0,1),(0,2,3)]),(5,[(0,1,2),(0,0,3)]),(5,[(3,1,2),(0,0,1)]),(7,[(3,1,2),(0,0,1)]),(0,[(1,1,2),(0,1,2)]),(0,[(1,1,3),(0,1,3)]),(0,[(1,2,3),(0,2,3)]),(6,[(3,0,2),(0,0,1)]),(6,[(3,1,2),(3,0,2)]),(6,[(2,1,2)]),(0,[(3,2,3),(2,1,4)]),(6,[(1,0,2)]),(6,[(2,0,2)]),(6,[(3,1,2),(0,0,1)]),(0,[(0,0,3),(1,1,2)]),(6,[(1,0,1),(0,2,3)]),(7,[(1,0,1),(0,2,3)]),(5,[(1,0,1),(0,2,3)]),(0,[(2,1,3),(2,2,4)]),(0,[(3,1,3),(2,2,4)]),(0,[(0,0,3),(2,1,2)]),(0,[(1,0,2),(3,1,4)]),(0,[(1,0,2),(3,3,4)]),(0,[(1,0,3),(3,1,4)]),(0,[(1,0,3),(3,2,4)]),(0,[(0,1,3),(3,0,1)]),(0,[(0,1,2),(3,0,2)]),(0,[(0,2,3),(3,0,2)]),(0,[(0,1,3),(1,0,3)]),(0,[(0,1,3),(3,0,3)]),(0,[(0,2,3),(1,0,3)]),(6,[(0,0,1),(2,0,2)])]
def p13_P : List (Nat × Nat) := [(28,29),(28,30),(5,7),(10,11),(26,30),(6,7),(22,30),(14,30),(9,11),(25,29),(21,29),(13,29),(3,7),(3,11),(3,19),(18,19),(2,11),(4,7),(2,7),(8,11),(17,19),(16,19),(1,11),(1,7),(3,15),(3,23),(3,27),(17,29),(9,29),(1,19),(20,29),(12,29),(24,30),(24,29),(20,30),(12,30),(13,15),(2,19),(21,23),(18,30),(10,30),(25,27),(5,29),(6,30),(14,15),(22,23),(26,27),(16,29),(8,29),(16,30),(8,30),(4,29),(4,30),(11,14),(11,13),(7,13),(7,21),(0,7),(0,11)]
def p13_K : List CutV := p13_C.map (mkCut p13_Z)
theorem p13_W : ∀ c ∈ p13_K, CutP p13_R p13_T c := cutsGood p13_Y (by decide +kernel)
theorem p13_Q : p13_P.all (sepOK p13_T) = true := by decide +kernel
noncomputable def p13_D8 : List StD := [
([w0,w1,w2,w3,w30],[0,1],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],[[100,101,0,1,102],[103,104,0,100],[105,106,0,100],[103,107,0,100],[108,109,1,101],[102,110,1,101],[102,111,1,101],[112,113,104,106],[112,114,104,107],[113,114,106,107]])]
noncomputable def p13_D7 : List StD := [
([w31,w0,w1,w2,w3,w30],[0,1,2,3,4],[9,12,10,13,11,14,4,0,6,7,1],[[0,1],[0],[100,2,101],[102,3,103],[104,4,105],[0,1],[0,106,107],[0,108,107],[0,109,107],[1,100,110],[1,102,110],[1,104,110],[101,103,100,102],[101,105,100,104],[103,105,102,104]]),
([w34,w0,w1,w2,w3,w30],[0,2,5,6,7],[8,2,13,10,14,11,1,4,15,16,3],[[0,1],[100,2,101],[0],[102,3,103],[104,4,105],[0,106,2],[0,1,107],[0,108,3,109],[0,110,4,108],[100,1,2,101],[101,103,2,3,100],[100,105,2,4,104],[3,102,107,1,103],[4,104,107,1,105],[102,104,3,4,103]]),
([w35,w0,w1,w2,w3,w30],[0,6,1,7,8],[3,8,13,14,0,17,4,5,10,11],[[0,1,100],[1,2,101],[0],[1,3,102],[1,3,103],[0,104,4,105],[0,1,106],[0,1,107],[0,3,107],[1,101,4],[1,108,4,102],[3,109,4,101],[1,102,3],[1,3,103],[1,3,102]]),
([w37,w0,w1,w2,w3,w30],[0,3,9,6,10],[2,8,12,9,14,11,1,15,18,6,5],[[0,1],[100,2,101],[102,3,103],[0],[104,4,105],[0,106,2],[0,107,3,108],[0,1,109],[0,110,4,107],[101,103,2,3,100],[100,1,2,101],[100,105,2,4,104],[3,102,1,109,103],[102,104,3,4,103],[4,104,109,1,105]]),
([w38,w0,w1,w2,w3,w30],[0,6,1,10,11],[5,2,12,14,0,19,3,6,9,11],[[0,1,100],[1,2,101],[1,3,102],[0],[1,3,103],[0,104,4,105],[0,1,106],[0,1,107],[0,3,106],[1,108,4,102],[1,101,4],[3,109,4,101],[1,102,3],[1,3,102],[1,3,103]]),
([w79,w0,w1,w2,w3,w30],[0,10,12,7],[2,20,12,9,13,10,1,3,18,5,7],[[0,1],[100,2,101],[102,3,103],[104,1,105],[0],[0,106,2],[0,107,3,108],[0,109,1,107],[0,1,110],[101,103,2,3,100],[100,105,1,2,104],[100,1,2,101],[102,104,1,3,103],[3,102,1,110,103],[1,104,3,110,105]]),
([w80,w0,w1,w2,w3,w30],[0,10,1,7,13],[5,2,12,13,0,21,15,7,9,10],[[0,1,100],[1,2,101],[1,3,102],[1,3,103],[0],[0,104,4,105],[0,3,106],[0,1,106],[0,1,107],[3,108,4,102],[1,109,4,101],[1,101,4],[1,3,102],[1,3,102],[1,103,3]]),
([w0,w40,w1,w2,w3,w30],[14,1,7,6],[3,5,0,6,7,13,14,9,20,22,8],[[100,0,101],[1,102,0],[100,0,2,101],[101,103,0,3,100],[100,104,0,2,102],[1,2],[1],[105,3,103],[106,2,104],[1,2,107],[1,108,3,109],[1,110,2,108],[3,105,107,2,103],[2,106,107,3,104],[105,106,2,3,103]]),
([w41,w0,w1,w2,w3,w30],[7,0,1,6,15],[3,8,13,14,1,17,6,7,9,2],[[0,1,100],[0,2,101],[0,2],[0,3,102],[0,3,103],[2,104,4,105],[0,100,4],[3,106,4,102],[0,107,4,100],[0,2,108],[2,3,109],[0,2,109],[0,3,102],[0,103,3],[0,3,102]]),
([w0,w43,w1,w2,w3,w30],[16,1,6,10],[5,3,0,4,7,12,14,20,23,10,2],[[100,0,101],[1,102,0],[101,103,0,2,100],[100,0,2,101],[100,104,0,3,102],[1,2],[105,2,103],[1],[106,3,104],[1,107,2,108],[1,2,109],[1,110,3,107],[2,105,3,109,103],[105,106,2,3,103],[3,106,109,2,104]]),
([w44,w0,w1,w2,w3,w30],[6,0,1,10,17],[5,2,12,14,1,19,4,7,8,10],[[0,1,100],[0,2,101],[0,3,102],[0,2],[0,3,103],[2,104,4,105],[0,106,4,102],[0,100,4],[3,107,4,100],[0,2,108],[0,2,109],[2,3,108],[0,102,3],[0,3,102],[0,3,103]]),
([w0,w81,w1,w2,w3,w30],[18,1,7,10],[5,15,0,4,6,12,13,8,23,2,11],[[100,0,101],[1,102,0],[101,103,0,2,100],[100,104,0,3,102],[100,0,2,101],[1,2],[105,2,103],[106,3,104],[1],[1,107,2,108],[1,109,3,107],[1,2,110],[105,106,2,3,103],[2,105,3,110,103],[3,106,2,110,104]]),
([w82,w0,w1,w2,w3,w30],[10,0,1,7,19],[5,2,12,13,1,21,4,6,20,11],[[0,1,100],[0,2,101],[0,3,102],[0,3,103],[0,2],[2,104,4,105],[3,106,4,102],[0,107,4,100],[0,100,4],[2,3,108],[0,2,108],[0,2,109],[0,3,102],[0,3,102],[0,103,3]]),
([w0,w1,w46,w2,w3,w30],[20,21,6,7,10],[0,1,2,5,3,7,8,11,14,13,12],[[100,101,0,1,102],[2,103,0],[2,104,0],[2,103,0],[103,105,0,3,100],[2,102,1],[2,106,1],[2,102,1],[102,107,1,3,101],[2,4],[2,3],[2,108,3],[2,109,110],[2,110,4,108],[2,109,3,108]]),
([w0,w1,w2,w3,w9,w30],[22,23,7,10,6],[0,1,2,4,3,6,5,15,7,9,10,20,11,12,14,13],[[100,101,0,1,102],[2,103,0,104],[3,105,0,106],[2,107,0],[2,108,0,104],[2,109,1,103],[3,110,1,102],[2,111,1],[2,112,1,102],[2,3],[2,113],[2,114,3,4],[2,3,115],[2,3,114,4],[2,114,4]]),
([w47,w0,w1,w2,w3,w30],[10,0,1,6,7,24,25],[5,2,12,0,1,4,3,7,9,11,13,24,14],[[0,1,100],[0,2,101],[0,3,102],[0,4],[0,3],[103,104,5,6,100],[3,105,5,106],[0,100,5],[0,107,5,100],[3,108,6,105],[0,101,6],[0,109,6,101],[0,3,110,111],[0,3,112],[0,110,3,112]]),
([w48,w0,w1,w2,w3,w30],[6,0,1,10,7,26,27],[3,8,13,0,1,6,5,7,10,11,12,24,14],[[0,1,100],[0,2,101],[0,3],[0,102],[0,3,4],[103,104,5,6,100],[0,100,5],[0,105,5,106],[4,107,5,100],[0,101,6],[0,108,6,105],[4,109,6,101],[0,110,4,111],[0,4,110,112],[0,4,112]]),
([w0,w1,w83,w2,w3,w30],[28,29,7,6,10],[0,1,2,5,3,6,8,10,13,12,14],[[100,101,0,1,102],[2,103,0],[2,104,0],[103,105,0,3,100],[2,103,0],[2,102,1],[2,106,1],[102,107,1,3,101],[2,102,1],[2,4],[2,108,3],[2,3],[2,109,4,108],[2,110,109],[2,110,3,108]]),
([w0,w1,w2,w3,w30,w84],[30,31,7,10,6],[0,1,2,4,3,6,5,7,9,10,11,8,13,12,14],[[100,101,0,1,102],[2,103,0,104],[3,105,0,106],[2,107,0,104],[2,104,0],[2,108,1,103],[3,109,1,102],[2,110,1,102],[2,111,1],[2,3,112],[2,3,4],[2,113],[2,3,112],[2,3,112],[2,114]]),
([w85,w0,w1,w2,w3,w30],[10,0,1,7,6,32,33],[5,2,12,0,1,4,3,6,9,10,13,14,25],[[0,1,100],[0,2,101],[0,3,102],[0,3],[0,4],[103,104,5,6,100],[3,105,5,106],[0,107,5,100],[0,100,5],[3,108,6,105],[0,109,6,101],[0,101,6],[0,3,110],[0,3,111,112],[0,110,3]]),
([w86,w0,w1,w2,w3,w30],[6,0,1,10,7,34,35],[15,20,14,0,1,6,7,5,10,11,12,13,25],[[0,1,100],[0,2,101],[0,3],[0,4],[0,4,102],[103,104,5,6,100],[0,100,5],[0,105,5,100],[4,106,5,107],[0,101,6],[0,108,6,101],[4,109,6,106],[0,110,4,111],[0,4,110,112],[0,4,111]]),
([w0,w1,w2,w87,w3,w30],[36,37,7,10,6],[0,1,2,3,4,5,8,9,12,13,14],[[100,101,0,1,102],[103,104,0,2,100],[3,103,0],[3,105,0],[3,103,0],[106,107,1,2,101],[3,102,1],[3,102,1],[3,102,1],[3,108,2],[3,109,2,108],[2,3,110,4,108],[2],[3,4],[2,3,110,109]]),
([w0,w1,w2,w3,w30,w88],[38,39,6,10,7],[0,1,2,4,18,6,5,7,9,10,11,12,13,14],[[100,101,0,1,102],[2,103,0,104],[2,105,0,106],[3,107,0,106],[2,106,0],[2,108,1,103],[2,109,1,102],[3,110,1,102],[2,102,1],[2,111,3],[2,3,111],[2,111,3],[2,3,4],[2,112],[2,3,113]]),
([w89,w0,w1,w2,w3,w30],[7,0,1,10,6,40,41],[3,8,13,0,1,4,6,5,9,10,12,14,26],[[0,1,100],[0,2,101],[0,3],[0,3,102],[0,4],[103,104,5,6,100],[0,105,5,100],[3,106,5,107],[0,100,5],[0,108,6,101],[3,109,6,106],[0,101,6],[0,3,110],[0,110,3],[0,3,111,112]]),
([w90,w0,w1,w2,w3,w30],[6,0,1,10,7,42,43],[15,20,14,0,1,4,7,5,9,11,12,13,26],[[0,1,100],[0,2,101],[0,3],[0,4],[0,3,102],[103,104,5,6,100],[0,105,5,100],[0,100,5],[3,106,5,107],[0,108,6,101],[0,101,6],[3,109,6,106],[0,110,3],[0,3,110],[0,3,111,112]])]
noncomputable def p13_D6 : List StD := [
([w91,w31,w0,w1,w2,w3,w30],[15,8,44,45,5,14,46,47,48,49,50],[13],[[0],[1],[0],[2],[3],[3],[4],[5],[3],[3,6],[3,6],[4,5],[3,5],[3,5],[3,5],[5,4,7],[7,4],[7,4],[6,8],[6,8],[100,9,10]]),
([w91,w0,w1,w2,w3,w30],[14,8,15,44,47,10,5,51,52,53,54,49,50],[13,14,0,15,3,9,20,22,8,27,28,11],[[0,1],[2],[3],[4,100,5],[4,101,5],[4,0,102,6],[6,0,7,102],[8,0,103,9,102],[10,0,104,7,102],[0,6,7,105],[8,4,106,6,9,107],[10,4,108,6,7,106],[10,100,11,7,105,109],[8,101,12,9,105,110],[10,8,100,7,9,111,101]]),
([w31,w0,w1,w2,w49,w3,w30],[55,56,57,44,48,51,1,58,15,46,59,53],[],[[0],[1],[0,2],[3],[4,2],[4,0,2],[1,4],[1,5],[6,1],[4,1],[4,1],[1,4,2],[1,3],[7,2],[7,2],[8],[9,4],[9,4],[2],[2],[10,5,11]]),
([w92,w31,w0,w1,w2,w3,w30],[14,5,56,51,46,53,8,15,47,45],[13],[[0],[1],[0],[2],[3,4],[5,4],[6],[7],[8,3],[8,4],[8,3,4],[6,7],[9,3,7],[9,4],[9,3,4],[8,3,6],[8,4],[8,3,4],[4,3],[4,5],[100,3]]),
([w50,w31,w0,w1,w2,w3,w30],[56,1,14,46,48,60,44,57,58,59,61],[],[[0],[1,0],[0,1],[2],[3,4],[3,4],[5],[6],[7],[4,3],[4,3],[5,6],[6,8],[4,3],[4,3],[4,5],[8,3],[8,3],[3,4],[3,4],[9,10]]),
([w50,w0,w1,w2,w3,w30],[44,60,14,46,6,48,7,54,51,52,53,59,62],[13,10,14,11,0,3,15,8,23],[[0,1],[0,1],[2],[3,100,4,5,101],[3,102,6,5,103],[1,0,104],[7,0,105,8,104],[9,0,106,10,104],[7,0,105,8,104],[7,1,107,5,108],[9,1,101,10],[7,1,103,8],[11,3,100,5,101],[12,3,102,5,103],[7,9,100,8,10,101]]),
([w93,w31,w0,w1,w2,w3,w30],[17,11,47,63,9,16,59,45,48,49,50],[12],[[0],[1],[0],[2],[3],[2],[4],[5],[2,6],[2],[2,6],[4,2],[7,5],[4,5,7],[7,5],[2,4],[2,4],[2,4],[6,8,9],[100,8,10],[6,9]]),
([w93,w0,w1,w2,w3,w30],[16,11,17,59,6,63,7,9,52,53,64,65,48,50],[12,14,0,15,5,20,23,10,2,27,11],[[0,1],[2],[3,100,4],[5],[3,101,6],[7,0,102],[8,0,103,9,102],[7,0,9,102],[10,0,104,11,102],[8,7,105,9,106],[0,7,9,107],[10,7,108,11,105],[3,100,11,12,107,109],[10,8,100,11,9,110,101],[3,101,13,9,107,110]]),
([w31,w0,w1,w2,w3,w51,w30],[66,67,49,6,59,46,63,53,68,17],[],[[0],[1],[2,3,4],[3,5],[6],[2,4],[0,1],[2,1],[0,7,1],[0,1],[2,1],[8,0],[0,2],[1,0],[8,0],[4,2],[2],[5,7],[9],[4,2],[2]]),
([w94,w31,w0,w1,w2,w3,w30],[16,9,50,59,67,53,69,17,48,47,11,49],[12],[[0],[1],[0],[2,3],[4],[5,3],[6],[7],[2,3],[2,5],[8,3],[7,2],[2,3],[2,5,7],[8,3],[9,3],[9,5,10],[9,2,3],[3,8,11],[100,2],[3,2,5]]),
([w52,w31,w0,w1,w2,w3,w30],[67,1,59,49,16,70,63,46,68,61],[],[[0],[1,0],[0,1],[2,3],[4],[2,3],[5],[6],[3,2],[7],[3,2],[5,6],[3,2],[6,8],[3,2],[8,2],[3,5],[8,2],[2,3],[7,9],[2,3]]),
([w52,w0,w1,w2,w3,w30],[63,70,59,6,49,16,7,52,53,64,65,46,62],[12,9,14,11,0,15,5,2,22],[[0,1],[0,1],[2,100,3,4,101],[5],[2,102,6,4,103],[1,0,104],[7,0,105,8,104],[7,0,105,8,104],[9,0,106,10,104],[7,1,101,8],[7,1,107,4,108],[9,1,103,10],[2,11,100,4,101],[9,7,100,10,8,101],[12,2,102,4,103]]),
([w95,w31,w0,w1,w2,w3,w30],[19,13,49,48,71,12,18,62,68,47,50],[12],[[0],[1],[0],[2],[3],[4],[5],[6],[2,7],[3,7],[2],[5,6],[2,6],[3,6],[2,6],[8,3,5],[9,2,5],[6,5,8],[100,2],[7,3,10],[7,2,10]]),
([w95,w0,w1,w2,w3,w30],[18,13,19,49,6,48,71,12,54,51,64,68,50],[12,13,0,3,5,8,23,2,11,10,28],[[0,1],[2],[3,100,4],[5,101,4],[6],[7,0,102],[8,0,103,9,102],[10,0,104,11,102],[7,0,9,102],[8,7,105,5,106],[10,7,107,3,105],[0,7,9,108],[10,8,100,3,5,109,101],[10,100,12,5,108,110],[8,101,9,3,108,109]]),
([w31,w0,w1,w2,w3,w30,w96],[72,73,50,59,46,7,71,51,74,62,19],[],[[0],[1],[2,3],[2,4],[5,3],[6],[0,1],[2,1],[2,1],[0,7,1],[0,1],[8,0],[8,0],[0,2],[1,0],[3,7,4],[4,2,9],[2],[3,2,9],[2],[10]]),
([w97,w31,w0,w1,w2,w3,w30],[18,12,50,62,73,13,19,48,7,68,47],[12],[[0],[1],[0],[2,3],[2,3],[4],[5],[6],[2,3],[2,3],[7,8],[5,6],[2,3],[2,3],[7,6],[9,3],[10,3],[9,2,5],[100,7,9],[3,2],[3,2]]),
([w98,w31,w0,w1,w2,w3,w30],[73,1,62,50,18,75,71,59,74,76,46],[],[[0],[1,0],[0,1],[2,3],[2,3],[4],[5],[6],[3,2],[3,2],[7],[5,6],[3,2],[3,2],[6,8],[8,2],[8,2],[3,5],[7,9,10],[2,3],[2,3]]),
([w98,w0,w1,w2,w3,w30],[71,75,62,7,50,6,18,54,51,64,65,46,59],[12,9,13,10,0,3,5,2,29],[[0,1],[0,1],[2,100,3,4,101],[2,102,5,4,103],[6],[1,0,104],[7,0,105,8,104],[9,0,106,10,104],[7,0,105,8,104],[7,1,101,8],[9,1,103,10],[7,1,107,4,108],[9,7,100,10,8,101],[2,11,100,4,101],[2,12,102,4,103]]),
([w31,w34,w1,w2,w3,w30],[5,7,51,0,50,54,52,6,46,48,53,77,49,78,79],[3,15,0,13,30,14,31,32,10,11],[[0,1,2],[0,3],[0,1,4,5,100],[6,4,101,7,8],[5,9,100,1,8],[0,4,102],[3],[4,103,10,11,102,104],[8,105,2,11,102,106],[0,2,107],[0,108,10],[0,109,2],[8,103,12,2,108],[8,105,4,9,109],[13,14,103,2,10,108]]),
([w31,w37,w1,w2,w3,w30],[9,6,53,0,52,50,59,64,48,80,10,81,51,82,79],[15,5,0,12,33,14,31,9,34,11],[[0,1,2],[0,3],[4,5,100,1,6],[0,1,5,4,100],[7,8,101,9,6,10],[0,5,102],[5,103,2,11,102,104],[3],[6,105,12,11,102,106],[0,107,2],[0,2,108],[0,109,5],[6,103,11,8,107],[13,14,103,5,2,107],[6,105,5,2,109]]),
([w31,w79,w1,w2,w3,w30],[12,7,51,0,54,50,62,64,83,10,48,84,53,65,82,78,49],[3,5,0,12,33,13,30,9,10,35],[[0,1,2],[0,3],[4,5,100,1,6],[7,5,101,8,6,9],[0,1,10,4,100],[0,5,102],[5,103,2,11,102,104],[5,105,12,11,102,106],[3],[0,107,2],[0,108,13],[0,2,109],[14,15,103,13,2,107],[6,103,5,10,107],[6,105,2,16,108]]),
([w31,w0,w40,w2,w3,w30],[14,1,6,15,47,54,52,46,85,7,51,53,86,68,74,87,88],[8,20,0,1,6,7,13,14],[[0,1],[0,2,3],[0,2,4,5,100],[6,4,101,2,7],[5,4,100,8,7,9],[4,0,102,103],[0,10,102],[0,104,11],[0,105,10],[1],[4,106,11,12,103,104],[4,107,10,12,103,105],[7,106,13,10,104],[7,107,14,11,105],[15,16,106,10,11,104]]),
([w31,w0,w43,w2,w3,w30],[16,1,6,17,52,74,59,64,68,89,10,53,90,51,58,91,88],[20,2,0,1,4,7,12,14],[[0,1],[0,2,3],[4,5,100,2,6],[0,2,5,4,100],[7,8,101,9,6,10],[5,0,102,103],[0,104,11],[0,8,102],[0,105,5],[5,106,11,12,103,104],[1],[6,107,13,12,103,105],[6,106,8,14,104],[15,16,106,5,11,104],[6,107,5,8,105]]),
([w31,w0,w81,w2,w3,w30],[18,1,7,19,54,74,62,64,92,10,68,51,93,53,91,87,58],[8,2,0,1,4,6,12,13],[[0,1],[0,2,3],[4,5,100,2,6],[7,5,101,8,6,9],[0,2,10,4,100],[5,0,102,103],[0,104,11],[0,105,10],[0,5,102],[5,106,11,12,103,104],[5,107,13,12,103,105],[1],[14,15,106,10,11,104],[6,106,5,16,104],[6,107,5,10,105]]),
([w31,w0,w1,w46,w2,w3,w30],[69,20,59,46,61,53,1,94,24,26],[],[[0],[1],[0],[0,2],[0,3],[4,2],[1,4],[1,5],[1,5],[1,5],[4,1],[4,6],[2,4],[3,4],[7,2],[8],[9],[2,4],[3,2],[3,4],[2,4]]),
([w31,w0,w1,w2,w3,w9,w30],[69,22,68,58,7,23,49,48,26,24],[14],[[0],[1],[2,0],[3,0],[0],[2,4,100],[1,5],[6,1],[7,1],[1,2],[6,1],[2,5],[3,5],[5,6],[2,5],[2,3],[8],[100,3],[9],[100,2],[100,2]]),
([w47,w31,w0,w1,w2,w3,w30],[6,53,0,1,20,22,25,24,68,46,49],[24,13,14],[[0],[1,2],[1,3],[4],[5],[1],[6],[7],[8,0],[0,9],[8,9],[6,7],[10,1,7],[1,7],[10,7],[8,1,6],[1,6],[8,6],[9,8,100],[9,1],[101,1,102]]),
([w48,w31,w0,w1,w2,w3,w30],[6,53,0,1,22,20,69,26,59,58,27,48],[24,12,14],[[0],[1,2],[1,3],[4],[5],[1],[6],[7],[0,8],[9,0],[9,8],[7,10],[1,7],[11,1,7],[11,7],[1,8],[9,1,10],[9,8],[8,9,100],[101,1,102],[8,1]]),
([w31,w0,w1,w83,w2,w3,w30],[29,28,7,62,76,46,51,95,32,34],[],[[0],[1],[2],[2,3],[4,3],[2,5],[0,1],[1,6],[1,6],[4,1],[1,6],[0,4],[0,4],[7,0],[0,4],[8],[3,4],[9],[5,4],[5,3],[3,4]]),
([w31,w0,w1,w2,w3,w30,w84],[69,30,74,58,7,31,50,48,34,32],[13],[[0],[1],[2,0],[2,0,100],[3,4],[0],[1,5],[6,1],[6,1],[7,1],[1,2],[2,5],[2,5],[3,5],[5,6],[100,3],[2,3],[8],[100,2],[100,2],[9]]),
([w85,w31,w0,w1,w2,w3,w30],[7,51,0,1,28,30,33,32,74,6,46,50],[25,13],[[0],[1,2],[1,3],[4],[1],[5],[6],[7],[8,0],[8,9,10],[0,10],[6,7],[11,1,7],[11,7],[1,7],[8,1,6],[8,6],[1,6],[10,1],[10,8,100],[101,1]]),
([w86,w31,w0,w1,w2,w3,w30],[6,53,0,1,30,51,28,69,34,62,48,58,35],[12,13,25],[[0],[1,2],[1,3],[4],[5],[6],[7],[8],[0,9],[10,0,9],[10,5],[8,10],[1,8],[10,1,8],[10,5,8],[1,9],[11,1,9],[11,5,12],[100,5,101],[9,1,102],[9,1,5]]),
([w31,w0,w1,w2,w87,w3,w30],[37,36,96,6,62,10,59,65,97,40,42],[],[[0],[1],[2,3,4],[5],[3,4],[5,6],[0,1],[2,1],[1,7],[1,7],[1,7],[8,0],[0,2],[0,2],[0,2],[4,2],[6,2],[4,2],[9],[10],[6,4]]),
([w31,w0,w1,w2,w3,w30,w88],[39,38,50,6,68,10,49,74,42,40],[12],[[0],[1],[2,3,100],[2,3],[4,5],[3],[0,1],[2,1],[2,1],[6,1],[1,4],[4,0],[7,0],[4,0],[0,2],[100,4],[100,2],[100,2],[2,4],[8],[9]]),
([w89,w31,w0,w1,w2,w3,w30],[10,65,0,1,36,38,98,40,50,6,59,74,41],[12,26],[[0],[1,2],[1,3],[1],[4],[5],[6],[7],[8,9,10],[8,0],[0,10],[7,8],[8,7],[8,1,7],[1,7],[11,10],[11,1,12],[1,10],[10,1],[100,1],[10,8,101]]),
([w90,w31,w0,w1,w2,w3,w30],[10,65,0,1,38,36,98,42,49,6,62,68,43],[12,26],[[0],[1,2],[1,3],[1],[4],[5],[6],[7],[8,9,10],[0,10],[8,0],[7,8],[8,7],[1,7],[8,1,7],[11,10],[1,10],[11,1,12],[100,1],[10,1],[10,8,101]]),
([w91,w34,w0,w1,w2,w3,w30],[44,15,50,6,49,7,53,5,14,77,48,46,52],[],[[0],[],[1],[0],[2,3],[4,5],[6],[7],[8],[2,9],[4,9],[2,7,8],[8,2],[2,8],[4,8],[8,7,10],[9,4,7],[9,2,7],[11,4,9],[11,2,9],[12,2,4]]),
([w56,w34,w0,w1,w2,w3,w30],[56,6,14,77,46,99,5,15,90,79,93],[],[[0],[1,0],[2],[0,1],[3,1,4],[3,4],[5],[6],[7],[4,3],[4,3],[6,7],[7,8],[9,3,10],[8,3],[6,7],[3,4],[3,4],[4,3],[4,3],[9,8]]),
([w56,w0,w1,w2,w3,w30],[15,99,5,14,77,46,6,10,79,78,100,68,74],[10,13,11,14,0,15,3,9,2],[[0,1,2],[2,3],[0,1,2],[4,100,1,5,6,101],[4,102,7,5,103],[2,0,104],[2,0,1,104],[8,0,105,1,104],[9,0,106,10,104],[2,107,0],[108,2,1,100],[108,2,10,102],[5,101,11,4,100],[5,103,12,1,102],[9,8,101,10,1,100]]),
([w99,w34,w0,w1,w2,w3,w30],[24,6,49,5,101,26,20,79,52,54,50,48],[],[[0],[1],[2,3,4],[0],[5],[2,4],[1],[2,4],[6],[1],[2,4],[2,4],[1,6],[7,1],[2,4],[8,1],[8,1],[9,7,10],[6,2,11],[7,1],[7,1]]),
([w99,w0,w1,w2,w3,w30],[20,6,52,1,101,24,26,10,79,54,102,59,46,64,50],[2,36,14,11,1,3,5,37,8,6,13],[[0,1],[2,100,3,4,101],[1,5],[1,6],[2,102,7,4,103],[0,104,8],[1,0,105],[1,0,106],[9,0,105,10,107],[1,108,11],[1,100,12],[9,103,10,8,102],[0,1,109,110],[13,1,102,10],[9,1,102,14]]),
([w58,w34,w0,w1,w2,w3,w30],[22,6,52,5,49,20,101,26,77,79],[],[[0],[1],[2,3,4],[0,1],[5],[2,4],[1],[2,6],[7],[1],[2,6],[4,6],[1,2],[2,1],[4,6],[2,1],[2,1],[8,9],[4,7],[2,1],[2,1]]),
([w58,w0,w1,w2,w3,w30],[26,6,52,1,49,20,10,79,64,102,59,77,103],[2,8,14,7,1,3,5,12,10,24],[[0,1],[2,100,3,4,101],[0,1],[1,5],[2,102,6,4,103],[0,104,7],[1,0,105],[1,0,106],[8,0,103,9],[1,101,10],[1,11,100],[8,11,100,9,7,102,104],[1,107,108,109],[8,1,102,9],[1,102,12]]),
([w100,w34,w0,w1,w2,w3,w30],[32,7,49,5,104,46,34,28,79,50,52,54,48],[],[[0],[1],[2,3,4],[0],[5,4],[6],[1],[2,4],[7],[5,4],[1],[2,4],[1,7],[8,4,9],[2,1,5],[10,1],[10,2],[11,1],[5,1],[5,9,12],[8,1,2]]),
([w100,w0,w1,w2,w3,w30],[28,7,49,1,104,32,48,10,34,79,102,62,52,64],[2,38,13,10,1,3,5,8,7,14],[[0,1],[2,100,3,4,101],[1,5],[6,102,7,4,103],[1,8],[0,104,9],[1,0,105],[9,0,106,10,105],[1,0,105],[1,107,11],[12,103,2,11,102],[1,100,9],[13,1,102,2],[0,1,108,109],[1,9,102,2]]),
([w101,w34,w0,w1,w2,w3,w30],[30,7,54,5,50,28,101,34,77,78],[],[[0],[1],[2,3,4],[0,1],[2,4],[5],[1],[2,6],[7],[2,8],[1],[4,6],[1,2],[4,7],[2,1],[2,1],[8,6,9],[2,1],[2,1],[4,6],[2,1]]),
([w101,w0,w1,w2,w3,w30],[34,54,7,1,50,10,28,78,64,102,62,77,101],[2,20,13,6,1,3,12,11,25],[[0,1,2],[1,100,3,4,101],[0,2],[1,102,5,4,103],[2,6],[0,104,7],[1,0,105,2],[8,0,103,9],[1,0,105,2],[1,101,2,10],[8,11,100,9,7,102,104],[1,11,100,2],[8,1,102,2,9],[2,106,107,108],[1,102,2,12]]),
([w34,w0,w40,w1,w2,w3,w30],[8,14,54,77,52,5,7,6,86],[],[[0],[1,0],[1,0],[1],[2,3],[4,3],[2,1],[1,5],[1,6],[4,1,7],[2,1,6],[6],[5],[2,7,8],[3,6,8],[5,6],[3,5],[2,5,3],[2,3],[4,3],[2,6]]),
([w34,w0,w40,w1,w3,w30],[14,7,1,44,5,54,85,77,52,6,86],[9,13,27,14,28,4,15,16,3,39,40,20,22,8,11],[[0,1],[0,2,3],[0,2,4,100],[5,101,6,7,100,102],[8,103,1,7,100,104],[4,0,105],[4,0],[8,0,106,9,107],[5,0,108,1,106],[1],[5,101,9,10,105,109],[7,103,1,10,105,110],[8,4,111,9,112],[5,4,113,1,111],[5,8,101,1,9,114,103]]),
([w41,w34,w0,w1,w3,w30],[56,6,15,5,14,7,48,77],[13,14,9,27,28,32,15,3,2],[[0,1],[1,0,2,3],[3,1,4],[1,5,100],[1,5,101],[1],[3,6,102,2],[1,6,100,7,103],[5,6,101,7,104],[3,2,105],[1,2,106],[5,2,107],[1,3,108],[5,3,108],[5,1,100]]),
([w34,w0,w43,w1,w2,w3,w30],[6,52,1,16,77,5,90],[2,3],[[0],[],[1,2,100],[3],[0,4],[1,4],[1,3,101],[3,5],[0,1],[1,0],[6,3],[0],[0,6],[5],[1,6],[1,0],[0,1],[4,5],[4,6],[1,0],[1,0]]),
([w34,w0,w81,w1,w2,w3,w30],[92,54,1,18,77,7,5,93],[2,15],[[0],[],[1,2,100],[3],[1,4],[4,5],[1,3,101],[3,6],[3,5],[7,3],[1,3,5],[5],[5,7],[1,7],[6],[1,5],[4,6],[5,1],[1,4],[4,7],[1,5]]),
([w34,w0,w1,w46,w3,w30],[20,7,54,21,101,6,64,52,10,105],[8,23,12,1,3,15,2,11,14],[[0,1],[2,100,3,4,101],[0,5],[0,5,102],[6,7,102,1,4,8],[0,103,9],[2,0,104,5],[5,0,105],[2,0,104,1,105],[2,100,4,5,9],[5,106,9],[2,107,1,9,103,100],[1],[5,108,1],[2,5,108,1]]),
([w48,w34,w0,w1,w3,w30],[22,7,26,5,20,6,52,27,101,48,106,77],[3,8,40,23,12,1,15,2,14],[[0,1],[1,0,2,100],[1,3,101],[4,1],[1,5,102],[1],[6,101,7,8,103],[5,9,104,2],[1,6,104,8],[2,105,10],[5,2,106],[1,2,100],[5,11,107,10],[1,11,101,10],[1,5,108]]),
([w34,w0,w1,w83,w3,w30],[28,6,52,29,104,7,64,54,10,107],[8,23,12,1,3,15,10,2,13],[[0,1],[2,100,3,4,101],[0,5],[6,7,102,1,4,8],[0,5,102],[0,103,9],[2,0,104,5],[2,0,105,1,104],[5,0,104],[2,100,4,5,9],[2,106,1,9,100,107],[5,100,9],[5,108,1],[1],[5,2,108,1]]),
([w86,w34,w0,w1,w3,w30],[30,7,34,5,6,28,54,35,101,77,48,108],[15,20,39,23,12,1,3,2,13],[[0,1],[1,0,2,100],[1,3,101],[1,4,102],[1,5],[1],[6,101,7,8,103],[4,6,104,9],[1,10,104,2],[2,105,11],[4,2,100],[1,2,106],[4,9,101,11],[1,9,107,11],[1,4,108]]),
([w34,w0,w1,w2,w87,w3,w30],[6,54,37,36,10,52,96,102,7],[2],[[0],[1,2,100],[3],[4],[1,0],[5,4],[6,3],[0,1],[1,3,7],[5,0],[1,3,7],[1,0],[1,6],[5,0],[1,6],[0,6],[1,6,8],[5,0],[8],[0],[0,5]]),
([w0,w102,w1,w2,w3,w30],[68,14,5,8,7,6,77,86],[0,4,5,13,6,14,7,20,8],[[0,1,2,3],[0,1,100,3],[4,1,101],[5,1,102],[4,1,102],[3,4],[1,2,3],[5,6,103,7,104],[4,0,105,7,106],[1,3,4],[5,3,107],[4,0,108,3],[5,103,4],[4,105,5],[4,5,103]]),
([w35,w0,w40,w1,w3,w30],[14,6,5,109,7,58,8,86],[13,14,33,5,39,40,20,8],[[0,1,2],[3,1],[1,2,0],[1,4,100],[1,4,101],[5,0,102,6],[5,0,102,6],[1,0,103],[4,0,103],[1],[1,5,100,7,104],[4,5,101,7,105],[1,5,106,6],[4,5,107,6],[4,1,100]]),
([w93,w37,w0,w1,w2,w3,w30],[63,17,64,6,86,10,53,9,81,16,48,52,50,96],[],[[0],[],[1],[2,3],[0],[4,5],[6],[7],[2,8],[9],[4,8],[10,7,9],[11,8,12],[9,4],[2,8,4],[8,7],[2,4,13],[2,4,8],[2,4,8],[2,4,11],[11,8]]),
([w62,w37,w0,w1,w2,w3,w30],[67,6,16,81,93,86,99,9,17,59,79],[],[[0],[1,0],[2],[3,1,4],[0,1],[3,5],[6],[7],[4,3],[8],[5,3],[7,8],[4,3],[8,4],[5,3],[3,4],[4,8],[3,5],[9,3],[10,4,5],[9,3]]),
([w62,w0,w1,w2,w3,w30],[17,99,9,16,81,93,6,10,86,79,82,110],[9,12,11,14,0,15,5,8,10],[[0,1,2],[2,3],[4,100,1,5,6,101],[0,1,2],[4,102,7,8,103],[2,0,104],[9,0,105,1,104],[2,0,1,104],[10,0,106,11,104],[107,2,1,100],[2,108,0],[107,2,11,102],[10,101,4,8,100],[10,9,101,5,1,100],[9,103,5,1,102]]),
([w99,w37,w0,w1,w2,w3,w30],[26,6,52,9,101,24,20,48,64,86,50,96],[],[[0],[1],[2,3,4],[5],[0],[2,4],[1],[2,4],[1],[6],[2,4],[7,4],[2,1],[1,2],[7,4],[2,1],[2,1],[8,9,10],[6,7,11],[2,1],[2,1]]),
([w64,w37,w0,w1,w2,w3,w30],[22,10,52,9,48,20,111,101,6,24,81,86],[],[[0],[1,0],[2,3,4],[5],[0,1],[2,1,4],[6],[2,7],[8],[9],[2,7],[4,7],[2,8],[8,2],[4,7],[2,4],[2,7],[10,11],[4,9],[2,4],[2,7]]),
([w64,w0,w1,w2,w3,w30],[24,111,6,52,1,48,20,10,79,54,81,86,80],[8,2,14,7,1,3,5,13,9,24],[[0,1,2],[3,100,4,5,101],[2,6],[0,1,2],[3,102,1,5,7,103],[0,104,8],[2,0,105],[2,0,106],[9,0,103,1],[2,10,100],[2,101,11],[9,10,100,1,8,102,104],[2,107,108,109],[2,102,1],[9,2,102,12]]),
([w103,w37,w0,w1,w2,w3,w30],[40,10,52,9,112,50,42,36,86,48,64,90],[],[[0],[1],[2,3,4],[5,4],[0],[6],[1],[2,4],[5,4],[7],[1],[5,4],[2,4,5],[1,2],[8,1,7],[2,9],[2,1],[10,1],[10,1],[2,1,8],[2,5,11]]),
([w103,w0,w1,w2,w3,w30],[36,10,52,1,112,64,7,40,42,79,80,90,86,54],[2,41,12,9,1,3,18,5,7,14],[[0,1],[2,100,3,4,101],[5,102,6,4,103],[1,7],[1,8],[0,104,9],[2,0,105,10,106],[1,0,107],[1,0,105],[2,103,10,11,100,101],[1,100,12],[1,100,9],[1,13,102,10],[1,2,102,12],[0,1,108,109]]),
([w104,w37,w0,w1,w2,w3,w30],[38,64,10,9,50,36,101,81,42,93],[],[[0],[1,0,2],[1,3,4],[1,4],[0,2],[5],[2],[1,6],[1,7],[8],[2],[4,6],[4,7],[2,1],[1,2],[7,6,9],[1,2],[1,2],[1,2],[1,2],[4,6]]),
([w104,w0,w1,w2,w3,w30],[42,64,10,1,50,7,36,82,54,80,81,93,101],[2,20,12,4,1,5,13,11,26],[[0,1,2],[1,100,3,4,101],[1,102,5,4,103],[0,2],[2,6],[0,104,7],[8,0,103,9],[1,0,105,2],[1,0,105,2],[8,10,101,9,7,100],[1,100,2,11],[1,10,100,2],[1,8,102,2,9],[1,102,2,12],[2,106,107,108]]),
([w37,w0,w40,w1,w2,w3,w30],[11,52,7,81,14,9,6,86],[8,5],[[0],[],[1,0,100],[2,3],[4],[1,2,3],[1,4,101],[4,5],[1,3,6],[4,6],[7,3],[6],[5],[6,7],[1,7],[5,3],[1,5,6],[3,5],[3,7],[1,6],[1,3]]),
([w37,w0,w43,w1,w2,w3,w30],[11,16,64,81,52,9,6,10,90],[],[[0],[1,0],[1,0],[2,3],[1],[4,3],[2,1],[1,5],[4,1,6],[1,6],[2,1,7],[6],[2,6,8],[5],[3,7,8],[3,5],[5,6],[2,5,3],[2,3],[2,6,4],[4,3]]),
([w37,w0,w43,w1,w2,w30],[16,6,1,63,9,64,81,52,10,90],[10,12,27,14,42,6,15,18,5,39,43,20,23,2,11],[[0,1],[0,2,3],[0,2,4,100],[5,101,1,6,100,102],[7,103,8,6,100,104],[4,0,105],[4,0],[7,0,106,1,107],[5,0,108,8,106],[1],[5,101,1,9,105,109],[6,103,8,9,105,110],[7,4,111,1,112],[5,4,113,8,111],[5,7,101,8,1,114,103]]),
([w44,w37,w0,w1,w2,w30],[67,70,17,10,9,16,6,96,81,90],[12,14,10,27,42,34,15,5,8],[[0,1],[2,3,4],[4,3,5],[3,6,100],[3,6,101],[2,3],[4,7,102,2],[6,7,100,8,103],[3,9,101,8,104],[4,2,105],[6,2,106],[3,2,107],[6,4,108],[3,4,108],[3,6,100]]),
([w37,w0,w81,w1,w2,w3,w30],[11,64,81,18,10,9,93],[8,15],[[0],[],[1,0,100],[1,2],[3],[2,4],[1,3,101],[3,5],[6,2],[3,4],[1,2,4],[4],[1,6],[4,6],[5],[2,5],[1,4],[4,1],[1,2],[1,4],[2,6]]),
([w37,w0,w1,w46,w2,w30],[20,10,64,21,101,6,54,52,7,113],[2,22,13,1,5,15,8,11,14],[[0,1],[2,100,3,4,101],[0,5],[0,5,102],[6,7,102,1,4,8],[0,103,9],[2,0,104,5],[5,0,105],[2,0,104,1,105],[2,100,4,5,9],[5,106,9],[2,107,1,9,103,100],[1],[5,108,1],[2,5,108,1]]),
([w47,w37,w0,w1,w2,w30],[22,10,24,9,20,6,52,25,101,90,114,81],[5,2,43,22,13,1,15,8,14],[[0,1],[1,0,2,100],[1,3,101],[4,1],[1,5,102],[1],[6,101,7,8,103],[5,9,104,2],[1,6,104,8],[2,105,10],[5,2,106],[1,2,100],[5,11,107,9],[1,11,101,9],[1,5,108]]),
([w37,w0,w1,w83,w2,w3,w30],[6,52,29,7,64,28,76,80,32,10],[8],[[0],[1,2,100],[3],[4,0],[5],[1,3],[6,5],[1,5,7],[1,0],[0,1],[4,5,7],[1,6],[1,0],[1,0],[4,6],[8],[0,6],[0],[4,6,9],[0,1],[1,0]]),
([w37,w0,w1,w2,w87,w30],[36,10,52,37,112,54,64,7,115,80,6],[2,22,12,13,1,15,18,5,9],[[0,1],[2,100,3,4,101],[5,6,102,7,4,103],[0,1],[0,1,103],[0,104,8],[2,0,105,9,106],[1,0,105],[1,0,107],[2,108,9,8,100,102],[1,100,8],[1,100,8],[1,102,9],[1,2,102,10],[1,10]]),
([w90,w37,w0,w1,w2,w30],[38,6,42,9,10,36,64,43,112,90,116,81],[15,20,39,22,12,13,1,5,2],[[0,1],[1,0,2,100],[1,3,101],[1,4,102],[4,5],[1],[6,101,7,8,103],[1,6,104,8,105],[4,9,105,2],[2,106,10],[1,2,100],[4,2,107],[1,11,101,9],[4,11,108,9],[4,1,104]]),
([w0,w105,w1,w2,w3,w30],[58,16,9,11,6,10,81,90],[0,3,6,12,4,14,7,20,2],[[0,1,2,3],[0,1,100,3],[4,1,101],[4,1,102],[5,1,101],[3,4],[4,6,103,7,104],[1,2,3],[5,0,105,7,106],[4,3,107],[1,3,4],[5,0,108,3],[4,103,5],[5,4,103],[5,105,4]]),
([w38,w0,w43,w1,w2,w30],[16,6,9,66,10,68,11,90],[12,14,30,3,39,43,20,2],[[0,1,2],[3,1],[1,2,0],[1,4,100],[1,4,101],[5,0,102,6],[5,0,102,6],[1,0,103],[4,0,103],[1],[1,5,100,7,104],[4,5,101,7,105],[1,5,106,6],[4,5,107,6],[4,1,100]]),
([w95,w79,w0,w1,w2,w3,w30],[71,19,90,7,54,10,65,12,84,18,96,64,93],[],[[0],[],[1],[2,3],[4,5],[0],[6],[7],[2,8],[4,8],[9],[10,7,9],[2,8],[11,8,12],[9,2],[4,2,8],[8,7],[4,2,10],[4,2,11],[11,8],[4,2,8]]),
([w106,w79,w0,w1,w2,w3,w30],[73,10,18,112,90,84,93,110,12,19,82,78],[],[[0],[1,0],[2],[3,4],[5,1,6],[0,1],[7],[3,8],[4,3],[6,5],[9],[3,8],[4,3],[6,5],[9,4],[5,4],[5,3,6],[3,4],[10,3],[10,3],[11,4,5]]),
([w106,w0,w1,w2,w3,w30],[19,110,12,18,112,6,90,84,93,78,100,82,58],[9,12,10,13,0,3,5,20,11],[[0,1,2],[2,3],[4,100,5,6,101],[7,102,1,8,5,103],[0,1,2],[2,0,104],[9,0,105,10,104],[11,0,106,1,104],[2,0,1,104],[107,2,10,100],[107,2,1,102],[2,108,0],[11,9,101,1,10,100],[11,101,1,12,100],[9,103,7,6,102]]),
([w100,w79,w0,w1,w2,w3,w30],[34,7,64,12,104,32,93,28,96,54],[],[[0],[1],[2,3,4],[5],[6,4],[0],[1],[2,4],[1],[6,4],[7],[8,4],[6,1,7],[2,4,6],[1,2],[9,1],[2,6,8],[2,1],[2,1,8],[2,6],[9,1]]),
([w107,w79,w0,w1,w2,w3,w30],[30,10,54,12,76,28,111,112,7,84,32,78,86],[],[[0],[1,0],[2,3,4],[5],[2,1,4],[0,1],[6],[2,7],[7,8],[2,9],[10],[4,7],[2,7,8],[4,9],[8,2],[2,4],[9,7,11],[2,4],[2,4],[7,12],[2,4]]),
([w107,w0,w1,w2,w3,w30],[32,111,7,54,1,76,28,10,78,52,84,86,83],[8,2,13,6,1,3,14,9,25],[[0,1,2],[3,100,4,5,101],[2,6],[3,102,1,5,7,103],[0,1,2],[0,104,8],[2,0,105],[9,0,103,1],[2,0,105],[2,10,100],[9,10,101,1,8,100],[2,100,11],[2,102,1],[2,106,107,108],[2,9,102,12]]),
([w103,w79,w0,w1,w2,w3,w30],[42,10,54,12,112,93,40,36,76,64],[],[[0],[1],[2,3,4],[5,4],[6],[0],[1],[2,4],[5,4],[1],[7],[8,4],[2,4,5],[5,1,7],[1,2],[2,5,8],[9,1],[2,1],[2,1,8],[9,1],[2,5]]),
([w108,w79,w0,w1,w2,w3,w30],[38,7,64,12,96,36,103,112,10,40,84,90],[],[[0],[1,0],[2,3,4],[2,1,4],[5],[0,1],[6],[2,7],[2,7],[8],[9],[4,7],[4,7],[2,8],[8,2],[10,11],[2,4],[2,4],[2,4],[2,4],[10,11]]),
([w108,w0,w1,w2,w3,w30],[40,103,10,64,1,96,7,36,82,52,84,90,83],[2,8,12,4,1,5,14,10,26],[[0,1,2],[3,100,4,5,101],[3,102,1,5,6,103],[2,7],[0,1,2],[0,104,8],[9,0,103,1],[2,0,105],[2,0,105],[9,10,101,1,8,100],[2,10,100],[2,100,11],[2,102,1],[2,9,102,12],[2,106,107,108]]),
([w79,w0,w40,w1,w2,w3,w30],[7,54,1,84,14,12,86],[20,5],[[0],[],[1,2,100],[0,3],[1,3],[4],[1,4,101],[4,5],[1,0],[6,3],[0,1],[0],[5],[1,6],[0,6],[0,1],[3,5],[1,0],[1,0],[3,6],[1,0]]),
([w79,w0,w43,w1,w2,w3,w30],[13,64,84,10,16,12,90],[20,3],[[0],[],[1,0,100],[1,2],[2,3],[4],[1,4,101],[4,5],[6,2],[1,2,3],[3,1],[3],[1,6],[5],[3,6],[2,5],[3,1],[1,3],[1,3],[1,2],[2,6]]),
([w79,w0,w81,w1,w2,w3,w30],[13,18,64,84,54,12,7,10,93],[],[[0],[1,0],[1,0],[2,3],[4,3],[1],[2,1],[1,5],[4,1,6],[2,1,7],[1,6],[6],[2,6,8],[3,7,8],[5],[3,5],[2,5,3],[5,6],[2,6,4],[2,3],[4,3]]),
([w79,w0,w81,w1,w2,w3],[18,10,1,71,12,64,7,84,54,93],[11,12,28,13,42,7,3,18,5,40,43,8,23,2,10],[[0,1],[0,2,3],[0,2,4,100],[5,101,6,7,100,102],[8,103,1,7,100,104],[4,0,105],[4,0],[8,0,106,6,107],[5,0,108,1,106],[1],[5,101,6,9,105,109],[7,103,1,9,105,110],[8,4,111,6,112],[5,4,113,1,111],[5,8,101,1,6,114,103]]),
([w82,w79,w0,w1,w2,w3],[73,75,19,7,12,18,10,96,84,93],[12,13,11,28,42,35,3,5,20],[[0,1],[2,3,4],[4,3,5],[3,6,100],[3,6,101],[2,3],[4,7,102,2],[3,7,100,8,103],[6,9,101,8,104],[4,2,105],[3,2,106],[6,2,107],[3,4,108],[6,4,108],[6,3,100]]),
([w79,w0,w1,w46,w2,w3,w30],[7,54,21,6,64,20,61,83,24,10],[20],[[0],[1,2,100],[3],[4,0],[1,3],[5],[6,5],[1,5,7],[1,0],[4,5,7],[0,1],[1,6],[1,0],[4,6],[1,0],[8],[0],[0,6],[0,1],[4,6,9],[1,0]]),
([w79,w0,w1,w83,w2,w3],[28,7,54,29,104,52,6,117,64,83,32,10],[2,29,14,1,5,3,8,10,13],[[0,1],[2,100,3,4,101],[0,1],[0,1,102],[5,2,102,6,4],[0,103,7],[1,0,104],[1,0,105],[8,0,104,9,105],[1,100,7],[1,106,7],[8,107,9,7,103,100],[1,10],[1,108,9],[8,1,108,11]]),
([w85,w79,w0,w1,w2,w3],[30,10,32,12,28,7,54,33,104,93,118,84],[5,2,43,29,14,1,3,8,13],[[0,1],[1,0,2,100],[1,3,101],[4,1],[1,5,102],[1],[6,101,7,8,103],[5,9,104,2],[1,6,104,8],[2,105,10],[5,2,106],[1,2,100],[5,11,107,9],[1,11,101,9],[1,5,108]]),
([w79,w0,w1,w2,w87,w3],[36,10,54,37,112,52,64,7,6,119],[2,29,12,14,1,3,18,5,9],[[0,1],[2,100,3,4,101],[5,6,102,7,4,8,103],[0,1],[0,1,103],[0,104,9],[2,0,105,7,106],[1,0,105],[1,0,107],[2,108,7,9,100,102],[1,100,9],[1,100,9],[1,102,7],[1,2,102,7],[1,7]]),
([w89,w79,w0,w1,w2,w3],[38,7,40,12,10,36,64,41,112,93,120,84],[3,8,40,29,12,14,1,5,2],[[0,1],[1,0,2,100],[1,3,101],[1,4,102],[4,5],[1],[6,101,7,8,103],[1,6,104,8,105],[4,9,105,2],[2,106,10],[1,2,100],[4,2,107],[1,11,101,9],[4,11,108,9],[4,1,104]]),
([w0,w109,w1,w2,w3,w30],[58,18,12,13,7,10,84,93],[0,15,7,12,4,13,6,8,2],[[0,1,2,3],[0,1,100,3],[4,1,101],[5,1,101],[4,1,102],[3,4],[4,6,103,7,104],[5,0,105,7,106],[1,2,3],[4,3,107],[5,0,108,3],[1,3,4],[5,4,103],[4,103,5],[4,5,105]]),
([w80,w0,w81,w1,w2,w3],[18,10,12,72,7,74,13,93],[12,13,31,15,40,43,8,2],[[0,1,2],[3,1],[1,2,0],[1,4,100],[1,4,101],[5,0,102,6],[5,0,102,6],[4,0,103],[1,0,103],[1],[4,5,100,7,104],[1,5,101,7,105],[4,5,106,6],[1,5,107,6],[1,4,100]]),
([w91,w0,w40,w1,w2,w3,w30],[8,0,60,84,6,58,7,14,5,52,86,51,54],[],[[0],[1],[],[2],[3,4],[5,6],[7],[5,7,8],[8,3,5],[9,3,10],[10,7],[11],[8],[3,10],[5,10],[8,3],[3,8],[5,8],[12,5],[9,3,5],[9,3,12]]),
([w110,w0,w40,w1,w2,w3,w30],[5,0,7,86,84,81,14,8,55,46,87],[],[[0],[1],[2,0],[0,2],[3,4],[3,2,5],[6],[6,7],[4,7],[3,4],[3,5],[8],[7],[4,3],[5,3],[7,4],[4,3],[5,3],[9,3],[9,3],[10,4]]),
([w110,w0,w1,w2,w3,w30],[14,5,15,55,8,86,10,84,81,69,88,87],[6,13,7,14,1,4,5,20,8],[[0,1],[2,3,0],[1,4,0],[5,100,6,7,101],[5,102,3,8,6,103],[4,0,104],[0,105,3],[106,0,9,100],[106,0,3,102],[0,3,4,104],[10,4,107,9,104],[11,4,108,3,104],[11,101,8,3,100],[10,103,7,5,102],[11,10,101,3,8,100]]),
([w0,w111,w40,w1,w2,w3,w30],[52,14,121,58,54,81,74,25,6,27,21],[],[[0,1,2],[0,2],[3,2],[0,2],[0,2],[4,5,6],[7],[8],[7],[9],[0,2],[8],[10],[8],[0,2],[8,0],[0,8],[3,2],[4,3],[0,2],[0,2]]),
([w0,w111,w1,w2,w3,w30],[52,121,0,21,87,84,6,54,89,81,25,27,7,64],[5,44,0,3,7,14,8,2,29,10,13],[[0,100,1,2,101],[3,102,4],[0,103,1,5,6],[0,100,1,4,6],[7,104,8,9,102,100],[3,6],[6,10],[6,11],[0,105,8,1,12,104],[0,3,106,6],[0,3,107,6],[4,3,106,8,108],[3,6,109,110],[13,0,105,5,1,6],[4,0,105,5,1,6]]),
([w112,w0,w40,w1,w2,w3,w30],[52,14,68,23,7,21,121,86,81,122,27,6],[],[[0,1,2],[3],[0,3,4],[3,4],[5],[0,2],[0,6],[2,6],[0,6],[0,2],[7,8],[9],[10],[7,11],[0,6],[10,2],[0,7,11],[2,6],[2,7],[0,6],[0,2]]),
([w112,w0,w1,w2,w3,w30],[52,0,68,27,6,21,7,88,81,86,64,122,85],[5,3,14,11,0,8,2,12,9],[[0,100,1,2,101],[3,0,4],[3,4],[4,5],[0,102,6,2,103],[2,104,3,7],[0,101,4,8],[0,9,100,2,4],[10,9,100,11,7,102,104],[0,2,105,3,4],[0,3,106,4],[10,2,103,3,11],[4,107,108],[10,0,102,4,12],[0,102,4,11]]),
([w0,w113,w40,w1,w2,w3,w30],[52,14,123,68,54,7,33,35,29,84,58],[],[[0,1,2],[0,2],[3,2],[0,2],[0,3],[4,2],[5],[5],[6],[4,2],[7],[5],[8],[4,2],[5],[5,0],[0,2,9],[3,5,4],[4,2],[0,9,10],[0,2,3]]),
([w0,w113,w1,w2,w3,w30],[52,123,0,29,88,7,84,92,33,6,35,64,68],[5,45,0,3,6,13,8,2,11,14],[[0,100,1,2,101],[3,102,4],[0,103,1,5,6],[0,104,7,6,102,100],[5,100,4],[3,5],[5,8],[6,105,7,1,9,104],[5,10],[0,3,106,5],[0,3,107,7,106],[5,3,106],[11,5,105,12],[3,5,108,109],[5,0,105,7]]),
([w114,w0,w40,w1,w2,w3,w30],[54,14,74,31,6,29,121,86,84,124,35,7],[],[[0,1,2],[3],[0,3,4],[3,4],[0,2],[5],[0,6],[2,6],[0,6],[7,6,8],[0,2],[9],[10],[0,7],[6,11],[10,2],[2,7],[0,6,11],[0,7],[2,6],[0,2]]),
([w114,w0,w1,w2,w3,w30],[54,0,74,35,6,7,29,87,84,64,86,124,85],[5,15,13,10,0,8,12,9],[[0,100,1,2,101],[3,0,4,5],[3,4,2],[0,102,4,2,103],[5,6],[2,104,3,7],[0,101,5,8],[9,10,100,11,7,102,104],[0,10,100,2,5],[0,2,105,3,5],[9,2,103,3,11],[0,3,105,5],[9,0,102,5,12],[5,106,107],[0,102,2,5,11]]),
([w0,w40,w1,w46,w3,w30],[54,121,20,21,125,14,6,7,64,68,10],[3,18,0,5,7,12,8,20,14],[[0,100,1,2,101],[3,102,4],[0,100,1,4,5,6],[6,103,4],[0,104,7,4,102,100],[3,6],[3,6],[3,6,105],[8,9,105,7,1,10],[0,3,106,6],[6,3,107],[0,3,106,7,107],[6,7],[6,108,7],[0,6,108,7]]),
([w48,w0,w40,w1,w3,w30],[7,14,23,27,21,6,68,121,26,126,86,58],[3,8,28,18,0,5,12,20,14],[[0,1,100],[2,0],[0,2,3,101],[4,0],[0,5,102],[6,100,7,8,103],[3,104,9],[5,10,105,9],[0,10,100,9],[0],[5,11,106,3],[0,6,106,7],[5,3,107],[0,3,101],[0,5,108]]),
([w0,w40,w1,w83,w3,w30],[54,123,28,29,127,14,7,52,6,64,10],[3,18,0,6,5,12,8,20,13],[[0,100,1,2,101],[3,102,4],[0,100,1,4,5,6],[7,103,8,4,100,104],[0,100,1,4,6],[3,6],[3,6],[9,0,105,8,1,10],[3,6,105],[0,3,106,6],[7,3,107,8,106],[0,3,106,6],[0,108,6,8],[6,8],[0,7,108,1,6,8]]),
([w86,w0,w40,w1,w3,w30],[6,14,31,35,7,29,54,121,34,128,86,58],[15,20,27,18,0,5,12,8,13],[[0,1,100],[2,0],[0,2,3,101],[0,4,102],[4,5],[6,100,7,8,103],[3,104,9],[0,10,100,9],[4,10,105,9],[0],[0,6,106,10],[4,11,106,3],[0,3,101],[4,3,107],[4,0,108]]),
([w0,w40,w1,w2,w87,w3,w30],[54,36,97,37,7,52,10,85,6],[5],[[0,1,100],[2,3],[0,4],[0,2],[5,2],[0,2],[4],[3],[6],[0,6],[5,4],[3,2],[0,3,7],[5,3,7],[0,3,4],[2,4],[0,2,4],[5,2,8],[4],[8],[4,0]]),
([w115,w0,w1,w2,w3,w30],[15,6,14,96,86,84,7,81,5],[13,10,14,11,1,15,3,9],[[0,1],[2,3,0],[0,1],[1,4,100,5,101],[6,4,102,7,103],[8,0,104],[1,0,8],[1,0,105],[6,0,106],[1,5,107,8],[1,5,101,4,8],[6,7,103,4,8],[1,100,6],[6,102,1],[6,1,100]]),
([w93,w0,w43,w1,w2,w3,w30],[11,0,84,6,70,52,10,16,58,9,68,64,74,53,90],[],[[0],[1],[],[2,3],[4],[5,6],[7],[8,7,9],[5,2,8],[5,2,10],[11,7,12],[13],[2,14],[9],[5,14],[2,9],[9,2],[8,9],[11,8,10],[5,2,8],[5,2,10]]),
([w116,w0,w43,w1,w2,w3,w30],[9,0,6,90,84,10,81,16,11,98,59,88,121],[],[[0],[1],[2,0],[3,2,4],[0,2],[3,5,6],[7],[7,8],[3,4],[4,8],[3,6],[9],[4,3],[8],[6,3],[4,3],[8,4],[6,3],[10,3],[11,4,12],[10,3]]),
([w116,w0,w1,w2,w3,w30],[16,9,17,98,90,6,84,11,81,10,69,88,91,86],[4,12,7,14,1,3,6,20,2],[[0,1],[2,3,0],[4,100,5,6,101],[1,7,0],[4,102,3,8,9,103],[7,0,104],[105,0,10,100],[0,106,3],[105,0,3,102],[11,6,107,7,10,104],[0,3,7,104],[12,7,108,3,104],[12,101,3,13,100],[12,11,101,3,10,100],[11,103,6,4,102]]),
([w0,w111,w43,w1,w2,w3,w30],[58,16,121,52,64,81,74,6,25,27,21],[],[[0,1,2],[0,2],[0,2],[3,0],[3,2],[4,5,6],[7],[7],[8],[9],[0,2],[7],[7],[10],[0,2],[3,7],[7,3],[0,2],[4,0,5],[3,0],[3,2]]),
([w117,w0,w43,w1,w2,w3,w30],[121,16,58,6,21,52,90,88,25],[],[[0,1,2],[3],[3],[4],[4,2,3],[0,2],[2,0],[2,0],[5,0],[5,0],[6,7],[3],[3],[8],[2,0],[5,3],[3,5],[2,0],[2,6],[5,0],[5,0]]),
([w117,w0,w1,w2,w3,w30],[121,0,58,6,21,25,10,88,90,87,54,129,89],[3,5,14,11,0,8,2,13,10],[[0,100,1,2,101],[3],[3,4],[3,5],[0,102,6,2,103],[2,104,0,5,7],[3,8,100],[3,101,9],[10,8,100,11,7,102,104],[3,5,105],[3,2,106,5],[9,2,103,5,11],[3,107,108],[3,102,11],[9,3,102,12]]),
([w0,w118,w43,w1,w2,w3,w30],[58,16,130,52,64,41,10,121,37,81],[],[[0,1,2],[0,2],[0,2],[3,0],[3,2],[4,2],[5],[6],[4,2],[5],[7],[6],[4,2],[8],[6],[3,2,9],[6,3],[0,6,4],[4,0,2],[3,0],[3,9]]),
([w0,w118,w1,w2,w3,w30],[58,130,0,37,88,52,81,10,87,6,41,43,92],[5,46,0,4,12,8,23,2,11,14],[[0,100,1,2,101],[0,102,1,3,4],[5,103,0,6,100,101],[5,100,1,7,8],[7,100,4],[3,7],[6,104,9,1,103],[7,10],[7,11],[4,3,105,12,106],[4,0,107,3,7],[7,0,105,3],[7,8,104,0],[7,4,104,0],[3,7,108,109]]),
([w119,w0,w43,w1,w2,w3,w30],[121,16,74,39,6,64,37,90,84,124,43,10],[],[[0,1,2],[3],[4,3],[5,2],[3,4],[6],[2,0],[2,0],[7,0,8],[5,0],[5,2],[9],[2,7],[10],[0,11],[2,7],[10,2],[5,0,11],[5,7],[5,0,2],[0,2]]),
([w119,w0,w1,w2,w3,w30],[121,0,74,43,124,10,64,6,37,87,54,90,84,89],[5,15,12,9,0,2,13,10],[[0,100,1,2,101],[3,4,5],[6,102,4,2,7,103],[3,4,2,5],[5,8],[2,104,0,3,9],[10,11,101,0,12,100],[5,100,9],[5,11,100],[9,2,103,3,4],[5,2,105,3],[5,3,105],[5,9,102,13],[5,102,0],[5,106,107]]),
([w0,w43,w1,w46,w2,w30],[64,121,20,21,131,16,6,10,87,58,7],[5,16,0,3,7,13,2,20,14],[[0,100,1,2,101],[3,102,4],[0,100,1,4,5,6],[6,103,4],[0,104,7,4,102,100],[3,6],[3,6],[3,6,105],[8,9,105,7,1,10],[0,3,106,6],[6,3,107],[0,3,106,7,107],[6,7],[6,108,7],[0,6,108,7]]),
([w47,w0,w43,w1,w2,w30],[6,16,23,25,21,10,58,121,24,132,90,81],[5,2,42,16,0,3,13,20,14],[[0,1,100],[2,0],[0,2,3,101],[0,4],[0,5,102],[6,100,7,8,103],[3,104,9],[0,10,105,9],[5,10,100,9],[0],[0,11,106,3],[5,6,106,7],[0,3,107],[5,3,101],[5,0,108]]),
([w0,w43,w1,w83,w2,w3,w30],[64,28,95,29,52,10,7,89,35,6],[3],[[0,1,100],[2,3],[0,2],[4,2],[0,5],[0,2],[5],[6],[0,6],[3],[4,5],[0,3,7],[4,3,7],[3,2],[0,3,5],[5],[2,5],[8],[0,2,5],[5,0],[4,2,9]]),
([w0,w43,w1,w2,w87,w30],[64,130,36,37,133,52,89,16,10,87,7,6],[5,16,0,4,18,12,13,20,23,2],[[0,100,1,2,101],[3,102,4],[5,103,6,4,100,104],[0,100,1,4,7,8],[0,100,1,4,8],[3,8],[9,0,105,6,1,10,103],[3,6],[3,6,8,106],[5,3,107,6,108],[0,3,107,8],[0,3,109,6,8],[0,105,1,6,8],[0,5,105,1,8,11],[8,11]]),
([w90,w0,w43,w1,w2,w30],[10,16,39,43,89,6,37,64,121,42,134,90,81],[15,20,27,16,0,5,12,13,2],[[0,1,100],[2,0],[0,2,3,101],[0,4,102,5],[0,6],[7,100,8,9,103],[3,104,10],[5,11,100,10],[0,11,105,10],[0],[5,7,106,11,107],[0,12,107,3],[5,3,101],[0,3,108],[0,5,106]]),
([w120,w0,w1,w2,w3,w30],[17,6,16,96,81,10,90,9],[12,9,14,11,1,15,5,10],[[0,1],[2,3,0],[1,3,100,4,101],[0,1],[5,6,102,4,103],[7,0,104],[1,0,105],[1,0,7],[5,0,106],[1,4,101,6,7],[1,7,107],[5,4,103,6,7],[1,100,5],[5,1,100],[5,102,1]]),
([w95,w0,w81,w1,w2,w3,w30],[13,0,81,7,87,10,75,18,58,12,54,64,68,74,65,93],[],[[0],[1],[],[2,3],[4,5],[6],[7],[8,4,9],[10,2,8],[11,4,12],[9,2,13],[14],[2,15],[4,15],[9],[2,9],[8,9],[9,2],[4,2,8],[11,8,13],[4,2,13]]),
([w121,w0,w81,w1,w2,w3,w30],[12,0,10,93,81,87,18,13,98,84,91],[],[[0],[1],[2,0],[3,4],[3,2,5],[0,2],[6],[5,7],[3,4],[3,5],[4,7],[8],[4,3],[5,3],[7],[4,3],[9,3],[7,4],[5,4,10],[10,3],[5,3]]),
([w121,w0,w1,w2,w3,w30],[18,12,19,98,93,6,81,87,13,55,91,86],[4,12,6,13,1,15,7,8,2],[[0,1],[2,3,0],[4,100,5,6,101],[4,102,3,7,5,103],[1,8,0],[8,0,104],[105,0,9,100],[105,0,3,102],[0,106,3],[7,6,107,8,9,104],[10,8,108,3,104],[0,3,8,104],[10,7,101,3,9,100],[10,101,3,11,100],[7,103,4,6,102]]),
([w0,w113,w81,w1,w2,w3,w30],[64,18,123,58,54,87,68,35,7,33,29,84],[],[[0,1,2],[0,2],[3,2],[4,2],[0,5,6],[0,2],[7],[8],[9],[3,2],[7],[8],[8],[3,2],[10],[4,8],[0,2,3],[8,0],[0,2,4],[0,3,11],[4,2]]),
([w122,w0,w81,w1,w2,w3,w30],[54,18,58,31,7,29,123,93,87,33],[],[[0,1,2],[3],[0,3,4],[5],[0,2],[3,4],[0,6],[2,6],[0,2],[7,8],[0,4],[4],[4],[0,6],[9],[0,4],[2,6],[4,0],[0,2],[2,7],[0,4]]),
([w122,w0,w1,w2,w3,w30],[54,0,58,33,7,29,6,87,93,52,92,88,129],[3,5,13,10,0,8,14,11],[[0,100,1,2,101],[3,0,4],[4,5],[0,102,6,2,103],[3,4],[2,104,3,7],[0,8,100,2,4],[9,8,101,10,7,100],[0,100,4,11],[0,3,105,4],[9,2,103,3,10],[0,2,105,3,4],[0,102,4,12],[4,106,107],[0,9,102,4,10]]),
([w0,w118,w81,w1,w2,w3,w30],[58,18,130,54,64,43,10,41,37,81,84],[],[[0,1,2],[0,2],[0,2],[3,0],[4,2],[3,2],[5],[6],[4,2],[7],[5],[6],[4,2],[6],[8],[3,2,9],[0,6,4],[6,3],[3,0],[4,0,2],[3,9,10]]),
([w123,w0,w81,w1,w2,w3,w30],[64,18,68,39,10,37,130,93,81,41],[],[[0,1,2],[3],[0,3,4],[0,2],[5],[3,4],[0,6],[2,6],[7,8],[0,2],[0,4],[4],[0,6],[4],[9],[2,6],[0,4],[4,0],[0,2],[0,4],[2,7]]),
([w123,w0,w1,w2,w3,w30],[64,0,68,41,10,6,37,88,52,93,92,81,122],[5,3,12,9,0,2,14,11],[[0,100,1,2,101],[3,0,4],[0,102,5,2,103],[4,6],[3,4],[2,104,3,7],[8,9,101,10,11,100],[0,9,100,2,4],[0,100,4,7],[7,2,103,3,10],[0,3,105,4],[0,2,105,3,4],[0,102,2,4,12],[0,7,102,4,10],[4,106,107]]),
([w0,w81,w1,w46,w2,w3,w30],[64,20,94,21,54,10,6,92,27,7],[15],[[0,1,100],[2,3],[0,2],[4,2],[0,2],[0,5],[5],[6],[0,6],[4,5],[3],[0,3,7],[4,3,7],[0,3,5],[3,2],[5],[8],[2,5],[5,0],[0,2,5],[4,2,9]]),
([w0,w81,w1,w83,w2,w3],[64,123,28,29,135,18,7,92,52,54,6,33,10],[5,37,0,3,6,14,2,8,13],[[0,100,1,2,101],[3,102,4],[0,100,1,4,5,6],[6,103,4],[0,104,7,4,102,100],[3,6],[3,6],[3,6,105],[8,9,105,7,1,10],[0,3,106,6],[6,3,107],[0,3,106,7,107],[6,11],[6,108,7],[0,6,108,12]]),
([w85,w0,w81,w1,w2,w3],[10,18,31,33,29,7,54,123,32,136,93,84],[5,2,42,37,0,3,14,8,13],[[0,1,100],[2,0],[0,2,3,101],[4,0],[0,5,102],[6,100,7,8,103],[3,104,9],[5,10,105,9],[0,10,100,9],[0],[5,11,106,3],[0,6,106,7],[5,3,107],[0,3,101],[0,5,108]]),
([w0,w81,w1,w2,w87,w3],[54,130,36,37,137,7,18,10,52,64,6],[5,37,0,4,18,12,14,8,23,2],[[0,100,1,2,101],[3,102,4],[0,103,5,4,100,104],[0,100,1,4,6,7],[7,100,4],[3,5],[8,9,105,5,1,10,103],[3,7],[3,7,106],[0,3,107,5,108],[0,3,107,7],[7,3,109],[7,105,5],[7,0,105,5],[5]]),
([w89,w0,w81,w1,w2,w3],[10,18,39,41,7,37,64,123,40,138,93,84],[3,8,28,37,0,5,12,14,2],[[0,1,100],[2,0],[0,2,3,101],[0,4,102],[0,5],[6,100,7,8,103],[3,104,9],[4,10,100,9],[0,10,105,9],[0],[4,6,106,10,107],[0,11,107,3],[4,3,101],[0,3,108],[0,4,106]]),
([w124,w0,w1,w2,w3,w30],[19,7,18,96,84,10,93,12],[12,9,13,10,1,3,5,11],[[0,1],[2,3,0],[1,3,100,4,101],[5,6,102,4,103],[0,1],[7,0,104],[1,0,105],[5,0,106],[1,0,7],[1,4,101,6,7],[5,4,103,6,7],[1,7,107],[5,1,100],[1,100,5],[1,5,102]]),
([w0,w1,w125,w2,w3,w30],[82,87,139,0,7,91,10,88,1,46,6],[0,1,2,5,3,8,12,13],[[100,101,0,1,102],[0,103,2,3,100],[4,104,5],[0,103,2,1,6],[0,103,2,4,7],[1,102,2,8,101],[1,105,2,0,4],[5,102,2,6,9],[1,102,2,4,9],[4,6],[4],[4,10],[0,1,106,4,6],[0,4,106,6],[1,6,107,4]]),
([w0,w1,w46,w9,w30],[140,141,6,22,10,23],[0,1,2,6,15,7,5,10,20,11,24,14],[[100,101,0,1,102],[2,103,0,3],[2,104,0],[4,105,0,106],[2,107,1,5],[2,108,1],[4,109,1,102],[2,110],[2,4,111],[2,4,111]]),
([w126,w0,w1,w2,w3,w30],[22,10,88,1,112,26,6,81,79,93,77,7],[20,2,14,11,1,15,7],[[0,1],[2,100,3,4,101],[0,5,6],[0,1],[1,2,102,7,103],[0,104,8],[6,0,105],[1,0,105],[1,0,106],[2,7,100,6,9],[1,10,100,9],[1,7,101,8],[1,6,11],[1,2,102,6],[1,102,6]]),
([w0,w127,w1,w2,w3,w30],[52,123,0,23,88,90,6,84,86,7,10],[15,5,0,14,7,20,11],[[0,100,1,2,101],[3,102,4],[0,5,100,1,6,7],[0,8,100,6,7],[9,5,101,4],[3,6],[3,6],[3,6],[9,0,103,5,104],[0,3,105,6],[0,3,105,6],[9,3,106],[6,3,10,9],[9,103,6],[9,0,103,5,6]]),
([w128,w0,w1,w2,w3,w30],[24,6,96,1,88,20,10,86,81,93],[2,8,7,14,1,5,4,13,24],[[0,1],[2,100,3,4,101],[1,2,5,0],[0,1],[6,7,102,4,103],[0,104,105],[1,0,106],[1,0,105],[6,0,102],[1,8,101,9],[1,100,7],[6,8,100,7],[1,107,6,108],[6,1,103],[6,103,1]]),
([w0,w76,w1,w2,w3,w30],[68,79,0,25,90,6,81,84,10,21],[5,3,0,2,11,14,9,13,24],[[0,100,1,2,101],[0,102,1,3,103],[1,4,101,5,6],[1,100,0,5,7],[8,4,100,6],[3,5],[5,0,9,3],[3,5],[8,0,104,1,105],[5,0,106,3],[5,3,103],[8,0,103,1],[5,107,8,108],[8,1,105,5],[8,105,5]]),
([w0,w1,w2,w3,w129],[6,10,0,1,7,36],[0,1,5,2,4,9,43,13,7,42,11,14],[[100,101,102,103],[0,104,105],[0,106,107],[1,108,2],[0,105,104],[0,109,106],[1,110,3],[0,107,1,4],[0,1,111],[0,1,5,4]]),
([w0,w1,w2,w3,w130],[6,10,0,1,36,40],[0,1,5,2,4,12,13,7,9,11],[[100,101,102,103],[0,104,105],[0,102,106],[1,107,2],[0,108,104],[0,103,106],[1,109,3],[0,105,1],[0,1,105],[0,1,4,5]]),
([w131,w0,w1,w2,w3,w30],[26,6,96,1,88,93,20,7,90,77],[8,2,7,14,1,3,6,12,24],[[0,1],[2,100,3,4,101],[0,1],[1,5,6,0],[7,8,102,4,103],[0,104,105],[1,0,105],[1,0,106],[7,0,102],[1,100,5],[1,9,101,5],[7,9,100,8],[1,107,7,108],[7,103,1],[7,1,103]]),
([w0,w78,w1,w2,w3,w30],[68,79,0,27,6,81,86,84,7,21],[3,5,0,8,11,14,10,12,24],[[0,100,1,2,101],[0,102,1,3,103],[1,100,4,5],[1,6,101,0,4,7],[8,6,100,5],[3,4],[3,4],[4,7,9,3],[8,0,104,1,105],[4,0,103,3],[4,3,106],[8,0,103,1],[4,107,8,108],[8,105,4],[8,1,105,0,4]]),
([w0,w1,w2,w3,w132],[7,6,0,1,10,28],[0,1,5,2,40,12,6,10,7,28,11,14],[[100,101,102,103],[0,104,105],[1,106,107],[0,108,2],[0,109,104],[1,107,106],[0,110,3],[0,1,105,4],[0,5,1,4],[0,1,111]]),
([w0,w1,w2,w133,w3],[6,7,0,1,28,32],[0,1,5,2,3,12,7,6,13,8,11,10],[[100,101,102,103],[0,104,105],[1,106,2],[0,107,108],[0,109,105],[1,110,3],[0,111,107],[0,1,4,5],[0,105,1,108],[0,1,108]]),
([w0,w1,w83,w3,w84],[142,143,7,30,6,31],[0,1,2,7,6,5,3,11,10,8,13,25],[[100,101,0,1,102],[2,103,0,3],[4,104,0,105],[2,106,0],[2,107,1,5],[4,108,1,102],[2,109,1],[2,4,110],[2,111],[2,4,110]]),
([w134,w0,w1,w2,w3,w30],[30,6,96,1,112,86,84,32,78,7,90,77,10],[8,2,13,10,1,3,6],[[0,1],[2,100,3,4,101],[0,1],[1,5,102,6,103],[0,7,5],[0,104,8],[1,0,105],[1,0,106],[8,0,105,9],[1,6,100,10],[1,6,101,5],[9,11,100,5],[1,102,9],[9,0,12,1],[8,1,102,6,9]]),
([w0,w135,w1,w2,w3,w30],[68,123,0,31,87,7,93,84,6,86,77,10],[3,5,0,13,6,8,10],[[0,100,1,2,101],[0,102,1,3,4],[5,6,100,7],[8,6,101,4],[5,9,100,10],[3,5],[3,5],[8,4,103,1,104],[3,5],[4,0,105,3,5],[8,3,106],[4,0,105,3,5],[8,103,5],[5,3,11,8],[4,8,103,1,5]]),
([w136,w0,w1,w2,w3,w30],[32,7,96,1,87,28,10,86,84,90],[2,8,6,13,1,5,4,14,25],[[0,1],[2,100,3,4,101],[1,2,5,0],[6,7,102,4,103],[0,1],[0,104,105],[1,0,106],[6,0,102],[1,0,105],[1,8,101,9],[6,8,100,7],[1,100,7],[6,1,103],[1,107,6,108],[1,6,103]]),
([w0,w137,w1,w2,w3,w30],[68,123,0,33,7,93,84,10,77,29],[5,3,0,2,10,13,9,14,25],[[0,100,1,2,101],[0,102,1,3,103],[4,5,101,6],[7,5,100,6],[4,100,8],[3,4],[4,0,9,3],[7,6,104,1,105],[3,4],[4,0,106,3],[7,3,103],[4,0,103,3],[7,4,105],[4,107,7,108],[4,7,105]]),
([w0,w1,w2,w138,w30],[7,10,0,1,6,36],[0,1,5,2,4,9,6,43,14,10,42,13],[[100,101,102,103],[0,104,105],[1,106,2],[0,107,108],[0,105,104],[1,109,3],[0,110,107],[0,1,111],[0,108,1,4],[0,1,5,4]]),
([w0,w1,w2,w139,w30],[7,10,0,1,36,42],[0,1,5,2,4,12,6,14,9,10],[[100,101,102,103],[0,104,105],[1,106,2],[0,102,107],[0,108,104],[1,109,3],[0,103,107],[0,1,105],[0,105,1],[0,1,4,5]]),
([w140,w0,w1,w2,w3,w30],[34,7,96,1,87,6,86,28,93,77],[20,2,6,13,1,15,7,12,25],[[0,1],[2,100,3,4,101],[0,1],[5,6,102,4,103],[1,6,7,0],[0,104,105],[1,0,105],[5,0,102],[1,0,106],[1,100,8],[5,9,100,6],[1,9,101,6],[5,103,1],[1,107,5,108],[1,5,103]]),
([w0,w141,w1,w2,w3,w30],[68,123,0,35,7,84,6,86,77,29],[15,5,0,20,10,13,11,12,25],[[0,100,1,2,101],[0,102,1,3,103],[4,100,5],[6,7,100,5],[4,7,101,8],[3,4],[3,4],[6,5,104,1,105],[4,0,9,3],[4,0,103,3],[6,3,103],[4,0,106,3],[6,105,4],[4,107,6,108],[4,6,105]]),
([w0,w1,w2,w142,w30],[6,0,7,1,20,24,10],[0,1,5,2,39,12,6,7,11,27,10,13],[[100,101,102,103],[0,104,105],[0,106,1],[2,107,108],[0,109,104],[0,110,3],[2,108,107],[0,4,2,5],[0,2,105,6],[0,2,111]]),
([w0,w1,w143,w2,w30],[6,0,7,1,20,24],[0,1,5,2,6,3,12,7,14,10,8,11],[[100,101,102,103],[0,104,1],[0,105,106],[2,107,108],[0,109,3],[0,110,106],[2,111,107],[0,4,2,5],[0,2,108],[0,2,106,108]]),
([w0,w1,w2,w87,w88],[144,145,7,10,38,39],[0,1,2,4,18,7,5,9,11,12,26],[[100,101,0,1,102],[2,103,0,104],[3,105,0,4],[2,106,0],[2,107,1,103],[3,108,1,5],[2,102,1],[2,3,109],[2,109,3],[2,3,110]]),
([w144,w0,w1,w2,w3,w30],[38,7,96,1,112,42,10,82,84,86,81,6],[2,8,12,9,1,4,5],[[0,1],[2,100,3,4,101],[1,2,102,4,103],[0,5,6],[0,1],[0,104,7],[1,0,105],[6,0,106],[1,0,106],[1,8,101,7],[6,8,100,9],[1,10,100,9],[6,1,102],[1,102,6],[1,6,11]]),
([w0,w145,w1,w2,w3,w30],[68,123,0,39,91,6,93,84,10,90,81,7],[5,3,0,12,4,9,2],[[0,100,1,2,101],[0,102,1,3,4],[5,6,101,4],[5,6,100,7],[8,9,100,10],[3,5],[5,0,103,6,104],[3,5],[3,8],[5,0,105,3],[4,3,106,5],[4,0,106,3,8],[4,5,103,8],[4,5,103,6,8],[8,3,11,5]]),
([w146,w0,w1,w2,w3,w30],[40,10,96,1,91,7,86,36,84,90],[8,2,4,12,1,3,6,14,26],[[0,1],[2,100,3,4,101],[5,2,102,4,103],[1,6,7,0],[0,1],[0,104,105],[5,0,102],[1,0,106],[1,0,105],[5,8,100,9],[1,8,101,6],[1,100,6],[1,5,103],[1,5,103],[1,107,5,108]]),
([w0,w147,w1,w2,w3,w30],[68,123,0,41,7,93,84,10,81,37],[3,5,0,8,9,12,10,14,26],[[0,100,1,2,101],[0,102,1,3,103],[4,5,100,6],[7,5,101,6],[4,100,8],[3,4],[4,0,104,5,105],[7,6,9,1,3],[3,4],[4,0,103,3],[7,3,106],[4,0,103,3],[7,4,105],[4,105,7],[4,7,107,108]]),
([w0,w1,w148,w3,w30],[7,0,6,1,24,28,10],[0,1,5,2,4,6,10,40,14,9,28,12],[[100,101,102,103],[0,104,1],[2,105,106],[0,107,108],[0,109,3],[2,106,105],[0,110,107],[0,2,111,4],[0,5,2,6],[0,2,108]]),
([w0,w1,w149,w3,w30],[7,0,10,1,28,34],[0,1,5,2,4,6,13,14,9,10],[[100,101,102,103],[0,104,1],[2,105,106],[0,102,107],[0,108,3],[2,109,105],[0,103,107],[0,2,106],[0,4,2,5],[0,2,106]]),
([w150,w0,w1,w2,w3,w30],[42,10,96,1,91,6,90,36,81,93],[20,2,4,12,1,15,7,13,26],[[0,1],[2,100,3,4,101],[5,2,102,4,103],[0,1],[1,6,7,0],[0,104,105],[5,0,102],[1,0,105],[1,0,106],[5,8,100,6],[1,100,9],[1,8,101,6],[1,5,103],[1,5,103],[1,107,5,108]]),
([w0,w151,w1,w2,w3,w30],[68,82,0,43,6,90,81,84,10,37],[15,5,0,20,9,12,11,13,26],[[0,100,1,2,101],[0,102,1,3,103],[4,5,100,6],[1,100,0,4,7],[1,5,101,8,6],[3,4],[4,0,104,1,105],[3,4],[8,0,9,3],[4,0,103,1],[4,3,103],[8,0,106,3],[1,4,105,8],[1,4,105,7,8],[8,107,4,108]]),
([w0,w1,w152,w3,w30],[6,0,10,1,20,26,7],[0,1,5,2,4,39,13,7,11,9,27,12],[[100,101,102,103],[0,104,1],[0,105,106],[2,107,108],[0,109,3],[0,110,105],[2,108,107],[0,4,2,5],[0,2,111],[0,2,106,6]]),
([w0,w1,w153,w3,w30],[6,0,10,1,20,26],[0,1,5,2,4,13,7,14,9,11],[[100,101,102,103],[0,104,1],[0,102,105],[2,106,107],[0,108,3],[0,103,105],[2,109,106],[0,4,2,5],[0,2,107],[0,2,105,107]])]
noncomputable def p13_D5 : List StD := [
([w31,w0,w1,w2,w154,w30],[98,110,146,6,51,63,81,46,96,93,90,84,53,62],[],[[0],[1],[2,3],[4,0,5],[6,0,7],[2,8],[8,2],[9,2],[10,2],[2,9,6],[11,7],[6,7],[7,4],[7,8,12],[13,4]]),
([w155,w31,w0,w1,w2,w30],[6,63,51,93,84,46,62,82,91,59,81,96,68,90,86],[],[[0,1,2],[3,1],[4,3],[5,2],[6,2],[7],[8],[3,9],[10,5],[11,12],[3,4],[13,5],[4,3],[10,5],[5,3,14]]),
([w31,w0,w1,w2,w3,w156],[55,100,147,84,46,81,96,93,90,51,34,59],[],[[0],[1],[2,0],[3,4],[5,0,4],[2,6],[6,2],[7,2],[8,2],[2,7,3],[3,4],[5,4],[4,5,9],[4,3,10],[11,3,5]]),
([w157,w31,w0,w1,w2,w3],[81,73,71,90,59,30,34,82,91,62,84,96,68,93,46,86],[],[[0,1,2],[3,0],[0,1,2],[4,5,6],[4,0],[7],[8],[0,9],[10,9],[11,12],[3,0],[13,9],[0,3],[10,9],[14,0,15]]),
([w91,w0,w1,w49,w3,w30],[55,148,84,6,59,81,62,51,149,96,93,90],[],[[0],[1],[],[2,3,4],[5,0,6],[7,8,9],[9,2],[10,2],[11,4],[2,7,10],[2,6],[5,4],[5,6],[2,4],[4,2,5]]),
([w50,w91,w0,w1,w3,w30],[0,90,14,62,86,59,150,151,96,152,84,81],[],[[0],[1,2],[2,1],[3,1,4],[5,4],[6],[7],[4,5],[1,3],[8,9],[4,3],[1,5],[10,3],[11,1],[3,1,5]]),
([w110,w91,w1,w2,w3,w30],[0,51,14,90,86,84,81,153,69,55,46,87],[17,5],[[0],[1,2],[3,1,2],[4,5],[3,1,6],[100],[7],[4,8,101],[3,9,101],[2,3,5],[5,4],[6,3],[10,3,4],[10,4],[11,3,5]]),
([w56,w91,w0,w2,w3,w30],[0,51,14,84,46,81,154,99,100,90,86,87],[17,2],[[0],[1,2],[2,1],[3,4],[5,1,4],[100],[6],[3,7,101],[4,8,101],[9,3],[10,3],[9,4],[4,5,10],[4,3,10],[11,3]]),
([w158,w0,w1,w2,w3,w30],[69,99,90,7,53,87,96,84,86,81,46],[],[[0],[1],[],[],[2,3],[4,5,6],[2,4,7],[8,4,5],[2,9],[5,2,4],[7,4,8],[5,2,6],[5,2,8],[10,4],[5,2,7]]),
([w91,w0,w1,w2,w154,w30],[69,99,90,10,53,146,96,86,84,81,46,87],[],[[0],[1],[],[],[2,3],[4,5,6],[2,4,5],[7,4,5],[2,5],[5,2,4],[8,4,7],[9,2],[10,2,7],[10,4],[11,2,8]]),
([w155,w0,w1,w2,w3,w30],[69,53,99,59,90,84,91,96,82,155],[],[[0,1],[2,1],[3,0,4],[5],[3,4],[1,6,7],[4,1,3],[8,1],[4,3],[9,1,3],[6,1],[6,3,7],[3,4],[6,1,7],[3,1]]),
([w155,w91,w0,w1,w2,w30],[6,86,14,84,46,87,59,96,90],[5,2],[[0],[1,2],[3,1],[4,1],[5,3],[100],[101],[6],[1],[7,5],[7,3],[1,4],[3,8],[5,1,7],[4,1]]),
([w155,w0,w1,w2,w30],[86,82,123,0,53,68,84,91,104,63,96,46,62,22,26,59,10,156,79,74,155],[16,22,13,0,2,17,18,5,29,12,11,14],[[0,1,2,3,4,5,100],[6,7,8,0,4,9,10,101],[11,1,12,0,5,13,14,102],[12,15,102,2,5,16],[5,10,103,1,7,104,105],[17,4,6,103,10,18,106],[1,0,107,19,11,103],[20,4,1,17,104],[7,5,104,10,0,17,108],[1,11,109,6,0,110,111]]),
([w159,w0,w1,w2,w3,w30],[123,100,84,10,96,82,91,86,46,79,90],[],[[0],[1],[],[2,3],[],[4,5,6],[4,2],[5,2,7],[5,8,7],[2,5],[2,4,6],[6,4],[5,4],[5,2],[9,2,10]]),
([w91,w0,w1,w2,w3,w156],[123,100,84,10,96,147,79,86,90,87],[],[[0],[1],[],[2,3],[],[4,5],[4,2],[6,2,7],[7,5],[2,8],[2,4,7],[9,4],[9,4,7],[6,2,7],[6,2,8]]),
([w157,w0,w1,w2,w3,w30],[123,0,51,100,82,96,87,84,90,93],[],[[0,1,2],[3,2],[4,2,5],[6,7],[8],[2,4,6],[5,2,7],[4,6,9],[4,2],[6,2],[7,5,9],[6,2],[4,2,5],[4,5],[6,2]]),
([w157,w91,w0,w1,w2,w3],[7,90,14,87,96,46,157,84,62,93,86],[5,2],[[0],[1,2],[3,1,4],[5,4,6],[3,1,7],[100],[101],[8],[3],[4,3],[1,7],[9,3],[3,1,7],[7,4,5],[3,1,10]]),
([w157,w0,w1,w2,w3],[90,82,121,0,51,74,68,87,101,71,96,46,59,30,34,10,79,158,84,93,159,91],[37,29,14,0,2,17,18,5,22,12,10,13],[[0,1,2,3,4,5,100],[6,7,8,0,4,9,10,101],[11,1,12,2,5,13,14,102],[12,7,102,0,5,15],[5,10,103,1,7,104,105],[16,0,17,4,18,103,106],[1,19,107,6,7,103],[7,5,20,4,0,17,104],[21,5,104,10,11,17,108],[1,7,109,0,4,110,111]]),
([w91,w0,w1,w46,w3,w30],[160,161,84,10,91,96,125,79,68,90,88,162,53],[],[[0],[1],[2,3,4],[4,3],[4,3],[5,6],[5,2],[7,6,8],[9,6],[2,9],[10,5],[8,5,7],[11],[7,2,12],[7,8]]),
([w48,w91,w0,w1,w3,w30],[90,14,84,125,79,163,164,91,10,96,126,68,88],[],[[],[0,1],[2,0],[3],[4,2],[5],[6],[7,8],[0,8,7],[9,4,10],[4,10,11],[0,10],[12,9],[11,0],[4,0]]),
([w91,w0,w1,w83,w3,w30],[165,166,84,10,91,96,127,79,93,78,51,87,157],[],[[0],[1],[2,3,4],[2,3,4],[4,3],[5,6],[5,2],[7,2,8],[9,6,10],[2,8],[2,5,8],[11,5],[9,5,10],[12],[7,2,9]]),
([w86,w91,w0,w1,w3,w30],[96,14,84,93,87,127,55,167,10,91,78,128,51],[],[[],[0,1],[2,3],[4,0],[5],[6],[7],[2,8,9],[9,6],[0,4],[3,2],[10,11,12],[2,0,3],[4,0],[4,2]]),
([w31,w34,w1,w49,w3,w30],[51,55,56,44,93,6,46,90,96,68,15,59,62,77],[],[[0,1],[2],[3],[4,5,6],[7,0,6],[0,2,8,9],[10],[4,9,11],[6,0,12],[2,3],[13,4],[13,0,6],[0,7],[4,6],[11,0,7]]),
([w31,w0,w40,w49,w3,w30],[55,168,169,84,62,68,59,96,1,86,93],[],[[0],[1,0],[2],[3,4],[5,0,6],[5,1,7],[8,1],[9,1],[9,1],[10],[3,7,6],[4,7],[4,5],[3,6],[4,3]]),
([w31,w0,w1,w2,w160,w30],[55,100,59,16,62,17,86,61,58,24,46],[],[[0],[1],[0,2],[3,4,5],[6,0,2],[7,8],[2,8],[6,3],[6,2],[2,7],[3,4,5],[8,2],[2,6,9],[4,6,10],[2,7]]),
([w161,w31,w0,w1,w2,w30],[17,62,16,86,24,20,51,55,100,96,59,68],[],[[0,1,2],[3,0],[0,1,2],[4,3,5],[1,6],[7],[8],[9,1],[3,6,10],[9,11],[9,1],[3,6,10],[11,1],[11,3],[1,3,9]]),
([w31,w0,w1,w2,w162,w3],[55,100,59,18,86,62,61,58,32,46],[],[[0],[1],[0,2],[3,0,2],[4,5],[6,7],[2,7],[4,2],[4,5],[2,6],[3,2,7],[7,4],[5,4,8],[2,4,9],[2,6]]),
([w163,w31,w0,w1,w2,w3],[19,59,18,86,32,28,62,51,55,100,96,58,84],[],[[0,1,2],[3,0],[0,1,2],[4,3,5],[1,6,7],[8],[9],[10,1],[3,6],[10,11],[10,1],[3,6],[12,1],[11,3],[1,3,10]]),
([w92,w50,w0,w1,w3,w30],[170,152,51,46,62,58,55,15,154,96,86],[],[[],[0],[1],[2,3],[4,3,5],[6,2],[7,2],[3,5],[3,2,5],[2,8,9],[10,3],[10,2,3],[5,3],[5,2,3],[4,2]]),
([w50,w31,w34,w1,w3,w30],[56,44,14,62,96,86,46,58,68,59,77,93],[],[[0],[1,2],[0,1],[3,4,5],[6,4,5],[7,3],[1],[5,3],[5,6],[4,3,7],[5,8,9],[3,10,5],[7,3],[7,4,5],[3,11]]),
([w50,w31,w0,w40,w3,w30],[149,1,62,86,46,60,152,151,58,96,68,59],[],[[0],[1,0],[0,1],[2,3],[4,3],[5],[6,7],[3,2],[3,4],[8,2,9],[3,2],[3,4],[4,3],[2,3,4],[2,10,11]]),
([w164,w0,w1,w2,w3,w30],[1,0,68,58,46,7,61,87,78,62,53,79,91,94],[],[[0,1],[1,0],[2],[3],[4,5,6],[6,7],[8,9,10],[11,4,10],[6,4],[7,6],[12,4,6],[7,4,13],[4,12],[4,6],[7,6,11]]),
([w165,w0,w1,w2,w3,w30],[58,0,11,16,17,68,26,62,7,91,61,79,53,59,88],[27],[[0,1,2],[3,2,4],[5,6],[7],[0,8],[0,9,10],[11,0],[11,12],[10,13],[14,10],[0,10,9],[0,11],[9,0,100],[9,0,11],[11,10]]),
([w166,w0,w1,w2,w3,w30],[55,51,0,96,62,6,95,58,79,76,78,88,91],[],[[0,1],[2,0],[3],[4,5,6],[7],[1,8,6],[8,1],[8,4,9],[10,1],[11,1],[6,4],[12,1],[10,1],[4,8],[4,1]]),
([w167,w0,w1,w2,w3,w30],[51,55,19,91,58,6,79,61,78,86,62,87],[28],[[0,1],[0,2],[3,0],[4,5],[6],[0,3,7],[8,0],[9,10],[7,0,8],[11,0],[3,7],[3,0],[3,0,8],[3,4,100],[8,0]]),
([w50,w0,w1,w3,w9,w30],[79,22,58,171,172,6,53,61,86,88,173],[],[[0,1,2],[1,3,4],[2,5],[],[0,2],[2,0],[0,4,6],[0,2],[7,4],[2,6,8],[9,6],[2,0],[10],[0,6],[0,2]]),
([w47,w50,w0,w1,w3,w30],[6,62,53,174,69,24,78,79,61,175,88,87,96],[18,23,27],[[0,1],[2,1,100],[2,1,101],[3],[1,2],[4,2],[5,0],[6,0,102],[7,8],[2,6,9],[7,2],[6,9,8],[10,2],[11,7,12],[6,2,7]]),
([w50,w0,w1,w3,w30,w84],[69,53,30,87,58,96,86,176,78,51,177],[],[[0,1],[2,0],[3,0,4],[4,5],[],[1,3,5],[6,1,3],[6,7],[8,1],[4,1,6],[3,5],[3,1],[3,1,9],[3,4],[10]]),
([w85,w50,w0,w1,w3,w30],[96,62,51,59,176,32,95,88,79,76,78,87],[18,23,28],[[0,1],[2,1,100],[0,1,101],[2,3],[4],[0,2],[5,2],[1,0,6],[7,0,102],[0,7],[8,1,9],[10,2],[6,0,1],[11,0],[1,2]]),
([w31,w0,w1,w168,w3,w30],[55,100,96,44,178,6,58,59,76,86,68,62],[],[[0],[1],[2,0,3],[4,5],[6,0,7],[4,2],[2,3],[8,4],[9,4],[10,7],[4,2,9],[6,2,7],[7,2],[11,2],[7,8,10]]),
([w169,w31,w0,w1,w3,w30],[6,44,96,68,56,59,62,78,87,179,46,58,76,86],[],[[0,1,2],[2,1],[3,4,1],[5,2],[6,2],[7],[8],[9,10,11],[3,5],[9,2],[12,3,9],[13,5],[9,2,10],[3,2,5],[5,3]]),
([w31,w0,w1,w2,w3,w170],[55,100,68,59,180,10,76,96,86,46],[],[[0],[1],[2,0,3],[4,5],[2,0,3],[4,6],[7,3],[6,2,4],[8,3],[2,3],[4,7,8],[2,3],[3,2],[9,7,8],[3,2]]),
([w171,w31,w0,w1,w2,w3],[6,73,71,53,86,58,46,78,87,96,59,62,68],[],[[0,1,2,3],[4,1],[5,1,2],[6,3],[6,3],[7],[8],[9,10],[4,11],[9,5],[9,5,10],[4,11],[12,10],[5,4],[10,4,9]]),
([w93,w0,w1,w2,w51,w30],[69,181,59,46,10,62,53,182,96,86,68,76],[],[[0],[1],[2,0,3],[],[2,4,5],[6,7,8],[8,2],[9,6,7],[9,2],[10,2],[7,9],[10,2],[2,9],[3,6],[2,11]]),
([w52,w93,w0,w1,w2,w30],[0,86,16,59,68,183,184,46,62,185,76,96],[],[[0],[1,2],[2,1],[3,1,4],[3,4],[5],[6],[3,7],[1,8],[4,9,10],[11,3],[1,3],[4,3],[4,1],[7,1]]),
([w116,w93,w1,w2,w3,w30],[0,76,16,96,59,86,69,186,98,68,88],[19,3],[[0],[1,2],[3,4],[1,2],[5,4],[100],[3,6,101],[7],[4,8,101],[9,1,4],[2,3,5],[9,1,4],[4,1,3],[10,3,5],[4,1,9]]),
([w62,w93,w0,w2,w3,w30],[0,76,16,68,59,182,187,99,188,110,96,86,88],[19,8],[[0],[1,2],[3,1,4],[2,5,6],[3,1,4],[100],[3,7,101],[8],[3,9,101],[10,4],[1,3,6],[11,4],[4,1,3],[12,10,11],[4,1,3]]),
([w93,w0,w1,w168,w3,w30],[69,99,59,7,53,178,96,86,68,88],[],[[0],[1],[],[],[2,3],[4,5,6],[6,2],[7,4,5],[7,2],[8,2],[5,4,7],[8,2],[2,6],[9,4],[2,4]]),
([w169,w0,w1,w2,w3,w30],[69,53,99,59,46,86,88,76,78,58],[],[[0,1],[2,1],[3],[4,0,5],[4,5],[1,6,7],[8,1],[5,1,4],[5,4],[6,1],[6,1],[9,4],[4,5],[4,1],[6,1]]),
([w169,w93,w0,w1,w3,w30],[6,96,16,88,189,76,59,86,46,179,68],[3,8],[[0],[1,2],[3,4,5],[6,1],[3,1,7],[100],[101],[8],[3],[1,3],[5,9],[7,3],[3,1],[10,1,6],[3,5,10]]),
([w169,w0,w1,w3,w30],[96,78,130,0,53,58,68,88,112,44,76,59,62,22,24,10,190,46,79,86,95,179,87],[18,23,12,0,2,17,5,22,29,13,11,14],[[0,1,2,3,4,5,100],[6,7,8,2,4,9,10,101],[11,1,12,0,5,13,14,102],[12,7,102,0,5,15],[5,0,103,1,7,104,105],[16,4,17,103,10,18,106],[1,19,106,20,7,103],[7,5,21,0,1,16,107],[22,5,104,0,11,16,108],[1,7,109,10,4,110,111]]),
([w172,w0,w1,w2,w3,w30],[98,110,59,6,65,88,79,95,86,68],[],[[0],[1],[2,3],[],[],[4,5,6],[6,2,7],[6,4],[8,2],[5,2,9],[5,4],[9,2],[2,4],[5,4,8],[2,7,9]]),
([w93,w0,w1,w2,w3,w170],[98,110,68,7,180,79,95,86,59],[],[[0],[1],[2,3],[],[],[2,4,5],[5,4,6],[5,2],[7,4],[2,8],[4,7,6],[2,5],[8,2],[5,7],[5,2]]),
([w171,w0,w1,w2,w3,w30],[98,65,110,62,6,96,95,68,87,191,78,76],[],[[0,1],[2,1],[3,4,5],[3,0,6],[7],[1,8,5],[5,3],[9,1,3],[10,1],[8,3,11],[6,1,3],[8,1],[8,1,6],[3,1],[3,6]]),
([w171,w93,w0,w1,w2,w3],[10,86,16,68,79,62,192,95,191,59],[3,8],[[0],[1,2],[3,1],[4,1],[4,3],[100],[101],[3],[5],[3,4],[4,6,7],[1,3,4],[3,8],[6,1,7],[9,1,3]]),
([w171,w0,w1,w2,w3],[86,78,121,0,95,68,87,101,65,71,76,79,62,96,6,46,191,192,59],[37,29,12,14,0,2,17,3,5,8,10,13],[[0,1,2,3,4,100],[5,6,7,0,8,9,10,101],[11,12,102,0,13,14,103],[11,1,15,2,4,14,103],[4,10,104,1,6,105,106],[1,13,107,4,12,102,104],[11,0,16,5,6,104,108],[6,5,109,10,12,16,105],[17,8,0,16,109],[18,1,102,5,0,110,111]]),
([w93,w0,w1,w46,w2,w30],[193,194,95,6,62,195,46,86,10,87,131,113,79,88,53,58,196],[],[[0],[1],[2,3,4],[5,3,6],[7,8,9],[2,10,11],[7,10],[12,2],[7,2,6],[2,7],[13,11,14],[15,6],[16],[6,2,14],[6,7]]),
([w47,w93,w0,w1,w2,w30],[65,16,86,95,131,53,98,197,87,132,114,79,88,58],[],[[],[0,1,2],[0,2,3],[4],[5,3],[6],[7],[8,5],[2,0,8],[0,9,10],[11,3],[2,0,9],[12,5],[13,0,2],[11,0,2]]),
([w93,w0,w1,w2,w87,w30],[98,198,87,6,65,133,115,79,95,82,88,76,91,199],[],[[0],[1],[2,3],[2,0],[2,0],[4,5,6],[7,5,8],[7,4],[9,4],[10,6,11],[8,4,6],[12,4],[9,4],[7,4,9],[13]]),
([w90,w93,w0,w1,w2,w30],[65,16,76,9,95,133,200,201,87,6,134,96,82,68,116],[],[[],[0,1,2],[0,3,4],[0,2],[5],[6],[7],[8,9],[8,0],[0,10,2],[11,4,10],[12,0],[13,2,12],[13,0,14],[12,0]]),
([w31,w37,w1,w2,w51,w30],[202,203,67,68,6,62,63,10,46,53,17,65,76],[],[[0,1],[2],[3,4,5],[6],[3,7,8],[3,0],[8,9],[10],[5,11],[3,0],[2,0],[3,0],[3,12],[5,9,8],[3,12]]),
([w31,w0,w43,w2,w51,w30],[98,204,68,6,62,205,46,76,96,1,61,11,95],[],[[0],[1,0],[2,3,4],[5],[2,0,6],[2,1,7],[8,1],[9,1],[10,1],[2,7,6],[11],[2,7,4],[2,12],[4,8],[2,12]]),
([w31,w0,w1,w173,w3,w30],[98,110,14,6,62,68,46,96,61,26,59],[],[[0],[1],[2,3,4],[0,4],[5,0,6],[7,5],[7,2],[4,5],[8,6],[2,4,5],[4,7],[5,6],[6,5,9],[4,7],[4,5,10]]),
([w174,w31,w0,w1,w3,w30],[15,62,14,53,96,26,20,69,99,95,68,10,46,76,61],[],[[0,1,2],[3,0,4],[0,1,2],[5,4,6],[1,4],[7],[8],[9,1],[10,11,12],[4,9],[13,1],[14,9,12],[9,1],[10,4,12],[1,3,9]]),
([w31,w0,w1,w2,w3,w175],[69,99,68,62,10,46,61,96,59],[],[[0],[1],[2,0,3],[0,3],[2,4,5],[6,2],[7,3],[2,3],[6,5],[2,3],[3,6],[2,5],[5,2,8],[3,6,5],[3,2,8]]),
([w176,w31,w0,w1,w2,w3],[19,46,18,65,61,40,36,98,110,96,59,76,68,95],[],[[0,1,2],[3,0,4],[0,1,2],[1,4],[5,4,6],[7],[8],[9,10],[11,1],[4,12],[9,10],[11,1],[12,4,10],[13,1],[1,3,10]]),
([w94,w52,w0,w1,w2,w30],[206,185,96,59,61,11,17,188,68,46],[],[[],[0],[1],[2,3],[4,3],[5,6],[6,2,5],[3,2],[3,4],[2,7],[2,3],[4,3],[8,3],[8,2,3],[9,2,4]]),
([w52,w31,w37,w1,w2,w30],[67,63,16,59,68,70,95,46,62,61],[],[[0],[1,2],[0,1],[3,4],[3,4],[4,5],[1],[4,3],[4,3],[4,5],[3,6,7],[3,6,8],[4,3],[4,3],[7,9]]),
([w52,w31,w0,w43,w2,w30],[182,1,62,68,46,70,185,184,61,96],[],[[0],[1,0],[0,1],[2,3],[4,3],[5],[6,7],[3,2],[3,4],[3,2,8],[9,2],[8,4],[3,8,4],[2,9],[2,8,4]]),
([w177,w0,w1,w2,w3,w30],[5,0,8,14,15,62,46,22,10,61,87,96,53,79,88],[27],[[0,1,2],[3,0,4],[5],[6,7],[6,8],[9,10],[11,12,13],[13,6,12],[9,6],[10,9],[14,6,9],[10,6,11],[6,11,100],[6,9],[10,9,13]]),
([w178,w0,w1,w2,w3,w30],[1,0,62,96,95,61,88,79,65,82,97,87],[],[[0,1],[1,0],[2,3],[4],[5],[3,6],[3,2],[7,2,8],[9,6,8],[6,2,10],[6,2,3],[11,3],[9,3],[2,3],[2,6]]),
([w179,w0,w1,w2,w3,w30],[12,0,13,18,19,96,6,87,79,62,82,65,61,91],[42],[[0,1,2],[3,0,4],[5,6],[7,6],[8],[5,7],[5,9],[10,7,11],[10,11],[7,9,12],[13,5],[7,5],[7,5,10],[9,5],[7,12,100]]),
([w52,w0,w1,w2,w9,w30],[79,22,23,96,6,61,207,53,88,68,208],[],[[0,1,2],[1,2],[3,4],[],[0,5],[3,0,6],[0,6,3],[0,6,7],[5,6],[8,5],[8,3],[9,0],[10],[0,3,5],[0,5]]),
([w48,w52,w0,w1,w2,w30],[6,87,53,63,70,207,62,27,82,88,61,79,91,76],[16,22,27],[[0,1],[2,3,100],[2,4,101],[5],[2,6],[7,0],[1,0,2],[8,0,102],[9,10],[2,8,9],[11,2],[8,9,10],[9,2],[12,11,13],[8,2,9]]),
([w52,w0,w1,w2,w30,w88],[39,38,91,6,96,61,76,209,82,53,68,210],[],[[0,1],[1,0],[2,3,4],[5,6],[],[4,2],[4,2],[5,7],[8,7,9],[10,5,8],[2,4],[2,4],[2,4],[2,4],[11]]),
([w89,w52,w0,w1,w2,w30],[76,87,82,63,70,46,209,40,211,212,96,79,65,88,91],[16,22,42],[[0,1],[2,3,100],[0,4,101],[2,5],[6],[0,7],[1,8,9],[2,0,10],[11,0,102],[0,2,9],[10,9],[2,9,12],[13,0],[14,0],[2,10]]),
([w31,w0,w1,w180,w3,w30],[82,91,96,56,44,76,6,62,213,7,61,68,95,86,59],[],[[0],[1],[2,3,4],[5,6,7],[8,9],[8,2],[2,3],[5,7],[10,8],[11,3,4],[12,2,7],[8,2,13],[14,2],[7,2],[7,5]]),
([w181,w31,w0,w1,w3,w30],[96,56,44,68,59,82,91,76,62,46,61,95],[],[[0,1,2],[0,1],[3,1,2],[4,0],[4,0],[5],[6],[7,8],[3,9],[0,3],[7,3,8],[10,9],[11,0,8],[3,0,9],[8,3,7]]),
([w31,w0,w1,w2,w182,w30],[82,91,68,62,76,10,96,61,95,77,86,46],[],[[0],[1],[2,3],[4,3],[2,5],[4,2],[6,3],[4,2,3],[7,8,9],[2,3],[8,3],[2,4,10],[11,2,4],[3,6],[3,2,4]]),
([w183,w31,w0,w1,w2,w30],[76,67,63,95,46,82,91,96,62,214,59,61,68],[],[[0,1,2],[0,1],[3,1,2],[4,0],[4,0],[5],[6],[7,8],[9,10,11],[9,0],[7,3,8],[11,3,9],[12,0,8],[9,0,10],[8,7]]),
([w95,w0,w1,w2,w3,w96],[98,215,68,7,46,76,59,216,96,61,95,217],[],[[0],[1],[2,3,4],[5,0,6],[],[2,7,5],[8,6],[5,2,4],[9,7],[2,5,6],[10,4],[2,5,11],[4,2,5],[6,9],[2,4]]),
([w98,w95,w0,w1,w2,w3],[0,61,18,216,217,91,96,46,95,218,219,59,76,68],[],[[0],[1,2],[2,3,4],[5,1,6],[7,1,8],[9],[10],[5,7],[8,11],[1,4],[6,4],[12,4],[13,1,11],[5,1],[5,6]]),
([w121,w95,w1,w2,w3,w30],[0,95,18,96,91,76,68,62,61,55,98,220],[21,15],[[0],[1,2],[3,1,4],[5,6,7],[8,1,2],[100],[3,9,101],[1,10,101],[11],[6,5,7],[1,3,4],[2,3,4],[4,1,3],[4,3],[7,1]]),
([w106,w95,w0,w2,w3,w30],[0,68,18,76,62,91,61,100,110,221,96,222],[21,20],[[0],[1,2,3],[1,3,4],[5,4,6],[1,3,2],[100],[1,7,101],[3,8,101],[9],[10,4],[3,1,4],[6,11],[5,1],[4,6,10],[4,1,3]]),
([w95,w0,w1,w180,w3,w30],[55,100,76,6,213,96,61,68,223,91,62],[],[[0],[1],[],[2,3],[],[2,4],[5,4],[2,4],[6,4],[7,2,8],[9,5],[4,2,9],[9,2,5],[9,5],[10,2]]),
([w181,w0,w1,w2,w3,w30],[55,51,100,91,46,76,61,79,95,88,224],[],[[0,1],[2,1],[3],[4,5],[4,0,6],[1,7,8],[7,1],[5,4],[6,1,4],[9,1],[8,4],[10,1,4],[4,1],[4,6],[7,1,6]]),
([w181,w95,w0,w1,w3,w30],[7,96,18,68,225,223,91,76,46,224,61,62],[15,20],[[0],[1,2],[3,4,5],[6,1],[6,1],[100],[101],[7],[8],[1,6],[7,3,9],[10,9],[6,1],[3,1,6],[11,3,7]]),
([w181,w0,w1,w3,w30],[96,79,130,0,51,95,68,88,112,44,61,91,46,10,59,76,226,82,224,62],[18,23,12,0,2,17,5,22,29,13,11,14],[[0,1,2,3,4,5,100],[6,7,8,2,4,9,10,101],[11,12,102,0,5,13],[11,1,14,0,10,13,102],[5,0,103,1,7,104,105],[1,15,106,6,12,103],[16,4,7,103,10,17,106],[7,5,104,0,12,16,107],[11,6,18,0,1,16,108],[19,1,109,4,6,110,111]]),
([w95,w0,w1,w2,w182,w30],[98,110,91,6,65,76,96,18,61,227,68,62],[],[[0],[1],[2,3],[],[],[4,2,5],[6,2],[5,4,7],[8,4,9],[10,5,11],[2,4],[2,4],[2,4],[2,4],[11,5]]),
([w183,w0,w1,w2,w3,w30],[98,65,110,91,7,68,76,46,61,96,82,88],[],[[0,1],[2,1],[3,4,5],[6],[7,0,5],[1,3,8],[9,3],[10,1],[8,1,10],[5,8,10],[3,1],[3,1],[3,1],[3,1],[11,5]]),
([w183,w95,w0,w1,w2,w30],[10,76,18,91,228,61,96,46,59,214,68,82],[15,20],[[0],[1,2],[3,4,5],[3,1,6],[7,1,5],[100],[101],[3],[8],[1,3],[6,3],[5,9],[10,1,11],[3,1],[3,5,6]]),
([w183,w0,w1,w2,w30],[76,82,123,0,65,68,95,91,104,63,96,46,7,59,62,79,61,229,88,214],[16,22,12,13,0,2,17,3,8,29,11,14],[[0,1,2,3,4,5,100],[6,7,8,2,4,9,10,101],[11,1,102,0,5,12,103],[11,13,0,5,12,14,103],[5,0,104,1,7,105,106],[15,10,107,6,7,102,104],[1,16,17,4,13,104,107],[18,5,108,0,1,17,105],[7,5,19,0,13,17,109],[1,15,102,4,16,110,111]]),
([w95,w0,w1,w83,w2,w3],[230,231,68,7,46,88,10,51,135,117,232,78,82,76,87,91,61,233],[],[[0],[1],[2,3,4],[4,3],[5,6],[7,8,9],[10,7,8],[11,7],[12,4,13],[2,7,9],[14,7],[15,4,16],[17],[4,2,7],[4,7]]),
([w85,w95,w0,w1,w2,w3],[65,18,61,12,68,135,51,98,234,46,88,136,96,76,87,95],[],[[],[0,1,2],[0,3,4],[5],[6,2],[7],[8],[9,6],[10,0],[0,11,2],[12,6,11],[13,0,9],[14,2],[15,0,9],[9,0,6]]),
([w95,w0,w1,w2,w87,w3],[98,235,88,7,65,137,96,236,82,87,68,91,237],[],[[0],[1],[2,3],[2,0],[2,0],[4,5,6],[6,5],[7,4,5],[8,4],[9,8,10],[9,4],[11,4],[8,4],[8,4],[12]]),
([w89,w95,w0,w1,w2,w3],[65,18,61,12,68,137,98,238,7,88,138,96,82,91],[],[[],[0,1,2],[0,3,4],[0,2],[5],[6],[7],[4,8,9],[9,0],[0,10,2],[11,10],[12,0],[4,2,12],[13,0],[12,0]]),
([w31,w79,w1,w2,w3,w96],[65,98,73,96,7,59,76,46,71,68,51,19,97,95,61],[],[[0,1],[2],[3,4,5],[6,0,7],[8],[0,2,3,9],[3,10,7],[5,0],[11],[12,5],[13,0,7],[2,8],[5,0],[0,14],[6,14]]),
([w31,w0,w81,w2,w3,w96],[55,239,68,59,95,10,46,217,96,76,1,13,77],[],[[0],[1,0],[2,0,3],[4,5,6],[7],[2,1,8],[8,1],[9,1],[10,1],[2,9,6],[3,8],[11],[3,2],[3,12],[2,4]]),
([w31,w0,w1,w184,w3,w30],[98,110,14,7,59,76,46,95,5,65,34,62],[],[[0],[1],[2,3,4],[5,0,6],[0,4],[5,7],[8,2,7],[5,6],[4,7],[2,4,5],[7,6],[4,5],[4,5,6],[6,9,10],[4,5,11]]),
([w185,w31,w0,w1,w3,w30],[15,59,14,51,5,65,34,28,98,110,76,46,61,95,77],[],[[0,1,2],[3,0,4],[0,1,2],[1,5],[6,5,7],[8],[9],[10,5,11],[12,1],[10,13],[10,5,11],[12,1],[13,5,11],[14,1],[1,3,12]]),
([w31,w0,w1,w2,w186,w30],[98,110,96,7,59,16,46,95,76,97,62],[],[[0],[1],[2,3,4],[5,0,6],[0,4],[2,7],[2,4],[8,5],[4,7],[9,4],[5,2,6],[2,4],[4,2],[6,2,10],[4,7,10]]),
([w187,w31,w0,w1,w2,w30],[17,46,16,76,42,36,98,110,96,7,62,61,95,97,68],[],[[0,1,2],[3,0],[0,1,2],[1,3],[4,3,5],[6],[7],[8,9,10],[11,1],[3,12],[8,10],[11,1],[13,3,10],[14,1],[1,8,10]]),
([w97,w98,w0,w1,w2,w3],[240,241,65,62,95,98,19,97,221,220,96,76,46],[],[[],[0],[1],[2,3],[4,3],[5,2],[6,2],[3,7],[3,2,4],[2,8,9],[10,3],[11,2,3],[7,3],[4,2,3],[12,2,4]]),
([w98,w31,w79,w1,w2,w3],[73,71,18,62,97,76,75,95,46,59],[],[[0],[1,2],[0,1],[3,4],[3,5],[4,6],[1],[4,3],[5,3],[4,6],[3,7,8],[3,4,9],[4,3],[7,3],[8,4,5]]),
([w98,w31,w0,w81,w2,w3],[216,1,59,97,46,95,75,241,219,76,96],[],[[0],[1,0],[0,1],[2,3],[4,5],[6],[7,8],[3,2],[5,4],[3,2,9],[10,2],[9,3,4],[3,9,4],[2,10],[2,3]]),
([w188,w0,w1,w2,w3,w30],[97,0,8,14,15,59,76,10,46,88,96,95,79,78,87],[28],[[0,1,2],[3,2,4],[5],[6,7],[8,7],[0,9,6],[10,11,12],[6,0,8],[13,0],[0,6,9],[9,8,10],[14,6],[8,0,6],[8,0,100],[9,6,13]]),
([w189,w0,w1,w2,w3,w30],[97,0,11,16,17,7,46,59,79,96,82,95,88,91],[42],[[0,1,2],[3,2,4],[0,5],[6],[7,5],[0,8],[8,7,9],[8,0],[10,0],[0,7],[11,9,12],[13,7,9],[7,0],[8,0,10],[7,11,100]]),
([w98,w0,w1,w2,w3,w84],[31,30,97,7,46,76,242,96,78,243,95,87,244],[],[[0,1],[1,0],[2,3],[4,5],[],[2,6,5],[7,6],[5,2,4],[8,2],[2,5,9],[10,4],[11,4,5],[4,2,5],[12],[8,5]]),
([w86,w98,w0,w1,w2,w3],[46,7,51,242,59,55,34,91,95,245,78,76,87],[37,29,28],[[0,1],[2,0,100],[2,0,101],[3],[2,4],[5,2],[6,1],[7,1,102],[0,8],[2,7,9],[10,2],[11,0],[12,2],[7,0,8],[0,2]]),
([w98,w0,w1,w2,w3,w88],[39,38,59,97,95,10,246,247,96,76,82,91,248],[],[[0,1],[1,0],[2,3],[4,5],[],[3,6,7],[8,2],[9,3,6],[10,2,3],[3,2],[4,7],[11,2,8],[2,3],[10,3],[12]]),
([w90,w98,w0,w1,w2,w3],[59,10,97,65,46,246,43,42,87,249,96,82,91],[37,29,42],[[0,1],[2,0,100],[3,0,101],[2,4],[5],[6,1],[7,1],[0,2],[8,1,102],[2,8,9],[10,0],[11,2],[2,0],[12,3],[0,2]]),
([w56,w31,w34,w2,w3,w30],[15,14,56,95,96,46,77,5,100,78],[],[[0,1],[2],[0,2],[3,4,5],[6,4,5],[3,7],[4,8,9],[3,5],[6,5],[0],[5,6],[5,3,6],[5,3],[5,4,6],[9,3]]),
([w31,w99,w1,w2,w3,w30],[95,1,20,250,80,78,251,102,46,24,26,76,96,94],[31],[[0,1],[2],[3,4,5],[6,7,8],[5,4],[0,1],[9],[10],[8,0,100],[3,11],[3,12],[13,3],[2,11,5],[8,12,13],[5,11]]),
([w58,w31,w1,w2,w3,w30],[95,66,70,0,20,59,61,26,156,96,77,102,82],[],[[0,1,2],[0,1],[3,0],[4],[5,0,6],[7],[8,5,9],[10,11,12],[6,5],[5,6],[10,6,8],[10,5],[5,9],[12,6,9],[5,6]]),
([w31,w100,w1,w2,w3,w30],[95,1,28,252,7,78,102,46,32,65,34,51,96,82],[30],[[0,1],[2],[3,4,5],[0,6,7],[5,4],[0,1],[8],[5,9,100],[10],[3,11],[0,3],[3,11],[5,0],[2,12,13],[5,0]]),
([w101,w31,w1,w2,w3,w30],[95,55,96,1,0,78,65,76,28,34,102,82,77],[],[[0,1],[0,2,3],[4,0],[5,6,7],[8],[9],[2,1,5],[0,10,11],[5,1],[7,11],[0,2,5],[12,2],[5,0],[11,2],[5,0]]),
([w31,w34,w40,w2,w3,w30],[14,1,8,15,7,78,77,46,44,96,86,51],[],[[0,1,2],[0,3],[0,4,5],[6,7],[5,4],[0,1],[0],[5,6],[7,6],[8],[5,9,10],[6,9,10],[5,6],[7,6],[5,11]]),
([w31,w34,w40,w3,w30],[14,5,7,51,88,77,52,253,46,6,78,54,254,97,255,86,96,53],[13,47,14,48,49,50,11],[[0,1,2,3],[0,2,3],[4,5,6,7,8,9],[10,5,11,2,8],[0,1],[8,100,12,5,13,101],[4,102,3,5,13,103],[5,100,14,15,16,104],[4,102,3,15,16,105],[10,4,100,3,17,106,102]]),
([w31,w34,w43,w2,w3,w30],[53,69,0,96,88,77,89,256,97,16,90,63],[],[[0,1],[0,2],[3,0,4],[4,0],[5,6,7],[0,3,8],[9],[0,5],[4,5],[0,10],[11],[4,3,10],[3,5],[4,0],[4,0]]),
([w31,w34,w81,w2,w3,w30],[51,55,0,96,78,77,92,256,97,18,93,71],[],[[0,1],[0,2],[3,0,4],[5,6,7],[4,0],[0,3,8],[9],[4,5],[0,5],[0,10],[4,3,10],[11],[4,0],[3,5],[4,0]]),
([w31,w34,w1,w46,w3,w30],[53,69,20,96,78,52,7,21,97,82,5,94,105,26,46,59],[],[[0,1],[2],[3,0,4],[5,0],[4,6],[0,7,8],[2,0],[2,0,9],[9,8],[0,10],[0,4],[11,3,12],[13],[14,0],[4,0,15]]),
([w48,w31,w34,w1,w3,w30],[96,257,6,22,53,5,20,26,77,52,7,27,97,59,82,106],[],[[0,1,2],[3],[4,5],[6],[4,0],[1,2],[7],[8,1,9],[1,10],[0,11,12],[13,4],[14,8,12],[8,0,15],[8,0,13],[13,4]]),
([w31,w34,w1,w83,w3,w30],[258,165,28,252,7,52,6,78,51,97,82,95,34],[],[[0,1],[2],[3,4,5],[5,6],[7,4],[8,0,9],[2,8],[7,9,10],[2,8,10],[0,8],[11,0],[0,8],[7,8],[12],[7,8]]),
([w86,w31,w34,w1,w3,w30],[7,259,30,51,5,96,28,34,6,78,35,97,82,95,77,108],[],[[0,1],[2],[3,4],[3,5],[6],[1,0],[7],[1,8],[9,0],[3,10,11],[9,11,12],[12,3],[13,5,9],[14,3,15],[9,3]]),
([w62,w31,w37,w2,w3,w30],[17,16,67,97,82,94,96,59,9,99,112,101],[],[[0,1],[2],[3,4],[0,2],[5,6,7],[3,8],[3,7],[4,9],[4,7,5],[4,5,10],[0],[7,3,11],[4,3],[4,3],[7,5]]),
([w64,w31,w1,w2,w3,w30],[97,109,60,20,46,86,24,78,6,81,53,76],[],[[0,1,2],[0,1],[3],[3,0],[4,0,5],[6],[7,8],[5,4],[5,4],[9,10],[4,10],[9,4],[4,5],[4,5],[7,9,11]]),
([w31,w103,w1,w2,w3,w30],[97,1,36,83,78,260,82,59,86,53,40,42,96,76],[33],[[0,1],[2],[0,3,4],[5,3,6],[4,7,8],[0,1],[6,9,100],[10],[11],[0,5],[4,12],[5,12],[4,0,6],[6,0],[2,13,4]]),
([w104,w31,w1,w2,w3,w30],[6,72,75,53,97,82,96,0,36,42,261,78,80,81,76],[],[[0,1,2,3],[4,1],[5,3,6],[7,3],[8],[9],[4,10,11],[5,10],[5,12],[4,5],[6,11],[13,6],[5,4],[5,4],[11,13,14]]),
([w31,w37,w40,w2,w3,w30],[53,69,0,14,52,81,80,256,76,97,262,44,86],[],[[0,1],[0,2],[3,0,4],[4,0],[5,6,7],[0,8,9],[0,5],[3],[10,5],[11],[0,12],[5,8,12],[5,8],[10,0],[10,0]]),
([w31,w37,w43,w2,w3,w30],[16,6,69,52,82,59,81,63,53,90,262],[],[[0,1,2],[0,1],[3,1],[0,1,3],[4,5,6],[0,7],[4,6],[0],[5,6],[4,8,9],[7],[5,9],[4,6],[4,8,10],[5,6]]),
([w31,w37,w43,w2,w30],[16,6,1,53,52,81,59,82,256,263,10,63,95,90,76,262,65],[12,47,14,51,49,52,11],[[0,1,2,3,4],[0,1,3],[4,5,1,6],[7,5,8,9,6,10],[0,2,11],[6,100,3,5,12,101],[6,102,12,5,103],[5,100,3,13,14,104],[5,102,14,13,105],[7,15,100,16,3,106,102]]),
([w31,w37,w81,w2,w3,w30],[82,92,0,19,81,259,65,76,95,18,93,71],[],[[0,1],[0,2,3],[4,1,5],[0,1],[0,5],[6,7,8],[0,4],[9],[4,6],[0,7,10],[6,10],[11],[0,4],[0,6],[4,7]]),
([w31,w37,w1,w46,w2,w30],[82,6,20,52,10,53,21,95,78,9,94,113,24,59,46],[],[[0,1],[2],[0,1],[3,1],[0,4],[5,6,7],[2,5],[0,5,8],[8,7],[5,9],[0,5],[10,11],[12],[13,5],[0,5,14]]),
([w47,w31,w37,w1,w2,w30],[6,256,22,53,9,20,76,24,52,10,25,95,78,81,114,46],[],[[0,1],[2],[3,4],[5],[3,6],[1,0],[7],[8,0],[1,9],[3,10,11],[12,3],[12,11],[13,3,14],[13,6,14],[15,3]]),
([w31,w37,w1,w2,w87,w30],[264,265,36,52,6,10,82,95,78,97,65,42],[],[[0,1],[2],[3,4],[3,5],[6,5],[7,0],[6,7,8],[2,7],[2,7,8],[9,0],[0,10],[0,10],[6,9],[6,9],[11]]),
([w90,w31,w37,w1,w2,w30],[10,259,38,65,9,76,36,42,6,82,43,95,78,97,81,116],[],[[0,1],[2],[3,4],[3,5],[6],[1,0],[7],[1,8],[9,0],[3,10,11],[9,11,12],[12,3],[13,5,9],[14,3,15],[9,3]]),
([w106,w31,w79,w2,w3,w30],[19,18,73,97,82,95,65,78,110,256,112,104],[],[[0,1],[2],[3,4],[5,6,7],[0,2],[3,8,4],[3,9,7],[4,8],[4,8],[4,5,10],[7,3,11],[0],[4,3],[4,3],[7,5]]),
([w107,w31,w1,w2,w3,w30],[10,109,111,65,95,28,78,76,32,256,84,46,86],[],[[0,1,2,3],[4,1],[5],[6,3,7],[5,3],[8],[6,9],[4,2,9],[6,2],[10,7],[4,6],[7,11],[6,4],[11,10,12],[6,4]]),
([w108,w31,w1,w2,w3,w30],[95,98,1,82,90,36,40,256,52,97,84,65,59],[],[[0,1],[0,2],[3,0,4],[5],[5,0],[6],[4,7,8],[3,1],[3,1],[9,3],[10,11],[4,11],[3,4],[3,9],[12,4]]),
([w31,w79,w40,w2,w3,w30],[12,85,14,15,256,78,95,76,84,65,86],[],[[0,1],[2,3],[2,4,5],[4,1],[0,1,4],[6,7],[6,8],[5,8],[2],[0],[5,9,10],[7,10],[5,6],[8,10],[5,6]]),
([w31,w79,w43,w2,w3,w30],[65,98,0,84,256,259,76,95,82,16,90,63],[],[[0,1],[0,2],[3,4,5],[3,0,4],[4,0],[0,6,7],[8,3],[0,3],[9],[3,6,10],[11],[0,10],[8,0],[8,0],[3,10]]),
([w31,w79,w81,w2,w3,w30],[18,10,98,84,256,78,71,82,76,93],[],[[0,1,2],[0,1],[3,4,5],[3,1,4],[0,1,4],[0,6],[7,3],[5,3],[0],[3,8,9],[3,9],[6],[5,8],[7,3],[5,3]]),
([w31,w79,w81,w2,w3],[18,10,1,65,256,78,84,54,62,71,95,94,76,93,61,82],[12,48,13,51,50,52,10],[[0,1,2,3,4],[0,1,3],[5,6,7,4,8],[4,6,1,8],[0,2,9],[8,100,10,6,11,101],[5,102,3,6,11,103],[6,100,12,13,14,104],[5,102,3,13,14,105],[15,5,100,3,10,106,102]]),
([w31,w79,w1,w83,w2,w3],[256,10,28,7,78,76,29,95,46,94,79,12,117,32],[],[[0,1],[2],[0,3],[4,0],[0,1],[5,6,7],[2,7],[2,7,8],[4,9,10],[5,11],[5,12],[7,4],[13],[4,5],[4,5]]),
([w85,w31,w79,w1,w2,w3],[10,256,30,65,12,28,76,90,32,78,33,95,93,84],[],[[0,1],[2],[3,4],[5],[6,7],[1,0],[8],[9,1],[1,0],[3,10,11],[12,11,8],[6,3,13],[13,6,12],[11,3,9],[9,3,6]]),
([w31,w79,w1,w2,w87,w3],[65,98,36,78,256,37,94,90,79,97,82,40],[],[[0,1],[2],[3,4],[3,0],[4,0],[0,5,6],[7,6,8],[2,0],[2,0,8],[9,7],[0,7],[0,3],[10,0],[3,0,10],[11]]),
([w89,w31,w79,w1,w2,w3],[10,257,38,65,12,86,36,40,256,41,94,90,79,97,95,120,82],[],[[0,1],[2],[3,4],[3,5],[6],[1,0],[7],[1,8],[8,0],[3,9,10],[11,10,12],[12,3],[13,11],[14,3,15],[16,3]]),
([w110,w31,w40,w2,w3,w30],[8,14,86,97,84,46,55,259,88,94],[],[[0,1],[1],[0,1],[2,3,4],[2,3,5],[1,0],[1,6,7],[2,5],[2,5],[0],[4,2],[5,2],[5,2],[5,2],[8,4,9]]),
([w31,w0,w111,w2,w3,w30],[21,256,0,76,266,259,85,94,61,25,27,97,95,46,88],[35],[[0],[1,2,3],[4,1,5],[1,6],[1,5],[3,2],[4,7],[4,7],[8,4],[9],[10],[7,3,100],[0,11,12],[13,7],[14,7]]),
([w112,w31,w0,w2,w3,w30],[256,67,76,1,21,88,94,27,85,59,86,97],[],[[0,1,2],[2,1],[3,2],[4],[5,2,6],[7],[5,0],[0,8],[0,8],[6,9],[10,6],[10,5],[9,10,11],[5,6],[5,6]]),
([w31,w0,w113,w2,w3,w30],[29,256,0,76,267,88,85,94,97,33,46,65,35],[34],[[0],[1,2,3],[4,1,5],[1,6],[1,6],[3,2],[4,7],[3,4],[4,8],[9],[10,11,100],[12],[10,3],[0,7,5],[5,3,7]]),
([w114,w31,w0,w2,w3,w30],[256,73,76,1,86,65,95,29,35,159,259,85,91,97,62],[],[[0,1,2],[2,1],[3,2],[4,5,6],[7],[8],[9,0,10],[0,11],[0,10],[6,9],[2,9],[4,6,9],[12,2,13],[12,4,13],[14,2]]),
([w31,w0,w40,w46,w3,w30],[21,268,161,266,6,259,94,46,61,59,65,91,162],[],[[0],[1,2],[3,4,5],[5,4],[6,5,7],[6,1,8],[1,6],[1,6],[8,1],[0,8],[0,8,9],[6,10,11],[12],[7,6],[9,6]]),
([w48,w31,w0,w40,w3,w30],[259,257,94,14,23,125,97,27,26,164,61,86,126,59],[],[[0,1],[2,3],[4],[5],[2,6],[7],[0,8,9],[0,1],[1,0],[2,8,10],[11,2,12],[10,6,12],[13,10],[2,11],[13,2]]),
([w31,w0,w40,w83,w3,w30],[29,269,166,267,7,259,85,257,97,76,51,46,65,91,157,88,62],[],[[0],[1,2],[3,4,5],[5,6],[7,4],[8,1,9],[1,10],[9,1],[1,8],[0,8],[11,12,13],[0,9,13],[11,8,9],[14],[15,9,16]]),
([w86,w31,w0,w40,w3,w30],[97,259,7,51,14,31,127,35,85,94,257,34,76,128,86,91,65,62],[],[[0,1,2],[3,4],[5],[3,0],[6],[7],[1,2],[1,8],[9,1,10],[0,11,12],[12,0,13],[14,0,13],[15,14,16],[9,3,7],[17,3]]),
([w116,w31,w43,w2,w3,w30],[10,16,90,94,91,1,65,88,98,59,11],[],[[0,1],[1],[2,3,4],[5,1],[2,6,7],[1,8],[2,9],[1,8,4],[2,8,4],[4,2],[10],[3,2],[4,2],[4,3,7],[7,2]]),
([w117,w31,w0,w2,w3,w30],[10,56,44,65,76,21,88,94,25,89,129,257,90,46,95],[],[[0,1,2,3],[4,1],[5],[5,3],[6,3,7],[8],[6,9],[6,10],[7,9,11],[12,7],[7,13],[12,6],[13,12,14],[6,7],[6,7]]),
([w31,w0,w118,w2,w3,w30],[98,65,0,88,89,270,257,76,96,91,41,43,94],[32],[[0],[1,2],[3,4],[3,0],[5,0,6],[1,2,7],[8,5],[1,5],[1,3],[9,7,100],[10],[11],[9,1],[3,1,9],[3,12]]),
([w119,w31,w0,w2,w3,w30],[10,73,65,76,91,97,1,37,98,89,257,90,62,95],[],[[0,1,2],[3,1],[4,3,5],[6,2],[7],[8],[5,9,10],[4,0],[4,0],[11,4],[2,12],[11,2],[4,2],[4,2],[12,11,13]]),
([w31,w0,w43,w46,w2,w30],[21,271,194,272,6,91,88,10,95,76,53,61,46,87,196],[],[[0],[1,2],[3,4,5],[6,4],[5,7],[8,1,9],[1,10],[1,8],[11,1],[0,8],[0,9,12],[6,9,13],[14],[6,8,10],[5,10,6]]),
([w47,w31,w0,w43,w2,w30],[10,256,65,16,23,131,53,95,69,90,88,24,76,132,46],[],[[0,1],[2,3],[4],[5],[6,7],[8],[1,0],[9,1,10],[1,0],[2,11,12],[9,6,13],[9,2,10],[14,6],[10,2,9],[10,2,6]]),
([w31,w0,w43,w2,w87,w30],[37,273,198,88,6,10,91,65,76,96,87,199],[],[[0],[1,2],[3,4],[3,5],[6,5],[7,1,8],[9,1],[1,7],[1,7],[6,8,10],[0,7],[0,7,10],[6,7],[3,7,6],[11]]),
([w90,w31,w0,w43,w2,w30],[6,259,53,16,39,65,95,133,98,91,42,76,90,134,87],[],[[0,1],[2,3],[4],[5,6],[7],[8],[1,0],[1,0],[9,1],[2,10,11],[12,2,9],[12,5,13],[9,2,12],[14,5],[9,2,5]]),
([w121,w31,w81,w2,w3,w30],[10,18,96,91,76,65,87,1,256,98,93,13],[],[[0,1],[1],[2,3],[4,5,6],[7,1],[1,2],[2,8,6],[3,9],[1,9,3],[3,4,10],[6,2,10],[11],[3,2],[3,2],[6,4]]),
([w122,w31,w0,w2,w3,w30],[10,56,44,65,76,29,87,95,33,92,256,129,93,88,94],[],[[0,1,2,3],[4,1],[5],[6,3,7],[5,3],[8],[6,9],[4,9,10],[6,11],[12,7],[4,6],[7,13],[6,4],[13,12,14],[6,4]]),
([w123,w31,w0,w2,w3,w30],[10,67,65,76,93,97,37,98,92,88,214,256,91,94],[],[[0,1,2],[3,1],[4,3,5],[6],[6,2],[7],[4,8,9],[4,0,9],[10,0,11],[4,10],[4,2,10],[2,9],[12,2],[9,2,12],[9,4,13]]),
([w31,w0,w81,w83,w2,w3],[29,274,231,275,7,256,87,10,94,76,51,88,53,233],[],[[0],[1,2],[3,4,5],[6,4],[5,7],[8,1,9],[1,10],[1,8],[9,1],[0,8],[0,9,11],[6,12,11],[13],[6,8,9],[6,9]]),
([w85,w31,w0,w81,w2,w3],[10,256,65,18,31,135,51,94,98,87,32,76,93,136,88],[],[[0,1],[2,3],[4],[5],[6,7],[8],[1,0],[9,1],[1,0],[2,10,11],[12,6,13],[11,2,9],[14,6],[9,2,12],[9,2,6]]),
([w31,w0,w81,w2,w87,w3],[98,276,87,256,65,96,88,53,91,237],[],[[0],[1,0],[2,3],[2,0],[3,0],[4,1,5],[5,1],[1,4],[1,4],[6,7],[6,4],[2,4,6],[8,4],[2,4,8],[9]]),
([w89,w31,w0,w81,w2,w3],[10,257,65,18,39,94,137,98,256,40,76,96,138,88,91],[],[[0,1],[2,3],[4],[2,5],[6],[7],[1,0],[1,8],[8,0],[2,9,10],[11,5,12],[10,2,12],[13,10],[13,2],[14,2]]),
([w31,w0,w1,w46,w9,w30],[98,140,76,6,46,94,90,97],[24,12,14],[[0],[1],[2,3],[0,4],[5,0,4],[1,2],[2,1],[1,5],[6,1],[7,6],[2,4],[5,2,4],[100],[4,2,5],[101,5,102]]),
([w190,w0,w1,w2,w3,w30],[98,110,14,6,44,16,63,94,88,76,90,259,53],[],[[0],[1],[2,3,4],[5,0,6],[7,0],[7,8,9],[10,7,11],[9,7,11],[10,8],[8,9],[8,12],[7,9,10],[9,10],[8,7],[8,7]]),
([w191,w0,w1,w2,w3,w30],[69,53,0,44,14,63,16,88,94,76,90,259,46],[],[[0,1],[2,0],[3,0,4],[5,0,6],[7,8],[1,7,9],[10,1,11],[9,1,11],[10,7],[7,1],[7,1],[8,9,10],[12,9],[7,1],[7,1]]),
([w31,w126,w1,w2,w3,w30],[53,69,22,90,259,1,94,65,81,95,93,79],[37],[[0,1],[2],[3,0,4],[4,0],[3,4,100],[0,5,6],[2,0],[2,0],[3,7,8],[8,0,3],[9,0,10],[6,3],[2,3,9],[11,0],[11,0]]),
([w31,w0,w127,w2,w3,w30],[69,53,0,90,259,76,81,84,63,88],[29],[[0],[1,2],[3,0,4],[4,0],[3,4,100],[1,2,5],[3,1,6],[5,1,7],[3,6],[6,1,3],[7,1,8],[6,3],[3,5],[9,1],[9,1]]),
([w192,w0,w1,w2,w3,w30],[53,69,0,90,91,16,63,10,46,96,81,256,59],[2],[[0,1],[0,2],[3,0,4],[5,0,6],[3,7,8],[0,100,9],[3,0,10],[11,0],[3,8],[10,0,3],[11,0],[10,3],[8,3,12],[8,0],[12,0]]),
([w193,w0,w1,w2,w3,w30],[98,110,90,56,16,63,46,65,76,81,256,53],[2,13],[[0],[1],[2,3],[4,0,5],[2,0,6],[7,100,8],[2,9],[8,6],[2,6],[9,2],[10,6,7],[9,2],[6,2,8],[6,7,11],[101,2,8]]),
([w31,w128,w1,w2,w3,w30],[65,98,24,81,6,256,1,94,20,90,46,76],[18,13],[[0,1],[2],[3,4,100],[5,0],[3,0,5],[0,6,7],[8,2],[2,0],[9,0,3],[3,9],[0,10],[3,0,9],[10,0,11],[10,0,7],[101,3,11]]),
([w31,w0,w76,w2,w3,w30],[69,53,0,81,256,46,76,90,16,95],[23,13],[[0],[1,2],[3,0,100],[4,0],[3,5],[1,2,6],[7,1,3],[1,5],[7,3],[3,1,7],[8,1,5],[3,5],[5,3,9],[5,1],[101,1,9]]),
([w31,w0,w1,w2,w3,w129],[69,99,90,76,46,95,81,30,34,36],[],[[0],[1],[2,0],[3,0,4],[2,4],[3,5],[2,5,6],[3,4],[2,4],[6,2],[5,4],[6,2],[4,2,3],[4,7,8],[9,2,3]]),
([w31,w0,w1,w2,w3,w130],[69,99,81,62,46,96,94,90,40],[12],[[0],[1],[2,0,3],[0,3],[2,4],[5,6],[5,2],[3,6],[7,2],[2,3],[3,5],[2,4],[4,2,100],[3,5],[3,2,8]]),
([w194,w0,w1,w2,w3,w30],[53,69,0,14,44,76,46,94,257,95,62],[8],[[0,1],[0,2],[3,0,4],[5,0,6],[7,6],[0,100,5],[8,0],[5,0,6],[8,6,9],[8,0],[9,0,6],[7,5,6],[6,5],[6,0],[10,0,5]]),
([w195,w0,w1,w2,w3,w30],[69,99,14,44,46,94,10,59,76,90,84,53,93],[8,12],[[0],[1],[2,0,3],[4,0],[5,6,7],[5,100,8],[9,5,7],[8,5,10],[9,7],[10,7],[10,11,12],[5,7],[7,8,9],[101,5,10],[7,5]]),
([w31,w131,w1,w2,w3,w30],[53,69,26,90,59,76,1,94,95,93],[16,12],[[0,1],[2],[3,0,4],[5,0,100],[3,4],[0,6,7],[2,0],[5,0,2],[3,4],[0,3],[8,0,9],[7,3],[4,3],[101,0,9],[4,0]]),
([w31,w0,w78,w2,w3,w30],[69,76,0,81,59,53,84,61,27],[22,12],[[0],[1,0,2],[3,0,4],[1,0,100],[3,4],[1,2],[3,5],[1,5,6],[7,3],[3,1,4],[6,5,8],[3,1,4],[4,1,3],[101,5,6],[4,1,3]]),
([w31,w0,w1,w2,w3,w132],[69,99,84,59,94,76,93,90,65,28],[],[[0],[1],[2,0,3],[2,0],[4,3],[5,4],[6,2],[5,2],[7,3],[2,3],[2,6],[4,3],[3,5,8],[9,2,4],[3,2,4]]),
([w31,w0,w1,w2,w133,w3],[69,99,59,94,76,62,90,95,32],[13],[[0],[1],[0,2],[3,2],[4,0,5],[4,3],[2,3],[6,2],[4,3,5],[2,4],[3,2],[7,5],[5,3,8],[2,4,100],[2,3]]),
([w31,w0,w1,w83,w3,w84],[69,142,94,7,76,62,93,95],[25,12,13],[[0],[1],[2,3],[4,0,5],[0,5],[1,4],[6,1],[4,1],[1,2],[2,4,6],[7,5],[4,5],[5,2,4],[100],[101,4,102]]),
([w196,w0,w1,w2,w3,w30],[69,99,14,44,76,18,10,71,87,93,53,84,90,65,81],[],[[0],[1],[2,0,3],[4,0],[5,6,7],[4,8],[9,10,11],[4,8],[12,13,14],[8,4],[11,9],[8,4],[8,4],[9,10],[8,4]]),
([w197,w0,w1,w2,w3,w30],[69,53,0,44,14,62,76,71,10,18,87,93,61,65,59,84],[],[[0,1],[2,0],[3,0,4],[5,0,6],[7,8,9],[1,10,6],[11,1,5],[6,1,5],[12,13,14],[10,1],[15,1,5],[10,6],[10,6],[5,1,11],[5,1,6]]),
([w31,w134,w1,w2,w3,w30],[65,98,30,93,6,257,1,94,84,90,78,76],[16],[[0,1],[2],[3,4,5],[3,0,100],[5,0],[0,6,7],[2,3],[3,0,8],[2,0],[8,3],[8,0,3],[7,0,9],[10,0,11],[0,7],[10,3]]),
([w31,w0,w135,w2,w3,w30],[69,53,0,84,87,10,76,93,61,65,81,71],[22],[[0],[1,2],[3,0,4],[3,0,100],[4,5],[1,2,6],[7,1,3],[6,1,3],[8,9,10],[3,1,7],[3,1,7],[10,6,11],[4,6],[1,3],[4,1,3]]),
([w198,w0,w1,w2,w3,w30],[65,98,0,93,56,62,18,71,76,256,84,59],[2],[[0,1],[0,2],[3,4,5],[3,0,5],[6,0,7],[0,100,8],[3,5],[3,0,5],[9,0],[10,3],[9,0],[9,0],[11,0],[5,0],[5,3]]),
([w199,w0,w1,w2,w3,w30],[98,110,84,56,46,18,65,76,93,61,81],[2,13],[[0],[1],[2,3],[2,0,4],[5,0,4],[6,100,7],[8,2],[7,2],[9,4],[2,7,8],[2,4],[10,4],[4,6,7],[4,2,9],[101,2]]),
([w31,w136,w1,w2,w3,w30],[65,98,32,93,83,46,61,1,94,84,76],[18,13],[[0,1],[2],[3,4,100],[3,0,5],[6,0,5],[0,7,8],[3,2],[3,0,5],[2,0],[9,3],[9,0,3],[0,5],[5,0,10],[5,0,6],[101,3]]),
([w31,w0,w137,w2,w3,w30],[98,65,0,93,92,46,94,76,84],[23,13],[[0],[1,2],[3,4,100],[3,0,5],[6,0,5],[1,2,7],[3,6,8],[3,1,5],[1,5],[8,3],[8,1,3],[6,1,5],[5,1,7],[5,1,6],[101,3]]),
([w31,w0,w1,w2,w138,w30],[69,99,84,46,94,76,93,61,36],[],[[0],[1],[2,0],[2,0,3],[4,3],[5,4],[6,2],[5,2],[7,3],[2,5,6],[2,3],[4,3],[3,5],[3,2,4],[8,2,4]]),
([w31,w0,w1,w2,w139,w30],[98,110,93,6,59,46,76,95,84,42],[12],[[0],[1],[2,3,4],[2,0,5],[0,4],[6,7],[2,4],[2,5],[4,7],[8,2],[7,2],[4,6],[4,6,5],[5,2,100],[4,2,9]]),
([w200,w0,w1,w2,w3,w30],[53,69,0,14,44,76,46,61,259,94,59],[20],[[0,1],[0,2],[3,0,4],[5,0,6],[7,6],[0,100,5],[8,0],[5,0,6],[7,6],[8,0],[8,0],[9,5,6],[6,5],[6,0],[10,0]]),
([w201,w0,w1,w2,w3,w30],[69,99,14,44,76,62,46,19,93,61,259,81,90],[20,12],[[0],[1],[2,0,3],[4,0,5],[6,7],[4,100],[8,5],[4,5],[9,10,11],[10,4],[10,5,9],[11,4,12],[101,4,11],[5,8],[5,4]]),
([w31,w140,w1,w2,w3,w30],[53,69,34,259,61,1,94,76,62,95,90,93],[37,12],[[0,1],[2],[3,0],[3,0],[4,3,100],[0,5,6],[2,0],[7,0,8],[4,2],[0,8],[9,0,8],[6,7,10],[101,7,10],[8,0,11],[8,0,7]]),
([w31,w0,w141,w2,w3,w30],[69,61,0,259,53,62,76,95,81,35,84],[29,12],[[0],[1,0,2],[3,0],[3,0],[1,3,100],[1,2],[4,5],[6,4,5],[1,7,8],[8,1,5],[7,1,5],[8,6,9],[101,6,8],[5,1,10],[5,1,6]]),
([w31,w0,w1,w2,w142,w30],[69,99,81,62,76,10,95,90,20,53,65],[],[[0],[1],[2,0,3],[4,0,3],[2,5],[4,6],[7,2],[4,3],[7,2],[2,3],[6,3],[2,4,7],[8,2,4],[3,9,10],[3,2,4]]),
([w31,w0,w1,w143,w2,w30],[69,99,76,46,62,61,10,59,95,94],[14],[[0],[1],[2,0,3],[0,4],[5,6,7],[2,8],[2,3],[4,8],[5,7],[8,3],[2,4],[9,2,7],[3,2],[3,2],[4,5,100]]),
([w31,w0,w1,w2,w87,w88],[98,144,90,62,76,65,81],[12,26],[[0],[1],[2,3],[2,0],[0,3],[1,4],[2,1],[2,1],[1,5],[6,2],[6,2],[3,4],[3,4,5],[100,2],[101]]),
([w202,w0,w1,w2,w3,w30],[98,110,81,6,16,63,71,65,91,76,90,84],[],[[0],[1],[2,3],[4,0,5],[2,0,6],[7,8,9],[10,2],[9,7,11],[10,2],[2,9,10],[8,7],[2,7,8],[8,2],[8,7],[2,9]]),
([w203,w0,w1,w2,w3,w30],[98,65,0,62,81,16,71,91,76,90],[],[[0,1],[2,0],[3,4],[3,0,5],[6,0,4],[1,7,8],[9,3],[8,1,3],[9,1,4],[4,3],[7,1],[4,1,7],[7,1],[3,1],[3,4,8]]),
([w31,w144,w1,w2,w3,w30],[65,98,38,90,6,76,256,1,95,81,93,82],[18],[[0,1],[2],[3,4,100],[5,0,6],[3,0,6],[0,7,8],[3,8,9],[2,0],[2,0],[9,3],[8,0,10],[9,0,3],[11,0],[11,0],[2,5,3]]),
([w31,w0,w145,w2,w3,w30],[98,65,0,90,6,76,91,84,81,63],[23],[[0],[1,2],[3,4,100],[5,0,6],[3,0,6],[1,2,5],[3,6],[5,1,7],[3,1,8],[6,3],[7,1,9],[8,1,3],[6,1],[6,1],[3,5]]),
([w204,w0,w1,w2,w3,w30],[65,98,0,84,6,62,18,71,76,93,257,46],[8],[[0,1],[0,2],[3,4,5],[3,0,5],[6,0,7],[0,100,8],[9,3],[8,0,3],[10,0],[3,5],[3,0,5],[10,0],[11,0,8],[5,0],[5,3]]),
([w205,w0,w1,w2,w3,w30],[98,110,90,6,59,76,65,84,93,81],[8,12],[[0],[1],[2,3,4],[5,0],[2,0,4],[5,100],[2,4],[5,6,7],[2,4],[7,2],[7,6,8],[9,2],[4,2],[101,6],[4,2]]),
([w31,w146,w1,w2,w3,w30],[65,98,40,93,83,59,90,1,95,84],[16,12],[[0,1],[2],[3,4,5],[3,0,100],[6,0,5],[0,7,8],[3,5],[3,0,2],[2,0],[9,3],[8,0,3],[0,5],[5,0],[101,0],[5,3,6]]),
([w31,w0,w147,w2,w3,w30],[98,65,0,93,92,59,81,76,84],[22,12],[[0],[1,2],[3,4,5],[3,0,100],[6,0,5],[1,2,7],[3,5],[3,1,8],[1,5],[6,3],[8,1,3],[6,1,5],[5,1],[101,1],[5,3,6]]),
([w31,w0,w1,w148,w3,w30],[69,99,84,59,94,76,93,61,24,28],[],[[0],[1],[2,0,3],[2,0],[4,3],[5,4],[6,2],[5,2],[7,3],[2,3],[2,6],[4,3],[3,5,8],[9,2,4],[3,2,4]]),
([w31,w0,w1,w149,w3,w30],[98,110,93,59,46,76,95,84,34],[13],[[0],[1],[2,3],[2,0,4],[0,3],[5,6],[2,3],[2,4],[3,6],[7,2],[6,2],[3,5],[3,5,4],[4,2,8],[3,2,100]]),
([w206,w0,w1,w2,w3,w30],[65,98,0,81,59,16,63,61,90,259,46],[20],[[0,1],[0,2],[3,4],[5,0,6],[3,0,4],[0,100,7],[8,3],[9,0],[7,0,3],[3,4],[9,0],[3,0,4],[4,0],[10,0,7],[4,3]]),
([w207,w0,w1,w2,w3,w30],[98,110,81,6,62,16,65,76,90,84],[20,12],[[0],[1],[2,3,4],[5,0,4],[2,0],[6,100,7],[8,2],[7,4],[8,2],[2,4],[9,4],[2,6,8],[101,2],[4,6],[4,2,7]]),
([w31,w150,w1,w2,w3,w30],[65,98,42,90,6,62,76,1,95,81],[37,12],[[0,1],[2],[3,4,5],[6,0,5],[3,0,100],[0,7,8],[3,5],[2,0],[3,0,2],[9,3],[0,5],[9,0,3],[101,0],[5,0],[5,3,6]]),
([w31,w0,w151,w2,w3,w30],[98,65,0,90,6,62,95,76,81],[29,12],[[0],[1,2],[3,4,5],[6,0,5],[3,0,100],[1,2,7],[3,5],[1,5],[3,1,8],[8,3],[6,1,5],[8,1,3],[101,1],[5,1],[5,3,6]]),
([w31,w0,w1,w152,w3,w30],[69,99,90,62,76,10,95,81,20,30,32],[],[[0],[1],[2,0,3],[4,0,3],[2,5],[4,6],[2,3],[4,3],[2,6,7],[7,2],[6,3],[7,2],[8,2,4],[3,9,10],[3,2,4]]),
([w31,w0,w1,w153,w3,w30],[98,110,90,62,46,61,94,81,26],[14],[[0],[1],[2,3],[0,3],[2,0,4],[5,6],[2,3],[3,6],[2,4],[7,2],[3,5],[6,2],[4,2,8],[3,5,4],[3,2,100]]),
([w110,w34,w1,w2,w3,w30],[44,14,15,76,102,46,90,8,69,77,87],[17],[[0,1],[2,1],[0,1],[3,4,5],[6,4,5],[1,7,100],[1],[3,8,9],[5,9],[1,3,6],[9,5],[9,3,5],[5,3],[5,8],[10,3]]),
([w155,w34,w0,w1,w2,w30],[76,22,26,259,67,61,46,87,53,81,77,90],[2,53],[[0,1,2],[0,1],[3,4,5],[6,0],[7,0],[8],[0,100],[9],[5,10],[0,7],[101,11,3],[5,3,6],[3,0],[7,0],[6,5]]),
([w157,w34,w0,w1,w2,w3],[90,30,34,87,76,46,94,81,77,259],[2,53],[[0,1,2],[0,1],[3,0,4],[5,1,2],[3,0,4],[6],[3,100],[7],[3,8],[4,3],[101,0,9],[4,3],[3,0,4],[8,5],[3,0,4]]),
([w56,w34,w0,w40,w3,w30],[149,6,77,46,99,277,154,90,259,93,86,87],[],[[0],[1,0],[0,1],[2,1,3],[2,3],[4],[5,6],[3,2],[3,2],[7,5],[8,2,9],[7,2],[2,7,10],[2,9,10],[11,7,9]]),
([w208,w0,w1,w2,w3,w30],[6,0,53,46,77,90,94,91,82,259,278,99,84,59],[],[[0,1],[2],[1,0],[3],[4,5],[6,7,8],[5,6,7],[8,4,6],[5,4],[9,5,10],[4,11,7],[4,5],[7,4,5],[7,4,12],[13,5]]),
([w0,w209,w1,w2,w3,w30],[6,0,94,91,82,259,99,24,77,46,90,59],[],[[0,1],[2,3,4],[5,2],[4,2],[4,5],[3,0,6],[3,0,7],[8],[9,2],[5,4,6],[3,6],[2,5,3],[3,10],[3,2,9],[11,2]]),
([w210,w0,w1,w2,w3,w30],[6,0,259,77,93,46,94,91,82,95,87,279,100],[],[[0,1],[2],[1,0],[3,0,4],[5],[6,7,8],[4,6,7],[4,3],[8,3,9],[10,4,11],[3,4],[3,12,7],[7,3,10],[7,3,4],[10,4]]),
([w0,w211,w1,w2,w3,w30],[83,0,280,95,91,82,90,46,93,73,100,32,94,87],[],[[0,1,2],[3,4,5],[6,3,4],[5,7,8],[5,3],[4,9,10],[4,0,11],[7,0,3],[12],[13,5,10],[3,7],[4,6,10],[4,3,6],[4,8],[13,3]]),
([w56,w0,w40,w2,w3,w30],[6,14,259,87,15,277,99,86,154,46,100],[17],[[0,1],[1,0],[1,0],[2,0],[3,2],[2,4,100],[2,5,6],[2,3,6],[7,2,5],[8],[3,6,7],[9,7],[3,7],[9,6],[3,6,10]]),
([w56,w0,w1,w46,w3,w30],[6,20,268,91,46,7,94,281,105,93,79,90,84,99,282],[23],[[0,1],[2],[1,0],[3,0],[3,4,5],[6,7,8],[9,6,7],[10,4,6],[11,4],[12,8],[100,4,13],[6,4],[14],[4,6],[10,6]]),
([w48,w56,w0,w1,w3,w30],[7,93,84,281,99,26,126,283,91,94,164,106,86,95,79],[],[[0,1,2],[1,2],[2,1],[3],[4,1],[0,5],[6],[7,4,8],[8,0],[9,10,11],[12,4,10],[12,10],[13,4,11],[9,11],[14,4]]),
([w56,w0,w1,w83,w3,w30],[6,28,269,93,15,91,46,7,95,284,79,78,84,100,285],[23],[[0,1],[2],[1,3,4],[5,0],[5,6,7],[8,9,10],[3,4],[3,6],[11,6,8],[12,3],[8,3],[100,6,13],[6,8],[14],[10,3,11]]),
([w86,w56,w0,w1,w3,w30],[91,93,84,100,90,284,128,95,167,108,86,94,78],[],[[0,1,2],[1,2],[2,1],[3,4],[5],[3,0],[6],[0,1,2],[0,3],[7,8,9],[1,2],[10,3,8],[2,1],[11,3,9],[12,1]]),
([w58,w99,w0,w1,w2,w30],[0,93,20,91,61,140,78,6,101,286,87,46,259],[],[[0],[1,2],[3,1,4],[2,5,3],[6,1],[7],[3,8],[9],[4,8],[4,3],[1,3],[4,8],[10,1,4],[3,11,12],[3,1]]),
([w212,w0,w1,w2,w3,w30],[95,0,78,91,84,56,93,94,46],[],[[0,1,2],[3],[4,5,6],[0,2],[7,8],[0,2],[2,0],[6,4],[2,0],[4,6],[0,2],[7,8],[2,0],[8,4,7],[2,0]]),
([w64,w99,w0,w1,w3,w30],[0,93,20,87,61,140,46,6,101,287,91,259],[],[[0],[1,2],[3,1,4],[2,5,3],[6,1,4],[7],[3,8],[9],[4,8],[4,3],[1,3],[4,6],[10,1,4],[3,6,11],[3,1]]),
([w213,w0,w1,w2,w3,w30],[280,91,1,111,103,261,61,93,83,46,87,80],[],[[0],[1,2],[3],[4],[5],[6,1],[7,1],[7,8,9],[6,9],[10,6],[1,6],[1,9,11],[1,11,9],[1,6,7],[10,6,7]]),
([w214,w0,w1,w2,w3,w30],[6,0,87,1,259,91,93,46,76,78,261],[],[[0,1],[2,3,4],[5,0,6],[2,0,6],[7],[8,2],[4,5,6],[4,2,6],[9,4],[2,6,8],[4,6,10],[2,4],[2,8],[5,6],[2,6]]),
([w99,w0,w40,w1,w3,w30],[6,93,1,84,162,46,20,268,78,259,91,87],[28],[[0],[1,2,3],[3,2],[4],[5,3,100],[1,6],[7,8],[1,0,5],[8,5,9],[0],[5,0,10],[5,1,10],[9,0],[11,5,9],[8,0,1]]),
([w99,w0,w43,w1,w2,w30],[6,46,1,84,196,251,93,271,78,259,91],[42],[[0],[1,2,3],[3,2],[4],[1,3,100],[5,1,6],[5,7],[6,0,7],[8,1,9],[0],[1,0],[8,6],[9,0],[10,1,9],[1,0]]),
([w58,w34,w0,w1,w46,w30],[140,6,91,78,61,7,101,259,46],[],[[0],[1],[2,3,4],[0,1],[3,4,5],[1],[4,6],[2,1],[2,6,4],[4,2],[3,1],[3,6,4],[2,1],[2,7],[8,1]]),
([w215,w0,w1,w2,w3,w30],[53,69,99,14,44,78,61,7,79,95,82,84,94,90],[22],[[0,1],[2],[3,0,4],[5,0],[6,7,8],[0,8,9],[8,0],[8,0],[6,9,10],[11,0,10],[9,0,100],[12,8],[10,9,13],[8,0],[8,0]]),
([w216,w0,w1,w2,w3,w30],[78,0,6,91,1,96,80,83,259,261,103],[],[[0,1,2],[3,4,5],[1,2],[6],[7],[5,0,3],[0,3,5],[8,9],[0,8],[8,9],[3,0,5],[3,5],[0,5,3],[3,5],[0,9,10]]),
([w217,w0,w1,w2,w3,w30],[7,0,91,259,32,80,103,261,61,83,78,96],[],[[0,1],[2,3],[2,0,4],[5,6],[7],[8,2],[3,2,6],[3,9],[8,3,10],[3,6],[2,8],[2,3],[2,6,10],[2,8,11],[10,6]]),
([w58,w0,w40,w1,w3,w30],[7,14,96,26,259,1,84,125,79,90,126,6,91,77],[],[[0,1],[1,2,3],[4,5,6],[7],[8,0,9],[2,3],[8,10],[4,10,11],[9,4,10],[11],[12,2],[8,2,12],[4,11],[13,4,8],[8,9]]),
([w45,w58,w0,w1,w2,w30],[1,84,259,26,288,91,103,90,63,122,79,208,6],[30,27,42,22],[[0,1],[2,3,100],[4],[5,6,101],[7,6,102],[2,8,9],[2,0,103],[1,7,5],[10,7],[5,10],[2,5,7],[7,2,11],[2,7,12],[5,2],[5,12,10]]),
([w58,w0,w1,w2,w87,w30],[7,36,259,37,96,103,80,289,78,290,102,91,291],[],[[0,1],[2,3,4],[1,0],[5,6],[7,0,8],[4,8,9],[2,5],[2,9,10],[8,2],[2,5],[2,4],[11,2],[11,4],[11,4],[12]]),
([w101,w100,w0,w1,w2,w3],[0,7,91,259,28,78,83,79,104,292,96,93],[],[[0],[1],[2,3],[2,1,4],[5,6,7],[1],[2,8],[9],[5,8],[10,2],[3,1],[3,8,11],[3,1],[2,5,10],[2,1,5]]),
([w218,w0,w1,w2,w3,w30],[7,0,259,84,90,6,78,77,95,79,93],[],[[0,1],[2],[3,0,4],[3,5,6],[7,0,4],[8,6],[4,3],[9,3,10],[4,7],[3,4],[3,6],[7,4],[6,4,7],[9,3,7],[6,3]]),
([w107,w100,w0,w1,w3,w30],[0,259,28,93,61,91,90,7,104,293,294,78],[],[[0],[1,2,3],[1,3,4],[5,6],[2,3],[7],[1,8],[3,8],[9],[4,5],[1,8,3],[4,1,10],[1,3,4],[5,1],[11,3]]),
([w219,w0,w1,w2,w3,w30],[259,0,83,61,91,90,78,261,82,79],[],[[0,1,2],[0,3],[4,2,5],[6],[7,2],[3,4],[0,2],[0,2],[2,0,8],[0,2],[0,2],[4,0],[4,5],[4,2,9],[9,2]]),
([w100,w0,w40,w1,w3,w30],[7,91,1,84,78,6,157,90,269,259,93,87],[27],[[0],[1,2,3],[3,2],[4,5,100],[6],[4,1,7],[4,8],[9,3,10],[4,0],[0],[1,7],[1,0],[3,4],[11,0],[4,0]]),
([w100,w0,w81,w1,w2,w3],[7,90,1,77,233,78,92,28,274,93,295,87],[42],[[0],[1,2,3],[3,2],[4],[5,6,100],[1,7],[5,8],[1,0,5],[9,3],[0],[10,0,9],[3,1,9],[11,0],[3,5],[5,0]]),
([w101,w34,w0,w1,w83,w3],[142,78,6,87,107,259,93,261,82,104,34,96],[],[[0],[1,0,2],[3,4,5],[0,2],[1,2,6],[7],[3,8,9],[6,10],[1,9],[11,1,3],[1,10,6],[5,3,6],[3,6,9],[5,1,11],[1,9]]),
([w220,w0,w1,w2,w3,w30],[53,0,78,87,14,44,93,90,19,96,95,77,259,51,82],[29],[[0,1,2],[3],[4,0,5],[6,0,2],[7,8],[9,2,10],[2,10],[6,11],[2,10],[12,6,13],[10,2],[11,9,100],[2,9,10],[14,6],[2,6]]),
([w221,w0,w1,w2,w3,w30],[6,0,96,1,101,24,78,83,261,259,82,91,79],[],[[0,1],[2,3,4],[2,0,5],[6],[7,4],[2,4],[2,8,9],[9,8],[10,4,9],[9,4],[9,2],[11,2],[10,2],[10,2],[12,4]]),
([w101,w0,w40,w1,w3,w30],[78,14,6,96,34,87,259,93,127,167,82,77],[],[[0,1,2],[1,3,4],[5,6],[0,2,7],[8],[0,4,3],[0,5],[6,5,7],[0,6],[9],[0,3,10],[10,3],[6,0,11],[5,6],[0,7]]),
([w222,w101,w0,w1,w2,w3],[77,79,296,82,78,261,71,124,87,244,93,7],[31,28,42,29],[[0,1],[1,0,100],[2],[3,0,101],[4,5,102],[3,6,7],[8,1,103],[1,7],[0,7,1],[1,8],[1,9,10],[1,0,10],[8,3,11],[0,4],[3,0,4]]),
([w101,w0,w1,w2,w87,w3],[78,36,6,87,96,261,83,79,34,102,259,82,297],[],[[0,1,2],[3,4],[1,2],[5,6],[0,2,7],[4,0,3],[0,5],[0,8,9],[7,3,5],[3,5],[3,4],[10,0,4],[11,4],[0,4,11],[12]]),
([w110,w34,w40,w1,w3,w30],[78,14,6,79,259,96,8,84,77,69,86],[],[[0,1],[1],[2,0],[3,2],[0,4],[1,5],[1,6,7],[0,8],[3,7,8],[9],[0,5,10],[3,5,10],[4,0,7],[8,3],[0,7]]),
([w34,w0,w111,w1,w3,w30],[6,96,0,266,21,84,195,77,79,78,259,298],[40],[[0],[1,2],[3,4,5],[6,0,7],[8,5,7],[1,2],[3,8],[8,0],[9,3,10],[0],[11],[7,1,100],[5,0,9],[7,8],[8,0]]),
([w112,w34,w0,w1,w3,w30],[1,22,26,5,96,259,6,78,79,81,27,82,85,91,86],[],[[0,1,2,3],[4,1],[5,3,6],[7],[8,4,9],[6],[5,10,9],[11,6],[8,12,11],[8,13],[5,6],[14,5,9],[5,6],[9,5,8],[8,6]]),
([w34,w0,w113,w1,w3,w30],[165,96,0,267,84,78,85,82,79,93,259,7,299,275],[39],[[0],[1,2],[3,0,4],[5,6,7],[7,4],[1,2],[3,5],[8,3,9],[5,3,10],[11],[4,1,100],[12],[4,5],[13,8,10],[5,4]]),
([w114,w34,w0,w1,w3,w30],[1,30,34,5,78,259,7,96,84,107,35,85,82,91,93],[],[[0,1,2,3],[4,1,5],[6],[4,7,8],[9],[6],[5,10,8],[4,11,12],[12,6],[4,13],[5,8,14],[4,5],[5,4,8],[13,5],[4,6]]),
([w0,w1,w223,w2,w3,w30],[79,101,0,7,300,90,44,259,77,1],[],[[0,1],[0,2,3],[0,4],[0,4],[5,1],[4,6],[7,1],[7,1],[8,0],[2,3],[9,4],[0,1],[5,8],[0,1],[0,1]]),
([w224,w0,w1,w2,w3,w30],[53,56,44,91,1,79,7,77,96,87,69,78,259],[],[[0],[0,1,2],[3],[4,0],[5,6,7],[8,5,9],[5,10],[5,7,10],[11,7,12],[9,10],[7,8,11],[7,5],[9,7],[5,7],[5,10]]),
([w34,w0,w43,w1,w46,w30],[160,195,78,82,259,16,196,77,79,131,6,7],[23,16],[[0],[1,2,3],[4,0,100],[3,5,6],[3,7,8],[4,1,101],[2,9],[2,5,10],[2,4],[10],[1,10,2],[2,11],[4,10],[7,4,8],[8,10]]),
([w0,w1,w225,w2,w3,w30],[301,78,87,93,77,0,1],[],[[0,1,2],[0,1],[1,0],[3,2],[1,0],[0,2],[2,0],[4,1],[2,0],[5,0],[1,3],[6,0],[1,0],[3,4],[1,0]]),
([w226,w0,w1,w2,w3,w30],[51,56,44,91,78,77,1,96,87,55,259,93,79],[],[[0],[0,1,2],[3],[4,5],[6,0],[7,4,8],[4,9],[10,5,11],[4,5,9],[8,9],[5,4],[5,7,8],[4,5],[12,5],[4,9]]),
([w34,w0,w81,w1,w83,w3],[7,295,79,91,87,29,77,78,93],[23,37],[[0],[1,2,3],[4,5,100],[3,0],[3,6,4],[7,1,101],[2,3],[2,0],[2,4,8],[0],[1,0,2],[2,8,4],[3,0],[3,7,6],[4,0]]),
([w34,w0,w1,w125,w3,w30],[7,87,82,0,93,6,96,79,78,259],[23,32],[[0],[1,2,100],[2,3,4],[1,5,2],[2,0],[6,1],[4,3],[7,1,5],[8,0],[1,4,101],[9,5],[1,0],[0],[5],[1,0]]),
([w34,w0,w78,w1,w3,w30],[163,14,84,82,6,93,298,79,90,7,77],[19],[[0],[1,0,2],[2,0],[3,4],[3,2],[5,1],[6,100],[7,2,4],[8,9,10],[4],[2,4,6],[10,5,7],[2,4,6],[10,6],[7,2,4]]),
([w34,w0,w1,w133,w3],[7,259,82,101,28,81,78,6,302,90,77,46],[8,12,23,1,15,2],[[0],[1,100,2,3,101,102],[0,4,3,5],[2,6,101,7,8],[8,103,6],[0,8,9],[1,8,104,7],[0,5,100,9],[1,10,105,3,6,7],[7,0,11]]),
([w34,w0,w141,w1,w3,w30],[7,14,82,81,93,78,6,77,299],[21],[[0],[1,2,3],[3,2],[2,3],[2,0],[4,1],[5,100],[4,6,7],[5,0],[0],[7,5],[3,0,8],[7,4],[3,0,8],[5,0]]),
([w34,w0,w1,w143,w30],[6,259,82,101,20,77,84,79,7,96,93,86,46],[8,12,23,1,3,2],[[0],[1,100,2,3,101,102],[0,4,5,6],[2,7,101,8,3],[9,103,7,3,100],[0,9,10,4],[8,11,104,3],[0,5,105,10],[8,5,100,7],[8,0,12]]),
([w116,w37,w1,w2,w3,w30],[63,16,17,79,6,82,80,11,69,81,303],[19],[[0,1],[2,1],[3,4],[0,1],[5,6],[1,7,100],[5,8,9],[1],[3,9],[9,5],[1,8,10],[9,3],[5,9],[3,8],[3,8]]),
([w169,w37,w0,w1,w3,w30],[1,22,24,9,79,93,81,82,53,179,96,86],[8],[[0,1,2,3],[4,1,5],[6,3],[7,1,2],[4,5,7],[8],[9,100,10],[9],[4,6],[10,4,9],[9,5],[7,6,11],[9,5,10],[6,4],[4,5,6]]),
([w171,w37,w0,w1,w2,w3],[79,38,42,82,86,81,65,192,96],[8],[[0,1,2],[3,1,4],[5,0],[0,4],[0,1,2],[6],[7,100,8],[3,5],[7],[8,0,7],[0,5,8],[7,4],[5,3],[7,4,8],[3,4,5]]),
([w62,w37,w0,w43,w2,w30],[182,6,81,82,79,99,304,188,86,93,90],[],[[0],[1,0],[0,1],[2,1,3],[2,4],[5],[6,7],[3,2],[4,2],[3,6,8],[4,2,9],[3,2,8],[2,8,10],[2,9,10],[3,8,4]]),
([w227,w0,w1,w2,w3,w30],[6,0,53,82,79,86,95,99,81,259,78],[],[[0,1],[2],[3],[1,0],[4,5],[6,4],[4,6],[4,7],[5,6,8],[8,7,9],[6,5],[8,4],[10,5],[4,5],[4,6,7]]),
([w0,w228,w1,w2,w3,w30],[82,0,6,95,79,99,53,81,20,10,77,259,78],[],[[0,1,2],[3,0],[4,3],[0,5],[0,3],[6,5],[7],[8,2,3],[4,9,10],[11,0,5],[3,5,11],[10,4],[0,3,12],[0,5,4],[4,3,5]]),
([w229,w0,w1,w2,w3,w30],[6,0,259,81,93,79,95,82,110,87],[],[[0,1],[2],[3,0,4],[1,0],[5],[6,7],[4,3],[4,8,7],[7,3,6],[3,4],[6,4],[3,8,9],[7,3],[7,4],[9,3,4]]),
([w0,w230,w1,w2,w3,w30],[83,0,280,95,82,79,110,65,84,36,81,93,87],[],[[0,1,2],[3,4],[5,3],[4,6],[4,3],[7,6],[4,0,8],[9,0,3],[10],[8,4],[3,6,11],[12,5,6],[4,3,6],[4,6],[5,3,12]]),
([w62,w0,w43,w2,w3,w30],[10,16,81,6,82,79,17,99,110,90,188],[19],[[0,1],[1,0],[2,3,4],[1,0],[2,0,5],[4,6,100],[5,2,7],[4,7],[4,2,8],[2,7,9],[10],[2,8,9],[4,2],[4,7,5],[5,2]]),
([w62,w0,w1,w46,w2,w30],[6,20,271,87,10,95,305,79,99,82,93,77,306],[22],[[0,1],[2],[1,0],[3,0],[3,4],[5,6,7],[7,6,8],[7,5],[9,5],[5,8,10],[100,8],[11,7],[12],[7,5,8],[7,8]]),
([w47,w62,w0,w1,w2,w30],[6,93,95,17,305,79,132,307,87,10,90,197,81,110,99],[],[[0,1,2],[1,3],[2,1],[4],[5,1],[0,5,2],[6],[7,0,8],[8,5,9],[2,5],[5,2],[10,2,11],[12,10],[12,5],[5,13,14]]),
([w62,w0,w1,w2,w87,w30],[10,36,273,87,93,6,95,308,79,82,84,110,309],[22],[[0,1],[2],[3,4,5],[1,0],[3,0],[6,7,8],[4,6,7],[4,7],[9,6],[10,4],[6,4],[100,8,11],[9,6,11],[8,4,9],[12]]),
([w90,w62,w0,w1,w2,w30],[10,93,95,17,110,308,42,134,84,310,87,201,82,81,90],[],[[0,1,2],[1,3],[2,1],[4,2],[5],[0,6],[7],[8,1],[9,0,10],[2,11,12],[1,2,8],[12,2],[8,1],[13,4,14],[12,1]]),
([w64,w37,w0,w1,w46,w30],[140,10,87,82,61,111,78,101,24,287,93,79,81],[],[[0],[1,0],[2,3,4],[0,1],[3,1],[5],[4,6,7],[2,8,9],[2,7,4],[4,2],[3,8,10],[3,7,4],[2,4],[2,11,12],[11,4]]),
([w231,w0,w1,w2,w3,w30],[65,0,98,87,93,15,16,63,81,79,95,84,53,78],[23],[[0,1,2],[3],[4,5],[6,0,7],[8,0,9],[10,9],[9,8,10],[9,11,12],[13,8,10],[8,12,100],[10,12,13],[8,9],[13,8,10],[9,11,12],[9,8]]),
([w232,w0,w1,w2,w3,w30],[79,0,10,87,1,76,93,83,261,78,111,259],[],[[0,1,2],[3,4,5],[6],[1,2],[7],[5,0,3],[0,8],[0,3,5],[9,10],[3,5],[11,8],[3,0,5],[3,5],[0,8],[0,5,3]]),
([w0,w233,w1,w2,w3,w30],[10,0,76,78,87,83,111,259,102,40,79,82],[],[[0,1],[2,3,4],[3,5],[2,4],[3,6],[2,7],[8,6],[2,0,9],[10],[4,2],[7,3,5],[4,2],[3,2],[11,5,6],[3,2]]),
([w42,w64,w0,w1,w3,w30],[82,81,311,78,79,111,44,129,259,173,6],[33,27,28,23],[[0,1],[0,1,100],[2],[3,1,101],[4,5,102],[3,6,7],[8,0,103],[0,7],[0,7],[0,9],[0,9,10],[0,1,8],[8,3,10],[1,4],[3,1,4]]),
([w64,w0,w43,w1,w2,w30],[79,16,10,76,24,259,1,84,131,86,132,6,78,81],[],[[0,1,2],[1,3,4],[5,6,7],[8],[0,2,9],[0,4,3],[0,10],[0,10,11],[9,5,10],[11],[12,3],[0,3,12],[5,11],[13,0],[0,9]]),
([w64,w0,w1,w83,w3,w30],[79,28,6,259,76,81,10,102,82,312,80,87],[],[[0,1,2],[3,4],[5,6,7],[1,2],[0,6,8],[4,0,9],[0,5,10],[0,2],[8,3],[3,4],[3,2],[11,0,3],[11,2,4],[2],[0,2]]),
([w104,w103,w0,w1,w2,w3],[0,10,87,259,79,83,112,82,313,76,93],[],[[0],[1],[2,3],[4,5],[2,1,4],[1],[2,6],[7,6],[8],[9,2],[3,6,10],[3,1],[2,7,9],[3,1],[2,1,7]]),
([w234,w0,w1,w2,w3,w30],[10,0,65,81,82,84,93,79,95],[],[[0,1],[2],[3,4],[5,0,6],[3,0,7],[8,4],[6,3],[4,5,6],[4,3,8],[3,4],[5,6],[3,7],[4,3],[4,5],[7,3]]),
([w235,w0,w1,w2,w3,w30],[79,0,10,259,76,102,84,83,87,78],[],[[0,1,2],[3,4],[5],[6,2,4],[0,2,7],[4,0,8],[0,7],[0,7],[7,3,9],[3,4],[3,7],[8,0,3],[8,4],[0,7],[0,4,7]]),
([w108,w103,w0,w1,w2,w30],[0,10,259,78,61,76,112,82,314,93,87],[],[[0],[1],[2,3,4],[3,5],[3,1],[1],[2,6],[7,6],[8],[4,3,6],[2,6,9],[3,1],[2,4],[10,1],[7,1]]),
([w103,w0,w43,w1,w2,w30],[10,78,1,84,82,6,199,36,76,273,93,91],[27],[[0],[1,2,3],[3,2],[4,5,100],[6],[4,7,8],[1,9],[1,3,10],[1,0],[0],[1,8],[1,0],[3,4],[11,0],[4,0]]),
([w103,w0,w81,w1,w2,w3],[10,79,1,81,82,92,237,36,61,276,93,91],[28],[[0],[1,2,3],[3,2],[4,5,100],[6],[4,7,8],[1,9],[1,3,10],[1,0],[0],[1,8],[1,0],[3,4],[11,0],[4,0]]),
([w104,w37,w0,w1,w2,w87],[144,82,10,91,79,76,93,78,112,81],[],[[0],[1,0,2],[3,4,5],[1,6],[0,2],[2],[3,7,8],[1,8],[5,2,7],[5,1,3],[4,3,6],[1,2],[9,1],[3,2],[1,2]]),
([w236,w0,w1,w2,w3,w30],[65,82,110,93,63,79,95,78,81],[29],[[0,1],[2],[3,1],[3,0,4],[5,0],[0,1,6],[3,6,7],[1,0],[1,0],[8,1],[6,0,3],[8,0,100],[1,0],[1,0],[7,3]]),
([w237,w0,w1,w2,w3,w30],[78,0,315,76,1,101,82,26,79,261,102,87,259],[],[[0,1,2],[3,4,5],[6],[0,2,7],[8,2,5],[3,0,5],[0,9],[3,9,8],[0,5,10],[11,3],[12,0,5],[11,3],[0,3],[8,5],[0,3]]),
([w104,w0,w43,w1,w2,w30],[82,16,10,76,42,91,259,6,93,133,78,81],[],[[0,1,2],[1,3,4],[5,6],[0,7,8],[9],[0,4,3],[0,5],[6,5,8],[0,2],[2],[0,3,10],[10,2],[6,0,11],[5,2],[0,2]]),
([w222,w104,w0,w1,w2,w3],[81,79,316,82,261,78,71,124,91,93,248,10],[31,28,42,29],[[0,1],[1,0,100],[2],[3,4,101],[5,0,102],[3,6,7],[8,1,103],[0,7,1],[1,7],[1,8],[1,0,9],[1,10,9],[0,3],[8,5,11],[3,0]]),
([w104,w0,w1,w83,w2,w3],[82,28,6,91,79,76,42,80,317,259,261,318,78],[],[[0,1,2],[3,4,5],[4,2],[0,2,4],[1,2],[5,0,3],[0,6,7],[4,3,7],[0,8,5],[3,5],[9,0,5],[3,10],[11],[12,5],[0,5,12]]),
([w0,w1,w238,w2,w3,w30],[300,79,101,86,63,146,259,81,1],[],[[0,1,2],[0,1],[1,0],[1,0],[3,2],[0,4],[5,0,6],[6,0],[7,1],[8,0],[4,0],[1,2],[3,7],[1,0],[1,0]]),
([w239,w0,w1,w2,w3,w30],[53,67,63,82,81,87,79,76,91,69,259],[],[[0],[0,1,2],[3,0,4],[5],[6,4],[7,3,8],[6,4,9],[3,9],[3,4,10],[4,3],[8,9],[4,6],[3,4],[3,9,6],[6,4]]),
([w37,w0,w111,w1,w2,w30],[6,76,0,272,21,95,195,81,79,82,259,319],[43],[[0],[1,2],[3,4,5],[6,0,7],[8,5,7],[1,2],[3,8],[8,0],[9,3,10],[0],[11],[7,1,100],[7,0,9],[7,8],[8,0]]),
([w37,w0,w40,w1,w46,w30],[6,195,82,87,259,21,81,79,86],[22,18],[[0],[1,2,3],[4,5,100],[3,0],[3,6,7],[4,1,101],[2,3],[2,0],[2,4],[0],[1,0,2],[2,8,6],[3,0],[3,4],[7,0]]),
([w116,w37,w43,w1,w2,w30],[82,16,6,79,259,11,95,81,69,86,90],[],[[0,1],[1],[2,0],[3,2],[0,4],[1,5],[1,5,6],[0,6,7],[3,6,7],[8],[0,9,10],[3,10],[4,0,7],[7,3],[0,9,3]]),
([w117,w37,w0,w1,w2,w30],[1,22,24,9,86,6,82,79,76,77,25,87,95],[],[[0,1,2,3],[4,1],[5],[6],[7,8,9],[5],[9,10],[11,5],[4,12,11],[7,11],[7,5],[4,9],[11,5],[9,4],[7,4]]),
([w37,w0,w118,w1,w2,w30],[92,95,0,86,37,82,87,79,81,93,259,10,320],[39],[[0],[1,2,3],[1,4],[5,1,6],[6,1],[3,2],[5,6],[7,8,9],[5,8,10],[11],[5,3,100],[12],[6,5,8],[6,7,8],[5,9]]),
([w119,w37,w0,w1,w2,w30],[1,38,42,9,82,259,87,86,84,115,200,95,93],[],[[0,1,2,3],[4,1,5],[6,3,5],[4,7,8],[9],[10],[5,10,8],[4,11,6],[6,8],[4,6],[5,8,12],[4,5],[5,4,8],[6,5],[4,8]]),
([w0,w1,w240,w2,w3,w30],[82,91,0,10,93,321,81,1],[],[[0,1],[0,2,3],[4,1],[0,5],[0,5],[1,5],[6,0],[1,4,5],[1,5],[0,4],[2,3],[7,3],[0,5],[0,4],[4,6]]),
([w241,w0,w1,w2,w3,w30],[65,67,63,82,81,87,1,76,91,93,98,79],[],[[0],[0,1,2],[3,4],[5],[6,0],[7,3,8],[9,4],[3,10],[3,4,10],[4,3],[8,9,10],[4,7,8],[3,4],[3,9],[11,4]]),
([w37,w0,w81,w1,w2,w87],[10,322,79,87,91,37,81,82,93],[22,37],[[0],[1,2,3],[4,5,100],[3,6,4],[3,0],[7,1,101],[2,3],[2,4,8],[2,0],[0],[2,8,4],[1,0,2],[3,7,6],[3,0],[4,0]]),
([w37,w0,w1,w125,w2,w30],[10,91,78,0,93,6,76,79,82,87],[22,34],[[0],[1,2,100],[2,3,4],[1,5,2],[2,0],[6,1],[4,3],[7,1,5],[8,0],[1,4,101],[9,5],[1,0],[0],[5],[1,0]]),
([w37,w0,w76,w1,w2,w30],[10,16,25,95,78,93,319,79,81,6,86],[17],[[0],[1,2,3],[3,2],[4,3],[4,0],[5,1],[6,100],[7,8,9],[10,0,8],[0],[8,5,6],[8,0,7],[8,6],[8,0,6],[7,0,9]]),
([w37,w0,w1,w2,w130],[10,91,78,101,6,323,36,77,79,86,81,82,59],[2,13,22,1,15,8],[[0],[1,100,2,3,101,102],[2,1,101,4,5],[0,6,3,7],[5,103,8],[4,5,104],[0,5,9],[4,10,105,11],[0,7,100,8],[0,4,12]]),
([w37,w0,w151,w1,w2,w30],[10,16,43,77,93,81,78,320,82],[21],[[0],[1,2,3],[3,2],[4,3,5],[6,0],[4,1],[7,100],[4,5],[8,0],[0],[5,8],[3,0,7],[5,4],[3,0,7],[8,0]]),
([w37,w0,w1,w153,w30],[10,91,78,101,20,6,81,84,79,76,93,90,59],[2,13,22,1,5,8],[[0],[1,100,2,3,101,102],[2,1,4,5,6,7],[0,8,101,3],[9,103,8,1,100],[5,9,10,1,4],[0,11,104,3],[5,6,105,10],[0,6,100,8],[0,5,12]]),
([w121,w79,w1,w2,w3,w30],[71,18,19,93,83,78,82,13,84,324,98],[21],[[0,1],[2,1],[3,4,5],[3,4,6],[0,1],[1,7,100],[3,8],[3,8],[1],[8,3],[8,3],[1,9,10],[5,10,6],[6,3],[5,3]]),
([w181,w79,w0,w1,w3,w30],[93,30,32,84,78,10,82,95,224,76,90],[20],[[0,1,2],[0,1],[3,0],[4,5,6],[6,0],[7],[8,100,9],[0,3],[8],[9,4,8],[0,3],[8,10],[3,0],[8,9,10],[4,0]]),
([w183,w79,w0,w1,w2,w30],[93,38,40,84,82,90,78,65,214,76],[20],[[0,1,2],[0,1],[3,0],[4,5],[6,0],[7],[8,100,9],[0,3],[8],[9,4,8],[0,3],[8,5],[3,0],[8,5,9],[4,0]]),
([w106,w79,w0,w81,w2,w3],[216,10,84,82,78,110,222,221,90,93],[],[[0],[1,0],[0,1],[2,3],[2,1,4],[5],[6,7],[3,2],[4,2],[3,6,8],[4,2,8],[3,2,9],[2,9],[2,8,9],[3,8]]),
([w242,w0,w1,w2,w3,w30],[10,0,76,93,78,86,95,84,100,87,79],[],[[0,1],[2],[3],[4,0,5],[1,0],[6,4],[4,6],[5,7],[4,6],[7,8,9],[6,4],[9,5,8],[4,5],[10,5],[4,6]]),
([w0,w243,w1,w2,w3,w30],[78,0,315,95,93,87,56,100,84,28,34,79,82],[],[[0,1,2],[3,0],[0,3],[4,5],[0,3],[5,6,7],[8],[0,2,3],[9,2,10],[5,4,7],[3,0],[5,7],[0,3],[11,4,12],[0,3]]),
([w244,w0,w1,w2,w3,w30],[10,0,65,84,7,90,93,95,82,110,91,79],[],[[0,1],[2],[3,4,5],[6],[1,0],[7,8],[5,3],[8,3,9],[5,7,8],[3,5],[3,9,10],[10,5,9],[8,5],[8,3],[11,3,5]]),
([w0,w245,w1,w2,w3,w30],[10,0,94,82,93,79,110,65,7,81,84,91],[],[[0,1],[2,3],[4,2,5],[3,2],[3,6],[7,6],[3,8,9],[10],[5,0,2],[9,3],[11,4,6],[2,5],[3,6],[3,2,4],[5,2]]),
([w106,w0,w81,w2,w3,w30],[10,18,84,93,82,19,222,110,221,78],[21],[[0,1],[1,0],[2,3],[2,0,3],[1,0],[4,5,100],[3,2],[3,2],[4,6,7],[2,3],[2,3],[8],[4,7],[4,2],[9,2]]),
([w106,w0,w1,w83,w2,w3],[10,28,274,7,79,95,325,82,78,94,100,90,326],[29],[[0,1],[2],[1,3],[4,3],[4,0],[5,6,7],[7,5],[8,5],[7,6,9],[9,10,11],[100,7,10],[5,8],[12],[8,5],[7,5,8]]),
([w85,w106,w0,w1,w2,w3],[7,90,94,19,325,93,32,136,327,95,234,78,84],[],[[0,1,2],[1,3],[2,1],[4],[5,1],[0,6],[7],[8,0,5],[9,5],[2,10,11],[5,2,10],[5,2,10],[12,5],[9,5],[11,9]]),
([w106,w0,w1,w2,w87,w3],[7,36,276,79,90,19,78,10,94,82,81,110,328],[29],[[0,1],[2],[3,0],[1,4,5],[3,6,7],[8,6],[4,8,6],[4,5],[9,8],[10,4],[8,4],[100,6,11],[9,8,11],[6,4,9],[12]]),
([w89,w106,w0,w1,w2,w3],[10,90,94,19,110,329,40,138,81,330,93,238,82,84],[],[[0,1,2],[1,3],[2,1],[4,2],[5],[0,6],[7],[8,1],[9,0,10],[2,11,12],[1,2,8],[10,2,11],[8,1],[13,4,10],[12,1]]),
([w107,w79,w0,w1,w83,w3],[142,10,87,82,76,111,79,112,293,84,90,78],[],[[0],[1,0],[2,3,4],[0,1],[2,1,3],[5],[2,6,7],[6,7,8],[2,9],[4,2],[3,7,10],[3,2,4],[2,4],[9,7,11],[2,4]]),
([w246,w0,w1,w2,w3,w30],[65,0,98,87,82,15,84,78,18,71,94,79,81,51],[23],[[0,1,2],[3],[4,5],[6,0,7],[8,0,9],[10,7],[7,6,10],[11,6,10],[7,12,13],[6,13,100],[6,7],[10,11],[7,12,13],[11,6,10],[7,6]]),
([w247,w0,w1,w2,w3,w30],[10,0,87,1,61,102,80,79,84,103,111,78],[],[[0,1],[2,3,4],[5],[6],[1,0],[4,2],[7,8,9],[7,2,10],[4,9,11],[2,4],[8,4,11],[2,7,9],[2,9],[7,4],[2,4,7]]),
([w0,w248,w1,w2,w3,w30],[10,0,61,79,112,80,111,82,103,42,259,91],[],[[0,1],[2,3,4],[3,4,5],[3,6],[2,5,7],[2,4],[7,0,4],[8],[2,0,9],[10,2],[10,2],[11,3,4],[7,4],[3,2],[3,2]]),
([w42,w107,w0,w1,w3,w30],[84,82,331,78,111,79,44,129,87,93,177,7],[33,27,28,23],[[0,1],[1,0,100],[2],[3,4,101],[5,0,102],[3,6,7],[8,1,103],[0,7,1],[1,7],[1,8],[1,0,9],[1,10,11],[0,3],[8,5,11],[3,0]]),
([w107,w0,w81,w1,w2,w3],[10,18,61,32,87,1,94,135,86,79,136,7,84],[],[[0,1],[1,2,3],[4,5,6],[7],[4,0,8],[2,3],[4,9],[9,10,11],[8,4],[11],[9,2],[4,2,9],[4,11],[12,8],[4,8]]),
([w107,w0,w1,w46,w3,w30],[7,87,61,84,10,102,82,83,91,79],[],[[0],[1,2],[3,4,5],[1,4,6],[6,0],[2,1],[6,3,7],[6,1,7],[2,0,6],[1,2],[8,2],[1,0],[0],[9,0,2],[1,0]]),
([w108,w79,w0,w1,w2,w87],[144,10,91,61,7,87,79,112,78,90],[],[[0],[1],[2,3],[2,4,5],[0,1],[1],[2,6,7],[2,7],[3,1,6],[3,2],[8,2,9],[3,1,8],[5,3],[2,1],[2,1]]),
([w249,w0,w1,w2,w3,w30],[65,98,110,84,7,82,18,71,94,79],[22],[[0,1],[2],[3,4,5],[3,0],[6,0,7],[0,5,8],[9,3,8],[5,0],[5,0],[3,5],[3,0,100],[8,0,9],[5,0],[5,0],[9,3,8]]),
([w250,w0,w1,w2,w3,w30],[102,315,87,1,104,84,28,34,61,103,79,78,259],[],[[0,1],[2,3,4],[5],[2,0,4],[6,0,7],[8,2],[0,9,10],[10,0],[8,0,11],[2,4],[12,0],[2,0],[2,0,4],[10,0,8],[2,4]]),
([w45,w108,w0,w1,w2,w30],[84,87,79,211,82,103,63,122,259,78,210,90,91],[30,27,42,22],[[0,1],[2,0,100],[3],[4,5,101],[2,0,102],[2,6,7],[8,9,103],[0,7,9],[2,7,6],[2,10],[2,0,11],[4,8],[0,4],[12,2,8],[2,0,4]]),
([w108,w0,w81,w1,w2,w3],[79,18,7,90,91,1,94,137,40,138,10,61,84],[],[[0,1,2],[0,3],[4,5,6],[4,2,3],[7],[3,8],[0,4],[0,4,3],[0,9,10],[10],[0,11],[0,3],[12,3],[4,10],[4,3]]),
([w108,w0,w1,w46,w2,w30],[79,20,7,91,78,61,40,83,332,87,103,333],[],[[0,1,2],[3,4,5],[4,2],[3,2,4],[0,2,1],[5,0,3],[0,6,7],[0,3,7],[4,8,5],[3,5],[9,5],[3,0,10],[11],[0,5],[0,5]]),
([w0,w1,w251,w2,w3,w30],[301,78,87,86,84,1,0],[],[[0,1,2],[0,1],[1,0],[3,2],[1,0],[0,2],[2,0],[4,1],[2,0],[5,0],[1,3],[6,0],[1,0],[3,4],[1,0]]),
([w252,w0,w1,w2,w3,w30],[51,73,71,91,84,78,81,61,55,86,87],[],[[0],[0,1,2],[3,0,4],[5,4],[6],[7,3],[5,3,8],[9,4],[5,8],[4,7,10],[3,5,4],[3,8],[3,8,5],[3,4],[5,4]]),
([w79,w0,w113,w1,w2,w3],[7,86,0,275,29,81,295,84,117,78,334,61],[43],[[0],[1,2],[3,4,5],[6,0,7],[1,5,7],[1,2],[3,8],[9,0],[1,3],[0],[10],[7,11,100],[5,0,8],[7,1],[9,0]]),
([w79,w0,w40,w1,w83,w3],[230,295,91,79,87,14,157,84,78,7,86],[29,18],[[0],[1,2,3],[4,0,100],[3,5,6],[3,7,4],[8,1,101],[4,8],[8,5,9],[10,4],[9],[1,9,2],[2,10,4],[4,9],[7,8],[4,9]]),
([w0,w1,w253,w2,w3,w30],[91,82,0,7,90,84,321,1],[],[[0,1],[1,2,3],[4,0],[1,5,6],[1,6],[0,6],[5,1],[0,6],[0,4,6],[0,3,4],[7,5,6],[2,3],[0,4],[0,5],[4,5]]),
([w254,w0,w1,w2,w3,w30],[65,73,71,91,7,84,1,81,61,78,90,86,98],[],[[0],[0,1,2],[3,4,5],[6,0],[7],[8,3],[9,3,10],[11,5],[8,12,9],[5,8,10],[3,8],[3,10,12],[3,10],[3,5],[9,5]]),
([w79,w0,w118,w1,w2,w3],[89,86,0,270,37,81,90,84,322,119,82,10,335],[40],[[0],[1,2],[3,4,5],[6,7],[8,5,7],[1,2],[3,9],[6,3],[10,3,11],[11],[5,1,100],[12],[5,6],[7,9],[10,5]]),
([w79,w0,w43,w1,w2,w87],[336,322,78,79,91,84,199,82,90,198,10],[29,16],[[0],[1,2,3],[4,0,100],[3,5,4],[3,5,6],[7,1,101],[2,4],[2,4,8],[2,5,8],[9],[2,8,4],[1,8,5],[5,7],[4,8,5],[4,10]]),
([w121,w79,w81,w1,w2,w3],[1,18,7,90,84,82,10,13,81,78,55,86,93],[],[[0,1],[1],[2,1],[3,2,4],[5,4,6],[1,3],[1,7,8],[3,4],[9,4],[10],[4,11,12],[4,3,12],[4,3],[4,9],[5,3]]),
([w122,w79,w0,w1,w2,w3],[1,30,32,12,78,86,7,117,10,77,33,93,79,92,87],[],[[0,1,2,3],[4,1,5],[6],[7],[4,8,9],[6],[9,10],[11,6,12],[4,13,12],[4,14],[4,6],[5,9],[14,6],[9,4],[4,5]]),
([w123,w79,w0,w1,w2,w3],[1,38,40,12,86,7,93,81,119,337,92,79,120,91,10,82],[],[[0,1,2,3],[4,1],[5,3],[6,4,7],[8],[9],[7,9],[6,10,11],[6,7,11],[12,13],[6,7],[6,14,15],[7,6],[13,6,14],[13,7]]),
([w79,w0,w1,w125,w2,w3],[7,91,79,0,86,10,61,78,82,87],[29,35],[[0],[1,2,100],[2,3,4],[1,0,2],[2,5],[6,1],[4,3],[7,0],[8,5],[1,4,101],[9,0],[1,5],[5],[0],[1,0,5]]),
([w79,w0,w137,w1,w2,w3],[338,18,81,79,7,86,334,78,10,84],[17],[[0],[1,0,2],[2,0],[3,4],[3,2],[5,1],[6,100],[7,2,4],[5,8,9],[4],[2,4,6],[9,7],[2,4,6],[9,5],[7,2,4]]),
([w79,w0,w1,w2,w139],[7,87,79,112,82,36,10,84,77,61,93,86,62],[2,14,29,1,3,8],[[0],[1,100,2,3,101,102],[0,4,101,3],[2,1,5,6,7,8],[9,103,4,1,100],[0,10,104,3],[4,9,11,6,1,5],[0,7,105,4],[6,7,100,10],[4,0,12,3,6]]),
([w79,w0,w147,w1,w2,w3],[7,18,79,77,10,86,335,93,84,82],[19],[[0],[1,2,3],[3,2],[2,0],[2,4],[5,1],[6,100],[7,0,8],[7,3],[0],[8,0,7],[3,4,6],[8,0,6],[3,4,6],[9,0,4]]),
([w79,w0,w1,w149,w3],[10,61,79,112,28,7,81,93,339,82,90,84,62],[2,14,29,1,5,8],[[0],[1,100,2,3,101,102],[2,1,4,5,3,6],[0,7,101,8],[1,103,8,9],[5,1,10,3,4],[0,7,104,8],[5,6,105,7],[0,11,100,7],[0,5,12]]),
([w155,w0,w40,w1,w2,w30],[79,14,86,84,62,81,94,61,82,87],[5,54],[[0,1,2],[1,2],[3,2],[4,2,5],[0,3,5],[0,100],[6,0],[0,3,6],[2,5],[7],[8],[0,2],[101,3,9],[5,0],[0,2]]),
([w157,w0,w40,w1,w2,w3],[86,14,81,79,94,61,82,84,87],[5,54],[[0,1],[1,0],[2,0],[3,0],[3,2],[3,100],[4,3],[3,2,4],[0,4,3],[5],[6],[7,0],[101,2,8],[7,0],[8,0]]),
([w0,w1,w255,w2,w3,w30],[61,82,87,0,69,79,81,272,91,90,86],[],[[0,1,2],[1,3,4],[5,4],[1,2,4],[0,6],[2,0],[2,0],[7,0,8],[2,5,6],[1,3,9],[10],[5,0],[1,6],[1,0,5],[2,0,5]]),
([w0,w1,w256,w2,w3,w30],[76,82,87,0,55,93,84,86],[],[[0,1,2],[1,3,4],[5,4,6],[0,2],[1,4],[2,0],[2,0],[6,5],[2,0],[1,3,5],[2,0],[7],[1,0,2],[1,5],[2,0]]),
([w110,w0,w1,w46,w3,w30],[79,161,268,82,84,93,87,10,61,69,88,90,81,162],[18],[[0],[1,2],[3,4,5],[3,6,7],[3,7],[8,2],[5,2],[100,2,9],[8,2],[4,5],[10,8],[6,11,12],[13],[10,4,8],[6,8,10]]),
([w48,w110,w0,w1,w3,w30],[26,14,90,84,125,61,79,126,82,10,86,88,81],[],[[0,1,2],[2,1],[3,2],[4],[5,3],[6],[5,0,7],[8,9],[2,9,8],[5,7],[10,7],[2,7],[11,5],[12,2],[11,2]]),
([w110,w0,w1,w83,w3,w30],[79,166,269,82,340,315,76,90,55,267,84,93,87,157],[18],[[0],[1,2],[3,4,5],[3,4],[3,4],[6,2],[7,2],[6,2],[100,2,8],[9,6,7],[10,11],[12,6],[12,6],[13],[12,6]]),
([w86,w110,w0,w1,w3,w30],[34,14,90,61,84,87,127,51,82,10,93,128,55],[],[[0,1,2],[2,1],[3,2,4],[5,2],[6],[7],[3,0,5],[8,4,9],[3,7,8],[3,5],[10,4],[3,11],[4,3,10],[5,12],[5,3,4]]),
([w112,w0,w111,w1,w2,w30],[79,87,94,0,89,85,88,121,82,86,6,341],[],[[0,1,2],[3],[4,5,6],[1,4],[0,2],[0,7],[2,0],[0,2],[8,6,9],[10],[11],[0,7],[1,8,10],[1,0,2],[0,2]]),
([w257,w0,w1,w2,w3,w30],[79,61,0,6,93,84,10,88,87,86,81],[],[[0],[1,2,3],[4,2,5],[4,2,5],[1,6,7],[1,7],[4,5],[4,5],[1,7],[5,1,4],[5,1,4],[8,9,10],[8,9],[7,1],[7,1]]),
([w117,w0,w111,w1,w3,w30],[79,81,94,0,6,87,82,121,90,342,88],[],[[0,1,2],[3],[1,4],[5,1,6],[0,2],[0,7],[2,0],[0,2],[6,1,8],[4],[9],[0,7],[10,4],[1,0],[0,1]]),
([w0,w258,w1,w2,w3,w30],[79,0,94,82,85,343,129,122,124,92,89,88],[],[[0,1],[2,0],[0,2],[0,2],[3,4],[5],[6],[7],[8],[4,3,9],[10,4,11],[2,0],[3,4],[0,2],[0,2]]),
([w259,w0,w1,w2,w3,w30],[82,0,259,6,71,85,122,89,92,95,87],[],[[0,1,2],[3,2,4],[0,3,5],[6,7],[8],[9,0],[2,7],[0,5],[0,2],[2,0,7],[2,5],[10,2],[0,5],[0,5],[10,7]]),
([w112,w0,w40,w1,w46,w30],[79,125,94,6,87,121,82,88,259],[],[[0,1,2],[3],[3],[4,1,3],[0,2],[0,5],[2,0],[0,2],[6,7,8],[3],[6,3],[0,5],[4,3],[2,0],[0,2]]),
([w260,w0,w1,w2,w3,w30],[69,53,99,81,60,87,88,61,90,86,91],[16],[[0],[1,2],[3,0,4],[5,0],[3,6],[1,6,7],[8,1,3],[9,1,100],[7,3],[3,1,6],[6,1],[3,8],[10,3],[6,1],[6,1]]),
([w261,w0,w1,w2,w3,w30],[82,0,97,6,344,124,89,92,259,87,88],[],[[0,1,2],[3,4,5],[0,2],[6],[7],[2,0],[8,5],[0,2],[0,2],[2,0],[8,5],[9,8],[0,2],[0,2],[9,5,10]]),
([w0,w262,w1,w2,w3,w30],[82,0,259,94,92,33,87,122,124,85],[],[[0,1,2],[3,0],[2,3],[0,3],[0,2],[4,2],[0,4,5],[6,4,7],[8],[2,0,4],[2,4],[3,2,6],[0,7,6],[0,3,9],[6,3,7]]),
([w112,w39,w0,w1,w2,w30],[0,86,82,6,87,103,88,122,259],[16,34,39,43],[[0,1],[2,0,100],[3],[2,3,4],[1,5,4],[3],[4,1,101],[2,1,102],[6,7,103],[2,4],[8,3],[1,6],[4,2,3],[4,1,8],[2,1,6]]),
([w112,w0,w1,w2,w87,w30],[259,36,97,345,7,87,82,122,86,85,6],[],[[0,1,2],[0,3,4],[5,2,4],[5,4],[5,4],[2,5,6],[0,7],[0,2],[6,0],[0,6,2],[0,8,9],[5,0],[6,2],[6,2],[10]]),
([w114,w0,w113,w1,w2,w3],[82,259,0,87,7,88,92,123,97,346,95],[],[[0,1],[2],[3,1],[0,4,5],[3,6,5],[0,7],[8,0],[1,4],[0,3,8],[4],[9],[3,7],[1,0,4],[1,7,10],[0,4,3]]),
([w263,w0,w1,w2,w3,w30],[51,0,90,81,86,87,61,88],[],[[0],[0,1],[2,0,3],[4,5],[2,0,3],[6,5],[2,3],[4,5],[2,3],[3,2],[7,4,6],[3,2],[5,2,4],[7,4],[5,2,7]]),
([w122,w0,w113,w1,w3,w30],[259,81,95,0,7,87,88,29,123,97,82,347],[],[[0,1,2],[3],[0,4],[5,1,2],[6,4,7],[0,8],[2,5,8],[0,5,9],[10,0],[4],[2,8],[11],[0,8,2],[1,0,5],[5,1,2]]),
([w264,w0,w1,w2,w3,w30],[82,0,97,7,67,63,87,124,92,259,91,88],[],[[0,1,2],[3,4,5],[0,2],[6],[7,8],[2,0],[9,8],[0,2],[0,2],[2,0],[9,8],[8,9,10],[0,2],[0,2],[11,8]]),
([w114,w0,w40,w1,w83,w3],[82,127,259,7,88,6,91,123,97,87,95],[],[[0,1,2],[3],[3],[4,1,3],[4,5],[2,6,7],[8,0],[0,3],[0,8],[3],[0,3],[0,7,9],[2,3],[2,7,10],[9,3]]),
([w265,w0,w1,w2,w3,w30],[55,53,99,97,91,95,87,88,61,259],[37],[[0],[1,0,2],[3,0,4],[5,1,6],[7,0],[3,4,8],[9,4,5],[9,3],[8,3,100],[3,8,6],[4,8],[4,9],[4,3],[4,3],[6,5]]),
([w0,w266,w1,w2,w3,w30],[259,0,121,95,82,124,25,122,92,91,97,88],[],[[0,1,2],[3,2],[0,2],[0,2],[4,0],[0,5],[4,5,6],[7],[8,2],[0,4,5],[0,5],[9,0],[4,3,10],[4,2,10],[11,2]]),
([w114,w267,w0,w1,w2,w3],[0,61,82,73,71,261,88,7,35,87,124,78,86,84],[37,35,40,43],[[0,1],[2,0,100],[1,3,4,5],[2,5,6],[6,5],[7],[6,8,101],[2,7,102],[9,10,103],[2,6],[11,7],[2,9,12],[6,2,7],[6,11,13],[2,7,9]]),
([w114,w0,w1,w2,w87,w3],[82,36,259,6,348,88,97,124,35,85,349],[],[[0,1,2],[3,2,4],[0,3,5],[5,3],[5,3],[6,0],[2,7],[0,6],[0,6],[2,0,6],[2,8,9],[2,7],[0,6],[0,6],[10]]),
([w0,w40,w1,w125,w3,w30],[259,91,97,88,82,14,6,1,7,87],[18,33],[[0,1,100],[2,3,4],[0,5,101],[0,2],[4,0],[6],[1,7,2],[1,6],[1,8],[0,7,2],[0,6],[9,0],[8],[6],[3,6]]),
([w131,w0,w40,w1,w3,w30],[6,14,26,90,97,1,125,162,88,86,91,81],[19],[[0],[1,2,3],[4,5],[6,7],[3,4,8],[3,2],[7,100],[9,0,7],[3,7],[0],[10,0],[8,9],[8,0],[11,3],[8,0]]),
([w0,w40,w1,w133,w3],[97,121,91,88,7,86,6,87,29,90,81,95,46],[3,12,18,0,5,20],[[0,100,1,2,101,102],[0,103,1,3,100],[4,5,100,3],[6,5,104,7],[4],[2,0,8,4,1,9],[2,7,101,6,5],[4,0,10,1,8],[3,11,105,6,5],[3,4,12,0,6]]),
([w140,w0,w40,w1,w3,w30],[6,14,34,90,81,1,86,87,157,91,7,259],[21],[[0],[1,2,3],[4,5],[6,0,7],[3,1,8],[3,2],[7,100],[6,0,7],[3,8],[0],[7,0,6],[9,6,10],[11,0],[7,3,10],[7,0,10]]),
([w0,w40,w1,w143,w30],[259,121,91,95,87,86,14,6,7,88,21,93,84,94,46],[3,12,18,0,5,8],[[0,100,1,2,101,102],[3,103,1,4,100],[0,5,104,1,4,6,7],[8,5,100,9],[7],[2,3,10,7,5,11],[2,9,101,8,1],[0,3,12,7,5,10],[4,13,105,0,1,8],[4,7,14,3,8]]),
([w169,w0,w43,w1,w3,w30],[259,16,95,6,84,91,82,94,53,86,90,88],[3,55],[[0,1,2],[1,3],[0,3,4],[5,2,3],[5,4],[0,100],[2,5,6],[0,4,7],[6,0],[8],[9],[7,10],[101,2,0],[5,0],[11,2,7]]),
([w171,w0,w43,w1,w2,w3],[90,16,91,259,6,88,94,82,65,86,84],[3,55],[[0,1],[1,0],[2,0,3],[2,4,5],[5,0],[3,100],[6,2,7],[0,2],[3,6],[8],[2,0],[9],[3,0,10],[101,10,2],[2,0]]),
([w0,w1,w268,w2,w3,w30],[61,87,259,0,69,88,90,86],[],[[0,1],[2,3,4],[2,4],[2,1,4],[0,2,5],[1,0],[1,0],[2,0],[1,2],[6],[1,3,7],[5,0],[1,7],[5,0],[1,0,5]]),
([w0,w1,w269,w2,w3,w30],[76,87,259,98,93,84,82,86],[],[[0,1],[2,3],[4,5],[0,1],[6,3],[1,0],[1,0],[5,3,4],[1,0],[5,4],[1,0],[7],[1,0],[6,3],[1,0]]),
([w116,w0,w1,w46,w2,w30],[53,20,86,87,88,61,16,131,69,91,76,196],[16],[[0],[0,1],[2,0,3],[3,0],[2,4],[5,4],[2,6],[100,7,8],[2,4],[4,2,5],[4,5],[9,2,10],[11],[4,5],[4,2]]),
([w47,w116,w0,w1,w2,w30],[24,16,86,69,84,131,53,87,88,76,90,132,81],[],[[0,1,2],[2,1],[3,2,4],[5],[3,4],[6],[3,0],[7,3],[2,8],[9,8],[10,3,11],[2,8],[8,3],[12,2],[8,2]]),
([w116,w0,w1,w2,w87,w30],[259,198,273,87,6,84,76,88,10,93,98,91,199],[16],[[0],[1,2],[3,4],[3,5,6],[3,7,8],[6,2],[9,2],[6,2],[100,2,10],[5,6,7],[5,9],[11,6],[11,6,10],[7,5,11],[12]]),
([w90,w116,w0,w1,w2,w30],[42,16,76,69,93,84,98,133,53,87,134,90,91],[],[[0,1,2],[2,1],[3,4,5],[6,2],[7],[8],[2,0,3],[4,3,5],[9,6],[2,10],[4,3,5],[11,6,10],[5,2,4],[12,2],[12,3,4]]),
([w117,w0,w43,w1,w46,w30],[259,131,94,6,91,88,87,121,90],[],[[0,1,2],[3],[0,3],[4,1,3],[4,2,5],[0,6,7],[2,4,7],[0,2],[8,0,5],[3],[6,3],[2,7],[0,3],[2,0,4],[5,2]]),
([w270,w0,w1,w2,w3,w30],[69,53,99,90,76,87,88],[18],[[0],[1,2],[3,0],[4,0,5],[3,6],[1,5,4],[3,1,100],[4,1,5],[3,6],[5,1],[6,1],[5,3,4],[5,3,4],[6,1],[5,1,4]]),
([w271,w0,w1,w2,w3,w30],[259,0,95,344,85,87,92,121,90,88,124],[],[[0,1,2],[0,3],[4],[5,2],[6],[2,5,7],[0,2],[0,5,7],[8,0,9],[0,8,10],[0,10],[5,0],[5,2],[9,7],[5,2]]),
([w0,w1,w272,w2,w3,w30],[95,87,82,0,259,92,129,93,124],[],[[0,1,2],[0,3,4],[4,0],[2,1,5],[2,0],[1,4],[1,2,5],[0,5,4],[1,4],[2,5,6],[0,5,7],[8],[1,0],[2,5,6],[1,0]]),
([w117,w36,w0,w1,w3,w30],[0,90,259,56,6,87,91,111,88,129,350],[18,32,39,40],[[0,1],[2,0,100],[2,3,4],[5,4,6],[1,7,6],[4],[2,1,101],[5,1,102],[8,9,103],[5,10],[2,4],[1,2,8],[2,4],[5,1,2],[5,1,8]]),
([w117,w0,w1,w83,w3,w30],[259,28,95,351,6,129,85,87,88,91,352,82,89],[],[[0,1,2],[0,3,4],[5,6],[7,2],[8,5,9],[2,7,10],[0,2],[0,4],[11,0],[0,10,12],[0,4],[7,0],[7,2],[4],[7,2]]),
([w119,w0,w118,w1,w2,w3],[82,88,259,0,10,92,130,95,353,84],[],[[0,1,2],[3],[4],[0,5,1],[1,4],[0,6],[7,0],[2,7],[0,4],[4],[0,6],[8],[1,0,9],[1,4],[0,4]]),
([w273,w0,w1,w2,w3,w30],[65,0,90,6,84,93,88,76,270,91],[],[[0],[0,1],[2,3,4],[5,0,4],[2,0,6],[7,6],[2,4],[5,4],[2,6],[4,2],[4,5],[8,2,7],[9,2],[6,4,9],[6,2]]),
([w274,w0,w1,w2,w3,w30],[259,0,95,56,10,85,93,88,92,130,78,87],[],[[0,1,2],[0,3,4],[5],[6,2,4],[7,4,8],[2,7,9],[0,2],[0,8],[10,0],[0,8],[0,8],[8,0,11],[10,2],[7,8],[7,2,8]]),
([w123,w0,w118,w1,w2,w30],[259,84,94,0,92,93,95,87,130,78,10,354,88],[],[[0,1,2],[3],[0,4,1],[5,6,7],[7,1],[0,8],[2,7,8],[0,1,2],[9,0],[10],[1,8],[11],[0,5,1],[2,0,7],[12,1,2]]),
([w119,w0,w43,w1,w2,w87],[130,133,95,10,6,88,78,84,91],[],[[0,1,2],[3],[3],[0,4,5],[5,1,3],[2,0],[2,0],[6,2],[6,0],[3],[6,0,7],[2,3,6],[5,0,7],[2,3,5],[8,0]]),
([w275,w0,w1,w2,w3,w30],[98,65,110,84,6,91,70,88,76,93,90,87],[37],[[0],[1,2],[3,4,5],[3,0,6],[7,0],[1,5,8],[9,3],[8,1,3],[10,1,100],[3,8,9],[3,1,5],[5,1],[5,1],[5,1],[11,3]]),
([w0,w276,w1,w2,w3,w30],[78,0,121,95,259,124,129,27,92,87,88],[],[[0,1,2],[3,0],[0,2],[4,2],[0,3],[4,5],[6],[0,5,7],[8,2],[4,5],[3,0],[9,2,4],[0,3],[10,2],[0,2,3]]),
([w119,w267,w0,w1,w2,w3],[0,121,78,261,73,71,88,10,91,90,82,84],[37,35,40,43],[[0,1],[2,0,100],[3,4,5],[6,3],[2,3,6],[7],[6,1,101],[8,1,102],[2,1,103],[2,6],[2,8,9],[10,7],[6,9,11],[6,2,7],[2,7,8]]),
([w119,w0,w1,w83,w2,w3],[78,28,259,91,88,6,95,124,90,89,10],[],[[0,1,2],[3,2],[4,5],[3,5,4],[0,5,4],[6,0],[0,6],[0,3,6],[2,7],[2,8,9],[2,7],[2,0,6],[10],[0,6],[0,6]]),
([w0,w43,w1,w125,w2,w30],[259,87,95,91,78,16,6,7,1,10],[16,30],[[0,1,100],[2,3,4],[0,5,101],[0,2],[4,0],[6],[1,7],[1,6],[1,7],[0,8,2],[0,6],[3,0],[9],[6],[3,6,9]]),
([w128,w0,w43,w1,w2,w30],[6,16,24,93,95,1,196,90,88,87,81],[17],[[0],[1,2,3],[4,5],[3,0,6],[7,4,8],[3,2],[6,100],[3,0,6],[7,6],[0],[9,0],[8,3,7],[8,0],[10,7],[8,0]]),
([w0,w43,w1,w2,w130],[259,121,87,95,91,90,6,10,16,37,86,81,77,59],[5,13,16,0,3,20],[[0,100,1,2,101,102],[3,103,1,4,100],[0,5,104,1,4,6],[7,5,100,8],[6],[2,4,101,6,5],[2,3,9,7,1,10],[0,11,105,6,5],[4,3,12,0,1,7,9],[4,6,13,7]]),
([w150,w0,w43,w1,w2,w30],[6,16,42,86,259,91,90,199,81,10],[21],[[0],[1,2,3],[4,5],[6,0,5],[3,1,7],[3,2],[5,100],[4,0],[3,4,7],[0],[5,0,6],[8,6],[4,0],[5,3,4],[5,0,9]]),
([w0,w43,w1,w153,w30],[259,121,87,95,91,90,16,6,10,81,21,93,84,59],[5,13,16,0,3,2],[[0,100,1,2,101,102],[3,103,1,4,100],[0,5,104,1,4,6,7],[8,5,100,9],[7],[2,3,10,7,5,11],[2,9,101,8,1],[0,3,12,7,5,10],[4,9,105,0,1,8],[4,7,13,3,8]]),
([w181,w0,w81,w1,w3,w30],[93,18,81,91,226,95,224,259,87],[15],[[0,1],[1,0],[2,0],[3,2],[3,0],[4,100,5],[5,3,4],[0,6],[4,2,5],[7],[5,0],[4],[3,0,5],[4,2],[8,0]]),
([w183,w0,w81,w1,w2,w30],[93,18,91,95,81,87,78,259,90],[15,56],[[0,1],[1,0],[2,0,3],[2,3,4],[5,0],[3,100],[3,2,6],[0,2],[6,3],[7],[2,0],[8],[4,0],[101,4,2],[2,0]]),
([w0,w1,w277,w2,w3,w30],[76,91,259,0,55,87,78,84,90,81,35],[],[[0,1],[2,3,4],[2,1,4],[0,5],[6,2],[1,0],[2,0],[1,6,7],[1,0],[8],[5,0],[9,3,10],[1,0,5],[1,7],[5,0]]),
([w0,w1,w278,w2,w3,w30],[61,87,259,0,98,81,90,93,91,84],[],[[0,1],[2,3,4],[2,5,6],[2,1,4],[0,2,5],[1,0],[1,0],[2,0],[1,2],[5,6],[7],[5,0],[1,4,8],[8,0,4],[1,0,9]]),
([w121,w0,w1,w83,w2,w3],[355,231,274,81,90,88,91,6,61,55,76,87,233],[37],[[0],[1,2],[0,3,4],[5,6,7],[5,7],[8,2],[4,2],[100,2,9],[10,2],[3,4],[11,8],[6,8],[12],[11,3,9],[6,9,11]]),
([w85,w121,w0,w1,w2,w3],[32,18,90,81,135,87,118,234,356,6,84,76,93],[],[[0,1,2],[2,1],[3,2],[4],[5,2],[6],[7,5],[8,9,10],[11,5],[11,5],[12,10],[11,5],[5,11],[10,12],[5,11]]),
([w121,w0,w1,w2,w87,w3],[357,235,276,90,6,81,88,61,98,91,237],[37],[[0],[1,2],[3,4,5],[0,5,3],[6,4],[7,2],[3,2],[3,2],[100,2,8],[5,3],[5,3],[9,7],[9,7,8],[9,3],[10]]),
([w89,w121,w0,w1,w2,w3],[40,18,90,81,91,61,137,120,358,6,88,76,138],[],[[0,1,2],[2,1],[3,2],[4,5],[6],[7],[5,0,4],[2,3],[8,9,10],[5,4],[2,3],[11,12],[3,2],[4,5],[4,2]]),
([w122,w0,w81,w1,w83,w3],[78,135,95,143,87,10,88,130,93,129,347,81],[],[[0,1,2],[3],[4,3,5],[3,5],[0,2],[0,6,7],[2,0],[0,2],[8,4],[9],[6,7,10],[0,8],[4,7,11],[2,0],[0,2]]),
([w279,w0,w1,w2,w3,w30],[78,65,44,56,110,81,93,87,12,75,76,95,90,88,61],[18],[[0],[1,2,3,4],[5,2],[6,1,7],[8,1,9],[10,7],[6,11,100],[6,7],[12,11,13],[7,6,10],[11,6],[7,10],[7,10],[13,6,14],[7,6]]),
([w280,w0,w1,w2,w3,w30],[78,0,94,10,1,85,95,93,87,129,92,88,91],[],[[0,1,2],[3,4],[5],[6],[4,2,3],[2,0],[0,2],[7,2,8],[0,9],[8,7,10],[11,0,9],[2,9,8],[0,9,12],[11,2],[0,2,7]]),
([w0,w1,w281,w2,w3,w30],[95,88,130,259,82,1,10,92,91,87,43],[],[[0,1,2],[0,2],[3,0],[3,2],[4,0],[1,5,6],[1,2,7],[0,7,1],[7,3,8],[4,2],[9],[1,6,10],[4,0,2],[1,2,4],[1,0,7]]),
([w122,w36,w0,w1,w3,w30],[0,130,259,56,111,87,91,359,88,360,93,78,84],[18,32,39,40],[[0,1],[2,0,100],[2,3,4],[5,4,6],[6,4],[7],[2,1,101],[5,1,102],[8,1,103],[5,9],[2,5,10],[11,2],[2,9,12],[5,2],[5,10]]),
([w122,w0,w1,w46,w3,w30],[78,20,94,10,361,362,129,85,91,259,33,92,363,88],[],[[0,1,2],[3,4,5],[6,7],[0,3,8],[8,2,3],[2,0],[0,2],[9,2],[0,6],[8,10,11],[8,0,6],[2,6,8],[12],[13,2],[0,2,13]]),
([w123,w0,w81,w1,w2,w87],[130,137,94,145,10,81,78,41,91],[],[[0,1,2],[3],[4],[0,5],[3,4],[2,0],[2,0],[6,2],[6,0],[4],[5,0],[2,4,7],[5,0],[2,4,7],[8,0]]),
([w282,w0,w1,w2,w3,w30],[98,65,110,81,91,78,75,61,93,88],[16],[[0],[1,2],[3,4],[5,0],[3,0,6],[1,4,7],[8,3],[8,1,100],[7,1,3],[3,7,8],[4,1],[3,1,4],[4,1],[4,1],[9,3]]),
([w0,w283,w1,w2,w3,w30],[78,0,123,94,259,1,343,91,35,92,87,88],[],[[0,1,2],[3,0],[0,2],[4,3],[0,2],[4,5,6],[7],[0,2],[3,6,8],[4,9],[4,0,9],[3,4,10],[0,2],[11,3],[0,2]]),
([w123,w39,w0,w1,w2,w30],[0,93,259,67,10,6,87,91,123,88,364,82,81],[16,34,39,43],[[0,1],[2,0,100],[2,3,4],[1,5,6],[6,4],[4],[2,1,101],[7,8,102],[9,1,103],[6,10],[1,7],[11,2],[2,1,12],[6,2],[7,1]]),
([w123,w0,w1,w46,w2,w30],[123,20,94,91,365,10,6,87,82,259,92,88],[],[[0,1,2],[3,4,5],[0,6,7],[3,6,7],[7,2,5],[2,0],[8,2],[9,0],[8,0],[3,0,10],[7,8,10],[2,5,3],[5],[11,0,2],[3,2,5]]),
([w0,w81,w1,w125,w2,w3],[82,88,94,18,78,366,1,87,92,91,10,123],[37,31],[[0,1,100],[2,0],[0,3,101],[4,2],[0,2],[5],[1,5],[0,5,1],[1,5],[2,6],[7,0,8],[9,4,8],[10],[11],[0,10]]),
([w136,w0,w81,w1,w2,w3],[10,18,32,61,94,87,1,135,233,93,88,84,7],[17],[[0],[1,2,3],[4,5,6],[7,8],[9,0,5],[3,2],[5,100],[9,8],[9,0,5],[0],[10,3],[5,0,9],[5,9,11],[11,0,9],[5,0,12]]),
([w0,w81,w1,w2,w139],[94,123,88,87,7,93,91,10,37,86,84,77,62],[5,14,37,0,3,8],[[0,100,1,2,101,102],[0,103,1,3,100],[4,5,104,6],[7,5,100,3],[4],[2,6,101,4,5],[2,0,8,7,1,9],[3,10,105,4,5],[6,0,11,7,1,8],[6,3,12,4,7]]),
([w146,w0,w81,w1,w2,w3],[10,18,40,86,94,1,93,84,138,91],[19],[[0],[1,2,3],[4,5],[6,4,7],[3,0,7],[3,2],[8,100],[6,7],[3,0,7],[0],[7,3,6],[7,0,6],[7,6],[7,0,3],[9,0]]),
([w0,w81,w1,w149,w3],[94,123,88,91,7,93,10,84,29,90,81,62],[5,14,37,0,3,2],[[0,100,1,2,101,102],[0,103,1,3,100],[4,5,104,3],[6,5,100,7],[4],[2,0,8,4,5,9],[2,7,101,6,1],[4,0,10,5,8],[3,7,105,6,1],[3,4,11,0,6]]),
([w284,w0,w1,w2,w3,w30],[102,61,1,88,0,93,62,91,315],[],[[0],[1,2,3],[0,4],[5,0,6],[1,0,3],[1,3],[5,6],[5,6],[1,3],[3,1],[3,1],[7,8],[7,8],[3,1],[3,1]]),
([w285,w0,w1,w2,w3,w30],[94,0,82,88,10,15,84,62,6,78,343,59],[],[[0,1,2],[3],[4,2,5],[6,4,7],[0,4,8],[0,2],[9,0],[2,0],[2,10],[6,2],[6,7],[0,10,11],[2,10],[2,0,6],[7,0,6]]),
([w126,w0,w1,w46,w30],[140,10,88,78,112,21,6,81,79,93],[20,23,12,1,7,2,14],[[0,1],[2,100,3,4,5,101],[0,6],[1,2,102,7],[0,103,8],[6,0,9],[1,0,104],[2,7,100,6,9],[1,7,105,8],[1,2,106,6]]),
([w0,w127,w1,w46,w30],[94,123,20,88,367,78,90,6,81,10,84],[15,18,0,5,12,11,14],[[0,100,1,2,101],[0,102,1,3,4],[5,6,100,0,7,8],[5,6,103,1,3,9],[4,7],[4,7],[5,0,104,9,6],[3,4,10,7],[9,0,105,4],[9,3,106,0,7]]),
([w286,w0,w1,w2,w3,w30],[10,0,65,6,81,90,94,79,84,110,93,100],[],[[0,1],[2],[1,3],[1,0],[4,0,5],[6,7],[5,4],[7,6],[5,4],[4,5],[8,9,10],[4,5],[4,11],[7,6],[7,4]]),
([w287,w0,w1,w2,w3,w30],[65,0,44,6,14,63,16,90,81,61,88,93,98,84,55],[],[[0],[0,1],[2,3,4],[5,0,6],[7,0,8],[9,10],[7,8],[11,12,13],[7,8],[8,7],[10,9],[8,7],[7,14],[10,9],[10,7]]),
([w288,w0,w1,w2,w3,w30],[10,0,65,81,93,90,94,88,84,87,86],[5],[[0,1],[2],[3,1,4],[1,0],[3,0,5],[6,7,100],[4,3],[4,6,8],[5,3],[3,4],[7,4,8],[3,5],[9,3,10],[7,4,6],[7,3]]),
([w289,w0,w1,w2,w3,w30],[65,0,93,15,81,16,90,61,78,98,84,86,79],[2],[[0],[0,1],[2,3,4],[2,0,5],[6,0,4],[7,8,100],[2,4],[2,9,10],[6,4],[4,2],[10,2],[4,6],[8,4,11],[12,2,7],[8,2]]),
([w0,w1,w4,w2,w3,w129],[79,88,110,81,93,321,90,98,7,78,301,34],[],[[0,1],[2],[0,3,4],[0,5],[6,1],[7],[1,4,3],[1,4,5],[3,0],[3,8],[2,4],[0,2],[9,3,10],[0,4,11],[0,3]]),
([w32,w0,w1,w2,w3,w129],[65,321,90,81,93,84,61,78,55,79],[17],[[0],[1],[2,3],[4,0,5],[2,0,3],[6,7,100],[2,3],[4,5],[2,3],[3,2],[5,4],[3,2],[7,2,8],[9,4,6],[7,2,4]]),
([w33,w0,w1,w2,w3,w129],[79,51,81,93,84,90,94,88,87,100],[17],[[0],[1],[2,1,3],[4,3],[2,1,5],[6,7,100],[3,2],[3,4],[5,2],[2,3],[4,3],[2,5],[8,2,9],[7,3,6],[7,2]]),
([w0,w1,w4,w2,w3,w130],[79,88,94,81,90,87,321,98,7,91],[],[[0,1],[2],[0,3,4],[0,5,6],[4,1],[7],[1,4,3],[1,6],[3,0],[3,8],[5,6],[0,6],[5,3,9],[0,6,9],[0,3]]),
([w32,w0,w1,w2,w3,w130],[65,321,90,81,78,61,79,98,82],[17],[[0],[1],[2,3],[4,0],[2,0,3],[5,4,100],[2,3],[6,7],[2,3],[3,2],[4,5],[3,2],[4,2,8],[6,5],[4,2,6]]),
([w33,w0,w1,w2,w3,w130],[321,65,81,90,87,94,88,110,91],[17],[[0],[1],[2,3],[4,0],[2,0,3],[5,4,100],[3,2],[4,5],[3,2],[2,3],[6,7],[2,3],[4,2,8],[6,5],[4,2,6]]),
([w290,w0,w1,w2,w3,w30],[94,0,7,51,84,78,90,91,93,100,81,88],[17],[[0,1,2],[3],[1,2],[4,1,5],[0,2,6],[0,7,100],[6,0,4],[8,0,4],[6,9,10],[4,6],[4,8],[0,6],[7,6],[7,0,4],[11,0]]),
([w291,w0,w1,w2,w3,w30],[51,0,44,14,93,17,84,90,81,61,79,82],[17],[[0],[0,1],[2,0,3],[4,5,6],[7,0,8],[9,10,100],[4,6],[4,6],[7,8],[6,4],[6,4],[8,7],[11,7],[10,4,9],[10,4,7]]),
([w0,w1,w4,w2,w3,w132],[79,88,100,301,321,90,55,81,84,82],[],[[0,1],[2],[0,3],[0,4],[5,1],[6],[1,3],[1,4],[7,0],[2,8],[4,8],[0,2],[9,3,4],[0,4,5],[0,3,5]]),
([w32,w0,w1,w2,w3,w132],[51,301,82,84,93,90,81,61,55,98,79],[17],[[0],[1],[2,0,3],[4,3],[5,0,6],[7,2,100],[4,3],[2,3,4],[2,6,5],[3,2],[3,4],[6,5],[2,8,9],[2,3],[10,3,5]]),
([w33,w0,w1,w2,w3,w132],[301,51,84,93,0,90,94,88,91,100,110],[17],[[0],[1],[2,0,3],[2,3],[4,0,5],[6,7,100],[3,2],[3,2],[5,4],[2,3],[2,3],[6,5],[8,9,10],[7,2,5],[7,2,5]]),
([w0,w1,w4,w2,w133,w3],[79,88,100,301,90,87,86,55,300,91],[],[[0,1],[2],[0,3],[4,1],[0,5,6],[7],[1,3],[5,0,3],[1,6,8],[2,9],[0,2],[5,8],[0,4],[5,3],[0,3,4]]),
([w32,w0,w1,w2,w133,w3],[51,301,82,90,81,86,6,77,61,79,55,78],[17],[[0],[1],[2,0],[3,0,4],[5,6,7],[8,2,100],[9,10],[2,4,3],[2,7,5],[2,8],[4,3],[7,5],[2,3,9],[2,5,11],[9,3]]),
([w33,w0,w1,w2,w133,w3],[301,51,91,0,90,77,86,94,88,100,87],[17],[[0],[1],[2,0],[3,0,4],[5,6],[7,2,100],[2,7],[4,3],[6,5],[8,9],[2,4,5],[2,6,5],[2,4,8],[2,5,10],[8,4]]),
([w134,w0,w1,w83,w3],[142,7,87,79,112,29,6,77,78,90],[8,23,12,1,6,2,13],[[0,1],[2,100,3,4,5,101],[0,1],[3,2,102,6,7],[0,103,8],[1,0,9],[6,0,104],[1,7,100,9],[6,7,105,8],[6,1,106]]),
([w0,w135,w1,w83,w3],[78,123,28,368,87,86,7,77,79,6,81],[3,18,0,5,12,10,13],[[0,100,1,2,101],[3,102,4],[0,5,100,1,6,7],[8,5,103,9,4],[3,6],[3,6],[8,0,104,9,1],[4,3,10,6],[9,3,105],[9,0,106,1,6]]),
([w292,w0,w1,w2,w3,w30],[7,0,51,77,6,86,94,78,81,100,90,112],[],[[0,1],[2],[1,0],[3,4,5],[1,0],[6,7],[7,6],[5,3],[5,3],[8,9,10],[3,5],[3,5],[7,3],[3,11],[7,6,9]]),
([w293,w0,w1,w2,w3,w30],[51,0,44,14,86,6,87,18,61,90,55,81,77,84],[],[[0],[0,1],[2,0,3],[4,5,6],[4,0,7],[8,6],[9,10,11],[4,6],[4,10,11],[6,8],[12,4],[6,4,10],[6,4],[4,13],[6,8,10]]),
([w294,w0,w1,w2,w3,w30],[7,0,51,81,90,87,6,86,94,77,88],[5],[[0,1],[2],[3,0,4],[5,6,7],[1,0],[8,5,100],[4,3],[7,5],[4,3],[3,4],[9,7],[3,4],[5,3,7],[10,7],[5,3,10]]),
([w295,w0,w1,w2,w3,w30],[94,87,0,7,90,81,86,77,61,78,79],[2],[[0],[1,2,3],[4,3,5],[6,7],[4,3,5],[8,9,100],[4,5],[6,7],[4,5],[5,4],[7,6],[5,4],[9,4,6],[10,6],[9,4,10]]),
([w0,w1,w4,w2,w138,w30],[78,87,94,81,90,86,61,77,7,6,79,300],[],[[0,1],[2],[0,3,4],[5,1],[0,3,4],[6],[1,4,3],[7,0],[1,4,3],[3,8],[0,9],[3,8],[0,3,5],[10,11],[0,3,5]]),
([w32,w0,w1,w2,w138,w30],[53,300,90,81,86,77,61,79,78],[17],[[0],[1],[2,0,3],[4,0,5],[2,3],[6,7,100],[2,3],[4,5],[2,3],[3,2],[5,4],[3,2],[8,2,4],[7,6],[7,2]]),
([w33,w0,w1,w2,w138,w30],[300,53,81,90,0,86,94,87,77,88],[17],[[0],[1],[2,0,3],[4,0,5],[2,3],[6,7,100],[3,2],[5,4],[3,2],[2,3],[8,5],[2,3],[7,2,5],[9,6],[7,2,5]]),
([w0,w1,w4,w2,w139,w30],[79,88,100,301,0,86,78,55,77,87,84,10,91],[],[[0,1],[2],[0,3],[0,4,5],[6,1,3],[7],[1,3],[1,5,8],[9,0,3],[2,10],[4,11],[0,2],[6,3],[0,10,12],[0,3,6]]),
([w32,w0,w1,w2,w139,w30],[51,301,82,84,86,79,76,55,78],[17],[[0],[1],[2,0,3],[4,3],[5,0],[6,2,100],[5,3,7],[2,3,4],[2,7],[3,2],[3,4],[5,6],[2,4,8],[2,3],[5,3,8]]),
([w33,w0,w1,w2,w139,w30],[301,51,84,93,88,95,87,100,91],[17],[[0],[1],[2,0,3],[2,3],[4,0],[5,4,100],[3,2],[3,2],[4,5],[2,3],[2,3],[6,7],[6,5],[4,2,8],[4,2,6]]),
([w296,w0,w1,w2,w3,w30],[7,0,51,84,86,77,95,87,93,91],[17],[[0,1],[2],[1,0],[3,4],[5,0,4],[6,7,100],[8,3],[4,3],[4,5],[3,8],[3,4],[5,4],[7,4],[9,3],[7,3]]),
([w297,w0,w1,w2,w3,w30],[51,0,44,14,86,84,77,76,78,55,93,82],[17],[[0],[0,1],[2,0,3],[4,5],[4,0,6],[7,8,100],[8,5,9],[4,5],[4,6],[5,7,10],[5,4],[6,4],[8,4],[11,4,5],[8,5]]),
([w0,w1,w4,w2,w142,w30],[82,87,100,78,301,93,55,84,6,77,321],[],[[0,1],[2],[3,4],[0,1,5],[0,4],[6],[1,0,4],[7,3],[1,4],[0,2],[1,8],[2,9],[0,4,1],[0,9,10],[1,4]]),
([w32,w0,w1,w2,w142,w30],[51,301,82,81,93,84,86,76,78,55,98],[17],[[0],[1],[2,0,3],[4,5],[6,0,3],[7,2,100],[8,3,9],[2,5,4],[2,3,6],[3,2],[5,4],[3,6],[2,3],[2,6,10],[8,3,4]]),
([w33,w0,w1,w2,w142,w30],[301,51,81,90,0,93,95,87,91,110],[17],[[0],[1],[2,0,3],[4,5],[2,0,3],[6,7,100],[3,2],[5,4],[3,2],[2,3],[6,5],[2,3],[7,2,5],[8,9],[7,2,5]]),
([w0,w1,w4,w143,w2,w30],[78,87,100,93,301,55,84,6,91,86,88],[],[[0,1],[2],[3,1],[0,4],[0,4],[5],[6,0],[1,4],[1,4],[0,7],[2,8],[2,9],[0,3],[0,3],[8,9,10]]),
([w32,w0,w1,w143,w2,w30],[51,301,93,84,82,86,77,76,78,55,79],[17],[[0],[1],[2,3],[4,0],[5,0,6],[7,4,100],[2,3],[8,9],[4,6,5],[3,2],[4,7],[6,5],[4,2,8],[8,2],[4,5,10]]),
([w33,w0,w1,w143,w2,w30],[301,51,0,86,91,77,95,87,100,88],[17],[[0],[1],[2,3],[4,0],[5,0,3],[6,4,100],[3,2],[4,6],[3,5],[4,3,5],[7,8],[4,3,5],[4,3,7],[7,6],[4,3,9]]),
([w144,w0,w1,w2,w87],[144,7,91,78,112,37,10,82,86,84],[2,22,12,13,1,4,8],[[0,1],[2,100,3,4,5,101],[1,2,102,4,103],[0,6],[0,104,7],[1,0,105],[6,0,8],[1,9,106,7],[2,9,100,4,6,8],[2,1,102,4,6]]),
([w0,w145,w1,w2,w87],[82,123,36,369,91,7,93,10,84,77],[5,16,0,3,12,13,9],[[0,100,1,2,101],[3,102,4],[5,6,103,4],[0,6,100,7,8],[3,5],[5,0,104,6,105],[3,7],[5,3,106],[4,3,9,7],[0,5,104,7]]),
([w298,w0,w1,w2,w3,w30],[7,0,51,84,82,86,95,93,77,110,99],[],[[0,1],[2],[3,0,4],[1,5,3],[1,0],[6,4],[7,3],[4,3,5],[4,6],[3,4],[3,5],[8,5],[4,5,9],[4,3],[3,10]]),
([w299,w0,w1,w2,w3,w30],[65,0,93,84,71,18,76,91,86,98,77,69],[],[[0],[0,1],[2,3],[2,0,3],[4,0,5],[6,7],[2,3],[2,3],[8,9,10],[3,2],[3,2],[7,6],[7,6,9],[7,2],[2,11]]),
([w300,w0,w1,w2,w3,w30],[10,0,65,84,6,93,95,91,86,77,110,88,81],[17],[[0,1],[2],[3,4,5],[3,0,5],[1,0],[6,7,100],[5,3],[5,3],[8,6,9],[3,5],[3,5],[7,8,9],[7,6,10],[7,3],[11,3,12]]),
([w301,w0,w1,w2,w3,w30],[65,0,93,6,84,71,18,76,82,98,77,86,79,81],[17],[[0],[0,1],[2,3,4],[2,0,4],[5,0,6],[7,8,100],[2,4],[2,4],[8,9],[4,2],[4,2],[10,7,11],[8,7,9],[8,2],[12,2,13]]),
([w0,w1,w4,w148,w3,w30],[82,91,110,93,321,98,81,6,77,79,300],[],[[0,1],[2],[3,1],[0,4],[0,4],[5],[6,0],[1,3,4],[1,4],[0,7],[2,3],[2,8],[0,4],[0,3],[9,3,10]]),
([w32,w0,w1,w148,w3,w30],[53,300,93,81,77,79,76,82,98,69],[17],[[0],[1],[2,0,3],[2,0,4],[5,4],[6,5,100],[2,3],[2,4],[7,4,8],[3,2],[4,2],[4,5],[7,3],[5,2,4],[5,2,9]]),
([w33,w0,w1,w148,w3,w30],[300,53,0,93,77,10,86,95,91,81,88,99],[17],[[0],[1],[2,0,3],[4,0,3],[4,5,6],[7,8,100],[3,2],[3,4],[6,4],[9,3],[4,3],[4,6],[8,4,9],[8,3],[10,3,11]]),
([w0,w1,w4,w149,w3,w30],[79,88,110,0,93,321,82,98,81,91,7,78],[],[[0,1],[2],[0,3,4],[0,5],[6,1,5],[7],[1,4,8],[1,4,5],[9,0,5],[3,10],[2,4],[0,2],[6,5],[0,4,6],[0,4,11]]),
([w32,w0,w1,w149,w3,w30],[65,321,93,81,84,79,76,78,98,34],[17],[[0],[1],[2,3],[2,0,4],[5,0],[6,5,100],[2,3],[2,4],[7,8],[3,2],[4,2],[5,6],[7,3,6],[5,2,9],[5,2,7]]),
([w33,w0,w1,w149,w3,w30],[321,65,0,93,84,88,95,91,110,87],[17],[[0],[1],[2,3],[4,0,3],[5,0],[6,5,100],[3,2],[3,4],[5,6],[4,3],[4,3],[7,8],[7,6,8],[5,3,7],[5,3,9]]),
([w302,w0,w1,w2,w3,w30],[10,0,65,81,93,79,95,91,110,84,86,87],[17],[[0,1],[2],[3,4],[1,0],[3,0,5],[6,7,100],[4,3],[4,8,9],[10,3],[3,4],[6,4],[3,8,7],[7,3],[7,4],[11,3,4]]),
([w303,w0,w1,w2,w3,w30],[65,0,93,84,86,81,76,78,82],[17],[[0],[0,1],[2,3],[2,0,3],[4,0,5],[6,7,100],[2,3],[2,3],[4,5],[3,2],[3,2],[5,4],[7,4],[8,2],[7,2]]),
([w0,w1,w4,w152,w3,w30],[78,91,110,93,86,321,82,98,84,6,300,301],[],[[0,1],[2],[0,1,3],[4,5,6],[0,5],[7],[8,3],[1,0,5],[1,4,5],[1,9],[0,2],[2,4],[0,3,1],[1,3],[0,10,11]]),
([w32,w0,w1,w152,w3,w30],[53,300,93,84,86,77,76,82,78],[17],[[0],[1],[2,0,3],[4,0,5],[4,5],[6,7,100],[2,3],[4,5],[4,5],[3,2],[5,4],[5,4],[7,2],[7,2],[8,6]]),
([w33,w0,w1,w152,w3,w30],[82,53,0,93,77,86,95,91,84,87],[17],[[0],[1],[2,1,3],[4,1,5],[4,5],[6,7,100],[3,2],[5,4],[5,4],[8,3],[4,5],[4,5],[7,3],[7,3],[9,6]]),
([w0,w1,w4,w153,w3,w30],[82,91,99,93,300,321,69,84,87,81,79],[],[[0,1],[2],[3,1],[0,4],[0,5],[6],[7,0],[1,4],[1,5],[0,2],[2,8],[5,9],[0,3],[0,3],[8,4,10]]),
([w32,w0,w1,w153,w3,w30],[53,300,82,84,78,79,10,81,61,69],[17],[[0],[1],[2,0,3],[4,0],[5,6,7],[8,2,100],[4,3,9],[2,9],[2,7,8],[3,2],[4,8],[7,5],[2,3],[2,3],[4,7,5]]),
([w33,w0,w1,w153,w3,w30],[300,53,0,93,87,81,10,90,94,91,99,88],[17],[[0],[1],[2,0,3],[4,0],[5,6,7],[8,4,100],[3,2],[4,8],[7,5],[4,3,5],[9,10],[4,7,5],[4,3,9],[9,3],[4,5,11]])]
noncomputable def p13_D4 : List StD := [
([w50,w0,w1,w154,w30],[69,53,84,82,86,88,79,81],[],[[0,1],[2,0],[3,0,4],[5,2,4],[1,5,6],[4,1,2],[4,5],[2,1,4],[7,4],[5,1]]),
([w155,w31,w4,w2,w30],[84,67,63,53,82,22,81,79,59,95],[17],[[0,1,2],[0,3],[4,5,6],[7,0,6],[100],[0,8],[4,8,6],[0,3],[6,9],[4,0]]),
([w50,w0,w1,w3,w156],[79,81,95,370,129,87,53,86],[],[[0,1,2],[1,3,4],[5,1,2],[0,3,6],[2,0],[0,5,7],[7,1],[2,7],[1,0],[0,1]]),
([w157,w31,w4,w2,w3],[81,73,71,95,79,30,34,62,371,82],[17],[[0,1,2],[0,3],[4,5,6],[4,0],[100],[0,7],[3,7],[0,3],[7,8],[9,0]]),
([w304,w0,w1,w3,w30],[69,79,15,14,82,10,53,61,86,84,81,62],[23],[[0,1],[2,0,3],[4,0],[4,5],[6,100,7],[8,6,9],[7,10],[9,6,8],[10,8],[11,6,9]]),
([w91,w0,w1,w160,w30],[69,99,82,7,53,79,95,86,81],[],[[0],[1],[2,0],[2,3],[4,5,6],[5,4],[7,6,8],[6,4,7],[8,5],[5,4]]),
([w91,w0,w1,w162,w3],[69,99,82,7,53,87,61,14,86,372,95],[],[[0],[1],[2,3],[2,0],[4,5,6],[6,7],[8,4,5],[5,8,9],[10,4,8],[5,4,10]]),
([w169,w0,w1,w3,w30],[69,53,99,82,86,7,95,81,87],[],[[0,1],[2,1],[3,0],[3,4,5],[1,3,6],[3,1],[3,6],[6,1,4],[7,4],[8,1,6]]),
([w155,w0,w1,w2,w30],[86,0,95,87,82,79,81],[],[[0,1],[2,0],[3,0],[3,2],[2,3,4],[5,2],[0,2,4],[3,4,6],[3,0,6],[4,0,5]]),
([w305,w0,w1,w2,w3],[82,0,86,87,81,79,95],[],[[0,1,2],[3,2,4],[0,2,5],[3,4,5],[6,0],[5,4,6],[0,3,2],[3,0,4],[6,2],[0,2,3]]),
([w157,w0,w1,w2,w154],[86,95,81,79,87,61],[],[[0,1,2],[2,0],[3,0],[3,1,2],[1,3],[3,1],[0,4],[2,5,4],[1,0],[4,0]]),
([w155,w0,w1,w2,w156],[79,87,86,95,81,61],[],[[0,1,2],[3,2],[1,2],[0,3,1],[3,0],[0,3],[2,3,4],[1,5],[1,0,4],[0,2]]),
([w155,w157,w0,w1,w2],[87,81,79,86,95,61],[],[[0,1,2],[2,0,3],[4,3],[0,1,3],[3,1],[0,2,1],[2,3],[4,0,2],[2,1,4],[0,5]]),
([w181,w0,w1,w3,w30],[79,0,95,87,56,61,86,81],[],[[0,1,2],[3,4,5],[3,2],[0,5],[2,0],[0,3,6],[5,2,7],[2,5,6],[3,0,7],[0,2,3]]),
([w306,w0,w1,w2,w30],[86,0,95,87,61,79,81],[],[[0,1],[2,0],[3,0],[3,2],[2,3,4],[5,2],[0,2,6],[3,4],[3,0,6],[5,0]]),
([w157,w0,w1,w2,w3],[61,0,87,73,81,79,95,86],[],[[0,1],[2,3,4],[5,0],[2,0,5],[0,2],[5,4,6],[5,2,7],[2,0],[6,0,7],[2,4,6]]),
([w307,w0,w1,w3,w30],[95,0,69,81,87,86,7,82,79,53],[],[[0,1,2],[3,2],[0,2,4],[5,6,7],[0,8],[5,9,8],[5,0,3],[0,5],[3,5],[8,0,3]]),
([w91,w0,w1,w133,w3],[69,99,81,7,82,53,79,95,86],[],[[0],[1],[2,3,4],[4,0],[5,6,7],[8,2],[6,5],[2,6],[7,5,8],[6,2]]),
([w308,w0,w1,w3,w30],[53,69,81,86,82,87,61,95,78,51],[],[[0,1],[0,2],[3,0,4],[3,2,4],[0,5,6],[3,0,5],[3,7,8],[7,0,3],[5,3,9],[5,0,7]]),
([w91,w0,w1,w143,w30],[55,100,86,6,82,51,87,61,78,81],[],[[0],[1],[2,3,4],[2,0,4],[5,6,7],[2,6],[2,5,8],[9,2],[6,2,5],[6,5]]),
([w31,w34,w1,w160,w30],[51,55,100,16,78,17,86,59,95,53,82,94],[],[[0,1],[2],[3,4,5],[6,0,7],[0,7,8],[4,9,7],[6,0,10],[3,4,5],[11,0,6],[4,0]]),
([w31,w34,w1,w162,w3],[78,373,7,86,6,62,51,95,53,82,18],[],[[0,1,2],[1],[0,2],[3,4,5],[6,1,5,7],[3,6,5],[0,8,9],[10,3,6],[7,0],[0,6]]),
([w31,w0,w40,w160,w30],[69,53,99,374,78,86,7,59,61,81],[],[[0],[1,2],[3,0,4],[5,6,7],[1,7,8],[5,1,3],[5,7],[7,1],[9,5],[7,1]]),
([w31,w0,w40,w162,w3],[69,53,99,375,7,59,86,62,61,51],[],[[0],[1,2],[3,4,5],[6,0,7],[1,5,8],[6,3],[6,1,7],[7,6,9],[5,1],[5,1]]),
([w31,w4,w2,w160,w30],[79,376],[17],[[100],[0,1],[0,1],[1],[1],[1],[1],[1],[0,1],[0,1]]),
([w161,w31,w4,w2,w30],[17,62,16,53,24,377,20,81,59,378,379],[17],[[0,1,2],[3,0],[4,5,6],[1,5],[100],[7,1],[7,5,8],[1,3],[5,7],[1,9,10]]),
([w31,w4,w2,w162,w3],[78,373],[17],[[100],[0,1],[0,1],[1],[1],[1],[1],[1],[0,1],[0,1]]),
([w163,w31,w4,w2,w3],[19,59,18,51,32,378,28,84,62,377,379],[17],[[0,1,2],[3,0],[4,5,6],[1,5],[100],[7,1],[7,5,8],[1,3],[5,7],[1,9,10]]),
([w164,w0,w1,w9,w30],[69,53,22,59,7,61,78,95,79,88,81],[27],[[0,1],[2,0],[100],[3,4,5],[1,6,7],[8,1],[5,3],[9,1],[10,3],[6,1,8]]),
([w309,w0,w1,w2,w3],[78,0,95,81,59,79,62,86,88,61],[],[[0,1,2],[3,4],[5,3],[0,2],[2,0],[0,2],[5,6,7],[8,4,9],[2,0],[0,2]]),
([w166,w0,w1,w3,w84],[78,30,61,86,95,62,87],[28],[[0,1,2],[1,3],[0,2,4],[100],[2,0,4],[3,5],[0,4],[4,0],[6,2],[0,3]]),
([w310,w0,w1,w2,w30],[86,0,95,59,78,87,61,94,62,79],[],[[0,1],[2,0],[3,0,4],[3,2,4],[2,4],[4,2],[0,2,3],[5,3,6],[5,0,7],[8,0,9]]),
([w50,w0,w1,w3,w129],[78,95,87,61,59,79,94],[],[[0,1],[2,3],[0,1],[4,3],[1,0],[5,2,6],[0,1],[1,0],[2,4,6],[0,1]]),
([w50,w0,w1,w138,w30],[78,94,87,61,95,79],[],[[0,1],[2,3],[0,4],[5,1],[1,0],[5,1],[0,4],[4,0],[1,5],[0,1,4]]),
([w52,w0,w1,w168,w30],[79,94,95,61,86,59,81],[],[[0,1],[2,3,4],[5,2,6],[0,1],[1,0],[0,1],[3,2,5],[6,3,5],[1,0],[0,1]]),
([w52,w0,w1,w2,w170],[86,94,79,95,59,81],[],[[0,1,2],[3,0],[4,0,5],[2,1],[1,2],[2,1],[0,3,4],[5,4],[1,0],[2,0]]),
([w171,w31,w4,w2,w3],[94,73,71,95,79,59,81,62],[17],[[0,1,2],[1,3],[4,0],[4,0],[100],[4,5,6],[3,7],[0,5],[0,7],[5,3,6]]),
([w311,w0,w1,w2,w30],[86,0,17,16,87,94,95,61,93,81,62],[22],[[0,1],[2,0,3],[4,0],[4,5,6],[5,100,7],[8,5,9],[0,6,9],[9,7,8],[5,0],[10,0,8]]),
([w93,w0,w1,w173,w30],[69,99,81,87,10,94,79,61,62],[],[[0],[1],[2,0,3],[2,4,3],[5,6],[6,2,5],[7,2],[2,7,8],[2,6],[6,5]]),
([w93,w0,w1,w2,w175],[69,99,81,87,10,53,82,94,93,65],[],[[0],[1],[2,0,3],[2,4,3],[5,6,7],[8,2],[6,2,8],[2,5,6],[2,8],[6,5,9]]),
([w171,w0,w1,w168,w3],[61,380,261,94,344,124,62,65,79,81,381,93],[],[[0,1,2],[3,4,5],[6,0,7],[8,0],[0,8,3],[8,3],[8,3],[9,0,6],[10,0,11],[6,7]]),
([w169,w0,w1,w3,w170],[93,340,111,81,62,82,382,94,383,79],[],[[0,1,2],[3,0],[4,1,5],[4,0,5],[6,5,7],[0,6,5],[5,3,6],[8,0,6],[3,6,9],[9,0,3]]),
([w169,w171,w0,w1,w3],[79,65,94,81,62,82,61,384,93],[],[[0,1,2],[0,2],[3,4],[4,1],[5,3,6],[2,0],[0,2],[2,0],[0,2],[7,6,8]]),
([w312,w0,w1,w3,w30],[93,0,81,82,382,94,95,79],[],[[0,1],[2,0],[3,2],[3,0],[4,3,5],[0,4,3],[3,2,4],[6,0],[2,4,7],[7,0,2]]),
([w183,w0,w1,w2,w30],[98,65,110,82,95,81,79],[],[[0,1],[2,1],[3,4,5],[6,0,5],[1,3,4],[6,4],[3,1],[5,3],[5,1,6],[3,1]]),
([w171,w0,w1,w2,w3],[98,65,110,82,94,79,81,192],[],[[0,1],[2,1],[3,4,5],[5,0],[1,3,4],[5,4],[3,1],[6,3],[7],[3,1]]),
([w313,w0,w1,w2,w30],[65,98,110,81,95,82,62,79,61,88],[],[[0,1],[0,2],[3,4,5],[3,0,6],[0,7,4],[7,3,4],[8,0,3],[3,8,9],[3,0,7],[7,0,8]]),
([w93,w0,w1,w2,w130],[98,110,82,6,87,65,88,79,53,81],[],[[0],[1],[2,3,4],[4,0],[5,2,6],[7,8],[2,5],[6,2,8],[9,5,7],[2,5]]),
([w314,w0,w1,w2,w30],[65,98,110,81,6,87,82,95,93,91],[],[[0,1],[0,2],[3,4,5],[3,0,5],[0,6,7],[8,3],[6,0],[3,6],[3,0,9],[6,0]]),
([w93,w0,w1,w153,w30],[69,99,82,87,10,65,95,79,16,53,81],[],[[0],[1],[2,0,3],[3,4],[5,2,6],[7,8,9],[2,5],[6,2],[10,5,7],[2,5]]),
([w31,w37,w1,w173,w30],[79,385,6,81,10,59,65,61,95],[],[[0,1,2],[1],[0,2],[3,4,5],[6,1,7,8],[5,3],[0,3],[3,5],[3,0],[0,6,7]]),
([w31,w37,w1,w2,w175],[82,386,10,81,6,59,53,61,95,65],[],[[0,1,2],[1],[3,4,5],[0,2],[6,1,7,8],[0,3],[5,3],[3,0],[3,5],[0,6,9]]),
([w31,w0,w43,w173,w30],[69,53,99,387,82,81,10,59,87,61,93,65,91],[],[[0],[1,2],[3,0,4],[5,6,7],[1,8,9],[10,1,3],[9,5],[5,1,8],[5,11,8],[12,1,10]]),
([w31,w0,w43,w2,w175],[82,65,110,81,59,87,61,90,91],[],[[0],[1,2],[3,4],[3,1,4],[1,5,6],[7,3],[6,1,3],[3,6,5],[3,1,5],[8,1]]),
([w31,w4,w173,w3,w30],[14,59,15,79,385],[19],[[100],[0,1,2],[3,4],[4],[4],[4],[4],[1,4],[3,4],[1,4]]),
([w174,w31,w4,w3,w30],[15,59,14,61,379,82,95,62],[57],[[0,1,2],[3,0],[1,4],[3,4,5],[100],[6,4,7],[3,1],[3,7],[1,4],[1,3]]),
([w31,w4,w2,w3,w175],[87,59,81,82,386],[17],[[100],[0,1,2],[3,4],[0,1,2],[4],[4],[4],[0,2,1],[3,4],[0,2,1]]),
([w176,w31,w4,w2,w3],[19,59,18,65,379,61,62,81,95],[19],[[0,1,2],[3,0],[4,5,6],[1,5],[100],[7,1],[8,4,6],[1,5],[3,6],[1,4]]),
([w315,w0,w1,w2,w3],[61,0,81,10,59,82,87,79,90,94,91],[],[[0,1],[2,3],[4,0],[4,0],[0,5,6],[7,2,8],[5,6,9],[2,0,5],[10,0],[5,2]]),
([w178,w0,w1,w2,w88],[98,65,38,59,94,97,82,79,91],[42],[[0,1],[2,0],[3,4,5],[100],[1,6,4],[7,3,4],[6,1],[5,3],[8,1],[6,1]]),
([w316,w0,w1,w3,w30],[79,0,94,87,82,81,90,91,61],[],[[0,1,2],[3,4,5],[3,5,4],[0,2],[2,0],[0,2],[4,5,6],[7,8],[2,0],[0,2]]),
([w52,w0,w1,w2,w132],[82,94,87,61,91,95,97,79],[],[[0,1],[2,3,4],[0,5,6],[7,1],[1,0],[7,1],[0,5],[6,0],[1,7],[0,1,6]]),
([w52,w0,w1,w148,w30],[82,97,87,61,91,79,95,94],[],[[0,1],[2,3,4],[0,1],[5,3],[1,0],[5,4,6],[0,1],[1,0],[4,5,7],[0,1]]),
([w98,w0,w1,w180,w3],[82,95,87,90,94,97,71,61,91],[],[[0,1],[2,3,4],[0,4,5],[2,1],[1,0],[3,1,6],[0,2,4],[2,0,5],[1,7,8],[0,1,2]]),
([w181,w31,w4,w3,w30],[87,56,97,95,91,62,46,94],[17],[[0,1,2],[1,3],[0,2,3],[4,2],[100],[3,5],[0,6,7],[0,2],[2,6],[0,3]]),
([w98,w0,w1,w2,w182],[61,95,82,87,90,94,97,91],[],[[0,1,2],[3,4,5],[2,0,6],[3,0,1],[0,2,1],[4,1,7],[2,3,5],[3,0],[1,0,7],[2,1,3]]),
([w31,w4,w2,w182,w30],[87,62,97,95,321,90],[17],[[100],[0,1,2],[3,1],[0,4],[1,3],[0,2],[2,5],[0,2,3],[1,2],[0,3]]),
([w317,w0,w1,w2,w3],[90,0,19,18,79,94,61,62,93,97,95,59],[29],[[0,1],[2,0,3],[4,5],[4,0],[5,100,6],[0,5,7],[8,5,7],[9,0],[10,6,7],[11,0]]),
([w95,w0,w1,w184,w3],[98,110,94,7,79,87,61,18,93,95],[],[[0],[1],[2,3,4],[4,0],[2,5,6],[6,7],[8,2,5],[2,8],[9,6,8],[5,2,9]]),
([w95,w0,w1,w2,w186],[98,110,93,7,79,65,91,61,18,97],[],[[0],[1],[2,3,4],[2,0,4],[5,6,7],[2,6],[2,5,8],[9,2],[6,2,5],[6,5]]),
([w183,w0,w1,w180,w30],[93,94,87,95,61,79,82,90],[],[[0,1,2],[3,0],[2,3],[2,0],[1,2,4],[0,1,5],[4,3,6],[2,0,4],[1,7],[6,0]]),
([w181,w0,w1,w182,w30],[93,94,111,87,61,95,82,90],[],[[0,1,2],[3,0,4],[3,2,5],[6,0],[1,3,4],[0,1,3],[4,5,6],[5,0],[1,7],[3,0]]),
([w181,w183,w0,w1,w30],[82,95,90,79,87,61,94,93],[],[[0,1,2],[2,1,3],[4,0,5],[0,5,3],[0,4,6],[1,5,7],[3,1,2],[1,0],[0,1],[4,2,6]]),
([w318,w0,w1,w2,w3],[90,0,94,93,79,87,61,78,95],[],[[0,1],[2,0],[3,0,4],[3,0,4],[2,5,6],[3,2,7],[3,2,5],[5,3,6],[8,3],[5,8]]),
([w95,w0,w1,w2,w139],[98,110,93,7,79,94,87,61,78],[],[[0],[1],[2,3,4],[2,0,4],[5,6,7],[2,5,8],[2,6],[6,2,7],[5,2],[6,5]]),
([w319,w0,w1,w2,w3],[61,0,94,10,93,79,82,91,97],[],[[0,1],[2,3],[4,0,5],[4,0,5],[0,6,2],[4,2,7],[4,2,6],[8,0,4],[7,0],[6,8]]),
([w95,w0,w1,w149,w3],[98,110,94,7,79,82,93,18,91,65],[],[[0],[1],[2,3,4],[4,0],[2,5],[6,7],[5,2],[2,5],[8,6,9],[5,2]]),
([w31,w79,w1,w184,w3],[94,388,98,14,82,15,93,62,79,95,65],[],[[0,1,2],[1],[3,4,5],[6,2,7],[0,1,8],[4,0,8],[6,0,8],[3,4,5],[9,6],[4,9,10]]),
([w31,w79,w1,w2,w186],[65,98,110,93,62,389,79,94,97,16,82],[],[[0,1],[2],[3,4],[3,0,4],[0,5,6,7],[3,7,6],[3,0,6],[8,3],[9,0,3],[10,0]]),
([w31,w0,w81,w184,w3],[79,65,110,390,62,391,93,59,61],[],[[0],[1,2],[3,4,5],[6,1,4],[1,7,8],[6,3],[6,1,4],[4,6],[4,1,6],[7,1]]),
([w31,w0,w81,w2,w186],[79,65,110,93,62,59,61],[],[[0],[1,2],[3,4],[3,1,4],[1,5,6],[3,4],[3,1,4],[4,3],[4,1,3],[5,1]]),
([w31,w4,w184,w3,w30],[14,62,15,93,78,388],[19],[[100],[0,1,2],[3,1],[4,5],[5],[5],[5],[4,5],[1,3],[1,3]]),
([w185,w31,w4,w3,w30],[15,62,14,61,59,379,93],[57],[[0,1,2],[3,0],[4,5],[1,5],[100],[6,1],[3,4],[1,3],[4,5],[1,3,4]]),
([w31,w4,w2,w186,w30],[93,59,321,62,82,95,65,379],[17],[[100],[0,1],[0,2,3],[4,1,2],[0,5],[0,6],[1,5],[1,5,7],[3,0],[1,0,3]]),
([w187,w31,w4,w2,w30],[17,62,16,65,379,59,95,93,61],[58],[[0,1,2],[3,0],[4,5],[1,5,6],[100],[7,1],[8,4,5],[1,6],[3,5],[1,4]]),
([w320,w0,w1,w2,w30],[93,0,95,59,62,82,97,91,76],[],[[0,1],[2,0],[3,2,4],[3,0,4],[2,5],[0,2,3],[5,2],[6,0],[7,3,8],[5,0]]),
([w321,w0,w1,w3,w30],[93,0,97,62,82,95,91,59,76,78],[],[[0,1],[2,0],[3,2],[3,0],[2,4],[0,2,4],[4,2],[5,0],[6,7,8],[7,0,9]]),
([w98,w0,w1,w2,w142],[82,95,91,76,97,59,78],[],[[0,1],[2,3],[0,4],[5,1],[1,0],[6,1],[0,4],[4,0],[1,5],[0,1,4]]),
([w98,w0,w1,w152,w3],[78,95,91,76,97,82],[],[[0,1],[2,3],[2,4],[0,1],[1,0],[0,1],[3,4,5],[4,3,5],[1,0],[0,1]]),
([w31,w99,w40,w3,w30],[266,6,78,76,82,59,61,1,97,162],[48],[[0,1,2],[2,1],[3,1,4],[2,5,6],[0,7,8],[9],[5,8,100],[2,6,4],[4,3],[2,3]]),
([w31,w99,w43,w2,w30],[272,6,82,78,59,61,1,97,196,76,93],[51],[[0,1,2],[2,1],[3,1],[2,4,5],[0,6,7],[8],[4,7,100],[2,5,3],[3,9],[2,5,10]]),
([w58,w31,w40,w3,w30],[82,66,97,23,125,59,61,6,392],[],[[0,1,2],[0,3,2],[4],[5,2,6],[6,5],[0,7],[0,5,6],[0,6],[0,8],[5,6]]),
([w31,w100,w40,w3,w30],[267,1,97,269,166,82,83,253,76,157,255,78],[47],[[0,1,2],[3,4],[5,6],[5,7],[0,1,2],[8,2,100],[9],[5,10],[5,8],[11,8]]),
([w31,w100,w81,w2,w3],[275,1,97,274,231,252,393,78,82,233,394,93,76],[51],[[0,1,2],[3,4],[5,6,7],[8,6],[0,1,2],[9],[7,2,100],[8,10,11],[7,10,11],[7,12]]),
([w101,w31,w40,w3,w30],[6,72,75,53,0,31,34,14,78,76,127,261,82,253,392],[],[[0,1,2,3],[4,5,6,7],[8,3,9],[10],[8,6,9],[9,11,12],[8,13],[8,14,12],[12,9],[8,9]]),
([w222,w101,w31,w2,w3],[1,371,97,296,82,395,78,95,72,71,76,396],[48],[[0,1,2],[3],[4,5,100],[6,5,7],[2,8,4],[4,2,9],[6,2,10],[6,11],[4,11],[4,7,6]]),
([w31,w34,w111,w3,w30],[266,6,69,272,91,253,76,53,254,298,59],[50],[[0,1,2],[0,1],[3,1,4],[4,5],[0,6],[4,7],[4,8],[9],[10,6,100],[10,7]]),
([w112,w31,w34,w3,w30],[6,67,53,1,22,26,105,59,255,94,91,397],[],[[0,1,2],[3,4,5,2],[6],[7,8,9],[2,7],[10,0],[9,7],[7,2],[10,11],[7,2]]),
([w31,w34,w113,w3,w30],[267,92,29,76,91,253,254,78,53,299],[49],[[0,1,2],[0,3],[3,1,4],[4,5],[0,3],[3,6,4],[4,6],[7,8,100],[9],[7,3]]),
([w114,w31,w34,w3,w30],[6,73,71,53,1,30,34,5,78,95,107,35,124,91,398,397],[],[[0,1,2,3],[4,5,6,7],[8,3,9],[10],[8,11,9],[9,12,13],[8,14],[8,15,13],[13,9],[8,9]]),
([w31,w223,w2,w3,w30],[53,56,44,399,300,79,94,259,257,65,90,95],[],[[0,1,2],[3,4,5],[5,4],[6,7,8],[1,0],[3,0],[5,9,10],[10,11],[5,6],[5,6]]),
([w31,w34,w43,w46,w30],[400,160,271,194,272,6,91,102,78,196,65,53,76,79],[],[[0,1],[2,3],[4,5,6],[6,7],[6,8],[2,9],[6,10],[0,11],[8,12],[13,11]]),
([w31,w225,w2,w3,w30],[65,56,44,78,301,76,257,259,93,1,94],[],[[0,1,2],[3,4],[5,6,7],[3,4],[1,5],[3,0,8],[9,0],[3,5],[8,10],[3,5]]),
([w31,w34,w81,w83,w3],[258,165,274,231,275,7,78,76,102,91,233,65,53,79],[],[[0,1],[2,3],[4,5,6],[7,8,9],[7,9],[2,10],[6,11,9],[0,7],[6,12,13],[6,7]]),
([w31,w34,w78,w3,w30],[106,163,401,0,6,79,94,253,257,76,402,254,82,105],[],[[0,1],[2,3,4],[5,4],[6,7,8],[0,6],[9,6,10],[5,11,12],[13,0],[6,5],[5,6]]),
([w31,w34,w1,w133,w3],[53,69,99,94,7,257,76,79,82,65,95,78],[],[[0,1],[2],[3,4,5],[6,0,7],[0,8,3],[7,9,8],[6,0,8],[3,6,7],[10,0,11],[7,0]]),
([w31,w34,w141,w3,w30],[53,69,0,76,259,78,35,95,82,107,299],[],[[0,1],[0,2],[3,0,4],[5,4],[0,6,7],[3,0,8],[8,7],[7,0,5],[9,10],[5,0,3]]),
([w31,w34,w1,w143,w30],[53,69,99,76,259,78,82,95,94,79],[],[[0,1],[2],[3,0,4],[5,4],[0,6,7],[3,0,6],[6,7],[7,0,5],[8,3,9],[5,0,3]]),
([w42,w64,w31,w3,w30],[82,76,95,311,78,53,79,94,69,259],[47],[[0,1,2],[3],[4,5,100],[6,1,7],[2,8],[0,1,2],[0,2],[0,5],[0,9],[4,1]]),
([w64,w31,w43,w2,w30],[6,69,53,0,76,24,131,79,95,61,259,78],[],[[0,1,2],[3,4,5],[6],[7,8,9],[2,5],[7,0],[9,10,11],[11,2],[7,4,11],[7,2]]),
([w31,w103,w43,w2,w30],[403,1,95,273,198,79,83,78,259,82,199,76,61],[47],[[0,1,2],[3,4],[5,6],[7,8],[0,1,2],[9,2,100],[10],[7,11],[5,11,7],[5,12]]),
([w31,w103,w81,w2,w3],[270,1,95,276,235,78,393,76,259,82,237,79,394],[48],[[0,1,2],[3,4],[5,6],[7,6,8],[0,1,2],[9,2,100],[10],[9,7,11],[5,12,11],[5,7]]),
([w104,w31,w43,w2,w30],[6,259,261,0,76,42,82,53,93,133,78],[],[[0,1,2],[3,4,5],[6,7,8],[9],[1,2],[1,2],[6,1],[6,4,10],[10,4],[6,8]]),
([w222,w104,w31,w2,w3],[79,371,95,316,82,395,97,78,259,396],[51],[[0,1,2],[3],[4,5,6],[7,5,100],[2,8,4],[0,2],[0,2],[0,9],[0,9],[4,6]]),
([w31,w238,w2,w3,w30],[53,67,63,146,300,259,61,257,1,79,76,81],[],[[0,1,2],[3,4,5],[5,4],[6,5,7],[8,0],[1,0],[9,10,11],[10,11],[9,6],[9,6]]),
([w31,w37,w111,w2,w30],[272,6,69,266,259,61,82,53,78,81,319,76,79],[52],[[0,1,2],[0,1],[3,1,4],[5,4,6],[0,5],[6,7,8],[5,9],[10],[9,11,100],[6,5,12]]),
([w31,w37,w40,w46,w30],[259,6,61,82,78,14,162,81,76,79],[],[[0,1],[0,1],[0,1],[2,0,3],[2,4],[4,5,6],[2,7],[3,2],[3,8],[9,2]]),
([w117,w31,w37,w2,w30],[259,56,53,78,22,81,79,76,94,257,95],[],[[0,1,2],[3,4,2],[5],[6,7,8],[0,2],[0,2],[8,0,9],[3,2],[3,10],[6,2]]),
([w31,w37,w118,w2,w30],[403,78,92,76,79,270,259,257,95,81,320,94],[49],[[0,1,2],[0,3],[4,2],[5,6,7],[0,3],[1,8],[1,8],[9,3,100],[10],[4,11]]),
([w119,w31,w37,w2,w30],[257,73,76,38,42,82,97,79,124,259,95,78],[],[[0,1,2],[2,3,4],[5,2,6],[7],[5,0],[0,8],[0,9],[5,10,11],[11,6],[5,6]]),
([w31,w240,w2,w3,w30],[95,67,63,257,123,76,259,82,81,1,97],[],[[0,1,2],[3,4],[5,3,6],[3,4],[7,0,8],[1,0],[9,0],[7,4,8],[7,10],[4,8]]),
([w31,w37,w81,w2,w87],[259,78,97,276,92,10,76,81,82,79,53],[],[[0,1,2],[3,0],[0,4],[0,5],[1,6],[1,7,8],[1,2],[2,6,9],[7,10,9],[8,2]]),
([w31,w37,w76,w2,w30],[259,6,53,0,81,46,97,79,319],[],[[0,1],[2,3],[0,1],[4,0,5],[2,5,6],[5,2],[7,4],[4,2,8],[4,5],[5,2]]),
([w31,w37,w1,w2,w130],[259,6,99,81,82,53,78,97,79],[],[[0,1],[2],[0,1],[3,0,4],[5,6,7],[4,3],[6,3,7],[3,4],[3,8],[4,5,7]]),
([w31,w37,w151,w2,w30],[53,69,0,81,259,82,78,97,73,320],[],[[0,1],[0,2],[3,0,4],[3,4,5],[0,6,7],[5,0,3],[6,3,7],[3,0,5],[3,8,9],[5,0,7]]),
([w31,w37,w1,w153,w30],[259,78,97,99,81,82,79],[],[[0,1,2],[3],[0,3],[4,0,5],[2,1],[1,4,5],[1,2],[2,5],[4,6],[5,2]]),
([w42,w107,w31,w3,w30],[82,97,331,78,404,95,79,109,405],[48],[[0,1],[2],[3,4,5],[6,4,100],[1,7,3],[0,1],[0,1],[0,8],[0,8],[3,5]]),
([w107,w31,w81,w2,w3],[97,109,60,31,32,135,78,76,393,79,406],[],[[0,1,2],[0,3,4],[5],[6,0,7],[6,4,7],[6,8],[7,8,9],[9,7],[6,10,9],[6,7]]),
([w45,w108,w31,w2,w30],[1,97,211,82,79,76,66,53,78,83,10],[51],[[0,1],[2],[3,1],[4,5,100],[1,6,3],[3,7,8],[4,1,8],[1,9,4],[3,10],[3,1]]),
([w108,w31,w81,w2,w3],[97,66,70,39,40,82,407,90,137,393,79,406],[],[[0,1,2],[0,3,4],[5,6,7],[8],[5,4,7],[0,9,10],[5,9],[0,11,10],[10,7],[5,0]]),
([w31,w251,w2,w3,w30],[53,73,71,147,123,78,76,257,259,1,97,61],[],[[0,1,2],[3,4,5],[6,7,8],[5,4],[9,0],[5,0,4],[1,3,6],[5,4],[10,11],[5,4]]),
([w31,w79,w113,w2,w3],[275,29,230,76,267,393,78,259,295,407,79,334,394],[52],[[0,1,2],[0,3],[4,5,6],[3,5,7],[0,3],[8,9,10],[3,9,10],[11],[6,12,100],[6,3]]),
([w31,w79,w40,w83,w3],[355,230,269,166,267,7,78,259,83,295,76,79,157,53,61,82],[],[[0,1],[2,3],[4,5,6],[7,8],[9,10,11],[2,12],[6,13,11],[0,10],[6,14,15],[6,10]]),
([w31,w253,w2,w3,w30],[53,73,71,259,121,408,82,90,41,97,95],[],[[0,1,2],[3,4],[3,4],[5,3,6],[6,0,7],[5,0],[1,4,8],[6,7],[6,4,9],[4,10]]),
([w31,w79,w118,w2,w3],[270,37,336,61,259,393,82,407,79,335,97],[50],[[0,1,2],[0,3],[4,5],[4,5],[0,3],[6,7,8],[8,7],[6,3,100],[9],[6,10]]),
([w31,w79,w43,w2,w87],[357,336,273,198,97,83,259,10,61,82,53,79,90,335],[],[[0,1],[2,3],[4,5,6],[6,7],[4,8],[9,10,11],[2,4],[4,8,12],[0,13],[9,4]]),
([w122,w31,w79,w2,w3],[90,56,44,30,32,97,78,95,79,409,259,410],[],[[0,1,2],[0,3,4],[5],[6,0,7],[6,8,7],[6,9],[7,9,10],[8,7],[6,11,8],[6,7]]),
([w123,w31,w79,w2,w3],[259,67,411,79,38,412,82,394,97,95,409,410],[],[[0,1,2],[3,4,5],[6,7,8],[9],[6,0],[0,10],[0,10],[3,11],[3,8],[6,8]]),
([w31,w79,w137,w2,w3],[413,79,97,411,0,259,393,78,95,46,56,334],[],[[0,1,2],[3,4,5],[2,6,7],[8,6,9],[2,1],[1,8],[1,2],[2,10,11],[8,7],[7,2,8]]),
([w31,w79,w1,w2,w139],[97,79,110,83,78,95,82],[],[[0,1],[2],[0,3,4],[5,2,6],[0,1],[1,5],[1,0],[0,6],[5,4],[4,0,5]]),
([w31,w79,w147,w2,w3],[413,79,95,411,0,82,97,393,257,67,335],[],[[0,1,2],[3,4,5],[6,7,8],[2,7,5],[2,1],[1,2],[1,6],[6,5],[2,9,10],[5,2,6]]),
([w31,w79,w1,w149,w3],[95,79,110,97,7,78,82],[],[[0,1],[2],[3,4,5],[0,2,6],[0,1],[1,0],[1,3],[3,6],[0,5],[5,0]]),
([w112,w39,w31,w2,w30],[0,95,61,67,63,82,97,79,65,81,69,85],[49],[[0,1,2],[2,3,4],[5,2,6],[7,8,9],[10],[5,1,100],[7,1,2],[6,10,7],[2,11,5],[5,2,6]]),
([w31,w131,w40,w3,w30],[97,6,69,126,95,259,81,257,61,125,59,255,91],[],[[0,1,2],[3,1],[4,1,5],[6,5,7],[0,3,8],[9,3],[8,0,10],[4,8,10],[6,11,12],[10,4,6]]),
([w31,w0,w40,w133,w3],[69,53,99,97,259,257,91,61,14,76,62],[],[[0],[1,2],[3,4,5],[4,0],[1,6,7],[7,8],[9,1,10],[3,9,6],[6,1],[10,1,9]]),
([w31,w140,w40,w3,w30],[97,6,69,128,259,61,257,76,62,91],[],[[0,1,2],[3,1],[4,1],[5,4,6],[0,3,5],[7,0,8],[5,0,3],[9,5],[8,7],[8,5,7]]),
([w31,w0,w40,w143,w30],[69,61,99,97,62,259,257,76,59],[],[[0],[1,0,2],[3,0,4],[1,5,6],[1,4],[7,4],[1,3,8],[3,1,8],[4,7],[4,1,3]]),
([w117,w36,w31,w3,w30],[0,53,76,56,62,69,78,59,97,61,179],[49],[[0,1,2],[1,3],[4,1],[4,2],[5],[6,1,100],[7,8,9],[10],[6,7,9],[6,1,7]]),
([w119,w267,w31,w2,w3],[0,371,61,73,71,62,97,59,98,414,96,192],[52],[[0,1,2],[2,3,4],[5,2,6],[5,2,7],[8],[5,9,10],[5,6,100],[6,5],[11],[7,6]]),
([w31,w128,w43,w2,w30],[53,69,24,97,259,61,46,131,196,81,65,90],[],[[0,1],[0,2],[3,0,4],[5,4,6],[0,2,5],[7,8],[5,3,6],[3,0,6],[9,10,11],[6,0]]),
([w31,w0,w43,w2,w130],[69,53,99,97,259,61,59,62,90],[],[[0],[1,2],[3,0,4],[5,4,6],[1,7,5],[8,1,7],[5,3,6],[3,1,8],[6,8],[6,1]]),
([w31,w150,w43,w2,w30],[53,69,42,90,62,259,91,61,16,199,65],[],[[0,1],[0,2],[3,0,4],[3,5,6],[0,2,7],[3,0,4],[3,8,9],[6,0,3],[4,3,10],[4,0,10]]),
([w31,w0,w43,w153,w30],[69,53,99,259,61,91,62,90,65,81],[],[[0],[1,2],[3,0],[4,3,5],[1,6,4],[7,1,5],[4,8,9],[5,1,7],[6,7,8],[5,1,8]]),
([w122,w36,w31,w3,w30],[0,61,56,44,91,55,62,415,76,81],[50],[[0,1],[1,2,3],[4,1],[4,1],[5],[6,7,8],[9,7,100],[4,6,8],[4,5],[6,8]]),
([w31,w136,w81,w2,w3],[65,98,32,90,393,257,76,46,18,233,95,93],[],[[0,1],[0,2],[3,4,5],[6,0,7],[0,2,3],[3,8,9],[6,0,7],[7,6],[10,0,11],[7,0,6]]),
([w31,w0,w81,w2,w139],[98,65,110,257,92,76,46,93,95,91],[],[[0],[1,2],[3,4],[5,0,6],[1,6,5],[7,8,9],[5,1,6],[6,5],[8,1,7],[6,1,5]]),
([w31,w146,w81,w2,w3],[65,98,40,93,393,257,91,61,237,95],[],[[0,1],[0,2],[3,4,5],[3,0,6],[0,2,7],[3,6],[3,0,8],[6,3],[9,0,3],[6,0]]),
([w31,w0,w81,w149,w3],[98,65,110,257,62,93,91,46,61,95],[],[[0],[1,2],[3,4,5],[5,0,6],[1,7,8],[5,4],[5,1,7],[4,5],[9,1,5],[4,1]]),
([w190,w0,w1,w46,w30],[98,110,95,6,91,79,53,61,46,93,81],[],[[0],[1],[2,3,4],[4,0],[2,5],[5,6],[7,2,8],[2,6,9],[10,5],[5,2,6]]),
([w31,w126,w1,w46,w30],[65,98,416,93,6,79,61,46,95,81],[],[[0,1],[2],[3,4,5],[6,0,7],[0,7,8],[2,3],[5,0,9],[8,3],[9,0,5],[5,0,6]]),
([w31,w0,w127,w46,w30],[98,65,20,95,6,259,61,46,76,53,81,91],[],[[0],[1,2],[3,4,5],[6,0,7],[1,2,6],[8,9,10],[6,1,7],[3,6,7],[10,1,11],[7,1,6]]),
([w322,w0,w1,w2,w3],[61,0,81,73,71,91,46,259,95,65],[],[[0,1],[2,3,4],[5,0,6],[6,0],[0,5],[7,2,8],[7,9],[2,0,7],[5,0],[5,2]]),
([w31,w4,w2,w3,w129],[81,300,79,46,95,53,30,34],[17],[[100],[0,1,2],[2,1],[0,3],[0,4],[3,5],[0,4],[3,0,4],[2,6,7],[2,0]]),
([w31,w4,w2,w3,w130],[81,300,79,46,53,65,91,30],[17],[[100],[0,1,2],[2,1],[0,3],[0,4],[3,4],[0,5],[3,0,6],[2,7,6],[2,0]]),
([w31,w4,w2,w3,w132],[79,300,91,321,53,93,65,379,42],[17],[[100],[0,1],[0,1],[2,3],[2,4],[4,5],[0,6],[2,7],[0,5,2],[0,5,8]]),
([w31,w4,w2,w133,w3],[79,300,91,46,81,53,95,62,78],[17],[[100],[0,1],[2,3,4],[0,1],[2,5],[0,6],[5,7],[0,4],[2,6,8],[0,4]]),
([w196,w0,w1,w83,w3],[69,99,91,7,53,78,95,93,46,81],[],[[0],[1],[2,3],[2,0],[4,5,6],[5,6],[7,4,8],[9,7],[6,4,5],[5,4,6]]),
([w31,w134,w1,w83,w3],[95,46,417,93,7,78,53,79,97],[],[[0,1],[2],[3,4,5],[0,1],[0,1],[1,0],[3,6,7],[8,3],[0,1],[1,0]]),
([w31,w0,w135,w83,w3],[69,53,28,93,7,257,46,61,95,81],[],[[0],[1,2],[3,4,5],[3,0,6],[1,2,7],[3,8,9],[3,1,6],[6,3,9],[8,1,3],[6,1,8]]),
([w323,w0,w1,w2,w30],[69,53,99,46,95,79,61,81,93],[],[[0,1],[2,1],[3,0],[3,4],[1,5,4],[5,1],[6,4,7],[7,1,8],[7,5],[5,1]]),
([w31,w4,w2,w138,w30],[93,300,79,81,46,95,53,378],[17],[[100],[0,1,2],[0,1,2],[3,4],[0,5],[0,6],[2,5],[4,3,5],[2,0,7],[2,0,3]]),
([w31,w4,w2,w139,w30],[93,300,79,46,78,301,53,97,26,91],[17],[[100],[0,1,2],[0,3],[4,3,5],[0,6],[0,7],[2,7],[3,7,8],[2,0,9],[2,0,4]]),
([w31,w4,w2,w142,w30],[97,300,78,93,46,301,53,91,81],[17],[[100],[0,1,2],[3,1,4],[2,5],[6,7],[0,2],[0,8],[2,0,3],[7,0],[2,3]]),
([w31,w4,w143,w2,w30],[91,300,78,301,53,51,79,377,378],[17],[[100],[0,1],[2,1],[0,3],[2,4],[0,4],[5,6],[0,7,2],[2,7],[0,8,6]]),
([w202,w0,w1,w2,w87],[55,100,91,79,10,51,61,93,65,81],[],[[0],[1],[2,0,3],[3,4],[5,2,6],[7,2],[6,8,9],[9,5,7],[2,7,8],[2,5,8]]),
([w31,w144,w1,w2,w87],[51,55,418,81,62,10,82,97,65,93],[],[[0,1],[2],[3,0,4],[3,5,6],[0,4,7],[6,0,3],[2,7],[3,0,4],[3,8,9],[4,0,7]]),
([w31,w0,w145,w2,w87],[55,51,36,81,62,10,91,61,93,65],[],[[0],[1,2],[3,0,4],[3,5,6],[1,2,7],[8,1,3],[7,3],[3,1,8],[3,8],[4,1,9]]),
([w324,w0,w1,w3,w30],[93,0,81,91,382,61,79],[],[[0,1],[2,0],[3,2],[3,0],[4,3,5],[0,4,6],[5,2],[3,0,4],[2,4,3],[6,0,2]]),
([w31,w4,w148,w3,w30],[81,301,79,321,61,91,93,65],[17],[[100],[0,1,2],[2,3],[4,1,5],[0,4],[4,6],[2,7],[5,0],[2,0,4],[2,4]]),
([w31,w4,w149,w3,w30],[93,301,79,321,91,51,65,22,24,78],[17],[[100],[0,1,2],[0,3,2],[4,1],[0,5],[0,6],[2,5],[4,7,8],[2,0,4],[2,0,9]]),
([w31,w4,w152,w3,w30],[93,301,78,91,321,51,65,81,377],[17],[[100],[0,1,2],[3,4],[2,1],[0,5],[2,6],[5,7],[2,0,3],[3,0],[2,7,8]]),
([w31,w4,w153,w3,w30],[81,62,91,321,61,65,32,79],[17],[[100],[0,1],[2,1,3],[0,3,2],[0,4],[1,4],[0,5],[2,0],[1,4,6],[1,0,7]]),
([w56,w0,w1,w133,w3],[7,321,110,51,91,97,79,78,15,100,95],[],[[0,1,2],[3],[4,0],[4,1],[5,6],[7,8,9],[6,5],[5,6],[10,7],[6,5]]),
([w56,w0,w1,w143,w30],[7,91,51,78,343,95,79,15,93,94],[],[[0,1],[2],[1,3,4],[1,0],[5,3],[6,7,8],[3,5],[5,3],[9,6],[3,5]]),
([w325,w0,w2,w3,w30],[95,0,79,81,56,93,97,78,91],[],[[0,1,2],[3,4,5],[0,5],[3,2],[2,0],[2,6],[7,0],[7,0],[2,5,8],[2,0,3]]),
([w45,w58,w31,w2,w30],[93,97,288,419,79,94,62,420,91],[47],[[0,1],[2],[0,3,100],[4,3,5],[0,6],[6,1],[4,0,6],[0,7,4],[5,7,8],[4,0,5]]),
([w0,w1,w223,w46,w30],[91,79,7,300,78,46,259],[],[[0,1],[1,0,2],[1,3],[4,5,6],[3,4],[0,3],[0,1,6],[0,3],[0,2],[1,3]]),
([w0,w1,w225,w83,w3],[301,79,91,46,93,257,78],[],[[0,1,2],[0,2],[1,0],[1,3,4],[0,1],[2,0],[2,3,5],[1,0],[1,4,6],[3,0]]),
([w33,w34,w1,w143,w30],[301,51,0,93,78,97,62,91,99,100],[],[[0],[1],[2,3],[4,0],[5,6],[3,5,7],[6,5],[7,3,8],[7,9],[4,3]]),
([w62,w0,w1,w2,w130],[97,78,6,53,93,421,79,99,17,62,94],[],[[0,1,2],[3],[0,2,1],[1,4,5],[0,6],[6,7],[4,0,8],[0,7,9],[10,4],[6,0,4]]),
([w62,w0,w1,w153,w30],[6,300,99,53,78,7,94,79,82,97],[],[[0,1,2],[3],[4,0],[4,5],[6,7],[7,2],[8,9],[9,2,8],[6,7],[7,2]]),
([w0,w1,w238,w46,w30],[300,79,87,82,46,259,7],[],[[0,1,2],[0,1],[1,0],[3,4,5],[0,3],[2,0],[2,1,5],[2,0],[1,6,2],[1,0]]),
([w0,w1,w240,w2,w87],[79,91,6,36,93,81,7,280,321],[],[[0,1],[2,3],[0,1,4],[0,5,4],[1,0,6],[5,4],[1,4,5],[0,2],[0,4,7],[1,8]]),
([w33,w37,w1,w153,w30],[300,53,0,79,82,80,91,46,99,100,422],[],[[0],[1],[2,0,3],[4,5],[6,7,8],[4,8,7],[3,9,10],[10],[6,3,10],[3,8]]),
([w106,w0,w1,w2,w139],[7,79,51,344,366,97,82,93,100,78,81],[],[[0,1],[2],[1,0],[1,3,4],[5,6],[7,8,9],[6,5],[5,6],[10,7],[6,5]]),
([w106,w0,w1,w149,w3],[7,300,99,51,79,97,82,93,19,95],[],[[0,1,2],[3],[4,0],[4,1],[5,6],[7,8],[6,5],[5,6],[9,7],[6,5]]),
([w0,w1,w251,w83,w3],[82,87,7,28,301,257,88,6],[],[[0,1],[2,3],[0,4],[0,1,5],[1,0,2],[1,4],[6,5],[0,2],[0,7],[1,4]]),
([w0,w1,w253,w2,w87],[82,88,7,78,91,90,321,84],[],[[0,1],[0,1,2],[3,4,5],[0,6],[4,3,6],[1,0,7],[1,5,6],[0,2,1],[1,5,6],[0,6]]),
([w33,w79,w1,w2,w139],[301,51,78,0,93,91,79,100,99,88,110],[],[[0],[1],[2,0],[3,4],[5,6,7],[4,7,6],[2,8,6],[9,4,7],[5,2,10],[2,7]]),
([w110,w0,w1,w133,w3],[79,7,301,55,91,6,61,88,76,69,87],[],[[0],[1,2,3],[4,1],[4,5],[6,7],[6,3,7],[8,9,10],[10,3],[7,6],[7,3,6]]),
([w110,w0,w1,w143,w30],[79,6,300,69,91,88,7,61,93,14,87,55],[],[[0],[1,2,3],[4,1],[4,5,6],[7,5],[8,3,9],[7,5],[5,3],[10,11],[5,3]]),
([w326,w1,w2,w3,w30],[61,0,88,79,87,76],[],[[0,1,2],[3,1],[3,1],[0,1,2],[2,0],[2,0],[4,3,5],[4,5],[2,0],[2,0]]),
([w114,w267,w31,w2,w3],[0,51,61,73,88,55,91,87,76,396],[50],[[0,1,2],[1,3],[4,1],[4,2],[5],[6,1,100],[7,8],[4,1],[4,9],[6,1,7]]),
([w32,w0,w40,w133,w3],[51,301,79,87,76,6,88,91,61],[],[[0],[1],[2,0,3],[4,5,6],[2,7,4],[8,6],[2,3,4],[2,4,7],[3,8,7],[2,4,3]]),
([w32,w0,w40,w143,w30],[53,300,88,79,7,87,91,69,61,55],[],[[0],[1],[2,0],[3,4,5],[3,6,7],[3,5,7],[8,2],[5,7,6],[2,9,6],[2,7]]),
([w116,w0,w1,w2,w130],[79,6,300,69,87,423,424,61,88,90,91,98],[],[[0],[1,2,3],[4,1],[4,5,6],[7,8],[9,3,10],[7,8],[8,3],[10,9,11],[8,3]]),
([w116,w0,w1,w153,w30],[79,61,88,87,91,424,90,98],[],[[0],[1,2],[3,4,5],[1,2],[1,2],[6,4],[1,2],[2,1],[4,6,7],[2,1]]),
([w32,w0,w43,w2,w130],[65,321,88,89,91,79,87,98,90],[],[[0],[1],[2,3],[4,0],[5,6,7],[5,4,8],[8,2],[4,8],[2,7,6],[2,7,4]]),
([w32,w0,w43,w153,w30],[65,321,88,6,91,79,87,98,69,90],[],[[0],[1],[2,3],[4,0],[5,6,7],[5,4,8],[9,2],[4,8,6],[2,7,6],[2,7,4]]),
([w121,w0,w1,w2,w139],[65,91,98,88,6,61,93,18,87],[],[[0],[0,1,2],[3,1,4],[3,0],[5,1],[6,1],[5,2,7],[8,5],[1,2],[1,2]]),
([w121,w0,w1,w149,w3],[65,91,69,88,280,61,93,98,87,55],[],[[0],[0,1,2],[3,1,4],[3,0],[5,1],[5,1],[6,7,8],[8,6,9],[1,5],[1,5]]),
([w123,w39,w31,w2,w30],[0,65,93,67,53,87,98,91,425,96,88,420],[52],[[0,1,2],[1,3],[2,4,5],[5,1],[6],[7,8,9],[10,1,100],[2,11,5],[5,1],[7,1]]),
([w32,w0,w81,w2,w139],[51,301,87,91,10,61,88,93,426],[],[[0],[1],[2,0],[3,4],[5,6],[7,3],[7,2],[3,5,6],[2,5,6],[2,8,3]]),
([w32,w0,w81,w149,w3],[65,321,93,7,87,91,61,88,426],[],[[0],[1],[2,3,4],[2,0,5],[6,7],[2,5],[2,4],[5,2],[4,2],[4,8,5]]),
([w286,w0,w1,w46,w30],[7,20,51,93,6,91,97,79,99,90,81],[],[[0,1],[2],[1,3,4],[5,0],[6,7],[3,8,7],[9,6,10],[6,3],[10,7],[7,3,8]]),
([w287,w0,w1,w46,w30],[51,20,91,6,61,88,90,69,81],[],[[0],[0,1],[2,3],[2,0],[4,5],[6,7,8],[4,5],[5,4],[8,6],[5,4]]),
([w0,w1,w53,w3,w129],[301,79,88,300,90,81,87,123,34],[],[[0,1,2],[0,1],[1,3],[4,0,2],[0,2],[2,3],[5,0,1],[6,3,7],[1,0,8],[1,0,3]]),
([w0,w1,w54,w2,w129],[427,79,88,300,90,81,87],[],[[0,1,2],[1,3],[1,0],[4,0,2],[2,3],[2,0],[5,0,1],[6,0],[1,0,4],[1,3]]),
([w0,w1,w327,w2,w3],[87,79,90,0,81,321,88,30,34,301],[],[[0,1],[2,3],[1,4,2],[1,0,5],[0,1,4],[0,2,4],[6,5],[1,7,8],[0,2,1],[0,2,9]]),
([w0,w1,w53,w3,w130],[87,79,81,7,300,90,88,91,30],[],[[0,1],[1,2,3],[1,0,4],[5,2],[0,4],[6,4],[0,1,2],[0,2,7],[1,8,7],[0,2,1]]),
([w0,w1,w54,w2,w130],[87,79,424,91,90,0,300,81],[],[[0,1],[1,0,2],[1,3,4],[4,5],[3,6],[0,4,6],[0,1,7],[0,2],[0,2],[1,6]]),
([w0,w1,w328,w2,w3],[87,79,90,0,91,321,81,30],[],[[0,1],[2,3],[1,4,2],[1,0,5],[0,1,5],[0,2,6],[4,5],[1,7,4],[0,2,1],[0,2,4]]),
([w0,w1,w329,w2,w130],[61,91,65,98,90,16,81],[],[[0,1],[2,3],[4,1],[0,3,5],[1,0],[6,0,4],[1,3],[1,4],[6,0],[1,0,3]]),
([w0,w330,w1,w2,w130],[10,110,321,97,91,79,90,0,81],[],[[0,1,2],[3,4,5],[5,4,6],[6,1,7],[4,0,1],[4,3],[5,0,8],[3,6],[4,1],[4,1]]),
([w33,w37,w1,w2,w130],[321,65,81,90,91,78,110],[],[[0],[1],[2,3],[2,0,3],[4,5,6],[3,2],[3,2],[2,3],[2,3],[4,6]]),
([w0,w1,w53,w3,w132],[428,79,91,315,90,0,85,300,69],[],[[0,1,2],[1,2,3],[1,0],[4,0,5],[6,7,8],[2,0],[2,0],[2,0],[1,0,2],[1,4]]),
([w0,w1,w54,w2,w132],[300,79,91,90,0,88,321,112],[],[[0,1,2],[0,1],[1,0],[3,4],[0,2],[5,0],[2,1,6],[2,0,7],[1,3],[1,0]]),
([w0,w1,w331,w2,w3],[321,79,91,0,301,88],[],[[0,1,2],[0,3],[1,2,4],[1,0],[0,1],[5,4],[2,0],[1,4],[1,0],[2,0]]),
([w0,w1,w53,w133,w3],[91,79,315,90,0,300,69,301],[],[[0,1],[1,0,2],[3,4],[1,5],[5,6],[0,1,7],[0,5],[0,2],[0,2],[1,3]]),
([w0,w1,w332,w2,w3],[429,79,91,83,0,280,366,88,301,87],[],[[0,1,2],[3,4,5],[1,0],[1,0],[2,1,6],[7,0],[2,0],[1,0],[1,0],[2,8,9]]),
([w0,w1,w54,w2,w133],[300,79,87,90,0,69,81],[],[[0,1,2],[0,1],[1,0],[3,4],[0,5],[2,0],[2,1,6],[2,0],[1,3],[1,0]]),
([w0,w1,w333,w133,w3],[61,87,53,69,14,79,81,88,91],[],[[0,1],[2,3],[0,4],[5,1,3],[1,0],[1,5,6],[7,0],[5,0],[1,2,8],[1,0,5]]),
([w0,w334,w1,w133,w3],[6,99,300,95,79,90,0,53,81,91],[],[[0,1,2],[3,4],[5,3,6],[4,1],[7,1],[4,8],[9,0],[8,4],[3,1,9],[4,1]]),
([w33,w34,w1,w133,w3],[300,53,0,90,79,88,82,99,81],[],[[0],[1],[2,3],[4,0],[5,6,7],[3,8],[6,7],[8,3],[5,7],[4,3]]),
([w292,w0,w1,w83,w3],[6,28,53,90,81,79,95,78,93,99,84],[],[[0,1],[2],[1,3,4],[5,0],[6,7],[3,4],[8,9,10],[4,3],[6,7],[7,3,6]]),
([w293,w0,w1,w83,w3],[53,28,79,81,90,61,87,93,84,55],[],[[0],[0,1],[2,3,4],[2,0],[5,6],[4,3],[7,6],[3,4],[8,5,7],[6,3,9]]),
([w0,w1,w53,w138,w30],[79,87,81,90,93,84,26,121],[],[[0,1],[0,2,3],[0,1,4],[3,2],[1,3,2],[5,4],[1,0,2],[1,2,6],[0,4,7],[0,2]]),
([w0,w1,w335,w2,w30],[79,87,93,84,90,81,26,300],[],[[0,1],[0,1,2],[0,3,2],[4,5],[3,2],[1,2,3],[1,0,5],[1,4,6],[0,2,1],[0,2,7]]),
([w0,w1,w336,w2,w138],[429,79,87,83,81,280,84,93,26],[],[[0,1,2],[3,4,5],[1,0],[1,0],[2,1,4],[2,0],[6,0,7],[1,0],[1,0],[2,4,8]]),
([w0,w1,w53,w139,w30],[87,79,84,6,93,78,301,22,26,91],[],[[0,1],[1,2,3],[1,0,4],[5,6],[0,4,2],[2,4],[0,1,6],[0,7,8],[1,2,9],[0,2]]),
([w0,w1,w337,w2,w30],[427,79,91,0,280,78,366,84,93],[],[[0,1,2],[1,3,4],[1,0],[5,0],[2,5,6],[7,0,8],[2,0],[2,0,5],[1,0,5],[1,7,2]]),
([w0,w1,w336,w2,w139],[301,78,91,93,0,84],[],[[0,1,2],[0,1],[1,0],[3,4],[0,2],[5,0,3],[2,1,5],[2,0,3],[1,3],[1,0]]),
([w0,w1,w338,w2,w139],[76,91,51,55,93,18,84,78],[],[[0,1],[2,3],[4,1],[0,5],[1,0],[6,0,4],[1,4,6],[1,2,4],[6,0],[1,0,7]]),
([w0,w339,w1,w2,w139],[83,100,301,95,78,93,0,51,430],[],[[0,1,2],[3,4],[4,1],[5,6],[7,1],[5,0,8],[4,0,3],[8],[3,4],[4,1]]),
([w0,w1,w53,w142,w30],[300,78,91,93,0,301,69],[],[[0,1,2],[0,1],[3,0,4],[1,5],[0,6],[2,0],[2,5],[1,0,2],[2,5],[1,0,3]]),
([w0,w1,w340,w2,w30],[300,78,91,0,81,90,40,321],[],[[0,1,2],[0,3],[1,0],[1,4,5],[0,1],[4,0,5],[2,5,4],[1,0],[1,4,6],[2,0,7]]),
([w0,w1,w336,w2,w142],[429,78,91,301,93,0,81,90,112],[],[[0,1,2],[1,3],[1,0],[4,0,5],[2,3],[6,0,7],[2,0],[2,0,8],[1,0,4],[1,3]]),
([w0,w1,w341,w2,w30],[91,78,80,0,424,300,88,123,79,259],[],[[0,1],[2,3,4],[1,0,5],[1,6,7],[0,1,5],[6,5],[0,8,9],[0,2,1],[1,2],[0,5,6]]),
([w0,w1,w53,w143,w30],[91,78,7,79,0,300,301,55],[],[[0,1],[1,0,2],[3,4,5],[1,6],[2,5,7],[0,1,5],[0,3,6],[0,5],[0,2],[1,5,3]]),
([w0,w1,w336,w143,w2],[301,79,91,100,0,93,84,88,6,24],[],[[0,1,2],[0,3],[1,4,5],[1,0],[0,1],[2,5,6],[7,0],[1,5,8],[1,0],[2,0,9]]),
([w0,w1,w333,w143,w30],[76,79,88,7,55,14,78,69,87,91],[],[[0,1,2],[1,3,4],[0,5],[6,2,4],[2,0],[2,6,7],[8,0],[6,0],[1,3,9],[1,0,6]]),
([w0,w334,w1,w143,w30],[7,100,301,95,79,0,99,78,51,431],[],[[0,1,2],[3,4],[4,5,6],[7,1],[8,1],[7,3],[4,0,9],[3,6,7],[9],[4,1,6]]),
([w298,w0,w1,w2,w87],[7,36,51,78,93,95,112,82,84],[],[[0,1],[2],[3,0],[1,4,5],[5,6,7],[4,5,6],[4,8],[8,4],[5,4],[7,5,6]]),
([w299,w0,w1,w2,w87],[51,36,78,84,93,76,91,98],[],[[0],[0,1],[2,0],[2,3,4],[5,6],[4,3],[4,3],[3,4],[3,4],[6,5,7]]),
([w0,w1,w342,w3,w30],[301,79,91,84,93,82,22,24,300],[],[[0,1,2],[0,1],[1,3,4],[5,0],[0,4],[2,4,3],[2,0],[2,6,7],[1,0,2],[1,0,8]]),
([w0,w1,w54,w148,w30],[427,82,91,84,424,93,24,79,121],[],[[0,1,2],[1,3,4],[5,0,2],[1,0],[2,5,3],[3,0,1],[2,0],[1,0,6],[7,0,8],[1,3]]),
([w0,w1,w336,w148,w3],[301,79,91,100,84,93,6,24],[],[[0,1,2],[0,3],[1,0],[1,4,5],[0,1],[4,0,5],[2,5,4],[1,0],[1,4,6],[2,0,7]]),
([w0,w1,w343,w3,w30],[301,79,91,84,93,82,22,24,78],[],[[0,1,2],[0,1],[1,3,4],[5,0],[0,4],[2,4,3],[2,0],[2,6,7],[1,0,2],[1,0,8]]),
([w0,w1,w54,w149,w30],[427,82,91,84,424,93,24,78],[],[[0,1,2],[1,3,4],[5,0,2],[1,0],[2,5,3],[3,0,1],[2,0],[1,0,6],[7,0],[1,3]]),
([w0,w1,w336,w149,w3],[82,91,301,93,84,78],[],[[0,1],[0,2],[3,1],[0,4,3],[1,2],[4,0],[1,3,4],[0,2,3],[5,3],[0,2,5]]),
([w0,w1,w338,w149,w3],[76,82,91,7,55,93,84,432],[],[[0,1,2],[1,3,4],[5,2],[0,6],[2,0],[6,0,1],[2,5,6],[1,3,5],[6,0],[1,0,7]]),
([w0,w339,w1,w149,w3],[7,100,301,95,82,93,0,84,51,24],[],[[0,1,2],[3,4],[5,1,6],[4,7,5],[8,1],[4,0,7],[5,3],[7,1,4],[3,5],[4,1,9]]),
([w33,w79,w1,w149,w3],[301,51,0,93,84,95,79,82,24],[],[[0],[1],[2,0,3],[4,3],[5,6],[3,4],[3,4],[4,3],[4,3],[7,5,8]]),
([w0,w1,w344,w3,w30],[82,91,7,300,301,78],[],[[0,1],[2,1],[0,3],[0,4],[2,0],[1,3],[1,4],[0,3],[0,2],[5,3,4]]),
([w0,w1,w54,w152,w30],[82,91,300,78,321,84],[],[[0,1],[0,2],[3,1,2],[0,4],[1,2],[5,0],[1,4],[0,2,3],[3,4],[0,2,4]]),
([w0,w1,w336,w152,w3],[82,91,301,78,321,84,123],[],[[0,1],[0,2],[3,1,2],[0,4],[1,2],[5,0],[1,3,4],[0,2,5],[3,4,6],[0,2,3]]),
([w0,w1,w345,w3,w30],[82,91,78,315,300,88,90,112],[],[[0,1],[2,1,3],[0,4],[0,5,6],[4,0],[1,2,4],[1,6,7],[0,3],[0,3],[2,4,5]]),
([w0,w1,w54,w153,w30],[78,91,10,321,110,300,84,82],[],[[0,1],[2,3,4],[0,1,5],[0,3],[1,0,2],[6,5,7],[1,3],[0,5],[0,2],[1,3]]),
([w0,w1,w336,w153,w3],[321,82,91,78,90,84,88],[],[[0,1,2],[0,1],[3,2,4],[1,0],[0,2],[5,1],[2,0],[1,5],[3,0,6],[1,0]]),
([w0,w1,w329,w153,w30],[61,82,88,10,98,78,16,90,91],[],[[0,1,2],[1,3,4],[5,6,7],[0,2],[2,0],[2,0],[8,4],[1,7],[2,0],[1,0,2]]),
([w0,w330,w1,w153,w30],[10,110,321,97,91,82,90,422],[],[[0,1,2],[3,4,5],[6,4],[5,1],[4,0,1],[4,3],[6,0,7],[3,5],[4,1],[4,1]])]
noncomputable def p13_D3 : List StD := [
([w346,w31,w2,w30],[91,67,84,22,90,78,59],[],[[0,1,2],[0,3,4],[5,2],[2,6],[0,6,4],[0,2]]),
([w155,w31,w53,w30],[91,67,84,22,90,78,59],[],[[0,1,2],[0,3,4],[5,2],[2,6],[0,6,4],[0,2]]),
([w155,w31,w336,w2],[91,67,84,78,22,59,90],[],[[0,1,2],[3,2],[0,4,3],[0,5,6],[2,5],[0,2]]),
([w347,w31,w2,w3],[91,73,90,30,59,62,84],[],[[0,1,2],[0,3,4],[4,2],[2,5],[0,5,6],[0,2]]),
([w157,w31,w53,w3],[91,73,90,30,84,59,62],[],[[0,1,2],[0,3,4],[5,2],[2,6],[0,6,4],[0,2]]),
([w157,w31,w54,w2],[91,73,90,59,30,62,84],[],[[0,1,2],[3,2],[0,4,3],[0,5,6],[2,5],[0,2]]),
([w31,w348,w2,w30],[16,62,17,90,59,379],[],[[0,1,2],[3,1],[3,4],[4,3],[1,3,4],[1,5]]),
([w161,w31,w53,w30],[17,62,16,24,59,90,65],[],[[0,1,2],[3,4,5],[1,4,5],[5,1],[5,4],[1,6]]),
([w161,w31,w336,w2],[17,62,16,59,65,24,379,90,53,112],[],[[0,1,2],[1,3,4],[5,3,6],[4,3],[7,1],[1,8,9]]),
([w31,w349,w2,w3],[18,321,59,84,62,379],[],[[0,1,2],[3,2],[3,1,4],[4,3],[2,3,4],[2,5]]),
([w163,w31,w53,w3],[19,59,18,32,62,65,90,84],[],[[0,1,2],[3,4,5],[1,4,6],[7,1],[7,4],[1,5]]),
([w163,w31,w54,w2],[19,59,18,62,84,112],[],[[0,1,2],[1,3,4],[4,3],[4,3],[4,1],[1,5]]),
([w350,w31,w2,w3],[112,71,90,62,84,59],[],[[0,1,2],[3,4],[3,2,4],[2,3],[4,3],[5,2]]),
([w171,w31,w53,w3],[112,71,90,62,84,59],[],[[0,1,2],[3,4],[3,2,4],[2,3],[4,3],[5,2]]),
([w171,w31,w54,w2],[112,71,90,59,62,84],[],[[0,1,2],[3,2],[4,5],[5,4],[2,3],[3,2]]),
([w31,w351,w3,w30],[14,59,15,95,433],[],[[0,1,2],[3,4],[4],[1,4],[4],[1,3,4]]),
([w174,w31,w54,w30],[15,59,14,84,62,65,90],[],[[0,1,2],[1,3],[4,3],[5,4],[6,1],[1,5,4]]),
([w174,w31,w336,w3],[15,62,14,84,26,20,90,59,95],[],[[0,1,2],[1,3],[4,3,5],[6,7],[8,1],[1,6,7]]),
([w31,w352,w2,w3],[18,59,19,90,95,434],[],[[0,1,2],[3,1],[4,5],[5],[1,3],[1,3]]),
([w176,w31,w53,w3],[19,59,18,95,62,90],[],[[0,1,2],[3,4],[1,4,3],[3,1],[3,4],[1,5]]),
([w176,w31,w54,w2],[19,59,18,90,84,62],[],[[0,1,2],[1,3],[4,5],[4,5],[3,1],[1,3]]),
([w353,w31,w3,w30],[90,56,44,59,30,32,84,62,259,91],[],[[0,1,2],[3,0],[3,4,5],[6,7],[0,8,9],[7,0,6]]),
([w181,w31,w54,w30],[90,56,44,91,30,32,62,84,259],[],[[0,1,2],[3,0],[3,4,5],[3,6,7],[0,8,3],[6,0,7]]),
([w181,w31,w336,w3],[84,56,44,62,91,90,46],[],[[0,1,2],[3,0],[4,5],[4,6,5],[0,3],[3,0]]),
([w31,w53,w182,w30],[90,62,91,84,112],[],[[0,1],[2,1,3],[0,4,2],[2,0],[1,3],[1,0,3]]),
([w31,w354,w2,w30],[91,67,84,62,112],[],[[0,1,2],[2,3],[0,4],[0,4],[3,2],[0,2]]),
([w31,w336,w2,w182],[227],[],[[0],[0],[0],[0],[0],[0]]),
([w31,w355,w3,w30],[14,62,15,84,61,435],[],[[0,1,2],[3,1],[4,5],[5],[1,3],[1,3]]),
([w185,w31,w54,w30],[15,62,14,91,112,84,61,59],[],[[0,1,2],[3,4],[1,4],[5,1],[6,4,7],[1,5]]),
([w185,w31,w336,w3],[15,62,14,84,59,112,61],[],[[0,1,2],[1,3],[4,5],[6,4],[3,1],[1,3]]),
([w31,w53,w186,w30],[84,62,91,389],[],[[0,1],[0,1],[2,3],[2,3],[1,0],[1,0]]),
([w31,w356,w2,w30],[16,62,17,84,91,389],[],[[0,1,2],[3,1],[4,5],[4,5],[1,3],[1,3]]),
([w31,w336,w2,w186],[91,389],[],[[0,1],[1],[0,1],[0,1],[1],[0,1]]),
([w31,w357,w2,w30],[16,91,17,62,84,61,436],[],[[0,1,2,3],[4,3],[5,6],[6],[3,4],[3,4]]),
([w187,w31,w53,w30],[17,62,16,61,59,84],[],[[0,1,2],[3,4],[1,4,3],[3,1],[3,4],[1,5]]),
([w187,w31,w336,w2],[17,62,16,84,112,59,61],[],[[0,1,2],[1,3],[4,5],[6,4,5],[3,1],[1,3]]),
([w31,w223,w46,w30],[61,361,362,84,300,91,59,90,95],[],[[0,1,2],[3,4,5],[0,6],[1,0],[5,7,8],[6,0]]),
([w31,w225,w83,w3],[61,351,437,90,301,91,62,95],[],[[0,1,2],[3,4,5],[5,6,7],[1,0],[5,0],[6,3,7]]),
([w31,w238,w46,w30],[61,365,438,84,300,259,59,91,95],[],[[0,1,2],[3,4,5],[0,5,6],[1,0],[7,8],[6,0]]),
([w31,w240,w2,w87],[61,345,439,259,59,97,112,91],[],[[0,1,2],[3,4,5],[3,6],[7,0,6],[1,0],[4,5]]),
([w31,w251,w83,w3],[61,440,441,301,259,112,51,91,62,377],[],[[0,1,2],[0,3,4],[4,5],[1,5,6],[7,0],[8,0,9]]),
([w31,w253,w2,w87],[61,442,348,259,62,90,112,91,443],[],[[0,1,2],[3,4,5],[0,6,3],[7,0,5],[1,5,8],[4,0,6]]),
([w31,w53,w3,w129],[259,301,112,61,59,78,123,34],[],[[0,1],[0,2],[3,0,4],[5,2,6],[4,2,7],[4,3]]),
([w31,w54,w2,w129],[61,112,259,123,59,78],[],[[0,1,2],[2,3],[0,1,4],[5,0],[4,3,5],[4,0]]),
([w31,w327,w2,w3],[78,112,301,95,46,123],[],[[0,1],[0,2],[3,1,4],[4,1,3],[0,5],[0,1,3]]),
([w31,w53,w3,w130],[51,301,78,259,112,91,61,40],[],[[0,1,2],[3,4],[2,3],[2,4,5],[5,4],[2,6,7]]),
([w31,w54,w2,w130],[259,112,62,90,78,51],[],[[0,1],[0,2,3],[3,0,4],[4,1,5],[2,3,5],[2,1]]),
([w31,w328,w2,w3],[78,112,62,90,91,40],[],[[0,1],[0,2,3],[4,1],[2,1],[0,3,5],[0,1,4]]),
([w31,w53,w3,w132],[51,301,259,112,90,91,59],[],[[0,1,2],[2,3],[4,1,5],[5,3],[5,0],[6,4]]),
([w31,w54,w2,w132],[91,112,259,59,123,42],[],[[0,1],[2,3,4],[0,1],[0,1],[3,4,5],[0,1]]),
([w31,w331,w2,w3],[91,112,84,59,42],[],[[0,1],[2,3],[0,1],[0,1],[3,2,4],[0,1]]),
([w31,w53,w133,w3],[259,59,123,91,62,95,78],[],[[0,1,2],[3,0],[0,4,5],[3,5],[1,2,6],[1,2,4]]),
([w31,w332,w2,w3],[91,59,123,78,62,95,32],[],[[0,1,2],[3,1,2],[0,4,5],[0,5,6],[1,2,3],[0,2,3]]),
([w31,w54,w2,w133],[95,62,78,123,90,32],[],[[0,1],[2,1,3],[2,3],[2,0],[1,0],[1,4,5]]),
([w31,w53,w138,w30],[95,123,78,62,46,121],[],[[0,1,2],[0,3],[2,1],[2,1],[4,0,5],[2,0]]),
([w31,w335,w2,w30],[95,62,78,123,46,112,121],[],[[0,1],[2,3],[2,3],[1,0],[1,0],[4,5,6]]),
([w31,w336,w2,w138],[78,123,95,46],[],[[0,1],[0,1],[2,3],[3,2],[0,1],[0,1]]),
([w31,w53,w139,w30],[78,123,95,46,91],[],[[0,1],[2,3],[0,1],[0,1],[3,2,4],[0,1]]),
([w31,w337,w2,w30],[95,46,78,123,112,91],[],[[0,1],[2,3],[2,1,3],[1,0],[2,0],[1,4,5]]),
([w31,w336,w2,w139],[91,46,123,78,112],[],[[0,1,2],[3,2],[0,1,4],[0,4],[3,2],[0,2,1]]),
([w31,w53,w142,w30],[78,123,91,112],[],[[0,1],[2,3],[0,1],[0,1],[2,3],[0,1]]),
([w31,w340,w2,w30],[91,112,78,123],[],[[0,1],[2,3],[0,1],[0,1],[2,3],[0,1]]),
([w31,w336,w2,w142],[78,123,91,112],[],[[0,1],[0,1],[2,3],[2,3],[0,1],[0,1]]),
([w31,w341,w2,w30],[91,46,95,78,123,121,88],[],[[0,1,2],[3,4],[0,4],[0,2,1],[1,2],[0,5,6]]),
([w31,w53,w143,w30],[78,123,91,121,95],[],[[0,1],[2,3],[0,1],[0,1],[2,3,4],[0,1]]),
([w31,w336,w143,w2],[95,123,91,121,78,88],[],[[0,1,2],[0,3,2],[4,1],[4,1],[2,0,5],[2,0,4]]),
([w31,w342,w3,w30],[95,121,88,91,123,24],[],[[0,1,2],[0,1,2],[3,4],[3,4,5],[2,0,1],[2,0,1]]),
([w31,w54,w148,w30],[91,121,88,123,24],[],[[0,1],[2,1],[0,3],[0,3,4],[2,1],[0,1,2]]),
([w31,w336,w148,w3],[91,123,88,121,24],[],[[0,1],[2,1],[0,3],[0,3,2],[2,1,3],[0,1,4]]),
([w31,w343,w3,w30],[88,123,46,95,91,78],[],[[0,1],[0,2,3],[4,1],[2,1],[0,3,4],[0,1,5]]),
([w31,w54,w149,w30],[88,46,95,123,78,112,34],[],[[0,1,2],[0,3],[4,1,3],[1,2],[0,2,4],[0,5,6]]),
([w31,w336,w149,w3],[78,123,88,112,34],[],[[0,1],[0,1],[2,3],[2,3,4],[0,1],[0,1]]),
([w31,w344,w3,w30],[78,123,95,112,91],[],[[0,1],[2,3,4],[0,1],[0,1],[4,2],[0,1]]),
([w31,w54,w152,w30],[91,112,78,123],[],[[0,1],[2,3],[0,1],[0,1],[2,3],[0,1]]),
([w31,w336,w152,w3],[91,112,78,123],[],[[0,1],[2,3],[0,1],[0,1],[2,3],[0,1]]),
([w31,w345,w3,w30],[78,121,91,112,88],[],[[0,1],[2,1],[0,3],[0,3,2],[2,1,3],[0,1,4]]),
([w31,w54,w153,w30],[88,112,121,78,26],[],[[0,1],[0,2],[3,1],[3,1,4],[0,2],[0,1,2]]),
([w31,w336,w153,w3],[78,112,121,88,26],[],[[0,1],[0,2],[3,1],[3,1,2],[0,2,3],[0,1,4]])]
def p13_D2 : List StD := []
theorem p13_I2 : LevelN p13_R p13_T 2 p13_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C3x0 : levelOK p13_T p13_K p13_P 2 (p13_D2.map Prod.fst) ((p13_D3.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C3x1 : levelOK p13_T p13_K p13_P 2 (p13_D2.map Prod.fst) ((p13_D3.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C3x2 : levelOK p13_T p13_K p13_P 2 (p13_D2.map Prod.fst) ((p13_D3.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C3x3 : levelOK p13_T p13_K p13_P 2 (p13_D2.map Prod.fst) ((p13_D3.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C3x4 : levelOK p13_T p13_K p13_P 2 (p13_D2.map Prod.fst) ((p13_D3.drop (4*16)).take 16) = true := by decide +kernel
theorem p13_I3 : LevelN p13_R p13_T 3 p13_D3 := levelStep p13_B p13_W p13_Q p13_I2 (chunks 16 p13_D3 5 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C3x0
  · exact p13_C3x1
  · exact p13_C3x2
  · exact p13_C3x3
  · exact p13_C3x4
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x0 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x1 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x2 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x3 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x4 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (4*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x5 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (5*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x6 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (6*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x7 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (7*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x8 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (8*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x9 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (9*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x10 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (10*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x11 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (11*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x12 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (12*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x13 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (13*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x14 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (14*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x15 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (15*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x16 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (16*16)).take 16) = true := by decide +kernel
theorem p13_I4 : LevelN p13_R p13_T 4 p13_D4 := levelStep p13_B p13_W p13_Q p13_I3 (chunks 16 p13_D4 17 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C4x0
  · exact p13_C4x1
  · exact p13_C4x2
  · exact p13_C4x3
  · exact p13_C4x4
  · exact p13_C4x5
  · exact p13_C4x6
  · exact p13_C4x7
  · exact p13_C4x8
  · exact p13_C4x9
  · exact p13_C4x10
  · exact p13_C4x11
  · exact p13_C4x12
  · exact p13_C4x13
  · exact p13_C4x14
  · exact p13_C4x15
  · exact p13_C4x16
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x0 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x1 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x2 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x3 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x4 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (4*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x5 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (5*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x6 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (6*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x7 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (7*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x8 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (8*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x9 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (9*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x10 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (10*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x11 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (11*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x12 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (12*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x13 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (13*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x14 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (14*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x15 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (15*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x16 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (16*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x17 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (17*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x18 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (18*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x19 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (19*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x20 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (20*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x21 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (21*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x22 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (22*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x23 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (23*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x24 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (24*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x25 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (25*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x26 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (26*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x27 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (27*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x28 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (28*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x29 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (29*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x30 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (30*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x31 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (31*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x32 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (32*16)).take 16) = true := by decide +kernel
theorem p13_I5 : LevelN p13_R p13_T 5 p13_D5 := levelStep p13_B p13_W p13_Q p13_I4 (chunks 16 p13_D5 33 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C5x0
  · exact p13_C5x1
  · exact p13_C5x2
  · exact p13_C5x3
  · exact p13_C5x4
  · exact p13_C5x5
  · exact p13_C5x6
  · exact p13_C5x7
  · exact p13_C5x8
  · exact p13_C5x9
  · exact p13_C5x10
  · exact p13_C5x11
  · exact p13_C5x12
  · exact p13_C5x13
  · exact p13_C5x14
  · exact p13_C5x15
  · exact p13_C5x16
  · exact p13_C5x17
  · exact p13_C5x18
  · exact p13_C5x19
  · exact p13_C5x20
  · exact p13_C5x21
  · exact p13_C5x22
  · exact p13_C5x23
  · exact p13_C5x24
  · exact p13_C5x25
  · exact p13_C5x26
  · exact p13_C5x27
  · exact p13_C5x28
  · exact p13_C5x29
  · exact p13_C5x30
  · exact p13_C5x31
  · exact p13_C5x32
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x0 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x1 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x2 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x3 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x4 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (4*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x5 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (5*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x6 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (6*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x7 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (7*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x8 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (8*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x9 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (9*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x10 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (10*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x11 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (11*16)).take 16) = true := by decide +kernel
theorem p13_I6 : LevelN p13_R p13_T 6 p13_D6 := levelStep p13_B p13_W p13_Q p13_I5 (chunks 16 p13_D6 12 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C6x0
  · exact p13_C6x1
  · exact p13_C6x2
  · exact p13_C6x3
  · exact p13_C6x4
  · exact p13_C6x5
  · exact p13_C6x6
  · exact p13_C6x7
  · exact p13_C6x8
  · exact p13_C6x9
  · exact p13_C6x10
  · exact p13_C6x11
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x0 : levelOK p13_T p13_K p13_P 6 (p13_D6.map Prod.fst) ((p13_D7.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x1 : levelOK p13_T p13_K p13_P 6 (p13_D6.map Prod.fst) ((p13_D7.drop (1*16)).take 16) = true := by decide +kernel
theorem p13_I7 : LevelN p13_R p13_T 7 p13_D7 := levelStep p13_B p13_W p13_Q p13_I6 (chunks 16 p13_D7 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C7x0
  · exact p13_C7x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C8x0 : levelOK p13_T p13_K p13_P 7 (p13_D7.map Prod.fst) ((p13_D8.drop (0*16)).take 16) = true := by decide +kernel
theorem p13_I8 : LevelN p13_R p13_T 8 p13_D8 := levelStep p13_B p13_W p13_Q p13_I7 (chunks 16 p13_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C8x0
  ))
theorem p13_L : LowN p13_R p13_T 9 := lowSearch p13_B p13_I8 (by decide +kernel)
def ptopT : Nat := 0xfefefe80fe808000fefefe80fe808000
def ptopR : List Nat := [0, 1, 2, 3, 4, 5]
def ptopE : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15),(4,7,23),(5,7,39)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
theorem ptopS0 : SliceN ptopR ptopT (0x88888888888888888888888888888888,7,[2, 3, 4, 5]) := mkSlice (w:=3) ptopB p5_B p5_L (by decide +kernel)
theorem ptopS1 : SliceN ptopR ptopT (0xcccccccccccccccccccccccccccccccc,8,[3, 4, 5, 2, 0]) := mkSlice (w:=2) ptopB p6_B p6_L (by decide +kernel)
theorem ptopS2 : SliceN ptopR ptopT (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,8,[3, 4, 5, 2, 1]) := mkSlice (w:=1) ptopB p6_B p6_L (by decide +kernel)
theorem ptopS3 : SliceN ptopR ptopT (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,7,[1, 3, 4, 5]) := mkSlice (w:=5) ptopB p5_B p5_L (by decide +kernel)
theorem ptopS4 : SliceN ptopR ptopT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,8,[3, 4, 5, 1, 0]) := mkSlice (w:=4) ptopB p6_B p6_L (by decide +kernel)
theorem ptopS5 : SliceN ptopR ptopT (0xff00ff00ff00ff00ff00ff00ff00ff,9,[4, 5, 2, 0, 1]) := mkSlice (w:=0) ptopB p13_B p13_L (by decide +kernel)
theorem ptopS6 : SliceN ptopR ptopT (0xffff0000ffff0000ffff0000ffff,9,[3, 5, 2, 0, 1]) := mkSlice (w:=0) ptopB p13_B p13_L (by decide +kernel)
theorem ptopS7 : SliceN ptopR ptopT (0xffffffff00000000ffffffff,9,[3, 4, 2, 0, 1]) := mkSlice (w:=0) ptopB p13_B p13_L (by decide +kernel)
theorem ptopS8 : SliceN ptopR ptopT (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,7,[0, 3, 4, 5]) := mkSlice (w:=6) ptopB p5_B p5_L (by decide +kernel)
def ptopZ : List SliceD := [(0x88888888888888888888888888888888,7,[2, 3, 4, 5]),(0xcccccccccccccccccccccccccccccccc,8,[3, 4, 5, 2, 0]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,8,[3, 4, 5, 2, 1]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,7,[1, 3, 4, 5]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,8,[3, 4, 5, 1, 0]),(0xff00ff00ff00ff00ff00ff00ff00ff,9,[4, 5, 2, 0, 1]),(0xffff0000ffff0000ffff0000ffff,9,[3, 5, 2, 0, 1]),(0xffffffff00000000ffffffff,9,[3, 4, 2, 0, 1]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,7,[0, 3, 4, 5])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨ptopS0,ptopS1,ptopS2,ptopS3,ptopS4,ptopS5,ptopS6,ptopS7,ptopS8,by simp⟩
def ptopC : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[])]
def ptopP : List (Nat × Nat) := [(24,25),(24,26),(13,15),(24,28),(11,15),(18,26),(10,26),(7,39),(10,42),(17,25),(9,25),(9,41),(17,49)]
def ptopK : List CutV := ptopC.map (mkCut ptopZ)
theorem ptopW : ∀ c ∈ ptopK, CutP ptopR ptopT c := cutsGood ptopY (by decide +kernel)
theorem ptopQ : ptopP.all (sepOK ptopT) = true := by decide +kernel
noncomputable def ptopD10 : List StD := [
([w0,w1,w2,w3,w30,w358],[0,1,2,3,4,5,6,7,8],[0,1,2,3,4,5,6,7,8,9,10,11,12],[[0,100,101,1,2,102],[3,100,103,4,0,104],[5,0,100,105],[6,0,100,106],[7,0,107,108],[8,101,103,3,0,102],[5,0,101,109],[6,0,101,110],[7,0,107,111],[5,3,103,105],[6,3,103,106],[7,3,107,108],[5,6,105],[5,7,108],[6,7,112]])]
def ptopD9 : List StD := []
theorem ptopI9 : LevelN ptopR ptopT 9 ptopD9 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC10x0 : levelOK ptopT ptopK ptopP 9 (ptopD9.map Prod.fst) ((ptopD10.drop (0*16)).take 16) = true := by decide +kernel
theorem ptopI10 : LevelN ptopR ptopT 10 ptopD10 := levelStep ptopB ptopW ptopQ ptopI9 (chunks 16 ptopD10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC10x0
  ))
theorem ptopL : LowN ptopR ptopT 11 := lowSearch ptopB ptopI10 (by decide +kernel)

def sixInputs : List Sig := rootsW [0,1,2,3,4,5]
def graph : Sig := W ptopT
theorem graph_proper : proper graph := (baseOK_ok ptopB).prop
def sample (r : Row) (i : Fin 6) : Bool := bit r (sixInputs.getD i.val zero)
theorem sixList : List.ofFn (fun i : Fin 6 => sixInputs.getD i.val zero) = sixInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = sixInputs.map (bit r) := by
  rw [←sixList,List.map_ofFn]
  rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sixTable : ∀ r : Row, bit r graph = target (sample r) := by decide +kernel
theorem sixEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sixInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sixInputs.toFinset := by
  have b := baseOK_ok ptopB
  have goalEq : (execute C.gates sixInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sixEval C legal C.output r).trans ((computes (sample r)).trans (sixTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sixInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W ptopT) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sixInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sixInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = sixInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run sixInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes : Impossible true graph 10 sixInputs.toFinset := by
  intro k small run
  have steps := list_run run sixInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (sixInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptopL q bank built hit
  omega
theorem replaceShort (s : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize 6 target s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  classical
  by_cases big : 12 ≤ s
  · exact ⟨smallCircuit,witnessMonotone,(by rw [witnessSize]; exact big),witnessCorrect⟩
  obtain ⟨C,legal,hs,correct⟩ := h
  by_cases mono : ∀ g ∈ C.gates, g.op ≠ GateOp.not
  · refine ⟨C,?_,hs,correct⟩
    intro g hg
    obtain ⟨ho,hl⟩ := legal g hg
    refine ⟨?_,hl⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ho ⊢
    rcases ho with a | a | a
    · exact Or.inl a
    · exact Or.inr a
    · exact (mono g hg a).elim
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : C.gates.countP (fun q => !isNot q) < C.gates.length := by
    rcases Nat.lt_or_ge (C.gates.countP (fun q => !isNot q)) C.gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  obtain ⟨k,hk,run⟩ := physicalSigned C legal correct
  have hs' : C.gates.length ≤ s := hs
  exact (excludes k (by omega) run).elim

end PEqualNP.Outside.L_meta_12360

theorem PEqualNP.Outside.L_meta_12360 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124160 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124160 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  exact PEqualNP.Outside.L_meta_12360.replaceShort s h
