import PEqualNP.Defs

-- The live-set and restriction lemmas follow L-meta-10554, L-meta-10802, L-meta-1674, L-meta-670 and L-meta-1667.
namespace PEqualNP.Outside.L_meta_12142
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
theorem bin_four (u : Bool) (o : Nat) (h : (u || Nat.blt o 2) = true) : ∃ e, allowed u e ∧ ∀ a b, bin o a b = bin e a b := by
  cases u
  · refine ⟨o,Or.inl ?_,fun _ _ => rfl⟩
    simpa only [Bool.false_or,Nat.blt_eq] using h
  · by_cases h : o < 4
    · exact ⟨o,Or.inr ⟨rfl,h⟩,fun _ _ => rfl⟩
    · refine ⟨3,Or.inr ⟨rfl,by omega⟩,fun a b => ?_⟩
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
def LowN (u : Bool) (R : List Nat) (T L : Nat) : Prop := Lower u (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (u : Bool) (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice u (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

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

theorem lowOf {u T R E K} (hB : baseOK T R E = true) (h : Impossible u (W T) K (rootsW R).toFinset) :
    LowN u R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {u T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN u R T (K+1) := by
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

theorem mkSlice {u R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN u R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN u R T (d,L,vs) := by
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

def opOK (u : Bool) (o : Nat) : Bool := u || Nat.blt o 2
def av (u : Bool) (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || (u && Nat.beq x (Nat.xor d m)))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (u : Bool) (P : List Nat) : List Nat → List Nat
  | [] => P
  | c::cs => mkPool u (bif opOK u (Nat.mod c 4) then P ++ [nb (Nat.mod c 4) (P.getD (Nat.mod (Nat.div c 4) 32) 0) (P.getD (Nat.div c 128) 0)] else P) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available u bank (RF f v)
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
theorem av_ok {u} {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS u f bank P)
    (h : av u d P v = true) : Available u bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | ⟨hu,h⟩⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv hu e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {u} {f : Row → Row} {roots bank p P} (o a b : Nat) (ho : opOK u o = true) (hr : Reach u roots p bank) (hP : PS u f bank P)
    (ha : Available u bank (RF f a)) (hb : Available u bank (RF f b)) :
    ∃ next, Reach u roots (p+1) next ∧ PS u f next P ∧ Available u next (RF f (nb o a b)) ∧
      ∀ v, Available u bank v → Available u next v := by
  obtain ⟨e,he,heq⟩ := bin_four u o ho
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) he ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {u} {f : Row → Row} {bank P} (hP : PS u f bank P) (i : Nat) : Available u bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {u} {f : Row → Row} {roots} (cs : List Nat) {bank p P} (hr : Reach u roots p bank)
    (hP : PS u f bank P) : ∃ next, Reach u roots (p+cs.length) next ∧ PS u f next (mkPool u P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    have big : ∃ next, Reach u roots (p+1) next ∧ PS u f next (bif opOK u (Nat.mod c 4) then P ++ [nb (Nat.mod c 4) (P.getD (Nat.mod (Nat.div c 4) 32) 0) (P.getD (Nat.div c 128) 0)] else P) := by
      cases ho : opOK u (Nat.mod c 4)
      · refine ⟨_,Reach.two false hr (Or.inr (Or.inl ⟨false,rfl⟩)) (Or.inr (Or.inl ⟨false,rfl⟩)),fun v hv => available_cons _ (hP v hv)⟩
      · obtain ⟨next,h1,h2,h3,_⟩ := pay_nb (Nat.mod c 4) _ _ ho hr hP (getD_ps hP (Nat.mod (Nat.div c 4) 32)) (getD_ps hP (Nat.div c 128))
        refine ⟨next,h1,?_⟩
        intro v hv
        rw [cond_true] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact h2 v hv
        · rw [List.mem_singleton.mp hv]
          exact h3
    obtain ⟨next,h1,this⟩ := big
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (u : Bool) (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av u d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (u : Bool) (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av u c.1 c.2.2.2) && keepB u c.1 c.2.2.2 ka a && keepB u c.1 c.2.2.2 kb b &&
  (bif av u c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av u c.1 c.2.2.2 a && av u c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def same (u : Bool) (p : Nat × Nat) (v : Nat) : Bool :=
  bif u then Nat.testBit v p.1 == Nat.testBit v p.2 else !(Nat.testBit v p.1) || Nat.testBit v p.2
def sepEval (u : Bool) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  same u p z && (!ka || same u p a) && (!kb || same u p b) && rest.all (same u p)
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && T.testBit p.1 && !(T.testBit p.2)

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

def CutP (u : Bool) (_R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach u (roots.map observe) c.2.2.1 bank ∧ PS u f bank c.2.2.2 ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {u R T c k rest a b o ka kb} (hc : CutP u R T c) (ho : opOK u o = true)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval u k rest a b (nb o a b) ka kb c = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach u (roots.map observe) q bank' ∧ PS u f bank' c.2.2.2 ∧ Available u bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av u c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b ho hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply u bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available u bank' v := by
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

theorem kid_mem {rest : List Nat} {a b z : Nat} {ka kb : Bool} {v : Sig} (hv : v ∈ kidW rest a b z ka kb) :
    ∃ x, v = W x ∧ (x = z ∨ (ka = true ∧ x = a) ∨ (kb = true ∧ x = b) ∨ x ∈ rest) := by
  rcases List.mem_cons.mp hv with rfl | hv
  · exact ⟨z,rfl,Or.inl rfl⟩
  have low : ∀ v ∈ kept kb (W b) (rest.map W), ∃ x, v = W x ∧ ((kb = true ∧ x = b) ∨ x ∈ rest) := by
    intro v hv
    cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
      exact ⟨x,e.symm,Or.inr hx⟩
    · rcases List.mem_cons.mp hv with e | hv
      · exact ⟨b,e,Or.inl ⟨rfl,rfl⟩⟩
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        exact ⟨x,e.symm,Or.inr hx⟩
  cases ka
  · obtain ⟨x,h1,h2⟩ := low v hv
    exact ⟨x,h1,Or.inr (Or.inr h2)⟩
  · rcases List.mem_cons.mp hv with e | hv
    · exact ⟨a,e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
    · obtain ⟨x,h1,h2⟩ := low v hv
      exact ⟨x,h1,Or.inr (Or.inr h2)⟩
theorem sep_sound {u T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval u rest a b (nb o a b) ka kb p = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨p1,p2⟩,t1⟩,t2⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have all : ∀ v ∈ kidW rest a b (nb o a b) ka kb, ∃ x, v = W x ∧ same u p x = true := by
    intro v hv
    obtain ⟨x,rfl,hx⟩ := kid_mem hv
    refine ⟨x,rfl,?_⟩
    rcases hx with rfl | ⟨q,rfl⟩ | ⟨q,rfl⟩ | hx
    · exact h1
    · subst q; exact h2.resolve_left (by simp)
    · subst q; exact h3.resolve_left (by simp)
    · exact h4 x hx
  intro k' _ run
  cases u
  · obtain ⟨v,hv,hp,hn⟩ := mono_row_difference run rfl (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W]; exact t1) (by rw [bit_W]; exact t2)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    rw [bit_W] at hp hn
    simp only [same,cond_false,Bool.or_eq_true,Bool.not_eq_true'] at hx
    rcases hx with hx | hx
    · rw [hx] at hp; exact Bool.noConfusion hp
    · rw [hx] at hn; exact Bool.noConfusion hn
  · obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W,t1,t2]; simp)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    apply hne
    rw [bit_W,bit_W]
    simpa only [same,cond_true,beq_iff_eq] using hx

-- A tight live set of a monotone run is a formula over distinct leaves, so its
-- leaves own disjoint rectangles of true rows against false rows.
def KWOwn (S : Finset Sig) (T : Sig) (owns : Sig → Row → Row → Prop) : Prop :=
  (∀ p n, bit p T = true → bit n T = false → ∃ v, owns v p n) ∧
  (∀ v p n, owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false) ∧
  (∀ v w p n, owns v p n → owns w p n → v = w) ∧
  (∀ v p n p' n', owns v p n → owns v p' n' → owns v p n')
abbrev KWRooms (S : Finset Sig) (T : Sig) := {o : Sig → Row → Row → Prop // KWOwn S T o}
def KWRooms.owns {S T} (H : KWRooms S T) : Sig → Row → Row → Prop := H.1
theorem KWRooms.total {S T} (H : KWRooms S T) : ∀ p n, bit p T = true → bit n T = false → ∃ v, H.owns v p n := H.2.1
theorem KWRooms.valid {S T} (H : KWRooms S T) {v p n} : H.owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false := H.2.2.1 v p n
theorem KWRooms.unique {S T} (H : KWRooms S T) {v w p n} : H.owns v p n → H.owns w p n → v = w := H.2.2.2.1 v w p n
theorem KWRooms.rect {S T} (H : KWRooms S T) {v p n p' n'} : H.owns v p n → H.owns v p' n' → H.owns v p n' := H.2.2.2.2 v p n p' n'
theorem kwLeaf (T : Sig) : Nonempty (KWRooms {T} T) := by
  refine ⟨⟨fun v p n => v = T ∧ bit p T = true ∧ bit n T = false,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    exact ⟨T,rfl,hp,hn⟩
  · rintro v p n ⟨rfl,hp,hn⟩
    exact ⟨by simp,hp,hn⟩
  · rintro v w p n ⟨rfl,_⟩ ⟨rfl,_⟩
    rfl
  · rintro v p n p' n' ⟨rfl,hp,_⟩ ⟨_,_,hn⟩
    exact ⟨rfl,hp,hn⟩
theorem kwFork {T : Sig} {U : Finset Sig} {a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1) (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U)
    (hz : bin d a b ∉ U) (H : KWRooms (insert (bin d a b) U) T) : Nonempty (KWRooms (insert a (insert b U)) T) := by
  classical
  let z := bin d a b
  let own : Sig → Row → Row → Prop := fun v p n => (v ∈ U ∧ H.owns v p n) ∨
    (H.owns z p n ∧ v = (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)))
  have pickU : ∀ (p n : Row), (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)) ∉ U := by
    intro p n
    split <;> split <;> assumption
  refine ⟨⟨own,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with e | hm
    · refine ⟨_,Or.inr ⟨?_,rfl⟩⟩
      rw [show v = z from e] at hv
      exact hv
    · exact ⟨v,Or.inl ⟨hm,hv⟩⟩
  · intro v p n h
    rcases h with ⟨hm,hv⟩ | ⟨hv,rfl⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm),(H.valid hv).2⟩
    · obtain ⟨_,hp,hn⟩ := H.valid hv
      change bit p (bin d a b) = true at hp
      change bit n (bin d a b) = false at hn
      rw [bit_bin] at hp hn
      rcases d01 with rfl | rfl
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,rfl⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,rfl⟩
    · exact H.unique hv hw
    · exact absurd (show z ∈ U by rw [←H.unique hv hw]; exact vU) hz
    · exact absurd (show z ∈ U by rw [←H.unique hw hv]; exact wU) hz
    · rfl
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,e1⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,e2⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact absurd (e2 ▸ vU) (pickU p' n')
    · exact absurd (e1 ▸ wU) (pickU p n)
    · refine Or.inr ⟨H.rect hv hw,?_⟩
      by_cases h : d=0
      · rw [if_pos h] at e2 ⊢
        exact e2
      · rw [if_neg h] at e1 ⊢
        exact e1
theorem kwTight {T : Sig} {k : Nat} {S : Finset Sig} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact kwLeaf T
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b ∉ U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := live_size tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le a (insert b U)
    have le2 := Finset.card_insert_le b U
    have ha : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a ∈ insert b U)] at tight
      omega
    have hb : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by
      rcases hd with h | ⟨h,_⟩
      · omega
      · exact Bool.noConfusion h
    exact kwFork d01 hab ha hb fresh H
def only (l : List Nat) (p n a : Nat) : Bool :=
  Nat.blt p 128 && Nat.blt n 128 && l.all (fun x => !(Nat.testBit x p) || Nat.testBit x n || Nat.beq x a)
abbrev KwD := Nat × Nat × Nat × Nat × Nat × Nat
def findW (l : List Nat) (p n : Nat) : Nat := (l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n))).getD 0
def kwOK (T : Nat) (q : KwD) : Bool :=
  T.testBit q.1 && T.testBit q.2.2.2.1 && T.testBit q.2.2.2.2.2 && !(T.testBit q.2.1) && !(T.testBit q.2.2.1) && !(T.testBit q.2.2.2.2.1)
def kwList (l : List Nat) (q : KwD) : Bool :=
  let a := findW l q.1 q.2.2.1
  let b := findW l q.1 q.2.2.2.2.1
  only l q.1 q.2.2.1 a && only l q.2.2.2.1 q.2.1 a &&
  (bif Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1 then !(Nat.testBit a q.1 && !(Nat.testBit a q.2.1))
   else only l q.1 q.2.2.2.2.1 b && only l q.2.2.2.2.2 q.2.1 b && !(Nat.beq a b))
theorem only_own {l : List Nat} {T p n a : Nat} (H : KWRooms ((l.map W).toFinset) (W T))
    (h : only l p n a = true) (tp : T.testBit p = true) (tn : T.testBit n = false) :
    ∃ (hp : p < 128) (hn : n < 128), H.owns (W a) ⟨p,hp⟩ ⟨n,hn⟩ := by
  simp only [only,Bool.and_eq_true,Nat.blt_eq,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨hp,hn⟩,hl⟩ := h
  refine ⟨hp,hn,?_⟩
  obtain ⟨v,hv⟩ := H.total ⟨p,hp⟩ ⟨n,hn⟩ (by rw [bit_W]; exact tp) (by rw [bit_W]; exact tn)
  obtain ⟨hm,h1,h2⟩ := H.valid hv
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  rw [bit_W] at h1 h2
  rcases hl x hx with (h | h) | h
  · rw [h] at h1; exact Bool.noConfusion h1
  · rw [h] at h2; exact Bool.noConfusion h2
  · rw [Nat.eq_of_beq_eq_true h] at hv
    exact hv
theorem kw_sound {T k : Nat} {l : List Nat} (nd : (l.map W).Nodup) (size : l.length = k+1) (lt : ∀ x ∈ l, x < 2^128) (q : KwD)
    (hT : kwOK T q = true) (h : kwList l q = true) : Impossible false (W T) k (l.map W).toFinset := by
  intro k' hk run
  have lb := live_size run
  rw [List.toFinset_card_of_nodup nd,List.length_map] at lb
  obtain ⟨H⟩ := kwTight run (by rw [List.toFinset_card_of_nodup nd,List.length_map]; omega)
  simp only [kwOK,Bool.and_eq_true,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨⟨⟨t1,t2⟩,t3⟩,t4⟩,t5⟩,t6⟩ := hT
  simp only [kwList,Bool.and_eq_true] at h
  obtain ⟨⟨h1,h2⟩,h3⟩ := h
  obtain ⟨hp,hna,o1⟩ := only_own H h1 t1 t5
  obtain ⟨hpa,hn,o2⟩ := only_own H h2 t2 t4
  have own := H.rect o1 o2
  cases hc : (Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1)
  · rw [hc,cond_false] at h3
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at h3
    obtain ⟨⟨h4,h5⟩,h6⟩ := h3
    obtain ⟨_,hnb,o3⟩ := only_own H h4 t1 t6
    obtain ⟨hpb,_,o4⟩ := only_own H h5 t3 t4
    have own' := H.rect o3 o4
    have ee := H.unique own own'
    have mem : ∀ {a : Nat}, W a ∈ (l.map W).toFinset → ∃ x ∈ l, W x = W a := by
      intro a ha
      obtain ⟨x,hx,e⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact ⟨x,hx,e⟩
    have fw : ∀ p n, findW l p n < 2^128 := by
      intro p n
      unfold findW
      cases hf : l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n)) with
      | none => exact Nat.two_pow_pos 128
      | some x => exact lt x (List.mem_of_find?_eq_some hf)
    have := W_inj (fw _ _) (fw _ _) ee
    rw [this,Nat.beq_refl] at h6
    exact Bool.noConfusion h6
  · rw [hc,cond_true] at h3
    have v := (H.valid own).2
    rw [bit_W,bit_W] at v
    rw [v.1,v.2] at h3
    exact Bool.noConfusion h3

-- Symmetry: exchanging neighbouring input variables.
def hiM : Nat → Nat
  | 0 => 0x22222222222222222222222222222222
  | 1 => 0x0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
  | 2 => 0x00f000f000f000f000f000f000f000f0
  | 3 => 0x0000ff000000ff000000ff000000ff00
  | _ => 0x00000000ffff000000000000ffff0000
def loM : Nat → Nat
  | 0 => 0x44444444444444444444444444444444
  | 1 => 0x30303030303030303030303030303030
  | 2 => 0x0f000f000f000f000f000f000f000f00
  | 3 => 0x00ff000000ff000000ff000000ff0000
  | _ => 0x0000ffff000000000000ffff00000000
def keM : Nat → Nat
  | 0 => 0x99999999999999999999999999999999
  | 1 => 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3
  | 2 => 0xf00ff00ff00ff00ff00ff00ff00ff00f
  | 3 => 0xff0000ffff0000ffff0000ffff0000ff
  | _ => 0xffff00000000ffffffff00000000ffff
def shM : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | _ => 16
def swapN (i v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land v (keM i)) (Nat.shiftLeft (Nat.land v (hiM i)) (shM i))) (Nat.shiftRight (Nat.land v (loM i)) (shM i))
def sig (i : Nat) (r : Row) : Row :=
  if (hiM i).testBit r.val then Fin.ofNat 128 (r.val + shM i) else
    if (loM i).testBit r.val then Fin.ofNat 128 (r.val - shM i) else r
def swapFacts (i : Nat) (r : Row) : Prop :=
  ((keM i).testBit r.val = true ∧ (sig i r).val = r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ shM i ≤ r.val ∧ (sig i r).val = r.val - shM i ∧ (hiM i).testBit (r.val - shM i) = true ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ (sig i r).val = shM i + r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = true)
theorem swap_facts : ∀ (i : Fin 5) (r : Row), swapFacts i.val r ∧ sig i.val (sig i.val r) = r := by
  unfold swapFacts
  decide +kernel
theorem swap_ok (i : Nat) (hi : i < 5) (v : Nat) : W (swapN i v) = rename (sig i) (W v) := by
  apply bit_ext
  intro r
  rw [bit_W,bit_rename,bit_W]
  have e : (swapN i v).testBit r.val = (((v.testBit r.val && (keM i).testBit r.val) ||
      (decide (shM i ≤ r.val) && (v.testBit (r.val - shM i) && (hiM i).testBit (r.val - shM i)))) ||
      (v.testBit (shM i + r.val) && (loM i).testBit (shM i + r.val))) := by
    have s1 : (Nat.shiftLeft (Nat.land v (hiM i)) (shM i)).testBit r.val = (decide (shM i ≤ r.val) && (Nat.land v (hiM i)).testBit (r.val - shM i)) := by
      exact Nat.testBit_shiftLeft ..
    have s2 : (Nat.shiftRight (Nat.land v (loM i)) (shM i)).testBit r.val = (Nat.land v (loM i)).testBit (shM i + r.val) := by
      exact Nat.testBit_shiftRight ..
    unfold swapN
    rw [tb_lor,tb_lor,s1,s2,tb_land,tb_land,tb_land]
  rw [e]
  rcases (swap_facts ⟨i,hi⟩ r).1 with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4⟩
  · change (sig i r).val = r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
  · change (sig i r).val = r.val - shM i at h3
    rw [h3]
    simp only [] at h1 h2 h4 h5
    rw [h1,h4,h5,decide_eq_true h2]
    simp
  · change (sig i r).val = shM i + r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
def permN (l : List Nat) (v : Nat) : Nat := l.foldl (fun v i => swapN i v) v
def symOK (T : Nat) (l : List Nat) : Bool := l.all fun i => Nat.blt i 5 && Nat.beq (swapN i T) T
theorem perm_sound {u T k} (l : List Nat) (hT : symOK T l = true) (s : List Nat)
    (h : Impossible u (W T) k ((s.map (permN l)).map W).toFinset) : Impossible u (W T) k (s.map W).toFinset := by
  induction l generalizing s with
  | nil =>
    simpa [show (permN [] : Nat → Nat) = id from rfl] using h
  | cons i l ih =>
    simp only [symOK,List.all_cons,Bool.and_eq_true,Nat.blt_eq] at hT
    obtain ⟨⟨hi,hs⟩,hl⟩ := hT
    have h' : Impossible u (W T) k ((s.map (swapN i)).map W).toFinset := by
      apply ih hl
      have : (s.map (swapN i)).map (permN l) = s.map (permN (i::l)) := by
        rw [List.map_map]
        rfl
      rw [this]
      exact h
    intro k' hk run
    have onto : Function.Surjective (sig i) := fun r => ⟨sig i r,(swap_facts ⟨i,hi⟩ r).2⟩
    have r2 := live_rename run (sig i) onto
    rw [←swap_ok i hi T,Nat.eq_of_beq_eq_true hs] at r2
    apply h' k' hk
    have : ((s.map (swapN i)).map W).toFinset = (s.map W).toFinset.image (rename (sig i)) := by
      ext v
      simp only [List.mem_toFinset,List.mem_map,Finset.mem_image,exists_exists_and_eq_and,swap_ok i hi]
    rw [this]
    exact r2

abbrev StD := List Nat × List Nat × List Nat
def pick : List Nat → Nat → List Nat
  | [],_ => []
  | x::xs,m => bif Nat.beq (Nat.mod m 2) 1 then x :: pick xs (Nat.div m 2) else pick xs (Nat.div m 2)
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
def mkCut (u : Bool) (Z : List SliceD) (c : Nat × List Nat) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool u (initPool s.1 s.2.2) c.2)
abbrev Tabs := List CutV × List (Nat × Nat) × List KwD × List (List Nat)
def Tabs.cuts (t : Tabs) : List CutV := t.1
def Tabs.seps (t : Tabs) : List (Nat × Nat) := t.2.1
def Tabs.kws (t : Tabs) : List KwD := t.2.2.1
def Tabs.perms (t : Tabs) : List (List Nat) := t.2.2.2
def sortN (l : List Nat) : List Nat := l.foldr ins []
theorem mem_sortN {v : Nat} {l : List Nat} : v ∈ sortN l ↔ v ∈ l := by
  induction l with
  | nil => simp [sortN]
  | cons x xs ih =>
    change v ∈ ins x (sortN xs) ↔ _
    rw [mem_ins,ih]
    simp
def ty (i n : Nat) : Bool := Nat.beq (Nat.mod i 4) n
def hintOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif ty i 0 then (match t.cuts[Nat.div i 4]? with
    | some c => cutEval u k rest a b z ka kb c
    | none => false)
  else bif ty i 1 then (match t.seps[Nat.div i 4]? with
    | some q => sepEval u rest a b z ka kb q
    | none => false)
  else bif ty i 2 then (match t.kws[Nat.div i 4]? with
    | some q => !u && Nat.beq (kidN rest a b z ka kb).length (k+1) && kwList (kidN rest a b z ka kb) q
    | none => false)
  else (match t.perms[Nat.div i 4]? with
    | some l => next.any (beqL (sortN ((kidN rest a b z ka kb).map (permN l))))
    | none => false)
def kidOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK u k next t rest a b z kk.1 kk.2)
def opsOf (u : Bool) : List Nat := bif u then [0,1,2,3] else [0,1]
def pairOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  (opsOf u).all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK u k next t p.2.2 hints p.1 p.2.1 z)
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
def stOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK u k next t st.1) (pairs st.1) (st.2.2.map (pick st.2.1))
def levelOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK u T t k next)
abbrev TabsP (u : Bool) (R : List Nat) (T : Nat) (t : Tabs) : Prop :=
  (∀ c ∈ t.cuts, CutP u R T c) ∧ t.seps.all (sepOK T) = true ∧ t.kws.all (kwOK T) = true ∧ t.perms.all (symOK T) = true
theorem TabsP.c {u R T t} (h : TabsP u R T t) : ∀ c ∈ t.cuts, CutP u R T c := h.1
theorem TabsP.s {u R T t} (h : TabsP u R T t) : t.seps.all (sepOK T) = true := h.2.1
theorem TabsP.k {u R T t} (h : TabsP u R T t) : t.kws.all (kwOK T) = true := h.2.2.1
theorem TabsP.p {u R T t} (h : TabsP u R T t) : t.perms.all (symOK T) = true := h.2.2.2
def LevelN (u : Bool) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible u (W T) k (st.1.map W).toFinset
theorem cutsGood {u R T} {Z : List SliceD} {C : List (Nat × List Nat)} (hZ : ∀ s ∈ Z, SliceN u R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut u Z), CutP u R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS u f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=u) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

theorem stStep {u R T E t k next st} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hn : ∀ s ∈ next, Impossible u (W T) k (s.map W).toFinset)
    (h : stOK u T t k next st = true) : Impossible u (W T) (k+1) (st.1.map W).toFinset := by
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
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have inOps : ∀ {o : Nat}, allowed u o → o ∈ opsOf u := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · have : o = 0 ∨ o = 1 := by omega
        simpa [opsOf] using this
      · exact Bool.noConfusion h
    · have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by rcases h with h | ⟨_,h⟩ <;> omega
      simpa [opsOf] using this
  have opk : ∀ {o : Nat}, allowed u o → opOK u o = true := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · simpa only [opOK,Bool.false_or,Nat.blt_eq] using h
      · exact Bool.noConfusion h
    · rfl
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp
  -- one unordered pair serves both orders
  have core : ∀ (o : Nat) (ja jb : Bool), allowed u o → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible u (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (inOps ho4)
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
    rcases hk with hk | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      have sub : ∀ x ∈ kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb, x < 2^128 := by
        intro x hx
        have hx' : x = nb o p.1 p.2.1 ∨ x ∈ st.1 := by
          unfold kidN at hx
          rw [mem_ins] at hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · right
            rw [pm]
            cases ja <;> cases jb <;> simp only [cond_true,cond_false,mem_ins] at hx <;> tauto
        rcases hx' with rfl | hx'
        · have l1 : p.1 < 2^128 := lt _ ((pm _).mpr (Or.inl rfl))
          have l2 : p.2.1 < 2^128 := lt _ ((pm _).mpr (Or.inr (Or.inl rfl)))
          have la : Nat.land p.1 p.2.1 < 2^128 := Nat.lt_of_le_of_lt (Nat.and_le_left) l1
          unfold nb
          cases Nat.beq o 0 <;> cases Nat.beq o 1 <;> cases Nat.beq o 2 <;>
            first | exact la | exact Nat.or_lt_two_pow l1 l2 | exact Nat.xor_lt_two_pow l1 la | exact Nat.xor_lt_two_pow l2 la
        · exact lt x hx'
      cases h1 : ty i 0
      · rw [h1,cond_false] at hi
        cases h2 : ty i 1
        · rw [h2,cond_false] at hi
          cases h3 : ty i 2
          · rw [h3,cond_false] at hi
            cases hg : t.perms[Nat.div i 4]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some l =>
              rw [hg] at hi
              obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hi
              rw [←kid_fin]
              apply perm_sound l (List.all_eq_true.mp ht.p l (List.mem_of_getElem? hg))
              have : (((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map (permN l)).map W).toFinset = (s.map W).toFinset := by
                rw [←beqL_ok e]
                ext v
                simp only [List.mem_toFinset,List.mem_map,mem_sortN]
              rw [this]
              exact hn s hs'
          · rw [h3,cond_true] at hi
            cases hg : t.kws[Nat.div i 4]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some q =>
              rw [hg] at hi
              simp only [Bool.and_eq_true,Bool.not_eq_true'] at hi
              obtain ⟨⟨hu,hlen⟩,hkw⟩ := hi
              rw [←kid_fin]
              have sz := Nat.eq_of_beq_eq_true hlen
              have nd' : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).Nodup := by
                apply List.dedup_eq_self.mp
                apply (List.dedup_sublist _).eq_of_length
                have c1 : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).toFinset.card = (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).length := by
                  rw [kid_fin,List.toFinset_card_of_nodup nk]
                rw [List.card_toFinset] at c1
                rw [c1,List.length_map]
                have il : ∀ (z : Nat) (l : List Nat), (ins z l).length = l.length + 1 := by
                  intro z l
                  induction l with
                  | nil => rfl
                  | cons x xs ih =>
                    unfold ins
                    cases Nat.ble z x
                    · rw [cond_false,List.length_cons,ih,List.length_cons]
                    · rfl
                unfold kidN kidW
                cases ja <;> cases jb <;> simp [kept,il]
              subst hu
              exact kw_sound nd' sz sub q (List.all_eq_true.mp ht.k q (List.mem_of_getElem? hg)) hkw
        · rw [h2,cond_true] at hi
          cases hg : t.seps[Nat.div i 4]? with
          | none => rw [hg] at hi; exact Bool.noConfusion hi
          | some q =>
            rw [hg] at hi
            exact sep_sound (List.all_eq_true.mp ht.s q (List.mem_of_getElem? hg)) hi
      · rw [h1,cond_true] at hi
        cases hg : t.cuts[Nat.div i 4]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (ht.c q (List.mem_of_getElem? hg)) (opk ho4) nk hi
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
  · have r := core d ka kb hd (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have r := core (flipOp d) kb ka hfl.1 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {u R T E t k D' D} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hI : LevelN u T k D') (h : levelOK u T t k (D'.map Prod.fst) D = true) : LevelN u T (k+1) D := by
  intro st hst
  refine stStep hB ht ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {u : Bool} {T : Nat} {t : Tabs} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK u T t k next ((D.drop (i*c)).take c) = true) : levelOK u T t k next D = true := by
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
theorem lowSearch {u R T E K D} (hB : baseOK T R E = true) (hI : LevelN u T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN u R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this


def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276682240 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[
    ⟨.and, [0, 2]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [8, 5]⟩,
    ⟨.and, [7, 4]⟩,
    ⟨.and, [7, 9]⟩,
    ⟨.or, [6, 9]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.or, [6, 13]⟩,
    ⟨.and, [14, 10]⟩,
    ⟨.or, [13, 11]⟩,
    ⟨.or, [15, 3]⟩,
    ⟨.and, [16, 17]⟩], 18⟩
theorem witnessMonotone : PEqualNP.MetaComplexity.Monotone2 smallCircuit := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel
theorem witnessSize : smallCircuit.size = 13 := rfl
def pw0 : Nat := 0x33333333333333333333333333333333
def pw1 : Nat := 0x55555555555555555555555555555555
def pw2 : Nat := 0xcccccccccccccccccccccccccccccccc
def pw3 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def pw4 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def pw5 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def pw6 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
def pw7 : Nat := 0x88888888888888888888888888888888
def pw8 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def pw9 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa
def pw10 : Nat := 0x30303030303030303030303030303030
def pw11 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def pw12 : Nat := 0x80808080808080808080808080808080
def pw13 : Nat := 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa
def pw14 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def pw15 : Nat := 0x2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa
def pw16 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
def pw17 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def pw18 : Nat := 0x11111111111111111111111111111111
def pw19 : Nat := 0x22222222222222222222222222222222
def pw20 : Nat := 0x44444444444444444444444444444444
def pw21 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc
def pw22 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def pw23 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def pw24 : Nat := 0xffccffccffccffccffccffccffccffcc
def pw25 : Nat := 0xfefefefefefefefefefefefefefefefe
def pw26 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee
def pw27 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def pw28 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def pw29 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe
def pw30 : Nat := 0x3030303030303030303030303030303
def pw31 : Nat := 0x50505050505050505050505050505050
def pw32 : Nat := 0x330033003300330033003300330033
def pw33 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00
def pw34 : Nat := 0x55005500550055005500550055005500
def pw35 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88
def pw36 : Nat := 0x44cc44cc44cc44cc44cc44cc44cc44cc
def pw37 : Nat := 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8
def pw38 : Nat := 0xff0cff0cff0cff0cff0cff0cff0cff0c
def pw39 : Nat := 0xc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0cc
def pw40 : Nat := 0xffff0000ffff0000ffff0000ffff0000
def pw41 : Nat := 0xffff0000ffff0000ffff0000ffff
def pw42 : Nat := 0xf000f000f000f000f000f000f000f000
def pw43 : Nat := 0xf0f00000f0f00000f0f00000f0f00000
def pw44 : Nat := 0xff000000ff000000ff000000ff000000
def pw45 : Nat := 0x8080808080808080808080808080808
def pw46 : Nat := 0x55550000555500005555000055550000
def pw47 : Nat := 0xf000f000f000f000f000f000f000f
def pw48 : Nat := 0xf0f00000f0f00000f0f00000f0f
def pw49 : Nat := 0x880088008800880088008800880088
def pw50 : Nat := 0x8888000088880000888800008888
def pw51 : Nat := 0x50005000500050005000500050005000
def pw52 : Nat := 0x20202020202020202020202020202020
def pw53 : Nat := 0x30003000300030003000300030003000
def pw54 : Nat := 0x33003300330033003300330033003300
def pw55 : Nat := 0x33330000333300003333000033330000
def pw56 : Nat := 0xcccc0000cccc0000cccc0000cccc0000
def pw57 : Nat := 0x44440000444400004444000044440000
def pw58 : Nat := 0xa0a00000a0a00000a0a00000a0a
def pw59 : Nat := 0xaa000000aa000000aa000000aa
def pw60 : Nat := 0xa000a000a000a000a000a000a000a000
def pw61 : Nat := 0x40404040404040404040404040404040
def pw62 : Nat := 0xf0000000f0000000f0000000f0000
def pw63 : Nat := 0x44004400440044004400440044004400
def pw64 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000
def pw65 : Nat := 0x22220000222200002222000022220000
def pw66 : Nat := 0x55000000550000005500000055000000
def pw67 : Nat := 0x22002200220022002200220022002200
def pw68 : Nat := 0x50500000505000005050000050500000
def pw69 : Nat := 0xf0000000f0000000f0000000f0
def pw70 : Nat := 0xcc000000cc000000cc000000cc
def pw71 : Nat := 0xc000c000c000c000c000c000c000c
def pw72 : Nat := 0xc0c00000c0c00000c0c00000c0c00000
def pw73 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
def pw74 : Nat := 0xf0f00000f0f00000f0f00000f0f0
def pw75 : Nat := 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8
def pw76 : Nat := 0x70707070707070707070707070707070
def pw77 : Nat := 0x2222aaaa2222aaaa2222aaaa2222aaaa
def pw78 : Nat := 0x3030f0f03030f0f03030f0f03030f0f0
def pw79 : Nat := 0xa2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2
def pw80 : Nat := 0xf0000000f0000000f0000000f0000000
def pw81 : Nat := 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0
def pw82 : Nat := 0xa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaa
def pw83 : Nat := 0xffff00f0ffff00f0ffff00f0ffff00f0
def pw84 : Nat := 0xf000f0f0f000f0f0f000f0f0f000f0f0
def pw85 : Nat := 0xffff8080ffff8080ffff8080ffff8080
def pw86 : Nat := 0x7070f0f07070f0f07070f0f07070f0f0
def pw87 : Nat := 0x88880000888800008888000088880000
def pw88 : Nat := 0x80008000800080008000800080008000
def pw89 : Nat := 0xf080f080f080f080f080f080f080f080
def pw90 : Nat := 0xf8f80000f8f80000f8f80000f8f8
def pw91 : Nat := 0x77770000777700007777000077770000
def pw92 : Nat := 0x70007000700070007000700070007000
def pw93 : Nat := 0x8080f0f08080f0f08080f0f08080f0f0
def pw94 : Nat := 0x88808880888088808880888088808880
def pw95 : Nat := 0x77707770777077707770777077707770
def pw96 : Nat := 0x8888f8f88888f8f88888f8f88888f8f8
def pw97 : Nat := 0x80808888808088888080888880808888
def pw98 : Nat := 0x2020a0a02020a0a02020a0a02020a0a0
def pw99 : Nat := 0xb030b030b030b030b030b030b030b030
def pw100 : Nat := 0x22aaaaaa22aaaaaa22aaaaaa22aaaaaa
def pw101 : Nat := 0xa0000000a0000000a0000000a0000000
def pw102 : Nat := 0x30f0f0f030f0f0f030f0f0f030f0f0f0
def pw103 : Nat := 0x8080aaaa8080aaaa8080aaaa8080aaaa
def pw104 : Nat := 0x3000f0003000f0003000f0003000f000
def pw105 : Nat := 0xa000f0f0a000f0f0a000f0f0a000f0f0
def pw106 : Nat := 0xeac0eac0eac0eac0eac0eac0eac0eac0
def pw107 : Nat := 0xc0c0ccccc0c0ccccc0c0ccccc0c0cccc
def pw108 : Nat := 0xf000ff00f000ff00f000ff00f000ff00
def pw109 : Nat := 0xaaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa
def pw110 : Nat := 0x222222aa222222aa222222aa222222aa
def pw111 : Nat := 0x2222a2a22222a2a22222a2a22222a2a2
def pw112 : Nat := 0x77778888777788887777888877778888
def pw113 : Nat := 0xf800f800f800f800f800f800f800f800
def pw114 : Nat := 0x70f0f0f070f0f0f070f0f0f070f0f0f0
def pw115 : Nat := 0xff88ff00ff88ff00ff88ff00ff88ff00
def pw116 : Nat := 0x7700ff007700ff007700ff007700ff00
def pw117 : Nat := 0x8888f0f08888f0f08888f0f08888f0f0
def pw118 : Nat := 0x7000f0f07000f0f07000f0f07000f0f0
def pw119 : Nat := 0x707070f0707070f0707070f0707070f0
def pw120 : Nat := 0xf0f000f0f0f000f0f0f000f0f0f000f0
def pw121 : Nat := 0x2aaaaaaa2aaaaaaa2aaaaaaa2aaaaaaa
def pw122 : Nat := 0xaa000000aa000000aa000000aa00
def pw123 : Nat := 0x3333000033330000333300003333
def pw124 : Nat := 0xaa000000aa000000aa000000aa0000
def pw125 : Nat := 0xa000a000a000a000a000a000a000a
def pw126 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00
def pw127 : Nat := 0x4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c
def pw128 : Nat := 0x88008800880088008800880088008800
def pw129 : Nat := 0x5f005f005f005f005f005f005f005f00
def pw130 : Nat := 0xaf00af00af00af00af00af00af00af00
def pw131 : Nat := 0x4444cccc4444cccc4444cccc4444cccc
def pw132 : Nat := 0x5500ff005500ff005500ff005500ff00
def pw133 : Nat := 0x8888cccc8888cccc8888cccc8888cccc
def pw134 : Nat := 0xeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaa
def pw135 : Nat := 0xa0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa
def pw136 : Nat := 0x4c4ccccc4c4ccccc4c4ccccc4c4ccccc
def pw137 : Nat := 0x5f00ff005f00ff005f00ff005f00ff00
def pw138 : Nat := 0x4400ff004400ff004400ff004400ff00
def pw139 : Nat := 0x4c0c4c0c4c0c4c0c4c0c4c0c4c0c4c0c
def pw140 : Nat := 0xc888c888c888c888c888c888c888c888
def pw141 : Nat := 0xee00aa00ee00aa00ee00aa00ee00aa00
def pw142 : Nat := 0xf000f000f000f000f000f000f000f00
def pw143 : Nat := 0xf0f00000f0f00000f0f00000f0f0000
def pw144 : Nat := 0x5050505050505050505050505050505
def pw145 : Nat := 0xfafafafafafafafafafafafafafafafa
def pw146 : Nat := 0xffffffff00000000ffffffff
def pw147 : Nat := 0xffffffff00000000ffffffff00000000
def pw148 : Nat := 0xff000000ff000000ff000000ff0000
def pw149 : Nat := 0xff000000ff000000ff000000ff00
def pw150 : Nat := 0xffff000000000000ffff000000000000
def pw151 : Nat := 0xff00ff0000000000ff00ff00
def pw152 : Nat := 0xffff000000000000ffff0000
def pw153 : Nat := 0xa0a0a0a000000000a0a0a0a0
def pw154 : Nat := 0x888888880000000088888888
def pw155 : Nat := 0xc0c0c0c000000000c0c0c0c0
def pw156 : Nat := 0xf000f000f000f000f000f000f000f0
def pw157 : Nat := 0xf0000000f0000000f0000000f00000
def pw158 : Nat := 0xf0f0000000000000f0f000000000000
def pw159 : Nat := 0x300030000000000030003000000000
def pw160 : Nat := 0x303000003030000030300000303
def pw161 : Nat := 0x500050000000000050005000000000
def pw162 : Nat := 0x505000005050000050500000505
def pw163 : Nat := 0x3000300030003000300030003000300
def pw164 : Nat := 0x5000500050005000500050005000500
def pw165 : Nat := 0x55550000000000005555000000000000
def pw166 : Nat := 0xc000c00000000000c000c00000000
def pw167 : Nat := 0xa000a00000000000a000a00000000
def pw168 : Nat := 0xff00ff0000000000ff00ff00000000
def pw169 : Nat := 0xcc000000cc000000cc000000cc0000
def pw170 : Nat := 0x1111000011110000111100001111
def pw171 : Nat := 0x440044000000000044004400000000
def pw172 : Nat := 0x11001100110011001100110011001100
def pw173 : Nat := 0xff00ff0000000000ff00ff
def pw174 : Nat := 0x550000000000000055000000
def pw175 : Nat := 0x111111110000000011111111
def pw176 : Nat := 0x2020202020202020202020202020202
def pw177 : Nat := 0xf000f00000000000f000f00000000
def pw178 : Nat := 0x10101010101010101010101010101010
def pw179 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaa
def pw180 : Nat := 0xaaaaaaaa00000000aaaaaaaa
def pw181 : Nat := 0xffffffffff00ff00ffffffffff00ff00
def pw182 : Nat := 0x3f3f00003f3f00003f3f00003f3f0000
def pw183 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0
def pw184 : Nat := 0xeeee0000eeee0000eeee0000eeee0000
def pw185 : Nat := 0xff0aff0aff0aff0aff0aff0aff0aff0a
def pw186 : Nat := 0xafaf0000afaf0000afaf0000afaf0000
def pw187 : Nat := 0xffffffffccccccccffffffffcccccccc
def pw188 : Nat := 0xffaa0000ffaa0000ffaa0000ffaa0000
def pw189 : Nat := 0xff0f0000ff0f0000ff0f0000ff0f0000
def pw190 : Nat := 0xffaaff00ffaaff00ffaaff00ffaaff00
def pw191 : Nat := 0xff0fff00ff0fff00ff0fff00ff0fff00
def pw192 : Nat := 0xff00ff00aa00aa00ff00ff00aa00aa
def pw193 : Nat := 0xff00ff00ffaaffaaff00ff00ffaaffaa
def pw194 : Nat := 0xffffffffff000000ffffffffff000000
def pw195 : Nat := 0xff00ff00ffffff00ff00ff00ffffff00
def pw196 : Nat := 0x3f2a3f2a3f2a3f2a3f2a3f2a3f2a3f2a
def pw197 : Nat := 0xfff00000fff00000fff00000fff00000
def pw198 : Nat := 0x88f888f888f888f888f888f888f888f8
def pw199 : Nat := 0x8f888f888f888f888f888f888f888f88
def pw200 : Nat := 0xeaeac0c0eaeac0c0eaeac0c0eaeac0c0
def pw201 : Nat := 0xfff0ff00fff0ff00fff0ff00fff0ff00
def pw202 : Nat := 0x8f8f88888f8f88888f8f88888f8f8888
def pw203 : Nat := 0x3f3f3f3f2a2a2a2a3f3f3f3f2a2a2a2a
def pw204 : Nat := 0x88888888f8f8f8f888888888f8f8f8f8
def pw205 : Nat := 0xff00ff00fff0fff0ff00ff00fff0fff0
def pw206 : Nat := 0xff888888ff888888ff888888ff888888
def pw207 : Nat := 0x3f3f3f3f3f003f003f3f3f3f3f003f00
def pw208 : Nat := 0xeee0eee0eee0eee0eee0eee0eee0eee
def pw209 : Nat := 0xeee0eee0eee0eee0eee0eee0eee0eee0
def pw210 : Nat := 0xee0eee0eee0eee0eee0eee0eee0eee0e
def pw211 : Nat := 0xa8fca8fca8fca8fca8fca8fca8fca8fc
def pw212 : Nat := 0xe0eeeee0e0eeeee0e0eeeee0e0eeeee
def pw213 : Nat := 0xa8a8fcfca8a8fcfca8a8fcfca8a8fcfc
def pw214 : Nat := 0xeeeeeeeee0e0e0e0eeeeeeeee0e0e0e0
def pw215 : Nat := 0xeeeeeeee0e0e0e0eeeeeeeee0e0e0e0e
def pw216 : Nat := 0xeeeeee00eeeeee00eeeeee00eeeeee
def pw217 : Nat := 0xeeeeeeeeee00ee00eeeeeeeeee00ee00
def pw218 : Nat := 0xae0cae0cae0cae0cae0cae0cae0cae0c
def pw219 : Nat := 0xaf8caf8caf8caf8caf8caf8caf8caf8c
def pw220 : Nat := 0xffcc0000ffcc0000ffcc0000ffcc0000
def pw221 : Nat := 0xace0ace0ace0ace0ace0ace0ace0ace
def pw222 : Nat := 0xff330000ff330000ff330000ff330000
def pw223 : Nat := 0x2f222f222f222f222f222f222f222f22
def pw224 : Nat := 0xaeae0c0caeae0c0caeae0c0caeae0c0c
def pw225 : Nat := 0xffccff00ffccff00ffccff00ffccff00
def pw226 : Nat := 0x2f2f22222f2f22222f2f22222f2f2222
def pw227 : Nat := 0xff33ff00ff33ff00ff33ff00ff33ff00
def pw228 : Nat := 0xafafafaf8c8c8c8cafafafaf8c8c8c8c
def pw229 : Nat := 0xa0a0a0acececece0a0a0a0acececece
def pw230 : Nat := 0xff0a0a0aff0a0a0aff0a0a0aff0a0a0a
def pw231 : Nat := 0xafafafafaf00af00afafafafaf00af00
def pw232 : Nat := 0xfff0fff0aaa0aaa0fff0fff0aaa0aaa
def pw233 : Nat := 0xaa00aa00eecceeccaa00aa00eecceecc
def pw234 : Nat := 0xffaaffaacc88cc88ffaaffaacc88cc88
def pw235 : Nat := 0xffaaffaa0f0a0f0affaaffaa0f0a0f0a
def pw236 : Nat := 0xff0fff0faa0aaa0aff0fff0faa0aaa0a
def pw237 : Nat := 0xaa00aacceeccee00aa00aacceeccee
def pw238 : Nat := 0xaaffaaff88cc88ccaaffaaff88cc88cc
def pw239 : Nat := 0xf000f00afaaafaa0f000f00afaaafaa
def pw240 : Nat := 0xffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0
def pw241 : Nat := 0xeee0ee00eee0ee00eee0ee00eee0ee00
def pw242 : Nat := 0xf0f0f0f000000000f0f0f0f000000000
def pw243 : Nat := 0xf0f0f0f000000000f0f0f0f00000000
def pw244 : Nat := 0xa8a8a8a8a800a800a8a8a8a8a800a800
def pw245 : Nat := 0xfcfcfcfcfc00fc00fcfcfcfcfc00fc00
def pw246 : Nat := 0x202020202aa02aa0202020202aa02aa
def pw247 : Nat := 0xe0e0e0e0e000e000e0e0e0e0e000e000
def pw248 : Nat := 0xe0e0e00eeeeee000e0e0e00eeeeee
def p1_T : Nat := 0x88888888888888888888888888888888
def p1_R : List Nat := [0, 1]
def p1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem p1_B : baseOK p1_T p1_R p1_E = true := by decide +kernel
theorem p1_L : LowN true p1_R p1_T 1 := lowCount p1_B (by decide +kernel)
def p2_T : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def p2_R : List Nat := [0, 1]
def p2_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
theorem p2_L : LowN true p2_R p2_T 1 := lowCount p2_B (by decide +kernel)
def p3_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def p3_R : List Nat := [0, 1, 2]
def p3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
def p3_Z : List SliceD := [(pw0,1,[0, 2]),(pw1,1,[1, 2]),(pw2,1,[0, 2]),(pw3,1,[1, 2]),(pw4,1,[0, 1]),(pw5,1,[0, 1])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN true p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=2) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=1) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p3_B p2_B p2_L (by decide +kernel),by simp⟩
def p3_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def p3_t : Tabs := (p3_C.map (mkCut true p3_Z),[(5,4),(3,1),(3,0),(3,2),(6,2),(5,1)],[],[])
theorem p3_W : TabsP true p3_R p3_T p3_t := ⟨cutsGood p3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D3 : List StD := [
([pw3,pw2,pw5],[0,4,8,12,1,5,16,20,9,13,17,21],[319,602,3237])]
def p3_D2 : List StD := []
theorem p3_I2 : LevelN true p3_T 2 p3_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C3x0 : levelOK true p3_T p3_t 2 (p3_D2.map Prod.fst) ((p3_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p3_I3 : LevelN true p3_T 3 p3_D3 := levelStep p3_B p3_W p3_I2 (chunks 32 p3_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C3x0
  ))
theorem p3_L : LowN true p3_R p3_T 4 := lowSearch p3_B p3_I3 (by decide +kernel)
def p4_T : Nat := 0x80808080808080808080808080808080
def p4_R : List Nat := [0, 1, 2]
def p4_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
theorem p4_L : LowN true p4_R p4_T 2 := lowCount p4_B (by decide +kernel)
def p5_T : Nat := 0xe880e880e880e880e880e880e880e880
def p5_R : List Nat := [0, 1, 2, 3]
def p5_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
def p5_Z : List SliceD := [(pw3,4,[1, 2, 3]),(pw2,4,[0, 2, 3]),(pw5,4,[0, 1, 3]),(pw6,4,[0, 1, 2]),(pw1,2,[1, 2, 3]),(pw7,1,[2, 3]),(pw0,2,[0, 2, 3]),(pw4,2,[0, 1, 3]),(pw8,1,[1, 3]),(pw9,1,[1, 2]),(pw10,1,[0, 3]),(pw11,1,[0, 3])]
theorem p5_Y : ∀ s ∈ p5_Z, SliceN true p5_R p5_T s := by
  unfold p5_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=2) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=4) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=8) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p5_B p4_B p4_L (by decide +kernel),mkSlice (w:=3) p5_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p5_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p5_B p4_B p4_L (by decide +kernel),mkSlice (w:=1) p5_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p5_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p5_B p1_B p1_L (by decide +kernel),mkSlice (w:=2) p5_B p1_B p1_L (by decide +kernel),by simp⟩
def p5_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(2,[128]),(3,[128]),(2,[130]),(0,[130]),(0,[131]),(0,[128]),(1,[128]),(6,[]),(7,[]),(2,[256]),(8,[]),(0,[260]),(2,[258]),(9,[]),(3,[258]),(3,[256]),(10,[]),(11,[]),(2,[128,270]),(2,[258,143]),(3,[130,268]),(3,[130,271]),(2,[130,268]),(2,[130,271]),(3,[260,15]),(2,[260,15]),(1,[260,15]),(6,[128]),(3,[256,260]),(4,[128]),(3,[128,260]),(3,[128,256])]
def p5_t : Tabs := (p5_C.map (mkCut true p5_Z),[(13,12),(14,12),(7,5),(11,10),(14,10),(7,6),(14,6),(11,9),(13,9),(13,5),(7,3),(11,3),(11,2),(13,4),(11,0),(13,0),(14,0)],[],[[],[1],[2,1],[0,1],[0,2,1],[1,0,2,1],[2],[1,0,2,1,0],[0],[0,2],[2,1,0]])
theorem p5_W : TabsP true p5_R p5_T p5_t := ⟨cutsGood p5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D6 : List StD := [
([pw3,pw2,pw5,pw6],[0,4,8,12,1,5,9,17,13,21,25,29,33,37,41,45,3,7,11,15,19,23],[65651,131477,263705,530470,1056874,2146444])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D5 : List StD := [
([pw7,pw3,pw2,pw5,pw6],[0,4,33,37,16,20,24,28,41,45,3,27,8,12,17,25,23,31,35,39],[3,1,70964,141880,3,17473,34945,262214,524426,780])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D4 : List StD := [
([pw12,pw3,pw2,pw5,pw6],[16,44,24,48,12,32,36,40,52,56,43],[32,64,128,1041,3,3,3,14,264,516]),
([pw13,pw3,pw2,pw5,pw6],[16,64,60,68,72,4,76,80],[4,35,13,7,3,9,3,18,192,18]),
([pw7,pw14,pw2,pw5,pw6],[24,48,0,16,28,32,52,56,84,88,92,49,53,3],[33,4,131,2312,67,4,4120,8195,514,1025])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D3 : List StD := [
([pw15,pw2,pw5,pw6],[120,124,128,0,96,100,104,108,112,116],[56,208,776,7,7,7]),
([pw7,pw14,pw16,pw6],[44,8,132,32,40,136,140,144,148,57,61,65],[11,3,548,17,1216,2308])]
def p5_D2 : List StD := []
theorem p5_I2 : LevelN true p5_T 2 p5_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C3x0 : levelOK true p5_T p5_t 2 (p5_D2.map Prod.fst) ((p5_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I3 : LevelN true p5_T 3 p5_D3 := levelStep p5_B p5_W p5_I2 (chunks 32 p5_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C4x0 : levelOK true p5_T p5_t 3 (p5_D3.map Prod.fst) ((p5_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I4 : LevelN true p5_T 4 p5_D4 := levelStep p5_B p5_W p5_I3 (chunks 32 p5_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C5x0 : levelOK true p5_T p5_t 4 (p5_D4.map Prod.fst) ((p5_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I5 : LevelN true p5_T 5 p5_D5 := levelStep p5_B p5_W p5_I4 (chunks 32 p5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C6x0 : levelOK true p5_T p5_t 5 (p5_D5.map Prod.fst) ((p5_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I6 : LevelN true p5_T 6 p5_D6 := levelStep p5_B p5_W p5_I5 (chunks 32 p5_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C6x0
  ))
theorem p5_L : LowN true p5_R p5_T 7 := lowSearch p5_B p5_I6 (by decide +kernel)
def p6_T : Nat := 0xfefefefefefefefefefefefefefefefe
def p6_R : List Nat := [0, 1, 2]
def p6_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
theorem p6_L : LowN true p6_R p6_T 2 := lowCount p6_B (by decide +kernel)
def p7_T : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def p7_R : List Nat := [0, 1, 2, 3]
def p7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
def p7_Z : List SliceD := [(pw1,4,[1, 2, 3]),(pw0,4,[0, 2, 3]),(pw4,4,[0, 1, 3]),(pw17,4,[0, 1, 2]),(pw18,1,[2, 3]),(pw19,1,[2, 3]),(pw20,1,[2, 3]),(pw3,2,[1, 2, 3]),(pw2,2,[0, 2, 3]),(pw5,2,[0, 1, 3]),(pw9,1,[1, 2]),(pw6,2,[0, 1, 2]),(pw21,1,[0, 2])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN true p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=2) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=1) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=2) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=4) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=1) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=8) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=2) p7_B p2_B p2_L (by decide +kernel),by simp⟩
def p7_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(2,[129]),(3,[129]),(4,[]),(0,[257]),(1,[257]),(5,[]),(1,[259]),(6,[]),(0,[259]),(2,[261]),(2,[257]),(0,[129]),(1,[129]),(1,[131]),(7,[]),(0,[131]),(8,[]),(0,[130]),(9,[]),(10,[]),(0,[258]),(11,[]),(12,[]),(0,[257,261]),(8,[261]),(0,[129,261]),(0,[129,257]),(0,[261,385]),(3,[263]),(1,[262,13]),(1,[131,270]),(0,[262,13]),(0,[131,270]),(0,[258,141]),(0,[130,270]),(0,[260]),(0,[129,270]),(1,[129,270])]
def p7_t : Tabs := (p7_C.map (mkCut true p7_Z),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(6,4),(6,2),(10,8),(10,2),(12,8),(12,4),(7,8)],[],[[],[1],[2,1],[0,1],[0,2,1],[1,0,2,1],[0,1,2],[0,1,2,1],[1,2],[1,2,1],[2],[1,0]])
theorem p7_W : TabsP true p7_R p7_T p7_t := ⟨cutsGood p7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D6 : List StD := [
([pw3,pw2,pw5,pw6],[0,4,8,12,1,9,5,13,17,21,25,29,33,37,41,45,3,7,11,15,19,23],[65651,131285,262937,527398,1060906,2146444])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D5 : List StD := [
([pw3,pw2,pw22,pw5,pw6],[0,4,16,20,13,24,21,41,45,3,43,8,12,29,37,27,31,35,39],[3,2,32789,65609,1,139270,278538,3764,5992,404])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D4 : List StD := [
([pw3,pw2,pw5,pw23,pw24],[28,32,36,44,40,48,52,56,13,29,47],[1027,5,16,7,10,11,32,580,392,3]),
([pw3,pw2,pw5,pw25,pw6],[16,60,64,72,12,68,76,80,84,88,3],[7,7,32,10,7,64,132,256,513,1048]),
([pw26,pw3,pw2,pw5,pw6],[92,24,100,0,4,8,20,28,96,104],[24,24,35,128,257,3,70,514,5,5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D3 : List StD := [
([pw3,pw27,pw24,pw28],[112,4,12,1,108,116,120,124,128,5,49],[1041,41,584,388,7,3]),
([pw29,pw3,pw2,pw5],[132,160,72,0,80,136,140,144,148,152,156,164],[41,193,1793,6,6,2066])]
def p7_D2 : List StD := []
theorem p7_I2 : LevelN true p7_T 2 p7_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C3x0 : levelOK true p7_T p7_t 2 (p7_D2.map Prod.fst) ((p7_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I3 : LevelN true p7_T 3 p7_D3 := levelStep p7_B p7_W p7_I2 (chunks 32 p7_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C4x0 : levelOK true p7_T p7_t 3 (p7_D3.map Prod.fst) ((p7_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I4 : LevelN true p7_T 4 p7_D4 := levelStep p7_B p7_W p7_I3 (chunks 32 p7_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C5x0 : levelOK true p7_T p7_t 4 (p7_D4.map Prod.fst) ((p7_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I5 : LevelN true p7_T 5 p7_D5 := levelStep p7_B p7_W p7_I4 (chunks 32 p7_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C6x0 : levelOK true p7_T p7_t 5 (p7_D5.map Prod.fst) ((p7_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I6 : LevelN true p7_T 6 p7_D6 := levelStep p7_B p7_W p7_I5 (chunks 32 p7_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C6x0
  ))
theorem p7_L : LowN true p7_R p7_T 7 := lowSearch p7_B p7_I6 (by decide +kernel)
def p8_T : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
def p8_R : List Nat := [0, 1, 2, 3]
def p8_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,6,14)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
def p8_Z : List SliceD := [(pw6,4,[0, 1, 2])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN true p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=8) p8_B p3_B p3_L (by decide +kernel),by simp⟩
def p8_C : List (Nat × List Nat) := [(0,[])]
def p8_t : Tabs := (p8_C.map (mkCut true p8_Z),[],[],[])
theorem p8_W : TabsP true p8_R p8_T p8_t := ⟨cutsGood p8_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p8_D4 : List StD := [
([pw3,pw2,pw5,pw6],[0],[1,1,1,1,1,1])]
def p8_D3 : List StD := []
theorem p8_I3 : LevelN true p8_T 3 p8_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p8_C4x0 : levelOK true p8_T p8_t 3 (p8_D3.map Prod.fst) ((p8_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p8_I4 : LevelN true p8_T 4 p8_D4 := levelStep p8_B p8_W p8_I3 (chunks 32 p8_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C4x0
  ))
theorem p8_L : LowN true p8_R p8_T 5 := lowSearch p8_B p8_I4 (by decide +kernel)
def p9_T : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
def p9_R : List Nat := [0, 1, 2, 3]
def p9_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
def p9_Z : List SliceD := [(pw1,4,[1, 2, 3])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN true p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p9_B p3_B p3_L (by decide +kernel),by simp⟩
def p9_C : List (Nat × List Nat) := [(0,[])]
def p9_t : Tabs := (p9_C.map (mkCut true p9_Z),[],[],[])
theorem p9_W : TabsP true p9_R p9_T p9_t := ⟨cutsGood p9_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D4 : List StD := [
([pw3,pw2,pw5,pw6],[0],[1,1,1,1,1,1])]
def p9_D3 : List StD := []
theorem p9_I3 : LevelN true p9_T 3 p9_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C4x0 : levelOK true p9_T p9_t 3 (p9_D3.map Prod.fst) ((p9_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p9_I4 : LevelN true p9_T 4 p9_D4 := levelStep p9_B p9_W p9_I3 (chunks 32 p9_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C4x0
  ))
theorem p9_L : LowN true p9_R p9_T 5 := lowSearch p9_B p9_I4 (by decide +kernel)
def p10_T : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def p10_R : List Nat := [0, 1, 2]
def p10_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
theorem p10_L : LowN true p10_R p10_T 2 := lowCount p10_B (by decide +kernel)
def p11_T : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def p11_R : List Nat := [0, 1, 2]
def p11_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
theorem p11_L : LowN true p11_R p11_T 2 := lowCount p11_B (by decide +kernel)
def p12_T : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
def p12_R : List Nat := [0, 1, 2, 3]
def p12_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
def p12_Z : List SliceD := [(pw2,2,[0, 2, 3]),(pw3,2,[1, 2, 3]),(pw1,2,[1, 2, 3]),(pw0,2,[0, 2, 3]),(pw19,1,[2, 3]),(pw20,1,[2, 3]),(pw30,1,[0, 3]),(pw31,1,[1, 3]),(pw8,1,[1, 3]),(pw16,1,[0, 3]),(pw17,2,[0, 1, 2]),(pw9,1,[1, 2]),(pw6,2,[0, 1, 2]),(pw4,2,[0, 1, 3]),(pw32,1,[0, 2]),(pw33,1,[0, 2]),(pw34,1,[1, 2])]
theorem p12_Y : ∀ s ∈ p12_Z, SliceN true p12_R p12_T s := by
  unfold p12_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=2) p12_B p10_B p10_L (by decide +kernel),mkSlice (w:=1) p12_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p12_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=2) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=6) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=8) p12_B p10_B p10_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=0) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=10) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=8) p12_B p1_B p1_L (by decide +kernel),by simp⟩
def p12_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[])]
def p12_t : Tabs := (p12_C.map (mkCut true p12_Z),[(5,4),(14,12),(3,2),(3,1),(14,10),(5,1),(14,6),(9,8),(9,1),(5,6),(9,0),(3,0),(11,1),(7,1)],[],[[],[1,2],[1],[2],[2,1],[1,2,1]])
theorem p12_W : TabsP true p12_R p12_T p12_t := ⟨cutsGood p12_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D5 : List StD := [
([pw3,pw2,pw5,pw6],[3,1,5,13,17,21,25,33,7,15,9,11,19,29,23],[1295,3634,12483,829,17101,6640])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D4 : List StD := [
([pw7,pw3,pw2,pw5,pw6],[8,12,16,20,0,4,24,28,37,3,7,15,23],[16,32,3073,4609,259,5,5,10,10,192]),
([pw3,pw2,pw22,pw5,pw6],[0,4,16,20,8,12,32,36,37,3,11,15,19],[259,32,10,10,16,5,5,3073,4609,192]),
([pw9,pw3,pw2,pw5,pw6],[44,8,48,4,20,28,40,13,41],[64,3,3,8,3,3,262,176,5,5]),
([pw20,pw3,pw2,pw5,pw6],[20,12,4,0,8,32,44,25,45],[8,16,3,3,262,5,5,3,3,224]),
([pw3,pw16,pw2,pw5,pw6],[36,12,52,20,28,32,56,41,3],[3,3,5,224,16,8,3,262,3,5]),
([pw3,pw2,pw5,pw27,pw6],[24,28,0,12,32,36,60,9,3],[7,33,5,194,262,16,5,8,3,3]),
([pw21,pw3,pw2,pw5,pw6],[12,9,64,16,60,0,24,44,56,49,7,15],[3,128,3073,32,3,14,26,17,517,324])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D3 : List StD := [
([pw3,pw2,pw5,pw35],[60,8,12,16,0,28,32],[7,10,11,5,20,97]),
([pw36,pw3,pw5,pw6],[8,12,0,16,28,32,24],[7,50,38,9,9,80]),
([pw3,pw37,pw5,pw6],[32,36,8,24,16,28],[5,26,33,5,10,3]),
([pw26,pw3,pw2,pw5],[32,16,8,64,0,28],[5,6,33,9,10,19]),
([pw3,pw16,pw27,pw6],[24,28,36,16,53],[7,5,10,16,5,3]),
([pw3,pw2,pw5,pw38],[24,28,36,16,60],[7,5,10,26,5,3]),
([pw3,pw39,pw5,pw6],[24,36,16,28,8,60],[19,3,12,44,3,3])]
def p12_D2 : List StD := []
theorem p12_I2 : LevelN true p12_T 2 p12_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C3x0 : levelOK true p12_T p12_t 2 (p12_D2.map Prod.fst) ((p12_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I3 : LevelN true p12_T 3 p12_D3 := levelStep p12_B p12_W p12_I2 (chunks 32 p12_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C4x0 : levelOK true p12_T p12_t 3 (p12_D3.map Prod.fst) ((p12_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I4 : LevelN true p12_T 4 p12_D4 := levelStep p12_B p12_W p12_I3 (chunks 32 p12_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C5x0 : levelOK true p12_T p12_t 4 (p12_D4.map Prod.fst) ((p12_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I5 : LevelN true p12_T 5 p12_D5 := levelStep p12_B p12_W p12_I4 (chunks 32 p12_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C5x0
  ))
theorem p12_L : LowN true p12_R p12_T 6 := lowSearch p12_B p12_I5 (by decide +kernel)
def p13_T : Nat := 0xfee8eaa8fee8eaa8fee8eaa8fee8eaa8
def p13_R : List Nat := [0, 1, 2, 3, 4]
def p13_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,6,22)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
def p13_Z : List SliceD := [(pw1,7,[1, 2, 3, 4]),(pw40,7,[0, 1, 2, 3]),(pw0,5,[0, 2, 3, 4]),(pw4,5,[0, 1, 3, 4]),(pw6,5,[0, 1, 2, 4]),(pw17,5,[0, 1, 2, 4]),(pw41,6,[0, 1, 2, 3]),(pw2,5,[0, 2, 3, 4]),(pw5,5,[0, 1, 3, 4])]
theorem p13_Y : ∀ s ∈ p13_Z, SliceN true p13_R p13_T s := by
  unfold p13_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p13_B p5_B p5_L (by decide +kernel),mkSlice (w:=16) p13_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel),mkSlice (w:=8) p13_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p13_B p12_B p12_L (by decide +kernel),mkSlice (w:=2) p13_B p9_B p9_L (by decide +kernel),mkSlice (w:=4) p13_B p9_B p9_L (by decide +kernel),by simp⟩
def p13_C : List (Nat × List Nat) := [(0,[]),(1,[]),(0,[128]),(2,[]),(3,[]),(1,[260]),(0,[130]),(0,[131]),(4,[]),(5,[]),(6,[]),(0,[129]),(7,[]),(1,[261]),(8,[]),(0,[258]),(0,[256]),(0,[257]),(1,[390]),(0,[129,128]),(1,[260,261]),(4,[261]),(5,[261]),(6,[261]),(5,[260]),(4,[260])]
def p13_t : Tabs := (p13_C.map (mkCut true p13_Z),[(3,2),(5,4),(9,8),(3,1),(5,1),(14,12),(14,10),(9,1),(14,6),(28,12),(22,6),(26,10),(7,6),(26,24),(28,24),(22,20),(22,18),(11,1),(28,20),(3,6),(3,0),(7,1)],[],[[],[2],[1,2],[1,2,1],[1],[2,1]])
theorem p13_W : TabsP true p13_R p13_T p13_t := ⟨cutsGood p13_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D8 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0,4,1,37,5,13,17,21,25,29,33,41,3,7,11,9,45,15,19,23],[21,21,32773,7,29152,145056,2058,804672,65546,2058])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D7 : List StD := [
([pw3,pw16,pw2,pw5,pw6,pw40],[12,8,16,20,49,13,17,24,28,32,36,40,9,33,41,45,53,57,3],[19,19,22,4114,26,129,261,9729,2057,262149,65569,41,131140,76,49160]),
([pw3,pw2,pw5,pw27,pw6,pw40],[48,16,44,52,56,5,9,21,25,24,32,36,40,1,29,41,45,61,65,3],[37,8230,69,100,44,524307,3,131201,137,529,262418,282,19457,4105,98312]),
([pw21,pw3,pw2,pw5,pw6,pw40],[12,60,72,1,32,21,29,4,16,40,56,64,68,5,41,45,53,65,69,73],[11,2049,132353,4097,645,11,8202,26,14,65569,262161,37,524368,49156,84])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D6 : List StD := [
([pw3,pw16,pw27,pw6,pw40],[12,56,76,80,9,13,84,88,92,96,100,1,29,33,41,45,77,81,85],[65541,131078,2068,28,262147,8385,265,5666,42,49160])]
def p13_D5 : List StD := []
theorem p13_I5 : LevelN true p13_T 5 p13_D5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x0 : levelOK true p13_T p13_t 5 (p13_D5.map Prod.fst) ((p13_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p13_I6 : LevelN true p13_T 6 p13_D6 := levelStep p13_B p13_W p13_I5 (chunks 32 p13_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x0 : levelOK true p13_T p13_t 6 (p13_D6.map Prod.fst) ((p13_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p13_I7 : LevelN true p13_T 7 p13_D7 := levelStep p13_B p13_W p13_I6 (chunks 32 p13_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C8x0 : levelOK true p13_T p13_t 7 (p13_D7.map Prod.fst) ((p13_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p13_I8 : LevelN true p13_T 8 p13_D8 := levelStep p13_B p13_W p13_I7 (chunks 32 p13_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C8x0
  ))
theorem p13_L : LowN true p13_R p13_T 9 := lowSearch p13_B p13_I8 (by decide +kernel)
def p14_T : Nat := 0xe888e888e888e888e888e888e888e888
def p14_R : List Nat := [0, 1, 2, 3]
def p14_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,9,13),(3,5,13)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
def p14_Z : List SliceD := [(pw5,4,[0, 1, 3])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN true p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=4) p14_B p3_B p3_L (by decide +kernel),by simp⟩
def p14_C : List (Nat × List Nat) := [(0,[])]
def p14_t : Tabs := (p14_C.map (mkCut true p14_Z),[],[],[])
theorem p14_W : TabsP true p14_R p14_T p14_t := ⟨cutsGood p14_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D4 : List StD := [
([pw3,pw2,pw5,pw6],[0],[1,1,1,1,1,1])]
def p14_D3 : List StD := []
theorem p14_I3 : LevelN true p14_T 3 p14_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C4x0 : levelOK true p14_T p14_t 3 (p14_D3.map Prod.fst) ((p14_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p14_I4 : LevelN true p14_T 4 p14_D4 := levelStep p14_B p14_W p14_I3 (chunks 32 p14_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C4x0
  ))
theorem p14_L : LowN true p14_R p14_T 5 := lowSearch p14_B p14_I4 (by decide +kernel)
def p15_T : Nat := 0x80008000800080008000800080008000
def p15_R : List Nat := [0, 1, 2, 3]
def p15_E : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15)]
theorem p15_B : baseOK p15_T p15_R p15_E = true := by decide +kernel
theorem p15_L : LowN true p15_R p15_T 3 := lowCount p15_B (by decide +kernel)
def p16_T : Nat := 0xe8888880e8888880e8888880e8888880
def p16_R : List Nat := [0, 1, 2, 3, 4]
def p16_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,3,19)]
theorem p16_B : baseOK p16_T p16_R p16_E = true := by decide +kernel
def p16_Z : List SliceD := [(pw3,6,[1, 2, 3, 4]),(pw2,6,[0, 2, 3, 4]),(pw5,5,[0, 1, 3, 4]),(pw6,5,[0, 1, 2, 4]),(pw40,5,[0, 1, 2, 3]),(pw42,4,[0, 1, 4]),(pw43,4,[0, 1, 3]),(pw44,4,[0, 1, 2]),(pw1,3,[1, 2, 3, 4]),(pw45,1,[3, 4]),(pw0,3,[0, 2, 3, 4]),(pw31,2,[1, 3, 4]),(pw34,2,[1, 2, 4]),(pw46,2,[1, 2, 3]),(pw47,2,[0, 1, 4]),(pw48,2,[0, 1, 3]),(pw7,2,[2, 3, 4]),(pw10,2,[0, 3, 4]),(pw49,1,[2, 4]),(pw50,1,[2, 3]),(pw51,1,[1, 4]),(pw52,1,[3, 4]),(pw53,1,[0, 4]),(pw54,2,[0, 2, 4]),(pw55,2,[0, 2, 3]),(pw56,2,[0, 2, 3]),(pw57,1,[2, 3]),(pw19,2,[2, 3, 4]),(pw58,1,[1, 3]),(pw59,1,[1, 2]),(pw60,1,[1, 4]),(pw61,1,[3, 4]),(pw62,1,[0, 1]),(pw63,1,[2, 4]),(pw64,2,[1, 2, 3]),(pw65,1,[2, 3]),(pw66,1,[1, 2]),(pw67,1,[2, 4]),(pw68,1,[1, 3]),(pw69,1,[0, 1]),(pw70,1,[0, 2]),(pw71,1,[0, 4]),(pw72,1,[0, 3])]
theorem p16_Y : ∀ s ∈ p16_Z, SliceN true p16_R p16_T s := by
  unfold p16_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p16_B p12_B p12_L (by decide +kernel),mkSlice (w:=2) p16_B p12_B p12_L (by decide +kernel),mkSlice (w:=4) p16_B p14_B p14_L (by decide +kernel),mkSlice (w:=8) p16_B p14_B p14_L (by decide +kernel),mkSlice (w:=16) p16_B p14_B p14_L (by decide +kernel),mkSlice (w:=12) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=20) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=24) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p16_B p15_B p15_L (by decide +kernel),mkSlice (w:=3) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p16_B p15_B p15_L (by decide +kernel),mkSlice (w:=4) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=8) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=16) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=3) p16_B p6_B p6_L (by decide +kernel),mkSlice (w:=4) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=3) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=3) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=12) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=5) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=12) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=8) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=16) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=18) p16_B p10_B p10_L (by decide +kernel),mkSlice (w:=18) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=1) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=13) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=6) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=16) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=10) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=17) p16_B p10_B p10_L (by decide +kernel),mkSlice (w:=17) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=24) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=9) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=20) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=2) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=2) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=22) p16_B p2_B p2_L (by decide +kernel),by simp⟩
def p16_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(1,[128]),(5,[]),(6,[]),(7,[]),(1,[386]),(0,[260]),(1,[260]),(0,[261]),(1,[261]),(0,[390]),(1,[390]),(0,[130]),(1,[130]),(0,[131]),(8,[]),(0,[128]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(6,[128]),(5,[128]),(5,[130]),(0,[129]),(16,[]),(17,[]),(18,[]),(0,[384]),(1,[384]),(19,[]),(0,[385]),(0,[386]),(7,[128]),(1,[131]),(20,[]),(21,[]),(22,[]),(0,[262]),(0,[263]),(23,[]),(0,[388]),(0,[389]),(24,[]),(25,[]),(26,[]),(6,[130]),(27,[]),(28,[]),(7,[130]),(29,[]),(30,[]),(1,[128,272]),(6,[256]),(1,[388]),(0,[384,147]),(7,[263]),(31,[]),(1,[385]),(0,[256]),(32,[]),(33,[]),(0,[259]),(1,[128,260]),(7,[256]),(34,[]),(35,[]),(1,[392]),(0,[392]),(36,[]),(1,[260,400]),(0,[260,400]),(0,[260,261]),(1,[260,261]),(1,[261,16]),(37,[]),(0,[391]),(1,[391,19]),(0,[262,401]),(1,[262,401]),(0,[395,147]),(1,[395,147]),(0,[128,401]),(1,[128,401]),(0,[128,402]),(0,[390,19]),(1,[128,402]),(1,[390,19]),(1,[384,147]),(0,[129,130]),(0,[128,129]),(1,[131,130]),(0,[131,130]),(0,[131,128]),(1,[386,387]),(1,[386,384]),(1,[260,19]),(0,[260,19]),(0,[256,147]),(0,[128,275]),(0,[128,272]),(0,[260,512]),(6,[131]),(0,[128,403]),(0,[128,525]),(1,[128,525]),(0,[128,400]),(0,[131,400]),(0,[384,145]),(0,[384,518]),(1,[384,518]),(7,[128,271]),(1,[260,130]),(0,[260,130]),(0,[257,144]),(0,[128,274]),(0,[131,272]),(0,[128,260]),(0,[128,263]),(0,[384,388]),(0,[390,386]),(0,[390,384]),(1,[390,384]),(1,[129,128]),(1,[129,130]),(1,[257,144]),(0,[260,17]),(0,[390,17]),(0,[131,402]),(0,[386,145]),(0,[130,402]),(1,[129,402]),(0,[129,402]),(1,[387,384]),(0,[387,384]),(0,[386,387]),(1,[131,128]),(0,[259,147]),(0,[131,275]),(0,[387,147]),(1,[387,147]),(0,[131,261]),(1,[131,261]),(0,[131,262]),(0,[131,389]),(7,[130,268]),(7,[263,15]),(0,[390,129]),(38,[]),(0,[390,131]),(1,[256,516]),(5,[260]),(14,[128]),(7,[256,260]),(7,[128,260]),(7,[128,256]),(39,[]),(40,[]),(0,[130,274]),(0,[261,16]),(0,[261,18]),(1,[261,18]),(1,[130,274]),(41,[]),(1,[390,17]),(0,[130,400]),(0,[391,19]),(0,[387]),(5,[256]),(0,[131,403]),(0,[258,147]),(5,[131]),(0,[388,386]),(0,[388,384]),(0,[129,400]),(0,[384,390]),(1,[390,388]),(42,[]),(1,[390,391]),(1,[256,400]),(0,[392,19]),(0,[256,400]),(0,[256,403]),(1,[392,19]),(6,[258]),(0,[392,147]),(0,[388,275]),(0,[260,403]),(6,[260]),(6,[263]),(1,[392,147]),(0,[260,128]),(1,[130,400]),(1,[394,147]),(1,[260,402]),(0,[262,400]),(5,[259]),(0,[260,129]),(1,[262,402]),(1,[390,260]),(0,[128,273]),(1,[256,145]),(5,[129]),(0,[256,260]),(1,[391,130]),(1,[128,391]),(0,[391,275]),(1,[391,275]),(0,[263,402]),(1,[128,391,279]),(5,[258]),(1,[260,261,20]),(0,[256,402]),(0,[256,401]),(0,[393,16]),(0,[130,401]),(0,[131,128,405]),(0,[130,129,276]),(0,[128,129,276]),(13,[260]),(0,[128,256]),(0,[384,273]),(0,[129,384,277]),(0,[131,384,277]),(0,[384,147,521]),(0,[384,275]),(0,[129,384,279]),(0,[131,384,279]),(0,[384,147,522]),(0,[389,16]),(5,[128,271]),(0,[130,391,279]),(0,[128,391,279]),(0,[129,272]),(0,[130,272]),(0,[261,131,276]),(1,[261,131,276]),(6,[128,271]),(6,[261]),(0,[131,262,405]),(0,[128,520]),(5,[128,256]),(14,[256]),(5,[260,256]),(5,[260,128]),(0,[257]),(6,[256,141]),(0,[131,274]),(0,[260,258]),(0,[260,130,278]),(0,[260,261,20]),(0,[261,260]),(0,[386,394,151]),(0,[384,394,151]),(5,[128,270]),(5,[258,143]),(5,[130,268]),(5,[130,271]),(5,[260,15]),(0,[260,128,277]),(0,[260,259]),(0,[128,273,520]),(0,[392,393,20]),(0,[260,257]),(13,[128]),(5,[128,129])]
def p16_t : Tabs := (p16_C.map (mkCut true p16_Z),[(29,28),(30,28),(7,5),(11,10),(30,26),(7,6),(30,22),(30,14),(11,9),(29,25),(29,21),(29,13),(7,3),(11,3),(19,3),(19,18),(11,2),(19,16),(19,17),(23,3),(11,1),(29,17),(29,9),(7,1),(29,20),(29,12),(30,24),(15,13),(19,2),(30,18),(30,10),(30,6),(19,1),(15,3),(29,5),(7,2),(29,16),(29,8),(30,16),(30,8)],[],[[],[2,3],[2],[3],[3,2],[0],[0,2,3],[0,2],[0,3],[0,3,2],[2,3,2],[0,2,3,2]])
theorem p16_W : TabsP true p16_R p16_T p16_t := ⟨cutsGood p16_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D8 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[3,0,4,1,5,9,17,25,29,7,15,13,49,53,57,11,19,23,21,33,37,41,45,27,31,35,39,43],[63,2635,296074,67851,10092564,52428852,71434292,14017,134239553,123776])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D7 : List StD := [
([pw7,pw3,pw2,pw5,pw6,pw40],[0,4,3,37,41,45,1,5,49,53,57,7,11,15,19,8,12,16,17,25,29,23,31,39,43],[3,1,35084,78352,148516,3,262213,528449,1065025,2097290,4194450,8388770,11036,16786732,24112]),
([pw14,pw3,pw2,pw5,pw6,pw40],[3,0,8,20,24,28,33,41,57,9,17,45,53,15,27,61,5,13,65,7,43,47],[6,16969,2,20625,2107680,65547,1030,294930,163874,16973,729,10600,529557,1060132,4529]),
([pw73,pw3,pw2,pw5,pw6,pw40],[28,0,32,49,53,16,36,9,61,4,12,1,21,29,37,41,69,3,39],[4099,262785,41,1045,2,67650,259,262,8195,16393,32788,131265,13,41,21]),
([pw3,pw2,pw42,pw5,pw6,pw40],[24,28,40,44,3,9,21,57,1,5,49,53,23,12,32,13,29,33,45,11,19,31,39],[828,85,32789,524357,1114438,4137,135177,2097193,4457002,8193,3,147,3089,17537,2179]),
([pw3,pw2,pw5,pw6,pw28,pw40],[28,32,48,52,29,9,17,57,3,13,1,5,21,25,37,41,45,49,53,61,73,23],[3372,581,12294,524549,533,16457,32810,3145737,65577,259,131073,209,262147,147,145]),
([pw74,pw3,pw2,pw5,pw6,pw40],[32,28,56,60,21,9,17,53,3,0,4,24,1,5,13,25,37,41,49,57,77,7,15,23,43,47],[16777745,33555489,262147,6291459,2049,12572,16454,32789,277,65610,131113,8388649,131,1572867,131])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D6 : List StD := [
([pw12,pw7,pw3,pw2,pw5,pw6,pw40],[76,80,20,84,88,64,92,3,68,72,96,100,53,7,15,43],[32,256,32,512,24577,32897,4,2,129,9,9,6,3,3,3,22,20,20,72,72,7168]),
([pw12,pw3,pw2,pw5,pw6,pw40],[80,20,88,112,1,3,116,37,53,57,7,15,104,108,73,43,24,28,64,68,72,13,33,45,61,81,85,89,27],[525313,268697600,1048608,68900,166436,23,19,16781329,2105361,139,33574982,4218894,67110312,134253248,8389448]),
([pw7,pw3,pw2,pw5,pw75,pw6,pw40],[92,124,128,120,3,72,84,116,132,4,64,136,11,15,19,23],[8,2,28,32,13,5,3,146,514,3,3,32775,34,260,260,1024,65,65,12292,16404,2176]),
([pw50,pw7,pw3,pw2,pw5,pw6,pw40],[148,88,36,76,112,140,156,160,28,144,152,49,3],[32,512,32,3,3,1024,4,64,3,3,4354,6,9,9,72,3,3,6,2192,129,17]),
([pw76,pw7,pw3,pw2,pw5,pw6,pw40],[84,92,72,124,132,164,4,3,80,128,136,168,7,23],[8,72,72,256,3,3,32,4,4736,3,3,36,148,3,3,8226,17,17,3,3,3072]),
([pw76,pw3,pw2,pw5,pw6,pw40],[72,164,92,84,108,1,41,45,3,53,57,15,32,104,13,33,80,112,136,148,61,93,7,43],[3,3,65792,4199244,8395916,35,16433,1056801,16433,2129942,41026,131218,265036,527756,1728]),
([pw7,pw14,pw2,pw5,pw6,pw40],[20,76,112,3,84,28,172,1,13,41,53,57,15,0,108,116,45,27,96,100,104,61,97,101,105,7,43,47],[37,8193,16683,3146002,16690,131203,8192,4326602,142612678,16777229,33289,69637,33818140,67704912,36356]),
([pw7,pw3,pw2,pw42,pw5,pw6,pw40],[168,40,44,136,3,24,84,116,11,23,176,180,184,31],[4,2,48,56,352,9,6,146,146,386,3,517,517,8197,1028,2048,4096,9,88,65,9]),
([pw7,pw3,pw2,pw5,pw6,pw28,pw40],[96,48,92,57,120,3,52,188,28,116,132,180,184,11,23],[16,2,49,8212,48,265,3,3,6,546,3,196,1089,16449,136,37,4096,12,2048,9,9]),
([pw74,pw7,pw3,pw2,pw5,pw6,pw40],[112,56,60,100,84,3,28,200,43,0,4,24,192,196,53,77,7,15,23,47],[352,769,525313,4096,196609,8192,4,2,104,2072,112,6,11,10,35,133,132,262149,17,32792,16385]),
([pw12,pw14,pw3,pw2,pw5,pw6,pw40],[84,172,80,96,20,72,100,7,24,28,64,92,108,116,27,43],[32,128,1024,32,385,33281,8192,16400,4,3,3,28,12,65,9,2068,3,3,3,3,4168]),
([pw77,pw3,pw56,pw2,pw5,pw6,pw40],[204,140,148,28,216,3,36,208,0,4,108,172,212,220],[1024,256,10,13,5,520,34,35,130,130,35,4096,5,5,64,17,17,80,10240,5,5]),
([pw77,pw3,pw2,pw5,pw6,pw40],[140,212,96,36,148,5,17,3,25,49,53,144,29,61,11,24,28,100,156,220,224,228,9,33,27,35],[2177,262147,33620694,16958736,2053,41,8259,1057025,4227,8912938,6291500,43,1606,4816,17686]),
([pw60,pw14,pw3,pw2,pw5,pw6,pw40],[24,96,232,40,100,108,104,180,20,92,184,27],[128,1,262,128,1024,6,1,6,8,2049,6,6,9,25,6,33,65,48,522,65,49]),
([pw60,pw3,pw2,pw5,pw6,pw40],[24,40,100,57,3,236,9,232,13,45,53,39,4,28,92,180,184,228,240,5,21,25,33,109,113,11,27,35],[3,8394964,134250497,67174401,27288,524338,259,1048579,17039618,4194353,33554529,588,2098179,131085,1037]),
([pw78,pw3,pw56,pw2,pw5,pw6,pw40],[108,28,132,204,244,3,60,140,172,208],[133,2,3,16,5,22,9,12,5,768,3,2,34,9,64,3,12,3,5,44,3]),
([pw78,pw3,pw2,pw5,pw6,pw40],[28,108,132,3,60,13,53,248,33,104,208,21,41,45,0,24,244,252,1,57,27,43],[2115630,1,65545,1085518,17,262332,1191,3168,171,275,4884,279,131147,532481,8771]),
([pw14,pw3,pw16,pw2,pw5,pw6,pw40],[24,80,108,172,104,20,68,28,256,3,7,27],[64,66,2114,2,13,24,1030,546,3,19,134,1,32,261,392,5,25,44,12,17,21]),
([pw14,pw3,pw16,pw2,pw6,pw40],[24,80,20,108,104,172,17,37,53,57,4,256,61,73,3,7,27,28,72,13,33,45,65,81,85,89,117,121,15,23,35,43,47],[3,263170,66694,16859561,4596957872,32838,16390,4198419,528394,1,604014921,3355445856,8396821,1056780,2229017]),
([pw73,pw3,pw56,pw2,pw5,pw6],[28,32,140,200,49,53,36,144,208,61,101,260,9,33,121,125],[133,2049,133,19,35,1100,1100,517,518,1,16657,33058,8217,4138,19]),
([pw14,pw3,pw33,pw2,pw5,pw6,pw40],[104,24,264,172,9,13,272,3,32,68,268,23,276,11,15,27],[512,51328,529,4,8456,265,37,176,6,37,1060,2,2114,4096,65,17,3,1040,200,9,3]),
([pw14,pw3,pw2,pw42,pw6,pw40],[24,40,280,3,33,104,232,5,13,49,57,61,27,28,32,44,108,184,284,9,45,93,23],[3,2134136,3,4611,16992,142,259,2051,2306,4194325,524301,1048724,131073,263177,74753]),
([pw74,pw64,pw3,pw2,pw5,pw6],[32,28,56,208,9,21,196,288,292,57,3,43,60,144,192,5,13,33,53,125,129,23],[65,101,10257,16385,526339,1,3150992,526,649,33828,65542,37,131338,281,262147]),
([pw14,pw3,pw2,pw5,pw44,pw6,pw40],[28,108,304,104,300,9,24,32,284,3,27,296,47],[1,2082,16,1664,1154,4105,36,3,274,280,3,3,6,36,3,517,3,76,1,64,3]),
([pw79,pw3,pw2,pw5,pw6,pw40],[24,64,28,172,41,53,20,92,57,45,80,5,13,37,61],[3,1154,3,185,908,2114,67,16387,4102,8257,57,780,49,261,49]),
([pw3,pw2,pw80,pw5,pw6,pw40],[24,28,104,308,312,1,5,9,32,21,49,3,23,13,33,53,11,19,31,39],[248,2612,10293,66101,131634,4296,20557,262345,524490,257,3,1,1283,1283,32775]),
([pw3,pw2,pw42,pw28,pw40],[24,32,316,320,9,57,3,48,1,5,21,25,29,41,45,61,73,133,23],[860,2181,32837,5126,8217,327689,16410,131073,35,35]),
([pw81,pw3,pw2,pw5,pw6,pw40],[32,48,24,104,232,57,324,73,3,45,61,4,28,172,184,328,5,9,29,39],[3,657816,16390,3,569,65858,1038,1027,262147,32988,8385,545,4357,61,37]),
([pw82,pw3,pw2,pw5,pw6,pw40],[28,332,24,92,172,336,25,53,73,232,9,3,4,192,5,29,49,61,77,23,47],[3,1056520,3,220,8203,18466,131075,70,32771,524577,852,1073,133,327685,133]),
([pw3,pw2,pw5,pw6,pw83],[28,24,340,344,17,9,13,29,53,1,5,21,37,45,57,125,137,3],[132652,85,34822,197,4121,65578,8329,259,16403,259]),
([pw3,pw2,pw84,pw6,pw40],[24,32,348,352,9,17,21,0,40,184,1,5,29,37,45,49,53,57,3,11,31],[265244,165,524357,4166,8233,1048601,16410,801,32771,196611])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D5 : List StD := [
([pw7,pw3,pw2,pw5,pw6,pw85],[356,84,172,112,224,360,92,28,116,136,3],[16,1,1153,22,22,33,41,65,65,41,6,6,6,6,776]),
([pw86,pw7,pw3,pw2,pw6,pw40],[92,248,380,364,368,72,84,124,136,172,148,160,208,372,376],[184,24584,184,2305,273,4,2,65,65,6,3,3,516,518,5120]),
([pw12,pw3,pw2,pw75,pw6,pw40],[92,136,148,388,20,96,120,172,28,208,384,3,7,15],[64,1024,4096,67,261,9,24,5,3,24,132,130,2081,8705,34]),
([pw76,pw12,pw3,pw2,pw6,pw40],[92,148,136,20,80,172,0,208,392,396,400,3,15],[64,24,24,3,5,256,512,4101,2051,1025,3,5,34,36,130]),
([pw77,pw87,pw2,pw5,pw6,pw40],[92,208,148,140,108,172,61,0,212,224,404,408,69],[128,9,6,5,9,4096,322,577,1024,17,34,2088,17,7,6]),
([pw88,pw3,pw2,pw5,pw6,pw40],[172,92,236,428,108,208,28,84,412,416,420,424,432,19],[256,512,1024,2048,8257,10,44,3,3,14,5,5,4113,129,48]),
([pw12,pw3,pw2,pw5,pw6,pw85],[208,112,108,444,172,440,32,84,212,436,448,3,7],[256,512,2048,4161,32,1034,11,9,38,11,17,6,6,145,5]),
([pw86,pw3,pw2,pw5,pw6,pw40],[108,172,112,372,376,380,0,84,92,248,364,368,452,456],[88,3080,4096,3,8210,548,5,258,7,5,34,5,3,130,5]),
([pw86,pw87,pw3,pw2,pw6,pw40],[108,208,92,148,172,460,464,84,468,61,73,3],[32,35,7,5,10,512,1024,2049,128,68,10,69,18,273,3]),
([pw86,pw3,pw2,pw6,pw40],[108,132,248,380,104,1,32,136,372,472,49,84,92,96,112,364,368,376,9,21,45,53,57,81,129],[131335,102665,1219,3266,46,524340,45,8651290,16777740,7364625]),
([pw12,pw3,pw2,pw42,pw6,pw40],[96,136,84,104,116,428,32,108,188,228,432,476,480,484,488,492,496,500],[2048,4096,57376,1090,580,65537,33,28,3,56,13,386,131072,18,3]),
([pw74,pw87,pw3,pw2,pw5,pw6],[160,172,84,96,108,112,512,516,24,92,104,140,144,224,504,508,3,43],[65536,2057,4099,16384,131084,8192,32768,260,1027,193,112,515,176,7,7]),
([pw7,pw14,pw2,pw75,pw6,pw40],[92,520,172,84,96,124,188,64,72,136,208,524,3,15],[2050,32,256,9,9,67,128,69,5,34,6,6,4113,9217,528]),
([pw7,pw3,pw2,pw89,pw6,pw40],[528,96,484,84,32,64,80,160,532,11,116,136,184,188,492,31],[1,4,16736,537,26,5,6,645,6,97,32771,8193,4354,1160,2050]),
([pw90,pw7,pw3,pw2,pw5,pw6],[136,208,156,536,552,556,140,200,540,32,36,84,96,144,160,192,544,548],[332,9220,332,229384,4097,16,32,3,2562,48,3,34,129,144,16385]),
([pw50,pw91,pw3,pw2,pw5,pw6],[148,160,208,136,36,156,188,200,404,560,564,568,3],[4096,512,1024,3,13,18,34,5,7,2306,5,7,65,131,10]),
([pw76,pw7,pw14,pw2,pw6,pw40],[84,96,72,92,124,136,172,188,572,80,148,200,392],[16,516,20,11,9,4352,4,9,3,386,161,3073,65,65,34]),
([pw92,pw3,pw2,pw5,pw6,pw40],[136,168,108,104,0,4,116,492,32,268,576,580,3],[48,48,1024,2048,259,130,69,200,3,7,10,517,4101,10,3]),
([pw93,pw3,pw2,pw5,pw6,pw40],[200,104,108,588,584,20,32,208,0,64,68,80,112,268,440,452,456,89,7],[1312,2592,65536,262209,49216,25,146,146,5,9,9,8204,4100,131075,7]),
([pw76,pw3,pw2,pw6,pw28,pw40],[104,172,472,32,48,52,96,596,592,600,3,7],[48,48,1034,2048,11,388,7,5,66,7,5,134,512,65,3]),
([pw74,pw76,pw3,pw2,pw6,pw40],[472,108,200,104,620,540,612,56,136,164,248,364,456,604,608,616,624,89,93,141,15],[7200,524321,262657,1048836,8192,16576,32836,19,131081,65553,25,3,13,3,6]),
([pw77,pw7,pw56,pw5,pw6,pw40],[148,208,140,224,4,32,36,108,112,172,188,228],[36,4,259,3,20,12,3,3,140,3,3,64,3584,3,3]),
([pw7,pw60,pw2,pw5,pw6,pw40],[236,116,136,40,108,200,240,84,96,104,176,180,184,284,412,628,101,3,11],[16385,8,81,41472,80,33,2048,4096,65572,131075,262147,1025,268,130,6]),
([pw78,pw7,pw3,pw5,pw6,pw40],[84,172,208,96,364,60,72,104,112,124,220,248,368,452,632,3],[4688,24,8192,11,3,32,16512,3,3,2052,5,33025,3,3,1028]),
([pw7,pw14,pw16,pw5,pw6,pw40],[172,80,84,4,24,104,116,256,28,64,68,72,636],[1034,514,50,48,261,10,2,5,5,2048,193,129,5,5,4160]),
([pw7,pw14,pw16,pw6,pw40],[172,116,84,24,80,53,57,4,104,256,28,72,96,100,108,112,188,200,640,644,648,45,145,149,153,157,3,7,15,23,27,35,43,47],[410,26,269,279557,2192,1145110567,8867414085,687870499,6477062721,2130018]),
([pw7,pw14,pw33,pw5,pw6,pw40],[116,96,172,104,200,272,636,23,0,120,264,276,284,652,3,11],[513,257,9,9,12290,147,1024,32773,22,161,2048,36,16390,65,65]),
([pw7,pw14,pw2,pw42,pw6,pw40],[96,84,24,40,104,116,136,188,20,44,160,176,184,284,656,3,23],[20,8,20,20,8195,641,9,200,17409,65824,32771,2050,4096,34,65]),
([pw74,pw7,pw64,pw2,pw5,pw6],[84,160,200,652,32,256,43,56,96,108,116,144,192,196,292,516],[24,8192,2114,4096,321,24,128,524,24,7,1025,16418,32772,7,35]),
([pw7,pw3,pw2,pw42,pw28,pw40],[96,84,316,116,120,3,188,52,49,57,133,23],[16,4,49,50,3,5,5,44,5,200,2051,66,1024,10,769]),
([pw94,pw3,pw2,pw5,pw6,pw40],[96,256,664,120,104,188,32,72,80,116,200,264,276,324,660,3,19],[8,16384,392,6152,65601,5,5,6,5,8736,1027,34,32771,18,17]),
([pw95,pw3,pw2,pw5,pw6,pw40],[116,104,96,120,668,0,72,80,84,188,256,264,276,672],[9,40,200,6152,6,21,3,3,20,3,3,8704,1284,3,3]),
([pw7,pw81,pw2,pw5,pw6,pw40],[96,324,172,188,48,24,104,160,680,32,676,113,3],[1026,16,97,96,2561,11,17,24,133,10,6,10,4103,388,257]),
([pw96,pw3,pw2,pw5,pw6,pw40],[160,84,200,100,136,148,536,584,652,684,0,64,124,140,224,456],[16385,1025,39040,7,8321,577,72,11,257,516,7,257,19,35,52]),
([pw97,pw3,pw2,pw5,pw6,pw40],[148,200,96,120,100,692,72,80,152,156,188,336,440,452,688,49],[8,16384,200,11,13056,38,5,17,38,3,3,3088,32772,3,3]),
([pw7,pw82,pw2,pw5,pw6,pw40],[116,148,100,96,332,172,4,120,200,284,336,49,113,23],[129,16,11,7,4616,321,17,7,24,8195,35,1060,2056,7,7]),
([pw7,pw3,pw2,pw5,pw6,pw83],[96,200,340,344,84,24,172,100,112,300,3],[8,4,1057,50,17,12,5,132,5,10,10,72,273,82,515]),
([pw7,pw3,pw2,pw84,pw6,pw40],[96,148,348,84,120,116,11,184,188,200,57,31],[16,4,19,82,9,5,5,100,5,514,2051,264,137,42,1027]),
([pw77,pw64,pw2,pw5,pw6,pw40],[148,140,96,100,292,212,696,700,36,108,156,408,69],[66,1026,133,137,66,4354,52,17,2,17,21,2058,548,9,13]),
([pw86,pw64,pw3,pw2,pw6,pw40],[96,108,456,73,256,292,56,196,248,380,704,112,124,364,368],[1220,5,28676,19,1220,2048,521,34,256,521,48,257,9,26,35]),
([pw77,pw64,pw56,pw2,pw5,pw6],[292,108,140,256,28,148,208,4,36,188,212],[132,4,20,18,9,12,772,33,3,1024,73,66,35,9,10]),
([pw98,pw3,pw2,pw5,pw6,pw40],[172,108,96,112,256,212,248,24,72,84,124,452,456],[8,1288,2048,131,4105,68,70,17,7,34,21,19,3,513,38]),
([pw3,pw99,pw2,pw5,pw6,pw40],[108,176,236,256,412,708,0,84,172,184,208,416,488,628,712],[81,38,3,8226,41,2065,4096,529,10,16389,260,7,9,130,1027]),
([pw77,pw3,pw2,pw43,pw5,pw6],[256,720,84,172,24,92,212,108,220,452,456,688,716,724,728,113],[128,4098,11776,20,25,34,3,32834,3,9,288,12,16384,68,5]),
([pw74,pw77,pw3,pw2,pw5,pw6],[256,212,172,56,84,140,512,92,96,112,208,220,504,11],[41,33,5,4096,8450,512,10,18,5,192,1090,5,2050,5,17]),
([pw78,pw3,pw72,pw2,pw6,pw40],[108,28,176,172,84,208,452,220,248,252,732,736,740],[69,64,3,9,20,289,1156,44,3,2,2561,4096,24,3,7]),
([pw100,pw3,pw2,pw5,pw6,pw40],[208,752,96,148,220,92,748,28,172,744,756,760],[512,66,137,67,1026,6,3,3,6,49,7,2320,52,9,9]),
([pw101,pw3,pw2,pw5,pw6,pw40],[220,92,208,104,312,4,96,240,764,768,772,776,23],[256,4129,512,1024,2048,3,20,3,18,3,76,129,3,10,5]),
([pw102,pw3,pw2,pw5,pw6,pw40],[104,176,780,788,108,0,124,172,308,784],[35,69,256,516,3,10,3,3,20,5,137,14,20,3,3]),
([pw60,pw3,pw16,pw2,pw6,pw40],[104,208,108,256,412,792,236,292,428,24,40,268,480,488,500,89,3],[16,8464,400,16384,32897,1027,65632,35,44,4096,12,11,515,2116,7]),
([pw78,pw3,pw56,pw2,pw43,pw6],[28,108,176,84,172,204,4,208,504],[262,1,3,69,18,42,36,3,148,1,13,34,3,24,7]),
([pw103,pw3,pw2,pw5,pw6,pw40],[208,220,112,440,692,796,148,196,256,292,336,452,456,584,688],[32,16432,12432,3,2056,1030,9,3,264,7,513,6,6,65,3]),
([pw104,pw3,pw2,pw5,pw6,pw40],[108,176,804,784,28,104,208,800,0,220,532,632,780],[259,1041,128,4096,146,6,3,578,9,13,2084,7,9,34,67]),
([pw105,pw3,pw2,pw5,pw6,pw40],[240,220,100,652,812,4,104,184,208,312,348,764,776,808],[2049,42,8192,129,4609,6,1029,7,9,3,280,3,3,84,3]),
([pw78,pw64,pw3,pw2,pw5,pw6],[108,172,256,28,104,456,56,60,196,208,248,368,452,516,632,700,704,3],[65888,37,2053,4096,32771,8,131,530,16401,140288,9,6,9,6,5]),
([pw78,pw3,pw2,pw42,pw6,pw40],[104,176,28,824,632,804,24,40,108,136,308,352,816,820],[131,4101,11296,608,3,10,3,3,260,25,25,14,4,3,3]),
([pw3,pw2,pw106,pw5,pw6,pw40],[836,828,832,104,256,328,3,324,676],[70,386,11,7,18,13,7,13,36,5,3,24,112,9,9]),
([pw14,pw3,pw33,pw2,pw42,pw40],[24,136,104,108,432,172,272,280,840,65,93,3,23],[1,4122,1030,3,36,532,2432,5,66,1,25,74,5,34,3]),
([pw14,pw3,pw2,pw80,pw6,pw40],[104,24,312,28,108,136,304,20,148,308,768,93,105],[2,2561,1028,38,265,68,69,3,28,4225,3,56,8,2,3]),
([pw14,pw3,pw107,pw2,pw6,pw40],[256,292,172,844,24,80,148,208,548,692,848,3],[8,296,10,21,7,160,3584,3,5,16,3,5,3,5,66]),
([pw14,pw3,pw2,pw108,pw40],[24,852,28,148,104,172,864,33,3,40,208,232,312,856,860,5,9,13,49,93,27],[3,1583504,16897,262174,33090,1027,131078,65577,228,4109]),
([pw109,pw3,pw2,pw5,pw6,pw40],[100,220,312,256,148,868,0,4,104,228,776],[256,131,69,3,1028,3,5,3,12,50,552,3,10,17,3]),
([pw81,pw3,pw2,pw42,pw40],[24,316,28,872,73,104,172,220,232,3,44,208,5,9,29,49,57,93,39],[3,395056,3,33188,4618,2051,16390,89,8412,65541]),
([pw110,pw3,pw2,pw5,pw6,pw40],[208,292,116,256,100,228,272,884,0,140,172,696,876,880,3],[4,260,7,7,14848,144,3,3,136,3,3,1048,104,33,16449]),
([pw111,pw3,pw2,pw5,pw6,pw40],[208,172,368,376,84,100,256,24,248,272,292,364,452,680,888],[8,2052,4360,131,16394,36,5,5,68,1025,3,98,18,19,8705])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D4 : List StD := [
([pw76,pw3,pw2,pw6,pw85],[208,84,172,356,100,104,116,256,892],[9,9,6,7,272,3,130,5,6,97]),
([pw112,pw3,pw2,pw5,pw6],[256,292,208,129,104,0,24,84,100,140,156],[33,1537,17,84,264,6,3,14,11,129]),
([pw12,pw3,pw2,pw113,pw40],[116,256,904,120,228,428,900,28,104,172,896,908],[8,1024,56,144,69,36,66,2051,518,257]),
([pw114,pw3,pw2,pw6,pw40],[100,104,84,256,292,228,0,48,124,272],[65,274,140,11,33,17,12,22,33,515]),
([pw86,pw3,pw2,pw115,pw40],[100,228,256,292,84,272,912,916,920,924],[65,392,38,3,3,9,516,12,3,17]),
([pw86,pw116,pw3,pw2,pw40],[100,256,84,228,292,928,932,936,940],[6,33,208,11,6,20,5,9,258,11]),
([pw117,pw3,pw2,pw5,pw6],[256,220,100,292,0,104,272,456,548,584,944,948],[17,1281,641,100,6,12,3,2050,9,3]),
([pw12,pw3,pw2,pw108,pw40],[904,104,116,120,228,256,428,956,28,220,952],[8,1024,88,272,129,65,160,38,513,7]),
([pw7,pw14,pw2,pw113,pw40],[116,256,176,264,492,904,960,28,84,112,120,148,172,964],[1025,64,25,386,101,8195,4610,25,6,2081]),
([pw92,pw3,pw2,pw28,pw40],[256,84,176,104,48,28,968,972,976,85],[17,17,512,38,196,14,3,266,5,9]),
([pw118,pw3,pw2,pw6,pw40],[84,176,100,680,220,0,104,256,272,304,364,368,784,980],[36,15360,133,7,26,11,257,577,3,26]),
([pw76,pw3,pw2,pw6,pw83],[84,112,212,272,620,104,116,176,256,340,984],[6,516,25,261,1042,17,11,97,131,42]),
([pw7,pw60,pw16,pw6,pw40],[256,24,84,988,104,112,116,120,240,484,488,492,500,636,792,149],[138,16386,19,261,3592,4096,32801,5,5,8256]),
([pw78,pw7,pw64,pw5,pw6],[84,172,368,72,124,196,364,452,456,636,704,992,996,1000,1004],[92,1316,128,2051,3,12288,3,3,16896,3]),
([pw7,pw106,pw5,pw6,pw40],[256,636,664,104,328,828,836,184,276,484,488,652,660,1008,1012,1016,3],[12548,104,72,18433,33412,1060,3,65553,3,18]),
([pw7,pw14,pw33,pw42,pw40],[84,172,104,176,780,24,40,112,272,840,960,1020,23],[20,2116,36,19,4105,520,3,1027,386,9]),
([pw7,pw14,pw107,pw6,pw40],[116,172,148,256,0,28,108,112,120,548],[257,17,7,98,517,11,14,7,10,133]),
([pw7,pw14,pw2,pw108,pw40],[256,116,28,104,112,148,176,852,24,108,172,860],[12,128,264,517,98,2051,145,1025,65,50]),
([pw94,pw3,pw2,pw42,pw40],[256,112,1028,120,172,28,104,108,116,428,492,904,1024],[8,4096,1544,161,2054,5,7,17,17,322]),
([pw7,pw81,pw2,pw42,pw40],[112,172,84,176,256,1032,24,104,212],[257,32,194,7,13,40,19,18,7,13]),
([pw119,pw3,pw2,pw6,pw40],[116,104,256,100,120,220,172,456,492,580,712],[17,1025,784,134,41,7,68,3,44,3]),
([pw77,pw3,pw2,pw120,pw6],[256,1040,100,104,228,24,84,172,176,304,688,1036],[256,2050,1033,40,6,3,6,129,592,17]),
([pw121,pw2,pw5,pw6,pw40],[104,1060,1044,0,84,100,172,1048,1052,1056],[140,5,5,776,3,3,50,80,3,3]),
([pw3,pw2,pw106,pw42,pw40],[680,1064,836,24,256,220,328,1068,1072,3],[515,11,7,18,140,276,97,10,17,5]),
([pw110,pw3,pw2,pw5,pw44],[172,116,256,100,148,220,1076,120,300,304,328],[2,258,34,37,72,72,5,1168,5,529])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D3 : List StD := [
([pw7,pw106,pw42,pw40],[220,84,256,1028,1072,172,836,904,1024,1068,1080,1084,1088],[1800,81,7,56,133,6146])]
def p16_D2 : List StD := []
theorem p16_I2 : LevelN true p16_T 2 p16_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C3x0 : levelOK true p16_T p16_t 2 (p16_D2.map Prod.fst) ((p16_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I3 : LevelN true p16_T 3 p16_D3 := levelStep p16_B p16_W p16_I2 (chunks 32 p16_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C4x0 : levelOK true p16_T p16_t 3 (p16_D3.map Prod.fst) ((p16_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I4 : LevelN true p16_T 4 p16_D4 := levelStep p16_B p16_W p16_I3 (chunks 32 p16_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C5x0 : levelOK true p16_T p16_t 4 (p16_D4.map Prod.fst) ((p16_D5.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C5x1 : levelOK true p16_T p16_t 4 (p16_D4.map Prod.fst) ((p16_D5.drop (1*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C5x2 : levelOK true p16_T p16_t 4 (p16_D4.map Prod.fst) ((p16_D5.drop (2*32)).take 32) = true := by decide +kernel
theorem p16_I5 : LevelN true p16_T 5 p16_D5 := levelStep p16_B p16_W p16_I4 (chunks 32 p16_D5 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C5x0
  · exact p16_C5x1
  · exact p16_C5x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C6x0 : levelOK true p16_T p16_t 5 (p16_D5.map Prod.fst) ((p16_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I6 : LevelN true p16_T 6 p16_D6 := levelStep p16_B p16_W p16_I5 (chunks 32 p16_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C7x0 : levelOK true p16_T p16_t 6 (p16_D6.map Prod.fst) ((p16_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I7 : LevelN true p16_T 7 p16_D7 := levelStep p16_B p16_W p16_I6 (chunks 32 p16_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C8x0 : levelOK true p16_T p16_t 7 (p16_D7.map Prod.fst) ((p16_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I8 : LevelN true p16_T 8 p16_D8 := levelStep p16_B p16_W p16_I7 (chunks 32 p16_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C8x0
  ))
theorem p16_L : LowN true p16_R p16_T 9 := lowSearch p16_B p16_I8 (by decide +kernel)
def p17_T : Nat := 0x88808880888088808880888088808880
def p17_R : List Nat := [0, 1, 2, 3]
def p17_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
theorem p17_L : LowN true p17_R p17_T 3 := lowCount p17_B (by decide +kernel)
def p18_T : Nat := 0xe8a8a800e8a8a800e8a8a800e8a8a800
def p18_R : List Nat := [0, 1, 2, 3, 4]
def p18_E : List (Nat × Nat × Nat) := [(0,10,11),(1,9,11),(2,9,13),(3,3,11),(4,3,19)]
theorem p18_B : baseOK p18_T p18_R p18_E = true := by decide +kernel
def p18_Z : List SliceD := [(pw2,5,[0, 3, 4, 2]),(pw5,5,[0, 3, 4, 1]),(pw6,5,[0, 1, 2, 4]),(pw40,5,[0, 1, 2, 3]),(pw16,4,[0, 3, 4]),(pw44,4,[0, 1, 2]),(pw1,3,[1, 2, 3, 4]),(pw45,1,[3, 4]),(pw32,2,[0, 2, 4]),(pw20,2,[2, 3, 4]),(pw0,3,[0, 2, 3, 4]),(pw9,2,[4, 2, 1]),(pw73,2,[3, 2, 1]),(pw122,1,[1, 2]),(pw47,2,[0, 1, 4]),(pw34,2,[1, 2, 4]),(pw19,2,[2, 3, 4]),(pw8,2,[1, 3, 4]),(pw33,2,[0, 2, 4]),(pw63,1,[2, 4]),(pw48,2,[0, 1, 3]),(pw52,1,[3, 4]),(pw123,2,[0, 2, 3]),(pw31,2,[1, 3, 4]),(pw124,1,[1, 2]),(pw46,2,[1, 2, 3]),(pw125,1,[1, 4])]
theorem p18_Y : ∀ s ∈ p18_Z, SliceN true p18_R p18_T s := by
  unfold p18_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=2) p18_B p8_B p8_L (by decide +kernel),mkSlice (w:=4) p18_B p8_B p8_L (by decide +kernel),mkSlice (w:=8) p18_B p8_B p8_L (by decide +kernel),mkSlice (w:=16) p18_B p8_B p8_L (by decide +kernel),mkSlice (w:=6) p18_B p3_B p3_L (by decide +kernel),mkSlice (w:=24) p18_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p18_B p15_B p15_L (by decide +kernel),mkSlice (w:=3) p18_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=2) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p18_B p17_B p17_L (by decide +kernel),mkSlice (w:=1) p18_B p11_B p11_L (by decide +kernel),mkSlice (w:=1) p18_B p11_B p11_L (by decide +kernel),mkSlice (w:=9) p18_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=8) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=1) p18_B p11_B p11_L (by decide +kernel),mkSlice (w:=1) p18_B p11_B p11_L (by decide +kernel),mkSlice (w:=10) p18_B p10_B p10_L (by decide +kernel),mkSlice (w:=10) p18_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=5) p18_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=4) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=17) p18_B p2_B p2_L (by decide +kernel),mkSlice (w:=16) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=1) p18_B p1_B p1_L (by decide +kernel),by simp⟩
def p18_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(5,[128]),(3,[128]),(2,[128]),(9,[]),(10,[]),(3,[131]),(11,[]),(2,[131]),(12,[]),(13,[]),(0,[128]),(14,[]),(1,[128]),(15,[]),(0,[131]),(4,[131]),(16,[]),(17,[]),(18,[]),(19,[]),(5,[131]),(5,[256]),(20,[]),(21,[]),(5,[256,143]),(22,[]),(3,[256,147]),(0,[130]),(4,[128]),(0,[129]),(1,[131]),(5,[259]),(5,[257]),(23,[]),(2,[259]),(0,[258]),(0,[256]),(4,[256]),(24,[]),(0,[256,147]),(1,[256,147]),(0,[259]),(0,[257]),(25,[]),(4,[259]),(5,[129]),(5,[258]),(1,[258]),(26,[]),(4,[258]),(5,[131,268]),(5,[131,271]),(0,[389]),(0,[390]),(0,[261]),(0,[262]),(4,[256,143]),(0,[128,274]),(0,[262,19]),(0,[386]),(0,[384]),(5,[260,13]),(4,[129]),(5,[257,140]),(5,[263]),(2,[257,144]),(0,[257,144]),(0,[260,17]),(4,[257,140]),(0,[263])]
def p18_t : Tabs := (p18_C.map (mkCut true p18_Z),[(13,12),(30,28),(11,9),(11,10),(30,26),(13,9),(19,18),(30,22),(11,3),(30,14),(19,3),(19,17),(13,5),(21,5),(21,17),(21,20),(19,1),(19,16),(11,1),(13,14),(11,8),(13,1),(19,26),(11,14),(11,26)],[],[[],[1],[3],[1,3]])
theorem p18_W : TabsP true p18_R p18_T p18_t := ⟨cutsGood p18_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D7 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0,8,5,4,12,9,17,21,33,41,3,1,29,7,11,16,20,13,25,37,45,49,53,57,15],[3109,139464,267522,543248,32933,3146759,4210741,8397130,16777944,70402])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D6 : List StD := [
([pw7,pw3,pw2,pw5,pw6,pw40],[0,24,16,21,49,3,28,1,53,20,32,36,17,33,61,7,11,40,44,9,37,41,15],[1,524321,32782,41586,6357826,161,4110,17554,16578,13,2097,67841,9228,4108,1442064]),
([pw20,pw3,pw2,pw5,pw6,pw40],[0,48,16,32,21,33,1,17,29,37,3,56,41,8,12,52,60,64,68,5,9,49,65,7,11,15],[1,525313,158,8430882,50352650,1089,150,362,6722,21,2293761,5507073,60,148,808]),
([pw126,pw3,pw2,pw5,pw6,pw40],[8,24,20,72,41,45,57,3,76,61,32,84,9,37,7,11,0,16,80,17,21,25,33,69,15],[1,102570,17973322,4194433,32790,8390434,2359818,641,8214,526688,417,5180,18497,8284,21]),
([pw34,pw3,pw2,pw5,pw6,pw40],[20,88,80,32,9,37,41,5,17,21,3,92,96,49,0,16,100,104,25,29,33,73,7,11,15],[1,8406166,21005066,525313,103,2202,4870,263169,99,412,2172929,89,1191937,549,97]),
([pw3,pw33,pw2,pw5,pw6,pw40],[20,32,0,108,1,16,60,21,3,112,13,25,37,41,100,17,53,57,15],[263450,350,1616,18707,2640,5,32938,4,12299,164,5,65551,131115,161,12289])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D5 : List StD := [
([pw20,pw7,pw3,pw5,pw6,pw40],[32,48,16,100,0,104,116,60,68,88],[16,16,7,10,3,16,37,194,321,14,11,10,37,36,513]),
([pw127,pw14,pw3,pw5,pw6,pw40],[104,16,80,48,120,124,128,0,60,88,100],[128,2,259,20,48,2,1024,65,65,6,13,41,3,3,516]),
([pw127,pw3,pw5,pw6,pw40],[48,100,16,32,9,13,60,132,25,41,49,20,88,136,140,21,33,37,73],[4,87,263251,2067,39,299,291,65676,41604,153096]),
([pw128,pw3,pw2,pw5,pw6,pw40],[60,36,76,88,100,116,15,16,80,92,144,148],[1024,32,193,512,97,7,9,22,9,20,3,22,3,2306,9]),
([pw129,pw3,pw2,pw5,pw6,pw40],[60,88,16,80,120,156,32,92,96,148,152],[1156,7,7,512,3,3,3,24,3,40,3,336,3,56,3]),
([pw7,pw3,pw33,pw5,pw6,pw40],[88,32,16,20,36,0,60,80,112,116,136,65,77],[32,521,133,136,2057,4099,69,18,65,262,32,274,3,1044,3]),
([pw63,pw3,pw2,pw5,pw6,pw40],[32,112,60,36,92,96,116,16,76,80,152],[1024,8,131,256,11,17,38,65,6,3,84,3,3,544,3]),
([pw3,pw130,pw2,pw5,pw6,pw40],[160,32,60,148,80,76,168,72,96,164,172,15],[545,14,28,3,69,164,3,256,2051,82,5,11,3,25,1026]),
([pw131,pw3,pw2,pw5,pw6,pw40],[32,180,112,100,136,36,48,176,184,16,116],[130,32,517,112,131,3,268,73,14,3,18,3,5,1296,5]),
([pw34,pw126,pw3,pw2,pw5,pw40],[20,80,88,72,32,100,0,68,76,92,96,112],[64,1,262,20,7,1,546,1036,131,12,38,37,2066,25,11]),
([pw132,pw64,pw3,pw2,pw5,pw40],[20,136,124,188,88,60,112,180,184],[1,1,130,260,3,1,12,10,32,26,28,3,66,5,3]),
([pw132,pw3,pw2,pw5,pw40],[60,88,20,32,124,192,1,9,49,100,196,21,0,80,13,17,33,81],[4,4867,65811,775,131307,16467,71,36024,172,11268]),
([pw126,pw3,pw33,pw2,pw5,pw40],[80,100,76,20,48,32,112,144,148,16,92,136,85,89],[128,1028,131,4640,2057,8213,36,19,18,8,322,73,7,6,265]),
([pw133,pw3,pw2,pw5,pw6,pw40],[32,200,136,28,208,0,116,212,16,36,100,204,15],[2082,64,4353,76,35,3,1168,25,524,3,6,3,137,20,21]),
([pw3,pw2,pw134,pw5,pw6,pw40],[60,152,216,112,100,16,72,92,77,89,7,11],[259,128,9,532,9,6,18,7,18,1057,6,2053,9,68,9]),
([pw135,pw3,pw2,pw5,pw6,pw40],[88,72,48,184,68,220,20,28,224,228,104],[8,11,11,84,72,3,3,20,161,1284,513,38,385,34,529])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D4 : List StD := [
([pw136,pw3,pw5,pw6,pw40],[184,100,48,232,28,236,32,88,136,240],[9,552,38,11,7,6,7,17,17,448]),
([pw137,pw3,pw2,pw5,pw40],[48,28,136,260,72,32,92,100,152,244,248,252,256],[321,129,1538,6148,12,25,3,5,49,10]),
([pw138,pw3,pw2,pw5,pw40],[32,72,192,100,116,264,268,16,48,92,136,152,252],[2656,40,131,4168,7,258,1044,5,5,18]),
([pw139,pw3,pw5,pw6,pw40],[132,72,100,32,136,272,20,48,88,96,276],[1058,34,134,66,517,13,21,9,17,264]),
([pw3,pw140,pw5,pw6,pw40],[284,280,288,32,100,136,0,72,236,292,296,93],[322,2065,13,52,515,3,146,13,37,1032]),
([pw3,pw2,pw141,pw5,pw40],[32,300,80,100,308,216,72,144,304,312,97],[3,385,28,1064,14,3,3,81,545,20])]
def p18_D3 : List StD := []
theorem p18_I3 : LevelN true p18_T 3 p18_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C4x0 : levelOK true p18_T p18_t 3 (p18_D3.map Prod.fst) ((p18_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I4 : LevelN true p18_T 4 p18_D4 := levelStep p18_B p18_W p18_I3 (chunks 32 p18_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C5x0 : levelOK true p18_T p18_t 4 (p18_D4.map Prod.fst) ((p18_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I5 : LevelN true p18_T 5 p18_D5 := levelStep p18_B p18_W p18_I4 (chunks 32 p18_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C6x0 : levelOK true p18_T p18_t 5 (p18_D5.map Prod.fst) ((p18_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I6 : LevelN true p18_T 6 p18_D6 := levelStep p18_B p18_W p18_I5 (chunks 32 p18_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C7x0 : levelOK true p18_T p18_t 6 (p18_D6.map Prod.fst) ((p18_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I7 : LevelN true p18_T 7 p18_D7 := levelStep p18_B p18_W p18_I6 (chunks 32 p18_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C7x0
  ))
theorem p18_L : LowN true p18_R p18_T 8 := lowSearch p18_B p18_I7 (by decide +kernel)
def p19_T : Nat := 0xa880a880a880a880a880a880a880a880
def p19_R : List Nat := [0, 1, 2, 3]
def p19_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p19_B : baseOK p19_T p19_R p19_E = true := by decide +kernel
def p19_Z : List SliceD := [(pw3,4,[1, 2, 3])]
theorem p19_Y : ∀ s ∈ p19_Z, SliceN true p19_R p19_T s := by
  unfold p19_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p19_B p3_B p3_L (by decide +kernel),by simp⟩
def p19_C : List (Nat × List Nat) := [(0,[])]
def p19_t : Tabs := (p19_C.map (mkCut true p19_Z),[],[],[])
theorem p19_W : TabsP true p19_R p19_T p19_t := ⟨cutsGood p19_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p19_D4 : List StD := [
([pw3,pw2,pw5,pw6],[0],[1,1,1,1,1,1])]
def p19_D3 : List StD := []
theorem p19_I3 : LevelN true p19_T 3 p19_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p19_C4x0 : levelOK true p19_T p19_t 3 (p19_D3.map Prod.fst) ((p19_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p19_I4 : LevelN true p19_T 4 p19_D4 := levelStep p19_B p19_W p19_I3 (chunks 32 p19_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p19_C4x0
  ))
theorem p19_L : LowN true p19_R p19_T 5 := lowSearch p19_B p19_I4 (by decide +kernel)
def p20_T : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
def p20_R : List Nat := [0, 1, 2, 3]
def p20_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p20_B : baseOK p20_T p20_R p20_E = true := by decide +kernel
def p20_Z : List SliceD := [(pw4,4,[0, 1, 3])]
theorem p20_Y : ∀ s ∈ p20_Z, SliceN true p20_R p20_T s := by
  unfold p20_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p20_B p3_B p3_L (by decide +kernel),by simp⟩
def p20_C : List (Nat × List Nat) := [(0,[])]
def p20_t : Tabs := (p20_C.map (mkCut true p20_Z),[],[],[])
theorem p20_W : TabsP true p20_R p20_T p20_t := ⟨cutsGood p20_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p20_D4 : List StD := [
([pw3,pw2,pw5,pw6],[0],[1,1,1,1,1,1])]
def p20_D3 : List StD := []
theorem p20_I3 : LevelN true p20_T 3 p20_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C4x0 : levelOK true p20_T p20_t 3 (p20_D3.map Prod.fst) ((p20_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p20_I4 : LevelN true p20_T 4 p20_D4 := levelStep p20_B p20_W p20_I3 (chunks 32 p20_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C4x0
  ))
theorem p20_L : LowN true p20_R p20_T 5 := lowSearch p20_B p20_I4 (by decide +kernel)
def p21_T : Nat := 0xfeeefeeefeeefeeefeeefeeefeeefeee
def p21_R : List Nat := [0, 1, 2, 3]
def p21_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12)]
theorem p21_B : baseOK p21_T p21_R p21_E = true := by decide +kernel
theorem p21_L : LowN true p21_R p21_T 3 := lowCount p21_B (by decide +kernel)
def p22_T : Nat := 0xa888a888a888a888a888a888a888a888
def p22_R : List Nat := [0, 1, 2, 3]
def p22_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,9,13),(3,5,13)]
theorem p22_B : baseOK p22_T p22_R p22_E = true := by decide +kernel
theorem p22_L : LowN true p22_R p22_T 3 := lowCount p22_B (by decide +kernel)
def p23_T : Nat := 0xeee8e8a8eee8e8a8eee8e8a8eee8e8a8
def p23_R : List Nat := [0, 1, 2, 3, 4]
def p23_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,6,14),(4,6,22)]
theorem p23_B : baseOK p23_T p23_R p23_E = true := by decide +kernel
def p23_Z : List SliceD := [(pw1,5,[1, 2, 3, 4]),(pw2,5,[0, 2, 3, 4]),(pw20,4,[2, 3, 4]),(pw4,5,[0, 1, 3, 4]),(pw6,5,[0, 1, 2, 4]),(pw17,5,[0, 1, 2, 4]),(pw40,5,[0, 1, 2, 3]),(pw41,5,[0, 1, 2, 3]),(pw142,4,[0, 1, 4]),(pw143,4,[0, 1, 3]),(pw144,2,[1, 3, 4]),(pw3,3,[1, 2, 3, 4]),(pw11,2,[0, 3, 4]),(pw0,3,[0, 2, 3, 4])]
theorem p23_Y : ∀ s ∈ p23_Z, SliceN true p23_R p23_T s := by
  unfold p23_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p23_B p19_B p19_L (by decide +kernel),mkSlice (w:=2) p23_B p9_B p9_L (by decide +kernel),mkSlice (w:=2) p23_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p23_B p14_B p14_L (by decide +kernel),mkSlice (w:=8) p23_B p20_B p20_L (by decide +kernel),mkSlice (w:=0) p23_B p8_B p8_L (by decide +kernel),mkSlice (w:=16) p23_B p20_B p20_L (by decide +kernel),mkSlice (w:=0) p23_B p8_B p8_L (by decide +kernel),mkSlice (w:=8) p23_B p3_B p3_L (by decide +kernel),mkSlice (w:=16) p23_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p23_B p4_B p4_L (by decide +kernel),mkSlice (w:=1) p23_B p21_B p21_L (by decide +kernel),mkSlice (w:=2) p23_B p10_B p10_L (by decide +kernel),mkSlice (w:=0) p23_B p22_B p22_L (by decide +kernel),by simp⟩
def p23_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(1,[129]),(4,[257]),(8,[]),(6,[257]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(4,[262]),(6,[262])]
def p23_t : Tabs := (p23_C.map (mkCut true p23_Z),[(5,4),(3,1),(3,0),(3,2),(5,1),(25,17),(11,2),(25,9),(19,2),(14,12),(3,17),(14,6),(22,6),(26,24),(5,9),(5,17),(22,20)],[],[[]])
theorem p23_W : TabsP true p23_R p23_T p23_t := ⟨cutsGood p23_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p23_D7 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0,4,12,16,20,28,1,5,17,21,24,29,37,45,3,8,9,13,25,33,41,49],[98499,147781,262745,527457,20870,4762,1051810,8988,2100516,8760])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p23_D6 : List StD := [
([pw3,pw2,pw5,pw145,pw6,pw40],[0,8,12,40,48,5,36,44,52,17,56,1,20,28,32,45,53,57,61],[16419,5,4,2121,2193,550,65826,106,178,1,131660,262804,5384,9488,32792]),
([pw11,pw3,pw2,pw5,pw6,pw40],[8,13,12,40,48,60,64,1,68,72,17,0,16,20,24,28,37,45,57,61,65],[2275,5,1,12384,49248,131,163,267,531,5,1048585,65553,263436,525844,131096])]
def p23_D5 : List StD := []
theorem p23_I5 : LevelN true p23_T 5 p23_D5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p23_C6x0 : levelOK true p23_T p23_t 5 (p23_D5.map Prod.fst) ((p23_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p23_I6 : LevelN true p23_T 6 p23_D6 := levelStep p23_B p23_W p23_I5 (chunks 32 p23_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p23_C6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p23_C7x0 : levelOK true p23_T p23_t 6 (p23_D6.map Prod.fst) ((p23_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p23_I7 : LevelN true p23_T 7 p23_D7 := levelStep p23_B p23_W p23_I6 (chunks 32 p23_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p23_C7x0
  ))
theorem p23_L : LowN true p23_R p23_T 8 := lowSearch p23_B p23_I7 (by decide +kernel)
def p24_T : Nat := 0xa8808000a8808000a8808000a8808000
def p24_R : List Nat := [0, 1, 2, 3, 4]
def p24_E : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15),(4,7,23)]
theorem p24_B : baseOK p24_T p24_R p24_E = true := by decide +kernel
def p24_Z : List SliceD := [(pw3,7,[1, 2, 3, 4])]
theorem p24_Y : ∀ s ∈ p24_Z, SliceN true p24_R p24_T s := by
  unfold p24_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p24_B p5_B p5_L (by decide +kernel),by simp⟩
def p24_C : List (Nat × List Nat) := [(0,[])]
def p24_t : Tabs := (p24_C.map (mkCut true p24_Z),[],[],[])
theorem p24_W : TabsP true p24_R p24_T p24_t := ⟨cutsGood p24_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p24_D7 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0],[1,1,1,1,1,1,1,1,1,1])]
def p24_D6 : List StD := []
theorem p24_I6 : LevelN true p24_T 6 p24_D6 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p24_C7x0 : levelOK true p24_T p24_t 6 (p24_D6.map Prod.fst) ((p24_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p24_I7 : LevelN true p24_T 7 p24_D7 := levelStep p24_B p24_W p24_I6 (chunks 32 p24_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p24_C7x0
  ))
theorem p24_L : LowN true p24_R p24_T 8 := lowSearch p24_B p24_I7 (by decide +kernel)
def p25_T : Nat := 0xeeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0
def p25_R : List Nat := [0, 1, 2, 3, 4]
def p25_E : List (Nat × Nat × Nat) := [(0,4,5),(1,12,14),(2,1,5),(3,1,9),(4,1,17)]
theorem p25_B : baseOK p25_T p25_R p25_E = true := by decide +kernel
def p25_Z : List SliceD := [(pw2,7,[0, 2, 3, 4])]
theorem p25_Y : ∀ s ∈ p25_Z, SliceN true p25_R p25_T s := by
  unfold p25_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=2) p25_B p7_B p7_L (by decide +kernel),by simp⟩
def p25_C : List (Nat × List Nat) := [(0,[])]
def p25_t : Tabs := (p25_C.map (mkCut true p25_Z),[],[],[])
theorem p25_W : TabsP true p25_R p25_T p25_t := ⟨cutsGood p25_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p25_D7 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0],[1,1,1,1,1,1,1,1,1,1])]
def p25_D6 : List StD := []
theorem p25_I6 : LevelN true p25_T 6 p25_D6 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p25_C7x0 : levelOK true p25_T p25_t 6 (p25_D6.map Prod.fst) ((p25_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p25_I7 : LevelN true p25_T 7 p25_D7 := levelStep p25_B p25_W p25_I6 (chunks 32 p25_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p25_C7x0
  ))
theorem p25_L : LowN true p25_R p25_T 8 := lowSearch p25_B p25_I7 (by decide +kernel)
def p26_T : Nat := 0xfeeeeee0feeeeee0feeeeee0feeeeee0
def p26_R : List Nat := [0, 1, 2, 3, 4]
def p26_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,1,9),(4,1,17)]
theorem p26_B : baseOK p26_T p26_R p26_E = true := by decide +kernel
def p26_Z : List SliceD := [(pw1,6,[1, 2, 3, 4])]
theorem p26_Y : ∀ s ∈ p26_Z, SliceN true p26_R p26_T s := by
  unfold p26_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p26_B p12_B p12_L (by decide +kernel),by simp⟩
def p26_C : List (Nat × List Nat) := [(0,[])]
def p26_t : Tabs := (p26_C.map (mkCut true p26_Z),[],[],[])
theorem p26_W : TabsP true p26_R p26_T p26_t := ⟨cutsGood p26_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p26_D6 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0],[1,1,1,1,1,1,1,1,1,1])]
def p26_D5 : List StD := []
theorem p26_I5 : LevelN true p26_T 5 p26_D5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p26_C6x0 : levelOK true p26_T p26_t 5 (p26_D5.map Prod.fst) ((p26_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p26_I6 : LevelN true p26_T 6 p26_D6 := levelStep p26_B p26_W p26_I5 (chunks 32 p26_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p26_C6x0
  ))
theorem p26_L : LowN true p26_R p26_T 7 := lowSearch p26_B p26_I6 (by decide +kernel)
def p27_T : Nat := 0xa8888880a8888880a8888880a8888880
def p27_R : List Nat := [0, 1, 2, 3, 4]
def p27_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,3,19)]
theorem p27_B : baseOK p27_T p27_R p27_E = true := by decide +kernel
def p27_Z : List SliceD := [(pw3,6,[1, 2, 3, 4])]
theorem p27_Y : ∀ s ∈ p27_Z, SliceN true p27_R p27_T s := by
  unfold p27_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p27_B p12_B p12_L (by decide +kernel),by simp⟩
def p27_C : List (Nat × List Nat) := [(0,[])]
def p27_t : Tabs := (p27_C.map (mkCut true p27_Z),[],[],[])
theorem p27_W : TabsP true p27_R p27_T p27_t := ⟨cutsGood p27_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p27_D6 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0],[1,1,1,1,1,1,1,1,1,1])]
def p27_D5 : List StD := []
theorem p27_I5 : LevelN true p27_T 5 p27_D5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p27_C6x0 : levelOK true p27_T p27_t 5 (p27_D5.map Prod.fst) ((p27_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p27_I6 : LevelN true p27_T 6 p27_D6 := levelStep p27_B p27_W p27_I5 (chunks 32 p27_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p27_C6x0
  ))
theorem p27_L : LowN true p27_R p27_T 7 := lowSearch p27_B p27_I6 (by decide +kernel)
def ptopT : Nat := 0xfee8fe00fe808000fee8fe00fe808000
def ptopR : List Nat := [0, 1, 2, 3, 4, 5]
def ptopE : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15),(4,7,23),(5,9,41)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(pw40,9,[3, 1, 2, 0, 5]),(pw146,9,[3, 4, 2, 0, 1]),(pw1,8,[3, 2, 1, 4, 5]),(pw2,8,[3, 4, 5, 2, 0]),(pw0,8,[3, 2, 0, 4, 5]),(pw3,8,[3, 4, 5, 2, 1]),(pw5,8,[3, 4, 5, 1, 0]),(pw4,8,[3, 1, 0, 4, 5]),(pw17,8,[4, 1, 2, 0, 5]),(pw147,8,[3, 4, 2, 0, 1]),(pw148,7,[0, 1, 2, 5]),(pw6,7,[4, 5, 2, 0, 1]),(pw149,6,[5, 1, 2, 0]),(pw150,7,[0, 1, 2, 3]),(pw151,6,[4, 1, 2, 0]),(pw45,4,[3, 4, 5]),(pw41,7,[3, 5, 2, 0, 1]),(pw61,4,[3, 4, 5]),(pw52,4,[3, 4, 5]),(pw152,6,[3, 1, 2, 0]),(pw153,4,[1, 3, 4]),(pw154,4,[2, 3, 4]),(pw155,4,[0, 3, 4]),(pw156,5,[4, 1, 0, 5]),(pw157,4,[0, 1, 5]),(pw64,5,[3, 2, 1, 5]),(pw124,4,[1, 2, 5]),(pw158,4,[0, 1, 3]),(pw159,1,[0, 4]),(pw160,2,[0, 3, 5]),(pw161,1,[1, 4]),(pw162,2,[1, 3, 5]),(pw163,2,[0, 4, 5]),(pw164,2,[1, 4, 5]),(pw9,5,[4, 2, 1, 5]),(pw43,5,[3, 1, 0, 5]),(pw46,5,[3, 2, 1, 5]),(pw165,4,[1, 2, 3]),(pw166,1,[0, 4]),(pw167,1,[1, 4]),(pw168,5,[4, 1, 2, 0]),(pw11,5,[3, 4, 5, 0]),(pw31,5,[3, 4, 5, 1]),(pw8,5,[3, 4, 5, 1]),(pw21,5,[4, 2, 0, 5]),(pw169,4,[0, 2, 5]),(pw19,5,[3, 4, 5, 2]),(pw143,5,[3, 1, 0, 5]),(pw170,2,[2, 3, 5]),(pw171,1,[2, 4]),(pw172,2,[2, 4, 5]),(pw173,3,[0, 1, 2, 4]),(pw174,1,[1, 2]),(pw175,2,[2, 3, 4]),(pw42,3,[4, 5, 0, 1]),(pw33,3,[4, 5, 0, 2]),(pw176,2,[3, 4, 5]),(pw177,2,[0, 1, 4]),(pw178,2,[3, 4, 5])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=16) ptopB p13_B p13_L (by decide +kernel),mkSlice (w:=0) ptopB p16_B p16_L (by decide +kernel),mkSlice (w:=0) ptopB p18_B p18_L (by decide +kernel),mkSlice (w:=2) ptopB p23_B p23_L (by decide +kernel),mkSlice (w:=0) ptopB p18_B p18_L (by decide +kernel),mkSlice (w:=1) ptopB p23_B p23_L (by decide +kernel),mkSlice (w:=4) ptopB p23_B p23_L (by decide +kernel),mkSlice (w:=0) ptopB p18_B p18_L (by decide +kernel),mkSlice (w:=0) ptopB p24_B p24_L (by decide +kernel),mkSlice (w:=32) ptopB p25_B p25_L (by decide +kernel),mkSlice (w:=16) ptopB p5_B p5_L (by decide +kernel),mkSlice (w:=8) ptopB p26_B p26_L (by decide +kernel),mkSlice (w:=8) ptopB p12_B p12_L (by decide +kernel),mkSlice (w:=48) ptopB p7_B p7_L (by decide +kernel),mkSlice (w:=8) ptopB p12_B p12_L (by decide +kernel),mkSlice (w:=3) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=0) ptopB p27_B p27_L (by decide +kernel),mkSlice (w:=6) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=5) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=16) ptopB p12_B p12_L (by decide +kernel),mkSlice (w:=5) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=3) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=6) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=4) ptopB p19_B p19_L (by decide +kernel),mkSlice (w:=20) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=17) ptopB p9_B p9_L (by decide +kernel),mkSlice (w:=17) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=48) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=36) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=0) ptopB p4_B p4_L (by decide +kernel),mkSlice (w:=36) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=0) ptopB p4_B p4_L (by decide +kernel),mkSlice (w:=8) ptopB p11_B p11_L (by decide +kernel),mkSlice (w:=8) ptopB p11_B p11_L (by decide +kernel),mkSlice (w:=1) ptopB p19_B p19_L (by decide +kernel),mkSlice (w:=20) ptopB p9_B p9_L (by decide +kernel),mkSlice (w:=16) ptopB p8_B p8_L (by decide +kernel),mkSlice (w:=48) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=34) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=33) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=32) ptopB p19_B p19_L (by decide +kernel),mkSlice (w:=2) ptopB p8_B p8_L (by decide +kernel),mkSlice (w:=4) ptopB p8_B p8_L (by decide +kernel),mkSlice (w:=1) ptopB p8_B p8_L (by decide +kernel),mkSlice (w:=2) ptopB p19_B p19_L (by decide +kernel),mkSlice (w:=18) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=1) ptopB p8_B p8_L (by decide +kernel),mkSlice (w:=16) ptopB p8_B p8_L (by decide +kernel),mkSlice (w:=0) ptopB p4_B p4_L (by decide +kernel),mkSlice (w:=34) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=8) ptopB p11_B p11_L (by decide +kernel),mkSlice (w:=0) ptopB p15_B p15_L (by decide +kernel),mkSlice (w:=24) ptopB p2_B p2_L (by decide +kernel),mkSlice (w:=0) ptopB p4_B p4_L (by decide +kernel),mkSlice (w:=12) ptopB p21_B p21_L (by decide +kernel),mkSlice (w:=10) ptopB p21_B p21_L (by decide +kernel),mkSlice (w:=1) ptopB p11_B p11_L (by decide +kernel),mkSlice (w:=32) ptopB p4_B p4_L (by decide +kernel),mkSlice (w:=4) ptopB p11_B p11_L (by decide +kernel),by simp⟩
def ptopC : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(0,[388]),(1,[524]),(0,[389]),(1,[525]),(0,[395]),(1,[395]),(10,[]),(1,[384]),(11,[]),(12,[]),(0,[385]),(1,[385]),(0,[387]),(1,[387]),(1,[258]),(1,[388]),(13,[]),(1,[262]),(1,[128]),(1,[131]),(0,[513]),(8,[388]),(14,[]),(15,[]),(1,[517]),(16,[]),(17,[]),(0,[260]),(13,[260]),(1,[520,151]),(6,[525]),(7,[261]),(8,[389]),(9,[525]),(7,[260]),(6,[524]),(0,[388,389]),(1,[524,525]),(4,[128]),(8,[391]),(8,[390]),(2,[128]),(2,[131]),(10,[128]),(9,[524]),(1,[524,256]),(2,[129]),(6,[527]),(6,[526]),(9,[257]),(1,[257]),(3,[385]),(4,[129]),(12,[388]),(18,[]),(0,[388,257]),(2,[260]),(10,[260]),(4,[259]),(7,[257]),(9,[520]),(1,[520]),(7,[259]),(2,[263]),(2,[262]),(9,[387]),(0,[387,260]),(14,[260]),(1,[387,520]),(12,[260]),(2,[130]),(9,[258]),(4,[130]),(4,[388]),(7,[263]),(7,[262]),(9,[260]),(1,[260]),(2,[388]),(2,[390]),(2,[391]),(13,[128]),(2,[389]),(9,[262]),(4,[391]),(4,[517]),(1,[526]),(1,[527]),(10,[393]),(0,[521]),(2,[517]),(7,[522]),(4,[522]),(4,[521]),(1,[523]),(1,[522]),(4,[384]),(10,[130]),(10,[131]),(6,[128]),(7,[384]),(2,[384]),(1,[524,128]),(4,[387]),(2,[387]),(2,[385]),(6,[131]),(7,[387]),(1,[131,524]),(2,[513]),(6,[257]),(7,[513]),(4,[513]),(4,[514]),(6,[258]),(7,[514]),(2,[514]),(2,[526]),(19,[]),(6,[262]),(7,[526]),(4,[526]),(4,[392]),(1,[391]),(1,[519]),(1,[525,148]),(13,[129]),(10,[261]),(6,[515]),(6,[512]),(6,[514]),(2,[261]),(0,[261]),(13,[261]),(1,[521]),(3,[512]),(1,[384,521]),(7,[256]),(4,[256]),(13,[384]),(8,[261]),(5,[385]),(10,[129]),(13,[393]),(12,[389]),(20,[]),(0,[389,257]),(14,[389]),(12,[261]),(6,[513]),(3,[515]),(13,[386]),(0,[387,261]),(14,[261]),(1,[387,521]),(5,[386]),(3,[386]),(3,[384]),(13,[395]),(1,[258,525]),(3,[516]),(6,[518]),(6,[516]),(0,[263]),(0,[262]),(5,[390]),(3,[390]),(3,[388]),(0,[390]),(0,[391]),(1,[262,525]),(3,[393]),(5,[393]),(3,[395]),(3,[523]),(3,[521]),(6,[523]),(21,[]),(10,[386]),(9,[521]),(3,[128]),(5,[128]),(9,[128]),(1,[525,128]),(3,[131]),(3,[129]),(5,[131]),(1,[131,525]),(3,[257]),(5,[257]),(22,[]),(5,[258]),(3,[258]),(5,[262]),(3,[262]),(10,[258]),(13,[259]),(0,[394]),(1,[394,151]),(6,[384]),(7,[128]),(10,[257]),(13,[388]),(1,[512]),(2,[256]),(3,[527]),(4,[263]),(6,[387]),(13,[258]),(1,[395,512]),(8,[395]),(6,[385]),(3,[524]),(3,[525]),(13,[389]),(2,[257]),(12,[395]),(0,[395,129]),(14,[395]),(10,[262]),(13,[262]),(12,[262]),(1,[387,523]),(6,[386]),(10,[256]),(2,[258]),(1,[395,514]),(2,[392]),(4,[260]),(4,[261]),(8,[128]),(1,[516]),(6,[388]),(2,[394]),(1,[395,516]),(2,[395]),(8,[130]),(1,[518]),(2,[393]),(2,[521]),(1,[392]),(1,[393]),(6,[393]),(9,[395]),(2,[522]),(8,[526]),(9,[523]),(8,[392]),(8,[393]),(1,[395,128]),(1,[131,395]),(10,[389]),(7,[517]),(1,[386]),(8,[517]),(9,[384]),(10,[385]),(1,[515]),(9,[512]),(3,[513]),(5,[521]),(13,[385]),(12,[129]),(5,[523]),(1,[513]),(12,[387]),(1,[385,148]),(1,[259,151]),(13,[394]),(0,[259]),(13,[390]),(7,[131]),(2,[259]),(9,[515]),(1,[256]),(6,[521]),(8,[525]),(8,[384]),(1,[388,21]),(8,[258]),(2,[515]),(8,[514]),(10,[129,128]),(13,[129,392]),(13,[128,392]),(3,[387]),(13,[128,129]),(1,[524,525,256]),(8,[388,389]),(6,[525,524]),(1,[524,257]),(13,[128,393]),(10,[128,129]),(12,[388,389]),(0,[388,389,257]),(10,[260,261]),(12,[261,260]),(2,[261,260]),(0,[260,261]),(13,[260,261]),(1,[520,521]),(13,[386,261]),(0,[387,260,261]),(14,[260,261]),(1,[387,520,521]),(7,[261,260]),(1,[524,260]),(12,[389,388]),(3,[389]),(10,[129,393]),(13,[129,128]),(10,[128,393]),(14,[388]),(9,[524,525]),(7,[260,261]),(13,[261,260]),(9,[520,521]),(5,[524]),(2,[260,261]),(10,[386,260]),(6,[525,128]),(7,[261,384]),(7,[260,384]),(6,[524,128]),(6,[524,525]),(1,[524,525,128]),(6,[131,525]),(7,[387,261]),(7,[387,260]),(6,[131,524]),(1,[131,524,525]),(6,[525,257]),(7,[261,513]),(1,[525,524]),(7,[260,513]),(6,[524,257]),(7,[514,261]),(7,[514,260]),(6,[258,524]),(19,[389]),(19,[388]),(6,[262,525]),(7,[526,261]),(7,[526,260]),(6,[262,524]),(3,[512,405]),(8,[260]),(10,[260,19]),(6,[513,406]),(3,[513,406]),(1,[385,534]),(4,[257]),(8,[260,407]),(12,[391]),(4,[129,404]),(12,[390]),(1,[257,148]),(5,[385,148]),(2,[129,404]),(16,[524]),(4,[131]),(10,[128,273]),(23,[]),(24,[]),(4,[131,407]),(2,[131,407]),(13,[128,394]),(2,[391,21]),(2,[129,407]),(0,[388,259]),(7,[392]),(25,[]),(0,[260,405]),(26,[]),(2,[388,21]),(6,[129]),(1,[260,21]),(4,[388,21]),(1,[262,405]),(1,[262,406]),(0,[394,151]),(1,[262,533]),(1,[262,534]),(0,[260,406]),(0,[388,279]),(27,[]),(0,[259,391]),(4,[391,21]),(0,[259,390]),(7,[385]),(1,[262,21]),(1,[520,407]),(2,[260,535]),(1,[392,532]),(1,[395,532]),(1,[395,535]),(1,[392,534]),(1,[526,279]),(7,[521]),(1,[520,387]),(1,[520,384]),(10,[260,385]),(4,[521,22]),(7,[521,22]),(1,[387,522]),(2,[518]),(4,[518]),(1,[524,277]),(1,[257,526]),(4,[518,21]),(1,[257,527]),(10,[394]),(10,[128,394]),(2,[518,21]),(0,[388,21]),(2,[384,533]),(6,[128,277]),(7,[384,533]),(4,[384,533]),(1,[524,131]),(4,[387,526]),(15,[131]),(1,[131,526]),(1,[131,527]),(6,[262,131]),(7,[526,387]),(2,[526,387]),(28,[]),(29,[]),(30,[]),(31,[]),(1,[258,532]),(1,[514]),(1,[258,535]),(1,[256,534]),(1,[514,279]),(10,[260,403]),(8,[260,535]),(1,[129,526]),(2,[526,21]),(1,[129,527]),(6,[262,21]),(7,[526,21]),(1,[129,524]),(4,[526,21]),(32,[]),(33,[]),(34,[]),(4,[259,128]),(7,[261,22]),(0,[389,22]),(4,[128,279]),(1,[393,533]),(1,[525,278]),(1,[525,22]),(5,[384]),(4,[129,276]),(1,[257,404]),(10,[129,272]),(1,[257,532]),(5,[387]),(8,[389,276]),(3,[385,148]),(1,[525,257,152]),(13,[129,393]),(5,[388,21]),(5,[131,404]),(16,[525]),(4,[131,279]),(5,[387,151]),(3,[387,151]),(1,[525,259,155]),(13,[129,394]),(0,[389,259]),(5,[525]),(7,[258,151]),(4,[258,151]),(3,[514]),(4,[388,279]),(10,[129,274]),(13,[129,274]),(35,[]),(0,[389,278]),(3,[388,21]),(1,[525,260,25]),(13,[261,16]),(4,[395,151]),(1,[390,535]),(1,[390,532]),(1,[390,279]),(1,[260,406]),(36,[]),(3,[518]),(0,[261,404]),(10,[261,16]),(37,[]),(3,[390,21]),(5,[390,21]),(1,[520,405]),(1,[525,276]),(1,[521,387]),(1,[521,384]),(3,[521,22]),(6,[521,22]),(5,[395]),(13,[129,402]),(3,[128,277]),(5,[128,277]),(13,[131]),(13,[130]),(1,[525,131]),(5,[131,262]),(3,[131,262]),(38,[]),(22,[263]),(39,[]),(20,[263]),(10,[129,400]),(1,[525,20]),(3,[262,21]),(5,[262,21]),(22,[261]),(1,[525,129]),(20,[261]),(40,[]),(3,[512,407]),(41,[]),(5,[513]),(3,[526]),(42,[]),(7,[129]),(10,[259,147]),(12,[394]),(12,[392]),(7,[129,404]),(6,[385,148]),(5,[513,148]),(2,[257,404]),(13,[258,389]),(2,[392,21]),(2,[259,404]),(16,[395]),(1,[515,405]),(1,[385,535]),(1,[259,532]),(1,[515,279]),(43,[]),(10,[258,145]),(44,[]),(45,[]),(2,[259,407]),(1,[515,151]),(6,[387,151]),(13,[258,390]),(1,[395,515,155]),(0,[395,131]),(4,[130,277]),(46,[]),(13,[262,17]),(0,[262,405]),(6,[388,21]),(12,[393]),(1,[516,21]),(1,[395,516,25]),(1,[262,532]),(0,[263,406]),(0,[394,149]),(1,[262,535]),(10,[130,275]),(0,[391,279]),(47,[]),(0,[131,392]),(6,[390,21]),(4,[385]),(2,[395,21]),(1,[393,535]),(1,[394,535]),(9,[394]),(1,[523,384]),(14,[262]),(6,[515,277]),(5,[527]),(1,[522,407]),(1,[395,533]),(1,[395,534]),(6,[395]),(1,[128,405]),(1,[128,406]),(13,[258,401]),(0,[395,21]),(13,[256]),(13,[257]),(1,[395,131]),(6,[131,262]),(4,[387,263]),(1,[131,392]),(3,[262,131]),(4,[526,387]),(1,[131,393]),(48,[]),(49,[]),(2,[513,150]),(6,[257,532]),(10,[259,403]),(14,[394]),(1,[394,23]),(1,[129,392]),(1,[129,393]),(1,[129,395]),(50,[]),(1,[256,407]),(1,[259,404]),(1,[387,279]),(9,[256]),(13,[392]),(1,[384,533]),(10,[390]),(4,[257,532]),(2,[521,20]),(10,[389,16]),(9,[385]),(1,[385,532]),(2,[518,23]),(10,[394,19]),(12,[259]),(2,[131,535]),(12,[385]),(10,[385,274]),(9,[259]),(1,[259,407]),(10,[390,17]),(1,[387,533]),(12,[131]),(2,[521,22]),(13,[387]),(4,[258,535]),(1,[258,405]),(1,[385,278]),(4,[131,276]),(1,[524,393,537]),(1,[524,525,282]),(4,[259,151]),(40,[388]),(7,[261,20]),(1,[524,525,280]),(4,[256,149]),(4,[130,276]),(1,[524,394,538]),(10,[128,129,276]),(24,[128]),(1,[524,257,152]),(4,[131,404]),(16,[524,525]),(27,[128]),(1,[524,259,155]),(13,[128,129,394]),(1,[524,525,259,159]),(0,[388,389,259]),(1,[525,392,536]),(1,[525,524,283]),(1,[525,387,536]),(7,[260,21]),(6,[525,129]),(6,[524,129]),(1,[524,260,25]),(13,[128,129,393]),(1,[524,525,260,29]),(14,[388,389]),(7,[261,385]),(7,[260,385]),(1,[524,262,25]),(1,[521,520,411]),(6,[521,406]),(34,[260]),(14,[260,403]),(1,[520,521,387]),(1,[520,521,384]),(10,[260,261,385]),(34,[261]),(1,[520,521,385]),(2,[515,261]),(2,[515,260]),(2,[518,279]),(6,[128,405]),(10,[261,260]),(13,[261,260,405]),(14,[260,17]),(1,[521,259,536]),(0,[261,260,25]),(6,[525,128,281]),(7,[261,384,537]),(7,[260,384,537]),(6,[524,128,281]),(1,[524,525,131]),(2,[387,526]),(6,[131,524,525]),(2,[387,525]),(6,[262,131,525]),(7,[526,387,261]),(7,[526,387,260]),(6,[262,131,524]),(2,[513,276]),(51,[]),(27,[129]),(1,[524,525,24]),(10,[128,129,404]),(6,[525,262,25]),(7,[261,526,25]),(1,[525,129,524]),(7,[260,526,25]),(6,[524,262,25]),(1,[128,407]),(10,[392,129]),(10,[392,131]),(10,[392,130]),(34,[388]),(1,[385,533]),(52,[]),(14,[389,18]),(2,[384,279]),(53,[]),(4,[384,279]),(3,[128,392]),(3,[128,394]),(15,[128]),(20,[260]),(13,[390,17]),(13,[131,402]),(1,[128,404]),(13,[386,145]),(13,[130,402]),(1,[128,532]),(34,[391]),(3,[394,131]),(3,[128,393]),(10,[129,395]),(17,[128]),(18,[128]),(1,[521,20,782]),(13,[261,128]),(13,[261,131]),(13,[261,256]),(13,[261,259]),(42,[257]),(37,[129]),(6,[257,656]),(13,[261,512]),(1,[521,20,780]),(6,[257,658]),(13,[261,514]),(54,[]),(55,[]),(56,[]),(24,[129]),(14,[389,388]),(57,[]),(13,[129,128,276]),(13,[129,128,278]),(13,[128,129,276]),(2,[513,276,772]),(12,[389,520]),(15,[257]),(1,[524,525,24,906]),(51,[128]),(1,[520,521,24,908]),(13,[260,129,277]),(27,[130]),(1,[520,521,24,910]),(12,[261,403]),(1,[128,535]),(20,[262]),(22,[260]),(21,[260]),(58,[])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[(25,24),(26,24),(15,14),(15,13),(28,24),(15,11),(23,22),(26,18),(15,7),(26,10),(23,7),(42,10),(41,40),(41,9),(23,21),(25,17),(25,9),(42,40),(23,19),(44,40),(44,12),(51,19),(41,33),(51,35),(43,11),(53,52),(54,52),(51,50),(51,49),(28,20),(28,12),(15,10),(54,50),(26,19),(42,34),(54,38),(54,22),(15,6),(53,49),(15,3),(44,36),(53,37),(41,11),(43,3),(41,8),(15,5),(41,13),(41,1),(15,12),(25,21),(53,21),(15,39),(25,8),(26,8),(44,4),(23,39),(15,9),(25,19),(42,2),(23,20),(51,48),(41,49),(25,16),(27,11),(41,0),(23,3),(42,50),(44,24),(25,1),(23,18),(28,4)],[],[[],[1],[0,1],[0,1,0],[0],[1,0]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD11 : List StD := [
([pw3,pw2,pw5,pw6,pw40,pw147],[3,0,4,37,45,7,11,19,23,1,5,9,13,17,21,29,33,41,53,25,49,57,61,65,69,73,77,81,85,89,93,15],[7777,2147510817,623169,133195,1310741,30144,6325408,8392874,17039508,33661185,147723,201326868,196619,805306389,1073741855])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD10 : List StD := [
([pw7,pw3,pw2,pw5,pw6,pw40,pw147],[8,3,16,41,97,101,105,40,44,1,5,21,33,23,12,65,0,4,20,24,28,32,36,49,61,69,73,77,81,85,89,93],[16385,262149,1574913,2101251,73737,4325393,16391,545,545,8388641,545,1092,1092,33554500,1092,83900418,34954,402661650,37002,1610613010,2147484058]),
([pw3,pw2,pw22,pw5,pw6,pw40,pw147],[20,3,12,16,9,13,81,109,113,121,48,52,23,17,117,0,4,8,24,28,32,36,21,33,41,53,61,65,73,77,85,89,93],[15,8,145,145,145,145,131077,300,300,300,300,794625,1064963,33283,2162753,335572994,138417666,570431554,25167362,3221227586,4294970946]),
([pw8,pw3,pw2,pw5,pw6,pw40,pw147],[24,3,28,8,9,17,53,65,101,56,60,113,129,13,33,41,61,19,0,4,12,16,20,32,36,45,77,85,89,93,125,15],[4,3147777,4194305,8454147,2147745921,17301569,280,1073741837,280,280,280,4133,223234,41602,33688642,4133,67108901,4133,49794,402654274,536872642]),
([pw126,pw3,pw2,pw5,pw6,pw40,pw147],[8,32,64,65,25,29,53,68,13,21,41,101,117,3,19,23,0,4,12,16,20,24,28,36,5,9,17,45,69,77,81,93,109,133,137,7,11],[33554433,786689,6291969,1048579,65549,8519745,2065,4294967313,8589934595,13,2065,68803420928,4130,1036,402677952,4130,1036,35970384064,14,17179869218,2147483660]),
([pw3,pw2,pw5,pw6,pw23,pw40,pw147],[20,32,1,72,80,61,76,84,9,33,65,41,53,105,129,141,3,19,23,4,8,12,16,24,28,36,5,13,17,21,45,49,81,89,133,145,7,11],[261,261,17179869191,3,261,2147483653,138445979648,554,6299649,3152,1073950848,554,25182209,3152,73014726784,1048577,554,8589934634,98321,34393817217,33872]),
([pw9,pw3,pw2,pw5,pw6,pw40,pw147],[8,76,32,9,41,117,88,1,65,85,92,29,57,73,137,3,7,0,4,12,16,20,24,28,36,5,17,49,53,69,77,81,93,149,11,19,23],[4,1576961,12591105,2097153,17180000273,17039873,137,137,8589934605,137,134217737,100773888,2086,338,35165079040,2086,338,71940769280,16678,16422,4294967378]),
([pw142,pw3,pw2,pw5,pw6,pw40,pw147],[24,64,65,33,53,117,129,96,1,5,37,45,73,3,0,4,8,12,16,20,28,36,9,13,21,49,69,93,153,157,161,7,11,19],[590081,393729,16777217,1048577,16391,2129937,6455042816,4161,42,1030,33564816,268435521,42,1030,8657045648,536870915,7,4161,46,1073741834,134217734]),
([pw64,pw3,pw2,pw5,pw6,pw40,pw147],[8,0,64,9,61,85,121,76,104,49,100,33,37,53,57,73,141,3,4,12,16,20,24,28,36,5,17,81,11,19,23],[2,1589249,12615681,131093,2097155,17039393,521,521,29,11,521,1979891712,2196,4162,9504,2196,4162,134219040,65602,8628,65602]),
([pw143,pw3,pw2,pw5,pw6,pw40,pw147],[76,24,0,64,61,77,85,121,104,21,41,108,1,5,29,45,3,4,8,12,16,20,28,36,9,13,53,165,7,11],[2363395,1581059,6,65563,4194311,8519747,855715840,546,16409,1157,35136,546,16409,1157,67111232,27,39,546,1157,33113,134217861]),
([pw3,pw2,pw5,pw6,pw40,pw147,pw179],[20,104,4,49,5,17,41,65,109,33,61,3,19,23,8,12,16,24,28,36,64,13,21,29,37,57,73,101,7,11],[265,134217737,265,265,13,5,543174704,301995536,194,6,98321,67120672,194,6,393249,194,6,9439233,524294,16777219,16389]),
([pw180,pw3,pw2,pw5,pw6,pw40,pw147],[8,104,4,41,3,13,21,33,65,109,7,64,49,61,0,12,16,20,24,28,36,5,17,57,73,101],[4,98337,786497,2193,18443,131077,4609,33554945,4609,11,7,6292592,8398000,266,6,16786640,266,6,266,6,1048582]),
([pw3,pw2,pw5,pw44,pw6,pw40,pw147],[64,104,33,112,141,1,5,17,45,137,3,9,13,21,41,53,7,11,0,4,8,12,16,20,24,28,65,81,89,93,165,15,19,23],[203872,2147560608,9437217,517,16401,33034,12885045440,6291521,268435461,1073741841,33034,50331777,517,536870929,134217994,3,67108865,525323,262149,517,16401]),
([pw148,pw3,pw2,pw5,pw6,pw40,pw147],[64,53,104,33,37,116,9,13,21,3,0,1,5,17,45,65,137,7,11,4,8,12,16,20,24,28,32,81,89,121,15,19,23],[9437249,6291585,50331905,1025,67108865,524295,400064,1073883968,65545,32785,16422,6442725760,268435465,32785,16422,65545,536870929,134217766,1033,15,531]),
([pw3,pw2,pw5,pw6,pw40,pw147,pw181],[104,76,32,37,4,120,137,41,1,5,9,13,17,21,89,3,7,11,8,12,16,20,24,28,36,25,57,65,73,161,15,19,23],[233216,1073853696,16454,171,17,35913729,6442596864,16454,134217770,17,68681729,536870982,171,17,281018369,111,21,19,16777259,139,4]),
([pw151,pw3,pw2,pw5,pw6,pw40,pw147],[104,4,65,32,9,13,21,89,36,1,5,17,37,137,3,7,11,0,8,12,16,20,24,28,41,53,161,15,19,23],[2359313,1572897,12582977,3,131333,33554433,116272,134269520,8328,4101,3,805375072,8328,4101,3,67109000,16777221,3,13,3,259]),
([pw152,pw3,pw2,pw5,pw6,pw40,pw147],[36,4,0,61,141,3,64,76,25,57,73,1,5,17,29,33,93,7,11,8,12,16,20,24,28,32,165,15,19,23],[4718849,3146241,25166849,33554473,3,5,400160,134360352,16584,65556,3,805582336,16584,67108884,3,32968,65556,3,32820,3,3])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD9 : List StD := [
([pw3,pw2,pw5,pw6,pw35,pw40,pw147],[128,8,124,16,13,33,76,9,53,132,1,5,41,73,165,4,24,28,36,81,169,173],[26,1154,166,134,1154,259,2072,60,28,2072,1048585,8741,196609,12864,524545,2,4197,2097445,16449,295169,16449]),
([pw182,pw3,pw2,pw5,pw6,pw40,pw147],[76,28,16,61,152,13,24,136,140,144,148,5,17,21,25,8,20,32,36,156,53,157,169,177,181,185,189],[98305,193,67,131337,3,262273,2084,12290,16905,1025,9978384,38,16777229,2053,4194356,2097155,4099,33562642,265,67108889,1025]),
([pw7,pw22,pw5,pw6,pw40,pw147],[3,16,20,1,184,188,13,21,53,65,41,49,117,23,48,124,160,164,168,172,176,180,17,33,61,73,77,81,85,89,93,169,181,193],[8589934598,196738,4295229506,16450,2148008002,7340044,36876,2060,2060,50344065,1681,201335073,8390161,805306657,1073742641]),
([pw7,pw3,pw2,pw42,pw5,pw6,pw40,pw147],[132,124,192,204,212,73,121,81,12,20,24,28,40,44,180,196,200,208,216,220,89,93,153,197,3,23],[32772,65540,33554438,3076,7,5,5,16777229,523,41,11,9,9,262,37,7,5,5,131075,16386,4178,270466,8388611,113,4194337,82,1572994,2097232]),
([pw7,pw3,pw2,pw5,pw6,pw28,pw40,pw147],[180,224,212,248,252,21,144,228,256,65,64,76,33,93,3,12,20,28,44,124,208,216,232,236,240,244,260,41,77,85,97,161,197,23],[130,4194306,131203,3074,8589934723,3074,1098907650,33570826,35,274,65539,258,258,41,88,32777,72,72,4294967333,5,549,268435489,1048577,201855504,2147487764,24581,539230209,8724]),
([pw9,pw3,pw16,pw2,pw5,pw6,pw40,pw147],[264,268,272,144,41,288,9,308,76,316,85,137,11,12,20,24,28,64,148,276,280,284,292,296,300,304,312,29,49,65,93,149,3],[3,4101,8197,98305,524289,266259,3146753,16389,69,97,2147483715,83,268435521,4194308,8388644,131334,278,16777228,4294967332,14,30,12,42,58,40,570427538,201330306,1073742482]),
([pw142,pw7,pw3,pw2,pw5,pw6,pw40,pw147],[180,320,212,144,65,328,33,73,41,3,12,16,20,28,40,44,96,204,216,224,228,232,256,324,53,93,97,153,157,161],[515,4099,3081,524289,131073,16405,17072129,1048578,2097162,8195,70,262,75563010,554,131,70,22,4194306,169,44,28,40,268435461,21,134217857,340,536870980,33554452]),
([pw7,pw3,pw2,pw43,pw5,pw6,pw40,pw147],[176,332,132,352,212,252,21,40,117,201,64,76,364,65,93,3,12,20,24,44,104,216,336,340,344,348,356,360,205,23],[4194306,8388610,536870915,262147,3074,3074,51380226,32778,131081,73,44,12,12,65539,67,38,6,6,67108865,33041,134217729,2621953,337,209,4673,24736,268440368,24752]),
([pw143,pw7,pw3,pw2,pw5,pw6,pw40,pw147],[180,360,212,40,376,21,61,252,85,144,3,64,76,256,364,41,12,16,20,28,44,108,216,228,232,352,368,372,121,165,205],[1027,262147,196609,67108865,1093,33554433,5243137,8388610,16777218,524291,6150,6150,136315138,1042,35,198,8206,8194,49,724,540,528,101,45,16673,268468236,1073758660,536903820]),
([pw7,pw3,pw2,pw5,pw6,pw40,pw147,pw183],[144,364,380,1,41,44,400,24,180,384,392,5,65,77,23,28,128,176,212,216,256,388,396,33,61,153,3],[516,2097156,32901,8455172,4195350,518,16517,67108933,329,1048585,19,11,75,2309,5,5,5,2055,33562625,8195,35,33,4114,34,17055745,524306,4099,131075]),
([pw180,pw3,pw16,pw2,pw5,pw6,pw40,pw147],[404,280,284,152,408,41,264,144,268,11,12,20,24,148,412,416,420,33,49,65,109,113,153,3],[4,515,1042,4099,131842,8490,16390,2113,2097232,4194369,1310784,104,6,32785,65537,129,41,7,8388625,144,56,6,129,41,7,524328,6,6]),
([pw7,pw3,pw2,pw5,pw44,pw6,pw40,pw147],[212,424,444,1,5,41,364,33,3,76,428,448,89,93,101,105,40,44,104,112,176,180,432,436,440,452,17,21,53,81],[1026,4194306,159383554,259,515,1539,786434,262,16396,13,13,37,16396,32786,19,19,35,32786,70254593,4225,8225,805308480,65,33554433,133441,65665,4225,8225]),
([pw148,pw7,pw3,pw2,pw5,pw6,pw40,pw147],[212,452,456,364,53,76,1,5,33,65,64,21,105,3,8,12,20,40,44,104,116,176,180,428,432,444,460,464,468,472,81,89,101,121,209,213],[1059,81925,32771,6293505,67108865,33554433,262169,8388614,16777218,402655234,35,1059,1572874,8198,4294967364,69,17179869189,92,4226,131,34359738371,4234,2147483905,8589935105,1610612760,131841,281,8721]),
([pw7,pw3,pw2,pw5,pw6,pw40,pw147,pw181],[364,476,44,488,41,76,65,64,212,1,5,101,105,12,20,104,176,180,216,252,384,388,480,484,21,73,89,161,3,23],[1048578,2097154,29360130,162,162,32774,536870947,268435466,2562,2562,19,7,16387,5128,5128,25,5,8201,201851136,81,5,33751041,81,5,4,262149,81,261]),
([pw151,pw7,pw3,pw2,pw5,pw6,pw40,pw147],[212,492,44,216,504,41,65,128,1,5,21,8,12,20,40,176,180,384,388,476,496,500,89,101,105,161,3],[131,10241,4099,99329,5,16457,524293,131074,262146,3146754,131,35,14,67108882,8388880,273,81,12,16777730,515,35,14,37748737,97,12,97,13,13]),
([pw152,pw7,pw3,pw2,pw5,pw6,pw40,pw147],[364,508,212,44,61,524,93,3,76,512,1,5,33,73,105,12,16,20,64,176,180,252,384,388,516,520,49,69,101,165],[515,131075,98305,1581057,149,9,5,4194306,8388610,50339842,262406,259,515,162,268436482,1046,67108867,11,18464,18484,134217761,9,2101268,536870977,9,4289,29,73]),
([pw26,pw3,pw2,pw5,pw6,pw40,pw147],[76,128,20,12,272,41,1,16,68,5,53,117,8,24,28,64,104,9,13,25,57,65,73,81,177,217,221,3],[385,4225,24577,5,32803,65795,92,131140,524293,69,16777222,262680,1048601,561,1034,138414081,2097185,8389634,35,33556483,67108867]),
([pw3,pw2,pw184,pw5,pw6,pw40,pw147],[76,20,12,528,49,61,48,140,532,544,9,13,25,57,69,24,28,64,104,536,540,33,53,81,189],[30,275,1042,4099,4115,1042,524301,18444,8205,8205,18444,98305,131233,2,262401,2097185,65,13632000,161,16777761,65]),
([pw126,pw3,pw2,pw5,pw27,pw6,pw40,pw147],[548,556,564,65,580,53,552,584,13,21,11,12,16,20,28,560,568,572,576,588,592,596,600,93,105,109,129,133,137],[65,6145,16451,1091,32769,65549,393249,276,518,8198,134217733,13,33554596,1042,524306,273,25,16777488,1048578,515,11,67109378,1027,11,2097314,4194313,268435617,8388617]),
([pw3,pw2,pw22,pw5,pw6,pw28,pw40,pw147],[160,604,608,164,244,248,17,620,144,256,3,64,76,616,81,93,8,16,52,168,228,240,612,624,628,21,33,41,53,65,85,197,217],[1074,32,75,262,65539,258,258,1048594,121,564,131121,560,560,75,6150,1027,6150,6307842,2147483725,5,33562697,268435657,8,763887620,4294983812,33797,1074004097,41092]),
([pw9,pw3,pw2,pw5,pw27,pw6,pw40,pw147],[632,548,552,564,640,41,57,73,12,64,76,9,13,21,53,85,137,11,16,20,24,28,92,272,288,568,572,576,636,644,648,652,656,49,65,93,105,125,129,149,193,3],[2,262409,3145741,131341,268435465,33685547,201359369,1099511627800,137438953484,524300,549755815947,43,8589936648,2199023255572,16777236,4179,4179,68719476816,8388612,8327,8327,274877907076,1543,1543,541081604,20401160226,4295081987,34359738403]),
([pw142,pw3,pw2,pw22,pw5,pw6,pw40,pw147],[160,660,608,664,65,53,144,620,20,256,8,12,16,28,48,52,96,168,228,232,244,544,668,672,676,81,109,113,117,121,157,3,23],[1283,6153,4294967555,1048577,4194305,16405,2129953,2147483658,524290,67108867,70,70,66,262154,134217737,524,28,520,8195,268435462,536870918,42008578,1073741829,21,16777377,131092,164,180]),
([pw64,pw3,pw2,pw5,pw27,pw6,pw40,pw147],[144,680,572,632,568,61,548,85,76,564,53,11,688,9,13,21,37,141,16,20,24,28,100,576,600,684,692,696,125,193],[4,262147,3145729,2307,16779297,33554433,8388741,536871427,268440065,524803,105,8213,8325,6147,67108866,106,16414,17414,134217731,105,32797,32901,354,278,4195334,196632,1260,196636]),
([pw143,pw3,pw2,pw22,pw5,pw6,pw40,pw147],[160,700,48,704,608,77,544,61,144,616,85,20,76,256,720,41,3,8,12,16,52,64,104,108,620,708,712,716,53,121,205,23],[133123,786441,2147485699,5,65681,33554437,1049665,65546,67108866,35,274,262,258,134217738,41,664,8204,8200,35,2101778,4102,12582978,177,37,17473,536903684,1073743568,285261828]),
([pw3,pw2,pw22,pw5,pw6,pw40,pw147,pw183],[620,724,544,728,77,144,256,52,388,121,3,8,16,128,172,384,392,608,732,41,61,65,117,153,23],[1034,266,25,40,40,41,2057,32770,19,66,66,67,4099,19,4268034,518,263,1031,8388625,21,145,129,524804,5,17956865,16389,2097157,262145]),
([pw180,pw3,pw2,pw5,pw27,pw6,pw40,pw147],[620,572,736,576,144,564,13,21,65,20,24,28,128,416,420,740,744,748,752,756,41,57,61,73,3,11],[8,7,3075,33554439,3,19,32777,37,196641,549,17,19,11,16777221,16388,2097220,70,14,8197,8388737,131,11,4460548,262,14,1048834,10,524298]),
([pw3,pw2,pw22,pw5,pw44,pw6,pw40,pw147],[608,760,764,109,9,13,544,33,3,76,772,17,41,89,93,113,8,16,48,52,104,112,160,164,436,440,712,716,768,776,53,81],[262,67108870,28,65549,28,28,28,134217730,32802,131075,35,35,32802,50333698,259,515,515,271581186,12584961,8321,20481,3221226560,65,536870913,525633,262273,8321,20481]),
([pw148,pw3,pw2,pw22,pw5,pw6,pw40,pw147],[608,776,544,784,53,9,13,76,620,33,65,109,3,8,16,20,48,52,104,116,164,464,468,712,716,760,780,788,17,21,81,89,113,121],[41217,16387,131,537919745,67108865,33554433,131349,4106,8388618,2088,41,41,2092,16777218,4294967362,67,67,86,274726914,131,131,786438,2147484161,8589935617,1207959572,67073,533,5137]),
([pw3,pw2,pw22,pw5,pw6,pw40,pw147,pw181],[544,792,616,800,796,65,109,608,9,13,52,76,388,17,73,89,113,3,8,16,64,164,168,172,384,480,484,620,21,41,125,225],[131090,4114,1073741912,340,340,344,262161,16777218,2281766914,66054,519,515,524291,100671490,1050630,2055,4099,131075,57484,268435501,1033,2113545,4227109,1161,8,8388653,536870949,129]),
([pw151,pw3,pw2,pw22,pw5,pw6,pw40,pw147],[608,804,52,172,808,65,128,800,21,9,89,8,12,16,48,160,164,384,388,496,500,544,620,792,13,17,109,113,121,125,225,3],[2051,12305,67,98561,5,16425,8388613,2147483666,262146,603979906,515,515,14,131090,1212153872,16777233,49,28,35127298,67,268435459,78,1409,417,12,2098209,13,13]),
([pw152,pw3,pw2,pw22,pw5,pw6,pw40,pw147],[544,812,608,816,52,616,61,800,93,3,76,512,17,73,109,8,12,16,64,160,164,384,388,516,520,620,9,13,21,33,113,125,149,225],[32771,196617,2051,1581057,581,17,5,522,4194306,2147500162,4294983718,67108867,19,2097162,9697230856,108,134217737,25,25169922,263206,1027,2051,12516,268435841,17,536871681,85,273]),
([pw3,pw2,pw5,pw6,pw185,pw40,pw147],[128,820,8,53,24,9,76,132,1,61,17,21,41,57,4,12,16,104,25,65,169,189,221],[292,292,262182,38,292,13,3088,8835,98305,532672,1048713,531,19,3090,25,4,4163,2097675,4161,147465,4194315]),
([pw3,pw186,pw2,pw5,pw6,pw40,pw147],[76,20,29,824,28,360,1,828,24,140,532,9,21,77,8,12,16,64,104,144,832,13,53,61,157,169,177,189],[1281,2146,2146,39,67,67108970,98305,16641,131589,3,263177,12304,8388613,129,41418760,16777237,145,12312,517,134217741,129]),
([pw8,pw3,pw33,pw2,pw5,pw6,pw40,pw147],[820,836,65,856,61,860,864,876,37,45,53,113,12,16,20,28,56,60,256,840,844,848,852,868,872,880,9,77,89,93,125,229,19],[524290,4294967299,12290,1048578,19,7,6292482,16393,67108968,1073741834,25,13,262152,8388673,32771,33,65797,16908801,2114,2147483697,293,2752,19,7,134218882,33554453,268435473,536870917]),
([pw8,pw3,pw2,pw5,pw6,pw24,pw40,pw147],[860,884,132,820,900,800,5,888,904,64,76,53,165,16,20,28,60,868,880,892,896,908,912,13,33,41,65,125,193,201,229,233,3,15],[130,8323,524290,1538,8589934723,1538,1048582,268435477,134217750,20,16405,20,20,67,1073741897,9,8388929,2145,6,32771,6,6,131073,123994120,2147485992,4294971401,536936481,4392]),
([pw9,pw11,pw3,pw2,pw5,pw6,pw40,pw147],[292,552,916,272,924,41,1,13,29,85,64,76,144,640,65,137,19,12,16,20,28,92,288,416,556,636,644,696,920,928,49,77,93,149,225],[65539,16777217,393217,1048579,33554433,134283301,276824577,524291,4194306,8194,3078,3078,69206530,8329,67,8589934661,53,1073741889,17179869194,4236,172,4104,278,16406,2684355074,49444,33044,4294967348]),
([pw8,pw54,pw3,pw2,pw5,pw6,pw40,pw147],[820,932,132,860,940,53,65,800,8,12,16,20,28,56,60,856,872,880,892,900,936,944,17,125,181,237,7],[67108867,1048578,1546,262146,7,7,6,2309,524297,4099,32769,8265,81953,33554460,8388630,21,21,20,4194314,16777225,73,2097320,7,7,6,131137,161,225]),
([pw8,pw3,pw56,pw2,pw5,pw6,pw40,pw147],[864,948,800,872,904,968,13,29,85,56,256,65,64,76,820,165,12,20,28,104,880,952,956,960,964,972,976,69,125,205,3,19],[2097154,2147483651,65539,4194306,8400898,12290,17301506,131075,67,268435494,1042,1026,1026,33554433,262181,1074790529,5,269,134217825,16577,585,329,16560,2104,67109164,35344,536871324,35356]),
([pw8,pw55,pw3,pw2,pw5,pw6,pw40,pw147],[860,980,800,904,201,820,61,56,132,64,76,16,20,24,28,104,880,888,892,948,984,988,992,13,17,37,41,53,125,193,205,3,7],[4294967299,131074,2051,262146,1050114,1538,2129922,4099,4194305,24581,2147549249,524289,21,536870915,268435462,106,418,22,16777221,105,8388777,21,108,268,276,100663432,1073741852,134217756]),
([pw8,pw3,pw2,pw5,pw6,pw40,pw147,pw187],[860,996,132,800,113,872,1008,12,60,65,69,16,20,28,880,1000,1004,1012,1016,41,61,125,15,19],[32770,2179,65538,6,6,6,4194435,19,2097166,6,6,6,4099,85,1041,1041,281,257,12,12,76,8261,524832,40,9453569,131112,545,262153]),
([pw180,pw11,pw3,pw2,pw5,pw6,pw40,pw147],[620,292,800,132,920,37,408,24,104,284,416,12,16,20,28,128,144,576,744,1020,1024,17,29,41,49,153,225,19],[134217870,6,6154,16526,3,3,10,8195,521,131081,4751365,309,773,7,17039366,3,3,1043,67108937,65600,112,29,35651597,61,1049,8388656,21,1048597]),
([pw8,pw3,pw2,pw5,pw44,pw6,pw40,pw147],[436,880,444,872,17,9,820,904,33,101,76,104,1036,41,89,129,165,3,20,56,60,112,424,464,760,860,864,1028,1032,5,45,53,77,113,125],[134217729,8610906113,268435457,131075,1027,3073,2099201,548,17179869189,262150,38,548,548,32785,637534210,16642,73928,3221229576,19,19,4294967441,32785,10,8388674,1183754,524554,16642,73928]),
([pw148,pw8,pw3,pw2,pw5,pw6,pw40,pw147],[820,464,456,53,872,9,65,76,17,33,64,8,20,28,56,60,116,452,460,776,844,860,864,880,936,1040,13,37,45,89,101,113,125,129,3],[1155,6149,73400321,8195,262145,8388609,32793,16777222,2148139010,1048578,131,1155,65562,1073741860,4294967302,37,37,60,8589934850,536871425,134217793,301989912,259,67,282,16961,537,17179869257]),
([pw8,pw3,pw2,pw5,pw6,pw40,pw147,pw181],[872,476,800,60,484,65,113,76,480,880,904,101,9,13,17,89,129,20,28,32,64,104,488,792,864,1000,1004,1012,41,57,125,15],[33554434,12582978,67108866,524418,1048706,2097162,2147483779,2118,1073743894,7170,4099,11,131075,82244,42564,8229,9,553648133,82964,309,9,262421,33313,9,8,134217737,268435489,521]),
([pw151,pw8,pw3,pw2,pw5,pw6,pw40,pw147],[496,880,872,60,65,504,13,800,128,17,8,20,28,56,480,492,808,820,860,864,1000,1004,1012,9,89,101,113,125,129],[259,3074,786498,4099,10,8214,16394,1048577,67207169,2097153,259,21,13,33554656,134217761,8388642,52,12,268435969,16777410,212,12,515,21,13,22,14,4325388]),
([pw152,pw8,pw3,pw2,pw5,pw6,pw40,pw147],[872,516,508,820,60,61,800,904,165,76,512,33,57,3,20,28,524,816,860,864,1000,1004,9,13,17,77,101,113,125,129],[1027,16389,790529,32771,8233,17,9,1048582,134414338,2097154,554,515,1027,67113028,268435462,172,4194309,21,553648130,2280,8388929,17,170,33554435,19,10497,57,273]),
([pw126,pw3,pw2,pw5,pw6,pw40,pw147,pw187],[1044,580,68,996,65,144,596,21,12,92,104,17,117,16,20,1008,1016,1048,1052,1056,1060,133,241,11],[513,8451,163969,262145,1049,1537,8388867,4194314,168,2097161,25,76,16394,2082,4099,19,70,6,161,49,228,2082,524305,69,4099,1048597,19,65542]),
([pw180,pw3,pw33,pw2,pw5,pw6,pw40,pw147],[1020,848,856,852,61,408,41,736,21,37,57,12,16,20,64,144,404,744,752,836,840,1064,1068,1072,49,101,113,229,19],[8,268435461,6148,1573124,21,16454,2097164,8197,1188,50331652,21,70,14,4194337,196865,129,515,11,67109920,134217873,98,10,33041,578,10,531,11,8650762]),
([pw3,pw2,pw5,pw6,pw23,pw40,pw147,pw187],[1076,1084,1080,1044,132,996,1,17,65,84,1088,61,141,16,1056,1092,9,21,33,125,129,133,157,3],[101,524404,2097260,12,65574,102,101,145,3081,8197,259,515,513,4194456,1048596,131098,146,145,32,278794,3082,3081,4102,518,8388613,4354,259,32771]),
([pw180,pw3,pw2,pw5,pw6,pw24,pw40,pw147],[736,900,896,1096,748,144,13,128,752,165,16,20,740,884,1068,1100,5,21,33,73,153,229,11],[8,1027,8210,18,4194307,18,4106,67,18,18,2051,18,14,65633,2097473,257,69,13,557472,1048609,131108,12,16513,262276,12,517,13,524]),
([pw3,pw2,pw5,pw6,pw188,pw40,pw147],[76,64,20,1,1084,9,1104,53,4,8,12,16,24,28,80,104,140,5,13,17,21,45,81,177,11,19,23],[44,44,14,44,44,8388636,119406592,3,3073,3,2097360,3,12289,3,4194512,515,81922,19,4,33105,3]),
([pw3,pw2,pw5,pw6,pw189,pw40,pw147],[76,64,28,21,1112,17,1108,45,53,4,8,12,16,20,24,104,140,1116,1,5,9,13,185,3,7,11],[62652416,44,3,9217,3,464,44,3,6145,3,464,15,44,44,4194332,16387,196609,3,4,33361,3]),
([pw9,pw3,pw2,pw5,pw6,pw40,pw147,pw187],[640,996,644,144,1044,1,41,65,73,1088,17,117,12,68,92,104,16,84,272,300,1008,1048,149,11],[8194,69635,3145986,131074,32838,40962,8392707,35,266,4194354,70,38,35,1033,2577,133,16389,16385,1288,140,268,1033,196,2580,2577,524356,133,262149]),
([pw180,pw21,pw3,pw2,pw5,pw6,pw40,pw147],[1120,408,1068,1128,41,13,64,76,752,21,49,65,73,101,12,20,144,404,412,744,852,868,1096,1100,1124,1132,5,61,181,19],[536870915,5,16387,18874881,193,193,262145,32778,1048578,659458,4194306,19,7,42,9224,9224,25,5,67108898,268435746,19,7,142676736,2065,5,2065,5,33554437]),
([pw142,pw3,pw2,pw5,pw6,pw40,pw147,pw179],[1064,660,96,1140,256,5,65,49,672,20,104,240,8,28,324,412,740,744,1136,1144,13,37,117,157,23],[4611,98337,2049,262145,1097,3073,16777731,50,138,131,131,134,6,56,49,1048657,276,50,8388617,73,268,8202,524353,261,4194307,16453,2097155,131078]),
([pw180,pw142,pw3,pw2,pw5,pw6,pw40,pw147],[672,744,620,96,320,65,144,752,5,324,73,8,20,28,240,408,664,736,1020,1136,1140,157,3],[4194307,9,65541,8195,5,517,1048577,6150,164098,16386,524290,35,11,20,1046,20,21,9,322,448,97,9,2098306,35,11,262305,9,521]),
([pw3,pw2,pw5,pw6,pw190,pw40,pw147],[76,64,8,1148,9,1084,53,1152,1,4,12,16,20,24,28,80,104,128,5,13,17,21,45,81,245,11,19,23],[276,276,30,28,276,116,238813184,11,3073,3,4194528,11,24577,3,8388832,4,16941066,107,4099,66209,3]),
([pw3,pw2,pw5,pw6,pw191,pw40,pw147],[128,64,24,1156,17,76,21,53,41,45,4,8,12,16,20,104,1,5,9,13,3,7,11],[8323072,84,11,18433,34,641,84,11,12289,34,641,30,28,84,149,4,267,43,259,33825,35]),
([pw192,pw3,pw2,pw5,pw6,pw40,pw147],[76,92,104,1144,41,20,1160,1,29,128,9,117,8,12,16,24,28,36,64,84,5,13,17,21,3,7],[10,24577,98305,524289,262673,4099,1248,1248,361,209,38,66060288,2313,21,6,2313,21,6,537,7,131075]),
([pw3,pw2,pw5,pw6,pw193,pw40,pw147],[104,8,1020,84,128,9,33,620,748,1,76,5,17,61,93,12,16,24,28,21,11],[546,546,102,38,546,11,1579392,10580,98576,1025,9,12500,393360,1025,9,2,85,77,16401,13,16393]),
([pw3,pw2,pw5,pw6,pw40,pw194],[104,32,33,141,137,1,5,9,13,17,21,41,3,7,11,8,12,16,20,24,28,89,93,165,15,19,23],[29152,16791200,22,2057,294913,100681536,2097158,8388617,196609,22,4194313,1572865,7,22,2057]),
([pw152,pw148,pw3,pw2,pw5,pw6,pw147],[104,64,116,128,25,57,73,1,5,17,3,7,11,32,452,456,464,468,776,784,15,19,23],[5,557073,278561,196673,8201,7,10,10,10,1,5,7600,1052368,10,5,6296416,10,5,10,5,5]),
([pw3,pw2,pw5,pw6,pw195,pw40,pw147],[128,64,1164,76,104,1,5,9,13,17,21,93,3,7,11,8,12,16,20,24,28,15,19,23],[29152,2111136,7,294913,10,17,12601152,7,196609,10,17,7,1572865,10,17,19,2055,15,2051,6,11])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD8 : List StD := [
([pw7,pw22,pw42,pw5,pw6,pw40,pw147],[1168,132,192,668,121,13,81,1188,164,176,180,188,220,664,1172,1176,1180,1184,1192,89,93,153,177,193,197,249,3],[8388620,37,292,37,37,16390,67108873,1546,33554441,25,4231176,65539,8193,19,133185,16777219,19,2097346,262161,524481,1048593]),
([pw7,pw22,pw5,pw6,pw28,pw40,pw147],[1196,1208,244,248,620,1212,21,65,160,212,252,608,628,53,93,113,3,164,176,188,616,1180,1192,1200,1204,1216,33,41,85,177,193,197,217],[1073741836,131337,6152,33033,1050632,36872,262149,1540,65541,1540,562036740,2147483747,3,227,8273,2097153,239075458,4294975538,81923,268959761,16562]),
([pw9,pw3,pw16,pw27,pw6,pw40,pw147],[1224,1220,1228,288,640,41,113,73,316,9,85,137,12,28,144,276,312,632,1232,1236,1240,1244,1248,1252,1256,29,49,65,93,149,225,11],[2,8333,4181,32773,2147745831,1573893,140,84,536871431,39,67109380,1073741848,131211,171,2113544,339,339,65616,146802722,50334723,268435491]),
([pw142,pw7,pw22,pw5,pw6,pw40,pw147],[1168,144,320,620,664,1,53,65,33,12,164,180,184,188,244,668,1184,1192,13,121,157,169,177,193,3],[16777221,561,16385,32769,4227,73793,8388628,1038,261,262149,2097164,2098,49,524305,4194360,1048579,131,74,131457,73,201]),
([pw7,pw22,pw43,pw5,pw6,pw40,pw147],[1260,352,708,184,57,101,1184,117,201,252,616,1208,1212,21,65,93,188,544,704,1192,1264,193,205,3],[2097158,19,19,1042,1042,131090,37,37,548,548,1048612,9,8913025,262153,65857,6273,8201,8513,49160,4200896,49160]),
([pw143,pw7,pw22,pw5,pw6,pw40,pw147],[1268,1196,360,704,1208,1,113,1184,184,61,85,616,21,41,8,12,188,212,252,364,620,708,720,1272,53,121,193,205,3],[16455,32811,8388610,268435987,2097155,66691,67108876,70,2117,2117,4194372,42,131129,262185,524456,531,4371,5250,33562881,134219409,17834257]),
([pw7,pw22,pw5,pw6,pw40,pw147,pw183],[620,1280,400,724,188,544,1276,77,121,23,44,164,176,180,628,1208,1284,1288,1292,1296,1,13,33,41,61,65,117,153,193],[268435468,2053,4210756,2097254,37,517,12297,67305480,266,1035,1048587,134217857,131,19,17,8388866,3,16810497,262147,33554435,524289]),
([pw180,pw3,pw16,pw27,pw6,pw40,pw147],[1300,620,1240,404,144,1304,1312,65,12,264,308,564,652,736,740,1308,1316,41,61,225,11],[4,11,1048835,3,35,16389,2058,41474,66,67,5,524298,4120,25,13,328706,131,5,131201,5,37]),
([pw7,pw22,pw5,pw44,pw6,pw40,pw147],[1168,444,760,1,1184,33,616,1340,17,41,89,93,184,188,252,364,544,772,776,1296,1320,1324,1328,1332,1336,21,53,81,193,3,23],[268435462,36700162,1073741827,67,67,196610,12583180,13,13,16389,32780,17301761,1057,2561,201326736,17,262145,536879249,4129,1057,2561]),
([pw148,pw7,pw22,pw5,pw6,pw40,pw147],[1168,456,776,1184,53,252,616,33,65,1,21,8,184,188,364,544,760,780,788,1296,1336,1344,1348,1352,1356,1360,17,81,89,121,193,3],[2115,37,1573889,131073,65537,8217,1073741830,6292482,67,67,294922,92275204,37,37,16908,268435585,536871169,167772184,4481,153,2147483921]),
([pw7,pw22,pw5,pw6,pw40,pw147,pw181],[1280,1372,476,792,616,620,21,65,608,1208,1,73,89,212,252,544,1192,1212,1292,1296,1364,1368,1376,1380,17,41,57,193,3],[134217740,3145796,276,276,32774,67108885,29361160,9224,16393,11,268435465,137824,225,3,526369,69761,3,2,262147,33554561,515]),
([pw151,pw7,pw22,pw5,pw6,pw40,pw147],[1168,620,1292,504,808,21,65,628,1288,188,89,184,792,1184,1296,1384,1388,1392,1,13,17,121,193],[137,275,16419,3,2117,4101,4194328,32810,137,524297,140,1507346,275,2097169,278,1059,99,550,9281,517,71]),
([pw152,pw7,pw22,pw5,pw6,pw40,pw147],[1280,508,816,1208,188,61,73,93,616,620,1396,1400,1,17,3,12,212,252,608,1212,1296,1336,1404,1408,1412,1416,21,33,193],[1027,34821,3145793,16425,17,9,268435462,12582978,262410,259,1027,50343940,69644,131077,2053,533096,67109505,17,134234241,57,145]),
([pw3,pw2,pw106,pw5,pw6,pw40,pw147],[800,264,592,268,588,53,1420,144,33,4,76,104,1424,9,21,65],[71,7,19,266,8202,35,7,16455,5,5,133,66,5,1033,2593,17,17,145,37128,41,41]),
([pw196,pw3,pw2,pw5,pw6,pw40,pw147],[144,276,316,1428,800,1444,1308,24,1436,1440,64,76,104,308,1432,1448,33,53,61,129,189,205,221],[10,17285,135,7,3085,4609,49,19,75,77,81,524579,41,37,33,7,11,3,368648,3145756,4325404]),
([pw7,pw3,pw2,pw5,pw6,pw197,pw40,pw147],[252,144,1456,800,212,132,1452,1204,21,64,180,1468,1472,24,44,256,260,364,440,612,1460,1464,1476,53,3],[68,1048580,270348,581,101,581,2621452,16783366,5378,19,35,2065,32906,1286,7,37,7,6,19,43,27,8388994,49,4259841,25,8,147593,25]),
([pw198,pw3,pw2,pw5,pw6,pw40,pw147],[176,132,208,252,144,1480,748,1484,1488,104,1492,33,57,4,76,53,65,205],[21,33,5,20,16906,8706,4149,69,30,22,22,4129,42,34,34,2185,385,321,68872,131528,33992]),
([pw7,pw3,pw2,pw5,pw6,pw189,pw40,pw147],[252,1496,132,176,212,1500,1452,21,64,1504,44,364,436,1460,1476,1508,1512,1516,185,3],[66,8194,4106,323,71,323,6,524326,172,37,37,37,36,138,7,7,7,6,25,25,25,262792,98321,147457,17,8,3585,17]),
([pw199,pw3,pw2,pw5,pw6,pw40,pw147],[132,212,320,180,328,748,4,76,104,124,224,432,53,65,205,3],[6,2051,1029,6,131,321,32791,45,7,7,5,57,19,19,17,11,11,9,8706,16418,4130]),
([pw3,pw2,pw200,pw5,pw6,pw40,pw147],[800,264,528,1524,1520,316,144,1532,4,64,76,104,1528,9,33,53,73,205],[7,6,19,42,12298,11,6,65543,5,5,69,19,1569,5,2313,17,17,81,16552,131233,32777]),
([pw7,pw3,pw2,pw5,pw6,pw201,pw40,pw147],[252,1536,212,176,1548,748,1204,1452,21,64,132,1288,93,260,364,612,1460,1540,1544,185,3],[130,65538,131082,643,163,515,294914,1048594,266,7,35,7,1090,280,21,49,21,1104,13,13,15,524616,8,14337,5,6149,16481,5]),
([pw202,pw3,pw2,pw5,pw6,pw40,pw147],[132,360,748,376,180,252,113,1552,1560,1576,64,76,104,1556,1564,1568,1572,1580,41,53,253],[8323,114945,259,3073,3,4225,67,7,3,3,3,77,73,9,13,49,17,21,1311264,131108,524804]),
([pw7,pw3,pw2,pw5,pw6,pw191,pw40,pw147],[252,1588,212,180,1508,748,1504,76,21,1288,1584,41,24,64,144,256,364,1112,1516,1592,1596,1600,53,3],[1026,524290,1052682,8323,163,1154,2228226,8388626,280,21,49,21,32848,266,7,35,7,16450,13,13,13,4194632,8,264705,5,2565,65633,5]),
([pw203,pw3,pw2,pw5,pw6,pw40,pw147],[144,1604,412,1608,1632,152,64,76,256,800,1616,52,104,280,384,1004,1612,1620,1624,1628,41,65,3],[65547,150529,820225,193,193,4099,525,537,265,265,7,4194327,5,5,7,17,17,19,3145760,34,8226]),
([pw192,pw3,pw16,pw2,pw5,pw6,pw40,pw147],[316,256,1648,1636,1644,152,1652,144,41,308,1308,9,29,20,28,268,280,928,1064,1160,1640,1656,3],[1048600,133,133,16515,3,33537,137,532486,3078,3138,4122,35,46,131076,2097154,262165,261,44,4194374,4117,261,44,82,67,74,769,41,65560]),
([pw204,pw3,pw2,pw5,pw6,pw40,pw147],[800,176,1660,364,1664,748,64,76,216,380,1668,41,65],[6,18,6,193,193,517,23,7,36,36,13,50,17,17,1049,3,3,43,6152,9,265]),
([pw7,pw3,pw2,pw5,pw6,pw205,pw40,pw147],[800,1676,176,252,132,364,748,1688,1692,76,1672,1684,93,104,620,1200,1680,33],[1026,65538,7,2562,67,2562,9219,3,5,408,321,400,273,16390,3,67,3,19,5,141,5,32805,4,131112,41,4105,105,4233]),
([pw3,pw2,pw5,pw6,pw206,pw40,pw147],[212,748,444,132,424,33,4,24,28,104,1696,21,53,185,205,23],[32789,6,7,5,7,14,18,19,17,19,26,41,394,2057,8202,5,1061,16387,7,586,4099]),
([pw7,pw3,pw2,pw5,pw6,pw40,pw194],[1700,212,364,1712,132,41,33,76,428,1,5,93,104,180,432,1704,1708,21,89,101,105,3],[257,16385,229377,131,387,4117,2097161,524801,515,35,21,1049608,1034,42,28,262210,2082,8212,71,70,2086]),
([pw152,pw148,pw7,pw3,pw2,pw5,pw6,pw147],[212,364,1720,1288,1716,73,1724,1744,456,512,776,784,1356,1728,1732,1736,1740,1748,1752,1756,1760,3],[17,518,2370,1030,4194,11,17,13,9,13,9,3,19,8196,16388,98340,13,18,2097284,393376,9,18,1572900,13,18,9,18,19]),
([pw207,pw3,pw2,pw5,pw6,pw40,pw147],[800,152,488,144,484,1764,64,132,33,8,20,76,240,280,308,316,1096,1768,1772,1776,1780,1784,1788,9,73],[1665,458785,1576993,161,2115,97,5,17,2130184,8388618,3,16777223,5,7,15,17,19,27,4210946,3,8195]),
([pw7,pw3,pw2,pw5,pw6,pw195,pw40,pw147],[252,212,1796,1812,21,132,364,1816,76,1792,104,180,1288,1748,1756,1800,1804,1808,1820,1824,93,3],[516,32772,196628,262,293,262,1548,2097284,270356,7,37,7,76,540816,3,161,3,200,3,2081,19,88,65,1052682,3,11,2,3]),
([pw26,pw3,pw2,pw42,pw5,pw40,pw147],[76,608,144,128,1828,132,668,81,249,20,24,28,272,1128,1832,1836,1840,9,13,53,257],[3,3,7,3077,27,25,16756,8722,131380,3,1048604,4166,295012,3,524332,1,65539,138,3,172,3]),
([pw208,pw3,pw2,pw5,pw6,pw40,pw147],[132,164,608,1844,9,13,668,1848,1860,65,24,64,76,104,168,336,800,1852,1856,61,73,77,89,93,109,113,197,261,3],[10,32771,131203,263169,6145,8321,268435787,275,21,21,16777233,99,45,45,33554473,67108870,134217734,3145730,16900,4784132,8389124]),
([pw3,pw2,pw209,pw5,pw6,pw40,pw147],[800,604,1872,144,1864,17,256,616,53,160,1868,64,76,104,228,244,628,1876,1880,1884,21,33,117,197,217,221,3],[67108883,1027,35,14,10,11,147985,33329,85,81,89,35,262147,6149,9225,8388645,1048737,297,6881284,16777605,33554821]),
([pw3,pw2,pw22,pw5,pw6,pw197,pw40,pw147],[616,1468,608,160,1888,17,1456,1892,144,1896,16,52,228,256,544,612,624,1464,1492,1900,1904,1908,53,3],[8388690,64,42,7,259,7,258,4114,120,69,1041,21,8400,42,7,262147,7,163970,13,41,41,4194856,1572869,2162689,5,8,19073,5]),
([pw3,pw2,pw210,pw5,pw6,pw40,pw147],[1492,616,1880,164,1180,1912,101,9,13,76,104,1488,65,4,800,21,61,89,93,113,157],[116,70,76,198,198,196,56,57,305,307,524592,12,519,1539,9217,1081355,2059,9,6147,212993,266243]),
([pw3,pw2,pw22,pw5,pw6,pw189,pw40,pw147],[616,608,1916,164,1920,1924,1928,1496,144,1580,16,52,436,544,1108,1452,1908,1932,9,13,21,45,53,125,185,225,3],[67109012,128,8388620,7,261,7,2359396,32788,33554456,131,1041,19,4718832,4108,7,517,7,16996,11,11,11,17825896,259,196609,3,8,10337,3]),
([pw211,pw3,pw2,pw5,pw6,pw40,pw147],[548,560,1936,748,1948,1944,1,37,5,132,256,1492,4,76,104,1488,1940,53,177,205],[6,65540,6,3,10241,22528,116,70,69,133,262220,306,273,1073,1336,515,131,522,32897,524297,131209]),
([pw212,pw3,pw2,pw5,pw6,pw40,pw147],[164,1956,132,708,1492,616,1952,101,53,76,1960,1964,9,13,33,4,64,104,800,1968,21,93,149,181],[65,9,9,66054,524,163844,205,133,4194470,4262,4228,25,8388698,8314,9544,2081,1572867,17,18450,17682,2359602]),
([pw3,pw2,pw22,pw5,pw6,pw201,pw40,pw147],[132,616,608,628,1548,1976,164,1972,144,1900,3,16,52,544,612,1452,1540,45,53,93,125,185,225],[1681,16,1049153,7,259,7,131113,32769,4194497,22,2067,7,262201,65729,7,1027,7,16425,7,7,7,2097161,1,524298,6,262,12330,6]),
([pw213,pw3,pw2,pw5,pw6,pw40,pw147],[132,684,2004,1984,1980,256,76,748,1936,1988,2016,5,41,12,64,104,632,1992,1996,2000,2008,2012,2020,9,53,65],[18,139785,786435,16449,67,33297,1048845,263,5,10485765,5,2059,1065,45,2105,3,3,3,33558532,4260992,16781460]),
([pw3,pw2,pw22,pw5,pw6,pw191,pw40,pw147],[616,2024,256,608,2028,17,628,144,1460,41,52,544,1112,1452,1492,1600,1928,1932,53,3],[524306,274,52,25,145,25,144,8194,38,6,6,6,6,38,11,16387,267,36866,13,13,37,327716,4,131649,9,585,3137,9]),
([pw3,pw2,pw214,pw5,pw6,pw40,pw147],[256,724,544,2036,1,144,160,2032,64,76,65,153,60,172,728,732,5,17,41],[19,4241,16465,33,33,49,195,65603,3,3,3,131,769,769,32779,133121,1029,2057,263172,12,8204]),
([pw192,pw3,pw2,pw5,pw27,pw6,pw40,pw147],[632,256,2048,2040,572,132,1,12,652,1828,2052,41,756,928,1656,1936,2044,29,3],[65545,135,35,645,3,2321,25,70,33858,70,131075,19,30,263174,16388,7,7,14,8198,35,35,42,517,21,28,2305,25,4105]),
([pw3,pw2,pw215,pw5,pw6,pw40,pw147],[544,132,732,800,2056,164,620,9,13,172,1852,25,41,57,65,3],[32788,17,58,2192,145,25,5,102,8452,261,69,38,10,11,5,10,11,1027,20481,9,521]),
([pw216,pw3,pw2,pw5,pw6,pw40,pw147],[608,764,760,2060,1,1828,5,33,45,9,13,41,93,4,24,28,104,132,256,776,1840,21,53,81,89,3],[3,5,442400,3,524321,73760,22,530,19,515,282,1092,69,1029,4194380,16777345,6145,44040456,1048707,393,6145]),
([pw3,pw2,pw22,pw5,pw6,pw40,pw194],[2064,608,2068,544,9,13,81,109,113,76,33,64,164,1704,1708,2072,2076,17,41,89,93,3],[2097157,32773,148,148,148,148,65537,289,289,289,289,155649,2563,515,73,525314,1310722,4168,1035,74,74]),
([pw152,pw148,pw3,pw2,pw22,pw5,pw6,pw147],[544,2084,608,628,2080,2088,17,784,73,452,456,512,776,1344,1348,1728,1732,1736,1740,2092,2096,2100,2104,3],[17,1155,4641,2179,24833,13,21,14,44,14,12,1,17,8388642,65538,1572930,14,17,32802,6291552,44,17,393282,14,17,268,17,17]),
([pw3,pw2,pw217,pw5,pw6,pw40,pw147],[544,796,792,800,616,9,13,21,41,65,2108,2112,73,109,113,28,172,620,89,125,225,3,23],[2097158,3,532490,8242,35,35,5,1196036,16468,69,69,4231304,10,769,3,267416,649,2049,769,3073,65793]),
([pw3,pw2,pw22,pw5,pw6,pw195,pw40,pw147],[616,608,2116,2120,2124,2128,544,2092,17,256,1800,8,164,628,1792,1804,1808,2100,2132,2136,93,3],[2097164,1036,408,139,2185,11,120,16388,393476,7,517,7,100,98564,7,524293,7,1124,275,4625,131,352,65,1056802,19,162,18,19]),
([pw3,pw218,pw2,pw5,pw6,pw40,pw147],[2144,556,292,592,916,132,65,4,76,104,620,1488,2140,29,93,137,225],[6,4109,7,54,52,36,13,6,3,273,641,65547,9,9,9,3,3,3,2128,42000,16464]),
([pw3,pw219,pw2,pw5,pw6,pw40,pw147],[2156,2148,2152,2160,2164,2168,748,13,53,65,104,4,76,1828,29,33,125,221,229,233],[6,7,65547,3,3,3,6,13,3,5121,3073,13,262324,692,452,9,9,9,57872,524656,131952]),
([pw8,pw3,pw2,pw5,pw6,pw220,pw40,pw147],[904,132,2180,860,2188,820,2172,2176,5,2184,64,2192,60,424,872,908,2196,2200,2204,53,125,193],[192,8204,516,1093,71,1093,6,2097178,1048726,19,531,531,18,396,41,265,265,526600,135,7,7,6,196641,294913,33,8,22529,33]),
([pw221,pw3,pw2,pw5,pw6,pw40,pw147],[132,1128,868,864,2228,104,2208,2224,2232,2236,65,20,76,800,856,2212,2216,2220,61,89,93,125],[32835,16387,198657,3,4129,97,131,2097159,3,3,3,133,25,9,9,5,5,5,1808,794896,1050112]),
([pw8,pw3,pw2,pw5,pw6,pw222,pw40,pw147],[820,904,2240,864,132,2248,2252,13,76,936,2256,60,256,760,844,872,1120,2204,2244,2260,5,17,53,125,169],[516,8204,16388,261,22,773,327684,140,8388644,7,22,7,4164,1048744,11,9,11,16777416,3,50,3,6292576,19,655361,3,8,35906,3]),
([pw223,pw3,pw2,pw5,pw6,pw40,pw147],[428,256,664,132,228,320,2264,800,53,65,2268,4,76,104,2232,73,157,193],[65,13,28,5,4099,10242,131174,1082,43,35,34,1108,15,71,70,65553,537,33176,16897,385,897]),
([pw3,pw224,pw2,pw5,pw6,pw40,pw147],[2144,2272,528,292,688,924,132,1532,2276,33,4,64,76,104,620,37,93,205,225],[6,13,25,104,78,74,12,25,6177,5,9219,262165,5,7,7,17,19,19,928,131714,114978]),
([pw8,pw3,pw2,pw5,pw6,pw225,pw40,pw147],[904,2280,820,864,2196,132,2172,2192,64,912,2292,13,60,256,780,872,896,908,2284,2288,5,53,125,169,265],[66,16394,262146,323,99,323,589826,2072,4194322,21,49,21,8336,1048586,13,41,15,8390792,7,35,7,2098690,8,16908801,5,37,38017,5]),
([pw226,pw3,pw2,pw5,pw6,pw40,pw147],[256,360,1580,704,2312,1552,2268,2300,2316,21,41,64,76,104,228,800,1556,2296,2304,2308,2320,53,65,193],[65571,917633,131,6145,3,8225,8388619,16451,3,3,3,73,9,9,9,21,773,1049093,4195348,32788,2098436]),
([pw8,pw3,pw2,pw5,pw6,pw227,pw40,pw147],[820,904,2328,132,860,2336,76,912,2324,5,41,12,60,872,892,2252,2260,2332,53,125,193],[260,133140,16388,69,78,325,12,1048632,524332,3,42,3,40,532,19,1,19,295440,7,14,7,12,16,66689,3,1155,12418,3]),
([pw3,pw228,pw2,pw5,pw6,pw40,pw147],[132,824,2156,1080,2340,2344,1580,69,1612,2152,2348,41,65,113,125],[19,525,16457,5,7,7,29,259,5,7,19,69,8321,131,35,5,7,7,6146,34,1058]),
([pw192,pw11,pw3,pw2,pw5,pw6,pw40,pw147],[132,924,2356,2052,1648,41,24,920,2352,1,29,16,20,312,656,696,1024,1160,2360,2364,193,225],[67,259,2051,67,3,32806,262406,135177,8193,16385,11,35,13,1572881,521,1027,515,133,2097177,19,19,21,11,35,13,38,1158,65542]),
([pw229,pw3,pw2,pw5,pw6,pw40,pw147],[132,2372,2380,864,1016,2368,872,64,76,748,52,284,388,800,1012,1624,1848,1852,2376,41,65],[37921,262179,198689,385,385,39,8201,533,17,17,19,525,9,9,7,5,5,7,1572928,66,16450]),
([pw3,pw2,pw5,pw6,pw230,pw40,pw147],[132,444,436,820,2224,2392,2384,13,33,53,12,16,104,2388,2396,41,93,125,181],[19,131079,3,8259,3,3,21,262153,3089,137,673,5,13,5,5,3,16650,808,3,4193,98312]),
([pw8,pw3,pw2,pw5,pw6,pw40,pw194],[1704,820,872,1700,132,2400,9,33,76,17,41,165,864,1712,2064,2404,89,101,113,125,129,269],[33,286721,32769,259,291,53,131144,524297,74,74,28,1049089,65666,3074,4116,515,2097155,21,135,134,3078]),
([pw152,pw148,pw8,pw3,pw2,pw5,pw6,pw147],[872,2412,820,912,2408,57,1724,1744,113,456,468,512,784,1748,2096,2416,2420,2424,2428,2432,2436,2440,125],[17,2051,4673,32865,1027,13,21,14,12,12,14,1,17,65538,393474,524290,14,17,24736,4194434,12,17,3145986,44,17,14,17,17]),
([pw3,pw231,pw2,pw5,pw6,pw40,pw147],[824,2156,796,2444,484,144,2452,13,41,57,12,16,76,132,1828,2168,2348,2448,2456,2460,65,125],[131081,14,2097182,14,15,15,11266,9,6,4099,7,18,33504,161,545,18,19,19,1327361,524353,65793]),
([pw8,pw3,pw2,pw5,pw6,pw195,pw40,pw147],[904,1796,820,2472,1804,113,2124,132,1012,64,76,1748,2464,36,864,912,1816,2116,2440,2468,2476,93,125],[4098,196642,524290,1539,1155,515,12298,2146,4194386,7,131,7,266,1310768,37,16545,2145,264,21,209,85,280,257,2129929,13,13,13,13]),
([pw232,pw3,pw2,pw5,pw6,pw40,pw147],[132,1064,2480,2492,5,1860,2488,13,12,16,60,76,752,1004,1632,1828,2484,2496,9,125,149,197,261,273],[6,769,74817,67,2051,4103,49,540705,1048579,262147,15,145,19,131,13,2097159,4194307,13,8552450,14,14]),
([pw233,pw3,pw2,pw5,pw6,pw40,pw147],[800,2504,592,628,2500,1060,748,1016,24,28,76,596,1044,2136,21,33,157],[12,22,769,6,1027,4123,5,193,204,194,184,69,13,7,52,65539,16387,57,43010,58,58]),
([pw3,pw2,pw5,pw6,pw234,pw40,pw147],[748,2516,1088,2508,2512,132,1080,1,2520,1076,17,65,128,1084,2524,9,21,33,61,125,133,157],[729,524465,1048723,721,32917,465,1065,262159,585,2063,16713,2098214,1057,66598,289,529,143362,261,2055,73,259]),
([pw3,pw2,pw5,pw6,pw235,pw40,pw147],[132,800,2520,2528,1,2532,2056,2536,128,620,276,57,12,16,1084,9,13,25,33],[91,91,131129,27,32921,31,1537,2465,12801,67745,519,3,1089,3,263,3,278816,134,3,71,38]),
([pw3,pw2,pw5,pw6,pw236,pw40,pw147],[132,1488,128,2540,5,1880,1632,2552,2544,2548,12,16,2556,13,37,157],[57,107,15,105,17161,141,19,19,3089,8465,149,32775,97,3,3,39,6,4230,3,73,644]),
([pw237,pw3,pw2,pw5,pw6,pw40,pw147],[800,2560,300,2564,272,748,1016,128,1828,24,28,64,76,644,2568,21],[6,88,1569,5,6147,12,81,97,98,98,12,49,19,19,12,387,57347,12,386,14,12]),
([pw3,pw238,pw2,pw5,pw6,pw40,pw147],[748,2576,1044,2572,2580,132,1,1288,5,37,2136,17,24,28,1948,21,65,277],[138,16473,131177,77,523,75,149,12321,10,515,7,2353,277,65555,275,2212,32802,3,1542,3,1031]),
([pw239,pw3,pw2,pw5,pw6,pw40,pw147],[748,752,2584,2136,320,620,672,5,12,16,92,1000,1064,2588,13,21,33,157],[6,769,10241,1027,11,4103,49,17,19,19,13,161,131,16387,13,131106,32802,12,65610,70,14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD7 : List StD := [
([pw208,pw7,pw5,pw6,pw40,pw147],[132,1168,1844,2596,2604,65,193,164,252,364,620,1828,2592,2600,2608,61,73,77,89,93,197,261],[71,12313,19,259,16905,197,7,7,5,1048579,2097155,196609,2082,295938,524322]),
([pw7,pw209,pw5,pw6,pw40,pw147],[620,1864,2632,1212,21,53,616,1872,2616,2620,65,212,252,364,1336,1828,2592,2612,2624,2628,33,117,169,193,197,217,221],[8388611,131075,194,194,4194307,787201,66049,6145,8449,16777245,1053,16433,3179524,33554477,67108909]),
([pw7,pw22,pw5,pw6,pw197,pw40,pw147],[620,1168,1268,1456,616,180,748,1184,1204,1216,1324,1328,1336,1548,1896,2636,2640,2644,2648,21,53,193],[2097161,1033,26,76,26,16393,2081,7,32773,7,65793,7,2,7,1576961,139270,262658,7,1,133,7]),
([pw7,pw22,pw5,pw6,pw189,pw40,pw147],[132,1212,1208,1496,212,2652,2660,2664,164,176,188,1184,1320,1332,1336,2648,2656,2668,21,185,193],[1048577,4361,9,9,9,9,8705,19,35,19,65569,7,7,7,786625,16390,163842,6,1,3266,6]),
([pw199,pw22,pw5,pw6,pw40,pw147],[132,1168,1336,748,121,2672,1,544,608,616,1828,2676,2680,2684,53,177,193,205],[65541,2085,4353,515,161,8197,67,19,32841,5,5,5,1042,131082,16410]),
([pw7,pw22,pw5,pw6,pw201,pw40,pw147],[132,1168,1268,2708,616,2700,2704,93,16,164,176,188,608,1184,1204,1896,1976,2688,2692,2696,185,193,3],[2097153,131585,4115,261,19,98305,263169,7,4194309,7,540673,7,3,7,1048681,1,138,6,142,10340,6]),
([pw7,pw22,pw5,pw6,pw191,pw40,pw147],[620,1268,1588,1208,132,212,608,616,2708,180,1184,1336,1504,1928,2636,2712,2716,2720,41,53,193],[1048581,32773,198,150,70,8197,66049,35,16387,35,135169,11,19,11,526593,1,262402,11,26,1027,11]),
([pw203,pw3,pw27,pw6,pw40,pw147],[132,2724,2728,1236,144,1632,152,548,632,65,404,1304,1308,1608,2732,2736,41,61,225],[34,262213,385,385,1059,12293,17,17,51,180228,524,70,66056,10,2058]),
([pw192,pw3,pw16,pw27,pw6,pw40,pw147],[1224,2740,1652,1236,2052,2748,132,41,2732,2752,1252,24,28,1220,1304,2360,2744,2756,2760,2764,29,225],[65570,4613,2321,131073,9345,32771,262724,524624,1048674,201,78,2097172,549,165,14,305,25,26,1153,11,16418]),
([pw7,pw215,pw5,pw6,pw40,pw147],[132,620,2768,1184,544,44,2600,164,180,1292,2596,41,65],[23,135,5,21,21,1121,3,3,291,3,3,75,6152,10,522]),
([pw3,pw27,pw6,pw240,pw40,pw147],[2776,144,2772,1,53,2780,316,620,33,564,800,2180,2784,2788,2792,9,225],[14,11,650,32779,58,69,65543,69,4148,8195,16645,305,2051,178,1041]),
([pw7,pw22,pw5,pw6,pw40,pw194],[1828,1280,1700,81,132,544,616,1,33,41,93,212,252,2796,2800,2804,2808,17,21,89,193],[1048581,286724,69,100,54,229505,2177,4099,11,524545,1538,26,263,11,1546]),
([pw152,pw148,pw7,pw22,pw5,pw6,pw147],[1184,1212,2812,2084,2816,73,212,608,1208,1724,1828,1396,1400,2708,2820,2824,2828,2832,2836,2840,1,17,193],[5,2065,5641,16929,9219,32773,146,74,258,1,5,4194328,196656,146,5,3932168,74,5,290,5,5]),
([pw7,pw217,pw5,pw6,pw40,pw147],[1184,620,2844,2856,21,65,616,2848,41,73,176,1212,1292,2108,2112,2852,2860,89,193,3,23],[262277,32790,8388,69,16389,1574418,10,289,9,199186,51,9,289,9,4105]),
([pw7,pw22,pw5,pw6,pw195,pw40,pw147],[1268,2872,1208,1796,2120,21,132,608,616,1184,2608,1,212,544,1336,2708,2864,2868,2876,2880,17,93,193],[4194328,196648,393,329,137,8202,1837072,4113,1041,2065,1042,5,16449,37,546,513,2129923,7,7,7,7]),
([pw3,pw2,pw241,pw5,pw6,pw40,pw147],[132,1872,616,628,1900,1972,2612,45,104,2436,53,125,161,185,225,281,3],[65587,5,2129,7,7,137,5,16481,7,7,1033,3,1,6,904,7,7,8201,36874,6,6]),
([pw216,pw3,pw2,pw242,pw5,pw6,pw40,pw147],[2888,2900,2908,2912,2060,2920,2884,616,1828,2928,24,28,104,128,760,1856,2100,2892,2896,2904,2916,2924,2932,2936,2940,3],[131137,262145,33554752,3074,557057,8193,4162,7,1048840,6,9,35,26,2113540,544,5,545,20,16,129,137,4194304,5,25165825,20,10,49,65545]),
([pw216,pw243,pw3,pw2,pw5,pw6,pw40,pw147],[2912,2968,2060,1580,1828,2100,2984,4,616,620,2908,2940,2944,2980,760,2884,2916,2924,2928,2932,2948,2952,2956,2960,2964,2972,2976,2988],[152,3182592,29364224,522,520,33554434,136,65553,147457,67108864,272,261,262144,1026,1026,8193,66,7,526368,3,134217796,5,3,100,5,3,2054,8225]),
([pw244,pw3,pw2,pw5,pw245,pw6,pw40,pw147],[620,3016,3012,748,2848,1752,2996,1820,2440,2992,632,792,3000,3004,3008,3020,3024,3028,11],[512,6208,24577,1,1,1088,576,5,32778,5,5,5,196612,262153,10,56,138,3,3,49,129,14,1,274,7,50,7,257]),
([pw246,pw3,pw2,pw5,pw245,pw6,pw40,pw147],[620,3016,3012,748,572,1756,792,3028,3040,632,1748,2092,2440,2992,3032,3036,3044,3048,3],[128,80,17,1,65,528,144,5,16394,5,5,5,40964,262153,10,296,1034,3,3,69633,2049,14,1,131106,7,290,7,33])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD6 : List StD := [
([pw7,pw241,pw5,pw6,pw40,pw147],[132,1268,2632,3056,2132,3052,364,628,2436,2612,3044,3060,161,185,281],[3,545,35,35,2201,5,3,6,1368,7,7,8201,20490,22,14]),
([pw7,pw247,pw217,pw5,pw6,pw40,pw147],[620,3072,3084,132,3076,3064,3092,748,2100,3080,1212,2436,2852,3068,3088],[8352,10,4113,532,530,19,1,16384,1,1060,160,9,9,322,10,5,7,70,2114,3,257]),
([pw246,pw3,pw16,pw245,pw6,pw40,pw147],[620,3104,3012,1224,3112,800,1236,2440,2848,3036,3096,632,2436,3044,3100,3108],[1024,2088,16384,40,72,1088,7,5,5,7,32774,274,274,528,513,1,4098,3,8322,3,129]),
([pw248,pw3,pw2,pw5,pw6,pw40,pw147],[2940,1748,2436,3124,2936,3128,132,620,1756,2884,104,2104,2476,2900,2912,2952,2964,3116,3120,3132],[33408,196672,192,262145,2049,1536,11,38,7,257,10,37,12,10,257,17,21,524336,16387,12289,3])]
def ptopD5 : List StD := []
theorem ptopI5 : LevelN true ptopT 5 ptopD5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC6x0 : levelOK true ptopT ptopt 5 (ptopD5.map Prod.fst) ((ptopD6.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI6 : LevelN true ptopT 6 ptopD6 := levelStep ptopB ptopW ptopI5 (chunks 32 ptopD6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC7x0 : levelOK true ptopT ptopt 6 (ptopD6.map Prod.fst) ((ptopD7.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI7 : LevelN true ptopT 7 ptopD7 := levelStep ptopB ptopW ptopI6 (chunks 32 ptopD7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x0 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x1 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (1*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x2 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (2*32)).take 32) = true := by decide +kernel
theorem ptopI8 : LevelN true ptopT 8 ptopD8 := levelStep ptopB ptopW ptopI7 (chunks 32 ptopD8 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC8x0
  · exact ptopC8x1
  · exact ptopC8x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x0 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x1 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (1*32)).take 32) = true := by decide +kernel
theorem ptopI9 : LevelN true ptopT 9 ptopD9 := levelStep ptopB ptopW ptopI8 (chunks 32 ptopD9 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC9x0
  · exact ptopC9x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC10x0 : levelOK true ptopT ptopt 9 (ptopD9.map Prod.fst) ((ptopD10.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI10 : LevelN true ptopT 10 ptopD10 := levelStep ptopB ptopW ptopI9 (chunks 32 ptopD10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC10x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC11x0 : levelOK true ptopT ptopt 10 (ptopD10.map Prod.fst) ((ptopD11.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI11 : LevelN true ptopT 11 ptopD11 := levelStep ptopB ptopW ptopI10 (chunks 32 ptopD11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC11x0
  ))
theorem ptopL : LowN true ptopR ptopT 12 := lowSearch ptopB ptopI11 (by decide +kernel)

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
theorem excludes : Impossible true graph 11 sixInputs.toFinset := by
  intro k small run
  have steps := list_run run sixInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (sixInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptopL q bank built hit
  omega
theorem replaceShort (s : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize 6 target s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  classical
  by_cases big : 13 ≤ s
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

end PEqualNP.Outside.L_meta_12142

theorem PEqualNP.Outside.L_meta_12142 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682240 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682240 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  exact PEqualNP.Outside.L_meta_12142.replaceShort s h
