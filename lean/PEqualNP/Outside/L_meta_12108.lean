import PEqualNP.Defs

-- The live-set and restriction lemmas follow L-meta-10554, L-meta-10802, L-meta-1674, L-meta-670 and L-meta-1667.
namespace PEqualNP.Outside.L_meta_12108
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


def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276676608 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [6, 5]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.and, [9, 3]⟩,
    ⟨.or, [10, 4]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.and, [8, 11]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [14, 13]⟩,
    ⟨.or, [12, 4]⟩,
    ⟨.and, [10, 16]⟩,
    ⟨.or, [15, 17]⟩], 18⟩
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
def pw42 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
def pw43 : Nat := 0xf0f00000f0f00000f0f00000f0f0
def pw44 : Nat := 0x5050505050505050505050505050505
def pw45 : Nat := 0xf000f000f000f000f000f000f000f0
def pw46 : Nat := 0xf0f00000f0f00000f0f00000f0f0000
def pw47 : Nat := 0xff000000ff000000ff000000ff0000
def pw48 : Nat := 0xff000000ff000000ff000000ff00
def pw49 : Nat := 0xf000f000f000f000f000f000f000f00
def pw50 : Nat := 0x5000500050005000500050005000500
def pw51 : Nat := 0x500050005000500050005000500050
def pw52 : Nat := 0x8080808080808080808080808080808
def pw53 : Nat := 0x5050000050500000505000005050
def pw54 : Nat := 0x8888000088880000888800008888
def pw55 : Nat := 0xf000f000f000f000f000f000f000f
def pw56 : Nat := 0xf0000000f0000000f0000000f0000
def pw57 : Nat := 0x20202020202020202020202020202020
def pw58 : Nat := 0xc000c000c000c000c000c000c000c
def pw59 : Nat := 0xaa000000aa000000aa000000aa
def pw60 : Nat := 0x40404040404040404040404040404040
def pw61 : Nat := 0x55550000555500005555000055550000
def pw62 : Nat := 0x33330000333300003333000033330000
def pw63 : Nat := 0x33003300330033003300330033003300
def pw64 : Nat := 0x550000005500000055000000550000
def pw65 : Nat := 0x5500000055000000550000005500
def pw66 : Nat := 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8
def pw67 : Nat := 0xa2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2
def pw68 : Nat := 0xf0f0fafaf0f0fafaf0f0fafaf0f0fafa
def pw69 : Nat := 0xcccc0000cccc0000cccc0000cccc
def pw70 : Nat := 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0
def pw71 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0
def pw72 : Nat := 0xffffff00ffffff00ffffff00ffffff00
def pw73 : Nat := 0xfffffff0fffffff0fffffff0fffffff0
def pw74 : Nat := 0xfff00000fff00000fff00000fff0
def pw75 : Nat := 0xffff8888ffff8888ffff8888ffff8888
def pw76 : Nat := 0xfff8fff8fff8fff8fff8fff8fff8fff8
def pw77 : Nat := 0xf8f80000f8f80000f8f80000f8f8
def pw78 : Nat := 0x88808880888088808880888088808880
def pw79 : Nat := 0x77707770777077707770777077707770
def pw80 : Nat := 0x222222aa222222aa222222aa222222aa
def pw81 : Nat := 0xccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0
def pw82 : Nat := 0xaaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0
def pw83 : Nat := 0xfff80000fff80000fff80000fff8
def pw84 : Nat := 0x77777770777777707777777077777770
def pw85 : Nat := 0xffffffff00000000ffffffff00000000
def pw86 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00
def pw87 : Nat := 0xffffffff00000000ffffffff
def pw88 : Nat := 0xff00ff0000000000ff00ff00
def pw89 : Nat := 0xaa000000aa000000aa000000aa00
def pw90 : Nat := 0x55555555000000005555555500000000
def pw91 : Nat := 0x33333333000000003333333300000000
def pw92 : Nat := 0xf000f000f000f000f000f000f000f000
def pw93 : Nat := 0xf0000000f0000000f0000000f000
def pw94 : Nat := 0xff00ff0000000000ff00ff00000000
def pw95 : Nat := 0x22222222000000002222222200000000
def pw96 : Nat := 0xa0a0a0a000000000a0a0a0a00000000
def pw97 : Nat := 0x30303030000000003030303000000000
def pw98 : Nat := 0xc0c0c0c000000000c0c0c0c00000000
def pw99 : Nat := 0x44444444000000004444444400000000
def pw100 : Nat := 0x55005500000000005500550000000000
def pw101 : Nat := 0xffff000000000000ffff000000000000
def pw102 : Nat := 0x55550000000000005555000000000000
def pw103 : Nat := 0xcc000000cc000000cc000000cc00
def pw104 : Nat := 0xff00000000000000ff000000000000
def pw105 : Nat := 0x30303030000000003030303
def pw106 : Nat := 0x50505050000000005050505
def pw107 : Nat := 0x220022000000000022002200000000
def pw108 : Nat := 0x440044000000000044004400000000
def pw109 : Nat := 0x101010100000000010101010
def pw110 : Nat := 0x10101010000000001010101000000000
def pw111 : Nat := 0x500050000000000050005000000000
def pw112 : Nat := 0x888888880000000088888888
def pw113 : Nat := 0xa0a0a0a000000000a0a0a0a0
def pw114 : Nat := 0xa000a00000000000a000a00000000
def pw115 : Nat := 0xc0c0c0c000000000c0c0c0c0
def pw116 : Nat := 0x111111110000000011111111
def pw117 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000
def pw118 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaa
def pw119 : Nat := 0xff000000ff000000ff000000ff000000
def pw120 : Nat := 0x3f003f003f003f003f003f003f003f00
def pw121 : Nat := 0xf0f00000f0f00000f0f00000f0f00000
def pw122 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee00
def pw123 : Nat := 0xeeeeeeee00000000eeeeeeee00000000
def pw124 : Nat := 0xaf00af00af00af00af00af00af00af00
def pw125 : Nat := 0xcccc0000cccc0000cccc0000cccc0000
def pw126 : Nat := 0xffffccccffffccccffffccccffffcccc
def pw127 : Nat := 0xff00aa00ff00aa00ff00aa00ff00aa00
def pw128 : Nat := 0xff000f00ff000f00ff000f00ff000f00
def pw129 : Nat := 0xffffff0000000000ffffff00000000
def pw130 : Nat := 0xeac0eac0eac0eac0eac0eac0eac0eac0
def pw131 : Nat := 0x8f888f888f888f888f888f888f888f88
def pw132 : Nat := 0xeaeac0c0eaeac0c0eaeac0c0eaeac0c0
def pw133 : Nat := 0x3f3f2a2a3f3f2a2a3f3f2a2a3f3f2a2a
def pw134 : Nat := 0xff00f000ff00f000ff00f000ff00f000
def pw135 : Nat := 0x8888f8f88888f8f88888f8f88888f8f8
def pw136 : Nat := 0x8f8f88888f8f88888f8f88888f8f8888
def pw137 : Nat := 0xff888888ff888888ff888888ff888888
def pw138 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc00
def pw139 : Nat := 0xfefefefef0f0f0f0fefefefef0f0f0f0
def pw140 : Nat := 0x2020202aaaaaaaa02020202aaaaaaaa
def pw141 : Nat := 0xfcfcfcfc00000000fcfcfcfc00000000
def pw142 : Nat := 0xffffeeeeffff0000ffffeeeeffff0000
def pw143 : Nat := 0x3030000ffff000003030000ffff0000
def pw144 : Nat := 0xeee0eee0eee0eee0eee0eee0eee0eee
def pw145 : Nat := 0xa8fca8fca8fca8fca8fca8fca8fca8fc
def pw146 : Nat := 0xe0eeeee0e0eeeee0e0eeeee0e0eeeee
def pw147 : Nat := 0xeeeee0e0eeeee0e0eeeee0e0eeeee0e0
def pw148 : Nat := 0xeeee0e0eeeee0e0eeeee0e0eeeee0e0e
def pw149 : Nat := 0xa8a8fcfca8a8fcfca8a8fcfca8a8fcfc
def pw150 : Nat := 0xeeeeee00eeeeee00eeeeee00eeeeee
def pw151 : Nat := 0xae0cae0cae0cae0cae0cae0cae0cae0c
def pw152 : Nat := 0x2f222f222f222f222f222f222f222f22
def pw153 : Nat := 0xaeae0c0caeae0c0caeae0c0caeae0c0c
def pw154 : Nat := 0xafaf8c8cafaf8c8cafaf8c8cafaf8c8c
def pw155 : Nat := 0xff00cc00ff00cc00ff00cc00ff00cc00
def pw156 : Nat := 0xa0acece0a0acece0a0acece0a0acece
def pw157 : Nat := 0xff003300ff003300ff003300ff003300
def pw158 : Nat := 0x2f2f22222f2f22222f2f22222f2f2222
def pw159 : Nat := 0xff0a0a0aff0a0a0aff0a0a0aff0a0a0a
def pw160 : Nat := 0xfff0aaa0fff0aaa0fff0aaa0fff0aaa
def pw161 : Nat := 0xaa00eeccaa00eeccaa00eeccaa00eecc
def pw162 : Nat := 0xaaff88ccaaff88ccaaff88ccaaff88cc
def pw163 : Nat := 0xf00afaa0f00afaa0f00afaa0f00afaa
def pw164 : Nat := 0xaaffffffaaaaaaaaaaffffffaaaaaaaa
def pw165 : Nat := 0xaa000000aaaaaaaaaa000000aaaaaaaa
def pw166 : Nat := 0xffc0c0c0ffc0c0c0ffc0c0c0ffc0c0c0
def pw167 : Nat := 0xf0fffffff0f0f0f0f0fffffff0f0f0f0
def pw168 : Nat := 0xf0000000f0f0f0f0f0000000f0f0f0f0
def pw169 : Nat := 0xffeeeeeeff000000ffeeeeeeff000000
def pw170 : Nat := 0xf0f0f0f000000000f0f0f0f000000000
def pw171 : Nat := 0xf0f0f0f000000000f0f0f0f00000000
def pw172 : Nat := 0xee000000eeeeeeeeee000000eeeeeeee
def pw173 : Nat := 0xccffffffccccccccccffffffcccccccc
def pw174 : Nat := 0xcc000000cccccccccc000000cccccccc
def pw175 : Nat := 0x2a3f3f3f2a2a2a2a2a3f3f3f2a2a2a2a
def pw176 : Nat := 0xeac0c0c0eaeaeaeaeac0c0c0eaeaeaea
def pw177 : Nat := 0xa8fcfcfca8a8a8a8a8fcfcfca8a8a8a8
def pw178 : Nat := 0xeeeeeee0e0e0e0e0eeeeeee0e0e0e0e
def pw179 : Nat := 0x8acfcfcf8a8a8a8a8acfcfcf8a8a8a8a
def pw180 : Nat := 0xae0c0c0caeaeaeaeae0c0c0caeaeaeae
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
def p14_T : Nat := 0xa880a880a880a880a880a880a880a880
def p14_R : List Nat := [0, 1, 2, 3]
def p14_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
def p14_Z : List SliceD := [(pw3,4,[1, 2, 3])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN true p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p14_B p3_B p3_L (by decide +kernel),by simp⟩
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
def p15_T : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
def p15_R : List Nat := [0, 1, 2, 3]
def p15_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p15_B : baseOK p15_T p15_R p15_E = true := by decide +kernel
def p15_Z : List SliceD := [(pw4,4,[0, 1, 3])]
theorem p15_Y : ∀ s ∈ p15_Z, SliceN true p15_R p15_T s := by
  unfold p15_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p15_B p3_B p3_L (by decide +kernel),by simp⟩
def p15_C : List (Nat × List Nat) := [(0,[])]
def p15_t : Tabs := (p15_C.map (mkCut true p15_Z),[],[],[])
theorem p15_W : TabsP true p15_R p15_T p15_t := ⟨cutsGood p15_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D4 : List StD := [
([pw3,pw2,pw5,pw6],[0],[1,1,1,1,1,1])]
def p15_D3 : List StD := []
theorem p15_I3 : LevelN true p15_T 3 p15_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p15_C4x0 : levelOK true p15_T p15_t 3 (p15_D3.map Prod.fst) ((p15_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p15_I4 : LevelN true p15_T 4 p15_D4 := levelStep p15_B p15_W p15_I3 (chunks 32 p15_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C4x0
  ))
theorem p15_L : LowN true p15_R p15_T 5 := lowSearch p15_B p15_I4 (by decide +kernel)
def p16_T : Nat := 0xeee8e880eee8e880eee8e880eee8e880
def p16_R : List Nat := [0, 1, 2, 3, 4]
def p16_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,3,19)]
theorem p16_B : baseOK p16_T p16_R p16_E = true := by decide +kernel
def p16_Z : List SliceD := [(pw3,7,[1, 2, 3, 4]),(pw2,7,[0, 2, 3, 4]),(pw4,7,[0, 1, 3, 4]),(pw17,7,[0, 1, 2, 4]),(pw41,7,[0, 1, 2, 3]),(pw1,5,[1, 2, 3, 4]),(pw42,4,[1, 2, 3]),(pw5,5,[0, 1, 3, 4]),(pw43,4,[0, 1, 3]),(pw0,5,[0, 2, 3, 4]),(pw44,2,[1, 3, 4]),(pw45,4,[0, 1, 4]),(pw6,5,[0, 1, 2, 4]),(pw46,4,[0, 1, 3]),(pw47,4,[0, 1, 2]),(pw19,4,[2, 3, 4]),(pw20,4,[2, 3, 4]),(pw48,4,[0, 1, 2]),(pw14,2,[1, 3, 4]),(pw49,4,[0, 1, 4]),(pw50,1,[1, 4]),(pw51,1,[1, 4]),(pw52,1,[3, 4]),(pw31,2,[1, 3, 4]),(pw53,1,[1, 3]),(pw54,1,[2, 3]),(pw55,2,[0, 1, 4]),(pw10,2,[0, 3, 4]),(pw56,1,[0, 1]),(pw57,1,[3, 4]),(pw58,1,[0, 4]),(pw59,1,[1, 2]),(pw60,1,[3, 4]),(pw61,2,[1, 2, 3]),(pw34,2,[1, 2, 4]),(pw62,2,[0, 2, 3]),(pw63,2,[0, 2, 4]),(pw64,1,[1, 2]),(pw65,1,[1, 2])]
theorem p16_Y : ∀ s ∈ p16_Z, SliceN true p16_R p16_T s := by
  unfold p16_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p16_B p7_B p7_L (by decide +kernel),mkSlice (w:=2) p16_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p16_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p16_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p16_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p16_B p14_B p14_L (by decide +kernel),mkSlice (w:=1) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=4) p16_B p15_B p15_L (by decide +kernel),mkSlice (w:=4) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p16_B p14_B p14_L (by decide +kernel),mkSlice (w:=0) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=4) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=8) p16_B p15_B p15_L (by decide +kernel),mkSlice (w:=16) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=16) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=1) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=2) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=8) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=5) p16_B p6_B p6_L (by decide +kernel),mkSlice (w:=8) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=8) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=3) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=4) p16_B p11_B p11_L (by decide +kernel),mkSlice (w:=4) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=3) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p16_B p4_B p4_L (by decide +kernel),mkSlice (w:=4) p16_B p11_B p11_L (by decide +kernel),mkSlice (w:=16) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=5) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=2) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=6) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=16) p16_B p11_B p11_L (by decide +kernel),mkSlice (w:=8) p16_B p11_B p11_L (by decide +kernel),mkSlice (w:=16) p16_B p11_B p11_L (by decide +kernel),mkSlice (w:=8) p16_B p11_B p11_L (by decide +kernel),mkSlice (w:=16) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=8) p16_B p1_B p1_L (by decide +kernel),by simp⟩
def p16_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(2,[128]),(5,[]),(3,[128]),(4,[128]),(1,[386]),(6,[]),(2,[386]),(3,[386]),(0,[261]),(1,[261]),(7,[]),(4,[393]),(8,[]),(1,[129]),(0,[129]),(3,[128,273]),(4,[128,273]),(9,[]),(10,[]),(11,[]),(0,[130]),(0,[386]),(4,[130]),(4,[131]),(12,[]),(0,[385]),(2,[128,402]),(13,[]),(14,[]),(2,[130]),(5,[261]),(12,[128]),(4,[128,393]),(2,[129]),(15,[]),(1,[128]),(3,[262,19]),(4,[262,19]),(0,[391]),(1,[386,145]),(3,[386,273]),(4,[257]),(3,[384]),(4,[385]),(3,[385]),(1,[258,402]),(0,[393]),(16,[]),(2,[262]),(0,[258]),(2,[386,262]),(17,[]),(4,[390]),(2,[384]),(2,[385]),(1,[386,261]),(2,[258]),(18,[]),(2,[256]),(1,[261,512]),(3,[256]),(1,[261,16]),(1,[389,393]),(0,[389,393]),(2,[393]),(19,[]),(0,[389]),(3,[395]),(2,[395]),(0,[261,401]),(1,[261,401]),(2,[394]),(0,[261,402]),(1,[261,402]),(2,[128,521]),(1,[129,257]),(0,[129,257]),(3,[128,521]),(11,[128]),(20,[]),(21,[]),(14,[130]),(0,[385,389]),(2,[128,401]),(15,[257]),(22,[]),(2,[128,403]),(1,[385,389]),(5,[389]),(23,[]),(0,[385,391]),(3,[128,393]),(24,[]),(3,[128,525]),(1,[129,273]),(0,[129,273]),(2,[128,273]),(2,[128,275]),(15,[129]),(3,[128,523]),(2,[128,523]),(2,[128,400]),(0,[384]),(8,[128]),(13,[128]),(2,[128,525]),(8,[130]),(0,[129,402]),(5,[390]),(25,[]),(15,[258]),(14,[128]),(2,[260,19]),(2,[256,147]),(2,[128,272]),(0,[261,512]),(2,[260,512]),(3,[128,272]),(26,[]),(2,[130,272]),(2,[257]),(2,[259]),(2,[263,19]),(2,[131,272]),(2,[261]),(2,[259,147]),(0,[261,515]),(1,[261,515]),(3,[128,275]),(27,[]),(2,[128,257]),(2,[128,259]),(0,[259,145]),(0,[129,275]),(2,[128,520]),(1,[261,18]),(0,[261,18]),(3,[128,522]),(28,[]),(17,[128]),(2,[261,16]),(2,[128,274]),(2,[256,131]),(2,[256,516]),(9,[261]),(29,[]),(2,[128,256]),(3,[128,256]),(30,[]),(2,[393,130]),(2,[393,131]),(3,[393]),(12,[393]),(9,[393]),(9,[389]),(2,[128,393]),(19,[128]),(5,[393]),(0,[393,391]),(2,[128,395]),(0,[393,146]),(2,[128,394]),(0,[394,145]),(2,[394,130]),(2,[394,131]),(2,[394,128]),(2,[393,128]),(2,[393,129]),(0,[393,130]),(0,[393,129]),(1,[128,393]),(15,[261]),(1,[393]),(1,[393,514]),(0,[393,512]),(12,[130]),(17,[130]),(31,[]),(3,[388,19]),(5,[395]),(2,[260,258]),(2,[129,272]),(15,[131]),(16,[129]),(32,[]),(2,[256,260]),(1,[261,389,393]),(0,[261,389,393]),(33,[]),(34,[]),(35,[]),(36,[]),(2,[393,16]),(2,[384,273]),(2,[256,401]),(3,[393,16]),(12,[128,401]),(0,[257,385,393]),(16,[261]),(2,[393,128,405]),(37,[]),(2,[393,128,277]),(38,[]),(2,[128,273,525]),(0,[393,392,21]),(0,[393,259,406]),(0,[385,257,407]),(0,[257,259,406]),(2,[128,394,21]),(5,[394,145]),(2,[128,393,535]),(8,[131]),(5,[261,402]),(2,[128,273,655]),(9,[261,402]),(2,[393,130,276]),(2,[393,257]),(2,[393,259]),(2,[393,263,23]),(2,[393,131,276]),(2,[393,261]),(2,[393,259,151]),(2,[393,128,279]),(0,[393,261,22]),(1,[393,261,22]),(13,[128,271]),(2,[394,128,279]),(2,[260,261,20]),(2,[260,128,278]),(2,[260,130,276]),(2,[256,257,148]),(2,[256,128,278]),(2,[256,131,276]),(2,[256,260,640]),(3,[256,260]),(2,[128,129,276]),(2,[128,130,276]),(2,[128,131,276]),(2,[128,260,256]),(2,[128,260,259]),(5,[261,16]),(2,[128,256,263]),(3,[128,256,260]),(5,[389,393]),(5,[261,393]),(5,[261,389]),(9,[389,393]),(9,[261,393]),(9,[261,389]),(0,[393,392,149]),(0,[393,263,406]),(0,[393,261,407]),(2,[129,128,406]),(17,[129]),(14,[129]),(17,[128,129]),(14,[128,129]),(2,[128,129,394]),(2,[128,129,527,281]),(2,[128,129,393,539]),(2,[128,129,392]),(0,[129,521,406]),(0,[389,393,261,26]),(33,[261]),(1,[389,261,22]),(8,[129]),(8,[128,129])]
def p16_t : Tabs := (p16_C.map (mkCut true p16_Z),[(13,12),(14,12),(7,5),(14,10),(7,2),(14,6),(7,6),(22,6),(19,18),(13,9),(13,5),(21,5),(19,17),(7,3),(21,17),(25,17),(25,9),(11,3),(19,3),(21,20),(22,20),(25,24),(26,10),(13,4),(21,4),(13,8),(13,1),(7,4),(19,2),(11,9),(22,18),(26,18),(11,2),(7,1),(11,1),(19,1),(14,18),(11,10),(13,17)],[],[[],[2,3],[3],[0,2,3],[0,3],[0],[2],[3,2],[0,3,2],[2,3,2]])
theorem p16_W : TabsP true p16_R p16_T p16_t := ⟨cutsGood p16_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D9 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0,4,8,12,16,1,5,13,21,3,9,29,7,11,17,25,33,37,41,45,49,53,57,61,65,15,19,23],[1635,20645,41257,68145,33685702,67372106,135790674,2098060,4204692,25170200])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D8 : List StD := [
([pw7,pw3,pw2,pw5,pw6,pw40],[0,4,20,28,32,24,1,37,41,45,53,3,5,69,7,11,8,12,16,13,21,57,61,65,73,77,81,27,31],[3,1,85156,134390056,285477424,3,524357,1048649,33554513,4230,4362,67109394,3468,2131476,12607512]),
([pw42,pw3,pw2,pw5,pw6,pw40],[0,3,16,36,44,5,24,40,48,13,53,77,27,9,21,29,4,8,12,37,41,49,57,69,85,89,35],[5,67182826,136898,8671426,1,2089,2577,16779265,5,529464,1057066,2097166,18194,4227092,33587460]),
([pw3,pw2,pw5,pw6,pw28,pw40],[8,12,52,56,1,5,3,60,64,29,13,21,33,49,23,68,9,37,41,45,65,73,7,11,31,35],[65660,1045,2070,16781524,4948,131113,262186,33579176,549160,3,3,4195841,1,9439234,2130880])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D7 : List StD := [
([pw7,pw3,pw2,pw5,pw66,pw6,pw40],[72,24,76,20,80,84,88,69,3,11,92,61,65,73,28,32,41,45,7,39],[1,5,10,8,402,8738,5,15,5,6,6,73,5,81,97,2,327704,655400,20368,46880,6288]),
([pw3,pw2,pw5,pw66,pw6,pw40],[20,60,76,72,68,80,96,84,61,12,16,100,41,45,65,93,97],[13,7,13,32868,65684,15,5,4200,8344,2051,3,3,866,17554,368]),
([pw54,pw3,pw2,pw5,pw6,pw40],[88,32,36,104,128,24,124,132,53,8,12,60,108,112,116,120,41,69],[4105,8193,2817,148481,32771,13,104,40,14,5,5,7,66000,146,18]),
([pw7,pw3,pw2,pw5,pw6,pw28,pw40],[56,20,28,52,148,140,45,3,24,60,136,144,73,7,11,12,64,88,116,128,1,37,41,65,77,81,93,101,23],[1025,9,9762,311332,928,594016,9,134217738,67108876,2440,17825816,2097155,4194309,268568577,33554513,6,4,8274,2,8405012,4304]),
([pw67,pw3,pw2,pw5,pw6,pw40],[24,100,136,156,160,164,37,20,116,152,168,57,61,65,69,105,3],[129,513,7,265,9,3,7,3,3,28,24,24,32868,2116,95264]),
([pw3,pw2,pw5,pw68,pw6,pw40],[96,44,24,172,1,128,180,176,69,41,88,184,109],[4252,30,22,93,30,131,1057,961,2080,4,515,3,353,10,353]),
([pw59,pw3,pw2,pw5,pw6,pw40],[24,128,48,9,53,116,204,208,200,4,88,132,188,192,196],[4097,1545,19,8197,16387,329,19,69,67,154,420,138,38,2066,38]),
([pw42,pw21,pw3,pw2,pw5,pw6,pw40],[156,132,36,40,208,53,24,116,188,220,224,4,44,48,68,96,212,216,228,5,61],[203,259,2051,98338,386,1,73,3,20513,7,11,655365,529,19,19,5,7,7,1026,1570,1318914]),
([pw42,pw69,pw3,pw2,pw5,pw6],[132,36,104,128,156,16,53,69,97,24,208,41],[6,36,23,73,137,519,34,73,145,262,268,1029,18,19,2057]),
([pw42,pw3,pw2,pw5,pw6,pw28,pw40],[132,68,44,52,96,224,240,40,232,5,24,56,116,128,156,236,9,49,77,35],[257,591873,277,4113,147,32769,262728,6,41,1034,3,6,609,147522,3,5,1,37,4,8195,131]),
([pw70,pw3,pw2,pw5,pw6,pw28,pw40],[116,252,52,140,224,248,5,45,68,256,73,3,244,56,96,132,260,9,49,113,35],[4097,1189992,36878,47,5,1208,2636,262,47,5,524340,834,16385,264705,1232,259,65539,146,3,145,1041]),
([pw70,pw3,pw2,pw5,pw6,pw40],[24,52,252,45,68,208,260,9,156,244,264,4,132,224,41,49,117,121,125],[513,2433,7,769,4121,3,7,3,3,1188,65760,33848,70,139276,278616]),
([pw3,pw2,pw5,pw6,pw71,pw72],[96,276,280,268,272,1,5,288,9,89,3,132,204,284,292,29,45,65],[1400,51,53,4625,40980,75,77,131593,65804,3075,131,3,135,16389,3]),
([pw3,pw2,pw5,pw6,pw40,pw73],[96,224,276,296,300,132,1,5,3,0,4,24,68,156,288,292,304,9,23],[131544,77,75,42,2825,149,147,50,271377,39,5,16389,4103,32769,65539]),
([pw74,pw3,pw2,pw5,pw6,pw40],[132,68,304,224,8,12,308,312,1,5,0,128,276,9,3],[1027,3,51,51,4097,25536,6,329,3,6,649,3,7,15,2051])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D6 : List StD := [
([pw3,pw2,pw5,pw66,pw6,pw35,pw40],[316,320,324,24,328,156,336,68,224,332,340,31],[7,11,3,14,6,12,35,5,34,6,34,8,2065,145,513,273,17,832,8,80,1216]),
([pw7,pw3,pw2,pw5,pw6,pw75,pw71],[356,348,352,360,368,344,372,376,364,380,384,388,392,69,27],[32,2,16389,41,256,41,18,70,66,18,66,21,9,18,9,132,133,512,3080,12416,5]),
([pw7,pw3,pw2,pw5,pw6,pw76,pw40],[396,140,400,404,80,412,360,40,144,332,408,416,420,3],[1,4,11,26,1024,66,5,11,6,5,6,41,49,5,33,26,2048,520,4096,272,8384]),
([pw77,pw7,pw3,pw2,pw5,pw6,pw40],[124,432,436,448,452,456,24,28,424,428,440,444,460,464],[257,65,513,65,134,1024,2048,8,3,48,6,24,3,24,6,3,4128,6,3,8225,6]),
([pw78,pw3,pw2,pw5,pw6,pw28,pw40],[476,480,140,432,144,488,68,264,408,468,132,332,412,472,484,492],[512,8192,576,257,256,1088,7,7,6,6,6,9,16432,138,4232,9,32,2049,1,56,32784]),
([pw79,pw3,pw2,pw5,pw6,pw28,pw40],[432,408,524,528,144,532,492,68,376,476,496,508,132,500,504,512,516,520,536],[27648,231424,1152,514,512,4224,14,7,52,69,261,11,56,73,262153,3,32,258,2,49,80]),
([pw79,pw7,pw3,pw2,pw5,pw6,pw40],[360,376,404,408,412,564,4,456,548,560,0,40,140,336,540,544,552,556,568],[4,49216,1088,65796,131332,2051,512,32,152,3,3,544,4136,3,3,10,17,17,3,3,270464]),
([pw79,pw3,pw2,pw5,pw6,pw40],[408,560,532,564,432,496,572,68,132,360,376,500,576,1,5,17,45,65,113,129,133,137,141,3,27],[2090,10,37,5,1920,11,32777,524300,270424,1048579,2097158,4210770,7,16846849,8519700]),
([pw7,pw70,pw2,pw5,pw6,pw28,pw40],[432,600,476,604,52,68,256,588,592,608,28,56,144,224,260,376,492,496,572,580,584,596,612,3],[1703940,128,160,24832,65824,262176,2099204,1044,20,16,32771,9,66,8388673,67,9,512,10,8,4609,4194306]),
([pw7,pw3,pw2,pw5,pw6,pw71,pw72],[332,640,268,272,644,68,384,616,628,632,636,372,620,624,648,652,656,3,7,11],[128,4096,160,8448,524832,263424,12,11,25,16392,2056,7,21,516,1028,131138,32768,3,82,65536,3]),
([pw7,pw3,pw2,pw5,pw6,pw40,pw73],[296,432,300,640,384,68,24,144,464,616,88,116,132,332,620,624,656,660,664,3],[512,16384,544,34816,4128,524384,5,11,145,259,65,14,148,262,1028,11,8216,131072,26,65536,262144]),
([pw74,pw7,pw3,pw2,pw5,pw6,pw40],[432,464,680,68,132,576,20,308,312,668,672,0,116,436,640,676],[24,2051,3,578,577,16384,1024,32768,1032,4112,24,384,5,162,3,5,290,3,7,38,8193]),
([pw67,pw3,pw2,pw5,pw6,pw40,pw72],[692,616,68,648,700,96,132,684,24,156,704,116,224,688,696],[128,8322,16513,2112,4160,832,9,11,9,9,257,19,1040,1040,528,6,34,6,36,4,32]),
([pw80,pw3,pw2,pw5,pw6,pw40,pw72],[704,648,712,144,344,68,688,708,720,732,616,716,724,728,736],[8,1096,96,138,35,138,2054,3,3,3,3,5,5,5,5,272,4112,8208,768,16384,512]),
([pw70,pw3,pw81,pw2,pw5,pw6,pw40],[412,224,492,256,600,740,156,24,52,56,68,116,476,480,484,496,512,744,748,752,756,760,3],[32,233472,16960,262177,96,22,388,4202504,1029,7,524291,2,9,11,1048577,9,7,9,2097169,22,2052]),
([pw3,pw2,pw28,pw71,pw72],[628,68,764,768,145,12,9,8,272,376,600,772,776,780,784,1,5,25,117,149,153,3],[2195532,2329,528394,131593,1056789,278534,1093,35,147,35]),
([pw82,pw2,pw5,pw6,pw40],[68,788,24,800,156,4,88,116,132,208,224,792,796],[116,7,2068,4101,3,136,769,3,1035,11])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D5 : List StD := [
([pw3,pw2,pw5,pw35,pw75,pw72],[648,804,808,812,704,820,816,824,828,832,836,840,844,848,53],[7,5,7,5,7,24,12,12,26,98,416,16898,3074,4097,8193]),
([pw83,pw7,pw3,pw2,pw5,pw6],[432,464,868,872,68,124,132,144,852,128,444,856,860,864,876,3],[112,259,3,2082,4353,1024,8192,532,76,49156,13,130,9,130,11]),
([pw79,pw3,pw2,pw5,pw40,pw72],[432,908,912,916,376,880,68,408,892,920,132,576,596,884,888,896,900,904,924,3],[24864,229632,96,1088,176,14,7,517,20,11,521,4104,526338,144,262144]),
([pw7,pw70,pw81,pw5,pw6,pw40],[432,972,68,600,932,944,144,224,484,556,572,592,760,772,928,936,940,948,952,956,960,964,968,976,980,984,988],[49424,198688,4100,786560,1028,7340544,17,8388610,16777225,33,33554434,8193,3,10,67108929]),
([pw7,pw3,pw2,pw28,pw71,pw72],[764,768,640,68,992,996,1000,224,616,620,656,664,1004,1008,1012,1016,1020,1024,3,7,11],[256,512,262168,1048616,524480,3,18,34,66,4097,8193,16385,229380,1028,2052]),
([pw84,pw3,pw2,pw5,pw6,pw40],[432,772,436,444,784,464,576,0,8,132,224,408,476,3],[9,136,264,7168,520,8211,7,50,5,21,96,3,5,66,3])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D4 : List StD := [
([pw83,pw7,pw22,pw5,pw6],[464,576,1028,1032,1036,1040,1044,1064,876,1048,1052,1056,1060,109],[28,3,100,7680,8192,384,24,128,3,96]),
([pw79,pw3,pw2,pw71,pw72],[600,784,1072,532,880,892,1068,132,408,884,888,896,900,904,908,916,996,1000,1076],[1584,14368,138,273,16452,65600,131073,32774,262149,10]),
([pw84,pw22,pw5,pw6,pw40],[772,464,1036,432,1040,1080,152,436,576,1032,1044,1084,109],[4102,97,517,36,136,258,10,1040,17,2049])]
def p16_D3 : List StD := []
theorem p16_I3 : LevelN true p16_T 3 p16_D3 := by intro s h; cases h
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
theorem p16_I5 : LevelN true p16_T 5 p16_D5 := levelStep p16_B p16_W p16_I4 (chunks 32 p16_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C5x0
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
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C9x0 : levelOK true p16_T p16_t 8 (p16_D8.map Prod.fst) ((p16_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I9 : LevelN true p16_T 9 p16_D9 := levelStep p16_B p16_W p16_I8 (chunks 32 p16_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C9x0
  ))
theorem p16_L : LowN true p16_R p16_T 10 := lowSearch p16_B p16_I9 (by decide +kernel)
def p17_T : Nat := 0xe8808880e8808880e8808880e8808880
def p17_R : List Nat := [0, 1, 2, 3, 4]
def p17_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,13,29)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
def p17_Z : List SliceD := [(pw40,7,[0, 1, 2, 3])]
theorem p17_Y : ∀ s ∈ p17_Z, SliceN true p17_R p17_T s := by
  unfold p17_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=16) p17_B p5_B p5_L (by decide +kernel),by simp⟩
def p17_C : List (Nat × List Nat) := [(0,[])]
def p17_t : Tabs := (p17_C.map (mkCut true p17_Z),[],[],[])
theorem p17_W : TabsP true p17_R p17_T p17_t := ⟨cutsGood p17_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D7 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0],[1,1,1,1,1,1,1,1,1,1])]
def p17_D6 : List StD := []
theorem p17_I6 : LevelN true p17_T 6 p17_D6 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p17_C7x0 : levelOK true p17_T p17_t 6 (p17_D6.map Prod.fst) ((p17_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I7 : LevelN true p17_T 7 p17_D7 := levelStep p17_B p17_W p17_I6 (chunks 32 p17_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C7x0
  ))
theorem p17_L : LowN true p17_R p17_T 8 := lowSearch p17_B p17_I7 (by decide +kernel)
def p18_T : Nat := 0xe888e888e888e888e888e888e888e888
def p18_R : List Nat := [0, 1, 2, 3]
def p18_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,9,13),(3,5,13)]
theorem p18_B : baseOK p18_T p18_R p18_E = true := by decide +kernel
def p18_Z : List SliceD := [(pw5,4,[0, 1, 3])]
theorem p18_Y : ∀ s ∈ p18_Z, SliceN true p18_R p18_T s := by
  unfold p18_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=4) p18_B p3_B p3_L (by decide +kernel),by simp⟩
def p18_C : List (Nat × List Nat) := [(0,[])]
def p18_t : Tabs := (p18_C.map (mkCut true p18_Z),[],[],[])
theorem p18_W : TabsP true p18_R p18_T p18_t := ⟨cutsGood p18_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D4 : List StD := [
([pw3,pw2,pw5,pw6],[0],[1,1,1,1,1,1])]
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
theorem p18_L : LowN true p18_R p18_T 5 := lowSearch p18_B p18_I4 (by decide +kernel)
def p19_T : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8
def p19_R : List Nat := [0, 1, 2, 3]
def p19_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p19_B : baseOK p19_T p19_R p19_E = true := by decide +kernel
def p19_Z : List SliceD := [(pw17,4,[0, 1, 2])]
theorem p19_Y : ∀ s ∈ p19_Z, SliceN true p19_R p19_T s := by
  unfold p19_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p19_B p3_B p3_L (by decide +kernel),by simp⟩
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
def p20_T : Nat := 0x88808880888088808880888088808880
def p20_R : List Nat := [0, 1, 2, 3]
def p20_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p20_B : baseOK p20_T p20_R p20_E = true := by decide +kernel
theorem p20_L : LowN true p20_R p20_T 3 := lowCount p20_B (by decide +kernel)
def p21_T : Nat := 0xa888a888a888a888a888a888a888a888
def p21_R : List Nat := [0, 1, 2, 3]
def p21_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,9,13),(3,5,13)]
theorem p21_B : baseOK p21_T p21_R p21_E = true := by decide +kernel
theorem p21_L : LowN true p21_R p21_T 3 := lowCount p21_B (by decide +kernel)
def p22_T : Nat := 0xeae8e888eae8e888eae8e888eae8e888
def p22_R : List Nat := [0, 1, 2, 3, 4]
def p22_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,9,13),(3,5,13),(4,5,21)]
theorem p22_B : baseOK p22_T p22_R p22_E = true := by decide +kernel
def p22_Z : List SliceD := [(pw0,5,[0, 2, 3, 4]),(pw3,5,[1, 2, 3, 4]),(pw19,4,[2, 3, 4]),(pw5,5,[0, 1, 3, 4]),(pw17,5,[0, 1, 2, 4]),(pw6,5,[0, 1, 2, 4]),(pw41,5,[0, 1, 2, 3]),(pw40,5,[0, 1, 2, 3]),(pw14,2,[1, 3, 4]),(pw1,3,[1, 2, 3, 4]),(pw45,4,[0, 1, 4]),(pw43,4,[0, 1, 3]),(pw4,3,[0, 1, 3, 4]),(pw10,2,[0, 3, 4])]
theorem p22_Y : ∀ s ∈ p22_Z, SliceN true p22_R p22_T s := by
  unfold p22_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p22_B p14_B p14_L (by decide +kernel),mkSlice (w:=1) p22_B p9_B p9_L (by decide +kernel),mkSlice (w:=1) p22_B p3_B p3_L (by decide +kernel),mkSlice (w:=4) p22_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p22_B p18_B p18_L (by decide +kernel),mkSlice (w:=8) p22_B p19_B p19_L (by decide +kernel),mkSlice (w:=0) p22_B p18_B p18_L (by decide +kernel),mkSlice (w:=16) p22_B p19_B p19_L (by decide +kernel),mkSlice (w:=5) p22_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p22_B p20_B p20_L (by decide +kernel),mkSlice (w:=4) p22_B p3_B p3_L (by decide +kernel),mkSlice (w:=4) p22_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p22_B p21_B p21_L (by decide +kernel),mkSlice (w:=4) p22_B p11_B p11_L (by decide +kernel),by simp⟩
def p22_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(4,[256]),(10,[]),(6,[256]),(11,[]),(12,[]),(13,[])]
def p22_t : Tabs := (p22_C.map (mkCut true p22_Z),[(14,12),(3,2),(3,0),(14,10),(3,6),(14,6),(3,10),(22,6),(3,18),(3,1),(19,1),(25,17),(25,9),(7,5),(11,2),(19,2),(3,17),(22,18),(14,2),(13,12),(3,9)],[],[[]])
theorem p22_W : TabsP true p22_R p22_T p22_t := ⟨cutsGood p22_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p22_D7 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0,4,12,16,20,28,1,5,21,24,13,29,37,45,3,8,9,17,25,33,41,49],[98499,148614,262554,527010,21573,4441,1051233,9500,2099748,8504])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p22_D6 : List StD := [
([pw14,pw3,pw2,pw5,pw6,pw40],[4,8,12,52,32,36,44,40,48,1,37,53,69,0,16,20,24,28,13,49,57,61,65,73],[5,11314,1,49200,196656,515,5,1048769,2097417,1030,2562,4194314,8392900,266508,524360]),
([pw10,pw3,pw2,pw5,pw6,pw40],[8,52,44,5,56,60,77,69,16,20,28,13,49,61,65,73,81],[121,3,1,820,1074,73,121,73,8203,3,65541,16387,32902,2182,4102])]
def p22_D5 : List StD := []
theorem p22_I5 : LevelN true p22_T 5 p22_D5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p22_C6x0 : levelOK true p22_T p22_t 5 (p22_D5.map Prod.fst) ((p22_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p22_I6 : LevelN true p22_T 6 p22_D6 := levelStep p22_B p22_W p22_I5 (chunks 32 p22_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p22_C7x0 : levelOK true p22_T p22_t 6 (p22_D6.map Prod.fst) ((p22_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p22_I7 : LevelN true p22_T 7 p22_D7 := levelStep p22_B p22_W p22_I6 (chunks 32 p22_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C7x0
  ))
theorem p22_L : LowN true p22_R p22_T 8 := lowSearch p22_B p22_I7 (by decide +kernel)
def p23_T : Nat := 0xeeeaeaa0eeeaeaa0eeeaeaa0eeeaeaa0
def p23_R : List Nat := [0, 1, 2, 3, 4]
def p23_E : List (Nat × Nat × Nat) := [(0,4,5),(1,12,14),(2,1,5),(3,1,9),(4,1,17)]
theorem p23_B : baseOK p23_T p23_R p23_E = true := by decide +kernel
def p23_Z : List SliceD := [(pw2,7,[0, 2, 3, 4])]
theorem p23_Y : ∀ s ∈ p23_Z, SliceN true p23_R p23_T s := by
  unfold p23_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=2) p23_B p7_B p7_L (by decide +kernel),by simp⟩
def p23_C : List (Nat × List Nat) := [(0,[])]
def p23_t : Tabs := (p23_C.map (mkCut true p23_Z),[],[],[])
theorem p23_W : TabsP true p23_R p23_T p23_t := ⟨cutsGood p23_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p23_D7 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0],[1,1,1,1,1,1,1,1,1,1])]
def p23_D6 : List StD := []
theorem p23_I6 : LevelN true p23_T 6 p23_D6 := by intro s h; cases h
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
def p25_T : Nat := 0x88808000888080008880800088808000
def p25_R : List Nat := [0, 1, 2, 3, 4]
def p25_E : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15),(4,7,23)]
theorem p25_B : baseOK p25_T p25_R p25_E = true := by decide +kernel
def p25_Z : List SliceD := [(pw3,5,[1, 2, 3, 4])]
theorem p25_Y : ∀ s ∈ p25_Z, SliceN true p25_R p25_T s := by
  unfold p25_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p25_B p14_B p14_L (by decide +kernel),by simp⟩
def p25_C : List (Nat × List Nat) := [(0,[])]
def p25_t : Tabs := (p25_C.map (mkCut true p25_Z),[],[],[])
theorem p25_W : TabsP true p25_R p25_T p25_t := ⟨cutsGood p25_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p25_D5 : List StD := [
([pw3,pw2,pw5,pw6,pw40],[0],[1,1,1,1,1,1,1,1,1,1])]
def p25_D4 : List StD := []
theorem p25_I4 : LevelN true p25_T 4 p25_D4 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p25_C5x0 : levelOK true p25_T p25_t 4 (p25_D4.map Prod.fst) ((p25_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p25_I5 : LevelN true p25_T 5 p25_D5 := levelStep p25_B p25_W p25_I4 (chunks 32 p25_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p25_C5x0
  ))
theorem p25_L : LowN true p25_R p25_T 6 := lowSearch p25_B p25_I5 (by decide +kernel)
def p26_T : Nat := 0xa8888880a8888880a8888880a8888880
def p26_R : List Nat := [0, 1, 2, 3, 4]
def p26_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,3,19)]
theorem p26_B : baseOK p26_T p26_R p26_E = true := by decide +kernel
def p26_Z : List SliceD := [(pw3,6,[1, 2, 3, 4])]
theorem p26_Y : ∀ s ∈ p26_Z, SliceN true p26_R p26_T s := by
  unfold p26_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p26_B p12_B p12_L (by decide +kernel),by simp⟩
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
def ptopT : Nat := 0xfee8e800fe008000fee8e800fe008000
def ptopR : List Nat := [0, 1, 2, 3, 4, 5]
def ptopE : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15),(4,9,25),(5,11,43)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(pw6,9,[4, 1, 2, 0, 5]),(pw85,10,[3, 4, 2, 0, 1]),(pw1,8,[3, 4, 1, 2, 5]),(pw5,8,[3, 4, 5, 1, 0]),(pw4,8,[3, 4, 0, 1, 5]),(pw40,8,[3, 5, 2, 0, 1]),(pw41,8,[3, 1, 2, 0, 5]),(pw0,8,[3, 4, 0, 2, 5]),(pw2,8,[3, 4, 5, 2, 0]),(pw3,8,[3, 4, 5, 2, 1]),(pw48,7,[0, 1, 2, 5]),(pw17,6,[4, 5, 2, 0, 1]),(pw63,5,[4, 2, 0, 5]),(pw60,4,[3, 4, 5]),(pw47,5,[5, 1, 2, 0]),(pw52,4,[3, 4, 5]),(pw57,4,[3, 4, 5]),(pw86,5,[4, 2, 1, 5]),(pw87,7,[3, 4, 2, 0, 1]),(pw88,6,[4, 1, 2, 0]),(pw49,5,[4, 1, 0, 5]),(pw89,4,[1, 2, 5]),(pw90,7,[1, 2, 3, 4]),(pw16,5,[3, 4, 5, 0]),(pw91,7,[0, 2, 3, 4]),(pw92,5,[4, 1, 0, 5]),(pw61,5,[3, 2, 1, 5]),(pw43,5,[3, 1, 0, 5]),(pw93,4,[0, 1, 5]),(pw46,5,[3, 1, 0, 5]),(pw7,5,[3, 4, 5, 2]),(pw94,5,[4, 1, 2, 0]),(pw95,4,[2, 3, 4]),(pw96,4,[1, 3, 4]),(pw97,4,[0, 3, 4]),(pw98,4,[0, 3, 4]),(pw99,4,[2, 3, 4]),(pw34,5,[4, 2, 1, 5]),(pw100,4,[1, 2, 4]),(pw101,7,[0, 1, 2, 3]),(pw102,4,[1, 2, 3]),(pw31,5,[3, 4, 1, 5]),(pw33,5,[4, 2, 0, 5]),(pw69,5,[3, 2, 0, 5]),(pw103,4,[0, 2, 5]),(pw42,5,[3, 2, 1, 5]),(pw104,4,[0, 1, 2]),(pw105,2,[0, 3, 4]),(pw106,2,[1, 3, 4]),(pw107,1,[2, 4]),(pw108,1,[2, 4]),(pw109,1,[3, 4]),(pw110,1,[3, 4]),(pw111,1,[1, 4]),(pw112,2,[3, 2, 4]),(pw113,2,[3, 1, 4]),(pw114,1,[1, 4]),(pw115,2,[3, 0, 4]),(pw116,2,[2, 3, 4])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=8) ptopB p13_B p13_L (by decide +kernel),mkSlice (w:=32) ptopB p16_B p16_L (by decide +kernel),mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel),mkSlice (w:=4) ptopB p22_B p22_L (by decide +kernel),mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel),mkSlice (w:=16) ptopB p23_B p23_L (by decide +kernel),mkSlice (w:=0) ptopB p24_B p24_L (by decide +kernel),mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel),mkSlice (w:=2) ptopB p22_B p22_L (by decide +kernel),mkSlice (w:=1) ptopB p22_B p22_L (by decide +kernel),mkSlice (w:=8) ptopB p5_B p5_L (by decide +kernel),mkSlice (w:=0) ptopB p25_B p25_L (by decide +kernel),mkSlice (w:=8) ptopB p8_B p8_L (by decide +kernel),mkSlice (w:=6) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=16) ptopB p14_B p14_L (by decide +kernel),mkSlice (w:=3) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=5) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=9) ptopB p9_B p9_L (by decide +kernel),mkSlice (w:=0) ptopB p26_B p26_L (by decide +kernel),mkSlice (w:=8) ptopB p12_B p12_L (by decide +kernel),mkSlice (w:=8) ptopB p8_B p8_L (by decide +kernel),mkSlice (w:=9) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=32) ptopB p5_B p5_L (by decide +kernel),mkSlice (w:=6) ptopB p19_B p19_L (by decide +kernel),mkSlice (w:=32) ptopB p5_B p5_L (by decide +kernel),mkSlice (w:=12) ptopB p9_B p9_L (by decide +kernel),mkSlice (w:=16) ptopB p8_B p8_L (by decide +kernel),mkSlice (w:=4) ptopB p14_B p14_L (by decide +kernel),mkSlice (w:=12) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=16) ptopB p8_B p8_L (by decide +kernel),mkSlice (w:=3) ptopB p19_B p19_L (by decide +kernel),mkSlice (w:=32) ptopB p14_B p14_L (by decide +kernel),mkSlice (w:=33) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=33) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=36) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=34) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=34) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=8) ptopB p8_B p8_L (by decide +kernel),mkSlice (w:=40) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=48) ptopB p7_B p7_L (by decide +kernel),mkSlice (w:=48) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=4) ptopB p18_B p18_L (by decide +kernel),mkSlice (w:=10) ptopB p9_B p9_L (by decide +kernel),mkSlice (w:=2) ptopB p14_B p14_L (by decide +kernel),mkSlice (w:=10) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=1) ptopB p14_B p14_L (by decide +kernel),mkSlice (w:=48) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=0) ptopB p4_B p4_L (by decide +kernel),mkSlice (w:=0) ptopB p4_B p4_L (by decide +kernel),mkSlice (w:=33) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=34) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=4) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=36) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=36) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=3) ptopB p11_B p11_L (by decide +kernel),mkSlice (w:=5) ptopB p11_B p11_L (by decide +kernel),mkSlice (w:=33) ptopB p1_B p1_L (by decide +kernel),mkSlice (w:=6) ptopB p11_B p11_L (by decide +kernel),mkSlice (w:=0) ptopB p4_B p4_L (by decide +kernel),by simp⟩
def ptopC : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(1,[526]),(1,[527]),(3,[]),(4,[]),(5,[]),(6,[]),(1,[524]),(7,[]),(0,[388]),(8,[]),(9,[]),(1,[525]),(0,[389]),(1,[392]),(1,[393]),(1,[395]),(0,[395]),(1,[386]),(1,[384]),(10,[]),(1,[257]),(1,[256]),(1,[258]),(1,[390]),(1,[388]),(0,[385]),(1,[389]),(1,[391]),(0,[387]),(1,[261]),(1,[260]),(1,[262]),(1,[128]),(1,[130]),(1,[129]),(11,[]),(12,[]),(1,[258,532]),(1,[513]),(0,[260]),(1,[256,534]),(1,[520,23]),(13,[]),(10,[260]),(14,[]),(3,[525]),(4,[393]),(6,[389]),(4,[392]),(3,[524]),(6,[388]),(0,[388,389]),(1,[524,525]),(2,[384]),(1,[256,526]),(1,[256,527]),(15,[]),(7,[384]),(1,[524,258]),(5,[524]),(1,[524,256]),(10,[128]),(7,[386]),(1,[524,257]),(1,[258,526]),(1,[258,527]),(5,[258]),(6,[258]),(9,[386]),(2,[386]),(2,[388]),(1,[260,526]),(1,[260,527]),(0,[256]),(7,[388]),(1,[524,263]),(1,[524,262]),(1,[524,260]),(2,[389]),(1,[261,526]),(1,[261,527]),(0,[257]),(1,[261,524]),(8,[389]),(7,[389]),(16,[]),(0,[388,257]),(6,[260]),(5,[520]),(7,[263]),(1,[520,389]),(1,[520,391]),(2,[392]),(3,[519]),(4,[263]),(0,[387,260]),(1,[391,522]),(2,[390]),(1,[524,261]),(1,[262,526]),(1,[262,527]),(7,[390]),(2,[128]),(1,[128,526]),(1,[128,527]),(3,[128]),(4,[128]),(1,[128,524]),(7,[128]),(1,[524,130]),(1,[524,131]),(2,[130]),(1,[524,128]),(1,[524,129]),(1,[130,526]),(1,[130,527]),(3,[130]),(4,[130]),(1,[130,524]),(7,[130]),(2,[256]),(7,[256]),(1,[525,20]),(10,[129]),(17,[]),(7,[520]),(2,[520]),(18,[]),(0,[389,532]),(19,[]),(10,[261]),(2,[393]),(3,[512]),(1,[521,386]),(5,[521]),(1,[521,384]),(8,[512]),(0,[261]),(1,[384,522]),(5,[384]),(8,[386]),(1,[525,257]),(1,[525,256]),(5,[525]),(1,[525,258]),(1,[521,391]),(8,[516]),(3,[516]),(1,[521,390]),(1,[521,388]),(1,[388,522]),(1,[388,523]),(6,[261]),(9,[389]),(1,[261,525]),(1,[525,262]),(0,[389,257]),(1,[525,263]),(8,[519]),(1,[521,389]),(0,[387,261]),(1,[391,523]),(9,[390]),(8,[390]),(1,[525,261]),(1,[525,260]),(8,[128]),(9,[128]),(1,[128,525]),(1,[525,130]),(1,[525,131]),(9,[130]),(1,[525,128]),(1,[525,129]),(8,[130]),(1,[130,525]),(0,[394]),(1,[256,404]),(1,[394,23]),(10,[259]),(3,[384]),(1,[512,392]),(7,[394]),(1,[512,393]),(5,[512]),(1,[512,395]),(9,[512]),(5,[395]),(10,[258]),(2,[258]),(1,[514,392]),(1,[514,393]),(8,[527]),(1,[395,512]),(1,[395,514]),(2,[260]),(1,[516,392]),(1,[516,393]),(1,[516,395]),(3,[388]),(1,[395,519]),(6,[395]),(3,[389]),(1,[517,392]),(1,[517,393]),(0,[129]),(2,[261]),(0,[395,129]),(1,[395,517]),(5,[523]),(1,[523,388]),(0,[262]),(1,[523,389]),(1,[523,391]),(1,[391,520]),(1,[391,521]),(2,[394]),(0,[387,262]),(2,[262]),(1,[518,392]),(1,[518,393]),(0,[130]),(1,[395,516]),(1,[395,518]),(3,[390]),(1,[128,392]),(1,[128,393]),(1,[128,395]),(1,[395,130]),(1,[395,128]),(1,[395,129]),(1,[130,392]),(1,[130,393]),(1,[130,395]),(4,[389]),(1,[517,386]),(1,[517,384]),(1,[384,519]),(1,[512,388]),(4,[384]),(1,[512,389]),(1,[512,391]),(8,[517]),(7,[261]),(1,[389,257]),(1,[389,256]),(3,[517]),(1,[389,258]),(1,[258,391]),(1,[258,388]),(1,[258,389]),(1,[391,256]),(1,[389,20]),(20,[]),(1,[263,23]),(1,[131]),(8,[384]),(4,[393,392]),(14,[389]),(14,[388]),(1,[524,256,525]),(1,[524,525,259]),(1,[524,525,258]),(5,[524,525]),(10,[128,129]),(3,[525,524]),(1,[524,525,257]),(1,[524,525,256]),(8,[388]),(10,[129,128]),(1,[524,260,525]),(1,[524,525,263]),(1,[524,525,262]),(6,[388,389]),(5,[525,524]),(1,[525,261,524]),(4,[392,393]),(3,[524,525]),(0,[388,389,257]),(10,[260,261]),(5,[521,520]),(0,[260,261]),(1,[520,521,389]),(1,[520,521,391]),(2,[392,393]),(14,[261]),(14,[260]),(0,[387,260,261]),(1,[524,525,261]),(1,[524,525,260]),(3,[525,128]),(4,[393,128]),(1,[525,128,524]),(4,[392,128]),(3,[524,128]),(1,[524,525,130]),(1,[524,525,131]),(1,[524,525,128]),(1,[524,525,129]),(3,[130,525]),(4,[130,393]),(1,[130,525,524]),(4,[130,392]),(3,[130,524]),(8,[512,405]),(1,[520,405]),(1,[394,532]),(0,[260,405]),(3,[512,405]),(4,[256]),(21,[]),(22,[128]),(0,[388,279]),(4,[392,21]),(10,[128,275]),(22,[263]),(23,[]),(7,[260]),(4,[260]),(24,[384]),(4,[261]),(10,[260,19]),(3,[517,406]),(1,[389,533]),(1,[389,534]),(9,[524]),(6,[260,407]),(24,[385]),(1,[526,261,24]),(1,[527,261,24]),(7,[389,20]),(25,[]),(1,[524,261,24]),(22,[389,272]),(25,[260]),(5,[526]),(5,[527]),(1,[524,277]),(1,[395,532]),(26,[]),(27,[]),(7,[391]),(22,[390]),(28,[]),(1,[526,263,27]),(22,[390,275]),(1,[527,263,27]),(7,[391,23]),(2,[391,23]),(20,[260]),(22,[]),(1,[262,405]),(1,[262,406]),(10,[131]),(22,[389]),(22,[391]),(29,[]),(1,[524,128,665]),(22,[392]),(30,[]),(1,[128,405]),(1,[128,406]),(1,[128,533]),(1,[128,534]),(0,[388,21]),(31,[]),(18,[524]),(7,[128,535]),(3,[128,279]),(4,[128,535]),(5,[131]),(22,[129,272]),(5,[521,20]),(1,[521,20]),(1,[384,521,24]),(22,[256,392]),(22,[256]),(1,[128,525,24]),(3,[525,20]),(4,[393,20]),(1,[131,525,24]),(22,[129]),(8,[393]),(9,[393]),(1,[525,649]),(3,[525,276]),(32,[]),(1,[394,534]),(33,[]),(10,[129,400]),(5,[525,148]),(1,[521,652]),(1,[521,653]),(10,[261,400]),(0,[261,532]),(5,[521,148]),(8,[523]),(34,[]),(35,[]),(3,[523]),(8,[261]),(22,[385]),(9,[261]),(1,[525,645]),(36,[]),(1,[390,534]),(9,[525,276]),(1,[521]),(1,[521,645]),(6,[261,532]),(8,[262]),(3,[262]),(1,[262,534]),(1,[521,387]),(7,[524]),(4,[524]),(19,[257]),(18,[261]),(19,[387]),(1,[262,525]),(19,[258]),(6,[389,532]),(4,[393,532]),(22,[394]),(22,[260,19]),(9,[384]),(3,[525,22]),(0,[389,278]),(9,[525]),(3,[514]),(4,[258,407]),(0,[261,404]),(22,[129,274]),(10,[261,16]),(37,[]),(8,[514]),(38,[]),(9,[388]),(10,[129,272]),(6,[389,276]),(39,[129]),(8,[389,20]),(9,[389,20]),(1,[525,261,24]),(25,[261]),(1,[525,256,153]),(9,[391]),(8,[391]),(8,[391,23]),(9,[391,23]),(20,[261]),(1,[525,263,27]),(8,[518]),(3,[518]),(40,[]),(39,[129,402]),(9,[128,279]),(19,[389]),(8,[128,279]),(5,[525,131]),(10,[262,17]),(22,[130]),(0,[262,405]),(3,[527]),(1,[392,534]),(1,[526,279]),(10,[130,275]),(10,[262]),(6,[262]),(1,[517,404]),(1,[391,534]),(41,[]),(8,[526]),(9,[517]),(10,[259,147]),(6,[394,151]),(5,[394]),(1,[392,517,24]),(3,[389,20]),(1,[393,517,24]),(22,[385,272]),(14,[395]),(42,[263]),(5,[392]),(1,[395,533]),(1,[395,534]),(5,[393]),(22,[386]),(3,[391]),(43,[]),(44,[]),(1,[392,519,27]),(3,[391,23]),(1,[393,519,27]),(1,[395,519,27]),(22,[386,275]),(12,[263]),(10,[130]),(7,[390,277]),(5,[526,279]),(6,[391]),(19,[395]),(5,[395,131]),(1,[395,131]),(22,[260,403]),(1,[261,405]),(39,[392]),(1,[387,517,24]),(1,[384,512,153]),(1,[384,130,536]),(22,[385,274]),(5,[385]),(7,[258,151]),(39,[387]),(1,[258,405]),(1,[258,406]),(5,[257]),(5,[256]),(1,[258,151]),(45,[]),(5,[131,405]),(46,[]),(1,[128,655]),(10,[386]),(22,[129,128]),(8,[516,405]),(9,[524,149]),(19,[261]),(5,[520,405]),(7,[389,276]),(4,[393,148]),(22,[389,16]),(1,[524,525,280]),(1,[524,394,538]),(7,[263,404]),(19,[388]),(10,[128,129,276]),(1,[525,524,261,28]),(14,[388,389]),(25,[260,261]),(1,[524,525,263,31]),(20,[260,261]),(3,[128,405]),(10,[261,260]),(39,[261,260,405]),(24,[392]),(39,[260,401]),(0,[261,260,25]),(31,[389]),(19,[388,389]),(31,[388]),(39,[128,129]),(3,[525,128,283]),(4,[393,128,539]),(4,[392,128,539]),(3,[524,128,283]),(1,[524,128,280]),(3,[524,130,280]),(1,[524,128,282]),(1,[128,651,526]),(1,[128,651,527]),(22,[392,519]),(39,[395]),(10,[393]),(24,[392,519]),(47,[]),(46,[128]),(10,[128,393]),(48,[]),(22,[260,400]),(39,[128,392]),(1,[128,648,526]),(1,[128,648,527]),(22,[392,516]),(10,[394]),(24,[392,516]),(49,[]),(50,[]),(51,[]),(10,[128,394]),(24,[389,272]),(24,[]),(39,[]),(24,[390,275]),(20,[261,400]),(19,[259]),(22,[392,17]),(24,[392,17]),(1,[525,128,665]),(8,[128,277]),(9,[128,277]),(1,[128,407]),(10,[392,129]),(10,[392,131]),(22,[256,402]),(22,[392,19]),(24,[392,19]),(9,[128,392]),(19,[389,18]),(8,[128,392]),(33,[260]),(52,[]),(9,[128,394]),(1,[128,404]),(1,[128,535]),(19,[387,145]),(19,[129,403]),(1,[128,532]),(9,[394,130]),(9,[394,128]),(13,[128]),(8,[128,394]),(24,[256,400]),(10,[129,402]),(9,[263,23]),(9,[130,276]),(31,[261]),(1,[521,128,408]),(9,[525,130,280]),(1,[521,128,410]),(53,[]),(9,[525,128,283]),(1,[128,655,522]),(1,[128,655,523]),(43,[393]),(46,[261]),(10,[385]),(22,[129,394]),(54,[]),(22,[392,129]),(8,[128,279,786]),(55,[]),(1,[128,652,522]),(10,[386,261]),(1,[128,652,523]),(22,[259,400]),(31,[395]),(1,[395,128,536]),(8,[527,130,280]),(1,[395,128,538]),(1,[128,659,392]),(1,[128,659,393]),(22,[392,515]),(10,[389]),(8,[527,128,283]),(56,[]),(3,[128,279,781]),(10,[258,389]),(46,[258]),(22,[256,400]),(1,[128,656,392]),(22,[392,512]),(1,[128,656,393]),(10,[390]),(3,[128,279,782]),(57,[]),(22,[263,400]),(46,[129]),(46,[128,129]),(1,[524,525,128,284]),(3,[524,525,130,284]),(1,[524,525,128,286]),(10,[129,393]),(3,[524,525,128,287]),(31,[388,389]),(4,[392,393,130,540]),(10,[129,394]),(8,[128,279,782]),(4,[392,393,128,543]),(19,[260,403]),(1,[128,406,520,797]),(31,[260]),(9,[524,130,280]),(31,[262]),(1,[128,263,536]),(1,[128,520,153]),(24,[392,515]),(9,[524,128,283]),(4,[128,535,777]),(19,[260,401]),(22,[128,394]),(22,[128,392]),(24,[392,512]),(4,[128,535,778]),(46,[260]),(24,[392,147]),(24,[392,145]),(19,[261,400]),(1,[128,406,521,798]),(31,[263]),(1,[128,261,537]),(1,[128,521,154]),(3,[128,279,785]),(8,[128,279,785]),(19,[389,274]),(4,[393,130,536]),(4,[393,513]),(4,[393,515]),(4,[393,519,27]),(31,[390]),(1,[128,393,537]),(1,[128,389,537]),(1,[128,525,154]),(9,[128,279,782]),(19,[263,403]),(1,[128,406,522,797]),(9,[526,130,280]),(1,[128,263,538]),(9,[526,128,283]),(34,[260]),(58,[]),(19,[262,401]),(22,[130,394]),(22,[130,392]),(1,[128,393,539]),(35,[260]),(3,[128,279,786]),(46,[262]),(15,[128,271]),(19,[261,260,407]),(1,[521,128,410,520,929]),(31,[260,261]),(9,[524,525,130,284]),(1,[128,521,263,540]),(9,[524,525,128,287]),(21,[128]),(19,[388,389,278]),(31,[389,388]),(4,[393,392,130,540]),(4,[393,392,513]),(4,[393,392,515]),(4,[393,392,519,31]),(1,[128,524,389,541]),(24,[392,516,23])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[(25,24),(26,24),(15,14),(15,13),(28,24),(15,11),(51,50),(26,18),(15,7),(26,10),(25,9),(46,14),(43,11),(51,49),(25,17),(45,13),(53,49),(28,12),(51,35),(51,19),(27,11),(45,44),(53,52),(46,44),(54,52),(43,42),(43,41),(28,20),(15,10),(46,42),(54,50),(46,38),(26,11),(29,13),(25,8),(54,38),(45,41),(30,14),(28,8),(45,37),(53,37),(43,35),(51,3),(30,22),(15,12),(53,21),(25,13),(27,19),(51,34),(51,33),(30,20),(25,11),(15,9),(26,8),(51,48),(15,5),(27,17),(15,6),(26,2),(15,3),(27,3),(28,16),(43,3),(43,10),(43,9),(25,23),(26,6),(26,14),(45,12),(25,33),(15,23)],[],[[],[1],[0,1],[0,1,0],[0],[1,0]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD11 : List StD := [
([pw3,pw2,pw5,pw6,pw40,pw85],[3,0,4,29,45,7,11,1,5,9,13,17,21,33,37,19,23,41,49,77,25,53,57,61,65,69,73,15],[2017,134224545,1056843,148161,262164,105792,6324266,181536,8388628,16850955,33642497,262164,67117067,524302,524308])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD10 : List StD := [
([pw7,pw3,pw2,pw5,pw6,pw40,pw85],[8,36,49,40,3,33,85,93,12,44,1,5,21,57,65,77,81,23,0,16,20,24,28,32,61,69,73,89,97],[257,524289,3149825,393249,12648449,263,25,1089,134217793,1089,7,2184,268435592,2184,14,25136,33771536,16777222,67117616,32774,32774]),
([pw3,pw2,pw22,pw5,pw6,pw40,pw85],[48,8,40,3,52,56,101,105,109,60,9,13,17,25,49,53,69,77,23,0,20,24,28,32,21,33,41,57,61,65,73],[31,4,1106,8274,8274,1106,2,2181,32901,32901,2181,3149825,524553,12648449,41,671351560,84217864,268451872,1107297032,131872,147488]),
([pw8,pw3,pw2,pw5,pw6,pw40,pw85],[8,72,49,20,24,9,17,57,3,64,76,33,41,53,77,89,105,117,0,28,32,40,48,68,37,61,73,85,113,121,15,19],[513,6356993,8388609,1074004097,1576961,519,134217761,268435505,32801,32801,7,131160,11648,2164338944,33554438,536871000,131160,14,67112320,16390,16390]),
([pw86,pw3,pw2,pw5,pw6,pw40,pw85],[8,0,84,49,25,41,109,88,80,5,13,17,21,29,61,89,3,19,23,20,24,28,32,40,48,37,69,77,125,7,11],[2,25166849,1576961,259,6291489,269,32785,32785,19,177,13,1074208256,8258,33751712,16396,8258,604244128,16396,268435522,70,134217740]),
([pw49,pw3,pw2,pw5,pw6,pw40,pw85],[20,100,0,49,41,109,121,88,1,5,33,92,37,65,3,8,28,32,40,48,52,96,9,13,45,61,77,7,11,19],[1081601,786945,2049,2097153,196625,2059,415253248,8257,1060,20880,16777226,8257,1060,536875664,33554442,69,209,11,1060,38,67108874]),
([pw117,pw3,pw2,pw5,pw6,pw40,pw85],[32,88,108,57,8,77,28,104,9,33,37,53,61,65,69,0,20,24,40,48,13,21,85,101,129,3,11,19,23],[64,788481,204801,32779,129,165,4194576,8388880,26,16777297,52,506472448,522,17409,4132,522,17409,4132,11,14,37]),
([pw3,pw2,pw5,pw6,pw40,pw118,pw85],[52,8,32,112,116,1,28,57,25,33,41,49,61,3,19,23,20,24,40,48,5,13,17,21,45,53,65,73,77,81,89,93,117,125,129,133,7,11],[291,1073741859,291,17179869223,5,291,137454731264,68753048200,536872004,2148270081,6160,67150472,34359739460,4295163905,6160,134218444,8589942793,268435608,2,1108,16777233]),
([pw42,pw3,pw2,pw5,pw6,pw40,pw85],[8,32,120,49,28,25,33,124,57,3,7,116,1,13,21,37,61,69,0,20,24,40,48,5,17,53,65,77,89,137,141,11],[2,6299649,1589249,2147745857,2049,2061,4129,268435489,4129,536870947,13,25191936,33556416,163858,65548,67110848,163858,65548,1073742290,134217740,30]),
([pw46,pw3,pw2,pw5,pw6,pw40,pw85],[32,88,136,57,20,77,24,128,1,5,29,117,133,0,8,40,48,52,132,9,13,21,45,61,69,145,149,153,3,7,11],[147713,98817,129,8203,262145,165,1880621824,2099280,1034,16781313,4194340,33556560,1034,67112961,8388644,26,134217745,52,11,14,37]),
([pw3,pw2,pw5,pw119,pw6,pw40,pw85],[32,0,140,73,125,1,5,17,45,3,9,13,21,33,49,141,7,11,8,20,24,40,48,52,144,61,157,161,165,169,15,19,23],[200288,1073813152,8650785,8210,32777,16644,6442588352,6291521,67108882,134217737,33554692,1572993,268435474,32777,16644,16777219,3,517,11,8210,536870925]),
([pw48,pw3,pw2,pw5,pw6,pw40,pw85],[88,28,144,29,45,1,5,9,13,17,21,49,57,3,7,11,0,8,140,148,61,73,109,15,19,23],[131075,3,3,262145,524289,3,57824,8414880,4105,3,2068,50366272,4105,3,1048596,4194313,3,2068,2162691,13,3])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD9 : List StD := [
([pw120,pw3,pw2,pw5,pw6,pw40,pw85],[156,152,168,24,176,40,45,173,180,188,5,17,33,41,49,105,145,8,28,32,52,160,164,172,184,9,121,137],[1179651,6291463,8388615,14,786435,16467,33825,67592,4487,184558336,16464,67108909,166,33825,113,143,67592,88,4231,147,8784]),
([pw7,pw22,pw5,pw6,pw40,pw85],[8,52,1,216,220,53,57,3,13,17,21,33,49,69,77,89,60,192,196,200,204,208,212,41,61,65,73,177,23],[134217731,394241,65569,524577,289,3146246,32774,4202502,32774,33556680,276833920,16781328,67111112,16472,20496]),
([pw7,pw3,pw2,pw92,pw5,pw6,pw40,pw85],[204,224,236,44,240,252,61,228,244,57,65,69,0,20,48,52,212,232,248,256,77,85,93,165,3,23],[130,131074,33554435,8195,4110,6,134,16777238,32771,2097155,14,6,6,16405,4194309,28,20,20,9,265,329729,353,1033,527361,97,8389128,552,1048672]),
([pw49,pw7,pw3,pw2,pw5,pw6,pw40,pw85],[208,260,244,44,49,288,33,256,41,264,1,5,65,81,3,0,8,24,48,52,212,248,252,268,272,276,280,284,77,109],[16387,589825,262147,513,4194305,3145985,533,8388610,16777218,131075,32842,100671490,22,134234146,1057,104,1440,52,2051,74,10370,22,4105,4481,21,536870984,76,268435476]),
([pw7,pw3,pw2,pw121,pw5,pw6,pw40,pw85],[236,212,292,256,308,320,109,21,296,312,181,20,24,44,48,52,300,304,316,185,3,23],[260,65540,2097158,6148,131085,7,261,1048597,32774,133,13,7,5,16403,145,25,19,17,515,8266,262146,1570,73,524291,161,74,104,1058]),
([pw7,pw3,pw2,pw5,pw6,pw40,pw71,pw85],[208,324,340,49,348,212,248,356,1,5,20,180,188,328,352,33,57,65,3,24,28,32,48,52,312,332,336,344,77,161,165,185,23],[8194,33554434,525315,67145730,3149826,4294968323,8206,134479890,259,16642,16642,8388611,14,529,2576,2576,4194321,28,196737,2147614753,33,13,536969440,1074004097,268435468,16777281,76,13]),
([pw42,pw3,pw16,pw2,pw5,pw6,pw40,pw85],[368,364,360,376,49,380,180,384,388,33,105,392,145,372,11,8,20,24,32,48,52,168,188,396,25,77,137,141,3],[4,16387,524291,196610,2114050,8194,8218,1081345,1057,4512,16779808,67108902,56,129,8388865,4196865,262151,73,268436609,1089,1031,25,4416,4358,216,134220294,33554456,30]),
([pw46,pw7,pw3,pw2,pw5,pw6,pw40,pw85],[208,256,400,180,316,57,77,416,404,21,33,3,24,28,40,44,48,52,320,352,408,412,153],[2053,131077,81929,257,32803,262147,337,1048580,2097164,4101,1030,8198,84,2188,517,38,524294,84,649,42,138,152,35,4194307,81,1058,50,82]),
([pw7,pw3,pw2,pw5,pw119,pw6,pw40,pw85],[256,420,440,444,33,49,1,5,3,424,161,28,44,204,208,428,432,436,448,452,17,21,61,73,85,93,165,169],[514,32770,2293762,259,19,2051,550,266,16777282,67,19,67,38,33554568,137,25,137,44,1073153,67108881,8389633,4194340,262145,524289,261,5121,21,134217733]),
([pw48,pw7,pw3,pw2,pw5,pw6,pw40,pw85],[256,248,456,484,189,488,49,88,468,44,460,464,472,476,480,1,5,21,61,73,85,93,109,3],[134,7,3,3,1027,2050,3,260,4100,155652,149,134,332,8388644,1081348,21,7,76,2162720,49,3,104,4194321,3,262216,524803,25,3]),
([pw3,pw2,pw122,pw5,pw6,pw40,pw85],[504,492,500,48,52,188,496,60,89,41,109,101,508,13,77,105,20,24,28,88,152,9,49,61,65,69,73,3,23],[350,275,2322,2323,2323,2097174,194,41032,1224,33385,8268,200736,8,1835553,4214820,285213824,33554977,8404996,201327745,1156,549]),
([pw3,pw2,pw123,pw5,pw6,pw40],[512,516,1,3,48,52,23,56,520,524,5,73,165,88,9,13,65,77,145,20,24,528,25,33,53,57,69],[183,135,16422,4194342,16422,131,33809,16778257,33809,1835336,2241280,141640,8458824,67438664,33561096]),
([pw86,pw3,pw2,pw5,pw27,pw6,pw40,pw85],[536,540,532,496,552,560,41,556,49,109,48,544,13,25,3,11,20,24,40,52,548,564,568,21,29,77,97,121,125],[4,263177,196611,33795,2049,1048645,2321,4233,8388611,524291,8229,8261,273,32906,2097282,680,67109068,4376,8,16777250,134217798,274,16418,4194374,16402,268436004,560,33554516]),
([pw49,pw3,pw2,pw22,pw5,pw6,pw40,pw85],[192,572,504,588,60,288,284,41,180,352,49,109,52,576,65,101,3,8,24,40,48,88,272,276,580,584,33,69,77,105,23],[135169,1572867,1073745923,8193,16777217,33554565,9225,65634,4194370,32865,368,33124,1320,34,536870915,530,646,522,262147,2066,144703494,65546,16401,16517,1033,67110932,2072,268435596]),
([pw117,pw3,pw2,pw5,pw27,pw6,pw40,pw85],[532,536,596,600,608,57,77,48,592,11,20,24,28,40,52,560,604,612,616,620,13,37,69,113,129,177,3],[258,8326,3082,646,32803,65539,338,33554438,8388618,16390,35,16777219,82,524,131076,37,4194309,1048596,262156,41,2097161,88,37,4101,67108884,524321,49,81]),
([pw3,pw2,pw22,pw5,pw6,pw40,pw71,pw85],[192,344,624,628,17,584,3,180,352,636,88,188,109,8,28,40,328,332,632,640,33,49,65,69,77,161,165,185],[70,131078,21,132,132,8197,132,65538,19,258,258,32771,258,19,7170,19458,67,74,4194321,134217761,262145,25,34603552,67109441,16781832,524321,8388648,2097161]),
([pw42,pw3,pw2,pw5,pw27,pw6,pw40,pw85],[548,644,384,592,536,49,13,652,21,33,48,608,3,11,20,24,40,52,88,188,396,560,648,656,25,57,77,97,121,137,141],[2049,66563,49157,9219,2105857,4194305,2089,82,276,131090,16777872,536870929,56,4102,1048578,134217794,67,74,8388614,268435716,261,44,34078850,262147,4106,1073742465,67108904,41]),
([pw46,pw3,pw2,pw22,pw5,pw6,pw40,pw85],[192,504,660,632,664,57,180,77,52,352,668,3,8,24,28,40,48,60,200,408,412,672,101,105,109,153,23],[4357,98321,67109125,1025,131107,2097155,1161,2068,1048580,4194309,70,70,76,524308,8388625,50,530,536,8197,16777222,16390,2060,35,33554435,137,262178,42,138]),
([pw3,pw2,pw22,pw5,pw119,pw6,pw40,pw85],[504,676,680,684,3,101,9,13,17,105,125,161,8,28,40,60,192,196,424,428,432,436,688,692,33,49,61,73,157,165,169,193,197],[22,524294,100,4133,1029,2147483685,100,262146,642,16387,268435459,4294967299,642,3145986,19,19,8195,26,196865,536871937,134219777,100663304,4194305,8388609,25,34817,16777225,1073741833]),
([pw48,pw3,pw2,pw22,pw5,pw6,pw40,pw85],[504,696,584,708,712,29,9,13,101,105,109,3,60,468,472,476,480,700,704,17,49,57,61,73],[7,5,7,5,131073,262145,5,2058,16386,322,35,7,322,8202,648,2097161,5,648,622594,1027,7,2066,1057,5,5242896,8392709,49,5]),
([pw3,pw124,pw2,pw5,pw6,pw40,pw85],[180,716,52,188,724,109,1,45,24,508,540,101,21,41,49,28,40,48,88,720,728,13,61,113,125,145,185,201,205],[1026,2116,8389700,38,2116,2116,197129,524299,6,295433,17041,33558785,134217763,271589385,4194449,290,67113224,17552,16777250,50,8344]),
([pw8,pw3,pw33,pw2,pw5,pw6,pw40,pw85],[732,740,76,752,49,180,57,492,764,9,88,736,756,37,41,53,8,24,48,52,352,744,748,760,17,77,113,117,157,19],[2049,536870915,262147,2097153,1093,4211713,2073,589858,4738,67108993,228,1053344,568,6,131075,38,8397058,26,134217731,32774,41218,26,69,16793857,25,268435524,76,33554456]),
([pw8,pw63,pw3,pw2,pw5,pw6,pw40,pw85],[180,768,236,76,788,764,780,41,48,772,784,33,53,61,85,0,20,24,40,52,760,776,17,29,77,113,7],[67109123,514,262403,2097155,32782,6,518,524291,9,196673,1033,1048737,9233,16451,33570819,14,6,6,4194369,4105,4257,8209,13,5,5,8390664,2072,16777392]),
([pw8,pw3,pw125,pw2,pw5,pw6,pw40,pw85],[764,792,804,57,808,740,780,49,796,13,29,77,24,28,40,48,52,76,352,800,812,816,41,105,113,205,19],[258,67108867,49154,524290,11,8195,390,65539,610,16777234,11,262147,134,1048609,4113,132105,65,2053,8389168,1097,33554529,164,25,4194321,148,2097161,13,2053]),
([pw8,pw3,pw2,pw5,pw6,pw40,pw126,pw85],[780,820,236,836,816,5,760,840,844,48,824,33,53,85,24,40,812,828,832,37,61,73,77,113,157,205,3,15],[1026,33283,131074,262150,6,134218243,1030,8205,8388622,12,12,8205,12,35,4129,33554481,17,4129,6,6,16387,6,2099408,83886209,4196736,65601,524624,1048833]),
([pw42,pw11,pw3,pw2,pw5,pw6,pw40,pw85],[368,848,384,864,49,876,13,852,880,1,29,33,19,8,20,24,32,48,52,124,180,188,856,860,868,872,25,37,65,77,137,141,209],[4099,130,131075,49158,4200450,8388610,154,270337,16777217,33554437,2622465,65539,25,97,548,67109408,1073741858,56,4294967301,1048641,67,25,268436740,134217734,28,2147485954,536870936,26]),
([pw8,pw62,pw3,pw2,pw5,pw6,pw40,pw85],[780,884,236,764,904,57,181,908,844,888,20,24,40,52,76,816,892,896,900,17,113,177,213,7],[8388611,514,4099,65538,131078,6,518,8195,257,3077,16425,262153,337,2097155,1048710,6,6,6,524293,41,4194313,81,140,140,84,32808,56,88]),
([pw8,pw3,pw2,pw5,pw119,pw6,pw40,pw85],[432,816,76,920,420,49,73,165,912,17,3,0,28,52,444,676,740,780,916,924,5,9,33,61,85,105,113,117,157,161,169],[257,33603585,262145,1027,2181,4099,297,18874384,67108881,8210,148,82,56,134218241,1245186,268435588,536870978,8388648,515,133,67,41,524294,6,1034,70,4194316,1073741834]),
([pw48,pw8,pw3,pw2,pw5,pw6,pw40,pw85],[764,456,760,944,57,476,49,88,936,9,76,488,708,928,932,940,17,29,61,73,85,105,113,117],[134,7,5,5,8197,16388,5,258,2103298,32770,147,134,330,1049090,4194850,19,7,74,8454176,131089,5,262216,49,5,104,525317,25,5]),
([pw86,pw3,pw2,pw5,pw6,pw40,pw126,pw85],[88,556,836,188,956,180,49,952,5,21,28,40,52,568,820,948,960,17,61,125,145,217,3,11],[1,2054,49668,133,1029,8388614,212,2097158,548,13,13,4102,84,131362,11,11,1,274,41,41,1048610,112,532481,4194307,25,65539,25,262162]),
([pw42,pw3,pw33,pw2,pw5,pw6,pw40,pw85],[88,368,748,180,976,49,492,21,53,157,188,964,8,48,52,388,732,756,968,972,1,89,97,19],[2052,8388614,8198,327812,517,524292,2100,20490,131394,3145800,585,5,120,3,32906,11,7,50,4194562,259,7,50,1025,5,184,517,1041,5]),
([pw49,pw3,pw2,pw5,pw6,pw40,pw118,pw85],[188,284,88,996,1000,352,5,988,1,49,8,24,28,276,980,984,992,1004,33,45,93,125,23],[1027,49217,129,65537,4109,4194315,657,98,266,7,7,6,274,104,5,5,1048610,112,13,13,2058,536,270337,2097155,5,131075,5,524306]),
([pw42,pw49,pw3,pw2,pw5,pw6,pw40,pw85],[88,288,384,1004,180,188,33,49,5,13,1008,1,24,28,52,260,276,368,572,644,1012,1016,3],[4194310,1026,295426,4102,67,1048579,1162,16390,655620,5,2097157,8197,140,530,2054,67,2051,138,276,49,273,536,37,37,140,65601,73,41]),
([pw3,pw2,pw5,pw127,pw6,pw40,pw85],[88,28,52,420,1,1020,25,188,508,61,125,49,19,23,20,24,40,48,5,13,17,21,45,53,65,77,89,11],[92,67108892,92,92,11,92,138162176,196992,8393729,3,2592,49536,16786433,3,2592,4,3,4195232,1027,33554465,3]),
([pw3,pw2,pw5,pw128,pw6,pw40,pw85],[188,24,88,1024,65,28,17,125,1028,45,33,49,8,40,48,52,1,5,9,13,61,121,157,3,7,11],[59703296,82,36873,1165,36,2816,2097170,24585,4194441,36,1049344,82,82,22,82,2,45,2825,165,1161,36]),
([pw129,pw3,pw2,pw5,pw6,pw40],[88,520,29,140,33,41,101,105,145,3,37,7,11,19,23,8,20,24,40,48,52,144,1032,1,5,9,13,17,21,57,69,15],[1081922,794754,213250,2097162,4194314,25172672,2315258688,21,1057,335573376,536870917,1057,21,1073741857,29])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD8 : List StD := [
([pw7,pw22,pw92,pw5,pw6,pw40,pw85],[1040,240,1036,1052,1068,85,216,236,13,69,1044,1048,57,61,65,89,1056,1060,1064,1,77,165,177],[4194310,259,259,1410,1154,130,37,37,34852,34852,524300,65537,131073,262673,8201,16465,16913,8201,2101328,4168,1049112]),
([pw49,pw7,pw22,pw5,pw6,pw40,pw85],[1072,260,572,1060,1068,1,105,216,41,49,109,1044,1076,65,48,256,1048,1064,1080,33,77,177,205,221],[67,16421,4097,262145,131345,4617,2097158,67,8390722,4196418,586,37,66596,32820,44,8321,8465,521,525456,1160,1048856]),
([pw7,pw22,pw121,pw5,pw6,pw40,pw85],[1088,236,308,1084,1092,89,109,181,192,196,204,216,1096,1100,1104,1,177,185,23],[65548,262149,772,7,7,6,41,1066,41,41,32792,4099,2115,8193,145,67,131075,146,16449,81,145]),
([pw7,pw22,pw5,pw6,pw40,pw71,pw85],[1108,344,348,1112,1068,1116,1120,109,192,256,504,1044,105,3,196,204,208,584,1048,1124,1,13,17,33,49,57,65,69,77,161,165,177,185,221],[2147483654,16644,8589937668,134148,4357,2101260,98306,262786,515,8195,1048586,100663536,4294967393,17,4194408,545783809,1073750033,268435608,33,134217737,16777225]),
([pw42,pw3,pw16,pw27,pw6,pw40,pw85],[1128,1132,384,388,1144,21,33,1148,49,105,1140,20,380,536,1136,1152,1156,1160,5,25,57,77,137,141,209,11],[1,42,2566,33570883,1026,1298,8232,4612,524481,4194435,400,16777228,32873,43,56,1114117,519,262164,8519747,2097233,275]),
([pw46,pw7,pw22,pw5,pw6,pw40,pw85],[1088,400,664,1100,1120,53,1,57,77,1164,48,216,1104,1168,109,153,177],[35,1093,513,2193,8193,777,65542,50,35,35,298,84,16389,69,76,145,32785,280,4225,137,265]),
([pw7,pw22,pw5,pw119,pw6,pw40,pw85],[1088,420,676,1180,1,17,33,161,216,584,700,1116,1120,1172,1176,1184,1188,1192,1196,13,21,49,61,73,89,165,169,177,221,3,23],[134217734,1073154,1073741827,268435459,515,525322,98356,21,16777221,21,28,6177,33554497,8388737,6291464,131073,262145,536870921,385,73,67108873]),
([pw48,pw7,pw22,pw5,pw6,pw40,pw85],[1088,1108,456,708,1216,109,1,216,712,1200,1204,1208,1212,1220,1224,13,17,21,49,57,61,73,177,225],[3,3,3,513,1025,3,4194316,137220,8388613,3,33044,90184,41,3,88,524321,3,1310736,2097283,49,3]),
([pw3,pw2,pw130,pw5,pw6,pw40,pw85],[508,380,180,496,1248,1228,1232,1252,1256,33,28,88,520,1236,1240,1244,21,41,229,233],[35,8259,3,278531,3,3,3,98362,13,12,12,34,13,3073,4161,21,20,20,524929,769,131456]),
([pw131,pw3,pw2,pw5,pw6,pw40,pw85],[208,288,260,1260,180,236,1024,1268,1272,33,105,4,28,88,520,1264,41,77,189],[3,5,3,32778,12432,18448,1031,67,42,34,34,1029,28,20,20,41,193,65,262664,776,196992]),
([pw3,pw2,pw132,pw5,pw6,pw40,pw85],[180,1256,1280,184,1284,1276,29,360,520,1288,9,37,129,229,3],[39,39,51,8202,4106,1539,7,16407,5,5,7,19,73,5,259,17,17,19,200,74,2058]),
([pw133,pw3,pw2,pw5,pw6,pw40,pw85],[180,1292,1296,236,984,20,364,1276,1304,1312,41,73,88,1300,1308,1316,1320,33,77,117],[6,24865,35,4109,3,265,657,643,13,15,9,524307,17,21,17,7,3,3,35908,458756,3140]),
([pw7,pw3,pw2,pw5,pw134,pw6,pw40,pw85],[180,1332,1048,1340,49,256,248,1,188,208,236,352,1324,1336,1344,165,20,88,436,1328,1348,5,61,77,3],[4097,524289,327683,8449,8449,131329,4121,16793603,17025,1157,2181,2177,25,2097667,3,3,3,3,1061,32805,97,25,1,96,5242904,32864,8388636,92]),
([pw135,pw3,pw2,pw5,pw6,pw40,pw85],[236,248,180,1368,1372,13,204,1376,88,188,1352,1356,1360,1364,1380,1384,21,33],[1031,2051,12545,521,7,9,47,93,13,22,13,101,129,35,161,17,65539,17,18,180224,18]),
([pw7,pw3,pw2,pw5,pw128,pw6,pw40,pw85],[1392,236,204,256,1400,248,1388,33,432,1048,1396,1404,1408,17,49,61,85,93,237,3],[65,1025,261,3,3,3,83,524307,65541,3,3,3,2051,131078,18,18,18,19,12,262156,44,8197,4,40,53761,168,137,41]),
([pw136,pw3,pw2,pw5,pw6,pw40,pw85],[180,256,1432,236,1412,53,1436,208,212,416,1416,1420,1424,1428,33],[3089,4099,8213,11,19,29,39,197,11,11,13,161,35,35,517,11,11,13,322,16390,70]),
([pw3,pw2,pw5,pw6,pw137,pw40,pw85],[236,1440,1444,444,256,1448,17,20,24,420,520,1452,1456,1460,1464,1468,33,81,237,241,23],[1048590,37,5,6149,5,519,41,9,24585,9,11,262161,417,81,67,5,557074,65554,5,1027,131090]),
([pw129,pw7,pw3,pw2,pw5,pw6,pw40],[1444,256,1480,1476,33,236,85,93,1472,1,5,57,3,40,88,208,424,428,448,452,520,1484,1488,1492,21,41,69,145],[1048865,105,8364,134254632,262153,524297,65537,131077,23068673,16657,8388611,4101,577,83,515,1156,150,1030,2066,100663298,2067]),
([pw86,pw3,pw2,pw5,pw138,pw40,pw85],[1496,180,188,532,236,41,13,48,21,49,20,52,88,240,540,556,568,968,1500,1504,1508,53,57],[8,8337,132113,145,262185,4718595,32835,16643,2053,45,1049091,2097235,14,62,67,30,62,275,69676,517,45]),
([pw3,pw2,pw122,pw5,pw119,pw40,pw85],[504,676,1512,188,680,1520,89,28,1516,13,109,432,436,496,1252,1524,1528,1532,9,49,61,101,105,245],[86,85,2097236,341,85,262196,3,4194818,8195,11,546,6152,139,139,16424,8487937,9,1572896,131073,1317,45]),
([pw3,pw2,pw123,pw5,pw139,pw6,pw40],[1552,1556,1536,1540,1544,1,520,1548,528,180,1564,57,1560,1568,1572,33,41],[60,180,53,180,564,564,136,11,136,10,10,67,4099,66,66,65,1281,1025,2305,90113,35072]),
([pw140,pw3,pw2,pw5,pw141,pw6,pw40],[1536,528,1600,1596,33,1576,1604,1584,20,48,1580,1588,1592,1608,5,25,41,57,101],[33,545,289,1025,2195,69761,13,69,7,19,294913,24588,3,14,12,3,70,68,22,6,131090]),
([pw3,pw2,pw123,pw5,pw6,pw40,pw142],[1564,528,1612,1616,1620,1628,1,1624,1556,1572,21,33,520,1632,237],[92,216,121,120,120,152,132,261,260,260,132,35,4099,3,8193,16387,1537,1057,2562,2051,3]),
([pw143,pw3,pw2,pw5,pw141,pw6,pw40],[1584,528,1628,57,1652,1656,1,1604,1640,1648,5,20,48,1252,1536,1636,1644,1660],[49217,4353,2305,65537,523,3,84,100,8326,13,69,1072,131090,25,1041,6,41,161,15,7,523]),
([pw86,pw3,pw2,pw5,pw141,pw6,pw40],[1536,528,540,556,1252,1584,41,109,188,5,25,20,48,544,1592,1664,1668,1672,13,17,21,29,125],[32769,69641,133125,19,8195,16481,262153,1048581,19,1027,1121,524,9,138,616,5,2097158,524388,402,274,4194434]),
([pw49,pw3,pw2,pw123,pw5,pw6,pw40],[528,1552,1252,284,572,1024,41,100,180,188,1,5,65,48,52,88,352,512,580,1412,1572,33,109],[540686,139282,35,6,262147,1048646,1048,137,1034,269,268,145,2066,65553,2132,35,545,33285,4099,4166,6291461]),
([pw117,pw3,pw2,pw5,pw141,pw6,pw40],[1584,1536,596,600,57,1628,77,528,1592,5,20,604,1604,1648,1668,1672,37,113,129,177],[256,16389,33801,4289,147,2049,524294,131082,98,19,262403,524,6,21,517,10,25,65545,49,97,8209]),
([pw3,pw2,pw123,pw5,pw6,pw40,pw71],[1552,1676,344,624,1428,1,1604,1568,65,88,180,188,352,628,24,512,528,1412,1572,1680,5,33,49,57,161,165,185,3],[60,8248,57,1080,1080,131097,8196,1048581,4100,4100,32773,16643,526914,2626,4259907,8388867,67109249,129,19136642,167772163,65]),
([pw42,pw3,pw2,pw5,pw141,pw6,pw40],[1536,384,644,1252,1628,13,21,33,188,528,1584,1684,5,25,121,20,48,608,648,1592,1604,1668,1672,97,137,141,11],[131073,2162693,4227075,1049097,67109505,262145,37,67,25,10369,16786433,4102,5,8388644,4132,3,16450,16450,280,280,34081920]),
([pw46,pw3,pw2,pw123,pw5,pw6,pw40],[1252,1552,1604,664,57,1,1436,180,528,1692,5,48,52,136,512,668,1412,1568,1688,1696,145,153,249],[69635,18446,326,32770,275,7,41,8229,35,145,131233,262156,1034,25,1037,1049154,4194325,581,19,2097155,524305]),
([pw3,pw2,pw123,pw5,pw119,pw6,pw40],[1252,528,676,1444,1,5,9,188,684,125,161,432,436,680,688,1552,1700,13,17,73,157,165,3],[29,281,89,89,8729,89,260,131108,37,1048581,37,6146,4194307,131,131,360449,2097665,525313,16385,3,1027]),
([pw48,pw3,pw2,pw123,pw5,pw6,pw40],[1252,528,1704,708,1572,188,1,9,29,52,144,476,480,512,696,700,1412,1700,5,13,57,73,109],[66053,8201,35,131089,32769,3,77,1031,197,16647,149,14,786440,1048585,25,6146,35,35,4194561,17,2097155]),
([pw144,pw3,pw2,pw5,pw6,pw40,pw85],[1604,196,1708,1712,1384,1252,1720,29,85,37,4,28,88,188,528,1036,1336,1564,1716,9,13,41,57,165,245],[14,6,10,262152,14369,17409,269,270,204,796,524301,19,4194369,2097201,1212417,16777314,65554,22,8388848,193,561]),
([pw145,pw3,pw2,pw5,pw6,pw40,pw85],[1724,1728,352,1736,1744,1740,1748,236,1752,5,33,4,28,88,528,1732,1756,25,41,57,77,249],[3,32769,3,42,12308,18468,69,67,131081,81,65,518,268,788,292,138,146,130,525320,2098216,1376272]),
([pw146,pw3,pw2,pw5,pw6,pw40,pw85],[504,196,1760,1084,109,1604,89,1252,41,4,200,236,528,1564,9,13,61,185,209],[6,10,6,2193,5,4736,76,70,21,69,16420,262154,25,265,41000,19,131075,65570,1041,49,289]),
([pw3,pw2,pw147,pw5,pw6,pw40,pw85],[192,344,180,624,17,1764,352,109,188,584,65,69,161,4,24,88,528,1768,1772,77,185,3],[2097162,9,25,12,12,12,3,19,66,66,66,3,33156,16646,73732,1041,1048625,1041,137888,786592,6688]),
([pw3,pw2,pw22,pw5,pw134,pw6,pw40,pw85],[1776,1044,1176,192,1780,17,504,1784,180,352,188,584,1336,1788,165,3,88,580,1324,1328,1792,49,61,77],[32785,524305,60,274,274,272,272,262145,45,515,515,513,513,45,5123,5123,66563,32897,131118,16430,101,172,8,1056836,6299778,18496,8388802,2240]),
([pw3,pw2,pw148,pw5,pw6,pw40,pw85],[1384,196,1796,1800,584,85,1564,29,1372,4,528,9,13,57,153],[44,38,38,133,53,2148,10,11,8201,25,4168,6,385,21,1601,259,16403,3,385,193,17]),
([pw3,pw2,pw22,pw5,pw128,pw6,pw40,pw85],[504,1804,196,584,1808,1816,1812,9,13,125,180,188,3,352,432,1024,1044,1388,1396,17,33,49,61,157],[4114,262162,148,1232,529,153,176,131074,262,8514,8388611,11,290,16390,34882,2051,11,4130,5,517,13,524324,4,1097,6357088,521,1048609,9]),
([pw149,pw3,pw2,pw5,pw6,pw40,pw85],[532,1368,1724,1820,1824,352,236,620,1828,5,33,137],[12,12,20,35,9,34,14,22,7,2053,6,536,41,41,40,81,19,80,131,1281,3]),
([pw150,pw3,pw2,pw5,pw6,pw40,pw85],[504,680,676,109,1832,1,1252,5,165,69,73,4,20,24,352,528,708,9,13,21,49,61,253,257,3],[3,5,28736,65603,3,34880,38,131106,11,35,4194354,262276,13,133,8388756,265,1537,20447248,267,281,1537]),
([pw129,pw3,pw2,pw22,pw5,pw6,pw40],[1836,1840,504,1844,1848,29,37,101,105,180,700,1472,109,3,196,352,424,428,528,688,692,1484,1488,1492,9,13,17,41,57,69,145,23],[643,33034,272387,3221242370,525330,1049618,8201,131073,16777345,37,209,65545,33554696,268435468,134218008,73400321,6147,8388613,4132,536870980,119]),
([pw3,pw151,pw2,pw5,pw6,pw40,pw85],[1252,180,1856,540,1852,352,236,496,1860,29,41,165,209,233],[24,39,15,122,83,7,39,14,40,83,7,4234,163,179,166,73,89,76,10513,517,1045]),
([pw152,pw3,pw2,pw5,pw6,pw40,pw85],[352,180,1864,1024,1272,57,192,208,572,1868,1872,1876,33,41,77,177],[133,69,1541,3,3,3,33041,29,3,3,3,13,3,3,3,44,12,28,4136,56,26640]),
([pw3,pw153,pw2,pw5,pw6,pw40,pw85],[180,1856,600,1604,1280,236,1880,57,384,1884,37,209],[261,27,15,97,101,43,19,7,9,13,35,2069,17,17,19,12,12,38,704,194,1090]),
([pw3,pw154,pw2,pw5,pw6,pw40,pw85],[180,1904,948,1908,1604,1896,53,57,20,236,1888,1900,1916,37,88,1892,1912,5,73,77,113,205],[34049,2083,1048583,3,3,3,2083,261,16897,3,1537,37,201,2097225,131153,5,5,5,340104,524440,12312]),
([pw8,pw3,pw2,pw5,pw155,pw6,pw40,pw85],[236,1924,1932,764,780,760,5,1920,157,48,180,444,1928,1936,1940,49,61,77,85,113],[130,2578,4098,3,3,3,131,262165,524295,5,5,5,1029,82,8,280,90,84,3,3,3,3,16,40,122884,296,131084,44]),
([pw156,pw3,pw2,pw5,pw6,pw40,pw85],[236,352,760,1960,88,1564,1964,1968,188,1368,1944,1948,1952,1956,1972,33,113],[1029,6161,8197,259,21,3,41,65609,9,13,521,97,3,7,3,3,7,3,132,49160,140]),
([pw8,pw3,pw2,pw5,pw157,pw6,pw40,pw85],[352,1980,764,760,1988,49,9,188,1992,5,156,740,1976,1996,165,40,88,236,676,1936,1984,33,61,113,221],[4098,294915,1048578,1154,1154,65674,4146,2113,8388867,321,257,73,81,2563,517,16777733,13,49,663554,16390,14,50,1,12,4202544,16396,2097172,56]),
([pw158,pw3,pw2,pw5,pw6,pw40,pw85],[352,2000,664,1436,180,1432,2004,1864,2008,2012,33,41,177],[66,6,260,19,6,17,4197,169,19,19,17,205,71,7,69,11,2051,41,522,1058,42]),
([pw3,pw2,pw5,pw6,pw159,pw40,pw85],[236,1444,432,764,1564,41,57,40,48,420,528,1452,1456,13,113],[19,16391,3,6147,3,515,21,73,401,41,8195,5,13,5,7,3,106,74,3,1027,42]),
([pw129,pw8,pw3,pw2,pw5,pw6,pw40],[1444,1484,2016,764,2020,57,85,236,41,117,528,1472,105,88,740,912,916,924,1480,1492,1844,2024,9,17,33,37,113,3],[3201,197,134238340,646,131093,2097157,32769,1314817,65539,3105,532497,4194369,67108931,105,337,8389122,16777256,33554696,42,786,317]),
([pw160,pw3,pw2,pw5,pw6,pw40,pw85],[236,764,2028,188,1564,1,2036,720,1336,40,48,276,528,1712,2032,13,165,177],[135,1537,16387,2051,7,4229,131125,8231,14,39,117,273,11,11,32785,11,11,325,65602,26,30]),
([pw86,pw3,pw2,pw5,pw155,pw40,pw85],[1932,188,88,556,180,236,21,49,48,2040,5,28,52,444,1924,2044,2048,17,217],[513,8457,16481,289,2053,643,262153,81,4099,7,145,132120,12,14,1033,114,102,113,98310,131,7]),
([pw161,pw3,pw2,pw5,pw6,pw40,pw85],[504,1960,568,188,180,496,1968,236,1252,20,24,528,1368,21,49],[7,3,1688,141,5,2058,35,258,11,7,4354,112,9,5,98,9,5,24594,69,11,7]),
([pw3,pw162,pw2,pw5,pw6,pw40,pw85],[188,256,2052,236,1748,2060,2056,2064,180,1752,1904,5,17,1888,33],[8261,1838,1052,7,7,28,35,25,77,67,17,6696,3,35,2476,3,3,4236,16529,7,3]),
([pw163,pw3,pw2,pw5,pw6,pw40,pw85],[180,1252,1272,276,188,1412,728,1024,2076,40,48,384,528,2068,2072,2080,2084,2088,13],[24609,1537,297,32801,65801,4133,7,7,83,73,7,2177,19,11,262149,19,11,133,131082,22,14]),
([pw129,pw3,pw164,pw2,pw5,pw6,pw40],[1472,528,1444,1252,1456,2096,85,2092,5,17,101,88,1480,1484,1488,1836,1844,13,21,29,3,11,19,23],[7,4,3,3,150,7,2,1100,1100,7,33004,69889,25089,524307,2073,16122624,3,40,3,40,3]),
([pw129,pw165,pw3,pw2,pw5,pw6,pw40],[1444,528,1472,2096,2100,2104,13,21,85,101,88,1480,1484,1488,1704,1844,5,17,33,3,11,19,23],[17,7,6,6,16387,3,3,34881,12417,262163,1041,769,769,7,41,8061120,6,40,6,40,7])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD7 : List StD := [
([pw3,pw132,pw27,pw6,pw40,pw85],[2108,1128,2112,180,1280,29,1288,1968,2116,2120,2124,5,9,37,57,129,209,229],[17,261,131075,32787,4169,65549,42,18,521,16390,1030,2053,162,35,8195]),
([pw7,pw147,pw5,pw6,pw40,pw85],[180,2128,2136,2156,256,584,1048,1064,1764,65,69,109,192,1044,1772,2132,2140,2144,2148,2152,13,17,57,77,161,177,185,221],[33554467,36867,134226178,290,1064966,196625,2129,262225,524293,4194825,67109385,2097157,16778376,8390668,1164]),
([pw7,pw22,pw5,pw134,pw6,pw40,pw85],[180,1068,1108,2160,1044,1048,1348,1788,165,192,208,256,504,1176,1184,1332,1784,2164,2168,1,13,17,49,61,77,177],[33554433,41473,145,145,4117,1114121,17409,97,97,2053,524297,2,259,7,2097161,1,6,12976136,262,16777226,14]),
([pw7,pw22,pw5,pw128,pw6,pw40,pw85],[236,1068,1400,1804,2172,1064,1048,1408,1788,33,196,204,256,1172,1188,2164,2176,1,17,49,61,177,237],[2097164,9476,5,261,5,5,18441,200,200,4168,131096,3,4194307,35,262161,1,34,1671184,546,530,50]),
([pw3,pw27,pw6,pw166,pw40,pw85],[2184,180,2192,2180,1,1536,1724,2120,2188,2196,2200,5,33,209,229,261,265,269],[26,16403,114,19,278,32777,8203,521,2060,7,66569,4101,7,134,131077]),
([pw129,pw7,pw22,pw5,pw6,pw40],[1444,2208,1836,2216,1068,109,236,1840,2204,2212,1,69,256,504,1120,1192,1196,1772,2152,2220,2224,2228,2232,17,21,41,57,145,177,221,273,3],[449,1074004486,2281717826,32779,65539,268435461,18350081,536871297,139273,14681092,550,5132,67108912,33556496,2107]),
([pw129,pw7,pw3,pw2,pw5,pw167,pw6,pw40],[2212,2152,2272,2256,2268,1472,2232,528,1444,2244,2276,2280,2284,1484,1488,2236,2240,2248,2252,2260,2264,3,23],[160,3,3,3,32768,66048,3,131072,262144,24576,4194592,160,1572872,2097176,76,261,3,3080,4176,4113,3,3088,2,3,68,518,5,3]),
([pw129,pw7,pw3,pw2,pw168,pw5,pw6,pw40],[2212,2152,2304,2288,2312,1472,2324,528,1444,2236,2244,2316,2320,1484,1488,1836,1844,2036,2228,2292,2296,2300,2308,2328,3,23],[168,11,3,1024,3,524808,11,1048576,2097152,33554720,24580,160,4325380,16777236,33025,2052,3,2052,65553,4112,3,4112,2,576,1089,3,8650816,3]),
([pw3,pw2,pw123,pw5,pw134,pw6,pw40],[2204,1676,1552,1344,1,1776,1780,2332,1568,1784,1772,180,352,1336,1472,5,165,436,1412,2336,2340],[760,664,92,262233,2137,2128,520,32932,557217,4257,4128,131078,24579,24579,1048834,7,65543,1796,4,1283,66818]),
([pw3,pw2,pw123,pw5,pw128,pw6,pw40],[1568,1392,1700,1772,1804,1808,1,2344,1816,2348,2352,9,125,1472,13,432,1024,2336,157],[498,450,2150,2146,4131,2146,258,16404,148112,262289,25,33796,75264,9217,9,5,4101,13,4,521,4105]),
([pw3,pw2,pw5,pw6,pw169,pw40],[1564,1568,2356,2360,2368,2372,1628,2364,1,1556,2340,20,528,1024,17,237,277],[444,357,356,164,356,537,536,152,536,32771,10305,16387,1027,69762,1027]),
([pw150,pw3,pw2,pw170,pw5,pw6,pw40,pw85],[2380,2392,2396,2404,2416,2400,2408,2412,528,1600,1968,1992,2376,680,1024,1304,1412,1832,2324,2384,2388,2420],[528385,65537,1792,16896,1050625,34817,4352,7,8194,34,35,35,12,1028,68,69,69,10,2,145,25,2097152,145,145,10,131082,262147,11]),
([pw150,pw171,pw3,pw2,pw5,pw6,pw40,pw85],[2392,2404,2448,2412,2452,1564,528,2396,20,1832,2324,2376,2400,2424,2428,2432,2436,2440,2444,2456],[96,10272,245760,288,262148,96,96,7,10,1,24,10,4096,5,5,5,5,22,524424,146,144,3,26,24,3,518,1025,3]),
([pw3,pw2,pw172,pw5,pw6,pw40],[2464,1472,1836,2460,1844,273,1840,2096,2468,20,1024,1564,1968,2472,13,101,105,281],[60,100,32804,7,165,90,81944,11,153,3586,8451,259,3,129,135239]),
([pw129,pw3,pw164,pw2,pw5,pw27,pw6,pw40],[2476,2120,2492,2496,2320,2324,1844,2488,2512,1444,1484,1488,2192,2480,2484,2500,2504,2508,2516,3,11],[3,8192,3,3,3,16512,3,2,12,24,520,3,12,4161,3073,524353,162,33,1048596,32768,3,48,65536,3,131332,3,262404,3]),
([pw129,pw165,pw3,pw2,pw5,pw27,pw6,pw40],[2512,2120,2480,2524,2528,2544,1844,2520,2532,2536,11,1484,1488,1836,2192,2476,2488,2540,2548],[65536,3,3,3,3,132,134,2,16449,6145,1089,12,12,784,24,8464,3,25,1544,131072,3,33,262144,3,33,3,33,32774]),
([pw129,pw8,pw3,pw2,pw173,pw5,pw6,pw40],[2556,2016,2552,2580,2592,2596,1472,2588,528,1444,2560,2568,2600,1488,1836,1844,2096,2192,2324,2564,2572,2576,2584,2604,113,11],[324,7,3,1024,3,526340,7,1048576,163840,33555008,2097152,320,4259848,152,16897,16777256,3,24,2,176,3,8392832,8225,264194,5121,3,48,3]),
([pw129,pw8,pw3,pw174,pw2,pw5,pw6,pw40],[2604,2016,2324,2592,2096,2608,2560,2616,2628,2632,528,1444,2568,1488,1836,1844,2192,2612,2620,2624,113,19],[1072,35,4096,3,3,100,98,131072,2099216,98432,262144,1040,524308,18433,136,1048960,3,13,2,8449,518,4612,264,3,517,3,13,74])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD6 : List StD := [
([pw129,pw7,pw22,pw5,pw167,pw6,pw40],[2208,2656,2276,2284,2640,2256,2636,2644,1840,2152,2648,2220,2224,2228,2232,2280,2652,2660,2664,2668,177,23],[336,516,129,1024,65602,67,1048576,6176,2097200,272,131120,24576,12,516,32772,1,129,262280,11,1034,524291]),
([pw129,pw7,pw22,pw168,pw5,pw6,pw40],[2208,2632,2648,2276,2640,2288,2644,1840,2152,1844,2224,2228,2232,2328,2656,2668,2672,2676,2680,2684,177,3],[176,264,16384,65,65572,37,1048576,18,1026,144,131088,2097672,268288,264,8200,1,6,6,65,524354,32773]),
([pw129,pw175,pw3,pw2,pw5,pw6,pw40],[2688,2696,2284,2692,1472,1488,2632,2716,2720,88,2700,2704,2708,2712,2724,3],[48,11,3,3,1032,9,33,2050,48,17,12800,388,16704,3,260,32901,3,192,3,68,11]),
([pw129,pw3,pw2,pw176,pw5,pw6,pw40],[2696,2728,2740,2632,2736,2744,2524,2592,2732,2748],[3,3,3,3,272,3,28,6,56,3,656,5,70,3,12,33,3,12,3,40,3]),
([pw129,pw177,pw3,pw2,pw5,pw6,pw40],[2760,2476,2284,2764,2496,2752,2780,1444,2272,88,2484,2512,2756,2768,2772,2776,2784],[4256,11,3,3,1032,9,129,8226,34,3,49664,20,336,3,20,69,3,67840,3,68,11]),
([pw129,pw178,pw3,pw2,pw5,pw6,pw40],[2788,2204,1472,2224,2392,2680,2824,2324,2632,88,2356,2536,2792,2796,2800,2804,2808,2812,2816,2820,3],[1044,3,3,3,61440,3,65554,20,131073,5,786944,1048673,328,3,192,2088,3,160,3,264,3]),
([pw129,pw179,pw3,pw2,pw5,pw6,pw40],[2828,2768,1472,2324,2832,1488,2284,2844,2784,88,2496,2724,2836,2840,2848,2852],[36,19,3,3,4112,17,33,1030,36,5,8712,192,18560,3,136,33088,3,264,3,72,19]),
([pw129,pw3,pw180,pw2,pw5,pw6,pw40],[2704,2856,2740,2872,2864,2876,1856,2524,2860,2868,2880,2884],[67,3,3,3,272,67,514,28,56,3,3088,5,33,3,12,164,3,12,3,40,3])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD5 : List StD := [
([pw129,pw175,pw3,pw27,pw6,pw40],[2888,2896,2284,2892,2476,1488,2716,2720,2748,2900,2904,2908,2912],[48,11,3,520,9,33,22,17,1092,132,3,2052,3,4352,11]),
([pw129,pw178,pw7,pw5,pw6,pw40],[2916,2632,2920,2204,2212,1836,2788,2884,256,2224,2640,2924,2928,2932,2936,2940,2944],[48,72,5,30720,5,26,33,17,33026,514,72,66688,5,130,5])]
def ptopD4 : List StD := []
theorem ptopI4 : LevelN true ptopT 4 ptopD4 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC5x0 : levelOK true ptopT ptopt 4 (ptopD4.map Prod.fst) ((ptopD5.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI5 : LevelN true ptopT 5 ptopD5 := levelStep ptopB ptopW ptopI4 (chunks 32 ptopD5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC5x0
  ))
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
theorem ptopI8 : LevelN true ptopT 8 ptopD8 := levelStep ptopB ptopW ptopI7 (chunks 32 ptopD8 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC8x0
  · exact ptopC8x1
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

end PEqualNP.Outside.L_meta_12108

theorem PEqualNP.Outside.L_meta_12108 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676608 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676608 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  exact PEqualNP.Outside.L_meta_12108.replaceShort s h
