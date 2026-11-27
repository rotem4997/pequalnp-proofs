import PEqualNP.Defs

-- The live-set and restriction lemmas follow L-meta-10554, L-meta-10802, L-meta-1674, L-meta-670 and L-meta-1667.
namespace PEqualNP.Outside.L_meta_12064
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


def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4269860864 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[
    ⟨.and, [0, 1]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.and, [9, 4]⟩,
    ⟨.or, [9, 4]⟩,
    ⟨.and, [8, 11]⟩,
    ⟨.and, [12, 5]⟩,
    ⟨.or, [6, 13]⟩,
    ⟨.or, [12, 5]⟩,
    ⟨.and, [14, 3]⟩,
    ⟨.or, [16, 10]⟩,
    ⟨.and, [17, 15]⟩], 18⟩
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
def pw6 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
def pw7 : Nat := 0x11111111111111111111111111111111
def pw8 : Nat := 0x22222222222222222222222222222222
def pw9 : Nat := 0x44444444444444444444444444444444
def pw10 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa
def pw11 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
def pw12 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc
def pw13 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def pw14 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def pw15 : Nat := 0xffccffccffccffccffccffccffccffcc
def pw16 : Nat := 0xfefefefefefefefefefefefefefefefe
def pw17 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee
def pw18 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def pw19 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def pw20 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe
def pw21 : Nat := 0x88888888888888888888888888888888
def pw22 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def pw23 : Nat := 0x30303030303030303030303030303030
def pw24 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def pw25 : Nat := 0x80808080808080808080808080808080
def pw26 : Nat := 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa
def pw27 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def pw28 : Nat := 0x2aaa2aaa2aaa2aaa2aaa2aaa2aaa2aaa
def pw29 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
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
def pw40 : Nat := 0xffff0000ffff0000ffff0000ffff
def pw41 : Nat := 0xffff0000ffff0000ffff0000ffff0000
def pw42 : Nat := 0xff000000ff000000ff000000ff000000
def pw43 : Nat := 0xf000f000f000f000f000f000f000f000
def pw44 : Nat := 0x50005000500050005000500050005000
def pw45 : Nat := 0x8080808080808080808080808080808
def pw46 : Nat := 0x880088008800880088008800880088
def pw47 : Nat := 0x22002200220022002200220022002200
def pw48 : Nat := 0x33330000333300003333000033330000
def pw49 : Nat := 0x55550000555500005555000055550000
def pw50 : Nat := 0xf0000000f0000000f0000000f0000000
def pw51 : Nat := 0xf0f00000f0f00000f0f00000f0f00000
def pw52 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
def pw53 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00
def pw54 : Nat := 0x33000000330000003300000033000000
def pw55 : Nat := 0x55000000550000005500000055000000
def pw56 : Nat := 0xf0000000f0000000f0000000f000000
def pw57 : Nat := 0x40404040404040404040404040404040
def pw58 : Nat := 0x8888000088880000888800008888
def pw59 : Nat := 0xa000a000a000a000a000a000a000a0
def pw60 : Nat := 0x44004400440044004400440044004400
def pw61 : Nat := 0xcc000000cc000000cc000000cc000000
def pw62 : Nat := 0xc0c00000c0c00000c0c00000c0c00000
def pw63 : Nat := 0xc000c000c000c000c000c000c000c000
def pw64 : Nat := 0xff000000ff000000ff000000ff0000
def pw65 : Nat := 0xff000000ff000000ff000000ff00
def pw66 : Nat := 0x44440000444400004444000044440000
def pw67 : Nat := 0xc0c00000c0c00000c0c00000c0c0
def pw68 : Nat := 0xa0a00000a0a00000a0a00000a0a0000
def pw69 : Nat := 0xaa000000aa000000aa000000aa00
def pw70 : Nat := 0xc000c000c000c000c000c000c000c0
def pw71 : Nat := 0xa0a00000a0a00000a0a00000a0a0
def pw72 : Nat := 0xcccc0000cccc0000cccc0000cccc0000
def pw73 : Nat := 0xf0000000f0000000f0000000f00000
def pw74 : Nat := 0xcc000000cc000000cc000000cc00
def pw75 : Nat := 0xc000c000c000c000c000c000c000c00
def pw76 : Nat := 0x30300000303000003030000030300000
def pw77 : Nat := 0xa000a000a000a000a000a000a000a00
def pw78 : Nat := 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa
def pw79 : Nat := 0x80008000800080008000800080008000
def pw80 : Nat := 0xaaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa
def pw81 : Nat := 0x88008800880088008800880088008800
def pw82 : Nat := 0x8080aaaa8080aaaa8080aaaa8080aaaa
def pw83 : Nat := 0x888888008888880088888800888888
def pw84 : Nat := 0x2aaaaaaa2aaaaaaa2aaaaaaa2aaaaaaa
def pw85 : Nat := 0xa000a000a000a000a000a000a000a000
def pw86 : Nat := 0xa0000000a0000000a0000000a0000000
def pw87 : Nat := 0x80000000800000008000000080000000
def pw88 : Nat := 0xffff8000ffff8000ffff8000ffff8000
def pw89 : Nat := 0xc0000000c0000000c0000000c0000000
def pw90 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000
def pw91 : Nat := 0x8888888088888880888888808888888
def pw92 : Nat := 0x8000aaaa8000aaaa8000aaaa8000aaaa
def pw93 : Nat := 0xaa000000aa000000aa000000aa000000
def pw94 : Nat := 0x80008888800088888000888880008888
def pw95 : Nat := 0x888aaaa0888aaaa0888aaaa0888aaaa
def pw96 : Nat := 0x2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a
def pw97 : Nat := 0xc0ccccc0c0ccccc0c0ccccc0c0ccccc
def pw98 : Nat := 0xeccccccceccccccceccccccceccccccc
def pw99 : Nat := 0x28a8a8a828a8a8a828a8a8a828a8a8a8
def pw100 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc00
def pw101 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0
def pw102 : Nat := 0xfcccf000fcccf000fcccf000fcccf000
def pw103 : Nat := 0xffffffff00000000ffffffff
def pw104 : Nat := 0xffffffff00000000ffffffff00000000
def pw105 : Nat := 0xaaaaaaaa00000000aaaaaaaa
def pw106 : Nat := 0xc0c0c0c000000000c0c0c0c0
def pw107 : Nat := 0xeaeac0c0eaeac0c0eaeac0c0eaeac0c0
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
def p4_T : Nat := 0xfefefefefefefefefefefefefefefefe
def p4_R : List Nat := [0, 1, 2]
def p4_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
theorem p4_L : LowN true p4_R p4_T 2 := lowCount p4_B (by decide +kernel)
def p5_T : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def p5_R : List Nat := [0, 1, 2, 3]
def p5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
def p5_Z : List SliceD := [(pw1,4,[1, 2, 3]),(pw0,4,[0, 2, 3]),(pw4,4,[0, 1, 3]),(pw6,4,[0, 1, 2]),(pw7,1,[2, 3]),(pw8,1,[2, 3]),(pw9,1,[2, 3]),(pw3,2,[1, 2, 3]),(pw2,2,[0, 2, 3]),(pw5,2,[0, 1, 3]),(pw10,1,[1, 2]),(pw11,2,[0, 1, 2]),(pw12,1,[0, 2])]
theorem p5_Y : ∀ s ∈ p5_Z, SliceN true p5_R p5_T s := by
  unfold p5_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p5_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p5_B p2_B p2_L (by decide +kernel),mkSlice (w:=2) p5_B p2_B p2_L (by decide +kernel),mkSlice (w:=1) p5_B p4_B p4_L (by decide +kernel),mkSlice (w:=2) p5_B p4_B p4_L (by decide +kernel),mkSlice (w:=4) p5_B p4_B p4_L (by decide +kernel),mkSlice (w:=1) p5_B p2_B p2_L (by decide +kernel),mkSlice (w:=8) p5_B p4_B p4_L (by decide +kernel),mkSlice (w:=2) p5_B p2_B p2_L (by decide +kernel),by simp⟩
def p5_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(2,[129]),(3,[129]),(4,[]),(0,[257]),(1,[257]),(5,[]),(1,[259]),(6,[]),(0,[259]),(2,[261]),(2,[257]),(0,[129]),(1,[129]),(1,[131]),(7,[]),(0,[131]),(8,[]),(0,[130]),(9,[]),(10,[]),(0,[258]),(11,[]),(12,[]),(0,[257,261]),(8,[261]),(0,[129,261]),(0,[129,257]),(0,[261,385]),(3,[263]),(1,[262,13]),(1,[131,270]),(0,[262,13]),(0,[131,270]),(0,[258,141]),(0,[130,270]),(0,[260]),(0,[129,270]),(1,[129,270])]
def p5_t : Tabs := (p5_C.map (mkCut true p5_Z),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(6,4),(6,2),(10,8),(10,2),(12,8),(12,4),(7,8)],[],[[],[1],[2,1],[0,1],[0,2,1],[1,0,2,1],[0,1,2],[0,1,2,1],[1,2],[1,2,1],[2],[1,0]])
theorem p5_W : TabsP true p5_R p5_T p5_t := ⟨cutsGood p5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D6 : List StD := [
([pw3,pw2,pw5,pw11],[0,4,8,12,1,9,5,13,17,21,25,29,33,37,41,45,3,7,11,15,19,23],[65651,131285,262937,527398,1060906,2146444])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D5 : List StD := [
([pw3,pw2,pw13,pw5,pw11],[0,4,16,20,13,24,21,41,45,3,43,8,12,29,37,27,31,35,39],[3,2,32789,65609,1,139270,278538,3764,5992,404])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D4 : List StD := [
([pw3,pw2,pw5,pw14,pw15],[28,32,36,44,40,48,52,56,13,29,47],[1027,5,16,7,10,11,32,580,392,3]),
([pw3,pw2,pw5,pw16,pw11],[16,60,64,72,12,68,76,80,84,88,3],[7,7,32,10,7,64,132,256,513,1048]),
([pw17,pw3,pw2,pw5,pw11],[92,24,100,0,4,8,20,28,96,104],[24,24,35,128,257,3,70,514,5,5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D3 : List StD := [
([pw3,pw18,pw15,pw19],[112,4,12,1,108,116,120,124,128,5,49],[1041,41,584,388,7,3]),
([pw20,pw3,pw2,pw5],[132,160,72,0,80,136,140,144,148,152,156,164],[41,193,1793,6,6,2066])]
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
def p6_T : Nat := 0x80808080808080808080808080808080
def p6_R : List Nat := [0, 1, 2]
def p6_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
theorem p6_L : LowN true p6_R p6_T 2 := lowCount p6_B (by decide +kernel)
def p7_T : Nat := 0xe880e880e880e880e880e880e880e880
def p7_R : List Nat := [0, 1, 2, 3]
def p7_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
def p7_Z : List SliceD := [(pw3,4,[1, 2, 3]),(pw2,4,[0, 2, 3]),(pw5,4,[0, 1, 3]),(pw11,4,[0, 1, 2]),(pw1,2,[1, 2, 3]),(pw21,1,[2, 3]),(pw0,2,[0, 2, 3]),(pw4,2,[0, 1, 3]),(pw22,1,[1, 3]),(pw10,1,[1, 2]),(pw23,1,[0, 3]),(pw24,1,[0, 3])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN true p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=2) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=4) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=8) p7_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=3) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=1) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=2) p7_B p1_B p1_L (by decide +kernel),by simp⟩
def p7_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(2,[128]),(3,[128]),(2,[130]),(0,[130]),(0,[131]),(0,[128]),(1,[128]),(6,[]),(7,[]),(2,[256]),(8,[]),(0,[260]),(2,[258]),(9,[]),(3,[258]),(3,[256]),(10,[]),(11,[]),(2,[128,270]),(2,[258,143]),(3,[130,268]),(3,[130,271]),(2,[130,268]),(2,[130,271]),(3,[260,15]),(2,[260,15]),(1,[260,15]),(6,[128]),(3,[256,260]),(4,[128]),(3,[128,260]),(3,[128,256])]
def p7_t : Tabs := (p7_C.map (mkCut true p7_Z),[(13,12),(14,12),(7,5),(11,10),(14,10),(7,6),(14,6),(11,9),(13,9),(13,5),(7,3),(11,3),(11,2),(13,4),(11,0),(13,0),(14,0)],[],[[],[1],[2,1],[0,1],[0,2,1],[1,0,2,1],[2],[1,0,2,1,0],[0],[0,2],[2,1,0]])
theorem p7_W : TabsP true p7_R p7_T p7_t := ⟨cutsGood p7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D6 : List StD := [
([pw3,pw2,pw5,pw11],[0,4,8,12,1,5,9,17,13,21,25,29,33,37,41,45,3,7,11,15,19,23],[65651,131477,263705,530470,1056874,2146444])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D5 : List StD := [
([pw21,pw3,pw2,pw5,pw11],[0,4,33,37,16,20,24,28,41,45,3,27,8,12,17,25,23,31,35,39],[3,1,70964,141880,3,17473,34945,262214,524426,780])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D4 : List StD := [
([pw25,pw3,pw2,pw5,pw11],[16,44,24,48,12,32,36,40,52,56,43],[32,64,128,1041,3,3,3,14,264,516]),
([pw26,pw3,pw2,pw5,pw11],[16,64,60,68,72,4,76,80],[4,35,13,7,3,9,3,18,192,18]),
([pw21,pw27,pw2,pw5,pw11],[24,48,0,16,28,32,52,56,84,88,92,49,53,3],[33,4,131,2312,67,4,4120,8195,514,1025])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D3 : List StD := [
([pw28,pw2,pw5,pw11],[120,124,128,0,96,100,104,108,112,116],[56,208,776,7,7,7]),
([pw21,pw27,pw29,pw11],[44,8,132,32,40,136,140,144,148,57,61,65],[11,3,548,17,1216,2308])]
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
def p8_T : Nat := 0xa880a880a880a880a880a880a880a880
def p8_R : List Nat := [0, 1, 2, 3]
def p8_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
def p8_Z : List SliceD := [(pw3,4,[1, 2, 3])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN true p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p8_B p3_B p3_L (by decide +kernel),by simp⟩
def p8_C : List (Nat × List Nat) := [(0,[])]
def p8_t : Tabs := (p8_C.map (mkCut true p8_Z),[],[],[])
theorem p8_W : TabsP true p8_R p8_T p8_t := ⟨cutsGood p8_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p8_D4 : List StD := [
([pw3,pw2,pw5,pw11],[0],[1,1,1,1,1,1])]
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
def p9_T : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8
def p9_R : List Nat := [0, 1, 2, 3]
def p9_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
def p9_Z : List SliceD := [(pw6,4,[0, 1, 2])]
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
([pw3,pw2,pw5,pw11],[0],[1,1,1,1,1,1])]
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
def p12_Z : List SliceD := [(pw2,2,[0, 2, 3]),(pw3,2,[1, 2, 3]),(pw1,2,[1, 2, 3]),(pw0,2,[0, 2, 3]),(pw8,1,[2, 3]),(pw9,1,[2, 3]),(pw30,1,[0, 3]),(pw31,1,[1, 3]),(pw22,1,[1, 3]),(pw29,1,[0, 3]),(pw6,2,[0, 1, 2]),(pw10,1,[1, 2]),(pw11,2,[0, 1, 2]),(pw4,2,[0, 1, 3]),(pw32,1,[0, 2]),(pw33,1,[0, 2]),(pw34,1,[1, 2])]
theorem p12_Y : ∀ s ∈ p12_Z, SliceN true p12_R p12_T s := by
  unfold p12_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=2) p12_B p10_B p10_L (by decide +kernel),mkSlice (w:=1) p12_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p12_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=2) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=4) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=6) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=8) p12_B p10_B p10_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=0) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=10) p12_B p2_B p2_L (by decide +kernel),mkSlice (w:=8) p12_B p1_B p1_L (by decide +kernel),by simp⟩
def p12_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[])]
def p12_t : Tabs := (p12_C.map (mkCut true p12_Z),[(5,4),(14,12),(3,2),(3,1),(14,10),(5,1),(14,6),(9,8),(9,1),(5,6),(9,0),(3,0),(11,1),(7,1)],[],[[],[1,2],[1],[2],[2,1],[1,2,1]])
theorem p12_W : TabsP true p12_R p12_T p12_t := ⟨cutsGood p12_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D5 : List StD := [
([pw3,pw2,pw5,pw11],[3,1,5,13,17,21,25,33,7,15,9,11,19,29,23],[1295,3634,12483,829,17101,6640])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D4 : List StD := [
([pw21,pw3,pw2,pw5,pw11],[8,12,16,20,0,4,24,28,37,3,7,15,23],[16,32,3073,4609,259,5,5,10,10,192]),
([pw3,pw2,pw13,pw5,pw11],[0,4,16,20,8,12,32,36,37,3,11,15,19],[259,32,10,10,16,5,5,3073,4609,192]),
([pw10,pw3,pw2,pw5,pw11],[44,8,48,4,20,28,40,13,41],[64,3,3,8,3,3,262,176,5,5]),
([pw9,pw3,pw2,pw5,pw11],[20,12,4,0,8,32,44,25,45],[8,16,3,3,262,5,5,3,3,224]),
([pw3,pw29,pw2,pw5,pw11],[36,12,52,20,28,32,56,41,3],[3,3,5,224,16,8,3,262,3,5]),
([pw3,pw2,pw5,pw18,pw11],[24,28,0,12,32,36,60,9,3],[7,33,5,194,262,16,5,8,3,3]),
([pw12,pw3,pw2,pw5,pw11],[12,9,64,16,60,0,24,44,56,49,7,15],[3,128,3073,32,3,14,26,17,517,324])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D3 : List StD := [
([pw3,pw2,pw5,pw35],[60,8,12,16,0,28,32],[7,10,11,5,20,97]),
([pw36,pw3,pw5,pw11],[8,12,0,16,28,32,24],[7,50,38,9,9,80]),
([pw3,pw37,pw5,pw11],[32,36,8,24,16,28],[5,26,33,5,10,3]),
([pw17,pw3,pw2,pw5],[32,16,8,64,0,28],[5,6,33,9,10,19]),
([pw3,pw29,pw18,pw11],[24,28,36,16,53],[7,5,10,16,5,3]),
([pw3,pw2,pw5,pw38],[24,28,36,16,60],[7,5,10,26,5,3]),
([pw3,pw39,pw5,pw11],[24,36,16,28,8,60],[19,3,12,44,3,3])]
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
def p13_T : Nat := 0xeaa8e880eaa8e880eaa8e880eaa8e880
def p13_R : List Nat := [0, 1, 2, 3, 4]
def p13_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,3,19)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
def p13_Z : List SliceD := [(pw3,7,[1, 2, 3, 4]),(pw40,7,[0, 1, 2, 3]),(pw0,5,[0, 2, 3, 4]),(pw4,5,[0, 1, 3, 4]),(pw11,5,[0, 1, 2, 4]),(pw6,5,[0, 1, 2, 4]),(pw41,6,[0, 1, 2, 3]),(pw2,5,[0, 2, 3, 4]),(pw5,5,[0, 1, 3, 4])]
theorem p13_Y : ∀ s ∈ p13_Z, SliceN true p13_R p13_T s := by
  unfold p13_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p13_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p13_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel),mkSlice (w:=8) p13_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel),mkSlice (w:=16) p13_B p12_B p12_L (by decide +kernel),mkSlice (w:=2) p13_B p9_B p9_L (by decide +kernel),mkSlice (w:=4) p13_B p9_B p9_L (by decide +kernel),by simp⟩
def p13_C : List (Nat × List Nat) := [(0,[]),(1,[]),(0,[128]),(2,[]),(3,[]),(1,[260]),(1,[262]),(1,[263]),(4,[]),(5,[]),(6,[]),(0,[129]),(7,[]),(8,[]),(1,[261]),(0,[258]),(1,[388]),(1,[389]),(1,[390]),(0,[129,128]),(4,[261]),(5,[261]),(1,[261,260]),(6,[261]),(5,[260]),(4,[260])]
def p13_t : Tabs := (p13_C.map (mkCut true p13_Z),[(13,12),(7,6),(11,10),(19,2),(11,9),(13,9),(7,5),(7,3),(13,5),(11,3),(19,3),(21,5),(25,9),(14,6),(19,17),(21,17),(25,24),(14,12),(14,10),(25,17),(11,1),(7,2),(7,1)],[],[[],[2],[1,2],[1,2,1],[1],[2,1]])
theorem p13_W : TabsP true p13_R p13_T p13_t := ⟨cutsGood p13_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D8 : List StD := [
([pw3,pw2,pw5,pw11,pw41],[0,4,1,41,5,17,21,25,29,33,37,45,3,7,11,9,13,49,15,19,23],[21,32773,21,65543,29152,276128,2058,1591104,2058,131082])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D7 : List StD := [
([pw3,pw29,pw2,pw5,pw11,pw41],[12,8,16,20,5,57,61,24,28,32,36,40,9,13,17,21,41,49,53,3],[19,19,22,4114,8218,129,261,263681,2057,524293,16417,41,32836,76,196616]),
([pw3,pw2,pw5,pw18,pw11,pw41],[48,12,16,44,56,1,52,25,45,65,32,36,40,5,9,29,41,49,69,73,77,3],[43,16428,521,8232,552,2097223,5,262275,403,2,557124,65620,1051649,4113,131344]),
([pw12,pw3,pw2,pw5,pw11,pw41],[12,60,72,5,41,32,36,9,69,0,16,40,52,64,68,13,17,29,33,45,77,81],[523,8193,136193,16385,2053,11,138,138,32782,65793,2097473,21,1310816,524308,52])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D6 : List StD := [
([pw3,pw29,pw18,pw11,pw41],[16,52,76,88,65,5,57,80,84,92,96,100,41,49,53,81,85,89],[65541,22,52,52,131075,16769,521,35906,74,12296])]
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
def p14_T : Nat := 0xfee8e880fee8e880fee8e880fee8e880
def p14_R : List Nat := [0, 1, 2, 3, 4]
def p14_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,3,19)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
def p14_Z : List SliceD := [(pw1,7,[1, 2, 3, 4]),(pw0,7,[0, 2, 3, 4]),(pw3,7,[1, 2, 3, 4]),(pw2,7,[0, 2, 3, 4]),(pw4,7,[0, 1, 3, 4]),(pw6,7,[0, 1, 2, 4]),(pw41,7,[0, 1, 2, 3]),(pw5,7,[0, 1, 3, 4]),(pw11,7,[0, 1, 2, 4])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN true p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p14_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p14_B p7_B p7_L (by decide +kernel),mkSlice (w:=1) p14_B p5_B p5_L (by decide +kernel),mkSlice (w:=2) p14_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p14_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p14_B p7_B p7_L (by decide +kernel),mkSlice (w:=16) p14_B p5_B p5_L (by decide +kernel),mkSlice (w:=4) p14_B p5_B p5_L (by decide +kernel),mkSlice (w:=8) p14_B p5_B p5_L (by decide +kernel),by simp⟩
def p14_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[])]
def p14_t : Tabs := (p14_C.map (mkCut true p14_Z),[(13,12),(7,5),(7,4),(11,10),(7,6),(19,3),(19,2),(11,9),(19,1),(7,3),(13,5),(11,3),(21,5),(25,9)],[],[])
theorem p14_W : TabsP true p14_R p14_T p14_t := ⟨cutsGood p14_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D9 : List StD := [
([pw3,pw2,pw5,pw11,pw41],[0,4,8,12,16,24,1,5,21,20,28,32,29,37,41,9,13,17,25,33,45,49,53],[32975,65621,131653,262501,4250,4234,524714,1076752,2106672,4213536])]
def p14_D8 : List StD := []
theorem p14_I8 : LevelN true p14_T 8 p14_D8 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C9x0 : levelOK true p14_T p14_t 8 (p14_D8.map Prod.fst) ((p14_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p14_I9 : LevelN true p14_T 9 p14_D9 := levelStep p14_B p14_W p14_I8 (chunks 32 p14_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C9x0
  ))
theorem p14_L : LowN true p14_R p14_T 10 := lowSearch p14_B p14_I9 (by decide +kernel)
def p15_T : Nat := 0x80008000800080008000800080008000
def p15_R : List Nat := [0, 1, 2, 3]
def p15_E : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15)]
theorem p15_B : baseOK p15_T p15_R p15_E = true := by decide +kernel
theorem p15_L : LowN true p15_R p15_T 3 := lowCount p15_B (by decide +kernel)
def p16_T : Nat := 0xe8808000e8808000e8808000e8808000
def p16_R : List Nat := [0, 1, 2, 3, 4]
def p16_E : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15),(4,7,23)]
theorem p16_B : baseOK p16_T p16_R p16_E = true := by decide +kernel
def p16_Z : List SliceD := [(pw3,7,[1, 2, 3, 4]),(pw2,7,[0, 2, 3, 4]),(pw5,7,[0, 1, 3, 4]),(pw11,7,[0, 1, 2, 4]),(pw41,7,[0, 1, 2, 3]),(pw21,4,[2, 3, 4]),(pw29,4,[0, 3, 4]),(pw27,4,[1, 3, 4]),(pw1,3,[1, 2, 3, 4]),(pw25,1,[3, 4]),(pw42,4,[0, 1, 2]),(pw43,4,[0, 1, 4]),(pw44,1,[1, 4]),(pw0,3,[0, 2, 3, 4]),(pw45,1,[3, 4]),(pw46,1,[2, 4]),(pw22,2,[1, 3, 4]),(pw10,2,[1, 2, 4]),(pw47,1,[2, 4]),(pw48,2,[0, 2, 3]),(pw49,2,[1, 2, 3]),(pw50,1,[0, 1]),(pw51,4,[0, 1, 3]),(pw52,2,[1, 2, 3]),(pw53,4,[1, 2, 4]),(pw54,1,[0, 2]),(pw55,1,[1, 2]),(pw56,1,[0, 1]),(pw57,1,[3, 4]),(pw33,4,[0, 2, 4]),(pw58,1,[2, 3]),(pw59,1,[1, 4]),(pw60,1,[2, 4]),(pw6,3,[0, 1, 2, 4]),(pw40,3,[0, 1, 2, 3]),(pw61,1,[0, 2]),(pw62,1,[0, 3]),(pw63,1,[0, 4]),(pw24,2,[0, 3, 4]),(pw64,2,[0, 1, 2]),(pw65,2,[0, 1, 2]),(pw66,1,[2, 3]),(pw67,1,[0, 3]),(pw68,1,[1, 3]),(pw69,1,[1, 2]),(pw70,1,[0, 4]),(pw71,1,[1, 3]),(pw72,4,[0, 2, 3]),(pw73,1,[0, 1]),(pw74,1,[0, 2]),(pw75,1,[0, 4]),(pw76,1,[0, 3]),(pw77,1,[1, 4])]
theorem p16_Y : ∀ s ∈ p16_Z, SliceN true p16_R p16_T s := by
  unfold p16_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p16_B p7_B p7_L (by decide +kernel),mkSlice (w:=2) p16_B p7_B p7_L (by decide +kernel),mkSlice (w:=4) p16_B p7_B p7_L (by decide +kernel),mkSlice (w:=8) p16_B p7_B p7_L (by decide +kernel),mkSlice (w:=16) p16_B p7_B p7_L (by decide +kernel),mkSlice (w:=3) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=6) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=5) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p16_B p15_B p15_L (by decide +kernel),mkSlice (w:=7) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=24) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=12) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=12) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p16_B p15_B p15_L (by decide +kernel),mkSlice (w:=3) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=3) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=1) p16_B p6_B p6_L (by decide +kernel),mkSlice (w:=1) p16_B p6_B p6_L (by decide +kernel),mkSlice (w:=9) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=16) p16_B p6_B p6_L (by decide +kernel),mkSlice (w:=16) p16_B p6_B p6_L (by decide +kernel),mkSlice (w:=28) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=20) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=1) p16_B p6_B p6_L (by decide +kernel),mkSlice (w:=9) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=24) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=24) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=24) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=6) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=10) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=3) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=5) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=10) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p16_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p16_B p15_B p15_L (by decide +kernel),mkSlice (w:=26) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=22) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=14) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=2) p16_B p6_B p6_L (by decide +kernel),mkSlice (w:=16) p16_B p6_B p6_L (by decide +kernel),mkSlice (w:=8) p16_B p6_B p6_L (by decide +kernel),mkSlice (w:=18) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=6) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=17) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=9) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=6) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=5) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=18) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=20) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=10) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=10) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=20) p16_B p1_B p1_L (by decide +kernel),mkSlice (w:=9) p16_B p1_B p1_L (by decide +kernel),by simp⟩
def p16_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(2,[128]),(5,[]),(3,[128]),(4,[128]),(0,[130]),(0,[128]),(6,[]),(7,[]),(8,[]),(9,[]),(3,[128,272]),(4,[128,272]),(1,[128]),(0,[392]),(10,[]),(4,[384]),(0,[395]),(1,[392,19]),(2,[392,19]),(3,[256,128]),(4,[256,128]),(0,[260]),(1,[260]),(11,[]),(5,[128]),(12,[]),(4,[392]),(11,[128]),(0,[260,19]),(1,[260,19]),(0,[256,147]),(0,[128,275]),(1,[128,272]),(0,[128,272]),(2,[128,520]),(0,[256,516]),(3,[128,520]),(13,[]),(14,[]),(15,[]),(3,[256,400]),(16,[]),(0,[260,402]),(0,[260,400]),(3,[256,402]),(2,[256,402]),(4,[392,19]),(3,[392,19]),(17,[]),(0,[261,16]),(0,[128,274]),(0,[130,272]),(1,[256,130]),(0,[256,130]),(0,[256,131]),(4,[128,400]),(1,[128,258]),(0,[128,258]),(0,[128,259]),(0,[128,256]),(1,[128,256]),(1,[130,272]),(0,[131]),(1,[256,516]),(4,[128,384]),(2,[128,256]),(18,[]),(0,[260,130]),(1,[260,130]),(0,[257,144]),(0,[131,272]),(0,[260,512]),(4,[128,392]),(1,[128,260]),(0,[128,260]),(1,[128,520]),(0,[128,263]),(0,[128,522]),(6,[128]),(7,[128]),(0,[128,520]),(2,[128,272]),(19,[]),(20,[]),(3,[392,512]),(21,[]),(1,[260,400]),(22,[]),(23,[]),(10,[258]),(22,[258]),(11,[258]),(3,[392,514]),(2,[392,514]),(0,[392,147]),(0,[388,275]),(0,[260,403]),(1,[256,519]),(24,[128]),(4,[384,128,276]),(1,[392,130]),(0,[392,130]),(0,[392,131]),(0,[128,392]),(1,[128,392]),(2,[128,392]),(25,[]),(26,[]),(0,[128,395]),(0,[128,403]),(7,[259]),(5,[259]),(0,[128,400]),(4,[256,516]),(2,[391,19]),(1,[391,19]),(2,[256,400]),(10,[260]),(0,[128,394]),(27,[]),(28,[]),(4,[386,260]),(3,[386,260]),(0,[256,392]),(3,[384]),(1,[257]),(0,[256,524]),(2,[260]),(29,[258]),(2,[260,392,23]),(3,[256,260,128]),(3,[256,260]),(4,[256,260]),(4,[256,260,128]),(3,[256,516]),(0,[256]),(0,[258]),(2,[260,128]),(29,[]),(29,[128]),(4,[128,256]),(4,[128,256,388]),(1,[392,128]),(2,[392]),(0,[394]),(0,[256,400]),(1,[256,400]),(0,[256,402]),(0,[257]),(0,[386,275]),(0,[258,400]),(0,[392,19]),(5,[260]),(30,[]),(4,[128,527]),(4,[260,384,534]),(4,[260,514,407]),(3,[260,384,534]),(3,[260,514,407]),(29,[260,15]),(4,[260,400,642]),(6,[260,15]),(1,[260,524,23]),(1,[388,520,23]),(3,[260,524,23]),(3,[256,527]),(2,[256,527]),(3,[259,392,23]),(2,[259,392,23]),(4,[392,19,512]),(3,[256,392,23]),(0,[260,524]),(31,[]),(4,[256,392,642]),(0,[260,261,20]),(0,[260,128,278]),(0,[260,130,276]),(1,[256,260,130]),(0,[256,260,130]),(0,[256,257,148]),(0,[256,128,278]),(0,[256,131,276]),(4,[392,128,404]),(1,[128,260,258]),(0,[128,260,258]),(0,[128,129,276]),(0,[128,130,276]),(0,[128,131,276]),(4,[392,128,276]),(0,[128,256,260]),(1,[128,256,644]),(0,[128,256,644]),(13,[260]),(1,[128,256,260]),(1,[261,16]),(1,[128,274]),(4,[128,384,388]),(2,[128,256,260]),(32,[]),(1,[260,261,20]),(1,[260,128,278]),(1,[260,130,276]),(4,[128,384,392]),(1,[128,260,256]),(13,[256]),(4,[128,520,392]),(4,[260,400]),(33,[]),(1,[260,384,534]),(1,[260,514,407]),(4,[256,400,527]),(2,[256,400,527]),(2,[392,19,512]),(4,[256,388,532]),(4,[128,392,532]),(0,[128,272,653]),(2,[128,272,653]),(4,[384,260,532]),(0,[387,128,276]),(0,[384,260,532]),(4,[129,260,404]),(4,[130,260,404]),(4,[257,260,404]),(4,[258,260,404]),(34,[]),(35,[]),(36,[]),(37,[]),(4,[260,524,23]),(4,[388,520,23]),(2,[388,520,23]),(4,[392,516,23]),(2,[384,128,276]),(1,[384,128,276]),(3,[384,128,276]),(4,[392,256,406]),(1,[260,400,642]),(0,[388,520]),(38,[]),(0,[129]),(0,[387]),(11,[131]),(0,[256,516,407]),(0,[260,512,407]),(11,[130]),(1,[386,260,23]),(22,[260,15]),(1,[129]),(0,[128,388,279]),(0,[128,260,404]),(0,[128,260,407]),(0,[130,260,404]),(0,[260,400,512]),(3,[260,392,23]),(4,[260,392,23]),(0,[128,392,644]),(1,[256,400,516]),(3,[384,260,532]),(4,[128,272,524]),(1,[128,256,404]),(3,[260,384]),(6,[129]),(4,[386]),(1,[260,392,23]),(0,[392,260,23]),(0,[392,256,151]),(3,[260,19]),(0,[256,519]),(4,[384,388]),(2,[128,260,256]),(3,[388,128,276]),(3,[388,260,23]),(0,[389,16]),(0,[128,402]),(0,[130,400]),(0,[384,131]),(39,[]),(0,[384,516]),(40,[]),(3,[128,272,524]),(3,[388,256,644]),(0,[128,384]),(41,[]),(0,[128,387]),(2,[128,256,388]),(2,[256,388,532]),(6,[260]),(42,[]),(2,[128,256,392]),(1,[128,256,392]),(3,[128,275]),(6,[131]),(0,[385]),(3,[128,395,535]),(43,[]),(4,[388,256,532]),(11,[256]),(3,[386,275]),(2,[386,275]),(0,[391,19]),(0,[387,147]),(0,[131,400]),(2,[256,391,23]),(44,[]),(45,[]),(2,[260,130,404]),(3,[386,145]),(3,[130,402]),(0,[256,387,151]),(0,[256,131,404]),(0,[256,128,404]),(0,[256,128,407]),(4,[388,256,644]),(2,[260,391,23]),(0,[259,128,407]),(2,[130,392,23]),(4,[386,260,23]),(3,[386,260,23]),(4,[260,388,384]),(0,[128,259,404]),(0,[128,385,276]),(0,[128,256,395]),(0,[128,256,392]),(0,[392,256,131]),(4,[386,388]),(0,[392,128,512]),(46,[]),(6,[258]),(4,[262,384]),(0,[388,19,520]),(0,[392,128,404]),(0,[392,386,151]),(3,[386]),(0,[392,388,23]),(1,[388,392,23]),(2,[390,392,23]),(3,[386,392,151]),(0,[256,384,392]),(3,[388,384]),(0,[384,256,520]),(1,[385]),(47,[258]),(2,[388,392,23]),(2,[260,256,404]),(0,[388,256,406]),(0,[388,259,404]),(0,[388,385,276]),(0,[388,256,404]),(0,[256,263,404]),(0,[256,260,404]),(0,[256,388,648]),(0,[392,388]),(0,[392,256,388]),(0,[392,128,532]),(2,[392,130]),(10,[256,260]),(10,[128,260]),(10,[128,256]),(3,[128,256,260]),(0,[260,256]),(10,[256]),(0,[260,258]),(2,[260,512]),(13,[128]),(4,[256,388,392]),(0,[256,262]),(10,[128]),(4,[128,256,392]),(2,[260,130]),(0,[388,256]),(0,[388,258]),(4,[256,388,516]),(22,[260]),(48,[]),(29,[260]),(0,[256,390]),(49,[]),(22,[128]),(0,[388,259]),(50,[]),(51,[]),(29,[128,270]),(0,[129,128]),(29,[258,143]),(0,[128,392,532]),(4,[260,261,384,538]),(4,[260,261,514,411]),(29,[130,268]),(29,[130,271]),(4,[261,260,404,770]),(10,[260,386]),(10,[128,270]),(29,[129]),(29,[130]),(0,[260,400,641]),(2,[256,402,524,153]),(0,[129,260,404]),(2,[392,19,512,153]),(4,[392,19,512,153]),(10,[258,143]),(6,[128,270]),(6,[258,143]),(6,[130,268]),(6,[130,271]),(10,[260,15]),(0,[384,256,151]),(0,[384,128,279]),(0,[384,128,276]),(33,[388]),(33,[384]),(0,[384,260,640]),(2,[384,388,128,280]),(3,[384,388,128,280]),(10,[129]),(22,[128,270]),(0,[260,524,23]),(6,[130]),(4,[129]),(4,[130]),(4,[260,388,256,408]),(0,[256,388,532]),(0,[128,256,260,411]),(0,[128,256,260,408]),(8,[256]),(8,[128]),(0,[260,400,128,282]),(23,[256]),(4,[388,392,23]),(23,[128]),(0,[392,128,276]),(0,[392,130,276]),(34,[388]),(0,[128,256,406]),(22,[128,256]),(0,[128,392,640]),(4,[384,388,128,280]),(4,[384,260,404]),(0,[128,272,258,408]),(0,[128,272,259,408]),(0,[128,272,257,408]),(0,[128,272,256,408]),(17,[256]),(8,[384]),(0,[392,384]),(2,[260,388,392,27]),(4,[386,392,151]),(0,[392,384,256,155]),(0,[256,388,516]),(2,[260,130,276]),(0,[388,130,276]),(0,[256,388,640]),(0,[128,388,256]),(0,[128,388,259]),(22,[128,260]),(52,[]),(0,[128,256,391]),(2,[388,392,261,24]),(2,[388,392,130,280]),(0,[392,389,20]),(0,[392,130,404]),(0,[384,392,131]),(47,[128]),(2,[256,131,276]),(2,[131,272]),(0,[256,260,128,408]),(0,[256,260,128,411]),(4,[392,128,276,652]),(8,[260]),(0,[128,403,520]),(0,[128,403,131,280]),(23,[260]),(4,[388,128,276]),(0,[128,256,404]),(0,[392,128,278]),(0,[392,261,20]),(0,[256,388,656]),(0,[128,388,259,408]),(0,[128,388,385,280]),(0,[128,256,262,408]),(0,[128,256,263,408]),(0,[128,256,261,408]),(0,[392,128,388]),(0,[392,128,256]),(0,[392,256,128,408]),(4,[262,392,384]),(10,[262]),(0,[388,19,263,408]),(0,[392,260,128,408]),(10,[261]),(0,[392,260,388,27]),(1,[388,260,392,27]),(4,[388,261,20]),(4,[388,128,278]),(4,[388,130,276]),(0,[388,392,256]),(0,[388,392,258]),(0,[256,388,524]),(5,[256]),(0,[256,262,404]),(22,[130]),(22,[258,143]),(22,[130,268]),(0,[128,129,277]),(22,[130,271]),(0,[129,272]),(0,[128,272,652]),(0,[128,274,392,536]),(22,[129]),(0,[392,388,128,280]),(0,[392,388,130,280]),(0,[392,256,131,408]),(0,[128,388,256,408]),(0,[128,388,256,410]),(0,[128,392,656]),(29,[128,256]),(0,[392,388,128,282]),(0,[392,388,261,24]),(0,[392,256,128,410]),(0,[392,256,385,152]),(0,[392,128,656]),(22,[258,130]),(29,[258,130])]
def p16_t : Tabs := (p16_C.map (mkCut true p16_Z),[(29,28),(30,28),(15,13),(27,26),(30,26),(23,22),(30,22),(15,14),(30,14),(27,25),(29,25),(23,21),(29,21),(29,13),(23,19),(27,19),(15,11),(27,11),(15,7),(23,7),(27,24),(23,3),(29,20),(27,18),(23,5),(30,24),(29,12),(27,3),(29,24),(15,12),(15,10),(15,6),(15,9),(15,5),(23,6),(27,10),(29,4),(15,3),(15,8),(15,4)],[],[[],[1],[2,1],[3,2,1],[0,1],[0,2,1],[0,3,2,1],[1,0,2,1],[1,0,3,2,1],[2,1,0,3,2,1],[1,0,2,1,3,2],[2],[1,0,2,1,0,3,2],[3,2],[1,0,2,1,3,2,1,0],[0],[0,2],[0,3,2],[3],[2,3],[2,1,0,3,2,1,0],[0,3],[1,0],[1,0,3],[0,1,2,1,3,2],[0,1,0,2,1,3,2],[1,3],[1,2],[0,2,1,0,3,2],[1,3,2],[0,2,1,3,2,1,0],[2,1,0],[0,1,0,2,1],[0,1,2],[3,2,1,0],[0,1,2,3],[1,2,3],[0,1,3,2,1,0],[0,1,2,1,0,3,2,1],[2,1,0,3,2],[0,1,3,2],[2,1,3,2,1,0],[1,2,1],[0,1,2,1],[0,2,1,3,2],[1,3,2,1,0],[1,3,2,1],[1,0,2],[1,0,3,2],[0,1,3],[0,2,1,3,2,1]])
theorem p16_W : TabsP true p16_R p16_T p16_t := ⟨cutsGood p16_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D9 : List StD := [
([pw3,pw2,pw5,pw11,pw41],[0,4,8,12,16,1,5,17,9,25,13,21,29,33,37,41,45,49,53,57,61,65,69,73,77,3,7,11,15,19,23,27,31,35,39],[33554787,67110053,134220329,268447793,536920134,1073938506,2147746130,4296540300,8596226196,17205035544])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D8 : List StD := [
([pw21,pw3,pw2,pw5,pw11,pw41],[0,4,20,28,32,41,24,49,3,53,65,73,77,47,55,8,12,16,17,25,33,57,61,69,43,51,59,63,67,71,75,79],[3,1,16811364,33630408,67261008,3,262405,532489,1064977,134217766,268435594,536871442,6291756,1082131508,2147489944])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D7 : List StD := [
([pw25,pw21,pw3,pw2,pw5,pw11,pw41],[40,20,24,60,64,3,75,44,61,69,36,52,56,68,49,53,73,77,28,32,48,25,33,39,63,83,87],[1026,129,1049600,6,8722720,34216512,129,1,6,16428,32852,8321,8195,2097193,4194385,7,16793612,67141652,298,594,197376]),
([pw25,pw3,pw2,pw5,pw11,pw41],[20,40,68,60,64,44,61,3,48,69,73,77,75,24,25,33,49,53,39,63,83,87,91,95],[34,260,8193,263368,1055248,7,39,16522,36882,295,589836,2228244,4194377,8389137,3288]),
([pw78,pw3,pw2,pw5,pw11,pw41],[76,72,88,9,25,33,80,1,65,3,4,8,84,92,13,37,41,45,57,81,7,75,99,103,107],[67,4195337,8390913,67,4099,524422,16514,19,35,107020,131589,2097165,1310737,16777505,51]),
([pw21,pw27,pw2,pw5,pw11,pw41],[20,68,96,100,49,24,48,13,53,3,0,61,69,73,77,1,7,47,51,55,59,75,107,111,115,119,123],[3,1026,163,401588,1589672,32835,1025,25167956,100667720,515,534,2097418,67589,4198409,25116]),
([pw21,pw3,pw2,pw43,pw5,pw11,pw41],[20,104,28,108,116,120,53,77,43,55,1,5,57,61,3,31,24,32,112,124,128,33,69,7,11,19,23,47,51,59,71,91,111,127,131,135,139],[10,2,377600,2147504145,8724160532,537395952,10,4296049666,8388611,16777222,2098690,51539609640,33554441,67108876,1073743944,5,1,68719608288,5,4198657,268443780])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D6 : List StD := [
([pw79,pw21,pw3,pw2,pw5,pw11,pw41],[52,152,148,116,156,164,132,32,136,140,144,160,168,172,176,139],[64,256,64,512,1024,32897,4,2,9,9,9,6,3,3,3,22,2084,4100,56,8208,16416]),
([pw80,pw3,pw2,pw43,pw5,pw11,pw41],[184,120,92,192,204,180,188,208,3,108,196,200,212,9,47],[32,515,72,1096,2081,3,3,280,268,16513,3,3,3,4098,8208,128,4,3,5,3,22]),
([pw25,pw81,pw3,pw2,pw5,pw11,pw41],[52,256,77,69,152,156,164,260,20,28,64,160,168,216,220,224,228,232,236,240,244,248,252,3,35,39],[57360,65536,131072,262144,33556992,524293,1048576,2097152,16777488,4194304,1033,3,3,3,5,162,194,4100,8388704,12,12]),
([pw25,pw21,pw53,pw2,pw5,pw11,pw41],[164,52,77,24,280,40,284,36,68,3,168,264,268,272,276,69,39],[128,2049,128,4096,73729,16390,257,32,24,11,6,1281,82,32,66,56,521,68,529,32772,5]),
([pw25,pw21,pw3,pw2,pw43,pw11,pw41],[120,176,152,312,316,60,288,3,24,28,52,116,168,220,284,292,296,300,304,308,320,324,85,63],[64,32768,64,204804,262658,4718593,8,16,4356,2208,3,24,1049604,176,3,13,8388617,16386,2097152,3,3]),
([pw79,pw25,pw3,pw2,pw5,pw11,pw41],[52,60,77,340,168,184,320,64,116,156,220,328,332,336,15,27,35,39,139],[1024,16384,32768,65536,2048,262273,4096,8192,256,131074,5,9,9,11,5,88,82,20,546,36,6]),
([pw79,pw3,pw2,pw5,pw11,pw41],[152,148,344,60,348,77,3,16,52,132,136,140,144,160,272,304,352,33,53,69,15,27,35,39,63,91,127,139],[1049601,2097664,4196352,8392704,134218208,7,7,16393,131153,7,8202,17104898,32780,34078740,67108920]),
([pw80,pw3,pw2,pw50,pw5,pw11,pw41],[184,360,192,212,76,356,388,3,0,112,364,368,372,376,380,384,392,1,5,47,55],[32,1027,256,20,2080,529,393217,134,134,524291,1048579,3,3,10,4098,8192,16384,32768,73,65537,72]),
([pw80,pw3,pw2,pw5,pw11,pw41],[192,92,52,208,5,17,25,3,184,204,9,33,4,180,396,400,404,1,37,45,47,55,143,147],[8321,4199828,16389,32773,65541,8519697,35,73,2561,262578,1572936,2100752,35,42,74]),
([pw25,pw53,pw2,pw5,pw11,pw41],[60,52,260,280,3,320,416,69,77,12,44,48,272,412,13,21,7,24,36,40,268,408,53,81,39,75,83,151],[2102817,264192,1179648,16814595,100696450,8396837,25642,2049,134234514,524300,21,4194388,65545,65736,337]),
([pw25,pw3,pw2,pw5,pw42,pw11,pw41],[64,73,432,436,444,77,76,440,3,448,63,91,420,424,428,452,39,75,87,95,127,139],[4096,8192,16384,65856,1048642,2097248,13,140,276,274,131105,140,1544,1538,262177,2192,2066,524321,1,32768,3]),
([pw82,pw3,pw2,pw5,pw11,pw41],[44,64,456,52,444,33,61,3,12,120,372,460,464,468,472,476,480,9,25,49,65,73,77,7,11,155],[5,2051,4099,52430152,8206,7,16389,262292,38,98309,524929,131075,8388689,1048579,4194338]),
([pw78,pw3,pw29,pw2,pw5,pw11,pw41],[432,488,88,92,500,76,444,3,44,484,75,452,492,496,504,508,7,99,103,107,143],[512,1048864,131330,262658,4097,2049,193,69,8201,19,19,8,4,176,1072,68,134,1030,65546,524298,49153]),
([pw78,pw3,pw33,pw2,pw5,pw41],[76,512,88,444,3,532,33,65,89,516,520,524,92,528,536,13,41,57,93,103,107],[515,3073,3073,532609,515,262442,302,33026,67,1,1183896,101,81948,21,209]),
([pw21,pw27,pw29,pw11,pw41],[540,552,49,40,53,73,77,20,24,44,48,68,544,548,61,69,3,47,51,55,59,111,115,119,123,135,159,163,167],[2184,136,397605,1581394,2056,6308869,25199634,100663845,402653778,65639]),
([pw21,pw27,pw33,pw5,pw11,pw41],[96,556,568,24,68,120,560,53,69,44,164,444,584,13,3,48,336,564,572,576,580,45,77,89,97,101,55,59,67,111,119,123,135,171,175,179,183],[1554,131138,8734,2097227,218112168,298016,64,9135259649,3221227936,21508915204,16,103080264064,16389,20740,272633857]),
([pw21,pw27,pw2,pw5,pw42,pw11,pw41],[588,448,444,496,73,440,77,72,24,48,84,420,580,592,596,3,11,15,43,67,71,79,147,171,179,187,191,195],[2049,128,8201,2097416,65560,131144,37,128,4194820,8388628,33554500,32801,16777219,524291,1048579,262178,67108882,134217794,16384,1024,4112]),
([pw83,pw21,pw3,pw2,pw5,pw11,pw41],[176,444,52,88,168,600,616,624,632,20,564,604,608,612,620,628,636],[32,2048,32,515,13376,16449,8,128,3,32772,5,10,5,134,7,3,24,17,3,258,65793])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D5 : List StD := [
([pw84,pw29,pw2,pw5,pw11,pw41],[444,664,168,496,40,660,0,120,640,644,648,652,656,668,672,676,3],[81,17,24,769,3073,128,4096,38,38,65545,14,14,8195,16387,32802]),
([pw80,pw85,pw2,pw5,pw11,pw41],[120,192,188,184,212,9,148,204,680,684,688,692,696,700,105],[6,73,262,518,7,33,1024,2048,16514,9,17,4128,8210,9,17]),
([pw80,pw27,pw2,pw43,pw11,pw41],[120,704,708,104,184,196,208,92,200,212,312,668,712,9],[42,1041,42,290,11,2053,66,578,5,17,5,12288,128,19,5]),
([pw25,pw81,pw3,pw2,pw43,pw41],[120,740,776,780,52,160,176,304,340,716,720,724,728,732,736,744,748,752,756,760,764,768,772,784,788,792,85,109],[3712,4096,8192,49186,67174401,131072,262144,3670272,138412033,5,26,5,8388617,50331648,65]),
([pw25,pw21,pw53,pw33,pw5,pw41],[120,220,284,800,77,160,808,812,24,216,224,232,236,244,256,264,320,796,804,69],[2048,163880,1570,4096,262161,24584,3,320,17,11,65604,5,133,144,524289]),
([pw25,pw21,pw53,pw2,pw43,pw41],[120,832,284,288,304,316,340,820,24,116,176,220,296,300,324,752,788,816,824,828,836,840,85],[8,393360,8,14352,4718593,32770,32,1048896,513,65665,16416,2097157,67,6,1025]),
([pw84,pw63,pw2,pw5,pw11,pw41],[152,168,848,33,496,0,16,120,184,284,656,664,668,844,852,856],[8289,3,17,5,49153,128,1024,2048,10,4098,22,26,516,264,12]),
([pw80,pw86,pw2,pw5,pw11,pw41],[120,184,192,212,0,372,696,860,864,868,1,89,105,113,3],[16,3,132,262,3,17409,8192,2048,4096,3,9,96,514,3,9]),
([pw87,pw3,pw2,pw5,pw11,pw41],[120,184,212,284,872,52,372,3,63,91,127,139],[128,256,512,1024,2048,3,56,34,3,3,21,88,14,3,5]),
([pw79,pw3,pw2,pw5,pw11,pw88],[120,876,880,184,212,872,884,52,284,888,892,15,27,35,39,139],[2048,4096,8192,16384,32768,7,100,644,7,13,49,1282,74,11,19]),
([pw84,pw3,pw2,pw5,pw11,pw41],[212,120,0,52,184,284,168,176,896],[64,7,13,28,7,3,9,24,3,18,3,416,33,18,3]),
([pw84,pw89,pw2,pw5,pw11,pw41],[168,496,848,916,284,900,0,176,660,904,908,912,5,17,25,33],[64,545,3074,6,40,4096,8192,16384,32768,129,7,11,20,264,20]),
([pw84,pw2,pw5,pw11,pw41],[120,212,0,168,360,916,932,184,496,65,73,52,176,664,848,920,924,928,936,940,944,9,29,117,121,125,129,133],[8388639,16812310,33638548,4325431,67113801,134489099,2625896,1058434,737,1123]),
([pw79,pw90,pw2,pw5,pw11,pw41],[872,496,948,16,168,332,916,952,956,132,140,144,152,304,848,888,3,7,11],[88,512,1024,2048,72,48,35,49154,4096,6,131,65665,8452,131077,262401]),
([pw80,pw27,pw2,pw50,pw11,pw41],[360,192,212,372,708,960,112,368,380,384,496,712,964,968],[34,5,2,130,96,5136,3,7,8209,5,5,9,256,512,2060]),
([pw91,pw3,pw2,pw5,pw11,pw41],[176,168,52,632,284,360,120,212,368,444,612,972,976,3],[2048,128,4099,1282,3,8198,5,44,5,3,42,3,17,584,17]),
([pw92,pw3,pw2,pw5,pw11,pw41],[372,52,496,120,984,444,980,352,500,632,916,988,992,137,139],[1024,84,19,19,16450,3,7,7,8198,12,2564,5,4384,41,137]),
([pw52,pw28,pw2,pw5,pw11,pw41],[496,52,152,120,1000,16,444,996,1004,3,136,160,916,117,121,125,137,7,11],[4640,9217,16514,32898,4,6,5,7,65570,9,2065,529,336,131144,262408]),
([pw80,pw3,pw29,pw2,pw11,pw41],[500,1016,52,444,1008,1032,1036,204,208,496,672,1012,1020,1024,1028,1040,113,3,75,147],[512,28,24,2050,4098,6,589826,3,3,8192,16641,1153,131105,262209,32864]),
([pw25,pw93,pw2,pw5,pw11,pw41],[496,444,44,1056,500,80,416,424,428,432,452,492,516,848,916,956,1044,1048,1052,3,7,75,107],[5,128,256,77824,147488,262150,5,2048,1024,11,524297,2097161,1048594,4194322,33344]),
([pw78,pw3,pw63,pw2,pw5,pw41],[496,212,444,500,1064,844,1060,1068,1072,16,72,168,536,632,1076,1080,3,7],[64,688,2065,22,96,1033,262,4099,11,16384,32768,8322,261,65545,131084]),
([pw25,pw53,pw33,pw5,pw41],[444,69,77,44,60,500,1096,24,48,160,37,3,12,236,284,340,556,576,1084,1088,1092,13,63,75,83,151,183],[266777,525072,8320,26214438,409,2179144,33556519,164929,71304198,2151]),
([pw25,pw53,pw72,pw5,pw11,pw41],[1100,496,1148,468,888,1156,44,52,280,284,412,1104,1108,1112,1116,1120,1124,1128,1132,1136,1140,1144,1152,3,7,63,75,199],[2049,28680,32768,65553,393232,525440,1048642,2097152,67109378,266,33554437,4194304,16777249,134217764,8388613]),
([pw25,pw53,pw2,pw5,pw42,pw41],[444,496,60,1172,76,432,1164,332,424,428,556,848,1084,1160,1168,1176,137,3,7,15,63,91],[4100,256,512,10256,589840,69,1090,33,16417,11,1048706,163842,2097161,262153,4]),
([pw94,pw3,pw2,pw5,pw11,pw41],[284,1196,52,500,996,1192,128,632,1200,60,332,984,1180,1184,1188,139],[16,2048,4624,9232,49153,38,5,38,5,67,296,11,11,448,131]),
([pw95,pw3,pw2,pw5,pw11,pw41],[52,372,176,444,1204,348,980,212,360,384,500,1208,1212],[16,193,2065,4113,80,3,3,3,13,12,1568,262,12,10,34]),
([pw82,pw53,pw2,pw5,pw11,pw41],[332,444,496,52,456,112,1232,120,416,468,848,1116,1216,1220,1224,1228,1236,141,3,7],[33,6145,24577,1057,528,11,13,16,131082,32788,262149,69,524291,67,65920]),
([pw82,pw3,pw33,pw5,pw11,pw41],[1264,444,1268,1272,120,128,1052,1240,3,52,372,496,848,984,1200,1232,1244,1248,1252,1256,1260,1276,97],[128,204832,786560,20512,1048577,577,13,259,17,2058,2097152,1088,266,32772,4194324]),
([pw78,pw96,pw2,pw5,pw11,pw41],[444,664,432,496,44,3,452,492,848,1280,1284,1288,93,117,121,141,7,75,107],[289,8216,16401,132,68,5,12,4099,32771,521,42,131082,65539,262147,3076]),
([pw78,pw3,pw29,pw33,pw5,pw41],[444,500,1308,496,44,1292,3,168,536,1296,1300,1304,1312,1316,1320,1324,75,103],[32,144,1568,131089,2052,69,7,268,7,10,4096,73730,11,49160,67]),
([pw78,pw97,pw3,pw2,pw5,pw11],[444,500,212,1328,1352,1332,1336,1356,168,1248,1340,1344,1348,1360,1364,97,141,3],[524,32,264,73,96,7,1024,2051,4100,145,73744,19,129,49154,131075]),
([pw78,pw3,pw33,pw72,pw5],[76,1368,444,65,145,1372,1384,57,44,520,532,536,1376,1380,1388,13,93,141,3,7,75,103,107],[35,4609,8225,2097417,66582,131158,32786,1,4472972,1575112]),
([pw78,pw3,pw33,pw2,pw51,pw5],[76,500,89,1356,1392,1408,1428,44,212,532,536,1396,1400,1404,1412,1416,1420,1424,1432,97,141,149,3,7,75],[16,14368,161,49153,65553,131074,76,70,1048580,1,262912,10485762,17301506,4195336,1]),
([pw21,pw27,pw29,pw42,pw11,pw41],[77,432,1440,1444,1448,73,592,24,44,48,428,452,492,1436,1452,47,55,79,111,119,135,143,147,163],[8258,66,131204,32804,65541,1026,4194824,262184,524297,2097424,1048624,8388625,4096,2048,16385]),
([pw21,pw27,pw33,pw43,pw41],[120,212,53,69,44,568,572,1456,1460,24,48,112,116,160,304,584,1464,1468,1472,1476,1480,1484,1488,97,43,55,59,119,123,139,179,183],[48,65920,403970,109580549,17475,1048768,404750349,48,3225419790,553680911]),
([pw21,pw27,pw33,pw51,pw11,pw41],[1496,568,576,1504,1516,1528,1536,1540,24,48,156,1460,1484,1492,1500,1508,1512,1520,1524,1532,89,141,3,15,43,143,171,203],[8194,16385,33032,67585,10485768,1552,131073,68157456,266241,33554468,524288,134217824,16777348,2,4194496])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D4 : List StD := [
([pw84,pw29,pw18,pw11,pw41],[656,664,1576,1544,1548,3,976,1552,1556,1560,1564,1568,1572,1580,129,75],[216,296,1544,6160,16384,7,7,8226,32773,7]),
([pw80,pw98,pw5,pw11,pw41],[1596,212,496,372,572,656,0,192,1024,1544,1568,1584,1588,1592,1600,1604,1608,1612],[2256,12801,16401,1025,33028,6,12,35,196616,34]),
([pw84,pw2,pw5,pw11,pw41],[656,1004,1584,0,664,896,1556,1636,1544,1552,1616,1620,1624,1628,1632],[1036,776,6148,24580,67,146,35,35,145,67]),
([pw79,pw90,pw72,pw5,pw11],[496,76,372,872,896,332,888,892,948,1640,1644,1648,1652,1656,1660,1664,1668],[22,22,512,1024,2176,41,4161,257,8201,114688]),
([pw91,pw13,pw5,pw11,pw41],[656,664,1672,1680,1676,36,976,1584,1620,1624,1628,1632,117,3,47,55],[4096,100,772,3076,8209,16514,32785,8,11,11]),
([pw52,pw28,pw72,pw5,pw11],[1004,1636,372,1648,16,212,496,892,896,1592,1640,1644,1660,1684,1688,1692,153,157],[276,128,73730,131585,49156,1032,2056,67,35,4099]),
([pw80,pw3,pw29,pw33,pw41],[1708,500,44,76,368,1028,1036,1064,1556,1684,1696,1700,1704,1712,1716,1720,1724,1728,1732],[1024,2060,912,4097,8193,16385,3,32802,196610,262208]),
([pw25,pw93,pw33,pw5,pw41],[44,76,496,1712,1736,500,1304,1312,1324,1700,1740,1744,1748,1752,1756,1760,3],[515,1042,128,2058,4105,13,64,8212,16644,98336]),
([pw78,pw3,pw63,pw72,pw5],[488,1784,496,500,1064,1764,1068,1768,1772,1776,1780,1788,1792,1796,1800,1804],[32,112,1920,19,6144,10,8198,16385,32768,13]),
([pw25,pw53,pw33,pw51,pw41],[76,496,1808,1232,1256,1260,1536,1752,1812,1816,1820,1824,1828,1832,1836,1840,3,63],[261,517,49,1033,6144,8194,81922,130,131138,32768]),
([pw25,pw53,pw72,pw5,pw42],[496,1324,1756,76,372,444,896,1156,1172,1296,1844,1848,1852,1856,1860,1864,91],[3073,12289,16384,88,32774,3,3,257,517,65696]),
([pw82,pw53,pw33,pw5,pw41],[496,44,76,500,1264,372,1232,1252,1256,1260,1760,1868,141],[7,2053,388,528,18,3,4105,9,33,1096]),
([pw82,pw3,pw33,pw43,pw41],[120,1724,1880,76,1884,344,1200,1240,1712,1872,1876,1888,1892,1896,1900,1904],[128,552,74,1028,2068,258,5,12289,16400,32771]),
([pw78,pw96,pw33,pw5,pw41],[664,1636,44,76,1308,496,1296,1300,1304,1312,1324,1700,1736,1740,1748,1908,1912,1916,121,141,3],[2060,49344,262150,272,208896,528,524297,35,1027,1048579]),
([pw78,pw3,pw29,pw33,pw51],[496,500,76,1292,44,380,1428,1708,1920,1924,1928,1932,1936,1940,1944,1948,1952,3],[8,276,1544,14464,131137,16386,32771,7,65542,33]),
([pw78,pw97,pw3,pw2,pw43],[500,212,444,1328,1956,1960,1976,788,1964,1968,1972,1980],[11,16,168,273,3,512,1058,2116,65,5]),
([pw21,pw27,pw33,pw51,pw42],[336,496,1324,1420,1528,1904,1996,2004,2008,876,1484,1504,1508,1516,1984,1988,1992,2000,2012],[114720,131136,6146,386,8708,96,1033,20,400,262153])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D3 : List StD := [
([pw99,pw29,pw11,pw41],[656,664,1004,1676,2020,976,1628,1632,2016,2024,2028,2032],[312,3600,200,7,7,7]),
([pw84,pw29,pw100,pw41],[664,656,760,1004,1676,1556,1628,1632,2020,2024,2036,2040,2044],[1300,548,208,6145,11,11]),
([pw91,pw101,pw11,pw41],[1680,1552,2048,976,1568,1572,1676],[74,6,52,1,1,1]),
([pw25,pw93,pw33,pw51],[44,76,1708,1752,1920,1932,1952,2052,2056,2060,2064,2068,2072,2076],[19,386,578,3073,37,12296]),
([pw78,pw96,pw33,pw51],[44,76,1708,1920,1924,1928,1932,1936,1940,1952,2052,2056,2060,2064,2068,2080,2084,2088,2092,2096,2100,2104],[11,24624,452,101376,397824,3670016])]
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
theorem p16_I5 : LevelN true p16_T 5 p16_D5 := levelStep p16_B p16_W p16_I4 (chunks 32 p16_D5 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C5x0
  · exact p16_C5x1
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
def p17_T : Nat := 0xa8808000a8808000a8808000a8808000
def p17_R : List Nat := [0, 1, 2, 3, 4]
def p17_E : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15),(4,7,23)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
def p17_Z : List SliceD := [(pw3,7,[1, 2, 3, 4])]
theorem p17_Y : ∀ s ∈ p17_Z, SliceN true p17_R p17_T s := by
  unfold p17_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p17_B p7_B p7_L (by decide +kernel),by simp⟩
def p17_C : List (Nat × List Nat) := [(0,[])]
def p17_t : Tabs := (p17_C.map (mkCut true p17_Z),[],[],[])
theorem p17_W : TabsP true p17_R p17_T p17_t := ⟨cutsGood p17_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D7 : List StD := [
([pw3,pw2,pw5,pw11,pw41],[0],[1,1,1,1,1,1,1,1,1,1])]
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
def p18_T : Nat := 0xeaa8a880eaa8a880eaa8a880eaa8a880
def p18_R : List Nat := [0, 1, 2, 3, 4]
def p18_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11),(4,3,19)]
theorem p18_B : baseOK p18_T p18_R p18_E = true := by decide +kernel
def p18_Z : List SliceD := [(pw3,7,[1, 2, 3, 4]),(pw2,6,[0, 2, 3, 4]),(pw41,6,[0, 1, 2, 3]),(pw5,6,[0, 1, 3, 4]),(pw11,6,[0, 1, 2, 4]),(pw0,5,[0, 2, 3, 4]),(pw4,5,[0, 1, 3, 4]),(pw6,5,[0, 1, 2, 4]),(pw40,5,[0, 1, 2, 3]),(pw30,2,[0, 3, 4]),(pw43,2,[0, 1, 4])]
theorem p18_Y : ∀ s ∈ p18_Z, SliceN true p18_R p18_T s := by
  unfold p18_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p18_B p5_B p5_L (by decide +kernel),mkSlice (w:=2) p18_B p12_B p12_L (by decide +kernel),mkSlice (w:=16) p18_B p12_B p12_L (by decide +kernel),mkSlice (w:=4) p18_B p12_B p12_L (by decide +kernel),mkSlice (w:=8) p18_B p12_B p12_L (by decide +kernel),mkSlice (w:=0) p18_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p18_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p18_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p18_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p18_B p6_B p6_L (by decide +kernel),mkSlice (w:=12) p18_B p10_B p10_L (by decide +kernel),by simp⟩
def p18_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(0,[128]),(5,[]),(6,[]),(4,[260]),(2,[260]),(0,[131]),(7,[]),(8,[]),(5,[392]),(0,[392]),(6,[392]),(0,[392,130]),(0,[392,131]),(3,[392]),(1,[392]),(0,[128,394]),(5,[260]),(1,[260,401]),(6,[388]),(3,[388,273]),(9,[]),(10,[]),(7,[388]),(8,[392]),(2,[392,145])]
def p18_t : Tabs := (p18_C.map (mkCut true p18_Z),[(13,12),(7,4),(11,10),(7,6),(19,2),(11,9),(13,9),(7,3),(7,5),(13,5),(21,5),(19,3),(11,3),(25,9),(11,2),(30,22),(30,14),(25,24)],[],[[],[2],[3,2],[1,2],[1,3,2],[2,1,3,2],[2,1]])
theorem p18_W : TabsP true p18_R p18_T p18_t := ⟨cutsGood p18_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D8 : List StD := [
([pw3,pw2,pw5,pw11,pw41],[0,4,8,1,12,16,21,25,41,29,37,45,5,9,13,17,33,49,53,3,7,11,15,19,23],[4107,8201,16393,32781,525010,1115234,2099526,4326064,8391060,17040676])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D7 : List StD := [
([pw3,pw29,pw2,pw5,pw11,pw41],[24,12,20,28,32,36,13,61,4,65,8,16,40,44,48,17,45,49,57,3],[69,69,14,262228,32868,3,4099,10385,17953,11,401,801,10,10,721072])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D6 : List StD := [
([pw3,pw29,pw2,pw5,pw42,pw11,pw41],[52,13,60,72,32,69,48,76,4,8,16,20,36,44,56,64,68,80,27],[16387,3,6,2082,34,34,32768,65536,262209,9217,577,12,257,145,129,12,12,12,131072,16,4112])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D5 : List StD := [
([pw3,pw2,pw5,pw102,pw11,pw41],[84,88,92,96,104,108,0,100,112,116],[3,12,208,48,768,3,3,3,3,5,13,12,9,6,48])]
def p18_D4 : List StD := []
theorem p18_I4 : LevelN true p18_T 4 p18_D4 := by intro s h; cases h
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
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C8x0 : levelOK true p18_T p18_t 7 (p18_D7.map Prod.fst) ((p18_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I8 : LevelN true p18_T 8 p18_D8 := levelStep p18_B p18_W p18_I7 (chunks 32 p18_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C8x0
  ))
theorem p18_L : LowN true p18_R p18_T 9 := lowSearch p18_B p18_I8 (by decide +kernel)
def ptopT : Nat := 0xfe80e800e8808000fe80e800e8808000
def ptopR : List Nat := [0, 1, 2, 3, 4, 5]
def ptopE : List (Nat × Nat × Nat) := [(0,14,15),(1,13,15),(2,11,15),(3,7,15),(4,7,23),(5,11,43)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(pw3,9,[3, 2, 1, 4, 5]),(pw2,9,[3, 2, 0, 4, 5]),(pw5,9,[3, 1, 0, 4, 5]),(pw11,10,[0, 1, 2, 4, 5]),(pw41,9,[3, 1, 2, 0, 5]),(pw103,10,[0, 1, 2, 3, 4]),(pw1,8,[3, 2, 1, 4, 5]),(pw4,8,[3, 1, 0, 4, 5]),(pw40,8,[3, 1, 2, 0, 5]),(pw104,9,[3, 1, 2, 0, 4]),(pw0,8,[3, 2, 0, 4, 5]),(pw34,7,[1, 2, 4, 5]),(pw29,5,[3, 0, 4, 5]),(pw105,7,[1, 2, 3, 4]),(pw106,4,[0, 3, 4])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) ptopB p13_B p13_L (by decide +kernel),mkSlice (w:=2) ptopB p13_B p13_L (by decide +kernel),mkSlice (w:=4) ptopB p13_B p13_L (by decide +kernel),mkSlice (w:=8) ptopB p14_B p14_L (by decide +kernel),mkSlice (w:=16) ptopB p13_B p13_L (by decide +kernel),mkSlice (w:=0) ptopB p16_B p16_L (by decide +kernel),mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel),mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel),mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel),mkSlice (w:=32) ptopB p18_B p18_L (by decide +kernel),mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel),mkSlice (w:=8) ptopB p7_B p7_L (by decide +kernel),mkSlice (w:=6) ptopB p9_B p9_L (by decide +kernel),mkSlice (w:=1) ptopB p7_B p7_L (by decide +kernel),mkSlice (w:=6) ptopB p3_B p3_L (by decide +kernel),by simp⟩
def ptopC : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(3,[128]),(8,[]),(5,[128]),(9,[]),(10,[]),(4,[388]),(2,[260]),(3,[384]),(5,[515]),(5,[512]),(1,[392]),(2,[392]),(1,[388]),(0,[388]),(6,[388]),(7,[260]),(3,[392]),(3,[392,128]),(5,[520,128]),(9,[520]),(10,[388]),(5,[128,523]),(9,[388]),(8,[388]),(10,[392]),(0,[260,405]),(6,[260]),(2,[392,149]),(7,[392]),(1,[392,149]),(11,[128]),(12,[]),(4,[260,405]),(13,[128,401]),(14,[]),(8,[260])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[(29,28),(30,28),(15,13),(27,26),(30,26),(30,22),(15,6),(15,14),(30,14),(43,11),(46,14),(27,25),(29,25),(29,21),(29,13),(45,13),(27,19),(15,11),(27,11),(15,7),(43,3),(23,39),(23,7),(23,21),(23,19),(43,35)],[],[[],[1],[0,1],[0],[1,0]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD11 : List StD := [
([pw3,pw2,pw5,pw11,pw41,pw104],[0,4,8,12,20,21,16,37,1,5,9,17,41,3,13,25,29,33,45,49,53,57,61,65,69,73,77,81,85,7,11,15,19],[9987,536889605,32809,205121,4241,1074528774,1048618,2149582402,4194450,8388652,4345301060,4244,67108904,134217784,268435664])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD10 : List StD := [
([pw21,pw3,pw2,pw5,pw11,pw41,pw104],[24,4,0,32,40,48,77,52,56,61,65,69,89,8,12,16,28,36,44,37,73,81,85,3],[2,6,75777,16457,167937,262161,6,5,5,5,5,34,42,34,50,1096,9443712,525072,1096,2097240,4194960]),
([pw90,pw3,pw2,pw5,pw11,pw41,pw104],[36,16,60,68,0,24,65,76,72,37,61,93,97,4,8,12,28,44,48,64,45,49,53,81,11],[2,272385,86017,32837,524291,131081,48,48,52,3,56,19925376,4194372,3,1800,4292,3,1672,3,8388684,3])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD9 : List StD := [
([pw21,pw3,pw2,pw51,pw5,pw11,pw41,pw104],[92,88,80,52,84,100,104,112,77,56,8,16,36,48,96,108,116,120,124,53,81,19],[4,20,2097155,1027,16674,6154,32834,20,18,18,18,18,18,8197,133,164,140,196,9,524321,65545,131137,289,521,577,296,1048928,262216])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD8 : List StD := [
([pw3,pw2,pw107,pw5,pw11,pw41,pw104],[128,136,132,140,144,148,152,101,156,160,164,168,20,44,172],[7,7,6,6,7,6,3,25,33,33,33,26,448,5,12544,24,24,24,704,3264,19968])]
def ptopD7 : List StD := []
theorem ptopI7 : LevelN true ptopT 7 ptopD7 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x0 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI8 : LevelN true ptopT 8 ptopD8 := levelStep ptopB ptopW ptopI7 (chunks 32 ptopD8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC8x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x0 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI9 : LevelN true ptopT 9 ptopD9 := levelStep ptopB ptopW ptopI8 (chunks 32 ptopD9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC9x0
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

end PEqualNP.Outside.L_meta_12064

theorem PEqualNP.Outside.L_meta_12064 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860864 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  exact PEqualNP.Outside.L_meta_12064.replaceShort s h
