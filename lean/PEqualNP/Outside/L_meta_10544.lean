import PEqualNP.Defs

-- The live-set and restriction lemmas follow L-meta-10554, L-meta-10802, L-meta-1674, L-meta-670 and L-meta-1667.
namespace PEqualNP.Outside.L_meta_10544
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


def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [2, 5]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.or, [1, 11]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [2, 13]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.and, [12, 9]⟩,
    ⟨.and, [10, 14]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [18, 17]⟩], 19⟩

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
def w31 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaa
def w32 : Nat := 0xffffccccffffccccffffccccffffcccc
def w33 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0
def w34 : Nat := 0xffffff00ffffff00ffffff00ffffff00
def w35 : Nat := 0xeeee0000eeee0000eeee0000eeee
def w36 : Nat := 0x33333030333330303333303033333030
def w37 : Nat := 0x55555500555555005555550055555500
def w38 : Nat := 0xffffffff00000000ffffffff00000000
def w39 : Nat := 0x55005500550055005500550055005500
def w40 : Nat := 0x55550000555500005555000055550000
def w41 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaa
def w42 : Nat := 0x33003300330033003300330033003300
def w43 : Nat := 0x33330000333300003333000033330000
def w44 : Nat := 0xffffffffccccccccffffffffcccccccc
def w45 : Nat := 0xf000f000f000f000f000f000f000f00
def w46 : Nat := 0xf0f00000f0f00000f0f00000f0f0000
def w47 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0
def w48 : Nat := 0xf0f0f0f000000000f0f0f0f00000000
def w49 : Nat := 0xff000000ff000000ff000000ff000000
def w50 : Nat := 0xff000000ff000000ff000000ff00
def w51 : Nat := 0xff000000ff000000ff000000ff0000
def w52 : Nat := 0xffffffffff00ff00ffffffffff00ff00
def w53 : Nat := 0xff00ff0000000000ff00ff00
def w54 : Nat := 0xffffffffffff0000ffffffffffff0000
def w55 : Nat := 0xffff000000000000ffff0000
def w56 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeee
def w57 : Nat := 0xeeeeeeee00000000eeeeeeee
def w58 : Nat := 0x5000500050005000500050005000500
def w59 : Nat := 0xfffffafafffffafafffffafafffffafa
def w60 : Nat := 0xfafa0000fafa0000fafa0000fafa
def w61 : Nat := 0xffffffaaffffffaaffffffaaffffffaa
def w62 : Nat := 0xffaa0000ffaa0000ffaa0000ffaa
def w63 : Nat := 0xf5f0f5f0f5f0f5f0f5f0f5f0f5f0f5f0
def w64 : Nat := 0xffff5500ffff5500ffff5500ffff5500
def w65 : Nat := 0xffffffff55005500ffffffff55005500
def w66 : Nat := 0xddddccccddddccccddddccccddddcccc
def w67 : Nat := 0xf5f5f0f0f5f5f0f0f5f5f0f0f5f5f0f0
def w68 : Nat := 0xff55ff00ff55ff00ff55ff00ff55ff00
def w69 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfc
def w70 : Nat := 0xfcfc0000fcfc0000fcfc0000fcfc
def w71 : Nat := 0x3030000030300000303000003030000
def w72 : Nat := 0xffffffccffffffccffffffccffffffcc
def w73 : Nat := 0xbbaabbaabbaabbaabbaabbaabbaabbaa
def w74 : Nat := 0xf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0
def w75 : Nat := 0xffff3300ffff3300ffff3300ffff3300
def w76 : Nat := 0x55554444555544445555444455554444
def w77 : Nat := 0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c
def w78 : Nat := 0xff00cc00ff00cc00ff00cc00ff00cc
def w79 : Nat := 0xf3f3f0f0f3f3f0f0f3f3f0f0f3f3f0f0
def w80 : Nat := 0xff33ff00ff33ff00ff33ff00ff33ff00
def w81 : Nat := 0xffffffff33330000ffffffff33330000
def w82 : Nat := 0xfffffff0fffffff0fffffff0fffffff0
def w83 : Nat := 0xfff00000fff00000fff00000fff0
def w84 : Nat := 0xf0000000f0000000f0000000f0000
def w85 : Nat := 0xfffffffffff0fff0fffffffffff0fff0
def w86 : Nat := 0xafaaafaaafaaafaaafaaafaaafaaafaa
def w87 : Nat := 0xffff0f00ffff0f00ffff0f00ffff0f00
def w88 : Nat := 0x55555050555550505555505055555050
def w89 : Nat := 0xf0000000f0000000f0000000f00
def w90 : Nat := 0xff00f000ff00f000ff00f000ff00f0
def w91 : Nat := 0xfffffffffffff0f0fffffffffffff0f0
def w92 : Nat := 0xcfcfcccccfcfcccccfcfcccccfcfcccc
def w93 : Nat := 0xff0fff00ff0fff00ff0fff00ff0fff00
def w94 : Nat := 0xff00ff00f000f000ff00ff00f000f0
def w95 : Nat := 0xffff0000f0f00000ffff0000f0f0
def w96 : Nat := 0xff00ff00f000f000ff00ff00f000f000
def w97 : Nat := 0xffff0000f0f00000ffff0000f0f00000
def w98 : Nat := 0xffaaaaaaffaaaaaaffaaaaaaffaaaaaa
def w99 : Nat := 0xffccccccffccccccffccccccffcccccc
def w100 : Nat := 0xfff0f0f0fff0f0f0fff0f0f0fff0f0f0
def w101 : Nat := 0xffffffffff000000ffffffffff000000
def w102 : Nat := 0x33333300333333003333330033333300
def w103 : Nat := 0xf0f0f000f0f0f000f0f0f000f0f0f00
def w104 : Nat := 0xffffffffffffff00ffffffffffffff00
def w105 : Nat := 0xffffff0000000000ffffff00
def w106 : Nat := 0xaaaaffaaaaaaffaaaaaaffaaaaaaffaa
def w107 : Nat := 0xf0f0fff0f0f0fff0f0f0fff0f0f0fff0
def w108 : Nat := 0xccffccccccffccccccffccccccffcccc
def w109 : Nat := 0xf0fff0f0f0fff0f0f0fff0f0f0fff0f0
def w110 : Nat := 0xaaaaaaaaffaaffaaaaaaaaaaffaaffaa
def w111 : Nat := 0xf0f0f0f0fff0fff0f0f0f0f0fff0fff0
def w112 : Nat := 0xffff0000ffffff00ffff0000ffffff00
def w113 : Nat := 0xccccccccffffccccccccccccffffcccc
def w114 : Nat := 0xf0f0f0f0fffff0f0f0f0f0f0fffff0f0
def w115 : Nat := 0xff00ff00ffffff00ff00ff00ffffff00
def w116 : Nat := 0xfffefffefffefffefffefffefffefffe
def w117 : Nat := 0xfffffefefffffefefffffefefffffefe
def w118 : Nat := 0xfefe0000fefe0000fefe0000fefe
def w119 : Nat := 0xffffffeeffffffeeffffffeeffffffee
def w120 : Nat := 0xffee0000ffee0000ffee0000ffee
def w121 : Nat := 0xf0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e
def w122 : Nat := 0xff00ee00ff00ee00ff00ee00ff00ee
def w123 : Nat := 0xf0f0f0f0fefefefef0f0f0f0fefefefe
def w124 : Nat := 0xf000f000f000f000f000f000f000f0
def w125 : Nat := 0xf0f00000f0f00000f0f00000f0f0
def w126 : Nat := 0x11111100111111001111110011111100
def w127 : Nat := 0xff32ff32ff32ff32ff32ff32ff32ff32
def w128 : Nat := 0xffff3232ffff3232ffff3232ffff3232
def w129 : Nat := 0xfbfafbfafbfafbfafbfafbfafbfafbfa
def w130 : Nat := 0xfffa0000fffa0000fffa0000fffa
def w131 : Nat := 0xfffa0000fffa0000fffa0000fffa0000
def w132 : Nat := 0xfffffffafffffffafffffffafffffffa
def w133 : Nat := 0xccfeccfeccfeccfeccfeccfeccfeccfe
def w134 : Nat := 0xffff00faffff00faffff00faffff00fa
def w135 : Nat := 0x33333232333332323333323233333232
def w136 : Nat := 0xff00fa00ff00fa00ff00fa00ff00fa
def w137 : Nat := 0xccccfefeccccfefeccccfefeccccfefe
def w138 : Nat := 0xff00fffaff00fffaff00fffaff00fffa
def w139 : Nat := 0x5050500050505000505050005050500
def w140 : Nat := 0xfafafffafafafffafafafffafafafffa
def w141 : Nat := 0xf3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2
def w142 : Nat := 0xffff3322ffff3322ffff3322ffff3322
def w143 : Nat := 0xcfcecfcecfcecfcecfcecfcecfcecfce
def w144 : Nat := 0xffff0f0affff0f0affff0f0affff0f0a
def w145 : Nat := 0x33333322333333223333332233333322
def w146 : Nat := 0xf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a
def w147 : Nat := 0xccccffeeccccffeeccccffeeccccffee
def w148 : Nat := 0xf0f0fffaf0f0fffaf0f0fffaf0f0fffa
def w149 : Nat := 0xfffff5f0fffff5f0fffff5f0fffff5f0
def w150 : Nat := 0xf0f05000f0f05000f0f05000f0f0500
def w151 : Nat := 0xaaffaaffa0f0a0f0aaffaaffa0f0a0f0
def w152 : Nat := 0xffffbbaaffffbbaaffffbbaaffffbbaa
def w153 : Nat := 0xffffafaaffffafaaffffafaaffffafaa
def w154 : Nat := 0xfdfdfcfcfdfdfcfcfdfdfcfcfdfdfcfc
def w155 : Nat := 0xffddffccffddffccffddffccffddffcc
def w156 : Nat := 0xfff5fff0fff5fff0fff5fff0fff5fff0
def w157 : Nat := 0x33113300331133003311330033113300
def w158 : Nat := 0xf050f000f050f000f050f000f050f00
def w159 : Nat := 0x77553300775533007755330077553300
def w160 : Nat := 0x5f550f005f550f005f550f005f550f00
def w161 : Nat := 0xff54ff54ff54ff54ff54ff54ff54ff54
def w162 : Nat := 0xffff5454ffff5454ffff5454ffff5454
def w163 : Nat := 0xfffffffcfffffffcfffffffcfffffffc
def w164 : Nat := 0xfffc0000fffc0000fffc0000fffc
def w165 : Nat := 0xaafeaafeaafeaafeaafeaafeaafeaafe
def w166 : Nat := 0xffff00fcffff00fcffff00fcffff00fc
def w167 : Nat := 0xff00fc00ff00fc00ff00fc00ff00fc
def w168 : Nat := 0x55555454555554545555545455555454
def w169 : Nat := 0xff00fc00ff00fc00ff00fc00ff00fc00
def w170 : Nat := 0xaaaafefeaaaafefeaaaafefeaaaafefe
def w171 : Nat := 0xff00fffcff00fffcff00fffcff00fffc
def w172 : Nat := 0x3030300030303000303030003030300
def w173 : Nat := 0xfcfffcfcfcfffcfcfcfffcfcfcfffcfc
def w174 : Nat := 0xffcfffccffcfffccffcfffccffcfffcc
def w175 : Nat := 0x55555544555555445555554455555544
def w176 : Nat := 0xf0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c
def w177 : Nat := 0xfffff3f0fffff3f0fffff3f0fffff3f0
def w178 : Nat := 0x55551100555511005555110055551100
def w179 : Nat := 0xf0f03000f0f03000f0f03000f0f0300
def w180 : Nat := 0x3f0f33003f0f33003f0f33003f0f3300
def w181 : Nat := 0xf5f5f4f4f5f5f4f4f5f5f4f4f5f5f4f4
def w182 : Nat := 0xff55ff44ff55ff44ff55ff44ff55ff44
def w183 : Nat := 0xafafaeaeafafaeaeafafaeaeafafaeae
def w184 : Nat := 0xff0fff0cff0fff0cff0fff0cff0fff0c
def w185 : Nat := 0xaaffaaeeaaffaaeeaaffaaeeaaffaaee
def w186 : Nat := 0xf0fff0fcf0fff0fcf0fff0fcf0fff0fc
def w187 : Nat := 0xfff3fff0fff3fff0fff3fff0fff3fff0
def w188 : Nat := 0xf030f000f030f000f030f000f030f00
def w189 : Nat := 0xccccffffc0c0f0f0ccccffffc0c0f0f0
def w190 : Nat := 0xdddcdddcdddcdddcdddcdddcdddcdddc
def w191 : Nat := 0xffff5550ffff5550ffff5550ffff5550
def w192 : Nat := 0xbbbabbbabbbabbbabbbabbbabbbabbba
def w193 : Nat := 0xffff3330ffff3330ffff3330ffff3330
def w194 : Nat := 0x55555550555555505555555055555550
def w195 : Nat := 0x33333330333333303333333033333330
def w196 : Nat := 0xaaaafffaaaaafffaaaaafffaaaaafffa
def w197 : Nat := 0xccccfffcccccfffcccccfffcccccfffc
def w198 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000
def w199 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
def w200 : Nat := 0x33333333333033303333333333303330
def w201 : Nat := 0xfff0fff0fffffff0fff0fff0fffffff0
def w202 : Nat := 0x55550500555505005555050055550500
def w203 : Nat := 0xdddddcdcdddddcdcdddddcdcdddddcdc
def w204 : Nat := 0xff55ff50ff55ff50ff55ff50ff55ff50
def w205 : Nat := 0xbbbbbababbbbbababbbbbababbbbbaba
def w206 : Nat := 0xff33ff30ff33ff30ff33ff30ff33ff30
def w207 : Nat := 0xaaffaafaaaffaafaaaffaafaaaffaafa
def w208 : Nat := 0xccffccfcccffccfcccffccfcccffccfc
def w209 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00
def w210 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc
def w211 : Nat := 0xfffff0f0fffffff0fffff0f0fffffff0
def w212 : Nat := 0x55555555555550505555555555555050
def w213 : Nat := 0x33033300330333003303330033033300
def w214 : Nat := 0xffff00ffffff00f0ffff00ffffff00f0
def w215 : Nat := 0xff00ffffff00fff0ff00ffffff00fff0
def w216 : Nat := 0xffffff00f0f0f000ffffff00f0f0f0
def w217 : Nat := 0xffffff00fffff000ffffff00fffff000
def w218 : Nat := 0xffffff00fff0ff00ffffff00fff0ff00
def w219 : Nat := 0xfffffffffff0f0f0fffffffffff0f0f0
def w220 : Nat := 0xddddddccddddddccddddddccddddddcc
def w221 : Nat := 0xf5f5f5f0f5f5f5f0f5f5f5f0f5f5f5f0
def w222 : Nat := 0xbbbbbbaabbbbbbaabbbbbbaabbbbbbaa
def w223 : Nat := 0xf3f3f3f0f3f3f3f0f3f3f3f0f3f3f3f0
def w224 : Nat := 0xafafafaaafafafaaafafafaaafafafaa
def w225 : Nat := 0xcfcfcfcccfcfcfcccfcfcfcccfcfcfcc
def w226 : Nat := 0xf0f00000f0f0f000f0f00000f0f0f00
def w227 : Nat := 0xf000f000f0f0f000f000f000f0f0f00
def w228 : Nat := 0xfffe0000fffe0000fffe0000fffe
def w229 : Nat := 0xff00fe00ff00fe00ff00fe00ff00fe
def w230 : Nat := 0xf0f0f0e0f0f0f0e0f0f0f0e0f0f0f0e
def w231 : Nat := 0xf000f0eefeeefe00f000f0eefeeefe
def w232 : Nat := 0xf0f0eeeefefe0000f0f0eeeefefe
def w233 : Nat := 0xfbfa0000fbfa0000fbfa0000fbfa
def w234 : Nat := 0xfd00fc00fd00fc00fd00fc00fd00fc
def w235 : Nat := 0xbbba0000bbba0000bbba0000bbba
def w236 : Nat := 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0
def w237 : Nat := 0xffaaff00ffaaff00ffaaff00ffaaff00
def w238 : Nat := 0xffffffffaaaa0000ffffffffaaaa0000
def w239 : Nat := 0xdd00dc00dd00dc00dd00dc00dd00dc
def w240 : Nat := 0xfcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0
def w241 : Nat := 0xffffcc00ffffcc00ffffcc00ffffcc00
def w242 : Nat := 0xffffffffcc00cc00ffffffffcc00cc00
def w243 : Nat := 0xffffffffffffffff0000000000000000
def w244 : Nat := 0x22222222222222222222222222222222
def w245 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def w246 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def w247 : Nat := 0x50505050505050505050505050505050
def w248 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa
def w249 : Nat := 0x30303030303030303030303030303030
def w250 : Nat := 0xffff2222ffff2222ffff2222ffff2222
def w251 : Nat := 0xecececececececececececececececec
def w252 : Nat := 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0
def w253 : Nat := 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0
def w254 : Nat := 0xffffffffa0a0a0a0ffffffffa0a0a0a0
def w255 : Nat := 0xffffffffffffffffa0a0a0a0a0a0a0a0
def w256 : Nat := 0xff0aff0aff0aff0aff0aff0aff0aff0a
def w257 : Nat := 0xffff5050ffff5050ffff5050ffff5050
def w258 : Nat := 0xcccceeeecccceeeecccceeeecccceeee
def w259 : Nat := 0xff30ff30ff30ff30ff30ff30ff30ff30
def w260 : Nat := 0xccfcccfcccfcccfcccfcccfcccfcccfc
def w261 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaa
def w262 : Nat := 0xffffffffffffffffcccccccccccccccc
def w263 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0
def w264 : Nat := 0xfffffffffffffffffefefefefefefefe
def w265 : Nat := 0xfefefefefefefefe
def w266 : Nat := 0xffffffffffffffffff00ff00ff00ff00
def w267 : Nat := 0xffffffffffffffff0f0a0f0a0f0a0f0a
def w268 : Nat := 0xffffffff55555050ffffffff55555050
def w269 : Nat := 0xffffffff00000000fffffffffefefefe
def w270 : Nat := 0xffffffffffffffffffffffff00000000
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
def p6_T : Nat := 0xfeeefee8feeefee8feeefee8feeefee8
def p6_R : List Nat := [0, 1, 2, 3, 4]
def p6_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
theorem p6_S0 : SliceN p6_R p6_T (0xffff0000ffff0000ffff0000ffff,7,[0, 1, 2, 3]) := mkSlice (w:=0) p6_B p5_B p5_L (by decide +kernel)
def p6_Z : List SliceD := [(0xffff0000ffff0000ffff0000ffff,7,[0, 1, 2, 3])]
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
def p8_T : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def p8_R : List Nat := [0, 1, 2]
def p8_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
theorem p8_L : LowN p8_R p8_T 2 := lowCount p8_B (by decide +kernel)
def p9_T : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8
def p9_R : List Nat := [0, 1, 2, 3]
def p9_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
theorem p9_S0 : SliceN p9_R p9_T (0x3030303030303030303030303030303,1,[0, 3]) := mkSlice (w:=0) p9_B p1_B p1_L (by decide +kernel)
theorem p9_S1 : SliceN p9_R p9_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]) := mkSlice (w:=1) p9_B p2_B p2_L (by decide +kernel)
theorem p9_S2 : SliceN p9_R p9_T (0x550055005500550055005500550055,1,[1, 2]) := mkSlice (w:=0) p9_B p1_B p1_L (by decide +kernel)
theorem p9_S3 : SliceN p9_R p9_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[1, 0, 3]) := mkSlice (w:=4) p9_B p7_B p7_L (by decide +kernel)
theorem p9_S4 : SliceN p9_R p9_T (0xff00ff00ff00ff00ff00ff00ff00ff,2,[1, 0, 2]) := mkSlice (w:=0) p9_B p8_B p8_L (by decide +kernel)
theorem p9_S5 : SliceN p9_R p9_T (0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]) := mkSlice (w:=8) p9_B p7_B p7_L (by decide +kernel)
def p9_Z : List SliceD := [(0x3030303030303030303030303030303,1,[0, 3]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]),(0x550055005500550055005500550055,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[1, 0, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,2,[1, 0, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨p9_S0,p9_S1,p9_S2,p9_S3,p9_S4,p9_S5,by simp⟩
def p9_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def p9_P : List (Nat × Nat) := []
def p9_K : List CutV := p9_C.map (mkCut p9_Z)
theorem p9_W : ∀ c ∈ p9_K, CutP p9_R p9_T c := cutsGood p9_Y (by decide +kernel)
theorem p9_Q : p9_P.all (sepOK p9_T) = true := by decide +kernel
noncomputable def p9_D3 : List StD := [
([w0,w1,w2,w3],[0,1,2,3,4,5],[],[[0,1,2],[0,3],[4,1,5],[1,3],[0,5,2],[0,3]])]
def p9_D2 : List StD := []
theorem p9_I2 : LevelN p9_R p9_T 2 p9_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C3x0 : levelOK p9_T p9_K p9_P 2 (p9_D2.map Prod.fst) ((p9_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem p9_I3 : LevelN p9_R p9_T 3 p9_D3 := levelStep p9_B p9_W p9_Q p9_I2 (chunks 16 p9_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C3x0
  ))
theorem p9_L : LowN p9_R p9_T 4 := lowSearch p9_B p9_I3 (by decide +kernel)
def p10_T : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8
def p10_R : List Nat := [0, 1, 2, 3]
def p10_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
theorem p10_S0 : SliceN p10_R p10_T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]) := mkSlice (w:=0) p10_B p3_B p3_L (by decide +kernel)
def p10_Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2])]
theorem p10_Y : ∀ s ∈ p10_Z, SliceN p10_R p10_T s := by
  unfold p10_Z
  simp only [List.forall_mem_cons]
  exact ⟨p10_S0,by simp⟩
def p10_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def p10_P : List (Nat × Nat) := []
def p10_K : List CutV := p10_C.map (mkCut p10_Z)
theorem p10_W : ∀ c ∈ p10_K, CutP p10_R p10_T c := cutsGood p10_Y (by decide +kernel)
theorem p10_Q : p10_P.all (sepOK p10_T) = true := by decide +kernel
noncomputable def p10_D4 : List StD := [
([w0,w1,w2,w3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def p10_D3 : List StD := []
theorem p10_I3 : LevelN p10_R p10_T 3 p10_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p10_C4x0 : levelOK p10_T p10_K p10_P 3 (p10_D3.map Prod.fst) ((p10_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem p10_I4 : LevelN p10_R p10_T 4 p10_D4 := levelStep p10_B p10_W p10_Q p10_I3 (chunks 16 p10_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C4x0
  ))
theorem p10_L : LowN p10_R p10_T 5 := lowSearch p10_B p10_I4 (by decide +kernel)
def p11_T : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
def p11_R : List Nat := [0, 1, 2, 3]
def p11_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
theorem p11_S0 : SliceN p11_R p11_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) p11_B p3_B p3_L (by decide +kernel)
def p11_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3])]
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
def p12_T : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
def p12_R : List Nat := [0, 1, 2, 3]
def p12_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
theorem p12_S0 : SliceN p12_R p12_T (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) p12_B p3_B p3_L (by decide +kernel)
def p12_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3])]
theorem p12_Y : ∀ s ∈ p12_Z, SliceN p12_R p12_T s := by
  unfold p12_Z
  simp only [List.forall_mem_cons]
  exact ⟨p12_S0,by simp⟩
def p12_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def p12_P : List (Nat × Nat) := []
def p12_K : List CutV := p12_C.map (mkCut p12_Z)
theorem p12_W : ∀ c ∈ p12_K, CutP p12_R p12_T c := cutsGood p12_Y (by decide +kernel)
theorem p12_Q : p12_P.all (sepOK p12_T) = true := by decide +kernel
noncomputable def p12_D4 : List StD := [
([w0,w1,w2,w3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def p12_D3 : List StD := []
theorem p12_I3 : LevelN p12_R p12_T 3 p12_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C4x0 : levelOK p12_T p12_K p12_P 3 (p12_D3.map Prod.fst) ((p12_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem p12_I4 : LevelN p12_R p12_T 4 p12_D4 := levelStep p12_B p12_W p12_Q p12_I3 (chunks 16 p12_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C4x0
  ))
theorem p12_L : LowN p12_R p12_T 5 := lowSearch p12_B p12_I4 (by decide +kernel)
def p13_T : Nat := 0xfeeefeeefeeefeeefeeefeeefeeefeee
def p13_R : List Nat := [0, 1, 2, 3]
def p13_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
theorem p13_L : LowN p13_R p13_T 3 := lowCount p13_B (by decide +kernel)
def p14_T : Nat := 0xfeeafce8feeafce8feeafce8feeafce8
def p14_R : List Nat := [0, 1, 2, 3, 4]
def p14_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
theorem p14_S0 : SliceN p14_R p14_T (0x33333333333333333333333333333333,4,[0, 2, 3, 4]) := mkSlice (w:=0) p14_B p9_B p9_L (by decide +kernel)
theorem p14_S1 : SliceN p14_R p14_T (0x5555000055550000555500005555,4,[1, 2, 3]) := mkSlice (w:=0) p14_B p3_B p3_L (by decide +kernel)
theorem p14_S2 : SliceN p14_R p14_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3, 4]) := mkSlice (w:=0) p14_B p9_B p9_L (by decide +kernel)
theorem p14_S3 : SliceN p14_R p14_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p14_B p10_B p10_L (by decide +kernel)
theorem p14_S4 : SliceN p14_R p14_T (0xffff0000ffff0000ffff0000ffff,5,[1, 2, 0, 3]) := mkSlice (w:=0) p14_B p11_B p11_L (by decide +kernel)
theorem p14_S5 : SliceN p14_R p14_T (0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) p14_B p12_B p12_L (by decide +kernel)
theorem p14_S6 : SliceN p14_R p14_T (0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]) := mkSlice (w:=2) p14_B p4_B p4_L (by decide +kernel)
theorem p14_S7 : SliceN p14_R p14_T (0xf0f00000f0f00000f0f00000f0f0,2,[0, 1, 3]) := mkSlice (w:=4) p14_B p4_B p4_L (by decide +kernel)
theorem p14_S8 : SliceN p14_R p14_T (0x30003000300030003000300030003,1,[0, 4]) := mkSlice (w:=0) p14_B p1_B p1_L (by decide +kernel)
theorem p14_S9 : SliceN p14_R p14_T (0x3000300030003000300030003000300,1,[0, 4]) := mkSlice (w:=8) p14_B p1_B p1_L (by decide +kernel)
theorem p14_S10 : SliceN p14_R p14_T (0xcc000000cc000000cc000000cc,1,[0, 2]) := mkSlice (w:=2) p14_B p2_B p2_L (by decide +kernel)
theorem p14_S11 : SliceN p14_R p14_T (0xff00ff00ff00ff00ff00ff00ff00ff00,3,[1, 2, 0, 4]) := mkSlice (w:=8) p14_B p13_B p13_L (by decide +kernel)
theorem p14_S12 : SliceN p14_R p14_T (0xaa00aa00aa00aa00aa00aa00aa00aa00,2,[1, 2, 4]) := mkSlice (w:=9) p14_B p4_B p4_L (by decide +kernel)
theorem p14_S13 : SliceN p14_R p14_T (0xcccc0000cccc0000cccc0000cccc0000,2,[0, 2, 3]) := mkSlice (w:=18) p14_B p4_B p4_L (by decide +kernel)
theorem p14_S14 : SliceN p14_R p14_T (0xf0f00000f0f00000f0f00000f0f00000,2,[0, 1, 3]) := mkSlice (w:=20) p14_B p4_B p4_L (by decide +kernel)
def p14_Z : List SliceD := [(0x33333333333333333333333333333333,4,[0, 2, 3, 4]),(0x5555000055550000555500005555,4,[1, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff,5,[1, 2, 0, 3]),(0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]),(0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]),(0xf0f00000f0f00000f0f00000f0f0,2,[0, 1, 3]),(0x30003000300030003000300030003,1,[0, 4]),(0x3000300030003000300030003000300,1,[0, 4]),(0xcc000000cc000000cc000000cc,1,[0, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff00,3,[1, 2, 0, 4]),(0xaa00aa00aa00aa00aa00aa00aa00aa00,2,[1, 2, 4]),(0xcccc0000cccc0000cccc0000cccc0000,2,[0, 2, 3]),(0xf0f00000f0f00000f0f00000f0f00000,2,[0, 1, 3])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨p14_S0,p14_S1,p14_S2,p14_S3,p14_S4,p14_S5,p14_S6,p14_S7,p14_S8,p14_S9,p14_S10,p14_S11,p14_S12,p14_S13,p14_S14,by simp⟩
def p14_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(5,[(1,1,2)]),(10,[]),(11,[]),(3,[(1,1,2)]),(0,[(2,1,2)]),(2,[(2,1,2)]),(12,[]),(13,[]),(14,[])]
def p14_P : List (Nat × Nat) := [(2,3),(0,3),(4,5),(17,24),(1,3),(4,6),(2,6),(2,10),(0,10),(4,12)]
def p14_K : List CutV := p14_C.map (mkCut p14_Z)
theorem p14_W : ∀ c ∈ p14_K, CutP p14_R p14_T c := cutsGood p14_Y (by decide +kernel)
theorem p14_Q : p14_P.all (sepOK p14_T) = true := by decide +kernel
noncomputable def p14_D6 : List StD := [
([w0,w1,w2,w3,w30],[0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8,9],[[0,1,100,101],[1,102,2,100],[1,3,103],[1,4,5],[0,2,104,105,106],[0,3,107,108],[0,1,5],[2,3,109,107],[1,5],[1,3,5]])]
noncomputable def p14_D5 : List StD := [
([w0,w1,w2,w7,w3,w30],[0,6,2,7,1,8,9,10,3],[],[[0,1],[2,3],[4,1,5],[5,6],[1,7],[0,1],[2],[0,1],[0,7,3],[0],[2,3],[1,7],[8,1],[4,7],[1,6,5]])]
noncomputable def p14_D4 : List StD := [
([w21,w0,w1,w2,w30],[1,11,12,13,5,14,15,7,16,17,18],[],[[0,1,2],[2,3],[2,1],[0,4],[5,1],[6,7],[1,8,9],[5,1],[5,10,7],[1,9]])]
def p14_D3 : List StD := []
theorem p14_I3 : LevelN p14_R p14_T 3 p14_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C4x0 : levelOK p14_T p14_K p14_P 3 (p14_D3.map Prod.fst) ((p14_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem p14_I4 : LevelN p14_R p14_T 4 p14_D4 := levelStep p14_B p14_W p14_Q p14_I3 (chunks 16 p14_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C5x0 : levelOK p14_T p14_K p14_P 4 (p14_D4.map Prod.fst) ((p14_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem p14_I5 : LevelN p14_R p14_T 5 p14_D5 := levelStep p14_B p14_W p14_Q p14_I4 (chunks 16 p14_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C6x0 : levelOK p14_T p14_K p14_P 5 (p14_D5.map Prod.fst) ((p14_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem p14_I6 : LevelN p14_R p14_T 6 p14_D6 := levelStep p14_B p14_W p14_Q p14_I5 (chunks 16 p14_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C6x0
  ))
theorem p14_L : LowN p14_R p14_T 7 := lowSearch p14_B p14_I6 (by decide +kernel)
def p15_T : Nat := 0xfeeefac0feeefac0feeefac0feeefac0
def p15_R : List Nat := [0, 1, 2, 3, 4]
def p15_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17)]
theorem p15_B : baseOK p15_T p15_R p15_E = true := by decide +kernel
theorem p15_S0 : SliceN p15_R p15_T (0x55555555555555555555555555555555,4,[1, 2, 3, 4]) := mkSlice (w:=0) p15_B p9_B p9_L (by decide +kernel)
theorem p15_S1 : SliceN p15_R p15_T (0x33333333333333333333333333333333,4,[0, 3, 2, 4]) := mkSlice (w:=0) p15_B p9_B p9_L (by decide +kernel)
theorem p15_S2 : SliceN p15_R p15_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 4, 1, 3]) := mkSlice (w:=0) p15_B p9_B p9_L (by decide +kernel)
theorem p15_S3 : SliceN p15_R p15_T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[1, 4, 0, 2]) := mkSlice (w:=0) p15_B p9_B p9_L (by decide +kernel)
theorem p15_S4 : SliceN p15_R p15_T (0xffff0000ffff0000ffff0000ffff,4,[2, 3, 0, 1]) := mkSlice (w:=0) p15_B p9_B p9_L (by decide +kernel)
theorem p15_S5 : SliceN p15_R p15_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,3,[3, 4, 1, 2]) := mkSlice (w:=1) p15_B p13_B p13_L (by decide +kernel)
theorem p15_S6 : SliceN p15_R p15_T (0xcccccccccccccccccccccccccccccccc,3,[2, 4, 3, 0]) := mkSlice (w:=2) p15_B p13_B p13_L (by decide +kernel)
theorem p15_S7 : SliceN p15_R p15_T (0x1111000011110000111100001111,1,[2, 3]) := mkSlice (w:=0) p15_B p1_B p1_L (by decide +kernel)
theorem p15_S8 : SliceN p15_R p15_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[4, 3, 0]) := mkSlice (w:=2) p15_B p7_B p7_L (by decide +kernel)
theorem p15_S9 : SliceN p15_R p15_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,2,[1, 3, 4]) := mkSlice (w:=5) p15_B p4_B p4_L (by decide +kernel)
theorem p15_S10 : SliceN p15_R p15_T (0xcc00cc00cc00cc00cc00cc00cc00cc00,2,[0, 2, 4]) := mkSlice (w:=10) p15_B p4_B p4_L (by decide +kernel)
theorem p15_S11 : SliceN p15_R p15_T (0xaa00aa00aa00aa00aa00aa00aa00aa,2,[4, 2, 1]) := mkSlice (w:=1) p15_B p7_B p7_L (by decide +kernel)
theorem p15_S12 : SliceN p15_R p15_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,3,[1, 3, 0, 4]) := mkSlice (w:=4) p15_B p13_B p13_L (by decide +kernel)
theorem p15_S13 : SliceN p15_R p15_T (0x50005000500050005000500050005,1,[1, 4]) := mkSlice (w:=0) p15_B p1_B p1_L (by decide +kernel)
theorem p15_S14 : SliceN p15_R p15_T (0x88888888888888888888888888888888,2,[2, 3, 4]) := mkSlice (w:=3) p15_B p4_B p4_L (by decide +kernel)
theorem p15_S15 : SliceN p15_R p15_T (0x30303030303030303030303030303030,2,[3, 0, 4]) := mkSlice (w:=4) p15_B p7_B p7_L (by decide +kernel)
theorem p15_S16 : SliceN p15_R p15_T (0xf0f00000f0f00000f0f00000f0f00000,2,[0, 1, 3]) := mkSlice (w:=20) p15_B p4_B p4_L (by decide +kernel)
theorem p15_S17 : SliceN p15_R p15_T (0xaaaa0000aaaa0000aaaa0000aaaa,2,[3, 2, 1]) := mkSlice (w:=1) p15_B p7_B p7_L (by decide +kernel)
theorem p15_S18 : SliceN p15_R p15_T (0xff00ff00ff00ff00ff00ff00ff00ff00,3,[0, 2, 1, 4]) := mkSlice (w:=8) p15_B p13_B p13_L (by decide +kernel)
theorem p15_S19 : SliceN p15_R p15_T (0xff000000ff000000ff000000ff000000,2,[0, 1, 2]) := mkSlice (w:=24) p15_B p4_B p4_L (by decide +kernel)
theorem p15_S20 : SliceN p15_R p15_T (0x550055005500550055005500550055,2,[1, 2, 4]) := mkSlice (w:=0) p15_B p8_B p8_L (by decide +kernel)
theorem p15_S21 : SliceN p15_R p15_T (0x5555000055550000555500005555,2,[2, 1, 3]) := mkSlice (w:=0) p15_B p8_B p8_L (by decide +kernel)
theorem p15_S22 : SliceN p15_R p15_T (0xffff0000ffff0000ffff0000ffff0000,3,[0, 1, 2, 3]) := mkSlice (w:=16) p15_B p13_B p13_L (by decide +kernel)
theorem p15_S23 : SliceN p15_R p15_T (0x3030303030303030303030303030303,2,[0, 3, 4]) := mkSlice (w:=0) p15_B p8_B p8_L (by decide +kernel)
theorem p15_S24 : SliceN p15_R p15_T (0xf000f000f000f000f000f000f000f0,2,[1, 0, 4]) := mkSlice (w:=4) p15_B p7_B p7_L (by decide +kernel)
theorem p15_S25 : SliceN p15_R p15_T (0xcccc0000cccc0000cccc0000cccc,2,[2, 0, 3]) := mkSlice (w:=2) p15_B p7_B p7_L (by decide +kernel)
theorem p15_S26 : SliceN p15_R p15_T (0x55005500550055005500550055005500,2,[2, 1, 4]) := mkSlice (w:=8) p15_B p7_B p7_L (by decide +kernel)
theorem p15_S27 : SliceN p15_R p15_T (0x30003000300030003000300030003,1,[0, 4]) := mkSlice (w:=0) p15_B p1_B p1_L (by decide +kernel)
theorem p15_S28 : SliceN p15_R p15_T (0x3333000033330000333300003333,2,[3, 2, 0]) := mkSlice (w:=0) p15_B p8_B p8_L (by decide +kernel)
theorem p15_S29 : SliceN p15_R p15_T (0x55550000555500005555000055550000,2,[1, 2, 3]) := mkSlice (w:=16) p15_B p7_B p7_L (by decide +kernel)
theorem p15_S30 : SliceN p15_R p15_T (0x303000003030000030300000303,1,[0, 3]) := mkSlice (w:=0) p15_B p1_B p1_L (by decide +kernel)
theorem p15_S31 : SliceN p15_R p15_T (0x33330000333300003333000033330000,2,[0, 2, 3]) := mkSlice (w:=16) p15_B p7_B p7_L (by decide +kernel)
theorem p15_S32 : SliceN p15_R p15_T (0xf000f000f000f000f000f000f000f00,2,[0, 1, 4]) := mkSlice (w:=8) p15_B p7_B p7_L (by decide +kernel)
theorem p15_S33 : SliceN p15_R p15_T (0x55000000550000005500000055,1,[1, 2]) := mkSlice (w:=0) p15_B p1_B p1_L (by decide +kernel)
def p15_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3, 4]),(0x33333333333333333333333333333333,4,[0, 3, 2, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 4, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,4,[1, 4, 0, 2]),(0xffff0000ffff0000ffff0000ffff,4,[2, 3, 0, 1]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,3,[3, 4, 1, 2]),(0xcccccccccccccccccccccccccccccccc,3,[2, 4, 3, 0]),(0x1111000011110000111100001111,1,[2, 3]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[4, 3, 0]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,2,[1, 3, 4]),(0xcc00cc00cc00cc00cc00cc00cc00cc00,2,[0, 2, 4]),(0xaa00aa00aa00aa00aa00aa00aa00aa,2,[4, 2, 1]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,3,[1, 3, 0, 4]),(0x50005000500050005000500050005,1,[1, 4]),(0x88888888888888888888888888888888,2,[2, 3, 4]),(0x30303030303030303030303030303030,2,[3, 0, 4]),(0xf0f00000f0f00000f0f00000f0f00000,2,[0, 1, 3]),(0xaaaa0000aaaa0000aaaa0000aaaa,2,[3, 2, 1]),(0xff00ff00ff00ff00ff00ff00ff00ff00,3,[0, 2, 1, 4]),(0xff000000ff000000ff000000ff000000,2,[0, 1, 2]),(0x550055005500550055005500550055,2,[1, 2, 4]),(0x5555000055550000555500005555,2,[2, 1, 3]),(0xffff0000ffff0000ffff0000ffff0000,3,[0, 1, 2, 3]),(0x3030303030303030303030303030303,2,[0, 3, 4]),(0xf000f000f000f000f000f000f000f0,2,[1, 0, 4]),(0xcccc0000cccc0000cccc0000cccc,2,[2, 0, 3]),(0x55005500550055005500550055005500,2,[2, 1, 4]),(0x30003000300030003000300030003,1,[0, 4]),(0x3333000033330000333300003333,2,[3, 2, 0]),(0x55550000555500005555000055550000,2,[1, 2, 3]),(0x303000003030000030300000303,1,[0, 3]),(0x33330000333300003333000033330000,2,[0, 2, 3]),(0xf000f000f000f000f000f000f000f00,2,[0, 1, 4]),(0x55000000550000005500000055,1,[1, 2])]
theorem p15_Y : ∀ s ∈ p15_Z, SliceN p15_R p15_T s := by
  unfold p15_Z
  simp only [List.forall_mem_cons]
  exact ⟨p15_S0,p15_S1,p15_S2,p15_S3,p15_S4,p15_S5,p15_S6,p15_S7,p15_S8,p15_S9,p15_S10,p15_S11,p15_S12,p15_S13,p15_S14,p15_S15,p15_S16,p15_S17,p15_S18,p15_S19,p15_S20,p15_S21,p15_S22,p15_S23,p15_S24,p15_S25,p15_S26,p15_S27,p15_S28,p15_S29,p15_S30,p15_S31,p15_S32,p15_S33,by simp⟩
def p15_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[]),(17,[]),(18,[]),(19,[]),(20,[]),(21,[]),(22,[]),(23,[]),(24,[]),(25,[]),(26,[]),(27,[]),(28,[]),(29,[]),(30,[]),(31,[]),(32,[]),(33,[]),(0,[(2,0,3)]),(1,[(2,0,3)]),(0,[(2,1,2)]),(2,[(2,0,3)]),(0,[(2,0,1)]),(0,[(0,0,1)]),(0,[(3,1,2)]),(0,[(0,1,2)]),(1,[(2,1,2)]),(3,[(2,0,3)]),(0,[(3,0,1)]),(0,[(3,0,3)]),(0,[(0,0,3)]),(2,[(2,1,2)]),(4,[(2,0,3)]),(3,[(2,1,2)]),(4,[(2,1,2)])]
def p15_P : List (Nat × Nat) := [(4,6),(10,11),(5,7),(20,21),(3,7),(1,9),(1,17),(8,12),(24,26),(3,11),(2,18),(4,12),(24,28),(5,21),(20,28),(10,26)]
def p15_K : List CutV := p15_C.map (mkCut p15_Z)
theorem p15_W : ∀ c ∈ p15_K, CutP p15_R p15_T c := cutsGood p15_Y (by decide +kernel)
theorem p15_Q : p15_P.all (sepOK p15_T) = true := by decide +kernel
noncomputable def p15_D6 : List StD := [
([w0,w1,w2,w3,w30],[0,1,2,3,4],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[[0,1,100,101,102],[0,2,101,103,104],[0,3,103,101,105],[0,4,101,103,106],[1,2,107,100,104],[1,3,100,108,109],[1,4,100,108,110],[2,3,104,107,111],[2,4,104,112,113],[3,4,105,114,115]])]
noncomputable def p15_D5 : List StD := [
([w0,w1,w4,w2,w3,w30],[0,1,5,6,2,7,4,8,9,10,11],[],[[0,1],[1],[0,2],[0,2],[0,2],[0],[1,3],[1,3],[1,3],[4,2,5],[5,2],[6,2],[7,8],[5,8,7],[5,9,10]]),
([w0,w1,w2,w5,w3,w30],[0,5,2,12,1,13,14,15,3,16,17],[],[[0,1],[0,1],[2],[0,1],[0,1],[2,3],[4,1,5],[5,6,7],[7,6],[0],[2,3],[2,3],[8,1],[5,1],[5,9,10]]),
([w0,w1,w2,w3,w6,w30],[0,5,3,13,14,9,18,17,19,2,20],[],[[0,1],[0,1],[0,1],[2],[0,1],[3,4,5],[2,4,6],[3,1],[7,4,8],[2,5,6],[9,1,10],[3,5],[0],[2,6],[3,1]]),
([w0,w1,w2,w3,w30,w31],[0,5,4,7,9,14,19,1,21,11,22],[],[[0,1],[0,1],[0,1],[0,1],[2],[3,4,5],[3,5],[2,5,6],[7,1,8],[9,4,6],[2,4,6],[3,1],[2,10],[3,1],[0]]),
([w0,w1,w2,w7,w3,w30],[1,9,6,2,14,12,0,23,24,10,25,16],[],[[0,1,2],[3,4,5],[6,2,7],[8,1,9],[10,1,11],[0,2],[3],[0,2],[0,2],[0],[3,1],[3,1],[7,1],[7,1],[8,9]]),
([w0,w1,w2,w3,w8,w30],[1,6,8,14,26,3,19,0,27,2,25],[],[[0,1],[2,3,4],[5,3,6],[7,1,8],[4,3],[0,1],[0,1],[5],[0,1],[2,4,5],[9,1],[2,6,10],[0],[5,4],[8,1]]),
([w0,w1,w2,w3,w30,w32],[1,6,8,14,16,7,25,0,28,4,19],[],[[0,1],[2,3,4],[5,3],[6,3,4],[7,1,8],[0,1],[0,1],[0,1],[9],[2,4],[2,10,5],[5,1],[5,4],[5,1],[0]]),
([w0,w1,w2,w3,w9,w30],[26,9,16,2,3,19,0,27,1,13,10],[],[[0,1],[0,2,3],[4,1,5],[6,2,7],[0,1],[3,1],[4,0],[8,0,9],[7,2,10],[3,1],[4],[3,1],[3],[4,0],[7,0]]),
([w0,w1,w2,w3,w30,w33],[15,9,29,2,4,19,0,30,24,1],[],[[0,1,2],[2,0,3],[2,1],[4,1,5],[6,0,7],[3,1],[0,5,8],[0,2,4],[9,1],[3,0],[3,0],[4],[4,2],[7,0],[3]]),
([w0,w1,w2,w3,w30,w34],[26,10,31,16,32,3,4,0,1,33],[],[[0,1,2],[0,3,4],[5,1],[0,2,6],[7,1],[2,1],[2,0,5],[6,1,3],[8,0,9],[5,0],[4,2,6],[9,0],[5,0],[6],[5]])]
noncomputable def p15_D4 : List StD := [
([w35,w0,w1,w2,w3],[0,1,19,9,2,3,10,34,16,14,35,8],[],[[0,1],[1,0],[2,3,4],[5,6],[7,3],[7,8,9],[7,2,3],[10,3,6],[10,2,9],[11,2,3]]),
([w16,w0,w1,w2,w30],[0,2,19,14,1,10,16,4,36,9,37,15],[],[[0,1],[2,3,4],[1,0],[5,6,7],[8,5,9],[8,3],[8,2,3],[10,3,6],[11,2,3],[10,2,9]]),
([w23,w0,w1,w3,w30],[0,14,38,39,40,19,41,9,4,42,10,43,26],[],[[0,1],[2,1,3],[4,5,6],[7,5,8],[9,7,10],[11,1,5],[12,1],[9,1],[9,1],[11,10]]),
([w36,w0,w2,w3,w30],[0,9,44,39,3,19,45,46,47,16,24,48],[],[[0,1],[2,1,3],[4,5],[6,5,7],[8,9],[10,1,5],[11,1,5],[8,1],[8,1],[10,9,11]]),
([w37,w1,w2,w3,w30],[1,10,2,16,0,32,49,50,19],[],[[0,1],[2,3],[4,1],[4,3],[5,1,3],[6,5],[7,1,3],[6,1],[5,8,7],[6,1]])]
def p15_D3 : List StD := []
theorem p15_I3 : LevelN p15_R p15_T 3 p15_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p15_C4x0 : levelOK p15_T p15_K p15_P 3 (p15_D3.map Prod.fst) ((p15_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem p15_I4 : LevelN p15_R p15_T 4 p15_D4 := levelStep p15_B p15_W p15_Q p15_I3 (chunks 16 p15_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p15_C5x0 : levelOK p15_T p15_K p15_P 4 (p15_D4.map Prod.fst) ((p15_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem p15_I5 : LevelN p15_R p15_T 5 p15_D5 := levelStep p15_B p15_W p15_Q p15_I4 (chunks 16 p15_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p15_C6x0 : levelOK p15_T p15_K p15_P 5 (p15_D5.map Prod.fst) ((p15_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem p15_I6 : LevelN p15_R p15_T 6 p15_D6 := levelStep p15_B p15_W p15_Q p15_I5 (chunks 16 p15_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C6x0
  ))
theorem p15_L : LowN p15_R p15_T 7 := lowSearch p15_B p15_I6 (by decide +kernel)
def p16_T : Nat := 0xfeeefae8feeefae8feeefae8feeefae8
def p16_R : List Nat := [0, 1, 2, 3, 4]
def p16_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p16_B : baseOK p16_T p16_R p16_E = true := by decide +kernel
theorem p16_S0 : SliceN p16_R p16_T (0x33333333333333333333333333333333,5,[0, 2, 3, 4]) := mkSlice (w:=0) p16_B p10_B p10_L (by decide +kernel)
theorem p16_S1 : SliceN p16_R p16_T (0x55555555555555555555555555555555,4,[1, 2, 3, 4]) := mkSlice (w:=0) p16_B p9_B p9_L (by decide +kernel)
theorem p16_S2 : SliceN p16_R p16_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 4, 3]) := mkSlice (w:=0) p16_B p10_B p10_L (by decide +kernel)
theorem p16_S3 : SliceN p16_R p16_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p16_B p11_B p11_L (by decide +kernel)
theorem p16_S4 : SliceN p16_R p16_T (0xffff0000ffff0000ffff0000ffff,5,[0, 2, 1, 3]) := mkSlice (w:=0) p16_B p11_B p11_L (by decide +kernel)
def p16_Z : List SliceD := [(0x33333333333333333333333333333333,5,[0, 2, 3, 4]),(0x55555555555555555555555555555555,4,[1, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 4, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff,5,[0, 2, 1, 3])]
theorem p16_Y : ∀ s ∈ p16_Z, SliceN p16_R p16_T s := by
  unfold p16_Z
  simp only [List.forall_mem_cons]
  exact ⟨p16_S0,p16_S1,p16_S2,p16_S3,p16_S4,by simp⟩
def p16_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p16_P : List (Nat × Nat) := [(1,3),(0,3),(1,5),(0,5),(1,9),(0,9),(1,17),(0,17),(2,6),(18,24),(2,18),(6,10),(12,24),(10,18)]
def p16_K : List CutV := p16_C.map (mkCut p16_Z)
theorem p16_W : ∀ c ∈ p16_K, CutP p16_R p16_T c := cutsGood p16_Y (by decide +kernel)
theorem p16_Q : p16_P.all (sepOK p16_T) = true := by decide +kernel
noncomputable def p16_D6 : List StD := [
([w0,w1,w2,w3,w30],[0,1,2,3,4],[0,1,2,3,4,5,6,7,8,9,10,11,12,13],[[0,100,1,101],[1,2,102,103],[1,3,104,105],[1,4,106,107],[0,2,108],[0,3,109],[0,4,110],[2,3,111],[2,4,112],[3,4,113]])]
def p16_D5 : List StD := []
theorem p16_I5 : LevelN p16_R p16_T 5 p16_D5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C6x0 : levelOK p16_T p16_K p16_P 5 (p16_D5.map Prod.fst) ((p16_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem p16_I6 : LevelN p16_R p16_T 6 p16_D6 := levelStep p16_B p16_W p16_Q p16_I5 (chunks 16 p16_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C6x0
  ))
theorem p16_L : LowN p16_R p16_T 7 := lowSearch p16_B p16_I6 (by decide +kernel)
def p17_T : Nat := 0xfeeefac8feeefac8feeefac8feeefac8
def p17_R : List Nat := [0, 1, 2, 3, 4]
def p17_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,1,17)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
theorem p17_S0 : SliceN p17_R p17_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 4, 3]) := mkSlice (w:=0) p17_B p10_B p10_L (by decide +kernel)
def p17_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 4, 3])]
theorem p17_Y : ∀ s ∈ p17_Z, SliceN p17_R p17_T s := by
  unfold p17_Z
  simp only [List.forall_mem_cons]
  exact ⟨p17_S0,by simp⟩
def p17_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def p17_P : List (Nat × Nat) := []
def p17_K : List CutV := p17_C.map (mkCut p17_Z)
theorem p17_W : ∀ c ∈ p17_K, CutP p17_R p17_T c := cutsGood p17_Y (by decide +kernel)
theorem p17_Q : p17_P.all (sepOK p17_T) = true := by decide +kernel
noncomputable def p17_D5 : List StD := [
([w0,w1,w2,w3,w30],[0],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p17_D4 : List StD := []
theorem p17_I4 : LevelN p17_R p17_T 4 p17_D4 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p17_C5x0 : levelOK p17_T p17_K p17_P 4 (p17_D4.map Prod.fst) ((p17_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem p17_I5 : LevelN p17_R p17_T 5 p17_D5 := levelStep p17_B p17_W p17_Q p17_I4 (chunks 16 p17_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C5x0
  ))
theorem p17_L : LowN p17_R p17_T 6 := lowSearch p17_B p17_I5 (by decide +kernel)
def p18_T : Nat := 0xfffefffefffefffefffefffefffefffe
def p18_R : List Nat := [0, 1, 2, 3]
def p18_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,0,8)]
theorem p18_B : baseOK p18_T p18_R p18_E = true := by decide +kernel
theorem p18_L : LowN p18_R p18_T 3 := lowCount p18_B (by decide +kernel)
def p19_T : Nat := 0xfffefefefffefefefffefefefffefefe
def p19_R : List Nat := [0, 1, 2, 3, 4]
def p19_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,16,24),(4,8,24)]
theorem p19_B : baseOK p19_T p19_R p19_E = true := by decide +kernel
theorem p19_L : LowN p19_R p19_T 4 := lowCount p19_B (by decide +kernel)
def p20_T : Nat := 0xfffefeeefffafce0fffefeeefffafce0
def p20_R : List Nat := [0, 1, 2, 3, 4, 5]
def p20_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,2,10),(4,1,17),(5,1,33)]
theorem p20_B : baseOK p20_T p20_R p20_E = true := by decide +kernel
theorem p20_S0 : SliceN p20_R p20_T (0x55555555555555555555555555555555,7,[1, 2, 3, 4, 5]) := mkSlice (w:=0) p20_B p14_B p14_L (by decide +kernel)
theorem p20_S1 : SliceN p20_R p20_T (0x33333333333333333333333333333333,7,[0, 2, 4, 3, 5]) := mkSlice (w:=0) p20_B p14_B p14_L (by decide +kernel)
theorem p20_S2 : SliceN p20_R p20_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4, 5]) := mkSlice (w:=0) p20_B p15_B p15_L (by decide +kernel)
theorem p20_S3 : SliceN p20_R p20_T (0xffffffff00000000ffffffff,7,[2, 3, 4, 0, 1]) := mkSlice (w:=0) p20_B p16_B p16_L (by decide +kernel)
theorem p20_S4 : SliceN p20_R p20_T (0x330033003300330033003300330033,5,[0, 2, 4, 5]) := mkSlice (w:=0) p20_B p10_B p10_L (by decide +kernel)
theorem p20_S5 : SliceN p20_R p20_T (0x33333333000000003333333300000000,5,[0, 2, 3, 4]) := mkSlice (w:=32) p20_B p12_B p12_L (by decide +kernel)
theorem p20_S6 : SliceN p20_R p20_T (0x5555000055550000555500005555,5,[1, 2, 3, 5]) := mkSlice (w:=0) p20_B p10_B p10_L (by decide +kernel)
theorem p20_S7 : SliceN p20_R p20_T (0x55555555000000005555555500000000,5,[1, 2, 3, 4]) := mkSlice (w:=32) p20_B p12_B p12_L (by decide +kernel)
theorem p20_S8 : SliceN p20_R p20_T (0x111111110000000011111111,4,[2, 3, 4]) := mkSlice (w:=0) p20_B p3_B p3_L (by decide +kernel)
theorem p20_S9 : SliceN p20_R p20_T (0x11111111000000001111111100000000,4,[2, 3, 4]) := mkSlice (w:=32) p20_B p3_B p3_L (by decide +kernel)
theorem p20_S10 : SliceN p20_R p20_T (0x5050505050505050505050505050505,4,[1, 3, 4, 5]) := mkSlice (w:=0) p20_B p9_B p9_L (by decide +kernel)
theorem p20_S11 : SliceN p20_R p20_T (0xff00ff00ff00ff00ff00ff00ff00ff,6,[0, 2, 1, 5, 4]) := mkSlice (w:=0) p20_B p17_B p17_L (by decide +kernel)
theorem p20_S12 : SliceN p20_R p20_T (0x550055005500550055005500550055,4,[1, 2, 4, 5]) := mkSlice (w:=0) p20_B p9_B p9_L (by decide +kernel)
theorem p20_S13 : SliceN p20_R p20_T (0xff00ff0000000000ff00ff,5,[2, 0, 4, 1]) := mkSlice (w:=0) p20_B p10_B p10_L (by decide +kernel)
theorem p20_S14 : SliceN p20_R p20_T (0xffff0000ffff0000ffff0000ffff,6,[1, 2, 0, 5, 3]) := mkSlice (w:=0) p20_B p17_B p17_L (by decide +kernel)
theorem p20_S15 : SliceN p20_R p20_T (0x55550000000000005555,4,[1, 2, 3]) := mkSlice (w:=0) p20_B p3_B p3_L (by decide +kernel)
theorem p20_S16 : SliceN p20_R p20_T (0xffff000000000000ffff,5,[2, 1, 3, 0]) := mkSlice (w:=0) p20_B p10_B p10_L (by decide +kernel)
theorem p20_S17 : SliceN p20_R p20_T (0x3030303030303030303030303030303,4,[0, 4, 3, 5]) := mkSlice (w:=0) p20_B p9_B p9_L (by decide +kernel)
theorem p20_S18 : SliceN p20_R p20_T (0x3300330000000000330033,4,[0, 2, 4]) := mkSlice (w:=0) p20_B p3_B p3_L (by decide +kernel)
theorem p20_S19 : SliceN p20_R p20_T (0x3333000033330000333300003333,4,[0, 2, 3, 5]) := mkSlice (w:=0) p20_B p9_B p9_L (by decide +kernel)
theorem p20_S20 : SliceN p20_R p20_T (0xf000f000f000f000f000f000f000f,4,[0, 5, 1, 4]) := mkSlice (w:=0) p20_B p9_B p9_L (by decide +kernel)
theorem p20_S21 : SliceN p20_R p20_T (0xf0f00000f0f00000f0f00000f0f,4,[1, 5, 0, 3]) := mkSlice (w:=0) p20_B p9_B p9_L (by decide +kernel)
theorem p20_S22 : SliceN p20_R p20_T (0xaa00aa00aa00aa00aa00aa00aa00aa00,3,[1, 2, 4, 5]) := mkSlice (w:=9) p20_B p18_B p18_L (by decide +kernel)
theorem p20_S23 : SliceN p20_R p20_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[2, 4, 5, 1, 3]) := mkSlice (w:=1) p20_B p19_B p19_L (by decide +kernel)
theorem p20_S24 : SliceN p20_R p20_T (0xcccc0000cccc0000cccc0000cccc0000,3,[0, 2, 3, 5]) := mkSlice (w:=18) p20_B p18_B p18_L (by decide +kernel)
theorem p20_S25 : SliceN p20_R p20_T (0xc0c00000c0c00000c0c00000c0c0000,2,[0, 3, 5]) := mkSlice (w:=18) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S26 : SliceN p20_R p20_T (0xcc000000cc000000cc000000cc0000,2,[0, 2, 5]) := mkSlice (w:=18) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S27 : SliceN p20_R p20_T (0xf0f0000000000000f0f0,2,[0, 1, 3]) := mkSlice (w:=4) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S28 : SliceN p20_R p20_T (0xff000000ff000000ff000000ff00,3,[1, 2, 0, 5]) := mkSlice (w:=8) p20_B p13_B p13_L (by decide +kernel)
theorem p20_S29 : SliceN p20_R p20_T (0x30300000000000003030,1,[0, 3]) := mkSlice (w:=4) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S30 : SliceN p20_R p20_T (0xcccccccccccccccccccccccccccccccc,4,[2, 3, 5, 4, 0]) := mkSlice (w:=2) p20_B p19_B p19_L (by decide +kernel)
theorem p20_S31 : SliceN p20_R p20_T (0xa000a000a000a000a000a000a000a00,2,[1, 4, 5]) := mkSlice (w:=9) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S32 : SliceN p20_R p20_T (0xf000f00000000000f000f0,2,[0, 1, 4]) := mkSlice (w:=4) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S33 : SliceN p20_R p20_T (0xff000000ff000000ff000000ff0000,3,[0, 2, 1, 5]) := mkSlice (w:=16) p20_B p13_B p13_L (by decide +kernel)
theorem p20_S34 : SliceN p20_R p20_T (0x5000500000000000500050,1,[1, 4]) := mkSlice (w:=4) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S35 : SliceN p20_R p20_T (0xaa000000aa000000aa000000aa00,2,[1, 2, 5]) := mkSlice (w:=9) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S36 : SliceN p20_R p20_T (0x10101010000000001010101,1,[3, 4]) := mkSlice (w:=0) p20_B p1_B p1_L (by decide +kernel)
theorem p20_S37 : SliceN p20_R p20_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,3,[3, 5, 4, 0]) := mkSlice (w:=2) p20_B p13_B p13_L (by decide +kernel)
theorem p20_S38 : SliceN p20_R p20_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3,[4, 5, 1, 3]) := mkSlice (w:=1) p20_B p13_B p13_L (by decide +kernel)
theorem p20_S39 : SliceN p20_R p20_T (0x1100110000000000110011,1,[2, 4]) := mkSlice (w:=0) p20_B p1_B p1_L (by decide +kernel)
theorem p20_S40 : SliceN p20_R p20_T (0x11110000000000001111,1,[2, 3]) := mkSlice (w:=0) p20_B p1_B p1_L (by decide +kernel)
theorem p20_S41 : SliceN p20_R p20_T (0xc000c000c000c000c000c000c000c,2,[5, 4, 0]) := mkSlice (w:=2) p20_B p7_B p7_L (by decide +kernel)
theorem p20_S42 : SliceN p20_R p20_T (0x101010100000000010101010,1,[3, 4]) := mkSlice (w:=4) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S43 : SliceN p20_R p20_T (0xa0a00000a0a00000a0a00000a0a,2,[5, 3, 1]) := mkSlice (w:=1) p20_B p7_B p7_L (by decide +kernel)
theorem p20_S44 : SliceN p20_R p20_T (0x22000000220000002200000022,1,[2, 5]) := mkSlice (w:=1) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S45 : SliceN p20_R p20_T (0x88888888888888888888888888888888,3,[2, 3, 4, 5]) := mkSlice (w:=3) p20_B p18_B p18_L (by decide +kernel)
theorem p20_S46 : SliceN p20_R p20_T (0x50000000500000005000000050000,1,[1, 5]) := mkSlice (w:=16) p20_B p1_B p1_L (by decide +kernel)
theorem p20_S47 : SliceN p20_R p20_T (0x220022002200220022002200220022,2,[2, 4, 5]) := mkSlice (w:=1) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S48 : SliceN p20_R p20_T (0x50005000000000005000500,1,[1, 4]) := mkSlice (w:=8) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S49 : SliceN p20_R p20_T (0x22002200220022002200220022002200,2,[2, 4, 5]) := mkSlice (w:=9) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S50 : SliceN p20_R p20_T (0x3000300000000000300030,1,[0, 4]) := mkSlice (w:=4) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S51 : SliceN p20_R p20_T (0x404000004040000040400000404,1,[3, 5]) := mkSlice (w:=2) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S52 : SliceN p20_R p20_T (0x5050000050500000505000005050000,2,[3, 1, 5]) := mkSlice (w:=16) p20_B p7_B p7_L (by decide +kernel)
theorem p20_S53 : SliceN p20_R p20_T (0xaaaaaaaa00000000aaaaaaaa,3,[2, 4, 3, 1]) := mkSlice (w:=1) p20_B p13_B p13_L (by decide +kernel)
theorem p20_S54 : SliceN p20_R p20_T (0xf0f0f0f000000000f0f0f0f000000000,3,[0, 1, 3, 4]) := mkSlice (w:=36) p20_B p18_B p18_L (by decide +kernel)
theorem p20_S55 : SliceN p20_R p20_T (0xff00ff0000000000ff00ff0000000000,3,[0, 1, 2, 4]) := mkSlice (w:=40) p20_B p18_B p18_L (by decide +kernel)
theorem p20_S56 : SliceN p20_R p20_T (0x880088008800880088008800880088,2,[2, 4, 5]) := mkSlice (w:=3) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S57 : SliceN p20_R p20_T (0x505000005050000050500000505,2,[1, 3, 5]) := mkSlice (w:=0) p20_B p8_B p8_L (by decide +kernel)
theorem p20_S58 : SliceN p20_R p20_T (0xf000000000000000f0,1,[0, 1]) := mkSlice (w:=4) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S59 : SliceN p20_R p20_T (0x88000000880000008800000088,1,[2, 5]) := mkSlice (w:=3) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S60 : SliceN p20_R p20_T (0x3000300030003000300030003000300,2,[4, 0, 5]) := mkSlice (w:=8) p20_B p7_B p7_L (by decide +kernel)
theorem p20_S61 : SliceN p20_R p20_T (0x44000000440000004400000044,1,[2, 5]) := mkSlice (w:=2) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S62 : SliceN p20_R p20_T (0x440000004400000044000000440000,1,[2, 5]) := mkSlice (w:=18) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S63 : SliceN p20_R p20_T (0x3300000033000000330000003300,2,[2, 0, 5]) := mkSlice (w:=8) p20_B p7_B p7_L (by decide +kernel)
theorem p20_S64 : SliceN p20_R p20_T (0x8080808080808080808080808080808,2,[3, 4, 5]) := mkSlice (w:=3) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S65 : SliceN p20_R p20_T (0xf0000000f0000000f0000000f00,2,[1, 0, 5]) := mkSlice (w:=8) p20_B p7_B p7_L (by decide +kernel)
theorem p20_S66 : SliceN p20_R p20_T (0x300000003000000030000000300,1,[0, 5]) := mkSlice (w:=8) p20_B p1_B p1_L (by decide +kernel)
theorem p20_S67 : SliceN p20_R p20_T (0x550000000000000055000000000000,1,[1, 2]) := mkSlice (w:=48) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S68 : SliceN p20_R p20_T (0x55000000550000005500000055,2,[1, 2, 5]) := mkSlice (w:=0) p20_B p8_B p8_L (by decide +kernel)
theorem p20_S69 : SliceN p20_R p20_T (0xf0000000f0000000f0000000f0000,2,[0, 1, 5]) := mkSlice (w:=16) p20_B p7_B p7_L (by decide +kernel)
theorem p20_S70 : SliceN p20_R p20_T (0xf0000000f0000000f0000000f,2,[5, 1, 0]) := mkSlice (w:=0) p20_B p8_B p8_L (by decide +kernel)
theorem p20_S71 : SliceN p20_R p20_T (0x808000008080000080800000808,1,[3, 5]) := mkSlice (w:=3) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S72 : SliceN p20_R p20_T (0xa0000000a0000000a0000000a00,1,[1, 5]) := mkSlice (w:=9) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S73 : SliceN p20_R p20_T (0x30300000000000003030000,1,[0, 3]) := mkSlice (w:=16) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S74 : SliceN p20_R p20_T (0x50500000000000005050,1,[1, 3]) := mkSlice (w:=4) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S75 : SliceN p20_R p20_T (0x20002000200020002000200020002,1,[4, 5]) := mkSlice (w:=1) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S76 : SliceN p20_R p20_T (0x80008000800080008000800080008,1,[4, 5]) := mkSlice (w:=3) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S77 : SliceN p20_R p20_T (0x5500000000000000550000000000,1,[1, 2]) := mkSlice (w:=40) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S78 : SliceN p20_R p20_T (0x44440000444400004444000044440000,2,[2, 3, 5]) := mkSlice (w:=18) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S79 : SliceN p20_R p20_T (0xf000000000000000f00000000,1,[0, 1]) := mkSlice (w:=32) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S80 : SliceN p20_R p20_T (0x30003000300030003000300030003,2,[0, 4, 5]) := mkSlice (w:=0) p20_B p8_B p8_L (by decide +kernel)
theorem p20_S81 : SliceN p20_R p20_T (0xcccccccc00000000cccccccc,3,[2, 3, 0, 4]) := mkSlice (w:=2) p20_B p13_B p13_L (by decide +kernel)
theorem p20_S82 : SliceN p20_R p20_T (0x330000000000000033000000000000,1,[0, 2]) := mkSlice (w:=48) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S83 : SliceN p20_R p20_T (0x33000000330000003300000033,2,[0, 2, 5]) := mkSlice (w:=0) p20_B p8_B p8_L (by decide +kernel)
theorem p20_S84 : SliceN p20_R p20_T (0x3300000000000000330000000000,1,[0, 2]) := mkSlice (w:=40) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S85 : SliceN p20_R p20_T (0x2200000022000000220000002200,1,[2, 5]) := mkSlice (w:=9) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S86 : SliceN p20_R p20_T (0xc0000000c0000000c0000000c0000,1,[0, 5]) := mkSlice (w:=18) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S87 : SliceN p20_R p20_T (0x550055000000000055005500,2,[1, 2, 4]) := mkSlice (w:=8) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S88 : SliceN p20_R p20_T (0xffff000000000000ffff000000000000,3,[0, 1, 2, 3]) := mkSlice (w:=48) p20_B p18_B p18_L (by decide +kernel)
theorem p20_S89 : SliceN p20_R p20_T (0x300030000000000030003,1,[0, 4]) := mkSlice (w:=0) p20_B p1_B p1_L (by decide +kernel)
theorem p20_S90 : SliceN p20_R p20_T (0xc000c00000000000c000c,1,[0, 4]) := mkSlice (w:=2) p20_B p1_B p1_L (by decide +kernel)
theorem p20_S91 : SliceN p20_R p20_T (0xf000000000000000f000000000000,1,[0, 1]) := mkSlice (w:=48) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S92 : SliceN p20_R p20_T (0x333300000000000033330000,2,[0, 2, 3]) := mkSlice (w:=16) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S93 : SliceN p20_R p20_T (0xf000000000000000f0000000000,1,[0, 1]) := mkSlice (w:=40) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S94 : SliceN p20_R p20_T (0x5050000000000000505,1,[1, 3]) := mkSlice (w:=0) p20_B p1_B p1_L (by decide +kernel)
theorem p20_S95 : SliceN p20_R p20_T (0xa000a00000000000a000a00,1,[1, 4]) := mkSlice (w:=9) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S96 : SliceN p20_R p20_T (0xf0f0f0f000000000f0f0f0f,4,[3, 4, 0, 1]) := mkSlice (w:=0) p20_B p9_B p9_L (by decide +kernel)
theorem p20_S97 : SliceN p20_R p20_T (0xff00000000000000ff,2,[2, 1, 0]) := mkSlice (w:=0) p20_B p8_B p8_L (by decide +kernel)
theorem p20_S98 : SliceN p20_R p20_T (0xf0f0000000000000f0f000000000000,2,[0, 1, 3]) := mkSlice (w:=48) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S99 : SliceN p20_R p20_T (0xf0f0000000000000f0f000000000,2,[0, 1, 3]) := mkSlice (w:=36) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S100 : SliceN p20_R p20_T (0xf000f00000000000f000f0000000000,2,[0, 1, 4]) := mkSlice (w:=40) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S101 : SliceN p20_R p20_T (0xf000f00000000000f000f000000000,2,[0, 1, 4]) := mkSlice (w:=36) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S102 : SliceN p20_R p20_T (0xaa00aa0000000000aa00aa00,2,[1, 2, 4]) := mkSlice (w:=9) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S103 : SliceN p20_R p20_T (0xcccc000000000000cccc0000,2,[0, 2, 3]) := mkSlice (w:=18) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S104 : SliceN p20_R p20_T (0x110011000000000011001100,1,[2, 4]) := mkSlice (w:=8) p20_B p2_B p2_L (by decide +kernel)
theorem p20_S105 : SliceN p20_R p20_T (0x5000000050000000500000005,1,[1, 5]) := mkSlice (w:=0) p20_B p1_B p1_L (by decide +kernel)
theorem p20_S106 : SliceN p20_R p20_T (0x4444000044440000444400004444,2,[2, 3, 5]) := mkSlice (w:=2) p20_B p4_B p4_L (by decide +kernel)
theorem p20_S107 : SliceN p20_R p20_T (0x3000000030000000300000003,1,[0, 5]) := mkSlice (w:=0) p20_B p1_B p1_L (by decide +kernel)
def p20_Z : List SliceD := [(0x55555555555555555555555555555555,7,[1, 2, 3, 4, 5]),(0x33333333333333333333333333333333,7,[0, 2, 4, 3, 5]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4, 5]),(0xffffffff00000000ffffffff,7,[2, 3, 4, 0, 1]),(0x330033003300330033003300330033,5,[0, 2, 4, 5]),(0x33333333000000003333333300000000,5,[0, 2, 3, 4]),(0x5555000055550000555500005555,5,[1, 2, 3, 5]),(0x55555555000000005555555500000000,5,[1, 2, 3, 4]),(0x111111110000000011111111,4,[2, 3, 4]),(0x11111111000000001111111100000000,4,[2, 3, 4]),(0x5050505050505050505050505050505,4,[1, 3, 4, 5]),(0xff00ff00ff00ff00ff00ff00ff00ff,6,[0, 2, 1, 5, 4]),(0x550055005500550055005500550055,4,[1, 2, 4, 5]),(0xff00ff0000000000ff00ff,5,[2, 0, 4, 1]),(0xffff0000ffff0000ffff0000ffff,6,[1, 2, 0, 5, 3]),(0x55550000000000005555,4,[1, 2, 3]),(0xffff000000000000ffff,5,[2, 1, 3, 0]),(0x3030303030303030303030303030303,4,[0, 4, 3, 5]),(0x3300330000000000330033,4,[0, 2, 4]),(0x3333000033330000333300003333,4,[0, 2, 3, 5]),(0xf000f000f000f000f000f000f000f,4,[0, 5, 1, 4]),(0xf0f00000f0f00000f0f00000f0f,4,[1, 5, 0, 3]),(0xaa00aa00aa00aa00aa00aa00aa00aa00,3,[1, 2, 4, 5]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[2, 4, 5, 1, 3]),(0xcccc0000cccc0000cccc0000cccc0000,3,[0, 2, 3, 5]),(0xc0c00000c0c00000c0c00000c0c0000,2,[0, 3, 5]),(0xcc000000cc000000cc000000cc0000,2,[0, 2, 5]),(0xf0f0000000000000f0f0,2,[0, 1, 3]),(0xff000000ff000000ff000000ff00,3,[1, 2, 0, 5]),(0x30300000000000003030,1,[0, 3]),(0xcccccccccccccccccccccccccccccccc,4,[2, 3, 5, 4, 0]),(0xa000a000a000a000a000a000a000a00,2,[1, 4, 5]),(0xf000f00000000000f000f0,2,[0, 1, 4]),(0xff000000ff000000ff000000ff0000,3,[0, 2, 1, 5]),(0x5000500000000000500050,1,[1, 4]),(0xaa000000aa000000aa000000aa00,2,[1, 2, 5]),(0x10101010000000001010101,1,[3, 4]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,3,[3, 5, 4, 0]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3,[4, 5, 1, 3]),(0x1100110000000000110011,1,[2, 4]),(0x11110000000000001111,1,[2, 3]),(0xc000c000c000c000c000c000c000c,2,[5, 4, 0]),(0x101010100000000010101010,1,[3, 4]),(0xa0a00000a0a00000a0a00000a0a,2,[5, 3, 1]),(0x22000000220000002200000022,1,[2, 5]),(0x88888888888888888888888888888888,3,[2, 3, 4, 5]),(0x50000000500000005000000050000,1,[1, 5]),(0x220022002200220022002200220022,2,[2, 4, 5]),(0x50005000000000005000500,1,[1, 4]),(0x22002200220022002200220022002200,2,[2, 4, 5]),(0x3000300000000000300030,1,[0, 4]),(0x404000004040000040400000404,1,[3, 5]),(0x5050000050500000505000005050000,2,[3, 1, 5]),(0xaaaaaaaa00000000aaaaaaaa,3,[2, 4, 3, 1]),(0xf0f0f0f000000000f0f0f0f000000000,3,[0, 1, 3, 4]),(0xff00ff0000000000ff00ff0000000000,3,[0, 1, 2, 4]),(0x880088008800880088008800880088,2,[2, 4, 5]),(0x505000005050000050500000505,2,[1, 3, 5]),(0xf000000000000000f0,1,[0, 1]),(0x88000000880000008800000088,1,[2, 5]),(0x3000300030003000300030003000300,2,[4, 0, 5]),(0x44000000440000004400000044,1,[2, 5]),(0x440000004400000044000000440000,1,[2, 5]),(0x3300000033000000330000003300,2,[2, 0, 5]),(0x8080808080808080808080808080808,2,[3, 4, 5]),(0xf0000000f0000000f0000000f00,2,[1, 0, 5]),(0x300000003000000030000000300,1,[0, 5]),(0x550000000000000055000000000000,1,[1, 2]),(0x55000000550000005500000055,2,[1, 2, 5]),(0xf0000000f0000000f0000000f0000,2,[0, 1, 5]),(0xf0000000f0000000f0000000f,2,[5, 1, 0]),(0x808000008080000080800000808,1,[3, 5]),(0xa0000000a0000000a0000000a00,1,[1, 5]),(0x30300000000000003030000,1,[0, 3]),(0x50500000000000005050,1,[1, 3]),(0x20002000200020002000200020002,1,[4, 5]),(0x80008000800080008000800080008,1,[4, 5]),(0x5500000000000000550000000000,1,[1, 2]),(0x44440000444400004444000044440000,2,[2, 3, 5]),(0xf000000000000000f00000000,1,[0, 1]),(0x30003000300030003000300030003,2,[0, 4, 5]),(0xcccccccc00000000cccccccc,3,[2, 3, 0, 4]),(0x330000000000000033000000000000,1,[0, 2]),(0x33000000330000003300000033,2,[0, 2, 5]),(0x3300000000000000330000000000,1,[0, 2]),(0x2200000022000000220000002200,1,[2, 5]),(0xc0000000c0000000c0000000c0000,1,[0, 5]),(0x550055000000000055005500,2,[1, 2, 4]),(0xffff000000000000ffff000000000000,3,[0, 1, 2, 3]),(0x300030000000000030003,1,[0, 4]),(0xc000c00000000000c000c,1,[0, 4]),(0xf000000000000000f000000000000,1,[0, 1]),(0x333300000000000033330000,2,[0, 2, 3]),(0xf000000000000000f0000000000,1,[0, 1]),(0x5050000000000000505,1,[1, 3]),(0xa000a00000000000a000a00,1,[1, 4]),(0xf0f0f0f000000000f0f0f0f,4,[3, 4, 0, 1]),(0xff00000000000000ff,2,[2, 1, 0]),(0xf0f0000000000000f0f000000000000,2,[0, 1, 3]),(0xf0f0000000000000f0f000000000,2,[0, 1, 3]),(0xf000f00000000000f000f0000000000,2,[0, 1, 4]),(0xf000f00000000000f000f000000000,2,[0, 1, 4]),(0xaa00aa0000000000aa00aa00,2,[1, 2, 4]),(0xcccc000000000000cccc0000,2,[0, 2, 3]),(0x110011000000000011001100,1,[2, 4]),(0x5000000050000000500000005,1,[1, 5]),(0x4444000044440000444400004444,2,[2, 3, 5]),(0x3000000030000000300000003,1,[0, 5])]
theorem p20_Y : ∀ s ∈ p20_Z, SliceN p20_R p20_T s := by
  unfold p20_Z
  simp only [List.forall_mem_cons]
  exact ⟨p20_S0,p20_S1,p20_S2,p20_S3,p20_S4,p20_S5,p20_S6,p20_S7,p20_S8,p20_S9,p20_S10,p20_S11,p20_S12,p20_S13,p20_S14,p20_S15,p20_S16,p20_S17,p20_S18,p20_S19,p20_S20,p20_S21,p20_S22,p20_S23,p20_S24,p20_S25,p20_S26,p20_S27,p20_S28,p20_S29,p20_S30,p20_S31,p20_S32,p20_S33,p20_S34,p20_S35,p20_S36,p20_S37,p20_S38,p20_S39,p20_S40,p20_S41,p20_S42,p20_S43,p20_S44,p20_S45,p20_S46,p20_S47,p20_S48,p20_S49,p20_S50,p20_S51,p20_S52,p20_S53,p20_S54,p20_S55,p20_S56,p20_S57,p20_S58,p20_S59,p20_S60,p20_S61,p20_S62,p20_S63,p20_S64,p20_S65,p20_S66,p20_S67,p20_S68,p20_S69,p20_S70,p20_S71,p20_S72,p20_S73,p20_S74,p20_S75,p20_S76,p20_S77,p20_S78,p20_S79,p20_S80,p20_S81,p20_S82,p20_S83,p20_S84,p20_S85,p20_S86,p20_S87,p20_S88,p20_S89,p20_S90,p20_S91,p20_S92,p20_S93,p20_S94,p20_S95,p20_S96,p20_S97,p20_S98,p20_S99,p20_S100,p20_S101,p20_S102,p20_S103,p20_S104,p20_S105,p20_S106,p20_S107,by simp⟩
def p20_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(2,[(1,0,1)]),(4,[]),(5,[]),(3,[(1,3,4)]),(6,[]),(7,[]),(8,[]),(9,[]),(1,[(1,0,1)]),(3,[(1,0,3)]),(10,[]),(1,[(1,0,3)]),(2,[(1,0,2)]),(3,[(1,1,3)]),(11,[]),(12,[]),(2,[(3,0,2)]),(13,[]),(1,[(1,0,2)]),(2,[(1,0,3)]),(14,[]),(15,[]),(1,[(3,0,2)]),(2,[(3,0,3)]),(16,[]),(2,[(1,0,4)]),(0,[(1,0,1)]),(17,[]),(3,[(1,0,4)]),(0,[(1,0,2)]),(2,[(1,1,2)]),(3,[(1,1,4)]),(18,[]),(0,[(3,0,2)]),(2,[(3,1,2)]),(0,[(1,0,3)]),(2,[(1,1,3)]),(19,[]),(3,[(1,2,4)]),(0,[(3,0,3)]),(2,[(3,1,3)]),(0,[(1,0,4)]),(2,[(1,1,4)]),(0,[(1,1,2)]),(1,[(1,1,3)]),(20,[]),(3,[(1,0,1)]),(0,[(3,1,2)]),(0,[(1,1,3)]),(1,[(1,1,2)]),(21,[]),(3,[(1,0,2)]),(0,[(3,1,3)]),(1,[(3,1,2)]),(0,[(1,1,4)]),(1,[(1,1,4)]),(0,[(3,1,4)]),(1,[(3,1,4)]),(0,[(0,2,3)]),(1,[(0,2,3)]),(2,[(0,2,3)]),(0,[(1,2,3)]),(1,[(1,2,3)]),(2,[(1,2,3)]),(0,[(2,2,3)]),(2,[(2,2,3)]),(0,[(3,2,3)]),(2,[(3,2,3)]),(1,[(2,2,3)]),(0,[(1,2,4)]),(1,[(1,3,4)]),(2,[(1,2,4)]),(0,[(2,2,4)]),(2,[(2,2,4)]),(0,[(1,3,4)]),(2,[(1,3,4)]),(0,[(2,3,4)]),(2,[(2,3,4)]),(22,[]),(3,[(1,3,4),(1,0,3)]),(13,[(1,0,1)]),(4,[(1,0,1)]),(23,[]),(24,[]),(25,[]),(2,[(1,0,1),(1,0,2)]),(26,[]),(2,[(3,0,3),(1,0,1)]),(16,[(1,1,3)]),(27,[]),(28,[]),(4,[(3,0,2)]),(29,[]),(6,[(1,0,1)]),(30,[]),(31,[]),(0,[(0,0,2)]),(2,[(3,1,2),(1,0,1)]),(32,[]),(33,[]),(6,[(3,0,2)]),(3,[(2,1,4)]),(34,[]),(2,[(1,0,1),(1,1,3)]),(35,[]),(36,[]),(37,[]),(38,[]),(39,[]),(6,[(1,0,2)]),(4,[(1,0,2)]),(40,[]),(0,[(2,0,4)]),(1,[(2,0,4)]),(4,[(2,0,3)]),(6,[(2,0,3)]),(41,[]),(8,[(1,0,1)]),(42,[]),(9,[(1,0,1)]),(43,[]),(8,[(1,0,2)]),(9,[(1,0,2)]),(8,[(1,1,2)]),(3,[(1,1,2)]),(44,[]),(9,[(1,1,2)]),(45,[]),(46,[]),(3,[(1,0,3),(1,1,3)]),(3,[(1,0,3),(1,2,3)]),(1,[(1,0,1),(1,0,2)]),(47,[]),(2,[(3,0,1)]),(0,[(2,0,1)]),(0,[(3,0,1)]),(2,[(2,0,1)]),(48,[]),(6,[(3,0,1)]),(49,[]),(50,[]),(51,[]),(52,[]),(1,[(1,0,1),(1,1,2)]),(4,[(1,1,2)]),(6,[(1,1,3)]),(4,[(1,1,3)]),(53,[]),(54,[]),(6,[(1,1,2)]),(0,[(2,1,2)]),(2,[(2,0,2)]),(55,[]),(56,[]),(8,[(2,0,1)]),(9,[(2,0,1)]),(0,[(0,1,2)]),(57,[]),(0,[(2,1,3)]),(2,[(2,0,3)]),(9,[(2,0,2)]),(58,[]),(59,[]),(4,[(3,0,1)]),(2,[(1,0,2),(1,0,3)]),(60,[]),(61,[]),(62,[]),(63,[]),(15,[(3,0,2)]),(64,[]),(15,[(1,1,2)]),(65,[]),(15,[(3,1,2)]),(4,[(2,0,1)]),(9,[(3,0,1)]),(6,[(3,1,2)]),(66,[]),(67,[]),(12,[(1,1,3)]),(12,[(3,1,3)]),(68,[]),(2,[(1,0,2),(1,2,3)]),(2,[(2,2,3),(1,0,2)]),(4,[(2,0,2)]),(9,[(2,1,2)]),(69,[]),(6,[(1,2,3)]),(0,[(3,2,4)]),(2,[(0,0,2)]),(13,[(1,0,2)]),(70,[]),(71,[]),(72,[]),(2,[(3,0,2),(1,2,3)]),(73,[]),(74,[]),(15,[(1,0,1)]),(75,[]),(15,[(1,0,2)]),(76,[]),(77,[]),(1,[(1,0,2),(1,1,2)]),(78,[]),(2,[(0,0,3)]),(79,[]),(0,[(1,0,1),(1,0,2)]),(0,[(1,0,1),(1,0,3)]),(0,[(1,0,1),(1,1,2)]),(0,[(1,0,1),(1,1,4)]),(80,[]),(0,[(2,0,2)]),(2,[(2,1,2)]),(81,[]),(5,[(1,1,3)]),(0,[(2,0,3)]),(0,[(0,0,3)]),(5,[(2,1,3)]),(2,[(2,1,3)]),(18,[(2,1,2)]),(2,[(0,1,3)]),(2,[(1,1,2),(1,1,3)]),(0,[(1,0,2),(1,0,3)]),(0,[(1,0,2),(1,1,2)]),(18,[(1,1,2)]),(82,[]),(4,[(0,1,2)]),(4,[(3,1,2)]),(18,[(3,1,2)]),(4,[(3,1,3)]),(83,[]),(2,[(0,1,2)]),(0,[(3,0,2),(1,1,2)]),(13,[(3,0,2)]),(9,[(3,0,2)]),(84,[]),(85,[]),(18,[(3,0,2)]),(1,[(3,1,3)]),(0,[(1,0,3),(1,1,3)]),(1,[(0,1,2)]),(1,[(2,1,2)]),(0,[(0,0,1)]),(15,[(2,0,1)]),(5,[(3,1,3)]),(19,[(1,1,3)]),(19,[(3,1,3)]),(0,[(1,0,3),(1,2,3)]),(2,[(3,2,3),(1,1,3)]),(15,[(2,0,2)]),(9,[(3,1,2)]),(1,[(1,2,4)]),(4,[(1,2,3)]),(0,[(3,3,4)]),(86,[]),(2,[(3,1,3),(1,2,3)]),(2,[(3,1,4)]),(87,[]),(18,[(3,0,1)]),(1,[(1,1,3),(1,1,2)]),(0,[(1,1,2),(1,1,3)]),(16,[(1,0,2)]),(0,[(1,1,2),(1,2,3)]),(0,[(2,2,3),(1,1,2)]),(0,[(0,1,3)]),(4,[(2,1,2)]),(88,[]),(89,[]),(90,[]),(2,[(3,2,4)]),(91,[]),(16,[(3,0,2)]),(0,[(3,1,2),(1,2,3)]),(16,[(1,0,3)]),(16,[(2,0,3)]),(16,[(1,0,1)]),(92,[]),(16,[(2,0,1)]),(0,[(1,1,3),(1,2,3)]),(1,[(1,1,2),(1,2,3)]),(1,[(2,2,3),(1,1,2)]),(6,[(2,1,2)]),(16,[(2,0,2)]),(2,[(0,2,4)]),(93,[]),(94,[]),(2,[(3,3,4)]),(1,[(3,1,2),(1,2,3)]),(95,[]),(96,[]),(0,[(0,2,3),(1,1,4)]),(9,[(0,1,2)]),(0,[(1,2,3),(1,1,4)]),(0,[(2,2,3),(1,1,4)]),(3,[(2,0,1)]),(0,[(1,1,4),(0,3,5)]),(2,[(0,3,4)]),(0,[(3,1,4),(1,2,3)]),(97,[]),(13,[(1,1,2)]),(13,[(3,1,2)]),(16,[(2,2,3)]),(16,[(1,1,2)]),(16,[(3,1,2)]),(7,[(1,2,3)]),(4,[(2,2,3)]),(16,[(1,2,3)]),(98,[]),(99,[]),(13,[(1,2,3)]),(100,[]),(101,[]),(13,[(1,1,3),(1,0,1)]),(2,[(1,0,1),(1,2,5)]),(18,[(1,0,1)]),(2,[(1,0,2),(1,1,5)]),(2,[(1,0,1),(1,3,5)]),(18,[(1,0,2)]),(4,[(0,0,1)]),(18,[(2,0,1)]),(99,[(1,0,1)]),(0,[(1,0,3),(2,0,1)]),(2,[(1,1,3),(3,0,1)]),(0,[(1,0,3),(1,1,5)]),(0,[(1,0,3),(2,0,2)]),(0,[(1,0,3),(3,2,3)]),(15,[(3,0,1)]),(0,[(1,1,2),(3,0,2)]),(0,[(1,0,3),(1,2,5)]),(18,[(2,0,2)]),(0,[(1,1,3),(3,0,3)]),(0,[(1,0,3),(3,1,5)]),(2,[(1,0,1),(3,4,5)]),(102,[]),(103,[]),(0,[(2,0,4),(1,1,2)]),(0,[(2,0,4),(2,1,2)]),(0,[(2,1,2),(2,0,4)]),(0,[(2,1,2),(0,0,4)]),(0,[(1,1,3),(2,0,4)]),(0,[(1,1,3),(0,0,4)]),(0,[(2,0,4),(2,1,3)]),(0,[(2,1,3),(2,0,4)]),(0,[(2,1,3),(0,0,4)]),(0,[(2,0,4),(0,1,3)]),(0,[(2,0,4),(1,1,3)]),(104,[]),(49,[(1,0,2)]),(105,[]),(18,[(0,0,2)]),(18,[(1,0,2),(1,1,2)]),(18,[(1,0,1),(1,0,2)]),(49,[(1,0,1)]),(35,[(1,1,2)]),(15,[(2,1,2)]),(10,[(1,0,2)]),(0,[(2,1,3),(3,0,3)]),(0,[(1,1,3),(2,1,2)]),(0,[(1,1,2),(2,1,3)]),(0,[(1,1,3),(1,1,2)]),(15,[(0,1,2)]),(0,[(2,1,2),(1,1,3)]),(0,[(2,1,2),(2,1,3)]),(0,[(1,1,3),(3,2,3)]),(0,[(1,1,2),(1,1,4)]),(0,[(1,1,4),(0,1,2)]),(0,[(3,1,2),(1,1,4)]),(0,[(1,1,3),(1,1,4)]),(0,[(1,1,4),(2,2,3)]),(0,[(1,1,4),(0,2,3)]),(0,[(1,1,4),(1,2,3)]),(2,[(1,0,2),(3,3,5)]),(10,[(2,1,2)]),(2,[(1,0,2),(3,1,5)]),(2,[(1,2,3),(3,0,2)]),(2,[(1,0,2),(1,3,5)]),(0,[(1,2,3),(3,1,2)]),(0,[(1,1,2),(2,2,3)]),(2,[(2,2,3),(3,0,2)]),(0,[(2,2,3),(3,1,2)]),(0,[(1,1,2),(0,3,5)]),(2,[(1,0,2),(0,3,5)]),(2,[(1,0,3),(1,2,5)]),(0,[(1,1,2),(3,3,5)]),(20,[(2,0,3)]),(0,[(2,1,3),(0,2,3)]),(0,[(2,1,3),(2,2,3)]),(0,[(1,1,2),(3,0,1)]),(0,[(1,1,2),(1,0,2)]),(0,[(1,2,3),(3,0,3)]),(12,[(1,0,2)]),(0,[(2,2,3),(3,0,3)]),(0,[(1,2,3),(1,1,2)]),(0,[(3,1,2),(2,2,3)]),(0,[(1,2,3),(3,1,3)]),(0,[(1,2,3),(3,1,4)]),(0,[(1,1,4),(3,2,3)]),(0,[(2,2,3),(3,1,4)]),(0,[(2,2,3),(0,1,3)]),(12,[(2,1,2)]),(0,[(1,1,2),(1,3,5)]),(0,[(1,2,3),(1,1,5)]),(0,[(1,2,3),(1,1,3)]),(0,[(1,1,3),(1,2,4)]),(0,[(1,2,4),(2,1,3)]),(0,[(1,0,3),(1,0,1)]),(0,[(1,0,1),(2,0,3)]),(0,[(1,0,3),(1,0,2)]),(0,[(1,0,3),(3,1,3)]),(15,[(0,0,2)]),(0,[(1,0,1),(1,0,2),(1,1,2)]),(15,[(1,0,1),(1,1,2)]),(106,[]),(107,[]),(0,[(1,0,1),(1,3,5)]),(0,[(1,1,2),(1,0,3)]),(0,[(1,0,3),(1,1,4)]),(0,[(1,0,3),(2,1,2)]),(0,[(3,2,3),(1,0,3)]),(0,[(3,2,3),(1,0,1)]),(0,[(1,1,2),(2,0,3)]),(0,[(1,1,2),(0,0,3)]),(0,[(1,0,1),(1,2,3)]),(26,[(1,1,2)]),(0,[(1,0,1),(1,2,5)]),(2,[(1,1,3),(1,2,5)]),(0,[(1,0,1),(2,0,2)]),(0,[(1,0,1),(0,0,2)]),(17,[(2,1,2)]),(2,[(1,1,3),(3,2,5)]),(1,[(1,1,2),(3,3,5)]),(18,[(0,1,2)]),(0,[(1,0,2),(1,1,3)]),(0,[(3,0,2),(1,1,3)]),(0,[(1,1,3),(1,0,3)]),(0,[(1,1,3),(1,0,5)]),(0,[(1,1,3),(2,0,2)]),(0,[(1,1,3),(0,0,2)]),(0,[(1,0,3),(0,0,2)]),(0,[(1,2,3),(2,0,1)]),(0,[(1,1,4),(2,0,2)]),(0,[(1,0,3),(3,0,2)]),(9,[(0,0,2)]),(0,[(1,0,3),(3,2,5)]),(0,[(1,1,3),(1,2,5)]),(0,[(1,1,2),(1,1,3),(1,2,3)]),(9,[(1,0,1),(1,0,2)]),(0,[(1,1,2),(3,1,2)]),(0,[(1,1,2),(2,3,5)]),(2,[(1,2,3),(3,1,5)]),(2,[(2,2,3),(2,0,3)]),(0,[(1,3,4),(2,1,3)]),(0,[(1,3,4),(0,2,3)]),(2,[(2,2,3),(2,3,4)]),(21,[(2,0,3)]),(0,[(1,1,3),(0,1,3)]),(0,[(1,1,3),(3,1,3)]),(21,[(0,0,3)]),(0,[(0,0,2),(2,1,2)]),(21,[(3,1,3)]),(21,[(2,1,2)]),(9,[(0,0,1)]),(0,[(1,1,4),(3,1,2)]),(0,[(1,1,4),(1,0,2)]),(0,[(1,1,4),(1,0,3)]),(0,[(1,1,4),(1,1,2)]),(0,[(1,1,4),(1,1,3)]),(0,[(1,1,4),(3,0,2)]),(0,[(1,1,4),(0,0,2)]),(0,[(1,1,2),(1,0,1)]),(0,[(1,2,3),(1,0,3)]),(15,[(1,0,2),(1,1,2)]),(18,[(1,0,1),(3,2,3)]),(18,[(1,1,2),(1,0,2)]),(18,[(1,0,1),(1,1,2)]),(0,[(2,2,3),(0,1,5)]),(18,[(2,0,2),(1,0,1)]),(18,[(2,1,2),(2,0,2)]),(15,[(0,0,1)]),(102,[(1,1,2)]),(0,[(1,1,4),(2,1,3)]),(0,[(1,1,4),(0,1,3)]),(9,[(1,0,2),(1,1,2)]),(9,[(1,0,1),(1,1,2)]),(9,[(2,1,2),(1,0,1)]),(9,[(2,0,2),(1,0,1)]),(0,[(2,1,3),(2,2,3),(1,1,2)]),(9,[(2,0,2),(2,1,2)]),(0,[(1,1,2),(1,2,3),(1,1,3)]),(0,[(1,2,3),(1,1,2),(1,1,3)]),(15,[(1,1,2),(1,0,1)]),(15,[(1,0,2),(1,0,1)]),(35,[(1,0,1)]),(15,[(1,0,1),(1,0,2)]),(15,[(1,1,2),(1,0,2)]),(0,[(1,1,2),(1,0,3),(1,2,3)]),(0,[(1,0,1),(1,0,3),(1,2,3)]),(0,[(1,0,1),(1,1,2),(1,2,3)]),(0,[(1,0,3),(1,2,3),(1,1,4)]),(0,[(1,0,1),(1,0,3),(1,1,4)]),(0,[(3,2,3),(1,0,1),(1,0,3)]),(15,[(2,0,2),(1,0,1)]),(0,[(1,0,1),(1,1,4),(2,0,2)]),(0,[(1,1,2),(1,0,3),(1,1,3)]),(0,[(1,0,2),(1,0,3),(1,1,3)]),(0,[(1,0,2),(1,1,2),(1,0,3)]),(0,[(1,1,4),(3,1,3)]),(0,[(3,0,3),(1,1,4)])]
def p20_P : List (Nat × Nat) := [(4,5),(18,19),(9,11),(1,5),(40,41),(3,11),(1,17),(1,33),(4,6),(2,6),(48,50),(3,19),(2,34),(8,12),(4,12),(16,20),(4,20),(40,44),(16,24),(8,24),(36,44),(9,41),(36,52),(18,50),(3,10),(2,11),(3,5),(2,10),(3,17),(3,33),(36,37),(3,7),(8,10),(9,13),(9,10),(8,11),(12,40),(0,5),(16,17),(9,33),(9,25),(36,38),(18,22),(0,33),(18,26),(17,18),(0,6),(16,19),(18,34),(32,34),(20,48),(48,52),(0,17),(0,10),(9,17),(48,56),(40,56),(0,24),(33,40),(34,48),(4,37),(5,9),(8,41),(2,5),(1,6),(2,17),(2,33),(4,38),(6,18),(1,10),(0,34),(16,50),(10,18),(20,36),(24,40),(0,20),(12,36),(24,48),(8,13),(32,33),(2,19),(0,12),(1,19),(16,22),(16,26),(12,16),(40,42),(48,49),(3,6),(17,32),(20,32),(24,32),(1,25),(8,25),(1,21),(4,21),(4,28),(2,26),(2,7),(10,32),(12,32),(2,14),(4,14),(13,16)]
def p20_K : List CutV := p20_C.map (mkCut p20_Z)
theorem p20_W : ∀ c ∈ p20_K, CutP p20_R p20_T c := cutsGood p20_Y (by decide +kernel)
theorem p20_Q : p20_P.all (sepOK p20_T) = true := by decide +kernel
noncomputable def p20_D9 : List StD := [
([w0,w1,w2,w3,w30,w38],[0,1,2,3],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],[[0,1,100,101,102],[0,2,101,100,103],[0,100,104,105],[0,100,101,106],[0,3,100,104,107],[1,2,102,108,109],[1,108,102,105],[1,102,110,111],[1,3,102,110,112],[2,103,113,114],[2,103,115,116],[2,3,103,117],[105,106,118,119],[3,107,120,121],[3,107,122,123]])]
noncomputable def p20_D8 : List StD := [
([w0,w1,w4,w2,w3,w30,w38],[0,1,4,5,6,7,8,9,10,3,11],[3,24,25,1,6,7,26,9,2,27,28,29,13,14,15,16,18,19],[[0,1],[0,1],[0,100,2],[0,101,3,102],[0,103,104],[0,4,105,5],[0],[1,106,2,107],[1,108,109],[1,110,6,108],[1,7,111,5,108],[2,8,100],[3,8,109],[6,8,104],[5,8,9,105],[2,3,100,112,113],[2,6,100,114,115],[2,5,8,10],[3,6,104,116,117],[3,5,8,10],[5,6,8,10]]),
([w0,w1,w2,w5,w3,w30,w38],[0,12,2,13,14,1,8,9,5,3],[2,5,0,6,30,31,3,32,8,10,11,12,33,16,27,19,7,18,21,23],[[0,100,1],[0,2],[0,2],[0,101,102],[0,103,102],[0,104,3,102],[1,2,105,106],[1,4,5,100,107],[1,108,100,101],[1,6,100,109,110],[1,3,100,7,111,109],[0],[2,112,105],[2,113,6],[2,7,3,105],[4,8,114,101],[4,6,115,103],[3,4,9,7,116,111],[6,103,117,115],[3,111,7,118],[3,6,103,7,119,111]]),
([w0,w1,w2,w3,w6,w30,w38],[0,15,16,5,17,18,19,1,8,9,2,3],[34,35,3,5,6,4,7,8,9,32,10,11,12,13,15,16,36,19,21,23],[[0,100,1,101],[0,102,2],[0,3,103],[0,3],[0,104,105],[0,105,4,106],[1,2,102,107,108],[1,5,107,3,109,103],[1,6,7,109,107],[1,8,104,110,111],[1,4,106,9,112],[2,3,102,113],[2,6,10,102,108],[2,8,102,114,115],[2,4,102,9,116,106],[0],[3,8,103,117,104],[3,4,103,9,118,106],[6,8,115,104],[4,6,11,9,106,112],[4,8,104,9,119,106]]),
([w39,w0,w1,w2,w3,w30,w38],[0,18,5,2,8,9,3,20,21],[4,32,13,19,2,0,37,5,38,7,8,10,15,16,36,39,23],[[0,1,100],[1,2,101],[1,102,3],[0],[1,103,4],[1,5,6],[0,2,104],[0,105,7,106],[0,1,107],[0,108,105],[0,8,109],[2,110,7,101],[1,2,101],[2,111,4,101],[2,5,111,8],[1,102,7],[4,7,102,112,113],[7,8,114,109],[1,103,4],[1,5,115,8,107],[4,8,116,109]]),
([w0,w1,w2,w3,w30,w31,w38],[0,22,23,8,24,25,5],[1,2,3,5,6,7,8,9,11,12,13,14,15,36,40,21,23],[[0,100,1,101],[0,102,2],[0,103,100],[0,3,104],[0,3,4],[0,5,105],[1,2,101,106,107],[1,106,101,103],[1,3,108,104],[1,3,101],[1,5,109,105],[2,102,110,111],[2,3,112],[2,3,102],[2,5,113,105],[3,114,104],[3,103,6],[5,115,105],[0],[3,5,116],[3,5,105]]),
([w40,w0,w1,w2,w3,w30,w38],[0,8,5,2,9,3,26,27,25,28],[38,10,15,18,23,34,0,37,4,6,8,9,32,27,11,13,14,36,40,21],[[0,1,100],[1,101,2],[1,102,3],[1,103,2],[0],[1,4,104,5],[0,105,6,106],[0,106,7,107],[0,108,106],[0,1,109],[0,8,108,9],[6,7,101,110,111],[6,101,112,113],[1,114,6,101],[6,8,104,101],[7,102,115,116],[1,102,7],[7,8,117,104],[1,118,109],[8,119,104],[1,4,104,8]]),
([w0,w1,w2,w3,w30,w38,w41],[0,6,29,21,25,3,9,10],[2,30,3,4,6,8,28,13,14,16,19],[[0,1,100],[0,101,2,102],[0,103,3,101],[0,4,104],[0,1,5],[0,1,3],[1,105,2,100],[1,100,3,105],[1,4,106],[1,4,6],[1,4,6],[2,3,102,107,108],[2,4,109,104],[1,2,4],[1,2,4],[3,4,110,104],[1,4],[1,3,4],[1,4,5],[1,4,7],[0]]),
([w0,w1,w2,w7,w3,w30,w38],[30,5,1,2,31,0,32,10,6,25,3],[1,31,0,38,4,5,6,7,8,11,41,14,42,18,12,19,21,23],[[0,1,2,100],[0,3,101,102],[0,4,5,100,103],[0,1,100,104,105],[0,102,100,106],[0,6,100,7,8,107,104],[1,2,3],[2,3],[1,2,105,108],[1,2,109,108],[1,2,110,6,108],[1],[1,3,111],[3,112,101],[3,8,6,101],[1,4,113,105],[4,9,106,109],[4,6,10,8,114,107],[1,105,113,115],[1,6,105,8,116,107],[6,107,8,117]]),
([w0,w1,w2,w3,w8,w30,w38],[33,5,34,35,36,1,21,25],[2,32,9,0,3,5,27,1,6,7,43,11,12,13,15,16,36,44,21,23],[[0,1,100,101],[0,2,102,103,104],[0,1,105,106],[0,1,107],[0,103,107,108],[0,3,4,109,110],[1,102,2],[1,5,105],[1,6],[1,111,100],[1,4,112],[1,113,2],[1,102,2],[2,102,114,115],[2,3,4,116,109],[1,5],[1,117,105],[1,4,118],[1,111,7],[1,4,112],[3,4,119,109]]),
([w42,w0,w1,w2,w3,w30,w38],[37,5,2,1,25,21,38],[4,32,13,19,21,45,8,0,3,5,38,6,46,10,15,16,36,44,23],[[0,1,100],[1,101],[1,102,2],[1,3],[1,103,4],[1,5,104],[0,1,105,106],[0,6,100,107,108],[0,1,109,100],[0,100,110,111],[0,5,104,100],[1,106,6,112],[1,3,109],[1,113,106],[1,5,113],[1,102,6],[6,102,114,115],[5,116,6,104],[1,117,109],[1,5,104],[5,118,104]]),
([w0,w1,w2,w3,w30,w32,w38],[39,1,40,5,24,25,41,0,42,6,2,3],[45,47,9,0,3,4,5,38,11,7,10,12,13,14,15,36,18,21,23],[[0,1,100,101],[0,2,102,103,104],[0,3,103,105,106],[0,4,103,5,107,108],[0,6,7,107,103],[0,8,103,5,9,109,105],[1,102,2],[1,106,110],[1,4,108],[1,4],[1,110,5,111],[2,3,102,112,113],[2,4,102,114],[2,6,10,102,104],[2,5,102,9,115,109],[3,4,106,116],[3,6,113,106],[3,5,106,9,117,109],[1],[4,8,108,5,9,118,109],[5,6,11,9,111,109]]),
([w43,w0,w1,w2,w3,w30,w38],[43,25,0,24,1,2,5,3,44,8,28],[38,10,15,18,34,0,4,8,46,32,11,29,13,14,36,7,21,48],[[0,1,2,100,3],[1,4,101],[1,102,5],[1,103,6],[1,4],[1,3,7],[0,1,4,104],[0,1,105,8,100],[0,1,106,6,100],[0,1,3,100],[0,1,9,106,10],[4,107,8,108],[4,109,107],[1,4,110],[1,4,111],[6,8,102,112,113],[1,102,8],[1,114,8,115],[1,103,6],[1,116,6,115],[1,3,117,110]]),
([w0,w1,w2,w3,w30,w38,w44],[45,5,1,10,46,36,28,6,3],[1,0,24,41,9,27,10,14,15,16,18],[[0,1,2,3,100],[0,3,101,4,100],[0,1,3,5,102],[0,3,100,6,101],[0,3,5,7],[0,3,5,7],[1,2,103,4,104],[1,2,5,105],[1,2,106,6,103],[1,2,3,8],[2,3,6],[1,4,5,107,105],[4,6,104,108,109],[3,7],[3,7],[1,5,110,6,105],[1,3,5,7],[1,3,5,7],[3,7],[3,7],[1]]),
([w0,w1,w2,w3,w9,w30,w38],[47,48,2,5,49,0,50,1,36,25,3,6],[0,1,2,33,4,6,7,8,49,10,11,12,14,16,17,19,20,21,22,23],[[0,1,100,101,102],[0,2,103,100],[0,3,100,104],[0,4,5,100,101],[0,100,101,105],[0,6,100,104,106],[1,2,107],[1,4,107,3,102],[1,4,7,102,108],[1,102,109,110],[1,6,102,8,108,111],[2,3,112],[2,3],[2,113,103],[2,114,6,103],[2],[3,112,115,105],[3,6,106,8,116,117],[4,9,105,113],[4,6,10,11,117,106],[6,106,118,119]]),
([w45,w0,w1,w2,w3,w30,w38],[51,36,1,21,2,25,3,5],[4,32,13,19,21,2,3,37,38,6,26,10,14,15,50,23],[[0,1,100],[1,2,101,3],[1,4,102],[1,4],[1,103,5],[1,6,104,7],[0,1,105,101],[0,4,106,107],[0,1,100],[0,100,108,109],[0,1,104,100],[1,4,110],[1,3,101],[1,111,101],[1,3,111],[1,4,112],[4,113,106],[1,4,114],[1,103,112],[1,7,104],[1,115,104]]),
([w0,w1,w2,w3,w30,w33,w38],[52,53,2,28,25,54,0,1,5,55,3,6],[0,1,2,4,5,7,42,8,10,12,14,16,51,18,20,21,22,23],[[0,1,100,101,102],[0,2,100],[0,100,103,104],[0,3,100,4,101],[0,5,6,100,103],[0,3,100,4,103,105],[1,2,106,107],[1,107,102,104],[1,3,102,108],[1,5,7,107,102],[1,3,102,108,109],[2,110,106],[2,3,111],[2,3],[2,112,3,106],[3,111,113,104],[5,8,104,110],[3,105,114,115],[2],[3,9,5,105,116,117],[3,5,10,11,117,105]]),
([w46,w0,w1,w2,w3,w30,w38],[56,25,0,28,1,2,5,3,8,57],[38,10,15,18,23,1,3,4,9,32,27,13,16,36,21],[[0,1,2,100,3],[1,101,4],[1,5,102],[1,103,6],[1,5],[1,7,104,8],[0,1,105,9,100],[0,1,5,106],[0,1,107,100],[0,1,3,100],[0,1,3,107],[5,108,9,106],[9,101,109,110],[1,101,9],[1,104,9,101],[5,111,106],[1,5,112],[1,5,113],[1,103,112],[1,114,104],[1,8,104]]),
([w0,w1,w2,w3,w30,w38,w47],[58,59,6,9,2,36,28,3,0,21,1],[34,0,4,38,8,32,10,17,14,51,18,19],[[0,1,2,3,100],[0,3,4,101],[0,3,102,5,101],[0,3,103,6,101],[0,2,7],[0,2,8,3,103],[1,2,4,104],[1,2,105,9,104],[1,2,106,6,104],[1,2,7,3],[1,2,10,3,105],[4,107,5,108],[4,109,6,107],[2,4,7],[2,4,5],[5,6,108,110,111],[2,7],[2,5,110],[2,7],[2,6,111],[2,4]]),
([w0,w1,w2,w3,w30,w47],[58,59,11,2,6,0,9,1,3,5,8],[0,1,2,4,5,6,7,8,10,11,12,36,50,18,19,21,23],[[0,1,100,2,101,102],[0,3,100],[0,100,103,104],[0,100,101,105],[0,101,2,4,106,5],[1,3,107],[1,107,102,104],[1,102,108,109],[1,102,2,6,110,7],[3,111,112],[3,112,111],[3,8],[104,105,113,114],[104,9,2,115,106],[105,10,2,116,106]]),
([w48,w0,w1,w2,w3,w30],[60,3,0,1,2,5,8,61,10,21,28,25,36],[7,12,36,21,23,0,1,2,3,4,5,6,9,8,10,11,13,15,18,19],[[0,1,100,2],[1,101,3],[1,4,102],[1,103,5,100],[1,104,6,100],[0,7,105,8,106,107],[0,4,108,105],[0,9,105,109,110],[0,10,105,11,106,111],[4,112,7,108],[7,9,113,12,107,110],[7,10,107,114,115],[4,116,9,108],[4,117,10,108],[9,10,110,118,119]]),
([w0,w1,w2,w49,w3,w30,w38],[62,63,8,5,64,0,28,1,21,2,3],[34,0,37,24,6,52,7,8,46,27,53,28,29,14,16,36,18,19,54,39,48],[[0,1,2,3,100],[0,2,101,4,102],[0,2,3,5],[0,2,3,103],[0,2,6,104,105],[0,2,6,106],[1,3,107,4,108],[1,2,3,7],[1,3,8,109,110],[1,2,3,111],[1,3,6,112],[2,4,9],[3,113,4,109],[2,114,4,104],[4,6,115,106],[2,3,116],[2,117],[2,6,10],[2,3,118],[3,6,119],[2,6,120,8]]),
([w0,w1,w2,w3,w30,w34,w38],[65,66,67,21,28,8,25,5,36,6],[0,1,2,3,4,40,7,8,9,44,10,12,13,15,17,54,55,21,56,23],[[0,1,100,101,102],[0,2,101,100,103],[0,3,100,104],[0,4,100,5,101,105],[0,100,101],[0,3,100,6,104,106],[1,2,102,107,108],[1,3,107,7,102,109],[1,4,102,110],[1,107,102],[1,3,102,8,110,111],[2,3,103,112],[2,4,103,113],[2,103,112],[2,3,103,114],[3,4,115,109,105],[4],[3,4,7,106,116,117],[3],[3,5,105,4,118,119],[3,106,9,117]]),
([w50,w0,w1,w2,w3,w30,w38],[68,36,21,2,28,5,69,8],[4,32,13,19,21,2,0,3,38,6,8,10,15,16,36,18,57,23],[[0,1,100],[1,2,101],[1,102,3],[1,4],[1,103],[1,5,104],[0,1,105,101],[0,6,100,106,107],[0,1,100],[0,4,100,7,108,109],[0,1,104,100],[1,110,6,101],[1,2,101],[1,111,4,101],[1,2,111],[1,102,6],[4,6,102,112,113],[1,114,6,104],[1,115,4,116],[1,5,104],[1,117,7,104]]),
([w51,w0,w1,w2,w3,w30,w38],[70,28,8,5,2,71,21,72],[38,10,15,18,23,1,0,4,8,9,32,27,13,14,36,19,57,21],[[0,1,2,100],[1,101,3],[1,102,4],[1,103],[1,3],[1,2,104],[0,2,105,3,100],[0,2,106,5,100],[0,2,107,3,100],[0,1,2,100],[0,1,2,107],[3,5,101,108,109],[3,6,7,101,110,111],[1,101,3],[1,104,3,101],[3,5,102,112,113],[1,102,5],[1,114,5,104],[1,115,3,116],[1,117,3,104],[1,2,104]]),
([w0,w1,w2,w3,w30,w38,w52],[73,74,36,9,75,28,6,21,3,5],[34,0,37,58,38,8,46,32,10,20,13,15,16,55],[[0,1,2,3,100],[0,3,101,4,102],[0,2,3,103],[0,3,104,5,101],[0,2,3,6],[0,2,3,6],[1,2,105,4,106],[1,2,6,107,7],[1,2,108,5,105],[1,2,7,3],[1,2,7,3],[2,109,4,110],[4,5,110,111,112],[2,3],[2,3],[2,113,5,109],[2,8,3],[2,5],[2,3],[2,3],[2,9]]),
([w53,w0,w1,w2,w3,w30,w38],[76,21,9,0,5,2,3,8,77,28,6],[32,13,19,21,34,0,37,58,38,8,10,20,15,16,55],[[0,1,2,3],[1,4,100],[1,101,5],[1,6],[1,102,7],[1,103],[0,2,4,104],[0,2,105,8,106],[0,1,2,107],[0,2,108,9,105],[0,1,2,10],[4,109,8,100],[1,4,100],[4,110,9,100],[1,2],[1,111,8,101],[8,9,101,112,113],[1,2],[1,114,9,102],[1,4,2,6],[1,2]]),
([w0,w1,w2,w3,w30,w38,w54],[78,6,9,79,21,28,3,8],[34,0,37,4,38,8,46,32,59,3,13,14,22,15,56],[[0,1,2,100],[0,2,101,3,102],[0,2,103,4,101],[0,2,5,104],[0,1,5],[0,1,5],[1,105,3,106],[1,107,4,105],[1,5,108],[1,5,2],[1,5,2],[3,4,109,110,111],[3,5,112,113],[1,3,5],[1,3,5],[4,5,114,112],[1,5],[1,4,5],[1,5,6],[1,4],[1,7]]),
([w55,w0,w1,w2,w3,w30,w38],[80,8,0,28,6,1,2,21,81,9,3],[38,15,18,23,34,0,4,8,46,32,59,13,14,22,56],[[0,1,2,100,3],[1,4,5],[1,101,6],[1,102,7],[1,7],[1,3,103],[0,1,4,104],[0,1,105,8,100],[0,1,106,7,100],[0,1,3,100],[0,1,3,4],[4,107,8,108],[4,109,7,107],[1,4,110],[3,4,9],[7,8,101,111,112],[1,113,8,101],[3,4],[1,114,7,102],[3,4],[1,3,4,10]])]
noncomputable def p20_D7 : List StD := [
([w1,w4,w2,w5,w3,w30,w38],[0,4,12,14,82,8,9,83,10,84,13,85,11,5,86,87,88],[26,1,27,28,2,29,6,7,60,61,3,16,24,19],[[0],[1,2,100],[2,1,3,101],[2,4,102],[2,103,5,104],[2,6,105,7,104],[1,2,8],[1,2],[8,102,9],[5,8,106],[7,8,10,107,108],[0],[1,4,109,11,110],[1,111,5],[1,6,12,8],[11,3,13,14,112,102],[5,3,113,15,4,101,106],[7,3,8,4,12],[5,11,102,16,4,113,106],[7,8,4,12],[7,5,8,12]]),
([w1,w4,w2,w3,w6,w30,w38],[0,5,89,11,86,19,8,15,17,4,90,10],[26,9,24,34,1,28,29,6,7,62,61,3,16,54],[[0],[1,100,2,101],[1,3,102],[1,4,103,5,104],[1,105,6,103],[1,3,106,103],[2,3,101],[1,3,7],[1],[3,107,6],[3,8,108,109],[1,110,2,102],[5,2,9,4,111,101],[6,2,101,10,112,107],[3,2,11],[0],[1,113,6,102],[1,3,11],[6,5,112,10,4,104,107],[3,5,11],[3,6,11]]),
([w40,w1,w4,w2,w3,w30,w38],[8,11,22,4,5,7,91,82,26,92,93,94,95,96,10],[1,15,18,63,64,27,65,66,3,6,7,43,61],[[0,1,100],[0,1,2],[0,101,3],[0,102,4],[0,1],[0,1,5],[0],[1,103,6,104],[1,7,105],[0,1,106],[1,8,107,9],[1,10,108,6],[1,11,105,12],[0,1,109],[1,9,110,111],[12,6,101,7,13,112,102],[0,101,6],[1,6,9],[0,7,102,12],[1,9],[0,1,14]]),
([w0,w4,w2,w7,w3,w30,w38],[5,30,4,31,87,10,97,32,11,82,8,98,99],[26,2,24,25,6,7,27,67,14,68,18,28],[[0],[1,2,100],[1,2,3,101],[0,1,102,103],[1,4,104],[1,5,105],[2,1,5],[1,2],[0,5,106],[5,104,6],[5,7,105,107],[0],[0,2,108],[2,4,109,6,100],[2,5,8],[0,3,110,9,4,101,106],[6,3,10,11,111,104],[5,4,8],[6,0,104,4,12,110,106],[5,8],[5,4,8]]),
([w42,w0,w4,w2,w3,w30,w38],[0,37,5,33,4,100,8,11,7,101,87,102,103,104,105,106,10],[2,13,19,3,69,6,7,27,70,68],[[0,1,2,100],[0,1,3,2],[2,101,4],[2,5],[2,102,6],[2,7,8],[2],[1,103,9],[1,2,104],[1,10,105],[1,7,106],[7,11,103,9],[2,7,107],[7,12,105,13],[7,14,106,108],[2,101,9],[13,9,101,10,15,109,102],[7,9,16],[2,10,102,13],[2,7,16],[7,13,16]]),
([w0,w4,w2,w3,w30,w32,w38],[10,5,107,8,87,41,39,42,108,4,11],[3,24,25,28,34,2,7,27,71,14,68,26,72],[[0,1],[0,100,2],[0,101,1,102],[0,3,103],[0,4,104,5,105],[0,3,106],[0,100,2],[0,107,1],[0,3,6],[0,3],[0,7,106,108],[1,2,100,8,109,107],[3,110,2,103],[5,2,9,4,111,100],[0,10],[3,112,1,103],[5,1,109,4,8,105,107],[0,8,10],[0],[0,3,10],[0,4,10]]),
([w0,w1,w2,w10,w3,w30,w38],[30,10,4,12,31,85,87,93,14,82,102,97,11,109,5,8],[24,0,6,7,27,28,8,29,61,3,68,18,19],[[0,1,2,3],[0,2,3],[4],[0,100,5,101],[0,6,102,7],[0,1,103],[1,0,2],[8],[1,9,104,10],[1,105,7,106],[1,3,107,106],[1],[2,9,108,5,109],[2,6,110,11,109],[1,2,12],[5,13,14,6,104,111],[11,13,15,9,102,112],[1,6,12],[7,5,102,6,9,111,104],[1,9,12],[1,6,12]]),
([w0,w1,w2,w3,w12,w30,w38],[33,11,5,110,15,87,94,111,19,112,2,10,113,8],[34,3,6,7,26,9,27,28,32,29,61,15,16,54],[[0,1,100,2],[0,101,3],[0,2,4],[2],[0,5,102,6],[0,1,103],[1,104,7,105],[1,0,2,106],[8],[1,107,6,108],[1,2,109,108],[2,110,3,106],[9,10,5,101,111],[6,3,101,5,112,102],[1,3,11],[1],[2,5,113,12,106],[1,2,11],[12,9,13,3,102,112],[1,11],[1,6,11]]),
([w0,w1,w2,w3,w30,w56,w38],[39,11,22,110,114,8,41,111,82,103,25,115,2,5,10],[34,3,24,25,6,7,26,9,27,29,14,68,13,54],[[0,1,100,2],[0,101,3],[0,102,4,103],[0,2,5,104],[6],[0,1,105],[1,106,7,107],[1,8,108,9],[1,0,5],[5],[1,2,109,10],[4,3,101,8,110,108],[5,111,3,104],[11,12,8,101,112],[1,3,10],[5,8,113,4,104],[11,4,13,3,108,110],[1,4,10],[1],[1,5,14],[1,10]]),
([w57,w0,w1,w2,w3,w30],[116,10,5,2,8,117,118,119],[3,21,23,34,60,1,62,67,2,71,27,13,14,6,15,16,18,19],[[0,1,2],[0,1,2],[1,100,3],[1,101,2],[1,102,4],[0,1,103,5],[0,104,105],[0,106,6,104],[0,105,104],[1,107,108],[1,108,107],[1,109,7,107],[6,110,111,112],[7,113,114,115],[6,7,110,116,117]]),
([w0,w1,w4,w2,w3,w9,w30,w38],[47,5,82,120,4,48,121,49,50,122,123],[],[[0,1],[1],[0,2],[0,1],[0,3],[0,2],[0,2],[0],[1,4],[5,2],[1,2],[1,3],[1,3],[4,2,6],[1,6],[6,7],[6,2],[8,2],[1,2],[1],[3,9],[3,10,6],[4],[1,2],[1,2],[3,2],[3,2],[6,10]]),
([w0,w1,w4,w2,w3,w30,w33,w38],[52,53,4,124,87,125,8,54,55,122,126],[],[[0,1],[1],[0,2],[0,3],[0,4],[0,4],[0,3],[0],[1,4],[1,4],[1,3],[1,3],[1,4],[2,4,5],[5,3],[5,6],[5,7],[8,3],[2,9],[2,6],[6],[2,10,5],[3,4],[3,4],[5,10],[2],[3,4],[3,4]]),
([w0,w1,w4,w2,w3,w30,w34,w38],[65,5,82,87,127,8,128,4,129,130],[],[[0,1],[1],[0,2],[0,1],[0,2],[0,3],[0,2],[0],[1,3],[4,2,3],[1,5],[1,2],[1,3],[4,2],[1,3,4],[4,2],[4],[6,2],[1,2],[5,3],[7,2,8],[4,9],[1,2],[5],[1,2],[1],[4,3,5],[4,2,8]]),
([w1,w2,w5,w3,w6,w30,w38],[16,131,85,14,5,82,49,10,19,12,8,132,133,9,94,17,13],[26,3,8,32,28,6,29,7,61,0,16,4,19,39,5,12,48],[[0,1,100,2,101],[3,2,4,5,102,103],[6,7,102,5,1,103],[8,2,9,5,103,102],[10,2,102,11,1,104,105],[12,2,102,13,1,106,107],[7],[0,5,108,2,101],[0,1,101,8,109],[0,110,10],[0,13,7,101],[2,3,4,0,14,111,1],[0,2],[10,3,111,1,105,112],[7,3,15,13,1,107,111],[3],[10,2,105,5,112],[7,2,107,13,5,113,114],[10,8,109,1,105,110],[7,8,16,13,1,107,115],[7,10,105,13,11,116,107]]),
([w1,w2,w5,w3,w30,w31,w38],[23,131,10,14,22,82,87,132,8,134,135,25,129,114,136,85],[26,3,8,32,28,6,2,29,7,61,27,5,38,12,54,39,23],[[0,1,100,2,101],[3,2,4,5,6,102,103],[7,2,102,5,1,103],[8,1,104,2,105],[8,106,2],[9,10,11,1,107,108],[2],[0,5,109,12,101],[0,8],[0,1,101,8],[0,11],[13,3,110,1,111],[8,0,3,112],[0,8],[2,3,11,1,108,113],[8,5,114,14,105],[8,111,15],[2,7,11,5,115,108],[2],[2,8,11,116],[2,8,11,108]]),
([w0,w1,w2,w5,w10,w3,w30,w38],[30,4,12,137,131,14,138,82,93,102,11,10,109],[],[[0,1,2],[0,1],[1],[3],[0,4],[0,4],[0,4],[1,0,2],[2,5],[5],[2,4],[2,4],[2,4],[0],[6],[1,7,8],[1,9],[1,10,11],[2],[5,4],[5,4],[5,4],[12,4],[12,4],[11,4,10],[8,7,9],[8,7,10],[9,10]]),
([w14,w0,w1,w2,w3,w30,w38],[0,139,140,30,14,5,8,10,11,12,85,87,96,141,132,142,143],[14,6,1,24,7,9,27,11,12,68,54],[[0,1,2],[3,4],[1,2],[4,100,5],[4,101,6],[4,7,8],[1,7,102,9],[1,2,9],[1,103,10,102],[1,11,101,12],[1,7,104],[2,7,105],[7,13,106,14],[7,14,107,15],[7,9,108],[2,16,100,10],[2,11,109,15,105],[2,7,8],[12,10,100,11,13,110,101],[7,8],[7,8]]),
([w0,w1,w2,w5,w3,w8,w30,w38],[33,82,34,131,85,141,12,37,144,11,10,145,14],[],[[0,1],[0,1],[2],[0,3],[0,4],[0,1],[0,1],[2,3,4],[4,1,5],[6,3],[7],[4,3],[4,3],[0],[2,1,4],[2,1,4],[2,8],[2,9,10],[4,3,11],[4,12],[5,1],[10,1,9],[6],[4,1],[4,1],[4,1],[4,1],[5,9]]),
([w42,w0,w1,w2,w5,w3,w30,w38],[0,85,33,143,14,100,37,38,131,102,132,12,11,10,145],[19],[[0,1],[2],[1,3],[1,4],[5],[1,3],[1,3],[1,6],[6,3],[7],[1,8,6],[6,3],[6,3],[1,8],[1,9,10],[9,8,11],[1,8],[1,8],[6],[1,3],[7,9],[7,12,13],[1,8,14],[100,3],[10,3],[1,3],[1,3],[9,10,12]]),
([w0,w1,w2,w5,w3,w30,w32,w38],[39,12,40,131,96,132,43,8,129,11,10,5,145,14,41,146],[],[[0,1],[0,2],[2],[0,3],[0,3],[0,4],[0,3],[1,3],[1,5],[1,3],[1,3],[6],[1,3],[0],[2,4],[2,7],[2,3,8],[2,9,10],[11,3,12],[7,3],[13,14],[5,3],[4,15],[4,3],[4,9],[1],[7,5],[8,3]]),
([w0,w1,w5,w3,w30,w33,w38],[52,147,2,102,8,54,25,14,53,87,108,145,12,131,148,93,85,132,11],[2,5,0,3,7,32,8,10,27,15,12,18,39,73,16],[[0,100,1],[2],[0,101,3],[0,4,102],[0,3,102,5,103],[0,6,104],[7,1,8,3,9,100,105],[3,1,106,10,11,100],[4,107,1],[5,1,12,3,13,106,100],[3,1,6,11,107],[14,7,108,15,101],[4,0,7,109],[0,4],[6,10,104,7,110],[4,111,3],[5,16,101,15,10,111],[6,10,112,17,104],[2],[3,4,6,113,114],[6,17,18,5]]),
([w0,w1,w5,w3,w30,w47],[58,11,2,14,149,12,9,150,60,85,82,8],[2,5,0,6,3,32,8,10,27,36,50,18,19,23],[[0,1,100],[0,2],[0,101,102],[0,103,102],[0,1,102,104],[1,100,3,105],[1,100,106],[1,107,4,100],[1,5,6,100],[3,7,108,109,101],[3,4,109,110,103],[0,1,8],[4,103,111,112],[1,9,101,10],[1,4,11,113]]),
([w0,w1,w2,w5,w3,w15,w30,w38],[47,82,16,131,20,102,14,12,132,93,129,51,151,8],[],[[0,1],[0,1],[2],[0,2,3],[4],[0,1],[0,1],[2,3,5],[6,1],[5,1],[7,1,8],[9,3,8],[5,3,10],[0],[2,0,9],[11],[2,5],[2,12],[6,3],[4],[6,1],[6,1],[6],[5,1],[8,1],[13,1],[8,1],[5,8,10]]),
([w0,w1,w2,w3,w15,w30,w38],[47,85,16,49,93,152,131,123,82,132,1,19,153,121,14,8,10,11],[34,0,6,7,26,3,8,32,49,28,16,36,54,5,39,48],[[0,100,1,101],[0,2,101],[0,2,1,101],[3],[0,102,4],[0,5,103,4],[2,6,104,1,105],[3,7,106,8,6,107],[9,1,10,4,106,108],[4,1,102,9,6,109,106],[4,1,103,5,6,108,106],[1,2,0,105],[11],[2,110,12],[2,7,111,13,105],[14],[4,1,102,8,112,113],[4,1,103,5,8,114,113],[12,15,5,102],[13,9,16,7,6,17],[13,12,102,5,9,115,103]]),
([w16,w0,w1,w2,w3,w30,w38],[0,154,155,1,14,47,8,11,10,85,94,156,102,157,158,145,132,146,159],[8,6,34,0,4,27,53,28,29,7,13,3,16,36,72,21,48],[[0,1,2],[3,4,100],[1,2],[5,4],[4,101,6],[4,7,8],[1,102,9,103],[1,2,103],[1,10,104,9,103],[1,101,10],[1,11,104,12,103],[2,13,100,9],[12,14,100,10,15,105,106],[10,9,100,16,13,107,101],[12,9,100,11,13,108,109],[2,10,110,9,111],[2,112,10],[2,11,113,14,110],[15,9,101,17,11,114,105],[14,9,105,18,10,115,109],[12,10,101,11,16,116,109]]),
([w58,w0,w1,w2,w5,w3,w30,w38],[16,10,141,132,47,160,8,85,11,82,51,20,131,102,151,14,129],[],[[0],[1,2,3],[4],[0],[5],[6,2,7],[1,8],[2,9],[10,9],[11],[7,12,10],[2,9],[3,9],[2,12,7],[2,9],[3,2],[7,3,12],[2,12,7],[10],[7,9],[2,13],[3,14],[7,12,15],[2,9],[3,9],[7,2],[3,9],[2,3,16]]),
([w0,w1,w2,w5,w3,w30,w59,w38],[52,82,23,131,27,102,14,8,132,11,161,129,151],[],[[0,1],[0,1],[2],[0,3],[0,1],[4],[0,1],[2,3,5],[6,1],[5,1],[7,3,8],[9,1,10],[5,3,11],[0],[2,1,11],[2,0,5],[7],[2,12],[6,3],[6,1],[4],[6,1],[5,1],[10,3],[8,1],[6],[5,8,7],[10,1]]),
([w0,w1,w2,w3,w30,w59,w38],[52,87,96,23,102,54,25,126,82,131,161,11,129,5,14,8],[2,3,5,0,7,26,8,28,6,32,29,61,50,54,27,39,73],[[0,1,100,2],[0,2,101,3],[0,102,4],[0,1,3,2,103],[5],[0,6,104],[3,1,105,7,101],[4,2,106,8,1,100],[5,6,9,107,7,108],[10,7,11,4,100,109],[4,6,1,110,12,104],[3,8,111,12,101],[3,0,6],[6],[3,6,112],[2,4,6,8,113,108],[10,13,1,102,114],[2,6,8,115,12,104],[14],[4,5,15,6,116,108],[6,1,11,10]]),
([w60,w0,w1,w2,w3,w30,w38],[0,162,163,11,14,5,52,25,87,96,103,164,141,129,108,8],[8,5,2,3,38,0,7,59,19,29,61,15,50,57,39,48],[[0,1,2],[3,4,100],[1,2],[4,101,5],[6,4],[4,3,7],[1,8,102,9],[1,2,103],[1,101,10],[1,7,104,105],[1,7,106],[2,8,100,11],[10,9,100,12,8,101,102],[7,107,11,108],[7,8,109,13,106],[2,14,110,10,103],[2,7,111],[2,7,112],[7,12,108,113],[7,14,114,10,106],[7,15,115,108]]),
([w0,w1,w2,w5,w3,w30,w34,w38],[65,82,67,165,5,132,166,129,25,146,141,14,68],[],[[0,1],[0,1],[2],[0,3],[0,1],[0,3],[0,1],[2,3],[4,1,5],[3,1],[3,5],[3,1],[3,6,7],[0],[2,1,6],[2,6],[2,1,6],[2,8],[4,9],[8,1,10],[11],[5,1],[8,9],[8],[5,1],[12],[6,5],[6,1]]),
([w50,w0,w1,w2,w5,w3,w30,w38],[0,85,11,108,132,14,62,65,68,167,136,102,157,69,25,146],[],[[0,1],[2,3,4],[1,3],[1,5],[6],[7],[1,2,3],[1,3,4],[8,3],[9],[1,8],[8,10],[4,3],[1,11,4],[1,3,4],[4,3],[1,4,3],[1,12],[8],[1,3],[3,11,13],[4,14],[1,15],[14,10],[4,3],[1,15,14],[1,3],[3,4]]),
([w1,w2,w3,w6,w30,w31,w38],[168,114,131,132,11,108,22,87,25,5,19,23,82,94,8],[3,8,46,32,28,6,34,29,7,61,5,9,15,36,54,39,38,12,23],[[0,1,100,101,2,102],[3,4,101,5,2,103],[3,1,6,5,7,103,101],[5,1,8,2,104,105],[8,106,1,9],[8,2,107,1,108],[1,0,100,5,109,110],[10,0,11,2,100,111],[5,0,8,112],[8,100,0],[8,113,0,108],[4],[8,12,114,1,105],[8,13,110,1],[8,5,115,1,108],[8,2,105,10,116],[8,13,116,1],[8,2,108,3,117],[4],[8,14,118],[8,14,108]]),
([w0,w1,w2,w7,w3,w6,w30,w38],[30,5,131,169,139,11,106,16,170,10,19,31],[],[[0,1],[0,2],[0,3],[0,1],[1],[0,2],[0,2],[1,2],[4],[5,2],[1,6],[1,2],[1,2],[1],[1,7],[7,2,8],[3,6],[3,5,9],[1,2],[10,11],[3,2],[3,2],[0],[1,3],[1,3],[6,2],[8,2],[6,5]]),
([w0,w1,w2,w3,w6,w12,w30,w38],[33,108,5,131,11,19,16,112,171,82,25],[],[[0,1],[0,1],[0,2],[2],[2],[0,3],[0,1],[2,3],[4,0,3],[2,5],[5],[1,3,2],[2,3],[2,1],[5,1],[6,1,7],[1,8],[7,4],[0],[4],[2,9],[2,1],[2],[5,3],[5,1],[7,3],[10,1,4],[1,4,7]]),
([w17,w0,w1,w2,w3,w30,w38],[0,37,5,19,33,2,25,11,110,15,87,172,106,132,173,10],[3,6,1,7,9,27,11,12,61,68,54],[[0,1,2],[2,3,4],[3,100,5],[1,2],[3,101,6],[3,7,6],[1,2,102],[1,100,8],[1,2,9],[1,10,101,11],[1,7,103],[2,12,104,13],[2,3,105,7],[2,13,106,14],[2,7,107],[2,108,8,105],[11,8,100,10,12,109,101],[7,8,15],[2,10,110,14,105],[2,7,15],[7,11,15]]),
([w0,w1,w2,w3,w6,w30,w32,w38],[39,5,131,172,11,132,43,40,170,171,25,19,41],[],[[0,1],[0,2],[0,1],[1],[0,2],[0,3],[0,2],[1,2],[4,2],[1,5],[1,2],[6],[1,2],[1,3],[7,2,8],[3,9],[3,2],[5,4,10],[0],[1,10],[1,2],[1,3],[10,2],[11,12],[5,2],[1],[3,4,5],[3,2]]),
([w0,w1,w2,w3,w6,w9,w30,w38],[47,82,5,16,49,106,132,108,156,19,21],[],[[0,1],[0,1],[0,2],[2],[0,3,4],[0,1],[0,1],[2,5,3],[4,1],[2,1,5],[2,1,4],[2,6,7],[2,8,5],[2,1],[3,0,9],[2],[3,5],[3,8,10],[0],[3],[2,1],[2,1],[0,3],[5,1],[6,1],[4,1],[4,1],[5,6,7]]),
([w0,w1,w2,w6,w9,w30,w38],[47,5,16,49,94,156,21,19,48,15,131,132,174,175,50,123,25,11],[34,35,61,5,6,7,8,32,28,29,14,16,36,12,48],[[0,100,1,101],[0,2,102],[1],[0,2,3,103],[0,104,4],[0,5,105,6],[2,106,1],[7,1,8,4,107,106],[3,1,9,4,10,103],[4,1,104,11,12,108,106],[6,1,105,5,12,109,106],[2,0,7,110],[1],[2,111,4],[2,5,112,6,102],[0,2],[13,7,110,5,104,111],[6,7,14,15,4,105,113],[13,3,16,5,111,104],[6,3,16,15,4,17],[6,4,104,5,11,114,105]]),
([w45,w0,w1,w2,w6,w30,w38],[0,51,19,16,5,47,160,25,11,176,21,132,171,177],[32,54,34,3,6,7,26,28,29,68,50,48],[[0,1,2,3,4],[2,4,100],[3,2,5],[2,6],[2,101,7],[2,8,7],[1,4,102],[1,3,103],[2,4],[1,104,9],[1,10,105],[3,4,106],[2,4,100],[4,11,107,9,100],[4,10,108],[2,3,103],[3,12,109,13,103],[3,10,110],[2,104,13],[2,10,105],[10,11,111,9,105]]),
([w0,w1,w2,w3,w6,w15,w30,w38],[47,108,131,85,49,132,106,156,19,16,151,154,25],[],[[0,1],[0,1],[0,2],[3],[4],[0,2],[0,1],[5,2,6],[5,1],[5,1],[5,1],[1,2,5],[6,2,7],[8,0,1],[8,1],[8],[1,6,9],[5,7,10],[0],[11],[6,7],[5,1],[4],[6,2],[5,1],[12,2],[5,1],[1,5]]),
([w18,w0,w1,w2,w3,w30,w38],[0,51,19,16,20,11,47,25,178,96,152,171,174,177,132,179,106,180],[32,6,34,0,7,9,46,28,29,14,68,50,54,39,48],[[0,1,2,3,4],[2,100,5],[3,2,6],[1,2,3],[2,101,7],[2,5,7],[1,102,8,103],[1,3,103],[1,2,3,103],[1,101,9],[1,10,104,9],[3,11,105,8,106],[2,12,100,9],[13,8,100,14,12,107,101],[13,8,100,10,11,108,104],[2,3,109],[3,11,110,13,105],[3,15,111,13,105],[2,112,9,109],[2,10,113,9,109],[16,17,101,10,11,114,104]]),
([w0,w1,w2,w3,w6,w30,w33,w38],[52,124,16,20,176,106,132,171,181,56,182,25,5,19,54],[],[[0,1],[0,2],[0,1],[3],[0,4],[0,4],[0,1],[1,5],[5,4],[5,1],[1,6],[1,5],[5,7,8],[1,7],[2,7],[2,5],[9],[1,10,11],[0],[1,5],[1,12],[6,4],[5,11],[13,14],[6,1],[2],[1,6],[1,6]]),
([w0,w1,w2,w3,w6,w30,w47],[58,11,16,150,176,183,132,5,9,156,182,25,19,8],[34,35,5,6,7,8,32,28,36,50,54,16],[[0,1,100,101],[0,2],[0,3,102],[3],[0,103,4],[0,1,104],[1,2,105],[1,4,102,5],[1,4,106,5,105],[1,6,107,4,105],[1,7,8,106],[2,9,108,3,109],[2,9,108,5,109],[2,10,109,11,108],[1,2,11],[0],[11,3,102,9,110,103],[1,3,7,4,102],[11,5,111,9,103],[1,5,12,4,104],[1,4,13,6,103]]),
([w48,w0,w1,w2,w3,w6,w30],[0,60,25,171,5,58,176,19,8,21,10,36,16,184,151],[7,29,39,48,34,3,6,26,32,8,28,61,9,68,54,16],[[0,1,2,100],[2,3,101,4],[5,2],[2,6,102,3,4],[2,6,100,3,7],[2,8,103,9],[1,10,104,11],[1,12,105],[1,9],[9],[1,2,106],[6,10,12,107],[9,10,108],[10,6,108,13,109],[2,10,110],[9,12,111],[12,14,105,13,112],[2,12,113],[1],[2,9,114],[2,14,106,13,115]]),
([w0,w1,w2,w3,w6,w30,w34,w38],[65,108,5,82,176,171,19,132,185,156,25],[],[[0,1],[0,1],[0,2],[2],[0,3],[0,4],[0,1],[2,5],[6,1],[2,1,6],[1,7],[2,1,8],[2,5],[2,1],[5,1],[1,5],[8,1],[4,9,10],[0],[2,3],[10],[2,1],[6,0,3],[0,10],[5,1],[2],[1,5],[8,1]]),
([w0,w1,w2,w6,w30,w34,w38],[65,5,176,25,171,19,66,87,185,15,131,67,156,186,16,8,11],[34,35,3,54,24,5,7,8,46,32,10,9,15,36,18,12,74],[[0,100,1,101],[0,102,2],[1],[0,3,103],[0,2,104,105],[0,3,106],[2,1,102,107,4,108],[5,1,6,2,7,109,107],[2,1,3,110],[8,1,9,2,10,105],[3,4,110,1],[4,11,12,102,111],[3,112,13],[8,13,14,4,112,102],[3,113,2,106],[3,0,5,114],[0,3],[3,2,106,4,115],[1],[3,15,116,103],[3,2,16,8]]),
([w50,w0,w1,w2,w6,w30,w38],[0,68,5,19,16,62,65,25,11,187,106,8,21],[24,32,61,34,3,6,7,26,28,29,68,36,48],[[0,1,2,100],[2,3,101],[2,102,4],[3,5],[6,2],[2,7,8],[1,2,103],[1,104,9],[2],[1,7,105],[1,7,106],[2,10,107,9,101],[2,3,101],[2,7,108],[2,7,109],[3,104,9],[7,10,110,9,105],[7,111,9,106],[3,7,105],[3,7,106],[7,11,112,12]]),
([w0,w1,w2,w3,w6,w30,w61,w38],[65,108,131,114,176,129,19,132,5,185,171,156,25],[],[[0,1],[0,1],[0,2],[3],[0,2],[],[0,1],[4,2,5],[6,1],[6,1],[1,2,7],[8,1,9],[5,2],[5,1],[6,1],[1,10],[9,1],[4,11,12],[0],[6,0,11],[12],[5,1],[6,2],[12],[6,1],[6],[1,7],[9,1]]),
([w0,w1,w2,w3,w30,w61,w38],[65,87,114,176,25,19,130,131,185,5,174,156,2,8,11],[34,35,3,24,5,6,0,7,8,46,32,28,29,61,15,9,36,39,74],[[0,1,100,2,101],[0,102,3],[0,3,103,2,104],[0,1,105,3],[0,106],[0,4,107],[3,2,102,108,1,109],[5,6,108,3,1,104,110],[3,2,4,7,111,105],[8,2,9,3,110,108],[4,1,112,2,107],[2,10,102,11,113,104],[4,114,10],[8,12,1,102,115],[4,116,3,107],[4,0,2,105],[4],[4,3,117,2,107],[5],[4,13,118,105],[4,1,14,8]]),
([w62,w0,w1,w2,w3,w30,w38],[0,68,19,5,2,65,11,25,87,188,176,106,189,146,8],[32,3,34,35,24,5,38,52,7,26,59,16,29,61,75,36,18,39,48],[[0,1,2,3],[2,100,3],[2,101,4],[1,2,3],[5,2],[2,6,7],[1,8,102,9,103],[1,101,10],[1,2,104,105],[1,7,106,107],[1,7,108],[10,9,100,11,8,109,101],[2,8,100,12],[7,110,9,111],[7,8,112,9,108],[2,113,13,105],[7,11,111,114],[7,115,10,108],[2,7,116],[2,7,117],[7,14,118,111]]),
([w0,w1,w2,w63,w3,w30,w38],[47,5,20,49,16,190,96,21,175,11,153],[2,0,5,6,7,8,28,29,16,36,54,39,48],[[0,1,100],[0,2,101],[0,3,4],[0,1,102],[0,5,103,6],[0,7,104],[1,2,105],[1,3,105],[1,3,100],[1,5,106,8,100],[1,7,107],[1],[1,0,2],[2,108,8],[2,7,109],[0,1,2],[3,108,8],[3,7,9],[1,110,6,102],[1,7,111,102],[7,5,112,10,104]]),
([w0,w1,w2,w3,w30,w64,w38],[65,5,165,49,8,87,25,21,132,146,185,2,11],[2,3,5,38,0,7,26,10,61,15,36,39,74],[[0,1,100],[0,2,101,3],[0,1,102],[0,4,103,104],[0,5,103,2,104],[0,6,105],[1,2,106,3,100],[1,7,100],[1,4,107],[1,8,107,2,100],[1,6,107],[1,108,9,102],[4,109,3],[10,3,11,5,109,101],[6,110,3,105],[1,0,4],[0,4],[1,6,111],[1],[4,6,112,7],[6,5,12,10]]),
([w0,w1,w2,w3,w30,w65],[73,11,49,5,6,21,191,9,192],[2,0,37,5,38,8,10,76,3,15,16,77],[[0,1,100],[0,101,2,102],[0,3,103],[0,104,101],[0,1,4,5],[1,105,2,100],[1,3,100,5],[1,106,6,100],[1,3,7,5],[2,3,107,103],[2,6,108,109,110],[1,2,5],[2,3,111,6,103],[0,1,3,8],[1,5]]),
([w39,w0,w1,w2,w9,w30,w38],[47,5,16,21,193,153,50,20,49,190,165,11],[32,19,76,2,0,6,7,8,28,29,16,36,48],[[0,1,2],[1,3,100],[1,0,2],[4,1],[1,101,5],[1,3,102,6],[0,1,103],[0,7,104],[0,8,104],[0,9,105,10],[0,3,106],[1,7,107],[1,8,100],[1,9,108,5,100],[1,3,109],[1],[5,7,110],[3,7,111],[5,8,101],[3,8,11],[3,9,112,5,106]]),
([w39,w0,w1,w2,w3,w30,w33,w38],[16,49,194,52,8,54,25,124,165,190,195,196,197,148,182],[32],[[0],[1,100],[0,2],[3],[1,4],[1,5],[1,6],[3,7],[1,8],[1,7,3],[3,9,8],[3,8,10],[2,7,3],[1,8],[1,11,12],[4,9],[7,8],[2,11,13],[2,7],[1,4],[4],[1,14,2],[1,4],[1,7],[1,12],[1],[2,9,4],[2,9,7]]),
([w39,w0,w1,w2,w3,w30,w47],[58,21,16,150,20,149,11,190,165,9,182,8],[32,36,19,2,0,5,6,38,8,28,16],[[0,1,2],[1,3,100],[1,4,101],[0],[1,102,5],[1,6],[0,3,103],[0,4,104],[0,1,105],[0,7,106,8],[0,6,104,107],[3,4,108],[1,3,100],[3,7,109,5,100],[3,6,9,100],[1,4,101],[4,10,110,5],[1],[1,102,5],[1,6,105],[6,5,11,7,102]]),
([w39,w0,w1,w2,w30,w34,w38],[65,5,21,67,8,25,165,198,190,185,20,182,11],[4,32,13,77,2,3,54,5,7,26,10,15,36,74],[[0,1,100],[1,2,101],[1,102,3],[1,0,4],[4],[1,2,103,5],[0,1,104],[0,6,105,7],[0,4,106],[0,8,107,6],[0,2,108],[1,6,109,7,101],[1,4,110],[1,8,101,6,107],[1,2,110],[4,111,7],[9,7,10,11,102,105],[2,112,7,108],[1],[2,4,113],[2,8,12,9]]),
([w0,w1,w2,w7,w3,w30,w31,w38],[30,87,22,131,199,27,139,97,200,23,11,201,202,31],[],[[0,1,2],[0,3],[0,1,4],[0,3],[0,3],[5],[0,3],[2,1],[6],[2,1],[2,3],[2,7],[2,1],[2],[4,8],[7,1],[5,1,7],[9,10,11],[4,1],[7,3,12],[7,13],[11,1,10],[7,1],[7,1],[4,10],[0],[7,1],[7,1]]),
([w0,w1,w2,w3,w8,w30,w31,w38],[33,87,114,131,95,11,37,108,113,203],[],[[0,1,2],[0,3],[0,3],[0,1,2],[0,3],[4],[0,3],[2,1],[5,1],[6],[2,3],[2,7,8],[2,1],[2,7],[2,1],[7,1],[8,1],[9,5],[5],[2,1,8],[2,1,8],[2,5,7],[2,3],[2,8],[2,1],[0],[7,1],[8,1]]),
([w42,w0,w1,w2,w3,w30,w31,w38],[0,114,33,143,100,8,87,37,131,95,11,190,104,173],[],[[0,1],[2],[1,3],[4],[1,3],[1,5],[1,3],[1,6],[7,3],[1,8,7],[7,3],[9],[7,3],[1,6],[10,6],[1,8],[1,11,12],[1,6],[1,3],[12,6],[12,3],[11,10,13],[1,3],[1,6,12],[1,3],[7],[12,6],[12,3]]),
([w0,w1,w2,w3,w9,w30,w31,w38],[47,108,190,143,27,200,204,23,51,153,205,175,5,49],[],[[0,1],[0,1],[0,2],[0,2],[0,3],[4],[0,1],[2,5],[2,1],[2,1],[1,2],[5,1],[3,6],[7,5],[8],[1,6],[4,1,9],[2,10,11],[7],[5,3,6],[5,12],[2,1],[6,3],[9,13],[2,1],[0],[1,2],[9,1]]),
([w45,w0,w1,w2,w3,w30,w31,w38],[0,114,190,197,47,160,99,8,51,129,95,171,180,200,23,182,177],[],[[0,1],[2,3],[4],[5],[1,6],[1,7],[1,3],[1,3,8],[2,9,8],[1,8],[8,6],[10],[8,3],[1,11],[2,3],[1,2,3],[1,2,12],[1,11],[1,13,14],[6,11,9],[12,9],[2,15,16],[1,6],[1,12],[1,3],[8],[3,2],[12,2]]),
([w0,w1,w2,w3,w31,w33,w38],[52,87,206,23,190,25,27,54,197,11,131,182,148,114,143,8],[2,5,6,7,8,29,14,50,39],[[0,1,100,2],[0,3],[0,101,4],[5,6],[0,1,3,7,102],[0,5,103],[3,1,104,2],[4,2,104,8,1,100],[5,100,2],[7,2,9,4,10,104,100],[5,1,105,2,103],[3,106,11],[3,0,5],[5],[3,5,107],[5,101,12],[7,13,101,1,14,106],[5,8,108,4,103],[0,3],[5,15,103],[5,1,9,7]]),
([w0,w1,w2,w3,w30,w31,w47],[58,11,23,190,25,27,197,22,9,205,182,99,202,150],[2,5,6,7,8,28,14,50,54],[[0,1,100],[0,2],[0,101,3],[0,4,102],[4,5],[0,1,103],[1,2,104],[1,6,100,3,101],[1,3,105,4],[1,3,100,4],[1,7,8,100],[2,9,106,10],[2,4,107],[2,4,107],[1,2,4],[4,11,108,12,102],[4,101,13],[1,3,101,6],[0],[1,4,102],[1,4,103]]),
([w0,w1,w66,w2,w3,w30,w38],[39,11,26,87,22,96,54,172,95,182,25,2,41,174,143,10],[1,3,24,7,9,27,12,61,68,6,54],[[0,1,100,2],[0,3,4,2],[0,5,101,6],[0,7,102,8,100],[0,3,100,2],[0,1,103],[6],[1,104,6],[1,105,9],[1,0,6,10],[1,2,106],[6,7,11,3,104,12],[8,5,12,105],[0,1],[1,7,10],[8,6,101,7,5,107,105],[7,10,108,13,109],[1,6,10],[5,8,10,14,110,109],[1,8,10],[1,6,12,15]]),
([w0,w1,w2,w67,w3,w30,w38],[52,96,27,23,176,165,25,171,126,5,54,174,41,11,99,106],[34,0,24,6,7,8,27,53,28,29,14,50,54,39,73],[[0,100,1,101],[0,1,101,2],[0,1,3,2],[0,4,102,5,101],[0,6,103],[0,6,104],[2,7,105,8],[4,8,9,5,105,10],[5,1,105,4,11,106,107],[4,6,11,108,8,103],[5,6,7,109,12,104],[6],[2,110,7],[2,0,6],[2,6,111],[9,10,110],[0,2],[6,7,13,4],[1,6,14,112,15,103],[1,6,4,113,7,104],[6,10,114,103]]),
([w0,w1,w2,w3,w68,w30,w38],[65,95,165,54,176,25,28,171,130,207,11,157,143,2,99,8],[34,0,37,4,6,3,26,46,8,32,28,29,7,13,15,36,21,74],[[0,100,1,101],[0,2,101,3,102],[0,4,103,1,101],[0,4,103,2,101],[0,5,104],[0,5,103,6],[3,1,105,2,7,106,107],[2,8,108,4,9,109],[2,1,10,4,109,108],[2,1,5,11,110,104],[2,1,5,7,111,112],[1,3,105,12,113],[11,3,13,7,113,105],[5,114,14],[5,115,3,112],[3],[3,1,5,0,104],[5,4,116,1,112],[0,1],[5,4,10,11],[5,15,117,104]]),
([w40,w0,w1,w2,w7,w3,w30,w38],[23,11,201,171,31,207,54,26,165,181,174,96,202],[18],[[0],[1,2],[0,3,2],[2,4],[2,5],[1],[6,1,3],[2,7],[1,8,6],[1,8,9],[1,9,8],[1,10],[3,10],[1,3],[6],[1,5],[1,10],[2,3,7],[1],[3,11,6],[2,3],[2,1],[100,5],[2,10,12],[2,1],[2,5],[2,1],[6,1,3]]),
([w40,w0,w1,w2,w3,w8,w30,w38],[114,203,171,207,33,174,99,143,176,95,11,37],[],[[0],[0,1],[1,2],[0,3,1],[0,1],[4],[5,2],[1,6],[1,7],[1,5],[1,8,9],[4,5],[2,5],[6,2,7],[10,3],[11],[1,5,7],[1,2,7],[2,7],[9,2],[1,2],[1,10],[10],[1,3],[1,6,2],[1,5,9],[1,2,9],[8,2]]),
([w42,w40,w0,w1,w2,w3,w30,w38],[25,5,172,95,33,100,143,114,182,173,207,37,11],[],[[0,1],[0,2,3],[4],[3,2],[5],[0,6,3],[0,2,3],[7],[1,8,9],[2,8],[1,10,9],[11],[2,10],[2,8],[8,6],[3,2],[2,6,11],[10,6],[2,10],[8,10,12],[3,8,9],[2,8,9],[3,2],[2,8],[9,8],[3,6],[3,2],[2,10]]),
([w40,w0,w1,w2,w3,w9,w30,w38],[23,175,132,5,49,47,143,99,176,165,195,205,27,96,51,202],[],[[0],[1,2],[0,1],[1,3],[1,4],[5],[6,2],[1,7],[1,6],[1,8,9],[1,8,10],[5,6],[2,6],[2,9],[2,7],[2,7],[1,2],[1,11],[12,13],[14],[1,7],[1,11],[12],[1,6,15],[1,6,2],[1,6,15],[1,6,2],[8,2]]),
([w45,w40,w0,w1,w2,w3,w30,w38],[5,25,176,95,165,47,160,99,114,182,177,51,171,96,27],[],[[0,1],[1,2,3],[4,2],[5],[6],[1,7,3],[1,2,3],[8],[0,9,2],[10,9],[0,10],[11],[2,12],[3,7,9],[2,4],[3,2],[2,7,11],[4,7,11],[2,4],[4,2],[2,9],[3,9,4],[3,13,14],[7,9,10],[2,9,10],[3,7],[3,2],[2,12]]),
([w40,w0,w1,w2,w3,w33,w38],[52,25,23,148,208,54,55,96,176,165,171,126,174,202,99,11],[10,18,73,34,0,24,7,8,27,14,50,39],[[0,1,2],[1,100,3],[1,0,2],[1,101,3],[4,1],[1,5,102,6],[0,103,7,104],[0,5,104],[0,8,105,9,104],[0,5,104],[0,1,106],[5,10,107,11],[9,7,100,8,12,108,101],[5,12,100,11],[1,10,100,13],[5,109,10],[1],[1,5,110],[5,14,101,13],[1,8,111,10,106],[1,5,15]]),
([w40,w0,w1,w2,w3,w30,w47],[58,25,23,11,27,150,176,165,26,9,205,182,99,202],[10,50,18,23,34,0,24,6,43,8,27,14],[[0,1,2],[1,3,100],[1,4,101],[1,102,5],[0],[1,3,103],[0,3,104,105],[0,4,105],[0,6,106,7,105],[0,1,107],[0,3,105,108],[3,4,109],[3,6,110,7],[1,3,100],[3,8,9,103],[4,10,111,11],[1,4,101],[1],[1,12,102,13],[3,13,102,6],[1,3,103]]),
([w0,w1,w2,w3,w9,w30,w38,w41],[47,99,143,156,21,209,106,204,2,175,154,123],[],[[0,1],[0,2],[0,3,4],[0,3,5],[0,1],[0,1],[4],[1,6],[4,1],[5,1],[2,7],[2,3,4],[6,1],[4,2],[4],[1,6],[1,3,4],[8,2,9],[10],[4,1],[7,1],[4,11,9],[7,1],[4,1,7],[9,11],[4,3],[6,1],[0]]),
([w0,w1,w2,w7,w10,w3,w30,w38],[30,4,12,31,174,140,11,96,171,106,10,5,109,207],[],[[0,1,2],[0,2,1],[0,3],[3],[0,4],[0,4],[0,4],[1,2],[1],[5],[2,4],[2,4],[2,4],[2],[6],[1,7],[1,8,9],[1,6,10],[0],[3,4],[3,4],[3,4],[11,4,12],[12,4],[10,4,6],[7,13],[7,6],[9,6]]),
([w19,w0,w1,w2,w3,w30,w38],[30,31,4,138,5,25,11,181,167,199,137,99,106,201,143,171,10],[27,16,2,3,5,6,7,28,29,61,54],[[0,1,2],[0,1,2],[0,1,3],[1,100,4],[1,101,5],[1,6,5],[0,1,102],[0,1,103],[0,7,104,8],[0,9,105,7],[0,6,106],[1,6,0,10],[1,11,100,12],[1,107,13,102],[1,6,108,102],[1,14,109,8,103],[1,15,101,13],[1,6,16],[13,8,100,9,11,110,101],[6,8,16],[6,7,16]]),
([w0,w2,w7,w3,w8,w30,w38],[34,131,210,31,33,165,99,5,87,36,170,203,145],[0,35,24,27,1,7,43,26,68,9,32,11,6,12,72,21,48],[[0,1,100,2],[3,2,4,5,6,100,101],[5,2,7,1,102,103],[7,104,2],[5,2,100,8,1,104],[5,2,9,1,105,106],[7],[0,7],[0,1,107,7],[0,8,108,10,109],[0,9],[7,0,3,110],[0,7],[11,3,110,1,111,112],[9,1,113,3,105],[3],[7,8,114,12,103],[7,9,115],[5,7,111],[5,7,9,113],[9,8,116,10,105]]),
([w0,w2,w7,w3,w30,w32,w38],[40,131,211,31,39,165,181,87,30,6,5,201,41,25,182,10,32],[0,38,24,27,7,43,14,68,9,8,18,10,39,48,11,12],[[0,1,100,2],[3,2,4,5,100,101],[5,2,100,6,1,102,103],[5,2,100,7,1,101],[6,2,8,7,101,100],[5,2,100,9,1,104,105],[9],[0,106,10],[0,7,107,11,108],[0,1,108,12,109],[0,9,11,108],[10,3,110,1,103],[11,3,13,0,14,111,1],[0,11],[11,3,13,9,1,111],[11,10,103,7,110],[12,5,106,1,103],[11,10,103,9,6,112,104],[3],[15,6,104,9,7,113,114],[5,6,16,9,1,115,104]]),
([w0,w1,w7,w3,w9,w30,w38],[5,212,31,47,165,143,49,30,131,90,36,48,175,106,96,201,11,181],[1,78,4,8,9,11,12,13,6,7,19,76,14,48],[[0,100,1],[2,1,3,4,5,100,101],[0,102,1],[6,1,7,4,8,102,100],[4,1,102,9,5,100],[4,1,10,5,102],[6],[0,11,103],[0,4,103,6,104],[0,105,4],[0,10,106],[0,11,2,107],[0],[12,2,107,13,105,108],[10,9,106,2,109],[2],[0,110,14],[0,10,111,112],[15,6,104,9,5,110,105],[10,5,16,6],[10,9,113,17,106]]),
([w0,w1,w7,w3,w30,w47],[213,150,59,11,31,30,6,2,25,131,5,41,171],[1,38,4,27,8,11,9,18,36,50,19,21],[[0,1,2,3,100],[0,3,100,4,101],[0,1,3,102,100],[0,3,100,102],[0,3,5,6,100],[2,7],[1,2,103,104],[1,2,105,104],[1,2,3,104,106],[1,4,107,108,103],[4,8,108,109,105],[2,3,9,8],[1,103,107,110],[1,3,10,111],[3,11,105,12]]),
([w0,w1,w2,w7,w3,w20,w30,w38],[5,87,31,131,165,181,30,214,171,34,38,48,106,36,96],[],[[0,1],[2,3,4],[2,1],[0,3,5],[6,1,7],[4,1],[4,3,8],[0,1],[9],[2,1],[10],[0,3],[0,1],[0],[0,11,2],[0],[2,1,12],[2,13],[0,2],[0],[2,3],[2,1],[2],[0,1,14],[0,5],[7,3],[7,1],[5,1]]),
([w0,w1,w2,w3,w20,w30,w38],[5,99,106,34,131,171,123,214,0,165,87,36,48,49,205,31,96,25,11,181],[34,8,0,24,27,38,7,43,11,12,68,9,36,72,76,6,48],[[0,1,100,2,101],[3,4,102,5],[0,4,103,6,104],[7,6,8,9,102,105],[9,2,102,10,1,105],[9,5,11,1,106,107],[0,2,101,1,3],[0,12,3,101],[13],[0,108,9],[0,11,109],[0,3,12],[0],[3,5,110,14,111],[3,6,112,11],[15],[0,10,113,16,104],[0,6,114,11,104],[17,7,1,108,115],[11,1,18,7],[2,11,5,116,19,106]]),
([w21,w0,w1,w2,w3,w30,w38],[0,31,215,2,100,5,34,25,11,99,106,143,159,165,199,171,36,216,205,181],[0,11,34,8,58,18,52,7,43,32,12,13,68,36,57,39,48],[[0,1,100],[1,2,3,4],[1,3,5],[5,1,6],[1,101,7],[1,8,7],[1,9,102,10,103],[1,11,100,12],[5,104,12,105],[13,10,100,14,9,101,106],[13,15,16,9,107,108],[1,5,103,17],[1,5,109,103],[1,101,13],[1,16,110],[1,5,111],[1,15,112,18,111],[1,12,113,16],[5,14,105,114],[5,12,115,14,105],[10,16,15,116,19,107]]),
([w0,w1,w2,w7,w3,w30,w69,w38],[181,87,165,131,171,40,31,44,148,96,106,57,217,5],[],[[0,1],[0,2],[0,1],[2,0],[0,1],[0,1],[2,3,4],[5,2],[5],[2,1,6],[2,3,6],[7],[0,1],[8],[4,9,5],[5,1,10],[11],[0,12],[6,1],[6,3],[7],[0,1],[9,1],[13,1],[4,0],[6],[0,1],[0,1]]),
([w0,w1,w2,w3,w30,w69,w38],[148,106,53,40,131,171,126,181,87,0,165,218,54,182,201,41,5,31,25,11],[45,8,0,24,27,38,79,12,14,9,50,72,11,39,48],[[0,1,2,100,101],[3,4,102,5],[0,6,102,7,4,103,104],[7,1,102,8,4,105],[7,6,9,8,102,106],[10,5,102,11,4,106],[2,1,101,3],[1,2,104],[2,3,10,101],[12],[1,0,2,13,107],[0,3,108],[3,2,14,109],[15],[3,6,110,14,109],[12,0,104,8,111,112],[0,16,4,104],[14,0,104,6,7,113,107],[17],[1,7,107,6,5,114,112],[14,7,18,6,4,19]]),
([w70,w0,w1,w2,w3,w30,w38],[0,181,165,31,219,2,220,5,40,11,25,201,166,196,164,87,202,171,221,222,182,169,223],[0,27,45,8,24,6,52,7,43,10,14,15,9,50,54,39,74],[[0,1,2,100,3],[3,4,5,6],[3,5,7],[3,101,7],[8,3],[3,9,10],[1,3,102,11,103],[1,3,12,100,11],[2,11,100,1,13,104,101],[1,14,100,15,16,105,106],[2,17,100,18,12,107,108],[3,19,103],[2,3,101],[2,3,20,109,103],[2,1,3,20,109,103],[3,110,12],[3,15,111,11,112],[3,14,113,11,111],[11,16,101,15,21,114,105],[11,12,101,14,1,115,107],[22,1,105,14,15,116,107]]),
([w71,w0,w1,w2,w7,w3,w30,w38],[30,199,87,40,53,224,11,36,165,181,131,171,44,57,96,201,31],[],[[0,1,2],[3],[4],[3],[2,1],[5],[2,6,7],[1,2],[1,8],[1,2],[8,9],[8,1],[1,10,11],[12,8],[12],[1,2],[8,10,13],[8,2,9],[13],[1,14],[12,2,13],[9,15],[1,2],[15,10,16],[9,2],[14,1],[1,9,11],[9,2]]),
([w0,w1,w2,w7,w3,w30,w34,w38],[5,87,67,165,65,181,166,171,66,36,199,25,169,31,71],[],[[0,1],[2,3],[4,1,5],[0,5],[3,1],[3,1],[3,6,7],[0,1],[2],[3,1,8],[0,3],[0,3],[0,1],[0],[0,2],[2,1,6],[2,1,6],[2,9],[0,1,10],[11,12],[13],[5,1],[0,12],[14],[0,5],[0],[5,1],[6,1]]),
([w51,w0,w1,w2,w7,w3,w30,w38],[30,90,165,5,2,201,31,67,36,11,71,181,166,171,145,72,96,169],[],[[0,1,2],[2,3],[4,1,5],[5,6],[7],[3],[8,1,9],[3,1],[5,2,10],[5,1,11],[1,11],[2,1],[2,12,13],[3,1],[10],[2,14,15],[2,3],[2,1,3],[3],[1,16,10],[5,1],[5,10],[3,14],[5,17],[5,1,11],[3,17],[1,11],[8,1,11]]),
([w0,w2,w3,w8,w30,w32,w38],[225,226,166,5,131,39,181,87,33,99,36,41,34,182],[9,0,37,24,27,45,38,7,43,13,68,11,36,72,32,21,48,12],[[0,1,100,101,2,102],[3,4,103,1,104],[3,105,1,5],[6,1,101,7,4,106],[6,1,8,7,9,106,101],[10,2,107,1,108],[2,0,3,109],[3,100,0],[2,0,100,7,110,111],[11,0,12,2,100,109],[10,112,0,107],[3,11],[3,7,113,11,104],[3,4,104,11,114],[3,10,115],[3,13,111,11],[3,13,114,11],[3,10,115],[3],[10,7,116,2,107],[10,2,117,6,107]]),
([w0,w1,w2,w8,w9,w30,w38],[5,99,227,34,143,49,33,181,131,88,36,205,48,96,41,11],[34,32,0,1,7,43,27,11,12,16,36,48],[[0,1,100,2,101],[3,4,102,2],[0,103,2],[5,2,6,7,8,102,103],[7,2,102,9,1,103],[10,1,104,2,105],[0,3],[0,5],[0,1,3,5,106],[0,107,11],[0,10,108],[0,3,12],[0],[3,109,11],[3,10,110],[0,3],[0,107,13],[0,10,108],[14,5,106,9,1,109,107],[10,1,15,5],[10,9,111,7,104]]),
([w0,w1,w2,w3,w8,w30,w33,w38],[228,87,34,144,181,197,171,53,38,57,229,145,25,54,148],[],[[0,1],[2,3],[0,4],[0,1],[4,1],[4,1],[0,5,6],[0,1],[7,1],[8],[0,5],[0,5],[4,1],[0,2],[0,1],[2,3],[9],[0,10],[7],[0,1,11],[0,1,11],[6,4],[0,12],[0,13],[12,1,14],[2],[0,1,4],[0,1,4]]),
([w46,w0,w1,w2,w3,w8,w30,w38],[33,88,181,5,203,148,230,166,231,232,145,57,38,205,144,34],[],[[0,1,2],[3,4],[5],[3,1,4],[3,4],[6],[2,1],[2,1],[1,7,4],[4,2,8],[4,1,8],[2,1],[9,7,10],[8,7],[11,1],[12],[4,8],[2,1],[1,13,7],[8,7],[4,14,15],[1,13,4],[11],[4,1],[4,2,7],[4,8],[4,1,8],[2,1]]),
([w0,w1,w2,w3,w8,w30,w47],[150,11,34,88,181,33,6,38,205,229,233,145,25],[34,32,0,24,1,27,11,12,36,16,72],[[0,1,100,101],[1,2,102],[0,1,103],[0,1,104],[1,3,104,4,102],[1,5,6,104],[0,2],[0,1,105],[0,7],[0,106,8],[0,1,107],[0,2,108],[0,2,108],[2,9,109,8],[1,2,10],[0,1],[0,3,110,11,105],[0,1,105],[0,106,12],[0,1,107],[1,4,106,3]]),
([w0,w1,w2,w3,w30,w72,w38],[5,99,203,181,166,131,130,88,234,0,36,145,66,182,2,41,11],[34,32,9,0,37,24,27,38,7,43,28,8,12,13,68,11,3,36,21,48],[[0,1,100,2,101],[3,2,102,103,4,104],[0,5,105,2,106],[3,6,103,7,1,107],[8,2,9,3,107,103],[10,1,108,11,109],[0,102,1],[0,12,101,106],[0,13,110,2,101],[0,111],[0,10,112],[0,113,7],[2,1,102,13,114,115],[8,14,4,102,116],[2,1,10,117,108],[0,7,12,2,106],[15],[0,6,118,2],[0],[10,7,119,3,108],[2,8,10,1,16]]),
([w0,w73,w1,w2,w3,w30,w38],[5,37,181,15,11,99,33,2,182,166,19,25,106,173,21,145,207,10],[2,3,6,7,26,28,29,61,27,68,54],[[0],[0,1,100],[1,101,2],[0,1,3],[1,102,2],[1,4,103],[0,5,6,1],[7,8,9,101,10],[0,1],[10,102,11],[4,10,11],[0,12,104,5,100],[0,3,100,1],[0,8,105,13,100],[0,4,106,14],[0,107,15,108],[9,5,101,8,12,109,102],[4,2,14],[0,16,110,13,108],[0,4,17],[4,2,14]]),
([w0,w1,w2,w74,w3,w30,w38],[5,106,38,143,123,88,0,181,49,174,36,145,34,48,132,165,21,172,25,11],[45,8,0,24,27,6,52,7,43,28,29,16,36,72,76,48],[[0,100,1,101],[2,3,102,4],[5,4,6,7,102,8],[0,9,103,4,104],[7,1,102,5,3,105,106],[10,3,107,11,108],[0,1,101,2],[0,1,12,2],[0,8,104,13],[0,14,109,15,101],[0,10,110,16],[0],[0,2,13],[2,111,17],[2,4,112,10],[0,2],[8,111,18],[8,4,19,10],[0,5,113,11,104],[0,4,114,10,104],[1,7,10,5,115,107]]),
([w0,w1,w2,w3,w30,w75,w38],[181,173,66,165,166,5,196,130,88,143,0,145,36,49,182,21,2,11],[45,8,9,3,24,27,0,38,7,43,10,13,15,36,21,74],[[0,1,2,100,101],[0,1,102,3,4,103],[3,1,5,6,104,105],[0,7,106,8,9,107],[3,1,10,0,107,106],[3,11,12,4,108,109],[2,3,101,13,102],[2,5,105],[1,2,14,110,101],[1,14,2,110,3,101],[1,0,2,12,110,15],[4,5,111,6],[1,13,102,14,112],[4,13,16,9,111,102],[1,0,12,113,108],[1,5,2,105],[2,1],[1,4,5,7,114],[5],[12,8,115,0,108],[1,4,12,0,17]]),
([w42,w0,w1,w2,w9,w30,w38],[47,36,34,38,48,235,175,49,50,236,143,131,181,88,132,165,21,172,173,11],[4,19,76,45,8,0,6,28,29,16,36,48,7],[[0,1,100],[1,2],[1,3,4],[5,1],[1,101,6],[1,7,102,8],[1,103,9,104],[3,10,105,9],[7,11,100,9],[12,9,100,13,10,106,101],[1,10,100,9],[1,3,104],[1,7,104],[1,14,107,15,104],[1,4,108,16],[1],[3,109,17],[1,3,110],[7,13,101,18],[1,7,19],[1,13,111,12,112]]),
([w42,w0,w1,w2,w3,w30,w33,w38],[52,181,49,34,194,126,25,54,88,165,196,145,53,182,195,106,173],[],[[0,1,2],[3],[3,4],[5],[2,6],[2,7],[2,1],[1,8],[1,9],[2,1],[1,8],[1,8],[4,10,11],[2,9],[2,8,12],[9,13],[12,9,14],[1,8],[4,8],[2,15],[16],[1,13,4],[2,8,10],[2,8,10],[2,1],[2],[1,8],[1,8]]),
([w46,w42,w0,w1,w2,w3,w30,w38],[25,49,37,88,165,132,53,173,145,181,203,2,172,237,238,196,57,106,239],[],[[0,1],[2,3,4],[4,5],[6],[1,3,7],[1],[8,3],[0,9,1],[10],[11,12,13],[14],[0,1],[0,9,1],[5,3,9],[1,4],[1,9],[4,3],[4,15,5],[1,4],[1,3,16],[4,5],[4,3,9],[3,12,13],[1,17],[1,18,7],[1,3,7],[1,9],[8,3]]),
([w42,w0,w1,w2,w3,w30,w47],[58,11,21,34,38,25,59,88,165,37,6,132,182,239,145],[4,36,19,21,45,8,0,6,27,28,70,16],[[0,1,2,100],[1,2,3],[2,4,101],[1],[2,102,5],[1,2,103],[1,6,104,105],[1,4,106],[1,2,100],[1,7,107,8],[1,9,10,103],[1,4,105],[1,2,108],[1,11,109,8,105],[1,6,105,110],[2,4,101],[4,12,111,13],[1,2],[2,7,102,14],[1,2,103],[1,14,102,7]]),
([w0,w1,w2,w3,w30,w32,w56,w38],[39,88,22,131,41,25,240,182,40,115,11],[],[[0,1,2],[0,3],[0,3],[0,1,3],[0,4],[4],[0,3],[2,3],[2,1],[2,3],[5],[5],[2,1],[1,6,7],[4,7],[4,3],[8,3,9],[1,7,5],[4,1],[4,1],[9,1],[5,6,10],[2],[10],[4,1],[0],[4,1],[5,1,10]]),
([w76,w0,w1,w2,w3,w30,w38],[39,41,22,43,2,21,25,11,96,181,241,132,99,145,172,10],[9,27,2,3,5,6,7,29,61,68,54],[[0,1,2],[0,1,3],[1,100,4],[1,101,5],[0,1,2],[1,6,7],[0,1,102],[0,8,103,9],[0,9,104,10],[0,1,105],[0,6,106],[1,100,11],[1,12,101,11],[1,6,0,7],[1,6,107],[10,13,100,14,8,108,101],[1,109,12,105],[6,7],[1,12,110,10,105],[6,7],[1,6,7,15]]),
([w0,w1,w2,w3,w9,w30,w32,w38],[48,120,96,172,190,239,175,40,242,36,25,41,49],[],[[0,1],[1,2],[1,3],[1,2],[2,4],[2,1],[2,5],[0,4],[0,4],[0,4],[0,1],[6],[0,1],[7,2],[8],[1,3],[3,7],[1,5,9],[7],[1,2],[2,9],[1,3],[1,10],[11,12],[1,3],[0],[3,4],[3,1]]),
([w0,w1,w2,w3,w30,w32,w33,w38],[53,88,96,25,181,196,145,171,40,54,41,182],[],[[0,1],[1,2],[3,4,5],[2,1],[2,1],[3,1,4],[2,5,6],[0,7],[0,1],[0,3],[3],[0,8,9],[0,1],[1,2],[3,7],[8,0,10],[3],[1,11,3],[2,1],[2,1],[5,1],[2,4,7],[0],[8],[4,1],[0,8],[3,1,4],[3,1,4]]),
([w0,w1,w2,w3,w32,w33,w38],[53,243,40,228,181,196,52,88,39,131,218,182,25,54,41,36,171,55,11],[45,47,0,24,27,38,80,7,43,68,11,12,14,16,50,39],[[0,100,1,101],[2,102,1],[3,1,102,4,5,103,104],[4,1,6,7,105,102],[4,1,8,7,9,102,106],[3,1,102,10,5,107,108],[0,2,109],[0,104,11],[12],[0,2,13,110],[0,11,111,12],[2,112,3],[2,0,14,113],[12],[2,10,114,3,109],[14,3,112,5,104],[5,3,15,7,112,104],[12,16,104,10,4,115,107],[0,2],[3,4,17,10,5,111,107],[3,4,15,10,7,18]]),
([w46,w0,w1,w2,w3,w32,w38],[39,41,25,40,1,53,36,244,11,181,232,8,132,172],[38,72,45,3,24,7,9,27,12,61,36,39],[[0,1,2,100],[1,2,3,4],[3,1,5],[1,101,6],[1,7],[1,2,8,6],[1,2,102],[2,3,103],[2,9,104,10,100],[1,2,100],[2,11,105],[1,3,106],[1,107,12],[1,2],[1,2,108],[3,13,109,10,103],[1,3,106],[2,3,110],[1,107,10],[2,9,111,12,105],[1,2,108]]),
([w0,w1,w2,w3,w30,w32,w69,w38],[53,88,131,182,145,181,201,54,96,40,41,217,36,132,245],[],[[0,1],[1,2,3],[4,2],[5,1],[5,1],[5,1],[4,2],[0,2],[0,1],[0,2],[6],[7],[0,1],[1,8],[9,0,10],[9,10],[10],[1,3,11],[4,1],[8,1],[12,1],[8,5,13],[0],[14],[4,1],[7],[5,1],[5,1]]),
([w77,w0,w1,w2,w3,w30,w38],[0,181,41,138,25,246,53,36,11,247,40,129,232,196,174,238,132,248,57,152,172],[38,27,45,8,3,37,24,7,43,12,61,16,36,72,39,48],[[0,1,2,100],[2,3,4,5],[6,2],[2,101,7],[2,4,6],[2,8,4],[1,2,102,9,103],[1,9,10,11,104,105],[12,9,100,1,13,106,101],[1,2,14,100,15],[12,16,100,17,11,107,108],[2,10,103],[2,101,16],[2,18,10,103],[2,19,109,9],[10,20,110,11,104],[2,10,111],[9,1,10,15,112,104],[2,113,12,111],[9,11,101,15,1,114,107],[2,15,115,12,111]]),
([w0,w1,w2,w3,w30,w32,w47],[59,11,40,181,36,88,39,6,132,25,239,182,249,5,41],[45,47,0,24,38,27,11,12,14,50,36,72],[[0,1,100,101],[1,2,102],[1,3,103,4,102],[1,5,104,3,102],[1,5,104,3,102],[1,6,7,104],[0,2],[0,105,8],[0,9,106],[9],[0,1,107],[2,10,108,4],[2,11,109,9,110],[2,11,109,10,110],[1,2,4],[9,4,105,5,111,106],[12,4,108,5,105],[1,4,13,3,105],[0],[1,3,14,5,106],[1,3,14,5,107]]),
([w48,w0,w1,w2,w3,w30,w32],[39,36,25,1,59,5,41,132,40,10,28,88,250,217],[7,12,39,48,45,3,24,38,0,9,27,61,68,72,14],[[0,1,2,100],[1,2,101,3],[4,1],[1,2,102,5],[1,2,103,6],[1,7,101,6],[1,2,104],[2,8,105],[1,2,106],[2,9,107,10],[2,11,107,12,108],[1,8,109],[1,9,110],[1,2],[2],[1,8,111],[2,8,112],[8,13,109,12,105],[1,2,113],[1,11,110,12,114],[1]]),
([w0,w1,w2,w3,w30,w32,w34,w38],[41,88,129,25,181,36,234,132,171,172,182],[],[[0,1],[1,2,3],[3,4,5],[0,1],[0,1],[3,1,6],[5,2,7],[0,8],[0,1],[3,5],[3],[0,7],[0,1],[1,9,2],[0,8],[0,8],[2,8],[1,10,3],[0,1],[0,1],[0],[2,4],[5],[5],[0,1],[0,5],[0,1],[2,1]]),
([w0,w1,w2,w3,w32,w34,w38],[41,251,66,88,129,36,65,99,234,39,131,132,25,67,182,40,5,11],[45,47,9,0,37,4,38,72,28,11,12,13,36,19,21],[[0,1,2,100,101],[3,1,102,103,4,104],[5,105,1],[0,1,6,3,7,106,103],[8,1,9,3,10,105,103],[5,4,105,1],[2,102,11],[2,5,107],[12],[2,11,108,109],[2,5,110],[4,3,5,111],[0,7,13,14,102,111],[4,15,14,111,102],[5,112,3,110],[0,5,2,113],[0],[5,16,114],[2,5],[5,3,110,0,114],[5,3,17,4]]),
([w51,w0,w1,w2,w3,w32,w38],[39,41,25,1,40,66,63,11,36,96,252,8,5],[38,28,68,45,3,24,7,9,27,12,61,36,39],[[0,1,2,100],[1,2,101,3],[1,102,4],[5,1],[1,6],[1,2,7,8],[1,2,103],[2,9,104,10],[2,8,105],[1,2,100],[2,8,106,11],[1,107,10],[1,8,108],[1,2],[1,2,109],[8,9,110,10,108],[1,107,10],[2,111,10,106],[1,8,108],[2,8,112,12],[1,2,109]]),
([w0,w1,w2,w3,w30,w32,w72,w38],[66,88,129,182,5,172,39,234,36,132,131,203,41],[],[[0,1],[1,2,3],[4,5],[5,1],[5,1],[6,1,7],[8,2,9],[0,10],[0,1],[0,10],[11],[],[0,1],[1,5,2],[2,3],[2,3],[2,3],[1,3,8],[4,0,12],[4,12],[12],[2,5],[0],[4],[2,1],[4],[2,1],[2,1]]),
([w78,w0,w1,w2,w3,w30,w38],[0,41,215,25,100,2,66,11,99,253,181,96,129,5,254,36,132],[38,9,34,32,3,58,14,7,43,53,28,12,81,68,11,36,19,39,48],[[0,1,100],[1,2,3,4],[1,101,5],[6,1],[1,3,6],[1,7,3],[1,8,102,9,103],[10,9,100,11,12,104,101],[13,105,9,106],[1,8,100,14],[11,15,8,107,16,108],[1,101,8],[1,8,103,13,109],[1,13,110,103],[1,15,111],[12,13,11,106,112],[1,113,8,114],[9,8,15,115,107],[1,8,116,13],[9,12,13,14,117,106],[1,14,118,15]]),
([w0,w1,w2,w79,w3,w30,w38],[53,25,44,96,181,54,148,8,40,197,165,11],[34,0,24,38,7,8,27,11,29,14,50,72,39,48],[[0,1,100],[1,2,101],[1,3,101,4,5],[1,4,102,6,101],[1,5,103],[1,7,104],[0,2,105],[0,5,8],[0,9,106,10],[0,1,107],[0,1,108],[1],[2,109,6],[1,0,2],[1,2,110],[5,109,6],[0,1,2],[1,5,11],[1,111,6,107],[1,4,112,6,104],[1,5,113,107]]),
([w0,w1,w2,w3,w80,w30,w38],[66,25,165,181,5,28,54,99,129,2,172,11,36,8],[34,3,4,0,38,26,46,32,8,11,29,13,68,36,7,21,48],[[0,1,100],[1,2,101,3],[1,3,102,2,4],[1,3,102,2,103],[1,5,104],[1,5,102],[0,2,105,6,106],[0,4,107,108],[0,7,107,2,108],[0,1,109],[0,1,110],[4,111,6],[8,6,9,10,111,101],[1,112,7,109],[1,113,3,114],[1],[1,0,4],[1,3,115,4],[0,1,4],[1,3,11,8],[1,12,116,13]]),
([w0,w1,w2,w3,w30,w81],[11,25,255,54,256,28,6,9,257],[34,0,37,4,38,8,46,32,11,3,13,14,73,74],[[0,1,100,2],[0,101,3,102],[0,103,4,101],[0,1,104,5],[0,5,6],[0,105,3,106],[0,107,105],[0,1,108],[0,1,7],[3,4,109,110,111],[1,112,108],[0,1],[1,113,4,108],[0,1],[0,1,2,8]]),
([w43,w0,w1,w2,w3,w9,w30,w38],[47,54,40,175,5,49,36,197,165,181,195,204,258,153,239],[38],[[0,100,1],[2],[2,3],[1,4],[1,5],[4],[1,6],[3,7],[1,8],[3,9,4],[3,8,10],[1,11,12],[6,7,13],[1,8],[8,7],[4,7,10],[1,11,4],[3,11,4],[1,4],[4],[3,11],[1,14,3],[1],[1,4],[3,7,4],[1,11],[3,7,10],[1,12]]),
([w43,w0,w1,w2,w3,w33,w38],[52,25,54,40,53,148,245,55,181,8,197,165,11],[38,18,73,34,0,24,7,8,27,29,14,50,39],[[0,1,100,2],[3,1],[1,2,4,3],[1,101,5],[2,6],[1,2,102,7],[1,4,103],[1,2,104],[1,8,105,5,100],[1,2,100],[1,9,106],[2,4,107],[4,10,108,11],[2,4,107],[1,4,109],[2,110,5],[1],[1,2,111],[2,101,5],[1,8,112,5,106],[1,2,12]]),
([w43,w0,w1,w2,w3,w30,w47],[58,181,11,149,54,40,150,59,6,197,165,239,61,5],[38,50,18,34,0,24,8,27,11,32,14],[[0,1,2,3,100,4],[2,3,5],[3,4,101],[3,102,6],[2],[2,1,3],[1,2,3,103,7],[1,2,4,104],[2,1,105,6,100],[1,2,3,100,4],[2,3,8,100],[2,4,106],[2,9,107,10],[2,3,108],[2,7,106,109],[4,11,110,6],[3,4,101],[2,4,12],[3,102,6],[2,6,13,1,102],[2,1,3,108]]),
([w43,w0,w1,w2,w3,w34,w38],[65,181,8,28,5,67,66,36,165,259,197,129,44,239,11],[38,10,15,74,34,3,4,0,26,46,32,8,29,13,36,7,21],[[0,1,2,100,3],[4,2,101],[2,102,5],[2,4,6],[4],[2,3,103,7],[1,2,4,104],[1,2,8,105],[2,1,106,4],[2,1,100,8,107],[2,3,106],[4,8,108,9,109],[4,6,110,111],[4,10,110,8,111],[3,4,112],[4,113,9],[11,9,12,13,102,105],[3,114,1,115],[2],[3,1,116,4],[3,1,14,11]]),
([w0,w1,w2,w3,w30,w33,w38,w44],[53,88,96,126,196,209,171,182,260,46,28,228],[],[[0,1],[1,2],[3,4],[2,1],[3,1,5],[2,4,5],[2,1],[0,6],[0,1],[0,7,5],[0,7,5],[0,1],[8],[1,2],[9,10],[10],[1,3,10],[8,3,11],[2,1],[4,1],[2,3],[2,1],[9],[4,1],[10,3,11],[4,1],[11,3],[0]]),
([w0,w1,w2,w3,w9,w15,w30,w38],[47,197,165,16,49,99,48,132,204,181,96,85,19,106,239,261,155],[],[[0,1],[0,2,3],[0,3,2],[0,4],[4],[0,5],[0,1],[1,2],[2,1],[4,1],[6,1,7],[1,7],[2,8,9],[3,10],[11],[12],[3,13],[1,14,15],[3],[16],[4,5],[4,1],[0],[4,5],[4,1],[5],[7,1],[1,7]]),
([w24,w0,w1,w2,w3,w30,w38],[47,49,16,1,51,28,11,120,167,190,195,209,262,131,123,106,20,129,153,175],[8,16,2,3,5,6,7,28,29,36,54,39,48],[[0,1,2],[1,100,3],[0,1,4],[0,1,2],[1,101,5],[1,6,5],[0,7,102,8],[0,1,103],[0,1,104],[0,9,105,10],[0,11,106,12],[1,13,100,8],[1,13,102,14],[10,8,100,9,7,107,101],[15,8,100,11,7,108,106],[1,16,0,103],[1,101,17],[1,14,109,12,103],[1,110,18,104],[1,14,111,19,104],[12,10,101,14,9,112,106]]),
([w0,w1,w2,w3,w9,w20,w30,w38],[48,197,106,34,165,239,49,47,214,99,204,5,36,216,152],[],[[0,1,2],[3,4],[4,5],[6,4],[7,4,8],[2,9],[4,1,5],[0,2,1],[0,1,2],[0,6],[6],[0,10],[0,10],[3,11],[11],[11],[3,2],[1,5,12],[3],[13],[2,9],[6,1],[0],[6,2],[6,1],[8,2],[8,1],[1,14,2]]),
([w25,w0,w1,w2,w3,w30,w38],[0,49,34,48,242,28,36,11,132,131,123,239,190,195,38,171,88,96],[0,16,45,47,24,27,6,7,43,9,28,82,29,70,36,72,76,48],[[0,1,100],[2,1],[1,2,3,4],[1,3,2],[1,101,5],[1,6,7],[3,102,8,103],[1,9,100,10],[1,9,104,10,105],[11,10,100,12,9,106,101],[6,9,107,8,108],[1,3,109],[1,3,105],[3,8,110,13,111],[3,6,112,113],[1,6,3,14],[1,15,101,11],[1,6,114],[1,16,115,17,105],[1,6,116,105],[6,8,117,13,107]]),
([w0,w1,w3,w9,w30,w33,w38],[263,264,90,197,239,49,52,195,47,143,228,53,132,48,265,152,2,54,36,28,126],[0,34,8,4,38,32,83,10,14,16,13,76,7,15,21,73,36],[[0,1,100,2,3,101,102],[2,1,100,4,103],[5,1,6,4,100,104],[4,1,100,2,104],[7,1,8,2,9,100,103],[10,1,100,4,3,103],[5,0,102,3,105],[5,0,11,3,2,102,106],[3,0,102,12,107],[3,0,13,12,102,105],[14,0,102,15,2,107],[16],[14,5,108,109],[17,5,18,15,4,108,110],[14,2,108,15,3,111,112],[14,5,19,2,15,109,113],[17,5,18,2,4,110],[10,5,19,20,3,114,112],[5],[10,3,109,15,2,115,112],[10,3,18,4,2,116,112]]),
([w0,w1,w2,w3,w9,w30,w34,w38],[36,197,132,67,165,239,65,49,190,209,99,71,195],[],[[0,1,2],[3,4],[0,5],[6,4,7],[4,8],[4,5],[0,1,2],[0,4,1],[2,1],[0,1,2],[0,2,1],[0,1,4],[4,9],[0,3],[0],[3,5],[3,5],[0,5],[3],[0,10],[11],[2,1],[7,3,10],[3,11],[0,1,2],[0],[0,2,1],[0,1,12]]),
([w0,w1,w2,w9,w30,w34,w38],[36,266,88,197,67,143,49,65,239,195,47,66,132,48,265,209,28,130,156,50,123],[0,34,8,38,7,43,84,10,13,14,36,18,21,74,19],[[0,1,100,2,3,101,102],[2,1,4,5,100],[6,1,7,8,100,103],[8,1,100,2,5,103],[9,1,10,2,103,100],[0,1,100,8,3,104,105],[3,0,4,102],[6,0,11,3,2,102,106],[3,0,102,12,107],[9,0,13,3,107,102],[14,5,102,15,2,107],[0],[4,8,108],[4,5,108,109],[0,2,4,8,110,108],[14,6,16,2,4,111,5],[4,14],[0,6,16,17,3,112,104],[0],[0,3,104,18,2,113,114],[0,9,19,20,2,112,104]]),
([w50,w0,w1,w2,w9,w30,w38],[47,49,36,2,64,67,50,197,267,108,265,88,204,132,5,21],[4,32,61,76,34,0,6,52,8,28,29,16,36,21,48],[[0,1,100],[1,2,101],[1,2,102,3],[1,4],[5,1],[1,2,103,6],[2,7,104,8,101],[1,9,105,8],[1,100,8],[10,8,100,11,12,106,107],[2,7,100,8],[1,2,108],[1,2,101],[2,13,109,7,101],[2,14,110,15],[1,2],[1,111,9],[1,2,112],[1,11,111,10],[1,2,113],[2,11,114,7,113]]),
([w51,w0,w1,w2,w3,w9,w30,w38],[47,190,265,2,67,64,36,197,132,143,165,239,209,71,49],[],[[0,1,2],[2,1],[2,3],[4],[2,4],[5],[6,1,7],[6,7,8],[1,9,10],[1,11],[1,10],[2,1],[2,7,8],[1,10],[1,7],[1,7],[2,1],[2,12],[6,9],[6],[2,13],[1,11,2],[13],[2,9,6],[1,7],[2,9,14],[1,7],[6,1,7]]),
([w0,w1,w2,w3,w9,w30,w82,w38],[132,197,67,143,165,239,49,190,47,209,152,228,261,71,36,195],[],[[0,1],[2,3,4],[4,5],[6,4],[4,3,7],[8,4,9],[0,1],[0,4],[0,1],[0,1],[1,0],[9,0],[3,9,4],[2,10],[11],[2,10],[],[0,5,12],[2],[6,2,3],[13],[0,1],[6,3],[13],[0,1],[6],[1,0],[14,0,15]]),
([w0,w1,w2,w3,w30,w82,w38],[228,132,88,197,67,143,171,153,239,106,209,0,96,36,54,152,49,195,11],[0,34,8,4,38,79,32,10,49,61,14,68,13,3,36,16,76,7,73],[[0,1,100,2,3,101,102],[2,4,5,100,6],[0,7,100,8,103],[8,9,100,2,5,104],[10,7,11,2,100,105],[0,1,100,8,3,103],[1,0,4,6,102],[1,12,102,3,2,106],[3,0,102,1,107],[10,0,13,1,102,108],[9,5,102,10,2,107],[0,2,4,5,109,110],[4,6,111,7,112],[4,113],[0,1,4,8,114,112],[7,0,110,2,4,115,5],[14],[12,1,110,15,3,116,117],[16],[0,3,115,15,1,118,117],[0,17,13,18,1]]),
([w83,w0,w1,w2,w3,w30,w38],[0,49,36,162,268,2,67,11,223,132,88,197,108,171,153,195,204,209,96,265,269,69,239,270],[0,8,34,4,6,52,32,28,29,7,61,14,15,13,36,18,76,48],[[0,1,100],[1,101,2],[1,3,2,4],[1,2,5],[6,1],[1,7,2],[8,9,100,10,11,102,101],[1,12,100,13],[1,103,14],[15,100,10,16,104,105],[8,9,100,17,11,103],[1,13,101,8],[1,10,106,18],[11,8,101,9,16,107,104],[19,20,101,17,10,108,109],[1,21,110,111],[1,13,112,12,113],[1,22,114,8,112],[1,10,115,14,111],[1,23,116,18,111],[8,11,104,9,117,109]]),
([w84,w0,w1,w2,w3,w9,w30,w38],[47,190,195,67,64,132,197,96,239,152,265,71,232,143,49],[],[[0,1,2],[2,1],[],[3],[3],[4],[2,1],[5,6],[1,7],[1,8],[1,7],[2,1],[5,6],[1,9],[1,6],[1,6],[2,1],[10,9],[11,7],[12],[8,9,11],[1,8,10],[11],[7,13,14],[1,6],[10,9,14],[1,6],[2,1]]),
([w0,w1,w2,w3,w9,w30,w38,w85],[36,197,106,75,96,239,49,143,47,271,272,209,273,152],[],[[0,1,2],[3,4],[0,5],[6,4],[2,7],[0,1,5],[8,4,9],[0,2,1],[2,1],[0,1,6],[0,10],[2,11],[0,1],[0,3],[0],[3,2],[0,5],[0],[3],[0,7],[4,1,6],[12],[6,2],[0,6],[0],[0,13],[9,2],[6]]),
([w0,w1,w2,w3,w9,w30,w38,w54],[36,258,152,239,47,96,79,156,209,132,265,11,81],[],[[0,1],[1,2],[0,3],[1,2],[3,1],[0,2],[4,1,5],[0,2,6],[5,7,8],[0,2,8],[0,9,8],[10,1,2],[0,2,10],[0,3],[0],[3,2,6],[0,3],[6,3,10],[6],[0,7],[1,2,5],[0,2,5],[10,2],[0,11],[10,11],[0,2],[0],[12]]),
([w55,w0,w1,w2,w3,w9,w30,w38],[47,239,36,209,2,265,49,79,197,153,96,274,152,81,156,11],[38],[[0,100,1],[2,3],[1,4],[2,5],[5,6],[2],[7],[1,8,9],[3,10],[2,1],[3,1],[1,11],[2,1],[1,12,3],[3,8],[2,8,3],[2,11,3],[5,3],[2,1],[2],[1,12,13],[2,1],[13],[2,14],[5,8,12],[5,12],[2,8,15],[2,12]]),
([w0,w86,w1,w2,w3,w30,w38],[36,51,16,181,197,132,19,47,28,11,5,21,171,180],[34,3,6,7,32,26,28,29,61,68,50,54,5,39,48],[[0],[0,1,100],[1,2,101],[0,1,2],[1,102,3],[0,1,103],[0,4,104,5,6],[1,2,6,7],[0,1],[6,102,8],[0,3,9,5],[0,2,105],[0,6,104],[0,5,106,4,104],[0,10,107,11],[0,2,108],[2,12,109,13,101],[0,2,110],[0,111,13,112],[0,6,113,112],[0,5,114,3,103]]),
([w0,w1,w2,w3,w30,w87,w38],[36,197,180,67,129,275,19,190,99,209,0,21,171,5,11],[34,8,3,37,4,38,0,32,10,14,15,50,76,74,7],[[0,1,100,2,101],[3,4,102,2,103],[0,104,2],[5,6,104,7,8,105],[9,2,10,7,104,106],[0,1,104,2],[0,3,101],[0,11,107],[0,7,108,1,101],[0,1,107,9,101],[0,11,108],[0,3,109],[2,3,12,110,102],[2,12,3,110,4,102],[0,3,111],[0,3,2,109],[0,3,2],[0,13,112,109],[0],[0,7,113,1,114],[0,1,14,4]]),
([w45,w0,w1,w2,w30,w34,w38],[65,209,36,21,67,28,54,5,197,276,129,190,99,51,171],[4,32,13,21,34,3,37,38,0,26,10,8,85,14,50,74,7],[[0,1,2,100],[2,3,101],[4,2,102],[2,4,5],[6],[2,5,103,7],[2,8,104,9,101],[1,4,10,105,9,106],[1,9,100,11,12,107],[1,9,13,11,100,108],[2,8,100,9],[1,2,4,109],[1,2,11,110,101],[1,2,8,101,111],[2,3,110],[4,14,112,10,105],[4,14,113,10],[2,4,114],[2],[2,11,115,6,103],[2,8,103,10,116]]),
([w0,w1,w2,w3,w30,w33,w59,w38],[52,197,96,23,196,54,171,152,190,53,161,106,277,8,182,25,88,163],[],[[0,1],[0,2,3],[0,4],[0,3,2],[0,5],[5],[0,1],[1,6,7],[2,1,4],[1,8],[1,7],[9,1,10],[11,4,7],[3,2],[3,7],[12],[13],[1,14,15],[2,16],[4,2],[10,2],[2,1,6],[3],[17],[1,6],[0],[1,6],[10,1]]),
([w88,w0,w1,w2,w3,w30,w38],[52,54,23,5,56,11,28,181,209,278,171,126,197,196,204,25,143,27],[8,14,34,35,3,24,25,6,7,27,28,29,50,54,39,73],[[0,1,2],[1,100,3],[0,1,4],[1,101,3],[0,1,2],[1,5,6],[0,102,7,103],[0,1,104],[0,7,105,8,106],[0,1,107],[0,8,108,9],[1,10,100,11],[8,11,100,12,13,109,101],[1,14,110,11,107],[9,7,15,10,111,108],[1,16,101,10],[1,15,0,17],[1,11,112,9,15],[1,16,113,14,107],[9,10,15,7,114,108],[1,11,115,15,107]]),
([w0,w1,w2,w3,w30,w33,w69,w38],[96,88,190,196,181,171,152,54,40,279,41,182,280,222],[],[[0,1],[1,0],[2,3,4],[0,1],[4,0],[4,0],[0,3,5],[2,5,6],[0,1],[7,2],[7,2],[7],[4,1],[1,0],[8,6],[9],[10],[1,11,12],[0,1],[3,0],[0],[0,4,2],[8],[13],[3,1],[10],[3,1],[4,1]]),
([w36,w0,w1,w2,w3,w30,w38],[0,209,54,40,28,5,11,148,142,53,197,131,181,126,281,44,228],[0,14,34,32,24,38,7,43,9,53,11,29,50,72,39,48],[[0,1,2,100],[3,2],[2,3,4],[2,101,5],[2,4,3],[2,6,4],[7,8,9,10,102,103],[1,2,11,100,8],[1,8,100,12,11,104,101],[1,2,11,105,13],[14,8,100,1,10,106,107],[1,2,9,108],[1,9,10,103,109],[1,2,9,110],[9,1,111,14,103],[2,101,7],[2,15,9,108],[2,13,112,14,108],[2,113,7,110],[14,7,101,13,10,114,106],[2,13,115,16,110]]),
([w0,w1,w2,w3,w30,w33,w34,w38],[181,197,8,165,190,209,67,171,182,28,88,5,54,69,195],[],[[0,1,2],[0,3],[2,0,3],[0,4],[0,3],[2,0,3],[2,1],[1,3],[3,1],[1,4],[1,3],[3,1],[0,5,3],[6,7],[2,6],[2],[6,7],[0,8,9],[2,10],[11,6,12],[2],[4,0],[6],[13],[0,4],[6,11],[0,4],[9,0,14]]),
([w0,w1,w2,w3,w33,w34,w38],[148,282,88,197,67,181,65,143,209,52,28,171,283,5,190,53,182,54,270,36,130,195,55,126],[0,34,8,4,32,29,7,85,68,16,50,15,19,21,74],[[0,1,100,2,3,101,102],[2,1,4,100],[0,1,100,5,103],[5,1,6,2,7,100,103],[8,1,9,2,103,100],[10,1,100,8,3,103],[3,0,4,11,102],[8,12,102,3,2,104],[3,0,13,14,102,104],[8,0,15,3,104,102],[10,0,102,8,2,105,106],[0,2,4,107],[10],[4,11,108,109],[4,16,110,10,111],[17,0,13,2,4,7,112],[10],[10,0,106,18,3,113],[4,0],[10,3,19,20,2,114,106],[10,21,22,23,2,113,106]]),
([w50,w0,w1,w2,w3,w30,w33,w38],[52,181,148,53,197,195,2,64,67,182,165,190,171,69,28,88,54],[],[[0,1,2],[3,4,5],[2,6],[7],[8],[2,8],[2,1],[1,4,9],[1,10],[2,1],[1,11],[1,10],[10,4,12],[2,10,4],[5,4],[2,9,4],[2,9,4],[1,9,10],[2,13],[13,14],[14],[1,9,14],[2,15,14],[2,15,16],[2,1],[13],[1,11],[1,11]]),
([w51,w0,w1,w2,w3,w33,w38],[52,28,8,148,71,67,64,55,90,181,54,182,284,197,196,143],[38,10,68,73,34,0,24,7,8,27,53,14,50,39,74],[[0,1,2,100],[1,101,3],[1,4,102],[5,1],[6,1],[1,2,103,7],[2,8,104,3,100],[2,4,105],[2,9,106,3,100],[2,8,100,9,10],[1,2,107],[4,8,108,3],[11,12,101,13,14,109,110],[10,101,3],[1,8,101,3],[3,4,111],[1],[1,4,112],[10,15,111,3],[1,9,113,3,107],[1,8,114,9,10]]),
([w0,w1,w2,w3,w30,w33,w82,w38],[182,197,165,67,181,88,52,195,171,152,265,280,54,69],[],[[0,1],[0,2,3],[2,4],[2,5],[4,2],[6,2,7],[2,1,8],[1,2],[0,1],[1,0],[1,0],[7,0],[2,0],[0,9,3],[3,9],[10],[],[1,0,11],[12,3,5],[12,5],[12],[7,1],[3],[13],[1,5],[13],[1,5],[7,1]]),
([w89,w0,w1,w2,w3,w30,w33,w38],[52,181,148,195,197,64,67,182,152,88,171,69,231,228,54],[],[[0,1,2],[3,4],[],[5],[6],[6],[2,1],[1,4,7],[1,8],[2,1],[1,9],[1,8],[10,4],[2,8,3],[3,4],[2,7,3],[2,7,3],[1,7,9],[2,8,9],[11,8],[12],[1,7,13],[2,9,14],[2,8,14],[2,1],[11],[1,8,9],[1,9]]),
([w90,w0,w1,w2,w3,w30,w38],[0,54,5,28,67,11,148,182,90,197,143,285,181,196,106,286,209,71,156],[0,8,34,24,27,38,7,43,53,10,13,81,68,36,19,16,39,73],[[0,1,100],[1,101,2],[1,2,3],[4,1],[1,2,4],[1,5,3],[6,7,100,8,9,102,101],[1,10,100,7],[6,11,100,12,13,103,104],[1,10,105,14],[15,11,100,16,9,106,107],[1,8,101,6],[7,101,9,13,104,108],[1,109,6],[14,6,101,7,8,109],[1,10,110,6,111],[1,17,112,110],[1,7,113,15,110],[1,10,114,6,115],[15,6,104,9,116,106],[1,18,117,14,114]]),
([w0,w1,w2,w3,w30,w33,w38,w52],[182,197,152,75,209,181,270,28,52,228,106,11,148],[],[[0,1],[0,2,3],[4,5],[4,6],[4,2],[7,1,2],[8,2,9],[1,2],[0,1],[1,0],[1,0],[5,0,7],[10,0],[0,2,3],[3,2],[7],[1,0,7],[3,0,9],[7,6],[9,2],[7,2],[7],[3],[1,2,9],[7,2,9],[1,11,7],[9,11],[12]]),
([w53,w0,w1,w2,w3,w30,w33,w38],[52,148,182,2,287,28,54,75,90,152,77,288,270,106,11],[32],[[0,1],[2,100],[1,3],[4],[1,5],[1,6],[7],[1,8],[2,9,10],[1,11],[5,8],[11,8],[5,9],[1,8],[2,11],[1,2,5],[1,2,11],[1,2,5],[1,9,10],[5,2],[5],[5,2],[1,12,5],[1,9],[1,9,5],[10],[13,8,9],[5,8,14]]),
([w0,w1,w2,w3,w30,w33,w38,w91],[182,90,96,79,288,52,106,53,289,28,270,126,290,81],[],[[0,1,2],[0,2,3],[1,4],[2,1],[4,1],[2,4],[5,1],[3,1,6],[0,4],[4,0],[4,0],[6,0],[7,0,8],[0,2,3],[3,6],[9],[3,0,9],[9],[2,10],[8,2],[1,10,2],[8,2],[3],[6,1,11],[12],[9,11],[9],[13]]),
([w0,w1,w92,w2,w3,w30,w38],[231,57,8,90,181,41,40,28,190,53,11,239],[45,38,3,24,7,9,27,12,61,68,36,72,11,39,48],[[0,1,2,100],[2,3,101,4,5],[2,6,102],[0,2,4,103,101],[2,5,101],[2,7,104],[2],[1,6,105],[1,106,8],[1,2,6],[1,7,107],[0,6,3,9,1],[0,5,106],[1,2],[5,7,10],[0,6,11,108,102],[2,6,109],[6,7,110],[2,111,0,112],[7,4,113,0,104],[2,7,114,112]]),
([w0,w1,w2,w3,w93,w30,w38],[231,106,8,88,67,181,209,28,166,41,197,5,239,11],[34,0,4,38,26,3,8,32,10,13,16,36,21,7,73],[[0,1,2,3,100,101],[2,4,101],[0,2,5,102,101],[2,3,102,6,101],[2,7,103],[2,6,102,7],[4,8,104,0,105],[1,9,106,10,3,107],[1,0,11,10,107,106],[2,108,0],[1,0,7,3,108],[0,3,4,12,109,105],[0,12,4,109,8,105],[2,1,110,4],[4,7,111],[2],[2,4,0,110],[7,5,112,0,113],[2,4,0],[7,3,13,8],[1,2,7,114,110]]),
([w46,w0,w1,w2,w3,w34,w38],[65,28,8,5,67,49,36,88,231,181,209,166,291,197,57,239],[38,10,15,74,34,3,4,0,26,32,8,13,36,21,7],[[0,1,2,100],[1,101,3],[4,1,102],[1,4,3],[5],[1,2,103,6],[2,7,104,8,100],[2,4,105],[2,9,106,5,100],[2,7,100,10,107],[1,2,106],[4,11,108,8,105],[5,12,101,13,7,109],[10,8,14,13,101,110],[1,7,101,8],[4,15,111,8,105],[4,15,111,11,105],[1,4,112],[1],[1,9,113,5,114],[1,7,113,11,114]]),
([w0,w1,w2,w3,w30,w34,w38,w47],[239,292,182,165,67,130,65,199,28,150,293],[],[[0,1,2],[2,3,4],[3,0],[0,1,5],[3,0],[3,0],[6,0,7],[0,3,1],[2,1],[3,2],[3,1],[1,2],[1,2],[2,0],[0,2],[4,0],[4,8],[8],[8,7],[8],[7,5],[7,5],[9],[1,5],[1,5],[8,5],[10,5],[4]]),
([w94,w0,w1,w2,w3,w30,w38],[0,239,11,209,293,154,28,160,36,9,199,6,182,286],[0,8,16,34,24,6,27,28,13,54],[[0,1,2,3,100,4],[2,3,101,4],[4,5,6,7],[2],[4,102,6],[2,4,6],[1,2,8,103,9],[2,4,100],[2,1,104,3,8],[1,2,10,105],[2,4,11],[2,4,101],[2,8,106],[2,12,107,3,101],[2,4,9],[4,1,108,8],[1,4,12,102],[2,4,8],[8,10,109,13,106],[2,4],[2,4]]),
([w95,w0,w1,w2,w3,w30,w38],[0,11,239,88,293,162,28,5,6,9,209,288,182,141,223],[0,8,14,34,24,6,27,28,15,54],[[0,1,2,100,3,4],[1,4,101],[4,5,6],[4,102,7],[1],[1,3,6],[1,8,103,9],[1,4,100],[1,2,104,10,100],[1,3,105,2],[1,4,8],[1,4,101],[1,11,106,10],[1,6,107],[1,4,9],[4,2,102,12],[2,4,6,108],[1,3,6],[6,13,109,14,105],[1,4],[1,4]]),
([w0,w1,w2,w49,w3,w30,w47],[150,197,294,149,64,58,28,239,271,11,49,182,289,69,71,293,295],[34,0,24,6,52,38,8,27,53,28,32,14,16,54],[[0,1,100,2,3],[3,4,101],[0,3,5],[0,3,102],[3,6,103,104],[3,7,101,8,105],[0,4,106],[0,3,9],[0,10,107,108],[0,3,109],[0,11,106,12,110],[0,4],[0,4,111],[3,4,112],[6],[0,13],[3,14],[0,9,15],[3,0,113],[0,16,111,12,107],[3,16,112,8,103]]),
([w0,w1,w2,w3,w30,w34,w47],[150,296,88,197,67,239,99,209,58,199,65,182,11,141,5,28,130,8,293,166],[0,34,8,4,38,32,10,36,50,54,18,19,21,74,7],[[0,1,100,2,3,101,102],[2,1,4,100],[0,1,100,5,103],[5,1,100,2,6,104],[7,1,8,2,103,100],[9,1,10,5,3,100,104],[3,0,4,102],[7,9,102,3,2,105],[3,0,102,11,106],[7,0,12,3,105,102],[13,0,14,7,2,102,105],[0,2,4,5,107,108],[4,11,108,5,107],[4,5,107],[15],[15,0,109,2,110,6,111],[15],[9,0,14,16,3,112],[0],[13,3,17,16,2,113,111],[18,19,114,12,2,112]]),
([w50,w0,w1,w2,w3,w30,w47],[58,150,11,49,64,67,293,197,297,28,88,204,199,68,239,182,189,271,8],[4,32,36,21,34,0,6,52,8,28,16,18,57],[[0,1,100],[1,2,101,3],[1,3,102],[1,4],[5,1],[1,2,6,103],[1,7,104,8,101],[3,105,8],[1,100,8],[9,8,100,10,11,106,107],[12,8,13,14,7,100,103],[1,3,108],[1,3,101],[1,15,109,7,101],[1,15,108,101],[1,3,102],[3,15,110,9],[9],[1,10,111,9,112],[1,16,103,12],[17,7,18,16,10,110,106]]),
([w51,w0,w1,w2,w3,w30,w47],[58,28,149,11,71,67,64,293,258,150,239,182,254,197,196,141,5,289],[38,10,50,23,34,0,24,8,27,53,14,19,57],[[0,1,2,100],[1,101,3],[1,4,102],[5,1],[1,6],[1,3,7,103],[2,8,104,9,100],[2,4,105],[2,10,106,8,100],[1,2,100],[2,10,105,100],[4,107,9],[11,12,101,13,14,108,109],[1,101,9],[15,9,16,11,8,101,103],[4,10,110,9],[1,4,102],[1],[1,15,111,9,112],[17,8,16,12,13,110,108],[1,12,103,15]]),
([w0,w1,w2,w96,w3,w30,w47],[150,11,9,293,199,239,6,49,182,209,3,2,233,28,273,289],[34,0,4,6,8,86,28,36,16,56],[[0,1,100,2],[1,3,101],[0,1,102],[0,1,102],[1,4,103,5],[1,3,6],[0,3,104],[0,1,105,3],[0,1,105,7],[0,8,106,9,104],[0,1,2,3],[0,3,10,11],[0,3,107],[3,8,108,5],[1,3,12],[0,1],[0,109,13],[1,0,14],[0,4,109,15],[1,0,3],[1,3]]),
([w94,w0,w1,w2,w3,w30,w47],[58,293,11,2,3,28,5,6,9,239,150,199,197,182,298,289,141],[0,8,16,34,24,6,27,28,36,50,54],[[0,1,2,100],[1,2,101],[1,3,4],[2],[1,102,5],[1,6],[2,7,103,8],[1,2,100],[2,9,104,10,100],[2,11,105,9],[1,2,7],[1,2,101],[2,12,106,13],[2,13,107,12,101],[1,2,8],[1,9,108,10,109],[1,13,102,9],[1,14],[15,10,102,11,16,110,106],[1,2],[1,2]]),
([w0,w1,w2,w3,w97,w30,w47],[239,299,6,197,9,300,209,28,293,182,3,150,141,271,290],[34,0,24,87,8,27,10,14,50,55],[[0,1,2,3,100,4],[4,5,101],[4,0,102,6,101],[0,1,4,7,103],[0,1,4,7,103],[2,1,8],[2,5,104],[2,3,105,6],[2,7,106],[2,7,106],[2,8,4],[5,0,107,9],[0,5,7,10],[0,5,7,108],[2,5,7],[7,109,11],[7,12,109,13],[2,8],[2],[2,7,14],[2,7,8]]),
([w95,w0,w1,w2,w3,w30,w47],[58,293,9,6,2,3,150,300,239,209,199,141,182,28,271],[0,8,14,34,24,6,27,28,50,36,54],[[0,1,2,100],[1,3,101],[1,4,5],[1,102,6],[2],[1,7],[2,3,103],[1,2,100],[2,8,104,9,100],[2,10,105,8],[1,2,3],[1,3,101],[3,11,106,9],[3,12,107,9,101],[1,2],[1,8,102,12],[1,12,108,8,109],[1,13],[13,14,102,10,11,110,105],[1,2],[1,2]]),
([w48,w0,w1,w2,w3,w30,w34],[65,28,197,88,5,67,128,8,166,233,301,36,25,209,21,280,302],[7,29,36,21,74,34,3,4,38,0,26,32,10,8,13,15],[[0,1,2,100],[1,3,101,4],[5,1,102],[1,2,103,4],[1,6,104,7],[1,2,103,8,100],[9,10,11,2,105,12],[3,5,12,106],[9,10,11,12,107],[1,12,108],[12,3,107,13,109],[2,5,11,110],[11,14,111],[1,11,112],[11,2,111,13,113],[5,11,114],[1,5,115],[5,15,114,16,106],[1,9,11],[1],[9]]),
([w1,w2,w3,w98,w30,w38],[5,49,21,8,54,2,0,28,6],[8,46,27,53,34,28,29,14,0,16,6,36,7,54,39,48],[[0,100,1,101],[0,2,102,103],[0,3,104],[0,3,105],[0,2,106],[0,107,4,102],[1,3,108,5],[1,3,109,110],[1,2,111,112],[0,3,6],[0,3,113],[0,2,114,7],[3,7,6],[2,3,8],[2,3,115]]),
([w0,w2,w3,w99,w30,w38],[8,49,5,28,54,2,21,33,215,39,9],[0,37,24,34,6,52,7,14,27,8,16,36,54,39,48],[[0,100,1,101],[0,2,102],[0,2,103],[0,3,104,105],[0,3,106],[1,2,107,4,108],[1,2,109,5],[0,110,1,104],[1,3,111,106],[1,2,6,7,8],[0,2,112],[1,2,3,113],[0,2,9],[2,3,10],[0,3,114,6]]),
([w0,w1,w2,w3,w100,w30,w38],[5,8,64,49,28,9,21],[34,0,24,6,52,7,8,27,53,28,29,14,16,54,39,48],[[0,1,100],[1,2,101],[0,1,102],[1,3,101],[1,4,103,104],[1,4,105],[0,2,106],[0,3,107,108],[0,3,106],[0,1,109],[0,4,110],[0,2,111],[0],[1,2,112],[2,4],[0,2],[0,1,113],[0,4,114],[1,2],[3,4,5],[1,4,115,6]]),
([w0,w1,w3,w100,w30,w38],[5,8,49,28,21,64,9],[34,24,0,37,6,52,7,27,53,8,46,28,29,14,54,39,16,48],[[0,1,100],[0,1,101],[1,102,2,103],[1,3,104,105],[1,3,106],[0,4,107,108],[0,109,2,110],[0,1,111],[0,3,112],[0,113,5],[0,1,114],[0,3,115],[1,116,2,5],[2,3,6],[1,3,117,4]]),
([w0,w1,w2,w3,w30,w101],[5,9,49,28,6,54,21],[34,0,37,24,6,8,46,27,28,14,16,54],[[0,1,100],[1,101,2,102],[0,1,103],[1,3,104],[1,3,4],[0,105,2,106],[0,4,107],[0,3,108],[0,1,3],[0,109,5,107],[2,3,110,104],[1,2,3],[0,3,111],[0,1,3],[1,3,6]]),
([w0,w1,w2,w3,w30,w34,w61,w38],[65,197,166,239,258,209,182,185,141,25,88,303,19],[],[[0,1],[0,2],[0,3,4],[0,4,3],[0],[5],[0,1],[1,2,3],[6,1],[1,6],[7,1],[7,1],[8,2,6],[2,3],[2,6],[2,3],[7,2],[1,3,9],[9,10],[9],[9],[2,1],[11],[12],[1,4],[0],[2,1],[7,1]]),
([w37,w0,w1,w2,w3,w30,w34,w38],[239,5,182,209,67,166,65,28,171,197,99,165,143,25,207,304],[],[[0],[1,2,3],[4,2,5],[1,6,7],[6,1],[6],[5,8],[2,9],[2,5],[3,6],[3,10,6],[3,6],[6,3,5],[3,5,11],[2,9],[3,2],[3,2],[11,2],[2,12],[5,2],[5,2],[9,2,13],[13,14],[13],[5,9],[15],[5,8],[5,8]]),
([w37,w0,w1,w2,w3,w30,w38],[65,5,197,182,2,166,70,305,304,21,25,171,9,95,165,209,130,207,204,196,143,8],[38,32,8,13,3,2,5,6,7,28,29,15,36,39,74],[[0,100],[1,2,3,101,102],[4,5,3,103,104],[0,6,7],[0,1,8],[7,2,9,10,11,12],[0,105,13],[0,14,104,15],[0,106,8],[0,10,107],[0,10,108],[2,13,101,14,5,102],[3,16,102,2,17,101],[2,10,18,109,13,107],[7,10,5,110,13,108],[3,19,104,20,103],[5,10,111,18],[7,2,10,112,108],[7,8,10,0,107],[7,5,10,2,113,108],[8,2,21,10,114,107]]),
([w0,w1,w2,w3,w30,w34,w72,w38],[182,197,166,5,239,143,88,234,171,209,36,306,41],[],[[0,1],[0,2],[3,4],[4,5,6],[7,4],[7,4],[8,1],[1,2,3],[0,1],[1,0],[3],[9],[3,0,2],[0,4],[2,0],[2,0],[7,0],[1,0,10],[3,5],[11],[12],[2,1],[3],[3],[1,6],[3],[2,1],[7,1]]),
([w102,w0,w1,w2,w3,w30,w34,w38],[65,239,209,182,166,5,28,143,88,171,199,36,307],[],[[0,1,2],[3],[4,1],[5,6],[5],[5],[4,7],[1,8],[2,4,9],[2,1],[1,7,8],[2,1],[9,1,4],[1,4],[2,8,10],[2,5],[2,5],[5,2,4],[4,1],[1,9],[4,1],[8,1,11],[5,7],[12],[4,7],[5],[4,8],[4,7]]),
([w102,w0,w1,w2,w3,w30,w38],[0,88,239,5,2,166,199,28,36,143,9,173,165,196,130,171,209,66,204],[38,0,32,13,3,1,24,27,7,43,26,46,11,29,8,68,36,21,48],[[0,1,2,100,101],[3,102],[4,5,2,103,104],[3,6,7,1],[3],[7,1,8,9,10],[2,3,105,11],[1,11,100,12,5,101],[3,13,106,11,107],[2,14,101,1,9,100],[6,8,5,108,15,109],[3,12,110,16,111],[3,17,107],[3,112,11],[3,8,113,114],[3,103,1],[2,18,103,15,115,112],[8,116,1,108],[3,1,17,11,107],[3,8,117],[8,1,118,5,108]]),
([w0,w1,w2,w3,w30,w34,w82,w38],[239,88,143,171,209,199,182,67,166,280,265,54,148,49,197,195],[54],[[0,1],[1,2,3],[4,0],[0,1],[4,0],[4,0],[3,0,2],[0,3],[4,1,5],[2,6,4],[4,6],[4,6],[2,1],[1,0,3],[0,3],[7],[8],[1,0,9],[100,1,2],[10],[11],[3,2],[12],[13],[14,1],[7],[15,1],[15,1]]),
([w103,w0,w1,w2,w3,w30,w34,w38],[65,88,209,197,143,5,28,2,166,199,165,181,190,67,302,141,275,231],[54],[[0,1,2],[2,3],[4],[5,1,6],[6,5],[7],[6,1,8],[9,1],[1,8,10],[2,11],[2,1],[2,1],[9,2],[2,8,10],[2,1,3],[2,12],[2,3],[10,1,2],[1,8],[8,13],[8,13],[1,14],[100,1,15],[16],[8,3],[17],[3,1],[8,1]]),
([w103,w0,w1,w2,w3,w30,w38],[0,209,199,5,197,67,28,275,231,166,9,141,88,177,181,99,180,190,152],[38,0,32,8,13,34,4,10,14,16,3,76,7,73],[[0,1,2,100,101],[3,1,4,102,103],[5,104],[3,5,6,7],[5,3,8],[6,9,10,4],[2,11,100,12,4,105,102],[1,5,9,101,13],[1,13,100,14,106],[1,11,101,2,15,100],[2,16,100,1,4,106],[1,5,9,103,8],[1,2,103,4,12,102],[1,8,102,17,107],[7,8,102,1,9,107],[5,108,8],[5,109,7],[5,7,110],[7,8,108,2,5,109,11],[2,8,108,18,4,111,112],[11,4,109,18,12,113,112]]),
([w0,w1,w2,w3,w30,w34,w38,w104],[199,88,143,25,181,209,165,190,171,302,308,256,36,166],[],[[0,1],[0,2,3],[3,4,5],[4,0],[3,0,5],[0,2,5],[3,0,6],[2,6,5],[0,1],[2,7,3],[5,7],[2,1],[6,5],[0,2,8],[3,8],[9,2],[1,10,3],[9,2],[3,0],[3],[0,2,7],[3],[11],[4,1],[12],[3,10],[3],[13]]),
([w105,w0,w1,w2,w3,w30,w34,w38],[65,199,209,141,166,280,5,28,88,292,308,239,182,309],[],[[0,1,2],[2,3],[4,5],[6,1,7],[7,3,6],[7],[8],[1,9,3],[1,4,10],[2,11],[2,1],[2,1],[1,2],[2,4,5],[1,3,2],[2,12],[2,3],[3,2],[1,11,4],[3,5,4],[4,5],[5,10],[7,1],[7],[1,10],[13],[3,10],[4,10,7]]),
([w0,w106,w1,w2,w3,w30,w38],[5,68,181,25,197,182,19,2,65,9,106,196,99,36,8],[34,3,24,6,7,32,26,28,29,61,5,68,36,54,39,48],[[0],[0,1,100],[1,101,2],[0,1,102],[1,3,103],[1,3,104],[0,4,105,5,6],[6,101,7],[0,1],[1,3,6,8],[3,2,9,6],[0,10,106,4,105],[0,6,105],[0,3,107],[0,3,108],[0,109,11,110],[3,10,111,12,103],[3,112,2,104],[0,3,113],[0,3,114],[3,13,115,14]]),
([w0,w1,w2,w107,w3,w30,w38],[5,197,175,209,69,108,0,181,49,19,88,204,265,36,190,21,67,9],[34,8,0,4,6,52,32,28,29,61,16,36,18,14,76,48,7],[[0,1,100,2,101],[3,2,4,5,102],[3,2,6,7,102,8],[0,103,2],[3,9,102,10,11,104,105],[12,9,13,1,103],[0,4,101],[0,1,101,3,8],[0,8,106],[0,14,107,1,101],[0,3,108,2,15],[0],[0,4,109],[2,4,110],[2,1,4,13,111],[0,4],[2,4,16,8],[2,8,13,17],[0,10,112,2,113],[0,13,114,112],[13,10,115,1,116]]),
([w0,w1,w2,w3,w30,w34,w38],[65,5,67,88,209,28,21,197,182,166,8,9],[34,3,4,38,0,26,32,10,8,13,15,36,21,74],[[0,1,100],[0,2,101],[0,1,102],[0,3,103,4,5],[0,3,102,4,104],[0,4,102,5],[1,2,105],[1,6,106],[1,5,107],[1,7,106,4,108],[1,4,107,5],[1,2,109],[2,5,110],[2,8,109,9,101],[2,5,111],[1,5],[5],[1,5,112],[1],[5,6,113,10],[5,3,11,9]]),
([w0,w1,w108,w2,w3,w30,w38],[5,8,88,181,41,96,28,190,2,66,9,204,36],[45,38,3,24,7,9,27,28,12,61,68,11,36,72,39,48],[[0,1,100],[1,2,101,3,4],[1,5,102,2],[0,1,103],[1,4,101],[1,6,104],[1],[0,105,7],[0,4,106],[0,1,107],[0,6,108],[4,105,8],[0,2,9,4],[0],[4,6,10],[0,5,109,2,106],[1,110,11,111],[6,112,2,104],[0,1,113],[0,6,114],[1,6,115,12]]),
([w0,w1,w2,w109,w3,w30,w38],[148,8,258,71,209,54,181,28,171,41,197,196,67,9,99],[34,0,24,38,7,8,27,53,10,14,68,50,19,16,39,73],[[0,1,2,100,101],[1,3,101],[1,2,101,4,5],[0,1,6,102,101],[1,5,103],[1,4,104,7],[3,8,105,0],[4,0,5,105],[4,9,105,10,11,106,107],[1,108,0],[7,2,108,0],[1],[0,3,109],[1,3,110],[3,7,111],[0,3,12,5],[1,3],[5,7,13],[1,14,112,0,113],[7,6,114,0,104],[1,7,115,112]]),
([w110,w1,w2,w3,w30,w38],[5,9,2,0,28,6,49,21,310,17],[32,0,38,8,10,20,24,3,15,16,55],[[0,1,100],[1,101,2],[0,1,3],[1,102,4],[1,3,5],[0,103,6,100],[0,5,100,7],[0,104,8,100],[0,1,7],[0,105,106],[6,8,107,108,109],[1,6,7],[0,110,8,105],[0,1,9],[1,7]]),
([w0,w1,w2,w111,w3,w30,w38],[5,9,77,49,190,265,21,6,50,311],[34,0,58,6,8,32,28,16,19],[[0,1,100],[1,2,101],[1,3,101],[0,1,102],[1,4,103,5],[1,6,7],[0,2,104],[0,3,104],[0,3,105],[0,4,106,5,104],[0,1,6],[0],[0,2,8],[2,107,5],[1,2,6],[0,2],[3,107,5],[1,2],[0,9,108,5],[0,1,8],[1,6]]),
([w0,w1,w2,w3,w30,w112,w38],[5,9,165,88,28,6,190,21,312,49,166,2,182,128],[34,3,58,38,0,26,46,32,10,8,13,15],[[0,1,100],[1,2,101,3],[0,1,102],[1,3,103,2,4],[1,3,103,2,104],[1,4,5],[0,2,105,6,106],[0,5,107,7],[0,4,108],[0,6,107,2,109],[0,1,4],[0,8,110,3],[4,111,9],[10,9,11,12,110,101],[1,3,4],[0,3,13,4],[0,3,4],[0,1,4],[0],[1,4,7],[1,4]]),
([w0,w113,w2,w3,w30,w38],[9,6,54,313,28,2,21,39,42],[34,0,37,4,28,8,32,3,13,14,22,56],[[0,1,100],[0,101,2,102],[0,103,3,101],[0,4,104],[0,4,1],[1,105,2,5],[1,106,3,6],[1,4,7],[0,1,4],[2,3,107,108,109],[2,4,110,104],[0,2,4],[2,3,4,111,104],[0,4],[0,2,8]]),
([w0,w1,w2,w114,w3,w30,w38],[9,6,81,54,181,194,28,197,55,314],[34,0,24,38,8,27,59,14,18],[[0,1,100],[0,2,101],[0,3,101],[0,4,102,5,101],[0,3,103],[0,6,1],[1,2,104],[1,3,104],[1,7,105,5],[1,3,106],[0,1,6],[0],[2,107,5],[2,3,8,6],[0,2,6],[3,107,5],[2,3,5],[0,2],[3,9,108,5],[0,6],[0,3,8]]),
([w0,w1,w2,w3,w115,w30,w38],[309,9,6,165,54,21,181,28,197,182,2,239,315,99,128],[34,3,4,0,38,26,46,32,8,59,13,15],[[0,1,2,100],[1,3,101,4],[0,1,5,102],[1,6,102,3,103],[1,7,104],[1,5,2],[2,3,105,4,106],[2,5,107],[2,8,107,3,108],[2,7,109],[1,0,5],[0,4,5,110],[9,4,10,11,110,101],[7,12,111,13],[1,4,5],[1],[4,0,5,7,14],[1,0,7],[4,5],[0,1,5],[1,4,5]])]
noncomputable def p20_D6 : List StD := [
([w42,w4,w2,w5,w3,w30,w38],[0,33,37,85,143,197,14,100,38,165,88,11,209,101,106,316,196,145],[19],[[0,1,2],[3,4],[3,5,6],[7],[3,4],[3,4],[8,3,9],[3,8],[3,10,11],[9,4,11],[9,4,12],[2],[3,4],[13,14],[5,11,15],[3,16,17],[100,4],[15,4,11],[3,4],[3,4],[5,10]]),
([w4,w2,w5,w3,w30,w32,w38],[40,165,88,11,39,312,96,107,166,129,25,5,145,41],[],[[0,1],[0,1],[1,2,3],[1,4,3],[1,4],[1,2,5],[3],[2,6],[7,8],[7,8,9],[2,3,10],[11,6,12],[10,2],[13,2],[10,3],[6,2],[6,2],[6,3],[3],[8,2],[9,2]]),
([w1,w2,w5,w3,w12,w30,w38],[85,166,317,88,11,37,204,143,165,144,318,319,181],[16],[[0,1],[0,2,3],[4,3],[5],[0,6],[0,1],[4],[0,7],[2,0,8],[1,9,2],[2,4,10],[0,11,12],[0,2],[12,3],[10,1,4],[4],[0,3,7],[0,4,7],[8,6,100],[8,1,4],[1,3]]),
([w1,w2,w5,w3,w30,w56,w38],[11,166,320,88,39,197,43,143,165,25,114,196,145],[14],[[0,1],[0,2,3],[0,3],[0,4,5],[6],[7,1],[0],[1,7],[1,2],[2,1,8],[2,0,9],[10,11,12],[9,3],[2,8],[9,0],[9,3],[8,3,100],[1,0,5],[0],[1,0,3],[8,0]]),
([w1,w4,w5,w3,w30,w33,w38],[52,148,4,88,126,197,166,25,129,312,196,145],[],[[0],[1,2,3],[4,3],[4,5],[4,6],[7,3,8],[1,2],[4,3],[4,7],[4,6],[7,3,9],[1,10,11],[7,0,3],[0,6],[7,4],[7,3],[6,3,10],[6,4,5],[2],[5,3],[5,3]]),
([w1,w4,w2,w3,w15,w30,w38],[47,89,166,123,197,196,88,204,85,165,312,51,144,318,154,143,25],[],[[0],[1,2,3],[3,4,5],[3,4,6],[3,7],[8,2],[1,2,3],[3,5],[3,6],[3,7],[9,2,10],[1,0,2],[11],[1,12],[1,3,13],[14],[5,15,7],[2,3,4],[16,6],[13,2,3],[2,3,12]]),
([w16,w1,w4,w2,w3,w30,w38],[197,88,5,0,47,25,166,154,85,159,145,204,165,239,144,318,143],[],[[0,1,2],[2,1],[1,3],[4],[5,1],[0,6],[7],[0,6,8],[9,0,10],[0,11,8],[8,6],[9,6],[8,10,9],[9,11],[12,0,13],[6,13],[6,14,11],[0,9,15],[8,16],[6,0],[0,9,14]]),
([w4,w2,w7,w3,w6,w30,w38],[11,30,166,139,196,88,204,165,288,171,36,197,19,169,106],[],[[0,1,2],[0,1,3],[0,4],[0,5],[0,6],[7,2,8],[0],[2,4],[5,2,9],[2,9],[4,0,10],[10,4,11],[12,5,11],[11,6,13],[10,0],[0],[4,13,6],[2,0,11],[14,5,6],[9,0,2],[2,0,9]]),
([w4,w2,w3,w6,w30,w32,w38],[11,166,196,88,39,204,43,36,239,171,197,25,19],[],[[0,1],[0,2],[0,3],[0,4,5],[0,4,6],[7,1,8],[1,8],[3,1,9],[1,9],[8,1],[2,0,7],[0],[2,5],[7,2,10],[1,0,10],[11,3],[12,3,10],[7,0],[0],[1,0,7],[7,0]]),
([w1,w2,w10,w3,w6,w30,w38],[318,30,166,139,11,197,196,88,204,165,85,143,171,239],[19],[[0,1,2],[3],[4,5,6],[0,5,7],[0,8],[9,2,10],[4],[0,11],[7,0,9],[2,12],[0,4],[0,6,13],[0,13],[13,8,100],[0,2,4],[1],[0,11],[2,4,5],[9,7],[0,2,4],[0,4]]),
([w1,w2,w3,w6,w30,w56,w38],[321,171,11,197,196,88,39,43,114,239,16,143,25],[13],[[0,1],[2,3,4],[0,3,5],[0,6,3],[7],[8,1],[0,9],[1,9],[9,1],[10,1,100],[0,2],[2],[0,11],[0,4,9],[1,2,3],[12,0,5],[0,9],[0,2],[2],[0,1,2],[0,1,2]]),
([w1,w4,w2,w6,w9,w30,w38],[47,36,197,88,196,204,5,16,143,123,239,96,122],[],[[0],[1,2],[1,2,3],[1,2,4],[1,5],[6,4],[7,8,9],[1],[9,4],[9,5],[1,2,10],[3,0,11],[1],[5,12],[1,9],[0,3],[11,3],[1,2,9],[4,8,5],[1,2,5],[1,9]]),
([w18,w1,w4,w2,w3,w30,w38],[5,88,178,322,47,25,197,11,51,171,179,196,204,323,312,96,144,99],[],[[0,1],[2,3],[4],[0,4],[5,1],[5,6,7],[8],[2,9],[10,6,11],[2,12],[2,9],[10,9],[2,11,10],[10,12],[13,6,14],[2,15,11],[12,9,16],[6,10,13],[2,17],[2,6],[6,9]]),
([w1,w4,w2,w6,w30,w34,w38],[65,36,171,88,197,196,5,130,143,239,166,25],[],[[0],[1,2],[1,3],[1,4],[1,4,5],[6,2],[7,2],[1],[7,8],[7,5],[1,2,9],[2,8],[9,2],[5,2,10],[1,7],[11,0,3],[0,5],[1,4,2],[1],[1,2,4],[1,2,7]]),
([w1,w4,w2,w67,w3,w30,w38],[52,126,171,88,204,25,181,312,96,36,196],[],[[0],[1,2],[1,3],[1,3],[1,4],[5,2,6],[1,2],[1,3],[1,3],[1,4],[5,2,7],[5],[2,8,3],[4,0,5],[3,1,5],[9,8,10],[0,3],[4,1,2],[4,3,5],[2,1,5],[6,1,2]]),
([w1,w4,w2,w3,w68,w30,w38],[65,241,171,130,197,207,88,204,25,95,239,166],[],[[0],[1,2],[3,4,5],[1,4,6],[1,7],[8,2,9],[3,2],[1,5,3],[1,6],[3,7],[1,2,10],[1,10],[6,2,11],[7,2,8],[1,3],[8],[1,0,8],[2,3,4],[0,1],[1,2,3],[1,2,3]]),
([w40,w4,w2,w7,w3,w30,w38],[36,88,171,201,31,207,30,11,139,204,312,324,202,166],[18],[[0,1],[1,2,3],[3,1,4],[0,5,3],[6],[0,2,7],[7,2],[3,8],[7,1],[3,9,7],[3,1,10],[7],[1,11],[3,2],[1,7,3],[100,1],[3,9,12],[3,1,7],[3,1],[2,7,3],[13,1]]),
([w42,w40,w4,w2,w3,w30,w38],[25,36,33,37,241,239,100,143,11,321,171,207,173],[],[[0,1],[0,2,3],[4,5],[6],[0,7,4],[0,7,8],[1,9,4],[5,10],[1,11,12],[3],[1,8],[8,7],[4,5],[5,7,8],[4,5],[4,5],[5,10],[4,5],[4,7],[10,7],[4,8]]),
([w40,w1,w4,w2,w3,w33,w38],[228,88,52,25,207,162,126,204,181,312,96,143],[],[[0,1],[0,1],[1,2,3],[0,4,3],[5],[0,4,6],[2],[6,4],[6,1],[6,7],[3,1,8],[6,4],[6,1],[6,7],[3,1,9],[1,10],[3],[1,6,3],[7,1,11],[3,6],[3,1,6]]),
([w0,w2,w7,w3,w12,w30,w38],[210,166,88,181,36,2,312,207,11,197,204,202,196],[16],[[0,1],[0,2,3],[0,3,4],[4],[0,2,3],[0,1],[4],[1,2],[5,1,6],[1,7],[2,8,4],[4,2,9],[5,6],[9,10,11],[3,1],[8],[4,2,12],[1,3],[6,10,100],[4,1,6],[1,2]]),
([w0,w2,w7,w3,w30,w56,w38],[211,166,88,197,196,204,181,325,200,207,2,11,201,182,36],[14],[[0,1],[0,2,3],[0,4],[0,2,5],[6],[0,1],[7],[1,8,2],[1,9],[10,1,8],[2,11,12],[13,2,3],[3,5,13],[10,3,8],[12,1,11],[4,2],[14,2,100],[1,3],[11],[1,2],[8,1,11]]),
([w0,w4,w7,w3,w9,w30,w38],[36,47,4,197,212,166,204,123,312,202,143],[],[[0],[1,2,3],[0,4],[4,5],[4,6],[0,3,4],[1,2],[0,7],[7,5],[7,6],[0,3,8],[0,3],[0],[3,6,9],[0,5,7],[2],[0,10],[5,3],[5,10,6],[0,3,6],[0,7]]),
([w0,w4,w2,w3,w30,w69,w38],[228,126,166,196,204,320,197,207,201,312,200,238,36,164],[],[[0],[1,2],[1,3],[1,4],[1,5,6],[7,2],[1,2],[1,3],[1,4],[1,5,6],[8,2,9],[2,10,3],[2,1,4],[11],[3,1,8],[3,7],[12,3,6],[2,1,6],[13],[2,1,7],[8,1]]),
([w70,w0,w4,w2,w3,w30,w38],[0,197,219,220,11,36,126,223,164,166,196,88,202,207,201,312,200],[],[[0,1],[2,1,3],[1,4],[5,1],[6],[5,4],[7],[8,9],[8,10],[8,11,12],[13,1],[8,9],[8,10],[8,12],[14,1,15],[9,16,10],[9,13],[1,8,14],[10,11],[9,1],[1,8,11]]),
([w0,w4,w2,w74,w3,w30,w38],[36,123,143,197,196,19,312,202,106],[],[[0],[1,2],[1,3],[0,4,1],[1,2],[0,2,5],[1,2],[1,3],[0,4,1],[1,2],[0,2,6],[0],[0,1,2],[7,8],[0,1],[0,1,3],[3,2,7],[0,1],[0,2],[5,1,2],[0,1]]),
([w0,w4,w2,w3,w30,w75,w38],[36,130,166,196,143,197,207,182],[],[[0],[1,2],[0,3,1],[1,4],[1,5],[0,2,6],[1,2],[0,3,1],[1,4],[1,5],[0,2,7],[0,4],[2,6],[2,4],[0,1],[0,1,3],[0,1,3],[2,1,4],[0],[0,1],[0,1]]),
([w42,w0,w4,w2,w9,w30,w38],[47,197,123,36,159,143,196,236,209,202,106],[],[[0,1],[0,1],[1,2,3],[4],[1,5,3],[6,2,5],[3],[2,5],[2,6],[2,5],[3,1,7],[2,5],[2,6],[2,5],[3,1,8],[3],[9,10],[1,2,3],[6,5,9],[3,1,2],[1,2,3]]),
([w0,w2,w10,w3,w30,w32,w38],[211,166,326,196,88,312,197,325,207,11,201,36,327,182,106],[18],[[0,1],[2],[0,3],[0,4,5],[0,4,6],[0,1],[7],[1,5,3],[1,8],[6,1,5],[3,9,10],[11,3,100],[10,12,13],[10,13],[10,1,9],[3,4],[14,3,6],[1,5,6],[9],[1,4],[10,1,5]]),
([w0,w2,w3,w12,w30,w32,w38],[226,166,196,36,88,204,197,239,40,182,328,25,11],[15],[[0,1],[0,2],[3],[0,4,5],[0,4,6],[0,1],[1,7],[8,1,100],[1,9],[6,1,7],[2,7,3],[10],[2,4],[3,2,6],[1,6],[11,5,9],[11,6,9],[3,1,9],[3],[1,4],[3,1,12]]),
([w0,w4,w2,w3,w32,w33,w38],[228,243,88,196,197,204,126,207,25,182,122,106],[],[[0],[1,2],[1,3],[1,2,4],[1,2,5],[1,3],[6,7],[6,2],[1,4],[6,5],[8,2,9],[2,10],[4,6,10],[8],[2,6,8],[11,2,4],[3,2],[5,4],[4,5,0],[8,2,6],[3,2]]),
([w77,w0,w4,w2,w3,w30,w38],[0,197,138,246,126,36,232,238,129,196,88,204,145,106,312,200,247],[],[[0,1],[2,1,3],[4],[5,1],[1,4],[5,4],[6],[7,8],[7,9],[7,10,11],[12,1],[7,8],[7,9],[7,11],[13,1,14],[8,15,9],[8,13,11],[1,7,16],[9,10],[8,1],[1,7,10]]),
([w0,w4,w2,w3,w32,w34,w38],[36,251,166,88,197,204,130,182,143,129,329],[],[[0],[1,2],[0,1],[1,3,4],[1,3,5],[0,2,1],[6,2],[0,3,6],[1,4],[6,5],[0,2,7],[0,8],[4,2,9],[2,7],[0,6],[0,3,4],[10],[2,4],[0],[0,2,6],[0,3,2]]),
([w0,w1,w2,w3,w116,w30,w38],[318,197,88,123,196,262,204,312,132,143,323,106,159,25],[],[[0,1,2],[2,0,3],[0,4,3],[5],[3,2,6],[0,1,7],[0,7,1],[3,1,2],[8],[0,6],[9,2],[0,3,2],[10],[6,11],[0,3],[12],[0,2,4],[6,1],[13,6],[0,1,3],[0,2,1]]),
([w26,w0,w1,w2,w3,w30,w38],[0,318,262,106,197,323,196,143,11,159,239,204],[],[[0,1,2],[1,3,4],[1,5],[6],[7,3],[1,8],[1,4,3],[9,1,7],[1,10],[3,7],[1,4,10],[1,3,4],[3,4],[1,11],[3,11,7],[1,7],[10,3,11],[1,9],[1,7],[11,4],[1,9]]),
([w0,w1,w2,w3,w30,w117,w38],[106,197,126,143,196,181,207,327,330,312,201,238,36,164],[],[[0,1],[2,3],[2,4],[0,3],[5],[6,1],[1,0],[0,1],[1,7,2],[8],[0,4,3],[4,3,9],[10,0,6],[11],[1,2,10],[0,3],[12,4],[10,1,2],[13],[0,2],[8,1,2]]),
([w118,w0,w1,w2,w3,w30,w38],[0,312,88,219,330,201,247,126,197,196,207,164,182],[],[[0,1,2],[3,1,4],[4,5,6],[2,1],[7],[2,7,4],[5,2,8],[2,1],[5,9],[1,2],[10,1,8],[8,1],[11,2],[1,12],[5,1],[2,1],[5,10],[2,11,5],[1,2],[5,1],[8,2]]),
([w0,w1,w2,w12,w9,w30,w38],[227,197,143,36,196,331,204,2,312,122,123],[16],[[0,1],[0,2],[3],[0,4],[0,2],[0,1],[1,2],[5],[3,1,4],[1,6,2],[2,4],[7,2,8],[3],[6,9],[1,10,3],[7,4,8],[8,2,100],[3,1,8],[4,2,6],[3,1,6],[1,10,3]]),
([w27,w0,w1,w2,w3,w30,w38],[0,36,197,312,318,11,25,204,106,179,88,196,323],[],[[0,1],[1,2,3],[4],[1,5],[6,7,8],[1,2,5],[8,2],[9,3,10],[9,11],[3,7,8],[12,2,3],[2,3],[8,2],[2,7,9],[8,3],[10,3],[7,8],[2,9,12],[3,10],[7,2],[2,9,8]]),
([w0,w1,w2,w3,w30,w119,w38],[321,88,143,130,196,241,207,332,204,173,203,2,253,333],[],[[0,1],[1,2,3],[0,4,3],[3,0,2],[5],[0,2,6],[0,6],[3,1],[0,7,8],[9],[2,1],[0,2],[8,6,10],[11,2],[0,3],[0,1,2],[12],[8,2],[13],[0,1,3],[0,1,3]]),
([w120,w0,w1,w2,w3,w30,w38],[0,36,203,173,2,239,207,321,11,88,129,333,189,182],[],[[0,1],[1,2,3],[4,5,6],[1,2,6],[7],[1,8],[2,9,5],[2,10],[2,5,11],[5,9],[6,5,10],[5,6],[12,2,6],[2,13],[2,6,10],[9,5,10],[2,6],[2,5],[2,6],[2,12],[10,6]]),
([w0,w1,w2,w3,w56,w33,w38],[243,88,197,196,181,204,207,126,334,25,182,122,2,228],[14],[[0,1,2],[0,1],[0,3],[4],[0,1,5],[0,2],[2,6,7],[7,1],[8],[2,5,7],[9,1,10],[1,11],[12,6,11],[9],[1,7,9],[13,1,100],[3,1],[5,2],[7,5],[9,1,7],[2,1]]),
([w121,w0,w1,w2,w3,w30,w38],[0,88,181,138,25,246,126,36,122,247,197,312,196,145,335,204,238],[],[[0,1,2],[3,4,5],[6],[7,1,8],[4,6],[4,1,6],[9,1,10],[1,11],[8,12],[8,1,11],[13,10],[10,11],[8,1],[8,14,9],[9,1,11],[1,8],[9,8,15],[1,16,9],[9,1],[8,10,11],[8,1,10]]),
([w122,w0,w1,w2,w3,w30,w38],[0,321,241,25,2,182,239,203,333,11,197,129,254,166,143],[],[[0,1,2],[1,3],[4,5,6],[7],[1,8],[1,9],[1,10,5],[5,11],[1,6],[6,1,12],[1,6],[1,13],[5,10],[1,5,10],[11,5,13],[1,6],[6,5],[1,5],[1,14],[11,10],[1,12]]),
([w0,w1,w2,w123,w3,w30],[11,6,336,9,312,85,209,167,288,88,30,139,311,337,318,338,201,197,314,25],[3,24,0,6,26,27,28,8,61,68,18,19],[[0,1,2,3],[0,2,100],[0,4,5,6,7],[0,8,101,6,102],[0,9,103,4],[0,2,104],[0,4,10,6,11],[0,8,105,6],[0,12,106,4,107],[0],[2,13,108,14,100],[2,15,109,16,100],[5,12,17,4,105,110],[16,18,19,9,13,103,111],[4,14,103,9,13,110,105]]),
([w57,w0,w1,w2,w3,w9,w30],[47,36,197,337,123,204,339,239,209,312,122,340],[],[[0,1],[1,0],[2,3,4],[1,2],[4,2,5],[2,3,4],[1,2,6],[4,3],[1,7],[4,7,8],[4,3],[1,9,2],[4,2,8],[1,2,8],[1,5],[1,3],[1],[5,10],[11],[1,3],[5,3]]),
([w57,w124,w0,w1,w2,w3,w30],[197,11,154,341,342,337,159,36,315,88,339,239,204],[],[[0,1],[2,0],[3,4],[0,5,6],[6,0,7],[0,5,6],[1,8,9],[0,8],[7],[10],[5,8],[3,0],[3,5],[3,11,7],[3,5],[0,8],[6,0,8],[0,12,6],[7,5],[11,8,12],[7,5]]),
([w57,w0,w1,w2,w3,w30,w33],[52,197,343,344,338,126,88,312,196,209,182,25,345],[],[[0,1],[2,3],[1,4,5],[5,1,4],[1,6],[1,6],[2,1],[2,7,6],[2,8],[2,4,7],[2,4,9],[1,4,5],[5,1,4],[1,10],[1,7],[6,7],[11,4],[11],[7,4],[8,4],[12]]),
([w57,w125,w0,w1,w2,w3,w30],[88,11,162,197,346,347,338,164,312,348,349,196,182,25],[],[[0,1],[2,3],[4,5],[0,6,7],[7,3,6],[3,0],[0,8],[1,8,3],[9],[0,8],[10],[4,0,3],[0,8],[4,11],[4,0,8],[3,6,7],[7,0],[3,12],[0,8],[13,6],[8,0]]),
([w57,w0,w1,w2,w3,w30,w34],[65,36,130,338,88,25,129,239,209,182],[],[[0,1],[1,0],[2,3],[1,3,2],[2,4,5],[2,4,6],[1,3],[2,6],[1,7],[2,3,7],[2,3,8],[1,3],[2,3],[1,9,5],[1,9,8],[1,7],[5,3],[6,3],[1,5],[5],[1]]),
([w25,w0,w4,w2,w3,w30,w38],[0,197,36,122,204,11,123,143,196,145,209],[],[[0,1],[0,1],[1,2],[2,1],[1,3,4],[2,5],[2],[6,7],[2,8,3],[3,4],[2,1,9],[6,7],[2,8,3],[3,4],[2,1,10],[2,3,7],[4,3],[1,6,2],[2,7],[3,1,4],[1,6,2]]),
([w88,w1,w4,w2,w3,w30,w38],[11,88,52,56,36,122,196,126,338,204,25,143,209],[],[[0,1],[0,1],[0,2,3],[4,5,6],[0,1],[4,0],[2],[7,8],[5,1],[5,9],[10,1,11],[7,8],[5,1],[5,9],[10,1,12],[1,5],[9,2,5],[1,7,8],[6,1],[5,7],[5,1,6]]),
([w37,w1,w4,w2,w3,w30,w38],[11,338,143,207,70,65,130,204,25,209,241],[],[[0,1],[0,1],[2,3],[0,3,4],[0,1],[1,0],[5],[2,1],[6,1],[2,7],[2,3],[6,1],[6,1],[6,2],[8,2,9],[10,2],[7,1,8],[1,6],[7,1,2],[1,2,6],[10,3,6]]),
([w102,w0,w4,w2,w3,w30,w38],[0,197,143,338,100,36,11,173,196,130,207,209],[],[[0,1],[0,1],[1,2,3],[3,1,4],[1,2,5],[5,2,6],[5],[7,2],[5,8,7],[9,2],[3,1,10],[9,2],[5,3,9],[7,2,9],[5,1,11],[5,2],[7,3],[1,9,3],[5,2],[3,1,9],[1,9,5]]),
([w126,w0,w1,w2,w3,w30,w38],[321,203,143,350,11,173,338,241,196,209,130,204],[],[[0],[1],[2,3],[0,1],[1,0],[0,4],[5,6,7],[3,2],[5,8],[3,2],[6,2,9],[2,6],[9,6,10],[2,11],[2,8],[7,2],[5,6],[3,10],[5,2,6],[5,2,10],[3,10]]),
([w14,w1,w2,w3,w6,w30,w38],[30,139,246,36,239,143,204,166,11,196,338,88,96,171,318],[],[[0],[1,2],[3,4],[3,4],[4,5,6],[3,4],[5,7],[8,9],[8,10],[5,6],[5,6],[7,5],[11,5,12],[6,13,7],[6,8,14],[1],[6,5],[6,5],[12,5,10],[10,5,8],[7,8,13]]),
([w17,w1,w2,w5,w3,w30,w38],[33,166,318,143,262,25,204,338,11,196,106,239],[],[[0],[1,2,3],[2,4],[2,0],[5,3,6],[1,3],[2,1],[2,7],[8,9],[2,6],[3,1],[8],[1,3],[1,10,6],[2,8],[2,9,11],[11,3,7],[2,1,8],[2,3],[1,3],[1,8,2]]),
([w1,w5,w3,w6,w30,w33,w38],[228,197,171,106,182,196,239,52,143,318,25,19,162],[],[[0,1,2],[3,1],[3,1],[1,4],[1,3],[3,2,4],[0,5,6],[0,6],[6,2],[6,2],[0,1,4],[7],[3,5],[5,8,9],[2,1],[3,10],[11,8],[2,1],[12],[1,2],[1,2]]),
([w1,w5,w3,w6,w30,w47],[11,197,132,143,166,36,14,239,196,96,182,351,318,106,19],[8,32,28,6,19,0,16],[[0,1,100,2,101],[0,1,101,2,100],[0,1,101,2,100],[0,2,102,1,100],[0,3,4],[5,6,7,8],[5,6,7,9],[7,6,10,11,103,104],[0,2,5,1],[0],[8,12,103,11,104],[0,2,4,1,3],[9,13,105,11,103,106],[0,2,14,1,3],[0,1,4,2,103]]),
([w1,w2,w3,w6,w30,w59,w38],[143,106,197,182,36,352,166,56,25,196,239,162,171],[],[[0,1,2],[1,2],[1,2],[0,3,2],[4,1,5],[0,3,1],[3,0],[3,0],[6,1,3],[7],[2,3,8],[8],[1,0],[4,9,10],[5,0],[1,0],[4,10],[5,0],[11],[1,12,2],[4,0,5]]),
([w60,w1,w2,w3,w6,w30,w38],[36,197,182,0,268,196,239,333,353,52,171,129,108,25,141,338],[],[[0,1,2],[2,3,4],[0,5,6],[7,6,8],[9],[0,1,6],[1,10,11],[2,1],[2,1],[1,2],[11,2,5],[2,12],[2,11],[11,2],[1,2,13],[13],[5,14],[10,1],[13,14,15],[10,1],[1,10]]),
([w1,w2,w5,w6,w30,w34,w38],[143,166,36,197,132,11,196,65,88,96,186,25,141,14,68],[],[[0,1],[2,3,4],[4,3],[0,4,3],[5,3,6],[0,1],[7],[8,0,9],[1,10],[1,0],[3,11],[2,9,8],[11,0,12],[13,6],[2,0,4],[9,0,8],[5,6],[4,0],[14],[1,4],[1,0]]),
([w50,w1,w2,w5,w6,w30,w38],[11,196,108,318,239,62,65,25,166,132,129,88,96,106,187],[],[[0,1],[1,2,3],[3,1,4],[5],[6],[7,0],[3,8],[3,2,9],[3,2,9],[2,9],[7,1,10],[7],[11,2,12],[2,13,14],[1,3],[3,4],[4,13],[3,1,4],[7,11],[3,1,9],[1,9]]),
([w1,w2,w5,w3,w30,w61,w38],[143,166,321,88,132,197,318,352,65,141,2,96,25,196,239,68],[],[[0,1],[2,3],[4,3,5],[0,4,5],[6,4,7],[0,1],[8],[1,0],[1,9],[10,0,11],[3,12],[2,13,14],[9,0],[10,3,11],[2,0,4],[12,0,3],[12],[1,0],[15],[1,3],[6,0,7]]),
([w62,w1,w2,w5,w3,w30,w38],[318,197,132,2,166,96,333,208,0,65,106,129,68,108,25,196,239,88],[],[[0,1,2],[3,4,5],[6,0,7],[0,8],[9],[0,1,2],[1,4,10],[2,1],[2,1],[1,2],[10,4,11],[12],[4,13],[4,10],[1,14],[6,15,16],[14,10,17],[2,1],[10,17,14],[2,1],[1,2]]),
([w1,w5,w3,w31,w33,w38],[132,354,206,106,88,338,96,108,25,197,355,143,166,131,356,14,90,270,196,157,144,315,11],[8,27,53,2,29,7,5,39],[[0,1,2,3,4,5],[0,6,100,7,4,101,102],[8,103,6],[9,10,11,0,12,13],[3,8,4,104,14,105],[1,15,16,6,106,101],[8,3,5,15],[8],[1,0,5,8,7,17],[8,106,3],[18,10,19,4,7,11],[6,0,8,7,107,105],[8,3,11,15],[3,8,20,21],[8,0,22,9]]),
([w1,w5,w3,w30,w31,w47],[11,357,14,132,25,143,166,321,229,239,196,351,96,204,318],[8,32,28,2,5,27,54,6],[[0,1,100,2,101],[0,1,101,3,100],[0,3,102,1,4],[0,1,103,4],[0,5,6],[7,2,8,9,10,104,105],[4,11,8,2],[4,12,8,2],[0,2,4],[4,11,106,13,107],[4,104,14],[0,3,6,1,5],[0],[0,1,4,107],[0,4,5]]),
([w1,w2,w3,w15,w30,w31,w38],[143,166,96,196,321,108,132,175,51,204,239,154,88,47],[],[[0,1],[2,3],[4,5,6],[0,6,5],[2,5,7],[0,1],[1,0],[8],[1,9],[7,0],[3,10,7],[11],[2,0,9],[7,3],[1,0],[7,0,12],[7,2,12],[4,0,6],[13],[1,6],[2,0,10]]),
([w16,w1,w2,w3,w30,w31,w38],[321,88,0,47,143,25,204,166,132,108,358,239,318,154],[],[[0,1],[0,2],[3],[4,1,5],[5,1],[0,6,4],[4,7],[8,9],[4,6],[10,8],[4,6],[7,4],[6,7],[10,4],[6,11,10],[6,4],[10,11,12],[6,4],[13],[7,8],[12,4,11]]),
([w0,w1,w2,w3,w127,w30,w38],[318,108,132,123,239,262,143,166,171,159,25,204],[],[[0,1,2],[3,0,1],[0,4],[0,5],[3,6],[0,1,2],[0,7],[2,1],[0,1,2],[0,2,1],[6,7],[0,1],[0,7],[1,8],[0,3],[9],[0,6],[2,1],[10,6,11],[0,1,2],[0,2,1]]),
([w0,w1,w2,w3,w30,w128,w38],[330,88,96,196,27,132,166,143,126,171,164],[],[[0,1,2],[0,2,1],[0,3],[2,1],[0,1,4],[2,3,5],[5,6,7],[2,1],[0,5],[0,5],[0,1,7],[1,2],[0,8,9],[0,4],[0,8],[0,1],[3,1],[0,7,5],[10],[3,1],[0,1,3]]),
([w73,w1,w2,w5,w3,w30,w38],[0,33,37,2,143,96,106,11,166,132,108,204,318,196,239],[19],[[0,1,2],[3,4,5],[3,5],[2,5],[5,4,6],[5,4,7],[4,6,8],[7,6,9],[6,10],[4,9,10],[4,8],[2],[8,4],[8,6,11],[9,7,12],[12,13,14],[14,4,100],[9,4],[6,4],[8,4],[6,7]]),
([w0,w1,w2,w129,w3,w30,w38],[318,108,132,123,262,239,143,166,323,106,204,154,25],[],[[0,1,2],[3,0,1],[4],[0,5],[3,6],[0,1,2],[0,7],[0,1,2],[2,1],[0,2,1],[6,7],[8],[0,1],[1,9,10],[0,3],[0,3,11],[12,6],[0,1,2],[0,6],[2,1],[0,2,1]]),
([w0,w1,w5,w3,w32,w33,w38],[243,96,40,196,143,228,171,334,166,25,129,145,14,106,126],[],[[0,1],[2],[0,3],[0,1],[0,1,4],[0,3],[5,6],[1,3],[7],[4,2,8],[9,3,10],[5,1,11],[12,6,13],[0,4],[5,3,11],[1,3],[3,1],[1,14],[2,4],[9,3,10],[3,6]]),
([w60,w0,w1,w2,w3,w32,w38],[39,40,36,204,196,359,88,96,166,164,360,25,129],[],[[0,1],[2,3],[1,0],[2,4,5],[2,3],[2,4,5],[5,6,7],[6,7],[5,4],[5,6,7],[5,3],[5,8,9],[7,4],[10],[11,3,12],[4,7],[5,8,12],[3,9,11],[7,4],[3,9,7],[11,3,9]]),
([w0,w1,w3,w15,w30,w33,w38],[264,108,196,20,96,228,171,132,318,166,175,129,361,106,362],[],[[0,1],[0,2],[3],[0,4],[0,1],[0,1],[4,1,2],[5,1,6],[1,7],[8,7,9],[10,2,11],[12],[2,13],[2,1,4],[4,1,6],[10,6],[10,6],[5,1,7],[14],[1,6],[2,6]]),
([w16,w0,w1,w3,w30,w33,w38],[52,2,228,106,171,363,25,154,364,166,126,108,365,239,144,132,129,146,358,366],[],[[0,1],[2,3,4],[5],[6,3,4],[7,0,8],[2,9,10],[3,11],[12,13,14],[3,13],[7,9],[4,9],[3,11],[11,15],[13,3,9],[3,4,16],[3,17,18],[9,11],[4,11],[19],[3,4,9],[18,4,13]]),
([w0,w1,w5,w3,w33,w34,w38],[282,108,67,144,165,228,132,318,166,129,146,14,367,130],[],[[0,1],[2],[0,3],[0,1],[0,4],[0,1],[5,1,6],[4,1],[7,4,8],[3,1,4],[4,8,9],[5,10],[0,1],[11,3],[5,1,6],[7,1],[12],[6,1],[2,3],[7,6,13],[3,1,8]]),
([w0,w1,w5,w3,w15,w30,w47],[368,357,16,144,20,204,123,132,129,14,196,351,25],[],[[0,1],[2],[0,2,3],[4],[0,5],[0,1],[6,1,7],[6,1,7],[6,1,7],[1,5,3],[8,5],[9,10],[4],[9,3],[0,1],[9],[3,11],[5,1],[12,3],[7,1],[1,3,7]]),
([w58,w0,w1,w5,w3,w30,w47],[16,11,141,132,369,25,318,357,262,196,370,351,14],[],[[0],[1,2,3],[0],[4],[5,2,6],[3,1,5],[2,7],[8],[6,9,10],[2,11],[3,6,7],[2,7],[3,2],[6,3,7],[2,9,6],[6,9,12],[2,11],[3,6],[6,2],[3,7],[2,3,7]]),
([w0,w1,w5,w3,w30,w59,w47],[371,357,23,196,351,27,14,126,132,352,144,145],[],[[0,1],[2],[0,3],[0,2,4],[5],[0,1],[6,1],[7,1,3],[1,8],[7,1,9],[4,3],[6,3],[6,4],[5],[0,1],[3,4,10],[11,3],[8,1],[6],[1,7,8],[9,1]]),
([w0,w1,w5,w3,w30,w34,w47],[296,357,67,165,351,132,166,36,239,141,14,25,146,372],[],[[0,1],[2],[0,3],[0,4],[0,3],[0,1],[5,1],[3,1],[1,5],[3,1],[4,3,6],[7,8],[8,4,9],[10,8],[0,1],[11,12],[11],[5,1],[13],[1,5],[6,1]]),
([w50,w0,w1,w5,w3,w30,w47],[58,318,132,357,239,373,374,69,297,204,182,146,25],[],[[0,1],[2,3],[1,4],[5],[6],[1,3],[1,3,2],[7],[1,8],[8,9],[2,1,3],[1,3,2],[2,3],[1,2,3],[1,9],[1,4],[4,9,10],[1,2],[1,11,12],[1,3],[3,2]]),
([w130,w0,w1,w2,w5,w3,w38],[0,204,132,318,108,144,162,268,14,88,375,376,166,143,175,337,196],[88],[[0,1],[2,1,3],[1,4,5],[6,1,7],[1,8],[2,4],[2,4],[100,5,4],[9],[5,10,11],[2,1],[2,12,13],[2,4],[2,4],[13,1],[14],[10,4,12],[1,15],[11,10,16],[2,1],[1,4]]),
([w28,w0,w1,w2,w3,w30,w38],[0,318,262,108,323,14,25,143,204,88,144,377,239,166,132,123],[],[[0,1,2],[3],[1,4],[1,5],[6,7,8],[1,7,8],[1,9],[9,1,10],[1,11,12],[12,7,9],[1,7,12],[1,13],[14,9,15],[1,8],[7,8],[1,7],[8,10],[1,12],[1,7],[8,7],[1,9,13]]),
([w0,w1,w2,w15,w30,w34,w38],[266,108,378,143,379,196,166,36,132,123,380,186,239,175,88,381],[],[[0,1],[0,1],[2],[0,3],[0,4,5],[0,1],[3,6],[7,1,8],[1,8],[9,1,5],[3,5],[10],[1,11],[4,1,6],[5,12,13],[13,3,14],[13,14],[7,1,8],[15],[1,8],[6,1]]),
([w50,w0,w1,w2,w15,w30,w38],[47,239,318,132,108,358,266,267,382,204,166,175,129,383,144,88],[],[[0,1,2],[3,4],[2,1],[5],[6],[3,4],[1,4,3],[7,2,4],[8],[1,9,7],[2,1],[1,10],[2,4,3],[2,3,4],[11,9,12],[13],[1,14,9],[2,1],[5,9,15],[2,4,3],[2,3,4]]),
([w0,w1,w2,w3,w131,w15,w38],[384,108,385,144,204,209,166,239,132,175,129,177,14,358,123],[],[[0,1],[0,1],[0,2,3],[0,4],[5],[0,1],[2,6,7],[8,1],[1,4,3],[8,1],[9,4,10],[2,0,6],[1,3,2],[11],[2,7,9],[3,12],[13],[4,1],[],[1,14,3],[8,1]]),
([w0,w1,w2,w3,w30,w132,w38],[175,108,379,144,239,386,88,209,166,132,36,352,129,177,358],[],[[0,1],[0,1],[0,2,3],[4,5,6],[7],[3,1,4],[2,8,4],[9,1],[0,9],[10,1,11],[0,6,12],[2,0,8],[0,3,2],[13],[0,4],[0,6],[14],[0,1,8],[],[1,6],[0,1,11]]),
([w130,w0,w1,w2,w3,w30,w38],[0,239,88,36,108,132,162,177,175,144,196,166,129,182],[],[[0,1,2],[3,4,5],[6,1,7],[2,8],[9],[2,4],[1,2],[2,4,8],[8,1,10],[1,2],[5,1,4],[1,11],[5,2,4],[4,5],[8,2,12],[2,1,11],[1,13],[2,1,8],[8,2],[5,4],[4,2]]),
([w130,w0,w1,w2,w3,w15,w38],[47,239,204,318,144,196,14,25,132,108,387,388,166,129,182,337,376],[],[[0,1,2],[3,2],[2,1,4],[2,5,6],[7],[3,5,8],[1,9,8],[10,4,9],[4,1],[11],[4,1],[1,12],[8,5,9],[8,9],[13,2],[5,1,12],[14],[2,1,15],[16],[2,9],[8,2]]),
([w130,w0,w1,w2,w3,w38],[0,88,337,239,49,36,132,204,108,182,144,19,196,14,11,175,375,166,96,129,387,312],[8,28,34,0,88,3,14,89,12,32,7,90,91],[[0,1,2,3,4],[5,6,7,8,100,101],[4,9,10,3,11],[4,1,2,12,13],[2,1,5,14,8],[3,6,100,1,2,102,103],[1,9,104,10,2,103,105],[10,15,103,3,12,16,106],[10,6,103,3,7,107,108],[6,3,16,17,100],[6,18,100,2,1,109],[2,19,100,9,1,108,110],[9,1,16,2,20,105],[2,1,16,3,111,105],[15,6,106,21,8,112,108]]),
([w0,w1,w133,w2,w3,w30,w38],[144,88,0,262,239,132,166,159,204,129,25,143,318],[],[[0,1],[2,0,3],[1,0],[0,4],[4,1],[0,4],[5],[4,6],[7,1],[0,8],[9,1],[3,6,4],[3,1,7],[10,0,11],[3,1,7],[1,4,6],[4,0,8],[1,4,12],[0,1,11],[6,7,11],[0,1,6]]),
([w0,w1,w2,w3,w30,w134,w38],[144,88,239,166,132,108,358,129,204,14],[],[[0,1],[1,0],[0,2],[2,1],[2,0],[0,2],[2,3],[4,1,5],[0,4,5],[5,4],[6,1,7],[1,2,3],[2,0,8],[2,3],[1,2,6],[0,1,6],[6,1],[3,5],[9],[0,1,3],[5,1]]),
([w135,w0,w1,w2,w3,w30,w38],[0,144,88,132,139,25,246,96,204,129,196,330,352,166,126],[],[[0,1,2],[3],[4,5,6],[2,7],[5,1,8],[2,9],[1,2],[2,1],[1,10,11],[7,2],[1,8,12],[9,13],[7,2],[1,8],[9,2],[2,7],[8,1],[2,14,11],[1,2,7],[7,14],[1,2,9]]),
([w136,w0,w1,w2,w3,w30,w38],[0,144,239,11,132,352,25,160,175,14,108,358,204,141,166,129],[],[[0,1,2],[3,4,5],[2,6,7],[8],[6,1,9],[5,3,4],[1,10,4],[11,1,10],[1,2],[2,12,13],[1,2],[2,14],[4,10],[1,4,5],[11,12,15],[14,2],[2,1,12],[4,2,11],[1,13],[4,10],[1,4,5]]),
([w0,w1,w137,w2,w3,w30,w38],[201,108,88,137,196,14,204,129,164,36,199,171],[],[[0,1],[0,2,3],[0,1],[0,4],[5,2,6],[5,1],[5],[5,0,7],[8,1,2],[0,6,8],[0,2,7],[0,8],[9,2,10],[0,6,8],[0,1,8],[2,1,7],[0,11],[0,8],[0,2],[0,1,6],[1,2]]),
([w0,w1,w2,w3,w138,w30,w38],[175,108,196,16,20,14,143,166,132,51,171,239],[92],[[0,1],[0,1],[0,2],[0,3,4],[5,6],[5,1],[5,7,6],[8,1],[8,1],[0,8],[0,2,6],[2,0,7],[0,9],[0,10],[0,11],[5],[0,6,100],[0,1,7],[0,6],[0,1,8],[1,8]]),
([w60,w50,w0,w1,w2,w3,w38],[14,204,68,376,108,144,132,129,389,390,171,182,25],[92,93],[[0,1],[2,1],[3,1,4],[1,2],[1,100,3],[3,4],[0,101,5],[6,4],[0,4,7],[8],[1,4],[3,4],[9,4],[3,5],[3,1],[3,10,7],[6,4],[7,1],[3,4,7],[1,11,12],[1,4]]),
([w139,w0,w1,w2,w3,w30,w38],[88,108,132,175,51,160,36,177,196,141,204,166,129,144],[],[[0],[1,2],[3],[4,3,5],[3,6],[1,2],[2,1],[7,1],[7,8],[9,10],[2,1],[2,11,12],[2,1],[1,2],[7,8,12],[8,1,7],[1,13,9],[2,7],[7,9,10],[2,1],[1,2]]),
([w106,w1,w2,w5,w3,w30,w38],[132,108,14,144,65,68,166,129,204,25,36,196,239,143],[93],[[0,1],[2,1,3],[2,3],[3,2],[2,4,5],[0,1],[0,6,7],[0,1],[0,1],[1,0],[7,6],[5],[6,1],[1,3,8],[0,9],[10,11,12],[9,3,100],[0,1],[3,13],[0,1],[1,0]]),
([w0,w1,w2,w140,w3,w30,w38],[132,108,175,262,196,239,204,19,166,129,144,154,143],[],[[0,1],[2,1],[3],[2,4],[5,6,7],[0,1],[0,8,5],[0,1],[0,1],[1,0],[2,4,9],[7],[4,1,7],[1,10,6],[0,5,2],[2,11],[2,6],[0,1],[2,12,6],[0,1],[1,0]]),
([w1,w2,w6,w9,w30,w31,w38],[143,200,132,108,196,88,51,204,175,239,47,36],[],[[0,1,2],[2,3],[2,1],[0,2,1],[1,2],[0,4],[5,0,1],[6],[3,7],[8,0],[2,9,8],[5,1],[1,0,5],[1,5],[1,0,2],[4,0,7],[8,4],[2,0],[10],[3,2],[11,0,9]]),
([w45,w1,w2,w6,w30,w31,w38],[132,196,11,47,160,99,204,25,166,321,177,129,88,171,182,51,352],[],[[0,1,2],[3],[4],[1,5,6],[7,1],[0,2,5],[0,8,9],[0,5],[9,0,6],[9,0,10],[10,1,11],[12,8,10],[5,13,8],[10,8],[0,14,9],[10,5,12],[9,10],[0,1],[15],[1,0],[9,0,16]]),
([w18,w1,w2,w3,w30,w31,w38],[321,88,47,25,196,171,352,200,96,204,182,177,99,51],[],[[0,1],[2],[0,2],[3,1],[3,0],[0,4,5],[6,5,7],[6,4,8],[6,9,10],[6,10],[7,4,10],[4,7],[9,5,11],[11,5],[4,10,11],[4,12,9],[7,4],[5,12],[13],[4,5],[6,4]]),
([w1,w2,w3,w6,w31,w33,w38],[352,171,106,196,99,182,88,25,204,19],[],[[0,1,2],[0,3,4],[0,4],[0,4],[0,2],[2,1,5],[1,3],[1,6],[7,1],[7],[0,5,7],[7],[2,3,7],[3,4,8],[0,4],[2,6,7],[9,4],[0,3],[7,2,4],[0,1],[0,1]]),
([w1,w2,w3,w6,w30,w31,w47],[352,196,99,204,182,129,239,25,88,58,171],[8],[[0,100],[0,1,2],[0,2],[0,3,4],[0,2],[5,1],[1,6,4],[4,6],[2,4,6],[7,4],[7],[7],[1,2,3],[7,1],[0,2],[7,2,8],[7,6,8],[0,1],[9],[0,10],[0,1]]),
([w0,w1,w7,w6,w9,w30,w38],[212,239,108,36,196,204,391,106,143,19,202,171],[],[[0,1],[0,2],[3],[0,1,4],[0,5],[0,1,3],[6],[3,7],[3,4],[3,5],[7,4,8],[9,1],[3],[1,5,10],[3,1],[0,4],[7,5],[3,4,11],[4,7,5],[3,8,5],[3,11,4]]),
([w21,w0,w1,w2,w6,w30,w38],[0,196,215,100,171,239,204,143,108,106,36],[],[[0,1],[2,1,3],[1,4,5],[0,1],[1,6,7],[7,4],[5,8,9],[4,7],[10],[5,6,9],[4,1],[5,4],[9,8],[7,6],[7,1],[4,5],[5,4],[1,5,10],[9,6],[4,1],[1,4]]),
([w0,w1,w2,w141,w3,w30,w38],[239,88,318,19,106,352,96,204,143],[],[[0,1],[1,2,3],[1,0],[2,0],[0,1],[2,0],[0,4,5],[2,4,5],[3,1,6],[2,7],[4,1,8],[3],[1,0,2],[0,4,7],[1,0,2],[1,6],[7,4],[1,8],[2,1,6],[3,8],[2,1,5]]),
([w0,w1,w2,w3,w30,w142,w38],[239,88,143,171,321,241,19,130,182,352,166,70],[],[[0,1],[1,2,3],[4,0],[0,1],[4,5],[3,0,2],[0,3],[6,1,7],[2,8,9],[4,8,9],[2,1],[1,0,3],[0,3],[10,0],[1,0,4],[4,1,2],[4,1,11],[3,2],[6],[4,1,7],[4,1,7]]),
([w17,w0,w1,w2,w9,w30,w38],[47,36,392,19,239,159,143,88,196,106,352,204],[],[[0,1],[2],[3,4],[3,0,5],[3,6],[1,6,3],[1,7],[3,6],[3,4,8],[3,6],[1,4],[1,9,10],[1,7],[1,11],[6,7],[1],[4,9,11],[1,4],[8,6,7],[1,5],[1,7,8]]),
([w0,w1,w2,w6,w32,w34,w38],[251,239,143,36,204,171,88,393,166,19,130],[],[[0,1],[0,2],[3],[0,2],[0,1,4],[0,1,2],[1,5],[3,6],[7],[3,4],[2,4],[5,1],[1,5],[4,1,8],[3,1],[9,2],[0,4],[3,2,5],[3],[3,4,10],[3,2,8]]),
([w78,w0,w1,w2,w6,w30,w38],[0,196,215,100,166,143,204,36,108,182,254,239,96],[57],[[0,1],[2,1,3],[1,4,5],[0,1],[1,6,5],[5,4],[7,8,9],[9,4],[7],[10,5],[7,1,11],[5,4],[7,8,9],[5,6],[5,1],[9,4],[4,9],[1,9,7],[12,5,100],[7,1,10],[1,10,7]]),
([w62,w0,w1,w2,w3,w32,w38],[39,36,204,166,394,88,333,239,189,395,25,182],[57],[[0,1],[1,2],[2,3,4],[1,0],[1,2],[1,3,4],[4,5,6],[4,3],[6,7],[4,5,7],[4,2],[6,3],[4,5,8],[9],[10,2,11],[3,7],[7,3],[2,7,6],[4,5,100],[2,8,10],[6,2,8]]),
([w0,w1,w6,w9,w30,w33,w38],[264,108,228,239,196,182,126,352,175,106,19,362,171],[],[[0,1],[2],[0,3,4],[0,3],[0,1],[0,1],[5,1],[6,1,4],[1,5],[3,5,7],[8,4,5],[0,4],[8,9],[10,1],[7,1],[4,5],[4,1,2],[7,1],[11],[1,12],[4,3,8]]),
([w0,w1,w2,w9,w30,w61,w38],[266,108,239,196,204,209,200,352,143,380,14,175,381,88],[],[[0,1],[0,1],[0,2,3],[0,4],[5],[0,1],[2,6,7],[7,1],[1,4,8],[7,1],[6,3,8],[9],[1,4],[10,1,6],[3,2,11],[3,8,4],[10,3,6],[4,1],[12],[1,13],[6,1,7]]),
([w62,w0,w1,w2,w9,w30,w38],[47,239,36,108,352,14,19,196,266,88,200,132,288,106,175],[],[[0,1,2],[2,3,4],[5,1,6],[6,0,7],[8],[2,3,4],[1,3,4],[6,3],[6,1,7],[1,9],[4,1,3],[1,10,4],[4,3],[3,11],[10,7,12],[6],[1,13],[4,1,14],[7,9],[4,3],[3,9]]),
([w0,w1,w2,w6,w30,w82,w38],[239,108,352,175,228,143,106,196,182,177,204,132],[],[[0,1,2],[3,1],[4],[0,5,6],[3,0,7],[2,0,1],[0,6,2],[2,1],[1,8],[2,1],[3,7,5],[8,0],[0,6,8],[9],[2,0,3],[3,5,6],[3,7],[2,1],[10],[1,11],[2,1]]),
([w83,w0,w1,w2,w6,w30,w38],[0,239,196,36,68,62,106,11,108,175,223,204,352,200,182,88,132],[],[[0,1,2],[3,2],[2,1,3],[4,2,5],[6],[3,7],[1,8,9],[9,8],[10],[1,11],[12,1,2],[1,13,12],[12,8],[8,11,14],[9,2,14],[14,1],[1,14],[2,1,9],[9,11,15],[9,2,12],[2,16]]),
([w0,w1,w2,w6,w30,w87,w38],[36,99,177,166,19,196,182,132],[],[[0,1,2],[2,3],[0],[4,1],[2,5],[0,1,4],[0,3],[0,1,4],[0,6,2],[0,1,5],[2,3,6],[4,3],[1,6,2],[2,6],[0,6],[2,1,4],[2,4],[0,1,4],[0],[0,7,3],[0,1,3]]),
([w45,w0,w1,w2,w30,w61,w38],[65,196,132,99,396,321,364,276,166,241,177,352,182,14,397],[],[[0,1],[2,1,3],[4],[1,3,5],[6],[2,3],[2,3],[7,8],[7,3],[9],[2,1],[2,8,5],[5,2,10],[5,2,11],[10,1,12],[3,12,8],[13,8,10],[1,12,5],[14],[1,2],[5,1,11]]),
([w130,w0,w1,w2,w3,w6,w38],[0,99,36,204,166,182,68,62,132,239,196,144,106,337,175],[24],[[0,1],[2,3],[1,4,5],[2,1],[6,1,7],[2,4,8],[5,1],[5,4],[100,9,10],[11],[8,1],[1,4,9],[5,1],[5,1],[12,3,5],[4,9],[5,4],[1,5,13],[14],[3,1],[8,1]]),
([w0,w1,w143,w2,w3,w30,w38],[323,99,88,166,196,179,19,204,202,25,144,96],[],[[0,1,2],[0,2],[2,3,0],[0,4,5],[5,1],[0,1,6],[6],[0,3],[5,1,2],[0,7],[8,2],[0,3],[0,2,5],[9,1,10],[0,1,5],[0,11,2],[1,10],[0,5],[0,1],[3,1],[0,2,3]]),
([w0,w1,w2,w3,w30,w144,w38],[182,99,96,88,177,196,132,200,144,11],[],[[0,1],[0,2,3],[4,5],[2,1,3],[2,3],[2,1,6],[1,7],[0,1],[4,0],[7,0],[4,0],[0,2,3],[1,0,4],[4,0],[1,0,4],[2,1,3],[2,3],[2,1,6],[8],[5,3],[4,1,9]]),
([w18,w0,w1,w2,w30,w34,w38],[65,36,99,182,396,25,88,51,364,132,96,288,276,196,200,177,397,179],[],[[0,1],[1,2,3],[4],[5,2,6],[7,0,8],[1,2,9],[3,2],[3,10,11],[10,2,12],[7,11,13],[9,2],[2,14],[11,3],[10,2,13],[14,3],[2,3,15],[13,3,10],[2,3,15],[16],[13,9],[10,2,17]]),
([w0,w1,w2,w6,w33,w34,w38],[282,99,288,228,196,106,126,182,88,398,25,19,132],[],[[0,1],[0,2],[3],[0,1],[0,2,4],[0,1],[1,5],[5,1],[2,5],[6,1,4],[5,2],[7,8],[9],[4,5],[1,7,10],[11,1],[0,4],[10,1,12],[4,1,3],[4,12],[5,1,6]]),
([w0,w1,w2,w3,w33,w61,w38],[282,99,88,196,209,106,130,288,126,352,182,398,14,25],[],[[0,1],[0,2],[0,3],[0,1],[4],[0,1],[1,5],[5,1],[6,5,7],[8,1,9],[5,2,7],[2,10],[11],[12,5],[1,10,13],[3,1,2],[13],[9,1],[12,1,5],[3,2],[5,1,8]]),
([w0,w1,w2,w6,w30,w34,w47],[296,99,288,36,196,182,11,143,239,25,88,132,352],[8],[[0,1],[0,2],[3],[0,1],[0,2,4],[0,1],[1,100],[5,1],[2,5],[6,1,4],[7,2,4],[5,8],[1,5,8],[4,5],[3],[9,0,10],[0,4],[11,1],[3],[4,11],[12,1]]),
([w50,w0,w1,w2,w6,w30,w47],[58,196,11,239,182,373,374,132,108,197,288,36,204,297,106],[],[[0,1],[2,1],[1,3,4],[5],[6],[7,2,8],[3,9,4],[4,10],[11],[3,12,13],[7,1],[3,14,7],[4,9],[9,4],[11,1],[4,3],[3,4],[11],[14,12],[7,1],[1,7]]),
([w0,w1,w2,w3,w30,w61,w47],[296,88,239,196,209,132,288,36,352,143,182,14,399,400,372],[8],[[0,1,2],[0,1],[0,2,3],[0,1,2],[4],[0,2,3],[2,100,5],[5,1,6],[6,5],[7,5,8],[9,1],[1,2,10],[2,10],[11,2],[12],[3,0,1],[13],[5,9],[14],[3,1],[8,1]]),
([w62,w0,w1,w2,w3,w30,w47],[58,288,36,132,182,239,374,196,88,297,106,129,401,189,108],[],[[0,1,2],[2,1,3],[4,5],[2,0],[6],[3,7],[3,8,5],[1,4],[9,1,7],[1,8],[3,1,7],[1,10],[3,1],[1,3],[11,1,7],[4,5],[5,4],[12],[7,8],[3,13,14],[7,3]]),
([w37,w1,w2,w3,w6,w30,w38],[36,132,108,182,65,70,166,241,25,19],[],[[0,1,2],[2,3],[0,4,5],[0,4,5],[4,0],[0,1,2],[1,6,7],[1,2],[1,2],[2,1],[8,3],[3,2],[3,2],[2,3],[1,3,7],[4],[7,4,8],[1,2],[8,4,9],[1,2],[2,1]]),
([w37,w1,w2,w6,w30,w34,w38],[36,182,108,65,25,132,166,239,352,88,241],[],[[0,1,2],[2,1],[0,3,4],[3,0],[3],[0,5,2],[5,6,7],[1,2],[2,1],[8,1],[4,1],[1,2],[2,1],[6,1],[4,1],[4,3,9],[3,4],[4,2,5],[10],[2,5],[4,2,6]]),
([w103,w0,w1,w2,w6,w30,w38],[0,288,196,36,182,51,160,132,352,99,166,177,232,106,88],[],[[0,1,2],[3,1,2],[4],[5,2,6],[2,3],[3,7,8],[7,9],[1,10,11],[12],[1,9,13],[7,1,2],[1,10,13],[7,1],[1,7],[11,1],[14,10,11],[9,13],[2,11],[11,9,13],[7,2],[2,7]]),
([w0,w1,w2,w107,w6,w30,w38],[36,108,132,175,196,106,204,288,88,19,239],[],[[0,1,2],[3,1],[3,4],[0],[5,6],[0,1,2],[0,5,2],[0,1,2],[0,1,2],[0,2,1],[3,4,7],[0],[8,1,9],[1,5,6],[0,10],[3,4],[3,5,6],[0,1,2],[3,6,5],[0,1,2],[0,2,1]]),
([w37,w1,w2,w3,w30,w61,w38],[321,132,88,182,108,65,25,166,239,241,352,209,165,19],[],[[0,1,2],[2,3,4],[0,5,6],[5,0],[0],[0,1,4],[1,7,8],[1,2,4],[4,1],[9,1,10],[6,2,3],[2,4,3],[4,3],[11,3,12],[1,3,6],[6,2],[6],[1,4],[13],[4,1],[6,1,10]]),
([w145,w0,w1,w2,w3,w30,w38],[0,321,241,132,166,239,25,333,11,88,173,352,130,204,143,171],[],[[0,1,2],[3],[4,5],[1,6],[1,7],[1,8],[1,9],[9,4,10],[1,5],[5,1,9],[1,4,5],[1,4],[11,9,12],[1,13],[10,4,14],[1,5],[4,15],[1,5],[1,9,10],[4,12,10],[1,9,4]]),
([w146,w0,w1,w2,w3,w30,w38],[0,88,209,36,132,352,175,204,19,99,165,288,200,106,177],[],[[0,1,2],[3,4,5],[6],[3,1,6],[6,7,8],[3,1,5],[4,1,9],[1,10],[10,11],[10,1],[4,7],[4,10],[4,1,9],[5,4],[10,1,11],[1,12],[7,13],[1,14],[7,1,9],[4,9],[5,1]]),
([w0,w1,w147,w2,w3,w30,w38],[333,88,166,203,288,173,19,204,14,229,215,11,239,189],[],[[0,1],[0,1],[1,2,3],[0,4],[4,1],[0,2,4],[5],[0,2],[6,1,4],[0,7],[3,1,4],[8,2,9],[0,1,10],[0,7],[0,1,11],[0,12],[2,9],[0,9],[0,1,3],[2,13,3],[0,1,2]]),
([w0,w1,w2,w148,w3,w30,w38],[175,88,239,166,165,36,352,288,132,177,106,108],[94],[[0,1,2],[0,3],[0,2,1],[0,2,4],[2,1],[4,2],[2,3],[5,4,6],[4,1,7],[0,8],[0,1,7],[9],[1,0,3],[0,10,100],[0,2],[0,1],[0,10],[0,3,1],[0,1],[0,11,3],[3,1]]),
([w125,w62,w0,w1,w2,w3,w38],[106,204,88,333,288,402,189,403,162,164,223,99,390,196,182,25],[95,8,96,94],[[0,1],[0,100,2],[3,101,4],[5],[0,102,2],[0,6],[2,1,4],[0,1,4],[1,103,7],[1,8],[2,9,10],[0,2,11],[2,7],[12,4,13],[7,1],[4,0],[0,2,4],[0,1,4],[2,7],[1,14,15],[1,11]]),
([w0,w1,w63,w3,w30,w33,w38],[264,197,288,209,196,229,106,182,25,404,36,175,132,362],[],[[0,1],[0,2,3],[0,4],[0,5,3],[0,5,3],[0,1],[1,6],[3,1],[1,7],[1,6],[6,3],[0,4],[8,5],[8,5],[1,5,8],[4,6],[4,9,10],[11,1,12],[13],[1,12],[1,12]]),
([w0,w1,w2,w3,w30,w149,w38],[228,88,165,196,175,209,197,182,177,132,223],[],[[0,1],[1,2],[0,3,4],[2,1],[4,1,5],[0,3,5],[0,2,5],[2,1,6],[0,7,2],[0,2,5],[2,1,5],[0,4,1],[4,0,7],[8],[0,7],[0,1,3],[0,1,3],[4,6,9],[10],[0,1,3],[0,1,3]]),
([w0,w1,w2,w63,w30,w34,w38],[266,197,165,209,99,196,132,380,175,200,205,405,130,381,123],[],[[0,1],[0,2,3],[0,2,3],[0,4],[0,5],[0,1],[1,2],[1,2],[1,6],[2,1],[2,3],[7],[4,8],[5,8,9],[1,10,8],[4,11,8],[5,8],[1,12,8],[13],[1,6],[8,1,14]]),
([w0,w1,w2,w9,w30,w64,w38],[266,88,36,165,196,132,209,175,141,108,14,205],[],[[0,1,2],[0,3,1],[0,3,4],[0,1,3],[0,1,3],[0,4],[2,3,5],[2,1],[2,5,3],[2,5,3],[3,1,6],[2],[7,8],[9,7,10],[1,11,2],[4,1],[4,1],[2,9,5],[2],[2,1,4],[2,1,4]]),
([w0,w1,w2,w3,w64,w33,w38],[406,88,228,165,196,209,197,132,14,106,398,182],[],[[0,1,2],[0,3,1],[0,4],[0,1,3],[0,1,5],[0,4],[2,3,5],[3,1,6],[2,7,3],[2,3,5],[3,1,5],[1,2],[8,2,9],[10],[1,11,2],[0,4],[2,1,4],[7,6],[2,8],[2,1,4],[2,1,4]]),
([w150,w0,w1,w2,w3,w30,w38],[0,88,209,132,228,196,56,268,232,165,177,197,108,106,141],[],[[0,1,2],[2,3],[4],[4,1,5],[6,4,7],[4,1,5],[3,1,8],[1,9],[2,5,10],[2,1],[3,2,5],[2,9],[2,1,11],[2,3],[9,1,2],[1,12,8],[10,13,14],[1,8],[5,1],[3,11],[5,1]]),
([w0,w1,w2,w3,w30,w64,w47],[296,197,165,209,196,88,132,36,205,182,14],[],[[0,1],[0,2,3],[0,4],[0,5,2],[0,5,2],[0,1],[1,2],[2,1],[1,6],[1,6],[7,2,4],[4,8,7],[8,9],[10,8],[7],[4,0,5],[0,4],[6,1],[7],[1,5],[1,5]]),
([w0,w1,w2,w3,w30,w33,w65],[407,197,165,209,196,229,132,312,25,228,270,408],[],[[0,1],[0,2,3],[0,4],[0,5,2],[0,2,3],[0,1],[1,2],[2,1],[1,6],[1,2],[2,3],[4,7],[8,5],[8],[1,5,9],[4,10],[4,7],[0,1],[11],[1,6],[1,6]]),
([w39,w0,w1,w9,w30,w33,w38],[288,209,205,361,228,175,312,197,196,229,132,362],[],[[0],[1,2],[3],[4,5],[4,2],[5,6],[2,7],[1,8,3],[1,9],[1,9],[4,1],[1,2],[1,10],[1,10],[5,1],[5,4,9],[4,2],[4,7,9],[11],[4,10,7],[4,2]]),
([w39,w0,w1,w2,w30,w82,w38],[288,209,205,228,405,175,358,312,197,165,229,132,177,223,11],[],[[0],[1,2],[3,2],[3,4,5],[6],[5,7],[2,8],[1,9],[1,10],[1,9],[3,1],[1,9],[1,11],[1,2],[5,1],[2,3,10],[12],[3,2],[13],[3,11,8],[3,8,14]]),
([w39,w0,w1,w2,w33,w34,w38],[288,209,88,141,228,367,25,270,197,165,229,196,106,132,126],[],[[0],[1,2,3],[2,4],[4,2,3],[5],[6,7],[3,8],[1,9],[1,9],[1,10],[4,1],[1,9],[1,9],[1,3],[3,1],[6],[11,4,12],[4,10],[4,3],[3,13,8],[4,8,14]]),
([w0,w151,w1,w2,w3,w30],[11,229,199,181,36,9,165,49,141,293,132,358],[0,34,24,6,8,16,27,28,13,54],[[0,1,100,2,3],[0,4,101,5],[0,6,100,2,7],[0,4,102],[0,1,103,6],[0,6,104,8,9],[3,4],[0],[3,8,9,10,105],[0,6,104,7],[0,4,106],[0,10,107,6,104],[1,2,4,7,108],[7,1,105,11],[4,2,109,11,106]]),
([w39,w0,w1,w2,w30,w34,w47],[288,197,141,36,205,400,130,199,165,209,229,65,132,196,352],[],[[0],[1,2],[3,4],[3,2],[5],[1,6,7],[2,1],[4,8,9],[2,10,8],[5,10,8],[11,1],[1,8],[1,12],[3,1,8],[2,4],[2,10,4],[13,4],[3],[3],[1,6,2],[14,1]]),
([w103,w39,w0,w1,w2,w30,w38],[51,25,160,196,36,228,197,11,288,141,232,312,199,177,165,209,99,132,106],[],[[0,1,2],[0,3],[4,3],[5],[1,4],[1,6,7],[8],[6,9],[10,11,12],[10,9],[3,11,12],[9,6],[13,14,15],[9,16],[10,3,15],[6,14],[6,17],[9,3,15],[9,18],[3,10],[3,17]]),
([w73,w1,w2,w3,w30,w31,w38],[0,33,37,199,108,182,25,132,166,321,173,99,196,11],[],[[0,1,2],[3,4,5],[2,3],[6,3],[6,3],[3,4,7],[7,8,9],[5,4],[4,5],[9,4,10],[10,5],[5,4],[4,5],[10,4],[7,5,9],[9,11],[9,12,10],[7,4],[2],[4,7],[9,4,13]]),
([w0,w1,w2,w3,w30,w152,w38],[173,197,108,196,130,321,99,241,132,166,182,14,185,333],[],[[0,1],[0,2],[0,3],[4,5,6],[7],[5,1,8],[1,9,4],[4,1,0],[0,8],[0,1],[0,3,10],[3,2,5],[0,10],[11,2,12],[0,4],[0,4,5],[0,3],[0,1,4],[13],[1,4,5],[0,1,4]]),
([w0,w1,w3,w9,w31,w33,w38],[264,197,229,190,165,99,175,182,361,228,321,352],[],[[0,1],[0,2],[0,3],[4],[0,2,5],[0,1],[3,1],[2,1,3],[6,1],[1,3],[6,7],[8],[6,9],[10,5],[3,1],[6,2],[6,2],[3,1],[0,5],[9,1,11],[1,3]]),
([w86,w1,w2,w3,w30,w31,w38],[321,197,182,47,25,229,166,177,108,99,196,51,132,352],[],[[0,1,2],[2,3],[0,3],[4,0,5],[0,4],[0,1,5],[0,6],[2,1],[0,2,1],[0,1,7],[7,2],[0,8],[6,2],[7,2],[0,2],[0,9],[0,10,7],[6,1],[11],[0,12,1],[0,1,13]]),
([w0,w1,w2,w3,w30,w153,w38],[177,197,166,196,141,99,241,321,132,352,182,108,333],[],[[0,1],[0,2],[0,3],[4,5],[6],[7,1,8],[1,2,7],[8,1],[0,8],[6,1,9],[0,2,10],[2,11],[0,10],[0,2],[0,10],[0,4,7],[0,3],[0,1,2],[12],[1,8],[0,1,9]]),
([w0,w66,w2,w7,w3,w30,w38],[30,199,181,166,409,165,88,14,96,410,325,171,11,201,182],[18],[[0,1,2],[2,3,4],[2,5],[4,2,5],[2,6],[4,3],[7,3,5],[7,5],[5,6,8],[0,4,9],[2,3],[10],[3,8,6],[3,11],[2,12,13],[14,6,100],[13,14],[2,3],[8,6],[3,2],[2,6]]),
([w0,w66,w2,w3,w8,w30,w38],[33,321,241,411,166,196,88,99,239,11,182,25],[],[[0,1,2],[3,4],[2,5,3],[2,6],[3,6,2],[2,4,3],[7,4,8],[1,5,7],[1,7],[0,1],[1,4,9],[2,8],[2,4],[4,10],[2,8],[9],[2,6,5],[4,7],[2,7],[11,4,9],[2,6,4]]),
([w0,w1,w2,w154,w3,w30,w38],[201,88,181,166,196,132,126,330,247,96,182,36,223],[],[[0,1,2],[0,3],[0,1,2],[0,2,4],[2,1],[5,3],[5,0,6],[7],[5,1,6],[0,5],[0,1,2],[8],[1,9],[0,6,10],[0,6],[11,1],[0,6,12],[0,1,2],[0,1],[0,2,3],[2,1]]),
([w0,w1,w2,w3,w155,w30,w38],[241,88,166,203,196,130,132,173,182,108,14,129,253],[],[[0,1],[1,2,3],[0,4,3],[0,1],[5,1,0],[0,2,6],[0,2],[5,1],[7],[0,6,3],[3,1,8],[0,9],[10,2,11],[2,8],[0,5],[12],[0,1,3],[2,5,3],[0,3],[0,1,5],[0,1,2]]),
([w0,w1,w66,w2,w3,w33,w38],[243,88,96,196,181,334,126,171,327,204,14,106,412,25],[],[[0,1,2],[0,1,2],[0,2,1],[0,3],[0,1,4],[0,3],[5],[6,7],[2,1],[6,8,9],[4,1],[10,6,11],[2,1],[6,9],[4,1],[1,2],[12],[1,6,13],[3,1],[2,4,6],[3,1]]),
([w0,w1,w67,w3,w9,w30,w38],[363,108,181,165,209,99,182,36,123,361,175,106,132],[],[[0,1],[0,1],[0,2,3],[0,2,4],[0,5],[0,1],[4,3],[3,1],[4,1],[1,6],[2,4,3],[7,1],[7,1],[0,5],[2,8,7],[9],[10,5,11],[10,1,12],[10,5,6],[10,1,6],[1,12]]),
([w0,w1,w2,w3,w156,w30,w38],[175,108,181,165,209,99,106,182,177,358,132,223,11],[],[[0,1],[0,1],[0,2,3],[0,2,4],[2,5,6],[3,1,4],[4,3],[3,1],[4,1],[0,7],[0,4],[7,0,1],[8],[0,6,5],[0,7],[9],[0,5,6],[0,1,10],[0,5,11],[0,1,12],[1,10]]),
([w157,w0,w1,w2,w3,w30,w38],[0,321,241,203,14,239,171,11,88,165,130,204,181,173],[],[[0,1,2],[3],[4,5,6],[1,3],[2,3],[1,7],[2,8],[6,9,8],[2,5],[5,8],[2,5],[2,6],[9,8,10],[2,11],[9,6,12],[2,5],[5,6],[2,5],[2,8,13],[6,10,12],[2,6,10]]),
([w0,w1,w2,w68,w9,w30,w38],[396,99,165,181,209,132,14,404,96,380,175,239,381,123,204],[],[[0,1],[0,2,3],[0,3,2],[0,2,4],[0,1],[0,1],[1,2],[2,1],[4,1],[2,5],[2,4],[6,7,8],[9],[1,10],[1,11,10],[6,7,8],[0,12],[8,1,13],[10,1,14],[5,1],[3,5]]),
([w45,w0,w1,w2,w68,w30,w38],[65,181,165,99,396,364,204,276,132,14,96,182,177],[],[[0,1,2],[2,3],[4],[5],[5,3,6],[5,1,6],[1,3,7],[1,2],[2,1],[1,3,7],[2,3,7],[3,2],[2,3],[2,6,8],[1,6],[9,10],[3,11,12],[1,11,12],[6,3],[6,1],[1,8]]),
([w158,w0,w1,w2,w3,w30,w38],[0,181,96,165,132,175,160,99,204,106,166,146,177],[],[[0,1,2],[3,4],[5],[2,5,6],[5,7,8],[5,1,8],[1,7,4],[1,2],[3,1],[1,7,9],[2,7,4],[4,3],[2,7,3],[3,4],[1,8],[10,2,11],[7,9],[1,12],[2,7,8],[2,1,4],[1,4]]),
([w0,w1,w2,w3,w68,w33,w38],[406,99,165,181,130,204,182,146,14,106,398,25],[],[[0,1],[0,2,3],[0,3,2],[0,3,2],[0,1],[0,1],[1,2],[2,1],[2,1],[4,2,5],[2,5,3],[6,7],[8,6,9],[10],[1,6,11],[11],[5,1],[5,1],[5,1],[5,1],[3,4,7]]),
([w0,w1,w2,w3,w68,w30,w47],[296,99,165,181,204,182,239,14,399,400,130,132],[],[[0,1],[0,2,3],[0,3,2],[0,3,2],[0,1],[0,1],[1,2],[2,1],[2,1],[2,4,5],[3,2,4],[5,6],[7,5],[1,5,6],[8],[9],[4,0,1],[4,1],[0,4],[4,1],[3,10,11]]),
([w159,w0,w1,w2,w3,w30,w38],[0,181,165,203,14,182,166,173,413,130,204,132,196,239],[],[[0,1,2],[2,3],[4,5,6],[7,8],[0,9,10],[3,1,6],[1,5],[1,2],[2,1],[1,10,9],[2,6,11],[9,2,6],[2,12,9],[2,5],[1,5,2],[5,13],[6,5],[1,5,7],[7,9,10],[6,1],[1,9,11]]),
([w40,w0,w1,w3,w9,w33,w38],[229,175,182,106,362,132,204,99,239,165,209,361],[],[[0],[1,2],[1,3],[1,2],[4],[3,5,6],[1,7],[1,8,9],[1,8,10],[1,6],[5,6],[2,7],[5,3],[8,2,6],[1,2],[11],[6,1,7],[1,7,5],[1,2],[1,2],[1,5,8]]),
([w160,w0,w1,w2,w3,w30,w38],[0,181,165,182,268,177,364,99,204,141,132,96,146],[],[[0,1,2],[2,3],[4,3,5],[5,6],[0,7,8],[5,1,8],[1,7,3],[1,2],[2,1],[1,7,9],[2,7,10],[7,2],[2,7],[2,3],[1,3,2],[3,11,12],[5,3],[1,3,5],[5,7,8],[5,1,8],[1,10]]),
([w0,w1,w2,w3,w161,w30,w38],[239,99,106,181,166,123,262,132,204,159],[],[[0,1,2],[3,4,5],[5,0,6],[5,0,6],[0,1,2],[6,0],[0,2,1],[2,1],[5,1,7],[5,8],[2,4,3],[4,0],[4,0],[0,2,1],[1,0,6],[9],[2,1],[4,1],[8,1],[4,1],[2,5]]),
([w0,w1,w2,w3,w30,w162,w38],[132,88,181,166,126,196,201,330,108,182,204],[],[[0,1,2],[1,3,4],[4,2,5],[2,1],[2,1],[0,3],[0,3,4],[0,1,4],[4,0,6],[4,0,7],[2,1],[1,8,3],[3,4,9],[3,4],[0,4,6],[5,1],[5,1],[0,2],[10],[2,0],[2,0]]),
([w19,w0,w2,w3,w30,w32,w38],[88,39,409,325,132,200,196,25,11,166,204,99,171,201,146,106],[],[[0],[1,2,3],[4,5,6],[7,4],[7,4],[6,8,7],[2,9],[2,6],[2,10],[2,11],[2,6],[6,5],[9,12],[11,5],[4,8,13],[5,14],[15,6,11],[4,8,5],[8],[6,4],[5,4,8]]),
([w0,w7,w8,w9,w30,w38],[181,227,88,99,108,36,212,49,210,166,131,414,106,202,205,415,200,312,416,338,11],[1,0,7,43,11,6,48],[[0,1,2,3,4],[5,100,6],[7,8,0,9,10],[0,11,101,2,3,100],[5,3,102,11,103],[5,12,4,7],[5],[4,13,12,104,105],[5,2,14,0],[5,12,10,7],[5,104,15],[5,16,17],[9,7,18,2,3,19],[5,0,20,7],[5,2,106,0,102]]),
([w0,w7,w3,w8,w30,w47],[11,88,181,36,210,166,205,31,106,182,196,201,171],[0,35,24,1,11,6,72,27],[[0,1,100,2,101],[0,2,102,3],[0,1,103,3],[0,1,103,2,100],[0,4,5],[3,1,6,7],[3,8,6,7],[6,7,9,8,104,105],[0,2,3],[0],[3,1,106,10,107],[0,3,107],[3,104,11],[0,3,5],[0,2,5,1,12]]),
([w0,w2,w3,w8,w30,w69,w38],[181,166,171,228,204,106,88,232,182,126,196,99,223],[],[[0,1,2],[3,0],[3,0],[0,4,5],[0,6],[2,1],[1,6],[3,1],[1,2],[7],[0,8,3],[9],[3,6,10],[3,6,11],[1,0],[3,4],[3,5,11],[5,0,8],[12],[0,2],[0,1]]),
([w70,w0,w2,w3,w8,w30,w38],[33,99,36,228,11,182,166,223,196,181,88,171,164,201],[],[[0,1],[1,2],[2,1],[2,1],[3],[2,4],[5,6],[7,8,9],[5,9,7],[9,10],[7,6,11],[5,8],[7,6],[6,5],[7,5],[12],[7,10,8],[6,9],[7,5,13],[13,5],[6,10]]),
([w0,w2,w7,w3,w30,w72,w38],[88,166,171,203,181,36,30,417,49,106,99,182,96],[],[[0,1,2],[3,0,4],[5,4],[4,0],[6,0,7],[2,1],[5],[0,1],[1,2],[8,1,9],[0,5],[5,0,10],[3,11],[8,9],[3,0,4],[5,0,10],[12],[1,4],[5],[1,0],[5,0,7]]),
([w76,w0,w2,w7,w3,w30,w38],[88,166,418,171,25,330,36,146,196,99,409,325,96,11,201,182],[],[[0],[1,2,3],[4,2,5],[6,7,8],[2,6],[1,3],[3,1],[4,9],[7,8],[10,9],[3,1],[11],[1,12,7],[1,3],[7,13,14],[15,8,9],[4,7],[4,1,13],[8,7],[1,9],[1,3]]),
([w0,w7,w3,w9,w30,w32,w38],[419,96,181,36,211,166,204,190,171,205,88,49,106],[],[[0,1,2],[3,2],[4,1,5],[1,6,7],[1,7],[1,5,8],[3,1,9],[3],[9,6,7],[9,7],[2,5],[10],[1,3],[1,3],[1,2,5],[5,8],[11,5,12],[3,2,6],[3],[2,7],[2,5]]),
([w0,w7,w3,w30,w32,w47],[181,420,96,11,36,88,211,166,31,182,205,25,204,106,171,41],[0,38,24,27,18,8,14],[[0,1,2,3,100,101],[3,0,102,4,100],[0,3,5,101,100],[0,3,5,101,100],[3,6,7],[4,8,9,10,2,103,104],[10,8,11,9,12],[11,8,9,13],[3,0,11,4],[2,4,103,5,104],[2,4,105,5,103,106],[3,4,7,0,103],[3],[3,0,7,5,14],[3,0,15,5,7]]),
([w0,w2,w3,w20,w30,w32,w38],[171,166,36,181,39,417,88,96,49,106,205,31,25,204,182],[],[[0,1],[2,3],[4,3,5],[3,6],[3,6],[0,1],[0,7,6],[2],[1,0],[8,0,9],[2,10],[11],[2,6,7],[2,6,7],[0,3],[12,13,14],[8,9],[2,0,5],[2],[1,0],[2,0,3]]),
([w21,w0,w2,w3,w30,w32,w38],[39,165,31,421,36,96,182,25,181,204,190,171,205,199],[],[[0,1,2],[3,4],[5],[2,6,7],[2,1],[2,6,4],[2,1],[1,8],[1,9,10],[8,10],[1,9,11],[2,12,4],[2,11,12],[2,1],[2,12,4],[4,13],[1,12],[9,8],[2],[4,10,8],[1,9,8]]),
([w0,w2,w7,w3,w32,w34,w38],[171,166,251,88,181,36,211,204,49,106,199,31,99,96],[],[[0,1],[2,3,4],[5,4],[4,3],[6,3,7],[0,1],[5],[0,3],[8,0,9],[1,0],[3,5],[5,3,10],[8,9],[11,7],[4,0],[5,3,12],[13],[0,4],[5],[4,0],[1,0]]),
([w51,w0,w2,w7,w3,w32,w38],[211,204,171,166,31,199,36,422,96,181,99,423,196,106],[],[[0,1],[1,2,3],[4,1],[5],[6],[3,2],[2,3],[7,8,9],[6,9],[8,10,11],[2,1],[6],[2,8,12],[10,2,13],[1,6],[6,8],[10,13],[6,1,9],[6,10],[1,9],[6,1,9]]),
([w78,w0,w2,w7,w3,w30,w38],[30,190,96,31,166,106,199,181,171,36,99,253],[],[[0,1,2],[3,4,5],[3,1,5],[6],[5,3],[5,1,7],[1,2],[7,2],[1,7],[2,1],[2,4,8],[9],[4,2],[4,8],[1,9],[1,2,10],[11,1],[7,4],[2,10,9],[1,7],[4,1]]),
([w0,w1,w3,w9,w30,w69,w38],[96,90,181,201,166,171,106,228,190,204,209,31,205],[],[[0,1],[1,2],[3,0,4],[0,1],[2,0],[0,4,5],[0,6],[7,1],[7,8,9],[10],[2,1],[11],[0,6],[7,0,12],[0,2,1],[3,1],[7,12],[3,2,8],[11],[2,1],[2,1]]),
([w70,w0,w1,w3,w9,w30,w38],[47,96,181,424,49,425,31,166,228,90,190,171,165,169,223],[],[[0,1,2],[3,4,5],[4,1,6],[4,7,6],[8],[2,7],[1,9],[9,2],[10,1],[1,9],[1,7,11],[1,10],[6,7],[6,10,12],[2,7],[6],[1,13,14],[1,2,7],[7,9],[10,2],[2,9]]),
([w0,w1,w7,w9,w30,w34,w38],[96,90,266,181,426,166,212,165,171,190,36,205,169,31,130],[],[[0,1],[2,0,3],[4,0,5],[0,1],[6,1,7],[0,5,8],[9],[10,1],[7,10],[0,7],[3,1],[10],[11,12],[13,0],[3,1],[5,1],[5,0,1],[10,3,14],[10],[3,1],[0,1,5]]),
([w0,w1,w7,w3,w20,w30,w47],[96,427,31,181,213,417,428,166,49,196,204,169,202],[],[[0,1],[2,0],[1,3],[4,0,5],[0,1],[6,0,7],[8],[0,9],[8],[2,10],[2,1],[2,0],[8],[2,10],[2,1],[2],[0,11,10],[1,0,3],[12,10],[5,1],[3,1]]),
([w0,w1,w7,w3,w30,w69,w47],[96,427,31,181,418,166,190,196,204,44,199,36],[],[[0,1],[2,0],[1,3],[0,1],[3,0],[4,0,5],[6],[0,7],[2,8],[9],[2,1],[2,0],[2,8],[9],[2,1],[0,10],[11,0],[1,0,3],[2],[3,1],[3,1]]),
([w71,w0,w1,w7,w3,w30,w47],[213,199,96,40,31,166,11,36,427,196,238,44,204],[],[[0,1,2],[3],[3],[2,1],[4],[5,6,7],[1,8],[1,2],[8,9,10],[2,1],[1,2],[11],[1,9],[4,12],[4,5],[1,2],[4,12],[4,5],[2,1],[1,2],[5,8]]),
([w0,w1,w7,w3,w30,w34,w47],[36,427,296,199,181,213,165,67,88,169,182,205,31,96,166],[],[[0,1],[2,1,3],[0,4],[4,1],[5,1,6],[3,6],[7],[3,8],[0,6],[0,6],[0,1],[0,8,3],[9,10,11],[12,10],[0],[0,9],[13],[0,4],[0],[4,1],[14,1]]),
([w51,w0,w1,w7,w3,w30,w47],[213,427,96,36,165,31,182,205,67,166,181,423,71,196,169],[],[[0,1,2],[3,4],[5,6,7],[8],[3],[9,1],[2,1],[6,1,10],[1,10],[2,1],[11,2,9],[12],[2,13],[3,4],[3,1],[3,2,7],[7,6],[3],[2,14,3],[1,2,10],[9,1]]),
([w29,w0,w1,w2,w3,w30,w38],[96,0,205,190,36,31,204,106,11,99,166,262,196,123,171],[],[[0],[1,2,3],[1,2,4],[1,5],[6,7],[4,8],[2,9],[2,10],[11,12,13],[7,6],[11,6,14],[9,7],[7,2],[2,6,11],[7,2],[10,2],[2,7,6],[6,2,11],[6,9],[6,9],[7,13]]),
([w0,w1,w2,w3,w30,w163,w38],[228,99,205,166,196,181,106,0,417,171,429,209,232,223],[],[[0,1,2],[2,3],[0,4,5],[5,1,6],[7,5,8],[0,1,9],[0,3],[6,1],[0,10,2],[11],[5,2,3],[0,2],[1,0,2],[12],[0,2],[0,1],[],[3,1],[13],[0,9,3],[0,1,8]]),
([w164,w0,w1,w2,w3,w30,w38],[0,96,417,219,205,209,162,36,31,228,166,90,196,181,171,223,190,199],[],[[0,1,2],[3,4,5],[6,4,7],[7,1,8],[9],[2,10],[1,11],[2,1],[2,12,13],[1,11],[1,10,14],[15,10],[1,4,12],[4,16],[2,4,10],[10,1,4],[4,11],[2,4,15],[1,17],[1,13,2],[2,11]]),
([w0,w165,w1,w2,w3,w30,w38],[262,318,90,171,166,196,159,99,205,25,141,204],[],[[0],[1,2],[3,1,4],[1,5,6],[6,2,7],[1,4,3],[0,7,8],[0,1,6],[0,5,6],[9,7,10],[0,2,6],[1,2],[6,5],[1,11],[10,2,8],[1,8],[4,2],[1,6],[1,7],[2,6,7],[1,2,4]]),
([w0,w1,w2,w3,w30,w166,w38],[228,90,205,166,181,171,190,199,223],[97],[[0,1],[2,3],[0,4],[4,1],[4,1],[0,3,5],[0,1],[6,2],[0,6,2],[0,6,2],[4,1],[0,2],[2,0,1],[0,2],[0,2],[0,7,100],[0,7],[1,4],[8],[0,1,3],[0,1,4]]),
([w21,w51,w0,w1,w2,w30,w38],[96,199,196,70,99,166,90,36,171,205,181],[97,84],[[0,1],[1,2,3],[0,2],[2,0],[0,100,4],[0,5,4],[0,6],[1,101,4],[1,6,5],[7],[1,6,2],[0,4,6],[1,0],[0,1],[0,2,8],[4,5,7],[7,9],[10,2],[4,6,5],[2,9,7],[2,6]]),
([w167,w0,w1,w2,w7,w30,w38],[30,90,181,430,196,431,96,36,199,171,106,99,432,204,228,338],[26],[[0,1,2],[3,4,5],[4,1,6],[7,4],[4,8],[2,1],[2,1],[2,6],[2,1],[2,1],[6,4,9],[100,10,1],[11],[12,13],[2,1],[14],[12,1,10],[2,15],[12,10],[2,1],[2,1]]),
([w168,w0,w1,w2,w3,w30,w38],[96,0,106,99,171,166,36,146,196,126,204,181,108,201],[],[[0],[1,2,3],[1,4,5],[6,7,8],[1,2,3],[3,4],[2,3],[4,5],[7,8],[2,3],[4,3],[3,2],[2,3],[9,7,10],[2,4,11],[4,12],[3,2],[3,9,13],[2,3],[4,3],[2,4,5]]),
([w0,w1,w2,w3,w69,w34,w38],[228,90,171,166,181,126,204,106,338,199,209,232,182,99,96],[],[[0,1],[2,3],[0,4],[4,1],[5,1,6],[0,3,2],[0,1],[7,8,9],[10],[0,6],[4,1],[0,9],[11],[3,0,1],[0,12],[0,8,13],[14],[1,4],[0,13],[0,1,4],[0,1,3]]),
([w51,w0,w1,w2,w3,w69,w38],[96,204,106,228,199,223,171,181,90,196,209,232,182,99],[],[[0,1,2],[3,1],[1,2],[4],[5],[2,6,7],[0,8],[6,0,7],[3,7],[7,0],[0,1,6],[3,2,6],[0,9],[10],[2,1,7],[3,0,9],[11],[1,12,3],[3,0,13],[0,7,1],[3,1,7]]),
([w0,w1,w2,w169,w30,w69,w38],[228,90,171,96,181,196,126,204,209,106,232,182,199,223],[],[[0,1],[2,3,4],[0,5,6],[3,1],[4,1],[0,5,2],[0,1],[3,5],[0,7],[8],[4,1],[0,3,5],[7,0,9],[10],[0,11],[0,12,3],[],[1,6,3],[13],[0,1,4],[0,1,4]]),
([w167,w0,w1,w2,w30,w69,w38],[181,90,199,182,196,96,36,171,146,106,165,197,204,239,338,432],[],[[0,1],[2,3,4],[2,1,5],[4,2],[6],[0,1],[0,1],[0,5],[0,1],[0,1],[2,4,7],[8,1,9],[10,3],[11],[0,1],[12,1,9],[13],[0,3,14],[15],[0,1],[0,1]]),
([w167,w0,w1,w2,w3,w30,w38],[0,90,181,215,182,209,154,232,199,228,223,165,204,171,99,239],[],[[0,1,2],[3,4,5],[6,1,7],[8],[7,9,10],[2,1],[2,1],[2,11],[1,2],[2,1],[9,12,13],[9,1],[4,14],[9,4,11],[2,1],[1,15],[12,1,15],[2,4,9],[9,14],[1,2],[2,1]]),
([w167,w0,w1,w2,w30,w38],[0,181,196,165,215,99,54,100,239,96,171,41,199,204,31,36,11,182,90,166,106,228,433,434,315],[0,24,69,8,9,98,38,7,43,26,16,99,100,91],[[0,1,2,3,100,101],[4,5,2,3,6,7],[2,8,6,9,10,11],[2,5,6,12,13,14],[9,1,15,16,10],[1,17,100,18,5,102,103],[1,10,104,3,19,100,105],[1,20,100,12,5,106],[3,10,100,8,2,107,108],[5,8,109,3,10,103,104],[3,21,103,17,13,22,110],[3,1,103,17,2,111,107],[8,5,22,10,23,104],[21,1,22,8,112,104],[20,1,107,24,10,113,110]]),
([w0,w170,w1,w2,w3,w30,w38],[181,182,99,166,164,196,171,36,146,204,31,96,201],[],[[0],[1,2],[1,3],[4,5],[4,2],[6,2],[1,2],[1,3],[7,5,8],[4,2],[6,2],[2,3,4],[1,2],[4,1,9],[10,1,3],[1,11,5],[2,1,3],[2,1,12],[5,2,8],[3,2],[3,4,6]]),
([w0,w1,w2,w3,w171,w30,w38],[181,99,182,166,223,0,90,171,165,96,31],[],[[0,1,2],[0,3,2],[4,0],[5,0,6],[0,1,6],[4,1,7],[1,3,4],[2,1],[2,1],[4,2,8],[0,2,3],[2,9,10],[2,3],[1,2,3],[0,2,4],[10],[4,1],[3,0],[4,1],[4,0,6],[0,6]]),
([w172,w0,w1,w2,w3,w30,w38],[0,181,96,99,228,25,171,90,166,232,196,204,199],[],[[0,1,2],[3],[4],[2,5,4],[5,4],[4,1,6],[1,7],[1,2],[7,1],[1,7],[2,8,6],[9,6],[2,10],[9,11],[1,6],[6,2,10],[8,6],[1,9],[2,12],[2,1,6],[1,6]]),
([w0,w108,w2,w7,w3,w30,w38],[30,90,181,96,166,171,31,165,199,36,196,25,204,182,338],[84],[[0,1,2],[2,3],[2,1],[1,2],[2,1],[3,4,5],[6,1,7],[6,7],[3,8,6],[7,6],[2,1],[9],[1,3,10],[4,1],[2,9],[9,3,100],[11,12,13],[2,1],[3,14],[1,2],[2,1]]),
([w0,w1,w2,w173,w3,w30,w38],[228,338,171,96,166,0,181,330,204,232,196,182,223],[],[[0,1],[2,3,4],[5,1,6],[0,6],[3,1],[0,4,2],[0,1],[7],[3,1],[0,8],[6,2],[9],[0,3,10],[4,0,1],[0,11],[0,1],[0,12],[0,2,6],[0,1,3],[1,6,2],[0,2,4]]),
([w0,w2,w8,w9,w30,w32,w38],[181,96,419,36,226,196,204,190,239,99,417,338,41],[],[[0,1],[2,0,3],[4,0,5],[0,6,7],[0,7],[1,5,8],[3,1,7],[3],[6,8],[8,9],[0,8,3],[3,1,5],[1,6,3],[1,7],[1,0,10],[5,11],[12,5],[3,0,6],[3],[0,7],[0,5]]),
([w0,w2,w3,w8,w32,w33,w38],[181,144,338,196,171,228,99,232,182,96,204,25],[],[[0,1],[1,0],[1,0],[0,2],[0,1],[1,3,4],[3,4],[5,2],[6,1],[7],[0,8,2],[9],[1,2,6],[3,2],[2,0,4],[1,6],[5,8,10],[11,0,8],[5,6],[0,3],[0,4]]),
([w46,w0,w2,w3,w8,w32,w38],[226,204,228,88,196,435,166,203,232,99,239,253,181,417],[],[[0,1],[2],[1,3,4],[2,1],[5],[2,3,4],[3,6,7],[7,4],[7,3,8],[7,3,9],[8,1,10],[3,10,6],[8,6],[9,6,8],[1,10,7],[11],[8,3,9],[1,12],[7,8],[7,1,13],[7,1,12]]),
([w77,w0,w2,w3,w8,w30,w38],[33,99,228,196,181,165,232,204,88,239,106,96,417],[],[[0,1],[2],[2,1],[2,1],[1,2],[2,3,4],[4,5],[5,3,4],[6,4],[4,7,8],[5,3,9],[3,9,6],[6,5,9],[7,10],[3,9,6],[11],[3,8],[7,4],[5,7,6],[5,3,12],[3,8]]),
([w0,w2,w3,w8,w30,w32,w47],[181,36,204,88,226,239,182,96,196,99],[0],[[0,100],[1,0],[1,0],[0,2,3],[0,3],[4,2],[1,5],[1,5],[2,6,5],[5,6],[1],[7],[1,3,8],[1,3,9],[1,0],[1,2],[1,6,9],[1,0],[1],[0,3],[0,2]]),
([w0,w1,w8,w9,w30,w33,w38],[228,88,436,239,196,227,181,182,197,96,417,223],[],[[0,1],[0,1],[2,3,4],[3,1],[5,1,6],[0,3],[7],[0,1],[0,8],[0,8],[6,1],[0,1],[0,9],[0,3],[9,1,10],[4,0,1],[0,3],[0,6,10],[11],[0,1,4],[0,1,3]]),
([w0,w1,w2,w9,w30,w72,w38],[36,88,96,417,196,239,99,204,165,31],[],[[0,1],[1,2],[3,2],[2,1],[3,1],[0,4,5],[0,6],[0,1],[0,7],[8],[3,1],[0],[5,6],[9,2],[0,5],[4,1],[9,1,2],[0,6,3],[0],[0,1,3],[0,1,3]]),
([w0,w1,w2,w3,w33,w72,w38],[228,99,88,144,196,181,52,417,171,182,204,165,232,31,96],[],[[0,1,2],[2,3],[0,4,5],[5,1,2],[6,2,7],[0,1,8],[0,8],[9,1],[0,9,10],[11],[5,2],[0,2],[12],[13,0,3],[0,9],[0,1],[14],[7,1],[0,1],[0,2,4],[0,1,7]]),
([w0,w92,w2,w3,w8,w30,w38],[33,99,417,144,196,239,204,88,228,232,96,181],[],[[0,1],[2,3],[2,4,5],[2,5],[2,6,7],[3,4,5],[1,8,5],[8,1],[8,1],[1,6,3],[2,4],[4,5,9],[9,5],[5,3,6],[2,5,9],[10],[3,7,4],[2,11],[3,6],[2,4],[2,7]]),
([w0,w1,w2,w3,w174,w30,w38],[232,99,88,144,196,239,171,41,165,204,417],[],[[0,1,2],[2,3],[0,4,5],[3,2],[5,1,2],[0,1,5],[0,6],[7,1,2],[8],[0,9],[7,2],[0,5],[0,5],[1,3],[0,5],[7],[0,1],[6,1],[0,1],[0,1,10],[0,2,4]]),
([w46,w0,w1,w2,w3,w72,w38],[239,99,88,36,204,228,435,196,144,56,417,166,41,165,31,232],[],[[0,1,2],[3,4],[5],[3,1],[6],[3,2,7],[0,1,2],[2,8],[8,0],[9,0,10],[8,0],[0,11],[12,1,2],[13],[10,2],[2,0,11],[14,0,8],[1,0,15],[12],[4,1],[8,1,10]]),
([w0,w1,w2,w3,w30,w72,w47],[239,99,88,36,58,417,171,182,204,165,31,249],[0],[[0,1,2],[2,100],[3,0],[0,1,2],[4,0,5],[6,0,1],[0,1],[7,1],[3,7,8],[9],[3,2],[2,0,3],[0,7],[10,0],[3],[3,1],[11],[3,1],[3],[5,2],[5,1]]),
([w175,w0,w1,w2,w3,w30,w38],[239,0,182,165,31,166,41,36,171,99,241,196,203,417,130,108],[],[[0],[1,2,3],[4,2,5],[1,6],[1,7],[5,8],[2,9],[2,5],[10,11,12],[13,9,14],[8,5],[9,5,10],[2,9],[10,2,12],[12,2],[2,15],[5,2],[9,2,10],[10,9],[5,9],[5,8]]),
([w102,w0,w2,w3,w30,w72,w38],[417,239,99,171,36,182,165,88,209,41],[],[[0,1],[2,1,3],[4,2],[4],[4],[0,5,4],[0,6],[0,1],[0,2,7],[0,1],[3,1,2],[3,1],[1,3],[8,1,6],[0,1,4],[4,2],[9],[0,2],[4],[0,3],[0,2]]),
([w176,w0,w1,w2,w3,w30,w38],[0,88,165,99,239,51,41,36,417,196,181,146,96,144,232],[],[[0,1,2],[2,3],[4],[5,1,6],[6,3,7],[7,1,8],[8,1],[1,2],[2,9,10],[2,1],[2,3,11],[3,2],[2,1,3],[2,11],[2,1,8],[1,12],[3,13],[1,14],[9,1],[8,3],[8,1]]),
([w0,w73,w1,w2,w9,w30,w38],[36,99,236,108,239,196,31,96,106,123,204,181],[],[[0],[0,1,2],[2,3],[2,4,5],[2,1],[0,1,2],[0,1,2],[6,3,7],[2,5],[7,1,8],[0,1,9],[0,8,1],[0,1,5],[0,10],[8,5,11],[0],[1,8],[0,4],[5,1,10],[0,1,9],[0,9]]),
([w0,w1,w74,w3,w30,w33,w38],[239,88,228,417,165,171,96,182,209,41,181,223],[],[[0,1],[1,0],[2,0],[0,1],[3,1],[2,0],[2,4,5],[4,1,6],[2,7,4],[0,4,8],[3,1],[1,6],[9,2,5],[2,0],[1,7,2],[2,1,6],[2,0],[3,10],[11],[2,1,3],[2,0]]),
([w0,w1,w2,w3,w30,w177,w38],[239,88,165,0,417,171,96,182,36,209,232,228,196,181,223],[],[[0,1],[1,2],[2,0],[0,1],[3,0,4],[2,0],[0,2,5],[2,1,6],[2,7],[8,2,9],[2,1,4],[1,0,5],[0,5],[10],[1,0,11],[6,1],[8,1,12],[4,13],[14],[4,1],[4,1]]),
([w178,w0,w1,w2,w3,w30,w38],[321,182,165,31,108,65,70,171,196,130,99,241],[],[[0],[0,1,2],[3,1,4],[0,5,6],[5,0],[0,7,4],[1,4],[1,2,4],[2,8,9],[2,10,9],[2,4,7],[9,2,7],[1,4],[2,1],[2,1],[1,4],[4,1],[8,1,11],[8,9,11],[7,4],[4,7]]),
([w0,w1,w2,w9,w30,w75,w38],[36,88,165,130,196,239,209,146,169,31,96],[],[[0,1],[1,2],[3,2,4],[2,1],[2,1],[0,4,5],[0,2,6],[0,1],[0,7,2],[0,7,2],[2,1,6],[0],[5,8],[9,5,10],[0,5],[4,1],[4,1],[0,3],[0],[0,1,4],[0,1,4]]),
([w0,w1,w2,w3,w75,w33,w38],[228,88,165,196,146,130,209,199,31,106,232,182,181,171],[],[[0,1],[1,2],[0,3,4],[2,1],[5,1,6],[0,3,4],[0,2,4],[2,1,7],[0,4,2],[0,2,6],[2,1,6],[0,1],[8,0,9],[10],[0,11],[0,1,3],[0,1,3],[7,12,13],[0,8],[0,1,3],[0,1,3]]),
([w46,w0,w1,w2,w3,w75,w38],[130,88,165,146,228,196,435,232,199,181,239,31,417],[],[[0,1,2],[0,3,2],[4],[4,1,5],[6],[4,0],[3,1,7],[1,2],[2,5,3],[2,1],[2,5,3],[3,2],[2,1,8],[2,3],[2,1,9],[1,10,7],[11,10,7],[1,10,7],[5,1],[8,9,12],[5,1]]),
([w179,w0,w1,w2,w3,w30,w38],[0,181,165,146,228,196,56,268,88,199,96,169,106,232,417],[],[[0,1,2],[2,3],[4],[4,3,5],[6,4,7],[4,1,5],[1,8],[1,2],[2,1],[1,8],[2,5,3],[3,2],[2,5,9],[2,3],[1,5],[3,10],[11,12],[1,13],[5,3],[9,1,14],[1,3]]),
([w0,w1,w2,w3,w30,w75,w47],[36,88,165,196,146,199,239,182,31,181],[],[[0,1],[1,2],[0,3,4],[2,1],[2,1],[4,2,3],[0,2,4],[2,1,5],[0,4,2],[0,4,2],[0,1],[0,6],[6,7],[8,6],[0],[0,1,3],[0,1,3],[0,9],[0],[3,1],[3,1]]),
([w42,w0,w1,w9,w30,w33,w38],[264,181,228,108,199,96,239,196,88,437,182,165,209,223],[],[[0,1,2],[3],[4],[2,5],[2,5,6],[5,1,7],[1,8],[9,1,7],[1,8],[1,5],[2,6],[2,7],[2,10,11],[2,10,12],[1,7],[7,2,8],[2,6],[2,1,10],[13],[1,8],[1,6,2]]),
([w180,w0,w1,w2,w3,w30,w38],[0,199,165,146,36,228,232,196,435,88,181,239,106,169,417],[],[[0,1,2],[2,3],[4,5,6],[4,1,7],[6,8],[4,3,7],[1,9],[1,2],[2,7,3],[2,1],[1,7,3],[3,2],[1,7],[2,3],[2,7,10],[1,11,6],[11,12,13],[3,11,6],[6,1,7],[1,10,14],[6,3,7]]),
([w0,w1,w2,w181,w3,w30,w38],[181,99,106,165,146,196,239,96,182,201,417],[],[[0,1,2],[0,3],[0,3],[3,0],[0,1,2],[3,1,4],[1,2],[1,2],[2,1],[3,4],[0,5],[6],[4,7],[1,2],[0,8,9],[5,4],[1,2],[0,4],[2,1],[7,0,10],[0,4]]),
([w0,w1,w2,w3,w182,w30,w38],[181,99,182,108,241,130,239,171,165,31,166,196],[],[[0,1,2],[0,3,2],[4,0],[4,0],[0,1,5],[4,1,6],[1,7,4],[2,1],[4,1,8],[3,2],[0,2,7],[2,3],[9,2,10],[1,2,3],[0,2,4],[11],[4,1],[7,0],[4,1],[4,0,5],[0,5,4]]),
([w76,w0,w1,w2,w3,w33,w38],[88,52,438,334,31,439,106,146,196,241,164,99,96,181,171,126,204,412,25],[],[[0],[1,2,3],[4,5,6],[6,7,8],[9,4,10],[6,7,8],[2,11],[2,12,13],[2,8],[2,11],[2,8],[7,14,15],[12,8],[9,7,16],[13,8],[7,12],[17],[7,15,18],[8,7],[12,11,14],[8,7]]),
([w0,w1,w3,w9,w32,w33,w38],[228,90,181,243,417,239,96,182,175,204,196,41],[],[[0,1],[0,2],[3,2,4],[2,1],[2,1],[0,5],[6,7],[0,1],[8],[0,7,9],[2,1],[10],[0,6],[0,5],[1,2],[11,0,1],[0,5],[0,2,4],[0,9],[0,1,2],[0,1,2]]),
([w0,w1,w2,w9,w32,w34,w38],[36,88,96,251,417,239,146,175,204,99,41,181],[],[[0,1],[1,2],[3,2,4],[2,1],[4,1],[0,5],[0,6],[0,1],[7],[0,6,8],[4,1],[0],[5,9],[8,2],[0,5],[10,1],[8,1,2],[0,11,4],[0],[0,1,4],[0,1,4]]),
([w0,w1,w2,w3,w32,w82,w38],[228,88,96,239,39,204,171,175,181,232,196,11],[],[[0,1],[1,2],[0,3],[2,1],[4,1,5],[0,3],[0,6],[2,1],[7],[0,5],[8,1],[0,2,1],[3,0,6],[9],[0,3],[0,1,2],[10],[2,8,5],[0,5],[0,1,8],[0,1,11]]),
([w78,w0,w1,w2,w3,w33,w38],[52,90,181,440,25,441,41,196,228,223,96,204,171,99,182],[],[[0,1,2],[3,4,5],[6,1],[7],[6,8,9],[2,1],[2,1],[2,10],[1,2],[2,1],[8,11,12],[6,1],[6,13,14],[6,11],[2,1],[1,10],[6],[2,14,8],[8,10,13],[1,2],[2,1]]),
([w90,w0,w1,w2,w3,w32,w38],[39,204,36,228,232,96,171,181,90,144,182,196,358,239,99],[],[[0,1],[2,1],[1,3,4],[5],[2,1],[2,6,7],[3,8],[6,9,7],[3,7],[7,8],[3,1,6],[3,6],[10,11],[12],[7,1],[3,13],[13,3,6],[1,10,3],[3,11,14],[1,7],[3,1,7]]),
([w0,w1,w2,w3,w93,w32,w38],[232,88,144,181,239,166,41,204,25],[],[[0,1],[1,2],[0,3],[2,1],[3,1],[0,4],[0,5],[6,1],[0,7],[8],[3,1],[0,4],[0,4],[4,2,5],[0,4],[6],[0,1,6],[5,3],[0,6],[0,1,5],[0,1,3]]),
([w167,w0,w1,w2,w30,w32,w38],[39,196,328,442,96,204,88,181,239,166,182,165,338,228],[28],[[0,1],[2,1,3],[1,4],[1,5,6],[4,1],[4,5,7],[4,6],[6,4],[4,5,6],[4,6],[4,1,8],[8,9],[100,10,5],[11],[7,1],[5,10,8],[8,9],[1,8,12],[13],[1,6],[7,1]]),
([w0,w183,w1,w2,w3,w30,w38],[181,247,88,99,166,196,41,146,36,200,333,11,106,238],[],[[0],[1,2,3],[1,4],[1,5],[6,2],[7,3],[1,3],[1,4],[8,2,9],[1,3,10],[1,2,11],[3,4,1],[6,2],[1,7],[1,2,6],[2,9],[1,12,3],[1,13],[1,2],[1,3,4],[4,2]]),
([w0,w1,w2,w3,w184,w30,w38],[181,88,165,239,99,146,232,106,41,204,11],[],[[0,1],[0,2],[2,0],[2,0],[0,1],[2,3],[3,2,4],[2,1,4],[2,4],[2,5],[0,1],[1,3,6],[6,3],[3,7,4],[0,3,6],[8],[6,1,4],[9,0],[6,4],[6,0,10],[0,1]]),
([w77,w0,w1,w2,w3,w34,w38],[65,88,181,443,146,106,228,99,435,165,239,41,232,204,238],[],[[0,1,2],[3,4,5],[6],[6,1,7],[5,6,8],[2,1],[2,1],[1,9],[4,2,9],[5,1,9],[4,10,9],[4,5],[5,1,11],[9,4],[2,1],[1,10,12],[13,5],[1,10,12],[11],[13,2],[5,1,14]]),
([w0,w1,w2,w3,w32,w34,w47],[36,88,239,420,204,251,146,130,165,182,99,254,181,166],[0],[[0,1],[1,100],[0,2],[2,1],[3,1,4],[5,2,4],[0,6],[7,1],[8],[0,4],[0,1],[0,2],[2,9],[4,2],[0],[0,1,10],[11],[0,7,12],[0],[12,1],[13,1]]),
([w51,w0,w1,w2,w3,w32,w47],[420,204,11,182,239,130,295,181,171,258,96,190,196,165,36],[],[[0,1],[2,1],[1,3,4],[5],[6],[7,2,8],[3,9,4],[3,10,7],[9,4],[4,9],[8,1],[4,11],[3,12,10],[13],[7,1],[3,4],[4,3],[14],[10,12],[1,7],[7,1]]),
([w78,w0,w1,w2,w3,w30,w47],[58,190,239,444,165,182,130,400,373,181,99,96,171,254,204,36],[],[[0,1,2],[3,1,4],[2,5],[6],[7,6,8],[9,1],[2,10,5],[1,11],[1,2],[2,1],[12,2,10],[1,2],[1,10],[13,1,14],[9,5,12],[5,2],[2,5],[15],[11,10,14],[1,9],[9,1]]),
([w102,w0,w2,w3,w30,w32,w38],[39,239,165,171,445,41,36,11,181,204,190,88],[],[[0,1,2],[3,1],[4,5],[5,6],[2,6],[3,7,6],[3,2,8],[2,1],[1,9,10],[1,10],[2,1],[3,1],[1,3],[1,2,3],[6,1],[5,11],[2,11,5],[3,8],[6],[5,3],[2,3,5]]),
([w102,w0,w2,w3,w32,w34,w38],[251,239,88,190,171,25,11,181,165,204,166,36,99,173],[],[[0,1,2],[3,1,4],[2,5,3],[5,3],[6],[2,7],[2,8],[3,1],[1,2],[8,1],[4,1,8],[2,1,4],[1,4],[9,1,10],[2,1,11],[8,2,12],[13],[3,7],[8,9,11],[7,2],[10,2]]),
([w103,w0,w1,w2,w3,w32,w38],[39,181,204,11,239,25,238,446,88,166,96,232,146,177,99],[],[[0,1,2],[3,2],[4],[2,5],[6,2,7],[5,1,3],[1,8],[1,9,10],[11,1],[1,8],[10,2,12],[11,9],[10,8],[13],[1,2],[8,10],[14,9,11],[1,11],[10,8],[2,1],[1,2]]),
([w0,w1,w2,w109,w3,w32,w38],[25,90,228,96,181,204,171,196,99,41,182],[],[[0,1,2],[0,3,4],[0,1,4],[0,4,1],[0,1,3],[2,5,6],[2,1],[2,5],[3,7],[0],[0,1,4],[0],[1,3,7],[8,1,9],[0,10],[2,3,7],[2,5],[0,1,4],[2,7,3],[0,4,1],[0,1,4]]),
([w0,w185,w1,w2,w3,w30,w38],[241,253,99,166,196,254,321,171,31,205,447],[],[[0],[1,2],[1,3],[1,4],[5,2],[6,2,7],[0,1],[8,3,9],[0,4,1],[0,2,5],[0,2,5],[2,3,5],[5,2,4],[1,10,5],[1,3,9],[3,9],[1,7],[1,5],[1,2,6],[1,2,3],[3,5,6]]),
([w0,w1,w2,w186,w3,w30,w38],[228,99,182,166,0,96,181,90,171,204,232],[101],[[0,1,2],[2,3],[4,5,6],[0,6],[5,1,7],[0,1,8],[0,3],[0,2,1],[2,1],[0,2,9],[6,2,3],[10],[0,5,100],[1,0,3],[0,2],[0,5],[0,1],[0,3,1],[0,1],[3,1],[0,7,3]]),
([w124,w78,w0,w1,w2,w30,w38],[96,196,253,181,99,36,254,154,239,159,205,88,204],[0,102,96,101],[[0,1],[2,100,3],[0,101,4],[5],[0,102,4],[0,6],[0,1,7],[4,1,5],[1,103,8],[1,5],[3,9,5],[0,4,10],[3,0],[0,4,11],[0,1,8],[4,5],[5,12],[3,1],[4,8],[1,8,5],[1,11]]),
([w0,w1,w79,w3,w9,w30,w38],[228,108,175,239,417,204,106,209,358,315],[],[[0,1,2],[2,1],[0,3],[2,3,4],[3,5,6],[0,1,3],[0,6,7],[6,1],[0,1,7],[0,5],[2,5,4],[0,1],[0,1],[0,5],[0,3],[8],[0,2],[2,1,4],[2,0,5],[0,1,4],[0,9]]),
([w0,w1,w2,w3,w187,w30,w38],[175,99,96,181,228,209,106,204,239,177,358,315],[],[[0,1],[0,2,3],[0,3,4],[0,2,5],[2,1,6],[2,1,5],[1,6],[2,1,5],[4,1,5],[0,7,4],[0,5],[4,0,8],[9],[0,4,1],[0,8],[10],[0,1,4],[0,1,7],[0,1,7],[0,1,7],[3,11,4]]),
([w0,w1,w2,w79,w3,w34,w38],[25,88,228,315,181,204,209,199,229,130],[],[[0,1,2],[0,3,1],[0,3,1],[0,4,2],[0,1,5],[2,3],[2,3,6],[2,3,6],[3,1,7],[2,5],[0,1,3],[0],[1,2],[5,2,3],[0,8],[1,7],[2,5],[0,9],[0],[0,4,5],[0,1,3]]),
([w0,w1,w2,w80,w9,w30,w38],[36,99,175,96,209,239,199,165,204,31,258,181],[],[[0,1,2],[2,3,4],[2,5,4],[2,3,4],[3,1,6],[0,1,4],[0,7,1],[0,1,4],[0,1,4],[0,8],[2,4],[9,2,3],[0],[1,2],[0,5],[2,6],[0],[0,1,8],[2,1,6],[0,1,8],[0,10,11]]),
([w188,w0,w1,w2,w3,w30,w38],[0,181,209,99,228,25,204,177,96,199,315,232],[],[[0,1,2],[2,3],[4],[4,5],[5,3,4],[4,1,6],[1,3,7],[1,8],[2,1],[1,3,9],[8,2],[2,10],[2,3],[2,6,11],[1,2,6],[9,8],[3,10],[1,7],[6,3],[6,1],[1,10,11]]),
([w0,w1,w2,w3,w80,w33,w38],[228,99,25,165,181,209,199,31,315,229,204,130],[],[[0,1,2],[2,3,4],[0,4],[2,4,3],[2,1],[0,1,5],[0,3,1],[3,1],[0,1,3],[0,3,5],[2,5],[0,6],[7,0,8],[2],[0,9],[2],[0,1],[2,1,10],[0,1],[0,1,8],[0,11]]),
([w0,w1,w2,w3,w80,w30,w47],[181,99,25,165,199,204,36,239,31,229,130,258],[],[[0,1,2],[0,3],[2,0,3],[2,0,3],[0,1,4],[2,1],[1,3],[3,1],[3,1],[2,5,6],[0,3,5],[4,7,6],[8,7],[1,9,2],[2],[2],[2,1,4],[4,0,5],[2,1,5],[5,0],[0,10,11]]),
([w0,w1,w2,w3,w9,w30,w81],[36,258,165,181,204,47,209,205,315,175,199,314],[],[[0,1],[1,2],[0,3],[1,2],[2,1],[2,4,5],[0,2,6],[2,7],[0,2,6],[0,4],[0,1],[0,7],[0],[4,8],[1,7,9],[10],[0,11],[0,3],[4,8],[1,3],[0]]),
([w43,w0,w1,w3,w9,w33,w38],[264,229,181,182,228,175,223,315,258,165,205,209,358],[],[[0,1,2],[3],[4,5],[5,1],[6],[2,7,4],[1,8],[1,2],[5,2,8],[2,1],[4,1],[9,10],[1,9,11],[4,9,11],[2,8],[12],[4,5,10],[5,2,8],[4,5],[4,1],[2,8]]),
([w43,w0,w1,w2,w9,w34,w38],[266,199,181,146,175,99,36,314,258,165,209,205,204,96,123],[],[[0,1,2],[3],[4,5],[4,1],[6],[2,7,6],[1,8],[1,9],[4,2,8],[4,1,9],[1,10],[6,9,10],[1,9,10],[6,11,9],[2,8],[6],[12,4,13],[2,11,4],[4,1],[1,2,8],[4,2,14]]),
([w43,w0,w1,w2,w3,w82,w38],[258,199,146,205,228,99,223,315,165,181,43,209,232,358,11],[],[[0,1],[2],[3,4,5],[4,1,5],[6],[0,7,4],[1,0],[0,8],[0,9],[10,0,11],[1,11],[4,8,11],[1,3,8],[4,3,11],[8,0,3],[1,3,4],[12],[0,3,4],[13],[0,9],[4,0,14]]),
([w0,w1,w189,w2,w3,w30],[223,205,25,258,6,209,199,293,181,11,141],[34,0,24,6,8,27,28,14,15,54],[[0,1,2,3,100,4],[2,5,101,6,7],[2,7,101],[0,2,8,102,101],[2,9,103],[4,1,104,7],[4,7,104],[4,1,105,5],[1,0,2,4,106],[2],[0,6,7,8,107],[0,2,4],[0,6,7,1,107],[1,2,7,108],[2,10,109,0,103]]),
([w43,w0,w1,w2,w3,w34,w47],[296,199,209,146,205,229,36,25,130,141,258,165,181,204,417],[],[[0,1,2],[3],[4,5],[6,1,7],[6],[7,8,9],[1,10],[1,11],[2,12],[2,1],[1,2],[2,11],[1,4,2],[2,4],[6,2,10],[1,4,5],[13,4],[6],[7],[1,8],[14,8,10]]),
([w103,w43,w0,w1,w2,w3,w38],[238,36,446,258,209,204,205,199,25,146,177,315,141,165,181,88,96],[],[[0,1,2],[0,3,4],[0,5],[6],[1,7,8],[1,0],[3,7],[9],[10,11,12],[10,7],[3,11,12],[7,3],[3,13],[3,14],[7,4],[4,13],[4,15,7],[10,3,4],[7,16],[3,10],[3,14]]),
([w0,w1,w2,w3,w9,w131,w38],[384,99,165,209,181,204,123,54,96,177,315,205,175,141],[],[[0,1],[0,2,3],[0,4,2],[0,2,3],[0,1],[0,1],[1,2],[2,1],[3,1],[2,5,6],[2,3],[7,8],[9],[1,10],[1,11,12],[7],[5,1],[5,1],[0,5],[5,1],[4,6,13]]),
([w130,w0,w1,w2,w3,w9,w38],[47,181,209,123,205,204,315,96,141,258,190,229,337,199],[61],[[0,1,2],[3,4,5],[5,4,6],[5,7,8],[5,0],[8,1,3],[1,9],[1,6],[6,1],[9,1],[7,5,6],[8,6],[6,4],[10,4],[1,4,5],[100,4,7],[11],[1,4,12],[13],[5,1],[5,1]]),
([w0,w1,w190,w2,w3,w30,w38],[205,258,262,166,196,123,204,171,209,141,159,25,202,338],[],[[0,1,2],[2,1],[0,3],[1,4,5],[5,1,6],[2,3,7],[8],[2,3],[5,0,4],[0,6,2],[9,0],[2,0],[2,4,10],[11,6,12],[2,1,5],[2,0],[0,7],[1,0,2],[2,9],[1,5,13],[2,1,3]]),
([w0,w1,w2,w3,w30,w191,w38],[205,258,199,166,196,175,209,229,146,108,204],[],[[0,1,2],[0,3],[1,4,5],[6,1],[5,1,6],[2,3,6],[6,3,7],[2,0,4],[0,8],[6,0],[5,0],[2,0,3],[0,7],[3,0],[1,0,5],[4,2],[4,2],[1,9],[10],[3,1],[3,1]]),
([w24,w0,w1,w3,w30,w33,w38],[181,209,205,52,363,361,25,448,229,258,108,196,190,175,106,166,362],[],[[0],[1,2],[3,4,5],[6,7,8],[6,2,8],[6,8],[2,9,10],[1,11,4],[1,9],[1,9],[4,1,10],[1,2],[1,12],[1,12],[13,1],[11,14],[11,2,15],[9,10],[16],[10,9],[11,2,9]]),
([w24,w0,w1,w2,w30,w34,w38],[181,209,205,65,380,25,405,199,130,258,108,266,166,200,190,141,175,381],[],[[0],[1,2],[3,2,4],[5,6,7],[5,6,7],[5,8],[2,9,10],[1,10,2],[1,9],[1,9],[11,1,10],[1,12,13],[1,14],[1,2],[13,1],[2,15],[12,2],[9,2,16],[17],[10,9],[12,9]]),
([w0,w192,w1,w2,w3,w30,w38],[258,181,108,132,123,196,204,179,159,25,166,171,318,99],[],[[0],[1,2,3],[1,2,4],[4,1,5],[1,6,4],[3,2],[3,2],[4,7],[4,8],[9,6],[3,1],[3,10,4],[3,2],[2,3],[1,5],[5,2,10],[2,11],[1,4,12],[5,13,6],[3,1],[1,3]]),
([w0,w1,w2,w3,w30,w193,w38],[228,258,166,171,196,181,0,209,199,190,96,229,223],[],[[0,1],[1,2,3],[0,4,5],[5,1],[6,1,7],[0,2,3],[0,2],[7,4,8],[0,9,7],[0,9,7],[5,1],[0,10,4],[2,0,3],[0,2],[0,11],[0,8,4],[0,8,4],[1,5],[12],[0,1,2],[0,1,2]]),
([w36,w0,w1,w3,w9,w30,w38],[47,229,258,190,36,96,205,228,223,181,197,209,204,196,330],[],[[0,1,2],[3],[4,5,6],[4,1,6],[4,7,8],[2,6,4],[1,2],[1,9],[2,5],[5,1],[5,1],[5,10,11],[1,10,11],[7,12],[9,2],[13],[5,7],[2,9],[12,1,14],[2,1,7],[7,2,9]]),
([w0,w1,w9,w30,w33,w34,w38],[175,258,181,209,96,205,190,229,99,228,36,417],[],[[0,1,2],[0,2,1],[2,1],[0,1,2],[0,1,3],[4,3],[3,5],[0,6],[3,6],[3,5],[0,1,2],[0,7],[0,7],[0,7],[0,2,1],[8],[9],[2,1],[10,0,5],[0,1,2],[0,1,11]]),
([w0,w1,w3,w9,w33,w34,w38],[228,258,181,264,209,205,190,199,175,25,229,417],[],[[0,1],[0,2],[1,2],[2,1],[3,1,4],[0,4],[4,5],[0,5,4],[0,6,4],[0,5,4],[2,1],[7],[0,5],[8],[1,2],[0,5],[9,0,10],[0,2,1],[0,5],[0,1,2],[0,1,11]]),
([w0,w1,w9,w33,w34,w38],[228,449,258,99,282,181,266,337,209,264,283,171,338,36,190,263,175,25,2,96,229,270,205,156,417,122,450,152],[0,34,8,103,38,7,43,32,29],[[0,1,100,2,3,101,102],[2,1,4,5,100,103],[5,1,6,2,3,7],[8,1,9,2,104,100],[0,1,100,8,3,105,106],[8,0,10,3,11,12],[8,0,13,14,102,107],[8,0,15,3,107,102],[16,5,102,8,2,108,105],[17,13,11,3,7],[17,18,11,19,12],[0,2,12,20,3,21],[13,18,3,19,7],[0,5,7,22,2,23],[0,24,25,26,2,27]]),
([w50,w0,w1,w9,w30,w33,w38],[264,181,258,209,205,358,67,36,228,190,229,223],[],[[0,1,2],[3,4],[5],[6],[6,7],[2,1],[1,2],[2,1],[1,2],[1,2],[8,3],[3,4],[3,9],[3,9],[1,2],[5,8,10],[5,4,7],[2,1],[11],[1,2],[1,2]]),
([w51,w0,w1,w3,w9,w33,w38],[264,258,209,190,67,71,64,228,181,205],[],[[0,1,2],[2,3],[4],[4,5],[6],[7,1,8],[7,1],[1,8],[1,8],[2,1],[7,2],[2,9],[2,9],[2,3],[8,1],[5],[7,9],[1,8],[7,5],[1,8],[7,1,8]]),
([w103,w0,w1,w3,w9,w30,w38],[47,258,209,190,451,67,452,36,205,232,181,96,177,49],[],[[0,1,2],[2,3],[4,5,6],[4,5,6],[5,7],[7,1,8],[8,1,9],[1,10],[1,10],[2,1],[9,2],[2,8],[2,8],[2,3],[10,1],[5],[9,5,11],[1,10],[12,5,13],[1,10],[9,1,10]]),
([w37,w0,w1,w2,w9,w30,w38],[181,36,205,209,2,96,20,193,123,99,337,196,65,396,200,204,146,380],[],[[0],[1,2,3],[4,2,5],[6,5,7],[5,1],[1,8],[2,9],[2,10],[3,11,12],[3,9,13],[13,3,9],[3,14],[3,2],[2,15,16],[10,2],[17],[2,9],[9,2,10],[11,9,15],[15,9],[10,16,11]]),
([w102,w0,w1,w2,w9,w30,w38],[47,181,209,205,2,96,38,235,36,123,258,165,204,239,453,196],[],[[0,1,2],[3],[4,5],[6,5,7],[5,8],[5,1,9],[1,10],[1,5],[2,1],[1,10],[5,2],[2,11],[2,11],[2,12,8],[1,2,10],[8],[12,13],[1,13,8],[12,14,15],[8,1,10],[1,10]]),
([w103,w0,w1,w9,w30,w34,w38],[266,181,96,36,99,209,405,205,2,258,146,177,232,417],[],[[0,1,2],[3,4,5],[3,6,7],[7,3],[8],[3,1,7],[1,4,7],[5,1],[1,4,9],[5,1],[2,4,5],[5,4],[5,10],[2,4,5],[1,5,9],[11,4,10],[11,2,10],[9,1],[12],[1,9],[2,1,13]]),
([w0,w106,w1,w2,w9,w30,w38],[36,99,267,337,181,196,146,2,96,200,106,205,189],[],[[0],[0,1,2],[2,3],[2,4,5],[2,1],[0,1,2],[0,1,6],[7,3,8],[2,5],[2,1],[0,1,6],[0,9,1],[0,1,5],[0,6,9],[3,5,4],[0],[1,10],[0,11],[5,1,6],[0,1,12],[0,6,4]]),
([w0,w1,w109,w3,w9,w30,w38],[96,99,205,181,228,258,209,200,190,71,25,229],[],[[0,1,2],[2,0,3],[4,3],[5,0],[0,1,5],[0,1,6],[1,7],[0,1,6],[4,1,6],[2,8],[3,2,5],[4,0,2],[4,2],[1,4],[1,2,4],[9],[0,1,4],[0,1,5],[10,1,11],[4,1,5],[3,5]]),
([w194,w0,w1,w2,w3,w30,w38],[96,36,205,99,0,177,175,358,106,146,337,196,200,417],[],[[0],[1,2,3],[4,2,5],[1,6,7],[3,8],[1,9,3],[2,3],[2,10],[6,11],[8,3],[9,3],[3,8],[8,2],[2,9],[6,2],[9,2,12],[2,8,3],[3,2,6],[6,3,8],[6,3,13],[8,9,11]]),
([w195,w0,w1,w2,w3,w30,w38],[0,96,417,205,139,228,232,196,223,181,258,229,171,204,239,453],[],[[0,1,2],[3],[4,5,6],[5,1,7],[5,8],[2,9],[1,10],[2,1],[2,7,9],[1,10],[1,7,11],[5,12],[1,7],[5,13],[2,7],[5,1,7],[13,5,14],[2,11,5],[1,15,5],[1,9,2],[2,10]]),
([w103,w0,w1,w3,w30,w82,w38],[96,181,228,171,205,258,177,417,229,106,146,232,209,54,49],[],[[0,1],[2,3],[0,4,2],[4,2],[2],[2,1,4],[0,5],[5,1],[0,5],[6,0,7],[0,8],[0,4,9],[4,10],[11,4,12],[1,3],[0,10],[13],[0,1,3],[14],[1,3],[6,1,7]]),
([w0,w196,w1,w2,w3,w30,w38],[229,205,99,96,181,175,196,146,323,171,239],[95],[[0],[1,2],[1,3,4],[5,4,6],[3,2,100],[3,2,7],[7,1],[5,8],[5,7],[5,2],[5,2,7],[2,9,10],[3,1,6],[1,7],[4,1,5],[6,1,3],[1,9],[2,1,5],[3,2,7],[3,2,9],[4,7]]),
([w0,w1,w197,w2,w3,w30,w38],[205,258,223,0,229,96,181,146,171,196,204,216,417,199],[],[[0,1,2],[3,1,4],[0,5,1],[1,6],[5,1],[2,4],[7],[2,8],[5,0,9],[0,10,2],[6,0,1],[2,0],[2,5,11],[2,10],[2,1,12],[2,0],[0,4],[1,0,2],[2,13,5],[1,6],[2,1,6]]),
([w83,w198,w0,w1,w2,w3,w38],[99,0,96,417,353,205,146,162,181,454,204,223,108,171,239,209,175],[],[[0],[1,2,3],[4,5,6],[7,4,5],[4,2,6],[3,8],[9],[5,10,11],[5,9],[2,10],[3,11],[2,12,5],[3,2],[3,8],[2,10,6],[6,13,14],[2,5,15],[3,5,10],[6,2],[3,5,16],[2,8,3]]),
([w199,w83,w0,w1,w2,w3,w38],[0,204,181,205,223,108,146,229,163,62,171,199,106,175],[92,95],[[0,1],[2],[3,1,4],[1,5,3],[1,100,6],[4,5,6],[0,101,7],[6,3],[7,3],[6,8,9],[1,5],[3,5],[3,5],[6,7],[6,1],[6,10,7],[11,3,12],[12,1,3],[6,3,7],[1,3,13],[1,5]]),
([w83,w0,w1,w2,w3,w38,w54],[78,239,199,146,205,455,171,79,456,11,36,258,96,209,175,270,457],[],[[0,1,2],[3,4],[5,1,6],[2,7,8],[3,9,10],[10,9],[1,11],[2,12],[3,1,11],[2,1],[12,1],[1,6],[2,4,13],[14,4],[14,3],[2,1,6],[3,1,14],[14,1],[2,15],[12,2],[16]]),
([w55,w83,w0,w1,w2,w3,w38],[228,239,199,223,204,338,175,171,205,209,181,11,96,270],[],[[0],[1,2],[3,4],[1,5],[3,2,6],[7],[2,1],[0,8,9],[3,1],[0,6,2],[0,10,11],[1,5],[2,12],[3,1],[2,1],[1,5],[2,5],[6,8],[2,1,3],[3,1],[2,10,13]]),
([w200,w0,w2,w3,w9,w30,w38],[47,96,258,391,36,205,123,204,181,209,106,159,99],[],[[0,1,2],[3,4],[4,1,5],[4],[5,6,7],[2,5,4],[2,1],[2,8],[2,1],[1,2],[1,7,9],[4,5],[4],[5,10,7],[2,5,4],[11],[1,12,4],[1,6],[7,10],[2,6,4],[4,2,6]]),
([w0,w113,w2,w3,w9,w30,w38],[47,99,205,96,209,181,204,123,106,36,315,159,314],[],[[0,1],[2,3,4],[4,5],[4,3],[3,6,7],[3,4],[1,8],[3,1,4],[4,1],[2,6,7],[5,2,6],[9,2],[9],[2,10,6],[5,2,9],[11],[3,12,6],[3,5,6],[6,10],[6,5],[5,7,9]]),
([w0,w1,w114,w3,w9,w30,w38],[228,108,205,181,11,209,274,106,362,159,314,96,123,25,338],[],[[0,1,2],[2,1],[0,3],[4,3,5],[3,6],[0,1,5],[0,7,5],[5,1],[0,1,5],[0,6,1],[3,2,7],[0,1],[0,1],[0,8],[0,2],[9],[0,10],[11,1,12],[13,0,14],[0,1,4],[0,10]]),
([w0,w1,w2,w115,w9,w30,w38],[205,99,96,209,181,123,315,274,175,2,179,338,36],[],[[0,1],[0,2,3],[3,4],[3,2],[2,1,5],[2,1,3],[1,6],[2,0,3],[3,0],[0,7],[4,0,8],[9,0,2],[10],[0,6,1],[1,0,8],[5,9],[2,1,6],[2,1,5],[8,1,11],[8,1,5],[4,5,12]]),
([w0,w1,w2,w3,w201,w30,w38],[205,338,228,96,209,181,274,175,179,159,123,223],[],[[0,1,2],[0,3,4],[2,5],[4,1],[3,1],[1,4],[2,1],[3,0,1],[2,0,4],[0,6],[5,0,7],[2,0],[8],[0,1],[1,0],[9],[2,1,3],[1,5,10],[2,11],[2,5,8],[2,10]]),
([w0,w86,w1,w2,w30,w34,w38],[36,99,276,108,181,196,338,25,130,171,146,177,182,179],[],[[0],[0,1,2],[2,3],[2,1],[2,4,5],[0,1,2],[0,1,6],[2,3],[7,1,6],[2,5],[0,1,8],[0,9],[0,10,3],[0,1,5],[4,5],[1,9,3],[5,3,11],[0,12],[0],[0,9,3],[0,1,13]]),
([w202,w0,w1,w2,w3,w30,w38],[321,146,209,268,175,177,11,99,108,196,141,171,241,182],[],[[0],[0,1,2],[3,4,5],[0,1,4],[3,0],[0,1,6],[1,7],[2,8,5],[1,9],[2,7,10],[1,2,7],[1,11,12],[2,7],[2,1],[5,2],[1,8,5],[5,11],[1,13,5],[5,1],[5,7,11],[8,1]]),
([w45,w37,w0,w1,w2,w30,w38],[51,65,364,196,130,396,99,241,321,146,2,171,177,165,209,276,182],[],[[0,1,2],[1,3],[4,3],[5],[2,6,7],[2,4],[8],[6,9],[10,11,12],[0,7],[3,9],[7,6,9],[11,13,14],[13,6,15],[7,3,9],[6,11,7],[7,9,12],[12,3,14],[6,11,12],[3,16,7],[3,9]]),
([w0,w1,w203,w2,w3,w30,w38],[201,338,181,166,196,171,330,126,327,247,36,164,200],[],[[0,1,2],[0,1,2],[0,3],[0,2,4],[2,1],[1,3,5],[6],[7,0,1],[7,1],[0,8,7],[0,3,2],[0,9],[10,1],[0,7,11],[0,3,2],[3,12,4],[0,1],[0,7],[0,1],[0,2,3],[2,5]]),
([w0,w1,w2,w3,w204,w30,w38],[175,99,108,181,209,106,171,182,177,358,69,11],[],[[0,1],[0,2],[0,3,4],[0,3,4],[3,1,5],[6,1],[1,5],[4,1],[4,1],[0,7],[0,4],[6,0,2],[0,8],[0,5,1],[0,7],[9],[0,1,5],[0,1,6],[0,1,10],[0,1,11],[2,6]]),
([w0,w1,w2,w169,w30,w33,w38],[182,338,228,96,209,196,52,181,49,106,232,126,171],[],[[0,1,2],[0,3,4],[2,5,6],[3,1],[4,1],[1,4],[2,1],[0,1,3],[2,0,4],[2,0,4],[7,0,5],[0,3,5],[8,9],[10],[1,0],[2,1,3],[2,1,5],[1,11],[8],[2,12,5],[2,12,5]]),
([w167,w0,w1,w2,w30,w33,w38],[52,196,440,441,171,96,106,338,126,181,146,200,458,108,182,99],[68],[[0,1],[2,1,3],[1,4,5],[1,6,7],[1,5],[5,4,8],[5,7],[4,5,9],[5,7],[9,5],[4,1],[10,4,6],[11,10],[12,6],[6,1,9],[100,4,6],[13],[1,14,7],[15],[1,4],[1,4]]),
([w0,w205,w1,w2,w3,w30,w38],[181,330,99,108,196,126,171,36,145,164,204,202],[],[[0],[1,2],[1,3],[1,4],[5,2],[6,2],[1,2],[1,3],[7,4,8],[1,2,9],[1,2,5],[2,6,5],[5,2,4],[1,10,5],[1,4,11],[4,3,6],[1,5,2],[1,5],[1,2,10],[1,2,5],[3,5,6]]),
([w0,w1,w2,w3,w206,w30,w38],[228,99,205,108,181,0,209,141,171,204,196],[],[[0,1,2],[2,3],[0,4],[5,4,6],[4,1,7],[0,1,6],[0,8],[6,1],[0,1,6],[0,9],[4,2,7],[0,2],[0,8],[1,0,2],[0,2],[10],[0,1],[8,1],[0,9],[0,1,8],[0,8,3]]),
([w36,w0,w1,w2,w3,w34,w38],[65,99,182,25,36,130,228,338,171,166,181,126,204,209,199,229,330],[],[[0,1],[2],[1,3],[4,1],[4,1],[3,5],[6,7],[8,9],[6,10],[11,7,12],[6,9,8],[6,7],[13,7,14],[6,12],[10,8],[6,14],[9,6,7],[6,15],[16],[7,10,8],[6,8,9]]),
([w103,w0,w1,w3,w30,w33,w38],[52,181,209,171,126,25,338,199,182,177,232,54,99],[],[[0,1,2],[2,3,4],[3,5],[5,3],[5,3],[5,1,4],[1,6],[2,1],[1,6],[1,6],[3,2,6],[2,6,7],[2,8],[2,8],[1,2,3],[9,6],[10,6,11],[3,1],[12],[1,3],[1,3]]),
([w37,w0,w1,w2,w3,w33,w38],[338,126,182,99,54,106,165,209,196,406,398,25,241,171],[],[[0],[1,2,3],[4,2,5],[1,4],[3,5,4],[3,1,5],[2,3],[2,6,7],[6,8,9],[7,3,6],[6,3,7],[3,5],[2,3],[7,2],[5,2],[2,8],[10],[3,2,11],[8,3,12],[11,3,13],[8,13]]),
([w102,w0,w1,w2,w3,w33,w38],[52,181,338,99,228,54,126,165,209,199,232,229,196,171],[],[[0,1,2],[3],[2,4,5],[2,5,4],[4,5],[4,1,6],[1,2],[1,7],[4,1],[1,2],[2,8],[4,2],[7,2,9],[4,7,8],[1,8,7],[4,9],[10],[1,11,2],[4,2,12],[2,1,13],[1,13]]),
([w103,w0,w1,w3,w33,w34,w38],[282,199,209,99,228,54,398,229,338,181,165,232,171,106,166],[],[[0,1,2],[2,3],[4,1,5],[6,3,4],[5],[4,3,7],[1,3,8],[2,9],[2,1],[2,1],[1,2],[1,3,2],[2,10],[2,3],[9,2,10],[11,1,3],[5],[1,3,12],[11,3],[9,12],[13,3,14]]),
([w0,w1,w107,w3,w30,w33,w38],[228,338,52,165,209,181,199,182,363,459,460,54,171,223],[],[[0,1],[2,3,4],[0,5],[3,1],[4,1],[0,4],[0,1],[3,1,6],[0,7,3],[0,3,4],[3,4],[0,8,6],[9,0,1,10],[0,10],[0,5,7],[0,1,11],[0,1,11],[1,5,12],[13],[0,12,5],[0,12,5]]),
([w0,w1,w108,w2,w3,w33,w38],[228,338,52,181,96,229,99,182,54,171,106,232],[],[[0,1],[2,1,3],[3,4],[0,3],[3,1],[0,5],[6],[0,1],[4,1],[0,7,8],[3,7,9],[8,0,10],[0,1,4],[0,8],[0,9,3],[0,4,8],[11],[0,5],[0,1,8],[1,3,9],[0,9,3]]),
([w0,w207,w1,w2,w3,w30,w38],[54,106,99,165,196,358,171,36,205,141,11,182],[],[[0],[1,2],[0,3],[3,4,5],[0,2,1],[3,2,6],[7,1,8],[0,5],[5,4],[0,1,9],[5,2,10],[0,1],[1,2],[0,11],[1,4,8],[0,8,6],[2,1],[0,8,5],[0,2,1],[5,2,6],[0,6]]),
([w0,w1,w208,w2,w3,w30,w38],[228,338,0,181,165,196,171,99,182,232,223,239],[102],[[0,1],[2,1,3],[3,4],[0,3],[3,1],[0,5,6],[7],[0,1],[4,1,100],[0,8,4],[3,5],[0,9],[0,1],[0,10],[0,5,3],[0,11],[11,0,1],[0,8],[0,1,5],[1,3,6],[0,6,3]]),
([w90,w0,w209,w1,w2,w30,w38],[100,165,461,338,462,228,232,223,171,196,358,258,99,182,239],[],[[0,1,2],[3],[2,1],[4,5,6],[5,7],[2,8],[1,9,10],[5,11],[2,1],[1,11],[1,9,8],[12],[2,5],[2,5],[8,10],[2,1],[1,13],[1,8,13],[14,5,8],[2,13,5],[2,8]]),
([w210,w90,w0,w1,w2,w30,w38],[36,196,228,358,182,171,99,215,258,239,96,458,181],[97,102],[[0,1],[2,1,3],[4],[1,5,2],[1,100,2],[3,5,6],[7,8,9],[0,101,6],[0,2,9],[0,2,6],[0,5,1],[2,6,8],[5,10,8],[9,6,8],[2,1,5],[2,5],[2,11],[12,1],[6,2,9],[1,9,2],[1,5]]),
([w90,w0,w1,w2,w30,w38,w52],[73,165,239,36,99,228,11,182,181,106,315,171],[],[[0,1,2],[3,1,4],[2,5],[3,5,4],[3,6],[3,6],[2,4,7],[7,1,8],[1,4,9],[1,2],[1,2],[2,1,4],[1,7],[1,7],[1,4],[2,5,4],[4,2,5],[5,2],[5,10],[5,4],[11]]),
([w53,w90,w0,w1,w2,w30,w38],[175,228,196,358,182,141,337,99,165,239,171,11,463],[],[[0],[1,2,3],[4,2,5],[1,6],[1,5],[7],[0,8,9],[1,4,5],[1,0],[0,1,5],[0,10,11],[1,6,3],[3,6],[5,6],[1,9],[1,8,5],[1,4,3],[3,4],[3,1,4],[1,4],[1,10,12]]),
([w110,w1,w2,w3,w30,w33,w38],[182,258,228,165,52,54,196,171,126,209,152,25,270,99],[],[[0,1,2],[0,3,1],[1,4],[3,1],[5,1],[2,6,7],[2,3,7],[0,6,8],[2,0,3],[2,0,9],[3,0],[0,10,6],[11,0],[11],[1,0,2],[2,12,6],[2,10,6],[1,8,11],[13],[2,1,6],[2,1,6]]),
([w0,w1,w111,w3,w30,w33,w38],[228,258,165,288,182,363,361,25,270,175,337,223,126],[],[[0,1],[1,2],[0,3],[2,1],[3,1],[0,3],[0,2,3],[2,3],[0,4,2],[0,2,3],[2,1,3],[0,5,6],[7,0,4],[0,7],[0,4],[0,8,9],[0,8,10],[1,8,9],[11],[0,1,12],[0,1,12]]),
([w0,w1,w2,w3,w112,w33,w38],[228,258,165,288,182,152,199,54,232,337,11],[],[[0,1],[1,2],[0,3],[2,1],[3,1],[0,3],[0,2,3],[2,3],[0,4,2],[0,2,3],[2,1,3],[0,5,6],[7,0,5],[8],[0,4],[0,6,7],[0,5,9],[1,5,6],[0,7],[0,1,5],[0,1,10]]),
([w0,w1,w2,w3,w30,w211,w38],[228,337,175,288,126,165,182,232,358,223],[],[[0,1,2],[2,1],[0,3],[3,1,4],[2,5,3],[0,3],[0,5,3],[4,1,5],[0,6,2],[0,1,3],[1,3],[0,1],[2,0,6],[7],[0,4],[0,1],[0,2,8],[2,4],[9],[0,4],[0,4]]),
([w212,w1,w2,w3,w30,w33,w38],[228,182,258,25,126,288,165,152,464,270,164],[],[[0,1,2],[2,1,3],[0,4,5],[3,2],[3],[0,5],[4,6,5],[1,5],[3,1],[4,1,5],[3,1],[1,7,8],[3,1],[3],[2,1,3],[3,9],[8,7],[2,4,3],[10],[8,2],[3,2,4]]),
([w0,w1,w92,w2,w3,w34,w38],[25,258,232,99,166,239,204,199,338,181],[],[[0,1,2],[0,1,3],[0,4],[0,5,1],[0,1,6],[2,4,5],[0],[2,4],[7,8],[2,6],[0,1,9],[2,4],[2,3],[2,6],[0,1,9],[2,5],[4,5],[0,5],[0],[0,9,1],[0,1,4]]),
([w213,w0,w1,w2,w3,w30,w38],[0,199,165,203,465,228,232,258,181,239,338,204,173],[],[[0,1,2],[3],[4,5,6],[4,1,3],[3,5],[3,4],[1,7],[1,2],[2,8],[2,1],[1,9],[6,2,10],[1,10],[2,11,6],[2,7,8],[1,9,6],[9,10],[6,9],[6,1,12],[1,8,7],[6,7,8]]),
([w46,w102,w0,w1,w2,w3,w38],[25,36,435,130,258,239,204,228,199,173,203,54,232,238,165,166,196,181],[],[[0,1,2],[3,4,5],[1,6],[7],[1,8,9],[1,3],[0,5,4],[10],[11,5,12],[9,8],[0,13],[5,4],[4,14],[4,5],[8,5],[5,14,15],[8,16],[9,4,17],[8,5,12],[4,5,9],[4,17]]),
([w103,w0,w1,w3,w30,w38,w47],[58,199,165,288,466,25,36,11,292,177,182,270,152,181],[],[[0,1,2],[2,3],[4,1,5],[5,6],[5,7],[5,7],[1,8,9],[2,3],[2,1],[1,3],[1,2],[1,3,2],[2,10],[2,3],[8,2],[9,1],[1,11],[1,11],[8,12],[8,12],[13]]),
([w0,w1,w2,w3,w30,w214,w38],[358,258,228,165,181,239,288,182,199,223],[],[[0,1,2],[0,3,1],[0,4,1],[3,1],[0,1,4],[2,5],[2,3,6],[3,6],[0,7],[2,3,6],[0,1,4],[2,5],[0,2,7],[0,2],[0,5],[0,8],[0,8],[0,4,1],[9],[2,1,4],[0,1,4]]),
([w0,w1,w2,w3,w215,w30,w38],[223,258,165,181,239,288,182,199,99],[],[[0,1],[1,2],[0,3],[1,2],[2,1],[0,4],[0,2,5],[2,5],[0,2,6],[0,6,2],[2,1,3],[0,4],[0,4],[4,6],[0,4],[7],[0,8],[1,3],[0,8],[0,3,1],[0,1,3]]),
([w1,w2,w3,w98,w30,w47],[288,239,36,165,54,49,99,182,25,292,58,295,289,11,199,293],[8,27,53,34,28,32,14,0,16,54,6],[[0,1,2,3,100,4],[2,5,101,102],[2,6,103,7,8],[0,2,4,104],[2,0,100,9,105],[2,4,106],[4,8,107],[1,4,5,108],[2],[2,8,10],[2,4,109],[2,11,106,12,101],[0,4,6,10,8],[8,0,13,14,15],[4,11,108,9,110]]),
([w0,w2,w3,w99,w30,w47],[181,295,25,165,54,36,271,49,467,289,468,11,293],[0,24,34,6,52,38,14,8,16,54,27],[[0,1,2,3,100,4],[2,0,101,3,5],[0,1,2,5,102],[0,1,4,2,103,104],[2,3,100,6,105],[4,5,106],[4,5,107],[2,4,108,7],[2],[5,7,8,1],[2,5,109],[5,1,106,9,110],[2,5,10],[5,1,11,9,12],[2,1,108,6,103]]),
([w0,w1,w3,w100,w30,w47],[181,36,25,165,54,271,49,289,469,152,470],[34,24,0,6,52,38,27,53,8,28,32,54,14,16],[[0,1,2,100],[1,2,101],[0,2,3,102,4],[0,2,4,103,104],[2,3,102,5,105],[1,6,106,107],[1,3,108,4],[1,2,109],[1,3,108,7,110],[1,4,8],[1,2,111],[1,9,112,7,106],[2,4,10,6],[1],[2,9,113,5,103]]),
([w216,w0,w1,w2,w3,w30],[0,25,165,199,293,36,11,54,49],[0,8,34,24,6,52,27,53,28,14,16,54],[[0,1,2,100,3,4],[4,5,101],[1],[4,5,6],[1,4,6],[1,5,102],[1,2,100,3,4],[1,5,103],[1,7,104,105],[4,5,101],[2,3,8,5,106,107],[1,5,108],[4,5,109],[1,4,110],[1,5,111]]),
([w37,w0,w1,w2,w3,w30,w47],[181,165,182,54,58,374,372,293,11,99,209,196,292,205,399,204,130],[],[[0],[1,2],[3,2],[4,3],[3,5,6],[7,8],[2,9],[2,1,10],[1,11,5],[1,9,5],[5,1,9],[9,1],[1,9],[1,2],[12,1],[2,13],[9,2,13],[14],[11,5,15],[15,9],[11,16,12]]),
([w102,w0,w1,w2,w3,w30,w47],[58,181,165,99,54,239,471,472,130,189,293,258,199,209,196,204,36,229],[],[[0,1,2],[3],[4,5],[6,4,7],[4,8,9],[10,1,8],[1,11],[1,2],[2,1],[1,11],[12,2],[5,2,13],[2,14,8],[2,15,8],[1,2,11],[12,5,16],[5,17],[16],[14,8,12],[11,1],[1,8,11]]),
([w103,w0,w1,w3,w30,w34,w47],[296,181,165,99,36,199,54,25,130,258,182,232,166],[54],[[0,1,2],[2,3],[4,5,6],[7,3,4],[6],[4,1,8],[1,3,9],[2,1],[1,3,5],[2,1],[5,2],[2,3],[2,10],[2,3],[1,2,9],[100,5,3],[6],[5,1,9],[11],[1,9],[12,1]]),
([w103,w0,w1,w3,w30,w47],[58,165,199,36,99,152,25,232,11,166,177,258,181,141,185,88,182,129,67],[38,0,32,8,34,4,10,14,16,81,75],[[0,1,2,100,101],[3,1,4,102,103],[3,5,6,2],[6,5,3,4],[3,7,8,4,9],[2,10,100,11,4,104,102],[1,10,100,12,105],[1,13,101,2,4,100],[2,10,14,1,4,9],[1,2,103,4,15,102],[1,7,102,16,106],[13,7,17,1,9],[10,7,107,2,4,18,108],[2,7,9,5,4,107,109],[13,9,5,11,108,110]]),
([w0,w106,w1,w2,w3,w30,w47],[165,297,99,181,36,182,239,293,11,106,25,166,292],[],[[0],[1,2],[1,3],[1,3,4],[1,2],[1,2],[4,2,5],[5,6],[1,4],[1,2],[7,2,8],[2,9],[5,2],[4,5,10],[3,5,11],[4,6],[2,5,6],[4],[4,2],[4,2],[3,9,12]]),
([w0,w1,w108,w2,w3,w30,w47],[36,258,58,181,96,25,166,54,196,182,239,88],[],[[0,1],[2,1,3],[1,4],[0,3],[3,1],[5,4,6],[5],[0,7],[4,8],[0,9,5],[0,1],[7,9,10],[0,8,4],[0],[3,1],[0,4,7],[5,9],[0],[0,11,4],[0,3],[3,1]]),
([w0,w1,w2,w3,w30,w217,w47],[36,258,165,239,293,88,130,182,25,289],[],[[0,1],[1,2],[0,3],[2,1],[2,1],[4,2],[0,2,4],[2,5,6],[0,7,2],[0,7,2],[0,1],[0,3],[3,7],[4,3,8],[0],[0,5,9],[0,5,8],[0,6,4],[0],[4,1,6],[4,1,6]]),
([w0,w1,w2,w3,w30,w214,w47],[182,258,239,165,293,88,189,289,358],[],[[0,1,2],[0,3,1],[1,2],[2,1],[2,1],[4,2],[2,3,4],[0,5,6],[3,0],[6,0,7],[4,0],[0,2],[2,0],[2,0],[8],[7,5],[7,5],[1,6,4],[4],[4,1,6],[4,1,6]]),
([w0,w1,w2,w3,w30,w218,w47],[182,99,165,293,239,130,36,25,270],[],[[0,1],[0,2,3],[2,4],[2,1,5],[2,4],[3,1,2],[1,2],[0,1],[2,0],[2,0],[3,0],[0,4],[1,0,4],[3,0,6],[7],[7,1,8],[3],[3,1,5],[5,6],[3,5],[3,1,5]]),
([w0,w1,w2,w3,w215,w30,w47],[182,99,165,293,239,58,258,175,96,271,254],[],[[0,1],[0,2,3],[2,4],[5,2,6],[2,1,6],[3,1,2],[1,2],[0,1],[0,1],[2,0],[3,0],[0,4],[0,4],[1,0,4],[7],[3],[8,1,9],[3,1,6],[9,1],[3,1,6],[3,6,10]]),
([w0,w1,w3,w100,w30,w219],[25,258,239,36,165,54,271,49,289,123,96,126,152],[34,24,0,6,52,38,27,53,8,28,32,54,14,16],[[0,1,100,2,3],[0,2,101,1,3],[0,4,102,1,5],[0,5,103,104],[0,2,102,6,105],[3,7,106,107],[3,4,108,5],[0,3,109],[3,4,108,8,110],[3,5,9],[0,3,111],[3,10,112,8,106],[0,5,11,7],[0],[0,12,113,6,103]]),
([w0,w1,w220,w2,w3,w30,w38],[203,258,241,166,196,130,171,173,332,182,54,129,253,205],[],[[0,1,2],[0,1,2],[0,3],[0,4],[5,1,2],[2,3,6],[7],[2,3],[5,0,4],[0,8,2],[0,1,9],[10,3,11],[0,12],[0,2],[0,1,5],[2,13],[0,6],[0,5],[0,5,2],[0,5],[2,1,3]]),
([w0,w1,w2,w221,w3,w30,w38],[175,99,165,209,196,141,182,177,11,106,152],[],[[0,1],[0,2,3],[0,2,3],[0,4],[2,1,5],[2,1,3],[1,2],[1,2],[2,1],[0,6],[0,3],[7],[4,0,6],[0,6],[0,6],[0,4],[0,5,1],[0,8],[0,1,9],[0,1,10],[4,10,5]]),
([w0,w222,w1,w2,w3,w30,w38],[165,173,99,166,196,130,321,239,54,171,189,204,129],[],[[0],[1,2],[1,3],[1,4],[5,2],[6,2,7],[1,2],[8,3,9],[1,4],[1,2,10],[1,2,5],[2,3,5],[5,2,1],[1,11,5],[1,3,12],[3,7],[1,9],[1,5],[1,2,6],[1,2,3],[3,5,6]]),
([w0,w1,w2,w223,w3,w30,w38],[228,258,165,196,239,209,96,204,232,11,88,152],[],[[0,1],[1,2],[1,2],[0,3,4],[2,1],[0,3,4],[0,2,5],[0,2,5],[2,3,6],[0,7],[2,1,5],[8],[0,4],[4,0,7],[0,4],[0,6,3],[0,7],[0,9],[0,10,3],[1,11,6],[0,1,3]]),
([w0,w224,w1,w2,w3,w30,w38],[165,177,258,99,166,196,141,199,288,11,106,204,146,337],[],[[0],[1,2,3],[1,4],[1,5],[6,2,3],[7,3,8],[9,3,10],[1,4],[1,5],[1,3,10],[1,2,9],[3,4,10],[7,3,5],[1,11,12],[1,2,8],[4,13],[1,10,3],[1,2],[1,3,7],[1,3,2],[4,2]]),
([w0,w1,w225,w2,w3,w30,w38],[232,258,0,96,196,288,165,166,204,141,11,171,99],[],[[0,1],[2,1,3],[1,3],[0,4,5],[3,1],[0,4,5],[6],[0,7],[3,4],[0,8],[9,1,5],[0,7],[0,4,3],[0,8],[0,1,10],[0,3,4],[7,11],[0,1],[0,9],[1,12],[0,1,4]]),
([w226,w0,w1,w2,w3,w30,w38],[0,258,165,141,228,25,11,232,288,146,96,106,238],[],[[0,1,2],[2,3],[4],[4,5],[5,3,4],[4,1,6],[3,1,7],[1,2],[1,8],[2,1],[2,8],[3,2],[2,3],[2,9],[2,1,8],[7,10,9],[3,11],[1,12,7],[7,3],[1,12,10],[3,1,12]]),
([w227,w0,w1,w2,w3,w30,w38],[0,288,165,123,51,160,232,435,99,106,182,96,54,179],[],[[0,1,2],[2,1],[3],[4,3,5],[6,7],[6,3],[6,8,9],[1,2],[2,1],[1,8,9],[2,1],[1,2],[2,1],[1,10],[2,1],[6,11,12],[8,9],[6,10],[6,8],[11,8,13],[6,13]])]
noncomputable def p20_D5 : List StD := [
([w4,w5,w3,w32,w33,w38],[126,165,288,196,438,54,182,146,41,96,164,106],[],[[0,1,2],[0,3],[0,4,1],[0,1,5],[1,3,6],[6,3,7],[8,0,6],[0,8],[7,0,3],[9,3],[3,7],[9,0],[0,10],[11,0],[3,0,7]]),
([w1,w5,w3,w56,w33,w38],[126,99,146,196,334,204,25,182,54,165],[14],[[0,1,2],[0,1,3],[4],[0,2,5],[6,3,7],[2,3],[8,0,9],[0,1],[2,0,1],[9,2,100],[3,1,2],[5,0,1],[0,1],[6,0],[3,0,2]]),
([w4,w7,w6,w9,w30,w38],[47,473,391,165,288,11,196,99,123,31,96,175,204,202,106],[],[[0,1,2],[3,4],[5,3,6],[3,7,8],[3,4],[9,7,10],[5,6],[11,12,13],[11,6,8],[1,6],[10,7,14],[10,6,8],[6,7,12],[12,5,7],[6,8,14]]),
([w4,w2,w6,w32,w34,w38],[130,166,288,165,474,196,25,182,99,239,41,146],[],[[0,1],[0,2,3],[0,4,2],[0,2,5],[6,1,2],[7,1],[8,1,9],[1,7],[5,0,6],[10,0,11],[0,5],[6,0],[0,5],[6,0],[1,0,6]]),
([w159,w4,w2,w3,w30,w38],[220,203,173,99,182,166,11,130,189,196,239,146],[],[[0,1,2],[3,4,5],[2,6],[0,7,8],[1,6],[7,5],[4,9,7],[2,3,4],[2,3,4],[4,10],[2,4],[2,4],[2,3,11],[2,3,5],[5,7,11]]),
([w0,w7,w12,w9,w30,w38],[227,99,36,210,196,414,54,182,475,204,202,11,123],[16],[[0,1],[2],[3,4],[5,1],[2,1,5],[6,1,7],[2],[8,9,10],[2,4,10],[6,4,11],[6,1,100],[2,1,12],[4,1,9],[2,1,9],[2,12]]),
([w228,w0,w1,w2,w3,w38],[0,99,219,204,220,239,182,25,196,11,476,166,202],[],[[0,1],[2,3,4],[1,5,6],[3,1],[7,8,9],[5,1,6],[6,10,11],[10,5],[10,1,5],[1,11,5],[6,1],[12,3],[6,5],[1,5,10],[3,1]]),
([w229,w0,w1,w2,w30,w38],[0,196,215,100,166,239,202,99,182,106,146,204,337],[],[[0,1],[2,1,3],[1,4,5],[1,6,7],[7,4],[5,7,8],[8,4],[5,6,9],[10,1],[5,4],[6,8,11],[6,1],[4,8],[1,5,12],[1,10]]),
([w230,w0,w1,w3,w30,w38],[0,166,138,246,196,239,99,182,337,146,106,202,204],[],[[0,1],[2,1,3],[1,4,5],[1,6,7],[8,4,5],[5,6,7],[9,4],[5,6,10],[9,1],[7,4,6],[11,7,12],[8,1,7],[4,6,9],[1,6],[1,9]]),
([w231,w0,w1,w2,w3,w30],[0,99,202,166,337,182,146,106,159,196,204,318],[],[[0,1],[2,3],[1,4,5],[2,1],[3,4,6],[7,1],[8,4],[8,9],[7,1],[1,7],[7,1],[2,10],[9,4,11],[1,7],[2,1]]),
([w232,w0,w1,w2,w3,w30],[0,99,182,146,106,318,353,241,337,164,196,201,204],[],[[0,1],[2,3,4],[1,5,2],[5,1],[6,3,7],[2,1],[2,8],[9,10],[9,1],[1,11,9],[2,1],[9,2,11],[2,8],[1,2,11],[10,1,12]]),
([w1,w5,w6,w33,w34,w38],[228,106,146,99,318,166,126,196,182,239,14,54,25,171],[],[[0,1,2],[1,3],[4,1,5],[6,2,7],[1,5,8],[0,9],[9,3,8],[10,1],[0,3,2],[11,2],[1,2,7],[12,3,13],[4,1,3],[4,2,7],[1,2,5]]),
([w1,w5,w3,w33,w61,w38],[477,106,146,196,99,355,166,478,352,182,65,54,367],[],[[0,1,2],[1,3,4],[5,1,6],[7,2,8],[1,3,9],[0,3,2],[10,4],[11,1],[0,3,2],[3,2],[12],[6,4],[11,1],[3,2],[1,2,8]]),
([w1,w5,w6,w30,w34,w47],[36,99,146,182,25,11,196,141,239,14,171,372,166],[],[[0,1,2],[3,1],[4,2],[5,1,6],[7,3],[0,8],[4,1,3],[9,3,6],[0,1,2],[4,1,2],[4],[10,1],[11],[4,2],[12,1]]),
([w50,w1,w5,w6,w30,w47],[182,196,11,239,373,374,318,181,106,146,288,25,171],[],[[0,1,2],[0,1,3],[4],[5],[6,2,7],[3,8,9],[0,10],[6,0,10],[6,0,1],[0,3],[3,0],[6,0],[8,9,11],[12,1],[1,8,9]]),
([w1,w5,w3,w30,w61,w47],[321,99,146,182,25,318,352,141,196,54,165,372],[],[[0,1,2],[3,1],[4,2],[5,1,6],[7,3],[0,8,2],[4,1,3],[9,3,10],[0,1,2],[4,1,2],[4],[6,1],[11],[4,2],[6,1]]),
([w62,w1,w5,w3,w30,w47],[146,288,333,58,373,374,196,165,181,182,171],[],[[0,1],[2,1],[0,3,4],[5],[0,6],[0,7],[7,1],[1,0],[8,1,6],[0,1,2],[1,9],[0,1,2],[6,0],[10,8],[6,0]]),
([w60,w50,w1,w2,w6,w38],[36,196,288,165,182,68,479,108,389,171,25],[],[[0,1,2],[0,3,4],[2,5],[6,2,3],[0,1,2],[3,1,2],[1,7,4],[8],[9,7],[2,3],[4,2],[3,1,2],[4,3,7],[1,4,10],[3,1,9]]),
([w125,w62,w1,w5,w3,w38],[54,476,165,480,182,402,337,189,288,162,196,171,481,181],[],[[0,1,2],[3,2,4],[5],[3,6],[3,7],[4,8],[0,2],[0,9],[2,10,11],[12,2,11],[2,8],[2,4],[4,8],[12,4],[11,13]]),
([w1,w3,w15,w31,w33,w38],[182,196,288,354,171,478,175,361,355,181,264],[],[[0,1,2],[3,2,4],[5,0,6],[2,0],[6,0],[7],[5,1,2],[1,6,8],[4,9],[6,0],[6,0],[3,0],[2,10],[5,1,2],[1,4]]),
([w16,w1,w3,w31,w33,w38],[354,171,363,181,25,154,364,182,288,358,478,355,146,365],[],[[0,1],[2],[3,1,4],[5,1,6],[0,7],[7,8],[3,7,9],[8,7],[3,1],[9,3,10],[11,12,9],[1,3],[3,13],[10,1,8],[3,1]]),
([w233,w0,w1,w2,w3,w38],[0,181,337,482,288,146,247,239,182,36,196,171],[],[[0,1,2],[3,4,5,6],[3,7,8],[5,2,9],[2,1,5],[1,2,5],[1,2,8],[5,1,10],[5,7,10],[5,11,7],[8,2],[1,8,2],[5,2,8],[1,7,2],[11,1]]),
([w0,w1,w15,w33,w34,w38],[449,483,258,181,196,228,171,318,146,288,165,25,182,175,450],[],[[0,1],[2],[0,1],[0,3,4],[0,4],[5,1,6],[7,8,9],[10,1],[1,4,3],[11,1,6],[11,4,6],[5,3,12],[4,1,7],[1,6,3],[13,3,14]]),
([w130,w0,w1,w5,w3,w47],[58,165,337,318,146,484,485,11,25,181,196,141,171],[],[[0,1,2],[3,1,4],[5,2,6],[3,2],[4,7,8],[4,2],[9],[1,10,4],[4,1,2],[4,1],[1,2],[11,1],[4,10],[4,2],[12,2]]),
([w139,w0,w1,w3,w30,w47],[181,36,146,165,25,177,337,196,141,171],[],[[0],[1,2,3],[1,2,4],[4,1],[1,2,5],[2,6],[2,7],[3,6,8],[2,3,6],[3,6],[3,2],[8,3],[5,2],[9,6],[5,2]]),
([w106,w1,w5,w3,w30,w47],[318,337,146,262,58,372,165,196,25,182],[],[[0,1,2],[0,3],[0,4],[4,1,5],[2,0,1],[0,1,2],[6,1],[0,2,6],[0,6,7],[0,7,2],[8,1,9],[0,2],[0,1],[0,1],[7,2]]),
([w130,w0,w1,w2,w3,w38],[0,165,337,36,146,162,175,177,196,182,181,171],[],[[0,1,2],[3,1,4],[5,6,7],[3,2],[2,8,4],[4,2],[6,1,2],[1,8,4],[1,8,4],[4,1],[1,2],[1,8,9],[4,2,9],[2,9],[6,10,11]]),
([w1,w6,w9,w31,w33,w38],[182,483,126,171,175,321,288,361,228,54,258,196],[],[[0,1],[2,1,3],[4,0],[5,0,6],[1,0],[0,4,7],[4,6,8],[9,1,10],[3,11],[4,0],[4,0],[4,0],[4,1],[8,3,6],[1,3,11]]),
([w0,w1,w9,w33,w61,w38],[449,483,196,165,486,321,182,288,228,352,25,54,106,487],[],[[0,1],[0,2],[0,1],[3],[0,2],[4,1,2],[5,6,7],[8,1,9],[1,2,6],[2,1,5],[10,2],[9,4,10],[11,1,12],[1,13],[8,2,9]]),
([w125,w62,w0,w1,w9,w38],[54,387,106,337,182,200,177,488,223,288,489,258,181,490,196,491],[],[[0,1,2],[2,3],[4,5],[6],[2,7],[0,8],[2,9],[0,5],[5,10],[2,11,12],[4,9,11],[13,9,14],[15,2,14],[2,4],[6,4]]),
([w199,w83,w1,w2,w6,w38],[0,288,196,182,204,223,108,165,68,62,106,175,352],[],[[0,1,2],[3,4,5],[1,6,3],[7],[5,1],[3,1],[2,6,3],[8,2,9],[4,6],[1,10],[3,1],[10,1],[3,6],[2,3,11],[11,2,12]]),
([w103,w0,w1,w6,w30,w47],[58,196,11,466,369,36,177,99,232,288,106,182,181,352,171],[],[[0,1],[2,1],[3,1,4],[1,5],[5,2],[6,7],[8],[9,7,10],[6,1],[10,7],[6,11],[12,1],[6,7,10],[13,1],[1,10,14]]),
([w146,w0,w1,w3,w30,w47],[58,288,165,466,25,369,182,99,106,177,181,171],[],[[0,1,2],[2,1],[3,4,5],[4,6],[4,6],[6,7],[2,1],[1,7,8],[9,1,7],[2,1],[1,6],[10,1,11],[8,7],[11,7],[9,8,11]]),
([w0,w1,w63,w33,w34,w38],[449,99,181,258,165,36,352,182,25],[],[[0,1],[0,2,3],[0,1],[0,3,4],[0,1],[1,4],[5,4,6],[4,1],[4,3,7],[1,7,8],[8,7],[1,7,8],[5,1],[5,3,6],[6,1]]),
([w0,w1,w9,w64,w33,w38],[492,258,228,165,108,352,182,25,223],[],[[0,1,2],[0,3,1],[0,1,3],[0,1,4],[0,4],[2,3,5],[2,6,3],[2,3,5],[3,1,6],[7,2,6],[2,4],[1,4],[2,8],[2,1,4],[2,1,5]]),
([w150,w0,w1,w3,w30,w47],[58,258,165,146,466,25,36,177,232,196,357],[],[[0,1,2],[2,3],[4,3,5],[5,6],[5,1,7],[3,1,8],[1,9,3],[2,1],[3,2,9],[2,9,10],[2,3],[8,1],[7,3],[1,10],[7,1]]),
([w103,w39,w0,w1,w30,w47],[466,25,369,258,165,196,36,177,181,141,232,200,199,182],[],[[0,1,2],[0,3,4],[4,5,6],[1,6],[1,3,7],[8],[4,9],[7,9,10],[3,11,12],[7,3,10],[4,3],[7,4,5],[4,13],[9,3,4],[5,3]]),
([w234,w0,w1,w2,w30,w38],[0,165,181,215,196,182,108,228,223,258,146,337],[],[[0,1,2],[3,1,4],[4,5,6],[4,7,8],[2,9],[2,6,5],[2,1],[1,9],[1,4,10],[10,1],[1,5],[1,4,2],[6,5],[2,5,11],[2,9]]),
([w0,w1,w68,w9,w33,w38],[493,108,181,165,209,25,448,358,241,228,352,146],[],[[0,1],[0,2,3],[0,2,4],[0,1],[0,1],[3,1],[4,1],[4,3],[2,4,3],[5,6,7],[8,1],[9,1,10],[5,1,8],[5,1,10],[2,11]]),
([w158,w0,w1,w3,w30,w47],[58,181,165,146,466,25,36,177,99,141,352],[],[[0,1,2],[2,3],[4,3,5],[5,6],[5,1,7],[1,8,3],[2,1],[1,8,9],[3,2,8],[2,8],[2,3],[1,2,9],[7,3],[10,1],[1,3]]),
([w0,w8,w9,w30,w69,w38],[494,181,228,495,258,496,171,146,182,223],[],[[0,1,2],[3,1,4],[1,4],[1,4],[2,5,6],[2,6],[0,7],[2,5],[0,1,8],[3,2,6],[2,5],[2,1,4],[9],[1,4],[1,4]]),
([w70,w0,w8,w9,w30,w38],[227,165,108,36,223,435,228,196,181,497,258,171,146,182],[],[[0,1,2],[3,1,2],[4,5],[6],[3,7,8],[4,8],[9,1,7],[1,10],[1,7,11],[4,1,7],[1,12],[1,7,13],[7,11],[4,8,10],[4,10,7]]),
([w0,w7,w9,w30,w72,w38],[498,165,108,497,258,212,417,496,146,36,54],[],[[0,1,2],[3,1,4],[1,4],[5,4,6],[1,7,8],[9],[0,8],[10,1],[0,4,6],[3,8],[10,1],[3,7,4],[9],[6,4],[1,4,6]]),
([w0,w7,w3,w30,w72,w47],[146,165,357,181,258,213,417,496,36,54,196,254],[],[[0,1,2],[0,3,1],[1,4],[5,3,6],[0,1,7],[8,2],[2,0],[9,0,1],[3,4],[8,0,10],[11],[4,3],[8],[3,0],[6,0]]),
([w0,w7,w9,w32,w34,w38],[499,108,500,165,258,501,181,204,146,36,31,41,123],[],[[0,1],[2,3,4],[5,4,6],[3,4],[3,7,8],[9],[1,3,8],[10,1,7],[6,4],[11,3,8],[7,8,11],[4,6],[3,7,9],[3,4,6],[9,4,12]]),
([w0,w7,w3,w32,w34,w47],[502,258,181,503,165,500,204,36,239,146,31,141,254,417],[],[[0,1,2],[1,2],[2,1],[3,1,4],[5,4,6],[7,8],[8,4,9],[10,6],[2,1],[4,9,11],[12],[1,2],[4,6,7],[2,1],[13,1]]),
([w51,w0,w7,w3,w32,w47],[503,258,165,31,204,146,36,181,504,196,239,141],[],[[0,1,2],[3,4],[5],[6],[7,1],[7,1],[1,7],[7,1],[8,2,4],[6,9,10],[10,2,11],[6],[2,9,11],[1,7],[7,1]]),
([w78,w0,w7,w3,w30,w47],[213,258,181,357,165,31,146,171,496,36,204,182,141],[],[[0,1,2],[3,4,5],[6],[4,5],[2,1],[2,1],[1,2],[2,1],[7,4,8],[9,3],[3,10,11],[2,1],[9,12],[1,2],[2,1]]),
([w21,w51,w0,w2,w32,w38],[31,146,204,165,181,36,108,258,171,432,239],[],[[0,1,2],[1,3,4],[1,5],[6,1,3],[4,2],[3,2,7],[0,8,6],[5],[4,7],[4,3],[4,6,7],[3,2,8],[9,3],[2,10,5],[3,2,4]]),
([w124,w78,w0,w7,w30,w38],[146,171,165,432,36,505,254,258,181,496],[],[[0,1,2],[1,2,3],[4],[3,1,5],[0,6,4],[0,7,8],[3,2],[2,0],[2,1,8],[0,2,3],[2,7],[0,9],[3,0,9],[3,1],[4,0,8]]),
([w0,w1,w9,w69,w34,w38],[146,258,228,181,165,239,171,54,31,450],[],[[0,1,2],[0,3,1],[3,1],[4,1],[0,5,2],[2,4,6],[7],[2,0,4],[3,1],[2,5],[8,0,7],[1,3],[2,5],[2,0,3],[2,0,9]]),
([w167,w0,w1,w7,w30,w47],[213,165,181,506,54,36,31,171,258,204,146,432],[],[[0,1,2],[3,1,4],[5,4],[4,6],[2,7],[2,8],[2,1],[1,8],[7,1,9],[10],[1,9,11],[2,1,7],[11,9],[2,7],[2,7]]),
([w172,w0,w1,w3,w30,w47],[58,181,258,146,36,54,171,204,165,196,199,232],[],[[0,1,2],[3],[4,5],[5,4],[2,1],[1,2],[2,1],[1,2],[6,7],[8,9,10],[8,7,11],[1,2],[7,10,9],[2,1],[1,2]]),
([w0,w108,w7,w3,w30,w47],[213,258,181,171,165,204,54,146,254,36,196,239,182,88],[],[[0,1,2],[2,1],[1,2],[2,1],[3,4,5],[6],[4,7,8],[4,5,8],[2,1],[9,10,11],[6,5,12],[2,1],[5,13,6],[1,2],[2,1]]),
([w167,w0,w1,w2,w30,w38],[0,196,215,100,171,232,228,223,11,258,165,146,182,204,239],[],[[0,1],[2,1,3],[1,4,5],[1,6,7],[5,4,8],[6,9],[4,10,9],[10,9],[4,1],[6,4],[6,11,10],[10,1,12],[13,4,14],[1,12,6],[1,4]]),
([w0,w8,w9,w32,w33,w38],[507,239,228,508,196,258,509,204,146,165,175,182,41,181],[],[[0,1,2],[3,1,4],[1,5],[6,5,7],[2,1],[2,4],[2,8,9],[2,1],[10,4,11],[12,2,4],[2,1],[2,11],[1,2,7],[2,4,13],[2,1]]),
([w0,w1,w9,w33,w72,w38],[146,258,228,239,181,264,417,196,204,165,41],[],[[0,1,2],[0,3,1],[4,1],[5,1,6],[0,3,2],[2,7],[2,0,8],[9],[4,1],[2,3],[10,0],[1,4],[2,3],[2,0,3],[2,0,6]]),
([w176,w0,w1,w3,w30,w47],[58,181,165,146,466,239,204,36,258,196,199],[],[[0,1,2],[2,3],[4,3,5],[5,6,7],[7,1,5],[1,8],[2,1],[1,6,8],[3,2,6],[2,9,10],[2,3],[1,2,6],[6,3,9],[6,1],[1,3]]),
([w0,w1,w9,w75,w33,w38],[239,258,264,165,181,228,196,146,352],[],[[0,1],[1,0],[2,0,3],[4,1],[3,0],[5,3,6],[3,7],[0,3,8],[3,1,4],[6,5,7],[5,0],[1,4],[5,0],[5,1,6],[4,0,1]]),
([w179,w0,w1,w3,w30,w47],[58,258,165,146,196,510,36,485,239,199,232,181],[],[[0,1,2],[2,3],[4,3],[5,6,7],[4,1],[3,1,8],[1,4,3],[2,1],[3,2,4],[2,4,9],[2,3],[10,1],[4,3],[1,11],[4,1]]),
([w124,w78,w0,w1,w33,w38],[196,228,41,239,144,171,232,182,365,181,258,204],[],[[0,1,2],[3,4],[1,5],[6],[0,7,1],[3,0,8],[1,0],[0,1],[1,5,9],[1,10],[9,4],[1,0,3],[1,7,11],[9,0],[0,3,1]]),
([w210,w90,w0,w2,w32,w38],[36,204,228,196,258,171,165,181,232,108,239],[],[[0,1],[2,3,4],[2,5],[6],[7,1],[7,1,4],[0,2,8],[0,1],[0,4,3],[4,9,5],[7,4],[2,1,5],[10,2,5],[1,10,2],[2,1,7]]),
([w103,w0,w1,w3,w32,w47],[420,181,204,36,239,258,171,182,88,199,165,232,141],[],[[0,1,2],[3,2],[2,4],[4,2],[3,1,4],[1,5],[5,1],[1,5],[6,2],[7,8,9],[10],[1,2],[11,8,12],[2,1],[1,2]]),
([w0,w1,w79,w9,w34,w38],[228,258,165,239,352,204,181,196],[],[[0,1],[1,2],[1,2],[2,1],[0,3],[0,2,4],[0,2,4],[0,5],[2,1,6],[0,3],[0,3],[0,3],[5,0,7],[0,6,1],[0,1,4]]),
([w0,w1,w80,w9,w33,w38],[228,258,239,181,182,165,171,204,196],[],[[0,1],[1,2],[1,2],[3,1],[0,2],[0,4,5],[0,5,6],[0,5,7],[3,1],[6,0,8],[0,2],[0,3,1],[0,2],[0,3,1],[0,1,2]]),
([w188,w0,w1,w3,w30,w47],[58,181,165,141,466,239,369,36,258,171,204,232],[],[[0,1,2],[2,3],[4,5,6],[5,3,7],[7,1,5],[1,8],[2,1],[1,8],[9,2,10],[2,3],[2,10,11],[1,2,3],[10,3],[8,1],[1,8]]),
([w103,w43,w0,w1,w3,w47],[232,435,511,204,239,199,182,141,106,258,88,181],[],[[0,1],[2,3],[0,3],[0,4],[0,4],[4,5],[6],[0,5,7],[3,8,7],[0,9],[0,4],[5,3,4],[5,10],[0,3],[0,11]]),
([w24,w0,w1,w33,w34,w38],[239,228,141,88,262,196,106,182,258,108,449,352],[],[[0],[1,2,3],[4,1,2],[5,3,6],[1,7],[2,8,9],[2,8,9],[6,5],[10,5],[4,6,11],[11,2],[2,5,7],[4,2],[2,8,5],[6,8,11]]),
([w235,w0,w1,w2,w3,w38],[0,239,88,108,182,141,36,258,352,171,181,337],[],[[0,1,2],[0,3,4],[4,1],[2,5,6],[2,3],[1,2],[2,3,4],[7,1],[8,1,3],[1,9],[4,2,3],[10,2],[2,1,4],[2,1,11],[7,3]]),
([w36,w0,w1,w9,w34,w38],[266,108,182,36,239,258,417,228,88,204,196,181],[],[[0,1],[2],[3,1],[3,1],[3,4],[4,5],[5,4],[6,4],[7,4],[7,8],[7,9],[6,5],[9,7,10],[5,11],[6,5]]),
([w37,w0,w1,w9,w33,w38],[258,228,182,352,196,241,141,171,108],[],[[0],[1,2,3],[4,2],[5,1,6],[1,7,3],[2,8],[2,4],[6,8],[3,4],[3,4,6],[3,2],[6,2],[4,2],[3,2,8],[3,7]]),
([w102,w0,w1,w9,w33,w38],[264,239,258,141,196,228,199,181,204],[],[[0,1,2],[3],[4,5,6],[5,1],[2,7],[1,2],[2,1],[7,2],[5,1],[5,4],[1,8],[7,2],[4,1,5],[2,7],[4,1,2]]),
([w83,w0,w1,w236,w3,w38],[0,181,417,352,108,162,36,68,141,62,258,204,223,239],[],[[0,1,2],[3,4],[5,4,6],[7,8,9],[2,1],[1,4,3],[1,4,10],[2,1],[3,4],[3,11,12],[3,4],[1,11],[11,4],[1,13,12],[2,1]]),
([w83,w0,w1,w2,w237,w38],[0,239,417,353,108,352,162,141,171,337],[],[[0,1,2],[3,4,5],[6,1,3],[3,7],[2,4],[1,4,5],[2,4,8],[2,1],[5,1,4],[1,8],[5,4],[2,8],[8,1],[2,1,9],[2,4]]),
([w83,w0,w1,w2,w3,w238],[0,239,417,353,108,352,162,141,171,175],[],[[0,1,2],[3,4,5],[6,1,3],[3,7],[2,4],[1,4,5],[2,4,8],[2,1],[5,1,4],[1,8],[5,4],[2,8],[8,1],[2,1,9],[2,4]]),
([w239,w0,w1,w2,w30,w38],[0,196,215,100,171,239,204,141,36,108,182,337],[],[[0,1],[2,1,3],[1,4,5],[1,6,7],[8,4,9],[5,9,7],[4,9],[5,6,7],[4,1],[5,4],[9,6,10],[7,1,10],[5,4],[1,5,11],[1,4]]),
([w90,w0,w1,w240,w30,w38],[239,258,36,182,352,228,223,108,171,417],[],[[0,1],[2,3,4],[0,3],[2,5,6],[2,1,4],[0,1],[1,7,3],[0,1],[4,0,5],[0,8],[4,3],[9,1],[0,3],[1,0,5],[4,1]]),
([w90,w0,w1,w2,w241,w38],[239,258,36,182,352,228,223,165],[],[[0,1],[2,3,4],[0,3],[2,5,6],[2,1,4],[0,1],[1,7],[0,1],[4,0,5],[0,7,4],[4,3],[7,1,3],[0,3],[1,0,5],[4,1]]),
([w90,w0,w1,w2,w30,w242],[239,258,36,182,352,228,223,165],[],[[0,1],[2,3,4],[0,3],[2,5,6],[2,1,4],[0,1],[1,7],[0,1],[4,0,5],[0,7,4],[4,3],[7,1,3],[0,3],[1,0,5],[4,1]]),
([w0,w224,w1,w3,w30,w47],[165,352,258,357,196,177,141,337,333,182,204],[],[[0],[1,2,3],[2,4,5],[6,2,7],[1,3],[1,3],[5,4],[5,6,8],[1,2],[1,3],[1,9],[6,2,9],[4,6,10],[1,3],[1,2]]),
([w0,w1,w225,w3,w30,w47],[232,258,58,417,196,239,171,352,199,204,181],[],[[0,1],[2,1,3],[0,4,5],[3,1],[6,4],[7],[8,4],[0,9],[0,1],[0,4,5],[0,5],[0,1],[0,8,4],[0,10],[3,1]])]
def p20_D4 : List StD := []
theorem p20_I4 : LevelN p20_R p20_T 4 p20_D4 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C5x0 : levelOK p20_T p20_K p20_P 4 (p20_D4.map Prod.fst) ((p20_D5.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C5x1 : levelOK p20_T p20_K p20_P 4 (p20_D4.map Prod.fst) ((p20_D5.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C5x2 : levelOK p20_T p20_K p20_P 4 (p20_D4.map Prod.fst) ((p20_D5.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C5x3 : levelOK p20_T p20_K p20_P 4 (p20_D4.map Prod.fst) ((p20_D5.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C5x4 : levelOK p20_T p20_K p20_P 4 (p20_D4.map Prod.fst) ((p20_D5.drop (4*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C5x5 : levelOK p20_T p20_K p20_P 4 (p20_D4.map Prod.fst) ((p20_D5.drop (5*16)).take 16) = true := by decide +kernel
theorem p20_I5 : LevelN p20_R p20_T 5 p20_D5 := levelStep p20_B p20_W p20_Q p20_I4 (chunks 16 p20_D5 6 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C5x0
  · exact p20_C5x1
  · exact p20_C5x2
  · exact p20_C5x3
  · exact p20_C5x4
  · exact p20_C5x5
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x0 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x1 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x2 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x3 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x4 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (4*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x5 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (5*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x6 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (6*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x7 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (7*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x8 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (8*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x9 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (9*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x10 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (10*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x11 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (11*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x12 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (12*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x13 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (13*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x14 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (14*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x15 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (15*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x16 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (16*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x17 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (17*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x18 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (18*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x19 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (19*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x20 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (20*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x21 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (21*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x22 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (22*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C6x23 : levelOK p20_T p20_K p20_P 5 (p20_D5.map Prod.fst) ((p20_D6.drop (23*16)).take 16) = true := by decide +kernel
theorem p20_I6 : LevelN p20_R p20_T 6 p20_D6 := levelStep p20_B p20_W p20_Q p20_I5 (chunks 16 p20_D6 24 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C6x0
  · exact p20_C6x1
  · exact p20_C6x2
  · exact p20_C6x3
  · exact p20_C6x4
  · exact p20_C6x5
  · exact p20_C6x6
  · exact p20_C6x7
  · exact p20_C6x8
  · exact p20_C6x9
  · exact p20_C6x10
  · exact p20_C6x11
  · exact p20_C6x12
  · exact p20_C6x13
  · exact p20_C6x14
  · exact p20_C6x15
  · exact p20_C6x16
  · exact p20_C6x17
  · exact p20_C6x18
  · exact p20_C6x19
  · exact p20_C6x20
  · exact p20_C6x21
  · exact p20_C6x22
  · exact p20_C6x23
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C7x0 : levelOK p20_T p20_K p20_P 6 (p20_D6.map Prod.fst) ((p20_D7.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C7x1 : levelOK p20_T p20_K p20_P 6 (p20_D6.map Prod.fst) ((p20_D7.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C7x2 : levelOK p20_T p20_K p20_P 6 (p20_D6.map Prod.fst) ((p20_D7.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C7x3 : levelOK p20_T p20_K p20_P 6 (p20_D6.map Prod.fst) ((p20_D7.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C7x4 : levelOK p20_T p20_K p20_P 6 (p20_D6.map Prod.fst) ((p20_D7.drop (4*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C7x5 : levelOK p20_T p20_K p20_P 6 (p20_D6.map Prod.fst) ((p20_D7.drop (5*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C7x6 : levelOK p20_T p20_K p20_P 6 (p20_D6.map Prod.fst) ((p20_D7.drop (6*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C7x7 : levelOK p20_T p20_K p20_P 6 (p20_D6.map Prod.fst) ((p20_D7.drop (7*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C7x8 : levelOK p20_T p20_K p20_P 6 (p20_D6.map Prod.fst) ((p20_D7.drop (8*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C7x9 : levelOK p20_T p20_K p20_P 6 (p20_D6.map Prod.fst) ((p20_D7.drop (9*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C7x10 : levelOK p20_T p20_K p20_P 6 (p20_D6.map Prod.fst) ((p20_D7.drop (10*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C7x11 : levelOK p20_T p20_K p20_P 6 (p20_D6.map Prod.fst) ((p20_D7.drop (11*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C7x12 : levelOK p20_T p20_K p20_P 6 (p20_D6.map Prod.fst) ((p20_D7.drop (12*16)).take 16) = true := by decide +kernel
theorem p20_I7 : LevelN p20_R p20_T 7 p20_D7 := levelStep p20_B p20_W p20_Q p20_I6 (chunks 16 p20_D7 13 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C7x0
  · exact p20_C7x1
  · exact p20_C7x2
  · exact p20_C7x3
  · exact p20_C7x4
  · exact p20_C7x5
  · exact p20_C7x6
  · exact p20_C7x7
  · exact p20_C7x8
  · exact p20_C7x9
  · exact p20_C7x10
  · exact p20_C7x11
  · exact p20_C7x12
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C8x0 : levelOK p20_T p20_K p20_P 7 (p20_D7.map Prod.fst) ((p20_D8.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C8x1 : levelOK p20_T p20_K p20_P 7 (p20_D7.map Prod.fst) ((p20_D8.drop (1*16)).take 16) = true := by decide +kernel
theorem p20_I8 : LevelN p20_R p20_T 8 p20_D8 := levelStep p20_B p20_W p20_Q p20_I7 (chunks 16 p20_D8 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C8x0
  · exact p20_C8x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C9x0 : levelOK p20_T p20_K p20_P 8 (p20_D8.map Prod.fst) ((p20_D9.drop (0*16)).take 16) = true := by decide +kernel
theorem p20_I9 : LevelN p20_R p20_T 9 p20_D9 := levelStep p20_B p20_W p20_Q p20_I8 (chunks 16 p20_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C9x0
  ))
theorem p20_L : LowN p20_R p20_T 10 := lowSearch p20_B p20_I9 (by decide +kernel)
def p21_T : Nat := 0xfffefeeefffefeeefffefeeefffefeee
def p21_R : List Nat := [0, 1, 2, 3, 4]
def p21_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20)]
theorem p21_B : baseOK p21_T p21_R p21_E = true := by decide +kernel
theorem p21_S0 : SliceN p21_R p21_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p21_B p12_B p12_L (by decide +kernel)
def p21_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4])]
theorem p21_Y : ∀ s ∈ p21_Z, SliceN p21_R p21_T s := by
  unfold p21_Z
  simp only [List.forall_mem_cons]
  exact ⟨p21_S0,by simp⟩
def p21_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def p21_P : List (Nat × Nat) := []
def p21_K : List CutV := p21_C.map (mkCut p21_Z)
theorem p21_W : ∀ c ∈ p21_K, CutP p21_R p21_T c := cutsGood p21_Y (by decide +kernel)
theorem p21_Q : p21_P.all (sepOK p21_T) = true := by decide +kernel
noncomputable def p21_D5 : List StD := [
([w0,w1,w2,w3,w30],[0],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p21_D4 : List StD := []
theorem p21_I4 : LevelN p21_R p21_T 4 p21_D4 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p21_C5x0 : levelOK p21_T p21_K p21_P 4 (p21_D4.map Prod.fst) ((p21_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem p21_I5 : LevelN p21_R p21_T 5 p21_D5 := levelStep p21_B p21_W p21_Q p21_I4 (chunks 16 p21_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p21_C5x0
  ))
theorem p21_L : LowN p21_R p21_T 6 := lowSearch p21_B p21_I5 (by decide +kernel)
def p22_T : Nat := 0xfefefea8fefefea8fefefea8fefefea8
def p22_R : List Nat := [0, 1, 2, 3, 4]
def p22_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p22_B : baseOK p22_T p22_R p22_E = true := by decide +kernel
theorem p22_S0 : SliceN p22_R p22_T (0x33333333333333333333333333333333,5,[0, 2, 3, 4]) := mkSlice (w:=0) p22_B p11_B p11_L (by decide +kernel)
def p22_Z : List SliceD := [(0x33333333333333333333333333333333,5,[0, 2, 3, 4])]
theorem p22_Y : ∀ s ∈ p22_Z, SliceN p22_R p22_T s := by
  unfold p22_Z
  simp only [List.forall_mem_cons]
  exact ⟨p22_S0,by simp⟩
def p22_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def p22_P : List (Nat × Nat) := []
def p22_K : List CutV := p22_C.map (mkCut p22_Z)
theorem p22_W : ∀ c ∈ p22_K, CutP p22_R p22_T c := cutsGood p22_Y (by decide +kernel)
theorem p22_Q : p22_P.all (sepOK p22_T) = true := by decide +kernel
noncomputable def p22_D5 : List StD := [
([w0,w1,w2,w3,w30],[0],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p22_D4 : List StD := []
theorem p22_I4 : LevelN p22_R p22_T 4 p22_D4 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p22_C5x0 : levelOK p22_T p22_K p22_P 4 (p22_D4.map Prod.fst) ((p22_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem p22_I5 : LevelN p22_R p22_T 5 p22_D5 := levelStep p22_B p22_W p22_Q p22_I4 (chunks 16 p22_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C5x0
  ))
theorem p22_L : LowN p22_R p22_T 6 := lowSearch p22_B p22_I5 (by decide +kernel)
def p23_T : Nat := 0xfffffffefffefefefffffffefffefefe
def p23_R : List Nat := [0, 1, 2, 3, 4, 5]
def p23_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,16,24),(4,8,24),(5,8,40)]
theorem p23_B : baseOK p23_T p23_R p23_E = true := by decide +kernel
theorem p23_S0 : SliceN p23_R p23_T (0x55555555555555555555555555555555,6,[1, 2, 3, 4, 5]) := mkSlice (w:=0) p23_B p21_B p21_L (by decide +kernel)
def p23_Z : List SliceD := [(0x55555555555555555555555555555555,6,[1, 2, 3, 4, 5])]
theorem p23_Y : ∀ s ∈ p23_Z, SliceN p23_R p23_T s := by
  unfold p23_Z
  simp only [List.forall_mem_cons]
  exact ⟨p23_S0,by simp⟩
def p23_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def p23_P : List (Nat × Nat) := []
def p23_K : List CutV := p23_C.map (mkCut p23_Z)
theorem p23_W : ∀ c ∈ p23_K, CutP p23_R p23_T c := cutsGood p23_Y (by decide +kernel)
theorem p23_Q : p23_P.all (sepOK p23_T) = true := by decide +kernel
noncomputable def p23_D6 : List StD := [
([w0,w1,w2,w3,w30,w38],[0],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p23_D5 : List StD := []
theorem p23_I5 : LevelN p23_R p23_T 5 p23_D5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p23_C6x0 : levelOK p23_T p23_K p23_P 5 (p23_D5.map Prod.fst) ((p23_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem p23_I6 : LevelN p23_R p23_T 6 p23_D6 := levelStep p23_B p23_W p23_Q p23_I5 (chunks 16 p23_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p23_C6x0
  ))
theorem p23_L : LowN p23_R p23_T 7 := lowSearch p23_B p23_I6 (by decide +kernel)
def p24_T : Nat := 0xfffffffefffefffefffffffefffefffe
def p24_R : List Nat := [0, 1, 2, 3, 4, 5]
def p24_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,0,8),(4,32,48),(5,16,48)]
theorem p24_B : baseOK p24_T p24_R p24_E = true := by decide +kernel
theorem p24_L : LowN p24_R p24_T 5 := lowCount p24_B (by decide +kernel)
def p25_T : Nat := 0xfffffffefffffffefffffffefffffffe
def p25_R : List Nat := [0, 1, 2, 3, 4]
def p25_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,0,8),(4,0,16)]
theorem p25_B : baseOK p25_T p25_R p25_E = true := by decide +kernel
theorem p25_L : LowN p25_R p25_T 4 := lowCount p25_B (by decide +kernel)
def p26_T : Nat := 0xeee0eee0eee0eee0eee0eee0eee0eee0
def p26_R : List Nat := [0, 1, 2, 3]
def p26_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,1,9)]
theorem p26_B : baseOK p26_T p26_R p26_E = true := by decide +kernel
theorem p26_L : LowN p26_R p26_T 3 := lowCount p26_B (by decide +kernel)
def ptopT : Nat := 0xfffffffffffffefefffefffefefceea0
def ptopR : List Nat := [0, 1, 2, 3, 4, 5, 6]
def ptopE : List (Nat × Nat × Nat) := [(0,4,5),(1,8,10),(2,1,5),(3,1,9),(4,2,18),(5,1,33),(6,1,65)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
theorem ptopS0 : SliceN ptopR ptopT (0x330033003300330033003300330033,8,[2, 6, 5, 0, 4]) := mkSlice (w:=0) ptopB p6_B p6_L (by decide +kernel)
theorem ptopS1 : SliceN ptopR ptopT (0x3333000033330000333300003333,8,[0, 5, 2, 6, 3]) := mkSlice (w:=0) ptopB p6_B p6_L (by decide +kernel)
theorem ptopS2 : SliceN ptopR ptopT (0xffffffff00000000ffffffff,10,[0, 1, 6, 4, 2, 3]) := mkSlice (w:=0) ptopB p20_B p20_L (by decide +kernel)
theorem ptopS3 : SliceN ptopR ptopT (0xffffffffffffffff,10,[1, 2, 5, 0, 3, 4]) := mkSlice (w:=0) ptopB p20_B p20_L (by decide +kernel)
theorem ptopS4 : SliceN ptopR ptopT (0xff000000ff000000ff000000ff,8,[5, 6, 2, 0, 1]) := mkSlice (w:=0) ptopB p6_B p6_L (by decide +kernel)
theorem ptopS5 : SliceN ptopR ptopT (0x11111111111111111111111111111111,7,[5, 2, 6, 4, 3]) := mkSlice (w:=0) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS6 : SliceN ptopR ptopT (0x3030303030303030303030303030303,7,[6, 5, 0, 3, 4]) := mkSlice (w:=0) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS7 : SliceN ptopR ptopT (0x5050505050505050505050505050505,7,[1, 5, 6, 4, 3]) := mkSlice (w:=0) ptopB p16_B p16_L (by decide +kernel)
theorem ptopS8 : SliceN ptopR ptopT (0xf000f000f000f000f000f000f000f,7,[6, 1, 5, 0, 4]) := mkSlice (w:=0) ptopB p16_B p16_L (by decide +kernel)
theorem ptopS9 : SliceN ptopR ptopT (0x5555000055550000555500005555,7,[5, 1, 6, 2, 3]) := mkSlice (w:=0) ptopB p16_B p16_L (by decide +kernel)
theorem ptopS10 : SliceN ptopR ptopT (0x55005500550055005500550055005500,6,[1, 5, 4, 2, 6]) := mkSlice (w:=8) ptopB p21_B p21_L (by decide +kernel)
theorem ptopS11 : SliceN ptopR ptopT (0xf0f00000f0f00000f0f00000f0f0000,6,[1, 6, 3, 5, 0]) := mkSlice (w:=16) ptopB p21_B p21_L (by decide +kernel)
theorem ptopS12 : SliceN ptopR ptopT (0x550055005500550055005500550055,6,[6, 2, 1, 5, 4]) := mkSlice (w:=0) ptopB p22_B p22_L (by decide +kernel)
theorem ptopS13 : SliceN ptopR ptopT (0xf0f00000f0f00000f0f00000f0f,6,[5, 1, 0, 3, 6]) := mkSlice (w:=0) ptopB p22_B p22_L (by decide +kernel)
theorem ptopS14 : SliceN ptopR ptopT (0x3333333333333333,7,[2, 0, 5, 3, 4]) := mkSlice (w:=0) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS15 : SliceN ptopR ptopT (0xf0f0f0f0f0f0f0f,7,[1, 3, 5, 0, 4]) := mkSlice (w:=0) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS16 : SliceN ptopR ptopT (0x1010101010101010101010101010101,4,[5, 6, 4, 3]) := mkSlice (w:=0) ptopB p9_B p9_L (by decide +kernel)
theorem ptopS17 : SliceN ptopR ptopT (0x555555550000000055555555,7,[1, 4, 6, 2, 3]) := mkSlice (w:=0) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS18 : SliceN ptopR ptopT (0x5555555555555555,6,[1, 5, 2, 4, 3]) := mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel)
theorem ptopS19 : SliceN ptopR ptopT (0x50005000500050005000500050005,5,[1, 6, 5, 4]) := mkSlice (w:=0) ptopB p11_B p11_L (by decide +kernel)
theorem ptopS20 : SliceN ptopR ptopT (0xffff0000ffff0000,6,[1, 2, 0, 3, 5]) := mkSlice (w:=16) ptopB p21_B p21_L (by decide +kernel)
theorem ptopS21 : SliceN ptopR ptopT (0x505000005050000050500000505,5,[1, 5, 3, 6]) := mkSlice (w:=0) ptopB p11_B p11_L (by decide +kernel)
theorem ptopS22 : SliceN ptopR ptopT (0xff00ff00ff00ff00ff00ff00ff00ff00,7,[0, 1, 5, 4, 2, 6]) := mkSlice (w:=8) ptopB p23_B p23_L (by decide +kernel)
theorem ptopS23 : SliceN ptopR ptopT (0xf0f0f0f000000000f0f0f0f,6,[1, 6, 0, 3, 4]) := mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel)
theorem ptopS24 : SliceN ptopR ptopT (0x5500550000000000550055,5,[4, 6, 1, 2]) := mkSlice (w:=0) ptopB p11_B p11_L (by decide +kernel)
theorem ptopS25 : SliceN ptopR ptopT (0x333333330000000033333333,7,[0, 2, 6, 4, 3]) := mkSlice (w:=0) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS26 : SliceN ptopR ptopT (0xff00ff0000000000ff00ff,7,[6, 2, 4, 1, 0]) := mkSlice (w:=0) ptopB p16_B p16_L (by decide +kernel)
theorem ptopS27 : SliceN ptopR ptopT (0xf0f00000f0f,5,[3, 5, 0, 1]) := mkSlice (w:=0) ptopB p11_B p11_L (by decide +kernel)
theorem ptopS28 : SliceN ptopR ptopT (0x505050505050505,5,[1, 3, 5, 4]) := mkSlice (w:=0) ptopB p10_B p10_L (by decide +kernel)
theorem ptopS29 : SliceN ptopR ptopT (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[2, 3, 5, 6, 1, 4]) := mkSlice (w:=1) ptopB p24_B p24_L (by decide +kernel)
theorem ptopS30 : SliceN ptopR ptopT (0x303000003030000,4,[0, 3, 5]) := mkSlice (w:=16) ptopB p3_B p3_L (by decide +kernel)
theorem ptopS31 : SliceN ptopR ptopT (0xcccccccccccccccccccccccccccccccc,5,[3, 4, 5, 6, 0, 2]) := mkSlice (w:=2) ptopB p24_B p24_L (by decide +kernel)
theorem ptopS32 : SliceN ptopR ptopT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 4, 5, 6, 3, 1]) := mkSlice (w:=4) ptopB p24_B p24_L (by decide +kernel)
theorem ptopS33 : SliceN ptopR ptopT (0xf000f000f000f000f000f000f000f000,4,[0, 1, 4, 5, 6]) := mkSlice (w:=12) ptopB p25_B p25_L (by decide +kernel)
theorem ptopS34 : SliceN ptopR ptopT (0x11001100110011001100110011001100,5,[5, 4, 2, 6]) := mkSlice (w:=8) ptopB p12_B p12_L (by decide +kernel)
theorem ptopS35 : SliceN ptopR ptopT (0xaaaa0000aaaa0000aaaa0000aaaa0000,4,[1, 2, 3, 5, 6]) := mkSlice (w:=17) ptopB p25_B p25_L (by decide +kernel)
theorem ptopS36 : SliceN ptopR ptopT (0x10001000100010000000000000000,1,[4, 5]) := mkSlice (w:=64) ptopB p2_B p2_L (by decide +kernel)
theorem ptopS37 : SliceN ptopR ptopT (0x10100000101,1,[3, 5]) := mkSlice (w:=0) ptopB p1_B p1_L (by decide +kernel)
theorem ptopS38 : SliceN ptopR ptopT (0x30003000300030003000300030003,5,[6, 5, 0, 4]) := mkSlice (w:=0) ptopB p10_B p10_L (by decide +kernel)
theorem ptopS39 : SliceN ptopR ptopT (0xcccccccc00000000cccccccc,4,[3, 4, 6, 2, 0]) := mkSlice (w:=2) ptopB p19_B p19_L (by decide +kernel)
theorem ptopS40 : SliceN ptopR ptopT (0xff00ff00ff00ff,6,[2, 5, 1, 4, 0]) := mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel)
theorem ptopS41 : SliceN ptopR ptopT (0x110011001100110011001100110011,5,[2, 6, 5, 4]) := mkSlice (w:=0) ptopB p11_B p11_L (by decide +kernel)
theorem ptopS42 : SliceN ptopR ptopT (0x55000000550000005500000055,5,[5, 6, 1, 2]) := mkSlice (w:=0) ptopB p11_B p11_L (by decide +kernel)
theorem ptopS43 : SliceN ptopR ptopT (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,4,[3, 5, 6, 1, 4]) := mkSlice (w:=1) ptopB p19_B p19_L (by decide +kernel)
theorem ptopS44 : SliceN ptopR ptopT (0xf0f0f0f0f0f0f0f0,4,[0, 4, 5, 1, 3]) := mkSlice (w:=4) ptopB p19_B p19_L (by decide +kernel)
theorem ptopS45 : SliceN ptopR ptopT (0x55005500550055,3,[1, 2, 4, 5]) := mkSlice (w:=0) ptopB p26_B p26_L (by decide +kernel)
theorem ptopS46 : SliceN ptopR ptopT (0x50500000505,4,[1, 3, 5]) := mkSlice (w:=0) ptopB p3_B p3_L (by decide +kernel)
theorem ptopS47 : SliceN ptopR ptopT (0xff00ff0000000000ff00ff00,6,[0, 1, 2, 4, 6]) := mkSlice (w:=8) ptopB p21_B p21_L (by decide +kernel)
theorem ptopS48 : SliceN ptopR ptopT (0xffff000000000000ffff,6,[0, 6, 1, 3, 2]) := mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel)
theorem ptopS49 : SliceN ptopR ptopT (0x303000003030000030300000303,5,[0, 5, 3, 6]) := mkSlice (w:=0) ptopB p11_B p11_L (by decide +kernel)
theorem ptopS50 : SliceN ptopR ptopT (0xf0000000f0000000f0000000f,5,[5, 6, 0, 1]) := mkSlice (w:=0) ptopB p11_B p11_L (by decide +kernel)
theorem ptopS51 : SliceN ptopR ptopT (0xf0f0000000000000f0f,3,[0, 1, 3, 6]) := mkSlice (w:=0) ptopB p26_B p26_L (by decide +kernel)
theorem ptopS52 : SliceN ptopR ptopT (0x50505050505050505050505050505050,4,[4, 5, 6, 3, 1]) := mkSlice (w:=4) ptopB p19_B p19_L (by decide +kernel)
theorem ptopS53 : SliceN ptopR ptopT (0x500050000000000050005,4,[1, 4, 6]) := mkSlice (w:=0) ptopB p3_B p3_L (by decide +kernel)
theorem ptopS54 : SliceN ptopR ptopT (0x88888888888888888888888888888888,4,[2, 3, 4, 5, 6]) := mkSlice (w:=3) ptopB p25_B p25_L (by decide +kernel)
theorem ptopS55 : SliceN ptopR ptopT (0xf0f0f0f000000000f0f0f0f0,4,[0, 4, 6, 1, 3]) := mkSlice (w:=4) ptopB p19_B p19_L (by decide +kernel)
theorem ptopS56 : SliceN ptopR ptopT (0x30300000000,1,[0, 3]) := mkSlice (w:=32) ptopB p2_B p2_L (by decide +kernel)
theorem ptopS57 : SliceN ptopR ptopT (0x110011000000000011001100,4,[2, 4, 6]) := mkSlice (w:=8) ptopB p3_B p3_L (by decide +kernel)
theorem ptopS58 : SliceN ptopR ptopT (0x2222000022220000222200002222,3,[2, 3, 5, 6]) := mkSlice (w:=1) ptopB p18_B p18_L (by decide +kernel)
theorem ptopS59 : SliceN ptopR ptopT (0xaaaaaaaaaaaaaaaa,4,[2, 3, 5, 4, 1]) := mkSlice (w:=1) ptopB p19_B p19_L (by decide +kernel)
theorem ptopS60 : SliceN ptopR ptopT (0xff00ff0000000000000000,3,[0, 1, 2, 4]) := mkSlice (w:=64) ptopB p18_B p18_L (by decide +kernel)
theorem ptopS61 : SliceN ptopR ptopT (0xcccccccccccccccc,4,[3, 4, 5, 2, 0]) := mkSlice (w:=2) ptopB p19_B p19_L (by decide +kernel)
theorem ptopS62 : SliceN ptopR ptopT (0xffff000000000000ffff00000000,4,[0, 1, 2, 3, 6]) := mkSlice (w:=32) ptopB p25_B p25_L (by decide +kernel)
theorem ptopS63 : SliceN ptopR ptopT (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,4,[0, 3, 4, 5, 6]) := mkSlice (w:=6) ptopB p25_B p25_L (by decide +kernel)
theorem ptopS64 : SliceN ptopR ptopT (0xffff00000000,3,[0, 1, 2, 3]) := mkSlice (w:=32) ptopB p18_B p18_L (by decide +kernel)
theorem ptopS65 : SliceN ptopR ptopT (0x50500000000,1,[1, 3]) := mkSlice (w:=32) ptopB p2_B p2_L (by decide +kernel)
def ptopZ : List SliceD := [(0x330033003300330033003300330033,8,[2, 6, 5, 0, 4]),(0x3333000033330000333300003333,8,[0, 5, 2, 6, 3]),(0xffffffff00000000ffffffff,10,[0, 1, 6, 4, 2, 3]),(0xffffffffffffffff,10,[1, 2, 5, 0, 3, 4]),(0xff000000ff000000ff000000ff,8,[5, 6, 2, 0, 1]),(0x11111111111111111111111111111111,7,[5, 2, 6, 4, 3]),(0x3030303030303030303030303030303,7,[6, 5, 0, 3, 4]),(0x5050505050505050505050505050505,7,[1, 5, 6, 4, 3]),(0xf000f000f000f000f000f000f000f,7,[6, 1, 5, 0, 4]),(0x5555000055550000555500005555,7,[5, 1, 6, 2, 3]),(0x55005500550055005500550055005500,6,[1, 5, 4, 2, 6]),(0xf0f00000f0f00000f0f00000f0f0000,6,[1, 6, 3, 5, 0]),(0x550055005500550055005500550055,6,[6, 2, 1, 5, 4]),(0xf0f00000f0f00000f0f00000f0f,6,[5, 1, 0, 3, 6]),(0x3333333333333333,7,[2, 0, 5, 3, 4]),(0xf0f0f0f0f0f0f0f,7,[1, 3, 5, 0, 4]),(0x1010101010101010101010101010101,4,[5, 6, 4, 3]),(0x555555550000000055555555,7,[1, 4, 6, 2, 3]),(0x5555555555555555,6,[1, 5, 2, 4, 3]),(0x50005000500050005000500050005,5,[1, 6, 5, 4]),(0xffff0000ffff0000,6,[1, 2, 0, 3, 5]),(0x505000005050000050500000505,5,[1, 5, 3, 6]),(0xff00ff00ff00ff00ff00ff00ff00ff00,7,[0, 1, 5, 4, 2, 6]),(0xf0f0f0f000000000f0f0f0f,6,[1, 6, 0, 3, 4]),(0x5500550000000000550055,5,[4, 6, 1, 2]),(0x333333330000000033333333,7,[0, 2, 6, 4, 3]),(0xff00ff0000000000ff00ff,7,[6, 2, 4, 1, 0]),(0xf0f00000f0f,5,[3, 5, 0, 1]),(0x505050505050505,5,[1, 3, 5, 4]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[2, 3, 5, 6, 1, 4]),(0x303000003030000,4,[0, 3, 5]),(0xcccccccccccccccccccccccccccccccc,5,[3, 4, 5, 6, 0, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 4, 5, 6, 3, 1]),(0xf000f000f000f000f000f000f000f000,4,[0, 1, 4, 5, 6]),(0x11001100110011001100110011001100,5,[5, 4, 2, 6]),(0xaaaa0000aaaa0000aaaa0000aaaa0000,4,[1, 2, 3, 5, 6]),(0x10001000100010000000000000000,1,[4, 5]),(0x10100000101,1,[3, 5]),(0x30003000300030003000300030003,5,[6, 5, 0, 4]),(0xcccccccc00000000cccccccc,4,[3, 4, 6, 2, 0]),(0xff00ff00ff00ff,6,[2, 5, 1, 4, 0]),(0x110011001100110011001100110011,5,[2, 6, 5, 4]),(0x55000000550000005500000055,5,[5, 6, 1, 2]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,4,[3, 5, 6, 1, 4]),(0xf0f0f0f0f0f0f0f0,4,[0, 4, 5, 1, 3]),(0x55005500550055,3,[1, 2, 4, 5]),(0x50500000505,4,[1, 3, 5]),(0xff00ff0000000000ff00ff00,6,[0, 1, 2, 4, 6]),(0xffff000000000000ffff,6,[0, 6, 1, 3, 2]),(0x303000003030000030300000303,5,[0, 5, 3, 6]),(0xf0000000f0000000f0000000f,5,[5, 6, 0, 1]),(0xf0f0000000000000f0f,3,[0, 1, 3, 6]),(0x50505050505050505050505050505050,4,[4, 5, 6, 3, 1]),(0x500050000000000050005,4,[1, 4, 6]),(0x88888888888888888888888888888888,4,[2, 3, 4, 5, 6]),(0xf0f0f0f000000000f0f0f0f0,4,[0, 4, 6, 1, 3]),(0x30300000000,1,[0, 3]),(0x110011000000000011001100,4,[2, 4, 6]),(0x2222000022220000222200002222,3,[2, 3, 5, 6]),(0xaaaaaaaaaaaaaaaa,4,[2, 3, 5, 4, 1]),(0xff00ff0000000000000000,3,[0, 1, 2, 4]),(0xcccccccccccccccc,4,[3, 4, 5, 2, 0]),(0xffff000000000000ffff00000000,4,[0, 1, 2, 3, 6]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,4,[0, 3, 4, 5, 6]),(0xffff00000000,3,[0, 1, 2, 3]),(0x50500000000,1,[1, 3])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨ptopS0,ptopS1,ptopS2,ptopS3,ptopS4,ptopS5,ptopS6,ptopS7,ptopS8,ptopS9,ptopS10,ptopS11,ptopS12,ptopS13,ptopS14,ptopS15,ptopS16,ptopS17,ptopS18,ptopS19,ptopS20,ptopS21,ptopS22,ptopS23,ptopS24,ptopS25,ptopS26,ptopS27,ptopS28,ptopS29,ptopS30,ptopS31,ptopS32,ptopS33,ptopS34,ptopS35,ptopS36,ptopS37,ptopS38,ptopS39,ptopS40,ptopS41,ptopS42,ptopS43,ptopS44,ptopS45,ptopS46,ptopS47,ptopS48,ptopS49,ptopS50,ptopS51,ptopS52,ptopS53,ptopS54,ptopS55,ptopS56,ptopS57,ptopS58,ptopS59,ptopS60,ptopS61,ptopS62,ptopS63,ptopS64,ptopS65,by simp⟩
def ptopC : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(2,[(1,0,1)]),(3,[(1,0,3)]),(2,[(2,0,1)]),(7,[]),(3,[(3,0,3)]),(2,[(2,0,4)]),(2,[(3,0,4)]),(8,[]),(9,[]),(2,[(0,0,4)]),(3,[(0,1,3)]),(0,[(1,0,3)]),(1,[(1,0,2)]),(2,[(1,0,4)]),(3,[(1,1,3)]),(4,[(1,2,3)]),(3,[(3,1,3)]),(4,[(3,2,3)]),(10,[]),(3,[(2,1,3)]),(11,[]),(4,[(2,2,3)]),(1,[(1,0,4)]),(2,[(1,0,5)]),(3,[(1,3,4)]),(12,[]),(2,[(0,0,5)]),(2,[(2,0,5)]),(3,[(2,3,4)]),(2,[(1,0,3)]),(3,[(1,3,5)]),(2,[(0,0,3)]),(2,[(2,0,3)]),(3,[(2,3,5)]),(2,[(1,1,4)]),(3,[(1,0,1)]),(2,[(3,1,4)]),(3,[(3,0,1)]),(1,[(1,2,4)]),(2,[(1,4,5)]),(3,[(1,1,4)]),(2,[(2,4,5)]),(3,[(2,1,4)]),(0,[(1,0,4)]),(13,[]),(2,[(1,3,4)]),(3,[(1,1,5)]),(2,[(3,3,4)]),(3,[(2,1,5)]),(2,[(1,0,1),(1,4,6)]),(2,[(1,0,1),(1,1,4)]),(3,[(1,0,3),(1,0,1)]),(2,[(1,1,4),(1,0,6)]),(2,[(1,0,4),(1,1,6)]),(14,[(1,0,1)]),(15,[(1,0,3)]),(16,[]),(6,[(1,2,4)]),(0,[(1,3,4)]),(17,[]),(14,[(1,1,4)]),(18,[]),(14,[]),(2,[(3,0,1)]),(15,[]),(2,[(3,4,5)]),(2,[(3,0,3)]),(2,[(1,0,2)]),(2,[(1,2,4)]),(2,[(2,2,4)]),(15,[(1,3,4)]),(2,[(1,0,4),(1,0,3)]),(3,[(1,1,3),(1,3,5)]),(9,[(1,3,4)]),(2,[(1,4,5),(3,0,4)]),(2,[(1,0,4),(1,4,5)]),(3,[(1,1,3),(1,1,4)]),(2,[(1,0,5),(1,4,6)]),(15,[(1,1,3)]),(19,[]),(20,[]),(21,[]),(17,[(1,1,3)]),(0,[(3,0,3)]),(22,[]),(1,[(3,0,2)]),(23,[]),(17,[(1,3,4)]),(2,[(1,0,5),(1,4,5)]),(3,[(1,3,4),(1,1,4)]),(17,[(3,3,4)]),(24,[]),(2,[(1,0,5),(3,4,6)]),(2,[(1,0,3),(1,3,4)]),(3,[(1,3,5),(1,1,5)]),(2,[(1,3,4),(1,0,6)]),(4,[(1,3,4)]),(0,[(2,3,4)]),(4,[(2,2,4)]),(25,[(1,1,4)]),(4,[(1,2,4)]),(26,[(1,1,3)]),(27,[]),(2,[(1,3,4),(3,0,6)]),(2,[(1,0,2),(1,1,4),(1,0,7)]),(1,[(1,0,2),(1,0,3)]),(0,[(1,0,3),(1,1,3)]),(18,[(1,0,2)]),(28,[]),(29,[]),(1,[(1,0,3),(1,2,5)]),(15,[(2,0,3)]),(30,[]),(2,[(1,1,2),(1,0,4),(1,1,7)]),(7,[(1,0,2)]),(3,[(1,0,1),(1,3,6)]),(1,[(1,0,2),(1,2,3)]),(2,[(1,2,4),(1,0,1),(1,4,7)]),(0,[(1,0,3),(1,0,1)]),(0,[(1,0,3),(1,1,5)]),(2,[(1,0,1),(1,4,6),(1,2,7)]),(5,[(1,1,2)]),(6,[(1,0,2)]),(6,[(2,0,2)]),(2,[(1,1,4),(1,0,6),(1,2,7)]),(31,[]),(7,[(3,0,2)]),(32,[]),(5,[(3,1,2)]),(1,[(1,0,2),(1,3,5)]),(33,[]),(34,[]),(35,[]),(36,[]),(37,[]),(38,[(1,0,2)]),(39,[]),(2,[(2,0,2)]),(7,[(2,0,2)]),(5,[(2,1,2)]),(3,[(1,0,3),(1,1,6)]),(2,[(1,2,5),(1,0,1),(1,4,7)]),(7,[(1,2,4)]),(2,[(1,2,5),(1,0,4),(1,1,7)]),(5,[(1,2,4)]),(1,[(1,0,2),(1,3,4)]),(2,[(1,2,5),(1,1,4),(1,0,7)]),(16,[(1,1,3)]),(40,[]),(1,[(1,0,2),(3,3,4)]),(1,[(1,0,3)]),(0,[(1,3,4),(1,1,3)]),(1,[(1,3,4)]),(17,[(1,2,4)]),(9,[(1,2,4)]),(1,[(3,3,4)]),(30,[(1,0,1)]),(41,[]),(8,[(1,0,3)]),(27,[(1,0,2)]),(40,[(3,0,4)]),(42,[]),(43,[]),(44,[]),(10,[(2,3,4)]),(45,[]),(46,[]),(2,[(1,2,5),(2,0,4)]),(0,[(1,1,3)]),(0,[(2,3,4),(1,1,3)]),(4,[(1,3,4),(1,1,3)]),(2,[(1,2,5),(1,0,1)]),(10,[(1,1,3)]),(1,[(1,2,4),(1,1,2)]),(47,[]),(0,[(1,0,2)]),(10,[(1,1,2)]),(7,[(1,1,3)]),(15,[(1,2,4)]),(8,[(1,2,4)]),(1,[(2,2,4),(1,1,2)]),(4,[(1,2,4),(1,0,2)]),(4,[(1,0,2),(1,4,5)]),(2,[(2,1,4)]),(48,[]),(6,[(1,1,4)]),(30,[(2,0,2)]),(49,[]),(50,[]),(51,[]),(52,[]),(9,[(1,0,3)]),(48,[(3,0,4)]),(53,[]),(0,[(1,0,3),(1,1,3),(1,0,1)]),(17,[(1,0,3),(1,2,3)]),(2,[(1,0,2),(1,2,5),(1,1,4),(1,0,8)]),(1,[(1,0,2),(1,0,3),(1,3,4)]),(6,[(1,0,2),(1,0,3)]),(10,[(1,0,3)]),(54,[]),(1,[(1,0,2),(1,3,4),(1,3,5)]),(33,[(1,0,4)]),(17,[(1,0,3),(1,2,5)]),(15,[(1,0,3),(1,2,5)]),(15,[(1,2,3),(3,0,3)]),(55,[]),(53,[(1,0,2)]),(30,[(1,0,2)]),(56,[]),(57,[(1,0,2)]),(15,[(1,2,3),(1,0,3)]),(58,[]),(28,[(1,0,2)]),(14,[(1,0,1),(1,2,5)]),(57,[(2,0,2)]),(59,[]),(30,[(3,0,2)]),(60,[]),(17,[(1,0,3),(3,2,5)]),(61,[]),(62,[]),(53,[(2,0,2)]),(46,[(1,0,2)]),(2,[(1,1,2),(1,2,5),(1,0,4),(1,1,8)]),(17,[(1,0,3),(1,0,2),(1,2,4)]),(33,[(1,1,4)]),(63,[]),(15,[(3,0,3)]),(1,[(1,0,3),(1,3,4)]),(17,[(3,2,4)]),(2,[(1,0,2),(1,2,5),(3,1,3)]),(2,[(1,2,5),(1,0,2),(1,1,7)]),(1,[(1,0,3),(1,4,5)]),(34,[(1,0,2)]),(20,[(1,1,4)]),(7,[(3,1,3)]),(47,[(1,0,4),(1,2,4)]),(1,[(1,0,3),(1,2,3)]),(7,[(1,0,1)]),(64,[]),(1,[(1,0,2),(1,0,3),(1,2,3)]),(65,[]),(33,[(1,1,3)]),(35,[(1,0,3)]),(54,[(1,0,4)]),(63,[(1,0,4)]),(35,[(1,1,4)]),(33,[(1,0,3)]),(35,[(1,1,3)]),(6,[(1,1,2),(1,0,2)]),(41,[(1,0,1)]),(34,[(1,2,3)]),(58,[(1,0,2)]),(57,[(3,0,2)]),(54,[(1,3,4)]),(1,[(1,0,1),(1,1,3)])]
def ptopP : List (Nat × Nat) := [(8,10),(6,7),(17,19),(8,9),(16,20),(1,5),(2,10),(1,9),(2,18),(24,25),(3,19),(1,33),(2,34),(1,65),(2,66),(12,14),(3,7),(24,28),(6,14),(4,20),(4,36),(4,68),(17,25),(12,28),(8,40),(12,76),(17,49),(16,80),(40,72),(3,18),(3,5),(1,7),(3,9),(3,33),(3,65),(9,17),(12,36),(12,68),(17,33),(17,65),(6,10),(5,17),(6,34),(6,66),(17,18),(9,12),(10,12),(2,14),(6,18),(4,5),(12,13),(16,18),(17,21),(0,5),(12,20),(24,40),(5,6),(4,7),(0,9),(0,33),(0,65),(32,40),(64,80),(64,96),(64,66),(64,68),(5,12),(72,73),(72,76),(48,49),(32,34),(48,52),(32,96),(32,33),(1,18),(4,10),(4,18),(4,34),(4,66),(64,65),(24,80),(40,64),(3,66),(10,64),(0,10),(9,72),(1,11),(25,72),(18,32),(32,80),(12,40),(48,80)]
def ptopK : List CutV := ptopC.map (mkCut ptopZ)
theorem ptopW : ∀ c ∈ ptopK, CutP ptopR ptopT c := cutsGood ptopY (by decide +kernel)
theorem ptopQ : ptopP.all (sepOK ptopT) = true := by decide +kernel
noncomputable def ptopD11 : List StD := [
([w0,w1,w2,w3,w30,w38,w243],[0,1,2,3,4],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28],[[0,100,101,102],[103,104,101,105],[0,106,103,107],[1,108,109,110],[2,111,112],[3,113,114],[0,100,115,116],[0,4,1,102,100,106],[0,4,100,1,102,108],[0,2,112,111],[0,3,114,113],[0,106,117,118],[1,108,104,119],[2,120,111],[3,121,113],[0,1,106,4,122,123],[0,2,124,111],[0,3,125,113],[1,2,126,111],[1,3,127,113],[2,3,128]])]
noncomputable def ptopD10 : List StD := [
([w0,w1,w4,w2,w3,w30,w38,w243],[1,5,6,0,7,8,9,10],[1,5,7,29,11,13,30,31,32,6,8,33,34,18,19,20,21,35,36,37,38,39,28],[[0,1,100],[0],[1,100,2,101],[1,3,102],[0,1,103],[1,4,104],[1,5,105],[0,1,6],[0,106,7,107],[0,3,108,109],[0,1,110],[0,4,111],[0,5,112],[1,101,2],[1,3,102],[0,1,110],[1,4,104],[1,5,105],[2,3,113,102],[0,114,2,110],[2,4,115,104],[2,5,116,105],[0,3,117],[3,4,118],[3,5,119],[0,4,120],[0,5,121],[4,5,122]]),
([w244,w0,w1,w2,w3,w30,w38,w243],[1,5,7,10,0,9,11],[5,7,11,13,1,29,16,6,8,12,14,40,41,42,43,35,36,37,38,39,28],[[0],[0,1,2],[1,3,100],[1,4,101],[0,1],[1,5,102],[1,6,103],[0,1,104],[1,3,100],[1,4,101],[0,1,105],[1,5,102],[1,6,103],[0,3,106],[0,4,107],[0,1,108],[0,5,109],[0,6,110],[3,4,111],[0,3,112],[3,5,113],[3,6,114],[0,4,115],[4,5,116],[4,6,117],[0,5,118],[0,6,119],[5,6,120]]),
([w245,w0,w1,w2,w3,w30,w38,w243],[10,12,5,0,13,14,15,1,16,17,6],[44,45,7,29,3,11,13,46,32,8,33,34,40,47,48,42,43,35,36,37,38,39,28],[[0,1],[0,2,3],[0,4],[0,5,3],[0,6,7],[0,8],[0,9],[0,2,100,10],[0,101,2,5],[0,5,102],[0,6,103,104],[0,8,105],[0,9,106],[0,2,107],[2,5,108],[2,6,109],[2,8,110],[2,9,111],[0,5,112,113],[0,6,114],[0,8,115],[0,9,116],[5,6,117],[5,8,118],[5,9,119],[6,8,120],[6,9,121],[8,9,122]]),
([w0,w1,w2,w5,w3,w30,w38,w243],[10,18,13,19,20,21,14,15,22],[1,49,45,5,50,10,11,13,16,15,7,6,51,12,14,18,52,20,21,22,23,24,25,26,27,28],[[0,100,1,101],[0,102,100,103],[0,2],[0,104,1,100],[0,105,3],[0,4,106],[0,5,107],[0,108,1,103],[0,109,1],[1,6,3,110,109,111],[1,7,109,3,112,105],[1,4,113,106],[1,5,114,107],[0,7],[0,115,1],[0,116,3,103],[0,4,117],[0,5,118],[0,110,1],[0,105,3],[0,4,106],[0,5,107],[1,3,105,8,119,120],[1,4,121,106],[1,5,122,107],[3,4,123,106],[3,5,124,107],[4,5,125]]),
([w246,w0,w1,w2,w3,w30,w38,w243],[10,16,5,20,4,15,12,23,24,25,14],[2,7,10,11,13,49,53,50,46,32,33,34,40,47,48,42,43,35,36,37,38,39,28],[[0,1],[0,2,100],[0,3],[0,101,4],[0,5,102],[0,6,103],[0,7,104],[0,2,100],[0,2,105,106],[0,107,8,101],[0,5,102],[0,6,103],[0,7,104],[0,2,108],[2,9,109,8,100],[2,5,100],[2,6,110],[2,7,111],[0,9,112,8,113],[0,5,114],[0,6,115],[0,7,116],[5,9,117,10,102],[6,9,118,8,103],[7,9,119,8,104],[5,6,120],[5,7,121],[6,7,122]]),
([w247,w0,w1,w2,w3,w30,w38,w243],[10,20,6,16,14,4,13,26,27,28,15],[15,18,19,20,21,44,5,53,7,29,3,11,13,8,33,34,52,35,36,37,38,39,28],[[0,1],[0,2,100],[0,3],[0,4,101],[0,102,5],[0,6,103],[0,7,104],[0,2,105],[0,2,106,107],[0,4,108],[0,8,109,9,110],[0,6,111],[0,7,112],[0,2,100],[2,4,100],[2,8,113,9],[2,6,114],[2,7,115],[0,4,101],[0,116,9,102],[0,6,103],[0,7,104],[4,8,117,10,101],[4,6,118],[4,7,119],[6,8,120,9,103],[7,8,121,9,104],[6,7,122]]),
([w0,w1,w2,w3,w6,w30,w38,w243],[15,29,0,14,10,4,30,31,25,32],[2,0,3,50,5,10,8,11,12,13,14,15,51,17,4,19,20,21,35,7,24,25,38,39,28],[[0,1,2,100,101],[0,3,102,4,103,104],[0,2,102],[2],[0,1,4,5,105,106],[0,6,107,108],[0,7,109,110],[1,2,111,3,100],[1,2,5,101],[1,2,8,100,9,112],[0,2,5,100],[1,2,6,108],[1,2,7,110],[2,113,4],[3,9,114,8,104],[0,3,5,115,105],[3,6,116,107],[3,7,117,109],[0],[0,2,5,118,119],[2,6,120],[2,7,121],[0,5,8,105,9,106],[6,8,107,9,108],[7,8,109,9,110],[0,5,6,122],[0,5,7,123],[6,7,124]]),
([w248,w0,w1,w2,w3,w30,w38,w243],[15,33,0,10,30,34,35,4,5],[2,5,10,11,13,3,30,6,33,34,40,41,42,43,54,36,37,38,39,28],[[0,1],[0,2,100],[0,3,101],[0,2,4],[0,3,102],[0,5,103],[0,6,104],[0,2,100],[0,3,101],[0,2,105],[0,3,102],[0,5,103],[0,6,104],[2,3,106],[2,7,107,8],[0,2,100],[2,5,108],[2,6,109],[2,3,110],[0,3,111],[3,5,112],[3,6,113],[0,2,114],[2,5,115],[2,6,116],[0,5,117],[0,6,118],[5,6,119]]),
([w0,w1,w2,w3,w30,w31,w38,w243],[15,1,27,4,36,37,10],[44,5,7,9,11,13,15,31,51,33,34,18,41,10,20,21,35,36,37,38,39,28],[[0,1,100],[0,101,2],[0,3,102],[0,1,103],[0,1],[0,4,104],[0,5,105],[1,106,2,107],[1,3,106],[0,1,108],[0,1,108],[1,4,109],[1,5,110],[2,3,111,102],[0,112,6,113],[0,101,6],[2,4,114,104],[2,5,115,105],[0,3,116,113],[0,3,102],[3,4,117],[3,5,118],[0,6],[0,4,119],[0,5,120],[0,4,104],[0,5,105],[4,5,121]]),
([w199,w0,w1,w2,w3,w30,w38,w243],[10,38,1,15,4,36,39,40,5],[5,7,11,13,44,9,30,32,8,33,34,40,48,42,43,54,36,37,55,27,28],[[0,1],[0,2],[0,3,100],[0,4,101],[0,2,5],[0,6,102],[0,7,103],[0,2,104],[0,3,100],[0,4,101],[0,2,105],[0,6,102],[0,7,103],[0,2,106],[2,4,107],[2,3,108,8],[2,6,109],[2,7,110],[0,4,111],[0,2,112],[0,6,113],[0,7,114],[2,4,115,108],[4,6,116],[4,7,117],[2,6,118],[2,7,119],[6,7,120]]),
([w0,w1,w2,w7,w3,w30,w38,w243],[5,1,10,14,6,0,41,42],[56,57,16,49,7,58,10,8,11,59,13,60,6,12,14,40,48,42,43,35,36,37,38,39,28],[[0,1,100,2,101],[0,3,4,102,103],[0,4,103],[0,3,5,104,105],[0,1,106,107],[0,6,108,109],[0,7,110,111],[0,1,2,102],[1,2],[0,1,5,112],[0,1,4,106],[0,1,6,113],[0,1,7,114],[0],[2,4,5,115],[1,4,116],[2,4,6,117],[2,4,7,118],[3,4,5,112],[1,4,106],[4,6,113],[4,7,114],[1,5,119],[3,5,6,120],[3,5,7,121],[1,6,122],[1,7,123],[6,7,124]]),
([w249,w0,w1,w2,w3,w30,w38,w243],[5,10,14,41,0,1,43,44],[49,19,20,21,1,7,29,11,13,16,32,8,33,34,40,35,36,37,38,39,28],[[0,1,2,100],[1,3],[0],[1,2,4],[1,5,101],[1,6,102],[1,7,103],[0,1,4,104],[0,1,2,100],[0,1,2,105],[0,1,5,106],[0,1,6,107],[0,1,7,108],[0,1,4,109],[0,2,4,110,5],[0,4,5,111],[0,4,6,112],[0,4,7,113],[1,2,114,4],[1,5,101],[1,6,102],[1,7,103],[2,5,115],[2,6,116],[2,7,117],[5,6,118],[5,7,119],[6,7,120]]),
([w0,w1,w2,w3,w9,w30,w38,w243],[45,0,10,14,25,4,46,47],[2,57,49,3,10,8,11,59,13,60,46,0,33,34,17,20,21,54,18,36,37,19,38,39,28],[[0,1,100,2,101],[2,3,102,4],[1,103,2],[2,3,102],[0,2,5,104,105],[2,6,106,107],[2,7,108,109],[0,1,3,110],[0,1,3,111],[0,1,3,111],[0,1,5,100],[0,1,6,112],[0,1,7,113],[1,2,114],[1],[0,2,3,5,114],[2,3,6,115],[2,3,7,116],[1,2],[0,1,5,117,118],[1,6,119],[1,7,120],[0,3,5,121],[3,6,115],[3,7,116],[0,5,6,122],[0,5,7,123],[6,7,124]]),
([w124,w0,w1,w2,w3,w30,w38,w243],[14,10,0,46,4,48,49,6],[49,19,20,21,56,7,29,11,13,46,32,8,33,34,17,35,24,25,38,39,28],[[0,1,100],[0,2],[0,2],[0,3],[0,4,101],[0,5,102],[0,6,103],[1,2,104],[0,1,100],[0,1,105],[1,4,106],[1,5,107],[1,6,108],[0,2,109],[0,2,110,7],[2,4,111],[2,5,112],[2,6,113],[0,1,114,2],[0,4,101],[0,5,102],[0,6,103],[0,4,115,105],[0,5,116],[0,6,117],[4,5,118],[4,6,119],[5,6,120]]),
([w0,w1,w2,w3,w30,w33,w38,w243],[50,10,1,14,15,4,51,27,52,53],[2,57,3,49,52,7,9,11,59,13,60,15,0,33,34,18,20,21,54,19,36,37,26,27,28],[[0,1,2,100,101],[1,3,4,102,103,104],[0,1,5,105,102],[1,2,106],[1,6,102,7,103],[1,8,107,108],[1,9,109,110],[0,1,2,111,100],[0,2,5,111],[0,2,5,100],[0,2,7,100,6,112],[0,2,8,113],[0,2,9,114],[0,1,5,115,105],[1,2,104],[2],[1,8,116,107],[1,9,117,109],[0,2,5,118,119],[0,5,7,115,6,105],[0,5,8,120],[0,5,9,121],[1],[2,8,122],[2,9,123],[6,8,7,116,107],[6,9,7,117,109],[8,9,124]]),
([w125,w0,w1,w2,w3,w30,w38,w243],[14,10,1,52,54,55,4,6],[49,15,18,20,21,56,7,29,11,13,8,33,34,4,35,36,37,38,39,28],[[0,1,100],[0,2,101],[0,2],[0,1,102],[0,2,3],[0,4,103],[0,5,104],[1,2,105],[0,1,100],[0,1,106],[1,2,107],[1,4,108],[1,5,109],[0,2,101],[0,2,101],[2,6,110,7],[2,4,111],[2,5,112],[0,1,102],[0,2,113],[0,4,103],[0,5,104],[0,2,114],[0,4,115],[0,5,116],[2,4,117],[2,5,118],[4,5,119]])]
noncomputable def ptopD9 : List StD := [
([w0,w4,w2,w7,w3,w30,w38,w243],[10,6,5,56,0,1,57,58,59],[30,7,29,11,13,8,40,48,42,43,32,33,34,35,36,37,38,39,28],[[0,1],[0,1,100,2],[0,1,3],[0,4,101],[0,5,102],[0,6,103],[0,7,104],[0,2,8],[0],[2,4,101],[2,5,105],[2,6,103],[2,7,104],[0,1,2],[0,4,106],[0,5,107],[0,6,108],[0,7,109],[1,4,110],[1,5,105],[1,6,111],[1,7,112],[4,5,113],[4,6,114],[4,7,115],[5,6,116],[5,7,117],[6,7,118]]),
([w0,w1,w2,w10,w3,w30,w38,w243],[10,56,6,60,5,18,19,61,59,62,63,3],[7,29,11,13,32,6,8,33,34,15,40,41,42,43,5,61,62,24,27,35,37,38,63],[[0,1,2],[0,2,3,4],[0,2],[0,5,100],[0,6,101],[0,1,102],[0,103,7],[0,2,8,4],[0],[2,5,104,105],[2,6,106],[1,2,107],[2,108,9,109],[0,4],[0,5,110],[0,6,111],[0,1,112],[0,113,7,114],[5,100,10,115],[6,106,10,116],[1,102,10,117],[7,10,11,103,118],[5,6,119],[1,5,115],[5,120,7,100],[1,6,121],[6,116,7,106],[1,122,7,102]]),
([w0,w1,w2,w3,w250,w38,w243],[64,1,5,10,65,66,67,27,15,68,69],[1,5,7,11,13,16,6,8,12,64,0,40,42,65,36,37,62,63],[[0,1,2,100],[0,2,3,100,101],[2,4,102],[1],[2,5,103],[2,104,6],[0,1,3,105],[0,1,4,106],[0,1,7,107,8],[0,1,5,108],[0,1,109,9,110],[0,3,4,111],[0,3,8,101],[0,3,5,112],[0,3,113,6,101],[4,7,102,8],[4,5,114],[4,115,6,102],[5,7,103,8],[6,8,116,10],[5,117,6,103]]),
([w0,w251,w2,w3,w30,w38,w243],[5,10,7,70,14,15,66,71,41],[30,7,29,56,11,13,32,8,33,34,40,48,42,43,35,36,37,38,39,28],[[0,1,2,3],[0,1,100],[0,4,101],[0,5,102,103],[0,6,104],[0,7,105],[0,1,8],[0,4,106],[0,5,107],[0,6,108],[0,7,109],[1,4,110,100],[1,5,111],[1,6,112],[1,7,113,100],[4,5,114],[4,6,115],[4,7,116],[5,6,117],[5,7,118],[6,7,119]]),
([w0,w1,w2,w252,w30,w38,w243],[5,10,6,14,30,15,66,71,46,72],[44,66,29,11,13,46,32,8,33,34,48,42,43,4,35,36,37,38,39,28],[[0,1,100,2],[0,1,101,2],[0,3,4],[0,5,102,101],[0,6,103],[0,7,104],[0,1,105],[0,3,106],[0,5,107],[0,6,108],[0,7,109],[1,3,8,9],[1,5,110],[1,6,111],[1,7,112,113],[3,5,114],[3,6,115],[3,7,116],[5,6,117],[5,7,118],[6,7,119]]),
([w0,w1,w2,w3,w253,w38,w243],[15,5,6,14,36,73,66,71,52],[44,45,7,11,13,46,32,8,33,34,40,47,42,43,41,35,36,37,38,39,28],[[0,1,100,2],[0,2,101],[0,3,102],[0,1,4,5],[0,6,103],[0,7,104],[1,2,105,3],[1,3,106],[0,1,107],[1,6,108],[1,7,109],[2,3,110,111],[0,2,8],[2,6,112],[2,7,113,114],[0,3,115],[3,6,116],[3,7,117],[0,6,118],[0,7,119],[6,7,120]]),
([w0,w1,w2,w3,w30,w254,w243],[15,5,6,14,16,71,66],[44,45,7,29,3,13,46,32,8,33,34,40,47,48,43,4,35,36,37,38,39,28],[[0,1,100,2],[0,2,101],[0,3,102],[0,1,103,104],[0,4],[0,5,105],[1,2,106,3],[1,3,107],[0,1,108],[1,6,109],[1,5,110],[2,3,111,112],[0,2,113],[2,4],[2,5,114,115],[0,3,116],[3,6,117],[3,5,118],[0,6,119],[0,5,120],[5,6,121]]),
([w0,w1,w2,w3,w30,w38,w255],[15,5,6,14,66,71,74,75,76],[44,45,7,29,3,11,46,32,8,33,34,40,47,48,42,35,36,37,38,39,28],[[0,1,100,2],[0,2,101],[0,3,102],[0,1,103,104],[0,4,105],[0,5,6],[1,2,106,3],[1,3,107],[0,1,108],[1,4,109],[1,5,110],[2,3,111,112],[0,2,113],[2,4,114],[2,5,7,8],[0,3,115],[3,4,116],[3,5,117],[0,4,118],[0,5,119],[4,5,120]]),
([w1,w2,w5,w3,w30,w31,w38,w243],[5,77,10,19,22,27,15,78,79],[30,15,33,34,18,41,20,21,36,37,28],[[0,1,2,3,100],[0,2,3,101],[0,3,4,101],[0,3,4,5],[0,3,5,6],[0,3,7,102],[0,1,3,8,103],[0],[1,2,4,104],[1,2,3,105],[1,2,3,5,6],[1,2,7,106],[1,2,8,107],[2,4,104],[2,3,5],[2,3],[2,7,106],[1,2,8,107],[3,4,5],[4,5,6],[4,7,108],[1,4,8,109],[0],[3,5],[1,3,5],[5,6],[1,5,6],[1,7,8,110]]),
([w0,w1,w5,w3,w9,w30,w38,w243],[80,10,18,81,14,22,82,83,25],[56,66,10,11,13,46,33,34,38,39,28],[[0,1,2,100],[1,3],[0,1,2,101],[0,1,2,4],[0,1,5,102],[0,1,6,103],[0,1,7,104],[1,2,105],[2,4,8],[2,4,8],[0,2,5,102],[2,6,106],[2,7,107],[1,2,8],[1,2],[0,1,5,102],[1,6,103],[1,7,104],[1],[0,2,5,8],[2,6,8],[2,7,8],[0,4,5,8],[4,6,8],[4,7,8],[0,5,6,108],[0,5,7,109],[6,7,110]]),
([w0,w1,w2,w3,w15,w30,w38,w243],[10,18,25,14,84,22,85,86,24],[56,10,11,67,49,30,33,64,0,41,20,68,5,38,62,63],[[0,1,100],[0,2,1,3],[0,1,4],[0,2,3],[0,5,101],[0,4,102],[0,103,6,104],[0,1,105],[1,3,2],[1,2,7],[1,5,101],[1,4,106],[1,107,6,108],[0,1,2],[0,2,8],[0,5,109],[0,4,110],[0,111,112],[0],[1,2],[1,2],[1,2],[2,5,7],[2,4,7],[2,6,7],[4,5,113],[5,114,6,101],[4,115,6,102]]),
([w0,w1,w2,w3,w30,w59,w38,w243],[10,19,15,27,22,28,87,88,89],[56,7,69,49,13,30,32,70,0,34,18,71,5,21,61,37,72],[[0,1,100],[0,2,1,3],[0,4,101],[0,1,3],[0,3,5],[0,102,103],[0,6,104],[0,1,105],[1,4,106],[1,2,3],[1,3,7],[1,107,8,108],[1,6,109],[0,4,110],[0,1,6],[0,2],[0,111,8,112],[0,6,113],[1,3],[3,4,7],[4,114,8,101],[4,6,115],[0],[1,3],[1,3],[3,7],[3,6,7],[6,116,8,104]]),
([w0,w1,w2,w3,w256,w30,w38,w243],[10,90,15,14,91,66,85,86,68],[56,49,10,11,67,46,33,64,0,48,42,65,4,38,62,63],[[0,1,100],[0,2,101,3],[0,1,4],[0,1],[0,2,102],[0,5,103],[0,104,6,101],[0,1,105],[1,3,4],[1,4,7],[1,2,102],[1,5,106],[1,107,6,108],[0,1,4],[0,4,1],[0,2,109],[0,5,110],[0,111,8,112],[0],[1,2,4],[1,4],[1,4],[2,4,7],[4,5,7],[4,6,7],[2,5,113],[2,114,6,102],[5,115,6,103]]),
([w0,w1,w2,w3,w30,w257,w38,w243],[15,92,71,28,27,93,51,87,89],[44,5,7,73,3,13,30,32,70,0,34,18,71,21,61,37,72],[[0,1,100],[0,2,101],[0,3,102],[0,1,4],[0,4,1],[0,103,5,104],[0,2,105],[1,2,106],[1,3,107],[0,1,4],[1,4,6],[1,108,5,109],[1,2,110],[2,3,111],[0,2,7],[0],[2,112,8,101],[2,4,113],[0,3,4],[3,4,6],[3,114,5,102],[2,3,115],[0,2],[0,4],[0,2,4],[4,5,6],[2,4,6],[2,116,5,105]]),
([w0,w1,w2,w6,w9,w30,w38,w243],[94,10,0,14,84,4,95,96,86,25],[2,66,10,11,13,46,33,34,18,19,20,21,38,39,28],[[0,1,2,100],[0,1,3,101],[1,2],[0,1,3,4],[0,1,5,102],[0,1,6,103],[0,1,7,104],[1,2,105],[2,8,9],[2,3,9],[2,5,100],[0,2,6,106],[2,7,107],[1,8,9,108],[1,2],[1,5,109],[0,1,6,110],[1,7,111],[1],[5,8,9],[0,6,8,9],[7,8,9],[3,5,9],[0,3,6,9],[3,7,9],[0,5,6,112],[5,7,113],[0,6,7,114]]),
([w18,w0,w1,w2,w3,w30,w38,w243],[24,97,10,90,86,18,98,71,14,99,85],[0,10,11,13,56,49,67,15,33,64,18,48,42,65,4,35,36,37,38,62,63],[[0,1,2],[3,4,100],[2,4,5],[0,2],[0,4,101],[1,4,6,102],[4,103,7],[1,2,3,104],[1,2,6,105,8],[0,2,9],[0,2,101],[1,2,6,102],[1,2,106,10,103],[2,3,107],[0,3,100],[0,3,101],[1,3,6,108],[3,109,10,100],[0,2,110],[0,2,111],[1,2,6,112],[2,113,114],[0,3,115,110],[0,6,116,9],[0,117,10,110],[0,6,118],[0,119,10,101],[1,6,120,10,102]]),
([w0,w1,w2,w3,w31,w33,w38,w243],[10,1,15,4,27,100,101,88,102],[44,41,7,10,11,13,15,33,34,18,20,21,36,37,28],[[0,1,100],[0,2,101],[0,3,102],[0,1],[0,4,103],[0,5,104],[0,6,105],[0,1,106],[1,3,106],[1,2,4],[1,4,7],[1,5,107],[1,6,108],[0,3,109],[0,2,8],[0,1],[0,5,110],[0,6,111],[2,3,4],[3,4,7],[3,5,112],[3,6,113],[0],[2,4],[2,4],[4,5,7],[4,6,7],[5,6,114]]),
([w0,w258,w2,w3,w30,w38,w243],[10,103,104,15,66,87,5,71,68],[5,7,74,11,13,8,64,40,48,42,65,54,36,37,55,62,63],[[0,1,2],[0,3,100],[0,1,101],[0,1,102],[0,4,103],[0,104,5],[0,6,100],[1,6,101],[1,6,105],[4,6,103],[5,6,106,7],[0,1,107],[0,1,108],[0,4,109],[0,110,5,100],[1,3,111,105],[1,4,112],[1,113,5,101],[1,4,114],[1,115,8,105],[4,116,5,103]]),
([w0,w1,w2,w259,w30,w38,w243],[0,10,71,14,27,105,45,93,106,2],[1,49,29,73,13,16,32,8,70,0,34,48,42,43,35,61,21,38,39,72],[[0,1,100],[1,2,100],[1,3,101],[1,4,102,5,6],[1,103,7,100],[1,2,104],[0,1,105],[0,3,106],[0,4,107,5],[0,108,7,109],[0,2,110],[0],[1,6,111],[1,112,8,105],[1,2,113,105],[3,4,114,5,6],[3,115,7,9],[2,3,116],[5,6,117,7,107],[2,4,118,5,6],[2,119,7,104]]),
([w0,w260,w2,w3,w30,w38,w243],[10,6,0,107,93,71,2,108],[49,7,29,73,13,32,8,70,34,75,76,77,30,78,35,61,25,38,39,72],[[0,1,100],[0,1,100],[0,2,101],[0,3,102],[0,103,4,100],[0,5,104],[0,1,2],[1,2,105],[1,3,106],[1,107,4,6],[1,5,108],[0,2,109],[0,3,110],[0,111,7,112],[0,5,113,112],[2,3,114,101],[2,115,4,101],[2,5,116],[3,117,4,106],[3,5,118],[4,5,119,104]]),
([w88,w0,w1,w2,w3,w30,w38,w243],[10,27,92,88,28,2,109,15,89,110],[15,18,20,21,2,5,7,10,73,3,13,70,34,35,36,37,38,39,28],[[0,1],[2,3,100],[0,2],[3,4,101],[0],[3,102,5],[3,6,103],[0,2,104],[0,6,105,7],[0,4,106],[0,1,107,2],[0,108,109],[0,6,110],[0,2,100],[2,4,100],[2,3,104],[2,111,8,100],[2,6,112],[0,4,101],[0,2,9],[0,9,102],[0,6,103],[2,4,113,107],[4,9,114],[4,6,115],[2,9,116],[2,6,117,107],[6,9,118]])]
noncomputable def ptopD8 : List StD := [
([w1,w2,w10,w3,w30,w38,w243,w261],[10,111,112,113,62,114,115,5,61,116,63,87,117,118,119],[32,6,8,33,34,40,41,42,49,61,11,24,79,7,39,63],[[0,1,2],[0],[2,3,100,101],[2,3,102],[1,2,103],[2,4,104],[2,4,5,6],[7],[0,3,105],[0,2,106],[0,1,107],[0,4,8],[0,6,8,108],[3,9,101,10,109],[2,9,11,10],[1,9,110,10,111],[4,9,12,10,112],[4,6,10,13],[2,3,14],[1,3,109],[3,4],[3,6,113],[1,2,14],[2,4,114],[2,6,14],[1,4,115],[1,6,110],[0]]),
([w0,w2,w10,w3,w30,w38,w243,w262],[62,120,121,5,6,18,19,119,61,122],[7,11,34,40,41,42,43],[[0,1,2,3],[4],[2,5,100],[2,6,7],[1,2,101],[0,2,102],[2,0,7],[3],[0,5,103],[0,6,104],[0,1,105],[0,2,106,8],[0,7,9],[5,9],[6,7],[1,9],[0,2,9],[0,2],[5,6,7],[1,5,9],[0,5,9],[5,7,9],[1,6,7],[0,6,9],[6,7,9],[0,1,9],[1,7,9],[3]]),
([w0,w1,w10,w3,w30,w38,w243,w263],[123,124,10,6,125,119,126,122],[7,11,32,6,8,33,43],[[0,1,2],[3],[2,4,100],[0,2,5],[1,2,101],[2,5],[2,5,6],[2],[0,4,102,103],[0,3,104],[0,1,105],[0,5,106],[0,5,7],[4,7],[0,5],[1,7],[5,7],[5,6,7],[0,4,5],[1,4,7],[4,5,7],[4,5,7],[0,1,5],[0,5,7],[0,5,7],[1,5,7],[1,5,7],[2]]),
([w0,w1,w2,w10,w3,w30,w38,w243,w264],[121,127,126,62,128,129,116,130,131,132,133,134,135,63,119,136,137,138,139,140,141],[],[[0,1,2],[3,2,4],[5],[0,6],[0,6],[0,6],[0,5,3],[7],[0,8,2],[0],[4,9],[2,9],[1,9,2],[2,0,3],[10],[4],[0,11],[0,11],[0,11],[0,4,11],[12],[2,6,13],[13,6],[1,6,13],[3,13],[3],[2,14,15],[1,16,2],[2,16],[2,6,17],[1,14,15],[3,18,15],[15,6,14],[1,19,3],[1,6,20],[13]]),
([w0,w1,w2,w3,w30,w38,w243,w264],[121,128,62,129,136,137,142,119,143,122],[7,11],[[0,1,2,3],[0,1,4,2],[0,5,100,6],[0,4,7],[0,101,8],[0,2,3],[7],[0,1,9],[1,5,9],[1,4,9],[1,9],[1,0,2],[9],[0,9],[0,4,9],[0,9],[0,1,2,9],[9],[4,5,7],[8,6,9],[2,5,9],[9],[4,7],[2,4,9],[4,5,7],[2,9],[9],[9]]),
([w265,w0,w1,w2,w3,w30,w38,w243],[144,145,119,146,0,63,25,1,121,147],[11],[[0,1,2],[1,2],[1,3],[4,5,6],[2,5,7],[0,5,100],[2,5,8],[1,2,9],[1,2,9],[1,9],[1,2,9],[1,9],[1,2,9],[1,2,9],[2,9],[2,3,9],[2,9],[2,3,9],[1,9],[1,2,9],[1,9],[1,2,9],[2,9],[9],[2,9],[9],[2,9],[2,9]]),
([w0,w1,w2,w10,w30,w38,w243,w266],[119,148,149,150,151,152,137,138,153,62,154,63,116,155,156],[11,7,8,33,32,6,41,42,37,5,24,80,81],[[0,1,2],[0,2,3,4],[0],[0,2,5],[1,2,100],[0,2],[2,6,101,7],[0,2,8,4],[2],[0,4,102],[0,1,103],[0,4,9],[0,6,104,7,105],[4],[0,2,106,5],[0,1,107],[0,2,108],[0,7,109],[0,5],[1,6,100,10,110],[0,6,108,10,111],[7,10,11,12,13],[1,0,5],[0,5,111],[5,0],[0,1,112],[1,6,7,100],[7,0,14]]),
([w1,w2,w3,w250,w38,w243,w261],[157,119,158,87,15,66,68],[16,6,12,82,1,40,42,65,36,7,63],[[0,1,100],[0,2,101],[0,1,3,4],[0,5,102],[0,1,103],[0,6,104],[1,2,105],[1,4,3],[1,5,106],[1,3,107],[1,6,100],[1,2,4],[2,5,108],[1,2],[2,6,109],[1,4],[1,4,0,6],[0,1],[1,5,110],[5,6,110],[1,4]]),
([w0,w1,w2,w250,w38,w243,w266],[159,151,119,160,25,87,161,149,162],[1,11,7,16,12,83,84,42,37,80,81],[[0,1,100],[1,2,100],[0],[1,3,101],[1,2],[1,4,102],[0,2,103],[0,2,5,6],[0,3,104],[0,2,105,5],[0,4,106],[2,6,5],[2,3,107],[2,5,108,7],[2,4,103],[2,3,6],[2,6,109],[2,4,6],[2,3,110],[3,4,101],[2,4,8]]),
([w0,w1,w2,w3,w30,w38,w243,w267],[163,149,164,85,165,166,98,167,168,169,170,171,172,25,173,119],[56,49,10,11,15,33,34,0,18,48,42,65,4,35,36,38,39,28,12],[[0,1,2,100,101],[0,1,2,101,3],[1,2,3,4],[1,0,102,5],[1,6,103],[0,1,3,4],[1,3,7],[1,2,104],[2,4,104],[2,8,102],[2,6,105],[2,3,106],[2,9,107,10,104],[1,2,108],[1,8,109],[1,6,110],[1,3,111,112],[1,11,12,13],[2,0,113,5,14],[2,6,114,108],[0,2,1,3],[1,10,2,13],[6,0,115,5,8],[3,8,116],[8,9,15,10],[0,3,6,117],[6,9,103,10,118],[2]]),
([w18,w0,w1,w2,w30,w38,w243,w266],[174,149,85,90,98,25,119,159,168],[0,11,56,49,10,85,15,33,64,86,48,42,37,47,38,62,28],[[0,1,2,3],[3,4,100],[1,4,5],[4,6,7],[0,4,101,8],[2,1,4],[1,2],[1,3,102],[1,2,103],[1,8,104],[1,4,101],[1,2,105],[1,2,5,103],[1,3,106],[3,8,104],[3,4,107],[2,3,108],[3,5,109],[1,8,110],[1,4,111],[1,2,112],[1,5,113],[4,8,114],[2,8,115],[5,8,104],[2,4,116],[4,5,101],[3]]),
([w258,w2,w3,w30,w38,w243,w261],[119,10,5,25,175,87,66,157,68,176,177],[5,7,11,40,42,65,36,87,63],[[0,1,100,2],[0,3,101,4],[0,2,5,4],[0,6,102],[0,2,7,5],[0,4,8],[0,3,103,9,10],[0,1,5,7],[0,6,104],[0,1,105,5],[0,8,100],[0,7],[6,3,106,9,10],[0,3,9,10],[8,3,101,9],[0,6,7],[0,7,107,8],[0,7],[0,6,108],[6,8,102],[0,1]]),
([w0,w258,w2,w30,w38,w243,w266],[119,178,25,159,160,149,151,87,155,162],[5,11,7,83,42,37,80,81],[[0,1,2],[0,2,100],[0,2,3],[2,4,101],[0,2],[2,4,102],[0,5,100,6],[0,3,7],[0,4,101],[0,6,103,7],[0,2,8],[0,3,7],[0,4,104],[0,5,105],[0,2,100],[0,3],[0,3,106],[0,2,3],[0,4,107],[2,4,101],[0,2,9]]),
([w0,w1,w259,w30,w38,w47,w243],[179,180,10,14,181,93,71,182],[1,29,73,13,8,42,16,34,48,39,72],[[0,1,2,100],[0,2,3,4],[0,1,2,101],[0,2,4,102],[0,2,5,100],[0,2,6,103],[1,0,4,3],[1,7,104],[1,4,105],[1,5,106],[1,6,107],[1,0,4,3],[3,4,7,5],[3,4],[3,4],[1,4],[1,5,108],[1,6,109],[2],[4,6,110],[5,6,110]]),
([w0,w1,w2,w259,w38,w54,w243],[183,184,45,185,186,181,119,27,72],[1,38,13,16,88,0,34,48,43,55,89],[[0,1,2,100],[0,1,3,100],[0,1,4,5],[0,1,5,101],[0,1,6,100],[0,1,3,102],[1,2,103],[2,0,5,4],[2,5,104],[2,6,7,105],[2,3,106],[1,0,2,4,8],[1,5],[1,6,107,103],[1,3,108,103],[4,5,109],[4,5],[3,0,5,4],[2],[3,5,110],[3,6,7,102]]),
([w0,w260,w3,w30,w38,w47,w243],[179,119,10,6,14,181,187,188,93,71,189],[49,29,73,13,8,34,90,76,39,72],[[0,1,2,3,100],[0,2,4,5],[0,2,1,101,6,7],[0,2,5,102],[0,2,8,100],[0,1,2,9,103],[1,3,0,5,4],[1,3,7,104],[1,3,5,10],[1,3,8,10],[1,3,9,105],[4,1,5],[4,5,106],[4,5],[1,4,5],[5,1,6,7],[6,7,8,107],[1,7,9,108],[1],[1,5,9,109],[1,8,9,109]]),
([w0,w260,w2,w3,w38,w54,w243],[119,184,107,181,190,6,87,191,192,71,27],[49,38,13,88,34,76,30,78,55,89],[[0,1,100],[0,1,100],[1,2,3],[1,3,101],[0,1,100],[0,1,102],[0,1,2,4],[0,2,3],[0,3,103],[0,5,6,7],[0,6,104,8],[0,2,3],[0,3],[0,1,105,106],[0,1,107,106],[2,3,108],[0,2,3],[0,2,3],[0,2],[0,3,109],[0,9,10,102]]),
([w0,w1,w2,w3,w30,w38,w268,w243],[193,184,194,89,195,196,119,109,197,198,199,200,181],[2,5,7,10,73,3,13,30,32,70,34,18,21,35,36,37,39,91],[[0,1,2,100],[0,1,2,101,3],[1,4,102],[1,0,103,2],[1,3,104,105],[1,0,5,6],[0,1,7,106],[1,2,107,101],[2,4,108],[2,4,100],[2,3,109],[2,8,109,5,100],[2,7,110],[1,4,111],[1,2,3,9],[1,3,9],[1,3,10],[1,7,112],[2,4,113,11],[3,4,114],[4,8,12,5],[0,4,7,115],[2,1,3],[1,11],[2,7,116,103],[2],[0,3,7,117],[0,5,6,7,8,112,106]])]
noncomputable def ptopD7 : List StD := [
([w1,w10,w3,w30,w38,w261,w263],[10,119,201,202,62,114,115,122],[32,6,8,33,15],[[0],[1,2,100,101],[1,2,102],[1,103,3,104],[1,4,5,6],[1,2,7],[2,7],[1,7],[3,7],[1],[1,7],[1,2,7],[2,7],[2,6,7],[1,2,7],[3,1,7],[5,1,6,7],[1,4,7],[5,3,6,7],[1,7],[0]]),
([w1,w2,w10,w30,w38,w261,w266],[149,203,119,204,205,62,114,115,206,207,138,208,137,209,154,63],[8,33,41,42,5,11,24],[[0,1,2,3],[0],[2,4,100],[1,2,101],[2,5,6,7],[2,8,9,10],[10],[0,2,102,3],[0,1,103],[0,7,11,12],[0,8,10,104],[2,3],[1,13,105,14,106],[2],[10,14,15,9],[1,2,3],[3,2],[3,2],[1,7,105],[1,8,10,105],[0,10,7,9]]),
([w1,w2,w3,w30,w38,w41,w243,w264],[121,210,128,207,211,212,213,135,214,215,173,216,217,218,139,219,145],[],[[0,1,2],[2,3],[2,3],[1,3,2],[1,4,2],[2,0,3],[5],[0,6],[0,6],[0,1],[0,3,1],[0,2,6],[7],[8,9,10],[1,11],[1,3],[8,12],[8,3,12],[1,9,10],[1,3],[13,14,15],[10,3,9],[0],[1,9],[1,3,11],[1,3],[1,4,9],[16]]),
([w0,w1,w2,w3,w30,w38,w269,w243],[215,211,220,221,222,223,224,225,226,227,170,228,4,229,230,193],[],[[0,1,2],[0,3,4],[2,5],[2,0,5],[2,0,5],[0,6],[0,7],[1,8,3],[0,9],[3,9],[0,2,7],[0,1,7],[1,7],[0,4,7],[1,10],[0,10],[0,3,4],[3,7],[7,0,4],[8,11],[12,4],[0,4,13],[4,0,14],[7,0,5],[1,7],[15],[0,11,4],[0,11,4]]),
([w0,w2,w10,w30,w38,w262,w266],[119,231,232,151,152,62,233,207,138,137,234,154,235,63,61],[11,41,42,24,8,33],[[0,1,2,3],[0],[0,2,3,4],[1,3,100],[0,3,5],[3,6,7,8],[3],[0,4,101,5],[0,1,102],[0,5,9],[0,8,10],[0,4],[1,6,100,11,103],[0,5,11,12],[8,11,13,7],[1,0,4],[0,4,104,14],[4,0],[0,1,105],[1,6,8,100],[0,3,8,7]]),
([w1,w2,w250,w38,w261,w266],[119,236,87,173,160,138,25,71,161,68,237],[16,12,1,84,42,11],[[0,1,100],[0,1,2,3],[0,4,101],[0,3,102],[0,5,6,103],[0,7,2,8],[0,4,104],[0,3,100,9],[0,5,100],[0,3],[0,1],[0,3],[3,4,105],[4,5,101],[3,4,5,10]]),
([w258,w2,w30,w38,w261,w266],[119,71,138,87,238,160,239,68,240,155,236,237],[5,11,42],[[0,1,100,2],[0,2,3,4],[0,5,101],[0,6,7],[0,2,8,9],[0,10,3],[0,5,102],[0,7,100],[0,2,100],[0,5,10],[0,7,10],[0,2,8],[5,7,101],[2,5,101],[2,5,7,11]]),
([w0,w1,w259,w47,w54,w243],[180,184,200,181,186,93,119,27,185],[1,13,16,0,34,43],[[0,1,100],[1,2,3,4],[1,2,100,5],[1,6,100],[1,6,101],[0,2,3],[0,2,102],[0,6,7,103],[0,6,104,8],[2,4,3],[2,3],[2,3],[0,1],[2,6,105],[6,8,7,101]]),
([w0,w260,w3,w47,w54,w243],[119,184,200,181,186,93,41,241,242,191,192,243,71,27],[49,13,34,78],[[0,1,100],[1,2,3,4],[1,2,100,5],[0,1,100],[0,1,101],[0,2,3],[0,2,6],[0,7,8,9],[0,8,102,10],[2,4,3],[0,2,3],[0,2,3],[0,1,2,11],[0,2,103],[0,12,13,101]])]
noncomputable def ptopD6 : List StD := [
([w10,w3,w30,w38,w44,w261,w263],[200,244,245,119,246,247,117,138,248,202,249,209,250,251,252,230,253,254],[],[[0,1],[2,3],[0,4,5],[0],[3],[3,6,7],[0,3,8],[9,10],[0,10,11],[0,12],[0,7],[0,3,8],[8,3],[8,3],[8,13],[3],[0,14,15],[0,16,3],[15,16,17],[3,11],[0]]),
([w1,w3,w30,w41,w47,w243,w264],[214,255,173,256,257,142,258,259,241,119,218,260,215,261,229],[],[[0,1],[2,3],[0,3],[0,1],[2,0,4],[2],[0,1],[5,1],[6,7],[0,1],[0,3,8],[0,9,2],[0,1],[10,3,11],[2,1,12],[2],[0,3],[0,1,9],[0,1],[0,3,13],[14]]),
([w1,w2,w3,w30,w41,w264,w270],[214,210,217,262,215,211,212,213,261,263,173,222],[],[[0,1,2],[0,3,4],[2,3],[0,5,4],[6],[2,0,3],[4,2,7],[0,7],[1,3],[8],[0,2,7],[0,2],[1,3],[0,2],[0,2],[0,3],[9,3,4],[10,4],[0,4],[0,3],[0,11]])]
def ptopD5 : List StD := []
theorem ptopI5 : LevelN ptopR ptopT 5 ptopD5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC6x0 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (0*16)).take 16) = true := by decide +kernel
theorem ptopI6 : LevelN ptopR ptopT 6 ptopD6 := levelStep ptopB ptopW ptopQ ptopI5 (chunks 16 ptopD6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC7x0 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (0*16)).take 16) = true := by decide +kernel
theorem ptopI7 : LevelN ptopR ptopT 7 ptopD7 := levelStep ptopB ptopW ptopQ ptopI6 (chunks 16 ptopD7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x0 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x1 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (1*16)).take 16) = true := by decide +kernel
theorem ptopI8 : LevelN ptopR ptopT 8 ptopD8 := levelStep ptopB ptopW ptopQ ptopI7 (chunks 16 ptopD8 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC8x0
  · exact ptopC8x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x0 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x1 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (1*16)).take 16) = true := by decide +kernel
theorem ptopI9 : LevelN ptopR ptopT 9 ptopD9 := levelStep ptopB ptopW ptopQ ptopI8 (chunks 16 ptopD9 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC9x0
  · exact ptopC9x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC10x0 : levelOK ptopT ptopK ptopP 9 (ptopD9.map Prod.fst) ((ptopD10.drop (0*16)).take 16) = true := by decide +kernel
theorem ptopI10 : LevelN ptopR ptopT 10 ptopD10 := levelStep ptopB ptopW ptopQ ptopI9 (chunks 16 ptopD10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC10x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC11x0 : levelOK ptopT ptopK ptopP 10 (ptopD10.map Prod.fst) ((ptopD11.drop (0*16)).take 16) = true := by decide +kernel
theorem ptopI11 : LevelN ptopR ptopT 11 ptopD11 := levelStep ptopB ptopW ptopQ ptopI10 (chunks 16 ptopD11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC11x0
  ))
theorem ptopL : LowN ptopR ptopT 12 := lowSearch ptopB ptopI11 (by decide +kernel)

def sevenInputs : List Sig := rootsW [0,1,2,3,4,5,6]
def graph : Sig := W ptopT
theorem graph_proper : proper graph := (baseOK_ok ptopB).prop
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


def lowRow (i : Fin 7) : Row := Fin.ofNat 128 (([4, 8, 1, 1, 2, 1, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 128 ((1 <<< i.val) ||| (([4, 8, 1, 1, 2, 1, 1] : List Nat).getD i.val 0))

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


theorem excludes : Impossible true graph 11 sevenInputs.toFinset := by
  intro k small run
  have steps := list_run run sevenInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (sevenInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptopL q bank built hit
  omega

end PEqualNP.Outside.L_meta_10544

theorem PEqualNP.Outside.L_meta_10544 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 0, 3, 1, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_10544.replaceShort PEqualNP.Outside.L_meta_10544.excludes gates o fit correct
